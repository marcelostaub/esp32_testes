
// rev10 - 23/01/2019: Validação de tags de setpoint recebidas. Criação do método /cmd p/ zerar ciclos.
// rev09 - 28/05/2018: Alterada definição do nome da máquina (com índice). Alterada rotina de reset do Wifi.
// rev08 - 09/05/2018: Adicionado monitoramento da potencia do sinal Wifi. Timeout Config aumentado para 2,5 minutos
// rev07 - 11/04/2018: Timeou Portal Config = 120 segundos. AccessPoint = AP-218
// rev06 - 27/02/2018: 1. Tempo parada atual já vem em segundos. Não precisa dividir por 10.
// rev05 - 26/02/2018: 1. Adicionada verificação de comunicação; 2. Somado tempo da parada atual ao tempo ocioso.

#include "FS.h"                   // this needs to be first, or it all crashes and burns...
#include "SPIFFS.h"
#include <WiFi.h>          
//needed for library
#include <DNSServer.h>
#include <WebServer.h>
#include <WiFiManager.h>          
#include <ArduinoJson.h>          // inclui biblioteca Json
#include <Wire.h>
#include <EEPROM.h>
#include <testes.h>

//#include <AsciiModbusMaster_7E1.h>
#include <AsciiCrouzetMaster_7E1.h>

#define NUM_MAQUINA     '1'                              // índice da máquina do tipo 218S em uma mesma rede. Alterar.

//#define DEBUGING
//#define DEBUG_RS232

// página original da biblioteca simple-modbus: // https://code.google.com/archive/p/simple-modbus/
// documentação completa da library: // https://drive.google.com/drive/folders/0B0B286tJkafVYnBhNGo4N3poQ2c?tid=0B0B286tJkafVSENVcU1RQVBfSzg
// exemplo de MASTER e SLAVE: // https://industruino.com/blog/our-news-1/post/modbus-rtu-master-and-slave-14

// modificações necessárias para utilizar a biblioteca no WEMOS:
// http://forum.arduino.cc/index.php?topic=176142.555
// VER RESPOSTA 566

//#define TxEnablePin D8                                // *verificar qual pino deve ser configurado como direcional -> resposta; D4

#define HOUR 3600                                     // quantidade de segundos em 1 hora
#define MIN  60                                       // quantidade de segundos em 1 minuto

//////////////////// Port information ///////////////////
#define baud 115200                                   // tested 9600 to 115200
#define timeout 500                                   // timeout da requisição modbus
#define polling 50                                    // the scan rate, standard was 200
#define retry_count 50                                // número de tentativas para desabilitar a requisição
#define SlaveID 4                                     // endereço do slave (CLP Crouzet sempre = 4)

#define IN5      22                                   // pino que será utilizado para reset dos parâmetros de conexão WiFi

#define BYTESEG_I2C   200                             // valor do byte de segurança da i2c - sempre será enviado/recebido depois dos bytes de dados

// endereços da EEPROM onde serão gravados os setpoints
#define ADDR_P1     0                                 // ADD setpoint PRESSÃO1
#define ADDR_P2     2                                 // ADD setpoint PRESSÃO2
#define ADDR_PV     4                                 // ADD setpoint PRESSÃO VACUO
#define ADDR_TPO1   6
#define ADDR_TPO2   8
#define ADDR_MODO   10
#define ADDR_CIC    12                                 // ADD setpoint tempo ciclo
#define ADDR_ATV    14                                 // ADD setpoint tempo ativo
#define ADDR_INA    16                                // ADD setpoint tempo inativo
                                                       
// The total amount of available memory on the master to store data
#define TOTAL_NO_OF_REGISTERS 24                      // numero de registradores

void grava_regs(void);

// declaração dos registradores modbus - os dois últimos não são do CLP. São valores referentes 
enum
{
  P1,
  P2,
  P_VACUO,
  TPO_P1,
  TPO_P2,
  PECAS,
  STATUS_MACH,
  CICLOS,
  TPO_CICLO,
  TPO_ATIVO,
  TPO_INATIVO,
  ALARME_PRESSAO,
  TPO_PARADA_ATUAL,
  SP_P1,
  SP_P2,
  SP_P_VACUO,
  SP_TPO_P1,
  SP_TPO_P2,
  SP_MODO,
  //SP_TPO_CICLO,
  //SP_TPO_ATIVO,
  //SP_TPO_INATIVO,
  ZERA_CICLOS
};

enum
{
  PACKET1,                                          // set 4 registers
  PACKET2,                                          // read 4 registers
  TOTAL_NO_OF_PACKETS // leave this last entry
};
// Create an array of Packets to be configured
Packet packets[TOTAL_NO_OF_PACKETS];

// Masters register array
unsigned int regs[TOTAL_NO_OF_REGISTERS];       // vetor com registradores p/ com. modbus
unsigned long previousMillis;
unsigned int counter = 0;
unsigned long t_last_request=0;

unsigned int flags[TOTAL_NO_OF_REGISTERS];

//Variáveis do web server
char homePage[400];                         // Página usada no servidor web
char dataPage[800];                         // declara página que retornará dados dos sensores
char spPage[500];                           // declara página dos setpoints
char cmdPage[200];                          // declara página que monitora os comandos do Client

float sp_p1=1.0, sp_p2=2.0, sp_pv=-0.5, sp_tpo_p1=2.0, sp_tpo_p2=8.0, sp_tpo_ciclo=20.0, sp_tpo_ativo=15.0, sp_tpo_inativo=5.0;
float tpo_ocioso=0, tpo_ciclo=0;
unsigned long T_ocioso_seg = 0;            // tempo ocioso em segundos sem casa decimal
char str_tpo_ocioso[10];

unsigned char sp_modo = 0, zera_ciclo=0, status_run=0, timerErrorCom=0;
unsigned int pecas=0, ciclos=0, T_ocioso_min=0, reg_erros_232=0;

unsigned char flag_client = 0;

WebServer server(80);                // Declaração do servidor, porta 80

unsigned long DelayWebData = 0, T_Loop=0, t_last_loop=0;

uint8_t Counter=0;
unsigned int timerAux_i2c = 0;
float temp_i2c = 0;

long pot_rssi=0;
int qualidade_sinal=0;

char nome_maquina[17];                    // nome máquina
char nome_AP[20];                         // nome Access Point

// funções para salvar e ler da EEPROM
void salva_sps_EEPROM()
{
  unsigned int u16aux=0;
  u16aux = regs[SP_P1];
  EEPROM.write(ADDR_P1, (u16aux>>8));
  EEPROM.write(ADDR_P1+1, (u16aux));
  u16aux = regs[SP_P2];
  EEPROM.write(ADDR_P2, (u16aux>>8));
  EEPROM.write(ADDR_P2+1, (u16aux));
  u16aux = regs[SP_P_VACUO];
  EEPROM.write(ADDR_PV, (u16aux>>8));
  EEPROM.write(ADDR_PV+1, (u16aux));
  u16aux = regs[SP_TPO_P1];
  EEPROM.write(ADDR_TPO1, (u16aux>>8));
  EEPROM.write(ADDR_TPO1+1, (u16aux));
  u16aux = regs[SP_TPO_P2];
  EEPROM.write(ADDR_TPO2, (u16aux>>8));
  EEPROM.write(ADDR_TPO2+1, (u16aux));
  u16aux = regs[SP_MODO];
  EEPROM.write(ADDR_MODO, (u16aux>>8));
  EEPROM.write(ADDR_MODO+1, (u16aux));
  u16aux = (sp_tpo_ciclo*10);
  EEPROM.write(ADDR_CIC, (u16aux>>8));
  EEPROM.write(ADDR_CIC+1, (u16aux));
  u16aux = (sp_tpo_ativo*10);
  EEPROM.write(ADDR_ATV, (u16aux>>8));
  EEPROM.write(ADDR_ATV+1, (u16aux));
  u16aux = (sp_tpo_inativo*10);
  EEPROM.write(ADDR_INA, (u16aux>>8));
  EEPROM.write(ADDR_INA+1, (u16aux));

  EEPROM.commit();
  
}

void carrega_sps_EEPROM()
{
  float teste=0.0;
  unsigned int u16aux=0;
  u16aux = EEPROM.read(ADDR_P1);
  sp_p1 = (u16aux<<8) | EEPROM.read(ADDR_P1+1);
  sp_p1/=10.0;
  u16aux = EEPROM.read(ADDR_P2);
  sp_p2 = (u16aux<<8) | EEPROM.read(ADDR_P2+1);
  sp_p2/=10.0;
  u16aux = EEPROM.read(ADDR_PV);
  sp_pv = (u16aux<<8) | EEPROM.read(ADDR_PV+1);        // p vácuo tem que ser com sinal, pq pode ser negativa
  sp_pv /= 10.0;
  u16aux = EEPROM.read(ADDR_TPO1);
  sp_tpo_p1 = (u16aux<<8) | EEPROM.read(ADDR_TPO1+1);
  sp_tpo_p1 /= 10.0;
  u16aux = EEPROM.read(ADDR_TPO2);
  sp_tpo_p2 = (u16aux<<8) | EEPROM.read(ADDR_TPO2+1);
  sp_tpo_p2 /= 10.0;
  u16aux = EEPROM.read(ADDR_MODO);
  sp_modo = (u16aux<<8) | EEPROM.read(ADDR_MODO+1);
  u16aux = EEPROM.read(ADDR_CIC);
  u16aux = (u16aux<<8) | EEPROM.read(ADDR_CIC+1);
  teste=u16aux;
  sp_tpo_ciclo=teste*10/100.0;                               // valor 511 quando divide por 10.0 está passando para 51 ao invés de 51.1
  u16aux = EEPROM.read(ADDR_ATV);
  sp_tpo_ativo = (u16aux<<8) | EEPROM.read(ADDR_ATV+1);
  sp_tpo_ativo /= 10.0;
  u16aux = EEPROM.read(ADDR_INA);
  sp_tpo_inativo = (u16aux<<8) | EEPROM.read(ADDR_INA+1);
  sp_tpo_inativo /= 10.0;

  grava_regs();                           // carrega os registradores modbus com os valores lidos da memória não-volátil
  
}


// função que converte segundos para formato hh:mm:ss
void ConvertSegToTime(unsigned long segundos, char *to_string)
{
    int time_target=segundos;
    int hour=time_target/HOUR;
    int second=time_target % HOUR;
    int minute=second/MIN;
    second %= MIN;
    sprintf(to_string, ("%.2d:%.2d:%.2d"),hour,minute,second);
}


// Página web que recebe escrita dos cmds
void writeCMD()
{
    StaticJsonBuffer<200> newBuffer;
    JsonObject& newjson = newBuffer.parseObject(server.arg("plain"));
       
    StaticJsonBuffer<200> jsonBuffer;
    JsonObject& root = jsonBuffer.createObject();

    char str_data[199];
    
    if (!newjson.success())
    {
      // Parsing failed
      server.send ( 400, "text/json", "{success: false}" );
      return;
    }

    if (newjson.containsKey("zera_ciclo")) { zera_ciclo = newjson["zera_ciclo"].as<int>(); }
    //if (newjson.containsKey("cmd_iniciar")) { cmd_iniciar = newjson["cmd_iniciar"].as<int>(); }

    //if(zera_ciclo==1) { ciclos=0;}            // verifica se deve zerar o contador de ciclos - NÃO ZERA! AGUARDA O CLP CROUZET ZERAR O CONTADOR!!
    if(zera_ciclo==1) { tpo_ocioso=0;}            // se deve zerar o contador de ciclos, zera tbm tpo_ocioso    
    
    root["tipo_maq"] = "218-PrensaSola";
    root["zera_ciclo"] = zera_ciclo;
    //root["cmd_iniciar"] = cmd_iniciar;
    root.printTo(str_data);
    
    server.send ( 200, "text/json", str_data );

    grava_regs();                                   // salva os novos valores nos registradores modbus  
}


// Página web que envia JSON com dados da máquina
void viewDATA() {

  char str_data[599];

  DelayWebData = millis();

  StaticJsonBuffer<600> jsonBuffer;
  JsonObject& root = jsonBuffer.createObject();

  T_ocioso_min = T_ocioso_seg/60;

  float signed_pv = regs[P_VACUO];
  if(signed_pv>32767)
  { signed_pv -= 65536; }
  
  float signed_sp_pv = regs[SP_P_VACUO];
  if(signed_sp_pv>32767)
  { signed_sp_pv -= 65536; }

  root["QualidSinal"] = qualidade_sinal;
  //root["RSSI_dB"] = pot_rssi;                       // atenuacao do sinal wifi
  root["tipo_maq"] = nome_maquina;
  root["press1"] = regs[P1]/10.0;                     // pressão1 medida no ciclo
  root["press2"] = regs[P2]/10.0;                     // pressão2 medida no ciclo
  root["p_vacuo"] = signed_pv/10.0;                   // pressão vácuo medida no ciclo
  root["tpo_p1"] = regs[TPO_P1]/10.0;                 // tempo da pressão 1
  root["tpo_p2"] = regs[TPO_P2]/10.0;                 // tempo da pressão 2
  root["pecas"] = regs[PECAS];                        // pecas produzidas
  root["ciclos"] = regs[PECAS];                       // numero de ciclos
  root["status"] = status_run;                        // 0 se parada, 1 se em operacao
  root["status_desc"] = regs[STATUS_MACH];            // status da máquina - código do clp
  root["tpo_ciclo"] = tpo_ciclo;                      // tempo do ciclo
  root["tpo_ativo"] = regs[TPO_ATIVO]/10.0;           // tempo ativo
  root["tpo_inativo"] = regs[TPO_INATIVO]/10.0;       // tempo inativo
  root["tpo_parada_atual"] = regs[TPO_PARADA_ATUAL];  // tempo da parada atual
  root["tpo_ocio_seg"] = T_ocioso_seg;                // somatório dos tempos inativos de todos os ciclos realizados
  root["tpo_ocio_min"] = T_ocioso_min;                // somatório dos tempos inativos de todos os ciclos realizados
  //root["tpo_ocioso"] = str_tpo_ocioso;              // total de tempo ocioso hh:mm:ss
  root["alm_press"] = regs[ALARME_PRESSAO];           // alarme pressao
  root["sp_p1"] = regs[SP_P1]/10.0;                   // valor desejado para a pressao1
  root["sp_p2"] = regs[SP_P2]/10.0;                   // valor desejado para a pressão2
  root["sp_pv"] = signed_sp_pv/10.0;                  // valor desejado para a pressão de vácuo
  root["sp_tpo_p1"] = regs[SP_TPO_P1]/10.0;           // valor desejado para o tempo da 1pressao
  root["sp_tpo_p2"] = regs[SP_TPO_P2]/10.0;           // valor desejado para o tempo da 2pressao
  root["sp_modo"] = regs[SP_MODO];                    // modo de operação desejado (bota/padrão)
  root["sp_tpo_ciclo"] = sp_tpo_ciclo;                // valor desejado para o tempo de ciclo
  root["sp_tpo_ativo"] = sp_tpo_ativo;                // tempo ativo desejado
  root["sp_tpo_inativo"] = sp_tpo_inativo;            // tempo inativo desejado
  root["zera_ciclo"] = zera_ciclo;                    // comando zera_ciclo

#ifdef DEBUG_RS232
  root["Erros_RS232"] = errorCount;
  root["B0"] = rec_frame[0];
  root["B1"] = rec_frame[1];
  root["B2"] = rec_frame[2];
  root["B3"] = rec_frame[3];
  root["B4"] = rec_frame[4];
  root["B5"] = rec_frame[5];
  root["B6"] = rec_frame[6];
  root["B7"] = rec_frame[7];
  root["B8"] = rec_frame[8];
  root["B9"] = rec_frame[9];
  root["B10"] = rec_frame[10];
  root["B11"] = rec_frame[11];
  root["B12"] = rec_frame[12];
  root["B13"] = rec_frame[13];
  root["B14"] = rec_frame[14];
  root["B15"] = rec_frame[15];
  root["B16"] = rec_frame[16];
  root["B17"] = rec_frame[17];
  root["B18"] = rec_frame[18];
  root["B19"] = rec_frame[19];
  //root["T_web"] = millis()-DelayWebData;
  root["T_Loop"] = T_Loop;
#endif

  root.printTo(str_data);
  
  snprintf(dataPage, sizeof(dataPage),          //snprintf salva a string, junto com o tamanho dela - snprintf(string, tamanho da string, conteúdo da string, variáveis)
           // retorna a string com as variáveis
          str_data
          );
  server.send(200, "text/json", dataPage);    //Envia a string para o servidor web - server.send(Código de resposta, tipo de texto, string)  
}

// Página web que reseta as configurações de rede WiFi
void resetConfig() {

  char str_data[50];
  str_data[0] = 0;

  snprintf(dataPage, sizeof(dataPage),          //snprintf salva a string, junto com o tamanho dela - snprintf(string, tamanho da string, conteúdo da string, variáveis)
           // retorna a string com as variáveis
          str_data
          );
  server.send(200, "text/json", dataPage);    //Envia a string para o servidor web - server.send(Código de resposta, tipo de texto, string)

  WiFiManager wifiManager;

  // reseta SSID e senha
  wifiManager.resetSettings();
  //digitalWrite(LED_BUILTIN, HIGH);   // turn the LED off (HIGH is the voltage level)

  delay(2000);

  // procedimento para restart do dispositivo
  //WiFi.forceSleepBegin();
  //wdt_reset();
  ESP.restart();
  //while(1) wdt_reset();
}

void webHOME() {
  snprintf(homePage, sizeof(homePage),      //snprintf salva a string, junto com o tamanho dela - snprintf(string, tamanho da string, conteúdo da string, variáveis)
           //------------------------ Código HTML ------------------------------------
           "<meta http-equiv='refresh' content='10'/>\
          <h1>TECSISTEL WebServer - 218S</h1></p>\
          <h2>Home</h2></p>\
          <a href=\"get_data\"> <button>Dados do Processo</button></a>&nbsp\
          <a href=\"reset_config\"> <button>Reset WiFi Config</button></a> "
           //--------------------------------------------------------------------------
          );
  server.send(200, "text/html", homePage);  //Envia a string para o servidor web - server.send(Código de resposta, tipo de texto, string)
  //          <a href=\"resetConfig\"> <button>Reset WiFi Config</button></a>"
}

void handleNotFound() {
  String message = "File Not Found\n\n";
  message += "URI: ";
  message += server.uri();
  message += "\nMethod: ";
  message += (server.method() == HTTP_GET) ? "GET" : "POST";
  message += "\nArguments: ";
  message += server.args();
  message += "\n";
  for (uint8_t i = 0; i < server.args(); i++) {
    message += " " + server.argName(i) + ": " + server.arg(i) + "\n";
  }
  server.send(404, "text/plain", message);
}


/**************************************************************************************
 * this example shows how to set a static IP configuration for the ESP
 * although the IP shows in the config portal, the changes will revert 
 * to the IP set in the source file.
 * if you want the ability to configure and persist the new IP configuration
 * look at the FS examples, which save the config to file
 *************************************************************************************/

//default custom static IP
//char static_ip[16] = "10.0.1.59";
//char static_gw[16] = "10.0.1.1";
//char static_sn[16] = "255.255.255.0";

//define your default values here, if there are different values in config.json, they are overwritten.
//length should be max size + 1 
char mqtt_server[40];
char mqtt_port[6] = "8080";
char blynk_token[33] = "YOUR_BLYNK_TOKEN";
//default custom static IP
char static_ip[16] = "192.168.1.14";
char static_gw[16] = "192.168.1.1";
char static_sn[16] = "255.255.255.0";

//flag for saving data
bool shouldSaveConfig = false;

//callback notifying us of the need to save config
void saveConfigCallback () {
  Serial.println("Should save config");
  shouldSaveConfig = true;
}

//callback que indica que o ESP entrou no modo AP
void configModeCallback (WiFiManager *myWiFiManager)
{  
//  Serial.println("Entered config mode");
  Serial.println("Entrou no modo de configuração");
  Serial.println(WiFi.softAPIP()); //imprime o IP do AP
  Serial.println(myWiFiManager->getConfigPortalSSID()); //imprime o SSID criado da rede
}

/*
// inicializa a Serial utilizada com o protocolo modbus
void init_serial_modbus()
{
  modbus_construct(&packets[PACKET2], SlaveID, READ_HOLDING_REGISTERS, 0xFF18, 13, 0);        // leitura dos registradores 24(0xFF18) a 36 do CLP - localAdd = 00 a 12
  modbus_construct(&packets[PACKET1], SlaveID, PRESET_MULTIPLE_REGISTERS, 0xFF00, 7, 13);    // escrita nos registradores 00 a 06 do CLP (setpoints) - localAdd = 13 a 19
  //modbus_construct(&packets[PACKET3], SlaveID, READ_HOLDING_REGISTERS, 0xFF32, 8, 0);       // leitura dos registradores 32 a 39

  while(Serial.available())
  { Serial.read();}
  
  modbus_configure(&Serial, baud, SERIAL_7E1, timeout, polling, retry_count, TxEnablePin, packets, TOTAL_NO_OF_PACKETS, regs, flags);
}
*/

void setup() {

  unsigned char i=0;

  //pinMode(LED_BUILTIN, OUTPUT);
  //pinMode(D3, OUTPUT);
  pinMode(23, OUTPUT);
  pinMode(22, INPUT);
  //digitalWrite(LED_BUILTIN, LOW);   // turn the LED on (HIGH is the voltage level)
  // put your setup code here, to run once:
  Serial.begin(115200);
  Serial.println();

  // monta o nome da linha:
  nome_maquina[0] = '2';
  nome_maquina[1] = '1';
  nome_maquina[2] = '8';
  nome_maquina[3] = 'S';
  nome_maquina[4] = '-';
  nome_maquina[5] = 'P';
  nome_maquina[6] = 'r';
  nome_maquina[7] = 'e';
  nome_maquina[8] = 'n';
  nome_maquina[9] = 's';
  nome_maquina[10] = 'a';
  nome_maquina[11] = 'S';
  nome_maquina[12] = 'o';
  nome_maquina[13] = 'l';
  nome_maquina[14] = 'a';
  nome_maquina[15] = NUM_MAQUINA;

  nome_AP[0] = 'A';
  nome_AP[1] = 'P';
  nome_AP[2] = '-';
  for(i=0; i<16; i++)
  {
    nome_AP[i+3] = nome_maquina[i];
  }

  //read configuration from FS json
  Serial.println("mounting FS...");

  if (SPIFFS.begin(true)) {
    Serial.println("mounted file system");
    if (SPIFFS.exists("/config.json")) {
      //file exists, reading and loading
      Serial.println("reading config file");
      File configFile = SPIFFS.open("/config.json", "r");
      if (configFile) {
        Serial.println("opened config file");
        size_t size = configFile.size();
        // Allocate a buffer to store contents of the file.
        std::unique_ptr<char[]> buf(new char[size]);

        configFile.readBytes(buf.get(), size);
        DynamicJsonBuffer jsonBuffer;
        JsonObject& json = jsonBuffer.parseObject(buf.get());
        json.printTo(Serial);
        if (json.success()) {
          Serial.println("\nparsed json");

          strcpy(mqtt_server, json["mqtt_server"]);
          strcpy(mqtt_port, json["mqtt_port"]);
          strcpy(blynk_token, json["blynk_token"]);

          if(json["ip"]) {
            Serial.println("setting custom ip from config");
            //static_ip = json["ip"];
            strcpy(static_ip, json["ip"]);
            strcpy(static_gw, json["gateway"]);
            strcpy(static_sn, json["subnet"]);
            //strcat(static_ip, json["ip"]);
            //static_gw = json["gateway"];
            //static_sn = json["subnet"];
            Serial.println(static_ip);
//            Serial.println("converting ip");
//            IPAddress ip = ipFromCharArray(static_ip);
//            Serial.println(ip);
          } else {
            Serial.println("no custom ip in config");
          }
        } else {
          Serial.println("failed to load json config");
        }
      }
    }
  } else {
    Serial.println("failed to mount FS");
  }


  //WiFiManager
  //Local intialization. Once its business is done, there is no need to keep it around
  WiFiManager wifiManager;
  
  //set config save notify callback
  //wifiManager.setAPCallback(configModeCallback); 
  wifiManager.setTimeout(50);              // configura o timeout do portal de configuração para 2,5 minutos (150 segundos)
  //set config save notify callback
  wifiManager.setSaveConfigCallback(saveConfigCallback);

  //set static ip
  IPAddress _ip,_gw,_sn;
  _ip.fromString(static_ip);
  _gw.fromString(static_gw);
  _sn.fromString(static_sn);

  wifiManager.setSTAStaticIPConfig(_ip, _gw, _sn);
  
  //reset settings - for testing
  if(digitalRead(22)==LOW)             // se entrada estiver em nível baixo, reseta configurações (mudar este pino. Não pode ser D0, D1, D2, nem D4)
  {
    Serial.println("Resetando WiFi Config...");
       
    WiFi.disconnect(true);      // still not erasing the ssid/pw. Will happily reconnect on next start
    WiFi.begin("0","0");        // adding this effectively seems to erase the previous stored SSID/PW
    
    digitalWrite(23, HIGH);     // turn the LED on (HIGH is the voltage level) 
  }

  // descomentar
  wifiManager.setSTAStaticIPConfig(_ip, _gw, _sn);

  //WiFi.mode(WIFI_AP_STA);

  //tries to connect to last known settings
  //if it does not connect it starts an access point with the specified name
  //here  "AutoConnectAP" with password "password"
  //and goes into a blocking loop awaiting configuration
  wifiManager.setTimeout(2);
  //delay(100);
  if (!wifiManager.autoConnect("AP_AUTO1", "tecsistel")) {
  //WiFi.begin();
  //if (!WiFi.status() != WL_CONNECTED) {
    WiFi.disconnect();
    delay(50);
    Serial.println("Falha ao tentar se conectar à rede.");
    //wifiManager.startConfigPortal("AP_START2", "tecsistel");
    //wifiManager.startConfigPortal("AP_START2", "tecsistel");
    wifiManager.setTimeout(150);
    //delay(100);
    //WiFi.mode(WIFI_AP);
    wifiManager.startConfigPortal("AP_START2", "tecsistel");
    delay(100);
    //wifiManager.setTimeout(2);
    //wifiManager.autoConnect("AP_START3", "tecsistel");
    //delay(100);
  }

  WiFi.mode(WIFI_STA);

  //if you get here you have connected to the WiFi
  Serial.println("connected...yeey :)");

  //save the custom parameters to FS
  if (shouldSaveConfig) {
    Serial.println("saving config");
    DynamicJsonBuffer jsonBuffer;
    JsonObject& json = jsonBuffer.createObject();
    json["mqtt_server"] = mqtt_server;
    json["mqtt_port"] = mqtt_port;
    json["blynk_token"] = blynk_token;

    json["ip"] = WiFi.localIP().toString();
    json["gateway"] = WiFi.gatewayIP().toString();
    json["subnet"] = WiFi.subnetMask().toString();

    File configFile = SPIFFS.open("/config.json", "w");
    if (!configFile) {
      Serial.println("failed to open config file for writing");
    }

    json.prettyPrintTo(Serial);
    json.printTo(configFile);
    configFile.close();
    //end save
  }

  // só para o caso de se desejar que o programa NÃO rode sem conexão WiFi
  // se não conectou, reseta o ESP p/ tentar conectar novamente
  Serial.println(WiFi.status());
  if (WiFi.status() != WL_CONNECTED)
    ESP.restart();

  Serial.println("local ip");
  Serial.println(WiFi.localIP());
  Serial.println(WiFi.gatewayIP());
  Serial.println(WiFi.subnetMask());
  
  //Serial.println("local ip");
  //Serial.println(WiFi.localIP());


  // 07/12/2017 - adicionadas instancias para eventos de requisições HTTP:
  server.on("/", webHOME);                                   //Função da página web
  server.on("/get_data", viewDATA);                          //Instancia pagina de dados dos sensores
  //server.on("/set_sps", setSP);                            //Instancia pagina de dados dos sensores
  server.on("/reset_config", resetConfig);                   //Instancia pagina de reset das configurações de rede
  server.on("/cmd", HTTP_POST, writeCMD);                    // instancia metodo recebe escrita dos cmds do Client 

  //---------- JSON
  StaticJsonBuffer<400> jsonBuffer;
  JsonObject& root = jsonBuffer.createObject();
  
  // -------------------------------
  server.onNotFound(handleNotFound);                          //Função da página web
  server.begin();                                             //Inicia o serviço de servidor WEB
  Serial.println("HTTP server started");                      //Envia pela serial


  // instancia e executa função de recebimento de dados da aplicação Web
  // todo: retirar a função daqui. Deixar só a declaração com chamada
  server.on("/set_sps", HTTP_POST, [](){
    StaticJsonBuffer<1999> newBuffer;
    JsonObject& newjson = newBuffer.parseObject(server.arg("plain"));

    // newjson.printTo(Serial);            // na versão com 485, não podemos mais utilizar a serial para debug
       
    char strMAQ[10];
        
    StaticJsonBuffer<400> jsonBuffer;
    JsonObject& root = jsonBuffer.createObject();

    char str_data[399];
    
    if (!newjson.success())
    {
      // Parsing failed
      server.send ( 400, "text/json", "{success: false}" );
      return;
    }
    
    //newjson["tipo_maq"].printTo(strMAQ);
    if (newjson.containsKey("sp_press1"))       { sp_p1 = newjson["sp_press1"].as<float>(); }
    if (newjson.containsKey("sp_press2"))       { sp_p2 = newjson["sp_press2"].as<float>(); } 
    if (newjson.containsKey("sp_p_vacuo"))      { sp_pv = newjson["sp_p_vacuo"].as<float>();  }
    if (newjson.containsKey("sp_tpo_p1"))       { sp_tpo_p1 = newjson["sp_tpo_p1"].as<float>(); }
    if (newjson.containsKey("sp_tpo_p2"))       { sp_tpo_p2 = newjson["sp_tpo_p2"].as<float>(); }
    if (newjson.containsKey("sp_modo"))         { sp_modo = newjson["sp_modo"].as<int>(); }
    if (newjson.containsKey("sp_tpo_ciclo"))    { sp_tpo_ciclo = newjson["sp_tpo_ciclo"].as<float>(); }
    if (newjson.containsKey("sp_tpo_ativo"))    { sp_tpo_ativo = newjson["sp_tpo_ativo"].as<float>(); }
    if (newjson.containsKey("sp_tpo_inativo"))  { sp_tpo_inativo = newjson["sp_tpo_inativo"].as<float>(); }
    if (newjson.containsKey("zera_ciclo"))      { zera_ciclo = newjson["zera_ciclo"].as<int>(); }

    if(zera_ciclo==1) { tpo_ocioso=0;}            // se deve zerar o contador de ciclos, zera tbm tpo_ocioso
      
    root["tipo_maq"] = "218-PrensaSola";
    root["sp_press1"] = sp_p1;
    root["sp_press2"] = sp_p2;
    root["sp_p_vacuo"] = sp_pv;
    root["sp_tpo_p1"] = sp_tpo_p1;
    root["sp_tpo_p2"] = sp_tpo_p2;
    root["sp_modo"] = sp_modo;
    root["sp_tpo_ciclo"] = sp_tpo_ciclo;
    root["sp_tpo_ativo"] = sp_tpo_ativo;
    root["sp_tpo_inativo"] = sp_tpo_inativo;
    root["zera_ciclo"] = zera_ciclo;
    root["ciclos"] = ciclos;  
    root.printTo(str_data);
    
    server.send ( 200, "text/json", str_data );

    grava_regs();                                   // salva os novos valores nos registradores modbus
    salva_sps_EEPROM();                             // salva os setpoints na EEPROM
    
  });

  delay(1000);        // delay necessário para garantir que o beffer da serial foi esvaziado. O canal serial será reconfigurado para a 485.

  //EEPROM.begin(512);
  delay(50);
  //carrega_sps_EEPROM();
  delay(100);
/*
  sp_temp=222.2;
  sp1=11.1;
  sp2=22.2;
  sp3=33.3;
  sp4=44.4;
  sp5=5;
  sp6=6;
  salva_sps_EEPROM();
*/
  //Wire.begin();                      // inicializa a I2C (SDA=GPIO4, SCL=GPIO5)
  
  // setup da 485:
  // o arquivo SimpleModbusSlave.cpp da bilioteca modbus deve ser alterado:
  // LINHA 47 original: (*ModbusPort).begin(baud, byteFormat);          // não funciona com o Wemos
  // LINHA 47 alterada: (*ModbusPort).begin(baud, SERIAL_8E1);          // Marcelo - Alterado 20/12/2017

#ifndef DEBUGING
  //init_serial_modbus();
#endif

  //digitalWrite(4, HIGH);   // testa SDA
  //digitalWrite(5, HIGH);   // testa SCL

}

// grava os valores nos registradores modbus
void grava_regs(void)
{ // CARREGA OS REGISTRADORES MODBUS COM OS VALORES DE SETPOINTS
  unsigned int temp = (sp_pv*10);
  temp = temp & 0xFFFF;
  
  regs[SP_P1] = sp_p1*10;              // multiplica por 10 para passar para inteiro em decimo de SEGUNDO
  regs[SP_P2] = sp_p2*10;              // multiplica por 10 para passar para inteiro em decimo de SEGUNDO
  regs[SP_P_VACUO] = temp;              // multiplica por 10 para passar para inteiro em decimo de SEGUNDO
  regs[SP_TPO_P1] = sp_tpo_p1*10;              // multiplica por 10 para passar para inteiro em decimo de SEGUNDO
  regs[SP_TPO_P2] = sp_tpo_p2*10;              // multiplica por 10 para passar para inteiro em decimo de SEGUNDO
  regs[SP_MODO] = sp_modo;
  //regs[SP_TPO_CICLO] = sp_tpo_ciclo*10;              // multiplica por 10 para passar para inteiro em decimo de SEGUNDO
  //regs[SP_TPO_ATIVO] = sp_tpo_ativo*10;
  //regs[SP_TPO_INATIVO] = sp_tpo_inativo*10;
  regs[ZERA_CICLOS] = zera_ciclo;      // multiplica por 10 para passar para inteiro em decimo de °C 

  ciclos = regs[CICLOS];

  if(ciclos < 2)  { (zera_ciclo=0); }   // se ciclos for menor que 2, presume-se que contador foi zerado

  // 218 - VALORES BIT A BIT: EMERG=1, AGUARDA_INICIO=2, EM_PROG=4, EM_TRABALHO=8, DEFEITO_MICRO=16, DEFEITO_PROTEÇÃO_MÓVEL=32, PERDA_PRESSAO1=64, PERDA_PRESSAO2=128.
  if(regs[STATUS_MACH]!=8)
  {
    status_run = 0;
  }
  else
  {
    status_run = 1;
  }
  
}

unsigned char cont1 = 0;

void loop()
{
  // put your main code here, to run repeatedly:

  // adicionado em 07/12/2017:
  server.handleClient();
  WiFiClient client = server.client();
  if (client) {flag_client = 1;}
  //Wait until the client sends some data
  //Serial.println(numberOfInterrupts);

  // Measure Signal Strength (RSSI) of Wi-Fi connection
  pot_rssi = WiFi.RSSI();
  // calcula a qualidade do sinal em %
  if(pot_rssi>(-50))
  {
    qualidade_sinal = 100;                      // se atenuação for menor que -50dB, qualidade = 100%
  }
  else
  {
    qualidade_sinal = 2 * (pot_rssi + 100);     // calcula a qualidade do sinal em %
  }
  
  
  //Serial.print("Qualidade: ");
  //Serial.print(qualidade_sinal);
  //Serial.println("%");

#ifndef DEBUGING
  //if((millis()-t_last_request) > 100)
  if((millis()-t_last_request) > 1000)
  {
    //modbus_update();                          // send Master request to Slave, as defined above

    // verifica se a comunicação com o slave está ok
    if(serial_fail==1)
    {
      //Serial.flush();
      //init_serial_modbus();                 // se há problema de conexão com o slave, reconfigura a serial modbus     
    }
    
    t_last_request = millis();              // registra instante da última requisição

    /*
    tpo_ocioso = 15000/10.0;           // soma ao total do tempo ocioso, o tempo inativo do último ciclo
    T_ocioso_seg = tpo_ocioso;                       // copia para uma variável int, para eliminar casa decimal
    ConvertSegToTime(T_ocioso_seg, str_tpo_ocioso);    // converte segundos para formato hh:mm:ss
    */
    
    if (regs[CICLOS] > ciclos)              // verifica se incrementou contador de ciclos
    {
      tpo_ciclo = ((regs[TPO_ATIVO]/10.0) + (regs[TPO_INATIVO]/10.0));
      tpo_ocioso += (regs[TPO_INATIVO]/10.0);           // soma ao total do tempo ocioso, o tempo inativo do último ciclo
      T_ocioso_seg = tpo_ocioso;                                        // copia para uma variável int, para eliminar casa decimal
      ConvertSegToTime(T_ocioso_seg, str_tpo_ocioso);                   // converte segundos para formato hh:mm:ss
    }
    else
    {
      T_ocioso_seg = (tpo_ocioso+(regs[TPO_PARADA_ATUAL]));        // se não executou ciclo, soma o tempo da parada atual ao tempo ocioso
      ConvertSegToTime(T_ocioso_seg, str_tpo_ocioso);                   // converte segundos para formato hh:mm:ss
    }

    // verificação da comunicação com o CLP
    timerErrorCom++;
    if(timerErrorCom==30)
    {                                             // passaram 3 segundos desde última verificação?
      timerErrorCom=0;
      if(errorCount > (reg_erros_232+1))
      {                                           // verifica se ocorreu mais de um erro de requisição desde a última verificação
        regs[STATUS_MACH]=0;                      // caso tenham ocorridos erros na com. com CLP, força status em 0
        status_run=0;
      }
      reg_erros_232 = errorCount;
    }
    
    cont1 = contador(cont1);
    Serial.println(cont1+3);

  }
#endif

  //grava_regs();            // chama função que sobrescreve os valores nos registradores (CLP não deve alterar os valores. Apenas ler.)

  T_Loop = millis()-t_last_loop;
  t_last_loop=millis();
  
/* MÁQUINA 732 NÃO PRECISA DA I2C, PQ COMUNICA APENAS COM UM CLP CROUZET
  // verifica se deve comunicar com o slave I2C
  timerAux_i2c++;
  if (timerAux_i2c>50000)
  {
    //Counter=Counter+5;                                // contador para debug
    timerAux_i2c=0;                                   // zera temporizador
    getI2C_Data();                                    // chama função requisição i2c
  }
  else if (timerAux_i2c==5000)
  {
    sendI2C_Data();                                   // chama função envio do setpoint
  }
*/   
}

