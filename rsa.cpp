#include <iostream>
using std::cerr;
using std::cin;
using std::cout;
using std::endl;
using std::wcin;
using std::wcout;

#include <cmath>
#include <stdio.h>

#include <math.h>
#include <cstdlib>
#include <string>
using std::string;
using std::wstring;
#include <sstream>
using std::ostringstream;

#include <stdexcept>
using std::runtime_error;

#include <unordered_map>
#include <stdlib.h>
using namespace std;

#include <sstream>

#include "Cryptopp/integer.h"
#include "Cryptopp/algebra.h"
using CryptoPP::EuclideanDomainOf;

#include "Cryptopp/modarith.h"

#include "Cryptopp/nbtheory.h"
using CryptoPP::ModularExponentiation;
using CryptoPP::ModularMultiplication;

#include "Cryptopp/sha3.h"
using CryptoPP::SHA3_512;

#include "Cryptopp/queue.h"
using CryptoPP::ByteQueue;

#include "Cryptopp/files.h"
using CryptoPP::FileSink;
using CryptoPP::FileSource;

#include "Cryptopp/dsa.h"
using CryptoPP::DSA;

#include "Cryptopp/rsa.h"
using CryptoPP::InvertibleRSAFunction;
using CryptoPP::RSA;
using CryptoPP::RSASS;

#include "Cryptopp/base64.h"
using CryptoPP::Base64Decoder;
using CryptoPP::Base64Encoder;

#include "Cryptopp/cryptlib.h"
using CryptoPP::BufferedTransformation;
using CryptoPP::byte;
using CryptoPP::Integer;
using CryptoPP::PrivateKey;
using CryptoPP::PublicKey;
using CryptoPP::StringSink;
using CryptoPP::StringSource;

#include "Cryptopp/osrng.h"
using CryptoPP::AutoSeededRandomPool;

#include "Cryptopp/hex.h"
using CryptoPP::HexDecoder;
using CryptoPP::HexEncoder;

/* Convert string*/
#include <io.h>
#include <fcntl.h>

#include <locale>
using std::wstring_convert;
#include <codecvt>
using std::codecvt_utf8;

wstring integer_to_wstring(const CryptoPP::Integer &t)
{
   std::ostringstream oss;
   oss.str("");
   oss.clear();
   oss << t;
   std::string encoded(oss.str());
   std::wstring_convert<codecvt_utf8<wchar_t>> towstring;
   return towstring.from_bytes(encoded);
}
wstring string_to_wstring(const std::string &str)
{
   wstring_convert<codecvt_utf8<wchar_t>> towstring;
   return towstring.from_bytes(str);
}
string wstring_to_string(const std::wstring &str)
{
   wstring_convert<codecvt_utf8<wchar_t>> tostring;
   return tostring.to_bytes(str);
}
Integer wstring_to_integer(const std::wstring &wstr)
{
   stringstream sstream(wstring_to_string(wstr));
   Integer n;
   sstream >> n;
   return n;
}
typedef struct User
{  
  
   wstring Id_i, Pw_i;
   wstring tempCidi, tempBu, V1, V2, V3;
   Integer randB, randNu, tempNs, tempAu, Tu;
   Integer tempV4, tempTs, Sku;
   wstring Au, Bu;
   Integer e, n, h;
   bool isValid = false;
} Ui;

typedef struct Server
{
   wstring serverId_i, serverPw_i, serverAi;
   wstring Au, Bu, Cidi;
   Integer tempV1, tempNu, randNs, Ts, V4, Sks, d;
   Integer tempV2, tempV3, tempTu,n,e;


} Sj;

Integer generateRandomNumber()
{
   AutoSeededRandomPool prng;
   Integer n;
   CryptoPP::AlgorithmParameters params = CryptoPP::MakeParameters("BitLength", 3072)("RandomNumberType", Integer::PRIME);

   n.GenerateRandom(prng, params);
   return n;
}
Integer gcd(Integer a, Integer h)
{
   Integer temp;
   while (1)
   {
      temp = a % h;
      if (temp == 0)
         return h;
      a = h;
      h = temp;
   }
}

Integer sha3_512(string message)
{
   string digest, encode;
   wstring wsmessage = string_to_wstring(message);

   CryptoPP::SHA3_512 hash;

   hash.Restart();
   hash.Update((const byte *)message.data(), message.size());
   digest.resize(hash.DigestSize());
   hash.TruncatedFinal((byte *)&digest[0], digest.size());
   encode.clear();
   StringSource(digest, true,
                new HexEncoder(new StringSink(encode)));

   encode = encode + "h";

   const char *t = encode.c_str();
   Integer a(t);
   return a;
}
void Save(const string &filename, const BufferedTransformation &bt)
{
   
   FileSink file(filename.c_str());

   bt.CopyTo(file);
   file.MessageEnd();
}
//Hàm lưu private key
void SavePrivateKey(const string &filename, const PrivateKey &key)
{
  
   ByteQueue queue;
   key.Save(queue);

   Save(filename, queue);
}

//Hàm lưu public key
void SavePublicKey(const string &filename, const PublicKey &key)
{
 
   ByteQueue queue;
   key.Save(queue);

   Save(filename, queue);
}

void Load(const string &filename, BufferedTransformation &bt)
{
 
   FileSource file(filename.c_str(), true /*pumpAll*/);

   file.TransferTo(bt);
   bt.MessageEnd();
}

void LoadPrivateKey(const string &filename, PrivateKey &key)
{
   
   ByteQueue queue;

   Load(filename, queue);
   key.Load(queue);
}

void LoadPublicKey(const string &filename, PublicKey &key)
{
   
   ByteQueue queue;

   Load(filename, queue);
   key.Load(queue);
}

void generateKey(Integer &p, Integer &q, Integer &phi, Integer &n)
{
   AutoSeededRandomPool rnd;
   RSA::PrivateKey rsaPrivate;
   rsaPrivate.GenerateRandomWithKeySize(rnd, 3072);
   RSA::PublicKey rsaPublic(rsaPrivate);
   SavePrivateKey("pri.key", rsaPrivate);
   SavePublicKey("pub.key", rsaPublic);
   LoadPrivateKey("pri.key", rsaPrivate);
   LoadPublicKey("pub.key", rsaPublic);
   n = rsaPublic.GetModulus();

   p = rsaPrivate.GetPrime1();

   q = rsaPrivate.GetPrime2();
   phi = (p - 1) * (q - 1);
}
Integer generateDforServer(Integer phi, Integer &e)
{
   Integer d;
   Integer k = 1;
   e = 2;
   while (e < phi)
   {
      if (gcd(e, phi) == 1)
         break;
      else
         e++;
   }
   while (1)
   {
      k = k + phi;

      if (k % e == 0)
      {
         d = (k / e);
         break;
      }
   }
   return d;
}

void registrationPhase(User &ui, Server &sj)
{
    wcout << "||---------- REGISTRATION PHASE ----------||" <<endl;

   wcout << "||----- Create your ID: " << endl;
   getline(wcin, ui.Id_i);
   wcout << "||----- Create your password: " << endl;
   getline(wcin, ui.Pw_i);
   ui.randB = generateRandomNumber();
   wstring showB = integer_to_wstring(ui.randB);
  wcout << "||----- Random number b: " << showB << endl;
   wstring temp1 = ui.Pw_i + integer_to_wstring(ui.randB);
   wstring Ai;
   Ai = integer_to_wstring(sha3_512(wstring_to_string(temp1)));
   
   wcout << "Ai = h(Pwi||b)..." <<Ai << endl;
   wcout<<"sending AI and ID to server"<<endl;
   sj.serverAi = Ai;
   sj.serverId_i = ui.Id_i;
   sj.serverPw_i = ui.Pw_i;
   Integer p, q, phi;

   wcout << "Server computing........." << endl;
   generateKey(p, q, phi, sj.n);
  
   wcout <<"||----- Private prime number p: "  << integer_to_wstring(p) << endl;
   wcout << "||----- Private prime number q: " << integer_to_wstring(q) << endl;
    wcout <<"||----- Public modulo n: "  << integer_to_wstring(sj.n) << endl;
   wcout << "||----- Phi: " << integer_to_wstring(phi) << endl;
   sj.d = generateDforServer(phi, sj.e);
   wcout <<"||----- d: " << integer_to_wstring(sj.d) << endl;
   wcout <<  "||----- e: " << integer_to_wstring(sj.e) << endl;
   wstring temp2 = sj.serverId_i + integer_to_wstring(sj.d);
   Integer integerCidi = sha3_512(wstring_to_string(temp2));
   sj.Cidi = integer_to_wstring(integerCidi);
   wcout <<  "||Calculating Cidi = h(ID_i||d)..." << sj.Cidi << endl;
   Integer temp6 = sha3_512(wstring_to_string(sj.serverAi + sj.serverId_i));
  
   Integer integerAu = integerCidi ^ temp6;
   sj.Au = integer_to_wstring(integerAu);
   wcout << "||Calculating Au = Cidi ^ h(Ai||ID_i):" << sj.Au << endl;
   Integer integerBu = sha3_512(wstring_to_string(sj.Cidi + sj.serverAi + sj.serverId_i));
   sj.Bu = integer_to_wstring(integerBu);
   wcout <<"||Calculating Bu = h(Cidi||Ai||ID_i)..." << sj.Bu << endl;
 
  

   ui.Au = sj.Au;
   ui.Bu = sj.Bu;
   ui.e = sj.e;
   ui.n = sj.n;
   Integer temp5 = wstring_to_integer(sj.serverId_i) ^ wstring_to_integer(sj.serverPw_i);
   
   Integer shaIdPw = sha3_512(wstring_to_string(integer_to_wstring(temp5)));
 
   ui.h = shaIdPw ^ ui.randB;
   wcout<<"||----- h(Id_i Xor Pw_i) xor b:"<<integer_to_wstring(ui.h) <<endl;
   wcout << "Storing Au,Bu,e,n,h(Id_i Xor Pw_i) xor b  into smart card for user" << endl;
   wcout << "register successfully" << endl;

   wcout << "----------------------------------" << endl;
}
void showStoringInSc(User ui){
   wcout<<"Showing Storing in Sc"<<endl;

   wcout<<"Au:"<<ui.Au<<endl;
   wcout<<"Bu:"<<ui.Bu<<endl;
   wcout<<"n:"<<integer_to_wstring(ui.n)<<endl;
   wcout<<"e:"<<integer_to_wstring(ui.e)<<endl;
   wcout<<"h(Id_i Xor Pw_i) xor b:"<<integer_to_wstring(ui.h)<<endl;



}
void loginPhase(User &ui, Server &sj)
{
  wcout << "||---------- LOGIN PHASE ----------||" <<endl;
   if (wstring_to_string(ui.Id_i) == "" || wstring_to_string(ui.Pw_i) == "")
   {
      wcout << ">>> This user is not register" << endl;
      return;
   }
   wstring x, y;
   wcout << ">>> Input your ID (Idi): ";
  
   getline(wcin, x);
   wcout << ">>> Input your password (Pwi): ";
 
   getline(wcin, y);
   wcout << "||----- Your user ID:" << x << endl;
   wcout <<"||----- Your password: " << y << endl;
   wcout << ">>> Recovering b ..." << endl;
   Integer b;
  
   Integer temp1 = wstring_to_integer(x) ^ wstring_to_integer(y);
  
   temp1 = sha3_512(wstring_to_string(integer_to_wstring(temp1)));

   b = wstring_to_integer(integer_to_wstring(ui.h)) ^ temp1;

   wcout << "||Calculating b =h(Idi||Pwi) ^ b ^ h(Idi||Pwi)..." << integer_to_wstring(b) << endl;
  

   wstring temp2 = y + integer_to_wstring(b);
   Integer Ai = sha3_512(wstring_to_string(temp2));
   wcout << "||Calculating Ai = h(Pwi||b)..." << integer_to_wstring(Ai) << endl;
   wstring temp3 = integer_to_wstring(Ai) + x;
   temp3 = integer_to_wstring(sha3_512(wstring_to_string(temp3)));
   // wcout << "temp3:" << temp3 << endl;
   Integer Cidi = wstring_to_integer(ui.Au) ^ wstring_to_integer(temp3);

   wcout << "||Calculating Cidi = Au ^ h(Ai||Idi)..." << integer_to_wstring(Cidi) << endl;
   string temp4 = wstring_to_string(integer_to_wstring(Cidi) + integer_to_wstring(Ai) + x);
   wstring Bu = integer_to_wstring(sha3_512(temp4));
   wcout << "||Calculating h(Cidi||Ai||Idi) = Bu..."  << Bu << endl;
   wcout << "Verifing Bu" << endl;
   if (ui.Bu != Bu)
   {
      wcout << "Verify not success" << endl;
      return;
   }
   wcout<<"user Bu == compute Bu"<<endl;
   ui.randNu = generateRandomNumber();

   wcout <<"Nu:" << integer_to_wstring(ui.randNu) << endl;
   Integer v1 = wstring_to_integer(temp3) ^ ui.randNu;
   wcout << "||Calculating V1 = h(Ai||Idi) ^ Nu..." << integer_to_wstring(v1) << endl;
   wstring temp5 = integer_to_wstring(Cidi) + ui.Au;
   wcout << "|| (Cidi||Au) = " << temp5 <<endl;
   // wcout << "Cidi+Au" << temp5 << endl;
   // wcout<<"e:"<<integer_to_wstring(ui.e)<<endl;
   Integer v2 = EuclideanDomainOf<Integer>().Exponentiate(wstring_to_integer(temp5), ui.e);
   wcout <<  "||Calculating V2 =(Cidi||Au) powar e..."  << integer_to_wstring(v2) << endl;
   time_t time_stamp;
   time_stamp = time(NULL);
   ui.Tu = time_stamp;
   wstring temp6 = integer_to_wstring(Cidi) + integer_to_wstring(ui.randNu) + integer_to_wstring(ui.Tu);
   Integer v3 = sha3_512(wstring_to_string(temp6));
   wcout <<  "||Calculating V3 = h(Cidi||Nu||Tu)..."  << integer_to_wstring(v3) << endl;
   wcout << ">>> Sending V1,V2,V3,Tu to server" << endl;
   sj.tempV1 = v1;
   sj.tempV2 = v2;
   sj.tempV3 = v3;
   sj.tempTu = ui.Tu;
    wcout << "||------- LOGIN SUCCESS! -------||" <<endl;
}
void authenticationUserPhase(Server &sj, User &ui)
{
   wcout << "||---------- USER AUTHENTICATION PHASE ----------||" <<endl;
   if (sj.tempTu != ui.Tu)
   {
      wcout << "time-stamp is invalid" << endl;
      return;
   }
   wcout << ">>> time-stamp checked" << endl;
  
  
   Integer v2ExpoD = ModularExponentiation(sj.tempV2, sj.d, sj.n);
  
   wstring v2CidiAu = sj.Cidi + sj.Au;
   wcout <<"||----- v2^d= (Cidi||Au):" << integer_to_wstring(v2ExpoD) << endl;
   
   Integer hashAiId = sha3_512(wstring_to_string(sj.serverAi + sj.serverId_i));
   wcout << "h(Ai||Id):" << integer_to_wstring(hashAiId) << endl;
   Integer CidiXorAu = wstring_to_integer(sj.Cidi) ^ wstring_to_integer(sj.Au);

   wcout << "||----- Cidi ^ Au:" << integer_to_wstring(CidiXorAu) << endl;
   Integer Nu = sj.tempV1 ^ hashAiId;
   wcout << "||Calculating V1 ^ h(Ai||Idi) = Nu: " << integer_to_wstring(Nu) << endl;
   wstring temp1 = sj.Cidi + integer_to_wstring(Nu) + integer_to_wstring(sj.tempTu);
   Integer v3 = sha3_512(wstring_to_string(temp1));
   wcout << ">>> Verify V3* = h(Cidi||Nu||Tu) = V3 " << integer_to_wstring(v3) << endl;
   if (sj.tempV3 != v3)
   {
      wcout << ">>> User not authenticate" << endl;

      sj.V4 = -1;
      ui.tempV4 = sj.V4;
      return;
   }
   wcout << ">>> User is authenticated" << endl;

   sj.randNs = generateRandomNumber();
   wcout <<  "||----- Ns:" << integer_to_wstring(sj.randNs) << endl;
   time_t time_stamp;
   time_stamp = time(NULL);
   sj.Ts = time_stamp;
   wstring temp2 = integer_to_wstring(sj.randNs) + integer_to_wstring(Nu) + integer_to_wstring(sj.tempTu) + integer_to_wstring(sj.Ts);

   sj.Sks = sha3_512(wstring_to_string(temp2));
   wcout <<"||Calculating Sks = h(Ns||Nu|Tu||Ts)..." << integer_to_wstring(sj.Sks) << endl;
   sj.V4 = sj.randNs ^ Nu ^ wstring_to_integer(sj.Cidi);
   wcout <<"||Calculating V4 = Ns ^ Nu ^ Cidi..." << integer_to_wstring(sj.V4) << endl;
   wcout <<  ">>> sending v4 and Ts to user"  << endl;
   ui.tempV4 = sj.V4;
   ui.tempTs = sj.Ts;
   ui.isValid = true;
}
void authenticateServerPhase(Server &sj, User &ui)
{
   Integer Ns = ui.tempV4 ^ ui.randNu ^ wstring_to_integer(sj.Cidi);
   wcout <<"||Calculating Ns* = V4 ^ Nu ^ Cidi..." << integer_to_wstring(Ns) << endl;
   Integer v4 = Ns ^ ui.randNu ^ wstring_to_integer(sj.Cidi);
   wcout <<"||Calculating V4* = Ns* ^ Nu ^ Cidi..." << integer_to_wstring(v4) << endl;
   // wcout << "v4 of ui:" << integer_to_wstring(ui.tempV4) << endl;
   if (v4 != ui.tempV4)
   {
      wcout << "authenticate server failed" << endl;
      return;
   }
   wcout<<"User authenticated server success"<<endl;
   wcout << "computing Sku" << endl;
   wstring temp1 = integer_to_wstring(Ns) + integer_to_wstring(ui.randNu) + integer_to_wstring(ui.Tu) + integer_to_wstring(sj.Ts);
   ui.Sku = sha3_512(wstring_to_string(temp1));
   wcout <<"||Sku = h(Ns||Nu||Tu||Ts) = Sks..." << integer_to_wstring(ui.Sku) << endl;
}
void changePasswordPhase(User &ui, Server &sj)
{
   wcout << "----------Change password----------" << endl;
   if (ui.isValid == false)
   {
      wcout << "You not a valid user" << endl;
      return;
   }
   wstring id, password, newPassword;
   wcout << "Enter id" << endl;
   getline(wcin, id);
   wcout << "Enter password" << endl;
   getline(wcin, password);
   // loginPhase(ui,sj);
   wcout << "Enter new password" << endl;
   getline(wcin, newPassword);
   Integer Ai;
   wstring temp1 = password + integer_to_wstring(ui.randB);
   Ai = sha3_512(wstring_to_string(temp1));
   wcout << "Ai = h(P wi||b):" << integer_to_wstring(Ai) << endl;

   Integer Cidi;
   wstring temp2 = integer_to_wstring(Ai) + id;
   Cidi = wstring_to_integer(sj.Au) ^ sha3_512(wstring_to_string(temp2));
   wcout << " Cidi =Au ^ h(Ai||I di):" << integer_to_wstring(Cidi) << endl;
   Integer hashCidiAiId;
   wstring temp3 = integer_to_wstring(Cidi) + integer_to_wstring(Ai) + id;
   hashCidiAiId = sha3_512(wstring_to_string(temp3));
   // wcout << "hashCidiAiId:" << integer_to_wstring(hashCidiAiId) << endl;
   Integer AiNew;
   wstring temp4 = newPassword + integer_to_wstring(ui.randB);
   AiNew = sha3_512(wstring_to_string(temp4));
   wcout << "Ai_new=h(pw_new || b)" << integer_to_wstring(AiNew) << endl;
   Integer CidiNew;
   wstring temp5 = integer_to_wstring(AiNew) + id;
   CidiNew = wstring_to_integer(sj.Au) ^ sha3_512(wstring_to_string(temp5));
   wcout<<"Cidi_new=h(Pw_new || b):"<<integer_to_wstring(CidiNew)<<endl;
   Integer BuNew;
   wstring temp6 = integer_to_wstring(CidiNew) + integer_to_wstring(AiNew) + id;
   BuNew = sha3_512(wstring_to_string(temp6));
   wcout << "Bu_new=h(Cidi_new || Ai_new||Id)" << integer_to_wstring(BuNew) << endl;

   ui.Bu = integer_to_wstring(BuNew);
   ui.Pw_i = newPassword;
   Integer newH;
   Integer temp7 = wstring_to_integer(ui.Id_i) ^ wstring_to_integer(ui.Pw_i);
   newH = sha3_512(wstring_to_string(integer_to_wstring(temp7))) ^ ui.randB;
   wcout << "new h:" << integer_to_wstring(newH) << endl;
   ui.h = newH;
   sj.Cidi=integer_to_wstring(CidiNew);
   sj.serverAi=integer_to_wstring (AiNew);
   wcout << "Change password successfully" << endl;
}

int main()
{

   Ui ui;
   Server sj;
 
   registrationPhase(ui,sj);
   showStoringInSc(ui);
   loginPhase(ui,sj);
   authenticationUserPhase(sj,ui);
   authenticateServerPhase(sj,ui);
   changePasswordPhase(ui,sj);
   loginPhase(ui,sj);
   authenticationUserPhase(sj,ui);
   authenticateServerPhase(sj,ui);
   
   return 0;
}