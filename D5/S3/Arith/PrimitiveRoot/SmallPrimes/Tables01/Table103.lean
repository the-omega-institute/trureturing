/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table103
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table103.pv429599
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table013
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table018
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table028
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table069

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr429599 : PrimeCertificate 429599 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv31,pv41]) (by decide +kernel)
def pv429599 : PrimeValue := ⟨429599, pr429599⟩
private theorem pr429643 : PrimeCertificate 429643 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23869]) (by decide +kernel)
def pv429643 : PrimeValue := ⟨429643, pr429643⟩
private theorem pr429673 : PrimeCertificate 429673 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17903]) (by decide +kernel)
def pv429673 : PrimeValue := ⟨429673, pr429673⟩
private theorem pr429683 : PrimeCertificate 429683 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv19531]) (by decide +kernel)
def pv429683 : PrimeValue := ⟨429683, pr429683⟩
private theorem pr429701 : PrimeCertificate 429701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv4297]) (by decide +kernel)
def pv429701 : PrimeValue := ⟨429701, pr429701⟩
private theorem pr429731 : PrimeCertificate 429731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv877]) (by decide +kernel)
def pv429731 : PrimeValue := ⟨429731, pr429731⟩
private theorem pr429733 : PrimeCertificate 429733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv173]) (by decide +kernel)
def pv429733 : PrimeValue := ⟨429733, pr429733⟩
private theorem pr429797 : PrimeCertificate 429797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv107449]) (by decide +kernel)
def pv429797 : PrimeValue := ⟨429797, pr429797⟩
private theorem pr429823 : PrimeCertificate 429823 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23879]) (by decide +kernel)
def pv429823 : PrimeValue := ⟨429823, pr429823⟩
private theorem pr429827 : PrimeCertificate 429827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv214913]) (by decide +kernel)
def pv429827 : PrimeValue := ⟨429827, pr429827⟩
private theorem pr429853 : PrimeCertificate 429853 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv113,pv317]) (by decide +kernel)
def pv429853 : PrimeValue := ⟨429853, pr429853⟩
private theorem pr429881 : PrimeCertificate 429881 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv11,pv977]) (by decide +kernel)
def pv429881 : PrimeValue := ⟨429881, pr429881⟩
private theorem pr429887 : PrimeCertificate 429887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv214943]) (by decide +kernel)
def pv429887 : PrimeValue := ⟨429887, pr429887⟩
private theorem pr429899 : PrimeCertificate 429899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv30707]) (by decide +kernel)
def pv429899 : PrimeValue := ⟨429899, pr429899⟩
private theorem pr429907 : PrimeCertificate 429907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv137,pv523]) (by decide +kernel)
def pv429907 : PrimeValue := ⟨429907, pr429907⟩
private theorem pr429911 : PrimeCertificate 429911 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv13,pv3307]) (by decide +kernel)
def pv429911 : PrimeValue := ⟨429911, pr429911⟩
private theorem pr429937 : PrimeCertificate 429937 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13,pv53]) (by decide +kernel)
def pv429937 : PrimeValue := ⟨429937, pr429937⟩
private theorem pr429943 : PrimeCertificate 429943 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv131,pv547]) (by decide +kernel)
def pv429943 : PrimeValue := ⟨429943, pr429943⟩
private theorem pr429953 : PrimeCertificate 429953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3359]) (by decide +kernel)
def pv429953 : PrimeValue := ⟨429953, pr429953⟩
private theorem pr429971 : PrimeCertificate 429971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv31,pv73]) (by decide +kernel)
def pv429971 : PrimeValue := ⟨429971, pr429971⟩
private theorem pr430013 : PrimeCertificate 430013 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv29,pv337]) (by decide +kernel)
def pv430013 : PrimeValue := ⟨430013, pr430013⟩
private theorem pr430019 : PrimeCertificate 430019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv211,pv1019]) (by decide +kernel)
def pv430019 : PrimeValue := ⟨430019, pr430019⟩
private theorem pr430091 : PrimeCertificate 430091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41,pv1049]) (by decide +kernel)
def pv430091 : PrimeValue := ⟨430091, pr430091⟩
private theorem pr430277 : PrimeCertificate 430277 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11,pv127]) (by decide +kernel)
def pv430277 : PrimeValue := ⟨430277, pr430277⟩
private theorem pr430289 : PrimeCertificate 430289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv26893]) (by decide +kernel)
def pv430289 : PrimeValue := ⟨430289, pr430289⟩
private theorem pr430343 : PrimeCertificate 430343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv31,pv631]) (by decide +kernel)
def pv430343 : PrimeValue := ⟨430343, pr430343⟩
private theorem pr430357 : PrimeCertificate 430357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv35863]) (by decide +kernel)
def pv430357 : PrimeValue := ⟨430357, pr430357⟩
private theorem pr430453 : PrimeCertificate 430453 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv1087]) (by decide +kernel)
def pv430453 : PrimeValue := ⟨430453, pr430453⟩
private theorem pr430487 : PrimeCertificate 430487 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv97,pv317]) (by decide +kernel)
def pv430487 : PrimeValue := ⟨430487, pr430487⟩
private theorem pr430513 : PrimeCertificate 430513 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv8969]) (by decide +kernel)
def pv430513 : PrimeValue := ⟨430513, pr430513⟩
private theorem pr430517 : PrimeCertificate 430517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv2503]) (by decide +kernel)
def pv430517 : PrimeValue := ⟨430517, pr430517⟩
private theorem pr430543 : PrimeCertificate 430543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv17,pv67]) (by decide +kernel)
def pv430543 : PrimeValue := ⟨430543, pr430543⟩
private theorem pr430571 : PrimeCertificate 430571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv6151]) (by decide +kernel)
def pv430571 : PrimeValue := ⟨430571, pr430571⟩
private theorem pr430589 : PrimeCertificate 430589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv107647]) (by decide +kernel)
def pv430589 : PrimeValue := ⟨430589, pr430589⟩
private theorem pr430601 : PrimeCertificate 430601 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv2153]) (by decide +kernel)
def pv430601 : PrimeValue := ⟨430601, pr430601⟩
private theorem pr430649 : PrimeCertificate 430649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv53831]) (by decide +kernel)
def pv430649 : PrimeValue := ⟨430649, pr430649⟩
private theorem pr430663 : PrimeCertificate 430663 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv71777]) (by decide +kernel)
def pv430663 : PrimeValue := ⟨430663, pr430663⟩
private theorem pr430691 : PrimeCertificate 430691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv3313]) (by decide +kernel)
def pv430691 : PrimeValue := ⟨430691, pr430691⟩
private theorem pr430723 : PrimeCertificate 430723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23929]) (by decide +kernel)
def pv430723 : PrimeValue := ⟨430723, pr430723⟩
private theorem pr430739 : PrimeCertificate 430739 :=
  certifyPrime (q := pv17) (ls := [pv2,pv7,pv11,pv2797]) (by decide +kernel)
def pv430739 : PrimeValue := ⟨430739, pr430739⟩
private theorem pr430747 : PrimeCertificate 430747 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv41,pv103]) (by decide +kernel)
def pv430747 : PrimeValue := ⟨430747, pr430747⟩
private theorem pr430799 : PrimeCertificate 430799 :=
  certifyPrime (q := pv13) (ls := [pv2,pv215399]) (by decide +kernel)
def pv430799 : PrimeValue := ⟨430799, pr430799⟩
private theorem pr430819 : PrimeCertificate 430819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv59,pv1217]) (by decide +kernel)
def pv430819 : PrimeValue := ⟨430819, pr430819⟩
private theorem pr430823 : PrimeCertificate 430823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv30773]) (by decide +kernel)
def pv430823 : PrimeValue := ⟨430823, pr430823⟩
private theorem pr430891 : PrimeCertificate 430891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv53,pv271]) (by decide +kernel)
def pv430891 : PrimeValue := ⟨430891, pr430891⟩
private theorem pr430909 : PrimeCertificate 430909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv149,pv241]) (by decide +kernel)
def pv430909 : PrimeValue := ⟨430909, pr430909⟩
private theorem pr430949 : PrimeCertificate 430949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv15391]) (by decide +kernel)
def pv430949 : PrimeValue := ⟨430949, pr430949⟩
private theorem pr430957 : PrimeCertificate 430957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11971]) (by decide +kernel)
def pv430957 : PrimeValue := ⟨430957, pr430957⟩
private theorem pr431021 : PrimeCertificate 431021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv937]) (by decide +kernel)
def pv431021 : PrimeValue := ⟨431021, pr431021⟩
private theorem pr431063 : PrimeCertificate 431063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv215531]) (by decide +kernel)
def pv431063 : PrimeValue := ⟨431063, pr431063⟩
private theorem pr431077 : PrimeCertificate 431077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv35923]) (by decide +kernel)
def pv431077 : PrimeValue := ⟨431077, pr431077⟩
private theorem pr431107 : PrimeCertificate 431107 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv5527]) (by decide +kernel)
def pv431107 : PrimeValue := ⟨431107, pr431107⟩
private theorem pr431141 : PrimeCertificate 431141 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv21557]) (by decide +kernel)
def pv431141 : PrimeValue := ⟨431141, pr431141⟩
private theorem pr431153 : PrimeCertificate 431153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv26947]) (by decide +kernel)
def pv431153 : PrimeValue := ⟨431153, pr431153⟩
private theorem pr431191 : PrimeCertificate 431191 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv1597]) (by decide +kernel)
def pv431191 : PrimeValue := ⟨431191, pr431191⟩
private theorem pr431203 : PrimeCertificate 431203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv71867]) (by decide +kernel)
def pv431203 : PrimeValue := ⟨431203, pr431203⟩
private theorem pr431213 : PrimeCertificate 431213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67,pv1609]) (by decide +kernel)
def pv431213 : PrimeValue := ⟨431213, pr431213⟩
private theorem pr431237 : PrimeCertificate 431237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv8293]) (by decide +kernel)
def pv431237 : PrimeValue := ⟨431237, pr431237⟩
private theorem pr431267 : PrimeCertificate 431267 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv19603]) (by decide +kernel)
def pv431267 : PrimeValue := ⟨431267, pr431267⟩
private theorem pr431269 : PrimeCertificate 431269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv83,pv433]) (by decide +kernel)
def pv431269 : PrimeValue := ⟨431269, pr431269⟩
private theorem pr431363 : PrimeCertificate 431363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv215681]) (by decide +kernel)
def pv431363 : PrimeValue := ⟨431363, pr431363⟩
private theorem pr431369 : PrimeCertificate 431369 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv7703]) (by decide +kernel)
def pv431369 : PrimeValue := ⟨431369, pr431369⟩
private theorem pr431377 : PrimeCertificate 431377 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv19,pv43]) (by decide +kernel)
def pv431377 : PrimeValue := ⟨431377, pr431377⟩
private theorem pr431399 : PrimeCertificate 431399 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv19609]) (by decide +kernel)
def pv431399 : PrimeValue := ⟨431399, pr431399⟩
private theorem pr431447 : PrimeCertificate 431447 :=
  certifyPrime (q := pv5) (ls := [pv2,pv215723]) (by decide +kernel)
def pv431447 : PrimeValue := ⟨431447, pr431447⟩
private theorem pr431521 : PrimeCertificate 431521 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv29,pv31]) (by decide +kernel)
def pv431521 : PrimeValue := ⟨431521, pr431521⟩
private theorem pr431533 : PrimeCertificate 431533 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11987]) (by decide +kernel)
def pv431533 : PrimeValue := ⟨431533, pr431533⟩
private theorem pr431581 : PrimeCertificate 431581 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7193]) (by decide +kernel)
def pv431581 : PrimeValue := ⟨431581, pr431581⟩
private theorem pr431603 : PrimeCertificate 431603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv215801]) (by decide +kernel)
def pv431603 : PrimeValue := ⟨431603, pr431603⟩
private theorem pr431617 : PrimeCertificate 431617 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv281]) (by decide +kernel)
def pv431617 : PrimeValue := ⟨431617, pr431617⟩
private theorem pr431729 : PrimeCertificate 431729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv223]) (by decide +kernel)
def pv431729 : PrimeValue := ⟨431729, pr431729⟩
private theorem pr431731 : PrimeCertificate 431731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv41]) (by decide +kernel)
def pv431731 : PrimeValue := ⟨431731, pr431731⟩
private theorem pr431797 : PrimeCertificate 431797 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv35983]) (by decide +kernel)
def pv431797 : PrimeValue := ⟨431797, pr431797⟩
private theorem pr431807 : PrimeCertificate 431807 :=
  certifyPrime (q := pv5) (ls := [pv2,pv43,pv5021]) (by decide +kernel)
def pv431807 : PrimeValue := ⟨431807, pr431807⟩
private theorem pr431857 : PrimeCertificate 431857 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2999]) (by decide +kernel)
def pv431857 : PrimeValue := ⟨431857, pr431857⟩
private theorem pr431867 : PrimeCertificate 431867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv181,pv1193]) (by decide +kernel)
def pv431867 : PrimeValue := ⟨431867, pr431867⟩
private theorem pr431891 : PrimeCertificate 431891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv43189]) (by decide +kernel)
def pv431891 : PrimeValue := ⟨431891, pr431891⟩
private theorem pr431903 : PrimeCertificate 431903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv12703]) (by decide +kernel)
def pv431903 : PrimeValue := ⟨431903, pr431903⟩
private theorem pr431929 : PrimeCertificate 431929 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv7,pv857]) (by decide +kernel)
def pv431929 : PrimeValue := ⟨431929, pr431929⟩
private theorem pr431933 : PrimeCertificate 431933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv83,pv1301]) (by decide +kernel)
def pv431933 : PrimeValue := ⟨431933, pr431933⟩
private theorem pr431947 : PrimeCertificate 431947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv421]) (by decide +kernel)
def pv431947 : PrimeValue := ⟨431947, pr431947⟩
private theorem pr431983 : PrimeCertificate 431983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv103,pv233]) (by decide +kernel)
def pv431983 : PrimeValue := ⟨431983, pr431983⟩
private theorem pr432007 : PrimeCertificate 432007 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv89,pv809]) (by decide +kernel)
def pv432007 : PrimeValue := ⟨432007, pr432007⟩
private theorem pr432023 : PrimeCertificate 432023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv11369]) (by decide +kernel)
def pv432023 : PrimeValue := ⟨432023, pr432023⟩
private theorem pr432037 : PrimeCertificate 432037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv1091]) (by decide +kernel)
def pv432037 : PrimeValue := ⟨432037, pr432037⟩
private theorem pr432043 : PrimeCertificate 432043 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv29,pv191]) (by decide +kernel)
def pv432043 : PrimeValue := ⟨432043, pr432043⟩
private theorem pr432053 : PrimeCertificate 432053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv108013]) (by decide +kernel)
def pv432053 : PrimeValue := ⟨432053, pr432053⟩
private theorem pr432059 : PrimeCertificate 432059 :=
  certifyPrime (q := pv23) (ls := [pv2,pv11,pv41,pv479]) (by decide +kernel)
def pv432059 : PrimeValue := ⟨432059, pr432059⟩
private theorem pr432067 : PrimeCertificate 432067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv107,pv673]) (by decide +kernel)
def pv432067 : PrimeValue := ⟨432067, pr432067⟩
private theorem pr432149 : PrimeCertificate 432149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv108037]) (by decide +kernel)
def pv432149 : PrimeValue := ⟨432149, pr432149⟩
private theorem pr432161 : PrimeCertificate 432161 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv37,pv73]) (by decide +kernel)
def pv432161 : PrimeValue := ⟨432161, pr432161⟩
private theorem pr432203 : PrimeCertificate 432203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv6971]) (by decide +kernel)
def pv432203 : PrimeValue := ⟨432203, pr432203⟩
private theorem pr432227 : PrimeCertificate 432227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv216113]) (by decide +kernel)
def pv432227 : PrimeValue := ⟨432227, pr432227⟩
private theorem pr432251 : PrimeCertificate 432251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv13,pv19]) (by decide +kernel)
def pv432251 : PrimeValue := ⟨432251, pr432251⟩
private theorem pr432277 : PrimeCertificate 432277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv17,pv163]) (by decide +kernel)
def pv432277 : PrimeValue := ⟨432277, pr432277⟩
private theorem pr432281 : PrimeCertificate 432281 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv101,pv107]) (by decide +kernel)
def pv432281 : PrimeValue := ⟨432281, pr432281⟩
private theorem pr432287 : PrimeCertificate 432287 :=
  certifyPrime (q := pv5) (ls := [pv2,pv331,pv653]) (by decide +kernel)
def pv432287 : PrimeValue := ⟨432287, pr432287⟩
private theorem pr432317 : PrimeCertificate 432317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv108079]) (by decide +kernel)
def pv432317 : PrimeValue := ⟨432317, pr432317⟩
private theorem pr432323 : PrimeCertificate 432323 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv43,pv457]) (by decide +kernel)
def pv432323 : PrimeValue := ⟨432323, pr432323⟩
private theorem pr432337 : PrimeCertificate 432337 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv9007]) (by decide +kernel)
def pv432337 : PrimeValue := ⟨432337, pr432337⟩
private theorem pr432343 : PrimeCertificate 432343 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv24019]) (by decide +kernel)
def pv432343 : PrimeValue := ⟨432343, pr432343⟩
private theorem pr432373 : PrimeCertificate 432373 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv137,pv263]) (by decide +kernel)
def pv432373 : PrimeValue := ⟨432373, pr432373⟩
private theorem pr432401 : PrimeCertificate 432401 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv23,pv47]) (by decide +kernel)
def pv432401 : PrimeValue := ⟨432401, pr432401⟩
private theorem pr432413 : PrimeCertificate 432413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv6359]) (by decide +kernel)
def pv432413 : PrimeValue := ⟨432413, pr432413⟩
private theorem pr432457 : PrimeCertificate 432457 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv37,pv487]) (by decide +kernel)
def pv432457 : PrimeValue := ⟨432457, pr432457⟩
private theorem pr432479 : PrimeCertificate 432479 :=
  certifyPrime (q := pv11) (ls := [pv2,pv19,pv599]) (by decide +kernel)
def pv432479 : PrimeValue := ⟨432479, pr432479⟩
private theorem pr432491 : PrimeCertificate 432491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv61,pv709]) (by decide +kernel)
def pv432491 : PrimeValue := ⟨432491, pr432491⟩
private theorem pr432527 : PrimeCertificate 432527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv216263]) (by decide +kernel)
def pv432527 : PrimeValue := ⟨432527, pr432527⟩
private theorem pr432559 : PrimeCertificate 432559 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv3433]) (by decide +kernel)
def pv432559 : PrimeValue := ⟨432559, pr432559⟩
private theorem pr432569 : PrimeCertificate 432569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv139,pv389]) (by decide +kernel)
def pv432569 : PrimeValue := ⟨432569, pr432569⟩
private theorem pr432589 : PrimeCertificate 432589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv47,pv59]) (by decide +kernel)
def pv432589 : PrimeValue := ⟨432589, pr432589⟩
private theorem pr432631 : PrimeCertificate 432631 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv11,pv19,pv23]) (by decide +kernel)
def pv432631 : PrimeValue := ⟨432631, pr432631⟩
private theorem pr432659 : PrimeCertificate 432659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv216329]) (by decide +kernel)
def pv432659 : PrimeValue := ⟨432659, pr432659⟩
private theorem pr432743 : PrimeCertificate 432743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv216371]) (by decide +kernel)
def pv432743 : PrimeValue := ⟨432743, pr432743⟩
private theorem pr432749 : PrimeCertificate 432749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv108187]) (by decide +kernel)
def pv432749 : PrimeValue := ⟨432749, pr432749⟩
private theorem pr432781 : PrimeCertificate 432781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7213]) (by decide +kernel)
def pv432781 : PrimeValue := ⟨432781, pr432781⟩
private theorem pr432797 : PrimeCertificate 432797 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv13,pv29,pv41]) (by decide +kernel)
def pv432797 : PrimeValue := ⟨432797, pr432797⟩
private theorem pr432847 : PrimeCertificate 432847 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv139,pv173]) (by decide +kernel)
def pv432847 : PrimeValue := ⟨432847, pr432847⟩
private theorem pr432893 : PrimeCertificate 432893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv108223]) (by decide +kernel)
def pv432893 : PrimeValue := ⟨432893, pr432893⟩
private theorem pr432923 : PrimeCertificate 432923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv17,pv107]) (by decide +kernel)
def pv432923 : PrimeValue := ⟨432923, pr432923⟩
private theorem pr432983 : PrimeCertificate 432983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv19681]) (by decide +kernel)
def pv432983 : PrimeValue := ⟨432983, pr432983⟩
private theorem pr432989 : PrimeCertificate 432989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv108247]) (by decide +kernel)
def pv432989 : PrimeValue := ⟨432989, pr432989⟩
private theorem pr433033 : PrimeCertificate 433033 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv18043]) (by decide +kernel)
def pv433033 : PrimeValue := ⟨433033, pr433033⟩
private theorem pr433061 : PrimeCertificate 433061 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv59,pv367]) (by decide +kernel)
def pv433061 : PrimeValue := ⟨433061, pr433061⟩
private theorem pr433073 : PrimeCertificate 433073 :=
  certifyPrime (q := pv3) (ls := [pv2,pv27067]) (by decide +kernel)
def pv433073 : PrimeValue := ⟨433073, pr433073⟩
private theorem pr433079 : PrimeCertificate 433079 :=
  certifyPrime (q := pv11) (ls := [pv2,pv79,pv2741]) (by decide +kernel)
def pv433079 : PrimeValue := ⟨433079, pr433079⟩
private theorem pr433087 : PrimeCertificate 433087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv29,pv131]) (by decide +kernel)
def pv433087 : PrimeValue := ⟨433087, pr433087⟩
private theorem pr433099 : PrimeCertificate 433099 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv24061]) (by decide +kernel)
def pv433099 : PrimeValue := ⟨433099, pr433099⟩
private theorem pr433117 : PrimeCertificate 433117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53,pv227]) (by decide +kernel)
def pv433117 : PrimeValue := ⟨433117, pr433117⟩
private theorem pr433141 : PrimeCertificate 433141 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv5,pv7219]) (by decide +kernel)
def pv433141 : PrimeValue := ⟨433141, pr433141⟩
private theorem pr433151 : PrimeCertificate 433151 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv8663]) (by decide +kernel)
def pv433151 : PrimeValue := ⟨433151, pr433151⟩
private theorem pr433207 : PrimeCertificate 433207 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv41,pv587]) (by decide +kernel)
def pv433207 : PrimeValue := ⟨433207, pr433207⟩
private theorem pr433259 : PrimeCertificate 433259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv4421]) (by decide +kernel)
def pv433259 : PrimeValue := ⟨433259, pr433259⟩
private theorem pr433271 : PrimeCertificate 433271 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv37,pv1171]) (by decide +kernel)
def pv433271 : PrimeValue := ⟨433271, pr433271⟩
private theorem pr433291 : PrimeCertificate 433291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv13,pv101]) (by decide +kernel)
def pv433291 : PrimeValue := ⟨433291, pr433291⟩
private theorem pr433319 : PrimeCertificate 433319 :=
  certifyPrime (q := pv17) (ls := [pv2,pv29,pv31,pv241]) (by decide +kernel)
def pv433319 : PrimeValue := ⟨433319, pr433319⟩
private theorem pr433373 : PrimeCertificate 433373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv108343]) (by decide +kernel)
def pv433373 : PrimeValue := ⟨433373, pr433373⟩
private theorem pr433421 : PrimeCertificate 433421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv1667]) (by decide +kernel)
def pv433421 : PrimeValue := ⟨433421, pr433421⟩
private theorem pr433549 : PrimeCertificate 433549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv12043]) (by decide +kernel)
def pv433549 : PrimeValue := ⟨433549, pr433549⟩
private theorem pr433571 : PrimeCertificate 433571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv191,pv227]) (by decide +kernel)
def pv433571 : PrimeValue := ⟨433571, pr433571⟩
private theorem pr433577 : PrimeCertificate 433577 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv13,pv379]) (by decide +kernel)
def pv433577 : PrimeValue := ⟨433577, pr433577⟩
private theorem pr433627 : PrimeCertificate 433627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv72271]) (by decide +kernel)
def pv433627 : PrimeValue := ⟨433627, pr433627⟩
private theorem pr433633 : PrimeCertificate 433633 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4517]) (by decide +kernel)
def pv433633 : PrimeValue := ⟨433633, pr433633⟩
private theorem pr433663 : PrimeCertificate 433663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv72277]) (by decide +kernel)
def pv433663 : PrimeValue := ⟨433663, pr433663⟩
private theorem pr433681 : PrimeCertificate 433681 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv13,pv139]) (by decide +kernel)
def pv433681 : PrimeValue := ⟨433681, pr433681⟩
private theorem pr433729 : PrimeCertificate 433729 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv251]) (by decide +kernel)
def pv433729 : PrimeValue := ⟨433729, pr433729⟩
private theorem pr433747 : PrimeCertificate 433747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv24097]) (by decide +kernel)
def pv433747 : PrimeValue := ⟨433747, pr433747⟩
private theorem pr433777 : PrimeCertificate 433777 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv1291]) (by decide +kernel)
def pv433777 : PrimeValue := ⟨433777, pr433777⟩
private theorem pr433781 : PrimeCertificate 433781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv41]) (by decide +kernel)
def pv433781 : PrimeValue := ⟨433781, pr433781⟩
private theorem pr433787 : PrimeCertificate 433787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89,pv2437]) (by decide +kernel)
def pv433787 : PrimeValue := ⟨433787, pr433787⟩
private theorem pr433813 : PrimeCertificate 433813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv36151]) (by decide +kernel)
def pv433813 : PrimeValue := ⟨433813, pr433813⟩
private theorem pr433859 : PrimeCertificate 433859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv4093]) (by decide +kernel)
def pv433859 : PrimeValue := ⟨433859, pr433859⟩
private theorem pr433883 : PrimeCertificate 433883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv401,pv541]) (by decide +kernel)
def pv433883 : PrimeValue := ⟨433883, pr433883⟩
private theorem pr433943 : PrimeCertificate 433943 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv12763]) (by decide +kernel)
def pv433943 : PrimeValue := ⟨433943, pr433943⟩
private theorem pr434009 : PrimeCertificate 434009 :=
  certifyPrime (q := pv3) (ls := [pv2,pv54251]) (by decide +kernel)
def pv434009 : PrimeValue := ⟨434009, pr434009⟩
private theorem pr434087 : PrimeCertificate 434087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv127,pv1709]) (by decide +kernel)
def pv434087 : PrimeValue := ⟨434087, pr434087⟩
private theorem pr434113 : PrimeCertificate 434113 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv17,pv19]) (by decide +kernel)
def pv434113 : PrimeValue := ⟨434113, pr434113⟩
private theorem pr434117 : PrimeCertificate 434117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv108529]) (by decide +kernel)
def pv434117 : PrimeValue := ⟨434117, pr434117⟩
private theorem pr434201 : PrimeCertificate 434201 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv167]) (by decide +kernel)
def pv434201 : PrimeValue := ⟨434201, pr434201⟩
private theorem pr434243 : PrimeCertificate 434243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv217121]) (by decide +kernel)
def pv434243 : PrimeValue := ⟨434243, pr434243⟩
private theorem pr434249 : PrimeCertificate 434249 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv31,pv103]) (by decide +kernel)
def pv434249 : PrimeValue := ⟨434249, pr434249⟩
private theorem pr434261 : PrimeCertificate 434261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv21713]) (by decide +kernel)
def pv434261 : PrimeValue := ⟨434261, pr434261⟩
private theorem pr434303 : PrimeCertificate 434303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv19,pv1039]) (by decide +kernel)
def pv434303 : PrimeValue := ⟨434303, pr434303⟩
private theorem pr434353 : PrimeCertificate 434353 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv9049]) (by decide +kernel)
def pv434353 : PrimeValue := ⟨434353, pr434353⟩
private theorem pr434363 : PrimeCertificate 434363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv7489]) (by decide +kernel)
def pv434363 : PrimeValue := ⟨434363, pr434363⟩
private theorem pr434431 : PrimeCertificate 434431 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv1609]) (by decide +kernel)
def pv434431 : PrimeValue := ⟨434431, pr434431⟩
private theorem pr434459 : PrimeCertificate 434459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv217229]) (by decide +kernel)
def pv434459 : PrimeValue := ⟨434459, pr434459⟩
private theorem pr434461 : PrimeCertificate 434461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv557]) (by decide +kernel)
def pv434461 : PrimeValue := ⟨434461, pr434461⟩
private theorem pr434471 : PrimeCertificate 434471 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv23,pv1889]) (by decide +kernel)
def pv434471 : PrimeValue := ⟨434471, pr434471⟩
private theorem pr434561 : PrimeCertificate 434561 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv97]) (by decide +kernel)
def pv434561 : PrimeValue := ⟨434561, pr434561⟩
private theorem pr434647 : PrimeCertificate 434647 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv2683]) (by decide +kernel)
def pv434647 : PrimeValue := ⟨434647, pr434647⟩
private theorem pr434683 : PrimeCertificate 434683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv31,pv41]) (by decide +kernel)
def pv434683 : PrimeValue := ⟨434683, pr434683⟩
private theorem pr434699 : PrimeCertificate 434699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv19759]) (by decide +kernel)
def pv434699 : PrimeValue := ⟨434699, pr434699⟩
private theorem pr434717 : PrimeCertificate 434717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv191,pv569]) (by decide +kernel)
def pv434717 : PrimeValue := ⟨434717, pr434717⟩
private theorem pr434743 : PrimeCertificate 434743 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv11,pv941]) (by decide +kernel)
def pv434743 : PrimeValue := ⟨434743, pr434743⟩
private theorem pr434783 : PrimeCertificate 434783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv149,pv1459]) (by decide +kernel)
def pv434783 : PrimeValue := ⟨434783, pr434783⟩
private theorem pr434831 : PrimeCertificate 434831 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv11,pv59,pv67]) (by decide +kernel)
def pv434831 : PrimeValue := ⟨434831, pr434831⟩
private theorem pr434839 : PrimeCertificate 434839 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv137]) (by decide +kernel)
def pv434839 : PrimeValue := ⟨434839, pr434839⟩
private theorem pr434873 : PrimeCertificate 434873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv2861]) (by decide +kernel)
def pv434873 : PrimeValue := ⟨434873, pr434873⟩
private theorem pr434881 : PrimeCertificate 434881 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv151]) (by decide +kernel)
def pv434881 : PrimeValue := ⟨434881, pr434881⟩
private theorem pr434909 : PrimeCertificate 434909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv108727]) (by decide +kernel)
def pv434909 : PrimeValue := ⟨434909, pr434909⟩
private theorem pr434923 : PrimeCertificate 434923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv173,pv419]) (by decide +kernel)
def pv434923 : PrimeValue := ⟨434923, pr434923⟩
private theorem pr434933 : PrimeCertificate 434933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv227,pv479]) (by decide +kernel)
def pv434933 : PrimeValue := ⟨434933, pr434933⟩
private theorem pr434939 : PrimeCertificate 434939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv47,pv661]) (by decide +kernel)
def pv434939 : PrimeValue := ⟨434939, pr434939⟩
private theorem pr434947 : PrimeCertificate 434947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv71,pv1021]) (by decide +kernel)
def pv434947 : PrimeValue := ⟨434947, pr434947⟩
private theorem pr434963 : PrimeCertificate 434963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv17,pv1163]) (by decide +kernel)
def pv434963 : PrimeValue := ⟨434963, pr434963⟩
private theorem pr434989 : PrimeCertificate 434989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv281]) (by decide +kernel)
def pv434989 : PrimeValue := ⟨434989, pr434989⟩
private theorem pr435041 : PrimeCertificate 435041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv2719]) (by decide +kernel)
def pv435041 : PrimeValue := ⟨435041, pr435041⟩
private theorem pr435109 : PrimeCertificate 435109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv101,pv359]) (by decide +kernel)
def pv435109 : PrimeValue := ⟨435109, pr435109⟩
private theorem pr435131 : PrimeCertificate 435131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv53,pv821]) (by decide +kernel)
def pv435131 : PrimeValue := ⟨435131, pr435131⟩
private theorem pr435143 : PrimeCertificate 435143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv97,pv2243]) (by decide +kernel)
def pv435143 : PrimeValue := ⟨435143, pr435143⟩
private theorem pr435161 : PrimeCertificate 435161 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv23,pv43]) (by decide +kernel)
def pv435161 : PrimeValue := ⟨435161, pr435161⟩
private theorem pr435181 : PrimeCertificate 435181 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7253]) (by decide +kernel)
def pv435181 : PrimeValue := ⟨435181, pr435181⟩
private theorem pr435187 : PrimeCertificate 435187 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv8059]) (by decide +kernel)
def pv435187 : PrimeValue := ⟨435187, pr435187⟩
private theorem pr435191 : PrimeCertificate 435191 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv6217]) (by decide +kernel)
def pv435191 : PrimeValue := ⟨435191, pr435191⟩
private theorem pr435263 : PrimeCertificate 435263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv367,pv593]) (by decide +kernel)
def pv435263 : PrimeValue := ⟨435263, pr435263⟩
private theorem pr435277 : PrimeCertificate 435277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv107,pv113]) (by decide +kernel)
def pv435277 : PrimeValue := ⟨435277, pr435277⟩
private theorem pr435283 : PrimeCertificate 435283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv72547]) (by decide +kernel)
def pv435283 : PrimeValue := ⟨435283, pr435283⟩
private theorem pr435287 : PrimeCertificate 435287 :=
  certifyPrime (q := pv5) (ls := [pv2,pv217643]) (by decide +kernel)
def pv435287 : PrimeValue := ⟨435287, pr435287⟩
private theorem pr435343 : PrimeCertificate 435343 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37,pv53]) (by decide +kernel)
def pv435343 : PrimeValue := ⟨435343, pr435343⟩
private theorem pr435371 : PrimeCertificate 435371 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv13,pv17,pv197]) (by decide +kernel)
def pv435371 : PrimeValue := ⟨435371, pr435371⟩
private theorem pr435397 : PrimeCertificate 435397 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv2791]) (by decide +kernel)
def pv435397 : PrimeValue := ⟨435397, pr435397⟩
private theorem pr435401 : PrimeCertificate 435401 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv311]) (by decide +kernel)
def pv435401 : PrimeValue := ⟨435401, pr435401⟩
private theorem pr435403 : PrimeCertificate 435403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv733]) (by decide +kernel)
def pv435403 : PrimeValue := ⟨435403, pr435403⟩
private theorem pr435439 : PrimeCertificate 435439 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv1423]) (by decide +kernel)
def pv435439 : PrimeValue := ⟨435439, pr435439⟩
private theorem pr435451 : PrimeCertificate 435451 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv2903]) (by decide +kernel)
def pv435451 : PrimeValue := ⟨435451, pr435451⟩
private theorem pr435577 : PrimeCertificate 435577 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv18149]) (by decide +kernel)
def pv435577 : PrimeValue := ⟨435577, pr435577⟩
private theorem pr435623 : PrimeCertificate 435623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv19801]) (by decide +kernel)
def pv435623 : PrimeValue := ⟨435623, pr435623⟩
private theorem pr435641 : PrimeCertificate 435641 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv10891]) (by decide +kernel)
def pv435641 : PrimeValue := ⟨435641, pr435641⟩
private theorem pr435647 : PrimeCertificate 435647 :=
  certifyPrime (q := pv5) (ls := [pv2,pv217823]) (by decide +kernel)
def pv435647 : PrimeValue := ⟨435647, pr435647⟩
private theorem pr435731 : PrimeCertificate 435731 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv43573]) (by decide +kernel)
def pv435731 : PrimeValue := ⟨435731, pr435731⟩
private theorem pr435839 : PrimeCertificate 435839 :=
  certifyPrime (q := pv19) (ls := [pv2,pv13,pv16763]) (by decide +kernel)
def pv435839 : PrimeValue := ⟨435839, pr435839⟩
private theorem pr435847 : PrimeCertificate 435847 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv4273]) (by decide +kernel)
def pv435847 : PrimeValue := ⟨435847, pr435847⟩
private theorem pr435859 : PrimeCertificate 435859 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv72643]) (by decide +kernel)
def pv435859 : PrimeValue := ⟨435859, pr435859⟩
private theorem pr435881 : PrimeCertificate 435881 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17,pv641]) (by decide +kernel)
def pv435881 : PrimeValue := ⟨435881, pr435881⟩
private theorem pr435889 : PrimeCertificate 435889 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv1009]) (by decide +kernel)
def pv435889 : PrimeValue := ⟨435889, pr435889⟩
private theorem pr435893 : PrimeCertificate 435893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59,pv1847]) (by decide +kernel)
def pv435893 : PrimeValue := ⟨435893, pr435893⟩
private theorem pr435907 : PrimeCertificate 435907 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv61,pv397]) (by decide +kernel)
def pv435907 : PrimeValue := ⟨435907, pr435907⟩
private theorem pr435973 : PrimeCertificate 435973 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv47,pv773]) (by decide +kernel)
def pv435973 : PrimeValue := ⟨435973, pr435973⟩
private theorem pr435997 : PrimeCertificate 435997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv367]) (by decide +kernel)
def pv435997 : PrimeValue := ⟨435997, pr435997⟩
private theorem pr436147 : PrimeCertificate 436147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv157,pv463]) (by decide +kernel)
def pv436147 : PrimeValue := ⟨436147, pr436147⟩
private theorem pr436253 : PrimeCertificate 436253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv109063]) (by decide +kernel)
def pv436253 : PrimeValue := ⟨436253, pr436253⟩
private theorem pr436283 : PrimeCertificate 436283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv2833]) (by decide +kernel)
def pv436283 : PrimeValue := ⟨436283, pr436283⟩
private theorem pr436343 : PrimeCertificate 436343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv218171]) (by decide +kernel)
def pv436343 : PrimeValue := ⟨436343, pr436343⟩
private theorem pr436417 : PrimeCertificate 436417 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2273]) (by decide +kernel)
def pv436417 : PrimeValue := ⟨436417, pr436417⟩
private theorem pr436463 : PrimeCertificate 436463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv16787]) (by decide +kernel)
def pv436463 : PrimeValue := ⟨436463, pr436463⟩
private theorem pr436507 : PrimeCertificate 436507 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv19,pv547]) (by decide +kernel)
def pv436507 : PrimeValue := ⟨436507, pr436507⟩
private theorem pr436673 : PrimeCertificate 436673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv6823]) (by decide +kernel)
def pv436673 : PrimeValue := ⟨436673, pr436673⟩
private theorem pr436853 : PrimeCertificate 436853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv31,pv271]) (by decide +kernel)
def pv436853 : PrimeValue := ⟨436853, pr436853⟩
private theorem pr436963 : PrimeCertificate 436963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv3833]) (by decide +kernel)
def pv436963 : PrimeValue := ⟨436963, pr436963⟩
private theorem pr436979 : PrimeCertificate 436979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv73]) (by decide +kernel)
def pv436979 : PrimeValue := ⟨436979, pr436979⟩
private theorem pr437071 : PrimeCertificate 437071 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv17,pv857]) (by decide +kernel)
def pv437071 : PrimeValue := ⟨437071, pr437071⟩
private theorem pr437083 : PrimeCertificate 437083 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv97,pv751]) (by decide +kernel)
def pv437083 : PrimeValue := ⟨437083, pr437083⟩
private theorem pr437093 : PrimeCertificate 437093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv4751]) (by decide +kernel)
def pv437093 : PrimeValue := ⟨437093, pr437093⟩
private theorem pr437113 : PrimeCertificate 437113 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv467]) (by decide +kernel)
def pv437113 : PrimeValue := ⟨437113, pr437113⟩
private theorem pr437191 : PrimeCertificate 437191 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv13,pv19,pv59]) (by decide +kernel)
def pv437191 : PrimeValue := ⟨437191, pr437191⟩
private theorem pr437201 : PrimeCertificate 437201 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv1093]) (by decide +kernel)
def pv437201 : PrimeValue := ⟨437201, pr437201⟩
private theorem pr437243 : PrimeCertificate 437243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv67,pv251]) (by decide +kernel)
def pv437243 : PrimeValue := ⟨437243, pr437243⟩
private theorem pr437273 : PrimeCertificate 437273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv4969]) (by decide +kernel)
def pv437273 : PrimeValue := ⟨437273, pr437273⟩
private theorem pr437287 : PrimeCertificate 437287 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31,pv2351]) (by decide +kernel)
def pv437287 : PrimeValue := ⟨437287, pr437287⟩
private theorem pr437293 : PrimeCertificate 437293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv4049]) (by decide +kernel)
def pv437293 : PrimeValue := ⟨437293, pr437293⟩
private theorem pr437351 : PrimeCertificate 437351 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv8747]) (by decide +kernel)
def pv437351 : PrimeValue := ⟨437351, pr437351⟩
private theorem pr437363 : PrimeCertificate 437363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv218681]) (by decide +kernel)
def pv437363 : PrimeValue := ⟨437363, pr437363⟩
private theorem pr437467 : PrimeCertificate 437467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv72911]) (by decide +kernel)
def pv437467 : PrimeValue := ⟨437467, pr437467⟩
private theorem pr437509 : PrimeCertificate 437509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv4051]) (by decide +kernel)
def pv437509 : PrimeValue := ⟨437509, pr437509⟩
private theorem pr437527 : PrimeCertificate 437527 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv109,pv223]) (by decide +kernel)
def pv437527 : PrimeValue := ⟨437527, pr437527⟩
private theorem pr437587 : PrimeCertificate 437587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv72931]) (by decide +kernel)
def pv437587 : PrimeValue := ⟨437587, pr437587⟩
private theorem pr437651 : PrimeCertificate 437651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv8753]) (by decide +kernel)
def pv437651 : PrimeValue := ⟨437651, pr437651⟩
private theorem pr437681 : PrimeCertificate 437681 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv5471]) (by decide +kernel)
def pv437681 : PrimeValue := ⟨437681, pr437681⟩
private theorem pr437771 : PrimeCertificate 437771 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv43777]) (by decide +kernel)
def pv437771 : PrimeValue := ⟨437771, pr437771⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
