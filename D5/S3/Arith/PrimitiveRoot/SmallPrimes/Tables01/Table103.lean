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

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr429599 : Nat.Prime 429599 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv13,pv31,pv41]) (by decide +kernel)
def pv429599 : PrimeValue := ⟨429599, pr429599⟩
private theorem pr429643 : Nat.Prime 429643 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23869]) (by decide +kernel)
def pv429643 : PrimeValue := ⟨429643, pr429643⟩
private theorem pr429673 : Nat.Prime 429673 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17903]) (by decide +kernel)
def pv429673 : PrimeValue := ⟨429673, pr429673⟩
private theorem pr429683 : Nat.Prime 429683 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv19531]) (by decide +kernel)
def pv429683 : PrimeValue := ⟨429683, pr429683⟩
private theorem pr429701 : Nat.Prime 429701 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv4297]) (by decide +kernel)
def pv429701 : PrimeValue := ⟨429701, pr429701⟩
private theorem pr429731 : Nat.Prime 429731 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv877]) (by decide +kernel)
def pv429731 : PrimeValue := ⟨429731, pr429731⟩
private theorem pr429733 : Nat.Prime 429733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv173]) (by decide +kernel)
def pv429733 : PrimeValue := ⟨429733, pr429733⟩
private theorem pr429797 : Nat.Prime 429797 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv107449]) (by decide +kernel)
def pv429797 : PrimeValue := ⟨429797, pr429797⟩
private theorem pr429823 : Nat.Prime 429823 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23879]) (by decide +kernel)
def pv429823 : PrimeValue := ⟨429823, pr429823⟩
private theorem pr429827 : Nat.Prime 429827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv214913]) (by decide +kernel)
def pv429827 : PrimeValue := ⟨429827, pr429827⟩
private theorem pr429853 : Nat.Prime 429853 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv113,pv317]) (by decide +kernel)
def pv429853 : PrimeValue := ⟨429853, pr429853⟩
private theorem pr429881 : Nat.Prime 429881 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv11,pv977]) (by decide +kernel)
def pv429881 : PrimeValue := ⟨429881, pr429881⟩
private theorem pr429887 : Nat.Prime 429887 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv214943]) (by decide +kernel)
def pv429887 : PrimeValue := ⟨429887, pr429887⟩
private theorem pr429899 : Nat.Prime 429899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv30707]) (by decide +kernel)
def pv429899 : PrimeValue := ⟨429899, pr429899⟩
private theorem pr429907 : Nat.Prime 429907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv137,pv523]) (by decide +kernel)
def pv429907 : PrimeValue := ⟨429907, pr429907⟩
private theorem pr429911 : Nat.Prime 429911 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv13,pv3307]) (by decide +kernel)
def pv429911 : PrimeValue := ⟨429911, pr429911⟩
private theorem pr429937 : Nat.Prime 429937 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv13,pv53]) (by decide +kernel)
def pv429937 : PrimeValue := ⟨429937, pr429937⟩
private theorem pr429943 : Nat.Prime 429943 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv131,pv547]) (by decide +kernel)
def pv429943 : PrimeValue := ⟨429943, pr429943⟩
private theorem pr429953 : Nat.Prime 429953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3359]) (by decide +kernel)
def pv429953 : PrimeValue := ⟨429953, pr429953⟩
private theorem pr429971 : Nat.Prime 429971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19,pv31,pv73]) (by decide +kernel)
def pv429971 : PrimeValue := ⟨429971, pr429971⟩
private theorem pr430013 : Nat.Prime 430013 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv29,pv337]) (by decide +kernel)
def pv430013 : PrimeValue := ⟨430013, pr430013⟩
private theorem pr430019 : Nat.Prime 430019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv211,pv1019]) (by decide +kernel)
def pv430019 : PrimeValue := ⟨430019, pr430019⟩
private theorem pr430091 : Nat.Prime 430091 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv41,pv1049]) (by decide +kernel)
def pv430091 : PrimeValue := ⟨430091, pr430091⟩
private theorem pr430277 : Nat.Prime 430277 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv11,pv127]) (by decide +kernel)
def pv430277 : PrimeValue := ⟨430277, pr430277⟩
private theorem pr430289 : Nat.Prime 430289 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv26893]) (by decide +kernel)
def pv430289 : PrimeValue := ⟨430289, pr430289⟩
private theorem pr430343 : Nat.Prime 430343 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv31,pv631]) (by decide +kernel)
def pv430343 : PrimeValue := ⟨430343, pr430343⟩
private theorem pr430357 : Nat.Prime 430357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv35863]) (by decide +kernel)
def pv430357 : PrimeValue := ⟨430357, pr430357⟩
private theorem pr430453 : Nat.Prime 430453 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv1087]) (by decide +kernel)
def pv430453 : PrimeValue := ⟨430453, pr430453⟩
private theorem pr430487 : Nat.Prime 430487 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv97,pv317]) (by decide +kernel)
def pv430487 : PrimeValue := ⟨430487, pr430487⟩
private theorem pr430513 : Nat.Prime 430513 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv8969]) (by decide +kernel)
def pv430513 : PrimeValue := ⟨430513, pr430513⟩
private theorem pr430517 : Nat.Prime 430517 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv2503]) (by decide +kernel)
def pv430517 : PrimeValue := ⟨430517, pr430517⟩
private theorem pr430543 : Nat.Prime 430543 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv17,pv67]) (by decide +kernel)
def pv430543 : PrimeValue := ⟨430543, pr430543⟩
private theorem pr430571 : Nat.Prime 430571 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv6151]) (by decide +kernel)
def pv430571 : PrimeValue := ⟨430571, pr430571⟩
private theorem pr430589 : Nat.Prime 430589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv107647]) (by decide +kernel)
def pv430589 : PrimeValue := ⟨430589, pr430589⟩
private theorem pr430601 : Nat.Prime 430601 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv2153]) (by decide +kernel)
def pv430601 : PrimeValue := ⟨430601, pr430601⟩
private theorem pr430649 : Nat.Prime 430649 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv53831]) (by decide +kernel)
def pv430649 : PrimeValue := ⟨430649, pr430649⟩
private theorem pr430663 : Nat.Prime 430663 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv71777]) (by decide +kernel)
def pv430663 : PrimeValue := ⟨430663, pr430663⟩
private theorem pr430691 : Nat.Prime 430691 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv3313]) (by decide +kernel)
def pv430691 : PrimeValue := ⟨430691, pr430691⟩
private theorem pr430723 : Nat.Prime 430723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23929]) (by decide +kernel)
def pv430723 : PrimeValue := ⟨430723, pr430723⟩
private theorem pr430739 : Nat.Prime 430739 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv7,pv11,pv2797]) (by decide +kernel)
def pv430739 : PrimeValue := ⟨430739, pr430739⟩
private theorem pr430747 : Nat.Prime 430747 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv41,pv103]) (by decide +kernel)
def pv430747 : PrimeValue := ⟨430747, pr430747⟩
private theorem pr430799 : Nat.Prime 430799 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv215399]) (by decide +kernel)
def pv430799 : PrimeValue := ⟨430799, pr430799⟩
private theorem pr430819 : Nat.Prime 430819 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv59,pv1217]) (by decide +kernel)
def pv430819 : PrimeValue := ⟨430819, pr430819⟩
private theorem pr430823 : Nat.Prime 430823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv30773]) (by decide +kernel)
def pv430823 : PrimeValue := ⟨430823, pr430823⟩
private theorem pr430891 : Nat.Prime 430891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv53,pv271]) (by decide +kernel)
def pv430891 : PrimeValue := ⟨430891, pr430891⟩
private theorem pr430909 : Nat.Prime 430909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv149,pv241]) (by decide +kernel)
def pv430909 : PrimeValue := ⟨430909, pr430909⟩
private theorem pr430949 : Nat.Prime 430949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv15391]) (by decide +kernel)
def pv430949 : PrimeValue := ⟨430949, pr430949⟩
private theorem pr430957 : Nat.Prime 430957 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11971]) (by decide +kernel)
def pv430957 : PrimeValue := ⟨430957, pr430957⟩
private theorem pr431021 : Nat.Prime 431021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23,pv937]) (by decide +kernel)
def pv431021 : PrimeValue := ⟨431021, pr431021⟩
private theorem pr431063 : Nat.Prime 431063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv215531]) (by decide +kernel)
def pv431063 : PrimeValue := ⟨431063, pr431063⟩
private theorem pr431077 : Nat.Prime 431077 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv35923]) (by decide +kernel)
def pv431077 : PrimeValue := ⟨431077, pr431077⟩
private theorem pr431107 : Nat.Prime 431107 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv5527]) (by decide +kernel)
def pv431107 : PrimeValue := ⟨431107, pr431107⟩
private theorem pr431141 : Nat.Prime 431141 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv21557]) (by decide +kernel)
def pv431141 : PrimeValue := ⟨431141, pr431141⟩
private theorem pr431153 : Nat.Prime 431153 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv26947]) (by decide +kernel)
def pv431153 : PrimeValue := ⟨431153, pr431153⟩
private theorem pr431191 : Nat.Prime 431191 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv1597]) (by decide +kernel)
def pv431191 : PrimeValue := ⟨431191, pr431191⟩
private theorem pr431203 : Nat.Prime 431203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv71867]) (by decide +kernel)
def pv431203 : PrimeValue := ⟨431203, pr431203⟩
private theorem pr431213 : Nat.Prime 431213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv67,pv1609]) (by decide +kernel)
def pv431213 : PrimeValue := ⟨431213, pr431213⟩
private theorem pr431237 : Nat.Prime 431237 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv8293]) (by decide +kernel)
def pv431237 : PrimeValue := ⟨431237, pr431237⟩
private theorem pr431267 : Nat.Prime 431267 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv19603]) (by decide +kernel)
def pv431267 : PrimeValue := ⟨431267, pr431267⟩
private theorem pr431269 : Nat.Prime 431269 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv83,pv433]) (by decide +kernel)
def pv431269 : PrimeValue := ⟨431269, pr431269⟩
private theorem pr431363 : Nat.Prime 431363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv215681]) (by decide +kernel)
def pv431363 : PrimeValue := ⟨431363, pr431363⟩
private theorem pr431369 : Nat.Prime 431369 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv7703]) (by decide +kernel)
def pv431369 : PrimeValue := ⟨431369, pr431369⟩
private theorem pr431377 : Nat.Prime 431377 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv19,pv43]) (by decide +kernel)
def pv431377 : PrimeValue := ⟨431377, pr431377⟩
private theorem pr431399 : Nat.Prime 431399 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv11,pv19609]) (by decide +kernel)
def pv431399 : PrimeValue := ⟨431399, pr431399⟩
private theorem pr431447 : Nat.Prime 431447 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv215723]) (by decide +kernel)
def pv431447 : PrimeValue := ⟨431447, pr431447⟩
private theorem pr431521 : Nat.Prime 431521 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv29,pv31]) (by decide +kernel)
def pv431521 : PrimeValue := ⟨431521, pr431521⟩
private theorem pr431533 : Nat.Prime 431533 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv11987]) (by decide +kernel)
def pv431533 : PrimeValue := ⟨431533, pr431533⟩
private theorem pr431581 : Nat.Prime 431581 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv7193]) (by decide +kernel)
def pv431581 : PrimeValue := ⟨431581, pr431581⟩
private theorem pr431603 : Nat.Prime 431603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv215801]) (by decide +kernel)
def pv431603 : PrimeValue := ⟨431603, pr431603⟩
private theorem pr431617 : Nat.Prime 431617 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv281]) (by decide +kernel)
def pv431617 : PrimeValue := ⟨431617, pr431617⟩
private theorem pr431729 : Nat.Prime 431729 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv223]) (by decide +kernel)
def pv431729 : PrimeValue := ⟨431729, pr431729⟩
private theorem pr431731 : Nat.Prime 431731 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv41]) (by decide +kernel)
def pv431731 : PrimeValue := ⟨431731, pr431731⟩
private theorem pr431797 : Nat.Prime 431797 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv35983]) (by decide +kernel)
def pv431797 : PrimeValue := ⟨431797, pr431797⟩
private theorem pr431807 : Nat.Prime 431807 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv43,pv5021]) (by decide +kernel)
def pv431807 : PrimeValue := ⟨431807, pr431807⟩
private theorem pr431857 : Nat.Prime 431857 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2999]) (by decide +kernel)
def pv431857 : PrimeValue := ⟨431857, pr431857⟩
private theorem pr431867 : Nat.Prime 431867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv181,pv1193]) (by decide +kernel)
def pv431867 : PrimeValue := ⟨431867, pr431867⟩
private theorem pr431891 : Nat.Prime 431891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv43189]) (by decide +kernel)
def pv431891 : PrimeValue := ⟨431891, pr431891⟩
private theorem pr431903 : Nat.Prime 431903 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv12703]) (by decide +kernel)
def pv431903 : PrimeValue := ⟨431903, pr431903⟩
private theorem pr431929 : Nat.Prime 431929 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv7,pv857]) (by decide +kernel)
def pv431929 : PrimeValue := ⟨431929, pr431929⟩
private theorem pr431933 : Nat.Prime 431933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv83,pv1301]) (by decide +kernel)
def pv431933 : PrimeValue := ⟨431933, pr431933⟩
private theorem pr431947 : Nat.Prime 431947 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv421]) (by decide +kernel)
def pv431947 : PrimeValue := ⟨431947, pr431947⟩
private theorem pr431983 : Nat.Prime 431983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv103,pv233]) (by decide +kernel)
def pv431983 : PrimeValue := ⟨431983, pr431983⟩
private theorem pr432007 : Nat.Prime 432007 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv89,pv809]) (by decide +kernel)
def pv432007 : PrimeValue := ⟨432007, pr432007⟩
private theorem pr432023 : Nat.Prime 432023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv11369]) (by decide +kernel)
def pv432023 : PrimeValue := ⟨432023, pr432023⟩
private theorem pr432037 : Nat.Prime 432037 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv1091]) (by decide +kernel)
def pv432037 : PrimeValue := ⟨432037, pr432037⟩
private theorem pr432043 : Nat.Prime 432043 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv29,pv191]) (by decide +kernel)
def pv432043 : PrimeValue := ⟨432043, pr432043⟩
private theorem pr432053 : Nat.Prime 432053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv108013]) (by decide +kernel)
def pv432053 : PrimeValue := ⟨432053, pr432053⟩
private theorem pr432059 : Nat.Prime 432059 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv11,pv41,pv479]) (by decide +kernel)
def pv432059 : PrimeValue := ⟨432059, pr432059⟩
private theorem pr432067 : Nat.Prime 432067 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv107,pv673]) (by decide +kernel)
def pv432067 : PrimeValue := ⟨432067, pr432067⟩
private theorem pr432149 : Nat.Prime 432149 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv108037]) (by decide +kernel)
def pv432149 : PrimeValue := ⟨432149, pr432149⟩
private theorem pr432161 : Nat.Prime 432161 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv37,pv73]) (by decide +kernel)
def pv432161 : PrimeValue := ⟨432161, pr432161⟩
private theorem pr432203 : Nat.Prime 432203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv6971]) (by decide +kernel)
def pv432203 : PrimeValue := ⟨432203, pr432203⟩
private theorem pr432227 : Nat.Prime 432227 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv216113]) (by decide +kernel)
def pv432227 : PrimeValue := ⟨432227, pr432227⟩
private theorem pr432251 : Nat.Prime 432251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv13,pv19]) (by decide +kernel)
def pv432251 : PrimeValue := ⟨432251, pr432251⟩
private theorem pr432277 : Nat.Prime 432277 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv17,pv163]) (by decide +kernel)
def pv432277 : PrimeValue := ⟨432277, pr432277⟩
private theorem pr432281 : Nat.Prime 432281 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv101,pv107]) (by decide +kernel)
def pv432281 : PrimeValue := ⟨432281, pr432281⟩
private theorem pr432287 : Nat.Prime 432287 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv331,pv653]) (by decide +kernel)
def pv432287 : PrimeValue := ⟨432287, pr432287⟩
private theorem pr432317 : Nat.Prime 432317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv108079]) (by decide +kernel)
def pv432317 : PrimeValue := ⟨432317, pr432317⟩
private theorem pr432323 : Nat.Prime 432323 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv43,pv457]) (by decide +kernel)
def pv432323 : PrimeValue := ⟨432323, pr432323⟩
private theorem pr432337 : Nat.Prime 432337 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv9007]) (by decide +kernel)
def pv432337 : PrimeValue := ⟨432337, pr432337⟩
private theorem pr432343 : Nat.Prime 432343 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv24019]) (by decide +kernel)
def pv432343 : PrimeValue := ⟨432343, pr432343⟩
private theorem pr432373 : Nat.Prime 432373 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv137,pv263]) (by decide +kernel)
def pv432373 : PrimeValue := ⟨432373, pr432373⟩
private theorem pr432401 : Nat.Prime 432401 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv23,pv47]) (by decide +kernel)
def pv432401 : PrimeValue := ⟨432401, pr432401⟩
private theorem pr432413 : Nat.Prime 432413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv6359]) (by decide +kernel)
def pv432413 : PrimeValue := ⟨432413, pr432413⟩
private theorem pr432457 : Nat.Prime 432457 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv37,pv487]) (by decide +kernel)
def pv432457 : PrimeValue := ⟨432457, pr432457⟩
private theorem pr432479 : Nat.Prime 432479 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv19,pv599]) (by decide +kernel)
def pv432479 : PrimeValue := ⟨432479, pr432479⟩
private theorem pr432491 : Nat.Prime 432491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv61,pv709]) (by decide +kernel)
def pv432491 : PrimeValue := ⟨432491, pr432491⟩
private theorem pr432527 : Nat.Prime 432527 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv216263]) (by decide +kernel)
def pv432527 : PrimeValue := ⟨432527, pr432527⟩
private theorem pr432559 : Nat.Prime 432559 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv3433]) (by decide +kernel)
def pv432559 : PrimeValue := ⟨432559, pr432559⟩
private theorem pr432569 : Nat.Prime 432569 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv139,pv389]) (by decide +kernel)
def pv432569 : PrimeValue := ⟨432569, pr432569⟩
private theorem pr432589 : Nat.Prime 432589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv47,pv59]) (by decide +kernel)
def pv432589 : PrimeValue := ⟨432589, pr432589⟩
private theorem pr432631 : Nat.Prime 432631 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv11,pv19,pv23]) (by decide +kernel)
def pv432631 : PrimeValue := ⟨432631, pr432631⟩
private theorem pr432659 : Nat.Prime 432659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv216329]) (by decide +kernel)
def pv432659 : PrimeValue := ⟨432659, pr432659⟩
private theorem pr432743 : Nat.Prime 432743 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv216371]) (by decide +kernel)
def pv432743 : PrimeValue := ⟨432743, pr432743⟩
private theorem pr432749 : Nat.Prime 432749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv108187]) (by decide +kernel)
def pv432749 : PrimeValue := ⟨432749, pr432749⟩
private theorem pr432781 : Nat.Prime 432781 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7213]) (by decide +kernel)
def pv432781 : PrimeValue := ⟨432781, pr432781⟩
private theorem pr432797 : Nat.Prime 432797 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv13,pv29,pv41]) (by decide +kernel)
def pv432797 : PrimeValue := ⟨432797, pr432797⟩
private theorem pr432847 : Nat.Prime 432847 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv139,pv173]) (by decide +kernel)
def pv432847 : PrimeValue := ⟨432847, pr432847⟩
private theorem pr432893 : Nat.Prime 432893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv108223]) (by decide +kernel)
def pv432893 : PrimeValue := ⟨432893, pr432893⟩
private theorem pr432923 : Nat.Prime 432923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv17,pv107]) (by decide +kernel)
def pv432923 : PrimeValue := ⟨432923, pr432923⟩
private theorem pr432983 : Nat.Prime 432983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv19681]) (by decide +kernel)
def pv432983 : PrimeValue := ⟨432983, pr432983⟩
private theorem pr432989 : Nat.Prime 432989 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv108247]) (by decide +kernel)
def pv432989 : PrimeValue := ⟨432989, pr432989⟩
private theorem pr433033 : Nat.Prime 433033 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv18043]) (by decide +kernel)
def pv433033 : PrimeValue := ⟨433033, pr433033⟩
private theorem pr433061 : Nat.Prime 433061 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv59,pv367]) (by decide +kernel)
def pv433061 : PrimeValue := ⟨433061, pr433061⟩
private theorem pr433073 : Nat.Prime 433073 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv27067]) (by decide +kernel)
def pv433073 : PrimeValue := ⟨433073, pr433073⟩
private theorem pr433079 : Nat.Prime 433079 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv79,pv2741]) (by decide +kernel)
def pv433079 : PrimeValue := ⟨433079, pr433079⟩
private theorem pr433087 : Nat.Prime 433087 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv29,pv131]) (by decide +kernel)
def pv433087 : PrimeValue := ⟨433087, pr433087⟩
private theorem pr433099 : Nat.Prime 433099 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv24061]) (by decide +kernel)
def pv433099 : PrimeValue := ⟨433099, pr433099⟩
private theorem pr433117 : Nat.Prime 433117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv53,pv227]) (by decide +kernel)
def pv433117 : PrimeValue := ⟨433117, pr433117⟩
private theorem pr433141 : Nat.Prime 433141 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv3,pv5,pv7219]) (by decide +kernel)
def pv433141 : PrimeValue := ⟨433141, pr433141⟩
private theorem pr433151 : Nat.Prime 433151 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv8663]) (by decide +kernel)
def pv433151 : PrimeValue := ⟨433151, pr433151⟩
private theorem pr433207 : Nat.Prime 433207 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv41,pv587]) (by decide +kernel)
def pv433207 : PrimeValue := ⟨433207, pr433207⟩
private theorem pr433259 : Nat.Prime 433259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv4421]) (by decide +kernel)
def pv433259 : PrimeValue := ⟨433259, pr433259⟩
private theorem pr433271 : Nat.Prime 433271 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv37,pv1171]) (by decide +kernel)
def pv433271 : PrimeValue := ⟨433271, pr433271⟩
private theorem pr433291 : Nat.Prime 433291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv13,pv101]) (by decide +kernel)
def pv433291 : PrimeValue := ⟨433291, pr433291⟩
private theorem pr433319 : Nat.Prime 433319 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv29,pv31,pv241]) (by decide +kernel)
def pv433319 : PrimeValue := ⟨433319, pr433319⟩
private theorem pr433373 : Nat.Prime 433373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv108343]) (by decide +kernel)
def pv433373 : PrimeValue := ⟨433373, pr433373⟩
private theorem pr433421 : Nat.Prime 433421 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv1667]) (by decide +kernel)
def pv433421 : PrimeValue := ⟨433421, pr433421⟩
private theorem pr433549 : Nat.Prime 433549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv12043]) (by decide +kernel)
def pv433549 : PrimeValue := ⟨433549, pr433549⟩
private theorem pr433571 : Nat.Prime 433571 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv191,pv227]) (by decide +kernel)
def pv433571 : PrimeValue := ⟨433571, pr433571⟩
private theorem pr433577 : Nat.Prime 433577 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv13,pv379]) (by decide +kernel)
def pv433577 : PrimeValue := ⟨433577, pr433577⟩
private theorem pr433627 : Nat.Prime 433627 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv72271]) (by decide +kernel)
def pv433627 : PrimeValue := ⟨433627, pr433627⟩
private theorem pr433633 : Nat.Prime 433633 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv4517]) (by decide +kernel)
def pv433633 : PrimeValue := ⟨433633, pr433633⟩
private theorem pr433663 : Nat.Prime 433663 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv72277]) (by decide +kernel)
def pv433663 : PrimeValue := ⟨433663, pr433663⟩
private theorem pr433681 : Nat.Prime 433681 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv13,pv139]) (by decide +kernel)
def pv433681 : PrimeValue := ⟨433681, pr433681⟩
private theorem pr433729 : Nat.Prime 433729 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv251]) (by decide +kernel)
def pv433729 : PrimeValue := ⟨433729, pr433729⟩
private theorem pr433747 : Nat.Prime 433747 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv24097]) (by decide +kernel)
def pv433747 : PrimeValue := ⟨433747, pr433747⟩
private theorem pr433777 : Nat.Prime 433777 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv1291]) (by decide +kernel)
def pv433777 : PrimeValue := ⟨433777, pr433777⟩
private theorem pr433781 : Nat.Prime 433781 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23,pv41]) (by decide +kernel)
def pv433781 : PrimeValue := ⟨433781, pr433781⟩
private theorem pr433787 : Nat.Prime 433787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv89,pv2437]) (by decide +kernel)
def pv433787 : PrimeValue := ⟨433787, pr433787⟩
private theorem pr433813 : Nat.Prime 433813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv36151]) (by decide +kernel)
def pv433813 : PrimeValue := ⟨433813, pr433813⟩
private theorem pr433859 : Nat.Prime 433859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53,pv4093]) (by decide +kernel)
def pv433859 : PrimeValue := ⟨433859, pr433859⟩
private theorem pr433883 : Nat.Prime 433883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv401,pv541]) (by decide +kernel)
def pv433883 : PrimeValue := ⟨433883, pr433883⟩
private theorem pr433943 : Nat.Prime 433943 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv12763]) (by decide +kernel)
def pv433943 : PrimeValue := ⟨433943, pr433943⟩
private theorem pr434009 : Nat.Prime 434009 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv54251]) (by decide +kernel)
def pv434009 : PrimeValue := ⟨434009, pr434009⟩
private theorem pr434087 : Nat.Prime 434087 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv127,pv1709]) (by decide +kernel)
def pv434087 : PrimeValue := ⟨434087, pr434087⟩
private theorem pr434113 : Nat.Prime 434113 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv17,pv19]) (by decide +kernel)
def pv434113 : PrimeValue := ⟨434113, pr434113⟩
private theorem pr434117 : Nat.Prime 434117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv108529]) (by decide +kernel)
def pv434117 : PrimeValue := ⟨434117, pr434117⟩
private theorem pr434201 : Nat.Prime 434201 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv167]) (by decide +kernel)
def pv434201 : PrimeValue := ⟨434201, pr434201⟩
private theorem pr434243 : Nat.Prime 434243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv217121]) (by decide +kernel)
def pv434243 : PrimeValue := ⟨434243, pr434243⟩
private theorem pr434249 : Nat.Prime 434249 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv31,pv103]) (by decide +kernel)
def pv434249 : PrimeValue := ⟨434249, pr434249⟩
private theorem pr434261 : Nat.Prime 434261 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv21713]) (by decide +kernel)
def pv434261 : PrimeValue := ⟨434261, pr434261⟩
private theorem pr434303 : Nat.Prime 434303 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv19,pv1039]) (by decide +kernel)
def pv434303 : PrimeValue := ⟨434303, pr434303⟩
private theorem pr434353 : Nat.Prime 434353 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv9049]) (by decide +kernel)
def pv434353 : PrimeValue := ⟨434353, pr434353⟩
private theorem pr434363 : Nat.Prime 434363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv7489]) (by decide +kernel)
def pv434363 : PrimeValue := ⟨434363, pr434363⟩
private theorem pr434431 : Nat.Prime 434431 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv1609]) (by decide +kernel)
def pv434431 : PrimeValue := ⟨434431, pr434431⟩
private theorem pr434459 : Nat.Prime 434459 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv217229]) (by decide +kernel)
def pv434459 : PrimeValue := ⟨434459, pr434459⟩
private theorem pr434461 : Nat.Prime 434461 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv557]) (by decide +kernel)
def pv434461 : PrimeValue := ⟨434461, pr434461⟩
private theorem pr434471 : Nat.Prime 434471 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv23,pv1889]) (by decide +kernel)
def pv434471 : PrimeValue := ⟨434471, pr434471⟩
private theorem pr434561 : Nat.Prime 434561 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv97]) (by decide +kernel)
def pv434561 : PrimeValue := ⟨434561, pr434561⟩
private theorem pr434647 : Nat.Prime 434647 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv2683]) (by decide +kernel)
def pv434647 : PrimeValue := ⟨434647, pr434647⟩
private theorem pr434683 : Nat.Prime 434683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv31,pv41]) (by decide +kernel)
def pv434683 : PrimeValue := ⟨434683, pr434683⟩
private theorem pr434699 : Nat.Prime 434699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv19759]) (by decide +kernel)
def pv434699 : PrimeValue := ⟨434699, pr434699⟩
private theorem pr434717 : Nat.Prime 434717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv191,pv569]) (by decide +kernel)
def pv434717 : PrimeValue := ⟨434717, pr434717⟩
private theorem pr434743 : Nat.Prime 434743 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv11,pv941]) (by decide +kernel)
def pv434743 : PrimeValue := ⟨434743, pr434743⟩
private theorem pr434783 : Nat.Prime 434783 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv149,pv1459]) (by decide +kernel)
def pv434783 : PrimeValue := ⟨434783, pr434783⟩
private theorem pr434831 : Nat.Prime 434831 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv11,pv59,pv67]) (by decide +kernel)
def pv434831 : PrimeValue := ⟨434831, pr434831⟩
private theorem pr434839 : Nat.Prime 434839 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv137]) (by decide +kernel)
def pv434839 : PrimeValue := ⟨434839, pr434839⟩
private theorem pr434873 : Nat.Prime 434873 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv2861]) (by decide +kernel)
def pv434873 : PrimeValue := ⟨434873, pr434873⟩
private theorem pr434881 : Nat.Prime 434881 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv151]) (by decide +kernel)
def pv434881 : PrimeValue := ⟨434881, pr434881⟩
private theorem pr434909 : Nat.Prime 434909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv108727]) (by decide +kernel)
def pv434909 : PrimeValue := ⟨434909, pr434909⟩
private theorem pr434923 : Nat.Prime 434923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv173,pv419]) (by decide +kernel)
def pv434923 : PrimeValue := ⟨434923, pr434923⟩
private theorem pr434933 : Nat.Prime 434933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv227,pv479]) (by decide +kernel)
def pv434933 : PrimeValue := ⟨434933, pr434933⟩
private theorem pr434939 : Nat.Prime 434939 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv47,pv661]) (by decide +kernel)
def pv434939 : PrimeValue := ⟨434939, pr434939⟩
private theorem pr434947 : Nat.Prime 434947 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv71,pv1021]) (by decide +kernel)
def pv434947 : PrimeValue := ⟨434947, pr434947⟩
private theorem pr434963 : Nat.Prime 434963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv17,pv1163]) (by decide +kernel)
def pv434963 : PrimeValue := ⟨434963, pr434963⟩
private theorem pr434989 : Nat.Prime 434989 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv43,pv281]) (by decide +kernel)
def pv434989 : PrimeValue := ⟨434989, pr434989⟩
private theorem pr435041 : Nat.Prime 435041 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv2719]) (by decide +kernel)
def pv435041 : PrimeValue := ⟨435041, pr435041⟩
private theorem pr435109 : Nat.Prime 435109 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv101,pv359]) (by decide +kernel)
def pv435109 : PrimeValue := ⟨435109, pr435109⟩
private theorem pr435131 : Nat.Prime 435131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv53,pv821]) (by decide +kernel)
def pv435131 : PrimeValue := ⟨435131, pr435131⟩
private theorem pr435143 : Nat.Prime 435143 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv97,pv2243]) (by decide +kernel)
def pv435143 : PrimeValue := ⟨435143, pr435143⟩
private theorem pr435161 : Nat.Prime 435161 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv23,pv43]) (by decide +kernel)
def pv435161 : PrimeValue := ⟨435161, pr435161⟩
private theorem pr435181 : Nat.Prime 435181 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv7253]) (by decide +kernel)
def pv435181 : PrimeValue := ⟨435181, pr435181⟩
private theorem pr435187 : Nat.Prime 435187 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv8059]) (by decide +kernel)
def pv435187 : PrimeValue := ⟨435187, pr435187⟩
private theorem pr435191 : Nat.Prime 435191 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv6217]) (by decide +kernel)
def pv435191 : PrimeValue := ⟨435191, pr435191⟩
private theorem pr435263 : Nat.Prime 435263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv367,pv593]) (by decide +kernel)
def pv435263 : PrimeValue := ⟨435263, pr435263⟩
private theorem pr435277 : Nat.Prime 435277 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv107,pv113]) (by decide +kernel)
def pv435277 : PrimeValue := ⟨435277, pr435277⟩
private theorem pr435283 : Nat.Prime 435283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv72547]) (by decide +kernel)
def pv435283 : PrimeValue := ⟨435283, pr435283⟩
private theorem pr435287 : Nat.Prime 435287 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv217643]) (by decide +kernel)
def pv435287 : PrimeValue := ⟨435287, pr435287⟩
private theorem pr435343 : Nat.Prime 435343 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv37,pv53]) (by decide +kernel)
def pv435343 : PrimeValue := ⟨435343, pr435343⟩
private theorem pr435371 : Nat.Prime 435371 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv13,pv17,pv197]) (by decide +kernel)
def pv435371 : PrimeValue := ⟨435371, pr435371⟩
private theorem pr435397 : Nat.Prime 435397 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv2791]) (by decide +kernel)
def pv435397 : PrimeValue := ⟨435397, pr435397⟩
private theorem pr435401 : Nat.Prime 435401 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv311]) (by decide +kernel)
def pv435401 : PrimeValue := ⟨435401, pr435401⟩
private theorem pr435403 : Nat.Prime 435403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv733]) (by decide +kernel)
def pv435403 : PrimeValue := ⟨435403, pr435403⟩
private theorem pr435439 : Nat.Prime 435439 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv1423]) (by decide +kernel)
def pv435439 : PrimeValue := ⟨435439, pr435439⟩
private theorem pr435451 : Nat.Prime 435451 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv2903]) (by decide +kernel)
def pv435451 : PrimeValue := ⟨435451, pr435451⟩
private theorem pr435577 : Nat.Prime 435577 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv18149]) (by decide +kernel)
def pv435577 : PrimeValue := ⟨435577, pr435577⟩
private theorem pr435623 : Nat.Prime 435623 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv19801]) (by decide +kernel)
def pv435623 : PrimeValue := ⟨435623, pr435623⟩
private theorem pr435641 : Nat.Prime 435641 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv10891]) (by decide +kernel)
def pv435641 : PrimeValue := ⟨435641, pr435641⟩
private theorem pr435647 : Nat.Prime 435647 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv217823]) (by decide +kernel)
def pv435647 : PrimeValue := ⟨435647, pr435647⟩
private theorem pr435731 : Nat.Prime 435731 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv43573]) (by decide +kernel)
def pv435731 : PrimeValue := ⟨435731, pr435731⟩
private theorem pr435839 : Nat.Prime 435839 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv13,pv16763]) (by decide +kernel)
def pv435839 : PrimeValue := ⟨435839, pr435839⟩
private theorem pr435847 : Nat.Prime 435847 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv4273]) (by decide +kernel)
def pv435847 : PrimeValue := ⟨435847, pr435847⟩
private theorem pr435859 : Nat.Prime 435859 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv72643]) (by decide +kernel)
def pv435859 : PrimeValue := ⟨435859, pr435859⟩
private theorem pr435881 : Nat.Prime 435881 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17,pv641]) (by decide +kernel)
def pv435881 : PrimeValue := ⟨435881, pr435881⟩
private theorem pr435889 : Nat.Prime 435889 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv1009]) (by decide +kernel)
def pv435889 : PrimeValue := ⟨435889, pr435889⟩
private theorem pr435893 : Nat.Prime 435893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv59,pv1847]) (by decide +kernel)
def pv435893 : PrimeValue := ⟨435893, pr435893⟩
private theorem pr435907 : Nat.Prime 435907 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv61,pv397]) (by decide +kernel)
def pv435907 : PrimeValue := ⟨435907, pr435907⟩
private theorem pr435973 : Nat.Prime 435973 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv47,pv773]) (by decide +kernel)
def pv435973 : PrimeValue := ⟨435973, pr435973⟩
private theorem pr435997 : Nat.Prime 435997 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv367]) (by decide +kernel)
def pv435997 : PrimeValue := ⟨435997, pr435997⟩
private theorem pr436147 : Nat.Prime 436147 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv157,pv463]) (by decide +kernel)
def pv436147 : PrimeValue := ⟨436147, pr436147⟩
private theorem pr436253 : Nat.Prime 436253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv109063]) (by decide +kernel)
def pv436253 : PrimeValue := ⟨436253, pr436253⟩
private theorem pr436283 : Nat.Prime 436283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv2833]) (by decide +kernel)
def pv436283 : PrimeValue := ⟨436283, pr436283⟩
private theorem pr436343 : Nat.Prime 436343 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv218171]) (by decide +kernel)
def pv436343 : PrimeValue := ⟨436343, pr436343⟩
private theorem pr436417 : Nat.Prime 436417 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2273]) (by decide +kernel)
def pv436417 : PrimeValue := ⟨436417, pr436417⟩
private theorem pr436463 : Nat.Prime 436463 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv16787]) (by decide +kernel)
def pv436463 : PrimeValue := ⟨436463, pr436463⟩
private theorem pr436507 : Nat.Prime 436507 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv19,pv547]) (by decide +kernel)
def pv436507 : PrimeValue := ⟨436507, pr436507⟩
private theorem pr436673 : Nat.Prime 436673 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv6823]) (by decide +kernel)
def pv436673 : PrimeValue := ⟨436673, pr436673⟩
private theorem pr436853 : Nat.Prime 436853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv31,pv271]) (by decide +kernel)
def pv436853 : PrimeValue := ⟨436853, pr436853⟩
private theorem pr436963 : Nat.Prime 436963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv3833]) (by decide +kernel)
def pv436963 : PrimeValue := ⟨436963, pr436963⟩
private theorem pr436979 : Nat.Prime 436979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv73]) (by decide +kernel)
def pv436979 : PrimeValue := ⟨436979, pr436979⟩
private theorem pr437071 : Nat.Prime 437071 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv17,pv857]) (by decide +kernel)
def pv437071 : PrimeValue := ⟨437071, pr437071⟩
private theorem pr437083 : Nat.Prime 437083 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv97,pv751]) (by decide +kernel)
def pv437083 : PrimeValue := ⟨437083, pr437083⟩
private theorem pr437093 : Nat.Prime 437093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv4751]) (by decide +kernel)
def pv437093 : PrimeValue := ⟨437093, pr437093⟩
private theorem pr437113 : Nat.Prime 437113 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv467]) (by decide +kernel)
def pv437113 : PrimeValue := ⟨437113, pr437113⟩
private theorem pr437191 : Nat.Prime 437191 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv13,pv19,pv59]) (by decide +kernel)
def pv437191 : PrimeValue := ⟨437191, pr437191⟩
private theorem pr437201 : Nat.Prime 437201 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv1093]) (by decide +kernel)
def pv437201 : PrimeValue := ⟨437201, pr437201⟩
private theorem pr437243 : Nat.Prime 437243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv67,pv251]) (by decide +kernel)
def pv437243 : PrimeValue := ⟨437243, pr437243⟩
private theorem pr437273 : Nat.Prime 437273 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv4969]) (by decide +kernel)
def pv437273 : PrimeValue := ⟨437273, pr437273⟩
private theorem pr437287 : Nat.Prime 437287 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv31,pv2351]) (by decide +kernel)
def pv437287 : PrimeValue := ⟨437287, pr437287⟩
private theorem pr437293 : Nat.Prime 437293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4049]) (by decide +kernel)
def pv437293 : PrimeValue := ⟨437293, pr437293⟩
private theorem pr437351 : Nat.Prime 437351 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv8747]) (by decide +kernel)
def pv437351 : PrimeValue := ⟨437351, pr437351⟩
private theorem pr437363 : Nat.Prime 437363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv218681]) (by decide +kernel)
def pv437363 : PrimeValue := ⟨437363, pr437363⟩
private theorem pr437467 : Nat.Prime 437467 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv72911]) (by decide +kernel)
def pv437467 : PrimeValue := ⟨437467, pr437467⟩
private theorem pr437509 : Nat.Prime 437509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4051]) (by decide +kernel)
def pv437509 : PrimeValue := ⟨437509, pr437509⟩
private theorem pr437527 : Nat.Prime 437527 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv109,pv223]) (by decide +kernel)
def pv437527 : PrimeValue := ⟨437527, pr437527⟩
private theorem pr437587 : Nat.Prime 437587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv72931]) (by decide +kernel)
def pv437587 : PrimeValue := ⟨437587, pr437587⟩
private theorem pr437651 : Nat.Prime 437651 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv8753]) (by decide +kernel)
def pv437651 : PrimeValue := ⟨437651, pr437651⟩
private theorem pr437681 : Nat.Prime 437681 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv5471]) (by decide +kernel)
def pv437681 : PrimeValue := ⟨437681, pr437681⟩
private theorem pr437771 : Nat.Prime 437771 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv43777]) (by decide +kernel)
def pv437771 : PrimeValue := ⟨437771, pr437771⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
