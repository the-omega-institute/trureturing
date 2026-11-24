/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table080
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table080.pv269641
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table011
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table012
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table018
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table048
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table049

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr269641 : Nat.Prime 269641 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv107]) (by decide +kernel)
def pv269641 : PrimeValue := ⟨269641, pr269641⟩
private theorem pr269651 : Nat.Prime 269651 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv5393]) (by decide +kernel)
def pv269651 : PrimeValue := ⟨269651, pr269651⟩
private theorem pr269683 : Nat.Prime 269683 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv6421]) (by decide +kernel)
def pv269683 : PrimeValue := ⟨269683, pr269683⟩
private theorem pr269701 : Nat.Prime 269701 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv29,pv31]) (by decide +kernel)
def pv269701 : PrimeValue := ⟨269701, pr269701⟩
private theorem pr269713 : Nat.Prime 269713 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1873]) (by decide +kernel)
def pv269713 : PrimeValue := ⟨269713, pr269713⟩
private theorem pr269723 : Nat.Prime 269723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv7933]) (by decide +kernel)
def pv269723 : PrimeValue := ⟨269723, pr269723⟩
private theorem pr269749 : Nat.Prime 269749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv59,pv127]) (by decide +kernel)
def pv269749 : PrimeValue := ⟨269749, pr269749⟩
private theorem pr269783 : Nat.Prime 269783 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv43,pv3137]) (by decide +kernel)
def pv269783 : PrimeValue := ⟨269783, pr269783⟩
private theorem pr269791 : Nat.Prime 269791 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv17,pv23]) (by decide +kernel)
def pv269791 : PrimeValue := ⟨269791, pr269791⟩
private theorem pr269891 : Nat.Prime 269891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv137,pv197]) (by decide +kernel)
def pv269891 : PrimeValue := ⟨269891, pr269891⟩
private theorem pr269897 : Nat.Prime 269897 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv3067]) (by decide +kernel)
def pv269897 : PrimeValue := ⟨269897, pr269897⟩
private theorem pr269923 : Nat.Prime 269923 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv44987]) (by decide +kernel)
def pv269923 : PrimeValue := ⟨269923, pr269923⟩
private theorem pr269939 : Nat.Prime 269939 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv139,pv971]) (by decide +kernel)
def pv269939 : PrimeValue := ⟨269939, pr269939⟩
private theorem pr269947 : Nat.Prime 269947 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv4999]) (by decide +kernel)
def pv269947 : PrimeValue := ⟨269947, pr269947⟩
private theorem pr269953 : Nat.Prime 269953 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv37]) (by decide +kernel)
def pv269953 : PrimeValue := ⟨269953, pr269953⟩
private theorem pr269981 : Nat.Prime 269981 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13499]) (by decide +kernel)
def pv269981 : PrimeValue := ⟨269981, pr269981⟩
private theorem pr269987 : Nat.Prime 269987 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv2213]) (by decide +kernel)
def pv269987 : PrimeValue := ⟨269987, pr269987⟩
private theorem pr270029 : Nat.Prime 270029 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv17,pv19]) (by decide +kernel)
def pv270029 : PrimeValue := ⟨270029, pr270029⟩
private theorem pr270059 : Nat.Prime 270059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv135029]) (by decide +kernel)
def pv270059 : PrimeValue := ⟨270059, pr270059⟩
private theorem pr270073 : Nat.Prime 270073 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv31]) (by decide +kernel)
def pv270073 : PrimeValue := ⟨270073, pr270073⟩
private theorem pr270131 : Nat.Prime 270131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv17,pv227]) (by decide +kernel)
def pv270131 : PrimeValue := ⟨270131, pr270131⟩
private theorem pr270133 : Nat.Prime 270133 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv22511]) (by decide +kernel)
def pv270133 : PrimeValue := ⟨270133, pr270133⟩
private theorem pr270157 : Nat.Prime 270157 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv47,pv479]) (by decide +kernel)
def pv270157 : PrimeValue := ⟨270157, pr270157⟩
private theorem pr270163 : Nat.Prime 270163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5003]) (by decide +kernel)
def pv270163 : PrimeValue := ⟨270163, pr270163⟩
private theorem pr270167 : Nat.Prime 270167 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv10391]) (by decide +kernel)
def pv270167 : PrimeValue := ⟨270167, pr270167⟩
private theorem pr270191 : Nat.Prime 270191 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv41,pv659]) (by decide +kernel)
def pv270191 : PrimeValue := ⟨270191, pr270191⟩
private theorem pr270209 : Nat.Prime 270209 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2111]) (by decide +kernel)
def pv270209 : PrimeValue := ⟨270209, pr270209⟩
private theorem pr270223 : Nat.Prime 270223 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv29,pv1553]) (by decide +kernel)
def pv270223 : PrimeValue := ⟨270223, pr270223⟩
private theorem pr270269 : Nat.Prime 270269 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv67567]) (by decide +kernel)
def pv270269 : PrimeValue := ⟨270269, pr270269⟩
private theorem pr270287 : Nat.Prime 270287 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv149,pv907]) (by decide +kernel)
def pv270287 : PrimeValue := ⟨270287, pr270287⟩
private theorem pr270299 : Nat.Prime 270299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv43,pv449]) (by decide +kernel)
def pv270299 : PrimeValue := ⟨270299, pr270299⟩
private theorem pr270307 : Nat.Prime 270307 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv15017]) (by decide +kernel)
def pv270307 : PrimeValue := ⟨270307, pr270307⟩
private theorem pr270311 : Nat.Prime 270311 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv27031]) (by decide +kernel)
def pv270311 : PrimeValue := ⟨270311, pr270311⟩
private theorem pr270343 : Nat.Prime 270343 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv653]) (by decide +kernel)
def pv270343 : PrimeValue := ⟨270343, pr270343⟩
private theorem pr270443 : Nat.Prime 270443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv135221]) (by decide +kernel)
def pv270443 : PrimeValue := ⟨270443, pr270443⟩
private theorem pr270451 : Nat.Prime 270451 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv601]) (by decide +kernel)
def pv270451 : PrimeValue := ⟨270451, pr270451⟩
private theorem pr270463 : Nat.Prime 270463 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv45077]) (by decide +kernel)
def pv270463 : PrimeValue := ⟨270463, pr270463⟩
private theorem pr270493 : Nat.Prime 270493 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv22541]) (by decide +kernel)
def pv270493 : PrimeValue := ⟨270493, pr270493⟩
private theorem pr270509 : Nat.Prime 270509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv9661]) (by decide +kernel)
def pv270509 : PrimeValue := ⟨270509, pr270509⟩
private theorem pr270527 : Nat.Prime 270527 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv23,pv5881]) (by decide +kernel)
def pv270527 : PrimeValue := ⟨270527, pr270527⟩
private theorem pr270539 : Nat.Prime 270539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv73,pv109]) (by decide +kernel)
def pv270539 : PrimeValue := ⟨270539, pr270539⟩
private theorem pr270547 : Nat.Prime 270547 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv67,pv673]) (by decide +kernel)
def pv270547 : PrimeValue := ⟨270547, pr270547⟩
private theorem pr270551 : Nat.Prime 270551 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv773]) (by decide +kernel)
def pv270551 : PrimeValue := ⟨270551, pr270551⟩
private theorem pr270553 : Nat.Prime 270553 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11273]) (by decide +kernel)
def pv270553 : PrimeValue := ⟨270553, pr270553⟩
private theorem pr270577 : Nat.Prime 270577 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv1879]) (by decide +kernel)
def pv270577 : PrimeValue := ⟨270577, pr270577⟩
private theorem pr270583 : Nat.Prime 270583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv3469]) (by decide +kernel)
def pv270583 : PrimeValue := ⟨270583, pr270583⟩
private theorem pr270619 : Nat.Prime 270619 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv37,pv53]) (by decide +kernel)
def pv270619 : PrimeValue := ⟨270619, pr270619⟩
private theorem pr270653 : Nat.Prime 270653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv71,pv953]) (by decide +kernel)
def pv270653 : PrimeValue := ⟨270653, pr270653⟩
private theorem pr270679 : Nat.Prime 270679 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv197,pv229]) (by decide +kernel)
def pv270679 : PrimeValue := ⟨270679, pr270679⟩
private theorem pr270689 : Nat.Prime 270689 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv769]) (by decide +kernel)
def pv270689 : PrimeValue := ⟨270689, pr270689⟩
private theorem pr270709 : Nat.Prime 270709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv1327]) (by decide +kernel)
def pv270709 : PrimeValue := ⟨270709, pr270709⟩
private theorem pr270719 : Nat.Prime 270719 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv61,pv317]) (by decide +kernel)
def pv270719 : PrimeValue := ⟨270719, pr270719⟩
private theorem pr270737 : Nat.Prime 270737 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv16921]) (by decide +kernel)
def pv270737 : PrimeValue := ⟨270737, pr270737⟩
private theorem pr270761 : Nat.Prime 270761 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv967]) (by decide +kernel)
def pv270761 : PrimeValue := ⟨270761, pr270761⟩
private theorem pr270833 : Nat.Prime 270833 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv16927]) (by decide +kernel)
def pv270833 : PrimeValue := ⟨270833, pr270833⟩
private theorem pr270899 : Nat.Prime 270899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv135449]) (by decide +kernel)
def pv270899 : PrimeValue := ⟨270899, pr270899⟩
private theorem pr270923 : Nat.Prime 270923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv135461]) (by decide +kernel)
def pv270923 : PrimeValue := ⟨270923, pr270923⟩
private theorem pr270931 : Nat.Prime 270931 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv821]) (by decide +kernel)
def pv270931 : PrimeValue := ⟨270931, pr270931⟩
private theorem pr270937 : Nat.Prime 270937 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv53,pv71]) (by decide +kernel)
def pv270937 : PrimeValue := ⟨270937, pr270937⟩
private theorem pr270953 : Nat.Prime 270953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv3079]) (by decide +kernel)
def pv270953 : PrimeValue := ⟨270953, pr270953⟩
private theorem pr270961 : Nat.Prime 270961 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv1129]) (by decide +kernel)
def pv270961 : PrimeValue := ⟨270961, pr270961⟩
private theorem pr270967 : Nat.Prime 270967 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv45161]) (by decide +kernel)
def pv270967 : PrimeValue := ⟨270967, pr270967⟩
private theorem pr270973 : Nat.Prime 270973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv193]) (by decide +kernel)
def pv270973 : PrimeValue := ⟨270973, pr270973⟩
private theorem pr271013 : Nat.Prime 271013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv9679]) (by decide +kernel)
def pv271013 : PrimeValue := ⟨271013, pr271013⟩
private theorem pr271021 : Nat.Prime 271021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv4517]) (by decide +kernel)
def pv271021 : PrimeValue := ⟨271021, pr271021⟩
private theorem pr271043 : Nat.Prime 271043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53,pv2557]) (by decide +kernel)
def pv271043 : PrimeValue := ⟨271043, pr271043⟩
private theorem pr271057 : Nat.Prime 271057 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv5647]) (by decide +kernel)
def pv271057 : PrimeValue := ⟨271057, pr271057⟩
private theorem pr271109 : Nat.Prime 271109 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv67777]) (by decide +kernel)
def pv271109 : PrimeValue := ⟨271109, pr271109⟩
private theorem pr271127 : Nat.Prime 271127 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv31,pv4373]) (by decide +kernel)
def pv271127 : PrimeValue := ⟨271127, pr271127⟩
private theorem pr271163 : Nat.Prime 271163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv135581]) (by decide +kernel)
def pv271163 : PrimeValue := ⟨271163, pr271163⟩
private theorem pr271177 : Nat.Prime 271177 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11299]) (by decide +kernel)
def pv271177 : PrimeValue := ⟨271177, pr271177⟩
private theorem pr271211 : Nat.Prime 271211 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv37,pv733]) (by decide +kernel)
def pv271211 : PrimeValue := ⟨271211, pr271211⟩
private theorem pr271231 : Nat.Prime 271231 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv9041]) (by decide +kernel)
def pv271231 : PrimeValue := ⟨271231, pr271231⟩
private theorem pr271241 : Nat.Prime 271241 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv6781]) (by decide +kernel)
def pv271241 : PrimeValue := ⟨271241, pr271241⟩
private theorem pr271289 : Nat.Prime 271289 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv33911]) (by decide +kernel)
def pv271289 : PrimeValue := ⟨271289, pr271289⟩
private theorem pr271357 : Nat.Prime 271357 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv22613]) (by decide +kernel)
def pv271357 : PrimeValue := ⟨271357, pr271357⟩
private theorem pr271367 : Nat.Prime 271367 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv241,pv563]) (by decide +kernel)
def pv271367 : PrimeValue := ⟨271367, pr271367⟩
private theorem pr271393 : Nat.Prime 271393 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv257]) (by decide +kernel)
def pv271393 : PrimeValue := ⟨271393, pr271393⟩
private theorem pr271451 : Nat.Prime 271451 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv61,pv89]) (by decide +kernel)
def pv271451 : PrimeValue := ⟨271451, pr271451⟩
private theorem pr271463 : Nat.Prime 271463 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv135731]) (by decide +kernel)
def pv271463 : PrimeValue := ⟨271463, pr271463⟩
private theorem pr271471 : Nat.Prime 271471 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv9049]) (by decide +kernel)
def pv271471 : PrimeValue := ⟨271471, pr271471⟩
private theorem pr271483 : Nat.Prime 271483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv45247]) (by decide +kernel)
def pv271483 : PrimeValue := ⟨271483, pr271483⟩
private theorem pr271489 : Nat.Prime 271489 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv7,pv101]) (by decide +kernel)
def pv271489 : PrimeValue := ⟨271489, pr271489⟩
private theorem pr271499 : Nat.Prime 271499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv31,pv151]) (by decide +kernel)
def pv271499 : PrimeValue := ⟨271499, pr271499⟩
private theorem pr271501 : Nat.Prime 271501 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv181]) (by decide +kernel)
def pv271501 : PrimeValue := ⟨271501, pr271501⟩
private theorem pr271549 : Nat.Prime 271549 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv19,pv397]) (by decide +kernel)
def pv271549 : PrimeValue := ⟨271549, pr271549⟩
private theorem pr271553 : Nat.Prime 271553 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv4243]) (by decide +kernel)
def pv271553 : PrimeValue := ⟨271553, pr271553⟩
private theorem pr271571 : Nat.Prime 271571 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv2089]) (by decide +kernel)
def pv271571 : PrimeValue := ⟨271571, pr271571⟩
private theorem pr271573 : Nat.Prime 271573 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv53,pv61]) (by decide +kernel)
def pv271573 : PrimeValue := ⟨271573, pr271573⟩
private theorem pr271597 : Nat.Prime 271597 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv1741]) (by decide +kernel)
def pv271597 : PrimeValue := ⟨271597, pr271597⟩
private theorem pr271603 : Nat.Prime 271603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv79,pv191]) (by decide +kernel)
def pv271603 : PrimeValue := ⟨271603, pr271603⟩
private theorem pr271619 : Nat.Prime 271619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv67,pv2027]) (by decide +kernel)
def pv271619 : PrimeValue := ⟨271619, pr271619⟩
private theorem pr271639 : Nat.Prime 271639 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv15091]) (by decide +kernel)
def pv271639 : PrimeValue := ⟨271639, pr271639⟩
private theorem pr271693 : Nat.Prime 271693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7547]) (by decide +kernel)
def pv271693 : PrimeValue := ⟨271693, pr271693⟩
private theorem pr271703 : Nat.Prime 271703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv135851]) (by decide +kernel)
def pv271703 : PrimeValue := ⟨271703, pr271703⟩
private theorem pr271723 : Nat.Prime 271723 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv23,pv179]) (by decide +kernel)
def pv271723 : PrimeValue := ⟨271723, pr271723⟩
private theorem pr271729 : Nat.Prime 271729 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv17,pv37]) (by decide +kernel)
def pv271729 : PrimeValue := ⟨271729, pr271729⟩
private theorem pr271769 : Nat.Prime 271769 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv7,pv23,pv211]) (by decide +kernel)
def pv271769 : PrimeValue := ⟨271769, pr271769⟩
private theorem pr271771 : Nat.Prime 271771 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv9059]) (by decide +kernel)
def pv271771 : PrimeValue := ⟨271771, pr271771⟩
private theorem pr271807 : Nat.Prime 271807 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv89,pv509]) (by decide +kernel)
def pv271807 : PrimeValue := ⟨271807, pr271807⟩
private theorem pr271811 : Nat.Prime 271811 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv353]) (by decide +kernel)
def pv271811 : PrimeValue := ⟨271811, pr271811⟩
private theorem pr271829 : Nat.Prime 271829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv67957]) (by decide +kernel)
def pv271829 : PrimeValue := ⟨271829, pr271829⟩
private theorem pr271841 : Nat.Prime 271841 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv1699]) (by decide +kernel)
def pv271841 : PrimeValue := ⟨271841, pr271841⟩
private theorem pr271853 : Nat.Prime 271853 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv19,pv73]) (by decide +kernel)
def pv271853 : PrimeValue := ⟨271853, pr271853⟩
private theorem pr271867 : Nat.Prime 271867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv6473]) (by decide +kernel)
def pv271867 : PrimeValue := ⟨271867, pr271867⟩
private theorem pr271879 : Nat.Prime 271879 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv113,pv401]) (by decide +kernel)
def pv271879 : PrimeValue := ⟨271879, pr271879⟩
private theorem pr271897 : Nat.Prime 271897 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11329]) (by decide +kernel)
def pv271897 : PrimeValue := ⟨271897, pr271897⟩
private theorem pr271903 : Nat.Prime 271903 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv45317]) (by decide +kernel)
def pv271903 : PrimeValue := ⟨271903, pr271903⟩
private theorem pr271919 : Nat.Prime 271919 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv79,pv1721]) (by decide +kernel)
def pv271919 : PrimeValue := ⟨271919, pr271919⟩
private theorem pr271939 : Nat.Prime 271939 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv61,pv743]) (by decide +kernel)
def pv271939 : PrimeValue := ⟨271939, pr271939⟩
private theorem pr271967 : Nat.Prime 271967 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv19,pv421]) (by decide +kernel)
def pv271967 : PrimeValue := ⟨271967, pr271967⟩
private theorem pr271969 : Nat.Prime 271969 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv2833]) (by decide +kernel)
def pv271969 : PrimeValue := ⟨271969, pr271969⟩
private theorem pr271981 : Nat.Prime 271981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1511]) (by decide +kernel)
def pv271981 : PrimeValue := ⟨271981, pr271981⟩
private theorem pr272003 : Nat.Prime 272003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv307,pv443]) (by decide +kernel)
def pv272003 : PrimeValue := ⟨272003, pr272003⟩
private theorem pr272009 : Nat.Prime 272009 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv281]) (by decide +kernel)
def pv272009 : PrimeValue := ⟨272009, pr272009⟩
private theorem pr272039 : Nat.Prime 272039 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv13,pv10463]) (by decide +kernel)
def pv272039 : PrimeValue := ⟨272039, pr272039⟩
private theorem pr272059 : Nat.Prime 272059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv45343]) (by decide +kernel)
def pv272059 : PrimeValue := ⟨272059, pr272059⟩
private theorem pr272131 : Nat.Prime 272131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv47,pv193]) (by decide +kernel)
def pv272131 : PrimeValue := ⟨272131, pr272131⟩
private theorem pr272141 : Nat.Prime 272141 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv1237]) (by decide +kernel)
def pv272141 : PrimeValue := ⟨272141, pr272141⟩
private theorem pr272183 : Nat.Prime 272183 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv23,pv61,pv97]) (by decide +kernel)
def pv272183 : PrimeValue := ⟨272183, pr272183⟩
private theorem pr272189 : Nat.Prime 272189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv9721]) (by decide +kernel)
def pv272189 : PrimeValue := ⟨272189, pr272189⟩
private theorem pr272191 : Nat.Prime 272191 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv43,pv211]) (by decide +kernel)
def pv272191 : PrimeValue := ⟨272191, pr272191⟩
private theorem pr272201 : Nat.Prime 272201 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv1361]) (by decide +kernel)
def pv272201 : PrimeValue := ⟨272201, pr272201⟩
private theorem pr272227 : Nat.Prime 272227 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv59,pv769]) (by decide +kernel)
def pv272227 : PrimeValue := ⟨272227, pr272227⟩
private theorem pr272231 : Nat.Prime 272231 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv3889]) (by decide +kernel)
def pv272231 : PrimeValue := ⟨272231, pr272231⟩
private theorem pr272257 : Nat.Prime 272257 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv709]) (by decide +kernel)
def pv272257 : PrimeValue := ⟨272257, pr272257⟩
private theorem pr272263 : Nat.Prime 272263 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv45377]) (by decide +kernel)
def pv272263 : PrimeValue := ⟨272263, pr272263⟩
private theorem pr272267 : Nat.Prime 272267 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv136133]) (by decide +kernel)
def pv272267 : PrimeValue := ⟨272267, pr272267⟩
private theorem pr272269 : Nat.Prime 272269 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2521]) (by decide +kernel)
def pv272269 : PrimeValue := ⟨272269, pr272269⟩
private theorem pr272299 : Nat.Prime 272299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv3491]) (by decide +kernel)
def pv272299 : PrimeValue := ⟨272299, pr272299⟩
private theorem pr272317 : Nat.Prime 272317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv2063]) (by decide +kernel)
def pv272317 : PrimeValue := ⟨272317, pr272317⟩
private theorem pr272333 : Nat.Prime 272333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv103,pv661]) (by decide +kernel)
def pv272333 : PrimeValue := ⟨272333, pr272333⟩
private theorem pr272341 : Nat.Prime 272341 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv17,pv89]) (by decide +kernel)
def pv272341 : PrimeValue := ⟨272341, pr272341⟩
private theorem pr272351 : Nat.Prime 272351 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv419]) (by decide +kernel)
def pv272351 : PrimeValue := ⟨272351, pr272351⟩
private theorem pr272381 : Nat.Prime 272381 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13619]) (by decide +kernel)
def pv272381 : PrimeValue := ⟨272381, pr272381⟩
private theorem pr272407 : Nat.Prime 272407 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv83,pv547]) (by decide +kernel)
def pv272407 : PrimeValue := ⟨272407, pr272407⟩
private theorem pr272453 : Nat.Prime 272453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv68113]) (by decide +kernel)
def pv272453 : PrimeValue := ⟨272453, pr272453⟩
private theorem pr272533 : Nat.Prime 272533 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv13,pv1747]) (by decide +kernel)
def pv272533 : PrimeValue := ⟨272533, pr272533⟩
private theorem pr272549 : Nat.Prime 272549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv1117]) (by decide +kernel)
def pv272549 : PrimeValue := ⟨272549, pr272549⟩
private theorem pr272567 : Nat.Prime 272567 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv19469]) (by decide +kernel)
def pv272567 : PrimeValue := ⟨272567, pr272567⟩
private theorem pr272581 : Nat.Prime 272581 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv7,pv11,pv59]) (by decide +kernel)
def pv272581 : PrimeValue := ⟨272581, pr272581⟩
private theorem pr272603 : Nat.Prime 272603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv12391]) (by decide +kernel)
def pv272603 : PrimeValue := ⟨272603, pr272603⟩
private theorem pr272621 : Nat.Prime 272621 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv43,pv317]) (by decide +kernel)
def pv272621 : PrimeValue := ⟨272621, pr272621⟩
private theorem pr272651 : Nat.Prime 272651 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv19,pv41]) (by decide +kernel)
def pv272651 : PrimeValue := ⟨272651, pr272651⟩
private theorem pr272683 : Nat.Prime 272683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv15149]) (by decide +kernel)
def pv272683 : PrimeValue := ⟨272683, pr272683⟩
private theorem pr272693 : Nat.Prime 272693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv9739]) (by decide +kernel)
def pv272693 : PrimeValue := ⟨272693, pr272693⟩
private theorem pr272717 : Nat.Prime 272717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv2351]) (by decide +kernel)
def pv272717 : PrimeValue := ⟨272717, pr272717⟩
private theorem pr272719 : Nat.Prime 272719 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv109,pv139]) (by decide +kernel)
def pv272719 : PrimeValue := ⟨272719, pr272719⟩
private theorem pr272737 : Nat.Prime 272737 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv947]) (by decide +kernel)
def pv272737 : PrimeValue := ⟨272737, pr272737⟩
private theorem pr272759 : Nat.Prime 272759 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv136379]) (by decide +kernel)
def pv272759 : PrimeValue := ⟨272759, pr272759⟩
private theorem pr272771 : Nat.Prime 272771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv27277]) (by decide +kernel)
def pv272771 : PrimeValue := ⟨272771, pr272771⟩
private theorem pr272863 : Nat.Prime 272863 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv31,pv163]) (by decide +kernel)
def pv272863 : PrimeValue := ⟨272863, pr272863⟩
private theorem pr272879 : Nat.Prime 272879 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv19,pv43,pv167]) (by decide +kernel)
def pv272879 : PrimeValue := ⟨272879, pr272879⟩
private theorem pr272887 : Nat.Prime 272887 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv45481]) (by decide +kernel)
def pv272887 : PrimeValue := ⟨272887, pr272887⟩
private theorem pr272927 : Nat.Prime 272927 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv136463]) (by decide +kernel)
def pv272927 : PrimeValue := ⟨272927, pr272927⟩
private theorem pr272933 : Nat.Prime 272933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv6203]) (by decide +kernel)
def pv272933 : PrimeValue := ⟨272933, pr272933⟩
private theorem pr272959 : Nat.Prime 272959 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv67,pv97]) (by decide +kernel)
def pv272959 : PrimeValue := ⟨272959, pr272959⟩
private theorem pr272981 : Nat.Prime 272981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13649]) (by decide +kernel)
def pv272981 : PrimeValue := ⟨272981, pr272981⟩
private theorem pr272989 : Nat.Prime 272989 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7583]) (by decide +kernel)
def pv272989 : PrimeValue := ⟨272989, pr272989⟩
private theorem pr272999 : Nat.Prime 272999 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv11,pv12409]) (by decide +kernel)
def pv272999 : PrimeValue := ⟨272999, pr272999⟩
private theorem pr273001 : Nat.Prime 273001 :=
  checkPrime_prime (q := pv53) (ls := [pv2,pv3,pv5,pv7,pv13]) (by decide +kernel)
def pv273001 : PrimeValue := ⟨273001, pr273001⟩
private theorem pr273029 : Nat.Prime 273029 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv199]) (by decide +kernel)
def pv273029 : PrimeValue := ⟨273029, pr273029⟩
private theorem pr273043 : Nat.Prime 273043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv197]) (by decide +kernel)
def pv273043 : PrimeValue := ⟨273043, pr273043⟩
private theorem pr273059 : Nat.Prime 273059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv311,pv439]) (by decide +kernel)
def pv273059 : PrimeValue := ⟨273059, pr273059⟩
private theorem pr273067 : Nat.Prime 273067 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv71,pv641]) (by decide +kernel)
def pv273067 : PrimeValue := ⟨273067, pr273067⟩
private theorem pr273083 : Nat.Prime 273083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv136541]) (by decide +kernel)
def pv273083 : PrimeValue := ⟨273083, pr273083⟩
private theorem pr273131 : Nat.Prime 273131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv13,pv191]) (by decide +kernel)
def pv273131 : PrimeValue := ⟨273131, pr273131⟩
private theorem pr273149 : Nat.Prime 273149 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv2969]) (by decide +kernel)
def pv273149 : PrimeValue := ⟨273149, pr273149⟩
private theorem pr273157 : Nat.Prime 273157 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv17,pv103]) (by decide +kernel)
def pv273157 : PrimeValue := ⟨273157, pr273157⟩
private theorem pr273181 : Nat.Prime 273181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv29,pv157]) (by decide +kernel)
def pv273181 : PrimeValue := ⟨273181, pr273181⟩
private theorem pr273193 : Nat.Prime 273193 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv11383]) (by decide +kernel)
def pv273193 : PrimeValue := ⟨273193, pr273193⟩
private theorem pr273233 : Nat.Prime 273233 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17077]) (by decide +kernel)
def pv273233 : PrimeValue := ⟨273233, pr273233⟩
private theorem pr273253 : Nat.Prime 273253 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv3253]) (by decide +kernel)
def pv273253 : PrimeValue := ⟨273253, pr273253⟩
private theorem pr273283 : Nat.Prime 273283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv1231]) (by decide +kernel)
def pv273283 : PrimeValue := ⟨273283, pr273283⟩
private theorem pr273313 : Nat.Prime 273313 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv73]) (by decide +kernel)
def pv273313 : PrimeValue := ⟨273313, pr273313⟩
private theorem pr273359 : Nat.Prime 273359 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv31,pv4409]) (by decide +kernel)
def pv273359 : PrimeValue := ⟨273359, pr273359⟩
private theorem pr273433 : Nat.Prime 273433 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11393]) (by decide +kernel)
def pv273433 : PrimeValue := ⟨273433, pr273433⟩
private theorem pr273473 : Nat.Prime 273473 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv4273]) (by decide +kernel)
def pv273473 : PrimeValue := ⟨273473, pr273473⟩
private theorem pr273503 : Nat.Prime 273503 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv136751]) (by decide +kernel)
def pv273503 : PrimeValue := ⟨273503, pr273503⟩
private theorem pr273517 : Nat.Prime 273517 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv991]) (by decide +kernel)
def pv273517 : PrimeValue := ⟨273517, pr273517⟩
private theorem pr273521 : Nat.Prime 273521 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv263]) (by decide +kernel)
def pv273521 : PrimeValue := ⟨273521, pr273521⟩
private theorem pr273551 : Nat.Prime 273551 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv5471]) (by decide +kernel)
def pv273551 : PrimeValue := ⟨273551, pr273551⟩
private theorem pr273569 : Nat.Prime 273569 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv83,pv103]) (by decide +kernel)
def pv273569 : PrimeValue := ⟨273569, pr273569⟩
private theorem pr273601 : Nat.Prime 273601 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv273601 : PrimeValue := ⟨273601, pr273601⟩
private theorem pr273613 : Nat.Prime 273613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv151]) (by decide +kernel)
def pv273613 : PrimeValue := ⟨273613, pr273613⟩
private theorem pr273643 : Nat.Prime 273643 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv59,pv773]) (by decide +kernel)
def pv273643 : PrimeValue := ⟨273643, pr273643⟩
private theorem pr273653 : Nat.Prime 273653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv43]) (by decide +kernel)
def pv273653 : PrimeValue := ⟨273653, pr273653⟩
private theorem pr273727 : Nat.Prime 273727 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv37,pv137]) (by decide +kernel)
def pv273727 : PrimeValue := ⟨273727, pr273727⟩
private theorem pr273739 : Nat.Prime 273739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv43,pv1061]) (by decide +kernel)
def pv273739 : PrimeValue := ⟨273739, pr273739⟩
private theorem pr273787 : Nat.Prime 273787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv45631]) (by decide +kernel)
def pv273787 : PrimeValue := ⟨273787, pr273787⟩
private theorem pr273821 : Nat.Prime 273821 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13691]) (by decide +kernel)
def pv273821 : PrimeValue := ⟨273821, pr273821⟩
private theorem pr273857 : Nat.Prime 273857 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv389]) (by decide +kernel)
def pv273857 : PrimeValue := ⟨273857, pr273857⟩
private theorem pr273881 : Nat.Prime 273881 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv41,pv167]) (by decide +kernel)
def pv273881 : PrimeValue := ⟨273881, pr273881⟩
private theorem pr273899 : Nat.Prime 273899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv136949]) (by decide +kernel)
def pv273899 : PrimeValue := ⟨273899, pr273899⟩
private theorem pr273913 : Nat.Prime 273913 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv101,pv113]) (by decide +kernel)
def pv273913 : PrimeValue := ⟨273913, pr273913⟩
private theorem pr273919 : Nat.Prime 273919 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv71,pv643]) (by decide +kernel)
def pv273919 : PrimeValue := ⟨273919, pr273919⟩
private theorem pr273929 : Nat.Prime 273929 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv97,pv353]) (by decide +kernel)
def pv273929 : PrimeValue := ⟨273929, pr273929⟩
private theorem pr273941 : Nat.Prime 273941 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13697]) (by decide +kernel)
def pv273941 : PrimeValue := ⟨273941, pr273941⟩
private theorem pr273943 : Nat.Prime 273943 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv89]) (by decide +kernel)
def pv273943 : PrimeValue := ⟨273943, pr273943⟩
private theorem pr273971 : Nat.Prime 273971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv27397]) (by decide +kernel)
def pv273971 : PrimeValue := ⟨273971, pr273971⟩
private theorem pr273997 : Nat.Prime 273997 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv43,pv59]) (by decide +kernel)
def pv273997 : PrimeValue := ⟨273997, pr273997⟩
private theorem pr274019 : Nat.Prime 274019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv7211]) (by decide +kernel)
def pv274019 : PrimeValue := ⟨274019, pr274019⟩
private theorem pr274033 : Nat.Prime 274033 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv173]) (by decide +kernel)
def pv274033 : PrimeValue := ⟨274033, pr274033⟩
private theorem pr274061 : Nat.Prime 274061 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv71,pv193]) (by decide +kernel)
def pv274061 : PrimeValue := ⟨274061, pr274061⟩
private theorem pr274081 : Nat.Prime 274081 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv571]) (by decide +kernel)
def pv274081 : PrimeValue := ⟨274081, pr274081⟩
private theorem pr274093 : Nat.Prime 274093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv251]) (by decide +kernel)
def pv274093 : PrimeValue := ⟨274093, pr274093⟩
private theorem pr274117 : Nat.Prime 274117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv53,pv431]) (by decide +kernel)
def pv274117 : PrimeValue := ⟨274117, pr274117⟩
private theorem pr274121 : Nat.Prime 274121 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv7,pv11,pv89]) (by decide +kernel)
def pv274121 : PrimeValue := ⟨274121, pr274121⟩
private theorem pr274123 : Nat.Prime 274123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv97,pv157]) (by decide +kernel)
def pv274123 : PrimeValue := ⟨274123, pr274123⟩
private theorem pr274147 : Nat.Prime 274147 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv45691]) (by decide +kernel)
def pv274147 : PrimeValue := ⟨274147, pr274147⟩
private theorem pr274187 : Nat.Prime 274187 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv103]) (by decide +kernel)
def pv274187 : PrimeValue := ⟨274187, pr274187⟩
private theorem pr274199 : Nat.Prime 274199 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv47,pv2917]) (by decide +kernel)
def pv274199 : PrimeValue := ⟨274199, pr274199⟩
private theorem pr274213 : Nat.Prime 274213 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv2539]) (by decide +kernel)
def pv274213 : PrimeValue := ⟨274213, pr274213⟩
private theorem pr274237 : Nat.Prime 274237 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv22853]) (by decide +kernel)
def pv274237 : PrimeValue := ⟨274237, pr274237⟩
private theorem pr274243 : Nat.Prime 274243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv45707]) (by decide +kernel)
def pv274243 : PrimeValue := ⟨274243, pr274243⟩
private theorem pr274259 : Nat.Prime 274259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv241,pv569]) (by decide +kernel)
def pv274259 : PrimeValue := ⟨274259, pr274259⟩
private theorem pr274271 : Nat.Prime 274271 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv27427]) (by decide +kernel)
def pv274271 : PrimeValue := ⟨274271, pr274271⟩
private theorem pr274283 : Nat.Prime 274283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv4729]) (by decide +kernel)
def pv274283 : PrimeValue := ⟨274283, pr274283⟩
private theorem pr274333 : Nat.Prime 274333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv22861]) (by decide +kernel)
def pv274333 : PrimeValue := ⟨274333, pr274333⟩
private theorem pr274357 : Nat.Prime 274357 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7621]) (by decide +kernel)
def pv274357 : PrimeValue := ⟨274357, pr274357⟩
private theorem pr274441 : Nat.Prime 274441 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv2287]) (by decide +kernel)
def pv274441 : PrimeValue := ⟨274441, pr274441⟩
private theorem pr274451 : Nat.Prime 274451 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv11,pv499]) (by decide +kernel)
def pv274451 : PrimeValue := ⟨274451, pr274451⟩
private theorem pr274453 : Nat.Prime 274453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv22871]) (by decide +kernel)
def pv274453 : PrimeValue := ⟨274453, pr274453⟩
private theorem pr274489 : Nat.Prime 274489 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11437]) (by decide +kernel)
def pv274489 : PrimeValue := ⟨274489, pr274489⟩
private theorem pr274517 : Nat.Prime 274517 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv17,pv367]) (by decide +kernel)
def pv274517 : PrimeValue := ⟨274517, pr274517⟩
private theorem pr274529 : Nat.Prime 274529 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv373]) (by decide +kernel)
def pv274529 : PrimeValue := ⟨274529, pr274529⟩
private theorem pr274583 : Nat.Prime 274583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv11,pv1783]) (by decide +kernel)
def pv274583 : PrimeValue := ⟨274583, pr274583⟩
private theorem pr274609 : Nat.Prime 274609 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv1907]) (by decide +kernel)
def pv274609 : PrimeValue := ⟨274609, pr274609⟩
private theorem pr274627 : Nat.Prime 274627 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv11,pv19,pv73]) (by decide +kernel)
def pv274627 : PrimeValue := ⟨274627, pr274627⟩
private theorem pr274661 : Nat.Prime 274661 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv31,pv443]) (by decide +kernel)
def pv274661 : PrimeValue := ⟨274661, pr274661⟩
private theorem pr274679 : Nat.Prime 274679 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv137339]) (by decide +kernel)
def pv274679 : PrimeValue := ⟨274679, pr274679⟩
private theorem pr274711 : Nat.Prime 274711 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv9157]) (by decide +kernel)
def pv274711 : PrimeValue := ⟨274711, pr274711⟩
private theorem pr274723 : Nat.Prime 274723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv31,pv211]) (by decide +kernel)
def pv274723 : PrimeValue := ⟨274723, pr274723⟩
private theorem pr274751 : Nat.Prime 274751 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv157]) (by decide +kernel)
def pv274751 : PrimeValue := ⟨274751, pr274751⟩
private theorem pr274783 : Nat.Prime 274783 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv41,pv1117]) (by decide +kernel)
def pv274783 : PrimeValue := ⟨274783, pr274783⟩
private theorem pr274787 : Nat.Prime 274787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv137393]) (by decide +kernel)
def pv274787 : PrimeValue := ⟨274787, pr274787⟩
private theorem pr274811 : Nat.Prime 274811 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv27481]) (by decide +kernel)
def pv274811 : PrimeValue := ⟨274811, pr274811⟩
private theorem pr274831 : Nat.Prime 274831 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv9161]) (by decide +kernel)
def pv274831 : PrimeValue := ⟨274831, pr274831⟩
private theorem pr274837 : Nat.Prime 274837 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv619]) (by decide +kernel)
def pv274837 : PrimeValue := ⟨274837, pr274837⟩
private theorem pr274843 : Nat.Prime 274843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv15269]) (by decide +kernel)
def pv274843 : PrimeValue := ⟨274843, pr274843⟩
private theorem pr274853 : Nat.Prime 274853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv68713]) (by decide +kernel)
def pv274853 : PrimeValue := ⟨274853, pr274853⟩
private theorem pr274909 : Nat.Prime 274909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv739]) (by decide +kernel)
def pv274909 : PrimeValue := ⟨274909, pr274909⟩
private theorem pr274931 : Nat.Prime 274931 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19,pv1447]) (by decide +kernel)
def pv274931 : PrimeValue := ⟨274931, pr274931⟩
private theorem pr274951 : Nat.Prime 274951 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv47]) (by decide +kernel)
def pv274951 : PrimeValue := ⟨274951, pr274951⟩
private theorem pr274957 : Nat.Prime 274957 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv2083]) (by decide +kernel)
def pv274957 : PrimeValue := ⟨274957, pr274957⟩
private theorem pr274961 : Nat.Prime 274961 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv491]) (by decide +kernel)
def pv274961 : PrimeValue := ⟨274961, pr274961⟩
private theorem pr274973 : Nat.Prime 274973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv68743]) (by decide +kernel)
def pv274973 : PrimeValue := ⟨274973, pr274973⟩
private theorem pr274993 : Nat.Prime 274993 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv337]) (by decide +kernel)
def pv274993 : PrimeValue := ⟨274993, pr274993⟩
private theorem pr275003 : Nat.Prime 275003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv13,pv1511]) (by decide +kernel)
def pv275003 : PrimeValue := ⟨275003, pr275003⟩
private theorem pr275027 : Nat.Prime 275027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv8089]) (by decide +kernel)
def pv275027 : PrimeValue := ⟨275027, pr275027⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
