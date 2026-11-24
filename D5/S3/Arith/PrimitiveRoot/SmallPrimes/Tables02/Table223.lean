/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table223
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table223.pv963643
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table010
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table021
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table055
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table056

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr963643 : Nat.Prime 963643 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv79,pv107]) (by decide +kernel)
def pv963643 : PrimeValue := ⟨963643, pr963643⟩
private theorem pr963799 : Nat.Prime 963799 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv17,pv859]) (by decide +kernel)
def pv963799 : PrimeValue := ⟨963799, pr963799⟩
private theorem pr964009 : Nat.Prime 964009 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv4463]) (by decide +kernel)
def pv964009 : PrimeValue := ⟨964009, pr964009⟩
private theorem pr964027 : Nat.Prime 964027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv1093]) (by decide +kernel)
def pv964027 : PrimeValue := ⟨964027, pr964027⟩
private theorem pr964153 : Nat.Prime 964153 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv1913]) (by decide +kernel)
def pv964153 : PrimeValue := ⟨964153, pr964153⟩
private theorem pr964219 : Nat.Prime 964219 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv271,pv593]) (by decide +kernel)
def pv964219 : PrimeValue := ⟨964219, pr964219⟩
private theorem pr964357 : Nat.Prime 964357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv80363]) (by decide +kernel)
def pv964357 : PrimeValue := ⟨964357, pr964357⟩
private theorem pr964879 : Nat.Prime 964879 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv160813]) (by decide +kernel)
def pv964879 : PrimeValue := ⟨964879, pr964879⟩
private theorem pr965023 : Nat.Prime 965023 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv9461]) (by decide +kernel)
def pv965023 : PrimeValue := ⟨965023, pr965023⟩
private theorem pr965047 : Nat.Prime 965047 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv160841]) (by decide +kernel)
def pv965047 : PrimeValue := ⟨965047, pr965047⟩
private theorem pr965059 : Nat.Prime 965059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv41,pv3923]) (by decide +kernel)
def pv965059 : PrimeValue := ⟨965059, pr965059⟩
private theorem pr965089 : Nat.Prime 965089 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv1117]) (by decide +kernel)
def pv965089 : PrimeValue := ⟨965089, pr965089⟩
private theorem pr965317 : Nat.Prime 965317 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv11,pv71,pv103]) (by decide +kernel)
def pv965317 : PrimeValue := ⟨965317, pr965317⟩
private theorem pr965329 : Nat.Prime 965329 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv13,pv17]) (by decide +kernel)
def pv965329 : PrimeValue := ⟨965329, pr965329⟩
private theorem pr965623 : Nat.Prime 965623 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv83,pv277]) (by decide +kernel)
def pv965623 : PrimeValue := ⟨965623, pr965623⟩
private theorem pr965647 : Nat.Prime 965647 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv4877]) (by decide +kernel)
def pv965647 : PrimeValue := ⟨965647, pr965647⟩
private theorem pr965677 : Nat.Prime 965677 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv80473]) (by decide +kernel)
def pv965677 : PrimeValue := ⟨965677, pr965677⟩
private theorem pr965749 : Nat.Prime 965749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv11497]) (by decide +kernel)
def pv965749 : PrimeValue := ⟨965749, pr965749⟩
private theorem pr966139 : Nat.Prime 966139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv7001]) (by decide +kernel)
def pv966139 : PrimeValue := ⟨966139, pr966139⟩
private theorem pr966157 : Nat.Prime 966157 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv80513]) (by decide +kernel)
def pv966157 : PrimeValue := ⟨966157, pr966157⟩
private theorem pr966307 : Nat.Prime 966307 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv966307 : PrimeValue := ⟨966307, pr966307⟩
private theorem pr966337 : Nat.Prime 966337 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv719]) (by decide +kernel)
def pv966337 : PrimeValue := ⟨966337, pr966337⟩
private theorem pr966379 : Nat.Prime 966379 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv19,pv173]) (by decide +kernel)
def pv966379 : PrimeValue := ⟨966379, pr966379⟩
private theorem pr966409 : Nat.Prime 966409 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv67,pv601]) (by decide +kernel)
def pv966409 : PrimeValue := ⟨966409, pr966409⟩
private theorem pr966463 : Nat.Prime 966463 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv23011]) (by decide +kernel)
def pv966463 : PrimeValue := ⟨966463, pr966463⟩
private theorem pr966583 : Nat.Prime 966583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv53699]) (by decide +kernel)
def pv966583 : PrimeValue := ⟨966583, pr966583⟩
private theorem pr966613 : Nat.Prime 966613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv109,pv739]) (by decide +kernel)
def pv966613 : PrimeValue := ⟨966613, pr966613⟩
private theorem pr966883 : Nat.Prime 966883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv23021]) (by decide +kernel)
def pv966883 : PrimeValue := ⟨966883, pr966883⟩
private theorem pr966907 : Nat.Prime 966907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv53717]) (by decide +kernel)
def pv966907 : PrimeValue := ⟨966907, pr966907⟩
private theorem pr967003 : Nat.Prime 967003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv161167]) (by decide +kernel)
def pv967003 : PrimeValue := ⟨967003, pr967003⟩
private theorem pr967129 : Nat.Prime 967129 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv59,pv683]) (by decide +kernel)
def pv967129 : PrimeValue := ⟨967129, pr967129⟩
private theorem pr967297 : Nat.Prime 967297 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv229]) (by decide +kernel)
def pv967297 : PrimeValue := ⟨967297, pr967297⟩
private theorem pr967663 : Nat.Prime 967663 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv53759]) (by decide +kernel)
def pv967663 : PrimeValue := ⟨967663, pr967663⟩
private theorem pr967693 : Nat.Prime 967693 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv7331]) (by decide +kernel)
def pv967693 : PrimeValue := ⟨967693, pr967693⟩
private theorem pr967753 : Nat.Prime 967753 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13441]) (by decide +kernel)
def pv967753 : PrimeValue := ⟨967753, pr967753⟩
private theorem pr968353 : Nat.Prime 968353 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv7,pv11,pv131]) (by decide +kernel)
def pv968353 : PrimeValue := ⟨968353, pr968353⟩
private theorem pr968377 : Nat.Prime 968377 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv157,pv257]) (by decide +kernel)
def pv968377 : PrimeValue := ⟨968377, pr968377⟩
private theorem pr968419 : Nat.Prime 968419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv67,pv73]) (by decide +kernel)
def pv968419 : PrimeValue := ⟨968419, pr968419⟩
private theorem pr968557 : Nat.Prime 968557 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv80713]) (by decide +kernel)
def pv968557 : PrimeValue := ⟨968557, pr968557⟩
private theorem pr968713 : Nat.Prime 968713 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv181,pv223]) (by decide +kernel)
def pv968713 : PrimeValue := ⟨968713, pr968713⟩
private theorem pr968827 : Nat.Prime 968827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv161471]) (by decide +kernel)
def pv968827 : PrimeValue := ⟨968827, pr968827⟩
private theorem pr968857 : Nat.Prime 968857 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv73,pv79]) (by decide +kernel)
def pv968857 : PrimeValue := ⟨968857, pr968857⟩
private theorem pr969139 : Nat.Prime 969139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv131,pv137]) (by decide +kernel)
def pv969139 : PrimeValue := ⟨969139, pr969139⟩
private theorem pr969343 : Nat.Prime 969343 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv19,pv773]) (by decide +kernel)
def pv969343 : PrimeValue := ⟨969343, pr969343⟩
private theorem pr969403 : Nat.Prime 969403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv23081]) (by decide +kernel)
def pv969403 : PrimeValue := ⟨969403, pr969403⟩
private theorem pr969433 : Nat.Prime 969433 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv31,pv1303]) (by decide +kernel)
def pv969433 : PrimeValue := ⟨969433, pr969433⟩
private theorem pr969637 : Nat.Prime 969637 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv80803]) (by decide +kernel)
def pv969637 : PrimeValue := ⟨969637, pr969637⟩
private theorem pr969877 : Nat.Prime 969877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv929]) (by decide +kernel)
def pv969877 : PrimeValue := ⟨969877, pr969877⟩
private theorem pr970147 : Nat.Prime 970147 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv53897]) (by decide +kernel)
def pv970147 : PrimeValue := ⟨970147, pr970147⟩
private theorem pr970213 : Nat.Prime 970213 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv233,pv347]) (by decide +kernel)
def pv970213 : PrimeValue := ⟨970213, pr970213⟩
private theorem pr970237 : Nat.Prime 970237 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv26951]) (by decide +kernel)
def pv970237 : PrimeValue := ⟨970237, pr970237⟩
private theorem pr970267 : Nat.Prime 970267 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv61,pv241]) (by decide +kernel)
def pv970267 : PrimeValue := ⟨970267, pr970267⟩
private theorem pr970537 : Nat.Prime 970537 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv53,pv109]) (by decide +kernel)
def pv970537 : PrimeValue := ⟨970537, pr970537⟩
private theorem pr970777 : Nat.Prime 970777 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv97,pv139]) (by decide +kernel)
def pv970777 : PrimeValue := ⟨970777, pr970777⟩
private theorem pr970909 : Nat.Prime 970909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv80909]) (by decide +kernel)
def pv970909 : PrimeValue := ⟨970909, pr970909⟩
private theorem pr971029 : Nat.Prime 971029 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv37]) (by decide +kernel)
def pv971029 : PrimeValue := ⟨971029, pr971029⟩
private theorem pr971053 : Nat.Prime 971053 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv19,pv4259]) (by decide +kernel)
def pv971053 : PrimeValue := ⟨971053, pr971053⟩
private theorem pr971419 : Nat.Prime 971419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv101,pv229]) (by decide +kernel)
def pv971419 : PrimeValue := ⟨971419, pr971419⟩
private theorem pr971683 : Nat.Prime 971683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv161947]) (by decide +kernel)
def pv971683 : PrimeValue := ⟨971683, pr971683⟩
private theorem pr971863 : Nat.Prime 971863 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv161977]) (by decide +kernel)
def pv971863 : PrimeValue := ⟨971863, pr971863⟩
private theorem pr972163 : Nat.Prime 972163 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv353]) (by decide +kernel)
def pv972163 : PrimeValue := ⟨972163, pr972163⟩
private theorem pr972229 : Nat.Prime 972229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv81019]) (by decide +kernel)
def pv972229 : PrimeValue := ⟨972229, pr972229⟩
private theorem pr972259 : Nat.Prime 972259 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv3307]) (by decide +kernel)
def pv972259 : PrimeValue := ⟨972259, pr972259⟩
private theorem pr972313 : Nat.Prime 972313 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv29,pv127]) (by decide +kernel)
def pv972313 : PrimeValue := ⟨972313, pr972313⟩
private theorem pr972337 : Nat.Prime 972337 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv47,pv431]) (by decide +kernel)
def pv972337 : PrimeValue := ⟨972337, pr972337⟩
private theorem pr972343 : Nat.Prime 972343 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv7717]) (by decide +kernel)
def pv972343 : PrimeValue := ⟨972343, pr972343⟩
private theorem pr972373 : Nat.Prime 972373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv81031]) (by decide +kernel)
def pv972373 : PrimeValue := ⟨972373, pr972373⟩
private theorem pr972577 : Nat.Prime 972577 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv307]) (by decide +kernel)
def pv972577 : PrimeValue := ⟨972577, pr972577⟩
private theorem pr972799 : Nat.Prime 972799 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv73,pv2221]) (by decide +kernel)
def pv972799 : PrimeValue := ⟨972799, pr972799⟩
private theorem pr972847 : Nat.Prime 972847 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv1103]) (by decide +kernel)
def pv972847 : PrimeValue := ⟨972847, pr972847⟩
private theorem pr972943 : Nat.Prime 972943 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv167,pv971]) (by decide +kernel)
def pv972943 : PrimeValue := ⟨972943, pr972943⟩
private theorem pr972967 : Nat.Prime 972967 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv31,pv5231]) (by decide +kernel)
def pv972967 : PrimeValue := ⟨972967, pr972967⟩
private theorem pr973759 : Nat.Prime 973759 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv162293]) (by decide +kernel)
def pv973759 : PrimeValue := ⟨973759, pr973759⟩
private theorem pr974089 : Nat.Prime 974089 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv83,pv163]) (by decide +kernel)
def pv974089 : PrimeValue := ⟨974089, pr974089⟩
private theorem pr974143 : Nat.Prime 974143 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv23,pv181]) (by decide +kernel)
def pv974143 : PrimeValue := ⟨974143, pr974143⟩
private theorem pr974317 : Nat.Prime 974317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv1657]) (by decide +kernel)
def pv974317 : PrimeValue := ⟨974317, pr974317⟩
private theorem pr974437 : Nat.Prime 974437 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv81203]) (by decide +kernel)
def pv974437 : PrimeValue := ⟨974437, pr974437⟩
private theorem pr974863 : Nat.Prime 974863 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv2579]) (by decide +kernel)
def pv974863 : PrimeValue := ⟨974863, pr974863⟩
private theorem pr974887 : Nat.Prime 974887 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv14771]) (by decide +kernel)
def pv974887 : PrimeValue := ⟨974887, pr974887⟩
private theorem pr974989 : Nat.Prime 974989 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv53,pv73]) (by decide +kernel)
def pv974989 : PrimeValue := ⟨974989, pr974989⟩
private theorem pr975187 : Nat.Prime 975187 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv18059]) (by decide +kernel)
def pv975187 : PrimeValue := ⟨975187, pr975187⟩
private theorem pr975439 : Nat.Prime 975439 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv47,pv1153]) (by decide +kernel)
def pv975439 : PrimeValue := ⟨975439, pr975439⟩
private theorem pr975463 : Nat.Prime 975463 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv162577]) (by decide +kernel)
def pv975463 : PrimeValue := ⟨975463, pr975463⟩
private theorem pr975619 : Nat.Prime 975619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv29,pv89]) (by decide +kernel)
def pv975619 : PrimeValue := ⟨975619, pr975619⟩
private theorem pr975643 : Nat.Prime 975643 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv113,pv1439]) (by decide +kernel)
def pv975643 : PrimeValue := ⟨975643, pr975643⟩
private theorem pr975823 : Nat.Prime 975823 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv103,pv1579]) (by decide +kernel)
def pv975823 : PrimeValue := ⟨975823, pr975823⟩
private theorem pr975883 : Nat.Prime 975883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv41,pv3967]) (by decide +kernel)
def pv975883 : PrimeValue := ⟨975883, pr975883⟩
private theorem pr976117 : Nat.Prime 976117 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv81343]) (by decide +kernel)
def pv976117 : PrimeValue := ⟨976117, pr976117⟩
private theorem pr976369 : Nat.Prime 976369 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv20341]) (by decide +kernel)
def pv976369 : PrimeValue := ⟨976369, pr976369⟩
private theorem pr976447 : Nat.Prime 976447 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv3191]) (by decide +kernel)
def pv976447 : PrimeValue := ⟨976447, pr976447⟩
private theorem pr976483 : Nat.Prime 976483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv107]) (by decide +kernel)
def pv976483 : PrimeValue := ⟨976483, pr976483⟩
private theorem pr976639 : Nat.Prime 976639 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv13,pv19,pv659]) (by decide +kernel)
def pv976639 : PrimeValue := ⟨976639, pr976639⟩
private theorem pr976699 : Nat.Prime 976699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv6029]) (by decide +kernel)
def pv976699 : PrimeValue := ⟨976699, pr976699⟩
private theorem pr976933 : Nat.Prime 976933 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv11,pv2467]) (by decide +kernel)
def pv976933 : PrimeValue := ⟨976933, pr976933⟩
private theorem pr977209 : Nat.Prime 977209 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv19,pv2143]) (by decide +kernel)
def pv977209 : PrimeValue := ⟨977209, pr977209⟩
private theorem pr977323 : Nat.Prime 977323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv8573]) (by decide +kernel)
def pv977323 : PrimeValue := ⟨977323, pr977323⟩
private theorem pr977437 : Nat.Prime 977437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv1429]) (by decide +kernel)
def pv977437 : PrimeValue := ⟨977437, pr977437⟩
private theorem pr977923 : Nat.Prime 977923 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv449]) (by decide +kernel)
def pv977923 : PrimeValue := ⟨977923, pr977923⟩
private theorem pr978223 : Nat.Prime 978223 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv23291]) (by decide +kernel)
def pv978223 : PrimeValue := ⟨978223, pr978223⟩
private theorem pr978277 : Nat.Prime 978277 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv6271]) (by decide +kernel)
def pv978277 : PrimeValue := ⟨978277, pr978277⟩
private theorem pr978349 : Nat.Prime 978349 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv19,pv613]) (by decide +kernel)
def pv978349 : PrimeValue := ⟨978349, pr978349⟩
private theorem pr978883 : Nat.Prime 978883 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv163147]) (by decide +kernel)
def pv978883 : PrimeValue := ⟨978883, pr978883⟩
private theorem pr978907 : Nat.Prime 978907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv163151]) (by decide +kernel)
def pv978907 : PrimeValue := ⟨978907, pr978907⟩
private theorem pr978973 : Nat.Prime 978973 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv23,pv3547]) (by decide +kernel)
def pv978973 : PrimeValue := ⟨978973, pr978973⟩
private theorem pr979009 : Nat.Prime 979009 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5099]) (by decide +kernel)
def pv979009 : PrimeValue := ⟨979009, pr979009⟩
private theorem pr979093 : Nat.Prime 979093 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv27197]) (by decide +kernel)
def pv979093 : PrimeValue := ⟨979093, pr979093⟩
private theorem pr979117 : Nat.Prime 979117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv139,pv587]) (by decide +kernel)
def pv979117 : PrimeValue := ⟨979117, pr979117⟩
private theorem pr979159 : Nat.Prime 979159 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv163193]) (by decide +kernel)
def pv979159 : PrimeValue := ⟨979159, pr979159⟩
private theorem pr979273 : Nat.Prime 979273 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv29,pv67]) (by decide +kernel)
def pv979273 : PrimeValue := ⟨979273, pr979273⟩
private theorem pr979549 : Nat.Prime 979549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv81629]) (by decide +kernel)
def pv979549 : PrimeValue := ⟨979549, pr979549⟩
private theorem pr979567 : Nat.Prime 979567 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv83,pv281]) (by decide +kernel)
def pv979567 : PrimeValue := ⟨979567, pr979567⟩
private theorem pr979717 : Nat.Prime 979717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv4297]) (by decide +kernel)
def pv979717 : PrimeValue := ⟨979717, pr979717⟩
private theorem pr979807 : Nat.Prime 979807 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv73,pv2237]) (by decide +kernel)
def pv979807 : PrimeValue := ⟨979807, pr979807⟩
private theorem pr979819 : Nat.Prime 979819 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv41,pv569]) (by decide +kernel)
def pv979819 : PrimeValue := ⟨979819, pr979819⟩
private theorem pr980107 : Nat.Prime 980107 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv163351]) (by decide +kernel)
def pv980107 : PrimeValue := ⟨980107, pr980107⟩
private theorem pr980293 : Nat.Prime 980293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv151,pv541]) (by decide +kernel)
def pv980293 : PrimeValue := ⟨980293, pr980293⟩
private theorem pr980503 : Nat.Prime 980503 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv163417]) (by decide +kernel)
def pv980503 : PrimeValue := ⟨980503, pr980503⟩
private theorem pr980587 : Nat.Prime 980587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv6053]) (by decide +kernel)
def pv980587 : PrimeValue := ⟨980587, pr980587⟩
private theorem pr981073 : Nat.Prime 981073 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv757]) (by decide +kernel)
def pv981073 : PrimeValue := ⟨981073, pr981073⟩
private theorem pr981133 : Nat.Prime 981133 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv81761]) (by decide +kernel)
def pv981133 : PrimeValue := ⟨981133, pr981133⟩
private theorem pr981199 : Nat.Prime 981199 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv151]) (by decide +kernel)
def pv981199 : PrimeValue := ⟨981199, pr981199⟩
private theorem pr981283 : Nat.Prime 981283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv67,pv2441]) (by decide +kernel)
def pv981283 : PrimeValue := ⟨981283, pr981283⟩
private theorem pr981319 : Nat.Prime 981319 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv13,pv23,pv547]) (by decide +kernel)
def pv981319 : PrimeValue := ⟨981319, pr981319⟩
private theorem pr981493 : Nat.Prime 981493 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv89,pv919]) (by decide +kernel)
def pv981493 : PrimeValue := ⟨981493, pr981493⟩
private theorem pr981523 : Nat.Prime 981523 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv31,pv1759]) (by decide +kernel)
def pv981523 : PrimeValue := ⟨981523, pr981523⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
