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
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr963643 : PrimeCertificate 963643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv79,pv107]) (by decide +kernel)
def pv963643 : PrimeValue := ⟨963643, pr963643⟩
private theorem pr963799 : PrimeCertificate 963799 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv17,pv859]) (by decide +kernel)
def pv963799 : PrimeValue := ⟨963799, pr963799⟩
private theorem pr964009 : PrimeCertificate 964009 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv4463]) (by decide +kernel)
def pv964009 : PrimeValue := ⟨964009, pr964009⟩
private theorem pr964027 : PrimeCertificate 964027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1093]) (by decide +kernel)
def pv964027 : PrimeValue := ⟨964027, pr964027⟩
private theorem pr964153 : PrimeCertificate 964153 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv1913]) (by decide +kernel)
def pv964153 : PrimeValue := ⟨964153, pr964153⟩
private theorem pr964219 : PrimeCertificate 964219 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv271,pv593]) (by decide +kernel)
def pv964219 : PrimeValue := ⟨964219, pr964219⟩
private theorem pr964357 : PrimeCertificate 964357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv80363]) (by decide +kernel)
def pv964357 : PrimeValue := ⟨964357, pr964357⟩
private theorem pr964879 : PrimeCertificate 964879 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv160813]) (by decide +kernel)
def pv964879 : PrimeValue := ⟨964879, pr964879⟩
private theorem pr965023 : PrimeCertificate 965023 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv9461]) (by decide +kernel)
def pv965023 : PrimeValue := ⟨965023, pr965023⟩
private theorem pr965047 : PrimeCertificate 965047 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv160841]) (by decide +kernel)
def pv965047 : PrimeValue := ⟨965047, pr965047⟩
private theorem pr965059 : PrimeCertificate 965059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv3923]) (by decide +kernel)
def pv965059 : PrimeValue := ⟨965059, pr965059⟩
private theorem pr965089 : PrimeCertificate 965089 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv1117]) (by decide +kernel)
def pv965089 : PrimeValue := ⟨965089, pr965089⟩
private theorem pr965317 : PrimeCertificate 965317 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv71,pv103]) (by decide +kernel)
def pv965317 : PrimeValue := ⟨965317, pr965317⟩
private theorem pr965329 : PrimeCertificate 965329 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv13,pv17]) (by decide +kernel)
def pv965329 : PrimeValue := ⟨965329, pr965329⟩
private theorem pr965623 : PrimeCertificate 965623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv83,pv277]) (by decide +kernel)
def pv965623 : PrimeValue := ⟨965623, pr965623⟩
private theorem pr965647 : PrimeCertificate 965647 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv4877]) (by decide +kernel)
def pv965647 : PrimeValue := ⟨965647, pr965647⟩
private theorem pr965677 : PrimeCertificate 965677 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv80473]) (by decide +kernel)
def pv965677 : PrimeValue := ⟨965677, pr965677⟩
private theorem pr965749 : PrimeCertificate 965749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11497]) (by decide +kernel)
def pv965749 : PrimeValue := ⟨965749, pr965749⟩
private theorem pr966139 : PrimeCertificate 966139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv7001]) (by decide +kernel)
def pv966139 : PrimeValue := ⟨966139, pr966139⟩
private theorem pr966157 : PrimeCertificate 966157 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv80513]) (by decide +kernel)
def pv966157 : PrimeValue := ⟨966157, pr966157⟩
private theorem pr966307 : PrimeCertificate 966307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv966307 : PrimeValue := ⟨966307, pr966307⟩
private theorem pr966337 : PrimeCertificate 966337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv719]) (by decide +kernel)
def pv966337 : PrimeValue := ⟨966337, pr966337⟩
private theorem pr966379 : PrimeCertificate 966379 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv19,pv173]) (by decide +kernel)
def pv966379 : PrimeValue := ⟨966379, pr966379⟩
private theorem pr966409 : PrimeCertificate 966409 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv67,pv601]) (by decide +kernel)
def pv966409 : PrimeValue := ⟨966409, pr966409⟩
private theorem pr966463 : PrimeCertificate 966463 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv23011]) (by decide +kernel)
def pv966463 : PrimeValue := ⟨966463, pr966463⟩
private theorem pr966583 : PrimeCertificate 966583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv53699]) (by decide +kernel)
def pv966583 : PrimeValue := ⟨966583, pr966583⟩
private theorem pr966613 : PrimeCertificate 966613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv109,pv739]) (by decide +kernel)
def pv966613 : PrimeValue := ⟨966613, pr966613⟩
private theorem pr966883 : PrimeCertificate 966883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv23021]) (by decide +kernel)
def pv966883 : PrimeValue := ⟨966883, pr966883⟩
private theorem pr966907 : PrimeCertificate 966907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53717]) (by decide +kernel)
def pv966907 : PrimeValue := ⟨966907, pr966907⟩
private theorem pr967003 : PrimeCertificate 967003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv161167]) (by decide +kernel)
def pv967003 : PrimeValue := ⟨967003, pr967003⟩
private theorem pr967129 : PrimeCertificate 967129 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv59,pv683]) (by decide +kernel)
def pv967129 : PrimeValue := ⟨967129, pr967129⟩
private theorem pr967297 : PrimeCertificate 967297 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv229]) (by decide +kernel)
def pv967297 : PrimeValue := ⟨967297, pr967297⟩
private theorem pr967663 : PrimeCertificate 967663 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv53759]) (by decide +kernel)
def pv967663 : PrimeValue := ⟨967663, pr967663⟩
private theorem pr967693 : PrimeCertificate 967693 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv7331]) (by decide +kernel)
def pv967693 : PrimeValue := ⟨967693, pr967693⟩
private theorem pr967753 : PrimeCertificate 967753 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13441]) (by decide +kernel)
def pv967753 : PrimeValue := ⟨967753, pr967753⟩
private theorem pr968353 : PrimeCertificate 968353 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv11,pv131]) (by decide +kernel)
def pv968353 : PrimeValue := ⟨968353, pr968353⟩
private theorem pr968377 : PrimeCertificate 968377 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv157,pv257]) (by decide +kernel)
def pv968377 : PrimeValue := ⟨968377, pr968377⟩
private theorem pr968419 : PrimeCertificate 968419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv67,pv73]) (by decide +kernel)
def pv968419 : PrimeValue := ⟨968419, pr968419⟩
private theorem pr968557 : PrimeCertificate 968557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv80713]) (by decide +kernel)
def pv968557 : PrimeValue := ⟨968557, pr968557⟩
private theorem pr968713 : PrimeCertificate 968713 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv181,pv223]) (by decide +kernel)
def pv968713 : PrimeValue := ⟨968713, pr968713⟩
private theorem pr968827 : PrimeCertificate 968827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv161471]) (by decide +kernel)
def pv968827 : PrimeValue := ⟨968827, pr968827⟩
private theorem pr968857 : PrimeCertificate 968857 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv73,pv79]) (by decide +kernel)
def pv968857 : PrimeValue := ⟨968857, pr968857⟩
private theorem pr969139 : PrimeCertificate 969139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv131,pv137]) (by decide +kernel)
def pv969139 : PrimeValue := ⟨969139, pr969139⟩
private theorem pr969343 : PrimeCertificate 969343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv19,pv773]) (by decide +kernel)
def pv969343 : PrimeValue := ⟨969343, pr969343⟩
private theorem pr969403 : PrimeCertificate 969403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv23081]) (by decide +kernel)
def pv969403 : PrimeValue := ⟨969403, pr969403⟩
private theorem pr969433 : PrimeCertificate 969433 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv1303]) (by decide +kernel)
def pv969433 : PrimeValue := ⟨969433, pr969433⟩
private theorem pr969637 : PrimeCertificate 969637 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv80803]) (by decide +kernel)
def pv969637 : PrimeValue := ⟨969637, pr969637⟩
private theorem pr969877 : PrimeCertificate 969877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv929]) (by decide +kernel)
def pv969877 : PrimeValue := ⟨969877, pr969877⟩
private theorem pr970147 : PrimeCertificate 970147 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv53897]) (by decide +kernel)
def pv970147 : PrimeValue := ⟨970147, pr970147⟩
private theorem pr970213 : PrimeCertificate 970213 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv233,pv347]) (by decide +kernel)
def pv970213 : PrimeValue := ⟨970213, pr970213⟩
private theorem pr970237 : PrimeCertificate 970237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv26951]) (by decide +kernel)
def pv970237 : PrimeValue := ⟨970237, pr970237⟩
private theorem pr970267 : PrimeCertificate 970267 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv61,pv241]) (by decide +kernel)
def pv970267 : PrimeValue := ⟨970267, pr970267⟩
private theorem pr970537 : PrimeCertificate 970537 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv53,pv109]) (by decide +kernel)
def pv970537 : PrimeValue := ⟨970537, pr970537⟩
private theorem pr970777 : PrimeCertificate 970777 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv97,pv139]) (by decide +kernel)
def pv970777 : PrimeValue := ⟨970777, pr970777⟩
private theorem pr970909 : PrimeCertificate 970909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv80909]) (by decide +kernel)
def pv970909 : PrimeValue := ⟨970909, pr970909⟩
private theorem pr971029 : PrimeCertificate 971029 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv37]) (by decide +kernel)
def pv971029 : PrimeValue := ⟨971029, pr971029⟩
private theorem pr971053 : PrimeCertificate 971053 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv19,pv4259]) (by decide +kernel)
def pv971053 : PrimeValue := ⟨971053, pr971053⟩
private theorem pr971419 : PrimeCertificate 971419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv101,pv229]) (by decide +kernel)
def pv971419 : PrimeValue := ⟨971419, pr971419⟩
private theorem pr971683 : PrimeCertificate 971683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv161947]) (by decide +kernel)
def pv971683 : PrimeValue := ⟨971683, pr971683⟩
private theorem pr971863 : PrimeCertificate 971863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv161977]) (by decide +kernel)
def pv971863 : PrimeValue := ⟨971863, pr971863⟩
private theorem pr972163 : PrimeCertificate 972163 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv353]) (by decide +kernel)
def pv972163 : PrimeValue := ⟨972163, pr972163⟩
private theorem pr972229 : PrimeCertificate 972229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv81019]) (by decide +kernel)
def pv972229 : PrimeValue := ⟨972229, pr972229⟩
private theorem pr972259 : PrimeCertificate 972259 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv3307]) (by decide +kernel)
def pv972259 : PrimeValue := ⟨972259, pr972259⟩
private theorem pr972313 : PrimeCertificate 972313 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv29,pv127]) (by decide +kernel)
def pv972313 : PrimeValue := ⟨972313, pr972313⟩
private theorem pr972337 : PrimeCertificate 972337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv47,pv431]) (by decide +kernel)
def pv972337 : PrimeValue := ⟨972337, pr972337⟩
private theorem pr972343 : PrimeCertificate 972343 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv7717]) (by decide +kernel)
def pv972343 : PrimeValue := ⟨972343, pr972343⟩
private theorem pr972373 : PrimeCertificate 972373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv81031]) (by decide +kernel)
def pv972373 : PrimeValue := ⟨972373, pr972373⟩
private theorem pr972577 : PrimeCertificate 972577 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv307]) (by decide +kernel)
def pv972577 : PrimeValue := ⟨972577, pr972577⟩
private theorem pr972799 : PrimeCertificate 972799 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv73,pv2221]) (by decide +kernel)
def pv972799 : PrimeValue := ⟨972799, pr972799⟩
private theorem pr972847 : PrimeCertificate 972847 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv1103]) (by decide +kernel)
def pv972847 : PrimeValue := ⟨972847, pr972847⟩
private theorem pr972943 : PrimeCertificate 972943 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv167,pv971]) (by decide +kernel)
def pv972943 : PrimeValue := ⟨972943, pr972943⟩
private theorem pr972967 : PrimeCertificate 972967 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31,pv5231]) (by decide +kernel)
def pv972967 : PrimeValue := ⟨972967, pr972967⟩
private theorem pr973759 : PrimeCertificate 973759 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv162293]) (by decide +kernel)
def pv973759 : PrimeValue := ⟨973759, pr973759⟩
private theorem pr974089 : PrimeCertificate 974089 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv83,pv163]) (by decide +kernel)
def pv974089 : PrimeValue := ⟨974089, pr974089⟩
private theorem pr974143 : PrimeCertificate 974143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv23,pv181]) (by decide +kernel)
def pv974143 : PrimeValue := ⟨974143, pr974143⟩
private theorem pr974317 : PrimeCertificate 974317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1657]) (by decide +kernel)
def pv974317 : PrimeValue := ⟨974317, pr974317⟩
private theorem pr974437 : PrimeCertificate 974437 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv81203]) (by decide +kernel)
def pv974437 : PrimeValue := ⟨974437, pr974437⟩
private theorem pr974863 : PrimeCertificate 974863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv2579]) (by decide +kernel)
def pv974863 : PrimeValue := ⟨974863, pr974863⟩
private theorem pr974887 : PrimeCertificate 974887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv14771]) (by decide +kernel)
def pv974887 : PrimeValue := ⟨974887, pr974887⟩
private theorem pr974989 : PrimeCertificate 974989 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv53,pv73]) (by decide +kernel)
def pv974989 : PrimeValue := ⟨974989, pr974989⟩
private theorem pr975187 : PrimeCertificate 975187 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv18059]) (by decide +kernel)
def pv975187 : PrimeValue := ⟨975187, pr975187⟩
private theorem pr975439 : PrimeCertificate 975439 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv47,pv1153]) (by decide +kernel)
def pv975439 : PrimeValue := ⟨975439, pr975439⟩
private theorem pr975463 : PrimeCertificate 975463 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv162577]) (by decide +kernel)
def pv975463 : PrimeValue := ⟨975463, pr975463⟩
private theorem pr975619 : PrimeCertificate 975619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv29,pv89]) (by decide +kernel)
def pv975619 : PrimeValue := ⟨975619, pr975619⟩
private theorem pr975643 : PrimeCertificate 975643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv113,pv1439]) (by decide +kernel)
def pv975643 : PrimeValue := ⟨975643, pr975643⟩
private theorem pr975823 : PrimeCertificate 975823 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv103,pv1579]) (by decide +kernel)
def pv975823 : PrimeValue := ⟨975823, pr975823⟩
private theorem pr975883 : PrimeCertificate 975883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv3967]) (by decide +kernel)
def pv975883 : PrimeValue := ⟨975883, pr975883⟩
private theorem pr976117 : PrimeCertificate 976117 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv81343]) (by decide +kernel)
def pv976117 : PrimeValue := ⟨976117, pr976117⟩
private theorem pr976369 : PrimeCertificate 976369 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv20341]) (by decide +kernel)
def pv976369 : PrimeValue := ⟨976369, pr976369⟩
private theorem pr976447 : PrimeCertificate 976447 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv3191]) (by decide +kernel)
def pv976447 : PrimeValue := ⟨976447, pr976447⟩
private theorem pr976483 : PrimeCertificate 976483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv107]) (by decide +kernel)
def pv976483 : PrimeValue := ⟨976483, pr976483⟩
private theorem pr976639 : PrimeCertificate 976639 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv13,pv19,pv659]) (by decide +kernel)
def pv976639 : PrimeValue := ⟨976639, pr976639⟩
private theorem pr976699 : PrimeCertificate 976699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv6029]) (by decide +kernel)
def pv976699 : PrimeValue := ⟨976699, pr976699⟩
private theorem pr976933 : PrimeCertificate 976933 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv11,pv2467]) (by decide +kernel)
def pv976933 : PrimeValue := ⟨976933, pr976933⟩
private theorem pr977209 : PrimeCertificate 977209 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv19,pv2143]) (by decide +kernel)
def pv977209 : PrimeValue := ⟨977209, pr977209⟩
private theorem pr977323 : PrimeCertificate 977323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv8573]) (by decide +kernel)
def pv977323 : PrimeValue := ⟨977323, pr977323⟩
private theorem pr977437 : PrimeCertificate 977437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv1429]) (by decide +kernel)
def pv977437 : PrimeValue := ⟨977437, pr977437⟩
private theorem pr977923 : PrimeCertificate 977923 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv449]) (by decide +kernel)
def pv977923 : PrimeValue := ⟨977923, pr977923⟩
private theorem pr978223 : PrimeCertificate 978223 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv23291]) (by decide +kernel)
def pv978223 : PrimeValue := ⟨978223, pr978223⟩
private theorem pr978277 : PrimeCertificate 978277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv6271]) (by decide +kernel)
def pv978277 : PrimeValue := ⟨978277, pr978277⟩
private theorem pr978349 : PrimeCertificate 978349 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv19,pv613]) (by decide +kernel)
def pv978349 : PrimeValue := ⟨978349, pr978349⟩
private theorem pr978883 : PrimeCertificate 978883 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv163147]) (by decide +kernel)
def pv978883 : PrimeValue := ⟨978883, pr978883⟩
private theorem pr978907 : PrimeCertificate 978907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv163151]) (by decide +kernel)
def pv978907 : PrimeValue := ⟨978907, pr978907⟩
private theorem pr978973 : PrimeCertificate 978973 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv23,pv3547]) (by decide +kernel)
def pv978973 : PrimeValue := ⟨978973, pr978973⟩
private theorem pr979009 : PrimeCertificate 979009 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5099]) (by decide +kernel)
def pv979009 : PrimeValue := ⟨979009, pr979009⟩
private theorem pr979093 : PrimeCertificate 979093 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv27197]) (by decide +kernel)
def pv979093 : PrimeValue := ⟨979093, pr979093⟩
private theorem pr979117 : PrimeCertificate 979117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv139,pv587]) (by decide +kernel)
def pv979117 : PrimeValue := ⟨979117, pr979117⟩
private theorem pr979159 : PrimeCertificate 979159 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv163193]) (by decide +kernel)
def pv979159 : PrimeValue := ⟨979159, pr979159⟩
private theorem pr979273 : PrimeCertificate 979273 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv29,pv67]) (by decide +kernel)
def pv979273 : PrimeValue := ⟨979273, pr979273⟩
private theorem pr979549 : PrimeCertificate 979549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv81629]) (by decide +kernel)
def pv979549 : PrimeValue := ⟨979549, pr979549⟩
private theorem pr979567 : PrimeCertificate 979567 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv83,pv281]) (by decide +kernel)
def pv979567 : PrimeValue := ⟨979567, pr979567⟩
private theorem pr979717 : PrimeCertificate 979717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv4297]) (by decide +kernel)
def pv979717 : PrimeValue := ⟨979717, pr979717⟩
private theorem pr979807 : PrimeCertificate 979807 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv73,pv2237]) (by decide +kernel)
def pv979807 : PrimeValue := ⟨979807, pr979807⟩
private theorem pr979819 : PrimeCertificate 979819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv41,pv569]) (by decide +kernel)
def pv979819 : PrimeValue := ⟨979819, pr979819⟩
private theorem pr980107 : PrimeCertificate 980107 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv163351]) (by decide +kernel)
def pv980107 : PrimeValue := ⟨980107, pr980107⟩
private theorem pr980293 : PrimeCertificate 980293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv151,pv541]) (by decide +kernel)
def pv980293 : PrimeValue := ⟨980293, pr980293⟩
private theorem pr980503 : PrimeCertificate 980503 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv163417]) (by decide +kernel)
def pv980503 : PrimeValue := ⟨980503, pr980503⟩
private theorem pr980587 : PrimeCertificate 980587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv6053]) (by decide +kernel)
def pv980587 : PrimeValue := ⟨980587, pr980587⟩
private theorem pr981073 : PrimeCertificate 981073 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv757]) (by decide +kernel)
def pv981073 : PrimeValue := ⟨981073, pr981073⟩
private theorem pr981133 : PrimeCertificate 981133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv81761]) (by decide +kernel)
def pv981133 : PrimeValue := ⟨981133, pr981133⟩
private theorem pr981199 : PrimeCertificate 981199 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv151]) (by decide +kernel)
def pv981199 : PrimeValue := ⟨981199, pr981199⟩
private theorem pr981283 : PrimeCertificate 981283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv67,pv2441]) (by decide +kernel)
def pv981283 : PrimeValue := ⟨981283, pr981283⟩
private theorem pr981319 : PrimeCertificate 981319 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13,pv23,pv547]) (by decide +kernel)
def pv981319 : PrimeValue := ⟨981319, pr981319⟩
private theorem pr981493 : PrimeCertificate 981493 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv89,pv919]) (by decide +kernel)
def pv981493 : PrimeValue := ⟨981493, pr981493⟩
private theorem pr981523 : PrimeCertificate 981523 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31,pv1759]) (by decide +kernel)
def pv981523 : PrimeValue := ⟨981523, pr981523⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
