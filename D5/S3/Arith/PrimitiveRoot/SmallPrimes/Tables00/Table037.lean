/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table037
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table037.pv97081
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table007
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table019
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table020

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr97081 : PrimeCertificate 97081 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv809]) (by decide +kernel)
def pv97081 : PrimeValue := ⟨97081, pr97081⟩
private theorem pr97103 : PrimeCertificate 97103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv47,pv1033]) (by decide +kernel)
def pv97103 : PrimeValue := ⟨97103, pr97103⟩
private theorem pr97117 : PrimeCertificate 97117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv8093]) (by decide +kernel)
def pv97117 : PrimeValue := ⟨97117, pr97117⟩
private theorem pr97127 : PrimeCertificate 97127 :=
  certifyPrime (q := pv5) (ls := [pv2,pv48563]) (by decide +kernel)
def pv97127 : PrimeValue := ⟨97127, pr97127⟩
private theorem pr97151 : PrimeCertificate 97151 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv29,pv67]) (by decide +kernel)
def pv97151 : PrimeValue := ⟨97151, pr97151⟩
private theorem pr97157 : PrimeCertificate 97157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv107,pv227]) (by decide +kernel)
def pv97157 : PrimeValue := ⟨97157, pr97157⟩
private theorem pr97159 : PrimeCertificate 97159 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv16193]) (by decide +kernel)
def pv97159 : PrimeValue := ⟨97159, pr97159⟩
private theorem pr97169 : PrimeCertificate 97169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv6073]) (by decide +kernel)
def pv97169 : PrimeValue := ⟨97169, pr97169⟩
private theorem pr97171 : PrimeCertificate 97171 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv41,pv79]) (by decide +kernel)
def pv97171 : PrimeValue := ⟨97171, pr97171⟩
private theorem pr97177 : PrimeCertificate 97177 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4049]) (by decide +kernel)
def pv97177 : PrimeValue := ⟨97177, pr97177⟩
private theorem pr97187 : PrimeCertificate 97187 :=
  certifyPrime (q := pv2) (ls := [pv2,pv48593]) (by decide +kernel)
def pv97187 : PrimeValue := ⟨97187, pr97187⟩
private theorem pr97213 : PrimeCertificate 97213 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv8101]) (by decide +kernel)
def pv97213 : PrimeValue := ⟨97213, pr97213⟩
private theorem pr97231 : PrimeCertificate 97231 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv463]) (by decide +kernel)
def pv97231 : PrimeValue := ⟨97231, pr97231⟩
private theorem pr97241 : PrimeCertificate 97241 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv13,pv17]) (by decide +kernel)
def pv97241 : PrimeValue := ⟨97241, pr97241⟩
private theorem pr97259 : PrimeCertificate 97259 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv6947]) (by decide +kernel)
def pv97259 : PrimeValue := ⟨97259, pr97259⟩
private theorem pr97283 : PrimeCertificate 97283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv127,pv383]) (by decide +kernel)
def pv97283 : PrimeValue := ⟨97283, pr97283⟩
private theorem pr97301 : PrimeCertificate 97301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv139]) (by decide +kernel)
def pv97301 : PrimeValue := ⟨97301, pr97301⟩
private theorem pr97303 : PrimeCertificate 97303 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv16217]) (by decide +kernel)
def pv97303 : PrimeValue := ⟨97303, pr97303⟩
private theorem pr97327 : PrimeCertificate 97327 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv5407]) (by decide +kernel)
def pv97327 : PrimeValue := ⟨97327, pr97327⟩
private theorem pr97367 : PrimeCertificate 97367 :=
  certifyPrime (q := pv5) (ls := [pv2,pv89,pv547]) (by decide +kernel)
def pv97367 : PrimeValue := ⟨97367, pr97367⟩
private theorem pr97369 : PrimeCertificate 97369 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv4057]) (by decide +kernel)
def pv97369 : PrimeValue := ⟨97369, pr97369⟩
private theorem pr97373 : PrimeCertificate 97373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv2213]) (by decide +kernel)
def pv97373 : PrimeValue := ⟨97373, pr97373⟩
private theorem pr97379 : PrimeCertificate 97379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv181,pv269]) (by decide +kernel)
def pv97379 : PrimeValue := ⟨97379, pr97379⟩
private theorem pr97387 : PrimeCertificate 97387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv16231]) (by decide +kernel)
def pv97387 : PrimeValue := ⟨97387, pr97387⟩
private theorem pr97397 : PrimeCertificate 97397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv1873]) (by decide +kernel)
def pv97397 : PrimeValue := ⟨97397, pr97397⟩
private theorem pr97423 : PrimeCertificate 97423 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv1249]) (by decide +kernel)
def pv97423 : PrimeValue := ⟨97423, pr97423⟩
private theorem pr97429 : PrimeCertificate 97429 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23,pv353]) (by decide +kernel)
def pv97429 : PrimeValue := ⟨97429, pr97429⟩
private theorem pr97441 : PrimeCertificate 97441 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv5,pv7,pv29]) (by decide +kernel)
def pv97441 : PrimeValue := ⟨97441, pr97441⟩
private theorem pr97453 : PrimeCertificate 97453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv2707]) (by decide +kernel)
def pv97453 : PrimeValue := ⟨97453, pr97453⟩
private theorem pr97459 : PrimeCertificate 97459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv439]) (by decide +kernel)
def pv97459 : PrimeValue := ⟨97459, pr97459⟩
private theorem pr97463 : PrimeCertificate 97463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv48731]) (by decide +kernel)
def pv97463 : PrimeValue := ⟨97463, pr97463⟩
private theorem pr97499 : PrimeCertificate 97499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv41]) (by decide +kernel)
def pv97499 : PrimeValue := ⟨97499, pr97499⟩
private theorem pr97501 : PrimeCertificate 97501 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv97501 : PrimeValue := ⟨97501, pr97501⟩
private theorem pr97511 : PrimeCertificate 97511 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv199]) (by decide +kernel)
def pv97511 : PrimeValue := ⟨97511, pr97511⟩
private theorem pr97523 : PrimeCertificate 97523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv48761]) (by decide +kernel)
def pv97523 : PrimeValue := ⟨97523, pr97523⟩
private theorem pr97547 : PrimeCertificate 97547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv19,pv151]) (by decide +kernel)
def pv97547 : PrimeValue := ⟨97547, pr97547⟩
private theorem pr97549 : PrimeCertificate 97549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv739]) (by decide +kernel)
def pv97549 : PrimeValue := ⟨97549, pr97549⟩
private theorem pr97553 : PrimeCertificate 97553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv13,pv67]) (by decide +kernel)
def pv97553 : PrimeValue := ⟨97553, pr97553⟩
private theorem pr97561 : PrimeCertificate 97561 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv271]) (by decide +kernel)
def pv97561 : PrimeValue := ⟨97561, pr97561⟩
private theorem pr97571 : PrimeCertificate 97571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv887]) (by decide +kernel)
def pv97571 : PrimeValue := ⟨97571, pr97571⟩
private theorem pr97579 : PrimeCertificate 97579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv139]) (by decide +kernel)
def pv97579 : PrimeValue := ⟨97579, pr97579⟩
private theorem pr97583 : PrimeCertificate 97583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv97,pv503]) (by decide +kernel)
def pv97583 : PrimeValue := ⟨97583, pr97583⟩
private theorem pr97607 : PrimeCertificate 97607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv37,pv1319]) (by decide +kernel)
def pv97607 : PrimeValue := ⟨97607, pr97607⟩
private theorem pr97609 : PrimeCertificate 97609 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv83]) (by decide +kernel)
def pv97609 : PrimeValue := ⟨97609, pr97609⟩
private theorem pr97613 : PrimeCertificate 97613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv1061]) (by decide +kernel)
def pv97613 : PrimeValue := ⟨97613, pr97613⟩
private theorem pr97649 : PrimeCertificate 97649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv359]) (by decide +kernel)
def pv97649 : PrimeValue := ⟨97649, pr97649⟩
private theorem pr97651 : PrimeCertificate 97651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv31]) (by decide +kernel)
def pv97651 : PrimeValue := ⟨97651, pr97651⟩
private theorem pr97673 : PrimeCertificate 97673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv421]) (by decide +kernel)
def pv97673 : PrimeValue := ⟨97673, pr97673⟩
private theorem pr97687 : PrimeCertificate 97687 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv67]) (by decide +kernel)
def pv97687 : PrimeValue := ⟨97687, pr97687⟩
private theorem pr97711 : PrimeCertificate 97711 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv3257]) (by decide +kernel)
def pv97711 : PrimeValue := ⟨97711, pr97711⟩
private theorem pr97729 : PrimeCertificate 97729 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv509]) (by decide +kernel)
def pv97729 : PrimeValue := ⟨97729, pr97729⟩
private theorem pr97771 : PrimeCertificate 97771 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv3259]) (by decide +kernel)
def pv97771 : PrimeValue := ⟨97771, pr97771⟩
private theorem pr97777 : PrimeCertificate 97777 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv97]) (by decide +kernel)
def pv97777 : PrimeValue := ⟨97777, pr97777⟩
private theorem pr97787 : PrimeCertificate 97787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv3761]) (by decide +kernel)
def pv97787 : PrimeValue := ⟨97787, pr97787⟩
private theorem pr97789 : PrimeCertificate 97789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv281]) (by decide +kernel)
def pv97789 : PrimeValue := ⟨97789, pr97789⟩
private theorem pr97813 : PrimeCertificate 97813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv13,pv19]) (by decide +kernel)
def pv97813 : PrimeValue := ⟨97813, pr97813⟩
private theorem pr97829 : PrimeCertificate 97829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv661]) (by decide +kernel)
def pv97829 : PrimeValue := ⟨97829, pr97829⟩
private theorem pr97841 : PrimeCertificate 97841 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv1223]) (by decide +kernel)
def pv97841 : PrimeValue := ⟨97841, pr97841⟩
private theorem pr97843 : PrimeCertificate 97843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv709]) (by decide +kernel)
def pv97843 : PrimeValue := ⟨97843, pr97843⟩
private theorem pr97847 : PrimeCertificate 97847 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv29,pv241]) (by decide +kernel)
def pv97847 : PrimeValue := ⟨97847, pr97847⟩
private theorem pr97849 : PrimeCertificate 97849 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv151]) (by decide +kernel)
def pv97849 : PrimeValue := ⟨97849, pr97849⟩
private theorem pr97859 : PrimeCertificate 97859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv113,pv433]) (by decide +kernel)
def pv97859 : PrimeValue := ⟨97859, pr97859⟩
private theorem pr97861 : PrimeCertificate 97861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv233]) (by decide +kernel)
def pv97861 : PrimeValue := ⟨97861, pr97861⟩
private theorem pr97871 : PrimeCertificate 97871 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv9787]) (by decide +kernel)
def pv97871 : PrimeValue := ⟨97871, pr97871⟩
private theorem pr97879 : PrimeCertificate 97879 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11,pv1483]) (by decide +kernel)
def pv97879 : PrimeValue := ⟨97879, pr97879⟩
private theorem pr97883 : PrimeCertificate 97883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv109,pv449]) (by decide +kernel)
def pv97883 : PrimeValue := ⟨97883, pr97883⟩
private theorem pr97919 : PrimeCertificate 97919 :=
  certifyPrime (q := pv23) (ls := [pv2,pv173,pv283]) (by decide +kernel)
def pv97919 : PrimeValue := ⟨97919, pr97919⟩
private theorem pr97927 : PrimeCertificate 97927 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv859]) (by decide +kernel)
def pv97927 : PrimeValue := ⟨97927, pr97927⟩
private theorem pr97931 : PrimeCertificate 97931 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv1399]) (by decide +kernel)
def pv97931 : PrimeValue := ⟨97931, pr97931⟩
private theorem pr97943 : PrimeCertificate 97943 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv3767]) (by decide +kernel)
def pv97943 : PrimeValue := ⟨97943, pr97943⟩
private theorem pr97961 : PrimeCertificate 97961 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv31,pv79]) (by decide +kernel)
def pv97961 : PrimeValue := ⟨97961, pr97961⟩
private theorem pr97967 : PrimeCertificate 97967 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv61,pv73]) (by decide +kernel)
def pv97967 : PrimeValue := ⟨97967, pr97967⟩
private theorem pr97973 : PrimeCertificate 97973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv3499]) (by decide +kernel)
def pv97973 : PrimeValue := ⟨97973, pr97973⟩
private theorem pr98009 : PrimeCertificate 98009 :=
  certifyPrime (q := pv3) (ls := [pv2,pv12251]) (by decide +kernel)
def pv98009 : PrimeValue := ⟨98009, pr98009⟩
private theorem pr98011 : PrimeCertificate 98011 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv98011 : PrimeValue := ⟨98011, pr98011⟩
private theorem pr98017 : PrimeCertificate 98017 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1021]) (by decide +kernel)
def pv98017 : PrimeValue := ⟨98017, pr98017⟩
private theorem pr98041 : PrimeCertificate 98041 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv19,pv43]) (by decide +kernel)
def pv98041 : PrimeValue := ⟨98041, pr98041⟩
private theorem pr98047 : PrimeCertificate 98047 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv419]) (by decide +kernel)
def pv98047 : PrimeValue := ⟨98047, pr98047⟩
private theorem pr98057 : PrimeCertificate 98057 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv17,pv103]) (by decide +kernel)
def pv98057 : PrimeValue := ⟨98057, pr98057⟩
private theorem pr98081 : PrimeCertificate 98081 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv613]) (by decide +kernel)
def pv98081 : PrimeValue := ⟨98081, pr98081⟩
private theorem pr98101 : PrimeCertificate 98101 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv109]) (by decide +kernel)
def pv98101 : PrimeValue := ⟨98101, pr98101⟩
private theorem pr98123 : PrimeCertificate 98123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71,pv691]) (by decide +kernel)
def pv98123 : PrimeValue := ⟨98123, pr98123⟩
private theorem pr98129 : PrimeCertificate 98129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv6133]) (by decide +kernel)
def pv98129 : PrimeValue := ⟨98129, pr98129⟩
private theorem pr98143 : PrimeCertificate 98143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv1487]) (by decide +kernel)
def pv98143 : PrimeValue := ⟨98143, pr98143⟩
private theorem pr98207 : PrimeCertificate 98207 :=
  certifyPrime (q := pv5) (ls := [pv2,pv49103]) (by decide +kernel)
def pv98207 : PrimeValue := ⟨98207, pr98207⟩
private theorem pr98213 : PrimeCertificate 98213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv571]) (by decide +kernel)
def pv98213 : PrimeValue := ⟨98213, pr98213⟩
private theorem pr98221 : PrimeCertificate 98221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1637]) (by decide +kernel)
def pv98221 : PrimeValue := ⟨98221, pr98221⟩
private theorem pr98227 : PrimeCertificate 98227 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv107]) (by decide +kernel)
def pv98227 : PrimeValue := ⟨98227, pr98227⟩
private theorem pr98251 : PrimeCertificate 98251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv131]) (by decide +kernel)
def pv98251 : PrimeValue := ⟨98251, pr98251⟩
private theorem pr98257 : PrimeCertificate 98257 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv23,pv89]) (by decide +kernel)
def pv98257 : PrimeValue := ⟨98257, pr98257⟩
private theorem pr98269 : PrimeCertificate 98269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv431]) (by decide +kernel)
def pv98269 : PrimeValue := ⟨98269, pr98269⟩
private theorem pr98297 : PrimeCertificate 98297 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv1117]) (by decide +kernel)
def pv98297 : PrimeValue := ⟨98297, pr98297⟩
private theorem pr98299 : PrimeCertificate 98299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv127]) (by decide +kernel)
def pv98299 : PrimeValue := ⟨98299, pr98299⟩
private theorem pr98317 : PrimeCertificate 98317 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv2731]) (by decide +kernel)
def pv98317 : PrimeValue := ⟨98317, pr98317⟩
private theorem pr98321 : PrimeCertificate 98321 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1229]) (by decide +kernel)
def pv98321 : PrimeValue := ⟨98321, pr98321⟩
private theorem pr98323 : PrimeCertificate 98323 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv2341]) (by decide +kernel)
def pv98323 : PrimeValue := ⟨98323, pr98323⟩
private theorem pr98327 : PrimeCertificate 98327 :=
  certifyPrime (q := pv5) (ls := [pv2,pv211,pv233]) (by decide +kernel)
def pv98327 : PrimeValue := ⟨98327, pr98327⟩
private theorem pr98347 : PrimeCertificate 98347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv443]) (by decide +kernel)
def pv98347 : PrimeValue := ⟨98347, pr98347⟩
private theorem pr98369 : PrimeCertificate 98369 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv53]) (by decide +kernel)
def pv98369 : PrimeValue := ⟨98369, pr98369⟩
private theorem pr98377 : PrimeCertificate 98377 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4099]) (by decide +kernel)
def pv98377 : PrimeValue := ⟨98377, pr98377⟩
private theorem pr98387 : PrimeCertificate 98387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv49193]) (by decide +kernel)
def pv98387 : PrimeValue := ⟨98387, pr98387⟩
private theorem pr98389 : PrimeCertificate 98389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv911]) (by decide +kernel)
def pv98389 : PrimeValue := ⟨98389, pr98389⟩
private theorem pr98407 : PrimeCertificate 98407 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv11,pv71]) (by decide +kernel)
def pv98407 : PrimeValue := ⟨98407, pr98407⟩
private theorem pr98411 : PrimeCertificate 98411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv757]) (by decide +kernel)
def pv98411 : PrimeValue := ⟨98411, pr98411⟩
private theorem pr98419 : PrimeCertificate 98419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv349]) (by decide +kernel)
def pv98419 : PrimeValue := ⟨98419, pr98419⟩
private theorem pr98429 : PrimeCertificate 98429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv2237]) (by decide +kernel)
def pv98429 : PrimeValue := ⟨98429, pr98429⟩
private theorem pr98443 : PrimeCertificate 98443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1823]) (by decide +kernel)
def pv98443 : PrimeValue := ⟨98443, pr98443⟩
private theorem pr98453 : PrimeCertificate 98453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv151,pv163]) (by decide +kernel)
def pv98453 : PrimeValue := ⟨98453, pr98453⟩
private theorem pr98459 : PrimeCertificate 98459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv2591]) (by decide +kernel)
def pv98459 : PrimeValue := ⟨98459, pr98459⟩
private theorem pr98467 : PrimeCertificate 98467 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv16411]) (by decide +kernel)
def pv98467 : PrimeValue := ⟨98467, pr98467⟩
private theorem pr98473 : PrimeCertificate 98473 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv11,pv373]) (by decide +kernel)
def pv98473 : PrimeValue := ⟨98473, pr98473⟩
private theorem pr98479 : PrimeCertificate 98479 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5471]) (by decide +kernel)
def pv98479 : PrimeValue := ⟨98479, pr98479⟩
private theorem pr98491 : PrimeCertificate 98491 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv67]) (by decide +kernel)
def pv98491 : PrimeValue := ⟨98491, pr98491⟩
private theorem pr98507 : PrimeCertificate 98507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv49253]) (by decide +kernel)
def pv98507 : PrimeValue := ⟨98507, pr98507⟩
private theorem pr98519 : PrimeCertificate 98519 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv31,pv227]) (by decide +kernel)
def pv98519 : PrimeValue := ⟨98519, pr98519⟩
private theorem pr98533 : PrimeCertificate 98533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv23]) (by decide +kernel)
def pv98533 : PrimeValue := ⟨98533, pr98533⟩
private theorem pr98543 : PrimeCertificate 98543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv29,pv1699]) (by decide +kernel)
def pv98543 : PrimeValue := ⟨98543, pr98543⟩
private theorem pr98561 : PrimeCertificate 98561 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv11]) (by decide +kernel)
def pv98561 : PrimeValue := ⟨98561, pr98561⟩
private theorem pr98563 : PrimeCertificate 98563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv16427]) (by decide +kernel)
def pv98563 : PrimeValue := ⟨98563, pr98563⟩
private theorem pr98573 : PrimeCertificate 98573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv1297]) (by decide +kernel)
def pv98573 : PrimeValue := ⟨98573, pr98573⟩
private theorem pr98597 : PrimeCertificate 98597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv157]) (by decide +kernel)
def pv98597 : PrimeValue := ⟨98597, pr98597⟩
private theorem pr98621 : PrimeCertificate 98621 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv4931]) (by decide +kernel)
def pv98621 : PrimeValue := ⟨98621, pr98621⟩
private theorem pr98627 : PrimeCertificate 98627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv4483]) (by decide +kernel)
def pv98627 : PrimeValue := ⟨98627, pr98627⟩
private theorem pr98639 : PrimeCertificate 98639 :=
  certifyPrime (q := pv7) (ls := [pv2,pv149,pv331]) (by decide +kernel)
def pv98639 : PrimeValue := ⟨98639, pr98639⟩
private theorem pr98641 : PrimeCertificate 98641 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv137]) (by decide +kernel)
def pv98641 : PrimeValue := ⟨98641, pr98641⟩
private theorem pr98663 : PrimeCertificate 98663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv49331]) (by decide +kernel)
def pv98663 : PrimeValue := ⟨98663, pr98663⟩
private theorem pr98669 : PrimeCertificate 98669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv1451]) (by decide +kernel)
def pv98669 : PrimeValue := ⟨98669, pr98669⟩
private theorem pr98689 : PrimeCertificate 98689 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv257]) (by decide +kernel)
def pv98689 : PrimeValue := ⟨98689, pr98689⟩
private theorem pr98711 : PrimeCertificate 98711 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv9871]) (by decide +kernel)
def pv98711 : PrimeValue := ⟨98711, pr98711⟩
private theorem pr98717 : PrimeCertificate 98717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv29,pv37]) (by decide +kernel)
def pv98717 : PrimeValue := ⟨98717, pr98717⟩
private theorem pr98729 : PrimeCertificate 98729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv41,pv43]) (by decide +kernel)
def pv98729 : PrimeValue := ⟨98729, pr98729⟩
private theorem pr98731 : PrimeCertificate 98731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1097]) (by decide +kernel)
def pv98731 : PrimeValue := ⟨98731, pr98731⟩
private theorem pr98737 : PrimeCertificate 98737 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv17]) (by decide +kernel)
def pv98737 : PrimeValue := ⟨98737, pr98737⟩
private theorem pr98773 : PrimeCertificate 98773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv8231]) (by decide +kernel)
def pv98773 : PrimeValue := ⟨98773, pr98773⟩
private theorem pr98779 : PrimeCertificate 98779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv101,pv163]) (by decide +kernel)
def pv98779 : PrimeValue := ⟨98779, pr98779⟩
private theorem pr98801 : PrimeCertificate 98801 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv19]) (by decide +kernel)
def pv98801 : PrimeValue := ⟨98801, pr98801⟩
private theorem pr98807 : PrimeCertificate 98807 :=
  certifyPrime (q := pv5) (ls := [pv2,pv127,pv389]) (by decide +kernel)
def pv98807 : PrimeValue := ⟨98807, pr98807⟩
private theorem pr98837 : PrimeCertificate 98837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv24709]) (by decide +kernel)
def pv98837 : PrimeValue := ⟨98837, pr98837⟩
private theorem pr98849 : PrimeCertificate 98849 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3089]) (by decide +kernel)
def pv98849 : PrimeValue := ⟨98849, pr98849⟩
private theorem pr98867 : PrimeCertificate 98867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv49433]) (by decide +kernel)
def pv98867 : PrimeValue := ⟨98867, pr98867⟩
private theorem pr98869 : PrimeCertificate 98869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv107]) (by decide +kernel)
def pv98869 : PrimeValue := ⟨98869, pr98869⟩
private theorem pr98873 : PrimeCertificate 98873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv727]) (by decide +kernel)
def pv98873 : PrimeValue := ⟨98873, pr98873⟩
private theorem pr98887 : PrimeCertificate 98887 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv16481]) (by decide +kernel)
def pv98887 : PrimeValue := ⟨98887, pr98887⟩
private theorem pr98893 : PrimeCertificate 98893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv67]) (by decide +kernel)
def pv98893 : PrimeValue := ⟨98893, pr98893⟩
private theorem pr98897 : PrimeCertificate 98897 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv883]) (by decide +kernel)
def pv98897 : PrimeValue := ⟨98897, pr98897⟩
private theorem pr98899 : PrimeCertificate 98899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53,pv311]) (by decide +kernel)
def pv98899 : PrimeValue := ⟨98899, pr98899⟩
private theorem pr98909 : PrimeCertificate 98909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv79,pv313]) (by decide +kernel)
def pv98909 : PrimeValue := ⟨98909, pr98909⟩
private theorem pr98911 : PrimeCertificate 98911 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv7,pv157]) (by decide +kernel)
def pv98911 : PrimeValue := ⟨98911, pr98911⟩
private theorem pr98927 : PrimeCertificate 98927 :=
  certifyPrime (q := pv5) (ls := [pv2,pv49463]) (by decide +kernel)
def pv98927 : PrimeValue := ⟨98927, pr98927⟩
private theorem pr98929 : PrimeCertificate 98929 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv229]) (by decide +kernel)
def pv98929 : PrimeValue := ⟨98929, pr98929⟩
private theorem pr98939 : PrimeCertificate 98939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv37,pv191]) (by decide +kernel)
def pv98939 : PrimeValue := ⟨98939, pr98939⟩
private theorem pr98947 : PrimeCertificate 98947 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv239]) (by decide +kernel)
def pv98947 : PrimeValue := ⟨98947, pr98947⟩
private theorem pr98953 : PrimeCertificate 98953 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv19,pv31]) (by decide +kernel)
def pv98953 : PrimeValue := ⟨98953, pr98953⟩
private theorem pr98963 : PrimeCertificate 98963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv49481]) (by decide +kernel)
def pv98963 : PrimeValue := ⟨98963, pr98963⟩
private theorem pr98981 : PrimeCertificate 98981 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv101]) (by decide +kernel)
def pv98981 : PrimeValue := ⟨98981, pr98981⟩
private theorem pr98993 : PrimeCertificate 98993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv269]) (by decide +kernel)
def pv98993 : PrimeValue := ⟨98993, pr98993⟩
private theorem pr98999 : PrimeCertificate 98999 :=
  certifyPrime (q := pv19) (ls := [pv2,pv49499]) (by decide +kernel)
def pv98999 : PrimeValue := ⟨98999, pr98999⟩
private theorem pr99017 : PrimeCertificate 99017 :=
  certifyPrime (q := pv3) (ls := [pv2,pv12377]) (by decide +kernel)
def pv99017 : PrimeValue := ⟨99017, pr99017⟩
private theorem pr99023 : PrimeCertificate 99023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11,pv643]) (by decide +kernel)
def pv99023 : PrimeValue := ⟨99023, pr99023⟩
private theorem pr99041 : PrimeCertificate 99041 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv619]) (by decide +kernel)
def pv99041 : PrimeValue := ⟨99041, pr99041⟩
private theorem pr99053 : PrimeCertificate 99053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv24763]) (by decide +kernel)
def pv99053 : PrimeValue := ⟨99053, pr99053⟩
private theorem pr99079 : PrimeCertificate 99079 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv337]) (by decide +kernel)
def pv99079 : PrimeValue := ⟨99079, pr99079⟩
private theorem pr99083 : PrimeCertificate 99083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv107,pv463]) (by decide +kernel)
def pv99083 : PrimeValue := ⟨99083, pr99083⟩
private theorem pr99089 : PrimeCertificate 99089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv563]) (by decide +kernel)
def pv99089 : PrimeValue := ⟨99089, pr99089⟩
private theorem pr99103 : PrimeCertificate 99103 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv83,pv199]) (by decide +kernel)
def pv99103 : PrimeValue := ⟨99103, pr99103⟩
private theorem pr99109 : PrimeCertificate 99109 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv2753]) (by decide +kernel)
def pv99109 : PrimeValue := ⟨99109, pr99109⟩
private theorem pr99119 : PrimeCertificate 99119 :=
  certifyPrime (q := pv11) (ls := [pv2,pv49559]) (by decide +kernel)
def pv99119 : PrimeValue := ⟨99119, pr99119⟩
private theorem pr99131 : PrimeCertificate 99131 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv23,pv431]) (by decide +kernel)
def pv99131 : PrimeValue := ⟨99131, pr99131⟩
private theorem pr99133 : PrimeCertificate 99133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv751]) (by decide +kernel)
def pv99133 : PrimeValue := ⟨99133, pr99133⟩
private theorem pr99137 : PrimeCertificate 99137 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1549]) (by decide +kernel)
def pv99137 : PrimeValue := ⟨99137, pr99137⟩
private theorem pr99149 : PrimeCertificate 99149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv3541]) (by decide +kernel)
def pv99149 : PrimeValue := ⟨99149, pr99149⟩
private theorem pr99173 : PrimeCertificate 99173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv24793]) (by decide +kernel)
def pv99173 : PrimeValue := ⟨99173, pr99173⟩
private theorem pr99181 : PrimeCertificate 99181 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv19,pv29]) (by decide +kernel)
def pv99181 : PrimeValue := ⟨99181, pr99181⟩
private theorem pr99191 : PrimeCertificate 99191 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv13,pv109]) (by decide +kernel)
def pv99191 : PrimeValue := ⟨99191, pr99191⟩
private theorem pr99223 : PrimeCertificate 99223 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv719]) (by decide +kernel)
def pv99223 : PrimeValue := ⟨99223, pr99223⟩
private theorem pr99233 : PrimeCertificate 99233 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv443]) (by decide +kernel)
def pv99233 : PrimeValue := ⟨99233, pr99233⟩
private theorem pr99241 : PrimeCertificate 99241 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv827]) (by decide +kernel)
def pv99241 : PrimeValue := ⟨99241, pr99241⟩
private theorem pr99251 : PrimeCertificate 99251 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv397]) (by decide +kernel)
def pv99251 : PrimeValue := ⟨99251, pr99251⟩
private theorem pr99257 : PrimeCertificate 99257 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv653]) (by decide +kernel)
def pv99257 : PrimeValue := ⟨99257, pr99257⟩
private theorem pr99259 : PrimeCertificate 99259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv71,pv233]) (by decide +kernel)
def pv99259 : PrimeValue := ⟨99259, pr99259⟩
private theorem pr99277 : PrimeCertificate 99277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv8273]) (by decide +kernel)
def pv99277 : PrimeValue := ⟨99277, pr99277⟩
private theorem pr99289 : PrimeCertificate 99289 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv7,pv197]) (by decide +kernel)
def pv99289 : PrimeValue := ⟨99289, pr99289⟩
private theorem pr99317 : PrimeCertificate 99317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv3547]) (by decide +kernel)
def pv99317 : PrimeValue := ⟨99317, pr99317⟩
private theorem pr99347 : PrimeCertificate 99347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv3821]) (by decide +kernel)
def pv99347 : PrimeValue := ⟨99347, pr99347⟩
private theorem pr99367 : PrimeCertificate 99367 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv16561]) (by decide +kernel)
def pv99367 : PrimeValue := ⟨99367, pr99367⟩
private theorem pr99371 : PrimeCertificate 99371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv523]) (by decide +kernel)
def pv99371 : PrimeValue := ⟨99371, pr99371⟩
private theorem pr99377 : PrimeCertificate 99377 :=
  certifyPrime (q := pv3) (ls := [pv2,pv6211]) (by decide +kernel)
def pv99377 : PrimeValue := ⟨99377, pr99377⟩
private theorem pr99391 : PrimeCertificate 99391 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv3313]) (by decide +kernel)
def pv99391 : PrimeValue := ⟨99391, pr99391⟩
private theorem pr99397 : PrimeCertificate 99397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv251]) (by decide +kernel)
def pv99397 : PrimeValue := ⟨99397, pr99397⟩
private theorem pr99401 : PrimeCertificate 99401 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv71]) (by decide +kernel)
def pv99401 : PrimeValue := ⟨99401, pr99401⟩
private theorem pr99409 : PrimeCertificate 99409 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv19,pv109]) (by decide +kernel)
def pv99409 : PrimeValue := ⟨99409, pr99409⟩
private theorem pr99431 : PrimeCertificate 99431 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv61,pv163]) (by decide +kernel)
def pv99431 : PrimeValue := ⟨99431, pr99431⟩
private theorem pr99439 : PrimeCertificate 99439 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv16573]) (by decide +kernel)
def pv99439 : PrimeValue := ⟨99439, pr99439⟩
private theorem pr99469 : PrimeCertificate 99469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv307]) (by decide +kernel)
def pv99469 : PrimeValue := ⟨99469, pr99469⟩
private theorem pr99487 : PrimeCertificate 99487 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5527]) (by decide +kernel)
def pv99487 : PrimeValue := ⟨99487, pr99487⟩
private theorem pr99497 : PrimeCertificate 99497 :=
  certifyPrime (q := pv3) (ls := [pv2,pv12437]) (by decide +kernel)
def pv99497 : PrimeValue := ⟨99497, pr99497⟩
private theorem pr99523 : PrimeCertificate 99523 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv97]) (by decide +kernel)
def pv99523 : PrimeValue := ⟨99523, pr99523⟩
private theorem pr99527 : PrimeCertificate 99527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv7109]) (by decide +kernel)
def pv99527 : PrimeValue := ⟨99527, pr99527⟩
private theorem pr99529 : PrimeCertificate 99529 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv13,pv29]) (by decide +kernel)
def pv99529 : PrimeValue := ⟨99529, pr99529⟩
private theorem pr99551 : PrimeCertificate 99551 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv181]) (by decide +kernel)
def pv99551 : PrimeValue := ⟨99551, pr99551⟩
private theorem pr99559 : PrimeCertificate 99559 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5531]) (by decide +kernel)
def pv99559 : PrimeValue := ⟨99559, pr99559⟩
private theorem pr99563 : PrimeCertificate 99563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67,pv743]) (by decide +kernel)
def pv99563 : PrimeValue := ⟨99563, pr99563⟩
private theorem pr99571 : PrimeCertificate 99571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv3319]) (by decide +kernel)
def pv99571 : PrimeValue := ⟨99571, pr99571⟩
private theorem pr99577 : PrimeCertificate 99577 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv461]) (by decide +kernel)
def pv99577 : PrimeValue := ⟨99577, pr99577⟩
private theorem pr99581 : PrimeCertificate 99581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv383]) (by decide +kernel)
def pv99581 : PrimeValue := ⟨99581, pr99581⟩
private theorem pr99607 : PrimeCertificate 99607 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv1277]) (by decide +kernel)
def pv99607 : PrimeValue := ⟨99607, pr99607⟩
private theorem pr99611 : PrimeCertificate 99611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv1423]) (by decide +kernel)
def pv99611 : PrimeValue := ⟨99611, pr99611⟩
private theorem pr99623 : PrimeCertificate 99623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv49811]) (by decide +kernel)
def pv99623 : PrimeValue := ⟨99623, pr99623⟩
private theorem pr99643 : PrimeCertificate 99643 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv16607]) (by decide +kernel)
def pv99643 : PrimeValue := ⟨99643, pr99643⟩
private theorem pr99661 : PrimeCertificate 99661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv151]) (by decide +kernel)
def pv99661 : PrimeValue := ⟨99661, pr99661⟩
private theorem pr99667 : PrimeCertificate 99667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv113]) (by decide +kernel)
def pv99667 : PrimeValue := ⟨99667, pr99667⟩
private theorem pr99679 : PrimeCertificate 99679 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv37,pv449]) (by decide +kernel)
def pv99679 : PrimeValue := ⟨99679, pr99679⟩
private theorem pr99689 : PrimeCertificate 99689 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv733]) (by decide +kernel)
def pv99689 : PrimeValue := ⟨99689, pr99689⟩
private theorem pr99707 : PrimeCertificate 99707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv49853]) (by decide +kernel)
def pv99707 : PrimeValue := ⟨99707, pr99707⟩
private theorem pr99709 : PrimeCertificate 99709 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv7,pv1187]) (by decide +kernel)
def pv99709 : PrimeValue := ⟨99709, pr99709⟩
private theorem pr99713 : PrimeCertificate 99713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv41]) (by decide +kernel)
def pv99713 : PrimeValue := ⟨99713, pr99713⟩
private theorem pr99719 : PrimeCertificate 99719 :=
  certifyPrime (q := pv7) (ls := [pv2,pv73,pv683]) (by decide +kernel)
def pv99719 : PrimeValue := ⟨99719, pr99719⟩
private theorem pr99721 : PrimeCertificate 99721 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv277]) (by decide +kernel)
def pv99721 : PrimeValue := ⟨99721, pr99721⟩
private theorem pr99733 : PrimeCertificate 99733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv8311]) (by decide +kernel)
def pv99733 : PrimeValue := ⟨99733, pr99733⟩
private theorem pr99761 : PrimeCertificate 99761 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv29,pv43]) (by decide +kernel)
def pv99761 : PrimeValue := ⟨99761, pr99761⟩
private theorem pr99787 : PrimeCertificate 99787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv16631]) (by decide +kernel)
def pv99787 : PrimeValue := ⟨99787, pr99787⟩
private theorem pr99793 : PrimeCertificate 99793 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv11]) (by decide +kernel)
def pv99793 : PrimeValue := ⟨99793, pr99793⟩
private theorem pr99809 : PrimeCertificate 99809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3119]) (by decide +kernel)
def pv99809 : PrimeValue := ⟨99809, pr99809⟩
private theorem pr99817 : PrimeCertificate 99817 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4159]) (by decide +kernel)
def pv99817 : PrimeValue := ⟨99817, pr99817⟩
private theorem pr99823 : PrimeCertificate 99823 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv127,pv131]) (by decide +kernel)
def pv99823 : PrimeValue := ⟨99823, pr99823⟩
private theorem pr99829 : PrimeCertificate 99829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv59]) (by decide +kernel)
def pv99829 : PrimeValue := ⟨99829, pr99829⟩
private theorem pr99833 : PrimeCertificate 99833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv12479]) (by decide +kernel)
def pv99833 : PrimeValue := ⟨99833, pr99833⟩
private theorem pr99839 : PrimeCertificate 99839 :=
  certifyPrime (q := pv11) (ls := [pv2,pv49919]) (by decide +kernel)
def pv99839 : PrimeValue := ⟨99839, pr99839⟩
private theorem pr99859 : PrimeCertificate 99859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv17,pv89]) (by decide +kernel)
def pv99859 : PrimeValue := ⟨99859, pr99859⟩
private theorem pr99871 : PrimeCertificate 99871 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv3329]) (by decide +kernel)
def pv99871 : PrimeValue := ⟨99871, pr99871⟩
private theorem pr99877 : PrimeCertificate 99877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv29,pv41]) (by decide +kernel)
def pv99877 : PrimeValue := ⟨99877, pr99877⟩
private theorem pr99901 : PrimeCertificate 99901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv37]) (by decide +kernel)
def pv99901 : PrimeValue := ⟨99901, pr99901⟩
private theorem pr99907 : PrimeCertificate 99907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv16651]) (by decide +kernel)
def pv99907 : PrimeValue := ⟨99907, pr99907⟩
private theorem pr99929 : PrimeCertificate 99929 :=
  certifyPrime (q := pv3) (ls := [pv2,pv12491]) (by decide +kernel)
def pv99929 : PrimeValue := ⟨99929, pr99929⟩
private theorem pr99961 : PrimeCertificate 99961 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv7,pv17]) (by decide +kernel)
def pv99961 : PrimeValue := ⟨99961, pr99961⟩
private theorem pr99989 : PrimeCertificate 99989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv3571]) (by decide +kernel)
def pv99989 : PrimeValue := ⟨99989, pr99989⟩
private theorem pr99991 : PrimeCertificate 99991 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv101]) (by decide +kernel)
def pv99991 : PrimeValue := ⟨99991, pr99991⟩
private theorem pr100019 : PrimeCertificate 100019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv1163]) (by decide +kernel)
def pv100019 : PrimeValue := ⟨100019, pr100019⟩
private theorem pr100043 : PrimeCertificate 100043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv50021]) (by decide +kernel)
def pv100043 : PrimeValue := ⟨100043, pr100043⟩
private theorem pr100049 : PrimeCertificate 100049 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv37]) (by decide +kernel)
def pv100049 : PrimeValue := ⟨100049, pr100049⟩
private theorem pr100057 : PrimeCertificate 100057 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv11,pv379]) (by decide +kernel)
def pv100057 : PrimeValue := ⟨100057, pr100057⟩
private theorem pr100069 : PrimeCertificate 100069 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv31,pv269]) (by decide +kernel)
def pv100069 : PrimeValue := ⟨100069, pr100069⟩
private theorem pr100103 : PrimeCertificate 100103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv50051]) (by decide +kernel)
def pv100103 : PrimeValue := ⟨100103, pr100103⟩
private theorem pr100109 : PrimeCertificate 100109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv863]) (by decide +kernel)
def pv100109 : PrimeValue := ⟨100109, pr100109⟩
private theorem pr100129 : PrimeCertificate 100129 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv149]) (by decide +kernel)
def pv100129 : PrimeValue := ⟨100129, pr100129⟩
private theorem pr100151 : PrimeCertificate 100151 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv2003]) (by decide +kernel)
def pv100151 : PrimeValue := ⟨100151, pr100151⟩
private theorem pr100153 : PrimeCertificate 100153 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv107]) (by decide +kernel)
def pv100153 : PrimeValue := ⟨100153, pr100153⟩
private theorem pr100169 : PrimeCertificate 100169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv659]) (by decide +kernel)
def pv100169 : PrimeValue := ⟨100169, pr100169⟩
private theorem pr100183 : PrimeCertificate 100183 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv59,pv283]) (by decide +kernel)
def pv100183 : PrimeValue := ⟨100183, pr100183⟩
private theorem pr100189 : PrimeCertificate 100189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv23]) (by decide +kernel)
def pv100189 : PrimeValue := ⟨100189, pr100189⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
