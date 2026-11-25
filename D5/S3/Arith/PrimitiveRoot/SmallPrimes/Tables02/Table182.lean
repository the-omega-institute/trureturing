/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table182
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table182.pv387281
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table012
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table016
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table025
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table026
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table064
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table065

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr387281 : PrimeCertificate 387281 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv47,pv103]) (by decide +kernel)
def pv387281 : PrimeValue := ⟨387281, pr387281⟩
private theorem pr387307 : PrimeCertificate 387307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv21517]) (by decide +kernel)
def pv387307 : PrimeValue := ⟨387307, pr387307⟩
private theorem pr387509 : PrimeCertificate 387509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv8807]) (by decide +kernel)
def pv387509 : PrimeValue := ⟨387509, pr387509⟩
private theorem pr387631 : PrimeCertificate 387631 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv59,pv73]) (by decide +kernel)
def pv387631 : PrimeValue := ⟨387631, pr387631⟩
private theorem pr387659 : PrimeCertificate 387659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv239,pv811]) (by decide +kernel)
def pv387659 : PrimeValue := ⟨387659, pr387659⟩
private theorem pr387679 : PrimeCertificate 387679 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv64613]) (by decide +kernel)
def pv387679 : PrimeValue := ⟨387679, pr387679⟩
private theorem pr387967 : PrimeCertificate 387967 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv64661]) (by decide +kernel)
def pv387967 : PrimeValue := ⟨387967, pr387967⟩
private theorem pr388081 : PrimeCertificate 388081 :=
  certifyPrime (q := pv59) (ls := [pv2,pv3,pv5,pv7,pv11]) (by decide +kernel)
def pv388081 : PrimeValue := ⟨388081, pr388081⟩
private theorem pr388099 : PrimeCertificate 388099 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7187]) (by decide +kernel)
def pv388099 : PrimeValue := ⟨388099, pr388099⟩
private theorem pr388159 : PrimeCertificate 388159 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv64693]) (by decide +kernel)
def pv388159 : PrimeValue := ⟨388159, pr388159⟩
private theorem pr388183 : PrimeCertificate 388183 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31,pv2087]) (by decide +kernel)
def pv388183 : PrimeValue := ⟨388183, pr388183⟩
private theorem pr388391 : PrimeCertificate 388391 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv38839]) (by decide +kernel)
def pv388391 : PrimeValue := ⟨388391, pr388391⟩
private theorem pr388481 : PrimeCertificate 388481 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv607]) (by decide +kernel)
def pv388481 : PrimeValue := ⟨388481, pr388481⟩
private theorem pr388499 : PrimeCertificate 388499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv17659]) (by decide +kernel)
def pv388499 : PrimeValue := ⟨388499, pr388499⟩
private theorem pr388529 : PrimeCertificate 388529 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv3469]) (by decide +kernel)
def pv388529 : PrimeValue := ⟨388529, pr388529⟩
private theorem pr388711 : PrimeCertificate 388711 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv617]) (by decide +kernel)
def pv388711 : PrimeValue := ⟨388711, pr388711⟩
private theorem pr388823 : PrimeCertificate 388823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv27773]) (by decide +kernel)
def pv388823 : PrimeValue := ⟨388823, pr388823⟩
private theorem pr388879 : PrimeCertificate 388879 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv47,pv197]) (by decide +kernel)
def pv388879 : PrimeValue := ⟨388879, pr388879⟩
private theorem pr388963 : PrimeCertificate 388963 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv388963 : PrimeValue := ⟨388963, pr388963⟩
private theorem pr388991 : PrimeCertificate 388991 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv5557]) (by decide +kernel)
def pv388991 : PrimeValue := ⟨388991, pr388991⟩
private theorem pr389083 : PrimeCertificate 389083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv3413]) (by decide +kernel)
def pv389083 : PrimeValue := ⟨389083, pr389083⟩
private theorem pr389231 : PrimeCertificate 389231 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv38923]) (by decide +kernel)
def pv389231 : PrimeValue := ⟨389231, pr389231⟩
private theorem pr389539 : PrimeCertificate 389539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv19,pv67]) (by decide +kernel)
def pv389539 : PrimeValue := ⟨389539, pr389539⟩
private theorem pr389569 : PrimeCertificate 389569 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv2029]) (by decide +kernel)
def pv389569 : PrimeValue := ⟨389569, pr389569⟩
private theorem pr389621 : PrimeCertificate 389621 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv11,pv23]) (by decide +kernel)
def pv389621 : PrimeValue := ⟨389621, pr389621⟩
private theorem pr389761 : PrimeCertificate 389761 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv29]) (by decide +kernel)
def pv389761 : PrimeValue := ⟨389761, pr389761⟩
private theorem pr389903 : PrimeCertificate 389903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv137,pv1423]) (by decide +kernel)
def pv389903 : PrimeValue := ⟨389903, pr389903⟩
private theorem pr389941 : PrimeCertificate 389941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv67,pv97]) (by decide +kernel)
def pv389941 : PrimeValue := ⟨389941, pr389941⟩
private theorem pr389989 : PrimeCertificate 389989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv157]) (by decide +kernel)
def pv389989 : PrimeValue := ⟨389989, pr389989⟩
private theorem pr390083 : PrimeCertificate 390083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv17,pv149]) (by decide +kernel)
def pv390083 : PrimeValue := ⟨390083, pr390083⟩
private theorem pr390109 : PrimeCertificate 390109 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv19,pv29,pv59]) (by decide +kernel)
def pv390109 : PrimeValue := ⟨390109, pr390109⟩
private theorem pr390151 : PrimeCertificate 390151 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv390151 : PrimeValue := ⟨390151, pr390151⟩
private theorem pr390157 : PrimeCertificate 390157 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv41,pv61]) (by decide +kernel)
def pv390157 : PrimeValue := ⟨390157, pr390157⟩
private theorem pr390263 : PrimeCertificate 390263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv195131]) (by decide +kernel)
def pv390263 : PrimeValue := ⟨390263, pr390263⟩
private theorem pr390307 : PrimeCertificate 390307 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv9293]) (by decide +kernel)
def pv390307 : PrimeValue := ⟨390307, pr390307⟩
private theorem pr390343 : PrimeCertificate 390343 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv67,pv971]) (by decide +kernel)
def pv390343 : PrimeValue := ⟨390343, pr390343⟩
private theorem pr390449 : PrimeCertificate 390449 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv1061]) (by decide +kernel)
def pv390449 : PrimeValue := ⟨390449, pr390449⟩
private theorem pr390491 : PrimeCertificate 390491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv2297]) (by decide +kernel)
def pv390491 : PrimeValue := ⟨390491, pr390491⟩
private theorem pr390553 : PrimeCertificate 390553 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv16273]) (by decide +kernel)
def pv390553 : PrimeValue := ⟨390553, pr390553⟩
private theorem pr390673 : PrimeCertificate 390673 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2713]) (by decide +kernel)
def pv390673 : PrimeValue := ⟨390673, pr390673⟩
private theorem pr390703 : PrimeCertificate 390703 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv5009]) (by decide +kernel)
def pv390703 : PrimeValue := ⟨390703, pr390703⟩
private theorem pr390781 : PrimeCertificate 390781 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv13,pv167]) (by decide +kernel)
def pv390781 : PrimeValue := ⟨390781, pr390781⟩
private theorem pr390829 : PrimeCertificate 390829 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv32569]) (by decide +kernel)
def pv390829 : PrimeValue := ⟨390829, pr390829⟩
private theorem pr390877 : PrimeCertificate 390877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv32573]) (by decide +kernel)
def pv390877 : PrimeValue := ⟨390877, pr390877⟩
private theorem pr390953 : PrimeCertificate 390953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv48869]) (by decide +kernel)
def pv390953 : PrimeValue := ⟨390953, pr390953⟩
private theorem pr390991 : PrimeCertificate 390991 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv13033]) (by decide +kernel)
def pv390991 : PrimeValue := ⟨390991, pr390991⟩
private theorem pr391063 : PrimeCertificate 391063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv9311]) (by decide +kernel)
def pv391063 : PrimeValue := ⟨391063, pr391063⟩
private theorem pr391231 : PrimeCertificate 391231 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv23]) (by decide +kernel)
def pv391231 : PrimeValue := ⟨391231, pr391231⟩
private theorem pr391273 : PrimeCertificate 391273 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv7,pv17,pv137]) (by decide +kernel)
def pv391273 : PrimeValue := ⟨391273, pr391273⟩
private theorem pr391351 : PrimeCertificate 391351 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv2609]) (by decide +kernel)
def pv391351 : PrimeValue := ⟨391351, pr391351⟩
private theorem pr391399 : PrimeCertificate 391399 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv9319]) (by decide +kernel)
def pv391399 : PrimeValue := ⟨391399, pr391399⟩
private theorem pr391441 : PrimeCertificate 391441 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv5,pv7,pv233]) (by decide +kernel)
def pv391441 : PrimeValue := ⟨391441, pr391441⟩
private theorem pr391537 : PrimeCertificate 391537 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2719]) (by decide +kernel)
def pv391537 : PrimeValue := ⟨391537, pr391537⟩
private theorem pr391627 : PrimeCertificate 391627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv21757]) (by decide +kernel)
def pv391627 : PrimeValue := ⟨391627, pr391627⟩
private theorem pr391639 : PrimeCertificate 391639 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13,pv5021]) (by decide +kernel)
def pv391639 : PrimeValue := ⟨391639, pr391639⟩
private theorem pr391693 : PrimeCertificate 391693 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv4663]) (by decide +kernel)
def pv391693 : PrimeValue := ⟨391693, pr391693⟩
private theorem pr391801 : PrimeCertificate 391801 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv653]) (by decide +kernel)
def pv391801 : PrimeValue := ⟨391801, pr391801⟩
private theorem pr391861 : PrimeCertificate 391861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv311]) (by decide +kernel)
def pv391861 : PrimeValue := ⟨391861, pr391861⟩
private theorem pr391879 : PrimeCertificate 391879 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41,pv59]) (by decide +kernel)
def pv391879 : PrimeValue := ⟨391879, pr391879⟩
private theorem pr391921 : PrimeCertificate 391921 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv23,pv71]) (by decide +kernel)
def pv391921 : PrimeValue := ⟨391921, pr391921⟩
private theorem pr391961 : PrimeCertificate 391961 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv41,pv239]) (by decide +kernel)
def pv391961 : PrimeValue := ⟨391961, pr391961⟩
private theorem pr392069 : PrimeCertificate 392069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv98017]) (by decide +kernel)
def pv392069 : PrimeValue := ⟨392069, pr392069⟩
private theorem pr392269 : PrimeCertificate 392269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv97,pv337]) (by decide +kernel)
def pv392269 : PrimeValue := ⟨392269, pr392269⟩
private theorem pr392279 : PrimeCertificate 392279 :=
  certifyPrime (q := pv19) (ls := [pv2,pv196139]) (by decide +kernel)
def pv392279 : PrimeValue := ⟨392279, pr392279⟩
private theorem pr392473 : PrimeCertificate 392473 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv79]) (by decide +kernel)
def pv392473 : PrimeValue := ⟨392473, pr392473⟩
private theorem pr392519 : PrimeCertificate 392519 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv23,pv53]) (by decide +kernel)
def pv392519 : PrimeValue := ⟨392519, pr392519⟩
private theorem pr392531 : PrimeCertificate 392531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv2309]) (by decide +kernel)
def pv392531 : PrimeValue := ⟨392531, pr392531⟩
private theorem pr392569 : PrimeCertificate 392569 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv11,pv1487]) (by decide +kernel)
def pv392569 : PrimeValue := ⟨392569, pr392569⟩
private theorem pr392629 : PrimeCertificate 392629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv32719]) (by decide +kernel)
def pv392629 : PrimeValue := ⟨392629, pr392629⟩
private theorem pr392761 : PrimeCertificate 392761 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv1091]) (by decide +kernel)
def pv392761 : PrimeValue := ⟨392761, pr392761⟩
private theorem pr392893 : PrimeCertificate 392893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv1129]) (by decide +kernel)
def pv392893 : PrimeValue := ⟨392893, pr392893⟩
private theorem pr392923 : PrimeCertificate 392923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv83,pv263]) (by decide +kernel)
def pv392923 : PrimeValue := ⟨392923, pr392923⟩
private theorem pr392929 : PrimeCertificate 392929 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv4093]) (by decide +kernel)
def pv392929 : PrimeValue := ⟨392929, pr392929⟩
private theorem pr392983 : PrimeCertificate 392983 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv65497]) (by decide +kernel)
def pv392983 : PrimeValue := ⟨392983, pr392983⟩
private theorem pr393031 : PrimeCertificate 393031 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv397]) (by decide +kernel)
def pv393031 : PrimeValue := ⟨393031, pr393031⟩
private theorem pr393059 : PrimeCertificate 393059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59,pv3331]) (by decide +kernel)
def pv393059 : PrimeValue := ⟨393059, pr393059⟩
private theorem pr393079 : PrimeCertificate 393079 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv191]) (by decide +kernel)
def pv393079 : PrimeValue := ⟨393079, pr393079⟩
private theorem pr393301 : PrimeCertificate 393301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv23]) (by decide +kernel)
def pv393301 : PrimeValue := ⟨393301, pr393301⟩
private theorem pr393331 : PrimeCertificate 393331 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv1873]) (by decide +kernel)
def pv393331 : PrimeValue := ⟨393331, pr393331⟩
private theorem pr393373 : PrimeCertificate 393373 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv223]) (by decide +kernel)
def pv393373 : PrimeValue := ⟨393373, pr393373⟩
private theorem pr393473 : PrimeCertificate 393473 :=
  certifyPrime (q := pv7) (ls := [pv2,pv29,pv53]) (by decide +kernel)
def pv393473 : PrimeValue := ⟨393473, pr393473⟩
private theorem pr393541 : PrimeCertificate 393541 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv937]) (by decide +kernel)
def pv393541 : PrimeValue := ⟨393541, pr393541⟩
private theorem pr393671 : PrimeCertificate 393671 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv39367]) (by decide +kernel)
def pv393671 : PrimeValue := ⟨393671, pr393671⟩
private theorem pr393709 : PrimeCertificate 393709 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv43,pv109]) (by decide +kernel)
def pv393709 : PrimeValue := ⟨393709, pr393709⟩
private theorem pr393721 : PrimeCertificate 393721 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv17,pv193]) (by decide +kernel)
def pv393721 : PrimeValue := ⟨393721, pr393721⟩
private theorem pr393847 : PrimeCertificate 393847 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv41,pv1601]) (by decide +kernel)
def pv393847 : PrimeValue := ⟨393847, pr393847⟩
private theorem pr393853 : PrimeCertificate 393853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv1427]) (by decide +kernel)
def pv393853 : PrimeValue := ⟨393853, pr393853⟩
private theorem pr393961 : PrimeCertificate 393961 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv7,pv67]) (by decide +kernel)
def pv393961 : PrimeValue := ⟨393961, pr393961⟩
private theorem pr394063 : PrimeCertificate 394063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv65677]) (by decide +kernel)
def pv394063 : PrimeValue := ⟨394063, pr394063⟩
private theorem pr394099 : PrimeCertificate 394099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv3457]) (by decide +kernel)
def pv394099 : PrimeValue := ⟨394099, pr394099⟩
private theorem pr394259 : PrimeCertificate 394259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv6359]) (by decide +kernel)
def pv394259 : PrimeValue := ⟨394259, pr394259⟩
private theorem pr394369 : PrimeCertificate 394369 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv79]) (by decide +kernel)
def pv394369 : PrimeValue := ⟨394369, pr394369⟩
private theorem pr394529 : PrimeCertificate 394529 :=
  certifyPrime (q := pv3) (ls := [pv2,pv12329]) (by decide +kernel)
def pv394529 : PrimeValue := ⟨394529, pr394529⟩
private theorem pr394549 : PrimeCertificate 394549 :=
  certifyPrime (q := pv83) (ls := [pv2,pv3,pv7,pv11,pv61]) (by decide +kernel)
def pv394549 : PrimeValue := ⟨394549, pr394549⟩
private theorem pr394579 : PrimeCertificate 394579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7307]) (by decide +kernel)
def pv394579 : PrimeValue := ⟨394579, pr394579⟩
private theorem pr394631 : PrimeCertificate 394631 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv19,pv31,pv67]) (by decide +kernel)
def pv394631 : PrimeValue := ⟨394631, pr394631⟩
private theorem pr394699 : PrimeCertificate 394699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv157,pv419]) (by decide +kernel)
def pv394699 : PrimeValue := ⟨394699, pr394699⟩
private theorem pr394729 : PrimeCertificate 394729 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv16447]) (by decide +kernel)
def pv394729 : PrimeValue := ⟨394729, pr394729⟩
private theorem pr394987 : PrimeCertificate 394987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv65831]) (by decide +kernel)
def pv394987 : PrimeValue := ⟨394987, pr394987⟩
private theorem pr395039 : PrimeCertificate 395039 :=
  certifyPrime (q := pv43) (ls := [pv2,pv7,pv29,pv139]) (by decide +kernel)
def pv395039 : PrimeValue := ⟨395039, pr395039⟩
private theorem pr395111 : PrimeCertificate 395111 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv39511]) (by decide +kernel)
def pv395111 : PrimeValue := ⟨395111, pr395111⟩
private theorem pr395113 : PrimeCertificate 395113 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv101,pv163]) (by decide +kernel)
def pv395113 : PrimeValue := ⟨395113, pr395113⟩
private theorem pr395137 : PrimeCertificate 395137 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv395137 : PrimeValue := ⟨395137, pr395137⟩
private theorem pr395251 : PrimeCertificate 395251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv31]) (by decide +kernel)
def pv395251 : PrimeValue := ⟨395251, pr395251⟩
private theorem pr395429 : PrimeCertificate 395429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv19,pv43]) (by decide +kernel)
def pv395429 : PrimeValue := ⟨395429, pr395429⟩
private theorem pr395533 : PrimeCertificate 395533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv10987]) (by decide +kernel)
def pv395533 : PrimeValue := ⟨395533, pr395533⟩
private theorem pr395701 : PrimeCertificate 395701 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv1319]) (by decide +kernel)
def pv395701 : PrimeValue := ⟨395701, pr395701⟩
private theorem pr395767 : PrimeCertificate 395767 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv349]) (by decide +kernel)
def pv395767 : PrimeValue := ⟨395767, pr395767⟩
private theorem pr395803 : PrimeCertificate 395803 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv1999]) (by decide +kernel)
def pv395803 : PrimeValue := ⟨395803, pr395803⟩
private theorem pr395873 : PrimeCertificate 395873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv89,pv139]) (by decide +kernel)
def pv395873 : PrimeValue := ⟨395873, pr395873⟩
private theorem pr395921 : PrimeCertificate 395921 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv101]) (by decide +kernel)
def pv395921 : PrimeValue := ⟨395921, pr395921⟩
private theorem pr396043 : PrimeCertificate 396043 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv149,pv443]) (by decide +kernel)
def pv396043 : PrimeValue := ⟨396043, pr396043⟩
private theorem pr396061 : PrimeCertificate 396061 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv7,pv23,pv41]) (by decide +kernel)
def pv396061 : PrimeValue := ⟨396061, pr396061⟩
private theorem pr396079 : PrimeCertificate 396079 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv251,pv263]) (by decide +kernel)
def pv396079 : PrimeValue := ⟨396079, pr396079⟩
private theorem pr396119 : PrimeCertificate 396119 :=
  certifyPrime (q := pv19) (ls := [pv2,pv31,pv6389]) (by decide +kernel)
def pv396119 : PrimeValue := ⟨396119, pr396119⟩
private theorem pr396203 : PrimeCertificate 396203 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv43,pv271]) (by decide +kernel)
def pv396203 : PrimeValue := ⟨396203, pr396203⟩
private theorem pr396247 : PrimeCertificate 396247 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv66041]) (by decide +kernel)
def pv396247 : PrimeValue := ⟨396247, pr396247⟩
private theorem pr396259 : PrimeCertificate 396259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv211,pv313]) (by decide +kernel)
def pv396259 : PrimeValue := ⟨396259, pr396259⟩
private theorem pr396269 : PrimeCertificate 396269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv157,pv631]) (by decide +kernel)
def pv396269 : PrimeValue := ⟨396269, pr396269⟩
private theorem pr396563 : PrimeCertificate 396563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv198281]) (by decide +kernel)
def pv396563 : PrimeValue := ⟨396563, pr396563⟩
private theorem pr396619 : PrimeCertificate 396619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv66103]) (by decide +kernel)
def pv396619 : PrimeValue := ⟨396619, pr396619⟩
private theorem pr396623 : PrimeCertificate 396623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv61,pv3251]) (by decide +kernel)
def pv396623 : PrimeValue := ⟨396623, pr396623⟩
private theorem pr396919 : PrimeCertificate 396919 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv22051]) (by decide +kernel)
def pv396919 : PrimeValue := ⟨396919, pr396919⟩
private theorem pr397027 : PrimeCertificate 397027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv23,pv137]) (by decide +kernel)
def pv397027 : PrimeValue := ⟨397027, pr397027⟩
private theorem pr397099 : PrimeCertificate 397099 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv1697]) (by decide +kernel)
def pv397099 : PrimeValue := ⟨397099, pr397099⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
