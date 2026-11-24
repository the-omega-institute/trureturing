/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table201
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table201.pv630101
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table014
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table015
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table025
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table039
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table040
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table087
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table088

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr630101 : Nat.Prime 630101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv6301]) (by decide +kernel)
def pv630101 : PrimeValue := ⟨630101, pr630101⟩
private theorem pr630181 : Nat.Prime 630181 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv389]) (by decide +kernel)
def pv630181 : PrimeValue := ⟨630181, pr630181⟩
private theorem pr630263 : Nat.Prime 630263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv79,pv3989]) (by decide +kernel)
def pv630263 : PrimeValue := ⟨630263, pr630263⟩
private theorem pr630467 : Nat.Prime 630467 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv7331]) (by decide +kernel)
def pv630467 : PrimeValue := ⟨630467, pr630467⟩
private theorem pr630577 : Nat.Prime 630577 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29,pv151]) (by decide +kernel)
def pv630577 : PrimeValue := ⟨630577, pr630577⟩
private theorem pr630677 : Nat.Prime 630677 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv157669]) (by decide +kernel)
def pv630677 : PrimeValue := ⟨630677, pr630677⟩
private theorem pr630733 : Nat.Prime 630733 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv52561]) (by decide +kernel)
def pv630733 : PrimeValue := ⟨630733, pr630733⟩
private theorem pr630871 : Nat.Prime 630871 :=
  checkPrime_prime (q := pv47) (ls := [pv2,pv3,pv5,pv17,pv1237]) (by decide +kernel)
def pv630871 : PrimeValue := ⟨630871, pr630871⟩
private theorem pr631153 : Nat.Prime 631153 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv487]) (by decide +kernel)
def pv631153 : PrimeValue := ⟨631153, pr631153⟩
private theorem pr631187 : Nat.Prime 631187 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv315593]) (by decide +kernel)
def pv631187 : PrimeValue := ⟨631187, pr631187⟩
private theorem pr631307 : Nat.Prime 631307 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv24281]) (by decide +kernel)
def pv631307 : PrimeValue := ⟨631307, pr631307⟩
private theorem pr631577 : Nat.Prime 631577 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv7177]) (by decide +kernel)
def pv631577 : PrimeValue := ⟨631577, pr631577⟩
private theorem pr631643 : Nat.Prime 631643 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv28711]) (by decide +kernel)
def pv631643 : PrimeValue := ⟨631643, pr631643⟩
private theorem pr631843 : Nat.Prime 631843 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv31,pv43,pv79]) (by decide +kernel)
def pv631843 : PrimeValue := ⟨631843, pr631843⟩
private theorem pr631861 : Nat.Prime 631861 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv10531]) (by decide +kernel)
def pv631861 : PrimeValue := ⟨631861, pr631861⟩
private theorem pr631903 : Nat.Prime 631903 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv23,pv241]) (by decide +kernel)
def pv631903 : PrimeValue := ⟨631903, pr631903⟩
private theorem pr631913 : Nat.Prime 631913 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv78989]) (by decide +kernel)
def pv631913 : PrimeValue := ⟨631913, pr631913⟩
private theorem pr631927 : Nat.Prime 631927 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv35107]) (by decide +kernel)
def pv631927 : PrimeValue := ⟨631927, pr631927⟩
private theorem pr631993 : Nat.Prime 631993 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv1549]) (by decide +kernel)
def pv631993 : PrimeValue := ⟨631993, pr631993⟩
private theorem pr632081 : Nat.Prime 632081 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7901]) (by decide +kernel)
def pv632081 : PrimeValue := ⟨632081, pr632081⟩
private theorem pr632083 : Nat.Prime 632083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv61,pv157]) (by decide +kernel)
def pv632083 : PrimeValue := ⟨632083, pr632083⟩
private theorem pr632123 : Nat.Prime 632123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv113,pv2797]) (by decide +kernel)
def pv632123 : PrimeValue := ⟨632123, pr632123⟩
private theorem pr632147 : Nat.Prime 632147 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv316073]) (by decide +kernel)
def pv632147 : PrimeValue := ⟨632147, pr632147⟩
private theorem pr632251 : Nat.Prime 632251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv281]) (by decide +kernel)
def pv632251 : PrimeValue := ⟨632251, pr632251⟩
private theorem pr632347 : Nat.Prime 632347 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv11,pv13,pv67]) (by decide +kernel)
def pv632347 : PrimeValue := ⟨632347, pr632347⟩
private theorem pr632351 : Nat.Prime 632351 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv12647]) (by decide +kernel)
def pv632351 : PrimeValue := ⟨632351, pr632351⟩
private theorem pr632371 : Nat.Prime 632371 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv107,pv197]) (by decide +kernel)
def pv632371 : PrimeValue := ⟨632371, pr632371⟩
private theorem pr632483 : Nat.Prime 632483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv316241]) (by decide +kernel)
def pv632483 : PrimeValue := ⟨632483, pr632483⟩
private theorem pr632497 : Nat.Prime 632497 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13177]) (by decide +kernel)
def pv632497 : PrimeValue := ⟨632497, pr632497⟩
private theorem pr632501 : Nat.Prime 632501 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv11,pv23]) (by decide +kernel)
def pv632501 : PrimeValue := ⟨632501, pr632501⟩
private theorem pr632561 : Nat.Prime 632561 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7907]) (by decide +kernel)
def pv632561 : PrimeValue := ⟨632561, pr632561⟩
private theorem pr632713 : Nat.Prime 632713 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv41,pv643]) (by decide +kernel)
def pv632713 : PrimeValue := ⟨632713, pr632713⟩
private theorem pr632813 : Nat.Prime 632813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv281,pv563]) (by decide +kernel)
def pv632813 : PrimeValue := ⟨632813, pr632813⟩
private theorem pr632897 : Nat.Prime 632897 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv29,pv31]) (by decide +kernel)
def pv632897 : PrimeValue := ⟨632897, pr632897⟩
private theorem pr632923 : Nat.Prime 632923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv2851]) (by decide +kernel)
def pv632923 : PrimeValue := ⟨632923, pr632923⟩
private theorem pr632977 : Nat.Prime 632977 :=
  checkPrime_prime (q := pv53) (ls := [pv2,pv3,pv13187]) (by decide +kernel)
def pv632977 : PrimeValue := ⟨632977, pr632977⟩
private theorem pr633013 : Nat.Prime 633013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv29,pv107]) (by decide +kernel)
def pv633013 : PrimeValue := ⟨633013, pr633013⟩
private theorem pr633091 : Nat.Prime 633091 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv47,pv449]) (by decide +kernel)
def pv633091 : PrimeValue := ⟨633091, pr633091⟩
private theorem pr633377 : Nat.Prime 633377 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19793]) (by decide +kernel)
def pv633377 : PrimeValue := ⟨633377, pr633377⟩
private theorem pr633407 : Nat.Prime 633407 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv316703]) (by decide +kernel)
def pv633407 : PrimeValue := ⟨633407, pr633407⟩
private theorem pr633667 : Nat.Prime 633667 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv9601]) (by decide +kernel)
def pv633667 : PrimeValue := ⟨633667, pr633667⟩
private theorem pr633793 : Nat.Prime 633793 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv3301]) (by decide +kernel)
def pv633793 : PrimeValue := ⟨633793, pr633793⟩
private theorem pr633797 : Nat.Prime 633797 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv158449]) (by decide +kernel)
def pv633797 : PrimeValue := ⟨633797, pr633797⟩
private theorem pr633833 : Nat.Prime 633833 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv79229]) (by decide +kernel)
def pv633833 : PrimeValue := ⟨633833, pr633833⟩
private theorem pr633931 : Nat.Prime 633931 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv17,pv113]) (by decide +kernel)
def pv633931 : PrimeValue := ⟨633931, pr633931⟩
private theorem pr633937 : Nat.Prime 633937 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv47,pv281]) (by decide +kernel)
def pv633937 : PrimeValue := ⟨633937, pr633937⟩
private theorem pr633943 : Nat.Prime 633943 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv41,pv859]) (by decide +kernel)
def pv633943 : PrimeValue := ⟨633943, pr633943⟩
private theorem pr634031 : Nat.Prime 634031 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv19,pv47,pv71]) (by decide +kernel)
def pv634031 : PrimeValue := ⟨634031, pr634031⟩
private theorem pr634091 : Nat.Prime 634091 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv63409]) (by decide +kernel)
def pv634091 : PrimeValue := ⟨634091, pr634091⟩
private theorem pr634157 : Nat.Prime 634157 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv61,pv113]) (by decide +kernel)
def pv634157 : PrimeValue := ⟨634157, pr634157⟩
private theorem pr634177 : Nat.Prime 634177 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv367]) (by decide +kernel)
def pv634177 : PrimeValue := ⟨634177, pr634177⟩
private theorem pr634273 : Nat.Prime 634273 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv6607]) (by decide +kernel)
def pv634273 : PrimeValue := ⟨634273, pr634273⟩
private theorem pr634331 : Nat.Prime 634331 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv229,pv277]) (by decide +kernel)
def pv634331 : PrimeValue := ⟨634331, pr634331⟩
private theorem pr634531 : Nat.Prime 634531 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv13,pv1627]) (by decide +kernel)
def pv634531 : PrimeValue := ⟨634531, pr634531⟩
private theorem pr634651 : Nat.Prime 634651 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv4231]) (by decide +kernel)
def pv634651 : PrimeValue := ⟨634651, pr634651⟩
private theorem pr634807 : Nat.Prime 634807 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv35267]) (by decide +kernel)
def pv634807 : PrimeValue := ⟨634807, pr634807⟩
private theorem pr634861 : Nat.Prime 634861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv3527]) (by decide +kernel)
def pv634861 : PrimeValue := ⟨634861, pr634861⟩
private theorem pr634937 : Nat.Prime 634937 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv79367]) (by decide +kernel)
def pv634937 : PrimeValue := ⟨634937, pr634937⟩
private theorem pr635057 : Nat.Prime 635057 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv2089]) (by decide +kernel)
def pv635057 : PrimeValue := ⟨635057, pr635057⟩
private theorem pr635087 : Nat.Prime 635087 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv18679]) (by decide +kernel)
def pv635087 : PrimeValue := ⟨635087, pr635087⟩
private theorem pr635353 : Nat.Prime 635353 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv23,pv1151]) (by decide +kernel)
def pv635353 : PrimeValue := ⟨635353, pr635353⟩
private theorem pr635431 : Nat.Prime 635431 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv59,pv359]) (by decide +kernel)
def pv635431 : PrimeValue := ⟨635431, pr635431⟩
private theorem pr635441 : Nat.Prime 635441 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv13,pv47]) (by decide +kernel)
def pv635441 : PrimeValue := ⟨635441, pr635441⟩
private theorem pr635483 : Nat.Prime 635483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv317741]) (by decide +kernel)
def pv635483 : PrimeValue := ⟨635483, pr635483⟩
private theorem pr635563 : Nat.Prime 635563 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv31,pv67]) (by decide +kernel)
def pv635563 : PrimeValue := ⟨635563, pr635563⟩
private theorem pr635603 : Nat.Prime 635603 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv167,pv173]) (by decide +kernel)
def pv635603 : PrimeValue := ⟨635603, pr635603⟩
private theorem pr635711 : Nat.Prime 635711 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv151,pv421]) (by decide +kernel)
def pv635711 : PrimeValue := ⟨635711, pr635711⟩
private theorem pr635731 : Nat.Prime 635731 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv21191]) (by decide +kernel)
def pv635731 : PrimeValue := ⟨635731, pr635731⟩
private theorem pr635737 : Nat.Prime 635737 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv26489]) (by decide +kernel)
def pv635737 : PrimeValue := ⟨635737, pr635737⟩
private theorem pr635917 : Nat.Prime 635917 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv197,pv269]) (by decide +kernel)
def pv635917 : PrimeValue := ⟨635917, pr635917⟩
private theorem pr636017 : Nat.Prime 636017 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv127,pv313]) (by decide +kernel)
def pv636017 : PrimeValue := ⟨636017, pr636017⟩
private theorem pr636071 : Nat.Prime 636071 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv63607]) (by decide +kernel)
def pv636071 : PrimeValue := ⟨636071, pr636071⟩
private theorem pr636193 : Nat.Prime 636193 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv47]) (by decide +kernel)
def pv636193 : PrimeValue := ⟨636193, pr636193⟩
private theorem pr636241 : Nat.Prime 636241 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv11,pv241]) (by decide +kernel)
def pv636241 : PrimeValue := ⟨636241, pr636241⟩
private theorem pr636257 : Nat.Prime 636257 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv59,pv337]) (by decide +kernel)
def pv636257 : PrimeValue := ⟨636257, pr636257⟩
private theorem pr636263 : Nat.Prime 636263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv28921]) (by decide +kernel)
def pv636263 : PrimeValue := ⟨636263, pr636263⟩
private theorem pr636331 : Nat.Prime 636331 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv21211]) (by decide +kernel)
def pv636331 : PrimeValue := ⟨636331, pr636331⟩
private theorem pr636421 : Nat.Prime 636421 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv10607]) (by decide +kernel)
def pv636421 : PrimeValue := ⟨636421, pr636421⟩
private theorem pr636473 : Nat.Prime 636473 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv79559]) (by decide +kernel)
def pv636473 : PrimeValue := ⟨636473, pr636473⟩
private theorem pr636533 : Nat.Prime 636533 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv12241]) (by decide +kernel)
def pv636533 : PrimeValue := ⟨636533, pr636533⟩
private theorem pr636761 : Nat.Prime 636761 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv15919]) (by decide +kernel)
def pv636761 : PrimeValue := ⟨636761, pr636761⟩
private theorem pr636877 : Nat.Prime 636877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5897]) (by decide +kernel)
def pv636877 : PrimeValue := ⟨636877, pr636877⟩
private theorem pr636967 : Nat.Prime 636967 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv3217]) (by decide +kernel)
def pv636967 : PrimeValue := ⟨636967, pr636967⟩
private theorem pr637097 : Nat.Prime 637097 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv97,pv821]) (by decide +kernel)
def pv637097 : PrimeValue := ⟨637097, pr637097⟩
private theorem pr637201 : Nat.Prime 637201 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv59]) (by decide +kernel)
def pv637201 : PrimeValue := ⟨637201, pr637201⟩
private theorem pr637243 : Nat.Prime 637243 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv106207]) (by decide +kernel)
def pv637243 : PrimeValue := ⟨637243, pr637243⟩
private theorem pr637271 : Nat.Prime 637271 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv63727]) (by decide +kernel)
def pv637271 : PrimeValue := ⟨637271, pr637271⟩
private theorem pr637291 : Nat.Prime 637291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv73,pv97]) (by decide +kernel)
def pv637291 : PrimeValue := ⟨637291, pr637291⟩
private theorem pr637321 : Nat.Prime 637321 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv47,pv113]) (by decide +kernel)
def pv637321 : PrimeValue := ⟨637321, pr637321⟩
private theorem pr637447 : Nat.Prime 637447 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv131,pv811]) (by decide +kernel)
def pv637447 : PrimeValue := ⟨637447, pr637447⟩
private theorem pr637471 : Nat.Prime 637471 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv787]) (by decide +kernel)
def pv637471 : PrimeValue := ⟨637471, pr637471⟩
private theorem pr637513 : Nat.Prime 637513 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv101,pv263]) (by decide +kernel)
def pv637513 : PrimeValue := ⟨637513, pr637513⟩
private theorem pr637573 : Nat.Prime 637573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv61,pv67]) (by decide +kernel)
def pv637573 : PrimeValue := ⟨637573, pr637573⟩
private theorem pr637607 : Nat.Prime 637607 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv23,pv83,pv167]) (by decide +kernel)
def pv637607 : PrimeValue := ⟨637607, pr637607⟩
private theorem pr637787 : Nat.Prime 637787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv347,pv919]) (by decide +kernel)
def pv637787 : PrimeValue := ⟨637787, pr637787⟩
private theorem pr638063 : Nat.Prime 638063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv319031]) (by decide +kernel)
def pv638063 : PrimeValue := ⟨638063, pr638063⟩
private theorem pr638423 : Nat.Prime 638423 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv319211]) (by decide +kernel)
def pv638423 : PrimeValue := ⟨638423, pr638423⟩
private theorem pr638437 : Nat.Prime 638437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv83,pv641]) (by decide +kernel)
def pv638437 : PrimeValue := ⟨638437, pr638437⟩
private theorem pr638501 : Nat.Prime 638501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1277]) (by decide +kernel)
def pv638501 : PrimeValue := ⟨638501, pr638501⟩
private theorem pr638587 : Nat.Prime 638587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv2729]) (by decide +kernel)
def pv638587 : PrimeValue := ⟨638587, pr638587⟩
private theorem pr638621 : Nat.Prime 638621 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv5,pv37,pv863]) (by decide +kernel)
def pv638621 : PrimeValue := ⟨638621, pr638621⟩
private theorem pr638717 : Nat.Prime 638717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv71,pv173]) (by decide +kernel)
def pv638717 : PrimeValue := ⟨638717, pr638717⟩
private theorem pr638767 : Nat.Prime 638767 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv3943]) (by decide +kernel)
def pv638767 : PrimeValue := ⟨638767, pr638767⟩
private theorem pr638893 : Nat.Prime 638893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17747]) (by decide +kernel)
def pv638893 : PrimeValue := ⟨638893, pr638893⟩
private theorem pr639007 : Nat.Prime 639007 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv106501]) (by decide +kernel)
def pv639007 : PrimeValue := ⟨639007, pr639007⟩
private theorem pr639083 : Nat.Prime 639083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv319541]) (by decide +kernel)
def pv639083 : PrimeValue := ⟨639083, pr639083⟩
private theorem pr639091 : Nat.Prime 639091 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv263]) (by decide +kernel)
def pv639091 : PrimeValue := ⟨639091, pr639091⟩
private theorem pr639151 : Nat.Prime 639151 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv4261]) (by decide +kernel)
def pv639151 : PrimeValue := ⟨639151, pr639151⟩
private theorem pr639211 : Nat.Prime 639211 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv11,pv13,pv149]) (by decide +kernel)
def pv639211 : PrimeValue := ⟨639211, pr639211⟩
private theorem pr639371 : Nat.Prime 639371 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv3761]) (by decide +kernel)
def pv639371 : PrimeValue := ⟨639371, pr639371⟩
private theorem pr639517 : Nat.Prime 639517 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv137,pv389]) (by decide +kernel)
def pv639517 : PrimeValue := ⟨639517, pr639517⟩
private theorem pr639533 : Nat.Prime 639533 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv101,pv1583]) (by decide +kernel)
def pv639533 : PrimeValue := ⟨639533, pr639533⟩
private theorem pr639631 : Nat.Prime 639631 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv23,pv103]) (by decide +kernel)
def pv639631 : PrimeValue := ⟨639631, pr639631⟩
private theorem pr639671 : Nat.Prime 639671 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv47,pv1361]) (by decide +kernel)
def pv639671 : PrimeValue := ⟨639671, pr639671⟩
private theorem pr639697 : Nat.Prime 639697 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv13327]) (by decide +kernel)
def pv639697 : PrimeValue := ⟨639697, pr639697⟩
private theorem pr639937 : Nat.Prime 639937 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv101]) (by decide +kernel)
def pv639937 : PrimeValue := ⟨639937, pr639937⟩
private theorem pr640007 : Nat.Prime 640007 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv97,pv3299]) (by decide +kernel)
def pv640007 : PrimeValue := ⟨640007, pr640007⟩
private theorem pr640027 : Nat.Prime 640027 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv31,pv37]) (by decide +kernel)
def pv640027 : PrimeValue := ⟨640027, pr640027⟩
private theorem pr640043 : Nat.Prime 640043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv103,pv239]) (by decide +kernel)
def pv640043 : PrimeValue := ⟨640043, pr640043⟩
private theorem pr640223 : Nat.Prime 640223 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv29101]) (by decide +kernel)
def pv640223 : PrimeValue := ⟨640223, pr640223⟩
private theorem pr640261 : Nat.Prime 640261 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv3557]) (by decide +kernel)
def pv640261 : PrimeValue := ⟨640261, pr640261⟩
private theorem pr640267 : Nat.Prime 640267 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv89,pv109]) (by decide +kernel)
def pv640267 : PrimeValue := ⟨640267, pr640267⟩
private theorem pr640307 : Nat.Prime 640307 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv320153]) (by decide +kernel)
def pv640307 : PrimeValue := ⟨640307, pr640307⟩
private theorem pr640463 : Nat.Prime 640463 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv179,pv1789]) (by decide +kernel)
def pv640463 : PrimeValue := ⟨640463, pr640463⟩
private theorem pr640483 : Nat.Prime 640483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv106747]) (by decide +kernel)
def pv640483 : PrimeValue := ⟨640483, pr640483⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
