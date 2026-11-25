/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table131
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table131.pv808751
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table013
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table018
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table023
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table031
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table032
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table048
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table049
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table100
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table101

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr808751 : PrimeCertificate 808751 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv647]) (by decide +kernel)
def pv808751 : PrimeValue := ⟨808751, pr808751⟩
private theorem pr808777 : PrimeCertificate 808777 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv47,pv239]) (by decide +kernel)
def pv808777 : PrimeValue := ⟨808777, pr808777⟩
private theorem pr808957 : PrimeCertificate 808957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv977]) (by decide +kernel)
def pv808957 : PrimeValue := ⟨808957, pr808957⟩
private theorem pr808961 : PrimeCertificate 808961 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv79]) (by decide +kernel)
def pv808961 : PrimeValue := ⟨808961, pr808961⟩
private theorem pr809093 : PrimeCertificate 809093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67,pv3019]) (by decide +kernel)
def pv809093 : PrimeValue := ⟨809093, pr809093⟩
private theorem pr809173 : PrimeCertificate 809173 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv19]) (by decide +kernel)
def pv809173 : PrimeValue := ⟨809173, pr809173⟩
private theorem pr809239 : PrimeCertificate 809239 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv134873]) (by decide +kernel)
def pv809239 : PrimeValue := ⟨809239, pr809239⟩
private theorem pr809269 : PrimeCertificate 809269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv3967]) (by decide +kernel)
def pv809269 : PrimeValue := ⟨809269, pr809269⟩
private theorem pr809309 : PrimeCertificate 809309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv202327]) (by decide +kernel)
def pv809309 : PrimeValue := ⟨809309, pr809309⟩
private theorem pr809339 : PrimeCertificate 809339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv10937]) (by decide +kernel)
def pv809339 : PrimeValue := ⟨809339, pr809339⟩
private theorem pr809579 : PrimeCertificate 809579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv751]) (by decide +kernel)
def pv809579 : PrimeValue := ⟨809579, pr809579⟩
private theorem pr809587 : PrimeCertificate 809587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv1097]) (by decide +kernel)
def pv809587 : PrimeValue := ⟨809587, pr809587⟩
private theorem pr809603 : PrimeCertificate 809603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv367,pv1103]) (by decide +kernel)
def pv809603 : PrimeValue := ⟨809603, pr809603⟩
private theorem pr809801 : PrimeCertificate 809801 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv4049]) (by decide +kernel)
def pv809801 : PrimeValue := ⟨809801, pr809801⟩
private theorem pr809827 : PrimeCertificate 809827 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv71,pv1901]) (by decide +kernel)
def pv809827 : PrimeValue := ⟨809827, pr809827⟩
private theorem pr809843 : PrimeCertificate 809843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv131,pv281]) (by decide +kernel)
def pv809843 : PrimeValue := ⟨809843, pr809843⟩
private theorem pr809917 : PrimeCertificate 809917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv67493]) (by decide +kernel)
def pv809917 : PrimeValue := ⟨809917, pr809917⟩
private theorem pr809993 : PrimeCertificate 809993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv103,pv983]) (by decide +kernel)
def pv809993 : PrimeValue := ⟨809993, pr809993⟩
private theorem pr810049 : PrimeCertificate 810049 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv4219]) (by decide +kernel)
def pv810049 : PrimeValue := ⟨810049, pr810049⟩
private theorem pr810053 : PrimeCertificate 810053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv3821]) (by decide +kernel)
def pv810053 : PrimeValue := ⟨810053, pr810053⟩
private theorem pr810269 : PrimeCertificate 810269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv202567]) (by decide +kernel)
def pv810269 : PrimeValue := ⟨810269, pr810269⟩
private theorem pr810349 : PrimeCertificate 810349 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv11,pv877]) (by decide +kernel)
def pv810349 : PrimeValue := ⟨810349, pr810349⟩
private theorem pr810401 : PrimeCertificate 810401 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1013]) (by decide +kernel)
def pv810401 : PrimeValue := ⟨810401, pr810401⟩
private theorem pr810443 : PrimeCertificate 810443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv405221]) (by decide +kernel)
def pv810443 : PrimeValue := ⟨810443, pr810443⟩
private theorem pr810539 : PrimeCertificate 810539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv405269]) (by decide +kernel)
def pv810539 : PrimeValue := ⟨810539, pr810539⟩
private theorem pr810581 : PrimeCertificate 810581 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv40529]) (by decide +kernel)
def pv810581 : PrimeValue := ⟨810581, pr810581⟩
private theorem pr810643 : PrimeCertificate 810643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv19301]) (by decide +kernel)
def pv810643 : PrimeValue := ⟨810643, pr810643⟩
private theorem pr810791 : PrimeCertificate 810791 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv89,pv911]) (by decide +kernel)
def pv810791 : PrimeValue := ⟨810791, pr810791⟩
private theorem pr810809 : PrimeCertificate 810809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43,pv2357]) (by decide +kernel)
def pv810809 : PrimeValue := ⟨810809, pr810809⟩
private theorem pr810839 : PrimeCertificate 810839 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv57917]) (by decide +kernel)
def pv810839 : PrimeValue := ⟨810839, pr810839⟩
private theorem pr810907 : PrimeCertificate 810907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv135151]) (by decide +kernel)
def pv810907 : PrimeValue := ⟨810907, pr810907⟩
private theorem pr810989 : PrimeCertificate 810989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv202747]) (by decide +kernel)
def pv810989 : PrimeValue := ⟨810989, pr810989⟩
private theorem pr811147 : PrimeCertificate 811147 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv31,pv89]) (by decide +kernel)
def pv811147 : PrimeValue := ⟨811147, pr811147⟩
private theorem pr811241 : PrimeCertificate 811241 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17,pv1193]) (by decide +kernel)
def pv811241 : PrimeValue := ⟨811241, pr811241⟩
private theorem pr811297 : PrimeCertificate 811297 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv313]) (by decide +kernel)
def pv811297 : PrimeValue := ⟨811297, pr811297⟩
private theorem pr811493 : PrimeCertificate 811493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv18443]) (by decide +kernel)
def pv811493 : PrimeValue := ⟨811493, pr811493⟩
private theorem pr811511 : PrimeCertificate 811511 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv11593]) (by decide +kernel)
def pv811511 : PrimeValue := ⟨811511, pr811511⟩
private theorem pr811519 : PrimeCertificate 811519 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31,pv4363]) (by decide +kernel)
def pv811519 : PrimeValue := ⟨811519, pr811519⟩
private theorem pr811523 : PrimeCertificate 811523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv199,pv2039]) (by decide +kernel)
def pv811523 : PrimeValue := ⟨811523, pr811523⟩
private theorem pr811553 : PrimeCertificate 811553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv3623]) (by decide +kernel)
def pv811553 : PrimeValue := ⟨811553, pr811553⟩
private theorem pr811649 : PrimeCertificate 811649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv373]) (by decide +kernel)
def pv811649 : PrimeValue := ⟨811649, pr811649⟩
private theorem pr811747 : PrimeCertificate 811747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv3469]) (by decide +kernel)
def pv811747 : PrimeValue := ⟨811747, pr811747⟩
private theorem pr811777 : PrimeCertificate 811777 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv151]) (by decide +kernel)
def pv811777 : PrimeValue := ⟨811777, pr811777⟩
private theorem pr811799 : PrimeCertificate 811799 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv31223]) (by decide +kernel)
def pv811799 : PrimeValue := ⟨811799, pr811799⟩
private theorem pr811897 : PrimeCertificate 811897 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv33829]) (by decide +kernel)
def pv811897 : PrimeValue := ⟨811897, pr811897⟩
private theorem pr811931 : PrimeCertificate 811931 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv1657]) (by decide +kernel)
def pv811931 : PrimeValue := ⟨811931, pr811931⟩
private theorem pr812137 : PrimeCertificate 812137 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv19,pv137]) (by decide +kernel)
def pv812137 : PrimeValue := ⟨812137, pr812137⟩
private theorem pr812527 : PrimeCertificate 812527 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv13,pv947]) (by decide +kernel)
def pv812527 : PrimeValue := ⟨812527, pr812527⟩
private theorem pr812849 : PrimeCertificate 812849 :=
  certifyPrime (q := pv3) (ls := [pv2,pv101,pv503]) (by decide +kernel)
def pv812849 : PrimeValue := ⟨812849, pr812849⟩
private theorem pr812921 : PrimeCertificate 812921 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv20323]) (by decide +kernel)
def pv812921 : PrimeValue := ⟨812921, pr812921⟩
private theorem pr812939 : PrimeCertificate 812939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv58067]) (by decide +kernel)
def pv812939 : PrimeValue := ⟨812939, pr812939⟩
private theorem pr812963 : PrimeCertificate 812963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv406481]) (by decide +kernel)
def pv812963 : PrimeValue := ⟨812963, pr812963⟩
private theorem pr813023 : PrimeCertificate 813023 :=
  certifyPrime (q := pv29) (ls := [pv2,pv7,pv58073]) (by decide +kernel)
def pv813023 : PrimeValue := ⟨813023, pr813023⟩
private theorem pr813041 : PrimeCertificate 813041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv10163]) (by decide +kernel)
def pv813041 : PrimeValue := ⟨813041, pr813041⟩
private theorem pr813133 : PrimeCertificate 813133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7529]) (by decide +kernel)
def pv813133 : PrimeValue := ⟨813133, pr813133⟩
private theorem pr813217 : PrimeCertificate 813217 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv43,pv197]) (by decide +kernel)
def pv813217 : PrimeValue := ⟨813217, pr813217⟩
private theorem pr813251 : PrimeCertificate 813251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv3253]) (by decide +kernel)
def pv813251 : PrimeValue := ⟨813251, pr813251⟩
private theorem pr813367 : PrimeCertificate 813367 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv73,pv619]) (by decide +kernel)
def pv813367 : PrimeValue := ⟨813367, pr813367⟩
private theorem pr813401 : PrimeCertificate 813401 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv83]) (by decide +kernel)
def pv813401 : PrimeValue := ⟨813401, pr813401⟩
private theorem pr813427 : PrimeCertificate 813427 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv135571]) (by decide +kernel)
def pv813427 : PrimeValue := ⟨813427, pr813427⟩
private theorem pr813443 : PrimeCertificate 813443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv97,pv599]) (by decide +kernel)
def pv813443 : PrimeValue := ⟨813443, pr813443⟩
private theorem pr813503 : PrimeCertificate 813503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv31,pv13121]) (by decide +kernel)
def pv813503 : PrimeValue := ⟨813503, pr813503⟩
private theorem pr813529 : PrimeCertificate 813529 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11299]) (by decide +kernel)
def pv813529 : PrimeValue := ⟨813529, pr813529⟩
private theorem pr813583 : PrimeCertificate 813583 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv587]) (by decide +kernel)
def pv813583 : PrimeValue := ⟨813583, pr813583⟩
private theorem pr813623 : PrimeCertificate 813623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv406811]) (by decide +kernel)
def pv813623 : PrimeValue := ⟨813623, pr813623⟩
private theorem pr813697 : PrimeCertificate 813697 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv163]) (by decide +kernel)
def pv813697 : PrimeValue := ⟨813697, pr813697⟩
private theorem pr813817 : PrimeCertificate 813817 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv89,pv127]) (by decide +kernel)
def pv813817 : PrimeValue := ⟨813817, pr813817⟩
private theorem pr813847 : PrimeCertificate 813847 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv19,pv59]) (by decide +kernel)
def pv813847 : PrimeValue := ⟨813847, pr813847⟩
private theorem pr813863 : PrimeCertificate 813863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv61,pv953]) (by decide +kernel)
def pv813863 : PrimeValue := ⟨813863, pr813863⟩
private theorem pr813971 : PrimeCertificate 813971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv3539]) (by decide +kernel)
def pv813971 : PrimeValue := ⟨813971, pr813971⟩
private theorem pr814031 : PrimeCertificate 814031 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv29,pv401]) (by decide +kernel)
def pv814031 : PrimeValue := ⟨814031, pr814031⟩
private theorem pr814139 : PrimeCertificate 814139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv173,pv181]) (by decide +kernel)
def pv814139 : PrimeValue := ⟨814139, pr814139⟩
private theorem pr814193 : PrimeCertificate 814193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv151,pv337]) (by decide +kernel)
def pv814193 : PrimeValue := ⟨814193, pr814193⟩
private theorem pr814279 : PrimeCertificate 814279 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv113,pv1201]) (by decide +kernel)
def pv814279 : PrimeValue := ⟨814279, pr814279⟩
private theorem pr814493 : PrimeCertificate 814493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv19,pv1531]) (by decide +kernel)
def pv814493 : PrimeValue := ⟨814493, pr814493⟩
private theorem pr814537 : PrimeCertificate 814537 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv419]) (by decide +kernel)
def pv814537 : PrimeValue := ⟨814537, pr814537⟩
private theorem pr814543 : PrimeCertificate 814543 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv135757]) (by decide +kernel)
def pv814543 : PrimeValue := ⟨814543, pr814543⟩
private theorem pr814559 : PrimeCertificate 814559 :=
  certifyPrime (q := pv7) (ls := [pv2,pv131,pv3109]) (by decide +kernel)
def pv814559 : PrimeValue := ⟨814559, pr814559⟩
private theorem pr814601 : PrimeCertificate 814601 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv4073]) (by decide +kernel)
def pv814601 : PrimeValue := ⟨814601, pr814601⟩
private theorem pr814603 : PrimeCertificate 814603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv137,pv991]) (by decide +kernel)
def pv814603 : PrimeValue := ⟨814603, pr814603⟩
private theorem pr814699 : PrimeCertificate 814699 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv47,pv107]) (by decide +kernel)
def pv814699 : PrimeValue := ⟨814699, pr814699⟩
private theorem pr814717 : PrimeCertificate 814717 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv53,pv61]) (by decide +kernel)
def pv814717 : PrimeValue := ⟨814717, pr814717⟩
private theorem pr814747 : PrimeCertificate 814747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv251,pv541]) (by decide +kernel)
def pv814747 : PrimeValue := ⟨814747, pr814747⟩
private theorem pr814799 : PrimeCertificate 814799 :=
  certifyPrime (q := pv13) (ls := [pv2,pv23,pv17713]) (by decide +kernel)
def pv814799 : PrimeValue := ⟨814799, pr814799⟩
private theorem pr814823 : PrimeCertificate 814823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv53,pv7687]) (by decide +kernel)
def pv814823 : PrimeValue := ⟨814823, pr814823⟩
private theorem pr814883 : PrimeCertificate 814883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv211,pv1931]) (by decide +kernel)
def pv814883 : PrimeValue := ⟨814883, pr814883⟩
private theorem pr814949 : PrimeCertificate 814949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv10723]) (by decide +kernel)
def pv814949 : PrimeValue := ⟨814949, pr814949⟩
private theorem pr814991 : PrimeCertificate 814991 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv31,pv239]) (by decide +kernel)
def pv814991 : PrimeValue := ⟨814991, pr814991⟩
private theorem pr815063 : PrimeCertificate 815063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv89,pv241]) (by decide +kernel)
def pv815063 : PrimeValue := ⟨815063, pr815063⟩
private theorem pr815123 : PrimeCertificate 815123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv67,pv79]) (by decide +kernel)
def pv815123 : PrimeValue := ⟨815123, pr815123⟩
private theorem pr815149 : PrimeCertificate 815149 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv22643]) (by decide +kernel)
def pv815149 : PrimeValue := ⟨815149, pr815149⟩
private theorem pr815231 : PrimeCertificate 815231 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv6271]) (by decide +kernel)
def pv815231 : PrimeValue := ⟨815231, pr815231⟩
private theorem pr815257 : PrimeCertificate 815257 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv67]) (by decide +kernel)
def pv815257 : PrimeValue := ⟨815257, pr815257⟩
private theorem pr815273 : PrimeCertificate 815273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv101,pv1009]) (by decide +kernel)
def pv815273 : PrimeValue := ⟨815273, pr815273⟩
private theorem pr815459 : PrimeCertificate 815459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv53,pv157]) (by decide +kernel)
def pv815459 : PrimeValue := ⟨815459, pr815459⟩
private theorem pr815471 : PrimeCertificate 815471 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv81547]) (by decide +kernel)
def pv815471 : PrimeValue := ⟨815471, pr815471⟩
private theorem pr815539 : PrimeCertificate 815539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv43,pv109]) (by decide +kernel)
def pv815539 : PrimeValue := ⟨815539, pr815539⟩
private theorem pr815569 : PrimeCertificate 815569 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv13,pv1307]) (by decide +kernel)
def pv815569 : PrimeValue := ⟨815569, pr815569⟩
private theorem pr815599 : PrimeCertificate 815599 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv6473]) (by decide +kernel)
def pv815599 : PrimeValue := ⟨815599, pr815599⟩
private theorem pr815621 : PrimeCertificate 815621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv3137]) (by decide +kernel)
def pv815621 : PrimeValue := ⟨815621, pr815621⟩
private theorem pr815653 : PrimeCertificate 815653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv139,pv163]) (by decide +kernel)
def pv815653 : PrimeValue := ⟨815653, pr815653⟩
private theorem pr815681 : PrimeCertificate 815681 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv2549]) (by decide +kernel)
def pv815681 : PrimeValue := ⟨815681, pr815681⟩
private theorem pr815809 : PrimeCertificate 815809 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv607]) (by decide +kernel)
def pv815809 : PrimeValue := ⟨815809, pr815809⟩
private theorem pr815819 : PrimeCertificate 815819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv9949]) (by decide +kernel)
def pv815819 : PrimeValue := ⟨815819, pr815819⟩
private theorem pr815891 : PrimeCertificate 815891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv83,pv983]) (by decide +kernel)
def pv815891 : PrimeValue := ⟨815891, pr815891⟩
private theorem pr815923 : PrimeCertificate 815923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv45329]) (by decide +kernel)
def pv815923 : PrimeValue := ⟨815923, pr815923⟩
private theorem pr815939 : PrimeCertificate 815939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv407969]) (by decide +kernel)
def pv815939 : PrimeValue := ⟨815939, pr815939⟩
private theorem pr815989 : PrimeCertificate 815989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53,pv1283]) (by decide +kernel)
def pv815989 : PrimeValue := ⟨815989, pr815989⟩
private theorem pr816019 : PrimeCertificate 816019 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv19429]) (by decide +kernel)
def pv816019 : PrimeValue := ⟨816019, pr816019⟩
private theorem pr816113 : PrimeCertificate 816113 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv4637]) (by decide +kernel)
def pv816113 : PrimeValue := ⟨816113, pr816113⟩
private theorem pr816133 : PrimeCertificate 816133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv2957]) (by decide +kernel)
def pv816133 : PrimeValue := ⟨816133, pr816133⟩
private theorem pr816191 : PrimeCertificate 816191 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv81619]) (by decide +kernel)
def pv816191 : PrimeValue := ⟨816191, pr816191⟩
private theorem pr816223 : PrimeCertificate 816223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv83,pv149]) (by decide +kernel)
def pv816223 : PrimeValue := ⟨816223, pr816223⟩
private theorem pr816239 : PrimeCertificate 816239 :=
  certifyPrime (q := pv7) (ls := [pv2,pv17,pv24007]) (by decide +kernel)
def pv816239 : PrimeValue := ⟨816239, pr816239⟩
private theorem pr816443 : PrimeCertificate 816443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv17,pv37,pv59]) (by decide +kernel)
def pv816443 : PrimeValue := ⟨816443, pr816443⟩
private theorem pr816469 : PrimeCertificate 816469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv3581]) (by decide +kernel)
def pv816469 : PrimeValue := ⟨816469, pr816469⟩
private theorem pr816521 : PrimeCertificate 816521 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv137,pv149]) (by decide +kernel)
def pv816521 : PrimeValue := ⟨816521, pr816521⟩
private theorem pr816547 : PrimeCertificate 816547 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv61,pv97]) (by decide +kernel)
def pv816547 : PrimeValue := ⟨816547, pr816547⟩
private theorem pr816593 : PrimeCertificate 816593 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv23,pv317]) (by decide +kernel)
def pv816593 : PrimeValue := ⟨816593, pr816593⟩
private theorem pr816649 : PrimeCertificate 816649 :=
  certifyPrime (q := pv59) (ls := [pv2,pv3,pv7,pv4861]) (by decide +kernel)
def pv816649 : PrimeValue := ⟨816649, pr816649⟩
private theorem pr816779 : PrimeCertificate 816779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv408389]) (by decide +kernel)
def pv816779 : PrimeValue := ⟨816779, pr816779⟩
private theorem pr816839 : PrimeCertificate 816839 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv107,pv347]) (by decide +kernel)
def pv816839 : PrimeValue := ⟨816839, pr816839⟩
private theorem pr816911 : PrimeCertificate 816911 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv151,pv541]) (by decide +kernel)
def pv816911 : PrimeValue := ⟨816911, pr816911⟩
private theorem pr817013 : PrimeCertificate 817013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv29179]) (by decide +kernel)
def pv817013 : PrimeValue := ⟨817013, pr817013⟩
private theorem pr817039 : PrimeCertificate 817039 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv19,pv2389]) (by decide +kernel)
def pv817039 : PrimeValue := ⟨817039, pr817039⟩
private theorem pr817049 : PrimeCertificate 817049 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41,pv47,pv53]) (by decide +kernel)
def pv817049 : PrimeValue := ⟨817049, pr817049⟩
private theorem pr817093 : PrimeCertificate 817093 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv22697]) (by decide +kernel)
def pv817093 : PrimeValue := ⟨817093, pr817093⟩
private theorem pr817123 : PrimeCertificate 817123 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv8011]) (by decide +kernel)
def pv817123 : PrimeValue := ⟨817123, pr817123⟩
private theorem pr817303 : PrimeCertificate 817303 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv136217]) (by decide +kernel)
def pv817303 : PrimeValue := ⟨817303, pr817303⟩
private theorem pr817409 : PrimeCertificate 817409 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv103]) (by decide +kernel)
def pv817409 : PrimeValue := ⟨817409, pr817409⟩
private theorem pr817723 : PrimeCertificate 817723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv797]) (by decide +kernel)
def pv817723 : PrimeValue := ⟨817723, pr817723⟩
private theorem pr817777 : PrimeCertificate 817777 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv631]) (by decide +kernel)
def pv817777 : PrimeValue := ⟨817777, pr817777⟩
private theorem pr817913 : PrimeCertificate 817913 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv5381]) (by decide +kernel)
def pv817913 : PrimeValue := ⟨817913, pr817913⟩
private theorem pr817933 : PrimeCertificate 817933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv68161]) (by decide +kernel)
def pv817933 : PrimeValue := ⟨817933, pr817933⟩
private theorem pr818017 : PrimeCertificate 818017 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv8521]) (by decide +kernel)
def pv818017 : PrimeValue := ⟨818017, pr818017⟩
private theorem pr818021 : PrimeCertificate 818021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv5843]) (by decide +kernel)
def pv818021 : PrimeValue := ⟨818021, pr818021⟩
private theorem pr818171 : PrimeCertificate 818171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv81817]) (by decide +kernel)
def pv818171 : PrimeValue := ⟨818171, pr818171⟩
private theorem pr818189 : PrimeCertificate 818189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv29221]) (by decide +kernel)
def pv818189 : PrimeValue := ⟨818189, pr818189⟩
private theorem pr818231 : PrimeCertificate 818231 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv11689]) (by decide +kernel)
def pv818231 : PrimeValue := ⟨818231, pr818231⟩
private theorem pr818309 : PrimeCertificate 818309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv149,pv1373]) (by decide +kernel)
def pv818309 : PrimeValue := ⟨818309, pr818309⟩
private theorem pr818383 : PrimeCertificate 818383 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv136397]) (by decide +kernel)
def pv818383 : PrimeValue := ⟨818383, pr818383⟩
private theorem pr818393 : PrimeCertificate 818393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv102299]) (by decide +kernel)
def pv818393 : PrimeValue := ⟨818393, pr818393⟩
private theorem pr818569 : PrimeCertificate 818569 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11369]) (by decide +kernel)
def pv818569 : PrimeValue := ⟨818569, pr818569⟩
private theorem pr818621 : PrimeCertificate 818621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv61]) (by decide +kernel)
def pv818621 : PrimeValue := ⟨818621, pr818621⟩
private theorem pr818659 : PrimeCertificate 818659 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv45481]) (by decide +kernel)
def pv818659 : PrimeValue := ⟨818659, pr818659⟩
private theorem pr818689 : PrimeCertificate 818689 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13,pv41]) (by decide +kernel)
def pv818689 : PrimeValue := ⟨818689, pr818689⟩
private theorem pr818819 : PrimeCertificate 818819 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv11,pv13,pv409]) (by decide +kernel)
def pv818819 : PrimeValue := ⟨818819, pr818819⟩
private theorem pr818827 : PrimeCertificate 818827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv136471]) (by decide +kernel)
def pv818827 : PrimeValue := ⟨818827, pr818827⟩
private theorem pr818963 : PrimeCertificate 818963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv271,pv1511]) (by decide +kernel)
def pv818963 : PrimeValue := ⟨818963, pr818963⟩
private theorem pr819029 : PrimeCertificate 819029 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv29251]) (by decide +kernel)
def pv819029 : PrimeValue := ⟨819029, pr819029⟩
private theorem pr819037 : PrimeCertificate 819037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv22751]) (by decide +kernel)
def pv819037 : PrimeValue := ⟨819037, pr819037⟩
private theorem pr819073 : PrimeCertificate 819073 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv79]) (by decide +kernel)
def pv819073 : PrimeValue := ⟨819073, pr819073⟩
private theorem pr819083 : PrimeCertificate 819083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv31,pv1201]) (by decide +kernel)
def pv819083 : PrimeValue := ⟨819083, pr819083⟩
private theorem pr819173 : PrimeCertificate 819173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv204793]) (by decide +kernel)
def pv819173 : PrimeValue := ⟨819173, pr819173⟩
private theorem pr819449 : PrimeCertificate 819449 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv14633]) (by decide +kernel)
def pv819449 : PrimeValue := ⟨819449, pr819449⟩
private theorem pr819457 : PrimeCertificate 819457 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv11,pv97]) (by decide +kernel)
def pv819457 : PrimeValue := ⟨819457, pr819457⟩
private theorem pr819463 : PrimeCertificate 819463 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv109,pv179]) (by decide +kernel)
def pv819463 : PrimeValue := ⟨819463, pr819463⟩
private theorem pr819473 : PrimeCertificate 819473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv51217]) (by decide +kernel)
def pv819473 : PrimeValue := ⟨819473, pr819473⟩
private theorem pr819487 : PrimeCertificate 819487 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv53,pv859]) (by decide +kernel)
def pv819487 : PrimeValue := ⟨819487, pr819487⟩
private theorem pr819491 : PrimeCertificate 819491 :=
  certifyPrime (q := pv37) (ls := [pv2,pv5,pv7,pv23,pv509]) (by decide +kernel)
def pv819491 : PrimeValue := ⟨819491, pr819491⟩
private theorem pr819509 : PrimeCertificate 819509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv41,pv263]) (by decide +kernel)
def pv819509 : PrimeValue := ⟨819509, pr819509⟩
private theorem pr819583 : PrimeCertificate 819583 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv5939]) (by decide +kernel)
def pv819583 : PrimeValue := ⟨819583, pr819583⟩
private theorem pr819619 : PrimeCertificate 819619 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv136603]) (by decide +kernel)
def pv819619 : PrimeValue := ⟨819619, pr819619⟩
private theorem pr819653 : PrimeCertificate 819653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv204913]) (by decide +kernel)
def pv819653 : PrimeValue := ⟨819653, pr819653⟩
private theorem pr819799 : PrimeCertificate 819799 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv131,pv149]) (by decide +kernel)
def pv819799 : PrimeValue := ⟨819799, pr819799⟩
private theorem pr819823 : PrimeCertificate 819823 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv139,pv983]) (by decide +kernel)
def pv819823 : PrimeValue := ⟨819823, pr819823⟩
private theorem pr819911 : PrimeCertificate 819911 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv13,pv17,pv53]) (by decide +kernel)
def pv819911 : PrimeValue := ⟨819911, pr819911⟩
private theorem pr820073 : PrimeCertificate 820073 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv9319]) (by decide +kernel)
def pv820073 : PrimeValue := ⟨820073, pr820073⟩
private theorem pr820093 : PrimeCertificate 820093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv751]) (by decide +kernel)
def pv820093 : PrimeValue := ⟨820093, pr820093⟩
private theorem pr820117 : PrimeCertificate 820117 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv11,pv19,pv109]) (by decide +kernel)
def pv820117 : PrimeValue := ⟨820117, pr820117⟩
private theorem pr820129 : PrimeCertificate 820129 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv8543]) (by decide +kernel)
def pv820129 : PrimeValue := ⟨820129, pr820129⟩
private theorem pr820133 : PrimeCertificate 820133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv205033]) (by decide +kernel)
def pv820133 : PrimeValue := ⟨820133, pr820133⟩
private theorem pr820223 : PrimeCertificate 820223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv31547]) (by decide +kernel)
def pv820223 : PrimeValue := ⟨820223, pr820223⟩
private theorem pr820273 : PrimeCertificate 820273 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv743]) (by decide +kernel)
def pv820273 : PrimeValue := ⟨820273, pr820273⟩
private theorem pr820331 : PrimeCertificate 820331 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv11719]) (by decide +kernel)
def pv820331 : PrimeValue := ⟨820331, pr820331⟩
private theorem pr820409 : PrimeCertificate 820409 :=
  certifyPrime (q := pv3) (ls := [pv2,pv102551]) (by decide +kernel)
def pv820409 : PrimeValue := ⟨820409, pr820409⟩
private theorem pr820609 : PrimeCertificate 820609 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv2137]) (by decide +kernel)
def pv820609 : PrimeValue := ⟨820609, pr820609⟩
private theorem pr820627 : PrimeCertificate 820627 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv233,pv587]) (by decide +kernel)
def pv820627 : PrimeValue := ⟨820627, pr820627⟩
private theorem pr820679 : PrimeCertificate 820679 :=
  certifyPrime (q := pv13) (ls := [pv2,pv410339]) (by decide +kernel)
def pv820679 : PrimeValue := ⟨820679, pr820679⟩
private theorem pr820723 : PrimeCertificate 820723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv19541]) (by decide +kernel)
def pv820723 : PrimeValue := ⟨820723, pr820723⟩
private theorem pr820759 : PrimeCertificate 820759 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv53,pv89]) (by decide +kernel)
def pv820759 : PrimeValue := ⟨820759, pr820759⟩
private theorem pr820793 : PrimeCertificate 820793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv14657]) (by decide +kernel)
def pv820793 : PrimeValue := ⟨820793, pr820793⟩
private theorem pr820837 : PrimeCertificate 820837 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv151]) (by decide +kernel)
def pv820837 : PrimeValue := ⟨820837, pr820837⟩
private theorem pr820873 : PrimeCertificate 820873 :=
  certifyPrime (q := pv59) (ls := [pv2,pv3,pv13,pv877]) (by decide +kernel)
def pv820873 : PrimeValue := ⟨820873, pr820873⟩
private theorem pr820957 : PrimeCertificate 820957 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv37,pv43]) (by decide +kernel)
def pv820957 : PrimeValue := ⟨820957, pr820957⟩
private theorem pr821039 : PrimeCertificate 821039 :=
  certifyPrime (q := pv7) (ls := [pv2,pv410519]) (by decide +kernel)
def pv821039 : PrimeValue := ⟨821039, pr821039⟩
private theorem pr821167 : PrimeCertificate 821167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv136861]) (by decide +kernel)
def pv821167 : PrimeValue := ⟨821167, pr821167⟩
private theorem pr821173 : PrimeCertificate 821173 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv6221]) (by decide +kernel)
def pv821173 : PrimeValue := ⟨821173, pr821173⟩
private theorem pr821377 : PrimeCertificate 821377 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv31]) (by decide +kernel)
def pv821377 : PrimeValue := ⟨821377, pr821377⟩
private theorem pr821459 : PrimeCertificate 821459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv37339]) (by decide +kernel)
def pv821459 : PrimeValue := ⟨821459, pr821459⟩
private theorem pr821519 : PrimeCertificate 821519 :=
  certifyPrime (q := pv17) (ls := [pv2,pv410759]) (by decide +kernel)
def pv821519 : PrimeValue := ⟨821519, pr821519⟩
private theorem pr821819 : PrimeCertificate 821819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv7753]) (by decide +kernel)
def pv821819 : PrimeValue := ⟨821819, pr821819⟩
private theorem pr821827 : PrimeCertificate 821827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv89]) (by decide +kernel)
def pv821827 : PrimeValue := ⟨821827, pr821827⟩
private theorem pr821857 : PrimeCertificate 821857 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv7,pv1223]) (by decide +kernel)
def pv821857 : PrimeValue := ⟨821857, pr821857⟩
private theorem pr821993 : PrimeCertificate 821993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv2777]) (by decide +kernel)
def pv821993 : PrimeValue := ⟨821993, pr821993⟩
private theorem pr822007 : PrimeCertificate 822007 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv45667]) (by decide +kernel)
def pv822007 : PrimeValue := ⟨822007, pr822007⟩
private theorem pr822013 : PrimeCertificate 822013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv68501]) (by decide +kernel)
def pv822013 : PrimeValue := ⟨822013, pr822013⟩
private theorem pr822067 : PrimeCertificate 822067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv23,pv37]) (by decide +kernel)
def pv822067 : PrimeValue := ⟨822067, pr822067⟩
private theorem pr822079 : PrimeCertificate 822079 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv109,pv419]) (by decide +kernel)
def pv822079 : PrimeValue := ⟨822079, pr822079⟩
private theorem pr822229 : PrimeCertificate 822229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv6229]) (by decide +kernel)
def pv822229 : PrimeValue := ⟨822229, pr822229⟩
private theorem pr822259 : PrimeCertificate 822259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv15227]) (by decide +kernel)
def pv822259 : PrimeValue := ⟨822259, pr822259⟩
private theorem pr822553 : PrimeCertificate 822553 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv34273]) (by decide +kernel)
def pv822553 : PrimeValue := ⟨822553, pr822553⟩
private theorem pr822683 : PrimeCertificate 822683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv58763]) (by decide +kernel)
def pv822683 : PrimeValue := ⟨822683, pr822683⟩
private theorem pr822697 : PrimeCertificate 822697 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv59,pv83]) (by decide +kernel)
def pv822697 : PrimeValue := ⟨822697, pr822697⟩
private theorem pr822743 : PrimeCertificate 822743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv411371]) (by decide +kernel)
def pv822743 : PrimeValue := ⟨822743, pr822743⟩
private theorem pr822803 : PrimeCertificate 822803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv31,pv577]) (by decide +kernel)
def pv822803 : PrimeValue := ⟨822803, pr822803⟩
private theorem pr822821 : PrimeCertificate 822821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41141]) (by decide +kernel)
def pv822821 : PrimeValue := ⟨822821, pr822821⟩
private theorem pr822823 : PrimeCertificate 822823 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv11,pv13,pv137]) (by decide +kernel)
def pv822823 : PrimeValue := ⟨822823, pr822823⟩
private theorem pr822989 : PrimeCertificate 822989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv6637]) (by decide +kernel)
def pv822989 : PrimeValue := ⟨822989, pr822989⟩
private theorem pr823243 : PrimeCertificate 823243 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv17,pv1153]) (by decide +kernel)
def pv823243 : PrimeValue := ⟨823243, pr823243⟩
private theorem pr823271 : PrimeCertificate 823271 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv19,pv619]) (by decide +kernel)
def pv823271 : PrimeValue := ⟨823271, pr823271⟩
private theorem pr823357 : PrimeCertificate 823357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv22871]) (by decide +kernel)
def pv823357 : PrimeValue := ⟨823357, pr823357⟩
private theorem pr823373 : PrimeCertificate 823373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv18713]) (by decide +kernel)
def pv823373 : PrimeValue := ⟨823373, pr823373⟩
private theorem pr823447 : PrimeCertificate 823447 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv17,pv23]) (by decide +kernel)
def pv823447 : PrimeValue := ⟨823447, pr823447⟩
private theorem pr823451 : PrimeCertificate 823451 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv43,pv383]) (by decide +kernel)
def pv823451 : PrimeValue := ⟨823451, pr823451⟩
private theorem pr823489 : PrimeCertificate 823489 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv4289]) (by decide +kernel)
def pv823489 : PrimeValue := ⟨823489, pr823489⟩
private theorem pr823519 : PrimeCertificate 823519 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv45751]) (by decide +kernel)
def pv823519 : PrimeValue := ⟨823519, pr823519⟩
private theorem pr823541 : PrimeCertificate 823541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41177]) (by decide +kernel)
def pv823541 : PrimeValue := ⟨823541, pr823541⟩
private theorem pr823573 : PrimeCertificate 823573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv22877]) (by decide +kernel)
def pv823573 : PrimeValue := ⟨823573, pr823573⟩
private theorem pr823703 : PrimeCertificate 823703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv37441]) (by decide +kernel)
def pv823703 : PrimeValue := ⟨823703, pr823703⟩
private theorem pr823729 : PrimeCertificate 823729 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv131]) (by decide +kernel)
def pv823729 : PrimeValue := ⟨823729, pr823729⟩
private theorem pr823747 : PrimeCertificate 823747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv1783]) (by decide +kernel)
def pv823747 : PrimeValue := ⟨823747, pr823747⟩
private theorem pr823799 : PrimeCertificate 823799 :=
  certifyPrime (q := pv7) (ls := [pv2,pv277,pv1487]) (by decide +kernel)
def pv823799 : PrimeValue := ⟨823799, pr823799⟩
private theorem pr823819 : PrimeCertificate 823819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv137303]) (by decide +kernel)
def pv823819 : PrimeValue := ⟨823819, pr823819⟩
private theorem pr824189 : PrimeCertificate 824189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv206047]) (by decide +kernel)
def pv824189 : PrimeValue := ⟨824189, pr824189⟩
private theorem pr824287 : PrimeCertificate 824287 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37,pv47,pv79]) (by decide +kernel)
def pv824287 : PrimeValue := ⟨824287, pr824287⟩
private theorem pr824459 : PrimeCertificate 824459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv17923]) (by decide +kernel)
def pv824459 : PrimeValue := ⟨824459, pr824459⟩
private theorem pr824497 : PrimeCertificate 824497 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv89,pv193]) (by decide +kernel)
def pv824497 : PrimeValue := ⟨824497, pr824497⟩
private theorem pr824501 : PrimeCertificate 824501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv97]) (by decide +kernel)
def pv824501 : PrimeValue := ⟨824501, pr824501⟩
private theorem pr824651 : PrimeCertificate 824651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv16493]) (by decide +kernel)
def pv824651 : PrimeValue := ⟨824651, pr824651⟩
private theorem pr824753 : PrimeCertificate 824753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv2713]) (by decide +kernel)
def pv824753 : PrimeValue := ⟨824753, pr824753⟩
private theorem pr824779 : PrimeCertificate 824779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv45821]) (by decide +kernel)
def pv824779 : PrimeValue := ⟨824779, pr824779⟩
private theorem pr824947 : PrimeCertificate 824947 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv137491]) (by decide +kernel)
def pv824947 : PrimeValue := ⟨824947, pr824947⟩
private theorem pr825007 : PrimeCertificate 825007 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv1511]) (by decide +kernel)
def pv825007 : PrimeValue := ⟨825007, pr825007⟩
private theorem pr825029 : PrimeCertificate 825029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv239,pv863]) (by decide +kernel)
def pv825029 : PrimeValue := ⟨825029, pr825029⟩
private theorem pr825131 : PrimeCertificate 825131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv109,pv757]) (by decide +kernel)
def pv825131 : PrimeValue := ⟨825131, pr825131⟩
private theorem pr825229 : PrimeCertificate 825229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv283]) (by decide +kernel)
def pv825229 : PrimeValue := ⟨825229, pr825229⟩
private theorem pr825247 : PrimeCertificate 825247 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv127]) (by decide +kernel)
def pv825247 : PrimeValue := ⟨825247, pr825247⟩
private theorem pr825259 : PrimeCertificate 825259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv401]) (by decide +kernel)
def pv825259 : PrimeValue := ⟨825259, pr825259⟩
private theorem pr825281 : PrimeCertificate 825281 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv2579]) (by decide +kernel)
def pv825281 : PrimeValue := ⟨825281, pr825281⟩
private theorem pr825329 : PrimeCertificate 825329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv7369]) (by decide +kernel)
def pv825329 : PrimeValue := ⟨825329, pr825329⟩
private theorem pr825479 : PrimeCertificate 825479 :=
  certifyPrime (q := pv7) (ls := [pv2,pv412739]) (by decide +kernel)
def pv825479 : PrimeValue := ⟨825479, pr825479⟩
private theorem pr825491 : PrimeCertificate 825491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv82549]) (by decide +kernel)
def pv825491 : PrimeValue := ⟨825491, pr825491⟩
private theorem pr825509 : PrimeCertificate 825509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv4391]) (by decide +kernel)
def pv825509 : PrimeValue := ⟨825509, pr825509⟩
private theorem pr825689 : PrimeCertificate 825689 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv3559]) (by decide +kernel)
def pv825689 : PrimeValue := ⟨825689, pr825689⟩
private theorem pr825883 : PrimeCertificate 825883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv59,pv2333]) (by decide +kernel)
def pv825883 : PrimeValue := ⟨825883, pr825883⟩
private theorem pr825889 : PrimeCertificate 825889 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv1229]) (by decide +kernel)
def pv825889 : PrimeValue := ⟨825889, pr825889⟩
private theorem pr825971 : PrimeCertificate 825971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv151,pv547]) (by decide +kernel)
def pv825971 : PrimeValue := ⟨825971, pr825971⟩
private theorem pr826019 : PrimeCertificate 826019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv413009]) (by decide +kernel)
def pv826019 : PrimeValue := ⟨826019, pr826019⟩
private theorem pr826069 : PrimeCertificate 826069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv41,pv73]) (by decide +kernel)
def pv826069 : PrimeValue := ⟨826069, pr826069⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
