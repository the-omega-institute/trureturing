/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table064
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table064.pv192461
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table013
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table014
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table036
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table037

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr192461 : Nat.Prime 192461 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv9623]) (by decide +kernel)
def pv192461 : PrimeValue := ⟨192461, pr192461⟩
private theorem pr192463 : Nat.Prime 192463 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv32077]) (by decide +kernel)
def pv192463 : PrimeValue := ⟨192463, pr192463⟩
private theorem pr192499 : Nat.Prime 192499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv32083]) (by decide +kernel)
def pv192499 : PrimeValue := ⟨192499, pr192499⟩
private theorem pr192529 : Nat.Prime 192529 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv7,pv191]) (by decide +kernel)
def pv192529 : PrimeValue := ⟨192529, pr192529⟩
private theorem pr192539 : Nat.Prime 192539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv96269]) (by decide +kernel)
def pv192539 : PrimeValue := ⟨192539, pr192539⟩
private theorem pr192553 : Nat.Prime 192553 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv71,pv113]) (by decide +kernel)
def pv192553 : PrimeValue := ⟨192553, pr192553⟩
private theorem pr192571 : Nat.Prime 192571 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv131]) (by decide +kernel)
def pv192571 : PrimeValue := ⟨192571, pr192571⟩
private theorem pr192583 : Nat.Prime 192583 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv823]) (by decide +kernel)
def pv192583 : PrimeValue := ⟨192583, pr192583⟩
private theorem pr192587 : Nat.Prime 192587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv96293]) (by decide +kernel)
def pv192587 : PrimeValue := ⟨192587, pr192587⟩
private theorem pr192601 : Nat.Prime 192601 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv107]) (by decide +kernel)
def pv192601 : PrimeValue := ⟨192601, pr192601⟩
private theorem pr192611 : Nat.Prime 192611 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv11,pv17,pv103]) (by decide +kernel)
def pv192611 : PrimeValue := ⟨192611, pr192611⟩
private theorem pr192613 : Nat.Prime 192613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv2293]) (by decide +kernel)
def pv192613 : PrimeValue := ⟨192613, pr192613⟩
private theorem pr192617 : Nat.Prime 192617 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv24077]) (by decide +kernel)
def pv192617 : PrimeValue := ⟨192617, pr192617⟩
private theorem pr192629 : Nat.Prime 192629 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv48157]) (by decide +kernel)
def pv192629 : PrimeValue := ⟨192629, pr192629⟩
private theorem pr192637 : Nat.Prime 192637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5351]) (by decide +kernel)
def pv192637 : PrimeValue := ⟨192637, pr192637⟩
private theorem pr192667 : Nat.Prime 192667 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv163,pv197]) (by decide +kernel)
def pv192667 : PrimeValue := ⟨192667, pr192667⟩
private theorem pr192677 : Nat.Prime 192677 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv29,pv151]) (by decide +kernel)
def pv192677 : PrimeValue := ⟨192677, pr192677⟩
private theorem pr192697 : Nat.Prime 192697 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv31,pv37]) (by decide +kernel)
def pv192697 : PrimeValue := ⟨192697, pr192697⟩
private theorem pr192737 : Nat.Prime 192737 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv317]) (by decide +kernel)
def pv192737 : PrimeValue := ⟨192737, pr192737⟩
private theorem pr192757 : Nat.Prime 192757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv16063]) (by decide +kernel)
def pv192757 : PrimeValue := ⟨192757, pr192757⟩
private theorem pr192767 : Nat.Prime 192767 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv281]) (by decide +kernel)
def pv192767 : PrimeValue := ⟨192767, pr192767⟩
private theorem pr192781 : Nat.Prime 192781 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv17]) (by decide +kernel)
def pv192781 : PrimeValue := ⟨192781, pr192781⟩
private theorem pr192791 : Nat.Prime 192791 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv1483]) (by decide +kernel)
def pv192791 : PrimeValue := ⟨192791, pr192791⟩
private theorem pr192817 : Nat.Prime 192817 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv103]) (by decide +kernel)
def pv192817 : PrimeValue := ⟨192817, pr192817⟩
private theorem pr192847 : Nat.Prime 192847 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv32141]) (by decide +kernel)
def pv192847 : PrimeValue := ⟨192847, pr192847⟩
private theorem pr192859 : Nat.Prime 192859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv32143]) (by decide +kernel)
def pv192859 : PrimeValue := ⟨192859, pr192859⟩
private theorem pr192877 : Nat.Prime 192877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv16073]) (by decide +kernel)
def pv192877 : PrimeValue := ⟨192877, pr192877⟩
private theorem pr192883 : Nat.Prime 192883 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv31,pv61]) (by decide +kernel)
def pv192883 : PrimeValue := ⟨192883, pr192883⟩
private theorem pr192887 : Nat.Prime 192887 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv96443]) (by decide +kernel)
def pv192887 : PrimeValue := ⟨192887, pr192887⟩
private theorem pr192917 : Nat.Prime 192917 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv2837]) (by decide +kernel)
def pv192917 : PrimeValue := ⟨192917, pr192917⟩
private theorem pr192923 : Nat.Prime 192923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv96461]) (by decide +kernel)
def pv192923 : PrimeValue := ⟨192923, pr192923⟩
private theorem pr192931 : Nat.Prime 192931 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv59,pv109]) (by decide +kernel)
def pv192931 : PrimeValue := ⟨192931, pr192931⟩
private theorem pr192961 : Nat.Prime 192961 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv67]) (by decide +kernel)
def pv192961 : PrimeValue := ⟨192961, pr192961⟩
private theorem pr192971 : Nat.Prime 192971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23,pv839]) (by decide +kernel)
def pv192971 : PrimeValue := ⟨192971, pr192971⟩
private theorem pr192977 : Nat.Prime 192977 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv1723]) (by decide +kernel)
def pv192977 : PrimeValue := ⟨192977, pr192977⟩
private theorem pr192979 : Nat.Prime 192979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv71,pv151]) (by decide +kernel)
def pv192979 : PrimeValue := ⟨192979, pr192979⟩
private theorem pr192991 : Nat.Prime 192991 :=
  checkPrime_prime (q := pv47) (ls := [pv2,pv3,pv5,pv7,pv919]) (by decide +kernel)
def pv192991 : PrimeValue := ⟨192991, pr192991⟩
private theorem pr193003 : Nat.Prime 193003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv1693]) (by decide +kernel)
def pv193003 : PrimeValue := ⟨193003, pr193003⟩
private theorem pr193031 : Nat.Prime 193031 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv97,pv199]) (by decide +kernel)
def pv193031 : PrimeValue := ⟨193031, pr193031⟩
private theorem pr193043 : Nat.Prime 193043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv263,pv367]) (by decide +kernel)
def pv193043 : PrimeValue := ⟨193043, pr193043⟩
private theorem pr193051 : Nat.Prime 193051 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv13]) (by decide +kernel)
def pv193051 : PrimeValue := ⟨193051, pr193051⟩
private theorem pr193057 : Nat.Prime 193057 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2011]) (by decide +kernel)
def pv193057 : PrimeValue := ⟨193057, pr193057⟩
private theorem pr193073 : Nat.Prime 193073 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv1097]) (by decide +kernel)
def pv193073 : PrimeValue := ⟨193073, pr193073⟩
private theorem pr193093 : Nat.Prime 193093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv16091]) (by decide +kernel)
def pv193093 : PrimeValue := ⟨193093, pr193093⟩
private theorem pr193133 : Nat.Prime 193133 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53,pv911]) (by decide +kernel)
def pv193133 : PrimeValue := ⟨193133, pr193133⟩
private theorem pr193139 : Nat.Prime 193139 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv8779]) (by decide +kernel)
def pv193139 : PrimeValue := ⟨193139, pr193139⟩
private theorem pr193153 : Nat.Prime 193153 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv503]) (by decide +kernel)
def pv193153 : PrimeValue := ⟨193153, pr193153⟩
private theorem pr193163 : Nat.Prime 193163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv96581]) (by decide +kernel)
def pv193163 : PrimeValue := ⟨193163, pr193163⟩
private theorem pr193181 : Nat.Prime 193181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv743]) (by decide +kernel)
def pv193181 : PrimeValue := ⟨193181, pr193181⟩
private theorem pr193189 : Nat.Prime 193189 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv17,pv947]) (by decide +kernel)
def pv193189 : PrimeValue := ⟨193189, pr193189⟩
private theorem pr193201 : Nat.Prime 193201 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv23]) (by decide +kernel)
def pv193201 : PrimeValue := ⟨193201, pr193201⟩
private theorem pr193243 : Nat.Prime 193243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv43,pv107]) (by decide +kernel)
def pv193243 : PrimeValue := ⟨193243, pr193243⟩
private theorem pr193261 : Nat.Prime 193261 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv3221]) (by decide +kernel)
def pv193261 : PrimeValue := ⟨193261, pr193261⟩
private theorem pr193301 : Nat.Prime 193301 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1933]) (by decide +kernel)
def pv193301 : PrimeValue := ⟨193301, pr193301⟩
private theorem pr193337 : Nat.Prime 193337 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv13]) (by decide +kernel)
def pv193337 : PrimeValue := ⟨193337, pr193337⟩
private theorem pr193357 : Nat.Prime 193357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv41,pv131]) (by decide +kernel)
def pv193357 : PrimeValue := ⟨193357, pr193357⟩
private theorem pr193373 : Nat.Prime 193373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv1667]) (by decide +kernel)
def pv193373 : PrimeValue := ⟨193373, pr193373⟩
private theorem pr193381 : Nat.Prime 193381 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv293]) (by decide +kernel)
def pv193381 : PrimeValue := ⟨193381, pr193381⟩
private theorem pr193393 : Nat.Prime 193393 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv17,pv79]) (by decide +kernel)
def pv193393 : PrimeValue := ⟨193393, pr193393⟩
private theorem pr193423 : Nat.Prime 193423 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv32237]) (by decide +kernel)
def pv193423 : PrimeValue := ⟨193423, pr193423⟩
private theorem pr193441 : Nat.Prime 193441 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv13,pv31]) (by decide +kernel)
def pv193441 : PrimeValue := ⟨193441, pr193441⟩
private theorem pr193463 : Nat.Prime 193463 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv96731]) (by decide +kernel)
def pv193463 : PrimeValue := ⟨193463, pr193463⟩
private theorem pr193469 : Nat.Prime 193469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv4397]) (by decide +kernel)
def pv193469 : PrimeValue := ⟨193469, pr193469⟩
private theorem pr193493 : Nat.Prime 193493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv61]) (by decide +kernel)
def pv193493 : PrimeValue := ⟨193493, pr193493⟩
private theorem pr193513 : Nat.Prime 193513 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv733]) (by decide +kernel)
def pv193513 : PrimeValue := ⟨193513, pr193513⟩
private theorem pr193541 : Nat.Prime 193541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv9677]) (by decide +kernel)
def pv193541 : PrimeValue := ⟨193541, pr193541⟩
private theorem pr193573 : Nat.Prime 193573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv283]) (by decide +kernel)
def pv193573 : PrimeValue := ⟨193573, pr193573⟩
private theorem pr193577 : Nat.Prime 193577 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv24197]) (by decide +kernel)
def pv193577 : PrimeValue := ⟨193577, pr193577⟩
private theorem pr193601 : Nat.Prime 193601 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv11]) (by decide +kernel)
def pv193601 : PrimeValue := ⟨193601, pr193601⟩
private theorem pr193603 : Nat.Prime 193603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv41,pv787]) (by decide +kernel)
def pv193603 : PrimeValue := ⟨193603, pr193603⟩
private theorem pr193649 : Nat.Prime 193649 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv13,pv19]) (by decide +kernel)
def pv193649 : PrimeValue := ⟨193649, pr193649⟩
private theorem pr193663 : Nat.Prime 193663 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv29,pv53]) (by decide +kernel)
def pv193663 : PrimeValue := ⟨193663, pr193663⟩
private theorem pr193679 : Nat.Prime 193679 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv179,pv541]) (by decide +kernel)
def pv193679 : PrimeValue := ⟨193679, pr193679⟩
private theorem pr193703 : Nat.Prime 193703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv96851]) (by decide +kernel)
def pv193703 : PrimeValue := ⟨193703, pr193703⟩
private theorem pr193723 : Nat.Prime 193723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv83,pv389]) (by decide +kernel)
def pv193723 : PrimeValue := ⟨193723, pr193723⟩
private theorem pr193727 : Nat.Prime 193727 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv7451]) (by decide +kernel)
def pv193727 : PrimeValue := ⟨193727, pr193727⟩
private theorem pr193751 : Nat.Prime 193751 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv5,pv31]) (by decide +kernel)
def pv193751 : PrimeValue := ⟨193751, pr193751⟩
private theorem pr193757 : Nat.Prime 193757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv59,pv821]) (by decide +kernel)
def pv193757 : PrimeValue := ⟨193757, pr193757⟩
private theorem pr193789 : Nat.Prime 193789 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv769]) (by decide +kernel)
def pv193789 : PrimeValue := ⟨193789, pr193789⟩
private theorem pr193793 : Nat.Prime 193793 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv757]) (by decide +kernel)
def pv193793 : PrimeValue := ⟨193793, pr193793⟩
private theorem pr193811 : Nat.Prime 193811 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19381]) (by decide +kernel)
def pv193811 : PrimeValue := ⟨193811, pr193811⟩
private theorem pr193813 : Nat.Prime 193813 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv31,pv521]) (by decide +kernel)
def pv193813 : PrimeValue := ⟨193813, pr193813⟩
private theorem pr193841 : Nat.Prime 193841 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv2423]) (by decide +kernel)
def pv193841 : PrimeValue := ⟨193841, pr193841⟩
private theorem pr193847 : Nat.Prime 193847 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv103,pv941]) (by decide +kernel)
def pv193847 : PrimeValue := ⟨193847, pr193847⟩
private theorem pr193859 : Nat.Prime 193859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv61,pv227]) (by decide +kernel)
def pv193859 : PrimeValue := ⟨193859, pr193859⟩
private theorem pr193861 : Nat.Prime 193861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv359]) (by decide +kernel)
def pv193861 : PrimeValue := ⟨193861, pr193861⟩
private theorem pr193871 : Nat.Prime 193871 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv19387]) (by decide +kernel)
def pv193871 : PrimeValue := ⟨193871, pr193871⟩
private theorem pr193877 : Nat.Prime 193877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv2551]) (by decide +kernel)
def pv193877 : PrimeValue := ⟨193877, pr193877⟩
private theorem pr193891 : Nat.Prime 193891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv23,pv281]) (by decide +kernel)
def pv193891 : PrimeValue := ⟨193891, pr193891⟩
private theorem pr193937 : Nat.Prime 193937 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv23,pv31]) (by decide +kernel)
def pv193937 : PrimeValue := ⟨193937, pr193937⟩
private theorem pr193939 : Nat.Prime 193939 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv32323]) (by decide +kernel)
def pv193939 : PrimeValue := ⟨193939, pr193939⟩
private theorem pr193957 : Nat.Prime 193957 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv2309]) (by decide +kernel)
def pv193957 : PrimeValue := ⟨193957, pr193957⟩
private theorem pr193979 : Nat.Prime 193979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv96989]) (by decide +kernel)
def pv193979 : PrimeValue := ⟨193979, pr193979⟩
private theorem pr194027 : Nat.Prime 194027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv13859]) (by decide +kernel)
def pv194027 : PrimeValue := ⟨194027, pr194027⟩
private theorem pr194057 : Nat.Prime 194057 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv127,pv191]) (by decide +kernel)
def pv194057 : PrimeValue := ⟨194057, pr194057⟩
private theorem pr194069 : Nat.Prime 194069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv29,pv239]) (by decide +kernel)
def pv194069 : PrimeValue := ⟨194069, pr194069⟩
private theorem pr194071 : Nat.Prime 194071 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv6469]) (by decide +kernel)
def pv194071 : PrimeValue := ⟨194071, pr194071⟩
private theorem pr194083 : Nat.Prime 194083 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv4621]) (by decide +kernel)
def pv194083 : PrimeValue := ⟨194083, pr194083⟩
private theorem pr194087 : Nat.Prime 194087 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv53,pv1831]) (by decide +kernel)
def pv194087 : PrimeValue := ⟨194087, pr194087⟩
private theorem pr194093 : Nat.Prime 194093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv48523]) (by decide +kernel)
def pv194093 : PrimeValue := ⟨194093, pr194093⟩
private theorem pr194101 : Nat.Prime 194101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv647]) (by decide +kernel)
def pv194101 : PrimeValue := ⟨194101, pr194101⟩
private theorem pr194113 : Nat.Prime 194113 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv337]) (by decide +kernel)
def pv194113 : PrimeValue := ⟨194113, pr194113⟩
private theorem pr194141 : Nat.Prime 194141 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv571]) (by decide +kernel)
def pv194141 : PrimeValue := ⟨194141, pr194141⟩
private theorem pr194149 : Nat.Prime 194149 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5393]) (by decide +kernel)
def pv194149 : PrimeValue := ⟨194149, pr194149⟩
private theorem pr194167 : Nat.Prime 194167 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv23,pv67]) (by decide +kernel)
def pv194167 : PrimeValue := ⟨194167, pr194167⟩
private theorem pr194197 : Nat.Prime 194197 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv16183]) (by decide +kernel)
def pv194197 : PrimeValue := ⟨194197, pr194197⟩
private theorem pr194203 : Nat.Prime 194203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv10789]) (by decide +kernel)
def pv194203 : PrimeValue := ⟨194203, pr194203⟩
private theorem pr194239 : Nat.Prime 194239 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv11,pv109]) (by decide +kernel)
def pv194239 : PrimeValue := ⟨194239, pr194239⟩
private theorem pr194263 : Nat.Prime 194263 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv32377]) (by decide +kernel)
def pv194263 : PrimeValue := ⟨194263, pr194263⟩
private theorem pr194323 : Nat.Prime 194323 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv139,pv233]) (by decide +kernel)
def pv194323 : PrimeValue := ⟨194323, pr194323⟩
private theorem pr194353 : Nat.Prime 194353 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv4049]) (by decide +kernel)
def pv194353 : PrimeValue := ⟨194353, pr194353⟩
private theorem pr194371 : Nat.Prime 194371 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv19,pv31]) (by decide +kernel)
def pv194371 : PrimeValue := ⟨194371, pr194371⟩
private theorem pr194377 : Nat.Prime 194377 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv89]) (by decide +kernel)
def pv194377 : PrimeValue := ⟨194377, pr194377⟩
private theorem pr194413 : Nat.Prime 194413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv953]) (by decide +kernel)
def pv194413 : PrimeValue := ⟨194413, pr194413⟩
private theorem pr194431 : Nat.Prime 194431 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv6481]) (by decide +kernel)
def pv194431 : PrimeValue := ⟨194431, pr194431⟩
private theorem pr194471 : Nat.Prime 194471 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv19447]) (by decide +kernel)
def pv194471 : PrimeValue := ⟨194471, pr194471⟩
private theorem pr194479 : Nat.Prime 194479 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv32413]) (by decide +kernel)
def pv194479 : PrimeValue := ⟨194479, pr194479⟩
private theorem pr194483 : Nat.Prime 194483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv97241]) (by decide +kernel)
def pv194483 : PrimeValue := ⟨194483, pr194483⟩
private theorem pr194527 : Nat.Prime 194527 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv101,pv107]) (by decide +kernel)
def pv194527 : PrimeValue := ⟨194527, pr194527⟩
private theorem pr194591 : Nat.Prime 194591 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv11,pv29,pv61]) (by decide +kernel)
def pv194591 : PrimeValue := ⟨194591, pr194591⟩
private theorem pr194609 : Nat.Prime 194609 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv12163]) (by decide +kernel)
def pv194609 : PrimeValue := ⟨194609, pr194609⟩
private theorem pr194647 : Nat.Prime 194647 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv32441]) (by decide +kernel)
def pv194647 : PrimeValue := ⟨194647, pr194647⟩
private theorem pr194653 : Nat.Prime 194653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5407]) (by decide +kernel)
def pv194653 : PrimeValue := ⟨194653, pr194653⟩
private theorem pr194659 : Nat.Prime 194659 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv32443]) (by decide +kernel)
def pv194659 : PrimeValue := ⟨194659, pr194659⟩
private theorem pr194671 : Nat.Prime 194671 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv103]) (by decide +kernel)
def pv194671 : PrimeValue := ⟨194671, pr194671⟩
private theorem pr194683 : Nat.Prime 194683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv71,pv457]) (by decide +kernel)
def pv194683 : PrimeValue := ⟨194683, pr194683⟩
private theorem pr194707 : Nat.Prime 194707 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv373]) (by decide +kernel)
def pv194707 : PrimeValue := ⟨194707, pr194707⟩
private theorem pr194713 : Nat.Prime 194713 :=
  checkPrime_prime (q := pv47) (ls := [pv2,pv3,pv7,pv19,pv61]) (by decide +kernel)
def pv194713 : PrimeValue := ⟨194713, pr194713⟩
private theorem pr194723 : Nat.Prime 194723 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv53,pv167]) (by decide +kernel)
def pv194723 : PrimeValue := ⟨194723, pr194723⟩
private theorem pr194729 : Nat.Prime 194729 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv101,pv241]) (by decide +kernel)
def pv194729 : PrimeValue := ⟨194729, pr194729⟩
private theorem pr194749 : Nat.Prime 194749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv16229]) (by decide +kernel)
def pv194749 : PrimeValue := ⟨194749, pr194749⟩
private theorem pr194767 : Nat.Prime 194767 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv13,pv227]) (by decide +kernel)
def pv194767 : PrimeValue := ⟨194767, pr194767⟩
private theorem pr194771 : Nat.Prime 194771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19477]) (by decide +kernel)
def pv194771 : PrimeValue := ⟨194771, pr194771⟩
private theorem pr194809 : Nat.Prime 194809 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv8117]) (by decide +kernel)
def pv194809 : PrimeValue := ⟨194809, pr194809⟩
private theorem pr194813 : Nat.Prime 194813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv113,pv431]) (by decide +kernel)
def pv194813 : PrimeValue := ⟨194813, pr194813⟩
private theorem pr194839 : Nat.Prime 194839 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv4639]) (by decide +kernel)
def pv194839 : PrimeValue := ⟨194839, pr194839⟩
private theorem pr194861 : Nat.Prime 194861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv9743]) (by decide +kernel)
def pv194861 : PrimeValue := ⟨194861, pr194861⟩
private theorem pr194863 : Nat.Prime 194863 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv47,pv691]) (by decide +kernel)
def pv194863 : PrimeValue := ⟨194863, pr194863⟩
private theorem pr194867 : Nat.Prime 194867 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv31,pv449]) (by decide +kernel)
def pv194867 : PrimeValue := ⟨194867, pr194867⟩
private theorem pr194869 : Nat.Prime 194869 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5413]) (by decide +kernel)
def pv194869 : PrimeValue := ⟨194869, pr194869⟩
private theorem pr194891 : Nat.Prime 194891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19489]) (by decide +kernel)
def pv194891 : PrimeValue := ⟨194891, pr194891⟩
private theorem pr194911 : Nat.Prime 194911 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv73,pv89]) (by decide +kernel)
def pv194911 : PrimeValue := ⟨194911, pr194911⟩
private theorem pr194917 : Nat.Prime 194917 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv439]) (by decide +kernel)
def pv194917 : PrimeValue := ⟨194917, pr194917⟩
private theorem pr194933 : Nat.Prime 194933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv48733]) (by decide +kernel)
def pv194933 : PrimeValue := ⟨194933, pr194933⟩
private theorem pr194963 : Nat.Prime 194963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv2267]) (by decide +kernel)
def pv194963 : PrimeValue := ⟨194963, pr194963⟩
private theorem pr194977 : Nat.Prime 194977 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv677]) (by decide +kernel)
def pv194977 : PrimeValue := ⟨194977, pr194977⟩
private theorem pr194981 : Nat.Prime 194981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv9749]) (by decide +kernel)
def pv194981 : PrimeValue := ⟨194981, pr194981⟩
private theorem pr195023 : Nat.Prime 195023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv97511]) (by decide +kernel)
def pv195023 : PrimeValue := ⟨195023, pr195023⟩
private theorem pr195043 : Nat.Prime 195043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv32507]) (by decide +kernel)
def pv195043 : PrimeValue := ⟨195043, pr195043⟩
private theorem pr195053 : Nat.Prime 195053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv13,pv31]) (by decide +kernel)
def pv195053 : PrimeValue := ⟨195053, pr195053⟩
private theorem pr195071 : Nat.Prime 195071 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv19507]) (by decide +kernel)
def pv195071 : PrimeValue := ⟨195071, pr195071⟩
private theorem pr195089 : Nat.Prime 195089 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv89,pv137]) (by decide +kernel)
def pv195089 : PrimeValue := ⟨195089, pr195089⟩
private theorem pr195121 : Nat.Prime 195121 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv271]) (by decide +kernel)
def pv195121 : PrimeValue := ⟨195121, pr195121⟩
private theorem pr195131 : Nat.Prime 195131 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv5,pv13,pv19,pv79]) (by decide +kernel)
def pv195131 : PrimeValue := ⟨195131, pr195131⟩
private theorem pr195157 : Nat.Prime 195157 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv139]) (by decide +kernel)
def pv195157 : PrimeValue := ⟨195157, pr195157⟩
private theorem pr195161 : Nat.Prime 195161 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv17,pv41]) (by decide +kernel)
def pv195161 : PrimeValue := ⟨195161, pr195161⟩
private theorem pr195163 : Nat.Prime 195163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv2957]) (by decide +kernel)
def pv195163 : PrimeValue := ⟨195163, pr195163⟩
private theorem pr195193 : Nat.Prime 195193 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv2711]) (by decide +kernel)
def pv195193 : PrimeValue := ⟨195193, pr195193⟩
private theorem pr195197 : Nat.Prime 195197 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv48799]) (by decide +kernel)
def pv195197 : PrimeValue := ⟨195197, pr195197⟩
private theorem pr195203 : Nat.Prime 195203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv73,pv191]) (by decide +kernel)
def pv195203 : PrimeValue := ⟨195203, pr195203⟩
private theorem pr195229 : Nat.Prime 195229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv17,pv29]) (by decide +kernel)
def pv195229 : PrimeValue := ⟨195229, pr195229⟩
private theorem pr195241 : Nat.Prime 195241 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv1627]) (by decide +kernel)
def pv195241 : PrimeValue := ⟨195241, pr195241⟩
private theorem pr195253 : Nat.Prime 195253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv53,pv307]) (by decide +kernel)
def pv195253 : PrimeValue := ⟨195253, pr195253⟩
private theorem pr195259 : Nat.Prime 195259 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv4649]) (by decide +kernel)
def pv195259 : PrimeValue := ⟨195259, pr195259⟩
private theorem pr195311 : Nat.Prime 195311 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv19531]) (by decide +kernel)
def pv195311 : PrimeValue := ⟨195311, pr195311⟩
private theorem pr195329 : Nat.Prime 195329 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv109]) (by decide +kernel)
def pv195329 : PrimeValue := ⟨195329, pr195329⟩
private theorem pr195341 : Nat.Prime 195341 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv9767]) (by decide +kernel)
def pv195341 : PrimeValue := ⟨195341, pr195341⟩
private theorem pr195343 : Nat.Prime 195343 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv4651]) (by decide +kernel)
def pv195343 : PrimeValue := ⟨195343, pr195343⟩
private theorem pr195353 : Nat.Prime 195353 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv24419]) (by decide +kernel)
def pv195353 : PrimeValue := ⟨195353, pr195353⟩
private theorem pr195401 : Nat.Prime 195401 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv977]) (by decide +kernel)
def pv195401 : PrimeValue := ⟨195401, pr195401⟩
private theorem pr195407 : Nat.Prime 195407 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv41,pv2383]) (by decide +kernel)
def pv195407 : PrimeValue := ⟨195407, pr195407⟩
private theorem pr195443 : Nat.Prime 195443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv7517]) (by decide +kernel)
def pv195443 : PrimeValue := ⟨195443, pr195443⟩
private theorem pr195469 : Nat.Prime 195469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv179]) (by decide +kernel)
def pv195469 : PrimeValue := ⟨195469, pr195469⟩
private theorem pr195479 : Nat.Prime 195479 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv43,pv2273]) (by decide +kernel)
def pv195479 : PrimeValue := ⟨195479, pr195479⟩
private theorem pr195493 : Nat.Prime 195493 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv1481]) (by decide +kernel)
def pv195493 : PrimeValue := ⟨195493, pr195493⟩
private theorem pr195527 : Nat.Prime 195527 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv59,pv1657]) (by decide +kernel)
def pv195527 : PrimeValue := ⟨195527, pr195527⟩
private theorem pr195539 : Nat.Prime 195539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv13967]) (by decide +kernel)
def pv195539 : PrimeValue := ⟨195539, pr195539⟩
private theorem pr195581 : Nat.Prime 195581 :=
  checkPrime_prime (q := pv59) (ls := [pv2,pv5,pv7,pv11,pv127]) (by decide +kernel)
def pv195581 : PrimeValue := ⟨195581, pr195581⟩
private theorem pr195599 : Nat.Prime 195599 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv13,pv7523]) (by decide +kernel)
def pv195599 : PrimeValue := ⟨195599, pr195599⟩
private theorem pr195677 : Nat.Prime 195677 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv53,pv71]) (by decide +kernel)
def pv195677 : PrimeValue := ⟨195677, pr195677⟩
private theorem pr195691 : Nat.Prime 195691 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv593]) (by decide +kernel)
def pv195691 : PrimeValue := ⟨195691, pr195691⟩
private theorem pr195697 : Nat.Prime 195697 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv151]) (by decide +kernel)
def pv195697 : PrimeValue := ⟨195697, pr195697⟩
private theorem pr195731 : Nat.Prime 195731 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv23,pv37]) (by decide +kernel)
def pv195731 : PrimeValue := ⟨195731, pr195731⟩
private theorem pr195733 : Nat.Prime 195733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5437]) (by decide +kernel)
def pv195733 : PrimeValue := ⟨195733, pr195733⟩
private theorem pr195737 : Nat.Prime 195737 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv43,pv569]) (by decide +kernel)
def pv195737 : PrimeValue := ⟨195737, pr195737⟩
private theorem pr195739 : Nat.Prime 195739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv19,pv101]) (by decide +kernel)
def pv195739 : PrimeValue := ⟨195739, pr195739⟩
private theorem pr195743 : Nat.Prime 195743 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv97871]) (by decide +kernel)
def pv195743 : PrimeValue := ⟨195743, pr195743⟩
private theorem pr195751 : Nat.Prime 195751 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv29]) (by decide +kernel)
def pv195751 : PrimeValue := ⟨195751, pr195751⟩
private theorem pr195781 : Nat.Prime 195781 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv251]) (by decide +kernel)
def pv195781 : PrimeValue := ⟨195781, pr195781⟩
private theorem pr195787 : Nat.Prime 195787 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv73,pv149]) (by decide +kernel)
def pv195787 : PrimeValue := ⟨195787, pr195787⟩
private theorem pr195809 : Nat.Prime 195809 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv211]) (by decide +kernel)
def pv195809 : PrimeValue := ⟨195809, pr195809⟩
private theorem pr195817 : Nat.Prime 195817 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv41,pv199]) (by decide +kernel)
def pv195817 : PrimeValue := ⟨195817, pr195817⟩
private theorem pr195869 : Nat.Prime 195869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv2129]) (by decide +kernel)
def pv195869 : PrimeValue := ⟨195869, pr195869⟩
private theorem pr195883 : Nat.Prime 195883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv32647]) (by decide +kernel)
def pv195883 : PrimeValue := ⟨195883, pr195883⟩
private theorem pr195893 : Nat.Prime 195893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv48973]) (by decide +kernel)
def pv195893 : PrimeValue := ⟨195893, pr195893⟩
private theorem pr195913 : Nat.Prime 195913 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv907]) (by decide +kernel)
def pv195913 : PrimeValue := ⟨195913, pr195913⟩
private theorem pr195919 : Nat.Prime 195919 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv32653]) (by decide +kernel)
def pv195919 : PrimeValue := ⟨195919, pr195919⟩
private theorem pr195929 : Nat.Prime 195929 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv1289]) (by decide +kernel)
def pv195929 : PrimeValue := ⟨195929, pr195929⟩
private theorem pr195931 : Nat.Prime 195931 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv311]) (by decide +kernel)
def pv195931 : PrimeValue := ⟨195931, pr195931⟩
private theorem pr195967 : Nat.Prime 195967 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv191]) (by decide +kernel)
def pv195967 : PrimeValue := ⟨195967, pr195967⟩
private theorem pr195971 : Nat.Prime 195971 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv19597]) (by decide +kernel)
def pv195971 : PrimeValue := ⟨195971, pr195971⟩
private theorem pr195973 : Nat.Prime 195973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv2333]) (by decide +kernel)
def pv195973 : PrimeValue := ⟨195973, pr195973⟩
private theorem pr195997 : Nat.Prime 195997 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv16333]) (by decide +kernel)
def pv195997 : PrimeValue := ⟨195997, pr195997⟩
private theorem pr196003 : Nat.Prime 196003 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv10889]) (by decide +kernel)
def pv196003 : PrimeValue := ⟨196003, pr196003⟩
private theorem pr196033 : Nat.Prime 196033 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv1021]) (by decide +kernel)
def pv196033 : PrimeValue := ⟨196033, pr196033⟩
private theorem pr196039 : Nat.Prime 196039 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv10891]) (by decide +kernel)
def pv196039 : PrimeValue := ⟨196039, pr196039⟩
private theorem pr196043 : Nat.Prime 196043 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv11,pv19,pv67]) (by decide +kernel)
def pv196043 : PrimeValue := ⟨196043, pr196043⟩
private theorem pr196051 : Nat.Prime 196051 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv1307]) (by decide +kernel)
def pv196051 : PrimeValue := ⟨196051, pr196051⟩
private theorem pr196087 : Nat.Prime 196087 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv2971]) (by decide +kernel)
def pv196087 : PrimeValue := ⟨196087, pr196087⟩
private theorem pr196111 : Nat.Prime 196111 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv2179]) (by decide +kernel)
def pv196111 : PrimeValue := ⟨196111, pr196111⟩
private theorem pr196139 : Nat.Prime 196139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv281,pv349]) (by decide +kernel)
def pv196139 : PrimeValue := ⟨196139, pr196139⟩
private theorem pr196169 : Nat.Prime 196169 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv31,pv113]) (by decide +kernel)
def pv196169 : PrimeValue := ⟨196169, pr196169⟩
private theorem pr196171 : Nat.Prime 196171 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv13,pv503]) (by decide +kernel)
def pv196171 : PrimeValue := ⟨196171, pr196171⟩
private theorem pr196181 : Nat.Prime 196181 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17,pv577]) (by decide +kernel)
def pv196181 : PrimeValue := ⟨196181, pr196181⟩
private theorem pr196193 : Nat.Prime 196193 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv6131]) (by decide +kernel)
def pv196193 : PrimeValue := ⟨196193, pr196193⟩
private theorem pr196201 : Nat.Prime 196201 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv109]) (by decide +kernel)
def pv196201 : PrimeValue := ⟨196201, pr196201⟩
private theorem pr196247 : Nat.Prime 196247 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv98123]) (by decide +kernel)
def pv196247 : PrimeValue := ⟨196247, pr196247⟩
private theorem pr196271 : Nat.Prime 196271 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv19,pv1033]) (by decide +kernel)
def pv196271 : PrimeValue := ⟨196271, pr196271⟩
private theorem pr196291 : Nat.Prime 196291 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv727]) (by decide +kernel)
def pv196291 : PrimeValue := ⟨196291, pr196291⟩
private theorem pr196307 : Nat.Prime 196307 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv8923]) (by decide +kernel)
def pv196307 : PrimeValue := ⟨196307, pr196307⟩
private theorem pr196331 : Nat.Prime 196331 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv29,pv677]) (by decide +kernel)
def pv196331 : PrimeValue := ⟨196331, pr196331⟩
private theorem pr196337 : Nat.Prime 196337 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv1753]) (by decide +kernel)
def pv196337 : PrimeValue := ⟨196337, pr196337⟩
private theorem pr196379 : Nat.Prime 196379 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv13,pv83]) (by decide +kernel)
def pv196379 : PrimeValue := ⟨196379, pr196379⟩
private theorem pr196387 : Nat.Prime 196387 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv71,pv461]) (by decide +kernel)
def pv196387 : PrimeValue := ⟨196387, pr196387⟩
private theorem pr196429 : Nat.Prime 196429 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv16369]) (by decide +kernel)
def pv196429 : PrimeValue := ⟨196429, pr196429⟩
private theorem pr196439 : Nat.Prime 196439 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv11,pv8929]) (by decide +kernel)
def pv196439 : PrimeValue := ⟨196439, pr196439⟩
private theorem pr196453 : Nat.Prime 196453 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv17,pv107]) (by decide +kernel)
def pv196453 : PrimeValue := ⟨196453, pr196453⟩
private theorem pr196519 : Nat.Prime 196519 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv4679]) (by decide +kernel)
def pv196519 : PrimeValue := ⟨196519, pr196519⟩
private theorem pr196523 : Nat.Prime 196523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv97,pv1013]) (by decide +kernel)
def pv196523 : PrimeValue := ⟨196523, pr196523⟩
private theorem pr196541 : Nat.Prime 196541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv31,pv317]) (by decide +kernel)
def pv196541 : PrimeValue := ⟨196541, pr196541⟩
private theorem pr196543 : Nat.Prime 196543 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv61,pv179]) (by decide +kernel)
def pv196543 : PrimeValue := ⟨196543, pr196543⟩
private theorem pr196549 : Nat.Prime 196549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv1489]) (by decide +kernel)
def pv196549 : PrimeValue := ⟨196549, pr196549⟩
private theorem pr196583 : Nat.Prime 196583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv227,pv433]) (by decide +kernel)
def pv196583 : PrimeValue := ⟨196583, pr196583⟩
private theorem pr196597 : Nat.Prime 196597 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv43,pv127]) (by decide +kernel)
def pv196597 : PrimeValue := ⟨196597, pr196597⟩
private theorem pr196643 : Nat.Prime 196643 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv98321]) (by decide +kernel)
def pv196643 : PrimeValue := ⟨196643, pr196643⟩
private theorem pr196657 : Nat.Prime 196657 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv17,pv241]) (by decide +kernel)
def pv196657 : PrimeValue := ⟨196657, pr196657⟩
private theorem pr196663 : Nat.Prime 196663 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv73,pv449]) (by decide +kernel)
def pv196663 : PrimeValue := ⟨196663, pr196663⟩
private theorem pr196681 : Nat.Prime 196681 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv11,pv149]) (by decide +kernel)
def pv196681 : PrimeValue := ⟨196681, pr196681⟩
private theorem pr196687 : Nat.Prime 196687 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv223]) (by decide +kernel)
def pv196687 : PrimeValue := ⟨196687, pr196687⟩
private theorem pr196709 : Nat.Prime 196709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv49177]) (by decide +kernel)
def pv196709 : PrimeValue := ⟨196709, pr196709⟩
private theorem pr196717 : Nat.Prime 196717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv97]) (by decide +kernel)
def pv196717 : PrimeValue := ⟨196717, pr196717⟩
private theorem pr196739 : Nat.Prime 196739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv98369]) (by decide +kernel)
def pv196739 : PrimeValue := ⟨196739, pr196739⟩
private theorem pr196751 : Nat.Prime 196751 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv787]) (by decide +kernel)
def pv196751 : PrimeValue := ⟨196751, pr196751⟩
private theorem pr196769 : Nat.Prime 196769 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv13,pv43]) (by decide +kernel)
def pv196769 : PrimeValue := ⟨196769, pr196769⟩
private theorem pr196771 : Nat.Prime 196771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv937]) (by decide +kernel)
def pv196771 : PrimeValue := ⟨196771, pr196771⟩
private theorem pr196799 : Nat.Prime 196799 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv14057]) (by decide +kernel)
def pv196799 : PrimeValue := ⟨196799, pr196799⟩
private theorem pr196817 : Nat.Prime 196817 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv12301]) (by decide +kernel)
def pv196817 : PrimeValue := ⟨196817, pr196817⟩
private theorem pr196831 : Nat.Prime 196831 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv196831 : PrimeValue := ⟨196831, pr196831⟩
private theorem pr196837 : Nat.Prime 196837 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv47,pv349]) (by decide +kernel)
def pv196837 : PrimeValue := ⟨196837, pr196837⟩
private theorem pr196853 : Nat.Prime 196853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv1697]) (by decide +kernel)
def pv196853 : PrimeValue := ⟨196853, pr196853⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
