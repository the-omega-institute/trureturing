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
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr192461 : PrimeCertificate 192461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv9623]) (by decide +kernel)
def pv192461 : PrimeValue := ⟨192461, pr192461⟩
private theorem pr192463 : PrimeCertificate 192463 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv32077]) (by decide +kernel)
def pv192463 : PrimeValue := ⟨192463, pr192463⟩
private theorem pr192499 : PrimeCertificate 192499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv32083]) (by decide +kernel)
def pv192499 : PrimeValue := ⟨192499, pr192499⟩
private theorem pr192529 : PrimeCertificate 192529 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv7,pv191]) (by decide +kernel)
def pv192529 : PrimeValue := ⟨192529, pr192529⟩
private theorem pr192539 : PrimeCertificate 192539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv96269]) (by decide +kernel)
def pv192539 : PrimeValue := ⟨192539, pr192539⟩
private theorem pr192553 : PrimeCertificate 192553 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv71,pv113]) (by decide +kernel)
def pv192553 : PrimeValue := ⟨192553, pr192553⟩
private theorem pr192571 : PrimeCertificate 192571 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv131]) (by decide +kernel)
def pv192571 : PrimeValue := ⟨192571, pr192571⟩
private theorem pr192583 : PrimeCertificate 192583 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv823]) (by decide +kernel)
def pv192583 : PrimeValue := ⟨192583, pr192583⟩
private theorem pr192587 : PrimeCertificate 192587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv96293]) (by decide +kernel)
def pv192587 : PrimeValue := ⟨192587, pr192587⟩
private theorem pr192601 : PrimeCertificate 192601 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv107]) (by decide +kernel)
def pv192601 : PrimeValue := ⟨192601, pr192601⟩
private theorem pr192611 : PrimeCertificate 192611 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv11,pv17,pv103]) (by decide +kernel)
def pv192611 : PrimeValue := ⟨192611, pr192611⟩
private theorem pr192613 : PrimeCertificate 192613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv2293]) (by decide +kernel)
def pv192613 : PrimeValue := ⟨192613, pr192613⟩
private theorem pr192617 : PrimeCertificate 192617 :=
  certifyPrime (q := pv3) (ls := [pv2,pv24077]) (by decide +kernel)
def pv192617 : PrimeValue := ⟨192617, pr192617⟩
private theorem pr192629 : PrimeCertificate 192629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv48157]) (by decide +kernel)
def pv192629 : PrimeValue := ⟨192629, pr192629⟩
private theorem pr192637 : PrimeCertificate 192637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5351]) (by decide +kernel)
def pv192637 : PrimeValue := ⟨192637, pr192637⟩
private theorem pr192667 : PrimeCertificate 192667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv163,pv197]) (by decide +kernel)
def pv192667 : PrimeValue := ⟨192667, pr192667⟩
private theorem pr192677 : PrimeCertificate 192677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv29,pv151]) (by decide +kernel)
def pv192677 : PrimeValue := ⟨192677, pr192677⟩
private theorem pr192697 : PrimeCertificate 192697 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv31,pv37]) (by decide +kernel)
def pv192697 : PrimeValue := ⟨192697, pr192697⟩
private theorem pr192737 : PrimeCertificate 192737 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv317]) (by decide +kernel)
def pv192737 : PrimeValue := ⟨192737, pr192737⟩
private theorem pr192757 : PrimeCertificate 192757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv16063]) (by decide +kernel)
def pv192757 : PrimeValue := ⟨192757, pr192757⟩
private theorem pr192767 : PrimeCertificate 192767 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv281]) (by decide +kernel)
def pv192767 : PrimeValue := ⟨192767, pr192767⟩
private theorem pr192781 : PrimeCertificate 192781 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv17]) (by decide +kernel)
def pv192781 : PrimeValue := ⟨192781, pr192781⟩
private theorem pr192791 : PrimeCertificate 192791 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv1483]) (by decide +kernel)
def pv192791 : PrimeValue := ⟨192791, pr192791⟩
private theorem pr192817 : PrimeCertificate 192817 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv103]) (by decide +kernel)
def pv192817 : PrimeValue := ⟨192817, pr192817⟩
private theorem pr192847 : PrimeCertificate 192847 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv32141]) (by decide +kernel)
def pv192847 : PrimeValue := ⟨192847, pr192847⟩
private theorem pr192859 : PrimeCertificate 192859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv32143]) (by decide +kernel)
def pv192859 : PrimeValue := ⟨192859, pr192859⟩
private theorem pr192877 : PrimeCertificate 192877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv16073]) (by decide +kernel)
def pv192877 : PrimeValue := ⟨192877, pr192877⟩
private theorem pr192883 : PrimeCertificate 192883 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv31,pv61]) (by decide +kernel)
def pv192883 : PrimeValue := ⟨192883, pr192883⟩
private theorem pr192887 : PrimeCertificate 192887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv96443]) (by decide +kernel)
def pv192887 : PrimeValue := ⟨192887, pr192887⟩
private theorem pr192917 : PrimeCertificate 192917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv2837]) (by decide +kernel)
def pv192917 : PrimeValue := ⟨192917, pr192917⟩
private theorem pr192923 : PrimeCertificate 192923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv96461]) (by decide +kernel)
def pv192923 : PrimeValue := ⟨192923, pr192923⟩
private theorem pr192931 : PrimeCertificate 192931 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv59,pv109]) (by decide +kernel)
def pv192931 : PrimeValue := ⟨192931, pr192931⟩
private theorem pr192961 : PrimeCertificate 192961 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv67]) (by decide +kernel)
def pv192961 : PrimeValue := ⟨192961, pr192961⟩
private theorem pr192971 : PrimeCertificate 192971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv839]) (by decide +kernel)
def pv192971 : PrimeValue := ⟨192971, pr192971⟩
private theorem pr192977 : PrimeCertificate 192977 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv1723]) (by decide +kernel)
def pv192977 : PrimeValue := ⟨192977, pr192977⟩
private theorem pr192979 : PrimeCertificate 192979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv71,pv151]) (by decide +kernel)
def pv192979 : PrimeValue := ⟨192979, pr192979⟩
private theorem pr192991 : PrimeCertificate 192991 :=
  certifyPrime (q := pv47) (ls := [pv2,pv3,pv5,pv7,pv919]) (by decide +kernel)
def pv192991 : PrimeValue := ⟨192991, pr192991⟩
private theorem pr193003 : PrimeCertificate 193003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv1693]) (by decide +kernel)
def pv193003 : PrimeValue := ⟨193003, pr193003⟩
private theorem pr193031 : PrimeCertificate 193031 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv97,pv199]) (by decide +kernel)
def pv193031 : PrimeValue := ⟨193031, pr193031⟩
private theorem pr193043 : PrimeCertificate 193043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv263,pv367]) (by decide +kernel)
def pv193043 : PrimeValue := ⟨193043, pr193043⟩
private theorem pr193051 : PrimeCertificate 193051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv13]) (by decide +kernel)
def pv193051 : PrimeValue := ⟨193051, pr193051⟩
private theorem pr193057 : PrimeCertificate 193057 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2011]) (by decide +kernel)
def pv193057 : PrimeValue := ⟨193057, pr193057⟩
private theorem pr193073 : PrimeCertificate 193073 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv1097]) (by decide +kernel)
def pv193073 : PrimeValue := ⟨193073, pr193073⟩
private theorem pr193093 : PrimeCertificate 193093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv16091]) (by decide +kernel)
def pv193093 : PrimeValue := ⟨193093, pr193093⟩
private theorem pr193133 : PrimeCertificate 193133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv911]) (by decide +kernel)
def pv193133 : PrimeValue := ⟨193133, pr193133⟩
private theorem pr193139 : PrimeCertificate 193139 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv8779]) (by decide +kernel)
def pv193139 : PrimeValue := ⟨193139, pr193139⟩
private theorem pr193153 : PrimeCertificate 193153 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv503]) (by decide +kernel)
def pv193153 : PrimeValue := ⟨193153, pr193153⟩
private theorem pr193163 : PrimeCertificate 193163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv96581]) (by decide +kernel)
def pv193163 : PrimeValue := ⟨193163, pr193163⟩
private theorem pr193181 : PrimeCertificate 193181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv743]) (by decide +kernel)
def pv193181 : PrimeValue := ⟨193181, pr193181⟩
private theorem pr193189 : PrimeCertificate 193189 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv947]) (by decide +kernel)
def pv193189 : PrimeValue := ⟨193189, pr193189⟩
private theorem pr193201 : PrimeCertificate 193201 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv23]) (by decide +kernel)
def pv193201 : PrimeValue := ⟨193201, pr193201⟩
private theorem pr193243 : PrimeCertificate 193243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv43,pv107]) (by decide +kernel)
def pv193243 : PrimeValue := ⟨193243, pr193243⟩
private theorem pr193261 : PrimeCertificate 193261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv3221]) (by decide +kernel)
def pv193261 : PrimeValue := ⟨193261, pr193261⟩
private theorem pr193301 : PrimeCertificate 193301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1933]) (by decide +kernel)
def pv193301 : PrimeValue := ⟨193301, pr193301⟩
private theorem pr193337 : PrimeCertificate 193337 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv13]) (by decide +kernel)
def pv193337 : PrimeValue := ⟨193337, pr193337⟩
private theorem pr193357 : PrimeCertificate 193357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv131]) (by decide +kernel)
def pv193357 : PrimeValue := ⟨193357, pr193357⟩
private theorem pr193373 : PrimeCertificate 193373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv1667]) (by decide +kernel)
def pv193373 : PrimeValue := ⟨193373, pr193373⟩
private theorem pr193381 : PrimeCertificate 193381 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv293]) (by decide +kernel)
def pv193381 : PrimeValue := ⟨193381, pr193381⟩
private theorem pr193393 : PrimeCertificate 193393 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv17,pv79]) (by decide +kernel)
def pv193393 : PrimeValue := ⟨193393, pr193393⟩
private theorem pr193423 : PrimeCertificate 193423 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv32237]) (by decide +kernel)
def pv193423 : PrimeValue := ⟨193423, pr193423⟩
private theorem pr193441 : PrimeCertificate 193441 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv13,pv31]) (by decide +kernel)
def pv193441 : PrimeValue := ⟨193441, pr193441⟩
private theorem pr193463 : PrimeCertificate 193463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv96731]) (by decide +kernel)
def pv193463 : PrimeValue := ⟨193463, pr193463⟩
private theorem pr193469 : PrimeCertificate 193469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv4397]) (by decide +kernel)
def pv193469 : PrimeValue := ⟨193469, pr193469⟩
private theorem pr193493 : PrimeCertificate 193493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv61]) (by decide +kernel)
def pv193493 : PrimeValue := ⟨193493, pr193493⟩
private theorem pr193513 : PrimeCertificate 193513 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv733]) (by decide +kernel)
def pv193513 : PrimeValue := ⟨193513, pr193513⟩
private theorem pr193541 : PrimeCertificate 193541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv9677]) (by decide +kernel)
def pv193541 : PrimeValue := ⟨193541, pr193541⟩
private theorem pr193573 : PrimeCertificate 193573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv283]) (by decide +kernel)
def pv193573 : PrimeValue := ⟨193573, pr193573⟩
private theorem pr193577 : PrimeCertificate 193577 :=
  certifyPrime (q := pv3) (ls := [pv2,pv24197]) (by decide +kernel)
def pv193577 : PrimeValue := ⟨193577, pr193577⟩
private theorem pr193601 : PrimeCertificate 193601 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv11]) (by decide +kernel)
def pv193601 : PrimeValue := ⟨193601, pr193601⟩
private theorem pr193603 : PrimeCertificate 193603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv787]) (by decide +kernel)
def pv193603 : PrimeValue := ⟨193603, pr193603⟩
private theorem pr193649 : PrimeCertificate 193649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv13,pv19]) (by decide +kernel)
def pv193649 : PrimeValue := ⟨193649, pr193649⟩
private theorem pr193663 : PrimeCertificate 193663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv29,pv53]) (by decide +kernel)
def pv193663 : PrimeValue := ⟨193663, pr193663⟩
private theorem pr193679 : PrimeCertificate 193679 :=
  certifyPrime (q := pv13) (ls := [pv2,pv179,pv541]) (by decide +kernel)
def pv193679 : PrimeValue := ⟨193679, pr193679⟩
private theorem pr193703 : PrimeCertificate 193703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv96851]) (by decide +kernel)
def pv193703 : PrimeValue := ⟨193703, pr193703⟩
private theorem pr193723 : PrimeCertificate 193723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv83,pv389]) (by decide +kernel)
def pv193723 : PrimeValue := ⟨193723, pr193723⟩
private theorem pr193727 : PrimeCertificate 193727 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv7451]) (by decide +kernel)
def pv193727 : PrimeValue := ⟨193727, pr193727⟩
private theorem pr193751 : PrimeCertificate 193751 :=
  certifyPrime (q := pv29) (ls := [pv2,pv5,pv31]) (by decide +kernel)
def pv193751 : PrimeValue := ⟨193751, pr193751⟩
private theorem pr193757 : PrimeCertificate 193757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59,pv821]) (by decide +kernel)
def pv193757 : PrimeValue := ⟨193757, pr193757⟩
private theorem pr193789 : PrimeCertificate 193789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv769]) (by decide +kernel)
def pv193789 : PrimeValue := ⟨193789, pr193789⟩
private theorem pr193793 : PrimeCertificate 193793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv757]) (by decide +kernel)
def pv193793 : PrimeValue := ⟨193793, pr193793⟩
private theorem pr193811 : PrimeCertificate 193811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19381]) (by decide +kernel)
def pv193811 : PrimeValue := ⟨193811, pr193811⟩
private theorem pr193813 : PrimeCertificate 193813 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv521]) (by decide +kernel)
def pv193813 : PrimeValue := ⟨193813, pr193813⟩
private theorem pr193841 : PrimeCertificate 193841 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv2423]) (by decide +kernel)
def pv193841 : PrimeValue := ⟨193841, pr193841⟩
private theorem pr193847 : PrimeCertificate 193847 :=
  certifyPrime (q := pv5) (ls := [pv2,pv103,pv941]) (by decide +kernel)
def pv193847 : PrimeValue := ⟨193847, pr193847⟩
private theorem pr193859 : PrimeCertificate 193859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv61,pv227]) (by decide +kernel)
def pv193859 : PrimeValue := ⟨193859, pr193859⟩
private theorem pr193861 : PrimeCertificate 193861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv359]) (by decide +kernel)
def pv193861 : PrimeValue := ⟨193861, pr193861⟩
private theorem pr193871 : PrimeCertificate 193871 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv19387]) (by decide +kernel)
def pv193871 : PrimeValue := ⟨193871, pr193871⟩
private theorem pr193877 : PrimeCertificate 193877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv2551]) (by decide +kernel)
def pv193877 : PrimeValue := ⟨193877, pr193877⟩
private theorem pr193891 : PrimeCertificate 193891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv23,pv281]) (by decide +kernel)
def pv193891 : PrimeValue := ⟨193891, pr193891⟩
private theorem pr193937 : PrimeCertificate 193937 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv23,pv31]) (by decide +kernel)
def pv193937 : PrimeValue := ⟨193937, pr193937⟩
private theorem pr193939 : PrimeCertificate 193939 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv32323]) (by decide +kernel)
def pv193939 : PrimeValue := ⟨193939, pr193939⟩
private theorem pr193957 : PrimeCertificate 193957 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv2309]) (by decide +kernel)
def pv193957 : PrimeValue := ⟨193957, pr193957⟩
private theorem pr193979 : PrimeCertificate 193979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv96989]) (by decide +kernel)
def pv193979 : PrimeValue := ⟨193979, pr193979⟩
private theorem pr194027 : PrimeCertificate 194027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13859]) (by decide +kernel)
def pv194027 : PrimeValue := ⟨194027, pr194027⟩
private theorem pr194057 : PrimeCertificate 194057 :=
  certifyPrime (q := pv3) (ls := [pv2,pv127,pv191]) (by decide +kernel)
def pv194057 : PrimeValue := ⟨194057, pr194057⟩
private theorem pr194069 : PrimeCertificate 194069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv29,pv239]) (by decide +kernel)
def pv194069 : PrimeValue := ⟨194069, pr194069⟩
private theorem pr194071 : PrimeCertificate 194071 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv6469]) (by decide +kernel)
def pv194071 : PrimeValue := ⟨194071, pr194071⟩
private theorem pr194083 : PrimeCertificate 194083 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv4621]) (by decide +kernel)
def pv194083 : PrimeValue := ⟨194083, pr194083⟩
private theorem pr194087 : PrimeCertificate 194087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv53,pv1831]) (by decide +kernel)
def pv194087 : PrimeValue := ⟨194087, pr194087⟩
private theorem pr194093 : PrimeCertificate 194093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv48523]) (by decide +kernel)
def pv194093 : PrimeValue := ⟨194093, pr194093⟩
private theorem pr194101 : PrimeCertificate 194101 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv647]) (by decide +kernel)
def pv194101 : PrimeValue := ⟨194101, pr194101⟩
private theorem pr194113 : PrimeCertificate 194113 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv337]) (by decide +kernel)
def pv194113 : PrimeValue := ⟨194113, pr194113⟩
private theorem pr194141 : PrimeCertificate 194141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv571]) (by decide +kernel)
def pv194141 : PrimeValue := ⟨194141, pr194141⟩
private theorem pr194149 : PrimeCertificate 194149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5393]) (by decide +kernel)
def pv194149 : PrimeValue := ⟨194149, pr194149⟩
private theorem pr194167 : PrimeCertificate 194167 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv23,pv67]) (by decide +kernel)
def pv194167 : PrimeValue := ⟨194167, pr194167⟩
private theorem pr194197 : PrimeCertificate 194197 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv16183]) (by decide +kernel)
def pv194197 : PrimeValue := ⟨194197, pr194197⟩
private theorem pr194203 : PrimeCertificate 194203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv10789]) (by decide +kernel)
def pv194203 : PrimeValue := ⟨194203, pr194203⟩
private theorem pr194239 : PrimeCertificate 194239 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv109]) (by decide +kernel)
def pv194239 : PrimeValue := ⟨194239, pr194239⟩
private theorem pr194263 : PrimeCertificate 194263 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv32377]) (by decide +kernel)
def pv194263 : PrimeValue := ⟨194263, pr194263⟩
private theorem pr194323 : PrimeCertificate 194323 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv139,pv233]) (by decide +kernel)
def pv194323 : PrimeValue := ⟨194323, pr194323⟩
private theorem pr194353 : PrimeCertificate 194353 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4049]) (by decide +kernel)
def pv194353 : PrimeValue := ⟨194353, pr194353⟩
private theorem pr194371 : PrimeCertificate 194371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv19,pv31]) (by decide +kernel)
def pv194371 : PrimeValue := ⟨194371, pr194371⟩
private theorem pr194377 : PrimeCertificate 194377 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv89]) (by decide +kernel)
def pv194377 : PrimeValue := ⟨194377, pr194377⟩
private theorem pr194413 : PrimeCertificate 194413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv953]) (by decide +kernel)
def pv194413 : PrimeValue := ⟨194413, pr194413⟩
private theorem pr194431 : PrimeCertificate 194431 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv6481]) (by decide +kernel)
def pv194431 : PrimeValue := ⟨194431, pr194431⟩
private theorem pr194471 : PrimeCertificate 194471 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv19447]) (by decide +kernel)
def pv194471 : PrimeValue := ⟨194471, pr194471⟩
private theorem pr194479 : PrimeCertificate 194479 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv32413]) (by decide +kernel)
def pv194479 : PrimeValue := ⟨194479, pr194479⟩
private theorem pr194483 : PrimeCertificate 194483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv97241]) (by decide +kernel)
def pv194483 : PrimeValue := ⟨194483, pr194483⟩
private theorem pr194527 : PrimeCertificate 194527 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv101,pv107]) (by decide +kernel)
def pv194527 : PrimeValue := ⟨194527, pr194527⟩
private theorem pr194591 : PrimeCertificate 194591 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv29,pv61]) (by decide +kernel)
def pv194591 : PrimeValue := ⟨194591, pr194591⟩
private theorem pr194609 : PrimeCertificate 194609 :=
  certifyPrime (q := pv3) (ls := [pv2,pv12163]) (by decide +kernel)
def pv194609 : PrimeValue := ⟨194609, pr194609⟩
private theorem pr194647 : PrimeCertificate 194647 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv32441]) (by decide +kernel)
def pv194647 : PrimeValue := ⟨194647, pr194647⟩
private theorem pr194653 : PrimeCertificate 194653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5407]) (by decide +kernel)
def pv194653 : PrimeValue := ⟨194653, pr194653⟩
private theorem pr194659 : PrimeCertificate 194659 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv32443]) (by decide +kernel)
def pv194659 : PrimeValue := ⟨194659, pr194659⟩
private theorem pr194671 : PrimeCertificate 194671 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv103]) (by decide +kernel)
def pv194671 : PrimeValue := ⟨194671, pr194671⟩
private theorem pr194683 : PrimeCertificate 194683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv71,pv457]) (by decide +kernel)
def pv194683 : PrimeValue := ⟨194683, pr194683⟩
private theorem pr194707 : PrimeCertificate 194707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv373]) (by decide +kernel)
def pv194707 : PrimeValue := ⟨194707, pr194707⟩
private theorem pr194713 : PrimeCertificate 194713 :=
  certifyPrime (q := pv47) (ls := [pv2,pv3,pv7,pv19,pv61]) (by decide +kernel)
def pv194713 : PrimeValue := ⟨194713, pr194713⟩
private theorem pr194723 : PrimeCertificate 194723 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv53,pv167]) (by decide +kernel)
def pv194723 : PrimeValue := ⟨194723, pr194723⟩
private theorem pr194729 : PrimeCertificate 194729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv101,pv241]) (by decide +kernel)
def pv194729 : PrimeValue := ⟨194729, pr194729⟩
private theorem pr194749 : PrimeCertificate 194749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv16229]) (by decide +kernel)
def pv194749 : PrimeValue := ⟨194749, pr194749⟩
private theorem pr194767 : PrimeCertificate 194767 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv13,pv227]) (by decide +kernel)
def pv194767 : PrimeValue := ⟨194767, pr194767⟩
private theorem pr194771 : PrimeCertificate 194771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19477]) (by decide +kernel)
def pv194771 : PrimeValue := ⟨194771, pr194771⟩
private theorem pr194809 : PrimeCertificate 194809 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv8117]) (by decide +kernel)
def pv194809 : PrimeValue := ⟨194809, pr194809⟩
private theorem pr194813 : PrimeCertificate 194813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv113,pv431]) (by decide +kernel)
def pv194813 : PrimeValue := ⟨194813, pr194813⟩
private theorem pr194839 : PrimeCertificate 194839 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv4639]) (by decide +kernel)
def pv194839 : PrimeValue := ⟨194839, pr194839⟩
private theorem pr194861 : PrimeCertificate 194861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv9743]) (by decide +kernel)
def pv194861 : PrimeValue := ⟨194861, pr194861⟩
private theorem pr194863 : PrimeCertificate 194863 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv47,pv691]) (by decide +kernel)
def pv194863 : PrimeValue := ⟨194863, pr194863⟩
private theorem pr194867 : PrimeCertificate 194867 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv31,pv449]) (by decide +kernel)
def pv194867 : PrimeValue := ⟨194867, pr194867⟩
private theorem pr194869 : PrimeCertificate 194869 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5413]) (by decide +kernel)
def pv194869 : PrimeValue := ⟨194869, pr194869⟩
private theorem pr194891 : PrimeCertificate 194891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19489]) (by decide +kernel)
def pv194891 : PrimeValue := ⟨194891, pr194891⟩
private theorem pr194911 : PrimeCertificate 194911 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv73,pv89]) (by decide +kernel)
def pv194911 : PrimeValue := ⟨194911, pr194911⟩
private theorem pr194917 : PrimeCertificate 194917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv439]) (by decide +kernel)
def pv194917 : PrimeValue := ⟨194917, pr194917⟩
private theorem pr194933 : PrimeCertificate 194933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv48733]) (by decide +kernel)
def pv194933 : PrimeValue := ⟨194933, pr194933⟩
private theorem pr194963 : PrimeCertificate 194963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv2267]) (by decide +kernel)
def pv194963 : PrimeValue := ⟨194963, pr194963⟩
private theorem pr194977 : PrimeCertificate 194977 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv677]) (by decide +kernel)
def pv194977 : PrimeValue := ⟨194977, pr194977⟩
private theorem pr194981 : PrimeCertificate 194981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv9749]) (by decide +kernel)
def pv194981 : PrimeValue := ⟨194981, pr194981⟩
private theorem pr195023 : PrimeCertificate 195023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv97511]) (by decide +kernel)
def pv195023 : PrimeValue := ⟨195023, pr195023⟩
private theorem pr195043 : PrimeCertificate 195043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv32507]) (by decide +kernel)
def pv195043 : PrimeValue := ⟨195043, pr195043⟩
private theorem pr195053 : PrimeCertificate 195053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13,pv31]) (by decide +kernel)
def pv195053 : PrimeValue := ⟨195053, pr195053⟩
private theorem pr195071 : PrimeCertificate 195071 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv19507]) (by decide +kernel)
def pv195071 : PrimeValue := ⟨195071, pr195071⟩
private theorem pr195089 : PrimeCertificate 195089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv89,pv137]) (by decide +kernel)
def pv195089 : PrimeValue := ⟨195089, pr195089⟩
private theorem pr195121 : PrimeCertificate 195121 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv271]) (by decide +kernel)
def pv195121 : PrimeValue := ⟨195121, pr195121⟩
private theorem pr195131 : PrimeCertificate 195131 :=
  certifyPrime (q := pv41) (ls := [pv2,pv5,pv13,pv19,pv79]) (by decide +kernel)
def pv195131 : PrimeValue := ⟨195131, pr195131⟩
private theorem pr195157 : PrimeCertificate 195157 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv139]) (by decide +kernel)
def pv195157 : PrimeValue := ⟨195157, pr195157⟩
private theorem pr195161 : PrimeCertificate 195161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv17,pv41]) (by decide +kernel)
def pv195161 : PrimeValue := ⟨195161, pr195161⟩
private theorem pr195163 : PrimeCertificate 195163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv2957]) (by decide +kernel)
def pv195163 : PrimeValue := ⟨195163, pr195163⟩
private theorem pr195193 : PrimeCertificate 195193 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv2711]) (by decide +kernel)
def pv195193 : PrimeValue := ⟨195193, pr195193⟩
private theorem pr195197 : PrimeCertificate 195197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv48799]) (by decide +kernel)
def pv195197 : PrimeValue := ⟨195197, pr195197⟩
private theorem pr195203 : PrimeCertificate 195203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv73,pv191]) (by decide +kernel)
def pv195203 : PrimeValue := ⟨195203, pr195203⟩
private theorem pr195229 : PrimeCertificate 195229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv17,pv29]) (by decide +kernel)
def pv195229 : PrimeValue := ⟨195229, pr195229⟩
private theorem pr195241 : PrimeCertificate 195241 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv1627]) (by decide +kernel)
def pv195241 : PrimeValue := ⟨195241, pr195241⟩
private theorem pr195253 : PrimeCertificate 195253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53,pv307]) (by decide +kernel)
def pv195253 : PrimeValue := ⟨195253, pr195253⟩
private theorem pr195259 : PrimeCertificate 195259 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv4649]) (by decide +kernel)
def pv195259 : PrimeValue := ⟨195259, pr195259⟩
private theorem pr195311 : PrimeCertificate 195311 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv19531]) (by decide +kernel)
def pv195311 : PrimeValue := ⟨195311, pr195311⟩
private theorem pr195329 : PrimeCertificate 195329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv109]) (by decide +kernel)
def pv195329 : PrimeValue := ⟨195329, pr195329⟩
private theorem pr195341 : PrimeCertificate 195341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv9767]) (by decide +kernel)
def pv195341 : PrimeValue := ⟨195341, pr195341⟩
private theorem pr195343 : PrimeCertificate 195343 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv4651]) (by decide +kernel)
def pv195343 : PrimeValue := ⟨195343, pr195343⟩
private theorem pr195353 : PrimeCertificate 195353 :=
  certifyPrime (q := pv3) (ls := [pv2,pv24419]) (by decide +kernel)
def pv195353 : PrimeValue := ⟨195353, pr195353⟩
private theorem pr195401 : PrimeCertificate 195401 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv977]) (by decide +kernel)
def pv195401 : PrimeValue := ⟨195401, pr195401⟩
private theorem pr195407 : PrimeCertificate 195407 :=
  certifyPrime (q := pv5) (ls := [pv2,pv41,pv2383]) (by decide +kernel)
def pv195407 : PrimeValue := ⟨195407, pr195407⟩
private theorem pr195443 : PrimeCertificate 195443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv7517]) (by decide +kernel)
def pv195443 : PrimeValue := ⟨195443, pr195443⟩
private theorem pr195469 : PrimeCertificate 195469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv179]) (by decide +kernel)
def pv195469 : PrimeValue := ⟨195469, pr195469⟩
private theorem pr195479 : PrimeCertificate 195479 :=
  certifyPrime (q := pv7) (ls := [pv2,pv43,pv2273]) (by decide +kernel)
def pv195479 : PrimeValue := ⟨195479, pr195479⟩
private theorem pr195493 : PrimeCertificate 195493 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv1481]) (by decide +kernel)
def pv195493 : PrimeValue := ⟨195493, pr195493⟩
private theorem pr195527 : PrimeCertificate 195527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv59,pv1657]) (by decide +kernel)
def pv195527 : PrimeValue := ⟨195527, pr195527⟩
private theorem pr195539 : PrimeCertificate 195539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13967]) (by decide +kernel)
def pv195539 : PrimeValue := ⟨195539, pr195539⟩
private theorem pr195581 : PrimeCertificate 195581 :=
  certifyPrime (q := pv59) (ls := [pv2,pv5,pv7,pv11,pv127]) (by decide +kernel)
def pv195581 : PrimeValue := ⟨195581, pr195581⟩
private theorem pr195599 : PrimeCertificate 195599 :=
  certifyPrime (q := pv17) (ls := [pv2,pv13,pv7523]) (by decide +kernel)
def pv195599 : PrimeValue := ⟨195599, pr195599⟩
private theorem pr195677 : PrimeCertificate 195677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv53,pv71]) (by decide +kernel)
def pv195677 : PrimeValue := ⟨195677, pr195677⟩
private theorem pr195691 : PrimeCertificate 195691 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv593]) (by decide +kernel)
def pv195691 : PrimeValue := ⟨195691, pr195691⟩
private theorem pr195697 : PrimeCertificate 195697 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv151]) (by decide +kernel)
def pv195697 : PrimeValue := ⟨195697, pr195697⟩
private theorem pr195731 : PrimeCertificate 195731 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv23,pv37]) (by decide +kernel)
def pv195731 : PrimeValue := ⟨195731, pr195731⟩
private theorem pr195733 : PrimeCertificate 195733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5437]) (by decide +kernel)
def pv195733 : PrimeValue := ⟨195733, pr195733⟩
private theorem pr195737 : PrimeCertificate 195737 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43,pv569]) (by decide +kernel)
def pv195737 : PrimeValue := ⟨195737, pr195737⟩
private theorem pr195739 : PrimeCertificate 195739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv19,pv101]) (by decide +kernel)
def pv195739 : PrimeValue := ⟨195739, pr195739⟩
private theorem pr195743 : PrimeCertificate 195743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv97871]) (by decide +kernel)
def pv195743 : PrimeValue := ⟨195743, pr195743⟩
private theorem pr195751 : PrimeCertificate 195751 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv29]) (by decide +kernel)
def pv195751 : PrimeValue := ⟨195751, pr195751⟩
private theorem pr195781 : PrimeCertificate 195781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv251]) (by decide +kernel)
def pv195781 : PrimeValue := ⟨195781, pr195781⟩
private theorem pr195787 : PrimeCertificate 195787 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv73,pv149]) (by decide +kernel)
def pv195787 : PrimeValue := ⟨195787, pr195787⟩
private theorem pr195809 : PrimeCertificate 195809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv211]) (by decide +kernel)
def pv195809 : PrimeValue := ⟨195809, pr195809⟩
private theorem pr195817 : PrimeCertificate 195817 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv41,pv199]) (by decide +kernel)
def pv195817 : PrimeValue := ⟨195817, pr195817⟩
private theorem pr195869 : PrimeCertificate 195869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv2129]) (by decide +kernel)
def pv195869 : PrimeValue := ⟨195869, pr195869⟩
private theorem pr195883 : PrimeCertificate 195883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv32647]) (by decide +kernel)
def pv195883 : PrimeValue := ⟨195883, pr195883⟩
private theorem pr195893 : PrimeCertificate 195893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv48973]) (by decide +kernel)
def pv195893 : PrimeValue := ⟨195893, pr195893⟩
private theorem pr195913 : PrimeCertificate 195913 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv907]) (by decide +kernel)
def pv195913 : PrimeValue := ⟨195913, pr195913⟩
private theorem pr195919 : PrimeCertificate 195919 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv32653]) (by decide +kernel)
def pv195919 : PrimeValue := ⟨195919, pr195919⟩
private theorem pr195929 : PrimeCertificate 195929 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv1289]) (by decide +kernel)
def pv195929 : PrimeValue := ⟨195929, pr195929⟩
private theorem pr195931 : PrimeCertificate 195931 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv311]) (by decide +kernel)
def pv195931 : PrimeValue := ⟨195931, pr195931⟩
private theorem pr195967 : PrimeCertificate 195967 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv191]) (by decide +kernel)
def pv195967 : PrimeValue := ⟨195967, pr195967⟩
private theorem pr195971 : PrimeCertificate 195971 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv19597]) (by decide +kernel)
def pv195971 : PrimeValue := ⟨195971, pr195971⟩
private theorem pr195973 : PrimeCertificate 195973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv2333]) (by decide +kernel)
def pv195973 : PrimeValue := ⟨195973, pr195973⟩
private theorem pr195997 : PrimeCertificate 195997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv16333]) (by decide +kernel)
def pv195997 : PrimeValue := ⟨195997, pr195997⟩
private theorem pr196003 : PrimeCertificate 196003 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv10889]) (by decide +kernel)
def pv196003 : PrimeValue := ⟨196003, pr196003⟩
private theorem pr196033 : PrimeCertificate 196033 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv1021]) (by decide +kernel)
def pv196033 : PrimeValue := ⟨196033, pr196033⟩
private theorem pr196039 : PrimeCertificate 196039 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv10891]) (by decide +kernel)
def pv196039 : PrimeValue := ⟨196039, pr196039⟩
private theorem pr196043 : PrimeCertificate 196043 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11,pv19,pv67]) (by decide +kernel)
def pv196043 : PrimeValue := ⟨196043, pr196043⟩
private theorem pr196051 : PrimeCertificate 196051 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv1307]) (by decide +kernel)
def pv196051 : PrimeValue := ⟨196051, pr196051⟩
private theorem pr196087 : PrimeCertificate 196087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv2971]) (by decide +kernel)
def pv196087 : PrimeValue := ⟨196087, pr196087⟩
private theorem pr196111 : PrimeCertificate 196111 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv2179]) (by decide +kernel)
def pv196111 : PrimeValue := ⟨196111, pr196111⟩
private theorem pr196139 : PrimeCertificate 196139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv281,pv349]) (by decide +kernel)
def pv196139 : PrimeValue := ⟨196139, pr196139⟩
private theorem pr196169 : PrimeCertificate 196169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv31,pv113]) (by decide +kernel)
def pv196169 : PrimeValue := ⟨196169, pr196169⟩
private theorem pr196171 : PrimeCertificate 196171 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv13,pv503]) (by decide +kernel)
def pv196171 : PrimeValue := ⟨196171, pr196171⟩
private theorem pr196181 : PrimeCertificate 196181 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17,pv577]) (by decide +kernel)
def pv196181 : PrimeValue := ⟨196181, pr196181⟩
private theorem pr196193 : PrimeCertificate 196193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv6131]) (by decide +kernel)
def pv196193 : PrimeValue := ⟨196193, pr196193⟩
private theorem pr196201 : PrimeCertificate 196201 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv109]) (by decide +kernel)
def pv196201 : PrimeValue := ⟨196201, pr196201⟩
private theorem pr196247 : PrimeCertificate 196247 :=
  certifyPrime (q := pv5) (ls := [pv2,pv98123]) (by decide +kernel)
def pv196247 : PrimeValue := ⟨196247, pr196247⟩
private theorem pr196271 : PrimeCertificate 196271 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv19,pv1033]) (by decide +kernel)
def pv196271 : PrimeValue := ⟨196271, pr196271⟩
private theorem pr196291 : PrimeCertificate 196291 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv727]) (by decide +kernel)
def pv196291 : PrimeValue := ⟨196291, pr196291⟩
private theorem pr196307 : PrimeCertificate 196307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv8923]) (by decide +kernel)
def pv196307 : PrimeValue := ⟨196307, pr196307⟩
private theorem pr196331 : PrimeCertificate 196331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29,pv677]) (by decide +kernel)
def pv196331 : PrimeValue := ⟨196331, pr196331⟩
private theorem pr196337 : PrimeCertificate 196337 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv1753]) (by decide +kernel)
def pv196337 : PrimeValue := ⟨196337, pr196337⟩
private theorem pr196379 : PrimeCertificate 196379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv83]) (by decide +kernel)
def pv196379 : PrimeValue := ⟨196379, pr196379⟩
private theorem pr196387 : PrimeCertificate 196387 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv71,pv461]) (by decide +kernel)
def pv196387 : PrimeValue := ⟨196387, pr196387⟩
private theorem pr196429 : PrimeCertificate 196429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv16369]) (by decide +kernel)
def pv196429 : PrimeValue := ⟨196429, pr196429⟩
private theorem pr196439 : PrimeCertificate 196439 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv8929]) (by decide +kernel)
def pv196439 : PrimeValue := ⟨196439, pr196439⟩
private theorem pr196453 : PrimeCertificate 196453 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv107]) (by decide +kernel)
def pv196453 : PrimeValue := ⟨196453, pr196453⟩
private theorem pr196519 : PrimeCertificate 196519 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv4679]) (by decide +kernel)
def pv196519 : PrimeValue := ⟨196519, pr196519⟩
private theorem pr196523 : PrimeCertificate 196523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv97,pv1013]) (by decide +kernel)
def pv196523 : PrimeValue := ⟨196523, pr196523⟩
private theorem pr196541 : PrimeCertificate 196541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31,pv317]) (by decide +kernel)
def pv196541 : PrimeValue := ⟨196541, pr196541⟩
private theorem pr196543 : PrimeCertificate 196543 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv61,pv179]) (by decide +kernel)
def pv196543 : PrimeValue := ⟨196543, pr196543⟩
private theorem pr196549 : PrimeCertificate 196549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv1489]) (by decide +kernel)
def pv196549 : PrimeValue := ⟨196549, pr196549⟩
private theorem pr196583 : PrimeCertificate 196583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv227,pv433]) (by decide +kernel)
def pv196583 : PrimeValue := ⟨196583, pr196583⟩
private theorem pr196597 : PrimeCertificate 196597 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv43,pv127]) (by decide +kernel)
def pv196597 : PrimeValue := ⟨196597, pr196597⟩
private theorem pr196643 : PrimeCertificate 196643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv98321]) (by decide +kernel)
def pv196643 : PrimeValue := ⟨196643, pr196643⟩
private theorem pr196657 : PrimeCertificate 196657 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv241]) (by decide +kernel)
def pv196657 : PrimeValue := ⟨196657, pr196657⟩
private theorem pr196663 : PrimeCertificate 196663 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv73,pv449]) (by decide +kernel)
def pv196663 : PrimeValue := ⟨196663, pr196663⟩
private theorem pr196681 : PrimeCertificate 196681 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv11,pv149]) (by decide +kernel)
def pv196681 : PrimeValue := ⟨196681, pr196681⟩
private theorem pr196687 : PrimeCertificate 196687 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv223]) (by decide +kernel)
def pv196687 : PrimeValue := ⟨196687, pr196687⟩
private theorem pr196709 : PrimeCertificate 196709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv49177]) (by decide +kernel)
def pv196709 : PrimeValue := ⟨196709, pr196709⟩
private theorem pr196717 : PrimeCertificate 196717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv97]) (by decide +kernel)
def pv196717 : PrimeValue := ⟨196717, pr196717⟩
private theorem pr196739 : PrimeCertificate 196739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv98369]) (by decide +kernel)
def pv196739 : PrimeValue := ⟨196739, pr196739⟩
private theorem pr196751 : PrimeCertificate 196751 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv787]) (by decide +kernel)
def pv196751 : PrimeValue := ⟨196751, pr196751⟩
private theorem pr196769 : PrimeCertificate 196769 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv13,pv43]) (by decide +kernel)
def pv196769 : PrimeValue := ⟨196769, pr196769⟩
private theorem pr196771 : PrimeCertificate 196771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv937]) (by decide +kernel)
def pv196771 : PrimeValue := ⟨196771, pr196771⟩
private theorem pr196799 : PrimeCertificate 196799 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv14057]) (by decide +kernel)
def pv196799 : PrimeValue := ⟨196799, pr196799⟩
private theorem pr196817 : PrimeCertificate 196817 :=
  certifyPrime (q := pv3) (ls := [pv2,pv12301]) (by decide +kernel)
def pv196817 : PrimeValue := ⟨196817, pr196817⟩
private theorem pr196831 : PrimeCertificate 196831 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv196831 : PrimeValue := ⟨196831, pr196831⟩
private theorem pr196837 : PrimeCertificate 196837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv349]) (by decide +kernel)
def pv196837 : PrimeValue := ⟨196837, pr196837⟩
private theorem pr196853 : PrimeCertificate 196853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv1697]) (by decide +kernel)
def pv196853 : PrimeValue := ⟨196853, pr196853⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
