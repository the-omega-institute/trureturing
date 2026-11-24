/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table140
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table140.pv1090013
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table020
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table030
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table031
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table040
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table041
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table115
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table116

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr1090013 : Nat.Prime 1090013 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv11,pv3539]) (by decide +kernel)
def pv1090013 : PrimeValue := ⟨1090013, pr1090013⟩
private theorem pr1090151 : Nat.Prime 1090151 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv5,pv21803]) (by decide +kernel)
def pv1090151 : PrimeValue := ⟨1090151, pr1090151⟩
private theorem pr1090373 : Nat.Prime 1090373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv14347]) (by decide +kernel)
def pv1090373 : PrimeValue := ⟨1090373, pr1090373⟩
private theorem pr1090403 : Nat.Prime 1090403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv457,pv1193]) (by decide +kernel)
def pv1090403 : PrimeValue := ⟨1090403, pr1090403⟩
private theorem pr1090613 : Nat.Prime 1090613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv7369]) (by decide +kernel)
def pv1090613 : PrimeValue := ⟨1090613, pr1090613⟩
private theorem pr1090709 : Nat.Prime 1090709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv257,pv1061]) (by decide +kernel)
def pv1090709 : PrimeValue := ⟨1090709, pr1090709⟩
private theorem pr1090769 : Nat.Prime 1090769 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv9739]) (by decide +kernel)
def pv1090769 : PrimeValue := ⟨1090769, pr1090769⟩
private theorem pr1091003 : Nat.Prime 1091003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv101,pv491]) (by decide +kernel)
def pv1091003 : PrimeValue := ⟨1091003, pr1091003⟩
private theorem pr1092023 : Nat.Prime 1092023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv61,pv8951]) (by decide +kernel)
def pv1092023 : PrimeValue := ⟨1092023, pr1092023⟩
private theorem pr1092089 : Nat.Prime 1092089 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv136511]) (by decide +kernel)
def pv1092089 : PrimeValue := ⟨1092089, pr1092089⟩
private theorem pr1092251 : Nat.Prime 1092251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv257]) (by decide +kernel)
def pv1092251 : PrimeValue := ⟨1092251, pr1092251⟩
private theorem pr1092389 : Nat.Prime 1092389 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv37,pv61]) (by decide +kernel)
def pv1092389 : PrimeValue := ⟨1092389, pr1092389⟩
private theorem pr1092593 : Nat.Prime 1092593 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv2969]) (by decide +kernel)
def pv1092593 : PrimeValue := ⟨1092593, pr1092593⟩
private theorem pr1092713 : Nat.Prime 1092713 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv137,pv997]) (by decide +kernel)
def pv1092713 : PrimeValue := ⟨1092713, pr1092713⟩
private theorem pr1092863 : Nat.Prime 1092863 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv32143]) (by decide +kernel)
def pv1092863 : PrimeValue := ⟨1092863, pr1092863⟩
private theorem pr1093283 : Nat.Prime 1093283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv23767]) (by decide +kernel)
def pv1093283 : PrimeValue := ⟨1093283, pr1093283⟩
private theorem pr1093289 : Nat.Prime 1093289 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv2789]) (by decide +kernel)
def pv1093289 : PrimeValue := ⟨1093289, pr1093289⟩
private theorem pr1093679 : Nat.Prime 1093679 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv17,pv19,pv1693]) (by decide +kernel)
def pv1093679 : PrimeValue := ⟨1093679, pr1093679⟩
private theorem pr1093871 : Nat.Prime 1093871 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv109387]) (by decide +kernel)
def pv1093871 : PrimeValue := ⟨1093871, pr1093871⟩
private theorem pr1094081 : Nat.Prime 1094081 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv13,pv263]) (by decide +kernel)
def pv1094081 : PrimeValue := ⟨1094081, pr1094081⟩
private theorem pr1094339 : Nat.Prime 1094339 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv78167]) (by decide +kernel)
def pv1094339 : PrimeValue := ⟨1094339, pr1094339⟩
private theorem pr1094531 : Nat.Prime 1094531 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv109453]) (by decide +kernel)
def pv1094531 : PrimeValue := ⟨1094531, pr1094531⟩
private theorem pr1094573 : Nat.Prime 1094573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv273643]) (by decide +kernel)
def pv1094573 : PrimeValue := ⟨1094573, pr1094573⟩
private theorem pr1094603 : Nat.Prime 1094603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv547301]) (by decide +kernel)
def pv1094603 : PrimeValue := ⟨1094603, pr1094603⟩
private theorem pr1094633 : Nat.Prime 1094633 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv11,pv1777]) (by decide +kernel)
def pv1094633 : PrimeValue := ⟨1094633, pr1094633⟩
private theorem pr1094669 : Nat.Prime 1094669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv211,pv1297]) (by decide +kernel)
def pv1094669 : PrimeValue := ⟨1094669, pr1094669⟩
private theorem pr1094921 : Nat.Prime 1094921 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv31,pv883]) (by decide +kernel)
def pv1094921 : PrimeValue := ⟨1094921, pr1094921⟩
private theorem pr1094939 : Nat.Prime 1094939 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv23,pv1831]) (by decide +kernel)
def pv1094939 : PrimeValue := ⟨1094939, pr1094939⟩
private theorem pr1094969 : Nat.Prime 1094969 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv19553]) (by decide +kernel)
def pv1094969 : PrimeValue := ⟨1094969, pr1094969⟩
private theorem pr1095023 : Nat.Prime 1095023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv601,pv911]) (by decide +kernel)
def pv1095023 : PrimeValue := ⟨1095023, pr1095023⟩
private theorem pr1095071 : Nat.Prime 1095071 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv109507]) (by decide +kernel)
def pv1095071 : PrimeValue := ⟨1095071, pr1095071⟩
private theorem pr1095173 : Nat.Prime 1095173 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv21061]) (by decide +kernel)
def pv1095173 : PrimeValue := ⟨1095173, pr1095173⟩
private theorem pr1095239 : Nat.Prime 1095239 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv547619]) (by decide +kernel)
def pv1095239 : PrimeValue := ⟨1095239, pr1095239⟩
private theorem pr1095443 : Nat.Prime 1095443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv421,pv1301]) (by decide +kernel)
def pv1095443 : PrimeValue := ⟨1095443, pr1095443⟩
private theorem pr1095491 : Nat.Prime 1095491 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv11,pv23,pv433]) (by decide +kernel)
def pv1095491 : PrimeValue := ⟨1095491, pr1095491⟩
private theorem pr1095791 : Nat.Prime 1095791 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv109579]) (by decide +kernel)
def pv1095791 : PrimeValue := ⟨1095791, pr1095791⟩
private theorem pr1095851 : Nat.Prime 1095851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv31,pv101]) (by decide +kernel)
def pv1095851 : PrimeValue := ⟨1095851, pr1095851⟩
private theorem pr1096031 : Nat.Prime 1096031 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv13,pv8431]) (by decide +kernel)
def pv1096031 : PrimeValue := ⟨1096031, pr1096031⟩
private theorem pr1096061 : Nat.Prime 1096061 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv7829]) (by decide +kernel)
def pv1096061 : PrimeValue := ⟨1096061, pr1096061⟩
private theorem pr1096163 : Nat.Prime 1096163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv14813]) (by decide +kernel)
def pv1096163 : PrimeValue := ⟨1096163, pr1096163⟩
private theorem pr1096289 : Nat.Prime 1096289 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv34259]) (by decide +kernel)
def pv1096289 : PrimeValue := ⟨1096289, pr1096289⟩
private theorem pr1096373 : Nat.Prime 1096373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv274093]) (by decide +kernel)
def pv1096373 : PrimeValue := ⟨1096373, pr1096373⟩
private theorem pr1096481 : Nat.Prime 1096481 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv11,pv89]) (by decide +kernel)
def pv1096481 : PrimeValue := ⟨1096481, pr1096481⟩
private theorem pr1096583 : Nat.Prime 1096583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv548291]) (by decide +kernel)
def pv1096583 : PrimeValue := ⟨1096583, pr1096583⟩
private theorem pr1096631 : Nat.Prime 1096631 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv109663]) (by decide +kernel)
def pv1096631 : PrimeValue := ⟨1096631, pr1096631⟩
private theorem pr1096691 : Nat.Prime 1096691 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv7,pv15667]) (by decide +kernel)
def pv1096691 : PrimeValue := ⟨1096691, pr1096691⟩
private theorem pr1096853 : Nat.Prime 1096853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv274213]) (by decide +kernel)
def pv1096853 : PrimeValue := ⟨1096853, pr1096853⟩
private theorem pr1097009 : Nat.Prime 1097009 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv11,pv23,pv271]) (by decide +kernel)
def pv1097009 : PrimeValue := ⟨1097009, pr1097009⟩
private theorem pr1097423 : Nat.Prime 1097423 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv23,pv23857]) (by decide +kernel)
def pv1097423 : PrimeValue := ⟨1097423, pr1097423⟩
private theorem pr1097441 : Nat.Prime 1097441 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv19]) (by decide +kernel)
def pv1097441 : PrimeValue := ⟨1097441, pr1097441⟩
private theorem pr1097483 : Nat.Prime 1097483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv73,pv7517]) (by decide +kernel)
def pv1097483 : PrimeValue := ⟨1097483, pr1097483⟩
private theorem pr1097501 : Nat.Prime 1097501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv439]) (by decide +kernel)
def pv1097501 : PrimeValue := ⟨1097501, pr1097501⟩
private theorem pr1097669 : Nat.Prime 1097669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv13,pv19,pv101]) (by decide +kernel)
def pv1097669 : PrimeValue := ⟨1097669, pr1097669⟩
private theorem pr1097699 : Nat.Prime 1097699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv23,pv487]) (by decide +kernel)
def pv1097699 : PrimeValue := ⟨1097699, pr1097699⟩
private theorem pr1097861 : Nat.Prime 1097861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv3229]) (by decide +kernel)
def pv1097861 : PrimeValue := ⟨1097861, pr1097861⟩
private theorem pr1097879 : Nat.Prime 1097879 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv61,pv8999]) (by decide +kernel)
def pv1097879 : PrimeValue := ⟨1097879, pr1097879⟩
private theorem pr1097909 : Nat.Prime 1097909 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv113,pv347]) (by decide +kernel)
def pv1097909 : PrimeValue := ⟨1097909, pr1097909⟩
private theorem pr1097933 : Nat.Prime 1097933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv24953]) (by decide +kernel)
def pv1097933 : PrimeValue := ⟨1097933, pr1097933⟩
private theorem pr1098203 : Nat.Prime 1098203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv47,pv1669]) (by decide +kernel)
def pv1098203 : PrimeValue := ⟨1098203, pr1098203⟩
private theorem pr1098269 : Nat.Prime 1098269 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv31,pv521]) (by decide +kernel)
def pv1098269 : PrimeValue := ⟨1098269, pr1098269⟩
private theorem pr1098479 : Nat.Prime 1098479 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv43,pv53,pv241]) (by decide +kernel)
def pv1098479 : PrimeValue := ⟨1098479, pr1098479⟩
private theorem pr1098731 : Nat.Prime 1098731 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv109873]) (by decide +kernel)
def pv1098731 : PrimeValue := ⟨1098731, pr1098731⟩
private theorem pr1098953 : Nat.Prime 1098953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv137369]) (by decide +kernel)
def pv1098953 : PrimeValue := ⟨1098953, pr1098953⟩
private theorem pr1099079 : Nat.Prime 1099079 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv23,pv23893]) (by decide +kernel)
def pv1099079 : PrimeValue := ⟨1099079, pr1099079⟩
private theorem pr1099223 : Nat.Prime 1099223 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv71,pv7741]) (by decide +kernel)
def pv1099223 : PrimeValue := ⟨1099223, pr1099223⟩
private theorem pr1099391 : Nat.Prime 1099391 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv17,pv29,pv223]) (by decide +kernel)
def pv1099391 : PrimeValue := ⟨1099391, pr1099391⟩
private theorem pr1099421 : Nat.Prime 1099421 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv7853]) (by decide +kernel)
def pv1099421 : PrimeValue := ⟨1099421, pr1099421⟩
private theorem pr1099589 : Nat.Prime 1099589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv173,pv227]) (by decide +kernel)
def pv1099589 : PrimeValue := ⟨1099589, pr1099589⟩
private theorem pr1099649 : Nat.Prime 1099649 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv71]) (by decide +kernel)
def pv1099649 : PrimeValue := ⟨1099649, pr1099649⟩
private theorem pr1099841 : Nat.Prime 1099841 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv7,pv491]) (by decide +kernel)
def pv1099841 : PrimeValue := ⟨1099841, pr1099841⟩
private theorem pr1099859 : Nat.Prime 1099859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv379,pv1451]) (by decide +kernel)
def pv1099859 : PrimeValue := ⟨1099859, pr1099859⟩
private theorem pr1100051 : Nat.Prime 1100051 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv449]) (by decide +kernel)
def pv1100051 : PrimeValue := ⟨1100051, pr1100051⟩
private theorem pr1100321 : Nat.Prime 1100321 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv23]) (by decide +kernel)
def pv1100321 : PrimeValue := ⟨1100321, pr1100321⟩
private theorem pr1100381 : Nat.Prime 1100381 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv37,pv1487]) (by decide +kernel)
def pv1100381 : PrimeValue := ⟨1100381, pr1100381⟩
private theorem pr1100471 : Nat.Prime 1100471 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv79,pv199]) (by decide +kernel)
def pv1100471 : PrimeValue := ⟨1100471, pr1100471⟩
private theorem pr1100483 : Nat.Prime 1100483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv550241]) (by decide +kernel)
def pv1100483 : PrimeValue := ⟨1100483, pr1100483⟩
private theorem pr1100591 : Nat.Prime 1100591 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv110059]) (by decide +kernel)
def pv1100591 : PrimeValue := ⟨1100591, pr1100591⟩
private theorem pr1101143 : Nat.Prime 1101143 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv78653]) (by decide +kernel)
def pv1101143 : PrimeValue := ⟨1101143, pr1101143⟩
private theorem pr1101179 : Nat.Prime 1101179 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv13,pv41,pv1033]) (by decide +kernel)
def pv1101179 : PrimeValue := ⟨1101179, pr1101179⟩
private theorem pr1101473 : Nat.Prime 1101473 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv34421]) (by decide +kernel)
def pv1101473 : PrimeValue := ⟨1101473, pr1101473⟩
private theorem pr1101839 : Nat.Prime 1101839 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv17,pv23,pv1409]) (by decide +kernel)
def pv1101839 : PrimeValue := ⟨1101839, pr1101839⟩
private theorem pr1102001 : Nat.Prime 1102001 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv19,pv29]) (by decide +kernel)
def pv1102001 : PrimeValue := ⟨1102001, pr1102001⟩
private theorem pr1102163 : Nat.Prime 1102163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv13441]) (by decide +kernel)
def pv1102163 : PrimeValue := ⟨1102163, pr1102163⟩
private theorem pr1102253 : Nat.Prime 1102253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv11981]) (by decide +kernel)
def pv1102253 : PrimeValue := ⟨1102253, pr1102253⟩
private theorem pr1102301 : Nat.Prime 1102301 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv73,pv151]) (by decide +kernel)
def pv1102301 : PrimeValue := ⟨1102301, pr1102301⟩
private theorem pr1102553 : Nat.Prime 1102553 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv17,pv67]) (by decide +kernel)
def pv1102553 : PrimeValue := ⟨1102553, pr1102553⟩
private theorem pr1102583 : Nat.Prime 1102583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv42407]) (by decide +kernel)
def pv1102583 : PrimeValue := ⟨1102583, pr1102583⟩
private theorem pr1102901 : Nat.Prime 1102901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv41,pv269]) (by decide +kernel)
def pv1102901 : PrimeValue := ⟨1102901, pr1102901⟩
private theorem pr1103279 : Nat.Prime 1103279 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv47,pv97]) (by decide +kernel)
def pv1103279 : PrimeValue := ⟨1103279, pr1103279⟩
private theorem pr1103309 : Nat.Prime 1103309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv275827]) (by decide +kernel)
def pv1103309 : PrimeValue := ⟨1103309, pr1103309⟩
private theorem pr1103519 : Nat.Prime 1103519 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv13,pv42443]) (by decide +kernel)
def pv1103519 : PrimeValue := ⟨1103519, pr1103519⟩
private theorem pr1103549 : Nat.Prime 1103549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv263,pv1049]) (by decide +kernel)
def pv1103549 : PrimeValue := ⟨1103549, pr1103549⟩
private theorem pr1103561 : Nat.Prime 1103561 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv47,pv587]) (by decide +kernel)
def pv1103561 : PrimeValue := ⟨1103561, pr1103561⟩
private theorem pr1103579 : Nat.Prime 1103579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11261]) (by decide +kernel)
def pv1103579 : PrimeValue := ⟨1103579, pr1103579⟩
private theorem pr1103621 : Nat.Prime 1103621 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv7883]) (by decide +kernel)
def pv1103621 : PrimeValue := ⟨1103621, pr1103621⟩
private theorem pr1103639 : Nat.Prime 1103639 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv41,pv43,pv313]) (by decide +kernel)
def pv1103639 : PrimeValue := ⟨1103639, pr1103639⟩
private theorem pr1103981 : Nat.Prime 1103981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv191]) (by decide +kernel)
def pv1103981 : PrimeValue := ⟨1103981, pr1103981⟩
private theorem pr1104041 : Nat.Prime 1104041 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv3943]) (by decide +kernel)
def pv1104041 : PrimeValue := ⟨1104041, pr1104041⟩
private theorem pr1104101 : Nat.Prime 1104101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv61,pv181]) (by decide +kernel)
def pv1104101 : PrimeValue := ⟨1104101, pr1104101⟩
private theorem pr1104203 : Nat.Prime 1104203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv53,pv947]) (by decide +kernel)
def pv1104203 : PrimeValue := ⟨1104203, pr1104203⟩
private theorem pr1104353 : Nat.Prime 1104353 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv34511]) (by decide +kernel)
def pv1104353 : PrimeValue := ⟨1104353, pr1104353⟩
private theorem pr1104671 : Nat.Prime 1104671 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv43,pv367]) (by decide +kernel)
def pv1104671 : PrimeValue := ⟨1104671, pr1104671⟩
private theorem pr1104749 : Nat.Prime 1104749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv276187]) (by decide +kernel)
def pv1104749 : PrimeValue := ⟨1104749, pr1104749⟩
private theorem pr1104833 : Nat.Prime 1104833 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv61,pv283]) (by decide +kernel)
def pv1104833 : PrimeValue := ⟨1104833, pr1104833⟩
private theorem pr1105193 : Nat.Prime 1105193 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv19,pv661]) (by decide +kernel)
def pv1105193 : PrimeValue := ⟨1105193, pr1105193⟩
private theorem pr1105589 : Nat.Prime 1105589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv25127]) (by decide +kernel)
def pv1105589 : PrimeValue := ⟨1105589, pr1105589⟩
private theorem pr1105613 : Nat.Prime 1105613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv71,pv229]) (by decide +kernel)
def pv1105613 : PrimeValue := ⟨1105613, pr1105613⟩
private theorem pr1105823 : Nat.Prime 1105823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv719,pv769]) (by decide +kernel)
def pv1105823 : PrimeValue := ⟨1105823, pr1105823⟩
private theorem pr1106243 : Nat.Prime 1106243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv73,pv7577]) (by decide +kernel)
def pv1106243 : PrimeValue := ⟨1106243, pr1106243⟩
private theorem pr1106489 : Nat.Prime 1106489 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv138311]) (by decide +kernel)
def pv1106489 : PrimeValue := ⟨1106489, pr1106489⟩
private theorem pr1106621 : Nat.Prime 1106621 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv55331]) (by decide +kernel)
def pv1106621 : PrimeValue := ⟨1106621, pr1106621⟩
private theorem pr1107479 : Nat.Prime 1107479 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv157,pv3527]) (by decide +kernel)
def pv1107479 : PrimeValue := ⟨1107479, pr1107479⟩
private theorem pr1107581 : Nat.Prime 1107581 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv79,pv701]) (by decide +kernel)
def pv1107581 : PrimeValue := ⟨1107581, pr1107581⟩
private theorem pr1107773 : Nat.Prime 1107773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv12041]) (by decide +kernel)
def pv1107773 : PrimeValue := ⟨1107773, pr1107773⟩
private theorem pr1107791 : Nat.Prime 1107791 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv47,pv2357]) (by decide +kernel)
def pv1107791 : PrimeValue := ⟨1107791, pr1107791⟩
private theorem pr1107923 : Nat.Prime 1107923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv553961]) (by decide +kernel)
def pv1107923 : PrimeValue := ⟨1107923, pr1107923⟩
private theorem pr1107989 : Nat.Prime 1107989 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv5653]) (by decide +kernel)
def pv1107989 : PrimeValue := ⟨1107989, pr1107989⟩
private theorem pr1108181 : Nat.Prime 1108181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv67,pv827]) (by decide +kernel)
def pv1108181 : PrimeValue := ⟨1108181, pr1108181⟩
private theorem pr1108259 : Nat.Prime 1108259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv554129]) (by decide +kernel)
def pv1108259 : PrimeValue := ⟨1108259, pr1108259⟩
private theorem pr1108571 : Nat.Prime 1108571 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv17,pv6521]) (by decide +kernel)
def pv1108571 : PrimeValue := ⟨1108571, pr1108571⟩
private theorem pr1109033 : Nat.Prime 1109033 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv138629]) (by decide +kernel)
def pv1109033 : PrimeValue := ⟨1109033, pr1109033⟩
private theorem pr1109159 : Nat.Prime 1109159 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv661,pv839]) (by decide +kernel)
def pv1109159 : PrimeValue := ⟨1109159, pr1109159⟩
private theorem pr1109219 : Nat.Prime 1109219 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv127,pv397]) (by decide +kernel)
def pv1109219 : PrimeValue := ⟨1109219, pr1109219⟩
private theorem pr1109291 : Nat.Prime 1109291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv13,pv23,pv53]) (by decide +kernel)
def pv1109291 : PrimeValue := ⟨1109291, pr1109291⟩
private theorem pr1109561 : Nat.Prime 1109561 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv27739]) (by decide +kernel)
def pv1109561 : PrimeValue := ⟨1109561, pr1109561⟩
private theorem pr1109639 : Nat.Prime 1109639 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv19,pv29201]) (by decide +kernel)
def pv1109639 : PrimeValue := ⟨1109639, pr1109639⟩
private theorem pr1109903 : Nat.Prime 1109903 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv554951]) (by decide +kernel)
def pv1109903 : PrimeValue := ⟨1109903, pr1109903⟩
private theorem pr1110041 : Nat.Prime 1110041 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv27751]) (by decide +kernel)
def pv1110041 : PrimeValue := ⟨1110041, pr1110041⟩
private theorem pr1110269 : Nat.Prime 1110269 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv277567]) (by decide +kernel)
def pv1110269 : PrimeValue := ⟨1110269, pr1110269⟩
private theorem pr1110929 : Nat.Prime 1110929 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv13,pv109]) (by decide +kernel)
def pv1110929 : PrimeValue := ⟨1110929, pr1110929⟩
private theorem pr1110953 : Nat.Prime 1110953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv138869]) (by decide +kernel)
def pv1110953 : PrimeValue := ⟨1110953, pr1110953⟩
private theorem pr1110971 : Nat.Prime 1110971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv59,pv269]) (by decide +kernel)
def pv1110971 : PrimeValue := ⟨1110971, pr1110971⟩
private theorem pr1111283 : Nat.Prime 1111283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv593,pv937]) (by decide +kernel)
def pv1111283 : PrimeValue := ⟨1111283, pr1111283⟩
private theorem pr1111289 : Nat.Prime 1111289 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv4481]) (by decide +kernel)
def pv1111289 : PrimeValue := ⟨1111289, pr1111289⟩
private theorem pr1111361 : Nat.Prime 1111361 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv23,pv151]) (by decide +kernel)
def pv1111361 : PrimeValue := ⟨1111361, pr1111361⟩
private theorem pr1111559 : Nat.Prime 1111559 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv79397]) (by decide +kernel)
def pv1111559 : PrimeValue := ⟨1111559, pr1111559⟩
private theorem pr1111703 : Nat.Prime 1111703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv37,pv83,pv181]) (by decide +kernel)
def pv1111703 : PrimeValue := ⟨1111703, pr1111703⟩
private theorem pr1111793 : Nat.Prime 1111793 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv6317]) (by decide +kernel)
def pv1111793 : PrimeValue := ⟨1111793, pr1111793⟩
private theorem pr1111991 : Nat.Prime 1111991 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv11,pv919]) (by decide +kernel)
def pv1111991 : PrimeValue := ⟨1111991, pr1111991⟩
private theorem pr1112129 : Nat.Prime 1112129 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17377]) (by decide +kernel)
def pv1112129 : PrimeValue := ⟨1112129, pr1112129⟩
private theorem pr1112141 : Nat.Prime 1112141 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17,pv3271]) (by decide +kernel)
def pv1112141 : PrimeValue := ⟨1112141, pr1112141⟩
private theorem pr1112333 : Nat.Prime 1112333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv21391]) (by decide +kernel)
def pv1112333 : PrimeValue := ⟨1112333, pr1112333⟩
private theorem pr1112339 : Nat.Prime 1112339 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv457,pv1217]) (by decide +kernel)
def pv1112339 : PrimeValue := ⟨1112339, pr1112339⟩
private theorem pr1112381 : Nat.Prime 1112381 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv55619]) (by decide +kernel)
def pv1112381 : PrimeValue := ⟨1112381, pr1112381⟩
private theorem pr1112519 : Nat.Prime 1112519 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv61,pv829]) (by decide +kernel)
def pv1112519 : PrimeValue := ⟨1112519, pr1112519⟩
private theorem pr1112561 : Nat.Prime 1112561 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv13907]) (by decide +kernel)
def pv1112561 : PrimeValue := ⟨1112561, pr1112561⟩
private theorem pr1112591 : Nat.Prime 1112591 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv31,pv37,pv97]) (by decide +kernel)
def pv1112591 : PrimeValue := ⟨1112591, pr1112591⟩
private theorem pr1112789 : Nat.Prime 1112789 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv53,pv181]) (by decide +kernel)
def pv1112789 : PrimeValue := ⟨1112789, pr1112789⟩
private theorem pr1113011 : Nat.Prime 1113011 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv111301]) (by decide +kernel)
def pv1113011 : PrimeValue := ⟨1113011, pr1113011⟩
private theorem pr1113239 : Nat.Prime 1113239 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv131,pv607]) (by decide +kernel)
def pv1113239 : PrimeValue := ⟨1113239, pr1113239⟩
private theorem pr1113461 : Nat.Prime 1113461 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv55673]) (by decide +kernel)
def pv1113461 : PrimeValue := ⟨1113461, pr1113461⟩
private theorem pr1113509 : Nat.Prime 1113509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv25307]) (by decide +kernel)
def pv1113509 : PrimeValue := ⟨1113509, pr1113509⟩
private theorem pr1113719 : Nat.Prime 1113719 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv556859]) (by decide +kernel)
def pv1113719 : PrimeValue := ⟨1113719, pr1113719⟩
private theorem pr1113863 : Nat.Prime 1113863 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv556931]) (by decide +kernel)
def pv1113863 : PrimeValue := ⟨1113863, pr1113863⟩
private theorem pr1113971 : Nat.Prime 1113971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv13,pv19,pv41]) (by decide +kernel)
def pv1113971 : PrimeValue := ⟨1113971, pr1113971⟩
private theorem pr1114241 : Nat.Prime 1114241 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv1741]) (by decide +kernel)
def pv1114241 : PrimeValue := ⟨1114241, pr1114241⟩
private theorem pr1114271 : Nat.Prime 1114271 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv111427]) (by decide +kernel)
def pv1114271 : PrimeValue := ⟨1114271, pr1114271⟩
private theorem pr1114493 : Nat.Prime 1114493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv278623]) (by decide +kernel)
def pv1114493 : PrimeValue := ⟨1114493, pr1114493⟩
private theorem pr1114541 : Nat.Prime 1114541 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv19,pv419]) (by decide +kernel)
def pv1114541 : PrimeValue := ⟨1114541, pr1114541⟩
private theorem pr1114709 : Nat.Prime 1114709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv41,pv971]) (by decide +kernel)
def pv1114709 : PrimeValue := ⟨1114709, pr1114709⟩
private theorem pr1114733 : Nat.Prime 1114733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv6481]) (by decide +kernel)
def pv1114733 : PrimeValue := ⟨1114733, pr1114733⟩
private theorem pr1114829 : Nat.Prime 1114829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv13,pv1949]) (by decide +kernel)
def pv1114829 : PrimeValue := ⟨1114829, pr1114829⟩
private theorem pr1114931 : Nat.Prime 1114931 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv111493]) (by decide +kernel)
def pv1114931 : PrimeValue := ⟨1114931, pr1114931⟩
private theorem pr1115321 : Nat.Prime 1115321 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv27883]) (by decide +kernel)
def pv1115321 : PrimeValue := ⟨1115321, pr1115321⟩
private theorem pr1115363 : Nat.Prime 1115363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv24247]) (by decide +kernel)
def pv1115363 : PrimeValue := ⟨1115363, pr1115363⟩
private theorem pr1115711 : Nat.Prime 1115711 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv17,pv6563]) (by decide +kernel)
def pv1115711 : PrimeValue := ⟨1115711, pr1115711⟩
private theorem pr1115759 : Nat.Prime 1115759 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv79697]) (by decide +kernel)
def pv1115759 : PrimeValue := ⟨1115759, pr1115759⟩
private theorem pr1115843 : Nat.Prime 1115843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv13,pv6131]) (by decide +kernel)
def pv1115843 : PrimeValue := ⟨1115843, pr1115843⟩
private theorem pr1116053 : Nat.Prime 1116053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv23,pv1733]) (by decide +kernel)
def pv1116053 : PrimeValue := ⟨1116053, pr1116053⟩
private theorem pr1116701 : Nat.Prime 1116701 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv859]) (by decide +kernel)
def pv1116701 : PrimeValue := ⟨1116701, pr1116701⟩
private theorem pr1116749 : Nat.Prime 1116749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv279187]) (by decide +kernel)
def pv1116749 : PrimeValue := ⟨1116749, pr1116749⟩
private theorem pr1116893 : Nat.Prime 1116893 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv113,pv353]) (by decide +kernel)
def pv1116893 : PrimeValue := ⟨1116893, pr1116893⟩
private theorem pr1117079 : Nat.Prime 1117079 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv558539]) (by decide +kernel)
def pv1117079 : PrimeValue := ⟨1117079, pr1117079⟩
private theorem pr1117169 : Nat.Prime 1117169 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv41,pv131]) (by decide +kernel)
def pv1117169 : PrimeValue := ⟨1117169, pr1117169⟩
private theorem pr1117349 : Nat.Prime 1117349 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv279337]) (by decide +kernel)
def pv1117349 : PrimeValue := ⟨1117349, pr1117349⟩
private theorem pr1117463 : Nat.Prime 1117463 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv558731]) (by decide +kernel)
def pv1117463 : PrimeValue := ⟨1117463, pr1117463⟩
private theorem pr1117661 : Nat.Prime 1117661 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv29,pv41,pv47]) (by decide +kernel)
def pv1117661 : PrimeValue := ⟨1117661, pr1117661⟩
private theorem pr1117769 : Nat.Prime 1117769 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv139721]) (by decide +kernel)
def pv1117769 : PrimeValue := ⟨1117769, pr1117769⟩
private theorem pr1117793 : Nat.Prime 1117793 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv2687]) (by decide +kernel)
def pv1117793 : PrimeValue := ⟨1117793, pr1117793⟩
private theorem pr1117799 : Nat.Prime 1117799 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv31,pv149]) (by decide +kernel)
def pv1117799 : PrimeValue := ⟨1117799, pr1117799⟩
private theorem pr1117901 : Nat.Prime 1117901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv1597]) (by decide +kernel)
def pv1117901 : PrimeValue := ⟨1117901, pr1117901⟩
private theorem pr1117943 : Nat.Prime 1117943 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv47,pv1699]) (by decide +kernel)
def pv1117943 : PrimeValue := ⟨1117943, pr1117943⟩
private theorem pr1118003 : Nat.Prime 1118003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv559001]) (by decide +kernel)
def pv1118003 : PrimeValue := ⟨1118003, pr1118003⟩
private theorem pr1118291 : Nat.Prime 1118291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv111829]) (by decide +kernel)
def pv1118291 : PrimeValue := ⟨1118291, pr1118291⟩
private theorem pr1118723 : Nat.Prime 1118723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv211,pv241]) (by decide +kernel)
def pv1118723 : PrimeValue := ⟨1118723, pr1118723⟩
private theorem pr1118783 : Nat.Prime 1118783 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv157,pv509]) (by decide +kernel)
def pv1118783 : PrimeValue := ⟨1118783, pr1118783⟩
private theorem pr1119179 : Nat.Prime 1119179 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv32917]) (by decide +kernel)
def pv1119179 : PrimeValue := ⟨1119179, pr1119179⟩
private theorem pr1119323 : Nat.Prime 1119323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv307,pv1823]) (by decide +kernel)
def pv1119323 : PrimeValue := ⟨1119323, pr1119323⟩
private theorem pr1119389 : Nat.Prime 1119389 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv279847]) (by decide +kernel)
def pv1119389 : PrimeValue := ⟨1119389, pr1119389⟩
private theorem pr1119473 : Nat.Prime 1119473 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv37,pv61]) (by decide +kernel)
def pv1119473 : PrimeValue := ⟨1119473, pr1119473⟩
private theorem pr1119623 : Nat.Prime 1119623 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv79973]) (by decide +kernel)
def pv1119623 : PrimeValue := ⟨1119623, pr1119623⟩
private theorem pr1119659 : Nat.Prime 1119659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv18059]) (by decide +kernel)
def pv1119659 : PrimeValue := ⟨1119659, pr1119659⟩
private theorem pr1120001 : Nat.Prime 1120001 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7]) (by decide +kernel)
def pv1120001 : PrimeValue := ⟨1120001, pr1120001⟩
private theorem pr1120349 : Nat.Prime 1120349 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv173,pv1619]) (by decide +kernel)
def pv1120349 : PrimeValue := ⟨1120349, pr1120349⟩
private theorem pr1120481 : Nat.Prime 1120481 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv47,pv149]) (by decide +kernel)
def pv1120481 : PrimeValue := ⟨1120481, pr1120481⟩
private theorem pr1120649 : Nat.Prime 1120649 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv127,pv1103]) (by decide +kernel)
def pv1120649 : PrimeValue := ⟨1120649, pr1120649⟩
private theorem pr1120739 : Nat.Prime 1120739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53,pv97,pv109]) (by decide +kernel)
def pv1120739 : PrimeValue := ⟨1120739, pr1120739⟩
private theorem pr1120799 : Nat.Prime 1120799 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv223,pv359]) (by decide +kernel)
def pv1120799 : PrimeValue := ⟨1120799, pr1120799⟩
private theorem pr1120961 : Nat.Prime 1120961 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv31,pv113]) (by decide +kernel)
def pv1120961 : PrimeValue := ⟨1120961, pr1120961⟩
private theorem pr1121093 : Nat.Prime 1121093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv40039]) (by decide +kernel)
def pv1121093 : PrimeValue := ⟨1121093, pr1121093⟩
private theorem pr1121189 : Nat.Prime 1121189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv280297]) (by decide +kernel)
def pv1121189 : PrimeValue := ⟨1121189, pr1121189⟩
private theorem pr1121369 : Nat.Prime 1121369 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv140171]) (by decide +kernel)
def pv1121369 : PrimeValue := ⟨1121369, pr1121369⟩
private theorem pr1121423 : Nat.Prime 1121423 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv32983]) (by decide +kernel)
def pv1121423 : PrimeValue := ⟨1121423, pr1121423⟩
private theorem pr1121699 : Nat.Prime 1121699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv13043]) (by decide +kernel)
def pv1121699 : PrimeValue := ⟨1121699, pr1121699⟩
private theorem pr1121831 : Nat.Prime 1121831 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv17,pv6599]) (by decide +kernel)
def pv1121831 : PrimeValue := ⟨1121831, pr1121831⟩
private theorem pr1121993 : Nat.Prime 1121993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv140249]) (by decide +kernel)
def pv1121993 : PrimeValue := ⟨1121993, pr1121993⟩
private theorem pr1122113 : Nat.Prime 1122113 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv89,pv197]) (by decide +kernel)
def pv1122113 : PrimeValue := ⟨1122113, pr1122113⟩
private theorem pr1122281 : Nat.Prime 1122281 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv28057]) (by decide +kernel)
def pv1122281 : PrimeValue := ⟨1122281, pr1122281⟩
private theorem pr1122389 : Nat.Prime 1122389 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv280597]) (by decide +kernel)
def pv1122389 : PrimeValue := ⟨1122389, pr1122389⟩
private theorem pr1122431 : Nat.Prime 1122431 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv107,pv1049]) (by decide +kernel)
def pv1122431 : PrimeValue := ⟨1122431, pr1122431⟩
private theorem pr1122449 : Nat.Prime 1122449 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv73]) (by decide +kernel)
def pv1122449 : PrimeValue := ⟨1122449, pr1122449⟩
private theorem pr1122623 : Nat.Prime 1122623 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv563,pv997]) (by decide +kernel)
def pv1122623 : PrimeValue := ⟨1122623, pr1122623⟩
private theorem pr1122659 : Nat.Prime 1122659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv83,pv6763]) (by decide +kernel)
def pv1122659 : PrimeValue := ⟨1122659, pr1122659⟩
private theorem pr1122899 : Nat.Prime 1122899 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv80207]) (by decide +kernel)
def pv1122899 : PrimeValue := ⟨1122899, pr1122899⟩
private theorem pr1123541 : Nat.Prime 1123541 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv5107]) (by decide +kernel)
def pv1123541 : PrimeValue := ⟨1123541, pr1123541⟩
private theorem pr1123901 : Nat.Prime 1123901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11239]) (by decide +kernel)
def pv1123901 : PrimeValue := ⟨1123901, pr1123901⟩
private theorem pr1123943 : Nat.Prime 1123943 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv727,pv773]) (by decide +kernel)
def pv1123943 : PrimeValue := ⟨1123943, pr1123943⟩
private theorem pr1123961 : Nat.Prime 1123961 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv28099]) (by decide +kernel)
def pv1123961 : PrimeValue := ⟨1123961, pr1123961⟩
private theorem pr1124219 : Nat.Prime 1124219 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv683,pv823]) (by decide +kernel)
def pv1124219 : PrimeValue := ⟨1124219, pr1124219⟩
private theorem pr1124351 : Nat.Prime 1124351 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv113,pv199]) (by decide +kernel)
def pv1124351 : PrimeValue := ⟨1124351, pr1124351⟩
private theorem pr1124369 : Nat.Prime 1124369 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv7,pv10039]) (by decide +kernel)
def pv1124369 : PrimeValue := ⟨1124369, pr1124369⟩
private theorem pr1124423 : Nat.Prime 1124423 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv59,pv733]) (by decide +kernel)
def pv1124423 : PrimeValue := ⟨1124423, pr1124423⟩
private theorem pr1124531 : Nat.Prime 1124531 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv10223]) (by decide +kernel)
def pv1124531 : PrimeValue := ⟨1124531, pr1124531⟩
private theorem pr1124603 : Nat.Prime 1124603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv562301]) (by decide +kernel)
def pv1124603 : PrimeValue := ⟨1124603, pr1124603⟩
private theorem pr1124681 : Nat.Prime 1124681 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv31,pv907]) (by decide +kernel)
def pv1124681 : PrimeValue := ⟨1124681, pr1124681⟩
private theorem pr1124699 : Nat.Prime 1124699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv562349]) (by decide +kernel)
def pv1124699 : PrimeValue := ⟨1124699, pr1124699⟩
private theorem pr1124741 : Nat.Prime 1124741 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv56237]) (by decide +kernel)
def pv1124741 : PrimeValue := ⟨1124741, pr1124741⟩
private theorem pr1124789 : Nat.Prime 1124789 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv17,pv139]) (by decide +kernel)
def pv1124789 : PrimeValue := ⟨1124789, pr1124789⟩
private theorem pr1124993 : Nat.Prime 1124993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv17,pv47]) (by decide +kernel)
def pv1124993 : PrimeValue := ⟨1124993, pr1124993⟩
private theorem pr1125209 : Nat.Prime 1125209 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv71,pv283]) (by decide +kernel)
def pv1125209 : PrimeValue := ⟨1125209, pr1125209⟩
private theorem pr1125581 : Nat.Prime 1125581 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv167,pv337]) (by decide +kernel)
def pv1125581 : PrimeValue := ⟨1125581, pr1125581⟩
private theorem pr1125599 : Nat.Prime 1125599 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv19,pv1559]) (by decide +kernel)
def pv1125599 : PrimeValue := ⟨1125599, pr1125599⟩
private theorem pr1125713 : Nat.Prime 1125713 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv19,pv23]) (by decide +kernel)
def pv1125713 : PrimeValue := ⟨1125713, pr1125713⟩
private theorem pr1126043 : Nat.Prime 1126043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv563021]) (by decide +kernel)
def pv1126043 : PrimeValue := ⟨1126043, pr1126043⟩
private theorem pr1126259 : Nat.Prime 1126259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv80447]) (by decide +kernel)
def pv1126259 : PrimeValue := ⟨1126259, pr1126259⟩
private theorem pr1126283 : Nat.Prime 1126283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv107,pv277]) (by decide +kernel)
def pv1126283 : PrimeValue := ⟨1126283, pr1126283⟩
private theorem pr1126319 : Nat.Prime 1126319 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv17,pv157,pv211]) (by decide +kernel)
def pv1126319 : PrimeValue := ⟨1126319, pr1126319⟩
private theorem pr1126523 : Nat.Prime 1126523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv1949]) (by decide +kernel)
def pv1126523 : PrimeValue := ⟨1126523, pr1126523⟩
private theorem pr1126661 : Nat.Prime 1126661 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv56333]) (by decide +kernel)
def pv1126661 : PrimeValue := ⟨1126661, pr1126661⟩
private theorem pr1127033 : Nat.Prime 1127033 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv8287]) (by decide +kernel)
def pv1127033 : PrimeValue := ⟨1127033, pr1127033⟩
private theorem pr1127039 : Nat.Prime 1127039 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv51229]) (by decide +kernel)
def pv1127039 : PrimeValue := ⟨1127039, pr1127039⟩
private theorem pr1127111 : Nat.Prime 1127111 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv269,pv419]) (by decide +kernel)
def pv1127111 : PrimeValue := ⟨1127111, pr1127111⟩
private theorem pr1127123 : Nat.Prime 1127123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv563561]) (by decide +kernel)
def pv1127123 : PrimeValue := ⟨1127123, pr1127123⟩
private theorem pr1127303 : Nat.Prime 1127303 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv51241]) (by decide +kernel)
def pv1127303 : PrimeValue := ⟨1127303, pr1127303⟩
private theorem pr1127453 : Nat.Prime 1127453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv89,pv3167]) (by decide +kernel)
def pv1127453 : PrimeValue := ⟨1127453, pr1127453⟩
private theorem pr1127531 : Nat.Prime 1127531 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv47,pv2399]) (by decide +kernel)
def pv1127531 : PrimeValue := ⟨1127531, pr1127531⟩
private theorem pr1127573 : Nat.Prime 1127573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv281893]) (by decide +kernel)
def pv1127573 : PrimeValue := ⟨1127573, pr1127573⟩
private theorem pr1127891 : Nat.Prime 1127891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv43,pv61]) (by decide +kernel)
def pv1127891 : PrimeValue := ⟨1127891, pr1127891⟩
private theorem pr1127993 : Nat.Prime 1127993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv41,pv181]) (by decide +kernel)
def pv1127993 : PrimeValue := ⟨1127993, pr1127993⟩
private theorem pr1128089 : Nat.Prime 1128089 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv10847]) (by decide +kernel)
def pv1128089 : PrimeValue := ⟨1128089, pr1128089⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
