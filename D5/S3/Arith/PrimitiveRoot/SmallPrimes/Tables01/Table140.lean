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
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr1090013 : PrimeCertificate 1090013 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11,pv3539]) (by decide +kernel)
def pv1090013 : PrimeValue := ⟨1090013, pr1090013⟩
private theorem pr1090151 : PrimeCertificate 1090151 :=
  certifyPrime (q := pv29) (ls := [pv2,pv5,pv21803]) (by decide +kernel)
def pv1090151 : PrimeValue := ⟨1090151, pr1090151⟩
private theorem pr1090373 : PrimeCertificate 1090373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv14347]) (by decide +kernel)
def pv1090373 : PrimeValue := ⟨1090373, pr1090373⟩
private theorem pr1090403 : PrimeCertificate 1090403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv457,pv1193]) (by decide +kernel)
def pv1090403 : PrimeValue := ⟨1090403, pr1090403⟩
private theorem pr1090613 : PrimeCertificate 1090613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv7369]) (by decide +kernel)
def pv1090613 : PrimeValue := ⟨1090613, pr1090613⟩
private theorem pr1090709 : PrimeCertificate 1090709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv257,pv1061]) (by decide +kernel)
def pv1090709 : PrimeValue := ⟨1090709, pr1090709⟩
private theorem pr1090769 : PrimeCertificate 1090769 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv9739]) (by decide +kernel)
def pv1090769 : PrimeValue := ⟨1090769, pr1090769⟩
private theorem pr1091003 : PrimeCertificate 1091003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv101,pv491]) (by decide +kernel)
def pv1091003 : PrimeValue := ⟨1091003, pr1091003⟩
private theorem pr1092023 : PrimeCertificate 1092023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv61,pv8951]) (by decide +kernel)
def pv1092023 : PrimeValue := ⟨1092023, pr1092023⟩
private theorem pr1092089 : PrimeCertificate 1092089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv136511]) (by decide +kernel)
def pv1092089 : PrimeValue := ⟨1092089, pr1092089⟩
private theorem pr1092251 : PrimeCertificate 1092251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv257]) (by decide +kernel)
def pv1092251 : PrimeValue := ⟨1092251, pr1092251⟩
private theorem pr1092389 : PrimeCertificate 1092389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv37,pv61]) (by decide +kernel)
def pv1092389 : PrimeValue := ⟨1092389, pr1092389⟩
private theorem pr1092593 : PrimeCertificate 1092593 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv2969]) (by decide +kernel)
def pv1092593 : PrimeValue := ⟨1092593, pr1092593⟩
private theorem pr1092713 : PrimeCertificate 1092713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv137,pv997]) (by decide +kernel)
def pv1092713 : PrimeValue := ⟨1092713, pr1092713⟩
private theorem pr1092863 : PrimeCertificate 1092863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv32143]) (by decide +kernel)
def pv1092863 : PrimeValue := ⟨1092863, pr1092863⟩
private theorem pr1093283 : PrimeCertificate 1093283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv23767]) (by decide +kernel)
def pv1093283 : PrimeValue := ⟨1093283, pr1093283⟩
private theorem pr1093289 : PrimeCertificate 1093289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv2789]) (by decide +kernel)
def pv1093289 : PrimeValue := ⟨1093289, pr1093289⟩
private theorem pr1093679 : PrimeCertificate 1093679 :=
  certifyPrime (q := pv11) (ls := [pv2,pv17,pv19,pv1693]) (by decide +kernel)
def pv1093679 : PrimeValue := ⟨1093679, pr1093679⟩
private theorem pr1093871 : PrimeCertificate 1093871 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv109387]) (by decide +kernel)
def pv1093871 : PrimeValue := ⟨1093871, pr1093871⟩
private theorem pr1094081 : PrimeCertificate 1094081 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv13,pv263]) (by decide +kernel)
def pv1094081 : PrimeValue := ⟨1094081, pr1094081⟩
private theorem pr1094339 : PrimeCertificate 1094339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv78167]) (by decide +kernel)
def pv1094339 : PrimeValue := ⟨1094339, pr1094339⟩
private theorem pr1094531 : PrimeCertificate 1094531 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv109453]) (by decide +kernel)
def pv1094531 : PrimeValue := ⟨1094531, pr1094531⟩
private theorem pr1094573 : PrimeCertificate 1094573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv273643]) (by decide +kernel)
def pv1094573 : PrimeValue := ⟨1094573, pr1094573⟩
private theorem pr1094603 : PrimeCertificate 1094603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv547301]) (by decide +kernel)
def pv1094603 : PrimeValue := ⟨1094603, pr1094603⟩
private theorem pr1094633 : PrimeCertificate 1094633 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11,pv1777]) (by decide +kernel)
def pv1094633 : PrimeValue := ⟨1094633, pr1094633⟩
private theorem pr1094669 : PrimeCertificate 1094669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv211,pv1297]) (by decide +kernel)
def pv1094669 : PrimeValue := ⟨1094669, pr1094669⟩
private theorem pr1094921 : PrimeCertificate 1094921 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv31,pv883]) (by decide +kernel)
def pv1094921 : PrimeValue := ⟨1094921, pr1094921⟩
private theorem pr1094939 : PrimeCertificate 1094939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv23,pv1831]) (by decide +kernel)
def pv1094939 : PrimeValue := ⟨1094939, pr1094939⟩
private theorem pr1094969 : PrimeCertificate 1094969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv19553]) (by decide +kernel)
def pv1094969 : PrimeValue := ⟨1094969, pr1094969⟩
private theorem pr1095023 : PrimeCertificate 1095023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv601,pv911]) (by decide +kernel)
def pv1095023 : PrimeValue := ⟨1095023, pr1095023⟩
private theorem pr1095071 : PrimeCertificate 1095071 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv109507]) (by decide +kernel)
def pv1095071 : PrimeValue := ⟨1095071, pr1095071⟩
private theorem pr1095173 : PrimeCertificate 1095173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv21061]) (by decide +kernel)
def pv1095173 : PrimeValue := ⟨1095173, pr1095173⟩
private theorem pr1095239 : PrimeCertificate 1095239 :=
  certifyPrime (q := pv13) (ls := [pv2,pv547619]) (by decide +kernel)
def pv1095239 : PrimeValue := ⟨1095239, pr1095239⟩
private theorem pr1095443 : PrimeCertificate 1095443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv421,pv1301]) (by decide +kernel)
def pv1095443 : PrimeValue := ⟨1095443, pr1095443⟩
private theorem pr1095491 : PrimeCertificate 1095491 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv23,pv433]) (by decide +kernel)
def pv1095491 : PrimeValue := ⟨1095491, pr1095491⟩
private theorem pr1095791 : PrimeCertificate 1095791 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv109579]) (by decide +kernel)
def pv1095791 : PrimeValue := ⟨1095791, pr1095791⟩
private theorem pr1095851 : PrimeCertificate 1095851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv31,pv101]) (by decide +kernel)
def pv1095851 : PrimeValue := ⟨1095851, pr1095851⟩
private theorem pr1096031 : PrimeCertificate 1096031 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv13,pv8431]) (by decide +kernel)
def pv1096031 : PrimeValue := ⟨1096031, pr1096031⟩
private theorem pr1096061 : PrimeCertificate 1096061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv7829]) (by decide +kernel)
def pv1096061 : PrimeValue := ⟨1096061, pr1096061⟩
private theorem pr1096163 : PrimeCertificate 1096163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv14813]) (by decide +kernel)
def pv1096163 : PrimeValue := ⟨1096163, pr1096163⟩
private theorem pr1096289 : PrimeCertificate 1096289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv34259]) (by decide +kernel)
def pv1096289 : PrimeValue := ⟨1096289, pr1096289⟩
private theorem pr1096373 : PrimeCertificate 1096373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv274093]) (by decide +kernel)
def pv1096373 : PrimeValue := ⟨1096373, pr1096373⟩
private theorem pr1096481 : PrimeCertificate 1096481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv11,pv89]) (by decide +kernel)
def pv1096481 : PrimeValue := ⟨1096481, pr1096481⟩
private theorem pr1096583 : PrimeCertificate 1096583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv548291]) (by decide +kernel)
def pv1096583 : PrimeValue := ⟨1096583, pr1096583⟩
private theorem pr1096631 : PrimeCertificate 1096631 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv109663]) (by decide +kernel)
def pv1096631 : PrimeValue := ⟨1096631, pr1096631⟩
private theorem pr1096691 : PrimeCertificate 1096691 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv7,pv15667]) (by decide +kernel)
def pv1096691 : PrimeValue := ⟨1096691, pr1096691⟩
private theorem pr1096853 : PrimeCertificate 1096853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv274213]) (by decide +kernel)
def pv1096853 : PrimeValue := ⟨1096853, pr1096853⟩
private theorem pr1097009 : PrimeCertificate 1097009 :=
  certifyPrime (q := pv29) (ls := [pv2,pv11,pv23,pv271]) (by decide +kernel)
def pv1097009 : PrimeValue := ⟨1097009, pr1097009⟩
private theorem pr1097423 : PrimeCertificate 1097423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv23857]) (by decide +kernel)
def pv1097423 : PrimeValue := ⟨1097423, pr1097423⟩
private theorem pr1097441 : PrimeCertificate 1097441 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv19]) (by decide +kernel)
def pv1097441 : PrimeValue := ⟨1097441, pr1097441⟩
private theorem pr1097483 : PrimeCertificate 1097483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv7517]) (by decide +kernel)
def pv1097483 : PrimeValue := ⟨1097483, pr1097483⟩
private theorem pr1097501 : PrimeCertificate 1097501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv439]) (by decide +kernel)
def pv1097501 : PrimeValue := ⟨1097501, pr1097501⟩
private theorem pr1097669 : PrimeCertificate 1097669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13,pv19,pv101]) (by decide +kernel)
def pv1097669 : PrimeValue := ⟨1097669, pr1097669⟩
private theorem pr1097699 : PrimeCertificate 1097699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv23,pv487]) (by decide +kernel)
def pv1097699 : PrimeValue := ⟨1097699, pr1097699⟩
private theorem pr1097861 : PrimeCertificate 1097861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv3229]) (by decide +kernel)
def pv1097861 : PrimeValue := ⟨1097861, pr1097861⟩
private theorem pr1097879 : PrimeCertificate 1097879 :=
  certifyPrime (q := pv29) (ls := [pv2,pv61,pv8999]) (by decide +kernel)
def pv1097879 : PrimeValue := ⟨1097879, pr1097879⟩
private theorem pr1097909 : PrimeCertificate 1097909 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv113,pv347]) (by decide +kernel)
def pv1097909 : PrimeValue := ⟨1097909, pr1097909⟩
private theorem pr1097933 : PrimeCertificate 1097933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv24953]) (by decide +kernel)
def pv1097933 : PrimeValue := ⟨1097933, pr1097933⟩
private theorem pr1098203 : PrimeCertificate 1098203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv47,pv1669]) (by decide +kernel)
def pv1098203 : PrimeValue := ⟨1098203, pr1098203⟩
private theorem pr1098269 : PrimeCertificate 1098269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv31,pv521]) (by decide +kernel)
def pv1098269 : PrimeValue := ⟨1098269, pr1098269⟩
private theorem pr1098479 : PrimeCertificate 1098479 :=
  certifyPrime (q := pv7) (ls := [pv2,pv43,pv53,pv241]) (by decide +kernel)
def pv1098479 : PrimeValue := ⟨1098479, pr1098479⟩
private theorem pr1098731 : PrimeCertificate 1098731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv109873]) (by decide +kernel)
def pv1098731 : PrimeValue := ⟨1098731, pr1098731⟩
private theorem pr1098953 : PrimeCertificate 1098953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv137369]) (by decide +kernel)
def pv1098953 : PrimeValue := ⟨1098953, pr1098953⟩
private theorem pr1099079 : PrimeCertificate 1099079 :=
  certifyPrime (q := pv7) (ls := [pv2,pv23,pv23893]) (by decide +kernel)
def pv1099079 : PrimeValue := ⟨1099079, pr1099079⟩
private theorem pr1099223 : PrimeCertificate 1099223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv71,pv7741]) (by decide +kernel)
def pv1099223 : PrimeValue := ⟨1099223, pr1099223⟩
private theorem pr1099391 : PrimeCertificate 1099391 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv17,pv29,pv223]) (by decide +kernel)
def pv1099391 : PrimeValue := ⟨1099391, pr1099391⟩
private theorem pr1099421 : PrimeCertificate 1099421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv7853]) (by decide +kernel)
def pv1099421 : PrimeValue := ⟨1099421, pr1099421⟩
private theorem pr1099589 : PrimeCertificate 1099589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv173,pv227]) (by decide +kernel)
def pv1099589 : PrimeValue := ⟨1099589, pr1099589⟩
private theorem pr1099649 : PrimeCertificate 1099649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv71]) (by decide +kernel)
def pv1099649 : PrimeValue := ⟨1099649, pr1099649⟩
private theorem pr1099841 : PrimeCertificate 1099841 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv491]) (by decide +kernel)
def pv1099841 : PrimeValue := ⟨1099841, pr1099841⟩
private theorem pr1099859 : PrimeCertificate 1099859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv379,pv1451]) (by decide +kernel)
def pv1099859 : PrimeValue := ⟨1099859, pr1099859⟩
private theorem pr1100051 : PrimeCertificate 1100051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv449]) (by decide +kernel)
def pv1100051 : PrimeValue := ⟨1100051, pr1100051⟩
private theorem pr1100321 : PrimeCertificate 1100321 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv23]) (by decide +kernel)
def pv1100321 : PrimeValue := ⟨1100321, pr1100321⟩
private theorem pr1100381 : PrimeCertificate 1100381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv37,pv1487]) (by decide +kernel)
def pv1100381 : PrimeValue := ⟨1100381, pr1100381⟩
private theorem pr1100471 : PrimeCertificate 1100471 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv79,pv199]) (by decide +kernel)
def pv1100471 : PrimeValue := ⟨1100471, pr1100471⟩
private theorem pr1100483 : PrimeCertificate 1100483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv550241]) (by decide +kernel)
def pv1100483 : PrimeValue := ⟨1100483, pr1100483⟩
private theorem pr1100591 : PrimeCertificate 1100591 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv110059]) (by decide +kernel)
def pv1100591 : PrimeValue := ⟨1100591, pr1100591⟩
private theorem pr1101143 : PrimeCertificate 1101143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv78653]) (by decide +kernel)
def pv1101143 : PrimeValue := ⟨1101143, pr1101143⟩
private theorem pr1101179 : PrimeCertificate 1101179 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv41,pv1033]) (by decide +kernel)
def pv1101179 : PrimeValue := ⟨1101179, pr1101179⟩
private theorem pr1101473 : PrimeCertificate 1101473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv34421]) (by decide +kernel)
def pv1101473 : PrimeValue := ⟨1101473, pr1101473⟩
private theorem pr1101839 : PrimeCertificate 1101839 :=
  certifyPrime (q := pv7) (ls := [pv2,pv17,pv23,pv1409]) (by decide +kernel)
def pv1101839 : PrimeValue := ⟨1101839, pr1101839⟩
private theorem pr1102001 : PrimeCertificate 1102001 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv19,pv29]) (by decide +kernel)
def pv1102001 : PrimeValue := ⟨1102001, pr1102001⟩
private theorem pr1102163 : PrimeCertificate 1102163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv13441]) (by decide +kernel)
def pv1102163 : PrimeValue := ⟨1102163, pr1102163⟩
private theorem pr1102253 : PrimeCertificate 1102253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv11981]) (by decide +kernel)
def pv1102253 : PrimeValue := ⟨1102253, pr1102253⟩
private theorem pr1102301 : PrimeCertificate 1102301 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv73,pv151]) (by decide +kernel)
def pv1102301 : PrimeValue := ⟨1102301, pr1102301⟩
private theorem pr1102553 : PrimeCertificate 1102553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv17,pv67]) (by decide +kernel)
def pv1102553 : PrimeValue := ⟨1102553, pr1102553⟩
private theorem pr1102583 : PrimeCertificate 1102583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv42407]) (by decide +kernel)
def pv1102583 : PrimeValue := ⟨1102583, pr1102583⟩
private theorem pr1102901 : PrimeCertificate 1102901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41,pv269]) (by decide +kernel)
def pv1102901 : PrimeValue := ⟨1102901, pr1102901⟩
private theorem pr1103279 : PrimeCertificate 1103279 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv47,pv97]) (by decide +kernel)
def pv1103279 : PrimeValue := ⟨1103279, pr1103279⟩
private theorem pr1103309 : PrimeCertificate 1103309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv275827]) (by decide +kernel)
def pv1103309 : PrimeValue := ⟨1103309, pr1103309⟩
private theorem pr1103519 : PrimeCertificate 1103519 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv42443]) (by decide +kernel)
def pv1103519 : PrimeValue := ⟨1103519, pr1103519⟩
private theorem pr1103549 : PrimeCertificate 1103549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv263,pv1049]) (by decide +kernel)
def pv1103549 : PrimeValue := ⟨1103549, pr1103549⟩
private theorem pr1103561 : PrimeCertificate 1103561 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv47,pv587]) (by decide +kernel)
def pv1103561 : PrimeValue := ⟨1103561, pr1103561⟩
private theorem pr1103579 : PrimeCertificate 1103579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11261]) (by decide +kernel)
def pv1103579 : PrimeValue := ⟨1103579, pr1103579⟩
private theorem pr1103621 : PrimeCertificate 1103621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv7883]) (by decide +kernel)
def pv1103621 : PrimeValue := ⟨1103621, pr1103621⟩
private theorem pr1103639 : PrimeCertificate 1103639 :=
  certifyPrime (q := pv19) (ls := [pv2,pv41,pv43,pv313]) (by decide +kernel)
def pv1103639 : PrimeValue := ⟨1103639, pr1103639⟩
private theorem pr1103981 : PrimeCertificate 1103981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv191]) (by decide +kernel)
def pv1103981 : PrimeValue := ⟨1103981, pr1103981⟩
private theorem pr1104041 : PrimeCertificate 1104041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv3943]) (by decide +kernel)
def pv1104041 : PrimeValue := ⟨1104041, pr1104041⟩
private theorem pr1104101 : PrimeCertificate 1104101 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv61,pv181]) (by decide +kernel)
def pv1104101 : PrimeValue := ⟨1104101, pr1104101⟩
private theorem pr1104203 : PrimeCertificate 1104203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv53,pv947]) (by decide +kernel)
def pv1104203 : PrimeValue := ⟨1104203, pr1104203⟩
private theorem pr1104353 : PrimeCertificate 1104353 :=
  certifyPrime (q := pv3) (ls := [pv2,pv34511]) (by decide +kernel)
def pv1104353 : PrimeValue := ⟨1104353, pr1104353⟩
private theorem pr1104671 : PrimeCertificate 1104671 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv43,pv367]) (by decide +kernel)
def pv1104671 : PrimeValue := ⟨1104671, pr1104671⟩
private theorem pr1104749 : PrimeCertificate 1104749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv276187]) (by decide +kernel)
def pv1104749 : PrimeValue := ⟨1104749, pr1104749⟩
private theorem pr1104833 : PrimeCertificate 1104833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv61,pv283]) (by decide +kernel)
def pv1104833 : PrimeValue := ⟨1104833, pr1104833⟩
private theorem pr1105193 : PrimeCertificate 1105193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv19,pv661]) (by decide +kernel)
def pv1105193 : PrimeValue := ⟨1105193, pr1105193⟩
private theorem pr1105589 : PrimeCertificate 1105589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv25127]) (by decide +kernel)
def pv1105589 : PrimeValue := ⟨1105589, pr1105589⟩
private theorem pr1105613 : PrimeCertificate 1105613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv71,pv229]) (by decide +kernel)
def pv1105613 : PrimeValue := ⟨1105613, pr1105613⟩
private theorem pr1105823 : PrimeCertificate 1105823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv719,pv769]) (by decide +kernel)
def pv1105823 : PrimeValue := ⟨1105823, pr1105823⟩
private theorem pr1106243 : PrimeCertificate 1106243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv7577]) (by decide +kernel)
def pv1106243 : PrimeValue := ⟨1106243, pr1106243⟩
private theorem pr1106489 : PrimeCertificate 1106489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv138311]) (by decide +kernel)
def pv1106489 : PrimeValue := ⟨1106489, pr1106489⟩
private theorem pr1106621 : PrimeCertificate 1106621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv55331]) (by decide +kernel)
def pv1106621 : PrimeValue := ⟨1106621, pr1106621⟩
private theorem pr1107479 : PrimeCertificate 1107479 :=
  certifyPrime (q := pv7) (ls := [pv2,pv157,pv3527]) (by decide +kernel)
def pv1107479 : PrimeValue := ⟨1107479, pr1107479⟩
private theorem pr1107581 : PrimeCertificate 1107581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv79,pv701]) (by decide +kernel)
def pv1107581 : PrimeValue := ⟨1107581, pr1107581⟩
private theorem pr1107773 : PrimeCertificate 1107773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv12041]) (by decide +kernel)
def pv1107773 : PrimeValue := ⟨1107773, pr1107773⟩
private theorem pr1107791 : PrimeCertificate 1107791 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv47,pv2357]) (by decide +kernel)
def pv1107791 : PrimeValue := ⟨1107791, pr1107791⟩
private theorem pr1107923 : PrimeCertificate 1107923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv553961]) (by decide +kernel)
def pv1107923 : PrimeValue := ⟨1107923, pr1107923⟩
private theorem pr1107989 : PrimeCertificate 1107989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv5653]) (by decide +kernel)
def pv1107989 : PrimeValue := ⟨1107989, pr1107989⟩
private theorem pr1108181 : PrimeCertificate 1108181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv67,pv827]) (by decide +kernel)
def pv1108181 : PrimeValue := ⟨1108181, pr1108181⟩
private theorem pr1108259 : PrimeCertificate 1108259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv554129]) (by decide +kernel)
def pv1108259 : PrimeValue := ⟨1108259, pr1108259⟩
private theorem pr1108571 : PrimeCertificate 1108571 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv17,pv6521]) (by decide +kernel)
def pv1108571 : PrimeValue := ⟨1108571, pr1108571⟩
private theorem pr1109033 : PrimeCertificate 1109033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv138629]) (by decide +kernel)
def pv1109033 : PrimeValue := ⟨1109033, pr1109033⟩
private theorem pr1109159 : PrimeCertificate 1109159 :=
  certifyPrime (q := pv7) (ls := [pv2,pv661,pv839]) (by decide +kernel)
def pv1109159 : PrimeValue := ⟨1109159, pr1109159⟩
private theorem pr1109219 : PrimeCertificate 1109219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv127,pv397]) (by decide +kernel)
def pv1109219 : PrimeValue := ⟨1109219, pr1109219⟩
private theorem pr1109291 : PrimeCertificate 1109291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv13,pv23,pv53]) (by decide +kernel)
def pv1109291 : PrimeValue := ⟨1109291, pr1109291⟩
private theorem pr1109561 : PrimeCertificate 1109561 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv27739]) (by decide +kernel)
def pv1109561 : PrimeValue := ⟨1109561, pr1109561⟩
private theorem pr1109639 : PrimeCertificate 1109639 :=
  certifyPrime (q := pv11) (ls := [pv2,pv19,pv29201]) (by decide +kernel)
def pv1109639 : PrimeValue := ⟨1109639, pr1109639⟩
private theorem pr1109903 : PrimeCertificate 1109903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv554951]) (by decide +kernel)
def pv1109903 : PrimeValue := ⟨1109903, pr1109903⟩
private theorem pr1110041 : PrimeCertificate 1110041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv27751]) (by decide +kernel)
def pv1110041 : PrimeValue := ⟨1110041, pr1110041⟩
private theorem pr1110269 : PrimeCertificate 1110269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv277567]) (by decide +kernel)
def pv1110269 : PrimeValue := ⟨1110269, pr1110269⟩
private theorem pr1110929 : PrimeCertificate 1110929 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv13,pv109]) (by decide +kernel)
def pv1110929 : PrimeValue := ⟨1110929, pr1110929⟩
private theorem pr1110953 : PrimeCertificate 1110953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv138869]) (by decide +kernel)
def pv1110953 : PrimeValue := ⟨1110953, pr1110953⟩
private theorem pr1110971 : PrimeCertificate 1110971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv59,pv269]) (by decide +kernel)
def pv1110971 : PrimeValue := ⟨1110971, pr1110971⟩
private theorem pr1111283 : PrimeCertificate 1111283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv593,pv937]) (by decide +kernel)
def pv1111283 : PrimeValue := ⟨1111283, pr1111283⟩
private theorem pr1111289 : PrimeCertificate 1111289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv4481]) (by decide +kernel)
def pv1111289 : PrimeValue := ⟨1111289, pr1111289⟩
private theorem pr1111361 : PrimeCertificate 1111361 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv23,pv151]) (by decide +kernel)
def pv1111361 : PrimeValue := ⟨1111361, pr1111361⟩
private theorem pr1111559 : PrimeCertificate 1111559 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv79397]) (by decide +kernel)
def pv1111559 : PrimeValue := ⟨1111559, pr1111559⟩
private theorem pr1111703 : PrimeCertificate 1111703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv37,pv83,pv181]) (by decide +kernel)
def pv1111703 : PrimeValue := ⟨1111703, pr1111703⟩
private theorem pr1111793 : PrimeCertificate 1111793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv6317]) (by decide +kernel)
def pv1111793 : PrimeValue := ⟨1111793, pr1111793⟩
private theorem pr1111991 : PrimeCertificate 1111991 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv919]) (by decide +kernel)
def pv1111991 : PrimeValue := ⟨1111991, pr1111991⟩
private theorem pr1112129 : PrimeCertificate 1112129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17377]) (by decide +kernel)
def pv1112129 : PrimeValue := ⟨1112129, pr1112129⟩
private theorem pr1112141 : PrimeCertificate 1112141 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17,pv3271]) (by decide +kernel)
def pv1112141 : PrimeValue := ⟨1112141, pr1112141⟩
private theorem pr1112333 : PrimeCertificate 1112333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv21391]) (by decide +kernel)
def pv1112333 : PrimeValue := ⟨1112333, pr1112333⟩
private theorem pr1112339 : PrimeCertificate 1112339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv457,pv1217]) (by decide +kernel)
def pv1112339 : PrimeValue := ⟨1112339, pr1112339⟩
private theorem pr1112381 : PrimeCertificate 1112381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv55619]) (by decide +kernel)
def pv1112381 : PrimeValue := ⟨1112381, pr1112381⟩
private theorem pr1112519 : PrimeCertificate 1112519 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv61,pv829]) (by decide +kernel)
def pv1112519 : PrimeValue := ⟨1112519, pr1112519⟩
private theorem pr1112561 : PrimeCertificate 1112561 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv13907]) (by decide +kernel)
def pv1112561 : PrimeValue := ⟨1112561, pr1112561⟩
private theorem pr1112591 : PrimeCertificate 1112591 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv31,pv37,pv97]) (by decide +kernel)
def pv1112591 : PrimeValue := ⟨1112591, pr1112591⟩
private theorem pr1112789 : PrimeCertificate 1112789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv53,pv181]) (by decide +kernel)
def pv1112789 : PrimeValue := ⟨1112789, pr1112789⟩
private theorem pr1113011 : PrimeCertificate 1113011 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv111301]) (by decide +kernel)
def pv1113011 : PrimeValue := ⟨1113011, pr1113011⟩
private theorem pr1113239 : PrimeCertificate 1113239 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv131,pv607]) (by decide +kernel)
def pv1113239 : PrimeValue := ⟨1113239, pr1113239⟩
private theorem pr1113461 : PrimeCertificate 1113461 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv55673]) (by decide +kernel)
def pv1113461 : PrimeValue := ⟨1113461, pr1113461⟩
private theorem pr1113509 : PrimeCertificate 1113509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv25307]) (by decide +kernel)
def pv1113509 : PrimeValue := ⟨1113509, pr1113509⟩
private theorem pr1113719 : PrimeCertificate 1113719 :=
  certifyPrime (q := pv23) (ls := [pv2,pv556859]) (by decide +kernel)
def pv1113719 : PrimeValue := ⟨1113719, pr1113719⟩
private theorem pr1113863 : PrimeCertificate 1113863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv556931]) (by decide +kernel)
def pv1113863 : PrimeValue := ⟨1113863, pr1113863⟩
private theorem pr1113971 : PrimeCertificate 1113971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv13,pv19,pv41]) (by decide +kernel)
def pv1113971 : PrimeValue := ⟨1113971, pr1113971⟩
private theorem pr1114241 : PrimeCertificate 1114241 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1741]) (by decide +kernel)
def pv1114241 : PrimeValue := ⟨1114241, pr1114241⟩
private theorem pr1114271 : PrimeCertificate 1114271 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv111427]) (by decide +kernel)
def pv1114271 : PrimeValue := ⟨1114271, pr1114271⟩
private theorem pr1114493 : PrimeCertificate 1114493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv278623]) (by decide +kernel)
def pv1114493 : PrimeValue := ⟨1114493, pr1114493⟩
private theorem pr1114541 : PrimeCertificate 1114541 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv19,pv419]) (by decide +kernel)
def pv1114541 : PrimeValue := ⟨1114541, pr1114541⟩
private theorem pr1114709 : PrimeCertificate 1114709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv41,pv971]) (by decide +kernel)
def pv1114709 : PrimeValue := ⟨1114709, pr1114709⟩
private theorem pr1114733 : PrimeCertificate 1114733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv6481]) (by decide +kernel)
def pv1114733 : PrimeValue := ⟨1114733, pr1114733⟩
private theorem pr1114829 : PrimeCertificate 1114829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13,pv1949]) (by decide +kernel)
def pv1114829 : PrimeValue := ⟨1114829, pr1114829⟩
private theorem pr1114931 : PrimeCertificate 1114931 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv111493]) (by decide +kernel)
def pv1114931 : PrimeValue := ⟨1114931, pr1114931⟩
private theorem pr1115321 : PrimeCertificate 1115321 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv27883]) (by decide +kernel)
def pv1115321 : PrimeValue := ⟨1115321, pr1115321⟩
private theorem pr1115363 : PrimeCertificate 1115363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv24247]) (by decide +kernel)
def pv1115363 : PrimeValue := ⟨1115363, pr1115363⟩
private theorem pr1115711 : PrimeCertificate 1115711 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv17,pv6563]) (by decide +kernel)
def pv1115711 : PrimeValue := ⟨1115711, pr1115711⟩
private theorem pr1115759 : PrimeCertificate 1115759 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv79697]) (by decide +kernel)
def pv1115759 : PrimeValue := ⟨1115759, pr1115759⟩
private theorem pr1115843 : PrimeCertificate 1115843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv6131]) (by decide +kernel)
def pv1115843 : PrimeValue := ⟨1115843, pr1115843⟩
private theorem pr1116053 : PrimeCertificate 1116053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv23,pv1733]) (by decide +kernel)
def pv1116053 : PrimeValue := ⟨1116053, pr1116053⟩
private theorem pr1116701 : PrimeCertificate 1116701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv859]) (by decide +kernel)
def pv1116701 : PrimeValue := ⟨1116701, pr1116701⟩
private theorem pr1116749 : PrimeCertificate 1116749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv279187]) (by decide +kernel)
def pv1116749 : PrimeValue := ⟨1116749, pr1116749⟩
private theorem pr1116893 : PrimeCertificate 1116893 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv113,pv353]) (by decide +kernel)
def pv1116893 : PrimeValue := ⟨1116893, pr1116893⟩
private theorem pr1117079 : PrimeCertificate 1117079 :=
  certifyPrime (q := pv13) (ls := [pv2,pv558539]) (by decide +kernel)
def pv1117079 : PrimeValue := ⟨1117079, pr1117079⟩
private theorem pr1117169 : PrimeCertificate 1117169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv41,pv131]) (by decide +kernel)
def pv1117169 : PrimeValue := ⟨1117169, pr1117169⟩
private theorem pr1117349 : PrimeCertificate 1117349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv279337]) (by decide +kernel)
def pv1117349 : PrimeValue := ⟨1117349, pr1117349⟩
private theorem pr1117463 : PrimeCertificate 1117463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv558731]) (by decide +kernel)
def pv1117463 : PrimeValue := ⟨1117463, pr1117463⟩
private theorem pr1117661 : PrimeCertificate 1117661 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv29,pv41,pv47]) (by decide +kernel)
def pv1117661 : PrimeValue := ⟨1117661, pr1117661⟩
private theorem pr1117769 : PrimeCertificate 1117769 :=
  certifyPrime (q := pv3) (ls := [pv2,pv139721]) (by decide +kernel)
def pv1117769 : PrimeValue := ⟨1117769, pr1117769⟩
private theorem pr1117793 : PrimeCertificate 1117793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv2687]) (by decide +kernel)
def pv1117793 : PrimeValue := ⟨1117793, pr1117793⟩
private theorem pr1117799 : PrimeCertificate 1117799 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv31,pv149]) (by decide +kernel)
def pv1117799 : PrimeValue := ⟨1117799, pr1117799⟩
private theorem pr1117901 : PrimeCertificate 1117901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv1597]) (by decide +kernel)
def pv1117901 : PrimeValue := ⟨1117901, pr1117901⟩
private theorem pr1117943 : PrimeCertificate 1117943 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv47,pv1699]) (by decide +kernel)
def pv1117943 : PrimeValue := ⟨1117943, pr1117943⟩
private theorem pr1118003 : PrimeCertificate 1118003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv559001]) (by decide +kernel)
def pv1118003 : PrimeValue := ⟨1118003, pr1118003⟩
private theorem pr1118291 : PrimeCertificate 1118291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv111829]) (by decide +kernel)
def pv1118291 : PrimeValue := ⟨1118291, pr1118291⟩
private theorem pr1118723 : PrimeCertificate 1118723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv211,pv241]) (by decide +kernel)
def pv1118723 : PrimeValue := ⟨1118723, pr1118723⟩
private theorem pr1118783 : PrimeCertificate 1118783 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv157,pv509]) (by decide +kernel)
def pv1118783 : PrimeValue := ⟨1118783, pr1118783⟩
private theorem pr1119179 : PrimeCertificate 1119179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv32917]) (by decide +kernel)
def pv1119179 : PrimeValue := ⟨1119179, pr1119179⟩
private theorem pr1119323 : PrimeCertificate 1119323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv307,pv1823]) (by decide +kernel)
def pv1119323 : PrimeValue := ⟨1119323, pr1119323⟩
private theorem pr1119389 : PrimeCertificate 1119389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv279847]) (by decide +kernel)
def pv1119389 : PrimeValue := ⟨1119389, pr1119389⟩
private theorem pr1119473 : PrimeCertificate 1119473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv37,pv61]) (by decide +kernel)
def pv1119473 : PrimeValue := ⟨1119473, pr1119473⟩
private theorem pr1119623 : PrimeCertificate 1119623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv79973]) (by decide +kernel)
def pv1119623 : PrimeValue := ⟨1119623, pr1119623⟩
private theorem pr1119659 : PrimeCertificate 1119659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv18059]) (by decide +kernel)
def pv1119659 : PrimeValue := ⟨1119659, pr1119659⟩
private theorem pr1120001 : PrimeCertificate 1120001 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7]) (by decide +kernel)
def pv1120001 : PrimeValue := ⟨1120001, pr1120001⟩
private theorem pr1120349 : PrimeCertificate 1120349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv173,pv1619]) (by decide +kernel)
def pv1120349 : PrimeValue := ⟨1120349, pr1120349⟩
private theorem pr1120481 : PrimeCertificate 1120481 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv47,pv149]) (by decide +kernel)
def pv1120481 : PrimeValue := ⟨1120481, pr1120481⟩
private theorem pr1120649 : PrimeCertificate 1120649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv127,pv1103]) (by decide +kernel)
def pv1120649 : PrimeValue := ⟨1120649, pr1120649⟩
private theorem pr1120739 : PrimeCertificate 1120739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv97,pv109]) (by decide +kernel)
def pv1120739 : PrimeValue := ⟨1120739, pr1120739⟩
private theorem pr1120799 : PrimeCertificate 1120799 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv223,pv359]) (by decide +kernel)
def pv1120799 : PrimeValue := ⟨1120799, pr1120799⟩
private theorem pr1120961 : PrimeCertificate 1120961 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv31,pv113]) (by decide +kernel)
def pv1120961 : PrimeValue := ⟨1120961, pr1120961⟩
private theorem pr1121093 : PrimeCertificate 1121093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv40039]) (by decide +kernel)
def pv1121093 : PrimeValue := ⟨1121093, pr1121093⟩
private theorem pr1121189 : PrimeCertificate 1121189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv280297]) (by decide +kernel)
def pv1121189 : PrimeValue := ⟨1121189, pr1121189⟩
private theorem pr1121369 : PrimeCertificate 1121369 :=
  certifyPrime (q := pv3) (ls := [pv2,pv140171]) (by decide +kernel)
def pv1121369 : PrimeValue := ⟨1121369, pr1121369⟩
private theorem pr1121423 : PrimeCertificate 1121423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv32983]) (by decide +kernel)
def pv1121423 : PrimeValue := ⟨1121423, pr1121423⟩
private theorem pr1121699 : PrimeCertificate 1121699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv13043]) (by decide +kernel)
def pv1121699 : PrimeValue := ⟨1121699, pr1121699⟩
private theorem pr1121831 : PrimeCertificate 1121831 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv17,pv6599]) (by decide +kernel)
def pv1121831 : PrimeValue := ⟨1121831, pr1121831⟩
private theorem pr1121993 : PrimeCertificate 1121993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv140249]) (by decide +kernel)
def pv1121993 : PrimeValue := ⟨1121993, pr1121993⟩
private theorem pr1122113 : PrimeCertificate 1122113 :=
  certifyPrime (q := pv3) (ls := [pv2,pv89,pv197]) (by decide +kernel)
def pv1122113 : PrimeValue := ⟨1122113, pr1122113⟩
private theorem pr1122281 : PrimeCertificate 1122281 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv28057]) (by decide +kernel)
def pv1122281 : PrimeValue := ⟨1122281, pr1122281⟩
private theorem pr1122389 : PrimeCertificate 1122389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv280597]) (by decide +kernel)
def pv1122389 : PrimeValue := ⟨1122389, pr1122389⟩
private theorem pr1122431 : PrimeCertificate 1122431 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv107,pv1049]) (by decide +kernel)
def pv1122431 : PrimeValue := ⟨1122431, pr1122431⟩
private theorem pr1122449 : PrimeCertificate 1122449 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv73]) (by decide +kernel)
def pv1122449 : PrimeValue := ⟨1122449, pr1122449⟩
private theorem pr1122623 : PrimeCertificate 1122623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv563,pv997]) (by decide +kernel)
def pv1122623 : PrimeValue := ⟨1122623, pr1122623⟩
private theorem pr1122659 : PrimeCertificate 1122659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv83,pv6763]) (by decide +kernel)
def pv1122659 : PrimeValue := ⟨1122659, pr1122659⟩
private theorem pr1122899 : PrimeCertificate 1122899 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv80207]) (by decide +kernel)
def pv1122899 : PrimeValue := ⟨1122899, pr1122899⟩
private theorem pr1123541 : PrimeCertificate 1123541 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv5107]) (by decide +kernel)
def pv1123541 : PrimeValue := ⟨1123541, pr1123541⟩
private theorem pr1123901 : PrimeCertificate 1123901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11239]) (by decide +kernel)
def pv1123901 : PrimeValue := ⟨1123901, pr1123901⟩
private theorem pr1123943 : PrimeCertificate 1123943 :=
  certifyPrime (q := pv5) (ls := [pv2,pv727,pv773]) (by decide +kernel)
def pv1123943 : PrimeValue := ⟨1123943, pr1123943⟩
private theorem pr1123961 : PrimeCertificate 1123961 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv28099]) (by decide +kernel)
def pv1123961 : PrimeValue := ⟨1123961, pr1123961⟩
private theorem pr1124219 : PrimeCertificate 1124219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv683,pv823]) (by decide +kernel)
def pv1124219 : PrimeValue := ⟨1124219, pr1124219⟩
private theorem pr1124351 : PrimeCertificate 1124351 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv113,pv199]) (by decide +kernel)
def pv1124351 : PrimeValue := ⟨1124351, pr1124351⟩
private theorem pr1124369 : PrimeCertificate 1124369 :=
  certifyPrime (q := pv23) (ls := [pv2,pv7,pv10039]) (by decide +kernel)
def pv1124369 : PrimeValue := ⟨1124369, pr1124369⟩
private theorem pr1124423 : PrimeCertificate 1124423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv59,pv733]) (by decide +kernel)
def pv1124423 : PrimeValue := ⟨1124423, pr1124423⟩
private theorem pr1124531 : PrimeCertificate 1124531 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv10223]) (by decide +kernel)
def pv1124531 : PrimeValue := ⟨1124531, pr1124531⟩
private theorem pr1124603 : PrimeCertificate 1124603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv562301]) (by decide +kernel)
def pv1124603 : PrimeValue := ⟨1124603, pr1124603⟩
private theorem pr1124681 : PrimeCertificate 1124681 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv31,pv907]) (by decide +kernel)
def pv1124681 : PrimeValue := ⟨1124681, pr1124681⟩
private theorem pr1124699 : PrimeCertificate 1124699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv562349]) (by decide +kernel)
def pv1124699 : PrimeValue := ⟨1124699, pr1124699⟩
private theorem pr1124741 : PrimeCertificate 1124741 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv56237]) (by decide +kernel)
def pv1124741 : PrimeValue := ⟨1124741, pr1124741⟩
private theorem pr1124789 : PrimeCertificate 1124789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv17,pv139]) (by decide +kernel)
def pv1124789 : PrimeValue := ⟨1124789, pr1124789⟩
private theorem pr1124993 : PrimeCertificate 1124993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv17,pv47]) (by decide +kernel)
def pv1124993 : PrimeValue := ⟨1124993, pr1124993⟩
private theorem pr1125209 : PrimeCertificate 1125209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv71,pv283]) (by decide +kernel)
def pv1125209 : PrimeValue := ⟨1125209, pr1125209⟩
private theorem pr1125581 : PrimeCertificate 1125581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv167,pv337]) (by decide +kernel)
def pv1125581 : PrimeValue := ⟨1125581, pr1125581⟩
private theorem pr1125599 : PrimeCertificate 1125599 :=
  certifyPrime (q := pv13) (ls := [pv2,pv19,pv1559]) (by decide +kernel)
def pv1125599 : PrimeValue := ⟨1125599, pr1125599⟩
private theorem pr1125713 : PrimeCertificate 1125713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv19,pv23]) (by decide +kernel)
def pv1125713 : PrimeValue := ⟨1125713, pr1125713⟩
private theorem pr1126043 : PrimeCertificate 1126043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv563021]) (by decide +kernel)
def pv1126043 : PrimeValue := ⟨1126043, pr1126043⟩
private theorem pr1126259 : PrimeCertificate 1126259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv80447]) (by decide +kernel)
def pv1126259 : PrimeValue := ⟨1126259, pr1126259⟩
private theorem pr1126283 : PrimeCertificate 1126283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv107,pv277]) (by decide +kernel)
def pv1126283 : PrimeValue := ⟨1126283, pr1126283⟩
private theorem pr1126319 : PrimeCertificate 1126319 :=
  certifyPrime (q := pv23) (ls := [pv2,pv17,pv157,pv211]) (by decide +kernel)
def pv1126319 : PrimeValue := ⟨1126319, pr1126319⟩
private theorem pr1126523 : PrimeCertificate 1126523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv1949]) (by decide +kernel)
def pv1126523 : PrimeValue := ⟨1126523, pr1126523⟩
private theorem pr1126661 : PrimeCertificate 1126661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv56333]) (by decide +kernel)
def pv1126661 : PrimeValue := ⟨1126661, pr1126661⟩
private theorem pr1127033 : PrimeCertificate 1127033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv8287]) (by decide +kernel)
def pv1127033 : PrimeValue := ⟨1127033, pr1127033⟩
private theorem pr1127039 : PrimeCertificate 1127039 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv51229]) (by decide +kernel)
def pv1127039 : PrimeValue := ⟨1127039, pr1127039⟩
private theorem pr1127111 : PrimeCertificate 1127111 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv269,pv419]) (by decide +kernel)
def pv1127111 : PrimeValue := ⟨1127111, pr1127111⟩
private theorem pr1127123 : PrimeCertificate 1127123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv563561]) (by decide +kernel)
def pv1127123 : PrimeValue := ⟨1127123, pr1127123⟩
private theorem pr1127303 : PrimeCertificate 1127303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv51241]) (by decide +kernel)
def pv1127303 : PrimeValue := ⟨1127303, pr1127303⟩
private theorem pr1127453 : PrimeCertificate 1127453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89,pv3167]) (by decide +kernel)
def pv1127453 : PrimeValue := ⟨1127453, pr1127453⟩
private theorem pr1127531 : PrimeCertificate 1127531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv47,pv2399]) (by decide +kernel)
def pv1127531 : PrimeValue := ⟨1127531, pr1127531⟩
private theorem pr1127573 : PrimeCertificate 1127573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv281893]) (by decide +kernel)
def pv1127573 : PrimeValue := ⟨1127573, pr1127573⟩
private theorem pr1127891 : PrimeCertificate 1127891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv43,pv61]) (by decide +kernel)
def pv1127891 : PrimeValue := ⟨1127891, pr1127891⟩
private theorem pr1127993 : PrimeCertificate 1127993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv41,pv181]) (by decide +kernel)
def pv1127993 : PrimeValue := ⟨1127993, pr1127993⟩
private theorem pr1128089 : PrimeCertificate 1128089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv10847]) (by decide +kernel)
def pv1128089 : PrimeValue := ⟨1128089, pr1128089⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
