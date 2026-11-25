/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table141
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table141.pv1128233
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table021
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table031
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table042
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table043
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table116
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table117
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table118

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr1128233 : PrimeCertificate 1128233 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv20147]) (by decide +kernel)
def pv1128233 : PrimeValue := ⟨1128233, pr1128233⟩
private theorem pr1128371 : PrimeCertificate 1128371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv53,pv2129]) (by decide +kernel)
def pv1128371 : PrimeValue := ⟨1128371, pr1128371⟩
private theorem pr1128503 : PrimeCertificate 1128503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv564251]) (by decide +kernel)
def pv1128503 : PrimeValue := ⟨1128503, pr1128503⟩
private theorem pr1128623 : PrimeCertificate 1128623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv29,pv61]) (by decide +kernel)
def pv1128623 : PrimeValue := ⟨1128623, pr1128623⟩
private theorem pr1128719 : PrimeCertificate 1128719 :=
  certifyPrime (q := pv7) (ls := [pv2,pv564359]) (by decide +kernel)
def pv1128719 : PrimeValue := ⟨1128719, pr1128719⟩
private theorem pr1128773 : PrimeCertificate 1128773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv9103]) (by decide +kernel)
def pv1128773 : PrimeValue := ⟨1128773, pr1128773⟩
private theorem pr1128779 : PrimeCertificate 1128779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv80627]) (by decide +kernel)
def pv1128779 : PrimeValue := ⟨1128779, pr1128779⟩
private theorem pr1128821 : PrimeCertificate 1128821 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv11,pv733]) (by decide +kernel)
def pv1128821 : PrimeValue := ⟨1128821, pr1128821⟩
private theorem pr1128899 : PrimeCertificate 1128899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv564449]) (by decide +kernel)
def pv1128899 : PrimeValue := ⟨1128899, pr1128899⟩
private theorem pr1129169 : PrimeCertificate 1129169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv70573]) (by decide +kernel)
def pv1129169 : PrimeValue := ⟨1129169, pr1129169⟩
private theorem pr1129391 : PrimeCertificate 1129391 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv112939]) (by decide +kernel)
def pv1129391 : PrimeValue := ⟨1129391, pr1129391⟩
private theorem pr1129409 : PrimeCertificate 1129409 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv2521]) (by decide +kernel)
def pv1129409 : PrimeValue := ⟨1129409, pr1129409⟩
private theorem pr1129571 : PrimeCertificate 1129571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv8689]) (by decide +kernel)
def pv1129571 : PrimeValue := ⟨1129571, pr1129571⟩
private theorem pr1129619 : PrimeCertificate 1129619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv80687]) (by decide +kernel)
def pv1129619 : PrimeValue := ⟨1129619, pr1129619⟩
private theorem pr1129763 : PrimeCertificate 1129763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv564881]) (by decide +kernel)
def pv1129763 : PrimeValue := ⟨1129763, pr1129763⟩
private theorem pr1129853 : PrimeCertificate 1129853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv12281]) (by decide +kernel)
def pv1129853 : PrimeValue := ⟨1129853, pr1129853⟩
private theorem pr1130081 : PrimeCertificate 1130081 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv7,pv1009]) (by decide +kernel)
def pv1130081 : PrimeValue := ⟨1130081, pr1130081⟩
private theorem pr1130273 : PrimeCertificate 1130273 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv13,pv19]) (by decide +kernel)
def pv1130273 : PrimeValue := ⟨1130273, pr1130273⟩
private theorem pr1130429 : PrimeCertificate 1130429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv21739]) (by decide +kernel)
def pv1130429 : PrimeValue := ⟨1130429, pr1130429⟩
private theorem pr1130819 : PrimeCertificate 1130819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv23,pv31,pv61]) (by decide +kernel)
def pv1130819 : PrimeValue := ⟨1130819, pr1130819⟩
private theorem pr1130963 : PrimeCertificate 1130963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv80783]) (by decide +kernel)
def pv1130963 : PrimeValue := ⟨1130963, pr1130963⟩
private theorem pr1131479 : PrimeCertificate 1131479 :=
  certifyPrime (q := pv13) (ls := [pv2,pv47,pv12037]) (by decide +kernel)
def pv1131479 : PrimeValue := ⟨1131479, pr1131479⟩
private theorem pr1131569 : PrimeCertificate 1131569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv197,pv359]) (by decide +kernel)
def pv1131569 : PrimeValue := ⟨1131569, pr1131569⟩
private theorem pr1131653 : PrimeCertificate 1131653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv282913]) (by decide +kernel)
def pv1131653 : PrimeValue := ⟨1131653, pr1131653⟩
private theorem pr1131821 : PrimeCertificate 1131821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv56591]) (by decide +kernel)
def pv1131821 : PrimeValue := ⟨1131821, pr1131821⟩
private theorem pr1131869 : PrimeCertificate 1131869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv53,pv281]) (by decide +kernel)
def pv1131869 : PrimeValue := ⟨1131869, pr1131869⟩
private theorem pr1131881 : PrimeCertificate 1131881 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv28297]) (by decide +kernel)
def pv1131881 : PrimeValue := ⟨1131881, pr1131881⟩
private theorem pr1132091 : PrimeCertificate 1132091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv113209]) (by decide +kernel)
def pv1132091 : PrimeValue := ⟨1132091, pr1132091⟩
private theorem pr1132139 : PrimeCertificate 1132139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv193,pv419]) (by decide +kernel)
def pv1132139 : PrimeValue := ⟨1132139, pr1132139⟩
private theorem pr1132643 : PrimeCertificate 1132643 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv17,pv4759]) (by decide +kernel)
def pv1132643 : PrimeValue := ⟨1132643, pr1132643⟩
private theorem pr1132661 : PrimeCertificate 1132661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv56633]) (by decide +kernel)
def pv1132661 : PrimeValue := ⟨1132661, pr1132661⟩
private theorem pr1132721 : PrimeCertificate 1132721 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv14159]) (by decide +kernel)
def pv1132721 : PrimeValue := ⟨1132721, pr1132721⟩
private theorem pr1132793 : PrimeCertificate 1132793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv43,pv89]) (by decide +kernel)
def pv1132793 : PrimeValue := ⟨1132793, pr1132793⟩
private theorem pr1132811 : PrimeCertificate 1132811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv16183]) (by decide +kernel)
def pv1132811 : PrimeValue := ⟨1132811, pr1132811⟩
private theorem pr1132823 : PrimeCertificate 1132823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv53,pv10687]) (by decide +kernel)
def pv1132823 : PrimeValue := ⟨1132823, pr1132823⟩
private theorem pr1132949 : PrimeCertificate 1132949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv16661]) (by decide +kernel)
def pv1132949 : PrimeValue := ⟨1132949, pr1132949⟩
private theorem pr1133039 : PrimeCertificate 1133039 :=
  certifyPrime (q := pv13) (ls := [pv2,pv397,pv1427]) (by decide +kernel)
def pv1133039 : PrimeValue := ⟨1133039, pr1133039⟩
private theorem pr1133579 : PrimeCertificate 1133579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv23,pv1297]) (by decide +kernel)
def pv1133579 : PrimeValue := ⟨1133579, pr1133579⟩
private theorem pr1133651 : PrimeCertificate 1133651 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv7,pv41,pv79]) (by decide +kernel)
def pv1133651 : PrimeValue := ⟨1133651, pr1133651⟩
private theorem pr1133861 : PrimeCertificate 1133861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv13,pv89]) (by decide +kernel)
def pv1133861 : PrimeValue := ⟨1133861, pr1133861⟩
private theorem pr1133903 : PrimeCertificate 1133903 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv11,pv37,pv199]) (by decide +kernel)
def pv1133903 : PrimeValue := ⟨1133903, pr1133903⟩
private theorem pr1134071 : PrimeCertificate 1134071 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv17,pv953]) (by decide +kernel)
def pv1134071 : PrimeValue := ⟨1134071, pr1134071⟩
private theorem pr1134389 : PrimeCertificate 1134389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv6917]) (by decide +kernel)
def pv1134389 : PrimeValue := ⟨1134389, pr1134389⟩
private theorem pr1134443 : PrimeCertificate 1134443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv103,pv5507]) (by decide +kernel)
def pv1134443 : PrimeValue := ⟨1134443, pr1134443⟩
private theorem pr1134719 : PrimeCertificate 1134719 :=
  certifyPrime (q := pv11) (ls := [pv2,pv13,pv19,pv2297]) (by decide +kernel)
def pv1134719 : PrimeValue := ⟨1134719, pr1134719⟩
private theorem pr1135091 : PrimeCertificate 1135091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv17,pv607]) (by decide +kernel)
def pv1135091 : PrimeValue := ⟨1135091, pr1135091⟩
private theorem pr1135133 : PrimeCertificate 1135133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv163,pv1741]) (by decide +kernel)
def pv1135133 : PrimeValue := ⟨1135133, pr1135133⟩
private theorem pr1135229 : PrimeCertificate 1135229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv283807]) (by decide +kernel)
def pv1135229 : PrimeValue := ⟨1135229, pr1135229⟩
private theorem pr1135241 : PrimeCertificate 1135241 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv101,pv281]) (by decide +kernel)
def pv1135241 : PrimeValue := ⟨1135241, pr1135241⟩
private theorem pr1135619 : PrimeCertificate 1135619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv41,pv1259]) (by decide +kernel)
def pv1135619 : PrimeValue := ⟨1135619, pr1135619⟩
private theorem pr1135643 : PrimeCertificate 1135643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv233,pv2437]) (by decide +kernel)
def pv1135643 : PrimeValue := ⟨1135643, pr1135643⟩
private theorem pr1135703 : PrimeCertificate 1135703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv33403]) (by decide +kernel)
def pv1135703 : PrimeValue := ⟨1135703, pr1135703⟩
private theorem pr1135721 : PrimeCertificate 1135721 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv28393]) (by decide +kernel)
def pv1135721 : PrimeValue := ⟨1135721, pr1135721⟩
private theorem pr1135913 : PrimeCertificate 1135913 :=
  certifyPrime (q := pv3) (ls := [pv2,pv107,pv1327]) (by decide +kernel)
def pv1135913 : PrimeValue := ⟨1135913, pr1135913⟩
private theorem pr1136111 : PrimeCertificate 1136111 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv17,pv41,pv163]) (by decide +kernel)
def pv1136111 : PrimeValue := ⟨1136111, pr1136111⟩
private theorem pr1136231 : PrimeCertificate 1136231 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv113623]) (by decide +kernel)
def pv1136231 : PrimeValue := ⟨1136231, pr1136231⟩
private theorem pr1136309 : PrimeCertificate 1136309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv4657]) (by decide +kernel)
def pv1136309 : PrimeValue := ⟨1136309, pr1136309⟩
private theorem pr1136363 : PrimeCertificate 1136363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv227,pv2503]) (by decide +kernel)
def pv1136363 : PrimeValue := ⟨1136363, pr1136363⟩
private theorem pr1136633 : PrimeCertificate 1136633 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv20297]) (by decide +kernel)
def pv1136633 : PrimeValue := ⟨1136633, pr1136633⟩
private theorem pr1136651 : PrimeCertificate 1136651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv127,pv179]) (by decide +kernel)
def pv1136651 : PrimeValue := ⟨1136651, pr1136651⟩
private theorem pr1136699 : PrimeCertificate 1136699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv568349]) (by decide +kernel)
def pv1136699 : PrimeValue := ⟨1136699, pr1136699⟩
private theorem pr1136981 : PrimeCertificate 1136981 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv4373]) (by decide +kernel)
def pv1136981 : PrimeValue := ⟨1136981, pr1136981⟩
private theorem pr1137203 : PrimeCertificate 1137203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv51691]) (by decide +kernel)
def pv1137203 : PrimeValue := ⟨1137203, pr1137203⟩
private theorem pr1137341 : PrimeCertificate 1137341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv41,pv73]) (by decide +kernel)
def pv1137341 : PrimeValue := ⟨1137341, pr1137341⟩
private theorem pr1137551 : PrimeCertificate 1137551 :=
  certifyPrime (q := pv29) (ls := [pv2,pv5,pv22751]) (by decide +kernel)
def pv1137551 : PrimeValue := ⟨1137551, pr1137551⟩
private theorem pr1137569 : PrimeCertificate 1137569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv1871]) (by decide +kernel)
def pv1137569 : PrimeValue := ⟨1137569, pr1137569⟩
private theorem pr1137659 : PrimeCertificate 1137659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv271,pv2099]) (by decide +kernel)
def pv1137659 : PrimeValue := ⟨1137659, pr1137659⟩
private theorem pr1137803 : PrimeCertificate 1137803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv397,pv1433]) (by decide +kernel)
def pv1137803 : PrimeValue := ⟨1137803, pr1137803⟩
private theorem pr1137809 : PrimeCertificate 1137809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv10159]) (by decide +kernel)
def pv1137809 : PrimeValue := ⟨1137809, pr1137809⟩
private theorem pr1138391 : PrimeCertificate 1138391 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv79,pv131]) (by decide +kernel)
def pv1138391 : PrimeValue := ⟨1138391, pr1138391⟩
private theorem pr1138433 : PrimeCertificate 1138433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv4447]) (by decide +kernel)
def pv1138433 : PrimeValue := ⟨1138433, pr1138433⟩
private theorem pr1138589 : PrimeCertificate 1138589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv113,pv229]) (by decide +kernel)
def pv1138589 : PrimeValue := ⟨1138589, pr1138589⟩
private theorem pr1138751 : PrimeCertificate 1138751 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv911]) (by decide +kernel)
def pv1138751 : PrimeValue := ⟨1138751, pr1138751⟩
private theorem pr1138829 : PrimeCertificate 1138829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv284707]) (by decide +kernel)
def pv1138829 : PrimeValue := ⟨1138829, pr1138829⟩
private theorem pr1138883 : PrimeCertificate 1138883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv311,pv1831]) (by decide +kernel)
def pv1138883 : PrimeValue := ⟨1138883, pr1138883⟩
private theorem pr1139003 : PrimeCertificate 1139003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv18371]) (by decide +kernel)
def pv1139003 : PrimeValue := ⟨1139003, pr1139003⟩
private theorem pr1139321 : PrimeCertificate 1139321 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv13,pv313]) (by decide +kernel)
def pv1139321 : PrimeValue := ⟨1139321, pr1139321⟩
private theorem pr1139423 : PrimeCertificate 1139423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv569711]) (by decide +kernel)
def pv1139423 : PrimeValue := ⟨1139423, pr1139423⟩
private theorem pr1139471 : PrimeCertificate 1139471 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv113947]) (by decide +kernel)
def pv1139471 : PrimeValue := ⟨1139471, pr1139471⟩
private theorem pr1139483 : PrimeCertificate 1139483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv101,pv5641]) (by decide +kernel)
def pv1139483 : PrimeValue := ⟨1139483, pr1139483⟩
private theorem pr1139531 : PrimeCertificate 1139531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv73,pv223]) (by decide +kernel)
def pv1139531 : PrimeValue := ⟨1139531, pr1139531⟩
private theorem pr1139669 : PrimeCertificate 1139669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv284917]) (by decide +kernel)
def pv1139669 : PrimeValue := ⟨1139669, pr1139669⟩
private theorem pr1139681 : PrimeCertificate 1139681 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17,pv419]) (by decide +kernel)
def pv1139681 : PrimeValue := ⟨1139681, pr1139681⟩
private theorem pr1139843 : PrimeCertificate 1139843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv197,pv263]) (by decide +kernel)
def pv1139843 : PrimeValue := ⟨1139843, pr1139843⟩
private theorem pr1139921 : PrimeCertificate 1139921 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv14249]) (by decide +kernel)
def pv1139921 : PrimeValue := ⟨1139921, pr1139921⟩
private theorem pr1140101 : PrimeCertificate 1140101 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv877]) (by decide +kernel)
def pv1140101 : PrimeValue := ⟨1140101, pr1140101⟩
private theorem pr1140143 : PrimeCertificate 1140143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv570071]) (by decide +kernel)
def pv1140143 : PrimeValue := ⟨1140143, pr1140143⟩
private theorem pr1140203 : PrimeCertificate 1140203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv23,pv3541]) (by decide +kernel)
def pv1140203 : PrimeValue := ⟨1140203, pr1140203⟩
private theorem pr1140311 : PrimeCertificate 1140311 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv114031]) (by decide +kernel)
def pv1140311 : PrimeValue := ⟨1140311, pr1140311⟩
private theorem pr1140341 : PrimeCertificate 1140341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv37,pv67]) (by decide +kernel)
def pv1140341 : PrimeValue := ⟨1140341, pr1140341⟩
private theorem pr1140383 : PrimeCertificate 1140383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv570191]) (by decide +kernel)
def pv1140383 : PrimeValue := ⟨1140383, pr1140383⟩
private theorem pr1140413 : PrimeCertificate 1140413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv241]) (by decide +kernel)
def pv1140413 : PrimeValue := ⟨1140413, pr1140413⟩
private theorem pr1140449 : PrimeCertificate 1140449 :=
  certifyPrime (q := pv3) (ls := [pv2,pv157,pv227]) (by decide +kernel)
def pv1140449 : PrimeValue := ⟨1140449, pr1140449⟩
private theorem pr1140539 : PrimeCertificate 1140539 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv41,pv1987]) (by decide +kernel)
def pv1140539 : PrimeValue := ⟨1140539, pr1140539⟩
private theorem pr1140563 : PrimeCertificate 1140563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv15413]) (by decide +kernel)
def pv1140563 : PrimeValue := ⟨1140563, pr1140563⟩
private theorem pr1140803 : PrimeCertificate 1140803 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv17,pv29,pv89]) (by decide +kernel)
def pv1140803 : PrimeValue := ⟨1140803, pr1140803⟩
private theorem pr1140911 : PrimeCertificate 1140911 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv271,pv421]) (by decide +kernel)
def pv1140911 : PrimeValue := ⟨1140911, pr1140911⟩
private theorem pr1141103 : PrimeCertificate 1141103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv30029]) (by decide +kernel)
def pv1141103 : PrimeValue := ⟨1141103, pr1141103⟩
private theorem pr1141223 : PrimeCertificate 1141223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv127,pv4493]) (by decide +kernel)
def pv1141223 : PrimeValue := ⟨1141223, pr1141223⟩
private theorem pr1141229 : PrimeCertificate 1141229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv37,pv701]) (by decide +kernel)
def pv1141229 : PrimeValue := ⟨1141229, pr1141229⟩
private theorem pr1141379 : PrimeCertificate 1141379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv81527]) (by decide +kernel)
def pv1141379 : PrimeValue := ⟨1141379, pr1141379⟩
private theorem pr1141769 : PrimeCertificate 1141769 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41,pv59]) (by decide +kernel)
def pv1141769 : PrimeValue := ⟨1141769, pr1141769⟩
private theorem pr1141853 : PrimeCertificate 1141853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv285463]) (by decide +kernel)
def pv1141853 : PrimeValue := ⟨1141853, pr1141853⟩
private theorem pr1141901 : PrimeCertificate 1141901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv601]) (by decide +kernel)
def pv1141901 : PrimeValue := ⟨1141901, pr1141901⟩
private theorem pr1142021 : PrimeCertificate 1142021 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv29,pv179]) (by decide +kernel)
def pv1142021 : PrimeValue := ⟨1142021, pr1142021⟩
private theorem pr1142243 : PrimeCertificate 1142243 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv30059]) (by decide +kernel)
def pv1142243 : PrimeValue := ⟨1142243, pr1142243⟩
private theorem pr1142549 : PrimeCertificate 1142549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv23,pv1129]) (by decide +kernel)
def pv1142549 : PrimeValue := ⟨1142549, pr1142549⟩
private theorem pr1142573 : PrimeCertificate 1142573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv285643]) (by decide +kernel)
def pv1142573 : PrimeValue := ⟨1142573, pr1142573⟩
private theorem pr1142633 : PrimeCertificate 1142633 :=
  certifyPrime (q := pv3) (ls := [pv2,pv233,pv613]) (by decide +kernel)
def pv1142633 : PrimeValue := ⟨1142633, pr1142633⟩
private theorem pr1143101 : PrimeCertificate 1143101 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv23,pv71]) (by decide +kernel)
def pv1143101 : PrimeValue := ⟨1143101, pr1143101⟩
private theorem pr1144001 : PrimeCertificate 1144001 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv13]) (by decide +kernel)
def pv1144001 : PrimeValue := ⟨1144001, pr1144001⟩
private theorem pr1144061 : PrimeCertificate 1144061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv57203]) (by decide +kernel)
def pv1144061 : PrimeValue := ⟨1144061, pr1144061⟩
private theorem pr1144103 : PrimeCertificate 1144103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv572051]) (by decide +kernel)
def pv1144103 : PrimeValue := ⟨1144103, pr1144103⟩
private theorem pr1144301 : PrimeCertificate 1144301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11443]) (by decide +kernel)
def pv1144301 : PrimeValue := ⟨1144301, pr1144301⟩
private theorem pr1144343 : PrimeCertificate 1144343 :=
  certifyPrime (q := pv7) (ls := [pv2,pv23,pv24877]) (by decide +kernel)
def pv1144343 : PrimeValue := ⟨1144343, pr1144343⟩
private theorem pr1144439 : PrimeCertificate 1144439 :=
  certifyPrime (q := pv7) (ls := [pv2,pv389,pv1471]) (by decide +kernel)
def pv1144439 : PrimeValue := ⟨1144439, pr1144439⟩
private theorem pr1144529 : PrimeCertificate 1144529 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11,pv929]) (by decide +kernel)
def pv1144529 : PrimeValue := ⟨1144529, pr1144529⟩
private theorem pr1144589 : PrimeCertificate 1144589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv5399]) (by decide +kernel)
def pv1144589 : PrimeValue := ⟨1144589, pr1144589⟩
private theorem pr1144823 : PrimeCertificate 1144823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv81773]) (by decide +kernel)
def pv1144823 : PrimeValue := ⟨1144823, pr1144823⟩
private theorem pr1144889 : PrimeCertificate 1144889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv143111]) (by decide +kernel)
def pv1144889 : PrimeValue := ⟨1144889, pr1144889⟩
private theorem pr1144901 : PrimeCertificate 1144901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv107]) (by decide +kernel)
def pv1144901 : PrimeValue := ⟨1144901, pr1144901⟩
private theorem pr1144919 : PrimeCertificate 1144919 :=
  certifyPrime (q := pv17) (ls := [pv2,pv43,pv13313]) (by decide +kernel)
def pv1144919 : PrimeValue := ⟨1144919, pr1144919⟩
private theorem pr1144931 : PrimeCertificate 1144931 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv114493]) (by decide +kernel)
def pv1144931 : PrimeValue := ⟨1144931, pr1144931⟩
private theorem pr1145003 : PrimeCertificate 1145003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv15473]) (by decide +kernel)
def pv1145003 : PrimeValue := ⟨1145003, pr1145003⟩
private theorem pr1145129 : PrimeCertificate 1145129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv143141]) (by decide +kernel)
def pv1145129 : PrimeValue := ⟨1145129, pr1145129⟩
private theorem pr1145141 : PrimeCertificate 1145141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31,pv1847]) (by decide +kernel)
def pv1145141 : PrimeValue := ⟨1145141, pr1145141⟩
private theorem pr1145849 : PrimeCertificate 1145849 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv29,pv449]) (by decide +kernel)
def pv1145849 : PrimeValue := ⟨1145849, pr1145849⟩
private theorem pr1145873 : PrimeCertificate 1145873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv13,pv787]) (by decide +kernel)
def pv1145873 : PrimeValue := ⟨1145873, pr1145873⟩
private theorem pr1145999 : PrimeCertificate 1145999 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv23,pv3559]) (by decide +kernel)
def pv1145999 : PrimeValue := ⟨1145999, pr1145999⟩
private theorem pr1146083 : PrimeCertificate 1146083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv71,pv1153]) (by decide +kernel)
def pv1146083 : PrimeValue := ⟨1146083, pr1146083⟩
private theorem pr1146179 : PrimeCertificate 1146179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv53,pv983]) (by decide +kernel)
def pv1146179 : PrimeValue := ⟨1146179, pr1146179⟩
private theorem pr1146461 : PrimeCertificate 1146461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv19,pv431]) (by decide +kernel)
def pv1146461 : PrimeValue := ⟨1146461, pr1146461⟩
private theorem pr1146569 : PrimeCertificate 1146569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv251,pv571]) (by decide +kernel)
def pv1146569 : PrimeValue := ⟨1146569, pr1146569⟩
private theorem pr1146713 : PrimeCertificate 1146713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv20477]) (by decide +kernel)
def pv1146713 : PrimeValue := ⟨1146713, pr1146713⟩
private theorem pr1146731 : PrimeCertificate 1146731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv8821]) (by decide +kernel)
def pv1146731 : PrimeValue := ⟨1146731, pr1146731⟩
private theorem pr1146779 : PrimeCertificate 1146779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv15497]) (by decide +kernel)
def pv1146779 : PrimeValue := ⟨1146779, pr1146779⟩
private theorem pr1147193 : PrimeCertificate 1147193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv193,pv743]) (by decide +kernel)
def pv1147193 : PrimeValue := ⟨1147193, pr1147193⟩
private theorem pr1147409 : PrimeCertificate 1147409 :=
  certifyPrime (q := pv3) (ls := [pv2,pv71713]) (by decide +kernel)
def pv1147409 : PrimeValue := ⟨1147409, pr1147409⟩
private theorem pr1147739 : PrimeCertificate 1147739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv33757]) (by decide +kernel)
def pv1147739 : PrimeValue := ⟨1147739, pr1147739⟩
private theorem pr1148039 : PrimeCertificate 1148039 :=
  certifyPrime (q := pv7) (ls := [pv2,pv103,pv5573]) (by decide +kernel)
def pv1148039 : PrimeValue := ⟨1148039, pr1148039⟩
private theorem pr1148453 : PrimeCertificate 1148453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv16889]) (by decide +kernel)
def pv1148453 : PrimeValue := ⟨1148453, pr1148453⟩
private theorem pr1148489 : PrimeCertificate 1148489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv31,pv421]) (by decide +kernel)
def pv1148489 : PrimeValue := ⟨1148489, pr1148489⟩
private theorem pr1148513 : PrimeCertificate 1148513 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv1889]) (by decide +kernel)
def pv1148513 : PrimeValue := ⟨1148513, pr1148513⟩
private theorem pr1148663 : PrimeCertificate 1148663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv353,pv1627]) (by decide +kernel)
def pv1148663 : PrimeValue := ⟨1148663, pr1148663⟩
private theorem pr1148879 : PrimeCertificate 1148879 :=
  certifyPrime (q := pv7) (ls := [pv2,pv574439]) (by decide +kernel)
def pv1148879 : PrimeValue := ⟨1148879, pr1148879⟩
private theorem pr1148921 : PrimeCertificate 1148921 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv28723]) (by decide +kernel)
def pv1148921 : PrimeValue := ⟨1148921, pr1148921⟩
private theorem pr1149059 : PrimeCertificate 1149059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv574529]) (by decide +kernel)
def pv1149059 : PrimeValue := ⟨1149059, pr1149059⟩
private theorem pr1149341 : PrimeCertificate 1149341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv57467]) (by decide +kernel)
def pv1149341 : PrimeValue := ⟨1149341, pr1149341⟩
private theorem pr1149539 : PrimeCertificate 1149539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv19,pv179]) (by decide +kernel)
def pv1149539 : PrimeValue := ⟨1149539, pr1149539⟩
private theorem pr1149569 : PrimeCertificate 1149569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv1283]) (by decide +kernel)
def pv1149569 : PrimeValue := ⟨1149569, pr1149569⟩
private theorem pr1149581 : PrimeCertificate 1149581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv229,pv251]) (by decide +kernel)
def pv1149581 : PrimeValue := ⟨1149581, pr1149581⟩
private theorem pr1149749 : PrimeCertificate 1149749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv287437]) (by decide +kernel)
def pv1149749 : PrimeValue := ⟨1149749, pr1149749⟩
private theorem pr1149773 : PrimeCertificate 1149773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv22111]) (by decide +kernel)
def pv1149773 : PrimeValue := ⟨1149773, pr1149773⟩
private theorem pr1149881 : PrimeCertificate 1149881 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv17,pv19,pv89]) (by decide +kernel)
def pv1149881 : PrimeValue := ⟨1149881, pr1149881⟩
private theorem pr1150031 : PrimeCertificate 1150031 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv2347]) (by decide +kernel)
def pv1150031 : PrimeValue := ⟨1150031, pr1150031⟩
private theorem pr1150139 : PrimeCertificate 1150139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv23,pv2273]) (by decide +kernel)
def pv1150139 : PrimeValue := ⟨1150139, pr1150139⟩
private theorem pr1150199 : PrimeCertificate 1150199 :=
  certifyPrime (q := pv13) (ls := [pv2,pv7,pv29,pv2833]) (by decide +kernel)
def pv1150199 : PrimeValue := ⟨1150199, pr1150199⟩
private theorem pr1150511 : PrimeCertificate 1150511 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv103,pv1117]) (by decide +kernel)
def pv1150511 : PrimeValue := ⟨1150511, pr1150511⟩
private theorem pr1150703 : PrimeCertificate 1150703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv82193]) (by decide +kernel)
def pv1150703 : PrimeValue := ⟨1150703, pr1150703⟩
private theorem pr1150739 : PrimeCertificate 1150739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv575369]) (by decide +kernel)
def pv1150739 : PrimeValue := ⟨1150739, pr1150739⟩
private theorem pr1150871 : PrimeCertificate 1150871 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv41,pv401]) (by decide +kernel)
def pv1150871 : PrimeValue := ⟨1150871, pr1150871⟩
private theorem pr1150949 : PrimeCertificate 1150949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv61,pv89]) (by decide +kernel)
def pv1150949 : PrimeValue := ⟨1150949, pr1150949⟩
private theorem pr1151021 : PrimeCertificate 1151021 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv19,pv233]) (by decide +kernel)
def pv1151021 : PrimeValue := ⟨1151021, pr1151021⟩
private theorem pr1151141 : PrimeCertificate 1151141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv57557]) (by decide +kernel)
def pv1151141 : PrimeValue := ⟨1151141, pr1151141⟩
private theorem pr1151399 : PrimeCertificate 1151399 :=
  certifyPrime (q := pv7) (ls := [pv2,pv575699]) (by decide +kernel)
def pv1151399 : PrimeValue := ⟨1151399, pr1151399⟩
private theorem pr1151651 : PrimeCertificate 1151651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31,pv743]) (by decide +kernel)
def pv1151651 : PrimeValue := ⟨1151651, pr1151651⟩
private theorem pr1151861 : PrimeCertificate 1151861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv57593]) (by decide +kernel)
def pv1151861 : PrimeValue := ⟨1151861, pr1151861⟩
private theorem pr1151933 : PrimeCertificate 1151933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv23,pv659]) (by decide +kernel)
def pv1151933 : PrimeValue := ⟨1151933, pr1151933⟩
private theorem pr1151963 : PrimeCertificate 1151963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv107,pv769]) (by decide +kernel)
def pv1151963 : PrimeValue := ⟨1151963, pr1151963⟩
private theorem pr1151999 : PrimeCertificate 1151999 :=
  certifyPrime (q := pv7) (ls := [pv2,pv67,pv8597]) (by decide +kernel)
def pv1151999 : PrimeValue := ⟨1151999, pr1151999⟩
private theorem pr1152029 : PrimeCertificate 1152029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv288007]) (by decide +kernel)
def pv1152029 : PrimeValue := ⟨1152029, pr1152029⟩
private theorem pr1152419 : PrimeCertificate 1152419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv233,pv2473]) (by decide +kernel)
def pv1152419 : PrimeValue := ⟨1152419, pr1152419⟩
private theorem pr1152881 : PrimeCertificate 1152881 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv14411]) (by decide +kernel)
def pv1152881 : PrimeValue := ⟨1152881, pr1152881⟩
private theorem pr1152941 : PrimeCertificate 1152941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv3391]) (by decide +kernel)
def pv1152941 : PrimeValue := ⟨1152941, pr1152941⟩
private theorem pr1153073 : PrimeCertificate 1153073 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv3793]) (by decide +kernel)
def pv1153073 : PrimeValue := ⟨1153073, pr1153073⟩
private theorem pr1153811 : PrimeCertificate 1153811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv53,pv311]) (by decide +kernel)
def pv1153811 : PrimeValue := ⟨1153811, pr1153811⟩
private theorem pr1154039 : PrimeCertificate 1154039 :=
  certifyPrime (q := pv17) (ls := [pv2,pv47,pv12277]) (by decide +kernel)
def pv1154039 : PrimeValue := ⟨1154039, pr1154039⟩
private theorem pr1154123 : PrimeCertificate 1154123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv347,pv1663]) (by decide +kernel)
def pv1154123 : PrimeValue := ⟨1154123, pr1154123⟩
private theorem pr1154339 : PrimeCertificate 1154339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv577169]) (by decide +kernel)
def pv1154339 : PrimeValue := ⟨1154339, pr1154339⟩
private theorem pr1154561 : PrimeCertificate 1154561 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv41]) (by decide +kernel)
def pv1154561 : PrimeValue := ⟨1154561, pr1154561⟩
private theorem pr1154633 : PrimeCertificate 1154633 :=
  certifyPrime (q := pv3) (ls := [pv2,pv101,pv1429]) (by decide +kernel)
def pv1154633 : PrimeValue := ⟨1154633, pr1154633⟩
private theorem pr1154651 : PrimeCertificate 1154651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv3299]) (by decide +kernel)
def pv1154651 : PrimeValue := ⟨1154651, pr1154651⟩
private theorem pr1154771 : PrimeCertificate 1154771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv37,pv3121]) (by decide +kernel)
def pv1154771 : PrimeValue := ⟨1154771, pr1154771⟩
private theorem pr1155053 : PrimeCertificate 1155053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv7043]) (by decide +kernel)
def pv1155053 : PrimeValue := ⟨1155053, pr1155053⟩
private theorem pr1155179 : PrimeCertificate 1155179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv577589]) (by decide +kernel)
def pv1155179 : PrimeValue := ⟨1155179, pr1155179⟩
private theorem pr1155239 : PrimeCertificate 1155239 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv19,pv43,pv101]) (by decide +kernel)
def pv1155239 : PrimeValue := ⟨1155239, pr1155239⟩
private theorem pr1155449 : PrimeCertificate 1155449 :=
  certifyPrime (q := pv17) (ls := [pv2,pv7,pv47,pv439]) (by decide +kernel)
def pv1155449 : PrimeValue := ⟨1155449, pr1155449⟩
private theorem pr1155611 : PrimeCertificate 1155611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv115561]) (by decide +kernel)
def pv1155611 : PrimeValue := ⟨1155611, pr1155611⟩
private theorem pr1156013 : PrimeCertificate 1156013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13,pv43,pv47]) (by decide +kernel)
def pv1156013 : PrimeValue := ⟨1156013, pr1156013⟩
private theorem pr1156073 : PrimeCertificate 1156073 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv61,pv103]) (by decide +kernel)
def pv1156073 : PrimeValue := ⟨1156073, pr1156073⟩
private theorem pr1156079 : PrimeCertificate 1156079 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv11,pv7507]) (by decide +kernel)
def pv1156079 : PrimeValue := ⟨1156079, pr1156079⟩
private theorem pr1156541 : PrimeCertificate 1156541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv751]) (by decide +kernel)
def pv1156541 : PrimeValue := ⟨1156541, pr1156541⟩
private theorem pr1156553 : PrimeCertificate 1156553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv144569]) (by decide +kernel)
def pv1156553 : PrimeValue := ⟨1156553, pr1156553⟩
private theorem pr1156709 : PrimeCertificate 1156709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv109,pv379]) (by decide +kernel)
def pv1156709 : PrimeValue := ⟨1156709, pr1156709⟩
private theorem pr1156769 : PrimeCertificate 1156769 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv977]) (by decide +kernel)
def pv1156769 : PrimeValue := ⟨1156769, pr1156769⟩
private theorem pr1157099 : PrimeCertificate 1157099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv107,pv5407]) (by decide +kernel)
def pv1157099 : PrimeValue := ⟨1157099, pr1157099⟩
private theorem pr1157333 : PrimeCertificate 1157333 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv29,pv907]) (by decide +kernel)
def pv1157333 : PrimeValue := ⟨1157333, pr1157333⟩
private theorem pr1157363 : PrimeCertificate 1157363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv109,pv5309]) (by decide +kernel)
def pv1157363 : PrimeValue := ⟨1157363, pr1157363⟩
private theorem pr1157531 : PrimeCertificate 1157531 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv17,pv619]) (by decide +kernel)
def pv1157531 : PrimeValue := ⟨1157531, pr1157531⟩
private theorem pr1157699 : PrimeCertificate 1157699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59,pv9811]) (by decide +kernel)
def pv1157699 : PrimeValue := ⟨1157699, pr1157699⟩
private theorem pr1158089 : PrimeCertificate 1158089 :=
  certifyPrime (q := pv29) (ls := [pv2,pv19,pv401]) (by decide +kernel)
def pv1158089 : PrimeValue := ⟨1158089, pr1158089⟩
private theorem pr1158161 : PrimeCertificate 1158161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv31,pv467]) (by decide +kernel)
def pv1158161 : PrimeValue := ⟨1158161, pr1158161⟩
private theorem pr1158203 : PrimeCertificate 1158203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv29,pv1051]) (by decide +kernel)
def pv1158203 : PrimeValue := ⟨1158203, pr1158203⟩
private theorem pr1158539 : PrimeCertificate 1158539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv373,pv1553]) (by decide +kernel)
def pv1158539 : PrimeValue := ⟨1158539, pr1158539⟩
private theorem pr1158611 : PrimeCertificate 1158611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv115861]) (by decide +kernel)
def pv1158611 : PrimeValue := ⟨1158611, pr1158611⟩
private theorem pr1158719 : PrimeCertificate 1158719 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv31,pv1699]) (by decide +kernel)
def pv1158719 : PrimeValue := ⟨1158719, pr1158719⟩
private theorem pr1158953 : PrimeCertificate 1158953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv317,pv457]) (by decide +kernel)
def pv1158953 : PrimeValue := ⟨1158953, pr1158953⟩
private theorem pr1159001 : PrimeCertificate 1159001 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv19,pv61]) (by decide +kernel)
def pv1159001 : PrimeValue := ⟨1159001, pr1159001⟩
private theorem pr1159079 : PrimeCertificate 1159079 :=
  certifyPrime (q := pv11) (ls := [pv2,pv579539]) (by decide +kernel)
def pv1159079 : PrimeValue := ⟨1159079, pr1159079⟩
private theorem pr1159139 : PrimeCertificate 1159139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv579569]) (by decide +kernel)
def pv1159139 : PrimeValue := ⟨1159139, pr1159139⟩
private theorem pr1159241 : PrimeCertificate 1159241 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv73,pv397]) (by decide +kernel)
def pv1159241 : PrimeValue := ⟨1159241, pr1159241⟩
private theorem pr1159271 : PrimeCertificate 1159271 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv16561]) (by decide +kernel)
def pv1159271 : PrimeValue := ⟨1159271, pr1159271⟩
private theorem pr1159283 : PrimeCertificate 1159283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv579641]) (by decide +kernel)
def pv1159283 : PrimeValue := ⟨1159283, pr1159283⟩
private theorem pr1159421 : PrimeCertificate 1159421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29,pv1999]) (by decide +kernel)
def pv1159421 : PrimeValue := ⟨1159421, pr1159421⟩
private theorem pr1159649 : PrimeCertificate 1159649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv31,pv167]) (by decide +kernel)
def pv1159649 : PrimeValue := ⟨1159649, pr1159649⟩
private theorem pr1159661 : PrimeCertificate 1159661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv2521]) (by decide +kernel)
def pv1159661 : PrimeValue := ⟨1159661, pr1159661⟩
private theorem pr1160129 : PrimeCertificate 1160129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv18127]) (by decide +kernel)
def pv1160129 : PrimeValue := ⟨1160129, pr1160129⟩
private theorem pr1160213 : PrimeCertificate 1160213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv12611]) (by decide +kernel)
def pv1160213 : PrimeValue := ⟨1160213, pr1160213⟩
private theorem pr1160429 : PrimeCertificate 1160429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv290107]) (by decide +kernel)
def pv1160429 : PrimeValue := ⟨1160429, pr1160429⟩
private theorem pr1160543 : PrimeCertificate 1160543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv37,pv15683]) (by decide +kernel)
def pv1160543 : PrimeValue := ⟨1160543, pr1160543⟩
private theorem pr1161059 : PrimeCertificate 1161059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv580529]) (by decide +kernel)
def pv1161059 : PrimeValue := ⟨1161059, pr1161059⟩
private theorem pr1161113 : PrimeCertificate 1161113 :=
  certifyPrime (q := pv3) (ls := [pv2,pv145139]) (by decide +kernel)
def pv1161113 : PrimeValue := ⟨1161113, pr1161113⟩
private theorem pr1161239 : PrimeCertificate 1161239 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv59,pv757]) (by decide +kernel)
def pv1161239 : PrimeValue := ⟨1161239, pr1161239⟩
private theorem pr1161683 : PrimeCertificate 1161683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv20029]) (by decide +kernel)
def pv1161683 : PrimeValue := ⟨1161683, pr1161683⟩
private theorem pr1161791 : PrimeCertificate 1161791 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv2371]) (by decide +kernel)
def pv1161791 : PrimeValue := ⟨1161791, pr1161791⟩
private theorem pr1161851 : PrimeCertificate 1161851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv1223]) (by decide +kernel)
def pv1161851 : PrimeValue := ⟨1161851, pr1161851⟩
private theorem pr1161893 : PrimeCertificate 1161893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv290473]) (by decide +kernel)
def pv1161893 : PrimeValue := ⟨1161893, pr1161893⟩
private theorem pr1162061 : PrimeCertificate 1162061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv97,pv599]) (by decide +kernel)
def pv1162061 : PrimeValue := ⟨1162061, pr1162061⟩
private theorem pr1162079 : PrimeCertificate 1162079 :=
  certifyPrime (q := pv7) (ls := [pv2,pv19,pv53,pv577]) (by decide +kernel)
def pv1162079 : PrimeValue := ⟨1162079, pr1162079⟩
private theorem pr1162223 : PrimeCertificate 1162223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv34183]) (by decide +kernel)
def pv1162223 : PrimeValue := ⟨1162223, pr1162223⟩
private theorem pr1162229 : PrimeCertificate 1162229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv290557]) (by decide +kernel)
def pv1162229 : PrimeValue := ⟨1162229, pr1162229⟩
private theorem pr1162253 : PrimeCertificate 1162253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv31,pv103]) (by decide +kernel)
def pv1162253 : PrimeValue := ⟨1162253, pr1162253⟩
private theorem pr1162541 : PrimeCertificate 1162541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv37,pv1571]) (by decide +kernel)
def pv1162541 : PrimeValue := ⟨1162541, pr1162541⟩
private theorem pr1162571 : PrimeCertificate 1162571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv116257]) (by decide +kernel)
def pv1162571 : PrimeValue := ⟨1162571, pr1162571⟩
private theorem pr1162631 : PrimeCertificate 1162631 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv7,pv17,pv977]) (by decide +kernel)
def pv1162631 : PrimeValue := ⟨1162631, pr1162631⟩
private theorem pr1162649 : PrimeCertificate 1162649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv7649]) (by decide +kernel)
def pv1162649 : PrimeValue := ⟨1162649, pr1162649⟩
private theorem pr1162901 : PrimeCertificate 1162901 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv29,pv401]) (by decide +kernel)
def pv1162901 : PrimeValue := ⟨1162901, pr1162901⟩
private theorem pr1163003 : PrimeCertificate 1163003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv151,pv3851]) (by decide +kernel)
def pv1163003 : PrimeValue := ⟨1163003, pr1163003⟩
private theorem pr1163033 : PrimeCertificate 1163033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv53,pv211]) (by decide +kernel)
def pv1163033 : PrimeValue := ⟨1163033, pr1163033⟩
private theorem pr1163159 : PrimeCertificate 1163159 :=
  certifyPrime (q := pv7) (ls := [pv2,pv563,pv1033]) (by decide +kernel)
def pv1163159 : PrimeValue := ⟨1163159, pr1163159⟩
private theorem pr1163423 : PrimeCertificate 1163423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv29,pv1543]) (by decide +kernel)
def pv1163423 : PrimeValue := ⟨1163423, pr1163423⟩
private theorem pr1163699 : PrimeCertificate 1163699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv571,pv1019]) (by decide +kernel)
def pv1163699 : PrimeValue := ⟨1163699, pr1163699⟩
private theorem pr1163993 : PrimeCertificate 1163993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv83,pv1753]) (by decide +kernel)
def pv1163993 : PrimeValue := ⟨1163993, pr1163993⟩
private theorem pr1164071 : PrimeCertificate 1164071 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv59,pv1973]) (by decide +kernel)
def pv1164071 : PrimeValue := ⟨1164071, pr1164071⟩
private theorem pr1164413 : PrimeCertificate 1164413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv291103]) (by decide +kernel)
def pv1164413 : PrimeValue := ⟨1164413, pr1164413⟩
private theorem pr1164419 : PrimeCertificate 1164419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv582209]) (by decide +kernel)
def pv1164419 : PrimeValue := ⟨1164419, pr1164419⟩
private theorem pr1164629 : PrimeCertificate 1164629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv12659]) (by decide +kernel)
def pv1164629 : PrimeValue := ⟨1164629, pr1164629⟩
private theorem pr1164659 : PrimeCertificate 1164659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv167,pv317]) (by decide +kernel)
def pv1164659 : PrimeValue := ⟨1164659, pr1164659⟩
private theorem pr1164749 : PrimeCertificate 1164749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv1723]) (by decide +kernel)
def pv1164749 : PrimeValue := ⟨1164749, pr1164749⟩
private theorem pr1164791 : PrimeCertificate 1164791 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv11,pv10589]) (by decide +kernel)
def pv1164791 : PrimeValue := ⟨1164791, pr1164791⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
