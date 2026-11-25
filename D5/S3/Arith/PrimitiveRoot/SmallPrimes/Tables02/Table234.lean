/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table234
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table234.pv1175857
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table012
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table026
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table064
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table065

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr1175857 : PrimeCertificate 1175857 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv17,pv131]) (by decide +kernel)
def pv1175857 : PrimeValue := ⟨1175857, pr1175857⟩
private theorem pr1175959 : PrimeCertificate 1175959 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv17,pv61]) (by decide +kernel)
def pv1175959 : PrimeValue := ⟨1175959, pr1175959⟩
private theorem pr1175989 : PrimeCertificate 1175989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv59,pv151]) (by decide +kernel)
def pv1175989 : PrimeValue := ⟨1175989, pr1175989⟩
private theorem pr1176127 : PrimeCertificate 1176127 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv41,pv683]) (by decide +kernel)
def pv1176127 : PrimeValue := ⟨1176127, pr1176127⟩
private theorem pr1176223 : PrimeCertificate 1176223 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv43,pv47,pv97]) (by decide +kernel)
def pv1176223 : PrimeValue := ⟨1176223, pr1176223⟩
private theorem pr1176277 : PrimeCertificate 1176277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv83,pv1181]) (by decide +kernel)
def pv1176277 : PrimeValue := ⟨1176277, pr1176277⟩
private theorem pr1176463 : PrimeCertificate 1176463 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv9337]) (by decide +kernel)
def pv1176463 : PrimeValue := ⟨1176463, pr1176463⟩
private theorem pr1176787 : PrimeCertificate 1176787 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv13,pv47,pv107]) (by decide +kernel)
def pv1176787 : PrimeValue := ⟨1176787, pr1176787⟩
private theorem pr1176793 : PrimeCertificate 1176793 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv49033]) (by decide +kernel)
def pv1176793 : PrimeValue := ⟨1176793, pr1176793⟩
private theorem pr1177087 : PrimeCertificate 1177087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv196181]) (by decide +kernel)
def pv1177087 : PrimeValue := ⟨1177087, pr1177087⟩
private theorem pr1177147 : PrimeCertificate 1177147 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv21799]) (by decide +kernel)
def pv1177147 : PrimeValue := ⟨1177147, pr1177147⟩
private theorem pr1177219 : PrimeCertificate 1177219 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv9343]) (by decide +kernel)
def pv1177219 : PrimeValue := ⟨1177219, pr1177219⟩
private theorem pr1177399 : PrimeCertificate 1177399 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv149,pv439]) (by decide +kernel)
def pv1177399 : PrimeValue := ⟨1177399, pr1177399⟩
private theorem pr1177453 : PrimeCertificate 1177453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv32707]) (by decide +kernel)
def pv1177453 : PrimeValue := ⟨1177453, pr1177453⟩
private theorem pr1177513 : PrimeCertificate 1177513 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv43,pv163]) (by decide +kernel)
def pv1177513 : PrimeValue := ⟨1177513, pr1177513⟩
private theorem pr1177717 : PrimeCertificate 1177717 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv98143]) (by decide +kernel)
def pv1177717 : PrimeValue := ⟨1177717, pr1177717⟩
private theorem pr1178059 : PrimeCertificate 1178059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv4007]) (by decide +kernel)
def pv1178059 : PrimeValue := ⟨1178059, pr1178059⟩
private theorem pr1178113 : PrimeCertificate 1178113 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv59]) (by decide +kernel)
def pv1178113 : PrimeValue := ⟨1178113, pr1178113⟩
private theorem pr1178197 : PrimeCertificate 1178197 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv47,pv2089]) (by decide +kernel)
def pv1178197 : PrimeValue := ⟨1178197, pr1178197⟩
private theorem pr1178239 : PrimeCertificate 1178239 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv359,pv547]) (by decide +kernel)
def pv1178239 : PrimeValue := ⟨1178239, pr1178239⟩
private theorem pr1178263 : PrimeCertificate 1178263 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv67,pv977]) (by decide +kernel)
def pv1178263 : PrimeValue := ⟨1178263, pr1178263⟩
private theorem pr1178347 : PrimeCertificate 1178347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv15107]) (by decide +kernel)
def pv1178347 : PrimeValue := ⟨1178347, pr1178347⟩
private theorem pr1178659 : PrimeCertificate 1178659 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv23,pv73]) (by decide +kernel)
def pv1178659 : PrimeValue := ⟨1178659, pr1178659⟩
private theorem pr1178689 : PrimeCertificate 1178689 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv877]) (by decide +kernel)
def pv1178689 : PrimeValue := ⟨1178689, pr1178689⟩
private theorem pr1178743 : PrimeCertificate 1178743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv71,pv2767]) (by decide +kernel)
def pv1178743 : PrimeValue := ⟨1178743, pr1178743⟩
private theorem pr1178887 : PrimeCertificate 1178887 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv61,pv3221]) (by decide +kernel)
def pv1178887 : PrimeValue := ⟨1178887, pr1178887⟩
private theorem pr1179289 : PrimeCertificate 1179289 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv11,pv1489]) (by decide +kernel)
def pv1179289 : PrimeValue := ⟨1179289, pr1179289⟩
private theorem pr1179403 : PrimeCertificate 1179403 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv28081]) (by decide +kernel)
def pv1179403 : PrimeValue := ⟨1179403, pr1179403⟩
private theorem pr1179499 : PrimeCertificate 1179499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv196583]) (by decide +kernel)
def pv1179499 : PrimeValue := ⟨1179499, pr1179499⟩
private theorem pr1179973 : PrimeCertificate 1179973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv73,pv449]) (by decide +kernel)
def pv1179973 : PrimeValue := ⟨1179973, pr1179973⟩
private theorem pr1179979 : PrimeCertificate 1179979 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv196663]) (by decide +kernel)
def pv1179979 : PrimeValue := ⟨1179979, pr1179979⟩
private theorem pr1180057 : PrimeCertificate 1180057 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv49169]) (by decide +kernel)
def pv1180057 : PrimeValue := ⟨1180057, pr1180057⟩
private theorem pr1180159 : PrimeCertificate 1180159 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv28099]) (by decide +kernel)
def pv1180159 : PrimeValue := ⟨1180159, pr1180159⟩
private theorem pr1180369 : PrimeCertificate 1180369 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv1171]) (by decide +kernel)
def pv1180369 : PrimeValue := ⟨1180369, pr1180369⟩
private theorem pr1180519 : PrimeCertificate 1180519 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv151,pv1303]) (by decide +kernel)
def pv1180519 : PrimeValue := ⟨1180519, pr1180519⟩
private theorem pr1180549 : PrimeCertificate 1180549 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv643]) (by decide +kernel)
def pv1180549 : PrimeValue := ⟨1180549, pr1180549⟩
private theorem pr1180987 : PrimeCertificate 1180987 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv196831]) (by decide +kernel)
def pv1180987 : PrimeValue := ⟨1180987, pr1180987⟩
private theorem pr1181203 : PrimeCertificate 1181203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv1627]) (by decide +kernel)
def pv1181203 : PrimeValue := ⟨1181203, pr1181203⟩
private theorem pr1181329 : PrimeCertificate 1181329 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv24611]) (by decide +kernel)
def pv1181329 : PrimeValue := ⟨1181329, pr1181329⟩
private theorem pr1181407 : PrimeCertificate 1181407 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv196901]) (by decide +kernel)
def pv1181407 : PrimeValue := ⟨1181407, pr1181407⟩
private theorem pr1181473 : PrimeCertificate 1181473 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv397]) (by decide +kernel)
def pv1181473 : PrimeValue := ⟨1181473, pr1181473⟩
private theorem pr1181767 : PrimeCertificate 1181767 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv196961]) (by decide +kernel)
def pv1181767 : PrimeValue := ⟨1181767, pr1181767⟩
private theorem pr1181893 : PrimeCertificate 1181893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv98491]) (by decide +kernel)
def pv1181893 : PrimeValue := ⟨1181893, pr1181893⟩
private theorem pr1182043 : PrimeCertificate 1182043 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv97,pv677]) (by decide +kernel)
def pv1182043 : PrimeValue := ⟨1182043, pr1182043⟩
private theorem pr1182283 : PrimeCertificate 1182283 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv67,pv173]) (by decide +kernel)
def pv1182283 : PrimeValue := ⟨1182283, pr1182283⟩
private theorem pr1182679 : PrimeCertificate 1182679 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv29,pv971]) (by decide +kernel)
def pv1182679 : PrimeValue := ⟨1182679, pr1182679⟩
private theorem pr1182703 : PrimeCertificate 1182703 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv197117]) (by decide +kernel)
def pv1182703 : PrimeValue := ⟨1182703, pr1182703⟩
private theorem pr1182763 : PrimeCertificate 1182763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv149]) (by decide +kernel)
def pv1182763 : PrimeValue := ⟨1182763, pr1182763⟩
private theorem pr1182889 : PrimeCertificate 1182889 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv7,pv2347]) (by decide +kernel)
def pv1182889 : PrimeValue := ⟨1182889, pr1182889⟩
private theorem pr1183027 : PrimeCertificate 1183027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv29,pv523]) (by decide +kernel)
def pv1183027 : PrimeValue := ⟨1183027, pr1183027⟩
private theorem pr1183057 : PrimeCertificate 1183057 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv503]) (by decide +kernel)
def pv1183057 : PrimeValue := ⟨1183057, pr1183057⟩
private theorem pr1183279 : PrimeCertificate 1183279 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv53,pv61]) (by decide +kernel)
def pv1183279 : PrimeValue := ⟨1183279, pr1183279⟩
private theorem pr1183447 : PrimeCertificate 1183447 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv43,pv139]) (by decide +kernel)
def pv1183447 : PrimeValue := ⟨1183447, pr1183447⟩
private theorem pr1183687 : PrimeCertificate 1183687 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv28183]) (by decide +kernel)
def pv1183687 : PrimeValue := ⟨1183687, pr1183687⟩
private theorem pr1183723 : PrimeCertificate 1183723 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv6803]) (by decide +kernel)
def pv1183723 : PrimeValue := ⟨1183723, pr1183723⟩
private theorem pr1183759 : PrimeCertificate 1183759 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv197293]) (by decide +kernel)
def pv1183759 : PrimeValue := ⟨1183759, pr1183759⟩
private theorem pr1183813 : PrimeCertificate 1183813 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv17,pv829]) (by decide +kernel)
def pv1183813 : PrimeValue := ⟨1183813, pr1183813⟩
private theorem pr1183837 : PrimeCertificate 1183837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv2099]) (by decide +kernel)
def pv1183837 : PrimeValue := ⟨1183837, pr1183837⟩
private theorem pr1183933 : PrimeCertificate 1183933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv32887]) (by decide +kernel)
def pv1183933 : PrimeValue := ⟨1183933, pr1183933⟩
private theorem pr1184047 : PrimeCertificate 1184047 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv197341]) (by decide +kernel)
def pv1184047 : PrimeValue := ⟨1184047, pr1184047⟩
private theorem pr1184119 : PrimeCertificate 1184119 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv17,pv19,pv47]) (by decide +kernel)
def pv1184119 : PrimeValue := ⟨1184119, pr1184119⟩
private theorem pr1184143 : PrimeCertificate 1184143 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv151,pv1307]) (by decide +kernel)
def pv1184143 : PrimeValue := ⟨1184143, pr1184143⟩
private theorem pr1184539 : PrimeCertificate 1184539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv197423]) (by decide +kernel)
def pv1184539 : PrimeValue := ⟨1184539, pr1184539⟩
private theorem pr1184893 : PrimeCertificate 1184893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv293,pv337]) (by decide +kernel)
def pv1184893 : PrimeValue := ⟨1184893, pr1184893⟩
private theorem pr1184959 : PrimeCertificate 1184959 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv65831]) (by decide +kernel)
def pv1184959 : PrimeValue := ⟨1184959, pr1184959⟩
private theorem pr1185013 : PrimeCertificate 1185013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv32917]) (by decide +kernel)
def pv1185013 : PrimeValue := ⟨1185013, pr1185013⟩
private theorem pr1185103 : PrimeCertificate 1185103 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv65839]) (by decide +kernel)
def pv1185103 : PrimeValue := ⟨1185103, pr1185103⟩
private theorem pr1185127 : PrimeCertificate 1185127 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv197521]) (by decide +kernel)
def pv1185127 : PrimeValue := ⟨1185127, pr1185127⟩
private theorem pr1185307 : PrimeCertificate 1185307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv197551]) (by decide +kernel)
def pv1185307 : PrimeValue := ⟨1185307, pr1185307⟩
private theorem pr1185403 : PrimeCertificate 1185403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv197567]) (by decide +kernel)
def pv1185403 : PrimeValue := ⟨1185403, pr1185403⟩
private theorem pr1185493 : PrimeCertificate 1185493 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv1283]) (by decide +kernel)
def pv1185493 : PrimeValue := ⟨1185493, pr1185493⟩
private theorem pr1185589 : PrimeCertificate 1185589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv32933]) (by decide +kernel)
def pv1185589 : PrimeValue := ⟨1185589, pr1185589⟩
private theorem pr1185787 : PrimeCertificate 1185787 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv3137]) (by decide +kernel)
def pv1185787 : PrimeValue := ⟨1185787, pr1185787⟩
private theorem pr1185997 : PrimeCertificate 1185997 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv2017]) (by decide +kernel)
def pv1185997 : PrimeValue := ⟨1185997, pr1185997⟩
private theorem pr1186117 : PrimeCertificate 1186117 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv97,pv1019]) (by decide +kernel)
def pv1186117 : PrimeValue := ⟨1186117, pr1186117⟩
private theorem pr1186147 : PrimeCertificate 1186147 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv37,pv137]) (by decide +kernel)
def pv1186147 : PrimeValue := ⟨1186147, pr1186147⟩
private theorem pr1186249 : PrimeCertificate 1186249 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv7,pv23,pv307]) (by decide +kernel)
def pv1186249 : PrimeValue := ⟨1186249, pr1186249⟩
private theorem pr1186489 : PrimeCertificate 1186489 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1831]) (by decide +kernel)
def pv1186489 : PrimeValue := ⟨1186489, pr1186489⟩
private theorem pr1186693 : PrimeCertificate 1186693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv7607]) (by decide +kernel)
def pv1186693 : PrimeValue := ⟨1186693, pr1186693⟩
private theorem pr1186807 : PrimeCertificate 1186807 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv223,pv887]) (by decide +kernel)
def pv1186807 : PrimeValue := ⟨1186807, pr1186807⟩
private theorem pr1187239 : PrimeCertificate 1187239 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv13,pv31,pv491]) (by decide +kernel)
def pv1187239 : PrimeValue := ⟨1187239, pr1187239⟩
private theorem pr1187629 : PrimeCertificate 1187629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv23,pv331]) (by decide +kernel)
def pv1187629 : PrimeValue := ⟨1187629, pr1187629⟩
private theorem pr1187707 : PrimeCertificate 1187707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv15227]) (by decide +kernel)
def pv1187707 : PrimeValue := ⟨1187707, pr1187707⟩
private theorem pr1187749 : PrimeCertificate 1187749 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv32993]) (by decide +kernel)
def pv1187749 : PrimeValue := ⟨1187749, pr1187749⟩
private theorem pr1187803 : PrimeCertificate 1187803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv857]) (by decide +kernel)
def pv1187803 : PrimeValue := ⟨1187803, pr1187803⟩
private theorem pr1187833 : PrimeCertificate 1187833 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv43,pv1151]) (by decide +kernel)
def pv1187833 : PrimeValue := ⟨1187833, pr1187833⟩
private theorem pr1188169 : PrimeCertificate 1188169 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv31,pv1597]) (by decide +kernel)
def pv1188169 : PrimeValue := ⟨1188169, pr1188169⟩
private theorem pr1188259 : PrimeCertificate 1188259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv198043]) (by decide +kernel)
def pv1188259 : PrimeValue := ⟨1188259, pr1188259⟩
private theorem pr1188277 : PrimeCertificate 1188277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv99023]) (by decide +kernel)
def pv1188277 : PrimeValue := ⟨1188277, pr1188277⟩
private theorem pr1188637 : PrimeCertificate 1188637 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv99053]) (by decide +kernel)
def pv1188637 : PrimeValue := ⟨1188637, pr1188637⟩
private theorem pr1188667 : PrimeCertificate 1188667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv66037]) (by decide +kernel)
def pv1188667 : PrimeValue := ⟨1188667, pr1188667⟩
private theorem pr1188727 : PrimeCertificate 1188727 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv11,pv31,pv83]) (by decide +kernel)
def pv1188727 : PrimeValue := ⟨1188727, pr1188727⟩
private theorem pr1188769 : PrimeCertificate 1188769 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv29,pv61]) (by decide +kernel)
def pv1188769 : PrimeValue := ⟨1188769, pr1188769⟩
private theorem pr1189003 : PrimeCertificate 1189003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53,pv3739]) (by decide +kernel)
def pv1189003 : PrimeValue := ⟨1189003, pr1189003⟩
private theorem pr1189033 : PrimeCertificate 1189033 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv37,pv103]) (by decide +kernel)
def pv1189033 : PrimeValue := ⟨1189033, pr1189033⟩
private theorem pr1189063 : PrimeCertificate 1189063 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv9437]) (by decide +kernel)
def pv1189063 : PrimeValue := ⟨1189063, pr1189063⟩
private theorem pr1189093 : PrimeCertificate 1189093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv197,pv503]) (by decide +kernel)
def pv1189093 : PrimeValue := ⟨1189093, pr1189093⟩
private theorem pr1189159 : PrimeCertificate 1189159 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv198193]) (by decide +kernel)
def pv1189159 : PrimeValue := ⟨1189159, pr1189159⟩
private theorem pr1189213 : PrimeCertificate 1189213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv113,pv877]) (by decide +kernel)
def pv1189213 : PrimeValue := ⟨1189213, pr1189213⟩
private theorem pr1189219 : PrimeCertificate 1189219 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv89,pv131]) (by decide +kernel)
def pv1189219 : PrimeValue := ⟨1189219, pr1189219⟩
private theorem pr1189327 : PrimeCertificate 1189327 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv198221]) (by decide +kernel)
def pv1189327 : PrimeValue := ⟨1189327, pr1189327⟩
private theorem pr1189387 : PrimeCertificate 1189387 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv6007]) (by decide +kernel)
def pv1189387 : PrimeValue := ⟨1189387, pr1189387⟩
private theorem pr1189567 : PrimeCertificate 1189567 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv1049]) (by decide +kernel)
def pv1189567 : PrimeValue := ⟨1189567, pr1189567⟩
private theorem pr1189843 : PrimeCertificate 1189843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv6397]) (by decide +kernel)
def pv1189843 : PrimeValue := ⟨1189843, pr1189843⟩
private theorem pr1190029 : PrimeCertificate 1190029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv31,pv457]) (by decide +kernel)
def pv1190029 : PrimeValue := ⟨1190029, pr1190029⟩
private theorem pr1190149 : PrimeCertificate 1190149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv59]) (by decide +kernel)
def pv1190149 : PrimeValue := ⟨1190149, pr1190149⟩
private theorem pr1190533 : PrimeCertificate 1190533 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv14173]) (by decide +kernel)
def pv1190533 : PrimeValue := ⟨1190533, pr1190533⟩
private theorem pr1190737 : PrimeCertificate 1190737 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv8269]) (by decide +kernel)
def pv1190737 : PrimeValue := ⟨1190737, pr1190737⟩
private theorem pr1190809 : PrimeCertificate 1190809 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv37,pv149]) (by decide +kernel)
def pv1190809 : PrimeValue := ⟨1190809, pr1190809⟩
private theorem pr1190947 : PrimeCertificate 1190947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv198491]) (by decide +kernel)
def pv1190947 : PrimeValue := ⟨1190947, pr1190947⟩
private theorem pr1190983 : PrimeCertificate 1190983 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv15269]) (by decide +kernel)
def pv1190983 : PrimeValue := ⟨1190983, pr1190983⟩
private theorem pr1191079 : PrimeCertificate 1191079 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv23,pv137]) (by decide +kernel)
def pv1191079 : PrimeValue := ⟨1191079, pr1191079⟩
private theorem pr1191103 : PrimeCertificate 1191103 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv18047]) (by decide +kernel)
def pv1191103 : PrimeValue := ⟨1191103, pr1191103⟩
private theorem pr1191247 : PrimeCertificate 1191247 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv113,pv251]) (by decide +kernel)
def pv1191247 : PrimeValue := ⟨1191247, pr1191247⟩
private theorem pr1191277 : PrimeCertificate 1191277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv33091]) (by decide +kernel)
def pv1191277 : PrimeValue := ⟨1191277, pr1191277⟩
private theorem pr1191283 : PrimeCertificate 1191283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv367,pv541]) (by decide +kernel)
def pv1191283 : PrimeValue := ⟨1191283, pr1191283⟩
private theorem pr1191439 : PrimeCertificate 1191439 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv66191]) (by decide +kernel)
def pv1191439 : PrimeValue := ⟨1191439, pr1191439⟩
private theorem pr1191457 : PrimeCertificate 1191457 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv7,pv197]) (by decide +kernel)
def pv1191457 : PrimeValue := ⟨1191457, pr1191457⟩
private theorem pr1191499 : PrimeCertificate 1191499 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv11,pv2579]) (by decide +kernel)
def pv1191499 : PrimeValue := ⟨1191499, pr1191499⟩
private theorem pr1191529 : PrimeCertificate 1191529 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv19,pv67]) (by decide +kernel)
def pv1191529 : PrimeValue := ⟨1191529, pr1191529⟩
private theorem pr1191577 : PrimeCertificate 1191577 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv131,pv379]) (by decide +kernel)
def pv1191577 : PrimeValue := ⟨1191577, pr1191577⟩
private theorem pr1191679 : PrimeCertificate 1191679 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv198613]) (by decide +kernel)
def pv1191679 : PrimeValue := ⟨1191679, pr1191679⟩
private theorem pr1191793 : PrimeCertificate 1191793 :=
  certifyPrime (q := pv59) (ls := [pv2,pv3,pv7,pv3547]) (by decide +kernel)
def pv1191793 : PrimeValue := ⟨1191793, pr1191793⟩
private theorem pr1192099 : PrimeCertificate 1192099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv10457]) (by decide +kernel)
def pv1192099 : PrimeValue := ⟨1192099, pr1192099⟩
private theorem pr1192339 : PrimeCertificate 1192339 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv9463]) (by decide +kernel)
def pv1192339 : PrimeValue := ⟨1192339, pr1192339⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
