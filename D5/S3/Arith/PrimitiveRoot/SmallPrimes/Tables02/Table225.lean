/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table225
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table225.pv999907
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table008
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table022
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table057
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table058

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr999907 : PrimeCertificate 999907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv9803]) (by decide +kernel)
def pv999907 : PrimeValue := ⟨999907, pr999907⟩
private theorem pr999979 : PrimeCertificate 999979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv29,pv821]) (by decide +kernel)
def pv999979 : PrimeValue := ⟨999979, pr999979⟩
private theorem pr1000033 : PrimeCertificate 1000033 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv947]) (by decide +kernel)
def pv1000033 : PrimeValue := ⟨1000033, pr1000033⟩
private theorem pr1000213 : PrimeCertificate 1000213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv4903]) (by decide +kernel)
def pv1000213 : PrimeValue := ⟨1000213, pr1000213⟩
private theorem pr1000303 : PrimeCertificate 1000303 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv293,pv569]) (by decide +kernel)
def pv1000303 : PrimeValue := ⟨1000303, pr1000303⟩
private theorem pr1000723 : PrimeCertificate 1000723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv9811]) (by decide +kernel)
def pv1000723 : PrimeValue := ⟨1000723, pr1000723⟩
private theorem pr1000849 : PrimeCertificate 1000849 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv29,pv719]) (by decide +kernel)
def pv1000849 : PrimeValue := ⟨1000849, pr1000849⟩
private theorem pr1000969 : PrimeCertificate 1000969 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv179,pv233]) (by decide +kernel)
def pv1000969 : PrimeValue := ⟨1000969, pr1000969⟩
private theorem pr1001017 : PrimeCertificate 1001017 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13903]) (by decide +kernel)
def pv1001017 : PrimeValue := ⟨1001017, pr1001017⟩
private theorem pr1001197 : PrimeCertificate 1001197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv29,pv137]) (by decide +kernel)
def pv1001197 : PrimeValue := ⟨1001197, pr1001197⟩
private theorem pr1001527 : PrimeCertificate 1001527 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv71,pv2351]) (by decide +kernel)
def pv1001527 : PrimeValue := ⟨1001527, pr1001527⟩
private theorem pr1001563 : PrimeCertificate 1001563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv79,pv2113]) (by decide +kernel)
def pv1001563 : PrimeValue := ⟨1001563, pr1001563⟩
private theorem pr1001587 : PrimeCertificate 1001587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv166931]) (by decide +kernel)
def pv1001587 : PrimeValue := ⟨1001587, pr1001587⟩
private theorem pr1001629 : PrimeCertificate 1001629 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv27823]) (by decide +kernel)
def pv1001629 : PrimeValue := ⟨1001629, pr1001629⟩
private theorem pr1001659 : PrimeCertificate 1001659 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv3407]) (by decide +kernel)
def pv1001659 : PrimeValue := ⟨1001659, pr1001659⟩
private theorem pr1001947 : PrimeCertificate 1001947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv17,pv19,pv47]) (by decide +kernel)
def pv1001947 : PrimeValue := ⟨1001947, pr1001947⟩
private theorem pr1001953 : PrimeCertificate 1001953 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv71]) (by decide +kernel)
def pv1001953 : PrimeValue := ⟨1001953, pr1001953⟩
private theorem pr1001983 : PrimeCertificate 1001983 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31,pv5387]) (by decide +kernel)
def pv1001983 : PrimeValue := ⟨1001983, pr1001983⟩
private theorem pr1002109 : PrimeCertificate 1002109 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv37,pv61]) (by decide +kernel)
def pv1002109 : PrimeValue := ⟨1002109, pr1002109⟩
private theorem pr1002259 : PrimeCertificate 1002259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv55681]) (by decide +kernel)
def pv1002259 : PrimeValue := ⟨1002259, pr1002259⟩
private theorem pr1002343 : PrimeCertificate 1002343 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv15187]) (by decide +kernel)
def pv1002343 : PrimeValue := ⟨1002343, pr1002343⟩
private theorem pr1002913 : PrimeCertificate 1002913 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv31,pv337]) (by decide +kernel)
def pv1002913 : PrimeValue := ⟨1002913, pr1002913⟩
private theorem pr1003003 : PrimeCertificate 1003003 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv11,pv13,pv167]) (by decide +kernel)
def pv1003003 : PrimeValue := ⟨1003003, pr1003003⟩
private theorem pr1003039 : PrimeCertificate 1003039 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv167173]) (by decide +kernel)
def pv1003039 : PrimeValue := ⟨1003039, pr1003039⟩
private theorem pr1003543 : PrimeCertificate 1003543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv8803]) (by decide +kernel)
def pv1003543 : PrimeValue := ⟨1003543, pr1003543⟩
private theorem pr1003753 : PrimeCertificate 1003753 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv1549]) (by decide +kernel)
def pv1003753 : PrimeValue := ⟨1003753, pr1003753⟩
private theorem pr1003909 : PrimeCertificate 1003909 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv269,pv311]) (by decide +kernel)
def pv1003909 : PrimeValue := ⟨1003909, pr1003909⟩
private theorem pr1003957 : PrimeCertificate 1003957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv83663]) (by decide +kernel)
def pv1003957 : PrimeValue := ⟨1003957, pr1003957⟩
private theorem pr1004053 : PrimeCertificate 1004053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11953]) (by decide +kernel)
def pv1004053 : PrimeValue := ⟨1004053, pr1004053⟩
private theorem pr1004089 : PrimeCertificate 1004089 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv17,pv23,pv107]) (by decide +kernel)
def pv1004089 : PrimeValue := ⟨1004089, pr1004089⟩
private theorem pr1004119 : PrimeCertificate 1004119 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv113,pv1481]) (by decide +kernel)
def pv1004119 : PrimeValue := ⟨1004119, pr1004119⟩
private theorem pr1004137 : PrimeCertificate 1004137 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv7,pv43,pv139]) (by decide +kernel)
def pv1004137 : PrimeValue := ⟨1004137, pr1004137⟩
private theorem pr1004293 : PrimeCertificate 1004293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv547]) (by decide +kernel)
def pv1004293 : PrimeValue := ⟨1004293, pr1004293⟩
private theorem pr1004317 : PrimeCertificate 1004317 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv127,pv659]) (by decide +kernel)
def pv1004317 : PrimeValue := ⟨1004317, pr1004317⟩
private theorem pr1004527 : PrimeCertificate 1004527 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv55807]) (by decide +kernel)
def pv1004527 : PrimeValue := ⟨1004527, pr1004527⟩
private theorem pr1004599 : PrimeCertificate 1004599 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv17,pv67]) (by decide +kernel)
def pv1004599 : PrimeValue := ⟨1004599, pr1004599⟩
private theorem pr1004779 : PrimeCertificate 1004779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv809]) (by decide +kernel)
def pv1004779 : PrimeValue := ⟨1004779, pr1004779⟩
private theorem pr1004977 : PrimeCertificate 1004977 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv997]) (by decide +kernel)
def pv1004977 : PrimeValue := ⟨1004977, pr1004977⟩
private theorem pr1005049 : PrimeCertificate 1005049 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv47]) (by decide +kernel)
def pv1005049 : PrimeValue := ⟨1005049, pr1005049⟩
private theorem pr1005073 : PrimeCertificate 1005073 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv20939]) (by decide +kernel)
def pv1005073 : PrimeValue := ⟨1005073, pr1005073⟩
private theorem pr1005187 : PrimeCertificate 1005187 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv263]) (by decide +kernel)
def pv1005187 : PrimeValue := ⟨1005187, pr1005187⟩
private theorem pr1005217 : PrimeCertificate 1005217 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv37,pv283]) (by decide +kernel)
def pv1005217 : PrimeValue := ⟨1005217, pr1005217⟩
private theorem pr1005349 : PrimeCertificate 1005349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv199,pv421]) (by decide +kernel)
def pv1005349 : PrimeValue := ⟨1005349, pr1005349⟩
private theorem pr1005493 : PrimeCertificate 1005493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv83791]) (by decide +kernel)
def pv1005493 : PrimeValue := ⟨1005493, pr1005493⟩
private theorem pr1005619 : PrimeCertificate 1005619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv9859]) (by decide +kernel)
def pv1005619 : PrimeValue := ⟨1005619, pr1005619⟩
private theorem pr1005637 : PrimeCertificate 1005637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv181,pv463]) (by decide +kernel)
def pv1005637 : PrimeValue := ⟨1005637, pr1005637⟩
private theorem pr1005679 : PrimeCertificate 1005679 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv55871]) (by decide +kernel)
def pv1005679 : PrimeValue := ⟨1005679, pr1005679⟩
private theorem pr1005883 : PrimeCertificate 1005883 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23,pv37,pv197]) (by decide +kernel)
def pv1005883 : PrimeValue := ⟨1005883, pr1005883⟩
private theorem pr1005913 : PrimeCertificate 1005913 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv4657]) (by decide +kernel)
def pv1005913 : PrimeValue := ⟨1005913, pr1005913⟩
private theorem pr1005937 : PrimeCertificate 1005937 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv1103]) (by decide +kernel)
def pv1005937 : PrimeValue := ⟨1005937, pr1005937⟩
private theorem pr1006147 : PrimeCertificate 1006147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv55897]) (by decide +kernel)
def pv1006147 : PrimeValue := ⟨1006147, pr1006147⟩
private theorem pr1006513 : PrimeCertificate 1006513 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv1613]) (by decide +kernel)
def pv1006513 : PrimeValue := ⟨1006513, pr1006513⟩
private theorem pr1006609 : PrimeCertificate 1006609 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv67,pv313]) (by decide +kernel)
def pv1006609 : PrimeValue := ⟨1006609, pr1006609⟩
private theorem pr1006933 : PrimeCertificate 1006933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv83911]) (by decide +kernel)
def pv1006933 : PrimeValue := ⟨1006933, pr1006933⟩
private theorem pr1007023 : PrimeCertificate 1007023 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv47,pv3571]) (by decide +kernel)
def pv1007023 : PrimeValue := ⟨1007023, pr1007023⟩
private theorem pr1007173 : PrimeCertificate 1007173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv101,pv277]) (by decide +kernel)
def pv1007173 : PrimeValue := ⟨1007173, pr1007173⟩
private theorem pr1007353 : PrimeCertificate 1007353 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv823]) (by decide +kernel)
def pv1007353 : PrimeValue := ⟨1007353, pr1007353⟩
private theorem pr1007359 : PrimeCertificate 1007359 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv15263]) (by decide +kernel)
def pv1007359 : PrimeValue := ⟨1007359, pr1007359⟩
private theorem pr1007719 : PrimeCertificate 1007719 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv167953]) (by decide +kernel)
def pv1007719 : PrimeValue := ⟨1007719, pr1007719⟩
private theorem pr1007959 : PrimeCertificate 1007959 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv103,pv233]) (by decide +kernel)
def pv1007959 : PrimeValue := ⟨1007959, pr1007959⟩
private theorem pr1008043 : PrimeCertificate 1008043 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv24001]) (by decide +kernel)
def pv1008043 : PrimeValue := ⟨1008043, pr1008043⟩
private theorem pr1008193 : PrimeCertificate 1008193 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv59,pv89]) (by decide +kernel)
def pv1008193 : PrimeValue := ⟨1008193, pr1008193⟩
private theorem pr1008247 : PrimeCertificate 1008247 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv197,pv853]) (by decide +kernel)
def pv1008247 : PrimeValue := ⟨1008247, pr1008247⟩
private theorem pr1008547 : PrimeCertificate 1008547 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv37,pv59]) (by decide +kernel)
def pv1008547 : PrimeValue := ⟨1008547, pr1008547⟩
private theorem pr1008913 : PrimeCertificate 1008913 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv21019]) (by decide +kernel)
def pv1008913 : PrimeValue := ⟨1008913, pr1008913⟩
private theorem pr1009189 : PrimeCertificate 1009189 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv17,pv97]) (by decide +kernel)
def pv1009189 : PrimeValue := ⟨1009189, pr1009189⟩
private theorem pr1009483 : PrimeCertificate 1009483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv168247]) (by decide +kernel)
def pv1009483 : PrimeValue := ⟨1009483, pr1009483⟩
private theorem pr1009669 : PrimeCertificate 1009669 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv7649]) (by decide +kernel)
def pv1009669 : PrimeValue := ⟨1009669, pr1009669⟩
private theorem pr1009747 : PrimeCertificate 1009747 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv271]) (by decide +kernel)
def pv1009747 : PrimeValue := ⟨1009747, pr1009747⟩
private theorem pr1009927 : PrimeCertificate 1009927 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv19,pv2953]) (by decide +kernel)
def pv1009927 : PrimeValue := ⟨1009927, pr1009927⟩
private theorem pr1010143 : PrimeCertificate 1010143 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv8017]) (by decide +kernel)
def pv1010143 : PrimeValue := ⟨1010143, pr1010143⟩
private theorem pr1010167 : PrimeCertificate 1010167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv5431]) (by decide +kernel)
def pv1010167 : PrimeValue := ⟨1010167, pr1010167⟩
private theorem pr1010179 : PrimeCertificate 1010179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv1439]) (by decide +kernel)
def pv1010179 : PrimeValue := ⟨1010179, pr1010179⟩
private theorem pr1010353 : PrimeCertificate 1010353 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv31,pv97]) (by decide +kernel)
def pv1010353 : PrimeValue := ⟨1010353, pr1010353⟩
private theorem pr1010509 : PrimeCertificate 1010509 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv107,pv787]) (by decide +kernel)
def pv1010509 : PrimeValue := ⟨1010509, pr1010509⟩
private theorem pr1010797 : PrimeCertificate 1010797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv131,pv643]) (by decide +kernel)
def pv1010797 : PrimeValue := ⟨1010797, pr1010797⟩
private theorem pr1010899 : PrimeCertificate 1010899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv71,pv113]) (by decide +kernel)
def pv1010899 : PrimeValue := ⟨1010899, pr1010899⟩
private theorem pr1010929 : PrimeCertificate 1010929 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv21061]) (by decide +kernel)
def pv1010929 : PrimeValue := ⟨1010929, pr1010929⟩
private theorem pr1011067 : PrimeCertificate 1011067 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv19,pv181]) (by decide +kernel)
def pv1011067 : PrimeValue := ⟨1011067, pr1011067⟩
private theorem pr1011217 : PrimeCertificate 1011217 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv21067]) (by decide +kernel)
def pv1011217 : PrimeValue := ⟨1011217, pr1011217⟩
private theorem pr1011229 : PrimeCertificate 1011229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv4957]) (by decide +kernel)
def pv1011229 : PrimeValue := ⟨1011229, pr1011229⟩
private theorem pr1011763 : PrimeCertificate 1011763 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv56209]) (by decide +kernel)
def pv1011763 : PrimeValue := ⟨1011763, pr1011763⟩
private theorem pr1012147 : PrimeCertificate 1012147 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv17,pv9923]) (by decide +kernel)
def pv1012147 : PrimeValue := ⟨1012147, pr1012147⟩
private theorem pr1012159 : PrimeCertificate 1012159 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv29,pv277]) (by decide +kernel)
def pv1012159 : PrimeValue := ⟨1012159, pr1012159⟩
private theorem pr1012213 : PrimeCertificate 1012213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv907]) (by decide +kernel)
def pv1012213 : PrimeValue := ⟨1012213, pr1012213⟩
private theorem pr1012267 : PrimeCertificate 1012267 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv56237]) (by decide +kernel)
def pv1012267 : PrimeValue := ⟨1012267, pr1012267⟩
private theorem pr1012447 : PrimeCertificate 1012447 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv18749]) (by decide +kernel)
def pv1012447 : PrimeValue := ⟨1012447, pr1012447⟩
private theorem pr1012519 : PrimeCertificate 1012519 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv4327]) (by decide +kernel)
def pv1012519 : PrimeValue := ⟨1012519, pr1012519⟩
private theorem pr1012549 : PrimeCertificate 1012549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv4441]) (by decide +kernel)
def pv1012549 : PrimeValue := ⟨1012549, pr1012549⟩
private theorem pr1012717 : PrimeCertificate 1012717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv9377]) (by decide +kernel)
def pv1012717 : PrimeValue := ⟨1012717, pr1012717⟩
private theorem pr1012903 : PrimeCertificate 1012903 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv103,pv149]) (by decide +kernel)
def pv1012903 : PrimeValue := ⟨1012903, pr1012903⟩
private theorem pr1013203 : PrimeCertificate 1013203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv647]) (by decide +kernel)
def pv1013203 : PrimeValue := ⟨1013203, pr1013203⟩
private theorem pr1013239 : PrimeCertificate 1013239 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv181,pv311]) (by decide +kernel)
def pv1013239 : PrimeValue := ⟨1013239, pr1013239⟩
private theorem pr1013329 : PrimeCertificate 1013329 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv31,pv227]) (by decide +kernel)
def pv1013329 : PrimeValue := ⟨1013329, pr1013329⟩
private theorem pr1013839 : PrimeCertificate 1013839 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv101,pv239]) (by decide +kernel)
def pv1013839 : PrimeValue := ⟨1013839, pr1013839⟩
private theorem pr1013893 : PrimeCertificate 1013893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv7681]) (by decide +kernel)
def pv1013893 : PrimeValue := ⟨1013893, pr1013893⟩
private theorem pr1014127 : PrimeCertificate 1014127 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv173,pv977]) (by decide +kernel)
def pv1014127 : PrimeValue := ⟨1014127, pr1014127⟩
private theorem pr1014337 : PrimeCertificate 1014337 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv587]) (by decide +kernel)
def pv1014337 : PrimeValue := ⟨1014337, pr1014337⟩
private theorem pr1014397 : PrimeCertificate 1014397 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv84533]) (by decide +kernel)
def pv1014397 : PrimeValue := ⟨1014397, pr1014397⟩
private theorem pr1014457 : PrimeCertificate 1014457 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv43,pv983]) (by decide +kernel)
def pv1014457 : PrimeValue := ⟨1014457, pr1014457⟩
private theorem pr1014787 : PrimeCertificate 1014787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv56377]) (by decide +kernel)
def pv1014787 : PrimeValue := ⟨1014787, pr1014787⟩
private theorem pr1014877 : PrimeCertificate 1014877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv9397]) (by decide +kernel)
def pv1014877 : PrimeValue := ⟨1014877, pr1014877⟩
private theorem pr1015009 : PrimeCertificate 1015009 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv97,pv109]) (by decide +kernel)
def pv1015009 : PrimeValue := ⟨1015009, pr1015009⟩
private theorem pr1015309 : PrimeCertificate 1015309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv79]) (by decide +kernel)
def pv1015309 : PrimeValue := ⟨1015309, pr1015309⟩
private theorem pr1015549 : PrimeCertificate 1015549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv84629]) (by decide +kernel)
def pv1015549 : PrimeValue := ⟨1015549, pr1015549⟩
private theorem pr1015603 : PrimeCertificate 1015603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv24181]) (by decide +kernel)
def pv1015603 : PrimeValue := ⟨1015603, pr1015603⟩
private theorem pr1015723 : PrimeCertificate 1015723 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv73,pv773]) (by decide +kernel)
def pv1015723 : PrimeValue := ⟨1015723, pr1015723⟩
private theorem pr1015753 : PrimeCertificate 1015753 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv42323]) (by decide +kernel)
def pv1015753 : PrimeValue := ⟨1015753, pr1015753⟩
private theorem pr1015843 : PrimeCertificate 1015843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv169307]) (by decide +kernel)
def pv1015843 : PrimeValue := ⟨1015843, pr1015843⟩
private theorem pr1015897 : PrimeCertificate 1015897 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv7,pv6047]) (by decide +kernel)
def pv1015897 : PrimeValue := ⟨1015897, pr1015897⟩
private theorem pr1016053 : PrimeCertificate 1016053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv227,pv373]) (by decide +kernel)
def pv1016053 : PrimeValue := ⟨1016053, pr1016053⟩
private theorem pr1016137 : PrimeCertificate 1016137 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv1283]) (by decide +kernel)
def pv1016137 : PrimeValue := ⟨1016137, pr1016137⟩
private theorem pr1016173 : PrimeCertificate 1016173 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv97]) (by decide +kernel)
def pv1016173 : PrimeValue := ⟨1016173, pr1016173⟩
private theorem pr1016227 : PrimeCertificate 1016227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv41]) (by decide +kernel)
def pv1016227 : PrimeValue := ⟨1016227, pr1016227⟩
private theorem pr1016497 : PrimeCertificate 1016497 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv181]) (by decide +kernel)
def pv1016497 : PrimeValue := ⟨1016497, pr1016497⟩
private theorem pr1016737 : PrimeCertificate 1016737 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv17,pv89]) (by decide +kernel)
def pv1016737 : PrimeValue := ⟨1016737, pr1016737⟩
private theorem pr1016929 : PrimeCertificate 1016929 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv11,pv107]) (by decide +kernel)
def pv1016929 : PrimeValue := ⟨1016929, pr1016929⟩
private theorem pr1016959 : PrimeCertificate 1016959 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv169493]) (by decide +kernel)
def pv1016959 : PrimeValue := ⟨1016959, pr1016959⟩
private theorem pr1017439 : PrimeCertificate 1017439 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv151,pv1123]) (by decide +kernel)
def pv1017439 : PrimeValue := ⟨1017439, pr1017439⟩
private theorem pr1017703 : PrimeCertificate 1017703 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv41,pv197]) (by decide +kernel)
def pv1017703 : PrimeValue := ⟨1017703, pr1017703⟩
private theorem pr1018177 : PrimeCertificate 1018177 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5303]) (by decide +kernel)
def pv1018177 : PrimeValue := ⟨1018177, pr1018177⟩
private theorem pr1018489 : PrimeCertificate 1018489 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv42437]) (by decide +kernel)
def pv1018489 : PrimeValue := ⟨1018489, pr1018489⟩
private theorem pr1018513 : PrimeCertificate 1018513 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv643]) (by decide +kernel)
def pv1018513 : PrimeValue := ⟨1018513, pr1018513⟩
private theorem pr1018543 : PrimeCertificate 1018543 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv24251]) (by decide +kernel)
def pv1018543 : PrimeValue := ⟨1018543, pr1018543⟩
private theorem pr1018669 : PrimeCertificate 1018669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv67,pv181]) (by decide +kernel)
def pv1018669 : PrimeValue := ⟨1018669, pr1018669⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
