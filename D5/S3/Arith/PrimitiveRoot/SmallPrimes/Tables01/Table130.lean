/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table130
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table130.pv790043
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table018
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table030
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table031
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table047
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table048
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table098
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table099

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr790043 : PrimeCertificate 790043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv35911]) (by decide +kernel)
def pv790043 : PrimeValue := ⟨790043, pr790043⟩
private theorem pr790099 : PrimeCertificate 790099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv3559]) (by decide +kernel)
def pv790099 : PrimeValue := ⟨790099, pr790099⟩
private theorem pr790169 : PrimeCertificate 790169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43,pv2297]) (by decide +kernel)
def pv790169 : PrimeValue := ⟨790169, pr790169⟩
private theorem pr790189 : PrimeCertificate 790189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv23,pv409]) (by decide +kernel)
def pv790189 : PrimeValue := ⟨790189, pr790189⟩
private theorem pr790219 : PrimeCertificate 790219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv13,pv307]) (by decide +kernel)
def pv790219 : PrimeValue := ⟨790219, pr790219⟩
private theorem pr790241 : PrimeCertificate 790241 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv449]) (by decide +kernel)
def pv790241 : PrimeValue := ⟨790241, pr790241⟩
private theorem pr790327 : PrimeCertificate 790327 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv83]) (by decide +kernel)
def pv790327 : PrimeValue := ⟨790327, pr790327⟩
private theorem pr790379 : PrimeCertificate 790379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv395189]) (by decide +kernel)
def pv790379 : PrimeValue := ⟨790379, pr790379⟩
private theorem pr790649 : PrimeCertificate 790649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv4297]) (by decide +kernel)
def pv790649 : PrimeValue := ⟨790649, pr790649⟩
private theorem pr790693 : PrimeCertificate 790693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv9413]) (by decide +kernel)
def pv790693 : PrimeValue := ⟨790693, pr790693⟩
private theorem pr790739 : PrimeCertificate 790739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv17,pv1789]) (by decide +kernel)
def pv790739 : PrimeValue := ⟨790739, pr790739⟩
private theorem pr790747 : PrimeCertificate 790747 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv11981]) (by decide +kernel)
def pv790747 : PrimeValue := ⟨790747, pr790747⟩
private theorem pr790843 : PrimeCertificate 790843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv10139]) (by decide +kernel)
def pv790843 : PrimeValue := ⟨790843, pr790843⟩
private theorem pr790871 : PrimeCertificate 790871 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv79087]) (by decide +kernel)
def pv790871 : PrimeValue := ⟨790871, pr790871⟩
private theorem pr791009 : PrimeCertificate 791009 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv1301]) (by decide +kernel)
def pv791009 : PrimeValue := ⟨791009, pr791009⟩
private theorem pr791137 : PrimeCertificate 791137 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv41,pv67]) (by decide +kernel)
def pv791137 : PrimeValue := ⟨791137, pr791137⟩
private theorem pr791159 : PrimeCertificate 791159 :=
  certifyPrime (q := pv13) (ls := [pv2,pv107,pv3697]) (by decide +kernel)
def pv791159 : PrimeValue := ⟨791159, pr791159⟩
private theorem pr791291 : PrimeCertificate 791291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv53,pv1493]) (by decide +kernel)
def pv791291 : PrimeValue := ⟨791291, pr791291⟩
private theorem pr791317 : PrimeCertificate 791317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv431]) (by decide +kernel)
def pv791317 : PrimeValue := ⟨791317, pr791317⟩
private theorem pr791347 : PrimeCertificate 791347 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv131891]) (by decide +kernel)
def pv791347 : PrimeValue := ⟨791347, pr791347⟩
private theorem pr791519 : PrimeCertificate 791519 :=
  certifyPrime (q := pv19) (ls := [pv2,pv7,pv13,pv4349]) (by decide +kernel)
def pv791519 : PrimeValue := ⟨791519, pr791519⟩
private theorem pr791563 : PrimeCertificate 791563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv131927]) (by decide +kernel)
def pv791563 : PrimeValue := ⟨791563, pr791563⟩
private theorem pr791569 : PrimeCertificate 791569 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv23,pv239]) (by decide +kernel)
def pv791569 : PrimeValue := ⟨791569, pr791569⟩
private theorem pr791629 : PrimeCertificate 791629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv1609]) (by decide +kernel)
def pv791629 : PrimeValue := ⟨791629, pr791629⟩
private theorem pr791899 : PrimeCertificate 791899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv59,pv2237]) (by decide +kernel)
def pv791899 : PrimeValue := ⟨791899, pr791899⟩
private theorem pr791933 : PrimeCertificate 791933 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv6827]) (by decide +kernel)
def pv791933 : PrimeValue := ⟨791933, pr791933⟩
private theorem pr792023 : PrimeCertificate 792023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11,pv37,pv139]) (by decide +kernel)
def pv792023 : PrimeValue := ⟨792023, pr792023⟩
private theorem pr792041 : PrimeCertificate 792041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv19801]) (by decide +kernel)
def pv792041 : PrimeValue := ⟨792041, pr792041⟩
private theorem pr792101 : PrimeCertificate 792101 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv89]) (by decide +kernel)
def pv792101 : PrimeValue := ⟨792101, pr792101⟩
private theorem pr792163 : PrimeCertificate 792163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv6287]) (by decide +kernel)
def pv792163 : PrimeValue := ⟨792163, pr792163⟩
private theorem pr792247 : PrimeCertificate 792247 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv1451]) (by decide +kernel)
def pv792247 : PrimeValue := ⟨792247, pr792247⟩
private theorem pr792277 : PrimeCertificate 792277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv103,pv641]) (by decide +kernel)
def pv792277 : PrimeValue := ⟨792277, pr792277⟩
private theorem pr792371 : PrimeCertificate 792371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv59,pv79]) (by decide +kernel)
def pv792371 : PrimeValue := ⟨792371, pr792371⟩
private theorem pr792383 : PrimeCertificate 792383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv149,pv2659]) (by decide +kernel)
def pv792383 : PrimeValue := ⟨792383, pr792383⟩
private theorem pr792413 : PrimeCertificate 792413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv397,pv499]) (by decide +kernel)
def pv792413 : PrimeValue := ⟨792413, pr792413⟩
private theorem pr792479 : PrimeCertificate 792479 :=
  certifyPrime (q := pv7) (ls := [pv2,pv396239]) (by decide +kernel)
def pv792479 : PrimeValue := ⟨792479, pr792479⟩
private theorem pr792487 : PrimeCertificate 792487 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv44027]) (by decide +kernel)
def pv792487 : PrimeValue := ⟨792487, pr792487⟩
private theorem pr792553 : PrimeCertificate 792553 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv33023]) (by decide +kernel)
def pv792553 : PrimeValue := ⟨792553, pr792553⟩
private theorem pr792563 : PrimeCertificate 792563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv7477]) (by decide +kernel)
def pv792563 : PrimeValue := ⟨792563, pr792563⟩
private theorem pr792667 : PrimeCertificate 792667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv233]) (by decide +kernel)
def pv792667 : PrimeValue := ⟨792667, pr792667⟩
private theorem pr792713 : PrimeCertificate 792713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv99089]) (by decide +kernel)
def pv792713 : PrimeValue := ⟨792713, pr792713⟩
private theorem pr792881 : PrimeCertificate 792881 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv17,pv53]) (by decide +kernel)
def pv792881 : PrimeValue := ⟨792881, pr792881⟩
private theorem pr792973 : PrimeCertificate 792973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv22027]) (by decide +kernel)
def pv792973 : PrimeValue := ⟨792973, pr792973⟩
private theorem pr792983 : PrimeCertificate 792983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv83,pv281]) (by decide +kernel)
def pv792983 : PrimeValue := ⟨792983, pr792983⟩
private theorem pr793069 : PrimeCertificate 793069 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv66089]) (by decide +kernel)
def pv793069 : PrimeValue := ⟨793069, pr793069⟩
private theorem pr793297 : PrimeCertificate 793297 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv787]) (by decide +kernel)
def pv793297 : PrimeValue := ⟨793297, pr793297⟩
private theorem pr793327 : PrimeCertificate 793327 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv19,pv6959]) (by decide +kernel)
def pv793327 : PrimeValue := ⟨793327, pr793327⟩
private theorem pr793453 : PrimeCertificate 793453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv6011]) (by decide +kernel)
def pv793453 : PrimeValue := ⟨793453, pr793453⟩
private theorem pr793633 : PrimeCertificate 793633 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv1181]) (by decide +kernel)
def pv793633 : PrimeValue := ⟨793633, pr793633⟩
private theorem pr793789 : PrimeCertificate 793789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv2281]) (by decide +kernel)
def pv793789 : PrimeValue := ⟨793789, pr793789⟩
private theorem pr793841 : PrimeCertificate 793841 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv9923]) (by decide +kernel)
def pv793841 : PrimeValue := ⟨793841, pr793841⟩
private theorem pr793843 : PrimeCertificate 793843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv41,pv461]) (by decide +kernel)
def pv793843 : PrimeValue := ⟨793843, pr793843⟩
private theorem pr793979 : PrimeCertificate 793979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv83,pv4783]) (by decide +kernel)
def pv793979 : PrimeValue := ⟨793979, pr793979⟩
private theorem pr794009 : PrimeCertificate 794009 :=
  certifyPrime (q := pv3) (ls := [pv2,pv99251]) (by decide +kernel)
def pv794009 : PrimeValue := ⟨794009, pr794009⟩
private theorem pr794149 : PrimeCertificate 794149 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv66179]) (by decide +kernel)
def pv794149 : PrimeValue := ⟨794149, pr794149⟩
private theorem pr794179 : PrimeCertificate 794179 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv191]) (by decide +kernel)
def pv794179 : PrimeValue := ⟨794179, pr794179⟩
private theorem pr794203 : PrimeCertificate 794203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv132367]) (by decide +kernel)
def pv794203 : PrimeValue := ⟨794203, pr794203⟩
private theorem pr794383 : PrimeCertificate 794383 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv43,pv3079]) (by decide +kernel)
def pv794383 : PrimeValue := ⟨794383, pr794383⟩
private theorem pr794509 : PrimeCertificate 794509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv13,pv463]) (by decide +kernel)
def pv794509 : PrimeValue := ⟨794509, pr794509⟩
private theorem pr794693 : PrimeCertificate 794693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv198673]) (by decide +kernel)
def pv794693 : PrimeValue := ⟨794693, pr794693⟩
private theorem pr794749 : PrimeCertificate 794749 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv103,pv643]) (by decide +kernel)
def pv794749 : PrimeValue := ⟨794749, pr794749⟩
private theorem pr794779 : PrimeCertificate 794779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv4273]) (by decide +kernel)
def pv794779 : PrimeValue := ⟨794779, pr794779⟩
private theorem pr794831 : PrimeCertificate 794831 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv61,pv1303]) (by decide +kernel)
def pv794831 : PrimeValue := ⟨794831, pr794831⟩
private theorem pr795007 : PrimeCertificate 795007 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv29,pv1523]) (by decide +kernel)
def pv795007 : PrimeValue := ⟨795007, pr795007⟩
private theorem pr795023 : PrimeCertificate 795023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv67,pv349]) (by decide +kernel)
def pv795023 : PrimeValue := ⟨795023, pr795023⟩
private theorem pr795101 : PrimeCertificate 795101 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7951]) (by decide +kernel)
def pv795101 : PrimeValue := ⟨795101, pr795101⟩
private theorem pr795103 : PrimeCertificate 795103 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv1721]) (by decide +kernel)
def pv795103 : PrimeValue := ⟨795103, pr795103⟩
private theorem pr795217 : PrimeCertificate 795217 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv16567]) (by decide +kernel)
def pv795217 : PrimeValue := ⟨795217, pr795217⟩
private theorem pr795233 : PrimeCertificate 795233 :=
  certifyPrime (q := pv3) (ls := [pv2,pv24851]) (by decide +kernel)
def pv795233 : PrimeValue := ⟨795233, pr795233⟩
private theorem pr795307 : PrimeCertificate 795307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv83,pv1597]) (by decide +kernel)
def pv795307 : PrimeValue := ⟨795307, pr795307⟩
private theorem pr795337 : PrimeCertificate 795337 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv31,pv1069]) (by decide +kernel)
def pv795337 : PrimeValue := ⟨795337, pr795337⟩
private theorem pr795427 : PrimeCertificate 795427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv3583]) (by decide +kernel)
def pv795427 : PrimeValue := ⟨795427, pr795427⟩
private theorem pr795493 : PrimeCertificate 795493 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv1163]) (by decide +kernel)
def pv795493 : PrimeValue := ⟨795493, pr795493⟩
private theorem pr795551 : PrimeCertificate 795551 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv2273]) (by decide +kernel)
def pv795551 : PrimeValue := ⟨795551, pr795551⟩
private theorem pr795643 : PrimeCertificate 795643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv132607]) (by decide +kernel)
def pv795643 : PrimeValue := ⟨795643, pr795643⟩
private theorem pr795799 : PrimeCertificate 795799 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv14737]) (by decide +kernel)
def pv795799 : PrimeValue := ⟨795799, pr795799⟩
private theorem pr795941 : PrimeCertificate 795941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv2341]) (by decide +kernel)
def pv795941 : PrimeValue := ⟨795941, pr795941⟩
private theorem pr795997 : PrimeCertificate 795997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv22111]) (by decide +kernel)
def pv795997 : PrimeValue := ⟨795997, pr795997⟩
private theorem pr796091 : PrimeCertificate 796091 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv79609]) (by decide +kernel)
def pv796091 : PrimeValue := ⟨796091, pr796091⟩
private theorem pr796121 : PrimeCertificate 796121 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv1531]) (by decide +kernel)
def pv796121 : PrimeValue := ⟨796121, pr796121⟩
private theorem pr796193 : PrimeCertificate 796193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv139,pv179]) (by decide +kernel)
def pv796193 : PrimeValue := ⟨796193, pr796193⟩
private theorem pr796363 : PrimeCertificate 796363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv67,pv283]) (by decide +kernel)
def pv796363 : PrimeValue := ⟨796363, pr796363⟩
private theorem pr796459 : PrimeCertificate 796459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv10211]) (by decide +kernel)
def pv796459 : PrimeValue := ⟨796459, pr796459⟩
private theorem pr796567 : PrimeCertificate 796567 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv132761]) (by decide +kernel)
def pv796567 : PrimeValue := ⟨796567, pr796567⟩
private theorem pr796583 : PrimeCertificate 796583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv17317]) (by decide +kernel)
def pv796583 : PrimeValue := ⟨796583, pr796583⟩
private theorem pr796619 : PrimeCertificate 796619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv59,pv157]) (by decide +kernel)
def pv796619 : PrimeValue := ⟨796619, pr796619⟩
private theorem pr796687 : PrimeCertificate 796687 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv12071]) (by decide +kernel)
def pv796687 : PrimeValue := ⟨796687, pr796687⟩
private theorem pr796769 : PrimeCertificate 796769 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv3557]) (by decide +kernel)
def pv796769 : PrimeValue := ⟨796769, pr796769⟩
private theorem pr796819 : PrimeCertificate 796819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv12073]) (by decide +kernel)
def pv796819 : PrimeValue := ⟨796819, pr796819⟩
private theorem pr796849 : PrimeCertificate 796849 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv13,pv1277]) (by decide +kernel)
def pv796849 : PrimeValue := ⟨796849, pr796849⟩
private theorem pr796867 : PrimeCertificate 796867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv18973]) (by decide +kernel)
def pv796867 : PrimeValue := ⟨796867, pr796867⟩
private theorem pr796871 : PrimeCertificate 796871 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv79687]) (by decide +kernel)
def pv796871 : PrimeValue := ⟨796871, pr796871⟩
private theorem pr796933 : PrimeCertificate 796933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv157]) (by decide +kernel)
def pv796933 : PrimeValue := ⟨796933, pr796933⟩
private theorem pr797063 : PrimeCertificate 797063 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv17,pv197]) (by decide +kernel)
def pv797063 : PrimeValue := ⟨797063, pr797063⟩
private theorem pr797143 : PrimeCertificate 797143 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv132857]) (by decide +kernel)
def pv797143 : PrimeValue := ⟨797143, pr797143⟩
private theorem pr797201 : PrimeCertificate 797201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1993]) (by decide +kernel)
def pv797201 : PrimeValue := ⟨797201, pr797201⟩
private theorem pr797353 : PrimeCertificate 797353 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv33223]) (by decide +kernel)
def pv797353 : PrimeValue := ⟨797353, pr797353⟩
private theorem pr797633 : PrimeCertificate 797633 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv103]) (by decide +kernel)
def pv797633 : PrimeValue := ⟨797633, pr797633⟩
private theorem pr797647 : PrimeCertificate 797647 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37,pv3593]) (by decide +kernel)
def pv797647 : PrimeValue := ⟨797647, pr797647⟩
private theorem pr797743 : PrimeCertificate 797743 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv17,pv79]) (by decide +kernel)
def pv797743 : PrimeValue := ⟨797743, pr797743⟩
private theorem pr797833 : PrimeCertificate 797833 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv1583]) (by decide +kernel)
def pv797833 : PrimeValue := ⟨797833, pr797833⟩
private theorem pr797869 : PrimeCertificate 797869 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv37,pv599]) (by decide +kernel)
def pv797869 : PrimeValue := ⟨797869, pr797869⟩
private theorem pr798023 : PrimeCertificate 798023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv29,pv13759]) (by decide +kernel)
def pv798023 : PrimeValue := ⟨798023, pr798023⟩
private theorem pr798097 : PrimeCertificate 798097 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv1279]) (by decide +kernel)
def pv798097 : PrimeValue := ⟨798097, pr798097⟩
private theorem pr798173 : PrimeCertificate 798173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv383,pv521]) (by decide +kernel)
def pv798173 : PrimeValue := ⟨798173, pr798173⟩
private theorem pr798191 : PrimeCertificate 798191 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv19,pv4201]) (by decide +kernel)
def pv798191 : PrimeValue := ⟨798191, pr798191⟩
private theorem pr798251 : PrimeCertificate 798251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31,pv103]) (by decide +kernel)
def pv798251 : PrimeValue := ⟨798251, pr798251⟩
private theorem pr798263 : PrimeCertificate 798263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv399131]) (by decide +kernel)
def pv798263 : PrimeValue := ⟨798263, pr798263⟩
private theorem pr798383 : PrimeCertificate 798383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv30707]) (by decide +kernel)
def pv798383 : PrimeValue := ⟨798383, pr798383⟩
private theorem pr798517 : PrimeCertificate 798517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv541]) (by decide +kernel)
def pv798517 : PrimeValue := ⟨798517, pr798517⟩
private theorem pr798533 : PrimeCertificate 798533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv19,pv79]) (by decide +kernel)
def pv798533 : PrimeValue := ⟨798533, pr798533⟩
private theorem pr798569 : PrimeCertificate 798569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv173,pv577]) (by decide +kernel)
def pv798569 : PrimeValue := ⟨798569, pr798569⟩
private theorem pr798911 : PrimeCertificate 798911 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv101,pv113]) (by decide +kernel)
def pv798911 : PrimeValue := ⟨798911, pr798911⟩
private theorem pr799063 : PrimeCertificate 799063 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv12107]) (by decide +kernel)
def pv799063 : PrimeValue := ⟨799063, pr799063⟩
private theorem pr799091 : PrimeCertificate 799091 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv41,pv1949]) (by decide +kernel)
def pv799091 : PrimeValue := ⟨799091, pr799091⟩
private theorem pr799093 : PrimeCertificate 799093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv151]) (by decide +kernel)
def pv799093 : PrimeValue := ⟨799093, pr799093⟩
private theorem pr799219 : PrimeCertificate 799219 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv6343]) (by decide +kernel)
def pv799219 : PrimeValue := ⟨799219, pr799219⟩
private theorem pr799223 : PrimeCertificate 799223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv61,pv6551]) (by decide +kernel)
def pv799223 : PrimeValue := ⟨799223, pr799223⟩
private theorem pr799417 : PrimeCertificate 799417 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3701]) (by decide +kernel)
def pv799417 : PrimeValue := ⟨799417, pr799417⟩
private theorem pr799453 : PrimeCertificate 799453 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv53,pv419]) (by decide +kernel)
def pv799453 : PrimeValue := ⟨799453, pr799453⟩
private theorem pr799481 : PrimeCertificate 799481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv23,pv79]) (by decide +kernel)
def pv799481 : PrimeValue := ⟨799481, pr799481⟩
private theorem pr799523 : PrimeCertificate 799523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv399761]) (by decide +kernel)
def pv799523 : PrimeValue := ⟨799523, pr799523⟩
private theorem pr799723 : PrimeCertificate 799723 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv577]) (by decide +kernel)
def pv799723 : PrimeValue := ⟨799723, pr799723⟩
private theorem pr799753 : PrimeCertificate 799753 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv47,pv709]) (by decide +kernel)
def pv799753 : PrimeValue := ⟨799753, pr799753⟩
private theorem pr799759 : PrimeCertificate 799759 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv157,pv283]) (by decide +kernel)
def pv799759 : PrimeValue := ⟨799759, pr799759⟩
private theorem pr799853 : PrimeCertificate 799853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv359,pv557]) (by decide +kernel)
def pv799853 : PrimeValue := ⟨799853, pr799853⟩
private theorem pr799999 : PrimeCertificate 799999 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv151,pv883]) (by decide +kernel)
def pv799999 : PrimeValue := ⟨799999, pr799999⟩
private theorem pr800029 : PrimeCertificate 800029 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv71,pv313]) (by decide +kernel)
def pv800029 : PrimeValue := ⟨800029, pr800029⟩
private theorem pr800053 : PrimeCertificate 800053 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv19,pv29]) (by decide +kernel)
def pv800053 : PrimeValue := ⟨800053, pr800053⟩
private theorem pr800083 : PrimeCertificate 800083 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv44449]) (by decide +kernel)
def pv800083 : PrimeValue := ⟨800083, pr800083⟩
private theorem pr800089 : PrimeCertificate 800089 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv37,pv53]) (by decide +kernel)
def pv800089 : PrimeValue := ⟨800089, pr800089⟩
private theorem pr800113 : PrimeCertificate 800113 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv79,pv211]) (by decide +kernel)
def pv800113 : PrimeValue := ⟨800113, pr800113⟩
private theorem pr800171 : PrimeCertificate 800171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv23,pv71]) (by decide +kernel)
def pv800171 : PrimeValue := ⟨800171, pr800171⟩
private theorem pr800209 : PrimeCertificate 800209 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5557]) (by decide +kernel)
def pv800209 : PrimeValue := ⟨800209, pr800209⟩
private theorem pr800473 : PrimeCertificate 800473 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv33353]) (by decide +kernel)
def pv800473 : PrimeValue := ⟨800473, pr800473⟩
private theorem pr800483 : PrimeCertificate 800483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv12911]) (by decide +kernel)
def pv800483 : PrimeValue := ⟨800483, pr800483⟩
private theorem pr800557 : PrimeCertificate 800557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv66713]) (by decide +kernel)
def pv800557 : PrimeValue := ⟨800557, pr800557⟩
private theorem pr800573 : PrimeCertificate 800573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv263,pv761]) (by decide +kernel)
def pv800573 : PrimeValue := ⟨800573, pr800573⟩
private theorem pr800587 : PrimeCertificate 800587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv79,pv563]) (by decide +kernel)
def pv800587 : PrimeValue := ⟨800587, pr800587⟩
private theorem pr800677 : PrimeCertificate 800677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv967]) (by decide +kernel)
def pv800677 : PrimeValue := ⟨800677, pr800677⟩
private theorem pr800711 : PrimeCertificate 800711 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv80071]) (by decide +kernel)
def pv800711 : PrimeValue := ⟨800711, pr800711⟩
private theorem pr800729 : PrimeCertificate 800729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv101,pv991]) (by decide +kernel)
def pv800729 : PrimeValue := ⟨800729, pr800729⟩
private theorem pr800773 : PrimeCertificate 800773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv9533]) (by decide +kernel)
def pv800773 : PrimeValue := ⟨800773, pr800773⟩
private theorem pr800977 : PrimeCertificate 800977 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv37,pv41]) (by decide +kernel)
def pv800977 : PrimeValue := ⟨800977, pr800977⟩
private theorem pr801007 : PrimeCertificate 801007 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv7853]) (by decide +kernel)
def pv801007 : PrimeValue := ⟨801007, pr801007⟩
private theorem pr801487 : PrimeCertificate 801487 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv6361]) (by decide +kernel)
def pv801487 : PrimeValue := ⟨801487, pr801487⟩
private theorem pr801539 : PrimeCertificate 801539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv8527]) (by decide +kernel)
def pv801539 : PrimeValue := ⟨801539, pr801539⟩
private theorem pr801569 : PrimeCertificate 801569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv677]) (by decide +kernel)
def pv801569 : PrimeValue := ⟨801569, pr801569⟩
private theorem pr801607 : PrimeCertificate 801607 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv43,pv239]) (by decide +kernel)
def pv801607 : PrimeValue := ⟨801607, pr801607⟩
private theorem pr801701 : PrimeCertificate 801701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv8017]) (by decide +kernel)
def pv801701 : PrimeValue := ⟨801701, pr801701⟩
private theorem pr801709 : PrimeCertificate 801709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv66809]) (by decide +kernel)
def pv801709 : PrimeValue := ⟨801709, pr801709⟩
private theorem pr801733 : PrimeCertificate 801733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv71,pv941]) (by decide +kernel)
def pv801733 : PrimeValue := ⟨801733, pr801733⟩
private theorem pr801859 : PrimeCertificate 801859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv107,pv1249]) (by decide +kernel)
def pv801859 : PrimeValue := ⟨801859, pr801859⟩
private theorem pr801959 : PrimeCertificate 801959 :=
  certifyPrime (q := pv7) (ls := [pv2,pv17,pv103,pv229]) (by decide +kernel)
def pv801959 : PrimeValue := ⟨801959, pr801959⟩
private theorem pr802073 : PrimeCertificate 802073 :=
  certifyPrime (q := pv3) (ls := [pv2,pv107,pv937]) (by decide +kernel)
def pv802073 : PrimeValue := ⟨802073, pr802073⟩
private theorem pr802121 : PrimeCertificate 802121 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv1823]) (by decide +kernel)
def pv802121 : PrimeValue := ⟨802121, pr802121⟩
private theorem pr802279 : PrimeCertificate 802279 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv83,pv179]) (by decide +kernel)
def pv802279 : PrimeValue := ⟨802279, pr802279⟩
private theorem pr802283 : PrimeCertificate 802283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv59,pv523]) (by decide +kernel)
def pv802283 : PrimeValue := ⟨802283, pr802283⟩
private theorem pr802453 : PrimeCertificate 802453 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv41,pv233]) (by decide +kernel)
def pv802453 : PrimeValue := ⟨802453, pr802453⟩
private theorem pr802523 : PrimeCertificate 802523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv19,pv431]) (by decide +kernel)
def pv802523 : PrimeValue := ⟨802523, pr802523⟩
private theorem pr802573 : PrimeCertificate 802573 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv47,pv1423]) (by decide +kernel)
def pv802573 : PrimeValue := ⟨802573, pr802573⟩
private theorem pr802603 : PrimeCertificate 802603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv89,pv167]) (by decide +kernel)
def pv802603 : PrimeValue := ⟨802603, pr802603⟩
private theorem pr802643 : PrimeCertificate 802643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv401321]) (by decide +kernel)
def pv802643 : PrimeValue := ⟨802643, pr802643⟩
private theorem pr802649 : PrimeCertificate 802649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11,pv1303]) (by decide +kernel)
def pv802649 : PrimeValue := ⟨802649, pr802649⟩
private theorem pr802661 : PrimeCertificate 802661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv67,pv599]) (by decide +kernel)
def pv802661 : PrimeValue := ⟨802661, pr802661⟩
private theorem pr802709 : PrimeCertificate 802709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv2749]) (by decide +kernel)
def pv802709 : PrimeValue := ⟨802709, pr802709⟩
private theorem pr802729 : PrimeCertificate 802729 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv11149]) (by decide +kernel)
def pv802729 : PrimeValue := ⟨802729, pr802729⟩
private theorem pr802759 : PrimeCertificate 802759 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv12163]) (by decide +kernel)
def pv802759 : PrimeValue := ⟨802759, pr802759⟩
private theorem pr802793 : PrimeCertificate 802793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv4363]) (by decide +kernel)
def pv802793 : PrimeValue := ⟨802793, pr802793⟩
private theorem pr803053 : PrimeCertificate 803053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv22307]) (by decide +kernel)
def pv803053 : PrimeValue := ⟨803053, pr803053⟩
private theorem pr803189 : PrimeCertificate 803189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv200797]) (by decide +kernel)
def pv803189 : PrimeValue := ⟨803189, pr803189⟩
private theorem pr803273 : PrimeCertificate 803273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv41,pv79]) (by decide +kernel)
def pv803273 : PrimeValue := ⟨803273, pr803273⟩
private theorem pr803287 : PrimeCertificate 803287 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv4057]) (by decide +kernel)
def pv803287 : PrimeValue := ⟨803287, pr803287⟩
private theorem pr803443 : PrimeCertificate 803443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv359,pv373]) (by decide +kernel)
def pv803443 : PrimeValue := ⟨803443, pr803443⟩
private theorem pr803483 : PrimeCertificate 803483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv17467]) (by decide +kernel)
def pv803483 : PrimeValue := ⟨803483, pr803483⟩
private theorem pr803501 : PrimeCertificate 803501 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1607]) (by decide +kernel)
def pv803501 : PrimeValue := ⟨803501, pr803501⟩
private theorem pr803587 : PrimeCertificate 803587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv19,pv53]) (by decide +kernel)
def pv803587 : PrimeValue := ⟨803587, pr803587⟩
private theorem pr803591 : PrimeCertificate 803591 :=
  certifyPrime (q := pv47) (ls := [pv2,pv5,pv17,pv29,pv163]) (by decide +kernel)
def pv803591 : PrimeValue := ⟨803591, pr803591⟩
private theorem pr803623 : PrimeCertificate 803623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv151,pv887]) (by decide +kernel)
def pv803623 : PrimeValue := ⟨803623, pr803623⟩
private theorem pr803749 : PrimeCertificate 803749 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv6089]) (by decide +kernel)
def pv803749 : PrimeValue := ⟨803749, pr803749⟩
private theorem pr803849 : PrimeCertificate 803849 :=
  certifyPrime (q := pv3) (ls := [pv2,pv89,pv1129]) (by decide +kernel)
def pv803849 : PrimeValue := ⟨803849, pr803849⟩
private theorem pr804007 : PrimeCertificate 804007 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv7,pv709]) (by decide +kernel)
def pv804007 : PrimeValue := ⟨804007, pr804007⟩
private theorem pr804113 : PrimeCertificate 804113 :=
  certifyPrime (q := pv5) (ls := [pv2,pv29,pv1733]) (by decide +kernel)
def pv804113 : PrimeValue := ⟨804113, pr804113⟩
private theorem pr804119 : PrimeCertificate 804119 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv19,pv3023]) (by decide +kernel)
def pv804119 : PrimeValue := ⟨804119, pr804119⟩
private theorem pr804127 : PrimeCertificate 804127 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv5827]) (by decide +kernel)
def pv804127 : PrimeValue := ⟨804127, pr804127⟩
private theorem pr804161 : PrimeCertificate 804161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv359]) (by decide +kernel)
def pv804161 : PrimeValue := ⟨804161, pr804161⟩
private theorem pr804179 : PrimeCertificate 804179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv402089]) (by decide +kernel)
def pv804179 : PrimeValue := ⟨804179, pr804179⟩
private theorem pr804239 : PrimeCertificate 804239 :=
  certifyPrime (q := pv7) (ls := [pv2,pv379,pv1061]) (by decide +kernel)
def pv804239 : PrimeValue := ⟨804239, pr804239⟩
private theorem pr804283 : PrimeCertificate 804283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv134047]) (by decide +kernel)
def pv804283 : PrimeValue := ⟨804283, pr804283⟩
private theorem pr804371 : PrimeCertificate 804371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv11491]) (by decide +kernel)
def pv804371 : PrimeValue := ⟨804371, pr804371⟩
private theorem pr804521 : PrimeCertificate 804521 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv20113]) (by decide +kernel)
def pv804521 : PrimeValue := ⟨804521, pr804521⟩
private theorem pr804523 : PrimeCertificate 804523 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv134087]) (by decide +kernel)
def pv804523 : PrimeValue := ⟨804523, pr804523⟩
private theorem pr804581 : PrimeCertificate 804581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv821]) (by decide +kernel)
def pv804581 : PrimeValue := ⟨804581, pr804581⟩
private theorem pr804589 : PrimeCertificate 804589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv67049]) (by decide +kernel)
def pv804589 : PrimeValue := ⟨804589, pr804589⟩
private theorem pr804619 : PrimeCertificate 804619 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv44701]) (by decide +kernel)
def pv804619 : PrimeValue := ⟨804619, pr804619⟩
private theorem pr804709 : PrimeCertificate 804709 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7451]) (by decide +kernel)
def pv804709 : PrimeValue := ⟨804709, pr804709⟩
private theorem pr804761 : PrimeCertificate 804761 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv31,pv59]) (by decide +kernel)
def pv804761 : PrimeValue := ⟨804761, pr804761⟩
private theorem pr804833 : PrimeCertificate 804833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv3593]) (by decide +kernel)
def pv804833 : PrimeValue := ⟨804833, pr804833⟩
private theorem pr804847 : PrimeCertificate 804847 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv19163]) (by decide +kernel)
def pv804847 : PrimeValue := ⟨804847, pr804847⟩
private theorem pr804997 : PrimeCertificate 804997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv59,pv379]) (by decide +kernel)
def pv804997 : PrimeValue := ⟨804997, pr804997⟩
private theorem pr805061 : PrimeCertificate 805061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv40253]) (by decide +kernel)
def pv805061 : PrimeValue := ⟨805061, pr805061⟩
private theorem pr805267 : PrimeCertificate 805267 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv83]) (by decide +kernel)
def pv805267 : PrimeValue := ⟨805267, pr805267⟩
private theorem pr805289 : PrimeCertificate 805289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv9151]) (by decide +kernel)
def pv805289 : PrimeValue := ⟨805289, pr805289⟩
private theorem pr805297 : PrimeCertificate 805297 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv19,pv883]) (by decide +kernel)
def pv805297 : PrimeValue := ⟨805297, pr805297⟩
private theorem pr805309 : PrimeCertificate 805309 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv9587]) (by decide +kernel)
def pv805309 : PrimeValue := ⟨805309, pr805309⟩
private theorem pr805313 : PrimeCertificate 805313 :=
  certifyPrime (q := pv3) (ls := [pv2,pv12583]) (by decide +kernel)
def pv805313 : PrimeValue := ⟨805313, pr805313⟩
private theorem pr805463 : PrimeCertificate 805463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv8219]) (by decide +kernel)
def pv805463 : PrimeValue := ⟨805463, pr805463⟩
private theorem pr805729 : PrimeCertificate 805729 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv7,pv11,pv109]) (by decide +kernel)
def pv805729 : PrimeValue := ⟨805729, pr805729⟩
private theorem pr805843 : PrimeCertificate 805843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv14923]) (by decide +kernel)
def pv805843 : PrimeValue := ⟨805843, pr805843⟩
private theorem pr805853 : PrimeCertificate 805853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv6947]) (by decide +kernel)
def pv805853 : PrimeValue := ⟨805853, pr805853⟩
private theorem pr806009 : PrimeCertificate 806009 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv37,pv389]) (by decide +kernel)
def pv806009 : PrimeValue := ⟨806009, pr806009⟩
private theorem pr806111 : PrimeCertificate 806111 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv80611]) (by decide +kernel)
def pv806111 : PrimeValue := ⟨806111, pr806111⟩
private theorem pr806153 : PrimeCertificate 806153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv100769]) (by decide +kernel)
def pv806153 : PrimeValue := ⟨806153, pr806153⟩
private theorem pr806159 : PrimeCertificate 806159 :=
  certifyPrime (q := pv7) (ls := [pv2,pv403079]) (by decide +kernel)
def pv806159 : PrimeValue := ⟨806159, pr806159⟩
private theorem pr806213 : PrimeCertificate 806213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv73,pv251]) (by decide +kernel)
def pv806213 : PrimeValue := ⟨806213, pr806213⟩
private theorem pr806257 : PrimeCertificate 806257 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv11,pv509]) (by decide +kernel)
def pv806257 : PrimeValue := ⟨806257, pr806257⟩
private theorem pr806363 : PrimeCertificate 806363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv403181]) (by decide +kernel)
def pv806363 : PrimeValue := ⟨806363, pr806363⟩
private theorem pr806381 : PrimeCertificate 806381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv1753]) (by decide +kernel)
def pv806381 : PrimeValue := ⟨806381, pr806381⟩
private theorem pr806549 : PrimeCertificate 806549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv29,pv409]) (by decide +kernel)
def pv806549 : PrimeValue := ⟨806549, pr806549⟩
private theorem pr806639 : PrimeCertificate 806639 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv8231]) (by decide +kernel)
def pv806639 : PrimeValue := ⟨806639, pr806639⟩
private theorem pr806917 : PrimeCertificate 806917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv6113]) (by decide +kernel)
def pv806917 : PrimeValue := ⟨806917, pr806917⟩
private theorem pr806929 : PrimeCertificate 806929 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv16811]) (by decide +kernel)
def pv806929 : PrimeValue := ⟨806929, pr806929⟩
private theorem pr806947 : PrimeCertificate 806947 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv19213]) (by decide +kernel)
def pv806947 : PrimeValue := ⟨806947, pr806947⟩
private theorem pr807011 : PrimeCertificate 807011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv80701]) (by decide +kernel)
def pv807011 : PrimeValue := ⟨807011, pr807011⟩
private theorem pr807221 : PrimeCertificate 807221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv40361]) (by decide +kernel)
def pv807221 : PrimeValue := ⟨807221, pr807221⟩
private theorem pr807337 : PrimeCertificate 807337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11213]) (by decide +kernel)
def pv807337 : PrimeValue := ⟨807337, pr807337⟩
private theorem pr807379 : PrimeCertificate 807379 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv13,pv941]) (by decide +kernel)
def pv807379 : PrimeValue := ⟨807379, pr807379⟩
private theorem pr807473 : PrimeCertificate 807473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv109,pv463]) (by decide +kernel)
def pv807473 : PrimeValue := ⟨807473, pr807473⟩
private theorem pr807493 : PrimeCertificate 807493 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv9613]) (by decide +kernel)
def pv807493 : PrimeValue := ⟨807493, pr807493⟩
private theorem pr807523 : PrimeCertificate 807523 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv134587]) (by decide +kernel)
def pv807523 : PrimeValue := ⟨807523, pr807523⟩
private theorem pr807539 : PrimeCertificate 807539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv79,pv269]) (by decide +kernel)
def pv807539 : PrimeValue := ⟨807539, pr807539⟩
private theorem pr807559 : PrimeCertificate 807559 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv134593]) (by decide +kernel)
def pv807559 : PrimeValue := ⟨807559, pr807559⟩
private theorem pr807749 : PrimeCertificate 807749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv201937]) (by decide +kernel)
def pv807749 : PrimeValue := ⟨807749, pr807749⟩
private theorem pr807757 : PrimeCertificate 807757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv83,pv811]) (by decide +kernel)
def pv807757 : PrimeValue := ⟨807757, pr807757⟩
private theorem pr807817 : PrimeCertificate 807817 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv97,pv347]) (by decide +kernel)
def pv807817 : PrimeValue := ⟨807817, pr807817⟩
private theorem pr807869 : PrimeCertificate 807869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv139,pv1453]) (by decide +kernel)
def pv807869 : PrimeValue := ⟨807869, pr807869⟩
private theorem pr807923 : PrimeCertificate 807923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv83,pv157]) (by decide +kernel)
def pv807923 : PrimeValue := ⟨807923, pr807923⟩
private theorem pr807943 : PrimeCertificate 807943 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv17,pv89]) (by decide +kernel)
def pv807943 : PrimeValue := ⟨807943, pr807943⟩
private theorem pr808019 : PrimeCertificate 808019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv404009]) (by decide +kernel)
def pv808019 : PrimeValue := ⟨808019, pr808019⟩
private theorem pr808039 : PrimeCertificate 808039 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv53]) (by decide +kernel)
def pv808039 : PrimeValue := ⟨808039, pr808039⟩
private theorem pr808147 : PrimeCertificate 808147 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv19,pv139]) (by decide +kernel)
def pv808147 : PrimeValue := ⟨808147, pr808147⟩
private theorem pr808343 : PrimeCertificate 808343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv389,pv1039]) (by decide +kernel)
def pv808343 : PrimeValue := ⟨808343, pr808343⟩
private theorem pr808361 : PrimeCertificate 808361 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv2887]) (by decide +kernel)
def pv808361 : PrimeValue := ⟨808361, pr808361⟩
private theorem pr808363 : PrimeCertificate 808363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv44909]) (by decide +kernel)
def pv808363 : PrimeValue := ⟨808363, pr808363⟩
private theorem pr808481 : PrimeCertificate 808481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv31,pv163]) (by decide +kernel)
def pv808481 : PrimeValue := ⟨808481, pr808481⟩
private theorem pr808523 : PrimeCertificate 808523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13,pv257]) (by decide +kernel)
def pv808523 : PrimeValue := ⟨808523, pr808523⟩
private theorem pr808579 : PrimeCertificate 808579 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv1549]) (by decide +kernel)
def pv808579 : PrimeValue := ⟨808579, pr808579⟩
private theorem pr808693 : PrimeCertificate 808693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv67391]) (by decide +kernel)
def pv808693 : PrimeValue := ⟨808693, pr808693⟩
private theorem pr808699 : PrimeCertificate 808699 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv12253]) (by decide +kernel)
def pv808699 : PrimeValue := ⟨808699, pr808699⟩
private theorem pr808721 : PrimeCertificate 808721 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv919]) (by decide +kernel)
def pv808721 : PrimeValue := ⟨808721, pr808721⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
