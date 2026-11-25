/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table150
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table150.pv1482263
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table023
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table026
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table027
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table039
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table040
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table052
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table053
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table127
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table128

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr1482263 : PrimeCertificate 1482263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv741131]) (by decide +kernel)
def pv1482263 : PrimeValue := ⟨1482263, pr1482263⟩
private theorem pr1482359 : PrimeCertificate 1482359 :=
  certifyPrime (q := pv7) (ls := [pv2,pv31,pv23909]) (by decide +kernel)
def pv1482359 : PrimeValue := ⟨1482359, pr1482359⟩
private theorem pr1482413 : PrimeCertificate 1482413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv370603]) (by decide +kernel)
def pv1482413 : PrimeValue := ⟨1482413, pr1482413⟩
private theorem pr1482599 : PrimeCertificate 1482599 :=
  certifyPrime (q := pv29) (ls := [pv2,pv13,pv127,pv449]) (by decide +kernel)
def pv1482599 : PrimeValue := ⟨1482599, pr1482599⟩
private theorem pr1483049 : PrimeCertificate 1483049 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv71,pv373]) (by decide +kernel)
def pv1483049 : PrimeValue := ⟨1483049, pr1483049⟩
private theorem pr1483253 : PrimeCertificate 1483253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv370813]) (by decide +kernel)
def pv1483253 : PrimeValue := ⟨1483253, pr1483253⟩
private theorem pr1483259 : PrimeCertificate 1483259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv53,pv1999]) (by decide +kernel)
def pv1483259 : PrimeValue := ⟨1483259, pr1483259⟩
private theorem pr1483439 : PrimeCertificate 1483439 :=
  certifyPrime (q := pv29) (ls := [pv2,pv11,pv67429]) (by decide +kernel)
def pv1483439 : PrimeValue := ⟨1483439, pr1483439⟩
private theorem pr1483721 : PrimeCertificate 1483721 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv757]) (by decide +kernel)
def pv1483721 : PrimeValue := ⟨1483721, pr1483721⟩
private theorem pr1483991 : PrimeCertificate 1483991 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv148399]) (by decide +kernel)
def pv1483991 : PrimeValue := ⟨1483991, pr1483991⟩
private theorem pr1484009 : PrimeCertificate 1484009 :=
  certifyPrime (q := pv3) (ls := [pv2,pv61,pv3041]) (by decide +kernel)
def pv1484009 : PrimeValue := ⟨1484009, pr1484009⟩
private theorem pr1484111 : PrimeCertificate 1484111 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv148411]) (by decide +kernel)
def pv1484111 : PrimeValue := ⟨1484111, pr1484111⟩
private theorem pr1484141 : PrimeCertificate 1484141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv10601]) (by decide +kernel)
def pv1484141 : PrimeValue := ⟨1484141, pr1484141⟩
private theorem pr1484183 : PrimeCertificate 1484183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv106013]) (by decide +kernel)
def pv1484183 : PrimeValue := ⟨1484183, pr1484183⟩
private theorem pr1484243 : PrimeCertificate 1484243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv139,pv281]) (by decide +kernel)
def pv1484243 : PrimeValue := ⟨1484243, pr1484243⟩
private theorem pr1484393 : PrimeCertificate 1484393 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv13,pv2039]) (by decide +kernel)
def pv1484393 : PrimeValue := ⟨1484393, pr1484393⟩
private theorem pr1484453 : PrimeCertificate 1484453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv67,pv191]) (by decide +kernel)
def pv1484453 : PrimeValue := ⟨1484453, pr1484453⟩
private theorem pr1484501 : PrimeCertificate 1484501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv2969]) (by decide +kernel)
def pv1484501 : PrimeValue := ⟨1484501, pr1484501⟩
private theorem pr1484531 : PrimeCertificate 1484531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv53,pv2801]) (by decide +kernel)
def pv1484531 : PrimeValue := ⟨1484531, pr1484531⟩
private theorem pr1484573 : PrimeCertificate 1484573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv371143]) (by decide +kernel)
def pv1484573 : PrimeValue := ⟨1484573, pr1484573⟩
private theorem pr1484849 : PrimeCertificate 1484849 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv53,pv103]) (by decide +kernel)
def pv1484849 : PrimeValue := ⟨1484849, pr1484849⟩
private theorem pr1485023 : PrimeCertificate 1485023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11,pv9643]) (by decide +kernel)
def pv1485023 : PrimeValue := ⟨1485023, pr1485023⟩
private theorem pr1485233 : PrimeCertificate 1485233 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv89,pv149]) (by decide +kernel)
def pv1485233 : PrimeValue := ⟨1485233, pr1485233⟩
private theorem pr1485251 : PrimeCertificate 1485251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv457]) (by decide +kernel)
def pv1485251 : PrimeValue := ⟨1485251, pr1485251⟩
private theorem pr1485461 : PrimeCertificate 1485461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv257]) (by decide +kernel)
def pv1485461 : PrimeValue := ⟨1485461, pr1485461⟩
private theorem pr1485479 : PrimeCertificate 1485479 :=
  certifyPrime (q := pv7) (ls := [pv2,pv23,pv43,pv751]) (by decide +kernel)
def pv1485479 : PrimeValue := ⟨1485479, pr1485479⟩
private theorem pr1486091 : PrimeCertificate 1486091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv148609]) (by decide +kernel)
def pv1486091 : PrimeValue := ⟨1486091, pr1486091⟩
private theorem pr1486139 : PrimeCertificate 1486139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv743069]) (by decide +kernel)
def pv1486139 : PrimeValue := ⟨1486139, pr1486139⟩
private theorem pr1486181 : PrimeCertificate 1486181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv3911]) (by decide +kernel)
def pv1486181 : PrimeValue := ⟨1486181, pr1486181⟩
private theorem pr1486223 : PrimeCertificate 1486223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv743111]) (by decide +kernel)
def pv1486223 : PrimeValue := ⟨1486223, pr1486223⟩
private theorem pr1486241 : PrimeCertificate 1486241 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv1327]) (by decide +kernel)
def pv1486241 : PrimeValue := ⟨1486241, pr1486241⟩
private theorem pr1486343 : PrimeCertificate 1486343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv13,pv5197]) (by decide +kernel)
def pv1486343 : PrimeValue := ⟨1486343, pr1486343⟩
private theorem pr1486451 : PrimeCertificate 1486451 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv31,pv137]) (by decide +kernel)
def pv1486451 : PrimeValue := ⟨1486451, pr1486451⟩
private theorem pr1486781 : PrimeCertificate 1486781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv79,pv941]) (by decide +kernel)
def pv1486781 : PrimeValue := ⟨1486781, pr1486781⟩
private theorem pr1487093 : PrimeCertificate 1487093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv19,pv1151]) (by decide +kernel)
def pv1487093 : PrimeValue := ⟨1487093, pr1487093⟩
private theorem pr1487231 : PrimeCertificate 1487231 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv148723]) (by decide +kernel)
def pv1487231 : PrimeValue := ⟨1487231, pr1487231⟩
private theorem pr1487273 : PrimeCertificate 1487273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv59,pv137]) (by decide +kernel)
def pv1487273 : PrimeValue := ⟨1487273, pr1487273⟩
private theorem pr1487303 : PrimeCertificate 1487303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv61,pv73,pv167]) (by decide +kernel)
def pv1487303 : PrimeValue := ⟨1487303, pr1487303⟩
private theorem pr1487399 : PrimeCertificate 1487399 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv17,pv41,pv97]) (by decide +kernel)
def pv1487399 : PrimeValue := ⟨1487399, pr1487399⟩
private theorem pr1487429 : PrimeCertificate 1487429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv371857]) (by decide +kernel)
def pv1487429 : PrimeValue := ⟨1487429, pr1487429⟩
private theorem pr1487441 : PrimeCertificate 1487441 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv18593]) (by decide +kernel)
def pv1487441 : PrimeValue := ⟨1487441, pr1487441⟩
private theorem pr1487753 : PrimeCertificate 1487753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv31,pv857]) (by decide +kernel)
def pv1487753 : PrimeValue := ⟨1487753, pr1487753⟩
private theorem pr1487819 : PrimeCertificate 1487819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv367,pv2027]) (by decide +kernel)
def pv1487819 : PrimeValue := ⟨1487819, pr1487819⟩
private theorem pr1487873 : PrimeCertificate 1487873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1453]) (by decide +kernel)
def pv1487873 : PrimeValue := ⟨1487873, pr1487873⟩
private theorem pr1488131 : PrimeCertificate 1488131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv3037]) (by decide +kernel)
def pv1488131 : PrimeValue := ⟨1488131, pr1488131⟩
private theorem pr1488533 : PrimeCertificate 1488533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv197,pv1889]) (by decide +kernel)
def pv1488533 : PrimeValue := ⟨1488533, pr1488533⟩
private theorem pr1488761 : PrimeCertificate 1488761 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv7,pv13,pv409]) (by decide +kernel)
def pv1488761 : PrimeValue := ⟨1488761, pr1488761⟩
private theorem pr1488869 : PrimeCertificate 1488869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv12007]) (by decide +kernel)
def pv1488869 : PrimeValue := ⟨1488869, pr1488869⟩
private theorem pr1488989 : PrimeCertificate 1488989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv157,pv2371]) (by decide +kernel)
def pv1488989 : PrimeValue := ⟨1488989, pr1488989⟩
private theorem pr1489109 : PrimeCertificate 1489109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv372277]) (by decide +kernel)
def pv1489109 : PrimeValue := ⟨1489109, pr1489109⟩
private theorem pr1489199 : PrimeCertificate 1489199 :=
  certifyPrime (q := pv19) (ls := [pv2,pv744599]) (by decide +kernel)
def pv1489199 : PrimeValue := ⟨1489199, pr1489199⟩
private theorem pr1489409 : PrimeCertificate 1489409 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2909]) (by decide +kernel)
def pv1489409 : PrimeValue := ⟨1489409, pr1489409⟩
private theorem pr1489511 : PrimeCertificate 1489511 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv1231]) (by decide +kernel)
def pv1489511 : PrimeValue := ⟨1489511, pr1489511⟩
private theorem pr1489529 : PrimeCertificate 1489529 :=
  certifyPrime (q := pv3) (ls := [pv2,pv186191]) (by decide +kernel)
def pv1489529 : PrimeValue := ⟨1489529, pr1489529⟩
private theorem pr1489613 : PrimeCertificate 1489613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv41,pv293]) (by decide +kernel)
def pv1489613 : PrimeValue := ⟨1489613, pr1489613⟩
private theorem pr1489781 : PrimeCertificate 1489781 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv74489]) (by decide +kernel)
def pv1489781 : PrimeValue := ⟨1489781, pr1489781⟩
private theorem pr1490081 : PrimeCertificate 1490081 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv67,pv139]) (by decide +kernel)
def pv1490081 : PrimeValue := ⟨1490081, pr1490081⟩
private theorem pr1490213 : PrimeCertificate 1490213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv10069]) (by decide +kernel)
def pv1490213 : PrimeValue := ⟨1490213, pr1490213⟩
private theorem pr1490243 : PrimeCertificate 1490243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv4409]) (by decide +kernel)
def pv1490243 : PrimeValue := ⟨1490243, pr1490243⟩
private theorem pr1490591 : PrimeCertificate 1490591 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv149059]) (by decide +kernel)
def pv1490591 : PrimeValue := ⟨1490591, pr1490591⟩
private theorem pr1490669 : PrimeCertificate 1490669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv372667]) (by decide +kernel)
def pv1490669 : PrimeValue := ⟨1490669, pr1490669⟩
private theorem pr1490999 : PrimeCertificate 1490999 :=
  certifyPrime (q := pv11) (ls := [pv2,pv23,pv32413]) (by decide +kernel)
def pv1490999 : PrimeValue := ⟨1490999, pr1490999⟩
private theorem pr1491449 : PrimeCertificate 1491449 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv26633]) (by decide +kernel)
def pv1491449 : PrimeValue := ⟨1491449, pr1491449⟩
private theorem pr1491683 : PrimeCertificate 1491683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv73,pv601]) (by decide +kernel)
def pv1491683 : PrimeValue := ⟨1491683, pr1491683⟩
private theorem pr1491701 : PrimeCertificate 1491701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv2131]) (by decide +kernel)
def pv1491701 : PrimeValue := ⟨1491701, pr1491701⟩
private theorem pr1491761 : PrimeCertificate 1491761 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv29,pv643]) (by decide +kernel)
def pv1491761 : PrimeValue := ⟨1491761, pr1491761⟩
private theorem pr1491839 : PrimeCertificate 1491839 :=
  certifyPrime (q := pv13) (ls := [pv2,pv239,pv3121]) (by decide +kernel)
def pv1491839 : PrimeValue := ⟨1491839, pr1491839⟩
private theorem pr1492019 : PrimeCertificate 1492019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv67819]) (by decide +kernel)
def pv1492019 : PrimeValue := ⟨1492019, pr1492019⟩
private theorem pr1492103 : PrimeCertificate 1492103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv163,pv199]) (by decide +kernel)
def pv1492103 : PrimeValue := ⟨1492103, pr1492103⟩
private theorem pr1492163 : PrimeCertificate 1492163 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv53,pv2011]) (by decide +kernel)
def pv1492163 : PrimeValue := ⟨1492163, pr1492163⟩
private theorem pr1492181 : PrimeCertificate 1492181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv74609]) (by decide +kernel)
def pv1492181 : PrimeValue := ⟨1492181, pr1492181⟩
private theorem pr1492223 : PrimeCertificate 1492223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv107,pv367]) (by decide +kernel)
def pv1492223 : PrimeValue := ⟨1492223, pr1492223⟩
private theorem pr1492643 : PrimeCertificate 1492643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv523,pv1427]) (by decide +kernel)
def pv1492643 : PrimeValue := ⟨1492643, pr1492643⟩
private theorem pr1493273 : PrimeCertificate 1493273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv71,pv239]) (by decide +kernel)
def pv1493273 : PrimeValue := ⟨1493273, pr1493273⟩
private theorem pr1493279 : PrimeCertificate 1493279 :=
  certifyPrime (q := pv7) (ls := [pv2,pv149,pv5011]) (by decide +kernel)
def pv1493279 : PrimeValue := ⟨1493279, pr1493279⟩
private theorem pr1493291 : PrimeCertificate 1493291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv59,pv2531]) (by decide +kernel)
def pv1493291 : PrimeValue := ⟨1493291, pr1493291⟩
private theorem pr1493483 : PrimeCertificate 1493483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv32467]) (by decide +kernel)
def pv1493483 : PrimeValue := ⟨1493483, pr1493483⟩
private theorem pr1493489 : PrimeCertificate 1493489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv269,pv347]) (by decide +kernel)
def pv1493489 : PrimeValue := ⟨1493489, pr1493489⟩
private theorem pr1493573 : PrimeCertificate 1493573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv373393]) (by decide +kernel)
def pv1493573 : PrimeValue := ⟨1493573, pr1493573⟩
private theorem pr1493729 : PrimeCertificate 1493729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv46679]) (by decide +kernel)
def pv1493729 : PrimeValue := ⟨1493729, pr1493729⟩
private theorem pr1493741 : PrimeCertificate 1493741 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv74687]) (by decide +kernel)
def pv1493741 : PrimeValue := ⟨1493741, pr1493741⟩
private theorem pr1493759 : PrimeCertificate 1493759 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv23,pv4639]) (by decide +kernel)
def pv1493759 : PrimeValue := ⟨1493759, pr1493759⟩
private theorem pr1494071 : PrimeCertificate 1494071 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv53,pv2819]) (by decide +kernel)
def pv1494071 : PrimeValue := ⟨1494071, pr1494071⟩
private theorem pr1494659 : PrimeCertificate 1494659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv67939]) (by decide +kernel)
def pv1494659 : PrimeValue := ⟨1494659, pr1494659⟩
private theorem pr1494743 : PrimeCertificate 1494743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv43963]) (by decide +kernel)
def pv1494743 : PrimeValue := ⟨1494743, pr1494743⟩
private theorem pr1495463 : PrimeCertificate 1495463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv747731]) (by decide +kernel)
def pv1495463 : PrimeValue := ⟨1495463, pr1495463⟩
private theorem pr1495601 : PrimeCertificate 1495601 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv3739]) (by decide +kernel)
def pv1495601 : PrimeValue := ⟨1495601, pr1495601⟩
private theorem pr1495853 : PrimeCertificate 1495853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv373963]) (by decide +kernel)
def pv1495853 : PrimeValue := ⟨1495853, pr1495853⟩
private theorem pr1495859 : PrimeCertificate 1495859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv8219]) (by decide +kernel)
def pv1495859 : PrimeValue := ⟨1495859, pr1495859⟩
private theorem pr1496129 : PrimeCertificate 1496129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv97,pv241]) (by decide +kernel)
def pv1496129 : PrimeValue := ⟨1496129, pr1496129⟩
private theorem pr1496279 : PrimeCertificate 1496279 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv106877]) (by decide +kernel)
def pv1496279 : PrimeValue := ⟨1496279, pr1496279⟩
private theorem pr1496549 : PrimeCertificate 1496549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv374137]) (by decide +kernel)
def pv1496549 : PrimeValue := ⟨1496549, pr1496549⟩
private theorem pr1496669 : PrimeCertificate 1496669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv47,pv419]) (by decide +kernel)
def pv1496669 : PrimeValue := ⟨1496669, pr1496669⟩
private theorem pr1496723 : PrimeCertificate 1496723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv748361]) (by decide +kernel)
def pv1496723 : PrimeValue := ⟨1496723, pr1496723⟩
private theorem pr1496783 : PrimeCertificate 1496783 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv17,pv19,pv331]) (by decide +kernel)
def pv1496783 : PrimeValue := ⟨1496783, pr1496783⟩
private theorem pr1497263 : PrimeCertificate 1497263 :=
  certifyPrime (q := pv11) (ls := [pv2,pv13,pv57587]) (by decide +kernel)
def pv1497263 : PrimeValue := ⟨1497263, pr1497263⟩
private theorem pr1497533 : PrimeCertificate 1497533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71,pv5273]) (by decide +kernel)
def pv1497533 : PrimeValue := ⟨1497533, pr1497533⟩
private theorem pr1497659 : PrimeCertificate 1497659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv748829]) (by decide +kernel)
def pv1497659 : PrimeValue := ⟨1497659, pr1497659⟩
private theorem pr1497731 : PrimeCertificate 1497731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv41,pv281]) (by decide +kernel)
def pv1497731 : PrimeValue := ⟨1497731, pr1497731⟩
private theorem pr1497911 : PrimeCertificate 1497911 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv149791]) (by decide +kernel)
def pv1497911 : PrimeValue := ⟨1497911, pr1497911⟩
private theorem pr1498391 : PrimeCertificate 1498391 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv149839]) (by decide +kernel)
def pv1498391 : PrimeValue := ⟨1498391, pr1498391⟩
private theorem pr1498751 : PrimeCertificate 1498751 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv109]) (by decide +kernel)
def pv1498751 : PrimeValue := ⟨1498751, pr1498751⟩
private theorem pr1498811 : PrimeCertificate 1498811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv71,pv2111]) (by decide +kernel)
def pv1498811 : PrimeValue := ⟨1498811, pr1498811⟩
private theorem pr1499429 : PrimeCertificate 1499429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv53551]) (by decide +kernel)
def pv1499429 : PrimeValue := ⟨1499429, pr1499429⟩
private theorem pr1499549 : PrimeCertificate 1499549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv374887]) (by decide +kernel)
def pv1499549 : PrimeValue := ⟨1499549, pr1499549⟩
private theorem pr1499891 : PrimeCertificate 1499891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv3061]) (by decide +kernel)
def pv1499891 : PrimeValue := ⟨1499891, pr1499891⟩
private theorem pr1500269 : PrimeCertificate 1500269 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11,pv4871]) (by decide +kernel)
def pv1500269 : PrimeValue := ⟨1500269, pr1500269⟩
private theorem pr1500371 : PrimeCertificate 1500371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv59,pv2543]) (by decide +kernel)
def pv1500371 : PrimeValue := ⟨1500371, pr1500371⟩
private theorem pr1500491 : PrimeCertificate 1500491 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv181,pv829]) (by decide +kernel)
def pv1500491 : PrimeValue := ⟨1500491, pr1500491⟩
private theorem pr1500533 : PrimeCertificate 1500533 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv67,pv509]) (by decide +kernel)
def pv1500533 : PrimeValue := ⟨1500533, pr1500533⟩
private theorem pr1500731 : PrimeCertificate 1500731 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv11,pv1949]) (by decide +kernel)
def pv1500731 : PrimeValue := ⟨1500731, pr1500731⟩
private theorem pr1501229 : PrimeCertificate 1501229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv19753]) (by decide +kernel)
def pv1501229 : PrimeValue := ⟨1501229, pr1501229⟩
private theorem pr1501583 : PrimeCertificate 1501583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv750791]) (by decide +kernel)
def pv1501583 : PrimeValue := ⟨1501583, pr1501583⟩
private theorem pr1501613 : PrimeCertificate 1501613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv53629]) (by decide +kernel)
def pv1501613 : PrimeValue := ⟨1501613, pr1501613⟩
private theorem pr1501679 : PrimeCertificate 1501679 :=
  certifyPrime (q := pv7) (ls := [pv2,pv17,pv29,pv1523]) (by decide +kernel)
def pv1501679 : PrimeValue := ⟨1501679, pr1501679⟩
private theorem pr1501859 : PrimeCertificate 1501859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv750929]) (by decide +kernel)
def pv1501859 : PrimeValue := ⟨1501859, pr1501859⟩
private theorem pr1501889 : PrimeCertificate 1501889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv757]) (by decide +kernel)
def pv1501889 : PrimeValue := ⟨1501889, pr1501889⟩
private theorem pr1501943 : PrimeCertificate 1501943 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv61,pv947]) (by decide +kernel)
def pv1501943 : PrimeValue := ⟨1501943, pr1501943⟩
private theorem pr1501949 : PrimeCertificate 1501949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv79,pv97]) (by decide +kernel)
def pv1501949 : PrimeValue := ⟨1501949, pr1501949⟩
private theorem pr1502201 : PrimeCertificate 1502201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv29,pv37]) (by decide +kernel)
def pv1502201 : PrimeValue := ⟨1502201, pr1502201⟩
private theorem pr1502471 : PrimeCertificate 1502471 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv150247]) (by decide +kernel)
def pv1502471 : PrimeValue := ⟨1502471, pr1502471⟩
private theorem pr1502639 : PrimeCertificate 1502639 :=
  certifyPrime (q := pv13) (ls := [pv2,pv751319]) (by decide +kernel)
def pv1502639 : PrimeValue := ⟨1502639, pr1502639⟩
private theorem pr1502993 : PrimeCertificate 1502993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv93937]) (by decide +kernel)
def pv1502993 : PrimeValue := ⟨1502993, pr1502993⟩
private theorem pr1503059 : PrimeCertificate 1503059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv751529]) (by decide +kernel)
def pv1503059 : PrimeValue := ⟨1503059, pr1503059⟩
private theorem pr1503149 : PrimeCertificate 1503149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv375787]) (by decide +kernel)
def pv1503149 : PrimeValue := ⟨1503149, pr1503149⟩
private theorem pr1503311 : PrimeCertificate 1503311 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv17,pv37,pv239]) (by decide +kernel)
def pv1503311 : PrimeValue := ⟨1503311, pr1503311⟩
private theorem pr1503611 : PrimeCertificate 1503611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv53,pv2837]) (by decide +kernel)
def pv1503611 : PrimeValue := ⟨1503611, pr1503611⟩
private theorem pr1503959 : PrimeCertificate 1503959 :=
  certifyPrime (q := pv7) (ls := [pv2,pv179,pv4201]) (by decide +kernel)
def pv1503959 : PrimeValue := ⟨1503959, pr1503959⟩
private theorem pr1504103 : PrimeCertificate 1504103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv227,pv3313]) (by decide +kernel)
def pv1504103 : PrimeValue := ⟨1504103, pr1504103⟩
private theorem pr1504271 : PrimeCertificate 1504271 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv150427]) (by decide +kernel)
def pv1504271 : PrimeValue := ⟨1504271, pr1504271⟩
private theorem pr1504859 : PrimeCertificate 1504859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv97,pv7757]) (by decide +kernel)
def pv1504859 : PrimeValue := ⟨1504859, pr1504859⟩
private theorem pr1504949 : PrimeCertificate 1504949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv376237]) (by decide +kernel)
def pv1504949 : PrimeValue := ⟨1504949, pr1504949⟩
private theorem pr1505033 : PrimeCertificate 1505033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv179,pv1051]) (by decide +kernel)
def pv1505033 : PrimeValue := ⟨1505033, pr1505033⟩
private theorem pr1505099 : PrimeCertificate 1505099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv107507]) (by decide +kernel)
def pv1505099 : PrimeValue := ⟨1505099, pr1505099⟩
private theorem pr1505183 : PrimeCertificate 1505183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv15359]) (by decide +kernel)
def pv1505183 : PrimeValue := ⟨1505183, pr1505183⟩
private theorem pr1505261 : PrimeCertificate 1505261 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv73,pv1031]) (by decide +kernel)
def pv1505261 : PrimeValue := ⟨1505261, pr1505261⟩
private theorem pr1505291 : PrimeCertificate 1505291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv109,pv1381]) (by decide +kernel)
def pv1505291 : PrimeValue := ⟨1505291, pr1505291⟩
private theorem pr1505489 : PrimeCertificate 1505489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv4091]) (by decide +kernel)
def pv1505489 : PrimeValue := ⟨1505489, pr1505489⟩
private theorem pr1505753 : PrimeCertificate 1505753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv5087]) (by decide +kernel)
def pv1505753 : PrimeValue := ⟨1505753, pr1505753⟩
private theorem pr1505813 : PrimeCertificate 1505813 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11,pv4889]) (by decide +kernel)
def pv1505813 : PrimeValue := ⟨1505813, pr1505813⟩
private theorem pr1505831 : PrimeCertificate 1505831 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv150583]) (by decide +kernel)
def pv1505831 : PrimeValue := ⟨1505831, pr1505831⟩
private theorem pr1506269 : PrimeCertificate 1506269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv1303]) (by decide +kernel)
def pv1506269 : PrimeValue := ⟨1506269, pr1506269⟩
private theorem pr1506341 : PrimeCertificate 1506341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv41,pv167]) (by decide +kernel)
def pv1506341 : PrimeValue := ⟨1506341, pr1506341⟩
private theorem pr1506359 : PrimeCertificate 1506359 :=
  certifyPrime (q := pv17) (ls := [pv2,pv7,pv19,pv809]) (by decide +kernel)
def pv1506359 : PrimeValue := ⟨1506359, pr1506359⟩
private theorem pr1506413 : PrimeCertificate 1506413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv376603]) (by decide +kernel)
def pv1506413 : PrimeValue := ⟨1506413, pr1506413⟩
private theorem pr1506509 : PrimeCertificate 1506509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv376627]) (by decide +kernel)
def pv1506509 : PrimeValue := ⟨1506509, pr1506509⟩
private theorem pr1506689 : PrimeCertificate 1506689 :=
  certifyPrime (q := pv3) (ls := [pv2,pv79,pv149]) (by decide +kernel)
def pv1506689 : PrimeValue := ⟨1506689, pr1506689⟩
private theorem pr1506731 : PrimeCertificate 1506731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv6551]) (by decide +kernel)
def pv1506731 : PrimeValue := ⟨1506731, pr1506731⟩
private theorem pr1506779 : PrimeCertificate 1506779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv17,pv487]) (by decide +kernel)
def pv1506779 : PrimeValue := ⟨1506779, pr1506779⟩
private theorem pr1506929 : PrimeCertificate 1506929 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv4957]) (by decide +kernel)
def pv1506929 : PrimeValue := ⟨1506929, pr1506929⟩
private theorem pr1506959 : PrimeCertificate 1506959 :=
  certifyPrime (q := pv11) (ls := [pv2,pv401,pv1879]) (by decide +kernel)
def pv1506959 : PrimeValue := ⟨1506959, pr1506959⟩
private theorem pr1507073 : PrimeCertificate 1507073 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv29]) (by decide +kernel)
def pv1507073 : PrimeValue := ⟨1507073, pr1507073⟩
private theorem pr1507763 : PrimeCertificate 1507763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv691,pv1091]) (by decide +kernel)
def pv1507763 : PrimeValue := ⟨1507763, pr1507763⟩
private theorem pr1507769 : PrimeCertificate 1507769 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv67,pv97]) (by decide +kernel)
def pv1507769 : PrimeValue := ⟨1507769, pr1507769⟩
private theorem pr1508033 : PrimeCertificate 1508033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23563]) (by decide +kernel)
def pv1508033 : PrimeValue := ⟨1508033, pr1508033⟩
private theorem pr1508051 : PrimeCertificate 1508051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv30161]) (by decide +kernel)
def pv1508051 : PrimeValue := ⟨1508051, pr1508051⟩
private theorem pr1508579 : PrimeCertificate 1508579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv754289]) (by decide +kernel)
def pv1508579 : PrimeValue := ⟨1508579, pr1508579⟩
private theorem pr1508651 : PrimeCertificate 1508651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv13,pv211]) (by decide +kernel)
def pv1508651 : PrimeValue := ⟨1508651, pr1508651⟩
private theorem pr1508711 : PrimeCertificate 1508711 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv3079]) (by decide +kernel)
def pv1508711 : PrimeValue := ⟨1508711, pr1508711⟩
private theorem pr1508729 : PrimeCertificate 1508729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv89,pv163]) (by decide +kernel)
def pv1508729 : PrimeValue := ⟨1508729, pr1508729⟩
private theorem pr1508789 : PrimeCertificate 1508789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv377197]) (by decide +kernel)
def pv1508789 : PrimeValue := ⟨1508789, pr1508789⟩
private theorem pr1508813 : PrimeCertificate 1508813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv13007]) (by decide +kernel)
def pv1508813 : PrimeValue := ⟨1508813, pr1508813⟩
private theorem pr1508879 : PrimeCertificate 1508879 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv107777]) (by decide +kernel)
def pv1508879 : PrimeValue := ⟨1508879, pr1508879⟩
private theorem pr1508933 : PrimeCertificate 1508933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv97,pv3889]) (by decide +kernel)
def pv1508933 : PrimeValue := ⟨1508933, pr1508933⟩
private theorem pr1509269 : PrimeCertificate 1509269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv127,pv2971]) (by decide +kernel)
def pv1509269 : PrimeValue := ⟨1509269, pr1509269⟩
private theorem pr1509509 : PrimeCertificate 1509509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv13,pv29]) (by decide +kernel)
def pv1509509 : PrimeValue := ⟨1509509, pr1509509⟩
private theorem pr1509533 : PrimeCertificate 1509533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv79,pv281]) (by decide +kernel)
def pv1509533 : PrimeValue := ⟨1509533, pr1509533⟩
private theorem pr1509941 : PrimeCertificate 1509941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv4441]) (by decide +kernel)
def pv1509941 : PrimeValue := ⟨1509941, pr1509941⟩
private theorem pr1510013 : PrimeCertificate 1510013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv199,pv271]) (by decide +kernel)
def pv1510013 : PrimeValue := ⟨1510013, pr1510013⟩
private theorem pr1510109 : PrimeCertificate 1510109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv377527]) (by decide +kernel)
def pv1510109 : PrimeValue := ⟨1510109, pr1510109⟩
private theorem pr1510163 : PrimeCertificate 1510163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv755081]) (by decide +kernel)
def pv1510163 : PrimeValue := ⟨1510163, pr1510163⟩
private theorem pr1510199 : PrimeCertificate 1510199 :=
  certifyPrime (q := pv11) (ls := [pv2,pv107,pv7057]) (by decide +kernel)
def pv1510199 : PrimeValue := ⟨1510199, pr1510199⟩
private theorem pr1510343 : PrimeCertificate 1510343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv755171]) (by decide +kernel)
def pv1510343 : PrimeValue := ⟨1510343, pr1510343⟩
private theorem pr1510391 : PrimeCertificate 1510391 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv21577]) (by decide +kernel)
def pv1510391 : PrimeValue := ⟨1510391, pr1510391⟩
private theorem pr1510703 : PrimeCertificate 1510703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv755351]) (by decide +kernel)
def pv1510703 : PrimeValue := ⟨1510703, pr1510703⟩
private theorem pr1510763 : PrimeCertificate 1510763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv43,pv1597]) (by decide +kernel)
def pv1510763 : PrimeValue := ⟨1510763, pr1510763⟩
private theorem pr1510961 : PrimeCertificate 1510961 :=
  certifyPrime (q := pv29) (ls := [pv2,pv5,pv11,pv17,pv101]) (by decide +kernel)
def pv1510961 : PrimeValue := ⟨1510961, pr1510961⟩
private theorem pr1510991 : PrimeCertificate 1510991 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv13,pv59,pv197]) (by decide +kernel)
def pv1510991 : PrimeValue := ⟨1510991, pr1510991⟩
private theorem pr1511021 : PrimeCertificate 1511021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv43,pv251]) (by decide +kernel)
def pv1511021 : PrimeValue := ⟨1511021, pr1511021⟩
private theorem pr1511129 : PrimeCertificate 1511129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv188891]) (by decide +kernel)
def pv1511129 : PrimeValue := ⟨1511129, pr1511129⟩
private theorem pr1511201 : PrimeCertificate 1511201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1889]) (by decide +kernel)
def pv1511201 : PrimeValue := ⟨1511201, pr1511201⟩
private theorem pr1511423 : PrimeCertificate 1511423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv23,pv29,pv103]) (by decide +kernel)
def pv1511423 : PrimeValue := ⟨1511423, pr1511423⟩
private theorem pr1511441 : PrimeCertificate 1511441 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv2699]) (by decide +kernel)
def pv1511441 : PrimeValue := ⟨1511441, pr1511441⟩
private theorem pr1511651 : PrimeCertificate 1511651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv617]) (by decide +kernel)
def pv1511651 : PrimeValue := ⟨1511651, pr1511651⟩
private theorem pr1511921 : PrimeCertificate 1511921 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv18899]) (by decide +kernel)
def pv1511921 : PrimeValue := ⟨1511921, pr1511921⟩
private theorem pr1512041 : PrimeCertificate 1512041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv103,pv367]) (by decide +kernel)
def pv1512041 : PrimeValue := ⟨1512041, pr1512041⟩
private theorem pr1512083 : PrimeCertificate 1512083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13,pv17,pv311]) (by decide +kernel)
def pv1512083 : PrimeValue := ⟨1512083, pr1512083⟩
private theorem pr1512113 : PrimeCertificate 1512113 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv23,pv587]) (by decide +kernel)
def pv1512113 : PrimeValue := ⟨1512113, pr1512113⟩
private theorem pr1512221 : PrimeCertificate 1512221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv75611]) (by decide +kernel)
def pv1512221 : PrimeValue := ⟨1512221, pr1512221⟩
private theorem pr1512299 : PrimeCertificate 1512299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv756149]) (by decide +kernel)
def pv1512299 : PrimeValue := ⟨1512299, pr1512299⟩
private theorem pr1512383 : PrimeCertificate 1512383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv756191]) (by decide +kernel)
def pv1512383 : PrimeValue := ⟨1512383, pr1512383⟩
private theorem pr1512431 : PrimeCertificate 1512431 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv151243]) (by decide +kernel)
def pv1512431 : PrimeValue := ⟨1512431, pr1512431⟩
private theorem pr1512809 : PrimeCertificate 1512809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv17191]) (by decide +kernel)
def pv1512809 : PrimeValue := ⟨1512809, pr1512809⟩
private theorem pr1513073 : PrimeCertificate 1513073 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv8597]) (by decide +kernel)
def pv1513073 : PrimeValue := ⟨1513073, pr1513073⟩
private theorem pr1513091 : PrimeCertificate 1513091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv83,pv1823]) (by decide +kernel)
def pv1513091 : PrimeValue := ⟨1513091, pr1513091⟩
private theorem pr1513139 : PrimeCertificate 1513139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv109,pv631]) (by decide +kernel)
def pv1513139 : PrimeValue := ⟨1513139, pr1513139⟩
private theorem pr1513751 : PrimeCertificate 1513751 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv173]) (by decide +kernel)
def pv1513751 : PrimeValue := ⟨1513751, pr1513751⟩
private theorem pr1513859 : PrimeCertificate 1513859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv43,pv607]) (by decide +kernel)
def pv1513859 : PrimeValue := ⟨1513859, pr1513859⟩
private theorem pr1514213 : PrimeCertificate 1514213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv41,pv1319]) (by decide +kernel)
def pv1514213 : PrimeValue := ⟨1514213, pr1514213⟩
private theorem pr1514291 : PrimeCertificate 1514291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv151429]) (by decide +kernel)
def pv1514291 : PrimeValue := ⟨1514291, pr1514291⟩
private theorem pr1514321 : PrimeCertificate 1514321 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv23,pv823]) (by decide +kernel)
def pv1514321 : PrimeValue := ⟨1514321, pr1514321⟩
private theorem pr1514399 : PrimeCertificate 1514399 :=
  certifyPrime (q := pv17) (ls := [pv2,pv137,pv5527]) (by decide +kernel)
def pv1514399 : PrimeValue := ⟨1514399, pr1514399⟩
private theorem pr1514549 : PrimeCertificate 1514549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv54091]) (by decide +kernel)
def pv1514549 : PrimeValue := ⟨1514549, pr1514549⟩
private theorem pr1514741 : PrimeCertificate 1514741 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv53,pv1429]) (by decide +kernel)
def pv1514741 : PrimeValue := ⟨1514741, pr1514741⟩
private theorem pr1514801 : PrimeCertificate 1514801 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv541]) (by decide +kernel)
def pv1514801 : PrimeValue := ⟨1514801, pr1514801⟩
private theorem pr1515053 : PrimeCertificate 1515053 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11,pv4919]) (by decide +kernel)
def pv1515053 : PrimeValue := ⟨1515053, pr1515053⟩
private theorem pr1515089 : PrimeCertificate 1515089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv94693]) (by decide +kernel)
def pv1515089 : PrimeValue := ⟨1515089, pr1515089⟩
private theorem pr1515359 : PrimeCertificate 1515359 :=
  certifyPrime (q := pv23) (ls := [pv2,pv13,pv167,pv349]) (by decide +kernel)
def pv1515359 : PrimeValue := ⟨1515359, pr1515359⟩
private theorem pr1515509 : PrimeCertificate 1515509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv223,pv1699]) (by decide +kernel)
def pv1515509 : PrimeValue := ⟨1515509, pr1515509⟩
private theorem pr1515623 : PrimeCertificate 1515623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv757811]) (by decide +kernel)
def pv1515623 : PrimeValue := ⟨1515623, pr1515623⟩
private theorem pr1515809 : PrimeCertificate 1515809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv67,pv101]) (by decide +kernel)
def pv1515809 : PrimeValue := ⟨1515809, pr1515809⟩
private theorem pr1516103 : PrimeCertificate 1516103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv108293]) (by decide +kernel)
def pv1516103 : PrimeValue := ⟨1516103, pr1516103⟩
private theorem pr1516199 : PrimeCertificate 1516199 :=
  certifyPrime (q := pv11) (ls := [pv2,pv758099]) (by decide +kernel)
def pv1516199 : PrimeValue := ⟨1516199, pr1516199⟩
private theorem pr1516433 : PrimeCertificate 1516433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv94777]) (by decide +kernel)
def pv1516433 : PrimeValue := ⟨1516433, pr1516433⟩
private theorem pr1516499 : PrimeCertificate 1516499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv97,pv7817]) (by decide +kernel)
def pv1516499 : PrimeValue := ⟨1516499, pr1516499⟩
private theorem pr1516583 : PrimeCertificate 1516583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv31,pv61,pv401]) (by decide +kernel)
def pv1516583 : PrimeValue := ⟨1516583, pr1516583⟩
private theorem pr1516661 : PrimeCertificate 1516661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv75833]) (by decide +kernel)
def pv1516661 : PrimeValue := ⟨1516661, pr1516661⟩
private theorem pr1516709 : PrimeCertificate 1516709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv379177]) (by decide +kernel)
def pv1516709 : PrimeValue := ⟨1516709, pr1516709⟩
private theorem pr1517189 : PrimeCertificate 1517189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv19963]) (by decide +kernel)
def pv1517189 : PrimeValue := ⟨1517189, pr1517189⟩
private theorem pr1517261 : PrimeCertificate 1517261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv107,pv709]) (by decide +kernel)
def pv1517261 : PrimeValue := ⟨1517261, pr1517261⟩
private theorem pr1517339 : PrimeCertificate 1517339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv26161]) (by decide +kernel)
def pv1517339 : PrimeValue := ⟨1517339, pr1517339⟩
private theorem pr1517441 : PrimeCertificate 1517441 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv2371]) (by decide +kernel)
def pv1517441 : PrimeValue := ⟨1517441, pr1517441⟩
private theorem pr1517531 : PrimeCertificate 1517531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv19,pv163]) (by decide +kernel)
def pv1517531 : PrimeValue := ⟨1517531, pr1517531⟩
private theorem pr1517591 : PrimeCertificate 1517591 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv17,pv79,pv113]) (by decide +kernel)
def pv1517591 : PrimeValue := ⟨1517591, pr1517591⟩
private theorem pr1517753 : PrimeCertificate 1517753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv193,pv983]) (by decide +kernel)
def pv1517753 : PrimeValue := ⟨1517753, pr1517753⟩
private theorem pr1518449 : PrimeCertificate 1518449 :=
  certifyPrime (q := pv3) (ls := [pv2,pv94903]) (by decide +kernel)
def pv1518449 : PrimeValue := ⟨1518449, pr1518449⟩
private theorem pr1518623 : PrimeCertificate 1518623 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv67,pv1619]) (by decide +kernel)
def pv1518623 : PrimeValue := ⟨1518623, pr1518623⟩
private theorem pr1519313 : PrimeCertificate 1519313 :=
  certifyPrime (q := pv3) (ls := [pv2,pv269,pv353]) (by decide +kernel)
def pv1519313 : PrimeValue := ⟨1519313, pr1519313⟩
private theorem pr1519421 : PrimeCertificate 1519421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv10853]) (by decide +kernel)
def pv1519421 : PrimeValue := ⟨1519421, pr1519421⟩
private theorem pr1519499 : PrimeCertificate 1519499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv293,pv2593]) (by decide +kernel)
def pv1519499 : PrimeValue := ⟨1519499, pr1519499⟩
private theorem pr1519631 : PrimeCertificate 1519631 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv17,pv1277]) (by decide +kernel)
def pv1519631 : PrimeValue := ⟨1519631, pr1519631⟩
private theorem pr1519673 : PrimeCertificate 1519673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11,pv2467]) (by decide +kernel)
def pv1519673 : PrimeValue := ⟨1519673, pr1519673⟩
private theorem pr1519709 : PrimeCertificate 1519709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv379927]) (by decide +kernel)
def pv1519709 : PrimeValue := ⟨1519709, pr1519709⟩
private theorem pr1519733 : PrimeCertificate 1519733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv22349]) (by decide +kernel)
def pv1519733 : PrimeValue := ⟨1519733, pr1519733⟩
private theorem pr1520153 : PrimeCertificate 1520153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv73,pv137]) (by decide +kernel)
def pv1520153 : PrimeValue := ⟨1520153, pr1520153⟩
private theorem pr1520483 : PrimeCertificate 1520483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv760241]) (by decide +kernel)
def pv1520483 : PrimeValue := ⟨1520483, pr1520483⟩
private theorem pr1520639 : PrimeCertificate 1520639 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv47,pv2311]) (by decide +kernel)
def pv1520639 : PrimeValue := ⟨1520639, pr1520639⟩
private theorem pr1520801 : PrimeCertificate 1520801 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1901]) (by decide +kernel)
def pv1520801 : PrimeValue := ⟨1520801, pr1520801⟩
private theorem pr1521011 : PrimeCertificate 1521011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv89,pv1709]) (by decide +kernel)
def pv1521011 : PrimeValue := ⟨1521011, pr1521011⟩
private theorem pr1521029 : PrimeCertificate 1521029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv5209]) (by decide +kernel)
def pv1521029 : PrimeValue := ⟨1521029, pr1521029⟩
private theorem pr1521479 : PrimeCertificate 1521479 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv108677]) (by decide +kernel)
def pv1521479 : PrimeValue := ⟨1521479, pr1521479⟩
private theorem pr1521623 : PrimeCertificate 1521623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv661,pv1151]) (by decide +kernel)
def pv1521623 : PrimeValue := ⟨1521623, pr1521623⟩
private theorem pr1521809 : PrimeCertificate 1521809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv227,pv419]) (by decide +kernel)
def pv1521809 : PrimeValue := ⟨1521809, pr1521809⟩
private theorem pr1521869 : PrimeCertificate 1521869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv101,pv3767]) (by decide +kernel)
def pv1521869 : PrimeValue := ⟨1521869, pr1521869⟩
private theorem pr1521893 : PrimeCertificate 1521893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv337,pv1129]) (by decide +kernel)
def pv1521893 : PrimeValue := ⟨1521893, pr1521893⟩
private theorem pr1522331 : PrimeCertificate 1522331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41,pv47,pv79]) (by decide +kernel)
def pv1522331 : PrimeValue := ⟨1522331, pr1522331⟩
private theorem pr1522589 : PrimeCertificate 1522589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv22391]) (by decide +kernel)
def pv1522589 : PrimeValue := ⟨1522589, pr1522589⟩
private theorem pr1522799 : PrimeCertificate 1522799 :=
  certifyPrime (q := pv11) (ls := [pv2,pv761399]) (by decide +kernel)
def pv1522799 : PrimeValue := ⟨1522799, pr1522799⟩
private theorem pr1523069 : PrimeCertificate 1523069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv41,pv251]) (by decide +kernel)
def pv1523069 : PrimeValue := ⟨1523069, pr1523069⟩
private theorem pr1523381 : PrimeCertificate 1523381 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv59,pv1291]) (by decide +kernel)
def pv1523381 : PrimeValue := ⟨1523381, pr1523381⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
