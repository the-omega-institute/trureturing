/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table230
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table230.pv1100653
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table011
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table024
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table061
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table062

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr1100653 : PrimeCertificate 1100653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv13103]) (by decide +kernel)
def pv1100653 : PrimeValue := ⟨1100653, pr1100653⟩
private theorem pr1100773 : PrimeCertificate 1100773 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv30577]) (by decide +kernel)
def pv1100773 : PrimeValue := ⟨1100773, pr1100773⟩
private theorem pr1100857 : PrimeCertificate 1100857 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv45869]) (by decide +kernel)
def pv1100857 : PrimeValue := ⟨1100857, pr1100857⟩
private theorem pr1100977 : PrimeCertificate 1100977 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv22937]) (by decide +kernel)
def pv1100977 : PrimeValue := ⟨1100977, pr1100977⟩
private theorem pr1101109 : PrimeCertificate 1101109 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv89,pv1031]) (by decide +kernel)
def pv1101109 : PrimeValue := ⟨1101109, pr1101109⟩
private theorem pr1101169 : PrimeCertificate 1101169 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv2549]) (by decide +kernel)
def pv1101169 : PrimeValue := ⟨1101169, pr1101169⟩
private theorem pr1101193 : PrimeCertificate 1101193 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv17,pv2699]) (by decide +kernel)
def pv1101193 : PrimeValue := ⟨1101193, pr1101193⟩
private theorem pr1101283 : PrimeCertificate 1101283 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv13,pv2017]) (by decide +kernel)
def pv1101283 : PrimeValue := ⟨1101283, pr1101283⟩
private theorem pr1101409 : PrimeCertificate 1101409 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv7,pv11,pv149]) (by decide +kernel)
def pv1101409 : PrimeValue := ⟨1101409, pr1101409⟩
private theorem pr1101517 : PrimeCertificate 1101517 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv13,pv23,pv307]) (by decide +kernel)
def pv1101517 : PrimeValue := ⟨1101517, pr1101517⟩
private theorem pr1101613 : PrimeCertificate 1101613 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv91801]) (by decide +kernel)
def pv1101613 : PrimeValue := ⟨1101613, pr1101613⟩
private theorem pr1101619 : PrimeCertificate 1101619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1249]) (by decide +kernel)
def pv1101619 : PrimeValue := ⟨1101619, pr1101619⟩
private theorem pr1102027 : PrimeCertificate 1102027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61,pv3011]) (by decide +kernel)
def pv1102027 : PrimeValue := ⟨1102027, pr1102027⟩
private theorem pr1102069 : PrimeCertificate 1102069 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv23]) (by decide +kernel)
def pv1102069 : PrimeValue := ⟨1102069, pr1102069⟩
private theorem pr1102159 : PrimeCertificate 1102159 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv61231]) (by decide +kernel)
def pv1102159 : PrimeValue := ⟨1102159, pr1102159⟩
private theorem pr1102243 : PrimeCertificate 1102243 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv183707]) (by decide +kernel)
def pv1102243 : PrimeValue := ⟨1102243, pr1102243⟩
private theorem pr1102249 : PrimeCertificate 1102249 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv1102249 : PrimeValue := ⟨1102249, pr1102249⟩
private theorem pr1102333 : PrimeCertificate 1102333 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv11,pv1193]) (by decide +kernel)
def pv1102333 : PrimeValue := ⟨1102333, pr1102333⟩
private theorem pr1103119 : PrimeCertificate 1103119 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv37,pv4969]) (by decide +kernel)
def pv1103119 : PrimeValue := ⟨1103119, pr1103119⟩
private theorem pr1103203 : PrimeCertificate 1103203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv167,pv367]) (by decide +kernel)
def pv1103203 : PrimeValue := ⟨1103203, pr1103203⟩
private theorem pr1103257 : PrimeCertificate 1103257 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv199]) (by decide +kernel)
def pv1103257 : PrimeValue := ⟨1103257, pr1103257⟩
private theorem pr1103293 : PrimeCertificate 1103293 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv1613]) (by decide +kernel)
def pv1103293 : PrimeValue := ⟨1103293, pr1103293⟩
private theorem pr1103449 : PrimeCertificate 1103449 :=
  certifyPrime (q := pv47) (ls := [pv2,pv3,pv23,pv1999]) (by decide +kernel)
def pv1103449 : PrimeValue := ⟨1103449, pr1103449⟩
private theorem pr1103467 : PrimeCertificate 1103467 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv43,pv47]) (by decide +kernel)
def pv1103467 : PrimeValue := ⟨1103467, pr1103467⟩
private theorem pr1103587 : PrimeCertificate 1103587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv23,pv727]) (by decide +kernel)
def pv1103587 : PrimeValue := ⟨1103587, pr1103587⟩
private theorem pr1104193 : PrimeCertificate 1104193 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv71]) (by decide +kernel)
def pv1104193 : PrimeValue := ⟨1104193, pr1104193⟩
private theorem pr1104217 : PrimeCertificate 1104217 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv139,pv331]) (by decide +kernel)
def pv1104217 : PrimeValue := ⟨1104217, pr1104217⟩
private theorem pr1104373 : PrimeCertificate 1104373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv30677]) (by decide +kernel)
def pv1104373 : PrimeValue := ⟨1104373, pr1104373⟩
private theorem pr1104403 : PrimeCertificate 1104403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv14159]) (by decide +kernel)
def pv1104403 : PrimeValue := ⟨1104403, pr1104403⟩
private theorem pr1104517 : PrimeCertificate 1104517 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv487]) (by decide +kernel)
def pv1104517 : PrimeValue := ⟨1104517, pr1104517⟩
private theorem pr1104589 : PrimeCertificate 1104589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61,pv503]) (by decide +kernel)
def pv1104589 : PrimeValue := ⟨1104589, pr1104589⟩
private theorem pr1104823 : PrimeCertificate 1104823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv61379]) (by decide +kernel)
def pv1104823 : PrimeValue := ⟨1104823, pr1104823⟩
private theorem pr1104877 : PrimeCertificate 1104877 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv47,pv653]) (by decide +kernel)
def pv1104877 : PrimeValue := ⟨1104877, pr1104877⟩
private theorem pr1104889 : PrimeCertificate 1104889 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv19,pv2423]) (by decide +kernel)
def pv1104889 : PrimeValue := ⟨1104889, pr1104889⟩
private theorem pr1105009 : PrimeCertificate 1105009 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23021]) (by decide +kernel)
def pv1105009 : PrimeValue := ⟨1105009, pr1105009⟩
private theorem pr1105309 : PrimeCertificate 1105309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv30703]) (by decide +kernel)
def pv1105309 : PrimeValue := ⟨1105309, pr1105309⟩
private theorem pr1105639 : PrimeCertificate 1105639 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv184273]) (by decide +kernel)
def pv1105639 : PrimeValue := ⟨1105639, pr1105639⟩
private theorem pr1105693 : PrimeCertificate 1105693 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv13163]) (by decide +kernel)
def pv1105693 : PrimeValue := ⟨1105693, pr1105693⟩
private theorem pr1105759 : PrimeCertificate 1105759 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv20477]) (by decide +kernel)
def pv1105759 : PrimeValue := ⟨1105759, pr1105759⟩
private theorem pr1105813 : PrimeCertificate 1105813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3413]) (by decide +kernel)
def pv1105813 : PrimeValue := ⟨1105813, pr1105813⟩
private theorem pr1105873 : PrimeCertificate 1105873 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23039]) (by decide +kernel)
def pv1105873 : PrimeValue := ⟨1105873, pr1105873⟩
private theorem pr1106029 : PrimeCertificate 1106029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv19]) (by decide +kernel)
def pv1106029 : PrimeValue := ⟨1106029, pr1106029⟩
private theorem pr1106167 : PrimeCertificate 1106167 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv107,pv1723]) (by decide +kernel)
def pv1106167 : PrimeValue := ⟨1106167, pr1106167⟩
private theorem pr1106197 : PrimeCertificate 1106197 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv1013]) (by decide +kernel)
def pv1106197 : PrimeValue := ⟨1106197, pr1106197⟩
private theorem pr1106419 : PrimeCertificate 1106419 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv61,pv3023]) (by decide +kernel)
def pv1106419 : PrimeValue := ⟨1106419, pr1106419⟩
private theorem pr1106527 : PrimeCertificate 1106527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv223,pv827]) (by decide +kernel)
def pv1106527 : PrimeValue := ⟨1106527, pr1106527⟩
private theorem pr1106569 : PrimeCertificate 1106569 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv47,pv109]) (by decide +kernel)
def pv1106569 : PrimeValue := ⟨1106569, pr1106569⟩
private theorem pr1106629 : PrimeCertificate 1106629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv92219]) (by decide +kernel)
def pv1106629 : PrimeValue := ⟨1106629, pr1106629⟩
private theorem pr1106767 : PrimeCertificate 1106767 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv61487]) (by decide +kernel)
def pv1106767 : PrimeValue := ⟨1106767, pr1106767⟩
private theorem pr1106779 : PrimeCertificate 1106779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv184463]) (by decide +kernel)
def pv1106779 : PrimeValue := ⟨1106779, pr1106779⟩
private theorem pr1107217 : PrimeCertificate 1107217 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv233]) (by decide +kernel)
def pv1107217 : PrimeValue := ⟨1107217, pr1107217⟩
private theorem pr1107319 : PrimeCertificate 1107319 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv184553]) (by decide +kernel)
def pv1107319 : PrimeValue := ⟨1107319, pr1107319⟩
private theorem pr1107439 : PrimeCertificate 1107439 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv379,pv487]) (by decide +kernel)
def pv1107439 : PrimeValue := ⟨1107439, pr1107439⟩
private theorem pr1107523 : PrimeCertificate 1107523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv4733]) (by decide +kernel)
def pv1107523 : PrimeValue := ⟨1107523, pr1107523⟩
private theorem pr1107553 : PrimeCertificate 1107553 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv83,pv139]) (by decide +kernel)
def pv1107553 : PrimeValue := ⟨1107553, pr1107553⟩
private theorem pr1107787 : PrimeCertificate 1107787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv184631]) (by decide +kernel)
def pv1107787 : PrimeValue := ⟨1107787, pr1107787⟩
private theorem pr1107823 : PrimeCertificate 1107823 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv17,pv10861]) (by decide +kernel)
def pv1107823 : PrimeValue := ⟨1107823, pr1107823⟩
private theorem pr1107913 : PrimeCertificate 1107913 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13,pv53,pv67]) (by decide +kernel)
def pv1107913 : PrimeValue := ⟨1107913, pr1107913⟩
private theorem pr1108057 : PrimeCertificate 1108057 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv137,pv337]) (by decide +kernel)
def pv1108057 : PrimeValue := ⟨1108057, pr1108057⟩
private theorem pr1108207 : PrimeCertificate 1108207 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv29,pv193]) (by decide +kernel)
def pv1108207 : PrimeValue := ⟨1108207, pr1108207⟩
private theorem pr1108267 : PrimeCertificate 1108267 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv184711]) (by decide +kernel)
def pv1108267 : PrimeValue := ⟨1108267, pr1108267⟩
private theorem pr1108369 : PrimeCertificate 1108369 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv43,pv179]) (by decide +kernel)
def pv1108369 : PrimeValue := ⟨1108369, pr1108369⟩
private theorem pr1108537 : PrimeCertificate 1108537 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv13,pv17,pv19]) (by decide +kernel)
def pv1108537 : PrimeValue := ⟨1108537, pr1108537⟩
private theorem pr1108543 : PrimeCertificate 1108543 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv47,pv3931]) (by decide +kernel)
def pv1108543 : PrimeValue := ⟨1108543, pr1108543⟩
private theorem pr1108867 : PrimeCertificate 1108867 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11,pv53,pv317]) (by decide +kernel)
def pv1108867 : PrimeValue := ⟨1108867, pr1108867⟩
private theorem pr1109167 : PrimeCertificate 1109167 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv401,pv461]) (by decide +kernel)
def pv1109167 : PrimeValue := ⟨1109167, pr1109167⟩
private theorem pr1109653 : PrimeCertificate 1109653 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv89,pv1039]) (by decide +kernel)
def pv1109653 : PrimeValue := ⟨1109653, pr1109653⟩
private theorem pr1109737 : PrimeCertificate 1109737 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv15413]) (by decide +kernel)
def pv1109737 : PrimeValue := ⟨1109737, pr1109737⟩
private theorem pr1109749 : PrimeCertificate 1109749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv92479]) (by decide +kernel)
def pv1109749 : PrimeValue := ⟨1109749, pr1109749⟩
private theorem pr1110103 : PrimeCertificate 1110103 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv26431]) (by decide +kernel)
def pv1110103 : PrimeValue := ⟨1110103, pr1110103⟩
private theorem pr1110349 : PrimeCertificate 1110349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv149]) (by decide +kernel)
def pv1110349 : PrimeValue := ⟨1110349, pr1110349⟩
private theorem pr1110397 : PrimeCertificate 1110397 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv13219]) (by decide +kernel)
def pv1110397 : PrimeValue := ⟨1110397, pr1110397⟩
private theorem pr1110433 : PrimeCertificate 1110433 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv43,pv269]) (by decide +kernel)
def pv1110433 : PrimeValue := ⟨1110433, pr1110433⟩
private theorem pr1110517 : PrimeCertificate 1110517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv47,pv179]) (by decide +kernel)
def pv1110517 : PrimeValue := ⟨1110517, pr1110517⟩
private theorem pr1110523 : PrimeCertificate 1110523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv137,pv193]) (by decide +kernel)
def pv1110523 : PrimeValue := ⟨1110523, pr1110523⟩
private theorem pr1110547 : PrimeCertificate 1110547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv103,pv599]) (by decide +kernel)
def pv1110547 : PrimeValue := ⟨1110547, pr1110547⟩
private theorem pr1110589 : PrimeCertificate 1110589 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv19,pv4871]) (by decide +kernel)
def pv1110589 : PrimeValue := ⟨1110589, pr1110589⟩
private theorem pr1110643 : PrimeCertificate 1110643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv29,pv491]) (by decide +kernel)
def pv1110643 : PrimeValue := ⟨1110643, pr1110643⟩
private theorem pr1110727 : PrimeCertificate 1110727 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv67,pv307]) (by decide +kernel)
def pv1110727 : PrimeValue := ⟨1110727, pr1110727⟩
private theorem pr1110913 : PrimeCertificate 1110913 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv263]) (by decide +kernel)
def pv1110913 : PrimeValue := ⟨1110913, pr1110913⟩
private theorem pr1110973 : PrimeCertificate 1110973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv92581]) (by decide +kernel)
def pv1110973 : PrimeValue := ⟨1110973, pr1110973⟩
private theorem pr1111057 : PrimeCertificate 1111057 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv79,pv293]) (by decide +kernel)
def pv1111057 : PrimeValue := ⟨1111057, pr1111057⟩
private theorem pr1111219 : PrimeCertificate 1111219 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv167,pv1109]) (by decide +kernel)
def pv1111219 : PrimeValue := ⟨1111219, pr1111219⟩
private theorem pr1111333 : PrimeCertificate 1111333 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv37,pv2503]) (by decide +kernel)
def pv1111333 : PrimeValue := ⟨1111333, pr1111333⟩
private theorem pr1111573 : PrimeCertificate 1111573 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv401]) (by decide +kernel)
def pv1111573 : PrimeValue := ⟨1111573, pr1111573⟩
private theorem pr1111897 : PrimeCertificate 1111897 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv15443]) (by decide +kernel)
def pv1111897 : PrimeValue := ⟨1111897, pr1111897⟩
private theorem pr1111963 : PrimeCertificate 1111963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv185327]) (by decide +kernel)
def pv1111963 : PrimeValue := ⟨1111963, pr1111963⟩
private theorem pr1112143 : PrimeCertificate 1112143 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23,pv8059]) (by decide +kernel)
def pv1112143 : PrimeValue := ⟨1112143, pr1112143⟩
private theorem pr1112239 : PrimeCertificate 1112239 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv43,pv479]) (by decide +kernel)
def pv1112239 : PrimeValue := ⟨1112239, pr1112239⟩
private theorem pr1112269 : PrimeCertificate 1112269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv59,pv1571]) (by decide +kernel)
def pv1112269 : PrimeValue := ⟨1112269, pr1112269⟩
private theorem pr1112653 : PrimeCertificate 1112653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv997]) (by decide +kernel)
def pv1112653 : PrimeValue := ⟨1112653, pr1112653⟩
private theorem pr1112689 : PrimeCertificate 1112689 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7727]) (by decide +kernel)
def pv1112689 : PrimeValue := ⟨1112689, pr1112689⟩
private theorem pr1112707 : PrimeCertificate 1112707 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv8831]) (by decide +kernel)
def pv1112707 : PrimeValue := ⟨1112707, pr1112707⟩
private theorem pr1112827 : PrimeCertificate 1112827 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv13,pv1297]) (by decide +kernel)
def pv1112827 : PrimeValue := ⟨1112827, pr1112827⟩
private theorem pr1112857 : PrimeCertificate 1112857 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv89,pv521]) (by decide +kernel)
def pv1112857 : PrimeValue := ⟨1112857, pr1112857⟩
private theorem pr1112953 : PrimeCertificate 1112953 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv79,pv587]) (by decide +kernel)
def pv1112953 : PrimeValue := ⟨1112953, pr1112953⟩
private theorem pr1113199 : PrimeCertificate 1113199 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv185533]) (by decide +kernel)
def pv1113199 : PrimeValue := ⟨1113199, pr1113199⟩
private theorem pr1113253 : PrimeCertificate 1113253 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv29,pv457]) (by decide +kernel)
def pv1113253 : PrimeValue := ⟨1113253, pr1113253⟩
private theorem pr1113337 : PrimeCertificate 1113337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv47]) (by decide +kernel)
def pv1113337 : PrimeValue := ⟨1113337, pr1113337⟩
private theorem pr1113379 : PrimeCertificate 1113379 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv541]) (by decide +kernel)
def pv1113379 : PrimeValue := ⟨1113379, pr1113379⟩
private theorem pr1113403 : PrimeCertificate 1113403 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv185567]) (by decide +kernel)
def pv1113403 : PrimeValue := ⟨1113403, pr1113403⟩
private theorem pr1113877 : PrimeCertificate 1113877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv30941]) (by decide +kernel)
def pv1113877 : PrimeValue := ⟨1113877, pr1113877⟩
private theorem pr1113883 : PrimeCertificate 1113883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv2411]) (by decide +kernel)
def pv1113883 : PrimeValue := ⟨1113883, pr1113883⟩
private theorem pr1113949 : PrimeCertificate 1113949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv29,pv97]) (by decide +kernel)
def pv1113949 : PrimeValue := ⟨1113949, pr1113949⟩
private theorem pr1114249 : PrimeCertificate 1114249 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv2731]) (by decide +kernel)
def pv1114249 : PrimeValue := ⟨1114249, pr1114249⟩
private theorem pr1114273 : PrimeCertificate 1114273 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv53,pv73]) (by decide +kernel)
def pv1114273 : PrimeValue := ⟨1114273, pr1114273⟩
private theorem pr1114423 : PrimeCertificate 1114423 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv185737]) (by decide +kernel)
def pv1114423 : PrimeValue := ⟨1114423, pr1114423⟩
private theorem pr1114567 : PrimeCertificate 1114567 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv431]) (by decide +kernel)
def pv1114567 : PrimeValue := ⟨1114567, pr1114567⟩
private theorem pr1114723 : PrimeCertificate 1114723 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv983]) (by decide +kernel)
def pv1114723 : PrimeValue := ⟨1114723, pr1114723⟩
private theorem pr1115113 : PrimeCertificate 1115113 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv97,pv479]) (by decide +kernel)
def pv1115113 : PrimeValue := ⟨1115113, pr1115113⟩
private theorem pr1115227 : PrimeCertificate 1115227 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv53,pv167]) (by decide +kernel)
def pv1115227 : PrimeValue := ⟨1115227, pr1115227⟩
private theorem pr1115449 : PrimeCertificate 1115449 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv46477]) (by decide +kernel)
def pv1115449 : PrimeValue := ⟨1115449, pr1115449⟩
private theorem pr1115467 : PrimeCertificate 1115467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv16901]) (by decide +kernel)
def pv1115467 : PrimeValue := ⟨1115467, pr1115467⟩
private theorem pr1116133 : PrimeCertificate 1116133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv281,pv331]) (by decide +kernel)
def pv1116133 : PrimeValue := ⟨1116133, pr1116133⟩
private theorem pr1116223 : PrimeCertificate 1116223 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv186037]) (by decide +kernel)
def pv1116223 : PrimeValue := ⟨1116223, pr1116223⟩
private theorem pr1116229 : PrimeCertificate 1116229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv167,pv557]) (by decide +kernel)
def pv1116229 : PrimeValue := ⟨1116229, pr1116229⟩
private theorem pr1116289 : PrimeCertificate 1116289 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv19]) (by decide +kernel)
def pv1116289 : PrimeValue := ⟨1116289, pr1116289⟩
private theorem pr1116319 : PrimeCertificate 1116319 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv3797]) (by decide +kernel)
def pv1116319 : PrimeValue := ⟨1116319, pr1116319⟩
private theorem pr1116523 : PrimeCertificate 1116523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv5639]) (by decide +kernel)
def pv1116523 : PrimeValue := ⟨1116523, pr1116523⟩
private theorem pr1117027 : PrimeCertificate 1117027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv62057]) (by decide +kernel)
def pv1117027 : PrimeValue := ⟨1117027, pr1117027⟩
private theorem pr1117117 : PrimeCertificate 1117117 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv7,pv11,pv13,pv31]) (by decide +kernel)
def pv1117117 : PrimeValue := ⟨1117117, pr1117117⟩
private theorem pr1117153 : PrimeCertificate 1117153 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv431]) (by decide +kernel)
def pv1117153 : PrimeValue := ⟨1117153, pr1117153⟩
private theorem pr1117603 : PrimeCertificate 1117603 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv2141]) (by decide +kernel)
def pv1117603 : PrimeValue := ⟨1117603, pr1117603⟩
private theorem pr1117939 : PrimeCertificate 1117939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv8101]) (by decide +kernel)
def pv1117939 : PrimeValue := ⟨1117939, pr1117939⟩
private theorem pr1118197 : PrimeCertificate 1118197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv89,pv349]) (by decide +kernel)
def pv1118197 : PrimeValue := ⟨1118197, pr1118197⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
