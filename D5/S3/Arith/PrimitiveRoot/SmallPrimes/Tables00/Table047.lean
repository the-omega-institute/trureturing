/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table047
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table047.pv129263
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table006
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table009
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table025
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table026

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr129263 : PrimeCertificate 129263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv1319]) (by decide +kernel)
def pv129263 : PrimeValue := ⟨129263, pr129263⟩
private theorem pr129281 : PrimeCertificate 129281 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv101]) (by decide +kernel)
def pv129281 : PrimeValue := ⟨129281, pr129281⟩
private theorem pr129287 : PrimeCertificate 129287 :=
  certifyPrime (q := pv5) (ls := [pv2,pv127,pv509]) (by decide +kernel)
def pv129287 : PrimeValue := ⟨129287, pr129287⟩
private theorem pr129293 : PrimeCertificate 129293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv32323]) (by decide +kernel)
def pv129293 : PrimeValue := ⟨129293, pr129293⟩
private theorem pr129313 : PrimeCertificate 129313 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv449]) (by decide +kernel)
def pv129313 : PrimeValue := ⟨129313, pr129313⟩
private theorem pr129341 : PrimeCertificate 129341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29,pv223]) (by decide +kernel)
def pv129341 : PrimeValue := ⟨129341, pr129341⟩
private theorem pr129347 : PrimeCertificate 129347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv9239]) (by decide +kernel)
def pv129347 : PrimeValue := ⟨129347, pr129347⟩
private theorem pr129361 : PrimeCertificate 129361 :=
  certifyPrime (q := pv53) (ls := [pv2,pv3,pv5,pv7,pv11]) (by decide +kernel)
def pv129361 : PrimeValue := ⟨129361, pr129361⟩
private theorem pr129379 : PrimeCertificate 129379 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv21563]) (by decide +kernel)
def pv129379 : PrimeValue := ⟨129379, pr129379⟩
private theorem pr129401 : PrimeCertificate 129401 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv647]) (by decide +kernel)
def pv129401 : PrimeValue := ⟨129401, pr129401⟩
private theorem pr129403 : PrimeCertificate 129403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv79]) (by decide +kernel)
def pv129403 : PrimeValue := ⟨129403, pr129403⟩
private theorem pr129419 : PrimeCertificate 129419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv64709]) (by decide +kernel)
def pv129419 : PrimeValue := ⟨129419, pr129419⟩
private theorem pr129443 : PrimeCertificate 129443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv1061]) (by decide +kernel)
def pv129443 : PrimeValue := ⟨129443, pr129443⟩
private theorem pr129449 : PrimeCertificate 129449 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv1471]) (by decide +kernel)
def pv129449 : PrimeValue := ⟨129449, pr129449⟩
private theorem pr129457 : PrimeCertificate 129457 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv29,pv31]) (by decide +kernel)
def pv129457 : PrimeValue := ⟨129457, pr129457⟩
private theorem pr129461 : PrimeCertificate 129461 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv6473]) (by decide +kernel)
def pv129461 : PrimeValue := ⟨129461, pr129461⟩
private theorem pr129469 : PrimeCertificate 129469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv10789]) (by decide +kernel)
def pv129469 : PrimeValue := ⟨129469, pr129469⟩
private theorem pr129491 : PrimeCertificate 129491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv563]) (by decide +kernel)
def pv129491 : PrimeValue := ⟨129491, pr129491⟩
private theorem pr129497 : PrimeCertificate 129497 :=
  certifyPrime (q := pv3) (ls := [pv2,pv16187]) (by decide +kernel)
def pv129497 : PrimeValue := ⟨129497, pr129497⟩
private theorem pr129509 : PrimeCertificate 129509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv32377]) (by decide +kernel)
def pv129509 : PrimeValue := ⟨129509, pr129509⟩
private theorem pr129517 : PrimeCertificate 129517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv251]) (by decide +kernel)
def pv129517 : PrimeValue := ⟨129517, pr129517⟩
private theorem pr129529 : PrimeCertificate 129529 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv7,pv257]) (by decide +kernel)
def pv129529 : PrimeValue := ⟨129529, pr129529⟩
private theorem pr129533 : PrimeCertificate 129533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv47,pv53]) (by decide +kernel)
def pv129533 : PrimeValue := ⟨129533, pr129533⟩
private theorem pr129539 : PrimeCertificate 129539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv239,pv271]) (by decide +kernel)
def pv129539 : PrimeValue := ⟨129539, pr129539⟩
private theorem pr129553 : PrimeCertificate 129553 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2699]) (by decide +kernel)
def pv129553 : PrimeValue := ⟨129553, pr129553⟩
private theorem pr129581 : PrimeCertificate 129581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv19,pv31]) (by decide +kernel)
def pv129581 : PrimeValue := ⟨129581, pr129581⟩
private theorem pr129587 : PrimeCertificate 129587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv64793]) (by decide +kernel)
def pv129587 : PrimeValue := ⟨129587, pr129587⟩
private theorem pr129589 : PrimeCertificate 129589 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv10799]) (by decide +kernel)
def pv129589 : PrimeValue := ⟨129589, pr129589⟩
private theorem pr129593 : PrimeCertificate 129593 :=
  certifyPrime (q := pv3) (ls := [pv2,pv97,pv167]) (by decide +kernel)
def pv129593 : PrimeValue := ⟨129593, pr129593⟩
private theorem pr129607 : PrimeCertificate 129607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv21601]) (by decide +kernel)
def pv129607 : PrimeValue := ⟨129607, pr129607⟩
private theorem pr129629 : PrimeCertificate 129629 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv1409]) (by decide +kernel)
def pv129629 : PrimeValue := ⟨129629, pr129629⟩
private theorem pr129631 : PrimeCertificate 129631 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv29,pv149]) (by decide +kernel)
def pv129631 : PrimeValue := ⟨129631, pr129631⟩
private theorem pr129641 : PrimeCertificate 129641 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv463]) (by decide +kernel)
def pv129641 : PrimeValue := ⟨129641, pr129641⟩
private theorem pr129643 : PrimeCertificate 129643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv31,pv41]) (by decide +kernel)
def pv129643 : PrimeValue := ⟨129643, pr129643⟩
private theorem pr129671 : PrimeCertificate 129671 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv12967]) (by decide +kernel)
def pv129671 : PrimeValue := ⟨129671, pr129671⟩
private theorem pr129707 : PrimeCertificate 129707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv64853]) (by decide +kernel)
def pv129707 : PrimeValue := ⟨129707, pr129707⟩
private theorem pr129719 : PrimeCertificate 129719 :=
  certifyPrime (q := pv7) (ls := [pv2,pv79,pv821]) (by decide +kernel)
def pv129719 : PrimeValue := ⟨129719, pr129719⟩
private theorem pr129733 : PrimeCertificate 129733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv569]) (by decide +kernel)
def pv129733 : PrimeValue := ⟨129733, pr129733⟩
private theorem pr129737 : PrimeCertificate 129737 :=
  certifyPrime (q := pv3) (ls := [pv2,pv16217]) (by decide +kernel)
def pv129737 : PrimeValue := ⟨129737, pr129737⟩
private theorem pr129749 : PrimeCertificate 129749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv163,pv199]) (by decide +kernel)
def pv129749 : PrimeValue := ⟨129749, pr129749⟩
private theorem pr129757 : PrimeCertificate 129757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv983]) (by decide +kernel)
def pv129757 : PrimeValue := ⟨129757, pr129757⟩
private theorem pr129763 : PrimeCertificate 129763 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv89]) (by decide +kernel)
def pv129763 : PrimeValue := ⟨129763, pr129763⟩
private theorem pr129769 : PrimeCertificate 129769 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5407]) (by decide +kernel)
def pv129769 : PrimeValue := ⟨129769, pr129769⟩
private theorem pr129793 : PrimeCertificate 129793 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv129793 : PrimeValue := ⟨129793, pr129793⟩
private theorem pr129803 : PrimeCertificate 129803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv64901]) (by decide +kernel)
def pv129803 : PrimeValue := ⟨129803, pr129803⟩
private theorem pr129853 : PrimeCertificate 129853 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3607]) (by decide +kernel)
def pv129853 : PrimeValue := ⟨129853, pr129853⟩
private theorem pr129887 : PrimeCertificate 129887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv101,pv643]) (by decide +kernel)
def pv129887 : PrimeValue := ⟨129887, pr129887⟩
private theorem pr129893 : PrimeCertificate 129893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv4639]) (by decide +kernel)
def pv129893 : PrimeValue := ⟨129893, pr129893⟩
private theorem pr129901 : PrimeCertificate 129901 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv433]) (by decide +kernel)
def pv129901 : PrimeValue := ⟨129901, pr129901⟩
private theorem pr129917 : PrimeCertificate 129917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv32479]) (by decide +kernel)
def pv129917 : PrimeValue := ⟨129917, pr129917⟩
private theorem pr129919 : PrimeCertificate 129919 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv59,pv367]) (by decide +kernel)
def pv129919 : PrimeValue := ⟨129919, pr129919⟩
private theorem pr129937 : PrimeCertificate 129937 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv2707]) (by decide +kernel)
def pv129937 : PrimeValue := ⟨129937, pr129937⟩
private theorem pr129953 : PrimeCertificate 129953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv131]) (by decide +kernel)
def pv129953 : PrimeValue := ⟨129953, pr129953⟩
private theorem pr129959 : PrimeCertificate 129959 :=
  certifyPrime (q := pv7) (ls := [pv2,pv181,pv359]) (by decide +kernel)
def pv129959 : PrimeValue := ⟨129959, pr129959⟩
private theorem pr129971 : PrimeCertificate 129971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41,pv317]) (by decide +kernel)
def pv129971 : PrimeValue := ⟨129971, pr129971⟩
private theorem pr130003 : PrimeCertificate 130003 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv47,pv461]) (by decide +kernel)
def pv130003 : PrimeValue := ⟨130003, pr130003⟩
private theorem pr130021 : PrimeCertificate 130021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv197]) (by decide +kernel)
def pv130021 : PrimeValue := ⟨130021, pr130021⟩
private theorem pr130027 : PrimeCertificate 130027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv1667]) (by decide +kernel)
def pv130027 : PrimeValue := ⟨130027, pr130027⟩
private theorem pr130043 : PrimeCertificate 130043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv23,pv257]) (by decide +kernel)
def pv130043 : PrimeValue := ⟨130043, pr130043⟩
private theorem pr130051 : PrimeCertificate 130051 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv130051 : PrimeValue := ⟨130051, pr130051⟩
private theorem pr130057 : PrimeCertificate 130057 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv5419]) (by decide +kernel)
def pv130057 : PrimeValue := ⟨130057, pr130057⟩
private theorem pr130069 : PrimeCertificate 130069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3613]) (by decide +kernel)
def pv130069 : PrimeValue := ⟨130069, pr130069⟩
private theorem pr130073 : PrimeCertificate 130073 :=
  certifyPrime (q := pv3) (ls := [pv2,pv71,pv229]) (by decide +kernel)
def pv130073 : PrimeValue := ⟨130073, pr130073⟩
private theorem pr130079 : PrimeCertificate 130079 :=
  certifyPrime (q := pv11) (ls := [pv2,pv13,pv5003]) (by decide +kernel)
def pv130079 : PrimeValue := ⟨130079, pr130079⟩
private theorem pr130087 : PrimeCertificate 130087 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv73]) (by decide +kernel)
def pv130087 : PrimeValue := ⟨130087, pr130087⟩
private theorem pr130121 : PrimeCertificate 130121 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv3253]) (by decide +kernel)
def pv130121 : PrimeValue := ⟨130121, pr130121⟩
private theorem pr130127 : PrimeCertificate 130127 :=
  certifyPrime (q := pv5) (ls := [pv2,pv65063]) (by decide +kernel)
def pv130127 : PrimeValue := ⟨130127, pr130127⟩
private theorem pr130147 : PrimeCertificate 130147 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv109,pv199]) (by decide +kernel)
def pv130147 : PrimeValue := ⟨130147, pr130147⟩
private theorem pr130171 : PrimeCertificate 130171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv4339]) (by decide +kernel)
def pv130171 : PrimeValue := ⟨130171, pr130171⟩
private theorem pr130183 : PrimeCertificate 130183 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv1669]) (by decide +kernel)
def pv130183 : PrimeValue := ⟨130183, pr130183⟩
private theorem pr130199 : PrimeCertificate 130199 :=
  certifyPrime (q := pv11) (ls := [pv2,pv65099]) (by decide +kernel)
def pv130199 : PrimeValue := ⟨130199, pr130199⟩
private theorem pr130201 : PrimeCertificate 130201 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv31]) (by decide +kernel)
def pv130201 : PrimeValue := ⟨130201, pr130201⟩
private theorem pr130211 : PrimeCertificate 130211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29,pv449]) (by decide +kernel)
def pv130211 : PrimeValue := ⟨130211, pr130211⟩
private theorem pr130223 : PrimeCertificate 130223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv65111]) (by decide +kernel)
def pv130223 : PrimeValue := ⟨130223, pr130223⟩
private theorem pr130241 : PrimeCertificate 130241 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv37]) (by decide +kernel)
def pv130241 : PrimeValue := ⟨130241, pr130241⟩
private theorem pr130253 : PrimeCertificate 130253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv32563]) (by decide +kernel)
def pv130253 : PrimeValue := ⟨130253, pr130253⟩
private theorem pr130259 : PrimeCertificate 130259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv65129]) (by decide +kernel)
def pv130259 : PrimeValue := ⟨130259, pr130259⟩
private theorem pr130261 : PrimeCertificate 130261 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv13,pv167]) (by decide +kernel)
def pv130261 : PrimeValue := ⟨130261, pr130261⟩
private theorem pr130267 : PrimeCertificate 130267 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7237]) (by decide +kernel)
def pv130267 : PrimeValue := ⟨130267, pr130267⟩
private theorem pr130279 : PrimeCertificate 130279 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv21713]) (by decide +kernel)
def pv130279 : PrimeValue := ⟨130279, pr130279⟩
private theorem pr130303 : PrimeCertificate 130303 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv127]) (by decide +kernel)
def pv130303 : PrimeValue := ⟨130303, pr130303⟩
private theorem pr130337 : PrimeCertificate 130337 :=
  certifyPrime (q := pv3) (ls := [pv2,pv4073]) (by decide +kernel)
def pv130337 : PrimeValue := ⟨130337, pr130337⟩
private theorem pr130343 : PrimeCertificate 130343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv65171]) (by decide +kernel)
def pv130343 : PrimeValue := ⟨130343, pr130343⟩
private theorem pr130349 : PrimeCertificate 130349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv32587]) (by decide +kernel)
def pv130349 : PrimeValue := ⟨130349, pr130349⟩
private theorem pr130367 : PrimeCertificate 130367 :=
  certifyPrime (q := pv5) (ls := [pv2,pv65183]) (by decide +kernel)
def pv130367 : PrimeValue := ⟨130367, pr130367⟩
private theorem pr130369 : PrimeCertificate 130369 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv97]) (by decide +kernel)
def pv130369 : PrimeValue := ⟨130369, pr130369⟩
private theorem pr130379 : PrimeCertificate 130379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv47,pv73]) (by decide +kernel)
def pv130379 : PrimeValue := ⟨130379, pr130379⟩
private theorem pr130399 : PrimeCertificate 130399 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv103,pv211]) (by decide +kernel)
def pv130399 : PrimeValue := ⟨130399, pr130399⟩
private theorem pr130409 : PrimeCertificate 130409 :=
  certifyPrime (q := pv3) (ls := [pv2,pv16301]) (by decide +kernel)
def pv130409 : PrimeValue := ⟨130409, pr130409⟩
private theorem pr130411 : PrimeCertificate 130411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv23]) (by decide +kernel)
def pv130411 : PrimeValue := ⟨130411, pr130411⟩
private theorem pr130423 : PrimeCertificate 130423 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv21737]) (by decide +kernel)
def pv130423 : PrimeValue := ⟨130423, pr130423⟩
private theorem pr130439 : PrimeCertificate 130439 :=
  certifyPrime (q := pv11) (ls := [pv2,pv7,pv11]) (by decide +kernel)
def pv130439 : PrimeValue := ⟨130439, pr130439⟩
private theorem pr130447 : PrimeCertificate 130447 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7247]) (by decide +kernel)
def pv130447 : PrimeValue := ⟨130447, pr130447⟩
private theorem pr130457 : PrimeCertificate 130457 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv709]) (by decide +kernel)
def pv130457 : PrimeValue := ⟨130457, pr130457⟩
private theorem pr130469 : PrimeCertificate 130469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv193]) (by decide +kernel)
def pv130469 : PrimeValue := ⟨130469, pr130469⟩
private theorem pr130483 : PrimeCertificate 130483 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv659]) (by decide +kernel)
def pv130483 : PrimeValue := ⟨130483, pr130483⟩
private theorem pr130489 : PrimeCertificate 130489 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5437]) (by decide +kernel)
def pv130489 : PrimeValue := ⟨130489, pr130489⟩
private theorem pr130513 : PrimeCertificate 130513 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2719]) (by decide +kernel)
def pv130513 : PrimeValue := ⟨130513, pr130513⟩
private theorem pr130517 : PrimeCertificate 130517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67,pv487]) (by decide +kernel)
def pv130517 : PrimeValue := ⟨130517, pr130517⟩
private theorem pr130523 : PrimeCertificate 130523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv9323]) (by decide +kernel)
def pv130523 : PrimeValue := ⟨130523, pr130523⟩
private theorem pr130531 : PrimeCertificate 130531 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv19,pv229]) (by decide +kernel)
def pv130531 : PrimeValue := ⟨130531, pr130531⟩
private theorem pr130547 : PrimeCertificate 130547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv5021]) (by decide +kernel)
def pv130547 : PrimeValue := ⟨130547, pr130547⟩
private theorem pr130553 : PrimeCertificate 130553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv16319]) (by decide +kernel)
def pv130553 : PrimeValue := ⟨130553, pr130553⟩
private theorem pr130579 : PrimeCertificate 130579 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv3109]) (by decide +kernel)
def pv130579 : PrimeValue := ⟨130579, pr130579⟩
private theorem pr130619 : PrimeCertificate 130619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv65309]) (by decide +kernel)
def pv130619 : PrimeValue := ⟨130619, pr130619⟩
private theorem pr130631 : PrimeCertificate 130631 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13063]) (by decide +kernel)
def pv130631 : PrimeValue := ⟨130631, pr130631⟩
private theorem pr130633 : PrimeCertificate 130633 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5443]) (by decide +kernel)
def pv130633 : PrimeValue := ⟨130633, pr130633⟩
private theorem pr130639 : PrimeCertificate 130639 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv21773]) (by decide +kernel)
def pv130639 : PrimeValue := ⟨130639, pr130639⟩
private theorem pr130649 : PrimeCertificate 130649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv2333]) (by decide +kernel)
def pv130649 : PrimeValue := ⟨130649, pr130649⟩
private theorem pr130657 : PrimeCertificate 130657 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1361]) (by decide +kernel)
def pv130657 : PrimeValue := ⟨130657, pr130657⟩
private theorem pr130681 : PrimeCertificate 130681 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv130681 : PrimeValue := ⟨130681, pr130681⟩
private theorem pr130687 : PrimeCertificate 130687 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv947]) (by decide +kernel)
def pv130687 : PrimeValue := ⟨130687, pr130687⟩
private theorem pr130693 : PrimeCertificate 130693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv10891]) (by decide +kernel)
def pv130693 : PrimeValue := ⟨130693, pr130693⟩
private theorem pr130699 : PrimeCertificate 130699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53,pv137]) (by decide +kernel)
def pv130699 : PrimeValue := ⟨130699, pr130699⟩
private theorem pr130783 : PrimeCertificate 130783 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv71,pv307]) (by decide +kernel)
def pv130783 : PrimeValue := ⟨130783, pr130783⟩
private theorem pr130787 : PrimeCertificate 130787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv65393]) (by decide +kernel)
def pv130787 : PrimeValue := ⟨130787, pr130787⟩
private theorem pr130807 : PrimeCertificate 130807 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv43]) (by decide +kernel)
def pv130807 : PrimeValue := ⟨130807, pr130807⟩
private theorem pr130811 : PrimeCertificate 130811 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv103,pv127]) (by decide +kernel)
def pv130811 : PrimeValue := ⟨130811, pr130811⟩
private theorem pr130829 : PrimeCertificate 130829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv32707]) (by decide +kernel)
def pv130829 : PrimeValue := ⟨130829, pr130829⟩
private theorem pr130841 : PrimeCertificate 130841 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv3271]) (by decide +kernel)
def pv130841 : PrimeValue := ⟨130841, pr130841⟩
private theorem pr130843 : PrimeCertificate 130843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv2423]) (by decide +kernel)
def pv130843 : PrimeValue := ⟨130843, pr130843⟩
private theorem pr130873 : PrimeCertificate 130873 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv19,pv41]) (by decide +kernel)
def pv130873 : PrimeValue := ⟨130873, pr130873⟩
private theorem pr130927 : PrimeCertificate 130927 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv21821]) (by decide +kernel)
def pv130927 : PrimeValue := ⟨130927, pr130927⟩
private theorem pr130957 : PrimeCertificate 130957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1559]) (by decide +kernel)
def pv130957 : PrimeValue := ⟨130957, pr130957⟩
private theorem pr130969 : PrimeCertificate 130969 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv17,pv107]) (by decide +kernel)
def pv130969 : PrimeValue := ⟨130969, pr130969⟩
private theorem pr130973 : PrimeCertificate 130973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv137,pv239]) (by decide +kernel)
def pv130973 : PrimeValue := ⟨130973, pr130973⟩
private theorem pr130981 : PrimeCertificate 130981 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv37,pv59]) (by decide +kernel)
def pv130981 : PrimeValue := ⟨130981, pr130981⟩
private theorem pr130987 : PrimeCertificate 130987 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv383]) (by decide +kernel)
def pv130987 : PrimeValue := ⟨130987, pr130987⟩
private theorem pr131009 : PrimeCertificate 131009 :=
  certifyPrime (q := pv11) (ls := [pv2,pv23,pv89]) (by decide +kernel)
def pv131009 : PrimeValue := ⟨131009, pr131009⟩
private theorem pr131041 : PrimeCertificate 131041 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv7,pv13]) (by decide +kernel)
def pv131041 : PrimeValue := ⟨131041, pr131041⟩
private theorem pr131059 : PrimeCertificate 131059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv809]) (by decide +kernel)
def pv131059 : PrimeValue := ⟨131059, pr131059⟩
private theorem pr131063 : PrimeCertificate 131063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv3449]) (by decide +kernel)
def pv131063 : PrimeValue := ⟨131063, pr131063⟩
private theorem pr131071 : PrimeCertificate 131071 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv17,pv257]) (by decide +kernel)
def pv131071 : PrimeValue := ⟨131071, pr131071⟩
private theorem pr131101 : PrimeCertificate 131101 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv19,pv23]) (by decide +kernel)
def pv131101 : PrimeValue := ⟨131101, pr131101⟩
private theorem pr131111 : PrimeCertificate 131111 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv1873]) (by decide +kernel)
def pv131111 : PrimeValue := ⟨131111, pr131111⟩
private theorem pr131113 : PrimeCertificate 131113 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv607]) (by decide +kernel)
def pv131113 : PrimeValue := ⟨131113, pr131113⟩
private theorem pr131129 : PrimeCertificate 131129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv443]) (by decide +kernel)
def pv131129 : PrimeValue := ⟨131129, pr131129⟩
private theorem pr131143 : PrimeCertificate 131143 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv1987]) (by decide +kernel)
def pv131143 : PrimeValue := ⟨131143, pr131143⟩
private theorem pr131149 : PrimeCertificate 131149 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv3643]) (by decide +kernel)
def pv131149 : PrimeValue := ⟨131149, pr131149⟩
private theorem pr131171 : PrimeCertificate 131171 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv13,pv1009]) (by decide +kernel)
def pv131171 : PrimeValue := ⟨131171, pr131171⟩
private theorem pr131203 : PrimeCertificate 131203 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37,pv197]) (by decide +kernel)
def pv131203 : PrimeValue := ⟨131203, pr131203⟩
private theorem pr131213 : PrimeCertificate 131213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv32803]) (by decide +kernel)
def pv131213 : PrimeValue := ⟨131213, pr131213⟩
private theorem pr131221 : PrimeCertificate 131221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv131221 : PrimeValue := ⟨131221, pr131221⟩
private theorem pr131231 : PrimeCertificate 131231 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv1193]) (by decide +kernel)
def pv131231 : PrimeValue := ⟨131231, pr131231⟩
private theorem pr131249 : PrimeCertificate 131249 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv631]) (by decide +kernel)
def pv131249 : PrimeValue := ⟨131249, pr131249⟩
private theorem pr131251 : PrimeCertificate 131251 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv131251 : PrimeValue := ⟨131251, pr131251⟩
private theorem pr131267 : PrimeCertificate 131267 :=
  certifyPrime (q := pv2) (ls := [pv2,pv65633]) (by decide +kernel)
def pv131267 : PrimeValue := ⟨131267, pr131267⟩
private theorem pr131293 : PrimeCertificate 131293 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv521]) (by decide +kernel)
def pv131293 : PrimeValue := ⟨131293, pr131293⟩
private theorem pr131297 : PrimeCertificate 131297 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv373]) (by decide +kernel)
def pv131297 : PrimeValue := ⟨131297, pr131297⟩
private theorem pr131303 : PrimeCertificate 131303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv65651]) (by decide +kernel)
def pv131303 : PrimeValue := ⟨131303, pr131303⟩
private theorem pr131311 : PrimeCertificate 131311 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv1459]) (by decide +kernel)
def pv131311 : PrimeValue := ⟨131311, pr131311⟩
private theorem pr131317 : PrimeCertificate 131317 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv31,pv353]) (by decide +kernel)
def pv131317 : PrimeValue := ⟨131317, pr131317⟩
private theorem pr131321 : PrimeCertificate 131321 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv67]) (by decide +kernel)
def pv131321 : PrimeValue := ⟨131321, pr131321⟩
private theorem pr131357 : PrimeCertificate 131357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv32839]) (by decide +kernel)
def pv131357 : PrimeValue := ⟨131357, pr131357⟩
private theorem pr131363 : PrimeCertificate 131363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv853]) (by decide +kernel)
def pv131363 : PrimeValue := ⟨131363, pr131363⟩
private theorem pr131371 : PrimeCertificate 131371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv29,pv151]) (by decide +kernel)
def pv131371 : PrimeValue := ⟨131371, pr131371⟩
private theorem pr131381 : PrimeCertificate 131381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv6569]) (by decide +kernel)
def pv131381 : PrimeValue := ⟨131381, pr131381⟩
private theorem pr131413 : PrimeCertificate 131413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv233]) (by decide +kernel)
def pv131413 : PrimeValue := ⟨131413, pr131413⟩
private theorem pr131431 : PrimeCertificate 131431 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv13,pv337]) (by decide +kernel)
def pv131431 : PrimeValue := ⟨131431, pr131431⟩
private theorem pr131437 : PrimeCertificate 131437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1217]) (by decide +kernel)
def pv131437 : PrimeValue := ⟨131437, pr131437⟩
private theorem pr131441 : PrimeCertificate 131441 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv31,pv53]) (by decide +kernel)
def pv131441 : PrimeValue := ⟨131441, pr131441⟩
private theorem pr131447 : PrimeCertificate 131447 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv41,pv229]) (by decide +kernel)
def pv131447 : PrimeValue := ⟨131447, pr131447⟩
private theorem pr131449 : PrimeCertificate 131449 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5477]) (by decide +kernel)
def pv131449 : PrimeValue := ⟨131449, pr131449⟩
private theorem pr131477 : PrimeCertificate 131477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv32869]) (by decide +kernel)
def pv131477 : PrimeValue := ⟨131477, pr131477⟩
private theorem pr131489 : PrimeCertificate 131489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv587]) (by decide +kernel)
def pv131489 : PrimeValue := ⟨131489, pr131489⟩
private theorem pr131497 : PrimeCertificate 131497 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv5479]) (by decide +kernel)
def pv131497 : PrimeValue := ⟨131497, pr131497⟩
private theorem pr131501 : PrimeCertificate 131501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv263]) (by decide +kernel)
def pv131501 : PrimeValue := ⟨131501, pr131501⟩
private theorem pr131519 : PrimeCertificate 131519 :=
  certifyPrime (q := pv13) (ls := [pv2,pv19,pv3461]) (by decide +kernel)
def pv131519 : PrimeValue := ⟨131519, pr131519⟩
private theorem pr131543 : PrimeCertificate 131543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv89,pv739]) (by decide +kernel)
def pv131543 : PrimeValue := ⟨131543, pr131543⟩
private theorem pr131561 : PrimeCertificate 131561 :=
  certifyPrime (q := pv29) (ls := [pv2,pv5,pv11,pv13,pv23]) (by decide +kernel)
def pv131561 : PrimeValue := ⟨131561, pr131561⟩
private theorem pr131591 : PrimeCertificate 131591 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv13159]) (by decide +kernel)
def pv131591 : PrimeValue := ⟨131591, pr131591⟩
private theorem pr131627 : PrimeCertificate 131627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv31,pv193]) (by decide +kernel)
def pv131627 : PrimeValue := ⟨131627, pr131627⟩
private theorem pr131639 : PrimeCertificate 131639 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv61,pv83]) (by decide +kernel)
def pv131639 : PrimeValue := ⟨131639, pr131639⟩
private theorem pr131641 : PrimeCertificate 131641 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv1097]) (by decide +kernel)
def pv131641 : PrimeValue := ⟨131641, pr131641⟩
private theorem pr131671 : PrimeCertificate 131671 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv11,pv19]) (by decide +kernel)
def pv131671 : PrimeValue := ⟨131671, pr131671⟩
private theorem pr131687 : PrimeCertificate 131687 :=
  certifyPrime (q := pv5) (ls := [pv2,pv65843]) (by decide +kernel)
def pv131687 : PrimeValue := ⟨131687, pr131687⟩
private theorem pr131701 : PrimeCertificate 131701 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv439]) (by decide +kernel)
def pv131701 : PrimeValue := ⟨131701, pr131701⟩
private theorem pr131707 : PrimeCertificate 131707 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv271]) (by decide +kernel)
def pv131707 : PrimeValue := ⟨131707, pr131707⟩
private theorem pr131711 : PrimeCertificate 131711 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv13171]) (by decide +kernel)
def pv131711 : PrimeValue := ⟨131711, pr131711⟩
private theorem pr131713 : PrimeCertificate 131713 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv131713 : PrimeValue := ⟨131713, pr131713⟩
private theorem pr131731 : PrimeCertificate 131731 :=
  certifyPrime (q := pv47) (ls := [pv2,pv3,pv5,pv4391]) (by decide +kernel)
def pv131731 : PrimeValue := ⟨131731, pr131731⟩
private theorem pr131743 : PrimeCertificate 131743 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv563]) (by decide +kernel)
def pv131743 : PrimeValue := ⟨131743, pr131743⟩
private theorem pr131749 : PrimeCertificate 131749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv10979]) (by decide +kernel)
def pv131749 : PrimeValue := ⟨131749, pr131749⟩
private theorem pr131759 : PrimeCertificate 131759 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv53,pv113]) (by decide +kernel)
def pv131759 : PrimeValue := ⟨131759, pr131759⟩
private theorem pr131771 : PrimeCertificate 131771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13177]) (by decide +kernel)
def pv131771 : PrimeValue := ⟨131771, pr131771⟩
private theorem pr131779 : PrimeCertificate 131779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7321]) (by decide +kernel)
def pv131779 : PrimeValue := ⟨131779, pr131779⟩
private theorem pr131783 : PrimeCertificate 131783 :=
  certifyPrime (q := pv11) (ls := [pv2,pv7,pv9413]) (by decide +kernel)
def pv131783 : PrimeValue := ⟨131783, pr131783⟩
private theorem pr131797 : PrimeCertificate 131797 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv523]) (by decide +kernel)
def pv131797 : PrimeValue := ⟨131797, pr131797⟩
private theorem pr131837 : PrimeCertificate 131837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv1433]) (by decide +kernel)
def pv131837 : PrimeValue := ⟨131837, pr131837⟩
private theorem pr131839 : PrimeCertificate 131839 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv43,pv73]) (by decide +kernel)
def pv131839 : PrimeValue := ⟨131839, pr131839⟩
private theorem pr131849 : PrimeCertificate 131849 :=
  certifyPrime (q := pv3) (ls := [pv2,pv16481]) (by decide +kernel)
def pv131849 : PrimeValue := ⟨131849, pr131849⟩
private theorem pr131861 : PrimeCertificate 131861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv347]) (by decide +kernel)
def pv131861 : PrimeValue := ⟨131861, pr131861⟩
private theorem pr131891 : PrimeCertificate 131891 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv109]) (by decide +kernel)
def pv131891 : PrimeValue := ⟨131891, pr131891⟩
private theorem pr131893 : PrimeCertificate 131893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv379]) (by decide +kernel)
def pv131893 : PrimeValue := ⟨131893, pr131893⟩
private theorem pr131899 : PrimeCertificate 131899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv19,pv89]) (by decide +kernel)
def pv131899 : PrimeValue := ⟨131899, pr131899⟩
private theorem pr131909 : PrimeCertificate 131909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv673]) (by decide +kernel)
def pv131909 : PrimeValue := ⟨131909, pr131909⟩
private theorem pr131927 : PrimeCertificate 131927 :=
  certifyPrime (q := pv5) (ls := [pv2,pv65963]) (by decide +kernel)
def pv131927 : PrimeValue := ⟨131927, pr131927⟩
private theorem pr131933 : PrimeCertificate 131933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv32983]) (by decide +kernel)
def pv131933 : PrimeValue := ⟨131933, pr131933⟩
private theorem pr131939 : PrimeCertificate 131939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv1609]) (by decide +kernel)
def pv131939 : PrimeValue := ⟨131939, pr131939⟩
private theorem pr131941 : PrimeCertificate 131941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv733]) (by decide +kernel)
def pv131941 : PrimeValue := ⟨131941, pr131941⟩
private theorem pr131947 : PrimeCertificate 131947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv21991]) (by decide +kernel)
def pv131947 : PrimeValue := ⟨131947, pr131947⟩
private theorem pr131959 : PrimeCertificate 131959 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7331]) (by decide +kernel)
def pv131959 : PrimeValue := ⟨131959, pr131959⟩
private theorem pr131969 : PrimeCertificate 131969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1031]) (by decide +kernel)
def pv131969 : PrimeValue := ⟨131969, pr131969⟩
private theorem pr132001 : PrimeCertificate 132001 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv132001 : PrimeValue := ⟨132001, pr132001⟩
private theorem pr132019 : PrimeCertificate 132019 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv22003]) (by decide +kernel)
def pv132019 : PrimeValue := ⟨132019, pr132019⟩
private theorem pr132047 : PrimeCertificate 132047 :=
  certifyPrime (q := pv5) (ls := [pv2,pv103,pv641]) (by decide +kernel)
def pv132047 : PrimeValue := ⟨132047, pr132047⟩
private theorem pr132049 : PrimeCertificate 132049 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv7,pv131]) (by decide +kernel)
def pv132049 : PrimeValue := ⟨132049, pr132049⟩
private theorem pr132059 : PrimeCertificate 132059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv66029]) (by decide +kernel)
def pv132059 : PrimeValue := ⟨132059, pr132059⟩
private theorem pr132071 : PrimeCertificate 132071 :=
  certifyPrime (q := pv37) (ls := [pv2,pv5,pv47,pv281]) (by decide +kernel)
def pv132071 : PrimeValue := ⟨132071, pr132071⟩
private theorem pr132103 : PrimeCertificate 132103 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41,pv179]) (by decide +kernel)
def pv132103 : PrimeValue := ⟨132103, pr132103⟩
private theorem pr132109 : PrimeCertificate 132109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv101,pv109]) (by decide +kernel)
def pv132109 : PrimeValue := ⟨132109, pr132109⟩
private theorem pr132113 : PrimeCertificate 132113 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv359]) (by decide +kernel)
def pv132113 : PrimeValue := ⟨132113, pr132113⟩
private theorem pr132137 : PrimeCertificate 132137 :=
  certifyPrime (q := pv3) (ls := [pv2,pv83,pv199]) (by decide +kernel)
def pv132137 : PrimeValue := ⟨132137, pr132137⟩
private theorem pr132151 : PrimeCertificate 132151 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv881]) (by decide +kernel)
def pv132151 : PrimeValue := ⟨132151, pr132151⟩
private theorem pr132157 : PrimeCertificate 132157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3671]) (by decide +kernel)
def pv132157 : PrimeValue := ⟨132157, pr132157⟩
private theorem pr132173 : PrimeCertificate 132173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv173,pv191]) (by decide +kernel)
def pv132173 : PrimeValue := ⟨132173, pr132173⟩
private theorem pr132199 : PrimeCertificate 132199 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv2003]) (by decide +kernel)
def pv132199 : PrimeValue := ⟨132199, pr132199⟩
private theorem pr132229 : PrimeCertificate 132229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3673]) (by decide +kernel)
def pv132229 : PrimeValue := ⟨132229, pr132229⟩
private theorem pr132233 : PrimeCertificate 132233 :=
  certifyPrime (q := pv3) (ls := [pv2,pv16529]) (by decide +kernel)
def pv132233 : PrimeValue := ⟨132233, pr132233⟩
private theorem pr132241 : PrimeCertificate 132241 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv19,pv29]) (by decide +kernel)
def pv132241 : PrimeValue := ⟨132241, pr132241⟩
private theorem pr132247 : PrimeCertificate 132247 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31,pv79]) (by decide +kernel)
def pv132247 : PrimeValue := ⟨132247, pr132247⟩
private theorem pr132257 : PrimeCertificate 132257 :=
  certifyPrime (q := pv3) (ls := [pv2,pv4133]) (by decide +kernel)
def pv132257 : PrimeValue := ⟨132257, pr132257⟩
private theorem pr132263 : PrimeCertificate 132263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv5087]) (by decide +kernel)
def pv132263 : PrimeValue := ⟨132263, pr132263⟩
private theorem pr132283 : PrimeCertificate 132283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7349]) (by decide +kernel)
def pv132283 : PrimeValue := ⟨132283, pr132283⟩
private theorem pr132287 : PrimeCertificate 132287 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11,pv859]) (by decide +kernel)
def pv132287 : PrimeValue := ⟨132287, pr132287⟩
private theorem pr132299 : PrimeCertificate 132299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv2281]) (by decide +kernel)
def pv132299 : PrimeValue := ⟨132299, pr132299⟩
private theorem pr132313 : PrimeCertificate 132313 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv37,pv149]) (by decide +kernel)
def pv132313 : PrimeValue := ⟨132313, pr132313⟩
private theorem pr132329 : PrimeCertificate 132329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv17,pv139]) (by decide +kernel)
def pv132329 : PrimeValue := ⟨132329, pr132329⟩
private theorem pr132331 : PrimeCertificate 132331 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv401]) (by decide +kernel)
def pv132331 : PrimeValue := ⟨132331, pr132331⟩
private theorem pr132347 : PrimeCertificate 132347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv66173]) (by decide +kernel)
def pv132347 : PrimeValue := ⟨132347, pr132347⟩
private theorem pr132361 : PrimeCertificate 132361 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv1103]) (by decide +kernel)
def pv132361 : PrimeValue := ⟨132361, pr132361⟩
private theorem pr132367 : PrimeCertificate 132367 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv1697]) (by decide +kernel)
def pv132367 : PrimeValue := ⟨132367, pr132367⟩
private theorem pr132371 : PrimeCertificate 132371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv31,pv61]) (by decide +kernel)
def pv132371 : PrimeValue := ⟨132371, pr132371⟩
private theorem pr132383 : PrimeCertificate 132383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv66191]) (by decide +kernel)
def pv132383 : PrimeValue := ⟨132383, pr132383⟩
private theorem pr132403 : PrimeCertificate 132403 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv22067]) (by decide +kernel)
def pv132403 : PrimeValue := ⟨132403, pr132403⟩
private theorem pr132409 : PrimeCertificate 132409 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv613]) (by decide +kernel)
def pv132409 : PrimeValue := ⟨132409, pr132409⟩
private theorem pr132421 : PrimeCertificate 132421 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv2207]) (by decide +kernel)
def pv132421 : PrimeValue := ⟨132421, pr132421⟩
private theorem pr132437 : PrimeCertificate 132437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv113,pv293]) (by decide +kernel)
def pv132437 : PrimeValue := ⟨132437, pr132437⟩
private theorem pr132439 : PrimeCertificate 132439 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv22073]) (by decide +kernel)
def pv132439 : PrimeValue := ⟨132439, pr132439⟩
private theorem pr132469 : PrimeCertificate 132469 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv19,pv83]) (by decide +kernel)
def pv132469 : PrimeValue := ⟨132469, pr132469⟩
private theorem pr132491 : PrimeCertificate 132491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13249]) (by decide +kernel)
def pv132491 : PrimeValue := ⟨132491, pr132491⟩
private theorem pr132499 : PrimeCertificate 132499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv433]) (by decide +kernel)
def pv132499 : PrimeValue := ⟨132499, pr132499⟩
private theorem pr132511 : PrimeCertificate 132511 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv631]) (by decide +kernel)
def pv132511 : PrimeValue := ⟨132511, pr132511⟩
private theorem pr132523 : PrimeCertificate 132523 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv1699]) (by decide +kernel)
def pv132523 : PrimeValue := ⟨132523, pr132523⟩
private theorem pr132527 : PrimeCertificate 132527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv43,pv67]) (by decide +kernel)
def pv132527 : PrimeValue := ⟨132527, pr132527⟩
private theorem pr132533 : PrimeCertificate 132533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv1949]) (by decide +kernel)
def pv132533 : PrimeValue := ⟨132533, pr132533⟩
private theorem pr132541 : PrimeCertificate 132541 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv47]) (by decide +kernel)
def pv132541 : PrimeValue := ⟨132541, pr132541⟩
private theorem pr132547 : PrimeCertificate 132547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv22091]) (by decide +kernel)
def pv132547 : PrimeValue := ⟨132547, pr132547⟩
private theorem pr132589 : PrimeCertificate 132589 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv29,pv127]) (by decide +kernel)
def pv132589 : PrimeValue := ⟨132589, pr132589⟩
private theorem pr132607 : PrimeCertificate 132607 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv53,pv139]) (by decide +kernel)
def pv132607 : PrimeValue := ⟨132607, pr132607⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
