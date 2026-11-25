/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table097
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table097.pv380441
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table012
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table016
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table025
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table063
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table064

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr380441 : PrimeCertificate 380441 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv9511]) (by decide +kernel)
def pv380441 : PrimeValue := ⟨380441, pr380441⟩
private theorem pr380447 : PrimeCertificate 380447 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv17293]) (by decide +kernel)
def pv380447 : PrimeValue := ⟨380447, pr380447⟩
private theorem pr380453 : PrimeCertificate 380453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv227,pv419]) (by decide +kernel)
def pv380453 : PrimeValue := ⟨380453, pr380453⟩
private theorem pr380461 : PrimeCertificate 380461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv373]) (by decide +kernel)
def pv380461 : PrimeValue := ⟨380461, pr380461⟩
private theorem pr380483 : PrimeCertificate 380483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv103,pv1847]) (by decide +kernel)
def pv380483 : PrimeValue := ⟨380483, pr380483⟩
private theorem pr380503 : PrimeCertificate 380503 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv21139]) (by decide +kernel)
def pv380503 : PrimeValue := ⟨380503, pr380503⟩
private theorem pr380563 : PrimeCertificate 380563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv17,pv41]) (by decide +kernel)
def pv380563 : PrimeValue := ⟨380563, pr380563⟩
private theorem pr380591 : PrimeCertificate 380591 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv5437]) (by decide +kernel)
def pv380591 : PrimeValue := ⟨380591, pr380591⟩
private theorem pr380621 : PrimeCertificate 380621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19031]) (by decide +kernel)
def pv380621 : PrimeValue := ⟨380621, pr380621⟩
private theorem pr380629 : PrimeCertificate 380629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv97,pv109]) (by decide +kernel)
def pv380629 : PrimeValue := ⟨380629, pr380629⟩
private theorem pr380651 : PrimeCertificate 380651 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv23,pv331]) (by decide +kernel)
def pv380651 : PrimeValue := ⟨380651, pr380651⟩
private theorem pr380657 : PrimeCertificate 380657 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv643]) (by decide +kernel)
def pv380657 : PrimeValue := ⟨380657, pr380657⟩
private theorem pr380713 : PrimeCertificate 380713 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv29,pv547]) (by decide +kernel)
def pv380713 : PrimeValue := ⟨380713, pr380713⟩
private theorem pr380729 : PrimeCertificate 380729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv47591]) (by decide +kernel)
def pv380729 : PrimeValue := ⟨380729, pr380729⟩
private theorem pr380777 : PrimeCertificate 380777 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv4327]) (by decide +kernel)
def pv380777 : PrimeValue := ⟨380777, pr380777⟩
private theorem pr380909 : PrimeCertificate 380909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv787]) (by decide +kernel)
def pv380909 : PrimeValue := ⟨380909, pr380909⟩
private theorem pr380951 : PrimeCertificate 380951 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv19,pv401]) (by decide +kernel)
def pv380951 : PrimeValue := ⟨380951, pr380951⟩
private theorem pr380957 : PrimeCertificate 380957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv95239]) (by decide +kernel)
def pv380957 : PrimeValue := ⟨380957, pr380957⟩
private theorem pr380977 : PrimeCertificate 380977 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7937]) (by decide +kernel)
def pv380977 : PrimeValue := ⟨380977, pr380977⟩
private theorem pr381019 : PrimeCertificate 381019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv23,pv251]) (by decide +kernel)
def pv381019 : PrimeValue := ⟨381019, pr381019⟩
private theorem pr381239 : PrimeCertificate 381239 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv13,pv31,pv43]) (by decide +kernel)
def pv381239 : PrimeValue := ⟨381239, pr381239⟩
private theorem pr381289 : PrimeCertificate 381289 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv15887]) (by decide +kernel)
def pv381289 : PrimeValue := ⟨381289, pr381289⟩
private theorem pr381301 : PrimeCertificate 381301 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv31,pv41]) (by decide +kernel)
def pv381301 : PrimeValue := ⟨381301, pr381301⟩
private theorem pr381323 : PrimeCertificate 381323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv5153]) (by decide +kernel)
def pv381323 : PrimeValue := ⟨381323, pr381323⟩
private theorem pr381343 : PrimeCertificate 381343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv4889]) (by decide +kernel)
def pv381343 : PrimeValue := ⟨381343, pr381343⟩
private theorem pr381347 : PrimeCertificate 381347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv27239]) (by decide +kernel)
def pv381347 : PrimeValue := ⟨381347, pr381347⟩
private theorem pr381371 : PrimeCertificate 381371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv3467]) (by decide +kernel)
def pv381371 : PrimeValue := ⟨381371, pr381371⟩
private theorem pr381373 : PrimeCertificate 381373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61,pv521]) (by decide +kernel)
def pv381373 : PrimeValue := ⟨381373, pr381373⟩
private theorem pr381377 : PrimeCertificate 381377 :=
  certifyPrime (q := pv3) (ls := [pv2,pv59,pv101]) (by decide +kernel)
def pv381377 : PrimeValue := ⟨381377, pr381377⟩
private theorem pr381389 : PrimeCertificate 381389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv53,pv257]) (by decide +kernel)
def pv381389 : PrimeValue := ⟨381389, pr381389⟩
private theorem pr381413 : PrimeCertificate 381413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv71,pv79]) (by decide +kernel)
def pv381413 : PrimeValue := ⟨381413, pr381413⟩
private theorem pr381461 : PrimeCertificate 381461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19073]) (by decide +kernel)
def pv381461 : PrimeValue := ⟨381461, pr381461⟩
private theorem pr381481 : PrimeCertificate 381481 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv11,pv17]) (by decide +kernel)
def pv381481 : PrimeValue := ⟨381481, pr381481⟩
private theorem pr381509 : PrimeCertificate 381509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv127,pv751]) (by decide +kernel)
def pv381509 : PrimeValue := ⟨381509, pr381509⟩
private theorem pr381523 : PrimeCertificate 381523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv63587]) (by decide +kernel)
def pv381523 : PrimeValue := ⟨381523, pr381523⟩
private theorem pr381527 : PrimeCertificate 381527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv190763]) (by decide +kernel)
def pv381527 : PrimeValue := ⟨381527, pr381527⟩
private theorem pr381529 : PrimeCertificate 381529 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv757]) (by decide +kernel)
def pv381529 : PrimeValue := ⟨381529, pr381529⟩
private theorem pr381533 : PrimeCertificate 381533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv95383]) (by decide +kernel)
def pv381533 : PrimeValue := ⟨381533, pr381533⟩
private theorem pr381541 : PrimeCertificate 381541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv6359]) (by decide +kernel)
def pv381541 : PrimeValue := ⟨381541, pr381541⟩
private theorem pr381607 : PrimeCertificate 381607 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv63601]) (by decide +kernel)
def pv381607 : PrimeValue := ⟨381607, pr381607⟩
private theorem pr381673 : PrimeCertificate 381673 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv19,pv31]) (by decide +kernel)
def pv381673 : PrimeValue := ⟨381673, pr381673⟩
private theorem pr381707 : PrimeCertificate 381707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv53,pv277]) (by decide +kernel)
def pv381707 : PrimeValue := ⟨381707, pr381707⟩
private theorem pr381737 : PrimeCertificate 381737 :=
  certifyPrime (q := pv3) (ls := [pv2,pv47717]) (by decide +kernel)
def pv381737 : PrimeValue := ⟨381737, pr381737⟩
private theorem pr381749 : PrimeCertificate 381749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv5023]) (by decide +kernel)
def pv381749 : PrimeValue := ⟨381749, pr381749⟩
private theorem pr381757 : PrimeCertificate 381757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv1097]) (by decide +kernel)
def pv381757 : PrimeValue := ⟨381757, pr381757⟩
private theorem pr381761 : PrimeCertificate 381761 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1193]) (by decide +kernel)
def pv381761 : PrimeValue := ⟨381761, pr381761⟩
private theorem pr381791 : PrimeCertificate 381791 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv73,pv523]) (by decide +kernel)
def pv381791 : PrimeValue := ⟨381791, pr381791⟩
private theorem pr381793 : PrimeCertificate 381793 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv41,pv97]) (by decide +kernel)
def pv381793 : PrimeValue := ⟨381793, pr381793⟩
private theorem pr381853 : PrimeCertificate 381853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv10607]) (by decide +kernel)
def pv381853 : PrimeValue := ⟨381853, pr381853⟩
private theorem pr381911 : PrimeCertificate 381911 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv181,pv211]) (by decide +kernel)
def pv381911 : PrimeValue := ⟨381911, pr381911⟩
private theorem pr381937 : PrimeCertificate 381937 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv73,pv109]) (by decide +kernel)
def pv381937 : PrimeValue := ⟨381937, pr381937⟩
private theorem pr381943 : PrimeCertificate 381943 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv11,pv643]) (by decide +kernel)
def pv381943 : PrimeValue := ⟨381943, pr381943⟩
private theorem pr382001 : PrimeCertificate 382001 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv191]) (by decide +kernel)
def pv382001 : PrimeValue := ⟨382001, pr382001⟩
private theorem pr382003 : PrimeCertificate 382003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv63667]) (by decide +kernel)
def pv382003 : PrimeValue := ⟨382003, pr382003⟩
private theorem pr382061 : PrimeCertificate 382061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv2729]) (by decide +kernel)
def pv382061 : PrimeValue := ⟨382061, pr382061⟩
private theorem pr382073 : PrimeCertificate 382073 :=
  certifyPrime (q := pv3) (ls := [pv2,pv163,pv293]) (by decide +kernel)
def pv382073 : PrimeValue := ⟨382073, pr382073⟩
private theorem pr382087 : PrimeCertificate 382087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv21227]) (by decide +kernel)
def pv382087 : PrimeValue := ⟨382087, pr382087⟩
private theorem pr382117 : PrimeCertificate 382117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv4549]) (by decide +kernel)
def pv382117 : PrimeValue := ⟨382117, pr382117⟩
private theorem pr382163 : PrimeCertificate 382163 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv29,pv599]) (by decide +kernel)
def pv382163 : PrimeValue := ⟨382163, pr382163⟩
private theorem pr382229 : PrimeCertificate 382229 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11,pv17,pv73]) (by decide +kernel)
def pv382229 : PrimeValue := ⟨382229, pr382229⟩
private theorem pr382267 : PrimeCertificate 382267 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7079]) (by decide +kernel)
def pv382267 : PrimeValue := ⟨382267, pr382267⟩
private theorem pr382391 : PrimeCertificate 382391 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv38239]) (by decide +kernel)
def pv382391 : PrimeValue := ⟨382391, pr382391⟩
private theorem pr382511 : PrimeCertificate 382511 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv29,pv1319]) (by decide +kernel)
def pv382511 : PrimeValue := ⟨382511, pr382511⟩
private theorem pr382519 : PrimeCertificate 382519 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv79,pv269]) (by decide +kernel)
def pv382519 : PrimeValue := ⟨382519, pr382519⟩
private theorem pr382541 : PrimeCertificate 382541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31,pv617]) (by decide +kernel)
def pv382541 : PrimeValue := ⟨382541, pr382541⟩
private theorem pr382549 : PrimeCertificate 382549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv71,pv449]) (by decide +kernel)
def pv382549 : PrimeValue := ⟨382549, pr382549⟩
private theorem pr382601 : PrimeCertificate 382601 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv1913]) (by decide +kernel)
def pv382601 : PrimeValue := ⟨382601, pr382601⟩
private theorem pr382631 : PrimeCertificate 382631 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv83,pv461]) (by decide +kernel)
def pv382631 : PrimeValue := ⟨382631, pr382631⟩
private theorem pr382643 : PrimeCertificate 382643 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv14717]) (by decide +kernel)
def pv382643 : PrimeValue := ⟨382643, pr382643⟩
private theorem pr382703 : PrimeCertificate 382703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv179,pv1069]) (by decide +kernel)
def pv382703 : PrimeValue := ⟨382703, pr382703⟩
private theorem pr382709 : PrimeCertificate 382709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv241,pv397]) (by decide +kernel)
def pv382709 : PrimeValue := ⟨382709, pr382709⟩
private theorem pr382727 : PrimeCertificate 382727 :=
  certifyPrime (q := pv5) (ls := [pv2,pv31,pv6173]) (by decide +kernel)
def pv382727 : PrimeValue := ⟨382727, pr382727⟩
private theorem pr382751 : PrimeCertificate 382751 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv1531]) (by decide +kernel)
def pv382751 : PrimeValue := ⟨382751, pr382751⟩
private theorem pr382769 : PrimeCertificate 382769 :=
  certifyPrime (q := pv3) (ls := [pv2,pv47,pv509]) (by decide +kernel)
def pv382769 : PrimeValue := ⟨382769, pr382769⟩
private theorem pr382801 : PrimeCertificate 382801 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv29]) (by decide +kernel)
def pv382801 : PrimeValue := ⟨382801, pr382801⟩
private theorem pr382813 : PrimeCertificate 382813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv23,pv73]) (by decide +kernel)
def pv382813 : PrimeValue := ⟨382813, pr382813⟩
private theorem pr382843 : PrimeCertificate 382843 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv21269]) (by decide +kernel)
def pv382843 : PrimeValue := ⟨382843, pr382843⟩
private theorem pr382867 : PrimeCertificate 382867 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv5801]) (by decide +kernel)
def pv382867 : PrimeValue := ⟨382867, pr382867⟩
private theorem pr382883 : PrimeCertificate 382883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv191441]) (by decide +kernel)
def pv382883 : PrimeValue := ⟨382883, pr382883⟩
private theorem pr382999 : PrimeCertificate 382999 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv11,pv829]) (by decide +kernel)
def pv382999 : PrimeValue := ⟨382999, pr382999⟩
private theorem pr383023 : PrimeCertificate 383023 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41,pv173]) (by decide +kernel)
def pv383023 : PrimeValue := ⟨383023, pr383023⟩
private theorem pr383029 : PrimeCertificate 383029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv59,pv541]) (by decide +kernel)
def pv383029 : PrimeValue := ⟨383029, pr383029⟩
private theorem pr383081 : PrimeCertificate 383081 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv61,pv157]) (by decide +kernel)
def pv383081 : PrimeValue := ⟨383081, pr383081⟩
private theorem pr383101 : PrimeCertificate 383101 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv1277]) (by decide +kernel)
def pv383101 : PrimeValue := ⟨383101, pr383101⟩
private theorem pr383113 : PrimeCertificate 383113 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv313]) (by decide +kernel)
def pv383113 : PrimeValue := ⟨383113, pr383113⟩
private theorem pr383171 : PrimeCertificate 383171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv38317]) (by decide +kernel)
def pv383171 : PrimeValue := ⟨383171, pr383171⟩
private theorem pr383219 : PrimeCertificate 383219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv17419]) (by decide +kernel)
def pv383219 : PrimeValue := ⟨383219, pr383219⟩
private theorem pr383221 : PrimeCertificate 383221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv2129]) (by decide +kernel)
def pv383221 : PrimeValue := ⟨383221, pr383221⟩
private theorem pr383267 : PrimeCertificate 383267 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv14741]) (by decide +kernel)
def pv383267 : PrimeValue := ⟨383267, pr383267⟩
private theorem pr383291 : PrimeCertificate 383291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv38329]) (by decide +kernel)
def pv383291 : PrimeValue := ⟨383291, pr383291⟩
private theorem pr383297 : PrimeCertificate 383297 :=
  certifyPrime (q := pv5) (ls := [pv2,pv53,pv113]) (by decide +kernel)
def pv383297 : PrimeValue := ⟨383297, pr383297⟩
private theorem pr383429 : PrimeCertificate 383429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv95857]) (by decide +kernel)
def pv383429 : PrimeValue := ⟨383429, pr383429⟩
private theorem pr383483 : PrimeCertificate 383483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv17431]) (by decide +kernel)
def pv383483 : PrimeValue := ⟨383483, pr383483⟩
private theorem pr383527 : PrimeCertificate 383527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv13,pv149]) (by decide +kernel)
def pv383527 : PrimeValue := ⟨383527, pr383527⟩
private theorem pr383533 : PrimeCertificate 383533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv1031]) (by decide +kernel)
def pv383533 : PrimeValue := ⟨383533, pr383533⟩
private theorem pr383549 : PrimeCertificate 383549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv23,pv379]) (by decide +kernel)
def pv383549 : PrimeValue := ⟨383549, pr383549⟩
private theorem pr383573 : PrimeCertificate 383573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv19,pv103]) (by decide +kernel)
def pv383573 : PrimeValue := ⟨383573, pr383573⟩
private theorem pr383587 : PrimeCertificate 383587 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv9133]) (by decide +kernel)
def pv383587 : PrimeValue := ⟨383587, pr383587⟩
private theorem pr383609 : PrimeCertificate 383609 :=
  certifyPrime (q := pv3) (ls := [pv2,pv47951]) (by decide +kernel)
def pv383609 : PrimeValue := ⟨383609, pr383609⟩
private theorem pr383681 : PrimeCertificate 383681 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv11,pv109]) (by decide +kernel)
def pv383681 : PrimeValue := ⟨383681, pr383681⟩
private theorem pr383683 : PrimeCertificate 383683 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv4919]) (by decide +kernel)
def pv383683 : PrimeValue := ⟨383683, pr383683⟩
private theorem pr383693 : PrimeCertificate 383693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv95923]) (by decide +kernel)
def pv383693 : PrimeValue := ⟨383693, pr383693⟩
private theorem pr383759 : PrimeCertificate 383759 :=
  certifyPrime (q := pv19) (ls := [pv2,pv17,pv11287]) (by decide +kernel)
def pv383759 : PrimeValue := ⟨383759, pr383759⟩
private theorem pr383767 : PrimeCertificate 383767 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv167,pv383]) (by decide +kernel)
def pv383767 : PrimeValue := ⟨383767, pr383767⟩
private theorem pr383813 : PrimeCertificate 383813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13,pv61]) (by decide +kernel)
def pv383813 : PrimeValue := ⟨383813, pr383813⟩
private theorem pr383833 : PrimeCertificate 383833 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1777]) (by decide +kernel)
def pv383833 : PrimeValue := ⟨383833, pr383833⟩
private theorem pr383869 : PrimeCertificate 383869 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv10663]) (by decide +kernel)
def pv383869 : PrimeValue := ⟨383869, pr383869⟩
private theorem pr383891 : PrimeCertificate 383891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv2953]) (by decide +kernel)
def pv383891 : PrimeValue := ⟨383891, pr383891⟩
private theorem pr383917 : PrimeCertificate 383917 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv23,pv107]) (by decide +kernel)
def pv383917 : PrimeValue := ⟨383917, pr383917⟩
private theorem pr383963 : PrimeCertificate 383963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv23,pv491]) (by decide +kernel)
def pv383963 : PrimeValue := ⟨383963, pr383963⟩
private theorem pr383969 : PrimeCertificate 383969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv71]) (by decide +kernel)
def pv383969 : PrimeValue := ⟨383969, pr383969⟩
private theorem pr383987 : PrimeCertificate 383987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv5189]) (by decide +kernel)
def pv383987 : PrimeValue := ⟨383987, pr383987⟩
private theorem pr384017 : PrimeCertificate 384017 :=
  certifyPrime (q := pv3) (ls := [pv2,pv24001]) (by decide +kernel)
def pv384017 : PrimeValue := ⟨384017, pr384017⟩
private theorem pr384029 : PrimeCertificate 384029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv31,pv163]) (by decide +kernel)
def pv384029 : PrimeValue := ⟨384029, pr384029⟩
private theorem pr384067 : PrimeCertificate 384067 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv1123]) (by decide +kernel)
def pv384067 : PrimeValue := ⟨384067, pr384067⟩
private theorem pr384107 : PrimeCertificate 384107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv192053]) (by decide +kernel)
def pv384107 : PrimeValue := ⟨384107, pr384107⟩
private theorem pr384133 : PrimeCertificate 384133 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv17,pv269]) (by decide +kernel)
def pv384133 : PrimeValue := ⟨384133, pr384133⟩
private theorem pr384173 : PrimeCertificate 384173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv96043]) (by decide +kernel)
def pv384173 : PrimeValue := ⟨384173, pr384173⟩
private theorem pr384227 : PrimeCertificate 384227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv192113]) (by decide +kernel)
def pv384227 : PrimeValue := ⟨384227, pr384227⟩
private theorem pr384247 : PrimeCertificate 384247 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv21347]) (by decide +kernel)
def pv384247 : PrimeValue := ⟨384247, pr384247⟩
private theorem pr384253 : PrimeCertificate 384253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv41,pv71]) (by decide +kernel)
def pv384253 : PrimeValue := ⟨384253, pr384253⟩
private theorem pr384259 : PrimeCertificate 384259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1307]) (by decide +kernel)
def pv384259 : PrimeValue := ⟨384259, pr384259⟩
private theorem pr384317 : PrimeCertificate 384317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv96079]) (by decide +kernel)
def pv384317 : PrimeValue := ⟨384317, pr384317⟩
private theorem pr384331 : PrimeCertificate 384331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv23,pv557]) (by decide +kernel)
def pv384331 : PrimeValue := ⟨384331, pr384331⟩
private theorem pr384343 : PrimeCertificate 384343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv9151]) (by decide +kernel)
def pv384343 : PrimeValue := ⟨384343, pr384343⟩
private theorem pr384359 : PrimeCertificate 384359 :=
  certifyPrime (q := pv17) (ls := [pv2,pv13,pv14783]) (by decide +kernel)
def pv384359 : PrimeValue := ⟨384359, pr384359⟩
private theorem pr384367 : PrimeCertificate 384367 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29,pv47]) (by decide +kernel)
def pv384367 : PrimeValue := ⟨384367, pr384367⟩
private theorem pr384383 : PrimeCertificate 384383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv192191]) (by decide +kernel)
def pv384383 : PrimeValue := ⟨384383, pr384383⟩
private theorem pr384437 : PrimeCertificate 384437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv7393]) (by decide +kernel)
def pv384437 : PrimeValue := ⟨384437, pr384437⟩
private theorem pr384509 : PrimeCertificate 384509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv97,pv991]) (by decide +kernel)
def pv384509 : PrimeValue := ⟨384509, pr384509⟩
private theorem pr384581 : PrimeCertificate 384581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv41,pv67]) (by decide +kernel)
def pv384581 : PrimeValue := ⟨384581, pr384581⟩
private theorem pr384623 : PrimeCertificate 384623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv83,pv331]) (by decide +kernel)
def pv384623 : PrimeValue := ⟨384623, pr384623⟩
private theorem pr384697 : PrimeCertificate 384697 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv137]) (by decide +kernel)
def pv384697 : PrimeValue := ⟨384697, pr384697⟩
private theorem pr384701 : PrimeCertificate 384701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv3847]) (by decide +kernel)
def pv384701 : PrimeValue := ⟨384701, pr384701⟩
private theorem pr384733 : PrimeCertificate 384733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv10687]) (by decide +kernel)
def pv384733 : PrimeValue := ⟨384733, pr384733⟩
private theorem pr384751 : PrimeCertificate 384751 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv384751 : PrimeValue := ⟨384751, pr384751⟩
private theorem pr384757 : PrimeCertificate 384757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv32063]) (by decide +kernel)
def pv384757 : PrimeValue := ⟨384757, pr384757⟩
private theorem pr384773 : PrimeCertificate 384773 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv31,pv107]) (by decide +kernel)
def pv384773 : PrimeValue := ⟨384773, pr384773⟩
private theorem pr384817 : PrimeCertificate 384817 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv8017]) (by decide +kernel)
def pv384817 : PrimeValue := ⟨384817, pr384817⟩
private theorem pr384827 : PrimeCertificate 384827 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv19,pv41]) (by decide +kernel)
def pv384827 : PrimeValue := ⟨384827, pr384827⟩
private theorem pr384847 : PrimeCertificate 384847 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv7,pv11,pv17]) (by decide +kernel)
def pv384847 : PrimeValue := ⟨384847, pr384847⟩
private theorem pr384889 : PrimeCertificate 384889 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv29,pv79]) (by decide +kernel)
def pv384889 : PrimeValue := ⟨384889, pr384889⟩
private theorem pr384913 : PrimeCertificate 384913 :=
  certifyPrime (q := pv47) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv384913 : PrimeValue := ⟨384913, pr384913⟩
private theorem pr385013 : PrimeCertificate 385013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv101,pv953]) (by decide +kernel)
def pv385013 : PrimeValue := ⟨385013, pr385013⟩
private theorem pr385027 : PrimeCertificate 385027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv64171]) (by decide +kernel)
def pv385027 : PrimeValue := ⟨385027, pr385027⟩
private theorem pr385039 : PrimeCertificate 385039 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv21391]) (by decide +kernel)
def pv385039 : PrimeValue := ⟨385039, pr385039⟩
private theorem pr385057 : PrimeCertificate 385057 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv191]) (by decide +kernel)
def pv385057 : PrimeValue := ⟨385057, pr385057⟩
private theorem pr385079 : PrimeCertificate 385079 :=
  certifyPrime (q := pv7) (ls := [pv2,pv192539]) (by decide +kernel)
def pv385079 : PrimeValue := ⟨385079, pr385079⟩
private theorem pr385127 : PrimeCertificate 385127 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv27509]) (by decide +kernel)
def pv385127 : PrimeValue := ⟨385127, pr385127⟩
private theorem pr385193 : PrimeCertificate 385193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv89,pv541]) (by decide +kernel)
def pv385193 : PrimeValue := ⟨385193, pr385193⟩
private theorem pr385223 : PrimeCertificate 385223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv192611]) (by decide +kernel)
def pv385223 : PrimeValue := ⟨385223, pr385223⟩
private theorem pr385249 : PrimeCertificate 385249 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv4013]) (by decide +kernel)
def pv385249 : PrimeValue := ⟨385249, pr385249⟩
private theorem pr385279 : PrimeCertificate 385279 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv157,pv409]) (by decide +kernel)
def pv385279 : PrimeValue := ⟨385279, pr385279⟩
private theorem pr385289 : PrimeCertificate 385289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv2833]) (by decide +kernel)
def pv385289 : PrimeValue := ⟨385289, pr385289⟩
private theorem pr385291 : PrimeCertificate 385291 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv1427]) (by decide +kernel)
def pv385291 : PrimeValue := ⟨385291, pr385291⟩
private theorem pr385331 : PrimeCertificate 385331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv31,pv113]) (by decide +kernel)
def pv385331 : PrimeValue := ⟨385331, pr385331⟩
private theorem pr385391 : PrimeCertificate 385391 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv17,pv2267]) (by decide +kernel)
def pv385391 : PrimeValue := ⟨385391, pr385391⟩
private theorem pr385397 : PrimeCertificate 385397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv19,pv461]) (by decide +kernel)
def pv385397 : PrimeValue := ⟨385397, pr385397⟩
private theorem pr385403 : PrimeCertificate 385403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv131,pv1471]) (by decide +kernel)
def pv385403 : PrimeValue := ⟨385403, pr385403⟩
private theorem pr385433 : PrimeCertificate 385433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv48179]) (by decide +kernel)
def pv385433 : PrimeValue := ⟨385433, pr385433⟩
private theorem pr385501 : PrimeCertificate 385501 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv257]) (by decide +kernel)
def pv385501 : PrimeValue := ⟨385501, pr385501⟩
private theorem pr385519 : PrimeCertificate 385519 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv67,pv137]) (by decide +kernel)
def pv385519 : PrimeValue := ⟨385519, pr385519⟩
private theorem pr385531 : PrimeCertificate 385531 :=
  certifyPrime (q := pv47) (ls := [pv2,pv3,pv5,pv71,pv181]) (by decide +kernel)
def pv385531 : PrimeValue := ⟨385531, pr385531⟩
private theorem pr385571 : PrimeCertificate 385571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv38557]) (by decide +kernel)
def pv385571 : PrimeValue := ⟨385571, pr385571⟩
private theorem pr385573 : PrimeCertificate 385573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv23,pv127]) (by decide +kernel)
def pv385573 : PrimeValue := ⟨385573, pr385573⟩
private theorem pr385589 : PrimeCertificate 385589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv47,pv293]) (by decide +kernel)
def pv385589 : PrimeValue := ⟨385589, pr385589⟩
private theorem pr385607 : PrimeCertificate 385607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv14831]) (by decide +kernel)
def pv385607 : PrimeValue := ⟨385607, pr385607⟩
private theorem pr385661 : PrimeCertificate 385661 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv1753]) (by decide +kernel)
def pv385661 : PrimeValue := ⟨385661, pr385661⟩
private theorem pr385709 : PrimeCertificate 385709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv211,pv457]) (by decide +kernel)
def pv385709 : PrimeValue := ⟨385709, pr385709⟩
private theorem pr385783 : PrimeCertificate 385783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv113,pv569]) (by decide +kernel)
def pv385783 : PrimeValue := ⟨385783, pr385783⟩
private theorem pr385793 : PrimeCertificate 385793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv137]) (by decide +kernel)
def pv385793 : PrimeValue := ⟨385793, pr385793⟩
private theorem pr385811 : PrimeCertificate 385811 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv41,pv941]) (by decide +kernel)
def pv385811 : PrimeValue := ⟨385811, pr385811⟩
private theorem pr385837 : PrimeCertificate 385837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv37,pv79]) (by decide +kernel)
def pv385837 : PrimeValue := ⟨385837, pr385837⟩
private theorem pr385843 : PrimeCertificate 385843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv107,pv601]) (by decide +kernel)
def pv385843 : PrimeValue := ⟨385843, pr385843⟩
private theorem pr385877 : PrimeCertificate 385877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv96469]) (by decide +kernel)
def pv385877 : PrimeValue := ⟨385877, pr385877⟩
private theorem pr385897 : PrimeCertificate 385897 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv2297]) (by decide +kernel)
def pv385897 : PrimeValue := ⟨385897, pr385897⟩
private theorem pr385901 : PrimeCertificate 385901 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv17,pv227]) (by decide +kernel)
def pv385901 : PrimeValue := ⟨385901, pr385901⟩
private theorem pr385927 : PrimeCertificate 385927 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv131,pv491]) (by decide +kernel)
def pv385927 : PrimeValue := ⟨385927, pr385927⟩
private theorem pr385943 : PrimeCertificate 385943 :=
  certifyPrime (q := pv5) (ls := [pv2,pv192971]) (by decide +kernel)
def pv385943 : PrimeValue := ⟨385943, pr385943⟩
private theorem pr385967 : PrimeCertificate 385967 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv19,pv1451]) (by decide +kernel)
def pv385967 : PrimeValue := ⟨385967, pr385967⟩
private theorem pr385991 : PrimeCertificate 385991 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv11,pv29]) (by decide +kernel)
def pv385991 : PrimeValue := ⟨385991, pr385991⟩
private theorem pr385997 : PrimeCertificate 385997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv571]) (by decide +kernel)
def pv385997 : PrimeValue := ⟨385997, pr385997⟩
private theorem pr386041 : PrimeCertificate 386041 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv3217]) (by decide +kernel)
def pv386041 : PrimeValue := ⟨386041, pr386041⟩
private theorem pr386143 : PrimeCertificate 386143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv139,pv463]) (by decide +kernel)
def pv386143 : PrimeValue := ⟨386143, pr386143⟩
private theorem pr386161 : PrimeCertificate 386161 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv1609]) (by decide +kernel)
def pv386161 : PrimeValue := ⟨386161, pr386161⟩
private theorem pr386173 : PrimeCertificate 386173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv631]) (by decide +kernel)
def pv386173 : PrimeValue := ⟨386173, pr386173⟩
private theorem pr386219 : PrimeCertificate 386219 :=
  certifyPrime (q := pv11) (ls := [pv2,pv7,pv563]) (by decide +kernel)
def pv386219 : PrimeValue := ⟨386219, pr386219⟩
private theorem pr386227 : PrimeCertificate 386227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv499]) (by decide +kernel)
def pv386227 : PrimeValue := ⟨386227, pr386227⟩
private theorem pr386249 : PrimeCertificate 386249 :=
  certifyPrime (q := pv3) (ls := [pv2,pv48281]) (by decide +kernel)
def pv386249 : PrimeValue := ⟨386249, pr386249⟩
private theorem pr386279 : PrimeCertificate 386279 :=
  certifyPrime (q := pv11) (ls := [pv2,pv193139]) (by decide +kernel)
def pv386279 : PrimeValue := ⟨386279, pr386279⟩
private theorem pr386339 : PrimeCertificate 386339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv6661]) (by decide +kernel)
def pv386339 : PrimeValue := ⟨386339, pr386339⟩
private theorem pr386411 : PrimeCertificate 386411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv2273]) (by decide +kernel)
def pv386411 : PrimeValue := ⟨386411, pr386411⟩
private theorem pr386413 : PrimeCertificate 386413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv2477]) (by decide +kernel)
def pv386413 : PrimeValue := ⟨386413, pr386413⟩
private theorem pr386429 : PrimeCertificate 386429 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv37,pv373]) (by decide +kernel)
def pv386429 : PrimeValue := ⟨386429, pr386429⟩
private theorem pr386437 : PrimeCertificate 386437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv32203]) (by decide +kernel)
def pv386437 : PrimeValue := ⟨386437, pr386437⟩
private theorem pr386549 : PrimeCertificate 386549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv2357]) (by decide +kernel)
def pv386549 : PrimeValue := ⟨386549, pr386549⟩
private theorem pr386621 : PrimeCertificate 386621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv1487]) (by decide +kernel)
def pv386621 : PrimeValue := ⟨386621, pr386621⟩
private theorem pr386647 : PrimeCertificate 386647 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv4957]) (by decide +kernel)
def pv386647 : PrimeValue := ⟨386647, pr386647⟩
private theorem pr386651 : PrimeCertificate 386651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv19,pv37]) (by decide +kernel)
def pv386651 : PrimeValue := ⟨386651, pr386651⟩
private theorem pr386677 : PrimeCertificate 386677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv467]) (by decide +kernel)
def pv386677 : PrimeValue := ⟨386677, pr386677⟩
private theorem pr386689 : PrimeCertificate 386689 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv19,pv53]) (by decide +kernel)
def pv386689 : PrimeValue := ⟨386689, pr386689⟩
private theorem pr386693 : PrimeCertificate 386693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv277,pv349]) (by decide +kernel)
def pv386693 : PrimeValue := ⟨386693, pr386693⟩
private theorem pr386723 : PrimeCertificate 386723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv23,pv1201]) (by decide +kernel)
def pv386723 : PrimeValue := ⟨386723, pr386723⟩
private theorem pr386731 : PrimeCertificate 386731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv4297]) (by decide +kernel)
def pv386731 : PrimeValue := ⟨386731, pr386731⟩
private theorem pr386921 : PrimeCertificate 386921 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17,pv569]) (by decide +kernel)
def pv386921 : PrimeValue := ⟨386921, pr386921⟩
private theorem pr386927 : PrimeCertificate 386927 :=
  certifyPrime (q := pv5) (ls := [pv2,pv193463]) (by decide +kernel)
def pv386927 : PrimeValue := ⟨386927, pr386927⟩
private theorem pr386977 : PrimeCertificate 386977 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29,pv139]) (by decide +kernel)
def pv386977 : PrimeValue := ⟨386977, pr386977⟩
private theorem pr386987 : PrimeCertificate 386987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv193493]) (by decide +kernel)
def pv386987 : PrimeValue := ⟨386987, pr386987⟩
private theorem pr386993 : PrimeCertificate 386993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv67]) (by decide +kernel)
def pv386993 : PrimeValue := ⟨386993, pr386993⟩
private theorem pr387047 : PrimeCertificate 387047 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv73,pv241]) (by decide +kernel)
def pv387047 : PrimeValue := ⟨387047, pr387047⟩
private theorem pr387071 : PrimeCertificate 387071 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv38707]) (by decide +kernel)
def pv387071 : PrimeValue := ⟨387071, pr387071⟩
private theorem pr387077 : PrimeCertificate 387077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv96769]) (by decide +kernel)
def pv387077 : PrimeValue := ⟨387077, pr387077⟩
private theorem pr387137 : PrimeCertificate 387137 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv263]) (by decide +kernel)
def pv387137 : PrimeValue := ⟨387137, pr387137⟩
private theorem pr387161 : PrimeCertificate 387161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv9679]) (by decide +kernel)
def pv387161 : PrimeValue := ⟨387161, pr387161⟩
private theorem pr387173 : PrimeCertificate 387173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv2251]) (by decide +kernel)
def pv387173 : PrimeValue := ⟨387173, pr387173⟩
private theorem pr387269 : PrimeCertificate 387269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13831]) (by decide +kernel)
def pv387269 : PrimeValue := ⟨387269, pr387269⟩
private theorem pr387329 : PrimeCertificate 387329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv89]) (by decide +kernel)
def pv387329 : PrimeValue := ⟨387329, pr387329⟩
private theorem pr387403 : PrimeCertificate 387403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv64567]) (by decide +kernel)
def pv387403 : PrimeValue := ⟨387403, pr387403⟩
private theorem pr387433 : PrimeCertificate 387433 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv5381]) (by decide +kernel)
def pv387433 : PrimeValue := ⟨387433, pr387433⟩
private theorem pr387437 : PrimeCertificate 387437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv101,pv137]) (by decide +kernel)
def pv387437 : PrimeValue := ⟨387437, pr387437⟩
private theorem pr387463 : PrimeCertificate 387463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv64577]) (by decide +kernel)
def pv387463 : PrimeValue := ⟨387463, pr387463⟩
private theorem pr387503 : PrimeCertificate 387503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv193751]) (by decide +kernel)
def pv387503 : PrimeValue := ⟨387503, pr387503⟩
private theorem pr387577 : PrimeCertificate 387577 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv769]) (by decide +kernel)
def pv387577 : PrimeValue := ⟨387577, pr387577⟩
private theorem pr387587 : PrimeCertificate 387587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv193793]) (by decide +kernel)
def pv387587 : PrimeValue := ⟨387587, pr387587⟩
private theorem pr387677 : PrimeCertificate 387677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv5101]) (by decide +kernel)
def pv387677 : PrimeValue := ⟨387677, pr387677⟩
private theorem pr387683 : PrimeCertificate 387683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv193841]) (by decide +kernel)
def pv387683 : PrimeValue := ⟨387683, pr387683⟩
private theorem pr387721 : PrimeCertificate 387721 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv5,pv359]) (by decide +kernel)
def pv387721 : PrimeValue := ⟨387721, pr387721⟩
private theorem pr387743 : PrimeCertificate 387743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv193871]) (by decide +kernel)
def pv387743 : PrimeValue := ⟨387743, pr387743⟩
private theorem pr387763 : PrimeCertificate 387763 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv64627]) (by decide +kernel)
def pv387763 : PrimeValue := ⟨387763, pr387763⟩
private theorem pr387791 : PrimeCertificate 387791 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv13,pv19,pv157]) (by decide +kernel)
def pv387791 : PrimeValue := ⟨387791, pr387791⟩
private theorem pr387799 : PrimeCertificate 387799 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv64633]) (by decide +kernel)
def pv387799 : PrimeValue := ⟨387799, pr387799⟩
private theorem pr387839 : PrimeCertificate 387839 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv17,pv61]) (by decide +kernel)
def pv387839 : PrimeValue := ⟨387839, pr387839⟩
private theorem pr387911 : PrimeCertificate 387911 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv38791]) (by decide +kernel)
def pv387911 : PrimeValue := ⟨387911, pr387911⟩
private theorem pr387971 : PrimeCertificate 387971 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv11,pv3527]) (by decide +kernel)
def pv387971 : PrimeValue := ⟨387971, pr387971⟩
private theorem pr387977 : PrimeCertificate 387977 :=
  certifyPrime (q := pv3) (ls := [pv2,pv48497]) (by decide +kernel)
def pv387977 : PrimeValue := ⟨387977, pr387977⟩
private theorem pr388009 : PrimeCertificate 388009 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv317]) (by decide +kernel)
def pv388009 : PrimeValue := ⟨388009, pr388009⟩
private theorem pr388051 : PrimeCertificate 388051 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv5,pv13,pv199]) (by decide +kernel)
def pv388051 : PrimeValue := ⟨388051, pr388051⟩
private theorem pr388109 : PrimeCertificate 388109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv83,pv167]) (by decide +kernel)
def pv388109 : PrimeValue := ⟨388109, pr388109⟩
private theorem pr388117 : PrimeCertificate 388117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv10781]) (by decide +kernel)
def pv388117 : PrimeValue := ⟨388117, pr388117⟩
private theorem pr388133 : PrimeCertificate 388133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv5107]) (by decide +kernel)
def pv388133 : PrimeValue := ⟨388133, pr388133⟩
private theorem pr388163 : PrimeCertificate 388163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv421,pv461]) (by decide +kernel)
def pv388163 : PrimeValue := ⟨388163, pr388163⟩
private theorem pr388177 : PrimeCertificate 388177 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv8087]) (by decide +kernel)
def pv388177 : PrimeValue := ⟨388177, pr388177⟩
private theorem pr388187 : PrimeCertificate 388187 :=
  certifyPrime (q := pv2) (ls := [pv2,pv194093]) (by decide +kernel)
def pv388187 : PrimeValue := ⟨388187, pr388187⟩
private theorem pr388211 : PrimeCertificate 388211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv38821]) (by decide +kernel)
def pv388211 : PrimeValue := ⟨388211, pr388211⟩
private theorem pr388231 : PrimeCertificate 388231 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv12941]) (by decide +kernel)
def pv388231 : PrimeValue := ⟨388231, pr388231⟩
private theorem pr388237 : PrimeCertificate 388237 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv32353]) (by decide +kernel)
def pv388237 : PrimeValue := ⟨388237, pr388237⟩
private theorem pr388253 : PrimeCertificate 388253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv3347]) (by decide +kernel)
def pv388253 : PrimeValue := ⟨388253, pr388253⟩
private theorem pr388259 : PrimeCertificate 388259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv109,pv137]) (by decide +kernel)
def pv388259 : PrimeValue := ⟨388259, pr388259⟩
private theorem pr388273 : PrimeCertificate 388273 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv8089]) (by decide +kernel)
def pv388273 : PrimeValue := ⟨388273, pr388273⟩
private theorem pr388301 : PrimeCertificate 388301 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv353]) (by decide +kernel)
def pv388301 : PrimeValue := ⟨388301, pr388301⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
