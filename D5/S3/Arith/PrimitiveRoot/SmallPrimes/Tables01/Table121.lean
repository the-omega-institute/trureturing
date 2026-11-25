/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table121
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table121.pv624763
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table014
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table015
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table018
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table025
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table039
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table040
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table087
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table088

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr624763 : PrimeCertificate 624763 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv61,pv569]) (by decide +kernel)
def pv624763 : PrimeValue := ⟨624763, pr624763⟩
private theorem pr624787 : PrimeCertificate 624787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv101,pv1031]) (by decide +kernel)
def pv624787 : PrimeValue := ⟨624787, pr624787⟩
private theorem pr624847 : PrimeCertificate 624847 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv223,pv467]) (by decide +kernel)
def pv624847 : PrimeValue := ⟨624847, pr624847⟩
private theorem pr624997 : PrimeCertificate 624997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv643]) (by decide +kernel)
def pv624997 : PrimeValue := ⟨624997, pr624997⟩
private theorem pr625253 : PrimeCertificate 625253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv433]) (by decide +kernel)
def pv625253 : PrimeValue := ⟨625253, pr625253⟩
private theorem pr625489 : PrimeCertificate 625489 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv83,pv157]) (by decide +kernel)
def pv625489 : PrimeValue := ⟨625489, pr625489⟩
private theorem pr625543 : PrimeCertificate 625543 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv137,pv761]) (by decide +kernel)
def pv625543 : PrimeValue := ⟨625543, pr625543⟩
private theorem pr625589 : PrimeCertificate 625589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv5393]) (by decide +kernel)
def pv625589 : PrimeValue := ⟨625589, pr625589⟩
private theorem pr625643 : PrimeCertificate 625643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv10091]) (by decide +kernel)
def pv625643 : PrimeValue := ⟨625643, pr625643⟩
private theorem pr625657 : PrimeCertificate 625657 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv131,pv199]) (by decide +kernel)
def pv625657 : PrimeValue := ⟨625657, pr625657⟩
private theorem pr625661 : PrimeCertificate 625661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv41,pv109]) (by decide +kernel)
def pv625661 : PrimeValue := ⟨625661, pr625661⟩
private theorem pr625763 : PrimeCertificate 625763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv10789]) (by decide +kernel)
def pv625763 : PrimeValue := ⟨625763, pr625763⟩
private theorem pr625871 : PrimeCertificate 625871 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv8941]) (by decide +kernel)
def pv625871 : PrimeValue := ⟨625871, pr625871⟩
private theorem pr625909 : PrimeCertificate 625909 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv43,pv1213]) (by decide +kernel)
def pv625909 : PrimeValue := ⟨625909, pr625909⟩
private theorem pr625913 : PrimeCertificate 625913 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11177]) (by decide +kernel)
def pv625913 : PrimeValue := ⟨625913, pr625913⟩
private theorem pr626051 : PrimeCertificate 626051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv659]) (by decide +kernel)
def pv626051 : PrimeValue := ⟨626051, pr626051⟩
private theorem pr626173 : PrimeCertificate 626173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv52181]) (by decide +kernel)
def pv626173 : PrimeValue := ⟨626173, pr626173⟩
private theorem pr626201 : PrimeCertificate 626201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv31,pv101]) (by decide +kernel)
def pv626201 : PrimeValue := ⟨626201, pr626201⟩
private theorem pr626261 : PrimeCertificate 626261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv173,pv181]) (by decide +kernel)
def pv626261 : PrimeValue := ⟨626261, pr626261⟩
private theorem pr626389 : PrimeCertificate 626389 :=
  certifyPrime (q := pv47) (ls := [pv2,pv3,pv7,pv7457]) (by decide +kernel)
def pv626389 : PrimeValue := ⟨626389, pr626389⟩
private theorem pr626443 : PrimeCertificate 626443 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv131,pv797]) (by decide +kernel)
def pv626443 : PrimeValue := ⟨626443, pr626443⟩
private theorem pr626599 : PrimeCertificate 626599 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv4973]) (by decide +kernel)
def pv626599 : PrimeValue := ⟨626599, pr626599⟩
private theorem pr626663 : PrimeCertificate 626663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv313331]) (by decide +kernel)
def pv626663 : PrimeValue := ⟨626663, pr626663⟩
private theorem pr626749 : PrimeCertificate 626749 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv29,pv1801]) (by decide +kernel)
def pv626749 : PrimeValue := ⟨626749, pr626749⟩
private theorem pr626861 : PrimeCertificate 626861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv2411]) (by decide +kernel)
def pv626861 : PrimeValue := ⟨626861, pr626861⟩
private theorem pr626959 : PrimeCertificate 626959 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv61,pv571]) (by decide +kernel)
def pv626959 : PrimeValue := ⟨626959, pr626959⟩
private theorem pr627059 : PrimeCertificate 627059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv157,pv1997]) (by decide +kernel)
def pv627059 : PrimeValue := ⟨627059, pr627059⟩
private theorem pr627073 : PrimeCertificate 627073 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23,pv71]) (by decide +kernel)
def pv627073 : PrimeValue := ⟨627073, pr627073⟩
private theorem pr627089 : PrimeCertificate 627089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11,pv509]) (by decide +kernel)
def pv627089 : PrimeValue := ⟨627089, pr627089⟩
private theorem pr627101 : PrimeCertificate 627101 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv6271]) (by decide +kernel)
def pv627101 : PrimeValue := ⟨627101, pr627101⟩
private theorem pr627139 : PrimeCertificate 627139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv34841]) (by decide +kernel)
def pv627139 : PrimeValue := ⟨627139, pr627139⟩
private theorem pr627169 : PrimeCertificate 627169 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv47,pv139]) (by decide +kernel)
def pv627169 : PrimeValue := ⟨627169, pr627169⟩
private theorem pr627251 : PrimeCertificate 627251 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv193]) (by decide +kernel)
def pv627251 : PrimeValue := ⟨627251, pr627251⟩
private theorem pr627379 : PrimeCertificate 627379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv3373]) (by decide +kernel)
def pv627379 : PrimeValue := ⟨627379, pr627379⟩
private theorem pr627383 : PrimeCertificate 627383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv41,pv1093]) (by decide +kernel)
def pv627383 : PrimeValue := ⟨627383, pr627383⟩
private theorem pr627449 : PrimeCertificate 627449 :=
  certifyPrime (q := pv3) (ls := [pv2,pv107,pv733]) (by decide +kernel)
def pv627449 : PrimeValue := ⟨627449, pr627449⟩
private theorem pr627479 : PrimeCertificate 627479 :=
  certifyPrime (q := pv13) (ls := [pv2,pv313739]) (by decide +kernel)
def pv627479 : PrimeValue := ⟨627479, pr627479⟩
private theorem pr627491 : PrimeCertificate 627491 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv131,pv479]) (by decide +kernel)
def pv627491 : PrimeValue := ⟨627491, pr627491⟩
private theorem pr627593 : PrimeCertificate 627593 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv1601]) (by decide +kernel)
def pv627593 : PrimeValue := ⟨627593, pr627593⟩
private theorem pr627619 : PrimeCertificate 627619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv3607]) (by decide +kernel)
def pv627619 : PrimeValue := ⟨627619, pr627619⟩
private theorem pr627637 : PrimeCertificate 627637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv193,pv271]) (by decide +kernel)
def pv627637 : PrimeValue := ⟨627637, pr627637⟩
private theorem pr627787 : PrimeCertificate 627787 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv34877]) (by decide +kernel)
def pv627787 : PrimeValue := ⟨627787, pr627787⟩
private theorem pr627953 : PrimeCertificate 627953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv3019]) (by decide +kernel)
def pv627953 : PrimeValue := ⟨627953, pr627953⟩
private theorem pr628057 : PrimeCertificate 628057 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv13,pv61]) (by decide +kernel)
def pv628057 : PrimeValue := ⟨628057, pr628057⟩
private theorem pr628139 : PrimeCertificate 628139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv44867]) (by decide +kernel)
def pv628139 : PrimeValue := ⟨628139, pr628139⟩
private theorem pr628289 : PrimeCertificate 628289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv9817]) (by decide +kernel)
def pv628289 : PrimeValue := ⟨628289, pr628289⟩
private theorem pr628373 : PrimeCertificate 628373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv5417]) (by decide +kernel)
def pv628373 : PrimeValue := ⟨628373, pr628373⟩
private theorem pr628679 : PrimeCertificate 628679 :=
  certifyPrime (q := pv7) (ls := [pv2,pv314339]) (by decide +kernel)
def pv628679 : PrimeValue := ⟨628679, pr628679⟩
private theorem pr628753 : PrimeCertificate 628753 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13099]) (by decide +kernel)
def pv628753 : PrimeValue := ⟨628753, pr628753⟩
private theorem pr628781 : PrimeCertificate 628781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv149,pv211]) (by decide +kernel)
def pv628781 : PrimeValue := ⟨628781, pr628781⟩
private theorem pr628913 : PrimeCertificate 628913 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv1709]) (by decide +kernel)
def pv628913 : PrimeValue := ⟨628913, pr628913⟩
private theorem pr628939 : PrimeCertificate 628939 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv613]) (by decide +kernel)
def pv628939 : PrimeValue := ⟨628939, pr628939⟩
private theorem pr629081 : PrimeCertificate 629081 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv15727]) (by decide +kernel)
def pv629081 : PrimeValue := ⟨629081, pr629081⟩
private theorem pr629143 : PrimeCertificate 629143 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv47,pv97]) (by decide +kernel)
def pv629143 : PrimeValue := ⟨629143, pr629143⟩
private theorem pr629171 : PrimeCertificate 629171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv3701]) (by decide +kernel)
def pv629171 : PrimeValue := ⟨629171, pr629171⟩
private theorem pr629243 : PrimeCertificate 629243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv29,pv571]) (by decide +kernel)
def pv629243 : PrimeValue := ⟨629243, pr629243⟩
private theorem pr629383 : PrimeCertificate 629383 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv13,pv8069]) (by decide +kernel)
def pv629383 : PrimeValue := ⟨629383, pr629383⟩
private theorem pr629449 : PrimeCertificate 629449 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv26227]) (by decide +kernel)
def pv629449 : PrimeValue := ⟨629449, pr629449⟩
private theorem pr629467 : PrimeCertificate 629467 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv104911]) (by decide +kernel)
def pv629467 : PrimeValue := ⟨629467, pr629467⟩
private theorem pr629483 : PrimeCertificate 629483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv44963]) (by decide +kernel)
def pv629483 : PrimeValue := ⟨629483, pr629483⟩
private theorem pr629623 : PrimeCertificate 629623 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv19,pv263]) (by decide +kernel)
def pv629623 : PrimeValue := ⟨629623, pr629623⟩
private theorem pr629737 : PrimeCertificate 629737 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv1381]) (by decide +kernel)
def pv629737 : PrimeValue := ⟨629737, pr629737⟩
private theorem pr629743 : PrimeCertificate 629743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv103,pv1019]) (by decide +kernel)
def pv629743 : PrimeValue := ⟨629743, pr629743⟩
private theorem pr629773 : PrimeCertificate 629773 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv13,pv367]) (by decide +kernel)
def pv629773 : PrimeValue := ⟨629773, pr629773⟩
private theorem pr629819 : PrimeCertificate 629819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv44987]) (by decide +kernel)
def pv629819 : PrimeValue := ⟨629819, pr629819⟩
private theorem pr629899 : PrimeCertificate 629899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv277,pv379]) (by decide +kernel)
def pv629899 : PrimeValue := ⟨629899, pr629899⟩
private theorem pr629963 : PrimeCertificate 629963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv8513]) (by decide +kernel)
def pv629963 : PrimeValue := ⟨629963, pr629963⟩
private theorem pr630023 : PrimeCertificate 630023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv315011]) (by decide +kernel)
def pv630023 : PrimeValue := ⟨630023, pr630023⟩
private theorem pr630029 : PrimeCertificate 630029 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv22501]) (by decide +kernel)
def pv630029 : PrimeValue := ⟨630029, pr630029⟩
private theorem pr630043 : PrimeCertificate 630043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv2143]) (by decide +kernel)
def pv630043 : PrimeValue := ⟨630043, pr630043⟩
private theorem pr630169 : PrimeCertificate 630169 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv7,pv11,pv31]) (by decide +kernel)
def pv630169 : PrimeValue := ⟨630169, pr630169⟩
private theorem pr630299 : PrimeCertificate 630299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89,pv3541]) (by decide +kernel)
def pv630299 : PrimeValue := ⟨630299, pr630299⟩
private theorem pr630349 : PrimeCertificate 630349 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv52529]) (by decide +kernel)
def pv630349 : PrimeValue := ⟨630349, pr630349⟩
private theorem pr630433 : PrimeCertificate 630433 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv199]) (by decide +kernel)
def pv630433 : PrimeValue := ⟨630433, pr630433⟩
private theorem pr630559 : PrimeCertificate 630559 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11677]) (by decide +kernel)
def pv630559 : PrimeValue := ⟨630559, pr630559⟩
private theorem pr630589 : PrimeCertificate 630589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv7507]) (by decide +kernel)
def pv630589 : PrimeValue := ⟨630589, pr630589⟩
private theorem pr630709 : PrimeCertificate 630709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv311]) (by decide +kernel)
def pv630709 : PrimeValue := ⟨630709, pr630709⟩
private theorem pr630713 : PrimeCertificate 630713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv78839]) (by decide +kernel)
def pv630713 : PrimeValue := ⟨630713, pr630713⟩
private theorem pr630911 : PrimeCertificate 630911 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv9013]) (by decide +kernel)
def pv630911 : PrimeValue := ⟨630911, pr630911⟩
private theorem pr630967 : PrimeCertificate 630967 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv83,pv181]) (by decide +kernel)
def pv630967 : PrimeValue := ⟨630967, pr630967⟩
private theorem pr631039 : PrimeCertificate 631039 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv105173]) (by decide +kernel)
def pv631039 : PrimeValue := ⟨631039, pr631039⟩
private theorem pr631181 : PrimeCertificate 631181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv19,pv151]) (by decide +kernel)
def pv631181 : PrimeValue := ⟨631181, pr631181⟩
private theorem pr631259 : PrimeCertificate 631259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv13723]) (by decide +kernel)
def pv631259 : PrimeValue := ⟨631259, pr631259⟩
private theorem pr631271 : PrimeCertificate 631271 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv63127]) (by decide +kernel)
def pv631271 : PrimeValue := ⟨631271, pr631271⟩
private theorem pr631357 : PrimeCertificate 631357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv4783]) (by decide +kernel)
def pv631357 : PrimeValue := ⟨631357, pr631357⟩
private theorem pr631391 : PrimeCertificate 631391 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv103,pv613]) (by decide +kernel)
def pv631391 : PrimeValue := ⟨631391, pr631391⟩
private theorem pr631409 : PrimeCertificate 631409 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv31,pv67]) (by decide +kernel)
def pv631409 : PrimeValue := ⟨631409, pr631409⟩
private theorem pr631429 : PrimeCertificate 631429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv7517]) (by decide +kernel)
def pv631429 : PrimeValue := ⟨631429, pr631429⟩
private theorem pr631469 : PrimeCertificate 631469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv157867]) (by decide +kernel)
def pv631469 : PrimeValue := ⟨631469, pr631469⟩
private theorem pr631483 : PrimeCertificate 631483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv41,pv151]) (by decide +kernel)
def pv631483 : PrimeValue := ⟨631483, pr631483⟩
private theorem pr631549 : PrimeCertificate 631549 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv53,pv331]) (by decide +kernel)
def pv631549 : PrimeValue := ⟨631549, pr631549⟩
private theorem pr631619 : PrimeCertificate 631619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv17,pv1429]) (by decide +kernel)
def pv631619 : PrimeValue := ⟨631619, pr631619⟩
private theorem pr631717 : PrimeCertificate 631717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61,pv863]) (by decide +kernel)
def pv631717 : PrimeValue := ⟨631717, pr631717⟩
private theorem pr631723 : PrimeCertificate 631723 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv89]) (by decide +kernel)
def pv631723 : PrimeValue := ⟨631723, pr631723⟩
private theorem pr631751 : PrimeCertificate 631751 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv7,pv19]) (by decide +kernel)
def pv631751 : PrimeValue := ⟨631751, pr631751⟩
private theorem pr631753 : PrimeCertificate 631753 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv2393]) (by decide +kernel)
def pv631753 : PrimeValue := ⟨631753, pr631753⟩
private theorem pr631789 : PrimeCertificate 631789 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv17,pv19,pv163]) (by decide +kernel)
def pv631789 : PrimeValue := ⟨631789, pr631789⟩
private theorem pr631819 : PrimeCertificate 631819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv3191]) (by decide +kernel)
def pv631819 : PrimeValue := ⟨631819, pr631819⟩
private theorem pr631901 : PrimeCertificate 631901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv71,pv89]) (by decide +kernel)
def pv631901 : PrimeValue := ⟨631901, pr631901⟩
private theorem pr631931 : PrimeCertificate 631931 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv4861]) (by decide +kernel)
def pv631931 : PrimeValue := ⟨631931, pr631931⟩
private theorem pr631987 : PrimeCertificate 631987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv105331]) (by decide +kernel)
def pv631987 : PrimeValue := ⟨631987, pr631987⟩
private theorem pr632257 : PrimeCertificate 632257 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv37,pv89]) (by decide +kernel)
def pv632257 : PrimeValue := ⟨632257, pr632257⟩
private theorem pr632321 : PrimeCertificate 632321 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv19]) (by decide +kernel)
def pv632321 : PrimeValue := ⟨632321, pr632321⟩
private theorem pr632381 : PrimeCertificate 632381 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv4517]) (by decide +kernel)
def pv632381 : PrimeValue := ⟨632381, pr632381⟩
private theorem pr632389 : PrimeCertificate 632389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv151,pv349]) (by decide +kernel)
def pv632389 : PrimeValue := ⟨632389, pr632389⟩
private theorem pr632393 : PrimeCertificate 632393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv137,pv577]) (by decide +kernel)
def pv632393 : PrimeValue := ⟨632393, pr632393⟩
private theorem pr632473 : PrimeCertificate 632473 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv73]) (by decide +kernel)
def pv632473 : PrimeValue := ⟨632473, pr632473⟩
private theorem pr632503 : PrimeCertificate 632503 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv17,pv53]) (by decide +kernel)
def pv632503 : PrimeValue := ⟨632503, pr632503⟩
private theorem pr632677 : PrimeCertificate 632677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv4793]) (by decide +kernel)
def pv632677 : PrimeValue := ⟨632677, pr632677⟩
private theorem pr632683 : PrimeCertificate 632683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv35149]) (by decide +kernel)
def pv632683 : PrimeValue := ⟨632683, pr632683⟩
private theorem pr632743 : PrimeCertificate 632743 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv9587]) (by decide +kernel)
def pv632743 : PrimeValue := ⟨632743, pr632743⟩
private theorem pr632773 : PrimeCertificate 632773 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv31]) (by decide +kernel)
def pv632773 : PrimeValue := ⟨632773, pr632773⟩
private theorem pr632993 : PrimeCertificate 632993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv131,pv151]) (by decide +kernel)
def pv632993 : PrimeValue := ⟨632993, pr632993⟩
private theorem pr633053 : PrimeCertificate 633053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv23,pv983]) (by decide +kernel)
def pv633053 : PrimeValue := ⟨633053, pr633053⟩
private theorem pr633161 : PrimeCertificate 633161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv1439]) (by decide +kernel)
def pv633161 : PrimeValue := ⟨633161, pr633161⟩
private theorem pr633263 : PrimeCertificate 633263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv45233]) (by decide +kernel)
def pv633263 : PrimeValue := ⟨633263, pr633263⟩
private theorem pr633359 : PrimeCertificate 633359 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv28789]) (by decide +kernel)
def pv633359 : PrimeValue := ⟨633359, pr633359⟩
private theorem pr633383 : PrimeCertificate 633383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv316691]) (by decide +kernel)
def pv633383 : PrimeValue := ⟨633383, pr633383⟩
private theorem pr633427 : PrimeCertificate 633427 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv193,pv547]) (by decide +kernel)
def pv633427 : PrimeValue := ⟨633427, pr633427⟩
private theorem pr633449 : PrimeCertificate 633449 :=
  certifyPrime (q := pv3) (ls := [pv2,pv79181]) (by decide +kernel)
def pv633449 : PrimeValue := ⟨633449, pr633449⟩
private theorem pr633559 : PrimeCertificate 633559 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv4591]) (by decide +kernel)
def pv633559 : PrimeValue := ⟨633559, pr633559⟩
private theorem pr633599 : PrimeCertificate 633599 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv167,pv271]) (by decide +kernel)
def pv633599 : PrimeValue := ⟨633599, pr633599⟩
private theorem pr633653 : PrimeCertificate 633653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv157,pv1009]) (by decide +kernel)
def pv633653 : PrimeValue := ⟨633653, pr633653⟩
private theorem pr633739 : PrimeCertificate 633739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv79,pv191]) (by decide +kernel)
def pv633739 : PrimeValue := ⟨633739, pr633739⟩
private theorem pr633823 : PrimeCertificate 633823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv15091]) (by decide +kernel)
def pv633823 : PrimeValue := ⟨633823, pr633823⟩
private theorem pr633953 : PrimeCertificate 633953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv1801]) (by decide +kernel)
def pv633953 : PrimeValue := ⟨633953, pr633953⟩
private theorem pr634003 : PrimeCertificate 634003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv105667]) (by decide +kernel)
def pv634003 : PrimeValue := ⟨634003, pr634003⟩
private theorem pr634103 : PrimeCertificate 634103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv45293]) (by decide +kernel)
def pv634103 : PrimeValue := ⟨634103, pr634103⟩
private theorem pr634223 : PrimeCertificate 634223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv67,pv4733]) (by decide +kernel)
def pv634223 : PrimeValue := ⟨634223, pr634223⟩
private theorem pr634313 : PrimeCertificate 634313 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv47,pv241]) (by decide +kernel)
def pv634313 : PrimeValue := ⟨634313, pr634313⟩
private theorem pr634373 : PrimeCertificate 634373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv19,pv491]) (by decide +kernel)
def pv634373 : PrimeValue := ⟨634373, pr634373⟩
private theorem pr634421 : PrimeCertificate 634421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31721]) (by decide +kernel)
def pv634421 : PrimeValue := ⟨634421, pr634421⟩
private theorem pr634573 : PrimeCertificate 634573 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17627]) (by decide +kernel)
def pv634573 : PrimeValue := ⟨634573, pr634573⟩
private theorem pr634643 : PrimeCertificate 634643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv317321]) (by decide +kernel)
def pv634643 : PrimeValue := ⟨634643, pr634643⟩
private theorem pr634649 : PrimeCertificate 634649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv1619]) (by decide +kernel)
def pv634649 : PrimeValue := ⟨634649, pr634649⟩
private theorem pr634687 : PrimeCertificate 634687 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv79,pv103]) (by decide +kernel)
def pv634687 : PrimeValue := ⟨634687, pr634687⟩
private theorem pr634841 : PrimeCertificate 634841 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv59,pv269]) (by decide +kernel)
def pv634841 : PrimeValue := ⟨634841, pr634841⟩
private theorem pr634871 : PrimeCertificate 634871 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv63487]) (by decide +kernel)
def pv634871 : PrimeValue := ⟨634871, pr634871⟩
private theorem pr635039 : PrimeCertificate 635039 :=
  certifyPrime (q := pv11) (ls := [pv2,pv149,pv2131]) (by decide +kernel)
def pv635039 : PrimeValue := ⟨635039, pr635039⟩
private theorem pr635051 : PrimeCertificate 635051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv977]) (by decide +kernel)
def pv635051 : PrimeValue := ⟨635051, pr635051⟩
private theorem pr635149 : PrimeCertificate 635149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5881]) (by decide +kernel)
def pv635149 : PrimeValue := ⟨635149, pr635149⟩
private theorem pr635197 : PrimeCertificate 635197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv1231]) (by decide +kernel)
def pv635197 : PrimeValue := ⟨635197, pr635197⟩
private theorem pr635249 : PrimeCertificate 635249 :=
  certifyPrime (q := pv3) (ls := [pv2,pv39703]) (by decide +kernel)
def pv635249 : PrimeValue := ⟨635249, pr635249⟩
private theorem pr635263 : PrimeCertificate 635263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv239,pv443]) (by decide +kernel)
def pv635263 : PrimeValue := ⟨635263, pr635263⟩
private theorem pr635279 : PrimeCertificate 635279 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv45377]) (by decide +kernel)
def pv635279 : PrimeValue := ⟨635279, pr635279⟩
private theorem pr635293 : PrimeCertificate 635293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv2521]) (by decide +kernel)
def pv635293 : PrimeValue := ⟨635293, pr635293⟩
private theorem pr635333 : PrimeCertificate 635333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv5477]) (by decide +kernel)
def pv635333 : PrimeValue := ⟨635333, pr635333⟩
private theorem pr635339 : PrimeCertificate 635339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv28879]) (by decide +kernel)
def pv635339 : PrimeValue := ⟨635339, pr635339⟩
private theorem pr635471 : PrimeCertificate 635471 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv11,pv53,pv109]) (by decide +kernel)
def pv635471 : PrimeValue := ⟨635471, pr635471⟩
private theorem pr635527 : PrimeCertificate 635527 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv3923]) (by decide +kernel)
def pv635527 : PrimeValue := ⟨635527, pr635527⟩
private theorem pr635707 : PrimeCertificate 635707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv35317]) (by decide +kernel)
def pv635707 : PrimeValue := ⟨635707, pr635707⟩
private theorem pr635801 : PrimeCertificate 635801 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv17]) (by decide +kernel)
def pv635801 : PrimeValue := ⟨635801, pr635801⟩
private theorem pr635809 : PrimeCertificate 635809 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv37,pv179]) (by decide +kernel)
def pv635809 : PrimeValue := ⟨635809, pr635809⟩
private theorem pr635893 : PrimeCertificate 635893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv2789]) (by decide +kernel)
def pv635893 : PrimeValue := ⟨635893, pr635893⟩
private theorem pr635969 : PrimeCertificate 635969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv523]) (by decide +kernel)
def pv635969 : PrimeValue := ⟨635969, pr635969⟩
private theorem pr636073 : PrimeCertificate 636073 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv17,pv1559]) (by decide +kernel)
def pv636073 : PrimeValue := ⟨636073, pr636073⟩
private theorem pr636313 : PrimeCertificate 636313 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv26513]) (by decide +kernel)
def pv636313 : PrimeValue := ⟨636313, pr636313⟩
private theorem pr636553 : PrimeCertificate 636553 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv421]) (by decide +kernel)
def pv636553 : PrimeValue := ⟨636553, pr636553⟩
private theorem pr636563 : PrimeCertificate 636563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv318281]) (by decide +kernel)
def pv636563 : PrimeValue := ⟨636563, pr636563⟩
private theorem pr636731 : PrimeCertificate 636731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41,pv1553]) (by decide +kernel)
def pv636731 : PrimeValue := ⟨636731, pr636731⟩
private theorem pr636749 : PrimeCertificate 636749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv22741]) (by decide +kernel)
def pv636749 : PrimeValue := ⟨636749, pr636749⟩
private theorem pr636953 : PrimeCertificate 636953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv103,pv773]) (by decide +kernel)
def pv636953 : PrimeValue := ⟨636953, pr636953⟩
private theorem pr636997 : PrimeCertificate 636997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv109,pv487]) (by decide +kernel)
def pv636997 : PrimeValue := ⟨636997, pr636997⟩
private theorem pr637129 : PrimeCertificate 637129 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv8849]) (by decide +kernel)
def pv637129 : PrimeValue := ⟨637129, pr637129⟩
private theorem pr637309 : PrimeCertificate 637309 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv281]) (by decide +kernel)
def pv637309 : PrimeValue := ⟨637309, pr637309⟩
private theorem pr637339 : PrimeCertificate 637339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv8171]) (by decide +kernel)
def pv637339 : PrimeValue := ⟨637339, pr637339⟩
private theorem pr637379 : PrimeCertificate 637379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv53,pv859]) (by decide +kernel)
def pv637379 : PrimeValue := ⟨637379, pr637379⟩
private theorem pr637601 : PrimeCertificate 637601 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv797]) (by decide +kernel)
def pv637601 : PrimeValue := ⟨637601, pr637601⟩
private theorem pr637751 : PrimeCertificate 637751 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv2551]) (by decide +kernel)
def pv637751 : PrimeValue := ⟨637751, pr637751⟩
private theorem pr637781 : PrimeCertificate 637781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv13,pv223]) (by decide +kernel)
def pv637781 : PrimeValue := ⟨637781, pr637781⟩
private theorem pr637841 : PrimeCertificate 637841 :=
  certifyPrime (q := pv29) (ls := [pv2,pv5,pv7,pv17,pv67]) (by decide +kernel)
def pv637841 : PrimeValue := ⟨637841, pr637841⟩
private theorem pr637933 : PrimeCertificate 637933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53161]) (by decide +kernel)
def pv637933 : PrimeValue := ⟨637933, pr637933⟩
private theorem pr638051 : PrimeCertificate 638051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv1823]) (by decide +kernel)
def pv638051 : PrimeValue := ⟨638051, pr638051⟩
private theorem pr638179 : PrimeCertificate 638179 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv106363]) (by decide +kernel)
def pv638179 : PrimeValue := ⟨638179, pr638179⟩
private theorem pr638263 : PrimeCertificate 638263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv59,pv601]) (by decide +kernel)
def pv638263 : PrimeValue := ⟨638263, pr638263⟩
private theorem pr638347 : PrimeCertificate 638347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv106391]) (by decide +kernel)
def pv638347 : PrimeValue := ⟨638347, pr638347⟩
private theorem pr638467 : PrimeCertificate 638467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv106411]) (by decide +kernel)
def pv638467 : PrimeValue := ⟨638467, pr638467⟩
private theorem pr638527 : PrimeCertificate 638527 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv23,pv661]) (by decide +kernel)
def pv638527 : PrimeValue := ⟨638527, pr638527⟩
private theorem pr638633 : PrimeCertificate 638633 :=
  certifyPrime (q := pv3) (ls := [pv2,pv79829]) (by decide +kernel)
def pv638633 : PrimeValue := ⟨638633, pr638633⟩
private theorem pr638689 : PrimeCertificate 638689 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv6653]) (by decide +kernel)
def pv638689 : PrimeValue := ⟨638689, pr638689⟩
private theorem pr638857 : PrimeCertificate 638857 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv19,pv467]) (by decide +kernel)
def pv638857 : PrimeValue := ⟨638857, pr638857⟩
private theorem pr638861 : PrimeCertificate 638861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv1879]) (by decide +kernel)
def pv638861 : PrimeValue := ⟨638861, pr638861⟩
private theorem pr638933 : PrimeCertificate 638933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv19,pv1201]) (by decide +kernel)
def pv638933 : PrimeValue := ⟨638933, pr638933⟩
private theorem pr638959 : PrimeCertificate 638959 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv109,pv977]) (by decide +kernel)
def pv638959 : PrimeValue := ⟨638959, pr638959⟩
private theorem pr639053 : PrimeCertificate 639053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv159763]) (by decide +kernel)
def pv639053 : PrimeValue := ⟨639053, pr639053⟩
private theorem pr639143 : PrimeCertificate 639143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv71,pv643]) (by decide +kernel)
def pv639143 : PrimeValue := ⟨639143, pr639143⟩
private theorem pr639253 : PrimeCertificate 639253 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1973]) (by decide +kernel)
def pv639253 : PrimeValue := ⟨639253, pr639253⟩
private theorem pr639263 : PrimeCertificate 639263 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv23,pv1069]) (by decide +kernel)
def pv639263 : PrimeValue := ⟨639263, pr639263⟩
private theorem pr639311 : PrimeCertificate 639311 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv7,pv9133]) (by decide +kernel)
def pv639311 : PrimeValue := ⟨639311, pr639311⟩
private theorem pr639329 : PrimeCertificate 639329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19979]) (by decide +kernel)
def pv639329 : PrimeValue := ⟨639329, pr639329⟩
private theorem pr639439 : PrimeCertificate 639439 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv17,pv6269]) (by decide +kernel)
def pv639439 : PrimeValue := ⟨639439, pr639439⟩
private theorem pr639491 : PrimeCertificate 639491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv63949]) (by decide +kernel)
def pv639491 : PrimeValue := ⟨639491, pr639491⟩
private theorem pr639547 : PrimeCertificate 639547 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv106591]) (by decide +kernel)
def pv639547 : PrimeValue := ⟨639547, pr639547⟩
private theorem pr639703 : PrimeCertificate 639703 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv5077]) (by decide +kernel)
def pv639703 : PrimeValue := ⟨639703, pr639703⟩
private theorem pr639713 : PrimeCertificate 639713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19991]) (by decide +kernel)
def pv639713 : PrimeValue := ⟨639713, pr639713⟩
private theorem pr639833 : PrimeCertificate 639833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv79979]) (by decide +kernel)
def pv639833 : PrimeValue := ⟨639833, pr639833⟩
private theorem pr639839 : PrimeCertificate 639839 :=
  certifyPrime (q := pv7) (ls := [pv2,pv319919]) (by decide +kernel)
def pv639839 : PrimeValue := ⟨639839, pr639839⟩
private theorem pr639851 : PrimeCertificate 639851 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv67,pv191]) (by decide +kernel)
def pv639851 : PrimeValue := ⟨639851, pr639851⟩
private theorem pr639911 : PrimeCertificate 639911 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv89,pv719]) (by decide +kernel)
def pv639911 : PrimeValue := ⟨639911, pr639911⟩
private theorem pr639949 : PrimeCertificate 639949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv3137]) (by decide +kernel)
def pv639949 : PrimeValue := ⟨639949, pr639949⟩
private theorem pr639959 : PrimeCertificate 639959 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv19,pv1531]) (by decide +kernel)
def pv639959 : PrimeValue := ⟨639959, pr639959⟩
private theorem pr639997 : PrimeCertificate 639997 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv19,pv401]) (by decide +kernel)
def pv639997 : PrimeValue := ⟨639997, pr639997⟩
private theorem pr640039 : PrimeCertificate 640039 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv311]) (by decide +kernel)
def pv640039 : PrimeValue := ⟨640039, pr640039⟩
private theorem pr640249 : PrimeCertificate 640249 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv7,pv37,pv103]) (by decide +kernel)
def pv640249 : PrimeValue := ⟨640249, pr640249⟩
private theorem pr640259 : PrimeCertificate 640259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv113,pv2833]) (by decide +kernel)
def pv640259 : PrimeValue := ⟨640259, pr640259⟩
private theorem pr640579 : PrimeCertificate 640579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv241,pv443]) (by decide +kernel)
def pv640579 : PrimeValue := ⟨640579, pr640579⟩
private theorem pr640583 : PrimeCertificate 640583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv320291]) (by decide +kernel)
def pv640583 : PrimeValue := ⟨640583, pr640583⟩
private theorem pr640631 : PrimeCertificate 640631 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv64063]) (by decide +kernel)
def pv640631 : PrimeValue := ⟨640631, pr640631⟩
private theorem pr640691 : PrimeCertificate 640691 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv79,pv811]) (by decide +kernel)
def pv640691 : PrimeValue := ⟨640691, pr640691⟩
private theorem pr640777 : PrimeCertificate 640777 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv26699]) (by decide +kernel)
def pv640777 : PrimeValue := ⟨640777, pr640777⟩
private theorem pr640793 : PrimeCertificate 640793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv173,pv463]) (by decide +kernel)
def pv640793 : PrimeValue := ⟨640793, pr640793⟩
private theorem pr640873 : PrimeCertificate 640873 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv43]) (by decide +kernel)
def pv640873 : PrimeValue := ⟨640873, pr640873⟩
private theorem pr640901 : PrimeCertificate 640901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv17,pv29]) (by decide +kernel)
def pv640901 : PrimeValue := ⟨640901, pr640901⟩
private theorem pr640933 : PrimeCertificate 640933 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv53411]) (by decide +kernel)
def pv640933 : PrimeValue := ⟨640933, pr640933⟩
private theorem pr640949 : PrimeCertificate 640949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv2081]) (by decide +kernel)
def pv640949 : PrimeValue := ⟨640949, pr640949⟩
private theorem pr641083 : PrimeCertificate 641083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv8219]) (by decide +kernel)
def pv641083 : PrimeValue := ⟨641083, pr641083⟩
private theorem pr641093 : PrimeCertificate 641093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv83,pv1931]) (by decide +kernel)
def pv641093 : PrimeValue := ⟨641093, pr641093⟩
private theorem pr641167 : PrimeCertificate 641167 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv106861]) (by decide +kernel)
def pv641167 : PrimeValue := ⟨641167, pr641167⟩
private theorem pr641203 : PrimeCertificate 641203 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv106867]) (by decide +kernel)
def pv641203 : PrimeValue := ⟨641203, pr641203⟩
private theorem pr641213 : PrimeCertificate 641213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13,pv19,pv59]) (by decide +kernel)
def pv641213 : PrimeValue := ⟨641213, pr641213⟩
private theorem pr641239 : PrimeCertificate 641239 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv8221]) (by decide +kernel)
def pv641239 : PrimeValue := ⟨641239, pr641239⟩
private theorem pr641287 : PrimeCertificate 641287 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv1549]) (by decide +kernel)
def pv641287 : PrimeValue := ⟨641287, pr641287⟩
private theorem pr641453 : PrimeCertificate 641453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv31,pv739]) (by decide +kernel)
def pv641453 : PrimeValue := ⟨641453, pr641453⟩
private theorem pr641471 : PrimeCertificate 641471 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv23,pv2789]) (by decide +kernel)
def pv641471 : PrimeValue := ⟨641471, pr641471⟩
private theorem pr641479 : PrimeCertificate 641479 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv17,pv19,pv331]) (by decide +kernel)
def pv641479 : PrimeValue := ⟨641479, pr641479⟩
private theorem pr641513 : PrimeCertificate 641513 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv53,pv89]) (by decide +kernel)
def pv641513 : PrimeValue := ⟨641513, pr641513⟩
private theorem pr641549 : PrimeCertificate 641549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv160387]) (by decide +kernel)
def pv641549 : PrimeValue := ⟨641549, pr641549⟩
private theorem pr641579 : PrimeCertificate 641579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv45827]) (by decide +kernel)
def pv641579 : PrimeValue := ⟨641579, pr641579⟩
private theorem pr641749 : PrimeCertificate 641749 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv53479]) (by decide +kernel)
def pv641749 : PrimeValue := ⟨641749, pr641749⟩
private theorem pr641833 : PrimeCertificate 641833 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv47,pv569]) (by decide +kernel)
def pv641833 : PrimeValue := ⟨641833, pr641833⟩
private theorem pr641923 : PrimeCertificate 641923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv83,pv1289]) (by decide +kernel)
def pv641923 : PrimeValue := ⟨641923, pr641923⟩
private theorem pr641969 : PrimeCertificate 641969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv40123]) (by decide +kernel)
def pv641969 : PrimeValue := ⟨641969, pr641969⟩
private theorem pr642049 : PrimeCertificate 642049 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv11,pv19]) (by decide +kernel)
def pv642049 : PrimeValue := ⟨642049, pr642049⟩
private theorem pr642163 : PrimeCertificate 642163 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv43,pv131]) (by decide +kernel)
def pv642163 : PrimeValue := ⟨642163, pr642163⟩
private theorem pr642217 : PrimeCertificate 642217 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv26759]) (by decide +kernel)
def pv642217 : PrimeValue := ⟨642217, pr642217⟩
private theorem pr642233 : PrimeCertificate 642233 :=
  certifyPrime (q := pv3) (ls := [pv2,pv80279]) (by decide +kernel)
def pv642233 : PrimeValue := ⟨642233, pr642233⟩
private theorem pr642253 : PrimeCertificate 642253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv23,pv179]) (by decide +kernel)
def pv642253 : PrimeValue := ⟨642253, pr642253⟩
private theorem pr642517 : PrimeCertificate 642517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv7649]) (by decide +kernel)
def pv642517 : PrimeValue := ⟨642517, pr642517⟩
private theorem pr642547 : PrimeCertificate 642547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv73,pv163]) (by decide +kernel)
def pv642547 : PrimeValue := ⟨642547, pr642547⟩
private theorem pr642623 : PrimeCertificate 642623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv321311]) (by decide +kernel)
def pv642623 : PrimeValue := ⟨642623, pr642623⟩
private theorem pr642673 : PrimeCertificate 642673 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv4463]) (by decide +kernel)
def pv642673 : PrimeValue := ⟨642673, pr642673⟩
private theorem pr642739 : PrimeCertificate 642739 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv107123]) (by decide +kernel)
def pv642739 : PrimeValue := ⟨642739, pr642739⟩
private theorem pr642799 : PrimeCertificate 642799 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv41,pv67]) (by decide +kernel)
def pv642799 : PrimeValue := ⟨642799, pr642799⟩
private theorem pr642809 : PrimeCertificate 642809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv4229]) (by decide +kernel)
def pv642809 : PrimeValue := ⟨642809, pr642809⟩
private theorem pr642877 : PrimeCertificate 642877 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv317]) (by decide +kernel)
def pv642877 : PrimeValue := ⟨642877, pr642877⟩
private theorem pr642881 : PrimeCertificate 642881 :=
  certifyPrime (q := pv47) (ls := [pv2,pv5,pv7,pv41]) (by decide +kernel)
def pv642881 : PrimeValue := ⟨642881, pr642881⟩
private theorem pr642899 : PrimeCertificate 642899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv321449]) (by decide +kernel)
def pv642899 : PrimeValue := ⟨642899, pr642899⟩
private theorem pr642973 : PrimeCertificate 642973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv4871]) (by decide +kernel)
def pv642973 : PrimeValue := ⟨642973, pr642973⟩
private theorem pr643073 : PrimeCertificate 643073 :=
  certifyPrime (q := pv3) (ls := [pv2,pv157]) (by decide +kernel)
def pv643073 : PrimeValue := ⟨643073, pr643073⟩
private theorem pr643099 : PrimeCertificate 643099 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv107183]) (by decide +kernel)
def pv643099 : PrimeValue := ⟨643099, pr643099⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
