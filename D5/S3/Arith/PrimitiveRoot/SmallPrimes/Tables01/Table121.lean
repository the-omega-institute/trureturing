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

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr624763 : Nat.Prime 624763 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv61,pv569]) (by decide +kernel)
def pv624763 : PrimeValue := ⟨624763, pr624763⟩
private theorem pr624787 : Nat.Prime 624787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv101,pv1031]) (by decide +kernel)
def pv624787 : PrimeValue := ⟨624787, pr624787⟩
private theorem pr624847 : Nat.Prime 624847 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv223,pv467]) (by decide +kernel)
def pv624847 : PrimeValue := ⟨624847, pr624847⟩
private theorem pr624997 : Nat.Prime 624997 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv643]) (by decide +kernel)
def pv624997 : PrimeValue := ⟨624997, pr624997⟩
private theorem pr625253 : Nat.Prime 625253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv433]) (by decide +kernel)
def pv625253 : PrimeValue := ⟨625253, pr625253⟩
private theorem pr625489 : Nat.Prime 625489 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv83,pv157]) (by decide +kernel)
def pv625489 : PrimeValue := ⟨625489, pr625489⟩
private theorem pr625543 : Nat.Prime 625543 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv137,pv761]) (by decide +kernel)
def pv625543 : PrimeValue := ⟨625543, pr625543⟩
private theorem pr625589 : Nat.Prime 625589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv5393]) (by decide +kernel)
def pv625589 : PrimeValue := ⟨625589, pr625589⟩
private theorem pr625643 : Nat.Prime 625643 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv10091]) (by decide +kernel)
def pv625643 : PrimeValue := ⟨625643, pr625643⟩
private theorem pr625657 : Nat.Prime 625657 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv131,pv199]) (by decide +kernel)
def pv625657 : PrimeValue := ⟨625657, pr625657⟩
private theorem pr625661 : Nat.Prime 625661 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv41,pv109]) (by decide +kernel)
def pv625661 : PrimeValue := ⟨625661, pr625661⟩
private theorem pr625763 : Nat.Prime 625763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv10789]) (by decide +kernel)
def pv625763 : PrimeValue := ⟨625763, pr625763⟩
private theorem pr625871 : Nat.Prime 625871 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv8941]) (by decide +kernel)
def pv625871 : PrimeValue := ⟨625871, pr625871⟩
private theorem pr625909 : Nat.Prime 625909 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv43,pv1213]) (by decide +kernel)
def pv625909 : PrimeValue := ⟨625909, pr625909⟩
private theorem pr625913 : Nat.Prime 625913 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv11177]) (by decide +kernel)
def pv625913 : PrimeValue := ⟨625913, pr625913⟩
private theorem pr626051 : Nat.Prime 626051 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19,pv659]) (by decide +kernel)
def pv626051 : PrimeValue := ⟨626051, pr626051⟩
private theorem pr626173 : Nat.Prime 626173 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv52181]) (by decide +kernel)
def pv626173 : PrimeValue := ⟨626173, pr626173⟩
private theorem pr626201 : Nat.Prime 626201 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv31,pv101]) (by decide +kernel)
def pv626201 : PrimeValue := ⟨626201, pr626201⟩
private theorem pr626261 : Nat.Prime 626261 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv173,pv181]) (by decide +kernel)
def pv626261 : PrimeValue := ⟨626261, pr626261⟩
private theorem pr626389 : Nat.Prime 626389 :=
  checkPrime_prime (q := pv47) (ls := [pv2,pv3,pv7,pv7457]) (by decide +kernel)
def pv626389 : PrimeValue := ⟨626389, pr626389⟩
private theorem pr626443 : Nat.Prime 626443 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv131,pv797]) (by decide +kernel)
def pv626443 : PrimeValue := ⟨626443, pr626443⟩
private theorem pr626599 : Nat.Prime 626599 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv4973]) (by decide +kernel)
def pv626599 : PrimeValue := ⟨626599, pr626599⟩
private theorem pr626663 : Nat.Prime 626663 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv313331]) (by decide +kernel)
def pv626663 : PrimeValue := ⟨626663, pr626663⟩
private theorem pr626749 : Nat.Prime 626749 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv29,pv1801]) (by decide +kernel)
def pv626749 : PrimeValue := ⟨626749, pr626749⟩
private theorem pr626861 : Nat.Prime 626861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv2411]) (by decide +kernel)
def pv626861 : PrimeValue := ⟨626861, pr626861⟩
private theorem pr626959 : Nat.Prime 626959 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv61,pv571]) (by decide +kernel)
def pv626959 : PrimeValue := ⟨626959, pr626959⟩
private theorem pr627059 : Nat.Prime 627059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv157,pv1997]) (by decide +kernel)
def pv627059 : PrimeValue := ⟨627059, pr627059⟩
private theorem pr627073 : Nat.Prime 627073 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv23,pv71]) (by decide +kernel)
def pv627073 : PrimeValue := ⟨627073, pr627073⟩
private theorem pr627089 : Nat.Prime 627089 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv11,pv509]) (by decide +kernel)
def pv627089 : PrimeValue := ⟨627089, pr627089⟩
private theorem pr627101 : Nat.Prime 627101 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv6271]) (by decide +kernel)
def pv627101 : PrimeValue := ⟨627101, pr627101⟩
private theorem pr627139 : Nat.Prime 627139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv34841]) (by decide +kernel)
def pv627139 : PrimeValue := ⟨627139, pr627139⟩
private theorem pr627169 : Nat.Prime 627169 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv47,pv139]) (by decide +kernel)
def pv627169 : PrimeValue := ⟨627169, pr627169⟩
private theorem pr627251 : Nat.Prime 627251 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv193]) (by decide +kernel)
def pv627251 : PrimeValue := ⟨627251, pr627251⟩
private theorem pr627379 : Nat.Prime 627379 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv3373]) (by decide +kernel)
def pv627379 : PrimeValue := ⟨627379, pr627379⟩
private theorem pr627383 : Nat.Prime 627383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv41,pv1093]) (by decide +kernel)
def pv627383 : PrimeValue := ⟨627383, pr627383⟩
private theorem pr627449 : Nat.Prime 627449 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv107,pv733]) (by decide +kernel)
def pv627449 : PrimeValue := ⟨627449, pr627449⟩
private theorem pr627479 : Nat.Prime 627479 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv313739]) (by decide +kernel)
def pv627479 : PrimeValue := ⟨627479, pr627479⟩
private theorem pr627491 : Nat.Prime 627491 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv131,pv479]) (by decide +kernel)
def pv627491 : PrimeValue := ⟨627491, pr627491⟩
private theorem pr627593 : Nat.Prime 627593 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv1601]) (by decide +kernel)
def pv627593 : PrimeValue := ⟨627593, pr627593⟩
private theorem pr627619 : Nat.Prime 627619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv3607]) (by decide +kernel)
def pv627619 : PrimeValue := ⟨627619, pr627619⟩
private theorem pr627637 : Nat.Prime 627637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv193,pv271]) (by decide +kernel)
def pv627637 : PrimeValue := ⟨627637, pr627637⟩
private theorem pr627787 : Nat.Prime 627787 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv34877]) (by decide +kernel)
def pv627787 : PrimeValue := ⟨627787, pr627787⟩
private theorem pr627953 : Nat.Prime 627953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv3019]) (by decide +kernel)
def pv627953 : PrimeValue := ⟨627953, pr627953⟩
private theorem pr628057 : Nat.Prime 628057 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv13,pv61]) (by decide +kernel)
def pv628057 : PrimeValue := ⟨628057, pr628057⟩
private theorem pr628139 : Nat.Prime 628139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv44867]) (by decide +kernel)
def pv628139 : PrimeValue := ⟨628139, pr628139⟩
private theorem pr628289 : Nat.Prime 628289 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv9817]) (by decide +kernel)
def pv628289 : PrimeValue := ⟨628289, pr628289⟩
private theorem pr628373 : Nat.Prime 628373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv5417]) (by decide +kernel)
def pv628373 : PrimeValue := ⟨628373, pr628373⟩
private theorem pr628679 : Nat.Prime 628679 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv314339]) (by decide +kernel)
def pv628679 : PrimeValue := ⟨628679, pr628679⟩
private theorem pr628753 : Nat.Prime 628753 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13099]) (by decide +kernel)
def pv628753 : PrimeValue := ⟨628753, pr628753⟩
private theorem pr628781 : Nat.Prime 628781 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv149,pv211]) (by decide +kernel)
def pv628781 : PrimeValue := ⟨628781, pr628781⟩
private theorem pr628913 : Nat.Prime 628913 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv1709]) (by decide +kernel)
def pv628913 : PrimeValue := ⟨628913, pr628913⟩
private theorem pr628939 : Nat.Prime 628939 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv613]) (by decide +kernel)
def pv628939 : PrimeValue := ⟨628939, pr628939⟩
private theorem pr629081 : Nat.Prime 629081 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv15727]) (by decide +kernel)
def pv629081 : PrimeValue := ⟨629081, pr629081⟩
private theorem pr629143 : Nat.Prime 629143 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv47,pv97]) (by decide +kernel)
def pv629143 : PrimeValue := ⟨629143, pr629143⟩
private theorem pr629171 : Nat.Prime 629171 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv3701]) (by decide +kernel)
def pv629171 : PrimeValue := ⟨629171, pr629171⟩
private theorem pr629243 : Nat.Prime 629243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv29,pv571]) (by decide +kernel)
def pv629243 : PrimeValue := ⟨629243, pr629243⟩
private theorem pr629383 : Nat.Prime 629383 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv13,pv8069]) (by decide +kernel)
def pv629383 : PrimeValue := ⟨629383, pr629383⟩
private theorem pr629449 : Nat.Prime 629449 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv26227]) (by decide +kernel)
def pv629449 : PrimeValue := ⟨629449, pr629449⟩
private theorem pr629467 : Nat.Prime 629467 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv104911]) (by decide +kernel)
def pv629467 : PrimeValue := ⟨629467, pr629467⟩
private theorem pr629483 : Nat.Prime 629483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv44963]) (by decide +kernel)
def pv629483 : PrimeValue := ⟨629483, pr629483⟩
private theorem pr629623 : Nat.Prime 629623 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv19,pv263]) (by decide +kernel)
def pv629623 : PrimeValue := ⟨629623, pr629623⟩
private theorem pr629737 : Nat.Prime 629737 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv1381]) (by decide +kernel)
def pv629737 : PrimeValue := ⟨629737, pr629737⟩
private theorem pr629743 : Nat.Prime 629743 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv103,pv1019]) (by decide +kernel)
def pv629743 : PrimeValue := ⟨629743, pr629743⟩
private theorem pr629773 : Nat.Prime 629773 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv13,pv367]) (by decide +kernel)
def pv629773 : PrimeValue := ⟨629773, pr629773⟩
private theorem pr629819 : Nat.Prime 629819 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv44987]) (by decide +kernel)
def pv629819 : PrimeValue := ⟨629819, pr629819⟩
private theorem pr629899 : Nat.Prime 629899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv277,pv379]) (by decide +kernel)
def pv629899 : PrimeValue := ⟨629899, pr629899⟩
private theorem pr629963 : Nat.Prime 629963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv8513]) (by decide +kernel)
def pv629963 : PrimeValue := ⟨629963, pr629963⟩
private theorem pr630023 : Nat.Prime 630023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv315011]) (by decide +kernel)
def pv630023 : PrimeValue := ⟨630023, pr630023⟩
private theorem pr630029 : Nat.Prime 630029 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv22501]) (by decide +kernel)
def pv630029 : PrimeValue := ⟨630029, pr630029⟩
private theorem pr630043 : Nat.Prime 630043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv2143]) (by decide +kernel)
def pv630043 : PrimeValue := ⟨630043, pr630043⟩
private theorem pr630169 : Nat.Prime 630169 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv7,pv11,pv31]) (by decide +kernel)
def pv630169 : PrimeValue := ⟨630169, pr630169⟩
private theorem pr630299 : Nat.Prime 630299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv89,pv3541]) (by decide +kernel)
def pv630299 : PrimeValue := ⟨630299, pr630299⟩
private theorem pr630349 : Nat.Prime 630349 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv52529]) (by decide +kernel)
def pv630349 : PrimeValue := ⟨630349, pr630349⟩
private theorem pr630433 : Nat.Prime 630433 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv199]) (by decide +kernel)
def pv630433 : PrimeValue := ⟨630433, pr630433⟩
private theorem pr630559 : Nat.Prime 630559 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11677]) (by decide +kernel)
def pv630559 : PrimeValue := ⟨630559, pr630559⟩
private theorem pr630589 : Nat.Prime 630589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv7507]) (by decide +kernel)
def pv630589 : PrimeValue := ⟨630589, pr630589⟩
private theorem pr630709 : Nat.Prime 630709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv311]) (by decide +kernel)
def pv630709 : PrimeValue := ⟨630709, pr630709⟩
private theorem pr630713 : Nat.Prime 630713 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv78839]) (by decide +kernel)
def pv630713 : PrimeValue := ⟨630713, pr630713⟩
private theorem pr630911 : Nat.Prime 630911 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv9013]) (by decide +kernel)
def pv630911 : PrimeValue := ⟨630911, pr630911⟩
private theorem pr630967 : Nat.Prime 630967 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv83,pv181]) (by decide +kernel)
def pv630967 : PrimeValue := ⟨630967, pr630967⟩
private theorem pr631039 : Nat.Prime 631039 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv105173]) (by decide +kernel)
def pv631039 : PrimeValue := ⟨631039, pr631039⟩
private theorem pr631181 : Nat.Prime 631181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv19,pv151]) (by decide +kernel)
def pv631181 : PrimeValue := ⟨631181, pr631181⟩
private theorem pr631259 : Nat.Prime 631259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv13723]) (by decide +kernel)
def pv631259 : PrimeValue := ⟨631259, pr631259⟩
private theorem pr631271 : Nat.Prime 631271 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv63127]) (by decide +kernel)
def pv631271 : PrimeValue := ⟨631271, pr631271⟩
private theorem pr631357 : Nat.Prime 631357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv4783]) (by decide +kernel)
def pv631357 : PrimeValue := ⟨631357, pr631357⟩
private theorem pr631391 : Nat.Prime 631391 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv103,pv613]) (by decide +kernel)
def pv631391 : PrimeValue := ⟨631391, pr631391⟩
private theorem pr631409 : Nat.Prime 631409 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv31,pv67]) (by decide +kernel)
def pv631409 : PrimeValue := ⟨631409, pr631409⟩
private theorem pr631429 : Nat.Prime 631429 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv7517]) (by decide +kernel)
def pv631429 : PrimeValue := ⟨631429, pr631429⟩
private theorem pr631469 : Nat.Prime 631469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv157867]) (by decide +kernel)
def pv631469 : PrimeValue := ⟨631469, pr631469⟩
private theorem pr631483 : Nat.Prime 631483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv41,pv151]) (by decide +kernel)
def pv631483 : PrimeValue := ⟨631483, pr631483⟩
private theorem pr631549 : Nat.Prime 631549 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv53,pv331]) (by decide +kernel)
def pv631549 : PrimeValue := ⟨631549, pr631549⟩
private theorem pr631619 : Nat.Prime 631619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv17,pv1429]) (by decide +kernel)
def pv631619 : PrimeValue := ⟨631619, pr631619⟩
private theorem pr631717 : Nat.Prime 631717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv61,pv863]) (by decide +kernel)
def pv631717 : PrimeValue := ⟨631717, pr631717⟩
private theorem pr631723 : Nat.Prime 631723 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv89]) (by decide +kernel)
def pv631723 : PrimeValue := ⟨631723, pr631723⟩
private theorem pr631751 : Nat.Prime 631751 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv7,pv19]) (by decide +kernel)
def pv631751 : PrimeValue := ⟨631751, pr631751⟩
private theorem pr631753 : Nat.Prime 631753 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv11,pv2393]) (by decide +kernel)
def pv631753 : PrimeValue := ⟨631753, pr631753⟩
private theorem pr631789 : Nat.Prime 631789 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv17,pv19,pv163]) (by decide +kernel)
def pv631789 : PrimeValue := ⟨631789, pr631789⟩
private theorem pr631819 : Nat.Prime 631819 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv3191]) (by decide +kernel)
def pv631819 : PrimeValue := ⟨631819, pr631819⟩
private theorem pr631901 : Nat.Prime 631901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv71,pv89]) (by decide +kernel)
def pv631901 : PrimeValue := ⟨631901, pr631901⟩
private theorem pr631931 : Nat.Prime 631931 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv4861]) (by decide +kernel)
def pv631931 : PrimeValue := ⟨631931, pr631931⟩
private theorem pr631987 : Nat.Prime 631987 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv105331]) (by decide +kernel)
def pv631987 : PrimeValue := ⟨631987, pr631987⟩
private theorem pr632257 : Nat.Prime 632257 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv37,pv89]) (by decide +kernel)
def pv632257 : PrimeValue := ⟨632257, pr632257⟩
private theorem pr632321 : Nat.Prime 632321 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv19]) (by decide +kernel)
def pv632321 : PrimeValue := ⟨632321, pr632321⟩
private theorem pr632381 : Nat.Prime 632381 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv4517]) (by decide +kernel)
def pv632381 : PrimeValue := ⟨632381, pr632381⟩
private theorem pr632389 : Nat.Prime 632389 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv151,pv349]) (by decide +kernel)
def pv632389 : PrimeValue := ⟨632389, pr632389⟩
private theorem pr632393 : Nat.Prime 632393 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv137,pv577]) (by decide +kernel)
def pv632393 : PrimeValue := ⟨632393, pr632393⟩
private theorem pr632473 : Nat.Prime 632473 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv73]) (by decide +kernel)
def pv632473 : PrimeValue := ⟨632473, pr632473⟩
private theorem pr632503 : Nat.Prime 632503 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv17,pv53]) (by decide +kernel)
def pv632503 : PrimeValue := ⟨632503, pr632503⟩
private theorem pr632677 : Nat.Prime 632677 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv4793]) (by decide +kernel)
def pv632677 : PrimeValue := ⟨632677, pr632677⟩
private theorem pr632683 : Nat.Prime 632683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv35149]) (by decide +kernel)
def pv632683 : PrimeValue := ⟨632683, pr632683⟩
private theorem pr632743 : Nat.Prime 632743 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv9587]) (by decide +kernel)
def pv632743 : PrimeValue := ⟨632743, pr632743⟩
private theorem pr632773 : Nat.Prime 632773 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv31]) (by decide +kernel)
def pv632773 : PrimeValue := ⟨632773, pr632773⟩
private theorem pr632993 : Nat.Prime 632993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv131,pv151]) (by decide +kernel)
def pv632993 : PrimeValue := ⟨632993, pr632993⟩
private theorem pr633053 : Nat.Prime 633053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv23,pv983]) (by decide +kernel)
def pv633053 : PrimeValue := ⟨633053, pr633053⟩
private theorem pr633161 : Nat.Prime 633161 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv1439]) (by decide +kernel)
def pv633161 : PrimeValue := ⟨633161, pr633161⟩
private theorem pr633263 : Nat.Prime 633263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv45233]) (by decide +kernel)
def pv633263 : PrimeValue := ⟨633263, pr633263⟩
private theorem pr633359 : Nat.Prime 633359 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv11,pv28789]) (by decide +kernel)
def pv633359 : PrimeValue := ⟨633359, pr633359⟩
private theorem pr633383 : Nat.Prime 633383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv316691]) (by decide +kernel)
def pv633383 : PrimeValue := ⟨633383, pr633383⟩
private theorem pr633427 : Nat.Prime 633427 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv193,pv547]) (by decide +kernel)
def pv633427 : PrimeValue := ⟨633427, pr633427⟩
private theorem pr633449 : Nat.Prime 633449 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv79181]) (by decide +kernel)
def pv633449 : PrimeValue := ⟨633449, pr633449⟩
private theorem pr633559 : Nat.Prime 633559 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv4591]) (by decide +kernel)
def pv633559 : PrimeValue := ⟨633559, pr633559⟩
private theorem pr633599 : Nat.Prime 633599 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv167,pv271]) (by decide +kernel)
def pv633599 : PrimeValue := ⟨633599, pr633599⟩
private theorem pr633653 : Nat.Prime 633653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv157,pv1009]) (by decide +kernel)
def pv633653 : PrimeValue := ⟨633653, pr633653⟩
private theorem pr633739 : Nat.Prime 633739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv79,pv191]) (by decide +kernel)
def pv633739 : PrimeValue := ⟨633739, pr633739⟩
private theorem pr633823 : Nat.Prime 633823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv15091]) (by decide +kernel)
def pv633823 : PrimeValue := ⟨633823, pr633823⟩
private theorem pr633953 : Nat.Prime 633953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv1801]) (by decide +kernel)
def pv633953 : PrimeValue := ⟨633953, pr633953⟩
private theorem pr634003 : Nat.Prime 634003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv105667]) (by decide +kernel)
def pv634003 : PrimeValue := ⟨634003, pr634003⟩
private theorem pr634103 : Nat.Prime 634103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv45293]) (by decide +kernel)
def pv634103 : PrimeValue := ⟨634103, pr634103⟩
private theorem pr634223 : Nat.Prime 634223 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv67,pv4733]) (by decide +kernel)
def pv634223 : PrimeValue := ⟨634223, pr634223⟩
private theorem pr634313 : Nat.Prime 634313 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv47,pv241]) (by decide +kernel)
def pv634313 : PrimeValue := ⟨634313, pr634313⟩
private theorem pr634373 : Nat.Prime 634373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv19,pv491]) (by decide +kernel)
def pv634373 : PrimeValue := ⟨634373, pr634373⟩
private theorem pr634421 : Nat.Prime 634421 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv31721]) (by decide +kernel)
def pv634421 : PrimeValue := ⟨634421, pr634421⟩
private theorem pr634573 : Nat.Prime 634573 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17627]) (by decide +kernel)
def pv634573 : PrimeValue := ⟨634573, pr634573⟩
private theorem pr634643 : Nat.Prime 634643 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv317321]) (by decide +kernel)
def pv634643 : PrimeValue := ⟨634643, pr634643⟩
private theorem pr634649 : Nat.Prime 634649 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv1619]) (by decide +kernel)
def pv634649 : PrimeValue := ⟨634649, pr634649⟩
private theorem pr634687 : Nat.Prime 634687 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv79,pv103]) (by decide +kernel)
def pv634687 : PrimeValue := ⟨634687, pr634687⟩
private theorem pr634841 : Nat.Prime 634841 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv59,pv269]) (by decide +kernel)
def pv634841 : PrimeValue := ⟨634841, pr634841⟩
private theorem pr634871 : Nat.Prime 634871 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv63487]) (by decide +kernel)
def pv634871 : PrimeValue := ⟨634871, pr634871⟩
private theorem pr635039 : Nat.Prime 635039 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv149,pv2131]) (by decide +kernel)
def pv635039 : PrimeValue := ⟨635039, pr635039⟩
private theorem pr635051 : Nat.Prime 635051 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv977]) (by decide +kernel)
def pv635051 : PrimeValue := ⟨635051, pr635051⟩
private theorem pr635149 : Nat.Prime 635149 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5881]) (by decide +kernel)
def pv635149 : PrimeValue := ⟨635149, pr635149⟩
private theorem pr635197 : Nat.Prime 635197 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv43,pv1231]) (by decide +kernel)
def pv635197 : PrimeValue := ⟨635197, pr635197⟩
private theorem pr635249 : Nat.Prime 635249 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv39703]) (by decide +kernel)
def pv635249 : PrimeValue := ⟨635249, pr635249⟩
private theorem pr635263 : Nat.Prime 635263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv239,pv443]) (by decide +kernel)
def pv635263 : PrimeValue := ⟨635263, pr635263⟩
private theorem pr635279 : Nat.Prime 635279 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv45377]) (by decide +kernel)
def pv635279 : PrimeValue := ⟨635279, pr635279⟩
private theorem pr635293 : Nat.Prime 635293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv2521]) (by decide +kernel)
def pv635293 : PrimeValue := ⟨635293, pr635293⟩
private theorem pr635333 : Nat.Prime 635333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv5477]) (by decide +kernel)
def pv635333 : PrimeValue := ⟨635333, pr635333⟩
private theorem pr635339 : Nat.Prime 635339 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv28879]) (by decide +kernel)
def pv635339 : PrimeValue := ⟨635339, pr635339⟩
private theorem pr635471 : Nat.Prime 635471 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv11,pv53,pv109]) (by decide +kernel)
def pv635471 : PrimeValue := ⟨635471, pr635471⟩
private theorem pr635527 : Nat.Prime 635527 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv3923]) (by decide +kernel)
def pv635527 : PrimeValue := ⟨635527, pr635527⟩
private theorem pr635707 : Nat.Prime 635707 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv35317]) (by decide +kernel)
def pv635707 : PrimeValue := ⟨635707, pr635707⟩
private theorem pr635801 : Nat.Prime 635801 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv17]) (by decide +kernel)
def pv635801 : PrimeValue := ⟨635801, pr635801⟩
private theorem pr635809 : Nat.Prime 635809 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv37,pv179]) (by decide +kernel)
def pv635809 : PrimeValue := ⟨635809, pr635809⟩
private theorem pr635893 : Nat.Prime 635893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv2789]) (by decide +kernel)
def pv635893 : PrimeValue := ⟨635893, pr635893⟩
private theorem pr635969 : Nat.Prime 635969 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv523]) (by decide +kernel)
def pv635969 : PrimeValue := ⟨635969, pr635969⟩
private theorem pr636073 : Nat.Prime 636073 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv17,pv1559]) (by decide +kernel)
def pv636073 : PrimeValue := ⟨636073, pr636073⟩
private theorem pr636313 : Nat.Prime 636313 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv26513]) (by decide +kernel)
def pv636313 : PrimeValue := ⟨636313, pr636313⟩
private theorem pr636553 : Nat.Prime 636553 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv421]) (by decide +kernel)
def pv636553 : PrimeValue := ⟨636553, pr636553⟩
private theorem pr636563 : Nat.Prime 636563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv318281]) (by decide +kernel)
def pv636563 : PrimeValue := ⟨636563, pr636563⟩
private theorem pr636731 : Nat.Prime 636731 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv41,pv1553]) (by decide +kernel)
def pv636731 : PrimeValue := ⟨636731, pr636731⟩
private theorem pr636749 : Nat.Prime 636749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv22741]) (by decide +kernel)
def pv636749 : PrimeValue := ⟨636749, pr636749⟩
private theorem pr636953 : Nat.Prime 636953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv103,pv773]) (by decide +kernel)
def pv636953 : PrimeValue := ⟨636953, pr636953⟩
private theorem pr636997 : Nat.Prime 636997 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv109,pv487]) (by decide +kernel)
def pv636997 : PrimeValue := ⟨636997, pr636997⟩
private theorem pr637129 : Nat.Prime 637129 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv8849]) (by decide +kernel)
def pv637129 : PrimeValue := ⟨637129, pr637129⟩
private theorem pr637309 : Nat.Prime 637309 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv281]) (by decide +kernel)
def pv637309 : PrimeValue := ⟨637309, pr637309⟩
private theorem pr637339 : Nat.Prime 637339 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv8171]) (by decide +kernel)
def pv637339 : PrimeValue := ⟨637339, pr637339⟩
private theorem pr637379 : Nat.Prime 637379 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv53,pv859]) (by decide +kernel)
def pv637379 : PrimeValue := ⟨637379, pr637379⟩
private theorem pr637601 : Nat.Prime 637601 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv797]) (by decide +kernel)
def pv637601 : PrimeValue := ⟨637601, pr637601⟩
private theorem pr637751 : Nat.Prime 637751 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv2551]) (by decide +kernel)
def pv637751 : PrimeValue := ⟨637751, pr637751⟩
private theorem pr637781 : Nat.Prime 637781 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv13,pv223]) (by decide +kernel)
def pv637781 : PrimeValue := ⟨637781, pr637781⟩
private theorem pr637841 : Nat.Prime 637841 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv5,pv7,pv17,pv67]) (by decide +kernel)
def pv637841 : PrimeValue := ⟨637841, pr637841⟩
private theorem pr637933 : Nat.Prime 637933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv53161]) (by decide +kernel)
def pv637933 : PrimeValue := ⟨637933, pr637933⟩
private theorem pr638051 : Nat.Prime 638051 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv1823]) (by decide +kernel)
def pv638051 : PrimeValue := ⟨638051, pr638051⟩
private theorem pr638179 : Nat.Prime 638179 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv106363]) (by decide +kernel)
def pv638179 : PrimeValue := ⟨638179, pr638179⟩
private theorem pr638263 : Nat.Prime 638263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv59,pv601]) (by decide +kernel)
def pv638263 : PrimeValue := ⟨638263, pr638263⟩
private theorem pr638347 : Nat.Prime 638347 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv106391]) (by decide +kernel)
def pv638347 : PrimeValue := ⟨638347, pr638347⟩
private theorem pr638467 : Nat.Prime 638467 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv106411]) (by decide +kernel)
def pv638467 : PrimeValue := ⟨638467, pr638467⟩
private theorem pr638527 : Nat.Prime 638527 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv23,pv661]) (by decide +kernel)
def pv638527 : PrimeValue := ⟨638527, pr638527⟩
private theorem pr638633 : Nat.Prime 638633 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv79829]) (by decide +kernel)
def pv638633 : PrimeValue := ⟨638633, pr638633⟩
private theorem pr638689 : Nat.Prime 638689 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv6653]) (by decide +kernel)
def pv638689 : PrimeValue := ⟨638689, pr638689⟩
private theorem pr638857 : Nat.Prime 638857 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv19,pv467]) (by decide +kernel)
def pv638857 : PrimeValue := ⟨638857, pr638857⟩
private theorem pr638861 : Nat.Prime 638861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv1879]) (by decide +kernel)
def pv638861 : PrimeValue := ⟨638861, pr638861⟩
private theorem pr638933 : Nat.Prime 638933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv19,pv1201]) (by decide +kernel)
def pv638933 : PrimeValue := ⟨638933, pr638933⟩
private theorem pr638959 : Nat.Prime 638959 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv109,pv977]) (by decide +kernel)
def pv638959 : PrimeValue := ⟨638959, pr638959⟩
private theorem pr639053 : Nat.Prime 639053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv159763]) (by decide +kernel)
def pv639053 : PrimeValue := ⟨639053, pr639053⟩
private theorem pr639143 : Nat.Prime 639143 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv71,pv643]) (by decide +kernel)
def pv639143 : PrimeValue := ⟨639143, pr639143⟩
private theorem pr639253 : Nat.Prime 639253 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1973]) (by decide +kernel)
def pv639253 : PrimeValue := ⟨639253, pr639253⟩
private theorem pr639263 : Nat.Prime 639263 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv13,pv23,pv1069]) (by decide +kernel)
def pv639263 : PrimeValue := ⟨639263, pr639263⟩
private theorem pr639311 : Nat.Prime 639311 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv7,pv9133]) (by decide +kernel)
def pv639311 : PrimeValue := ⟨639311, pr639311⟩
private theorem pr639329 : Nat.Prime 639329 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19979]) (by decide +kernel)
def pv639329 : PrimeValue := ⟨639329, pr639329⟩
private theorem pr639439 : Nat.Prime 639439 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv17,pv6269]) (by decide +kernel)
def pv639439 : PrimeValue := ⟨639439, pr639439⟩
private theorem pr639491 : Nat.Prime 639491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv63949]) (by decide +kernel)
def pv639491 : PrimeValue := ⟨639491, pr639491⟩
private theorem pr639547 : Nat.Prime 639547 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv106591]) (by decide +kernel)
def pv639547 : PrimeValue := ⟨639547, pr639547⟩
private theorem pr639703 : Nat.Prime 639703 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv5077]) (by decide +kernel)
def pv639703 : PrimeValue := ⟨639703, pr639703⟩
private theorem pr639713 : Nat.Prime 639713 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19991]) (by decide +kernel)
def pv639713 : PrimeValue := ⟨639713, pr639713⟩
private theorem pr639833 : Nat.Prime 639833 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv79979]) (by decide +kernel)
def pv639833 : PrimeValue := ⟨639833, pr639833⟩
private theorem pr639839 : Nat.Prime 639839 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv319919]) (by decide +kernel)
def pv639839 : PrimeValue := ⟨639839, pr639839⟩
private theorem pr639851 : Nat.Prime 639851 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv67,pv191]) (by decide +kernel)
def pv639851 : PrimeValue := ⟨639851, pr639851⟩
private theorem pr639911 : Nat.Prime 639911 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv89,pv719]) (by decide +kernel)
def pv639911 : PrimeValue := ⟨639911, pr639911⟩
private theorem pr639949 : Nat.Prime 639949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv3137]) (by decide +kernel)
def pv639949 : PrimeValue := ⟨639949, pr639949⟩
private theorem pr639959 : Nat.Prime 639959 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv11,pv19,pv1531]) (by decide +kernel)
def pv639959 : PrimeValue := ⟨639959, pr639959⟩
private theorem pr639997 : Nat.Prime 639997 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv19,pv401]) (by decide +kernel)
def pv639997 : PrimeValue := ⟨639997, pr639997⟩
private theorem pr640039 : Nat.Prime 640039 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv311]) (by decide +kernel)
def pv640039 : PrimeValue := ⟨640039, pr640039⟩
private theorem pr640249 : Nat.Prime 640249 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv7,pv37,pv103]) (by decide +kernel)
def pv640249 : PrimeValue := ⟨640249, pr640249⟩
private theorem pr640259 : Nat.Prime 640259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv113,pv2833]) (by decide +kernel)
def pv640259 : PrimeValue := ⟨640259, pr640259⟩
private theorem pr640579 : Nat.Prime 640579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv241,pv443]) (by decide +kernel)
def pv640579 : PrimeValue := ⟨640579, pr640579⟩
private theorem pr640583 : Nat.Prime 640583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv320291]) (by decide +kernel)
def pv640583 : PrimeValue := ⟨640583, pr640583⟩
private theorem pr640631 : Nat.Prime 640631 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv64063]) (by decide +kernel)
def pv640631 : PrimeValue := ⟨640631, pr640631⟩
private theorem pr640691 : Nat.Prime 640691 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv79,pv811]) (by decide +kernel)
def pv640691 : PrimeValue := ⟨640691, pr640691⟩
private theorem pr640777 : Nat.Prime 640777 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv26699]) (by decide +kernel)
def pv640777 : PrimeValue := ⟨640777, pr640777⟩
private theorem pr640793 : Nat.Prime 640793 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv173,pv463]) (by decide +kernel)
def pv640793 : PrimeValue := ⟨640793, pr640793⟩
private theorem pr640873 : Nat.Prime 640873 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23,pv43]) (by decide +kernel)
def pv640873 : PrimeValue := ⟨640873, pr640873⟩
private theorem pr640901 : Nat.Prime 640901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv17,pv29]) (by decide +kernel)
def pv640901 : PrimeValue := ⟨640901, pr640901⟩
private theorem pr640933 : Nat.Prime 640933 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv53411]) (by decide +kernel)
def pv640933 : PrimeValue := ⟨640933, pr640933⟩
private theorem pr640949 : Nat.Prime 640949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv2081]) (by decide +kernel)
def pv640949 : PrimeValue := ⟨640949, pr640949⟩
private theorem pr641083 : Nat.Prime 641083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv8219]) (by decide +kernel)
def pv641083 : PrimeValue := ⟨641083, pr641083⟩
private theorem pr641093 : Nat.Prime 641093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv83,pv1931]) (by decide +kernel)
def pv641093 : PrimeValue := ⟨641093, pr641093⟩
private theorem pr641167 : Nat.Prime 641167 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv106861]) (by decide +kernel)
def pv641167 : PrimeValue := ⟨641167, pr641167⟩
private theorem pr641203 : Nat.Prime 641203 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv106867]) (by decide +kernel)
def pv641203 : PrimeValue := ⟨641203, pr641203⟩
private theorem pr641213 : Nat.Prime 641213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv13,pv19,pv59]) (by decide +kernel)
def pv641213 : PrimeValue := ⟨641213, pr641213⟩
private theorem pr641239 : Nat.Prime 641239 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv8221]) (by decide +kernel)
def pv641239 : PrimeValue := ⟨641239, pr641239⟩
private theorem pr641287 : Nat.Prime 641287 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv1549]) (by decide +kernel)
def pv641287 : PrimeValue := ⟨641287, pr641287⟩
private theorem pr641453 : Nat.Prime 641453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv31,pv739]) (by decide +kernel)
def pv641453 : PrimeValue := ⟨641453, pr641453⟩
private theorem pr641471 : Nat.Prime 641471 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv23,pv2789]) (by decide +kernel)
def pv641471 : PrimeValue := ⟨641471, pr641471⟩
private theorem pr641479 : Nat.Prime 641479 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv17,pv19,pv331]) (by decide +kernel)
def pv641479 : PrimeValue := ⟨641479, pr641479⟩
private theorem pr641513 : Nat.Prime 641513 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv53,pv89]) (by decide +kernel)
def pv641513 : PrimeValue := ⟨641513, pr641513⟩
private theorem pr641549 : Nat.Prime 641549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv160387]) (by decide +kernel)
def pv641549 : PrimeValue := ⟨641549, pr641549⟩
private theorem pr641579 : Nat.Prime 641579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv45827]) (by decide +kernel)
def pv641579 : PrimeValue := ⟨641579, pr641579⟩
private theorem pr641749 : Nat.Prime 641749 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv53479]) (by decide +kernel)
def pv641749 : PrimeValue := ⟨641749, pr641749⟩
private theorem pr641833 : Nat.Prime 641833 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv47,pv569]) (by decide +kernel)
def pv641833 : PrimeValue := ⟨641833, pr641833⟩
private theorem pr641923 : Nat.Prime 641923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv83,pv1289]) (by decide +kernel)
def pv641923 : PrimeValue := ⟨641923, pr641923⟩
private theorem pr641969 : Nat.Prime 641969 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv40123]) (by decide +kernel)
def pv641969 : PrimeValue := ⟨641969, pr641969⟩
private theorem pr642049 : Nat.Prime 642049 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv11,pv19]) (by decide +kernel)
def pv642049 : PrimeValue := ⟨642049, pr642049⟩
private theorem pr642163 : Nat.Prime 642163 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv43,pv131]) (by decide +kernel)
def pv642163 : PrimeValue := ⟨642163, pr642163⟩
private theorem pr642217 : Nat.Prime 642217 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv26759]) (by decide +kernel)
def pv642217 : PrimeValue := ⟨642217, pr642217⟩
private theorem pr642233 : Nat.Prime 642233 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv80279]) (by decide +kernel)
def pv642233 : PrimeValue := ⟨642233, pr642233⟩
private theorem pr642253 : Nat.Prime 642253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv23,pv179]) (by decide +kernel)
def pv642253 : PrimeValue := ⟨642253, pr642253⟩
private theorem pr642517 : Nat.Prime 642517 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv7649]) (by decide +kernel)
def pv642517 : PrimeValue := ⟨642517, pr642517⟩
private theorem pr642547 : Nat.Prime 642547 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv73,pv163]) (by decide +kernel)
def pv642547 : PrimeValue := ⟨642547, pr642547⟩
private theorem pr642623 : Nat.Prime 642623 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv321311]) (by decide +kernel)
def pv642623 : PrimeValue := ⟨642623, pr642623⟩
private theorem pr642673 : Nat.Prime 642673 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv4463]) (by decide +kernel)
def pv642673 : PrimeValue := ⟨642673, pr642673⟩
private theorem pr642739 : Nat.Prime 642739 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv107123]) (by decide +kernel)
def pv642739 : PrimeValue := ⟨642739, pr642739⟩
private theorem pr642799 : Nat.Prime 642799 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv41,pv67]) (by decide +kernel)
def pv642799 : PrimeValue := ⟨642799, pr642799⟩
private theorem pr642809 : Nat.Prime 642809 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv4229]) (by decide +kernel)
def pv642809 : PrimeValue := ⟨642809, pr642809⟩
private theorem pr642877 : Nat.Prime 642877 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv317]) (by decide +kernel)
def pv642877 : PrimeValue := ⟨642877, pr642877⟩
private theorem pr642881 : Nat.Prime 642881 :=
  checkPrime_prime (q := pv47) (ls := [pv2,pv5,pv7,pv41]) (by decide +kernel)
def pv642881 : PrimeValue := ⟨642881, pr642881⟩
private theorem pr642899 : Nat.Prime 642899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv321449]) (by decide +kernel)
def pv642899 : PrimeValue := ⟨642899, pr642899⟩
private theorem pr642973 : Nat.Prime 642973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv4871]) (by decide +kernel)
def pv642973 : PrimeValue := ⟨642973, pr642973⟩
private theorem pr643073 : Nat.Prime 643073 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv157]) (by decide +kernel)
def pv643073 : PrimeValue := ⟨643073, pr643073⟩
private theorem pr643099 : Nat.Prime 643099 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv107183]) (by decide +kernel)
def pv643099 : PrimeValue := ⟨643099, pr643099⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
