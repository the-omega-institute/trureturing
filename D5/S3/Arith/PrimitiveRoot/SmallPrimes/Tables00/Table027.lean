/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table027
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table027.pv67901
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table005
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table014
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table015

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr67901 : Nat.Prime 67901 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv97]) (by decide +kernel)
def pv67901 : PrimeValue := ⟨67901, pr67901⟩
private theorem pr67927 : Nat.Prime 67927 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11321]) (by decide +kernel)
def pv67927 : PrimeValue := ⟨67927, pr67927⟩
private theorem pr67931 : Nat.Prime 67931 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv6793]) (by decide +kernel)
def pv67931 : PrimeValue := ⟨67931, pr67931⟩
private theorem pr67933 : Nat.Prime 67933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv37]) (by decide +kernel)
def pv67933 : PrimeValue := ⟨67933, pr67933⟩
private theorem pr67939 : Nat.Prime 67939 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv67]) (by decide +kernel)
def pv67939 : PrimeValue := ⟨67939, pr67939⟩
private theorem pr67943 : Nat.Prime 67943 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv23,pv211]) (by decide +kernel)
def pv67943 : PrimeValue := ⟨67943, pr67943⟩
private theorem pr67957 : Nat.Prime 67957 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv809]) (by decide +kernel)
def pv67957 : PrimeValue := ⟨67957, pr67957⟩
private theorem pr67961 : Nat.Prime 67961 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv1699]) (by decide +kernel)
def pv67961 : PrimeValue := ⟨67961, pr67961⟩
private theorem pr67967 : Nat.Prime 67967 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv1999]) (by decide +kernel)
def pv67967 : PrimeValue := ⟨67967, pr67967⟩
private theorem pr67979 : Nat.Prime 67979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv829]) (by decide +kernel)
def pv67979 : PrimeValue := ⟨67979, pr67979⟩
private theorem pr67987 : Nat.Prime 67987 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1259]) (by decide +kernel)
def pv67987 : PrimeValue := ⟨67987, pr67987⟩
private theorem pr67993 : Nat.Prime 67993 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2833]) (by decide +kernel)
def pv67993 : PrimeValue := ⟨67993, pr67993⟩
private theorem pr68023 : Nat.Prime 68023 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv3779]) (by decide +kernel)
def pv68023 : PrimeValue := ⟨68023, pr68023⟩
private theorem pr68041 : Nat.Prime 68041 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv68041 : PrimeValue := ⟨68041, pr68041⟩
private theorem pr68053 : Nat.Prime 68053 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv53,pv107]) (by decide +kernel)
def pv68053 : PrimeValue := ⟨68053, pr68053⟩
private theorem pr68059 : Nat.Prime 68059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv199]) (by decide +kernel)
def pv68059 : PrimeValue := ⟨68059, pr68059⟩
private theorem pr68071 : Nat.Prime 68071 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv2269]) (by decide +kernel)
def pv68071 : PrimeValue := ⟨68071, pr68071⟩
private theorem pr68087 : Nat.Prime 68087 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv59,pv577]) (by decide +kernel)
def pv68087 : PrimeValue := ⟨68087, pr68087⟩
private theorem pr68099 : Nat.Prime 68099 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79,pv431]) (by decide +kernel)
def pv68099 : PrimeValue := ⟨68099, pr68099⟩
private theorem pr68111 : Nat.Prime 68111 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv139]) (by decide +kernel)
def pv68111 : PrimeValue := ⟨68111, pr68111⟩
private theorem pr68113 : Nat.Prime 68113 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv43]) (by decide +kernel)
def pv68113 : PrimeValue := ⟨68113, pr68113⟩
private theorem pr68141 : Nat.Prime 68141 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv3407]) (by decide +kernel)
def pv68141 : PrimeValue := ⟨68141, pr68141⟩
private theorem pr68147 : Nat.Prime 68147 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv2621]) (by decide +kernel)
def pv68147 : PrimeValue := ⟨68147, pr68147⟩
private theorem pr68161 : Nat.Prime 68161 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv71]) (by decide +kernel)
def pv68161 : PrimeValue := ⟨68161, pr68161⟩
private theorem pr68171 : Nat.Prime 68171 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv401]) (by decide +kernel)
def pv68171 : PrimeValue := ⟨68171, pr68171⟩
private theorem pr68207 : Nat.Prime 68207 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv67,pv509]) (by decide +kernel)
def pv68207 : PrimeValue := ⟨68207, pr68207⟩
private theorem pr68209 : Nat.Prime 68209 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv29]) (by decide +kernel)
def pv68209 : PrimeValue := ⟨68209, pr68209⟩
private theorem pr68213 : Nat.Prime 68213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17053]) (by decide +kernel)
def pv68213 : PrimeValue := ⟨68213, pr68213⟩
private theorem pr68219 : Nat.Prime 68219 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv1483]) (by decide +kernel)
def pv68219 : PrimeValue := ⟨68219, pr68219⟩
private theorem pr68227 : Nat.Prime 68227 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv83,pv137]) (by decide +kernel)
def pv68227 : PrimeValue := ⟨68227, pr68227⟩
private theorem pr68239 : Nat.Prime 68239 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv223]) (by decide +kernel)
def pv68239 : PrimeValue := ⟨68239, pr68239⟩
private theorem pr68261 : Nat.Prime 68261 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv3413]) (by decide +kernel)
def pv68261 : PrimeValue := ⟨68261, pr68261⟩
private theorem pr68279 : Nat.Prime 68279 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv4877]) (by decide +kernel)
def pv68279 : PrimeValue := ⟨68279, pr68279⟩
private theorem pr68281 : Nat.Prime 68281 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv569]) (by decide +kernel)
def pv68281 : PrimeValue := ⟨68281, pr68281⟩
private theorem pr68311 : Nat.Prime 68311 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv11,pv23]) (by decide +kernel)
def pv68311 : PrimeValue := ⟨68311, pr68311⟩
private theorem pr68329 : Nat.Prime 68329 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv13,pv73]) (by decide +kernel)
def pv68329 : PrimeValue := ⟨68329, pr68329⟩
private theorem pr68351 : Nat.Prime 68351 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv1367]) (by decide +kernel)
def pv68351 : PrimeValue := ⟨68351, pr68351⟩
private theorem pr68371 : Nat.Prime 68371 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv43,pv53]) (by decide +kernel)
def pv68371 : PrimeValue := ⟨68371, pr68371⟩
private theorem pr68389 : Nat.Prime 68389 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv41,pv139]) (by decide +kernel)
def pv68389 : PrimeValue := ⟨68389, pr68389⟩
private theorem pr68399 : Nat.Prime 68399 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv3109]) (by decide +kernel)
def pv68399 : PrimeValue := ⟨68399, pr68399⟩
private theorem pr68437 : Nat.Prime 68437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1901]) (by decide +kernel)
def pv68437 : PrimeValue := ⟨68437, pr68437⟩
private theorem pr68443 : Nat.Prime 68443 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv17,pv61]) (by decide +kernel)
def pv68443 : PrimeValue := ⟨68443, pr68443⟩
private theorem pr68447 : Nat.Prime 68447 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv4889]) (by decide +kernel)
def pv68447 : PrimeValue := ⟨68447, pr68447⟩
private theorem pr68449 : Nat.Prime 68449 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv23,pv31]) (by decide +kernel)
def pv68449 : PrimeValue := ⟨68449, pr68449⟩
private theorem pr68473 : Nat.Prime 68473 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv317]) (by decide +kernel)
def pv68473 : PrimeValue := ⟨68473, pr68473⟩
private theorem pr68477 : Nat.Prime 68477 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv19,pv53]) (by decide +kernel)
def pv68477 : PrimeValue := ⟨68477, pr68477⟩
private theorem pr68483 : Nat.Prime 68483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv97,pv353]) (by decide +kernel)
def pv68483 : PrimeValue := ⟨68483, pr68483⟩
private theorem pr68489 : Nat.Prime 68489 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv1223]) (by decide +kernel)
def pv68489 : PrimeValue := ⟨68489, pr68489⟩
private theorem pr68491 : Nat.Prime 68491 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv761]) (by decide +kernel)
def pv68491 : PrimeValue := ⟨68491, pr68491⟩
private theorem pr68501 : Nat.Prime 68501 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv137]) (by decide +kernel)
def pv68501 : PrimeValue := ⟨68501, pr68501⟩
private theorem pr68507 : Nat.Prime 68507 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv34253]) (by decide +kernel)
def pv68507 : PrimeValue := ⟨68507, pr68507⟩
private theorem pr68521 : Nat.Prime 68521 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv571]) (by decide +kernel)
def pv68521 : PrimeValue := ⟨68521, pr68521⟩
private theorem pr68531 : Nat.Prime 68531 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv11,pv89]) (by decide +kernel)
def pv68531 : PrimeValue := ⟨68531, pr68531⟩
private theorem pr68539 : Nat.Prime 68539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11423]) (by decide +kernel)
def pv68539 : PrimeValue := ⟨68539, pr68539⟩
private theorem pr68543 : Nat.Prime 68543 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv43,pv797]) (by decide +kernel)
def pv68543 : PrimeValue := ⟨68543, pr68543⟩
private theorem pr68567 : Nat.Prime 68567 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv34283]) (by decide +kernel)
def pv68567 : PrimeValue := ⟨68567, pr68567⟩
private theorem pr68581 : Nat.Prime 68581 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv127]) (by decide +kernel)
def pv68581 : PrimeValue := ⟨68581, pr68581⟩
private theorem pr68597 : Nat.Prime 68597 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv1559]) (by decide +kernel)
def pv68597 : PrimeValue := ⟨68597, pr68597⟩
private theorem pr68611 : Nat.Prime 68611 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv2287]) (by decide +kernel)
def pv68611 : PrimeValue := ⟨68611, pr68611⟩
private theorem pr68633 : Nat.Prime 68633 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv373]) (by decide +kernel)
def pv68633 : PrimeValue := ⟨68633, pr68633⟩
private theorem pr68639 : Nat.Prime 68639 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv34319]) (by decide +kernel)
def pv68639 : PrimeValue := ⟨68639, pr68639⟩
private theorem pr68659 : Nat.Prime 68659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11443]) (by decide +kernel)
def pv68659 : PrimeValue := ⟨68659, pr68659⟩
private theorem pr68669 : Nat.Prime 68669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17167]) (by decide +kernel)
def pv68669 : PrimeValue := ⟨68669, pr68669⟩
private theorem pr68683 : Nat.Prime 68683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11447]) (by decide +kernel)
def pv68683 : PrimeValue := ⟨68683, pr68683⟩
private theorem pr68687 : Nat.Prime 68687 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv61,pv563]) (by decide +kernel)
def pv68687 : PrimeValue := ⟨68687, pr68687⟩
private theorem pr68699 : Nat.Prime 68699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv701]) (by decide +kernel)
def pv68699 : PrimeValue := ⟨68699, pr68699⟩
private theorem pr68711 : Nat.Prime 68711 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv6871]) (by decide +kernel)
def pv68711 : PrimeValue := ⟨68711, pr68711⟩
private theorem pr68713 : Nat.Prime 68713 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv409]) (by decide +kernel)
def pv68713 : PrimeValue := ⟨68713, pr68713⟩
private theorem pr68729 : Nat.Prime 68729 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv71]) (by decide +kernel)
def pv68729 : PrimeValue := ⟨68729, pr68729⟩
private theorem pr68737 : Nat.Prime 68737 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv179]) (by decide +kernel)
def pv68737 : PrimeValue := ⟨68737, pr68737⟩
private theorem pr68743 : Nat.Prime 68743 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv67]) (by decide +kernel)
def pv68743 : PrimeValue := ⟨68743, pr68743⟩
private theorem pr68749 : Nat.Prime 68749 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv17,pv337]) (by decide +kernel)
def pv68749 : PrimeValue := ⟨68749, pr68749⟩
private theorem pr68767 : Nat.Prime 68767 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv73,pv157]) (by decide +kernel)
def pv68767 : PrimeValue := ⟨68767, pr68767⟩
private theorem pr68771 : Nat.Prime 68771 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv13,pv23]) (by decide +kernel)
def pv68771 : PrimeValue := ⟨68771, pr68771⟩
private theorem pr68777 : Nat.Prime 68777 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv8597]) (by decide +kernel)
def pv68777 : PrimeValue := ⟨68777, pr68777⟩
private theorem pr68791 : Nat.Prime 68791 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv2293]) (by decide +kernel)
def pv68791 : PrimeValue := ⟨68791, pr68791⟩
private theorem pr68813 : Nat.Prime 68813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17203]) (by decide +kernel)
def pv68813 : PrimeValue := ⟨68813, pr68813⟩
private theorem pr68819 : Nat.Prime 68819 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv1811]) (by decide +kernel)
def pv68819 : PrimeValue := ⟨68819, pr68819⟩
private theorem pr68821 : Nat.Prime 68821 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv31,pv37]) (by decide +kernel)
def pv68821 : PrimeValue := ⟨68821, pr68821⟩
private theorem pr68863 : Nat.Prime 68863 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv499]) (by decide +kernel)
def pv68863 : PrimeValue := ⟨68863, pr68863⟩
private theorem pr68879 : Nat.Prime 68879 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv34439]) (by decide +kernel)
def pv68879 : PrimeValue := ⟨68879, pr68879⟩
private theorem pr68881 : Nat.Prime 68881 :=
  checkPrime_prime (q := pv53) (ls := [pv2,pv3,pv5,pv7,pv41]) (by decide +kernel)
def pv68881 : PrimeValue := ⟨68881, pr68881⟩
private theorem pr68891 : Nat.Prime 68891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv83]) (by decide +kernel)
def pv68891 : PrimeValue := ⟨68891, pr68891⟩
private theorem pr68897 : Nat.Prime 68897 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2153]) (by decide +kernel)
def pv68897 : PrimeValue := ⟨68897, pr68897⟩
private theorem pr68899 : Nat.Prime 68899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11483]) (by decide +kernel)
def pv68899 : PrimeValue := ⟨68899, pr68899⟩
private theorem pr68903 : Nat.Prime 68903 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv47,pv733]) (by decide +kernel)
def pv68903 : PrimeValue := ⟨68903, pr68903⟩
private theorem pr68909 : Nat.Prime 68909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv23,pv107]) (by decide +kernel)
def pv68909 : PrimeValue := ⟨68909, pr68909⟩
private theorem pr68917 : Nat.Prime 68917 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv5743]) (by decide +kernel)
def pv68917 : PrimeValue := ⟨68917, pr68917⟩
private theorem pr68927 : Nat.Prime 68927 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv13,pv241]) (by decide +kernel)
def pv68927 : PrimeValue := ⟨68927, pr68927⟩
private theorem pr68947 : Nat.Prime 68947 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11491]) (by decide +kernel)
def pv68947 : PrimeValue := ⟨68947, pr68947⟩
private theorem pr68963 : Nat.Prime 68963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv41]) (by decide +kernel)
def pv68963 : PrimeValue := ⟨68963, pr68963⟩
private theorem pr68993 : Nat.Prime 68993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv11]) (by decide +kernel)
def pv68993 : PrimeValue := ⟨68993, pr68993⟩
private theorem pr69001 : Nat.Prime 69001 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv23]) (by decide +kernel)
def pv69001 : PrimeValue := ⟨69001, pr69001⟩
private theorem pr69011 : Nat.Prime 69011 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv67,pv103]) (by decide +kernel)
def pv69011 : PrimeValue := ⟨69011, pr69011⟩
private theorem pr69019 : Nat.Prime 69019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11503]) (by decide +kernel)
def pv69019 : PrimeValue := ⟨69019, pr69019⟩
private theorem pr69029 : Nat.Prime 69029 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17257]) (by decide +kernel)
def pv69029 : PrimeValue := ⟨69029, pr69029⟩
private theorem pr69031 : Nat.Prime 69031 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv59]) (by decide +kernel)
def pv69031 : PrimeValue := ⟨69031, pr69031⟩
private theorem pr69061 : Nat.Prime 69061 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1151]) (by decide +kernel)
def pv69061 : PrimeValue := ⟨69061, pr69061⟩
private theorem pr69067 : Nat.Prime 69067 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1279]) (by decide +kernel)
def pv69067 : PrimeValue := ⟨69067, pr69067⟩
private theorem pr69073 : Nat.Prime 69073 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv1439]) (by decide +kernel)
def pv69073 : PrimeValue := ⟨69073, pr69073⟩
private theorem pr69109 : Nat.Prime 69109 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv443]) (by decide +kernel)
def pv69109 : PrimeValue := ⟨69109, pr69109⟩
private theorem pr69119 : Nat.Prime 69119 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv7,pv4937]) (by decide +kernel)
def pv69119 : PrimeValue := ⟨69119, pr69119⟩
private theorem pr69127 : Nat.Prime 69127 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv41,pv281]) (by decide +kernel)
def pv69127 : PrimeValue := ⟨69127, pr69127⟩
private theorem pr69143 : Nat.Prime 69143 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv181,pv191]) (by decide +kernel)
def pv69143 : PrimeValue := ⟨69143, pr69143⟩
private theorem pr69149 : Nat.Prime 69149 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv59,pv293]) (by decide +kernel)
def pv69149 : PrimeValue := ⟨69149, pr69149⟩
private theorem pr69151 : Nat.Prime 69151 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv461]) (by decide +kernel)
def pv69151 : PrimeValue := ⟨69151, pr69151⟩
private theorem pr69163 : Nat.Prime 69163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11527]) (by decide +kernel)
def pv69163 : PrimeValue := ⟨69163, pr69163⟩
private theorem pr69191 : Nat.Prime 69191 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv11,pv17,pv37]) (by decide +kernel)
def pv69191 : PrimeValue := ⟨69191, pr69191⟩
private theorem pr69193 : Nat.Prime 69193 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv31]) (by decide +kernel)
def pv69193 : PrimeValue := ⟨69193, pr69193⟩
private theorem pr69197 : Nat.Prime 69197 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17299]) (by decide +kernel)
def pv69197 : PrimeValue := ⟨69197, pr69197⟩
private theorem pr69203 : Nat.Prime 69203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv4943]) (by decide +kernel)
def pv69203 : PrimeValue := ⟨69203, pr69203⟩
private theorem pr69221 : Nat.Prime 69221 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv3461]) (by decide +kernel)
def pv69221 : PrimeValue := ⟨69221, pr69221⟩
private theorem pr69233 : Nat.Prime 69233 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv4327]) (by decide +kernel)
def pv69233 : PrimeValue := ⟨69233, pr69233⟩
private theorem pr69239 : Nat.Prime 69239 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv13,pv2663]) (by decide +kernel)
def pv69239 : PrimeValue := ⟨69239, pr69239⟩
private theorem pr69247 : Nat.Prime 69247 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv3847]) (by decide +kernel)
def pv69247 : PrimeValue := ⟨69247, pr69247⟩
private theorem pr69257 : Nat.Prime 69257 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv787]) (by decide +kernel)
def pv69257 : PrimeValue := ⟨69257, pr69257⟩
private theorem pr69259 : Nat.Prime 69259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv97]) (by decide +kernel)
def pv69259 : PrimeValue := ⟨69259, pr69259⟩
private theorem pr69263 : Nat.Prime 69263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv34631]) (by decide +kernel)
def pv69263 : PrimeValue := ⟨69263, pr69263⟩
private theorem pr69313 : Nat.Prime 69313 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv19]) (by decide +kernel)
def pv69313 : PrimeValue := ⟨69313, pr69313⟩
private theorem pr69317 : Nat.Prime 69317 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv31,pv43]) (by decide +kernel)
def pv69317 : PrimeValue := ⟨69317, pr69317⟩
private theorem pr69337 : Nat.Prime 69337 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv107]) (by decide +kernel)
def pv69337 : PrimeValue := ⟨69337, pr69337⟩
private theorem pr69341 : Nat.Prime 69341 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv3467]) (by decide +kernel)
def pv69341 : PrimeValue := ⟨69341, pr69341⟩
private theorem pr69371 : Nat.Prime 69371 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv991]) (by decide +kernel)
def pv69371 : PrimeValue := ⟨69371, pr69371⟩
private theorem pr69379 : Nat.Prime 69379 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv373]) (by decide +kernel)
def pv69379 : PrimeValue := ⟨69379, pr69379⟩
private theorem pr69383 : Nat.Prime 69383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv113,pv307]) (by decide +kernel)
def pv69383 : PrimeValue := ⟨69383, pr69383⟩
private theorem pr69389 : Nat.Prime 69389 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv19,pv83]) (by decide +kernel)
def pv69389 : PrimeValue := ⟨69389, pr69389⟩
private theorem pr69401 : Nat.Prime 69401 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv347]) (by decide +kernel)
def pv69401 : PrimeValue := ⟨69401, pr69401⟩
private theorem pr69403 : Nat.Prime 69403 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv43,pv269]) (by decide +kernel)
def pv69403 : PrimeValue := ⟨69403, pr69403⟩
private theorem pr69427 : Nat.Prime 69427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv19,pv29]) (by decide +kernel)
def pv69427 : PrimeValue := ⟨69427, pr69427⟩
private theorem pr69431 : Nat.Prime 69431 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv53,pv131]) (by decide +kernel)
def pv69431 : PrimeValue := ⟨69431, pr69431⟩
private theorem pr69439 : Nat.Prime 69439 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv71,pv163]) (by decide +kernel)
def pv69439 : PrimeValue := ⟨69439, pr69439⟩
private theorem pr69457 : Nat.Prime 69457 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1447]) (by decide +kernel)
def pv69457 : PrimeValue := ⟨69457, pr69457⟩
private theorem pr69463 : Nat.Prime 69463 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv17,pv227]) (by decide +kernel)
def pv69463 : PrimeValue := ⟨69463, pr69463⟩
private theorem pr69467 : Nat.Prime 69467 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv739]) (by decide +kernel)
def pv69467 : PrimeValue := ⟨69467, pr69467⟩
private theorem pr69473 : Nat.Prime 69473 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv167]) (by decide +kernel)
def pv69473 : PrimeValue := ⟨69473, pr69473⟩
private theorem pr69481 : Nat.Prime 69481 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv193]) (by decide +kernel)
def pv69481 : PrimeValue := ⟨69481, pr69481⟩
private theorem pr69491 : Nat.Prime 69491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv6949]) (by decide +kernel)
def pv69491 : PrimeValue := ⟨69491, pr69491⟩
private theorem pr69493 : Nat.Prime 69493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5791]) (by decide +kernel)
def pv69493 : PrimeValue := ⟨69493, pr69493⟩
private theorem pr69499 : Nat.Prime 69499 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv13]) (by decide +kernel)
def pv69499 : PrimeValue := ⟨69499, pr69499⟩
private theorem pr69539 : Nat.Prime 69539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv4967]) (by decide +kernel)
def pv69539 : PrimeValue := ⟨69539, pr69539⟩
private theorem pr69593 : Nat.Prime 69593 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv8699]) (by decide +kernel)
def pv69593 : PrimeValue := ⟨69593, pr69593⟩
private theorem pr69623 : Nat.Prime 69623 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv4973]) (by decide +kernel)
def pv69623 : PrimeValue := ⟨69623, pr69623⟩
private theorem pr69653 : Nat.Prime 69653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv1583]) (by decide +kernel)
def pv69653 : PrimeValue := ⟨69653, pr69653⟩
private theorem pr69661 : Nat.Prime 69661 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv43]) (by decide +kernel)
def pv69661 : PrimeValue := ⟨69661, pr69661⟩
private theorem pr69677 : Nat.Prime 69677 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17419]) (by decide +kernel)
def pv69677 : PrimeValue := ⟨69677, pr69677⟩
private theorem pr69691 : Nat.Prime 69691 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv23,pv101]) (by decide +kernel)
def pv69691 : PrimeValue := ⟨69691, pr69691⟩
private theorem pr69697 : Nat.Prime 69697 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv69697 : PrimeValue := ⟨69697, pr69697⟩
private theorem pr69709 : Nat.Prime 69709 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv37,pv157]) (by decide +kernel)
def pv69709 : PrimeValue := ⟨69709, pr69709⟩
private theorem pr69737 : Nat.Prime 69737 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv379]) (by decide +kernel)
def pv69737 : PrimeValue := ⟨69737, pr69737⟩
private theorem pr69739 : Nat.Prime 69739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv59,pv197]) (by decide +kernel)
def pv69739 : PrimeValue := ⟨69739, pr69739⟩
private theorem pr69761 : Nat.Prime 69761 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv109]) (by decide +kernel)
def pv69761 : PrimeValue := ⟨69761, pr69761⟩
private theorem pr69763 : Nat.Prime 69763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv151]) (by decide +kernel)
def pv69763 : PrimeValue := ⟨69763, pr69763⟩
private theorem pr69767 : Nat.Prime 69767 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv34883]) (by decide +kernel)
def pv69767 : PrimeValue := ⟨69767, pr69767⟩
private theorem pr69779 : Nat.Prime 69779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv139,pv251]) (by decide +kernel)
def pv69779 : PrimeValue := ⟨69779, pr69779⟩
private theorem pr69809 : Nat.Prime 69809 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv4363]) (by decide +kernel)
def pv69809 : PrimeValue := ⟨69809, pr69809⟩
private theorem pr69821 : Nat.Prime 69821 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv3491]) (by decide +kernel)
def pv69821 : PrimeValue := ⟨69821, pr69821⟩
private theorem pr69827 : Nat.Prime 69827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv34913]) (by decide +kernel)
def pv69827 : PrimeValue := ⟨69827, pr69827⟩
private theorem pr69829 : Nat.Prime 69829 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv11,pv23]) (by decide +kernel)
def pv69829 : PrimeValue := ⟨69829, pr69829⟩
private theorem pr69833 : Nat.Prime 69833 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv29,pv43]) (by decide +kernel)
def pv69833 : PrimeValue := ⟨69833, pr69833⟩
private theorem pr69847 : Nat.Prime 69847 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv1663]) (by decide +kernel)
def pv69847 : PrimeValue := ⟨69847, pr69847⟩
private theorem pr69857 : Nat.Prime 69857 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv37,pv59]) (by decide +kernel)
def pv69857 : PrimeValue := ⟨69857, pr69857⟩
private theorem pr69859 : Nat.Prime 69859 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv3881]) (by decide +kernel)
def pv69859 : PrimeValue := ⟨69859, pr69859⟩
private theorem pr69877 : Nat.Prime 69877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv647]) (by decide +kernel)
def pv69877 : PrimeValue := ⟨69877, pr69877⟩
private theorem pr69899 : Nat.Prime 69899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv34949]) (by decide +kernel)
def pv69899 : PrimeValue := ⟨69899, pr69899⟩
private theorem pr69911 : Nat.Prime 69911 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv6991]) (by decide +kernel)
def pv69911 : PrimeValue := ⟨69911, pr69911⟩
private theorem pr69929 : Nat.Prime 69929 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv8741]) (by decide +kernel)
def pv69929 : PrimeValue := ⟨69929, pr69929⟩
private theorem pr69931 : Nat.Prime 69931 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv37]) (by decide +kernel)
def pv69931 : PrimeValue := ⟨69931, pr69931⟩
private theorem pr69941 : Nat.Prime 69941 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv269]) (by decide +kernel)
def pv69941 : PrimeValue := ⟨69941, pr69941⟩
private theorem pr69959 : Nat.Prime 69959 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv19,pv263]) (by decide +kernel)
def pv69959 : PrimeValue := ⟨69959, pr69959⟩
private theorem pr69991 : Nat.Prime 69991 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv2333]) (by decide +kernel)
def pv69991 : PrimeValue := ⟨69991, pr69991⟩
private theorem pr69997 : Nat.Prime 69997 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv307]) (by decide +kernel)
def pv69997 : PrimeValue := ⟨69997, pr69997⟩
private theorem pr70001 : Nat.Prime 70001 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7]) (by decide +kernel)
def pv70001 : PrimeValue := ⟨70001, pr70001⟩
private theorem pr70003 : Nat.Prime 70003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv3889]) (by decide +kernel)
def pv70003 : PrimeValue := ⟨70003, pr70003⟩
private theorem pr70009 : Nat.Prime 70009 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv2917]) (by decide +kernel)
def pv70009 : PrimeValue := ⟨70009, pr70009⟩
private theorem pr70019 : Nat.Prime 70019 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv13,pv2693]) (by decide +kernel)
def pv70019 : PrimeValue := ⟨70019, pr70019⟩
private theorem pr70039 : Nat.Prime 70039 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv1297]) (by decide +kernel)
def pv70039 : PrimeValue := ⟨70039, pr70039⟩
private theorem pr70051 : Nat.Prime 70051 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv467]) (by decide +kernel)
def pv70051 : PrimeValue := ⟨70051, pr70051⟩
private theorem pr70061 : Nat.Prime 70061 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv31,pv113]) (by decide +kernel)
def pv70061 : PrimeValue := ⟨70061, pr70061⟩
private theorem pr70067 : Nat.Prime 70067 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53,pv661]) (by decide +kernel)
def pv70067 : PrimeValue := ⟨70067, pr70067⟩
private theorem pr70079 : Nat.Prime 70079 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv37,pv947]) (by decide +kernel)
def pv70079 : PrimeValue := ⟨70079, pr70079⟩
private theorem pr70099 : Nat.Prime 70099 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv1669]) (by decide +kernel)
def pv70099 : PrimeValue := ⟨70099, pr70099⟩
private theorem pr70111 : Nat.Prime 70111 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv19,pv41]) (by decide +kernel)
def pv70111 : PrimeValue := ⟨70111, pr70111⟩
private theorem pr70117 : Nat.Prime 70117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5843]) (by decide +kernel)
def pv70117 : PrimeValue := ⟨70117, pr70117⟩
private theorem pr70121 : Nat.Prime 70121 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv1753]) (by decide +kernel)
def pv70121 : PrimeValue := ⟨70121, pr70121⟩
private theorem pr70123 : Nat.Prime 70123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv29,pv31]) (by decide +kernel)
def pv70123 : PrimeValue := ⟨70123, pr70123⟩
private theorem pr70139 : Nat.Prime 70139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv35069]) (by decide +kernel)
def pv70139 : PrimeValue := ⟨70139, pr70139⟩
private theorem pr70141 : Nat.Prime 70141 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv167]) (by decide +kernel)
def pv70141 : PrimeValue := ⟨70141, pr70141⟩
private theorem pr70157 : Nat.Prime 70157 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17539]) (by decide +kernel)
def pv70157 : PrimeValue := ⟨70157, pr70157⟩
private theorem pr70163 : Nat.Prime 70163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv35081]) (by decide +kernel)
def pv70163 : PrimeValue := ⟨70163, pr70163⟩
private theorem pr70177 : Nat.Prime 70177 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv43]) (by decide +kernel)
def pv70177 : PrimeValue := ⟨70177, pr70177⟩
private theorem pr70181 : Nat.Prime 70181 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv29]) (by decide +kernel)
def pv70181 : PrimeValue := ⟨70181, pr70181⟩
private theorem pr70183 : Nat.Prime 70183 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv557]) (by decide +kernel)
def pv70183 : PrimeValue := ⟨70183, pr70183⟩
private theorem pr70199 : Nat.Prime 70199 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv35099]) (by decide +kernel)
def pv70199 : PrimeValue := ⟨70199, pr70199⟩
private theorem pr70201 : Nat.Prime 70201 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv70201 : PrimeValue := ⟨70201, pr70201⟩
private theorem pr70207 : Nat.Prime 70207 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11701]) (by decide +kernel)
def pv70207 : PrimeValue := ⟨70207, pr70207⟩
private theorem pr70223 : Nat.Prime 70223 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv35111]) (by decide +kernel)
def pv70223 : PrimeValue := ⟨70223, pr70223⟩
private theorem pr70229 : Nat.Prime 70229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv97,pv181]) (by decide +kernel)
def pv70229 : PrimeValue := ⟨70229, pr70229⟩
private theorem pr70237 : Nat.Prime 70237 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1951]) (by decide +kernel)
def pv70237 : PrimeValue := ⟨70237, pr70237⟩
private theorem pr70249 : Nat.Prime 70249 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv2927]) (by decide +kernel)
def pv70249 : PrimeValue := ⟨70249, pr70249⟩
private theorem pr70271 : Nat.Prime 70271 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7027]) (by decide +kernel)
def pv70271 : PrimeValue := ⟨70271, pr70271⟩
private theorem pr70289 : Nat.Prime 70289 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv191]) (by decide +kernel)
def pv70289 : PrimeValue := ⟨70289, pr70289⟩
private theorem pr70297 : Nat.Prime 70297 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29,pv101]) (by decide +kernel)
def pv70297 : PrimeValue := ⟨70297, pr70297⟩
private theorem pr70309 : Nat.Prime 70309 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv31]) (by decide +kernel)
def pv70309 : PrimeValue := ⟨70309, pr70309⟩
private theorem pr70313 : Nat.Prime 70313 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv17,pv47]) (by decide +kernel)
def pv70313 : PrimeValue := ⟨70313, pr70313⟩
private theorem pr70321 : Nat.Prime 70321 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv293]) (by decide +kernel)
def pv70321 : PrimeValue := ⟨70321, pr70321⟩
private theorem pr70327 : Nat.Prime 70327 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv3907]) (by decide +kernel)
def pv70327 : PrimeValue := ⟨70327, pr70327⟩
private theorem pr70351 : Nat.Prime 70351 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv67]) (by decide +kernel)
def pv70351 : PrimeValue := ⟨70351, pr70351⟩
private theorem pr70373 : Nat.Prime 70373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv73,pv241]) (by decide +kernel)
def pv70373 : PrimeValue := ⟨70373, pr70373⟩
private theorem pr70379 : Nat.Prime 70379 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv11,pv457]) (by decide +kernel)
def pv70379 : PrimeValue := ⟨70379, pr70379⟩
private theorem pr70381 : Nat.Prime 70381 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv17,pv23]) (by decide +kernel)
def pv70381 : PrimeValue := ⟨70381, pr70381⟩
private theorem pr70393 : Nat.Prime 70393 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv419]) (by decide +kernel)
def pv70393 : PrimeValue := ⟨70393, pr70393⟩
private theorem pr70423 : Nat.Prime 70423 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv97]) (by decide +kernel)
def pv70423 : PrimeValue := ⟨70423, pr70423⟩
private theorem pr70429 : Nat.Prime 70429 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5869]) (by decide +kernel)
def pv70429 : PrimeValue := ⟨70429, pr70429⟩
private theorem pr70439 : Nat.Prime 70439 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv41,pv859]) (by decide +kernel)
def pv70439 : PrimeValue := ⟨70439, pr70439⟩
private theorem pr70451 : Nat.Prime 70451 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv1409]) (by decide +kernel)
def pv70451 : PrimeValue := ⟨70451, pr70451⟩
private theorem pr70457 : Nat.Prime 70457 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv8807]) (by decide +kernel)
def pv70457 : PrimeValue := ⟨70457, pr70457⟩
private theorem pr70459 : Nat.Prime 70459 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11743]) (by decide +kernel)
def pv70459 : PrimeValue := ⟨70459, pr70459⟩
private theorem pr70487 : Nat.Prime 70487 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv2711]) (by decide +kernel)
def pv70487 : PrimeValue := ⟨70487, pr70487⟩
private theorem pr70489 : Nat.Prime 70489 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv11,pv89]) (by decide +kernel)
def pv70489 : PrimeValue := ⟨70489, pr70489⟩
private theorem pr70501 : Nat.Prime 70501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv47]) (by decide +kernel)
def pv70501 : PrimeValue := ⟨70501, pr70501⟩
private theorem pr70507 : Nat.Prime 70507 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv3917]) (by decide +kernel)
def pv70507 : PrimeValue := ⟨70507, pr70507⟩
private theorem pr70529 : Nat.Prime 70529 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv29]) (by decide +kernel)
def pv70529 : PrimeValue := ⟨70529, pr70529⟩
private theorem pr70537 : Nat.Prime 70537 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2939]) (by decide +kernel)
def pv70537 : PrimeValue := ⟨70537, pr70537⟩
private theorem pr70549 : Nat.Prime 70549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5879]) (by decide +kernel)
def pv70549 : PrimeValue := ⟨70549, pr70549⟩
private theorem pr70571 : Nat.Prime 70571 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7057]) (by decide +kernel)
def pv70571 : PrimeValue := ⟨70571, pr70571⟩
private theorem pr70573 : Nat.Prime 70573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5881]) (by decide +kernel)
def pv70573 : PrimeValue := ⟨70573, pr70573⟩
private theorem pr70583 : Nat.Prime 70583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv35291]) (by decide +kernel)
def pv70583 : PrimeValue := ⟨70583, pr70583⟩
private theorem pr70589 : Nat.Prime 70589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv2521]) (by decide +kernel)
def pv70589 : PrimeValue := ⟨70589, pr70589⟩
private theorem pr70607 : Nat.Prime 70607 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv43,pv821]) (by decide +kernel)
def pv70607 : PrimeValue := ⟨70607, pr70607⟩
private theorem pr70619 : Nat.Prime 70619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv31,pv67]) (by decide +kernel)
def pv70619 : PrimeValue := ⟨70619, pr70619⟩
private theorem pr70621 : Nat.Prime 70621 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv11,pv107]) (by decide +kernel)
def pv70621 : PrimeValue := ⟨70621, pr70621⟩
private theorem pr70627 : Nat.Prime 70627 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv79,pv149]) (by decide +kernel)
def pv70627 : PrimeValue := ⟨70627, pr70627⟩
private theorem pr70639 : Nat.Prime 70639 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv61,pv193]) (by decide +kernel)
def pv70639 : PrimeValue := ⟨70639, pr70639⟩
private theorem pr70657 : Nat.Prime 70657 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv23]) (by decide +kernel)
def pv70657 : PrimeValue := ⟨70657, pr70657⟩
private theorem pr70663 : Nat.Prime 70663 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11777]) (by decide +kernel)
def pv70663 : PrimeValue := ⟨70663, pr70663⟩
private theorem pr70667 : Nat.Prime 70667 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv89,pv397]) (by decide +kernel)
def pv70667 : PrimeValue := ⟨70667, pr70667⟩
private theorem pr70687 : Nat.Prime 70687 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv17]) (by decide +kernel)
def pv70687 : PrimeValue := ⟨70687, pr70687⟩
private theorem pr70709 : Nat.Prime 70709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv1607]) (by decide +kernel)
def pv70709 : PrimeValue := ⟨70709, pr70709⟩
private theorem pr70717 : Nat.Prime 70717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv71,pv83]) (by decide +kernel)
def pv70717 : PrimeValue := ⟨70717, pr70717⟩
private theorem pr70729 : Nat.Prime 70729 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv7,pv421]) (by decide +kernel)
def pv70729 : PrimeValue := ⟨70729, pr70729⟩
private theorem pr70753 : Nat.Prime 70753 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv67]) (by decide +kernel)
def pv70753 : PrimeValue := ⟨70753, pr70753⟩
private theorem pr70769 : Nat.Prime 70769 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv4423]) (by decide +kernel)
def pv70769 : PrimeValue := ⟨70769, pr70769⟩
private theorem pr70783 : Nat.Prime 70783 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv47,pv251]) (by decide +kernel)
def pv70783 : PrimeValue := ⟨70783, pr70783⟩
private theorem pr70793 : Nat.Prime 70793 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv8849]) (by decide +kernel)
def pv70793 : PrimeValue := ⟨70793, pr70793⟩
private theorem pr70823 : Nat.Prime 70823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv2083]) (by decide +kernel)
def pv70823 : PrimeValue := ⟨70823, pr70823⟩
private theorem pr70841 : Nat.Prime 70841 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv11,pv23]) (by decide +kernel)
def pv70841 : PrimeValue := ⟨70841, pr70841⟩
private theorem pr70843 : Nat.Prime 70843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11807]) (by decide +kernel)
def pv70843 : PrimeValue := ⟨70843, pr70843⟩
private theorem pr70849 : Nat.Prime 70849 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv41]) (by decide +kernel)
def pv70849 : PrimeValue := ⟨70849, pr70849⟩
private theorem pr70853 : Nat.Prime 70853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17713]) (by decide +kernel)
def pv70853 : PrimeValue := ⟨70853, pr70853⟩
private theorem pr70877 : Nat.Prime 70877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv29,pv47]) (by decide +kernel)
def pv70877 : PrimeValue := ⟨70877, pr70877⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
