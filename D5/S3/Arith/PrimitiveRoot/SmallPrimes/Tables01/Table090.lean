/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table090
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table090.pv328931
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table010
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table014
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table022
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table056
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table057

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr328931 : Nat.Prime 328931 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv37,pv127]) (by decide +kernel)
def pv328931 : PrimeValue := ⟨328931, pr328931⟩
private theorem pr328961 : Nat.Prime 328961 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv257]) (by decide +kernel)
def pv328961 : PrimeValue := ⟨328961, pr328961⟩
private theorem pr329027 : Nat.Prime 329027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv164513]) (by decide +kernel)
def pv329027 : PrimeValue := ⟨329027, pr329027⟩
private theorem pr329053 : Nat.Prime 329053 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv1613]) (by decide +kernel)
def pv329053 : PrimeValue := ⟨329053, pr329053⟩
private theorem pr329083 : Nat.Prime 329083 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv4219]) (by decide +kernel)
def pv329083 : PrimeValue := ⟨329083, pr329083⟩
private theorem pr329123 : Nat.Prime 329123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv89]) (by decide +kernel)
def pv329123 : PrimeValue := ⟨329123, pr329123⟩
private theorem pr329167 : Nat.Prime 329167 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv18287]) (by decide +kernel)
def pv329167 : PrimeValue := ⟨329167, pr329167⟩
private theorem pr329177 : Nat.Prime 329177 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv1789]) (by decide +kernel)
def pv329177 : PrimeValue := ⟨329177, pr329177⟩
private theorem pr329191 : Nat.Prime 329191 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv10973]) (by decide +kernel)
def pv329191 : PrimeValue := ⟨329191, pr329191⟩
private theorem pr329201 : Nat.Prime 329201 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv823]) (by decide +kernel)
def pv329201 : PrimeValue := ⟨329201, pr329201⟩
private theorem pr329207 : Nat.Prime 329207 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv241,pv683]) (by decide +kernel)
def pv329207 : PrimeValue := ⟨329207, pr329207⟩
private theorem pr329233 : Nat.Prime 329233 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19]) (by decide +kernel)
def pv329233 : PrimeValue := ⟨329233, pr329233⟩
private theorem pr329243 : Nat.Prime 329243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv164621]) (by decide +kernel)
def pv329243 : PrimeValue := ⟨329243, pr329243⟩
private theorem pr329257 : Nat.Prime 329257 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv269]) (by decide +kernel)
def pv329257 : PrimeValue := ⟨329257, pr329257⟩
private theorem pr329269 : Nat.Prime 329269 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv1193]) (by decide +kernel)
def pv329269 : PrimeValue := ⟨329269, pr329269⟩
private theorem pr329293 : Nat.Prime 329293 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv3049]) (by decide +kernel)
def pv329293 : PrimeValue := ⟨329293, pr329293⟩
private theorem pr329297 : Nat.Prime 329297 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv1871]) (by decide +kernel)
def pv329297 : PrimeValue := ⟨329297, pr329297⟩
private theorem pr329321 : Nat.Prime 329321 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv8233]) (by decide +kernel)
def pv329321 : PrimeValue := ⟨329321, pr329321⟩
private theorem pr329387 : Nat.Prime 329387 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv157,pv1049]) (by decide +kernel)
def pv329387 : PrimeValue := ⟨329387, pr329387⟩
private theorem pr329419 : Nat.Prime 329419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv18301]) (by decide +kernel)
def pv329419 : PrimeValue := ⟨329419, pr329419⟩
private theorem pr329471 : Nat.Prime 329471 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv47,pv701]) (by decide +kernel)
def pv329471 : PrimeValue := ⟨329471, pr329471⟩
private theorem pr329489 : Nat.Prime 329489 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv20593]) (by decide +kernel)
def pv329489 : PrimeValue := ⟨329489, pr329489⟩
private theorem pr329503 : Nat.Prime 329503 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv54917]) (by decide +kernel)
def pv329503 : PrimeValue := ⟨329503, pr329503⟩
private theorem pr329557 : Nat.Prime 329557 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv947]) (by decide +kernel)
def pv329557 : PrimeValue := ⟨329557, pr329557⟩
private theorem pr329587 : Nat.Prime 329587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv163,pv337]) (by decide +kernel)
def pv329587 : PrimeValue := ⟨329587, pr329587⟩
private theorem pr329627 : Nat.Prime 329627 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv14983]) (by decide +kernel)
def pv329627 : PrimeValue := ⟨329627, pr329627⟩
private theorem pr329629 : Nat.Prime 329629 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv2113]) (by decide +kernel)
def pv329629 : PrimeValue := ⟨329629, pr329629⟩
private theorem pr329639 : Nat.Prime 329639 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv43,pv3833]) (by decide +kernel)
def pv329639 : PrimeValue := ⟨329639, pr329639⟩
private theorem pr329663 : Nat.Prime 329663 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv164831]) (by decide +kernel)
def pv329663 : PrimeValue := ⟨329663, pr329663⟩
private theorem pr329671 : Nat.Prime 329671 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv37]) (by decide +kernel)
def pv329671 : PrimeValue := ⟨329671, pr329671⟩
private theorem pr329677 : Nat.Prime 329677 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv83,pv331]) (by decide +kernel)
def pv329677 : PrimeValue := ⟨329677, pr329677⟩
private theorem pr329683 : Nat.Prime 329683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv2389]) (by decide +kernel)
def pv329683 : PrimeValue := ⟨329683, pr329683⟩
private theorem pr329687 : Nat.Prime 329687 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv23549]) (by decide +kernel)
def pv329687 : PrimeValue := ⟨329687, pr329687⟩
private theorem pr329711 : Nat.Prime 329711 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv32971]) (by decide +kernel)
def pv329711 : PrimeValue := ⟨329711, pr329711⟩
private theorem pr329761 : Nat.Prime 329761 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv229]) (by decide +kernel)
def pv329761 : PrimeValue := ⟨329761, pr329761⟩
private theorem pr329773 : Nat.Prime 329773 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv27481]) (by decide +kernel)
def pv329773 : PrimeValue := ⟨329773, pr329773⟩
private theorem pr329801 : Nat.Prime 329801 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17,pv97]) (by decide +kernel)
def pv329801 : PrimeValue := ⟨329801, pr329801⟩
private theorem pr329891 : Nat.Prime 329891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv2999]) (by decide +kernel)
def pv329891 : PrimeValue := ⟨329891, pr329891⟩
private theorem pr329947 : Nat.Prime 329947 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv127,pv433]) (by decide +kernel)
def pv329947 : PrimeValue := ⟨329947, pr329947⟩
private theorem pr329977 : Nat.Prime 329977 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv4583]) (by decide +kernel)
def pv329977 : PrimeValue := ⟨329977, pr329977⟩
private theorem pr329999 : Nat.Prime 329999 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv164999]) (by decide +kernel)
def pv329999 : PrimeValue := ⟨329999, pr329999⟩
private theorem pr330017 : Nat.Prime 330017 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv10313]) (by decide +kernel)
def pv330017 : PrimeValue := ⟨330017, pr330017⟩
private theorem pr330019 : Nat.Prime 330019 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv4231]) (by decide +kernel)
def pv330019 : PrimeValue := ⟨330019, pr330019⟩
private theorem pr330037 : Nat.Prime 330037 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv3929]) (by decide +kernel)
def pv330037 : PrimeValue := ⟨330037, pr330037⟩
private theorem pr330041 : Nat.Prime 330041 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv37,pv223]) (by decide +kernel)
def pv330041 : PrimeValue := ⟨330041, pr330041⟩
private theorem pr330047 : Nat.Prime 330047 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv59,pv2797]) (by decide +kernel)
def pv330047 : PrimeValue := ⟨330047, pr330047⟩
private theorem pr330061 : Nat.Prime 330061 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv5501]) (by decide +kernel)
def pv330061 : PrimeValue := ⟨330061, pr330061⟩
private theorem pr330097 : Nat.Prime 330097 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv23]) (by decide +kernel)
def pv330097 : PrimeValue := ⟨330097, pr330097⟩
private theorem pr330103 : Nat.Prime 330103 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv6113]) (by decide +kernel)
def pv330103 : PrimeValue := ⟨330103, pr330103⟩
private theorem pr330133 : Nat.Prime 330133 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv41,pv61]) (by decide +kernel)
def pv330133 : PrimeValue := ⟨330133, pr330133⟩
private theorem pr330139 : Nat.Prime 330139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv18341]) (by decide +kernel)
def pv330139 : PrimeValue := ⟨330139, pr330139⟩
private theorem pr330149 : Nat.Prime 330149 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv13,pv907]) (by decide +kernel)
def pv330149 : PrimeValue := ⟨330149, pr330149⟩
private theorem pr330167 : Nat.Prime 330167 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv165083]) (by decide +kernel)
def pv330167 : PrimeValue := ⟨330167, pr330167⟩
private theorem pr330229 : Nat.Prime 330229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv9173]) (by decide +kernel)
def pv330229 : PrimeValue := ⟨330229, pr330229⟩
private theorem pr330271 : Nat.Prime 330271 :=
  checkPrime_prime (q := pv59) (ls := [pv2,pv3,pv5,pv101,pv109]) (by decide +kernel)
def pv330271 : PrimeValue := ⟨330271, pr330271⟩
private theorem pr330289 : Nat.Prime 330289 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv983]) (by decide +kernel)
def pv330289 : PrimeValue := ⟨330289, pr330289⟩
private theorem pr330311 : Nat.Prime 330311 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv17,pv29,pv67]) (by decide +kernel)
def pv330311 : PrimeValue := ⟨330311, pr330311⟩
private theorem pr330313 : Nat.Prime 330313 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13763]) (by decide +kernel)
def pv330313 : PrimeValue := ⟨330313, pr330313⟩
private theorem pr330329 : Nat.Prime 330329 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv157,pv263]) (by decide +kernel)
def pv330329 : PrimeValue := ⟨330329, pr330329⟩
private theorem pr330347 : Nat.Prime 330347 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv165173]) (by decide +kernel)
def pv330347 : PrimeValue := ⟨330347, pr330347⟩
private theorem pr330359 : Nat.Prime 330359 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv3371]) (by decide +kernel)
def pv330359 : PrimeValue := ⟨330359, pr330359⟩
private theorem pr330409 : Nat.Prime 330409 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv13,pv353]) (by decide +kernel)
def pv330409 : PrimeValue := ⟨330409, pr330409⟩
private theorem pr330431 : Nat.Prime 330431 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv173,pv191]) (by decide +kernel)
def pv330431 : PrimeValue := ⟨330431, pr330431⟩
private theorem pr330433 : Nat.Prime 330433 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv1721]) (by decide +kernel)
def pv330433 : PrimeValue := ⟨330433, pr330433⟩
private theorem pr330439 : Nat.Prime 330439 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv55073]) (by decide +kernel)
def pv330439 : PrimeValue := ⟨330439, pr330439⟩
private theorem pr330509 : Nat.Prime 330509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53,pv1559]) (by decide +kernel)
def pv330509 : PrimeValue := ⟨330509, pr330509⟩
private theorem pr330557 : Nat.Prime 330557 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv3593]) (by decide +kernel)
def pv330557 : PrimeValue := ⟨330557, pr330557⟩
private theorem pr330563 : Nat.Prime 330563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv8699]) (by decide +kernel)
def pv330563 : PrimeValue := ⟨330563, pr330563⟩
private theorem pr330569 : Nat.Prime 330569 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv5903]) (by decide +kernel)
def pv330569 : PrimeValue := ⟨330569, pr330569⟩
private theorem pr330587 : Nat.Prime 330587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv165293]) (by decide +kernel)
def pv330587 : PrimeValue := ⟨330587, pr330587⟩
private theorem pr330607 : Nat.Prime 330607 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv18367]) (by decide +kernel)
def pv330607 : PrimeValue := ⟨330607, pr330607⟩
private theorem pr330641 : Nat.Prime 330641 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv4133]) (by decide +kernel)
def pv330641 : PrimeValue := ⟨330641, pr330641⟩
private theorem pr330643 : Nat.Prime 330643 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv157]) (by decide +kernel)
def pv330643 : PrimeValue := ⟨330643, pr330643⟩
private theorem pr330661 : Nat.Prime 330661 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv11,pv167]) (by decide +kernel)
def pv330661 : PrimeValue := ⟨330661, pr330661⟩
private theorem pr330679 : Nat.Prime 330679 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv18371]) (by decide +kernel)
def pv330679 : PrimeValue := ⟨330679, pr330679⟩
private theorem pr330697 : Nat.Prime 330697 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1531]) (by decide +kernel)
def pv330697 : PrimeValue := ⟨330697, pr330697⟩
private theorem pr330703 : Nat.Prime 330703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv55117]) (by decide +kernel)
def pv330703 : PrimeValue := ⟨330703, pr330703⟩
private theorem pr330719 : Nat.Prime 330719 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv17,pv71,pv137]) (by decide +kernel)
def pv330719 : PrimeValue := ⟨330719, pr330719⟩
private theorem pr330721 : Nat.Prime 330721 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv13,pv53]) (by decide +kernel)
def pv330721 : PrimeValue := ⟨330721, pr330721⟩
private theorem pr330731 : Nat.Prime 330731 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv33073]) (by decide +kernel)
def pv330731 : PrimeValue := ⟨330731, pr330731⟩
private theorem pr330787 : Nat.Prime 330787 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv23,pv47]) (by decide +kernel)
def pv330787 : PrimeValue := ⟨330787, pr330787⟩
private theorem pr330791 : Nat.Prime 330791 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv19,pv1741]) (by decide +kernel)
def pv330791 : PrimeValue := ⟨330791, pr330791⟩
private theorem pr330839 : Nat.Prime 330839 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv83,pv1993]) (by decide +kernel)
def pv330839 : PrimeValue := ⟨330839, pr330839⟩
private theorem pr330853 : Nat.Prime 330853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv79,pv349]) (by decide +kernel)
def pv330853 : PrimeValue := ⟨330853, pr330853⟩
private theorem pr330859 : Nat.Prime 330859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv557]) (by decide +kernel)
def pv330859 : PrimeValue := ⟨330859, pr330859⟩
private theorem pr330887 : Nat.Prime 330887 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv165443]) (by decide +kernel)
def pv330887 : PrimeValue := ⟨330887, pr330887⟩
private theorem pr330899 : Nat.Prime 330899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv165449]) (by decide +kernel)
def pv330899 : PrimeValue := ⟨330899, pr330899⟩
private theorem pr330907 : Nat.Prime 330907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv131,pv421]) (by decide +kernel)
def pv330907 : PrimeValue := ⟨330907, pr330907⟩
private theorem pr331027 : Nat.Prime 331027 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv55171]) (by decide +kernel)
def pv331027 : PrimeValue := ⟨331027, pr331027⟩
private theorem pr331031 : Nat.Prime 331031 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv4729]) (by decide +kernel)
def pv331031 : PrimeValue := ⟨331031, pr331031⟩
private theorem pr331141 : Nat.Prime 331141 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv5519]) (by decide +kernel)
def pv331141 : PrimeValue := ⟨331141, pr331141⟩
private theorem pr331153 : Nat.Prime 331153 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv6899]) (by decide +kernel)
def pv331153 : PrimeValue := ⟨331153, pr331153⟩
private theorem pr331159 : Nat.Prime 331159 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv97,pv569]) (by decide +kernel)
def pv331159 : PrimeValue := ⟨331159, pr331159⟩
private theorem pr331183 : Nat.Prime 331183 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv6133]) (by decide +kernel)
def pv331183 : PrimeValue := ⟨331183, pr331183⟩
private theorem pr331217 : Nat.Prime 331217 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv127,pv163]) (by decide +kernel)
def pv331217 : PrimeValue := ⟨331217, pr331217⟩
private theorem pr331241 : Nat.Prime 331241 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv13]) (by decide +kernel)
def pv331241 : PrimeValue := ⟨331241, pr331241⟩
private theorem pr331259 : Nat.Prime 331259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv89,pv1861]) (by decide +kernel)
def pv331259 : PrimeValue := ⟨331259, pr331259⟩
private theorem pr331283 : Nat.Prime 331283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv23663]) (by decide +kernel)
def pv331283 : PrimeValue := ⟨331283, pr331283⟩
private theorem pr331301 : Nat.Prime 331301 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv3313]) (by decide +kernel)
def pv331301 : PrimeValue := ⟨331301, pr331301⟩
private theorem pr331319 : Nat.Prime 331319 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv13,pv12743]) (by decide +kernel)
def pv331319 : PrimeValue := ⟨331319, pr331319⟩
private theorem pr331333 : Nat.Prime 331333 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv27611]) (by decide +kernel)
def pv331333 : PrimeValue := ⟨331333, pr331333⟩
private theorem pr331337 : Nat.Prime 331337 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv83,pv499]) (by decide +kernel)
def pv331337 : PrimeValue := ⟨331337, pr331337⟩
private theorem pr331391 : Nat.Prime 331391 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv31,pv1069]) (by decide +kernel)
def pv331391 : PrimeValue := ⟨331391, pr331391⟩
private theorem pr331423 : Nat.Prime 331423 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv607]) (by decide +kernel)
def pv331423 : PrimeValue := ⟨331423, pr331423⟩
private theorem pr331447 : Nat.Prime 331447 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv37,pv1493]) (by decide +kernel)
def pv331447 : PrimeValue := ⟨331447, pr331447⟩
private theorem pr331501 : Nat.Prime 331501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv17]) (by decide +kernel)
def pv331501 : PrimeValue := ⟨331501, pr331501⟩
private theorem pr331537 : Nat.Prime 331537 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv6907]) (by decide +kernel)
def pv331537 : PrimeValue := ⟨331537, pr331537⟩
private theorem pr331543 : Nat.Prime 331543 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv113,pv163]) (by decide +kernel)
def pv331543 : PrimeValue := ⟨331543, pr331543⟩
private theorem pr331549 : Nat.Prime 331549 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv7,pv3947]) (by decide +kernel)
def pv331549 : PrimeValue := ⟨331549, pr331549⟩
private theorem pr331603 : Nat.Prime 331603 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv3251]) (by decide +kernel)
def pv331603 : PrimeValue := ⟨331603, pr331603⟩
private theorem pr331613 : Nat.Prime 331613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv82903]) (by decide +kernel)
def pv331613 : PrimeValue := ⟨331613, pr331613⟩
private theorem pr331663 : Nat.Prime 331663 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv167,pv331]) (by decide +kernel)
def pv331663 : PrimeValue := ⟨331663, pr331663⟩
private theorem pr331691 : Nat.Prime 331691 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv41,pv809]) (by decide +kernel)
def pv331691 : PrimeValue := ⟨331691, pr331691⟩
private theorem pr331693 : Nat.Prime 331693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv131,pv211]) (by decide +kernel)
def pv331693 : PrimeValue := ⟨331693, pr331693⟩
private theorem pr331739 : Nat.Prime 331739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv17,pv887]) (by decide +kernel)
def pv331739 : PrimeValue := ⟨331739, pr331739⟩
private theorem pr331753 : Nat.Prime 331753 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23,pv601]) (by decide +kernel)
def pv331753 : PrimeValue := ⟨331753, pr331753⟩
private theorem pr331769 : Nat.Prime 331769 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv113,pv367]) (by decide +kernel)
def pv331769 : PrimeValue := ⟨331769, pr331769⟩
private theorem pr331781 : Nat.Prime 331781 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv53,pv313]) (by decide +kernel)
def pv331781 : PrimeValue := ⟨331781, pr331781⟩
private theorem pr331801 : Nat.Prime 331801 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv79]) (by decide +kernel)
def pv331801 : PrimeValue := ⟨331801, pr331801⟩
private theorem pr331841 : Nat.Prime 331841 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv17,pv61]) (by decide +kernel)
def pv331841 : PrimeValue := ⟨331841, pr331841⟩
private theorem pr331843 : Nat.Prime 331843 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv7901]) (by decide +kernel)
def pv331843 : PrimeValue := ⟨331843, pr331843⟩
private theorem pr331889 : Nat.Prime 331889 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv20743]) (by decide +kernel)
def pv331889 : PrimeValue := ⟨331889, pr331889⟩
private theorem pr331907 : Nat.Prime 331907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv263,pv631]) (by decide +kernel)
def pv331907 : PrimeValue := ⟨331907, pr331907⟩
private theorem pr331921 : Nat.Prime 331921 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv461]) (by decide +kernel)
def pv331921 : PrimeValue := ⟨331921, pr331921⟩
private theorem pr331937 : Nat.Prime 331937 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv23,pv41]) (by decide +kernel)
def pv331937 : PrimeValue := ⟨331937, pr331937⟩
private theorem pr331997 : Nat.Prime 331997 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv71,pv167]) (by decide +kernel)
def pv331997 : PrimeValue := ⟨331997, pr331997⟩
private theorem pr332009 : Nat.Prime 332009 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv47,pv883]) (by decide +kernel)
def pv332009 : PrimeValue := ⟨332009, pr332009⟩
private theorem pr332053 : Nat.Prime 332053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv59,pv67]) (by decide +kernel)
def pv332053 : PrimeValue := ⟨332053, pr332053⟩
private theorem pr332069 : Nat.Prime 332069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv7547]) (by decide +kernel)
def pv332069 : PrimeValue := ⟨332069, pr332069⟩
private theorem pr332081 : Nat.Prime 332081 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv593]) (by decide +kernel)
def pv332081 : PrimeValue := ⟨332081, pr332081⟩
private theorem pr332099 : Nat.Prime 332099 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv53,pv241]) (by decide +kernel)
def pv332099 : PrimeValue := ⟨332099, pr332099⟩
private theorem pr332147 : Nat.Prime 332147 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv9769]) (by decide +kernel)
def pv332147 : PrimeValue := ⟨332147, pr332147⟩
private theorem pr332159 : Nat.Prime 332159 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv19,pv8741]) (by decide +kernel)
def pv332159 : PrimeValue := ⟨332159, pr332159⟩
private theorem pr332161 : Nat.Prime 332161 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv173]) (by decide +kernel)
def pv332161 : PrimeValue := ⟨332161, pr332161⟩
private theorem pr332191 : Nat.Prime 332191 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv3691]) (by decide +kernel)
def pv332191 : PrimeValue := ⟨332191, pr332191⟩
private theorem pr332201 : Nat.Prime 332201 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv151]) (by decide +kernel)
def pv332201 : PrimeValue := ⟨332201, pr332201⟩
private theorem pr332203 : Nat.Prime 332203 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv4259]) (by decide +kernel)
def pv332203 : PrimeValue := ⟨332203, pr332203⟩
private theorem pr332207 : Nat.Prime 332207 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv61,pv389]) (by decide +kernel)
def pv332207 : PrimeValue := ⟨332207, pr332207⟩
private theorem pr332251 : Nat.Prime 332251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv443]) (by decide +kernel)
def pv332251 : PrimeValue := ⟨332251, pr332251⟩
private theorem pr332309 : Nat.Prime 332309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv83077]) (by decide +kernel)
def pv332309 : PrimeValue := ⟨332309, pr332309⟩
private theorem pr332317 : Nat.Prime 332317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv181]) (by decide +kernel)
def pv332317 : PrimeValue := ⟨332317, pr332317⟩
private theorem pr332399 : Nat.Prime 332399 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv29,pv521]) (by decide +kernel)
def pv332399 : PrimeValue := ⟨332399, pr332399⟩
private theorem pr332411 : Nat.Prime 332411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv2557]) (by decide +kernel)
def pv332411 : PrimeValue := ⟨332411, pr332411⟩
private theorem pr332417 : Nat.Prime 332417 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv53]) (by decide +kernel)
def pv332417 : PrimeValue := ⟨332417, pr332417⟩
private theorem pr332441 : Nat.Prime 332441 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv8311]) (by decide +kernel)
def pv332441 : PrimeValue := ⟨332441, pr332441⟩
private theorem pr332461 : Nat.Prime 332461 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1847]) (by decide +kernel)
def pv332461 : PrimeValue := ⟨332461, pr332461⟩
private theorem pr332471 : Nat.Prime 332471 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv33247]) (by decide +kernel)
def pv332471 : PrimeValue := ⟨332471, pr332471⟩
private theorem pr332561 : Nat.Prime 332561 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv4157]) (by decide +kernel)
def pv332561 : PrimeValue := ⟨332561, pr332561⟩
private theorem pr332611 : Nat.Prime 332611 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11087]) (by decide +kernel)
def pv332611 : PrimeValue := ⟨332611, pr332611⟩
private theorem pr332617 : Nat.Prime 332617 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13859]) (by decide +kernel)
def pv332617 : PrimeValue := ⟨332617, pr332617⟩
private theorem pr332623 : Nat.Prime 332623 :=
  checkPrime_prime (q := pv61) (ls := [pv2,pv3,pv17,pv1087]) (by decide +kernel)
def pv332623 : PrimeValue := ⟨332623, pr332623⟩
private theorem pr332687 : Nat.Prime 332687 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv397,pv419]) (by decide +kernel)
def pv332687 : PrimeValue := ⟨332687, pr332687⟩
private theorem pr332711 : Nat.Prime 332711 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv97]) (by decide +kernel)
def pv332711 : PrimeValue := ⟨332711, pr332711⟩
private theorem pr332729 : Nat.Prime 332729 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv19,pv199]) (by decide +kernel)
def pv332729 : PrimeValue := ⟨332729, pr332729⟩
private theorem pr332743 : Nat.Prime 332743 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv55457]) (by decide +kernel)
def pv332743 : PrimeValue := ⟨332743, pr332743⟩
private theorem pr332749 : Nat.Prime 332749 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv13,pv79]) (by decide +kernel)
def pv332749 : PrimeValue := ⟨332749, pr332749⟩
private theorem pr332779 : Nat.Prime 332779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv1499]) (by decide +kernel)
def pv332779 : PrimeValue := ⟨332779, pr332779⟩
private theorem pr332791 : Nat.Prime 332791 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11093]) (by decide +kernel)
def pv332791 : PrimeValue := ⟨332791, pr332791⟩
private theorem pr332837 : Nat.Prime 332837 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11887]) (by decide +kernel)
def pv332837 : PrimeValue := ⟨332837, pr332837⟩
private theorem pr332873 : Nat.Prime 332873 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv41609]) (by decide +kernel)
def pv332873 : PrimeValue := ⟨332873, pr332873⟩
private theorem pr332887 : Nat.Prime 332887 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv109,pv509]) (by decide +kernel)
def pv332887 : PrimeValue := ⟨332887, pr332887⟩
private theorem pr332903 : Nat.Prime 332903 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv23,pv7237]) (by decide +kernel)
def pv332903 : PrimeValue := ⟨332903, pr332903⟩
private theorem pr332921 : Nat.Prime 332921 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv29,pv41]) (by decide +kernel)
def pv332921 : PrimeValue := ⟨332921, pr332921⟩
private theorem pr332933 : Nat.Prime 332933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv83233]) (by decide +kernel)
def pv332933 : PrimeValue := ⟨332933, pr332933⟩
private theorem pr332947 : Nat.Prime 332947 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv53,pv349]) (by decide +kernel)
def pv332947 : PrimeValue := ⟨332947, pr332947⟩
private theorem pr332951 : Nat.Prime 332951 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv6659]) (by decide +kernel)
def pv332951 : PrimeValue := ⟨332951, pr332951⟩
private theorem pr332987 : Nat.Prime 332987 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv331,pv503]) (by decide +kernel)
def pv332987 : PrimeValue := ⟨332987, pr332987⟩
private theorem pr333019 : Nat.Prime 333019 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv881]) (by decide +kernel)
def pv333019 : PrimeValue := ⟨333019, pr333019⟩
private theorem pr333031 : Nat.Prime 333031 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv17,pv653]) (by decide +kernel)
def pv333031 : PrimeValue := ⟨333031, pr333031⟩
private theorem pr333041 : Nat.Prime 333041 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv23,pv181]) (by decide +kernel)
def pv333041 : PrimeValue := ⟨333041, pr333041⟩
private theorem pr333071 : Nat.Prime 333071 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv19,pv1753]) (by decide +kernel)
def pv333071 : PrimeValue := ⟨333071, pr333071⟩
private theorem pr333097 : Nat.Prime 333097 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13879]) (by decide +kernel)
def pv333097 : PrimeValue := ⟨333097, pr333097⟩
private theorem pr333101 : Nat.Prime 333101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv3331]) (by decide +kernel)
def pv333101 : PrimeValue := ⟨333101, pr333101⟩
private theorem pr333107 : Nat.Prime 333107 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv151,pv1103]) (by decide +kernel)
def pv333107 : PrimeValue := ⟨333107, pr333107⟩
private theorem pr333139 : Nat.Prime 333139 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv4271]) (by decide +kernel)
def pv333139 : PrimeValue := ⟨333139, pr333139⟩
private theorem pr333227 : Nat.Prime 333227 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv166613]) (by decide +kernel)
def pv333227 : PrimeValue := ⟨333227, pr333227⟩
private theorem pr333233 : Nat.Prime 333233 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv59,pv353]) (by decide +kernel)
def pv333233 : PrimeValue := ⟨333233, pr333233⟩
private theorem pr333283 : Nat.Prime 333283 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv55547]) (by decide +kernel)
def pv333283 : PrimeValue := ⟨333283, pr333283⟩
private theorem pr333299 : Nat.Prime 333299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv19,pv179]) (by decide +kernel)
def pv333299 : PrimeValue := ⟨333299, pr333299⟩
private theorem pr333323 : Nat.Prime 333323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv109,pv139]) (by decide +kernel)
def pv333323 : PrimeValue := ⟨333323, pr333323⟩
private theorem pr333331 : Nat.Prime 333331 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv41,pv271]) (by decide +kernel)
def pv333331 : PrimeValue := ⟨333331, pr333331⟩
private theorem pr333341 : Nat.Prime 333341 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv2381]) (by decide +kernel)
def pv333341 : PrimeValue := ⟨333341, pr333341⟩
private theorem pr333397 : Nat.Prime 333397 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv333397 : PrimeValue := ⟨333397, pr333397⟩
private theorem pr333427 : Nat.Prime 333427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv61,pv911]) (by decide +kernel)
def pv333427 : PrimeValue := ⟨333427, pr333427⟩
private theorem pr333433 : Nat.Prime 333433 :=
  checkPrime_prime (q := pv47) (ls := [pv2,pv3,pv11,pv421]) (by decide +kernel)
def pv333433 : PrimeValue := ⟨333433, pr333433⟩
private theorem pr333479 : Nat.Prime 333479 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv166739]) (by decide +kernel)
def pv333479 : PrimeValue := ⟨333479, pr333479⟩
private theorem pr333491 : Nat.Prime 333491 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv33349]) (by decide +kernel)
def pv333491 : PrimeValue := ⟨333491, pr333491⟩
private theorem pr333493 : Nat.Prime 333493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv27791]) (by decide +kernel)
def pv333493 : PrimeValue := ⟨333493, pr333493⟩
private theorem pr333533 : Nat.Prime 333533 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv83383]) (by decide +kernel)
def pv333533 : PrimeValue := ⟨333533, pr333533⟩
private theorem pr333539 : Nat.Prime 333539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79,pv2111]) (by decide +kernel)
def pv333539 : PrimeValue := ⟨333539, pr333539⟩
private theorem pr333563 : Nat.Prime 333563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv166781]) (by decide +kernel)
def pv333563 : PrimeValue := ⟨333563, pr333563⟩
private theorem pr333581 : Nat.Prime 333581 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv13,pv1283]) (by decide +kernel)
def pv333581 : PrimeValue := ⟨333581, pr333581⟩
private theorem pr333589 : Nat.Prime 333589 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv27799]) (by decide +kernel)
def pv333589 : PrimeValue := ⟨333589, pr333589⟩
private theorem pr333631 : Nat.Prime 333631 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv337]) (by decide +kernel)
def pv333631 : PrimeValue := ⟨333631, pr333631⟩
private theorem pr333673 : Nat.Prime 333673 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13903]) (by decide +kernel)
def pv333673 : PrimeValue := ⟨333673, pr333673⟩
private theorem pr333679 : Nat.Prime 333679 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv2927]) (by decide +kernel)
def pv333679 : PrimeValue := ⟨333679, pr333679⟩
private theorem pr333701 : Nat.Prime 333701 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv47,pv71]) (by decide +kernel)
def pv333701 : PrimeValue := ⟨333701, pr333701⟩
private theorem pr333713 : Nat.Prime 333713 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv20857]) (by decide +kernel)
def pv333713 : PrimeValue := ⟨333713, pr333713⟩
private theorem pr333719 : Nat.Prime 333719 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv7,pv11,pv197]) (by decide +kernel)
def pv333719 : PrimeValue := ⟨333719, pr333719⟩
private theorem pr333721 : Nat.Prime 333721 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv103]) (by decide +kernel)
def pv333721 : PrimeValue := ⟨333721, pr333721⟩
private theorem pr333737 : Nat.Prime 333737 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv3209]) (by decide +kernel)
def pv333737 : PrimeValue := ⟨333737, pr333737⟩
private theorem pr333779 : Nat.Prime 333779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv9817]) (by decide +kernel)
def pv333779 : PrimeValue := ⟨333779, pr333779⟩
private theorem pr333787 : Nat.Prime 333787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv55631]) (by decide +kernel)
def pv333787 : PrimeValue := ⟨333787, pr333787⟩
private theorem pr333791 : Nat.Prime 333791 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv5,pv29,pv1151]) (by decide +kernel)
def pv333791 : PrimeValue := ⟨333791, pr333791⟩
private theorem pr333793 : Nat.Prime 333793 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv61]) (by decide +kernel)
def pv333793 : PrimeValue := ⟨333793, pr333793⟩
private theorem pr333821 : Nat.Prime 333821 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv16691]) (by decide +kernel)
def pv333821 : PrimeValue := ⟨333821, pr333821⟩
private theorem pr333929 : Nat.Prime 333929 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv67,pv89]) (by decide +kernel)
def pv333929 : PrimeValue := ⟨333929, pr333929⟩
private theorem pr333941 : Nat.Prime 333941 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv59,pv283]) (by decide +kernel)
def pv333941 : PrimeValue := ⟨333941, pr333941⟩
private theorem pr333973 : Nat.Prime 333973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv9277]) (by decide +kernel)
def pv333973 : PrimeValue := ⟨333973, pr333973⟩
private theorem pr333997 : Nat.Prime 333997 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv13,pv2141]) (by decide +kernel)
def pv333997 : PrimeValue := ⟨333997, pr333997⟩
private theorem pr334031 : Nat.Prime 334031 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv33403]) (by decide +kernel)
def pv334031 : PrimeValue := ⟨334031, pr334031⟩
private theorem pr334057 : Nat.Prime 334057 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv31,pv449]) (by decide +kernel)
def pv334057 : PrimeValue := ⟨334057, pr334057⟩
private theorem pr334069 : Nat.Prime 334069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv41,pv97]) (by decide +kernel)
def pv334069 : PrimeValue := ⟨334069, pr334069⟩
private theorem pr334093 : Nat.Prime 334093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv2531]) (by decide +kernel)
def pv334093 : PrimeValue := ⟨334093, pr334093⟩
private theorem pr334127 : Nat.Prime 334127 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv71,pv181]) (by decide +kernel)
def pv334127 : PrimeValue := ⟨334127, pr334127⟩
private theorem pr334157 : Nat.Prime 334157 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv139,pv601]) (by decide +kernel)
def pv334157 : PrimeValue := ⟨334157, pr334157⟩
private theorem pr334171 : Nat.Prime 334171 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv47,pv79]) (by decide +kernel)
def pv334171 : PrimeValue := ⟨334171, pr334171⟩
private theorem pr334231 : Nat.Prime 334231 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv13,pv857]) (by decide +kernel)
def pv334231 : PrimeValue := ⟨334231, pr334231⟩
private theorem pr334247 : Nat.Prime 334247 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv15193]) (by decide +kernel)
def pv334247 : PrimeValue := ⟨334247, pr334247⟩
private theorem pr334261 : Nat.Prime 334261 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv619]) (by decide +kernel)
def pv334261 : PrimeValue := ⟨334261, pr334261⟩
private theorem pr334289 : Nat.Prime 334289 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv1229]) (by decide +kernel)
def pv334289 : PrimeValue := ⟨334289, pr334289⟩
private theorem pr334333 : Nat.Prime 334333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv251]) (by decide +kernel)
def pv334333 : PrimeValue := ⟨334333, pr334333⟩
private theorem pr334349 : Nat.Prime 334349 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11941]) (by decide +kernel)
def pv334349 : PrimeValue := ⟨334349, pr334349⟩
private theorem pr334363 : Nat.Prime 334363 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv19,pv419]) (by decide +kernel)
def pv334363 : PrimeValue := ⟨334363, pr334363⟩
private theorem pr334387 : Nat.Prime 334387 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv1429]) (by decide +kernel)
def pv334387 : PrimeValue := ⟨334387, pr334387⟩
private theorem pr334421 : Nat.Prime 334421 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23,pv727]) (by decide +kernel)
def pv334421 : PrimeValue := ⟨334421, pr334421⟩
private theorem pr334487 : Nat.Prime 334487 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv29,pv73,pv79]) (by decide +kernel)
def pv334487 : PrimeValue := ⟨334487, pr334487⟩
private theorem pr334493 : Nat.Prime 334493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv4919]) (by decide +kernel)
def pv334493 : PrimeValue := ⟨334493, pr334493⟩
private theorem pr334507 : Nat.Prime 334507 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv197,pv283]) (by decide +kernel)
def pv334507 : PrimeValue := ⟨334507, pr334507⟩
private theorem pr334511 : Nat.Prime 334511 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv11,pv3041]) (by decide +kernel)
def pv334511 : PrimeValue := ⟨334511, pr334511⟩
private theorem pr334513 : Nat.Prime 334513 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv23,pv101]) (by decide +kernel)
def pv334513 : PrimeValue := ⟨334513, pr334513⟩
private theorem pr334541 : Nat.Prime 334541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv43,pv389]) (by decide +kernel)
def pv334541 : PrimeValue := ⟨334541, pr334541⟩
private theorem pr334549 : Nat.Prime 334549 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv9293]) (by decide +kernel)
def pv334549 : PrimeValue := ⟨334549, pr334549⟩
private theorem pr334561 : Nat.Prime 334561 :=
  checkPrime_prime (q := pv47) (ls := [pv2,pv3,pv5,pv17,pv41]) (by decide +kernel)
def pv334561 : PrimeValue := ⟨334561, pr334561⟩
private theorem pr334603 : Nat.Prime 334603 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29,pv641]) (by decide +kernel)
def pv334603 : PrimeValue := ⟨334603, pr334603⟩
private theorem pr334619 : Nat.Prime 334619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv167309]) (by decide +kernel)
def pv334619 : PrimeValue := ⟨334619, pr334619⟩
private theorem pr334637 : Nat.Prime 334637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv269,pv311]) (by decide +kernel)
def pv334637 : PrimeValue := ⟨334637, pr334637⟩
private theorem pr334643 : Nat.Prime 334643 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv11,pv41,pv53]) (by decide +kernel)
def pv334643 : PrimeValue := ⟨334643, pr334643⟩
private theorem pr334661 : Nat.Prime 334661 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv29,pv577]) (by decide +kernel)
def pv334661 : PrimeValue := ⟨334661, pr334661⟩
private theorem pr334667 : Nat.Prime 334667 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv8807]) (by decide +kernel)
def pv334667 : PrimeValue := ⟨334667, pr334667⟩
private theorem pr334717 : Nat.Prime 334717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv27893]) (by decide +kernel)
def pv334717 : PrimeValue := ⟨334717, pr334717⟩
private theorem pr334721 : Nat.Prime 334721 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv523]) (by decide +kernel)
def pv334721 : PrimeValue := ⟨334721, pr334721⟩
private theorem pr334727 : Nat.Prime 334727 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv23909]) (by decide +kernel)
def pv334727 : PrimeValue := ⟨334727, pr334727⟩
private theorem pr334751 : Nat.Prime 334751 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv103]) (by decide +kernel)
def pv334751 : PrimeValue := ⟨334751, pr334751⟩
private theorem pr334777 : Nat.Prime 334777 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv3,pv13,pv29,pv37]) (by decide +kernel)
def pv334777 : PrimeValue := ⟨334777, pr334777⟩
private theorem pr334783 : Nat.Prime 334783 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv2657]) (by decide +kernel)
def pv334783 : PrimeValue := ⟨334783, pr334783⟩
private theorem pr334861 : Nat.Prime 334861 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv5581]) (by decide +kernel)
def pv334861 : PrimeValue := ⟨334861, pr334861⟩
private theorem pr334931 : Nat.Prime 334931 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv33493]) (by decide +kernel)
def pv334931 : PrimeValue := ⟨334931, pr334931⟩
private theorem pr334963 : Nat.Prime 334963 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv6203]) (by decide +kernel)
def pv334963 : PrimeValue := ⟨334963, pr334963⟩
private theorem pr334973 : Nat.Prime 334973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv23,pv331]) (by decide +kernel)
def pv334973 : PrimeValue := ⟨334973, pr334973⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
