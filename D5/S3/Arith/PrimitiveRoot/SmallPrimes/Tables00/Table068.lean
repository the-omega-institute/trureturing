/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table068
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table068.pv210403
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table009
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table014
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table015
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table039
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table040

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr210403 : Nat.Prime 210403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11689]) (by decide +kernel)
def pv210403 : PrimeValue := ⟨210403, pr210403⟩
private theorem pr210421 : Nat.Prime 210421 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv167]) (by decide +kernel)
def pv210421 : PrimeValue := ⟨210421, pr210421⟩
private theorem pr210437 : Nat.Prime 210437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv52609]) (by decide +kernel)
def pv210437 : PrimeValue := ⟨210437, pr210437⟩
private theorem pr210481 : Nat.Prime 210481 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv877]) (by decide +kernel)
def pv210481 : PrimeValue := ⟨210481, pr210481⟩
private theorem pr210487 : Nat.Prime 210487 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv35081]) (by decide +kernel)
def pv210487 : PrimeValue := ⟨210487, pr210487⟩
private theorem pr210499 : Nat.Prime 210499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv35083]) (by decide +kernel)
def pv210499 : PrimeValue := ⟨210499, pr210499⟩
private theorem pr210523 : Nat.Prime 210523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv2699]) (by decide +kernel)
def pv210523 : PrimeValue := ⟨210523, pr210523⟩
private theorem pr210601 : Nat.Prime 210601 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv210601 : PrimeValue := ⟨210601, pr210601⟩
private theorem pr210619 : Nat.Prime 210619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11701]) (by decide +kernel)
def pv210619 : PrimeValue := ⟨210619, pr210619⟩
private theorem pr210631 : Nat.Prime 210631 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv17,pv59]) (by decide +kernel)
def pv210631 : PrimeValue := ⟨210631, pr210631⟩
private theorem pr210643 : Nat.Prime 210643 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv35107]) (by decide +kernel)
def pv210643 : PrimeValue := ⟨210643, pr210643⟩
private theorem pr210659 : Nat.Prime 210659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv41,pv367]) (by decide +kernel)
def pv210659 : PrimeValue := ⟨210659, pr210659⟩
private theorem pr210671 : Nat.Prime 210671 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv21067]) (by decide +kernel)
def pv210671 : PrimeValue := ⟨210671, pr210671⟩
private theorem pr210713 : Nat.Prime 210713 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv26339]) (by decide +kernel)
def pv210713 : PrimeValue := ⟨210713, pr210713⟩
private theorem pr210719 : Nat.Prime 210719 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv105359]) (by decide +kernel)
def pv210719 : PrimeValue := ⟨210719, pr210719⟩
private theorem pr210731 : Nat.Prime 210731 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv1621]) (by decide +kernel)
def pv210731 : PrimeValue := ⟨210731, pr210731⟩
private theorem pr210739 : Nat.Prime 210739 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv11,pv31,pv103]) (by decide +kernel)
def pv210739 : PrimeValue := ⟨210739, pr210739⟩
private theorem pr210761 : Nat.Prime 210761 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv479]) (by decide +kernel)
def pv210761 : PrimeValue := ⟨210761, pr210761⟩
private theorem pr210803 : Nat.Prime 210803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv105401]) (by decide +kernel)
def pv210803 : PrimeValue := ⟨210803, pr210803⟩
private theorem pr210809 : Nat.Prime 210809 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv2027]) (by decide +kernel)
def pv210809 : PrimeValue := ⟨210809, pr210809⟩
private theorem pr210811 : Nat.Prime 210811 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv7027]) (by decide +kernel)
def pv210811 : PrimeValue := ⟨210811, pr210811⟩
private theorem pr210823 : Nat.Prime 210823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv41,pv857]) (by decide +kernel)
def pv210823 : PrimeValue := ⟨210823, pr210823⟩
private theorem pr210827 : Nat.Prime 210827 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv11,pv37]) (by decide +kernel)
def pv210827 : PrimeValue := ⟨210827, pr210827⟩
private theorem pr210839 : Nat.Prime 210839 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv271,pv389]) (by decide +kernel)
def pv210839 : PrimeValue := ⟨210839, pr210839⟩
private theorem pr210853 : Nat.Prime 210853 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv5857]) (by decide +kernel)
def pv210853 : PrimeValue := ⟨210853, pr210853⟩
private theorem pr210857 : Nat.Prime 210857 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv26357]) (by decide +kernel)
def pv210857 : PrimeValue := ⟨210857, pr210857⟩
private theorem pr210869 : Nat.Prime 210869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv17,pv443]) (by decide +kernel)
def pv210869 : PrimeValue := ⟨210869, pr210869⟩
private theorem pr210901 : Nat.Prime 210901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv37]) (by decide +kernel)
def pv210901 : PrimeValue := ⟨210901, pr210901⟩
private theorem pr210907 : Nat.Prime 210907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11717]) (by decide +kernel)
def pv210907 : PrimeValue := ⟨210907, pr210907⟩
private theorem pr210911 : Nat.Prime 210911 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv23,pv131]) (by decide +kernel)
def pv210911 : PrimeValue := ⟨210911, pr210911⟩
private theorem pr210913 : Nat.Prime 210913 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv210913 : PrimeValue := ⟨210913, pr210913⟩
private theorem pr210923 : Nat.Prime 210923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv163,pv647]) (by decide +kernel)
def pv210923 : PrimeValue := ⟨210923, pr210923⟩
private theorem pr210961 : Nat.Prime 210961 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv293]) (by decide +kernel)
def pv210961 : PrimeValue := ⟨210961, pr210961⟩
private theorem pr210967 : Nat.Prime 210967 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv5023]) (by decide +kernel)
def pv210967 : PrimeValue := ⟨210967, pr210967⟩
private theorem pr211007 : Nat.Prime 211007 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv105503]) (by decide +kernel)
def pv211007 : PrimeValue := ⟨211007, pr211007⟩
private theorem pr211039 : Nat.Prime 211039 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv2069]) (by decide +kernel)
def pv211039 : PrimeValue := ⟨211039, pr211039⟩
private theorem pr211049 : Nat.Prime 211049 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv31,pv37]) (by decide +kernel)
def pv211049 : PrimeValue := ⟨211049, pr211049⟩
private theorem pr211051 : Nat.Prime 211051 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv67]) (by decide +kernel)
def pv211051 : PrimeValue := ⟨211051, pr211051⟩
private theorem pr211063 : Nat.Prime 211063 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29,pv1213]) (by decide +kernel)
def pv211063 : PrimeValue := ⟨211063, pr211063⟩
private theorem pr211093 : Nat.Prime 211093 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv7,pv359]) (by decide +kernel)
def pv211093 : PrimeValue := ⟨211093, pr211093⟩
private theorem pr211097 : Nat.Prime 211097 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv26387]) (by decide +kernel)
def pv211097 : PrimeValue := ⟨211097, pr211097⟩
private theorem pr211129 : Nat.Prime 211129 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv19,pv463]) (by decide +kernel)
def pv211129 : PrimeValue := ⟨211129, pr211129⟩
private theorem pr211151 : Nat.Prime 211151 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv41,pv103]) (by decide +kernel)
def pv211151 : PrimeValue := ⟨211151, pr211151⟩
private theorem pr211153 : Nat.Prime 211153 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv53,pv83]) (by decide +kernel)
def pv211153 : PrimeValue := ⟨211153, pr211153⟩
private theorem pr211177 : Nat.Prime 211177 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv419]) (by decide +kernel)
def pv211177 : PrimeValue := ⟨211177, pr211177⟩
private theorem pr211187 : Nat.Prime 211187 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv4591]) (by decide +kernel)
def pv211187 : PrimeValue := ⟨211187, pr211187⟩
private theorem pr211193 : Nat.Prime 211193 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv26399]) (by decide +kernel)
def pv211193 : PrimeValue := ⟨211193, pr211193⟩
private theorem pr211217 : Nat.Prime 211217 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv43,pv307]) (by decide +kernel)
def pv211217 : PrimeValue := ⟨211217, pr211217⟩
private theorem pr211219 : Nat.Prime 211219 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv47,pv107]) (by decide +kernel)
def pv211219 : PrimeValue := ⟨211219, pr211219⟩
private theorem pr211229 : Nat.Prime 211229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv52807]) (by decide +kernel)
def pv211229 : PrimeValue := ⟨211229, pr211229⟩
private theorem pr211231 : Nat.Prime 211231 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv2347]) (by decide +kernel)
def pv211231 : PrimeValue := ⟨211231, pr211231⟩
private theorem pr211241 : Nat.Prime 211241 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv5281]) (by decide +kernel)
def pv211241 : PrimeValue := ⟨211241, pr211241⟩
private theorem pr211247 : Nat.Prime 211247 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv79,pv191]) (by decide +kernel)
def pv211247 : PrimeValue := ⟨211247, pr211247⟩
private theorem pr211283 : Nat.Prime 211283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv149,pv709]) (by decide +kernel)
def pv211283 : PrimeValue := ⟨211283, pr211283⟩
private theorem pr211313 : Nat.Prime 211313 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv47,pv281]) (by decide +kernel)
def pv211313 : PrimeValue := ⟨211313, pr211313⟩
private theorem pr211319 : Nat.Prime 211319 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv19,pv67,pv83]) (by decide +kernel)
def pv211319 : PrimeValue := ⟨211319, pr211319⟩
private theorem pr211333 : Nat.Prime 211333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv1601]) (by decide +kernel)
def pv211333 : PrimeValue := ⟨211333, pr211333⟩
private theorem pr211339 : Nat.Prime 211339 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv59,pv199]) (by decide +kernel)
def pv211339 : PrimeValue := ⟨211339, pr211339⟩
private theorem pr211349 : Nat.Prime 211349 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv52837]) (by decide +kernel)
def pv211349 : PrimeValue := ⟨211349, pr211349⟩
private theorem pr211373 : Nat.Prime 211373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv7549]) (by decide +kernel)
def pv211373 : PrimeValue := ⟨211373, pr211373⟩
private theorem pr211403 : Nat.Prime 211403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv105701]) (by decide +kernel)
def pv211403 : PrimeValue := ⟨211403, pr211403⟩
private theorem pr211427 : Nat.Prime 211427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv1733]) (by decide +kernel)
def pv211427 : PrimeValue := ⟨211427, pr211427⟩
private theorem pr211433 : Nat.Prime 211433 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv19,pv107]) (by decide +kernel)
def pv211433 : PrimeValue := ⟨211433, pr211433⟩
private theorem pr211493 : Nat.Prime 211493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv1429]) (by decide +kernel)
def pv211493 : PrimeValue := ⟨211493, pr211493⟩
private theorem pr211501 : Nat.Prime 211501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv47]) (by decide +kernel)
def pv211501 : PrimeValue := ⟨211501, pr211501⟩
private theorem pr211507 : Nat.Prime 211507 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv35251]) (by decide +kernel)
def pv211507 : PrimeValue := ⟨211507, pr211507⟩
private theorem pr211543 : Nat.Prime 211543 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv35257]) (by decide +kernel)
def pv211543 : PrimeValue := ⟨211543, pr211543⟩
private theorem pr211559 : Nat.Prime 211559 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv139,pv761]) (by decide +kernel)
def pv211559 : PrimeValue := ⟨211559, pr211559⟩
private theorem pr211571 : Nat.Prime 211571 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv21157]) (by decide +kernel)
def pv211571 : PrimeValue := ⟨211571, pr211571⟩
private theorem pr211583 : Nat.Prime 211583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv17,pv127]) (by decide +kernel)
def pv211583 : PrimeValue := ⟨211583, pr211583⟩
private theorem pr211597 : Nat.Prime 211597 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv229]) (by decide +kernel)
def pv211597 : PrimeValue := ⟨211597, pr211597⟩
private theorem pr211619 : Nat.Prime 211619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv9619]) (by decide +kernel)
def pv211619 : PrimeValue := ⟨211619, pr211619⟩
private theorem pr211643 : Nat.Prime 211643 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv41,pv89]) (by decide +kernel)
def pv211643 : PrimeValue := ⟨211643, pr211643⟩
private theorem pr211657 : Nat.Prime 211657 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv8819]) (by decide +kernel)
def pv211657 : PrimeValue := ⟨211657, pr211657⟩
private theorem pr211661 : Nat.Prime 211661 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19,pv557]) (by decide +kernel)
def pv211661 : PrimeValue := ⟨211661, pr211661⟩
private theorem pr211663 : Nat.Prime 211663 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv1069]) (by decide +kernel)
def pv211663 : PrimeValue := ⟨211663, pr211663⟩
private theorem pr211681 : Nat.Prime 211681 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv211681 : PrimeValue := ⟨211681, pr211681⟩
private theorem pr211691 : Nat.Prime 211691 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv21169]) (by decide +kernel)
def pv211691 : PrimeValue := ⟨211691, pr211691⟩
private theorem pr211693 : Nat.Prime 211693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv23,pv59]) (by decide +kernel)
def pv211693 : PrimeValue := ⟨211693, pr211693⟩
private theorem pr211711 : Nat.Prime 211711 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7057]) (by decide +kernel)
def pv211711 : PrimeValue := ⟨211711, pr211711⟩
private theorem pr211723 : Nat.Prime 211723 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv71]) (by decide +kernel)
def pv211723 : PrimeValue := ⟨211723, pr211723⟩
private theorem pr211727 : Nat.Prime 211727 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv105863]) (by decide +kernel)
def pv211727 : PrimeValue := ⟨211727, pr211727⟩
private theorem pr211741 : Nat.Prime 211741 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv3529]) (by decide +kernel)
def pv211741 : PrimeValue := ⟨211741, pr211741⟩
private theorem pr211747 : Nat.Prime 211747 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv35291]) (by decide +kernel)
def pv211747 : PrimeValue := ⟨211747, pr211747⟩
private theorem pr211777 : Nat.Prime 211777 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv1103]) (by decide +kernel)
def pv211777 : PrimeValue := ⟨211777, pr211777⟩
private theorem pr211789 : Nat.Prime 211789 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv37,pv53]) (by decide +kernel)
def pv211789 : PrimeValue := ⟨211789, pr211789⟩
private theorem pr211801 : Nat.Prime 211801 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv353]) (by decide +kernel)
def pv211801 : PrimeValue := ⟨211801, pr211801⟩
private theorem pr211811 : Nat.Prime 211811 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv59,pv359]) (by decide +kernel)
def pv211811 : PrimeValue := ⟨211811, pr211811⟩
private theorem pr211867 : Nat.Prime 211867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv35311]) (by decide +kernel)
def pv211867 : PrimeValue := ⟨211867, pr211867⟩
private theorem pr211873 : Nat.Prime 211873 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv2207]) (by decide +kernel)
def pv211873 : PrimeValue := ⟨211873, pr211873⟩
private theorem pr211879 : Nat.Prime 211879 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv79,pv149]) (by decide +kernel)
def pv211879 : PrimeValue := ⟨211879, pr211879⟩
private theorem pr211889 : Nat.Prime 211889 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv19,pv41]) (by decide +kernel)
def pv211889 : PrimeValue := ⟨211889, pr211889⟩
private theorem pr211943 : Nat.Prime 211943 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv105971]) (by decide +kernel)
def pv211943 : PrimeValue := ⟨211943, pr211943⟩
private theorem pr211949 : Nat.Prime 211949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv4817]) (by decide +kernel)
def pv211949 : PrimeValue := ⟨211949, pr211949⟩
private theorem pr212029 : Nat.Prime 212029 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv17669]) (by decide +kernel)
def pv212029 : PrimeValue := ⟨212029, pr212029⟩
private theorem pr212039 : Nat.Prime 212039 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv106019]) (by decide +kernel)
def pv212039 : PrimeValue := ⟨212039, pr212039⟩
private theorem pr212057 : Nat.Prime 212057 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv2039]) (by decide +kernel)
def pv212057 : PrimeValue := ⟨212057, pr212057⟩
private theorem pr212081 : Nat.Prime 212081 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv241]) (by decide +kernel)
def pv212081 : PrimeValue := ⟨212081, pr212081⟩
private theorem pr212099 : Nat.Prime 212099 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv173,pv613]) (by decide +kernel)
def pv212099 : PrimeValue := ⟨212099, pr212099⟩
private theorem pr212123 : Nat.Prime 212123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv67,pv1583]) (by decide +kernel)
def pv212123 : PrimeValue := ⟨212123, pr212123⟩
private theorem pr212131 : Nat.Prime 212131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv2357]) (by decide +kernel)
def pv212131 : PrimeValue := ⟨212131, pr212131⟩
private theorem pr212141 : Nat.Prime 212141 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv10607]) (by decide +kernel)
def pv212141 : PrimeValue := ⟨212141, pr212141⟩
private theorem pr212183 : Nat.Prime 212183 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv277,pv383]) (by decide +kernel)
def pv212183 : PrimeValue := ⟨212183, pr212183⟩
private theorem pr212203 : Nat.Prime 212203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11789]) (by decide +kernel)
def pv212203 : PrimeValue := ⟨212203, pr212203⟩
private theorem pr212227 : Nat.Prime 212227 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv31,pv163]) (by decide +kernel)
def pv212227 : PrimeValue := ⟨212227, pr212227⟩
private theorem pr212281 : Nat.Prime 212281 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv29,pv61]) (by decide +kernel)
def pv212281 : PrimeValue := ⟨212281, pr212281⟩
private theorem pr212297 : Nat.Prime 212297 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv17,pv223]) (by decide +kernel)
def pv212297 : PrimeValue := ⟨212297, pr212297⟩
private theorem pr212353 : Nat.Prime 212353 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv79]) (by decide +kernel)
def pv212353 : PrimeValue := ⟨212353, pr212353⟩
private theorem pr212369 : Nat.Prime 212369 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv1021]) (by decide +kernel)
def pv212369 : PrimeValue := ⟨212369, pr212369⟩
private theorem pr212383 : Nat.Prime 212383 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv19,pv23]) (by decide +kernel)
def pv212383 : PrimeValue := ⟨212383, pr212383⟩
private theorem pr212411 : Nat.Prime 212411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv1931]) (by decide +kernel)
def pv212411 : PrimeValue := ⟨212411, pr212411⟩
private theorem pr212419 : Nat.Prime 212419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11801]) (by decide +kernel)
def pv212419 : PrimeValue := ⟨212419, pr212419⟩
private theorem pr212423 : Nat.Prime 212423 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv15173]) (by decide +kernel)
def pv212423 : PrimeValue := ⟨212423, pr212423⟩
private theorem pr212453 : Nat.Prime 212453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53113]) (by decide +kernel)
def pv212453 : PrimeValue := ⟨212453, pr212453⟩
private theorem pr212467 : Nat.Prime 212467 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv2083]) (by decide +kernel)
def pv212467 : PrimeValue := ⟨212467, pr212467⟩
private theorem pr212479 : Nat.Prime 212479 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv5059]) (by decide +kernel)
def pv212479 : PrimeValue := ⟨212479, pr212479⟩
private theorem pr212501 : Nat.Prime 212501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17]) (by decide +kernel)
def pv212501 : PrimeValue := ⟨212501, pr212501⟩
private theorem pr212507 : Nat.Prime 212507 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv43,pv353]) (by decide +kernel)
def pv212507 : PrimeValue := ⟨212507, pr212507⟩
private theorem pr212557 : Nat.Prime 212557 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17713]) (by decide +kernel)
def pv212557 : PrimeValue := ⟨212557, pr212557⟩
private theorem pr212561 : Nat.Prime 212561 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv2657]) (by decide +kernel)
def pv212561 : PrimeValue := ⟨212561, pr212561⟩
private theorem pr212573 : Nat.Prime 212573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv2797]) (by decide +kernel)
def pv212573 : PrimeValue := ⟨212573, pr212573⟩
private theorem pr212579 : Nat.Prime 212579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv157,pv677]) (by decide +kernel)
def pv212579 : PrimeValue := ⟨212579, pr212579⟩
private theorem pr212587 : Nat.Prime 212587 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv3221]) (by decide +kernel)
def pv212587 : PrimeValue := ⟨212587, pr212587⟩
private theorem pr212593 : Nat.Prime 212593 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv43,pv103]) (by decide +kernel)
def pv212593 : PrimeValue := ⟨212593, pr212593⟩
private theorem pr212627 : Nat.Prime 212627 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv2593]) (by decide +kernel)
def pv212627 : PrimeValue := ⟨212627, pr212627⟩
private theorem pr212669 : Nat.Prime 212669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79,pv673]) (by decide +kernel)
def pv212669 : PrimeValue := ⟨212669, pr212669⟩
private theorem pr212671 : Nat.Prime 212671 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv17,pv139]) (by decide +kernel)
def pv212671 : PrimeValue := ⟨212671, pr212671⟩
private theorem pr212677 : Nat.Prime 212677 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv479]) (by decide +kernel)
def pv212677 : PrimeValue := ⟨212677, pr212677⟩
private theorem pr212683 : Nat.Prime 212683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv35447]) (by decide +kernel)
def pv212683 : PrimeValue := ⟨212683, pr212683⟩
private theorem pr212701 : Nat.Prime 212701 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv709]) (by decide +kernel)
def pv212701 : PrimeValue := ⟨212701, pr212701⟩
private theorem pr212791 : Nat.Prime 212791 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv41,pv173]) (by decide +kernel)
def pv212791 : PrimeValue := ⟨212791, pr212791⟩
private theorem pr212801 : Nat.Prime 212801 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv19]) (by decide +kernel)
def pv212801 : PrimeValue := ⟨212801, pr212801⟩
private theorem pr212837 : Nat.Prime 212837 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv4093]) (by decide +kernel)
def pv212837 : PrimeValue := ⟨212837, pr212837⟩
private theorem pr212867 : Nat.Prime 212867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv106433]) (by decide +kernel)
def pv212867 : PrimeValue := ⟨212867, pr212867⟩
private theorem pr212869 : Nat.Prime 212869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv73]) (by decide +kernel)
def pv212869 : PrimeValue := ⟨212869, pr212869⟩
private theorem pr212873 : Nat.Prime 212873 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv41,pv59]) (by decide +kernel)
def pv212873 : PrimeValue := ⟨212873, pr212873⟩
private theorem pr212909 : Nat.Prime 212909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv31,pv101]) (by decide +kernel)
def pv212909 : PrimeValue := ⟨212909, pr212909⟩
private theorem pr212969 : Nat.Prime 212969 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv3803]) (by decide +kernel)
def pv212969 : PrimeValue := ⟨212969, pr212969⟩
private theorem pr212987 : Nat.Prime 212987 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv109,pv977]) (by decide +kernel)
def pv212987 : PrimeValue := ⟨212987, pr212987⟩
private theorem pr212999 : Nat.Prime 212999 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv281,pv379]) (by decide +kernel)
def pv212999 : PrimeValue := ⟨212999, pr212999⟩
private theorem pr213023 : Nat.Prime 213023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv43,pv2477]) (by decide +kernel)
def pv213023 : PrimeValue := ⟨213023, pr213023⟩
private theorem pr213067 : Nat.Prime 213067 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv19,pv89]) (by decide +kernel)
def pv213067 : PrimeValue := ⟨213067, pr213067⟩
private theorem pr213091 : Nat.Prime 213091 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7103]) (by decide +kernel)
def pv213091 : PrimeValue := ⟨213091, pr213091⟩
private theorem pr213097 : Nat.Prime 213097 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv13,pv683]) (by decide +kernel)
def pv213097 : PrimeValue := ⟨213097, pr213097⟩
private theorem pr213119 : Nat.Prime 213119 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv23,pv41,pv113]) (by decide +kernel)
def pv213119 : PrimeValue := ⟨213119, pr213119⟩
private theorem pr213131 : Nat.Prime 213131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv21313]) (by decide +kernel)
def pv213131 : PrimeValue := ⟨213131, pr213131⟩
private theorem pr213133 : Nat.Prime 213133 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17761]) (by decide +kernel)
def pv213133 : PrimeValue := ⟨213133, pr213133⟩
private theorem pr213139 : Nat.Prime 213139 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv3947]) (by decide +kernel)
def pv213139 : PrimeValue := ⟨213139, pr213139⟩
private theorem pr213173 : Nat.Prime 213173 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv137,pv389]) (by decide +kernel)
def pv213173 : PrimeValue := ⟨213173, pr213173⟩
private theorem pr213181 : Nat.Prime 213181 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv11,pv17,pv19]) (by decide +kernel)
def pv213181 : PrimeValue := ⟨213181, pr213181⟩
private theorem pr213193 : Nat.Prime 213193 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv47]) (by decide +kernel)
def pv213193 : PrimeValue := ⟨213193, pr213193⟩
private theorem pr213203 : Nat.Prime 213203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv881]) (by decide +kernel)
def pv213203 : PrimeValue := ⟨213203, pr213203⟩
private theorem pr213209 : Nat.Prime 213209 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv919]) (by decide +kernel)
def pv213209 : PrimeValue := ⟨213209, pr213209⟩
private theorem pr213217 : Nat.Prime 213217 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2221]) (by decide +kernel)
def pv213217 : PrimeValue := ⟨213217, pr213217⟩
private theorem pr213223 : Nat.Prime 213223 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv35537]) (by decide +kernel)
def pv213223 : PrimeValue := ⟨213223, pr213223⟩
private theorem pr213247 : Nat.Prime 213247 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv11,pv359]) (by decide +kernel)
def pv213247 : PrimeValue := ⟨213247, pr213247⟩
private theorem pr213253 : Nat.Prime 213253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv1367]) (by decide +kernel)
def pv213253 : PrimeValue := ⟨213253, pr213253⟩
private theorem pr213263 : Nat.Prime 213263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv15233]) (by decide +kernel)
def pv213263 : PrimeValue := ⟨213263, pr213263⟩
private theorem pr213281 : Nat.Prime 213281 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv31,pv43]) (by decide +kernel)
def pv213281 : PrimeValue := ⟨213281, pr213281⟩
private theorem pr213289 : Nat.Prime 213289 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv8887]) (by decide +kernel)
def pv213289 : PrimeValue := ⟨213289, pr213289⟩
private theorem pr213307 : Nat.Prime 213307 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv73,pv487]) (by decide +kernel)
def pv213307 : PrimeValue := ⟨213307, pr213307⟩
private theorem pr213319 : Nat.Prime 213319 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv1693]) (by decide +kernel)
def pv213319 : PrimeValue := ⟨213319, pr213319⟩
private theorem pr213329 : Nat.Prime 213329 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv67,pv199]) (by decide +kernel)
def pv213329 : PrimeValue := ⟨213329, pr213329⟩
private theorem pr213337 : Nat.Prime 213337 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv2963]) (by decide +kernel)
def pv213337 : PrimeValue := ⟨213337, pr213337⟩
private theorem pr213361 : Nat.Prime 213361 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv7,pv127]) (by decide +kernel)
def pv213361 : PrimeValue := ⟨213361, pr213361⟩
private theorem pr213407 : Nat.Prime 213407 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv106703]) (by decide +kernel)
def pv213407 : PrimeValue := ⟨213407, pr213407⟩
private theorem pr213449 : Nat.Prime 213449 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv26681]) (by decide +kernel)
def pv213449 : PrimeValue := ⟨213449, pr213449⟩
private theorem pr213461 : Nat.Prime 213461 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv821]) (by decide +kernel)
def pv213461 : PrimeValue := ⟨213461, pr213461⟩
private theorem pr213467 : Nat.Prime 213467 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv31,pv313]) (by decide +kernel)
def pv213467 : PrimeValue := ⟨213467, pr213467⟩
private theorem pr213481 : Nat.Prime 213481 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv593]) (by decide +kernel)
def pv213481 : PrimeValue := ⟨213481, pr213481⟩
private theorem pr213491 : Nat.Prime 213491 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv37,pv577]) (by decide +kernel)
def pv213491 : PrimeValue := ⟨213491, pr213491⟩
private theorem pr213523 : Nat.Prime 213523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv1873]) (by decide +kernel)
def pv213523 : PrimeValue := ⟨213523, pr213523⟩
private theorem pr213533 : Nat.Prime 213533 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv23,pv211]) (by decide +kernel)
def pv213533 : PrimeValue := ⟨213533, pr213533⟩
private theorem pr213539 : Nat.Prime 213539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv43,pv191]) (by decide +kernel)
def pv213539 : PrimeValue := ⟨213539, pr213539⟩
private theorem pr213553 : Nat.Prime 213553 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1483]) (by decide +kernel)
def pv213553 : PrimeValue := ⟨213553, pr213553⟩
private theorem pr213557 : Nat.Prime 213557 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv29,pv263]) (by decide +kernel)
def pv213557 : PrimeValue := ⟨213557, pr213557⟩
private theorem pr213589 : Nat.Prime 213589 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv17,pv349]) (by decide +kernel)
def pv213589 : PrimeValue := ⟨213589, pr213589⟩
private theorem pr213611 : Nat.Prime 213611 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv41,pv521]) (by decide +kernel)
def pv213611 : PrimeValue := ⟨213611, pr213611⟩
private theorem pr213613 : Nat.Prime 213613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv2543]) (by decide +kernel)
def pv213613 : PrimeValue := ⟨213613, pr213613⟩
private theorem pr213623 : Nat.Prime 213623 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv61,pv103]) (by decide +kernel)
def pv213623 : PrimeValue := ⟨213623, pr213623⟩
private theorem pr213637 : Nat.Prime 213637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv937]) (by decide +kernel)
def pv213637 : PrimeValue := ⟨213637, pr213637⟩
private theorem pr213641 : Nat.Prime 213641 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv109]) (by decide +kernel)
def pv213641 : PrimeValue := ⟨213641, pr213641⟩
private theorem pr213659 : Nat.Prime 213659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv317,pv337]) (by decide +kernel)
def pv213659 : PrimeValue := ⟨213659, pr213659⟩
private theorem pr213713 : Nat.Prime 213713 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv37]) (by decide +kernel)
def pv213713 : PrimeValue := ⟨213713, pr213713⟩
private theorem pr213721 : Nat.Prime 213721 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv13,pv137]) (by decide +kernel)
def pv213721 : PrimeValue := ⟨213721, pr213721⟩
private theorem pr213727 : Nat.Prime 213727 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv179,pv199]) (by decide +kernel)
def pv213727 : PrimeValue := ⟨213727, pr213727⟩
private theorem pr213737 : Nat.Prime 213737 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv26717]) (by decide +kernel)
def pv213737 : PrimeValue := ⟨213737, pr213737⟩
private theorem pr213751 : Nat.Prime 213751 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv213751 : PrimeValue := ⟨213751, pr213751⟩
private theorem pr213827 : Nat.Prime 213827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv19,pv331]) (by decide +kernel)
def pv213827 : PrimeValue := ⟨213827, pr213827⟩
private theorem pr213833 : Nat.Prime 213833 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv26729]) (by decide +kernel)
def pv213833 : PrimeValue := ⟨213833, pr213833⟩
private theorem pr213847 : Nat.Prime 213847 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv29,pv1229]) (by decide +kernel)
def pv213847 : PrimeValue := ⟨213847, pr213847⟩
private theorem pr213881 : Nat.Prime 213881 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv5347]) (by decide +kernel)
def pv213881 : PrimeValue := ⟨213881, pr213881⟩
private theorem pr213887 : Nat.Prime 213887 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv229,pv467]) (by decide +kernel)
def pv213887 : PrimeValue := ⟨213887, pr213887⟩
private theorem pr213919 : Nat.Prime 213919 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv101,pv353]) (by decide +kernel)
def pv213919 : PrimeValue := ⟨213919, pr213919⟩
private theorem pr213929 : Nat.Prime 213929 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv11,pv13,pv17]) (by decide +kernel)
def pv213929 : PrimeValue := ⟨213929, pr213929⟩
private theorem pr213947 : Nat.Prime 213947 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv4651]) (by decide +kernel)
def pv213947 : PrimeValue := ⟨213947, pr213947⟩
private theorem pr213953 : Nat.Prime 213953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3343]) (by decide +kernel)
def pv213953 : PrimeValue := ⟨213953, pr213953⟩
private theorem pr213973 : Nat.Prime 213973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv1621]) (by decide +kernel)
def pv213973 : PrimeValue := ⟨213973, pr213973⟩
private theorem pr213977 : Nat.Prime 213977 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv3821]) (by decide +kernel)
def pv213977 : PrimeValue := ⟨213977, pr213977⟩
private theorem pr214003 : Nat.Prime 214003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1321]) (by decide +kernel)
def pv214003 : PrimeValue := ⟨214003, pr214003⟩
private theorem pr214007 : Nat.Prime 214007 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv8231]) (by decide +kernel)
def pv214007 : PrimeValue := ⟨214007, pr214007⟩
private theorem pr214009 : Nat.Prime 214009 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv37,pv241]) (by decide +kernel)
def pv214009 : PrimeValue := ⟨214009, pr214009⟩
private theorem pr214021 : Nat.Prime 214021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv29,pv41]) (by decide +kernel)
def pv214021 : PrimeValue := ⟨214021, pr214021⟩
private theorem pr214031 : Nat.Prime 214031 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv17,pv1259]) (by decide +kernel)
def pv214031 : PrimeValue := ⟨214031, pr214031⟩
private theorem pr214033 : Nat.Prime 214033 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv13]) (by decide +kernel)
def pv214033 : PrimeValue := ⟨214033, pr214033⟩
private theorem pr214043 : Nat.Prime 214043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv107021]) (by decide +kernel)
def pv214043 : PrimeValue := ⟨214043, pr214043⟩
private theorem pr214063 : Nat.Prime 214063 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv35677]) (by decide +kernel)
def pv214063 : PrimeValue := ⟨214063, pr214063⟩
private theorem pr214069 : Nat.Prime 214069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17839]) (by decide +kernel)
def pv214069 : PrimeValue := ⟨214069, pr214069⟩
private theorem pr214087 : Nat.Prime 214087 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv31,pv1151]) (by decide +kernel)
def pv214087 : PrimeValue := ⟨214087, pr214087⟩
private theorem pr214091 : Nat.Prime 214091 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv79,pv271]) (by decide +kernel)
def pv214091 : PrimeValue := ⟨214091, pr214091⟩
private theorem pr214129 : Nat.Prime 214129 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv1487]) (by decide +kernel)
def pv214129 : PrimeValue := ⟨214129, pr214129⟩
private theorem pr214141 : Nat.Prime 214141 :=
  checkPrime_prime (q := pv59) (ls := [pv2,pv3,pv5,pv43,pv83]) (by decide +kernel)
def pv214141 : PrimeValue := ⟨214141, pr214141⟩
private theorem pr214189 : Nat.Prime 214189 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv13,pv1373]) (by decide +kernel)
def pv214189 : PrimeValue := ⟨214189, pr214189⟩
private theorem pr214211 : Nat.Prime 214211 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv31,pv691]) (by decide +kernel)
def pv214211 : PrimeValue := ⟨214211, pr214211⟩
private theorem pr214213 : Nat.Prime 214213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17851]) (by decide +kernel)
def pv214213 : PrimeValue := ⟨214213, pr214213⟩
private theorem pr214237 : Nat.Prime 214237 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv541]) (by decide +kernel)
def pv214237 : PrimeValue := ⟨214237, pr214237⟩
private theorem pr214243 : Nat.Prime 214243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv5101]) (by decide +kernel)
def pv214243 : PrimeValue := ⟨214243, pr214243⟩
private theorem pr214283 : Nat.Prime 214283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv5639]) (by decide +kernel)
def pv214283 : PrimeValue := ⟨214283, pr214283⟩
private theorem pr214297 : Nat.Prime 214297 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv8929]) (by decide +kernel)
def pv214297 : PrimeValue := ⟨214297, pr214297⟩
private theorem pr214351 : Nat.Prime 214351 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv1429]) (by decide +kernel)
def pv214351 : PrimeValue := ⟨214351, pr214351⟩
private theorem pr214363 : Nat.Prime 214363 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11909]) (by decide +kernel)
def pv214363 : PrimeValue := ⟨214363, pr214363⟩
private theorem pr214373 : Nat.Prime 214373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53593]) (by decide +kernel)
def pv214373 : PrimeValue := ⟨214373, pr214373⟩
private theorem pr214381 : Nat.Prime 214381 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv397]) (by decide +kernel)
def pv214381 : PrimeValue := ⟨214381, pr214381⟩
private theorem pr214391 : Nat.Prime 214391 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv1949]) (by decide +kernel)
def pv214391 : PrimeValue := ⟨214391, pr214391⟩
private theorem pr214399 : Nat.Prime 214399 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv43,pv277]) (by decide +kernel)
def pv214399 : PrimeValue := ⟨214399, pr214399⟩
private theorem pr214439 : Nat.Prime 214439 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv17,pv53]) (by decide +kernel)
def pv214439 : PrimeValue := ⟨214439, pr214439⟩
private theorem pr214451 : Nat.Prime 214451 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv4289]) (by decide +kernel)
def pv214451 : PrimeValue := ⟨214451, pr214451⟩
private theorem pr214481 : Nat.Prime 214481 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv383]) (by decide +kernel)
def pv214481 : PrimeValue := ⟨214481, pr214481⟩
private theorem pr214507 : Nat.Prime 214507 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv701]) (by decide +kernel)
def pv214507 : PrimeValue := ⟨214507, pr214507⟩
private theorem pr214519 : Nat.Prime 214519 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv35753]) (by decide +kernel)
def pv214519 : PrimeValue := ⟨214519, pr214519⟩
private theorem pr214541 : Nat.Prime 214541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv631]) (by decide +kernel)
def pv214541 : PrimeValue := ⟨214541, pr214541⟩
private theorem pr214559 : Nat.Prime 214559 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv107279]) (by decide +kernel)
def pv214559 : PrimeValue := ⟨214559, pr214559⟩
private theorem pr214603 : Nat.Prime 214603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv47,pv761]) (by decide +kernel)
def pv214603 : PrimeValue := ⟨214603, pr214603⟩
private theorem pr214607 : Nat.Prime 214607 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv15329]) (by decide +kernel)
def pv214607 : PrimeValue := ⟨214607, pr214607⟩
private theorem pr214631 : Nat.Prime 214631 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv127]) (by decide +kernel)
def pv214631 : PrimeValue := ⟨214631, pr214631⟩
private theorem pr214651 : Nat.Prime 214651 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv53]) (by decide +kernel)
def pv214651 : PrimeValue := ⟨214651, pr214651⟩
private theorem pr214663 : Nat.Prime 214663 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv19,pv269]) (by decide +kernel)
def pv214663 : PrimeValue := ⟨214663, pr214663⟩
private theorem pr214667 : Nat.Prime 214667 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv181,pv593]) (by decide +kernel)
def pv214667 : PrimeValue := ⟨214667, pr214667⟩
private theorem pr214673 : Nat.Prime 214673 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13417]) (by decide +kernel)
def pv214673 : PrimeValue := ⟨214673, pr214673⟩
private theorem pr214691 : Nat.Prime 214691 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv3067]) (by decide +kernel)
def pv214691 : PrimeValue := ⟨214691, pr214691⟩
private theorem pr214723 : Nat.Prime 214723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv79,pv151]) (by decide +kernel)
def pv214723 : PrimeValue := ⟨214723, pr214723⟩
private theorem pr214733 : Nat.Prime 214733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv7669]) (by decide +kernel)
def pv214733 : PrimeValue := ⟨214733, pr214733⟩
private theorem pr214759 : Nat.Prime 214759 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv41,pv97]) (by decide +kernel)
def pv214759 : PrimeValue := ⟨214759, pr214759⟩
private theorem pr214783 : Nat.Prime 214783 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv35797]) (by decide +kernel)
def pv214783 : PrimeValue := ⟨214783, pr214783⟩
private theorem pr214787 : Nat.Prime 214787 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv11,pv13,pv751]) (by decide +kernel)
def pv214787 : PrimeValue := ⟨214787, pr214787⟩
private theorem pr214807 : Nat.Prime 214807 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv35801]) (by decide +kernel)
def pv214807 : PrimeValue := ⟨214807, pr214807⟩
private theorem pr214811 : Nat.Prime 214811 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv21481]) (by decide +kernel)
def pv214811 : PrimeValue := ⟨214811, pr214811⟩
private theorem pr214831 : Nat.Prime 214831 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv7,pv11,pv31]) (by decide +kernel)
def pv214831 : PrimeValue := ⟨214831, pr214831⟩
private theorem pr214849 : Nat.Prime 214849 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv373]) (by decide +kernel)
def pv214849 : PrimeValue := ⟨214849, pr214849⟩
private theorem pr214867 : Nat.Prime 214867 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv173]) (by decide +kernel)
def pv214867 : PrimeValue := ⟨214867, pr214867⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
