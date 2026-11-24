/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table084
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table084.pv291007
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table007
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table012
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table019
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table020
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table051
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table052

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr291007 : Nat.Prime 291007 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv317]) (by decide +kernel)
def pv291007 : PrimeValue := ⟨291007, pr291007⟩
private theorem pr291041 : Nat.Prime 291041 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17,pv107]) (by decide +kernel)
def pv291041 : PrimeValue := ⟨291041, pr291041⟩
private theorem pr291043 : Nat.Prime 291043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv23,pv37]) (by decide +kernel)
def pv291043 : PrimeValue := ⟨291043, pr291043⟩
private theorem pr291077 : Nat.Prime 291077 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53,pv1373]) (by decide +kernel)
def pv291077 : PrimeValue := ⟨291077, pr291077⟩
private theorem pr291089 : Nat.Prime 291089 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv7,pv23,pv113]) (by decide +kernel)
def pv291089 : PrimeValue := ⟨291089, pr291089⟩
private theorem pr291101 : Nat.Prime 291101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv41,pv71]) (by decide +kernel)
def pv291101 : PrimeValue := ⟨291101, pr291101⟩
private theorem pr291103 : Nat.Prime 291103 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv29,pv239]) (by decide +kernel)
def pv291103 : PrimeValue := ⟨291103, pr291103⟩
private theorem pr291107 : Nat.Prime 291107 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv59,pv2467]) (by decide +kernel)
def pv291107 : PrimeValue := ⟨291107, pr291107⟩
private theorem pr291113 : Nat.Prime 291113 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv36389]) (by decide +kernel)
def pv291113 : PrimeValue := ⟨291113, pr291113⟩
private theorem pr291143 : Nat.Prime 291143 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv8563]) (by decide +kernel)
def pv291143 : PrimeValue := ⟨291143, pr291143⟩
private theorem pr291167 : Nat.Prime 291167 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv197,pv739]) (by decide +kernel)
def pv291167 : PrimeValue := ⟨291167, pr291167⟩
private theorem pr291209 : Nat.Prime 291209 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv89,pv409]) (by decide +kernel)
def pv291209 : PrimeValue := ⟨291209, pr291209⟩
private theorem pr291217 : Nat.Prime 291217 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv6067]) (by decide +kernel)
def pv291217 : PrimeValue := ⟨291217, pr291217⟩
private theorem pr291253 : Nat.Prime 291253 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv1867]) (by decide +kernel)
def pv291253 : PrimeValue := ⟨291253, pr291253⟩
private theorem pr291287 : Nat.Prime 291287 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv145643]) (by decide +kernel)
def pv291287 : PrimeValue := ⟨291287, pr291287⟩
private theorem pr291293 : Nat.Prime 291293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv72823]) (by decide +kernel)
def pv291293 : PrimeValue := ⟨291293, pr291293⟩
private theorem pr291331 : Nat.Prime 291331 :=
  checkPrime_prime (q := pv43) (ls := [pv2,pv3,pv5,pv13,pv83]) (by decide +kernel)
def pv291331 : PrimeValue := ⟨291331, pr291331⟩
private theorem pr291337 : Nat.Prime 291337 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv61,pv199]) (by decide +kernel)
def pv291337 : PrimeValue := ⟨291337, pr291337⟩
private theorem pr291349 : Nat.Prime 291349 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv8093]) (by decide +kernel)
def pv291349 : PrimeValue := ⟨291349, pr291349⟩
private theorem pr291359 : Nat.Prime 291359 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv145679]) (by decide +kernel)
def pv291359 : PrimeValue := ⟨291359, pr291359⟩
private theorem pr291373 : Nat.Prime 291373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv24281]) (by decide +kernel)
def pv291373 : PrimeValue := ⟨291373, pr291373⟩
private theorem pr291419 : Nat.Prime 291419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv145709]) (by decide +kernel)
def pv291419 : PrimeValue := ⟨291419, pr291419⟩
private theorem pr291437 : Nat.Prime 291437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv72859]) (by decide +kernel)
def pv291437 : PrimeValue := ⟨291437, pr291437⟩
private theorem pr291443 : Nat.Prime 291443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv145721]) (by decide +kernel)
def pv291443 : PrimeValue := ⟨291443, pr291443⟩
private theorem pr291457 : Nat.Prime 291457 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv23]) (by decide +kernel)
def pv291457 : PrimeValue := ⟨291457, pr291457⟩
private theorem pr291491 : Nat.Prime 291491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv103,pv283]) (by decide +kernel)
def pv291491 : PrimeValue := ⟨291491, pr291491⟩
private theorem pr291503 : Nat.Prime 291503 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv23,pv6337]) (by decide +kernel)
def pv291503 : PrimeValue := ⟨291503, pr291503⟩
private theorem pr291509 : Nat.Prime 291509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv29,pv359]) (by decide +kernel)
def pv291509 : PrimeValue := ⟨291509, pr291509⟩
private theorem pr291539 : Nat.Prime 291539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv11213]) (by decide +kernel)
def pv291539 : PrimeValue := ⟨291539, pr291539⟩
private theorem pr291559 : Nat.Prime 291559 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv48593]) (by decide +kernel)
def pv291559 : PrimeValue := ⟨291559, pr291559⟩
private theorem pr291563 : Nat.Prime 291563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv73,pv1997]) (by decide +kernel)
def pv291563 : PrimeValue := ⟨291563, pr291563⟩
private theorem pr291569 : Nat.Prime 291569 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv18223]) (by decide +kernel)
def pv291569 : PrimeValue := ⟨291569, pr291569⟩
private theorem pr291649 : Nat.Prime 291649 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv31]) (by decide +kernel)
def pv291649 : PrimeValue := ⟨291649, pr291649⟩
private theorem pr291661 : Nat.Prime 291661 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv4861]) (by decide +kernel)
def pv291661 : PrimeValue := ⟨291661, pr291661⟩
private theorem pr291701 : Nat.Prime 291701 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv2917]) (by decide +kernel)
def pv291701 : PrimeValue := ⟨291701, pr291701⟩
private theorem pr291743 : Nat.Prime 291743 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv89,pv149]) (by decide +kernel)
def pv291743 : PrimeValue := ⟨291743, pr291743⟩
private theorem pr291751 : Nat.Prime 291751 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv389]) (by decide +kernel)
def pv291751 : PrimeValue := ⟨291751, pr291751⟩
private theorem pr291791 : Nat.Prime 291791 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv29179]) (by decide +kernel)
def pv291791 : PrimeValue := ⟨291791, pr291791⟩
private theorem pr291829 : Nat.Prime 291829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv83,pv293]) (by decide +kernel)
def pv291829 : PrimeValue := ⟨291829, pr291829⟩
private theorem pr291833 : Nat.Prime 291833 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv36479]) (by decide +kernel)
def pv291833 : PrimeValue := ⟨291833, pr291833⟩
private theorem pr291857 : Nat.Prime 291857 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv29,pv37]) (by decide +kernel)
def pv291857 : PrimeValue := ⟨291857, pr291857⟩
private theorem pr291869 : Nat.Prime 291869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv131,pv557]) (by decide +kernel)
def pv291869 : PrimeValue := ⟨291869, pr291869⟩
private theorem pr291887 : Nat.Prime 291887 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv20849]) (by decide +kernel)
def pv291887 : PrimeValue := ⟨291887, pr291887⟩
private theorem pr291901 : Nat.Prime 291901 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv7,pv139]) (by decide +kernel)
def pv291901 : PrimeValue := ⟨291901, pr291901⟩
private theorem pr291971 : Nat.Prime 291971 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv43,pv97]) (by decide +kernel)
def pv291971 : PrimeValue := ⟨291971, pr291971⟩
private theorem pr292057 : Nat.Prime 292057 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv43,pv283]) (by decide +kernel)
def pv292057 : PrimeValue := ⟨292057, pr292057⟩
private theorem pr292069 : Nat.Prime 292069 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv19,pv61]) (by decide +kernel)
def pv292069 : PrimeValue := ⟨292069, pr292069⟩
private theorem pr292081 : Nat.Prime 292081 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv1217]) (by decide +kernel)
def pv292081 : PrimeValue := ⟨292081, pr292081⟩
private theorem pr292091 : Nat.Prime 292091 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv29209]) (by decide +kernel)
def pv292091 : PrimeValue := ⟨292091, pr292091⟩
private theorem pr292133 : Nat.Prime 292133 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv199,pv367]) (by decide +kernel)
def pv292133 : PrimeValue := ⟨292133, pr292133⟩
private theorem pr292157 : Nat.Prime 292157 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv73039]) (by decide +kernel)
def pv292157 : PrimeValue := ⟨292157, pr292157⟩
private theorem pr292223 : Nat.Prime 292223 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv20873]) (by decide +kernel)
def pv292223 : PrimeValue := ⟨292223, pr292223⟩
private theorem pr292249 : Nat.Prime 292249 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv11,pv41]) (by decide +kernel)
def pv292249 : PrimeValue := ⟨292249, pr292249⟩
private theorem pr292267 : Nat.Prime 292267 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv13,pv1249]) (by decide +kernel)
def pv292267 : PrimeValue := ⟨292267, pr292267⟩
private theorem pr292301 : Nat.Prime 292301 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv37,pv79]) (by decide +kernel)
def pv292301 : PrimeValue := ⟨292301, pr292301⟩
private theorem pr292309 : Nat.Prime 292309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv24359]) (by decide +kernel)
def pv292309 : PrimeValue := ⟨292309, pr292309⟩
private theorem pr292363 : Nat.Prime 292363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv6961]) (by decide +kernel)
def pv292363 : PrimeValue := ⟨292363, pr292363⟩
private theorem pr292381 : Nat.Prime 292381 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv443]) (by decide +kernel)
def pv292381 : PrimeValue := ⟨292381, pr292381⟩
private theorem pr292393 : Nat.Prime 292393 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv31,pv131]) (by decide +kernel)
def pv292393 : PrimeValue := ⟨292393, pr292393⟩
private theorem pr292427 : Nat.Prime 292427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv146213]) (by decide +kernel)
def pv292427 : PrimeValue := ⟨292427, pr292427⟩
private theorem pr292471 : Nat.Prime 292471 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv9749]) (by decide +kernel)
def pv292471 : PrimeValue := ⟨292471, pr292471⟩
private theorem pr292483 : Nat.Prime 292483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv16249]) (by decide +kernel)
def pv292483 : PrimeValue := ⟨292483, pr292483⟩
private theorem pr292573 : Nat.Prime 292573 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv43]) (by decide +kernel)
def pv292573 : PrimeValue := ⟨292573, pr292573⟩
private theorem pr292577 : Nat.Prime 292577 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv41,pv223]) (by decide +kernel)
def pv292577 : PrimeValue := ⟨292577, pr292577⟩
private theorem pr292627 : Nat.Prime 292627 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5419]) (by decide +kernel)
def pv292627 : PrimeValue := ⟨292627, pr292627⟩
private theorem pr292679 : Nat.Prime 292679 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv61,pv2399]) (by decide +kernel)
def pv292679 : PrimeValue := ⟨292679, pr292679⟩
private theorem pr292709 : Nat.Prime 292709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv433]) (by decide +kernel)
def pv292709 : PrimeValue := ⟨292709, pr292709⟩
private theorem pr292711 : Nat.Prime 292711 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv11,pv887]) (by decide +kernel)
def pv292711 : PrimeValue := ⟨292711, pr292711⟩
private theorem pr292727 : Nat.Prime 292727 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv29,pv103]) (by decide +kernel)
def pv292727 : PrimeValue := ⟨292727, pr292727⟩
private theorem pr292753 : Nat.Prime 292753 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv107]) (by decide +kernel)
def pv292753 : PrimeValue := ⟨292753, pr292753⟩
private theorem pr292759 : Nat.Prime 292759 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv59,pv827]) (by decide +kernel)
def pv292759 : PrimeValue := ⟨292759, pr292759⟩
private theorem pr292777 : Nat.Prime 292777 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv1109]) (by decide +kernel)
def pv292777 : PrimeValue := ⟨292777, pr292777⟩
private theorem pr292793 : Nat.Prime 292793 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv36599]) (by decide +kernel)
def pv292793 : PrimeValue := ⟨292793, pr292793⟩
private theorem pr292849 : Nat.Prime 292849 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv6101]) (by decide +kernel)
def pv292849 : PrimeValue := ⟨292849, pr292849⟩
private theorem pr292879 : Nat.Prime 292879 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv53,pv307]) (by decide +kernel)
def pv292879 : PrimeValue := ⟨292879, pr292879⟩
private theorem pr292909 : Nat.Prime 292909 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv7,pv11,pv317]) (by decide +kernel)
def pv292909 : PrimeValue := ⟨292909, pr292909⟩
private theorem pr292921 : Nat.Prime 292921 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv2441]) (by decide +kernel)
def pv292921 : PrimeValue := ⟨292921, pr292921⟩
private theorem pr292933 : Nat.Prime 292933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv79,pv103]) (by decide +kernel)
def pv292933 : PrimeValue := ⟨292933, pr292933⟩
private theorem pr292979 : Nat.Prime 292979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv17,pv1231]) (by decide +kernel)
def pv292979 : PrimeValue := ⟨292979, pr292979⟩
private theorem pr293081 : Nat.Prime 293081 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17,pv431]) (by decide +kernel)
def pv293081 : PrimeValue := ⟨293081, pr293081⟩
private theorem pr293087 : Nat.Prime 293087 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv146543]) (by decide +kernel)
def pv293087 : PrimeValue := ⟨293087, pr293087⟩
private theorem pr293107 : Nat.Prime 293107 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv11,pv4441]) (by decide +kernel)
def pv293107 : PrimeValue := ⟨293107, pr293107⟩
private theorem pr293123 : Nat.Prime 293123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv113,pv1297]) (by decide +kernel)
def pv293123 : PrimeValue := ⟨293123, pr293123⟩
private theorem pr293129 : Nat.Prime 293129 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv3331]) (by decide +kernel)
def pv293129 : PrimeValue := ⟨293129, pr293129⟩
private theorem pr293201 : Nat.Prime 293201 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv733]) (by decide +kernel)
def pv293201 : PrimeValue := ⟨293201, pr293201⟩
private theorem pr293207 : Nat.Prime 293207 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv146603]) (by decide +kernel)
def pv293207 : PrimeValue := ⟨293207, pr293207⟩
private theorem pr293257 : Nat.Prime 293257 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv4073]) (by decide +kernel)
def pv293257 : PrimeValue := ⟨293257, pr293257⟩
private theorem pr293261 : Nat.Prime 293261 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv31,pv43]) (by decide +kernel)
def pv293261 : PrimeValue := ⟨293261, pr293261⟩
private theorem pr293263 : Nat.Prime 293263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv37,pv1321]) (by decide +kernel)
def pv293263 : PrimeValue := ⟨293263, pr293263⟩
private theorem pr293269 : Nat.Prime 293269 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv24439]) (by decide +kernel)
def pv293269 : PrimeValue := ⟨293269, pr293269⟩
private theorem pr293311 : Nat.Prime 293311 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv3259]) (by decide +kernel)
def pv293311 : PrimeValue := ⟨293311, pr293311⟩
private theorem pr293329 : Nat.Prime 293329 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv97]) (by decide +kernel)
def pv293329 : PrimeValue := ⟨293329, pr293329⟩
private theorem pr293339 : Nat.Prime 293339 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv146669]) (by decide +kernel)
def pv293339 : PrimeValue := ⟨293339, pr293339⟩
private theorem pr293357 : Nat.Prime 293357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv10477]) (by decide +kernel)
def pv293357 : PrimeValue := ⟨293357, pr293357⟩
private theorem pr293431 : Nat.Prime 293431 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv9781]) (by decide +kernel)
def pv293431 : PrimeValue := ⟨293431, pr293431⟩
private theorem pr293459 : Nat.Prime 293459 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv13339]) (by decide +kernel)
def pv293459 : PrimeValue := ⟨293459, pr293459⟩
private theorem pr293467 : Nat.Prime 293467 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv59,pv829]) (by decide +kernel)
def pv293467 : PrimeValue := ⟨293467, pr293467⟩
private theorem pr293543 : Nat.Prime 293543 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv317,pv463]) (by decide +kernel)
def pv293543 : PrimeValue := ⟨293543, pr293543⟩
private theorem pr293617 : Nat.Prime 293617 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2039]) (by decide +kernel)
def pv293617 : PrimeValue := ⟨293617, pr293617⟩
private theorem pr293633 : Nat.Prime 293633 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv31,pv37]) (by decide +kernel)
def pv293633 : PrimeValue := ⟨293633, pr293633⟩
private theorem pr293651 : Nat.Prime 293651 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv7,pv839]) (by decide +kernel)
def pv293651 : PrimeValue := ⟨293651, pr293651⟩
private theorem pr293677 : Nat.Prime 293677 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv24473]) (by decide +kernel)
def pv293677 : PrimeValue := ⟨293677, pr293677⟩
private theorem pr293681 : Nat.Prime 293681 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv3671]) (by decide +kernel)
def pv293681 : PrimeValue := ⟨293681, pr293681⟩
private theorem pr293701 : Nat.Prime 293701 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv89]) (by decide +kernel)
def pv293701 : PrimeValue := ⟨293701, pr293701⟩
private theorem pr293729 : Nat.Prime 293729 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv67,pv137]) (by decide +kernel)
def pv293729 : PrimeValue := ⟨293729, pr293729⟩
private theorem pr293767 : Nat.Prime 293767 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv4451]) (by decide +kernel)
def pv293767 : PrimeValue := ⟨293767, pr293767⟩
private theorem pr293773 : Nat.Prime 293773 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv24481]) (by decide +kernel)
def pv293773 : PrimeValue := ⟨293773, pr293773⟩
private theorem pr293827 : Nat.Prime 293827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv3767]) (by decide +kernel)
def pv293827 : PrimeValue := ⟨293827, pr293827⟩
private theorem pr293831 : Nat.Prime 293831 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv29383]) (by decide +kernel)
def pv293831 : PrimeValue := ⟨293831, pr293831⟩
private theorem pr293893 : Nat.Prime 293893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv1289]) (by decide +kernel)
def pv293893 : PrimeValue := ⟨293893, pr293893⟩
private theorem pr293989 : Nat.Prime 293989 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv24499]) (by decide +kernel)
def pv293989 : PrimeValue := ⟨293989, pr293989⟩
private theorem pr293999 : Nat.Prime 293999 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv17,pv8647]) (by decide +kernel)
def pv293999 : PrimeValue := ⟨293999, pr293999⟩
private theorem pr294001 : Nat.Prime 294001 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv294001 : PrimeValue := ⟨294001, pr294001⟩
private theorem pr294043 : Nat.Prime 294043 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv7001]) (by decide +kernel)
def pv294043 : PrimeValue := ⟨294043, pr294043⟩
private theorem pr294053 : Nat.Prime 294053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv41,pv163]) (by decide +kernel)
def pv294053 : PrimeValue := ⟨294053, pr294053⟩
private theorem pr294059 : Nat.Prime 294059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv147029]) (by decide +kernel)
def pv294059 : PrimeValue := ⟨294059, pr294059⟩
private theorem pr294067 : Nat.Prime 294067 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv31]) (by decide +kernel)
def pv294067 : PrimeValue := ⟨294067, pr294067⟩
private theorem pr294103 : Nat.Prime 294103 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv16339]) (by decide +kernel)
def pv294103 : PrimeValue := ⟨294103, pr294103⟩
private theorem pr294127 : Nat.Prime 294127 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv47,pv149]) (by decide +kernel)
def pv294127 : PrimeValue := ⟨294127, pr294127⟩
private theorem pr294131 : Nat.Prime 294131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv67,pv439]) (by decide +kernel)
def pv294131 : PrimeValue := ⟨294131, pr294131⟩
private theorem pr294149 : Nat.Prime 294149 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv151,pv487]) (by decide +kernel)
def pv294149 : PrimeValue := ⟨294149, pr294149⟩
private theorem pr294157 : Nat.Prime 294157 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv8171]) (by decide +kernel)
def pv294157 : PrimeValue := ⟨294157, pr294157⟩
private theorem pr294169 : Nat.Prime 294169 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv17,pv103]) (by decide +kernel)
def pv294169 : PrimeValue := ⟨294169, pr294169⟩
private theorem pr294179 : Nat.Prime 294179 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv147089]) (by decide +kernel)
def pv294179 : PrimeValue := ⟨294179, pr294179⟩
private theorem pr294181 : Nat.Prime 294181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv4903]) (by decide +kernel)
def pv294181 : PrimeValue := ⟨294181, pr294181⟩
private theorem pr294199 : Nat.Prime 294199 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv49033]) (by decide +kernel)
def pv294199 : PrimeValue := ⟨294199, pr294199⟩
private theorem pr294227 : Nat.Prime 294227 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv131,pv1123]) (by decide +kernel)
def pv294227 : PrimeValue := ⟨294227, pr294227⟩
private theorem pr294251 : Nat.Prime 294251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv107]) (by decide +kernel)
def pv294251 : PrimeValue := ⟨294251, pr294251⟩
private theorem pr294269 : Nat.Prime 294269 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv5659]) (by decide +kernel)
def pv294269 : PrimeValue := ⟨294269, pr294269⟩
private theorem pr294289 : Nat.Prime 294289 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv6131]) (by decide +kernel)
def pv294289 : PrimeValue := ⟨294289, pr294289⟩
private theorem pr294293 : Nat.Prime 294293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv43,pv59]) (by decide +kernel)
def pv294293 : PrimeValue := ⟨294293, pr294293⟩
private theorem pr294311 : Nat.Prime 294311 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv19,pv1549]) (by decide +kernel)
def pv294311 : PrimeValue := ⟨294311, pr294311⟩
private theorem pr294319 : Nat.Prime 294319 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv83,pv197]) (by decide +kernel)
def pv294319 : PrimeValue := ⟨294319, pr294319⟩
private theorem pr294337 : Nat.Prime 294337 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv73]) (by decide +kernel)
def pv294337 : PrimeValue := ⟨294337, pr294337⟩
private theorem pr294341 : Nat.Prime 294341 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv14717]) (by decide +kernel)
def pv294341 : PrimeValue := ⟨294341, pr294341⟩
private theorem pr294383 : Nat.Prime 294383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv13381]) (by decide +kernel)
def pv294383 : PrimeValue := ⟨294383, pr294383⟩
private theorem pr294391 : Nat.Prime 294391 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv3271]) (by decide +kernel)
def pv294391 : PrimeValue := ⟨294391, pr294391⟩
private theorem pr294397 : Nat.Prime 294397 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv24533]) (by decide +kernel)
def pv294397 : PrimeValue := ⟨294397, pr294397⟩
private theorem pr294403 : Nat.Prime 294403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv139,pv353]) (by decide +kernel)
def pv294403 : PrimeValue := ⟨294403, pr294403⟩
private theorem pr294431 : Nat.Prime 294431 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv29443]) (by decide +kernel)
def pv294431 : PrimeValue := ⟨294431, pr294431⟩
private theorem pr294467 : Nat.Prime 294467 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv5077]) (by decide +kernel)
def pv294467 : PrimeValue := ⟨294467, pr294467⟩
private theorem pr294499 : Nat.Prime 294499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv16361]) (by decide +kernel)
def pv294499 : PrimeValue := ⟨294499, pr294499⟩
private theorem pr294509 : Nat.Prime 294509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv61,pv71]) (by decide +kernel)
def pv294509 : PrimeValue := ⟨294509, pr294509⟩
private theorem pr294529 : Nat.Prime 294529 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv13,pv59]) (by decide +kernel)
def pv294529 : PrimeValue := ⟨294529, pr294529⟩
private theorem pr294551 : Nat.Prime 294551 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv43,pv137]) (by decide +kernel)
def pv294551 : PrimeValue := ⟨294551, pr294551⟩
private theorem pr294773 : Nat.Prime 294773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv73693]) (by decide +kernel)
def pv294773 : PrimeValue := ⟨294773, pr294773⟩
private theorem pr294787 : Nat.Prime 294787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv53,pv103]) (by decide +kernel)
def pv294787 : PrimeValue := ⟨294787, pr294787⟩
private theorem pr294793 : Nat.Prime 294793 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv71,pv173]) (by decide +kernel)
def pv294793 : PrimeValue := ⟨294793, pr294793⟩
private theorem pr294803 : Nat.Prime 294803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv147401]) (by decide +kernel)
def pv294803 : PrimeValue := ⟨294803, pr294803⟩
private theorem pr294821 : Nat.Prime 294821 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv14741]) (by decide +kernel)
def pv294821 : PrimeValue := ⟨294821, pr294821⟩
private theorem pr294829 : Nat.Prime 294829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv79,pv311]) (by decide +kernel)
def pv294829 : PrimeValue := ⟨294829, pr294829⟩
private theorem pr294869 : Nat.Prime 294869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv10531]) (by decide +kernel)
def pv294869 : PrimeValue := ⟨294869, pr294869⟩
private theorem pr294887 : Nat.Prime 294887 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv283,pv521]) (by decide +kernel)
def pv294887 : PrimeValue := ⟨294887, pr294887⟩
private theorem pr294919 : Nat.Prime 294919 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv19,pv199]) (by decide +kernel)
def pv294919 : PrimeValue := ⟨294919, pr294919⟩
private theorem pr294923 : Nat.Prime 294923 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv167,pv883]) (by decide +kernel)
def pv294923 : PrimeValue := ⟨294923, pr294923⟩
private theorem pr294949 : Nat.Prime 294949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2731]) (by decide +kernel)
def pv294949 : PrimeValue := ⟨294949, pr294949⟩
private theorem pr294991 : Nat.Prime 294991 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv9833]) (by decide +kernel)
def pv294991 : PrimeValue := ⟨294991, pr294991⟩
private theorem pr294997 : Nat.Prime 294997 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv31,pv61]) (by decide +kernel)
def pv294997 : PrimeValue := ⟨294997, pr294997⟩
private theorem pr295033 : Nat.Prime 295033 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv19,pv647]) (by decide +kernel)
def pv295033 : PrimeValue := ⟨295033, pr295033⟩
private theorem pr295049 : Nat.Prime 295049 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv2837]) (by decide +kernel)
def pv295049 : PrimeValue := ⟨295049, pr295049⟩
private theorem pr295123 : Nat.Prime 295123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv101,pv487]) (by decide +kernel)
def pv295123 : PrimeValue := ⟨295123, pr295123⟩
private theorem pr295153 : Nat.Prime 295153 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv11,pv13,pv43]) (by decide +kernel)
def pv295153 : PrimeValue := ⟨295153, pr295153⟩
private theorem pr295187 : Nat.Prime 295187 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv37,pv3989]) (by decide +kernel)
def pv295187 : PrimeValue := ⟨295187, pr295187⟩
private theorem pr295199 : Nat.Prime 295199 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv103,pv1433]) (by decide +kernel)
def pv295199 : PrimeValue := ⟨295199, pr295199⟩
private theorem pr295219 : Nat.Prime 295219 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv71]) (by decide +kernel)
def pv295219 : PrimeValue := ⟨295219, pr295219⟩
private theorem pr295237 : Nat.Prime 295237 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv59,pv139]) (by decide +kernel)
def pv295237 : PrimeValue := ⟨295237, pr295237⟩
private theorem pr295247 : Nat.Prime 295247 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv21089]) (by decide +kernel)
def pv295247 : PrimeValue := ⟨295247, pr295247⟩
private theorem pr295271 : Nat.Prime 295271 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv29527]) (by decide +kernel)
def pv295271 : PrimeValue := ⟨295271, pr295271⟩
private theorem pr295283 : Nat.Prime 295283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv41,pv277]) (by decide +kernel)
def pv295283 : PrimeValue := ⟨295283, pr295283⟩
private theorem pr295291 : Nat.Prime 295291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv193]) (by decide +kernel)
def pv295291 : PrimeValue := ⟨295291, pr295291⟩
private theorem pr295313 : Nat.Prime 295313 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv18457]) (by decide +kernel)
def pv295313 : PrimeValue := ⟨295313, pr295313⟩
private theorem pr295333 : Nat.Prime 295333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv24611]) (by decide +kernel)
def pv295333 : PrimeValue := ⟨295333, pr295333⟩
private theorem pr295357 : Nat.Prime 295357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv151,pv163]) (by decide +kernel)
def pv295357 : PrimeValue := ⟨295357, pr295357⟩
private theorem pr295387 : Nat.Prime 295387 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv541]) (by decide +kernel)
def pv295387 : PrimeValue := ⟨295387, pr295387⟩
private theorem pr295411 : Nat.Prime 295411 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv43,pv229]) (by decide +kernel)
def pv295411 : PrimeValue := ⟨295411, pr295411⟩
private theorem pr295433 : Nat.Prime 295433 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv36929]) (by decide +kernel)
def pv295433 : PrimeValue := ⟨295433, pr295433⟩
private theorem pr295439 : Nat.Prime 295439 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv11,pv13,pv1033]) (by decide +kernel)
def pv295439 : PrimeValue := ⟨295439, pr295439⟩
private theorem pr295441 : Nat.Prime 295441 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv1231]) (by decide +kernel)
def pv295441 : PrimeValue := ⟨295441, pr295441⟩
private theorem pr295513 : Nat.Prime 295513 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv1759]) (by decide +kernel)
def pv295513 : PrimeValue := ⟨295513, pr295513⟩
private theorem pr295553 : Nat.Prime 295553 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2309]) (by decide +kernel)
def pv295553 : PrimeValue := ⟨295553, pr295553⟩
private theorem pr295601 : Nat.Prime 295601 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv739]) (by decide +kernel)
def pv295601 : PrimeValue := ⟨295601, pr295601⟩
private theorem pr295663 : Nat.Prime 295663 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv49277]) (by decide +kernel)
def pv295663 : PrimeValue := ⟨295663, pr295663⟩
private theorem pr295693 : Nat.Prime 295693 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv41,pv601]) (by decide +kernel)
def pv295693 : PrimeValue := ⟨295693, pr295693⟩
private theorem pr295699 : Nat.Prime 295699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv17,pv223]) (by decide +kernel)
def pv295699 : PrimeValue := ⟨295699, pr295699⟩
private theorem pr295703 : Nat.Prime 295703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv13441]) (by decide +kernel)
def pv295703 : PrimeValue := ⟨295703, pr295703⟩
private theorem pr295727 : Nat.Prime 295727 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv147863]) (by decide +kernel)
def pv295727 : PrimeValue := ⟨295727, pr295727⟩
private theorem pr295787 : Nat.Prime 295787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv71,pv2083]) (by decide +kernel)
def pv295787 : PrimeValue := ⟨295787, pr295787⟩
private theorem pr295819 : Nat.Prime 295819 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv47,pv1049]) (by decide +kernel)
def pv295819 : PrimeValue := ⟨295819, pr295819⟩
private theorem pr295831 : Nat.Prime 295831 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv19,pv173]) (by decide +kernel)
def pv295831 : PrimeValue := ⟨295831, pr295831⟩
private theorem pr295837 : Nat.Prime 295837 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv89,pv277]) (by decide +kernel)
def pv295837 : PrimeValue := ⟨295837, pr295837⟩
private theorem pr295871 : Nat.Prime 295871 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv29587]) (by decide +kernel)
def pv295871 : PrimeValue := ⟨295871, pr295871⟩
private theorem pr295903 : Nat.Prime 295903 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv967]) (by decide +kernel)
def pv295903 : PrimeValue := ⟨295903, pr295903⟩
private theorem pr295909 : Nat.Prime 295909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv24659]) (by decide +kernel)
def pv295909 : PrimeValue := ⟨295909, pr295909⟩
private theorem pr295943 : Nat.Prime 295943 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv73,pv2027]) (by decide +kernel)
def pv295943 : PrimeValue := ⟨295943, pr295943⟩
private theorem pr296011 : Nat.Prime 296011 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv13,pv23]) (by decide +kernel)
def pv296011 : PrimeValue := ⟨296011, pr296011⟩
private theorem pr296017 : Nat.Prime 296017 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv881]) (by decide +kernel)
def pv296017 : PrimeValue := ⟨296017, pr296017⟩
private theorem pr296047 : Nat.Prime 296047 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv16447]) (by decide +kernel)
def pv296047 : PrimeValue := ⟨296047, pr296047⟩
private theorem pr296083 : Nat.Prime 296083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5483]) (by decide +kernel)
def pv296083 : PrimeValue := ⟨296083, pr296083⟩
private theorem pr296099 : Nat.Prime 296099 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv43,pv313]) (by decide +kernel)
def pv296099 : PrimeValue := ⟨296099, pr296099⟩
private theorem pr296117 : Nat.Prime 296117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv181,pv409]) (by decide +kernel)
def pv296117 : PrimeValue := ⟨296117, pr296117⟩
private theorem pr296129 : Nat.Prime 296129 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv661]) (by decide +kernel)
def pv296129 : PrimeValue := ⟨296129, pr296129⟩
private theorem pr296137 : Nat.Prime 296137 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv457]) (by decide +kernel)
def pv296137 : PrimeValue := ⟨296137, pr296137⟩
private theorem pr296183 : Nat.Prime 296183 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv148091]) (by decide +kernel)
def pv296183 : PrimeValue := ⟨296183, pr296183⟩
private theorem pr296237 : Nat.Prime 296237 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv2389]) (by decide +kernel)
def pv296237 : PrimeValue := ⟨296237, pr296237⟩
private theorem pr296243 : Nat.Prime 296243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv8713]) (by decide +kernel)
def pv296243 : PrimeValue := ⟨296243, pr296243⟩
private theorem pr296249 : Nat.Prime 296249 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv1949]) (by decide +kernel)
def pv296249 : PrimeValue := ⟨296249, pr296249⟩
private theorem pr296269 : Nat.Prime 296269 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv3527]) (by decide +kernel)
def pv296269 : PrimeValue := ⟨296269, pr296269⟩
private theorem pr296273 : Nat.Prime 296273 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv18517]) (by decide +kernel)
def pv296273 : PrimeValue := ⟨296273, pr296273⟩
private theorem pr296287 : Nat.Prime 296287 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv23,pv113]) (by decide +kernel)
def pv296287 : PrimeValue := ⟨296287, pr296287⟩
private theorem pr296299 : Nat.Prime 296299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv59]) (by decide +kernel)
def pv296299 : PrimeValue := ⟨296299, pr296299⟩
private theorem pr296347 : Nat.Prime 296347 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv49391]) (by decide +kernel)
def pv296347 : PrimeValue := ⟨296347, pr296347⟩
private theorem pr296363 : Nat.Prime 296363 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv19,pv709]) (by decide +kernel)
def pv296363 : PrimeValue := ⟨296363, pr296363⟩
private theorem pr296377 : Nat.Prime 296377 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv53,pv233]) (by decide +kernel)
def pv296377 : PrimeValue := ⟨296377, pr296377⟩
private theorem pr296437 : Nat.Prime 296437 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv7,pv3529]) (by decide +kernel)
def pv296437 : PrimeValue := ⟨296437, pr296437⟩
private theorem pr296473 : Nat.Prime 296473 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv11,pv1123]) (by decide +kernel)
def pv296473 : PrimeValue := ⟨296473, pr296473⟩
private theorem pr296563 : Nat.Prime 296563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv23,pv307]) (by decide +kernel)
def pv296563 : PrimeValue := ⟨296563, pr296563⟩
private theorem pr296579 : Nat.Prime 296579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv257,pv577]) (by decide +kernel)
def pv296579 : PrimeValue := ⟨296579, pr296579⟩
private theorem pr296581 : Nat.Prime 296581 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv4943]) (by decide +kernel)
def pv296581 : PrimeValue := ⟨296581, pr296581⟩
private theorem pr296587 : Nat.Prime 296587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv16477]) (by decide +kernel)
def pv296587 : PrimeValue := ⟨296587, pr296587⟩
private theorem pr296591 : Nat.Prime 296591 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv19,pv223]) (by decide +kernel)
def pv296591 : PrimeValue := ⟨296591, pr296591⟩
private theorem pr296683 : Nat.Prime 296683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv197,pv251]) (by decide +kernel)
def pv296683 : PrimeValue := ⟨296683, pr296683⟩
private theorem pr296693 : Nat.Prime 296693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv613]) (by decide +kernel)
def pv296693 : PrimeValue := ⟨296693, pr296693⟩
private theorem pr296713 : Nat.Prime 296713 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv317]) (by decide +kernel)
def pv296713 : PrimeValue := ⟨296713, pr296713⟩
private theorem pr296741 : Nat.Prime 296741 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv37,pv401]) (by decide +kernel)
def pv296741 : PrimeValue := ⟨296741, pr296741⟩
private theorem pr296749 : Nat.Prime 296749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv8243]) (by decide +kernel)
def pv296749 : PrimeValue := ⟨296749, pr296749⟩
private theorem pr296753 : Nat.Prime 296753 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv1091]) (by decide +kernel)
def pv296753 : PrimeValue := ⟨296753, pr296753⟩
private theorem pr296771 : Nat.Prime 296771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv59,pv503]) (by decide +kernel)
def pv296771 : PrimeValue := ⟨296771, pr296771⟩
private theorem pr296797 : Nat.Prime 296797 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv24733]) (by decide +kernel)
def pv296797 : PrimeValue := ⟨296797, pr296797⟩
private theorem pr296801 : Nat.Prime 296801 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv53]) (by decide +kernel)
def pv296801 : PrimeValue := ⟨296801, pr296801⟩
private theorem pr296819 : Nat.Prime 296819 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv73,pv107]) (by decide +kernel)
def pv296819 : PrimeValue := ⟨296819, pr296819⟩
private theorem pr296827 : Nat.Prime 296827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv61,pv811]) (by decide +kernel)
def pv296827 : PrimeValue := ⟨296827, pr296827⟩
private theorem pr296831 : Nat.Prime 296831 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv29683]) (by decide +kernel)
def pv296831 : PrimeValue := ⟨296831, pr296831⟩
private theorem pr296909 : Nat.Prime 296909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv199,pv373]) (by decide +kernel)
def pv296909 : PrimeValue := ⟨296909, pr296909⟩
private theorem pr296911 : Nat.Prime 296911 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv3299]) (by decide +kernel)
def pv296911 : PrimeValue := ⟨296911, pr296911⟩
private theorem pr296929 : Nat.Prime 296929 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv1031]) (by decide +kernel)
def pv296929 : PrimeValue := ⟨296929, pr296929⟩
private theorem pr296971 : Nat.Prime 296971 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv19,pv521]) (by decide +kernel)
def pv296971 : PrimeValue := ⟨296971, pr296971⟩
private theorem pr296983 : Nat.Prime 296983 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv2357]) (by decide +kernel)
def pv296983 : PrimeValue := ⟨296983, pr296983⟩
private theorem pr297023 : Nat.Prime 297023 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv11,pv23,pv587]) (by decide +kernel)
def pv297023 : PrimeValue := ⟨297023, pr297023⟩
private theorem pr297049 : Nat.Prime 297049 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv12377]) (by decide +kernel)
def pv297049 : PrimeValue := ⟨297049, pr297049⟩
private theorem pr297067 : Nat.Prime 297067 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv643]) (by decide +kernel)
def pv297067 : PrimeValue := ⟨297067, pr297067⟩
private theorem pr297079 : Nat.Prime 297079 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv67,pv739]) (by decide +kernel)
def pv297079 : PrimeValue := ⟨297079, pr297079⟩
private theorem pr297083 : Nat.Prime 297083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv89,pv1669]) (by decide +kernel)
def pv297083 : PrimeValue := ⟨297083, pr297083⟩
private theorem pr297097 : Nat.Prime 297097 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv12379]) (by decide +kernel)
def pv297097 : PrimeValue := ⟨297097, pr297097⟩
private theorem pr297113 : Nat.Prime 297113 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv37139]) (by decide +kernel)
def pv297113 : PrimeValue := ⟨297113, pr297113⟩
private theorem pr297151 : Nat.Prime 297151 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv283]) (by decide +kernel)
def pv297151 : PrimeValue := ⟨297151, pr297151⟩
private theorem pr297233 : Nat.Prime 297233 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv1429]) (by decide +kernel)
def pv297233 : PrimeValue := ⟨297233, pr297233⟩
private theorem pr297251 : Nat.Prime 297251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv29,pv41]) (by decide +kernel)
def pv297251 : PrimeValue := ⟨297251, pr297251⟩
private theorem pr297257 : Nat.Prime 297257 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv73,pv509]) (by decide +kernel)
def pv297257 : PrimeValue := ⟨297257, pr297257⟩
private theorem pr297371 : Nat.Prime 297371 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv131,pv227]) (by decide +kernel)
def pv297371 : PrimeValue := ⟨297371, pr297371⟩
private theorem pr297403 : Nat.Prime 297403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv73,pv97]) (by decide +kernel)
def pv297403 : PrimeValue := ⟨297403, pr297403⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
