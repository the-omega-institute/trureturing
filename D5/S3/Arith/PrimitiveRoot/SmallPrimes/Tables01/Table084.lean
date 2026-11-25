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
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr291007 : PrimeCertificate 291007 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv317]) (by decide +kernel)
def pv291007 : PrimeValue := ⟨291007, pr291007⟩
private theorem pr291041 : PrimeCertificate 291041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17,pv107]) (by decide +kernel)
def pv291041 : PrimeValue := ⟨291041, pr291041⟩
private theorem pr291043 : PrimeCertificate 291043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv23,pv37]) (by decide +kernel)
def pv291043 : PrimeValue := ⟨291043, pr291043⟩
private theorem pr291077 : PrimeCertificate 291077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv1373]) (by decide +kernel)
def pv291077 : PrimeValue := ⟨291077, pr291077⟩
private theorem pr291089 : PrimeCertificate 291089 :=
  certifyPrime (q := pv11) (ls := [pv2,pv7,pv23,pv113]) (by decide +kernel)
def pv291089 : PrimeValue := ⟨291089, pr291089⟩
private theorem pr291101 : PrimeCertificate 291101 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41,pv71]) (by decide +kernel)
def pv291101 : PrimeValue := ⟨291101, pr291101⟩
private theorem pr291103 : PrimeCertificate 291103 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv29,pv239]) (by decide +kernel)
def pv291103 : PrimeValue := ⟨291103, pr291103⟩
private theorem pr291107 : PrimeCertificate 291107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59,pv2467]) (by decide +kernel)
def pv291107 : PrimeValue := ⟨291107, pr291107⟩
private theorem pr291113 : PrimeCertificate 291113 :=
  certifyPrime (q := pv3) (ls := [pv2,pv36389]) (by decide +kernel)
def pv291113 : PrimeValue := ⟨291113, pr291113⟩
private theorem pr291143 : PrimeCertificate 291143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv8563]) (by decide +kernel)
def pv291143 : PrimeValue := ⟨291143, pr291143⟩
private theorem pr291167 : PrimeCertificate 291167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv197,pv739]) (by decide +kernel)
def pv291167 : PrimeValue := ⟨291167, pr291167⟩
private theorem pr291209 : PrimeCertificate 291209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv89,pv409]) (by decide +kernel)
def pv291209 : PrimeValue := ⟨291209, pr291209⟩
private theorem pr291217 : PrimeCertificate 291217 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv6067]) (by decide +kernel)
def pv291217 : PrimeValue := ⟨291217, pr291217⟩
private theorem pr291253 : PrimeCertificate 291253 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv1867]) (by decide +kernel)
def pv291253 : PrimeValue := ⟨291253, pr291253⟩
private theorem pr291287 : PrimeCertificate 291287 :=
  certifyPrime (q := pv5) (ls := [pv2,pv145643]) (by decide +kernel)
def pv291287 : PrimeValue := ⟨291287, pr291287⟩
private theorem pr291293 : PrimeCertificate 291293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv72823]) (by decide +kernel)
def pv291293 : PrimeValue := ⟨291293, pr291293⟩
private theorem pr291331 : PrimeCertificate 291331 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv5,pv13,pv83]) (by decide +kernel)
def pv291331 : PrimeValue := ⟨291331, pr291331⟩
private theorem pr291337 : PrimeCertificate 291337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv61,pv199]) (by decide +kernel)
def pv291337 : PrimeValue := ⟨291337, pr291337⟩
private theorem pr291349 : PrimeCertificate 291349 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv8093]) (by decide +kernel)
def pv291349 : PrimeValue := ⟨291349, pr291349⟩
private theorem pr291359 : PrimeCertificate 291359 :=
  certifyPrime (q := pv23) (ls := [pv2,pv145679]) (by decide +kernel)
def pv291359 : PrimeValue := ⟨291359, pr291359⟩
private theorem pr291373 : PrimeCertificate 291373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv24281]) (by decide +kernel)
def pv291373 : PrimeValue := ⟨291373, pr291373⟩
private theorem pr291419 : PrimeCertificate 291419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv145709]) (by decide +kernel)
def pv291419 : PrimeValue := ⟨291419, pr291419⟩
private theorem pr291437 : PrimeCertificate 291437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv72859]) (by decide +kernel)
def pv291437 : PrimeValue := ⟨291437, pr291437⟩
private theorem pr291443 : PrimeCertificate 291443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv145721]) (by decide +kernel)
def pv291443 : PrimeValue := ⟨291443, pr291443⟩
private theorem pr291457 : PrimeCertificate 291457 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv23]) (by decide +kernel)
def pv291457 : PrimeValue := ⟨291457, pr291457⟩
private theorem pr291491 : PrimeCertificate 291491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv103,pv283]) (by decide +kernel)
def pv291491 : PrimeValue := ⟨291491, pr291491⟩
private theorem pr291503 : PrimeCertificate 291503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv6337]) (by decide +kernel)
def pv291503 : PrimeValue := ⟨291503, pr291503⟩
private theorem pr291509 : PrimeCertificate 291509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv29,pv359]) (by decide +kernel)
def pv291509 : PrimeValue := ⟨291509, pr291509⟩
private theorem pr291539 : PrimeCertificate 291539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv11213]) (by decide +kernel)
def pv291539 : PrimeValue := ⟨291539, pr291539⟩
private theorem pr291559 : PrimeCertificate 291559 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv48593]) (by decide +kernel)
def pv291559 : PrimeValue := ⟨291559, pr291559⟩
private theorem pr291563 : PrimeCertificate 291563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv1997]) (by decide +kernel)
def pv291563 : PrimeValue := ⟨291563, pr291563⟩
private theorem pr291569 : PrimeCertificate 291569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv18223]) (by decide +kernel)
def pv291569 : PrimeValue := ⟨291569, pr291569⟩
private theorem pr291649 : PrimeCertificate 291649 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv31]) (by decide +kernel)
def pv291649 : PrimeValue := ⟨291649, pr291649⟩
private theorem pr291661 : PrimeCertificate 291661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv4861]) (by decide +kernel)
def pv291661 : PrimeValue := ⟨291661, pr291661⟩
private theorem pr291701 : PrimeCertificate 291701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv2917]) (by decide +kernel)
def pv291701 : PrimeValue := ⟨291701, pr291701⟩
private theorem pr291743 : PrimeCertificate 291743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv89,pv149]) (by decide +kernel)
def pv291743 : PrimeValue := ⟨291743, pr291743⟩
private theorem pr291751 : PrimeCertificate 291751 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv389]) (by decide +kernel)
def pv291751 : PrimeValue := ⟨291751, pr291751⟩
private theorem pr291791 : PrimeCertificate 291791 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv29179]) (by decide +kernel)
def pv291791 : PrimeValue := ⟨291791, pr291791⟩
private theorem pr291829 : PrimeCertificate 291829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv83,pv293]) (by decide +kernel)
def pv291829 : PrimeValue := ⟨291829, pr291829⟩
private theorem pr291833 : PrimeCertificate 291833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv36479]) (by decide +kernel)
def pv291833 : PrimeValue := ⟨291833, pr291833⟩
private theorem pr291857 : PrimeCertificate 291857 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv29,pv37]) (by decide +kernel)
def pv291857 : PrimeValue := ⟨291857, pr291857⟩
private theorem pr291869 : PrimeCertificate 291869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv131,pv557]) (by decide +kernel)
def pv291869 : PrimeValue := ⟨291869, pr291869⟩
private theorem pr291887 : PrimeCertificate 291887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv20849]) (by decide +kernel)
def pv291887 : PrimeValue := ⟨291887, pr291887⟩
private theorem pr291901 : PrimeCertificate 291901 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv7,pv139]) (by decide +kernel)
def pv291901 : PrimeValue := ⟨291901, pr291901⟩
private theorem pr291971 : PrimeCertificate 291971 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv43,pv97]) (by decide +kernel)
def pv291971 : PrimeValue := ⟨291971, pr291971⟩
private theorem pr292057 : PrimeCertificate 292057 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv43,pv283]) (by decide +kernel)
def pv292057 : PrimeValue := ⟨292057, pr292057⟩
private theorem pr292069 : PrimeCertificate 292069 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv19,pv61]) (by decide +kernel)
def pv292069 : PrimeValue := ⟨292069, pr292069⟩
private theorem pr292081 : PrimeCertificate 292081 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv1217]) (by decide +kernel)
def pv292081 : PrimeValue := ⟨292081, pr292081⟩
private theorem pr292091 : PrimeCertificate 292091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29209]) (by decide +kernel)
def pv292091 : PrimeValue := ⟨292091, pr292091⟩
private theorem pr292133 : PrimeCertificate 292133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv199,pv367]) (by decide +kernel)
def pv292133 : PrimeValue := ⟨292133, pr292133⟩
private theorem pr292157 : PrimeCertificate 292157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73039]) (by decide +kernel)
def pv292157 : PrimeValue := ⟨292157, pr292157⟩
private theorem pr292223 : PrimeCertificate 292223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv20873]) (by decide +kernel)
def pv292223 : PrimeValue := ⟨292223, pr292223⟩
private theorem pr292249 : PrimeCertificate 292249 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv11,pv41]) (by decide +kernel)
def pv292249 : PrimeValue := ⟨292249, pr292249⟩
private theorem pr292267 : PrimeCertificate 292267 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13,pv1249]) (by decide +kernel)
def pv292267 : PrimeValue := ⟨292267, pr292267⟩
private theorem pr292301 : PrimeCertificate 292301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv37,pv79]) (by decide +kernel)
def pv292301 : PrimeValue := ⟨292301, pr292301⟩
private theorem pr292309 : PrimeCertificate 292309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv24359]) (by decide +kernel)
def pv292309 : PrimeValue := ⟨292309, pr292309⟩
private theorem pr292363 : PrimeCertificate 292363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv6961]) (by decide +kernel)
def pv292363 : PrimeValue := ⟨292363, pr292363⟩
private theorem pr292381 : PrimeCertificate 292381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv443]) (by decide +kernel)
def pv292381 : PrimeValue := ⟨292381, pr292381⟩
private theorem pr292393 : PrimeCertificate 292393 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv131]) (by decide +kernel)
def pv292393 : PrimeValue := ⟨292393, pr292393⟩
private theorem pr292427 : PrimeCertificate 292427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv146213]) (by decide +kernel)
def pv292427 : PrimeValue := ⟨292427, pr292427⟩
private theorem pr292471 : PrimeCertificate 292471 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv9749]) (by decide +kernel)
def pv292471 : PrimeValue := ⟨292471, pr292471⟩
private theorem pr292483 : PrimeCertificate 292483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv16249]) (by decide +kernel)
def pv292483 : PrimeValue := ⟨292483, pr292483⟩
private theorem pr292573 : PrimeCertificate 292573 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv43]) (by decide +kernel)
def pv292573 : PrimeValue := ⟨292573, pr292573⟩
private theorem pr292577 : PrimeCertificate 292577 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41,pv223]) (by decide +kernel)
def pv292577 : PrimeValue := ⟨292577, pr292577⟩
private theorem pr292627 : PrimeCertificate 292627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5419]) (by decide +kernel)
def pv292627 : PrimeValue := ⟨292627, pr292627⟩
private theorem pr292679 : PrimeCertificate 292679 :=
  certifyPrime (q := pv7) (ls := [pv2,pv61,pv2399]) (by decide +kernel)
def pv292679 : PrimeValue := ⟨292679, pr292679⟩
private theorem pr292709 : PrimeCertificate 292709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv433]) (by decide +kernel)
def pv292709 : PrimeValue := ⟨292709, pr292709⟩
private theorem pr292711 : PrimeCertificate 292711 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv11,pv887]) (by decide +kernel)
def pv292711 : PrimeValue := ⟨292711, pr292711⟩
private theorem pr292727 : PrimeCertificate 292727 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv29,pv103]) (by decide +kernel)
def pv292727 : PrimeValue := ⟨292727, pr292727⟩
private theorem pr292753 : PrimeCertificate 292753 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv107]) (by decide +kernel)
def pv292753 : PrimeValue := ⟨292753, pr292753⟩
private theorem pr292759 : PrimeCertificate 292759 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv59,pv827]) (by decide +kernel)
def pv292759 : PrimeValue := ⟨292759, pr292759⟩
private theorem pr292777 : PrimeCertificate 292777 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv1109]) (by decide +kernel)
def pv292777 : PrimeValue := ⟨292777, pr292777⟩
private theorem pr292793 : PrimeCertificate 292793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv36599]) (by decide +kernel)
def pv292793 : PrimeValue := ⟨292793, pr292793⟩
private theorem pr292849 : PrimeCertificate 292849 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv6101]) (by decide +kernel)
def pv292849 : PrimeValue := ⟨292849, pr292849⟩
private theorem pr292879 : PrimeCertificate 292879 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv53,pv307]) (by decide +kernel)
def pv292879 : PrimeValue := ⟨292879, pr292879⟩
private theorem pr292909 : PrimeCertificate 292909 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv7,pv11,pv317]) (by decide +kernel)
def pv292909 : PrimeValue := ⟨292909, pr292909⟩
private theorem pr292921 : PrimeCertificate 292921 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv2441]) (by decide +kernel)
def pv292921 : PrimeValue := ⟨292921, pr292921⟩
private theorem pr292933 : PrimeCertificate 292933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv79,pv103]) (by decide +kernel)
def pv292933 : PrimeValue := ⟨292933, pr292933⟩
private theorem pr292979 : PrimeCertificate 292979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv17,pv1231]) (by decide +kernel)
def pv292979 : PrimeValue := ⟨292979, pr292979⟩
private theorem pr293081 : PrimeCertificate 293081 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17,pv431]) (by decide +kernel)
def pv293081 : PrimeValue := ⟨293081, pr293081⟩
private theorem pr293087 : PrimeCertificate 293087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv146543]) (by decide +kernel)
def pv293087 : PrimeValue := ⟨293087, pr293087⟩
private theorem pr293107 : PrimeCertificate 293107 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11,pv4441]) (by decide +kernel)
def pv293107 : PrimeValue := ⟨293107, pr293107⟩
private theorem pr293123 : PrimeCertificate 293123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv113,pv1297]) (by decide +kernel)
def pv293123 : PrimeValue := ⟨293123, pr293123⟩
private theorem pr293129 : PrimeCertificate 293129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv3331]) (by decide +kernel)
def pv293129 : PrimeValue := ⟨293129, pr293129⟩
private theorem pr293201 : PrimeCertificate 293201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv733]) (by decide +kernel)
def pv293201 : PrimeValue := ⟨293201, pr293201⟩
private theorem pr293207 : PrimeCertificate 293207 :=
  certifyPrime (q := pv5) (ls := [pv2,pv146603]) (by decide +kernel)
def pv293207 : PrimeValue := ⟨293207, pr293207⟩
private theorem pr293257 : PrimeCertificate 293257 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv4073]) (by decide +kernel)
def pv293257 : PrimeValue := ⟨293257, pr293257⟩
private theorem pr293261 : PrimeCertificate 293261 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv31,pv43]) (by decide +kernel)
def pv293261 : PrimeValue := ⟨293261, pr293261⟩
private theorem pr293263 : PrimeCertificate 293263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv37,pv1321]) (by decide +kernel)
def pv293263 : PrimeValue := ⟨293263, pr293263⟩
private theorem pr293269 : PrimeCertificate 293269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv24439]) (by decide +kernel)
def pv293269 : PrimeValue := ⟨293269, pr293269⟩
private theorem pr293311 : PrimeCertificate 293311 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv3259]) (by decide +kernel)
def pv293311 : PrimeValue := ⟨293311, pr293311⟩
private theorem pr293329 : PrimeCertificate 293329 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv97]) (by decide +kernel)
def pv293329 : PrimeValue := ⟨293329, pr293329⟩
private theorem pr293339 : PrimeCertificate 293339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv146669]) (by decide +kernel)
def pv293339 : PrimeValue := ⟨293339, pr293339⟩
private theorem pr293357 : PrimeCertificate 293357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv10477]) (by decide +kernel)
def pv293357 : PrimeValue := ⟨293357, pr293357⟩
private theorem pr293431 : PrimeCertificate 293431 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv9781]) (by decide +kernel)
def pv293431 : PrimeValue := ⟨293431, pr293431⟩
private theorem pr293459 : PrimeCertificate 293459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13339]) (by decide +kernel)
def pv293459 : PrimeValue := ⟨293459, pr293459⟩
private theorem pr293467 : PrimeCertificate 293467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv59,pv829]) (by decide +kernel)
def pv293467 : PrimeValue := ⟨293467, pr293467⟩
private theorem pr293543 : PrimeCertificate 293543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv317,pv463]) (by decide +kernel)
def pv293543 : PrimeValue := ⟨293543, pr293543⟩
private theorem pr293617 : PrimeCertificate 293617 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2039]) (by decide +kernel)
def pv293617 : PrimeValue := ⟨293617, pr293617⟩
private theorem pr293633 : PrimeCertificate 293633 :=
  certifyPrime (q := pv5) (ls := [pv2,pv31,pv37]) (by decide +kernel)
def pv293633 : PrimeValue := ⟨293633, pr293633⟩
private theorem pr293651 : PrimeCertificate 293651 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv839]) (by decide +kernel)
def pv293651 : PrimeValue := ⟨293651, pr293651⟩
private theorem pr293677 : PrimeCertificate 293677 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv24473]) (by decide +kernel)
def pv293677 : PrimeValue := ⟨293677, pr293677⟩
private theorem pr293681 : PrimeCertificate 293681 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv3671]) (by decide +kernel)
def pv293681 : PrimeValue := ⟨293681, pr293681⟩
private theorem pr293701 : PrimeCertificate 293701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv89]) (by decide +kernel)
def pv293701 : PrimeValue := ⟨293701, pr293701⟩
private theorem pr293729 : PrimeCertificate 293729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv67,pv137]) (by decide +kernel)
def pv293729 : PrimeValue := ⟨293729, pr293729⟩
private theorem pr293767 : PrimeCertificate 293767 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv4451]) (by decide +kernel)
def pv293767 : PrimeValue := ⟨293767, pr293767⟩
private theorem pr293773 : PrimeCertificate 293773 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv24481]) (by decide +kernel)
def pv293773 : PrimeValue := ⟨293773, pr293773⟩
private theorem pr293827 : PrimeCertificate 293827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv3767]) (by decide +kernel)
def pv293827 : PrimeValue := ⟨293827, pr293827⟩
private theorem pr293831 : PrimeCertificate 293831 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv29383]) (by decide +kernel)
def pv293831 : PrimeValue := ⟨293831, pr293831⟩
private theorem pr293893 : PrimeCertificate 293893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv1289]) (by decide +kernel)
def pv293893 : PrimeValue := ⟨293893, pr293893⟩
private theorem pr293989 : PrimeCertificate 293989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv24499]) (by decide +kernel)
def pv293989 : PrimeValue := ⟨293989, pr293989⟩
private theorem pr293999 : PrimeCertificate 293999 :=
  certifyPrime (q := pv23) (ls := [pv2,pv17,pv8647]) (by decide +kernel)
def pv293999 : PrimeValue := ⟨293999, pr293999⟩
private theorem pr294001 : PrimeCertificate 294001 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv294001 : PrimeValue := ⟨294001, pr294001⟩
private theorem pr294043 : PrimeCertificate 294043 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv7001]) (by decide +kernel)
def pv294043 : PrimeValue := ⟨294043, pr294043⟩
private theorem pr294053 : PrimeCertificate 294053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv41,pv163]) (by decide +kernel)
def pv294053 : PrimeValue := ⟨294053, pr294053⟩
private theorem pr294059 : PrimeCertificate 294059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv147029]) (by decide +kernel)
def pv294059 : PrimeValue := ⟨294059, pr294059⟩
private theorem pr294067 : PrimeCertificate 294067 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv31]) (by decide +kernel)
def pv294067 : PrimeValue := ⟨294067, pr294067⟩
private theorem pr294103 : PrimeCertificate 294103 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv16339]) (by decide +kernel)
def pv294103 : PrimeValue := ⟨294103, pr294103⟩
private theorem pr294127 : PrimeCertificate 294127 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv47,pv149]) (by decide +kernel)
def pv294127 : PrimeValue := ⟨294127, pr294127⟩
private theorem pr294131 : PrimeCertificate 294131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv67,pv439]) (by decide +kernel)
def pv294131 : PrimeValue := ⟨294131, pr294131⟩
private theorem pr294149 : PrimeCertificate 294149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv151,pv487]) (by decide +kernel)
def pv294149 : PrimeValue := ⟨294149, pr294149⟩
private theorem pr294157 : PrimeCertificate 294157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv8171]) (by decide +kernel)
def pv294157 : PrimeValue := ⟨294157, pr294157⟩
private theorem pr294169 : PrimeCertificate 294169 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv17,pv103]) (by decide +kernel)
def pv294169 : PrimeValue := ⟨294169, pr294169⟩
private theorem pr294179 : PrimeCertificate 294179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv147089]) (by decide +kernel)
def pv294179 : PrimeValue := ⟨294179, pr294179⟩
private theorem pr294181 : PrimeCertificate 294181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv4903]) (by decide +kernel)
def pv294181 : PrimeValue := ⟨294181, pr294181⟩
private theorem pr294199 : PrimeCertificate 294199 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv49033]) (by decide +kernel)
def pv294199 : PrimeValue := ⟨294199, pr294199⟩
private theorem pr294227 : PrimeCertificate 294227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv131,pv1123]) (by decide +kernel)
def pv294227 : PrimeValue := ⟨294227, pr294227⟩
private theorem pr294251 : PrimeCertificate 294251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv107]) (by decide +kernel)
def pv294251 : PrimeValue := ⟨294251, pr294251⟩
private theorem pr294269 : PrimeCertificate 294269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv5659]) (by decide +kernel)
def pv294269 : PrimeValue := ⟨294269, pr294269⟩
private theorem pr294289 : PrimeCertificate 294289 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv6131]) (by decide +kernel)
def pv294289 : PrimeValue := ⟨294289, pr294289⟩
private theorem pr294293 : PrimeCertificate 294293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv43,pv59]) (by decide +kernel)
def pv294293 : PrimeValue := ⟨294293, pr294293⟩
private theorem pr294311 : PrimeCertificate 294311 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv19,pv1549]) (by decide +kernel)
def pv294311 : PrimeValue := ⟨294311, pr294311⟩
private theorem pr294319 : PrimeCertificate 294319 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv83,pv197]) (by decide +kernel)
def pv294319 : PrimeValue := ⟨294319, pr294319⟩
private theorem pr294337 : PrimeCertificate 294337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv73]) (by decide +kernel)
def pv294337 : PrimeValue := ⟨294337, pr294337⟩
private theorem pr294341 : PrimeCertificate 294341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv14717]) (by decide +kernel)
def pv294341 : PrimeValue := ⟨294341, pr294341⟩
private theorem pr294383 : PrimeCertificate 294383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv13381]) (by decide +kernel)
def pv294383 : PrimeValue := ⟨294383, pr294383⟩
private theorem pr294391 : PrimeCertificate 294391 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv3271]) (by decide +kernel)
def pv294391 : PrimeValue := ⟨294391, pr294391⟩
private theorem pr294397 : PrimeCertificate 294397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv24533]) (by decide +kernel)
def pv294397 : PrimeValue := ⟨294397, pr294397⟩
private theorem pr294403 : PrimeCertificate 294403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv139,pv353]) (by decide +kernel)
def pv294403 : PrimeValue := ⟨294403, pr294403⟩
private theorem pr294431 : PrimeCertificate 294431 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv29443]) (by decide +kernel)
def pv294431 : PrimeValue := ⟨294431, pr294431⟩
private theorem pr294467 : PrimeCertificate 294467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv5077]) (by decide +kernel)
def pv294467 : PrimeValue := ⟨294467, pr294467⟩
private theorem pr294499 : PrimeCertificate 294499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv16361]) (by decide +kernel)
def pv294499 : PrimeValue := ⟨294499, pr294499⟩
private theorem pr294509 : PrimeCertificate 294509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv61,pv71]) (by decide +kernel)
def pv294509 : PrimeValue := ⟨294509, pr294509⟩
private theorem pr294529 : PrimeCertificate 294529 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv13,pv59]) (by decide +kernel)
def pv294529 : PrimeValue := ⟨294529, pr294529⟩
private theorem pr294551 : PrimeCertificate 294551 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv43,pv137]) (by decide +kernel)
def pv294551 : PrimeValue := ⟨294551, pr294551⟩
private theorem pr294773 : PrimeCertificate 294773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73693]) (by decide +kernel)
def pv294773 : PrimeValue := ⟨294773, pr294773⟩
private theorem pr294787 : PrimeCertificate 294787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53,pv103]) (by decide +kernel)
def pv294787 : PrimeValue := ⟨294787, pr294787⟩
private theorem pr294793 : PrimeCertificate 294793 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv71,pv173]) (by decide +kernel)
def pv294793 : PrimeValue := ⟨294793, pr294793⟩
private theorem pr294803 : PrimeCertificate 294803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv147401]) (by decide +kernel)
def pv294803 : PrimeValue := ⟨294803, pr294803⟩
private theorem pr294821 : PrimeCertificate 294821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv14741]) (by decide +kernel)
def pv294821 : PrimeValue := ⟨294821, pr294821⟩
private theorem pr294829 : PrimeCertificate 294829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv79,pv311]) (by decide +kernel)
def pv294829 : PrimeValue := ⟨294829, pr294829⟩
private theorem pr294869 : PrimeCertificate 294869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv10531]) (by decide +kernel)
def pv294869 : PrimeValue := ⟨294869, pr294869⟩
private theorem pr294887 : PrimeCertificate 294887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv283,pv521]) (by decide +kernel)
def pv294887 : PrimeValue := ⟨294887, pr294887⟩
private theorem pr294919 : PrimeCertificate 294919 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv19,pv199]) (by decide +kernel)
def pv294919 : PrimeValue := ⟨294919, pr294919⟩
private theorem pr294923 : PrimeCertificate 294923 :=
  certifyPrime (q := pv5) (ls := [pv2,pv167,pv883]) (by decide +kernel)
def pv294923 : PrimeValue := ⟨294923, pr294923⟩
private theorem pr294949 : PrimeCertificate 294949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv2731]) (by decide +kernel)
def pv294949 : PrimeValue := ⟨294949, pr294949⟩
private theorem pr294991 : PrimeCertificate 294991 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv9833]) (by decide +kernel)
def pv294991 : PrimeValue := ⟨294991, pr294991⟩
private theorem pr294997 : PrimeCertificate 294997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv31,pv61]) (by decide +kernel)
def pv294997 : PrimeValue := ⟨294997, pr294997⟩
private theorem pr295033 : PrimeCertificate 295033 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv19,pv647]) (by decide +kernel)
def pv295033 : PrimeValue := ⟨295033, pr295033⟩
private theorem pr295049 : PrimeCertificate 295049 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv2837]) (by decide +kernel)
def pv295049 : PrimeValue := ⟨295049, pr295049⟩
private theorem pr295123 : PrimeCertificate 295123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv101,pv487]) (by decide +kernel)
def pv295123 : PrimeValue := ⟨295123, pr295123⟩
private theorem pr295153 : PrimeCertificate 295153 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv11,pv13,pv43]) (by decide +kernel)
def pv295153 : PrimeValue := ⟨295153, pr295153⟩
private theorem pr295187 : PrimeCertificate 295187 :=
  certifyPrime (q := pv5) (ls := [pv2,pv37,pv3989]) (by decide +kernel)
def pv295187 : PrimeValue := ⟨295187, pr295187⟩
private theorem pr295199 : PrimeCertificate 295199 :=
  certifyPrime (q := pv7) (ls := [pv2,pv103,pv1433]) (by decide +kernel)
def pv295199 : PrimeValue := ⟨295199, pr295199⟩
private theorem pr295219 : PrimeCertificate 295219 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv71]) (by decide +kernel)
def pv295219 : PrimeValue := ⟨295219, pr295219⟩
private theorem pr295237 : PrimeCertificate 295237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv59,pv139]) (by decide +kernel)
def pv295237 : PrimeValue := ⟨295237, pr295237⟩
private theorem pr295247 : PrimeCertificate 295247 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv21089]) (by decide +kernel)
def pv295247 : PrimeValue := ⟨295247, pr295247⟩
private theorem pr295271 : PrimeCertificate 295271 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv29527]) (by decide +kernel)
def pv295271 : PrimeValue := ⟨295271, pr295271⟩
private theorem pr295283 : PrimeCertificate 295283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv41,pv277]) (by decide +kernel)
def pv295283 : PrimeValue := ⟨295283, pr295283⟩
private theorem pr295291 : PrimeCertificate 295291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv193]) (by decide +kernel)
def pv295291 : PrimeValue := ⟨295291, pr295291⟩
private theorem pr295313 : PrimeCertificate 295313 :=
  certifyPrime (q := pv3) (ls := [pv2,pv18457]) (by decide +kernel)
def pv295313 : PrimeValue := ⟨295313, pr295313⟩
private theorem pr295333 : PrimeCertificate 295333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv24611]) (by decide +kernel)
def pv295333 : PrimeValue := ⟨295333, pr295333⟩
private theorem pr295357 : PrimeCertificate 295357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv151,pv163]) (by decide +kernel)
def pv295357 : PrimeValue := ⟨295357, pr295357⟩
private theorem pr295387 : PrimeCertificate 295387 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv541]) (by decide +kernel)
def pv295387 : PrimeValue := ⟨295387, pr295387⟩
private theorem pr295411 : PrimeCertificate 295411 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv43,pv229]) (by decide +kernel)
def pv295411 : PrimeValue := ⟨295411, pr295411⟩
private theorem pr295433 : PrimeCertificate 295433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv36929]) (by decide +kernel)
def pv295433 : PrimeValue := ⟨295433, pr295433⟩
private theorem pr295439 : PrimeCertificate 295439 :=
  certifyPrime (q := pv23) (ls := [pv2,pv11,pv13,pv1033]) (by decide +kernel)
def pv295439 : PrimeValue := ⟨295439, pr295439⟩
private theorem pr295441 : PrimeCertificate 295441 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv1231]) (by decide +kernel)
def pv295441 : PrimeValue := ⟨295441, pr295441⟩
private theorem pr295513 : PrimeCertificate 295513 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv1759]) (by decide +kernel)
def pv295513 : PrimeValue := ⟨295513, pr295513⟩
private theorem pr295553 : PrimeCertificate 295553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2309]) (by decide +kernel)
def pv295553 : PrimeValue := ⟨295553, pr295553⟩
private theorem pr295601 : PrimeCertificate 295601 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv739]) (by decide +kernel)
def pv295601 : PrimeValue := ⟨295601, pr295601⟩
private theorem pr295663 : PrimeCertificate 295663 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv49277]) (by decide +kernel)
def pv295663 : PrimeValue := ⟨295663, pr295663⟩
private theorem pr295693 : PrimeCertificate 295693 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv41,pv601]) (by decide +kernel)
def pv295693 : PrimeValue := ⟨295693, pr295693⟩
private theorem pr295699 : PrimeCertificate 295699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv17,pv223]) (by decide +kernel)
def pv295699 : PrimeValue := ⟨295699, pr295699⟩
private theorem pr295703 : PrimeCertificate 295703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv13441]) (by decide +kernel)
def pv295703 : PrimeValue := ⟨295703, pr295703⟩
private theorem pr295727 : PrimeCertificate 295727 :=
  certifyPrime (q := pv5) (ls := [pv2,pv147863]) (by decide +kernel)
def pv295727 : PrimeValue := ⟨295727, pr295727⟩
private theorem pr295787 : PrimeCertificate 295787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71,pv2083]) (by decide +kernel)
def pv295787 : PrimeValue := ⟨295787, pr295787⟩
private theorem pr295819 : PrimeCertificate 295819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv1049]) (by decide +kernel)
def pv295819 : PrimeValue := ⟨295819, pr295819⟩
private theorem pr295831 : PrimeCertificate 295831 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv19,pv173]) (by decide +kernel)
def pv295831 : PrimeValue := ⟨295831, pr295831⟩
private theorem pr295837 : PrimeCertificate 295837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv89,pv277]) (by decide +kernel)
def pv295837 : PrimeValue := ⟨295837, pr295837⟩
private theorem pr295871 : PrimeCertificate 295871 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv29587]) (by decide +kernel)
def pv295871 : PrimeValue := ⟨295871, pr295871⟩
private theorem pr295903 : PrimeCertificate 295903 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv967]) (by decide +kernel)
def pv295903 : PrimeValue := ⟨295903, pr295903⟩
private theorem pr295909 : PrimeCertificate 295909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv24659]) (by decide +kernel)
def pv295909 : PrimeValue := ⟨295909, pr295909⟩
private theorem pr295943 : PrimeCertificate 295943 :=
  certifyPrime (q := pv5) (ls := [pv2,pv73,pv2027]) (by decide +kernel)
def pv295943 : PrimeValue := ⟨295943, pr295943⟩
private theorem pr296011 : PrimeCertificate 296011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv13,pv23]) (by decide +kernel)
def pv296011 : PrimeValue := ⟨296011, pr296011⟩
private theorem pr296017 : PrimeCertificate 296017 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv881]) (by decide +kernel)
def pv296017 : PrimeValue := ⟨296017, pr296017⟩
private theorem pr296047 : PrimeCertificate 296047 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv16447]) (by decide +kernel)
def pv296047 : PrimeValue := ⟨296047, pr296047⟩
private theorem pr296083 : PrimeCertificate 296083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5483]) (by decide +kernel)
def pv296083 : PrimeValue := ⟨296083, pr296083⟩
private theorem pr296099 : PrimeCertificate 296099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv43,pv313]) (by decide +kernel)
def pv296099 : PrimeValue := ⟨296099, pr296099⟩
private theorem pr296117 : PrimeCertificate 296117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv181,pv409]) (by decide +kernel)
def pv296117 : PrimeValue := ⟨296117, pr296117⟩
private theorem pr296129 : PrimeCertificate 296129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv661]) (by decide +kernel)
def pv296129 : PrimeValue := ⟨296129, pr296129⟩
private theorem pr296137 : PrimeCertificate 296137 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv457]) (by decide +kernel)
def pv296137 : PrimeValue := ⟨296137, pr296137⟩
private theorem pr296183 : PrimeCertificate 296183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv148091]) (by decide +kernel)
def pv296183 : PrimeValue := ⟨296183, pr296183⟩
private theorem pr296237 : PrimeCertificate 296237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv2389]) (by decide +kernel)
def pv296237 : PrimeValue := ⟨296237, pr296237⟩
private theorem pr296243 : PrimeCertificate 296243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv8713]) (by decide +kernel)
def pv296243 : PrimeValue := ⟨296243, pr296243⟩
private theorem pr296249 : PrimeCertificate 296249 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv1949]) (by decide +kernel)
def pv296249 : PrimeValue := ⟨296249, pr296249⟩
private theorem pr296269 : PrimeCertificate 296269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv3527]) (by decide +kernel)
def pv296269 : PrimeValue := ⟨296269, pr296269⟩
private theorem pr296273 : PrimeCertificate 296273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv18517]) (by decide +kernel)
def pv296273 : PrimeValue := ⟨296273, pr296273⟩
private theorem pr296287 : PrimeCertificate 296287 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv23,pv113]) (by decide +kernel)
def pv296287 : PrimeValue := ⟨296287, pr296287⟩
private theorem pr296299 : PrimeCertificate 296299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv59]) (by decide +kernel)
def pv296299 : PrimeValue := ⟨296299, pr296299⟩
private theorem pr296347 : PrimeCertificate 296347 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv49391]) (by decide +kernel)
def pv296347 : PrimeValue := ⟨296347, pr296347⟩
private theorem pr296363 : PrimeCertificate 296363 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv19,pv709]) (by decide +kernel)
def pv296363 : PrimeValue := ⟨296363, pr296363⟩
private theorem pr296377 : PrimeCertificate 296377 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv53,pv233]) (by decide +kernel)
def pv296377 : PrimeValue := ⟨296377, pr296377⟩
private theorem pr296437 : PrimeCertificate 296437 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv7,pv3529]) (by decide +kernel)
def pv296437 : PrimeValue := ⟨296437, pr296437⟩
private theorem pr296473 : PrimeCertificate 296473 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv11,pv1123]) (by decide +kernel)
def pv296473 : PrimeValue := ⟨296473, pr296473⟩
private theorem pr296563 : PrimeCertificate 296563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv23,pv307]) (by decide +kernel)
def pv296563 : PrimeValue := ⟨296563, pr296563⟩
private theorem pr296579 : PrimeCertificate 296579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv257,pv577]) (by decide +kernel)
def pv296579 : PrimeValue := ⟨296579, pr296579⟩
private theorem pr296581 : PrimeCertificate 296581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv4943]) (by decide +kernel)
def pv296581 : PrimeValue := ⟨296581, pr296581⟩
private theorem pr296587 : PrimeCertificate 296587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv16477]) (by decide +kernel)
def pv296587 : PrimeValue := ⟨296587, pr296587⟩
private theorem pr296591 : PrimeCertificate 296591 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv19,pv223]) (by decide +kernel)
def pv296591 : PrimeValue := ⟨296591, pr296591⟩
private theorem pr296683 : PrimeCertificate 296683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv197,pv251]) (by decide +kernel)
def pv296683 : PrimeValue := ⟨296683, pr296683⟩
private theorem pr296693 : PrimeCertificate 296693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv613]) (by decide +kernel)
def pv296693 : PrimeValue := ⟨296693, pr296693⟩
private theorem pr296713 : PrimeCertificate 296713 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv317]) (by decide +kernel)
def pv296713 : PrimeValue := ⟨296713, pr296713⟩
private theorem pr296741 : PrimeCertificate 296741 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv37,pv401]) (by decide +kernel)
def pv296741 : PrimeValue := ⟨296741, pr296741⟩
private theorem pr296749 : PrimeCertificate 296749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv8243]) (by decide +kernel)
def pv296749 : PrimeValue := ⟨296749, pr296749⟩
private theorem pr296753 : PrimeCertificate 296753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv1091]) (by decide +kernel)
def pv296753 : PrimeValue := ⟨296753, pr296753⟩
private theorem pr296771 : PrimeCertificate 296771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv59,pv503]) (by decide +kernel)
def pv296771 : PrimeValue := ⟨296771, pr296771⟩
private theorem pr296797 : PrimeCertificate 296797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv24733]) (by decide +kernel)
def pv296797 : PrimeValue := ⟨296797, pr296797⟩
private theorem pr296801 : PrimeCertificate 296801 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv53]) (by decide +kernel)
def pv296801 : PrimeValue := ⟨296801, pr296801⟩
private theorem pr296819 : PrimeCertificate 296819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv73,pv107]) (by decide +kernel)
def pv296819 : PrimeValue := ⟨296819, pr296819⟩
private theorem pr296827 : PrimeCertificate 296827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61,pv811]) (by decide +kernel)
def pv296827 : PrimeValue := ⟨296827, pr296827⟩
private theorem pr296831 : PrimeCertificate 296831 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv29683]) (by decide +kernel)
def pv296831 : PrimeValue := ⟨296831, pr296831⟩
private theorem pr296909 : PrimeCertificate 296909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv199,pv373]) (by decide +kernel)
def pv296909 : PrimeValue := ⟨296909, pr296909⟩
private theorem pr296911 : PrimeCertificate 296911 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv3299]) (by decide +kernel)
def pv296911 : PrimeValue := ⟨296911, pr296911⟩
private theorem pr296929 : PrimeCertificate 296929 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1031]) (by decide +kernel)
def pv296929 : PrimeValue := ⟨296929, pr296929⟩
private theorem pr296971 : PrimeCertificate 296971 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv19,pv521]) (by decide +kernel)
def pv296971 : PrimeValue := ⟨296971, pr296971⟩
private theorem pr296983 : PrimeCertificate 296983 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv2357]) (by decide +kernel)
def pv296983 : PrimeValue := ⟨296983, pr296983⟩
private theorem pr297023 : PrimeCertificate 297023 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv23,pv587]) (by decide +kernel)
def pv297023 : PrimeValue := ⟨297023, pr297023⟩
private theorem pr297049 : PrimeCertificate 297049 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv12377]) (by decide +kernel)
def pv297049 : PrimeValue := ⟨297049, pr297049⟩
private theorem pr297067 : PrimeCertificate 297067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv643]) (by decide +kernel)
def pv297067 : PrimeValue := ⟨297067, pr297067⟩
private theorem pr297079 : PrimeCertificate 297079 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv67,pv739]) (by decide +kernel)
def pv297079 : PrimeValue := ⟨297079, pr297079⟩
private theorem pr297083 : PrimeCertificate 297083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89,pv1669]) (by decide +kernel)
def pv297083 : PrimeValue := ⟨297083, pr297083⟩
private theorem pr297097 : PrimeCertificate 297097 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv12379]) (by decide +kernel)
def pv297097 : PrimeValue := ⟨297097, pr297097⟩
private theorem pr297113 : PrimeCertificate 297113 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37139]) (by decide +kernel)
def pv297113 : PrimeValue := ⟨297113, pr297113⟩
private theorem pr297151 : PrimeCertificate 297151 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv283]) (by decide +kernel)
def pv297151 : PrimeValue := ⟨297151, pr297151⟩
private theorem pr297233 : PrimeCertificate 297233 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv1429]) (by decide +kernel)
def pv297233 : PrimeValue := ⟨297233, pr297233⟩
private theorem pr297251 : PrimeCertificate 297251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29,pv41]) (by decide +kernel)
def pv297251 : PrimeValue := ⟨297251, pr297251⟩
private theorem pr297257 : PrimeCertificate 297257 :=
  certifyPrime (q := pv3) (ls := [pv2,pv73,pv509]) (by decide +kernel)
def pv297257 : PrimeValue := ⟨297257, pr297257⟩
private theorem pr297371 : PrimeCertificate 297371 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv131,pv227]) (by decide +kernel)
def pv297371 : PrimeValue := ⟨297371, pr297371⟩
private theorem pr297403 : PrimeCertificate 297403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv73,pv97]) (by decide +kernel)
def pv297403 : PrimeValue := ⟨297403, pr297403⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
