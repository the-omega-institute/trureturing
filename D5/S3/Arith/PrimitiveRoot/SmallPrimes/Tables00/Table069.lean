/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table069
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table069.pv214883
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table007
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table009
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table015
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table040
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table041

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr214883 : Nat.Prime 214883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv107441]) (by decide +kernel)
def pv214883 : PrimeValue := ⟨214883, pr214883⟩
private theorem pr214913 : Nat.Prime 214913 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv23,pv73]) (by decide +kernel)
def pv214913 : PrimeValue := ⟨214913, pr214913⟩
private theorem pr214939 : Nat.Prime 214939 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11941]) (by decide +kernel)
def pv214939 : PrimeValue := ⟨214939, pr214939⟩
private theorem pr214943 : Nat.Prime 214943 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv13,pv1181]) (by decide +kernel)
def pv214943 : PrimeValue := ⟨214943, pr214943⟩
private theorem pr214967 : Nat.Prime 214967 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv5657]) (by decide +kernel)
def pv214967 : PrimeValue := ⟨214967, pr214967⟩
private theorem pr214993 : Nat.Prime 214993 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1493]) (by decide +kernel)
def pv214993 : PrimeValue := ⟨214993, pr214993⟩
private theorem pr215063 : Nat.Prime 215063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv293,pv367]) (by decide +kernel)
def pv215063 : PrimeValue := ⟨215063, pr215063⟩
private theorem pr215077 : Nat.Prime 215077 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17923]) (by decide +kernel)
def pv215077 : PrimeValue := ⟨215077, pr215077⟩
private theorem pr215087 : Nat.Prime 215087 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv41,pv43,pv61]) (by decide +kernel)
def pv215087 : PrimeValue := ⟨215087, pr215087⟩
private theorem pr215123 : Nat.Prime 215123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv3709]) (by decide +kernel)
def pv215123 : PrimeValue := ⟨215123, pr215123⟩
private theorem pr215141 : Nat.Prime 215141 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv31,pv347]) (by decide +kernel)
def pv215141 : PrimeValue := ⟨215141, pr215141⟩
private theorem pr215153 : Nat.Prime 215153 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv17,pv113]) (by decide +kernel)
def pv215153 : PrimeValue := ⟨215153, pr215153⟩
private theorem pr215161 : Nat.Prime 215161 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv11,pv163]) (by decide +kernel)
def pv215161 : PrimeValue := ⟨215161, pr215161⟩
private theorem pr215179 : Nat.Prime 215179 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv35863]) (by decide +kernel)
def pv215179 : PrimeValue := ⟨215179, pr215179⟩
private theorem pr215183 : Nat.Prime 215183 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv9781]) (by decide +kernel)
def pv215183 : PrimeValue := ⟨215183, pr215183⟩
private theorem pr215197 : Nat.Prime 215197 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv79,pv227]) (by decide +kernel)
def pv215197 : PrimeValue := ⟨215197, pr215197⟩
private theorem pr215239 : Nat.Prime 215239 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29,pv1237]) (by decide +kernel)
def pv215239 : PrimeValue := ⟨215239, pr215239⟩
private theorem pr215249 : Nat.Prime 215249 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv1223]) (by decide +kernel)
def pv215249 : PrimeValue := ⟨215249, pr215249⟩
private theorem pr215261 : Nat.Prime 215261 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv47,pv229]) (by decide +kernel)
def pv215261 : PrimeValue := ⟨215261, pr215261⟩
private theorem pr215297 : Nat.Prime 215297 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29]) (by decide +kernel)
def pv215297 : PrimeValue := ⟨215297, pr215297⟩
private theorem pr215309 : Nat.Prime 215309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv2833]) (by decide +kernel)
def pv215309 : PrimeValue := ⟨215309, pr215309⟩
private theorem pr215317 : Nat.Prime 215317 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5981]) (by decide +kernel)
def pv215317 : PrimeValue := ⟨215317, pr215317⟩
private theorem pr215329 : Nat.Prime 215329 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv2243]) (by decide +kernel)
def pv215329 : PrimeValue := ⟨215329, pr215329⟩
private theorem pr215351 : Nat.Prime 215351 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv59,pv73]) (by decide +kernel)
def pv215351 : PrimeValue := ⟨215351, pr215351⟩
private theorem pr215353 : Nat.Prime 215353 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv997]) (by decide +kernel)
def pv215353 : PrimeValue := ⟨215353, pr215353⟩
private theorem pr215359 : Nat.Prime 215359 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv13,pv251]) (by decide +kernel)
def pv215359 : PrimeValue := ⟨215359, pr215359⟩
private theorem pr215381 : Nat.Prime 215381 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv89]) (by decide +kernel)
def pv215381 : PrimeValue := ⟨215381, pr215381⟩
private theorem pr215389 : Nat.Prime 215389 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv193]) (by decide +kernel)
def pv215389 : PrimeValue := ⟨215389, pr215389⟩
private theorem pr215393 : Nat.Prime 215393 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv53,pv127]) (by decide +kernel)
def pv215393 : PrimeValue := ⟨215393, pr215393⟩
private theorem pr215399 : Nat.Prime 215399 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv107699]) (by decide +kernel)
def pv215399 : PrimeValue := ⟨215399, pr215399⟩
private theorem pr215417 : Nat.Prime 215417 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv26927]) (by decide +kernel)
def pv215417 : PrimeValue := ⟨215417, pr215417⟩
private theorem pr215443 : Nat.Prime 215443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11969]) (by decide +kernel)
def pv215443 : PrimeValue := ⟨215443, pr215443⟩
private theorem pr215447 : Nat.Prime 215447 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv11,pv1399]) (by decide +kernel)
def pv215447 : PrimeValue := ⟨215447, pr215447⟩
private theorem pr215459 : Nat.Prime 215459 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv17,pv6337]) (by decide +kernel)
def pv215459 : PrimeValue := ⟨215459, pr215459⟩
private theorem pr215461 : Nat.Prime 215461 :=
  checkPrime_prime (q := pv59) (ls := [pv2,pv3,pv5,pv7,pv19]) (by decide +kernel)
def pv215461 : PrimeValue := ⟨215461, pr215461⟩
private theorem pr215471 : Nat.Prime 215471 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv29,pv743]) (by decide +kernel)
def pv215471 : PrimeValue := ⟨215471, pr215471⟩
private theorem pr215483 : Nat.Prime 215483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv107741]) (by decide +kernel)
def pv215483 : PrimeValue := ⟨215483, pr215483⟩
private theorem pr215497 : Nat.Prime 215497 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv41,pv73]) (by decide +kernel)
def pv215497 : PrimeValue := ⟨215497, pr215497⟩
private theorem pr215503 : Nat.Prime 215503 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv733]) (by decide +kernel)
def pv215503 : PrimeValue := ⟨215503, pr215503⟩
private theorem pr215507 : Nat.Prime 215507 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv277,pv389]) (by decide +kernel)
def pv215507 : PrimeValue := ⟨215507, pr215507⟩
private theorem pr215521 : Nat.Prime 215521 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv449]) (by decide +kernel)
def pv215521 : PrimeValue := ⟨215521, pr215521⟩
private theorem pr215531 : Nat.Prime 215531 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv3079]) (by decide +kernel)
def pv215531 : PrimeValue := ⟨215531, pr215531⟩
private theorem pr215573 : Nat.Prime 215573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv7699]) (by decide +kernel)
def pv215573 : PrimeValue := ⟨215573, pr215573⟩
private theorem pr215617 : Nat.Prime 215617 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv1123]) (by decide +kernel)
def pv215617 : PrimeValue := ⟨215617, pr215617⟩
private theorem pr215659 : Nat.Prime 215659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11981]) (by decide +kernel)
def pv215659 : PrimeValue := ⟨215659, pr215659⟩
private theorem pr215681 : Nat.Prime 215681 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv337]) (by decide +kernel)
def pv215681 : PrimeValue := ⟨215681, pr215681⟩
private theorem pr215687 : Nat.Prime 215687 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv107843]) (by decide +kernel)
def pv215687 : PrimeValue := ⟨215687, pr215687⟩
private theorem pr215689 : Nat.Prime 215689 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv19,pv43]) (by decide +kernel)
def pv215689 : PrimeValue := ⟨215689, pr215689⟩
private theorem pr215723 : Nat.Prime 215723 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv8297]) (by decide +kernel)
def pv215723 : PrimeValue := ⟨215723, pr215723⟩
private theorem pr215737 : Nat.Prime 215737 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv89,pv101]) (by decide +kernel)
def pv215737 : PrimeValue := ⟨215737, pr215737⟩
private theorem pr215767 : Nat.Prime 215767 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11987]) (by decide +kernel)
def pv215767 : PrimeValue := ⟨215767, pr215767⟩
private theorem pr215771 : Nat.Prime 215771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv21577]) (by decide +kernel)
def pv215771 : PrimeValue := ⟨215771, pr215771⟩
private theorem pr215797 : Nat.Prime 215797 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv367]) (by decide +kernel)
def pv215797 : PrimeValue := ⟨215797, pr215797⟩
private theorem pr215801 : Nat.Prime 215801 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv83]) (by decide +kernel)
def pv215801 : PrimeValue := ⟨215801, pr215801⟩
private theorem pr215827 : Nat.Prime 215827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv2767]) (by decide +kernel)
def pv215827 : PrimeValue := ⟨215827, pr215827⟩
private theorem pr215833 : Nat.Prime 215833 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv23]) (by decide +kernel)
def pv215833 : PrimeValue := ⟨215833, pr215833⟩
private theorem pr215843 : Nat.Prime 215843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv9811]) (by decide +kernel)
def pv215843 : PrimeValue := ⟨215843, pr215843⟩
private theorem pr215863 : Nat.Prime 215863 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv35977]) (by decide +kernel)
def pv215863 : PrimeValue := ⟨215863, pr215863⟩
private theorem pr215893 : Nat.Prime 215893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1999]) (by decide +kernel)
def pv215893 : PrimeValue := ⟨215893, pr215893⟩
private theorem pr215909 : Nat.Prime 215909 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv7,pv11,pv701]) (by decide +kernel)
def pv215909 : PrimeValue := ⟨215909, pr215909⟩
private theorem pr215921 : Nat.Prime 215921 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv2699]) (by decide +kernel)
def pv215921 : PrimeValue := ⟨215921, pr215921⟩
private theorem pr215927 : Nat.Prime 215927 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv107,pv1009]) (by decide +kernel)
def pv215927 : PrimeValue := ⟨215927, pr215927⟩
private theorem pr215939 : Nat.Prime 215939 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv101,pv1069]) (by decide +kernel)
def pv215939 : PrimeValue := ⟨215939, pr215939⟩
private theorem pr215981 : Nat.Prime 215981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv10799]) (by decide +kernel)
def pv215981 : PrimeValue := ⟨215981, pr215981⟩
private theorem pr215983 : Nat.Prime 215983 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv71]) (by decide +kernel)
def pv215983 : PrimeValue := ⟨215983, pr215983⟩
private theorem pr216023 : Nat.Prime 216023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv108011]) (by decide +kernel)
def pv216023 : PrimeValue := ⟨216023, pr216023⟩
private theorem pr216061 : Nat.Prime 216061 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv13,pv277]) (by decide +kernel)
def pv216061 : PrimeValue := ⟨216061, pr216061⟩
private theorem pr216071 : Nat.Prime 216071 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv17,pv31,pv41]) (by decide +kernel)
def pv216071 : PrimeValue := ⟨216071, pr216071⟩
private theorem pr216103 : Nat.Prime 216103 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv36017]) (by decide +kernel)
def pv216103 : PrimeValue := ⟨216103, pr216103⟩
private theorem pr216107 : Nat.Prime 216107 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv19,pv47]) (by decide +kernel)
def pv216107 : PrimeValue := ⟨216107, pr216107⟩
private theorem pr216113 : Nat.Prime 216113 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv1039]) (by decide +kernel)
def pv216113 : PrimeValue := ⟨216113, pr216113⟩
private theorem pr216119 : Nat.Prime 216119 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv43,pv359]) (by decide +kernel)
def pv216119 : PrimeValue := ⟨216119, pr216119⟩
private theorem pr216127 : Nat.Prime 216127 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv12007]) (by decide +kernel)
def pv216127 : PrimeValue := ⟨216127, pr216127⟩
private theorem pr216133 : Nat.Prime 216133 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv31,pv83]) (by decide +kernel)
def pv216133 : PrimeValue := ⟨216133, pr216133⟩
private theorem pr216149 : Nat.Prime 216149 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv54037]) (by decide +kernel)
def pv216149 : PrimeValue := ⟨216149, pr216149⟩
private theorem pr216157 : Nat.Prime 216157 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv18013]) (by decide +kernel)
def pv216157 : PrimeValue := ⟨216157, pr216157⟩
private theorem pr216173 : Nat.Prime 216173 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv17]) (by decide +kernel)
def pv216173 : PrimeValue := ⟨216173, pr216173⟩
private theorem pr216179 : Nat.Prime 216179 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv108089]) (by decide +kernel)
def pv216179 : PrimeValue := ⟨216179, pr216179⟩
private theorem pr216211 : Nat.Prime 216211 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv7207]) (by decide +kernel)
def pv216211 : PrimeValue := ⟨216211, pr216211⟩
private theorem pr216217 : Nat.Prime 216217 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv7,pv11,pv13]) (by decide +kernel)
def pv216217 : PrimeValue := ⟨216217, pr216217⟩
private theorem pr216233 : Nat.Prime 216233 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv151,pv179]) (by decide +kernel)
def pv216233 : PrimeValue := ⟨216233, pr216233⟩
private theorem pr216263 : Nat.Prime 216263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv108131]) (by decide +kernel)
def pv216263 : PrimeValue := ⟨216263, pr216263⟩
private theorem pr216329 : Nat.Prime 216329 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv3863]) (by decide +kernel)
def pv216329 : PrimeValue := ⟨216329, pr216329⟩
private theorem pr216371 : Nat.Prime 216371 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv281]) (by decide +kernel)
def pv216371 : PrimeValue := ⟨216371, pr216371⟩
private theorem pr216373 : Nat.Prime 216373 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv19,pv73]) (by decide +kernel)
def pv216373 : PrimeValue := ⟨216373, pr216373⟩
private theorem pr216397 : Nat.Prime 216397 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv6011]) (by decide +kernel)
def pv216397 : PrimeValue := ⟨216397, pr216397⟩
private theorem pr216401 : Nat.Prime 216401 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv541]) (by decide +kernel)
def pv216401 : PrimeValue := ⟨216401, pr216401⟩
private theorem pr216431 : Nat.Prime 216431 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv23,pv941]) (by decide +kernel)
def pv216431 : PrimeValue := ⟨216431, pr216431⟩
private theorem pr216451 : Nat.Prime 216451 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv13,pv37]) (by decide +kernel)
def pv216451 : PrimeValue := ⟨216451, pr216451⟩
private theorem pr216481 : Nat.Prime 216481 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv41]) (by decide +kernel)
def pv216481 : PrimeValue := ⟨216481, pr216481⟩
private theorem pr216509 : Nat.Prime 216509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv113,pv479]) (by decide +kernel)
def pv216509 : PrimeValue := ⟨216509, pr216509⟩
private theorem pr216523 : Nat.Prime 216523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv523]) (by decide +kernel)
def pv216523 : PrimeValue := ⟨216523, pr216523⟩
private theorem pr216551 : Nat.Prime 216551 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv61,pv71]) (by decide +kernel)
def pv216551 : PrimeValue := ⟨216551, pr216551⟩
private theorem pr216553 : Nat.Prime 216553 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv1289]) (by decide +kernel)
def pv216553 : PrimeValue := ⟨216553, pr216553⟩
private theorem pr216569 : Nat.Prime 216569 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv23,pv107]) (by decide +kernel)
def pv216569 : PrimeValue := ⟨216569, pr216569⟩
private theorem pr216571 : Nat.Prime 216571 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7219]) (by decide +kernel)
def pv216571 : PrimeValue := ⟨216571, pr216571⟩
private theorem pr216577 : Nat.Prime 216577 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv47]) (by decide +kernel)
def pv216577 : PrimeValue := ⟨216577, pr216577⟩
private theorem pr216641 : Nat.Prime 216641 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv677]) (by decide +kernel)
def pv216641 : PrimeValue := ⟨216641, pr216641⟩
private theorem pr216647 : Nat.Prime 216647 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv149,pv727]) (by decide +kernel)
def pv216647 : PrimeValue := ⟨216647, pr216647⟩
private theorem pr216653 : Nat.Prime 216653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv54163]) (by decide +kernel)
def pv216653 : PrimeValue := ⟨216653, pr216653⟩
private theorem pr216679 : Nat.Prime 216679 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv67]) (by decide +kernel)
def pv216679 : PrimeValue := ⟨216679, pr216679⟩
private theorem pr216703 : Nat.Prime 216703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv4013]) (by decide +kernel)
def pv216703 : PrimeValue := ⟨216703, pr216703⟩
private theorem pr216719 : Nat.Prime 216719 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv108359]) (by decide +kernel)
def pv216719 : PrimeValue := ⟨216719, pr216719⟩
private theorem pr216743 : Nat.Prime 216743 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv307,pv353]) (by decide +kernel)
def pv216743 : PrimeValue := ⟨216743, pr216743⟩
private theorem pr216779 : Nat.Prime 216779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv283,pv383]) (by decide +kernel)
def pv216779 : PrimeValue := ⟨216779, pr216779⟩
private theorem pr216787 : Nat.Prime 216787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv36131]) (by decide +kernel)
def pv216787 : PrimeValue := ⟨216787, pr216787⟩
private theorem pr216803 : Nat.Prime 216803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv108401]) (by decide +kernel)
def pv216803 : PrimeValue := ⟨216803, pr216803⟩
private theorem pr216829 : Nat.Prime 216829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv317]) (by decide +kernel)
def pv216829 : PrimeValue := ⟨216829, pr216829⟩
private theorem pr216851 : Nat.Prime 216851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv4337]) (by decide +kernel)
def pv216851 : PrimeValue := ⟨216851, pr216851⟩
private theorem pr216877 : Nat.Prime 216877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv31,pv53]) (by decide +kernel)
def pv216877 : PrimeValue := ⟨216877, pr216877⟩
private theorem pr216901 : Nat.Prime 216901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv241]) (by decide +kernel)
def pv216901 : PrimeValue := ⟨216901, pr216901⟩
private theorem pr216911 : Nat.Prime 216911 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv109,pv199]) (by decide +kernel)
def pv216911 : PrimeValue := ⟨216911, pr216911⟩
private theorem pr216919 : Nat.Prime 216919 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv13,pv103]) (by decide +kernel)
def pv216919 : PrimeValue := ⟨216919, pr216919⟩
private theorem pr216947 : Nat.Prime 216947 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv67,pv1619]) (by decide +kernel)
def pv216947 : PrimeValue := ⟨216947, pr216947⟩
private theorem pr216973 : Nat.Prime 216973 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv7,pv41]) (by decide +kernel)
def pv216973 : PrimeValue := ⟨216973, pr216973⟩
private theorem pr216991 : Nat.Prime 216991 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv2411]) (by decide +kernel)
def pv216991 : PrimeValue := ⟨216991, pr216991⟩
private theorem pr217001 : Nat.Prime 217001 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv31]) (by decide +kernel)
def pv217001 : PrimeValue := ⟨217001, pr217001⟩
private theorem pr217003 : Nat.Prime 217003 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv59,pv613]) (by decide +kernel)
def pv217003 : PrimeValue := ⟨217003, pr217003⟩
private theorem pr217027 : Nat.Prime 217027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4019]) (by decide +kernel)
def pv217027 : PrimeValue := ⟨217027, pr217027⟩
private theorem pr217033 : Nat.Prime 217033 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv9043]) (by decide +kernel)
def pv217033 : PrimeValue := ⟨217033, pr217033⟩
private theorem pr217057 : Nat.Prime 217057 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv7,pv17,pv19]) (by decide +kernel)
def pv217057 : PrimeValue := ⟨217057, pr217057⟩
private theorem pr217069 : Nat.Prime 217069 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv18089]) (by decide +kernel)
def pv217069 : PrimeValue := ⟨217069, pr217069⟩
private theorem pr217081 : Nat.Prime 217081 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv67]) (by decide +kernel)
def pv217081 : PrimeValue := ⟨217081, pr217081⟩
private theorem pr217111 : Nat.Prime 217111 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7237]) (by decide +kernel)
def pv217111 : PrimeValue := ⟨217111, pr217111⟩
private theorem pr217121 : Nat.Prime 217121 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv23,pv59]) (by decide +kernel)
def pv217121 : PrimeValue := ⟨217121, pr217121⟩
private theorem pr217157 : Nat.Prime 217157 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv233]) (by decide +kernel)
def pv217157 : PrimeValue := ⟨217157, pr217157⟩
private theorem pr217163 : Nat.Prime 217163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv9871]) (by decide +kernel)
def pv217163 : PrimeValue := ⟨217163, pr217163⟩
private theorem pr217199 : Nat.Prime 217199 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv131,pv829]) (by decide +kernel)
def pv217199 : PrimeValue := ⟨217199, pr217199⟩
private theorem pr217207 : Nat.Prime 217207 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv1097]) (by decide +kernel)
def pv217207 : PrimeValue := ⟨217207, pr217207⟩
private theorem pr217219 : Nat.Prime 217219 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv41,pv883]) (by decide +kernel)
def pv217219 : PrimeValue := ⟨217219, pr217219⟩
private theorem pr217223 : Nat.Prime 217223 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv313,pv347]) (by decide +kernel)
def pv217223 : PrimeValue := ⟨217223, pr217223⟩
private theorem pr217229 : Nat.Prime 217229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv4937]) (by decide +kernel)
def pv217229 : PrimeValue := ⟨217229, pr217229⟩
private theorem pr217271 : Nat.Prime 217271 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv21727]) (by decide +kernel)
def pv217271 : PrimeValue := ⟨217271, pr217271⟩
private theorem pr217313 : Nat.Prime 217313 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv6791]) (by decide +kernel)
def pv217313 : PrimeValue := ⟨217313, pr217313⟩
private theorem pr217319 : Nat.Prime 217319 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv193,pv563]) (by decide +kernel)
def pv217319 : PrimeValue := ⟨217319, pr217319⟩
private theorem pr217337 : Nat.Prime 217337 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv3881]) (by decide +kernel)
def pv217337 : PrimeValue := ⟨217337, pr217337⟩
private theorem pr217361 : Nat.Prime 217361 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv11,pv13,pv19]) (by decide +kernel)
def pv217361 : PrimeValue := ⟨217361, pr217361⟩
private theorem pr217397 : Nat.Prime 217397 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv23,pv139]) (by decide +kernel)
def pv217397 : PrimeValue := ⟨217397, pr217397⟩
private theorem pr217411 : Nat.Prime 217411 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv7247]) (by decide +kernel)
def pv217411 : PrimeValue := ⟨217411, pr217411⟩
private theorem pr217429 : Nat.Prime 217429 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv18119]) (by decide +kernel)
def pv217429 : PrimeValue := ⟨217429, pr217429⟩
private theorem pr217439 : Nat.Prime 217439 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv13,pv8363]) (by decide +kernel)
def pv217439 : PrimeValue := ⟨217439, pr217439⟩
private theorem pr217457 : Nat.Prime 217457 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13591]) (by decide +kernel)
def pv217457 : PrimeValue := ⟨217457, pr217457⟩
private theorem pr217463 : Nat.Prime 217463 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv317]) (by decide +kernel)
def pv217463 : PrimeValue := ⟨217463, pr217463⟩
private theorem pr217489 : Nat.Prime 217489 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv23,pv197]) (by decide +kernel)
def pv217489 : PrimeValue := ⟨217489, pr217489⟩
private theorem pr217499 : Nat.Prime 217499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv6397]) (by decide +kernel)
def pv217499 : PrimeValue := ⟨217499, pr217499⟩
private theorem pr217519 : Nat.Prime 217519 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv7,pv5179]) (by decide +kernel)
def pv217519 : PrimeValue := ⟨217519, pr217519⟩
private theorem pr217573 : Nat.Prime 217573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv18131]) (by decide +kernel)
def pv217573 : PrimeValue := ⟨217573, pr217573⟩
private theorem pr217577 : Nat.Prime 217577 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv27197]) (by decide +kernel)
def pv217577 : PrimeValue := ⟨217577, pr217577⟩
private theorem pr217579 : Nat.Prime 217579 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv36263]) (by decide +kernel)
def pv217579 : PrimeValue := ⟨217579, pr217579⟩
private theorem pr217643 : Nat.Prime 217643 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv108821]) (by decide +kernel)
def pv217643 : PrimeValue := ⟨217643, pr217643⟩
private theorem pr217681 : Nat.Prime 217681 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv907]) (by decide +kernel)
def pv217681 : PrimeValue := ⟨217681, pr217681⟩
private theorem pr217687 : Nat.Prime 217687 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv71,pv73]) (by decide +kernel)
def pv217687 : PrimeValue := ⟨217687, pr217687⟩
private theorem pr217691 : Nat.Prime 217691 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv1979]) (by decide +kernel)
def pv217691 : PrimeValue := ⟨217691, pr217691⟩
private theorem pr217739 : Nat.Prime 217739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv108869]) (by decide +kernel)
def pv217739 : PrimeValue := ⟨217739, pr217739⟩
private theorem pr217747 : Nat.Prime 217747 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv12097]) (by decide +kernel)
def pv217747 : PrimeValue := ⟨217747, pr217747⟩
private theorem pr217781 : Nat.Prime 217781 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv10889]) (by decide +kernel)
def pv217781 : PrimeValue := ⟨217781, pr217781⟩
private theorem pr217793 : Nat.Prime 217793 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv41,pv83]) (by decide +kernel)
def pv217793 : PrimeValue := ⟨217793, pr217793⟩
private theorem pr217823 : Nat.Prime 217823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv9901]) (by decide +kernel)
def pv217823 : PrimeValue := ⟨217823, pr217823⟩
private theorem pr217859 : Nat.Prime 217859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv108929]) (by decide +kernel)
def pv217859 : PrimeValue := ⟨217859, pr217859⟩
private theorem pr217979 : Nat.Prime 217979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv73,pv1493]) (by decide +kernel)
def pv217979 : PrimeValue := ⟨217979, pr217979⟩
private theorem pr217981 : Nat.Prime 217981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv173]) (by decide +kernel)
def pv217981 : PrimeValue := ⟨217981, pr217981⟩
private theorem pr218003 : Nat.Prime 218003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv109001]) (by decide +kernel)
def pv218003 : PrimeValue := ⟨218003, pr218003⟩
private theorem pr218047 : Nat.Prime 218047 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv36341]) (by decide +kernel)
def pv218047 : PrimeValue := ⟨218047, pr218047⟩
private theorem pr218069 : Nat.Prime 218069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv54517]) (by decide +kernel)
def pv218069 : PrimeValue := ⟨218069, pr218069⟩
private theorem pr218083 : Nat.Prime 218083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv1913]) (by decide +kernel)
def pv218083 : PrimeValue := ⟨218083, pr218083⟩
private theorem pr218087 : Nat.Prime 218087 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv23,pv431]) (by decide +kernel)
def pv218087 : PrimeValue := ⟨218087, pr218087⟩
private theorem pr218107 : Nat.Prime 218107 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv577]) (by decide +kernel)
def pv218107 : PrimeValue := ⟨218107, pr218107⟩
private theorem pr218137 : Nat.Prime 218137 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv61,pv149]) (by decide +kernel)
def pv218137 : PrimeValue := ⟨218137, pr218137⟩
private theorem pr218143 : Nat.Prime 218143 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv12119]) (by decide +kernel)
def pv218143 : PrimeValue := ⟨218143, pr218143⟩
private theorem pr218171 : Nat.Prime 218171 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv21817]) (by decide +kernel)
def pv218171 : PrimeValue := ⟨218171, pr218171⟩
private theorem pr218213 : Nat.Prime 218213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv3209]) (by decide +kernel)
def pv218213 : PrimeValue := ⟨218213, pr218213⟩
private theorem pr218233 : Nat.Prime 218233 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv433]) (by decide +kernel)
def pv218233 : PrimeValue := ⟨218233, pr218233⟩
private theorem pr218249 : Nat.Prime 218249 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv27281]) (by decide +kernel)
def pv218249 : PrimeValue := ⟨218249, pr218249⟩
private theorem pr218287 : Nat.Prime 218287 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv67,pv181]) (by decide +kernel)
def pv218287 : PrimeValue := ⟨218287, pr218287⟩
private theorem pr218357 : Nat.Prime 218357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79,pv691]) (by decide +kernel)
def pv218357 : PrimeValue := ⟨218357, pr218357⟩
private theorem pr218363 : Nat.Prime 218363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv47,pv101]) (by decide +kernel)
def pv218363 : PrimeValue := ⟨218363, pr218363⟩
private theorem pr218381 : Nat.Prime 218381 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv61,pv179]) (by decide +kernel)
def pv218381 : PrimeValue := ⟨218381, pr218381⟩
private theorem pr218417 : Nat.Prime 218417 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv17,pv73]) (by decide +kernel)
def pv218417 : PrimeValue := ⟨218417, pr218417⟩
private theorem pr218453 : Nat.Prime 218453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv4201]) (by decide +kernel)
def pv218453 : PrimeValue := ⟨218453, pr218453⟩
private theorem pr218509 : Nat.Prime 218509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv131,pv139]) (by decide +kernel)
def pv218509 : PrimeValue := ⟨218509, pr218509⟩
private theorem pr218513 : Nat.Prime 218513 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv1951]) (by decide +kernel)
def pv218513 : PrimeValue := ⟨218513, pr218513⟩
private theorem pr218521 : Nat.Prime 218521 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv607]) (by decide +kernel)
def pv218521 : PrimeValue := ⟨218521, pr218521⟩
private theorem pr218527 : Nat.Prime 218527 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv43]) (by decide +kernel)
def pv218527 : PrimeValue := ⟨218527, pr218527⟩
private theorem pr218551 : Nat.Prime 218551 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv31,pv47]) (by decide +kernel)
def pv218551 : PrimeValue := ⟨218551, pr218551⟩
private theorem pr218579 : Nat.Prime 218579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv293,pv373]) (by decide +kernel)
def pv218579 : PrimeValue := ⟨218579, pr218579⟩
private theorem pr218591 : Nat.Prime 218591 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv21859]) (by decide +kernel)
def pv218591 : PrimeValue := ⟨218591, pr218591⟩
private theorem pr218599 : Nat.Prime 218599 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv36433]) (by decide +kernel)
def pv218599 : PrimeValue := ⟨218599, pr218599⟩
private theorem pr218611 : Nat.Prime 218611 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv347]) (by decide +kernel)
def pv218611 : PrimeValue := ⟨218611, pr218611⟩
private theorem pr218623 : Nat.Prime 218623 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv83,pv439]) (by decide +kernel)
def pv218623 : PrimeValue := ⟨218623, pr218623⟩
private theorem pr218629 : Nat.Prime 218629 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv6073]) (by decide +kernel)
def pv218629 : PrimeValue := ⟨218629, pr218629⟩
private theorem pr218641 : Nat.Prime 218641 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv911]) (by decide +kernel)
def pv218641 : PrimeValue := ⟨218641, pr218641⟩
private theorem pr218657 : Nat.Prime 218657 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv6833]) (by decide +kernel)
def pv218657 : PrimeValue := ⟨218657, pr218657⟩
private theorem pr218681 : Nat.Prime 218681 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv7,pv11,pv71]) (by decide +kernel)
def pv218681 : PrimeValue := ⟨218681, pr218681⟩
private theorem pr218717 : Nat.Prime 218717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv54679]) (by decide +kernel)
def pv218717 : PrimeValue := ⟨218717, pr218717⟩
private theorem pr218723 : Nat.Prime 218723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv17,pv919]) (by decide +kernel)
def pv218723 : PrimeValue := ⟨218723, pr218723⟩
private theorem pr218749 : Nat.Prime 218749 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv18229]) (by decide +kernel)
def pv218749 : PrimeValue := ⟨218749, pr218749⟩
private theorem pr218761 : Nat.Prime 218761 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv1823]) (by decide +kernel)
def pv218761 : PrimeValue := ⟨218761, pr218761⟩
private theorem pr218783 : Nat.Prime 218783 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv109391]) (by decide +kernel)
def pv218783 : PrimeValue := ⟨218783, pr218783⟩
private theorem pr218797 : Nat.Prime 218797 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv18233]) (by decide +kernel)
def pv218797 : PrimeValue := ⟨218797, pr218797⟩
private theorem pr218819 : Nat.Prime 218819 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv2957]) (by decide +kernel)
def pv218819 : PrimeValue := ⟨218819, pr218819⟩
private theorem pr218833 : Nat.Prime 218833 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv47,pv97]) (by decide +kernel)
def pv218833 : PrimeValue := ⟨218833, pr218833⟩
private theorem pr218839 : Nat.Prime 218839 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv36473]) (by decide +kernel)
def pv218839 : PrimeValue := ⟨218839, pr218839⟩
private theorem pr218843 : Nat.Prime 218843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv19,pv443]) (by decide +kernel)
def pv218843 : PrimeValue := ⟨218843, pr218843⟩
private theorem pr218857 : Nat.Prime 218857 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv829]) (by decide +kernel)
def pv218857 : PrimeValue := ⟨218857, pr218857⟩
private theorem pr218873 : Nat.Prime 218873 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv109,pv251]) (by decide +kernel)
def pv218873 : PrimeValue := ⟨218873, pr218873⟩
private theorem pr218887 : Nat.Prime 218887 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv191]) (by decide +kernel)
def pv218887 : PrimeValue := ⟨218887, pr218887⟩
private theorem pr218963 : Nat.Prime 218963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv109481]) (by decide +kernel)
def pv218963 : PrimeValue := ⟨218963, pr218963⟩
private theorem pr218969 : Nat.Prime 218969 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv101,pv271]) (by decide +kernel)
def pv218969 : PrimeValue := ⟨218969, pr218969⟩
private theorem pr218971 : Nat.Prime 218971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv811]) (by decide +kernel)
def pv218971 : PrimeValue := ⟨218971, pr218971⟩
private theorem pr218989 : Nat.Prime 218989 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv7,pv11,pv79]) (by decide +kernel)
def pv218989 : PrimeValue := ⟨218989, pr218989⟩
private theorem pr218993 : Nat.Prime 218993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13687]) (by decide +kernel)
def pv218993 : PrimeValue := ⟨218993, pr218993⟩
private theorem pr219017 : Nat.Prime 219017 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv3911]) (by decide +kernel)
def pv219017 : PrimeValue := ⟨219017, pr219017⟩
private theorem pr219019 : Nat.Prime 219019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv173,pv211]) (by decide +kernel)
def pv219019 : PrimeValue := ⟨219019, pr219019⟩
private theorem pr219031 : Nat.Prime 219031 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv149]) (by decide +kernel)
def pv219031 : PrimeValue := ⟨219031, pr219031⟩
private theorem pr219053 : Nat.Prime 219053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv2381]) (by decide +kernel)
def pv219053 : PrimeValue := ⟨219053, pr219053⟩
private theorem pr219059 : Nat.Prime 219059 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv15647]) (by decide +kernel)
def pv219059 : PrimeValue := ⟨219059, pr219059⟩
private theorem pr219071 : Nat.Prime 219071 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv19,pv1153]) (by decide +kernel)
def pv219071 : PrimeValue := ⟨219071, pr219071⟩
private theorem pr219091 : Nat.Prime 219091 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv67,pv109]) (by decide +kernel)
def pv219091 : PrimeValue := ⟨219091, pr219091⟩
private theorem pr219097 : Nat.Prime 219097 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv179]) (by decide +kernel)
def pv219097 : PrimeValue := ⟨219097, pr219097⟩
private theorem pr219103 : Nat.Prime 219103 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv13,pv53]) (by decide +kernel)
def pv219103 : PrimeValue := ⟨219103, pr219103⟩
private theorem pr219119 : Nat.Prime 219119 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv89,pv1231]) (by decide +kernel)
def pv219119 : PrimeValue := ⟨219119, pr219119⟩
private theorem pr219133 : Nat.Prime 219133 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2029]) (by decide +kernel)
def pv219133 : PrimeValue := ⟨219133, pr219133⟩
private theorem pr219143 : Nat.Prime 219143 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv11,pv1423]) (by decide +kernel)
def pv219143 : PrimeValue := ⟨219143, pr219143⟩
private theorem pr219169 : Nat.Prime 219169 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv761]) (by decide +kernel)
def pv219169 : PrimeValue := ⟨219169, pr219169⟩
private theorem pr219187 : Nat.Prime 219187 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv41]) (by decide +kernel)
def pv219187 : PrimeValue := ⟨219187, pr219187⟩
private theorem pr219223 : Nat.Prime 219223 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv641]) (by decide +kernel)
def pv219223 : PrimeValue := ⟨219223, pr219223⟩
private theorem pr219251 : Nat.Prime 219251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv877]) (by decide +kernel)
def pv219251 : PrimeValue := ⟨219251, pr219251⟩
private theorem pr219277 : Nat.Prime 219277 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv6091]) (by decide +kernel)
def pv219277 : PrimeValue := ⟨219277, pr219277⟩
private theorem pr219311 : Nat.Prime 219311 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv13,pv241]) (by decide +kernel)
def pv219311 : PrimeValue := ⟨219311, pr219311⟩
private theorem pr219353 : Nat.Prime 219353 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv3917]) (by decide +kernel)
def pv219353 : PrimeValue := ⟨219353, pr219353⟩
private theorem pr219377 : Nat.Prime 219377 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13711]) (by decide +kernel)
def pv219377 : PrimeValue := ⟨219377, pr219377⟩
private theorem pr219389 : Nat.Prime 219389 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv4219]) (by decide +kernel)
def pv219389 : PrimeValue := ⟨219389, pr219389⟩
private theorem pr219437 : Nat.Prime 219437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv17,pv461]) (by decide +kernel)
def pv219437 : PrimeValue := ⟨219437, pr219437⟩
private theorem pr219463 : Nat.Prime 219463 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv79,pv463]) (by decide +kernel)
def pv219463 : PrimeValue := ⟨219463, pr219463⟩
private theorem pr219467 : Nat.Prime 219467 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv23,pv367]) (by decide +kernel)
def pv219467 : PrimeValue := ⟨219467, pr219467⟩
private theorem pr219491 : Nat.Prime 219491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv47,pv467]) (by decide +kernel)
def pv219491 : PrimeValue := ⟨219491, pr219491⟩
private theorem pr219503 : Nat.Prime 219503 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv109751]) (by decide +kernel)
def pv219503 : PrimeValue := ⟨219503, pr219503⟩
private theorem pr219547 : Nat.Prime 219547 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv12197]) (by decide +kernel)
def pv219547 : PrimeValue := ⟨219547, pr219547⟩
private theorem pr219577 : Nat.Prime 219577 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv1307]) (by decide +kernel)
def pv219577 : PrimeValue := ⟨219577, pr219577⟩
private theorem pr219587 : Nat.Prime 219587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv109793]) (by decide +kernel)
def pv219587 : PrimeValue := ⟨219587, pr219587⟩
private theorem pr219599 : Nat.Prime 219599 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv59,pv1861]) (by decide +kernel)
def pv219599 : PrimeValue := ⟨219599, pr219599⟩
private theorem pr219613 : Nat.Prime 219613 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv18301]) (by decide +kernel)
def pv219613 : PrimeValue := ⟨219613, pr219613⟩
private theorem pr219619 : Nat.Prime 219619 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv83]) (by decide +kernel)
def pv219619 : PrimeValue := ⟨219619, pr219619⟩
private theorem pr219629 : Nat.Prime 219629 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv54907]) (by decide +kernel)
def pv219629 : PrimeValue := ⟨219629, pr219629⟩
private theorem pr219649 : Nat.Prime 219649 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv13]) (by decide +kernel)
def pv219649 : PrimeValue := ⟨219649, pr219649⟩
private theorem pr219677 : Nat.Prime 219677 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv54919]) (by decide +kernel)
def pv219677 : PrimeValue := ⟨219677, pr219677⟩
private theorem pr219679 : Nat.Prime 219679 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv19,pv41,pv47]) (by decide +kernel)
def pv219679 : PrimeValue := ⟨219679, pr219679⟩
private theorem pr219683 : Nat.Prime 219683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv109841]) (by decide +kernel)
def pv219683 : PrimeValue := ⟨219683, pr219683⟩
private theorem pr219707 : Nat.Prime 219707 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv2969]) (by decide +kernel)
def pv219707 : PrimeValue := ⟨219707, pr219707⟩
private theorem pr219731 : Nat.Prime 219731 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv43,pv73]) (by decide +kernel)
def pv219731 : PrimeValue := ⟨219731, pr219731⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
