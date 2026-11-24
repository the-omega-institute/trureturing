/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table077
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table077.pv253507
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table011
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table017
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table018
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table046
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table047

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr253507 : Nat.Prime 253507 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv23,pv167]) (by decide +kernel)
def pv253507 : PrimeValue := ⟨253507, pr253507⟩
private theorem pr253537 : Nat.Prime 253537 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv139]) (by decide +kernel)
def pv253537 : PrimeValue := ⟨253537, pr253537⟩
private theorem pr253543 : Nat.Prime 253543 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv42257]) (by decide +kernel)
def pv253543 : PrimeValue := ⟨253543, pr253543⟩
private theorem pr253567 : Nat.Prime 253567 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv14087]) (by decide +kernel)
def pv253567 : PrimeValue := ⟨253567, pr253567⟩
private theorem pr253601 : Nat.Prime 253601 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv317]) (by decide +kernel)
def pv253601 : PrimeValue := ⟨253601, pr253601⟩
private theorem pr253607 : Nat.Prime 253607 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv7459]) (by decide +kernel)
def pv253607 : PrimeValue := ⟨253607, pr253607⟩
private theorem pr253609 : Nat.Prime 253609 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv10567]) (by decide +kernel)
def pv253609 : PrimeValue := ⟨253609, pr253609⟩
private theorem pr253633 : Nat.Prime 253633 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv1321]) (by decide +kernel)
def pv253633 : PrimeValue := ⟨253633, pr253633⟩
private theorem pr253639 : Nat.Prime 253639 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv61]) (by decide +kernel)
def pv253639 : PrimeValue := ⟨253639, pr253639⟩
private theorem pr253679 : Nat.Prime 253679 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv126839]) (by decide +kernel)
def pv253679 : PrimeValue := ⟨253679, pr253679⟩
private theorem pr253681 : Nat.Prime 253681 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv7,pv151]) (by decide +kernel)
def pv253681 : PrimeValue := ⟨253681, pr253681⟩
private theorem pr253717 : Nat.Prime 253717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv21143]) (by decide +kernel)
def pv253717 : PrimeValue := ⟨253717, pr253717⟩
private theorem pr253733 : Nat.Prime 253733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv229,pv277]) (by decide +kernel)
def pv253733 : PrimeValue := ⟨253733, pr253733⟩
private theorem pr253741 : Nat.Prime 253741 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv4229]) (by decide +kernel)
def pv253741 : PrimeValue := ⟨253741, pr253741⟩
private theorem pr253751 : Nat.Prime 253751 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv29]) (by decide +kernel)
def pv253751 : PrimeValue := ⟨253751, pr253751⟩
private theorem pr253763 : Nat.Prime 253763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv181,pv701]) (by decide +kernel)
def pv253763 : PrimeValue := ⟨253763, pr253763⟩
private theorem pr253777 : Nat.Prime 253777 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv17,pv311]) (by decide +kernel)
def pv253777 : PrimeValue := ⟨253777, pr253777⟩
private theorem pr253801 : Nat.Prime 253801 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv47]) (by decide +kernel)
def pv253801 : PrimeValue := ⟨253801, pr253801⟩
private theorem pr253811 : Nat.Prime 253811 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv1493]) (by decide +kernel)
def pv253811 : PrimeValue := ⟨253811, pr253811⟩
private theorem pr253819 : Nat.Prime 253819 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv59,pv239]) (by decide +kernel)
def pv253819 : PrimeValue := ⟨253819, pr253819⟩
private theorem pr253853 : Nat.Prime 253853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv63463]) (by decide +kernel)
def pv253853 : PrimeValue := ⟨253853, pr253853⟩
private theorem pr253871 : Nat.Prime 253871 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv5,pv53,pv479]) (by decide +kernel)
def pv253871 : PrimeValue := ⟨253871, pr253871⟩
private theorem pr253879 : Nat.Prime 253879 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv17,pv19,pv131]) (by decide +kernel)
def pv253879 : PrimeValue := ⟨253879, pr253879⟩
private theorem pr253901 : Nat.Prime 253901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv2539]) (by decide +kernel)
def pv253901 : PrimeValue := ⟨253901, pr253901⟩
private theorem pr253907 : Nat.Prime 253907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79,pv1607]) (by decide +kernel)
def pv253907 : PrimeValue := ⟨253907, pr253907⟩
private theorem pr253909 : Nat.Prime 253909 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv2351]) (by decide +kernel)
def pv253909 : PrimeValue := ⟨253909, pr253909⟩
private theorem pr253919 : Nat.Prime 253919 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv2591]) (by decide +kernel)
def pv253919 : PrimeValue := ⟨253919, pr253919⟩
private theorem pr253949 : Nat.Prime 253949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv63487]) (by decide +kernel)
def pv253949 : PrimeValue := ⟨253949, pr253949⟩
private theorem pr253951 : Nat.Prime 253951 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv1693]) (by decide +kernel)
def pv253951 : PrimeValue := ⟨253951, pr253951⟩
private theorem pr253969 : Nat.Prime 253969 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv11,pv13,pv37]) (by decide +kernel)
def pv253969 : PrimeValue := ⟨253969, pr253969⟩
private theorem pr253987 : Nat.Prime 253987 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv42331]) (by decide +kernel)
def pv253987 : PrimeValue := ⟨253987, pr253987⟩
private theorem pr254039 : Nat.Prime 254039 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv71,pv1789]) (by decide +kernel)
def pv254039 : PrimeValue := ⟨254039, pr254039⟩
private theorem pr254041 : Nat.Prime 254041 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv29,pv73]) (by decide +kernel)
def pv254041 : PrimeValue := ⟨254041, pr254041⟩
private theorem pr254053 : Nat.Prime 254053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7057]) (by decide +kernel)
def pv254053 : PrimeValue := ⟨254053, pr254053⟩
private theorem pr254083 : Nat.Prime 254083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv47,pv53]) (by decide +kernel)
def pv254083 : PrimeValue := ⟨254083, pr254083⟩
private theorem pr254141 : Nat.Prime 254141 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv97,pv131]) (by decide +kernel)
def pv254141 : PrimeValue := ⟨254141, pr254141⟩
private theorem pr254197 : Nat.Prime 254197 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv23,pv307]) (by decide +kernel)
def pv254197 : PrimeValue := ⟨254197, pr254197⟩
private theorem pr254207 : Nat.Prime 254207 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv127103]) (by decide +kernel)
def pv254207 : PrimeValue := ⟨254207, pr254207⟩
private theorem pr254209 : Nat.Prime 254209 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv331]) (by decide +kernel)
def pv254209 : PrimeValue := ⟨254209, pr254209⟩
private theorem pr254249 : Nat.Prime 254249 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv61,pv521]) (by decide +kernel)
def pv254249 : PrimeValue := ⟨254249, pr254249⟩
private theorem pr254279 : Nat.Prime 254279 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv127139]) (by decide +kernel)
def pv254279 : PrimeValue := ⟨254279, pr254279⟩
private theorem pr254291 : Nat.Prime 254291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv59,pv431]) (by decide +kernel)
def pv254291 : PrimeValue := ⟨254291, pr254291⟩
private theorem pr254377 : Nat.Prime 254377 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv3533]) (by decide +kernel)
def pv254377 : PrimeValue := ⟨254377, pr254377⟩
private theorem pr254389 : Nat.Prime 254389 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv17,pv29,pv43]) (by decide +kernel)
def pv254389 : PrimeValue := ⟨254389, pr254389⟩
private theorem pr254413 : Nat.Prime 254413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv191]) (by decide +kernel)
def pv254413 : PrimeValue := ⟨254413, pr254413⟩
private theorem pr254437 : Nat.Prime 254437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv233]) (by decide +kernel)
def pv254437 : PrimeValue := ⟨254437, pr254437⟩
private theorem pr254519 : Nat.Prime 254519 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv11,pv23,pv503]) (by decide +kernel)
def pv254519 : PrimeValue := ⟨254519, pr254519⟩
private theorem pr254623 : Nat.Prime 254623 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv42437]) (by decide +kernel)
def pv254623 : PrimeValue := ⟨254623, pr254623⟩
private theorem pr254627 : Nat.Prime 254627 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv7489]) (by decide +kernel)
def pv254627 : PrimeValue := ⟨254627, pr254627⟩
private theorem pr254659 : Nat.Prime 254659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv42443]) (by decide +kernel)
def pv254659 : PrimeValue := ⟨254659, pr254659⟩
private theorem pr254663 : Nat.Prime 254663 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv127331]) (by decide +kernel)
def pv254663 : PrimeValue := ⟨254663, pr254663⟩
private theorem pr254713 : Nat.Prime 254713 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv10613]) (by decide +kernel)
def pv254713 : PrimeValue := ⟨254713, pr254713⟩
private theorem pr254741 : Nat.Prime 254741 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv47,pv271]) (by decide +kernel)
def pv254741 : PrimeValue := ⟨254741, pr254741⟩
private theorem pr254753 : Nat.Prime 254753 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv419]) (by decide +kernel)
def pv254753 : PrimeValue := ⟨254753, pr254753⟩
private theorem pr254773 : Nat.Prime 254773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv337]) (by decide +kernel)
def pv254773 : PrimeValue := ⟨254773, pr254773⟩
private theorem pr254777 : Nat.Prime 254777 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31847]) (by decide +kernel)
def pv254777 : PrimeValue := ⟨254777, pr254777⟩
private theorem pr254833 : Nat.Prime 254833 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5309]) (by decide +kernel)
def pv254833 : PrimeValue := ⟨254833, pr254833⟩
private theorem pr254857 : Nat.Prime 254857 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv7,pv37,pv41]) (by decide +kernel)
def pv254857 : PrimeValue := ⟨254857, pr254857⟩
private theorem pr254887 : Nat.Prime 254887 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv1847]) (by decide +kernel)
def pv254887 : PrimeValue := ⟨254887, pr254887⟩
private theorem pr254911 : Nat.Prime 254911 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv29,pv293]) (by decide +kernel)
def pv254911 : PrimeValue := ⟨254911, pr254911⟩
private theorem pr254927 : Nat.Prime 254927 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv131,pv139]) (by decide +kernel)
def pv254927 : PrimeValue := ⟨254927, pr254927⟩
private theorem pr254929 : Nat.Prime 254929 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv47,pv113]) (by decide +kernel)
def pv254929 : PrimeValue := ⟨254929, pr254929⟩
private theorem pr254941 : Nat.Prime 254941 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv3,pv5,pv7,pv607]) (by decide +kernel)
def pv254941 : PrimeValue := ⟨254941, pr254941⟩
private theorem pr254959 : Nat.Prime 254959 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv3863]) (by decide +kernel)
def pv254959 : PrimeValue := ⟨254959, pr254959⟩
private theorem pr254977 : Nat.Prime 254977 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv83]) (by decide +kernel)
def pv254977 : PrimeValue := ⟨254977, pr254977⟩
private theorem pr255019 : Nat.Prime 255019 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv19,pv2237]) (by decide +kernel)
def pv255019 : PrimeValue := ⟨255019, pr255019⟩
private theorem pr255023 : Nat.Prime 255023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv47,pv2713]) (by decide +kernel)
def pv255023 : PrimeValue := ⟨255023, pr255023⟩
private theorem pr255043 : Nat.Prime 255043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4723]) (by decide +kernel)
def pv255043 : PrimeValue := ⟨255043, pr255043⟩
private theorem pr255053 : Nat.Prime 255053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv9109]) (by decide +kernel)
def pv255053 : PrimeValue := ⟨255053, pr255053⟩
private theorem pr255071 : Nat.Prime 255071 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv23,pv1109]) (by decide +kernel)
def pv255071 : PrimeValue := ⟨255071, pr255071⟩
private theorem pr255083 : Nat.Prime 255083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv127541]) (by decide +kernel)
def pv255083 : PrimeValue := ⟨255083, pr255083⟩
private theorem pr255097 : Nat.Prime 255097 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1181]) (by decide +kernel)
def pv255097 : PrimeValue := ⟨255097, pr255097⟩
private theorem pr255137 : Nat.Prime 255137 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv17,pv67]) (by decide +kernel)
def pv255137 : PrimeValue := ⟨255137, pr255137⟩
private theorem pr255149 : Nat.Prime 255149 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv227,pv281]) (by decide +kernel)
def pv255149 : PrimeValue := ⟨255149, pr255149⟩
private theorem pr255173 : Nat.Prime 255173 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv63793]) (by decide +kernel)
def pv255173 : PrimeValue := ⟨255173, pr255173⟩
private theorem pr255179 : Nat.Prime 255179 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv11,pv1657]) (by decide +kernel)
def pv255179 : PrimeValue := ⟨255179, pr255179⟩
private theorem pr255191 : Nat.Prime 255191 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv13,pv151]) (by decide +kernel)
def pv255191 : PrimeValue := ⟨255191, pr255191⟩
private theorem pr255193 : Nat.Prime 255193 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv31]) (by decide +kernel)
def pv255193 : PrimeValue := ⟨255193, pr255193⟩
private theorem pr255209 : Nat.Prime 255209 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv23,pv73]) (by decide +kernel)
def pv255209 : PrimeValue := ⟨255209, pr255209⟩
private theorem pr255217 : Nat.Prime 255217 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv13,pv409]) (by decide +kernel)
def pv255217 : PrimeValue := ⟨255217, pr255217⟩
private theorem pr255247 : Nat.Prime 255247 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv2239]) (by decide +kernel)
def pv255247 : PrimeValue := ⟨255247, pr255247⟩
private theorem pr255251 : Nat.Prime 255251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1021]) (by decide +kernel)
def pv255251 : PrimeValue := ⟨255251, pr255251⟩
private theorem pr255253 : Nat.Prime 255253 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv89,pv239]) (by decide +kernel)
def pv255253 : PrimeValue := ⟨255253, pr255253⟩
private theorem pr255313 : Nat.Prime 255313 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv197]) (by decide +kernel)
def pv255313 : PrimeValue := ⟨255313, pr255313⟩
private theorem pr255349 : Nat.Prime 255349 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv41,pv173]) (by decide +kernel)
def pv255349 : PrimeValue := ⟨255349, pr255349⟩
private theorem pr255361 : Nat.Prime 255361 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv19]) (by decide +kernel)
def pv255361 : PrimeValue := ⟨255361, pr255361⟩
private theorem pr255371 : Nat.Prime 255371 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv25537]) (by decide +kernel)
def pv255371 : PrimeValue := ⟨255371, pr255371⟩
private theorem pr255383 : Nat.Prime 255383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv127691]) (by decide +kernel)
def pv255383 : PrimeValue := ⟨255383, pr255383⟩
private theorem pr255413 : Nat.Prime 255413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv63853]) (by decide +kernel)
def pv255413 : PrimeValue := ⟨255413, pr255413⟩
private theorem pr255443 : Nat.Prime 255443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv17,pv683]) (by decide +kernel)
def pv255443 : PrimeValue := ⟨255443, pr255443⟩
private theorem pr255467 : Nat.Prime 255467 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv127733]) (by decide +kernel)
def pv255467 : PrimeValue := ⟨255467, pr255467⟩
private theorem pr255499 : Nat.Prime 255499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv97,pv439]) (by decide +kernel)
def pv255499 : PrimeValue := ⟨255499, pr255499⟩
private theorem pr255517 : Nat.Prime 255517 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv107,pv199]) (by decide +kernel)
def pv255517 : PrimeValue := ⟨255517, pr255517⟩
private theorem pr255523 : Nat.Prime 255523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv1151]) (by decide +kernel)
def pv255523 : PrimeValue := ⟨255523, pr255523⟩
private theorem pr255551 : Nat.Prime 255551 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv19,pv269]) (by decide +kernel)
def pv255551 : PrimeValue := ⟨255551, pr255551⟩
private theorem pr255571 : Nat.Prime 255571 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv1217]) (by decide +kernel)
def pv255571 : PrimeValue := ⟨255571, pr255571⟩
private theorem pr255587 : Nat.Prime 255587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv2719]) (by decide +kernel)
def pv255587 : PrimeValue := ⟨255587, pr255587⟩
private theorem pr255617 : Nat.Prime 255617 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1997]) (by decide +kernel)
def pv255617 : PrimeValue := ⟨255617, pr255617⟩
private theorem pr255641 : Nat.Prime 255641 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv7,pv11,pv83]) (by decide +kernel)
def pv255641 : PrimeValue := ⟨255641, pr255641⟩
private theorem pr255649 : Nat.Prime 255649 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv2663]) (by decide +kernel)
def pv255649 : PrimeValue := ⟨255649, pr255649⟩
private theorem pr255679 : Nat.Prime 255679 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv43,pv991]) (by decide +kernel)
def pv255679 : PrimeValue := ⟨255679, pr255679⟩
private theorem pr255709 : Nat.Prime 255709 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7103]) (by decide +kernel)
def pv255709 : PrimeValue := ⟨255709, pr255709⟩
private theorem pr255733 : Nat.Prime 255733 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv101,pv211]) (by decide +kernel)
def pv255733 : PrimeValue := ⟨255733, pr255733⟩
private theorem pr255743 : Nat.Prime 255743 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv71,pv1801]) (by decide +kernel)
def pv255743 : PrimeValue := ⟨255743, pr255743⟩
private theorem pr255763 : Nat.Prime 255763 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv1093]) (by decide +kernel)
def pv255763 : PrimeValue := ⟨255763, pr255763⟩
private theorem pr255803 : Nat.Prime 255803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79,pv1619]) (by decide +kernel)
def pv255803 : PrimeValue := ⟨255803, pr255803⟩
private theorem pr255841 : Nat.Prime 255841 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv13,pv41]) (by decide +kernel)
def pv255841 : PrimeValue := ⟨255841, pr255841⟩
private theorem pr255847 : Nat.Prime 255847 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv42641]) (by decide +kernel)
def pv255847 : PrimeValue := ⟨255847, pr255847⟩
private theorem pr255851 : Nat.Prime 255851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv17,pv43]) (by decide +kernel)
def pv255851 : PrimeValue := ⟨255851, pr255851⟩
private theorem pr255869 : Nat.Prime 255869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv1361]) (by decide +kernel)
def pv255869 : PrimeValue := ⟨255869, pr255869⟩
private theorem pr255887 : Nat.Prime 255887 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv97,pv1319]) (by decide +kernel)
def pv255887 : PrimeValue := ⟨255887, pr255887⟩
private theorem pr255907 : Nat.Prime 255907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv677]) (by decide +kernel)
def pv255907 : PrimeValue := ⟨255907, pr255907⟩
private theorem pr255919 : Nat.Prime 255919 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv17,pv193]) (by decide +kernel)
def pv255919 : PrimeValue := ⟨255919, pr255919⟩
private theorem pr255923 : Nat.Prime 255923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv3121]) (by decide +kernel)
def pv255923 : PrimeValue := ⟨255923, pr255923⟩
private theorem pr255961 : Nat.Prime 255961 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv5,pv79]) (by decide +kernel)
def pv255961 : PrimeValue := ⟨255961, pr255961⟩
private theorem pr255973 : Nat.Prime 255973 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv83,pv257]) (by decide +kernel)
def pv255973 : PrimeValue := ⟨255973, pr255973⟩
private theorem pr255989 : Nat.Prime 255989 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv63997]) (by decide +kernel)
def pv255989 : PrimeValue := ⟨255989, pr255989⟩
private theorem pr256019 : Nat.Prime 256019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv18287]) (by decide +kernel)
def pv256019 : PrimeValue := ⟨256019, pr256019⟩
private theorem pr256021 : Nat.Prime 256021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv251]) (by decide +kernel)
def pv256021 : PrimeValue := ⟨256021, pr256021⟩
private theorem pr256031 : Nat.Prime 256031 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv25603]) (by decide +kernel)
def pv256031 : PrimeValue := ⟨256031, pr256031⟩
private theorem pr256057 : Nat.Prime 256057 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv47,pv227]) (by decide +kernel)
def pv256057 : PrimeValue := ⟨256057, pr256057⟩
private theorem pr256121 : Nat.Prime 256121 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv19,pv337]) (by decide +kernel)
def pv256121 : PrimeValue := ⟨256121, pr256121⟩
private theorem pr256129 : Nat.Prime 256129 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv23,pv29]) (by decide +kernel)
def pv256129 : PrimeValue := ⟨256129, pr256129⟩
private theorem pr256147 : Nat.Prime 256147 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv3881]) (by decide +kernel)
def pv256147 : PrimeValue := ⟨256147, pr256147⟩
private theorem pr256181 : Nat.Prime 256181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv12809]) (by decide +kernel)
def pv256181 : PrimeValue := ⟨256181, pr256181⟩
private theorem pr256189 : Nat.Prime 256189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv577]) (by decide +kernel)
def pv256189 : PrimeValue := ⟨256189, pr256189⟩
private theorem pr256199 : Nat.Prime 256199 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv128099]) (by decide +kernel)
def pv256199 : PrimeValue := ⟨256199, pr256199⟩
private theorem pr256219 : Nat.Prime 256219 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv42703]) (by decide +kernel)
def pv256219 : PrimeValue := ⟨256219, pr256219⟩
private theorem pr256301 : Nat.Prime 256301 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv233]) (by decide +kernel)
def pv256301 : PrimeValue := ⟨256301, pr256301⟩
private theorem pr256337 : Nat.Prime 256337 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv37,pv433]) (by decide +kernel)
def pv256337 : PrimeValue := ⟨256337, pr256337⟩
private theorem pr256363 : Nat.Prime 256363 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv42727]) (by decide +kernel)
def pv256363 : PrimeValue := ⟨256363, pr256363⟩
private theorem pr256369 : Nat.Prime 256369 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv7,pv109]) (by decide +kernel)
def pv256369 : PrimeValue := ⟨256369, pr256369⟩
private theorem pr256423 : Nat.Prime 256423 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv42737]) (by decide +kernel)
def pv256423 : PrimeValue := ⟨256423, pr256423⟩
private theorem pr256441 : Nat.Prime 256441 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv2137]) (by decide +kernel)
def pv256441 : PrimeValue := ⟨256441, pr256441⟩
private theorem pr256471 : Nat.Prime 256471 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv83,pv103]) (by decide +kernel)
def pv256471 : PrimeValue := ⟨256471, pr256471⟩
private theorem pr256483 : Nat.Prime 256483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv14249]) (by decide +kernel)
def pv256483 : PrimeValue := ⟨256483, pr256483⟩
private theorem pr256489 : Nat.Prime 256489 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv10687]) (by decide +kernel)
def pv256489 : PrimeValue := ⟨256489, pr256489⟩
private theorem pr256499 : Nat.Prime 256499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv89,pv131]) (by decide +kernel)
def pv256499 : PrimeValue := ⟨256499, pr256499⟩
private theorem pr256517 : Nat.Prime 256517 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv4933]) (by decide +kernel)
def pv256517 : PrimeValue := ⟨256517, pr256517⟩
private theorem pr256541 : Nat.Prime 256541 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv101,pv127]) (by decide +kernel)
def pv256541 : PrimeValue := ⟨256541, pr256541⟩
private theorem pr256561 : Nat.Prime 256561 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv1069]) (by decide +kernel)
def pv256561 : PrimeValue := ⟨256561, pr256561⟩
private theorem pr256567 : Nat.Prime 256567 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv61,pv701]) (by decide +kernel)
def pv256567 : PrimeValue := ⟨256567, pr256567⟩
private theorem pr256577 : Nat.Prime 256577 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv211]) (by decide +kernel)
def pv256577 : PrimeValue := ⟨256577, pr256577⟩
private theorem pr256579 : Nat.Prime 256579 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv41,pv149]) (by decide +kernel)
def pv256579 : PrimeValue := ⟨256579, pr256579⟩
private theorem pr256603 : Nat.Prime 256603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv42767]) (by decide +kernel)
def pv256603 : PrimeValue := ⟨256603, pr256603⟩
private theorem pr256643 : Nat.Prime 256643 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv128321]) (by decide +kernel)
def pv256643 : PrimeValue := ⟨256643, pr256643⟩
private theorem pr256661 : Nat.Prime 256661 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv41,pv313]) (by decide +kernel)
def pv256661 : PrimeValue := ⟨256661, pr256661⟩
private theorem pr256721 : Nat.Prime 256721 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv3209]) (by decide +kernel)
def pv256721 : PrimeValue := ⟨256721, pr256721⟩
private theorem pr256723 : Nat.Prime 256723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv42787]) (by decide +kernel)
def pv256723 : PrimeValue := ⟨256723, pr256723⟩
private theorem pr256757 : Nat.Prime 256757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv64189]) (by decide +kernel)
def pv256757 : PrimeValue := ⟨256757, pr256757⟩
private theorem pr256801 : Nat.Prime 256801 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv107]) (by decide +kernel)
def pv256801 : PrimeValue := ⟨256801, pr256801⟩
private theorem pr256813 : Nat.Prime 256813 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv21401]) (by decide +kernel)
def pv256813 : PrimeValue := ⟨256813, pr256813⟩
private theorem pr256873 : Nat.Prime 256873 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv11,pv139]) (by decide +kernel)
def pv256873 : PrimeValue := ⟨256873, pr256873⟩
private theorem pr256889 : Nat.Prime 256889 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv163,pv197]) (by decide +kernel)
def pv256889 : PrimeValue := ⟨256889, pr256889⟩
private theorem pr256903 : Nat.Prime 256903 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv47,pv911]) (by decide +kernel)
def pv256903 : PrimeValue := ⟨256903, pr256903⟩
private theorem pr256939 : Nat.Prime 256939 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv17,pv229]) (by decide +kernel)
def pv256939 : PrimeValue := ⟨256939, pr256939⟩
private theorem pr256957 : Nat.Prime 256957 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv19,pv23]) (by decide +kernel)
def pv256957 : PrimeValue := ⟨256957, pr256957⟩
private theorem pr257053 : Nat.Prime 257053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv691]) (by decide +kernel)
def pv257053 : PrimeValue := ⟨257053, pr257053⟩
private theorem pr257069 : Nat.Prime 257069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv9181]) (by decide +kernel)
def pv257069 : PrimeValue := ⟨257069, pr257069⟩
private theorem pr257077 : Nat.Prime 257077 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv37,pv193]) (by decide +kernel)
def pv257077 : PrimeValue := ⟨257077, pr257077⟩
private theorem pr257093 : Nat.Prime 257093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv5843]) (by decide +kernel)
def pv257093 : PrimeValue := ⟨257093, pr257093⟩
private theorem pr257099 : Nat.Prime 257099 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv128549]) (by decide +kernel)
def pv257099 : PrimeValue := ⟨257099, pr257099⟩
private theorem pr257107 : Nat.Prime 257107 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv73,pv587]) (by decide +kernel)
def pv257107 : PrimeValue := ⟨257107, pr257107⟩
private theorem pr257123 : Nat.Prime 257123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv59,pv2179]) (by decide +kernel)
def pv257123 : PrimeValue := ⟨257123, pr257123⟩
private theorem pr257171 : Nat.Prime 257171 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv25717]) (by decide +kernel)
def pv257171 : PrimeValue := ⟨257171, pr257171⟩
private theorem pr257177 : Nat.Prime 257177 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv31,pv61]) (by decide +kernel)
def pv257177 : PrimeValue := ⟨257177, pr257177⟩
private theorem pr257189 : Nat.Prime 257189 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv113,pv569]) (by decide +kernel)
def pv257189 : PrimeValue := ⟨257189, pr257189⟩
private theorem pr257221 : Nat.Prime 257221 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1429]) (by decide +kernel)
def pv257221 : PrimeValue := ⟨257221, pr257221⟩
private theorem pr257239 : Nat.Prime 257239 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv31,pv461]) (by decide +kernel)
def pv257239 : PrimeValue := ⟨257239, pr257239⟩
private theorem pr257249 : Nat.Prime 257249 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv8039]) (by decide +kernel)
def pv257249 : PrimeValue := ⟨257249, pr257249⟩
private theorem pr257273 : Nat.Prime 257273 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv32159]) (by decide +kernel)
def pv257273 : PrimeValue := ⟨257273, pr257273⟩
private theorem pr257281 : Nat.Prime 257281 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv67]) (by decide +kernel)
def pv257281 : PrimeValue := ⟨257281, pr257281⟩
private theorem pr257321 : Nat.Prime 257321 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv919]) (by decide +kernel)
def pv257321 : PrimeValue := ⟨257321, pr257321⟩
private theorem pr257339 : Nat.Prime 257339 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv128669]) (by decide +kernel)
def pv257339 : PrimeValue := ⟨257339, pr257339⟩
private theorem pr257351 : Nat.Prime 257351 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv5147]) (by decide +kernel)
def pv257351 : PrimeValue := ⟨257351, pr257351⟩
private theorem pr257353 : Nat.Prime 257353 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv10723]) (by decide +kernel)
def pv257353 : PrimeValue := ⟨257353, pr257353⟩
private theorem pr257371 : Nat.Prime 257371 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv23,pv373]) (by decide +kernel)
def pv257371 : PrimeValue := ⟨257371, pr257371⟩
private theorem pr257381 : Nat.Prime 257381 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv17,pv757]) (by decide +kernel)
def pv257381 : PrimeValue := ⟨257381, pr257381⟩
private theorem pr257401 : Nat.Prime 257401 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv11,pv13]) (by decide +kernel)
def pv257401 : PrimeValue := ⟨257401, pr257401⟩
private theorem pr257407 : Nat.Prime 257407 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv42901]) (by decide +kernel)
def pv257407 : PrimeValue := ⟨257407, pr257407⟩
private theorem pr257437 : Nat.Prime 257437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7151]) (by decide +kernel)
def pv257437 : PrimeValue := ⟨257437, pr257437⟩
private theorem pr257443 : Nat.Prime 257443 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv107,pv401]) (by decide +kernel)
def pv257443 : PrimeValue := ⟨257443, pr257443⟩
private theorem pr257473 : Nat.Prime 257473 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv149]) (by decide +kernel)
def pv257473 : PrimeValue := ⟨257473, pr257473⟩
private theorem pr257489 : Nat.Prime 257489 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv11,pv19]) (by decide +kernel)
def pv257489 : PrimeValue := ⟨257489, pr257489⟩
private theorem pr257497 : Nat.Prime 257497 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv10729]) (by decide +kernel)
def pv257497 : PrimeValue := ⟨257497, pr257497⟩
private theorem pr257501 : Nat.Prime 257501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv103]) (by decide +kernel)
def pv257501 : PrimeValue := ⟨257501, pr257501⟩
private theorem pr257519 : Nat.Prime 257519 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv331,pv389]) (by decide +kernel)
def pv257519 : PrimeValue := ⟨257519, pr257519⟩
private theorem pr257539 : Nat.Prime 257539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv42923]) (by decide +kernel)
def pv257539 : PrimeValue := ⟨257539, pr257539⟩
private theorem pr257561 : Nat.Prime 257561 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv47,pv137]) (by decide +kernel)
def pv257561 : PrimeValue := ⟨257561, pr257561⟩
private theorem pr257591 : Nat.Prime 257591 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv25759]) (by decide +kernel)
def pv257591 : PrimeValue := ⟨257591, pr257591⟩
private theorem pr257611 : Nat.Prime 257611 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv31,pv277]) (by decide +kernel)
def pv257611 : PrimeValue := ⟨257611, pr257611⟩
private theorem pr257639 : Nat.Prime 257639 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv128819]) (by decide +kernel)
def pv257639 : PrimeValue := ⟨257639, pr257639⟩
private theorem pr257731 : Nat.Prime 257731 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv71]) (by decide +kernel)
def pv257731 : PrimeValue := ⟨257731, pr257731⟩
private theorem pr257797 : Nat.Prime 257797 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv31]) (by decide +kernel)
def pv257797 : PrimeValue := ⟨257797, pr257797⟩
private theorem pr257837 : Nat.Prime 257837 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv73,pv883]) (by decide +kernel)
def pv257837 : PrimeValue := ⟨257837, pr257837⟩
private theorem pr257861 : Nat.Prime 257861 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv12893]) (by decide +kernel)
def pv257861 : PrimeValue := ⟨257861, pr257861⟩
private theorem pr257867 : Nat.Prime 257867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv113,pv163]) (by decide +kernel)
def pv257867 : PrimeValue := ⟨257867, pr257867⟩
private theorem pr257869 : Nat.Prime 257869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv19,pv29]) (by decide +kernel)
def pv257869 : PrimeValue := ⟨257869, pr257869⟩
private theorem pr257893 : Nat.Prime 257893 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv21491]) (by decide +kernel)
def pv257893 : PrimeValue := ⟨257893, pr257893⟩
private theorem pr257903 : Nat.Prime 257903 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv128951]) (by decide +kernel)
def pv257903 : PrimeValue := ⟨257903, pr257903⟩
private theorem pr257921 : Nat.Prime 257921 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv31]) (by decide +kernel)
def pv257921 : PrimeValue := ⟨257921, pr257921⟩
private theorem pr257953 : Nat.Prime 257953 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2687]) (by decide +kernel)
def pv257953 : PrimeValue := ⟨257953, pr257953⟩
private theorem pr257989 : Nat.Prime 257989 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv21499]) (by decide +kernel)
def pv257989 : PrimeValue := ⟨257989, pr257989⟩
private theorem pr258019 : Nat.Prime 258019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv43003]) (by decide +kernel)
def pv258019 : PrimeValue := ⟨258019, pr258019⟩
private theorem pr258023 : Nat.Prime 258023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv129011]) (by decide +kernel)
def pv258023 : PrimeValue := ⟨258023, pr258023⟩
private theorem pr258031 : Nat.Prime 258031 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv47,pv61]) (by decide +kernel)
def pv258031 : PrimeValue := ⟨258031, pr258031⟩
private theorem pr258067 : Nat.Prime 258067 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv59]) (by decide +kernel)
def pv258067 : PrimeValue := ⟨258067, pr258067⟩
private theorem pr258101 : Nat.Prime 258101 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv29,pv89]) (by decide +kernel)
def pv258101 : PrimeValue := ⟨258101, pr258101⟩
private theorem pr258107 : Nat.Prime 258107 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv31,pv181]) (by decide +kernel)
def pv258107 : PrimeValue := ⟨258107, pr258107⟩
private theorem pr258109 : Nat.Prime 258109 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv137,pv157]) (by decide +kernel)
def pv258109 : PrimeValue := ⟨258109, pr258109⟩
private theorem pr258113 : Nat.Prime 258113 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv37,pv109]) (by decide +kernel)
def pv258113 : PrimeValue := ⟨258113, pr258113⟩
private theorem pr258127 : Nat.Prime 258127 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv3911]) (by decide +kernel)
def pv258127 : PrimeValue := ⟨258127, pr258127⟩
private theorem pr258131 : Nat.Prime 258131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv83,pv311]) (by decide +kernel)
def pv258131 : PrimeValue := ⟨258131, pr258131⟩
private theorem pr258161 : Nat.Prime 258161 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv461]) (by decide +kernel)
def pv258161 : PrimeValue := ⟨258161, pr258161⟩
private theorem pr258197 : Nat.Prime 258197 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv3797]) (by decide +kernel)
def pv258197 : PrimeValue := ⟨258197, pr258197⟩
private theorem pr258241 : Nat.Prime 258241 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv269]) (by decide +kernel)
def pv258241 : PrimeValue := ⟨258241, pr258241⟩
private theorem pr258253 : Nat.Prime 258253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv21521]) (by decide +kernel)
def pv258253 : PrimeValue := ⟨258253, pr258253⟩
private theorem pr258277 : Nat.Prime 258277 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv21523]) (by decide +kernel)
def pv258277 : PrimeValue := ⟨258277, pr258277⟩
private theorem pr258283 : Nat.Prime 258283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4783]) (by decide +kernel)
def pv258283 : PrimeValue := ⟨258283, pr258283⟩
private theorem pr258299 : Nat.Prime 258299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv71,pv107]) (by decide +kernel)
def pv258299 : PrimeValue := ⟨258299, pr258299⟩
private theorem pr258331 : Nat.Prime 258331 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv79,pv109]) (by decide +kernel)
def pv258331 : PrimeValue := ⟨258331, pr258331⟩
private theorem pr258337 : Nat.Prime 258337 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv23]) (by decide +kernel)
def pv258337 : PrimeValue := ⟨258337, pr258337⟩
private theorem pr258353 : Nat.Prime 258353 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv67,pv241]) (by decide +kernel)
def pv258353 : PrimeValue := ⟨258353, pr258353⟩
private theorem pr258373 : Nat.Prime 258373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7177]) (by decide +kernel)
def pv258373 : PrimeValue := ⟨258373, pr258373⟩
private theorem pr258403 : Nat.Prime 258403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv43067]) (by decide +kernel)
def pv258403 : PrimeValue := ⟨258403, pr258403⟩
private theorem pr258407 : Nat.Prime 258407 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv47,pv2749]) (by decide +kernel)
def pv258407 : PrimeValue := ⟨258407, pr258407⟩
private theorem pr258413 : Nat.Prime 258413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv839]) (by decide +kernel)
def pv258413 : PrimeValue := ⟨258413, pr258413⟩
private theorem pr258469 : Nat.Prime 258469 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv7,pv17,pv181]) (by decide +kernel)
def pv258469 : PrimeValue := ⟨258469, pr258469⟩
private theorem pr258487 : Nat.Prime 258487 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv67,pv643]) (by decide +kernel)
def pv258487 : PrimeValue := ⟨258487, pr258487⟩
private theorem pr258491 : Nat.Prime 258491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv25849]) (by decide +kernel)
def pv258491 : PrimeValue := ⟨258491, pr258491⟩
private theorem pr258521 : Nat.Prime 258521 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv23,pv281]) (by decide +kernel)
def pv258521 : PrimeValue := ⟨258521, pr258521⟩
private theorem pr258527 : Nat.Prime 258527 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv129263]) (by decide +kernel)
def pv258527 : PrimeValue := ⟨258527, pr258527⟩
private theorem pr258539 : Nat.Prime 258539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv59,pv313]) (by decide +kernel)
def pv258539 : PrimeValue := ⟨258539, pr258539⟩
private theorem pr258551 : Nat.Prime 258551 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv5171]) (by decide +kernel)
def pv258551 : PrimeValue := ⟨258551, pr258551⟩
private theorem pr258569 : Nat.Prime 258569 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv32321]) (by decide +kernel)
def pv258569 : PrimeValue := ⟨258569, pr258569⟩
private theorem pr258637 : Nat.Prime 258637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv3079]) (by decide +kernel)
def pv258637 : PrimeValue := ⟨258637, pr258637⟩
private theorem pr258691 : Nat.Prime 258691 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv8623]) (by decide +kernel)
def pv258691 : PrimeValue := ⟨258691, pr258691⟩
private theorem pr258703 : Nat.Prime 258703 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv43117]) (by decide +kernel)
def pv258703 : PrimeValue := ⟨258703, pr258703⟩
private theorem pr258707 : Nat.Prime 258707 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv17,pv1087]) (by decide +kernel)
def pv258707 : PrimeValue := ⟨258707, pr258707⟩
private theorem pr258733 : Nat.Prime 258733 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7187]) (by decide +kernel)
def pv258733 : PrimeValue := ⟨258733, pr258733⟩
private theorem pr258743 : Nat.Prime 258743 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv19,pv619]) (by decide +kernel)
def pv258743 : PrimeValue := ⟨258743, pr258743⟩
private theorem pr258787 : Nat.Prime 258787 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv1307]) (by decide +kernel)
def pv258787 : PrimeValue := ⟨258787, pr258787⟩
private theorem pr258803 : Nat.Prime 258803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv129401]) (by decide +kernel)
def pv258803 : PrimeValue := ⟨258803, pr258803⟩
private theorem pr258809 : Nat.Prime 258809 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv17,pv173]) (by decide +kernel)
def pv258809 : PrimeValue := ⟨258809, pr258809⟩
private theorem pr258827 : Nat.Prime 258827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv127,pv1019]) (by decide +kernel)
def pv258827 : PrimeValue := ⟨258827, pr258827⟩
private theorem pr258871 : Nat.Prime 258871 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv8629]) (by decide +kernel)
def pv258871 : PrimeValue := ⟨258871, pr258871⟩
private theorem pr258959 : Nat.Prime 258959 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv53,pv349]) (by decide +kernel)
def pv258959 : PrimeValue := ⟨258959, pr258959⟩
private theorem pr258967 : Nat.Prime 258967 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv14387]) (by decide +kernel)
def pv258967 : PrimeValue := ⟨258967, pr258967⟩
private theorem pr258983 : Nat.Prime 258983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv129491]) (by decide +kernel)
def pv258983 : PrimeValue := ⟨258983, pr258983⟩
private theorem pr258991 : Nat.Prime 258991 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv89,pv97]) (by decide +kernel)
def pv258991 : PrimeValue := ⟨258991, pr258991⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
