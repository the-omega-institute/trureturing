/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table030
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table030.pv76519
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table006
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table016

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr76519 : Nat.Prime 76519 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv109]) (by decide +kernel)
def pv76519 : PrimeValue := ⟨76519, pr76519⟩
private theorem pr76537 : Nat.Prime 76537 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1063]) (by decide +kernel)
def pv76537 : PrimeValue := ⟨76537, pr76537⟩
private theorem pr76541 : Nat.Prime 76541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv43,pv89]) (by decide +kernel)
def pv76541 : PrimeValue := ⟨76541, pr76541⟩
private theorem pr76543 : Nat.Prime 76543 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv12757]) (by decide +kernel)
def pv76543 : PrimeValue := ⟨76543, pr76543⟩
private theorem pr76561 : Nat.Prime 76561 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv11,pv29]) (by decide +kernel)
def pv76561 : PrimeValue := ⟨76561, pr76561⟩
private theorem pr76579 : Nat.Prime 76579 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv12763]) (by decide +kernel)
def pv76579 : PrimeValue := ⟨76579, pr76579⟩
private theorem pr76597 : Nat.Prime 76597 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv491]) (by decide +kernel)
def pv76597 : PrimeValue := ⟨76597, pr76597⟩
private theorem pr76603 : Nat.Prime 76603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv751]) (by decide +kernel)
def pv76603 : PrimeValue := ⟨76603, pr76603⟩
private theorem pr76607 : Nat.Prime 76607 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv38303]) (by decide +kernel)
def pv76607 : PrimeValue := ⟨76607, pr76607⟩
private theorem pr76631 : Nat.Prime 76631 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv79,pv97]) (by decide +kernel)
def pv76631 : PrimeValue := ⟨76631, pr76631⟩
private theorem pr76651 : Nat.Prime 76651 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv73]) (by decide +kernel)
def pv76651 : PrimeValue := ⟨76651, pr76651⟩
private theorem pr76667 : Nat.Prime 76667 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv38333]) (by decide +kernel)
def pv76667 : PrimeValue := ⟨76667, pr76667⟩
private theorem pr76673 : Nat.Prime 76673 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv599]) (by decide +kernel)
def pv76673 : PrimeValue := ⟨76673, pr76673⟩
private theorem pr76679 : Nat.Prime 76679 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv5477]) (by decide +kernel)
def pv76679 : PrimeValue := ⟨76679, pr76679⟩
private theorem pr76697 : Nat.Prime 76697 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv9587]) (by decide +kernel)
def pv76697 : PrimeValue := ⟨76697, pr76697⟩
private theorem pr76733 : Nat.Prime 76733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19183]) (by decide +kernel)
def pv76733 : PrimeValue := ⟨76733, pr76733⟩
private theorem pr76753 : Nat.Prime 76753 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv41]) (by decide +kernel)
def pv76753 : PrimeValue := ⟨76753, pr76753⟩
private theorem pr76757 : Nat.Prime 76757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv619]) (by decide +kernel)
def pv76757 : PrimeValue := ⟨76757, pr76757⟩
private theorem pr76771 : Nat.Prime 76771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv853]) (by decide +kernel)
def pv76771 : PrimeValue := ⟨76771, pr76771⟩
private theorem pr76781 : Nat.Prime 76781 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv349]) (by decide +kernel)
def pv76781 : PrimeValue := ⟨76781, pr76781⟩
private theorem pr76801 : Nat.Prime 76801 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv76801 : PrimeValue := ⟨76801, pr76801⟩
private theorem pr76819 : Nat.Prime 76819 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv31,pv59]) (by decide +kernel)
def pv76819 : PrimeValue := ⟨76819, pr76819⟩
private theorem pr76829 : Nat.Prime 76829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19207]) (by decide +kernel)
def pv76829 : PrimeValue := ⟨76829, pr76829⟩
private theorem pr76831 : Nat.Prime 76831 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv13,pv197]) (by decide +kernel)
def pv76831 : PrimeValue := ⟨76831, pr76831⟩
private theorem pr76837 : Nat.Prime 76837 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv337]) (by decide +kernel)
def pv76837 : PrimeValue := ⟨76837, pr76837⟩
private theorem pr76847 : Nat.Prime 76847 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv11,pv499]) (by decide +kernel)
def pv76847 : PrimeValue := ⟨76847, pr76847⟩
private theorem pr76871 : Nat.Prime 76871 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7687]) (by decide +kernel)
def pv76871 : PrimeValue := ⟨76871, pr76871⟩
private theorem pr76873 : Nat.Prime 76873 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv3203]) (by decide +kernel)
def pv76873 : PrimeValue := ⟨76873, pr76873⟩
private theorem pr76883 : Nat.Prime 76883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv2957]) (by decide +kernel)
def pv76883 : PrimeValue := ⟨76883, pr76883⟩
private theorem pr76907 : Nat.Prime 76907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv38453]) (by decide +kernel)
def pv76907 : PrimeValue := ⟨76907, pr76907⟩
private theorem pr76913 : Nat.Prime 76913 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv19,pv23]) (by decide +kernel)
def pv76913 : PrimeValue := ⟨76913, pr76913⟩
private theorem pr76919 : Nat.Prime 76919 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv38459]) (by decide +kernel)
def pv76919 : PrimeValue := ⟨76919, pr76919⟩
private theorem pr76943 : Nat.Prime 76943 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv17,pv31,pv73]) (by decide +kernel)
def pv76943 : PrimeValue := ⟨76943, pr76943⟩
private theorem pr76949 : Nat.Prime 76949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19237]) (by decide +kernel)
def pv76949 : PrimeValue := ⟨76949, pr76949⟩
private theorem pr76961 : Nat.Prime 76961 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv37]) (by decide +kernel)
def pv76961 : PrimeValue := ⟨76961, pr76961⟩
private theorem pr76963 : Nat.Prime 76963 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv101,pv127]) (by decide +kernel)
def pv76963 : PrimeValue := ⟨76963, pr76963⟩
private theorem pr76991 : Nat.Prime 76991 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv7699]) (by decide +kernel)
def pv76991 : PrimeValue := ⟨76991, pr76991⟩
private theorem pr77003 : Nat.Prime 77003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv38501]) (by decide +kernel)
def pv77003 : PrimeValue := ⟨77003, pr77003⟩
private theorem pr77017 : Nat.Prime 77017 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv3209]) (by decide +kernel)
def pv77017 : PrimeValue := ⟨77017, pr77017⟩
private theorem pr77023 : Nat.Prime 77023 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv389]) (by decide +kernel)
def pv77023 : PrimeValue := ⟨77023, pr77023⟩
private theorem pr77029 : Nat.Prime 77029 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv131]) (by decide +kernel)
def pv77029 : PrimeValue := ⟨77029, pr77029⟩
private theorem pr77041 : Nat.Prime 77041 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv107]) (by decide +kernel)
def pv77041 : PrimeValue := ⟨77041, pr77041⟩
private theorem pr77047 : Nat.Prime 77047 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv12841]) (by decide +kernel)
def pv77047 : PrimeValue := ⟨77047, pr77047⟩
private theorem pr77069 : Nat.Prime 77069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19267]) (by decide +kernel)
def pv77069 : PrimeValue := ⟨77069, pr77069⟩
private theorem pr77081 : Nat.Prime 77081 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv41,pv47]) (by decide +kernel)
def pv77081 : PrimeValue := ⟨77081, pr77081⟩
private theorem pr77093 : Nat.Prime 77093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19273]) (by decide +kernel)
def pv77093 : PrimeValue := ⟨77093, pr77093⟩
private theorem pr77101 : Nat.Prime 77101 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv257]) (by decide +kernel)
def pv77101 : PrimeValue := ⟨77101, pr77101⟩
private theorem pr77137 : Nat.Prime 77137 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv1607]) (by decide +kernel)
def pv77137 : PrimeValue := ⟨77137, pr77137⟩
private theorem pr77141 : Nat.Prime 77141 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv19,pv29]) (by decide +kernel)
def pv77141 : PrimeValue := ⟨77141, pr77141⟩
private theorem pr77153 : Nat.Prime 77153 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2411]) (by decide +kernel)
def pv77153 : PrimeValue := ⟨77153, pr77153⟩
private theorem pr77167 : Nat.Prime 77167 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv1429]) (by decide +kernel)
def pv77167 : PrimeValue := ⟨77167, pr77167⟩
private theorem pr77171 : Nat.Prime 77171 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7717]) (by decide +kernel)
def pv77171 : PrimeValue := ⟨77171, pr77171⟩
private theorem pr77191 : Nat.Prime 77191 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv31,pv83]) (by decide +kernel)
def pv77191 : PrimeValue := ⟨77191, pr77191⟩
private theorem pr77201 : Nat.Prime 77201 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv193]) (by decide +kernel)
def pv77201 : PrimeValue := ⟨77201, pr77201⟩
private theorem pr77213 : Nat.Prime 77213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv97,pv199]) (by decide +kernel)
def pv77213 : PrimeValue := ⟨77213, pr77213⟩
private theorem pr77239 : Nat.Prime 77239 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv613]) (by decide +kernel)
def pv77239 : PrimeValue := ⟨77239, pr77239⟩
private theorem pr77243 : Nat.Prime 77243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv3511]) (by decide +kernel)
def pv77243 : PrimeValue := ⟨77243, pr77243⟩
private theorem pr77249 : Nat.Prime 77249 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv71]) (by decide +kernel)
def pv77249 : PrimeValue := ⟨77249, pr77249⟩
private theorem pr77261 : Nat.Prime 77261 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv3863]) (by decide +kernel)
def pv77261 : PrimeValue := ⟨77261, pr77261⟩
private theorem pr77263 : Nat.Prime 77263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv79,pv163]) (by decide +kernel)
def pv77263 : PrimeValue := ⟨77263, pr77263⟩
private theorem pr77267 : Nat.Prime 77267 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv5519]) (by decide +kernel)
def pv77267 : PrimeValue := ⟨77267, pr77267⟩
private theorem pr77269 : Nat.Prime 77269 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv47,pv137]) (by decide +kernel)
def pv77269 : PrimeValue := ⟨77269, pr77269⟩
private theorem pr77279 : Nat.Prime 77279 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv38639]) (by decide +kernel)
def pv77279 : PrimeValue := ⟨77279, pr77279⟩
private theorem pr77291 : Nat.Prime 77291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv59,pv131]) (by decide +kernel)
def pv77291 : PrimeValue := ⟨77291, pr77291⟩
private theorem pr77317 : Nat.Prime 77317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv379]) (by decide +kernel)
def pv77317 : PrimeValue := ⟨77317, pr77317⟩
private theorem pr77323 : Nat.Prime 77323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv263]) (by decide +kernel)
def pv77323 : PrimeValue := ⟨77323, pr77323⟩
private theorem pr77339 : Nat.Prime 77339 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv38669]) (by decide +kernel)
def pv77339 : PrimeValue := ⟨77339, pr77339⟩
private theorem pr77351 : Nat.Prime 77351 :=
  checkPrime_prime (q := pv47) (ls := [pv2,pv5,pv7,pv13,pv17]) (by decide +kernel)
def pv77351 : PrimeValue := ⟨77351, pr77351⟩
private theorem pr77359 : Nat.Prime 77359 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv12893]) (by decide +kernel)
def pv77359 : PrimeValue := ⟨77359, pr77359⟩
private theorem pr77369 : Nat.Prime 77369 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv509]) (by decide +kernel)
def pv77369 : PrimeValue := ⟨77369, pr77369⟩
private theorem pr77377 : Nat.Prime 77377 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv31]) (by decide +kernel)
def pv77377 : PrimeValue := ⟨77377, pr77377⟩
private theorem pr77383 : Nat.Prime 77383 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv1433]) (by decide +kernel)
def pv77383 : PrimeValue := ⟨77383, pr77383⟩
private theorem pr77417 : Nat.Prime 77417 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv9677]) (by decide +kernel)
def pv77417 : PrimeValue := ⟨77417, pr77417⟩
private theorem pr77419 : Nat.Prime 77419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv17,pv23]) (by decide +kernel)
def pv77419 : PrimeValue := ⟨77419, pr77419⟩
private theorem pr77431 : Nat.Prime 77431 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv29,pv89]) (by decide +kernel)
def pv77431 : PrimeValue := ⟨77431, pr77431⟩
private theorem pr77447 : Nat.Prime 77447 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv38723]) (by decide +kernel)
def pv77447 : PrimeValue := ⟨77447, pr77447⟩
private theorem pr77471 : Nat.Prime 77471 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv61,pv127]) (by decide +kernel)
def pv77471 : PrimeValue := ⟨77471, pr77471⟩
private theorem pr77477 : Nat.Prime 77477 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv2767]) (by decide +kernel)
def pv77477 : PrimeValue := ⟨77477, pr77477⟩
private theorem pr77479 : Nat.Prime 77479 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv37,pv349]) (by decide +kernel)
def pv77479 : PrimeValue := ⟨77479, pr77479⟩
private theorem pr77489 : Nat.Prime 77489 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv167]) (by decide +kernel)
def pv77489 : PrimeValue := ⟨77489, pr77489⟩
private theorem pr77491 : Nat.Prime 77491 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv41]) (by decide +kernel)
def pv77491 : PrimeValue := ⟨77491, pr77491⟩
private theorem pr77509 : Nat.Prime 77509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2153]) (by decide +kernel)
def pv77509 : PrimeValue := ⟨77509, pr77509⟩
private theorem pr77513 : Nat.Prime 77513 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv9689]) (by decide +kernel)
def pv77513 : PrimeValue := ⟨77513, pr77513⟩
private theorem pr77521 : Nat.Prime 77521 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv17,pv19]) (by decide +kernel)
def pv77521 : PrimeValue := ⟨77521, pr77521⟩
private theorem pr77527 : Nat.Prime 77527 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv59,pv73]) (by decide +kernel)
def pv77527 : PrimeValue := ⟨77527, pr77527⟩
private theorem pr77543 : Nat.Prime 77543 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv137,pv283]) (by decide +kernel)
def pv77543 : PrimeValue := ⟨77543, pr77543⟩
private theorem pr77549 : Nat.Prime 77549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19387]) (by decide +kernel)
def pv77549 : PrimeValue := ⟨77549, pr77549⟩
private theorem pr77551 : Nat.Prime 77551 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv11,pv47]) (by decide +kernel)
def pv77551 : PrimeValue := ⟨77551, pr77551⟩
private theorem pr77557 : Nat.Prime 77557 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23,pv281]) (by decide +kernel)
def pv77557 : PrimeValue := ⟨77557, pr77557⟩
private theorem pr77563 : Nat.Prime 77563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv139]) (by decide +kernel)
def pv77563 : PrimeValue := ⟨77563, pr77563⟩
private theorem pr77573 : Nat.Prime 77573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv41,pv43]) (by decide +kernel)
def pv77573 : PrimeValue := ⟨77573, pr77573⟩
private theorem pr77587 : Nat.Prime 77587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv67,pv193]) (by decide +kernel)
def pv77587 : PrimeValue := ⟨77587, pr77587⟩
private theorem pr77591 : Nat.Prime 77591 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv7759]) (by decide +kernel)
def pv77591 : PrimeValue := ⟨77591, pr77591⟩
private theorem pr77611 : Nat.Prime 77611 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv199]) (by decide +kernel)
def pv77611 : PrimeValue := ⟨77611, pr77611⟩
private theorem pr77617 : Nat.Prime 77617 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv11]) (by decide +kernel)
def pv77617 : PrimeValue := ⟨77617, pr77617⟩
private theorem pr77621 : Nat.Prime 77621 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv3881]) (by decide +kernel)
def pv77621 : PrimeValue := ⟨77621, pr77621⟩
private theorem pr77641 : Nat.Prime 77641 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv647]) (by decide +kernel)
def pv77641 : PrimeValue := ⟨77641, pr77641⟩
private theorem pr77647 : Nat.Prime 77647 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv12941]) (by decide +kernel)
def pv77647 : PrimeValue := ⟨77647, pr77647⟩
private theorem pr77659 : Nat.Prime 77659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv43]) (by decide +kernel)
def pv77659 : PrimeValue := ⟨77659, pr77659⟩
private theorem pr77681 : Nat.Prime 77681 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv971]) (by decide +kernel)
def pv77681 : PrimeValue := ⟨77681, pr77681⟩
private theorem pr77687 : Nat.Prime 77687 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv31,pv179]) (by decide +kernel)
def pv77687 : PrimeValue := ⟨77687, pr77687⟩
private theorem pr77689 : Nat.Prime 77689 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv13,pv83]) (by decide +kernel)
def pv77689 : PrimeValue := ⟨77689, pr77689⟩
private theorem pr77699 : Nat.Prime 77699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53,pv733]) (by decide +kernel)
def pv77699 : PrimeValue := ⟨77699, pr77699⟩
private theorem pr77711 : Nat.Prime 77711 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv19,pv409]) (by decide +kernel)
def pv77711 : PrimeValue := ⟨77711, pr77711⟩
private theorem pr77713 : Nat.Prime 77713 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv1619]) (by decide +kernel)
def pv77713 : PrimeValue := ⟨77713, pr77713⟩
private theorem pr77719 : Nat.Prime 77719 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv12953]) (by decide +kernel)
def pv77719 : PrimeValue := ⟨77719, pr77719⟩
private theorem pr77723 : Nat.Prime 77723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv38861]) (by decide +kernel)
def pv77723 : PrimeValue := ⟨77723, pr77723⟩
private theorem pr77731 : Nat.Prime 77731 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv2591]) (by decide +kernel)
def pv77731 : PrimeValue := ⟨77731, pr77731⟩
private theorem pr77743 : Nat.Prime 77743 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv617]) (by decide +kernel)
def pv77743 : PrimeValue := ⟨77743, pr77743⟩
private theorem pr77747 : Nat.Prime 77747 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv38873]) (by decide +kernel)
def pv77747 : PrimeValue := ⟨77747, pr77747⟩
private theorem pr77761 : Nat.Prime 77761 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv77761 : PrimeValue := ⟨77761, pr77761⟩
private theorem pr77773 : Nat.Prime 77773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv6481]) (by decide +kernel)
def pv77773 : PrimeValue := ⟨77773, pr77773⟩
private theorem pr77783 : Nat.Prime 77783 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv38891]) (by decide +kernel)
def pv77783 : PrimeValue := ⟨77783, pr77783⟩
private theorem pr77797 : Nat.Prime 77797 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2161]) (by decide +kernel)
def pv77797 : PrimeValue := ⟨77797, pr77797⟩
private theorem pr77801 : Nat.Prime 77801 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv389]) (by decide +kernel)
def pv77801 : PrimeValue := ⟨77801, pr77801⟩
private theorem pr77813 : Nat.Prime 77813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv397]) (by decide +kernel)
def pv77813 : PrimeValue := ⟨77813, pr77813⟩
private theorem pr77839 : Nat.Prime 77839 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv12973]) (by decide +kernel)
def pv77839 : PrimeValue := ⟨77839, pr77839⟩
private theorem pr77849 : Nat.Prime 77849 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv37,pv263]) (by decide +kernel)
def pv77849 : PrimeValue := ⟨77849, pr77849⟩
private theorem pr77863 : Nat.Prime 77863 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv683]) (by decide +kernel)
def pv77863 : PrimeValue := ⟨77863, pr77863⟩
private theorem pr77867 : Nat.Prime 77867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv38933]) (by decide +kernel)
def pv77867 : PrimeValue := ⟨77867, pr77867⟩
private theorem pr77893 : Nat.Prime 77893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv6491]) (by decide +kernel)
def pv77893 : PrimeValue := ⟨77893, pr77893⟩
private theorem pr77899 : Nat.Prime 77899 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv12983]) (by decide +kernel)
def pv77899 : PrimeValue := ⟨77899, pr77899⟩
private theorem pr77929 : Nat.Prime 77929 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv17,pv191]) (by decide +kernel)
def pv77929 : PrimeValue := ⟨77929, pr77929⟩
private theorem pr77933 : Nat.Prime 77933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19483]) (by decide +kernel)
def pv77933 : PrimeValue := ⟨77933, pr77933⟩
private theorem pr77951 : Nat.Prime 77951 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv1559]) (by decide +kernel)
def pv77951 : PrimeValue := ⟨77951, pr77951⟩
private theorem pr77969 : Nat.Prime 77969 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv443]) (by decide +kernel)
def pv77969 : PrimeValue := ⟨77969, pr77969⟩
private theorem pr77977 : Nat.Prime 77977 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19]) (by decide +kernel)
def pv77977 : PrimeValue := ⟨77977, pr77977⟩
private theorem pr77983 : Nat.Prime 77983 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv41,pv317]) (by decide +kernel)
def pv77983 : PrimeValue := ⟨77983, pr77983⟩
private theorem pr78007 : Nat.Prime 78007 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13001]) (by decide +kernel)
def pv78007 : PrimeValue := ⟨78007, pr78007⟩
private theorem pr78017 : Nat.Prime 78017 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv53]) (by decide +kernel)
def pv78017 : PrimeValue := ⟨78017, pr78017⟩
private theorem pr78031 : Nat.Prime 78031 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv78031 : PrimeValue := ⟨78031, pr78031⟩
private theorem pr78041 : Nat.Prime 78041 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv1951]) (by decide +kernel)
def pv78041 : PrimeValue := ⟨78041, pr78041⟩
private theorem pr78049 : Nat.Prime 78049 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv271]) (by decide +kernel)
def pv78049 : PrimeValue := ⟨78049, pr78049⟩
private theorem pr78059 : Nat.Prime 78059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv1259]) (by decide +kernel)
def pv78059 : PrimeValue := ⟨78059, pr78059⟩
private theorem pr78079 : Nat.Prime 78079 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv3,pv7,pv11,pv13]) (by decide +kernel)
def pv78079 : PrimeValue := ⟨78079, pr78079⟩
private theorem pr78101 : Nat.Prime 78101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv71]) (by decide +kernel)
def pv78101 : PrimeValue := ⟨78101, pr78101⟩
private theorem pr78121 : Nat.Prime 78121 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv31]) (by decide +kernel)
def pv78121 : PrimeValue := ⟨78121, pr78121⟩
private theorem pr78137 : Nat.Prime 78137 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv9767]) (by decide +kernel)
def pv78137 : PrimeValue := ⟨78137, pr78137⟩
private theorem pr78139 : Nat.Prime 78139 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv1447]) (by decide +kernel)
def pv78139 : PrimeValue := ⟨78139, pr78139⟩
private theorem pr78157 : Nat.Prime 78157 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv13,pv167]) (by decide +kernel)
def pv78157 : PrimeValue := ⟨78157, pr78157⟩
private theorem pr78163 : Nat.Prime 78163 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv1861]) (by decide +kernel)
def pv78163 : PrimeValue := ⟨78163, pr78163⟩
private theorem pr78167 : Nat.Prime 78167 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv17,pv19]) (by decide +kernel)
def pv78167 : PrimeValue := ⟨78167, pr78167⟩
private theorem pr78173 : Nat.Prime 78173 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19543]) (by decide +kernel)
def pv78173 : PrimeValue := ⟨78173, pr78173⟩
private theorem pr78179 : Nat.Prime 78179 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv39089]) (by decide +kernel)
def pv78179 : PrimeValue := ⟨78179, pr78179⟩
private theorem pr78191 : Nat.Prime 78191 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv1117]) (by decide +kernel)
def pv78191 : PrimeValue := ⟨78191, pr78191⟩
private theorem pr78193 : Nat.Prime 78193 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv181]) (by decide +kernel)
def pv78193 : PrimeValue := ⟨78193, pr78193⟩
private theorem pr78203 : Nat.Prime 78203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv641]) (by decide +kernel)
def pv78203 : PrimeValue := ⟨78203, pr78203⟩
private theorem pr78229 : Nat.Prime 78229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv41,pv53]) (by decide +kernel)
def pv78229 : PrimeValue := ⟨78229, pr78229⟩
private theorem pr78233 : Nat.Prime 78233 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv11,pv127]) (by decide +kernel)
def pv78233 : PrimeValue := ⟨78233, pr78233⟩
private theorem pr78241 : Nat.Prime 78241 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv163]) (by decide +kernel)
def pv78241 : PrimeValue := ⟨78241, pr78241⟩
private theorem pr78259 : Nat.Prime 78259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13043]) (by decide +kernel)
def pv78259 : PrimeValue := ⟨78259, pr78259⟩
private theorem pr78277 : Nat.Prime 78277 :=
  checkPrime_prime (q := pv59) (ls := [pv2,pv3,pv11,pv593]) (by decide +kernel)
def pv78277 : PrimeValue := ⟨78277, pr78277⟩
private theorem pr78283 : Nat.Prime 78283 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv4349]) (by decide +kernel)
def pv78283 : PrimeValue := ⟨78283, pr78283⟩
private theorem pr78301 : Nat.Prime 78301 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv29]) (by decide +kernel)
def pv78301 : PrimeValue := ⟨78301, pr78301⟩
private theorem pr78307 : Nat.Prime 78307 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv421]) (by decide +kernel)
def pv78307 : PrimeValue := ⟨78307, pr78307⟩
private theorem pr78311 : Nat.Prime 78311 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv5,pv41,pv191]) (by decide +kernel)
def pv78311 : PrimeValue := ⟨78311, pr78311⟩
private theorem pr78317 : Nat.Prime 78317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv2797]) (by decide +kernel)
def pv78317 : PrimeValue := ⟨78317, pr78317⟩
private theorem pr78341 : Nat.Prime 78341 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv3917]) (by decide +kernel)
def pv78341 : PrimeValue := ⟨78341, pr78341⟩
private theorem pr78347 : Nat.Prime 78347 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv911]) (by decide +kernel)
def pv78347 : PrimeValue := ⟨78347, pr78347⟩
private theorem pr78367 : Nat.Prime 78367 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv37,pv353]) (by decide +kernel)
def pv78367 : PrimeValue := ⟨78367, pr78367⟩
private theorem pr78401 : Nat.Prime 78401 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv7]) (by decide +kernel)
def pv78401 : PrimeValue := ⟨78401, pr78401⟩
private theorem pr78427 : Nat.Prime 78427 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv4357]) (by decide +kernel)
def pv78427 : PrimeValue := ⟨78427, pr78427⟩
private theorem pr78437 : Nat.Prime 78437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19609]) (by decide +kernel)
def pv78437 : PrimeValue := ⟨78437, pr78437⟩
private theorem pr78439 : Nat.Prime 78439 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv17,pv769]) (by decide +kernel)
def pv78439 : PrimeValue := ⟨78439, pr78439⟩
private theorem pr78467 : Nat.Prime 78467 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv39233]) (by decide +kernel)
def pv78467 : PrimeValue := ⟨78467, pr78467⟩
private theorem pr78479 : Nat.Prime 78479 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv39239]) (by decide +kernel)
def pv78479 : PrimeValue := ⟨78479, pr78479⟩
private theorem pr78487 : Nat.Prime 78487 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv103,pv127]) (by decide +kernel)
def pv78487 : PrimeValue := ⟨78487, pr78487⟩
private theorem pr78497 : Nat.Prime 78497 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv223]) (by decide +kernel)
def pv78497 : PrimeValue := ⟨78497, pr78497⟩
private theorem pr78509 : Nat.Prime 78509 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv1033]) (by decide +kernel)
def pv78509 : PrimeValue := ⟨78509, pr78509⟩
private theorem pr78511 : Nat.Prime 78511 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv2617]) (by decide +kernel)
def pv78511 : PrimeValue := ⟨78511, pr78511⟩
private theorem pr78517 : Nat.Prime 78517 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv727]) (by decide +kernel)
def pv78517 : PrimeValue := ⟨78517, pr78517⟩
private theorem pr78539 : Nat.Prime 78539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv107,pv367]) (by decide +kernel)
def pv78539 : PrimeValue := ⟨78539, pr78539⟩
private theorem pr78541 : Nat.Prime 78541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv11,pv17]) (by decide +kernel)
def pv78541 : PrimeValue := ⟨78541, pr78541⟩
private theorem pr78553 : Nat.Prime 78553 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1091]) (by decide +kernel)
def pv78553 : PrimeValue := ⟨78553, pr78553⟩
private theorem pr78569 : Nat.Prime 78569 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv23,pv61]) (by decide +kernel)
def pv78569 : PrimeValue := ⟨78569, pr78569⟩
private theorem pr78571 : Nat.Prime 78571 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv97]) (by decide +kernel)
def pv78571 : PrimeValue := ⟨78571, pr78571⟩
private theorem pr78577 : Nat.Prime 78577 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1637]) (by decide +kernel)
def pv78577 : PrimeValue := ⟨78577, pr78577⟩
private theorem pr78583 : Nat.Prime 78583 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv1871]) (by decide +kernel)
def pv78583 : PrimeValue := ⟨78583, pr78583⟩
private theorem pr78593 : Nat.Prime 78593 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv307]) (by decide +kernel)
def pv78593 : PrimeValue := ⟨78593, pr78593⟩
private theorem pr78607 : Nat.Prime 78607 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv397]) (by decide +kernel)
def pv78607 : PrimeValue := ⟨78607, pr78607⟩
private theorem pr78623 : Nat.Prime 78623 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv2069]) (by decide +kernel)
def pv78623 : PrimeValue := ⟨78623, pr78623⟩
private theorem pr78643 : Nat.Prime 78643 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv17,pv257]) (by decide +kernel)
def pv78643 : PrimeValue := ⟨78643, pr78643⟩
private theorem pr78649 : Nat.Prime 78649 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv29,pv113]) (by decide +kernel)
def pv78649 : PrimeValue := ⟨78649, pr78649⟩
private theorem pr78653 : Nat.Prime 78653 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv53]) (by decide +kernel)
def pv78653 : PrimeValue := ⟨78653, pr78653⟩
private theorem pr78691 : Nat.Prime 78691 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv43,pv61]) (by decide +kernel)
def pv78691 : PrimeValue := ⟨78691, pr78691⟩
private theorem pr78697 : Nat.Prime 78697 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1093]) (by decide +kernel)
def pv78697 : PrimeValue := ⟨78697, pr78697⟩
private theorem pr78707 : Nat.Prime 78707 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv29,pv59]) (by decide +kernel)
def pv78707 : PrimeValue := ⟨78707, pr78707⟩
private theorem pr78713 : Nat.Prime 78713 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv9839]) (by decide +kernel)
def pv78713 : PrimeValue := ⟨78713, pr78713⟩
private theorem pr78721 : Nat.Prime 78721 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv41]) (by decide +kernel)
def pv78721 : PrimeValue := ⟨78721, pr78721⟩
private theorem pr78737 : Nat.Prime 78737 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv19,pv37]) (by decide +kernel)
def pv78737 : PrimeValue := ⟨78737, pr78737⟩
private theorem pr78779 : Nat.Prime 78779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv17,pv331]) (by decide +kernel)
def pv78779 : PrimeValue := ⟨78779, pr78779⟩
private theorem pr78781 : Nat.Prime 78781 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv13,pv101]) (by decide +kernel)
def pv78781 : PrimeValue := ⟨78781, pr78781⟩
private theorem pr78787 : Nat.Prime 78787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1459]) (by decide +kernel)
def pv78787 : PrimeValue := ⟨78787, pr78787⟩
private theorem pr78791 : Nat.Prime 78791 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7879]) (by decide +kernel)
def pv78791 : PrimeValue := ⟨78791, pr78791⟩
private theorem pr78797 : Nat.Prime 78797 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19699]) (by decide +kernel)
def pv78797 : PrimeValue := ⟨78797, pr78797⟩
private theorem pr78803 : Nat.Prime 78803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv41]) (by decide +kernel)
def pv78803 : PrimeValue := ⟨78803, pr78803⟩
private theorem pr78809 : Nat.Prime 78809 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv9851]) (by decide +kernel)
def pv78809 : PrimeValue := ⟨78809, pr78809⟩
private theorem pr78823 : Nat.Prime 78823 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29,pv151]) (by decide +kernel)
def pv78823 : PrimeValue := ⟨78823, pr78823⟩
private theorem pr78839 : Nat.Prime 78839 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv39419]) (by decide +kernel)
def pv78839 : PrimeValue := ⟨78839, pr78839⟩
private theorem pr78853 : Nat.Prime 78853 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv6571]) (by decide +kernel)
def pv78853 : PrimeValue := ⟨78853, pr78853⟩
private theorem pr78857 : Nat.Prime 78857 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv9857]) (by decide +kernel)
def pv78857 : PrimeValue := ⟨78857, pr78857⟩
private theorem pr78877 : Nat.Prime 78877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv313]) (by decide +kernel)
def pv78877 : PrimeValue := ⟨78877, pr78877⟩
private theorem pr78887 : Nat.Prime 78887 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv39443]) (by decide +kernel)
def pv78887 : PrimeValue := ⟨78887, pr78887⟩
private theorem pr78889 : Nat.Prime 78889 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv19,pv173]) (by decide +kernel)
def pv78889 : PrimeValue := ⟨78889, pr78889⟩
private theorem pr78893 : Nat.Prime 78893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv163]) (by decide +kernel)
def pv78893 : PrimeValue := ⟨78893, pr78893⟩
private theorem pr78901 : Nat.Prime 78901 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv263]) (by decide +kernel)
def pv78901 : PrimeValue := ⟨78901, pr78901⟩
private theorem pr78919 : Nat.Prime 78919 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv1879]) (by decide +kernel)
def pv78919 : PrimeValue := ⟨78919, pr78919⟩
private theorem pr78929 : Nat.Prime 78929 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv4933]) (by decide +kernel)
def pv78929 : PrimeValue := ⟨78929, pr78929⟩
private theorem pr78941 : Nat.Prime 78941 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv3947]) (by decide +kernel)
def pv78941 : PrimeValue := ⟨78941, pr78941⟩
private theorem pr78977 : Nat.Prime 78977 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv617]) (by decide +kernel)
def pv78977 : PrimeValue := ⟨78977, pr78977⟩
private theorem pr78979 : Nat.Prime 78979 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13163]) (by decide +kernel)
def pv78979 : PrimeValue := ⟨78979, pr78979⟩
private theorem pr78989 : Nat.Prime 78989 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv13,pv31]) (by decide +kernel)
def pv78989 : PrimeValue := ⟨78989, pr78989⟩
private theorem pr79031 : Nat.Prime 79031 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv1129]) (by decide +kernel)
def pv79031 : PrimeValue := ⟨79031, pr79031⟩
private theorem pr79039 : Nat.Prime 79039 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv4391]) (by decide +kernel)
def pv79039 : PrimeValue := ⟨79039, pr79039⟩
private theorem pr79043 : Nat.Prime 79043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv39521]) (by decide +kernel)
def pv79043 : PrimeValue := ⟨79043, pr79043⟩
private theorem pr79063 : Nat.Prime 79063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13177]) (by decide +kernel)
def pv79063 : PrimeValue := ⟨79063, pr79063⟩
private theorem pr79087 : Nat.Prime 79087 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv269]) (by decide +kernel)
def pv79087 : PrimeValue := ⟨79087, pr79087⟩
private theorem pr79103 : Nat.Prime 79103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv39551]) (by decide +kernel)
def pv79103 : PrimeValue := ⟨79103, pr79103⟩
private theorem pr79111 : Nat.Prime 79111 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv293]) (by decide +kernel)
def pv79111 : PrimeValue := ⟨79111, pr79111⟩
private theorem pr79133 : Nat.Prime 79133 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv73,pv271]) (by decide +kernel)
def pv79133 : PrimeValue := ⟨79133, pr79133⟩
private theorem pr79139 : Nat.Prime 79139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv39569]) (by decide +kernel)
def pv79139 : PrimeValue := ⟨79139, pr79139⟩
private theorem pr79147 : Nat.Prime 79147 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4397]) (by decide +kernel)
def pv79147 : PrimeValue := ⟨79147, pr79147⟩
private theorem pr79151 : Nat.Prime 79151 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv1583]) (by decide +kernel)
def pv79151 : PrimeValue := ⟨79151, pr79151⟩
private theorem pr79153 : Nat.Prime 79153 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv17,pv97]) (by decide +kernel)
def pv79153 : PrimeValue := ⟨79153, pr79153⟩
private theorem pr79159 : Nat.Prime 79159 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv79,pv167]) (by decide +kernel)
def pv79159 : PrimeValue := ⟨79159, pr79159⟩
private theorem pr79181 : Nat.Prime 79181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv37,pv107]) (by decide +kernel)
def pv79181 : PrimeValue := ⟨79181, pr79181⟩
private theorem pr79187 : Nat.Prime 79187 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv137]) (by decide +kernel)
def pv79187 : PrimeValue := ⟨79187, pr79187⟩
private theorem pr79193 : Nat.Prime 79193 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv521]) (by decide +kernel)
def pv79193 : PrimeValue := ⟨79193, pr79193⟩
private theorem pr79201 : Nat.Prime 79201 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv79201 : PrimeValue := ⟨79201, pr79201⟩
private theorem pr79229 : Nat.Prime 79229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv683]) (by decide +kernel)
def pv79229 : PrimeValue := ⟨79229, pr79229⟩
private theorem pr79241 : Nat.Prime 79241 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv283]) (by decide +kernel)
def pv79241 : PrimeValue := ⟨79241, pr79241⟩
private theorem pr79259 : Nat.Prime 79259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv1723]) (by decide +kernel)
def pv79259 : PrimeValue := ⟨79259, pr79259⟩
private theorem pr79273 : Nat.Prime 79273 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv367]) (by decide +kernel)
def pv79273 : PrimeValue := ⟨79273, pr79273⟩
private theorem pr79279 : Nat.Prime 79279 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv73,pv181]) (by decide +kernel)
def pv79279 : PrimeValue := ⟨79279, pr79279⟩
private theorem pr79283 : Nat.Prime 79283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv809]) (by decide +kernel)
def pv79283 : PrimeValue := ⟨79283, pr79283⟩
private theorem pr79301 : Nat.Prime 79301 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv61]) (by decide +kernel)
def pv79301 : PrimeValue := ⟨79301, pr79301⟩
private theorem pr79309 : Nat.Prime 79309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2203]) (by decide +kernel)
def pv79309 : PrimeValue := ⟨79309, pr79309⟩
private theorem pr79319 : Nat.Prime 79319 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv39659]) (by decide +kernel)
def pv79319 : PrimeValue := ⟨79319, pr79319⟩
private theorem pr79333 : Nat.Prime 79333 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv601]) (by decide +kernel)
def pv79333 : PrimeValue := ⟨79333, pr79333⟩
private theorem pr79337 : Nat.Prime 79337 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv47,pv211]) (by decide +kernel)
def pv79337 : PrimeValue := ⟨79337, pr79337⟩
private theorem pr79349 : Nat.Prime 79349 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv83,pv239]) (by decide +kernel)
def pv79349 : PrimeValue := ⟨79349, pr79349⟩
private theorem pr79357 : Nat.Prime 79357 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv17,pv389]) (by decide +kernel)
def pv79357 : PrimeValue := ⟨79357, pr79357⟩
private theorem pr79367 : Nat.Prime 79367 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv5669]) (by decide +kernel)
def pv79367 : PrimeValue := ⟨79367, pr79367⟩
private theorem pr79379 : Nat.Prime 79379 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv43,pv71]) (by decide +kernel)
def pv79379 : PrimeValue := ⟨79379, pr79379⟩
private theorem pr79393 : Nat.Prime 79393 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv827]) (by decide +kernel)
def pv79393 : PrimeValue := ⟨79393, pr79393⟩
private theorem pr79397 : Nat.Prime 79397 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv863]) (by decide +kernel)
def pv79397 : PrimeValue := ⟨79397, pr79397⟩
private theorem pr79399 : Nat.Prime 79399 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv401]) (by decide +kernel)
def pv79399 : PrimeValue := ⟨79399, pr79399⟩
private theorem pr79411 : Nat.Prime 79411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv2647]) (by decide +kernel)
def pv79411 : PrimeValue := ⟨79411, pr79411⟩
private theorem pr79423 : Nat.Prime 79423 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv31,pv61]) (by decide +kernel)
def pv79423 : PrimeValue := ⟨79423, pr79423⟩
private theorem pr79427 : Nat.Prime 79427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv151,pv263]) (by decide +kernel)
def pv79427 : PrimeValue := ⟨79427, pr79427⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
