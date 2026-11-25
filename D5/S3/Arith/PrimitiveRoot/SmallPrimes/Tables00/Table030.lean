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
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr76519 : PrimeCertificate 76519 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv109]) (by decide +kernel)
def pv76519 : PrimeValue := ⟨76519, pr76519⟩
private theorem pr76537 : PrimeCertificate 76537 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1063]) (by decide +kernel)
def pv76537 : PrimeValue := ⟨76537, pr76537⟩
private theorem pr76541 : PrimeCertificate 76541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv43,pv89]) (by decide +kernel)
def pv76541 : PrimeValue := ⟨76541, pr76541⟩
private theorem pr76543 : PrimeCertificate 76543 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv12757]) (by decide +kernel)
def pv76543 : PrimeValue := ⟨76543, pr76543⟩
private theorem pr76561 : PrimeCertificate 76561 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv11,pv29]) (by decide +kernel)
def pv76561 : PrimeValue := ⟨76561, pr76561⟩
private theorem pr76579 : PrimeCertificate 76579 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv12763]) (by decide +kernel)
def pv76579 : PrimeValue := ⟨76579, pr76579⟩
private theorem pr76597 : PrimeCertificate 76597 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv491]) (by decide +kernel)
def pv76597 : PrimeValue := ⟨76597, pr76597⟩
private theorem pr76603 : PrimeCertificate 76603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv751]) (by decide +kernel)
def pv76603 : PrimeValue := ⟨76603, pr76603⟩
private theorem pr76607 : PrimeCertificate 76607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv38303]) (by decide +kernel)
def pv76607 : PrimeValue := ⟨76607, pr76607⟩
private theorem pr76631 : PrimeCertificate 76631 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv79,pv97]) (by decide +kernel)
def pv76631 : PrimeValue := ⟨76631, pr76631⟩
private theorem pr76651 : PrimeCertificate 76651 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv73]) (by decide +kernel)
def pv76651 : PrimeValue := ⟨76651, pr76651⟩
private theorem pr76667 : PrimeCertificate 76667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv38333]) (by decide +kernel)
def pv76667 : PrimeValue := ⟨76667, pr76667⟩
private theorem pr76673 : PrimeCertificate 76673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv599]) (by decide +kernel)
def pv76673 : PrimeValue := ⟨76673, pr76673⟩
private theorem pr76679 : PrimeCertificate 76679 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv5477]) (by decide +kernel)
def pv76679 : PrimeValue := ⟨76679, pr76679⟩
private theorem pr76697 : PrimeCertificate 76697 :=
  certifyPrime (q := pv3) (ls := [pv2,pv9587]) (by decide +kernel)
def pv76697 : PrimeValue := ⟨76697, pr76697⟩
private theorem pr76733 : PrimeCertificate 76733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19183]) (by decide +kernel)
def pv76733 : PrimeValue := ⟨76733, pr76733⟩
private theorem pr76753 : PrimeCertificate 76753 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv41]) (by decide +kernel)
def pv76753 : PrimeValue := ⟨76753, pr76753⟩
private theorem pr76757 : PrimeCertificate 76757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv619]) (by decide +kernel)
def pv76757 : PrimeValue := ⟨76757, pr76757⟩
private theorem pr76771 : PrimeCertificate 76771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv853]) (by decide +kernel)
def pv76771 : PrimeValue := ⟨76771, pr76771⟩
private theorem pr76781 : PrimeCertificate 76781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv349]) (by decide +kernel)
def pv76781 : PrimeValue := ⟨76781, pr76781⟩
private theorem pr76801 : PrimeCertificate 76801 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv76801 : PrimeValue := ⟨76801, pr76801⟩
private theorem pr76819 : PrimeCertificate 76819 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv31,pv59]) (by decide +kernel)
def pv76819 : PrimeValue := ⟨76819, pr76819⟩
private theorem pr76829 : PrimeCertificate 76829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19207]) (by decide +kernel)
def pv76829 : PrimeValue := ⟨76829, pr76829⟩
private theorem pr76831 : PrimeCertificate 76831 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv13,pv197]) (by decide +kernel)
def pv76831 : PrimeValue := ⟨76831, pr76831⟩
private theorem pr76837 : PrimeCertificate 76837 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv337]) (by decide +kernel)
def pv76837 : PrimeValue := ⟨76837, pr76837⟩
private theorem pr76847 : PrimeCertificate 76847 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11,pv499]) (by decide +kernel)
def pv76847 : PrimeValue := ⟨76847, pr76847⟩
private theorem pr76871 : PrimeCertificate 76871 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7687]) (by decide +kernel)
def pv76871 : PrimeValue := ⟨76871, pr76871⟩
private theorem pr76873 : PrimeCertificate 76873 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv3203]) (by decide +kernel)
def pv76873 : PrimeValue := ⟨76873, pr76873⟩
private theorem pr76883 : PrimeCertificate 76883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv2957]) (by decide +kernel)
def pv76883 : PrimeValue := ⟨76883, pr76883⟩
private theorem pr76907 : PrimeCertificate 76907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv38453]) (by decide +kernel)
def pv76907 : PrimeValue := ⟨76907, pr76907⟩
private theorem pr76913 : PrimeCertificate 76913 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv19,pv23]) (by decide +kernel)
def pv76913 : PrimeValue := ⟨76913, pr76913⟩
private theorem pr76919 : PrimeCertificate 76919 :=
  certifyPrime (q := pv13) (ls := [pv2,pv38459]) (by decide +kernel)
def pv76919 : PrimeValue := ⟨76919, pr76919⟩
private theorem pr76943 : PrimeCertificate 76943 :=
  certifyPrime (q := pv11) (ls := [pv2,pv17,pv31,pv73]) (by decide +kernel)
def pv76943 : PrimeValue := ⟨76943, pr76943⟩
private theorem pr76949 : PrimeCertificate 76949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19237]) (by decide +kernel)
def pv76949 : PrimeValue := ⟨76949, pr76949⟩
private theorem pr76961 : PrimeCertificate 76961 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv37]) (by decide +kernel)
def pv76961 : PrimeValue := ⟨76961, pr76961⟩
private theorem pr76963 : PrimeCertificate 76963 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv101,pv127]) (by decide +kernel)
def pv76963 : PrimeValue := ⟨76963, pr76963⟩
private theorem pr76991 : PrimeCertificate 76991 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7699]) (by decide +kernel)
def pv76991 : PrimeValue := ⟨76991, pr76991⟩
private theorem pr77003 : PrimeCertificate 77003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv38501]) (by decide +kernel)
def pv77003 : PrimeValue := ⟨77003, pr77003⟩
private theorem pr77017 : PrimeCertificate 77017 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv3209]) (by decide +kernel)
def pv77017 : PrimeValue := ⟨77017, pr77017⟩
private theorem pr77023 : PrimeCertificate 77023 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv389]) (by decide +kernel)
def pv77023 : PrimeValue := ⟨77023, pr77023⟩
private theorem pr77029 : PrimeCertificate 77029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv131]) (by decide +kernel)
def pv77029 : PrimeValue := ⟨77029, pr77029⟩
private theorem pr77041 : PrimeCertificate 77041 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv107]) (by decide +kernel)
def pv77041 : PrimeValue := ⟨77041, pr77041⟩
private theorem pr77047 : PrimeCertificate 77047 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv12841]) (by decide +kernel)
def pv77047 : PrimeValue := ⟨77047, pr77047⟩
private theorem pr77069 : PrimeCertificate 77069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19267]) (by decide +kernel)
def pv77069 : PrimeValue := ⟨77069, pr77069⟩
private theorem pr77081 : PrimeCertificate 77081 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv41,pv47]) (by decide +kernel)
def pv77081 : PrimeValue := ⟨77081, pr77081⟩
private theorem pr77093 : PrimeCertificate 77093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19273]) (by decide +kernel)
def pv77093 : PrimeValue := ⟨77093, pr77093⟩
private theorem pr77101 : PrimeCertificate 77101 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv257]) (by decide +kernel)
def pv77101 : PrimeValue := ⟨77101, pr77101⟩
private theorem pr77137 : PrimeCertificate 77137 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv1607]) (by decide +kernel)
def pv77137 : PrimeValue := ⟨77137, pr77137⟩
private theorem pr77141 : PrimeCertificate 77141 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv19,pv29]) (by decide +kernel)
def pv77141 : PrimeValue := ⟨77141, pr77141⟩
private theorem pr77153 : PrimeCertificate 77153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2411]) (by decide +kernel)
def pv77153 : PrimeValue := ⟨77153, pr77153⟩
private theorem pr77167 : PrimeCertificate 77167 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv1429]) (by decide +kernel)
def pv77167 : PrimeValue := ⟨77167, pr77167⟩
private theorem pr77171 : PrimeCertificate 77171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7717]) (by decide +kernel)
def pv77171 : PrimeValue := ⟨77171, pr77171⟩
private theorem pr77191 : PrimeCertificate 77191 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv31,pv83]) (by decide +kernel)
def pv77191 : PrimeValue := ⟨77191, pr77191⟩
private theorem pr77201 : PrimeCertificate 77201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv193]) (by decide +kernel)
def pv77201 : PrimeValue := ⟨77201, pr77201⟩
private theorem pr77213 : PrimeCertificate 77213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv97,pv199]) (by decide +kernel)
def pv77213 : PrimeValue := ⟨77213, pr77213⟩
private theorem pr77239 : PrimeCertificate 77239 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv613]) (by decide +kernel)
def pv77239 : PrimeValue := ⟨77239, pr77239⟩
private theorem pr77243 : PrimeCertificate 77243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv3511]) (by decide +kernel)
def pv77243 : PrimeValue := ⟨77243, pr77243⟩
private theorem pr77249 : PrimeCertificate 77249 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv71]) (by decide +kernel)
def pv77249 : PrimeValue := ⟨77249, pr77249⟩
private theorem pr77261 : PrimeCertificate 77261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv3863]) (by decide +kernel)
def pv77261 : PrimeValue := ⟨77261, pr77261⟩
private theorem pr77263 : PrimeCertificate 77263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv79,pv163]) (by decide +kernel)
def pv77263 : PrimeValue := ⟨77263, pr77263⟩
private theorem pr77267 : PrimeCertificate 77267 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv5519]) (by decide +kernel)
def pv77267 : PrimeValue := ⟨77267, pr77267⟩
private theorem pr77269 : PrimeCertificate 77269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv137]) (by decide +kernel)
def pv77269 : PrimeValue := ⟨77269, pr77269⟩
private theorem pr77279 : PrimeCertificate 77279 :=
  certifyPrime (q := pv11) (ls := [pv2,pv38639]) (by decide +kernel)
def pv77279 : PrimeValue := ⟨77279, pr77279⟩
private theorem pr77291 : PrimeCertificate 77291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv59,pv131]) (by decide +kernel)
def pv77291 : PrimeValue := ⟨77291, pr77291⟩
private theorem pr77317 : PrimeCertificate 77317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv379]) (by decide +kernel)
def pv77317 : PrimeValue := ⟨77317, pr77317⟩
private theorem pr77323 : PrimeCertificate 77323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv263]) (by decide +kernel)
def pv77323 : PrimeValue := ⟨77323, pr77323⟩
private theorem pr77339 : PrimeCertificate 77339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv38669]) (by decide +kernel)
def pv77339 : PrimeValue := ⟨77339, pr77339⟩
private theorem pr77351 : PrimeCertificate 77351 :=
  certifyPrime (q := pv47) (ls := [pv2,pv5,pv7,pv13,pv17]) (by decide +kernel)
def pv77351 : PrimeValue := ⟨77351, pr77351⟩
private theorem pr77359 : PrimeCertificate 77359 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv12893]) (by decide +kernel)
def pv77359 : PrimeValue := ⟨77359, pr77359⟩
private theorem pr77369 : PrimeCertificate 77369 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv509]) (by decide +kernel)
def pv77369 : PrimeValue := ⟨77369, pr77369⟩
private theorem pr77377 : PrimeCertificate 77377 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv31]) (by decide +kernel)
def pv77377 : PrimeValue := ⟨77377, pr77377⟩
private theorem pr77383 : PrimeCertificate 77383 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1433]) (by decide +kernel)
def pv77383 : PrimeValue := ⟨77383, pr77383⟩
private theorem pr77417 : PrimeCertificate 77417 :=
  certifyPrime (q := pv3) (ls := [pv2,pv9677]) (by decide +kernel)
def pv77417 : PrimeValue := ⟨77417, pr77417⟩
private theorem pr77419 : PrimeCertificate 77419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv17,pv23]) (by decide +kernel)
def pv77419 : PrimeValue := ⟨77419, pr77419⟩
private theorem pr77431 : PrimeCertificate 77431 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv29,pv89]) (by decide +kernel)
def pv77431 : PrimeValue := ⟨77431, pr77431⟩
private theorem pr77447 : PrimeCertificate 77447 :=
  certifyPrime (q := pv5) (ls := [pv2,pv38723]) (by decide +kernel)
def pv77447 : PrimeValue := ⟨77447, pr77447⟩
private theorem pr77471 : PrimeCertificate 77471 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv61,pv127]) (by decide +kernel)
def pv77471 : PrimeValue := ⟨77471, pr77471⟩
private theorem pr77477 : PrimeCertificate 77477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv2767]) (by decide +kernel)
def pv77477 : PrimeValue := ⟨77477, pr77477⟩
private theorem pr77479 : PrimeCertificate 77479 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv37,pv349]) (by decide +kernel)
def pv77479 : PrimeValue := ⟨77479, pr77479⟩
private theorem pr77489 : PrimeCertificate 77489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv167]) (by decide +kernel)
def pv77489 : PrimeValue := ⟨77489, pr77489⟩
private theorem pr77491 : PrimeCertificate 77491 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv41]) (by decide +kernel)
def pv77491 : PrimeValue := ⟨77491, pr77491⟩
private theorem pr77509 : PrimeCertificate 77509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv2153]) (by decide +kernel)
def pv77509 : PrimeValue := ⟨77509, pr77509⟩
private theorem pr77513 : PrimeCertificate 77513 :=
  certifyPrime (q := pv3) (ls := [pv2,pv9689]) (by decide +kernel)
def pv77513 : PrimeValue := ⟨77513, pr77513⟩
private theorem pr77521 : PrimeCertificate 77521 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv17,pv19]) (by decide +kernel)
def pv77521 : PrimeValue := ⟨77521, pr77521⟩
private theorem pr77527 : PrimeCertificate 77527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv59,pv73]) (by decide +kernel)
def pv77527 : PrimeValue := ⟨77527, pr77527⟩
private theorem pr77543 : PrimeCertificate 77543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv137,pv283]) (by decide +kernel)
def pv77543 : PrimeValue := ⟨77543, pr77543⟩
private theorem pr77549 : PrimeCertificate 77549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19387]) (by decide +kernel)
def pv77549 : PrimeValue := ⟨77549, pr77549⟩
private theorem pr77551 : PrimeCertificate 77551 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv11,pv47]) (by decide +kernel)
def pv77551 : PrimeValue := ⟨77551, pr77551⟩
private theorem pr77557 : PrimeCertificate 77557 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv281]) (by decide +kernel)
def pv77557 : PrimeValue := ⟨77557, pr77557⟩
private theorem pr77563 : PrimeCertificate 77563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv139]) (by decide +kernel)
def pv77563 : PrimeValue := ⟨77563, pr77563⟩
private theorem pr77573 : PrimeCertificate 77573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv41,pv43]) (by decide +kernel)
def pv77573 : PrimeValue := ⟨77573, pr77573⟩
private theorem pr77587 : PrimeCertificate 77587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv67,pv193]) (by decide +kernel)
def pv77587 : PrimeValue := ⟨77587, pr77587⟩
private theorem pr77591 : PrimeCertificate 77591 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7759]) (by decide +kernel)
def pv77591 : PrimeValue := ⟨77591, pr77591⟩
private theorem pr77611 : PrimeCertificate 77611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv199]) (by decide +kernel)
def pv77611 : PrimeValue := ⟨77611, pr77611⟩
private theorem pr77617 : PrimeCertificate 77617 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv11]) (by decide +kernel)
def pv77617 : PrimeValue := ⟨77617, pr77617⟩
private theorem pr77621 : PrimeCertificate 77621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv3881]) (by decide +kernel)
def pv77621 : PrimeValue := ⟨77621, pr77621⟩
private theorem pr77641 : PrimeCertificate 77641 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv647]) (by decide +kernel)
def pv77641 : PrimeValue := ⟨77641, pr77641⟩
private theorem pr77647 : PrimeCertificate 77647 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv12941]) (by decide +kernel)
def pv77647 : PrimeValue := ⟨77647, pr77647⟩
private theorem pr77659 : PrimeCertificate 77659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv43]) (by decide +kernel)
def pv77659 : PrimeValue := ⟨77659, pr77659⟩
private theorem pr77681 : PrimeCertificate 77681 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv971]) (by decide +kernel)
def pv77681 : PrimeValue := ⟨77681, pr77681⟩
private theorem pr77687 : PrimeCertificate 77687 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv31,pv179]) (by decide +kernel)
def pv77687 : PrimeValue := ⟨77687, pr77687⟩
private theorem pr77689 : PrimeCertificate 77689 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv13,pv83]) (by decide +kernel)
def pv77689 : PrimeValue := ⟨77689, pr77689⟩
private theorem pr77699 : PrimeCertificate 77699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv733]) (by decide +kernel)
def pv77699 : PrimeValue := ⟨77699, pr77699⟩
private theorem pr77711 : PrimeCertificate 77711 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv19,pv409]) (by decide +kernel)
def pv77711 : PrimeValue := ⟨77711, pr77711⟩
private theorem pr77713 : PrimeCertificate 77713 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1619]) (by decide +kernel)
def pv77713 : PrimeValue := ⟨77713, pr77713⟩
private theorem pr77719 : PrimeCertificate 77719 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv12953]) (by decide +kernel)
def pv77719 : PrimeValue := ⟨77719, pr77719⟩
private theorem pr77723 : PrimeCertificate 77723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv38861]) (by decide +kernel)
def pv77723 : PrimeValue := ⟨77723, pr77723⟩
private theorem pr77731 : PrimeCertificate 77731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv2591]) (by decide +kernel)
def pv77731 : PrimeValue := ⟨77731, pr77731⟩
private theorem pr77743 : PrimeCertificate 77743 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv617]) (by decide +kernel)
def pv77743 : PrimeValue := ⟨77743, pr77743⟩
private theorem pr77747 : PrimeCertificate 77747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv38873]) (by decide +kernel)
def pv77747 : PrimeValue := ⟨77747, pr77747⟩
private theorem pr77761 : PrimeCertificate 77761 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv77761 : PrimeValue := ⟨77761, pr77761⟩
private theorem pr77773 : PrimeCertificate 77773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv6481]) (by decide +kernel)
def pv77773 : PrimeValue := ⟨77773, pr77773⟩
private theorem pr77783 : PrimeCertificate 77783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv38891]) (by decide +kernel)
def pv77783 : PrimeValue := ⟨77783, pr77783⟩
private theorem pr77797 : PrimeCertificate 77797 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2161]) (by decide +kernel)
def pv77797 : PrimeValue := ⟨77797, pr77797⟩
private theorem pr77801 : PrimeCertificate 77801 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv389]) (by decide +kernel)
def pv77801 : PrimeValue := ⟨77801, pr77801⟩
private theorem pr77813 : PrimeCertificate 77813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv397]) (by decide +kernel)
def pv77813 : PrimeValue := ⟨77813, pr77813⟩
private theorem pr77839 : PrimeCertificate 77839 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv12973]) (by decide +kernel)
def pv77839 : PrimeValue := ⟨77839, pr77839⟩
private theorem pr77849 : PrimeCertificate 77849 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv263]) (by decide +kernel)
def pv77849 : PrimeValue := ⟨77849, pr77849⟩
private theorem pr77863 : PrimeCertificate 77863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv683]) (by decide +kernel)
def pv77863 : PrimeValue := ⟨77863, pr77863⟩
private theorem pr77867 : PrimeCertificate 77867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv38933]) (by decide +kernel)
def pv77867 : PrimeValue := ⟨77867, pr77867⟩
private theorem pr77893 : PrimeCertificate 77893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv6491]) (by decide +kernel)
def pv77893 : PrimeValue := ⟨77893, pr77893⟩
private theorem pr77899 : PrimeCertificate 77899 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv12983]) (by decide +kernel)
def pv77899 : PrimeValue := ⟨77899, pr77899⟩
private theorem pr77929 : PrimeCertificate 77929 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv17,pv191]) (by decide +kernel)
def pv77929 : PrimeValue := ⟨77929, pr77929⟩
private theorem pr77933 : PrimeCertificate 77933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19483]) (by decide +kernel)
def pv77933 : PrimeValue := ⟨77933, pr77933⟩
private theorem pr77951 : PrimeCertificate 77951 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv1559]) (by decide +kernel)
def pv77951 : PrimeValue := ⟨77951, pr77951⟩
private theorem pr77969 : PrimeCertificate 77969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv443]) (by decide +kernel)
def pv77969 : PrimeValue := ⟨77969, pr77969⟩
private theorem pr77977 : PrimeCertificate 77977 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19]) (by decide +kernel)
def pv77977 : PrimeValue := ⟨77977, pr77977⟩
private theorem pr77983 : PrimeCertificate 77983 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41,pv317]) (by decide +kernel)
def pv77983 : PrimeValue := ⟨77983, pr77983⟩
private theorem pr78007 : PrimeCertificate 78007 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13001]) (by decide +kernel)
def pv78007 : PrimeValue := ⟨78007, pr78007⟩
private theorem pr78017 : PrimeCertificate 78017 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv53]) (by decide +kernel)
def pv78017 : PrimeValue := ⟨78017, pr78017⟩
private theorem pr78031 : PrimeCertificate 78031 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv78031 : PrimeValue := ⟨78031, pr78031⟩
private theorem pr78041 : PrimeCertificate 78041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1951]) (by decide +kernel)
def pv78041 : PrimeValue := ⟨78041, pr78041⟩
private theorem pr78049 : PrimeCertificate 78049 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv271]) (by decide +kernel)
def pv78049 : PrimeValue := ⟨78049, pr78049⟩
private theorem pr78059 : PrimeCertificate 78059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv1259]) (by decide +kernel)
def pv78059 : PrimeValue := ⟨78059, pr78059⟩
private theorem pr78079 : PrimeCertificate 78079 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv7,pv11,pv13]) (by decide +kernel)
def pv78079 : PrimeValue := ⟨78079, pr78079⟩
private theorem pr78101 : PrimeCertificate 78101 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv71]) (by decide +kernel)
def pv78101 : PrimeValue := ⟨78101, pr78101⟩
private theorem pr78121 : PrimeCertificate 78121 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv31]) (by decide +kernel)
def pv78121 : PrimeValue := ⟨78121, pr78121⟩
private theorem pr78137 : PrimeCertificate 78137 :=
  certifyPrime (q := pv3) (ls := [pv2,pv9767]) (by decide +kernel)
def pv78137 : PrimeValue := ⟨78137, pr78137⟩
private theorem pr78139 : PrimeCertificate 78139 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1447]) (by decide +kernel)
def pv78139 : PrimeValue := ⟨78139, pr78139⟩
private theorem pr78157 : PrimeCertificate 78157 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv13,pv167]) (by decide +kernel)
def pv78157 : PrimeValue := ⟨78157, pr78157⟩
private theorem pr78163 : PrimeCertificate 78163 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv1861]) (by decide +kernel)
def pv78163 : PrimeValue := ⟨78163, pr78163⟩
private theorem pr78167 : PrimeCertificate 78167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv17,pv19]) (by decide +kernel)
def pv78167 : PrimeValue := ⟨78167, pr78167⟩
private theorem pr78173 : PrimeCertificate 78173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19543]) (by decide +kernel)
def pv78173 : PrimeValue := ⟨78173, pr78173⟩
private theorem pr78179 : PrimeCertificate 78179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv39089]) (by decide +kernel)
def pv78179 : PrimeValue := ⟨78179, pr78179⟩
private theorem pr78191 : PrimeCertificate 78191 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv1117]) (by decide +kernel)
def pv78191 : PrimeValue := ⟨78191, pr78191⟩
private theorem pr78193 : PrimeCertificate 78193 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv181]) (by decide +kernel)
def pv78193 : PrimeValue := ⟨78193, pr78193⟩
private theorem pr78203 : PrimeCertificate 78203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv641]) (by decide +kernel)
def pv78203 : PrimeValue := ⟨78203, pr78203⟩
private theorem pr78229 : PrimeCertificate 78229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv53]) (by decide +kernel)
def pv78229 : PrimeValue := ⟨78229, pr78229⟩
private theorem pr78233 : PrimeCertificate 78233 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11,pv127]) (by decide +kernel)
def pv78233 : PrimeValue := ⟨78233, pr78233⟩
private theorem pr78241 : PrimeCertificate 78241 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv163]) (by decide +kernel)
def pv78241 : PrimeValue := ⟨78241, pr78241⟩
private theorem pr78259 : PrimeCertificate 78259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13043]) (by decide +kernel)
def pv78259 : PrimeValue := ⟨78259, pr78259⟩
private theorem pr78277 : PrimeCertificate 78277 :=
  certifyPrime (q := pv59) (ls := [pv2,pv3,pv11,pv593]) (by decide +kernel)
def pv78277 : PrimeValue := ⟨78277, pr78277⟩
private theorem pr78283 : PrimeCertificate 78283 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv4349]) (by decide +kernel)
def pv78283 : PrimeValue := ⟨78283, pr78283⟩
private theorem pr78301 : PrimeCertificate 78301 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv29]) (by decide +kernel)
def pv78301 : PrimeValue := ⟨78301, pr78301⟩
private theorem pr78307 : PrimeCertificate 78307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv421]) (by decide +kernel)
def pv78307 : PrimeValue := ⟨78307, pr78307⟩
private theorem pr78311 : PrimeCertificate 78311 :=
  certifyPrime (q := pv29) (ls := [pv2,pv5,pv41,pv191]) (by decide +kernel)
def pv78311 : PrimeValue := ⟨78311, pr78311⟩
private theorem pr78317 : PrimeCertificate 78317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv2797]) (by decide +kernel)
def pv78317 : PrimeValue := ⟨78317, pr78317⟩
private theorem pr78341 : PrimeCertificate 78341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv3917]) (by decide +kernel)
def pv78341 : PrimeValue := ⟨78341, pr78341⟩
private theorem pr78347 : PrimeCertificate 78347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv911]) (by decide +kernel)
def pv78347 : PrimeValue := ⟨78347, pr78347⟩
private theorem pr78367 : PrimeCertificate 78367 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv37,pv353]) (by decide +kernel)
def pv78367 : PrimeValue := ⟨78367, pr78367⟩
private theorem pr78401 : PrimeCertificate 78401 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7]) (by decide +kernel)
def pv78401 : PrimeValue := ⟨78401, pr78401⟩
private theorem pr78427 : PrimeCertificate 78427 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv4357]) (by decide +kernel)
def pv78427 : PrimeValue := ⟨78427, pr78427⟩
private theorem pr78437 : PrimeCertificate 78437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19609]) (by decide +kernel)
def pv78437 : PrimeValue := ⟨78437, pr78437⟩
private theorem pr78439 : PrimeCertificate 78439 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv769]) (by decide +kernel)
def pv78439 : PrimeValue := ⟨78439, pr78439⟩
private theorem pr78467 : PrimeCertificate 78467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv39233]) (by decide +kernel)
def pv78467 : PrimeValue := ⟨78467, pr78467⟩
private theorem pr78479 : PrimeCertificate 78479 :=
  certifyPrime (q := pv7) (ls := [pv2,pv39239]) (by decide +kernel)
def pv78479 : PrimeValue := ⟨78479, pr78479⟩
private theorem pr78487 : PrimeCertificate 78487 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv103,pv127]) (by decide +kernel)
def pv78487 : PrimeValue := ⟨78487, pr78487⟩
private theorem pr78497 : PrimeCertificate 78497 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv223]) (by decide +kernel)
def pv78497 : PrimeValue := ⟨78497, pr78497⟩
private theorem pr78509 : PrimeCertificate 78509 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv1033]) (by decide +kernel)
def pv78509 : PrimeValue := ⟨78509, pr78509⟩
private theorem pr78511 : PrimeCertificate 78511 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv2617]) (by decide +kernel)
def pv78511 : PrimeValue := ⟨78511, pr78511⟩
private theorem pr78517 : PrimeCertificate 78517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv727]) (by decide +kernel)
def pv78517 : PrimeValue := ⟨78517, pr78517⟩
private theorem pr78539 : PrimeCertificate 78539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv107,pv367]) (by decide +kernel)
def pv78539 : PrimeValue := ⟨78539, pr78539⟩
private theorem pr78541 : PrimeCertificate 78541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv11,pv17]) (by decide +kernel)
def pv78541 : PrimeValue := ⟨78541, pr78541⟩
private theorem pr78553 : PrimeCertificate 78553 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1091]) (by decide +kernel)
def pv78553 : PrimeValue := ⟨78553, pr78553⟩
private theorem pr78569 : PrimeCertificate 78569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv23,pv61]) (by decide +kernel)
def pv78569 : PrimeValue := ⟨78569, pr78569⟩
private theorem pr78571 : PrimeCertificate 78571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv97]) (by decide +kernel)
def pv78571 : PrimeValue := ⟨78571, pr78571⟩
private theorem pr78577 : PrimeCertificate 78577 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1637]) (by decide +kernel)
def pv78577 : PrimeValue := ⟨78577, pr78577⟩
private theorem pr78583 : PrimeCertificate 78583 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv1871]) (by decide +kernel)
def pv78583 : PrimeValue := ⟨78583, pr78583⟩
private theorem pr78593 : PrimeCertificate 78593 :=
  certifyPrime (q := pv3) (ls := [pv2,pv307]) (by decide +kernel)
def pv78593 : PrimeValue := ⟨78593, pr78593⟩
private theorem pr78607 : PrimeCertificate 78607 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv397]) (by decide +kernel)
def pv78607 : PrimeValue := ⟨78607, pr78607⟩
private theorem pr78623 : PrimeCertificate 78623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv2069]) (by decide +kernel)
def pv78623 : PrimeValue := ⟨78623, pr78623⟩
private theorem pr78643 : PrimeCertificate 78643 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv17,pv257]) (by decide +kernel)
def pv78643 : PrimeValue := ⟨78643, pr78643⟩
private theorem pr78649 : PrimeCertificate 78649 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv29,pv113]) (by decide +kernel)
def pv78649 : PrimeValue := ⟨78649, pr78649⟩
private theorem pr78653 : PrimeCertificate 78653 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv53]) (by decide +kernel)
def pv78653 : PrimeValue := ⟨78653, pr78653⟩
private theorem pr78691 : PrimeCertificate 78691 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv43,pv61]) (by decide +kernel)
def pv78691 : PrimeValue := ⟨78691, pr78691⟩
private theorem pr78697 : PrimeCertificate 78697 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1093]) (by decide +kernel)
def pv78697 : PrimeValue := ⟨78697, pr78697⟩
private theorem pr78707 : PrimeCertificate 78707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv29,pv59]) (by decide +kernel)
def pv78707 : PrimeValue := ⟨78707, pr78707⟩
private theorem pr78713 : PrimeCertificate 78713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv9839]) (by decide +kernel)
def pv78713 : PrimeValue := ⟨78713, pr78713⟩
private theorem pr78721 : PrimeCertificate 78721 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv41]) (by decide +kernel)
def pv78721 : PrimeValue := ⟨78721, pr78721⟩
private theorem pr78737 : PrimeCertificate 78737 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv19,pv37]) (by decide +kernel)
def pv78737 : PrimeValue := ⟨78737, pr78737⟩
private theorem pr78779 : PrimeCertificate 78779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv17,pv331]) (by decide +kernel)
def pv78779 : PrimeValue := ⟨78779, pr78779⟩
private theorem pr78781 : PrimeCertificate 78781 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv13,pv101]) (by decide +kernel)
def pv78781 : PrimeValue := ⟨78781, pr78781⟩
private theorem pr78787 : PrimeCertificate 78787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1459]) (by decide +kernel)
def pv78787 : PrimeValue := ⟨78787, pr78787⟩
private theorem pr78791 : PrimeCertificate 78791 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7879]) (by decide +kernel)
def pv78791 : PrimeValue := ⟨78791, pr78791⟩
private theorem pr78797 : PrimeCertificate 78797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19699]) (by decide +kernel)
def pv78797 : PrimeValue := ⟨78797, pr78797⟩
private theorem pr78803 : PrimeCertificate 78803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv41]) (by decide +kernel)
def pv78803 : PrimeValue := ⟨78803, pr78803⟩
private theorem pr78809 : PrimeCertificate 78809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv9851]) (by decide +kernel)
def pv78809 : PrimeValue := ⟨78809, pr78809⟩
private theorem pr78823 : PrimeCertificate 78823 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv151]) (by decide +kernel)
def pv78823 : PrimeValue := ⟨78823, pr78823⟩
private theorem pr78839 : PrimeCertificate 78839 :=
  certifyPrime (q := pv13) (ls := [pv2,pv39419]) (by decide +kernel)
def pv78839 : PrimeValue := ⟨78839, pr78839⟩
private theorem pr78853 : PrimeCertificate 78853 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv6571]) (by decide +kernel)
def pv78853 : PrimeValue := ⟨78853, pr78853⟩
private theorem pr78857 : PrimeCertificate 78857 :=
  certifyPrime (q := pv3) (ls := [pv2,pv9857]) (by decide +kernel)
def pv78857 : PrimeValue := ⟨78857, pr78857⟩
private theorem pr78877 : PrimeCertificate 78877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv313]) (by decide +kernel)
def pv78877 : PrimeValue := ⟨78877, pr78877⟩
private theorem pr78887 : PrimeCertificate 78887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv39443]) (by decide +kernel)
def pv78887 : PrimeValue := ⟨78887, pr78887⟩
private theorem pr78889 : PrimeCertificate 78889 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv19,pv173]) (by decide +kernel)
def pv78889 : PrimeValue := ⟨78889, pr78889⟩
private theorem pr78893 : PrimeCertificate 78893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv163]) (by decide +kernel)
def pv78893 : PrimeValue := ⟨78893, pr78893⟩
private theorem pr78901 : PrimeCertificate 78901 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv263]) (by decide +kernel)
def pv78901 : PrimeValue := ⟨78901, pr78901⟩
private theorem pr78919 : PrimeCertificate 78919 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv1879]) (by decide +kernel)
def pv78919 : PrimeValue := ⟨78919, pr78919⟩
private theorem pr78929 : PrimeCertificate 78929 :=
  certifyPrime (q := pv3) (ls := [pv2,pv4933]) (by decide +kernel)
def pv78929 : PrimeValue := ⟨78929, pr78929⟩
private theorem pr78941 : PrimeCertificate 78941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv3947]) (by decide +kernel)
def pv78941 : PrimeValue := ⟨78941, pr78941⟩
private theorem pr78977 : PrimeCertificate 78977 :=
  certifyPrime (q := pv3) (ls := [pv2,pv617]) (by decide +kernel)
def pv78977 : PrimeValue := ⟨78977, pr78977⟩
private theorem pr78979 : PrimeCertificate 78979 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13163]) (by decide +kernel)
def pv78979 : PrimeValue := ⟨78979, pr78979⟩
private theorem pr78989 : PrimeCertificate 78989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv31]) (by decide +kernel)
def pv78989 : PrimeValue := ⟨78989, pr78989⟩
private theorem pr79031 : PrimeCertificate 79031 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv1129]) (by decide +kernel)
def pv79031 : PrimeValue := ⟨79031, pr79031⟩
private theorem pr79039 : PrimeCertificate 79039 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv4391]) (by decide +kernel)
def pv79039 : PrimeValue := ⟨79039, pr79039⟩
private theorem pr79043 : PrimeCertificate 79043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv39521]) (by decide +kernel)
def pv79043 : PrimeValue := ⟨79043, pr79043⟩
private theorem pr79063 : PrimeCertificate 79063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13177]) (by decide +kernel)
def pv79063 : PrimeValue := ⟨79063, pr79063⟩
private theorem pr79087 : PrimeCertificate 79087 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv269]) (by decide +kernel)
def pv79087 : PrimeValue := ⟨79087, pr79087⟩
private theorem pr79103 : PrimeCertificate 79103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv39551]) (by decide +kernel)
def pv79103 : PrimeValue := ⟨79103, pr79103⟩
private theorem pr79111 : PrimeCertificate 79111 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv293]) (by decide +kernel)
def pv79111 : PrimeValue := ⟨79111, pr79111⟩
private theorem pr79133 : PrimeCertificate 79133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv271]) (by decide +kernel)
def pv79133 : PrimeValue := ⟨79133, pr79133⟩
private theorem pr79139 : PrimeCertificate 79139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv39569]) (by decide +kernel)
def pv79139 : PrimeValue := ⟨79139, pr79139⟩
private theorem pr79147 : PrimeCertificate 79147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv4397]) (by decide +kernel)
def pv79147 : PrimeValue := ⟨79147, pr79147⟩
private theorem pr79151 : PrimeCertificate 79151 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv1583]) (by decide +kernel)
def pv79151 : PrimeValue := ⟨79151, pr79151⟩
private theorem pr79153 : PrimeCertificate 79153 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv17,pv97]) (by decide +kernel)
def pv79153 : PrimeValue := ⟨79153, pr79153⟩
private theorem pr79159 : PrimeCertificate 79159 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv79,pv167]) (by decide +kernel)
def pv79159 : PrimeValue := ⟨79159, pr79159⟩
private theorem pr79181 : PrimeCertificate 79181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv37,pv107]) (by decide +kernel)
def pv79181 : PrimeValue := ⟨79181, pr79181⟩
private theorem pr79187 : PrimeCertificate 79187 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv137]) (by decide +kernel)
def pv79187 : PrimeValue := ⟨79187, pr79187⟩
private theorem pr79193 : PrimeCertificate 79193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv521]) (by decide +kernel)
def pv79193 : PrimeValue := ⟨79193, pr79193⟩
private theorem pr79201 : PrimeCertificate 79201 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv79201 : PrimeValue := ⟨79201, pr79201⟩
private theorem pr79229 : PrimeCertificate 79229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv683]) (by decide +kernel)
def pv79229 : PrimeValue := ⟨79229, pr79229⟩
private theorem pr79241 : PrimeCertificate 79241 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv283]) (by decide +kernel)
def pv79241 : PrimeValue := ⟨79241, pr79241⟩
private theorem pr79259 : PrimeCertificate 79259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv1723]) (by decide +kernel)
def pv79259 : PrimeValue := ⟨79259, pr79259⟩
private theorem pr79273 : PrimeCertificate 79273 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv367]) (by decide +kernel)
def pv79273 : PrimeValue := ⟨79273, pr79273⟩
private theorem pr79279 : PrimeCertificate 79279 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv73,pv181]) (by decide +kernel)
def pv79279 : PrimeValue := ⟨79279, pr79279⟩
private theorem pr79283 : PrimeCertificate 79283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv809]) (by decide +kernel)
def pv79283 : PrimeValue := ⟨79283, pr79283⟩
private theorem pr79301 : PrimeCertificate 79301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv61]) (by decide +kernel)
def pv79301 : PrimeValue := ⟨79301, pr79301⟩
private theorem pr79309 : PrimeCertificate 79309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv2203]) (by decide +kernel)
def pv79309 : PrimeValue := ⟨79309, pr79309⟩
private theorem pr79319 : PrimeCertificate 79319 :=
  certifyPrime (q := pv7) (ls := [pv2,pv39659]) (by decide +kernel)
def pv79319 : PrimeValue := ⟨79319, pr79319⟩
private theorem pr79333 : PrimeCertificate 79333 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv601]) (by decide +kernel)
def pv79333 : PrimeValue := ⟨79333, pr79333⟩
private theorem pr79337 : PrimeCertificate 79337 :=
  certifyPrime (q := pv3) (ls := [pv2,pv47,pv211]) (by decide +kernel)
def pv79337 : PrimeValue := ⟨79337, pr79337⟩
private theorem pr79349 : PrimeCertificate 79349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv83,pv239]) (by decide +kernel)
def pv79349 : PrimeValue := ⟨79349, pr79349⟩
private theorem pr79357 : PrimeCertificate 79357 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv389]) (by decide +kernel)
def pv79357 : PrimeValue := ⟨79357, pr79357⟩
private theorem pr79367 : PrimeCertificate 79367 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv5669]) (by decide +kernel)
def pv79367 : PrimeValue := ⟨79367, pr79367⟩
private theorem pr79379 : PrimeCertificate 79379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv43,pv71]) (by decide +kernel)
def pv79379 : PrimeValue := ⟨79379, pr79379⟩
private theorem pr79393 : PrimeCertificate 79393 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv827]) (by decide +kernel)
def pv79393 : PrimeValue := ⟨79393, pr79393⟩
private theorem pr79397 : PrimeCertificate 79397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv863]) (by decide +kernel)
def pv79397 : PrimeValue := ⟨79397, pr79397⟩
private theorem pr79399 : PrimeCertificate 79399 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv401]) (by decide +kernel)
def pv79399 : PrimeValue := ⟨79399, pr79399⟩
private theorem pr79411 : PrimeCertificate 79411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv2647]) (by decide +kernel)
def pv79411 : PrimeValue := ⟨79411, pr79411⟩
private theorem pr79423 : PrimeCertificate 79423 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv31,pv61]) (by decide +kernel)
def pv79423 : PrimeValue := ⟨79423, pr79423⟩
private theorem pr79427 : PrimeCertificate 79427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv151,pv263]) (by decide +kernel)
def pv79427 : PrimeValue := ⟨79427, pr79427⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
