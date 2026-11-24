/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks00/Block0067
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks00/Block0067.checked0067
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table013
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table016
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table022
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table035
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table080
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table081

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0067c00 : List Row := [
  .c 11, .p pv2 [pv2,pv3,pv53,pv863], .c 3, .c 13, .c 5, .c 3, .c 17, .c 263, .c 3, .c 5, .c 73,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv79,pv193], .c 3, .p pv5 [pv2,pv17,pv1009], .c 13, .c 3,
  .p pv5 [pv2,pv274451], .c 5, .c 3, .p pv2 [pv2,pv41,pv3347], .c 11, .c 3, .c 5, .c 31, .c 3,
  .c 53, .c 97, .c 3, .p pv5 [pv2,pv7,pv39209], .c 19, .c 3, .c 7, .c 5, .c 3, .c 61, .c 23, .c 3,
  .c 5, .c 7, .c 3, .c 13, .p pv5 [pv2,pv3,pv89,pv257], .c 3, .p pv2 [pv2,pv137239], .c 137, .c 3,
  .p pv2 [pv2,pv83,pv3307], .c 5, .c 3, .c 37, .c 79, .c 3, .c 5, .c 11, .c 3, .c 17, .c 239,
  .c 3, .c 23, .c 7, .c 3, .c 179, .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv61], .c 3, .c 5,
  .c 47, .c 3, .p pv7 [pv2,pv5,pv7,pv11,pv23,pv31], .p pv2 [pv2,pv3,pv45751], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv3389], .c 3, .p pv5 [pv2,pv211,pv1301], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv101,pv151], .c 3, .c 31, .c 11, .c 3, .c 677, .c 17, .c 3, .c 619, .c 5, .c 3,
  .c 7, .c 61, .c 3, .c 5, .c 43, .c 3, .p pv17 [pv2,pv5,pv54907], .c 7, .c 3, .c 739, .c 23,
  .c 3, .c 17, .c 5, .c 3, .p pv3 [pv2,pv17159], .p pv7 [pv2,pv3,pv5,pv6101], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv137,pv167], .c 3, .c 7, .c 31, .c 3, .c 13, .c 11, .c 3, .c 41, .c 5, .c 3,
  .c 19, .p pv47 [pv2,pv3,pv5,pv11,pv13],
]
private theorem h0067c00 : checkBlock 548867 128 b0067c00 = true := by
  decide +kernel

private def b0067c01 : List Row := [
  .c 3, .c 5, .c 449, .c 3, .c 11, .c 13, .c 3, .c 101, .p pv2 [pv2,pv3,pv19,pv4817], .c 3, .c 7,
  .c 5, .c 3, .p pv2 [pv2,pv23,pv47,pv127], .c 17, .c 3, .c 5, .c 7, .c 3,
  .p pv13 [pv2,pv5,pv13729], .p pv5 [pv2,pv3,pv30509], .c 3, .p pv5 [pv2,pv274583],
  .p pv7 [pv2,pv3,pv17,pv673], .c 3, .c 29, .c 5, .c 3, .c 73, .c 233, .c 3, .c 5, .c 151, .c 3,
  .c 37, .p pv5 [pv2,pv3,pv7,pv467], .c 3, .c 11, .c 7, .c 3, .p pv2 [pv2,pv17,pv29,pv557], .c 5,
  .c 3, .c 257, .c 13, .c 3, .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv7,pv3923], .c 307, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv37,pv1237], .c 3, .c 19, .c 5, .c 3, .c 43, .c 7, .c 3, .c 5,
  .p pv41 [pv2,pv3,pv91541], .c 3, .c 109, .c 17, .c 3, .p pv3 [pv2,pv71,pv967],
  .p pv2 [pv2,pv3,pv31,pv2953], .c 3, .c 11, .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 41, .c 3,
  .p pv3 [pv2,pv5,pv3433], .c 7, .c 3, .c 17, .c 13, .c 3, .c 113, .c 5, .c 3, .c 103, .c 347,
  .c 3, .c 5, .c 11, .c 3, .c 7, .p pv5 [pv2,pv3,pv2861], .c 3, .c 271,
  .p pv3 [pv2,pv3,pv7,pv11,pv29,pv41], .c 3, .p pv2 [pv2,pv274661], .c 5, .c 3, .c 11,
  .p pv17 [pv2,pv3,pv5,pv18311], .c 3, .c 5, .c 641, .c 3, .c 13, .c 157, .c 3, .c 19, .c 59,
  .c 3, .c 7, .c 5, .c 3, .c 41, .c 317, .c 3, .c 5, .c 7, .c 3, .c 229, .c 11, .c 3, .c 83,
]
private theorem h0067c01 : checkBlock 549123 128 b0067c01 = true := by
  decide +kernel

private def b0067c02 : List Row := [
  .p pv23 [pv2,pv3,pv23,pv1327], .c 3, .c 47, .c 5, .c 3, .c 17, .p pv23 [pv2,pv3,pv5,pv18313],
  .c 3, .c 5, .c 89, .c 3, .c 23, .p pv2 [pv2,pv3,pv7,pv103,pv127], .c 3, .c 263, .c 7, .c 3,
  .c 31, .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv9157], .c 3, .c 5, .c 61, .c 3,
  .p pv7 [pv2,pv5,pv7,pv47,pv167], .c 197, .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv19,pv761], .c 5,
  .c 3, .p pv3 [pv2,pv173,pv397], .c 7, .c 3, .c 5, .c 17, .c 3, .c 11, .c 29, .c 3, .c 59, .c 71,
  .c 3, .c 163, .c 5, .c 3, .c 7, .p pv31 [pv2,pv3,pv5,pv19,pv241], .c 3, .c 5, .c 37, .c 3,
  .c 17, .c 7, .c 3, .c 13, .c 19, .c 3, .p pv5 [pv2,pv274751], .c 5, .c 3,
  .p pv2 [pv2,pv17,pv8081], .p pv17 [pv2,pv3,pv5,pv13,pv1409], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv23,pv181], .c 3, .c 7, .c 13, .c 3, .c 11, .c 127, .c 3,
  .p pv2 [pv2,pv137383], .c 5, .c 3, .c 23, .c 101, .c 3, .c 5, .p pv2 [pv2,pv3,pv91591], .c 3,
  .p pv7 [pv2,pv5,pv29,pv379], .p pv5 [pv2,pv3,pv107], .c 3, .c 53, .c 17, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv31,pv277], .c 11, .c 3, .c 5, .c 7, .c 3, .c 463, .c 43, .c 3,
  .p pv2 [pv2,pv283,pv971], .p pv2 [pv2,pv3,pv13,pv271], .c 3, .c 11, .c 5, .c 3, .c 31, .c 13,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv139,pv659], .c 3, .c 71, .c 19, .c 3, .c 73, .c 7, .c 3,
  .p pv5 [pv2,pv274811], .c 5, .c 3, .c 359, .c 23, .c 3,
]
private theorem h0067c02 : checkBlock 549379 128 b0067c02 = true := by
  decide +kernel

private def b0067c03 : List Row := [
  .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv7,pv13,pv151], .p pv3 [pv2,pv3,pv101,pv907], .c 3, .c 7,
  .p pv17 [pv2,pv3,pv11,pv347], .c 3, .c 13, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv29], .c 3, .c 61, .c 523, .c 3, .c 23, .c 13, .c 3,
  .p pv2 [pv2,pv7,pv71,pv79], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv73,pv251], .c 3, .c 5,
  .c 181, .c 3, .p pv2 [pv2,pv5,pv23,pv239], .c 7, .c 3, .p pv2 [pv2,pv274853], .c 37, .c 3,
  .p pv5 [pv2,pv17,pv43,pv47], .c 5, .c 3, .p pv7 [pv2,pv13,pv21143], .c 241, .c 3, .c 5, .c 19,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv61,pv751], .c 3, .p pv3 [pv2,pv11,pv6247],
  .p pv2 [pv2,pv3,pv7,pv4363], .c 3, .c 101, .c 5, .c 3, .p pv2 [pv2,pv137437],
  .p pv17 [pv2,pv3,pv5,pv733], .c 3, .c 5, .c 13, .c 3, .c 79, .c 17, .c 3,
  .p pv5 [pv2,pv7,pv107,pv367], .c 11, .c 3, .c 7, .c 5, .c 3, .c 503, .c 137, .c 3, .c 5, .c 7,
  .c 3, .c 11, .c 61, .c 3, .c 17, .c 163, .c 3, .c 19, .c 5, .c 3, .c 13, .c 29, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv31,pv739], .c 3, .c 59, .c 487, .c 3, .c 197, .c 7, .c 3,
  .p pv3 [pv2,pv68729], .c 5, .c 3, .p pv11 [pv2,pv23,pv11953], .c 19, .c 3, .c 5, .c 31, .c 3,
  .c 41, .c 47, .c 3, .c 7, .c 271, .c 3, .p pv5 [pv2,pv274931], .c 5, .c 3, .c 29, .c 7, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv45823], .c 3, .c 577, .p pv5 [pv2,pv3,pv17,pv599], .c 3, .c 13, .c 191,
]
private theorem h0067c03 : checkBlock 549635 128 b0067c03 = true := by
  decide +kernel

private def b0067c04 : List Row := [
  .c 3, .c 97, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 23, .c 3, .p pv13 [pv2,pv5,pv127,pv433],
  .c 7, .c 3, .c 19, .c 79, .c 3, .c 11, .c 5, .c 3, .c 379, .c 37, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv19,pv67], .c 3, .c 7, .p pv5 [pv2,pv3,pv151,pv607], .c 3, .c 47,
  .p pv2 [pv2,pv3,pv7,pv6547], .c 3, .c 23, .c 5, .c 3, .c 149, .c 293, .c 3, .c 5, .c 11, .c 3,
  .c 31, .c 461, .c 3, .p pv3 [pv2,pv7,pv23,pv61], .p pv3 [pv2,pv3,pv11,pv13,pv641], .c 3, .c 7,
  .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 7, .c 3, .c 17, .c 67, .c 3, .p pv5 [pv2,pv275003],
  .p pv7 [pv2,pv3,pv7639], .c 3, .c 43, .c 5, .c 3, .c 587, .c 227, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv30557], .c 3, .c 19, .c 11, .c 3, .c 61, .c 7, .c 3, .c 13, .c 5, .c 3,
  .p pv3 [pv2,pv17189], .c 563, .c 3, .c 5, .c 59, .c 3, .p pv2 [pv2,pv5,pv7,pv3929],
  .p pv3 [pv2,pv3,pv30559], .c 3, .c 7, .c 13, .c 3, .p pv3 [pv2,pv29,pv2371], .c 5, .c 3, .c 37,
  .c 7, .c 3, .c 5, .c 53, .c 3, .c 23, .c 151, .c 3, .c 41, .c 11, .c 3, .c 17, .c 5, .c 3, .c 7,
  .p pv19 [pv2,pv3,pv5,pv11,pv1667], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv37,pv59], .c 3, .c 11,
  .c 7, .c 3, .p pv5 [pv2,pv19,pv31,pv467], .p pv7 [pv2,pv3,pv73,pv157], .c 3, .c 367, .c 5, .c 3,
  .p pv2 [pv2,pv41,pv6709], .c 223, .c 3, .c 5,
]
private theorem h0067c04 : checkBlock 549891 128 b0067c04 = true := by
  decide +kernel

private def b0067c05 : List Row := [
  .c 13, .c 3, .c 7, .c 37, .c 3, .c 31, .c 29, .c 3, .p pv2 [pv2,pv139,pv1979], .c 5, .c 3,
  .p pv3 [pv2,pv68771], .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv521], .c 3,
  .p pv2 [pv2,pv5,pv27509], .c 19, .c 3, .c 11, .p pv2 [pv2,pv3,pv17,pv29,pv31], .c 3, .c 7, .c 5,
  .c 3, .c 13, .c 73, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv55021],
  .p pv7 [pv2,pv3,pv13,pv3527], .c 3, .c 29, .c 31, .c 3, .c 569, .c 5, .c 3, .c 23, .c 11, .c 3,
  .c 5, .c 257, .c 3, .p pv3 [pv2,pv5,pv19,pv181], .c 193, .c 3, .c 421, .c 7, .c 3, .c 11, .c 5,
  .c 3, .c 19, .c 41, .c 3, .c 5, .p pv3 [pv2,pv3,pv91711], .c 3, .c 43, .c 17, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv19,pv1609], .c 3, .p pv2 [pv2,pv503,pv547], .c 5, .c 3,
  .p pv3 [pv2,pv163,pv211], .c 7, .c 3, .c 5, .c 11, .c 3, .c 37, .c 13, .c 3, .c 17,
  .p pv13 [pv2,pv3,pv11,pv379], .c 3, .c 173, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 353, .c 3,
  .c 131, .c 7, .c 3, .p pv3 [pv2,pv8599], .c 727, .c 3, .c 31, .c 5, .c 3, .c 101,
  .p pv7 [pv2,pv3,pv5,pv1223], .c 3, .c 5, .c 43, .c 3, .c 7, .c 11, .c 3, .c 23,
  .p pv11 [pv2,pv3,pv7,pv13], .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv97,pv2837], .c 13, .c 3,
  .c 5, .c 431, .c 3, .c 29, .c 79, .c 3, .c 499, .c 277, .c 3,
]
private theorem h0067c05 : checkBlock 550147 128 b0067c05 = true := by
  decide +kernel

private def b0067c06 : List Row := [
  .c 7, .c 5, .c 3, .c 17, .c 19, .c 3, .c 5, .c 7, .c 3, .c 181, .c 113, .c 3,
  .p pv5 [pv2,pv17,pv16189], .c 11, .c 3, .c 13, .c 5, .c 3, .p pv7 [pv2,pv7,pv39317],
  .p pv7 [pv2,pv3,pv5,pv11,pv139], .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv7057], .c 3, .c 11, .c 331,
  .c 3, .p pv3 [pv2,pv83,pv829], .c 7, .c 3, .c 71, .c 5, .c 3, .p pv2 [pv2,pv19,pv7243],
  .p pv3 [pv2,pv3,pv5,pv59,pv311], .c 3, .c 5, .c 17, .c 3, .c 599, .c 733, .c 3, .c 7,
  .p pv17 [pv2,pv3,pv22937], .c 3, .c 73, .c 5, .c 3, .c 211, .c 7, .c 3, .c 5, .c 29, .c 3,
  .c 13, .p pv5 [pv2,pv3,pv3823], .c 3, .c 11, .p pv7 [pv2,pv3,pv91753], .c 3, .c 37, .c 5, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv5,pv2039], .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv27527], .c 7,
  .c 3, .c 293, .c 607, .c 3, .p pv3 [pv2,pv68819], .c 5, .c 3, .c 109, .c 11, .c 3, .c 5, .c 313,
  .c 3, .c 7, .c 401, .c 3, .p pv3 [pv2,pv13,pv2647], .c 17, .c 3, .c 11, .c 5, .c 3, .c 13,
  .c 31, .c 3, .c 5, .c 23, .c 3, .c 19, .c 137, .c 3, .p pv5 [pv2,pv7,pv67,pv587],
  .p pv13 [pv2,pv3,pv11471], .c 3, .c 7, .c 5, .c 3, .c 641, .p pv13 [pv2,pv3,pv5,pv7,pv19,pv23],
  .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv17,pv41,pv79], .c 199, .c 3, .p pv2 [pv2,pv137659],
  .c 19, .c 3, .c 23, .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv3671], .c 3, .c 5,
  .p pv11 [pv2,pv3,pv239],
]
private theorem h0067c06 : checkBlock 550403 128 b0067c06 = true := by
  decide +kernel

private def b0067c07 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv11,pv2503], .p pv5 [pv2,pv3,pv7,pv1873], .c 3, .c 13, .c 7, .c 3, .c 67,
  .c 5, .c 3, .p pv23 [pv2,pv275339], .c 17, .c 3, .c 5, .c 379, .c 3,
  .p pv7 [pv2,pv5,pv7,pv7867], .c 11, .c 3, .c 7, .c 47, .c 3, .p pv5 [pv2,pv227,pv1213], .c 5,
  .c 3, .c 79, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv45893], .c 3, .p pv7 [pv2,pv5,pv1721], .c 53,
  .c 3, .c 691, .c 107, .c 3, .p pv2 [pv2,pv7,pv13,pv17,pv89], .c 5, .c 3, .c 7, .c 103, .c 3,
  .c 5, .c 71, .c 3, .c 257, .c 7, .c 3, .p pv2 [pv2,pv157,pv877], .c 11, .c 3,
  .p pv2 [pv2,pv113,pv2437], .c 5, .c 3, .c 61, .c 13, .c 3, .c 5, .c 31, .c 3, .c 7, .c 17, .c 3,
  .c 43, .p pv2 [pv2,pv3,pv7,pv79,pv83], .c 3, .c 47, .c 5, .c 3, .c 127,
  .p pv19 [pv2,pv3,pv5,pv17], .c 3, .c 5, .c 67, .c 3, .p pv2 [pv2,pv5,pv13,pv19,pv223],
  .p pv2 [pv2,pv3,pv197,pv233], .c 3, .c 17, .c 37, .c 3, .c 7, .c 5, .c 3, .c 19,
  .p pv3 [pv2,pv3,pv5,pv7,pv43,pv61], .c 3, .c 5, .c 7, .c 3, .p pv13 [pv2,pv5,pv47,pv293],
  .p pv3 [pv2,pv3,pv91807], .c 3, .c 11, .c 13, .c 3, .c 149, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv11,pv73], .p pv17 [pv2,pv3,pv5,pv9181], .c 3, .c 5, .c 19, .c 3, .c 83, .c 23,
  .c 3, .c 137, .c 7, .c 3, .c 59, .c 5, .c 3, .c 71, .c 11, .c 3, .c 5, .c 593, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv11,pv17,pv491], .c 3, .c 7, .p pv11 [pv2,pv3,pv5101], .c 3, .c 11,
]
private theorem h0067c07 : checkBlock 550659 128 b0067c07 = true := by
  decide +kernel

private def b0067c08 : List Row := [
  .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 13, .c 3, .c 73, .c 167, .c 3, .p pv3 [pv2,pv17,pv4051],
  .p pv2 [pv2,pv3,pv91823], .c 3, .c 19, .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv3673], .c 3,
  .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv71,pv97], .c 7, .c 3, .c 37, .p pv7 [pv2,pv3,pv11,pv2087],
  .c 3, .p pv2 [pv2,pv137743], .c 5, .c 3, .c 11, .c 19, .c 3, .c 5, .c 17, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv13,pv883], .c 3, .p pv2 [pv2,pv139,pv991], .c 41, .c 3,
  .p pv2 [pv2,pv43,pv149], .c 5, .c 3, .c 197, .c 23, .c 3, .c 5, .p pv5 [pv2,pv3,pv2551], .c 3,
  .c 17, .c 11, .c 3, .p pv2 [pv2,pv7,pv39359], .c 29, .c 3, .c 7, .c 5, .c 3,
  .p pv11 [pv2,pv17,pv19,pv853], .c 37, .c 3, .c 5, .c 7, .c 3, .c 643, .c 127, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv29,pv3167], .c 3, .p pv5 [pv2,pv275531], .c 5, .c 3, .p pv2 [pv2,pv7,pv19681],
  .c 349, .c 3, .c 5, .c 73, .c 3, .c 41, .c 13, .c 3, .c 29, .c 7, .c 3,
  .p pv2 [pv2,pv311,pv443], .c 5, .c 3, .p pv2 [pv2,pv275549], .c 113, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv17,pv1801], .c 3, .c 11, .p pv5 [pv2,pv3,pv22963], .c 3, .c 7, .c 59, .c 3,
  .c 17, .c 5, .c 3, .p pv3 [pv2,pv68891], .c 7, .c 3, .c 5, .c 383, .c 3, .c 179,
  .p pv3 [pv2,pv3,pv67,pv457], .c 3, .c 53, .c 23, .c 3, .c 103, .c 5, .c 3, .c 7, .c 13, .c 3,
  .c 5, .c 241, .c 3,
]
private theorem h0067c08 : checkBlock 550915 128 b0067c08 = true := by
  decide +kernel

private def b0067c09 : List Row := [
  .c 19, .c 7, .c 3, .c 11, .p pv2 [pv2,pv3,pv59,pv173], .c 3, .c 79, .c 5, .c 3, .c 37, .c 17,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv61,pv251], .c 3, .c 7, .c 29, .c 3, .p pv5 [pv2,pv197,pv1399],
  .c 19, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv23,pv521], .c 11, .c 3, .c 5, .c 157, .c 3,
  .p pv7 [pv2,pv5,pv199,pv277], .p pv23 [pv2,pv3,pv11,pv29], .c 3, .c 59, .c 13, .c 3, .c 7, .c 5,
  .c 3, .c 431, .c 97, .c 3, .c 5, .c 7, .c 3, .c 29, .c 37, .c 3, .c 167,
  .p pv2 [pv2,pv3,pv15313], .c 3, .c 31, .c 5, .c 3, .c 541, .p pv59 [pv2,pv3,pv5,pv2297], .c 3,
  .c 5, .c 11, .c 3, .c 13, .c 17, .c 3, .p pv3 [pv2,pv59,pv73], .c 7, .c 3, .c 43, .c 5, .c 3,
  .c 11, .p pv13 [pv2,pv3,pv5,pv17,pv23,pv47], .c 3, .c 5, .c 13, .c 3,
  .p pv3 [pv2,pv5,pv7,pv11,pv179], .c 19, .c 3, .c 7, .c 479, .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv275669], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv43,pv2137], .c 3, .c 173, .c 11,
  .c 3, .c 47, .c 53, .c 3, .p pv2 [pv2,pv7,pv39383], .c 5, .c 3, .c 7, .c 107, .c 3, .c 5, .c 29,
  .c 3, .p pv3 [pv2,pv5,pv19,pv1451], .c 7, .c 3, .p pv2 [pv2,pv11,pv71,pv353], .c 43, .c 3,
  .c 491, .c 5, .c 3, .c 19, .c 193, .c 3, .c 5, .p pv17 [pv2,pv3,pv29,pv3169], .c 3, .c 7,
  .c 139, .c 3, .c 191, .c 11, .c 3, .p pv5 [pv2,pv275711], .c 5,
]
private theorem h0067c09 : checkBlock 551171 128 b0067c09 = true := by
  decide +kernel

private def b0067c10 : List Row := [
  .c 3, .c 17, .c 109, .c 3, .c 5, .c 19, .c 3, .c 11, .p pv3 [pv2,pv3,pv73,pv1259], .c 3, .c 13,
  .c 149, .c 3, .c 7, .c 5, .c 3, .c 31, .p pv37 [pv2,pv3,pv5,pv7,pv13,pv101], .c 3, .c 5, .c 7,
  .c 3, .c 23, .c 13, .c 3, .c 67, .c 223, .c 3, .p pv2 [pv2,pv275741], .c 5, .c 3,
  .p pv3 [pv2,pv7,pv1231], .c 41, .c 3, .c 5, .c 17, .c 3, .c 61, .p pv3 [pv2,pv3,pv7,pv1459],
  .c 3, .c 11, .c 7, .c 3, .c 19, .c 5, .c 3, .p pv11 [pv2,pv11,pv43,pv53], .c 31, .c 3, .c 5,
  .c 467, .c 3, .c 17, .c 89, .c 3, .c 7, .p pv3 [pv2,pv3,pv13,pv2357], .c 3,
  .p pv5 [pv2,pv97,pv2843], .c 5, .c 3, .p pv3 [pv2,pv17,pv8111], .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv5107], .c 3, .c 43, .c 23, .c 3, .c 283, .p pv11 [pv2,pv3,pv11491], .c 3,
  .c 11, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv29,pv317], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv23,pv571], .c 3, .c 59, .c 7, .c 3, .p pv2 [pv2,pv37,pv3727], .c 17, .c 3,
  .c 13, .c 5, .c 3, .c 23, .c 67, .c 3, .c 5, .c 11, .c 3, .c 7, .c 61, .c 3, .c 19, .c 13, .c 3,
  .c 17, .c 5, .c 3, .c 11, .c 131, .c 3, .c 5, .c 43, .c 3, .p pv2 [pv2,pv5,pv11,pv17,pv59],
  .p pv13 [pv2,pv3,pv45971], .c 3, .c 79, .p pv2 [pv2,pv3,pv91943], .c 3, .c 7, .c 5, .c 3,
  .c 337, .p pv7 [pv2,pv3,pv5,pv7,pv37,pv71], .c 3, .c 5, .c 7, .c 3, .c 13,
]
private theorem h0067c10 : checkBlock 551427 128 b0067c10 = true := by
  decide +kernel

private def b0067c11 : List Row := [
  .c 11, .c 3, .c 701, .p pv7 [pv2,pv3,pv127,pv181], .c 3, .p pv2 [pv2,pv107,pv1289], .c 5, .c 3,
  .c 137, .c 17, .c 3, .c 5, .c 13, .c 3, .c 89, .p pv11 [pv2,pv3,pv7,pv821], .c 3,
  .p pv2 [pv2,pv11,pv12539], .c 7, .c 3, .p pv2 [pv2,pv19,pv14519], .c 5, .c 3,
  .p pv3 [pv2,pv34483], .p pv2 [pv2,pv3,pv5,pv53,pv347], .c 3, .c 5, .c 41, .c 3, .c 19,
  .p pv11 [pv2,pv3,pv91957], .c 3, .c 7, .c 11, .c 3, .p pv5 [pv2,pv17,pv4057], .c 5, .c 3, .c 13,
  .c 7, .c 3, .c 5, .p pv13 [pv2,pv3,pv91961], .c 3, .c 11, .p pv2 [pv2,pv3,pv13,pv131], .c 3,
  .c 331, .c 19, .c 3, .c 29, .c 5, .c 3, .c 7, .c 503, .c 3, .c 5, .c 197, .c 3,
  .p pv3 [pv2,pv5,pv31,pv89], .c 7, .c 3, .c 73, .p pv13 [pv2,pv3,pv479], .c 3,
  .p pv2 [pv2,pv29,pv67,pv71], .c 5, .c 3, .c 41, .c 449, .c 3, .c 5, .c 47, .c 3, .c 7, .c 97,
  .c 3, .c 11, .c 23, .c 3, .p pv2 [pv2,pv275921], .c 5, .c 3, .p pv3 [pv2,pv11,pv6271], .c 239,
  .c 3, .c 5, .c 179, .c 3, .p pv2 [pv2,pv5,pv41,pv673], .c 13, .c 3, .c 61, .c 181, .c 3, .c 7,
  .c 5, .c 3, .c 67, .c 11, .c 3, .c 5, .c 7, .c 3, .c 647, .c 19, .c 3, .c 317, .c 29, .c 3,
  .c 11, .c 5, .c 3, .p pv2 [pv2,pv7,pv23,pv857], .p pv3 [pv2,pv3,pv5,pv18397], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv15331], .c 3, .c 47, .c 547, .c 3, .p pv5 [pv2,pv275963], .c 7, .c 3,
  .p pv2 [pv2,pv137983], .c 5, .c 3,
]
private theorem h0067c11 : checkBlock 551683 128 b0067c11 = true := by
  decide +kernel

private def b0067c12 : List Row := [
  .c 17, .c 13, .c 3, .c 5, .c 11, .c 3, .p pv17 [pv2,pv5,pv7,pv19,pv83], .c 73, .c 3, .c 7,
  .p pv17 [pv2,pv3,pv11,pv8363], .c 3, .p pv2 [pv2,pv275981], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5,
  .c 23, .c 3, .p pv7 [pv2,pv5,pv11,pv13,pv193], .c 41, .c 3, .c 557, .c 61, .c 3, .c 13, .c 5,
  .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv23], .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv55201], .c 7,
  .c 3, .c 31, .c 13, .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv138007],
  .p pv3 [pv2,pv3,pv5,pv18401], .c 3, .c 5, .c 263, .c 3, .c 7, .c 173, .c 3,
  .p pv5 [pv2,pv11,pv23,pv1091], .c 743, .c 3, .p pv2 [pv2,pv79,pv1747], .c 5, .c 3,
  .p pv7 [pv2,pv13,pv17,pv1249], .c 277, .c 3, .c 5, .c 89, .c 3, .c 13, .c 29, .c 3, .c 37,
  .c 11, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv69011], .p pv3 [pv2,pv3,pv5,pv7,pv11,pv239], .c 3,
  .c 5, .c 7, .c 3, .c 11, .p pv3 [pv2,pv3,pv19,pv29,pv167], .c 3, .p pv2 [pv2,pv41,pv6733],
  .c 17, .c 3, .p pv3 [pv2,pv11,pv3137], .c 5, .c 3, .c 229, .c 19, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv17,pv5413], .c 3, .c 29, .c 283, .c 3, .p pv3 [pv2,pv13,pv5309], .c 7, .c 3,
  .c 17, .c 5, .c 3, .c 13, .c 37, .c 3, .c 5, .c 571, .c 3, .c 23, .c 43, .c 3, .c 7, .c 157,
  .c 3, .c 193, .c 5, .c 3, .p pv2 [pv2,pv11,pv19,pv1321], .c 7, .c 3, .c 5, .c 211, .c 3, .c 197,
  .p pv7 [pv2,pv3,pv719],
]
private theorem h0067c12 : checkBlock 551939 128 b0067c12 = true := by
  decide +kernel

private def b0067c13 : List Row := [
  .c 3, .c 19, .c 83, .c 3, .c 31, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .p pv17 [pv2,pv3,pv7,pv19,pv173], .c 3, .c 97, .c 7, .c 3, .c 13, .c 41, .c 3, .c 11, .c 5,
  .c 3, .p pv7 [pv2,pv71,pv3889], .p pv41 [pv2,pv3,pv5,pv13,pv59], .c 3, .c 5, .c 29, .c 3, .c 7,
  .c 13, .c 3, .c 269, .p pv2 [pv2,pv3,pv7,pv487], .c 3, .p pv5 [pv2,pv17,pv37,pv439], .c 5, .c 3,
  .c 167, .p pv3 [pv2,pv3,pv5,pv41,pv449], .c 3, .c 5, .c 11, .c 3, .c 67,
  .p pv2 [pv2,pv3,pv83,pv1109], .c 3, .c 479, .c 79, .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv5,pv7,pv263], .c 3, .c 5, .c 7, .c 3, .c 19, .c 17, .c 3,
  .p pv2 [pv2,pv138079], .c 601, .c 3, .c 127, .c 5, .c 3, .c 239, .c 13, .c 3, .c 5, .c 643,
  .c 3, .p pv2 [pv2,pv5,pv27617], .c 11, .c 3, .c 17, .c 7, .c 3, .p pv3 [pv2,pv41,pv421], .c 5,
  .c 3, .c 463, .c 541, .c 3, .c 5, .c 587, .c 3, .c 223, .c 37, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv43,pv2141], .c 3, .c 13, .c 5, .c 3, .c 31, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv3541], .c 3, .p pv3 [pv2,pv5,pv1381], .p pv2 [pv2,pv3,pv30689], .c 3,
  .c 163, .c 11, .c 3, .c 373, .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .c 131, .c 3, .c 11, .c 7,
  .c 3, .c 23, .c 331, .c 3, .c 233, .c 5, .c 3, .c 17,
]
private theorem h0067c13 : checkBlock 552195 128 b0067c13 = true := by
  decide +kernel

private def b0067c14 : List Row := [
  .c 31, .c 3, .c 5, .c 113, .c 3, .c 7, .c 19, .c 3, .c 349, .p pv2 [pv2,pv3,pv7,pv6577], .c 3,
  .p pv3 [pv2,pv53,pv1303], .c 5, .c 3, .c 29, .p pv7 [pv2,pv3,pv5,pv1151], .c 3, .c 5, .c 13,
  .c 3, .p pv2 [pv2,pv5,pv55249], .p pv5 [pv2,pv3,pv103,pv149], .c 3, .c 11, .c 569, .c 3, .c 7,
  .c 5, .c 3, .c 151, .p pv3 [pv2,pv3,pv5,pv7,pv877], .c 3, .c 5, .c 7, .c 3, .c 37,
  .p pv3 [pv2,pv3,pv71,pv1297], .c 3, .p pv5 [pv2,pv13,pv79,pv269], .c 23, .c 3, .c 673, .c 5,
  .c 3, .c 13, .c 11, .c 3, .c 5, .c 683, .c 3, .c 17, .p pv5 [pv2,pv3,pv7,pv11,pv13,pv23], .c 3,
  .c 41, .c 7, .c 3, .c 11, .c 5, .c 3, .c 271, .c 101, .c 3, .c 5, .c 19, .c 3,
  .p pv2 [pv2,pv5,pv7,pv3947], .p pv11 [pv2,pv3,pv379], .c 3, .c 7, .p pv2 [pv2,pv3,pv46049],
  .c 3, .c 43, .c 5, .c 3, .c 61, .c 7, .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv73,pv757],
  .c 241, .c 3, .c 13, .c 17, .c 3, .c 199, .c 5, .c 3, .c 7, .c 53, .c 3, .c 5, .c 31, .c 3,
  .c 149, .c 7, .c 3, .c 311, .p pv13 [pv2,pv3,pv23027], .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv137,pv2017], .c 419, .c 3, .c 5, .c 23, .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv233,pv593], .c 43, .c 3, .c 67, .c 5, .c 3, .c 131, .c 19, .c 3, .c 5, .c 83,
  .c 3, .c 439, .p pv3 [pv2,pv3,pv251,pv367], .c 3,
]
private theorem h0067c14 : checkBlock 552451 128 b0067c14 = true := by
  decide +kernel

private def b0067c15 : List Row := [
  .p pv2 [pv2,pv7,pv11,pv37,pv97], .p pv17 [pv2,pv3,pv13,pv1181], .c 3, .c 7, .c 5, .c 3, .c 449,
  .c 13, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv31,pv1783], .c 163, .c 3, .c 53, .c 11, .c 3,
  .c 37, .c 5, .c 3, .p pv3 [pv2,pv7,pv19,pv1039], .p pv41 [pv2,pv3,pv5,pv11,pv67], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv73,pv631], .c 3, .c 11, .c 79, .c 3, .c 19, .c 7, .c 3, .c 13, .c 5, .c 3,
  .c 89, .c 521, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv19,pv373], .c 3,
  .p pv7 [pv2,pv5,pv7,pv53,pv149], .p pv5 [pv2,pv3,pv31,pv743], .c 3, .c 7, .c 13, .c 3, .c 41,
  .c 5, .c 3, .p pv3 [pv2,pv43,pv1607], .c 7, .c 3, .c 5, .c 37, .c 3,
  .p pv2 [pv2,pv5,pv131,pv211], .c 17, .c 3, .c 11, .c 73, .c 3, .p pv3 [pv2,pv7,pv617], .c 5,
  .c 3, .c 7, .p pv29 [pv2,pv3,pv5,pv17,pv271], .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv13163], .c 3,
  .c 13, .c 7, .c 3, .c 17, .p pv2 [pv2,pv3,pv92143], .c 3, .c 83, .c 5, .c 3, .c 107, .c 11,
  .c 3, .c 5, .c 13, .c 3, .c 7, .p pv7 [pv2,pv3,pv11,pv8377], .c 3, .p pv5 [pv2,pv276443], .c 59,
  .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv276449], .c 659, .c 3, .c 5, .c 307, .c 3, .c 719,
  .p pv5 [pv2,pv3,pv11519], .c 3, .p pv2 [pv2,pv7,pv13,pv31], .c 19, .c 3, .c 7, .c 5, .c 3,
  .c 13, .c 179, .c 3, .c 5, .c 7, .c 3, .c 433, .c 23, .c 3, .c 31, .c 53, .c 3, .c 251, .c 5,
  .c 3, .c 11, .c 379,
]
private theorem h0067c15 : checkBlock 552707 128 b0067c15 = true := by
  decide +kernel

private def b0067c16 : List Row := [
  .c 3, .c 5, .c 41, .c 3, .p pv2 [pv2,pv5,pv11,pv457], .c 431, .c 3, .c 607, .c 7, .c 3,
  .p pv5 [pv2,pv283,pv977], .c 5, .c 3, .c 23, .p pv61 [pv2,pv3,pv5,pv18433], .c 3, .c 5, .c 97,
  .c 3, .c 29, .c 11, .c 3, .c 7, .c 31, .c 3, .p pv2 [pv2,pv23,pv6011], .c 5, .c 3, .c 71, .c 7,
  .c 3, .c 5, .c 17, .c 3, .c 211, .c 13, .c 3, .p pv2 [pv2,pv11,pv12569], .c 37, .c 3,
  .p pv2 [pv2,pv7,pv39503], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv1229], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv823], .c 3, .c 17, .c 7, .c 3, .p pv2 [pv2,pv43,pv59,pv109], .c 11, .c 3,
  .p pv3 [pv2,pv13,pv2659], .c 5, .c 3, .c 79, .c 23, .c 3, .c 5, .c 61, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv46091], .c 3, .p pv3 [pv2,pv47,pv1471], .p pv23 [pv2,pv3,pv7,pv13,pv1013],
  .c 3, .p pv5 [pv2,pv11,pv31,pv811], .c 5, .c 3, .c 19, .c 13, .c 3, .c 5, .c 29, .c 3, .c 73,
  .p pv2 [pv2,pv3,pv10243], .c 3, .c 23, .c 17, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv193,pv1433],
  .p pv2 [pv2,pv3,pv5,pv7,pv439], .c 3, .c 5, .c 7, .c 3, .c 353, .p pv5 [pv2,pv3,pv43,pv67],
  .c 3, .c 11, .c 373, .c 3, .c 13, .c 5, .c 3, .c 277, .p pv11 [pv2,pv3,pv5,pv18439], .c 3, .c 5,
  .c 101, .c 3, .p pv2 [pv2,pv5,pv17,pv1627], .c 641, .c 3, .c 37, .c 7, .c 3,
  .p pv3 [pv2,pv69149], .c 5, .c 3, .c 227, .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv137,pv673], .c 3,
  .p pv2 [pv2,pv5,pv7,pv1129], .c 41, .c 3, .c 7,
]
private theorem h0067c16 : checkBlock 552963 128 b0067c16 = true := by
  decide +kernel

private def b0067c17 : List Row := [
  .c 23, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv13,pv10639], .c 7, .c 3, .c 5, .c 47, .c 3, .c 13,
  .c 59, .c 3, .c 727, .p pv13 [pv2,pv3,pv17,pv113], .c 3, .p pv2 [pv2,pv7,pv19759], .c 5, .c 3,
  .c 7, .c 19, .c 3, .c 5, .c 11, .c 3, .c 167, .c 7, .c 3, .p pv2 [pv2,pv138319],
  .p pv3 [pv2,pv3,pv11,pv83,pv101], .c 3, .c 509, .c 5, .c 3, .c 11, .c 29, .c 3, .c 5, .c 107,
  .c 3, .c 7, .c 71, .c 3, .c 443, .p pv23 [pv2,pv3,pv7,pv941], .c 3, .c 89, .c 5, .c 3, .c 13,
  .c 257, .c 3, .c 5, .c 191, .c 3, .c 47, .c 11, .c 3, .c 19, .c 127, .c 3, .c 7, .c 5, .c 3,
  .c 29, .p pv3 [pv2,pv3,pv5,pv7,pv17,pv31], .c 3, .c 5, .c 7, .c 3, .c 59,
  .p pv2 [pv2,pv3,pv92227], .c 3, .c 17, .p pv7 [pv2,pv3,pv23057], .c 3, .c 53, .c 5, .c 3,
  .c 101, .c 31, .c 3, .c 5, .c 631, .c 3, .c 499, .c 109, .c 3, .c 13, .c 7, .c 3, .c 23, .c 5,
  .c 3, .c 37, .p pv2 [pv2,pv3,pv5,pv11,pv13,pv43], .c 3, .c 5, .p pv5 [pv2,pv3,pv23059], .c 3,
  .c 11, .c 13, .c 3, .c 7, .c 563, .c 3, .p pv3 [pv2,pv11,pv19,pv331], .c 5, .c 3,
  .p pv19 [pv2,pv167,pv1657], .c 7, .c 3, .c 5, .p pv11 [pv2,pv3,pv37,pv277], .c 3, .c 19, .c 43,
  .c 3, .p pv3 [pv2,pv34591], .c 41, .c 3, .p pv5 [pv2,pv7,pv13,pv3041], .c 5, .c 3, .c 7,
  .p pv19 [pv2,pv3,pv5,pv19,pv971], .c 3,
]
private theorem h0067c17 : checkBlock 553219 128 b0067c17 = true := by
  decide +kernel

private def b0067c18 : List Row := [
  .c 5, .c 293, .c 3, .p pv3 [pv2,pv5,pv101,pv137], .c 7, .c 3, .c 11, .c 19, .c 3, .c 229, .c 5,
  .c 3, .c 419, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv92251], .c 3, .c 7, .p pv5 [pv2,pv3,pv23063],
  .c 3, .p pv2 [pv2,pv71,pv1949], .c 47, .c 3, .c 29, .c 5, .c 3, .p pv3 [pv2,pv69191], .c 11,
  .c 3, .c 5, .c 17, .c 3, .c 23, .p pv5 [pv2,pv3,pv11,pv8387], .c 3, .c 389,
  .p pv2 [pv2,pv3,pv163,pv283], .c 3, .c 7, .c 5, .c 3, .c 73, .p pv43 [pv2,pv3,pv5,pv7,pv659],
  .c 3, .c 5, .c 7, .c 3, .c 17, .p pv2 [pv2,pv3,pv15377], .c 3, .c 241, .c 13, .c 3,
  .p pv5 [pv2,pv41,pv43,pv157], .c 5, .c 3, .p pv2 [pv2,pv7,pv17,pv1163],
  .p pv11 [pv2,pv3,pv5,pv6151], .c 3, .c 5, .c 11, .c 3, .p pv7 [pv2,pv5,pv173], .c 19, .c 3,
  .p pv5 [pv2,pv131,pv2113], .c 7, .c 3, .c 47, .c 5, .c 3, .c 11, .c 67, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv30757], .c 3, .c 13, .c 23, .c 3, .c 7, .c 17, .c 3, .p pv2 [pv2,pv276821],
  .c 5, .c 3, .p pv3 [pv2,pv34603], .c 7, .c 3, .c 5, .c 13, .c 3, .c 461, .c 11, .c 3,
  .p pv2 [pv2,pv276833], .c 89, .c 3, .c 17, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv769], .c 3,
  .c 5, .p pv7 [pv2,pv3,pv7,pv13183], .c 3, .c 31, .c 7, .c 3, .c 29,
  .p pv2 [pv2,pv3,pv19,pv1619], .c 3, .p pv5 [pv2,pv23,pv12037], .c 5, .c 3, .c 13, .c 43, .c 3,
  .c 5, .c 19, .c 3, .c 7, .c 277, .c 3, .p pv5 [pv2,pv29,pv9547], .c 11,
]
private theorem h0067c18 : checkBlock 553475 128 b0067c18 = true := by
  decide +kernel

private def b0067c19 : List Row := [
  .c 3, .p pv2 [pv2,pv138433], .c 5, .c 3, .c 157, .c 17, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv41,pv2251], .c 3, .c 11, .c 31, .c 3, .p pv2 [pv2,pv7,pv19777],
  .p pv19 [pv2,pv3,pv17,pv61,pv89], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv69221], .c 23, .c 3,
  .c 5, .c 7, .c 3, .c 401, .c 101, .c 3, .c 13, .p pv7 [pv2,pv3,pv15383], .c 3, .c 19, .c 5,
  .c 3, .c 317, .c 47, .c 3, .c 5, .c 433, .c 3, .p pv2 [pv2,pv5,pv55381], .c 13, .c 3, .c 11,
  .c 7, .c 3, .c 521, .c 5, .c 3, .c 109, .c 19, .c 3, .c 5, .p pv5 [pv2,pv3,pv46153], .c 3,
  .c 233, .c 17, .c 3, .c 7, .p pv11 [pv2,pv3,pv47,pv491], .c 3, .c 37, .c 5, .c 3, .c 83, .c 7,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv92311], .c 3, .c 29, .p pv7 [pv2,pv3,pv11,pv1049], .c 3, .c 17,
  .c 673, .c 3, .c 11, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .p pv29 [pv2,pv3,pv7,pv157], .c 3,
  .p pv2 [pv2,pv5,pv29,pv191], .c 7, .c 3, .c 19, .c 23, .c 3, .c 683, .c 5, .c 3,
  .p pv7 [pv2,pv419,pv661], .p pv31 [pv2,pv3,pv5,pv577], .c 3, .c 5, .c 11, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv23,pv223], .c 3, .c 359, .c 31, .c 3, .c 13, .c 5, .c 3, .c 11, .c 41, .c 3,
  .c 5, .c 251, .c 3, .p pv3 [pv2,pv5,pv11,pv1259], .p pv2 [pv2,pv3,pv17,pv5431], .c 3, .c 97,
  .c 13, .c 3, .c 7, .c 5, .c 3, .c 17, .p pv11 [pv2,pv3,pv5,pv7,pv1319], .c 3, .c 5,
]
private theorem h0067c19 : checkBlock 553731 128 b0067c19 = true := by
  decide +kernel

private def b0067c20 : List Row := [
  .c 7, .c 3, .p pv7 [pv2,pv5,pv55399], .c 11, .c 3, .c 73, .c 131, .c 3,
  .p pv2 [pv2,pv19,pv61,pv239], .c 5, .c 3, .c 53, .p pv2 [pv2,pv3,pv5,pv59,pv313], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv29,pv199], .c 3, .c 13, .c 67, .c 3, .c 79, .c 7, .c 3, .c 41, .c 5, .c 3,
  .c 113, .c 181, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv7,pv1583], .c 157, .c 3, .c 7, .c 11,
  .c 3, .c 31, .c 5, .c 3, .c 59, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv15391], .c 3, .c 11, .c 47,
  .c 3, .p pv5 [pv2,pv13,pv101,pv211], .p pv11 [pv2,pv3,pv23087], .c 3, .c 23, .c 5, .c 3, .c 7,
  .c 127, .c 3, .c 5, .c 227, .c 3, .c 547, .c 7, .c 3, .p pv2 [pv2,pv19,pv23,pv317], .c 173,
  .c 3, .p pv2 [pv2,pv461,pv601], .c 5, .c 3, .p pv3 [pv2,pv59,pv587], .c 149, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv2099], .c 3, .c 7, .c 73, .c 3, .c 11, .c 17, .c 3, .c 107, .c 5, .c 3,
  .c 347, .c 29, .c 3, .c 5, .p pv3 [pv2,pv3,pv17,pv1811], .c 3, .p pv7 [pv2,pv5,pv151,pv367],
  .c 19, .c 3, .c 13, .p pv2 [pv2,pv3,pv92363], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv138547],
  .c 11, .c 3, .c 5, .c 7, .c 3, .c 383, .c 13, .c 3, .p pv5 [pv2,pv487,pv569],
  .p pv7 [pv2,pv3,pv23,pv251], .c 3, .c 11, .c 5, .c 3, .c 29, .c 53, .c 3, .c 5, .c 43, .c 3,
  .c 23, .p pv19 [pv2,pv3,pv7,pv3299], .c 3, .p pv2 [pv2,pv138559], .c 7, .c 3,
]
private theorem h0067c20 : checkBlock 553987 128 b0067c20 = true := by
  decide +kernel

private def b0067c21 : List Row := [
  .c 103, .c 5, .c 3, .c 19, .c 17, .c 3, .c 5, .c 11, .c 3, .c 131, .p pv3 [pv2,pv3,pv92377],
  .c 3, .c 7, .p pv23 [pv2,pv3,pv11,pv13,pv17,pv19], .c 3, .c 167, .c 5, .c 3, .c 11, .c 7, .c 3,
  .c 5, .c 19, .c 3, .c 67, .p pv5 [pv2,pv3,pv89,pv173], .c 3, .c 37, .p pv2 [pv2,pv3,pv92383],
  .c 3, .p pv7 [pv2,pv7,pv17,pv137], .c 5, .c 3, .c 7, .c 31, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv6599], .c 3, .c 151, .c 7, .c 3, .c 53, .c 467, .c 3, .c 13, .c 5, .c 3,
  .c 491, .c 457, .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv23,pv103], .c 3, .c 7, .c 17, .c 3, .c 83,
  .c 13, .c 3, .c 19, .c 5, .c 3, .c 23, .c 37, .c 3, .c 5, .p pv7 [pv2,pv3,pv23099], .c 3, .c 89,
  .p pv7 [pv2,pv3,pv19,pv1621], .c 3, .c 17, .c 11, .c 3, .c 7, .c 5, .c 3, .c 43, .c 19, .c 3,
  .c 5, .c 7, .c 3, .c 11, .c 281, .c 3, .p pv3 [pv2,pv34651], .p pv2 [pv2,pv3,pv10267], .c 3,
  .c 59, .c 5, .c 3, .c 61, .p pv11 [pv2,pv3,pv5,pv18481], .c 3, .c 5, .c 13, .c 3, .c 571, .c 41,
  .c 3, .p pv5 [pv2,pv277223], .c 7, .c 3, .p pv2 [pv2,pv97,pv1429], .c 5, .c 3, .c 47, .c 23,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv31,pv271], .c 3, .c 139, .c 191, .c 3, .c 7, .c 647, .c 3,
  .c 109, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 31,
]
private theorem h0067c21 : checkBlock 554243 128 b0067c21 = true := by
  decide +kernel

private def b0067c22 : List Row := [
  .c 3, .c 79, .p pv11 [pv2,pv3,pv13,pv7109], .c 3, .c 23, .c 29, .c 3, .c 311, .c 5, .c 3, .c 7,
  .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv163], .c 3, .p pv2 [pv2,pv5,pv23,pv2411], .c 7, .c 3,
  .c 367, .c 53, .c 3, .c 11, .c 5, .c 3, .c 97, .c 61, .c 3, .c 5, .c 17, .c 3, .c 7, .c 353,
  .c 3, .c 13, .p pv17 [pv2,pv3,pv7,pv3301], .c 3, .p pv3 [pv2,pv19,pv7297], .c 5, .c 3, .c 661,
  .c 71, .c 3, .c 5, .c 11, .c 3, .c 17, .c 13, .c 3, .p pv3 [pv2,pv7,pv29,pv683], .c 23, .c 3,
  .c 7, .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv7,pv19,pv139], .c 3, .c 5, .c 7, .c 3, .c 31,
  .c 151, .c 3, .p pv2 [pv2,pv67,pv4139], .c 19, .c 3, .p pv3 [pv2,pv13,pv5333], .c 5, .c 3,
  .p pv7 [pv2,pv7,pv173,pv229], .p pv11 [pv2,pv3,pv5,pv2311], .c 3, .c 5, .c 47, .c 3, .c 373,
  .c 11, .c 3, .c 43, .c 7, .c 3, .p pv5 [pv2,pv277331], .c 5, .c 3, .p pv2 [pv2,pv23,pv6029],
  .c 13, .c 3, .c 5, .p pv11 [pv2,pv3,pv17,pv2719], .c 3, .c 157, .c 29, .c 3, .c 7, .c 41, .c 3,
  .c 17, .c 5, .c 3, .p pv2 [pv2,pv53,pv5233], .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv30817], .c 3,
  .p pv11 [pv2,pv5,pv13,pv17,pv251], .c 137, .c 3, .c 113, .c 11, .c 3, .c 13, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv11,pv41], .c 3, .c 5, .c 23, .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv277373], .c 13, .c 3, .p pv3 [pv2,pv11,pv197],
]
private theorem h0067c22 : checkBlock 554499 128 b0067c22 = true := by
  decide +kernel

private def b0067c23 : List Row := [
  .c 5, .c 3, .p pv7 [pv2,pv103,pv2693], .c 17, .c 3, .c 5, .p pv3 [pv2,pv3,pv92461], .c 3, .c 7,
  .c 233, .c 3, .c 59, .p pv2 [pv2,pv3,pv7,pv17,pv37], .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv47,pv227], .p pv3 [pv2,pv3,pv5,pv18493], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv467], .c 3, .c 13, .p pv2 [pv2,pv3,pv92467], .c 3, .c 11, .c 503, .c 3,
  .c 7, .c 5, .c 3, .c 19, .p pv2 [pv2,pv3,pv5,pv7,pv1321], .c 3, .c 5, .c 7, .c 3, .c 277,
  .p pv5 [pv2,pv3,pv3853], .c 3, .p pv2 [pv2,pv59,pv2351], .p pv17 [pv2,pv3,pv19,pv31,pv157],
  .c 3, .p pv2 [pv2,pv277421], .c 5, .c 3, .p pv3 [pv2,pv7,pv2477], .c 11, .c 3, .c 5, .c 19,
  .c 3, .c 103, .c 17, .c 3, .c 229, .c 7, .c 3, .c 11, .c 5, .c 3, .c 13, .c 733, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv29,pv1063], .c 3, .p pv17 [pv2,pv5,pv7,pv7927], .p pv7 [pv2,pv3,pv13,pv3557],
  .c 3, .c 7, .p pv3 [pv2,pv3,pv23,pv4021], .c 3, .c 523, .c 5, .c 3, .c 643, .c 7, .c 3, .c 5,
  .c 11, .c 3, .c 23, .p pv3 [pv2,pv3,pv30829], .c 3, .p pv5 [pv2,pv37,pv7499], .c 47, .c 3,
  .c 19, .c 5, .c 3, .c 7, .c 167, .c 3, .c 5, .c 269, .c 3, .p pv11 [pv2,pv5,pv11,pv1009], .c 7,
  .c 3, .c 13, .p pv3 [pv2,pv3,pv43,pv239], .c 3, .c 37, .c 5, .c 3, .p pv3 [pv2,pv69371], .c 19,
  .c 3, .c 5, .p pv13 [pv2,pv3,pv41,pv47], .c 3, .c 7, .c 11, .c 3, .c 137, .c 739, .c 3, .c 31,
  .c 5, .c 3, .c 17, .c 43, .c 3, .c 5, .c 71, .c 3,
]
private theorem h0067c23 : checkBlock 554755 128 b0067c23 = true := by
  decide +kernel

private def b0067c24 : List Row := [
  .c 199, .c 23, .c 3, .c 41, .c 73, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv19,pv67,pv109], .c 29,
  .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv3469], .p pv3 [pv2,pv3,pv92507], .c 3, .c 19, .c 11,
  .c 3, .p pv2 [pv2,pv138763], .c 5, .c 3, .c 23, .c 13, .c 3, .c 5, .c 17, .c 3, .c 11,
  .p pv17 [pv2,pv3,pv7,pv59], .c 3, .p pv2 [pv2,pv151,pv919], .c 7, .c 3,
  .p pv2 [pv2,pv11,pv23,pv1097], .c 5, .c 3, .c 29, .p pv2 [pv2,pv3,pv5,pv18503], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv101,pv229], .c 3, .c 17, .c 389, .c 3, .c 7, .p pv2 [pv2,pv3,pv167,pv277],
  .c 3, .c 13, .c 5, .c 3, .p pv13 [pv2,pv17,pv29,pv563], .c 7, .c 3, .c 5, .c 181, .c 3, .c 59,
  .c 79, .c 3, .c 11, .c 13, .c 3, .p pv5 [pv2,pv7,pv19,pv2087], .c 5, .c 3, .c 7, .c 23, .c 3,
  .c 5, .c 173, .c 3, .c 19, .c 7, .c 3, .p pv5 [pv2,pv139,pv1997], .c 17, .c 3, .c 43, .c 5,
  .c 3, .c 31, .c 11, .c 3, .c 5, .c 83, .c 3, .c 7, .c 263, .c 3, .c 23, .c 19, .c 3, .c 11,
  .c 5, .c 3, .p pv3 [pv2,pv69401], .c 47, .c 3, .c 5, .c 13, .c 3,
  .p pv19 [pv2,pv5,pv17,pv23,pv71], .c 107, .c 3, .c 151, .c 67, .c 3, .c 7, .c 5, .c 3, .c 233,
  .c 31, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv2221], .p pv2 [pv2,pv3,pv46271], .c 3,
  .p pv3 [pv2,pv13,pv19,pv281], .c 37, .c 3, .c 29, .c 5,
]
private theorem h0067c24 : checkBlock 555011 128 b0067c24 = true := by
  decide +kernel

private def b0067c25 : List Row := [
  .c 3, .c 11, .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv46273], .c 3, .c 53, .c 61, .c 3,
  .p pv5 [pv2,pv277643], .c 7, .c 3, .p pv2 [pv2,pv29,pv4787], .c 5, .c 3, .c 421,
  .p pv2 [pv2,pv3,pv5,pv617], .c 3, .c 5, .p pv3 [pv2,pv3,pv92551], .c 3, .c 73, .c 11, .c 3,
  .c 7, .c 509, .c 3, .c 149, .c 5, .c 3, .c 557, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv857], .c 3,
  .c 163, .c 197, .c 3, .c 13, .p pv2 [pv2,pv3,pv46279], .c 3, .c 83, .c 5, .c 3, .c 7,
  .p pv71 [pv2,pv3,pv5,pv13,pv89], .c 3, .c 5, .c 59, .c 3, .c 127, .c 7, .c 3, .c 257, .c 11,
  .c 3, .p pv5 [pv2,pv277691], .c 5, .c 3, .c 19, .p pv3 [pv2,pv3,pv5,pv11,pv17], .c 3, .c 5,
  .c 373, .c 3, .c 7, .c 397, .c 3, .c 17, .c 199, .c 3, .c 449, .c 5, .c 3,
  .p pv2 [pv2,pv331,pv839], .p pv2 [pv2,pv3,pv5,pv9257], .c 3, .c 5, .c 19, .c 3, .c 43, .c 71,
  .c 3, .c 29, .p pv3 [pv2,pv3,pv13,pv7121], .c 3, .c 7, .c 5, .c 3, .c 79, .c 13, .c 3, .c 5,
  .c 7, .c 3, .p pv3 [pv2,pv5,pv27773], .c 251, .c 3, .c 11, .c 227, .c 3, .c 23, .c 5, .c 3,
  .c 103, .c 37, .c 3, .c 5, .p pv3 [pv2,pv3,pv92581], .c 3, .p pv2 [pv2,pv5,pv13,pv4273], .c 47,
  .c 3, .c 67, .c 7, .c 3, .c 13, .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .c 43, .c 3,
  .p pv3 [pv2,pv5,pv7,pv31],
]
private theorem h0067c25 : checkBlock 555267 128 b0067c25 = true := by
  decide +kernel

private def b0067c26 : List Row := [
  .p pv5 [pv2,pv3,pv11,pv19,pv443], .c 3, .c 7, .c 13, .c 3, .c 11, .c 5, .c 3, .c 433, .c 7,
  .c 3, .c 5, .c 347, .c 3, .c 31, .c 29, .c 3, .p pv2 [pv2,pv138889], .c 431, .c 3, .c 211, .c 5,
  .c 3, .c 7, .c 131, .c 3, .c 5, .c 11, .c 3, .c 13, .c 7, .c 3, .c 47,
  .p pv2 [pv2,pv3,pv11,pv23,pv61], .c 3, .p pv3 [pv2,pv37,pv1877], .c 5, .c 3, .c 11, .c 101,
  .c 3, .c 5, .c 13, .c 3, .c 7, .c 31, .c 3, .c 19, .c 191, .c 3, .c 157, .c 5, .c 3, .c 37,
  .c 67, .c 3, .c 5, .p pv2 [pv2,pv3,pv19,pv2437], .c 3, .c 593, .c 11, .c 3, .c 193, .c 61, .c 3,
  .c 7, .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv7], .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv181,pv307], .c 41, .c 3, .p pv2 [pv2,pv11,pv73,pv173], .c 17, .c 3,
  .p pv2 [pv2,pv109,pv2549], .c 5, .c 3, .c 43, .p pv2 [pv2,pv3,pv5,pv18523], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv17,pv227], .c 3, .c 317, .c 23, .c 3, .p pv2 [pv2,pv31,pv8963], .c 7, .c 3,
  .c 17, .c 5, .c 3, .c 263, .c 59, .c 3, .c 5, .c 29, .c 3, .c 11, .c 383, .c 3, .c 7,
  .p pv23 [pv2,pv3,pv92623], .c 3, .p pv5 [pv2,pv11,pv25261], .c 5, .c 3, .c 23, .c 7, .c 3, .c 5,
  .c 311, .c 3, .p pv3 [pv2,pv5,pv6947], .c 13, .c 3, .p pv5 [pv2,pv277883], .c 19, .c 3, .c 647,
  .c 5, .c 3,
]
private theorem h0067c26 : checkBlock 555523 128 b0067c26 = true := by
  decide +kernel

private def b0067c27 : List Row := [
  .c 7, .c 17, .c 3, .c 5, .c 719, .c 3, .c 109, .c 7, .c 3, .c 11, .c 31, .c 3, .c 101, .c 5,
  .c 3, .c 137, .c 53, .c 3, .c 5, .c 677, .c 3, .c 7, .p pv7 [pv2,pv3,pv47,pv73], .c 3,
  .p pv2 [pv2,pv19,pv14627], .p pv11 [pv2,pv3,pv7,pv13,pv509], .c 3, .c 131, .c 5, .c 3, .c 59,
  .c 11, .c 3, .c 5, .c 113, .c 3, .c 37, .p pv5 [pv2,pv3,pv11,pv4211], .c 3,
  .p pv3 [pv2,pv7,pv709], .c 71, .c 3, .c 7, .c 5, .c 3, .c 47, .p pv3 [pv2,pv3,pv5,pv7,pv2647],
  .c 3, .c 5, .c 7, .c 3, .c 389, .c 17, .c 3, .c 23, .c 587, .c 3, .c 13, .c 5, .c 3, .c 67,
  .c 29, .c 3, .c 5, .c 11, .c 3, .c 631, .c 569, .c 3, .c 17, .c 7, .c 3, .c 31, .c 5, .c 3,
  .c 11, .p pv3 [pv2,pv3,pv5,pv29,pv71], .c 3, .c 5, .c 157, .c 3, .p pv2 [pv2,pv5,pv7,pv11,pv19],
  .c 167, .c 3, .c 7, .c 523, .c 3, .p pv3 [pv2,pv34747], .c 5, .c 3, .c 19, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv67,pv461], .c 3, .c 13, .c 11, .c 3, .c 307, .c 23, .c 3, .c 89, .c 5, .c 3,
  .c 7, .c 613, .c 3, .c 5, .c 13, .c 3, .c 41, .c 7, .c 3, .p pv7 [pv2,pv11,pv127,pv199], .c 109,
  .c 3, .c 419, .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv3089], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv92671], .c 3, .c 7, .c 43,
]
private theorem h0067c27 : checkBlock 555779 128 b0067c27 = true := by
  decide +kernel

private def b0067c28 : List Row := [
  .c 3, .p pv3 [pv2,pv13,pv17,pv37], .c 11, .c 3, .p pv2 [pv2,pv41,pv6781], .c 5, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv5,pv11,pv337], .c 3, .c 5, .c 47, .c 3, .c 11, .c 463, .c 3,
  .p pv2 [pv2,pv7,pv39719], .p pv2 [pv2,pv3,pv149,pv311], .c 3, .c 7, .c 5, .c 3, .c 107, .c 79,
  .c 3, .c 5, .c 7, .c 3, .c 359, .p pv2 [pv2,pv3,pv19,pv271], .c 3, .c 103, .c 281, .c 3,
  .p pv5 [pv2,pv278051], .c 5, .c 3, .c 31, .c 19, .c 3, .c 5, .c 23, .c 3, .c 17,
  .p pv5 [pv2,pv3,pv7,pv13241], .c 3, .c 11, .c 7, .c 3, .c 29, .c 5, .c 3, .c 139, .c 421, .c 3,
  .c 5, .c 37, .c 3, .c 47, .c 13, .c 3, .c 7, .p pv3 [pv2,pv3,pv92693], .c 3, .c 23, .c 5, .c 3,
  .c 457, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv11587], .c 3, .p pv2 [pv2,pv5,pv27809], .c 83, .c 3,
  .c 19, .c 17, .c 3, .c 11, .c 5, .c 3, .c 7, .c 313, .c 3, .c 5, .c 101, .c 3,
  .p pv2 [pv2,pv5,pv55621], .c 7, .c 3, .c 149, .p pv3 [pv2,pv3,pv13,pv2377], .c 3, .c 17, .c 5,
  .c 3, .p pv2 [pv2,pv241,pv577], .c 13, .c 3, .c 5, .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv92707],
  .c 3, .c 41, .c 29, .c 3, .p pv2 [pv2,pv59,pv2357], .c 5, .c 3, .c 11,
  .p pv41 [pv2,pv3,pv5,pv73,pv127], .c 3, .c 5, .p pv2 [pv2,pv3,pv83,pv1117], .c 3,
  .p pv7 [pv2,pv5,pv11,pv13,pv389], .p pv37 [pv2,pv3,pv3863], .c 3, .c 167,
  .p pv11 [pv2,pv3,pv23,pv29,pv139], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv41,pv53],
]
private theorem h0067c28 : checkBlock 556035 128 b0067c28 = true := by
  decide +kernel

private def b0067c29 : List Row := [
  .c 17, .c 3, .c 5, .c 7, .c 3, .c 19, .c 11, .c 3, .c 29, .c 13, .c 3, .p pv3 [pv2,pv69539],
  .c 5, .c 3, .c 163, .p pv11 [pv2,pv3,pv5,pv19,pv61], .c 3, .c 5, .p pv3 [pv2,pv3,pv31,pv997],
  .c 3, .p pv2 [pv2,pv5,pv55633], .c 73, .c 3, .c 509, .c 7, .c 3, .p pv5 [pv2,pv17,pv16363],
  .c 5, .c 3, .c 83, .p pv3 [pv2,pv3,pv5,pv3709], .c 3, .c 5, .c 31, .c 3, .c 13, .c 271, .c 3,
  .c 7, .c 11, .c 3, .p pv2 [pv2,pv367,pv379], .c 5, .c 3, .c 311, .c 7, .c 3, .c 5, .c 13, .c 3,
  .c 11, .c 17, .c 3, .c 79, .p pv23 [pv2,pv3,pv30911], .c 3, .p pv2 [pv2,pv7,pv11,pv3613], .c 5,
  .c 3, .c 7, .c 41, .c 3, .c 5, .c 139, .c 3, .c 431, .c 7, .c 3, .c 17, .c 59, .c 3, .c 47,
  .c 5, .c 3, .c 13, .p pv11 [pv2,pv3,pv5,pv4637], .c 3, .c 5, .c 53, .c 3, .c 7, .c 19, .c 3,
  .c 11, .p pv7 [pv2,pv3,pv7,pv13249], .c 3, .c 43, .c 5, .c 3, .c 241, .c 599, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv79,pv587], .c 3, .c 29, .p pv2 [pv2,pv3,pv163,pv569], .c 3,
  .p pv5 [pv2,pv7,pv39749], .c 97, .c 3, .c 7, .c 5, .c 3, .c 383, .c 11, .c 3, .c 5, .c 7, .c 3,
  .c 179, .p pv5 [pv2,pv3,pv11,pv17,pv31], .c 3, .c 13, .p pv17 [pv2,pv3,pv92753], .c 3, .c 11,
  .c 5, .c 3, .c 17, .c 23, .c 3, .c 5, .p pv19 [pv2,pv3,pv23189], .c 3, .c 173, .c 13, .c 3,
]
private theorem h0067c29 : checkBlock 556291 128 b0067c29 = true := by
  decide +kernel

private def b0067c30 : List Row := [
  .c 59, .c 7, .c 3, .c 53, .c 5, .c 3, .p pv11 [pv2,pv278279], .c 269, .c 3, .c 5, .c 11, .c 3,
  .c 673, .p pv7 [pv2,pv3,pv46381], .c 3, .c 7, .p pv2 [pv2,pv3,pv11,pv937], .c 3,
  .p pv5 [pv2,pv13,pv21407], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 17, .c 3,
  .p pv3 [pv2,pv5,pv11,pv23], .c 199, .c 3, .p pv5 [pv2,pv53,pv59,pv89],
  .p pv17 [pv2,pv3,pv13,pv223], .c 3, .p pv2 [pv2,pv7,pv103,pv193], .c 5, .c 3, .c 7, .c 13, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv7,pv29,pv457], .c 3, .c 17, .c 7, .c 3, .c 233,
  .p pv13 [pv2,pv3,pv113,pv821], .c 3, .c 19, .c 5, .c 3, .c 409, .p pv2 [pv2,pv3,pv5,pv1237],
  .c 3, .c 5, .c 41, .c 3, .c 7, .c 109, .c 3, .c 31, .c 23, .c 3, .c 13, .c 5, .c 3,
  .p pv7 [pv2,pv43,pv6473], .c 19, .c 3, .c 5, .p pv19 [pv2,pv3,pv13,pv61], .c 3,
  .p pv2 [pv2,pv5,pv179,pv311], .p pv2 [pv2,pv3,pv23,pv2017], .c 3, .p pv3 [pv2,pv7,pv9941],
  .c 11, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv139177], .c 71, .c 3, .c 5, .c 7, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv157,pv197], .c 3, .p pv5 [pv2,pv278363], .c 31, .c 3, .c 17, .c 5, .c 3,
  .c 37, .p pv2 [pv2,pv3,pv5,pv1031], .c 3, .c 5, .c 61, .c 3, .c 13,
  .p pv11 [pv2,pv3,pv7,pv1657], .c 3, .c 19, .c 7, .c 3, .p pv2 [pv2,pv47,pv5923], .c 5, .c 3,
  .p pv3 [pv2,pv127,pv137], .c 29, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv7,pv41,pv97], .c 59,
  .c 3, .c 7, .p pv11 [pv2,pv3,pv46399], .c 3, .p pv3 [pv2,pv79,pv881], .c 5, .c 3,
  .p pv11 [pv2,pv11,pv25309], .c 7,
]
private theorem h0067c30 : checkBlock 556547 128 b0067c30 = true := by
  decide +kernel

private def b0067c31 : List Row := [
  .c 3, .c 5, .c 23, .c 3, .p pv13 [pv2,pv5,pv55681], .c 37, .c 3, .p pv3 [pv2,pv13,pv2677],
  .p pv2 [pv2,pv3,pv17,pv53,pv103], .c 3, .p pv7 [pv2,pv7,pv31,pv1283], .c 5, .c 3, .c 7, .c 11,
  .c 3, .c 5, .c 67, .c 3, .p pv3 [pv2,pv5,pv13921], .c 7, .c 3, .c 83, .p pv11 [pv2,pv3,pv1289],
  .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv29,pv9601], .p pv2 [pv2,pv3,pv5,pv9281], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv30937], .c 3, .c 7, .c 89, .c 3, .c 97, .c 157, .c 3,
  .p pv2 [pv2,pv383,pv727], .c 5, .c 3, .c 373, .p pv11 [pv2,pv3,pv5,pv19,pv977], .c 3, .c 5,
  .c 11, .c 3, .c 59, .c 17, .c 3, .c 13, .c 19, .c 3, .c 7, .c 5, .c 3, .c 11, .c 103, .c 3,
  .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv11,pv61,pv83], .c 13, .c 3, .c 17, .p pv3 [pv2,pv3,pv30941],
  .c 3, .p pv5 [pv2,pv281,pv991], .c 5, .c 3, .c 521, .c 241, .c 3, .c 5, .p pv2 [pv2,pv3,pv191],
  .c 3, .c 37, .c 11, .c 3, .p pv5 [pv2,pv19,pv14657], .c 7, .c 3, .c 139, .c 5, .c 3, .c 43,
  .p pv17 [pv2,pv3,pv5,pv9283], .c 3, .c 5, .p pv2 [pv2,pv3,pv92831], .c 3, .c 23, .c 293, .c 3,
  .c 7, .p pv3 [pv2,pv3,pv13,pv37,pv193], .c 3, .c 29, .c 5, .c 3, .c 653, .c 7, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv23209], .c 3, .p pv3 [pv2,pv5,pv27851], .c 19, .c 3, .p pv2 [pv2,pv41,pv6793],
  .c 11, .c 3, .p pv3 [pv2,pv7,pv29], .c 5, .c 3, .c 7, .p pv37 [pv2,pv3,pv5,pv11,pv211], .c 3,
  .c 5, .c 277, .c 3, .c 11, .c 7, .c 3, .p pv3 [pv2,pv17],
]
private theorem h0067c31 : checkBlock 556803 128 b0067c31 = true := by
  decide +kernel

def rows0067 : List Row :=
  b0067c00 ++ b0067c01 ++ b0067c02 ++ b0067c03 ++ b0067c04 ++ b0067c05 ++ b0067c06 ++ b0067c07 ++
  b0067c08 ++ b0067c09 ++ b0067c10 ++ b0067c11 ++ b0067c12 ++ b0067c13 ++ b0067c14 ++ b0067c15 ++
  b0067c16 ++ b0067c17 ++ b0067c18 ++ b0067c19 ++ b0067c20 ++ b0067c21 ++ b0067c22 ++ b0067c23 ++
  b0067c24 ++ b0067c25 ++ b0067c26 ++ b0067c27 ++ b0067c28 ++ b0067c29 ++ b0067c30 ++ b0067c31

attribute [local irreducible] checkBlock checkRows checkPrime

theorem checked0067 : checkBlock 548867 4096 rows0067 = true :=
  checkBlock_append h0067c00 (
    checkBlock_append h0067c01 (
    checkBlock_append h0067c02 (
    checkBlock_append h0067c03 (
    checkBlock_append h0067c04 (
    checkBlock_append h0067c05 (
    checkBlock_append h0067c06 (
    checkBlock_append h0067c07 (
    checkBlock_append h0067c08 (
    checkBlock_append h0067c09 (
    checkBlock_append h0067c10 (
    checkBlock_append h0067c11 (
    checkBlock_append h0067c12 (
    checkBlock_append h0067c13 (
    checkBlock_append h0067c14 (
    checkBlock_append h0067c15 (
    checkBlock_append h0067c16 (
    checkBlock_append h0067c17 (
    checkBlock_append h0067c18 (
    checkBlock_append h0067c19 (
    checkBlock_append h0067c20 (
    checkBlock_append h0067c21 (
    checkBlock_append h0067c22 (
    checkBlock_append h0067c23 (
    checkBlock_append h0067c24 (
    checkBlock_append h0067c25 (
    checkBlock_append h0067c26 (
    checkBlock_append h0067c27 (
    checkBlock_append h0067c28 (
    checkBlock_append h0067c29 (
    checkBlock_append h0067c30 (
    h0067c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
