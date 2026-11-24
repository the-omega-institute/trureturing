/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks03/Block0252
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks03/Block0252.checked0252
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table030
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table031
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table035
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table036
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table042
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table052
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table067
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table092
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table138

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0252c00 : List Row := [
  .c 3, .p pv2 [pv2,pv19,pv23,pv1181], .c 7, .c 3, .c 5, .c 113, .c 3, .c 977, .c 11, .c 3, .c 19,
  .c 173, .c 3, .c 13, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv3823], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv13,pv19,pv199], .c 3, .p pv13 [pv2,pv5,pv43,pv4801], .c 7, .c 3,
  .p pv2 [pv2,pv11,pv46919], .c 13, .c 3, .p pv2 [pv2,pv1032221], .c 5, .c 3,
  .p pv3 [pv2,pv32257], .c 97, .c 3, .c 5, .c 23, .c 3, .c 7, .c 17, .c 3, .c 71, .c 11, .c 3,
  .c 41, .c 5, .c 3, .c 587, .c 29, .c 3, .c 5, .p pv17 [pv2,pv3,pv181,pv1901], .c 3, .c 11,
  .c 1039, .c 3, .c 17, .c 751, .c 3, .c 7, .c 5, .c 3, .c 53,
  .p pv3 [pv2,pv3,pv5,pv7,pv29,pv113], .c 3, .c 5, .c 7, .c 3, .c 19,
  .p pv5 [pv2,pv3,pv47,pv7321], .c 3, .p pv5 [pv2,pv23,pv37,pv1213], .p pv7 [pv2,pv3,pv59], .c 3,
  .c 89, .c 5, .c 3, .c 29, .c 101, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv10427], .c 3,
  .p pv11 [pv2,pv5,pv157,pv263], .c 1237, .c 3, .c 11, .c 7, .c 3, .c 37, .c 5, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv5,pv68819], .c 3, .c 5, .c 647, .c 3, .p pv2 [pv2,pv5,pv7,pv14747],
  .p pv29 [pv2,pv3,pv13,pv17,pv173], .c 3, .c 7, .p pv2 [pv2,pv3,pv172049], .c 3, .c 761, .c 5,
  .c 3, .c 17, .c 7, .c 3, .c 5, .c 467, .c 3, .p pv2 [pv2,pv5,pv206461], .c 233, .c 3, .c 439,
  .p pv2 [pv2,pv3,pv23,pv4987], .c 3, .c 11, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5, .c 37, .c 3,
  .c 23,
]
private theorem h0252c00 : checkBlock 2064387 128 b0252c00 = true := by
  decide +kernel

private def b0252c01 : List Row := [
  .c 7, .c 3, .c 13, .p pv19 [pv2,pv3,pv86027], .c 3, .p pv2 [pv2,pv516163], .c 5, .c 3, .c 73,
  .c 641, .c 3, .c 5, .c 11, .c 3, .c 7, .c 13, .c 3, .c 1093,
  .p pv7 [pv2,pv3,pv7,pv11,pv41,pv109], .c 3, .c 773, .c 5, .c 3, .c 11, .c 131, .c 3, .c 5,
  .c 353, .c 3, .c 17, .p pv3 [pv2,pv3,pv344117], .c 3, .c 157, .c 683, .c 3, .c 7, .c 5, .c 3,
  .c 41, .c 53, .c 3, .c 5, .c 7, .c 3, .c 43, .c 11, .c 3, .p pv3 [pv2,pv113,pv571], .c 67, .c 3,
  .c 101, .c 5, .c 3, .c 19, .c 13, .c 3, .c 5, .c 47, .c 3, .p pv3 [pv2,pv5,pv41,pv1259],
  .p pv2 [pv2,pv3,pv7,pv2341], .c 3, .p pv5 [pv2,pv11,pv127,pv739], .c 7, .c 3, .c 1423, .c 5,
  .c 3, .c 23, .p pv7 [pv2,pv3,pv5,pv11471], .c 3, .c 5, .c 19, .c 3, .c 83,
  .p pv5 [pv2,pv3,pv227,pv379], .c 3, .c 7, .c 11, .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv258101],
  .c 7, .c 3, .c 5, .c 31, .c 3, .c 11, .c 59, .c 3, .c 53, .c 13, .c 3,
  .p pv3 [pv2,pv7,pv11,pv419], .c 5, .c 3, .c 7, .c 103, .c 3, .c 5,
  .p pv17 [pv2,pv3,pv7,pv211,pv233], .c 3, .c 47, .c 7, .c 3, .p pv3 [pv2,pv258107], .c 37, .c 3,
  .c 19, .c 5, .c 3, .c 1427, .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv15643], .c 3, .c 7, .c 41,
  .c 3, .c 11, .c 89, .c 3, .c 71, .c 5, .c 3,
]
private theorem h0252c01 : checkBlock 2064643 128 b0252c01 = true := by
  decide +kernel

private def b0252c02 : List Row := [
  .p pv2 [pv2,pv11,pv47,pv1997], .c 19, .c 3, .c 5, .c 13, .c 3, .c 61, .p pv5 [pv2,pv3,pv43019],
  .c 3, .c 23, .p pv23 [pv2,pv3,pv344153], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv173,pv373],
  .c 11, .c 3, .c 5, .c 7, .c 3, .c 31, .p pv3 [pv2,pv3,pv11,pv10429], .c 3,
  .p pv5 [pv2,pv13,pv43,pv1847], .p pv2 [pv2,pv3,pv172079], .c 3, .c 11, .c 5, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv5,pv239], .c 3, .c 5, .c 1033, .c 3, .p pv2 [pv2,pv5,pv37,pv5581], .c 17,
  .c 3, .c 19, .c 7, .c 3, .p pv5 [pv2,pv1032491], .c 5, .c 3, .c 43, .c 149, .c 3, .c 5, .c 11,
  .c 3, .c 137, .c 29, .c 3, .c 7, .c 23, .c 3, .c 509, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5,
  .c 797, .c 3, .p pv11 [pv2,pv5,pv11,pv18773], .c 61, .c 3, .c 13, .c 47, .c 3,
  .p pv5 [pv2,pv7,pv147503], .c 5, .c 3, .c 7, .c 283, .c 3, .c 5, .c 211, .c 3, .c 29, .c 7,
  .c 3, .c 89, .c 281, .c 3, .p pv3 [pv2,pv19,pv6793], .c 5, .c 3, .c 233, .c 37, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv47,pv2441], .c 3, .c 7, .c 1031, .c 3, .c 73, .c 617, .c 3,
  .p pv5 [pv2,pv13,pv79427], .c 5, .c 3, .c 17, .p pv3 [pv2,pv3,pv5,pv19,pv3623], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv172093], .c 3, .p pv3 [pv2,pv5,pv12907], .c 83, .c 3, .c 31, .c 11, .c 3,
  .c 7, .c 5, .c 3, .c 79, .c 13, .c 3, .c 5, .c 7, .c 3, .c 11, .p pv5 [pv2,pv3,pv2689],
]
private theorem h0252c02 : checkBlock 2064899 128 b0252c02 = true := by
  decide +kernel

private def b0252c03 : List Row := [
  .c 3, .p pv2 [pv2,pv89,pv5801], .c 863, .c 3, .p pv2 [pv2,pv11,pv93871], .c 5, .c 3,
  .p pv3 [pv2,pv7,pv18439], .c 379, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv13,pv47], .c 457,
  .c 3, .p pv2 [pv2,pv19,pv54347], .c 7, .c 3, .c 13, .c 5, .c 3, .c 239, .c 389, .c 3, .c 5,
  .c 107, .c 3, .c 17, .p pv2 [pv2,pv3,pv57367], .c 3, .c 7, .c 13, .c 3, .c 109, .c 5, .c 3,
  .c 37, .c 7, .c 3, .c 5, .c 911, .c 3, .p pv3 [pv2,pv5,pv51631], .c 19, .c 3, .c 43, .c 1217,
  .c 3, .c 103, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv37,pv443], .c 3, .c 13,
  .c 7, .c 3, .c 61, .c 17, .c 3, .c 11, .c 5, .c 3, .c 83, .c 271, .c 3, .c 5, .c 13, .c 3, .c 7,
  .c 37, .c 3, .c 571, .p pv2 [pv2,pv3,pv7,pv23,pv1069], .c 3, .c 17, .c 5, .c 3, .c 19, .c 47,
  .c 3, .c 5, .c 11, .c 3, .c 23, .c 43, .c 3, .c 883, .c 263, .c 3, .c 7, .c 5, .c 3, .c 11,
  .c 29, .c 3, .c 5, .c 7, .c 3, .c 499, .p pv3 [pv2,pv3,pv13,pv26479], .c 3, .c 487,
  .p pv7 [pv2,pv3,pv47,pv1831], .c 3, .c 163, .c 5, .c 3, .p pv2 [pv2,pv7,pv151,pv977], .c 17,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv344231], .c 3, .c 181, .c 11, .c 3, .p pv2 [pv2,pv516349], .c 7,
  .c 3, .c 353, .c 5, .c 3, .c 29,
]
private theorem h0252c03 : checkBlock 2065155 128 b0252c03 = true := by
  decide +kernel

private def b0252c04 : List Row := [
  .p pv2 [pv2,pv3,pv5,pv53,pv433], .c 3, .c 5, .p pv5 [pv2,pv3,pv41,pv2099], .c 3, .c 97, .c 23,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv57373], .c 3, .c 19, .c 5, .c 3, .c 653, .c 7, .c 3, .c 5, .c 173,
  .c 3, .c 37, .c 13, .c 3, .c 41, .c 11, .c 3, .c 53, .c 5, .c 3, .c 7, .c 19, .c 3, .c 5,
  .c 131, .c 3, .c 11, .c 7, .c 3, .c 313, .p pv17 [pv2,pv3,pv37,pv1163], .c 3,
  .p pv2 [pv2,pv11,pv13,pv23,pv157], .c 5, .c 3, .c 31, .p pv2 [pv2,pv3,pv5,pv17], .c 3, .c 5,
  .c 1013, .c 3, .c 7, .c 1019, .c 3, .c 17, .c 383, .c 3, .p pv2 [pv2,pv509,pv2029], .c 5, .c 3,
  .c 151, .c 13, .c 3, .c 5, .c 1367, .c 3, .c 467, .c 67, .c 3, .c 11, .c 137, .c 3, .c 7, .c 5,
  .c 3, .p pv11 [pv2,pv11,pv93889], .c 23, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv13,pv15889],
  .p pv2 [pv2,pv3,pv181,pv317], .c 3, .p pv3 [pv2,pv258197], .p pv2 [pv2,pv3,pv344263], .c 3,
  .c 13, .c 5, .c 3, .c 277, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv13241], .c 3, .c 89, .c 47,
  .c 3, .c 23, .c 7, .c 3, .c 11, .c 5, .c 3, .c 17, .c 41, .c 3, .c 5, .p pv2 [pv2,pv3,pv114757],
  .c 3, .c 281, .p pv7 [pv2,pv3,pv21517], .c 3, .c 7, .p pv3 [pv2,pv3,pv344273], .c 3, .c 61,
  .c 5, .c 3, .c 59, .c 7, .c 3, .c 5, .c 11, .c 3, .c 13, .p pv5 [pv2,pv3,pv41,pv311], .c 3,
]
private theorem h0252c04 : checkBlock 2065411 128 b0252c04 = true := by
  decide +kernel

private def b0252c05 : List Row := [
  .p pv2 [pv2,pv1032833], .p pv2 [pv2,pv3,pv11,pv15649], .c 3, .c 37, .c 5, .c 3, .c 7, .c 73,
  .c 3, .c 5, .c 13, .c 3, .c 347, .c 7, .c 3, .c 47, .c 19, .c 3, .c 41, .c 5, .c 3, .c 443,
  .p pv23 [pv2,pv3,pv5,pv37,pv1861], .c 3, .c 5, .p pv2 [pv2,pv3,pv31,pv617], .c 3, .c 7, .c 11,
  .c 3, .p pv5 [pv2,pv13,pv79451], .p pv11 [pv2,pv3,pv7,pv29,pv53], .c 3, .p pv2 [pv2,pv516433],
  .c 5, .c 3, .c 13, .c 461, .c 3, .c 5, .c 31, .c 3, .p pv7 [pv2,pv5,pv8263], .c 101, .c 3,
  .c 29, .p pv3 [pv2,pv3,pv344293], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv23,pv103,pv109], .c 79,
  .c 3, .c 5, .c 7, .c 3, .c 53, .c 431, .c 3, .c 83, .c 11, .c 3, .c 173, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv147557], .p pv7 [pv2,pv3,pv5,pv11,pv313], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv17,pv43,pv157], .c 3, .c 11, .c 19, .c 3, .c 13, .c 7, .c 3, .c 17, .c 5,
  .c 3, .p pv2 [pv2,pv516457], .c 151, .c 3, .c 5, .c 23, .c 3, .p pv3 [pv2,pv5,pv7,pv17,pv31],
  .c 13, .c 3, .c 7, .c 43, .c 3, .c 757, .c 5, .c 3, .c 409, .c 7, .c 3, .c 5, .c 41, .c 3,
  .c 31, .c 29, .c 3, .c 11, .p pv7 [pv2,pv3,pv67,pv571], .c 3, .c 23, .c 5, .c 3, .c 7, .c 17,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv4099], .c 3, .c 211, .c 7, .c 3, .p pv2 [pv2,pv23,pv97,pv463],
  .c 127, .c 3, .c 557, .c 5, .c 3, .c 1103, .c 11,
]
private theorem h0252c05 : checkBlock 2065667 128 b0252c05 = true := by
  decide +kernel

private def b0252c06 : List Row := [
  .c 3, .c 5, .c 19, .c 3, .c 7, .c 31, .c 3, .p pv3 [pv2,pv129121], .c 197, .c 3, .c 11, .c 5,
  .c 3, .c 41, .c 599, .c 3, .c 5, .c 89, .c 3, .p pv3 [pv2,pv5,pv13,pv29,pv137], .c 157, .c 3,
  .p pv5 [pv2,pv7,pv173,pv853], .c 37, .c 3, .c 7, .c 5, .c 3, .c 47, .c 251, .c 3, .c 5, .c 7,
  .c 3, .p pv7 [pv2,pv5,pv41,pv5039], .c 17, .c 3, .p pv2 [pv2,pv516499], .c 13, .c 3, .c 19,
  .c 5, .c 3, .c 11, .c 233, .c 3, .c 5, .p pv11 [pv2,pv3,pv21521], .c 3, .c 23, .c 257, .c 3,
  .c 17, .c 7, .c 3, .p pv3 [pv2,pv129127], .c 5, .c 3, .c 569, .c 19, .c 3, .c 5, .c 29, .c 3,
  .c 13, .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv114781], .c 3, .c 107, .c 5, .c 3,
  .p pv2 [pv2,pv516517], .c 7, .c 3, .c 5, .c 13, .c 3, .p pv7 [pv2,pv5,pv37,pv349],
  .p pv2 [pv2,pv3,pv344347], .c 3, .c 79, .c 419, .c 3, .c 241, .c 5, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv5,pv71,pv97], .c 3, .c 5, .c 43, .c 3, .p pv13 [pv2,pv5,pv307,pv673], .c 7,
  .c 3, .c 19, .c 11, .c 3, .p pv2 [pv2,pv1033061], .c 5, .c 3, .c 13, .c 61, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv19,pv23,pv197], .c 3, .c 7, .c 277, .c 3, .c 337, .p pv2 [pv2,pv3,pv7,pv911],
  .c 3, .p pv3 [pv2,pv11,pv53,pv443], .c 5, .c 3, .c 23, .p pv7 [pv2,pv3,pv5,pv8609], .c 3, .c 5,
  .c 47, .c 3, .c 71, .p pv2 [pv2,pv3,pv172181], .c 3, .p pv3 [pv2,pv7,pv1153],
]
private theorem h0252c06 : checkBlock 2065923 128 b0252c06 = true := by
  decide +kernel

private def b0252c07 : List Row := [
  .p pv11 [pv2,pv3,pv344363], .c 3, .c 7, .c 5, .c 3, .c 269, .c 37, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv10331], .p pv2 [pv2,pv3,pv83,pv461], .c 3, .c 11, .p pv7 [pv2,pv3,pv21523],
  .c 3, .c 67, .c 5, .c 3, .p pv7 [pv2,pv7,pv11,pv13417], .c 29, .c 3, .c 5, .c 857, .c 3, .c 17,
  .c 13, .c 3, .c 577, .c 7, .c 3, .c 31, .c 5, .c 3, .p pv3 [pv2,pv17,pv15193], .c 11, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv4783], .c 3, .c 47, .c 131, .c 3, .c 7, .c 19, .c 3, .c 11, .c 5, .c 3,
  .c 29, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv521,pv661], .c 3, .c 167, .p pv5 [pv2,pv3,pv57397],
  .c 3, .c 23, .c 17, .c 3, .c 769, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 11, .c 3,
  .p pv3 [pv2,pv5,pv23,pv1123], .c 7, .c 3, .c 733, .p pv13 [pv2,pv3,pv11,pv2609], .c 3, .c 17,
  .c 5, .c 3, .c 11, .c 487, .c 3, .c 5, .c 67, .c 3, .c 7, .c 401, .c 3, .c 59, .c 41, .c 3,
  .c 13, .c 5, .c 3, .c 463, .c 137, .c 3, .c 5, .c 1069, .c 3, .c 227, .c 11, .c 3, .c 1087,
  .c 13, .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv31,pv33329], .c 17, .c 3, .c 5, .c 7, .c 3, .c 73,
  .c 37, .c 3, .c 53, .p pv2 [pv2,pv3,pv17,pv2251], .c 3, .c 613, .c 5, .c 3, .c 31, .c 113, .c 3,
]
private theorem h0252c07 : checkBlock 2066179 128 b0252c07 = true := by
  decide +kernel

private def b0252c08 : List Row := [
  .c 5, .p pv11 [pv2,pv3,pv61,pv941], .c 3, .c 13, .p pv3 [pv2,pv3,pv7,pv49201], .c 3,
  .p pv5 [pv2,pv1033223], .c 7, .c 3, .c 29, .c 5, .c 3, .c 19,
  .p pv79 [pv2,pv3,pv5,pv11,pv31,pv101], .c 3, .c 5, .c 13, .c 3, .c 11, .p pv5 [pv2,pv3,pv1063],
  .c 3, .c 7, .c 967, .c 3, .c 251, .c 5, .c 3, .c 103, .c 7, .c 3, .c 5, .c 19, .c 3,
  .p pv3 [pv2,pv5,pv4133], .c 17, .c 3, .p pv2 [pv2,pv13,pv79481], .p pv2 [pv2,pv3,pv137,pv419],
  .c 3, .c 139, .c 5, .c 3, .c 7, .p pv23 [pv2,pv3,pv5,pv17,pv1013], .c 3, .c 5, .c 23, .c 3,
  .c 109, .c 7, .c 3, .c 11, .p pv2 [pv2,pv3,pv344423], .c 3, .c 47, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv67,pv701], .p pv11 [pv2,pv3,pv5,pv23,pv599], .c 3, .c 5, .c 73, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv114809], .c 3, .c 1187, .c 29, .c 3, .c 19, .c 5, .c 3,
  .p pv2 [pv2,pv1033289], .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv151,pv2281], .c 3, .c 157, .c 59,
  .c 3, .c 13, .p pv3 [pv2,pv3,pv29,pv37,pv107], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv227,pv569],
  .c 19, .c 3, .c 5, .c 7, .c 3, .c 797, .c 13, .c 3, .c 29, .c 53, .c 3, .c 239, .c 5, .c 3,
  .c 17, .p pv7 [pv2,pv3,pv5,pv79,pv109], .c 3, .c 5, .c 11, .c 3, .c 1163,
  .p pv5 [pv2,pv3,pv7,pv59,pv139], .c 3, .c 113, .c 7, .c 3, .c 461, .c 5, .c 3, .c 11, .c 127,
  .c 3, .c 5, .c 31, .c 3, .p pv3 [pv2,pv5,pv7,pv11,pv61], .p pv2 [pv2,pv3,pv53,pv67,pv97], .c 3,
  .c 7, .c 421,
]
private theorem h0252c08 : checkBlock 2066435 128 b0252c08 = true := by
  decide +kernel

private def b0252c09 : List Row := [
  .c 3, .p pv2 [pv2,pv516673], .c 5, .c 3, .p pv2 [pv2,pv1033349], .c 7, .c 3, .c 5, .c 17, .c 3,
  .c 23, .c 11, .c 3, .p pv2 [pv2,pv516679], .c 79, .c 3, .p pv2 [pv2,pv7,pv21089], .c 5, .c 3,
  .c 7, .c 47, .c 3, .c 5, .c 151, .c 3, .c 17, .c 7, .c 3, .c 449, .c 67, .c 3, .c 13, .c 5,
  .c 3, .p pv7 [pv2,pv17,pv89,pv683], .p pv17 [pv2,pv3,pv5,pv5741], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv13,pv26497], .c 3, .c 7, .c 563, .c 3, .p pv3 [pv2,pv73,pv3539], .c 11, .c 3,
  .c 37, .c 5, .c 3, .p pv2 [pv2,pv53,pv9749], .c 139, .c 3, .c 5, .p pv7 [pv2,pv3,pv6379], .c 3,
  .c 11, .c 23, .c 3, .c 521, .c 17, .c 3, .c 7, .c 5, .c 3, .c 853, .c 337, .c 3, .c 5, .c 7,
  .c 3, .c 13, .p pv7 [pv2,pv3,pv31,pv463], .c 3, .c 193, .c 19, .c 3, .c 17, .c 5, .c 3, .c 23,
  .c 41, .c 3, .c 5, .c 13, .c 3, .c 727, .c 31, .c 3, .c 11, .c 7, .c 3, .c 1319, .c 5, .c 3,
  .p pv11 [pv2,pv11,pv93949], .c 43, .c 3, .c 5, .p pv3 [pv2,pv3,pv114827], .c 3, .c 1291,
  .p pv2 [pv2,pv3,pv41,pv4201], .c 3, .c 7, .p pv3 [pv2,pv3,pv344483], .c 3,
  .p pv5 [pv2,pv1033451], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 29, .c 3, .c 1201,
  .p pv11 [pv2,pv3,pv11,pv13,pv73], .c 3, .c 419, .p pv11 [pv2,pv3,pv17,pv149], .c 3, .c 11, .c 5,
  .c 3, .c 7, .c 23, .c 3, .c 5,
]
private theorem h0252c09 : checkBlock 2066691 128 b0252c09 = true := by
  decide +kernel

private def b0252c10 : List Row := [
  .c 53, .c 3, .p pv17 [pv2,pv5,pv67,pv617], .c 7, .c 3, .p pv2 [pv2,pv31,pv79,pv211], .c 167,
  .c 3, .p pv2 [pv2,pv17,pv60793], .c 5, .c 3, .p pv3 [pv2,pv37,pv6983],
  .p pv7 [pv2,pv3,pv5,pv68899], .c 3, .c 5, .c 11, .c 3, .c 7, .c 739, .c 3, .c 13,
  .p pv29 [pv2,pv3,pv7,pv11,pv2237], .c 3, .p pv3 [pv2,pv129187], .c 5, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv5,pv13,pv53], .c 3, .c 5, .p pv3 [pv2,pv3,pv59,pv5839], .c 3, .c 457, .c 13,
  .c 3, .c 67, .p pv2 [pv2,pv3,pv31,pv11113], .c 3, .c 7, .c 5, .c 3, .c 19, .c 307, .c 3, .c 5,
  .c 7, .c 3, .p pv3 [pv2,pv5,pv12919], .c 11, .c 3, .c 17, .c 31, .c 3, .c 43, .c 5, .c 3,
  .c 911, .p pv2 [pv2,pv3,pv5,pv47,pv733], .c 3, .c 5, .c 19, .c 3, .p pv13 [pv2,pv5,pv97,pv2131],
  .p pv5 [pv2,pv3,pv7,pv769], .c 3, .c 149, .c 7, .c 3, .p pv2 [pv2,pv1033541], .c 5, .c 3,
  .c 877, .c 13, .c 3, .c 5, .c 41, .c 3, .p pv2 [pv2,pv5,pv7,pv2953], .c 883, .c 3, .c 7, .c 11,
  .c 3, .c 547, .c 5, .c 3, .p pv13 [pv2,pv1033559], .c 7, .c 3, .c 5, .c 349, .c 3, .c 11,
  .c 107, .c 3, .p pv3 [pv2,pv32299], .c 43, .c 3, .c 13, .c 5, .c 3, .c 7, .c 67, .c 3, .c 5,
  .c 317, .c 3, .c 541, .c 7, .c 3, .c 97, .c 13, .c 3, .c 31, .c 5, .c 3, .c 41, .c 19, .c 3,
  .c 5, .p pv13 [pv2,pv3,pv11,pv31321], .c 3, .c 7, .c 79, .c 3, .c 11, .c 1129, .c 3,
]
private theorem h0252c10 : checkBlock 2066947 128 b0252c10 = true := by
  decide +kernel

private def b0252c11 : List Row := [
  .c 89, .c 5, .c 3, .p pv3 [pv2,pv11,pv13,pv139], .p pv2 [pv2,pv3,pv5,pv103,pv223], .c 3, .c 5,
  .c 17, .c 3, .c 13, .c 193, .c 3, .c 37, .c 61, .c 3, .c 7, .c 5, .c 3, .c 811, .c 11, .c 3,
  .c 5, .c 7, .c 3, .c 17, .p pv2 [pv2,pv3,pv11,pv15661], .c 3, .c 19, .c 971, .c 3, .c 11, .c 5,
  .c 3, .p pv2 [pv2,pv7,pv17,pv43,pv101], .c 179, .c 3, .c 5, .p pv31 [pv2,pv3,pv19,pv9067], .c 3,
  .c 83, .c 659, .c 3, .c 73, .c 7, .c 3, .c 167, .c 5, .c 3, .c 13, .c 37, .c 3, .c 5, .c 11,
  .c 3, .c 43, .c 103, .c 3, .c 7, .c 17, .c 3, .c 29, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv17,pv563], .c 3, .c 151, .c 41, .c 3, .c 107, .p pv2 [pv2,pv3,pv172279], .c 3,
  .c 17, .c 5, .c 3, .c 7, .c 97, .c 3, .c 5, .c 757, .c 3, .c 19, .c 7, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv23,pv71,pv211], .c 3, .p pv5 [pv2,pv181,pv5711], .c 5, .c 3, .c 47, .c 577,
  .c 3, .c 5, .c 43, .c 3, .c 7, .c 13, .c 3, .p pv5 [pv2,pv11,pv8543], .c 19, .c 3,
  .p pv2 [pv2,pv37,pv61,pv229], .c 5, .c 3, .c 59, .c 17, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv331,pv347], .c 3, .p pv7 [pv2,pv5,pv79,pv2617], .c 73, .c 3,
  .p pv2 [pv2,pv7,pv47,pv1571], .c 11, .c 3, .c 7, .c 5, .c 3, .c 37,
  .p pv7 [pv2,pv3,pv5,pv7,pv11,pv179], .c 3, .c 5, .c 7,
]
private theorem h0252c11 : checkBlock 2067203 128 b0252c11 = true := by
  decide +kernel

private def b0252c12 : List Row := [
  .c 3, .c 11, .c 1277, .c 3, .c 137, .c 1193, .c 3, .c 61, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv59,pv2503], .c 13, .c 3, .c 5, .c 251, .c 3, .p pv2 [pv2,pv5,pv206749], .c 23,
  .c 3, .c 29, .c 7, .c 3, .c 751, .c 5, .c 3, .c 79, .p pv3 [pv2,pv3,pv5,pv68917], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv23,pv227], .c 3, .c 353, .c 17, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv277,pv311], .c 3, .c 13, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv13,pv2039], .c 3, .c 1019, .c 67, .c 3, .c 17, .c 13, .c 3, .c 181, .c 5,
  .c 3, .c 7, .c 11, .c 3, .c 5, .c 47, .c 3, .p pv2 [pv2,pv5,pv19,pv5441], .c 7, .c 3,
  .p pv2 [pv2,pv1033793], .c 41, .c 3, .c 11, .c 5, .c 3, .c 19, .c 491, .c 3, .c 5, .c 31, .c 3,
  .c 7, .c 29, .c 3, .p pv3 [pv2,pv64613], .c 1423, .c 3, .p pv5 [pv2,pv103,pv10037], .c 5, .c 3,
  .c 179, .c 23, .c 3, .c 5, .c 11, .c 3, .c 229, .c 151, .c 3, .p pv5 [pv2,pv7,pv147689], .c 613,
  .c 3, .c 7, .c 5, .c 3, .c 11, .p pv13 [pv2,pv3,pv5,pv7,pv547], .c 3, .c 5, .c 7, .c 3, .c 29,
  .c 149, .c 3, .c 23, .p pv3 [pv2,pv3,pv313,pv367], .c 3, .c 1217, .c 5, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv5,pv157,pv439], .c 3, .c 5, .p pv5 [pv2,pv3,pv83,pv173], .c 3, .c 293, .c 11,
  .c 3, .c 881, .c 7, .c 3, .c 19,
]
private theorem h0252c12 : checkBlock 2067459 128 b0252c12 = true := by
  decide +kernel

private def b0252c13 : List Row := [
  .c 5, .c 3, .p pv11 [pv2,pv47,pv21997], .p pv7 [pv2,pv3,pv5,pv17231], .c 3, .c 5, .c 17, .c 3,
  .c 31, .c 71, .c 3, .c 7, .p pv2 [pv2,pv3,pv251,pv1373], .c 3, .c 227, .c 5, .c 3, .c 97, .c 7,
  .c 3, .c 5, .c 331, .c 3, .c 17, .c 1429, .c 3, .c 13, .c 11, .c 3, .c 59, .c 5, .c 3, .c 7,
  .p pv17 [pv2,pv3,pv5,pv11,pv13,pv241], .c 3, .c 5, .c 29, .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv516949], .p pv3 [pv2,pv3,pv73,pv4721], .c 3, .c 269, .c 5, .c 3, .c 199,
  .p pv2 [pv2,pv3,pv5,pv68927], .c 3, .c 5, .c 383, .c 3, .c 7, .p pv3 [pv2,pv3,pv149,pv257],
  .c 3, .c 19, .c 17, .c 3, .c 503, .c 5, .c 3, .c 61, .c 769, .c 3, .c 5, .c 157, .c 3,
  .p pv2 [pv2,pv5,pv41357], .p pv2 [pv2,pv3,pv172321], .c 3, .c 11, .c 47, .c 3, .c 7, .c 5, .c 3,
  .c 173, .c 13, .c 3, .c 5, .c 7, .c 3, .c 283, .p pv2 [pv2,pv3,pv107,pv3221], .c 3,
  .p pv5 [pv2,pv31,pv33353], .c 1061, .c 3, .c 37, .c 5, .c 3, .c 563, .c 11, .c 3, .c 5, .c 23,
  .c 3, .p pv17 [pv2,pv5,pv13,pv15907], .c 43, .c 3, .c 31, .c 7, .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv258491], .c 17, .c 3, .c 5, .p pv17 [pv2,pv3,pv13,pv1657], .c 3, .c 19, .c 97,
  .c 3, .c 7, .c 13, .c 3, .c 23, .c 5, .c 3, .c 937, .c 7, .c 3, .c 5, .c 11, .c 3,
]
private theorem h0252c13 : checkBlock 2067715 128 b0252c13 = true := by
  decide +kernel

private def b0252c14 : List Row := [
  .c 149, .c 397, .c 3, .p pv3 [pv2,pv23,pv11239], .c 19, .c 3, .c 79, .c 5, .c 3, .c 7, .c 313,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv3517], .c 3, .c 13, .c 7, .c 3, .c 53, .c 59, .c 3, .c 113,
  .c 5, .c 3, .c 29, .c 241, .c 3, .c 5, .c 13, .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv19,pv27211], .p pv3 [pv2,pv3,pv7,pv5471], .c 3, .p pv2 [pv2,pv43,pv139,pv173],
  .c 5, .c 3, .c 607, .c 653, .c 3, .c 5, .c 109, .c 3, .p pv2 [pv2,pv5,pv53,pv1951],
  .p pv3 [pv2,pv3,pv79,pv4363], .c 3, .c 17, .p pv2 [pv2,pv3,pv23,pv59,pv127], .c 3, .c 7, .c 5,
  .c 3, .c 13, .c 41, .c 3, .c 5, .c 7, .c 3, .c 23, .c 19, .c 3, .c 131, .c 11, .c 3, .c 31,
  .c 5, .c 3, .p pv2 [pv2,pv7,pv233,pv317], .c 83, .c 3, .c 5, .p pv2 [pv2,pv3,pv172343], .c 3,
  .c 11, .p pv5 [pv2,pv3,pv7,pv41,pv1201], .c 3, .c 59, .c 7, .c 3, .p pv2 [pv2,pv11,pv4273],
  .c 5, .c 3, .p pv2 [pv2,pv1034069], .c 47, .c 3, .c 5, .p pv2 [pv2,pv3,pv38299], .c 3,
  .p pv19 [pv2,pv5,pv7,pv19,pv311], .c 709, .c 3, .c 7, .c 71, .c 3, .c 41, .c 5, .c 3, .c 17,
  .c 7, .c 3, .c 5, .c 101, .c 3, .c 139, .c 13, .c 3, .c 11, .c 37, .c 3, .c 29, .c 5, .c 3,
  .c 7, .p pv19 [pv2,pv3,pv5,pv383], .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv206821], .c 7,
  .c 3, .c 991, .c 53, .c 3, .c 67, .c 5,
]
private theorem h0252c14 : checkBlock 2067971 128 b0252c14 = true := by
  decide +kernel

private def b0252c15 : List Row := [
  .c 3, .c 23, .c 11, .c 3, .c 5, .c 17, .c 3, .c 7, .c 541, .c 3, .c 151,
  .p pv11 [pv2,pv3,pv7,pv13,pv947], .c 3, .c 11, .c 5, .c 3, .c 307, .c 13, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv61,pv5651], .c 3, .c 17, .p pv31 [pv2,pv3,pv53,pv271], .c 3, .c 83,
  .p pv3 [pv2,pv3,pv101,pv3413], .c 3, .c 7, .c 5, .c 3, .c 31, .p pv3 [pv2,pv3,pv5,pv7,pv67],
  .c 3, .c 5, .c 7, .c 3, .c 71, .c 197, .c 3, .c 163, .c 29, .c 3, .c 13, .c 5, .c 3, .c 11,
  .c 19, .c 3, .c 5, .c 41, .c 3, .c 97, .p pv19 [pv2,pv3,pv7,pv24623], .c 3, .c 37, .c 7, .c 3,
  .c 43, .c 5, .c 3, .p pv2 [pv2,pv517087], .c 31, .c 3, .c 5, .c 67, .c 3,
  .p pv3 [pv2,pv5,pv7,pv83,pv89], .c 11, .c 3, .c 7, .c 431, .c 3, .c 17, .c 5, .c 3, .c 101,
  .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv43,pv8017], .c 3, .c 13, .p pv7 [pv2,pv3,pv86183], .c 3,
  .c 19, .p pv3 [pv2,pv3,pv151,pv761], .c 3, .p pv2 [pv2,pv7,pv147743], .c 5, .c 3, .c 7, .c 37,
  .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv103421], .c 7, .c 3, .p pv2 [pv2,pv137,pv7549],
  .c 11, .c 3, .c 211, .c 5, .c 3, .p pv7 [pv2,pv1034219], .c 17, .c 3, .c 5, .c 283, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv57457], .c 3, .c 79, .c 23, .c 3, .p pv5 [pv2,pv11,pv167,pv563], .c 5, .c 3,
  .c 13, .p pv3 [pv2,pv3,pv5,pv47,pv163], .c 3, .c 5, .p pv5 [pv2,pv3,pv172373], .c 3, .c 59,
]
private theorem h0252c15 : checkBlock 2068227 128 b0252c15 = true := by
  decide +kernel

private def b0252c16 : List Row := [
  .c 29, .c 3, .p pv5 [pv2,pv7,pv21107], .p pv7 [pv2,pv3,pv28729], .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv1034249], .p pv2 [pv2,pv3,pv5,pv7,pv197], .c 3, .c 5, .c 7, .c 3, .c 19,
  .p pv5 [pv2,pv3,pv29,pv743], .c 3, .c 11, .p pv3 [pv2,pv3,pv344753], .c 3, .c 349, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv11,pv23,pv73], .c 643, .c 3, .c 5, .c 31, .c 3, .c 29, .c 17, .c 3, .c 13,
  .c 7, .c 3, .p pv3 [pv2,pv258569], .c 5, .c 3, .c 37, .c 11, .c 3, .c 5, .c 149, .c 3, .c 61,
  .c 13, .c 3, .c 7, .p pv2 [pv2,pv3,pv113], .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv587,pv881],
  .c 7, .c 3, .c 5, .c 23, .c 3, .c 43, .c 419, .c 3, .p pv5 [pv2,pv19,pv54437], .c 83, .c 3,
  .c 809, .c 5, .c 3, .c 7, .c 131, .c 3, .c 5, .c 11, .c 3, .c 107, .c 7, .c 3,
  .p pv2 [pv2,pv277,pv1867], .p pv3 [pv2,pv3,pv11,pv13,pv2411], .c 3, .c 23, .c 5, .c 3, .c 11,
  .c 13, .c 3, .c 5, .c 29, .c 3, .c 7, .c 19, .c 3, .p pv2 [pv2,pv23,pv44971], .c 919, .c 3,
  .p pv3 [pv2,pv32323], .c 5, .c 3, .c 17, .p pv7 [pv2,pv3,pv5,pv17239], .c 3, .c 5, .c 43, .c 3,
  .c 113, .c 11, .c 3, .c 197, .p pv2 [pv2,pv3,pv557,pv619], .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv517177], .c 109, .c 3, .c 5, .c 7, .c 3, .c 191, .c 31, .c 3, .c 71, .c 13, .c 3,
  .c 571, .c 5, .c 3,
]
private theorem h0252c16 : checkBlock 2068483 128 b0252c16 = true := by
  decide +kernel

private def b0252c17 : List Row := [
  .c 19, .p pv17 [pv2,pv3,pv5,pv1277], .c 3, .c 5, .c 17, .c 3, .p pv11 [pv2,pv5,pv331],
  .p pv5 [pv2,pv3,pv7,pv47,pv131], .c 3, .p pv2 [pv2,pv517189], .c 7, .c 3,
  .p pv2 [pv2,pv1034381], .c 5, .c 3, .p pv3 [pv2,pv13,pv4973], .c 223, .c 3, .c 5, .c 19, .c 3,
  .c 11, .c 101, .c 3, .c 7, .c 157, .c 3, .c 1327, .c 5, .c 3, .c 47, .c 7, .c 3, .c 5, .c 13,
  .c 3, .p pv43 [pv2,pv5,pv443,pv467], .p pv5 [pv2,pv3,pv57467], .c 3,
  .p pv3 [pv2,pv31,pv43,pv97], .c 41, .c 3, .p pv5 [pv2,pv7,pv147773], .c 5, .c 3, .c 7, .c 29,
  .c 3, .c 5, .c 137, .c 3, .p pv3 [pv2,pv5,pv51721], .c 7, .c 3, .c 11, .c 17, .c 3, .c 19, .c 5,
  .c 3, .c 13, .c 811, .c 3, .c 5, .c 907, .c 3, .c 7, .c 23, .c 3, .p pv2 [pv2,pv61,pv139],
  .c 269, .c 3, .c 17, .c 5, .c 3, .c 29, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv23,pv937], .c 3,
  .c 41, .p pv5 [pv2,pv3,pv11,pv43], .c 3, .c 173, .c 31, .c 3, .c 7, .c 5, .c 3, .c 23,
  .p pv29 [pv2,pv3,pv5,pv7,pv821], .c 3, .c 5, .c 7, .c 3, .c 79, .c 353, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv114941], .c 3, .p pv5 [pv2,pv23,pv41,pv1097], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv19,pv3889], .c 17, .c 3, .c 5, .c 11, .c 3, .c 53, .c 13, .c 3, .c 19, .c 7,
  .c 3, .p pv2 [pv2,pv517243], .c 5, .c 3, .c 11, .c 1307, .c 3, .c 5, .c 47, .c 3,
  .p pv7 [pv2,pv5,pv7,pv11,pv2687], .c 251,
]
private theorem h0252c17 : checkBlock 2068739 128 b0252c17 = true := by
  decide +kernel

private def b0252c18 : List Row := [
  .c 3, .c 7, .p pv3 [pv2,pv3,pv61,pv5653], .c 3, .c 37, .c 5, .c 3, .p pv3 [pv2,pv129313], .c 7,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv86209], .c 3, .c 263, .c 11, .c 3, .c 67,
  .p pv2 [pv2,pv3,pv13,pv4421], .c 3, .c 31, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv16421], .c 3, .p pv31 [pv2,pv5,pv41381], .c 7, .c 3, .c 23, .c 61, .c 3,
  .c 29, .c 5, .c 3, .p pv2 [pv2,pv517267], .c 59, .c 3, .c 5, .c 37, .c 3, .c 7, .c 311, .c 3,
  .c 17, .c 11, .c 3, .c 13, .c 5, .c 3, .c 1033, .p pv2 [pv2,pv3,pv5,pv11,pv19], .c 3, .c 5,
  .c 83, .c 3, .c 11, .p pv13 [pv2,pv3,pv73,pv1181], .c 3, .c 43, .c 13, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv47,pv5503], .c 409, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv103457], .c 113,
  .c 3, .c 41, .c 23, .c 3, .c 71, .c 5, .c 3, .c 761, .c 67, .c 3, .c 5, .c 103, .c 3, .c 13,
  .c 53, .c 3, .c 11, .c 7, .c 3, .p pv5 [pv2,pv1034591], .c 5, .c 3, .c 17,
  .p pv11 [pv2,pv3,pv5,pv83,pv277], .c 3, .c 5, .c 13, .c 3, .c 971, .c 43, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv29,pv991], .c 3, .p pv2 [pv2,pv517303], .c 5, .c 3, .c 31, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv53,pv241], .c 3, .c 431, .c 19, .c 3, .c 29, .p pv7 [pv2,pv3,pv344873], .c 3,
  .c 11, .c 5, .c 3, .c 7,
]
private theorem h0252c18 : checkBlock 2068995 128 b0252c18 = true := by
  decide +kernel

private def b0252c19 : List Row := [
  .p pv3 [pv2,pv3,pv5,pv31,pv89], .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv157,pv659], .c 7,
  .c 3, .p pv2 [pv2,pv29,pv35677], .c 47, .c 3, .c 83, .c 5, .c 3, .c 53, .c 31, .c 3, .c 5,
  .c 11, .c 3, .c 7, .c 139, .c 3, .c 167, .c 37, .c 3, .c 61, .c 5, .c 3, .c 11, .c 41, .c 3,
  .c 5, .c 619, .c 3, .c 773, .c 1201, .c 3, .c 13, .p pv7 [pv2,pv3,pv19,pv2269], .c 3, .c 7,
  .c 5, .c 3, .c 89, .p pv2 [pv2,pv3,pv5,pv7,pv13,pv379], .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv41387], .c 11, .c 3, .c 653, .c 17, .c 3, .c 47, .c 5, .c 3, .c 113, .c 887,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv317], .c 3, .p pv2 [pv2,pv5,pv107,pv967],
  .p pv59 [pv2,pv3,pv7,pv29,pv1699], .c 3, .p pv2 [pv2,pv11,pv94063], .c 7, .c 3, .c 17, .c 5,
  .c 3, .p pv13 [pv2,pv97,pv10667], .c 199, .c 3, .c 5, .c 131, .c 3, .c 29,
  .p pv2 [pv2,pv3,pv331,pv521], .c 3, .c 7, .c 11, .c 3, .c 19, .c 5, .c 3, .c 67, .c 7, .c 3,
  .c 5, .c 71, .c 3, .c 11, .p pv3 [pv2,pv3,pv19,pv2017], .c 3, .c 37,
  .p pv11 [pv2,pv3,pv23,pv163], .c 3, .c 569, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 31, .c 3,
  .c 23, .c 7, .c 3, .c 73, .c 1283, .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv211,pv613], .c 53,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv13,pv67], .c 3, .c 7, .p pv3 [pv2,pv3,pv344917], .c 3,
]
private theorem h0252c19 : checkBlock 2069251 128 b0252c19 = true := by
  decide +kernel

private def b0252c20 : List Row := [
  .c 11, .c 13, .c 3, .c 367, .c 5, .c 3, .p pv7 [pv2,pv11,pv19,pv4951], .c 37, .c 3, .c 5, .c 29,
  .c 3, .p pv2 [pv2,pv5,pv206953], .p pv2 [pv2,pv3,pv57487], .c 3, .c 19, .c 193, .c 3, .c 7,
  .c 5, .c 3, .p pv2 [pv2,pv13,pv39799], .c 11, .c 3, .c 5, .c 7, .c 3, .c 13, .c 17, .c 3,
  .c 1021, .p pv7 [pv2,pv3,pv3593], .c 3, .c 11, .c 5, .c 3, .c 71,
  .p pv2 [pv2,pv3,pv5,pv17,pv2029], .c 3, .c 5, .c 13, .c 3, .c 31, .c 1249, .c 3, .c 17, .c 7,
  .c 3, .p pv2 [pv2,pv59,pv17539], .c 5, .c 3, .c 23, .c 163, .c 3, .c 5, .c 11, .c 3, .c 257,
  .c 73, .c 3, .c 7, .p pv2 [pv2,pv3,pv11,pv15679], .c 3, .c 43, .c 5, .c 3, .c 11, .c 7, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv344941], .c 3, .c 19, .c 31, .c 3, .p pv3 [pv2,pv258707], .c 137, .c 3,
  .c 223, .c 5, .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv19,pv3631], .c 3, .c 5, .c 1049, .c 3,
  .p pv3 [pv2,pv5,pv41,pv631], .c 7, .c 3, .p pv5 [pv2,pv269,pv3847], .c 19, .c 3, .c 317, .c 5,
  .c 3, .c 17, .c 23, .c 3, .c 5, .p pv2 [pv2,pv3,pv37,pv9323], .c 3, .c 7,
  .p pv5 [pv2,pv3,pv1597], .c 3, .c 13, .c 43, .c 3, .p pv2 [pv2,pv1034861], .c 5, .c 3,
  .p pv3 [pv2,pv64679], .c 157, .c 3, .c 5, .p pv7 [pv2,pv3,pv86239], .c 3, .c 821, .c 13, .c 3,
  .c 23, .c 11, .c 3, .c 7, .c 5, .c 3, .c 29, .p pv19 [pv2,pv3,pv5,pv7,pv11],
]
private theorem h0252c20 : checkBlock 2069507 128 b0252c20 = true := by
  decide +kernel

private def b0252c21 : List Row := [
  .c 3, .c 5, .c 7, .c 3, .c 11, .p pv5 [pv2,pv3,pv173,pv997], .c 3, .c 31, .c 59, .c 3,
  .p pv5 [pv2,pv11,pv13,pv7237], .c 5, .c 3, .c 641, .c 61, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv137,pv1259], .c 3, .c 17, .c 19, .c 3, .p pv5 [pv2,pv1034903], .c 7, .c 3,
  .c 839, .c 5, .c 3, .p pv2 [pv2,pv17,pv3581], .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv2851],
  .c 3, .c 67, .c 47, .c 3, .c 7, .c 23, .c 3, .p pv2 [pv2,pv73,pv14177], .c 5, .c 3, .c 139,
  .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv7187], .c 3, .p pv2 [pv2,pv5,pv13,pv19,pv419], .c 71, .c 3,
  .c 191, .c 17, .c 3, .c 13, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv7,pv13,pv17,pv223], .c 3, .c 37, .c 7, .c 3, .c 59, .c 13, .c 3, .c 11, .c 5,
  .c 3, .p pv2 [pv2,pv23,pv149,pv151], .p pv3 [pv2,pv3,pv5,pv109,pv211], .c 3, .c 5, .c 19, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv344987], .c 3, .c 47, .p pv23 [pv2,pv3,pv7,pv37], .c 3, .c 29, .c 5,
  .c 3, .c 739, .p pv2 [pv2,pv3,pv5,pv34499], .c 3, .c 5, .c 11, .c 3, .c 13,
  .p pv5 [pv2,pv3,pv10781], .c 3, .p pv2 [pv2,pv7,pv59,pv179], .p pv3 [pv2,pv3,pv11,pv79,pv397],
  .c 3, .c 7, .c 5, .c 3, .c 11, .c 17, .c 3, .c 5, .c 7, .c 3, .c 827, .p pv3 [pv2,pv3,pv38333],
  .c 3, .p pv2 [pv2,pv1034993], .p pv2 [pv2,pv3,pv17,pv73,pv139], .c 3, .c 19, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv199,pv743], .c 719, .c 3, .c 5, .c 1321, .c 3, .c 1061, .c 11, .c 3, .c 1277,
]
private theorem h0252c21 : checkBlock 2069763 128 b0252c21 = true := by
  decide +kernel

private def b0252c22 : List Row := [
  .c 7, .c 3, .c 23, .c 5, .c 3, .c 13, .c 19, .c 3, .c 5, .c 79, .c 3,
  .p pv3 [pv2,pv5,pv7,pv7393], .p pv2 [pv2,pv3,pv13,pv26539], .c 3, .c 7, .c 29, .c 3, .c 701,
  .c 5, .c 3, .c 151, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv345011], .c 3,
  .p pv23 [pv2,pv5,pv137,pv1511], .c 17, .c 3, .c 97, .c 11, .c 3, .p pv2 [pv2,pv7,pv147863],
  .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv11,pv17,pv41], .c 3, .c 5, .c 181, .c 3, .c 11, .c 7,
  .c 3, .c 13, .c 223, .c 3, .c 37, .c 5, .c 3, .c 1381, .c 211, .c 3, .c 5, .c 53, .c 3, .c 7,
  .c 13, .c 3, .p pv3 [pv2,pv29,pv8923], .c 443, .c 3, .p pv5 [pv2,pv947,pv1093], .c 5, .c 3,
  .c 31, .c 563, .c 3, .c 5, .c 61, .c 3, .c 23, .c 593, .c 3, .c 11, .c 271, .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv11,pv94099], .p pv2 [pv2,pv3,pv5,pv7,pv31,pv53], .c 3, .c 5, .c 7, .c 3,
  .c 337, .c 131, .c 3, .c 101, .c 991, .c 3, .p pv2 [pv2,pv19,pv157,pv347], .c 5, .c 3, .c 17,
  .c 11, .c 3, .c 5, .p pv13 [pv2,pv3,pv28753], .c 3, .c 19, .c 29, .c 3, .c 127, .c 7, .c 3,
  .c 11, .c 5, .c 3, .p pv13 [pv2,pv479,pv2161], .p pv31 [pv2,pv3,pv5,pv19,pv227], .c 3, .c 5,
  .c 367, .c 3, .c 59, .c 23, .c 3, .c 7, .c 19, .c 3, .c 13, .c 5, .c 3, .c 83, .c 7, .c 3,
]
private theorem h0252c22 : checkBlock 2070019 128 b0252c22 = true := by
  decide +kernel

private def b0252c23 : List Row := [
  .c 5, .c 11, .c 3, .c 29, .p pv2 [pv2,pv3,pv345047], .c 3, .p pv5 [pv2,pv53,pv19531], .c 13,
  .c 3, .c 1181, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv67,pv103], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv5477], .c 3, .c 17, .c 7, .c 3, .p pv2 [pv2,pv19,pv27241],
  .p pv11 [pv2,pv3,pv89,pv3877], .c 3, .p pv2 [pv2,pv23,pv45007], .c 5, .c 3,
  .p pv3 [pv2,pv13,pv17,pv1171], .c 1103, .c 3, .c 5, .c 863, .c 3, .c 7, .c 11, .c 3, .c 967,
  .c 587, .c 3, .c 73, .c 5, .c 3, .c 157, .c 151, .c 3, .c 5, .c 13, .c 3,
  .p pv2 [pv2,pv5,pv207037], .c 19, .c 3, .c 41, .c 17, .c 3, .c 7, .c 5, .c 3, .c 229, .c 23,
  .c 3, .c 5, .c 7, .c 3, .c 61, .c 103, .c 3, .c 43, .c 11, .c 3, .c 17, .c 5, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv5,pv11,pv3137], .c 3, .c 5, .p pv3 [pv2,pv3,pv29,pv73,pv163], .c 3, .c 11,
  .p pv41 [pv2,pv3,pv7,pv13,pv79], .c 3, .c 23, .c 7, .c 3, .p pv2 [pv2,pv11,pv94111], .c 5, .c 3,
  .c 19, .p pv2 [pv2,pv3,pv5,pv43,pv107], .c 3, .c 5, .c 239, .c 3,
  .p pv11 [pv2,pv5,pv7,pv23,pv643], .p pv3 [pv2,pv3,pv61,pv5657], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv19,pv1009], .c 3, .p pv3 [pv2,pv258809], .c 5, .c 3,
  .p pv11 [pv2,pv421,pv2459], .c 7, .c 3, .c 5, .c 19, .c 3, .c 47, .c 43, .c 3, .c 11, .c 73,
  .c 3, .c 1109, .c 5, .c 3, .c 7, .c 79, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv157], .c 3, .c 31,
  .c 7, .c 3, .p pv5 [pv2,pv1035263], .c 23,
]
private theorem h0252c23 : checkBlock 2070275 128 b0252c23 = true := by
  decide +kernel

private def b0252c24 : List Row := [
  .c 3, .p pv2 [pv2,pv17,pv30449], .c 5, .c 3, .c 1223, .c 11, .c 3, .c 5, .c 491, .c 3, .c 7,
  .p pv29 [pv2,pv3,pv11,pv23,pv31], .c 3, .c 37, .p pv3 [pv2,pv3,pv7,pv16433], .c 3, .c 11, .c 5,
  .c 3, .p pv11 [pv2,pv67,pv3863], .c 29, .c 3, .c 5, .c 1427, .c 3, .p pv2 [pv2,pv5,pv103529],
  .c 17, .c 3, .p pv5 [pv2,pv7,pv131,pv1129], .c 163, .c 3, .c 7, .c 5, .c 3, .c 263, .c 13, .c 3,
  .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv207061], .p pv2 [pv2,pv3,pv113,pv509], .c 3, .c 17,
  .p pv3 [pv2,pv3,pv11,pv137,pv229], .c 3, .c 41, .c 5, .c 3, .c 11, .c 37, .c 3, .c 5, .c 173,
  .c 3, .p pv3 [pv2,pv5,pv11,pv13,pv181], .p pv2 [pv2,pv3,pv7,pv7043], .c 3, .c 389, .c 7, .c 3,
  .c 13, .c 5, .c 3, .c 97, .p pv11 [pv2,pv3,pv5,pv34511], .c 3, .c 5, .c 23, .c 3, .c 233, .c 11,
  .c 3, .c 7, .c 13, .c 3, .c 139, .c 5, .c 3, .c 281, .c 7, .c 3, .c 5, .c 193, .c 3, .c 1279,
  .c 911, .c 3, .c 31, .p pv2 [pv2,pv3,pv43,pv4013], .c 3, .c 23, .c 5, .c 3, .c 7, .c 1439, .c 3,
  .c 5, .c 1039, .c 3, .c 13, .c 7, .c 3, .p pv3 [pv2,pv17,pv23,pv331], .c 11, .c 3, .c 599, .c 5,
  .c 3, .p pv2 [pv2,pv79,pv6553], .c 43, .c 3, .c 5, .c 13, .c 3, .c 7, .c 53, .c 3, .c 61, .c 31,
  .c 3, .c 47, .c 5, .c 3, .c 37, .p pv2 [pv2,pv3,pv5,pv34513], .c 3, .c 5,
]
private theorem h0252c24 : checkBlock 2070531 128 b0252c24 = true := by
  decide +kernel

private def b0252c25 : List Row := [
  .c 17, .c 3, .c 19, .p pv5 [pv2,pv3,pv9587], .c 3, .p pv2 [pv2,pv7,pv13,pv5689],
  .p pv3 [pv2,pv3,pv345133], .c 3, .c 7, .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv7,pv19,pv173],
  .c 3, .c 5, .c 7, .c 3, .c 17, .p pv3 [pv2,pv3,pv13,pv139,pv191], .c 3, .c 11, .c 19, .c 3,
  .p pv3 [pv2,pv29,pv4463], .c 5, .c 3, .p pv11 [pv2,pv7,pv11,pv17,pv113], .c 59, .c 3, .c 5,
  .c 229, .c 3, .c 23, .c 37, .c 3, .c 71, .c 7, .c 3, .p pv5 [pv2,pv31,pv127,pv263], .c 5, .c 3,
  .c 41, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv172573], .c 3, .c 383,
  .p pv2 [pv2,pv3,pv11,pv10459], .c 3, .c 7, .c 17, .c 3, .c 11, .c 5, .c 3, .c 421, .c 7, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv17,pv79,pv257], .c 3, .p pv13 [pv2,pv5,pv41,pv5051], .c 13, .c 3,
  .c 769, .c 29, .c 3, .c 17, .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv69031], .c 3, .c 5, .c 11,
  .c 3, .c 89, .c 7, .c 3, .p pv2 [pv2,pv1035473], .c 311, .c 3, .p pv3 [pv2,pv13,pv19913], .c 5,
  .c 3, .c 11, .c 47, .c 3, .c 5, .c 167, .c 3, .c 7, .p pv2 [pv2,pv3,pv57527], .c 3, .c 29,
  .c 131, .c 3, .c 173, .c 5, .c 3, .c 23, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv172583], .c 3,
  .c 37, .c 11, .c 3, .p pv7 [pv2,pv7,pv29,pv5101], .c 43, .c 3, .c 7, .c 5, .c 3, .c 19, .c 103,
  .c 3, .c 5, .c 7, .c 3, .c 269, .c 41, .c 3, .c 67, .c 433, .c 3,
]
private theorem h0252c25 : checkBlock 2070787 128 b0252c25 = true := by
  decide +kernel

private def b0252c26 : List Row := [
  .c 13, .c 5, .c 3, .c 859, .c 353, .c 3, .c 5, .c 19, .c 3, .c 197, .p pv3 [pv2,pv3,pv7,pv5479],
  .c 3, .c 331, .c 7, .c 3, .p pv3 [pv2,pv61,pv1061], .c 5, .c 3, .c 31, .c 23, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv345181], .c 3, .c 11, .c 17, .c 3, .c 7, .c 83, .c 3, .c 643, .c 5, .c 3,
  .c 109, .c 7, .c 3, .c 5, .c 419, .c 3, .c 13, .p pv2 [pv2,pv3,pv29,pv11903], .c 3, .c 17,
  .c 277, .c 3, .c 19, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5, .c 13, .c 3, .c 29, .c 7, .c 3, .c 11,
  .p pv23 [pv2,pv3,pv345193], .c 3, .c 257, .c 5, .c 3, .p pv3 [pv2,pv11,pv1471], .c 19, .c 3,
  .c 5, .c 113, .c 3, .c 7, .c 181, .c 3, .c 53, .p pv2 [pv2,pv3,pv7,pv8219], .c 3,
  .p pv3 [pv2,pv199,pv1301], .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 101, .c 3, .c 487,
  .p pv5 [pv2,pv3,pv11,pv13,pv17,pv71], .c 3, .c 293, .c 23, .c 3, .c 7, .c 5, .c 3, .c 17,
  .c 881, .c 3, .c 5, .c 7, .c 3, .c 97, .c 47, .c 3, .c 19, .c 149, .c 3, .c 271, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv197,pv751], .p pv7 [pv2,pv3,pv5,pv37,pv311], .c 3, .c 5, .c 11, .c 3,
  .p pv11 [pv2,pv5,pv207127], .c 461, .c 3, .c 13, .c 7, .c 3, .c 71, .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv13,pv47,pv113], .c 3, .c 5, .c 17,
]
private theorem h0252c26 : checkBlock 2071043 128 b0252c26 = true := by
  decide +kernel

private def b0252c27 : List Row := [
  .c 3, .c 79, .c 13, .c 3, .c 7, .c 1297, .c 3, .c 59, .c 5, .c 3, .p pv17 [pv2,pv1035659], .c 7,
  .c 3, .c 5, .c 31, .c 3, .c 17, .c 11, .c 3, .c 47, .p pv3 [pv2,pv3,pv97,pv3559], .c 3,
  .p pv17 [pv2,pv7,pv13,pv19,pv599], .c 5, .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv4603], .c 3, .c 5,
  .c 23, .c 3, .c 19, .c 7, .c 3, .p pv5 [pv2,pv11,pv94153], .c 857, .c 3,
  .p pv2 [pv2,pv59,pv67,pv131], .c 5, .c 3, .p pv2 [pv2,pv139,pv7451], .c 13, .c 3, .c 5, .c 211,
  .c 3, .c 7, .p pv5 [pv2,pv3,pv21577], .c 3, .p pv2 [pv2,pv43,pv12043], .c 11, .c 3, .c 23, .c 5,
  .c 3, .c 101, .p pv23 [pv2,pv3,pv5,pv11,pv6277], .c 3, .c 5, .c 739, .c 3, .c 11, .c 1289, .c 3,
  .p pv2 [pv2,pv7,pv23,pv919], .p pv7 [pv2,pv3,pv172619], .c 3, .c 7, .c 5, .c 3, .c 43, .c 29,
  .c 3, .c 5, .c 7, .c 3, .c 31, .p pv2 [pv2,pv3,pv53,pv3257], .c 3, .p pv3 [pv2,pv19,pv3407],
  .c 13, .c 3, .p pv5 [pv2,pv463,pv2237], .c 5, .c 3, .c 193, .p pv3 [pv2,pv3,pv5,pv29,pv2381],
  .c 3, .c 5, .c 1009, .c 3, .p pv3 [pv2,pv5,pv51787], .c 557, .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv517873], .c 5, .c 3, .c 29, .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv67,pv5153], .c 3,
  .c 13, .c 19, .c 3, .c 7, .c 37, .c 3, .c 587, .c 5, .c 3, .c 491, .c 7, .c 3, .c 5, .c 13,
  .c 3, .c 23, .p pv3 [pv2,pv3,pv11,pv31387], .c 3, .c 149, .c 59, .c 3, .c 11,
]
private theorem h0252c27 : checkBlock 2071299 128 b0252c27 = true := by
  decide +kernel

private def b0252c28 : List Row := [
  .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv61,pv283], .c 3, .c 5, .c 71, .c 3, .c 311, .c 7, .c 3,
  .c 137, .p pv3 [pv2,pv3,pv345263], .c 3, .p pv5 [pv2,pv1035791], .c 5, .c 3, .c 13,
  .p pv11 [pv2,pv3,pv5,pv199,pv347], .c 3, .c 5, .c 11, .c 3, .c 7, .c 17, .c 3, .c 41, .c 1021,
  .c 3, .p pv2 [pv2,pv467,pv1109], .c 5, .c 3, .c 11, .c 61, .c 3, .c 5, .c 19, .c 3,
  .p pv7 [pv2,pv5,pv11,pv37,pv509], .c 23, .c 3, .c 17, .c 103, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv41,pv1579], .c 263, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv103583], .c 11,
  .c 3, .c 13, .p pv2 [pv2,pv3,pv31,pv5569], .c 3, .c 29, .c 5, .c 3, .c 23,
  .p pv11 [pv2,pv3,pv5,pv13,pv83], .c 3, .c 5, .p pv3 [pv2,pv3,pv449,pv769], .c 3, .c 607, .c 13,
  .c 3, .c 43, .c 7, .c 3, .c 19, .c 5, .c 3, .c 71, .p pv3 [pv2,pv3,pv5,pv7673], .c 3, .c 5,
  .c 53, .c 3, .p pv3 [pv2,pv5,pv7,pv151], .p pv2 [pv2,pv3,pv17,pv19,pv1069], .c 3, .c 7, .c 11,
  .c 3, .p pv2 [pv2,pv13,pv39841], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 313, .c 3, .c 11,
  .p pv5 [pv2,pv3,pv86323], .c 3, .c 353, .p pv7 [pv2,pv3,pv13,pv26561], .c 3, .c 83, .c 5, .c 3,
  .c 7, .c 13, .c 3, .c 5, .c 191, .c 3, .p pv2 [pv2,pv5,pv71,pv1459], .c 7, .c 3, .c 1063, .c 29,
  .c 3, .c 619, .c 5, .c 3, .p pv7 [pv2,pv19,pv54521], .p pv11 [pv2,pv3,pv5,pv1151], .c 3, .c 5,
  .c 17, .c 3,
]
private theorem h0252c28 : checkBlock 2071555 128 b0252c28 = true := by
  decide +kernel

private def b0252c29 : List Row := [
  .c 7, .c 73, .c 3, .c 11, .p pv17 [pv2,pv3,pv7,pv29], .c 3, .c 13, .c 5, .c 3, .c 227, .c 89,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv19,pv233], .c 3, .c 17, .c 283, .c 3, .c 29, .c 13, .c 3,
  .c 7, .c 5, .c 3, .p pv2 [pv2,pv17,pv60937], .c 11, .c 3, .c 5, .c 7, .c 3, .c 151,
  .p pv5 [pv2,pv3,pv11,pv109], .c 3, .c 241, .p pv3 [pv2,pv3,pv127,pv2719], .c 3, .c 11, .c 5,
  .c 3, .c 37, .c 239, .c 3, .c 5, .p pv23 [pv2,pv3,pv131,pv659], .c 3, .c 13, .c 59, .c 3,
  .c 181, .c 7, .c 3, .p pv3 [pv2,pv19,pv43,pv317], .c 5, .c 3, .c 1399,
  .p pv7 [pv2,pv3,pv5,pv89,pv97], .c 3, .c 5, .c 11, .c 3, .c 19, .c 79, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv11,pv31393], .c 3, .c 17, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv172663], .c 3, .p pv3 [pv2,pv5,pv11,pv17,pv277], .c 29, .c 3, .c 401, .c 19,
  .c 3, .p pv2 [pv2,pv7,pv73999], .c 5, .c 3, .c 7, .c 109, .c 3, .c 5, .c 61, .c 3,
  .p pv11 [pv2,pv5,pv207199], .c 7, .c 3, .p pv2 [pv2,pv517999], .p pv3 [pv2,pv3,pv43,pv2677],
  .c 3, .p pv2 [pv2,pv1036001], .c 5, .c 3, .c 31, .c 17, .c 3, .c 5, .c 41, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv151,pv2287], .c 3, .c 131, .p pv2 [pv2,pv3,pv7,pv17,pv1451], .c 3,
  .p pv3 [pv2,pv73,pv887], .c 5, .c 3, .p pv7 [pv2,pv457,pv2267], .c 43, .c 3, .c 5, .c 23, .c 3,
  .c 103, .p pv2 [pv2,pv3,pv57557], .c 3, .c 13, .c 11, .c 3, .c 7, .c 5,
]
private theorem h0252c29 : checkBlock 2071811 128 b0252c29 = true := by
  decide +kernel

private def b0252c30 : List Row := [
  .c 3, .c 233, .c 31, .c 3, .c 5, .c 7, .c 3, .c 11, .c 13, .c 3, .p pv5 [pv2,pv157,pv6599],
  .c 47, .c 3, .c 23, .c 5, .c 3, .c 41, .p pv2 [pv2,pv3,pv5,pv6907], .c 3, .c 5, .c 269, .c 3,
  .c 37, .c 17, .c 3, .p pv2 [pv2,pv23,pv101,pv223], .c 7, .c 3, .p pv2 [pv2,pv13,pv79697], .c 5,
  .c 3, .p pv3 [pv2,pv32377], .p pv3 [pv2,pv3,pv5,pv17,pv239], .c 3, .c 5, .c 29, .c 3, .c 53,
  .c 149, .c 3, .c 7, .c 1319, .c 3, .p pv3 [pv2,pv259019], .c 5, .c 3, .c 19, .c 7, .c 3, .c 5,
  .c 673, .c 3, .c 787, .c 151, .c 3, .c 263, .p pv2 [pv2,pv3,pv19,pv73,pv83], .c 3, .c 47, .c 5,
  .c 3, .c 7, .c 11, .c 3, .c 5, .c 19, .c 3, .p pv3 [pv2,pv5,pv13,pv797], .c 7, .c 3,
  .p pv5 [pv2,pv71,pv14593], .p pv11 [pv2,pv3,pv23,pv1877], .c 3, .c 11, .c 5, .c 3, .c 163,
  .c 229, .c 3, .c 5, .c 743, .c 3, .c 7, .c 1097, .c 3, .c 277, .c 13, .c 3, .c 67, .c 5, .c 3,
  .c 17, .c 73, .c 3, .c 5, .c 11, .c 3, .c 83, .c 41, .c 3, .p pv2 [pv2,pv7,pv17,pv8707], .c 107,
  .c 3, .c 7, .c 5, .c 3, .c 11, .c 967, .c 3, .c 5, .c 7, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv19,pv61,pv149], .c 3, .c 677, .c 43, .c 3, .c 167, .c 5, .c 3, .c 691, .c 19,
  .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv1619],
]
private theorem h0252c30 : checkBlock 2072067 128 b0252c30 = true := by
  decide +kernel

private def b0252c31 : List Row := [
  .c 11, .c 3, .p pv5 [pv2,pv1036163], .c 7, .c 3, .c 37, .c 5, .c 3, .c 223, .c 647, .c 3, .c 5,
  .c 499, .c 3, .c 17, .c 53, .c 3, .c 7, .c 241, .c 3, .p pv2 [pv2,pv349,pv2969], .c 5, .c 3,
  .c 13, .c 7, .c 3, .c 5, .c 67, .c 3, .c 31, .p pv5 [pv2,pv3,pv13,pv163], .c 3, .c 19, .c 11,
  .c 3, .p pv3 [pv2,pv7,pv23,pv1609], .c 5, .c 3, .c 7, .c 883, .c 3, .c 5, .c 37, .c 3, .c 11,
  .c 7, .c 3, .c 109, .c 17, .c 3, .p pv5 [pv2,pv11,pv94201], .c 5, .c 3,
  .p pv2 [pv2,pv43,pv12049], .p pv11 [pv2,pv3,pv5,pv23027], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv17,pv10159], .c 3, .c 7, .c 31, .c 3, .c 13, .c 367, .c 3, .c 17, .c 5, .c 3,
  .c 53, .c 23, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv1163], .c 3, .c 43, .c 13, .c 3, .c 11,
  .p pv13 [pv2,pv3,pv345413], .c 3, .c 7, .c 5, .c 3, .p pv7 [pv2,pv11,pv2141],
  .p pv2 [pv2,pv3,pv5,pv7,pv71,pv139], .c 3, .c 5, .c 7, .c 3, .c 19, .c 617, .c 3, .c 23, .c 41,
  .c 3, .c 127, .c 5, .c 3, .c 439, .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv109,pv3169], .c 3,
  .p pv13 [pv2,pv5,pv23,pv9011], .c 113, .c 3, .c 1103, .c 7, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv518137], .c 13, .c 3, .c 5, .c 43, .c 3, .c 71, .p pv2 [pv2,pv3,pv223,pv1549],
  .c 3, .c 7, .p pv13 [pv2,pv3,pv86357], .c 3, .p pv2 [pv2,pv17,pv29,pv1051], .c 5, .c 3,
]
private theorem h0252c31 : checkBlock 2072323 128 b0252c31 = true := by
  decide +kernel

def rows0252 : List Row :=
  b0252c00 ++ b0252c01 ++ b0252c02 ++ b0252c03 ++ b0252c04 ++ b0252c05 ++ b0252c06 ++ b0252c07 ++
  b0252c08 ++ b0252c09 ++ b0252c10 ++ b0252c11 ++ b0252c12 ++ b0252c13 ++ b0252c14 ++ b0252c15 ++
  b0252c16 ++ b0252c17 ++ b0252c18 ++ b0252c19 ++ b0252c20 ++ b0252c21 ++ b0252c22 ++ b0252c23 ++
  b0252c24 ++ b0252c25 ++ b0252c26 ++ b0252c27 ++ b0252c28 ++ b0252c29 ++ b0252c30 ++ b0252c31

attribute [local irreducible] checkBlock checkRows checkPrime

theorem checked0252 : checkBlock 2064387 4096 rows0252 = true :=
  checkBlock_append h0252c00 (
    checkBlock_append h0252c01 (
    checkBlock_append h0252c02 (
    checkBlock_append h0252c03 (
    checkBlock_append h0252c04 (
    checkBlock_append h0252c05 (
    checkBlock_append h0252c06 (
    checkBlock_append h0252c07 (
    checkBlock_append h0252c08 (
    checkBlock_append h0252c09 (
    checkBlock_append h0252c10 (
    checkBlock_append h0252c11 (
    checkBlock_append h0252c12 (
    checkBlock_append h0252c13 (
    checkBlock_append h0252c14 (
    checkBlock_append h0252c15 (
    checkBlock_append h0252c16 (
    checkBlock_append h0252c17 (
    checkBlock_append h0252c18 (
    checkBlock_append h0252c19 (
    checkBlock_append h0252c20 (
    checkBlock_append h0252c21 (
    checkBlock_append h0252c22 (
    checkBlock_append h0252c23 (
    checkBlock_append h0252c24 (
    checkBlock_append h0252c25 (
    checkBlock_append h0252c26 (
    checkBlock_append h0252c27 (
    checkBlock_append h0252c28 (
    checkBlock_append h0252c29 (
    checkBlock_append h0252c30 (
    h0252c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
