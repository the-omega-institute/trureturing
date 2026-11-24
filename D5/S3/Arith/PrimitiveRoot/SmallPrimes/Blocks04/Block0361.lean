/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks04/Block0361
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks04/Block0361.checked0361
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table033
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table042
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table048
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table056
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table068
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table084
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table109
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table149
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table150

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0361c00 : List Row := [
  .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv17,pv4349], .c 113, .c 3, .p pv5 [pv2,pv1478663],
  .p pv31 [pv2,pv3,pv11,pv1867], .c 3, .c 29, .c 5, .c 3, .c 7, .c 61, .c 3, .c 5, .c 53, .c 3,
  .c 853, .c 7, .c 3, .c 13, .c 181, .c 3, .c 23, .c 5, .c 3, .c 19, .c 17, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv73,pv211], .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv23,pv239,pv269],
  .p pv2 [pv2,pv3,pv7,pv17,pv19,pv109], .c 3, .c 1459, .c 5, .c 3, .p pv7 [pv2,pv1478699],
  .p pv7 [pv2,pv3,pv5,pv31,pv53], .c 3, .c 5, .c 19, .c 3, .c 43, .p pv11 [pv2,pv3,pv41,pv6011],
  .c 3, .p pv3 [pv2,pv7,pv11,pv4801], .c 137, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv47,pv15731],
  .c 31, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv4621], .p pv5 [pv2,pv3,pv359,pv1373], .c 3,
  .c 37, .c 11, .c 3, .c 41, .c 5, .c 3, .p pv7 [pv2,pv7,pv211247], .c 13, .c 3, .c 5, .c 1579,
  .c 3, .c 11, .c 17, .c 3, .p pv2 [pv2,pv739369], .c 7, .c 3, .c 19, .c 5, .c 3,
  .p pv3 [pv2,pv184843], .c 1409, .c 3, .c 5, .c 43, .c 3, .c 23, .c 139, .c 3, .c 7, .c 1163,
  .c 3, .c 13, .c 5, .c 3, .c 701, .c 7, .c 3, .c 5, .c 1499, .c 3, .p pv11 [pv2,pv5,pv97,pv3049],
  .c 251, .c 3, .c 11, .c 13, .c 3, .c 439, .c 5, .c 3, .c 7, .c 487, .c 3, .c 5, .c 1481, .c 3,
  .c 197, .c 7, .c 3, .c 389, .c 47,
]
private theorem h0361c00 : checkBlock 2957315 128 b0361c00 = true := by
  decide +kernel

private def b0361c01 : List Row := [
  .c 3, .c 499, .c 5, .c 3, .p pv2 [pv2,pv13,pv19,pv5987], .c 11, .c 3, .c 5, .c 107, .c 3, .c 7,
  .c 23, .c 3, .c 19, .c 757, .c 3, .c 11, .c 5, .c 3, .c 17, .c 59, .c 3, .c 5, .c 13, .c 3,
  .p pv3 [pv2,pv5,pv147881], .c 29, .c 3, .c 97, .c 547, .c 3, .c 7, .c 5, .c 3, .c 23,
  .p pv13 [pv2,pv3,pv5,pv7,pv503], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv149,pv397], .c 367,
  .c 3, .p pv3 [pv2,pv13,pv28439], .p pv2 [pv2,pv3,pv11,pv41,pv1093], .c 3, .c 47, .c 5, .c 3,
  .c 11, .c 1693, .c 3, .c 5, .c 17, .c 3, .c 29, .p pv2 [pv2,pv3,pv7,pv13,pv5417], .c 3,
  .p pv5 [pv2,pv1478843], .c 7, .c 3, .c 137, .c 5, .c 3, .c 41, .c 1091, .c 3, .c 5, .c 61, .c 3,
  .c 17, .c 11, .c 3, .c 7, .c 1321, .c 3, .c 157, .c 5, .c 3, .c 59, .c 7, .c 3, .c 5, .c 89,
  .c 3, .c 31, .c 37, .c 3, .c 13, .c 19, .c 3, .p pv3 [pv2,pv7,pv52817], .c 5, .c 3, .c 7,
  .p pv59 [pv2,pv3,pv5,pv13,pv79], .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv70423], .c 3, .c 53, .c 7,
  .c 3, .c 23, .c 11, .c 3, .p pv5 [pv2,pv67,pv22073], .c 5, .c 3, .c 71,
  .p pv3 [pv2,pv3,pv5,pv11,pv8963], .c 3, .c 5, .c 29, .c 3, .c 7, .c 31, .c 3,
  .p pv5 [pv2,pv19,pv277,pv281], .p pv11 [pv2,pv3,pv7,pv8803], .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv1478909], .c 97, .c 3, .c 5,
]
private theorem h0361c01 : checkBlock 2957571 128 b0361c01 = true := by
  decide +kernel

private def b0361c02 : List Row := [
  .p pv2 [pv2,pv3,pv29,pv89,pv191], .c 3, .p pv13 [pv2,pv5,pv17,pv127,pv137],
  .p pv13 [pv2,pv3,pv41081], .c 3, .c 1021, .c 79, .c 3, .c 7, .c 5, .c 3, .c 67, .c 13, .c 3,
  .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv71,pv2083], .c 19, .c 3, .c 11, .c 23, .c 3,
  .p pv3 [pv2,pv223,pv829], .c 5, .c 3, .p pv11 [pv2,pv7,pv11,pv19207], .c 17, .c 3, .c 5, .c 73,
  .c 3, .c 37, .c 587, .c 3, .p pv3 [pv2,pv31,pv11927], .c 7, .c 3, .c 13, .c 5, .c 3, .c 383,
  .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv67,pv283], .c 3, .c 311, .c 1069, .c 3, .c 7, .c 13,
  .c 3, .c 11, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv421,pv1171], .c 3, .c 61,
  .c 431, .c 3, .c 127, .c 1699, .c 3, .p pv2 [pv2,pv7,pv211283], .c 5, .c 3, .c 7, .c 29, .c 3,
  .c 5, .c 11, .c 3, .c 13, .c 7, .c 3, .c 101, .c 31, .c 3, .c 229, .c 5, .c 3, .c 11, .c 113,
  .c 3, .c 5, .c 13, .c 3, .c 7, .c 43, .c 3, .c 17, .p pv2 [pv2,pv3,pv7,pv70429], .c 3,
  .p pv5 [pv2,pv1479011], .c 5, .c 3, .c 29, .p pv3 [pv2,pv3,pv5,pv23,pv1429], .c 3, .c 5, .c 83,
  .c 3, .p pv3 [pv2,pv5,pv73951], .c 11, .c 3, .c 397, .p pv11 [pv2,pv3,pv10271], .c 3, .c 7,
  .c 5, .c 3, .c 13, .p pv11 [pv2,pv3,pv5,pv7,pv7043], .c 3, .c 5, .c 7, .c 3, .c 167, .c 61,
  .c 3, .p pv2 [pv2,pv11,pv23,pv37,pv79], .p pv11 [pv2,pv3,pv493013], .c 3,
]
private theorem h0361c02 : checkBlock 2957827 128 b0361c02 = true := by
  decide +kernel

private def b0361c03 : List Row := [
  .c 59, .c 5, .c 3, .c 53, .c 19, .c 3, .c 5, .c 149, .c 3, .p pv3 [pv2,pv5,pv29581], .c 239,
  .c 3, .c 463, .c 7, .c 3, .c 31, .c 5, .c 3, .c 17, .c 877, .c 3, .c 5, .c 173, .c 3, .c 11,
  .c 47, .c 3, .c 7, .p pv2 [pv2,pv3,pv164341], .c 3, .c 503, .c 5, .c 3,
  .p pv2 [pv2,pv19,pv38923], .c 7, .c 3, .c 5, .c 1019, .c 3, .c 457, .c 13, .c 3, .c 19,
  .p pv37 [pv2,pv3,pv23,pv233], .c 3, .p pv3 [pv2,pv7,pv105649], .c 5, .c 3, .c 7, .c 1471, .c 3,
  .c 5, .c 17, .c 3, .c 23, .c 7, .c 3, .c 11, .c 283, .c 3, .c 29, .c 5, .c 3, .c 97, .c 127,
  .c 3, .c 5, .c 739, .c 3, .c 7, .p pv3 [pv2,pv3,pv229,pv2153], .c 3, .c 47, .c 107, .c 3,
  .p pv3 [pv2,pv29,pv41,pv311], .c 5, .c 3, .p pv7 [pv2,pv17,pv167,pv521], .c 11, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv149,pv1103], .c 3, .c 67, .p pv2 [pv2,pv3,pv11,pv73,pv307], .c 3,
  .p pv3 [pv2,pv7,pv61,pv433], .p pv3 [pv2,pv3,pv493043], .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv31,pv23857], .c 43, .c 3, .c 5, .c 7, .c 3, .c 19, .c 23, .c 3, .c 163, .c 17,
  .c 3, .c 13, .c 5, .c 3, .c 31, .c 53, .c 3, .c 5, .c 11, .c 3, .p pv13 [pv2,pv5,pv295831],
  .c 79, .c 3, .c 61, .c 7, .c 3, .c 17, .c 5, .c 3, .c 11, .p pv23 [pv2,pv3,pv5,pv31,pv3181],
  .c 3, .c 5, .c 139,
]
private theorem h0361c03 : checkBlock 2958083 128 b0361c03 = true := by
  decide +kernel

private def b0361c04 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv7,pv11,pv17,pv113], .c 769, .c 3, .c 7, .c 197, .c 3,
  .p pv3 [pv2,pv23,pv8039], .c 5, .c 3, .p pv29 [pv2,pv13,pv113783], .c 7, .c 3, .c 5, .c 421,
  .c 3, .c 13, .c 11, .c 3, .c 29, .p pv3 [pv2,pv3,pv59,pv61,pv137], .c 3,
  .p pv5 [pv2,pv7,pv211313], .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 13, .c 3, .c 233, .c 7, .c 3,
  .c 53, .c 37, .c 3, .p pv2 [pv2,pv739603], .c 5, .c 3, .p pv2 [pv2,pv1479209], .c 23, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv164357], .c 3, .c 7, .c 19, .c 3, .c 41, .c 11, .c 3, .c 43, .c 5, .c 3,
  .c 13, .c 229, .c 3, .c 5, .c 1297, .c 3, .c 11, .p pv7 [pv2,pv3,pv13,pv47,pv269], .c 3, .c 23,
  .c 103, .c 3, .c 7, .c 5, .c 3, .p pv17 [pv2,pv41,pv109,pv331], .p pv13 [pv2,pv3,pv5,pv7,pv587],
  .c 3, .c 5, .c 7, .c 3, .c 227, .c 17, .c 3, .c 193, .c 71, .c 3, .p pv5 [pv2,pv1479251], .c 5,
  .c 3, .c 19, .p pv29 [pv2,pv3,pv5,pv17,pv5801], .c 3, .c 5, .c 1319, .c 3,
  .p pv3 [pv2,pv5,pv37,pv1999], .c 337, .c 3, .c 11, .c 7, .c 3, .c 199, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv89,pv1511], .c 223, .c 3, .c 5, .c 19, .c 3, .c 29, .c 13, .c 3, .c 7, .c 23,
  .c 3, .p pv2 [pv2,pv1479281], .c 5, .c 3, .p pv3 [pv2,pv369821], .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv61637], .c 3, .c 239, .p pv3 [pv2,pv3,pv11,pv23,pv1949], .c 3, .c 109,
  .c 1451, .c 3, .c 11,
]
private theorem h0361c04 : checkBlock 2958339 128 b0361c04 = true := by
  decide +kernel

private def b0361c05 : List Row := [
  .c 5, .c 3, .c 7, .c 41, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv2609], .c 3, .c 523, .c 7, .c 3,
  .c 73, .c 53, .c 3, .c 19, .c 5, .c 3, .c 17, .c 13, .c 3, .c 5, .c 11, .c 3, .c 7, .c 1489,
  .c 3, .p pv5 [pv2,pv17,pv173,pv503], .c 281, .c 3, .c 67, .c 5, .c 3, .c 11, .c 19, .c 3, .c 5,
  .c 29, .c 3, .c 31, .c 59, .c 3, .p pv2 [pv2,pv7,pv105667], .c 113, .c 3, .c 7, .c 5, .c 3,
  .c 433, .c 179, .c 3, .c 5, .c 7, .c 3, .c 43, .c 11, .c 3, .p pv2 [pv2,pv409,pv3617], .c 13,
  .c 3, .p pv3 [pv2,pv71,pv5209], .c 5, .c 3, .c 127, .p pv7 [pv2,pv3,pv5,pv23,pv67], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv493121], .c 3, .c 17, .c 31, .c 3, .c 19, .c 7, .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv17,pv3347], .c 1093, .c 3, .c 5, .c 241, .c 3, .c 13, .c 73, .c 3, .c 7,
  .c 11, .c 3, .p pv2 [pv2,pv739693], .c 5, .c 3, .c 37, .c 7, .c 3, .c 5, .c 13, .c 3, .c 11,
  .p pv19 [pv2,pv3,pv113,pv1091], .c 3, .c 443, .c 17, .c 3, .p pv2 [pv2,pv7,pv11,pv19213], .c 5,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv98627], .c 3, .c 5, .c 509, .c 3,
  .p pv3 [pv2,pv5,pv239,pv619], .c 7, .c 3, .p pv2 [pv2,pv13,pv31,pv3671],
  .p pv2 [pv2,pv3,pv246569], .c 3, .c 17, .c 5, .c 3, .c 13, .c 29, .c 3, .c 5, .c 41, .c 3,
]
private theorem h0361c05 : checkBlock 2958595 128 b0361c05 = true := by
  decide +kernel

private def b0361c06 : List Row := [
  .c 7, .c 37, .c 3, .c 11, .p pv2 [pv2,pv3,pv7,pv23,pv1021], .c 3, .p pv5 [pv2,pv691,pv2141],
  .c 5, .c 3, .c 347, .c 107, .c 3, .c 5, .p pv2 [pv2,pv3,pv27397], .c 3, .c 23, .c 193, .c 3,
  .p pv5 [pv2,pv7,pv211349], .c 19, .c 3, .c 7, .c 5, .c 3, .c 29, .c 11, .c 3, .c 5, .c 7, .c 3,
  .p pv29 [pv2,pv5,pv449,pv659], .p pv7 [pv2,pv3,pv11,pv467], .c 3, .c 13, .c 31, .c 3, .c 11,
  .c 5, .c 3, .c 41, .c 199, .c 3, .c 5, .c 53, .c 3, .p pv2 [pv2,pv5,pv197,pv751], .c 13, .c 3,
  .p pv2 [pv2,pv19,pv77867], .c 7, .c 3, .p pv3 [pv2,pv17,pv21757], .c 5, .c 3, .c 43,
  .p pv7 [pv2,pv3,pv5,pv12329], .c 3, .c 5, .c 11, .c 3, .p pv7 [pv2,pv5,pv7,pv41,pv1031], .c 23,
  .c 3, .c 7, .c 47, .c 3, .c 89, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 101, .c 3, .c 37, .c 17,
  .c 3, .c 293, .c 373, .c 3, .c 263, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 59, .c 3,
  .p pv17 [pv2,pv5,pv295903], .c 7, .c 3, .c 17, .c 251, .c 3, .c 31, .c 5, .c 3, .c 61,
  .p pv3 [pv2,pv3,pv5,pv19727], .c 3, .c 5, .c 853, .c 3, .c 7, .c 137, .c 3, .c 71,
  .p pv31 [pv2,pv3,pv7,pv35227], .c 3, .c 13, .c 5, .c 3, .c 19, .p pv17 [pv2,pv3,pv5,pv24659],
  .c 3, .c 5, .c 103, .c 3, .p pv2 [pv2,pv5,pv295909], .c 41, .c 3, .p pv3 [pv2,pv7,pv53,pv997],
  .c 11, .c 3, .c 7, .c 5,
]
private theorem h0361c06 : checkBlock 2958851 128 b0361c06 = true := by
  decide +kernel

private def b0361c07 : List Row := [
  .c 3, .c 1129, .c 23, .c 3, .c 5, .c 7, .c 3, .c 11, .c 389, .c 3, .p pv5 [pv2,pv991,pv1493],
  .c 1061, .c 3, .p pv2 [pv2,pv11,pv109,pv617], .c 5, .c 3, .c 17,
  .p pv7 [pv2,pv3,pv5,pv149,pv331], .c 3, .c 5, .c 151, .c 3, .c 13, .c 839, .c 3, .c 23, .c 7,
  .c 3, .c 191, .c 5, .c 3, .c 181, .c 61, .c 3, .c 5, .c 13, .c 3, .c 673,
  .p pv5 [pv2,pv3,pv79,pv2081], .c 3, .c 7, .c 29, .c 3, .c 19, .c 5, .c 3, .c 83, .c 7, .c 3,
  .c 5, .c 17, .c 3, .c 281, .p pv2 [pv2,pv3,pv19,pv12979], .c 3, .c 43,
  .p pv3 [pv2,pv3,pv29,pv5669], .c 3, .c 37, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 359, .c 3,
  .c 17, .c 7, .c 3, .c 29, .c 23, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv17,pv87037], .c 47,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv493211], .c 3, .c 7, .p pv5 [pv2,pv3,pv23,pv1787], .c 3,
  .p pv2 [pv2,pv29,pv97,pv263], .c 881, .c 3, .p pv2 [pv2,pv83,pv17827], .c 5, .c 3, .c 149,
  .c 31, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv101,pv293], .c 43, .c 3, .c 13, .c 17, .c 3,
  .c 7, .c 5, .c 3, .c 11, .p pv17 [pv2,pv3,pv5,pv7,pv13,pv271], .c 3, .c 5, .c 7, .c 3, .c 283,
  .c 13, .c 3, .c 137, .c 41, .c 3, .c 17, .c 5, .c 3, .c 1103, .c 71, .c 3, .c 5, .c 113, .c 3,
  .c 53,
]
private theorem h0361c07 : checkBlock 2959107 128 b0361c07 = true := by
  decide +kernel

private def b0361c08 : List Row := [
  .c 11, .c 3, .c 229, .c 7, .c 3, .c 97, .c 5, .c 3, .c 467, .c 59, .c 3, .c 5, .c 23, .c 3,
  .p pv13 [pv2,pv5,pv7,pv67,pv631], .p pv5 [pv2,pv3,pv29,pv1063], .c 3, .c 7, .c 227, .c 3,
  .p pv2 [pv2,pv19,pv47,pv1657], .c 5, .c 3, .p pv3 [pv2,pv37,pv4999], .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv4567], .c 3, .c 19, .c 1531, .c 3, .p pv2 [pv2,pv1479713], .c 11, .c 3, .c 23,
  .c 5, .c 3, .c 7, .c 383, .c 3, .c 5, .p pv19 [pv2,pv3,pv7,pv31,pv2273], .c 3, .c 11, .c 7,
  .c 3, .c 67, .c 19, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv277,pv2671], .c 331, .c 3, .c 5,
  .c 31, .c 3, .c 7, .c 1381, .c 3, .p pv5 [pv2,pv211,pv7013], .c 13, .c 3, .c 71, .c 5, .c 3,
  .c 59, .p pv7 [pv2,pv3,pv5,pv1973], .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv14947], .c 3, .c 173,
  .c 17, .c 3, .c 11, .c 37, .c 3, .c 7, .c 5, .c 3, .c 761, .c 83, .c 3, .c 5, .c 7, .c 3, .c 13,
  .c 47, .c 3, .c 17, .p pv11 [pv2,pv3,pv23,pv10723], .c 3, .c 691, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv59,pv3583], .c 11, .c 3, .c 5, .c 13, .c 3, .c 23, .c 19, .c 3, .c 79, .c 7,
  .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv139,pv5323], .c 67, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv229,pv359], .c 3, .c 31, .c 101, .c 3, .c 7, .p pv17 [pv2,pv3,pv127,pv971],
  .c 3, .p pv2 [pv2,pv257,pv2879], .c 5, .c 3,
]
private theorem h0361c08 : checkBlock 2959363 128 b0361c08 = true := by
  decide +kernel

private def b0361c09 : List Row := [
  .c 13, .c 7, .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv19,pv37,pv421],
  .p pv5 [pv2,pv3,pv13,pv17,pv31], .c 3, .c 47, .c 73, .c 3, .p pv2 [pv2,pv7,pv211403], .c 5,
  .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv6577], .c 3, .c 5, .c 523, .c 3, .p pv7 [pv2,pv5,pv11,pv1223],
  .c 7, .c 3, .c 37, .p pv7 [pv2,pv3,pv19,pv4327], .c 3, .p pv3 [pv2,pv369959], .c 5, .c 3, .c 53,
  .p pv11 [pv2,pv3,pv5,pv3083], .c 3, .c 5, .c 19, .c 3, .c 7, .c 11, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv7,pv10067], .c 3, .p pv5 [pv2,pv1479851], .c 5, .c 3, .c 23, .c 29, .c 3,
  .c 5, .c 17, .c 3, .c 241, .c 13, .c 3, .c 107, .c 643, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv439,pv3371], .c 37, .c 3, .c 5, .c 7, .c 3, .c 17, .p pv5 [pv2,pv3,pv123323],
  .c 3, .p pv2 [pv2,pv31,pv23869], .c 11, .c 3, .c 19, .c 5, .c 3, .c 29,
  .p pv3 [pv2,pv3,pv5,pv11,pv8969], .c 3, .c 5, .c 71, .c 3, .c 11,
  .p pv5 [pv2,pv3,pv7,pv19,pv3709], .c 3, .c 31, .c 7, .c 3, .p pv3 [pv2,pv11,pv67,pv251], .c 5,
  .c 3, .c 233, .c 13, .c 3, .c 5, .c 269, .c 3, .c 541, .c 983, .c 3, .c 7, .c 17, .c 3,
  .p pv5 [pv2,pv1479911], .c 5, .c 3, .c 317, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv17,pv1319],
  .c 3, .p pv3 [pv2,pv5,pv13,pv1423], .p pv2 [pv2,pv3,pv61,pv8087], .c 3, .c 11, .c 31, .c 3,
  .c 13, .c 5, .c 3, .c 7, .p pv19 [pv2,pv3,pv5,pv49331], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv13,pv139], .c 3, .c 337, .c 7,
]
private theorem h0361c09 : checkBlock 2959619 128 b0361c09 = true := by
  decide +kernel

private def b0361c10 : List Row := [
  .c 3, .c 19, .c 13, .c 3, .c 1091, .c 5, .c 3, .c 37, .c 11, .c 3, .c 5, .c 283, .c 3, .c 7,
  .c 61, .c 3, .c 787, .c 1259, .c 3, .c 11, .c 5, .c 3, .c 47, .c 17, .c 3, .c 5, .c 191, .c 3,
  .c 13, .c 409, .c 3, .p pv5 [pv2,pv7,pv6607], .c 23, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv43,pv17209], .p pv11 [pv2,pv3,pv5,pv7,pv2819], .c 3, .c 5, .c 7, .c 3,
  .p pv17 [pv2,pv5,pv73999], .c 37, .c 3, .p pv5 [pv2,pv47,pv31489], .p pv7 [pv2,pv3,pv11,pv2803],
  .c 3, .c 31, .c 5, .c 3, .c 11, .p pv23 [pv2,pv3,pv5,pv49333], .c 3, .c 5, .c 967, .c 3, .c 19,
  .c 67, .c 3, .c 53, .c 7, .c 3, .p pv2 [pv2,pv1480001], .c 5, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv5,pv19,pv577], .c 3, .c 5, .p pv5 [pv2,pv3,pv61667], .c 3, .c 631, .c 11,
  .c 3, .c 7, .c 19, .c 3, .p pv3 [pv2,pv233,pv397], .c 5, .c 3, .p pv11 [pv2,pv1480019], .c 7,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv164447], .c 3, .c 79, .c 151, .c 3, .c 17, .c 29, .c 3, .c 1567,
  .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv98669], .c 3, .c 5, .c 23, .c 3, .c 461, .c 7, .c 3,
  .c 13, .c 11, .c 3, .c 997, .c 5, .c 3, .c 919, .p pv2 [pv2,pv3,pv5,pv11,pv13,pv23], .c 3, .c 5,
  .c 47, .c 3, .c 7, .c 13, .c 3, .c 29, .c 211, .c 3, .c 23, .c 5, .c 3, .p pv3 [pv2,pv31,pv373],
]
private theorem h0361c10 : checkBlock 2959875 128 b0361c10 = true := by
  decide +kernel

private def b0361c11 : List Row := [
  .c 809, .c 3, .c 5, .p pv5 [pv2,pv3,pv41113], .c 3, .c 1237, .c 19, .c 3, .c 61, .c 97, .c 3,
  .c 7, .c 5, .c 3, .c 17, .p pv11 [pv2,pv3,pv5,pv7,pv881], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv296017], .p pv13 [pv2,pv3,pv27409], .c 3, .c 11, .c 293, .c 3, .c 149, .c 5,
  .c 3, .p pv3 [pv2,pv7,pv11,pv1373], .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv246683], .c 3, .c 47,
  .c 71, .c 3, .c 59, .c 7, .c 3, .p pv2 [pv2,pv740053], .c 5, .c 3, .c 19, .c 11, .c 3, .c 5,
  .c 17, .c 3, .p pv7 [pv2,pv5,pv7,pv13,pv3253], .c 29, .c 3, .c 7, .c 491, .c 3, .c 11, .c 5,
  .c 3, .c 43, .c 7, .c 3, .c 5, .c 19, .c 3, .c 17, .c 1291, .c 3, .p pv2 [pv2,pv59,pv25087],
  .c 13, .c 3, .p pv3 [pv2,pv7,pv26431], .c 5, .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv2741], .c 3,
  .c 5, .c 11, .c 3, .c 29, .c 7, .c 3, .p pv3 [pv2,pv37,pv73,pv137], .c 277, .c 3,
  .p pv5 [pv2,pv179,pv8269], .c 5, .c 3, .c 11, .c 1459, .c 3, .c 5, .p pv2 [pv2,pv3,pv82231],
  .c 3, .c 7, .c 41, .c 3, .p pv5 [pv2,pv1480163], .c 17, .c 3, .c 19, .c 5, .c 3, .c 607,
  .p pv2 [pv2,pv3,pv5,pv49339], .c 3, .c 5, .c 13, .c 3, .p pv17 [pv2,pv5,pv59207], .c 11, .c 3,
  .p pv2 [pv2,pv7,pv105727], .c 829, .c 3, .c 7, .c 5, .c 3, .c 73, .c 19, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv17,pv8707], .c 257, .c 3,
]
private theorem h0361c11 : checkBlock 2960131 128 b0361c11 = true := by
  decide +kernel

private def b0361c12 : List Row := [
  .p pv2 [pv2,pv11,pv13,pv941], .c 47, .c 3, .p pv3 [pv2,pv157,pv2357], .c 5, .c 3, .c 13, .c 307,
  .c 3, .c 5, .c 29, .c 3, .c 101, .p pv23 [pv2,pv3,pv7,pv13,pv2711], .c 3,
  .p pv3 [pv2,pv71,pv1303], .c 7, .c 3, .p pv5 [pv2,pv23,pv139,pv463], .c 5, .c 3, .c 397, .c 17,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv29,pv47,pv181], .c 3, .c 11, .c 59, .c 3, .c 7,
  .p pv19 [pv2,pv3,pv17,pv907], .c 3, .p pv2 [pv2,pv11,pv61,pv1103], .c 5, .c 3,
  .p pv2 [pv2,pv1480229], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv19,pv25969], .c 3,
  .p pv17 [pv2,pv5,pv296047], .c 487, .c 3, .c 13, .p pv7 [pv2,pv3,pv164471], .c 3, .c 47, .c 5,
  .c 3, .c 7, .c 23, .c 3, .c 5, .c 127, .c 3, .c 373, .c 7, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv246709], .c 3, .c 61, .c 5, .c 3, .c 1481, .c 677, .c 3, .c 5, .c 53, .c 3,
  .c 7, .c 17, .c 3, .c 23, .c 431, .c 3, .p pv5 [pv2,pv13,pv19,pv461], .c 5, .c 3, .c 109, .c 11,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv246713], .c 3, .c 19, .p pv3 [pv2,pv3,pv11,pv31,pv1447], .c 3,
  .c 17, .c 41, .c 3, .c 7, .c 5, .c 3, .c 971, .c 13, .c 3, .c 5, .c 7, .c 3, .c 263, .c 31,
  .c 3, .p pv2 [pv2,pv67,pv11047], .c 19, .c 3, .p pv2 [pv2,pv1480301], .c 5, .c 3,
  .p pv13 [pv2,pv7,pv13217], .c 353, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv13,pv59,pv193],
  .p pv3 [pv2,pv3,pv7,pv23497], .c 3, .c 757, .c 7, .c 3, .c 13, .c 5, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv5,pv257],
]
private theorem h0361c12 : checkBlock 2960387 128 b0361c12 = true := by
  decide +kernel

private def b0361c13 : List Row := [
  .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv37957], .c 3, .c 41, .p pv2 [pv2,pv3,pv17,pv23,pv631], .c 3,
  .c 7, .c 13, .c 3, .c 67, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 619, .c 3,
  .p pv3 [pv2,pv5,pv74017], .c 11, .c 3, .p pv5 [pv2,pv17,pv31,pv53], .p pv11 [pv2,pv3,pv61681],
  .c 3, .c 83, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv71,pv139], .c 3, .c 5, .c 137, .c 3, .c 13,
  .c 7, .c 3, .c 31, .p pv11 [pv2,pv3,pv47,pv10499], .c 3, .c 929, .c 5, .c 3,
  .p pv3 [pv2,pv370091], .c 97, .c 3, .c 5, .c 13, .c 3, .c 7, .c 167, .c 3,
  .p pv2 [pv2,pv283,pv5231], .c 11, .c 3, .p pv3 [pv2,pv211,pv877], .c 5, .c 3,
  .p pv7 [pv2,pv1480379], .c 227, .c 3, .c 5, .c 23, .c 3, .c 11, .p pv2 [pv2,pv3,pv246731], .c 3,
  .c 37, .c 31, .c 3, .c 7, .c 5, .c 3, .c 13, .p pv37 [pv2,pv3,pv5,pv7,pv23,pv613], .c 3, .c 5,
  .c 7, .c 3, .p pv3 [pv2,pv5,pv3701], .c 1097, .c 3, .c 73, .p pv13 [pv2,pv3,pv19,pv43,pv151],
  .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv7,pv61,pv3467], .p pv2 [pv2,pv3,pv5,pv5483], .c 3, .c 5,
  .c 19, .c 3, .c 839, .c 1289, .c 3, .c 11, .c 7, .c 3, .c 521, .c 5, .c 3, .c 593, .c 37, .c 3,
  .c 5, .c 599, .c 3, .p pv3 [pv2,pv5,pv7,pv21149], .c 157, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv246739], .c 3, .c 17, .c 5, .c 3, .c 61, .c 7, .c 3, .c 5, .c 659, .c 3,
  .p pv2 [pv2,pv5,pv17,pv17417], .c 13, .c 3, .c 41,
]
private theorem h0361c13 : checkBlock 2960643 128 b0361c13 = true := by
  decide +kernel

private def b0361c14 : List Row := [
  .p pv2 [pv2,pv3,pv53,pv9311], .c 3, .c 11, .c 5, .c 3, .c 7, .c 547, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv101,pv349], .c 3, .c 199, .c 7, .c 3, .p pv5 [pv2,pv241,pv6143], .c 29,
  .c 3, .c 1213, .c 5, .c 3, .c 113, .c 17, .c 3, .c 5, .c 11, .c 3, .c 7, .c 47, .c 3,
  .p pv2 [pv2,pv367,pv2017], .c 151, .c 3, .c 211, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv61687], .c 3, .c 137, .c 617, .c 3, .c 29, .p pv2 [pv2,pv3,pv227,pv1087],
  .c 3, .c 7, .c 5, .c 3, .c 37, .c 61, .c 3, .c 5, .c 7, .c 3, .c 107, .c 11, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv179,pv919], .c 3, .c 13, .c 5, .c 3, .c 283, .c 311, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv13,pv19,pv37], .c 3, .c 881, .c 17, .c 3, .c 47, .c 7, .c 3,
  .p pv2 [pv2,pv113,pv6551], .c 5, .c 3, .c 1657, .c 41, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv23,pv43,pv499], .c 3, .c 727, .c 37, .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv1480541], .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 317, .c 3, .c 11, .c 29, .c 3,
  .c 197, .c 43, .c 3, .p pv3 [pv2,pv7,pv11,pv19,pv23], .c 5, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv5,pv31,pv199], .c 3, .c 5, .c 13, .c 3, .c 19, .c 7, .c 3,
  .p pv3 [pv2,pv185071], .p pv17 [pv2,pv3,pv493523], .c 3, .c 41, .c 5, .c 3,
  .p pv2 [pv2,pv740287], .c 31, .c 3,
]
private theorem h0361c14 : checkBlock 2960899 128 b0361c14 = true := by
  decide +kernel

private def b0361c15 : List Row := [
  .c 5, .c 79, .c 3, .c 7, .c 53, .c 3, .c 11, .c 19, .c 3, .c 739, .c 5, .c 3, .c 13, .c 23,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv493531], .c 3, .c 83, .c 751, .c 3, .c 71, .c 67, .c 3, .c 7,
  .c 5, .c 3, .p pv3 [pv2,pv89,pv4159], .c 11, .c 3, .c 5, .c 7, .c 3, .c 37, .c 397, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv246769], .c 3, .c 11, .c 5, .c 3, .p pv7 [pv2,pv7,pv43,pv4919], .c 173, .c 3,
  .c 5, .c 17, .c 3, .c 1061, .p pv2 [pv2,pv3,pv7,pv3917], .c 3, .c 13, .c 7, .c 3, .c 1423, .c 5,
  .c 3, .c 53, .p pv3 [pv2,pv3,pv5,pv13,pv2531], .c 3, .c 5, .c 11, .c 3, .c 17, .c 13, .c 3,
  .c 7, .p pv29 [pv2,pv3,pv11,pv3739], .c 3, .c 313, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 41,
  .c 3, .p pv11 [pv2,pv5,pv11,pv26921], .c 97, .c 3, .c 353, .c 23, .c 3, .c 367, .c 5, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv5,pv98711], .c 3, .c 5, .c 31, .c 3, .c 181, .c 7, .c 3, .c 821, .c 17,
  .c 3, .c 103, .c 5, .c 3, .c 19, .c 13, .c 3, .c 5, .c 43, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv246781], .c 3, .p pv3 [pv2,pv11,pv47,pv179], .c 1249, .c 3, .c 17, .c 5, .c 3,
  .c 41, .c 73, .c 3, .c 5, .c 19, .c 3, .c 431, .c 613, .c 3, .c 277, .c 11,
]
private theorem h0361c15 : checkBlock 2961155 128 b0361c15 = true := by
  decide +kernel

private def b0361c16 : List Row := [
  .c 3, .c 7, .c 5, .c 3, .c 769, .c 101, .c 3, .c 5, .c 7, .c 3, .c 11, .p pv5 [pv2,pv3,pv41131],
  .c 3, .p pv2 [pv2,pv740359], .c 13, .c 3, .c 37, .c 5, .c 3, .c 239, .c 17, .c 3, .c 5, .c 23,
  .c 3, .c 31, .p pv13 [pv2,pv3,pv7,pv1439], .c 3, .c 67, .c 7, .c 3, .c 19, .c 5, .c 3,
  .p pv11 [pv2,pv13,pv113903], .c 53, .c 3, .c 5, .c 827, .c 3, .c 13, .c 709, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv493583], .c 3, .c 23, .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .c 13, .c 3,
  .p pv3 [pv2,pv5,pv37019], .c 31, .c 3, .p pv5 [pv2,pv23,pv64381], .c 137, .c 3,
  .p pv2 [pv2,pv7,pv105769], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 163, .c 3, .c 1483, .c 7,
  .c 3, .p pv2 [pv2,pv13,pv337], .c 103, .c 3, .c 11, .c 5, .c 3, .c 13, .c 1553, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv13711], .c 3, .c 7, .p pv3 [pv2,pv3,pv13,pv43,pv883], .c 3, .c 17,
  .p pv23 [pv2,pv3,pv7,pv35257], .c 3, .p pv3 [pv2,pv370199], .c 5, .c 3,
  .p pv7 [pv2,pv743,pv1993], .c 67, .c 3, .c 5, .c 11, .c 3, .c 47, .p pv2 [pv2,pv3,pv82267],
  .c 3, .c 113, .p pv2 [pv2,pv3,pv11,pv23,pv1951], .c 3, .c 7, .c 5, .c 3, .c 11, .c 79, .c 3,
  .c 5, .c 7, .c 3, .c 23, .c 263, .c 3, .c 13, .c 241, .c 3, .c 89, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv47,pv643], .c 911, .c 3, .c 5,
]
private theorem h0361c16 : checkBlock 2961411 128 b0361c16 = true := by
  decide +kernel

private def b0361c17 : List Row := [
  .p pv3 [pv2,pv3,pv137,pv1201], .c 3, .p pv11 [pv2,pv5,pv353,pv839], .c 11, .c 3,
  .p pv2 [pv2,pv41,pv18059], .c 7, .c 3, .c 29, .c 5, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv5,pv269,pv367], .c 3, .c 5, .c 1709, .c 3, .c 19, .c 181, .c 3, .c 7, .c 31,
  .c 3, .p pv3 [pv2,pv13,pv29,pv491], .c 5, .c 3, .c 1303, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv493621], .c 3, .c 317, .c 23, .c 3, .p pv3 [pv2,pv370217], .c 11, .c 3,
  .p pv5 [pv2,pv7,pv89,pv2377], .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 17, .c 3, .c 11, .c 7,
  .c 3, .c 127, .p pv7 [pv2,pv3,pv123407], .c 3, .p pv2 [pv2,pv11,pv83,pv811], .c 5, .c 3, .c 23,
  .p pv17 [pv2,pv3,pv5,pv49363], .c 3, .c 5, .p pv2 [pv2,pv3,pv401,pv1231], .c 3, .c 7, .c 1583,
  .c 3, .c 43, .c 29, .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv17,pv10889], .c 463, .c 3, .c 5,
  .c 457, .c 3, .p pv3 [pv2,pv5,pv148091], .p pv3 [pv2,pv3,pv149,pv3313], .c 3, .c 11, .c 13,
  .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv11,pv12239], .c 1721, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv37,pv1601], .c 19, .c 3, .c 29, .c 17, .c 3, .p pv5 [pv2,pv1480931], .c 5,
  .c 3, .c 67, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv14519], .c 3, .c 13, .c 43, .c 3, .c 37,
  .c 7, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv443,pv3343], .p pv2 [pv2,pv3,pv5,pv1097], .c 3,
  .c 5, .c 13, .c 3, .c 419, .c 179, .c 3, .c 7, .c 313, .c 3,
]
private theorem h0361c17 : checkBlock 2961667 128 b0361c17 = true := by
  decide +kernel

private def b0361c18 : List Row := [
  .p pv2 [pv2,pv41,pv881], .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 11, .c 3, .c 661, .c 563, .c 3,
  .c 79, .p pv17 [pv2,pv3,pv11,pv19,pv1181], .c 3, .p pv5 [pv2,pv7,pv1889], .c 5, .c 3, .c 7,
  .c 17, .c 3, .c 5, .c 19, .c 3, .c 103, .c 7, .c 3, .c 59, .p pv2 [pv2,pv3,pv17,pv71,pv409],
  .c 3, .p pv5 [pv2,pv1480991], .c 5, .c 3, .p pv2 [pv2,pv31,pv23887],
  .p pv3 [pv2,pv3,pv5,pv32911], .c 3, .c 5, .p pv2 [pv2,pv3,pv246833], .c 3, .c 7, .c 11, .c 3,
  .p pv5 [pv2,pv1481003], .c 23, .c 3, .p pv2 [pv2,pv17,pv43,pv1013], .c 5, .c 3, .c 31, .c 83,
  .c 3, .c 5, .c 101, .c 3, .c 29, .p pv29 [pv2,pv3,pv23,pv2683], .c 3, .c 13,
  .p pv3 [pv2,pv3,pv61,pv8093], .c 3, .c 7, .c 5, .c 3, .c 71, .c 251, .c 3, .c 5, .c 7, .c 3,
  .c 641, .c 13, .c 3, .p pv2 [pv2,pv1481033], .c 11, .c 3, .p pv3 [pv2,pv37,pv10007], .c 5, .c 3,
  .c 167, .c 19, .c 3, .c 5, .c 997, .c 3, .c 11, .p pv2 [pv2,pv3,pv7,pv179,pv197], .c 3, .c 17,
  .c 7, .c 3, .p pv5 [pv2,pv11,pv13,pv10357], .c 5, .c 3, .c 37, .p pv3 [pv2,pv3,pv5,pv98737],
  .c 3, .c 5, .c 53, .c 3, .c 73, .c 227, .c 3, .c 7, .c 233, .c 3, .p pv2 [pv2,pv740533], .c 5,
  .c 3, .c 1109, .c 7, .c 3, .c 5, .c 23, .c 3, .p pv11 [pv2,pv5,pv59243], .c 433, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv493693], .c 3, .p pv2 [pv2,pv7,pv211583], .c 5, .c 3, .c 7, .c 683, .c 3,
  .c 5, .c 103,
]
private theorem h0361c18 : checkBlock 2961923 128 b0361c18 = true := by
  decide +kernel

private def b0361c19 : List Row := [
  .c 3, .c 467, .c 7, .c 3, .c 83, .c 1039, .c 3, .c 13, .c 5, .c 3, .c 17, .c 11, .c 3, .c 5,
  .p pv31 [pv2,pv3,pv13,pv12659], .c 3, .c 7, .c 59, .c 3, .c 617, .c 13, .c 3, .c 11, .c 5, .c 3,
  .c 101, .p pv19 [pv2,pv3,pv5,pv293,pv337], .c 3, .c 5, .p pv2 [pv2,pv3,pv31,pv7963], .c 3,
  .p pv3 [pv2,pv5,pv9257], .c 307, .c 3, .p pv5 [pv2,pv7,pv167,pv181], .p pv7 [pv2,pv3,pv123427],
  .c 3, .c 7, .c 5, .c 3, .c 1667, .p pv17 [pv2,pv3,pv5,pv7,pv2351], .c 3, .c 5, .c 7, .c 3,
  .c 13, .p pv5 [pv2,pv3,pv59,pv523], .c 3, .p pv2 [pv2,pv53,pv89,pv157], .c 173, .c 3, .c 97,
  .c 5, .c 3, .c 11, .c 41, .c 3, .c 5, .c 13, .c 3, .c 17, .c 131, .c 3, .p pv2 [pv2,pv1481153],
  .c 7, .c 3, .c 43, .c 5, .c 3, .p pv29 [pv2,pv17,pv151,pv577], .c 29, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv493721], .c 3, .c 23, .c 11, .c 3, .c 7, .c 347, .c 3, .c 61, .c 5, .c 3,
  .c 13, .c 7, .c 3, .c 5, .c 193, .c 3, .p pv7 [pv2,pv5,pv31,pv2389], .c 47, .c 3,
  .p pv5 [pv2,pv11,pv19,pv373], .c 17, .c 3, .c 41, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv97,pv509], .c 3, .c 5, .c 409, .c 3, .c 31, .c 7, .c 3,
  .p pv2 [pv2,pv740599], .c 11, .c 3, .c 17, .c 5, .c 3, .p pv3 [pv2,pv29,pv113],
  .p pv2 [pv2,pv3,pv5,pv11,pv47,pv191], .c 3, .c 5, .p pv5 [pv2,pv3,pv61717], .c 3, .c 7, .c 19,
  .c 3, .c 13, .p pv2 [pv2,pv3,pv7,pv35267], .c 3, .c 157,
]
private theorem h0361c19 : checkBlock 2962179 128 b0361c19 = true := by
  decide +kernel

private def b0361c20 : List Row := [
  .c 5, .c 3, .c 257, .p pv19 [pv2,pv3,pv5,pv13,pv211], .c 3, .c 5, .c 1283, .c 3,
  .p pv2 [pv2,pv5,pv179,pv331], .c 13, .c 3, .c 47, .p pv2 [pv2,pv3,pv164581], .c 3, .c 7, .c 5,
  .c 3, .c 23, .c 17, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv19,pv1949],
  .p pv2 [pv2,pv3,pv493747], .c 3, .c 11, .p pv11 [pv2,pv3,pv17,pv53,pv137], .c 3,
  .p pv2 [pv2,pv13,pv23,pv2477], .c 5, .c 3, .c 19, .p pv7 [pv2,pv3,pv5,pv79], .c 3, .c 5, .c 139,
  .c 3, .c 109, .c 199, .c 3, .p pv2 [pv2,pv37,pv541], .c 7, .c 3, .c 293, .c 5, .c 3, .c 127,
  .c 11, .c 3, .c 5, .c 19, .c 3, .c 53, .c 89, .c 3, .c 7, .p pv2 [pv2,pv3,pv27431], .c 3, .c 11,
  .c 5, .c 3, .c 73, .c 7, .c 3, .c 5, .c 59, .c 3, .c 43, .c 17, .c 3, .c 31, .c 79, .c 3, .c 13,
  .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv17,pv37,pv157], .c 3, .c 5, .c 11, .c 3, .c 191, .c 7,
  .c 3, .c 17, .c 13, .c 3, .c 19, .c 5, .c 3, .c 11, .p pv29 [pv2,pv3,pv5,pv109,pv151], .c 3,
  .c 5, .c 37, .c 3, .c 7, .c 101, .c 3, .p pv2 [pv2,pv740659], .c 31, .c 3, .c 379, .c 5, .c 3,
  .c 857, .c 19, .c 3, .c 5, .c 43, .c 3, .c 13, .c 11, .c 3, .c 1453, .c 29, .c 3, .c 7, .c 5,
  .c 3, .c 863, .p pv17 [pv2,pv3,pv5,pv7,pv3527], .c 3, .c 5, .c 7, .c 3,
]
private theorem h0361c20 : checkBlock 2962435 128 b0361c20 = true := by
  decide +kernel

private def b0361c21 : List Row := [
  .c 859, .p pv5 [pv2,pv3,pv17,pv47,pv103], .c 3, .p pv3 [pv2,pv11,pv131,pv257], .c 23, .c 3,
  .p pv5 [pv2,pv641,pv2311], .c 5, .c 3, .c 17, .p pv3 [pv2,pv3,pv5,pv10973], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv149,pv1657], .c 3, .c 89, .c 107, .c 3, .c 19, .c 7, .c 3,
  .p pv2 [pv2,pv31,pv23893], .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv11,pv67], .c 3, .c 5,
  .c 113, .c 3, .c 11, .c 53, .c 3, .c 7, .c 71, .c 3, .c 31, .c 5, .c 3, .c 1051, .c 7, .c 3,
  .c 5, .c 17, .c 3, .c 331, .c 41, .c 3, .p pv2 [pv2,pv43,pv47,pv733], .c 181, .c 3,
  .p pv3 [pv2,pv7,pv191,pv277], .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv823], .c 3, .c 5, .c 67,
  .c 3, .c 17, .c 7, .c 3, .c 11, .p pv3 [pv2,pv3,pv18289], .c 3, .p pv5 [pv2,pv19,pv77969], .c 5,
  .c 3, .c 43, .c 61, .c 3, .c 5, .c 23, .c 3, .c 7, .c 13, .c 3, .c 461, .c 37, .c 3,
  .p pv2 [pv2,pv740713], .c 5, .c 3, .c 53, .c 11, .c 3, .c 5, .c 1201, .c 3,
  .p pv7 [pv2,pv5,pv296287], .p pv5 [pv2,pv3,pv11,pv29,pv43], .c 3, .c 953, .c 17, .c 3, .c 7,
  .c 5, .c 3, .c 509, .p pv7 [pv2,pv3,pv5,pv7,pv4703], .c 3, .c 5, .c 7, .c 3, .c 29,
  .p pv3 [pv2,pv3,pv493817], .c 3, .p pv2 [pv2,pv23,pv41,pv1571], .c 773, .c 3, .c 17, .c 5, .c 3,
  .c 571, .c 13, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv17,pv29,pv601],
  .p pv2 [pv2,pv3,pv7,pv5039], .c 3, .c 107, .c 7, .c 3, .p pv5 [pv2,pv1021,pv1451], .c 5,
]
private theorem h0361c21 : checkBlock 2962691 128 b0361c21 = true := by
  decide +kernel

private def b0361c22 : List Row := [
  .c 3, .c 11, .c 449, .c 3, .c 5, .c 769, .c 3, .p pv3 [pv2,pv5,pv7,pv11,pv13,pv37],
  .p pv3 [pv2,pv3,pv97,pv1697], .c 3, .c 7, .c 1307, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv1481489], .c 7, .c 3, .c 5, .c 179, .c 3, .p pv11 [pv2,pv5,pv296299], .c 11, .c 3,
  .c 37, .c 13, .c 3, .c 1321, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5, .c 29, .c 3, .c 23, .c 7,
  .c 3, .p pv2 [pv2,pv11,pv134683], .c 41, .c 3, .c 347, .c 5, .c 3, .c 59,
  .p pv19 [pv2,pv3,pv5,pv6173], .c 3, .c 5, .p pv3 [pv2,pv3,pv29,pv17029], .c 3, .c 7, .c 79,
  .c 3, .c 541, .c 11, .c 3, .c 139, .c 5, .c 3, .c 19, .c 37, .c 3, .c 5, .c 13, .c 3, .c 11,
  .c 17, .c 3, .c 43, .c 131, .c 3, .c 7, .c 5, .c 3, .c 547, .p pv19 [pv2,pv3,pv5,pv7,pv17,pv83],
  .c 3, .c 5, .c 7, .c 3, .c 41, .c 23, .c 3, .c 17, .c 1229, .c 3, .c 1093, .c 5, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv5,pv43,pv2297], .c 3, .c 5, .p pv13 [pv2,pv3,pv11,pv23,pv61], .c 3, .c 827,
  .c 73, .c 3, .c 11, .c 7, .c 3, .c 619, .c 5, .c 3, .c 23, .p pv7 [pv2,pv3,pv5,pv8231], .c 3,
  .c 5, .p pv5 [pv2,pv3,pv31,pv89,pv179], .c 3, .c 313, .c 43, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv164621], .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv457,pv1621], .c 7, .c 3, .c 5,
  .c 31, .c 3, .p pv3 [pv2,pv5,pv463],
]
private theorem h0361c22 : checkBlock 2962947 128 b0361c22 = true := by
  decide +kernel

private def b0361c23 : List Row := [
  .p pv3 [pv2,pv3,pv11,pv17,pv19,pv139], .c 3, .c 13, .c 47, .c 3, .c 11, .c 5, .c 3, .c 7, .c 19,
  .c 3, .c 5, .c 443, .c 3, .p pv13 [pv2,pv5,pv53,pv5591], .c 7, .c 3, .c 1549, .c 101, .c 3,
  .p pv2 [pv2,pv613,pv2417], .c 5, .c 3, .c 29, .c 23, .c 3, .c 5, .c 11, .c 3, .c 7, .c 661,
  .c 3, .p pv2 [pv2,pv83,pv17851], .p pv37 [pv2,pv3,pv7,pv11,pv1069], .c 3,
  .p pv3 [pv2,pv13,pv28493], .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv12347], .c 3, .c 5, .c 17,
  .c 3, .c 127, .c 37, .c 3, .c 19, .p pv3 [pv2,pv3,pv13,pv37991], .c 3, .c 7, .c 5, .c 3, .c 199,
  .c 13, .c 3, .c 5, .c 7, .c 3, .c 17, .c 11, .c 3, .c 71, .c 1223, .c 3,
  .p pv2 [pv2,pv181,pv4093], .c 5, .c 3, .p pv2 [pv2,pv7,pv17,pv12451], .c 139, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv277,pv1783], .c 3, .c 131, .p pv5 [pv2,pv3,pv7,pv31,pv569], .c 3, .c 41, .c 7,
  .c 3, .c 13, .c 5, .c 3, .c 79, .p pv2 [pv2,pv3,pv5,pv98779], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv1583], .c 3, .p pv2 [pv2,pv5,pv7,pv61,pv347], .c 31, .c 3, .c 7, .c 11,
  .c 3, .c 59, .c 5, .c 3, .p pv17 [pv2,pv41,pv71,pv509], .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv17,pv1709], .c 3, .c 11, .c 103, .c 3, .p pv3 [pv2,pv370427], .c 421, .c 3,
  .c 17, .c 5, .c 3, .c 7, .c 43, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv35279], .c 3, .c 13, .c 7,
  .c 3, .c 97, .c 19, .c 3, .p pv3 [pv2,pv29,pv59,pv433], .c 5, .c 3,
]
private theorem h0361c23 : checkBlock 2963203 128 b0361c23 = true := by
  decide +kernel

private def b0361c24 : List Row := [
  .p pv2 [pv2,pv23,pv2801], .c 149, .c 3, .c 5, .c 13, .c 3, .c 7, .p pv5 [pv2,pv3,pv107,pv577],
  .c 3, .c 11, .p pv17 [pv2,pv3,pv7,pv37,pv1907], .c 3, .c 911, .c 5, .c 3, .c 229, .c 17, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv123479], .c 3, .p pv2 [pv2,pv5,pv5927], .c 163, .c 3, .c 31,
  .p pv2 [pv2,pv3,pv17,pv73,pv199], .c 3, .c 7, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 7, .c 3,
  .c 601, .p pv5 [pv2,pv3,pv11,pv13,pv157], .c 3, .c 683, .c 29, .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv53,pv1997], .p pv13 [pv2,pv3,pv5,pv23,pv859], .c 3, .c 5, .c 251, .c 3,
  .c 499, .c 19, .c 3, .p pv5 [pv2,pv1481783], .c 7, .c 3, .c 23, .c 5, .c 3, .c 107, .c 73, .c 3,
  .c 5, .c 11, .c 3, .c 1487, .c 17, .c 3, .c 7, .p pv7 [pv2,pv3,pv11,pv83,pv541], .c 3, .c 41,
  .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv30871], .c 3,
  .p pv3 [pv2,pv5,pv11,pv19,pv709], .c 13, .c 3, .c 17, .c 59, .c 3, .c 317, .c 5, .c 3, .c 7,
  .c 97, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv43,pv547], .c 3, .c 113, .c 7, .c 3,
  .p pv3 [pv2,pv271,pv1367], .c 1559, .c 3, .c 37, .c 5, .c 3, .p pv2 [pv2,pv197,pv3761],
  .p pv3 [pv2,pv3,pv5,pv223,pv443], .c 3, .c 5, .c 19, .c 3, .c 7, .p pv2 [pv2,pv3,pv71,pv773],
  .c 3, .p pv29 [pv2,pv11,pv107,pv1259], .c 43, .c 3, .c 31, .c 5, .c 3, .c 691, .c 13, .c 3,
  .c 5, .c 53, .c 3, .c 23, .c 29,
]
private theorem h0361c24 : checkBlock 2963459 128 b0361c24 = true := by
  decide +kernel

private def b0361c25 : List Row := [
  .c 3, .p pv2 [pv2,pv7,pv15121], .c 11, .c 3, .c 7, .c 5, .c 3, .c 17, .c 937, .c 3, .c 5, .c 7,
  .c 3, .c 11, .p pv3 [pv2,pv3,pv29,pv17033], .c 3, .c 59, .c 167, .c 3, .c 13, .c 5, .c 3,
  .c 149, .c 1103, .c 3, .c 5, .c 41, .c 3, .c 29, .c 47, .c 3, .p pv3 [pv2,pv46309], .c 7, .c 3,
  .c 1579, .c 5, .c 3, .c 89, .c 19, .c 3, .c 5, .c 17, .c 3, .c 1171, .c 23, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv41,pv251], .c 3, .c 53, .c 5, .c 3, .c 109, .c 7, .c 3, .c 5, .c 743, .c 3,
  .c 13, .p pv5 [pv2,pv3,pv123493], .c 3, .p pv2 [pv2,pv173,pv4283], .c 239, .c 3, .c 79, .c 5,
  .c 3, .c 7, .c 11, .c 3, .c 5, .c 13, .c 3, .c 43, .c 7, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv61,pv4049], .c 3, .c 11, .c 5, .c 3, .c 31, .p pv11 [pv2,pv3,pv5,pv8233],
  .c 3, .c 5, .c 29, .c 3, .c 7, .c 223, .c 3, .c 139, .c 17, .c 3, .p pv5 [pv2,pv1481951], .c 5,
  .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv31,pv3187], .c 3, .c 5, .c 11, .c 3, .c 569,
  .p pv3 [pv2,pv3,pv13,pv37,pv79], .c 3, .c 271, .c 61, .c 3, .c 7, .c 5, .c 3, .c 11, .c 23,
  .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv11,pv17,pv317], .p pv5 [pv2,pv3,pv2287], .c 3,
  .p pv2 [pv2,pv740989], .c 37, .c 3, .c 1021, .c 5, .c 3, .c 521,
]
private theorem h0361c25 : checkBlock 2963715 128 b0361c25 = true := by
  decide +kernel

private def b0361c26 : List Row := [
  .p pv3 [pv2,pv3,pv5,pv32933], .c 3, .c 5, .p pv5 [pv2,pv3,pv123499], .c 3, .c 19, .c 11, .c 3,
  .c 13, .c 7, .c 3, .c 233, .c 5, .c 3, .p pv11 [pv2,pv1481999], .c 17, .c 3, .c 5, .c 107, .c 3,
  .p pv7 [pv2,pv5,pv7,pv23,pv263], .c 13, .c 3, .c 7, .c 19, .c 3, .c 409, .c 5, .c 3, .c 97,
  .c 7, .c 3, .c 5, .c 71, .c 3, .p pv3 [pv2,pv5,pv74101], .c 797, .c 3, .c 101, .c 11, .c 3,
  .c 127, .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv70573], .c 3, .c 11, .c 7,
  .c 3, .p pv2 [pv2,pv19,pv43,pv907], .c 23, .c 3, .c 167, .c 5, .c 3, .p pv3 [pv2,pv370511],
  .c 13, .c 3, .c 5, .p pv7 [pv2,pv3,pv31,pv83], .c 3, .c 7, .c 17, .c 3, .c 37, .c 1423, .c 3,
  .c 443, .c 5, .c 3, .c 29, .p pv7 [pv2,pv3,pv5,pv17,pv1453], .c 3, .c 5, .c 31, .c 3, .c 53,
  .c 19, .c 3, .c 11, .c 541, .c 3, .c 7, .c 5, .c 3, .c 47, .p pv7 [pv2,pv3,pv5,pv7,pv941], .c 3,
  .c 5, .c 7, .c 3, .p pv11 [pv2,pv5,pv59,pv157], .p pv2 [pv2,pv3,pv43,pv11489], .c 3, .c 491,
  .c 13, .c 3, .c 61, .c 5, .c 3, .c 71, .c 11, .c 3, .c 5, .c 839, .c 3,
  .p pv17 [pv2,pv5,pv19,pv15601], .c 547, .c 3, .c 751, .c 7, .c 3, .c 11, .c 5, .c 3, .c 19,
  .p pv41 [pv2,pv3,pv5,pv98807], .c 3, .c 5, .c 23, .c 3, .c 13, .c 97, .c 3,
]
private theorem h0361c26 : checkBlock 2963971 128 b0361c26 = true := by
  decide +kernel

private def b0361c27 : List Row := [
  .c 7, .p pv2 [pv2,pv3,pv19,pv13001], .c 3, .p pv3 [pv2,pv370529], .c 5, .c 3, .c 17, .c 7, .c 3,
  .c 5, .c 11, .c 3, .c 31, .p pv2 [pv2,pv3,pv337,pv733], .c 3, .p pv3 [pv2,pv17,pv5449], .c 41,
  .c 3, .c 23, .c 5, .c 3, .c 7, .c 1019, .c 3, .c 5, .p pv23 [pv2,pv3,pv7,pv1307], .c 3, .c 67,
  .c 7, .c 3, .c 193, .p pv41 [pv2,pv3,pv15439], .c 3, .c 29, .c 5, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv5,pv41,pv241], .c 3, .c 5, .c 17, .c 3, .c 7, .c 11, .c 3, .c 79,
  .p pv3 [pv2,pv3,pv7,pv163,pv433], .c 3, .c 19, .c 5, .c 3, .c 37, .p pv3 [pv2,pv3,pv5,pv10979],
  .c 3, .c 5, .c 47, .c 3, .c 17, .c 53, .c 3, .p pv2 [pv2,pv7,pv11,pv19249],
  .p pv7 [pv2,pv3,pv67,pv1229], .c 3, .c 7, .c 5, .c 3, .p pv13 [pv2,pv17,pv87187], .c 19, .c 3,
  .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv296437], .c 1657, .c 3, .c 13, .c 11, .c 3,
  .p pv5 [pv2,pv41,pv36151], .c 5, .c 3, .c 1619, .c 619, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv53,pv59,pv79], .c 3, .c 11, .c 13, .c 3, .c 593, .c 7, .c 3,
  .p pv2 [pv2,pv11,pv89,pv757], .c 5, .c 3, .c 179, .c 347, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv17,pv29063], .c 3, .c 47, .p pv5 [pv2,pv3,pv151,pv409], .c 3, .c 7, .c 929,
  .c 3, .c 17, .c 5, .c 3, .c 53, .c 7, .c 3, .c 5, .c 73, .c 3, .p pv2 [pv2,pv5,pv17,pv8719],
  .c 43, .c 3, .c 11, .c 271, .c 3, .c 109, .c 5, .c 3, .c 7, .c 13,
]
private theorem h0361c27 : checkBlock 2964227 128 b0361c27 = true := by
  decide +kernel

private def b0361c28 : List Row := [
  .c 3, .c 5, .c 1163, .c 3, .p pv2 [pv2,pv5,pv521,pv569], .c 7, .c 3, .p pv3 [pv2,pv29,pv6389],
  .c 31, .c 3, .c 199, .c 5, .c 3, .p pv2 [pv2,pv741127], .c 11, .c 3, .c 5, .c 1483, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv11,pv44917], .c 3, .p pv5 [pv2,pv1482263], .c 701, .c 3, .c 11, .c 5, .c 3,
  .c 23, .c 241, .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv41,pv103], .c 3, .c 19,
  .p pv13 [pv2,pv3,pv101,pv1223], .c 3, .p pv2 [pv2,pv7,pv239,pv443], .c 13, .c 3, .c 7, .c 5,
  .c 3, .c 389, .p pv11 [pv2,pv3,pv5,pv7,pv19,pv743], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv148229], .c 29, .c 3, .c 41, .c 19, .c 3, .c 401, .c 5, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv5,pv61], .c 3, .c 5, .c 1637, .c 3, .c 13, .c 17, .c 3,
  .p pv3 [pv2,pv67,pv5531], .c 7, .c 3, .c 31, .c 5, .c 3, .c 787, .c 23, .c 3, .c 5, .c 13, .c 3,
  .c 29, .c 11, .c 3, .c 7, .c 103, .c 3, .c 101, .c 5, .c 3, .c 1697, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv47,pv10513], .c 3, .p pv13 [pv2,pv5,pv29,pv10223], .c 193, .c 3, .c 23, .c 89,
  .c 3, .c 67, .c 5, .c 3, .c 7, .c 59, .c 3, .c 5, .p pv11 [pv2,pv3,pv7,pv2521], .c 3, .c 173,
  .c 7, .c 3, .c 1063, .c 11, .c 3, .c 47, .c 5, .c 3, .p pv7 [pv2,pv1482359], .c 43, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv164707], .c 3, .c 7, .c 601, .c 3, .p pv3 [pv2,pv37,pv313],
]
private theorem h0361c28 : checkBlock 2964483 128 b0361c28 = true := by
  decide +kernel

private def b0361c29 : List Row := [
  .p pv2 [pv2,pv3,pv7,pv70589], .c 3, .p pv5 [pv2,pv11,pv12251], .c 5, .c 3, .c 17, .c 41, .c 3,
  .c 5, .c 29, .c 3, .c 211, .c 311, .c 3, .c 13, .c 23, .c 3, .c 7, .c 5, .c 3, .c 19, .c 113,
  .c 3, .c 5, .c 7, .c 3, .c 79, .c 13, .c 3, .c 11, .c 263, .c 3, .c 383, .c 5, .c 3, .c 31,
  .p pv2 [pv2,pv3,pv5,pv37,pv2671], .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv53,pv2797],
  .p pv11 [pv2,pv3,pv7,pv73,pv967], .c 3, .p pv2 [pv2,pv1482413], .c 7, .c 3, .c 41, .c 5, .c 3,
  .p pv11 [pv2,pv23,pv64453], .c 11, .c 3, .c 5, .c 37, .c 3, .c 17, .p pv2 [pv2,pv3,pv11,pv7487],
  .c 3, .c 7, .p pv19 [pv2,pv3,pv13,pv38011], .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv17,pv59,pv739], .c 7, .c 3, .c 5, .c 1433, .c 3, .p pv3 [pv2,pv5,pv37061],
  .p pv2 [pv2,pv3,pv494147], .c 3, .c 523, .c 71, .c 3, .c 19, .c 5, .c 3, .c 7, .c 47, .c 3,
  .c 5, .c 11, .c 3, .c 557, .c 7, .c 3, .c 379, .c 17, .c 3, .c 13, .c 5, .c 3, .c 11, .c 19,
  .c 3, .c 5, .c 587, .c 3, .c 7, .p pv3 [pv2,pv3,pv127,pv1297], .c 3, .p pv2 [pv2,pv89,pv16657],
  .c 13, .c 3, .c 17, .c 5, .c 3, .c 1583, .c 181, .c 3, .c 5, .p pv3 [pv2,pv3,pv61,pv8101], .c 3,
  .p pv2 [pv2,pv5,pv17,pv107,pv163], .c 11, .c 3, .c 373, .c 43, .c 3, .c 7, .c 5, .c 3, .c 29,
  .c 283, .c 3,
]
private theorem h0361c29 : checkBlock 2964739 128 b0361c29 = true := by
  decide +kernel

private def b0361c30 : List Row := [
  .c 5, .c 7, .c 3, .c 13, .p pv2 [pv2,pv3,pv494167], .c 3, .c 19, .c 83, .c 3, .c 1283, .c 5,
  .c 3, .p pv2 [pv2,pv7,pv29,pv67,pv109], .c 17, .c 3, .c 5, .c 13, .c 3, .c 71,
  .p pv5 [pv2,pv3,pv7,pv37,pv53], .c 3, .p pv2 [pv2,pv151,pv4909], .c 7, .c 3,
  .p pv2 [pv2,pv47,pv31543], .c 5, .c 3, .c 313, .c 1013, .c 3, .c 5, .c 31, .c 3, .c 11, .c 251,
  .c 3, .c 7, .c 37, .c 3, .p pv3 [pv2,pv11,pv17,pv991], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv6101], .c 3, .c 23, .p pv5 [pv2,pv3,pv13,pv83,pv229], .c 3,
  .p pv3 [pv2,pv97,pv3821], .p pv2 [pv2,pv3,pv331,pv1493], .c 3, .c 421, .c 5, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv5,pv98837], .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv11,pv3209], .c 3, .c 19, .c 7,
  .c 3, .c 11, .c 1663, .c 3, .c 163, .c 5, .c 3, .p pv2 [pv2,pv11,pv53,pv2543],
  .p pv31 [pv2,pv3,pv5,pv17,pv19], .c 3, .c 5, .p pv3 [pv2,pv3,pv494191], .c 3, .c 7,
  .p pv5 [pv2,pv3,pv67,pv461], .c 3, .c 13, .c 19, .c 3, .c 29, .c 5, .c 3, .c 757, .c 11, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv41183], .c 3, .c 31, .c 13, .c 3, .c 73, .p pv7 [pv2,pv3,pv247099],
  .c 3, .c 7, .c 5, .c 3, .p pv23 [pv2,pv1482599], .c 647, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv61,pv4861], .c 89, .c 3, .c 37, .c 67, .c 3, .p pv5 [pv2,pv13,pv59,pv1933],
  .c 5, .c 3, .c 23, .c 223, .c 3, .c 5, .c 11, .c 3, .c 887, .c 31, .c 3,
  .p pv5 [pv2,pv661,pv2243], .c 7,
]
private theorem h0361c30 : checkBlock 2964995 128 b0361c30 = true := by
  decide +kernel

private def b0361c31 : List Row := [
  .c 3, .p pv2 [pv2,pv23,pv167,pv193], .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 103, .c 3, .c 61,
  .c 19, .c 3, .c 7, .c 29, .c 3, .c 1721, .c 5, .c 3, .p pv3 [pv2,pv370661], .c 7, .c 3, .c 5,
  .c 53, .c 3, .c 227, .c 11, .c 3, .p pv2 [pv2,pv1039,pv1427], .c 1093, .c 3, .c 13, .c 5, .c 3,
  .c 7, .c 23, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv19,pv15607], .c 7, .c 3, .c 29, .c 13,
  .c 3, .c 487, .c 5, .c 3, .c 19, .p pv3 [pv2,pv3,pv5,pv53,pv373], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv27457], .c 3, .c 7, .p pv5 [pv2,pv3,pv313,pv1579], .c 3, .c 23, .c 11, .c 3,
  .p pv2 [pv2,pv741343], .c 5, .c 3, .p pv2 [pv2,pv13,pv17,pv6709],
  .p pv2 [pv2,pv3,pv5,pv11,pv4493], .c 3, .c 5, .c 19, .c 3, .c 11, .c 61, .c 3,
  .p pv2 [pv2,pv7,pv105907], .c 59, .c 3, .c 7, .c 5, .c 3, .c 43, .p pv2 [pv2,pv3,pv5,pv7,pv523],
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv67,pv2213], .c 79, .c 3, .c 1291, .c 17, .c 3, .c 727,
  .c 5, .c 3, .c 37, .c 197, .c 3, .c 5, .c 131, .c 3, .c 1009, .c 29, .c 3, .c 11, .c 7, .c 3,
  .c 17, .c 5, .c 3, .c 13, .p pv23 [pv2,pv3,pv5,pv98849], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv37,pv6679], .c 3, .p pv11 [pv2,pv5,pv7,pv17,pv89],
  .p pv11 [pv2,pv3,pv13,pv19,pv23,pv29], .c 3, .c 7, .c 41, .c 3, .c 179, .c 5, .c 3,
  .p pv2 [pv2,pv199,pv7451], .c 7, .c 3, .c 5,
]
private theorem h0361c31 : checkBlock 2965251 128 b0361c31 = true := by
  decide +kernel

def rows0361 : List Row :=
  b0361c00 ++ b0361c01 ++ b0361c02 ++ b0361c03 ++ b0361c04 ++ b0361c05 ++ b0361c06 ++ b0361c07 ++
  b0361c08 ++ b0361c09 ++ b0361c10 ++ b0361c11 ++ b0361c12 ++ b0361c13 ++ b0361c14 ++ b0361c15 ++
  b0361c16 ++ b0361c17 ++ b0361c18 ++ b0361c19 ++ b0361c20 ++ b0361c21 ++ b0361c22 ++ b0361c23 ++
  b0361c24 ++ b0361c25 ++ b0361c26 ++ b0361c27 ++ b0361c28 ++ b0361c29 ++ b0361c30 ++ b0361c31

theorem checked0361 : checkBlock 2957315 4096 rows0361 = true :=
  checkBlock_append h0361c00 (
    checkBlock_append h0361c01 (
    checkBlock_append h0361c02 (
    checkBlock_append h0361c03 (
    checkBlock_append h0361c04 (
    checkBlock_append h0361c05 (
    checkBlock_append h0361c06 (
    checkBlock_append h0361c07 (
    checkBlock_append h0361c08 (
    checkBlock_append h0361c09 (
    checkBlock_append h0361c10 (
    checkBlock_append h0361c11 (
    checkBlock_append h0361c12 (
    checkBlock_append h0361c13 (
    checkBlock_append h0361c14 (
    checkBlock_append h0361c15 (
    checkBlock_append h0361c16 (
    checkBlock_append h0361c17 (
    checkBlock_append h0361c18 (
    checkBlock_append h0361c19 (
    checkBlock_append h0361c20 (
    checkBlock_append h0361c21 (
    checkBlock_append h0361c22 (
    checkBlock_append h0361c23 (
    checkBlock_append h0361c24 (
    checkBlock_append h0361c25 (
    checkBlock_append h0361c26 (
    checkBlock_append h0361c27 (
    checkBlock_append h0361c28 (
    checkBlock_append h0361c29 (
    checkBlock_append h0361c30 (
    h0361c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
