/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks02/Block0161
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks02/Block0161.checked0161
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table020
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table024
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table028
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table036
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table047
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table048
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table070
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table122
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table123

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0161c00 : List Row := [
  .c 5, .c 3, .c 7, .c 461, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv31,pv1013], .c 3,
  .p pv11 [pv2,pv5,pv131893], .c 7, .c 3, .p pv3 [pv2,pv113,pv1459], .c 37, .c 3,
  .p pv5 [pv2,pv19,pv61,pv569], .c 5, .c 3, .c 29, .c 311, .c 3, .c 5, .c 31, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv17,pv67,pv193], .c 3, .c 13, .c 887, .c 3, .p pv2 [pv2,pv199,pv1657], .c 5,
  .c 3, .c 17, .c 23, .c 3, .c 5, .p pv2 [pv2,pv3,pv73277], .c 3, .p pv7 [pv2,pv5,pv131899],
  .c 13, .c 3, .p pv2 [pv2,pv7,pv17,pv163], .c 11, .c 3, .c 7, .c 5, .c 3, .c 109, .c 41, .c 3,
  .c 5, .c 7, .c 3, .c 11, .p pv3 [pv2,pv3,pv127,pv577], .c 3, .c 23, .c 67, .c 3,
  .p pv3 [pv2,pv11,pv13,pv1153], .c 5, .c 3, .c 131, .c 239, .c 3, .c 5, .c 17, .c 3, .c 179,
  .p pv2 [pv2,pv3,pv7,pv41,pv383], .c 3, .p pv3 [pv2,pv19,pv4339], .c 7, .c 3, .c 59, .c 5, .c 3,
  .c 89, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv3331], .c 3, .c 17, .p pv3 [pv2,pv3,pv219847],
  .c 3, .c 7, .c 619, .c 3, .c 41, .c 5, .c 3, .c 389, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv219851], .c 3, .c 43, .c 19, .c 3, .c 53, .c 23, .c 3, .c 13, .c 5, .c 3,
  .c 7, .c 11, .c 3, .c 5, .p pv17 [pv2,pv3,pv7,pv13,pv151], .c 3, .c 1033, .c 7, .c 3,
  .p pv2 [pv2,pv617,pv1069], .c 13, .c 3, .c 11, .c 5, .c 3, .c 163, .c 37, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv17,pv479], .c 3,
]
private theorem h0161c00 : checkBlock 1318915 128 b0161c00 = true := by
  decide +kernel

private def b0161c01 : List Row := [
  .c 7, .c 137, .c 3, .c 1117, .c 307, .c 3, .c 17, .c 5, .c 3, .c 19,
  .p pv3 [pv2,pv3,pv5,pv43973], .c 3, .c 5, .c 11, .c 3, .c 13, .c 107, .c 3,
  .p pv5 [pv2,pv7,pv94229], .p pv7 [pv2,pv3,pv11,pv19,pv263], .c 3, .c 7, .c 5, .c 3, .c 11,
  .c 79, .c 3, .c 5, .c 7, .c 3, .c 397, .c 647, .c 3, .c 191, .c 29, .c 3, .c 47, .c 5, .c 3,
  .c 139, .c 17, .c 3, .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv65963], .c 11, .c 3, .c 31, .c 7,
  .c 3, .p pv3 [pv2,pv37,pv4457], .c 5, .c 3, .c 13, .p pv7 [pv2,pv3,pv5,pv23,pv239], .c 3, .c 5,
  .c 151, .c 3, .c 431, .p pv2 [pv2,pv3,pv13,pv2819], .c 3, .c 7, .c 59, .c 3, .c 19, .c 5, .c 3,
  .c 37, .c 7, .c 3, .c 5, .c 491, .c 3, .p pv3 [pv2,pv5,pv32983],
  .p pv3 [pv2,pv3,pv19,pv71,pv163], .c 3, .c 103, .c 11, .c 3, .p pv3 [pv2,pv7,pv47119], .c 5,
  .c 3, .c 7, .c 19, .c 3, .c 5, .c 821, .c 3, .c 11, .c 7, .c 3, .c 13, .c 457, .c 3, .c 101,
  .c 5, .c 3, .c 43, .p pv3 [pv2,pv3,pv5,pv13,pv17,pv199], .c 3, .c 5, .p pv7 [pv2,pv3,pv27487],
  .c 3, .c 7, .c 13, .c 3, .c 17, .p pv13 [pv2,pv3,pv7,pv113,pv139], .c 3, .c 71, .c 5, .c 3,
  .p pv7 [pv2,pv19,pv34721], .p pv7 [pv2,pv3,pv5,pv733], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv19991], .c 3, .p pv2 [pv2,pv5,pv131941], .c 29, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv23,pv3187], .c 3, .c 7, .c 5,
]
private theorem h0161c01 : checkBlock 1319171 128 b0161c01 = true := by
  decide +kernel

private def b0161c02 : List Row := [
  .c 3, .p pv3 [pv2,pv11,pv157,pv191], .c 47, .c 3, .c 5, .c 7, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv29,pv7583], .c 3, .c 137, .c 709, .c 3, .c 31, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv79,pv1193], .c 11, .c 3, .c 5, .c 167, .c 3, .c 29, .c 677, .c 3,
  .p pv2 [pv2,pv59,pv5591], .c 7, .c 3, .c 11, .c 5, .c 3, .c 17, .c 61, .c 3, .c 5, .c 811, .c 3,
  .c 113, .c 41, .c 3, .c 7, .p pv2 [pv2,pv3,pv36653], .c 3, .c 13, .c 5, .c 3, .c 239, .c 7,
  .c 3, .c 5, .c 11, .c 3, .c 19, .c 23, .c 3, .c 79, .c 13, .c 3, .p pv5 [pv2,pv7,pv94253], .c 5,
  .c 3, .c 7, .c 227, .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv11,pv2999], .c 7, .c 3,
  .p pv5 [pv2,pv659783], .c 19, .c 3, .c 311, .c 5, .c 3, .c 23, .c 571, .c 3, .c 5, .c 29, .c 3,
  .c 7, .c 11, .c 3, .c 599, .c 577, .c 3, .c 89, .c 5, .c 3, .p pv3 [pv2,pv17,pv31,pv313],
  .c 449, .c 3, .c 5, .c 13, .c 3, .c 73, .p pv7 [pv2,pv3,pv219937], .c 3, .c 43, .c 283, .c 3,
  .c 7, .c 5, .c 3, .c 31, .c 347, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv26393], .c 59, .c 3,
  .c 127, .c 11, .c 3, .c 109, .c 5, .c 3, .c 13, .c 23, .c 3, .c 5, .c 71, .c 3, .c 11,
]
private theorem h0161c02 : checkBlock 1319427 128 b0161c02 = true := by
  decide +kernel

private def b0161c03 : List Row := [
  .c 19, .c 3, .p pv5 [pv2,pv659843], .c 7, .c 3, .c 17, .c 5, .c 3, .c 67, .c 31, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv24439], .c 3, .p pv7 [pv2,pv5,pv7,pv17,pv1109], .c 43, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv219953], .c 3, .p pv2 [pv2,pv431,pv1531], .c 5, .c 3, .p pv3 [pv2,pv82483],
  .c 7, .c 3, .c 5, .p pv17 [pv2,pv3,pv11,pv4999], .c 3, .p pv3 [pv2,pv5,pv19,pv23,pv151],
  .p pv3 [pv2,pv3,pv157,pv467], .c 3, .c 11, .c 41, .c 3, .c 37, .c 5, .c 3, .c 7, .c 17, .c 3,
  .c 5, .c 73, .c 3, .c 59, .c 7, .c 3, .p pv3 [pv2,pv41243], .p pv2 [pv2,pv3,pv17,pv19,pv227],
  .c 3, .c 83, .c 5, .c 3, .c 613, .c 11, .c 3, .c 5, .c 19, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv11,pv19997], .c 3, .c 47, .c 23, .c 3, .c 11, .c 5, .c 3, .c 29,
  .p pv2 [pv2,pv3,pv5,pv21997], .c 3, .c 5, .c 37, .c 3, .c 41, .c 67, .c 3, .c 509,
  .p pv17 [pv2,pv3,pv13,pv16921], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv29,pv5689], .c 13, .c 3,
  .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv65993], .c 17, .c 3, .c 353, .p pv2 [pv2,pv3,pv11,pv101],
  .c 3, .c 19, .c 5, .c 3, .c 11, .c 109, .c 3, .c 5, .c 31, .c 3, .c 151,
  .p pv23 [pv2,pv3,pv7,pv19,pv827], .c 3, .c 17, .c 7, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv329977], .c 19, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv8461], .c 3, .c 313, .c 11,
  .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv79,pv4177], .c 5, .c 3,
]
private theorem h0161c03 : checkBlock 1319683 128 b0161c03 = true := by
  decide +kernel

private def b0161c04 : List Row := [
  .c 1013, .c 7, .c 3, .c 5, .c 23, .c 3, .p pv17 [pv2,pv5,pv26399], .c 113, .c 3, .c 241, .c 89,
  .c 3, .p pv2 [pv2,pv7,pv13469], .c 5, .c 3, .c 7, .c 43, .c 3, .c 5, .c 659, .c 3, .c 13, .c 7,
  .c 3, .c 19, .c 11, .c 3, .c 23, .c 5, .c 3, .c 17, .c 191, .c 3, .c 5, .c 13, .c 3, .c 7,
  .c 463, .c 3, .c 661, .p pv2 [pv2,pv3,pv7,pv53,pv593], .c 3, .p pv5 [pv2,pv11,pv29,pv2069],
  .c 5, .c 3, .c 337, .p pv11 [pv2,pv3,pv5,pv4889], .c 3, .c 5, .p pv5 [pv2,pv3,pv41,pv2683],
  .c 3, .c 271, .c 359, .c 3, .c 373, .c 37, .c 3, .c 7, .c 5, .c 3, .c 13,
  .p pv17 [pv2,pv3,pv5,pv7,pv449], .c 3, .c 5, .c 7, .c 3, .c 53, .c 31, .c 3, .c 11, .c 643,
  .c 3, .c 139, .c 5, .c 3, .c 47, .p pv11 [pv2,pv3,pv5,pv79,pv557], .c 3, .c 5, .c 197, .c 3,
  .c 17, .c 71, .c 3, .p pv2 [pv2,pv660053], .c 7, .c 3, .p pv3 [pv2,pv82507], .c 5, .c 3,
  .p pv11 [pv2,pv17,pv41,pv947], .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv220021], .c 3, .c 23,
  .c 733, .c 3, .c 7, .c 19, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv330037], .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv36671], .c 3, .p pv3 [pv2,pv5,pv37,pv223], .c 13, .c 3, .c 29, .c 17, .c 3,
  .p pv3 [pv2,pv7,pv47149], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv22003], .c 3, .c 5, .c 11,
  .c 3, .p pv11 [pv2,pv5,pv132019], .c 7,
]
private theorem h0161c04 : checkBlock 1319939 128 b0161c04 = true := by
  decide +kernel

private def b0161c05 : List Row := [
  .c 3, .c 31, .p pv11 [pv2,pv3,pv11,pv83,pv241], .c 3, .c 17, .c 5, .c 3, .c 11,
  .p pv29 [pv2,pv3,pv5,pv14669], .c 3, .c 5, .c 433, .c 3, .c 7, .c 23, .c 3, .c 211, .c 43, .c 3,
  .c 937, .c 5, .c 3, .c 683, .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv23,pv1063], .c 3,
  .p pv7 [pv2,pv5,pv5281], .c 11, .c 3, .c 487, .c 31, .c 3, .c 7, .c 5, .c 3, .c 23, .c 17, .c 3,
  .c 5, .c 7, .c 3, .c 83, .c 29, .c 3, .p pv5 [pv2,pv11,pv60013], .c 149, .c 3, .c 13, .c 5,
  .c 3, .c 491, .p pv7 [pv2,pv3,pv5,pv163], .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv16927], .c 3,
  .c 743, .c 193, .c 3, .c 109, .c 7, .c 3, .c 41, .c 5, .c 3, .c 19,
  .p pv23 [pv2,pv3,pv5,pv11,pv4001], .c 3, .c 5, .p pv5 [pv2,pv3,pv53,pv173], .c 3, .c 11,
  .p pv3 [pv2,pv3,pv220057], .c 3, .c 7, .c 131, .c 3, .p pv5 [pv2,pv11,pv31], .c 5, .c 3, .c 331,
  .c 7, .c 3, .c 5, .c 19, .c 3, .c 13, .c 17, .c 3, .p pv3 [pv2,pv165047],
  .p pv2 [pv2,pv3,pv220063], .c 3, .c 31, .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv17,pv863], .c 3,
  .c 5, .c 13, .c 3, .c 43, .c 7, .c 3, .c 11, .p pv29 [pv2,pv3,pv6113], .c 3,
  .p pv2 [pv2,pv330103], .c 5, .c 3, .c 37, .p pv2 [pv2,pv3,pv5,pv59,pv373], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv109,pv673], .c 3, .c 7, .p pv5 [pv2,pv3,pv27509], .c 3,
  .p pv2 [pv2,pv13,pv67,pv379], .c 241, .c 3, .c 19, .c 5, .c 3, .c 13,
]
private theorem h0161c05 : checkBlock 1320195 128 b0161c05 = true := by
  decide +kernel

private def b0161c06 : List Row := [
  .c 11, .c 3, .c 5, .c 29, .c 3, .c 97, .c 163, .c 3, .c 61, .c 167, .c 3, .c 7, .c 5, .c 3,
  .c 59, .c 19, .c 3, .c 5, .c 7, .c 3, .c 197, .c 37, .c 3, .c 73, .c 23, .c 3, .c 67, .c 5,
  .c 3, .c 17, .c 251, .c 3, .c 5, .c 11, .c 3, .c 269, .c 263, .c 3, .c 13, .c 7, .c 3,
  .p pv2 [pv2,pv330133], .c 5, .c 3, .c 11, .p pv11 [pv2,pv3,pv5,pv13,pv1693], .c 3, .c 5, .c 313,
  .c 3, .c 293, .c 13, .c 3, .c 7, .c 47, .c 3, .c 103, .c 5, .c 3, .c 31, .c 7, .c 3, .c 5,
  .c 17, .c 3, .c 541, .c 11, .c 3, .c 149, .c 61, .c 3, .c 739, .c 5, .c 3, .c 7, .c 53, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv7,pv47,pv223], .c 3, .c 17, .c 7, .c 3, .p pv3 [pv2,pv11,pv43,pv349],
  .c 881, .c 3, .p pv5 [pv2,pv317,pv2083], .c 5, .c 3, .c 797, .c 13, .c 3, .c 5, .c 23, .c 3,
  .c 7, .c 73, .c 3, .c 557, .c 11, .c 3, .c 47, .c 5, .c 3, .c 43, .c 409, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv103,pv2137], .c 3, .c 11, .c 127, .c 3, .c 421, .c 17, .c 3, .c 7, .c 5, .c 3,
  .c 29, .c 1049, .c 3, .c 5, .c 7, .c 3, .c 107, .c 337, .c 3,
]
private theorem h0161c06 : checkBlock 1320451 128 b0161c06 = true := by
  decide +kernel

private def b0161c07 : List Row := [
  .c 53, .c 13, .c 3, .c 17, .c 5, .c 3, .c 827, .p pv7 [pv2,pv3,pv5,pv5503], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv20011], .c 3, .p pv2 [pv2,pv5,pv17,pv457], .c 41, .c 3, .c 11, .c 7,
  .c 3, .c 887, .c 5, .c 3, .p pv2 [pv2,pv11,pv13,pv2309], .p pv3 [pv2,pv3,pv5,pv587], .c 3, .c 5,
  .c 181, .c 3, .c 13, .c 199, .c 3, .c 7, .c 103, .c 3, .p pv2 [pv2,pv61,pv5413], .c 5, .c 3,
  .c 83, .c 7, .c 3, .c 5, .c 13, .c 3, .p pv17 [pv2,pv5,pv269,pv491], .c 373, .c 3, .c 151,
  .p pv3 [pv2,pv3,pv17,pv23,pv563], .c 3, .c 11, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv44027],
  .c 3, .c 5, .c 31, .c 3, .c 23, .c 7, .c 3, .c 677, .c 223, .c 3, .c 59, .c 5, .c 3, .c 13,
  .c 47, .c 3, .c 5, .c 11, .c 3, .c 7, .c 499, .c 3, .c 113, .p pv2 [pv2,pv3,pv7,pv11,pv953],
  .c 3, .c 29, .c 5, .c 3, .c 11, .p pv13 [pv2,pv3,pv5,pv44029], .c 3, .c 5, .c 233, .c 3,
  .p pv23 [pv2,pv5,pv11,pv19,pv79], .c 17, .c 3, .p pv5 [pv2,pv7,pv94349],
  .p pv7 [pv2,pv3,pv47,pv1171], .c 3, .c 7, .c 5, .c 3, .c 19,
  .p pv11 [pv2,pv3,pv5,pv7,pv17,pv37], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv31,pv4261],
  .c 11, .c 3, .c 13, .c 53, .c 3, .p pv2 [pv2,pv683,pv967], .c 5, .c 3, .p pv3 [pv2,pv7,pv5897],
  .p pv2 [pv2,pv3,pv5,pv13,pv1129], .c 3, .c 5, .c 19, .c 3, .c 31, .c 13, .c 3,
  .p pv2 [pv2,pv11,pv97,pv619], .c 7, .c 3, .c 239, .c 5, .c 3, .c 23, .p pv13 [pv2,pv3,pv5,pv43],
]
private theorem h0161c07 : checkBlock 1320707 128 b0161c07 = true := by
  decide +kernel

private def b0161c08 : List Row := [
  .c 3, .c 5, .c 383, .c 3, .c 109, .p pv2 [pv2,pv3,pv31,pv53,pv67], .c 3, .c 7, .c 11, .c 3,
  .p pv11 [pv2,pv13,pv23,pv47], .c 5, .c 3, .c 821, .c 7, .c 3, .c 5, .c 617, .c 3, .c 11, .c 31,
  .c 3, .p pv5 [pv2,pv660503], .c 751, .c 3, .c 19, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 89,
  .c 3, .p pv17 [pv2,pv5,pv132103], .c 7, .c 3, .c 29, .c 67, .c 3, .c 97, .c 5, .c 3, .c 263,
  .c 19, .c 3, .c 5, .c 773, .c 3, .c 7, .p pv7 [pv2,pv3,pv220177], .c 3, .c 11, .c 59, .c 3,
  .c 13, .c 5, .c 3, .p pv7 [pv2,pv11,pv53,pv103], .c 73, .c 3, .c 5, .c 17, .c 3, .c 137,
  .p pv2 [pv2,pv3,pv36697], .c 3, .c 23, .c 13, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv19,pv17383],
  .c 11, .c 3, .c 5, .c 7, .c 3, .c 17, .c 47, .c 3, .c 19, .c 107, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv13,pv17,pv61], .p pv2 [pv2,pv3,pv5,pv97,pv227], .c 3, .c 5, .c 191, .c 3,
  .c 13, .c 29, .c 3, .p pv2 [pv2,pv330289], .c 7, .c 3, .p pv2 [pv2,pv241,pv2741], .c 5, .c 3,
  .p pv3 [pv2,pv71,pv1163], .p pv3 [pv2,pv3,pv5,pv47,pv937], .c 3, .c 5, .c 11, .c 3, .c 101,
  .c 149, .c 3, .c 7, .c 17, .c 3, .p pv3 [pv2,pv239,pv691], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5,
  .c 1033, .c 3, .c 29, .p pv2 [pv2,pv3,pv23,pv4787], .c 3, .c 47,
]
private theorem h0161c08 : checkBlock 1320963 128 b0161c08 = true := by
  decide +kernel

private def b0161c09 : List Row := [
  .p pv2 [pv2,pv3,pv43,pv569], .c 3, .c 17, .c 5, .c 3, .c 7, .c 487, .c 3, .c 5, .c 53, .c 3,
  .c 19, .c 7, .c 3, .p pv5 [pv2,pv59,pv11197], .p pv11 [pv2,pv3,pv13763], .c 3, .c 863, .c 5,
  .c 3, .p pv2 [pv2,pv23,pv28723], .c 43, .c 3, .c 5, .p pv2 [pv2,pv3,pv41,pv131], .c 3, .c 7,
  .p pv5 [pv2,pv3,pv2039], .c 3, .c 83, .c 19, .c 3, .p pv2 [pv2,pv31,pv101,pv211], .c 5, .c 3,
  .p pv3 [pv2,pv165161], .c 17, .c 3, .c 5, .c 853, .c 3, .p pv2 [pv2,pv5,pv73,pv181],
  .p pv11 [pv2,pv3,pv220217], .c 3, .c 13, .c 11, .c 3, .c 7, .c 5, .c 3, .p pv17 [pv2,pv660659],
  .c 61, .c 3, .c 5, .c 7, .c 3, .c 11, .c 13, .c 3, .c 587, .c 661, .c 3, .c 53, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv41,pv1151], .p pv3 [pv2,pv3,pv5,pv23,pv383], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv29,pv3797], .c 3, .c 563, .p pv2 [pv2,pv3,pv7,pv10487], .c 3, .c 227, .c 7,
  .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv179,pv3691], .c 37, .c 3, .c 5, .c 103, .c 3,
  .p pv23 [pv2,pv5,pv7,pv43,pv439], .c 17, .c 3, .c 7, .p pv3 [pv2,pv3,pv13,pv5647], .c 3, .c 241,
  .c 5, .c 3, .p pv7 [pv2,pv11,pv1877], .c 7, .c 3, .c 5, .p pv13 [pv2,pv3,pv18353], .c 3,
  .p pv2 [pv2,pv5,pv66071], .c 59, .c 3, .c 17, .p pv2 [pv2,pv3,pv110119], .c 3, .c 43, .c 5,
  .c 3, .c 7, .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv73,pv431], .c 3,
  .p pv2 [pv2,pv5,pv13,pv19,pv107], .c 7, .c 3, .p pv3 [pv2,pv82591], .p pv2 [pv2,pv3,pv220243],
  .c 3, .c 11, .c 5, .c 3, .c 19, .c 41, .c 3,
]
private theorem h0161c09 : checkBlock 1321219 128 b0161c09 = true := by
  decide +kernel

private def b0161c10 : List Row := [
  .c 5, .p pv2 [pv2,pv3,pv13,pv43,pv197], .c 3, .c 7, .p pv2 [pv2,pv3,pv59,pv3733], .c 3,
  .p pv5 [pv2,pv313,pv2111], .c 13, .c 3, .c 211, .c 5, .c 3, .c 31, .c 29, .c 3, .c 5, .c 11,
  .c 3, .c 23, .p pv29 [pv2,pv3,pv17,pv41,pv79], .c 3, .p pv2 [pv2,pv7,pv109,pv433], .c 43, .c 3,
  .c 7, .c 5, .c 3, .c 11, .c 971, .c 3, .c 5, .c 7, .c 3, .c 13, .c 281, .c 3, .c 173,
  .p pv13 [pv2,pv3,pv110129], .c 3, .c 41, .c 5, .c 3, .c 29, .c 31, .c 3, .c 5, .c 13, .c 3,
  .p pv2 [pv2,pv5,pv132157], .c 11, .c 3, .p pv3 [pv2,pv233,pv709], .c 7, .c 3, .c 19, .c 5, .c 3,
  .p pv2 [pv2,pv29,pv11393], .c 79, .c 3, .c 5, .c 17, .c 3, .p pv11 [pv2,pv5,pv7,pv59], .c 23,
  .c 3, .c 7, .c 83, .c 3, .c 397, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv23,pv61,pv157], .c 3, .c 17, .p pv5 [pv2,pv3,pv13,pv353], .c 3,
  .p pv2 [pv2,pv330409], .c 11, .c 3, .c 1019, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv11,pv89],
  .c 3, .c 5, .p pv11 [pv2,pv3,pv7,pv7867], .c 3, .c 11, .c 7, .c 3, .c 271,
  .p pv11 [pv2,pv3,pv36713], .c 3, .c 197, .c 5, .c 3, .p pv7 [pv2,pv19,pv34781],
  .p pv31 [pv2,pv3,pv5,pv5507], .c 3, .c 5, .c 47, .c 3, .c 7, .p pv2 [pv2,pv3,pv83,pv1327], .c 3,
  .c 13, .c 17, .c 3, .c 151, .c 5, .c 3, .c 67, .p pv17 [pv2,pv3,pv5,pv13,pv3389], .c 3, .c 5,
  .c 41, .c 3, .c 223, .c 13, .c 3, .c 11, .p pv19 [pv2,pv3,pv1721],
]
private theorem h0161c10 : checkBlock 1321475 128 b0161c10 = true := by
  decide +kernel

private def b0161c11 : List Row := [
  .c 3, .c 7, .c 5, .c 3, .c 89, .c 23, .c 3, .c 5, .c 7, .c 3, .c 37, .p pv5 [pv2,pv3,pv55073],
  .c 3, .p pv2 [pv2,pv330439], .p pv19 [pv2,pv3,pv41,pv199], .c 3, .p pv2 [pv2,pv13,pv29,pv1753],
  .c 5, .c 3, .p pv3 [pv2,pv7,pv23603], .c 11, .c 3, .c 5, .c 43, .c 3, .c 47, .c 157, .c 3,
  .c 23, .c 7, .c 3, .c 11, .c 5, .c 3, .c 41, .c 13, .c 3, .c 5, .c 71, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv12239], .c 3, .c 7, .c 97, .c 3, .p pv5 [pv2,pv389,pv1699], .c 5, .c 3,
  .c 439, .c 7, .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv13,pv31,pv41], .c 67, .c 3,
  .p pv5 [pv2,pv660923], .c 19, .c 3, .c 13, .c 5, .c 3, .c 7, .c 911, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv13,pv269], .c 3, .c 31, .c 7, .c 3, .c 431, .c 13, .c 3, .c 691, .c 5,
  .c 3, .c 967, .p pv3 [pv2,pv3,pv5,pv139,pv317], .c 3, .c 5, .p pv5 [pv2,pv3,pv55079], .c 3,
  .c 7, .c 11, .c 3, .c 29, .c 239, .c 3, .c 137, .c 5, .c 3, .p pv7 [pv2,pv13,pv3911], .c 131,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv53,pv4157], .c 3, .c 13, .c 31, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv271], .c 3, .c 7, .c 5, .c 3, .c 43, .p pv3 [pv2,pv3,pv5,pv7,pv1259], .c 3,
  .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv33049], .c 19, .c 3, .c 929, .c 11, .c 3, .c 37, .c 5, .c 3,
  .c 53, .p pv13 [pv2,pv3,pv5,pv11,pv2003], .c 3, .c 5,
]
private theorem h0161c11 : checkBlock 1321731 128 b0161c11 = true := by
  decide +kernel

private def b0161c12 : List Row := [
  .c 113, .c 3, .c 11, .c 599, .c 3, .p pv2 [pv2,pv13,pv25423], .c 7, .c 3,
  .p pv2 [pv2,pv11,pv60091], .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv37,pv397], .c 3, .c 5,
  .c 23, .c 3, .p pv11 [pv2,pv5,pv7,pv19,pv71], .c 29, .c 3, .c 7, .c 139, .c 3,
  .p pv3 [pv2,pv53,pv1559], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 37, .c 3, .c 337, .c 61, .c 3,
  .c 11, .c 1129, .c 3, .c 23, .c 5, .c 3, .c 7, .c 739, .c 3, .c 5, .c 19, .c 3, .c 29, .c 7,
  .c 3, .c 13, .p pv11 [pv2,pv3,pv31,pv1777], .c 3, .c 163, .c 5, .c 3, .c 547, .c 11, .c 3, .c 5,
  .c 17, .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv383,pv863], .c 31, .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv82633], .c 59, .c 3, .c 5, .p pv5 [pv2,pv3,pv6121], .c 3, .c 17,
  .p pv3 [pv2,pv3,pv220357], .c 3, .p pv2 [pv2,pv7,pv94439], .p pv2 [pv2,pv3,pv239,pv461], .c 3,
  .c 7, .c 5, .c 3, .p pv11 [pv2,pv17,pv37,pv1051], .p pv19 [pv2,pv3,pv5,pv7,pv787], .c 3, .c 5,
  .c 7, .c 3, .p pv7 [pv2,pv5,pv109,pv1213], .p pv2 [pv2,pv3,pv19,pv1933], .c 3,
  .p pv3 [pv2,pv73,pv283], .p pv11 [pv2,pv3,pv11,pv13,pv23,pv67], .c 3, .c 131, .c 5, .c 3, .c 11,
  .c 13, .c 3, .c 5, .c 29, .c 3, .c 23, .p pv2 [pv2,pv3,pv7,pv31481], .c 3, .c 43, .c 7, .c 3,
  .c 113, .c 5, .c 3, .p pv2 [pv2,pv661109], .p pv23 [pv2,pv3,pv5,pv22037], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv17,pv29,pv149], .c 3, .c 617, .c 11, .c 3, .c 7, .c 173, .c 3,
]
private theorem h0161c12 : checkBlock 1321987 128 b0161c12 = true := by
  decide +kernel

private def b0161c13 : List Row := [
  .c 13, .c 5, .c 3, .c 59, .c 7, .c 3, .c 5, .p pv11 [pv2,pv3,pv13,pv163], .c 3,
  .p pv2 [pv2,pv5,pv17,pv3889], .c 491, .c 3, .c 19, .c 13, .c 3, .c 83, .c 5, .c 3, .c 7,
  .p pv19 [pv2,pv3,pv5,pv3673], .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv19,pv1657], .c 3, .c 41, .c 7,
  .c 3, .c 53, .c 11, .c 3, .p pv5 [pv2,pv79,pv8369], .c 5, .c 3, .c 293, .c 17, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv23,pv1597], .c 3, .c 7, .p pv2 [pv2,pv3,pv73,pv3019], .c 3,
  .p pv5 [pv2,pv113,pv5851], .p pv13 [pv2,pv3,pv7,pv17,pv463], .c 3, .p pv2 [pv2,pv11,pv41,pv733],
  .c 5, .c 3, .c 23, .p pv7 [pv2,pv3,pv5,pv22039], .c 3, .c 5, .c 13, .c 3, .c 857, .c 1069, .c 3,
  .p pv3 [pv2,pv7,pv83,pv569], .p pv3 [pv2,pv3,pv61,pv3613], .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv10331], .c 29, .c 3, .c 5, .c 7, .c 3, .c 19, .c 641, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv109,pv337], .c 3, .c 101, .c 5, .c 3, .c 13, .c 97, .c 3, .c 5, .c 397, .c 3,
  .c 157, .c 17, .c 3, .c 37, .c 7, .c 3, .p pv5 [pv2,pv43,pv15377], .c 5, .c 3, .c 29, .c 11,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv193,pv571], .c 3, .c 919, .p pv2 [pv2,pv3,pv11,pv6679], .c 3,
  .c 7, .p pv11 [pv2,pv3,pv27551], .c 3, .c 11, .c 5, .c 3, .c 283, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv220411], .c 3, .p pv13 [pv2,pv5,pv132247], .c 167, .c 3, .c 13, .c 757, .c 3,
  .p pv2 [pv2,pv7,pv94463], .c 5, .c 3, .c 7, .c 31, .c 3, .c 5, .c 11,
]
private theorem h0161c13 : checkBlock 1322243 128 b0161c13 = true := by
  decide +kernel

private def b0161c14 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv23], .c 7, .c 3, .p pv2 [pv2,pv661253], .c 53, .c 3, .c 67, .c 5, .c 3,
  .c 11, .p pv11 [pv2,pv3,pv5,pv103,pv107], .c 3, .c 5, .p pv3 [pv2,pv3,pv220421], .c 3, .c 7,
  .c 19, .c 3, .c 41, .c 79, .c 3, .p pv5 [pv2,pv13,pv50867], .c 5, .c 3, .c 17, .c 43, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv307,pv359], .c 3, .c 823, .c 11, .c 3, .c 181, .c 23, .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv41,pv127], .c 13, .c 3, .c 5, .c 7, .c 3, .p pv29 [pv2,pv5,pv19,pv6961],
  .p pv5 [pv2,pv3,pv23,pv599], .c 3, .p pv2 [pv2,pv11,pv30059], .p pv11 [pv2,pv3,pv137,pv1609],
  .c 3, .c 29, .c 5, .c 3, .c 19, .p pv11 [pv2,pv3,pv5,pv44087], .c 3, .c 5, .c 17, .c 3,
  .p pv3 [pv2,pv5,pv13,pv5087], .c 103, .c 3, .c 47, .c 7, .c 3, .c 13, .c 5, .c 3, .c 37,
  .p pv7 [pv2,pv3,pv5,pv11,pv167], .c 3, .c 5, .c 19, .c 3, .c 11, .c 607, .c 3, .c 7, .c 13,
  .c 3, .c 61, .c 5, .c 3, .p pv2 [pv2,pv17,pv53,pv367], .c 7, .c 3, .c 5, .c 31, .c 3,
  .p pv3 [pv2,pv5,pv43,pv769], .c 311, .c 3, .c 73, .p pv23 [pv2,pv3,pv83], .c 3,
  .p pv2 [pv2,pv7,pv97,pv487], .c 5, .c 3, .c 7, .c 41, .c 3, .c 5, .c 23, .c 3, .c 13, .c 7,
  .c 3, .c 11, .c 17, .c 3, .c 19, .c 5, .c 3, .c 227, .p pv2 [pv2,pv3,pv5,pv23,pv71], .c 3, .c 5,
  .c 13, .c 3, .c 7, .p pv7 [pv2,pv3,pv19,pv41,pv283], .c 3, .p pv2 [pv2,pv661373],
  .p pv11 [pv2,pv3,pv7,pv29,pv181], .c 3, .c 17,
]
private theorem h0161c14 : checkBlock 1322499 128 b0161c14 = true := by
  decide +kernel

private def b0161c15 : List Row := [
  .c 5, .c 3, .c 211, .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv43,pv1709], .c 3, .c 83, .c 1031, .c 3,
  .c 29, .c 257, .c 3, .c 7, .c 5, .c 3, .c 13, .c 463, .c 3, .c 5, .c 7, .c 3, .c 31, .c 619,
  .c 3, .c 89, .c 43, .c 3, .p pv2 [pv2,pv330703], .c 5, .c 3, .c 521, .c 17, .c 3, .c 5, .c 11,
  .c 3, .p pv11 [pv2,pv5,pv132283], .c 73, .c 3, .c 19, .c 7, .c 3, .p pv2 [pv2,pv661421], .c 5,
  .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv8819], .c 3, .c 5, .p pv11 [pv2,pv3,pv19,pv967], .c 3, .c 37,
  .c 31, .c 3, .c 7, .p pv2 [pv2,pv3,pv23,pv4793], .c 3, .p pv3 [pv2,pv17,pv71,pv137], .c 5, .c 3,
  .c 1087, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv97,pv2273], .c 3, .c 23, .c 11, .c 3,
  .p pv3 [pv2,pv89,pv929], .c 401, .c 3, .p pv5 [pv2,pv7,pv13499], .c 5, .c 3, .c 7, .c 151, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv7,pv15749], .c 3, .p pv3 [pv2,pv5,pv33073], .c 7, .c 3,
  .p pv5 [pv2,pv11,pv60133], .c 181, .c 3, .c 53, .c 5, .c 3, .p pv2 [pv2,pv43,pv15383],
  .p pv2 [pv2,pv3,pv5,pv17,pv1297], .c 3, .c 5, .c 41, .c 3, .c 7, .p pv5 [pv2,pv3,pv199,pv277],
  .c 3, .c 17, .c 11, .c 3, .p pv2 [pv2,pv661481], .c 5, .c 3, .c 131, .c 13, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv13781], .c 3, .c 11, .c 23, .c 3, .c 31, .c 19, .c 3, .c 7, .c 5, .c 3,
  .c 101, .p pv37 [pv2,pv3,pv5,pv7], .c 3, .c 5, .c 7, .c 3,
]
private theorem h0161c15 : checkBlock 1322755 128 b0161c15 = true := by
  decide +kernel

private def b0161c16 : List Row := [
  .c 467, .c 79, .c 3, .p pv3 [pv2,pv59,pv2803], .c 997, .c 3, .c 13, .c 5, .c 3, .c 23, .c 373,
  .c 3, .c 5, .c 1109, .c 3, .p pv13 [pv2,pv5,pv8269], .p pv19 [pv2,pv3,pv7,pv17,pv109], .c 3,
  .c 11, .c 7, .c 3, .p pv2 [pv2,pv23,pv73,pv197], .c 5, .c 3, .c 17, .c 577, .c 3, .c 5, .c 29,
  .c 3, .c 163, .p pv5 [pv2,pv3,pv2297], .c 3, .c 7, .p pv3 [pv2,pv3,pv220513], .c 3, .c 37, .c 5,
  .c 3, .c 379, .c 7, .c 3, .c 5, .c 47, .c 3, .c 13, .c 19, .c 3, .p pv2 [pv2,pv661553],
  .p pv2 [pv2,pv3,pv12251], .c 3, .c 11, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 13, .c 3,
  .p pv19 [pv2,pv5,pv132313], .c 7, .c 3, .p pv3 [pv2,pv10337], .p pv2 [pv2,pv3,pv103,pv2141],
  .c 3, .p pv5 [pv2,pv31,pv21341], .c 5, .c 3, .p pv2 [pv2,pv330787], .c 61, .c 3, .c 5, .c 11,
  .c 3, .c 7, .c 89, .c 3, .c 23, .p pv29 [pv2,pv3,pv7,pv11,pv179], .c 3, .c 31, .c 5, .c 3,
  .c 11, .c 211, .c 3, .c 5, .p pv2 [pv2,pv3,pv83,pv2657], .c 3, .c 47, .c 41, .c 3,
  .p pv2 [pv2,pv7,pv43,pv157], .p pv3 [pv2,pv3,pv19,pv53,pv73], .c 3, .c 7, .c 5, .c 3, .c 1051,
  .c 269, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv66161], .c 11, .c 3, .c 71, .c 17, .c 3,
  .p pv3 [pv2,pv41351], .c 5, .c 3, .c 43, .c 29, .c 3, .c 5, .p pv3 [pv2,pv3,pv17,pv12973], .c 3,
  .c 53, .p pv2 [pv2,pv3,pv7,pv59,pv89], .c 3, .c 13, .c 7, .c 3, .c 17, .c 5,
]
private theorem h0161c16 : checkBlock 1323011 128 b0161c16 = true := by
  decide +kernel

private def b0161c17 : List Row := [
  .c 3, .c 83, .c 73, .c 3, .c 5, .c 173, .c 3, .p pv23 [pv2,pv5,pv7,pv17,pv139], .c 13, .c 3,
  .c 7, .c 11, .c 3, .c 19, .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv73517], .c 3,
  .c 11, .c 907, .c 3, .c 67, .p pv3 [pv2,pv3,pv220553], .c 3, .p pv5 [pv2,pv7,pv11,pv13,pv661],
  .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv7877], .c 3, .c 89, .c 7, .c 3,
  .c 179, .p pv7 [pv2,pv3,pv13,pv17,pv499], .c 3, .c 157, .c 5, .c 3, .c 31, .c 13, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv20051], .c 3, .c 7, .p pv11 [pv2,pv3,pv110281], .c 3, .c 11, .c 37, .c 3,
  .c 1091, .c 5, .c 3, .p pv2 [pv2,pv11,pv19,pv1583], .c 229, .c 3, .c 5, .c 23, .c 3, .c 193,
  .c 101, .c 3, .c 19, .p pv7 [pv2,pv3,pv79,pv349], .c 3, .c 7, .c 5, .c 3, .c 139, .c 11, .c 3,
  .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv89,pv1487], .c 17, .c 3, .p pv2 [pv2,pv330859], .c 13, .c 3,
  .c 11, .c 5, .c 3, .c 769, .c 67, .c 3, .c 5, .p pv13 [pv2,pv3,pv61,pv113], .c 3,
  .p pv3 [pv2,pv5,pv66173], .c 53, .c 3, .c 17, .c 7, .c 3, .c 29, .c 5, .c 3,
  .p pv11 [pv2,pv13,pv109,pv467], .c 293, .c 3, .c 5, .c 11, .c 3, .c 13, .c 131, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv11,pv1823], .c 3, .p pv5 [pv2,pv19,pv29,pv1201], .c 5, .c 3, .c 11, .c 7,
  .c 3, .c 5, .c 13, .c 3, .c 19,
]
private theorem h0161c17 : checkBlock 1323267 128 b0161c17 = true := by
  decide +kernel

private def b0161c18 : List Row := [
  .c 251, .c 3, .c 37, .p pv17 [pv2,pv3,pv55147], .c 3, .p pv2 [pv2,pv7,pv47269], .c 5, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv5,pv19,pv43], .c 3, .c 5, .c 59, .c 3, .p pv11 [pv2,pv5,pv103,pv257],
  .c 7, .c 3, .c 137, .c 19, .c 3, .c 73, .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv44119], .c 3,
  .c 5, .p pv5 [pv2,pv3,pv31,pv593], .c 3, .c 7, .c 43, .c 3, .c 109, .c 29, .c 3,
  .p pv3 [pv2,pv165449], .c 5, .c 3, .p pv7 [pv2,pv397,pv1667], .c 37, .c 3, .c 5, .c 31, .c 3,
  .p pv2 [pv2,pv5,pv132361], .c 563, .c 3, .c 883, .c 11, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv330907], .c 653, .c 3, .c 5, .c 7, .c 3, .c 11, .c 197, .c 3, .c 13,
  .p pv11 [pv2,pv3,pv383], .c 3, .c 71, .c 5, .c 3, .p pv2 [pv2,pv7,pv94547], .c 47, .c 3, .c 5,
  .c 157, .c 3, .c 17, .c 13, .c 3, .c 313, .c 7, .c 3, .c 911, .c 5, .c 3,
  .p pv3 [pv2,pv17,pv9733], .p pv2 [pv2,pv3,pv5,pv44123], .c 3, .c 5, .c 89, .c 3, .c 401, .c 709,
  .c 3, .c 7, .c 73, .c 3, .c 523, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv41,pv5381], .c 3, .c 31, .p pv7 [pv2,pv3,pv110311], .c 3,
  .p pv3 [pv2,pv337,pv491], .c 17, .c 3, .p pv5 [pv2,pv7,pv23,pv4111], .c 5, .c 3, .c 7, .c 11,
  .c 3, .c 5, .c 349, .c 3, .c 61, .c 7, .c 3, .c 41, .c 367, .c 3, .c 11, .c 5, .c 3,
]
private theorem h0161c18 : checkBlock 1323523 128 b0161c18 = true := by
  decide +kernel

private def b0161c19 : List Row := [
  .p pv2 [pv2,pv661889], .c 53, .c 3, .c 5, .c 19, .c 3, .c 7, .c 31, .c 3,
  .p pv2 [pv2,pv173,pv1913], .p pv3 [pv2,pv3,pv7,pv43,pv733], .c 3, .c 13, .c 5, .c 3, .c 167,
  .c 23, .c 3, .c 5, .c 11, .c 3, .c 29, .c 37, .c 3, .c 541, .c 13, .c 3, .c 7, .c 5, .c 3,
  .c 11, .c 17, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv11,pv29,pv83], .c 67, .c 3, .c 23,
  .c 103, .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv7,pv13,pv3637], .p pv31 [pv2,pv3,pv5,pv44129],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv110323], .c 3, .c 13, .c 11, .c 3, .c 53, .c 7, .c 3,
  .p pv2 [pv2,pv17,pv19469], .c 5, .c 3, .p pv2 [pv2,pv661949], .c 19, .c 3, .c 5, .c 13, .c 3,
  .c 107, .c 829, .c 3, .c 7, .p pv7 [pv2,pv3,pv24517], .c 3, .p pv2 [pv2,pv661961], .c 5, .c 3,
  .c 457, .c 7, .c 3, .c 5, .c 29, .c 3, .p pv2 [pv2,pv5,pv53,pv1249], .c 17, .c 3, .c 199, .c 11,
  .c 3, .c 97, .c 5, .c 3, .c 7, .c 79, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv29,pv1087], .c 3, .c 11,
  .c 7, .c 3, .c 17, .c 31, .c 3, .c 661, .c 5, .c 3, .c 557, .c 1013, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv19,pv5807], .c 3, .c 7, .c 601, .c 3, .p pv5 [pv2,pv662003], .c 101, .c 3,
  .c 41, .c 5, .c 3, .c 59, .c 113, .c 3, .c 5, .c 827, .c 3, .c 383, .p pv11 [pv2,pv3,pv431],
]
private theorem h0161c19 : checkBlock 1323779 128 b0161c19 = true := by
  decide +kernel

private def b0161c20 : List Row := [
  .c 3, .c 11, .p pv3 [pv2,pv3,pv220673], .c 3, .c 7, .c 5, .c 3, .c 163,
  .p pv2 [pv2,pv3,pv5,pv7,pv13,pv97], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv239,pv277], .c 13,
  .c 3, .c 293, .p pv2 [pv2,pv3,pv110339], .c 3, .c 337, .c 5, .c 3, .c 17, .c 11, .c 3, .c 5,
  .c 23, .c 3, .c 19, .p pv31 [pv2,pv3,pv7,pv11,pv1433], .c 3, .p pv5 [pv2,pv17,pv1217], .c 7,
  .c 3, .c 11, .c 5, .c 3, .c 317, .c 29, .c 3, .c 5, .p pv5 [pv2,pv3,pv36781], .c 3, .c 67,
  .p pv2 [pv2,pv3,pv220687], .c 3, .c 7, .c 19, .c 3, .c 23, .c 5, .c 3, .c 233, .c 7, .c 3, .c 5,
  .c 11, .c 3, .p pv11 [pv2,pv5,pv71,pv373], .c 487, .c 3, .c 283, .p pv7 [pv2,pv3,pv11,pv20063],
  .c 3, .c 149, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv14713], .c 3, .c 5, .c 41, .c 3, .c 17,
  .c 7, .c 3, .p pv2 [pv2,pv19,pv34847], .c 701, .c 3, .c 13, .c 5, .c 3,
  .p pv7 [pv2,pv17,pv29,pv79], .p pv11 [pv2,pv3,pv5,pv2207], .c 3, .c 5, .c 823, .c 3, .c 7,
  .c 11, .c 3, .p pv3 [pv2,pv165527], .c 13, .c 3, .p pv5 [pv2,pv662111], .c 5, .c 3, .c 127,
  .c 89, .c 3, .c 5, .c 1021, .c 3, .c 109, .c 19, .c 3, .c 113, .c 17, .c 3, .c 7, .c 5, .c 3,
  .c 41, .p pv19 [pv2,pv3,pv5,pv7,pv1051], .c 3, .c 5, .c 7, .c 3, .c 13, .c 821, .c 3, .c 79,
  .c 11, .c 3, .c 17, .c 5, .c 3, .c 31,
]
private theorem h0161c20 : checkBlock 1324035 128 b0161c20 = true := by
  decide +kernel

private def b0161c21 : List Row := [
  .c 887, .c 3, .c 5, .c 13, .c 3, .c 11, .c 313, .c 3, .c 229, .c 7, .c 3,
  .p pv3 [pv2,pv11,pv101,pv149], .c 5, .c 3, .c 19, .c 257, .c 3, .c 5, .p pv5 [pv2,pv3,pv220721],
  .c 3, .c 331, .c 809, .c 3, .c 7, .c 107, .c 3, .c 29, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .c 19, .c 3, .p pv3 [pv2,pv5,pv113,pv293], .c 23, .c 3, .c 11, .p pv11 [pv2,pv3,pv17,pv541],
  .c 3, .c 59, .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv22073], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv23,pv457], .c 3, .p pv17 [pv2,pv5,pv132439], .c 7, .c 3, .c 223, .c 503,
  .c 3, .p pv2 [pv2,pv17,pv38953], .c 5, .c 3, .c 23, .c 11, .c 3, .c 5, .c 53, .c 3, .c 7, .c 41,
  .c 3, .c 13, .p pv2 [pv2,pv3,pv7,pv15767], .c 3, .c 11, .c 5, .c 3, .c 73,
  .p pv7 [pv2,pv3,pv5,pv13,pv283], .c 3, .c 5, .c 211, .c 3, .p pv2 [pv2,pv5,pv26489], .c 13,
  .c 3, .p pv5 [pv2,pv7,pv67,pv353], .c 29, .c 3, .c 7, .c 5, .c 3, .c 631, .c 19, .c 3, .c 5,
  .c 7, .c 3, .p pv3 [pv2,pv5,pv4139], .c 127, .c 3, .c 17, .c 37, .c 3, .c 61, .c 5, .c 3, .c 11,
  .c 23, .c 3, .c 5, .c 47, .c 3, .p pv11 [pv2,pv5,pv11,pv12041], .p pv37 [pv2,pv3,pv7,pv73],
  .c 3, .c 29, .c 7, .c 3, .c 53, .c 5, .c 3, .c 43, .c 13, .c 3, .c 5, .c 31, .c 3, .c 131,
  .c 11, .c 3,
]
private theorem h0161c21 : checkBlock 1324291 128 b0161c21 = true := by
  decide +kernel

private def b0161c22 : List Row := [
  .c 7, .c 311, .c 3, .c 107, .c 5, .c 3, .c 193, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv19,pv1291],
  .c 3, .p pv2 [pv2,pv5,pv13,pv23,pv443], .p pv2 [pv2,pv3,pv17,pv43,pv151], .c 3,
  .p pv3 [pv2,pv11,pv53,pv71], .p pv2 [pv2,pv3,pv257,pv859], .c 3, .c 13, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv67,pv659], .c 3, .c 5, .c 83, .c 3, .c 47, .c 7, .c 3,
  .p pv5 [pv2,pv17,pv38959], .c 11, .c 3, .p pv2 [pv2,pv331153], .c 5, .c 3,
  .p pv2 [pv2,pv662309], .p pv2 [pv2,pv3,pv5,pv11,pv223], .c 3, .c 5, .p pv13 [pv2,pv3,pv220771],
  .c 3, .c 7, .c 29, .c 3, .c 37, .c 23, .c 3, .c 463, .c 5, .c 3, .p pv11 [pv2,pv13,pv47,pv271],
  .p pv2 [pv2,pv3,pv5,pv8831], .c 3, .c 5, .c 17, .c 3, .c 13, .p pv3 [pv2,pv3,pv23,pv29,pv331],
  .c 3, .p pv2 [pv2,pv7,pv1931], .c 41, .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv662339],
  .p pv41 [pv2,pv3,pv5,pv7,pv19,pv83], .c 3, .c 5, .c 7, .c 3, .c 17, .c 613, .c 3, .c 11, .c 19,
  .c 3, .c 1103, .c 5, .c 3, .c 853, .c 37, .c 3, .c 5, .p pv37 [pv2,pv3,pv101,pv1093], .c 3,
  .p pv3 [pv2,pv5,pv29,pv571], .c 31, .c 3, .c 59, .c 7, .c 3, .p pv2 [pv2,pv331183], .c 5, .c 3,
  .c 13, .c 11, .c 3, .c 5, .c 337, .c 3, .c 41, .p pv5 [pv2,pv3,pv11,pv13,pv193], .c 3, .c 7,
  .c 17, .c 3, .c 11, .c 5, .c 3, .c 743, .c 7, .c 3, .c 5, .c 23, .c 3, .c 839,
  .p pv3 [pv2,pv3,pv24533], .c 3, .c 43, .c 47, .c 3, .c 17, .c 5, .c 3, .c 7, .c 1151,
]
private theorem h0161c22 : checkBlock 1324547 128 b0161c22 = true := by
  decide +kernel

private def b0161c23 : List Row := [
  .c 3, .c 5, .c 11, .c 3, .c 167, .c 7, .c 3, .c 13, .p pv11 [pv2,pv3,pv11,pv6691], .c 3, .c 23,
  .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv13,pv43,pv79], .c 3, .c 5, .p pv2 [pv2,pv3,pv29,pv47],
  .c 3, .c 7, .c 13, .c 3, .c 31, .p pv53 [pv2,pv3,pv7,pv3943], .c 3, .c 947, .c 5, .c 3, .c 37,
  .c 17, .c 3, .c 5, .p pv3 [pv2,pv3,pv220811], .c 3, .p pv7 [pv2,pv5,pv19,pv367], .c 11, .c 3,
  .c 73, .c 467, .c 3, .c 7, .c 5, .c 3, .c 19, .c 277, .c 3, .c 5, .c 7, .c 3, .c 761, .c 521,
  .c 3, .p pv2 [pv2,pv11,pv60223], .c 31, .c 3, .p pv5 [pv2,pv17,pv4871], .c 5, .c 3, .c 271,
  .c 13, .c 3, .c 5, .c 19, .c 3, .c 71, .c 37, .c 3, .c 653, .c 7, .c 3, .c 89, .c 5, .c 3,
  .p pv2 [pv2,pv139,pv2383], .p pv3 [pv2,pv3,pv5,pv11,pv73], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv41,pv2693], .c 3, .c 11, .c 17, .c 3, .c 7, .p pv11 [pv2,pv3,pv55207], .c 3,
  .c 13, .c 5, .c 3, .p pv2 [pv2,pv167,pv3967], .c 7, .c 3, .c 5, .c 769, .c 3, .c 127, .c 331,
  .c 3, .c 17, .c 13, .c 3, .c 19, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv29,pv1523], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv11,pv239], .c 3, .p pv2 [pv2,pv5,pv97,pv683], .c 7, .c 3, .c 11, .c 251,
  .c 3, .c 31, .c 5, .c 3, .c 29, .c 19, .c 3, .c 5, .p pv3 [pv2,pv3,pv220841], .c 3, .c 7, .c 23,
  .c 3, .c 149,
]
private theorem h0161c23 : checkBlock 1324803 128 b0161c23 = true := by
  decide +kernel

private def b0161c24 : List Row := [
  .c 67, .c 3, .p pv5 [pv2,pv662531], .c 5, .c 3, .c 359, .c 11, .c 3, .c 5, .c 13, .c 3, .c 37,
  .p pv5 [pv2,pv3,pv11,pv17,pv1181], .c 3, .c 139, .p pv7 [pv2,pv3,pv43,pv107], .c 3, .c 7, .c 5,
  .c 3, .c 17, .c 181, .c 3, .c 5, .c 7, .c 3, .p pv13 [pv2,pv5,pv132511], .c 109, .c 3, .c 19,
  .p pv3 [pv2,pv3,pv37,pv47,pv127], .c 3, .p pv2 [pv2,pv23,pv28807], .c 5, .c 3, .c 13, .c 43,
  .c 3, .c 5, .c 11, .c 3, .c 199, .p pv3 [pv2,pv3,pv7,pv13,pv809], .c 3, .c 877, .c 7, .c 3,
  .c 349, .c 5, .c 3, .c 11, .c 41, .c 3, .c 5, .c 17, .c 3, .c 311, .p pv7 [pv2,pv3,pv110431],
  .c 3, .c 7, .p pv2 [pv2,pv3,pv83,pv887], .c 3, .p pv5 [pv2,pv662591], .c 5, .c 3, .c 1061, .c 7,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv131,pv281], .c 3, .c 17, .c 11, .c 3, .c 13, .c 491, .c 3, .c 29,
  .c 5, .c 3, .c 7, .c 101, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv139,pv227], .c 3, .c 19, .c 7, .c 3,
  .c 23, .c 293, .c 3, .c 41, .c 5, .c 3, .c 659, .p pv2 [pv2,pv3,pv5,pv19,pv31], .c 3, .c 5,
  .c 263, .c 3, .c 7, .p pv3 [pv2,pv3,pv220877], .c 3, .p pv2 [pv2,pv37,pv17909], .c 11, .c 3,
  .p pv3 [pv2,pv13,pv12743], .c 5, .c 3, .c 619, .c 31, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv17,pv61,pv71], .c 3, .c 11, .p pv2 [pv2,pv3,pv110441], .c 3, .c 419, .c 89,
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv421,pv787], .c 13, .c 3,
]
private theorem h0161c24 : checkBlock 1325059 128 b0161c24 = true := by
  decide +kernel

private def b0161c25 : List Row := [
  .c 5, .c 7, .c 3, .c 727, .c 389, .c 3, .c 67, .c 23, .c 3, .p pv2 [pv2,pv331333], .c 5, .c 3,
  .c 1033, .c 439, .c 3, .c 5, .c 61, .c 3, .p pv11 [pv2,pv5,pv13,pv2039], .c 47, .c 3, .c 11,
  .c 7, .c 3, .c 13, .c 5, .c 3, .c 577, .c 17, .c 3, .c 5, .c 37, .c 3, .c 547, .c 19, .c 3,
  .c 7, .c 13, .c 3, .c 479, .c 5, .c 3, .p pv11 [pv2,pv23,pv28813], .c 7, .c 3, .c 5, .c 41,
  .c 3, .c 797, .c 433, .c 3, .p pv3 [pv2,pv29,pv197], .p pv2 [pv2,pv3,pv220903], .c 3, .c 11,
  .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv4909], .c 3, .c 5, .c 859, .c 3, .c 13, .c 7, .c 3,
  .c 47, .p pv7 [pv2,pv3,pv41,pv449], .c 3, .c 227, .c 5, .c 3, .c 19, .c 67, .c 3, .c 5, .c 11,
  .c 3, .c 7, .c 17, .c 3, .c 53, .c 167, .c 3, .p pv2 [pv2,pv311,pv2131], .c 5, .c 3, .c 11,
  .p pv53 [pv2,pv3,pv5,pv17,pv23,pv113], .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv11,pv241],
  .c 29, .c 3, .c 17, .p pv2 [pv2,pv3,pv110459], .c 3, .c 7, .c 5, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv5,pv7,pv263], .c 3, .c 5, .c 7, .c 3, .c 251, .c 11, .c 3, .c 233, .c 199,
  .c 3, .p pv5 [pv2,pv662771], .c 5, .c 3, .c 109, .c 157, .c 3, .c 5, .p pv2 [pv2,pv3,pv36821],
  .c 3, .c 29, .c 383, .c 3, .p pv5 [pv2,pv11,pv89,pv677], .c 7,
]
private theorem h0161c25 : checkBlock 1325315 128 b0161c25 = true := by
  decide +kernel

private def b0161c26 : List Row := [
  .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv662789], .p pv2 [pv2,pv3,pv5,pv22093], .c 3, .c 5,
  .c 599, .c 3, .c 31, .c 83, .c 3, .c 7, .c 11, .c 3, .c 113, .c 5, .c 3, .c 17, .c 7, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv27617], .c 3, .c 11, .c 13, .c 3, .p pv2 [pv2,pv17,pv127,pv307], .c 151,
  .c 3, .p pv3 [pv2,pv7,pv11,pv269], .c 5, .c 3, .c 7, .c 71, .c 3, .c 5, .c 43, .c 3, .c 23,
  .c 7, .c 3, .p pv3 [pv2,pv165707], .p pv2 [pv2,pv3,pv109,pv2027], .c 3,
  .p pv5 [pv2,pv13,pv67,pv761], .c 5, .c 3, .p pv3 [pv2,pv19,pv17443], .c 59, .c 3, .c 5, .c 17,
  .c 3, .c 7, .c 929, .c 3, .c 11, .c 53, .c 3, .p pv2 [pv2,pv331423], .c 5, .c 3, .c 79, .c 13,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv19,pv29,pv401], .c 3, .c 17, .c 61, .c 3, .c 193, .c 1019, .c 3,
  .c 7, .c 5, .c 3, .c 47, .c 11, .c 3, .c 5, .c 7, .c 3, .c 241, .c 23, .c 3, .c 37, .c 137,
  .c 3, .c 11, .c 5, .c 3, .c 83, .p pv7 [pv2,pv3,pv5,pv1381], .c 3, .c 5, .c 109, .c 3,
  .p pv2 [pv2,pv5,pv233,pv569], .p pv19 [pv2,pv3,pv7,pv5261], .c 3, .c 31, .c 7, .c 3, .c 71,
  .c 5, .c 3, .c 23, .p pv11 [pv2,pv3,pv5,pv14731], .c 3, .c 5, .c 11, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv149,pv1483], .c 3, .c 7, .c 1093, .c 3, .c 17, .c 5, .c 3, .c 11, .c 7, .c 3,
  .c 5,
]
private theorem h0161c26 : checkBlock 1325571 128 b0161c26 = true := by
  decide +kernel

private def b0161c27 : List Row := [
  .c 101, .c 3, .c 13, .c 89, .c 3, .c 107, .c 19, .c 3, .c 499, .c 5, .c 3, .c 7, .c 29, .c 3,
  .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv66293], .c 7, .c 3, .p pv2 [pv2,pv643,pv1031], .c 941,
  .c 3, .p pv3 [pv2,pv173,pv479], .c 5, .c 3, .c 1117, .c 17, .c 3, .c 5, .c 347, .c 3, .c 7,
  .c 97, .c 3, .c 449, .c 41, .c 3, .p pv5 [pv2,pv662951], .c 5, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv5,pv193,pv229], .c 3, .c 5, .c 47, .c 3, .c 139,
  .p pv5 [pv2,pv3,pv13,pv89,pv191], .c 3, .c 23, .c 11, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv29,pv22861], .p pv2 [pv2,pv3,pv5,pv7,pv11,pv41], .c 3, .c 5, .c 7, .c 3, .c 11,
  .c 19, .c 3, .c 61, .p pv3 [pv2,pv3,pv223,pv991], .c 3, .c 31, .c 5, .c 3, .c 37, .c 367, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv55249], .c 3, .c 41, .c 17, .c 3, .c 13, .c 7, .c 3,
  .p pv3 [pv2,pv165749], .c 5, .c 3, .c 277, .p pv19 [pv2,pv3,pv5,pv13,pv17], .c 3, .c 5, .c 53,
  .c 3, .c 47, .c 13, .c 3, .c 7, .c 23, .c 3, .c 137, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv110503], .c 3, .p pv3 [pv2,pv5,pv33151], .c 37, .c 3,
  .p pv5 [pv2,pv263,pv2521], .p pv31 [pv2,pv3,pv19,pv727], .c 3, .p pv2 [pv2,pv7,pv13,pv3643],
  .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 19, .c 3, .p pv13 [pv2,pv5,pv132607], .c 7, .c 3, .c 43,
  .c 61, .c 3,
]
private theorem h0161c27 : checkBlock 1325827 128 b0161c27 = true := by
  decide +kernel

private def b0161c28 : List Row := [
  .c 11, .c 5, .c 3, .p pv3 [pv2,pv23,pv7207], .c 13, .c 3, .c 5, .p pv29 [pv2,pv3,pv9209], .c 3,
  .c 7, .c 193, .c 3, .c 401, .p pv2 [pv2,pv3,pv7,pv15787], .c 3, .c 53, .c 5, .c 3, .c 17,
  .c 379, .c 3, .c 5, .c 11, .c 3, .c 67, .p pv2 [pv2,pv3,pv4093], .c 3,
  .p pv3 [pv2,pv7,pv17,pv199], .c 229, .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv29 [pv2,pv3,pv5,pv7,pv421], .c 3, .c 5, .c 7, .c 3, .p pv13 [pv2,pv5,pv11,pv137], .c 43,
  .c 3, .p pv5 [pv2,pv53,pv12511], .c 13, .c 3, .c 79, .c 5, .c 3, .c 157, .c 19, .c 3, .c 5,
  .c 17, .c 3, .c 37, .c 11, .c 3, .p pv2 [pv2,pv331549], .c 7, .c 3, .c 23, .c 5, .c 3, .c 71,
  .c 31, .c 3, .c 5, .c 557, .c 3, .c 13, .c 241, .c 3, .c 7, .c 641, .c 3, .c 151, .c 5, .c 3,
  .p pv13 [pv2,pv17,pv19,pv2053], .c 7, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv1061],
  .p pv2 [pv2,pv3,pv79,pv1399], .c 3, .c 19, .c 11, .c 3, .c 1123, .c 5, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv5,pv11,pv4019], .c 3, .c 5, .p pv11 [pv2,pv3,pv7,pv19,pv277], .c 3, .c 11,
  .c 7, .c 3, .p pv5 [pv2,pv13,pv29,pv1759], .c 17, .c 3, .c 47, .c 5, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv5,pv4421], .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv13003], .c 3, .c 7,
  .p pv5 [pv2,pv3,pv13,pv109], .c 3, .c 331, .p pv11 [pv2,pv3,pv7,pv23,pv1373], .c 3, .c 17, .c 5,
  .c 3, .c 383, .c 79, .c 3, .c 5, .c 73,
]
private theorem h0161c28 : checkBlock 1326083 128 b0161c28 = true := by
  decide +kernel

private def b0161c29 : List Row := [
  .c 3, .c 23, .p pv5 [pv2,pv3,pv443,pv499], .c 3, .c 11, .p pv7 [pv2,pv3,pv12281], .c 3, .c 7,
  .c 5, .c 3, .p pv11 [pv2,pv11,pv60289], .c 227, .c 3, .c 5, .c 7, .c 3, .c 19, .c 29, .c 3,
  .c 13, .c 59, .c 3, .p pv5 [pv2,pv663191], .c 5, .c 3, .p pv2 [pv2,pv7,pv127,pv373], .c 11,
  .c 3, .c 5, .c 31, .c 3, .c 197, .c 13, .c 3, .c 601, .c 7, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv663209], .c 43, .c 3, .c 5, .p pv2 [pv2,pv3,pv221071], .c 3, .c 29, .c 23, .c 3,
  .c 7, .c 269, .c 3, .p pv5 [pv2,pv13,pv17,pv3001], .c 5, .c 3, .p pv3 [pv2,pv82903], .c 7, .c 3,
  .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv29,pv2287], .p pv5 [pv2,pv3,pv221077], .c 3,
  .p pv5 [pv2,pv19,pv67,pv521], .c 233, .c 3, .c 41, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 37,
  .c 3, .p pv2 [pv2,pv5,pv11,pv31,pv389], .c 7, .c 3, .c 59, .p pv2 [pv2,pv3,pv221083], .c 3,
  .p pv5 [pv2,pv23,pv28837], .c 5, .c 3, .c 643, .p pv3 [pv2,pv3,pv5,pv17], .c 3, .c 5, .c 619,
  .c 3, .c 7, .c 11, .c 3, .c 17, .p pv11 [pv2,pv3,pv7,pv47], .c 3, .c 13, .c 5, .c 3, .c 709,
  .c 593, .c 3, .c 5, .c 29, .c 3, .p pv13 [pv2,pv5,pv43,pv617], .c 277, .c 3, .c 211, .c 13,
  .c 3, .c 7, .c 5, .c 3, .c 179, .c 23, .c 3, .c 5, .c 7, .c 3, .c 347, .c 31, .c 3,
  .p pv2 [pv2,pv107,pv6199], .c 11, .c 3, .c 43,
]
private theorem h0161c29 : checkBlock 1326339 128 b0161c29 = true := by
  decide +kernel

private def b0161c30 : List Row := [
  .c 5, .c 3, .c 19, .c 281, .c 3, .c 5, .p pv3 [pv2,pv3,pv221101], .c 3, .c 11,
  .p pv2 [pv2,pv3,pv7,pv17,pv929], .c 3, .c 23, .c 7, .c 3, .p pv5 [pv2,pv11,pv47,pv1283], .c 5,
  .c 3, .c 17, .p pv11 [pv2,pv3,pv5,pv44221], .c 3, .c 5, .c 13, .c 3,
  .p pv3 [pv2,pv5,pv7,pv23,pv103], .c 53, .c 3, .c 7, .p pv17 [pv2,pv3,pv167,pv331], .c 3,
  .p pv2 [pv2,pv331663], .c 5, .c 3, .p pv2 [pv2,pv439,pv1511], .c 7, .c 3, .c 5, .c 67, .c 3,
  .c 457, .p pv7 [pv2,pv3,pv37,pv83], .c 3, .c 11, .c 43, .c 3, .p pv2 [pv2,pv7,pv193,pv491],
  .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv14741], .c 3, .c 5, .c 17, .c 3,
  .p pv2 [pv2,pv5,pv13267], .c 7, .c 3, .c 31, .c 23, .c 3, .c 19, .c 5, .c 3, .c 41, .c 11, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv79,pv311], .c 3, .c 7, .c 59, .c 3, .c 173,
  .p pv2 [pv2,pv3,pv7,pv31,pv1019], .c 3, .c 11, .c 5, .c 3, .c 53, .c 19, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv110563], .c 3, .c 373, .c 47, .c 3, .c 13, .c 31, .c 3, .c 7, .c 5, .c 3,
  .c 29, .p pv2 [pv2,pv3,pv5,pv7,pv13], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv132679], .c 13,
  .c 3, .p pv2 [pv2,pv409,pv811], .c 17, .c 3, .c 1039, .c 5, .c 3, .c 11, .c 61, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv17,pv271], .c 3, .p pv2 [pv2,pv5,pv11,pv37,pv163],
  .p pv3 [pv2,pv3,pv7,pv4513], .c 3, .c 19, .c 7, .c 3, .c 17, .c 5, .c 3,
  .p pv13 [pv2,pv83,pv7993], .c 499, .c 3, .c 5, .c 23, .c 3,
]
private theorem h0161c30 : checkBlock 1326595 128 b0161c30 = true := by
  decide +kernel

private def b0161c31 : List Row := [
  .c 43, .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv13,pv17011], .c 3, .c 97, .c 5, .c 3,
  .p pv2 [pv2,pv67,pv4951], .c 7, .c 3, .c 5, .c 191, .c 3, .p pv3 [pv2,pv5,pv8293], .c 41, .c 3,
  .p pv5 [pv2,pv11,pv5483], .p pv13 [pv2,pv3,pv6143], .c 3, .c 23, .c 5, .c 3, .c 7, .c 17, .c 3,
  .c 5, .c 107, .c 3, .c 181, .c 7, .c 3, .p pv2 [pv2,pv23,pv14423], .c 11, .c 3, .c 13, .c 5,
  .c 3, .p pv3 [pv2,pv239,pv347], .c 37, .c 3, .c 5, .c 43, .c 3, .c 7, .p pv3 [pv2,pv3,pv8191],
  .c 3, .p pv2 [pv2,pv241,pv2753], .c 13, .c 3, .c 29, .c 5, .c 3, .c 113, .c 53, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv109,pv2029], .c 3, .p pv2 [pv2,pv5,pv132697], .c 419, .c 3, .c 269, .c 19,
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv13,pv151], .c 563, .c 3, .c 5, .c 7, .c 3, .c 13, .c 17,
  .c 3, .c 11, .p pv11 [pv2,pv3,pv23,pv601], .c 3, .p pv2 [pv2,pv331753], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv11,pv1231], .c 757, .c 3, .c 5, .c 13, .c 3, .c 23, .c 139, .c 3, .c 17, .c 7,
  .c 3, .p pv2 [pv2,pv37,pv79,pv227], .c 5, .c 3, .c 431, .c 11, .c 3, .c 5, .c 97, .c 3, .c 71,
  .p pv3 [pv2,pv3,pv11,pv20107], .c 3, .c 7, .c 29, .c 3, .c 11, .c 5, .c 3, .c 13, .c 7, .c 3,
  .c 5, .c 59, .c 3, .p pv2 [pv2,pv5,pv132709], .c 19, .c 3, .c 439, .p pv3 [pv2,pv3,pv29,pv263],
  .c 3, .c 1151, .c 5,
]
private theorem h0161c31 : checkBlock 1326851 128 b0161c31 = true := by
  decide +kernel

def rows0161 : List Row :=
  b0161c00 ++ b0161c01 ++ b0161c02 ++ b0161c03 ++ b0161c04 ++ b0161c05 ++ b0161c06 ++ b0161c07 ++
  b0161c08 ++ b0161c09 ++ b0161c10 ++ b0161c11 ++ b0161c12 ++ b0161c13 ++ b0161c14 ++ b0161c15 ++
  b0161c16 ++ b0161c17 ++ b0161c18 ++ b0161c19 ++ b0161c20 ++ b0161c21 ++ b0161c22 ++ b0161c23 ++
  b0161c24 ++ b0161c25 ++ b0161c26 ++ b0161c27 ++ b0161c28 ++ b0161c29 ++ b0161c30 ++ b0161c31

attribute [local irreducible] checkBlock checkRows checkPrime

theorem checked0161 : checkBlock 1318915 4096 rows0161 = true :=
  checkBlock_append h0161c00 (
    checkBlock_append h0161c01 (
    checkBlock_append h0161c02 (
    checkBlock_append h0161c03 (
    checkBlock_append h0161c04 (
    checkBlock_append h0161c05 (
    checkBlock_append h0161c06 (
    checkBlock_append h0161c07 (
    checkBlock_append h0161c08 (
    checkBlock_append h0161c09 (
    checkBlock_append h0161c10 (
    checkBlock_append h0161c11 (
    checkBlock_append h0161c12 (
    checkBlock_append h0161c13 (
    checkBlock_append h0161c14 (
    checkBlock_append h0161c15 (
    checkBlock_append h0161c16 (
    checkBlock_append h0161c17 (
    checkBlock_append h0161c18 (
    checkBlock_append h0161c19 (
    checkBlock_append h0161c20 (
    checkBlock_append h0161c21 (
    checkBlock_append h0161c22 (
    checkBlock_append h0161c23 (
    checkBlock_append h0161c24 (
    checkBlock_append h0161c25 (
    checkBlock_append h0161c26 (
    checkBlock_append h0161c27 (
    checkBlock_append h0161c28 (
    checkBlock_append h0161c29 (
    checkBlock_append h0161c30 (
    h0161c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
