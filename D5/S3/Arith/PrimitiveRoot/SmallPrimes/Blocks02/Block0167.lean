/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks02/Block0167
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks02/Block0167.checked0167
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table021
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table025
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table029
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table037
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table049
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table071
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table072
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table124

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0167c00 : List Row := [
  .c 577, .c 3, .p pv11 [pv2,pv5,pv11,pv12437], .c 7, .c 3, .p pv2 [pv2,pv19,pv47,pv383],
  .p pv3 [pv2,pv3,pv228013], .c 3, .p pv2 [pv2,pv137,pv4993], .c 5, .c 3, .c 53, .c 113, .c 3,
  .c 5, .c 179, .c 3, .c 7, .c 11, .c 3, .c 13, .c 17, .c 3, .c 389, .c 5, .c 3,
  .p pv7 [pv2,pv149,pv4591], .p pv7 [pv2,pv3,pv5,pv13,pv877], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv17,pv263], .c 3, .c 43, .c 13, .c 3, .c 1031, .c 971, .c 3, .c 7, .c 5, .c 3,
  .c 37, .c 59, .c 3, .c 5, .c 7, .c 3, .p pv13 [pv2,pv5,pv17,pv503],
  .p pv2 [pv2,pv3,pv29,pv2621], .c 3, .p pv5 [pv2,pv73,pv9371], .c 11, .c 3,
  .p pv2 [pv2,pv13,pv83,pv317], .c 5, .c 3, .c 181, .p pv2 [pv2,pv3,pv5,pv11,pv691], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv37,pv6163], .c 3, .c 11, .c 881, .c 3, .c 89, .c 7, .c 3,
  .p pv2 [pv2,pv11,pv62191], .c 5, .c 3, .c 19, .c 13, .c 3, .c 5, .c 43, .c 3, .c 347, .c 37,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv17,pv19,pv353], .c 3, .p pv3 [pv2,pv171029], .c 5, .c 3, .c 73,
  .c 7, .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv13,pv421], .p pv5 [pv2,pv3,pv41,pv103], .c 3,
  .c 11, .p pv2 [pv2,pv3,pv457,pv499], .c 3, .c 13, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv23,pv661], .c 3, .c 5, .c 109, .c 3, .p pv3 [pv2,pv5,pv79,pv433], .c 7,
  .c 3, .p pv5 [pv2,pv89,pv7687], .c 13, .c 3, .c 23, .c 5, .c 3, .c 307, .c 11, .c 3, .c 5,
  .c 29, .c 3, .c 7, .c 17, .c 3, .c 113, .p pv7 [pv2,pv3,pv7,pv32579], .c 3,
]
private theorem h0167c00 : checkBlock 1368067 128 b0167c00 = true := by
  decide +kernel

private def b0167c01 : List Row := [
  .c 11, .c 5, .c 3, .p pv11 [pv2,pv13,pv59,pv223], .p pv2 [pv2,pv3,pv5,pv17,pv2683], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv29,pv983], .c 3, .c 13, .p pv3 [pv2,pv3,pv19,pv4001], .c 3, .c 17,
  .p pv2 [pv2,pv3,pv101,pv1129], .c 3, .c 7, .c 5, .c 3, .c 79, .c 19, .c 3, .c 5, .c 7, .c 3,
  .c 31, .p pv5 [pv2,pv3,pv114031], .c 3, .p pv3 [pv2,pv171047], .c 97, .c 3, .c 71, .c 5, .c 3,
  .c 11, .c 919, .c 3, .c 5, .p pv5 [pv2,pv3,pv38011], .c 3, .p pv3 [pv2,pv5,pv11,pv311], .c 269,
  .c 3, .c 53, .c 7, .c 3, .c 61, .c 5, .c 3, .c 13, .c 83, .c 3, .c 5, .c 443, .c 3, .c 23,
  .c 11, .c 3, .c 7, .p pv13 [pv2,pv3,pv79,pv2887], .c 3, .p pv2 [pv2,pv684221], .c 5, .c 3,
  .c 17, .c 7, .c 3, .c 5, .c 41, .c 3, .p pv2 [pv2,pv5,pv53,pv1291], .p pv3 [pv2,pv3,pv228077],
  .c 3, .p pv2 [pv2,pv11,pv17,pv3659], .p pv2 [pv2,pv3,pv12671], .c 3, .p pv3 [pv2,pv7,pv3491],
  .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv10861], .c 3,
  .p pv11 [pv2,pv5,pv136849], .c 7, .c 3, .c 13, .c 11, .c 3, .c 479, .c 5, .c 3,
  .p pv2 [pv2,pv359,pv953], .c 733, .c 3, .c 5, .c 17, .c 3, .c 7, .c 13, .c 3,
  .p pv5 [pv2,pv31,pv22073], .p pv17 [pv2,pv3,pv7,pv4073], .c 3, .c 1087, .c 5, .c 3, .c 29,
  .c 181, .c 3, .c 5, .p pv2 [pv2,pv3,pv23,pv47,pv211], .c 3, .c 17, .c 89, .c 3, .c 31, .c 197,
  .c 3, .c 7, .c 5, .c 3, .c 23, .c 991, .c 3, .c 5, .c 7,
]
private theorem h0167c01 : checkBlock 1368323 128 b0167c01 = true := by
  decide +kernel

private def b0167c02 : List Row := [
  .c 3, .c 353, .c 227, .c 3, .c 11, .c 19, .c 3, .c 37, .c 5, .c 3, .p pv7 [pv2,pv7,pv11,pv8887],
  .c 13, .c 3, .c 5, .c 821, .c 3, .c 1153, .c 401, .c 3, .p pv3 [pv2,pv171077], .c 7, .c 3,
  .c 59, .c 5, .c 3, .c 857, .c 11, .c 3, .c 5, .c 107, .c 3, .c 887,
  .p pv2 [pv2,pv3,pv11,pv89,pv233], .c 3, .c 7, .c 823, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv684329], .c 7, .c 3, .c 5, .c 37, .c 3, .c 421, .p pv5 [pv2,pv3,pv53,pv269], .c 3,
  .c 73, .c 13, .c 3, .p pv5 [pv2,pv7,pv59,pv1657], .c 5, .c 3, .c 7, .c 523, .c 3, .c 5, .c 11,
  .c 3, .c 509, .c 7, .c 3, .c 23, .c 461, .c 3, .c 29, .c 5, .c 3, .c 11, .c 17, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv157,pv1453], .c 3, .c 7, .c 43, .c 3, .p pv3 [pv2,pv42773],
  .p pv3 [pv2,pv3,pv7,pv17,pv71], .c 3, .c 31, .c 5, .c 3, .c 313, .c 281, .c 3, .c 5, .c 13,
  .c 3, .p pv17 [pv2,pv5,pv19,pv1801], .c 11, .c 3, .c 97, .c 113, .c 3, .c 7, .c 5, .c 3, .c 19,
  .c 47, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv136879], .p pv7 [pv2,pv3,pv6337], .c 3,
  .p pv2 [pv2,pv11,pv13,pv2393], .c 23, .c 3, .p pv2 [pv2,pv439,pv1559], .c 5, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv5,pv67,pv227], .c 3, .c 5, .c 19, .c 3, .c 271, .c 17, .c 3,
  .p pv2 [pv2,pv41,pv16693], .c 7, .c 3, .c 79,
]
private theorem h0167c02 : checkBlock 1368579 128 b0167c02 = true := by
  decide +kernel

private def b0167c03 : List Row := [
  .c 5, .c 3, .p pv29 [pv2,pv684419], .p pv29 [pv2,pv3,pv5,pv11,pv17,pv61], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv25349], .c 3, .c 11, .c 101, .c 3, .c 7, .c 59, .c 3, .c 149, .c 5, .c 3,
  .p pv2 [pv2,pv23,pv14879], .c 7, .c 3, .c 5, .c 67, .c 3, .c 997, .c 157, .c 3, .c 13, .c 37,
  .c 3, .c 19, .c 5, .c 3, .c 7, .c 61, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv11,pv2963], .c 3,
  .p pv11 [pv2,pv5,pv367,pv373], .c 7, .c 3, .c 11, .c 83, .c 3, .c 409, .c 5, .c 3, .c 31, .c 19,
  .c 3, .c 5, .c 23, .c 3, .c 7, .p pv3 [pv2,pv3,pv17,pv13421], .c 3, .c 643, .c 41, .c 3, .c 197,
  .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv151,pv1511], .c 3,
  .p pv2 [pv2,pv5,pv136897], .c 103, .c 3, .c 59, .p pv2 [pv2,pv3,pv13,pv17551], .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv19,pv18013], .c 13, .c 3, .c 5, .c 7, .c 3, .c 449, .c 29, .c 3, .c 19,
  .p pv7 [pv2,pv3,pv3169], .c 3, .p pv2 [pv2,pv149,pv2297], .c 5, .c 3, .p pv2 [pv2,pv7,pv97787],
  .p pv2 [pv2,pv3,pv5,pv22817], .c 3, .c 5, .c 11, .c 3, .c 41, .p pv11 [pv2,pv3,pv7,pv29,pv281],
  .c 3, .c 37, .c 7, .c 3, .c 13, .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv9127], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv1097], .c 3, .c 17, .c 47, .c 3, .c 7, .c 13, .c 3, .c 751, .c 5, .c 3,
  .c 709, .c 7, .c 3, .c 5, .c 89, .c 3,
]
private theorem h0167c03 : checkBlock 1368835 128 b0167c03 = true := by
  decide +kernel

private def b0167c04 : List Row := [
  .c 463, .c 11, .c 3, .p pv3 [pv2,pv53,pv3229], .p pv2 [pv2,pv3,pv23,pv3307], .c 3,
  .p pv5 [pv2,pv7,pv19,pv5147], .c 5, .c 3, .c 7, .c 37, .c 3, .c 5, .c 151, .c 3, .c 13, .c 7,
  .c 3, .c 349, .c 17, .c 3, .p pv2 [pv2,pv342283], .c 5, .c 3, .p pv2 [pv2,pv684569], .c 547,
  .c 3, .c 5, .c 13, .c 3, .c 7, .p pv13 [pv2,pv3,pv2377], .c 3, .c 47, .c 11, .c 3, .c 17, .c 5,
  .c 3, .p pv3 [pv2,pv83,pv1031], .c 179, .c 3, .c 5, .c 29, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv228197], .c 3, .c 127, .c 293, .c 3, .c 7, .c 5, .c 3, .c 13,
  .p pv31 [pv2,pv3,pv5,pv7,pv163], .c 3, .c 5, .c 7, .c 3, .c 277, .c 23, .c 3,
  .p pv5 [pv2,pv19,pv563], .p pv2 [pv2,pv3,pv228203], .c 3, .p pv5 [pv2,pv37,pv18503], .c 5, .c 3,
  .p pv3 [pv2,pv7,pv79,pv619], .c 17, .c 3, .c 5, .c 593, .c 3, .c 439,
  .p pv2 [pv2,pv3,pv7,pv10867], .c 3, .c 11, .c 7, .c 3, .c 397, .c 5, .c 3, .c 23, .c 73, .c 3,
  .c 5, .c 61, .c 3, .c 541, .c 19, .c 3, .c 7, .c 67, .c 3, .c 373, .c 5, .c 3, .c 139, .c 7,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv37,pv257], .c 3, .c 31, .c 13, .c 3, .c 79,
  .p pv2 [pv2,pv3,pv53,pv2153], .c 3, .c 11, .c 5, .c 3, .c 7, .p pv19 [pv2,pv3,pv5,pv11411],
  .c 3, .c 5, .c 379, .c 3, .c 59, .c 7, .c 3, .p pv3 [pv2,pv171167], .p pv3 [pv2,pv3,pv228223],
  .c 3, .c 131, .c 5,
]
private theorem h0167c04 : checkBlock 1369091 128 b0167c04 = true := by
  decide +kernel

private def b0167c05 : List Row := [
  .c 3, .c 19, .c 23, .c 3, .c 5, .c 11, .c 3, .c 7, .c 31, .c 3, .c 17,
  .p pv43 [pv2,pv3,pv7,pv11,pv13,pv19], .c 3, .p pv2 [pv2,pv342343], .c 5, .c 3, .c 11, .c 13,
  .c 3, .c 5, .c 19, .c 3, .p pv7 [pv2,pv5,pv11,pv59,pv211], .p pv5 [pv2,pv3,pv47,pv607], .c 3,
  .c 23, .c 491, .c 3, .c 7, .c 5, .c 3, .c 29, .p pv19 [pv2,pv3,pv5,pv7,pv6521], .c 3, .c 5,
  .c 7, .c 3, .c 43, .c 11, .c 3, .p pv2 [pv2,pv684713], .p pv2 [pv2,pv3,pv139,pv821], .c 3,
  .c 13, .c 5, .c 3, .c 47, .c 41, .c 3, .c 5, .c 113, .c 3, .p pv2 [pv2,pv5,pv61,pv449], .c 1051,
  .c 3, .p pv5 [pv2,pv11,pv31,pv251], .c 7, .c 3, .c 19, .c 5, .c 3, .c 17, .c 587, .c 3, .c 5,
  .c 1129, .c 3, .c 37, .p pv3 [pv2,pv3,pv19,pv41,pv293], .c 3, .c 7, .c 11, .c 3, .c 107, .c 5,
  .c 3, .p pv2 [pv2,pv13,pv52673], .c 7, .c 3, .c 5, .c 43, .c 3, .c 11, .c 421, .c 3,
  .p pv2 [pv2,pv342379], .c 71, .c 3, .c 41, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv15217], .c 3,
  .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv68477], .c 7, .c 3, .c 67, .c 31, .c 3, .c 73, .c 5, .c 3,
  .p pv7 [pv2,pv19,pv23,pv1567], .p pv11 [pv2,pv3,pv5,pv101,pv113], .c 3, .c 5, .c 59, .c 3, .c 7,
  .c 53, .c 3, .c 11, .c 433, .c 3, .c 29, .c 5, .c 3, .c 13, .c 103, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv19,pv6007], .c 3, .c 211,
]
private theorem h0167c05 : checkBlock 1369347 128 b0167c05 = true := by
  decide +kernel

private def b0167c06 : List Row := [
  .c 241, .c 3, .p pv5 [pv2,pv7,pv97829], .c 347, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv684809],
  .c 11, .c 3, .c 5, .c 7, .c 3, .c 461, .c 61, .c 3, .c 809, .c 17, .c 3, .c 11, .c 5, .c 3,
  .c 229, .p pv3 [pv2,pv3,pv5,pv23,pv397], .c 3, .c 5, .p pv31 [pv2,pv3,pv17,pv373], .c 3, .c 71,
  .c 557, .c 3, .c 13, .c 7, .c 3, .c 17, .c 5, .c 3, .c 43, .c 67, .c 3, .c 5, .c 11, .c 3,
  .c 19, .c 13, .c 3, .c 7, .c 29, .c 3, .c 37, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 199, .c 3,
  .c 47, .p pv3 [pv2,pv3,pv43,pv5309], .c 3, .p pv5 [pv2,pv137,pv4999], .c 19, .c 3,
  .p pv3 [pv2,pv7,pv13,pv53,pv71], .c 5, .c 3, .c 7, .c 17, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv1553], .c 3, .c 1061, .c 7, .c 3, .c 29,
  .p pv3 [pv2,pv3,pv13,pv17,pv1033], .c 3, .p pv2 [pv2,pv101,pv6781], .c 5, .c 3, .c 41, .c 13,
  .c 3, .c 5, .c 37, .c 3, .c 7, .p pv3 [pv2,pv3,pv76099], .c 3,
  .p pv2 [pv2,pv11,pv19,pv29,pv113], .p pv13 [pv2,pv3,pv7,pv23,pv709], .c 3,
  .p pv3 [pv2,pv17,pv1259], .c 5, .c 3, .c 89, .p pv7 [pv2,pv3,pv5,pv761], .c 3, .c 5, .c 233,
  .c 3, .c 23, .p pv19 [pv2,pv3,pv211,pv541], .c 3, .c 641, .c 11, .c 3, .c 7, .c 5, .c 3, .c 571,
  .p pv7 [pv2,pv3,pv5,pv7,pv11,pv593], .c 3, .c 5, .c 7, .c 3, .c 11, .c 17, .c 3, .c 619, .c 13,
  .c 3, .p pv2 [pv2,pv11,pv163,pv191], .c 5, .c 3,
]
private theorem h0167c06 : checkBlock 1369603 128 b0167c06 = true := by
  decide +kernel

private def b0167c07 : List Row := [
  .c 31, .p pv7 [pv2,pv3,pv5,pv17,pv79], .c 3, .c 5, .c 131, .c 3, .p pv17 [pv2,pv5,pv136987],
  .c 29, .c 3, .c 17, .c 7, .c 3, .p pv2 [pv2,pv67,pv10223], .c 5, .c 3, .c 223, .c 53, .c 3,
  .c 5, .p pv71 [pv2,pv3,pv11,pv5189], .c 3, .c 13, .c 23, .c 3, .c 7, .c 47, .c 3, .c 599, .c 5,
  .c 3, .c 19, .c 7, .c 3, .c 5, .c 13, .c 3, .c 29, .c 41, .c 3, .c 43, .c 79, .c 3,
  .p pv7 [pv2,pv7,pv1997], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 19, .c 3,
  .p pv3 [pv2,pv5,pv29,pv1181], .c 7, .c 3, .c 263, .p pv7 [pv2,pv3,pv28541], .c 3, .c 11, .c 5,
  .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv43,pv59], .c 3, .c 5, .c 173, .c 3, .c 7, .c 353, .c 3,
  .c 53, .c 37, .c 3, .c 47, .c 5, .c 3, .c 331, .c 367, .c 3, .c 5, .c 11, .c 3, .c 109, .c 43,
  .c 3, .p pv2 [pv2,pv7,pv97859], .c 373, .c 3, .c 7, .c 5, .c 3, .c 11, .c 23, .c 3, .c 5, .c 7,
  .c 3, .p pv2 [pv2,pv5,pv11,pv47,pv53], .p pv2 [pv2,pv3,pv19,pv2003], .c 3, .c 13,
  .p pv11 [pv2,pv3,pv389,pv587], .c 3, .p pv5 [pv2,pv685031], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv167,pv293], .c 19, .c 3, .c 5, .p pv2 [pv2,pv3,pv29,pv31,pv127], .c 3, .c 17,
  .c 11, .c 3, .c 23, .c 7, .c 3, .p pv2 [pv2,pv461,pv743], .c 5, .c 3,
  .p pv2 [pv2,pv17,pv59,pv683], .p pv2 [pv2,pv3,pv5,pv4567], .c 3, .c 5, .c 31, .c 3,
  .p pv7 [pv2,pv5,pv7,pv23,pv37], .p pv5 [pv2,pv3,pv223],
]
private theorem h0167c07 : checkBlock 1369859 128 b0167c07 = true := by
  decide +kernel

private def b0167c08 : List Row := [
  .c 3, .c 7, .c 439, .c 3, .c 139, .c 5, .c 3, .c 131, .c 7, .c 3, .c 5, .c 73, .c 3, .c 307,
  .p pv5 [pv2,pv3,pv25373], .c 3, .c 19, .c 11, .c 3, .c 1097, .c 5, .c 3, .c 7, .c 13, .c 3,
  .c 5, .c 787, .c 3, .c 11, .c 7, .c 3, .p pv3 [pv2,pv79,pv271], .c 23, .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv342547], .c 47, .c 3, .c 5, .p pv19 [pv2,pv3,pv4229], .c 3, .c 7, .c 127, .c 3,
  .c 1063, .c 53, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv685109], .c 29, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv13,pv1597], .c 3, .c 31, .c 643, .c 3, .c 11, .c 13, .c 3, .c 7, .c 5,
  .c 3, .c 821, .c 17, .c 3, .c 5, .c 7, .c 3, .c 19, .p pv3 [pv2,pv3,pv31,pv53,pv139], .c 3,
  .c 101, .p pv7 [pv2,pv3,pv17,pv2239], .c 3, .c 233, .c 5, .c 3, .c 29, .c 11, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv269,pv283], .c 3, .c 13, .c 31, .c 3, .p pv3 [pv2,pv157,pv1091], .c 7, .c 3,
  .c 11, .c 5, .c 3, .c 947, .p pv3 [pv2,pv3,pv5,pv45677], .c 3, .c 5, .c 13, .c 3,
  .p pv3 [pv2,pv5,pv7,pv2447], .p pv2 [pv2,pv3,pv76129], .c 3, .c 7, .p pv41 [pv2,pv3,pv57097],
  .c 3, .c 89, .c 5, .c 3, .c 827, .c 7, .c 3, .c 5, .c 11, .c 3, .c 67, .c 17, .c 3, .c 617,
  .p pv3 [pv2,pv3,pv11,pv769], .c 3, .c 23, .c 5, .c 3, .c 7,
]
private theorem h0167c08 : checkBlock 1370115 128 b0167c08 = true := by
  decide +kernel

private def b0167c09 : List Row := [
  .c 71, .c 3, .c 5, .p pv17 [pv2,pv3,pv7,pv2719], .c 3, .c 491, .c 7, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv114199], .c 3, .c 59, .c 5, .c 3, .c 227, .c 139, .c 3, .c 5,
  .p pv17 [pv2,pv3,pv37,pv6173], .c 3, .c 7, .c 11, .c 3, .c 31, .c 479, .c 3, .c 593, .c 5, .c 3,
  .c 73, .p pv31 [pv2,pv3,pv5,pv15227], .c 3, .c 5, .c 281, .c 3, .c 1039, .c 37, .c 3, .c 13,
  .p pv17 [pv2,pv3,pv31,pv307], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv641,pv1069],
  .p pv17 [pv2,pv3,pv5,pv7,pv13,pv251], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv19,pv7213],
  .c 13, .c 3, .c 907, .c 11, .c 3, .p pv2 [pv2,pv29,pv23629], .c 5, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv5,pv11,pv4153], .c 3, .c 5, .c 709, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv7,pv73,pv149], .c 3, .c 41, .c 7, .c 3, .c 71, .c 5, .c 3,
  .p pv13 [pv2,pv103,pv6653], .p pv19 [pv2,pv3,pv5,pv47], .c 3, .c 5, .c 19, .c 3,
  .p pv2 [pv2,pv5,pv7,pv2797], .p pv2 [pv2,pv3,pv181,pv631], .c 3, .c 7, .c 43, .c 3, .c 457,
  .c 5, .c 3, .c 419, .c 7, .c 3, .c 5, .c 17, .c 3, .c 761, .c 107, .c 3, .c 11, .c 29, .c 3,
  .p pv2 [pv2,pv7,pv31,pv1579], .c 5, .c 3, .c 7, .c 257, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv32633], .c 3, .c 17, .c 7, .c 3, .p pv2 [pv2,pv277,pv1237],
  .p pv23 [pv2,pv3,pv29,pv7877], .c 3, .c 13, .c 5, .c 3, .c 61, .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv23,pv191], .c 3, .c 7, .p pv7 [pv2,pv3,pv11,pv19,pv1093], .c 3,
]
private theorem h0167c09 : checkBlock 1370371 128 b0167c09 = true := by
  decide +kernel

private def b0167c10 : List Row := [
  .c 29, .c 13, .c 3, .c 11, .c 5, .c 3, .c 23, .c 19, .c 3, .c 5, .c 653, .c 3, .c 149, .c 131,
  .c 3, .p pv3 [pv2,pv7,pv29,pv211], .c 17, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv13,pv43,pv613],
  .c 41, .c 3, .c 5, .c 7, .c 3, .c 13, .p pv2 [pv2,pv3,pv8461], .c 3,
  .p pv5 [pv2,pv53,pv67,pv193], .c 89, .c 3, .c 17, .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv1523], .c 3, .c 5, .c 13, .c 3, .c 43, .c 181, .c 3, .c 19, .c 7, .c 3,
  .p pv2 [pv2,pv685361], .c 5, .c 3, .c 79, .c 23, .c 3, .c 5, .c 509, .c 3,
  .p pv2 [pv2,pv5,pv7,pv9791], .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv114229], .c 3, .c 41, .c 5,
  .c 3, .c 13, .c 7, .c 3, .c 5, .c 157, .c 3, .c 853, .p pv2 [pv2,pv3,pv13,pv29,pv101], .c 3,
  .c 23, .p pv2 [pv2,pv3,pv17,pv89,pv151], .c 3, .c 523, .c 5, .c 3, .c 7, .c 1033, .c 3, .c 5,
  .c 43, .c 3, .c 29, .c 7, .c 3, .c 191, .c 11, .c 3, .c 37, .c 5, .c 3,
  .p pv2 [pv2,pv139,pv4931], .p pv47 [pv2,pv3,pv5,pv11,pv31,pv67], .c 3, .c 5, .c 103, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv28559], .c 3, .c 13, .p pv7 [pv2,pv3,pv7,pv127,pv257], .c 3, .c 379, .c 5,
  .c 3, .c 47, .c 31, .c 3, .c 5, .p pv5 [pv2,pv3,pv57119], .c 3, .p pv3 [pv2,pv5,pv68543], .c 13,
  .c 3, .c 73, .c 19, .c 3, .c 7, .c 5, .c 3, .c 193, .c 601,
]
private theorem h0167c10 : checkBlock 1370627 128 b0167c10 = true := by
  decide +kernel

private def b0167c11 : List Row := [
  .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv137089], .c 109, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv53,pv479], .c 3, .c 167, .c 5, .c 3, .p pv2 [pv2,pv7,pv11,pv4451], .c 83,
  .c 3, .c 5, .c 29, .c 3, .p pv3 [pv2,pv5,pv34273], .c 197, .c 3, .c 757, .c 7, .c 3,
  .p pv2 [pv2,pv342733], .c 5, .c 3, .c 71, .c 11, .c 3, .c 5, .c 293, .c 3, .c 53,
  .p pv5 [pv2,pv3,pv11,pv577], .c 3, .c 7, .c 137, .c 3, .c 11, .c 5, .c 3, .c 43, .c 7, .c 3,
  .c 5, .p pv7 [pv2,pv3,pv14281], .c 3, .p pv3 [pv2,pv5,pv13,pv5273], .c 19, .c 3,
  .p pv2 [pv2,pv685493], .c 271, .c 3, .c 13, .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv457], .c 3,
  .c 5, .c 11, .c 3, .c 431, .c 7, .c 3, .p pv3 [pv2,pv17,pv593], .c 13, .c 3, .c 229, .c 5, .c 3,
  .c 11, .p pv3 [pv2,pv3,pv5,pv23,pv1987], .c 3, .c 5, .c 31, .c 3, .c 7, .c 1049, .c 3,
  .p pv5 [pv2,pv131,pv5233], .c 241, .c 3, .c 23, .c 5, .c 3, .c 19, .p pv7 [pv2,pv3,pv5,pv2539],
  .c 3, .c 5, .c 17, .c 3, .c 13, .c 11, .c 3, .c 83, .p pv3 [pv2,pv3,pv19,pv211], .c 3, .c 7,
  .c 5, .c 3, .p pv3 [pv2,pv67,pv1279], .c 29, .c 3, .c 5, .c 7, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv228517], .c 3, .p pv2 [pv2,pv11,pv62323], .c 37, .c 3,
  .p pv3 [pv2,pv367,pv467], .c 5, .c 3, .p pv31 [pv2,pv7,pv17,pv823],
  .p pv7 [pv2,pv3,pv5,pv29,pv197], .c 3, .c 5, .c 769, .c 3, .c 47, .c 719, .c 3,
  .p pv3 [pv2,pv13,pv103],
]
private theorem h0167c11 : checkBlock 1370883 128 b0167c11 = true := by
  decide +kernel

private def b0167c12 : List Row := [
  .c 7, .c 3, .c 239, .c 5, .c 3, .c 13, .p pv11 [pv2,pv3,pv5,pv11,pv277], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv163,pv701], .c 3, .c 11, .c 41, .c 3, .c 7, .c 17, .c 3, .c 19, .c 5, .c 3,
  .p pv2 [pv2,pv29,pv47,pv503], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv4481], .c 3, .c 23,
  .p pv7 [pv2,pv3,pv19,pv31,pv97], .c 3, .c 421, .c 311, .c 3, .c 17, .c 5, .c 3, .c 7, .c 19,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv11,pv53], .c 3, .c 349, .c 7, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv114269], .c 3, .c 137, .c 5, .c 3, .c 103, .c 1171, .c 3, .c 5, .c 149, .c 3,
  .c 7, .c 13, .c 3, .c 37, .p pv3 [pv2,pv3,pv7,pv10883], .c 3, .p pv5 [pv2,pv685631], .c 5, .c 3,
  .c 53, .c 11, .c 3, .c 5, .c 101, .c 3, .c 613, .c 23, .c 3, .c 19, .c 67, .c 3, .c 7, .c 5,
  .c 3, .c 883, .p pv2 [pv2,pv3,pv5,pv7,pv653], .c 3, .c 5, .c 7, .c 3, .c 433, .c 43, .c 3,
  .c 197, .c 47, .c 3, .c 29, .c 5, .c 3, .c 23, .c 13, .c 3, .c 5, .c 11, .c 3, .c 61,
  .p pv7 [pv2,pv3,pv7,pv103,pv317], .c 3, .c 31, .c 7, .c 3, .p pv3 [pv2,pv23,pv29,pv257], .c 5,
  .c 3, .c 11, .c 79, .c 3, .c 5, .c 953, .c 3, .c 173, .c 17, .c 3, .c 7, .c 659, .c 3, .c 13,
  .c 5, .c 3, .p pv2 [pv2,pv342847], .c 7, .c 3,
]
private theorem h0167c12 : checkBlock 1371139 128 b0167c12 = true := by
  decide +kernel

private def b0167c13 : List Row := [
  .c 5, .p pv7 [pv2,pv3,pv13,pv59,pv149], .c 3, .c 19, .c 11, .c 3, .c 17, .c 13, .c 3, .c 47,
  .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 277, .c 3, .p pv17 [pv2,pv5,pv137143], .c 7, .c 3,
  .c 181, .c 19, .c 3, .c 733, .c 5, .c 3, .p pv3 [pv2,pv13,pv13187], .c 73, .c 3, .c 5, .c 457,
  .c 3, .c 7, .c 61, .c 3, .c 23, .c 11, .c 3, .c 127, .c 5, .c 3, .c 37, .c 53, .c 3, .c 5,
  .c 13, .c 3, .c 11, .p pv5 [pv2,pv3,pv17,pv83], .c 3, .c 29, .p pv23 [pv2,pv3,pv179,pv1277],
  .c 3, .c 7, .c 5, .c 3, .c 17, .p pv13 [pv2,pv3,pv5,pv7,pv311], .c 3, .c 5, .c 7, .c 3, .c 373,
  .c 383, .c 3, .c 1069, .c 577, .c 3, .c 31, .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv22859],
  .c 3, .c 5, .c 109, .c 3, .p pv11 [pv2,pv5,pv27431], .c 19, .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv685781], .c 5, .c 3, .p pv3 [pv2,pv11,pv7793], .c 43, .c 3, .c 5, .c 17, .c 3,
  .p pv3 [pv2,pv5,pv7,pv97,pv101], .p pv3 [pv2,pv3,pv23,pv3313], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv114299], .c 3, .p pv3 [pv2,pv171449], .c 5, .c 3, .p pv11 [pv2,pv79,pv8681],
  .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv228601], .c 3, .c 17, .c 29, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv181,pv421], .c 3, .c 11, .c 5, .c 3, .c 7, .c 269, .c 3, .c 5, .c 797, .c 3,
  .p pv3 [pv2,pv5,pv53,pv647], .c 7, .c 3, .p pv5 [pv2,pv61,pv11243], .c 71,
]
private theorem h0167c13 : checkBlock 1371395 128 b0167c13 = true := by
  decide +kernel

private def b0167c14 : List Row := [
  .c 3, .p pv2 [pv2,pv139,pv2467], .c 5, .c 3, .c 317, .p pv13 [pv2,pv3,pv5,pv22861], .c 3, .c 5,
  .c 11, .c 3, .c 7, .c 223, .c 3, .c 79, .c 17, .c 3, .p pv2 [pv2,pv13,pv52757], .c 5, .c 3,
  .c 11, .c 59, .c 3, .c 5, .c 23, .c 3, .c 37, .p pv3 [pv2,pv3,pv228617], .c 3, .c 61, .c 157,
  .c 3, .c 7, .c 5, .c 3, .c 31, .c 13, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv17,pv8069],
  .c 11, .c 3, .c 41, .c 359, .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv7,pv48991], .c 499, .c 3,
  .c 5, .c 89, .c 3, .c 227, .p pv2 [pv2,pv3,pv7,pv19,pv191], .c 3, .p pv5 [pv2,pv11,pv23,pv2711],
  .c 7, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv41,pv16729], .c 17, .c 3, .c 5, .c 29, .c 3, .c 71,
  .c 521, .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv271,pv2531], .c 5, .c 3, .c 59, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv29,pv73], .c 3, .c 11, .c 859, .c 3, .p pv2 [pv2,pv293,pv2341], .c 43, .c 3,
  .c 1109, .c 5, .c 3, .c 7, .p pv47 [pv2,pv3,pv5,pv1429], .c 3, .c 5, .c 107, .c 3, .c 13, .c 7,
  .c 3, .c 19, .c 569, .c 3, .p pv5 [pv2,pv71,pv9661], .c 5, .c 3, .c 463, .c 97, .c 3, .c 5,
  .c 13, .c 3, .c 7, .c 17, .c 3, .c 11, .c 73, .c 3, .p pv2 [pv2,pv67,pv5119], .c 5, .c 3,
  .p pv7 [pv2,pv11,pv5669], .c 41, .c 3, .c 5,
]
private theorem h0167c14 : checkBlock 1371651 128 b0167c14 = true := by
  decide +kernel

private def b0167c15 : List Row := [
  .c 83, .c 3, .p pv7 [pv2,pv5,pv137191], .p pv5 [pv2,pv3,pv57163], .c 3, .c 17, .c 349, .c 3,
  .c 7, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 7, .c 3, .c 823,
  .p pv11 [pv2,pv3,pv11,pv13,pv41], .c 3, .p pv2 [pv2,pv685973], .p pv2 [pv2,pv3,pv114329], .c 3,
  .c 11, .c 5, .c 3, .c 67, .c 29, .c 3, .c 5, .c 31, .c 3, .c 19, .c 23, .c 3, .c 47, .c 7, .c 3,
  .c 41, .c 5, .c 3, .p pv2 [pv2,pv227,pv1511], .p pv3 [pv2,pv3,pv5,pv19,pv29,pv83], .c 3, .c 5,
  .c 11, .c 3, .c 43, .c 389, .c 3, .c 7, .c 19, .c 3, .c 241, .c 5, .c 3, .c 11, .c 7, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv67,pv3413], .c 3, .c 563, .c 13, .c 3, .c 193, .c 421, .c 3,
  .p pv2 [pv2,pv7,pv23,pv4261], .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv3049], .c 3, .c 5, .c 857,
  .c 3, .c 107, .c 7, .c 3, .c 919, .c 139, .c 3, .c 61, .c 5, .c 3, .p pv7 [pv2,pv686039],
  .p pv11 [pv2,pv3,pv5,pv5717], .c 3, .c 5, .c 17, .c 3, .c 7, .c 67, .c 3,
  .p pv3 [pv2,pv11,pv1949], .c 239, .c 3, .p pv5 [pv2,pv686051], .c 5, .c 3,
  .p pv3 [pv2,pv37,pv73,pv127], .c 13, .c 3, .c 5, .c 53, .c 3, .c 17, .c 19, .c 3,
  .p pv7 [pv2,pv7,pv98009], .c 11, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv17,pv40357], .c 149,
  .c 3, .c 5, .c 7, .c 3, .c 11, .c 31, .c 3, .c 23, .c 113, .c 3,
]
private theorem h0167c15 : checkBlock 1371907 128 b0167c15 = true := by
  decide +kernel

private def b0167c16 : List Row := [
  .c 13, .c 5, .c 3, .c 269, .p pv3 [pv2,pv3,pv5,pv53,pv863], .c 3, .c 5, .c 433, .c 3, .c 73,
  .p pv5 [pv2,pv3,pv7,pv37,pv883], .c 3, .p pv2 [pv2,pv101,pv6793], .c 7, .c 3, .c 29, .c 5, .c 3,
  .c 19, .c 109, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv17,pv1223], .c 3,
  .p pv2 [pv2,pv5,pv7,pv19603], .c 367, .c 3, .c 7, .c 37, .c 3, .c 17, .c 5, .c 3, .c 41, .c 7,
  .c 3, .c 5, .c 19, .c 3, .c 13, .p pv2 [pv2,pv3,pv228707], .c 3, .c 673, .c 23, .c 3,
  .p pv2 [pv2,pv7,pv49009], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 13, .c 3,
  .p pv31 [pv2,pv5,pv41,pv3347], .c 7, .c 3, .c 31, .c 677, .c 3, .c 11, .c 5, .c 3, .c 383,
  .c 17, .c 3, .c 5, .c 163, .c 3, .c 7, .p pv3 [pv2,pv3,pv43,pv197], .c 3,
  .p pv2 [pv2,pv13,pv47,pv1123], .c 29, .c 3, .c 19, .c 5, .c 3, .c 13, .c 743, .c 3, .c 5, .c 11,
  .c 3, .p pv7 [pv2,pv5,pv37,pv3709], .c 1063, .c 3, .c 157, .c 31, .c 3, .c 7, .c 5, .c 3, .c 11,
  .c 19, .c 3, .c 5, .c 7, .c 3, .c 67, .p pv2 [pv2,pv3,pv127,pv1801], .c 3, .c 29,
  .p pv7 [pv2,pv3,pv28591], .c 3, .p pv2 [pv2,pv103,pv3331], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv61,pv1607], .c 641, .c 3, .c 5, .c 23, .c 3, .p pv11 [pv2,pv5,pv137239],
  .c 11, .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv686201], .c 5, .c 3, .c 173,
  .p pv2 [pv2,pv3,pv5,pv13,pv17,pv23], .c 3, .c 5, .p pv11 [pv2,pv3,pv1787],
]
private theorem h0167c16 : checkBlock 1372163 128 b0167c16 = true := by
  decide +kernel

private def b0167c17 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv7,pv9803], .c 13, .c 3, .c 7, .c 397, .c 3, .c 23, .c 5, .c 3, .c 61,
  .c 7, .c 3, .c 5, .c 47, .c 3, .p pv2 [pv2,pv5,pv27449], .c 97, .c 3, .c 359, .c 11, .c 3,
  .c 31, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv11,pv4159], .c 3, .c 5, .c 853, .c 3, .c 11,
  .c 7, .c 3, .c 131, .c 101, .c 3, .p pv2 [pv2,pv11,pv31193], .c 5, .c 3, .c 197, .c 13, .c 3,
  .c 5, .c 613, .c 3, .c 7, .c 467, .c 3, .c 43, .c 1039, .c 3, .c 181, .c 5, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv5,pv45751], .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv1733], .c 3, .c 19,
  .p pv7 [pv2,pv3,pv228757], .c 3, .c 11, .p pv7 [pv2,pv3,pv23,pv4973], .c 3, .c 7, .c 5, .c 3,
  .p pv11 [pv2,pv11,pv89,pv701], .c 61, .c 3, .c 5, .c 7, .c 3, .c 23, .c 167, .c 3, .c 239,
  .c 13, .c 3, .p pv5 [pv2,pv173,pv3967], .c 5, .c 3, .c 37, .c 11, .c 3, .c 5, .c 17, .c 3,
  .c 337, .c 43, .c 3, .p pv5 [pv2,pv653,pv1051], .c 7, .c 3, .c 11, .c 5, .c 3, .c 73,
  .p pv2 [pv2,pv3,pv5,pv22877], .c 3, .c 5, .p pv2 [pv2,pv3,pv37,pv229], .c 3, .c 13,
  .p pv5 [pv2,pv3,pv57193], .c 3, .c 7, .c 41, .c 3, .c 71, .c 5, .c 3, .c 31, .c 7, .c 3, .c 5,
  .c 11, .c 3, .p pv2 [pv2,pv5,pv68633], .c 23, .c 3, .p pv2 [pv2,pv686333], .c 227, .c 3,
  .p pv3 [pv2,pv7,pv383],
]
private theorem h0167c17 : checkBlock 1372419 128 b0167c17 = true := by
  decide +kernel

private def b0167c18 : List Row := [
  .c 5, .c 3, .c 7, .c 103, .c 3, .c 5, .c 503, .c 3, .c 101, .c 7, .c 3, .c 659, .c 17, .c 3,
  .c 107, .c 5, .c 3, .c 13, .c 31, .c 3, .c 5, .c 191, .c 3, .c 7, .c 11, .c 3,
  .p pv5 [pv2,pv686363], .c 47, .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv379,pv1811], .c 151, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv109,pv2099], .c 3, .c 179, .c 53, .c 3, .p pv3 [pv2,pv7,pv11,pv4457],
  .p pv3 [pv2,pv3,pv228793], .c 3, .c 7, .c 5, .c 3, .c 19, .p pv3 [pv2,pv3,pv5,pv7,pv2179], .c 3,
  .c 5, .c 7, .c 3, .c 389, .c 79, .c 3, .c 13, .c 11, .c 3, .c 1117, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv98057], .c 17, .c 3, .c 5, .c 19, .c 3, .c 11, .c 13, .c 3, .c 353, .c 7,
  .c 3, .c 47, .c 5, .c 3, .p pv2 [pv2,pv457,pv751], .c 29, .c 3, .c 5, .c 113, .c 3, .c 97,
  .p pv2 [pv2,pv3,pv25423], .c 3, .c 7, .p pv17 [pv2,pv3,pv37,pv773], .c 3, .c 487, .c 5, .c 3,
  .c 53, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv31,pv61], .c 3, .c 59, .c 809, .c 3, .c 11,
  .p pv17 [pv2,pv3,pv13,pv5867], .c 3, .c 19, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 31, .c 3,
  .c 199, .c 7, .c 3, .c 167, .c 733, .c 3, .p pv3 [pv2,pv53,pv1619], .c 5, .c 3, .c 941, .c 11,
  .c 3, .c 5, .c 61, .c 3,
]
private theorem h0167c18 : checkBlock 1372675 128 b0167c18 = true := by
  decide +kernel

private def b0167c19 : List Row := [
  .c 7, .p pv23 [pv2,pv3,pv11,pv3467], .c 3, .c 17, .c 23, .c 3, .c 11, .c 5, .c 3, .c 163,
  .p pv3 [pv2,pv3,pv5,pv113], .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv677], .c 3,
  .p pv3 [pv2,pv5,pv8581], .p pv3 [pv2,pv3,pv23,pv9949], .c 3, .c 41, .c 13, .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv19,pv36131], .p pv37 [pv2,pv3,pv5,pv7,pv467], .c 3, .c 5, .c 7, .c 3,
  .p pv11 [pv2,pv5,pv31,pv43,pv103], .c 587, .c 3, .c 19, .p pv3 [pv2,pv3,pv11,pv71,pv293], .c 3,
  .c 89, .c 5, .c 3, .c 11, .c 47, .c 3, .c 5, .c 691, .c 3, .c 13, .c 811, .c 3,
  .p pv2 [pv2,pv686513], .c 7, .c 3, .c 37, .c 5, .c 3, .c 17, .p pv7 [pv2,pv3,pv5,pv1907], .c 3,
  .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv7,pv3923], .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv47,pv541],
  .c 3, .c 29, .c 5, .c 3, .c 71, .c 7, .c 3, .c 5, .c 23, .c 3, .p pv3 [pv2,pv5,pv34327], .c 31,
  .c 3, .p pv7 [pv2,pv11,pv13,pv4801], .c 277, .c 3, .c 103, .c 5, .c 3, .c 7, .c 173, .c 3, .c 5,
  .c 17, .c 3, .c 19, .c 7, .c 3, .c 379, .c 11, .c 3, .c 23, .c 5, .c 3, .p pv3 [pv2,pv171641],
  .c 41, .c 3, .c 5, .p pv5 [pv2,pv3,pv28607], .c 3, .c 7, .c 1151, .c 3,
  .p pv2 [pv2,pv23,pv29851], .c 19, .c 3, .p pv3 [pv2,pv11,pv47,pv83], .c 5, .c 3,
  .p pv7 [pv2,pv17,pv40387], .p pv7 [pv2,pv3,pv5,pv11443], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv59,pv431], .c 3, .c 61, .p pv37 [pv2,pv3,pv41,pv2791], .c 3, .c 13, .c 29,
  .c 3, .c 7, .c 5,
]
private theorem h0167c19 : checkBlock 1372931 128 b0167c19 = true := by
  decide +kernel

private def b0167c20 : List Row := [
  .c 3, .p pv2 [pv2,pv211,pv1627], .p pv29 [pv2,pv3,pv5,pv7,pv13,pv503], .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv3433], .c 13, .c 3, .c 11, .c 17, .c 3, .c 41, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv11,pv37,pv241], .c 251, .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv13463], .c 3,
  .c 797, .p pv17 [pv2,pv3,pv7,pv61,pv67], .c 3, .c 29, .c 7, .c 3, .c 17, .c 5, .c 3, .c 1009,
  .c 11, .c 3, .c 5, .c 79, .c 3, .c 23, .c 19, .c 3, .c 7, .c 31, .c 3, .c 11, .c 5, .c 3,
  .c 157, .c 7, .c 3, .c 5, .c 197, .c 3, .c 43, .c 47, .c 3, .c 101, .c 67, .c 3, .c 727, .c 5,
  .c 3, .c 7, .c 17, .c 3, .c 5, .c 11, .c 3, .p pv17 [pv2,pv5,pv13,pv19,pv139], .c 7, .c 3,
  .c 491, .c 37, .c 3, .c 13, .c 5, .c 3, .c 11, .p pv13 [pv2,pv3,pv5,pv47,pv487], .c 3, .c 5,
  .p pv59 [pv2,pv3,pv13,pv5869], .c 3, .c 7, .c 23, .c 3, .p pv2 [pv2,pv521,pv659], .c 13, .c 3,
  .p pv19 [pv2,pv17,pv31,pv1303], .c 5, .c 3, .p pv3 [pv2,pv171671], .p pv3 [pv2,pv3,pv5,pv45779],
  .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv68669], .c 11, .c 3, .c 47, .c 53, .c 3, .c 7, .c 5,
  .c 3, .c 23, .c 83, .c 3, .c 5, .c 7, .c 3, .c 13, .c 17, .c 3, .p pv3 [pv2,pv11,pv15607],
  .p pv2 [pv2,pv3,pv41,pv1861], .c 3, .c 97, .c 5, .c 3, .c 1123,
  .p pv3 [pv2,pv3,pv5,pv17,pv2693], .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv29,pv37],
]
private theorem h0167c20 : checkBlock 1373187 128 b0167c20 = true := by
  decide +kernel

private def b0167c21 : List Row := [
  .c 839, .c 3, .c 17, .c 7, .c 3, .c 19, .c 5, .c 3, .c 41, .c 59, .c 3, .c 5, .c 179, .c 3,
  .c 11, .p pv5 [pv2,pv3,pv19,pv251], .c 3, .c 7, .c 881, .c 3, .p pv5 [pv2,pv11,pv149,pv419],
  .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv151,pv379], .c 3,
  .p pv2 [pv2,pv5,pv41,pv67], .c 1163, .c 3, .c 599, .c 109, .c 3, .c 683, .c 5, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv5,pv59,pv97], .c 3, .c 5, .c 29, .c 3, .p pv2 [pv2,pv5,pv137353], .c 7, .c 3,
  .c 11, .p pv2 [pv2,pv3,pv228923], .c 3, .p pv5 [pv2,pv229,pv2999], .c 5, .c 3, .c 17, .c 37,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv29,pv3947], .c 3, .c 7, .p pv3 [pv2,pv3,pv137,pv557], .c 3, .c 13,
  .c 1091, .c 3, .c 79, .c 5, .c 3, .c 31, .c 11, .c 3, .c 5, .c 823, .c 3,
  .p pv7 [pv2,pv5,pv137359], .c 13, .c 3, .c 431, .c 541, .c 3, .c 7, .c 5, .c 3, .c 181,
  .p pv3 [pv2,pv3,pv5,pv7,pv31,pv211], .c 3, .c 5, .c 7, .c 3, .c 773, .c 41, .c 3,
  .p pv2 [pv2,pv89,pv7717], .c 23, .c 3, .c 677, .c 5, .c 3, .p pv11 [pv2,pv7,pv59,pv1663], .c 31,
  .c 3, .c 5, .c 11, .c 3, .c 17, .c 829, .c 3, .c 1051, .c 7, .c 3, .c 641, .c 5, .c 3, .c 11,
  .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv114473], .c 3, .c 19, .p pv2 [pv2,pv3,pv283,pv809], .c 3,
  .c 7, .p pv19 [pv2,pv3,pv19079], .c 3, .c 503, .c 5, .c 3,
]
private theorem h0167c21 : checkBlock 1373443 128 b0167c21 = true := by
  decide +kernel

private def b0167c22 : List Row := [
  .c 37, .c 7, .c 3, .c 5, .c 53, .c 3, .c 103, .c 11, .c 3, .p pv2 [pv2,pv47,pv7307], .c 17,
  .c 3, .c 13, .c 5, .c 3, .c 7, .c 79, .c 3, .c 5, .c 139, .c 3, .c 113, .c 7, .c 3, .c 499,
  .c 13, .c 3, .c 17, .c 5, .c 3, .c 29, .p pv47 [pv2,pv3,pv5,pv53], .c 3, .c 5, .c 23, .c 3,
  .c 7, .c 37, .c 3, .p pv3 [pv2,pv19,pv4519], .c 11, .c 3, .c 269, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv29,pv911], .c 509, .c 3, .c 5, .c 131, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv101,pv2267], .c 3, .c 43, .c 281, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv491,pv1399], .c 17, .c 3, .c 5, .c 7, .c 3, .c 409, .c 19, .c 3, .c 577,
  .p pv3 [pv2,pv3,pv17,pv13469], .c 3, .p pv2 [pv2,pv61,pv11261], .c 5, .c 3,
  .p pv3 [pv2,pv7,pv24533], .p pv13 [pv2,pv3,pv5,pv43,pv71], .c 3, .c 5, .c 47, .c 3,
  .p pv2 [pv2,pv5,pv73,pv941], .c 191, .c 3, .c 11, .c 7, .c 3, .p pv3 [pv2,pv17,pv5051], .c 5,
  .c 3, .c 13, .p pv23 [pv2,pv3,pv5,pv107], .c 3, .c 5, .p pv3 [pv2,pv3,pv127,pv601], .c 3,
  .p pv2 [pv2,pv5,pv7,pv19,pv1033], .c 43, .c 3, .c 7, .c 83, .c 3, .c 61, .c 5, .c 3, .c 19,
  .c 7, .c 3, .c 5, .c 103, .c 3, .c 37, .c 17, .c 3, .c 163, .c 149, .c 3, .c 11, .c 5, .c 3,
  .c 7, .c 241, .c 3, .c 5, .c 19, .c 3, .c 23, .c 7,
]
private theorem h0167c22 : checkBlock 1373699 128 b0167c22 = true := by
  decide +kernel

private def b0167c23 : List Row := [
  .c 3, .c 13, .p pv11 [pv2,pv3,pv37,pv2063], .c 3, .c 887, .c 5, .c 3, .c 67, .c 181, .c 3, .c 5,
  .c 11, .c 3, .c 7, .c 13, .c 3, .c 107, .p pv47 [pv2,pv3,pv7,pv11,pv1487], .c 3, .c 1129, .c 5,
  .c 3, .c 11, .c 233, .c 3, .c 5, .p pv13 [pv2,pv3,pv73,pv3137], .c 3, .c 239, .c 31, .c 3,
  .c 397, .p pv2 [pv2,pv3,pv229003], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv431,pv797], .c 227,
  .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv34351], .c 11, .c 3, .c 79, .c 29, .c 3,
  .p pv2 [pv2,pv269,pv1277], .c 5, .c 3, .c 17, .c 13, .c 3, .c 5, .p pv13 [pv2,pv3,pv23,pv3319],
  .c 3, .c 89, .p pv5 [pv2,pv3,pv7,pv8179], .c 3, .p pv2 [pv2,pv11,pv17,pv167], .c 7, .c 3,
  .p pv2 [pv2,pv687041], .c 5, .c 3, .c 23, .c 643, .c 3, .c 5, .c 947, .c 3,
  .p pv2 [pv2,pv5,pv7,pv13,pv151], .c 67, .c 3, .c 7, .c 11, .c 3, .c 13, .c 5, .c 3, .c 557,
  .c 7, .c 3, .c 5, .c 17, .c 3, .c 11, .p pv5 [pv2,pv3,pv307,pv373], .c 3, .c 19, .c 13, .c 3,
  .c 37, .c 5, .c 3, .c 7, .c 43, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv19,pv41], .c 3, .c 17, .c 7,
  .c 3, .c 587, .c 59, .c 3, .p pv2 [pv2,pv343543], .c 5, .c 3, .c 257, .c 23, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv47,pv443], .c 3, .c 7, .c 113, .c 3, .c 11, .c 31, .c 3, .c 769, .c 5,
  .c 3, .p pv3 [pv2,pv11,pv61],
]
private theorem h0167c23 : checkBlock 1373955 128 b0167c23 = true := by
  decide +kernel

private def b0167c24 : List Row := [
  .p pv2 [pv2,pv3,pv5,pv15269], .c 3, .c 5, .c 13, .c 3, .c 157, .c 29, .c 3, .c 23, .c 17, .c 3,
  .c 7, .c 5, .c 3, .p pv11 [pv2,pv41,pv16759], .c 11, .c 3, .c 5, .c 7, .c 3, .c 19, .c 163,
  .c 3, .p pv3 [pv2,pv13,pv6607], .c 877, .c 3, .c 11, .c 5, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv5,pv19,pv2411], .c 3, .c 5, .p pv2 [pv2,pv3,pv71,pv1613], .c 3, .c 29,
  .c 563, .c 3, .c 59, .c 7, .c 3, .c 139, .c 5, .c 3, .p pv2 [pv2,pv73,pv9413],
  .p pv2 [pv2,pv3,pv5,pv509], .c 3, .c 5, .c 11, .c 3, .p pv7 [pv2,pv5,pv7,pv29,pv677],
  .p pv7 [pv2,pv3,pv173,pv331], .c 3, .c 7, .c 23, .c 3, .c 31, .c 5, .c 3, .c 11, .c 7, .c 3,
  .c 5, .c 389, .c 3, .p pv3 [pv2,pv5,pv11,pv6247], .c 53, .c 3, .c 13, .c 223, .c 3, .c 193,
  .c 5, .c 3, .c 7, .c 41, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv43,pv761], .c 3, .c 67, .c 7, .c 3,
  .p pv3 [pv2,pv149,pv1153], .p pv2 [pv2,pv3,pv157,pv1459], .c 3, .c 313, .c 5, .c 3, .c 449,
  .c 61, .c 3, .c 5, .c 29, .c 3, .c 7, .c 19, .c 3, .p pv5 [pv2,pv11,pv62473], .c 43, .c 3,
  .p pv2 [pv2,pv13,pv26431], .c 5, .c 3, .c 113, .c 47, .c 3, .c 5, .c 89, .c 3,
  .p pv7 [pv2,pv5,pv137443], .c 17, .c 3, .p pv2 [pv2,pv7,pv191,pv257], .c 11, .c 3, .c 7, .c 5,
  .c 3, .c 53, .c 13, .c 3, .c 5, .c 7, .c 3, .c 11, .c 293, .c 3,
]
private theorem h0167c24 : checkBlock 1374211 128 b0167c24 = true := by
  decide +kernel

private def b0167c25 : List Row := [
  .c 17, .c 197, .c 3, .p pv3 [pv2,pv11,pv15619], .c 5, .c 3, .c 19,
  .p pv17 [pv2,pv3,pv5,pv23,pv83], .c 3, .c 5, .c 601, .c 3, .c 809, .c 199, .c 3,
  .p pv3 [pv2,pv42953], .c 7, .c 3, .c 13, .c 5, .c 3, .c 31, .p pv3 [pv2,pv3,pv5,pv45817], .c 3,
  .c 5, .c 19, .c 3, .c 79, .c 59, .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv113,pv3041], .c 5, .c 3,
  .p pv2 [pv2,pv11,pv43,pv1453], .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv193,pv1187], .c 3,
  .p pv23 [pv2,pv5,pv37,pv743], .c 151, .c 3, .p pv2 [pv2,pv343639], .p pv3 [pv2,pv3,pv229093],
  .c 3, .c 83, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 167, .c 3, .c 13, .c 7, .c 3, .c 37,
  .p pv2 [pv2,pv3,pv38183], .c 3, .c 11, .c 5, .c 3, .c 109, .p pv11 [pv2,pv3,pv5,pv29,pv79],
  .c 3, .c 5, .c 13, .c 3, .c 7, .p pv2 [pv2,pv3,pv19,pv6029], .c 3, .p pv3 [pv2,pv171827],
  .p pv7 [pv2,pv3,pv7,pv23,pv1423], .c 3, .c 337, .c 5, .c 3, .c 29, .c 19, .c 3, .c 5, .c 11,
  .c 3, .c 23, .c 331, .c 3, .c 463, .c 409, .c 3, .c 7, .c 5, .c 3, .c 11, .c 37, .c 3, .c 5,
  .c 7, .c 3, .c 17, .p pv5 [pv2,pv3,pv13,pv2203], .c 3, .p pv2 [pv2,pv557,pv617], .c 79, .c 3,
  .p pv2 [pv2,pv687341], .c 5, .c 3, .c 41, .p pv3 [pv2,pv3,pv5,pv45823], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv61,pv313], .c 3, .c 263, .c 11, .c 3, .c 19, .c 7, .c 3,
  .p pv3 [pv2,pv227,pv757], .c 5, .c 3, .p pv11 [pv2,pv687359], .p pv19 [pv2,pv3,pv5,pv179],
]
private theorem h0167c25 : checkBlock 1374467 128 b0167c25 = true := by
  decide +kernel

private def b0167c26 : List Row := [
  .c 3, .c 5, .c 251, .c 3, .p pv2 [pv2,pv5,pv7,pv41,pv479], .c 23, .c 3, .c 7, .c 17, .c 3,
  .p pv5 [pv2,pv163,pv4217], .c 5, .c 3, .p pv2 [pv2,pv343687], .c 7, .c 3, .c 5, .c 31, .c 3,
  .p pv3 [pv2,pv5,pv34369], .c 13, .c 3, .c 53, .c 11, .c 3, .c 17, .c 5, .c 3, .c 7, .c 97, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv7,pv3637], .c 3, .c 11, .c 7, .c 3, .c 47, .c 619, .c 3, .c 29, .c 5,
  .c 3, .c 37, .c 397, .c 3, .c 5, .c 109, .c 3, .c 7, .c 149, .c 3, .p pv2 [pv2,pv687413],
  .c 317, .c 3, .p pv3 [pv2,pv29,pv2963], .c 5, .c 3, .c 43, .c 13, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv37,pv563], .c 3, .p pv2 [pv2,pv5,pv31,pv887], .c 41, .c 3, .c 11, .c 19,
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv11,pv31247], .c 23, .c 3, .c 5, .c 7, .c 3, .c 31, .c 37,
  .c 3, .p pv5 [pv2,pv687443], .c 787, .c 3, .c 13, .c 5, .c 3, .c 179, .c 11, .c 3, .c 5, .c 67,
  .c 3, .c 167, .c 101, .c 3, .c 23, .c 7, .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv85933], .c 311,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv59,pv971], .c 3, .p pv2 [pv2,pv5,pv7,pv23,pv61], .c 17, .c 3,
  .c 7, .c 631, .c 3, .p pv3 [pv2,pv171869], .c 5, .c 3, .c 613, .c 7, .c 3, .c 5, .c 11, .c 3,
  .c 13, .c 19, .c 3, .c 17,
]
private theorem h0167c26 : checkBlock 1374723 128 b0167c26 = true := by
  decide +kernel

private def b0167c27 : List Row := [
  .c 53, .c 3, .p pv5 [pv2,pv7,pv98213], .c 5, .c 3, .c 7, .c 577, .c 3, .c 5, .c 13, .c 3, .c 61,
  .c 7, .c 3, .p pv5 [pv2,pv29,pv151,pv157], .c 23, .c 3, .p pv2 [pv2,pv379,pv907], .c 5, .c 3,
  .p pv2 [pv2,pv223,pv3083], .p pv13 [pv2,pv3,pv5,pv7639], .c 3, .c 5, .c 1117, .c 3, .c 7, .c 11,
  .c 3, .p pv3 [pv2,pv13,pv31,pv853], .p pv19 [pv2,pv3,pv7,pv1559], .c 3, .p pv2 [pv2,pv687521],
  .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv89,pv103], .c 3, .c 5, .c 71, .c 3, .c 83,
  .p pv7 [pv2,pv3,pv13,pv17,pv61], .c 3, .c 31, .c 137, .c 3, .c 7, .c 5, .c 3, .c 17, .c 751,
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv199,pv691], .c 29, .c 3, .c 43, .c 11, .c 3,
  .p pv5 [pv2,pv687551], .c 5, .c 3, .p pv2 [pv2,pv7,pv67,pv733],
  .p pv29 [pv2,pv3,pv5,pv11,pv463], .c 3, .c 5, .p pv2 [pv2,pv3,pv114593], .c 3, .c 11, .c 61,
  .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv11,pv31253], .c 5, .c 3, .c 89,
  .p pv2 [pv2,pv3,pv5,pv13,pv41,pv43], .c 3, .c 5, .c 17, .c 3, .c 29, .c 13, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv419,pv547], .c 3, .c 19, .c 5, .c 3, .c 97, .c 7, .c 3, .c 5, .c 173, .c 3,
  .c 17, .c 43, .c 3, .c 11, .p pv11 [pv2,pv3,pv114599], .c 3, .c 23, .c 5, .c 3, .c 7, .c 19,
  .c 3, .c 5, .c 257, .c 3, .p pv13 [pv2,pv5,pv113,pv1217], .c 7, .c 3, .c 983,
  .p pv2 [pv2,pv3,pv13,pv653], .c 3, .p pv5 [pv2,pv31,pv41,pv541], .c 5, .c 3, .c 251, .c 11,
  .c 3,
]
private theorem h0167c27 : checkBlock 1374979 128 b0167c27 = true := by
  decide +kernel

private def b0167c28 : List Row := [
  .c 5, .p pv5 [pv2,pv3,pv38201], .c 3, .c 7, .p pv2 [pv2,pv3,pv11,pv67,pv311], .c 3, .c 73,
  .c 17, .c 3, .c 11, .c 5, .c 3, .c 859, .p pv2 [pv2,pv3,pv5,pv22921], .c 3, .c 5, .c 29, .c 3,
  .c 107, .c 569, .c 3, .c 19, .c 739, .c 3, .c 7, .c 5, .c 3, .c 199, .c 491, .c 3, .c 5, .c 7,
  .c 3, .c 827, .p pv13 [pv2,pv3,pv229217], .c 3, .p pv2 [pv2,pv61,pv11273], .c 13, .c 3,
  .p pv3 [pv2,pv43,pv1999], .c 5, .c 3, .c 11, .c 431, .c 3, .c 5, .c 37, .c 3, .c 23, .c 659,
  .c 3, .p pv3 [pv2,pv171917], .c 7, .c 3, .c 137, .c 5, .c 3, .c 59, .c 17, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv114613], .c 3, .c 13, .c 11, .c 3, .c 7, .c 131, .c 3,
  .p pv2 [pv2,pv19,pv18097], .c 5, .c 3, .p pv2 [pv2,pv107,pv6427], .c 7, .c 3, .c 5, .c 13, .c 3,
  .c 19, .c 73, .c 3, .c 269, .c 233, .c 3, .c 53, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv19,pv127], .c 3, .c 5, .p pv11 [pv2,pv3,pv7,pv2729], .c 3,
  .p pv2 [pv2,pv5,pv68771], .c 7, .c 3, .c 41, .c 11, .c 3, .p pv3 [pv2,pv171929], .c 5, .c 3,
  .c 13, .c 29, .c 3, .c 5, .c 719, .c 3, .c 7, .c 17, .c 3, .p pv3 [pv2,pv53,pv811], .c 151,
  .c 3, .c 317, .c 5, .c 3, .c 23, .c 109, .c 3, .c 5, .c 157, .c 3, .p pv3 [pv2,pv5,pv137,pv251],
  .c 71, .c 3, .c 17, .c 61,
]
private theorem h0167c28 : checkBlock 1375235 128 b0167c28 = true := by
  decide +kernel

private def b0167c29 : List Row := [
  .c 3, .c 7, .c 5, .c 3, .c 29, .c 31, .c 3, .c 5, .c 7, .c 3, .c 193,
  .p pv7 [pv2,pv3,pv37,pv1549], .c 3, .c 11, .c 101, .c 3, .c 173, .c 5, .c 3, .c 1153,
  .p pv2 [pv2,pv3,pv5,pv13,pv3527], .c 3, .c 5, .c 127, .c 3, .c 661, .c 13, .c 3,
  .p pv2 [pv2,pv687773], .c 7, .c 3, .c 311, .c 5, .c 3, .c 83, .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv229261], .c 3, .p pv7 [pv2,pv5,pv7,pv43,pv457], .c 463, .c 3, .c 7, .c 167,
  .c 3, .c 11, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv47,pv271], .c 3,
  .p pv3 [pv2,pv5,pv19,pv181], .c 229, .c 3, .c 23, .p pv17 [pv2,pv3,pv13,pv4409], .c 3, .c 43,
  .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 11, .c 3, .c 131, .c 7, .c 3, .p pv2 [pv2,pv331,pv1039],
  .p pv3 [pv2,pv3,pv11,pv19,pv1097], .c 3, .c 47, .c 5, .c 3, .c 11, .c 197, .c 3, .c 5, .c 17,
  .c 3, .c 7, .c 283, .c 3, .c 307, .p pv2 [pv2,pv3,pv7,pv53,pv103], .c 3, .c 13, .c 5, .c 3,
  .p pv7 [pv2,pv687839], .p pv7 [pv2,pv3,pv5,pv1433], .c 3, .c 5, .c 31, .c 3, .c 17, .c 11, .c 3,
  .c 37, .c 13, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv17,pv20231], .c 67, .c 3, .c 5, .c 7, .c 3,
  .c 53, .p pv2 [pv2,pv3,pv23,pv3323], .c 3, .p pv5 [pv2,pv11,pv62533], .p pv23 [pv2,pv3,pv28661],
  .c 3, .c 19, .c 5, .c 3, .p pv7 [pv2,pv7,pv13,pv7559], .c 769, .c 3, .c 5,
]
private theorem h0167c29 : checkBlock 1375491 128 b0167c29 = true := by
  decide +kernel

private def b0167c30 : List Row := [
  .p pv2 [pv2,pv3,pv167,pv1373], .c 3, .c 13, .c 263, .c 3, .p pv2 [pv2,pv343939], .c 7, .c 3,
  .c 541, .c 5, .c 3, .p pv3 [pv2,pv23,pv7477], .c 19, .c 3, .c 5, .c 13, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv467,pv491], .c 3, .c 7, .c 29, .c 3, .c 17, .c 5, .c 3,
  .p pv17 [pv2,pv109,pv6311], .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv107,pv2143], .c 3, .c 31,
  .p pv2 [pv2,pv3,pv12739], .c 3, .p pv5 [pv2,pv13,pv13229], .p pv2 [pv2,pv3,pv29,pv7907], .c 3,
  .p pv5 [pv2,pv7,pv101,pv139], .c 5, .c 3, .c 7, .c 47, .c 3, .c 5, .c 23, .c 3, .c 733, .c 7,
  .c 3, .c 11, .c 929, .c 3, .p pv2 [pv2,pv343963], .c 5, .c 3, .c 277, .c 17, .c 3, .c 5, .c 271,
  .c 3, .c 7, .c 31, .c 3, .p pv2 [pv2,pv29,pv409], .p pv3 [pv2,pv3,pv7,pv17,pv41,pv47], .c 3,
  .c 23, .c 5, .c 3, .c 853, .c 11, .c 3, .c 5, .c 193, .c 3, .p pv3 [pv2,pv5,pv13759], .c 599,
  .c 3, .c 13, .c 71, .c 3, .c 7, .c 5, .c 3, .c 37, .p pv31 [pv2,pv3,pv5,pv7,pv13], .c 3, .c 5,
  .c 7, .c 3, .c 211, .c 13, .c 3, .p pv3 [pv2,pv21499], .c 59, .c 3, .c 79, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv157,pv313], .p pv3 [pv2,pv3,pv5,pv9173], .c 3, .c 5, .c 11, .c 3, .c 19,
  .c 17, .c 3, .c 331, .c 7, .c 3, .c 179, .c 5, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv5,pv17,pv19,pv71], .c 3, .c 5, .p pv2 [pv2,pv3,pv53,pv4327], .c 3, .c 947,
  .c 37, .c 3, .c 7, .c 19, .c 3,
]
private theorem h0167c30 : checkBlock 1375747 128 b0167c30 = true := by
  decide +kernel

private def b0167c31 : List Row := [
  .p pv2 [pv2,pv397,pv1733], .c 5, .c 3, .p pv3 [pv2,pv172001], .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv109,pv263], .c 3, .c 23, .c 11, .c 3, .c 457, .c 89, .c 3,
  .p pv3 [pv2,pv7,pv6143], .c 5, .c 3, .c 7, .c 967, .c 3, .c 5, .c 359, .c 3, .c 71, .c 7, .c 3,
  .c 59, .c 31, .c 3, .c 13, .c 5, .c 3, .c 607, .p pv3 [pv2,pv3,pv5,pv45869], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv8821], .c 3, .c 7, .c 41, .c 3, .c 1093, .c 11, .c 3,
  .p pv2 [pv2,pv53,pv6491], .c 5, .c 3, .c 17, .c 79, .c 3, .c 5, .c 349, .c 3, .c 11, .c 19,
  .c 3, .c 1061, .c 383, .c 3, .c 7, .c 5, .c 3, .c 43, .p pv11 [pv2,pv3,pv5,pv7,pv6553], .c 3,
  .c 5, .c 7, .c 3, .c 13, .c 181, .c 3, .p pv2 [pv2,pv688073], .c 379, .c 3,
  .p pv3 [pv2,pv31,pv179], .c 5, .c 3, .c 23, .p pv7 [pv2,pv3,pv5,pv47,pv61], .c 3, .c 5, .c 13,
  .c 3, .p pv2 [pv2,pv5,pv19,pv7243], .p pv17 [pv2,pv3,pv7,pv43,pv127], .c 3, .c 11, .c 7, .c 3,
  .c 31, .c 5, .c 3, .c 19, .p pv3 [pv2,pv3,pv5,pv1699], .c 3, .c 5, .p pv5 [pv2,pv3,pv73,pv1571],
  .c 3, .c 17, .p pv2 [pv2,pv3,pv347,pv661], .c 3, .c 7, .c 163, .c 3, .p pv2 [pv2,pv344053],
  .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 19, .c 3, .p pv19 [pv2,pv5,pv137623], .c 251, .c 3,
  .p pv2 [pv2,pv97,pv3547], .c 139, .c 3, .c 11, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7],
]
private theorem h0167c31 : checkBlock 1376003 128 b0167c31 = true := by
  decide +kernel

def rows0167 : List Row :=
  b0167c00 ++ b0167c01 ++ b0167c02 ++ b0167c03 ++ b0167c04 ++ b0167c05 ++ b0167c06 ++ b0167c07 ++
  b0167c08 ++ b0167c09 ++ b0167c10 ++ b0167c11 ++ b0167c12 ++ b0167c13 ++ b0167c14 ++ b0167c15 ++
  b0167c16 ++ b0167c17 ++ b0167c18 ++ b0167c19 ++ b0167c20 ++ b0167c21 ++ b0167c22 ++ b0167c23 ++
  b0167c24 ++ b0167c25 ++ b0167c26 ++ b0167c27 ++ b0167c28 ++ b0167c29 ++ b0167c30 ++ b0167c31

attribute [local irreducible] checkBlock checkRows checkPrime

theorem checked0167 : checkBlock 1368067 4096 rows0167 = true :=
  checkBlock_append h0167c00 (
    checkBlock_append h0167c01 (
    checkBlock_append h0167c02 (
    checkBlock_append h0167c03 (
    checkBlock_append h0167c04 (
    checkBlock_append h0167c05 (
    checkBlock_append h0167c06 (
    checkBlock_append h0167c07 (
    checkBlock_append h0167c08 (
    checkBlock_append h0167c09 (
    checkBlock_append h0167c10 (
    checkBlock_append h0167c11 (
    checkBlock_append h0167c12 (
    checkBlock_append h0167c13 (
    checkBlock_append h0167c14 (
    checkBlock_append h0167c15 (
    checkBlock_append h0167c16 (
    checkBlock_append h0167c17 (
    checkBlock_append h0167c18 (
    checkBlock_append h0167c19 (
    checkBlock_append h0167c20 (
    checkBlock_append h0167c21 (
    checkBlock_append h0167c22 (
    checkBlock_append h0167c23 (
    checkBlock_append h0167c24 (
    checkBlock_append h0167c25 (
    checkBlock_append h0167c26 (
    checkBlock_append h0167c27 (
    checkBlock_append h0167c28 (
    checkBlock_append h0167c29 (
    checkBlock_append h0167c30 (
    h0167c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
