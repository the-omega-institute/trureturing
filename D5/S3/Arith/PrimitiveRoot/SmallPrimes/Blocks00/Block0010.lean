/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks00/Block0010
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks00/Block0010.checked0010
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table018

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0010c00 : List Row := [
  .c 17, .c 5, .c 3, .p pv3 [pv2,pv7,pv11,pv19], .p pv3 [pv2,pv3,pv5,pv2731], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv569], .c 3, .c 67, .p pv5 [pv2,pv3,pv7,pv1951], .c 3, .c 19, .c 7, .c 3,
  .p pv3 [pv2,pv13,pv197], .c 5, .c 3, .c 41, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv19,pv719],
  .c 3, .p pv2 [pv2,pv5,pv7,pv1171], .p pv2 [pv2,pv3,pv11,pv23], .c 3, .c 7, .c 73, .c 3, .c 11,
  .c 5, .c 3, .c 163, .c 7, .c 3, .c 5, .c 167, .c 3, .c 43, .p pv2 [pv2,pv3,pv79,pv173], .c 3,
  .p pv5 [pv2,pv131,pv313], .p pv13 [pv2,pv3,pv17,pv67], .c 3, .p pv11 [pv2,pv7,pv29,pv101], .c 5,
  .c 3, .c 7, .p pv31 [pv2,pv3,pv5,pv1367], .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv13,pv631],
  .c 7, .c 3, .p pv2 [pv2,pv20509], .p pv17 [pv2,pv3,pv11,pv113], .c 3, .c 13, .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv547], .c 3, .c 5, .c 31, .c 3, .c 7, .c 137, .c 3,
  .p pv2 [pv2,pv37,pv1109], .c 13, .c 3, .p pv3 [pv2,pv10259], .c 5, .c 3, .c 211, .c 79, .c 3,
  .c 5, .c 23, .c 3, .c 103, .c 11, .c 3, .c 53, .c 19, .c 3, .c 7, .c 5, .c 3, .c 47, .c 157,
  .c 3, .c 5, .c 7, .c 3, .c 13, .c 41, .c 3, .c 17, .p pv13 [pv2,pv3,pv29,pv59], .c 3, .c 23,
  .c 5, .c 3, .p pv7 [pv2,pv7,pv5867], .p pv7 [pv2,pv3,pv5,pv37], .c 3, .c 5, .c 13, .c 3, .c 113,
  .p pv5 [pv2,pv3,pv7,pv163], .c 3, .c 29, .c 7, .c 3, .p pv2 [pv2,pv41081], .c 5, .c 3, .c 127,
  .p pv2 [pv2,pv3,pv5,pv11,pv83], .c 3, .c 5, .c 37,
]
private theorem h0010c00 : checkBlock 81923 128 b0010c00 = true := by
  decide +kernel

private def b0010c01 : List Row := [
  .c 3, .c 11, .p pv23 [pv2,pv3,pv13697], .c 3, .c 7, .p pv11 [pv2,pv3,pv761], .c 3,
  .p pv5 [pv2,pv11,pv467], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv4567], .c 3,
  .c 229, .c 19, .c 3, .p pv3 [pv2,pv43,pv239], .p pv2 [pv2,pv3,pv71,pv193], .c 3,
  .p pv5 [pv2,pv7,pv839], .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv2741], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv11,pv89], .c 3, .p pv3 [pv2,pv5,pv257], .c 7, .c 3, .c 11, .c 233, .c 3,
  .c 83, .c 5, .c 3, .c 43, .p pv29 [pv2,pv3,pv5,pv457], .c 3, .c 5, .p pv2 [pv2,pv3,pv13711],
  .c 3, .c 7, .c 29, .c 3, .c 13, .p pv7 [pv2,pv3,pv7,pv653], .c 3, .c 107, .c 5, .c 3, .c 19,
  .c 11, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv823], .c 13, .c 3, .p pv2 [pv2,pv7,pv5879],
  .c 53, .c 3, .c 7, .c 5, .c 3, .c 263, .c 191, .c 3, .c 5, .c 7, .c 3, .c 17, .c 281, .c 3,
  .c 137, .p pv2 [pv2,pv3,pv13723], .c 3, .c 67, .c 5, .c 3, .p pv3 [pv2,pv7,pv17,pv173],
  .p pv3 [pv2,pv3,pv5,pv61], .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv29,pv71], .c 23, .c 3,
  .c 31, .c 7, .c 3, .p pv2 [pv2,pv20593], .c 5, .c 3, .c 11, .c 13, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv23,pv199], .c 3, .c 47, .p pv5 [pv2,pv3,pv3433], .c 3, .c 7, .c 17, .c 3,
  .c 19, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 73, .c 3, .p pv2 [pv2,pv5,pv13,pv317], .c 11,
  .c 3, .c 139, .c 31, .c 3, .c 13,
]
private theorem h0010c01 : checkBlock 82179 128 b0010c01 = true := by
  decide +kernel

private def b0010c02 : List Row := [
  .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 29, .c 3, .c 41, .c 7, .c 3, .p pv3 [pv2,pv11,pv937],
  .c 13, .c 3, .p pv5 [pv2,pv41231], .c 5, .c 3, .p pv2 [pv2,pv53,pv389],
  .p pv3 [pv2,pv3,pv5,pv2749], .c 3, .c 5, .c 67, .c 3, .c 7, .p pv2 [pv2,pv3,pv59,pv233], .c 3,
  .p pv5 [pv2,pv41243], .c 11, .c 3, .p pv2 [pv2,pv41,pv503], .c 5, .c 3,
  .p pv31 [pv2,pv13,pv19,pv167], .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv13751], .c 3, .c 11, .c 109,
  .c 3, .c 19, .c 179, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv2579],
  .p pv3 [pv2,pv3,pv5,pv7,pv131], .c 3, .c 5, .c 7, .c 3, .c 59, .c 197, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv2293], .c 3, .c 31, .c 5, .c 3, .p pv7 [pv2,pv7,pv5897],
  .p pv7 [pv2,pv3,pv5,pv43], .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv139], .c 3,
  .p pv13 [pv2,pv5,pv23,pv359], .c 71, .c 3, .c 11, .c 7, .c 3, .c 269, .c 5, .c 3, .c 13,
  .p pv11 [pv2,pv3,pv5,pv2753], .c 3, .c 5, .c 151, .c 3, .p pv3 [pv2,pv5,pv7,pv59], .c 17, .c 3,
  .c 7, .p pv11 [pv2,pv3,pv1721], .c 3, .p pv2 [pv2,pv19,pv1087], .c 5, .c 3,
  .p pv2 [pv2,pv101,pv409], .c 7, .c 3, .c 5, .c 53, .c 3, .c 19, .p pv5 [pv2,pv3,pv11,pv313],
  .c 3, .c 17, .c 23, .c 3, .c 11, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv19,pv29], .c 3, .c 5,
  .p pv31 [pv2,pv3,pv7,pv41], .c 3, .c 131, .c 7, .c 3, .c 13, .c 19, .c 3, .c 47, .c 5, .c 3,
  .c 29, .c 89, .c 3, .c 5, .c 11, .c 3,
]
private theorem h0010c02 : checkBlock 82435 128 b0010c02 = true := by
  decide +kernel

private def b0010c03 : List Row := [
  .c 7, .c 13, .c 3, .c 41, .p pv3 [pv2,pv3,pv7,pv11,pv179], .c 3, .c 191, .c 5, .c 3, .c 11,
  .c 107, .c 3, .c 5, .c 181, .c 3, .p pv19 [pv2,pv5,pv11,pv47], .p pv2 [pv2,pv3,pv17,pv811],
  .c 3, .p pv5 [pv2,pv7,pv19,pv311], .p pv7 [pv2,pv3,pv383], .c 3, .c 7, .c 5, .c 3, .c 17, .c 97,
  .c 3, .c 5, .c 7, .c 3, .c 83, .c 11, .c 3, .p pv2 [pv2,pv17,pv1217],
  .p pv3 [pv2,pv3,pv13,pv1061], .c 3, .p pv2 [pv2,pv41381], .c 5, .c 3, .c 37, .c 13, .c 3, .c 5,
  .c 23, .c 3, .p pv2 [pv2,pv5,pv4139], .c 19, .c 3, .p pv2 [pv2,pv11,pv53,pv71], .c 7, .c 3,
  .p pv3 [pv2,pv79,pv131], .c 5, .c 3, .p pv13 [pv2,pv41399], .c 31, .c 3, .c 5, .c 17, .c 3,
  .p pv2 [pv2,pv5,pv7,pv13], .p pv2 [pv2,pv3,pv67,pv103], .c 3, .c 7, .c 11, .c 3, .c 13, .c 5,
  .c 3, .c 113, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv59], .c 3, .c 11, .c 37, .c 3,
  .p pv5 [pv2,pv23,pv1801], .c 13, .c 3, .c 29, .c 5, .c 3, .c 7, .c 41, .c 3, .c 5, .c 173, .c 3,
  .c 79, .c 7, .c 3, .c 179, .c 67, .c 3, .p pv2 [pv2,pv29,pv1429], .c 5, .c 3,
  .p pv3 [pv2,pv13,pv797], .p pv2 [pv2,pv3,pv5,pv307], .c 3, .c 5, .c 19, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv41,pv337], .c 3, .c 11, .c 17, .c 3, .p pv3 [pv2,pv2591], .c 5, .c 3, .c 283,
  .c 101, .c 3, .c 5, .c 13, .c 3, .c 127, .c 239, .c 3, .c 197, .p pv2 [pv2,pv3,pv23,pv601],
  .c 3, .c 7, .c 5,
]
private theorem h0010c03 : checkBlock 82691 128 b0010c03 = true := by
  decide +kernel

private def b0010c04 : List Row := [
  .c 3, .c 109, .c 11, .c 3, .c 5, .c 7, .c 3, .c 23, .p pv3 [pv2,pv3,pv11,pv419], .c 3, .c 163,
  .c 29, .c 3, .c 11, .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv461], .c 3, .c 5, .c 31, .c 3,
  .c 37, .c 149, .c 3, .p pv2 [pv2,pv20749], .c 7, .c 3, .p pv2 [pv2,pv47,pv883], .c 5, .c 3,
  .p pv3 [pv2,pv1297], .c 17, .c 3, .c 5, .c 11, .c 3, .c 61, .p pv3 [pv2,pv3,pv101,pv137], .c 3,
  .c 7, .c 79, .c 3, .c 43, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv13841], .c 3,
  .c 53, .c 23, .c 3, .c 13, .p pv2 [pv2,pv3,pv109,pv127], .c 3, .p pv5 [pv2,pv7,pv17,pv349],
  .c 5, .c 3, .c 7, .p pv23 [pv2,pv3,pv5,pv13,pv71], .c 3, .c 5, .p pv53 [pv2,pv3,pv7,pv23,pv43],
  .c 3, .c 251, .c 7, .c 3, .c 19, .p pv7 [pv2,pv3,pv577], .c 3, .p pv2 [pv2,pv20773], .c 5, .c 3,
  .c 23, .p pv2 [pv2,pv3,pv5,pv277], .c 3, .c 5, .c 41, .c 3, .c 7, .c 17, .c 3,
  .p pv2 [pv2,pv11,pv1889], .c 43, .c 3, .c 101, .c 5, .c 3, .c 97, .c 59, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv433], .c 3, .c 71, .c 29, .c 3, .c 17, .c 11, .c 3, .c 7, .c 5, .c 3, .c 137,
  .c 13, .c 3, .c 5, .c 7, .c 3, .c 11, .c 31, .c 3, .p pv3 [pv2,pv37,pv281], .c 223, .c 3,
  .c 193, .c 5, .c 3, .c 41, .c 23, .c 3, .c 5, .c 271, .c 3, .c 19,
]
private theorem h0010c04 : checkBlock 82947 128 b0010c04 = true := by
  decide +kernel

private def b0010c05 : List Row := [
  .p pv2 [pv2,pv3,pv7,pv283], .c 3, .p pv5 [pv2,pv41603], .c 7, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv41609], .p pv7 [pv2,pv3,pv5,pv19,pv73], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv13,pv97], .c 3, .p pv7 [pv2,pv5,pv7,pv29,pv41], .p pv7 [pv2,pv3,pv17],
  .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv41621], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv3469], .c 3, .c 139, .c 53, .c 3, .p pv2 [pv2,pv17,pv31,pv79],
  .p pv2 [pv2,pv3,pv257], .c 3, .p pv3 [pv2,pv7,pv1487], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .c 37, .c 3, .c 13, .c 7, .c 3, .c 31, .p pv2 [pv2,pv3,pv13883], .c 3, .c 11, .c 5, .c 3,
  .c 227, .p pv13 [pv2,pv3,pv5,pv2777], .c 3, .c 5, .c 13, .c 3, .c 7, .c 97, .c 3, .c 103, .c 23,
  .c 3, .c 167, .c 5, .c 3, .p pv2 [pv2,pv41669], .p pv13 [pv2,pv3,pv5,pv463], .c 3, .c 5, .c 11,
  .c 3, .c 17, .c 19, .c 3, .p pv2 [pv2,pv7,pv13,pv229], .c 31, .c 3, .c 7, .c 5, .c 3, .c 11,
  .c 263, .c 3, .c 5, .c 7, .c 3, .c 199, .p pv3 [pv2,pv3,pv13,pv1069], .c 3, .c 61,
  .p pv2 [pv2,pv3,pv6949], .c 3, .c 89, .c 5, .c 3, .p pv7 [pv2,pv7,pv23,pv37],
  .p pv7 [pv2,pv3,pv5,pv139], .c 3, .c 5, .p pv5 [pv2,pv3,pv13901], .c 3, .c 239, .c 11, .c 3,
  .p pv3 [pv2,pv10427], .c 7, .c 3, .p pv5 [pv2,pv53,pv787], .c 5, .c 3, .c 19,
  .p pv17 [pv2,pv3,pv5,pv103], .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv409], .c 3, .c 181,
  .p pv2 [pv2,pv3,pv13907], .c 3, .c 7, .p pv13 [pv2,pv3,pv19,pv61], .c 3, .c 17, .c 5, .c 3,
]
private theorem h0010c05 : checkBlock 83203 128 b0010c05 = true := by
  decide +kernel

private def b0010c06 : List Row := [
  .p pv2 [pv2,pv41729], .c 7, .c 3, .c 5, .c 19, .c 3, .p pv11 [pv2,pv5,pv17,pv491], .c 13, .c 3,
  .p pv2 [pv2,pv41,pv509], .c 11, .c 3, .c 31, .c 5, .c 3, .c 7, .c 29, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv7,pv71], .c 3, .c 11, .c 7, .c 3, .c 113, .c 37, .c 3, .c 23, .c 5, .c 3,
  .c 47, .c 17, .c 3, .c 5, .c 101, .c 3, .c 7, .c 103, .c 3, .p pv3 [pv2,pv23,pv227], .c 139,
  .c 3, .c 19, .c 5, .c 3, .c 29, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv211], .c 3,
  .p pv3 [pv2,pv5,pv2089], .p pv2 [pv2,pv3,pv19,pv733], .c 3, .c 11, .c 193, .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv11,pv29,pv131], .c 19, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv13,pv643],
  .c 179, .c 3, .p pv2 [pv2,pv20899], .c 41, .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv7,pv1493],
  .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv67], .c 3, .p pv2 [pv2,pv5,pv37,pv113], .c 17, .c 3,
  .c 241, .c 7, .c 3, .c 11, .c 5, .c 3, .p pv19 [pv2,pv19,pv31,pv71],
  .p pv7 [pv2,pv3,pv5,pv17,pv41], .c 3, .c 5, .c 233, .c 3, .c 23, .p pv5 [pv2,pv3,pv6971], .c 3,
  .c 7, .c 269, .c 3, .p pv5 [pv2,pv59,pv709], .c 5, .c 3, .c 31, .c 7, .c 3, .c 5, .c 11, .c 3,
  .c 13, .c 67, .c 3, .c 53, .p pv13 [pv2,pv3,pv11,pv317], .c 3, .c 127, .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv31], .c 3, .c 5, .c 13, .c 3, .c 97, .c 7,
]
private theorem h0010c06 : checkBlock 83459 128 b0010c06 = true := by
  decide +kernel

private def b0010c07 : List Row := [
  .c 3, .p pv2 [pv2,pv20929], .p pv11 [pv2,pv3,pv4651], .c 3, .c 29, .c 5, .c 3, .c 101, .c 31,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv1163], .c 3, .c 7, .c 11, .c 3, .c 83, .c 89, .c 3, .c 61, .c 5,
  .c 3, .c 13, .p pv11 [pv2,pv3,pv5,pv349], .c 3, .c 5, .c 211, .c 3, .c 19,
  .p pv5 [pv2,pv3,pv13,pv179], .c 3, .p pv3 [pv2,pv7,pv11,pv17], .c 199, .c 3, .c 7, .c 5, .c 3,
  .c 23, .p pv3 [pv2,pv3,pv5,pv7,pv19], .c 3, .c 5, .c 7, .c 3, .c 47, .c 181, .c 3, .c 43, .c 11,
  .c 3, .p pv2 [pv2,pv23,pv911], .c 5, .c 3, .c 79, .c 109, .c 3, .c 5, .c 17, .c 3, .c 11,
  .p pv5 [pv2,pv3,pv7,pv499], .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv11,pv37,pv103], .c 5, .c 3,
  .c 191, .c 71, .c 3, .c 5, .p pv5 [pv2,pv3,pv1747], .c 3, .c 17, .c 13, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv29,pv241], .c 3, .p pv3 [pv2,pv2621], .c 5, .c 3, .c 37, .c 7, .c 3, .c 5,
  .c 149, .c 3, .p pv2 [pv2,pv5,pv8389], .c 43, .c 3, .c 11, .c 53, .c 3,
  .p pv5 [pv2,pv7,pv13,pv461], .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv2797], .c 3, .c 5, .c 31,
  .c 3, .p pv3 [pv2,pv5,pv1049], .c 7, .c 3, .c 23, .c 17, .c 3, .p pv2 [pv2,pv20983], .c 5, .c 3,
  .p pv2 [pv2,pv41969], .c 11, .c 3, .c 5, .c 127, .c 3, .c 7, .c 37, .c 3, .c 59, .c 113, .c 3,
  .c 11, .c 5, .c 3, .p pv3 [pv2,pv41],
]
private theorem h0010c07 : checkBlock 83715 128 b0010c07 = true := by
  decide +kernel

private def b0010c08 : List Row := [
  .c 131, .c 3, .c 5, .c 79, .c 3, .c 137, .p pv5 [pv2,pv3,pv13997], .c 3, .p pv2 [pv2,pv7,pv857],
  .c 47, .c 3, .c 7, .c 5, .c 3, .c 19, .c 167, .c 3, .c 5, .c 7, .c 3,
  .p pv11 [pv2,pv5,pv31,pv271], .c 29, .c 3, .p pv3 [pv2,pv59,pv89], .c 13, .c 3, .c 73, .c 5,
  .c 3, .c 11, .c 17, .c 3, .c 5, .c 19, .c 3, .c 31, .c 229, .c 3, .p pv5 [pv2,pv42023], .c 7,
  .c 3, .p pv2 [pv2,pv21013], .c 5, .c 3, .p pv2 [pv2,pv13,pv53,pv61], .p pv7 [pv2,pv3,pv5,pv467],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv14011], .c 3, .c 13, .c 11, .c 3, .c 7, .c 83, .c 3, .c 47, .c 5,
  .c 3, .p pv3 [pv2,pv23,pv457], .c 7, .c 3, .c 5, .c 13, .c 3, .c 37, .c 31, .c 3, .c 151,
  .c 241, .c 3, .c 19, .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv701], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv2003], .c 3, .p pv2 [pv2,pv5,pv47,pv179], .c 7, .c 3,
  .p pv3 [pv2,pv13,pv809], .c 11, .c 3, .p pv5 [pv2,pv42071], .c 5, .c 3, .c 13, .c 19, .c 3,
  .c 5, .c 23, .c 3, .c 7, .p pv2 [pv2,pv3,pv13,pv83], .c 3, .c 17, .c 73, .c 3, .c 41, .c 5,
  .c 3, .p pv2 [pv2,pv42089], .p pv2 [pv2,pv3,pv5,pv23,pv61], .c 3, .c 5, .c 29, .c 3,
  .p pv7 [pv2,pv5,pv8419], .c 59, .c 3, .c 269, .p pv11 [pv2,pv3,pv14033], .c 3, .c 7, .c 5, .c 3,
  .c 107, .p pv3 [pv2,pv3,pv5,pv7,pv401], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv4211],
  .p pv17 [pv2,pv3,pv4679], .c 3,
]
private theorem h0010c08 : checkBlock 83971 128 b0010c08 = true := by
  decide +kernel

private def b0010c09 : List Row := [
  .c 11, .p pv2 [pv2,pv3,pv7019], .c 3, .c 131, .c 5, .c 3, .p pv11 [pv2,pv7,pv11,pv547], .c 61,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv19,pv739], .c 3, .c 173, .c 13, .c 3, .c 109, .c 7, .c 3,
  .p pv5 [pv2,pv42131], .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .c 71, .c 3, .c 271, .c 89, .c 3,
  .c 7, .c 31, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv113,pv373], .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv14051], .c 3, .c 59, .p pv5 [pv2,pv3,pv1171], .c 3, .p pv2 [pv2,pv107,pv197],
  .p pv11 [pv2,pv3,pv13,pv23,pv47], .c 3, .c 37, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 11, .c 3,
  .c 19, .c 7, .c 3, .p pv2 [pv2,pv181,pv233], .p pv2 [pv2,pv3,pv11,pv71], .c 3, .c 67, .c 5,
  .c 3, .c 11, .c 29, .c 3, .c 5, .c 239, .c 3, .c 7, .c 139, .c 3, .p pv3 [pv2,pv53,pv199],
  .c 19, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv17,pv73], .p pv3 [pv2,pv3,pv5,pv29,pv97], .c 3,
  .c 5, .c 37, .c 3, .p pv3 [pv2,pv5,pv211], .c 11, .c 3, .p pv5 [pv2,pv7,pv6029], .c 13, .c 3,
  .c 7, .c 5, .c 3, .c 29, .p pv2 [pv2,pv3,pv5,pv7,pv67], .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv8443], .c 23, .c 3, .p pv2 [pv2,pv11,pv19,pv101], .c 17, .c 3,
  .p pv2 [pv2,pv42221], .c 5, .c 3, .p pv3 [pv2,pv7,pv13,pv29], .c 79, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv17,pv23], .c 3, .c 13, .p pv5 [pv2,pv3,pv7,pv2011], .c 3,
  .p pv2 [pv2,pv157,pv269], .c 7, .c 3, .c 17, .c 5, .c 3, .c 23, .p pv7 [pv2,pv3,pv5,pv11],
]
private theorem h0010c09 : checkBlock 84227 128 b0010c09 = true := by
  decide +kernel

private def b0010c10 : List Row := [
  .c 3, .c 5, .c 13, .c 3, .c 11, .c 19, .c 3, .c 7, .p pv2 [pv2,pv3,pv14083], .c 3,
  .p pv23 [pv2,pv11,pv23,pv167], .c 5, .c 3, .p pv2 [pv2,pv37,pv571], .c 7, .c 3, .c 5, .c 223,
  .c 3, .p pv3 [pv2,pv5,pv2113], .p pv2 [pv2,pv3,pv14087], .c 3, .c 181, .c 137, .c 3,
  .p pv2 [pv2,pv7,pv3019], .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 59, .c 3,
  .p pv19 [pv2,pv5,pv19,pv89], .c 7, .c 3, .c 11, .p pv3 [pv2,pv3,pv17,pv829], .c 3, .c 103, .c 5,
  .c 3, .c 19, .c 23, .c 3, .c 5, .c 83, .c 3, .c 7, .c 41, .c 3, .c 251,
  .p pv2 [pv2,pv3,pv7,pv19,pv53], .c 3, .c 29, .c 5, .c 3, .c 31, .c 11, .c 3, .c 5, .c 19, .c 3,
  .c 211, .c 191, .c 3, .c 13, .c 37, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv21157],
  .p pv17 [pv2,pv3,pv5,pv7,pv13,pv31], .c 3, .c 5, .c 7, .c 3, .c 53, .c 13, .c 3, .c 47,
  .p pv13 [pv2,pv3,pv3527], .c 3, .p pv2 [pv2,pv21163], .c 5, .c 3, .p pv2 [pv2,pv7,pv6047],
  .c 31, .c 3, .c 5, .c 11, .c 3, .c 227, .p pv11 [pv2,pv3,pv7], .c 3, .c 17, .c 7, .c 3, .c 19,
  .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv941], .c 3, .c 5, .p pv11 [pv2,pv3,pv3529], .c 3,
  .p pv2 [pv2,pv5,pv7,pv11], .c 71, .c 3, .c 7, .c 23, .c 3, .p pv3 [pv2,pv10589], .c 5, .c 3,
  .p pv13 [pv2,pv42359], .c 7, .c 3, .c 5, .c 193, .c 3, .p pv2 [pv2,pv5,pv37,pv229], .c 11, .c 3,
  .p pv3 [pv2,pv331],
]
private theorem h0010c10 : checkBlock 84483 128 b0010c10 = true := by
  decide +kernel

private def b0010c11 : List Row := [
  .c 101, .c 3, .c 83, .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv113], .c 3, .c 5, .c 131, .c 3,
  .p pv7 [pv2,pv5,pv13,pv163], .c 7, .c 3, .c 29, .c 103, .c 3, .c 13, .c 5, .c 3, .c 17, .c 149,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv1087], .c 3, .c 7, .p pv5 [pv2,pv3,pv3533], .c 3, .c 19,
  .c 11, .c 3, .c 137, .c 5, .c 3, .p pv3 [pv2,pv10601], .p pv3 [pv2,pv3,pv5,pv11,pv257], .c 3,
  .c 5, .c 89, .c 3, .c 11, .c 271, .c 3, .p pv2 [pv2,pv7,pv73,pv83], .c 41, .c 3, .c 7, .c 5,
  .c 3, .c 43, .c 37, .c 3, .c 5, .c 7, .c 3, .c 13, .c 53, .c 3, .p pv3 [pv2,pv10607],
  .p pv2 [pv2,pv3,pv14143], .c 3, .c 113, .c 5, .c 3, .p pv3 [pv2,pv7,pv433],
  .p pv3 [pv2,pv3,pv5,pv23,pv41], .c 3, .c 5, .c 13, .c 3, .c 17, .c 29, .c 3, .c 11, .c 7, .c 3,
  .c 23, .c 5, .c 3, .c 73, .c 59, .c 3, .c 5, .c 197, .c 3, .c 19, .p pv5 [pv2,pv3,pv29,pv61],
  .c 3, .c 7, .p pv3 [pv2,pv3,pv14153], .c 3, .c 163, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 157,
  .c 3, .c 29, .c 173, .c 3, .p pv2 [pv2,pv42473], .c 17, .c 3, .c 11, .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv59], .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv17], .c 3, .c 31, .c 7, .c 3,
  .p pv3 [pv2,pv47,pv113], .p pv2 [pv2,pv3,pv4721], .c 3, .c 17, .c 5, .c 3, .c 37,
  .p pv3 [pv2,pv3,pv5,pv2833], .c 3,
]
private theorem h0010c11 : checkBlock 84739 128 b0010c11 = true := by
  decide +kernel

private def b0010c12 : List Row := [
  .c 5, .c 11, .c 3, .c 7, .c 167, .c 3, .c 13, .p pv13 [pv2,pv3,pv7,pv11,pv23], .c 3, .c 151,
  .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv13,pv109], .c 3, .c 5, .p pv2 [pv2,pv3,pv37,pv383],
  .c 3, .c 23, .c 13, .c 3, .p pv2 [pv2,pv7,pv3037], .c 277, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv10631], .c 17, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv4253], .c 11, .c 3,
  .c 257, .c 97, .c 3, .c 241, .c 5, .c 3, .c 149, .p pv7 [pv2,pv3,pv5,pv709], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv29,pv163], .c 3, .p pv17 [pv2,pv5,pv67,pv127], .p pv2 [pv2,pv3,pv7,pv1013],
  .c 3, .c 43, .c 7, .c 3, .p pv5 [pv2,pv17,pv2503], .c 5, .c 3, .p pv2 [pv2,pv21277], .c 13,
  .c 3, .c 5, .c 47, .c 3, .p pv53 [pv2,pv5,pv7,pv19], .c 23, .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv21283], .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv23,pv617], .c 3,
  .c 11, .c 17, .c 3, .c 31, .p pv3 [pv2,pv3,pv19,pv83], .c 3, .c 13, .c 5, .c 3, .c 7, .c 53,
  .c 3, .c 5, .c 19, .c 3, .c 103, .c 7, .c 3, .c 17, .c 13, .c 3, .p pv3 [pv2,pv23,pv463], .c 5,
  .c 3, .p pv7 [pv2,pv41,pv1039], .p pv41 [pv2,pv3,pv5,pv71], .c 3, .c 5, .c 139, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv263], .c 3, .c 11, .c 31, .c 3, .p pv5 [pv2,pv42611], .c 5, .c 3,
  .p pv3 [pv2,pv11,pv13,pv149], .c 29, .c 3, .c 5, .p pv2 [pv2,pv3,pv7103], .c 3, .c 13,
  .p pv3 [pv2,pv3,pv14207], .c 3, .p pv5 [pv2,pv7,pv6089], .c 163,
]
private theorem h0010c12 : checkBlock 84995 128 b0010c12 = true := by
  decide +kernel

private def b0010c13 : List Row := [
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv47,pv907], .c 11, .c 3, .c 5, .c 7, .c 3, .c 71, .c 269,
  .c 3, .c 53, .c 107, .c 3, .c 11, .c 5, .c 3, .c 17, .c 19, .c 3, .c 5,
  .p pv41 [pv2,pv3,pv1777], .c 3, .c 197, .p pv5 [pv2,pv3,pv7,pv677], .c 3, .c 23, .c 7, .c 3,
  .p pv3 [pv2,pv31,pv43], .c 5, .c 3, .c 13, .c 41, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv7,pv23,pv53], .p pv5 [pv2,pv3,pv13,pv547], .c 3, .c 7, .c 61, .c 3, .c 31,
  .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv11,pv97],
  .p pv3 [pv2,pv3,pv41,pv347], .c 3, .c 19, .p pv17 [pv2,pv3,pv3557], .c 3, .c 59, .c 5, .c 3,
  .c 7, .p pv11 [pv2,pv3,pv5,pv1423], .c 3, .c 5, .c 103, .c 3, .c 17, .c 7, .c 3, .c 13, .c 23,
  .c 3, .c 41, .c 5, .c 3, .c 223, .p pv2 [pv2,pv3,pv5,pv13,pv73], .c 3, .c 5, .c 229, .c 3, .c 7,
  .c 13, .c 3, .p pv2 [pv2,pv11,pv353], .p pv23 [pv2,pv3,pv7,pv113], .c 3, .c 37, .c 5, .c 3,
  .p pv7 [pv2,pv42719], .c 43, .c 3, .c 5, .p pv3 [pv2,pv3,pv47,pv101], .c 3,
  .p pv2 [pv2,pv5,pv1709], .p pv2 [pv2,pv3,pv7121], .c 3, .c 97, .c 11, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv23,pv929], .c 127, .c 3, .c 5, .c 7, .c 3, .c 11, .c 73, .c 3,
  .p pv5 [pv2,pv42743], .c 53, .c 3, .c 17, .c 5, .c 3, .c 193, .c 13, .c 3, .c 5,
]
private theorem h0010c13 : checkBlock 85251 128 b0010c13 = true := by
  decide +kernel

private def b0010c14 : List Row := [
  .c 37, .c 3, .c 233, .p pv5 [pv2,pv3,pv7,pv509], .c 3, .p pv2 [pv2,pv21379], .c 7, .c 3,
  .p pv2 [pv2,pv61,pv701], .c 5, .c 3, .c 31, .p pv29 [pv2,pv3,pv5,pv2851], .c 3, .c 5, .c 23,
  .c 3, .c 113, .c 131, .c 3, .c 7, .p pv2 [pv2,pv3,pv7129], .c 3, .c 13, .c 5, .c 3, .c 67, .c 7,
  .c 3, .c 5, .c 41, .c 3, .p pv2 [pv2,pv5,pv43,pv199], .c 83, .c 3, .p pv3 [pv2,pv19,pv563],
  .c 13, .c 3, .c 23, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv1019], .c 3,
  .p pv3 [pv2,pv5,pv107], .c 7, .c 3, .p pv5 [pv2,pv23,pv1861], .c 59, .c 3, .c 11, .c 5, .c 3,
  .p pv7 [pv2,pv13,pv37,pv89], .p pv11 [pv2,pv3,pv5,pv1427], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv67,pv71], .c 3, .c 7, .c 19, .c 3, .c 29, .p pv3 [pv2,pv3,pv7,pv2039], .c 3,
  .p pv2 [pv2,pv42821], .c 5, .c 3, .c 41, .c 97, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv4283], .c 17, .c 3, .p pv5 [pv2,pv7,pv29,pv211], .p pv2 [pv2,pv3,pv11,pv59],
  .c 3, .c 7, .c 5, .c 3, .c 11, .c 47, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv11,pv19,pv41],
  .c 67, .c 3, .c 17, .c 43, .c 3, .p pv5 [pv2,pv73,pv587], .c 5, .c 3, .c 13,
  .p pv61 [pv2,pv3,pv5,pv2857], .c 3, .c 5, .p pv2 [pv2,pv3,pv2381], .c 3, .c 23, .c 11, .c 3,
  .c 59, .c 7, .c 3, .p pv2 [pv2,pv21433], .c 5, .c 3, .c 83, .c 179, .c 3, .c 5, .c 19, .c 3,
  .p pv31 [pv2,pv5,pv7], .c 29, .c 3, .c 7, .c 191, .c 3,
]
private theorem h0010c14 : checkBlock 85507 128 b0010c14 = true := by
  decide +kernel

private def b0010c15 : List Row := [
  .c 139, .c 5, .c 3, .c 199, .c 7, .c 3, .c 5, .c 31, .c 3, .p pv2 [pv2,pv5,pv4289], .c 109,
  .c 3, .c 13, .c 11, .c 3, .p pv3 [pv2,pv7,pv383], .c 5, .c 3, .c 7, .c 239, .c 3, .c 5, .c 53,
  .c 3, .c 11, .c 7, .c 3, .p pv3 [pv2,pv17,pv631], .p pv2 [pv2,pv3,pv14303], .c 3, .c 19, .c 5,
  .c 3, .p pv2 [pv2,pv43,pv499], .p pv3 [pv2,pv3,pv5,pv2861], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv23,pv311], .c 3, .c 7, .p pv3 [pv2,pv3,pv19,pv251], .c 3,
  .p pv5 [pv2,pv42923], .c 293, .c 3, .p pv2 [pv2,pv13,pv127], .c 5, .c 3, .c 23, .c 19, .c 3,
  .c 5, .c 17, .c 3, .c 43, .c 79, .c 3, .c 11, .c 157, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv11,pv61], .c 13, .c 3, .c 5, .c 7, .c 3, .c 17, .p pv3 [pv2,pv3,pv103,pv139],
  .c 3, .c 271, .p pv2 [pv2,pv3,pv7159], .c 3, .c 53, .c 5, .c 3, .c 151, .c 11, .c 3, .c 5,
  .c 29, .c 3, .p pv2 [pv2,pv5,pv13,pv661], .p pv5 [pv2,pv3,pv7,pv11,pv31], .c 3, .c 19, .c 7,
  .c 3, .c 11, .c 5, .c 3, .c 61, .c 23, .c 3, .c 5, .c 43, .c 3, .c 67, .c 31, .c 3, .c 7, .c 13,
  .c 3, .c 149, .c 5, .c 3, .c 127, .c 7, .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv8599],
  .c 113, .c 3, .c 23, .p pv3 [pv2,pv3,pv11,pv1303], .c 3, .c 17, .c 5, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv5,pv47,pv61], .c 3, .c 5, .p pv5 [pv2,pv3,pv7],
]
private theorem h0010c15 : checkBlock 85763 128 b0010c15 = true := by
  decide +kernel

private def b0010c16 : List Row := [
  .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv43013], .p pv2 [pv2,pv3,pv67,pv107], .c 3, .c 227, .c 5,
  .c 3, .c 97, .c 139, .c 3, .c 5, .c 13, .c 3, .c 7, .c 11, .c 3, .c 47, .c 41, .c 3, .c 89,
  .c 5, .c 3, .p pv2 [pv2,pv21517], .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv797], .c 3, .c 59,
  .p pv2 [pv2,pv3,pv14347], .c 3, .c 31, .c 19, .c 3, .c 7, .c 5, .c 3, .c 13, .c 29, .c 3, .c 5,
  .c 7, .c 3, .p pv11 [pv2,pv5,pv79,pv109], .p pv5 [pv2,pv3,pv13,pv23], .c 3,
  .p pv2 [pv2,pv21529], .c 11, .c 3, .c 71, .c 5, .c 3, .c 43, .p pv2 [pv2,pv3,pv5,pv11,pv29],
  .c 3, .c 5, .p pv5 [pv2,pv3,pv37,pv97], .c 3, .c 11, .p pv3 [pv2,pv3,pv7,pv293], .c 3, .c 277,
  .c 7, .c 3, .c 101, .c 5, .c 3, .c 29, .p pv17 [pv2,pv3,pv5,pv359], .c 3, .c 5, .c 199, .c 3,
  .p pv7 [pv2,pv5,pv7,pv1231], .c 17, .c 3, .c 7, .p pv2 [pv2,pv3,pv53,pv271], .c 3,
  .p pv5 [pv2,pv41,pv1051], .c 5, .c 3, .c 79, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv653],
  .c 3, .p pv3 [pv2,pv5,pv431], .c 13, .c 3, .c 11, .p pv11 [pv2,pv3,pv449], .c 3, .c 73, .c 5,
  .c 3, .c 7, .c 151, .c 3, .c 5, .c 23, .c 3, .c 53, .c 7, .c 3, .c 83, .p pv3 [pv2,pv3,pv1597],
  .c 3, .p pv2 [pv2,pv13,pv31,pv107], .c 5, .c 3, .p pv3 [pv2,pv10781], .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv599], .c 3, .c 7, .p pv3 [pv2,pv3,pv11,pv1307], .c 3, .c 281,
  .p pv17 [pv2,pv3,pv7,pv13,pv79], .c 3, .c 11,
]
private theorem h0010c16 : checkBlock 86019 128 b0010c16 = true := by
  decide +kernel

private def b0010c17 : List Row := [
  .c 5, .c 3, .c 19, .c 13, .c 3, .c 5, .p pv11 [pv2,pv3,pv73,pv197], .c 3,
  .p pv2 [pv2,pv5,pv8629], .p pv2 [pv2,pv3,pv17,pv47], .c 3, .p pv3 [pv2,pv7,pv23,pv67], .c 211,
  .c 3, .c 7, .c 5, .c 3, .c 17, .p pv3 [pv2,pv3,pv5,pv7,pv137], .c 3, .c 5, .c 7, .c 3, .c 37,
  .p pv2 [pv2,pv3,pv14387], .c 3, .c 173, .c 131, .c 3, .c 13, .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv1439], .c 3, .c 5, .c 79, .c 3, .p pv13 [pv2,pv5,pv11,pv157],
  .p pv13 [pv2,pv3,pv7,pv257], .c 3, .p pv2 [pv2,pv21589], .c 7, .c 3, .c 67, .c 5, .c 3,
  .p pv3 [pv2,pv2699], .p pv3 [pv2,pv3,pv5,pv2879], .c 3, .c 5, .c 17, .c 3,
  .p pv3 [pv2,pv5,pv7,pv617], .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv23,pv313], .c 3, .c 19, .c 5,
  .c 3, .p pv11 [pv2,pv13,pv3323], .c 7, .c 3, .c 5, .c 71, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv19,pv379], .c 3, .c 103, .c 89, .c 3, .p pv5 [pv2,pv7,pv6173], .c 5, .c 3,
  .c 7, .c 19, .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv2161], .c 7, .c 3, .c 137, .c 11, .c 3,
  .p pv2 [pv2,pv21613], .c 5, .c 3, .c 31, .p pv2 [pv2,pv3,pv5,pv11,pv131], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv14411], .c 3, .c 7, .c 43, .c 3, .p pv2 [pv2,pv13,pv1663], .c 17, .c 3,
  .c 197, .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv31], .c 3, .c 5, .c 67, .c 3,
  .p pv2 [pv2,pv5,pv173], .c 23, .c 3, .c 19, .p pv7 [pv2,pv3,pv89], .c 3, .c 7, .c 5, .c 3,
  .c 241, .c 31, .c 3, .c 5, .c 7, .c 3,
]
private theorem h0010c17 : checkBlock 86275 128 b0010c17 = true := by
  decide +kernel

private def b0010c18 : List Row := [
  .p pv2 [pv2,pv5,pv17,pv509], .p pv2 [pv2,pv3,pv7211], .c 3, .c 11, .p pv3 [pv2,pv3,pv14423],
  .c 3, .c 37, .c 5, .c 3, .c 23, .c 41, .c 3, .c 5, .c 101, .c 3, .p pv3 [pv2,pv5,pv541], .c 107,
  .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv23,pv941], .c 5, .c 3, .p pv2 [pv2,pv73,pv593], .c 11,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv14431], .c 3, .c 131, .c 13, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv17,pv283], .c 3, .c 11, .c 5, .c 3, .c 257, .c 7, .c 3, .c 5, .c 37, .c 3,
  .c 19, .c 29, .c 3, .p pv2 [pv2,pv43313], .p pv2 [pv2,pv3,pv7219], .c 3, .c 41, .c 5, .c 3,
  .c 7, .c 23, .c 3, .c 5, .c 11, .c 3, .c 73, .c 7, .c 3, .c 193, .c 19, .c 3, .c 79, .c 5, .c 3,
  .c 11, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv31,pv233], .c 3, .c 7, .c 17, .c 3, .c 23,
  .p pv13 [pv2,pv3,pv7,pv43], .c 3, .p pv2 [pv2,pv21673], .c 5, .c 3, .c 181, .c 277, .c 3, .c 5,
  .c 31, .c 3, .p pv7 [pv2,pv5,pv13,pv23,pv29], .c 11, .c 3, .c 17, .p pv23 [pv2,pv3,pv97,pv149],
  .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv37,pv293], .c 43, .c 3, .c 5, .c 7, .c 3, .c 127,
  .p pv3 [pv2,pv3,pv61,pv79], .c 3, .c 223, .c 13, .c 3, .p pv3 [pv2,pv2711], .c 5, .c 3, .c 101,
  .c 53, .c 3, .c 5, .p pv3 [pv2,pv3,pv14461], .c 3, .p pv11 [pv2,pv5,pv8677], .c 19, .c 3,
  .c 107, .c 7, .c 3, .p pv5 [pv2,pv43391], .c 5,
]
private theorem h0010c18 : checkBlock 86531 128 b0010c18 = true := by
  decide +kernel

private def b0010c19 : List Row := [
  .c 3, .c 59, .c 229, .c 3, .c 5, .c 29, .c 3, .c 11, .c 61, .c 3, .c 7, .c 47, .c 3,
  .p pv2 [pv2,pv11,pv1973], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 13, .c 3, .c 31, .c 71, .c 3,
  .p pv2 [pv2,pv17,pv1277], .c 37, .c 3, .p pv2 [pv2,pv7,pv6203], .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv193], .c 3, .c 5, .p pv29 [pv2,pv3,pv7,pv11,pv47], .c 3,
  .p pv2 [pv2,pv5,pv43,pv101], .c 7, .c 3, .c 11, .p pv2 [pv2,pv3,pv19,pv127], .c 3, .c 109, .c 5,
  .c 3, .c 13, .c 283, .c 3, .c 5, .c 17, .c 3, .c 7, .c 31, .c 3, .c 113, .c 67, .c 3, .c 43,
  .c 5, .c 3, .c 233, .c 11, .c 3, .c 5, .c 23, .c 3, .c 17, .p pv2 [pv2,pv3,pv11,pv439], .c 3,
  .p pv5 [pv2,pv7,pv887], .p pv47 [pv2,pv3,pv1811], .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv17,pv2557], .c 227, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv37,pv47], .c 89,
  .c 3, .c 13, .p pv3 [pv2,pv3,pv4831], .c 3, .c 19, .c 5, .c 3, .p pv3 [pv2,pv7,pv1553], .c 29,
  .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv4349], .c 13, .c 3, .c 37, .c 7, .c 3,
  .p pv3 [pv2,pv5437], .c 5, .c 3, .c 11, .c 19, .c 3, .c 5, .c 167, .c 3,
  .p pv2 [pv2,pv5,pv7,pv11,pv113], .p pv5 [pv2,pv3,pv2417], .c 3, .c 7, .c 173, .c 3, .c 17, .c 5,
  .c 3, .c 29, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv7253], .c 3, .p pv3 [pv2,pv5,pv17],
]
private theorem h0010c19 : checkBlock 86787 128 b0010c19 = true := by
  decide +kernel

private def b0010c20 : List Row := [
  .c 11, .c 3, .c 61, .p pv19 [pv2,pv3,pv13,pv31], .c 3, .c 263, .c 5, .c 3, .c 7, .c 13, .c 3,
  .c 5, .c 83, .c 3, .p pv17 [pv2,pv5,pv8707], .c 7, .c 3, .c 19, .c 31, .c 3,
  .p pv2 [pv2,pv43541], .c 5, .c 3, .c 73, .c 17, .c 3, .c 5, .c 251, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv1613], .c 3, .p pv2 [pv2,pv97,pv449], .c 11, .c 3, .c 13, .c 5, .c 3,
  .p pv7 [pv2,pv43,pv1013], .p pv7 [pv2,pv3,pv5,pv11], .c 3, .c 5, .c 151, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv53,pv137], .c 3, .c 79, .c 13, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv21787],
  .p pv3 [pv2,pv3,pv5,pv7,pv83], .c 3, .c 5, .c 7, .c 3, .c 43, .c 101, .c 3, .c 67, .c 61, .c 3,
  .c 179, .c 5, .c 3, .p pv2 [pv2,pv7,pv13,pv479], .p pv2 [pv2,pv3,pv5,pv1453], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv1321], .c 3, .c 13, .c 17, .c 3, .c 11, .c 7, .c 3, .c 29, .c 5, .c 3,
  .c 37, .p pv13 [pv2,pv3,pv5,pv17,pv19], .c 3, .c 5, .c 13, .c 3, .p pv11 [pv2,pv5,pv7,pv89],
  .p pv3 [pv2,pv3,pv14537], .c 3, .c 7, .c 19, .c 3, .c 83, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5,
  .c 43, .c 3, .p pv2 [pv2,pv5,pv349], .p pv2 [pv2,pv3,pv11,pv661], .c 3, .p pv3 [pv2,pv13,pv839],
  .c 71, .c 3, .c 11, .c 5, .c 3, .c 7, .c 197, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv1039], .c 3,
  .p pv3 [pv2,pv5,pv1091], .c 7, .c 3, .c 191, .c 41, .c 3, .p pv2 [pv2,pv139,pv157], .c 5, .c 3,
]
private theorem h0010c20 : checkBlock 87043 128 b0010c20 = true := by
  decide +kernel

private def b0010c21 : List Row := [
  .p pv2 [pv2,pv43649], .c 67, .c 3, .c 5, .c 11, .c 3, .c 7, .p pv5 [pv2,pv3,pv17,pv107], .c 3,
  .p pv2 [pv2,pv83,pv263], .c 29, .c 3, .p pv2 [pv2,pv43661], .c 5, .c 3, .c 11, .c 23, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv1213], .c 3, .c 167, .c 19, .c 3, .c 13, .c 113, .c 3, .c 7, .c 5, .c 3,
  .p pv19 [pv2,pv31,pv1409], .c 199, .c 3, .c 5, .c 7, .c 3, .c 41, .c 11, .c 3, .c 23, .c 59,
  .c 3, .p pv5 [pv2,pv43691], .c 5, .c 3, .c 31, .c 281, .c 3, .c 5, .c 17, .c 3, .c 71,
  .p pv2 [pv2,pv3,pv7,pv2081], .c 3, .p pv5 [pv2,pv11,pv29,pv137], .c 7, .c 3, .c 61, .c 5, .c 3,
  .c 19, .p pv17 [pv2,pv3,pv5,pv31,pv47], .c 3, .c 5, .p pv2 [pv2,pv3,pv1619], .c 3, .c 17,
  .p pv5 [pv2,pv3,pv3643], .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv43721], .c 5, .c 3, .c 157,
  .c 7, .c 3, .c 5, .c 19, .c 3, .c 11, .c 149, .c 3, .c 47, .c 23, .c 3,
  .p pv5 [pv2,pv7,pv11,pv71], .c 5, .c 3, .c 7, .p pv29 [pv2,pv3,pv5], .c 3, .c 5, .c 89, .c 3,
  .p pv2 [pv2,pv5,pv13,pv673], .c 7, .c 3, .c 59, .c 17, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv131,pv167], .p pv3 [pv2,pv3,pv5,pv2917], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv13,pv17], .c 3, .c 7, .p pv2 [pv2,pv3,pv29,pv503], .c 3, .c 11, .c 13,
  .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv11,pv23,pv173], .p pv19 [pv2,pv3,pv5,pv1459], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv14591], .c 3, .c 29, .p pv5 [pv2,pv3,pv19],
]
private theorem h0010c21 : checkBlock 87299 128 b0010c21 = true := by
  decide +kernel

private def b0010c22 : List Row := [
  .c 3, .p pv3 [pv2,pv7,pv53,pv59], .p pv3 [pv2,pv3,pv14593], .c 3, .c 7, .c 5, .c 3, .c 67,
  .c 11, .c 3, .c 5, .c 7, .c 3, .c 13, .p pv3 [pv2,pv3,pv11,pv1327], .c 3, .p pv2 [pv2,pv43793],
  .p pv2 [pv2,pv3,pv811], .c 3, .c 11, .c 5, .c 3, .c 251, .c 17, .c 3, .c 5, .c 13, .c 3, .c 79,
  .p pv2 [pv2,pv3,pv7,pv149], .c 3, .c 41, .c 7, .c 3, .p pv5 [pv2,pv193,pv227], .c 5, .c 3,
  .p pv2 [pv2,pv19,pv1153], .p pv13 [pv2,pv3,pv5,pv23,pv127], .c 3, .c 5, .c 11, .c 3,
  .p pv3 [pv2,pv5,pv7,pv313], .p pv3 [pv2,pv3,pv541], .c 3, .c 7, .p pv17 [pv2,pv3,pv11,pv83],
  .c 3, .c 23, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 29, .c 3, .p pv11 [pv2,pv5,pv11,pv797],
  .c 73, .c 3, .c 43, .p pv3 [pv2,pv3,pv4871], .c 3, .p pv2 [pv2,pv7,pv6263], .c 5, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv5,pv37,pv79], .c 3, .c 5, .p pv17 [pv2,pv3,pv7,pv29], .c 3,
  .p pv2 [pv2,pv5,pv877], .c 7, .c 3, .c 229, .c 139, .c 3, .c 239, .c 5, .c 3,
  .p pv7 [pv2,pv61,pv719], .p pv11 [pv2,pv3,pv5,pv17,pv43], .c 3, .c 5, .c 37, .c 3, .c 7, .c 59,
  .c 3, .c 13, .p pv7 [pv2,pv3,pv7,pv2089], .c 3, .p pv5 [pv2,pv19,pv2309], .c 5, .c 3, .c 47,
  .p pv3 [pv2,pv3,pv5,pv13], .c 3, .c 5, .c 127, .c 3, .c 19, .c 13, .c 3,
  .p pv5 [pv2,pv7,pv6269], .c 11, .c 3, .c 7, .c 5, .c 3, .c 61, .c 41, .c 3, .c 5, .c 7, .c 3,
  .c 11, .p pv5 [pv2,pv3,pv31,pv59], .c 3, .p pv2 [pv2,pv47,pv467], .c 19, .c 3,
  .p pv5 [pv2,pv11,pv13,pv307], .c 5, .c 3, .c 277,
]
private theorem h0010c22 : checkBlock 87555 128 b0010c22 = true := by
  decide +kernel

private def b0010c23 : List Row := [
  .p pv2 [pv2,pv3,pv5,pv2927], .c 3, .c 5, .c 137, .c 3, .c 53, .c 31, .c 3, .c 71, .c 7, .c 3,
  .p pv3 [pv2,pv10979], .c 5, .c 3, .c 17, .c 13, .c 3, .c 5, .c 107, .c 3, .c 59,
  .p pv2 [pv2,pv3,pv7321], .c 3, .c 7, .c 103, .c 3, .c 41, .c 5, .c 3, .p pv2 [pv2,pv11,pv1997],
  .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv2441], .c 3, .p pv3 [pv2,pv5,pv13], .c 23, .c 3,
  .p pv5 [pv2,pv43943], .c 179, .c 3, .c 13, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 17, .c 3,
  .p pv29 [pv2,pv5,pv59,pv149], .c 7, .c 3, .p pv2 [pv2,pv31,pv709], .c 13, .c 3, .c 11, .c 5,
  .c 3, .c 23, .p pv41 [pv2,pv3,pv5,pv977], .c 3, .c 5, .c 47, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv14657], .c 3, .c 31, .c 37, .c 3, .c 281, .c 5, .c 3,
  .p pv7 [pv2,pv13,pv17,pv199], .p pv19 [pv2,pv3,pv5,pv733], .c 3, .c 5, .c 11, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv7331], .c 3, .p pv3 [pv2,pv7,pv1571], .c 97, .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv47 [pv2,pv3,pv5,pv7,pv419], .c 3, .c 5, .c 7, .c 3, .p pv19 [pv2,pv5,pv11],
  .p pv2 [pv2,pv3,pv4889], .c 3, .p pv5 [pv2,pv79,pv557], .c 17, .c 3, .c 283, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv6287], .c 23, .c 3, .c 5, .c 19, .c 3, .c 47, .c 11, .c 3,
  .p pv2 [pv2,pv13,pv1693], .c 7, .c 3, .c 17, .c 5, .c 3, .c 13, .c 191, .c 3, .c 5, .c 173,
  .c 3, .c 107, .c 83, .c 3,
]
private theorem h0010c23 : checkBlock 87811 128 b0010c23 = true := by
  decide +kernel

private def b0010c24 : List Row := [
  .c 7, .p pv2 [pv2,pv3,pv41,pv179], .c 3, .c 29, .c 5, .c 3, .p pv31 [pv2,pv47,pv937], .c 7,
  .c 3, .c 5, .c 59, .c 3, .c 137, .p pv2 [pv2,pv3,pv2447], .c 3, .c 37, .c 11, .c 3, .c 19, .c 5,
  .c 3, .c 7, .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv1049], .c 3, .c 11, .c 7, .c 3, .c 13,
  .p pv11 [pv2,pv3,pv17], .c 3, .c 31, .c 5, .c 3, .c 53, .c 19, .c 3, .c 5, .c 181, .c 3, .c 7,
  .c 13, .c 3, .c 199, .c 23, .c 3, .c 131, .c 5, .c 3, .p pv3 [pv2,pv103,pv107], .c 37, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv11,pv167], .c 3, .c 109, .c 163, .c 3, .c 11, .c 29, .c 3, .c 7, .c 5,
  .c 3, .c 89, .c 193, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv8821], .c 17, .c 3, .c 19, .c 47,
  .c 3, .p pv5 [pv2,pv44111], .c 5, .c 3, .c 83, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv19,pv43],
  .c 3, .p pv3 [pv2,pv5,pv1103], .c 79, .c 3, .c 17, .c 7, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv44129], .p pv2 [pv2,pv3,pv5,pv1471], .c 3, .c 5, .c 61, .c 3, .c 103, .c 41, .c 3,
  .c 7, .c 43, .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv31,pv89], .c 7, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv883], .c 227, .c 3, .c 233, .c 13, .c 3, .c 47, .c 5, .c 3, .c 7,
  .p pv43 [pv2,pv3,pv5,pv23],
]
private theorem h0010c24 : checkBlock 88067 128 b0010c24 = true := by
  decide +kernel

private def b0010c25 : List Row := [
  .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv701], .c 3, .c 19, .c 7, .c 3, .p pv3 [pv2,pv5521],
  .p pv3 [pv2,pv3,pv14723], .c 3, .c 23, .c 5, .c 3, .c 17, .c 53, .c 3, .c 5, .c 149, .c 3, .c 7,
  .c 11, .c 3, .c 97, .c 19, .c 3, .c 67, .c 5, .c 3, .p pv2 [pv2,pv44189], .c 31, .c 3, .c 5,
  .c 13, .c 3, .c 157, .c 37, .c 3, .p pv2 [pv2,pv7,pv11,pv41], .c 109, .c 3, .c 7, .c 5, .c 3,
  .c 211, .p pv2 [pv2,pv3,pv5,pv7,pv421], .c 3, .c 5, .c 7, .c 3, .c 29,
  .p pv11 [pv2,pv3,pv14737], .c 3, .p pv2 [pv2,pv13,pv19,pv179], .c 11, .c 3, .c 191, .c 5, .c 3,
  .c 13, .c 59, .c 3, .c 5, .c 241, .c 3, .c 11, .c 197, .c 3, .c 53, .c 7, .c 3,
  .p pv5 [pv2,pv11,pv4021], .c 5, .c 3, .p pv2 [pv2,pv17,pv1301], .p pv11 [pv2,pv3,pv5,pv983],
  .c 3, .c 5, .c 103, .c 3, .c 23, .c 19, .c 3, .c 7, .c 107, .c 3, .p pv2 [pv2,pv22123], .c 5,
  .c 3, .p pv2 [pv2,pv44249], .c 7, .c 3, .c 5, .c 67, .c 3, .c 61, .p pv11 [pv2,pv3,pv461], .c 3,
  .c 11, .c 17, .c 3, .p pv2 [pv2,pv7,pv6323], .c 5, .c 3, .c 7, .c 223, .c 3, .c 5, .c 29, .c 3,
  .c 37, .c 7, .c 3, .p pv2 [pv2,pv44273], .c 73, .c 3, .c 17, .c 5, .c 3, .c 19, .c 11, .c 3,
  .c 5, .c 31, .c 3, .c 7, .c 23, .c 3, .c 101,
]
private theorem h0010c25 : checkBlock 88323 128 b0010c25 = true := by
  decide +kernel

private def b0010c26 : List Row := [
  .c 283, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv22147], .p pv23 [pv2,pv3,pv5,pv2953], .c 3, .c 5,
  .c 19, .c 3, .c 41, .c 251, .c 3, .p pv5 [pv2,pv7,pv6329], .p pv17 [pv2,pv3,pv13,pv71], .c 3,
  .c 7, .c 5, .c 3, .c 23, .c 13, .c 3, .c 5, .c 7, .c 3, .c 263, .c 61, .c 3, .c 151, .c 137,
  .c 3, .p pv2 [pv2,pv23,pv41,pv47], .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv197], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv1847], .c 3, .p pv2 [pv2,pv5,pv11,pv13,pv31], .p pv3 [pv2,pv3,pv7,pv2111],
  .c 3, .p pv2 [pv2,pv43,pv1031], .c 7, .c 3, .c 13, .c 5, .c 3, .c 71,
  .p pv7 [pv2,pv3,pv5,pv739], .c 3, .c 5, .c 131, .c 3, .c 31, .c 11, .c 3, .c 7, .c 13, .c 3,
  .c 107, .c 5, .c 3, .c 43, .c 7, .c 3, .c 5, .c 79, .c 3, .p pv3 [pv2,pv5,pv1109], .c 17, .c 3,
  .c 83, .p pv17 [pv2,pv3,pv3697], .c 3, .c 89, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv17,pv29],
  .c 3, .c 5, .p pv7 [pv2,pv3,pv7,pv2113], .c 3, .c 13, .c 7, .c 3, .c 17, .c 11, .c 3, .c 37,
  .c 5, .c 3, .c 29, .p pv11 [pv2,pv3,pv5,pv11,pv269], .c 3, .c 5, .c 13, .c 3, .c 7, .c 47, .c 3,
  .c 19, .p pv2 [pv2,pv3,pv7,pv151], .c 3, .p pv3 [pv2,pv11,pv1009], .c 5, .c 3,
  .p pv7 [pv2,pv29,pv1531], .p pv7 [pv2,pv3,pv5,pv37], .c 3, .c 5, .p pv5 [pv2,pv3,pv19,pv41],
  .c 3, .p pv2 [pv2,pv5,pv83,pv107], .p pv5 [pv2,pv3,pv2467], .c 3, .p pv3 [pv2,pv7,pv13,pv61],
  .p pv2 [pv2,pv3,pv113,pv131], .c 3, .c 7, .c 5, .c 3, .c 13, .c 211, .c 3,
]
private theorem h0010c26 : checkBlock 88579 128 b0010c26 = true := by
  decide +kernel

private def b0010c27 : List Row := [
  .c 5, .c 7, .c 3, .c 73, .p pv2 [pv2,pv3,pv13,pv17,pv67], .c 3, .c 11, .c 23, .c 3,
  .p pv2 [pv2,pv97,pv229], .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv1481], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv4937], .c 3, .c 181, .p pv31 [pv2,pv3,pv7,pv23], .c 3, .c 31, .c 7, .c 3,
  .p pv2 [pv2,pv19,pv2339], .c 5, .c 3, .c 103, .c 11, .c 3, .c 5, .p pv11 [pv2,pv3,pv463], .c 3,
  .c 19, .p pv3 [pv2,pv3,pv11,pv449], .c 3, .c 7, .c 67, .c 3, .c 11, .c 5, .c 3,
  .p pv23 [pv2,pv23,pv1933], .c 7, .c 3, .c 5, .c 17, .c 3, .c 113, .c 13, .c 3,
  .p pv3 [pv2,pv11117], .c 19, .c 3, .c 29, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv593], .c 3,
  .c 5, .c 11, .c 3, .c 17, .c 7, .c 3, .c 43, .p pv7 [pv2,pv3,pv11,pv337], .c 3, .c 193, .c 5,
  .c 3, .c 11, .c 101, .c 3, .c 5, .c 23, .c 3, .c 7, .p pv5 [pv2,pv3,pv103], .c 3,
  .p pv2 [pv2,pv19,pv1171], .c 61, .c 3, .p pv2 [pv2,pv44501], .c 5, .c 3, .p pv3 [pv2,pv5563],
  .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv3709], .c 3, .p pv2 [pv2,pv5,pv4451], .c 11, .c 3, .c 127,
  .c 17, .c 3, .c 7, .c 5, .c 3, .c 269, .p pv29 [pv2,pv3,pv5,pv7,pv53], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv13,pv137], .c 19, .c 3, .p pv3 [pv2,pv11,pv23], .c 29, .c 3, .c 13, .c 5,
  .c 3, .p pv2 [pv2,pv7,pv3181], .p pv13 [pv2,pv3,pv5,pv2969], .c 3, .c 5, .c 281, .c 3, .c 229,
  .p pv2 [pv2,pv3,pv7,pv101], .c 3, .p pv5 [pv2,pv44543], .c 7,
]
private theorem h0010c27 : checkBlock 88835 128 b0010c27 = true := by
  decide +kernel

private def b0010c28 : List Row := [
  .c 3, .c 41, .c 5, .c 3, .c 139, .p pv2 [pv2,pv3,pv5,pv11], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv14851], .c 3, .c 11, .p pv7 [pv2,pv3,pv47,pv79], .c 3, .c 7,
  .p pv17 [pv2,pv3,pv4951], .c 3, .p pv5 [pv2,pv11,pv4051], .c 5, .c 3, .c 19, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv619], .c 3, .c 13, .c 97, .c 3, .c 239, .c 59, .c 3, .p pv3 [pv2,pv7,pv199],
  .c 5, .c 3, .c 7, .c 163, .c 3, .c 5, .c 13, .c 3, .c 23, .c 7, .c 3, .c 11, .c 257, .c 3,
  .c 101, .c 5, .c 3, .p pv2 [pv2,pv11,pv2027], .c 79, .c 3, .c 5, .c 191, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv14867], .c 3, .c 37, .p pv41 [pv2,pv3,pv7,pv59], .c 3, .p pv2 [pv2,pv22303],
  .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv4957], .c 3, .p pv19 [pv2,pv5,pv8923],
  .c 17, .c 3, .p pv2 [pv2,pv7,pv3187], .c 233, .c 3, .c 7, .c 5, .c 3, .c 31, .c 149, .c 3, .c 5,
  .c 7, .c 3, .p pv2 [pv2,pv5,pv4463], .c 23, .c 3, .c 17, .p pv2 [pv2,pv3,pv43,pv173], .c 3,
  .p pv3 [pv2,pv11159], .c 5, .c 3, .c 73, .c 19, .c 3, .c 5, .c 11, .c 3, .c 29,
  .p pv5 [pv2,pv3,pv7,pv1063], .c 3, .c 13, .c 7, .c 3, .p pv5 [pv2,pv44651], .c 5, .c 3, .c 11,
  .c 31, .c 3, .c 5, .p pv2 [pv2,pv3,pv827], .c 3, .c 179, .c 13, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv1861], .c 3, .c 157, .c 5, .c 3, .c 41, .c 7, .c 3, .c 5,
]
private theorem h0010c28 : checkBlock 89091 128 b0010c28 = true := by
  decide +kernel

private def b0010c29 : List Row := [
  .c 47, .c 3, .c 199, .c 11, .c 3, .c 19, .c 193, .c 3, .p pv5 [pv2,pv7,pv13,pv491], .c 5, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv5,pv331], .c 3, .c 5, .c 139, .c 3, .p pv2 [pv2,pv5,pv41,pv109], .c 7,
  .c 3, .p pv2 [pv2,pv11,pv17,pv239], .c 71, .c 3, .p pv3 [pv2,pv37,pv151], .c 5, .c 3,
  .p pv7 [pv2,pv44699], .c 13, .c 3, .c 5, .c 29, .c 3, .c 7, .p pv2 [pv2,pv3,pv7451], .c 3,
  .p pv3 [pv2,pv11177], .c 11, .c 3, .c 223, .c 5, .c 3, .c 37, .p pv11 [pv2,pv3,pv5,pv11,pv271],
  .c 3, .c 5, .c 17, .c 3, .c 11, .p pv2 [pv2,pv3,pv4969], .c 3, .c 23, .p pv11 [pv2,pv3,pv3727],
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv44729], .c 137, .c 3, .c 5, .c 7, .c 3, .c 17, .c 131,
  .c 3, .p pv2 [pv2,pv22369], .c 13, .c 3, .c 43, .c 5, .c 3, .c 109,
  .p pv2 [pv2,pv3,pv5,pv19,pv157], .c 3, .c 5, .c 31, .c 3, .p pv2 [pv2,pv5,pv179], .c 37, .c 3,
  .c 11, .c 7, .c 3, .p pv3 [pv2,pv67,pv167], .c 5, .c 3, .p pv11 [pv2,pv11,pv13,pv313],
  .p pv29 [pv2,pv3,pv5,pv373], .c 3, .c 5, .p pv3 [pv2,pv3,pv43,pv347], .c 3, .c 13,
  .p pv2 [pv2,pv3,pv829], .c 3, .c 7, .c 17, .c 3, .c 151, .c 5, .c 3, .c 149, .c 7, .c 3, .c 5,
  .c 13, .c 3, .p pv3 [pv2,pv5,pv2239], .p pv2 [pv2,pv3,pv11,pv23,pv59], .c 3,
  .p pv5 [pv2,pv19,pv2357], .c 43, .c 3, .c 11, .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .c 101, .c 3,
  .p pv13 [pv2,pv5,pv17,pv31], .c 7, .c 3, .p pv2 [pv2,pv13,pv1723], .p pv3 [pv2,pv3,pv109,pv137],
  .c 3,
]
private theorem h0010c29 : checkBlock 89347 128 b0010c29 = true := by
  decide +kernel

private def b0010c30 : List Row := [
  .p pv2 [pv2,pv71,pv631], .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv29,pv103], .c 3, .c 5, .c 11,
  .c 3, .c 7, .c 19, .c 3, .p pv2 [pv2,pv41,pv1093], .c 47, .c 3, .p pv3 [pv2,pv2801], .c 5, .c 3,
  .c 11, .c 17, .c 3, .c 5, .c 157, .c 3, .c 37, .p pv17 [pv2,pv3,pv31,pv241], .c 3,
  .p pv3 [pv2,pv7,pv1601], .p pv31 [pv2,pv3,pv17,pv293], .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv29,pv773], .p pv31 [pv2,pv3,pv5,pv7,pv61], .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv19,pv59], .c 11, .c 3, .c 13, .p pv7 [pv2,pv3,pv37,pv101], .c 3, .c 257, .c 5,
  .c 3, .c 19, .c 271, .c 3, .c 5, .c 109, .c 3, .c 283, .c 13, .c 3, .c 73, .c 7, .c 3, .c 23,
  .c 5, .c 3, .c 53, .c 61, .c 3, .c 5, .c 19, .c 3, .c 43, .c 17, .c 3, .c 7, .c 11, .c 3,
  .p pv3 [pv2,pv13,pv863], .c 5, .c 3, .p pv13 [pv2,pv44879], .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv4987], .c 3, .c 11, .c 107, .c 3, .c 17, .p pv2 [pv2,pv3,pv13,pv1151], .c 3,
  .p pv5 [pv2,pv7,pv11,pv53], .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv1069],
  .c 3, .c 89, .c 7, .c 3, .c 31, .p pv7 [pv2,pv3,pv1871], .c 3, .c 19, .c 5, .c 3,
  .p pv2 [pv2,pv44909], .p pv2 [pv2,pv3,pv5,pv499], .c 3, .c 5, .c 43, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv19,pv197], .c 3, .c 11, .p pv7 [pv2,pv3,pv7,pv23,pv31], .c 3, .c 13, .c 5,
  .c 3, .p pv3 [pv2,pv11,pv1021], .c 19, .c 3, .c 5, .c 59,
]
private theorem h0010c30 : checkBlock 89603 128 b0010c30 = true := by
  decide +kernel

private def b0010c31 : List Row := [
  .c 3, .c 23, .c 73, .c 3, .p pv2 [pv2,pv7,pv131], .c 13, .c 3, .c 7, .c 5, .c 3, .c 17, .c 11,
  .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv89,pv101], .c 241, .c 3, .p pv3 [pv2,pv17,pv661],
  .p pv2 [pv2,pv3,pv14983], .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv7,pv13,pv19], .c 47, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv59,pv127], .c 3, .c 13, .p pv3 [pv2,pv3,pv7,pv2141], .c 3, .c 19, .c 7,
  .c 3, .c 139, .c 5, .c 3, .p pv2 [pv2,pv193,pv233], .c 53, .c 3, .c 5, .c 11, .c 3, .c 293,
  .c 23, .c 3, .c 7, .p pv3 [pv2,pv3,pv11,pv29,pv47], .c 3, .p pv2 [pv2,pv31,pv1451], .c 5, .c 3,
  .c 11, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv23,pv163], .c 3, .c 17, .p pv3 [pv2,pv3,pv4999],
  .c 3, .c 29, .p pv2 [pv2,pv3,pv7499], .c 3, .c 31, .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5],
  .c 3, .c 5, .p pv7 [pv2,pv3,pv7,pv2143], .c 3, .p pv2 [pv2,pv5,pv9001], .c 7, .c 3,
  .p pv3 [pv2,pv29,pv97], .p pv29 [pv2,pv3,pv1667], .c 3, .p pv5 [pv2,pv19,pv23,pv103], .c 5,
  .c 3, .c 197, .p pv3 [pv2,pv3,pv5,pv3001], .c 3, .c 5, .c 179, .c 3, .c 7, .c 127, .c 3, .c 53,
  .c 17, .c 3, .p pv2 [pv2,pv47,pv479], .c 5, .c 3, .p pv2 [pv2,pv37,pv1217], .c 113, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv17,pv883], .c 3, .p pv7 [pv2,pv5,pv9007], .p pv17 [pv2,pv3,pv139], .c 3,
  .c 13, .c 11, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv11261], .c 23, .c 3, .c 5, .c 7, .c 3,
  .c 11, .c 13, .c 3, .p pv2 [pv2,pv45053], .c 251, .c 3, .c 97,
]
private theorem h0010c31 : checkBlock 89859 128 b0010c31 = true := by
  decide +kernel

def rows0010 : List Row :=
  b0010c00 ++ b0010c01 ++ b0010c02 ++ b0010c03 ++ b0010c04 ++ b0010c05 ++ b0010c06 ++ b0010c07 ++
  b0010c08 ++ b0010c09 ++ b0010c10 ++ b0010c11 ++ b0010c12 ++ b0010c13 ++ b0010c14 ++ b0010c15 ++
  b0010c16 ++ b0010c17 ++ b0010c18 ++ b0010c19 ++ b0010c20 ++ b0010c21 ++ b0010c22 ++ b0010c23 ++
  b0010c24 ++ b0010c25 ++ b0010c26 ++ b0010c27 ++ b0010c28 ++ b0010c29 ++ b0010c30 ++ b0010c31

theorem checked0010 : checkBlock 81923 4096 rows0010 = true :=
  checkBlock_append h0010c00 (
    checkBlock_append h0010c01 (
    checkBlock_append h0010c02 (
    checkBlock_append h0010c03 (
    checkBlock_append h0010c04 (
    checkBlock_append h0010c05 (
    checkBlock_append h0010c06 (
    checkBlock_append h0010c07 (
    checkBlock_append h0010c08 (
    checkBlock_append h0010c09 (
    checkBlock_append h0010c10 (
    checkBlock_append h0010c11 (
    checkBlock_append h0010c12 (
    checkBlock_append h0010c13 (
    checkBlock_append h0010c14 (
    checkBlock_append h0010c15 (
    checkBlock_append h0010c16 (
    checkBlock_append h0010c17 (
    checkBlock_append h0010c18 (
    checkBlock_append h0010c19 (
    checkBlock_append h0010c20 (
    checkBlock_append h0010c21 (
    checkBlock_append h0010c22 (
    checkBlock_append h0010c23 (
    checkBlock_append h0010c24 (
    checkBlock_append h0010c25 (
    checkBlock_append h0010c26 (
    checkBlock_append h0010c27 (
    checkBlock_append h0010c28 (
    checkBlock_append h0010c29 (
    checkBlock_append h0010c30 (
    h0010c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
