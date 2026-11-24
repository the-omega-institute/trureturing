/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks00/Block0009
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks00/Block0009.checked0009
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table017

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0009c00 : List Row := [
  .c 3, .c 11, .c 5, .c 3, .c 19, .c 37, .c 3, .c 5, .c 29, .c 3, .p pv13 [pv2,pv5,pv59], .c 131,
  .c 3, .p pv2 [pv2,pv18439], .c 7, .c 3, .c 17, .c 5, .c 3, .c 71, .p pv2 [pv2,pv3,pv5,pv2459],
  .c 3, .c 5, .c 11, .c 3, .c 89, .p pv3 [pv2,pv3,pv4099], .c 3, .c 7, .c 113, .c 3, .c 109, .c 5,
  .c 3, .c 11, .c 7, .c 3, .c 5, .c 23, .c 3, .c 31, .c 223, .c 3, .c 97, .p pv3 [pv2,pv3,pv1367],
  .c 3, .p pv5 [pv2,pv7,pv5273], .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 47, .c 3, .c 41, .c 7,
  .c 3, .p pv5 [pv2,pv36923], .p pv7 [pv2,pv3,pv17,pv181], .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv36929], .c 233, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv947], .c 3, .c 7, .c 31, .c 3,
  .p pv2 [pv2,pv11,pv23,pv73], .c 13, .c 3, .p pv2 [pv2,pv17,pv41,pv53], .c 5, .c 3, .c 37, .c 19,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv3079], .c 3, .c 67, .c 263, .c 3, .p pv2 [pv2,pv7,pv5279], .c 11,
  .c 3, .c 7, .c 5, .c 3, .c 193, .c 29, .c 3, .c 5, .c 7, .c 3, .c 11, .c 17, .c 3, .c 107,
  .p pv2 [pv2,pv3,pv12323], .c 3, .p pv5 [pv2,pv11,pv3361], .c 5, .c 3, .c 73,
  .p pv3 [pv2,pv3,pv5,pv17,pv29], .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv43], .c 37, .c 3,
  .c 17, .c 7, .c 3, .p pv2 [pv2,pv18493], .c 5, .c 3, .c 29, .c 167, .c 3, .c 5,
]
private theorem h0009c00 : checkBlock 73731 128 b0009c00 = true := by
  decide +kernel

private def b0009c01 : List Row := [
  .c 241, .c 3, .c 23, .c 61, .c 3, .c 7, .p pv31 [pv2,pv3,pv4111], .c 3, .c 43, .c 5, .c 3,
  .c 13, .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv257], .c 3, .p pv2 [pv2,pv5,pv3701], .c 79, .c 3,
  .p pv2 [pv2,pv37013], .c 181, .c 3, .c 101, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv41,pv43], .c 3, .p pv29 [pv2,pv5,pv1481], .c 7, .c 3, .c 103, .c 31, .c 3,
  .c 11, .c 5, .c 3, .c 17, .p pv19 [pv2,pv3,pv5,pv823], .c 3, .c 5, .p pv5 [pv2,pv3,pv6173],
  .c 3, .c 7, .c 23, .c 3, .c 13, .c 43, .c 3, .p pv2 [pv2,pv18523], .c 5, .c 3,
  .p pv2 [pv2,pv37049], .p pv2 [pv2,pv3,pv5,pv13,pv19], .c 3, .c 5, .c 11, .c 3, .c 37, .c 13,
  .c 3, .c 137, .c 19, .c 3, .c 7, .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv7,pv353], .c 3, .c 5,
  .c 7, .c 3, .c 151, .p pv5 [pv2,pv3,pv1373], .c 3, .c 53, .p pv2 [pv2,pv3,pv37,pv167], .c 3,
  .c 29, .c 5, .c 3, .p pv13 [pv2,pv7,pv5297], .p pv7 [pv2,pv3,pv5,pv103], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv47,pv263], .c 3, .c 17, .c 11, .c 3, .p pv3 [pv2,pv19,pv61], .c 7, .c 3,
  .c 31, .c 5, .c 3, .p pv2 [pv2,pv17,pv1091], .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv229], .c 3,
  .p pv11 [pv2,pv5,pv7,pv53], .p pv2 [pv2,pv3,pv83,pv149], .c 3, .c 7, .p pv19 [pv2,pv3,pv773],
  .c 3, .c 47, .c 5, .c 3, .p pv2 [pv2,pv43,pv863], .c 7, .c 3, .c 5, .c 199, .c 3,
  .p pv11 [pv2,pv5,pv13,pv571], .c 19, .c 3, .c 61, .c 11, .c 3,
]
private theorem h0009c01 : checkBlock 73987 128 b0009c01 = true := by
  decide +kernel

private def b0009c02 : List Row := [
  .c 13, .c 5, .c 3, .c 7, .c 41, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv13,pv17], .c 3, .c 11, .c 7,
  .c 3, .c 23, .c 13, .c 3, .c 17, .c 5, .c 3, .p pv7 [pv2,pv37139], .c 59, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv4127], .c 3, .c 7, .p pv5 [pv2,pv3,pv41,pv151], .c 3, .p pv3 [pv2,pv37,pv251],
  .c 191, .c 3, .c 67, .c 5, .c 3, .c 19, .p pv31 [pv2,pv3,pv5,pv2477], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv563], .c 3, .c 13, .p pv5 [pv2,pv3,pv4129], .c 3, .c 11, .c 239, .c 3,
  .c 7, .c 5, .c 3, .c 79, .c 17, .c 3, .c 5, .c 7, .c 3, .c 149, .p pv5 [pv2,pv3,pv1549], .c 3,
  .p pv2 [pv2,pv29,pv641], .c 23, .c 3, .p pv2 [pv2,pv37181], .c 5, .c 3, .c 31, .c 11, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv1033], .c 3, .p pv2 [pv2,pv5,pv3719], .p pv5 [pv2,pv3,pv7,pv11,pv23],
  .c 3, .c 73, .c 7, .c 3, .c 11, .c 5, .c 3, .c 13, .c 47, .c 3, .c 5, .c 37, .c 3,
  .p pv2 [pv2,pv5,pv7,pv1063], .p pv5 [pv2,pv3,pv13,pv53], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv79,pv157], .c 3, .c 19, .c 5, .c 3, .c 263, .c 7, .c 3, .c 5, .c 11, .c 3,
  .p pv3 [pv2,pv5,pv1861], .c 17, .c 3, .c 109, .p pv13 [pv2,pv3,pv11,pv47], .c 3,
  .p pv2 [pv2,pv7,pv2659], .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 113, .c 3,
  .p pv11 [pv2,pv5,pv11,pv677], .c 7, .c 3, .c 13, .c 71, .c 3, .c 211, .c 5, .c 3,
  .p pv3 [pv2,pv9311], .c 163, .c 3, .c 5, .c 23,
]
private theorem h0009c02 : checkBlock 74243 128 b0009c02 = true := by
  decide +kernel

private def b0009c03 : List Row := [
  .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv37253], .p pv2 [pv2,pv3,pv7,pv887], .c 3, .c 269, .c 5,
  .c 3, .c 43, .p pv13 [pv2,pv3,pv5,pv23], .c 3, .c 5, .p pv3 [pv2,pv3,pv12421], .c 3,
  .p pv2 [pv2,pv5,pv29,pv257], .c 73, .c 3, .c 19, .c 131, .c 3, .c 7, .c 5, .c 3, .c 127,
  .p pv11 [pv2,pv3,pv5,pv7,pv71], .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv233], .c 173, .c 3,
  .p pv5 [pv2,pv23,pv1621], .c 11, .c 3, .p pv2 [pv2,pv103,pv181], .c 5, .c 3, .c 17, .c 13, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv31,pv401], .c 3, .c 11, .c 97, .c 3, .p pv2 [pv2,pv17,pv1097], .c 7,
  .c 3, .c 61, .c 5, .c 3, .p pv3 [pv2,pv4663], .p pv2 [pv2,pv3,pv5,pv829], .c 3, .c 5, .c 29,
  .c 3, .c 71, .p pv3 [pv2,pv3,pv12437], .c 3, .c 7, .c 37, .c 3, .c 13, .c 5, .c 3, .c 101, .c 7,
  .c 3, .c 5, .c 17, .c 3, .c 19, .p pv2 [pv2,pv3,pv6221], .c 3, .c 11, .c 13, .c 3, .c 197, .c 5,
  .c 3, .c 7, .c 89, .c 3, .c 5, .c 53, .c 3, .c 17, .c 7, .c 3, .p pv5 [pv2,pv107,pv349], .c 19,
  .c 3, .c 113, .c 5, .c 3, .p pv2 [pv2,pv13,pv17], .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv12451],
  .c 3, .c 7, .p pv13 [pv2,pv3,pv11,pv283], .c 3, .p pv2 [pv2,pv18679],
  .p pv7 [pv2,pv3,pv7,pv593], .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv9341],
  .p pv2 [pv2,pv3,pv5,pv47,pv53], .c 3, .c 5, .c 13, .c 3, .c 31, .c 41, .c 3,
  .p pv2 [pv2,pv7,pv19,pv281], .c 17, .c 3, .c 7,
]
private theorem h0009c03 : checkBlock 74499 128 b0009c03 = true := by
  decide +kernel

private def b0009c04 : List Row := [
  .c 5, .c 3, .p pv11 [pv2,pv37379], .p pv19 [pv2,pv3,pv5,pv7,pv89], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv7477], .c 23, .c 3, .c 37, .p pv2 [pv2,pv3,pv11,pv103], .c 3, .c 17, .c 5,
  .c 3, .c 11, .c 29, .c 3, .c 5, .p pv5 [pv2,pv3,pv23,pv271], .c 3, .c 131, .c 19, .c 3, .c 239,
  .c 7, .c 3, .c 79, .c 5, .c 3, .c 23, .p pv11 [pv2,pv3,pv5,pv29,pv43], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv4157], .c 3, .p pv7 [pv2,pv5,pv7,pv1069], .c 11, .c 3, .c 7, .c 67, .c 3,
  .p pv2 [pv2,pv23,pv1627], .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv3119], .c 3,
  .p pv2 [pv2,pv5,pv19,pv197], .c 43, .c 3, .c 13, .p pv2 [pv2,pv3,pv17,pv367], .c 3,
  .p pv3 [pv2,pv7,pv191], .c 5, .c 3, .c 7, .c 103, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv1783], .c 3,
  .p pv2 [pv2,pv5,pv7489], .c 7, .c 3, .p pv3 [pv2,pv31,pv151], .c 11, .c 3,
  .p pv5 [pv2,pv17,pv2203], .c 5, .c 3, .c 173, .c 23, .c 3, .c 5, .c 19, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv12487], .c 3, .c 31, .p pv17 [pv2,pv3,pv7,pv223], .c 3,
  .p pv2 [pv2,pv11,pv13,pv131], .c 5, .c 3, .c 137, .p pv7 [pv2,pv3,pv5,pv1249], .c 3, .c 5,
  .c 149, .c 3, .c 241, .c 17, .c 3, .c 23, .p pv3 [pv2,pv3,pv13,pv31], .c 3, .c 7, .c 5, .c 3,
  .c 61, .c 13, .c 3, .c 5, .c 7, .c 3, .c 97, .c 167, .c 3, .c 11, .c 31, .c 3, .c 19, .c 5,
  .c 3, .c 37, .c 179, .c 3, .c 5, .c 107, .c 3,
]
private theorem h0009c04 : checkBlock 74755 128 b0009c04 = true := by
  decide +kernel

private def b0009c05 : List Row := [
  .p pv17 [pv2,pv5,pv13,pv577], .p pv2 [pv2,pv3,pv7,pv19,pv47], .c 3, .p pv3 [pv2,pv9377], .c 7,
  .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv18757], .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv37],
  .c 3, .p pv3 [pv2,pv5,pv7,pv67], .c 101, .c 3, .c 7, .c 13, .c 3, .c 11, .c 5, .c 3, .c 47,
  .c 7, .c 3, .c 5, .c 271, .c 3, .c 41, .c 37, .c 3, .c 193, .p pv3 [pv2,pv3,pv43,pv97], .c 3,
  .p pv2 [pv2,pv7,pv31,pv173], .c 5, .c 3, .c 7, .c 61, .c 3, .c 5, .c 11, .c 3, .c 13, .c 7,
  .c 3, .c 19, .p pv2 [pv2,pv3,pv11,pv569], .c 3, .c 31, .c 5, .c 3, .c 11, .c 43, .c 3, .c 5,
  .c 13, .c 3, .c 7, .p pv2 [pv2,pv3,pv2087], .c 3, .c 227, .c 29, .c 3, .c 163, .c 5, .c 3,
  .p pv2 [pv2,pv18787], .c 223, .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv1879], .c 11, .c 3,
  .p pv5 [pv2,pv7,pv13,pv59], .p pv7 [pv2,pv3,pv29], .c 3, .c 7, .c 5, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv5,pv7,pv179], .c 3, .c 5, .c 7, .c 3, .c 17, .p pv7 [pv2,pv3,pv13,pv241],
  .c 3, .c 29, .c 139, .c 3, .c 157, .c 5, .c 3, .p pv3 [pv2,pv7,pv17,pv79],
  .p pv2 [pv2,pv3,pv5,pv23,pv109], .c 3, .c 5, .p pv5 [pv2,pv3,pv1567], .c 3, .c 19,
  .p pv3 [pv2,pv3,pv7,pv199], .c 3, .p pv2 [pv2,pv29,pv1297], .c 7, .c 3, .c 23, .c 5, .c 3,
  .p pv13 [pv2,pv37619], .c 67, .c 3, .c 5, .c 47, .c 3, .c 11, .p pv2 [pv2,pv3,pv6271], .c 3,
  .c 7, .c 17, .c 3, .c 73, .c 5,
]
private theorem h0009c05 : checkBlock 75011 128 b0009c05 = true := by
  decide +kernel

private def b0009c06 : List Row := [
  .c 3, .p pv2 [pv2,pv31,pv607], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv41], .c 3, .c 83, .c 13,
  .c 3, .c 79, .p pv13 [pv2,pv3,pv3137], .c 3, .c 17, .c 5, .c 3, .c 7, .c 257, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv11,pv163], .c 3, .c 127, .c 7, .c 3, .c 11, .c 109, .c 3,
  .p pv2 [pv2,pv13,pv2897], .c 5, .c 3, .p pv3 [pv2,pv11,pv107], .c 71, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv43,pv73], .c 3, .c 7, .c 59, .c 3, .p pv2 [pv2,pv101,pv373], .c 151, .c 3,
  .p pv3 [pv2,pv9419], .c 5, .c 3, .c 179, .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv53,pv79], .c 3,
  .c 23, .c 19, .c 3, .p pv3 [pv2,pv7,pv673], .c 43, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv47,pv401], .p pv3 [pv2,pv3,pv5,pv7,pv359], .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv13,pv29], .p pv3 [pv2,pv3,pv59,pv71], .c 3, .p pv5 [pv2,pv37,pv1019], .c 73,
  .c 3, .c 13, .c 5, .c 3, .c 53, .c 199, .c 3, .c 5, .c 11, .c 3, .p pv19 [pv2,pv5,pv19,pv397],
  .c 241, .c 3, .p pv2 [pv2,pv18859], .c 7, .c 3, .c 37, .c 5, .c 3, .c 11, .c 197, .c 3, .c 5,
  .c 61, .c 3, .c 59, .c 17, .c 3, .c 7, .c 163, .c 3, .c 71, .c 5, .c 3,
  .p pv19 [pv2,pv13,pv2903], .c 7, .c 3, .c 5, .c 19, .c 3, .c 13, .c 11, .c 3, .c 17, .c 103,
  .c 3, .p pv5 [pv2,pv7,pv5393], .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv839], .c 3, .c 5, .c 13,
  .c 3, .p pv3 [pv2,pv5,pv59],
]
private theorem h0009c06 : checkBlock 75267 128 b0009c06 = true := by
  decide +kernel

private def b0009c07 : List Row := [
  .c 7, .c 3, .p pv5 [pv2,pv11,pv3433], .c 47, .c 3, .p pv2 [pv2,pv23,pv821], .c 5, .c 3,
  .p pv2 [pv2,pv179,pv211], .p pv2 [pv2,pv3,pv5,pv1259], .c 3, .c 5, .c 31, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv787], .c 3, .p pv2 [pv2,pv13,pv1453], .c 11, .c 3, .c 19, .c 5, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv5,pv11,pv229], .c 3, .c 5, .p pv17 [pv2,pv3,pv47,pv67], .c 3, .c 11,
  .p pv5 [pv2,pv3,pv13,pv17,pv19], .c 3, .c 131, .c 269, .c 3, .c 7, .c 5, .c 3, .c 17, .c 19,
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv7561], .c 83, .c 3, .p pv3 [pv2,pv17,pv139],
  .p pv2 [pv2,pv3,pv4201], .c 3, .c 47, .c 5, .c 3, .p pv2 [pv2,pv7,pv37,pv73], .c 53, .c 3, .c 5,
  .c 43, .c 3, .p pv3 [pv2,pv5,pv31,pv61], .c 67, .c 3, .c 11, .c 7, .c 3, .p pv2 [pv2,pv18913],
  .c 5, .c 3, .p pv2 [pv2,pv11,pv19,pv181], .c 29, .c 3, .c 5, .c 17, .c 3, .c 31, .c 13, .c 3,
  .c 7, .p pv13 [pv2,pv3,pv12613], .c 3, .p pv2 [pv2,pv79,pv479], .c 5, .c 3, .p pv3 [pv2,pv9461],
  .c 7, .c 3, .c 5, .c 59, .c 3, .c 17, .p pv5 [pv2,pv3,pv11,pv31,pv37], .c 3,
  .p pv2 [pv2,pv37853], .p pv2 [pv2,pv3,pv701], .c 3, .c 11, .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv631], .c 3, .c 5, .c 41, .c 3, .p pv2 [pv2,pv5,pv7573], .c 7, .c 3,
  .c 53, .c 23, .c 3, .p pv5 [pv2,pv37871], .c 5, .c 3, .c 211, .c 13, .c 3, .c 5, .c 11, .c 3,
  .c 7, .c 239, .c 3, .p pv5 [pv2,pv43,pv881], .c 17, .c 3, .p pv2 [pv2,pv19,pv997], .c 5, .c 3,
]
private theorem h0009c07 : checkBlock 75523 128 b0009c07 = true := by
  decide +kernel

private def b0009c08 : List Row := [
  .c 11, .p pv11 [pv2,pv3,pv5,pv421], .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv743], .c 3, .c 19,
  .p pv19 [pv2,pv3,pv1579], .c 3, .p pv2 [pv2,pv7,pv2707], .c 229, .c 3, .c 7, .c 5, .c 3, .c 41,
  .c 47, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv17,pv223], .c 11, .c 3, .c 191, .c 13, .c 3,
  .p pv3 [pv2,pv9479], .c 5, .c 3, .c 181, .c 149, .c 3, .c 5, .c 73, .c 3, .c 101,
  .p pv5 [pv2,pv3,pv7,pv43], .c 3, .c 31, .c 7, .c 3, .c 107, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv1459], .c 17, .c 3, .c 5, .c 23, .c 3, .c 13, .p pv2 [pv2,pv3,pv12647], .c 3,
  .c 7, .c 11, .c 3, .c 29, .c 5, .c 3, .c 71, .c 7, .c 3, .c 5, .c 13, .c 3, .c 11,
  .p pv5 [pv2,pv3,pv3163], .c 3, .c 89, .c 31, .c 3, .c 23, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv2531], .c 3, .c 5, .p pv29 [pv2,pv3,pv7,pv113], .c 3,
  .p pv2 [pv2,pv5,pv3797], .c 7, .c 3, .c 173, .c 53, .c 3, .c 151, .c 5, .c 3, .c 13, .c 37,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv1151], .c 3, .c 7, .c 17, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv7,pv67], .c 3, .p pv5 [pv2,pv37991], .c 5, .c 3, .p pv2 [pv2,pv11,pv157],
  .p pv11 [pv2,pv3,pv5,pv17,pv149], .c 3, .c 5, .p pv2 [pv2,pv3,pv2111], .c 3,
  .p pv3 [pv2,pv5,pv19], .p pv5 [pv2,pv3,pv53,pv239], .c 3, .c 17, .c 29, .c 3, .c 7, .c 5, .c 3,
  .c 19, .c 11, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv7603], .c 139,
]
private theorem h0009c08 : checkBlock 75779 128 b0009c08 = true := by
  decide +kernel

private def b0009c09 : List Row := [
  .c 3, .c 13, .p pv19 [pv2,pv3,pv19,pv23,pv29], .c 3, .c 11, .c 5, .c 3, .c 113, .c 59, .c 3,
  .c 5, .c 19, .c 3, .c 23, .c 13, .c 3, .c 29, .c 7, .c 3, .c 127, .c 5, .c 3,
  .p pv11 [pv2,pv38039], .p pv7 [pv2,pv3,pv5,pv317], .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv7,pv1087], .c 47, .c 3, .c 7, .p pv7 [pv2,pv3,pv11,pv1153], .c 3,
  .p pv5 [pv2,pv13,pv2927], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 103, .c 3, .c 163,
  .p pv3 [pv2,pv3,pv4229], .c 3, .c 269, .p pv17 [pv2,pv3,pv13,pv61], .c 3, .c 19, .c 5, .c 3,
  .c 7, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv37], .c 3, .c 271, .c 7, .c 3,
  .p pv2 [pv2,pv79,pv241], .p pv3 [pv2,pv3,pv4231], .c 3, .p pv2 [pv2,pv113,pv337], .c 5, .c 3,
  .c 59, .c 19, .c 3, .c 5, .c 17, .c 3, .c 7, .c 29, .c 3, .c 47, .c 61, .c 3, .c 13, .c 5, .c 3,
  .c 23, .c 181, .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv977], .c 3, .c 17, .p pv5 [pv2,pv3,pv29,pv73],
  .c 3, .c 199, .c 11, .c 3, .c 7, .c 5, .c 3, .c 31, .p pv11 [pv2,pv3,pv5,pv7,pv11], .c 3, .c 5,
  .c 7, .c 3, .c 11, .p pv3 [pv2,pv3,pv97,pv131], .c 3, .c 19, .p pv7 [pv2,pv3,pv353], .c 3,
  .p pv2 [pv2,pv11,pv1733], .c 5, .c 3, .p pv2 [pv2,pv7,pv13,pv419],
  .p pv2 [pv2,pv3,pv5,pv31,pv41], .c 3, .c 5, .c 53, .c 3, .c 13, .c 89, .c 3, .c 83, .c 7, .c 3,
  .p pv2 [pv2,pv43,pv887], .c 5, .c 3, .p pv3 [pv2,pv149],
]
private theorem h0009c09 : checkBlock 76035 128 b0009c09 = true := by
  decide +kernel

private def b0009c10 : List Row := [
  .c 23, .c 3, .c 5, .c 13, .c 3, .c 41, .p pv3 [pv2,pv3,pv157], .c 3, .c 7, .c 137, .c 3, .c 17,
  .c 5, .c 3, .c 167, .c 7, .c 3, .c 5, .c 127, .c 3, .c 37, .p pv5 [pv2,pv3,pv6361], .c 3, .c 23,
  .c 97, .c 3, .p pv5 [pv2,pv7,pv19,pv41], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 29, .c 3,
  .c 19, .c 7, .c 3, .p pv5 [pv2,pv38183], .p pv11 [pv2,pv3,pv37,pv43], .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv38189], .c 17, .c 3, .c 5, .p pv3 [pv2,pv3,pv29,pv439], .c 3, .c 7, .c 79, .c 3,
  .c 241, .c 19, .c 3, .p pv2 [pv2,pv38201], .c 5, .c 3, .c 109, .c 43, .c 3, .c 5, .c 11, .c 3,
  .p pv3 [pv2,pv5,pv3821], .p pv5 [pv2,pv3,pv47,pv271], .c 3, .c 13, .c 23, .c 3, .c 7, .c 5,
  .c 3, .c 11, .p pv11 [pv2,pv3,pv5,pv7,pv13], .c 3, .c 5, .c 7, .c 3, .c 89, .c 13, .c 3, .c 101,
  .c 157, .c 3, .p pv5 [pv2,pv38231], .c 5, .c 3, .c 47, .p pv13 [pv2,pv3,pv5,pv2549], .c 3, .c 5,
  .c 31, .c 3, .p pv3 [pv2,pv5,pv239], .c 11, .c 3, .p pv5 [pv2,pv167,pv229], .c 7, .c 3,
  .p pv2 [pv2,pv13,pv1471], .c 5, .c 3, .c 227, .c 113, .c 3, .c 5, .p pv2 [pv2,pv3,pv41,pv311],
  .c 3, .p pv7 [pv2,pv5,pv7,pv1093], .c 19, .c 3, .c 7, .p pv3 [pv2,pv3,pv13,pv109], .c 3, .c 59,
  .c 5, .c 3, .c 103, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv1063], .c 3, .p pv2 [pv2,pv5,pv43,pv89],
  .p pv3 [pv2,pv3,pv12757], .c 3,
]
private theorem h0009c10 : checkBlock 76291 128 b0009c10 = true := by
  decide +kernel

private def b0009c11 : List Row := [
  .c 41, .c 11, .c 3, .c 37, .c 5, .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv11,pv29], .c 3, .c 5, .c 23,
  .c 3, .c 11, .c 7, .c 3, .c 73, .p pv17 [pv2,pv3,pv12763], .c 3, .c 13, .c 5, .c 3, .c 19,
  .c 191, .c 3, .c 5, .p pv7 [pv2,pv3,pv13,pv491], .c 3, .c 7, .p pv2 [pv2,pv3,pv17,pv751], .c 3,
  .p pv5 [pv2,pv38303], .c 13, .c 3, .c 23, .c 5, .c 3, .c 17, .c 193, .c 3, .c 5, .c 19, .c 3,
  .p pv7 [pv2,pv5,pv79,pv97], .c 197, .c 3, .c 11, .c 173, .c 3, .c 7, .c 5, .c 3,
  .p pv7 [pv2,pv11,pv13,pv67], .p pv3 [pv2,pv3,pv5,pv7,pv73], .c 3, .c 5, .c 7, .c 3, .c 13,
  .c 31, .c 3, .p pv2 [pv2,pv38333], .c 43, .c 3, .p pv3 [pv2,pv599], .c 5, .c 3,
  .p pv7 [pv2,pv7,pv5477], .c 11, .c 3, .c 5, .c 13, .c 3, .c 53, .c 271, .c 3,
  .p pv3 [pv2,pv9587], .c 7, .c 3, .c 11, .c 5, .c 3, .c 79, .c 41, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv2131], .c 3, .c 17, .c 73, .c 3, .c 7, .c 277, .c 3, .p pv2 [pv2,pv19183],
  .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 11, .c 3, .c 23, .p pv5 [pv2,pv3,pv13,pv41], .c 3,
  .p pv2 [pv2,pv31,pv619], .c 59, .c 3, .c 29, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv853], .c 3,
  .c 5, .p pv5 [pv2,pv3,pv7,pv457], .c 3, .p pv2 [pv2,pv5,pv11,pv349], .c 7, .c 3, .c 31, .c 17,
  .c 3, .c 41, .c 5, .c 3, .c 61, .p pv17 [pv2,pv3,pv5],
]
private theorem h0009c11 : checkBlock 76547 128 b0009c11 = true := by
  decide +kernel

private def b0009c12 : List Row := [
  .c 3, .c 5, .c 89, .c 3, .c 7, .c 11, .c 3, .c 13, .p pv7 [pv2,pv3,pv7,pv31,pv59], .c 3, .c 17,
  .c 5, .c 3, .p pv2 [pv2,pv19207], .p pv29 [pv2,pv3,pv5,pv13,pv197], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv19,pv337], .c 3, .c 43, .c 13, .c 3, .p pv5 [pv2,pv7,pv11,pv499], .c 31, .c 3,
  .c 7, .c 5, .c 3, .c 151, .c 101, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv7687],
  .p pv19 [pv2,pv3,pv3203], .c 3, .c 59, .c 11, .c 3, .p pv2 [pv2,pv13,pv2957], .c 5, .c 3, .c 23,
  .c 17, .c 3, .c 5, .c 131, .c 3, .c 11, .c 53, .c 3, .p pv2 [pv2,pv38453], .c 7, .c 3,
  .p pv3 [pv2,pv11,pv19,pv23], .c 5, .c 3, .p pv13 [pv2,pv38459], .c 13, .c 3, .c 5, .c 43, .c 3,
  .c 19, .c 107, .c 3, .c 7, .c 47, .c 3, .p pv11 [pv2,pv17,pv31,pv73], .c 5, .c 3,
  .p pv2 [pv2,pv19237], .c 7, .c 3, .c 5, .c 41, .c 3, .p pv3 [pv2,pv5,pv13,pv37],
  .p pv3 [pv2,pv3,pv101,pv127], .c 3, .c 11, .c 19, .c 3, .c 13, .c 5, .c 3, .c 7, .c 23, .c 3,
  .c 5, .c 167, .c 3, .p pv13 [pv2,pv5,pv7699], .c 7, .c 3, .c 37, .c 13, .c 3,
  .p pv2 [pv2,pv38501], .c 5, .c 3, .c 53, .c 11, .c 3, .c 5, .p pv7 [pv2,pv3,pv3209], .c 3, .c 7,
  .p pv3 [pv2,pv3,pv11,pv389], .c 3, .c 17, .p pv2 [pv2,pv3,pv7,pv131], .c 3, .c 11, .c 5, .c 3,
  .c 41, .p pv7 [pv2,pv3,pv5,pv107], .c 3, .c 5, .p pv3 [pv2,pv3,pv12841], .c 3, .c 13, .c 29,
  .c 3, .c 251,
]
private theorem h0009c12 : checkBlock 76803 128 b0009c12 = true := by
  decide +kernel

private def b0009c13 : List Row := [
  .c 263, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv19267], .c 37, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv41,pv47], .c 19, .c 3, .c 157, .c 127, .c 3, .p pv2 [pv2,pv19273], .c 5, .c 3,
  .c 11, .p pv7 [pv2,pv3,pv5,pv257], .c 3, .c 5, .c 83, .c 3, .c 29, .c 59, .c 3, .c 67, .c 7,
  .c 3, .c 233, .c 5, .c 3, .c 13, .c 137, .c 3, .c 5, .p pv13 [pv2,pv3,pv1607], .c 3,
  .p pv3 [pv2,pv5,pv7,pv19,pv29], .c 11, .c 3, .c 7, .c 179, .c 3, .p pv3 [pv2,pv2411], .c 5,
  .c 3, .c 19, .c 7, .c 3, .c 5, .p pv23 [pv2,pv3,pv1429], .c 3, .p pv2 [pv2,pv5,pv7717], .c 229,
  .c 3, .c 71, .c 113, .c 3, .c 79, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv31,pv83], .c 3, .c 5,
  .c 17, .c 3, .p pv3 [pv2,pv5,pv193], .c 7, .c 3, .c 13, .c 11, .c 3, .p pv2 [pv2,pv97,pv199],
  .c 5, .c 3, .c 37, .c 31, .c 3, .c 5, .c 29, .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv19309],
  .p pv3 [pv2,pv3,pv7,pv613], .c 3, .p pv2 [pv2,pv11,pv3511], .c 5, .c 3, .p pv3 [pv2,pv17,pv71],
  .c 67, .c 3, .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv3863], .p pv5 [pv2,pv3,pv79,pv163], .c 3,
  .p pv2 [pv2,pv7,pv5519], .p pv2 [pv2,pv3,pv47,pv137], .c 3, .c 7, .c 5, .c 3,
  .p pv11 [pv2,pv38639], .c 109, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv59,pv131], .c 37, .c 3,
  .c 11, .c 17, .c 3, .c 23, .c 5, .c 3, .c 97, .c 13, .c 3,
]
private theorem h0009c13 : checkBlock 77059 128 b0009c13 = true := by
  decide +kernel

private def b0009c14 : List Row := [
  .c 5, .p pv2 [pv2,pv3,pv17,pv379], .c 3, .c 167, .p pv2 [pv2,pv3,pv7,pv263], .c 3, .c 53, .c 7,
  .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv38669], .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv4297], .c 3,
  .p pv47 [pv2,pv5,pv7,pv13,pv17], .c 103, .c 3, .c 7, .p pv3 [pv2,pv3,pv12893], .c 3, .c 11,
  .c 5, .c 3, .p pv3 [pv2,pv19,pv509], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv31], .c 3, .c 223,
  .p pv3 [pv2,pv3,pv1433], .c 3, .c 19, .c 13, .c 3, .c 193, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5,
  .c 11, .c 3, .c 199, .c 7, .c 3, .p pv3 [pv2,pv9677], .p pv2 [pv2,pv3,pv11,pv17,pv23], .c 3,
  .c 139, .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv29,pv89], .c 3, .c 5, .c 211, .c 3, .c 7,
  .c 43, .c 3, .p pv5 [pv2,pv38723], .c 41, .c 3, .c 73, .c 5, .c 3, .c 29, .c 71, .c 3, .c 5,
  .c 13, .c 3, .p pv7 [pv2,pv5,pv61,pv127], .c 11, .c 3, .p pv2 [pv2,pv7,pv2767],
  .p pv19 [pv2,pv3,pv37,pv349], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv29,pv167],
  .p pv3 [pv2,pv3,pv5,pv7,pv41], .c 3, .c 5, .c 7, .c 3, .c 19, .c 17, .c 3, .c 179,
  .p pv2 [pv2,pv3,pv2153], .c 3, .p pv3 [pv2,pv9689], .c 5, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv5,pv17,pv19], .c 3, .c 5, .p pv5 [pv2,pv3,pv59,pv73], .c 3, .c 31, .c 23,
  .c 3, .c 17, .c 7, .c 3, .p pv5 [pv2,pv137,pv283], .c 5, .c 3, .p pv2 [pv2,pv19387],
  .p pv13 [pv2,pv3,pv5,pv11,pv47], .c 3, .c 5, .p pv5 [pv2,pv3,pv23,pv281], .c 3, .c 11,
  .p pv2 [pv2,pv3,pv31,pv139], .c 3, .c 7, .p pv13 [pv2,pv3,pv101],
]
private theorem h0009c14 : checkBlock 77315 128 b0009c14 = true := by
  decide +kernel

private def b0009c15 : List Row := [
  .c 3, .p pv2 [pv2,pv11,pv41,pv43], .c 5, .c 3, .c 23, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv67,pv193], .c 3, .p pv13 [pv2,pv5,pv7759], .c 31, .c 3, .c 13, .c 73, .c 3,
  .c 71, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv13,pv199], .c 3, .c 5,
  .p pv17 [pv2,pv3,pv7,pv11], .c 3, .p pv2 [pv2,pv5,pv3881], .c 7, .c 3, .c 11, .c 149, .c 3,
  .c 29, .c 5, .c 3, .c 17, .p pv13 [pv2,pv3,pv5,pv647], .c 3, .c 5, .p pv3 [pv2,pv3,pv12941],
  .c 3, .c 7, .c 19, .c 3, .c 79, .p pv2 [pv2,pv3,pv7,pv43], .c 3, .c 37, .c 5, .c 3, .c 101,
  .c 11, .c 3, .c 5, .c 173, .c 3, .p pv3 [pv2,pv5,pv971], .c 131, .c 3,
  .p pv5 [pv2,pv7,pv31,pv179], .p pv29 [pv2,pv3,pv13,pv83], .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv53,pv733], .c 13, .c 3, .c 5, .c 7, .c 3, .p pv19 [pv2,pv5,pv19,pv409],
  .p pv7 [pv2,pv3,pv1619], .c 3, .c 23, .p pv11 [pv2,pv3,pv12953], .c 3, .p pv2 [pv2,pv38861],
  .c 5, .c 3, .c 19, .p pv2 [pv2,pv3,pv5,pv2591], .c 3, .c 5, .c 11, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv7,pv617], .c 3, .p pv2 [pv2,pv38873], .c 7, .c 3, .c 13, .c 5, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv5], .c 3, .c 5, .c 19, .c 3, .c 83, .p pv2 [pv2,pv3,pv6481], .c 3, .c 7,
  .c 13, .c 3, .p pv5 [pv2,pv38891], .c 5, .c 3, .c 107, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv2161], .c 3, .p pv7 [pv2,pv5,pv389], .c 11, .c 3, .c 29, .c 17, .c 3,
  .p pv2 [pv2,pv7,pv397], .c 5, .c 3, .c 7, .c 59, .c 3, .c 5,
]
private theorem h0009c15 : checkBlock 77571 128 b0009c15 = true := by
  decide +kernel

private def b0009c16 : List Row := [
  .c 223, .c 3, .c 13, .c 7, .c 3, .c 277, .p pv3 [pv2,pv3,pv12973], .c 3, .c 17, .c 5, .c 3,
  .p pv3 [pv2,pv37,pv263], .c 127, .c 3, .c 5, .c 13, .c 3, .c 7, .p pv5 [pv2,pv3,pv19,pv683],
  .c 3, .p pv2 [pv2,pv38933], .c 11, .c 3, .c 43, .c 5, .c 3, .c 47, .c 19, .c 3, .c 5, .c 71,
  .c 3, .c 11, .p pv2 [pv2,pv3,pv6491], .c 3, .c 61, .p pv17 [pv2,pv3,pv12983], .c 3, .c 7, .c 5,
  .c 3, .c 13, .c 17, .c 3, .c 5, .c 7, .c 3, .c 67, .c 29, .c 3, .c 149,
  .p pv19 [pv2,pv3,pv17,pv191], .c 3, .p pv2 [pv2,pv19483], .c 5, .c 3, .c 59, .c 41, .c 3, .c 5,
  .c 23, .c 3, .p pv11 [pv2,pv5,pv1559], .c 137, .c 3, .c 11, .c 7, .c 3, .c 53, .c 5, .c 3,
  .p pv3 [pv2,pv11,pv443], .c 103, .c 3, .c 5, .p pv5 [pv2,pv3,pv19], .c 3, .c 29,
  .p pv3 [pv2,pv3,pv41,pv317], .c 3, .c 7, .c 167, .c 3, .c 23, .c 5, .c 3,
  .p pv11 [pv2,pv59,pv661], .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv13001], .c 3, .c 181, .c 13, .c 3,
  .p pv3 [pv2,pv23,pv53], .c 61, .c 3, .c 11, .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv17], .c 3,
  .c 5, .c 73, .c 3, .p pv3 [pv2,pv5,pv1951], .c 7, .c 3, .c 17, .p pv7 [pv2,pv3,pv271], .c 3,
  .c 89, .c 5, .c 3, .p pv2 [pv2,pv31,pv1259], .c 251, .c 3, .c 5, .c 11, .c 3, .c 7, .c 101,
  .c 3, .c 163, .p pv41 [pv2,pv3,pv7,pv11,pv13], .c 3,
]
private theorem h0009c16 : checkBlock 77827 128 b0009c16 = true := by
  decide +kernel

private def b0009c17 : List Row := [
  .c 113, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 29, .c 3, .p pv2 [pv2,pv5,pv11,pv71], .c 83,
  .c 3, .c 37, .c 19, .c 3, .c 7, .c 5, .c 3, .c 191, .p pv11 [pv2,pv3,pv5,pv7,pv31], .c 3, .c 5,
  .c 7, .c 3, .c 23, .c 11, .c 3, .p pv3 [pv2,pv9767], .p pv3 [pv2,pv3,pv1447], .c 3, .c 13, .c 5,
  .c 3, .c 17, .c 31, .c 3, .c 5, .p pv11 [pv2,pv3,pv13,pv167], .c 3, .c 47,
  .p pv3 [pv2,pv3,pv7,pv1861], .c 3, .p pv5 [pv2,pv11,pv17,pv19], .c 7, .c 3,
  .p pv2 [pv2,pv19543], .c 5, .c 3, .p pv2 [pv2,pv39089], .c 37, .c 3, .c 5, .c 41, .c 3,
  .p pv11 [pv2,pv5,pv7,pv1117], .p pv5 [pv2,pv3,pv181], .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv61,pv641], .c 5, .c 3, .c 197, .c 7, .c 3, .c 5, .c 17, .c 3, .c 11, .c 19, .c 3,
  .c 137, .p pv2 [pv2,pv3,pv41,pv53], .c 3, .p pv3 [pv2,pv7,pv11,pv127], .c 5, .c 3, .c 7,
  .p pv19 [pv2,pv3,pv5,pv163], .c 3, .c 5, .c 13, .c 3, .c 17, .c 7, .c 3, .c 139,
  .p pv2 [pv2,pv3,pv13043], .c 3, .c 61, .c 5, .c 3, .c 23, .c 29, .c 3, .c 5,
  .p pv59 [pv2,pv3,pv11,pv593], .c 3, .c 7, .p pv3 [pv2,pv3,pv4349], .c 3, .c 11, .c 79, .c 3,
  .c 59, .c 5, .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv29], .c 3, .c 5, .p pv2 [pv2,pv3,pv31,pv421],
  .c 3, .p pv29 [pv2,pv5,pv41,pv191], .c 71, .c 3, .p pv2 [pv2,pv7,pv2797], .c 17, .c 3, .c 7,
  .c 5, .c 3, .c 29, .c 11, .c 3, .c 5, .c 7,
]
private theorem h0009c17 : checkBlock 78083 128 b0009c17 = true := by
  decide +kernel

private def b0009c18 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv3917], .c 157, .c 3, .p pv2 [pv2,pv43,pv911], .c 47, .c 3, .c 11, .c 5,
  .c 3, .c 127, .c 23, .c 3, .c 5, .p pv5 [pv2,pv3,pv37,pv353], .c 3, .c 109, .c 181, .c 3, .c 13,
  .c 7, .c 3, .c 103, .c 5, .c 3, .c 43, .c 277, .c 3, .c 5, .c 11, .c 3, .p pv13 [pv2,pv5,pv7],
  .c 13, .c 3, .c 7, .c 89, .c 3, .c 19, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv4357], .c 3, .c 107, .c 41, .c 3, .p pv2 [pv2,pv19609],
  .p pv7 [pv2,pv3,pv17,pv769], .c 3, .c 47, .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 67, .c 3,
  .c 31, .c 7, .c 3, .p pv2 [pv2,pv39233], .c 131, .c 3, .c 97, .c 5, .c 3, .p pv7 [pv2,pv39239],
  .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv103,pv127], .c 3, .c 7, .c 53, .c 3,
  .p pv3 [pv2,pv11,pv223], .c 23, .c 3, .c 29, .c 5, .c 3, .p pv3 [pv2,pv19,pv1033],
  .p pv3 [pv2,pv3,pv5,pv2617], .c 3, .c 5, .p pv2 [pv2,pv3,pv727], .c 3, .c 233, .c 17, .c 3,
  .c 19, .c 11, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv107,pv367],
  .p pv2 [pv2,pv3,pv5,pv7,pv11,pv17], .c 3, .c 5, .c 7, .c 3, .c 11, .p pv5 [pv2,pv3,pv1091],
  .c 3, .c 17, .c 13, .c 3, .c 251, .c 5, .c 3, .p pv3 [pv2,pv7,pv23,pv61],
  .p pv2 [pv2,pv3,pv5,pv97], .c 3, .c 5, .p pv5 [pv2,pv3,pv1637], .c 3, .c 179,
  .p pv3 [pv2,pv3,pv7,pv1871], .c 3, .c 89, .c 7, .c 3, .p pv3 [pv2,pv307],
]
private theorem h0009c18 : checkBlock 78339 128 b0009c18 = true := by
  decide +kernel

private def b0009c19 : List Row := [
  .c 5, .c 3, .c 53, .c 83, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv397], .c 3, .c 13, .c 127, .c 3,
  .c 7, .c 29, .c 3, .p pv5 [pv2,pv19,pv2069], .c 5, .c 3, .c 61, .c 7, .c 3, .c 5, .c 13, .c 3,
  .c 19, .p pv11 [pv2,pv3,pv17,pv257], .c 3, .c 31, .p pv11 [pv2,pv3,pv29,pv113], .c 3,
  .p pv3 [pv2,pv7,pv53], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 97, .c 3, .c 151, .c 7, .c 3,
  .c 29, .c 19, .c 3, .c 11, .c 5, .c 3, .c 13, .p pv7 [pv2,pv3,pv5,pv43,pv61], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv1093], .c 3, .c 7, .c 211, .c 3, .p pv2 [pv2,pv23,pv29,pv59], .c 31, .c 3,
  .p pv3 [pv2,pv9839], .c 5, .c 3, .c 223, .p pv7 [pv2,pv3,pv5,pv41], .c 3, .c 5, .c 11, .c 3,
  .c 131, .c 43, .c 3, .p pv3 [pv2,pv7,pv19,pv37], .c 71, .c 3, .c 7, .c 5, .c 3, .c 11, .c 61,
  .c 3, .c 5, .c 7, .c 3, .c 17, .c 79, .c 3, .c 13, .c 227, .c 3, .c 37, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv17,pv331], .p pv29 [pv2,pv3,pv5,pv13,pv101], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv1459], .c 3, .p pv11 [pv2,pv5,pv7879], .c 11, .c 3, .p pv2 [pv2,pv19699],
  .c 7, .c 3, .p pv2 [pv2,pv31,pv41], .c 5, .c 3, .p pv3 [pv2,pv9851], .c 53, .c 3, .c 5, .c 269,
  .c 3, .c 23, .p pv3 [pv2,pv3,pv29,pv151], .c 3, .c 7, .c 17, .c 3, .c 31, .c 5, .c 3,
  .p pv13 [pv2,pv39419], .c 7, .c 3, .c 5, .c 37, .c 3,
]
private theorem h0009c19 : checkBlock 78595 128 b0009c19 = true := by
  decide +kernel

private def b0009c20 : List Row := [
  .c 29, .p pv5 [pv2,pv3,pv6571], .c 3, .p pv3 [pv2,pv9857], .c 11, .c 3, .c 17, .c 5, .c 3, .c 7,
  .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv313], .c 3, .c 11, .c 7, .c 3, .p pv5 [pv2,pv39443],
  .p pv11 [pv2,pv3,pv19,pv173], .c 3, .p pv2 [pv2,pv11,pv163], .c 5, .c 3, .c 257,
  .p pv23 [pv2,pv3,pv5,pv263], .c 3, .c 5, .c 19, .c 3, .c 7, .c 23, .c 3, .c 53,
  .p pv3 [pv2,pv3,pv7,pv1879], .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv4933], .c 17, .c 3, .c 5,
  .c 193, .c 3, .p pv2 [pv2,pv5,pv3947], .c 89, .c 3, .c 11, .c 13, .c 3, .c 7, .c 5, .c 3, .c 23,
  .c 281, .c 3, .c 5, .c 7, .c 3, .c 157, .c 151, .c 3, .p pv3 [pv2,pv617],
  .p pv3 [pv2,pv3,pv13163], .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv7,pv13,pv31], .c 11, .c 3,
  .c 5, .c 197, .c 3, .c 13, .c 199, .c 3, .c 41, .c 7, .c 3, .c 11, .c 5, .c 3, .c 31, .c 19,
  .c 3, .c 5, .c 13, .c 3, .p pv7 [pv2,pv5,pv7,pv1129], .c 17, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv4391], .c 3, .p pv2 [pv2,pv39521], .c 5, .c 3, .c 137, .c 7, .c 3, .c 5,
  .c 11, .c 3, .c 173, .p pv5 [pv2,pv3,pv13177], .c 3, .c 17, .c 37, .c 3, .c 107, .c 5, .c 3,
  .c 7, .c 31, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv269], .c 3, .c 139, .c 7, .c 3, .c 19, .c 83,
  .c 3, .p pv5 [pv2,pv39551], .c 5,
]
private theorem h0009c20 : checkBlock 78851 128 b0009c20 = true := by
  decide +kernel

private def b0009c21 : List Row := [
  .c 3, .c 239, .p pv13 [pv2,pv3,pv5,pv293], .c 3, .c 5, .c 61, .c 3, .c 7, .c 11, .c 3, .c 67,
  .c 53, .c 3, .p pv2 [pv2,pv73,pv271], .c 5, .c 3, .p pv2 [pv2,pv39569], .c 29, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv4397], .c 3, .p pv13 [pv2,pv5,pv1583], .p pv11 [pv2,pv3,pv17,pv97], .c 3,
  .c 13, .p pv3 [pv2,pv3,pv79,pv167], .c 3, .c 7, .c 5, .c 3, .c 17, .c 41, .c 3, .c 5, .c 7,
  .c 3, .p pv2 [pv2,pv5,pv37,pv107], .c 13, .c 3, .p pv5 [pv2,pv17,pv137], .c 11, .c 3,
  .p pv3 [pv2,pv19,pv521], .c 5, .c 3, .c 29, .p pv13 [pv2,pv3,pv5,pv11], .c 3, .c 5, .c 103,
  .c 3, .c 11, .c 113, .c 3, .c 37, .c 7, .c 3, .c 227, .c 5, .c 3, .p pv2 [pv2,pv29,pv683],
  .p pv3 [pv2,pv3,pv5,pv19,pv139], .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv7,pv283], .c 109,
  .c 3, .c 7, .c 19, .c 3, .c 41, .c 5, .c 3, .p pv2 [pv2,pv23,pv1723], .c 7, .c 3, .c 5, .c 31,
  .c 3, .c 17, .p pv5 [pv2,pv3,pv367], .c 3, .c 11, .p pv3 [pv2,pv3,pv73,pv181], .c 3,
  .p pv2 [pv2,pv7,pv809], .c 5, .c 3, .c 7, .c 37, .c 3, .c 5, .c 179, .c 3,
  .p pv2 [pv2,pv5,pv13,pv61], .c 7, .c 3, .c 71, .p pv2 [pv2,pv3,pv2203], .c 3, .c 13, .c 5, .c 3,
  .p pv7 [pv2,pv39659], .c 11, .c 3, .c 5, .c 23, .c 3, .c 7, .p pv5 [pv2,pv3,pv11,pv601], .c 3,
  .p pv3 [pv2,pv47,pv211], .c 13, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv83,pv239], .c 73, .c 3,
  .c 5, .p pv7 [pv2,pv3,pv17,pv389], .c 3, .c 61,
]
private theorem h0009c21 : checkBlock 79107 128 b0009c21 = true := by
  decide +kernel

private def b0009c22 : List Row := [
  .c 19, .c 3, .p pv5 [pv2,pv7,pv5669], .c 139, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv43,pv71], .c 163, .c 3, .c 5, .c 7, .c 3, .c 13, .p pv5 [pv2,pv3,pv827],
  .c 3, .p pv2 [pv2,pv23,pv863], .p pv3 [pv2,pv3,pv11,pv401], .c 3, .c 271, .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv2647], .c 3, .c 5, .c 13, .c 3, .c 43, .p pv3 [pv2,pv3,pv7,pv31,pv61],
  .c 3, .p pv2 [pv2,pv151,pv263], .c 7, .c 3, .p pv3 [pv2,pv9929], .c 5, .c 3, .c 19, .c 17, .c 3,
  .c 5, .c 53, .c 3, .p pv11 [pv2,pv5,pv7,pv227], .c 11, .c 3, .c 7, .c 181, .c 3, .c 229, .c 5,
  .c 3, .c 13, .c 7, .c 3, .c 5, .c 19, .c 3, .p pv7 [pv2,pv5,pv1987], .c 61, .c 3, .c 101, .c 29,
  .c 3, .p pv5 [pv2,pv7,pv17,pv167], .c 5, .c 3, .c 7, .c 107, .c 3, .c 5, .c 43, .c 3, .c 23,
  .c 7, .c 3, .c 131, .c 11, .c 3, .c 281, .c 5, .c 3, .c 67, .p pv2 [pv2,pv3,pv5,pv11,pv241],
  .c 3, .c 5, .p pv7 [pv2,pv3,pv1657], .c 3, .c 7, .c 17, .c 3, .c 13, .p pv2 [pv2,pv3,pv7,pv947],
  .c 3, .c 19, .c 5, .c 3, .p pv7 [pv2,pv39779], .p pv7 [pv2,pv3,pv5,pv13,pv17], .c 3, .c 5,
  .c 251, .c 3, .c 47, .c 13, .c 3, .c 17, .p pv13 [pv2,pv3,pv4421], .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv101,pv197], .c 19, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv199], .c 23, .c 3,
  .c 11, .p pv19 [pv2,pv3,pv31,pv107], .c 3, .p pv2 [pv2,pv13,pv1531], .c 5, .c 3,
]
private theorem h0009c22 : checkBlock 79363 128 b0009c22 = true := by
  decide +kernel

private def b0009c23 : List Row := [
  .c 103, .p pv2 [pv2,pv3,pv5,pv1327], .c 3, .c 5, .p pv3 [pv2,pv3,pv23,pv577], .c 3,
  .p pv13 [pv2,pv5,pv7963], .p pv13 [pv2,pv3,pv7,pv79], .c 3, .c 97, .c 7, .c 3, .c 73, .c 5,
  .c 3, .c 23, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv3319], .c 3, .c 37, .c 29, .c 3, .c 7,
  .p pv17 [pv2,pv3,pv2213], .c 3, .c 11, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv19,pv233], .c 3, .p pv17 [pv2,pv5,pv13,pv613], .p pv5 [pv2,pv3,pv29,pv229],
  .c 3, .p pv3 [pv2,pv17,pv293], .p pv2 [pv2,pv3,pv37,pv359], .c 3, .c 13, .c 5, .c 3, .c 7,
  .c 79, .c 3, .c 5, .c 11, .c 3, .c 29, .c 7, .c 3, .c 61, .c 13, .c 3, .c 71, .c 5, .c 3, .c 11,
  .c 23, .c 3, .c 5, .c 17, .c 3, .c 7, .c 173, .c 3, .p pv2 [pv2,pv127,pv157], .c 47, .c 3,
  .c 31, .c 5, .c 3, .p pv3 [pv2,pv13,pv59], .c 241, .c 3, .c 5, .p pv5 [pv2,pv3,pv277], .c 3,
  .c 13, .c 11, .c 3, .c 23, .c 73, .c 3, .c 7, .c 5, .c 3, .c 199,
  .p pv23 [pv2,pv3,pv5,pv7,pv19], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv23,pv347],
  .p pv2 [pv2,pv3,pv739], .c 3, .p pv3 [pv2,pv11,pv907], .c 19, .c 3, .p pv5 [pv2,pv107,pv373],
  .c 5, .c 3, .p pv2 [pv2,pv7,pv2851], .c 97, .c 3, .c 5, .c 29, .c 3, .p pv3 [pv2,pv5,pv499],
  .p pv2 [pv2,pv3,pv7,pv1901], .c 3, .p pv5 [pv2,pv13,pv37,pv83], .c 7, .c 3, .c 47, .c 5, .c 3,
  .c 13, .p pv2 [pv2,pv3,pv5,pv11], .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv29], .c 3, .c 11,
  .p pv7 [pv2,pv3,pv13],
]
private theorem h0009c23 : checkBlock 79619 128 b0009c23 = true := by
  decide +kernel

private def b0009c24 : List Row := [
  .c 3, .c 7, .c 23, .c 3, .c 17, .c 5, .c 3, .p pv3 [pv2,pv4993], .c 7, .c 3, .c 5, .c 109, .c 3,
  .p pv2 [pv2,pv5,pv17,pv47], .p pv3 [pv2,pv3,pv23,pv193], .c 3, .p pv2 [pv2,pv39953], .c 41,
  .c 3, .c 157, .c 5, .c 3, .c 7, .c 229, .c 3, .c 5, .c 257, .c 3, .c 67, .c 7, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv4441], .c 3, .p pv5 [pv2,pv39971], .c 5, .c 3, .c 31, .c 17, .c 3, .c 5,
  .c 37, .c 3, .c 7, .c 13, .c 3, .p pv5 [pv2,pv39983], .c 211, .c 3, .p pv2 [pv2,pv19993], .c 5,
  .c 3, .p pv2 [pv2,pv39989], .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv13331], .c 3, .c 41, .c 167,
  .c 3, .p pv2 [pv2,pv7,pv2857], .p pv3 [pv2,pv3,pv67,pv199], .c 3, .c 7, .c 5, .c 3, .c 19,
  .c 29, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv4001], .c 43, .c 3, .c 79, .c 191, .c 3,
  .c 163, .c 5, .c 3, .p pv11 [pv2,pv7,pv5717], .c 13, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv1601], .c 17, .c 3, .c 223, .c 7, .c 3, .c 23, .c 5, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv5,pv17,pv157], .c 3, .c 5, .p pv2 [pv2,pv3,pv6673], .c 3, .c 73, .c 53, .c 3,
  .c 7, .c 283, .c 3, .c 13, .c 5, .c 3, .c 173, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv79],
  .c 3, .p pv11 [pv2,pv5,pv8011], .c 11, .c 3, .c 113, .c 13, .c 3, .c 19, .c 5, .c 3, .c 7,
]
private theorem h0009c24 : checkBlock 79875 128 b0009c24 = true := by
  decide +kernel

private def b0009c25 : List Row := [
  .c 227, .c 3, .c 5, .c 127, .c 3, .p pv2 [pv2,pv5,pv4007], .c 7, .c 3, .p pv2 [pv2,pv11,pv3643],
  .p pv17 [pv2,pv3,pv6679], .c 3, .p pv3 [pv2,pv43,pv233], .c 5, .c 3, .c 71, .c 19, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv31,pv431], .c 3, .c 7, .p pv13 [pv2,pv3,pv17,pv131], .c 3,
  .p pv3 [pv2,pv5011], .c 11, .c 3, .c 181, .c 5, .c 3, .c 17, .p pv11 [pv2,pv3,pv5,pv11], .c 3,
  .c 5, .c 13, .c 3, .c 11, .c 139, .c 3, .p pv5 [pv2,pv7,pv17,pv337], .p pv17 [pv2,pv3,pv557],
  .c 3, .c 7, .c 5, .c 3, .c 97, .p pv2 [pv2,pv3,pv5,pv7,pv191], .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv71,pv113], .p pv7 [pv2,pv3,pv3343], .c 3, .c 19, .p pv3 [pv2,pv3,pv43,pv311],
  .c 3, .c 29, .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv107], .c 3, .c 5, .c 17, .c 3, .c 83,
  .p pv3 [pv2,pv3,pv7,pv13], .c 3, .c 11, .c 7, .c 3, .p pv3 [pv2,pv29,pv173], .c 5, .c 3,
  .p pv11 [pv2,pv11,pv41,pv89], .c 43, .c 3, .c 5, .p pv3 [pv2,pv3,pv13381], .c 3, .c 17, .c 23,
  .c 3, .c 7, .c 59, .c 3, .c 131, .c 5, .c 3, .p pv2 [pv2,pv17,pv1181], .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv23,pv97], .c 3, .c 31, .c 47, .c 3, .c 13, .p pv11 [pv2,pv3,pv3347], .c 3,
  .c 11, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv13,pv103], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv1913], .c 3, .c 19, .c 7, .c 3, .c 107, .c 17, .c 3,
  .p pv2 [pv2,pv23,pv1747], .c 5, .c 3, .p pv3 [pv2,pv5023], .c 179, .c 3, .c 5, .c 11, .c 3,
  .c 7, .c 31, .c 3,
]
private theorem h0009c25 : checkBlock 80131 128 b0009c25 = true := by
  decide +kernel

private def b0009c26 : List Row := [
  .p pv2 [pv2,pv40193], .c 19, .c 3, .c 17, .c 5, .c 3, .c 11, .c 37, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv1489], .c 3, .c 191, .c 97, .c 3, .c 29, .c 137, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv20107], .c 13, .c 3, .c 5, .c 7, .c 3, .c 257, .c 11, .c 3,
  .p pv5 [pv2,pv19,pv29,pv73], .p pv7 [pv2,pv3,pv419], .c 3, .c 43, .c 5, .c 3, .c 61, .c 17,
  .c 3, .c 5, .c 67, .c 3, .p pv17 [pv2,pv5,pv13,pv619], .p pv5 [pv2,pv3,pv7,pv479], .c 3, .c 23,
  .c 7, .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv10061], .p pv2 [pv2,pv3,pv5,pv2683], .c 3, .c 5,
  .c 101, .c 3, .c 79, .c 19, .c 3, .c 7, .c 11, .c 3, .p pv3 [pv2,pv17,pv37], .c 5, .c 3, .c 73,
  .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv13421], .c 3, .c 11, .c 29, .c 3, .p pv3 [pv2,pv10067],
  .c 43, .c 3, .c 239, .c 5, .c 3, .c 7, .c 109, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv137], .c 3,
  .c 13, .c 7, .c 3, .p pv5 [pv2,pv40283], .c 23, .c 3, .c 197, .c 5, .c 3, .c 19, .c 61, .c 3,
  .c 5, .c 13, .c 3, .c 7, .c 83, .c 3, .c 11, .p pv3 [pv2,pv3,pv7,pv19,pv101], .c 3,
  .p pv2 [pv2,pv191,pv211], .c 5, .c 3, .c 149, .p pv2 [pv2,pv3,pv5,pv2687], .c 3, .c 5, .c 19,
  .c 3, .p pv2 [pv2,pv5,pv29,pv139], .c 37, .c 3, .p pv2 [pv2,pv7,pv13,pv443],
  .p pv2 [pv2,pv3,pv6719], .c 3, .c 7, .c 5, .c 3, .c 13, .c 11,
]
private theorem h0009c26 : checkBlock 80387 128 b0009c26 = true := by
  decide +kernel

private def b0009c27 : List Row := [
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv1613], .c 59, .c 3, .p pv3 [pv2,pv71], .c 79, .c 3,
  .c 11, .c 5, .c 3, .p pv2 [pv2,pv7,pv43,pv67], .p pv3 [pv2,pv3,pv5,pv2689], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv83], .c 3, .p pv3 [pv2,pv5,pv2017], .p pv3 [pv2,pv3,pv7,pv17,pv113], .c 3,
  .p pv5 [pv2,pv40343], .c 7, .c 3, .c 19, .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv269], .c 3,
  .c 5, .c 11, .c 3, .c 43, .p pv5 [pv2,pv3,pv19,pv59], .c 3, .c 7, .c 53, .c 3, .c 89, .c 5,
  .c 3, .c 11, .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv29], .c 3, .c 263, .c 13, .c 3,
  .p pv2 [pv2,pv47,pv859], .p pv2 [pv2,pv3,pv2243], .c 3, .c 23, .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv673], .c 3, .c 5, .c 17, .c 3, .c 37, .c 7, .c 3,
  .p pv3 [pv2,pv23,pv439], .p pv2 [pv2,pv3,pv13463], .c 3, .p pv5 [pv2,pv13,pv239], .c 5, .c 3,
  .p pv2 [pv2,pv19,pv1063], .c 173, .c 3, .c 5, .c 43, .c 3, .c 7, .p pv2 [pv2,pv3,pv67], .c 3,
  .c 19, .p pv19 [pv2,pv3,pv7,pv13,pv37], .c 3, .c 211, .c 5, .c 3, .p pv2 [pv2,pv17,pv2377],
  .c 13, .c 3, .c 5, .c 131, .c 3, .p pv7 [pv2,pv5,pv59,pv137], .p pv5 [pv2,pv3,pv421], .c 3,
  .c 229, .c 11, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv31,pv163], .c 233, .c 3, .c 5, .c 7, .c 3,
  .c 11, .p pv3 [pv2,pv3,pv13477], .c 3, .c 193, .c 17, .c 3, .c 13, .c 5, .c 3, .c 31, .c 29,
  .c 3, .c 5, .c 47, .c 3, .c 23, .c 41, .c 3, .p pv3 [pv2,pv79],
]
private theorem h0009c27 : checkBlock 80643 128 b0009c27 = true := by
  decide +kernel

private def b0009c28 : List Row := [
  .c 7, .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv113,pv179], .p pv3 [pv2,pv3,pv5,pv29,pv31], .c 3,
  .c 5, .p pv13 [pv2,pv3,pv11,pv613], .c 3, .c 19, .p pv2 [pv2,pv3,pv13487], .c 3, .c 7,
  .p pv19 [pv2,pv3,pv281], .c 3, .p pv2 [pv2,pv20233], .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .c 61,
  .c 3, .c 13, .p pv7 [pv2,pv3,pv3373], .c 3, .c 73, .c 19, .c 3, .p pv5 [pv2,pv7,pv5783], .c 5,
  .c 3, .c 7, .c 11, .c 3, .c 5, .c 13, .c 3, .c 47, .c 7, .c 3, .c 109,
  .p pv2 [pv2,pv3,pv17,pv397], .c 3, .c 11, .c 5, .c 3, .c 107, .p pv11 [pv2,pv3,pv5], .c 3, .c 5,
  .c 59, .c 3, .c 7, .p pv23 [pv2,pv3,pv43,pv157], .c 3, .p pv3 [pv2,pv13,pv19,pv41],
  .p pv2 [pv2,pv3,pv7,pv643], .c 3, .p pv5 [pv2,pv17,pv2383], .c 5, .c 3, .c 13,
  .p pv11 [pv2,pv3,pv5,pv37,pv73], .c 3, .c 5, .c 11, .c 3, .p pv43 [pv2,pv5,pv1013],
  .p pv5 [pv2,pv3,pv13,pv1039], .c 3, .p pv5 [pv2,pv7,pv827], .p pv7 [pv2,pv3,pv11,pv307], .c 3,
  .c 7, .c 5, .c 3, .c 11, .c 103, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv11,pv67], .c 17,
  .c 3, .p pv2 [pv2,pv20269], .c 89, .c 3, .p pv2 [pv2,pv71,pv571], .c 5, .c 3, .c 131, .c 83,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv31,pv109], .c 3, .p pv2 [pv2,pv5,pv811], .c 11, .c 3, .c 13, .c 7,
  .c 3, .c 29, .c 5, .c 3, .p pv11 [pv2,pv40559], .c 23, .c 3, .c 5, .c 31, .c 3,
  .p pv2 [pv2,pv5,pv7,pv19,pv61], .c 13, .c 3, .c 7, .c 41, .c 3, .c 53, .c 5, .c 3, .c 19, .c 7,
  .c 3,
]
private theorem h0009c28 : checkBlock 80899 128 b0009c28 = true := by
  decide +kernel

private def b0009c29 : List Row := [
  .c 5, .p pv7 [pv2,pv3,pv6763], .c 3, .c 277, .p pv2 [pv2,pv3,pv167], .c 3, .c 23, .c 11, .c 3,
  .p pv2 [pv2,pv7,pv13,pv223], .c 5, .c 3, .c 7, .p pv23 [pv2,pv3,pv5,pv11,pv41], .c 3, .c 5,
  .c 19, .c 3, .c 11, .c 7, .c 3, .p pv2 [pv2,pv53,pv383], .p pv17 [pv2,pv3,pv13,pv347], .c 3,
  .p pv2 [pv2,pv11,pv3691], .c 5, .c 3, .c 17, .c 13, .c 3, .c 5, .c 241, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv13537], .c 3, .c 43, .c 29, .c 3, .p pv3 [pv2,pv5077], .c 5, .c 3,
  .p pv7 [pv2,pv151,pv269], .c 137, .c 3, .c 5, .c 113, .c 3, .c 31, .c 193, .c 3, .c 11, .c 23,
  .c 3, .c 7, .c 5, .c 3, .c 181, .c 67, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv127],
  .p pv2 [pv2,pv3,pv19,pv23,pv31], .c 3, .c 29, .c 13, .c 3, .p pv2 [pv2,pv20323], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv5807], .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv4517], .c 3, .c 17, .c 31, .c 3,
  .c 233, .c 7, .c 3, .c 11, .c 5, .c 3, .c 167, .p pv17 [pv2,pv3,pv5,pv2711], .c 3, .c 5, .c 163,
  .c 3, .c 13, .p pv13 [pv2,pv3,pv4519], .c 3, .c 7, .p pv2 [pv2,pv3,pv6779], .c 3,
  .p pv3 [pv2,pv10169], .c 5, .c 3, .p pv11 [pv2,pv19,pv2141], .c 7, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv79,pv103], .p pv2 [pv2,pv3,pv6781], .c 3, .c 19, .c 17, .c 3, .c 97, .c 5,
  .c 3, .c 7, .c 199, .c 3, .c 5, .c 23, .c 3, .p pv3 [pv2,pv5,pv11,pv37], .c 7, .c 3, .c 127,
  .p pv7 [pv2,pv3,pv53],
]
private theorem h0009c29 : checkBlock 81155 128 b0009c29 = true := by
  decide +kernel

private def b0009c30 : List Row := [
  .c 3, .c 17, .c 5, .c 3, .c 13, .p pv11 [pv2,pv3,pv5,pv23,pv59], .c 3, .c 5, .c 107, .c 3, .c 7,
  .c 11, .c 3, .c 31, .p pv3 [pv2,pv3,pv7,pv277], .c 3, .c 23, .c 5, .c 3, .c 79, .c 47, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv1697], .c 3, .c 29, .p pv5 [pv2,pv3,pv13577], .c 3, .c 41, .c 257, .c 3,
  .c 7, .c 5, .c 3, .c 59, .c 17, .c 3, .c 5, .c 7, .c 3, .c 19, .c 227, .c 3, .c 13, .c 11, .c 3,
  .c 149, .c 5, .c 3, .p pv2 [pv2,pv7,pv41,pv71], .c 37, .c 3, .c 5, .p pv2 [pv2,pv3,pv6793],
  .c 3, .c 11, .c 13, .c 3, .p pv5 [pv2,pv40763], .c 7, .c 3, .p pv3 [pv2,pv11,pv17,pv109], .c 5,
  .c 3, .c 67, .c 73, .c 3, .c 5, .p pv3 [pv2,pv3,pv13591], .c 3, .p pv7 [pv2,pv5,pv7,pv233],
  .p pv5 [pv2,pv3,pv1699], .c 3, .c 7, .p pv11 [pv2,pv3,pv23,pv197], .c 3,
  .p pv2 [pv2,pv13,pv3137], .c 5, .c 3, .p pv3 [pv2,pv2549], .c 7, .c 3, .c 5, .c 29, .c 3, .c 23,
  .c 17, .c 3, .c 11, .c 83, .c 3, .c 139, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 79, .c 3,
  .p pv2 [pv2,pv5,pv8161], .c 7, .c 3, .c 17, .p pv3 [pv2,pv3,pv61,pv223], .c 3, .c 31, .c 5,
  .c 3, .p pv2 [pv2,pv20407], .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv6803], .c 3, .c 7, .c 19, .c 3,
  .p pv5 [pv2,pv40823], .p pv11 [pv2,pv3,pv7], .c 3, .c 11, .c 5, .c 3, .c 37, .c 127, .c 3, .c 5,
]
private theorem h0009c30 : checkBlock 81411 128 b0009c30 = true := by
  decide +kernel

private def b0009c31 : List Row := [
  .p pv3 [pv2,pv3,pv13,pv349], .c 3, .p pv7 [pv2,pv5,pv8167], .c 23, .c 3,
  .p pv3 [pv2,pv7,pv2917], .c 13, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv10211], .c 151, .c 3,
  .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv19,pv43], .p pv3 [pv2,pv3,pv17,pv89], .c 3,
  .p pv2 [pv2,pv40853], .c 101, .c 3, .c 41, .c 5, .c 3, .c 11, .c 71, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv53,pv257], .c 3, .c 13, .c 37, .c 3, .p pv3 [pv2,pv17,pv601], .c 7, .c 3,
  .c 43, .c 5, .c 3, .p pv2 [pv2,pv107,pv191], .c 29, .c 3, .c 5, .c 13, .c 3,
  .p pv23 [pv2,pv5,pv7,pv73], .c 11, .c 3, .c 7, .p pv11 [pv2,pv3,pv3407], .c 3,
  .p pv2 [pv2,pv20443], .c 5, .c 3, .c 53, .c 7, .c 3, .c 5, .c 17, .c 3, .c 89, .c 263, .c 3,
  .c 157, .p pv3 [pv2,pv3,pv13633], .c 3, .c 179, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv487], .c 3, .c 17, .c 7, .c 3, .c 47, .c 11, .c 3, .c 19, .c 5, .c 3,
  .p pv7 [pv2,pv17,pv29,pv83], .c 223, .c 3, .c 5, .p pv3 [pv2,pv3,pv4547], .c 3, .c 7,
  .p pv11 [pv2,pv3,pv19,pv359], .c 3, .c 23, .c 109, .c 3, .c 71, .c 5, .c 3,
  .p pv2 [pv2,pv97,pv211], .c 19, .c 3, .c 5, .c 41, .c 3, .c 37, .p pv3 [pv2,pv3,pv4549], .c 3,
  .c 13, .c 17, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv40949], .p pv2 [pv2,pv3,pv5,pv7,pv13], .c 3,
  .c 5, .c 7, .c 3, .c 101, .c 13, .c 3, .c 11, .p pv3 [pv2,pv3,pv37,pv41], .c 3,
]
private theorem h0009c31 : checkBlock 81667 128 b0009c31 = true := by
  decide +kernel

def rows0009 : List Row :=
  b0009c00 ++ b0009c01 ++ b0009c02 ++ b0009c03 ++ b0009c04 ++ b0009c05 ++ b0009c06 ++ b0009c07 ++
  b0009c08 ++ b0009c09 ++ b0009c10 ++ b0009c11 ++ b0009c12 ++ b0009c13 ++ b0009c14 ++ b0009c15 ++
  b0009c16 ++ b0009c17 ++ b0009c18 ++ b0009c19 ++ b0009c20 ++ b0009c21 ++ b0009c22 ++ b0009c23 ++
  b0009c24 ++ b0009c25 ++ b0009c26 ++ b0009c27 ++ b0009c28 ++ b0009c29 ++ b0009c30 ++ b0009c31

theorem checked0009 : checkBlock 73731 4096 rows0009 = true :=
  checkBlock_append h0009c00 (
    checkBlock_append h0009c01 (
    checkBlock_append h0009c02 (
    checkBlock_append h0009c03 (
    checkBlock_append h0009c04 (
    checkBlock_append h0009c05 (
    checkBlock_append h0009c06 (
    checkBlock_append h0009c07 (
    checkBlock_append h0009c08 (
    checkBlock_append h0009c09 (
    checkBlock_append h0009c10 (
    checkBlock_append h0009c11 (
    checkBlock_append h0009c12 (
    checkBlock_append h0009c13 (
    checkBlock_append h0009c14 (
    checkBlock_append h0009c15 (
    checkBlock_append h0009c16 (
    checkBlock_append h0009c17 (
    checkBlock_append h0009c18 (
    checkBlock_append h0009c19 (
    checkBlock_append h0009c20 (
    checkBlock_append h0009c21 (
    checkBlock_append h0009c22 (
    checkBlock_append h0009c23 (
    checkBlock_append h0009c24 (
    checkBlock_append h0009c25 (
    checkBlock_append h0009c26 (
    checkBlock_append h0009c27 (
    checkBlock_append h0009c28 (
    checkBlock_append h0009c29 (
    checkBlock_append h0009c30 (
    h0009c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
