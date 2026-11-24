/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks00/Block0011
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks00/Block0011.checked0011
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table020

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0011c00 : List Row := [
  .c 5, .c 3, .c 227, .p pv23 [pv2,pv3,pv5,pv751], .c 3, .c 5, .p pv3 [pv2,pv3,pv1669], .c 3,
  .c 193, .c 173, .c 3, .c 23, .c 7, .c 3, .c 109, .c 5, .c 3, .p pv2 [pv2,pv31,pv727], .c 17,
  .c 3, .c 5, .c 89, .c 3, .c 29, .p pv2 [pv2,pv3,pv5009], .c 3, .c 7, .c 37, .c 3,
  .p pv2 [pv2,pv22543], .c 5, .c 3, .c 31, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv15031], .c 3,
  .p pv17 [pv2,pv5,pv29,pv311], .c 19, .c 3, .p pv2 [pv2,pv22549], .p pv3 [pv2,pv3,pv5011], .c 3,
  .p pv2 [pv2,pv7,pv17,pv379], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .p pv29 [pv2,pv3,pv7,pv179],
  .c 3, .c 83, .c 7, .c 3, .p pv2 [pv2,pv197,pv229], .c 23, .c 3, .c 11, .c 5, .c 3,
  .p pv7 [pv2,pv45119], .c 31, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv89], .c 3, .c 7, .c 17, .c 3,
  .c 43, .c 13, .c 3, .p pv5 [pv2,pv45131], .c 5, .c 3, .c 19, .p pv3 [pv2,pv3,pv5,pv17,pv59],
  .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv37,pv61], .c 137, .c 3, .c 17,
  .p pv23 [pv2,pv3,pv11,pv19], .c 3, .c 7, .c 5, .c 3, .c 11, .c 73, .c 3, .c 5, .c 7, .c 3,
  .c 13, .p pv5 [pv2,pv3,pv53,pv71], .c 3, .c 37, .c 181, .c 3, .c 41, .c 5, .c 3, .c 59, .c 103,
  .c 3, .c 5, .c 13, .c 3, .c 61, .c 11, .c 3, .c 167, .c 7, .c 3, .p pv3 [pv2,pv5647], .c 5,
  .c 3, .p pv11 [pv2,pv45179], .c 109, .c 3, .c 5, .c 23, .c 3,
]
private theorem h0011c00 : checkBlock 90115 128 b0011c00 = true := by
  decide +kernel

private def b0011c01 : List Row := [
  .p pv2 [pv2,pv5,pv7,pv1291], .p pv5 [pv2,pv3,pv17,pv443], .c 3, .c 7, .p pv2 [pv2,pv3,pv5021],
  .c 3, .c 19, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv31], .c 3,
  .p pv7 [pv2,pv5,pv113], .p pv3 [pv2,pv3,pv13,pv19,pv61], .c 3, .p pv5 [pv2,pv17,pv2659], .c 11,
  .c 3, .c 23, .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 31, .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv23,pv983], .p pv13 [pv2,pv3,pv15073], .c 3, .c 149, .c 5, .c 3, .c 151, .c 29,
  .c 3, .c 5, .c 17, .c 3, .c 7, .c 61, .c 3, .c 13, .p pv2 [pv2,pv3,pv7,pv359], .c 3,
  .p pv3 [pv2,pv43,pv263], .c 5, .c 3, .c 173, .p pv17 [pv2,pv3,pv5,pv13,pv29], .c 3, .c 5, .c 41,
  .c 3, .c 17, .c 13, .c 3, .c 11, .p pv2 [pv2,pv3,pv15083], .c 3, .c 7, .c 5, .c 3, .c 29,
  .p pv3 [pv2,pv3,pv5,pv7,pv431], .c 3, .c 5, .c 7, .c 3, .c 131, .p pv2 [pv2,pv3,pv47,pv107],
  .c 3, .p pv5 [pv2,pv45263], .p pv7 [pv2,pv3,pv23,pv41], .c 3, .p pv2 [pv2,pv13,pv1741], .c 5,
  .c 3, .c 37, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv15091], .c 3, .c 23, .c 83, .c 3, .c 137,
  .c 7, .c 3, .c 11, .c 5, .c 3, .c 41, .c 13, .c 3, .c 5, .c 53, .c 3, .c 239,
  .p pv5 [pv2,pv3,pv31,pv487], .c 3, .c 7, .c 157, .c 3, .c 17, .c 5, .c 3,
  .p pv11 [pv2,pv97,pv467], .c 7, .c 3, .c 5, .c 11, .c 3, .c 19, .c 31, .c 3,
  .p pv3 [pv2,pv47,pv241], .p pv3 [pv2,pv3,pv11,pv1373], .c 3, .c 13, .c 5,
]
private theorem h0011c01 : checkBlock 90371 128 b0011c01 = true := by
  decide +kernel

private def b0011c02 : List Row := [
  .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv19,pv53], .c 3, .c 5, .c 233, .c 3,
  .p pv3 [pv2,pv5,pv11,pv103], .c 7, .c 3, .p pv5 [pv2,pv61,pv743], .c 13, .c 3, .c 269, .c 5,
  .c 3, .p pv2 [pv2,pv45329], .c 17, .c 3, .c 5, .c 71, .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv22669], .p pv3 [pv2,pv3,pv7,pv17,pv127], .c 3, .c 29, .c 5, .c 3, .c 23, .c 89,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv3779], .c 3, .c 13, .p pv3 [pv2,pv3,pv5039], .c 3, .c 61,
  .p pv17 [pv2,pv3,pv7559], .c 3, .c 7, .c 5, .c 3, .c 83, .c 257, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv43,pv211], .c 41, .c 3, .c 31, .c 11, .c 3, .c 103, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv463], .c 151, .c 3, .c 5, .c 47, .c 3, .c 11, .c 17, .c 3, .c 139, .c 7, .c 3,
  .c 43, .c 5, .c 3, .c 13, .c 23, .c 3, .c 5, .p pv3 [pv2,pv3,pv15131], .c 3, .c 163,
  .p pv5 [pv2,pv3,pv13,pv97], .c 3, .c 7, .c 29, .c 3, .p pv2 [pv2,pv83,pv547], .c 5, .c 3, .c 71,
  .c 7, .c 3, .c 5, .c 197, .c 3, .p pv3 [pv2,pv5,pv19,pv239], .p pv61 [pv2,pv3,pv15137], .c 3,
  .c 11, .c 61, .c 3, .p pv3 [pv2,pv7,pv811], .c 5, .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv757], .c 3,
  .c 5, .p pv5 [pv2,pv3,pv7,pv103], .c 3, .c 47, .c 7, .c 3, .c 13, .c 43, .c 3,
  .p pv5 [pv2,pv181,pv251], .c 5, .c 3, .c 89, .c 11, .c 3, .c 5, .c 19, .c 3, .c 7,
]
private theorem h0011c02 : checkBlock 90627 128 b0011c02 = true := by
  decide +kernel

private def b0011c03 : List Row := [
  .c 13, .c 3, .p pv5 [pv2,pv29,pv1567], .c 97, .c 3, .c 11, .c 5, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv5,pv101], .c 3, .c 5, .p pv5 [pv2,pv3,pv109,pv139], .c 3,
  .p pv7 [pv2,pv5,pv9091], .c 229, .c 3, .p pv2 [pv2,pv7,pv17,pv191], .c 23, .c 3, .c 7, .c 5,
  .c 3, .c 79, .p pv11 [pv2,pv3,pv5,pv7,pv433], .c 3, .c 5, .c 7, .c 3, .c 211, .c 199, .c 3,
  .p pv2 [pv2,pv37,pv1229], .c 103, .c 3, .c 19, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 17,
  .c 3, .p pv2 [pv2,pv5,pv11,pv827], .c 29, .c 3, .p pv3 [pv2,pv2843], .c 7, .c 3, .c 37, .c 5,
  .c 3, .p pv2 [pv2,pv23,pv43], .c 19, .c 3, .c 5, .p pv5 [pv2,pv3,pv7583], .c 3, .c 17, .c 11,
  .c 3, .c 7, .p pv11 [pv2,pv3,pv79], .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv17,pv2677], .c 7,
  .c 3, .c 5, .c 227, .c 3, .c 29, .p pv5 [pv2,pv3,pv3793], .c 3, .c 59, .c 13, .c 3, .c 181,
  .c 5, .c 3, .c 7, .c 83, .c 3, .c 5, .c 23, .c 3, .c 41, .c 7, .c 3, .c 19, .c 11, .c 3, .c 61,
  .c 5, .c 3, .p pv7 [pv2,pv13,pv31,pv113], .p pv17 [pv2,pv3,pv5,pv11,pv23], .c 3, .c 5, .c 79,
  .c 3, .c 7, .c 71, .c 3, .p pv3 [pv2,pv59,pv193], .p pv2 [pv2,pv3,pv7,pv241], .c 3, .c 17, .c 5,
  .c 3, .c 31, .c 179, .c 3, .c 5, .c 13, .c 3, .p pv11 [pv2,pv5,pv17,pv67], .c 293, .c 3,
  .p pv5 [pv2,pv7,pv23,pv283], .p pv7 [pv2,pv3,pv3797], .c 3, .c 7, .c 5, .c 3,
]
private theorem h0011c03 : checkBlock 90883 128 b0011c03 = true := by
  decide +kernel

private def b0011c04 : List Row := [
  .p pv2 [pv2,pv45569], .p pv11 [pv2,pv3,pv5,pv7,pv31], .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv1823], .p pv7 [pv2,pv3,pv211], .c 3, .c 11, .p pv17 [pv2,pv3,pv15193], .c 3,
  .p pv2 [pv2,pv19,pv2399], .c 5, .c 3, .c 13, .c 17, .c 3, .c 5, .c 73, .c 3, .c 19,
  .p pv3 [pv2,pv3,pv7,pv13,pv167], .c 3, .c 67, .c 7, .c 3, .p pv3 [pv2,pv11399], .c 5, .c 3,
  .p pv11 [pv2,pv45599], .c 11, .c 3, .c 5, .c 223, .c 3, .c 197, .c 53, .c 3, .c 7, .c 19, .c 3,
  .c 11, .c 5, .c 3, .p pv2 [pv2,pv22807], .c 7, .c 3, .c 5, .p pv23 [pv2,pv3,pv7603], .c 3,
  .c 23, .p pv5 [pv2,pv3,pv37,pv137], .c 3, .c 13, .p pv17 [pv2,pv3,pv1901], .c 3,
  .p pv2 [pv2,pv7,pv3259], .c 5, .c 3, .c 7, .c 263, .c 3, .c 5, .c 11, .c 3, .c 107, .c 7, .c 3,
  .c 97, .c 37, .c 3, .p pv2 [pv2,pv45641], .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv17,pv179],
  .c 3, .c 5, .p pv5 [pv2,pv3,pv317], .c 3, .c 7, .p pv3 [pv2,pv3,pv15217], .c 3, .c 17,
  .p pv29 [pv2,pv3,pv7,pv1087], .c 3, .c 127, .c 5, .c 3, .c 53, .c 29, .c 3, .c 5, .c 271, .c 3,
  .p pv2 [pv2,pv5,pv9133], .c 11, .c 3, .c 149, .c 241, .c 3, .c 7, .c 5, .c 3, .c 167, .c 13,
  .c 3, .c 5, .c 7, .c 3, .c 103, .c 211, .c 3, .p pv11 [pv2,pv11,pv4153], .p pv7 [pv2,pv3,pv47],
  .c 3, .p pv3 [pv2,pv53,pv431], .c 5, .c 3, .c 23, .p pv17 [pv2,pv3,pv5,pv1523], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv5077], .c 3, .c 59, .p pv23 [pv2,pv3,pv7,pv17],
]
private theorem h0011c04 : checkBlock 91139 128 b0011c04 = true := by
  decide +kernel

private def b0011c05 : List Row := [
  .c 3, .p pv2 [pv2,pv73,pv313], .c 7, .c 3, .c 13, .c 5, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv5,pv11,pv277], .c 3, .c 5, .c 113, .c 3, .c 11, .p pv3 [pv2,pv3,pv1693], .c 3,
  .c 7, .c 13, .c 3, .p pv3 [pv2,pv11,pv1039], .c 5, .c 3, .c 61, .c 7, .c 3, .c 5, .c 19, .c 3,
  .c 109, .p pv7 [pv2,pv3,pv7621], .c 3, .p pv3 [pv2,pv1429], .p pv2 [pv2,pv3,pv5081], .c 3,
  .p pv5 [pv2,pv7,pv47,pv139], .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 17, .c 3, .c 13, .c 7,
  .c 3, .c 11, .c 191, .c 3, .p pv2 [pv2,pv89,pv257], .c 5, .c 3, .p pv2 [pv2,pv11,pv4159], .c 37,
  .c 3, .c 5, .c 13, .c 3, .c 7, .p pv13 [pv2,pv3,pv31,pv41], .c 3, .c 23, .c 71, .c 3, .c 19,
  .c 5, .c 3, .p pv3 [pv2,pv17,pv673], .c 11, .c 3, .c 5, .c 239, .c 3,
  .p pv2 [pv2,pv5,pv23,pv199], .c 31, .c 3, .c 43, .c 83, .c 3, .c 7, .c 5, .c 3, .c 13, .c 19,
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv9157], .p pv5 [pv2,pv3,pv13,pv587], .c 3,
  .p pv3 [pv2,pv11447], .c 17, .c 3, .p pv5 [pv2,pv29,pv1579], .c 5, .c 3, .c 67,
  .p pv3 [pv2,pv3,pv5,pv43,pv71], .c 3, .c 5, .c 11, .c 3, .c 139, .c 47, .c 3, .c 101, .c 7,
  .c 3, .c 17, .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv509], .c 3, .c 5, .c 59, .c 3,
  .p pv7 [pv2,pv5,pv7,pv11,pv17], .c 43, .c 3, .c 7, .p pv3 [pv2,pv3,pv1697], .c 3, .c 113, .c 5,
  .c 3, .c 37,
]
private theorem h0011c05 : checkBlock 91395 128 b0011c05 = true := by
  decide +kernel

private def b0011c06 : List Row := [
  .c 7, .c 3, .c 5, .c 151, .c 3, .c 71, .c 11, .c 3, .c 31, .c 29, .c 3, .p pv3 [pv2,pv7,pv1637],
  .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 277, .c 3, .p pv2 [pv2,pv5,pv53,pv173], .c 7, .c 3,
  .c 47, .c 107, .c 3, .p pv5 [pv2,pv13,pv3527], .c 5, .c 3, .c 293, .p pv11 [pv2,pv3,pv5,pv1019],
  .c 3, .c 5, .c 41, .c 3, .c 7, .c 37, .c 3, .c 29, .c 11, .c 3, .p pv2 [pv2,pv17,pv19,pv71],
  .c 5, .c 3, .c 199, .c 13, .c 3, .c 5, .c 23, .c 3, .c 11, .p pv11 [pv2,pv3,pv3823], .c 3,
  .p pv2 [pv2,pv7,pv29,pv113], .c 89, .c 3, .c 7, .c 5, .c 3, .c 163,
  .p pv2 [pv2,pv3,pv5,pv7,pv19,pv23], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv13,pv353], .c 17,
  .c 3, .c 263, .c 19, .c 3, .c 13, .c 5, .c 3, .c 41, .p pv13 [pv2,pv3,pv5,pv17], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv13,pv107], .c 3, .p pv2 [pv2,pv5,pv9181], .p pv2 [pv2,pv3,pv7,pv1093],
  .c 3, .c 11, .c 7, .c 3, .p pv5 [pv2,pv31,pv1481], .c 5, .c 3, .c 229, .c 131, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv2551], .c 3, .p pv3 [pv2,pv5,pv7,pv41], .c 29, .c 3, .c 7, .c 53, .c 3, .c 31,
  .c 5, .c 3, .c 97, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv61,pv251], .c 3, .c 13,
  .p pv5 [pv2,pv3,pv11,pv29], .c 3, .c 79, .c 139, .c 3, .c 11, .c 5, .c 3, .c 7, .c 43, .c 3,
  .c 5, .c 13, .c 3, .c 29, .c 7, .c 3,
]
private theorem h0011c06 : checkBlock 91651 128 b0011c06 = true := by
  decide +kernel

private def b0011c07 : List Row := [
  .c 73, .p pv2 [pv2,pv3,pv23,pv37], .c 3, .c 107, .c 5, .c 3, .c 17, .p pv13 [pv2,pv3,pv5,pv383],
  .c 3, .c 5, .c 11, .c 3, .c 7, .c 149, .c 3, .c 89, .p pv2 [pv2,pv3,pv7,pv11,pv199], .c 3,
  .p pv5 [pv2,pv45971], .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv613], .c 3, .c 5,
  .p pv7 [pv2,pv3,pv79,pv97], .c 3, .p pv23 [pv2,pv5,pv11,pv19], .c 41, .c 3,
  .p pv5 [pv2,pv7,pv6569], .p pv13 [pv2,pv3,pv479], .c 3, .c 7, .c 5, .c 3, .c 19, .c 59, .c 3,
  .c 5, .c 7, .c 3, .c 67, .c 11, .c 3, .p pv2 [pv2,pv109,pv211], .c 197, .c 3,
  .p pv2 [pv2,pv157,pv293], .c 5, .c 3, .p pv3 [pv2,pv7,pv31,pv53], .c 101, .c 3, .c 5, .c 19,
  .c 3, .c 17, .c 23, .c 3, .c 13, .c 7, .c 3, .p pv3 [pv2,pv719], .c 5, .c 3, .c 31,
  .p pv7 [pv2,pv3,pv5,pv13,pv59], .c 3, .c 5, .c 83, .c 3, .p pv7 [pv2,pv5,pv7,pv263], .c 13,
  .c 3, .c 7, .c 11, .c 3, .c 43, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv7673],
  .c 3, .c 11, .p pv2 [pv2,pv3,pv103,pv149], .c 3, .c 71, .c 17, .c 3, .c 19, .c 5, .c 3, .c 7,
  .c 31, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv17,pv43], .c 3, .p pv13 [pv2,pv5,pv61,pv151], .c 7,
  .c 3, .c 251, .p pv3 [pv2,pv3,pv13,pv1181], .c 3, .c 17, .c 5, .c 3, .c 181, .c 13, .c 3, .c 5,
  .c 199, .c 3, .c 7, .p pv5 [pv2,pv3,pv5119], .c 3, .c 11, .c 43, .c 3, .p pv3 [pv2,pv11519],
  .c 5, .c 3, .c 157, .c 23,
]
private theorem h0011c07 : checkBlock 91907 128 b0011c07 = true := by
  decide +kernel

private def b0011c08 : List Row := [
  .c 3, .c 5, .c 37, .c 3, .c 61, .p pv2 [pv2,pv3,pv7681], .c 3, .p pv11 [pv2,pv7,pv823],
  .p pv3 [pv2,pv3,pv569], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv19,pv1213], .c 11, .c 3, .c 5,
  .c 7, .c 3, .c 137, .p pv2 [pv2,pv3,pv11,pv127], .c 3, .c 19, .c 13, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv941], .p pv7 [pv2,pv3,pv5,pv29,pv53], .c 3, .c 5, .p pv3 [pv2,pv3,pv19,pv809],
  .c 3, .c 149, .p pv5 [pv2,pv3,pv7,pv61], .c 3, .p pv2 [pv2,pv23059], .c 7, .c 3,
  .p pv2 [pv2,pv17,pv2713], .c 5, .c 3, .c 29, .p pv2 [pv2,pv3,pv5,pv41], .c 3, .c 5, .c 11, .c 3,
  .c 13, .c 257, .c 3, .c 7, .p pv13 [pv2,pv3,pv11,pv233], .c 3, .c 53, .c 5, .c 3, .c 11, .c 7,
  .c 3, .c 5, .c 13, .c 3, .c 41, .c 17, .c 3, .p pv3 [pv2,pv83,pv139], .c 23, .c 3, .c 241, .c 5,
  .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv17,pv181], .c 3, .c 5, .p pv17 [pv2,pv3,pv7,pv157], .c 3,
  .c 19, .c 7, .c 3, .c 17, .c 127, .c 3, .p pv2 [pv2,pv41,pv563], .c 5, .c 3, .c 13, .c 107,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv15391], .c 3, .c 7, .p pv5 [pv2,pv3,pv13,pv37], .c 3,
  .p pv3 [pv2,pv11,pv2099], .c 19, .c 3, .p pv2 [pv2,pv46181], .c 5, .c 3,
  .p pv3 [pv2,pv23,pv251], .c 71, .c 3, .c 5, .p pv7 [pv2,pv3,pv1283], .c 3,
  .p pv2 [pv2,pv5,pv31,pv149], .p pv3 [pv2,pv3,pv89,pv173], .c 3, .p pv2 [pv2,pv7,pv6599], .c 11,
  .c 3, .c 7, .c 5, .c 3, .p pv13 [pv2,pv46199], .p pv41 [pv2,pv3,pv5,pv7,pv11], .c 3, .c 5, .c 7,
  .c 3, .c 11, .p pv2 [pv2,pv3,pv17,pv151], .c 3, .c 13,
]
private theorem h0011c08 : checkBlock 92163 128 b0011c08 = true := by
  decide +kernel

private def b0011c09 : List Row := [
  .p pv2 [pv2,pv3,pv73,pv211], .c 3, .c 29, .c 5, .c 3, .c 17, .p pv41 [pv2,pv3,pv5,pv13,pv79],
  .c 3, .c 5, .c 23, .c 3, .c 97, .c 13, .c 3, .c 193, .c 7, .c 3, .c 59, .c 5, .c 3,
  .p pv2 [pv2,pv46229], .p pv2 [pv2,pv3,pv5,pv23,pv67], .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv467],
  .c 3, .c 89, .c 19, .c 3, .c 7, .p pv7 [pv2,pv3,pv15413], .c 3, .c 23, .c 5, .c 3,
  .p pv3 [pv2,pv11,pv1051], .c 7, .c 3, .c 5, .c 17, .c 3, .c 233, .p pv5 [pv2,pv3,pv571], .c 3,
  .p pv2 [pv2,pv23,pv2011], .c 79, .c 3, .c 71, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 67, .c 3,
  .c 17, .c 7, .c 3, .c 37, .c 29, .c 3, .c 11, .c 5, .c 3, .c 19, .p pv7 [pv2,pv3,pv5,pv617],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv857], .c 3, .c 7, .c 151, .c 3, .p pv5 [pv2,pv31,pv1493],
  .p pv31 [pv2,pv3,pv7,pv19,pv29], .c 3, .c 13, .c 5, .c 3, .c 43, .p pv7 [pv2,pv3,pv5,pv1543],
  .c 3, .c 5, .c 11, .c 3, .c 53, .p pv5 [pv2,pv3,pv643], .c 3, .c 29, .c 13, .c 3, .c 7, .c 5,
  .c 3, .c 11, .c 37, .c 3, .c 5, .c 7, .c 3, .c 23, .p pv11 [pv2,pv3,pv43,pv359], .c 3,
  .p pv2 [pv2,pv29,pv1597], .c 211, .c 3, .c 17, .c 5, .c 3, .p pv7 [pv2,pv7,pv13,pv509],
  .p pv11 [pv2,pv3,pv5,pv193], .c 3, .c 5, .p pv3 [pv2,pv3,pv5147], .c 3, .c 13, .c 11, .c 3,
  .p pv3 [pv2,pv5791], .c 7, .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv23167],
  .p pv3 [pv2,pv3,pv5,pv3089], .c 3,
]
private theorem h0011c09 : checkBlock 92419 128 b0011c09 = true := by
  decide +kernel

private def b0011c10 : List Row := [
  .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv7,pv331], .p pv3 [pv2,pv3,pv19,pv271], .c 3, .c 7, .c 59,
  .c 3, .p pv2 [pv2,pv23173], .c 5, .c 3, .p pv2 [pv2,pv46349], .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv15451], .c 3, .c 83, .c 23, .c 3, .p pv2 [pv2,pv13,pv1783], .c 11, .c 3,
  .p pv2 [pv2,pv7,pv37,pv179], .c 5, .c 3, .c 7, .c 47, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv23],
  .c 3, .c 11, .c 7, .c 3, .c 163, .c 137, .c 3, .p pv3 [pv2,pv11,pv17,pv31], .c 5, .c 3, .c 23,
  .p pv37 [pv2,pv3,pv5,pv773], .c 3, .c 5, .p pv3 [pv2,pv3,pv15461], .c 3, .c 7, .c 113, .c 3,
  .c 19, .p pv2 [pv2,pv3,pv7,pv47], .c 3, .c 31, .c 5, .c 3, .p pv2 [pv2,pv23197],
  .p pv23 [pv2,pv3,pv5,pv1031], .c 3, .c 5, .c 71, .c 3, .p pv3 [pv2,pv5,pv29], .c 17, .c 3,
  .c 11, .p pv19 [pv2,pv3,pv1289], .c 3, .c 7, .c 5, .c 3, .c 101,
  .p pv47 [pv2,pv3,pv5,pv7,pv13,pv17], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv9283], .c 13,
  .c 3, .c 17, .c 263, .c 3, .c 227, .c 5, .c 3, .p pv3 [pv2,pv7,pv829], .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv53,pv73], .c 3, .p pv2 [pv2,pv5,pv4643], .p pv7 [pv2,pv3,pv7,pv11,pv67], .c 3,
  .p pv2 [pv2,pv59,pv787], .c 7, .c 3, .c 11, .c 5, .c 3, .c 131, .c 293, .c 3, .c 5, .c 29, .c 3,
  .c 19, .p pv5 [pv2,pv3,pv7741], .c 3, .c 7, .p pv7 [pv2,pv3,pv13,pv397], .c 3, .c 61, .c 5,
  .c 3, .c 53, .c 7, .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv23,pv101], .c 43, .c 3,
  .p pv5 [pv2,pv97,pv479], .c 19,
]
private theorem h0011c10 : checkBlock 92675 128 b0011c10 = true := by
  decide +kernel

private def b0011c11 : List Row := [
  .c 3, .c 199, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv1549], .c 3, .c 5, .c 41, .c 3,
  .p pv11 [pv2,pv5,pv11,pv13], .c 7, .c 3, .p pv2 [pv2,pv17,pv1367], .p pv11 [pv2,pv3,pv15493],
  .c 3, .c 13, .c 5, .c 3, .c 31, .c 239, .c 3, .c 5, .c 109, .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv19,pv2447], .c 13, .c 3, .p pv3 [pv2,pv1453], .c 5, .c 3, .c 113,
  .p pv17 [pv2,pv3,pv5,pv31], .c 3, .c 5, .c 17, .c 3, .c 281, .c 47, .c 3, .c 191, .c 167, .c 3,
  .c 7, .c 5, .c 3, .c 41, .c 31, .c 3, .c 5, .c 7, .c 3, .c 13, .c 19, .c 3,
  .p pv5 [pv2,pv46523], .c 11, .c 3, .p pv2 [pv2,pv43,pv541], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv17,pv23], .c 29, .c 3, .c 5, .c 13, .c 3, .c 11, .c 163, .c 3,
  .p pv2 [pv2,pv23269], .c 7, .c 3, .p pv2 [pv2,pv11,pv4231], .c 5, .c 3, .p pv3 [pv2,pv2909],
  .c 127, .c 3, .c 5, .p pv17 [pv2,pv3,pv431], .c 3, .c 157, .p pv5 [pv2,pv3,pv59,pv263], .c 3,
  .c 7, .c 17, .c 3, .p pv3 [pv2,pv103,pv113], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 23, .c 3,
  .p pv17 [pv2,pv5,pv67,pv139], .p pv7 [pv2,pv3,pv13,pv199], .c 3, .c 11,
  .p pv2 [pv2,pv3,pv19,pv43], .c 3, .c 17, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv23], .c 3,
  .c 5, .c 19, .c 3, .c 59, .c 7, .c 3, .c 151, .p pv11 [pv2,pv3,pv647], .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv46589], .c 11, .c 3, .c 5,
]
private theorem h0011c11 : checkBlock 92931 128 b0011c11 = true := by
  decide +kernel

private def b0011c12 : List Row := [
  .p pv3 [pv2,pv3,pv31,pv167], .c 3, .c 7, .c 41, .c 3, .c 13, .p pv7 [pv2,pv3,pv7,pv317], .c 3,
  .c 11, .c 5, .c 3, .c 83, .c 17, .c 3, .c 5, .c 31, .c 3, .c 73, .c 13, .c 3, .c 53,
  .p pv13 [pv2,pv3,pv17,pv457], .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv46619],
  .p pv13 [pv2,pv3,pv5,pv7,pv37], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv373],
  .p pv2 [pv2,pv3,pv19,pv409], .c 3, .p pv3 [pv2,pv11657], .c 179, .c 3,
  .p pv5 [pv2,pv13,pv17,pv211], .c 5, .c 3, .c 11, .c 19, .c 3, .c 5, .c 37, .c 3,
  .p pv3 [pv2,pv5,pv11,pv53], .p pv2 [pv2,pv3,pv7,pv2221], .c 3, .p pv5 [pv2,pv46643], .c 7, .c 3,
  .c 29, .c 5, .c 3, .c 79, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv15551], .c 3, .c 23, .c 11, .c 3,
  .c 7, .p pv3 [pv2,pv3,pv103,pv151], .c 3, .p pv2 [pv2,pv29,pv1609], .c 5, .c 3,
  .p pv3 [pv2,pv19,pv307], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv3889], .c 3, .c 31, .c 269, .c 3,
  .c 17, .c 277, .c 3, .c 13, .c 5, .c 3, .c 7, .c 89, .c 3, .c 5, .c 73, .c 3,
  .p pv2 [pv2,pv5,pv9337], .c 7, .c 3, .p pv3 [pv2,pv1459], .c 11, .c 3, .p pv5 [pv2,pv46691],
  .c 5, .c 3, .c 47, .c 61, .c 3, .c 5, .c 59, .c 3, .c 7, .c 23, .c 3, .p pv5 [pv2,pv46703],
  .c 29, .c 3, .c 109, .c 5, .c 3, .p pv2 [pv2,pv13,pv3593], .c 103, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv23,pv677], .c 3, .c 13, .c 233, .c 3, .c 223, .c 41, .c 3,
]
private theorem h0011c12 : checkBlock 93187 128 b0011c12 = true := by
  decide +kernel

private def b0011c13 : List Row := [
  .c 7, .c 5, .c 3, .c 17, .c 113, .c 3, .c 5, .c 7, .c 3, .c 19, .p pv3 [pv2,pv3,pv37,pv421],
  .c 3, .c 11, .c 151, .c 3, .c 211, .c 5, .c 3, .p pv7 [pv2,pv7,pv11,pv607],
  .p pv107 [pv2,pv3,pv5,pv19,pv41], .c 3, .c 5, .p pv7 [pv2,pv3,pv15581], .c 3,
  .p pv2 [pv2,pv5,pv9349], .p pv2 [pv2,pv3,pv7,pv53], .c 3, .p pv3 [pv2,pv13,pv29,pv31], .c 7,
  .c 3, .p pv5 [pv2,pv46751], .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 17, .c 3, .c 41,
  .p pv2 [pv2,pv3,pv11,pv13,pv109], .c 3, .c 7, .p pv11 [pv2,pv3,pv433], .c 3, .c 11, .c 5, .c 3,
  .c 89, .c 7, .c 3, .c 5, .c 139, .c 3, .c 17, .p pv5 [pv2,pv3,pv1949], .c 3,
  .p pv2 [pv2,pv19,pv1231], .p pv3 [pv2,pv3,pv31,pv503], .c 3, .p pv5 [pv2,pv7,pv41,pv163], .c 5,
  .c 3, .c 7, .c 137, .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv4679], .c 7, .c 3, .c 13, .c 31,
  .c 3, .c 173, .c 5, .c 3, .c 11, .p pv23 [pv2,pv3,pv5,pv13], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv15601], .c 3, .c 7, .c 13, .c 3, .c 179, .c 17, .c 3, .c 251, .c 5, .c 3,
  .p pv2 [pv2,pv89,pv263], .c 109, .c 3, .c 5, .p pv5 [pv2,pv3,pv17], .c 3, .c 29, .c 11, .c 3,
  .c 37, .c 71, .c 3, .c 7, .c 5, .c 3, .c 73, .c 229, .c 3, .c 5, .c 7, .c 3, .c 47, .c 283,
  .c 3, .c 113, .c 23, .c 3, .p pv2 [pv2,pv31,pv1511], .c 5, .c 3, .c 19, .c 13, .c 3, .c 5,
  .c 43,
]
private theorem h0011c13 : checkBlock 93443 128 b0011c13 = true := by
  decide +kernel

private def b0011c14 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv937], .p pv5 [pv2,pv3,pv7,pv23,pv97], .c 3, .c 83, .c 7, .c 3, .c 31,
  .c 5, .c 3, .p pv13 [pv2,pv47,pv997], .c 17, .c 3, .c 5, .c 19, .c 3, .c 11, .c 67, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv17,pv919], .c 3, .c 13, .c 5, .c 3, .c 241, .c 7, .c 3, .c 5, .c 29, .c 3,
  .p pv11 [pv2,pv5,pv293], .p pv2 [pv2,pv3,pv5209], .c 3, .c 41, .c 13, .c 3, .c 79, .c 5, .c 3,
  .c 7, .c 191, .c 3, .c 5, .p pv7 [pv2,pv3,pv7,pv11,pv29], .c 3, .c 71, .c 7, .c 3, .c 11, .c 97,
  .c 3, .c 19, .c 5, .c 3, .p pv3 [pv2,pv11,pv13,pv41], .p pv2 [pv2,pv3,pv5,pv53,pv59], .c 3,
  .c 5, .c 23, .c 3, .c 7, .c 17, .c 3, .p pv2 [pv2,pv43,pv1091], .c 101, .c 3, .c 103, .c 5,
  .c 3, .c 107, .c 11, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv1877], .c 127, .c 3, .c 17,
  .c 47, .c 3, .c 7, .c 5, .c 3, .c 37, .p pv3 [pv2,pv3,pv5,pv7,pv149], .c 3, .c 5, .c 7, .c 3,
  .c 269, .c 223, .c 3, .p pv5 [pv2,pv13,pv23,pv157], .p pv19 [pv2,pv3,pv163], .c 3,
  .p pv2 [pv2,pv23473], .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv313], .c 3, .c 5, .c 11, .c 3,
  .p pv11 [pv2,pv5,pv9391], .p pv5 [pv2,pv3,pv7,pv13,pv43], .c 3, .c 19, .c 7, .c 3,
  .p pv2 [pv2,pv151,pv311], .c 5, .c 3, .c 11, .c 29, .c 3, .c 5, .p pv17 [pv2,pv3,pv19,pv103],
  .c 3, .p pv2 [pv2,pv5,pv7,pv11,pv61], .c 37, .c 3, .c 7, .p pv2 [pv2,pv3,pv7829], .c 3, .c 47,
]
private theorem h0011c14 : checkBlock 93699 128 b0011c14 = true := by
  decide +kernel

private def b0011c15 : List Row := [
  .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .p pv11 [pv2,pv3,pv15661], .c 3, .p pv2 [pv2,pv5,pv9397],
  .c 11, .c 3, .c 13, .p pv3 [pv2,pv3,pv23,pv227], .c 3, .p pv5 [pv2,pv7,pv137], .c 5, .c 3, .c 7,
  .c 193, .c 3, .c 5, .p pv11 [pv2,pv3,pv7,pv373], .c 3, .c 23, .c 7, .c 3,
  .p pv5 [pv2,pv11,pv4273], .p pv13 [pv2,pv3,pv3917], .c 3, .c 41, .c 5, .c 3, .c 149, .c 167,
  .c 3, .c 5, .c 17, .c 3, .c 7, .p pv47 [pv2,pv3,pv653], .c 3, .c 271, .c 11, .c 3, .c 157, .c 5,
  .c 3, .p pv3 [pv2,pv2939], .c 163, .c 3, .c 5, .p pv7 [pv2,pv3,pv3919], .c 3, .c 11,
  .p pv3 [pv2,pv3,pv61,pv257], .c 3, .c 109, .c 19, .c 3, .c 7, .c 5, .c 3,
  .p pv13 [pv2,pv17,pv2767], .c 13, .c 3, .c 5, .c 7, .c 3, .c 37, .c 23, .c 3, .c 73,
  .p pv2 [pv2,pv3,pv15683], .c 3, .c 139, .c 5, .c 3, .p pv2 [pv2,pv7,pv3361],
  .p pv3 [pv2,pv3,pv5,pv3137], .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv23,pv31], .c 3,
  .p pv3 [pv2,pv5,pv13,pv181], .c 61, .c 3, .c 11, .c 7, .c 3, .c 13, .c 5, .c 3, .c 23, .c 47,
  .c 3, .c 5, .c 31, .c 3, .p pv7 [pv2,pv5,pv7,pv269], .p pv5 [pv2,pv3,pv3923], .c 3, .c 7, .c 13,
  .c 3, .c 17, .c 5, .c 3, .p pv3 [pv2,pv79,pv149], .c 7, .c 3, .c 5, .c 41, .c 3, .c 53, .c 19,
  .c 3, .c 97, .c 131, .c 3, .c 11, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv157], .c 3, .c 5,
  .p pv11 [pv2,pv3,pv7,pv2243], .c 3,
]
private theorem h0011c15 : checkBlock 93955 128 b0011c15 = true := by
  decide +kernel

private def b0011c16 : List Row := [
  .c 13, .c 7, .c 3, .c 71, .p pv3 [pv2,pv3,pv41,pv383], .c 3, .c 59, .c 5, .c 3,
  .p pv2 [pv2,pv23557], .c 17, .c 3, .c 5, .c 11, .c 3, .c 7, .c 73, .c 3, .c 79, .c 307, .c 3,
  .p pv2 [pv2,pv23563], .c 5, .c 3, .c 11, .p pv11 [pv2,pv3,pv5,pv1571], .c 3, .c 5, .c 107, .c 3,
  .c 31, .p pv5 [pv2,pv3,pv491], .c 3, .c 23, .c 29, .c 3, .c 7, .c 5, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv5,pv7,pv449], .c 3, .c 5, .c 7, .c 3, .c 181, .c 11, .c 3,
  .p pv2 [pv2,pv61,pv773], .p pv7 [pv2,pv3,pv29,pv271], .c 3, .c 37, .c 5, .c 3, .c 257,
  .p pv7 [pv2,pv3,pv5,pv131], .c 3, .c 5, .p pv3 [pv2,pv3,pv79,pv199], .c 3,
  .p pv2 [pv2,pv5,pv9433], .c 17, .c 3, .c 29, .c 7, .c 3, .p pv5 [pv2,pv43,pv1097], .c 5, .c 3,
  .p pv2 [pv2,pv103,pv229], .p pv3 [pv2,pv3,pv5,pv17,pv37], .c 3, .c 5, .c 157, .c 3, .c 127,
  .c 197, .c 3, .c 7, .c 11, .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv47189], .c 7, .c 3, .c 5,
  .c 37, .c 3, .c 11, .c 13, .c 3, .p pv2 [pv2,pv23599], .p pv3 [pv2,pv3,pv15733], .c 3, .c 67,
  .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 263, .c 3, .p pv2 [pv2,pv5,pv4721], .c 7, .c 3,
  .p pv2 [pv2,pv31,pv1523], .c 89, .c 3, .p pv5 [pv2,pv13,pv227], .c 5, .c 3,
  .p pv7 [pv2,pv23,pv2053], .p pv11 [pv2,pv3,pv5,pv787], .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv53],
  .c 3, .c 7, .c 29, .c 3, .c 11, .c 59, .c 3, .p pv5 [pv2,pv73,pv647], .c 5,
]
private theorem h0011c16 : checkBlock 94211 128 b0011c16 = true := by
  decide +kernel

private def b0011c17 : List Row := [
  .c 3, .c 17, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv7873], .c 3, .c 107,
  .p pv2 [pv2,pv3,pv29,pv181], .c 3, .c 19, .c 61, .c 3, .c 7, .c 5, .c 3, .c 53, .c 11, .c 3,
  .c 5, .c 7, .c 3, .c 29, .p pv5 [pv2,pv3,pv11,pv179], .c 3, .c 47, .c 31, .c 3, .c 11, .c 5,
  .c 3, .p pv3 [pv2,pv7,pv211], .p pv13 [pv2,pv3,pv5,pv23,pv137], .c 3, .c 5, .c 17, .c 3,
  .p pv2 [pv2,pv5,pv29,pv163], .p pv3 [pv2,pv3,pv7,pv2251], .c 3, .p pv2 [pv2,pv41,pv1153], .c 7,
  .c 3, .c 23, .c 5, .c 3, .p pv11 [pv2,pv47279], .p pv17 [pv2,pv3,pv5,pv197], .c 3, .c 5, .c 11,
  .c 3, .c 17, .p pv2 [pv2,pv3,pv37,pv71], .c 3, .c 7, .c 271, .c 3, .p pv5 [pv2,pv19,pv131],
  .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv7883], .c 3, .c 13,
  .p pv5 [pv2,pv3,pv15767], .c 3, .c 89, .c 37, .c 3, .p pv3 [pv2,pv7,pv31,pv109], .c 5, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv5,pv19,pv83], .c 3, .c 5, .c 13, .c 3, .c 173, .c 7, .c 3, .c 101,
  .c 17, .c 3, .c 31, .c 5, .c 3, .p pv3 [pv2,pv11831], .p pv2 [pv2,pv3,pv5,pv631], .c 3, .c 5,
  .c 103, .c 3, .c 7, .c 181, .c 3, .c 137, .c 41, .c 3, .c 17, .c 5, .c 3, .c 13, .c 73, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv43,pv367], .c 3, .c 23, .p pv5 [pv2,pv3,pv13,pv607], .c 3, .c 281,
  .c 11, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv23677], .c 53, .c 3, .c 5, .c 7, .c 3, .c 11,
]
private theorem h0011c17 : checkBlock 94467 128 b0011c17 = true := by
  decide +kernel

private def b0011c18 : List Row := [
  .p pv2 [pv2,pv3,pv15787], .c 3, .p pv5 [pv2,pv47363], .c 43, .c 3, .c 61, .c 5, .c 3, .c 211,
  .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv15791], .c 3, .c 41, .c 19, .c 3, .c 13, .c 7, .c 3,
  .c 193, .c 5, .c 3, .c 97, .p pv31 [pv2,pv3,pv5,pv13], .c 3, .c 5, .p pv13 [pv2,pv3,pv11,pv359],
  .c 3, .p pv2 [pv2,pv5,pv7,pv677], .c 13, .c 3, .c 7, .p pv2 [pv2,pv3,pv2633], .c 3,
  .p pv3 [pv2,pv17,pv41], .c 5, .c 3, .c 47, .c 7, .c 3, .c 5, .c 113, .c 3,
  .p pv2 [pv2,pv5,pv19,pv499], .c 59, .c 3, .c 53, .p pv2 [pv2,pv3,pv15803], .c 3,
  .p pv5 [pv2,pv7,pv13,pv521], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv1129],
  .c 3, .p pv3 [pv2,pv5,pv2371], .c 7, .c 3, .p pv5 [pv2,pv47,pv1009], .p pv7 [pv2,pv3,pv13,pv19],
  .c 3, .c 11, .c 5, .c 3, .c 29, .c 13, .c 3, .c 5, .c 19, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv59,pv67], .c 3, .c 17, .c 79, .c 3, .c 239, .c 5, .c 3,
  .p pv3 [pv2,pv29,pv409], .c 31, .c 3, .c 5, .c 11, .c 3, .c 43, .p pv3 [pv2,pv3,pv15817], .c 3,
  .p pv2 [pv2,pv7,pv6779], .c 107, .c 3, .c 7, .c 5, .c 3, .c 11, .c 23, .c 3, .c 5, .c 7, .c 3,
  .c 59, .p pv2 [pv2,pv3,pv293], .c 3, .c 139, .c 13, .c 3, .c 19, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv3391], .p pv59 [pv2,pv3,pv5,pv211], .c 3, .c 5, .c 269, .c 3,
  .p pv3 [pv2,pv5,pv1187], .c 11, .c 3, .c 23, .c 7, .c 3, .c 73, .c 5, .c 3,
]
private theorem h0011c18 : checkBlock 94723 128 b0011c18 = true := by
  decide +kernel

private def b0011c19 : List Row := [
  .c 17, .c 19, .c 3, .c 5, .c 43, .c 3, .c 13, .p pv11 [pv2,pv3,pv1979], .c 3, .c 7,
  .p pv3 [pv2,pv3,pv71,pv223], .c 3, .p pv2 [pv2,pv47501], .c 5, .c 3, .p pv3 [pv2,pv2969], .c 7,
  .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv4751], .c 167, .c 3, .p pv2 [pv2,pv47513], .c 11,
  .c 3, .c 29, .c 5, .c 3, .c 7, .c 101, .c 3, .c 5, .c 17, .c 3, .c 11, .c 7, .c 3, .c 19, .c 23,
  .c 3, .p pv5 [pv2,pv11,pv29,pv149], .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv3169], .c 3, .c 5,
  .c 31, .c 3, .c 7, .p pv2 [pv2,pv3,pv13,pv23,pv53], .c 3, .p pv5 [pv2,pv47543],
  .p pv13 [pv2,pv3,pv7,pv283], .c 3, .p pv2 [pv2,pv23773], .c 5, .c 3, .c 61,
  .p pv2 [pv2,pv3,pv5,pv317], .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv131], .c 3,
  .p pv11 [pv2,pv5,pv9511], .c 227, .c 3, .c 11, .c 73, .c 3, .c 7, .c 5, .c 3, .c 251,
  .p pv7 [pv2,pv3,pv5,pv7,pv151], .c 3, .c 5, .c 7, .c 3, .c 89, .p pv3 [pv2,pv3,pv101,pv157],
  .c 3, .c 13, .c 17, .c 3, .p pv3 [pv2,pv19,pv313], .c 5, .c 3, .c 43, .c 11, .c 3, .c 5, .c 59,
  .c 3, .c 19, .c 13, .c 3, .p pv3 [pv2,pv11897], .c 7, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv53,pv449], .p pv13 [pv2,pv3,pv5,pv19,pv167], .c 3, .c 5, .c 23, .c 3, .c 31,
  .p pv2 [pv2,pv3,pv41,pv43], .c 3, .c 7, .c 19, .c 3, .p pv3 [pv2,pv13,pv1831], .c 5, .c 3,
  .p pv2 [pv2,pv47609], .c 7, .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv89,pv107],
  .p pv5 [pv2,pv3,pv31],
]
private theorem h0011c19 : checkBlock 94979 128 b0011c19 = true := by
  decide +kernel

private def b0011c20 : List Row := [
  .c 3, .c 131, .p pv7 [pv2,pv3,pv11,pv13,pv37], .c 3, .c 23, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7], .c 3, .p pv2 [pv2,pv5,pv11,pv433], .c 7, .c 3,
  .p pv2 [pv2,pv19,pv23,pv109], .c 47, .c 3, .p pv3 [pv2,pv11909], .c 5, .c 3,
  .p pv7 [pv2,pv47639], .c 151, .c 3, .c 5, .p pv3 [pv2,pv3,pv15881], .c 3, .c 7, .c 11, .c 3,
  .c 233, .c 157, .c 3, .c 13, .c 5, .c 3, .c 191, .p pv3 [pv2,pv3,pv5,pv353], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv47], .c 3, .c 199, .c 19, .c 3, .p pv5 [pv2,pv7,pv11,pv619], .c 13, .c 3,
  .c 7, .c 5, .c 3, .p pv2 [pv2,pv73,pv653], .c 67, .c 3, .c 5, .c 7, .c 3, .c 97, .c 17, .c 3,
  .c 167, .c 11, .c 3, .c 47, .c 5, .c 3, .p pv3 [pv2,pv7,pv13,pv131], .c 283, .c 3, .c 5, .c 127,
  .c 3, .c 11, .p pv3 [pv2,pv3,pv7,pv757], .c 3, .c 17, .c 7, .c 3, .p pv3 [pv2,pv11,pv271], .c 5,
  .c 3, .c 19, .p pv7 [pv2,pv3,pv5,pv53], .c 3, .c 5, .c 13, .c 3, .c 73, .p pv2 [pv2,pv3,pv7951],
  .c 3, .c 7, .p pv3 [pv2,pv3,pv19,pv31], .c 3, .c 37, .c 5, .c 3, .p pv2 [pv2,pv23857], .c 7,
  .c 3, .c 5, .c 19, .c 3, .p pv3 [pv2,pv5,pv1193], .p pv3 [pv2,pv3,pv15907], .c 3, .c 11, .c 31,
  .c 3, .c 53, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv37,pv43], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv2273], .c 3, .p pv43 [pv2,pv5,pv9547], .c 7, .c 3, .c 307,
  .p pv17 [pv2,pv3,pv15913], .c 3, .p pv2 [pv2,pv47741], .c 5, .c 3, .c 17,
]
private theorem h0011c20 : checkBlock 95235 128 b0011c20 = true := by
  decide +kernel

private def b0011c21 : List Row := [
  .c 11, .c 3, .c 5, .c 29, .c 3, .c 7, .c 43, .c 3, .p pv2 [pv2,pv17,pv53], .c 149, .c 3, .c 11,
  .c 5, .c 3, .c 23, .c 59, .c 3, .c 5, .p pv3 [pv2,pv3,pv29,pv61], .c 3,
  .p pv2 [pv2,pv5,pv41,pv233], .c 83, .c 3, .c 13, .p pv3 [pv2,pv3,pv15923], .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv23887], .c 19, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv2389], .c 13, .c 3,
  .c 227, .p pv17 [pv2,pv3,pv11,pv181], .c 3, .c 31, .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv59],
  .c 3, .c 5, .c 61, .c 3, .c 17, .c 109, .c 3, .p pv2 [pv2,pv23899], .c 7, .c 3,
  .p pv5 [pv2,pv13,pv3677], .c 5, .c 3, .c 67, .c 23, .c 3, .c 5, .p pv5 [pv2,pv3,pv83], .c 3,
  .p pv3 [pv2,pv5,pv7,pv683], .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv13,pv613], .c 3,
  .p pv3 [pv2,pv43,pv139], .c 5, .c 3, .c 59, .c 7, .c 3, .c 5, .c 101, .c 3,
  .p pv2 [pv2,pv5,pv1913], .c 41, .c 3, .c 23, .c 17, .c 3, .c 271, .c 5, .c 3, .c 7, .c 29, .c 3,
  .c 5, .c 241, .c 3, .c 163, .c 7, .c 3, .c 103, .c 11, .c 3, .c 13, .c 5, .c 3, .c 83,
  .p pv2 [pv2,pv3,pv5,pv11,pv29], .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv409], .c 3, .c 7,
  .p pv5 [pv2,pv3,pv997], .c 3, .p pv2 [pv2,pv23929], .c 13, .c 3, .p pv2 [pv2,pv11,pv19,pv229],
  .c 5, .c 3, .c 29, .p pv2 [pv2,pv3,pv5,pv3191], .c 3, .c 5, .p pv5 [pv2,pv3,pv3989], .c 3,
  .c 19, .c 67, .c 3,
]
private theorem h0011c21 : checkBlock 95491 128 b0011c21 = true := by
  decide +kernel

private def b0011c22 : List Row := [
  .p pv5 [pv2,pv7,pv977], .c 23, .c 3, .c 7, .c 5, .c 3, .c 31, .c 17, .c 3, .c 5, .c 7, .c 3,
  .c 13, .p pv7 [pv2,pv3,pv23,pv347], .c 3, .c 11, .c 19, .c 3, .p pv5 [pv2,pv83,pv577], .c 5,
  .c 3, .p pv2 [pv2,pv7,pv11,pv311], .p pv3 [pv2,pv3,pv5,pv31,pv103], .c 3, .c 5, .c 13, .c 3,
  .p pv3 [pv2,pv5,pv479], .p pv3 [pv2,pv3,pv7,pv2281], .c 3, .c 149, .c 7, .c 3,
  .p pv2 [pv2,pv17,pv1409], .c 5, .c 3, .p pv2 [pv2,pv23,pv2083], .c 11, .c 3, .c 5, .c 79, .c 3,
  .c 61, .c 47, .c 3, .c 7, .c 239, .c 3, .c 11, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv1997], .c 3, .c 257, .c 17, .c 3, .c 37, .p pv17 [pv2,pv3,pv2663], .c 3,
  .p pv3 [pv2,pv7,pv107], .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv17,pv47], .c 3, .c 5, .c 11,
  .c 3, .p pv2 [pv2,pv5,pv43,pv223], .c 7, .c 3, .c 17, .c 41, .c 3, .c 29, .c 5, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv5,pv23,pv139], .c 3, .c 5, .p pv2 [pv2,pv3,pv7993], .c 3, .c 7,
  .p pv3 [pv2,pv3,pv73], .c 3, .c 13, .p pv29 [pv2,pv3,pv7,pv571], .c 3, .c 23, .c 5, .c 3,
  .c 197, .c 37, .c 3, .c 5, .p pv2 [pv2,pv3,pv15991], .c 3, .c 229, .c 11, .c 3,
  .p pv2 [pv2,pv7,pv23,pv149], .p pv3 [pv2,pv3,pv1777], .c 3, .c 7, .c 5, .c 3, .c 19,
  .p pv3 [pv2,pv3,pv5,pv7,pv457], .c 3, .c 5, .c 7, .c 3, .c 41, .c 53, .c 3,
  .p pv2 [pv2,pv11,pv4363], .p pv7 [pv2,pv3,pv19,pv421], .c 3, .c 59, .c 5, .c 3, .c 17,
  .p pv7 [pv2,pv3,pv5],
]
private theorem h0011c22 : checkBlock 95747 128 b0011c22 = true := by
  decide +kernel

private def b0011c23 : List Row := [
  .c 3, .c 5, .c 19, .c 3, .c 67, .p pv2 [pv2,pv3,pv7,pv127], .c 3, .p pv3 [pv2,pv17,pv353], .c 7,
  .c 3, .c 131, .c 5, .c 3, .c 109, .c 13, .c 3, .c 5, .c 137, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv16007], .c 3, .c 7, .c 139, .c 3, .p pv2 [pv2,pv11,pv37,pv59], .c 5, .c 3,
  .p pv2 [pv2,pv48029], .c 7, .c 3, .c 5, .c 17, .c 3, .c 23, .c 191, .c 3, .c 29,
  .p pv3 [pv2,pv3,pv67,pv239], .c 3, .c 13, .c 5, .c 3, .c 7, .c 307, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv11,pv13], .c 3, .c 17, .c 7, .c 3, .c 11, .c 13, .c 3, .c 223, .c 5, .c 3,
  .c 277, .c 19, .c 3, .c 5, .c 97, .c 3, .c 7, .c 251, .c 3, .p pv3 [pv2,pv61,pv197], .c 127,
  .c 3, .c 79, .c 5, .c 3, .p pv2 [pv2,pv13,pv43], .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv2671],
  .c 3, .c 13, .c 23, .c 3, .p pv5 [pv2,pv7,pv6869], .c 17, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv19,pv2531], .p pv11 [pv2,pv3,pv5,pv7,pv229], .c 3, .c 5, .c 7, .c 3, .c 43, .c 29,
  .c 3, .c 19, .p pv3 [pv2,pv3,pv16033], .c 3, .c 17, .c 5, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv5,pv1069], .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv17,pv283],
  .p pv5 [pv2,pv3,pv7,pv29,pv79], .c 3, .c 41, .c 7, .c 3, .p pv3 [pv2,pv23,pv523], .c 5, .c 3,
  .c 11, .c 157, .c 3, .c 5, .c 109, .c 3, .c 29, .c 101, .c 3, .c 7,
]
private theorem h0011c23 : checkBlock 96003 128 b0011c23 = true := by
  decide +kernel

private def b0011c24 : List Row := [
  .p pv2 [pv2,pv3,pv61,pv263], .c 3, .p pv5 [pv2,pv48131], .c 5, .c 3, .p pv2 [pv2,pv41,pv587],
  .c 7, .c 3, .c 5, .c 43, .c 3, .p pv3 [pv2,pv5,pv29,pv83], .c 11, .c 3, .c 73,
  .p pv11 [pv2,pv3,pv17,pv59], .c 3, .p pv2 [pv2,pv7,pv19,pv181], .c 5, .c 3, .c 7, .c 23, .c 3,
  .c 5, .c 193, .c 3, .c 19, .c 7, .c 3, .c 13, .c 61, .c 3, .p pv2 [pv2,pv17,pv2833], .c 5, .c 3,
  .p pv3 [pv2,pv12041], .p pv11 [pv2,pv3,pv5,pv13,pv19], .c 3, .c 5, .p pv5 [pv2,pv3,pv223], .c 3,
  .c 7, .c 13, .c 3, .c 23, .c 11, .c 3, .p pv3 [pv2,pv3011], .c 5, .c 3, .c 167, .c 173, .c 3,
  .c 5, .c 29, .c 3, .c 11, .c 17, .c 3, .p pv3 [pv2,pv7,pv1721], .c 31, .c 3, .c 7, .c 5, .c 3,
  .c 113, .c 41, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv241], .c 149, .c 3, .c 17, .c 229,
  .c 3, .c 67, .c 5, .c 3, .p pv7 [pv2,pv7,pv71,pv97], .c 13, .c 3, .c 5, .c 211, .c 3,
  .p pv11 [pv2,pv5,pv9643], .c 73, .c 3, .c 11, .c 7, .c 3, .p pv2 [pv2,pv48221], .c 5, .c 3,
  .c 43, .p pv2 [pv2,pv3,pv5,pv643], .c 3, .c 5, .p pv5 [pv2,pv3,pv4019], .c 3,
  .p pv2 [pv2,pv5,pv7,pv13,pv53], .c 19, .c 3, .c 7, .p pv11 [pv2,pv3,pv8039], .c 3, .c 13, .c 5,
  .c 3, .p pv11 [pv2,pv48239], .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv1237], .c 3, .c 47,
  .p pv5 [pv2,pv3,pv11,pv17,pv43], .c 3, .p pv3 [pv2,pv37,pv163], .c 13, .c 3, .c 11, .c 5, .c 3,
  .c 7, .c 103, .c 3,
]
private theorem h0011c24 : checkBlock 96259 128 b0011c24 = true := by
  decide +kernel

private def b0011c25 : List Row := [
  .c 5, .p pv2 [pv2,pv3,pv7,pv383], .c 3, .c 263, .c 7, .c 3, .p pv5 [pv2,pv17,pv167], .c 83,
  .c 3, .c 37, .c 5, .c 3, .c 19, .c 29, .c 3, .c 5, .c 11, .c 3, .c 7, .p pv5 [pv2,pv3,pv149],
  .c 3, .p pv2 [pv2,pv101,pv239], .c 223, .c 3, .c 61, .c 5, .c 3, .c 11, .c 269, .c 3, .c 5,
  .c 13, .c 3, .p pv2 [pv2,pv5,pv11,pv439], .c 59, .c 3, .p pv2 [pv2,pv7,pv6899],
  .p pv7 [pv2,pv3,pv2683], .c 3, .c 7, .c 5, .c 3, .c 29, .p pv11 [pv2,pv3,pv5,pv7,pv23], .c 3,
  .c 5, .c 7, .c 3, .c 17, .c 11, .c 3, .c 79, .c 53, .c 3, .c 23, .c 5, .c 3, .c 13, .c 71, .c 3,
  .c 5, .c 41, .c 3, .c 241, .p pv2 [pv2,pv3,pv7,pv13,pv59], .c 3, .c 127, .c 7, .c 3, .c 19,
  .c 5, .c 3, .c 163, .p pv7 [pv2,pv3,pv5,pv179], .c 3, .c 5, .p pv2 [pv2,pv3,pv16111], .c 3,
  .p pv7 [pv2,pv5,pv7,pv1381], .c 277, .c 3, .c 7, .c 11, .c 3, .c 109, .c 5, .c 3, .c 31, .c 7,
  .c 3, .c 5, .p pv7 [pv2,pv3,pv17,pv79], .c 3, .c 11, .p pv3 [pv2,pv3,pv71,pv227], .c 3, .c 13,
  .c 97, .c 3, .c 17, .c 5, .c 3, .c 7, .c 311, .c 3, .c 5, .c 197, .c 3,
  .p pv2 [pv2,pv5,pv17,pv569], .c 7, .c 3, .p pv3 [pv2,pv3023], .p pv2 [pv2,pv3,pv23,pv701], .c 3,
  .c 89, .c 5, .c 3, .p pv2 [pv2,pv19,pv67], .c 31, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv733], .c 3,
  .c 7, .p pv5 [pv2,pv3,pv16127], .c 3, .c 11, .p pv37 [pv2,pv3,pv7],
]
private theorem h0011c25 : checkBlock 96515 128 b0011c25 = true := by
  decide +kernel

private def b0011c26 : List Row := [
  .c 3, .c 29, .c 5, .c 3, .p pv2 [pv2,pv11,pv53,pv83], .c 17, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv19,pv283], .c 3, .c 151, .c 43, .c 3, .p pv2 [pv2,pv7,pv3457],
  .p pv29 [pv2,pv3,pv13,pv17,pv73], .c 3, .c 7, .c 5, .c 3, .c 131, .c 11, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv47,pv103], .p pv5 [pv2,pv3,pv11,pv163], .c 3, .p pv2 [pv2,pv48413], .c 37,
  .c 3, .c 11, .c 5, .c 3, .c 179, .c 113, .c 3, .c 5, .p pv3 [pv2,pv3,pv16141], .c 3,
  .p pv2 [pv2,pv5,pv13,pv149], .c 23, .c 3, .p pv3 [pv2,pv12107], .c 7, .c 3, .c 13, .c 5, .c 3,
  .c 157, .c 73, .c 3, .c 5, .c 11, .c 3, .c 19, .c 17, .c 3, .c 7, .c 13, .c 3,
  .p pv2 [pv2,pv24223], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv31,pv521], .c 3,
  .p pv11 [pv2,pv5,pv11,pv881], .c 199, .c 3, .c 17, .c 19, .c 3, .c 103, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv359], .c 3, .c 5, .c 31, .c 3, .c 13, .c 7, .c 3, .c 29, .c 67, .c 3,
  .p pv3 [pv2,pv12119], .c 5, .c 3, .p pv7 [pv2,pv48479], .c 47, .c 3, .c 5, .c 13, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv8081], .c 3, .c 37, .p pv3 [pv2,pv3,pv7,pv2309], .c 3, .c 293, .c 5, .c 3,
  .p pv2 [pv2,pv24247], .c 23, .c 3, .c 5, .p pv2 [pv2,pv3,pv59,pv137], .c 3,
  .p pv3 [pv2,pv5,pv97], .p pv7 [pv2,pv3,pv17,pv317], .c 3, .p pv5 [pv2,pv7,pv13,pv41], .c 11,
  .c 3, .c 7, .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv7,pv11], .c 3, .c 5,
]
private theorem h0011c26 : checkBlock 96771 128 b0011c26 = true := by
  decide +kernel

private def b0011c27 : List Row := [
  .c 7, .c 3, .c 11, .c 19, .c 3, .c 23, .p pv3 [pv2,pv3,pv599], .c 3, .c 53, .c 5, .c 3, .c 107,
  .c 37, .c 3, .c 5, .c 71, .c 3, .c 31, .c 29, .c 3, .c 113, .c 7, .c 3, .p pv3 [pv2,pv6067],
  .c 5, .c 3, .c 193, .p pv7 [pv2,pv3,pv5,pv809], .c 3, .c 5, .c 17, .c 3, .c 79, .c 151, .c 3,
  .c 7, .c 89, .c 3, .p pv5 [pv2,pv47,pv1033], .c 5, .c 3, .c 19, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv8093], .c 3, .c 17, .c 13, .c 3, .p pv5 [pv2,pv48563], .c 23, .c 3, .c 137,
  .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 19, .c 3, .p pv13 [pv2,pv5,pv29,pv67], .c 7, .c 3,
  .p pv2 [pv2,pv107,pv227], .p pv3 [pv2,pv3,pv16193], .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv6073], .p pv19 [pv2,pv3,pv5,pv41,pv79], .c 3, .c 5, .p pv5 [pv2,pv3,pv4049], .c 3,
  .c 7, .c 157, .c 3, .p pv2 [pv2,pv48593], .c 17, .c 3, .c 83, .c 5, .c 3, .c 37, .c 13, .c 3,
  .c 5, .c 11, .c 3, .c 41, .p pv5 [pv2,pv3,pv8101], .c 3, .c 67, .c 191, .c 3, .c 7, .c 5, .c 3,
  .c 11, .p pv7 [pv2,pv3,pv5,pv7,pv463], .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv11,pv13,pv17],
  .c 47, .c 3, .c 31, .c 79, .c 3, .c 13, .c 5, .c 3, .p pv7 [pv2,pv7,pv6947], .c 19, .c 3, .c 5,
  .c 23, .c 3, .c 211, .c 11, .c 3, .c 89, .c 7, .c 3,
]
private theorem h0011c27 : checkBlock 97027 128 b0011c27 = true := by
  decide +kernel

private def b0011c28 : List Row := [
  .p pv2 [pv2,pv127,pv383], .c 5, .c 3, .c 271, .c 17, .c 3, .c 5, .c 149, .c 3,
  .p pv2 [pv2,pv5,pv7,pv139], .p pv3 [pv2,pv3,pv16217], .c 3, .c 7, .c 31, .c 3, .c 23, .c 5,
  .c 3, .c 307, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv5407], .c 3, .c 13, .c 131, .c 3, .c 19,
  .c 11, .c 3, .c 311, .c 5, .c 3, .c 7, .c 67, .c 3, .c 5, .c 13, .c 3, .c 11, .c 7, .c 3,
  .p pv5 [pv2,pv89,pv547], .p pv7 [pv2,pv3,pv4057], .c 3, .p pv2 [pv2,pv11,pv2213], .c 5, .c 3,
  .p pv2 [pv2,pv181,pv269], .p pv2 [pv2,pv3,pv5,pv541], .c 3, .c 5, .p pv2 [pv2,pv3,pv16231],
  .c 3, .c 7, .c 17, .c 3, .p pv2 [pv2,pv13,pv1873], .c 173, .c 3, .c 257, .c 5, .c 3, .c 13,
  .c 29, .c 3, .c 5, .c 61, .c 3, .c 37, .p pv3 [pv2,pv3,pv13,pv1249], .c 3, .c 11,
  .p pv7 [pv2,pv3,pv23,pv353], .c 3, .c 7, .c 5, .c 3, .c 139, .p pv37 [pv2,pv3,pv5,pv7,pv29],
  .c 3, .c 5, .c 7, .c 3, .c 19, .p pv2 [pv2,pv3,pv2707], .c 3, .c 41,
  .p pv2 [pv2,pv3,pv37,pv439], .c 3, .p pv5 [pv2,pv48731], .c 5, .c 3, .c 29, .c 11, .c 3, .c 5,
  .c 107, .c 3, .c 43, .c 71, .c 3, .c 13, .c 7, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv29,pv41],
  .p pv7 [pv2,pv3,pv5,pv13], .c 3, .c 5, .c 281, .c 3, .p pv7 [pv2,pv5,pv7,pv199], .c 13, .c 3,
  .c 7, .c 113, .c 3, .p pv2 [pv2,pv48761], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 11,
]
private theorem h0011c28 : checkBlock 97283 128 b0011c28 = true := by
  decide +kernel

private def b0011c29 : List Row := [
  .c 3, .c 103, .c 23, .c 3, .p pv2 [pv2,pv17,pv19,pv151], .p pv2 [pv2,pv3,pv11,pv739], .c 3,
  .p pv3 [pv2,pv7,pv13,pv67], .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv271], .c 3, .c 5, .c 43,
  .c 3, .p pv2 [pv2,pv5,pv11,pv887], .c 7, .c 3, .p pv3 [pv2,pv12197],
  .p pv2 [pv2,pv3,pv13,pv139], .c 3, .p pv5 [pv2,pv97,pv503], .c 5, .c 3, .c 23, .c 13, .c 3,
  .c 5, .c 17, .c 3, .c 7, .c 11, .c 3, .p pv5 [pv2,pv37,pv1319], .p pv17 [pv2,pv3,pv7,pv83],
  .c 3, .p pv2 [pv2,pv23,pv1061], .c 5, .c 3, .c 31, .c 41, .c 3, .c 5, .c 233, .c 3, .c 17,
  .c 89, .c 3, .c 163, .c 251, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv17,pv359],
  .p pv2 [pv2,pv3,pv5,pv7,pv31], .c 3, .c 5, .c 7, .c 3, .c 61, .c 127, .c 3, .c 101, .c 11, .c 3,
  .p pv3 [pv2,pv29,pv421], .c 5, .c 3, .c 19, .c 23, .c 3, .c 5, .p pv5 [pv2,pv3,pv67], .c 3,
  .c 11, .c 211, .c 3, .c 151, .c 7, .c 3, .c 41, .c 5, .c 3, .c 199,
  .p pv11 [pv2,pv3,pv5,pv3257], .c 3, .c 5, .c 19, .c 3, .c 13, .c 79, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv509], .c 3, .c 17, .c 5, .c 3, .c 43, .c 7, .c 3, .c 5, .c 13, .c 3, .c 239,
  .c 67, .c 3, .c 11, .c 29, .c 3, .c 59, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv3259], .c 3,
  .c 5, .p pv17 [pv2,pv3,pv7,pv97], .c 3, .c 277, .c 7, .c 3, .p pv2 [pv2,pv13,pv3761],
  .p pv2 [pv2,pv3,pv29,pv281], .c 3, .c 19,
]
private theorem h0011c29 : checkBlock 97539 128 b0011c29 = true := by
  decide +kernel

private def b0011c30 : List Row := [
  .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 47, .c 3, .c 7, .p pv2 [pv2,pv3,pv11,pv13,pv19], .c 3,
  .c 29, .c 23, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv37,pv661], .c 19, .c 3, .c 5, .c 227, .c 3,
  .p pv11 [pv2,pv5,pv1223], .p pv2 [pv2,pv3,pv23,pv709], .c 3, .p pv5 [pv2,pv7,pv29,pv241],
  .p pv13 [pv2,pv3,pv151], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv113,pv433],
  .p pv2 [pv2,pv3,pv5,pv7,pv233], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv9787], .c 97, .c 3,
  .c 13, .p pv11 [pv2,pv3,pv11,pv1483], .c 3, .p pv2 [pv2,pv109,pv449], .c 5, .c 3, .c 11, .c 53,
  .c 3, .c 5, .c 223, .c 3, .c 47, .c 13, .c 3, .c 19, .c 7, .c 3, .c 179, .c 5, .c 3,
  .p pv23 [pv2,pv173,pv283], .c 181, .c 3, .c 5, .p pv3 [pv2,pv3,pv19,pv859], .c 3,
  .p pv2 [pv2,pv5,pv7,pv1399], .c 11, .c 3, .c 7, .c 37, .c 3, .p pv5 [pv2,pv13,pv3767], .c 5,
  .c 3, .c 41, .c 7, .c 3, .c 5, .c 23, .c 3, .p pv3 [pv2,pv5,pv31,pv79], .c 163, .c 3,
  .p pv5 [pv2,pv11,pv61,pv73], .c 313, .c 3, .p pv2 [pv2,pv7,pv3499], .c 5, .c 3, .c 7, .c 13,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv2333], .c 3, .c 29, .c 7, .c 3, .c 43, .c 11, .c 3, .c 23,
  .c 5, .c 3, .p pv3 [pv2,pv12251], .p pv43 [pv2,pv3,pv5,pv11], .c 3, .c 5,
  .p pv7 [pv2,pv3,pv1021], .c 3, .c 7, .c 83, .c 3, .c 61, .c 167, .c 3, .c 13, .c 5, .c 3, .c 17,
  .p pv13 [pv2,pv3,pv5,pv19,pv43], .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv419], .c 3,
]
private theorem h0011c30 : checkBlock 97795 128 b0011c30 = true := by
  decide +kernel

private def b0011c31 : List Row := [
  .c 71, .c 31, .c 3, .p pv3 [pv2,pv7,pv17,pv103], .c 13, .c 3, .c 7, .c 5, .c 3, .c 281, .c 101,
  .c 3, .c 5, .c 7, .c 3, .p pv19 [pv2,pv5,pv613], .c 43, .c 3, .c 11, .c 47, .c 3, .c 233, .c 5,
  .c 3, .c 263, .p pv2 [pv2,pv3,pv5,pv109], .c 3, .c 5, .c 17, .c 3, .c 13, .c 41, .c 3, .c 59,
  .c 7, .c 3, .p pv2 [pv2,pv71,pv691], .c 5, .c 3, .p pv3 [pv2,pv6133], .c 11, .c 3, .c 5, .c 13,
  .c 3, .c 17, .p pv5 [pv2,pv3,pv11,pv1487], .c 3, .c 7, .c 61, .c 3, .c 11, .c 5, .c 3, .c 103,
  .c 7, .c 3, .c 5, .c 89, .c 3, .c 127, .c 19, .c 3, .c 31, .p pv2 [pv2,pv3,pv16363], .c 3,
  .c 47, .c 5, .c 3, .c 7, .c 149, .c 3, .c 5, .c 11, .c 3, .c 283, .c 7, .c 3,
  .p pv5 [pv2,pv49103], .c 17, .c 3, .p pv2 [pv2,pv43,pv571], .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv1637], .c 3, .c 5, .p pv3 [pv2,pv3,pv17,pv107], .c 3, .c 7, .c 23, .c 3,
  .c 193, .c 31, .c 3, .c 17, .c 5, .c 3, .c 19, .p pv2 [pv2,pv3,pv5,pv131], .c 3, .c 5,
  .p pv17 [pv2,pv3,pv23,pv89], .c 3, .c 97, .c 11, .c 3, .c 13, .p pv2 [pv2,pv3,pv19,pv431], .c 3,
  .c 7, .c 5, .c 3, .c 23, .c 29, .c 3, .c 5, .c 7, .c 3, .c 227, .c 13, .c 3,
  .p pv3 [pv2,pv11,pv1117], .p pv2 [pv2,pv3,pv43,pv127], .c 3, .c 197, .c 5,
]
private theorem h0011c31 : checkBlock 98051 128 b0011c31 = true := by
  decide +kernel

def rows0011 : List Row :=
  b0011c00 ++ b0011c01 ++ b0011c02 ++ b0011c03 ++ b0011c04 ++ b0011c05 ++ b0011c06 ++ b0011c07 ++
  b0011c08 ++ b0011c09 ++ b0011c10 ++ b0011c11 ++ b0011c12 ++ b0011c13 ++ b0011c14 ++ b0011c15 ++
  b0011c16 ++ b0011c17 ++ b0011c18 ++ b0011c19 ++ b0011c20 ++ b0011c21 ++ b0011c22 ++ b0011c23 ++
  b0011c24 ++ b0011c25 ++ b0011c26 ++ b0011c27 ++ b0011c28 ++ b0011c29 ++ b0011c30 ++ b0011c31

theorem checked0011 : checkBlock 90115 4096 rows0011 = true :=
  checkBlock_append h0011c00 (
    checkBlock_append h0011c01 (
    checkBlock_append h0011c02 (
    checkBlock_append h0011c03 (
    checkBlock_append h0011c04 (
    checkBlock_append h0011c05 (
    checkBlock_append h0011c06 (
    checkBlock_append h0011c07 (
    checkBlock_append h0011c08 (
    checkBlock_append h0011c09 (
    checkBlock_append h0011c10 (
    checkBlock_append h0011c11 (
    checkBlock_append h0011c12 (
    checkBlock_append h0011c13 (
    checkBlock_append h0011c14 (
    checkBlock_append h0011c15 (
    checkBlock_append h0011c16 (
    checkBlock_append h0011c17 (
    checkBlock_append h0011c18 (
    checkBlock_append h0011c19 (
    checkBlock_append h0011c20 (
    checkBlock_append h0011c21 (
    checkBlock_append h0011c22 (
    checkBlock_append h0011c23 (
    checkBlock_append h0011c24 (
    checkBlock_append h0011c25 (
    checkBlock_append h0011c26 (
    checkBlock_append h0011c27 (
    checkBlock_append h0011c28 (
    checkBlock_append h0011c29 (
    checkBlock_append h0011c30 (
    h0011c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
