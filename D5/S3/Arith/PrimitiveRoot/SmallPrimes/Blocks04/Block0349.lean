/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks04/Block0349
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks04/Block0349.checked0349
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table148

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0349c00 : List Row := [
  .c 421, .c 113, .c 3, .c 7, .p pv2 [pv2,pv3,pv83,pv5741], .c 3, .c 29, .c 5, .c 3,
  .p pv2 [pv2,pv71,pv10067], .c 7, .c 3, .c 5, .c 31, .c 3, .c 1213, .c 11, .c 3,
  .p pv5 [pv2,pv1429523], .p pv11 [pv2,pv3,pv39709], .c 3, .c 41, .c 5, .c 3, .c 7, .c 23, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv7,pv22691], .c 3, .p pv13 [pv2,pv5,pv43,pv61,pv109], .c 7, .c 3, .c 13,
  .c 191, .c 3, .c 223, .c 5, .c 3, .c 79, .c 67, .c 3, .c 5, .p pv7 [pv2,pv3,pv119129], .c 3,
  .c 7, .c 13, .c 3, .c 23, .c 11, .c 3, .c 43, .c 5, .c 3, .c 863,
  .p pv7 [pv2,pv3,pv5,pv11,pv19], .c 3, .c 5, .c 157, .c 3, .c 11, .p pv5 [pv2,pv3,pv238261],
  .c 3, .p pv3 [pv2,pv7,pv3191], .c 19, .c 3, .c 7, .c 5, .c 3, .c 283, .c 47, .c 3, .c 5, .c 7,
  .c 3, .c 31, .p pv2 [pv2,pv3,pv17,pv28031], .c 3, .c 179, .c 547, .c 3,
  .p pv2 [pv2,pv97,pv7369], .c 5, .c 3, .c 17, .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv43321],
  .c 3, .c 53, .c 1609, .c 3, .c 11, .c 7, .c 3, .c 1277, .c 5, .c 3, .c 101,
  .p pv2 [pv2,pv3,pv5,pv31769], .c 3, .c 5, .c 41, .c 3, .c 829, .c 31, .c 3, .c 7,
  .p pv19 [pv2,pv3,pv79423], .c 3, .c 13, .c 5, .c 3, .c 113, .c 7, .c 3, .c 5, .c 17, .c 3,
  .p pv2 [pv2,pv5,pv11437], .c 19, .c 3, .c 181, .c 13, .c 3, .c 11, .c 5,
]
private theorem h0349c00 : checkBlock 2859011 128 b0349c00 = true := by
  decide +kernel

private def b0349c01 : List Row := [
  .c 3, .c 7, .p pv37 [pv2,pv3,pv5,pv191,pv499], .c 3, .c 5, .c 587, .c 3, .c 17, .c 7, .c 3,
  .p pv5 [pv2,pv37,pv38639], .p pv23 [pv2,pv3,pv109,pv1093], .c 3, .c 1439, .c 5, .c 3, .c 41,
  .p pv2 [pv2,pv3,pv5,pv353], .c 3, .c 5, .c 11, .c 3, .c 7, .c 29, .c 3, .c 59, .c 409, .c 3,
  .c 37, .c 5, .c 3, .c 11, .p pv29 [pv2,pv3,pv5,pv95311], .c 3, .c 5, .c 13, .c 3,
  .p pv19 [pv2,pv5,pv11,pv41,pv317], .p pv3 [pv2,pv3,pv29,pv16433], .c 3, .c 31, .c 17, .c 3,
  .c 7, .c 5, .c 3, .c 67, .c 107, .c 3, .c 5, .c 7, .c 3, .c 29, .c 11, .c 3,
  .p pv5 [pv2,pv13,pv59,pv233], .c 701, .c 3, .c 17, .c 5, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv5,pv31771], .c 3, .c 5, .c 37, .c 3, .c 659, .c 53, .c 3,
  .p pv5 [pv2,pv11,pv23,pv5651], .c 7, .c 3, .p pv2 [pv2,pv714853], .c 5, .c 3, .c 967, .c 643,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv67,pv2371], .c 3, .c 199, .c 47, .c 3, .c 7, .c 11, .c 3, .c 19,
  .c 5, .c 3, .c 457, .c 7, .c 3, .c 5, .c 43, .c 3, .c 11, .c 41, .c 3, .c 13,
  .p pv11 [pv2,pv3,pv17,pv107,pv131], .c 3, .p pv5 [pv2,pv7,pv11,pv211], .c 5, .c 3, .c 7, .c 19,
  .c 3, .c 5, .c 29, .c 3, .p pv2 [pv2,pv5,pv285949], .c 7, .c 3, .c 61,
  .p pv2 [pv2,pv3,pv23,pv6907], .c 3, .p pv5 [pv2,pv17,pv31,pv2713], .c 5, .c 3, .c 53, .c 1091,
  .c 3, .c 5, .c 173, .c 3, .c 7,
]
private theorem h0349c01 : checkBlock 2859267 128 b0349c01 = true := by
  decide +kernel

private def b0349c02 : List Row := [
  .c 229, .c 3, .c 11, .c 223, .c 3, .c 31, .c 5, .c 3, .c 389, .c 167, .c 3, .c 5, .c 983, .c 3,
  .p pv7 [pv2,pv5,pv57191], .c 17, .c 3, .c 19, .p pv3 [pv2,pv3,pv13,pv61,pv601], .c 3, .c 7,
  .c 5, .c 3, .c 1579, .c 11, .c 3, .c 5, .c 7, .c 3, .c 1201, .c 461, .c 3, .c 17, .c 103, .c 3,
  .c 11, .c 5, .c 3, .c 83, .c 137, .c 3, .c 5, .p pv5 [pv2,pv3,pv158867], .c 3, .c 859, .c 23,
  .c 3, .p pv3 [pv2,pv89363], .c 7, .c 3, .c 13, .c 5, .c 3, .c 43,
  .p pv3 [pv2,pv3,pv5,pv199,pv479], .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv7,pv1459], .c 251,
  .c 3, .c 7, .c 13, .c 3, .c 353, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 71, .c 3, .c 19,
  .p pv13 [pv2,pv3,pv17,pv43,pv163], .c 3, .p pv2 [pv2,pv714919], .c 977, .c 3, .c 211, .c 5,
  .c 3, .c 7, .c 113, .c 3, .c 5, .p pv23 [pv2,pv3,pv7,pv2837], .c 3, .c 13, .c 7, .c 3,
  .p pv2 [pv2,pv17,pv241,pv349], .c 19, .c 3, .p pv3 [pv2,pv44683], .c 5, .c 3, .c 29, .c 53,
  .c 3, .c 5, .c 13, .c 3, .c 7, .p pv5 [pv2,pv3,pv26479], .c 3, .c 281, .c 269, .c 3,
  .p pv5 [pv2,pv1429871], .c 5, .c 3, .p pv2 [pv2,pv29,pv89,pv277], .c 23, .c 3, .c 5, .c 17,
  .c 3, .c 67, .p pv3 [pv2,pv3,pv47,pv10141], .c 3, .c 37, .c 11, .c 3, .c 7, .c 5, .c 3,
]
private theorem h0349c02 : checkBlock 2859523 128 b0349c02 = true := by
  decide +kernel

private def b0349c03 : List Row := [
  .c 13, .c 31, .c 3, .c 5, .c 7, .c 3, .c 11, .p pv11 [pv2,pv3,pv13,pv4583], .c 3, .c 23,
  .p pv3 [pv2,pv3,pv476633], .c 3, .p pv2 [pv2,pv11,pv61,pv2131], .c 5, .c 3, .c 47, .c 1481,
  .c 3, .c 5, .c 1163, .c 3, .c 1021, .c 19, .c 3, .c 53, .c 7, .c 3, .c 109, .c 5, .c 3, .c 1637,
  .c 37, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv43331], .c 3, .c 97, .c 421, .c 3, .c 7, .c 17, .c 3,
  .c 61, .c 5, .c 3, .p pv2 [pv2,pv11,pv64997], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv4673],
  .c 3, .c 313, .c 13, .c 3, .c 43, .c 23, .c 3, .c 17, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .c 59, .c 3, .c 769, .c 7, .c 3, .c 113, .p pv3 [pv2,pv3,pv19,pv25087], .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv389,pv919], .c 83, .c 3, .c 5, .c 19, .c 3, .c 7, .p pv3 [pv2,pv3,pv109,pv4373],
  .c 3, .c 241, .p pv2 [pv2,pv3,pv7,pv13,pv97], .c 3, .c 953, .c 5, .c 3, .c 1373, .c 13, .c 3,
  .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv285997], .c 43, .c 3, .p pv3 [pv2,pv7,pv51071],
  .p pv2 [pv2,pv3,pv11,pv17,pv2549], .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv5,pv7,pv13619], .c 3, .c 5, .c 7, .c 3, .c 103, .c 107, .c 3,
  .p pv5 [pv2,pv353,pv4051], .c 29, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv7,pv281,pv727],
  .p pv2 [pv2,pv3,pv5,pv15889], .c 3, .c 5, .c 23, .c 3, .c 367, .c 11,
]
private theorem h0349c03 : checkBlock 2859779 128 b0349c03 = true := by
  decide +kernel

private def b0349c04 : List Row := [
  .c 3, .c 41, .c 7, .c 3, .p pv2 [pv2,pv167,pv8563], .c 5, .c 3, .c 691, .c 19, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13241], .c 3, .p pv2 [pv2,pv5,pv7,pv31,pv659], .c 17, .c 3, .c 7, .c 157,
  .c 3, .c 23, .c 5, .c 3, .c 1103, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv476681], .c 3, .c 13,
  .c 71, .c 3, .c 17, .c 11, .c 3, .p pv7 [pv2,pv7,pv43,pv4751], .c 5, .c 3, .c 7, .c 1109, .c 3,
  .c 5, .c 13, .c 3, .c 11, .c 7, .c 3, .c 19, .p pv7 [pv2,pv3,pv9931], .c 3,
  .p pv3 [pv2,pv11,pv65003], .c 5, .c 3, .c 571, .p pv17 [pv2,pv3,pv5,pv73,pv653], .c 3, .c 5,
  .c 661, .c 3, .c 7, .c 31, .c 3, .p pv2 [pv2,pv13,pv4231], .c 601, .c 3, .c 67, .c 5, .c 3,
  .c 13, .c 331, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv5417], .c 3, .p pv2 [pv2,pv5,pv83,pv1723],
  .c 29, .c 3, .c 11, .c 577, .c 3, .c 7, .c 5, .c 3, .c 17, .c 41, .c 3, .c 5, .c 7, .c 3, .c 23,
  .c 73, .c 3, .c 107, .c 101, .c 3, .p pv5 [pv2,pv19,pv75269], .c 5, .c 3, .c 61, .c 11, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv79451], .c 3, .c 19, .c 197, .c 3, .c 13, .c 7, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv613,pv2333], .c 59, .c 3, .c 5, .c 17, .c 3, .p pv7 [pv2,pv5,pv7,pv29,pv1409],
  .c 13, .c 3, .c 7, .c 19, .c 3, .c 41, .c 5, .c 3, .p pv3 [pv2,pv11173],
]
private theorem h0349c04 : checkBlock 2860035 128 b0349c04 = true := by
  decide +kernel

private def b0349c05 : List Row := [
  .c 7, .c 3, .c 5, .c 11, .c 3, .c 17, .c 23, .c 3, .p pv2 [pv2,pv71,pv20143],
  .p pv2 [pv2,pv3,pv11,pv31,pv233], .c 3, .c 379, .c 5, .c 3, .c 7, .c 347, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv23,pv47], .c 3, .p pv11 [pv2,pv5,pv11,pv26003], .c 7, .c 3,
  .p pv3 [pv2,pv19,pv97], .c 31, .c 3, .c 181, .c 5, .c 3, .c 23, .c 13, .c 3, .c 5, .c 29, .c 3,
  .c 7, .c 11, .c 3, .c 1039, .c 17, .c 3, .c 47, .c 5, .c 3, .c 59, .c 1093, .c 3, .c 5, .c 647,
  .c 3, .c 929, .c 19, .c 3, .c 811, .c 619, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv357551],
  .p pv3 [pv2,pv3,pv5,pv7,pv53,pv257], .c 3, .c 5, .c 7, .c 3, .c 101, .c 137, .c 3, .c 227,
  .c 11, .c 3, .c 37, .c 5, .c 3, .c 229, .c 23, .c 3, .c 5, .c 41, .c 3, .c 11, .c 193, .c 3,
  .p pv3 [pv2,pv337,pv1061], .c 7, .c 3, .c 31, .c 5, .c 3, .c 19, .c 17, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv238373], .c 3, .c 13, .p pv2 [pv2,pv3,pv113,pv4219], .c 3, .c 7, .c 43, .c 3,
  .p pv2 [pv2,pv715123], .c 5, .c 3, .p pv2 [pv2,pv67,pv21347], .c 7, .c 3, .c 5, .c 13, .c 3,
  .c 79, .c 419, .c 3, .c 11, .c 71, .c 3, .p pv5 [pv2,pv7,pv17,pv101], .c 5, .c 3, .c 7, .c 29,
  .c 3, .c 5, .c 373, .c 3, .c 233, .c 7, .c 3,
]
private theorem h0349c05 : checkBlock 2860291 128 b0349c05 = true := by
  decide +kernel

private def b0349c06 : List Row := [
  .c 431, .c 89, .c 3, .p pv3 [pv2,pv357569], .c 5, .c 3, .c 13, .c 11, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv491,pv971], .c 3, .c 7, .c 17, .c 3, .p pv3 [pv2,pv89393], .c 23, .c 3, .c 11,
  .c 5, .c 3, .c 29, .c 239, .c 3, .c 5, .c 1223, .c 3, .p pv3 [pv2,pv5,pv14303], .c 563, .c 3,
  .c 17, .p pv7 [pv2,pv3,pv47,pv317], .c 3, .c 7, .c 5, .c 3, .c 103, .c 19, .c 3, .c 5, .c 7,
  .c 3, .p pv7 [pv2,pv5,pv286063], .p pv11 [pv2,pv3,pv67,pv593], .c 3, .c 13,
  .p pv13 [pv2,pv3,pv11,pv89,pv487], .c 3, .p pv2 [pv2,pv1430321], .c 5, .c 3, .c 11, .c 73, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv61,pv977], .c 3, .c 43, .c 13, .c 3, .c 257, .c 7, .c 3,
  .p pv3 [pv2,pv22349], .c 5, .c 3, .p pv19 [pv2,pv19,pv83,pv907],
  .p pv7 [pv2,pv3,pv5,pv31,pv769], .c 3, .c 5, .p pv5 [pv2,pv3,pv158927], .c 3,
  .p pv2 [pv2,pv5,pv7,pv40867], .c 11, .c 3, .c 7, .c 67, .c 3, .c 757, .c 5, .c 3, .c 17, .c 7,
  .c 3, .c 5, .c 23, .c 3, .p pv7 [pv2,pv5,pv35759], .p pv2 [pv2,pv3,pv103,pv1543], .c 3, .c 89,
  .c 37, .c 3, .c 59, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 43, .c 3, .p pv11 [pv2,pv5,pv11443],
  .c 7, .c 3, .p pv2 [pv2,pv715189], .c 11, .c 3, .c 23, .c 5, .c 3, .p pv3 [pv2,pv89399],
  .p pv2 [pv2,pv3,pv5,pv11,pv8669], .c 3, .c 5, .c 17, .c 3, .c 7, .c 641, .c 3,
  .p pv2 [pv2,pv23,pv62191], .p pv11 [pv2,pv3,pv7,pv34057], .c 3, .c 13, .c 5, .c 3,
  .p pv7 [pv2,pv191,pv7489], .p pv13 [pv2,pv3,pv5,pv149],
]
private theorem h0349c06 : checkBlock 2860547 128 b0349c06 = true := by
  decide +kernel

private def b0349c07 : List Row := [
  .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv36677], .c 3, .c 17, .c 163, .c 3,
  .p pv3 [pv2,pv7,pv41,pv89], .c 13, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv17,pv42071], .c 433,
  .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv37,pv1933], .c 47, .c 3, .c 11, .c 19, .c 3,
  .p pv2 [pv2,pv293,pv2441], .c 5, .c 3, .c 107, .c 281, .c 3, .c 5, .c 223, .c 3, .c 13, .c 773,
  .c 3, .c 37, .c 7, .c 3, .p pv2 [pv2,pv1430441], .c 5, .c 3, .c 311, .c 11, .c 3, .c 5, .c 13,
  .c 3, .c 23, .p pv3 [pv2,pv3,pv11,pv14449], .c 3, .c 7, .c 131, .c 3, .c 11, .c 5, .c 3, .c 43,
  .c 7, .c 3, .c 5, .c 83, .c 3, .p pv2 [pv2,pv5,pv17,pv16829], .c 307, .c 3, .c 29, .c 41, .c 3,
  .c 73, .c 5, .c 3, .c 7, .c 37, .c 3, .c 5, .c 11, .c 3, .c 61, .c 7, .c 3, .c 67, .c 59, .c 3,
  .p pv2 [pv2,pv715243], .c 5, .c 3, .c 11, .c 17, .c 3, .c 5, .c 1601, .c 3, .c 7, .c 23, .c 3,
  .c 151, .p pv13 [pv2,pv3,pv7,pv17,pv4007], .c 3, .c 1549, .c 5, .c 3, .p pv3 [pv2,pv178813],
  .c 157, .c 3, .c 5, .c 991, .c 3, .c 31, .c 11, .c 3, .c 13, .c 617, .c 3, .c 7, .c 5, .c 3,
  .c 19, .p pv11 [pv2,pv3,pv5,pv7,pv13,pv131], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv57221],
  .c 13, .c 3, .c 491,
]
private theorem h0349c07 : checkBlock 2860803 128 b0349c07 = true := by
  decide +kernel

private def b0349c08 : List Row := [
  .p pv2 [pv2,pv3,pv19,pv25097], .c 3, .p pv5 [pv2,pv23,pv37,pv41], .c 5, .c 3, .c 239, .c 379,
  .c 3, .c 5, .c 19, .c 3, .p pv7 [pv2,pv5,pv71527], .c 17, .c 3, .c 59, .c 7, .c 3, .c 83, .c 5,
  .c 3, .c 37, .c 67, .c 3, .c 5, .p pv2 [pv2,pv3,pv476851], .c 3, .c 11,
  .p pv5 [pv2,pv3,pv97,pv1229], .c 3, .c 7, .p pv19 [pv2,pv3,pv13,pv12227], .c 3, .c 1279, .c 5,
  .c 3, .p pv3 [pv2,pv101,pv3541], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv37,pv179], .c 3, .c 109,
  .c 79, .c 3, .p pv2 [pv2,pv59,pv24247], .c 251, .c 3, .c 19, .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv113,pv211], .c 3, .c 5, .c 1217, .c 3, .c 131, .c 7, .c 3, .c 11, .c 397,
  .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv11,pv65027], .c 19, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv13,pv18341], .c 3, .c 7, .p pv2 [pv2,pv3,pv17,pv28051], .c 3, .c 31, .c 13,
  .c 3, .p pv2 [pv2,pv715303], .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .c 29, .c 3,
  .p pv7 [pv2,pv5,pv359,pv797], .p pv5 [pv2,pv3,pv11,pv5419], .c 3, .c 103,
  .p pv3 [pv2,pv3,pv31,pv15383], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv13,pv19,pv181],
  .p pv59 [pv2,pv3,pv5,pv7,pv109], .c 3, .c 5, .c 7, .c 3, .c 13, .c 43, .c 3, .c 19, .c 23, .c 3,
  .c 113, .c 5, .c 3, .p pv7 [pv2,pv7,pv204377], .c 571, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv286129], .c 743, .c 3, .p pv3 [pv2,pv178831], .c 7, .c 3,
  .p pv5 [pv2,pv67,pv131,pv163], .c 5, .c 3, .c 11, .c 53, .c 3,
]
private theorem h0349c08 : checkBlock 2861059 128 b0349c08 = true := by
  decide +kernel

private def b0349c09 : List Row := [
  .c 5, .p pv5 [pv2,pv3,pv79481], .c 3, .c 17, .c 59, .c 3, .c 7, .c 859, .c 3, .c 523, .c 5,
  .c 3, .c 13, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv476891], .c 3, .c 419, .c 11, .c 3, .c 547,
  .c 109, .c 3, .p pv2 [pv2,pv7,pv19,pv31,pv347], .c 5, .c 3, .c 7, .c 71, .c 3, .c 5,
  .p pv17 [pv2,pv3,pv7,pv2129], .c 3, .c 19, .c 7, .c 3, .p pv2 [pv2,pv11,pv113,pv1151], .c 17,
  .c 3, .c 31, .c 5, .c 3, .p pv7 [pv2,pv607,pv2357], .c 29, .c 3, .c 5, .c 23, .c 3, .c 7,
  .c 283, .c 3, .c 13, .c 11, .c 3, .c 17, .c 5, .c 3, .c 181, .c 41, .c 3, .c 5, .c 127, .c 3,
  .c 11, .c 13, .c 3, .p pv7 [pv2,pv7,pv313,pv653], .c 61, .c 3, .c 7, .c 5, .c 3, .c 29,
  .p pv2 [pv2,pv3,pv5,pv7,pv757], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv53,pv5399], .c 233,
  .c 3, .c 449, .p pv3 [pv2,pv3,pv43,pv3697], .c 3, .p pv2 [pv2,pv13,pv157,pv701], .c 5, .c 3,
  .c 271, .c 17, .c 3, .c 5, .p pv13 [pv2,pv3,pv11,pv3613], .c 3, .c 47, .c 67, .c 3, .c 11, .c 7,
  .c 3, .c 41, .c 5, .c 3, .c 137, .c 13, .c 3, .c 5, .c 73, .c 3, .p pv17 [pv2,pv5,pv7,pv40879],
  .c 19, .c 3, .c 7, .p pv3 [pv2,pv3,pv79,pv6037], .c 3, .c 37, .c 5, .c 3,
  .p pv2 [pv2,pv31,pv47,pv491], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv238463], .c 3,
  .p pv3 [pv2,pv5,pv13,pv5503], .c 1181, .c 3, .c 503, .p pv11 [pv2,pv3,pv23],
]
private theorem h0349c09 : checkBlock 2861315 128 b0349c09 = true := by
  decide +kernel

private def b0349c10 : List Row := [
  .c 3, .c 11, .c 5, .c 3, .c 7, .c 941, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv13,pv1747], .c 3,
  .c 23, .c 7, .c 3, .c 97, .c 13, .c 3, .p pv2 [pv2,pv1430801], .c 5, .c 3, .c 19, .c 193, .c 3,
  .c 5, .c 11, .c 3, .c 7, .p pv3 [pv2,pv3,pv197,pv269], .c 3, .c 17, .c 53, .c 3, .c 29, .c 5,
  .c 3, .c 11, .c 31, .c 3, .c 5, .c 19, .c 3, .c 13, .c 1423, .c 3, .p pv3 [pv2,pv7,pv137,pv373],
  .p pv2 [pv2,pv3,pv158981], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv715417],
  .p pv3 [pv2,pv3,pv5,pv7,pv13627], .c 3, .c 5, .c 7, .c 3, .c 647, .c 11, .c 3, .c 277, .c 47,
  .c 3, .c 43, .c 5, .c 3, .p pv2 [pv2,pv7,pv29201], .c 1433, .c 3, .c 5, .c 1259, .c 3,
  .p pv13 [pv2,pv5,pv286171], .c 1069, .c 3, .c 1523, .c 7, .c 3, .c 19, .c 5, .c 3, .c 13,
  .c 293, .c 3, .c 5, .p pv5 [pv2,pv3,pv43,pv47,pv59], .c 3, .p pv2 [pv2,pv5,pv7,pv20441],
  .p pv5 [pv2,pv3,pv13,pv19,pv1931], .c 3, .c 7, .c 11, .c 3, .c 191, .c 5, .c 3, .c 41, .c 7,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv173,pv919], .c 3, .c 11, .c 409, .c 3, .p pv3 [pv2,pv383,pv467],
  .c 43, .c 3, .c 47, .c 5, .c 3, .c 7, .c 97, .c 3, .c 5, .c 17, .c 3,
  .p pv3 [pv2,pv5,pv41,pv349], .c 7, .c 3, .c 13, .p pv7 [pv2,pv3,pv59621], .c 3, .c 229, .c 5,
  .c 3, .c 73, .c 23, .c 3, .c 5,
]
private theorem h0349c10 : checkBlock 2861571 128 b0349c10 = true := by
  decide +kernel

private def b0349c11 : List Row := [
  .c 31, .c 3, .c 7, .c 13, .c 3, .c 11, .c 37, .c 3, .c 149, .c 5, .c 3,
  .p pv3 [pv2,pv11,pv17,pv1913], .p pv2 [pv2,pv3,pv5,pv19079], .c 3, .c 5, .c 1187, .c 3,
  .p pv3 [pv2,pv5,pv143093], .c 1021, .c 3, .c 23, .p pv2 [pv2,pv3,pv71,pv3359], .c 3, .c 7, .c 5,
  .c 3, .c 167, .c 11, .c 3, .c 5, .c 7, .c 3, .c 269, .c 1627, .c 3, .p pv3 [pv2,pv357737],
  .c 17, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv7,pv43,pv2377], .c 13, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv17,pv14029], .c 3, .p pv3 [pv2,pv5,pv31,pv577], .c 29, .c 3,
  .p pv5 [pv2,pv449,pv3187], .c 7, .c 3, .c 17, .c 5, .c 3, .c 71, .p pv2 [pv2,pv3,pv5,pv47699],
  .c 3, .c 5, .c 11, .c 3, .c 19, .c 157, .c 3, .c 7, .c 23, .c 3, .c 13, .c 5, .c 3, .c 11, .c 7,
  .c 3, .c 5, .p pv11 [pv2,pv3,pv13,pv9173], .c 3, .c 29, .c 1201, .c 3, .c 37, .c 13, .c 3,
  .c 643, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 1193, .c 3, .p pv2 [pv2,pv5,pv29,pv71,pv139],
  .c 7, .c 3, .p pv3 [pv2,pv197,pv227], .c 811, .c 3, .c 1663, .c 5, .c 3, .c 373, .c 59, .c 3,
  .c 5, .c 43, .c 3, .c 7, .p pv2 [pv2,pv3,pv229,pv2083], .c 3, .p pv5 [pv2,pv11,pv19,pv41,pv167],
  .p pv13 [pv2,pv3,pv7,pv4259], .c 3, .c 53, .c 5, .c 3, .c 61, .c 37, .c 3, .c 5, .c 13, .c 3,
  .c 1087, .c 1097, .c 3, .p pv2 [pv2,pv7,pv102217], .c 11, .c 3,
]
private theorem h0349c11 : checkBlock 2861827 128 b0349c11 = true := by
  decide +kernel

private def b0349c12 : List Row := [
  .c 7, .c 5, .c 3, .c 83, .c 79, .c 3, .c 5, .c 7, .c 3, .c 11, .c 17, .c 3, .c 509,
  .p pv2 [pv2,pv3,pv26501], .c 3, .p pv3 [pv2,pv11,pv47,pv173], .c 5, .c 3, .c 13, .c 761, .c 3,
  .c 5, .p pv7 [pv2,pv3,pv29,pv5483], .c 3, .p pv2 [pv2,pv5,pv433,pv661], .c 311, .c 3, .c 17,
  .c 7, .c 3, .c 23, .c 5, .c 3, .c 59, .c 89, .c 3, .c 5, .c 331, .c 3, .c 307,
  .p pv41 [pv2,pv3,pv53003], .c 3, .c 7, .c 41, .c 3, .c 67, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv477031], .c 3, .c 457, .c 317, .c 3, .c 13, .c 31, .c 3,
  .p pv2 [pv2,pv7,pv204443], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 19, .c 3,
  .p pv2 [pv2,pv5,pv143111], .c 7, .c 3, .p pv2 [pv2,pv1431113], .c 263, .c 3, .c 11, .c 5, .c 3,
  .c 17, .c 277, .c 3, .c 5, .c 827, .c 3, .c 7, .c 47, .c 3, .c 73,
  .p pv11 [pv2,pv3,pv7,pv23,pv2963], .c 3, .c 617, .c 5, .c 3, .c 673, .c 29, .c 3, .c 5, .c 11,
  .c 3, .c 23, .c 37, .c 3, .c 1429, .p pv7 [pv2,pv3,pv11,pv13,pv139], .c 3, .c 7, .c 5, .c 3,
  .c 11, .c 13, .c 3, .c 5, .c 7, .c 3, .p pv41 [pv2,pv5,pv11,pv26021],
  .p pv5 [pv2,pv3,pv19,pv6277], .c 3, .c 293, .c 787, .c 3, .c 31, .c 5, .c 3, .c 29, .c 19, .c 3,
  .c 5, .p pv23 [pv2,pv3,pv3727],
]
private theorem h0349c12 : checkBlock 2862083 128 b0349c12 = true := by
  decide +kernel

private def b0349c13 : List Row := [
  .c 3, .c 17, .c 11, .c 3, .c 47, .c 7, .c 3, .c 13, .c 5, .c 3, .p pv11 [pv2,pv17,pv29,pv2903],
  .p pv11 [pv2,pv3,pv5,pv7951], .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv36697], .c 3, .c 53, .c 23,
  .c 3, .c 7, .c 13, .c 3, .c 193, .c 5, .c 3, .c 179, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv23,pv3457], .c 3, .p pv7 [pv2,pv5,pv1789], .c 73, .c 3, .c 19, .c 11, .c 3,
  .p pv2 [pv2,pv7,pv102229], .c 5, .c 3, .c 7, .c 83, .c 3, .c 5, .c 139, .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv71,pv10079], .c 149, .c 3, .c 17, .c 5, .c 3, .c 109, .c 547, .c 3, .c 5, .c 13,
  .c 3, .c 7, .p pv13 [pv2,pv3,pv477077], .c 3, .c 43, .p pv41 [pv2,pv3,pv7,pv37,pv307], .c 3,
  .c 103, .c 5, .c 3, .c 1297, .c 131, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv61,pv79], .c 3,
  .p pv2 [pv2,pv5,pv286249], .p pv2 [pv2,pv3,pv263,pv907], .c 3, .c 11,
  .p pv3 [pv2,pv3,pv349,pv1367], .c 3, .c 7, .c 5, .c 3, .c 13, .c 17, .c 3, .c 5, .c 7, .c 3,
  .c 19, .p pv3 [pv2,pv3,pv13,pv941], .c 3, .c 1123, .p pv7 [pv2,pv3,pv17,pv877], .c 3, .c 1009,
  .c 5, .c 3, .p pv2 [pv2,pv7,pv41,pv4987], .c 11, .c 3, .c 5, .c 61, .c 3,
  .p pv17 [pv2,pv5,pv57251], .c 43, .c 3, .c 23, .c 7, .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv179,pv1999], .c 31, .c 3, .c 5, .p pv5 [pv2,pv3,pv103,pv193], .c 3, .c 157, .c 53,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv149,pv1601], .c 3, .p pv3 [pv2,pv5591],
]
private theorem h0349c13 : checkBlock 2862339 128 b0349c13 = true := by
  decide +kernel

private def b0349c14 : List Row := [
  .c 5, .c 3, .p pv11 [pv2,pv241,pv5939], .c 7, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv293,pv977], .c 13, .c 3, .p pv3 [pv2,pv19,pv37,pv509], .c 29, .c 3,
  .p pv5 [pv2,pv7,pv73,pv2801], .c 5, .c 3, .c 7, .c 173, .c 3, .c 5, .c 211, .c 3,
  .p pv3 [pv2,pv5,pv11,pv3253], .c 7, .c 3, .c 17, .c 23, .c 3, .c 37, .c 5, .c 3, .c 1063, .c 41,
  .c 3, .c 5, .c 109, .c 3, .c 7, .c 11, .c 3, .c 29, .c 103, .c 3, .p pv2 [pv2,pv43,pv33287],
  .c 5, .c 3, .c 53, .c 13, .c 3, .c 5, .c 227, .c 3, .p pv2 [pv2,pv5,pv28627],
  .p pv5 [pv2,pv3,pv41,pv431], .c 3, .c 127, .c 67, .c 3, .c 7, .c 5, .c 3, .c 439, .c 1049, .c 3,
  .c 5, .c 7, .c 3, .p pv19 [pv2,pv5,pv13,pv19,pv61], .p pv2 [pv2,pv3,pv17,pv14033], .c 3, .c 149,
  .c 11, .c 3, .c 13, .c 5, .c 3, .c 17, .p pv11 [pv2,pv3,pv5,pv11,pv347], .c 3, .c 5, .c 31,
  .c 3, .c 11, .c 499, .c 3, .c 397, .c 7, .c 3, .c 1481, .c 5, .c 3, .c 743, .c 947, .c 3, .c 5,
  .c 19, .c 3, .c 61, .c 29, .c 3, .c 7, .c 587, .c 3, .p pv2 [pv2,pv79,pv18119], .c 5, .c 3,
  .c 151, .c 7, .c 3, .c 5, .c 17, .c 3, .c 13, .c 1451, .c 3, .c 11,
  .p pv13 [pv2,pv3,pv281,pv283], .c 3, .c 23, .c 5, .c 3, .c 7, .c 73, .c 3, .c 5, .c 13, .c 3,
]
private theorem h0349c14 : checkBlock 2862595 128 b0349c14 = true := by
  decide +kernel

private def b0349c15 : List Row := [
  .c 17, .c 7, .c 3, .c 59, .p pv2 [pv2,pv3,pv97,pv4919], .c 3, .c 19, .c 5, .c 3, .c 1289, .c 11,
  .c 3, .c 5, .c 181, .c 3, .c 7, .p pv3 [pv2,pv3,pv11,pv19,pv761], .c 3,
  .p pv5 [pv2,pv13,pv149,pv739], .c 137, .c 3, .c 11, .c 5, .c 3, .c 13, .c 19, .c 3, .c 5, .c 41,
  .c 3, .c 47, .c 61, .c 3, .p pv2 [pv2,pv7,pv59,pv1733], .c 17, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv178933], .p pv2 [pv2,pv3,pv5,pv7,pv13633], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv43,pv3329], .c 31, .c 3, .p pv2 [pv2,pv101,pv14173], .c 37, .c 3, .c 17, .c 5,
  .c 3, .c 11, .c 127, .c 3, .c 5, .c 29, .c 3, .c 23, .p pv5 [pv2,pv3,pv7,pv541], .c 3, .c 13,
  .c 7, .c 3, .c 43, .c 5, .c 3, .c 41, .p pv3 [pv2,pv3,pv5,pv13,pv2447], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv19,pv29,pv433], .c 3, .c 197, .c 11, .c 3, .c 7, .p pv11 [pv2,pv3,pv9941],
  .c 3, .c 199, .c 5, .c 3, .p pv2 [pv2,pv263,pv5443], .c 7, .c 3, .c 5, .c 419, .c 3,
  .p pv13 [pv2,pv5,pv41,pv6983], .c 677, .c 3, .p pv2 [pv2,pv11,pv31,pv2099], .c 79, .c 3,
  .c 1223, .c 5, .c 3, .c 7, .c 809, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv8521], .c 3,
  .p pv2 [pv2,pv5,pv37,pv53,pv73], .c 7, .c 3, .c 31, .c 11, .c 3, .c 487, .c 5, .c 3,
  .p pv7 [pv2,pv1431539], .c 13, .c 3, .c 5, .c 1031, .c 3, .c 7, .c 59, .c 3, .c 37, .c 47, .c 3,
  .c 109, .c 5,
]
private theorem h0349c15 : checkBlock 2862851 128 b0349c15 = true := by
  decide +kernel

private def b0349c16 : List Row := [
  .c 3, .c 23, .c 67, .c 3, .c 5, .p pv7 [pv2,pv3,pv79531], .c 3, .p pv3 [pv2,pv5,pv13,pv2753],
  .c 17, .c 3, .p pv5 [pv2,pv7,pv204509], .c 19, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv1431569],
  .c 29, .c 3, .c 5, .c 7, .c 3, .c 227, .c 41, .c 3, .c 11, .c 13, .c 3, .c 137, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv11,pv83], .c 37, .c 3, .c 5, .c 467, .c 3, .p pv2 [pv2,pv5,pv143159], .c 353,
  .c 3, .c 229, .c 7, .c 3, .c 47, .c 5, .c 3, .c 29, .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv73,pv2179], .c 3, .c 13, .c 107, .c 3, .c 7, .c 53, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv29,pv24683], .c 7, .c 3, .c 5, .c 13, .c 3, .c 43, .c 19, .c 3, .c 23, .c 101,
  .c 3, .c 31, .c 5, .c 3, .c 7, .c 139, .c 3, .c 5, .c 11, .c 3, .c 461, .c 7, .c 3,
  .p pv3 [pv2,pv13,pv17,pv41,pv79], .c 61, .c 3, .p pv2 [pv2,pv37,pv38693], .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv95443], .c 3, .c 5, .c 103, .c 3, .c 7, .p pv3 [pv2,pv3,pv13,pv36709],
  .c 3, .c 113, .p pv2 [pv2,pv3,pv7,pv89,pv383], .c 3, .p pv5 [pv2,pv67,pv2671], .c 5, .c 3,
  .c 19, .c 109, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv286333], .c 11, .c 3, .c 233, .c 23,
  .c 3, .c 7, .c 5, .c 3, .c 277, .p pv23 [pv2,pv3,pv5,pv7,pv101], .c 3, .c 5, .c 7, .c 3, .c 17,
]
private theorem h0349c16 : checkBlock 2863107 128 b0349c16 = true := by
  decide +kernel

private def b0349c17 : List Row := [
  .p pv23 [pv2,pv3,pv23,pv20749], .c 3, .c 13, .p pv7 [pv2,pv3,pv39769], .c 3, .c 29, .c 5, .c 3,
  .c 67, .c 47, .c 3, .c 5, .p pv2 [pv2,pv3,pv271,pv587], .c 3, .p pv13 [pv2,pv5,pv281,pv1019],
  .c 13, .c 3, .c 89, .c 7, .c 3, .p pv2 [pv2,pv29,pv49369], .c 5, .c 3, .c 409, .c 199, .c 3,
  .c 5, .c 83, .c 3, .c 11, .p pv17 [pv2,pv3,pv159079], .c 3, .c 7, .c 17, .c 3, .c 19, .c 5,
  .c 3, .c 31, .c 7, .c 3, .c 5, .c 59, .c 3, .c 101, .p pv2 [pv2,pv3,pv19,pv661], .c 3,
  .p pv3 [pv2,pv43,pv2081], .c 239, .c 3, .c 17, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 23, .c 3,
  .c 41, .c 7, .c 3, .c 11, .c 29, .c 3, .p pv2 [pv2,pv715873], .c 5, .c 3, .c 43, .c 31, .c 3,
  .c 5, .c 839, .c 3, .c 7, .c 67, .c 3, .p pv2 [pv2,pv715879], .p pv17 [pv2,pv3,pv7,pv29,pv2351],
  .c 3, .c 13, .c 5, .c 3, .c 131, .c 11, .c 3, .c 5, .c 53, .c 3, .c 37, .c 223, .c 3, .c 19,
  .c 13, .c 3, .c 7, .c 5, .c 3, .p pv17 [pv2,pv1431779], .c 397, .c 3, .c 5, .c 7, .c 3, .c 73,
  .p pv7 [pv2,pv3,pv71,pv3361], .c 3, .p pv3 [pv2,pv29,pv12343], .c 503, .c 3, .c 83, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv13,pv7867], .p pv3 [pv2,pv3,pv5,pv53,pv1801], .c 3, .c 5, .c 11, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv7,pv22727], .c 3, .p pv5 [pv2,pv103,pv13901], .c 7, .c 3, .c 1447, .c 5, .c 3,
]
private theorem h0349c17 : checkBlock 2863363 128 b0349c17 = true := by
  decide +kernel

private def b0349c18 : List Row := [
  .c 11, .c 797, .c 3, .c 5, .c 13, .c 3, .c 149, .c 17, .c 3, .c 7, .c 1061, .c 3, .c 53, .c 5,
  .c 3, .p pv3 [pv2,pv109,pv821], .c 7, .c 3, .c 5, .c 271, .c 3, .c 19, .c 11, .c 3, .c 17,
  .c 173, .c 3, .c 1483, .c 5, .c 3, .c 7, .c 1279, .c 3, .c 5, .c 31, .c 3, .c 383, .c 7, .c 3,
  .p pv5 [pv2,pv11,pv53,pv307], .c 19, .c 3, .p pv5 [pv2,pv1431851], .c 5, .c 3, .c 103, .c 137,
  .c 3, .c 5, .c 73, .c 3, .c 7, .c 127, .c 3, .c 41, .c 11, .c 3, .p pv2 [pv2,pv461,pv1553],
  .c 5, .c 3, .p pv2 [pv2,pv1431869], .p pv17 [pv2,pv3,pv5,pv11,pv4339], .c 3, .c 5, .c 163, .c 3,
  .c 11, .c 23, .c 3, .c 13, .c 113, .c 3, .c 7, .c 5, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv5,pv7,pv13,pv1049], .c 3, .c 5, .c 7, .c 3, .c 67, .c 13, .c 3,
  .p pv2 [pv2,pv17,pv84229], .c 197, .c 3, .p pv3 [pv2,pv178987], .c 5, .c 3, .c 23, .c 59, .c 3,
  .c 5, .c 263, .c 3, .c 31, .c 19, .c 3, .c 11, .c 7, .c 3, .p pv5 [pv2,pv13,pv23,pv4789], .c 5,
  .c 3, .c 79, .c 733, .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv7,pv2557], .c 43, .c 3, .c 7,
  .p pv61 [pv2,pv3,pv13,pv67,pv137], .c 3, .p pv2 [pv2,pv715963], .c 5, .c 3,
  .p pv2 [pv2,pv1431929], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv29,pv109,pv151], .c 3, .c 17, .c 31,
]
private theorem h0349c18 : checkBlock 2863619 128 b0349c18 = true := by
  decide +kernel

private def b0349c19 : List Row := [
  .c 3, .p pv2 [pv2,pv715969], .p pv7 [pv2,pv3,pv477313], .c 3, .c 11, .c 5, .c 3, .c 7, .c 23,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv17047], .c 3, .c 827, .c 7, .c 3, .p pv2 [pv2,pv859,pv1667],
  .p pv2 [pv2,pv3,pv19,pv53,pv79], .c 3, .c 13, .c 5, .c 3, .c 59, .p pv13 [pv2,pv3,pv5,pv11933],
  .c 3, .c 5, .c 11, .c 3, .c 7, .c 1571, .c 3, .c 23, .c 13, .c 3, .p pv5 [pv2,pv401,pv3571],
  .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv61,pv313], .c 3, .c 5, .c 1249, .c 3, .c 53, .c 181,
  .c 3, .p pv5 [pv2,pv7,pv31,pv6599], .p pv7 [pv2,pv3,pv29833], .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv59,pv1867], .c 563, .c 3, .c 5, .c 7, .c 3, .c 13, .c 11, .c 3, .c 31,
  .c 311, .c 3, .c 19, .c 5, .c 3, .c 73, .c 29, .c 3, .c 5, .c 13, .c 3,
  .p pv2 [pv2,pv5,pv89,pv1609], .p pv3 [pv2,pv3,pv7,pv19,pv37,pv97], .c 3,
  .p pv5 [pv2,pv11,pv130183], .c 7, .c 3, .p pv3 [pv2,pv89501], .c 5, .c 3, .c 47, .c 17, .c 3,
  .c 5, .c 487, .c 3, .p pv11 [pv2,pv5,pv7,pv167], .c 131, .c 3, .c 7, .c 11, .c 3, .c 421, .c 5,
  .c 3, .c 13, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv238673], .c 3, .c 11,
  .p pv2 [pv2,pv3,pv13,pv73,pv503], .c 3, .p pv5 [pv2,pv47,pv30469], .p pv13 [pv2,pv3,pv39779],
  .c 3, .p pv2 [pv2,pv7,pv11,pv17,pv547], .c 5, .c 3, .c 7, .c 43, .c 3, .c 5, .c 929, .c 3,
  .c 467, .c 7, .c 3, .c 19, .c 97, .c 3, .c 887, .c 5, .c 3, .p pv3 [pv2,pv2797],
]
private theorem h0349c19 : checkBlock 2863875 128 b0349c19 = true := by
  decide +kernel

private def b0349c20 : List Row := [
  .c 881, .c 3, .c 5, .c 41, .c 3, .c 7, .c 17, .c 3, .c 11, .p pv2 [pv2,pv3,pv7,pv4871], .c 3,
  .p pv3 [pv2,pv31,pv11549], .c 5, .c 3, .p pv7 [pv2,pv11,pv101,pv1289], .c 251, .c 3, .c 5,
  .c 23, .c 3, .c 449, .c 13, .c 3, .c 17, .c 179, .c 3, .c 7, .c 5, .c 3, .c 1601, .c 11, .c 3,
  .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv14321], .p pv11 [pv2,pv3,pv11,pv43397], .c 3, .c 37,
  .p pv7 [pv2,pv3,pv59671], .c 3, .c 11, .c 5, .c 3, .c 41, .p pv11 [pv2,pv3,pv5,pv47737], .c 3,
  .c 5, .c 47, .c 3, .c 19, .c 281, .c 3, .p pv2 [pv2,pv23,pv163,pv191], .c 7, .c 3, .c 29, .c 5,
  .c 3, .p pv3 [pv2,pv358031], .c 13, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv7,pv41,pv499],
  .c 313, .c 3, .c 7, .c 19, .c 3, .c 43, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 89, .c 3,
  .p pv2 [pv2,pv5,pv11,pv13,pv2003], .p pv5 [pv2,pv3,pv238691], .c 3, .c 863,
  .p pv2 [pv2,pv3,pv477383], .c 3, .c 13, .c 5, .c 3, .c 7, .c 1277, .c 3, .c 5, .c 67, .c 3,
  .c 47, .c 7, .c 3, .c 103, .c 13, .c 3, .c 263, .c 5, .c 3, .p pv7 [pv2,pv31,pv46199],
  .p pv2 [pv2,pv3,pv5,pv15913], .c 3, .c 5, .c 17, .c 3, .c 7, .c 71, .c 3,
  .p pv2 [pv2,pv11,pv65099], .c 29, .c 3, .p pv2 [pv2,pv1432181], .c 5, .c 3, .c 31,
  .p pv2 [pv2,pv3,pv5,pv95479], .c 3, .c 5, .c 61, .c 3, .c 13, .c 19, .c 3,
]
private theorem h0349c20 : checkBlock 2864131 128 b0349c20 = true := by
  decide +kernel

private def b0349c21 : List Row := [
  .c 677, .c 11, .c 3, .c 7, .c 5, .c 3, .c 163, .p pv19 [pv2,pv3,pv5,pv7,pv11,pv31], .c 3, .c 5,
  .c 7, .c 3, .c 11, .c 83, .c 3, .c 29, .p pv3 [pv2,pv3,pv599,pv797], .c 3,
  .p pv5 [pv2,pv11,pv130201], .c 5, .c 3, .c 37, .c 31, .c 3, .c 5, .c 113, .c 3,
  .p pv3 [pv2,pv5,pv19,pv3769], .c 23, .c 3, .c 73, .c 7, .c 3, .p pv2 [pv2,pv811,pv883], .c 5,
  .c 3, .c 13, .c 79, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv17,pv23,pv37], .c 3, .c 523,
  .p pv5 [pv2,pv3,pv13,pv9181], .c 3, .c 7, .p pv3 [pv2,pv3,pv19,pv25127], .c 3, .c 17, .c 5,
  .c 3, .c 23, .c 7, .c 3, .c 5, .c 19, .c 3, .c 1531, .c 37, .c 3, .c 97, .c 47, .c 3, .c 227,
  .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv241,pv283], .c 3, .c 43, .c 7, .c 3,
  .c 13, .p pv2 [pv2,pv3,pv53047], .c 3, .c 11, .c 5, .c 3, .c 613, .c 17, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv47,pv1693], .c 3, .c 7, .c 13, .c 3, .c 1433, .p pv13 [pv2,pv3,pv7,pv17,pv59],
  .c 3, .c 19, .c 5, .c 3, .c 83, .c 23, .c 3, .c 5, .c 11, .c 3, .c 29, .c 73, .c 3, .c 53,
  .p pv3 [pv2,pv3,pv11,pv43403], .c 3, .c 7, .c 5, .c 3, .c 11, .c 19, .c 3, .c 5, .c 7, .c 3,
  .c 61, .p pv5 [pv2,pv3,pv157,pv3041], .c 3, .c 23, .c 41, .c 3, .p pv3 [pv2,pv358079], .c 5,
  .c 3, .c 547, .c 13,
]
private theorem h0349c21 : checkBlock 2864387 128 b0349c21 = true := by
  decide +kernel

private def b0349c22 : List Row := [
  .c 3, .c 5, .p pv3 [pv2,pv3,pv17683], .c 3, .c 37, .c 11, .c 3, .p pv3 [pv2,pv179041], .c 7,
  .c 3, .c 101, .c 5, .c 3, .c 809, .p pv3 [pv2,pv3,pv5,pv17,pv41,pv137], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv238723], .c 3, .p pv11 [pv2,pv5,pv7,pv13,pv787], .p pv3 [pv2,pv3,pv61,pv2609],
  .c 3, .c 7, .p pv19 [pv2,pv3,pv37,pv1613], .c 3, .c 13, .c 5, .c 3, .c 193, .c 7, .c 3, .c 5,
  .c 29, .c 3, .c 41, .p pv7 [pv2,pv3,pv119363], .c 3, .p pv2 [pv2,pv179,pv4001], .c 11, .c 3,
  .p pv5 [pv2,pv7,pv204623], .c 5, .c 3, .c 7, .c 617, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv29],
  .c 3, .c 11, .c 7, .c 3, .c 211, .p pv7 [pv2,pv3,pv238729], .c 3, .c 1093, .c 5, .c 3, .c 499,
  .p pv23 [pv2,pv3,pv5,pv23873], .c 3, .c 5, .c 241, .c 3, .c 7, .c 1123, .c 3, .c 79, .c 71,
  .c 3, .c 593, .c 5, .c 3, .c 17, .c 47, .c 3, .c 5, .c 13, .c 3, .c 19, .c 31, .c 3, .c 11,
  .c 53, .c 3, .c 7, .c 5, .c 3, .c 1049, .c 89, .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv286483], .p pv7 [pv2,pv3,pv43,pv347], .c 3, .c 337, .c 19, .c 3,
  .p pv2 [pv2,pv103,pv13907], .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 17, .c 3, .c 379, .c 59,
  .c 3, .p pv2 [pv2,pv127,pv11279], .c 7, .c 3, .c 11, .c 5, .c 3, .p pv17 [pv2,pv1432439], .c 29,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv691], .c 3, .c 17, .c 239, .c 3, .c 7,
]
private theorem h0349c22 : checkBlock 2864643 128 b0349c22 = true := by
  decide +kernel

private def b0349c23 : List Row := [
  .c 479, .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv17,pv42131], .c 7, .c 3, .c 5, .c 11, .c 3,
  .c 71, .c 151, .c 3, .c 13, .c 139, .c 3, .c 457, .c 5, .c 3, .c 7, .c 349, .c 3, .c 5, .c 37,
  .c 3, .c 857, .c 7, .c 3, .c 41, .c 17, .c 3, .p pv2 [pv2,pv1432481], .c 5, .c 3,
  .p pv3 [pv2,pv29,pv53,pv233], .c 197, .c 3, .c 5, .p pv13 [pv2,pv3,pv17,pv3511], .c 3, .c 7,
  .c 11, .c 3, .c 61, .c 31, .c 3, .c 17, .c 5, .c 3, .c 89, .p pv11 [pv2,pv3,pv5,pv191], .c 3,
  .c 5, .p pv5 [pv2,pv3,pv159167], .c 3, .c 277, .c 373, .c 3, .c 599, .c 229, .c 3, .c 7, .c 5,
  .c 3, .c 19, .c 13, .c 3, .c 5, .c 7, .c 3, .c 23, .p pv2 [pv2,pv3,pv159169], .c 3, .c 43,
  .c 11, .c 3, .c 173, .c 5, .c 3, .p pv2 [pv2,pv7,pv37,pv5531], .c 17, .c 3, .c 5, .c 19, .c 3,
  .c 11, .c 47, .c 3, .c 83, .c 7, .c 3, .c 13, .c 5, .c 3, .c 97,
  .p pv2 [pv2,pv3,pv5,pv43,pv2221], .c 3, .c 5, .p pv23 [pv2,pv3,pv13,pv3061], .c 3, .c 131,
  .c 739, .c 3, .c 7, .c 13, .c 3, .c 29, .c 5, .c 3, .c 269, .c 7, .c 3, .c 5, .c 53, .c 3,
  .p pv2 [pv2,pv5,pv286513], .c 23, .c 3, .c 11, .c 107, .c 3, .c 19, .c 5, .c 3, .c 7, .c 103,
  .c 3,
]
private theorem h0349c23 : checkBlock 2864899 128 b0349c23 = true := by
  decide +kernel

private def b0349c24 : List Row := [
  .c 5, .p pv5 [pv2,pv3,pv7,pv23,pv1483], .c 3, .c 13, .c 7, .c 3, .c 47, .c 37, .c 3,
  .p pv3 [pv2,pv79,pv9067], .c 5, .c 3, .c 23, .c 11, .c 3, .c 5, .c 13, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv11,pv10853], .c 3, .c 17, .p pv3 [pv2,pv3,pv7,pv68219], .c 3, .c 11, .c 5,
  .c 3, .p pv3 [pv2,pv557,pv643], .p pv3 [pv2,pv3,pv5,pv95507], .c 3, .c 5, .c 59, .c 3, .c 967,
  .c 383, .c 3, .c 853, .c 29, .c 3, .c 7, .c 5, .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv7,pv379],
  .c 3, .c 5, .c 7, .c 3, .c 79, .c 179, .c 3, .c 19, .p pv41 [pv2,pv3,pv11,pv29,pv499], .c 3,
  .c 811, .c 5, .c 3, .c 11, .c 23, .c 3, .c 5, .p pv2 [pv2,pv3,pv19,pv59,pv71], .c 3, .c 1607,
  .c 97, .c 3, .c 29, .c 7, .c 3, .c 257, .c 5, .c 3, .c 17, .c 353, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv477551], .c 3, .p pv17 [pv2,pv5,pv7,pv40933], .c 11, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv477553], .c 3, .c 73, .c 5, .c 3, .p pv3 [pv2,pv179083], .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv119389], .c 3, .c 113, .c 13, .c 3, .c 71, .c 1663, .c 3, .c 61, .c 5, .c 3,
  .c 7, .c 31, .c 3, .c 5, .c 17, .c 3, .c 19, .c 7, .c 3, .c 163, .c 11, .c 3,
  .p pv11 [pv2,pv13,pv191,pv577], .c 5, .c 3, .c 67, .c 37, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv73,pv3271], .c 3, .c 7, .c 29, .c 3, .c 157, .c 19,
]
private theorem h0349c24 : checkBlock 2865155 128 b0349c24 = true := by
  decide +kernel

private def b0349c25 : List Row := [
  .c 3, .p pv2 [pv2,pv11,pv65123], .c 5, .c 3, .c 149, .c 13, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv477571], .c 3, .p pv7 [pv2,pv5,pv286543], .p pv5 [pv2,pv3,pv23,pv29,pv179],
  .c 3, .c 1171, .p pv3 [pv2,pv3,pv159191], .c 3, .c 7, .c 5, .c 3, .c 41, .c 1373, .c 3, .c 5,
  .c 7, .c 3, .c 29, .p pv5 [pv2,pv3,pv477577], .c 3, .c 11, .c 17, .c 3, .c 13, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv11,pv23,pv809], .p pv13 [pv2,pv3,pv5,pv23879], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv17,pv2161], .c 3, .p pv2 [pv2,pv5,pv29,pv41,pv241],
  .p pv5 [pv2,pv3,pv7,pv83,pv137], .c 3, .p pv3 [pv2,pv47,pv7621], .c 7, .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv487,pv1471], .c 11, .c 3, .c 5, .c 523, .c 3, .p pv11 [pv2,pv5,pv7,pv17,pv43],
  .c 19, .c 3, .c 7, .p pv23 [pv2,pv3,pv39799], .c 3, .c 11, .c 5, .c 3, .c 37, .c 7, .c 3, .c 5,
  .c 23, .c 3, .c 13, .c 167, .c 3, .p pv2 [pv2,pv716389], .p pv3 [pv2,pv3,pv477593], .c 3, .c 43,
  .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv19,pv7541], .c 7, .c 3,
  .p pv2 [pv2,pv1193,pv1201], .p pv2 [pv2,pv3,pv11,pv17,pv1277], .c 3, .c 23, .c 5, .c 3, .c 11,
  .p pv19 [pv2,pv3,pv5,pv199], .c 3, .c 5, .p pv3 [pv2,pv3,pv29,pv43,pv383], .c 3, .c 7, .c 37,
  .c 3, .p pv3 [pv2,pv13,pv23,pv599], .c 379, .c 3, .p pv5 [pv2,pv17,pv89,pv947], .c 5, .c 3,
  .c 13, .c 71, .c 3, .c 5, .c 19, .c 3, .p pv41 [pv2,pv5,pv31,pv2311], .c 11, .c 3, .c 607,
  .c 43, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv61,pv83,pv283], .p pv17 [pv2,pv3,pv5,pv7,pv6823],
  .c 3, .c 5,
]
private theorem h0349c25 : checkBlock 2865411 128 b0349c25 = true := by
  decide +kernel

private def b0349c26 : List Row := [
  .c 7, .c 3, .c 31, .c 17, .c 3, .c 541, .p pv3 [pv2,pv3,pv151,pv3163], .c 3,
  .p pv2 [pv2,pv1432841], .c 5, .c 3, .c 59, .p pv2 [pv2,pv3,pv5,pv17,pv1873], .c 3, .c 5,
  .p pv31 [pv2,pv3,pv29851], .c 3, .p pv3 [pv2,pv5,pv28657], .c 163, .c 3, .c 13, .c 7, .c 3,
  .c 19, .c 5, .c 3, .c 61, .c 157, .c 3, .c 5, .p pv5 [pv2,pv3,pv53069], .c 3, .c 11, .c 13,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv477623], .c 3, .p pv5 [pv2,pv11,pv130261], .c 5, .c 3,
  .p pv2 [pv2,pv59,pv12143], .c 7, .c 3, .c 5, .c 499, .c 3, .c 37, .c 53, .c 3, .c 443, .c 103,
  .c 3, .c 71, .c 5, .c 3, .c 7, .c 107, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv11,pv6203], .c 3,
  .c 67, .c 7, .c 3, .c 11, .c 199, .c 3, .p pv2 [pv2,pv211,pv6791], .c 5, .c 3, .c 17, .c 13,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv53,pv751], .c 3, .c 7, .c 23, .c 3, .c 19, .c 151, .c 3, .c 293,
  .c 5, .c 3, .p pv7 [pv2,pv29,pv49411], .c 11, .c 3, .c 5, .c 457, .c 3, .c 643, .c 829, .c 3,
  .c 31, .c 41, .c 3, .c 7, .c 5, .c 3, .c 23, .p pv3 [pv2,pv3,pv5,pv7,pv4549], .c 3, .c 5, .c 7,
  .c 3, .p pv3 [pv2,pv5,pv71647], .c 79, .c 3, .c 131, .c 13, .c 3, .c 881, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv204707], .p pv7 [pv2,pv3,pv5,pv41,pv233], .c 3, .c 5, .c 11, .c 3, .c 17,
  .p pv11 [pv2,pv3,pv7,pv2437], .c 3, .p pv2 [pv2,pv716479], .c 7, .c 3,
]
private theorem h0349c26 : checkBlock 2865667 128 b0349c26 = true := by
  decide +kernel

private def b0349c27 : List Row := [
  .p pv2 [pv2,pv19,pv53,pv1423], .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv95531], .c 3, .c 5,
  .c 109, .c 3, .c 13, .c 397, .c 3, .c 7, .p pv2 [pv2,pv3,pv238829], .c 3, .p pv3 [pv2,pv89561],
  .c 5, .c 3, .c 577, .c 7, .c 3, .c 5, .c 13, .c 3, .p pv11 [pv2,pv5,pv463,pv619], .c 11, .c 3,
  .p pv3 [pv2,pv101,pv3547], .c 17, .c 3, .c 29, .c 5, .c 3, .c 7, .c 659, .c 3, .c 5, .c 317,
  .c 3, .p pv3 [pv2,pv5,pv1433], .c 7, .c 3, .c 23, .c 127, .c 3, .c 17, .c 5, .c 3, .c 13,
  .c 521, .c 3, .c 5, .c 433, .c 3, .c 7, .p pv5 [pv2,pv3,pv13,pv1531], .c 3, .c 461, .c 11, .c 3,
  .c 31, .c 5, .c 3, .p pv3 [pv2,pv22391], .p pv37 [pv2,pv3,pv5,pv11,pv193], .c 3, .c 5, .c 37,
  .c 3, .c 11, .c 769, .c 3, .c 89, .p pv2 [pv2,pv3,pv79613], .c 3, .c 7, .c 5, .c 3, .c 43,
  .c 17, .c 3, .c 5, .c 7, .c 3, .c 173, .c 19, .c 3, .c 13, .c 23, .c 3, .c 1301, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv2089], .c 821, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv21713], .c 3,
  .p pv3 [pv2,pv5,pv79,pv907], .c 13, .c 3, .c 11, .c 7, .c 3, .c 233, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv130279], .c 313, .c 3, .c 5, .p pv2 [pv2,pv3,pv41,pv61,pv191], .c 3,
  .p pv7 [pv2,pv5,pv7,pv19,pv431], .c 197, .c 3, .c 7, .p pv3 [pv2,pv3,pv53077], .c 3,
  .p pv2 [pv2,pv13,pv110237], .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 137,
]
private theorem h0349c27 : checkBlock 2865923 128 b0349c27 = true := by
  decide +kernel

private def b0349c28 : List Row := [
  .c 3, .c 103, .c 17, .c 3, .c 41, .p pv2 [pv2,pv3,pv13,pv19,pv967], .c 3, .c 11, .c 5, .c 3,
  .c 7, .c 13, .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv443,pv647], .c 7, .c 3, .c 17, .c 223,
  .c 3, .p pv5 [pv2,pv1117,pv1283], .c 5, .c 3, .c 31, .c 439, .c 3, .c 5, .c 11, .c 3, .c 7,
  .c 193, .c 3, .p pv5 [pv2,pv1433123], .c 1693, .c 3, .c 13, .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv23,pv31,pv67], .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv1361], .c 3,
  .p pv7 [pv2,pv5,pv11,pv71,pv367], .c 29, .c 3, .p pv2 [pv2,pv7,pv102367], .c 13, .c 3, .c 7,
  .c 5, .c 3, .p pv3 [pv2,pv179143], .c 31, .c 3, .c 5, .c 7, .c 3, .c 1613, .c 11, .c 3, .c 673,
  .p pv2 [pv2,pv3,pv238859], .c 3, .c 149, .c 5, .c 3, .c 17, .c 19, .c 3, .c 5, .c 67, .c 3,
  .c 13, .p pv2 [pv2,pv3,pv7,pv34123], .c 3, .c 43, .c 7, .c 3, .p pv5 [pv2,pv47,pv30493], .c 5,
  .c 3, .c 157, .c 41, .c 3, .c 5, .c 13, .c 3, .c 919, .p pv2 [pv2,pv3,pv477727], .c 3, .c 7,
  .c 11, .c 3, .c 109, .c 5, .c 3, .c 419, .c 7, .c 3, .c 5, .c 17, .c 3, .c 11, .c 229, .c 3,
  .c 19, .c 53, .c 3, .p pv2 [pv2,pv7,pv11,pv2659], .c 5, .c 3, .c 7, .c 131, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv7,pv19,pv449], .c 3, .c 17, .c 7, .c 3, .c 37, .p pv13 [pv2,pv3,pv983], .c 3,
  .c 41,
]
private theorem h0349c28 : checkBlock 2866179 128 b0349c28 = true := by
  decide +kernel

private def b0349c29 : List Row := [
  .c 5, .c 3, .p pv11 [pv2,pv17,pv84307], .p pv31 [pv2,pv3,pv5,pv23887], .c 3, .c 5, .c 29, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv53,pv4507], .c 3, .c 11, .c 307, .c 3, .p pv5 [pv2,pv149,pv9619], .c 5,
  .c 3, .p pv3 [pv2,pv11,pv65147], .c 113, .c 3, .c 5, .c 31, .c 3, .c 101, .c 47, .c 3, .c 13,
  .c 17, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv461,pv3109], .c 11, .c 3, .c 5, .c 7, .c 3, .c 19,
  .c 13, .c 3, .c 127, .p pv3 [pv2,pv3,pv163,pv977], .c 3, .c 11, .c 5, .c 3,
  .p pv17 [pv2,pv7,pv67,pv191], .c 1129, .c 3, .c 5, .p pv5 [pv2,pv3,pv23,pv577], .c 3, .c 389,
  .p pv5 [pv2,pv3,pv7,pv131,pv521], .c 3, .c 197, .c 7, .c 3, .p pv3 [pv2,pv13,pv43,pv641], .c 5,
  .c 3, .c 23, .c 727, .c 3, .c 5, .c 11, .c 3, .c 83, .c 61, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv11,pv13,pv257], .c 3, .p pv5 [pv2,pv23,pv101,pv617], .c 5, .c 3, .c 11, .c 7,
  .c 3, .c 5, .c 41, .c 3, .c 31, .p pv2 [pv2,pv3,pv477767], .c 3, .p pv5 [pv2,pv19,pv75437],
  .p pv13 [pv2,pv3,pv17,pv1171], .c 3, .p pv2 [pv2,pv7,pv37,pv2767], .c 5, .c 3, .c 7, .c 29,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv22751], .c 3, .c 317, .c 7, .c 3, .c 73, .c 1483, .c 3, .c 13,
  .c 5, .c 3, .c 37, .c 23, .c 3, .c 5, .p pv19 [pv2,pv3,pv13,pv2297], .c 3, .c 7, .c 19, .c 3,
  .p pv2 [pv2,pv11,pv130303], .c 13, .c 3, .c 79, .c 5, .c 3, .c 29, .c 43, .c 3, .c 5, .c 761,
  .c 3,
]
private theorem h0349c29 : checkBlock 2866435 128 b0349c29 = true := by
  decide +kernel

private def b0349c30 : List Row := [
  .p pv11 [pv2,pv5,pv89,pv3221], .c 17, .c 3, .c 23, .c 11, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv29,pv1901], .p pv59 [pv2,pv3,pv5,pv7,pv11,pv17,pv73], .c 3, .c 5, .c 7, .c 3,
  .c 11, .c 37, .c 3, .c 17, .c 67, .c 3, .c 269, .c 5, .c 3, .c 19, .p pv2 [pv2,pv3,pv5,pv47779],
  .c 3, .c 5, .c 13, .c 3, .c 59, .p pv5 [pv2,pv3,pv7,pv79], .c 3, .c 661, .c 7, .c 3, .c 733,
  .c 5, .c 3, .c 1453, .c 127, .c 3, .c 5, .c 19, .c 3, .p pv3 [pv2,pv5,pv7,pv20477], .c 73, .c 3,
  .c 7, .c 23, .c 3, .p pv3 [pv2,pv358349], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv53089], .c 3, .p pv2 [pv2,pv5,pv43,pv59,pv113], .c 1583, .c 3, .c 61,
  .p pv2 [pv2,pv3,pv31,pv15413], .c 3, .c 53, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv34129], .c 3, .p pv3 [pv2,pv5,pv71671], .c 7, .c 3,
  .p pv5 [pv2,pv17,pv84319], .c 31, .c 3, .c 11, .c 5, .c 3, .c 47, .c 607, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv477811], .c 3, .c 7, .p pv17 [pv2,pv3,pv19,pv6287], .c 3, .c 13, .c 557, .c 3,
  .p pv2 [pv2,pv29,pv49429], .c 5, .c 3, .c 167, .c 19, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv28669], .c 13, .c 3, .p pv2 [pv2,pv7,pv47,pv4357], .c 71, .c 3, .c 7, .c 5,
  .c 3, .c 11, .p pv13 [pv2,pv3,pv5,pv7,pv3413], .c 3, .c 5, .c 7, .c 3, .c 17, .c 853, .c 3,
  .p pv3 [pv2,pv241,pv1487], .c 43, .c 3, .p pv7 [pv2,pv13,pv31,pv3557], .c 5,
]
private theorem h0349c30 : checkBlock 2866691 128 b0349c30 = true := by
  decide +kernel

private def b0349c31 : List Row := [
  .c 3, .c 491, .p pv29 [pv2,pv3,pv5,pv23,pv277], .c 3, .c 5, .c 89, .c 3,
  .p pv3 [pv2,pv5,pv35837], .c 11, .c 3, .c 19, .c 7, .c 3, .c 23, .c 5, .c 3, .c 1471, .c 13,
  .c 3, .c 5, .c 59, .c 3, .c 571, .c 199, .c 3, .c 7, .c 17, .c 3, .p pv2 [pv2,pv73,pv269], .c 5,
  .c 3, .p pv3 [pv2,pv44797], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv7027], .c 3,
  .p pv2 [pv2,pv5,pv13,pv11027], .p pv3 [pv2,pv3,pv53093], .c 3, .c 29, .c 11, .c 3, .c 13, .c 5,
  .c 3, .c 7, .c 787, .c 3, .c 5, .c 47, .c 3, .c 11, .c 7, .c 3, .c 773, .c 13, .c 3, .c 521,
  .c 5, .c 3, .c 83, .p pv7 [pv2,pv3,pv5,pv95569], .c 3, .c 5, .p pv2 [pv2,pv3,pv8849], .c 3,
  .c 7, .p pv2 [pv2,pv3,pv477847], .c 3, .c 101, .c 41, .c 3, .c 37, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv110273], .c 17, .c 3, .c 5, .p pv11 [pv2,pv3,pv11,pv43441], .c 3, .c 13,
  .c 577, .c 3, .c 11, .c 19, .c 3, .c 7, .c 5, .c 3, .c 173, .c 67, .c 3, .c 5, .c 7, .c 3,
  .c 47, .c 29, .c 3, .c 79, .c 113, .c 3, .c 139, .c 5, .c 3, .c 31, .c 11, .c 3, .c 5, .c 37,
  .c 3, .c 41, .c 251, .c 3, .c 241, .c 7, .c 3, .c 11, .c 5, .c 3, .c 13, .c 569, .c 3, .c 5,
  .c 43, .c 3, .c 29,
]
private theorem h0349c31 : checkBlock 2866947 128 b0349c31 = true := by
  decide +kernel

def rows0349 : List Row :=
  b0349c00 ++ b0349c01 ++ b0349c02 ++ b0349c03 ++ b0349c04 ++ b0349c05 ++ b0349c06 ++ b0349c07 ++
  b0349c08 ++ b0349c09 ++ b0349c10 ++ b0349c11 ++ b0349c12 ++ b0349c13 ++ b0349c14 ++ b0349c15 ++
  b0349c16 ++ b0349c17 ++ b0349c18 ++ b0349c19 ++ b0349c20 ++ b0349c21 ++ b0349c22 ++ b0349c23 ++
  b0349c24 ++ b0349c25 ++ b0349c26 ++ b0349c27 ++ b0349c28 ++ b0349c29 ++ b0349c30 ++ b0349c31

theorem checked0349 : checkBlock 2859011 4096 rows0349 = true :=
  checkBlock_append h0349c00 (
    checkBlock_append h0349c01 (
    checkBlock_append h0349c02 (
    checkBlock_append h0349c03 (
    checkBlock_append h0349c04 (
    checkBlock_append h0349c05 (
    checkBlock_append h0349c06 (
    checkBlock_append h0349c07 (
    checkBlock_append h0349c08 (
    checkBlock_append h0349c09 (
    checkBlock_append h0349c10 (
    checkBlock_append h0349c11 (
    checkBlock_append h0349c12 (
    checkBlock_append h0349c13 (
    checkBlock_append h0349c14 (
    checkBlock_append h0349c15 (
    checkBlock_append h0349c16 (
    checkBlock_append h0349c17 (
    checkBlock_append h0349c18 (
    checkBlock_append h0349c19 (
    checkBlock_append h0349c20 (
    checkBlock_append h0349c21 (
    checkBlock_append h0349c22 (
    checkBlock_append h0349c23 (
    checkBlock_append h0349c24 (
    checkBlock_append h0349c25 (
    checkBlock_append h0349c26 (
    checkBlock_append h0349c27 (
    checkBlock_append h0349c28 (
    checkBlock_append h0349c29 (
    checkBlock_append h0349c30 (
    h0349c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
