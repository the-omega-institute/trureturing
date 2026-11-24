/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0143
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0143.checked0143
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table018
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table025
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table026
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table032
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table043
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table064
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table118
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table119

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0143c00 : List Row := [
  .c 23, .c 3, .p pv5 [pv2,pv83,pv7057], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv10847], .c 3, .c 163, .c 19, .c 3, .c 17, .c 11, .c 3, .c 41, .c 5, .c 3,
  .c 7, .c 241, .c 3, .c 5, .c 89, .c 3, .c 11, .c 7, .c 3, .p pv2 [pv2,pv292879], .c 857, .c 3,
  .p pv2 [pv2,pv11,pv47,pv103], .c 5, .c 3, .p pv3 [pv2,pv23,pv6367], .c 37, .c 3, .c 5, .c 311,
  .c 3, .c 7, .c 107, .c 3, .c 13, .p pv2 [pv2,pv3,pv7,pv4649], .c 3, .p pv3 [pv2,pv31,pv1181],
  .c 5, .c 3, .c 19, .p pv17 [pv2,pv3,pv5,pv13,pv751], .c 3, .c 5, .c 821, .c 3, .c 29, .c 13,
  .c 3, .c 11, .p pv2 [pv2,pv3,pv19,pv43,pv239], .c 3, .c 7, .c 5, .c 3, .c 17,
  .p pv7 [pv2,pv3,pv5,pv7,pv797], .c 3, .c 5, .c 7, .c 3, .p pv11 [pv2,pv5,pv29,pv101], .c 563,
  .c 3, .c 353, .c 151, .c 3, .c 181, .c 5, .c 3, .p pv2 [pv2,pv7,pv53,pv1579], .c 11, .c 3, .c 5,
  .c 61, .c 3, .c 139, .p pv13 [pv2,pv3,pv7,pv11,pv317], .c 3, .p pv2 [pv2,pv292909], .c 7, .c 3,
  .c 11, .c 5, .c 3, .c 79, .c 13, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv7,pv8369], .c 47,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv251,pv389], .c 3, .c 19, .c 5, .c 3, .c 37, .c 7, .c 3, .c 5,
  .c 11, .c 3, .c 17, .c 673, .c 3, .c 113, .p pv2 [pv2,pv3,pv11,pv41,pv433], .c 3, .c 13, .c 5,
  .c 3, .c 7, .c 19, .c 3,
]
private theorem h0143c00 : checkBlock 1171459 128 b0143c00 = true := by
  decide +kernel

private def b0143c01 : List Row := [
  .c 5, .c 647, .c 3, .p pv3 [pv2,pv5,pv11,pv2663], .c 7, .c 3, .c 887, .c 13, .c 3, .c 1049,
  .c 5, .c 3, .c 41, .c 883, .c 3, .c 5, .p pv3 [pv2,pv3,pv2411], .c 3, .c 7, .c 11, .c 3, .c 47,
  .c 17, .c 3, .c 67, .c 5, .c 3, .c 31, .p pv2 [pv2,pv3,pv5,pv139,pv281], .c 3, .c 5, .c 53,
  .c 3, .c 13, .p pv3 [pv2,pv3,pv65099], .c 3, .c 19, .p pv2 [pv2,pv3,pv97649], .c 3, .c 7, .c 5,
  .c 3, .c 59, .p pv43 [pv2,pv3,pv5,pv7,pv31], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv17,pv61,pv113], .p pv2 [pv2,pv3,pv97651], .c 3, .c 239, .c 11, .c 3,
  .p pv5 [pv2,pv585911], .c 5, .c 3, .c 127, .c 31, .c 3, .c 5, .p pv2 [pv2,pv3,pv43,pv757], .c 3,
  .c 11, .c 787, .c 3, .p pv5 [pv2,pv13,pv3467], .c 7, .c 3, .c 463, .c 5, .c 3, .c 13, .c 17,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv195311], .c 3, .c 61, .c 23, .c 3, .c 7, .c 43, .c 3, .c 53, .c 5,
  .c 3, .c 431, .c 7, .c 3, .c 5, .c 67, .c 3, .c 19, .c 41, .c 3, .c 11, .c 139, .c 3, .c 179,
  .c 5, .c 3, .c 7, .p pv61 [pv2,pv3,pv5,pv19,pv257], .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv71,pv131],
  .c 3, .p pv2 [pv2,pv5,pv117193], .c 7, .c 3, .c 13, .c 19, .c 3, .c 419, .c 5, .c 3, .c 317,
  .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv127,pv769], .c 3, .c 7, .c 13, .c 3,
  .p pv5 [pv2,pv373,pv1571], .p pv17 [pv2,pv3,pv7,pv109],
]
private theorem h0143c01 : checkBlock 1171715 128 b0143c01 = true := by
  decide +kernel

private def b0143c02 : List Row := [
  .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv585989], .p pv2 [pv2,pv3,pv5,pv17,pv383], .c 3, .c 5,
  .c 277, .c 3, .p pv13 [pv2,pv5,pv233,pv503], .c 61, .c 3, .c 17, .p pv3 [pv2,pv3,pv65111], .c 3,
  .c 7, .c 5, .c 3, .p pv3 [pv2,pv43,pv3407], .c 23, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv58601], .p pv3 [pv2,pv3,pv229,pv853], .c 3, .p pv2 [pv2,pv41,pv14293],
  .p pv2 [pv2,pv3,pv11,pv13,pv683], .c 3, .c 269, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv195341], .c 3, .c 43, .c 19, .c 3, .c 23, .c 7, .c 3,
  .p pv5 [pv2,pv151,pv3881], .c 5, .c 3, .p pv2 [pv2,pv71,pv4127], .c 331, .c 3, .c 5, .c 109,
  .c 3, .p pv37 [pv2,pv5,pv7,pv13,pv23], .c 11, .c 3, .c 7, .c 193, .c 3, .c 13, .c 5, .c 3,
  .c 17, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv5009], .c 3, .p pv17 [pv2,pv5,pv19,pv31,pv199],
  .c 479, .c 3, .c 607, .c 13, .c 3, .c 37, .c 5, .c 3, .c 7, .c 433, .c 3, .c 5, .c 43, .c 3,
  .c 31, .c 7, .c 3, .p pv2 [pv2,pv586073], .c 11, .c 3, .c 59, .c 5, .c 3, .c 311, .c 73, .c 3,
  .c 5, .c 17, .c 3, .c 7, .c 167, .c 3, .c 257, .p pv3 [pv2,pv3,pv7,pv443], .c 3, .c 149, .c 5,
  .c 3, .c 643, .c 263, .c 3, .c 5, .c 13, .c 3, .c 17, .c 31, .c 3, .p pv5 [pv2,pv7,pv101,pv829],
  .c 29, .c 3, .c 7, .c 5, .c 3, .c 89, .c 547, .c 3, .c 5,
]
private theorem h0143c02 : checkBlock 1171971 128 b0143c02 = true := by
  decide +kernel

private def b0143c03 : List Row := [
  .c 7, .c 3, .c 41, .p pv23 [pv2,pv3,pv67], .c 3, .c 11, .c 587, .c 3, .c 19, .c 5, .c 3, .c 13,
  .c 229, .c 3, .c 5, .p pv5 [pv2,pv3,pv12211], .c 3, .p pv3 [pv2,pv5,pv58613], .c 571, .c 3,
  .c 29, .c 7, .c 3, .p pv3 [pv2,pv41,pv1787], .c 5, .c 3, .p pv11 [pv2,pv586139], .c 11, .c 3,
  .c 5, .c 23, .c 3, .c 349, .c 293, .c 3, .c 7, .c 67, .c 3, .c 11, .c 5, .c 3, .c 43, .c 7,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv211,pv463], .c 3, .c 47, .c 461, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv48847], .c 3, .c 23, .c 5, .c 3, .c 7, .c 397, .c 3, .c 5, .c 11, .c 3,
  .p pv13 [pv2,pv5,pv23447], .c 7, .c 3, .c 19, .c 61, .c 3, .c 383, .c 5, .c 3, .c 11, .c 17,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv19,pv857], .c 3, .c 7, .c 29, .c 3, .c 797, .c 31, .c 3,
  .p pv3 [pv2,pv13,pv11273], .c 5, .c 3, .c 107, .p pv7 [pv2,pv3,pv5,pv977], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv195401], .c 3, .p pv2 [pv2,pv5,pv117241], .c 11, .c 3,
  .p pv3 [pv2,pv7,pv2617], .c 37, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv293107], .c 13, .c 3,
  .c 5, .c 7, .c 3, .c 29, .p pv2 [pv2,pv3,pv195407], .c 3, .p pv5 [pv2,pv11,pv137,pv389], .c 103,
  .c 3, .c 73, .c 5, .c 3, .c 163, .p pv7 [pv2,pv3,pv5,pv19541], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv53,pv1229], .c 3, .c 19, .c 17, .c 3, .c 41, .c 7, .c 3,
]
private theorem h0143c03 : checkBlock 1172227 128 b0143c03 = true := by
  decide +kernel

private def b0143c04 : List Row := [
  .c 13, .c 5, .c 3, .c 1063, .p pv2 [pv2,pv3,pv5,pv11,pv17,pv19], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv1879], .c 3, .c 11, .p pv5 [pv2,pv3,pv21713], .c 3, .c 7, .c 13, .c 3,
  .c 31, .c 5, .c 3, .c 53, .c 7, .c 3, .c 5, .c 211, .c 3, .p pv2 [pv2,pv5,pv37,pv3169],
  .p pv2 [pv2,pv3,pv97711], .c 3, .p pv3 [pv2,pv97,pv1511], .p pv2 [pv2,pv3,pv65141], .c 3,
  .p pv7 [pv2,pv7,pv61,pv1373], .c 5, .c 3, .c 7, .c 601, .c 3, .c 5, .c 29, .c 3, .c 13, .c 7,
  .c 3, .c 11, .c 439, .c 3, .p pv2 [pv2,pv53,pv5531], .c 5, .c 3, .p pv2 [pv2,pv11,pv53299],
  .c 131, .c 3, .c 5, .c 13, .c 3, .c 7, .c 757, .c 3, .c 79, .c 73, .c 3, .c 47, .c 5, .c 3,
  .c 17, .c 11, .c 3, .c 5, .c 271, .c 3, .c 443, .c 19, .c 3, .c 691, .c 179, .c 3, .c 7, .c 5,
  .c 3, .c 13, .c 37, .c 3, .c 5, .c 7, .c 3, .c 727, .c 43, .c 3, .p pv3 [pv2,pv73291],
  .p pv2 [pv2,pv3,pv195443], .c 3, .p pv5 [pv2,pv457,pv1283], .c 5, .c 3, .c 613,
  .p pv13 [pv2,pv3,pv5,pv39089], .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv19,pv1543],
  .p pv2 [pv2,pv3,pv7,pv41,pv227], .c 3, .p pv5 [pv2,pv709,pv827], .c 7, .c 3, .c 1069, .c 5,
  .c 3, .c 11, .c 23, .c 3, .c 5, .c 71, .c 3, .c 17, .p pv5 [pv2,pv3,pv131,pv373], .c 3, .c 7,
  .c 983, .c 3, .c 41, .c 5, .c 3, .c 563, .c 7, .c 3, .c 5, .c 19,
]
private theorem h0143c04 : checkBlock 1172483 128 b0143c04 = true := by
  decide +kernel

private def b0143c05 : List Row := [
  .c 3, .c 197, .c 11, .c 3, .c 23, .p pv2 [pv2,pv3,pv97729], .c 3, .c 89, .c 5, .c 3, .c 7,
  .c 31, .c 3, .c 5, .c 173, .c 3, .c 521, .c 7, .c 3, .p pv3 [pv2,pv11,pv13327], .c 17, .c 3,
  .p pv5 [pv2,pv13,pv43,pv1049], .c 5, .c 3, .c 29, .c 47, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv17,pv5749], .c 3, .c 7, .p pv2 [pv2,pv3,pv59,pv3313], .c 3,
  .p pv5 [pv2,pv586403], .c 11, .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv29,pv73,pv277], .c 13,
  .c 3, .c 5, .c 97, .c 3, .c 11, .p pv5 [pv2,pv3,pv19,pv643], .c 3, .c 53, .c 23, .c 3, .c 7,
  .c 5, .c 3, .c 71, .c 19, .c 3, .c 5, .c 7, .c 3, .c 59, .c 37, .c 3, .p pv2 [pv2,pv586433],
  .c 1019, .c 3, .c 13, .c 5, .c 3, .c 293, .c 17, .c 3, .c 5, .c 41, .c 3, .c 73,
  .p pv2 [pv2,pv3,pv7,pv13963], .c 3, .c 11, .c 7, .c 3, .p pv5 [pv2,pv67,pv8753], .c 5, .c 3,
  .c 227, .c 43, .c 3, .c 5, .c 617, .c 3, .p pv3 [pv2,pv5,pv7,pv59,pv71], .c 251, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv41,pv149], .c 3, .p pv2 [pv2,pv17,pv47,pv367], .c 5, .c 3,
  .p pv2 [pv2,pv13,pv197,pv229], .c 7, .c 3, .c 5, .c 31, .c 3, .c 13,
  .p pv5 [pv2,pv3,pv11,pv1481], .c 3, .p pv2 [pv2,pv83,pv3533], .p pv3 [pv2,pv3,pv195493], .c 3,
  .c 11, .c 5, .c 3, .c 7, .c 967, .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv223,pv263], .c 7,
  .c 3, .c 179, .c 349, .c 3, .p pv3 [pv2,pv29,pv79],
]
private theorem h0143c05 : checkBlock 1172739 128 b0143c05 = true := by
  decide +kernel

private def b0143c06 : List Row := [
  .c 5, .c 3, .c 491, .p pv13 [pv2,pv3,pv5,pv17,pv23], .c 3, .c 5, .c 11, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv239,pv409], .c 3, .c 17, .c 353, .c 3, .c 23, .c 5, .c 3, .c 11, .c 1039,
  .c 3, .c 5, .c 73, .c 3, .c 19, .p pv2 [pv2,pv3,pv13,pv557], .c 3, .c 307, .c 53, .c 3, .c 7,
  .c 5, .c 3, .p pv2 [pv2,pv109,pv5381], .c 181, .c 3, .c 5, .c 7, .c 3, .c 31, .c 11, .c 3,
  .c 149, .c 19, .c 3, .c 43, .c 5, .c 3, .c 523, .c 61, .c 3, .c 5, .c 59, .c 3,
  .p pv2 [pv2,pv5,pv11731], .c 67, .c 3, .c 13, .c 7, .c 3, .c 173, .c 5, .c 3, .c 17,
  .p pv41 [pv2,pv3,pv5,pv13,pv47], .c 3, .c 5, .p pv3 [pv2,pv3,pv43,pv4547], .c 3, .c 137, .c 13,
  .c 3, .c 7, .c 11, .c 3, .c 953, .c 5, .c 3, .c 499, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv59,pv1657], .c 3, .c 11, .p pv5 [pv2,pv3,pv195527], .c 3, .c 47, .c 43, .c 3,
  .p pv2 [pv2,pv7,pv11,pv13,pv293], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv19553], .c 3, .c 5,
  .c 17, .c 3, .p pv13 [pv2,pv5,pv117319], .c 7, .c 3, .c 743, .p pv3 [pv2,pv3,pv13,pv89], .c 3,
  .c 223, .c 5, .c 3, .c 821, .c 13, .c 3, .c 5, .c 317, .c 3, .c 7, .p pv3 [pv2,pv3,pv65179],
  .c 3, .c 11, .c 79, .c 3, .c 37, .c 5, .c 3, .p pv11 [pv2,pv11,pv17,pv3137], .c 677, .c 3, .c 5,
  .c 193, .c 3,
]
private theorem h0143c06 : checkBlock 1172995 128 b0143c06 = true := by
  decide +kernel

private def b0143c07 : List Row := [
  .c 239, .c 23, .c 3, .c 31, .p pv2 [pv2,pv3,pv21727], .c 3, .c 7, .c 5, .c 3, .c 19, .c 11,
  .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv7333], .p pv2 [pv2,pv3,pv11,pv29,pv613], .c 3, .c 89,
  .c 13, .c 3, .c 11, .c 5, .c 3, .c 23, .p pv2 [pv2,pv3,pv5,pv3911], .c 3, .c 5, .c 19, .c 3,
  .c 29, .c 191, .c 3, .c 101, .c 7, .c 3, .c 17, .c 5, .c 3, .c 73, .c 607, .c 3, .c 5, .c 11,
  .c 3, .c 13, .p pv3 [pv2,pv3,pv167,pv1171], .c 3, .c 7, .p pv13 [pv2,pv3,pv11,pv2963], .c 3,
  .c 127, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 13, .c 3, .c 67, .p pv2 [pv2,pv3,pv277,pv353],
  .c 3, .c 977, .c 41, .c 3, .c 19, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv61,pv229], .c 3, .p pv7 [pv2,pv5,pv5867], .c 7, .c 3,
  .p pv5 [pv2,pv13,pv45131], .c 97, .c 3, .c 587, .c 5, .c 3, .c 13, .c 19, .c 3, .c 5, .c 29,
  .c 3, .c 7, .p pv5 [pv2,pv3,pv13,pv3761], .c 3, .c 23, .p pv3 [pv2,pv3,pv7,pv67,pv139], .c 3,
  .c 31, .c 5, .c 3, .c 47, .c 59, .c 3, .c 5, .c 61, .c 3, .c 41, .p pv3 [pv2,pv3,pv257,pv761],
  .c 3, .c 1009, .c 11, .c 3, .c 7, .c 5, .c 3, .c 103, .p pv17 [pv2,pv3,pv5,pv7,pv11,pv127],
  .c 3, .c 5, .c 7, .c 3, .c 11, .c 17, .c 3, .c 13, .c 503, .c 3, .c 199, .c 5,
]
private theorem h0143c07 : checkBlock 1173251 128 b0143c07 = true := by
  decide +kernel

private def b0143c08 : List Row := [
  .c 3, .c 167, .p pv37 [pv2,pv3,pv5,pv13,pv17,pv59], .c 3, .c 5, .c 811, .c 3,
  .p pv3 [pv2,pv5,pv14669], .c 13, .c 3, .c 17, .c 7, .c 3, .c 733, .c 5, .c 3,
  .p pv2 [pv2,pv586769], .p pv7 [pv2,pv3,pv5,pv19559], .c 3, .c 5, .c 593, .c 3,
  .p pv7 [pv2,pv5,pv7,pv479], .p pv5 [pv2,pv3,pv23,pv1063], .c 3, .c 7, .c 71, .c 3, .c 919, .c 5,
  .c 3, .c 59, .c 7, .c 3, .c 5, .c 139, .c 3, .p pv2 [pv2,pv5,pv58679],
  .p pv3 [pv2,pv3,pv103,pv211], .c 3, .p pv2 [pv2,pv586793], .p pv2 [pv2,pv3,pv13,pv7523], .c 3,
  .p pv3 [pv2,pv7,pv19,pv1103], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 127, .c 3, .c 19, .c 7,
  .c 3, .p pv3 [pv2,pv73351], .c 419, .c 3, .c 11, .c 5, .c 3, .c 17,
  .p pv7 [pv2,pv3,pv5,pv19,pv29,pv71], .c 3, .c 5, .c 47, .c 3, .c 7, .c 89, .c 3, .c 269, .c 19,
  .c 3, .c 13, .c 5, .c 3, .c 29, .c 307, .c 3, .c 5, .c 11, .c 3, .c 641, .c 149, .c 3, .c 37,
  .c 13, .c 3, .c 7, .c 5, .c 3, .c 11, .c 31, .c 3, .c 5, .c 7, .c 3, .c 61, .c 79, .c 3, .c 41,
  .p pv29 [pv2,pv3,pv32603], .c 3, .c 23, .c 5, .c 3, .c 257, .c 101, .c 3, .c 5, .c 401, .c 3,
  .c 13, .c 11, .c 3, .c 281, .c 7, .c 3, .p pv5 [pv2,pv586871], .c 5, .c 3,
  .p pv2 [pv2,pv17,pv41,pv421], .c 37, .c 3, .c 5, .c 13, .c 3, .c 839,
]
private theorem h0143c08 : checkBlock 1173507 128 b0143c08 = true := by
  decide +kernel

private def b0143c09 : List Row := [
  .c 19, .c 3, .c 7, .c 263, .c 3, .c 67, .c 5, .c 3, .p pv2 [pv2,pv47,pv12487], .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv83,pv2357], .c 3, .c 53, .c 211, .c 3, .c 97, .c 11, .c 3,
  .p pv2 [pv2,pv7,pv83843], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv11,pv3557], .c 3, .c 5,
  .c 227, .c 3, .c 11, .c 7, .c 3, .p pv2 [pv2,pv193,pv3041], .p pv2 [pv2,pv3,pv23,pv4253], .c 3,
  .c 17, .c 5, .c 3, .c 19, .p pv13 [pv2,pv3,pv5,pv67,pv73], .c 3, .c 5, .c 569, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv3623], .c 3, .c 43, .c 809, .c 3, .c 433, .c 5, .c 3, .c 83, .c 41, .c 3,
  .c 5, .c 19, .c 3, .p pv3 [pv2,pv5,pv29347], .p pv2 [pv2,pv3,pv179,pv1093], .c 3, .c 11, .c 157,
  .c 3, .c 7, .c 5, .c 3, .c 37, .c 17, .c 3, .c 5, .c 7, .c 3, .c 241, .c 13, .c 3,
  .p pv2 [pv2,pv269,pv1091], .c 47, .c 3, .c 59, .c 5, .c 3, .c 397, .c 11, .c 3, .c 5,
  .p pv23 [pv2,pv3,pv37,pv661], .c 3, .p pv2 [pv2,pv5,pv79,pv743], .c 23, .c 3,
  .p pv2 [pv2,pv586973], .c 7, .c 3, .c 11, .c 5, .c 3, .p pv13 [pv2,pv586979],
  .p pv7 [pv2,pv3,pv5,pv1087], .c 3, .c 5, .c 1051, .c 3, .c 149, .c 37, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv13,pv29,pv173], .c 3, .p pv5 [pv2,pv59,pv9949], .c 5, .c 3, .c 23, .c 7, .c 3,
  .c 5, .c 11, .c 3, .c 31, .c 17, .c 3, .c 29, .c 691, .c 3, .c 47, .c 5, .c 3,
]
private theorem h0143c09 : checkBlock 1173763 128 b0143c09 = true := by
  decide +kernel

private def b0143c10 : List Row := [
  .c 7, .p pv41 [pv2,pv3,pv5,pv17,pv1151], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv27953], .c 3,
  .p pv47 [pv2,pv5,pv11,pv13,pv821], .c 7, .c 3, .c 17, .c 109, .c 3, .c 13, .c 5, .c 3,
  .p pv3 [pv2,pv19,pv1931], .c 293, .c 3, .c 5, .c 331, .c 3, .c 7, .c 11, .c 3, .c 19, .c 13,
  .c 3, .p pv3 [pv2,pv43,pv3413], .c 5, .c 3, .p pv7 [pv2,pv353,pv1663], .c 23, .c 3, .c 5,
  .c 233, .c 3, .p pv2 [pv2,pv5,pv137,pv857], .p pv2 [pv2,pv3,pv97841], .c 3, .c 103,
  .p pv2 [pv2,pv3,pv79,pv2477], .c 3, .c 7, .c 5, .c 3, .c 53, .c 107, .c 3, .c 5, .c 7, .c 3,
  .c 13, .c 29, .c 3, .c 23, .c 11, .c 3, .c 139, .c 5, .c 3, .c 17,
  .p pv7 [pv2,pv3,pv5,pv11,pv593], .c 3, .c 5, .c 13, .c 3, .c 11, .c 131, .c 3, .c 487, .c 7,
  .c 3, .p pv5 [pv2,pv11,pv19,pv53], .c 5, .c 3, .c 421, .p pv2 [pv2,pv3,pv5,pv39139], .c 3, .c 5,
  .c 79, .c 3, .c 19, .c 113, .c 3, .c 7, .c 61, .c 3, .p pv3 [pv2,pv73387], .c 5, .c 3, .c 13,
  .c 7, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv29,pv4049], .p pv2 [pv2,pv3,pv13,pv193], .c 3,
  .c 11, .c 19, .c 3, .c 761, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv4349], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv1997], .c 3, .c 17, .c 7, .c 3, .p pv5 [pv2,pv587123], .c 31, .c 3,
  .c 859, .c 5, .c 3, .p pv7 [pv2,pv17,pv34537], .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv89,pv733],
  .c 3, .c 7, .p pv5 [pv2,pv3,pv11,pv139],
]
private theorem h0143c10 : checkBlock 1174019 128 b0143c10 = true := by
  decide +kernel

private def b0143c11 : List Row := [
  .c 3, .c 13, .c 911, .c 3, .c 11, .c 5, .c 3, .c 359, .c 631, .c 3, .c 5, .c 29, .c 3,
  .p pv2 [pv2,pv5,pv11743], .c 13, .c 3, .p pv2 [pv2,pv7,pv37,pv2267], .c 17, .c 3, .c 7, .c 5,
  .c 3, .p pv11 [pv2,pv223,pv2633], .c 53, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv43,pv2731],
  .c 19, .c 3, .p pv5 [pv2,pv59,pv311], .p pv3 [pv2,pv3,pv11,pv659], .c 3, .c 17, .c 5, .c 3,
  .c 11, .c 73, .c 3, .c 5, .c 23, .c 3, .p pv3 [pv2,pv5,pv11,pv17,pv157], .c 41, .c 3, .c 83,
  .c 7, .c 3, .c 31, .c 5, .c 3, .c 97, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv195731], .c 3,
  .c 389, .c 11, .c 3, .c 7, .p pv3 [pv2,pv3,pv195733], .c 3, .c 23, .c 5, .c 3, .c 19, .c 7,
  .c 3, .c 5, .c 37, .c 3, .c 823, .p pv17 [pv2,pv3,pv195737], .c 3, .c 53, .c 251, .c 3, .c 13,
  .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv9787], .c 3, .c 5, .c 19, .c 3,
  .p pv2 [pv2,pv5,pv83,pv283], .c 7, .c 3, .c 419, .c 11, .c 3, .p pv5 [pv2,pv17,pv34543], .c 5,
  .c 3, .p pv2 [pv2,pv293617], .c 29, .c 3, .c 5, .p pv2 [pv2,pv3,pv97,pv1009], .c 3, .c 7, .c 47,
  .c 3, .p pv5 [pv2,pv41,pv14323], .p pv17 [pv2,pv3,pv7,pv6991], .c 3, .c 79, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv199,pv227], .c 137, .c 3, .c 5, .p pv2 [pv2,pv3,pv195751], .c 3, .c 13,
  .c 17, .c 3, .c 157, .p pv17 [pv2,pv3,pv23,pv2837], .c 3, .c 7, .c 5, .c 3, .c 29,
]
private theorem h0143c11 : checkBlock 1174275 128 b0143c11 = true := by
  decide +kernel

private def b0143c12 : List Row := [
  .p pv3 [pv2,pv3,pv5,pv7,pv17,pv47], .c 3, .c 5, .c 7, .c 3, .c 23, .c 863, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv97879], .c 3, .c 71, .c 5, .c 3, .c 31, .c 19, .c 3, .c 5, .c 149, .c 3,
  .p pv2 [pv2,pv5,pv73,pv1609], .c 97, .c 3, .c 47, .c 7, .c 3, .p pv5 [pv2,pv307,pv1913], .c 5,
  .c 3, .c 13, .c 11, .c 3, .c 5, .c 661, .c 3, .p pv3 [pv2,pv5,pv7,pv839],
  .p pv11 [pv2,pv3,pv11,pv13,pv37], .c 3, .c 7, .c 41, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv19,pv30911], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv65257], .c 3, .c 43, .c 23, .c 3,
  .c 19, .c 37, .c 3, .c 73, .c 5, .c 3, .c 7, .c 79, .c 3, .c 5, .c 11, .c 3, .c 383, .c 7, .c 3,
  .c 13, .p pv2 [pv2,pv3,pv11,pv809], .c 3, .p pv3 [pv2,pv73417], .c 5, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv5,pv13,pv251], .c 3, .c 5, .p pv5 [pv2,pv3,pv195781], .c 3, .c 7, .c 13,
  .c 3, .c 199, .c 83, .c 3, .c 29, .c 5, .c 3, .p pv2 [pv2,pv293677], .c 67, .c 3, .c 5, .c 17,
  .c 3, .p pv3 [pv2,pv5,pv3671], .c 11, .c 3, .p pv5 [pv2,pv7,pv11987], .c 433, .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv61,pv9629], .c 163, .c 3, .c 5, .c 7, .c 3, .c 17, .c 107, .c 3, .c 277,
  .p pv11 [pv2,pv3,pv13,pv15061], .c 3, .p pv2 [pv2,pv587381], .c 5, .c 3,
  .p pv11 [pv2,pv7,pv17,pv617], .c 13, .c 3, .c 5, .c 179, .c 3, .p pv2 [pv2,pv5,pv151,pv389],
  .p pv11 [pv2,pv3,pv7,pv83,pv337], .c 3,
]
private theorem h0143c12 : checkBlock 1174531 128 b0143c12 = true := by
  decide +kernel

private def b0143c13 : List Row := [
  .c 37, .c 7, .c 3, .p pv3 [pv2,pv146849], .c 5, .c 3, .c 61, .p pv41 [pv2,pv3,pv5,pv11,pv89],
  .c 3, .c 5, .c 31, .c 3, .c 11, .c 709, .c 3, .c 7, .c 17, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv139,pv2113], .c 7, .c 3, .c 5, .c 71, .c 3, .c 191, .c 173, .c 3,
  .p pv5 [pv2,pv19,pv43,pv719], .c 13, .c 3, .c 17, .c 5, .c 3, .c 7, .c 37, .c 3, .c 5, .c 59,
  .c 3, .c 181, .c 7, .c 3, .c 11, .p pv29 [pv2,pv3,pv21757], .c 3, .p pv2 [pv2,pv587441], .c 5,
  .c 3, .c 43, .p pv2 [pv2,pv3,pv5,pv39163], .c 3, .c 5, .p pv5 [pv2,pv3,pv41,pv199], .c 3, .c 7,
  .c 19, .c 3, .c 1019, .c 23, .c 3, .p pv3 [pv2,pv67,pv137], .c 5, .c 3, .p pv7 [pv2,pv587459],
  .c 11, .c 3, .c 5, .c 13, .c 3, .c 31, .c 101, .c 3, .c 41, .c 131, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv83,pv3539], .p pv3 [pv2,pv3,pv5,pv7,pv373], .c 3, .c 5, .c 7, .c 3, .c 97, .c 491,
  .c 3, .c 79, .p pv17 [pv2,pv3,pv16319], .c 3, .p pv2 [pv2,pv17,pv37,pv467], .c 5, .c 3, .c 13,
  .c 563, .c 3, .c 5, .c 11, .c 3, .c 787, .c 29, .c 3, .c 659, .c 7, .c 3,
  .p pv2 [pv2,pv313,pv1877], .c 5, .c 3, .c 11, .c 421, .c 3, .c 5, .c 19, .c 3,
  .p pv3 [pv2,pv5,pv7,pv11,pv109], .c 17, .c 3, .c 7, .p pv2 [pv2,pv3,pv97919], .c 3, .c 449,
  .c 5, .c 3, .p pv13 [pv2,pv587519], .c 7,
]
private theorem h0143c13 : checkBlock 1174787 128 b0143c13 = true := by
  decide +kernel

private def b0143c14 : List Row := [
  .c 3, .c 5, .c 23, .c 3, .c 29, .c 11, .c 3, .c 13, .c 211, .c 3, .c 53, .c 5, .c 3, .c 7,
  .p pv17 [pv2,pv3,pv5,pv13,pv23,pv131], .c 3, .c 5, .p pv17 [pv2,pv3,pv7,pv4663], .c 3, .c 73,
  .c 7, .c 3, .c 113, .c 461, .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv587549], .c 41, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv139,pv1409], .c 3, .c 7, .c 67, .c 3, .c 31, .c 11, .c 3,
  .p pv2 [pv2,pv13,pv45197], .c 5, .c 3, .c 109, .c 19, .c 3, .c 5, .c 353, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv17,pv41,pv281], .c 3, .c 43, .p pv7 [pv2,pv3,pv13,pv31], .c 3, .c 7, .c 5,
  .c 3, .c 17, .c 13, .c 3, .c 5, .c 7, .c 3, .c 1021, .p pv5 [pv2,pv3,pv97931], .c 3, .c 193,
  .c 31, .c 3, .c 41, .c 5, .c 3, .c 173, .p pv43 [pv2,pv3,pv5,pv43,pv911], .c 3, .c 5, .c 83,
  .c 3, .c 131, .c 439, .c 3, .c 11, .c 7, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv11,pv53419],
  .c 59, .c 3, .c 5, .c 17, .c 3, .c 23, .c 43, .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv587621],
  .c 5, .c 3, .p pv3 [pv2,pv73453], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv5441], .c 3, .c 17, .c 71,
  .c 3, .p pv2 [pv2,pv587633], .c 311, .c 3, .c 11, .c 5, .c 3, .c 7, .c 509, .c 3, .c 5, .c 61,
  .c 3, .c 13, .c 7, .c 3, .p pv3 [pv2,pv4591],
]
private theorem h0143c14 : checkBlock 1175043 128 b0143c14 = true := by
  decide +kernel

private def b0143c15 : List Row := [
  .c 283, .c 3, .c 31, .c 5, .c 3, .c 941, .c 277, .c 3, .c 5, .c 11, .c 3, .c 7, .c 23, .c 3,
  .c 271, .c 17, .c 3, .c 103, .c 5, .c 3, .c 11, .c 29, .c 3, .c 5, .c 41, .c 3,
  .p pv7 [pv2,pv5,pv11,pv2137], .p pv23 [pv2,pv3,pv48973], .c 3, .c 241, .c 19, .c 3, .c 7, .c 5,
  .c 3, .c 13, .p pv7 [pv2,pv3,pv5,pv7,pv29,pv193], .c 3, .c 5, .c 7, .c 3, .c 53, .c 11, .c 3,
  .p pv2 [pv2,pv587693], .p pv2 [pv2,pv3,pv41,pv2389], .c 3, .c 163, .c 5, .c 3, .c 29, .c 919,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv227,pv863], .c 3, .p pv2 [pv2,pv5,pv117541],
  .p pv2 [pv2,pv3,pv7,pv1999], .c 3, .p pv3 [pv2,pv11,pv19,pv37], .c 7, .c 3, .c 47, .c 5, .c 3,
  .c 41, .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv103,pv317], .c 3, .c 79, .c 683, .c 3, .c 7, .c 11,
  .c 3, .c 37, .c 5, .c 3, .c 157, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv409,pv479], .c 3, .c 11,
  .c 13, .c 3, .c 809, .p pv3 [pv2,pv3,pv195913], .c 3, .p pv2 [pv2,pv7,pv11,pv17,pv449], .c 5,
  .c 3, .c 7, .c 43, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv6997], .c 3, .c 367, .c 7, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv32653], .c 3, .c 167, .c 5, .c 3, .c 73, .p pv11 [pv2,pv3,pv5,pv31,pv79],
  .c 3, .c 5, .c 37, .c 3, .c 7, .c 17, .c 3, .c 11, .c 101, .c 3, .c 97, .c 5, .c 3, .c 19,
  .c 13, .c 3,
]
private theorem h0143c15 : checkBlock 1175299 128 b0143c15 = true := by
  decide +kernel

private def b0143c16 : List Row := [
  .c 5, .c 463, .c 3, .p pv3 [pv2,pv5,pv29389], .c 193, .c 3, .c 17, .p pv7 [pv2,pv3,pv19,pv1289],
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv587789], .c 11, .c 3, .c 5, .c 7, .c 3,
  .p pv19 [pv2,pv5,pv13,pv9043], .c 41, .c 3, .c 137, .c 23, .c 3, .c 11, .c 5, .c 3, .c 107,
  .c 47, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv157], .c 3, .c 757, .p pv5 [pv2,pv3,pv7,pv23,pv1217],
  .c 3, .p pv2 [pv2,pv587813], .c 7, .c 3, .c 227, .c 5, .c 3, .c 127, .c 239, .c 3, .c 5, .c 11,
  .c 3, .p pv2 [pv2,pv5,pv7,pv3359], .c 61, .c 3, .c 7, .p pv2 [pv2,pv3,pv11,pv47,pv379], .c 3,
  .c 19, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv97973], .c 3, .c 13,
  .p pv3 [pv2,pv3,pv19,pv10313], .c 3, .p pv5 [pv2,pv17,pv151,pv229], .c 29, .c 3, .c 59, .c 5,
  .c 3, .c 7, .c 19, .c 3, .c 5, .c 13, .c 3, .p pv11 [pv2,pv5,pv117571], .c 7, .c 3,
  .p pv2 [pv2,pv41,pv67,pv107], .c 163, .c 3, .p pv2 [pv2,pv443,pv1327], .c 5, .c 3,
  .p pv3 [pv2,pv73483], .c 673, .c 3, .c 5, .c 17, .c 3, .c 7, .p pv3 [pv2,pv3,pv21773], .c 3,
  .c 29, .c 37, .c 3, .c 317, .c 5, .c 3, .c 13, .c 587, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv127,pv1543], .c 3, .c 17, .c 157, .c 3, .c 19, .c 11, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv17,pv17291], .p pv3 [pv2,pv3,pv5,pv7,pv11,pv509], .c 3, .c 5, .c 7, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv195967], .c 3, .p pv5 [pv2,pv23,pv25561], .c 293,
]
private theorem h0143c16 : checkBlock 1175555 128 b0143c16 = true := by
  decide +kernel

private def b0143c17 : List Row := [
  .c 3, .p pv2 [pv2,pv11,pv26723], .c 5, .c 3, .p pv2 [pv2,pv7,pv83987],
  .p pv37 [pv2,pv3,pv5,pv19597], .c 3, .c 5, .c 557, .c 3, .c 71, .p pv5 [pv2,pv3,pv7,pv2333],
  .c 3, .c 13, .c 7, .c 3, .c 353, .c 5, .c 3, .p pv3 [pv2,pv103,pv1427], .c 179, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv17,pv131], .c 3, .c 31, .c 13, .c 3, .c 7, .c 271, .c 3, .c 17, .c 5,
  .c 3, .c 223, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv65327], .c 3, .c 19, .c 47, .c 3, .c 37,
  .p pv2 [pv2,pv3,pv23,pv8521], .c 3, .c 211, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 67, .c 3,
  .c 23, .c 7, .c 3, .p pv5 [pv2,pv577,pv1019], .c 19, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv587969], .c 13, .c 3, .c 5, .c 389, .c 3, .c 7, .p pv29 [pv2,pv3,pv24499], .c 3,
  .c 73, .p pv3 [pv2,pv3,pv7,pv17,pv61], .c 3, .p pv2 [pv2,pv41,pv14341], .c 5, .c 3,
  .p pv3 [pv2,pv36749], .c 37, .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv13,pv4523], .c 347,
  .c 3, .c 47, .p pv2 [pv2,pv3,pv11,pv59,pv151], .c 3, .c 7, .c 5, .c 3, .c 11, .c 109, .c 3,
  .c 5, .c 7, .c 3, .c 461, .c 23, .c 3, .c 53, .c 13, .c 3, .p pv5 [pv2,pv588011], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv97,pv433], .p pv3 [pv2,pv3,pv5,pv73,pv179], .c 3, .c 5, .c 29, .c 3,
  .p pv3 [pv2,pv5,pv29401], .c 11, .c 3, .c 31, .c 7, .c 3, .c 653, .c 5, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv5,pv17,pv1153], .c 3, .c 5,
]
private theorem h0143c17 : checkBlock 1175811 128 b0143c17 = true := by
  decide +kernel

private def b0143c18 : List Row := [
  .c 823, .c 3, .c 13, .c 79, .c 3, .c 7, .c 139, .c 3, .p pv5 [pv2,pv23,pv37,pv691], .c 5, .c 3,
  .p pv3 [pv2,pv147011], .c 7, .c 3, .c 5, .c 13, .c 3, .c 911, .c 73, .c 3, .c 563, .c 11, .c 3,
  .p pv3 [pv2,pv7,pv10501], .c 5, .c 3, .c 7, .p pv19 [pv2,pv3,pv5,pv11], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv41,pv683], .c 3, .c 11, .c 7, .c 3, .p pv3 [pv2,pv13,pv43,pv263], .c 151,
  .c 3, .c 499, .c 5, .c 3, .c 13, .c 23, .c 3, .c 5, .c 19, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv13,pv17,pv887], .c 3, .c 41, .c 743, .c 3, .p pv2 [pv2,pv294043], .c 5, .c 3,
  .c 17, .c 167, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv71,pv251], .c 3, .p pv7 [pv2,pv5,pv117619],
  .c 37, .c 3, .c 11, .c 431, .c 3, .c 7, .c 5, .c 3, .c 179, .c 29, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv23,pv2557], .p pv3 [pv2,pv3,pv43,pv47,pv97], .c 3, .c 13, .c 53, .c 3, .c 19,
  .c 5, .c 3, .p pv7 [pv2,pv7,pv84017], .c 11, .c 3, .c 5, .c 17, .c 3, .c 107, .c 13, .c 3,
  .c 71, .c 7, .c 3, .c 11, .c 5, .c 3, .c 29, .c 19, .c 3, .c 5, .p pv2 [pv2,pv3,pv83,pv1181],
  .c 3, .c 17, .c 59, .c 3, .c 7, .c 23, .c 3, .p pv2 [pv2,pv13,pv22621], .c 5, .c 3, .c 509,
  .c 7, .c 3, .c 5, .c 11, .c 3, .c 397, .c 89, .c 3, .c 991, .c 67, .c 3,
]
private theorem h0143c18 : checkBlock 1176067 128 b0143c18 = true := by
  decide +kernel

private def b0143c19 : List Row := [
  .p pv2 [pv2,pv7,pv73,pv1151], .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 269, .c 3, .c 37, .c 7,
  .c 3, .c 19, .c 17, .c 3, .p pv3 [pv2,pv36761], .c 5, .c 3, .c 83, .p pv11 [pv2,pv3,pv5,pv9803],
  .c 3, .c 5, .p pv3 [pv2,pv3,pv17,pv19,pv607], .c 3, .c 7, .c 11, .c 3, .p pv3 [pv2,pv147047],
  .c 907, .c 3, .c 13, .c 5, .c 3, .c 79, .p pv37 [pv2,pv3,pv5,pv4357], .c 3, .c 5,
  .p pv19 [pv2,pv3,pv13,pv7541], .c 3, .c 59, .p pv2 [pv2,pv3,pv89,pv2203], .c 3,
  .p pv5 [pv2,pv7,pv11,pv7639], .c 13, .c 3, .c 7, .c 5, .c 3, .c 31,
  .p pv2 [pv2,pv3,pv5,pv7,pv2801], .c 3, .c 5, .c 7, .c 3, .c 283, .p pv5 [pv2,pv3,pv24509], .c 3,
  .c 43, .c 11, .c 3, .c 29, .c 5, .c 3, .p pv3 [pv2,pv7,pv13,pv101], .c 17, .c 3, .c 5, .c 47,
  .c 3, .c 11, .p pv3 [pv2,pv3,pv7,pv9337], .c 3, .c 337, .c 7, .c 3, .c 23, .c 5, .c 3, .c 349,
  .c 31, .c 3, .c 5, .c 13, .c 3, .c 89, .c 821, .c 3, .c 7, .c 19, .c 3, .c 577, .c 5, .c 3,
  .p pv2 [pv2,pv294127], .c 7, .c 3, .c 5, .c 503, .c 3, .p pv3 [pv2,pv5,pv67,pv439], .c 43, .c 3,
  .c 11, .p pv11 [pv2,pv3,pv127,pv193], .c 3, .p pv2 [pv2,pv7,pv42019], .c 5, .c 3, .c 7, .c 71,
  .c 3, .c 5, .c 53, .c 3, .c 47, .c 7, .c 3, .p pv2 [pv2,pv19,pv113,pv137], .c 29, .c 3, .c 37,
  .c 5, .c 3, .c 103, .c 11, .c 3, .c 5, .c 41,
]
private theorem h0143c19 : checkBlock 1176323 128 b0143c19 = true := by
  decide +kernel

private def b0143c20 : List Row := [
  .c 3, .c 7, .p pv3 [pv2,pv3,pv11,pv17827], .c 3, .c 17, .p pv2 [pv2,pv3,pv7,pv23,pv29], .c 3,
  .c 11, .c 5, .c 3, .p pv7 [pv2,pv47,pv12517], .p pv11 [pv2,pv3,pv5,pv37,pv53], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv269], .c 3, .c 23, .c 19, .c 3, .c 13, .c 617, .c 3, .c 7, .c 5, .c 3, .c 61,
  .p pv41 [pv2,pv3,pv5,pv7,pv13,pv431], .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv3677], .c 13,
  .c 3, .p pv5 [pv2,pv29,pv20287], .c 1061, .c 3, .c 53, .c 5, .c 3, .c 11, .c 857, .c 3, .c 5,
  .c 31, .c 3, .p pv11 [pv2,pv5,pv11,pv19,pv563], .p pv19 [pv2,pv3,pv7,pv17,pv103], .c 3, .c 347,
  .c 7, .c 3, .c 71, .c 5, .c 3, .c 17, .c 83, .c 3, .c 5, .c 163, .c 3,
  .p pv3 [pv2,pv5,pv7,pv41], .c 11, .c 3, .c 7, .p pv17 [pv2,pv3,pv13,pv19,pv397], .c 3,
  .p pv3 [pv2,pv147089], .c 5, .c 3, .c 619, .c 7, .c 3, .c 5, .c 19, .c 3, .c 307, .c 29, .c 3,
  .p pv3 [pv2,pv11,pv3343], .c 47, .c 3, .c 151, .c 5, .c 3, .c 7, .c 61, .c 3, .c 5, .c 17, .c 3,
  .c 811, .c 7, .c 3, .p pv5 [pv2,pv588383], .c 11, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv588389], .c 43, .c 3, .c 5, .p pv37 [pv2,pv3,pv13,pv47,pv107], .c 3, .c 7,
  .p pv11 [pv2,pv3,pv49033], .c 3, .p pv2 [pv2,pv294199], .c 13, .c 3, .c 19, .c 5, .c 3, .c 683,
  .p pv3 [pv2,pv3,pv5,pv39227], .c 3, .c 5, .c 751, .c 3, .c 827, .c 41, .c 3,
  .p pv2 [pv2,pv7,pv84059], .c 449, .c 3, .c 7,
]
private theorem h0143c20 : checkBlock 1176579 128 b0143c20 = true := by
  decide +kernel

private def b0143c21 : List Row := [
  .c 5, .c 3, .c 967, .c 19, .c 3, .c 5, .c 7, .c 3, .c 13, .c 31, .c 3, .c 11, .c 17, .c 3,
  .c 79, .c 5, .c 3, .p pv2 [pv2,pv7,pv11,pv3821], .p pv19 [pv2,pv3,pv5,pv39229], .c 3, .c 5,
  .c 13, .c 3, .p pv3 [pv2,pv5,pv47,pv313], .c 233, .c 3, .c 23, .c 7, .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv19,pv30971], .c 11, .c 3, .c 5, .c 29, .c 3, .p pv7 [pv2,pv5,pv7,pv17,pv23,pv43],
  .c 139, .c 3, .c 7, .c 173, .c 3, .c 11, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv19,pv29,pv89], .c 3, .c 557, .p pv5 [pv2,pv3,pv13,pv79,pv191], .c 3,
  .p pv2 [pv2,pv31,pv41,pv463], .p pv2 [pv2,pv3,pv32693], .c 3, .c 43, .c 5, .c 3, .c 7, .c 17,
  .c 3, .c 5, .c 11, .c 3, .c 53, .c 7, .c 3, .c 31, .c 23, .c 3, .p pv5 [pv2,pv109,pv5399], .c 5,
  .c 3, .c 11, .c 59, .c 3, .c 5, .c 283, .c 3, .c 7, .c 719, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv7,pv31,pv113], .c 3, .c 727, .c 5, .c 3, .p pv2 [pv2,pv588509], .c 47, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv196171], .c 3, .c 19, .c 11, .c 3, .p pv2 [pv2,pv7,pv127,pv331], .c 31,
  .c 3, .c 7, .c 5, .c 3, .c 887, .c 443, .c 3, .c 5, .c 7, .c 3, .c 431, .c 17, .c 3,
  .p pv2 [pv2,pv11,pv53503], .c 19, .c 3, .p pv3 [pv2,pv13,pv5659], .c 5, .c 3, .c 487, .c 29,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv196181], .c 3,
]
private theorem h0143c21 : checkBlock 1176835 128 b0143c21 = true := by
  decide +kernel

private def b0143c22 : List Row := [
  .c 109, .p pv2 [pv2,pv3,pv7,pv173], .c 3, .c 17, .c 7, .c 3, .p pv5 [pv2,pv409,pv1439], .c 5,
  .c 3, .c 59, .c 13, .c 3, .c 5, .c 23, .c 3, .c 11, .c 67, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv16349], .c 3, .c 191, .c 5, .c 3, .c 29, .c 7, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv21799], .c 3, .c 41, .p pv7 [pv2,pv3,pv6131], .c 3, .p pv2 [pv2,pv294289],
  .p pv3 [pv2,pv3,pv196193], .c 3, .c 13, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv39239], .c 3,
  .c 5, .c 349, .c 3, .p pv2 [pv2,pv5,pv71,pv829], .c 7, .c 3, .c 11, .c 13, .c 3, .c 313, .c 5,
  .c 3, .c 17, .p pv19 [pv2,pv3,pv5,pv109], .c 3, .c 5, .p pv3 [pv2,pv3,pv196201], .c 3, .c 7,
  .c 1021, .c 3, .c 223, .p pv7 [pv2,pv3,pv7,pv9343], .c 3, .p pv5 [pv2,pv227,pv2593], .c 5, .c 3,
  .c 37, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv53,pv617], .c 3, .c 13,
  .p pv7 [pv2,pv3,pv11,pv17837], .c 3, .p pv5 [pv2,pv7,pv84089], .c 149, .c 3, .c 7, .c 5, .c 3,
  .c 19, .c 569, .c 3, .c 5, .c 7, .c 3, .c 73, .c 523, .c 3, .p pv2 [pv2,pv294319], .c 773, .c 3,
  .c 179, .c 5, .c 3, .c 53, .p pv2 [pv2,pv3,pv5,pv103,pv127], .c 3, .c 5, .c 11, .c 3, .c 17,
  .c 37, .c 3, .c 467, .c 7, .c 3, .c 29, .c 5, .c 3, .c 11, .c 107, .c 3, .c 5, .c 433, .c 3,
  .p pv2 [pv2,pv5,pv7,pv11,pv139], .c 643, .c 3, .c 7, .c 769, .c 3, .c 157, .c 5,
]
private theorem h0143c22 : checkBlock 1177091 128 b0143c22 = true := by
  decide +kernel

private def b0143c23 : List Row := [
  .c 3, .c 31, .c 7, .c 3, .c 5, .c 101, .c 3, .c 61, .c 11, .c 3, .c 331, .c 17, .c 3, .c 19,
  .c 5, .c 3, .c 7, .c 89, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv17,pv97], .c 3, .c 67, .c 7, .c 3,
  .c 13, .p pv3 [pv2,pv3,pv149,pv439], .c 3, .c 17, .c 5, .c 3, .c 463, .c 19, .c 3, .c 5, .c 73,
  .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv43,pv13691], .c 11, .c 3, .p pv3 [pv2,pv147179], .c 5,
  .c 3, .c 23, .c 251, .c 3, .c 5, .p pv5 [pv2,pv3,pv311,pv631], .c 3, .c 11,
  .p pv2 [pv2,pv3,pv32707], .c 3, .c 997, .p pv37 [pv2,pv3,pv29,pv67,pv101], .c 3, .c 7, .c 5,
  .c 3, .c 43, .c 17, .c 3, .c 5, .c 7, .c 3, .p pv11 [pv2,pv5,pv29437], .c 61, .c 3, .c 19,
  .p pv19 [pv2,pv3,pv13,pv17,pv37], .c 3, .c 193, .c 5, .c 3, .p pv2 [pv2,pv7,pv151,pv557], .c 13,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv19,pv313], .c 3, .c 409, .p pv5 [pv2,pv3,pv7,pv43,pv163],
  .c 3, .c 11, .c 7, .c 3, .c 503, .c 5, .c 3, .p pv3 [pv2,pv11,pv13381], .c 23, .c 3, .c 5,
  .c 421, .c 3, .p pv3 [pv2,pv5,pv7,pv13,pv647], .p pv3 [pv2,pv3,pv65419], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv98129], .c 3, .c 13, .c 5, .c 3, .c 89, .c 7, .c 3, .c 5, .c 293, .c 3,
  .p pv2 [pv2,pv5,pv117757], .c 17, .c 3, .c 23, .c 13, .c 3, .c 11, .c 5, .c 3, .c 7, .c 211,
  .c 3, .c 5, .c 31, .c 3, .c 19,
]
private theorem h0143c23 : checkBlock 1177347 128 b0143c23 = true := by
  decide +kernel

private def b0143c24 : List Row := [
  .c 7, .c 3, .c 17, .p pv7 [pv2,pv3,pv139,pv353], .c 3, .p pv2 [pv2,pv294403], .c 5, .c 3,
  .p pv2 [pv2,pv13,pv45293], .p pv17 [pv2,pv3,pv5,pv19,pv1033], .c 3, .c 5, .c 11, .c 3, .c 7,
  .c 659, .c 3, .p pv2 [pv2,pv37,pv73,pv109], .c 19, .c 3, .c 41, .c 5, .c 3, .c 11,
  .p pv17 [pv2,pv3,pv5,pv2617], .c 3, .c 5, .c 13, .c 3, .c 29, .c 223, .c 3,
  .p pv5 [pv2,pv7,pv61,pv197], .c 23, .c 3, .c 7, .c 5, .c 3, .c 47,
  .p pv11 [pv2,pv3,pv5,pv7,pv701], .c 3, .c 5, .c 7, .c 3, .c 547, .c 11, .c 3,
  .p pv3 [pv2,pv13,pv19,pv149], .c 59, .c 3, .c 367, .c 5, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv5,pv37,pv1061], .c 3, .c 5, .p pv5 [pv2,pv3,pv98143], .c 3, .c 31,
  .p pv2 [pv2,pv3,pv7,pv13,pv719], .c 3, .c 43, .c 7, .c 3, .p pv2 [pv2,pv79,pv3727], .c 5, .c 3,
  .p pv2 [pv2,pv23,pv25603], .p pv2 [pv2,pv3,pv5,pv727], .c 3, .c 5, .c 37, .c 3,
  .p pv7 [pv2,pv5,pv7,pv673], .c 19, .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv588881], .c 5, .c 3,
  .p pv3 [pv2,pv147221], .c 7, .c 3, .c 5, .c 17, .c 3, .c 11, .c 31, .c 3, .c 13, .c 137, .c 3,
  .c 67, .c 5, .c 3, .c 7, .p pv23 [pv2,pv3,pv5,pv13,pv151], .c 3, .c 5, .c 23, .c 3, .c 17, .c 7,
  .c 3, .c 59, .c 53, .c 3, .c 971, .c 5, .c 3, .c 19, .c 257, .c 3, .c 5, .c 439, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv196307], .c 3, .c 11, .c 61, .c 3, .c 23, .c 5, .c 3,
]
private theorem h0143c24 : checkBlock 1177603 128 b0143c24 = true := by
  decide +kernel

private def b0143c25 : List Row := [
  .p pv2 [pv2,pv11,pv37,pv1447], .c 479, .c 3, .c 5, .c 19, .c 3, .c 97,
  .p pv5 [pv2,pv3,pv53,pv463], .c 3, .p pv2 [pv2,pv7,pv23,pv31,pv59], .c 17, .c 3, .c 7, .c 5,
  .c 3, .c 41, .c 11, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv11779], .c 227, .c 3, .c 31,
  .c 491, .c 3, .c 11, .c 5, .c 3, .p pv7 [pv2,pv7,pv84137], .p pv7 [pv2,pv3,pv5,pv409], .c 3,
  .c 5, .c 67, .c 3, .c 733, .p pv2 [pv2,pv3,pv7,pv37,pv379], .c 3, .c 443, .c 7, .c 3, .c 13,
  .c 5, .c 3, .p pv2 [pv2,pv181,pv1627], .c 29, .c 3, .c 5, .c 11, .c 3, .c 47, .c 101, .c 3,
  .c 7, .c 13, .c 3, .c 571, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv196331], .c 3,
  .c 23, .c 853, .c 3, .p pv2 [pv2,pv294499], .c 179, .c 3, .p pv2 [pv2,pv7,pv84143], .c 5, .c 3,
  .c 7, .c 103, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv1753], .c 3, .c 13, .c 7, .c 3, .c 1049, .c 331,
  .c 3, .p pv3 [pv2,pv17,pv61,pv71], .c 5, .c 3, .p pv7 [pv2,pv19,pv29,pv1069],
  .p pv11 [pv2,pv3,pv5,pv9817], .c 3, .c 5, .c 13, .c 3, .c 7, .c 41, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv7,pv4007], .c 3, .c 137, .c 5, .c 3, .p pv2 [pv2,pv311,pv947], .c 43, .c 3,
  .c 5, .c 631, .c 3, .c 277, .c 17, .c 3, .p pv11 [pv2,pv7,pv13,pv6473], .c 11, .c 3, .c 7, .c 5,
  .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv7,pv11,pv17], .c 3, .c 5, .c 7, .c 3, .c 11,
  .p pv5 [pv2,pv3,pv13,pv59],
]
private theorem h0143c25 : checkBlock 1177859 128 b0143c25 = true := by
  decide +kernel

private def b0143c26 : List Row := [
  .c 3, .c 17, .c 1013, .c 3, .p pv2 [pv2,pv11,pv53551], .c 5, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv5,pv173,pv227], .c 3, .c 5, .c 53, .c 3, .p pv3 [pv2,pv5,pv58907], .c 149,
  .c 3, .c 73, .c 7, .c 3, .c 293, .c 5, .c 3, .p pv11 [pv2,pv641,pv919],
  .p pv7 [pv2,pv3,pv5,pv4909], .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv17851], .c 3, .c 19,
  .p pv2 [pv2,pv3,pv10909], .c 3, .c 7, .c 127, .c 3, .c 29, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv26777], .c 7, .c 3, .c 5, .p pv23 [pv2,pv3,pv47,pv2089], .c 3,
  .p pv11 [pv2,pv5,pv43,pv137], .c 13, .c 3, .p pv5 [pv2,pv79,pv7457], .c 19, .c 3,
  .p pv2 [pv2,pv7,pv29,pv1451], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv1039],
  .c 3, .p pv13 [pv2,pv5,pv59,pv1997], .c 7, .c 3, .p pv2 [pv2,pv17,pv17327],
  .p pv29 [pv2,pv3,pv359,pv547], .c 3, .c 11, .c 5, .c 3, .c 241, .c 113, .c 3, .c 5, .c 197,
  .c 3, .c 7, .p pv3 [pv2,pv3,pv67,pv977], .c 3, .c 23, .p pv2 [pv2,pv3,pv7,pv13,pv83], .c 3,
  .p pv3 [pv2,pv36821], .c 5, .c 3, .c 31, .c 13, .c 3, .c 5, .c 11, .c 3, .c 593, .c 73, .c 3,
  .p pv3 [pv2,pv7,pv53,pv397], .c 29, .c 3, .c 7, .c 5, .c 3, .c 11, .c 379, .c 3, .c 5, .c 7,
  .c 3, .c 17, .c 19, .c 3, .c 163, .c 43, .c 3, .c 13, .c 5, .c 3, .c 37, .c 31, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv13,pv15107], .c 3, .c 83, .c 11, .c 3, .c 29, .c 7, .c 3,
  .p pv2 [pv2,pv589181], .c 5, .c 3, .p pv3 [pv2,pv4603],
]
private theorem h0143c26 : checkBlock 1178115 128 b0143c26 = true := by
  decide +kernel

private def b0143c27 : List Row := [
  .p pv2 [pv2,pv3,pv5,pv13093], .c 3, .c 5, .p pv5 [pv2,pv3,pv37,pv1327], .c 3, .c 41, .c 811,
  .c 3, .c 7, .c 17, .c 3, .p pv3 [pv2,pv147299], .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 59,
  .c 3, .c 13, .c 37, .c 3, .p pv3 [pv2,pv73651], .c 11, .c 3, .c 17, .c 5, .c 3, .c 7, .c 47,
  .c 3, .c 5, .c 13, .c 3, .c 11, .c 7, .c 3, .p pv5 [pv2,pv293,pv2011], .c 89, .c 3, .c 97, .c 5,
  .c 3, .c 61, .p pv13 [pv2,pv3,pv5,pv6547], .c 3, .c 5, .c 727, .c 3, .c 7, .c 29, .c 3, .c 113,
  .p pv3 [pv2,pv3,pv7,pv47,pv199], .c 3, .p pv2 [pv2,pv589241], .c 5, .c 3, .c 13, .c 17, .c 3,
  .c 5, .c 23, .c 3, .c 43, .c 263, .c 3, .c 11, .c 239, .c 3, .c 7, .c 5, .c 3, .c 167,
  .p pv13 [pv2,pv3,pv5,pv7,pv23,pv61], .c 3, .c 5, .c 7, .c 3, .c 29,
  .p pv5 [pv2,pv3,pv19,pv1723], .c 3, .p pv3 [pv2,pv179,pv823], .c 401, .c 3, .c 23, .c 5, .c 3,
  .p pv13 [pv2,pv7,pv859], .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv98213], .c 3, .c 37, .c 661, .c 3,
  .c 13, .c 7, .c 3, .c 11, .c 5, .c 3, .c 271, .c 61, .c 3, .c 5, .c 43, .c 3,
  .p pv7 [pv2,pv5,pv7,pv113,pv149], .c 13, .c 3, .c 7, .c 157, .c 3, .c 457, .c 5, .c 3,
  .p pv3 [pv2,pv19,pv3877], .c 7, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv31,pv1901],
  .p pv5 [pv2,pv3,pv65479], .c 3,
]
private theorem h0143c27 : checkBlock 1178371 128 b0143c27 = true := by
  decide +kernel

private def b0143c28 : List Row := [
  .c 17, .c 103, .c 3, .p pv3 [pv2,pv7,pv13,pv1619], .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv1637], .c 3, .c 5, .c 29, .c 3, .c 31, .c 7, .c 3, .c 677,
  .p pv3 [pv2,pv3,pv13,pv23,pv73], .c 3, .c 229, .c 5, .c 3, .p pv2 [pv2,pv41,pv7187], .c 13,
  .c 3, .c 5, .c 199, .c 3, .c 7, .c 11, .c 3, .c 127, .p pv13 [pv2,pv3,pv7,pv877], .c 3, .c 397,
  .c 5, .c 3, .p pv2 [pv2,pv589349], .p pv23 [pv2,pv3,pv5,pv3929], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv151,pv1301], .c 3, .p pv7 [pv2,pv5,pv13,pv9067], .c 31, .c 3,
  .p pv2 [pv2,pv7,pv11,pv43,pv89], .p pv3 [pv2,pv3,pv196453], .c 3, .c 7, .c 5, .c 3, .c 17,
  .c 67, .c 3, .c 5, .c 7, .c 3, .c 19, .p pv5 [pv2,pv3,pv71,pv2767], .c 3, .c 233, .c 11, .c 3,
  .p pv3 [pv2,pv9209], .c 5, .c 3, .c 43, .c 59, .c 3, .c 5, .p pv3 [pv2,pv3,pv83,pv263], .c 3,
  .c 11, .c 23, .c 3, .c 461, .c 7, .c 3, .c 37, .c 5, .c 3, .c 761, .c 41, .c 3, .c 5, .c 17,
  .c 3, .c 13, .p pv2 [pv2,pv3,pv43,pv1523], .c 3, .c 7, .p pv29 [pv2,pv3,pv49117], .c 3, .c 71,
  .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 13, .c 3, .c 17, .p pv7 [pv2,pv3,pv41,pv599], .c 3,
  .c 11, .c 541, .c 3, .p pv2 [pv2,pv7,pv23,pv523], .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv29,pv271], .c 3, .c 5, .c 37, .c 3, .c 953, .c 7, .c 3, .c 1063, .c 131,
  .c 3, .c 41, .c 5, .c 3, .c 13, .c 11,
]
private theorem h0143c28 : checkBlock 1178627 128 b0143c28 = true := by
  decide +kernel

private def b0143c29 : List Row := [
  .c 3, .c 5, .p pv3 [pv2,pv3,pv61,pv3221], .c 3, .c 7, .c 19, .c 3, .p pv3 [pv2,pv73681], .c 17,
  .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv29,pv10163], .c 23, .c 3, .c 5, .c 79, .c 3,
  .p pv3 [pv2,pv5,pv29473], .c 317, .c 3, .p pv5 [pv2,pv7,pv107,pv787], .c 113, .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv59,pv97,pv103], .c 127, .c 3, .c 5, .c 7, .c 3, .c 659,
  .p pv11 [pv2,pv3,pv49123], .c 3, .c 13, .p pv3 [pv2,pv3,pv11,pv17863], .c 3,
  .p pv2 [pv2,pv589481], .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv13,pv3023], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv12281], .c 3, .p pv2 [pv2,pv5,pv11,pv23,pv233], .c 13, .c 3, .c 239, .c 7,
  .c 3, .p pv3 [pv2,pv31,pv2377], .c 5, .c 3, .c 67, .c 17, .c 3, .c 5, .c 19, .c 3,
  .p pv7 [pv2,pv5,pv7,pv16843], .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv17,pv3853], .c 3, .c 31,
  .c 5, .c 3, .c 263, .c 7, .c 3, .c 5, .c 41, .c 3, .c 103, .c 191, .c 3,
  .p pv5 [pv2,pv11,pv53593], .c 23, .c 3, .c 29, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 709,
  .c 3, .c 313, .c 7, .c 3, .c 919, .c 11, .c 3, .c 19, .c 5, .c 3, .c 47, .c 53, .c 3, .c 5,
  .c 71, .c 3, .c 7, .c 17, .c 3, .c 1069, .p pv2 [pv2,pv3,pv7,pv4679], .c 3, .c 13, .c 5, .c 3,
  .c 41, .c 19, .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv5039], .c 3, .c 131, .c 67, .c 3, .c 17,
]
private theorem h0143c29 : checkBlock 1178883 128 b0143c29 = true := by
  decide +kernel

private def b0143c30 : List Row := [
  .c 13, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv294787], .p pv19 [pv2,pv3,pv5,pv7,pv1123], .c 3,
  .c 5, .c 7, .c 3, .c 89, .c 337, .c 3, .c 11, .c 29, .c 3, .p pv2 [pv2,pv294793], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv11,pv13,pv19,pv31], .c 83, .c 3, .c 5, .c 23, .c 3, .c 13,
  .p pv5 [pv2,pv3,pv7,pv7019], .c 3, .c 19, .c 7, .c 3, .p pv2 [pv2,pv589601], .c 5, .c 3, .c 31,
  .c 11, .c 3, .c 5, .c 13, .c 3, .c 421, .p pv11 [pv2,pv3,pv11,pv17,pv1051], .c 3, .c 7, .c 97,
  .c 3, .c 11, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 103, .c 3, .p pv17 [pv2,pv5,pv53,pv89],
  .p pv2 [pv2,pv3,pv61,pv179], .c 3, .c 383, .p pv2 [pv2,pv3,pv196543], .c 3,
  .p pv5 [pv2,pv7,pv131,pv643], .c 5, .c 3, .c 7, .c 31, .c 3, .c 5, .c 11, .c 3,
  .p pv7 [pv2,pv5,pv14741], .c 7, .c 3, .p pv5 [pv2,pv589643], .p pv41 [pv2,pv3,pv11,pv1489],
  .c 3, .p pv3 [pv2,pv19,pv59,pv263], .c 5, .c 3, .c 11, .c 37, .c 3, .c 5, .c 17, .c 3, .c 7,
  .c 61, .c 3, .p pv2 [pv2,pv294829], .p pv3 [pv2,pv3,pv7,pv43,pv653], .c 3,
  .p pv2 [pv2,pv127,pv4643], .c 5, .c 3, .p pv3 [pv2,pv18427], .p pv19 [pv2,pv3,pv5,pv19,pv2069],
  .c 3, .c 5, .p pv7 [pv2,pv3,pv49139], .c 3, .c 17, .c 11, .c 3, .c 13, .c 19, .c 3, .c 7, .c 5,
  .c 3, .c 823, .c 43, .c 3, .c 5, .c 7, .c 3, .c 23, .c 13, .c 3, .c 101,
  .p pv2 [pv2,pv3,pv65521], .c 3, .p pv5 [pv2,pv491,pv1201], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv73,pv577], .c 79, .c 3,
]
private theorem h0143c30 : checkBlock 1179139 128 b0143c30 = true := by
  decide +kernel

private def b0143c31 : List Row := [
  .c 5, .c 733, .c 3, .c 29, .p pv3 [pv2,pv3,pv7,pv28081], .c 3, .c 859, .c 7, .c 3,
  .p pv2 [pv2,pv13,pv37,pv613], .c 5, .c 3, .p pv2 [pv2,pv47,pv12547],
  .p pv79 [pv2,pv3,pv5,pv11,pv1787], .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv31,pv373], .c 3, .c 11,
  .c 137, .c 3, .c 7, .c 197, .c 3, .c 17, .c 5, .c 3, .c 37, .c 7, .c 3, .c 5, .c 31, .c 3,
  .c 73, .c 19, .c 3, .p pv2 [pv2,pv277,pv2129], .c 59, .c 3, .c 199, .c 5, .c 3, .c 7, .c 647,
  .c 3, .c 5, .c 397, .c 3, .p pv11 [pv2,pv5,pv13,pv43,pv211], .c 7, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv196583], .c 3, .c 13, .c 5, .c 3, .c 23, .c 17, .c 3, .c 5, .c 29, .c 3, .c 7,
  .c 37, .c 3, .p pv5 [pv2,pv589763], .c 13, .c 3, .c 43, .c 5, .c 3, .c 19, .c 11, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv29,pv6779], .c 3, .p pv7 [pv2,pv5,pv31,pv761], .p pv13 [pv2,pv3,pv11,pv1117],
  .c 3, .c 61, .c 47, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv13,pv53,pv107],
  .p pv2 [pv2,pv3,pv5,pv7,pv41,pv137], .c 3, .c 5, .c 7, .c 3, .c 13, .p pv3 [pv2,pv3,pv196597],
  .c 3, .c 59, .p pv2 [pv2,pv3,pv98299], .c 3, .c 439, .c 5, .c 3, .p pv7 [pv2,pv7,pv109,pv773],
  .c 23, .c 3, .c 5, .c 11, .c 3, .c 41, .c 17, .c 3, .c 97, .c 7, .c 3, .c 311, .c 5, .c 3,
  .c 11, .c 163, .c 3, .c 5, .p pv5 [pv2,pv3,pv197,pv499], .c 3, .p pv41 [pv2,pv5,pv7,pv11,pv383],
  .c 31, .c 3, .c 7, .p pv19 [pv2,pv3],
]
private theorem h0143c31 : checkBlock 1179395 128 b0143c31 = true := by
  decide +kernel

def rows0143 : List Row :=
  b0143c00 ++ b0143c01 ++ b0143c02 ++ b0143c03 ++ b0143c04 ++ b0143c05 ++ b0143c06 ++ b0143c07 ++
  b0143c08 ++ b0143c09 ++ b0143c10 ++ b0143c11 ++ b0143c12 ++ b0143c13 ++ b0143c14 ++ b0143c15 ++
  b0143c16 ++ b0143c17 ++ b0143c18 ++ b0143c19 ++ b0143c20 ++ b0143c21 ++ b0143c22 ++ b0143c23 ++
  b0143c24 ++ b0143c25 ++ b0143c26 ++ b0143c27 ++ b0143c28 ++ b0143c29 ++ b0143c30 ++ b0143c31

theorem checked0143 : checkBlock 1171459 4096 rows0143 = true :=
  checkBlock_append h0143c00 (
    checkBlock_append h0143c01 (
    checkBlock_append h0143c02 (
    checkBlock_append h0143c03 (
    checkBlock_append h0143c04 (
    checkBlock_append h0143c05 (
    checkBlock_append h0143c06 (
    checkBlock_append h0143c07 (
    checkBlock_append h0143c08 (
    checkBlock_append h0143c09 (
    checkBlock_append h0143c10 (
    checkBlock_append h0143c11 (
    checkBlock_append h0143c12 (
    checkBlock_append h0143c13 (
    checkBlock_append h0143c14 (
    checkBlock_append h0143c15 (
    checkBlock_append h0143c16 (
    checkBlock_append h0143c17 (
    checkBlock_append h0143c18 (
    checkBlock_append h0143c19 (
    checkBlock_append h0143c20 (
    checkBlock_append h0143c21 (
    checkBlock_append h0143c22 (
    checkBlock_append h0143c23 (
    checkBlock_append h0143c24 (
    checkBlock_append h0143c25 (
    checkBlock_append h0143c26 (
    checkBlock_append h0143c27 (
    checkBlock_append h0143c28 (
    checkBlock_append h0143c29 (
    checkBlock_append h0143c30 (
    h0143c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
