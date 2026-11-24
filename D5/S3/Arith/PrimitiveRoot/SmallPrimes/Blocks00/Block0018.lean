/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks00/Block0018
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks00/Block0018.checked0018
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table030

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0018c00 : List Row := [
  .c 3, .c 167, .c 239, .c 3, .c 31, .c 7, .c 3, .c 89, .c 5, .c 3, .c 139,
  .p pv7 [pv2,pv3,pv5,pv1229], .c 3, .c 5, .p pv3 [pv2,pv3,pv47,pv523], .c 3, .c 83, .c 79, .c 3,
  .c 7, .c 11, .c 3, .p pv5 [pv2,pv73751], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv19,pv647], .c 3, .c 11, .c 29, .c 3, .c 151, .c 31, .c 3, .c 43, .c 5, .c 3,
  .c 7, .p pv23 [pv2,pv3,pv5,pv2459], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv1171], .c 3,
  .p pv23 [pv2,pv5,pv13,pv227], .c 7, .c 3, .p pv2 [pv2,pv37,pv997], .c 41, .c 3, .c 13, .c 5,
  .c 3, .c 173, .p pv2 [pv2,pv3,pv5,pv4919], .c 3, .c 5, .c 17, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv911], .c 3, .c 11, .c 13, .c 3, .c 37, .c 5, .c 3, .c 103, .c 67, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv73,pv337], .c 3, .c 17, .p pv2 [pv2,pv3,pv12301], .c 3,
  .p pv3 [pv2,pv7,pv659], .c 43, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv13,pv17,pv167], .c 11,
  .c 3, .c 5, .c 7, .c 3, .c 13, .c 191, .c 3, .p pv5 [pv2,pv73823], .c 19, .c 3, .c 11, .c 5,
  .c 3, .c 149, .p pv7 [pv2,pv3,pv5,pv23,pv107], .c 3, .c 5, .c 13, .c 3,
  .p pv29 [pv2,pv5,pv14767], .p pv5 [pv2,pv3,pv7,pv293], .c 3, .c 59, .c 7, .c 3, .c 23, .c 5,
  .c 3, .p pv3 [pv2,pv18461], .c 113, .c 3, .c 5, .c 11, .c 3, .c 127,
  .p pv5 [pv2,pv3,pv103,pv239], .c 3, .c 7, .p pv2 [pv2,pv3,pv11,pv373], .c 3, .c 17,
]
private theorem h0018c00 : checkBlock 147459 128 b0018c00 = true := by
  decide +kernel

private def b0018c01 : List Row := [
  .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv29,pv283], .c 3, .c 97, .c 241, .c 3,
  .c 157, .p pv7 [pv2,pv3,pv24623], .c 3, .p pv5 [pv2,pv7,pv61,pv173], .c 5, .c 3, .c 7, .c 71,
  .c 3, .c 5, .c 139, .c 3, .p pv3 [pv2,pv5,pv1847], .c 7, .c 3, .c 107,
  .p pv7 [pv2,pv3,pv47,pv131], .c 3, .p pv2 [pv2,pv36943], .c 5, .c 3, .p pv2 [pv2,pv37,pv1997],
  .c 17, .c 3, .c 5, .p pv3 [pv2,pv3,pv24631], .c 3, .c 7, .p pv5 [pv2,pv3,pv3079], .c 3, .c 13,
  .p pv3 [pv2,pv3,pv7,pv17,pv23], .c 3, .c 61, .c 5, .c 3, .c 79, .p pv3 [pv2,pv3,pv5,pv13,pv379],
  .c 3, .c 5, .c 53, .c 3, .c 23, .c 13, .c 3, .p pv2 [pv2,pv7,pv10559], .c 11, .c 3, .c 7, .c 5,
  .c 3, .c 19, .c 163, .c 3, .c 5, .c 7, .c 3, .c 11, .p pv5 [pv2,pv3,pv37], .c 3, .c 199,
  .p pv2 [pv2,pv3,pv19,pv1297], .c 3, .p pv7 [pv2,pv11,pv13,pv47], .c 5, .c 3, .c 67, .c 29, .c 3,
  .c 5, .c 19, .c 3, .p pv3 [pv2,pv5,pv3697], .c 17, .c 3, .c 41, .c 7, .c 3, .c 71, .c 5, .c 3,
  .c 131, .c 13, .c 3, .c 5, .c 353, .c 3, .c 211, .c 23, .c 3, .c 7, .p pv3 [pv2,pv3,pv89,pv277],
  .c 3, .c 53, .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv23,pv67], .c 3, .c 239,
  .c 337, .c 3, .c 197, .p pv11 [pv2,pv3,pv12329], .c 3, .c 13, .c 5, .c 3, .c 7, .c 11, .c 3,
  .c 5, .c 79, .c 3,
]
private theorem h0018c01 : checkBlock 147715 128 b0018c01 = true := by
  decide +kernel

private def b0018c02 : List Row := [
  .c 73, .c 7, .c 3, .p pv3 [pv2,pv53,pv349], .c 13, .c 3, .c 11, .c 5, .c 3, .c 83, .c 19, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv4111], .c 3, .c 7, .c 47, .c 3, .c 89, .c 283, .c 3,
  .p pv2 [pv2,pv37003], .c 5, .c 3, .c 17, .p pv31 [pv2,pv3,pv5,pv2467], .c 3, .c 5, .c 11, .c 3,
  .c 13, .c 179, .c 3, .c 37, .c 317, .c 3, .c 7, .c 5, .c 3, .c 11, .c 23, .c 3, .c 5, .c 7,
  .c 3, .p pv2 [pv2,pv5,pv11,pv673], .p pv3 [pv2,pv3,pv24677], .c 3, .c 19, .c 263, .c 3,
  .p pv3 [pv2,pv83,pv223], .c 5, .c 3, .p pv7 [pv2,pv7,pv1511], .c 373, .c 3, .c 5, .c 17, .c 3,
  .p pv2 [pv2,pv5,pv59,pv251], .c 11, .c 3, .c 23, .c 7, .c 3, .c 29, .c 5, .c 3, .c 13, .c 37,
  .c 3, .c 5, .c 73, .c 3, .c 17, .p pv2 [pv2,pv3,pv13,pv211], .c 3, .c 7, .c 167, .c 3, .c 41,
  .c 5, .c 3, .p pv2 [pv2,pv17,pv4357], .c 7, .c 3, .c 5, .p pv19 [pv2,pv3,pv24691], .c 3,
  .p pv11 [pv2,pv5,pv2963], .p pv5 [pv2,pv3,pv6173], .c 3, .p pv2 [pv2,pv37039], .c 11, .c 3,
  .c 229, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv11,pv449], .c 3, .c 5, .c 71, .c 3, .c 11, .c 7,
  .c 3, .c 13, .c 17, .c 3, .p pv3 [pv2,pv11,pv421], .c 5, .c 3, .p pv7 [pv2,pv74099],
  .p pv17 [pv2,pv3,pv5,pv13,pv19], .c 3, .c 5, .p pv3 [pv2,pv3,pv17,pv1453], .c 3, .c 7, .c 13,
  .c 3, .c 103, .c 19, .c 3, .c 17, .c 5,
]
private theorem h0018c02 : checkBlock 147971 128 b0018c02 = true := by
  decide +kernel

private def b0018c03 : List Row := [
  .c 3, .p pv2 [pv2,pv37057], .c 227, .c 3, .c 5, .c 271, .c 3, .c 53,
  .p pv2 [pv2,pv3,pv31,pv797], .c 3, .c 11, .p pv11 [pv2,pv3,pv29,pv71], .c 3, .c 7, .c 5, .c 3,
  .c 37, .c 173, .c 3, .c 5, .c 7, .c 3, .c 67, .c 31, .c 3, .c 29, .p pv17 [pv2,pv3,pv13,pv1901],
  .c 3, .c 79, .c 5, .c 3, .c 257, .c 11, .c 3, .c 5, .c 41, .c 3, .p pv2 [pv2,pv5,pv1483],
  .p pv3 [pv2,pv3,pv7,pv11,pv107], .c 3, .c 43, .c 7, .c 3, .c 11, .c 5, .c 3, .c 71, .c 83, .c 3,
  .c 5, .c 23, .c 3, .p pv7 [pv2,pv5,pv7,pv13,pv163], .c 19, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv41,pv67], .c 3, .c 13, .c 5, .c 3, .c 109, .c 7, .c 3, .c 5, .c 11, .c 3,
  .p pv3 [pv2,pv5,pv3709], .c 89, .c 3, .p pv5 [pv2,pv31,pv2393], .c 13, .c 3, .c 23, .c 5, .c 3,
  .c 7, .p pv19 [pv2,pv3,pv5,pv2473], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv3533], .c 3, .c 179, .c 7,
  .c 3, .c 31, .p pv3 [pv2,pv3,pv24733], .c 3, .p pv2 [pv2,pv74201], .c 5, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv5,pv17,pv97], .c 3, .c 5, .c 193, .c 3, .c 7, .c 11, .c 3, .c 17,
  .p pv13 [pv2,pv3,pv7,pv19,pv31], .c 3, .c 151, .c 5, .c 3, .p pv7 [pv2,pv74219], .c 79, .c 3,
  .c 5, .c 13, .c 3, .c 29, .c 53, .c 3, .p pv3 [pv2,pv7,pv11,pv241], .c 31, .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv37117], .p pv3 [pv2,pv3,pv5,pv7,pv101], .c 3, .c 5, .c 7, .c 3, .c 37,
]
private theorem h0018c03 : checkBlock 148227 128 b0018c03 = true := by
  decide +kernel

private def b0018c04 : List Row := [
  .p pv2 [pv2,pv3,pv73,pv113], .c 3, .c 83, .c 11, .c 3, .c 163, .c 5, .c 3, .c 13,
  .p pv83 [pv2,pv3,pv5,pv11], .c 3, .c 5, .c 97, .c 3, .c 11, .p pv5 [pv2,pv3,pv7,pv13,pv17],
  .c 3, .p pv2 [pv2,pv107,pv347], .c 7, .c 3, .c 19, .c 5, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv5,pv4951], .c 3, .c 5, .p pv19 [pv2,pv3,pv2063], .c 3, .c 89, .c 41, .c 3,
  .c 7, .p pv13 [pv2,pv3,pv12379], .c 3, .c 149, .c 5, .c 3, .c 53, .c 7, .c 3, .c 5, .c 29, .c 3,
  .c 101, .p pv5 [pv2,pv3,pv4127], .c 3, .c 11, .p pv2 [pv2,pv3,pv24763], .c 3, .c 31, .c 5, .c 3,
  .c 7, .c 139, .c 3, .c 5, .c 17, .c 3, .c 181, .c 7, .c 3, .c 173, .p pv7 [pv2,pv3,pv43], .c 3,
  .c 353, .c 5, .c 3, .c 331, .c 11, .c 3, .c 5, .p pv13 [pv2,pv3,pv23,pv359], .c 3, .c 7,
  .p pv19 [pv2,pv3,pv11,pv563], .c 3, .c 19, .p pv3 [pv2,pv3,pv7,pv3539], .c 3, .c 11, .c 5, .c 3,
  .c 23, .c 43, .c 3, .c 5, .c 61, .c 3, .c 47, .p pv3 [pv2,pv3,pv2753], .c 3,
  .p pv2 [pv2,pv7,pv37,pv41], .p pv2 [pv2,pv3,pv13,pv953], .c 3, .c 7, .c 5, .c 3, .c 157, .c 13,
  .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv14869], .p pv5 [pv2,pv3,pv12391], .c 3, .c 241, .c 17,
  .c 3, .c 37, .c 5, .c 3, .c 11, .p pv19 [pv2,pv3,pv5,pv4957], .c 3, .c 5, .c 127, .c 3,
  .p pv7 [pv2,pv5,pv11,pv13], .p pv2 [pv2,pv3,pv7,pv3541], .c 3, .p pv5 [pv2,pv74363], .c 7, .c 3,
  .c 13, .c 5, .c 3,
]
private theorem h0018c04 : checkBlock 148483 128 b0018c04 = true := by
  decide +kernel

private def b0018c05 : List Row := [
  .c 59, .c 23, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv1907], .c 3, .c 19, .c 11, .c 3, .c 7, .c 13,
  .c 3, .p pv2 [pv2,pv74381], .c 5, .c 3, .c 31, .c 7, .c 3, .c 5, .c 37, .c 3,
  .p pv3 [pv2,pv5,pv43,pv173], .p pv3 [pv2,pv3,pv137,pv181], .c 3, .c 23, .c 19, .c 3,
  .p pv3 [pv2,pv7,pv2657], .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 67, .c 3, .c 13, .c 7, .c 3,
  .p pv3 [pv2,pv71,pv131], .c 11, .c 3, .c 43, .c 5, .c 3, .p pv2 [pv2,pv29,pv1283], .c 31, .c 3,
  .c 5, .c 13, .c 3, .c 7, .c 251, .c 3, .c 73, .c 47, .c 3, .p pv2 [pv2,pv11,pv17,pv199], .c 5,
  .c 3, .p pv2 [pv2,pv263,pv283], .p pv23 [pv2,pv3,pv5,pv827], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv43,pv577], .c 3, .c 41, .p pv11 [pv2,pv3,pv6203], .c 3, .c 53, .c 23, .c 3,
  .c 7, .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv7,pv709], .c 3, .c 5, .c 7, .c 3, .c 61, .c 17,
  .c 3, .c 11, .c 43, .c 3, .p pv3 [pv2,pv41,pv227], .c 5, .c 3, .c 137,
  .p pv13 [pv2,pv3,pv5,pv17,pv73], .c 3, .c 5, .p pv3 [pv2,pv3,pv24821], .c 3,
  .p pv2 [pv2,pv5,pv53,pv281], .p pv29 [pv2,pv3,pv7,pv197], .c 3, .c 17, .c 7, .c 3, .c 47, .c 5,
  .c 3, .p pv2 [pv2,pv23,pv1619], .c 11, .c 3, .c 5, .p pv11 [pv2,pv3,pv12413], .c 3,
  .p pv3 [pv2,pv5,pv7,pv19], .c 181, .c 3, .c 7, .c 311, .c 3, .c 11, .c 5, .c 3, .c 19, .c 7,
  .c 3, .c 5, .c 383, .c 3, .p pv13 [pv2,pv5,pv47,pv317], .c 13,
]
private theorem h0018c05 : checkBlock 148739 128 b0018c05 = true := by
  decide +kernel

private def b0018c06 : List Row := [
  .c 3, .p pv3 [pv2,pv193], .c 37, .c 3, .c 109, .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv4967],
  .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv7451], .c 7, .c 3, .p pv2 [pv2,pv269,pv277], .c 71,
  .c 3, .p pv3 [pv2,pv13,pv1433], .c 5, .c 3, .c 11, .c 103, .c 3, .c 5, .c 113, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv12421], .c 3, .p pv3 [pv2,pv17,pv137], .p pv2 [pv2,pv3,pv7,pv13], .c 3, .c 23,
  .c 5, .c 3, .p pv2 [pv2,pv83,pv449], .c 13, .c 3, .c 5, .p pv19 [pv2,pv3,pv41,pv101], .c 3,
  .c 43, .c 11, .c 3, .p pv5 [pv2,pv7,pv23,pv463], .c 29, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv127,pv587], .p pv11 [pv2,pv3,pv5,pv7,pv71], .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv13,pv31,pv37], .p pv5 [pv2,pv3,pv19,pv109], .c 3, .c 41,
  .p pv17 [pv2,pv3,pv29,pv857], .c 3, .c 13, .c 5, .c 3, .c 197, .c 19, .c 3, .c 5, .c 293, .c 3,
  .c 17, .p pv3 [pv2,pv3,pv7,pv53,pv67], .c 3, .c 29, .c 7, .c 3, .p pv3 [pv2,pv59,pv79], .c 5,
  .c 3, .p pv19 [pv2,pv17,pv41,pv107], .p pv17 [pv2,pv3,pv5,pv11,pv113], .c 3, .c 5, .c 43, .c 3,
  .c 11, .p pv2 [pv2,pv3,pv31,pv401], .c 3, .c 7, .c 241, .c 3, .p pv5 [pv2,pv11,pv6781], .c 5,
  .c 3, .c 193, .c 7, .c 3, .c 5, .p pv17 [pv2,pv3,pv12433], .c 3, .c 13, .c 31, .c 3, .c 19,
  .c 17, .c 3, .p pv2 [pv2,pv7,pv73], .c 5, .c 3, .c 7, .c 37, .c 3, .c 5, .c 13, .c 3, .c 79,
  .c 7, .c 3, .c 11, .p pv31 [pv2,pv3,pv8291], .c 3, .c 17, .c 5, .c 3, .p pv3 [pv2,pv11,pv53],
]
private theorem h0018c06 : checkBlock 148995 128 b0018c06 = true := by
  decide +kernel

private def b0018c07 : List Row := [
  .p pv2 [pv2,pv3,pv5,pv199], .c 3, .c 5, .p pv5 [pv2,pv3,pv691], .c 3, .c 7, .c 29, .c 3, .c 61,
  .p pv2 [pv2,pv3,pv7,pv1777], .c 3, .c 113, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv139,pv179], .c 3, .c 337, .c 23, .c 3, .p pv3 [pv2,pv7,pv31,pv43], .c 173,
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv163,pv229], .c 17, .c 3, .c 5, .c 7, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv41,pv607], .c 3, .c 31, .c 59, .c 3, .p pv2 [pv2,pv37,pv1009], .c 5, .c 3,
  .c 23, .p pv2 [pv2,pv3,pv5,pv19,pv131], .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv29,pv103],
  .c 233, .c 3, .c 13, .c 7, .c 3, .c 41, .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv13,pv383],
  .c 3, .c 5, .p pv5 [pv2,pv3,pv389], .c 3, .p pv3 [pv2,pv5,pv7,pv11,pv97], .c 13, .c 3, .c 7,
  .c 31, .c 3, .p pv3 [pv2,pv9337], .c 5, .c 3, .p pv17 [pv2,pv74699], .c 7, .c 3, .c 5, .c 53,
  .c 3, .p pv2 [pv2,pv5,pv67,pv223], .c 11, .c 3, .p pv3 [pv2,pv19,pv983],
  .p pv3 [pv2,pv3,pv2767], .c 3, .p pv5 [pv2,pv7,pv13,pv821], .c 5, .c 3, .c 7, .c 23, .c 3, .c 5,
  .c 29, .c 3, .p pv3 [pv2,pv5,pv467], .c 7, .c 3, .c 17, .c 199, .c 3, .c 103, .c 5, .c 3,
  .p pv2 [pv2,pv74729], .c 13, .c 3, .c 5, .c 137, .c 3, .c 7, .c 19, .c 3, .c 23, .c 11, .c 3,
  .c 83, .c 5, .c 3, .p pv3 [pv2,pv9343], .p pv2 [pv2,pv3,pv5,pv11,pv151], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv6229], .c 3, .c 11, .p pv3 [pv2,pv3,pv24917], .c 3,
]
private theorem h0018c07 : checkBlock 149251 128 b0018c07 = true := by
  decide +kernel

private def b0018c08 : List Row := [
  .c 47, .c 307, .c 3, .c 7, .c 5, .c 3, .p pv13 [pv2,pv74759], .p pv17 [pv2,pv3,pv5,pv7,pv89],
  .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv19,pv787], .p pv5 [pv2,pv3,pv17,pv733], .c 3, .c 229,
  .c 13, .c 3, .p pv5 [pv2,pv74771], .c 5, .c 3, .c 17, .p pv3 [pv2,pv3,pv5,pv997], .c 3, .c 5,
  .c 347, .c 3, .p pv3 [pv2,pv5,pv3739], .p pv3 [pv2,pv3,pv7,pv1187], .c 3, .c 11, .c 7, .c 3,
  .c 373, .c 5, .c 3, .p pv2 [pv2,pv11,pv13,pv523], .c 101, .c 3, .c 5, .c 19, .c 3, .c 13,
  .c 227, .c 3, .c 7, .c 211, .c 3, .p pv2 [pv2,pv131,pv571], .c 5, .c 3, .c 41, .c 7, .c 3, .c 5,
  .c 13, .c 3, .c 157, .p pv3 [pv2,pv3,pv11,pv2267], .c 3, .p pv2 [pv2,pv79,pv947],
  .p pv2 [pv2,pv3,pv37,pv337], .c 3, .c 11, .c 5, .c 3, .c 7, .c 151, .c 3, .c 5, .c 263, .c 3,
  .c 17, .c 7, .c 3, .c 109, .c 103, .c 3, .c 19, .c 5, .c 3, .c 13, .c 97, .c 3, .c 5, .c 11,
  .c 3, .c 7, .c 43, .c 3, .c 181, .p pv31 [pv2,pv3,pv7,pv11], .c 3, .c 107, .c 5, .c 3, .c 11,
  .c 19, .c 3, .c 5, .c 23, .c 3, .p pv7 [pv2,pv5,pv11,pv1361], .p pv5 [pv2,pv3,pv3119], .c 3,
  .p pv3 [pv2,pv7,pv5347], .c 17, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv4679],
  .p pv19 [pv2,pv3,pv5,pv7,pv23,pv31], .c 3, .c 5, .c 7, .c 3, .c 137, .c 11, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv12479], .c 3, .c 17, .c 5, .c 3, .p pv11 [pv2,pv7,pv19,pv563], .c 31,
]
private theorem h0018c08 : checkBlock 149507 128 b0018c08 = true := by
  decide +kernel

private def b0018c09 : List Row := [
  .c 3, .c 5, .p pv13 [pv2,pv3,pv109,pv229], .c 3, .p pv23 [pv2,pv5,pv17,pv881], .c 13, .c 3,
  .c 19, .c 7, .c 3, .c 101, .c 5, .c 3, .c 47, .p pv47 [pv2,pv3,pv5,pv4993], .c 3, .c 5, .c 163,
  .c 3, .c 59, .p pv2 [pv2,pv3,pv24967], .c 3, .c 7, .c 11, .c 3, .c 37, .c 5, .c 3, .c 233, .c 7,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv24971], .c 3, .c 11, .c 269, .c 3, .p pv2 [pv2,pv47,pv797],
  .p pv3 [pv2,pv3,pv13,pv17,pv113], .c 3, .c 29, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 277,
  .c 3, .p pv2 [pv2,pv5,pv59,pv127], .c 7, .c 3, .p pv2 [pv2,pv74933], .c 73, .c 3,
  .p pv5 [pv2,pv17,pv19,pv29], .c 5, .c 3, .c 67, .c 71, .c 3, .c 5, .c 37, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv12491], .c 3, .c 11, .p pv2 [pv2,pv3,pv7,pv43,pv83], .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv3407], .p pv3 [pv2,pv3,pv5,pv19,pv263], .c 3, .c 5, .c 197, .c 3,
  .p pv13 [pv2,pv5,pv937], .c 17, .c 3, .c 313, .c 13, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv61,pv1229], .c 11, .c 3, .c 5, .c 7, .c 3, .c 113, .p pv31 [pv2,pv3,pv11,pv71],
  .c 3, .c 17, .c 29, .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv7,pv13,pv103],
  .p pv3 [pv2,pv3,pv5,pv4999], .c 3, .c 5, .c 47, .c 3, .c 13, .c 23, .c 3, .c 127, .c 7, .c 3,
  .p pv3 [pv2,pv18749], .c 5, .c 3, .c 61, .p pv7 [pv2,pv3,pv5], .c 3, .c 5, .c 11, .c 3,
  .p pv17 [pv2,pv5,pv7,pv2143], .c 67, .c 3, .c 7,
]
private theorem h0018c09 : checkBlock 149763 128 b0018c09 = true := by
  decide +kernel

private def b0018c10 : List Row := [
  .c 41, .c 3, .c 71, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 59, .c 3,
  .p pv3 [pv2,pv5,pv11,pv31], .c 19, .c 3, .c 227, .c 181, .c 3, .p pv2 [pv2,pv7,pv23,pv233],
  .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv41,pv61], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv397], .c 3,
  .c 31, .c 7, .c 3, .p pv2 [pv2,pv17,pv2207], .c 223, .c 3, .p pv2 [pv2,pv75041], .c 5, .c 3,
  .p pv3 [pv2,pv73,pv257], .p pv13 [pv2,pv3,pv5,pv5003], .c 3, .c 5, .p pv5 [pv2,pv3,pv53,pv59],
  .c 3, .c 7, .c 367, .c 3, .p pv5 [pv2,pv11,pv6823], .c 37, .c 3, .c 43, .c 5, .c 3, .c 19,
  .c 23, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv15013], .c 29, .c 3, .c 13, .c 11, .c 3, .c 7,
  .c 5, .c 3, .c 53, .p pv37 [pv2,pv3,pv5,pv7,pv11,pv13], .c 3, .c 5, .c 7, .c 3, .c 11, .c 13,
  .c 3, .c 23, .p pv7 [pv2,pv3,pv6257], .c 3, .c 263, .c 5, .c 3, .c 79, .c 179, .c 3, .c 5,
  .c 101, .c 3, .c 29, .p pv5 [pv2,pv3,pv7,pv149], .c 3, .p pv2 [pv2,pv37549], .c 7, .c 3,
  .p pv2 [pv2,pv13,pv53,pv109], .c 5, .c 3, .p pv3 [pv2,pv2347], .p pv2 [pv2,pv3,pv5,pv1669],
  .c 3, .c 5, .p pv13 [pv2,pv3,pv11,pv569], .c 3, .p pv3 [pv2,pv5,pv7,pv29,pv37],
  .p pv13 [pv2,pv3,pv25037], .c 3, .c 7, .c 17, .c 3, .c 19, .c 5, .c 3,
  .p pv11 [pv2,pv11,pv6829], .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv17,pv491], .c 3, .c 347, .c 97,
  .c 3, .c 31, .c 23, .c 3, .c 17, .c 5, .c 3, .c 7, .c 11, .c 3,
]
private theorem h0018c10 : checkBlock 150019 128 b0018c10 = true := by
  decide +kernel

private def b0018c11 : List Row := [
  .c 5, .c 103, .c 3, .c 67, .c 7, .c 3, .p pv5 [pv2,pv163,pv461], .c 137, .c 3, .c 11, .c 5,
  .c 3, .p pv2 [pv2,pv75149], .p pv2 [pv2,pv3,pv5,pv167], .c 3, .c 5, .c 29, .c 3, .c 7, .c 83,
  .c 3, .c 191, .c 13, .c 3, .p pv2 [pv2,pv75161], .c 5, .c 3, .p pv3 [pv2,pv19,pv23,pv43], .c 17,
  .c 3, .c 5, .c 11, .c 3, .c 149, .p pv5 [pv2,pv3,pv25057], .c 3, .c 19, .c 251, .c 3, .c 7,
  .c 5, .c 3, .c 11, .c 53, .c 3, .c 5, .c 7, .c 3, .c 13, .p pv5 [pv2,pv3,pv4177], .c 3,
  .p pv3 [pv2,pv18797], .p pv2 [pv2,pv3,pv71,pv353], .c 3, .p pv5 [pv2,pv17,pv4423], .c 5, .c 3,
  .c 101, .c 59, .c 3, .c 5, .c 13, .c 3, .p pv7 [pv2,pv5,pv47], .c 11, .c 3,
  .p pv5 [pv2,pv157,pv479], .c 7, .c 3, .p pv2 [pv2,pv31,pv1213], .c 5, .c 3, .c 349, .c 359,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv61,pv137], .c 3, .p pv7 [pv2,pv5,pv7,pv307], .c 17, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv25073], .c 3, .c 23, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 43, .c 3, .c 19,
  .c 379, .c 3, .c 17, .c 11, .c 3, .p pv3 [pv2,pv7,pv2687], .c 5, .c 3, .c 7, .c 29, .c 3, .c 5,
  .c 61, .c 3, .c 11, .c 7, .c 3, .p pv3 [pv2,pv4703], .c 19, .c 3, .p pv5 [pv2,pv11,pv6841],
  .c 5, .c 3, .c 59, .c 41, .c 3, .c 5, .p pv2 [pv2,pv3,pv37,pv113], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv25087], .c 3, .c 13, .c 109,
]
private theorem h0018c11 : checkBlock 150275 128 b0018c11 = true := by
  decide +kernel

private def b0018c12 : List Row := [
  .c 3, .p pv2 [pv2,pv37633], .c 5, .c 3, .c 29, .c 47, .c 3, .c 5, .c 151, .c 3,
  .p pv7 [pv2,pv5,pv3011], .c 13, .c 3, .c 11, .p pv3 [pv2,pv3,pv23,pv1091], .c 3, .c 7, .c 5,
  .c 3, .c 17, .p pv7 [pv2,pv3,pv5,pv7,pv239], .c 3, .c 5, .c 7, .c 3, .c 23,
  .p pv3 [pv2,pv3,pv25097], .c 3, .p pv2 [pv2,pv17,pv43,pv103], .p pv2 [pv2,pv3,pv47,pv89], .c 3,
  .c 41, .c 5, .c 3, .c 73, .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv2789], .c 3,
  .p pv13 [pv2,pv5,pv15061], .c 19, .c 3, .p pv3 [pv2,pv67,pv281], .c 7, .c 3, .c 11, .c 5, .c 3,
  .c 31, .c 13, .c 3, .c 5, .c 17, .c 3, .c 97, .c 199, .c 3, .c 7, .p pv17 [pv2,pv3,pv6277],
  .c 3, .c 79, .c 5, .c 3, .p pv2 [pv2,pv75329], .c 7, .c 3, .c 5, .c 11, .c 3, .c 17, .c 23,
  .c 3, .c 89, .c 53, .c 3, .c 13, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv13,pv23], .c 3, .c 37, .c 7, .c 3, .p pv2 [pv2,pv75353], .c 13, .c 3,
  .c 29, .c 5, .c 3, .c 23, .p pv31 [pv2,pv3,pv5,pv157], .c 3, .c 5, .c 19, .c 3, .c 7, .c 11,
  .c 3, .c 307, .c 17, .c 3, .p pv5 [pv2,pv23,pv29,pv113], .c 5, .c 3, .c 127, .c 233, .c 3, .c 5,
  .c 41, .c 3, .c 13, .c 107, .c 3, .p pv5 [pv2,pv7,pv11,pv89], .p pv13 [pv2,pv3,pv349], .c 3,
  .c 7, .c 5, .c 3, .p pv2 [pv2,pv75389], .c 131, .c 3, .c 5,
]
private theorem h0018c12 : checkBlock 150531 128 b0018c12 = true := by
  decide +kernel

private def b0018c13 : List Row := [
  .c 7, .c 3, .p pv7 [pv2,pv5,pv17,pv887], .c 101, .c 3, .p pv2 [pv2,pv37699], .c 11, .c 3, .c 19,
  .c 5, .c 3, .c 239, .c 23, .c 3, .c 5, .c 67, .c 3, .c 11, .c 47, .c 3,
  .p pv2 [pv2,pv13,pv5801], .c 7, .c 3, .p pv3 [pv2,pv11,pv857], .c 5, .c 3, .c 13, .c 17, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv31,pv811], .c 3, .c 251, .c 61, .c 3, .c 7, .c 257, .c 3, .c 59, .c 5,
  .c 3, .p pv2 [pv2,pv37717], .c 7, .c 3, .c 5, .c 31, .c 3, .p pv17 [pv2,pv5,pv23,pv41],
  .p pv5 [pv2,pv3,pv25147], .c 3, .c 11, .p pv11 [pv2,pv3,pv6287], .c 3,
  .p pv2 [pv2,pv7,pv17,pv317], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv503], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv3593], .c 3, .c 229, .c 7, .c 3, .c 13, .p pv3 [pv2,pv3,pv25153], .c 3,
  .c 37, .c 5, .c 3, .p pv3 [pv2,pv9433], .c 11, .c 3, .c 5, .c 149, .c 3, .c 7, .c 13, .c 3,
  .c 271, .c 23, .c 3, .c 11, .c 5, .c 3, .p pv7 [pv2,pv75479], .p pv11 [pv2,pv3,pv5,pv17,pv37],
  .c 3, .c 5, .p pv5 [pv2,pv3,pv8387], .c 3, .c 223, .c 43, .c 3, .c 17, .p pv2 [pv2,pv3,pv25163],
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv37747], .p pv3 [pv2,pv3,pv5,pv7,pv719], .c 3, .c 5, .c 7,
  .c 3, .c 31, .c 29, .c 3, .p pv5 [pv2,pv75503], .p pv47 [pv2,pv3,pv11,pv13], .c 3,
  .p pv2 [pv2,pv19,pv1987], .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv25171], .c 3,
  .c 19, .c 89, .c 3, .c 73, .c 7, .c 3,
]
private theorem h0018c13 : checkBlock 150787 128 b0018c13 = true := by
  decide +kernel

private def b0018c14 : List Row := [
  .c 131, .c 5, .c 3, .p pv3 [pv2,pv79,pv239], .p pv3 [pv2,pv3,pv5,pv19,pv53], .c 3, .c 5,
  .p pv17 [pv2,pv3,pv1049], .c 3, .c 29, .c 11, .c 3, .c 7, .c 19, .c 3, .c 13, .c 5, .c 3, .c 17,
  .c 7, .c 3, .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv29,pv521], .c 139, .c 3, .c 61, .c 13, .c 3,
  .c 53, .c 5, .c 3, .c 7, .c 137, .c 3, .c 5, .c 349, .c 3, .p pv3 [pv2,pv5,pv1889], .c 7, .c 3,
  .c 79, .c 11, .c 3, .c 23, .c 5, .c 3, .c 359, .p pv2 [pv2,pv3,pv5,pv11,pv229], .c 3, .c 5,
  .c 17, .c 3, .c 7, .p pv5 [pv2,pv3,pv47,pv67], .c 3, .p pv2 [pv2,pv23,pv31,pv53], .c 71, .c 3,
  .p pv2 [pv2,pv11,pv6871], .c 5, .c 3, .p pv3 [pv2,pv1181], .p pv11 [pv2,pv3,pv5,pv5039], .c 3,
  .c 5, .c 13, .c 3, .c 17, .c 19, .c 3, .c 31, .p pv2 [pv2,pv3,pv43,pv293], .c 3, .c 7, .c 5,
  .c 3, .c 47, .p pv17 [pv2,pv3,pv5,pv7], .c 3, .c 5, .c 7, .c 3, .c 89, .p pv7 [pv2,pv3,pv12601],
  .c 3, .c 11, .c 37, .c 3, .c 97, .c 5, .c 3, .c 13, .c 43, .c 3, .c 5, .p pv2 [pv2,pv3,pv4201],
  .c 3, .p pv7 [pv2,pv5,pv19,pv199], .p pv2 [pv2,pv3,pv7,pv13,pv277], .c 3,
  .p pv5 [pv2,pv47,pv1609], .c 7, .c 3, .p pv2 [pv2,pv37813], .c 5, .c 3, .c 19, .c 11, .c 3,
  .c 5, .c 331, .c 3, .c 23, .p pv5 [pv2,pv3,pv11,pv191], .c 3, .c 7,
  .p pv3 [pv2,pv3,pv19,pv1327], .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv18911], .c 7, .c 3, .c 5,
  .c 19,
]
private theorem h0018c14 : checkBlock 151043 128 b0018c14 = true := by
  decide +kernel

private def b0018c15 : List Row := [
  .c 3, .c 71, .p pv3 [pv2,pv3,pv151,pv167], .c 3, .c 13, .c 83, .c 3, .c 337, .c 5, .c 3, .c 7,
  .c 389, .c 3, .c 5, .c 11, .c 3, .c 41, .c 7, .c 3, .p pv3 [pv2,pv18917],
  .p pv2 [pv2,pv3,pv11,pv2293], .c 3, .p pv5 [pv2,pv31,pv2441], .c 5, .c 3, .c 11, .c 17, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv12613], .c 3, .c 7, .c 23, .c 3, .c 37, .c 229, .c 3, .c 19, .c 5, .c 3,
  .p pv2 [pv2,pv75689], .p pv7 [pv2,pv3,pv5,pv29], .c 3, .c 5, .c 47, .c 3,
  .p pv7 [pv2,pv5,pv15139], .c 11, .c 3, .p pv2 [pv2,pv7,pv5407], .c 101, .c 3, .c 7, .c 5, .c 3,
  .c 23, .c 13, .c 3, .c 5, .c 7, .c 3, .c 53, .p pv3 [pv2,pv3,pv25237], .c 3, .c 163,
  .p pv7 [pv2,pv3,pv12619], .c 3, .p pv3 [pv2,pv23,pv823], .c 5, .c 3, .c 199, .c 37, .c 3, .c 5,
  .c 269, .c 3, .p pv2 [pv2,pv5,pv13,pv233], .c 17, .c 3, .c 311, .c 7, .c 3, .c 13, .c 5, .c 3,
  .c 167, .p pv3 [pv2,pv3,pv5,pv11,pv17], .c 3, .c 5, .p pv11 [pv2,pv3,pv13,pv971], .c 3, .c 11,
  .p pv3 [pv2,pv3,pv25247], .c 3, .c 7, .c 13, .c 3, .c 197, .c 5, .c 3, .p pv2 [pv2,pv211,pv359],
  .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv19,pv443], .c 3, .c 127, .c 103, .c 3, .p pv2 [pv2,pv37879],
  .c 277, .c 3, .p pv2 [pv2,pv7,pv79,pv137], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv5051], .c 3,
  .c 5, .p pv29 [pv2,pv3,pv7,pv11,pv41], .c 3, .c 13, .c 7, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv73,pv173], .c 3, .p pv3 [pv2,pv37],
]
private theorem h0018c15 : checkBlock 151299 128 b0018c15 = true := by
  decide +kernel

private def b0018c16 : List Row := [
  .c 5, .c 3, .c 31, .p pv13 [pv2,pv3,pv5,pv421], .c 3, .c 5, .c 13, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv17,pv743], .c 3, .c 41, .p pv2 [pv2,pv3,pv7,pv401], .c 3, .c 29, .c 5, .c 3,
  .c 17, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv4211], .c 3, .c 19, .p pv2 [pv2,pv3,pv11,pv2297],
  .c 3, .p pv5 [pv2,pv7,pv13,pv17], .p pv7 [pv2,pv3,pv6317], .c 3, .c 7, .c 5, .c 3, .c 13, .c 31,
  .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv59,pv257], .c 53, .c 3, .p pv2 [pv2,pv167,pv227],
  .c 19, .c 3, .p pv2 [pv2,pv75821], .c 5, .c 3, .c 139, .p pv17 [pv2,pv3,pv5,pv337], .c 3, .c 5,
  .c 11, .c 3, .c 43, .c 37, .c 3, .p pv2 [pv2,pv75833], .c 7, .c 3, .p pv3 [pv2,pv18959], .c 5,
  .c 3, .c 11, .p pv11 [pv2,pv3,pv5,pv79], .c 3, .c 5, .p pv3 [pv2,pv3,pv53], .c 3, .c 17,
  .p pv2 [pv2,pv3,pv12641], .c 3, .c 7, .c 29, .c 3, .p pv5 [pv2,pv101,pv751], .c 5, .c 3, .c 211,
  .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv47,pv269], .c 3, .c 173, .c 11, .c 3, .c 71,
  .p pv23 [pv2,pv3,pv29,pv109], .c 3, .p pv2 [pv2,pv7,pv5419], .c 5, .c 3, .c 7, .c 41, .c 3,
  .c 5, .c 43, .c 3, .c 263, .c 7, .c 3, .c 29, .c 17, .c 3, .c 47, .c 5, .c 3,
  .p pv3 [pv2,pv61,pv311], .p pv2 [pv2,pv3,pv5,pv5059], .c 3, .c 5, .c 23, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv41,pv617], .c 3, .p pv2 [pv2,pv29,pv2617], .c 11, .c 3, .c 17, .c 5, .c 3,
  .p pv7 [pv2,pv71,pv1069], .c 13, .c 3, .c 5, .c 31, .c 3,
]
private theorem h0018c16 : checkBlock 151555 128 b0018c16 = true := by
  decide +kernel

private def b0018c17 : List Row := [
  .c 11, .p pv2 [pv2,pv3,pv4217], .c 3, .p pv5 [pv2,pv7,pv2711], .c 157, .c 3, .c 7, .c 5, .c 3,
  .c 19, .c 149, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv13,pv73], .c 317, .c 3,
  .p pv5 [pv2,pv23,pv3301], .p pv7 [pv2,pv3,pv19,pv37], .c 3, .c 13, .c 5, .c 3, .c 181, .c 17,
  .c 3, .c 5, .c 19, .c 3, .p pv11 [pv2,pv5,pv15187], .c 29, .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv75941], .c 5, .c 3, .c 67, .c 193, .c 3, .c 5, .p pv13 [pv2,pv3,pv6329], .c 3,
  .p pv17 [pv2,pv5,pv7,pv31], .p pv13 [pv2,pv3,pv29,pv97], .c 3, .c 7, .p pv2 [pv2,pv3,pv12659],
  .c 3, .c 73, .c 5, .c 3, .c 43, .c 7, .c 3, .c 5, .c 139, .c 3, .c 13, .c 137, .c 3,
  .p pv3 [pv2,pv1187], .p pv7 [pv2,pv3,pv23,pv367], .c 3, .c 11, .c 5, .c 3, .c 7, .c 47, .c 3,
  .c 5, .c 13, .c 3, .c 23, .c 7, .c 3, .p pv5 [pv2,pv75983], .p pv7 [pv2,pv3,pv1583], .c 3,
  .c 83, .c 5, .c 3, .c 379, .c 19, .c 3, .c 5, .c 11, .c 3, .c 7, .c 31, .c 3, .c 17, .c 97,
  .c 3, .p pv2 [pv2,pv76001], .c 5, .c 3, .c 11, .c 71, .c 3, .c 5, .p pv11 [pv2,pv3,pv3167],
  .c 3, .c 281, .c 67, .c 3, .p pv2 [pv2,pv7,pv10859], .p pv2 [pv2,pv3,pv41,pv103], .c 3, .c 7,
  .c 5, .c 3, .p pv19 [pv2,pv19,pv4001], .p pv11 [pv2,pv3,pv5,pv7,pv181], .c 3, .c 5, .c 7, .c 3,
  .c 383, .c 11, .c 3, .c 19, .c 73, .c 3, .p pv5 [pv2,pv76031], .c 5,
]
private theorem h0018c17 : checkBlock 151811 128 b0018c17 = true := by
  decide +kernel

private def b0018c18 : List Row := [
  .c 3, .c 41, .c 241, .c 3, .c 5, .p pv43 [pv2,pv3,pv19,pv23,pv29], .c 3,
  .p pv3 [pv2,pv5,pv1901], .p pv3 [pv2,pv3,pv7,pv17,pv71], .c 3, .c 13, .c 7, .c 3,
  .p pv2 [pv2,pv47,pv809], .c 5, .c 3, .c 17, .c 89, .c 3, .c 5, .c 37, .c 3,
  .p pv7 [pv2,pv5,pv7,pv41,pv53], .c 13, .c 3, .c 7, .c 11, .c 3, .p pv5 [pv2,pv23,pv3307], .c 5,
  .c 3, .c 149, .c 7, .c 3, .c 5, .c 167, .c 3, .c 11, .c 353, .c 3, .p pv2 [pv2,pv127,pv599],
  .c 233, .c 3, .c 71, .c 5, .c 3, .c 7, .c 59, .c 3, .c 5, .c 17, .c 3, .c 19, .c 7, .c 3, .c 43,
  .c 31, .c 3, .p pv5 [pv2,pv76091], .c 5, .c 3, .p pv2 [pv2,pv38047], .c 13, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv1153], .c 3, .c 7, .p pv3 [pv2,pv3,pv25367], .c 3, .c 11, .c 19, .c 3,
  .p pv2 [pv2,pv38053], .c 5, .c 3, .p pv2 [pv2,pv11,pv17,pv37], .c 29, .c 3, .c 5, .c 191, .c 3,
  .p pv29 [pv2,pv5,pv13,pv1171], .c 41, .c 3, .c 23, .p pv29 [pv2,pv3,pv25373], .c 3, .c 7, .c 5,
  .c 3, .p pv3 [pv2,pv19031], .c 11, .c 3, .c 5, .c 7, .c 3, .c 107, .c 43, .c 3,
  .p pv2 [pv2,pv19,pv4007], .c 13, .c 3, .c 11, .c 5, .c 3, .c 29, .c 197, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv17,pv1493], .c 3, .c 67, .p pv5 [pv2,pv3,pv7,pv37], .c 3,
  .p pv3 [pv2,pv19037], .c 7, .c 3, .c 17, .c 5, .c 3, .c 223, .p pv37 [pv2,pv3,pv5,pv5077], .c 3,
  .c 5, .c 11, .c 3, .c 13,
]
private theorem h0018c18 : checkBlock 152067 128 b0018c18 = true := by
  decide +kernel

private def b0018c19 : List Row := [
  .c 19, .c 3, .c 7, .c 23, .c 3, .c 347, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 13, .c 3, .c 73,
  .c 131, .c 3, .c 251, .c 151, .c 3, .p pv2 [pv2,pv7,pv10883], .c 5, .c 3, .c 7, .c 17, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv7,pv907], .c 3, .p pv3 [pv2,pv5,pv19,pv401], .c 7, .c 3, .c 97,
  .p pv7 [pv2,pv3,pv17,pv83], .c 3, .p pv3 [pv2,pv43,pv443], .c 5, .c 3, .c 13, .c 257, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv8467], .c 3, .c 7, .c 173, .c 3, .p pv3 [pv2,pv11,pv433],
  .p pv2 [pv2,pv3,pv7,pv19,pv191], .c 3, .p pv5 [pv2,pv17,pv4483], .c 5, .c 3,
  .p pv2 [pv2,pv53,pv719], .c 313, .c 3, .c 5, .c 19, .c 3, .p pv3 [pv2,pv5,pv37,pv103],
  .p pv3 [pv2,pv3,pv941], .c 3, .c 157, .c 11, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv31,pv2459],
  .p pv17 [pv2,pv3,pv5,pv7,pv11], .c 3, .c 5, .c 7, .c 3, .c 11, .c 17, .c 3, .c 13, .c 41, .c 3,
  .c 139, .c 5, .c 3, .c 31, .c 109, .c 3, .c 5, .c 73, .c 3, .p pv2 [pv2,pv5,pv61], .c 13, .c 3,
  .c 17, .c 7, .c 3, .c 19, .c 5, .c 3, .p pv11 [pv2,pv76259], .c 43, .c 3, .c 5, .c 127, .c 3,
  .p pv2 [pv2,pv5,pv7,pv2179], .p pv2 [pv2,pv3,pv19,pv223], .c 3, .c 7, .p pv2 [pv2,pv3,pv25423],
  .c 3, .c 103, .c 5, .c 3, .c 79, .c 7, .c 3, .c 5, .c 373, .c 3, .c 41,
  .p pv3 [pv2,pv3,pv47,pv541], .c 3, .p pv5 [pv2,pv76283], .c 29, .c 3, .c 271, .c 5, .c 3,
]
private theorem h0018c19 : checkBlock 152323 128 b0018c19 = true := by
  decide +kernel

private def b0018c20 : List Row := [
  .c 7, .c 11, .c 3, .c 5, .c 53, .c 3, .c 331, .c 7, .c 3, .p pv2 [pv2,pv38149],
  .p pv43 [pv2,pv3,pv29,pv877], .c 3, .c 11, .c 5, .c 3, .c 17, .c 101, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv6359], .c 3, .c 7, .p pv5 [pv2,pv3,pv61,pv139], .c 3, .c 19,
  .p pv41 [pv2,pv3,pv7,pv23,pv79], .c 3, .c 13, .c 5, .c 3, .p pv7 [pv2,pv167,pv457],
  .p pv13 [pv2,pv3,pv5,pv53], .c 3, .c 5, .c 11, .c 3, .c 23, .c 293, .c 3,
  .p pv3 [pv2,pv7,pv29,pv47], .c 13, .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv5,pv7,pv727], .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv11,pv347], .c 61,
  .c 3, .c 179, .c 107, .c 3, .c 43, .c 5, .c 3, .c 37, .c 311, .c 3, .c 5, .c 79, .c 3, .c 13,
  .c 11, .c 3, .p pv2 [pv2,pv73,pv523], .c 7, .c 3, .p pv2 [pv2,pv19,pv4019], .c 5, .c 3,
  .p pv3 [pv2,pv17,pv1123], .c 163, .c 3, .c 5, .c 13, .c 3, .c 19, .c 23, .c 3, .c 7, .c 103,
  .c 3, .p pv3 [pv2,pv9547], .c 5, .c 3, .c 173, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv23,pv41],
  .c 3, .c 227, .c 37, .c 3, .p pv3 [pv2,pv13,pv113], .c 11, .c 3, .p pv5 [pv2,pv7,pv1559], .c 5,
  .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv11,pv463], .c 3, .c 5, .c 47, .c 3, .c 11, .c 7, .c 3, .c 41,
  .p pv11 [pv2,pv3,pv6367], .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv109,pv701],
  .p pv2 [pv2,pv3,pv5,pv283], .c 3, .c 5, .c 67, .c 3, .c 7, .p pv5 [pv2,pv3,pv199],
]
private theorem h0018c20 : checkBlock 152579 128 b0018c20 = true := by
  decide +kernel

private def b0018c21 : List Row := [
  .c 3, .p pv2 [pv2,pv19,pv2011], .p pv3 [pv2,pv3,pv7,pv1213], .c 3, .p pv2 [pv2,pv76421], .c 5,
  .c 3, .c 353, .p pv3 [pv2,pv3,pv5,pv1019], .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv193], .c 3, .c 31,
  .c 71, .c 3, .c 11, .c 59, .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv11,pv6949], .c 17, .c 3, .c 5,
  .c 7, .c 3, .c 47, .c 13, .c 3, .p pv3 [pv2,pv2389], .p pv13 [pv2,pv3,pv17,pv1499], .c 3,
  .c 107, .c 5, .c 3, .p pv3 [pv2,pv7,pv43,pv127], .c 11, .c 3, .c 5, .c 29, .c 3, .c 37, .c 31,
  .c 3, .c 23, .c 7, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv47,pv1627],
  .p pv7 [pv2,pv3,pv5,pv2549], .c 3, .c 5, .p pv2 [pv2,pv3,pv29,pv293], .c 3, .c 43,
  .p pv5 [pv2,pv3,pv6373], .c 3, .c 7, .p pv17 [pv2,pv3,pv13,pv37,pv53], .c 3, .c 151, .c 5, .c 3,
  .c 19, .c 7, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv7649], .c 17, .c 3, .c 59,
  .p pv13 [pv2,pv3,pv11,pv19,pv61], .c 3, .p pv3 [pv2,pv7,pv683], .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv17], .c 3, .c 5, .c 19, .c 3, .c 53, .c 7, .c 3, .c 17, .c 23, .c 3,
  .c 13, .c 5, .c 3, .c 137, .c 199, .c 3, .c 5, .c 43, .c 3, .c 7, .c 11, .c 3, .c 31, .c 13,
  .c 3, .c 41, .c 5, .c 3, .p pv2 [pv2,pv103,pv743], .c 269, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv97,pv263], .c 3, .p pv7 [pv2,pv5,pv15307], .p pv5 [pv2,pv3,pv1063], .c 3,
  .p pv2 [pv2,pv7,pv11,pv71], .c 47, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv13,pv23],
]
private theorem h0018c21 : checkBlock 152835 128 b0018c21 = true := by
  decide +kernel

private def b0018c22 : List Row := [
  .c 29, .c 3, .c 5, .c 7, .c 3, .c 13, .c 283, .c 3, .p pv2 [pv2,pv37,pv2069], .c 11, .c 3,
  .p pv3 [pv2,pv19139], .c 5, .c 3, .c 17, .c 19, .c 3, .c 5, .c 13, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv7,pv1823], .c 3, .p pv5 [pv2,pv17,pv563], .c 7, .c 3, .c 37, .c 5, .c 3,
  .c 29, .p pv3 [pv2,pv3,pv5,pv1021], .c 3, .c 5, .c 23, .c 3, .c 103, .c 97, .c 3, .c 7, .c 89,
  .c 3, .c 47, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 17, .c 3, .p pv11 [pv2,pv5,pv15319],
  .c 307, .c 3, .c 11, .c 239, .c 3, .c 23, .c 5, .c 3, .c 7, .c 349, .c 3, .c 5, .c 37, .c 3,
  .c 17, .c 7, .c 3, .c 73, .c 67, .c 3, .c 31, .c 5, .c 3, .c 293, .c 11, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv25541], .c 3, .c 7, .c 331, .c 3, .c 13, .p pv7 [pv2,pv3,pv7,pv41,pv89], .c 3,
  .c 11, .c 5, .c 3, .p pv2 [pv2,pv38317], .p pv19 [pv2,pv3,pv5,pv13,pv131], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv53,pv241], .c 3, .p pv3 [pv2,pv5,pv479], .c 13, .c 3,
  .p pv5 [pv2,pv7,pv10949], .c 17, .c 3, .c 7, .c 5, .c 3, .c 41, .c 83, .c 3, .c 5, .c 7, .c 3,
  .c 19, .p pv5 [pv2,pv3,pv1597], .c 3, .c 139, .p pv11 [pv2,pv3,pv11,pv23,pv101], .c 3, .c 17,
  .c 5, .c 3, .c 11, .c 107, .c 3, .c 5, .p pv11 [pv2,pv3,pv6389], .c 3, .c 23,
  .p pv5 [pv2,pv3,pv7,pv1217], .c 3,
]
private theorem h0018c22 : checkBlock 153091 128 b0018c22 = true := by
  decide +kernel

private def b0018c23 : List Row := [
  .c 89, .c 7, .c 3, .p pv3 [pv2,pv29,pv661], .c 5, .c 3, .p pv13 [pv2,pv76679], .c 13, .c 3,
  .c 5, .c 103, .c 3, .p pv7 [pv2,pv5,pv7,pv313], .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv8521],
  .c 3, .c 163, .c 5, .c 3, .c 157, .c 7, .c 3, .c 5, .c 211, .c 3, .c 131, .c 179, .c 3,
  .p pv5 [pv2,pv11,pv19,pv367], .p pv19 [pv2,pv3,pv17,pv47], .c 3, .c 13, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv2557], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv13,pv281], .c 3, .c 71, .c 7,
  .c 3, .p pv2 [pv2,pv89,pv431], .c 11, .c 3, .p pv5 [pv2,pv17,pv4513], .c 5, .c 3,
  .p pv3 [pv2,pv19181], .c 173, .c 3, .c 5, .p pv5 [pv2,pv3,pv23,pv139], .c 3, .c 7, .c 19, .c 3,
  .c 43, .p pv2 [pv2,pv3,pv7,pv29], .c 3, .c 167, .c 5, .c 3, .c 23, .c 31, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv8527], .c 3, .c 13, .c 17, .c 3, .c 29, .p pv3 [pv2,pv3,pv25583], .c 3, .c 7,
  .c 5, .c 3, .p pv2 [pv2,pv38377], .p pv7 [pv2,pv3,pv5,pv7,pv17,pv43], .c 3, .c 5, .c 7, .c 3,
  .p pv17 [pv2,pv5,pv19,pv101], .p pv3 [pv2,pv3,pv2843], .c 3, .c 11, .p pv7 [pv2,pv3,pv6397],
  .c 3, .p pv2 [pv2,pv131,pv293], .c 5, .c 3, .c 19, .c 53, .c 3, .c 5, .c 233, .c 3, .c 97,
  .c 43, .c 3, .p pv2 [pv2,pv13,pv2953], .c 7, .c 3, .p pv2 [pv2,pv76781], .c 5, .c 3, .c 13,
  .c 11, .c 3, .c 5, .c 19, .c 3, .c 109, .c 383, .c 3, .c 7, .p pv2 [pv2,pv3,pv12799], .c 3,
  .c 11, .c 5, .c 3, .c 269, .c 7,
]
private theorem h0018c23 : checkBlock 153347 128 b0018c23 = true := by
  decide +kernel

private def b0018c24 : List Row := [
  .c 3, .c 5, .p pv3 [pv2,pv3,pv25601], .c 3, .p pv2 [pv2,pv5,pv15361], .c 29, .c 3, .c 23,
  .c 149, .c 3, .p pv5 [pv2,pv7,pv10973], .c 5, .c 3, .c 7, .c 67, .c 3, .c 5, .c 11, .c 3,
  .p pv3 [pv2,pv5,pv23,pv167], .c 7, .c 3, .c 13, .p pv7 [pv2,pv3,pv11,pv97], .c 3, .c 19, .c 5,
  .c 3, .c 11, .c 37, .c 3, .c 5, .c 31, .c 3, .c 7, .c 13, .c 3, .c 239, .c 227, .c 3, .c 313,
  .c 5, .c 3, .p pv3 [pv2,pv19211], .c 19, .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv29,pv53],
  .c 11, .c 3, .c 281, .c 23, .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv151,pv509], .c 347, .c 3,
  .c 5, .c 7, .c 3, .c 17, .p pv2 [pv2,pv3,pv23,pv557], .c 3, .c 47, .p pv2 [pv2,pv3,pv13,pv73],
  .c 3, .p pv5 [pv2,pv76871], .c 5, .c 3, .p pv11 [pv2,pv7,pv17,pv19], .c 13, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv4271], .c 3, .c 179, .p pv2 [pv2,pv3,pv7,pv523], .c 3, .c 19, .c 7, .c 3,
  .c 367, .c 5, .c 3, .c 103, .c 61, .c 3, .c 5, .c 29, .c 3, .c 11, .c 113, .c 3, .c 7, .c 17,
  .c 3, .c 13, .c 5, .c 3, .c 37, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv17,pv29], .c 3, .c 193,
  .c 101, .c 3, .c 199, .c 13, .c 3, .c 17, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv641], .c 3,
  .c 5, .c 23, .c 3, .c 137, .c 7, .c 3, .c 11,
]
private theorem h0018c24 : checkBlock 153603 128 b0018c24 = true := by
  decide +kernel

private def b0018c25 : List Row := [
  .c 53, .c 3, .c 251, .c 5, .c 3, .c 151, .p pv11 [pv2,pv3,pv5,pv23,pv223], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv12823], .c 3, .c 7, .c 37, .c 3, .p pv5 [pv2,pv76943],
  .p pv11 [pv2,pv3,pv7,pv229], .c 3, .c 23, .c 5, .c 3, .c 67, .c 11, .c 3, .c 5, .c 13, .c 3,
  .p pv7 [pv2,pv5,pv15391], .p pv19 [pv2,pv3,pv11,pv53], .c 3, .c 149, .c 19, .c 3, .c 7, .c 5,
  .c 3, .p pv7 [pv2,pv71,pv271], .c 59, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv43,pv179],
  .c 257, .c 3, .p pv2 [pv2,pv13,pv31,pv191], .p pv2 [pv2,pv3,pv12829], .c 3,
  .p pv3 [pv2,pv17,pv283], .c 5, .c 3, .c 13, .c 29, .c 3, .c 5, .c 11, .c 3, .c 79, .c 107, .c 3,
  .c 31, .c 7, .c 3, .c 43, .c 5, .c 3, .c 11, .p pv13 [pv2,pv3,pv5,pv29,pv59], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv41,pv313], .c 3, .p pv3 [pv2,pv5,pv7,pv11], .c 17, .c 3, .c 7, .c 337, .c 3,
  .c 233, .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv43,pv199], .c 3, .c 23, .c 11,
  .c 3, .c 13, .c 31, .c 3, .p pv2 [pv2,pv7,pv11003], .c 5, .c 3, .c 7, .c 127, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv131], .c 3, .p pv3 [pv2,pv5,pv7703], .c 7, .c 3,
  .p pv2 [pv2,pv11,pv47,pv149], .c 43, .c 3, .p pv3 [pv2,pv19259], .c 5, .c 3,
  .p pv7 [pv2,pv41,pv1879], .p pv19 [pv2,pv3,pv5,pv107], .c 3, .c 5, .p pv5 [pv2,pv3,pv61,pv421],
  .c 3, .c 7, .c 223, .c 3, .p pv3 [pv2,pv9631], .c 11, .c 3, .c 73, .c 5, .c 3, .c 19,
  .p pv11 [pv2,pv3,pv5,pv11,pv467], .c 3,
]
private theorem h0018c25 : checkBlock 153859 128 b0018c25 = true := by
  decide +kernel

private def b0018c26 : List Row := [
  .c 5, .c 229, .c 3, .c 11, .c 23, .c 3, .p pv5 [pv2,pv7,pv101,pv109], .c 79, .c 3, .c 7, .c 5,
  .c 3, .c 17, .c 13, .c 3, .c 5, .c 7, .c 3, .c 139, .p pv5 [pv2,pv3,pv2141], .c 3,
  .p pv2 [pv2,pv17,pv2267], .p pv3 [pv2,pv3,pv25693], .c 3, .c 31, .c 5, .c 3, .c 23, .c 151,
  .c 3, .c 5, .c 53, .c 3, .p pv2 [pv2,pv5,pv13,pv593], .p pv3 [pv2,pv3,pv7,pv3671], .c 3, .c 11,
  .c 7, .c 3, .c 13, .c 5, .c 3, .c 271, .c 41, .c 3, .c 5, .c 17, .c 3,
  .p pv2 [pv2,pv5,pv7,pv2203], .p pv2 [pv2,pv3,pv71,pv181], .c 3, .c 7, .c 13, .c 3, .c 19, .c 5,
  .c 3, .p pv2 [pv2,pv38557], .c 7, .c 3, .c 5, .c 89, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv11,pv19,pv41], .c 3, .p pv5 [pv2,pv233,pv331], .c 73, .c 3, .c 11, .c 5, .c 3,
  .c 7, .c 19, .c 3, .c 5, .p pv7 [pv2,pv3,pv7,pv3673], .c 3, .c 13, .c 7, .c 3,
  .p pv2 [pv2,pv38569], .p pv3 [pv2,pv3,pv2857], .c 3, .c 41, .c 5, .c 3, .c 277,
  .p pv3 [pv2,pv3,pv5,pv37,pv139], .c 3, .c 5, .c 11, .c 3, .c 7, .p pv5 [pv2,pv3,pv25717], .c 3,
  .c 23, .c 17, .c 3, .p pv3 [pv2,pv19289], .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv643], .c 3,
  .c 5, .c 37, .c 3, .c 157, .p pv2 [pv2,pv3,pv1429], .c 3, .c 19, .p pv3 [pv2,pv3,pv29,pv887],
  .c 3, .c 7, .c 5, .c 3, .c 13, .p pv41 [pv2,pv3,pv5,pv7], .c 3, .c 5, .c 7, .c 3, .c 163, .c 11,
  .c 3, .c 29, .p pv7 [pv2,pv3,pv67],
]
private theorem h0018c26 : checkBlock 154115 128 b0018c26 = true := by
  decide +kernel

private def b0018c27 : List Row := [
  .c 3, .p pv2 [pv2,pv38593], .c 5, .c 3, .c 317, .c 263, .c 3, .c 5, .p pv2 [pv2,pv3,pv953],
  .c 3, .c 61, .c 181, .c 3, .c 103, .c 7, .c 3, .c 59, .c 5, .c 3, .p pv3 [pv2,pv19301], .c 17,
  .c 3, .c 5, .p pv11 [pv2,pv3,pv3217], .c 3, .c 307, .p pv5 [pv2,pv3,pv23,pv373], .c 3, .c 7,
  .c 11, .c 3, .c 389, .c 5, .c 3, .p pv19 [pv2,pv37,pv2087], .c 7, .c 3, .c 5, .c 41, .c 3,
  .c 11, .c 13, .c 3, .c 257, .p pv2 [pv2,pv3,pv8581], .c 3, .c 83, .c 5, .c 3, .c 7, .c 113,
  .c 3, .c 5, .c 179, .c 3, .c 241, .c 7, .c 3, .p pv5 [pv2,pv77243], .c 19, .c 3,
  .p pv2 [pv2,pv13,pv2971], .c 5, .c 3, .c 43, .p pv17 [pv2,pv3,pv5,pv103], .c 3, .c 5, .c 367,
  .c 3, .c 7, .c 17, .c 3, .c 11, .c 191, .c 3, .p pv2 [pv2,pv77261], .c 5, .c 3, .c 41, .c 13,
  .c 3, .c 5, .c 23, .c 3, .c 29, .p pv3 [pv2,pv3,pv43,pv599], .c 3, .c 17, .c 37, .c 3, .c 7,
  .c 5, .c 3, .c 127, .c 11, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv13,pv29,pv41],
  .p pv2 [pv2,pv3,pv11,pv1171], .c 3, .c 331, .p pv53 [pv2,pv3,pv25763], .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv5521], .p pv13 [pv2,pv3,pv5,pv5153], .c 3, .c 5, .c 31, .c 3, .c 53, .c 19,
  .c 3, .c 349, .c 7, .c 3, .p pv2 [pv2,pv38653], .c 5, .c 3, .p pv2 [pv2,pv97,pv797],
  .p pv7 [pv2,pv3,pv5,pv859], .c 3, .c 5,
]
private theorem h0018c27 : checkBlock 154371 128 b0018c27 = true := by
  decide +kernel

private def b0018c28 : List Row := [
  .c 11, .c 3, .c 101, .c 239, .c 3, .c 7, .c 59, .c 3, .p pv2 [pv2,pv167,pv463], .c 5, .c 3,
  .c 11, .c 7, .c 3, .c 5, .c 29, .c 3, .c 13, .c 211, .c 3, .p pv2 [pv2,pv17,pv4549],
  .p pv2 [pv2,pv3,pv12889], .c 3, .c 137, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv1289], .c 3,
  .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv31,pv499], .c 7, .c 3, .c 37,
  .p pv3 [pv2,pv3,pv19,pv23,pv59], .c 3, .c 67, .c 5, .c 3, .c 71, .c 131, .c 3, .c 5, .c 17,
  .c 3, .c 7, .p pv7 [pv2,pv3,pv107,pv241], .c 3, .p pv5 [pv2,pv11,pv13,pv541], .c 359, .c 3,
  .p pv2 [pv2,pv101,pv383], .c 5, .c 3, .c 13, .c 271, .c 3, .c 5, .p pv2 [pv2,pv3,pv8597], .c 3,
  .c 17, .p pv5 [pv2,pv3,pv13,pv31], .c 3, .c 43, .c 11, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv17,pv569], .c 37, .c 3, .c 5, .c 7, .c 3, .c 11, .c 31, .c 3,
  .p pv2 [pv2,pv193,pv401], .p pv2 [pv2,pv3,pv12899], .c 3, .c 19, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv11057], .c 283, .c 3, .c 5, .p pv3 [pv2,pv3,pv25801], .c 3, .c 149, .c 23,
  .c 3, .c 13, .c 7, .c 3, .p pv5 [pv2,pv199,pv389], .c 5, .c 3, .c 107, .c 19, .c 3, .c 5, .c 67,
  .c 3, .p pv19 [pv2,pv5,pv7,pv79], .c 13, .c 3, .c 7, .p pv11 [pv2,pv3,pv1613], .c 3, .c 17,
  .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 251, .c 3, .p pv13 [pv2,pv5,pv17,pv911],
  .p pv7 [pv2,pv3,pv239], .c 3, .p pv2 [pv2,pv31,pv1249], .c 61, .c 3,
]
private theorem h0018c28 : checkBlock 154627 128 b0018c28 = true := by
  decide +kernel

private def b0018c29 : List Row := [
  .p pv2 [pv2,pv7,pv13,pv23,pv37], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv7,pv461], .c 3, .c 191, .c 7, .c 3, .c 19, .c 97, .c 3, .c 11, .c 5, .c 3,
  .c 37, .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv19,pv151], .c 3, .c 7, .p pv2 [pv2,pv3,pv12911],
  .c 3, .p pv3 [pv2,pv107,pv181], .c 41, .c 3, .p pv5 [pv2,pv77471], .c 5, .c 3, .c 89, .c 23,
  .c 3, .c 5, .c 11, .c 3, .c 83, .c 241, .c 3, .c 353, .c 31, .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv7,pv41], .c 3, .c 5, .c 7, .c 3, .p pv11 [pv2,pv5,pv11,pv1409], .c 37,
  .c 3, .c 23, .c 13, .c 3, .p pv2 [pv2,pv19,pv4079], .c 5, .c 3, .p pv3 [pv2,pv7,pv173], .c 379,
  .c 3, .c 5, .p pv17 [pv2,pv3,pv2153], .c 3, .c 19, .c 11, .c 3, .p pv2 [pv2,pv77513], .c 7,
  .c 3, .c 229, .c 5, .c 3, .c 197, .c 227, .c 3, .c 5, .p pv5 [pv2,pv3,pv25841], .c 3, .c 13,
  .c 47, .c 3, .c 7, .c 19, .c 3, .c 29, .c 5, .c 3, .p pv2 [pv2,pv38767], .c 7, .c 3, .c 5,
  .c 13, .c 3, .p pv3 [pv2,pv5,pv3877], .p pv2 [pv2,pv3,pv25847], .c 3, .p pv5 [pv2,pv77543],
  .c 11, .c 3, .c 31, .c 5, .c 3, .c 7, .c 43, .c 3, .c 5, .c 109, .c 3, .c 11, .c 7, .c 3,
  .c 181, .p pv3 [pv2,pv3,pv103,pv251], .c 3, .c 61, .c 5, .c 3, .c 13, .c 53, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv101],
]
private theorem h0018c29 : checkBlock 154883 128 b0018c29 = true := by
  decide +kernel

private def b0018c30 : List Row := [
  .c 3, .c 7, .c 167, .c 3, .c 47, .c 113, .c 3, .p pv3 [pv2,pv9697], .c 5, .c 3, .c 17,
  .p pv53 [pv2,pv3,pv5,pv431], .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv2351], .c 3,
  .p pv2 [pv2,pv5,pv59,pv263], .c 19, .c 3, .c 11, .c 29, .c 3, .c 7, .c 5, .c 3, .c 311,
  .p pv7 [pv2,pv3,pv5,pv7,pv739], .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv97],
  .p pv3 [pv2,pv3,pv25867], .c 3, .c 13, .p pv7 [pv2,pv3,pv29,pv223], .c 3, .c 269, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv11087], .c 11, .c 3, .c 5, .c 17, .c 3, .p pv19 [pv2,pv5,pv19,pv43], .c 13,
  .c 3, .c 29, .c 7, .c 3, .c 11, .c 5, .c 3, .c 19, .p pv2 [pv2,pv3,pv5,pv23], .c 3, .c 5,
  .c 107, .c 3, .c 17, .c 139, .c 3, .c 7, .p pv29 [pv2,pv3,pv19,pv227], .c 3, .c 23, .c 5, .c 3,
  .c 31, .c 7, .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv53,pv293], .c 83, .c 3, .c 97,
  .p pv3 [pv2,pv3,pv11,pv13,pv181], .c 3, .p pv7 [pv2,pv7,pv11093], .c 5, .c 3, .c 7, .c 13, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv7,pv43], .c 3, .c 127, .c 7, .c 3, .p pv5 [pv2,pv37,pv2099], .c 17,
  .c 3, .p pv2 [pv2,pv38833], .c 5, .c 3, .c 163, .c 31, .c 3, .c 5, .c 59, .c 3, .c 7, .c 11,
  .c 3, .c 337, .c 43, .c 3, .c 13, .c 5, .c 3, .c 251, .p pv2 [pv2,pv3,pv5,pv5179], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv83], .c 3, .p pv2 [pv2,pv5,pv17,pv457], .p pv7 [pv2,pv3,pv19,pv29,pv47],
  .c 3, .p pv2 [pv2,pv7,pv11,pv1009], .c 13, .c 3, .c 7,
]
private theorem h0018c30 : checkBlock 155139 128 b0018c30 = true := by
  decide +kernel

private def b0018c31 : List Row := [
  .c 5, .c 3, .p pv19 [pv2,pv77699], .c 19, .c 3, .c 5, .c 7, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv1439], .c 3, .c 73, .c 11, .c 3, .p pv5 [pv2,pv77711], .c 5, .c 3, .c 47,
  .c 17, .c 3, .c 5, .c 37, .c 3, .c 11, .p pv5 [pv2,pv3,pv7,pv3701], .c 3, .c 359, .c 7, .c 3,
  .p pv2 [pv2,pv11,pv3533], .c 5, .c 3, .c 83, .p pv7 [pv2,pv3,pv5,pv2591], .c 3, .c 5, .c 13,
  .c 3, .c 107, .p pv11 [pv2,pv3,pv41,pv79], .c 3, .c 7, .c 181, .c 3, .c 89, .c 5, .c 3, .c 61,
  .c 7, .c 3, .c 5, .c 131, .c 3, .p pv2 [pv2,pv5,pv311], .c 23, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv12959], .c 3, .c 41, .c 5, .c 3, .c 7, .p pv47 [pv2,pv3,pv5], .c 3, .c 5,
  .c 29, .c 3, .c 43, .c 7, .c 3, .p pv3 [pv2,pv9721], .p pv2 [pv2,pv3,pv8641], .c 3, .c 109,
  .c 5, .c 3, .c 23, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv29,pv149], .c 3, .c 7, .c 73, .c 3,
  .c 17, .p pv13 [pv2,pv3,pv7,pv463], .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv107,pv727],
  .p pv7 [pv2,pv3,pv5,pv2593], .c 3, .c 5, .c 157, .c 3, .c 19, .p pv19 [pv2,pv3,pv2161], .c 3,
  .c 13, .p pv11 [pv2,pv3,pv25933], .c 3, .c 7, .c 5, .c 3, .p pv7 [pv2,pv53,pv367], .c 61, .c 3,
  .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv31,pv251], .c 13, .c 3, .p pv2 [pv2,pv77813], .c 19, .c 3,
  .c 103, .c 5, .c 3, .c 11, .c 23, .c 3, .c 5, .c 317, .c 3,
]
private theorem h0018c31 : checkBlock 155395 128 b0018c31 = true := by
  decide +kernel

def rows0018 : List Row :=
  b0018c00 ++ b0018c01 ++ b0018c02 ++ b0018c03 ++ b0018c04 ++ b0018c05 ++ b0018c06 ++ b0018c07 ++
  b0018c08 ++ b0018c09 ++ b0018c10 ++ b0018c11 ++ b0018c12 ++ b0018c13 ++ b0018c14 ++ b0018c15 ++
  b0018c16 ++ b0018c17 ++ b0018c18 ++ b0018c19 ++ b0018c20 ++ b0018c21 ++ b0018c22 ++ b0018c23 ++
  b0018c24 ++ b0018c25 ++ b0018c26 ++ b0018c27 ++ b0018c28 ++ b0018c29 ++ b0018c30 ++ b0018c31

theorem checked0018 : checkBlock 147459 4096 rows0018 = true :=
  checkBlock_append h0018c00 (
    checkBlock_append h0018c01 (
    checkBlock_append h0018c02 (
    checkBlock_append h0018c03 (
    checkBlock_append h0018c04 (
    checkBlock_append h0018c05 (
    checkBlock_append h0018c06 (
    checkBlock_append h0018c07 (
    checkBlock_append h0018c08 (
    checkBlock_append h0018c09 (
    checkBlock_append h0018c10 (
    checkBlock_append h0018c11 (
    checkBlock_append h0018c12 (
    checkBlock_append h0018c13 (
    checkBlock_append h0018c14 (
    checkBlock_append h0018c15 (
    checkBlock_append h0018c16 (
    checkBlock_append h0018c17 (
    checkBlock_append h0018c18 (
    checkBlock_append h0018c19 (
    checkBlock_append h0018c20 (
    checkBlock_append h0018c21 (
    checkBlock_append h0018c22 (
    checkBlock_append h0018c23 (
    checkBlock_append h0018c24 (
    checkBlock_append h0018c25 (
    checkBlock_append h0018c26 (
    checkBlock_append h0018c27 (
    checkBlock_append h0018c28 (
    checkBlock_append h0018c29 (
    checkBlock_append h0018c30 (
    h0018c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
