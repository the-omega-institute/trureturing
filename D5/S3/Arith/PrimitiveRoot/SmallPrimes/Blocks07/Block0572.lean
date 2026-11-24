/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks07/Block0572
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks07/Block0572.checked0572
   digest: Kernel proof of checker success on extended consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table045
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table049
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table054
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table060
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table078
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table090
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table107
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table129
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table157
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table158
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table159
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table160
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table161
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table162
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table165
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table169
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table171
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table176
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table182
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table188
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table195
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table213
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table233
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables03.Table266

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0572c00 : List Row := [
  .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 29, .c 3, .c 89, .p pv5 [pv2,pv3,pv11,pv13,pv101], .c 3,
  .p pv3 [pv2,pv292471], .c 17, .c 3, .c 11, .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv10399], .c 3,
  .c 5, .c 23, .c 3, .c 43, .c 7, .c 3, .c 19, .c 127, .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv823,pv2843], .p pv2 [pv2,pv3,pv5,pv23,pv3391], .c 3, .c 5, .c 11, .c 3, .c 7,
  .c 941, .c 3, .c 13, .c 103, .c 3, .c 23, .c 5, .c 3, .c 11, .c 461, .c 3, .c 5, .c 41, .c 3,
  .p pv3 [pv2,pv5,pv11,pv89,pv239], .c 13, .c 3, .p pv2 [pv2,pv7,pv23,pv14533],
  .p pv7 [pv2,pv3,pv271,pv1439], .c 3, .c 7, .c 5, .c 3, .p pv23 [pv2,pv277,pv8447], .c 17, .c 3,
  .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv173,pv541], .c 11, .c 3, .p pv3 [pv2,pv563,pv1039], .c 1999,
  .c 3, .c 313, .c 5, .c 3, .c 113, .c 193, .c 3, .c 5, .p pv2 [pv2,pv3,pv61,pv2131], .c 3, .c 19,
  .p pv2 [pv2,pv3,pv7,pv67,pv1663], .c 3, .p pv5 [pv2,pv11,pv37,pv5749], .c 7, .c 3,
  .p pv2 [pv2,pv17,pv68819], .c 5, .c 3, .c 41, .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv83,pv9397],
  .c 3, .p pv23 [pv2,pv5,pv7,pv66853], .c 131, .c 3, .c 7, .c 11, .c 3, .c 37, .c 5, .c 3, .c 31,
  .c 7, .c 3, .c 5, .c 61, .c 3, .c 11, .c 17, .c 3, .p pv2 [pv2,pv509,pv4597], .c 67, .c 3,
  .c 13, .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv17,pv31,pv37], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv13,pv2857], .c 3,
]
private theorem h0572c00 : checkBlock 4679515 128 b0572c00 = true := by
  decide +kernel

private def b0572c01 : List Row := [
  .p pv2 [pv2,pv5,pv467977], .c 7, .c 3, .c 17, .c 13, .c 3, .c 137, .c 5, .c 3, .c 83, .c 31,
  .c 3, .c 5, .c 37, .c 3, .c 7, .p pv3 [pv2,pv3,pv79,pv1097], .c 3, .c 11,
  .p pv11 [pv2,pv3,pv7,pv1741], .c 3, .p pv2 [pv2,pv887,pv1319], .c 5, .c 3, .c 43, .c 59, .c 3,
  .c 5, .c 1621, .c 3, .c 13, .c 19, .c 3, .c 47, .p pv13 [pv2,pv3,pv259991], .c 3, .c 7, .c 5,
  .c 3, .p pv3 [pv2,pv584981], .c 11, .c 3, .c 5, .c 7, .c 3, .c 1279, .c 41, .c 3,
  .p pv2 [pv2,pv2339933], .p pv7 [pv2,pv3,pv389989], .c 3, .c 11, .c 5, .c 3, .c 17, .c 79, .c 3,
  .c 5, .c 89, .c 3, .p pv2 [pv2,pv5,pv19,pv24631], .c 163, .c 3, .p pv3 [pv2,pv13,pv17,pv2647],
  .c 7, .c 3, .p pv5 [pv2,pv23,pv101737], .c 5, .c 3, .c 13, .p pv23 [pv2,pv3,pv5,pv17333], .c 3,
  .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv7,pv61,pv137], .p pv2 [pv2,pv3,pv13,pv59999], .c 3, .c 7,
  .p pv13 [pv2,pv3,pv11,pv19,pv311], .c 3, .c 29, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 17,
  .c 3, .p pv11 [pv2,pv5,pv11,pv67,pv127], .c 53, .c 3, .c 73, .c 97, .c 3,
  .p pv2 [pv2,pv7,pv29,pv11527], .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 31, .c 3, .c 17, .c 7,
  .c 3, .c 13, .c 347, .c 3, .c 827, .c 5, .c 3, .p pv7 [pv2,pv17,pv59,pv2333],
  .p pv11 [pv2,pv3,pv5,pv13], .c 3, .c 5, .p pv23 [pv2,pv3,pv53,pv14717], .c 3, .c 7, .c 13, .c 3,
  .c 23, .c 37, .c 3, .c 19, .c 5,
]
private theorem h0572c01 : checkBlock 4679771 128 b0572c01 = true := by
  decide +kernel

private def b0572c02 : List Row := [
  .c 3, .c 1103, .c 373, .c 3, .c 5, .c 101, .c 3, .p pv3 [pv2,pv5,pv23,pv5087],
  .p pv2 [pv2,pv3,pv19,pv61,pv673], .c 3, .c 577, .c 11, .c 3, .c 7, .c 5, .c 3, .c 53, .c 19,
  .c 3, .c 5, .c 7, .c 3, .c 11, .c 107, .c 3, .c 43, .p pv31 [pv2,pv3,pv13,pv29,pv2069], .c 3,
  .c 17, .c 5, .c 3, .c 293, .c 13, .c 3, .c 5, .p pv13 [pv2,pv3,pv48751], .c 3, .c 31, .c 61,
  .c 3, .c 29, .c 7, .c 3, .c 1453, .c 5, .c 3, .c 47, .c 83, .c 3, .c 5, .c 631, .c 3,
  .p pv2 [pv2,pv5,pv7,pv13,pv37,pv139], .c 109, .c 3, .c 7, .c 1193, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv106367], .c 7, .c 3, .c 5, .c 743, .c 3, .p pv3 [pv2,pv5,pv29251], .c 31,
  .c 3, .c 37, .c 13, .c 3, .p pv2 [pv2,pv7,pv167149], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .c 409, .c 3, .c 41, .c 7, .c 3, .c 79, .p pv3 [pv2,pv3,pv260011], .c 3, .c 11, .c 5, .c 3,
  .c 1381, .p pv2 [pv2,pv3,pv5,pv156007], .c 3, .c 5, .c 103, .c 3, .c 7, .c 29, .c 3, .c 257,
  .c 431, .c 3, .c 397, .c 5, .c 3, .c 101, .c 37, .c 3, .c 5, .c 11, .c 3, .c 19, .c 17, .c 3,
  .c 421, .c 619, .c 3, .c 7, .c 5, .c 3, .c 11, .c 53, .c 3, .c 5, .c 7, .c 3, .c 29,
]
private theorem h0572c02 : checkBlock 4680027 128 b0572c02 = true := by
  decide +kernel

private def b0572c03 : List Row := [
  .c 359, .c 3, .c 17, .c 19, .c 3, .c 23, .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv15601], .c 3,
  .c 5, .c 47, .c 3, .p pv23 [pv2,pv5,pv29,pv16139], .c 11, .c 3, .p pv2 [pv2,pv23,pv50873], .c 7,
  .c 3, .p pv2 [pv2,pv73,pv32057], .c 5, .c 3, .c 1327, .c 127, .c 3, .c 5, .c 239, .c 3, .c 1187,
  .c 2027, .c 3, .c 7, .c 31, .c 3, .p pv3 [pv2,pv37,pv59,pv67], .c 5, .c 3, .c 1289, .c 7, .c 3,
  .c 5, .c 1307, .c 3, .p pv2 [pv2,pv5,pv83,pv5639], .p pv2 [pv2,pv3,pv17,pv22943], .c 3, .c 13,
  .c 11, .c 3, .p pv5 [pv2,pv7,pv163,pv293], .c 5, .c 3, .c 7, .c 71, .c 3, .c 5, .c 29, .c 3,
  .c 11, .c 7, .c 3, .p pv5 [pv2,pv17,pv137659], .p pv11 [pv2,pv3,pv23,pv61,pv139], .c 3,
  .p pv3 [pv2,pv11,pv106373], .c 5, .c 3, .c 67, .c 43, .c 3, .c 5, .c 353, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv32503], .c 3, .c 41, .c 349, .c 3, .c 193, .c 5, .c 3, .c 1951,
  .p pv3 [pv2,pv3,pv5,pv3467], .c 3, .c 5, .c 17, .c 3, .c 241, .c 37, .c 3, .c 11, .c 61, .c 3,
  .c 7, .c 5, .c 3, .c 19, .c 13, .c 3, .c 5, .c 7, .c 3, .c 17, .c 991, .c 3,
  .p pv3 [pv2,pv292531], .c 131, .c 3, .p pv5 [pv2,pv2340251], .c 5, .c 3, .c 167, .c 11, .c 3,
  .c 5, .c 19, .c 3, .c 821, .c 23, .c 3, .p pv5 [pv2,pv103,pv22721], .c 7, .c 3, .c 11, .c 5,
  .c 3,
]
private theorem h0572c03 : checkBlock 4680283 128 b0572c03 = true := by
  decide +kernel

private def b0572c04 : List Row := [
  .p pv2 [pv2,pv2340269], .c 73, .c 3, .c 5, .c 139, .c 3, .p pv13 [pv2,pv5,pv7,pv43,pv311],
  .c 67, .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv617,pv3793], .c 5, .c 3, .c 23, .c 7, .c 3, .c 5,
  .c 11, .c 3, .c 1609, .p pv5 [pv2,pv3,pv641,pv1217], .c 3, .p pv2 [pv2,pv599,pv3907], .c 47,
  .c 3, .c 17, .c 5, .c 3, .c 7, .c 41, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv111443], .c 3, .c 13,
  .c 7, .c 3, .c 281, .c 83, .c 3, .p pv5 [pv2,pv1087,pv2153], .c 5, .c 3, .c 29, .c 19, .c 3,
  .c 5, .c 13, .c 3, .c 7, .c 11, .c 3, .c 59, .c 419, .c 3, .p pv2 [pv2,pv61,pv19183], .c 5,
  .c 3, .c 31, .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv9631], .c 3, .c 79, .p pv5 [pv2,pv3,pv48757],
  .c 3, .p pv2 [pv2,pv7,pv11,pv13,pv167], .c 43, .c 3, .c 7, .c 5, .c 3, .c 13, .c 859, .c 3,
  .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv46807], .c 491, .c 3, .c 19, .c 11, .c 3, .c 61, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv367,pv911], .c 31, .c 3, .c 5, .p pv3 [pv2,pv3,pv19,pv2161], .c 3, .c 11,
  .p pv2 [pv2,pv3,pv7,pv103,pv541], .c 3, .c 233, .c 7, .c 3, .p pv5 [pv2,pv11,pv137,pv1553],
  .c 5, .c 3, .p pv2 [pv2,pv53,pv22079], .c 1009, .c 3, .c 5, .p pv2 [pv2,pv3,pv130021], .c 3,
  .c 131, .c 17, .c 3, .c 7, .p pv13 [pv2,pv3,pv24379], .c 3, .p pv2 [pv2,pv1170193], .c 5, .c 3,
  .p pv2 [pv2,pv677,pv3457], .c 7, .c 3, .c 5, .c 109, .c 3, .p pv13 [pv2,pv5,pv468079], .c 13,
]
private theorem h0572c04 : checkBlock 4680539 128 b0572c04 = true := by
  decide +kernel

private def b0572c05 : List Row := [
  .c 3, .c 11, .c 23, .c 3, .c 29, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv52009], .c 3, .c 5,
  .c 71, .c 3, .c 19, .c 7, .c 3, .p pv2 [pv2,pv739,pv3167], .c 79, .c 3, .c 37, .c 5, .c 3,
  .c 127, .c 11, .c 3, .c 5, .c 41, .c 3, .c 7, .p pv13 [pv2,pv3,pv11,pv35461], .c 3,
  .p pv3 [pv2,pv585107], .c 19, .c 3, .c 11, .c 5, .c 3, .c 269, .c 13, .c 3, .c 5, .c 659, .c 3,
  .p pv11 [pv2,pv5,pv58511], .c 59, .c 3, .p pv5 [pv2,pv7,pv334349],
  .p pv23 [pv2,pv3,pv41,pv67,pv71], .c 3, .c 7, .c 5, .c 3, .c 17,
  .p pv23 [pv2,pv3,pv5,pv7,pv743], .c 3, .c 5, .c 7, .c 3, .c 761, .p pv7 [pv2,pv3,pv113,pv863],
  .c 3, .c 197, .c 29, .c 3, .c 13, .c 5, .c 3, .c 11, .c 1583, .c 3, .c 5, .c 23, .c 3,
  .p pv2 [pv2,pv5,pv11,pv21277], .c 241, .c 3, .c 2063, .c 7, .c 3, .p pv3 [pv2,pv585119], .c 5,
  .c 3, .c 71, .p pv79 [pv2,pv3,pv5,pv23,pv53], .c 3, .c 5, .c 17, .c 3,
  .p pv2 [pv2,pv5,pv7,pv41,pv233], .c 11, .c 3, .c 7, .c 73, .c 3, .c 23, .c 5, .c 3, .c 229,
  .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv390083], .c 3, .c 13, .p pv3 [pv2,pv3,pv331,pv2357], .c 3,
  .p pv5 [pv2,pv11,pv23,pv29], .p pv13 [pv2,pv3,pv32507], .c 3, .c 53, .c 5, .c 3, .c 7, .c 947,
  .c 3, .c 5, .c 13, .c 3, .c 31, .c 7, .c 3, .p pv2 [pv2,pv107,pv10937], .c 11, .c 3,
  .p pv2 [pv2,pv2340521], .c 5, .c 3, .c 19,
]
private theorem h0572c05 : checkBlock 4680795 128 b0572c05 = true := by
  decide +kernel

private def b0572c06 : List Row := [
  .c 457, .c 3, .c 5, .c 439, .c 3, .c 7, .p pv3 [pv2,pv3,pv31,pv8389], .c 3, .c 1439, .c 17,
  .c 3, .c 1013, .c 5, .c 3, .c 13, .p pv7 [pv2,pv3,pv5,pv13003], .c 3, .c 5, .c 19, .c 3, .c 431,
  .c 29, .c 3, .p pv3 [pv2,pv7,pv83591], .c 421, .c 3, .c 7, .c 5, .c 3, .c 43, .c 1913, .c 3,
  .c 5, .c 7, .c 3, .c 23, .c 97, .c 3, .c 11, .c 37, .c 3, .c 89, .c 5, .c 3, .c 317, .c 2087,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv780191], .c 3, .c 29, .c 47, .c 3, .c 13, .c 7, .c 3, .c 19, .c 5,
  .c 3, .p pv3 [pv2,pv292573], .c 11, .c 3, .c 5, .c 167, .c 3, .c 443, .c 13, .c 3, .c 7, .c 601,
  .c 3, .c 11, .c 5, .c 3, .p pv17 [pv2,pv73,pv32063], .c 7, .c 3, .c 5, .c 173, .c 3,
  .p pv2 [pv2,pv5,pv468121], .c 23, .c 3, .c 31, .c 191, .c 3, .c 67, .c 5, .c 3, .c 7, .c 929,
  .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv37,pv3163], .c 7, .c 3, .c 47, .c 101, .c 3,
  .p pv2 [pv2,pv937,pv1249], .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 29, .c 3, .c 7, .c 17, .c 3,
  .c 19, .c 31, .c 3, .c 83, .c 5, .c 3, .p pv3 [pv2,pv757,pv773],
  .p pv2 [pv2,pv3,pv5,pv17,pv67,pv137], .c 3, .c 5, .p pv7 [pv2,pv3,pv19,pv29,pv59], .c 3,
  .p pv2 [pv2,pv5,pv13,pv277], .c 11, .c 3,
]
private theorem h0572c06 : checkBlock 4681051 128 b0572c06 = true := by
  decide +kernel

private def b0572c07 : List Row := [
  .c 17, .p pv2 [pv2,pv3,pv390109], .c 3, .c 7, .c 5, .c 3, .c 1093,
  .p pv17 [pv2,pv3,pv5,pv7,pv5573], .c 3, .c 5, .c 7, .c 3, .c 53, .c 331, .c 3,
  .p pv3 [pv2,pv11,pv53197], .c 13, .c 3, .p pv5 [pv2,pv821,pv2851], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv167191], .c 23, .c 3, .c 5, .c 67, .c 3, .p pv3 [pv2,pv5,pv163,pv359], .c 829,
  .c 3, .c 43, .c 7, .c 3, .c 523, .c 5, .c 3, .p pv2 [pv2,pv13,pv180053], .c 139, .c 3, .c 5,
  .c 179, .c 3, .c 11, .c 463, .c 3, .c 7, .p pv3 [pv2,pv3,pv780233], .c 3, .c 31, .c 5, .c 3,
  .c 17, .c 7, .c 3, .c 5, .c 13, .c 3, .c 41, .p pv3 [pv2,pv3,pv86693], .c 3, .c 137, .c 19,
  .c 3, .p pv3 [pv2,pv7,pv83597], .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .c 229, .c 3, .c 101, .c 7,
  .c 3, .c 11, .p pv3 [pv2,pv3,pv260081], .c 3, .p pv5 [pv2,pv37,pv41,pv1543], .c 5, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv5,pv29,pv5381], .c 3, .c 5, .c 17, .c 3, .c 7, .c 311, .c 3, .c 419, .c 23,
  .c 3, .c 1231, .c 5, .c 3, .c 29, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv61,pv12791], .c 3, .c 17,
  .p pv5 [pv2,pv3,pv11,pv23,pv257], .c 3, .p pv2 [pv2,pv7,pv167197], .p pv3 [pv2,pv3,pv780253],
  .c 3, .c 7, .c 5, .c 3, .c 47, .c 487, .c 3, .c 5, .c 7, .c 3, .c 313, .c 19, .c 3, .c 13,
  .c 1741, .c 3, .c 173, .c 5, .c 3, .p pv7 [pv2,pv7,pv23,pv31,pv67],
  .p pv41 [pv2,pv3,pv5,pv13,pv3001],
]
private theorem h0572c07 : checkBlock 4681307 128 b0572c07 = true := by
  decide +kernel

private def b0572c08 : List Row := [
  .c 3, .c 5, .c 11, .c 3, .c 107, .c 13, .c 3, .c 277, .c 7, .c 3, .c 157, .c 5, .c 3, .c 11,
  .c 59, .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv53,pv433], .c 3, .c 127, .p pv2 [pv2,pv3,pv260089],
  .c 3, .c 7, .p pv23 [pv2,pv3,pv97,pv2011], .c 3, .c 17, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5,
  .c 23, .c 3, .p pv11 [pv2,pv5,pv17,pv27539], .c 11, .c 3, .p pv2 [pv2,pv73,pv16033],
  .p pv3 [pv2,pv3,pv13,pv19], .c 3, .c 743, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 19, .c 3,
  .p pv2 [pv2,pv5,pv234083], .c 7, .c 3, .c 41, .c 71, .c 3, .c 23, .c 5, .c 3, .c 1303, .c 17,
  .c 3, .c 5, .c 1049, .c 3, .c 7, .p pv2 [pv2,pv3,pv67,pv647], .c 3, .p pv3 [pv2,pv23,pv6361],
  .c 11, .c 3, .c 13, .c 5, .c 3, .c 59, .c 43, .c 3, .c 5, .c 47, .c 3, .c 11, .c 449, .c 3,
  .p pv7 [pv2,pv7,pv173,pv1933], .c 13, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv2340869], .c 281,
  .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv61,pv307], .p pv7 [pv2,pv3,pv19,pv10267], .c 3,
  .p pv2 [pv2,pv89,pv13151], .c 67, .c 3, .p pv2 [pv2,pv103,pv22727], .c 5, .c 3, .c 257, .c 19,
  .c 3, .c 5, .c 79, .c 3, .c 13, .c 17, .c 3, .c 11, .c 7, .c 3, .p pv3 [pv2,pv191,pv383], .c 5,
  .c 3, .c 1217, .p pv13 [pv2,pv3,pv5,pv17], .c 3, .c 5, .c 13, .c 3, .c 23, .c 1789, .c 3, .c 7,
]
private theorem h0572c08 : checkBlock 4681563 128 b0572c08 = true := by
  decide +kernel

private def b0572c09 : List Row := [
  .c 367, .c 3, .c 409, .c 5, .c 3, .p pv2 [pv2,pv19,pv61603], .c 7, .c 3, .c 5, .c 31, .c 3,
  .p pv3 [pv2,pv5,pv43,pv1361], .p pv2 [pv2,pv3,pv11,pv70937], .c 3, .c 19, .c 163, .c 3, .c 11,
  .c 5, .c 3, .c 7, .c 53, .c 3, .c 5, .c 1831, .c 3, .p pv17 [pv2,pv5,pv468187], .c 7, .c 3,
  .c 109, .c 211, .c 3, .c 43, .c 5, .c 3, .p pv3 [pv2,pv146309], .p pv3 [pv2,pv3,pv5,pv52021],
  .c 3, .c 5, .c 11, .c 3, .c 7, .c 23, .c 3, .c 241, .p pv2 [pv2,pv3,pv7,pv11,pv563], .c 3,
  .c 41, .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv4877], .c 3, .c 5, .c 181, .c 3, .c 1459, .c 61,
  .c 3, .c 13, .p pv2 [pv2,pv3,pv780323], .c 3, .c 7, .c 5, .c 3, .c 23,
  .p pv23 [pv2,pv3,pv5,pv7,pv13], .c 3, .c 5, .c 7, .c 3, .c 19, .c 11, .c 3, .c 53, .c 43, .c 3,
  .p pv2 [pv2,pv23,pv50891], .c 5, .c 3, .c 701, .p pv11 [pv2,pv3,pv5,pv19,pv37], .c 3, .c 5,
  .c 17, .c 3, .p pv13 [pv2,pv5,pv468199], .p pv5 [pv2,pv3,pv7,pv29,pv31], .c 3,
  .p pv2 [pv2,pv11,pv97,pv1097], .c 7, .c 3, .p pv2 [pv2,pv13,pv180077], .c 5, .c 3,
  .p pv3 [pv2,pv585251], .p pv2 [pv2,pv3,pv5,pv239,pv653], .c 3, .c 5, .c 37, .c 3, .c 17, .c 31,
  .c 3, .c 7, .c 11, .c 3, .p pv3 [pv2,pv292627], .c 5, .c 3, .p pv13 [pv2,pv17,pv137707], .c 7,
  .c 3, .c 5, .c 823, .c 3, .c 11, .p pv2 [pv2,pv3,pv130057], .c 3, .c 101,
  .p pv2 [pv2,pv3,pv780343], .c 3, .c 59, .c 5, .c 3, .c 7, .c 103, .c 3,
]
private theorem h0572c09 : checkBlock 4681819 128 b0572c09 = true := by
  decide +kernel

private def b0572c10 : List Row := [
  .c 5, .c 41, .c 3, .p pv3 [pv2,pv5,pv13,pv2251], .c 7, .c 3, .c 23, .c 17, .c 3, .c 13, .c 5,
  .c 3, .c 197, .p pv2 [pv2,pv3,pv5,pv15607], .c 3, .c 5, .c 1409, .c 3, .c 7, .c 19, .c 3, .c 11,
  .c 13, .c 3, .c 17, .c 5, .c 3, .p pv3 [pv2,pv11,pv37,pv719], .c 277, .c 3, .c 5, .c 29, .c 3,
  .c 43, .p pv3 [pv2,pv3,pv467,pv557], .c 3, .c 31, .p pv2 [pv2,pv3,pv241,pv1619], .c 3, .c 7,
  .c 5, .c 3, .c 41, .c 11, .c 3, .c 5, .c 7, .c 3, .c 13, .p pv2 [pv2,pv3,pv11,pv79,pv449], .c 3,
  .c 61, .c 23, .c 3, .c 11, .c 5, .c 3, .c 19, .c 17, .c 3, .c 5, .c 13, .c 3, .c 89,
  .p pv2 [pv2,pv3,pv7,pv23,pv37,pv131], .c 3, .p pv5 [pv2,pv2341103], .c 7, .c 3, .c 107, .c 5,
  .c 3, .p pv2 [pv2,pv397,pv5897], .c 1259, .c 3, .c 5, .c 11, .c 3, .p pv7 [pv2,pv5,pv7,pv66889],
  .p pv5 [pv2,pv3,pv53,pv409], .c 3, .c 7, .c 37, .c 3, .p pv2 [pv2,pv17,pv137713], .c 5, .c 3,
  .c 11, .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv97547], .c 3, .p pv2 [pv2,pv5,pv11,pv21283], .c 1753,
  .c 3, .p pv2 [pv2,pv2341133], .c 373, .c 3, .p pv3 [pv2,pv7,pv20903], .c 5, .c 3, .c 7, .c 47,
  .c 3, .c 5, .c 97, .c 3, .c 509, .c 7, .c 3, .p pv3 [pv2,pv197,pv2971], .c 59, .c 3, .c 19,
  .c 5, .c 3, .p pv2 [pv2,pv71,pv16487], .c 29, .c 3, .c 5, .c 23, .c 3, .c 7, .c 41, .c 3, .c 13,
  .c 227,
]
private theorem h0572c10 : checkBlock 4682075 128 b0572c10 = true := by
  decide +kernel

private def b0572c11 : List Row := [
  .c 3, .c 31, .c 5, .c 3, .c 647, .c 19, .c 3, .c 5, .p pv3 [pv2,pv3,pv167,pv4673], .c 3,
  .p pv11 [pv2,pv5,pv37,pv2531], .c 13, .c 3, .p pv2 [pv2,pv7,pv43,pv3889], .c 11, .c 3, .c 7,
  .c 5, .c 3, .c 29, .p pv2 [pv2,pv3,pv5,pv7,pv11,pv2027], .c 3, .c 5, .c 7, .c 3, .c 11, .c 599,
  .c 3, .c 37, .c 241, .c 3, .c 389, .c 5, .c 3, .c 43, .p pv19 [pv2,pv3,pv5,pv1951], .c 3, .c 5,
  .c 317, .c 3, .p pv13 [pv2,pv5,pv468241], .c 617, .c 3, .c 19, .c 7, .c 3,
  .p pv5 [pv2,pv47,pv109,pv457], .c 5, .c 3, .c 17, .c 13, .c 3, .c 5, .c 359, .c 3, .c 769,
  .p pv2 [pv2,pv3,pv43,pv18149], .c 3, .c 7, .p pv11 [pv2,pv3,pv3613], .c 3, .c 1399, .c 5, .c 3,
  .c 839, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv260137], .c 3, .c 563, .c 887, .c 3, .c 401,
  .p pv19 [pv2,pv3,pv23,pv33931], .c 3, .c 13, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 17, .c 3,
  .c 23, .c 7, .c 3, .p pv2 [pv2,pv1439,pv1627], .c 13, .c 3, .c 11, .c 5, .c 3, .c 31, .c 71,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv780421], .c 3, .c 7, .c 349, .c 3, .p pv3 [pv2,pv585317], .c 1613,
  .c 3, .c 29, .c 5, .c 3, .c 883, .p pv11 [pv2,pv3,pv5,pv19,pv31,pv53], .c 3, .c 5, .c 11, .c 3,
  .c 13, .c 47, .c 3, .c 79, .c 19, .c 3, .c 7, .c 5, .c 3, .c 11, .c 31, .c 3, .c 5,
]
private theorem h0572c11 : checkBlock 4682331 128 b0572c11 = true := by
  decide +kernel

private def b0572c12 : List Row := [
  .c 7, .c 3, .c 173, .c 23, .c 3, .p pv2 [pv2,pv1170649], .c 17, .c 3, .c 53, .c 5, .c 3, .c 37,
  .c 83, .c 3, .c 5, .c 127, .c 3, .c 449, .c 11, .c 3, .c 1549, .c 7, .c 3, .c 17, .c 5, .c 3,
  .c 13, .c 107, .c 3, .c 5, .p pv3 [pv2,pv3,pv37,pv79,pv89], .c 3, .c 41, .c 59, .c 3, .c 7,
  .c 29, .c 3, .c 71, .c 5, .c 3, .c 199, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv390223], .c 3,
  .p pv7 [pv2,pv5,pv167,pv701], .c 19, .c 3, .p pv5 [pv2,pv2341343], .c 11, .c 3,
  .p pv2 [pv2,pv7,pv41,pv4079], .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 613, .c 3, .c 11, .c 7,
  .c 3, .c 13, .p pv3 [pv2,pv3,pv17,pv5101], .c 3, .c 211, .c 5, .c 3, .p pv3 [pv2,pv585341],
  .c 23, .c 3, .c 5, .p pv7 [pv2,pv3,pv31,pv1049], .c 3, .c 7, .c 13, .c 3, .c 191, .c 109, .c 3,
  .p pv3 [pv2,pv17,pv269], .c 5, .c 3, .c 19, .c 977, .c 3, .c 5, .c 31, .c 3, .c 59, .c 1039,
  .c 3, .c 11, .p pv17 [pv2,pv3,pv19,pv41077], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv11,pv106427],
  .p pv11 [pv2,pv3,pv5,pv7,pv7433], .c 3, .c 5, .c 7, .c 3, .c 283, .c 17, .c 3,
  .p pv5 [pv2,pv2341403], .c 677, .c 3, .c 439, .c 5, .c 3, .c 179, .c 11, .c 3, .c 5, .c 163,
  .c 3, .c 37, .c 29, .c 3, .c 17, .c 7, .c 3,
]
private theorem h0572c12 : checkBlock 4682587 128 b0572c12 = true := by
  decide +kernel

private def b0572c13 : List Row := [
  .c 11, .c 5, .c 3, .p pv3 [pv2,pv61,pv2399], .p pv3 [pv2,pv3,pv5,pv31219], .c 3, .c 5, .c 131,
  .c 3, .p pv2 [pv2,pv5,pv7,pv13,pv31,pv83], .p pv3 [pv2,pv3,pv29,pv8971], .c 3, .c 7, .c 23,
  .c 3, .c 13, .c 5, .c 3, .c 457, .c 7, .c 3, .c 5, .c 11, .c 3, .c 29, .c 2053, .c 3, .c 41,
  .c 13, .c 3, .p pv5 [pv2,pv7,pv334493], .c 5, .c 3, .c 7, .c 19, .c 3, .c 5,
  .p pv29 [pv2,pv3,pv7,pv18583], .c 3, .c 53, .c 7, .c 3, .p pv5 [pv2,pv2341463],
  .p pv7 [pv2,pv3,pv97561], .c 3, .p pv2 [pv2,pv577,pv2029], .c 5, .c 3, .c 17, .c 383, .c 3,
  .c 5, .c 71, .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv17,pv4051],
  .p pv7 [pv2,pv3,pv7,pv43,pv2593], .c 3, .c 151, .c 5, .c 3, .c 643, .c 1381, .c 3, .c 5, .c 13,
  .c 3, .c 1307, .c 1327, .c 3, .c 19, .p pv7 [pv2,pv3,pv131,pv331], .c 3, .c 7, .c 5, .c 3,
  .p pv29 [pv2,pv103,pv127,pv179], .c 43, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv227,pv2063],
  .c 181, .c 3, .p pv3 [pv2,pv13,pv37,pv1217], .c 11, .c 3, .c 73, .c 5, .c 3, .c 13, .c 61, .c 3,
  .c 5, .p pv13 [pv2,pv3,pv29,pv13457], .c 3, .c 11, .c 739, .c 3, .p pv5 [pv2,pv31,pv75533],
  .c 7, .c 3, .c 23, .c 5, .c 3, .c 113, .c 41, .c 3, .c 5, .c 101, .c 3, .c 137,
  .p pv11 [pv2,pv3,pv24391], .c 3, .c 7, .p pv3 [pv2,pv3,pv260171], .c 3,
  .p pv2 [pv2,pv19,pv123239], .c 5, .c 3, .c 71, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv73],
]
private theorem h0572c13 : checkBlock 4682843 128 b0572c13 = true := by
  decide +kernel

private def b0572c14 : List Row := [
  .c 3, .c 19, .p pv3 [pv2,pv3,pv41,pv19037], .c 3, .c 11, .c 17, .c 3, .c 1871, .c 5, .c 3, .c 7,
  .p pv17 [pv2,pv3,pv5,pv13,pv19,pv79], .c 3, .c 5, .c 37, .c 3, .p pv2 [pv2,pv5,pv43,pv10891],
  .c 7, .c 3, .c 733, .c 19, .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv1170787], .c 11, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv390263], .c 3, .c 7, .c 419, .c 3, .p pv5 [pv2,pv67,pv34949], .c 73, .c 3,
  .c 11, .c 5, .c 3, .p pv2 [pv2,pv2341589], .c 29, .c 3, .c 5, .p pv2 [pv2,pv3,pv53,pv4909],
  .c 3, .c 23, .p pv5 [pv2,pv3,pv83,pv2351], .c 3, .p pv2 [pv2,pv7,pv19,pv8803], .c 79, .c 3,
  .c 7, .c 5, .c 3, .p pv3 [pv2,pv137,pv4273], .c 13, .c 3, .c 5, .c 7, .c 3, .c 47, .c 223, .c 3,
  .p pv2 [pv2,pv2341613], .p pv7 [pv2,pv3,pv11,pv17,pv2087], .c 3, .c 67, .c 5, .c 3, .c 11,
  .c 263, .c 3, .c 5, .p pv3 [pv2,pv3,pv431,pv1811], .c 3, .c 353, .c 19, .c 3, .c 97, .c 7, .c 3,
  .c 13, .c 5, .c 3, .c 89, .p pv13 [pv2,pv3,pv5,pv156109], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv10007], .c 3, .c 197, .c 11, .c 3, .c 7, .c 13, .c 3,
  .p pv2 [pv2,pv53,pv22091], .c 5, .c 3, .c 461, .c 7, .c 3, .c 5, .c 41, .c 3, .c 257, .c 17,
  .c 3, .p pv2 [pv2,pv11,pv163,pv653], .c 331, .c 3, .p pv2 [pv2,pv7,pv6827], .c 5, .c 3, .c 7,
  .c 683, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv61,pv457], .c 3, .c 13, .c 7, .c 3, .c 17, .c 11,
  .c 3, .c 241,
]
private theorem h0572c14 : checkBlock 4683099 128 b0572c14 = true := by
  decide +kernel

private def b0572c15 : List Row := [
  .c 5, .c 3, .c 1987, .c 59, .c 3, .c 5, .c 13, .c 3, .c 7, .c 71, .c 3, .p pv3 [pv2,pv292711],
  .c 127, .c 3, .p pv5 [pv2,pv11,pv212881], .c 5, .c 3, .c 41, .p pv11 [pv2,pv3,pv5,pv107,pv1459],
  .c 3, .c 5, .c 61, .c 3, .c 1163, .c 109, .c 3, .c 673, .c 47, .c 3, .c 7, .c 5, .c 3, .c 13,
  .c 23, .c 3, .c 5, .c 7, .c 3, .c 43, .c 503, .c 3, .c 11, .c 569, .c 3, .c 19, .c 5, .c 3,
  .c 17, .c 53, .c 3, .c 5, .c 1637, .c 3, .c 73, .p pv3 [pv2,pv3,pv7,pv19,pv5869], .c 3, .c 23,
  .c 7, .c 3, .p pv3 [pv2,pv292717], .c 5, .c 3, .c 59, .c 11, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv677,pv1153], .c 3, .p pv2 [pv2,pv5,pv7,pv23,pv2909],
  .p pv2 [pv2,pv3,pv11,pv11827], .c 3, .c 7, .p pv2 [pv2,pv3,pv780583], .c 3, .c 11, .c 5, .c 3,
  .c 577, .c 7, .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv3659], .c 13, .c 3,
  .p pv5 [pv2,pv2341763], .c 29, .c 3, .c 233, .c 5, .c 3, .c 7, .c 1493, .c 3, .c 5, .c 11, .c 3,
  .c 17, .c 7, .c 3, .c 19, .c 23, .c 3, .p pv2 [pv2,pv13,pv180137], .c 5, .c 3, .c 11, .c 37,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv19,pv10271], .c 3, .c 7, .c 2039, .c 3, .c 29,
  .p pv2 [pv2,pv3,pv7,pv13,pv4289], .c 3, .c 601, .c 5, .c 3, .p pv7 [pv2,pv691,pv3389], .c 13,
  .c 3, .c 5, .c 73, .c 3,
]
private theorem h0572c15 : checkBlock 4683355 128 b0572c15 = true := by
  decide +kernel

private def b0572c16 : List Row := [
  .p pv2 [pv2,pv5,pv53,pv8837], .c 11, .c 3, .p pv3 [pv2,pv7,pv29,pv103], .c 17, .c 3, .c 7, .c 5,
  .c 3, .c 173, .p pv3 [pv2,pv3,pv5,pv7,pv22303], .c 3, .c 5, .c 7, .c 3, .c 61, .c 131, .c 3,
  .c 617, .c 491, .c 3, .c 13, .c 5, .c 3, .c 1933, .p pv2 [pv2,pv3,pv5,pv251,pv311], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv13,pv31,pv149], .c 3, .c 19, .c 79, .c 3, .c 431, .c 7, .c 3, .c 239, .c 5,
  .c 3, .c 43, .c 47, .c 3, .c 5, .c 23, .c 3, .c 11, .c 29, .c 3, .c 7, .c 19, .c 3,
  .p pv3 [pv2,pv11,pv6653], .c 5, .c 3, .c 37, .c 7, .c 3, .c 5, .c 1787, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv29,pv43,pv313], .c 3, .c 113, .p pv2 [pv2,pv3,pv17,pv47,pv977], .c 3, .c 23,
  .c 5, .c 3, .c 7, .p pv19 [pv2,pv3,pv5,pv1249], .c 3, .c 5, .c 13, .c 3, .c 29, .c 7, .c 3,
  .c 11, .c 53, .c 3, .c 83, .c 5, .c 3, .p pv7 [pv2,pv11,pv211,pv1009], .c 157, .c 3, .c 5,
  .c 641, .c 3, .c 7, .c 37, .c 3, .p pv3 [pv2,pv13,pv90073], .c 41, .c 3, .c 89, .c 5, .c 3,
  .c 13, .c 11, .c 3, .c 5, .p pv7 [pv2,pv3,pv65053], .c 3, .c 31, .c 17, .c 3,
  .p pv2 [pv2,pv7,pv73,pv4583], .p pv7 [pv2,pv3,pv269,pv1451], .c 3, .c 7, .c 5, .c 3, .c 97,
  .p pv11 [pv2,pv3,pv5,pv7,pv17,pv41], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv113,pv829],
  .p pv2 [pv2,pv3,pv31,pv1399], .c 3, .c 17, .p pv2 [pv2,pv3,pv23,pv33941], .c 3, .c 199, .c 5,
]
private theorem h0572c16 : checkBlock 4683611 128 b0572c16 = true := by
  decide +kernel

private def b0572c17 : List Row := [
  .c 3, .c 151, .p pv23 [pv2,pv3,pv5,pv71,pv733], .c 3, .c 5, .c 11, .c 3, .c 23, .c 31, .c 3,
  .c 13, .c 7, .c 3, .c 137, .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv13,pv1201], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv29,pv997], .c 3, .c 251, .c 13, .c 3, .c 7, .p pv7 [pv2,pv3,pv19,pv181,pv227],
  .c 3, .p pv2 [pv2,pv41,pv239], .c 5, .c 3, .c 349, .c 7, .c 3, .c 5, .c 19, .c 3, .c 37, .c 11,
  .c 3, .c 43, .c 389, .c 3, .p pv3 [pv2,pv7,pv13,pv3217], .c 5, .c 3, .c 7, .c 547, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv229,pv487], .c 3, .c 311, .c 7, .c 3, .p pv3 [pv2,pv11,pv17,pv31,pv101],
  .c 769, .c 3, .p pv5 [pv2,pv2341991], .c 5, .c 3, .c 79, .c 13, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv23,pv5657], .c 3, .c 7, .p pv7 [pv2,pv3,pv780667], .c 3, .c 31, .c 11, .c 3,
  .c 19, .c 5, .c 3, .c 23, .c 367, .c 3, .c 5, .c 17, .c 3, .c 11, .c 43, .c 3, .c 67,
  .p pv3 [pv2,pv3,pv31,pv25183], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv292753], .c 19, .c 3, .c 5,
  .c 7, .c 3, .c 17, .c 937, .c 3, .c 47, .c 13, .c 3, .p pv3 [pv2,pv179,pv3271], .c 5, .c 3,
  .p pv11 [pv2,pv7,pv17,pv19681], .c 401, .c 3, .c 5, .c 53, .c 3, .p pv2 [pv2,pv5,pv383,pv1223],
  .p pv2 [pv2,pv3,pv7,pv55763], .c 3, .c 11, .c 7, .c 3, .p pv5 [pv2,pv2342051], .c 5, .c 3,
  .c 29, .c 23, .c 3, .c 5, .p pv2 [pv2,pv3,pv390343], .c 3, .c 13,
]
private theorem h0572c17 : checkBlock 4683867 128 b0572c17 = true := by
  decide +kernel

private def b0572c18 : List Row := [
  .p pv3 [pv2,pv3,pv86743], .c 3, .c 7, .c 17, .c 3, .c 1627, .c 5, .c 3, .c 107, .c 7, .c 3,
  .c 5, .c 13, .c 3, .p pv17 [pv2,pv5,pv93683], .c 347, .c 3, .c 23, .c 89, .c 3, .c 11, .c 5,
  .c 3, .c 7, .c 67, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv1549], .c 3,
  .p pv3 [pv2,pv5,pv17,pv23,pv599], .c 7, .c 3, .c 59, .c 113, .c 3, .c 31, .c 5, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv5,pv37,pv211], .c 3, .c 5, .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv13,pv10009],
  .c 3, .c 1759, .c 607, .c 3, .p pv5 [pv2,pv19,pv123269], .c 5, .c 3, .c 11, .c 17, .c 3, .c 5,
  .c 37, .c 3, .c 19, .p pv3 [pv2,pv3,pv780707], .c 3, .c 887, .c 23, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv2342129], .c 199, .c 3, .c 5, .c 7, .c 3, .c 83, .c 11, .c 3, .c 13, .c 19, .c 3,
  .c 29, .c 5, .c 3, .c 691, .c 41, .c 3, .c 5, .p pv5 [pv2,pv3,pv71,pv2749], .c 3,
  .p pv2 [pv2,pv5,pv139,pv337], .c 13, .c 3, .c 1051, .c 7, .c 3, .p pv3 [pv2,pv29,pv61,pv331],
  .c 5, .c 3, .p pv17 [pv2,pv23,pv101833], .c 173, .c 3, .c 5, .c 509, .c 3, .c 2081, .c 17, .c 3,
  .c 7, .c 11, .c 3, .c 1019, .c 5, .c 3, .c 47, .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv130121],
  .c 3, .c 11, .c 709, .c 3, .c 17, .c 1709, .c 3, .c 41, .c 5, .c 3,
]
private theorem h0572c18 : checkBlock 4684123 128 b0572c18 = true := by
  decide +kernel

private def b0572c19 : List Row := [
  .c 7, .c 13, .c 3, .c 5, .c 23, .c 3, .p pv17 [pv2,pv5,pv468439], .c 7, .c 3, .c 2027, .c 29,
  .c 3, .c 1481, .c 5, .c 3, .c 157, .c 149, .c 3, .c 5, .c 449, .c 3, .c 7, .c 59, .c 3, .c 11,
  .c 131, .c 3, .c 13, .c 5, .c 3, .c 67, .c 31, .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv6673], .c 3,
  .p pv2 [pv2,pv5,pv19,pv4931], .c 487, .c 3, .c 29, .c 13, .c 3, .c 7, .c 5, .c 3, .c 17, .c 11,
  .c 3, .c 5, .c 7, .c 3, .c 101, .c 73, .c 3, .p pv5 [pv2,pv17,pv29,pv4751],
  .p pv7 [pv2,pv3,pv19,pv10273], .c 3, .c 11, .c 5, .c 3, .c 283, .p pv2 [pv2,pv3,pv5,pv347],
  .c 3, .c 5, .c 19, .c 3, .c 13, .c 307, .c 3, .c 167, .c 7, .c 3, .p pv2 [pv2,pv127,pv18443],
  .c 5, .c 3, .p pv3 [pv2,pv113,pv2591], .c 1693, .c 3, .c 5, .c 11, .c 3, .c 59, .c 103, .c 3,
  .c 7, .c 43, .c 3, .p pv3 [pv2,pv585569], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 107, .c 3,
  .c 17, .c 29, .c 3, .c 569, .p pv2 [pv2,pv3,pv41,pv137,pv139], .c 3, .c 19, .c 5, .c 3, .c 7,
  .c 359, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv31,pv257], .c 3, .p pv3 [pv2,pv5,pv59,pv397], .c 7,
  .c 3, .c 37, .c 179, .c 3, .p pv2 [pv2,pv499,pv2347], .c 5, .c 3, .c 41, .c 19, .c 3, .c 5,
  .c 31, .c 3, .c 7, .p pv5 [pv2,pv3,pv195193],
]
private theorem h0572c19 : checkBlock 4684379 128 b0572c19 = true := by
  decide +kernel

private def b0572c20 : List Row := [
  .c 3, .c 337, .c 17, .c 3, .c 331, .c 5, .c 3, .c 127, .c 71, .c 3, .c 5, .c 191, .c 3,
  .p pv2 [pv2,pv5,pv29,pv41,pv197], .c 23, .c 3, .c 13, .c 11, .c 3, .c 7, .c 5, .c 3, .c 829,
  .c 37, .c 3, .c 5, .c 7, .c 3, .c 11, .c 13, .c 3, .c 19, .p pv3 [pv2,pv3,pv233,pv1117], .c 3,
  .p pv5 [pv2,pv11,pv73,pv2917], .c 5, .c 3, .c 23, .c 109, .c 3, .c 5, .c 139, .c 3, .c 43,
  .c 53, .c 3, .c 389, .c 7, .c 3, .p pv2 [pv2,pv13,pv23,pv3917], .c 5, .c 3, .c 61, .c 17, .c 3,
  .c 5, .c 29, .c 3, .c 31, .c 673, .c 3, .c 7, .p pv3 [pv2,pv3,pv13,pv17,pv3533], .c 3,
  .p pv2 [pv2,pv2342381], .c 5, .c 3, .c 83, .c 7, .c 3, .c 5, .c 59, .c 3, .c 107, .c 41, .c 3,
  .c 1009, .p pv2 [pv2,pv3,pv179,pv727], .c 3, .c 71, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 43,
  .c 3, .c 19, .c 7, .c 3, .p pv3 [pv2,pv292801], .c 47, .c 3, .c 11, .c 5, .c 3, .c 37, .c 659,
  .c 3, .c 5, .c 1723, .c 3, .c 7, .c 17, .c 3, .c 23, .c 13, .c 3, .c 257, .c 5, .c 3,
  .p pv2 [pv2,pv79,pv149,pv199], .c 61, .c 3, .c 5, .c 11, .c 3, .c 89, .p pv5 [pv2,pv3,pv195203],
  .c 3, .c 17, .p pv3 [pv2,pv3,pv11,pv239], .c 3, .c 7, .c 5, .c 3, .c 11,
]
private theorem h0572c20 : checkBlock 4684635 128 b0572c20 = true := by
  decide +kernel

private def b0572c21 : List Row := [
  .p pv2 [pv2,pv3,pv5,pv7,pv3187], .c 3, .c 5, .c 7, .c 3, .c 13, .c 37, .c 3,
  .p pv2 [pv2,pv19,pv31,pv41,pv97], .p pv2 [pv2,pv3,pv67,pv5827], .c 3, .c 47, .c 5, .c 3, .c 809,
  .c 29, .c 3, .c 5, .c 13, .c 3, .c 233, .c 11, .c 3, .c 31, .c 7, .c 3, .c 317, .c 5, .c 3,
  .p pv2 [pv2,pv953,pv1229], .p pv3 [pv2,pv3,pv5,pv29,pv359], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv390413], .c 3, .c 2029, .c 19, .c 3, .c 7, .p pv17 [pv2,pv3,pv31,pv2099],
  .c 3, .p pv2 [pv2,pv1171243], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv101,pv859],
  .c 3, .p pv17 [pv2,pv5,pv468499], .p pv5 [pv2,pv3,pv13,pv1877], .c 3, .c 397, .c 11, .c 3,
  .c 97, .c 5, .c 3, .c 7, .c 787, .c 3, .c 5, .c 2003, .c 3, .c 11, .c 7, .c 3, .c 1181, .c 41,
  .c 3, .p pv3 [pv2,pv11,pv53239], .c 5, .c 3, .c 19, .c 53, .c 3, .c 5, .c 17, .c 3, .c 7,
  .c 227, .c 3, .c 13, .p pv2 [pv2,pv3,pv7,pv19,pv103], .c 3, .p pv5 [pv2,pv919,pv2549], .c 5,
  .c 3, .c 641, .p pv3 [pv2,pv3,pv5,pv13,pv41,pv293], .c 3, .c 5, .c 19, .c 3, .c 17, .c 13, .c 3,
  .c 11, .c 1187, .c 3, .c 7, .c 5, .c 3, .c 479, .c 47, .c 3, .c 5, .c 7, .c 3, .c 41, .c 281,
  .c 3, .c 239, .p pv3 [pv2,pv3,pv780853], .c 3, .c 23, .c 5, .c 3, .p pv3 [pv2,pv7,pv83663],
  .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv97607], .c 3, .p pv3 [pv2,pv5,pv73,pv3209], .c 461, .c 3,
]
private theorem h0572c21 : checkBlock 4684891 128 b0572c21 = true := by
  decide +kernel

private def b0572c22 : List Row := [
  .c 53, .c 7, .c 3, .c 11, .c 5, .c 3, .c 613, .c 13, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv17,pv61,pv251], .c 3, .c 1171, .c 269, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv277,pv2819], .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv101,pv11597], .c 7, .c 3,
  .c 5, .c 11, .c 3, .p pv7 [pv2,pv5,pv13,pv17,pv53], .p pv2 [pv2,pv3,pv28921], .c 3,
  .p pv5 [pv2,pv113,pv20731], .c 107, .c 3, .c 13, .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv26029], .c 3, .c 5, .c 61, .c 3, .p pv13 [pv2,pv5,pv11,pv191,pv223],
  .c 7, .c 3, .c 43, .c 13, .c 3, .c 67, .c 5, .c 3, .c 59, .c 17, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv109,pv199], .c 3, .c 7, .c 11, .c 3, .c 19, .c 29, .c 3, .c 37, .c 5, .c 3,
  .c 1451, .c 241, .c 3, .c 5, .c 1097, .c 3, .c 13, .c 593, .c 3, .c 313,
  .p pv3 [pv2,pv3,pv29,pv26927], .c 3, .c 7, .c 5, .c 3, .c 31, .c 337, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv117133], .c 43, .c 3, .c 29, .c 11, .c 3, .p pv2 [pv2,pv79,pv14827], .c 5,
  .c 3, .c 823, .p pv23 [pv2,pv3,pv5,pv11,pv31,pv229], .c 3, .c 5, .c 37, .c 3, .c 11, .c 17,
  .c 3, .c 41, .c 7, .c 3, .c 293, .c 5, .c 3, .c 13, .c 31, .c 3, .c 5, .c 67, .c 3, .c 19,
  .c 47, .c 3, .c 7, .p pv19 [pv2,pv3,pv390449], .c 3, .p pv3 [pv2,pv292837], .c 5, .c 3, .c 23,
  .c 7,
]
private theorem h0572c22 : checkBlock 4685147 128 b0572c22 = true := by
  decide +kernel

private def b0572c23 : List Row := [
  .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv70991], .c 3, .c 79, .p pv5 [pv2,pv3,pv53,pv139], .c 3,
  .c 11, .c 19, .c 3, .c 107, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv47,pv3323], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv18593], .c 3, .p pv7 [pv2,pv5,pv7321], .c 7, .c 3, .c 13,
  .p pv11 [pv2,pv3,pv197,pv991], .c 3, .c 223, .c 5, .c 3, .p pv2 [pv2,pv37,pv63317], .c 11, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv211,pv3701], .c 3, .c 7, .c 13, .c 3, .c 47,
  .p pv13 [pv2,pv3,pv7,pv15937], .c 3, .c 11, .c 5, .c 3, .c 17, .c 23, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv195229], .c 3, .c 29, .c 71, .c 3, .c 227, .p pv2 [pv2,pv3,pv157,pv829], .c 3,
  .c 7, .c 5, .c 3, .c 167, .c 41, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv29,pv107,pv151],
  .c 19, .c 3, .c 23, .p pv2 [pv2,pv3,pv11,pv13,pv43,pv127], .c 3, .c 1993, .c 5, .c 3, .c 11,
  .c 13, .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv11,pv23,pv463], .c 797, .c 3,
  .p pv5 [pv2,pv2342783], .c 7, .c 3, .c 103, .c 5, .c 3, .p pv2 [pv2,pv67,pv73,pv479], .c 43,
  .c 3, .c 5, .c 1321, .c 3, .c 17, .c 11, .c 3, .c 7, .c 83, .c 3, .c 13, .c 5, .c 3, .c 19,
  .c 7, .c 3, .c 5, .c 29, .c 3, .c 457, .p pv13 [pv2,pv3,pv383,pv2039], .c 3, .c 2089, .c 13,
  .c 3, .p pv5 [pv2,pv7,pv10459], .c 5, .c 3, .c 7, .p pv19 [pv2,pv3,pv5,pv39047], .c 3, .c 5,
  .c 19, .c 3, .c 73, .c 7, .c 3, .p pv3 [pv2,pv293,pv1999],
]
private theorem h0572c23 : checkBlock 4685403 128 b0572c23 = true := by
  decide +kernel

private def b0572c24 : List Row := [
  .c 11, .c 3, .p pv5 [pv2,pv59,pv39709], .c 5, .c 3, .p pv2 [pv2,pv13,pv251,pv359], .c 691, .c 3,
  .c 5, .c 53, .c 3, .c 7, .c 179, .c 3, .p pv5 [pv2,pv167,pv14029], .p pv43 [pv2,pv3,pv7,pv1033],
  .c 3, .c 17, .c 5, .c 3, .p pv7 [pv2,pv23,pv101863], .p pv29 [pv2,pv3,pv5,pv15619], .c 3, .c 5,
  .c 13, .c 3, .c 269, .p pv5 [pv2,pv3,pv31,pv47,pv67], .c 3, .c 37, .p pv3 [pv2,pv3,pv780953],
  .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv181,pv809], .p pv3 [pv2,pv3,pv5,pv7,pv53,pv421], .c 3,
  .c 5, .c 7, .c 3, .c 307, .c 31, .c 3, .c 11, .p pv2 [pv2,pv3,pv390479], .c 3, .c 43, .c 5,
  .c 3, .c 13, .c 17, .c 3, .c 5, .c 23, .c 3, .c 113, .p pv5 [pv2,pv3,pv7,pv13,pv613], .c 3,
  .p pv3 [pv2,pv61,pv4801], .c 7, .c 3, .c 53, .c 5, .c 3, .p pv2 [pv2,pv1171447], .c 11, .c 3,
  .c 5, .c 73, .c 3, .c 109, .c 191, .c 3, .c 7, .p pv13 [pv2,pv3,pv41,pv2381], .c 3, .c 11, .c 5,
  .c 3, .c 1213, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv780971], .c 3, .p pv13 [pv2,pv5,pv619,pv757],
  .p pv5 [pv2,pv3,pv151,pv431], .c 3, .c 13, .c 43, .c 3, .p pv2 [pv2,pv7,pv197,pv1699], .c 5,
  .c 3, .c 7, .c 107, .c 3, .c 5, .c 11, .c 3, .c 271, .c 7, .c 3, .c 31,
  .p pv2 [pv2,pv3,pv11,pv11833], .c 3, .p pv3 [pv2,pv292867], .c 5, .c 3, .c 11, .c 257, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv439,pv593], .c 3, .c 7, .p pv2 [pv2,pv3,pv390491], .c 3, .c 17, .c 223,
  .c 3, .p pv5 [pv2,pv13,pv37,pv4871], .c 5, .c 3, .c 181, .p pv67 [pv2,pv3,pv5,pv109,pv1433],
  .c 3,
]
private theorem h0572c24 : checkBlock 4685659 128 b0572c24 = true := by
  decide +kernel

private def b0572c25 : List Row := [
  .c 5, .p pv2 [pv2,pv3,pv390493], .c 3, .p pv3 [pv2,pv5,pv29287], .c 11, .c 3,
  .p pv11 [pv2,pv7,pv433,pv773], .c 31, .c 3, .c 7, .c 5, .c 3, .c 37, .c 13, .c 3, .c 5, .c 7,
  .c 3, .c 19, .p pv5 [pv2,pv3,pv12203], .c 3, .c 59, .c 61, .c 3, .p pv2 [pv2,pv2342981], .c 5,
  .c 3, .p pv3 [pv2,pv7,pv43,pv139], .p pv2 [pv2,pv3,pv5,pv19,pv8221], .c 3, .c 5, .c 599, .c 3,
  .c 919, .c 151, .c 3, .p pv2 [pv2,pv2342993], .c 7, .c 3, .c 13, .c 5, .c 3, .c 17, .c 131,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv60077], .c 3, .c 11, .c 37, .c 3, .c 7, .c 13, .c 3, .c 29,
  .c 5, .c 3, .p pv2 [pv2,pv89,pv13163], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv390503], .c 3, .c 47,
  .c 23, .c 3, .c 67, .c 1373, .c 3, .c 31, .c 5, .c 3, .c 7, .c 1297, .c 3, .c 5, .c 17, .c 3,
  .c 13, .c 7, .c 3, .c 11, .p pv17 [pv2,pv3,pv457,pv1709], .c 3, .p pv2 [pv2,pv967,pv2423], .c 5,
  .c 3, .c 23, .c 1543, .c 3, .c 5, .c 13, .c 3, .c 7, .c 19, .c 3, .c 139, .c 499, .c 3,
  .p pv3 [pv2,pv23,pv6367], .c 5, .c 3, .p pv7 [pv2,pv17,pv137827], .c 11, .c 3, .c 5, .c 1601,
  .c 3, .p pv2 [pv2,pv5,pv468613], .p pv5 [pv2,pv3,pv11,pv131,pv271], .c 3,
  .p pv3 [pv2,pv7,pv13,pv41,pv157], .c 29, .c 3, .c 7, .c 5, .c 3, .c 13, .c 421, .c 3, .c 5,
  .c 7, .c 3, .c 37, .p pv3 [pv2,pv3,pv13,pv73,pv823], .c 3, .c 97, .c 17,
]
private theorem h0572c25 : checkBlock 4685915 128 b0572c25 = true := by
  decide +kernel

private def b0572c26 : List Row := [
  .c 3, .c 127, .c 5, .c 3, .c 19, .c 23, .c 3, .c 5, .c 11, .c 3, .c 103, .c 59, .c 3, .c 29,
  .c 7, .c 3, .c 17, .c 5, .c 3, .c 11, .c 317, .c 3, .c 5, .c 19, .c 3, .c 647, .c 113, .c 3,
  .c 7, .c 47, .c 3, .c 193, .c 5, .c 3, .c 31, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv139,pv1873],
  .c 3, .c 199, .c 11, .c 3, .p pv3 [pv2,pv229,pv1279], .c 41, .c 3, .c 83, .c 5, .c 3, .c 7,
  .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv47,pv1187], .c 3, .p pv3 [pv2,pv5,pv79,pv1483], .c 7,
  .c 3, .p pv5 [pv2,pv11,pv277,pv769], .p pv37 [pv2,pv3,pv17,pv5743], .c 3, .c 19, .c 5, .c 3,
  .c 101, .c 31, .c 3, .c 5, .p pv2 [pv2,pv3,pv781051], .c 3, .c 7, .c 29, .c 3,
  .p pv2 [pv2,pv1171579], .c 11, .c 3, .c 47, .c 5, .c 3, .c 233, .c 13, .c 3, .c 5, .c 829, .c 3,
  .c 11, .p pv3 [pv2,pv3,pv23,pv29,pv1171], .c 3, .p pv2 [pv2,pv7,pv37,pv83,pv109],
  .p pv2 [pv2,pv3,pv149,pv2621], .c 3, .c 7, .c 5, .c 3, .c 79, .c 97, .c 3, .c 5, .c 7, .c 3,
  .c 29, .c 17, .c 3, .p pv3 [pv2,pv191,pv3067], .p pv11 [pv2,pv3,pv781063], .c 3, .c 13, .c 5,
  .c 3, .p pv2 [pv2,pv7,pv19,pv23,pv383], .c 1531, .c 3, .c 5, .c 103, .c 3, .c 487, .c 271, .c 3,
  .c 11, .c 7, .c 3, .c 163, .c 5, .c 3, .c 53, .c 251, .c 3, .c 5,
]
private theorem h0572c26 : checkBlock 4686171 128 b0572c26 = true := by
  decide +kernel

private def b0572c27 : List Row := [
  .c 127, .c 3, .p pv7 [pv2,pv5,pv7,pv66949], .c 197, .c 3, .c 7, .c 991, .c 3,
  .p pv2 [pv2,pv719,pv3259], .c 5, .c 3, .c 67, .c 7, .c 3, .c 5, .c 23, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv11,pv23669], .c 3, .p pv2 [pv2,pv2343233], .c 907, .c 3, .c 11, .c 5, .c 3,
  .c 7, .p pv37 [pv2,pv3,pv5,pv23,pv283], .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv661,pv709],
  .c 7, .c 3, .c 71, .p pv2 [pv2,pv3,pv9643], .c 3, .c 23, .c 5, .c 3, .c 17, .c 47, .c 3, .c 5,
  .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv781087], .c 3, .c 43, .p pv17 [pv2,pv3,pv7,pv11,pv317],
  .c 3, .p pv2 [pv2,pv1171633], .c 5, .c 3, .c 11, .p pv11 [pv2,pv3,pv5,pv19,pv4111], .c 3, .c 5,
  .c 59, .c 3, .c 239, .p pv5 [pv2,pv3,pv13,pv1669], .c 3, .p pv3 [pv2,pv7,pv23911], .c 19, .c 3,
  .c 7, .c 5, .c 3, .c 61, .p pv3 [pv2,pv3,pv5,pv7,pv43,pv173], .c 3, .c 5, .c 7, .c 3, .c 653,
  .c 11, .c 3, .c 41, .p pv2 [pv2,pv3,pv130183], .c 3, .p pv3 [pv2,pv18307], .c 5, .c 3,
  .p pv7 [pv2,pv7,pv557,pv601], .p pv7 [pv2,pv3,pv5,pv73,pv107], .c 3, .c 5, .c 157, .c 3, .c 17,
  .c 43, .c 3, .c 13, .c 7, .c 3, .p pv5 [pv2,pv2343311], .c 5, .c 3, .c 331, .c 53, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv390553], .c 3, .c 23, .c 13, .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv47,pv97,pv257], .c 5, .c 3, .c 337, .c 7, .c 3, .c 5, .c 1217, .c 3, .c 11, .c 19,
  .c 3, .p pv2 [pv2,pv1171669], .c 17, .c 3,
]
private theorem h0572c27 : checkBlock 4686427 128 b0572c27 = true := by
  decide +kernel

private def b0572c28 : List Row := [
  .c 541, .c 5, .c 3, .c 7, .c 61, .c 3, .c 5, .p pv13 [pv2,pv3,pv7,pv17,pv547], .c 3,
  .p pv2 [pv2,pv5,pv46867], .c 7, .c 3, .c 107, .p pv23 [pv2,pv3,pv13,pv2311], .c 3, .c 17, .c 5,
  .c 3, .c 29, .c 13, .c 3, .c 5, .c 241, .c 3, .c 7, .c 23, .c 3, .c 11, .c 163, .c 3, .c 173,
  .c 5, .c 3, .c 19, .c 41, .c 3, .c 5, .c 179, .c 3, .c 83, .c 283, .c 3, .c 1063, .c 811, .c 3,
  .c 7, .c 5, .c 3, .c 23, .c 11, .c 3, .c 5, .c 7, .c 3, .c 223, .c 47, .c 3, .c 31, .c 13, .c 3,
  .c 11, .c 5, .c 3, .c 103, .p pv2 [pv2,pv3,pv5,pv156227], .c 3, .c 5, .p pv5 [pv2,pv3,pv48821],
  .c 3, .p pv2 [pv2,pv5,pv234341], .c 1439, .c 3, .c 37, .c 7, .c 3, .c 41, .c 5, .c 3,
  .p pv17 [pv2,pv13,pv180263], .p pv37 [pv2,pv3,pv5,pv47,pv277], .c 3, .c 5, .c 11, .c 3, .c 13,
  .c 569, .c 3, .c 7, .c 31, .c 3, .c 19, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 13, .c 3,
  .p pv3 [pv2,pv5,pv11,pv2663], .c 17, .c 3, .c 47, .c 151, .c 3, .c 29, .c 5, .c 3, .c 7, .c 19,
  .c 3, .c 5, .c 137, .c 3, .p pv13 [pv2,pv5,pv468691], .c 7, .c 3, .c 17,
  .p pv23 [pv2,pv3,pv67,pv89,pv131], .c 3, .c 71, .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv17359],
  .c 3, .c 5, .p pv5 [pv2,pv3,pv179,pv1091],
]
private theorem h0572c28 : checkBlock 4686683 128 b0572c28 = true := by
  decide +kernel

private def b0572c29 : List Row := [
  .c 3, .c 7, .c 97, .c 3, .p pv2 [pv2,pv11,pv213043], .c 53, .c 3, .c 863, .c 5, .c 3, .c 1997,
  .p pv7 [pv2,pv3,pv5,pv59,pv331], .c 3, .c 5, .p pv5 [pv2,pv3,pv260387], .c 3, .c 577,
  .p pv2 [pv2,pv3,pv390581], .c 3, .c 19, .c 11, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv1171747],
  .c 79, .c 3, .c 5, .c 7, .c 3, .c 11, .p pv2 [pv2,pv3,pv17,pv53], .c 3, .c 13, .c 23, .c 3,
  .p pv2 [pv2,pv11,pv37,pv2879], .c 5, .c 3, .c 17, .p pv7 [pv2,pv3,pv5,pv13,pv2003], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv781171], .c 3, .p pv13 [pv2,pv5,pv468703], .c 13, .c 3,
  .p pv3 [pv2,pv17,pv68927], .c 7, .c 3, .c 43, .c 5, .c 3, .c 37, .p pv3 [pv2,pv3,pv5,pv31247],
  .c 3, .c 5, .c 61, .c 3, .c 389, .p pv3 [pv2,pv3,pv127,pv6151], .c 3, .c 7,
  .p pv11 [pv2,pv3,pv619,pv631], .c 3, .p pv3 [pv2,pv13,pv19,pv593], .c 5, .c 3, .c 41, .c 7,
  .c 3, .c 5, .c 17, .c 3, .c 19, .c 83, .c 3, .p pv3 [pv2,pv29,pv89,pv227],
  .p pv2 [pv2,pv3,pv13,pv60091], .c 3, .p pv5 [pv2,pv7,pv334793], .c 5, .c 3, .c 7, .c 11, .c 3,
  .c 5, .c 277, .c 3, .c 17, .c 7, .c 3, .c 113, .c 19, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv17,pv31,pv4447], .p pv2 [pv2,pv3,pv5,pv191,pv409], .c 3, .c 5, .c 23, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv97649], .c 3, .c 797, .p pv3 [pv2,pv3,pv7,pv111599], .c 3, .c 13, .c 5, .c 3,
  .c 31, .p pv2 [pv2,pv3,pv5,pv23,pv6793], .c 3, .c 5, .c 11, .c 3, .c 137, .c 29, .c 3,
  .p pv2 [pv2,pv7,pv19,pv67,pv263], .c 13, .c 3, .c 7,
]
private theorem h0572c29 : checkBlock 4686939 128 b0572c29 = true := by
  decide +kernel

private def b0572c30 : List Row := [
  .c 5, .c 3, .c 11, .c 1747, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv11,pv42611],
  .p pv5 [pv2,pv3,pv29,pv13469], .c 3, .p pv3 [pv2,pv23,pv47,pv271], .c 139, .c 3, .c 17, .c 5,
  .c 3, .p pv2 [pv2,pv7,pv13,pv79,pv163], .c 31, .c 3, .c 5, .c 223, .c 3, .c 13, .c 11, .c 3,
  .p pv5 [pv2,pv199,pv11777], .c 7, .c 3, .c 67, .c 5, .c 3, .c 83, .c 233, .c 3, .c 5, .c 13,
  .c 3, .c 37, .p pv5 [pv2,pv3,pv65101], .c 3, .c 7, .c 467, .c 3, .p pv2 [pv2,pv2343641], .c 5,
  .c 3, .c 401, .c 7, .c 3, .c 5, .c 1193, .c 3, .c 43, .p pv3 [pv2,pv3,pv781217], .c 3, .c 79,
  .c 11, .c 3, .p pv5 [pv2,pv7,pv41851], .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv11,pv53,pv67],
  .c 3, .c 5, .c 109, .c 3, .c 11, .c 7, .c 3, .p pv3 [pv2,pv585917], .c 571, .c 3, .c 1433, .c 5,
  .c 3, .c 71, .p pv7 [pv2,pv3,pv5,pv31249], .c 3, .c 5, .c 19, .c 3, .c 7, .c 89, .c 3,
  .p pv5 [pv2,pv41,pv57163], .p pv13 [pv2,pv3,pv7,pv27901], .c 3, .c 53, .c 5, .c 3, .c 397,
  .c 509, .c 3, .c 5, .c 43, .c 3, .c 149, .c 17, .c 3, .c 11, .p pv3 [pv2,pv3,pv260411], .c 3,
  .c 7, .c 5, .c 3, .p pv3 [pv2,pv11,pv26633], .c 1021, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv71,pv3301], .c 13, .c 3, .c 17, .c 683, .c 3, .c 19, .c 5, .c 3,
  .p pv11 [pv2,pv7,pv6833], .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv23,pv33967], .c 3,
]
private theorem h0572c30 : checkBlock 4687195 128 b0572c30 = true := by
  decide +kernel

private def b0572c31 : List Row := [
  .c 47, .p pv2 [pv2,pv3,pv7,pv11,pv19,pv89], .c 3, .c 503, .c 7, .c 3, .c 11, .c 5, .c 3, .c 23,
  .c 19, .c 3, .c 5, .c 739, .c 3, .c 1097, .p pv11 [pv2,pv3,pv781247], .c 3, .c 7, .c 41, .c 3,
  .c 37, .c 5, .c 3, .p pv2 [pv2,pv47,pv1061], .c 7, .c 3, .c 5, .c 11, .c 3, .c 101, .c 1171,
  .c 3, .p pv2 [pv2,pv43,pv27253], .p pv3 [pv2,pv3,pv11,pv71023], .c 3, .c 167, .c 5, .c 3, .c 7,
  .c 29, .c 3, .c 5, .c 383, .c 3, .c 31, .c 7, .c 3, .c 19, .c 73, .c 3, .c 13, .c 5, .c 3,
  .c 43, .c 23, .c 3, .c 5, .c 37, .c 3, .c 7, .c 11, .c 3, .c 491, .c 13, .c 3, .c 307, .c 5,
  .c 3, .c 29, .c 83, .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv11719], .c 31, .c 3, .c 23,
  .c 59, .c 3, .c 7, .c 5, .c 3, .c 1607, .c 1291, .c 3, .c 5, .c 7, .c 3, .c 13, .c 71, .c 3,
  .p pv2 [pv2,pv139,pv8431], .c 11, .c 3, .p pv2 [pv2,pv19,pv281,pv439], .c 5, .c 3, .c 523,
  .p pv11 [pv2,pv3,pv5,pv11,pv947], .c 3, .c 5, .c 13, .c 3, .c 11, .p pv3 [pv2,pv3,pv7,pv111611],
  .c 3, .c 61, .c 7, .c 3, .p pv3 [pv2,pv11,pv53269], .c 5, .c 3, .p pv17 [pv2,pv37,pv63347],
  .p pv23 [pv2,pv3,pv5,pv19,pv257], .c 3, .c 5, .c 619, .c 3, .c 53,
  .p pv2 [pv2,pv3,pv113,pv3457], .c 3, .c 7, .c 17, .c 3, .c 311, .c 5,
]
private theorem h0572c31 : checkBlock 4687451 128 b0572c31 = true := by
  decide +kernel

def rows0572 : List Row :=
  b0572c00 ++ b0572c01 ++ b0572c02 ++ b0572c03 ++ b0572c04 ++ b0572c05 ++ b0572c06 ++ b0572c07 ++
  b0572c08 ++ b0572c09 ++ b0572c10 ++ b0572c11 ++ b0572c12 ++ b0572c13 ++ b0572c14 ++ b0572c15 ++
  b0572c16 ++ b0572c17 ++ b0572c18 ++ b0572c19 ++ b0572c20 ++ b0572c21 ++ b0572c22 ++ b0572c23 ++
  b0572c24 ++ b0572c25 ++ b0572c26 ++ b0572c27 ++ b0572c28 ++ b0572c29 ++ b0572c30 ++ b0572c31

theorem checked0572 : checkBlock 4679515 4096 rows0572 = true :=
  checkBlock_append h0572c00 (
    checkBlock_append h0572c01 (
    checkBlock_append h0572c02 (
    checkBlock_append h0572c03 (
    checkBlock_append h0572c04 (
    checkBlock_append h0572c05 (
    checkBlock_append h0572c06 (
    checkBlock_append h0572c07 (
    checkBlock_append h0572c08 (
    checkBlock_append h0572c09 (
    checkBlock_append h0572c10 (
    checkBlock_append h0572c11 (
    checkBlock_append h0572c12 (
    checkBlock_append h0572c13 (
    checkBlock_append h0572c14 (
    checkBlock_append h0572c15 (
    checkBlock_append h0572c16 (
    checkBlock_append h0572c17 (
    checkBlock_append h0572c18 (
    checkBlock_append h0572c19 (
    checkBlock_append h0572c20 (
    checkBlock_append h0572c21 (
    checkBlock_append h0572c22 (
    checkBlock_append h0572c23 (
    checkBlock_append h0572c24 (
    checkBlock_append h0572c25 (
    checkBlock_append h0572c26 (
    checkBlock_append h0572c27 (
    checkBlock_append h0572c28 (
    checkBlock_append h0572c29 (
    checkBlock_append h0572c30 (
    h0572c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
