/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks05/Block0427
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks05/Block0427.checked0427
   digest: Kernel proof of checker success on extended consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table035
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table043
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table048
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table055
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table064
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table076
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table093
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table118
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table159
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table161
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table163
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table165
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table168
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table171
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table177
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table186
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table194
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table195
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table218
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table237
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table238

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0427c00 : List Row := [
  .c 5, .c 7, .c 3, .c 17, .c 13, .c 3, .c 19, .p pv7 [pv2,pv3,pv145487], .c 3, .c 53, .c 5, .c 3,
  .c 23, .c 61, .c 3, .c 5, .p pv5 [pv2,pv3,pv19,pv109,pv281], .c 3, .p pv11 [pv2,pv5,pv349171],
  .c 821, .c 3, .c 1831, .c 7, .c 3, .p pv2 [pv2,pv13,pv23,pv5839], .c 5, .c 3, .c 43, .c 107,
  .c 3, .c 5, .c 89, .c 3, .c 11, .p pv3 [pv2,pv3,pv521,pv1117], .c 3, .c 7, .c 17, .c 3, .c 179,
  .c 5, .c 3, .c 467, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv17,pv11411], .c 3, .c 47,
  .p pv5 [pv2,pv3,pv43,pv67,pv101], .c 3, .p pv3 [pv2,pv54559], .c 619, .c 3, .c 17, .c 5, .c 3,
  .c 7, .c 23, .c 3, .c 5, .c 59, .c 3, .c 19, .c 7, .c 3, .c 11, .c 31, .c 3, .c 13, .c 5, .c 3,
  .c 139, .p pv2 [pv2,pv3,pv5,pv19,pv1021], .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv89,pv503], .c 3,
  .c 7, .c 557, .c 3, .c 23, .c 13, .c 3, .p pv2 [pv2,pv1745921], .c 5, .c 3, .c 241, .c 11, .c 3,
  .c 5, .p pv7 [pv2,pv3,pv59,pv137], .c 3, .c 29, .c 911, .c 3, .p pv2 [pv2,pv7,pv249419],
  .c 1427, .c 3, .c 7, .c 5, .c 3, .c 79, .p pv11 [pv2,pv3,pv5,pv7,pv4157], .c 3, .c 5, .c 7,
  .c 3, .c 13, .c 83, .c 3, .p pv3 [pv2,pv19,pv22973], .p pv11 [pv2,pv3,pv581983], .c 3, .c 97,
  .c 5, .c 3, .c 1721, .c 1193, .c 3, .c 5, .c 11, .c 3, .c 1511,
  .p pv5 [pv2,pv3,pv7,pv71,pv1171], .c 3, .p pv5 [pv2,pv113,pv15451], .c 7,
]
private theorem h0427c00 : checkBlock 3491675 128 b0427c00 = true := by
  decide +kernel

private def b0427c01 : List Row := [
  .c 3, .c 31, .c 5, .c 3, .c 11, .c 227, .c 3, .c 5, .p pv2 [pv2,pv3,pv419,pv463], .c 3,
  .p pv11 [pv2,pv5,pv7,pv11,pv907], .c 17, .c 3, .c 7, .c 47, .c 3, .p pv2 [pv2,pv431,pv4051],
  .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 29, .c 3, .p pv2 [pv2,pv5,pv174599], .c 11, .c 3, .c 17,
  .c 823, .c 3, .c 71, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv97], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv29,pv47,pv61], .c 3, .c 41, .c 7, .c 3, .p pv3 [pv2,pv11,pv19841],
  .p pv11 [pv2,pv3,pv64667], .c 3, .c 37, .c 5, .c 3, .c 19, .p pv7 [pv2,pv3,pv5,pv43,pv2707],
  .c 3, .c 5, .c 79, .c 3, .c 7, .p pv3 [pv2,pv3,pv409,pv1423], .c 3, .c 13, .c 11, .c 3, .c 47,
  .c 5, .c 3, .c 83, .p pv2 [pv2,pv3,pv5,pv11,pv13,pv37], .c 3, .c 5, .c 19, .c 3, .c 11, .c 13,
  .c 3, .p pv2 [pv2,pv7,pv124717], .c 1039, .c 3, .c 7, .c 5, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv5,pv7,pv23,pv241], .c 3, .c 5, .c 7, .c 3, .c 73, .p pv5 [pv2,pv3,pv582017],
  .c 3, .c 67, .p pv2 [pv2,pv3,pv97003], .c 3, .c 23, .c 5, .c 3, .c 31, .c 1049, .c 3, .c 5,
  .c 1493, .c 3, .p pv11 [pv2,pv5,pv137,pv2549], .c 643, .c 3, .c 11, .c 7, .c 3, .c 19, .c 5,
  .c 3, .c 1009, .c 13, .c 3, .c 5, .c 17, .c 3, .p pv11 [pv2,pv5,pv7,pv1559], .c 251, .c 3, .c 7,
  .c 443, .c 3, .p pv2 [pv2,pv873043], .c 5, .c 3, .c 683, .c 7, .c 3, .c 5,
]
private theorem h0427c01 : checkBlock 3491931 128 b0427c01 = true := by
  decide +kernel

private def b0427c02 : List Row := [
  .p pv2 [pv2,pv3,pv582031], .c 3, .c 17, .p pv7 [pv2,pv3,pv11,pv3307], .c 3, .c 673, .c 937,
  .c 3, .c 11, .c 5, .c 3, .c 7, .c 1531, .c 3, .c 5, .c 1181, .c 3, .c 1433, .c 7, .c 3, .c 1213,
  .c 13, .c 3, .p pv3 [pv2,pv436529], .c 5, .c 3, .c 1523, .c 47, .c 3, .c 5, .c 11, .c 3, .c 7,
  .c 1747, .c 3, .c 19, .c 17, .c 3, .c 521, .c 5, .c 3, .c 11, .c 89, .c 3, .c 5, .c 71, .c 3,
  .c 13, .p pv2 [pv2,pv3,pv37,pv15731], .c 3, .p pv5 [pv2,pv7,pv249449], .c 563, .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv41,pv42589], .p pv2 [pv2,pv3,pv5,pv7,pv1663], .c 3, .c 5, .c 7, .c 3, .c 61,
  .c 11, .c 3, .p pv2 [pv2,pv873079], .c 37, .c 3, .p pv2 [pv2,pv449,pv3889], .c 5, .c 3, .c 53,
  .c 43, .c 3, .c 5, .p pv5 [pv2,pv3,pv31,pv2347], .c 3, .p pv2 [pv2,pv5,pv174617], .c 23, .c 3,
  .c 1231, .c 7, .c 3, .c 79, .c 5, .c 3, .c 13, .c 17, .c 3, .c 5, .c 31, .c 3, .c 19, .c 107,
  .c 3, .c 7, .c 11, .c 3, .c 29, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv3593],
  .c 3, .c 11, .c 223, .c 3, .p pv5 [pv2,pv1746203], .c 19, .c 3,
  .p pv13 [pv2,pv7,pv11,pv17,pv23,pv29], .c 5, .c 3, .c 7, .c 41, .c 3, .c 5, .c 269, .c 3,
  .p pv13 [pv2,pv5,pv37,pv9439], .c 7, .c 3, .c 13, .p pv11 [pv2,pv3,pv163,pv3571], .c 3,
]
private theorem h0427c02 : checkBlock 3492187 128 b0427c02 = true := by
  decide +kernel

private def b0427c03 : List Row := [
  .c 349, .c 5, .c 3, .c 89, .c 409, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv13229], .c 3, .c 7, .c 13,
  .c 3, .c 11, .c 109, .c 3, .c 1051, .c 5, .c 3, .c 101, .c 23, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv194027], .c 3, .c 31, .p pv2 [pv2,pv3,pv291041], .c 3, .c 17, .c 29, .c 3,
  .c 7, .c 5, .c 3, .c 67, .c 11, .c 3, .c 5, .c 7, .c 3, .c 1723, .c 19, .c 3, .c 23,
  .p pv7 [pv2,pv3,pv13,pv29,pv193], .c 3, .c 11, .c 5, .c 3, .c 73, .c 13, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv43,pv13537], .c 3, .p pv17 [pv2,pv5,pv23,pv3037], .c 31, .c 3, .c 29, .c 7,
  .c 3, .p pv2 [pv2,pv1746281], .c 5, .c 3, .p pv3 [pv2,pv436571],
  .p pv2 [pv2,pv3,pv5,pv47,pv2477], .c 3, .c 5, .c 11, .c 3, .c 577,
  .p pv29 [pv2,pv3,pv17,pv97,pv353], .c 3, .c 7, .c 43, .c 3, .c 13, .c 5, .c 3, .c 11, .c 7,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv44777], .c 3, .p pv2 [pv2,pv5,pv11,pv31751], .c 197, .c 3,
  .c 47, .c 13, .c 3, .c 59, .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv151,pv257], .c 3, .c 5,
  .c 19, .c 3, .p pv3 [pv2,pv5,pv83,pv263], .c 7, .c 3, .c 53, .c 199, .c 3, .c 139, .c 5, .c 3,
  .c 1693, .p pv2 [pv2,pv3,pv5,pv58211], .c 3, .c 5, .c 17, .c 3, .c 7, .c 29, .c 3, .c 31, .c 97,
  .c 3, .c 211, .c 5, .c 3, .c 37, .p pv3 [pv2,pv3,pv5,pv116423], .c 3, .c 5, .c 13,
]
private theorem h0427c03 : checkBlock 3492443 128 b0427c03 = true := by
  decide +kernel

private def b0427c04 : List Row := [
  .c 3, .c 17, .c 71, .c 3, .p pv2 [pv2,pv7,pv317,pv787], .c 11, .c 3, .c 7, .c 5, .c 3,
  .p pv19 [pv2,pv17,pv43,pv2389], .c 193, .c 3, .c 5, .c 7, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv19,pv15319], .c 3, .p pv3 [pv2,pv13,pv2099], .c 31, .c 3,
  .p pv5 [pv2,pv11,pv158761], .c 5, .c 3, .c 13, .c 19, .c 3, .c 5, .c 23, .c 3, .c 43, .c 37,
  .c 3, .c 313, .c 7, .c 3, .p pv2 [pv2,pv373,pv2341], .c 5, .c 3, .c 157, .c 151, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv17,pv283], .c 3, .p pv11 [pv2,pv5,pv7,pv41,pv1217],
  .p pv7 [pv2,pv3,pv139,pv349], .c 3, .c 7, .c 61, .c 3, .c 17, .c 5, .c 3, .c 641, .c 7, .c 3,
  .c 5, .c 191, .c 3, .c 1297, .p pv5 [pv2,pv3,pv582137], .c 3, .c 13, .p pv2 [pv2,pv3,pv32341],
  .c 3, .c 103, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 29, .c 3, .c 457, .c 7, .c 3, .c 907,
  .c 53, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv479,pv1823], .c 17, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv29,pv10037], .c 3, .c 7, .c 101, .c 3, .c 257, .c 83, .c 3,
  .p pv2 [pv2,pv13,pv5167], .c 5, .c 3, .c 47, .c 751, .c 3, .c 5, .c 11, .c 3, .c 37, .c 41,
  .c 3, .p pv2 [pv2,pv7,pv71,pv251], .c 271, .c 3, .c 7, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5,
  .c 7, .c 3, .c 19, .c 113, .c 3, .c 557, .c 1279, .c 3, .p pv3 [pv2,pv137,pv3187],
]
private theorem h0427c04 : checkBlock 3492699 128 b0427c04 = true := by
  decide +kernel

private def b0427c05 : List Row := [
  .c 5, .c 3, .p pv17 [pv2,pv7,pv249497], .p pv7 [pv2,pv3,pv5,pv19,pv383], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv582161], .c 3, .p pv11 [pv2,pv5,pv13,pv97,pv277], .c 11, .c 3, .c 59, .c 7,
  .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv873247], .p pv13 [pv2,pv3,pv5,pv17,pv761], .c 3, .c 5,
  .c 461, .c 3, .p pv3 [pv2,pv5,pv7,pv499], .p pv2 [pv2,pv3,pv582167], .c 3, .c 7, .c 13, .c 3,
  .p pv2 [pv2,pv601,pv1453], .c 5, .c 3, .c 43, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv194057], .c 3,
  .p pv11 [pv2,pv5,pv349303], .c 23, .c 3, .c 421, .c 11, .c 3, .c 61, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv11,pv29,pv73], .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv23,pv113], .c 3, .c 11,
  .c 7, .c 3, .c 97, .c 283, .c 3, .p pv3 [pv2,pv11,pv89,pv223], .c 5, .c 3, .c 23,
  .p pv17 [pv2,pv3,pv5,pv31,pv313], .c 3, .c 5, .c 13, .c 3, .c 7, .c 19, .c 3, .c 1861,
  .p pv2 [pv2,pv3,pv7,pv9241], .c 3, .p pv5 [pv2,pv23,pv75937], .c 5, .c 3, .c 17, .c 31, .c 3,
  .c 5, .c 523, .c 3, .p pv13 [pv2,pv5,pv2729], .c 73, .c 3, .c 11, .c 71, .c 3, .c 7, .c 5, .c 3,
  .c 13, .c 349, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv19,pv3677], .c 647, .c 3, .c 1867,
  .c 41, .c 3, .p pv2 [pv2,pv1746581], .c 5, .c 3, .c 19, .c 11, .c 3, .c 5, .c 17, .c 3, .c 47,
  .p pv5 [pv2,pv3,pv7,pv11,pv7561], .c 3, .c 773, .c 7, .c 3, .c 11, .c 5, .c 3, .c 191, .c 1103,
  .c 3, .c 5, .c 19, .c 3,
]
private theorem h0427c05 : checkBlock 3492955 128 b0427c05 = true := by
  decide +kernel

private def b0427c06 : List Row := [
  .c 17, .c 59, .c 3, .c 7, .p pv2 [pv2,pv3,pv582203], .c 3, .p pv5 [pv2,pv79,pv22109], .c 5,
  .c 3, .c 107, .c 7, .c 3, .c 5, .c 11, .c 3, .c 41, .c 13, .c 3, .c 277, .c 347, .c 3, .c 29,
  .c 5, .c 3, .c 7, .c 97, .c 3, .c 5, .c 509, .c 3, .c 71, .c 7, .c 3, .c 43, .c 17, .c 3, .c 19,
  .c 5, .c 3, .p pv3 [pv2,pv353,pv1237], .p pv2 [pv2,pv3,pv5,pv116443], .c 3, .c 5, .c 31, .c 3,
  .c 7, .c 11, .c 3, .p pv2 [pv2,pv167,pv10459], .c 23, .c 3, .c 17, .c 5, .c 3,
  .p pv7 [pv2,pv37,pv47207], .c 13, .c 3, .c 5, .p pv13 [pv2,pv3,pv582221], .c 3, .c 59,
  .p pv2 [pv2,pv3,pv23,pv4219], .c 3, .p pv3 [pv2,pv7,pv11,pv53,pv107], .c 89, .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv61,pv103,pv139], .p pv3 [pv2,pv3,pv5,pv7,pv1109], .c 3, .c 5, .c 7, .c 3,
  .p pv19 [pv2,pv5,pv13,pv3359], .c 43, .c 3, .p pv5 [pv2,pv1746683], .c 11, .c 3, .c 13, .c 5,
  .c 3, .p pv2 [pv2,pv7,pv19,pv23,pv571], .c 17, .c 3, .c 5, .c 83, .c 3, .c 11, .c 313, .c 3,
  .c 19, .c 7, .c 3, .p pv2 [pv2,pv11,pv158791], .c 5, .c 3, .c 61,
  .p pv37 [pv2,pv3,pv5,pv116447], .c 3, .c 5, .p pv5 [pv2,pv3,pv19,pv47,pv163], .c 3, .c 31,
  .p pv3 [pv2,pv3,pv64693], .c 3, .c 7, .c 37, .c 3, .p pv3 [pv2,pv17,pv1511], .c 5, .c 3, .c 293,
  .c 7, .c 3, .c 5, .c 23, .c 3, .c 13, .c 1249, .c 3, .c 11, .c 79, .c 3, .c 47, .c 5,
]
private theorem h0427c06 : checkBlock 3493211 128 b0427c06 = true := by
  decide +kernel

private def b0427c07 : List Row := [
  .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv23,pv61,pv83], .c 3, .c 5, .c 13, .c 3, .c 181, .c 7, .c 3,
  .c 41, .c 101, .c 3, .c 23, .c 5, .c 3, .c 499, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv582251],
  .c 3, .c 7, .p pv5 [pv2,pv3,pv11,pv401], .c 3, .c 17, .p pv3 [pv2,pv3,pv7,pv223,pv373], .c 3,
  .c 11, .c 5, .c 3, .c 13, .c 61, .c 3, .c 5, .p pv5 [pv2,pv3,pv151,pv241], .c 3,
  .p pv2 [pv2,pv5,pv37,pv4721], .c 29, .c 3, .p pv2 [pv2,pv7,pv249539], .c 19, .c 3, .c 7, .c 5,
  .c 3, .c 109, .c 73, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv349357],
  .p pv5 [pv2,pv3,pv29,pv10039], .c 3, .c 37, .c 163, .c 3, .p pv5 [pv2,pv983,pv1777], .c 5, .c 3,
  .c 11, .p pv3 [pv2,pv3,pv5,pv101,pv1153], .c 3, .c 5, .p pv2 [pv2,pv3,pv347,pv839], .c 3, .c 29,
  .c 149, .c 3, .c 13, .c 7, .c 3, .c 601, .c 5, .c 3, .c 17, .c 43, .c 3, .c 5, .c 467, .c 3,
  .c 23, .c 11, .c 3, .c 7, .c 131, .c 3, .c 127, .c 5, .c 3, .c 97, .c 7, .c 3, .c 5, .c 103,
  .c 3, .p pv2 [pv2,pv5,pv307,pv569], .c 19, .c 3, .p pv2 [pv2,pv11,pv158803], .c 31, .c 3,
  .c 281, .c 5, .c 3, .c 7, .c 1583, .c 3, .c 5, .c 17, .c 3, .c 101, .c 7, .c 3, .c 71, .c 11,
  .c 3, .p pv5 [pv2,pv239,pv7309], .c 5, .c 3, .c 1201, .c 13, .c 3, .c 5, .c 29, .c 3, .c 7,
]
private theorem h0427c07 : checkBlock 3493467 128 b0427c07 = true := by
  decide +kernel

private def b0427c08 : List Row := [
  .c 23, .c 3, .p pv5 [pv2,pv383,pv4561], .c 1753, .c 3, .c 41, .c 5, .c 3, .c 19, .c 223, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv23,pv29,pv97], .c 3, .c 761, .p pv19 [pv2,pv3,pv149,pv977], .c 3,
  .c 227, .p pv11 [pv2,pv3,pv19,pv1613], .c 3, .c 7, .c 5, .c 3, .c 23, .c 967, .c 3, .c 5, .c 7,
  .c 3, .p pv2 [pv2,pv5,pv73,pv2393], .p pv3 [pv2,pv3,pv67,pv2897], .c 3, .c 11, .c 13, .c 3,
  .c 31, .c 5, .c 3, .c 37, .c 277, .c 3, .c 5, .c 167, .c 3, .p pv2 [pv2,pv5,pv349381], .c 53,
  .c 3, .p pv3 [pv2,pv436727], .c 7, .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv13,pv67189], .c 11,
  .c 3, .c 5, .c 1013, .c 3, .c 13, .c 97, .c 3, .c 7, .c 67, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv1746929], .c 7, .c 3, .c 5, .c 13, .c 3, .c 107, .c 37, .c 3, .c 433, .c 43, .c 3,
  .p pv2 [pv2,pv7,pv249563], .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 11, .c 3, .c 131, .c 7, .c 3,
  .c 23, .p pv2 [pv2,pv3,pv11,pv17,pv173], .c 3, .c 401, .c 5, .c 3, .c 11, .c 59, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv73,pv2659], .c 3, .c 7, .c 47, .c 3, .p pv3 [pv2,pv218371],
  .p pv3 [pv2,pv3,pv7,pv41,pv2029], .c 3, .c 347, .c 5, .c 3, .c 29,
  .p pv13 [pv2,pv3,pv5,pv23293], .c 3, .c 5, .p pv2 [pv2,pv3,pv491,pv593], .c 3,
  .p pv3 [pv2,pv5,pv113,pv773], .c 11, .c 3, .c 19, .c 929, .c 3, .c 7, .c 5, .c 3,
]
private theorem h0427c08 : checkBlock 3493723 128 b0427c08 = true := by
  decide +kernel

private def b0427c09 : List Row := [
  .c 31, .c 71, .c 3, .c 5, .c 7, .c 3, .c 1327, .c 17, .c 3, .c 13, .c 23, .c 3, .c 271, .c 5,
  .c 3, .p pv3 [pv2,pv7,pv43,pv1451], .p pv31 [pv2,pv3,pv5,pv13,pv17,pv31], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv337], .c 3, .c 37, .c 13, .c 3, .c 17, .c 7, .c 3, .p pv3 [pv2,pv131,pv1667],
  .c 5, .c 3, .c 59, .c 31, .c 3, .c 5, .c 1229, .c 3, .c 11, .p pv2 [pv2,pv3,pv71,pv1367], .c 3,
  .c 7, .c 1031, .c 3, .p pv5 [pv2,pv11,pv13,pv19,pv643], .c 5, .c 3, .c 103, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv291173], .c 3, .c 19, .p pv2 [pv2,pv3,pv229,pv2543], .c 3, .c 409,
  .p pv17 [pv2,pv3,pv13,pv3733], .c 3, .p pv2 [pv2,pv7,pv17827], .c 5, .c 3, .c 7, .c 13, .c 3,
  .c 5, .p pv11 [pv2,pv3,pv7,pv11,pv2521], .c 3, .c 1223, .c 7, .c 3, .c 11, .c 19, .c 3, .c 29,
  .c 5, .c 3, .c 17, .c 53, .c 3, .c 5, .c 23, .c 3, .c 7, .c 41, .c 3, .c 359,
  .p pv11 [pv2,pv3,pv7,pv41597], .c 3, .c 13, .c 5, .c 3, .p pv7 [pv2,pv1747079], .c 11, .c 3,
  .c 5, .c 1009, .c 3, .c 251, .p pv2 [pv2,pv3,pv11,pv103,pv257], .c 3,
  .p pv3 [pv2,pv7,pv19,pv821], .c 13, .c 3, .c 7, .c 5, .c 3, .c 197,
  .p pv3 [pv2,pv3,pv5,pv7,pv2377], .c 3, .c 5, .c 7, .c 3, .c 283, .c 653, .c 3, .c 367,
  .p pv17 [pv2,pv3,pv18199], .c 3, .c 109, .c 5, .c 3, .c 1049, .p pv2 [pv2,pv3,pv5,pv58237],
  .c 3, .c 5, .c 11, .c 3, .c 13, .c 19,
]
private theorem h0427c09 : checkBlock 3493979 128 b0427c09 = true := by
  decide +kernel

private def b0427c10 : List Row := [
  .c 3, .c 53, .c 7, .c 3, .c 37, .c 5, .c 3, .c 11, .c 67, .c 3, .c 5, .c 13, .c 3, .c 463,
  .c 61, .c 3, .c 7, .p pv2 [pv2,pv3,pv29,pv3347], .c 3, .p pv3 [pv2,pv27299], .c 5, .c 3,
  .p pv17 [pv2,pv127,pv13757], .c 7, .c 3, .c 5, .c 863, .c 3, .c 73, .c 11, .c 3, .c 29, .c 17,
  .c 3, .p pv5 [pv2,pv7,pv249593], .c 5, .c 3, .c 7, .c 229, .c 3, .c 5, .c 37, .c 3, .c 23, .c 7,
  .c 3, .c 1579, .c 743, .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv1747169], .c 503, .c 3, .c 5,
  .c 19, .c 3, .c 7, .c 337, .c 3, .p pv2 [pv2,pv47,pv18587], .c 11, .c 3, .p pv2 [pv2,pv1747181],
  .c 5, .c 3, .p pv3 [pv2,pv109199], .c 211, .c 3, .c 5, .p pv5 [pv2,pv3,pv48533], .c 3, .c 11,
  .c 83, .c 3, .c 13, .c 41, .c 3, .c 7, .c 5, .c 3, .p pv23 [pv2,pv101,pv17299], .c 17, .c 3,
  .c 5, .c 7, .c 3, .c 587, .c 13, .c 3, .p pv3 [pv2,pv218401], .c 239, .c 3, .c 19, .c 5, .c 3,
  .c 257, .c 109, .c 3, .c 5, .c 73, .c 3, .p pv3 [pv2,pv5,pv199,pv439],
  .p pv5 [pv2,pv3,pv7,pv19,pv29,pv151], .c 3, .c 11, .c 7, .c 3, .p pv2 [pv2,pv13,pv17,pv59,pv67],
  .c 5, .c 3, .c 23, .c 19, .c 3, .c 5, .p pv2 [pv2,pv3,pv83,pv2339], .c 3, .c 29, .c 1091, .c 3,
  .c 7, .c 1289, .c 3, .p pv2 [pv2,pv23,pv75967], .c 5, .c 3, .p pv3 [pv2,pv436811],
]
private theorem h0427c10 : checkBlock 3494235 128 b0427c10 = true := by
  decide +kernel

private def b0427c11 : List Row := [
  .c 7, .c 3, .c 5, .c 47, .c 3, .p pv2 [pv2,pv5,pv29,pv241], .c 17, .c 3, .c 61,
  .p pv13 [pv2,pv3,pv291209], .c 3, .c 11, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv17,pv571],
  .c 3, .c 5, .p pv7 [pv2,pv3,pv7,pv83203], .c 3, .p pv17 [pv2,pv5,pv13,pv26881], .c 7, .c 3,
  .c 17, .c 37, .c 3, .c 13, .c 5, .c 3, .c 71, .c 23, .c 3, .c 5, .c 11, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv582427], .c 3, .c 43, .c 13, .c 3, .p pv2 [pv2,pv873643], .c 5, .c 3, .c 11,
  .c 307, .c 3, .c 5, .c 29, .c 3, .c 47, .c 151, .c 3, .c 23, .c 31, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv13,pv53,pv317], .c 293, .c 3, .c 5, .c 7, .c 3, .c 13, .c 11, .c 3,
  .p pv2 [pv2,pv1747313], .c 59, .c 3, .c 223, .c 5, .c 3, .c 17, .p pv7 [pv2,pv3,pv5,pv14561],
  .c 3, .c 5, .c 13, .c 3, .c 19, .c 43, .c 3, .p pv3 [pv2,pv11,pv17,pv73], .c 7, .c 3, .c 157,
  .c 5, .c 3, .p pv2 [pv2,pv873667], .c 907, .c 3, .c 5, .c 659, .c 3,
  .p pv3 [pv2,pv5,pv7,pv1783], .c 1489, .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv31,pv28183], .c 5,
  .c 3, .c 13, .c 7, .c 3, .c 5, .c 17, .c 3, .c 11, .c 613, .c 3, .c 41,
  .p pv3 [pv2,pv3,pv64717], .c 3, .c 31, .c 5, .c 3, .c 7, .c 739, .c 3, .c 5, .c 1291, .c 3,
  .c 17, .c 7, .c 3,
]
private theorem h0427c11 : checkBlock 3494491 128 b0427c11 = true := by
  decide +kernel

private def b0427c12 : List Row := [
  .c 59, .p pv7 [pv2,pv3,pv181,pv1609], .c 3, .p pv3 [pv2,pv109211], .c 5, .c 3, .c 379, .c 29,
  .c 3, .c 5, .c 53, .c 3, .c 7, .c 173, .c 3, .c 11, .c 47, .c 3, .c 547, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv79427], .c 397, .c 3, .c 5, .c 281, .c 3, .p pv3 [pv2,pv5,pv8737], .c 13,
  .c 3, .p pv5 [pv2,pv7,pv59,pv4231], .c 17, .c 3, .c 7, .c 5, .c 3, .c 29, .c 11, .c 3, .c 5,
  .c 7, .c 3, .p pv7 [pv2,pv5,pv349483], .c 71, .c 3, .p pv2 [pv2,pv873709],
  .p pv19 [pv2,pv3,pv199,pv2927], .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv7,pv29,pv269],
  .p pv2 [pv2,pv3,pv5,pv23,pv1013], .c 3, .c 5, .p pv5 [pv2,pv3,pv223,pv653], .c 3,
  .p pv2 [pv2,pv5,pv17,pv19,pv541], .p pv3 [pv2,pv3,pv7,pv27737], .c 3, .c 109, .c 7, .c 3, .c 23,
  .c 5, .c 3, .c 19, .c 13, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv7,pv49927], .c 103, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv11,pv19,pv929], .c 3, .c 101, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5,
  .c 19, .c 3, .c 67, .p pv2 [pv2,pv3,pv41,pv14207], .c 3, .c 881, .c 181, .c 3, .c 13, .c 5,
  .c 3, .c 7, .c 89, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv13,pv37,pv173], .c 3,
  .p pv11 [pv2,pv5,pv69899], .c 7, .c 3, .c 919, .c 13, .c 3, .c 41, .c 5, .c 3,
  .p pv3 [pv2,pv436871], .c 31, .c 3, .c 5, .c 113, .c 3, .c 7, .c 37, .c 3,
  .p pv2 [pv2,pv11,pv158863], .p pv17 [pv2,pv3,pv7,pv23,pv67], .c 3, .c 19, .c 5, .c 3,
  .p pv17 [pv2,pv13,pv229,pv587], .p pv17 [pv2,pv3,pv5,pv233],
]
private theorem h0427c12 : checkBlock 3494747 128 b0427c12 = true := by
  decide +kernel

private def b0427c13 : List Row := [
  .c 3, .c 5, .c 97, .c 3, .c 13, .c 17, .c 3, .p pv3 [pv2,pv7,pv139,pv449], .c 11, .c 3, .c 7,
  .c 5, .c 3, .c 331, .c 19, .c 3, .c 5, .c 7, .c 3, .c 11, .p pv2 [pv2,pv3,pv59,pv1097], .c 3,
  .c 17, .p pv11 [pv2,pv3,pv107,pv1361], .c 3, .c 353, .c 5, .c 3, .c 719, .c 47, .c 3, .c 5,
  .c 787, .c 3, .p pv13 [pv2,pv5,pv349507], .p pv11 [pv2,pv3,pv7,pv743], .c 3,
  .p pv2 [pv2,pv13,pv67213], .c 7, .c 3, .c 43, .c 5, .c 3, .c 13, .c 571, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv1471], .c 3, .c 59, .c 23, .c 3, .c 7, .c 29, .c 3, .c 1493, .c 5, .c 3,
  .c 89, .c 7, .c 3, .c 5, .c 41, .c 3, .c 37, .c 1759, .c 3, .p pv3 [pv2,pv239,pv457],
  .p pv2 [pv2,pv3,pv29,pv53,pv379], .c 3, .c 167, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 31,
  .c 3, .p pv3 [pv2,pv5,pv59,pv1481], .c 7, .c 3, .c 13, .c 43, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv61,pv28649], .p pv2 [pv2,pv3,pv5,pv13,pv4481], .c 3, .c 5, .c 463, .c 3, .c 7,
  .c 13, .c 3, .c 79, .c 487, .c 3, .c 113, .c 5, .c 3, .c 41, .c 131, .c 3, .c 5, .c 11, .c 3,
  .c 19, .c 241, .c 3, .c 229, .p pv19 [pv2,pv3,pv11,pv26479], .c 3, .c 7, .c 5, .c 3, .c 11,
  .c 23, .c 3, .c 5, .c 7, .c 3, .c 17, .p pv2 [pv2,pv3,pv291271], .c 3, .c 991,
]
private theorem h0427c13 : checkBlock 3495003 128 b0427c13 = true := by
  decide +kernel

private def b0427c14 : List Row := [
  .c 19, .c 3, .c 479, .c 5, .c 3, .p pv2 [pv2,pv7,pv17,pv1049], .c 13, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv79,pv1229], .c 3, .c 31, .c 11, .c 3, .c 23, .c 7, .c 3,
  .p pv2 [pv2,pv173,pv5051], .c 5, .c 3, .p pv2 [pv2,pv43,pv97,pv419],
  .p pv7 [pv2,pv3,pv5,pv61,pv191], .c 3, .c 5, .c 101, .c 3, .c 1381, .c 73, .c 3, .c 7, .c 17,
  .c 3, .c 13, .c 5, .c 3, .c 311, .c 7, .c 3, .c 5, .c 59, .c 3, .c 29, .c 31, .c 3, .c 503,
  .c 11, .c 3, .c 17, .c 5, .c 3, .c 7, .c 61, .c 3, .c 5, .c 569, .c 3, .c 11, .c 7, .c 3,
  .c 947, .c 23, .c 3, .c 373, .c 5, .c 3, .c 521, .c 149, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv59,pv4937], .c 3, .c 7, .c 53, .c 3, .c 1103,
  .p pv13 [pv2,pv3,pv7,pv101,pv103], .c 3, .p pv2 [pv2,pv109,pv8017], .c 5, .c 3, .c 1367, .c 17,
  .c 3, .c 5, .c 13, .c 3, .c 1483, .c 139, .c 3, .c 11, .p pv29 [pv2,pv3,pv17,pv11423], .c 3,
  .c 7, .c 5, .c 3, .c 19, .p pv53 [pv2,pv3,pv5,pv7,pv3329], .c 3, .c 5, .c 7, .c 3, .c 1733,
  .c 277, .c 3, .c 31, .p pv7 [pv2,pv3,pv19,pv15331], .c 3, .c 131, .c 5, .c 3, .c 13, .c 11,
  .c 3, .c 5, .c 19, .c 3, .c 191, .c 619, .c 3, .p pv3 [pv2,pv41,pv10657], .c 7, .c 3, .c 11,
  .c 5, .c 3, .c 53, .c 103, .c 3,
]
private theorem h0427c14 : checkBlock 3495259 128 b0427c14 = true := by
  decide +kernel

private def b0427c15 : List Row := [
  .c 5, .c 23, .c 3, .c 109, .c 17, .c 3, .c 7, .c 31, .c 3, .c 263, .c 5, .c 3,
  .p pv2 [pv2,pv37,pv47237], .c 7, .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv69911],
  .p pv5 [pv2,pv3,pv9103], .c 3, .c 13, .c 317, .c 3, .c 19, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv13,pv8963], .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv20807], .c 3,
  .p pv2 [pv2,pv5,pv11,pv15889], .c 7, .c 3, .c 1151, .c 97, .c 3, .c 457, .c 5, .c 3, .c 43,
  .c 19, .c 3, .c 5, .p pv3 [pv2,pv3,pv582601], .c 3, .c 7, .c 11, .c 3, .p pv3 [pv2,pv193,pv283],
  .c 41, .c 3, .p pv5 [pv2,pv13,pv31,pv4337], .c 5, .c 3, .c 271, .c 29, .c 3, .c 5, .c 211, .c 3,
  .c 383, .p pv2 [pv2,pv3,pv17,pv43,pv797], .c 3, .p pv5 [pv2,pv7,pv11,pv22699], .c 37, .c 3,
  .c 7, .c 5, .c 3, .c 17, .c 13, .c 3, .c 5, .c 7, .c 3, .c 79, .p pv7 [pv2,pv3,pv47,pv1033],
  .c 3, .c 19, .c 11, .c 3, .p pv2 [pv2,pv191,pv9151], .c 5, .c 3, .c 29, .c 59, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv19,pv3833], .c 3, .c 11, .c 857, .c 3, .p pv2 [pv2,pv977,pv1789], .c 7, .c 3,
  .c 13, .c 5, .c 3, .c 47, .c 53, .c 3, .c 5, .c 17, .c 3, .p pv13 [pv2,pv5,pv7,pv49939],
  .p pv2 [pv2,pv3,pv523,pv557], .c 3, .c 7, .c 13, .c 3, .p pv5 [pv2,pv41,pv89,pv479], .c 5, .c 3,
  .p pv2 [pv2,pv223,pv3919], .c 7, .c 3, .c 5, .c 439, .c 3, .c 17, .c 461, .c 3, .c 11, .c 691,
]
private theorem h0427c15 : checkBlock 3495515 128 b0427c15 = true := by
  decide +kernel

private def b0427c16 : List Row := [
  .c 3, .p pv2 [pv2,pv7,pv19,pv6571], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv19421], .c 3, .c 5,
  .c 1301, .c 3, .c 13, .c 7, .c 3, .c 37, .p pv13 [pv2,pv3,pv7193], .c 3, .c 1553, .c 5, .c 3,
  .c 59, .c 11, .c 3, .c 5, .c 13, .c 3, .c 7, .p pv3 [pv2,pv3,pv11,pv52967], .c 3, .c 53, .c 17,
  .c 3, .c 11, .c 5, .c 3, .c 23, .c 431, .c 3, .c 5, .p pv3 [pv2,pv3,pv17,pv34273], .c 3,
  .p pv17 [pv2,pv5,pv139,pv503], .c 239, .c 3, .c 43, .c 67, .c 3, .c 7, .c 5, .c 3, .c 13, .c 37,
  .c 3, .c 5, .c 7, .c 3, .c 113, .p pv2 [pv2,pv3,pv13,pv44819], .c 3, .c 701,
  .p pv19 [pv2,pv3,pv11,pv2207], .c 3, .c 829, .c 5, .c 3, .c 11, .c 31, .c 3, .c 5, .c 47, .c 3,
  .p pv11 [pv2,pv5,pv11,pv61,pv521], .c 101, .c 3, .p pv2 [pv2,pv873979], .c 7, .c 3, .c 103,
  .c 5, .c 3, .c 127, .c 17, .c 3, .c 5, .c 1487, .c 3, .p pv2 [pv2,pv5,pv7,pv24971], .c 11, .c 3,
  .c 7, .c 1303, .c 3, .p pv3 [pv2,pv151,pv1447], .c 5, .c 3, .p pv11 [pv2,pv1747979], .c 7, .c 3,
  .c 5, .c 1723, .c 3, .c 61, .c 13, .c 3, .c 23, .c 29, .c 3, .p pv7 [pv2,pv7,pv17,pv37,pv397],
  .c 5, .c 3, .c 7, .c 643, .c 3, .c 5, .c 131, .c 3, .c 47, .c 7, .c 3, .p pv5 [pv2,pv1748003],
  .c 11, .c 3, .c 863, .c 5, .c 3, .c 19, .p pv2 [pv2,pv3,pv5,pv11,pv5297], .c 3, .c 5,
]
private theorem h0427c16 : checkBlock 3495771 128 b0427c16 = true := by
  decide +kernel

private def b0427c17 : List Row := [
  .c 227, .c 3, .c 7, .c 17, .c 3, .c 29, .c 53, .c 3, .c 73, .c 5, .c 3, .c 179, .c 13, .c 3,
  .c 5, .c 19, .c 3, .p pv3 [pv2,pv5,pv67,pv2609], .p pv3 [pv2,pv3,pv582677], .c 3, .c 17, .c 23,
  .c 3, .c 7, .c 5, .c 3, .c 709, .p pv11 [pv2,pv3,pv5,pv7,pv2081], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv13,pv26893], .c 37, .c 3, .c 11, .p pv2 [pv2,pv3,pv89,pv6547], .c 3, .c 13,
  .c 5, .c 3, .p pv2 [pv2,pv7,pv11,pv11351], .c 41, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv73,pv307],
  .c 3, .c 1031, .p pv2 [pv2,pv3,pv7,pv3083], .c 3, .c 67, .c 7, .c 3, .c 19, .c 5, .c 3, .c 1097,
  .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv582691], .c 3, .p pv7 [pv2,pv5,pv7,pv1427], .c 29, .c 3,
  .c 7, .c 197, .c 3, .c 11, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv8093], .c 3,
  .c 13, .c 127, .c 3, .c 89, .c 47, .c 3, .c 41, .c 5, .c 3, .c 7, .c 43, .c 3, .c 5, .c 11,
  .c 3, .c 29, .c 7, .c 3, .p pv3 [pv2,pv101,pv4327], .p pv2 [pv2,pv3,pv11,pv52973], .c 3,
  .p pv5 [pv2,pv59,pv29629], .c 5, .c 3, .c 11, .c 199, .c 3, .c 5, .c 17, .c 3, .c 7, .c 1259,
  .c 3, .c 19, .p pv17 [pv2,pv3,pv7,pv991], .c 3, .c 23, .c 5, .c 3, .c 13, .c 67, .c 3, .c 5,
  .c 139, .c 3, .c 17, .c 11, .c 3, .c 683, .c 773, .c 3,
]
private theorem h0427c17 : checkBlock 3496027 128 b0427c17 = true := by
  decide +kernel

private def b0427c18 : List Row := [
  .c 7, .c 5, .c 3, .c 557, .p pv17 [pv2,pv3,pv5,pv7,pv16649], .c 3, .c 5, .c 7, .c 3, .c 359,
  .c 79, .c 3, .p pv2 [pv2,pv11,pv158923], .p pv2 [pv2,pv3,pv291359], .c 3,
  .p pv3 [pv2,pv167,pv2617], .c 5, .c 3, .c 401, .c 509, .c 3, .c 5, .c 29, .c 3, .c 239, .c 113,
  .c 3, .c 13, .c 7, .c 3, .p pv5 [pv2,pv19,pv92009], .c 5, .c 3, .p pv2 [pv2,pv874087],
  .p pv3 [pv2,pv3,pv5,pv11,pv13,pv163], .c 3, .c 5, .c 41, .c 3, .c 11, .c 13, .c 3, .c 7, .c 293,
  .c 3, .c 17, .c 5, .c 3, .c 397, .c 7, .c 3, .c 5, .p pv17 [pv2,pv3,pv582731], .c 3, .c 23,
  .c 109, .c 3, .c 31, .c 19, .c 3, .p pv5 [pv2,pv7,pv13,pv19211], .c 5, .c 3, .c 7, .c 491, .c 3,
  .c 5, .c 223, .c 3, .p pv3 [pv2,pv5,pv174821], .c 7, .c 3, .c 11, .c 467, .c 3,
  .p pv3 [pv2,pv218527], .c 5, .c 3, .c 41, .c 13, .c 3, .c 5, .c 853, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv291371], .c 3, .p pv3 [pv2,pv19,pv23003], .c 31, .c 3, .c 37, .c 5, .c 3,
  .p pv2 [pv2,pv874117], .c 11, .c 3, .c 5, .p pv7 [pv2,pv3,pv291373], .c 3, .c 73, .c 23, .c 3,
  .p pv5 [pv2,pv7,pv249749], .p pv7 [pv2,pv3,pv145687], .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv809,pv2161], .c 29, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv317,pv1103], .c 19,
  .c 3, .c 59, .c 13, .c 3, .c 313, .c 5, .c 3, .c 23, .c 983, .c 3, .c 5, .c 11,
]
private theorem h0427c18 : checkBlock 3496283 128 b0427c18 = true := by
  decide +kernel

private def b0427c19 : List Row := [
  .c 3, .c 83, .c 17, .c 3, .c 157, .c 7, .c 3, .c 197, .c 5, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv5,pv17,pv857], .c 3, .c 5, .c 1471, .c 3, .c 13, .c 311, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv582763], .c 3, .c 31, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 13, .c 3,
  .c 229, .c 11, .c 3, .p pv5 [pv2,pv1171,pv1493], .p pv11 [pv2,pv3,pv19,pv71], .c 3,
  .p pv2 [pv2,pv7,pv47,pv2657], .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 19, .c 3, .c 43, .c 7,
  .c 3, .c 191, .c 821, .c 3, .c 769, .c 5, .c 3, .c 13, .c 137, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv97,pv751], .c 3, .c 7, .c 67, .c 3, .c 23, .c 11, .c 3,
  .p pv3 [pv2,pv113,pv967], .c 5, .c 3, .c 17, .c 251, .c 3, .c 5, .c 1321, .c 3, .c 11,
  .p pv17 [pv2,pv3,pv211,pv1381], .c 3, .p pv3 [pv2,pv7,pv17,pv3673], .c 1069, .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv227,pv3851], .p pv11 [pv2,pv3,pv5,pv7,pv16651], .c 3, .c 5, .c 7, .c 3,
  .c 89, .p pv2 [pv2,pv3,pv19,pv37,pv829], .c 3, .c 13, .p pv7 [pv2,pv3,pv53,pv2749], .c 3, .c 29,
  .c 5, .c 3, .c 181, .c 19, .c 3, .c 5, .c 17, .c 3, .p pv11 [pv2,pv5,pv71,pv197], .c 13, .c 3,
  .c 11, .c 7, .c 3, .c 1429, .c 5, .c 3, .c 31, .p pv2 [pv2,pv3,pv5,pv1439], .c 3, .c 5, .c 79,
  .c 3, .c 17, .c 131, .c 3, .c 7, .p pv2 [pv2,pv3,pv137,pv709], .c 3, .c 563,
]
private theorem h0427c19 : checkBlock 3496539 128 b0427c19 = true := by
  decide +kernel

private def b0427c20 : List Row := [
  .c 5, .c 3, .p pv11 [pv2,pv17,pv19,pv5413], .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv194267], .c 3,
  .p pv2 [pv2,pv5,pv89,pv3929], .c 167, .c 3, .c 19, .c 1861, .c 3, .c 11, .c 5, .c 3, .c 7,
  .c 13, .c 3, .c 5, .c 1559, .c 3, .p pv3 [pv2,pv5,pv87421], .c 7, .c 3, .c 47, .c 17, .c 3,
  .p pv2 [pv2,pv874213], .c 5, .c 3, .p pv7 [pv2,pv151,pv11579], .c 157, .c 3, .c 5, .c 11, .c 3,
  .c 7, .c 83, .c 3, .p pv2 [pv2,pv863,pv1013], .c 1087, .c 3, .c 13, .c 5, .c 3, .c 11, .c 1867,
  .c 3, .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv11,pv17], .c 211, .c 3, .c 29, .c 13, .c 3, .c 7,
  .c 5, .c 3, .c 73, .c 593, .c 3, .c 5, .c 7, .c 3, .c 19, .c 11, .c 3,
  .p pv3 [pv2,pv29,pv15073], .p pv3 [pv2,pv3,pv109,pv5347], .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv13,pv739], .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv83,pv3511], .c 3, .c 13,
  .c 71, .c 3, .c 193, .c 7, .c 3, .p pv2 [pv2,pv41,pv21323], .c 5, .c 3, .p pv2 [pv2,pv1748489],
  .c 37, .c 3, .c 5, .c 13, .c 3, .p pv7 [pv2,pv5,pv7,pv49957], .c 53, .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv17,pv163,pv631], .c 5, .c 3, .c 151, .c 7, .c 3, .c 5, .c 31, .c 3, .c 11, .c 29,
  .c 3, .c 199, .p pv2 [pv2,pv3,pv291419], .c 3, .c 379, .c 5, .c 3, .c 7, .c 1811, .c 3, .c 5,
  .c 109, .c 3,
]
private theorem h0427c20 : checkBlock 3496795 128 b0427c20 = true := by
  decide +kernel

private def b0427c21 : List Row := [
  .p pv2 [pv2,pv5,pv69941], .c 7, .c 3, .c 1289, .c 229, .c 3, .p pv5 [pv2,pv137,pv12763], .c 5,
  .c 3, .c 61, .p pv3 [pv2,pv3,pv5,pv17,pv6857], .c 3, .c 5, .c 89, .c 3, .c 7, .c 19, .c 3,
  .c 11, .p pv13 [pv2,pv3,pv7,pv1301], .c 3, .c 79, .c 5, .c 3, .c 53, .c 139, .c 3, .c 5, .c 59,
  .c 3, .c 263, .p pv5 [pv2,pv3,pv48571], .c 3, .c 13, .p pv3 [pv2,pv3,pv582853], .c 3, .c 7,
  .c 5, .c 3, .c 37, .c 11, .c 3, .c 5, .c 7, .c 3, .c 31, .c 13, .c 3, .c 43, .c 313, .c 3,
  .c 11, .c 5, .c 3, .c 19, .p pv17 [pv2,pv3,pv5,pv151,pv193], .c 3, .c 5, .c 1499, .c 3, .c 353,
  .c 23, .c 3, .c 41, .c 7, .c 3, .c 251, .c 5, .c 3, .c 17, .c 61, .c 3, .c 5, .c 11, .c 3,
  .p pv17 [pv2,pv5,pv7,pv1249], .c 31, .c 3, .c 7, .p pv17 [pv2,pv3,pv11,pv13,pv1019], .c 3,
  .p pv2 [pv2,pv874303], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv29,pv101,pv199],
  .c 3, .p pv23 [pv2,pv5,pv11,pv31793], .c 43, .c 3, .c 113, .c 991, .c 3,
  .p pv2 [pv2,pv7,pv23,pv10861], .c 5, .c 3, .c 7, .c 79, .c 3, .c 5, .c 17, .c 3, .c 449, .c 7,
  .c 3, .p pv2 [pv2,pv67,pv26099], .c 269, .c 3, .c 13, .c 5, .c 3, .p pv7 [pv2,pv1748639],
  .p pv29 [pv2,pv3,pv5,pv3643], .c 3, .c 5, .c 239, .c 3, .c 7, .p pv5 [pv2,pv3,pv19,pv5113],
  .c 3, .p pv3 [pv2,pv11,pv31,pv641], .c 13, .c 3, .p pv5 [pv2,pv179,pv9769], .c 5,
]
private theorem h0427c21 : checkBlock 3497051 128 b0427c21 = true := by
  decide +kernel

private def b0427c22 : List Row := [
  .c 3, .c 223, .c 19, .c 3, .c 5, .c 47, .c 3, .p pv3 [pv2,pv5,pv87433],
  .p pv2 [pv2,pv3,pv582887], .c 3, .c 31, .c 11, .c 3, .c 7, .c 5, .c 3, .c 509, .c 41, .c 3,
  .c 5, .c 7, .c 3, .c 11, .c 193, .c 3, .c 23, .c 17, .c 3, .c 467, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv19,pv173], .c 29, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv23,pv7603],
  .c 827, .c 3, .c 19, .c 7, .c 3, .c 17, .c 5, .c 3, .c 1447, .c 191, .c 3, .c 5, .c 751, .c 3,
  .c 47, .c 347, .c 3, .c 7, .p pv2 [pv2,pv3,pv21589], .c 3, .c 41, .c 5, .c 3, .c 13, .c 7, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv97151], .c 3, .c 887, .p pv2 [pv2,pv3,pv13,pv44839], .c 3,
  .p pv5 [pv2,pv1748723], .c 23, .c 3, .c 127, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 67, .c 3,
  .p pv17 [pv2,pv5,pv53,pv6599], .c 7, .c 3, .c 149, .p pv13 [pv2,pv3,pv17,pv2017], .c 3, .c 11,
  .c 5, .c 3, .c 157, .c 43, .c 3, .c 5, .c 709, .c 3, .c 7, .c 73, .c 3, .c 13, .c 107, .c 3,
  .c 31, .c 5, .c 3, .p pv7 [pv2,pv23,pv139,pv547], .p pv43 [pv2,pv3,pv5,pv13,pv19,pv59], .c 3,
  .c 5, .c 11, .c 3, .c 71, .c 13, .c 3, .c 83, .c 19, .c 3, .c 7, .c 5, .c 3, .c 11, .c 829,
  .c 3, .c 5, .c 7, .c 3, .c 599,
]
private theorem h0427c22 : checkBlock 3497307 128 b0427c22 = true := by
  decide +kernel

private def b0427c23 : List Row := [
  .c 17, .c 3, .c 79, .c 131, .c 3, .c 37, .c 5, .c 3, .c 59, .c 673, .c 3, .c 5, .c 23, .c 3,
  .p pv11 [pv2,pv5,pv349759], .c 11, .c 3, .c 17, .c 7, .c 3, .c 29, .c 5, .c 3,
  .p pv3 [pv2,pv437201], .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv107,pv227], .c 3, .c 373,
  .p pv3 [pv2,pv3,pv582937], .c 3, .c 7, .c 53, .c 3, .c 23, .c 5, .c 3, .c 967, .c 7, .c 3, .c 5,
  .c 37, .c 3, .c 307, .c 19, .c 3, .c 139, .c 11, .c 3, .c 13, .c 5, .c 3, .c 7,
  .p pv47 [pv2,pv3,pv5,pv11,pv3533], .c 3, .c 5, .c 331, .c 3, .c 11, .c 7, .c 3, .c 739, .c 13,
  .c 3, .c 47, .c 5, .c 3, .c 17, .c 109, .c 3, .c 5, .c 127, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv72869], .c 3, .p pv2 [pv2,pv17,pv51437], .c 29, .c 3, .c 97, .c 5, .c 3,
  .c 19, .c 101, .c 3, .c 5, .c 359, .c 3, .c 13, .p pv3 [pv2,pv3,pv2399], .c 3, .c 11, .c 43,
  .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv11,pv37,pv4297], .c 31, .c 3, .c 5, .c 7, .c 3, .c 23,
  .c 617, .c 3, .c 29, .p pv2 [pv2,pv3,pv317,pv613], .c 3, .c 191, .c 5, .c 3, .c 89, .c 11, .c 3,
  .c 5, .c 271, .c 3, .c 17, .c 157, .c 3, .c 269, .c 7, .c 3, .c 11, .c 5, .c 3,
]
private theorem h0427c23 : checkBlock 3497563 128 b0427c23 = true := by
  decide +kernel

private def b0427c24 : List Row := [
  .c 13, .c 937, .c 3, .c 5, .p pv2 [pv2,pv3,pv582971], .c 3, .c 131, .c 41, .c 3, .c 7, .c 179,
  .c 3, .c 19, .c 5, .c 3, .p pv3 [pv2,pv509,pv859], .c 7, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv174893], .c 23, .c 3, .p pv2 [pv2,pv1748933], .c 17, .c 3,
  .p pv3 [pv2,pv7,pv31231], .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 173, .c 3,
  .p pv2 [pv2,pv5,pv11,pv31799], .c 7, .c 3, .c 13, .p pv2 [pv2,pv3,pv582983], .c 3, .c 17, .c 5,
  .c 3, .c 23, .p pv3 [pv2,pv3,pv5,pv13,pv8969], .c 3, .c 5, .c 97, .c 3, .c 7, .c 11, .c 3,
  .c 1657, .p pv11 [pv2,pv3,pv7,pv47,pv443], .c 3, .c 59, .c 5, .c 3, .c 383, .c 73, .c 3, .c 5,
  .c 31, .c 3, .c 29, .c 1433, .c 3, .c 19, .p pv3 [pv2,pv3,pv211,pv307], .c 3, .c 7, .c 5, .c 3,
  .c 619, .c 17, .c 3, .c 5, .c 7, .c 3, .c 1543, .c 103, .c 3, .p pv2 [pv2,pv1748993], .c 11,
  .c 3, .p pv3 [pv2,pv59,pv7411], .c 5, .c 3, .p pv7 [pv2,pv7,pv249857], .c 13, .c 3, .c 5, .c 43,
  .c 3, .c 11, .p pv5 [pv2,pv3,pv7,pv661], .c 3, .c 37, .c 7, .c 3,
  .p pv5 [pv2,pv11,pv17,pv47,pv199], .c 5, .c 3, .c 233, .p pv11 [pv2,pv3,pv5,pv38867], .c 3,
  .c 5, .p pv5 [pv2,pv3,pv291503], .c 3, .c 79, .p pv2 [pv2,pv3,pv583007], .c 3, .c 7,
  .p pv29 [pv2,pv3,pv6073], .c 3, .c 13, .c 5, .c 3, .c 677, .c 7, .c 3, .c 5, .c 29, .c 3, .c 19,
  .c 17,
]
private theorem h0427c24 : checkBlock 3497819 128 b0427c24 = true := by
  decide +kernel

private def b0427c25 : List Row := [
  .c 3, .c 11, .c 13, .c 3, .p pv2 [pv2,pv7,pv249863], .c 5, .c 3, .c 7, .c 37, .c 3, .c 5,
  .c 757, .c 3, .p pv2 [pv2,pv5,pv34981], .c 7, .c 3, .c 17, .c 19, .c 3, .p pv3 [pv2,pv27329],
  .c 5, .c 3, .p pv7 [pv2,pv13,pv83,pv1621], .c 11, .c 3, .c 5, .c 293, .c 3, .c 7, .c 31, .c 3,
  .c 67, .c 23, .c 3, .c 11, .c 5, .c 3, .c 167, .c 107, .c 3, .c 5, .c 13, .c 3, .c 41, .c 47,
  .c 3, .c 61, .c 59, .c 3, .c 7, .c 5, .c 3, .c 43, .c 769, .c 3, .c 5, .c 7, .c 3,
  .p pv13 [pv2,pv5,pv349819], .p pv11 [pv2,pv3,pv17,pv1429], .c 3, .c 179, .c 79, .c 3, .c 1009,
  .c 5, .c 3, .c 11, .p pv31 [pv2,pv3,pv5,pv47,pv827], .c 3, .c 5, .c 151, .c 3, .c 199, .c 19,
  .c 3, .c 1019, .c 7, .c 3, .c 73, .c 5, .c 3, .c 37, .c 29, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv109,pv1783], .c 3, .p pv2 [pv2,pv5,pv7,pv1999], .c 11, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv107,pv5449], .c 3, .p pv5 [pv2,pv233,pv7507], .c 5, .c 3, .c 1637, .c 7, .c 3,
  .c 5, .c 17, .c 3, .c 821, .p pv3 [pv2,pv3,pv64783], .c 3, .c 13, .c 61, .c 3,
  .p pv2 [pv2,pv7,pv103,pv1213], .c 5, .c 3, .c 7, .p pv41 [pv2,pv3,pv5,pv13,pv23], .c 3, .c 5,
  .p pv29 [pv2,pv3,pv7,pv73,pv163], .c 3, .c 17, .c 7, .c 3, .c 761, .c 11, .c 3, .c 23, .c 5,
  .c 3, .c 647,
]
private theorem h0427c25 : checkBlock 3498075 128 b0427c25 = true := by
  decide +kernel

private def b0427c26 : List Row := [
  .c 1523, .c 3, .c 5, .c 19, .c 3, .c 7, .p pv3 [pv2,pv3,pv127,pv4591], .c 3, .c 523,
  .p pv2 [pv2,pv3,pv7,pv41647], .c 3, .c 877, .c 5, .c 3, .p pv7 [pv2,pv1749179], .c 1451, .c 3,
  .c 5, .c 83, .c 3, .c 53, .p pv2 [pv2,pv3,pv97177], .c 3, .p pv3 [pv2,pv7,pv179,pv349], .c 17,
  .c 3, .c 7, .c 5, .c 3, .c 1301, .c 13, .c 3, .c 5, .c 7, .c 3, .c 313,
  .p pv3 [pv2,pv3,pv97,pv6011], .c 3, .c 11, .p pv7 [pv2,pv3,pv48589], .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv11,pv22717], .c 601, .c 3, .c 5, .c 431, .c 3, .c 157, .c 229, .c 3, .c 43,
  .c 7, .c 3, .c 13, .c 5, .c 3, .c 1249, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv11213], .c 3,
  .c 23, .c 953, .c 3, .c 7, .c 13, .c 3, .c 11, .c 5, .c 3, .p pv19 [pv2,pv1749239], .c 7, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv131,pv4451], .c 3, .c 139, .p pv2 [pv2,pv3,pv47,pv6203], .c 3, .c 983,
  .c 97, .c 3, .p pv5 [pv2,pv7,pv29,pv1231], .c 5, .c 3, .c 7, .c 193, .c 3, .c 5, .c 11, .c 3,
  .c 13, .c 7, .c 3, .c 19, .c 461, .c 3, .c 61, .c 5, .c 3, .c 11, .c 257, .c 3, .c 5, .c 13,
  .c 3, .c 7, .c 23, .c 3, .p pv2 [pv2,pv874639], .p pv3 [pv2,pv3,pv7,pv83299], .c 3, .c 643,
  .c 5, .c 3, .c 137, .c 41, .c 3, .c 5, .p pv7 [pv2,pv3,pv23,pv3169], .c 3,
  .p pv2 [pv2,pv5,pv174929], .c 11, .c 3,
]
private theorem h0427c26 : checkBlock 3498331 128 b0427c26 = true := by
  decide +kernel

private def b0427c27 : List Row := [
  .p pv5 [pv2,pv7,pv13,pv47,pv409], .c 29, .c 3, .c 7, .c 5, .c 3, .c 13, .c 103, .c 3, .c 5,
  .c 7, .c 3, .c 367, .p pv2 [pv2,pv3,pv13,pv41,pv547], .c 3, .c 17, .c 199, .c 3,
  .p pv5 [pv2,pv19,pv23,pv4003], .c 5, .c 3, .c 31, .c 659, .c 3, .c 5, .c 977, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv7,pv27767], .c 3, .c 29, .c 7, .c 3, .c 41, .c 5, .c 3, .c 1619,
  .p pv7 [pv2,pv3,pv5,pv11,pv19,pv31], .c 3, .c 5, .c 71, .c 3, .c 11, .c 67, .c 3, .c 7, .c 19,
  .c 3, .c 37, .c 5, .c 3, .c 53, .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv48593], .c 3,
  .p pv2 [pv2,pv5,pv59,pv593], .c 13, .c 3, .c 859, .p pv2 [pv2,pv3,pv291559], .c 3, .c 293, .c 5,
  .c 3, .c 7, .c 239, .c 3, .c 5, .c 47, .c 3, .c 281, .c 7, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv43,pv71,pv191], .c 3, .p pv5 [pv2,pv13,pv53,pv2539], .c 5, .c 3,
  .p pv2 [pv2,pv11,pv131,pv607], .c 227, .c 3, .c 5, .c 37, .c 3, .c 7, .c 29, .c 3,
  .p pv5 [pv2,pv1749383], .c 139, .c 3, .p pv2 [pv2,pv874693], .c 5, .c 3, .c 1051, .c 11, .c 3,
  .c 5, .c 17, .c 3, .c 109, .c 19, .c 3, .p pv2 [pv2,pv7,pv17851], .p pv3 [pv2,pv3,pv257,pv2269],
  .c 3, .c 7, .c 5, .c 3, .c 71, .p pv2 [pv2,pv3,pv5,pv7,pv16661], .c 3, .c 5, .c 7, .c 3, .c 17,
  .p pv5 [pv2,pv3,pv64793], .c 3, .p pv2 [pv2,pv1749413], .c 23, .c 3, .c 13, .c 5, .c 3, .c 1307,
  .p pv7 [pv2,pv3,pv5,pv9719],
]
private theorem h0427c27 : checkBlock 3498587 128 b0427c27 = true := by
  decide +kernel

private def b0427c28 : List Row := [
  .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv19,pv29,pv127], .p pv2 [pv2,pv3,pv7,pv23,pv1811],
  .c 3, .c 89, .c 7, .c 3, .p pv5 [pv2,pv1749431], .c 5, .c 3, .c 11,
  .p pv41 [pv2,pv3,pv5,pv223,pv523], .c 3, .c 5, .c 31, .c 3, .c 271, .c 269, .c 3, .c 7, .c 17,
  .c 3, .p pv2 [pv2,pv874723], .c 5, .c 3, .c 41, .c 7, .c 3, .c 5, .c 19, .c 3, .c 13, .c 11,
  .c 3, .c 197, .p pv3 [pv2,pv3,pv583153], .c 3, .c 17, .c 5, .c 3, .c 7, .c 421, .c 3, .c 5,
  .c 13, .c 3, .c 67, .c 7, .c 3, .p pv2 [pv2,pv11,pv89,pv1787], .p pv2 [pv2,pv3,pv83,pv1171],
  .c 3, .c 43, .c 5, .c 3, .p pv7 [pv2,pv163,pv10733], .c 233, .c 3, .c 5, .c 23, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv151,pv1931], .c 3, .c 127, .c 11, .c 3, .c 19, .c 5, .c 3, .c 13, .c 17, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv43,pv6781], .c 3, .c 11, .c 1223, .c 3, .c 53, .c 47, .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv1749509], .c 19, .c 3, .c 5, .c 7, .c 3, .c 83, .c 1667, .c 3, .c 827,
  .c 43, .c 3, .p pv2 [pv2,pv17,pv102913], .c 5, .c 3, .p pv3 [pv2,pv7,pv62483], .c 727, .c 3,
  .c 5, .c 449, .c 3, .c 311, .c 31, .c 3, .c 11, .c 7, .c 3, .c 433, .c 5, .c 3, .c 241, .c 97,
  .c 3, .c 5, .p pv7 [pv2,pv3,pv583181], .c 3, .p pv13 [pv2,pv5,pv7,pv37,pv193], .c 13, .c 3,
  .c 7,
]
private theorem h0427c28 : checkBlock 3498843 128 b0427c28 = true := by
  decide +kernel

private def b0427c29 : List Row := [
  .p pv2 [pv2,pv3,pv173,pv3371], .c 3, .c 47, .c 5, .c 3, .c 73, .c 7, .c 3, .c 5, .c 137, .c 3,
  .c 163, .c 151, .c 3, .c 17, .p pv11 [pv2,pv3,pv23,pv2113], .c 3, .c 11, .c 5, .c 3, .c 7,
  .c 131, .c 3, .c 5, .c 79, .c 3, .c 23, .c 7, .c 3, .c 1423, .c 547, .c 3,
  .p pv2 [pv2,pv1749581], .c 5, .c 3, .c 29, .c 13, .c 3, .c 5, .c 11, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv73,pv2663], .c 3, .c 31, .p pv2 [pv2,pv3,pv7,pv11,pv541], .c 3,
  .p pv3 [pv2,pv19,pv23021], .c 5, .c 3, .c 11, .c 37, .c 3, .c 5, .c 619, .c 3, .c 19, .c 89,
  .c 3, .p pv3 [pv2,pv7,pv157,pv199], .c 53, .c 3, .c 7, .c 5, .c 3, .c 17, .c 59, .c 3, .c 5,
  .c 7, .c 3, .c 1747, .c 11, .c 3, .p pv5 [pv2,pv17,pv101,pv1019], .c 13, .c 3,
  .p pv2 [pv2,pv874813], .c 5, .c 3, .p pv2 [pv2,pv7,pv249947], .p pv2 [pv2,pv3,pv5,pv58321],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv23,pv25357], .c 3, .c 113, .c 181, .c 3,
  .p pv2 [pv2,pv11,pv67,pv1187], .c 7, .c 3, .c 193, .c 5, .c 3, .c 23, .c 47, .c 3, .c 5, .c 17,
  .c 3, .c 13, .c 1181, .c 3, .c 7, .c 11, .c 3, .p pv3 [pv2,pv23,pv37,pv257], .c 5, .c 3,
  .p pv13 [pv2,pv167,pv10477], .c 7, .c 3, .c 5, .c 13, .c 3, .c 11, .p pv2 [pv2,pv3,pv331,pv881],
  .c 3, .p pv3 [pv2,pv109,pv4013], .p pv2 [pv2,pv3,pv47,pv12409], .c 3, .c 29, .c 5, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv5,pv41,pv569], .c 3,
]
private theorem h0427c29 : checkBlock 3499099 128 b0427c29 = true := by
  decide +kernel

private def b0427c30 : List Row := [
  .c 5, .c 491, .c 3, .p pv3 [pv2,pv5,pv21871], .c 7, .c 3, .p pv5 [pv2,pv13,pv134591],
  .p pv7 [pv2,pv3,pv145807], .c 3, .c 31, .c 5, .c 3, .c 13, .c 23, .c 3, .c 5, .c 61, .c 3, .c 7,
  .c 523, .c 3, .c 11, .c 17, .c 3, .c 131, .c 5, .c 3, .p pv3 [pv2,pv11,pv59,pv337],
  .p pv11 [pv2,pv3,pv5,pv67,pv1741], .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv953], .c 3, .c 269, .c 37,
  .c 3, .c 23, .p pv2 [pv2,pv3,pv291619], .c 3, .c 7, .c 5, .c 3, .c 19, .c 11, .c 3, .c 5, .c 7,
  .c 3, .c 461, .p pv7 [pv2,pv3,pv11,pv8837], .c 3, .c 13, .c 29, .c 3, .c 11, .c 5, .c 3, .c 43,
  .c 383, .c 3, .c 5, .c 19, .c 3, .p pv3 [pv2,pv5,pv89,pv983], .c 13, .c 3, .c 499, .c 7, .c 3,
  .c 307, .c 5, .c 3, .p pv2 [pv2,pv1749749], .c 17, .c 3, .c 5, .c 11, .c 3,
  .p pv13 [pv2,pv5,pv7,pv49993], .p pv5 [pv2,pv3,pv43,pv3391], .c 3, .c 7, .c 23, .c 3,
  .p pv2 [pv2,pv13,pv134597], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 53, .c 3,
  .p pv2 [pv2,pv5,pv11,pv15907], .c 929, .c 3, .c 73, .c 101, .c 3, .c 19, .c 5, .c 3, .c 7,
  .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv97,pv859], .c 3, .c 37, .c 7, .c 3,
  .p pv3 [pv2,pv151,pv2897], .c 941, .c 3, .p pv5 [pv2,pv487,pv3593], .c 5, .c 3,
  .p pv2 [pv2,pv23,pv38039], .c 19, .c 3, .c 5, .p pv2 [pv2,pv3,pv41,pv2371], .c 3, .c 7, .c 17,
  .c 3, .p pv13 [pv2,pv11,pv159073], .p pv19 [pv2,pv3,pv7,pv37,pv563],
]
private theorem h0427c30 : checkBlock 3499355 128 b0427c30 = true := by
  decide +kernel

private def b0427c31 : List Row := [
  .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv277,pv6317], .c 31, .c 3, .c 5, .c 797, .c 3, .c 61,
  .c 29, .c 3, .c 17, .c 11, .c 3, .c 7, .c 5, .c 3, .c 107, .p pv2 [pv2,pv3,pv5,pv7,pv11,pv101],
  .c 3, .c 5, .c 7, .c 3, .c 11, .c 97, .c 3, .c 19, .c 193, .c 3, .p pv3 [pv2,pv11,pv39769],
  .c 5, .c 3, .p pv7 [pv2,pv7,pv13,pv41,pv67], .p pv17 [pv2,pv3,pv5,pv23,pv317], .c 3, .c 5,
  .c 157, .c 3, .c 13, .c 73, .c 3, .p pv3 [pv2,pv53,pv4127], .c 7, .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv439,pv1993], .p pv3 [pv2,pv3,pv5,pv116657], .c 3, .c 5, .c 13, .c 3,
  .p pv37 [pv2,pv5,pv7,pv29,pv431], .c 113, .c 3, .c 7, .c 541, .c 3, .c 1231, .c 5, .c 3, .c 17,
  .c 7, .c 3, .c 5, .c 89, .c 3, .c 101, .c 61, .c 3, .p pv2 [pv2,pv13,pv17,pv37,pv107],
  .p pv3 [pv2,pv3,pv194431], .c 3, .p pv5 [pv2,pv7,pv19,pv59,pv223], .c 5, .c 3, .c 7, .c 11,
  .c 3, .c 5, .c 1373, .c 3, .c 19, .c 7, .c 3, .p pv2 [pv2,pv1093,pv1601], .c 787, .c 3, .c 11,
  .c 5, .c 3, .p pv7 [pv2,pv1749899], .c 41, .c 3, .c 5, .c 17, .c 3, .c 7, .c 43, .c 3, .c 463,
  .c 19, .c 3, .p pv5 [pv2,pv1749911], .c 5, .c 3, .p pv2 [pv2,pv874957],
  .p pv3 [pv2,pv3,pv5,pv37,pv1051], .c 3, .c 5, .c 11, .c 3, .c 17, .p pv3 [pv2,pv3,pv41,pv347],
  .c 3, .c 13, .c 643, .c 3, .c 7, .c 5, .c 3, .c 11, .c 83, .c 3, .c 5,
]
private theorem h0427c31 : checkBlock 3499611 128 b0427c31 = true := by
  decide +kernel

def rows0427 : List Row :=
  b0427c00 ++ b0427c01 ++ b0427c02 ++ b0427c03 ++ b0427c04 ++ b0427c05 ++ b0427c06 ++ b0427c07 ++
  b0427c08 ++ b0427c09 ++ b0427c10 ++ b0427c11 ++ b0427c12 ++ b0427c13 ++ b0427c14 ++ b0427c15 ++
  b0427c16 ++ b0427c17 ++ b0427c18 ++ b0427c19 ++ b0427c20 ++ b0427c21 ++ b0427c22 ++ b0427c23 ++
  b0427c24 ++ b0427c25 ++ b0427c26 ++ b0427c27 ++ b0427c28 ++ b0427c29 ++ b0427c30 ++ b0427c31

theorem checked0427 : checkBlock 3491675 4096 rows0427 = true :=
  checkBlock_append h0427c00 (
    checkBlock_append h0427c01 (
    checkBlock_append h0427c02 (
    checkBlock_append h0427c03 (
    checkBlock_append h0427c04 (
    checkBlock_append h0427c05 (
    checkBlock_append h0427c06 (
    checkBlock_append h0427c07 (
    checkBlock_append h0427c08 (
    checkBlock_append h0427c09 (
    checkBlock_append h0427c10 (
    checkBlock_append h0427c11 (
    checkBlock_append h0427c12 (
    checkBlock_append h0427c13 (
    checkBlock_append h0427c14 (
    checkBlock_append h0427c15 (
    checkBlock_append h0427c16 (
    checkBlock_append h0427c17 (
    checkBlock_append h0427c18 (
    checkBlock_append h0427c19 (
    checkBlock_append h0427c20 (
    checkBlock_append h0427c21 (
    checkBlock_append h0427c22 (
    checkBlock_append h0427c23 (
    checkBlock_append h0427c24 (
    checkBlock_append h0427c25 (
    checkBlock_append h0427c26 (
    checkBlock_append h0427c27 (
    checkBlock_append h0427c28 (
    checkBlock_append h0427c29 (
    checkBlock_append h0427c30 (
    h0427c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
