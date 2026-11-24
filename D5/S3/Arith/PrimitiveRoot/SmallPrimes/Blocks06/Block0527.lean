/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks06/Block0527
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks06/Block0527.checked0527
   digest: Kernel proof of checker success on extended consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table031
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table051
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table057
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table064
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table074
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table086
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table103
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table126
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table158
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table159
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table162
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table163
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table165
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table167
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table170
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table173
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table178
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table185
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table193
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table208
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table228
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables03.Table257

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0527c00 : List Row := [
  .c 5, .c 3, .c 29, .c 457, .c 3, .c 5, .c 7, .c 3, .c 13, .c 89, .c 3, .p pv3 [pv2,pv269431],
  .c 151, .c 3, .c 1867, .c 5, .c 3, .c 293, .c 11, .c 3, .c 5, .c 13, .c 3, .c 1451, .c 107,
  .c 3, .p pv5 [pv2,pv2155463], .c 7, .c 3, .c 11, .c 5, .c 3, .c 283, .c 211, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv139,pv1723], .c 3, .c 79, .c 31, .c 3, .c 7, .c 23, .c 3,
  .p pv2 [pv2,pv17,pv103,pv1231], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 11, .c 3, .c 37, .c 101,
  .c 3, .c 173, .p pv13 [pv2,pv3,pv11,pv2969], .c 3, .c 463, .c 5, .c 3, .c 7,
  .p pv19 [pv2,pv3,pv5,pv479], .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv102643], .c 3,
  .p pv2 [pv2,pv5,pv11,pv39191], .c 7, .c 3, .c 149, .p pv2 [pv2,pv3,pv37,pv6473], .c 3, .c 397,
  .c 5, .c 3, .c 919, .p pv7 [pv2,pv3,pv5,pv17,pv79,pv107], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv179,pv223], .c 3, .c 7, .c 11, .c 3, .c 13, .c 71, .c 3, .c 29, .c 5, .c 3,
  .c 109, .c 191, .c 3, .c 5, .c 1153, .c 3, .c 59, .c 13, .c 3, .c 31, .c 131, .c 3, .c 7, .c 5,
  .c 3, .c 523, .c 419, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv19,pv2269], .c 83, .c 3,
  .p pv2 [pv2,pv653,pv3301], .c 11, .c 3, .p pv3 [pv2,pv13,pv41453], .c 5, .c 3, .c 19,
  .p pv7 [pv2,pv3,pv5,pv11,pv23,pv71], .c 3, .c 5, .p pv5 [pv2,pv3,pv53,pv4519], .c 3,
]
private theorem h0527c00 : checkBlock 4310875 128 b0527c00 = true := by
  decide +kernel

private def b0527c01 : List Row := [
  .c 11, .p pv11 [pv2,pv3,pv7,pv17,pv3019], .c 3, .c 43, .c 7, .c 3, .c 23, .c 5, .c 3, .c 17,
  .c 13, .c 3, .c 5, .c 19, .c 3, .c 73, .p pv3 [pv2,pv3,pv239509], .c 3, .c 7, .c 29, .c 3,
  .p pv2 [pv2,pv1077793], .c 5, .c 3, .c 53, .c 7, .c 3, .c 5, .c 163, .c 3, .c 41,
  .p pv5 [pv2,pv3,pv179633], .c 3, .c 11, .c 233, .c 3, .c 13, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv131,pv1097], .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv157,pv1373], .c 7,
  .c 3, .c 29, .c 13, .c 3, .c 19, .c 5, .c 3, .c 181, .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv718541], .c 3, .c 7, .c 137, .c 3, .p pv3 [pv2,pv29,pv18583], .c 223, .c 3,
  .c 11, .c 5, .c 3, .c 83, .c 19, .c 3, .c 5, .c 37, .c 3, .c 13, .p pv2 [pv2,pv3,pv718547],
  .c 3, .c 389, .c 113, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv449,pv4801],
  .p pv2 [pv2,pv3,pv5,pv7,pv2053], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv47,pv9173], .c 569,
  .c 3, .p pv2 [pv2,pv67,pv16087], .c 17, .c 3, .p pv2 [pv2,pv2155661], .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv143711], .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv10567], .c 3, .c 131, .c 29,
  .c 3, .c 19, .c 7, .c 3, .c 17, .c 5, .c 3, .c 13, .p pv7 [pv2,pv3,pv5,pv499], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv19,pv59,pv641], .c 3, .p pv2 [pv2,pv5,pv7,pv17,pv3623], .c 11, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv239521], .c 3, .c 67, .c 5,
]
private theorem h0527c01 : checkBlock 4311131 128 b0527c01 = true := by
  decide +kernel

private def b0527c02 : List Row := [
  .c 3, .c 1019, .c 7, .c 3, .c 5, .c 1619, .c 3, .c 29, .p pv5 [pv2,pv3,pv113,pv6359], .c 3,
  .p pv5 [pv2,pv11,pv195973], .p pv13 [pv2,pv3,pv89821], .c 3, .p pv2 [pv2,pv7,pv21997], .c 5,
  .c 3, .c 7, .c 17, .c 3, .c 5, .c 89, .c 3, .c 383, .c 7, .c 3, .c 13, .c 11, .c 3, .c 191,
  .c 5, .c 3, .c 31, .c 47, .c 3, .c 5, .c 1009, .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv2155733],
  .c 1877, .c 3, .p pv3 [pv2,pv11,pv17,pv131], .c 5, .c 3, .c 479, .c 43, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv239527], .c 3, .c 751, .c 1601, .c 3, .c 53, .c 19, .c 3, .c 7, .c 5, .c 3,
  .c 1279, .c 23, .c 3, .c 5, .c 7, .c 3, .c 607, .c 17, .c 3, .c 11,
  .p pv17 [pv2,pv3,pv13,pv1063], .c 3, .p pv2 [pv2,pv269,pv4007], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv11,pv27997], .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv29,pv71,pv349], .c 3,
  .p pv17 [pv2,pv5,pv53,pv1627], .c 97, .c 3, .c 17, .c 7, .c 3, .p pv2 [pv2,pv2155781], .c 5,
  .c 3, .p pv3 [pv2,pv269473], .c 11, .c 3, .c 5, .p pv17 [pv2,pv3,pv19961], .c 3, .c 1607, .c 79,
  .c 3, .c 7, .c 101, .c 3, .c 11, .c 5, .c 3, .c 73, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv13,pv167,pv331], .c 3, .p pv2 [pv2,pv5,pv37,pv43,pv271], .c 19, .c 3, .c 71,
  .c 13, .c 3, .c 631, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv5323], .c 3, .c 5, .c 11, .c 3,
  .c 139,
]
private theorem h0527c02 : checkBlock 4311387 128 b0527c02 = true := by
  decide +kernel

private def b0527c03 : List Row := [
  .c 7, .c 3, .c 37, .c 23, .c 3, .c 43, .c 5, .c 3, .c 11, .c 59, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv31,pv7727], .c 3, .c 7, .p pv5 [pv2,pv3,pv23,pv73,pv107], .c 3,
  .p pv3 [pv2,pv17,pv163,pv389], .c 173, .c 3, .c 41, .c 5, .c 3, .c 19, .c 29, .c 3, .c 5, .c 13,
  .c 3, .p pv2 [pv2,pv5,pv43117], .c 11, .c 3, .c 887, .c 53, .c 3, .c 7, .c 5, .c 3, .c 443,
  .c 37, .c 3, .c 5, .c 7, .c 3, .c 241, .c 47, .c 3, .c 557, .c 43, .c 3,
  .p pv5 [pv2,pv1033,pv2087], .c 5, .c 3, .c 13, .p pv11 [pv2,pv3,pv5,pv5749], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv119771], .c 3, .c 17, .c 911, .c 3, .c 83, .c 7, .c 3, .c 167, .c 5, .c 3,
  .c 59, .p pv7 [pv2,pv3,pv5,pv11,pv47,pv139], .c 3, .c 5, .c 23, .c 3, .c 11, .c 1307, .c 3,
  .c 7, .c 239, .c 3, .c 19, .c 5, .c 3, .p pv3 [pv2,pv16843], .c 7, .c 3, .c 5, .c 397, .c 3,
  .c 31, .p pv5 [pv2,pv3,pv19,pv109,pv347], .c 3, .c 13, .c 17, .c 3, .c 23, .c 5, .c 3, .c 7,
  .c 19, .c 3, .c 5, .c 41, .c 3, .c 701, .c 7, .c 3, .c 11, .c 499, .c 3, .c 17, .c 5, .c 3,
  .c 37, .p pv13 [pv2,pv3,pv5,pv143729], .c 3, .c 5, .p pv5 [pv2,pv3,pv359323], .c 3, .c 7, .c 31,
  .c 3, .p pv5 [pv2,pv107,pv20149], .c 103, .c 3, .p pv2 [pv2,pv13,pv101,pv821], .c 5, .c 3,
]
private theorem h0527c03 : checkBlock 4311643 128 b0527c03 = true := by
  decide +kernel

private def b0527c04 : List Row := [
  .c 79, .c 11, .c 3, .c 5, .c 61, .c 3, .c 43, .p pv5 [pv2,pv3,pv11,pv16333], .c 3, .c 19, .c 67,
  .c 3, .c 7, .c 5, .c 3, .c 41, .c 13, .c 3, .c 5, .c 7, .c 3, .c 97, .c 37, .c 3,
  .p pv2 [pv2,pv257,pv8389], .c 359, .c 3, .c 401, .c 5, .c 3, .p pv7 [pv2,pv7,pv479,pv643],
  .c 89, .c 3, .c 5, .c 11, .c 3, .c 23, .c 787, .c 3, .p pv3 [pv2,pv31,pv17387], .c 7, .c 3,
  .c 13, .c 5, .c 3, .c 11, .c 1811, .c 3, .c 5, .c 43, .c 3, .c 547,
  .p pv2 [pv2,pv3,pv163,pv4409], .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv19,pv56737], .c 5, .c 3,
  .p pv2 [pv2,pv2156009], .c 7, .c 3, .c 5, .c 53, .c 3, .c 19, .c 11, .c 3, .c 73, .c 29, .c 3,
  .c 71, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv17,pv19,pv89], .c 3, .c 5, .c 79, .c 3, .c 13,
  .c 7, .c 3, .c 17, .c 19, .c 3, .p pv3 [pv2,pv539009], .c 5, .c 3, .p pv7 [pv2,pv2156039],
  .c 293, .c 3, .c 5, .c 13, .c 3, .c 7, .c 41, .c 3, .c 29, .c 11, .c 3,
  .p pv5 [pv2,pv587,pv3673], .c 5, .c 3, .c 23, .p pv3 [pv2,pv3,pv5,pv11,pv73,pv179], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv13309], .c 3, .c 11, .p pv2 [pv2,pv3,pv307,pv2341], .c 3, .c 131, .c 1087,
  .c 3, .c 7, .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv7,pv10267], .c 3, .c 5, .c 7, .c 3, .c 61,
  .p pv5 [pv2,pv3,pv13,pv17,pv271],
]
private theorem h0527c04 : checkBlock 4311899 128 b0527c04 = true := by
  decide +kernel

private def b0527c05 : List Row := [
  .c 3, .p pv2 [pv2,pv47,pv22937], .c 1663, .c 3, .c 1283, .c 5, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv5,pv15971], .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv8167], .c 3,
  .p pv2 [pv2,pv5,pv251,pv859], .c 19, .c 3, .c 11, .c 7, .c 3, .c 31, .c 5, .c 3, .c 193, .c 23,
  .c 3, .c 5, .c 107, .c 3, .c 971, .c 29, .c 3, .c 7, .c 503, .c 3, .p pv5 [pv2,pv2156111], .c 5,
  .c 3, .p pv2 [pv2,pv89,pv12113], .c 7, .c 3, .c 5, .c 17, .c 3, .c 1979, .c 13, .c 3, .c 23,
  .c 1579, .c 3, .c 11, .c 5, .c 3, .c 7, .p pv19 [pv2,pv3,pv5,pv23957], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv102673], .c 3, .c 17, .c 7, .c 3, .c 239, .p pv11 [pv2,pv3,pv19,pv467],
  .c 3, .p pv2 [pv2,pv13,pv165857], .c 5, .c 3, .c 179, .p pv3 [pv2,pv3,pv5,pv143743], .c 3, .c 5,
  .c 11, .c 3, .c 7, .c 421, .c 3, .c 1097, .p pv2 [pv2,pv3,pv7,pv11,pv13,pv359], .c 3, .c 37,
  .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 71, .c 3, .p pv2 [pv2,pv5,pv11,pv197,pv199],
  .p pv5 [pv2,pv3,pv39929], .c 3, .p pv3 [pv2,pv7,pv139,pv277], .c 17, .c 3, .c 7, .c 5, .c 3,
  .c 137, .p pv17 [pv2,pv3,pv5,pv7,pv37], .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv13,pv8293],
  .c 11, .c 3, .c 109, .c 59, .c 3, .c 13, .c 5, .c 3, .c 31, .p pv7 [pv2,pv3,pv5,pv41,pv1753],
  .c 3, .c 5, .c 29, .c 3, .c 47, .p pv5 [pv2,pv3,pv7,pv19,pv193], .c 3, .c 101, .c 7, .c 3,
  .p pv2 [pv2,pv73,pv29537], .c 5, .c 3, .c 151,
]
private theorem h0527c05 : checkBlock 4312155 128 b0527c05 = true := by
  decide +kernel

private def b0527c06 : List Row := [
  .c 19, .c 3, .c 5, .p pv5 [pv2,pv3,pv29,pv1549], .c 3, .c 41, .c 271, .c 3, .c 7, .c 11, .c 3,
  .p pv3 [pv2,pv269527], .c 5, .c 3, .c 1049, .c 7, .c 3, .c 5, .p pv17 [pv2,pv3,pv718741], .c 3,
  .c 11, .c 491, .c 3, .c 1741, .c 2003, .c 3, .p pv7 [pv2,pv7,pv11,pv41,pv683], .c 5, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv5,pv43,pv3343], .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv26953], .c 7, .c 3,
  .c 19, .p pv7 [pv2,pv3,pv179687], .c 3, .p pv2 [pv2,pv17,pv63419], .c 5, .c 3,
  .p pv2 [pv2,pv37,pv101,pv577], .p pv2 [pv2,pv3,pv5,pv23], .c 3, .c 5, .c 103, .c 3, .c 7, .c 43,
  .c 3, .c 11, .p pv3 [pv2,pv3,pv7,pv102679], .c 3, .c 23, .c 5, .c 3, .c 13, .c 79, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv179689], .c 3, .p pv2 [pv2,pv5,pv71,pv3037], .c 17, .c 3,
  .p pv2 [pv2,pv7,pv23,pv59,pv227], .p pv2 [pv2,pv3,pv73,pv547], .c 3, .c 7, .c 5, .c 3,
  .p pv11 [pv2,pv2156279], .c 11, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv431257], .c 619, .c 3,
  .c 17, .c 47, .c 3, .c 11, .c 5, .c 3, .c 67, .c 1063, .c 3, .c 5, .c 83, .c 3, .c 19, .c 941,
  .c 3, .c 13, .c 7, .c 3, .c 277, .c 5, .c 3, .c 29, .c 73, .c 3, .c 5, .c 11, .c 3,
  .p pv11 [pv2,pv5,pv7,pv61609], .c 13, .c 3, .c 7, .c 19, .c 3, .p pv2 [pv2,pv43,pv50147], .c 5,
  .c 3, .c 11, .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv67,pv149], .c 3, .c 23, .c 53, .c 3,
]
private theorem h0527c06 : checkBlock 4312411 128 b0527c06 = true := by
  decide +kernel

private def b0527c07 : List Row := [
  .c 41, .c 1723, .c 3, .c 47, .c 5, .c 3, .c 7, .c 1553, .c 3, .c 5, .c 181, .c 3,
  .p pv2 [pv2,pv5,pv431269], .c 7, .c 3, .p pv3 [pv2,pv17,pv19,pv1669],
  .p pv2 [pv2,pv3,pv13,pv55291], .c 3, .p pv5 [pv2,pv2156351], .c 5, .c 3, .c 457, .c 13, .c 3,
  .c 5, .c 97, .c 3, .c 7, .c 59, .c 3, .p pv5 [pv2,pv11,pv196033],
  .p pv13 [pv2,pv3,pv7,pv43,pv199], .c 3, .p pv2 [pv2,pv1078183], .c 5, .c 3,
  .p pv2 [pv2,pv2156369], .p pv7 [pv2,pv3,pv5,pv71879], .c 3, .c 5, .c 17, .c 3, .c 31, .c 19,
  .c 3, .c 37, .c 11, .c 3, .c 7, .c 5, .c 3, .c 53, .c 43, .c 3, .c 5, .c 7, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv31,pv59,pv131], .c 3, .p pv2 [pv2,pv2156393], .c 13, .c 3, .c 29, .c 5, .c 3,
  .c 23, .c 101, .c 3, .c 5, .p pv5 [pv2,pv3,pv718801], .c 3, .p pv2 [pv2,pv5,pv19,pv22699],
  .c 31, .c 3, .c 163, .c 7, .c 3, .p pv5 [pv2,pv23,pv29,pv53,pv61], .c 5, .c 3, .c 19, .c 37,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv10891], .c 3, .c 13, .c 389, .c 3, .c 7, .c 17, .c 3,
  .p pv2 [pv2,pv541,pv1993], .c 5, .c 3, .p pv2 [pv2,pv11,pv196039], .c 7, .c 3, .c 5, .c 13,
  .c 3, .c 113, .p pv5 [pv2,pv3,pv41,pv487], .c 3, .c 269, .p pv3 [pv2,pv3,pv718813], .c 3, .c 17,
  .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 137, .c 3, .c 1109, .c 7, .c 3,
  .p pv2 [pv2,pv13,pv31,pv5351], .c 29, .c 3, .c 11, .c 5, .c 3, .c 13, .c 197,
]
private theorem h0527c07 : checkBlock 4312667 128 b0527c07 = true := by
  decide +kernel

private def b0527c08 : List Row := [
  .c 3, .c 5, .c 199, .c 3, .c 7, .c 251, .c 3, .c 23, .p pv3 [pv2,pv3,pv7,pv29,pv3541], .c 3,
  .c 19, .c 5, .c 3, .c 1409, .c 17, .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv23,pv293], .c 383,
  .c 3, .c 29, .p pv7 [pv2,pv3,pv11,pv17,pv31], .c 3, .c 7, .c 5, .c 3, .c 11, .c 19, .c 3, .c 5,
  .c 7, .c 3, .c 67, .c 751, .c 3, .c 13, .c 31, .c 3, .c 101, .c 5, .c 3, .c 1361, .c 937, .c 3,
  .c 5, .c 431, .c 3, .c 109, .c 11, .c 3, .p pv2 [pv2,pv359,pv6007], .c 7, .c 3,
  .p pv3 [pv2,pv539129], .c 5, .c 3, .c 859, .p pv7 [pv2,pv3,pv5,pv17971], .c 3, .c 5, .c 127,
  .c 3, .c 211, .c 17, .c 3, .c 7, .c 73, .c 3, .c 107, .c 5, .c 3, .c 281, .c 7, .c 3, .c 5,
  .c 41, .c 3, .p pv3 [pv2,pv5,pv107827], .c 29, .c 3, .c 17, .c 11, .c 3,
  .p pv2 [pv2,pv7,pv31,pv4969], .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv34231],
  .c 3, .c 11, .c 7, .c 3, .c 1399, .p pv3 [pv2,pv3,pv41,pv89,pv197], .c 3, .c 31, .c 5, .c 3,
  .p pv3 [pv2,pv539141], .p pv2 [pv2,pv3,pv5,pv109,pv1319], .c 3, .c 5, .c 1949, .c 3, .c 7,
  .c 47, .c 3, .p pv2 [pv2,pv269,pv8017], .p pv17 [pv2,pv3,pv7,pv51347], .c 3, .c 13, .c 5, .c 3,
  .c 41, .p pv11 [pv2,pv3,pv5,pv11981], .c 3, .c 5, .c 23, .c 3, .c 19,
  .p pv5 [pv2,pv3,pv17,pv21143], .c 3, .c 11,
]
private theorem h0527c08 : checkBlock 4312923 128 b0527c08 = true := by
  decide +kernel

private def b0527c09 : List Row := [
  .c 13, .c 3, .c 7, .c 5, .c 3, .c 17, .p pv47 [pv2,pv3,pv5,pv7,pv19,pv23,pv47], .c 3, .c 5,
  .c 7, .c 3, .c 37, .c 283, .c 3, .c 89, .c 19, .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv13,pv1823], .c 11, .c 3, .c 5, .c 227, .c 3, .c 13, .c 239, .c 3, .c 47, .c 7,
  .c 3, .c 11, .c 5, .c 3, .c 61, .p pv2 [pv2,pv3,pv5,pv71], .c 3, .c 5, .c 13, .c 3, .c 83,
  .c 337, .c 3, .c 7, .p pv17 [pv2,pv3,pv119813], .c 3, .p pv3 [pv2,pv539159], .c 5, .c 3,
  .c 1789, .c 7, .c 3, .c 5, .c 11, .c 3, .c 17, .p pv2 [pv2,pv3,pv359441], .c 3,
  .p pv3 [pv2,pv13,pv89,pv233], .c 53, .c 3, .p pv5 [pv2,pv7,pv308093], .c 5, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv5,pv61,pv2357], .c 3, .c 5, .p pv19 [pv2,pv3,pv7,pv51349], .c 3, .c 71, .c 7,
  .c 3, .p pv5 [pv2,pv67,pv32189], .p pv7 [pv2,pv3,pv23,pv3907], .c 3, .p pv2 [pv2,pv1078333],
  .c 5, .c 3, .p pv2 [pv2,pv2156669], .p pv11 [pv2,pv3,pv5,pv31,pv773], .c 3, .c 5, .c 929, .c 3,
  .c 7, .c 11, .c 3, .c 193, .c 17, .c 3, .c 179, .c 5, .c 3, .c 1901, .c 31, .c 3, .c 5, .c 601,
  .c 3, .p pv2 [pv2,pv5,pv19,pv11351], .p pv5 [pv2,pv3,pv718897], .c 3, .c 13,
  .p pv7 [pv2,pv3,pv359449], .c 3, .c 7, .c 5, .c 3, .c 19, .c 149, .c 3, .c 5, .c 7, .c 3,
  .c 181, .c 13, .c 3, .p pv3 [pv2,pv43,pv12539], .c 11, .c 3, .c 37, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv127,pv1213], .c 29, .c 3,
]
private theorem h0527c09 : checkBlock 4313179 128 b0527c09 = true := by
  decide +kernel

private def b0527c10 : List Row := [
  .c 5, .c 19, .c 3, .c 11, .c 23, .c 3, .c 617, .c 7, .c 3, .c 313, .c 5, .c 3, .c 43, .c 17,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv23,pv151], .c 3, .p pv7 [pv2,pv5,pv7,pv8803], .c 211, .c 3, .c 7,
  .c 79, .c 3, .p pv2 [pv2,pv593,pv3637], .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 37, .c 3,
  .p pv2 [pv2,pv5,pv8627], .p pv3 [pv2,pv3,pv43,pv5573], .c 3, .c 11,
  .p pv11 [pv2,pv3,pv101,pv3559], .c 3, .c 19, .c 5, .c 3, .c 7, .c 1223, .c 3, .c 5, .c 67, .c 3,
  .p pv2 [pv2,pv5,pv13,pv33181], .c 7, .c 3, .c 103, .p pv2 [pv2,pv3,pv239641], .c 3, .c 13, .c 5,
  .c 3, .c 59, .c 11, .c 3, .c 5, .c 31, .c 3, .c 7, .c 17, .c 3, .c 1163, .c 13, .c 3, .c 11,
  .c 5, .c 3, .p pv2 [pv2,pv2156789], .c 23, .c 3, .c 5, .c 139, .c 3,
  .p pv17 [pv2,pv5,pv97,pv4447], .c 83, .c 3, .c 17, .p pv3 [pv2,pv3,pv107,pv6719], .c 3, .c 7,
  .c 5, .c 3, .c 101, .p pv89 [pv2,pv3,pv5,pv7,pv41,pv167], .c 3, .c 5, .c 7, .c 3, .c 13, .c 457,
  .c 3, .c 19, .p pv2 [pv2,pv3,pv11,pv3631], .c 3, .c 1489, .c 5, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv5,pv103,pv349], .c 3, .c 5, .c 13, .c 3, .c 41,
  .p pv17 [pv2,pv3,pv7,pv89,pv577], .c 3, .c 307, .c 7, .c 3, .c 29, .c 5, .c 3,
  .p pv2 [pv2,pv1078417], .p pv3 [pv2,pv3,pv5,pv53,pv2713], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv61,pv71,pv83], .c 3, .c 31, .c 11, .c 3, .c 7, .p pv11 [pv2,pv3,pv179737],
]
private theorem h0527c10 : checkBlock 4313435 128 b0527c10 = true := by
  decide +kernel

private def b0527c11 : List Row := [
  .c 3, .p pv2 [pv2,pv29,pv41,pv907], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 47, .c 3, .c 239,
  .p pv11 [pv2,pv3,pv13,pv31,pv223], .c 3, .c 43, .c 23, .c 3, .c 53, .c 5, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv5,pv143791], .c 3, .c 5, .c 61, .c 3, .c 19, .c 7, .c 3, .c 71, .c 11, .c 3,
  .c 1559, .c 5, .c 3, .c 83, .c 1699, .c 3, .c 5, .c 17, .c 3, .c 7, .c 181, .c 3, .c 13, .c 19,
  .c 3, .p pv5 [pv2,pv11,pv196081], .c 5, .c 3, .c 73, .p pv17 [pv2,pv3,pv5,pv13,pv1229], .c 3,
  .c 5, .p pv2 [pv2,pv3,pv359483], .c 3, .c 17, .c 13, .c 3, .p pv5 [pv2,pv7,pv308129], .c 127,
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv17,pv71,pv1787], .c 1427, .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv37,pv89,pv131], .c 1103, .c 3, .c 11, .c 293, .c 3,
  .p pv7 [pv2,pv13,pv83,pv1999], .c 5, .c 3, .p pv13 [pv2,pv7,pv11,pv47,pv149],
  .p pv2 [pv2,pv3,pv5,pv28759], .c 3, .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv215693], .c 587, .c 3,
  .c 31, .c 7, .c 3, .p pv3 [pv2,pv269617], .c 5, .c 3, .c 431, .c 11, .c 3, .c 5, .c 643, .c 3,
  .p pv2 [pv2,pv5,pv7,pv61627], .c 19, .c 3, .c 7, .p pv2 [pv2,pv3,pv31,pv859], .c 3, .c 11, .c 5,
  .c 3, .c 1129, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv119831], .c 3,
  .p pv3 [pv2,pv5,pv13,pv17,pv61], .c 331, .c 3, .p pv5 [pv2,pv23,pv191,pv491], .c 31, .c 3,
  .c 13, .c 5, .c 3, .c 7, .c 37, .c 3, .c 5,
]
private theorem h0527c11 : checkBlock 4313691 128 b0527c11 = true := by
  decide +kernel

private def b0527c12 : List Row := [
  .c 11, .c 3, .c 1567, .c 7, .c 3, .c 1453, .c 13, .c 3, .c 877, .c 5, .c 3, .c 11, .c 17, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv179749], .c 3, .c 7, .p pv7 [pv2,pv3,pv29,pv24793], .c 3, .c 421, .c 47,
  .c 3, .c 137, .c 5, .c 3, .p pv7 [pv2,pv13,pv277,pv599], .c 113, .c 3, .c 5, .c 19, .c 3, .c 13,
  .c 11, .c 3, .p pv3 [pv2,pv7,pv19259], .c 997, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv1078507],
  .c 71, .c 3, .c 5, .c 7, .c 3, .c 23, .p pv3 [pv2,pv3,pv61,pv3929], .c 3, .c 1483, .c 271, .c 3,
  .c 31, .c 5, .c 3, .p pv2 [pv2,pv7,pv44021], .c 41, .c 3, .c 5, .c 1279, .c 3, .c 1093, .c 17,
  .c 3, .c 1327, .c 7, .c 3, .c 19, .c 5, .c 3, .c 13, .c 83, .c 3, .c 5, .c 89, .c 3, .c 11,
  .c 61, .c 3, .c 7, .c 761, .c 3, .c 773, .c 5, .c 3, .p pv17 [pv2,pv373,pv5783], .c 7, .c 3,
  .c 5, .c 29, .c 3, .c 229, .c 23, .c 3, .c 863, .c 59, .c 3, .c 41, .c 5, .c 3, .c 7, .c 1429,
  .c 3, .c 5, .c 379, .c 3, .c 797, .c 7, .c 3, .c 11, .p pv7 [pv2,pv3,pv19973], .c 3, .c 71,
  .c 5, .c 3, .c 23, .p pv2 [pv2,pv3,pv5,pv13,pv5531], .c 3, .c 5, .p pv2 [pv2,pv3,pv89,pv2693],
  .c 3, .c 7, .c 13, .c 3, .c 19, .c 397, .c 3,
]
private theorem h0527c12 : checkBlock 4313947 128 b0527c12 = true := by
  decide +kernel

private def b0527c13 : List Row := [
  .c 157, .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .p pv7 [pv2,pv3,pv19,pv9461], .c 3, .c 151,
  .c 131, .c 3, .c 73, .c 577, .c 3, .c 7, .c 5, .c 3, .c 31, .p pv29 [pv2,pv3,pv5,pv7,pv107],
  .c 3, .c 5, .c 7, .c 3, .c 347, .c 53, .c 3, .c 59, .c 257, .c 3, .c 1459, .c 5, .c 3, .c 79,
  .c 13, .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv107857], .c 1289, .c 3,
  .p pv5 [pv2,pv61,pv35363], .c 7, .c 3, .p pv2 [pv2,pv19,pv56767], .c 5, .c 3, .c 11, .c 29,
  .c 3, .c 5, .c 41, .c 3, .c 17, .p pv5 [pv2,pv3,pv59921], .c 3, .c 7, .c 43, .c 3, .c 13, .c 5,
  .c 3, .c 109, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv3457], .c 3,
  .p pv2 [pv2,pv5,pv23,pv83,pv113], .c 11, .c 3, .c 61, .c 13, .c 3, .c 479, .c 5, .c 3, .c 7,
  .c 103, .c 3, .c 5, .c 1013, .c 3, .c 653, .c 7, .c 3, .c 443, .c 17, .c 3,
  .p pv5 [pv2,pv241,pv8951], .c 5, .c 3, .c 41, .p pv11 [pv2,pv3,pv5,pv143813], .c 3, .c 5,
  .c 809, .c 3, .c 7, .p pv2 [pv2,pv3,pv239689], .c 3, .c 1307, .c 11, .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv2157209], .c 139, .c 3, .c 5, .c 13, .c 3, .c 11, .p pv13 [pv2,pv3,pv23,pv977],
  .c 3, .c 179, .c 251, .c 3, .c 7, .c 5, .c 3, .c 1319, .p pv7 [pv2,pv3,pv5,pv7,pv587], .c 3,
  .c 5, .c 7,
]
private theorem h0527c13 : checkBlock 4314203 128 b0527c13 = true := by
  decide +kernel

private def b0527c14 : List Row := [
  .c 3, .c 233, .c 19, .c 3, .p pv2 [pv2,pv13,pv165941], .c 61, .c 3, .c 659, .c 5, .c 3, .c 13,
  .c 17, .c 3, .c 5, .c 31, .c 3, .c 43, .c 59, .c 3, .c 11, .c 7, .c 3, .c 311, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv98057], .c 683, .c 3, .c 5, .c 157, .c 3, .c 677, .c 151, .c 3, .c 7,
  .p pv23 [pv2,pv3,pv71,pv211], .c 3, .c 29, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 23, .c 3,
  .p pv29 [pv2,pv5,pv86291], .c 41, .c 3, .c 13, .p pv3 [pv2,pv3,pv19,pv37847], .c 3, .c 11, .c 5,
  .c 3, .c 7, .c 53, .c 3, .c 5, .c 19, .c 3, .p pv3 [pv2,pv5,pv31,pv6959], .c 7, .c 3,
  .p pv2 [pv2,pv2157293], .c 83, .c 3, .c 23, .c 5, .c 3, .c 67, .c 743, .c 3, .c 5, .c 11, .c 3,
  .c 7, .c 467, .c 3, .c 17, .c 101, .c 3, .c 241, .c 5, .c 3, .c 11, .c 89, .c 3, .c 5, .c 1867,
  .c 3, .c 1213, .p pv3 [pv2,pv3,pv31,pv23197], .c 3, .c 47, .c 29, .c 3, .c 7, .c 5, .c 3,
  .c 1523, .c 13, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv59,pv71,pv103], .c 11, .c 3, .c 53,
  .c 113, .c 3, .p pv2 [pv2,pv2157341], .c 5, .c 3, .p pv3 [pv2,pv7,pv9631], .c 19, .c 3, .c 5,
  .c 463, .c 3, .p pv2 [pv2,pv5,pv13,pv3319], .p pv3 [pv2,pv3,pv7,pv17,pv6043], .c 3, .c 29, .c 7,
  .c 3, .c 13,
]
private theorem h0527c14 : checkBlock 4314459 128 b0527c14 = true := by
  decide +kernel

private def b0527c15 : List Row := [
  .c 5, .c 3, .c 17, .p pv29 [pv2,pv3,pv5,pv89,pv101], .c 3, .c 5, .c 569, .c 3, .c 23, .c 67,
  .c 3, .c 7, .c 11, .c 3, .c 79, .c 5, .c 3, .c 43, .c 7, .c 3, .c 5, .c 859, .c 3, .c 11,
  .c 1433, .c 3, .c 19, .p pv11 [pv2,pv3,pv89891], .c 3, .c 103, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv23971], .c 3, .c 5, .c 17, .c 3, .c 13, .c 7, .c 3, .c 31, .c 41, .c 3,
  .p pv2 [pv2,pv2157401], .c 5, .c 3, .c 89, .c 73, .c 3, .c 5, .c 13, .c 3, .c 7, .c 23, .c 3,
  .c 11, .c 37, .c 3, .p pv3 [pv2,pv479,pv563], .c 5, .c 3, .p pv7 [pv2,pv11,pv17,pv83,pv139],
  .c 1033, .c 3, .c 5, .c 59, .c 3, .c 97, .c 499, .c 3, .p pv3 [pv2,pv7,pv13,pv5927], .c 31,
  .c 3, .c 7, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 7, .c 3, .c 19, .c 71, .c 3,
  .p pv5 [pv2,pv773,pv2791], .c 17, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv7,pv89,pv3463], .c 79,
  .c 3, .c 5, .c 613, .c 3, .p pv37 [pv2,pv5,pv29,pv14879], .p pv5 [pv2,pv3,pv7,pv6421], .c 3,
  .c 199, .c 7, .c 3, .c 17, .c 5, .c 3, .c 47, .c 439, .c 3, .c 5, .c 11, .c 3, .c 251,
  .p pv19 [pv2,pv3,pv53,pv4523], .c 3, .c 7, .p pv13 [pv2,pv3,pv11,pv97,pv337], .c 3,
  .p pv3 [pv2,pv31,pv127,pv137], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 1039, .c 3,
]
private theorem h0527c15 : checkBlock 4314715 128 b0527c15 = true := by
  decide +kernel

private def b0527c16 : List Row := [
  .c 1117, .c 13, .c 3, .c 37, .c 103, .c 3, .c 31, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 29,
  .c 3, .c 67, .c 7, .c 3, .c 23, .c 131, .c 3, .p pv2 [pv2,pv13,pv82981], .c 5, .c 3, .c 1229,
  .c 739, .c 3, .c 5, .p pv3 [pv2,pv3,pv29,pv24799], .c 3, .c 7, .c 19, .c 3, .c 587,
  .p pv3 [pv2,pv3,pv7,pv13,pv1129], .c 3, .c 227, .c 5, .c 3, .c 619, .c 13, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv89897], .c 3, .p pv2 [pv2,pv5,pv215753], .p pv3 [pv2,pv3,pv719177], .c 3,
  .p pv2 [pv2,pv7,pv308219], .c 11, .c 3, .c 7, .c 5, .c 3, .c 61, .c 1193, .c 3, .c 5, .c 7,
  .c 3, .c 11, .c 17, .c 3, .p pv3 [pv2,pv71,pv107], .c 23, .c 3, .c 13, .c 5, .c 3, .c 19,
  .p pv11 [pv2,pv3,pv5,pv17,pv8461], .c 3, .c 5, .c 47, .c 3, .c 787,
  .p pv2 [pv2,pv3,pv7,pv23,pv1489], .c 3, .c 17, .c 7, .c 3, .c 271, .c 5, .c 3, .c 173,
  .p pv7 [pv2,pv3,pv5,pv61,pv131], .c 3, .c 5, .c 19, .c 3, .p pv7 [pv2,pv5,pv7,pv12329], .c 179,
  .c 3, .c 7, .p pv7 [pv2,pv3,pv239731], .c 3, .c 607, .c 5, .c 3, .c 31, .c 7, .c 3, .c 5,
  .c 389, .c 3, .c 13, .p pv3 [pv2,pv3,pv719197], .c 3, .p pv2 [pv2,pv367,pv5879], .c 149, .c 3,
  .c 1201, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 13, .c 3, .c 47, .c 7, .c 3, .c 79,
  .p pv2 [pv2,pv3,pv719203], .c 3, .c 11, .c 5,
]
private theorem h0527c16 : checkBlock 4314971 128 b0527c16 = true := by
  decide +kernel

private def b0527c17 : List Row := [
  .c 3, .c 17, .c 31, .c 3, .c 5, .c 23, .c 3, .c 7, .p pv2 [pv2,pv3,pv19,pv37853], .c 3, .c 331,
  .c 73, .c 3, .c 83, .c 5, .c 3, .c 13, .c 19, .c 3, .c 5, .c 11, .c 3, .c 131, .c 37, .c 3,
  .p pv2 [pv2,pv7,pv229,pv673], .p pv3 [pv2,pv3,pv11,pv151,pv433], .c 3, .c 7, .c 5, .c 3, .c 11,
  .c 41, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv11,pv3923], .p pv3 [pv2,pv3,pv157,pv509], .c 3,
  .c 487, .c 71, .c 3, .c 53, .c 5, .c 3, .c 59, .c 317, .c 3, .c 5, .c 853, .c 3, .c 17, .c 11,
  .c 3, .c 13, .c 7, .c 3, .c 89, .c 5, .c 3, .p pv2 [pv2,pv17,pv3733], .c 43, .c 3, .c 5, .c 113,
  .c 3, .p pv3 [pv2,pv5,pv7,pv3853], .c 13, .c 3, .c 7, .p pv13 [pv2,pv3,pv179807], .c 3, .c 41,
  .c 5, .c 3, .p pv2 [pv2,pv59,pv36571], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv31,pv23201], .c 3,
  .c 103, .c 233, .c 3, .p pv2 [pv2,pv1078849], .c 11, .c 3, .c 29, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv11,pv1453], .c 3, .c 5, .c 31, .c 3, .c 11, .c 7, .c 3, .c 101, .c 151,
  .c 3, .c 17, .c 5, .c 3, .p pv7 [pv2,pv719,pv3001], .c 13, .c 3, .c 5, .c 167, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv359621], .c 3, .c 1693, .c 157, .c 3, .p pv5 [pv2,pv2157731], .c 5, .c 3,
  .p pv2 [pv2,pv73,pv14779], .c 1697, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv32693], .c 3,
  .p pv17 [pv2,pv5,pv13,pv43,pv193],
]
private theorem h0527c17 : checkBlock 4315227 128 b0527c17 = true := by
  decide +kernel

private def b0527c18 : List Row := [
  .c 2027, .c 3, .c 11, .c 19, .c 3, .c 7, .c 5, .c 3, .c 307, .c 17, .c 3, .c 5, .c 7, .c 3,
  .c 179, .c 23, .c 3, .c 1997, .c 13, .c 3, .c 43, .c 5, .c 3, .p pv17 [pv2,pv7,pv101,pv109],
  .c 11, .c 3, .c 5, .c 41, .c 3, .c 31, .p pv3 [pv2,pv3,pv7,pv11,pv9341], .c 3, .c 467, .c 7,
  .c 3, .c 11, .c 5, .c 3, .c 23, .c 1439, .c 3, .c 5, .c 61, .c 3, .c 13,
  .p pv5 [pv2,pv3,pv31,pv1289], .c 3, .c 7, .p pv3 [pv2,pv3,pv41,pv53,pv331], .c 3, .c 113, .c 5,
  .c 3, .p pv2 [pv2,pv163,pv6619], .c 7, .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv10789], .c 17,
  .c 3, .p pv5 [pv2,pv29,pv37,pv2011], .c 43, .c 3, .c 1811, .c 5, .c 3, .c 7, .c 1499, .c 3,
  .c 5, .c 97, .c 3, .c 53, .c 7, .c 3, .c 17, .c 347, .c 3, .c 37, .c 5, .c 3, .c 13, .c 23,
  .c 3, .c 5, .c 757, .c 3, .c 7, .c 11, .c 3, .c 1831, .c 661, .c 3, .c 59, .c 5, .c 3, .c 19,
  .c 47, .c 3, .c 5, .c 73, .c 3, .c 79, .c 29, .c 3, .c 23, .c 89, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv1078927], .c 433, .c 3, .c 5, .c 7, .c 3, .c 967,
  .p pv3 [pv2,pv3,pv17,pv29,pv1459], .c 3, .c 13, .c 11, .c 3, .p pv2 [pv2,pv59,pv18287], .c 5,
  .c 3,
]
private theorem h0527c18 : checkBlock 4315483 128 b0527c18 = true := by
  decide +kernel

private def b0527c19 : List Row := [
  .c 17, .p pv23 [pv2,pv3,pv5,pv11,pv13,pv503], .c 3, .c 5, .c 311, .c 3, .c 11, .c 13, .c 3,
  .p pv2 [pv2,pv17,pv63467], .c 7, .c 3, .p pv2 [pv2,pv11,pv196171], .c 5, .c 3,
  .p pv3 [pv2,pv409,pv1319], .c 1543, .c 3, .c 5, .p pv13 [pv2,pv3,pv11239], .c 3, .c 43, .c 41,
  .c 3, .c 7, .c 23, .c 3, .c 19, .c 5, .c 3, .p pv11 [pv2,pv2157899], .c 7, .c 3, .c 5, .c 17,
  .c 3, .c 61, .c 1291, .c 3, .c 11, .p pv3 [pv2,pv3,pv13,pv55331], .c 3,
  .p pv7 [pv2,pv7,pv47,pv937], .c 5, .c 3, .c 7, .c 13, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv191,pv269], .c 3, .c 17, .c 7, .c 3, .p pv5 [pv2,pv2157923], .c 79, .c 3,
  .c 641, .c 5, .c 3, .c 233, .c 11, .c 3, .c 5, .c 29, .c 3, .c 7,
  .p pv23 [pv2,pv3,pv11,pv61,pv67], .c 3, .c 71, .c 281, .c 3, .c 11, .c 5, .c 3, .c 1531,
  .p pv13 [pv2,pv3,pv5,pv293,pv491], .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv29,pv53], .c 3,
  .p pv3 [pv2,pv5,pv43159], .p pv3 [pv2,pv3,pv37,pv19441], .c 3, .c 19, .c 13, .c 3, .c 7, .c 5,
  .c 3, .p pv11 [pv2,pv97,pv22247], .p pv19 [pv2,pv3,pv5,pv7,pv367], .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv157,pv2749], .c 61, .c 3, .c 277, .c 37, .c 3, .c 17, .c 5, .c 3, .c 11,
  .c 227, .c 3, .c 5, .c 313, .c 3, .c 13, .c 47, .c 3, .c 1223, .c 7, .c 3, .c 23, .c 5, .c 3,
  .c 73, .p pv7 [pv2,pv3,pv5,pv71933], .c 3, .c 5, .c 13, .c 3, .p pv7 [pv2,pv5,pv7,pv61657],
  .c 11,
]
private theorem h0527c19 : checkBlock 4315739 128 b0527c19 = true := by
  decide +kernel

private def b0527c20 : List Row := [
  .c 3, .c 7, .p pv3 [pv2,pv3,pv719333], .c 3, .p pv2 [pv2,pv19,pv53,pv2143], .c 5, .c 3, .c 103,
  .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv89917], .c 3, .c 19, .p pv3 [pv2,pv3,pv239779], .c 3, .c 59,
  .c 41, .c 3, .c 101, .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .p pv7 [pv2,pv3,pv7,pv102763], .c 3,
  .p pv2 [pv2,pv5,pv37,pv2333], .c 7, .c 3, .c 47, .c 11, .c 3, .c 1879, .c 5, .c 3, .c 241,
  .p pv3 [pv2,pv3,pv5,pv11,pv29,pv41], .c 3, .c 5, .c 163, .c 3, .c 7, .c 83, .c 3, .c 37, .c 139,
  .c 3, .c 263, .c 5, .c 3, .c 29, .c 239, .c 3, .c 5, .p pv2 [pv2,pv3,pv719351], .c 3, .c 23,
  .c 17, .c 3, .c 13, .c 419, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv29,pv4651], .c 353, .c 3,
  .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv67,pv3221], .c 13, .c 3, .c 11, .c 443, .c 3,
  .p pv3 [pv2,pv41,pv13159], .c 5, .c 3, .p pv7 [pv2,pv7,pv11,pv28027], .c 31, .c 3, .c 5,
  .c 1129, .c 3, .p pv2 [pv2,pv5,pv431617], .c 19, .c 3, .c 61, .c 7, .c 3, .c 293, .c 5, .c 3,
  .c 571, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv251,pv1433], .c 3, .p pv3 [pv2,pv5,pv7,pv3083],
  .c 23, .c 3, .c 7, .c 97, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv191,pv11299], .c 7, .c 3, .c 5,
  .c 179, .c 3, .p pv19 [pv2,pv5,pv19,pv22717], .c 89, .c 3, .c 449, .p pv3 [pv2,pv3,pv61,pv3931],
  .c 3, .c 503, .c 5, .c 3, .c 7,
]
private theorem h0527c20 : checkBlock 4315995 128 b0527c20 = true := by
  decide +kernel

private def b0527c21 : List Row := [
  .p pv3 [pv2,pv3,pv5,pv1151], .c 3, .c 5, .c 11, .c 3, .c 113, .c 7, .c 3, .c 53, .c 479, .c 3,
  .c 13, .c 5, .c 3, .c 11, .c 487, .c 3, .c 5, .c 19, .c 3, .c 7, .p pv2 [pv2,pv3,pv47,pv2551],
  .c 3, .c 43, .c 13, .c 3, .c 71, .c 5, .c 3, .c 37, .p pv3 [pv2,pv3,pv5,pv199,pv241], .c 3,
  .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv53,pv509], .c 11, .c 3, .p pv5 [pv2,pv7,pv308309],
  .p pv11 [pv2,pv3,pv6661], .c 3, .c 7, .c 5, .c 3, .c 47, .c 23, .c 3, .c 5, .c 7, .c 3, .c 13,
  .c 983, .c 3, .c 41, .p pv3 [pv2,pv3,pv719393], .c 3, .c 19, .c 5, .c 3, .c 311,
  .p pv3 [pv2,pv3,pv5,pv143879], .c 3, .c 5, .c 13, .c 3, .c 59, .c 37, .c 3, .c 23, .c 7, .c 3,
  .c 1013, .c 5, .c 3, .p pv17 [pv2,pv41,pv52639], .c 19, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv179,pv4019], .c 3, .c 11, .c 907, .c 3, .c 7, .c 17, .c 3,
  .p pv5 [pv2,pv11,pv196201], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 101, .c 3, .c 281,
  .p pv5 [pv2,pv3,pv13,pv55339], .c 3, .c 29, .c 167, .c 3, .c 17, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv71941], .c 3, .c 5, .c 197, .c 3, .c 31, .c 7, .c 3, .c 11, .c 23, .c 3,
  .p pv2 [pv2,pv61,pv35381], .c 5, .c 3, .p pv3 [pv2,pv11,pv181,pv271], .c 277, .c 3, .c 5,
  .p pv17 [pv2,pv3,pv19,pv4733], .c 3, .c 7, .p pv11 [pv2,pv3,pv23,pv31,pv1009], .c 3,
]
private theorem h0527c21 : checkBlock 4316251 128 b0527c21 = true := by
  decide +kernel

private def b0527c22 : List Row := [
  .c 13, .c 109, .c 3, .c 421, .c 5, .c 3, .p pv7 [pv2,pv2158259], .c 11, .c 3, .c 5, .c 47, .c 3,
  .c 37, .c 13, .c 3, .c 577, .p pv2 [pv2,pv3,pv17,pv101,pv419], .c 3, .c 7, .c 5, .c 3, .c 463,
  .c 241, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv79,pv683], .c 29, .c 3,
  .p pv5 [pv2,pv163,pv13241], .p pv7 [pv2,pv3,pv37,pv4861], .c 3,
  .p pv2 [pv2,pv13,pv17,pv19,pv257], .c 5, .c 3, .c 239, .c 83, .c 3, .c 5, .c 11, .c 3, .c 19,
  .p pv13 [pv2,pv3,pv7,pv29,pv443], .c 3, .c 97, .c 7, .c 3, .c 41, .c 5, .c 3, .c 11, .c 13,
  .c 3, .c 5, .c 23, .c 3, .c 29, .c 17, .c 3, .c 7, .c 19, .c 3, .c 337, .c 5, .c 3, .c 79, .c 7,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv719441], .c 3, .p pv11 [pv2,pv5,pv13,pv29,pv229], .c 11, .c 3,
  .c 17, .p pv2 [pv2,pv3,pv71,pv10133], .c 3, .c 13, .c 5, .c 3, .c 7, .c 631, .c 3, .c 5, .c 691,
  .c 3, .p pv3 [pv2,pv5,pv311,pv347], .c 7, .c 3, .c 439, .c 13, .c 3, .p pv2 [pv2,pv1079173],
  .c 5, .c 3, .c 1217, .c 107, .c 3, .c 5, .p pv3 [pv2,pv3,pv79939], .c 3, .c 7, .c 113, .c 3,
  .p pv2 [pv2,pv37,pv29167], .c 11, .c 3, .c 1621, .c 5, .c 3, .c 71, .c 1327, .c 3, .c 5, .c 29,
  .c 3, .c 11, .c 19, .c 3, .c 83, .p pv2 [pv2,pv3,pv479,pv751], .c 3, .c 7, .c 5, .c 3, .c 17,
  .c 1487,
]
private theorem h0527c22 : checkBlock 4316507 128 b0527c22 = true := by
  decide +kernel

private def b0527c23 : List Row := [
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv43,pv10039], .p pv2 [pv2,pv3,pv359731], .c 3,
  .p pv5 [pv2,pv17,pv31741], .p pv2 [pv2,pv3,pv23,pv10427], .c 3, .c 167, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv151,pv1021], .c 97, .c 3, .c 5, .c 53, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv7,pv14683], .c 3, .c 11, .c 7, .c 3, .c 43, .c 5, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv5,pv71947], .c 3, .c 5, .c 17, .c 3, .c 193, .c 103, .c 3, .c 7, .c 1303,
  .c 3, .c 31, .c 5, .c 3, .c 41, .c 7, .c 3, .c 5, .c 19, .c 3, .c 17, .c 1453, .c 3,
  .p pv2 [pv2,pv2158433], .c 173, .c 3, .c 11, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv17987],
  .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv34261], .c 3, .p pv2 [pv2,pv5,pv41,pv10529], .c 7, .c 3,
  .c 13, .c 43, .c 3, .c 47, .c 5, .c 3, .c 61, .c 29, .c 3, .c 5, .c 11, .c 3, .c 7, .c 13, .c 3,
  .c 1511, .c 17, .c 3, .c 19, .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv29,pv827], .c 3, .c 5,
  .c 1609, .c 3, .p pv7 [pv2,pv5,pv11,pv47,pv167], .c 811, .c 3, .c 419,
  .p pv19 [pv2,pv3,pv239831], .c 3, .c 7, .c 5, .c 3, .c 29, .c 19, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv17,pv12697], .c 11, .c 3, .c 883, .p pv11 [pv2,pv3,pv13,pv27673], .c 3,
  .c 599, .c 5, .c 3, .p pv11 [pv2,pv7,pv29,pv31], .c 13, .c 3, .c 5, .c 137, .c 3, .c 67, .c 41,
  .c 3, .p pv3 [pv2,pv11,pv49057],
]
private theorem h0527c23 : checkBlock 4316763 128 b0527c23 = true := by
  decide +kernel

private def b0527c24 : List Row := [
  .c 7, .c 3, .p pv5 [pv2,pv107,pv20173], .c 5, .c 3, .c 31, .c 17, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv359753], .c 3, .p pv17 [pv2,pv5,pv7,pv13,pv593], .c 101, .c 3, .c 7, .c 11,
  .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv197,pv10957], .c 7, .c 3, .c 5, .c 1213, .c 3, .c 11,
  .p pv5 [pv2,pv3,pv89939], .c 3, .c 23, .c 13, .c 3, .p pv2 [pv2,pv7,pv11,pv17,pv97], .c 5, .c 3,
  .c 7, .c 31, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv3671], .c 3, .c 709, .c 7, .c 3,
  .p pv2 [pv2,pv199,pv10847], .c 659, .c 3, .c 79, .c 5, .c 3, .c 1187,
  .p pv37 [pv2,pv3,pv5,pv1499], .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv149,pv439], .c 3, .c 7, .c 17,
  .c 3, .c 11, .p pv2 [pv2,pv3,pv7,pv47], .c 3, .c 29, .c 5, .c 3, .c 617,
  .p pv3 [pv2,pv3,pv5,pv17,pv1693], .c 3, .c 5, .c 13, .c 3, .c 19, .c 109, .c 3, .c 17, .c 23,
  .c 3, .c 7, .c 5, .c 3, .c 97, .c 11, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv353,pv1223],
  .p pv5 [pv2,pv3,pv11,pv23,pv79], .c 3, .c 37, .c 19, .c 3, .c 11, .c 5, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv5,pv47969], .c 3, .c 5, .c 193, .c 3, .c 53, .c 317, .c 3, .c 479, .c 7, .c 3,
  .c 331, .c 5, .c 3, .p pv11 [pv2,pv23,pv127,pv739], .c 151, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv7,pv2467], .p pv2 [pv2,pv3,pv17,pv21163], .c 3, .c 7, .c 29, .c 3,
  .p pv5 [pv2,pv2158631], .c 5, .c 3, .c 11, .c 7, .c 3,
]
private theorem h0527c24 : checkBlock 4317019 128 b0527c24 = true := by
  decide +kernel

private def b0527c25 : List Row := [
  .c 5, .c 31, .c 3, .c 137, .p pv2 [pv2,pv3,pv239849], .c 3, .c 13,
  .p pv17 [pv2,pv3,pv29,pv6203], .c 3, .c 73, .c 5, .c 3, .c 7, .c 89, .c 3, .c 5, .c 23, .c 3,
  .p pv11 [pv2,pv5,pv431731], .c 7, .c 3, .c 29, .p pv3 [pv2,pv3,pv239851], .c 3,
  .p pv2 [pv2,pv277,pv7793], .c 5, .c 3, .c 43, .c 571, .c 3, .c 5, .c 17, .c 3, .c 7, .c 107,
  .c 3, .p pv2 [pv2,pv11,pv29,pv67,pv101], .c 797, .c 3, .c 23, .c 5, .c 3, .c 613,
  .p pv17 [pv2,pv3,pv5,pv17989], .c 3, .c 5, .c 131, .c 3, .c 17, .c 47, .c 3,
  .p pv3 [pv2,pv7,pv23,pv419], .c 11, .c 3, .c 7, .c 5, .c 3, .c 19, .c 13, .c 3, .c 5, .c 7,
  .c 3, .c 11, .p pv3 [pv2,pv3,pv719567], .c 3, .p pv5 [pv2,pv1013,pv2131],
  .p pv7 [pv2,pv3,pv19,pv263], .c 3, .c 67, .c 5, .c 3, .c 37, .p pv2 [pv2,pv3,pv5,pv47,pv1531],
  .c 3, .c 5, .c 19, .c 3, .c 647, .c 29, .c 3, .p pv2 [pv2,pv1079359], .c 7, .c 3, .c 13, .c 5,
  .c 3, .p pv3 [pv2,pv283,pv1907], .c 103, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv13,pv17,pv37], .c 3,
  .p pv2 [pv2,pv5,pv7,pv30839], .c 31, .c 3, .c 7, .c 13, .c 3, .c 17, .c 5, .c 3, .c 89, .c 7,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv53,pv13577], .c 3, .c 23, .c 37, .c 3, .p pv3 [pv2,pv539687],
  .c 751, .c 3, .c 19, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv5711], .c 3,
  .c 13, .c 7, .c 3, .c 521, .p pv7 [pv2,pv3,pv179897],
]
private theorem h0527c25 : checkBlock 4317275 128 b0527c25 = true := by
  decide +kernel

private def b0527c26 : List Row := [
  .c 3, .c 11, .c 5, .c 3, .c 53, .c 17, .c 3, .c 5, .c 13, .c 3, .c 7, .p pv5 [pv2,pv3,pv29983],
  .c 3, .c 107, .c 383, .c 3, .c 1951, .c 5, .c 3, .p pv3 [pv2,pv89,pv379],
  .p pv11 [pv2,pv3,pv5,pv15991], .c 3, .c 5, .c 11, .c 3, .c 71, .c 23, .c 3, .c 31, .c 863, .c 3,
  .c 7, .c 5, .c 3, .c 11, .p pv11 [pv2,pv3,pv5,pv7,pv257], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv11,pv39251], .c 311, .c 3, .c 19, .c 127, .c 3, .p pv5 [pv2,pv2158811], .c 5,
  .c 3, .c 23, .p pv3 [pv2,pv3,pv5,pv43,pv3347], .c 3, .c 5, .p pv43 [pv2,pv3,pv19,pv29,pv653],
  .c 3, .c 37, .c 11, .c 3, .c 563, .c 7, .c 3, .c 727, .c 5, .c 3, .c 179,
  .p pv7 [pv2,pv3,pv5,pv17,pv83], .c 3, .c 5, .p pv2 [pv2,pv3,pv79,pv9109], .c 3, .c 263, .c 43,
  .c 3, .c 7, .c 59, .c 3, .p pv2 [pv2,pv2158841], .c 5, .c 3, .p pv3 [pv2,pv539711], .c 7, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv937], .c 3, .p pv2 [pv2,pv5,pv43177], .c 13, .c 3, .c 163, .c 11, .c 3,
  .c 1297, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .p pv23 [pv2,pv3,pv7,pv223,pv461], .c 3, .c 11,
  .c 7, .c 3, .p pv3 [pv2,pv457,pv1181], .p pv2 [pv2,pv3,pv59,pv12197], .c 3, .c 83, .c 5, .c 3,
  .c 47, .c 41, .c 3, .c 5, .c 139, .c 3, .c 7, .c 61, .c 3, .c 23, .c 19, .c 3, .c 31, .c 5,
  .c 3, .c 17, .c 13, .c 3, .c 5,
]
private theorem h0527c26 : checkBlock 4317531 128 b0527c26 = true := by
  decide +kernel

private def b0527c27 : List Row := [
  .c 991, .c 3, .p pv11 [pv2,pv5,pv23,pv18773], .c 1249, .c 3, .c 11, .p pv17 [pv2,pv3,pv719633],
  .c 3, .c 7, .c 5, .c 3, .c 1021, .p pv2 [pv2,pv3,pv5,pv7,pv29,pv709], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv13,pv16607], .p pv3 [pv2,pv3,pv239879], .c 3, .p pv2 [pv2,pv19,pv37,pv83],
  .c 137, .c 3, .c 13, .c 5, .c 3, .c 29, .c 11, .c 3, .c 5, .c 17, .c 3, .c 101,
  .p pv2 [pv2,pv3,pv7,pv11,pv4673], .c 3, .c 53, .c 7, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv29,pv37223], .c 149, .c 3, .c 5, .c 73, .c 3, .c 17, .c 19, .c 3, .c 7,
  .p pv29 [pv2,pv3,pv43,pv523], .c 3, .p pv2 [pv2,pv1079473], .c 5, .c 3,
  .p pv2 [pv2,pv13,pv17,pv9769], .c 7, .c 3, .c 5, .c 11, .c 3, .c 13, .p pv5 [pv2,pv3,pv59971],
  .c 3, .p pv2 [pv2,pv887,pv1217], .p pv3 [pv2,pv3,pv11,pv65423], .c 3, .p pv2 [pv2,pv7,pv308423],
  .c 5, .c 3, .c 7, .c 43, .c 3, .c 5, .c 13, .c 3, .c 293, .c 7, .c 3, .c 379, .c 17, .c 3,
  .c 251, .c 5, .c 3, .c 19, .p pv11 [pv2,pv3,pv5,pv35983], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv17,pv103,pv137], .c 3, .c 7, .c 11, .c 3, .c 739,
  .p pv2 [pv2,pv3,pv7,pv19,pv773], .c 3, .c 17, .c 5, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv5,pv31,pv4643], .c 3, .c 5, .c 19, .c 3, .c 1613, .c 2069, .c 3, .c 61,
  .c 1607, .c 3, .c 7, .c 5, .c 3, .c 1301, .c 31, .c 3, .c 5, .c 7, .c 3, .c 47, .c 59, .c 3,
  .c 971, .c 11, .c 3,
]
private theorem h0527c27 : checkBlock 4317787 128 b0527c27 = true := by
  decide +kernel

private def b0527c28 : List Row := [
  .c 23, .c 5, .c 3, .p pv3 [pv2,pv7,pv37,pv521], .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv19991],
  .c 3, .c 11, .p pv5 [pv2,pv3,pv7,pv102811], .c 3, .c 13, .c 7, .c 3, .c 19, .c 5, .c 3, .c 41,
  .p pv23 [pv2,pv3,pv5,pv13,pv173], .c 3, .c 5, .p pv13 [pv2,pv3,pv719681], .c 3,
  .p pv23 [pv2,pv5,pv7,pv61687], .c 13, .c 3, .c 7, .p pv2 [pv2,pv3,pv719683], .c 3, .c 43, .c 5,
  .c 3, .p pv2 [pv2,pv1079527], .c 7, .c 3, .c 5, .c 181, .c 3, .p pv3 [pv2,pv5,pv41,pv2633],
  .p pv3 [pv2,pv3,pv37,pv53,pv367], .c 3, .c 11, .c 29, .c 3, .p pv2 [pv2,pv7,pv13,pv11863], .c 5,
  .c 3, .c 7, .c 569, .c 3, .c 5, .c 151, .c 3, .c 59, .c 7, .c 3, .p pv2 [pv2,pv1079539], .c 37,
  .c 3, .p pv2 [pv2,pv2159081], .c 5, .c 3, .c 73, .c 11, .c 3, .c 5, .c 349, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv11,pv113,pv193], .c 3, .c 17, .c 43, .c 3, .c 11, .c 5, .c 3, .c 107,
  .p pv11 [pv2,pv3,pv5,pv2399], .c 3, .c 5, .c 31, .c 3, .p pv2 [pv2,pv5,pv13,pv59,pv563],
  .p pv5 [pv2,pv3,pv359851], .c 3, .c 67, .c 47, .c 3, .c 7, .c 5, .c 3, .c 487,
  .p pv3 [pv2,pv3,pv5,pv7,pv20563], .c 3, .c 5, .c 7, .c 3, .c 83, .c 41, .c 3,
  .p pv5 [pv2,pv97,pv22259], .c 13, .c 3, .c 109, .c 5, .c 3, .c 11, .c 829, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv47,pv15313], .c 3, .p pv11 [pv2,pv5,pv11,pv37,pv1061], .c 23, .c 3,
  .p pv2 [pv2,pv1079569], .c 7, .c 3, .p pv2 [pv2,pv19,pv5981], .c 5, .c 3, .c 17, .c 71, .c 3,
  .c 5, .c 283,
]
private theorem h0527c28 : checkBlock 4318043 128 b0527c28 = true := by
  decide +kernel

private def b0527c29 : List Row := [
  .c 3, .c 13, .c 11, .c 3, .c 7, .c 433, .c 3, .c 47, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 13,
  .c 3, .c 31, .c 839, .c 3, .p pv3 [pv2,pv11,pv3067], .c 19, .c 3, .c 97, .c 5, .c 3, .c 7,
  .c 67, .c 3, .c 5, .c 17, .c 3, .c 29, .c 7, .c 3, .c 1237, .c 11, .c 3, .c 61, .c 5, .c 3,
  .c 13, .c 37, .c 3, .c 5, .c 53, .c 3, .c 7, .c 31, .c 3, .c 2017, .p pv7 [pv2,pv3,pv7,pv34273],
  .c 3, .p pv2 [pv2,pv11,pv196291], .c 5, .c 3, .p pv11 [pv2,pv17,pv113,pv281], .c 23, .c 3, .c 5,
  .c 641, .c 3, .c 557, .c 857, .c 3, .c 659, .p pv2 [pv2,pv3,pv359869], .c 3, .c 7, .c 5, .c 3,
  .c 1439, .p pv43 [pv2,pv3,pv5,pv7,pv53,pv97], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv86369],
  .c 19, .c 3, .c 11, .c 17, .c 3, .p pv5 [pv2,pv2159231], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv11,pv2003], .c 109, .c 3, .c 5, .c 29, .c 3, .c 103, .c 13, .c 3,
  .p pv5 [pv2,pv31,pv69653], .c 7, .c 3, .c 17, .c 5, .c 3, .c 199, .c 11, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv29,pv8273], .c 3, .p pv7 [pv2,pv5,pv7,pv17,pv19,pv191],
  .p pv5 [pv2,pv3,pv11,pv8179], .c 3, .c 7, .c 709, .c 3, .c 11, .c 5, .c 3, .c 19, .c 7, .c 3,
  .c 5, .c 97, .c 3, .p pv3 [pv2,pv5,pv215927], .p pv3 [pv2,pv3,pv79973], .c 3, .c 89, .c 23,
  .c 3, .p pv3 [pv2,pv7,pv67,pv1151],
]
private theorem h0527c29 : checkBlock 4318299 128 b0527c29 = true := by
  decide +kernel

private def b0527c30 : List Row := [
  .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 11, .c 3, .c 41, .c 7, .c 3, .p pv3 [pv2,pv43,pv6277],
  .c 31, .c 3, .c 677, .c 5, .c 3, .c 11, .c 139, .c 3, .c 5, .p pv5 [pv2,pv3,pv1481], .c 3, .c 7,
  .c 37, .c 3, .c 73, .c 683, .c 3, .c 13, .c 5, .c 3, .c 43, .p pv7 [pv2,pv3,pv5,pv167,pv431],
  .c 3, .c 5, .c 107, .c 3, .c 409, .c 11, .c 3, .p pv2 [pv2,pv7,pv89,pv1733], .c 13, .c 3, .c 7,
  .c 5, .c 3, .p pv3 [pv2,pv461,pv1171], .c 29, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv181,pv1193], .c 17, .c 3, .p pv2 [pv2,pv11,pv196303],
  .p pv7 [pv2,pv3,pv119963], .c 3, .p pv3 [pv2,pv31,pv8707], .c 5, .c 3, .c 1571, .c 19, .c 3,
  .c 5, .c 23, .c 3, .c 13, .c 79, .c 3, .c 17, .c 7, .c 3, .c 31, .c 5, .c 3, .c 29, .c 229,
  .c 3, .c 5, .c 13, .c 3, .c 11, .c 263, .c 3, .c 7, .p pv11 [pv2,pv3,pv179947], .c 3, .c 23,
  .c 5, .c 3, .c 61, .c 7, .c 3, .c 5, .c 113, .c 3, .c 37, .c 67, .c 3, .c 19,
  .p pv3 [pv2,pv3,pv53,pv503], .c 3, .c 619, .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv359,pv401],
  .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv11,pv19,pv41], .c 3, .p pv3 [pv2,pv5,pv215939], .c 7, .c 3,
  .c 11, .p pv7 [pv2,pv3,pv37,pv71,pv137], .c 3, .p pv3 [pv2,pv539849], .c 5, .c 3, .c 17,
  .p pv23 [pv2,pv3,pv5,pv59,pv61], .c 3, .c 5, .c 443, .c 3,
]
private theorem h0527c30 : checkBlock 4318555 128 b0527c30 = true := by
  decide +kernel

private def b0527c31 : List Row := [
  .c 7, .p pv2 [pv2,pv3,pv39989], .c 3, .c 41, .c 593, .c 3, .p pv5 [pv2,pv83,pv26017], .c 5,
  .c 3, .p pv2 [pv2,pv97,pv11131], .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv491,pv733], .c 3, .c 107,
  .c 1693, .c 3, .c 13, .p pv7 [pv2,pv3,pv23,pv163], .c 3, .c 7, .c 5, .c 3, .c 59, .c 61, .c 3,
  .c 5, .c 7, .c 3, .c 19, .c 13, .c 3, .c 43, .p pv3 [pv2,pv3,pv719813], .c 3, .c 29, .c 5, .c 3,
  .c 31, .p pv2 [pv2,pv3,pv5,pv19,pv7577], .c 3, .c 5, .c 11, .c 3, .c 17, .c 89, .c 3, .c 109,
  .c 7, .c 3, .c 157, .c 5, .c 3, .c 11, .c 929, .c 3, .c 5, .c 271, .c 3, .c 449,
  .p pv7 [pv2,pv3,pv359911], .c 3, .c 7, .c 131, .c 3, .c 797, .c 5, .c 3,
  .p pv2 [pv2,pv107,pv10091], .c 7, .c 3, .c 5, .c 251, .c 3, .c 241, .c 11, .c 3, .c 373, .c 17,
  .c 3, .c 37, .c 5, .c 3, .c 7, .c 41, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv17,pv23,pv263], .c 3,
  .p pv17 [pv2,pv5,pv13,pv33223], .c 7, .c 3, .p pv2 [pv2,pv11,pv103,pv953], .c 29, .c 3, .c 13,
  .c 5, .c 3, .c 23, .c 163, .c 3, .c 5, .p pv11 [pv2,pv3,pv13,pv109,pv127], .c 3, .c 7, .c 19,
  .c 3, .p pv2 [pv2,pv2159513], .c 11, .c 3, .c 719, .c 5, .c 3, .c 421,
  .p pv7 [pv2,pv3,pv5,pv11,pv409], .c 3, .c 5, .c 37, .c 3, .c 11, .c 151, .c 3, .c 29, .c 743,
  .c 3, .c 7, .c 5,
]
private theorem h0527c31 : checkBlock 4318811 128 b0527c31 = true := by
  decide +kernel

def rows0527 : List Row :=
  b0527c00 ++ b0527c01 ++ b0527c02 ++ b0527c03 ++ b0527c04 ++ b0527c05 ++ b0527c06 ++ b0527c07 ++
  b0527c08 ++ b0527c09 ++ b0527c10 ++ b0527c11 ++ b0527c12 ++ b0527c13 ++ b0527c14 ++ b0527c15 ++
  b0527c16 ++ b0527c17 ++ b0527c18 ++ b0527c19 ++ b0527c20 ++ b0527c21 ++ b0527c22 ++ b0527c23 ++
  b0527c24 ++ b0527c25 ++ b0527c26 ++ b0527c27 ++ b0527c28 ++ b0527c29 ++ b0527c30 ++ b0527c31

theorem checked0527 : checkBlock 4310875 4096 rows0527 = true :=
  checkBlock_append h0527c00 (
    checkBlock_append h0527c01 (
    checkBlock_append h0527c02 (
    checkBlock_append h0527c03 (
    checkBlock_append h0527c04 (
    checkBlock_append h0527c05 (
    checkBlock_append h0527c06 (
    checkBlock_append h0527c07 (
    checkBlock_append h0527c08 (
    checkBlock_append h0527c09 (
    checkBlock_append h0527c10 (
    checkBlock_append h0527c11 (
    checkBlock_append h0527c12 (
    checkBlock_append h0527c13 (
    checkBlock_append h0527c14 (
    checkBlock_append h0527c15 (
    checkBlock_append h0527c16 (
    checkBlock_append h0527c17 (
    checkBlock_append h0527c18 (
    checkBlock_append h0527c19 (
    checkBlock_append h0527c20 (
    checkBlock_append h0527c21 (
    checkBlock_append h0527c22 (
    checkBlock_append h0527c23 (
    checkBlock_append h0527c24 (
    checkBlock_append h0527c25 (
    checkBlock_append h0527c26 (
    checkBlock_append h0527c27 (
    checkBlock_append h0527c28 (
    checkBlock_append h0527c29 (
    checkBlock_append h0527c30 (
    h0527c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
