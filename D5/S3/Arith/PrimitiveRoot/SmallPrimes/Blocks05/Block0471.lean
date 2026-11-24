/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks05/Block0471
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks05/Block0471.checked0471
   digest: Kernel proof of checker success on extended consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table038
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table046
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table052
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table059
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table068
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table081
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table097
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table121
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table157
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table158
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table161
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table163
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table167
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table170
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table174
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table175
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table181
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table189
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table190
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table202
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table222
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table223
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables03.Table246

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0471c00 : List Row := [
  .c 3, .c 5, .p pv3 [pv2,pv3,pv214007], .c 3, .p pv2 [pv2,pv5,pv569,pv677],
  .p pv2 [pv2,pv3,pv17,pv23,pv821], .c 3, .c 73, .p pv3 [pv2,pv3,pv197,pv3259], .c 3,
  .p pv5 [pv2,pv7,pv275153], .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv61,pv421], .c 3, .c 5, .c 29,
  .c 3, .c 97, .c 7, .c 3, .c 11, .c 59, .c 3, .c 13, .c 5, .c 3, .c 163, .c 37, .c 3, .c 5,
  .c 89, .c 3, .c 7, .c 19, .c 3, .c 1193, .c 13, .c 3, .c 1439, .c 5, .c 3,
  .p pv3 [pv2,pv240763], .c 11, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv192611], .c 181, .c 3,
  .c 211, .c 281, .c 3, .c 7, .c 5, .c 3, .c 277, .c 43, .c 3, .c 5, .c 7, .c 3, .c 13,
  .p pv5 [pv2,pv3,pv53,pv673], .c 3, .p pv3 [pv2,pv120383], .c 179, .c 3,
  .p pv5 [pv2,pv349,pv5519], .c 5, .c 3, .c 19, .p pv13 [pv2,pv3,pv5,pv23,pv1861], .c 3, .c 5,
  .c 11, .c 3, .c 1327, .c 73, .c 3, .c 59, .c 7, .c 3, .c 23, .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv12841], .c 3, .c 5, .c 19, .c 3, .c 977, .p pv5 [pv2,pv3,pv151,pv1063],
  .c 3, .c 7, .c 17, .c 3, .p pv2 [pv2,pv1926161], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv17,pv4721], .c 3, .p pv3 [pv2,pv5,pv192617], .c 11, .c 3,
  .p pv2 [pv2,pv59,pv32647], .c 269, .c 3, .c 17, .c 5, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv5,pv29,pv41], .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv37,pv67], .c 3, .c 409, .c 7,
  .c 3, .c 983,
]
private theorem h0471c00 : checkBlock 3852123 128 b0471c00 = true := by
  decide +kernel

private def b0471c01 : List Row := [
  .p pv11 [pv2,pv3,pv214021], .c 3, .c 19, .c 5, .c 3, .c 29, .p pv3 [pv2,pv3,pv5,pv128413], .c 3,
  .c 5, .c 1151, .c 3, .c 7, .c 37, .c 3, .c 13, .c 11, .c 3, .c 43, .c 5, .c 3,
  .p pv2 [pv2,pv29,pv127,pv523], .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv642071], .c 3, .c 11, .c 13,
  .c 3, .c 1667, .c 1013, .c 3, .c 7, .c 5, .c 3, .c 47, .p pv3 [pv2,pv3,pv5,pv7,pv1223], .c 3,
  .c 5, .c 7, .c 3, .c 541, .c 31, .c 3, .c 229, .c 1933, .c 3, .c 193, .c 5, .c 3, .c 283,
  .c 587, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv19457], .c 3, .c 1061, .p pv2 [pv2,pv3,pv7,pv45863],
  .c 3, .c 11, .c 7, .c 3, .p pv5 [pv2,pv73,pv26387], .c 5, .c 3, .c 103, .c 13, .c 3, .c 5,
  .c 53, .c 3, .c 547, .c 17, .c 3, .c 7, .c 883, .c 3, .c 1117, .c 5, .c 3,
  .p pv2 [pv2,pv1926269], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv23,pv27917], .c 3, .c 37,
  .p pv5 [pv2,pv3,pv11,pv14593], .c 3, .c 17, .p pv3 [pv2,pv3,pv214031], .c 3, .c 11, .c 5, .c 3,
  .c 7, .c 421, .c 3, .c 5, .c 61, .c 3, .p pv2 [pv2,pv5,pv192629], .c 7, .c 3, .c 31, .c 13,
  .c 3, .c 79, .c 5, .c 3, .c 251, .p pv53 [pv2,pv3,pv5,pv6421], .c 3, .c 5, .c 11, .c 3, .c 7,
  .c 881, .c 3, .c 179, .c 911, .c 3, .c 53, .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv19,pv751],
  .c 3,
]
private theorem h0471c01 : checkBlock 3852379 128 b0471c01 = true := by
  decide +kernel

private def b0471c02 : List Row := [
  .c 5, .c 47, .c 3, .c 13, .p pv2 [pv2,pv3,pv17,pv107,pv353], .c 3, .c 41, .c 19, .c 3, .c 7,
  .c 5, .c 3, .c 17, .c 23, .c 3, .c 5, .c 7, .c 3, .c 43, .c 11, .c 3,
  .p pv3 [pv2,pv17,pv53,pv1069], .c 29, .c 3, .p pv2 [pv2,pv1926341], .c 5, .c 3,
  .p pv3 [pv2,pv7,pv41,pv839], .p pv2 [pv2,pv3,pv5,pv167,pv769], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv229,pv701], .c 3, .c 67, .p pv5 [pv2,pv3,pv7,pv30577], .c 3, .c 23, .c 7,
  .c 3, .p pv3 [pv2,pv481589], .c 5, .c 3, .c 13, .c 73, .c 3, .c 5, .c 17, .c 3, .c 47,
  .p pv2 [pv2,pv3,pv13,pv24697], .c 3, .c 7, .c 11, .c 3, .c 97, .c 5, .c 3, .c 107, .c 7, .c 3,
  .c 5, .c 43, .c 3, .c 11, .c 19, .c 3, .p pv5 [pv2,pv29,pv181,pv367], .c 557, .c 3, .c 31, .c 5,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv157,pv409], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv91733], .c 3,
  .c 281, .c 7, .c 3, .c 13, .c 23, .c 3, .c 683, .c 5, .c 3, .p pv3 [pv2,pv401,pv1201], .c 41,
  .c 3, .c 5, .c 1487, .c 3, .c 7, .c 13, .c 3, .c 11, .c 17, .c 3, .c 1741, .c 5, .c 3, .c 19,
  .c 131, .c 3, .c 5, .c 37, .c 3, .c 137, .c 29, .c 3, .c 167, .c 193, .c 3, .c 7, .c 5, .c 3,
  .c 449, .c 11, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv17,pv2833], .c 173, .c 3, .c 269,
  .p pv7 [pv2,pv3,pv13,pv53,pv233],
]
private theorem h0471c02 : checkBlock 3852635 128 b0471c02 = true := by
  decide +kernel

private def b0471c03 : List Row := [
  .c 3, .c 11, .c 5, .c 3, .c 89, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv642151], .c 3, .c 29,
  .p pv37 [pv2,pv3,pv7,pv11467], .c 3, .p pv2 [pv2,pv151,pv6379], .c 7, .c 3,
  .p pv2 [pv2,pv1926461], .c 5, .c 3, .c 43, .c 17, .c 3, .c 5, .c 11, .c 3, .c 53, .c 61, .c 3,
  .c 7, .p pv31 [pv2,pv3,pv11,pv17,pv101], .c 3, .c 13, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5,
  .c 457, .c 3, .c 1303, .p pv7 [pv2,pv3,pv19,pv43,pv131], .c 3, .c 1049, .c 13, .c 3, .c 23,
  .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv45869], .c 3, .c 853, .c 7, .c 3,
  .p pv5 [pv2,pv23,pv83761], .p pv11 [pv2,pv3,pv991], .c 3, .c 47, .c 5, .c 3, .c 1163, .c 31,
  .c 3, .c 5, .c 29, .c 3, .c 7, .c 17, .c 3, .p pv2 [pv2,pv11,pv67,pv1307],
  .p pv7 [pv2,pv3,pv7,pv199,pv461], .c 3, .c 191, .c 5, .c 3, .c 101, .c 641, .c 3, .c 5, .c 13,
  .c 3, .c 811, .c 1783, .c 3, .c 17, .c 11, .c 3, .c 7, .c 5, .c 3, .p pv17 [pv2,pv271,pv7109],
  .p pv13 [pv2,pv3,pv5,pv7,pv11,pv139], .c 3, .c 5, .c 7, .c 3, .c 11, .p pv5 [pv2,pv3,pv321091],
  .c 3, .p pv3 [pv2,pv13,pv37049], .c 71, .c 3, .c 67, .c 5, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv5,pv128437], .c 3, .c 5, .c 1621, .c 3, .c 23, .c 197, .c 3, .c 103, .c 7,
  .c 3, .c 367, .c 5, .c 3, .c 41, .p pv7 [pv2,pv3,pv5,pv149,pv431], .c 3, .c 5,
]
private theorem h0471c03 : checkBlock 3852891 128 b0471c03 = true := by
  decide +kernel

private def b0471c04 : List Row := [
  .c 359, .c 3, .p pv7 [pv2,pv5,pv7,pv101,pv109], .c 53, .c 3, .c 7, .c 73, .c 3,
  .p pv2 [pv2,pv19,pv101399], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 107, .c 3, .c 19,
  .p pv5 [pv2,pv3,pv642197], .c 3, .c 13, .c 409, .c 3, .p pv3 [pv2,pv7,pv83,pv829], .c 5, .c 3,
  .c 7, .c 11, .c 3, .c 5, .c 31, .c 3, .p pv2 [pv2,pv5,pv385321], .c 7, .c 3, .c 37, .c 19, .c 3,
  .c 11, .c 5, .c 3, .c 173, .c 59, .c 3, .c 5, .c 17, .c 3, .c 7, .c 293, .c 3,
  .p pv5 [pv2,pv1926623], .p pv29 [pv2,pv3,pv7,pv47,pv61], .c 3, .c 1567, .c 5, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv5,pv21407], .c 3, .c 5, .c 11, .c 3, .c 17, .c 43, .c 3, .c 1129,
  .p pv11 [pv2,pv3,pv11,pv13,pv499], .c 3, .c 7, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv11,pv31,pv113], .c 41, .c 3, .c 127, .c 61, .c 3, .p pv3 [pv2,pv53,pv71],
  .c 5, .c 3, .c 1721, .p pv7 [pv2,pv3,pv5,pv163,pv197], .c 3, .c 5, .c 1901, .c 3, .c 31, .c 11,
  .c 3, .c 1433, .c 7, .c 3, .c 13, .c 5, .c 3, .c 59, .c 23, .c 3, .c 5, .c 1321, .c 3, .c 1447,
  .c 383, .c 3, .c 7, .c 13, .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv73,pv26393], .c 7, .c 3, .c 5,
  .c 1297, .c 3, .c 107, .c 31, .c 3, .c 23, .c 11, .c 3,
]
private theorem h0471c04 : checkBlock 3853147 128 b0471c04 = true := by
  decide +kernel

private def b0471c05 : List Row := [
  .p pv2 [pv2,pv7,pv37,pv43,pv173], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv11,pv11677], .c 3,
  .c 5, .p pv17 [pv2,pv3,pv7,pv22937], .c 3, .c 11, .c 7, .c 3, .p pv2 [pv2,pv41,pv46993],
  .p pv7 [pv2,pv3,pv19,pv16901], .c 3, .c 29, .c 5, .c 3, .c 37, .c 17, .c 3, .c 5, .c 13, .c 3,
  .c 7, .c 101, .c 3, .c 1613, .c 769, .c 3, .c 373, .c 5, .c 3, .p pv2 [pv2,pv963367], .c 53,
  .c 3, .c 5, .c 109, .c 3, .c 1877, .c 47, .c 3, .c 11, .c 23, .c 3, .c 7, .c 5, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv5,pv7,pv367], .c 3, .c 5, .c 7, .c 3, .p pv19 [pv2,pv5,pv385351], .c 37, .c 3,
  .c 31, .c 97, .c 3, .c 19, .c 5, .c 3, .p pv3 [pv2,pv7,pv68813], .c 11, .c 3, .c 5,
  .p pv17 [pv2,pv3,pv137,pv293], .c 3, .c 79, .c 17, .c 3, .p pv2 [pv2,pv1926773], .c 7, .c 3,
  .c 11, .c 5, .c 3, .p pv13 [pv2,pv23,pv83773], .c 19, .c 3, .c 5, .p pv3 [pv2,pv3,pv214087],
  .c 3, .c 431, .c 1367, .c 3, .c 7, .c 31, .c 3, .p pv5 [pv2,pv1926791], .c 5, .c 3,
  .p pv2 [pv2,pv963397], .c 7, .c 3, .c 5, .c 11, .c 3, .c 311, .c 13, .c 3, .c 29,
  .p pv19 [pv2,pv3,pv11,pv1327], .c 3, .p pv2 [pv2,pv7,pv229,pv601], .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv79,pv271], .c 3, .c 5, .c 23, .c 3, .c 41, .c 7, .c 3, .c 19, .c 67,
  .c 3, .p pv2 [pv2,pv13,pv103,pv1439], .c 5, .c 3, .p pv3 [pv2,pv240853], .c 1039, .c 3, .c 5,
  .c 443,
]
private theorem h0471c05 : checkBlock 3853403 128 b0471c05 = true := by
  decide +kernel

private def b0471c06 : List Row := [
  .c 3, .c 7, .c 11, .c 3, .c 71, .p pv2 [pv2,pv3,pv7,pv13,pv3529], .c 3, .c 23, .c 5, .c 3,
  .c 17, .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv642281], .c 3, .c 179, .p pv2 [pv2,pv3,pv167,pv641],
  .c 3, .p pv3 [pv2,pv7,pv11,pv17,pv23], .c 79, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv963427],
  .p pv7 [pv2,pv3,pv5,pv7,pv2039], .c 3, .c 5, .c 7, .c 3, .c 1669, .c 29, .c 3,
  .p pv5 [pv2,pv1926863], .c 11, .c 3, .c 13, .c 5, .c 3, .c 263,
  .p pv2 [pv2,pv3,pv5,pv11,pv5839], .c 3, .c 5, .c 17, .c 3, .c 11,
  .p pv5 [pv2,pv3,pv7,pv29,pv113], .c 3, .p pv2 [pv2,pv101,pv9539], .c 7, .c 3,
  .p pv2 [pv2,pv11,pv59,pv2969], .c 5, .c 3, .c 317, .c 307, .c 3, .c 5, .c 499, .c 3, .c 17,
  .c 577, .c 3, .c 7, .c 19, .c 3, .p pv3 [pv2,pv120431], .c 5, .c 3, .c 1259, .c 7, .c 3, .c 5,
  .c 191, .c 3, .c 13, .p pv2 [pv2,pv3,pv47,pv6833], .c 3, .c 11, .c 107, .c 3, .c 389, .c 5,
  .c 3, .c 7, .c 241, .c 3, .c 5, .c 13, .c 3, .c 229, .c 7, .c 3, .p pv5 [pv2,pv19,pv37,pv2741],
  .c 17, .c 3, .p pv2 [pv2,pv181,pv5323], .c 5, .c 3, .c 47, .c 11, .c 3, .c 5, .c 367, .c 3,
  .c 7, .p pv5 [pv2,pv3,pv11,pv811], .c 3, .c 41, .c 157, .c 3, .c 11, .c 5, .c 3, .c 13, .c 271,
  .c 3, .c 5, .c 29, .c 3, .c 277, .c 19, .c 3, .c 67, .p pv7 [pv2,pv3,pv107053], .c 3, .c 7,
]
private theorem h0471c06 : checkBlock 3853659 128 b0471c06 = true := by
  decide +kernel

private def b0471c07 : List Row := [
  .c 5, .c 3, .c 61, .c 173, .c 3, .c 5, .c 7, .c 3, .c 613, .p pv2 [pv2,pv3,pv337,pv953], .c 3,
  .p pv3 [pv2,pv79,pv3049], .c 59, .c 3, .p pv7 [pv2,pv127,pv15173], .c 5, .c 3, .c 11, .c 17,
  .c 3, .c 5, .c 37, .c 3, .c 43, .c 269, .c 3, .c 13, .c 7, .c 3, .c 151, .c 5, .c 3, .c 19,
  .c 439, .c 3, .c 5, .c 523, .c 3, .p pv7 [pv2,pv5,pv7,pv55057], .c 11, .c 3, .c 7, .c 991, .c 3,
  .p pv19 [pv2,pv17,pv263,pv431], .c 5, .c 3, .c 1201, .c 7, .c 3, .c 5, .c 19, .c 3, .c 829,
  .p pv3 [pv2,pv3,pv71,pv83,pv109], .c 3, .p pv2 [pv2,pv11,pv167,pv1049],
  .p pv19 [pv2,pv3,pv321169], .c 3, .c 107, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 43, .c 3,
  .c 379, .c 7, .c 3, .c 59, .c 11, .c 3, .p pv5 [pv2,pv1927031], .c 5, .c 3, .c 127, .c 13, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv397,pv809], .c 3, .c 7, .p pv2 [pv2,pv3,pv41,pv15667], .c 3, .c 17,
  .p pv19 [pv2,pv3,pv7,pv2549], .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv701,pv2749], .c 97, .c 3,
  .c 5, .c 53, .c 3, .p pv7 [pv2,pv5,pv13,pv23,pv1289], .p pv11 [pv2,pv3,pv19,pv2113], .c 3,
  .p pv2 [pv2,pv7,pv59,pv2333], .p pv11 [pv2,pv3,pv487,pv1319], .c 3, .c 7, .c 5, .c 3, .c 29,
  .c 19, .c 3, .c 5, .c 7, .c 3, .c 47, .p pv5 [pv2,pv3,pv37,pv643], .c 3, .c 11, .c 13, .c 3,
  .p pv3 [pv2,pv481769], .c 5, .c 3, .p pv7 [pv2,pv7,pv11,pv29,pv863], .c 677, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv642361], .c 3,
]
private theorem h0471c07 : checkBlock 3853915 128 b0471c07 = true := by
  decide +kernel

private def b0471c08 : List Row := [
  .p pv2 [pv2,pv5,pv385417], .c 79, .c 3, .c 283, .c 7, .c 3, .c 149, .c 5, .c 3, .c 17, .c 11,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv127,pv281], .c 3, .c 13, .p pv2 [pv2,pv3,pv11,pv23,pv2539], .c 3,
  .c 7, .c 373, .c 3, .c 11, .c 5, .c 3, .c 43, .c 7, .c 3, .c 5, .c 13, .c 3,
  .p pv19 [pv2,pv5,pv31,pv12433], .c 227, .c 3, .p pv2 [pv2,pv963559], .c 1217, .c 3,
  .p pv2 [pv2,pv7,pv67,pv587], .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv571], .c 3, .c 5, .c 11,
  .c 3, .c 31, .c 7, .c 3, .c 173, .c 337, .c 3, .p pv3 [pv2,pv60223], .c 5, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv5,pv32119], .c 3, .c 5, .c 41, .c 3, .c 7, .c 59, .c 3,
  .p pv3 [pv2,pv481787], .c 229, .c 3, .c 29, .c 5, .c 3, .c 67, .p pv3 [pv2,pv3,pv5,pv128477],
  .c 3, .c 5, .c 23, .c 3, .c 19, .c 11, .c 3, .c 37, .c 47, .c 3, .c 7, .c 5, .c 3, .c 1579,
  .p pv41 [pv2,pv3,pv5,pv7,pv19,pv23], .c 3, .c 5, .c 7, .c 3, .c 1723, .c 239, .c 3, .c 13,
  .c 17, .c 3, .c 23, .c 5, .c 3, .c 41, .c 1381, .c 3, .c 5, .c 71, .c 3, .c 419, .c 13, .c 3,
  .p pv2 [pv2,pv23,pv83791], .c 7, .c 3, .c 17, .c 5, .c 3, .c 617, .c 37, .c 3, .c 5, .c 61,
  .c 3, .c 11, .c 131, .c 3, .c 7, .c 29, .c 3, .c 47, .c 5,
]
private theorem h0471c08 : checkBlock 3854171 128 b0471c08 = true := by
  decide +kernel

private def b0471c09 : List Row := [
  .c 3, .p pv2 [pv2,pv963607], .c 7, .c 3, .c 5, .c 83, .c 3, .c 911, .c 67, .c 3, .c 31,
  .p pv23 [pv2,pv3,pv13,pv29,pv71], .c 3, .p pv2 [pv2,pv7,pv137659], .c 5, .c 3, .c 7, .c 13,
  .c 3, .c 5, .p pv11 [pv2,pv3,pv7,pv11,pv103], .c 3, .p pv11 [pv2,pv5,pv47,pv59,pv139], .c 7,
  .c 3, .c 11, .c 1153, .c 3, .p pv2 [pv2,pv1927241], .c 5, .c 3, .c 79, .c 659, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv40151], .c 3, .c 7, .c 1091, .c 3, .c 157, .c 31, .c 3, .c 13, .c 5, .c 3,
  .c 71, .c 11, .c 3, .c 5, .c 167, .c 3, .c 53, .c 41, .c 3, .p pv3 [pv2,pv7,pv9833], .c 13,
  .c 3, .c 7, .c 5, .c 3, .c 19, .p pv3 [pv2,pv3,pv5,pv7,pv3671], .c 3, .c 5, .c 7, .c 3, .c 1511,
  .c 17, .c 3, .c 109, .c 103, .c 3, .p pv2 [pv2,pv963643], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv13,pv21179], .p pv29 [pv2,pv3,pv5,pv17,pv3779], .c 3, .c 5, .c 11, .c 3,
  .c 13, .c 23, .c 3, .c 17, .c 7, .c 3, .c 83, .c 5, .c 3, .c 11, .c 47, .c 3, .c 5, .c 13, .c 3,
  .p pv2 [pv2,pv5,pv7,pv11,pv2503], .c 37, .c 3, .c 7, .p pv2 [pv2,pv3,pv11897], .c 3, .c 31,
  .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 59, .c 3, .c 29, .c 11, .c 3, .c 509, .c 653, .c 3,
  .c 19, .c 5, .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv128489], .c 3, .c 5,
  .p pv11 [pv2,pv3,pv7,pv109,pv421], .c 3, .p pv7 [pv2,pv5,pv29,pv3323],
]
private theorem h0471c09 : checkBlock 3854427 128 b0471c09 = true := by
  decide +kernel

private def b0471c10 : List Row := [
  .c 7, .c 3, .c 227, .c 1847, .c 3, .p pv2 [pv2,pv43,pv73,pv307], .c 5, .c 3, .c 17, .c 19, .c 3,
  .c 5, .c 853, .c 3, .c 7, .c 1523, .c 3, .p pv2 [pv2,pv17,pv56687], .c 11, .c 3,
  .p pv2 [pv2,pv1927361], .c 5, .c 3, .p pv3 [pv2,pv151,pv3191], .c 23, .c 3, .c 5,
  .p pv43 [pv2,pv3,pv8923], .c 3, .c 11, .c 53, .c 3, .c 13, .p pv2 [pv2,pv3,pv139,pv2311], .c 3,
  .c 7, .c 5, .c 3, .c 211, .p pv19 [pv2,pv3,pv5,pv7,pv13,pv353], .c 3, .c 5, .c 7, .c 3, .c 37,
  .c 13, .c 3, .c 19, .c 41, .c 3, .p pv5 [pv2,pv107,pv18013], .c 5, .c 3, .c 193, .c 263, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv11,pv19,pv29,pv53], .c 3, .c 17, .c 71, .c 3, .c 11, .c 7, .c 3, .c 401,
  .c 5, .c 3, .c 31, .c 43, .c 3, .c 5, .p pv2 [pv2,pv3,pv331,pv647], .c 3, .c 127, .c 709, .c 3,
  .c 7, .c 1619, .c 3, .p pv2 [pv2,pv1927421], .c 5, .c 3, .c 53, .c 7, .c 3, .c 5, .c 89, .c 3,
  .c 41, .c 1301, .c 3, .c 101, .c 17, .c 3, .c 11, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5, .c 139,
  .c 3, .c 19, .c 7, .c 3, .p pv3 [pv2,pv197,pv1223], .p pv2 [pv2,pv3,pv71387], .c 3, .c 13, .c 5,
  .c 3, .c 1031, .c 73, .c 3, .c 5, .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv642487], .c 3,
  .p pv5 [pv2,pv1291,pv1493], .c 13, .c 3, .p pv2 [pv2,pv823,pv1171], .c 5, .c 3,
]
private theorem h0471c10 : checkBlock 3854683 128 b0471c10 = true := by
  decide +kernel

private def b0471c11 : List Row := [
  .c 11, .c 29, .c 3, .c 5, .p pv13 [pv2,pv3,pv89,pv7219], .c 3, .c 773, .c 191, .c 3,
  .p pv2 [pv2,pv7,pv37,pv61], .c 173, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv13,pv101,pv367],
  .c 17, .c 3, .c 5, .c 7, .c 3, .c 13, .c 11, .c 3, .c 47, .p pv2 [pv2,pv3,pv17,pv6299], .c 3,
  .c 37, .c 5, .c 3, .c 29, .c 59, .c 3, .c 5, .c 13, .c 3, .c 1093,
  .p pv37 [pv2,pv3,pv7,pv45893], .c 3, .c 61, .c 7, .c 3, .p pv5 [pv2,pv17,pv113383], .c 5, .c 3,
  .p pv2 [pv2,pv29,pv167,pv199], .c 1699, .c 3, .c 5, .c 317, .c 3, .p pv3 [pv2,pv5,pv7,pv1721],
  .c 19, .c 3, .c 7, .c 11, .c 3, .c 23, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 31, .c 3, .c 11,
  .c 17, .c 3, .c 149, .c 43, .c 3, .p pv2 [pv2,pv7,pv11,pv25033], .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv17,pv7559], .c 3, .c 5, .c 421, .c 3, .c 83, .c 7, .c 3, .c 17, .c 251,
  .c 3, .c 67, .c 5, .c 3, .c 19, .c 79, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv58411], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv173,pv619], .c 3, .c 11, .c 61, .c 3, .p pv5 [pv2,pv1927571], .c 5, .c 3,
  .p pv2 [pv2,pv11,pv41,pv2137], .p pv11 [pv2,pv3,pv5,pv13,pv659], .c 3, .c 5, .c 19, .c 3,
  .p pv3 [pv2,pv5,pv31,pv3109], .c 13, .c 3, .c 53, .p pv7 [pv2,pv3,pv23,pv97], .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv37,pv59,pv883], .c 11, .c 3, .c 5, .c 7, .c 3, .c 23, .c 1607,
]
private theorem h0471c11 : checkBlock 3854939 128 b0471c11 = true := by
  decide +kernel

private def b0471c12 : List Row := [
  .c 3, .p pv2 [pv2,pv963799], .c 131, .c 3, .c 11, .c 5, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv5,pv107,pv1201], .c 3, .c 5, .p pv5 [pv2,pv3,pv80317], .c 3, .c 109,
  .p pv5 [pv2,pv3,pv7,pv31,pv47], .c 3, .c 199, .c 7, .c 3, .c 19, .c 5, .c 3,
  .p pv11 [pv2,pv1927619], .c 13, .c 3, .c 5, .c 11, .c 3, .c 43, .c 31, .c 3, .c 7, .c 1123,
  .c 3, .c 1277, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 17, .c 3, .c 727, .c 23, .c 3,
  .p pv5 [pv2,pv277,pv6959], .c 29, .c 3, .c 13, .c 5, .c 3, .c 7, .c 359, .c 3, .c 5, .c 1451,
  .c 3, .c 17, .c 7, .c 3, .c 107, .c 13, .c 3, .p pv2 [pv2,pv61,pv31601], .c 5, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv5,pv109,pv131], .c 3, .c 5, .c 43, .c 3, .c 7, .c 461, .c 3, .c 19, .c 73,
  .c 3, .c 41, .c 5, .c 3, .p pv7 [pv2,pv13,pv79,pv1877], .p pv7 [pv2,pv3,pv5,pv251], .c 3, .c 5,
  .p pv17 [pv2,pv3,pv19,pv11273], .c 3, .c 13, .c 1229, .c 3, .c 31, .c 11, .c 3, .c 7, .c 5,
  .c 3, .c 1009, .c 89, .c 3, .c 5, .c 7, .c 3, .c 11, .c 349, .c 3, .c 1559,
  .p pv11 [pv2,pv3,pv31,pv2591], .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv7,pv39341], .c 23, .c 3,
  .c 5, .c 743, .c 3, .p pv13 [pv2,pv5,pv17,pv22679], .c 83, .c 3, .c 37, .c 7, .c 3, .c 139,
  .c 5, .c 3, .c 13,
]
private theorem h0471c12 : checkBlock 3855195 128 b0471c12 = true := by
  decide +kernel

private def b0471c13 : List Row := [
  .c 233, .c 3, .c 5, .c 47, .c 3, .c 19, .c 29, .c 3, .c 7, .p pv2 [pv2,pv3,pv321289], .c 3,
  .c 59, .c 5, .c 3, .p pv11 [pv2,pv11,pv173,pv1013], .c 7, .c 3, .c 5, .c 197, .c 3, .c 1471,
  .p pv2 [pv2,pv3,pv29,pv1231], .c 3, .p pv3 [pv2,pv103,pv4679], .c 19, .c 3,
  .p pv5 [pv2,pv7,pv275393], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 41, .c 3, .c 29, .c 7, .c 3,
  .c 13, .c 167, .c 3, .c 11, .c 5, .c 3, .p pv7 [pv2,pv53,pv36373],
  .p pv2 [pv2,pv3,pv5,pv13,pv4943], .c 3, .c 5, .p pv2 [pv2,pv3,pv71399], .c 3, .c 7, .c 13, .c 3,
  .p pv2 [pv2,pv19,pv97,pv523], .c 23, .c 3, .c 31, .c 5, .c 3, .c 89,
  .p pv2 [pv2,pv3,pv5,pv128519], .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv263,pv733], .c 17,
  .c 3, .c 293, .c 1087, .c 3, .c 7, .c 5, .c 3, .c 11, .c 281, .c 3, .c 5, .c 7, .c 3, .c 251,
  .c 19, .c 3, .c 17, .c 1811, .c 3, .p pv5 [pv2,pv37,pv52103], .c 5, .c 3, .c 1747, .c 13, .c 3,
  .c 5, .c 29, .c 3, .c 73, .c 11, .c 3, .p pv5 [pv2,pv1927823], .c 7, .c 3, .c 97, .c 5, .c 3,
  .c 37, .c 383, .c 3, .c 5, .p pv7 [pv2,pv3,pv29,pv22159], .c 3, .c 317, .c 113, .c 3, .c 7,
  .c 829, .c 3, .c 13, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 23, .c 3, .c 373,
  .p pv5 [pv2,pv3,pv17,pv103,pv367], .c 3,
]
private theorem h0471c13 : checkBlock 3855451 128 b0471c13 = true := by
  decide +kernel

private def b0471c14 : List Row := [
  .c 541, .c 11, .c 3, .c 1361, .c 5, .c 3, .c 7, .c 139, .c 3, .c 5, .c 19, .c 3, .c 11, .c 7,
  .c 3, .c 439, .c 47, .c 3, .c 23, .c 5, .c 3, .c 31, .c 619, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv321313], .c 3, .c 7, .c 41, .c 3, .c 43, .p pv13 [pv2,pv3,pv7,pv59,pv389],
  .c 3, .c 499, .c 5, .c 3, .p pv2 [pv2,pv311,pv6199], .p pv7 [pv2,pv3,pv5,pv31,pv691], .c 3,
  .c 5, .c 13, .c 3, .c 1487, .p pv5 [pv2,pv3,pv80329], .c 3, .c 11, .p pv17 [pv2,pv3,pv214211],
  .c 3, .c 7, .c 5, .c 3, .c 659, .c 29, .c 3, .c 5, .c 7, .c 3, .c 17, .c 491, .c 3, .c 59,
  .p pv7 [pv2,pv3,pv321319], .c 3, .c 47, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 97, .c 3,
  .p pv2 [pv2,pv5,pv67,pv1151], .c 43, .c 3, .p pv3 [pv2,pv53,pv4547], .c 7, .c 3, .c 11, .c 5,
  .c 3, .c 29, .c 61, .c 3, .c 5, .c 101, .c 3, .c 23, .c 1069, .c 3, .c 7, .c 17, .c 3, .c 223,
  .c 5, .c 3, .c 113, .c 7, .c 3, .c 5, .c 11, .c 3, .c 79, .p pv7 [pv2,pv3,pv160663], .c 3,
  .c 13, .p pv3 [pv2,pv3,pv11,pv37,pv1579], .c 3, .c 17, .c 5, .c 3, .c 7, .c 83, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv7,pv19,pv151], .c 3, .c 1801, .c 7, .c 3, .c 193, .p pv2 [pv2,pv3,pv321329],
  .c 3, .p pv3 [pv2,pv240997], .c 5, .c 3, .c 107, .p pv11 [pv2,pv3,pv5,pv10711],
]
private theorem h0471c14 : checkBlock 3855707 128 b0471c14 = true := by
  decide +kernel

private def b0471c15 : List Row := [
  .c 3, .c 5, .p pv3 [pv2,pv3,pv31,pv20731], .c 3, .c 7, .c 11, .c 3, .p pv3 [pv2,pv481997],
  .p pv3 [pv2,pv3,pv7,pv101], .c 3, .p pv5 [pv2,pv13,pv43,pv3449], .c 5, .c 3,
  .p pv2 [pv2,pv317,pv3041], .c 17, .c 3, .c 5, .c 31, .c 3, .p pv11 [pv2,pv5,pv241], .c 587,
  .c 3, .p pv7 [pv2,pv7,pv11,pv73], .c 41, .c 3, .c 7, .c 5, .c 3, .c 23, .c 13, .c 3, .c 5, .c 7,
  .c 3, .c 19, .p pv7 [pv2,pv3,pv4463], .c 3, .p pv2 [pv2,pv964009], .c 11, .c 3, .c 29, .c 5,
  .c 3, .c 227, .c 67, .c 3, .c 5, .c 419, .c 3, .c 11, .c 59, .c 3,
  .p pv2 [pv2,pv37,pv107,pv487], .c 7, .c 3, .c 13, .c 5, .c 3, .c 73, .c 71, .c 3, .c 5, .c 151,
  .c 3, .c 41, .c 17, .c 3, .c 7, .c 13, .c 3, .c 37, .c 5, .c 3, .p pv2 [pv2,pv964027], .c 7,
  .c 3, .c 5, .c 277, .c 3, .c 31, .p pv5 [pv2,pv3,pv59,pv3631], .c 3, .c 11,
  .p pv53 [pv2,pv3,pv5021], .c 3, .p pv11 [pv2,pv7,pv41,pv3359], .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv37,pv193], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv91813], .c 3, .c 13, .c 7,
  .c 3, .c 23, .c 29, .c 3, .c 281, .c 5, .c 3, .c 877, .c 11, .c 3, .c 5, .c 13, .c 3, .c 7,
  .c 19, .c 3, .p pv2 [pv2,pv1928093], .c 1033, .c 3, .c 11, .c 5, .c 3, .p pv7 [pv2,pv1928099],
  .c 701, .c 3, .c 5, .c 1931, .c 3, .c 347, .p pv2 [pv2,pv3,pv17,pv6301], .c 3, .c 29,
]
private theorem h0471c15 : checkBlock 3855963 128 b0471c15 = true := by
  decide +kernel

private def b0471c16 : List Row := [
  .c 977, .c 3, .c 7, .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv7,pv6121], .c 3, .c 5, .c 7, .c 3,
  .c 241, .p pv2 [pv2,pv3,pv13,pv3803], .c 3, .c 131, .c 23, .c 3, .p pv2 [pv2,pv67,pv14389],
  .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv64271], .c 3, .c 5, .p pv2 [pv2,pv3,pv214237], .c 3,
  .c 607, .p pv5 [pv2,pv3,pv7,pv23,pv499], .c 3, .c 139, .c 7, .c 3, .c 43, .c 5, .c 3,
  .p pv3 [pv2,pv37,pv3257], .c 337, .c 3, .c 5, .c 17, .c 3, .c 827, .c 11, .c 3, .c 7, .c 983,
  .c 3, .c 733, .c 5, .c 3, .c 67, .c 7, .c 3, .c 5, .c 463, .c 3, .c 17, .c 13, .c 3, .c 41,
  .c 223, .c 3, .c 173, .c 5, .c 3, .c 7, .c 113, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv5101], .c 3,
  .p pv3 [pv2,pv5,pv229,pv421], .c 7, .c 3, .p pv5 [pv2,pv1928183], .c 11, .c 3, .c 19, .c 5,
  .c 3, .p pv7 [pv2,pv41,pv131,pv359], .p pv19 [pv2,pv3,pv5,pv11,pv5843], .c 3, .c 5, .c 23, .c 3,
  .c 7, .p pv5 [pv2,pv3,pv19,pv2819], .c 3, .c 47, .c 17, .c 3, .p pv2 [pv2,pv11,pv175291], .c 5,
  .c 3, .p pv3 [pv2,pv482051], .c 13, .c 3, .c 5, .c 59, .c 3, .c 199, .c 103, .c 3, .c 383,
  .c 83, .c 3, .c 7, .c 5, .c 3, .c 53, .c 283, .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv13,pv17,pv349], .c 67, .c 3, .c 11, .c 89, .c 3, .c 13, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv11,pv19,pv659], .c 691, .c 3,
]
private theorem h0471c16 : checkBlock 3856219 128 b0471c16 = true := by
  decide +kernel

private def b0471c17 : List Row := [
  .c 5, .p pv2 [pv2,pv3,pv13,pv59,pv419], .c 3, .c 61, .c 101, .c 3, .c 19, .c 7, .c 3, .c 31,
  .c 5, .c 3, .p pv2 [pv2,pv43,pv44843], .c 11, .c 3, .c 5, .c 29, .c 3,
  .p pv7 [pv2,pv5,pv7,pv37,pv1489], .p pv7 [pv2,pv3,pv11,pv83], .c 3, .c 7,
  .p pv3 [pv2,pv3,pv17,pv4201], .c 3, .c 11, .c 5, .c 3, .c 109, .c 7, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv29,pv1847], .c 3, .c 13, .c 79, .c 3, .c 37, .p pv2 [pv2,pv3,pv23,pv89,pv157],
  .c 3, .c 487, .c 5, .c 3, .c 7, .p pv31 [pv2,pv3,pv5,pv16069], .c 3, .c 5, .c 11, .c 3, .c 23,
  .c 7, .c 3, .c 113, .p pv3 [pv2,pv3,pv11,pv71,pv823], .c 3, .c 41, .c 5, .c 3, .c 11,
  .p pv19 [pv2,pv3,pv5,pv73,pv587], .c 3, .c 5, .p pv7 [pv2,pv3,pv321383], .c 3, .c 7, .c 17,
  .c 3, .p pv5 [pv2,pv13,pv148331], .c 127, .c 3, .p pv2 [pv2,pv964153], .c 5, .c 3, .c 13, .c 37,
  .c 3, .c 5, .c 43, .c 3, .p pv7 [pv2,pv5,pv385663], .c 11, .c 3, .c 17, .c 19, .c 3, .c 7, .c 5,
  .c 3, .c 71, .c 53, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv192833], .c 23, .c 3,
  .p pv2 [pv2,pv11,pv175303], .c 197, .c 3, .c 1217, .c 5, .c 3, .c 31, .c 29, .c 3, .c 5, .c 137,
  .c 3, .c 151, .c 509, .c 3, .c 13, .c 7, .c 3, .p pv5 [pv2,pv1928351], .c 5, .c 3, .c 23,
  .c 311, .c 3, .c 5, .p pv2 [pv2,pv3,pv149,pv719], .c 3, .c 11, .c 13, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv160697],
]
private theorem h0471c17 : checkBlock 3856475 128 b0471c17 = true := by
  decide +kernel

private def b0471c18 : List Row := [
  .c 3, .p pv3 [pv2,pv11,pv23,pv37,pv103], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 41, .c 3,
  .p pv13 [pv2,pv5,pv15427], .c 19, .c 3, .c 53, .c 293, .c 3, .p pv2 [pv2,pv7,pv13,pv21191],
  .c 5, .c 3, .c 7, .c 59, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv11,pv2087], .c 3, .c 421, .c 7, .c 3,
  .c 11, .c 541, .c 3, .p pv3 [pv2,pv482099], .c 5, .c 3, .c 43, .c 13, .c 3, .c 5, .c 17, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv331,pv971], .c 3, .c 97, .c 199, .c 3, .p pv5 [pv2,pv1928411], .c 5,
  .c 3, .c 19, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv321403], .c 3, .c 17, .c 37, .c 3, .c 23,
  .c 233, .c 3, .c 7, .c 5, .c 3, .c 79, .p pv2 [pv2,pv3,pv5,pv7,pv3061], .c 3, .c 5, .c 7, .c 3,
  .c 1429, .p pv5 [pv2,pv3,pv271,pv593], .c 3, .p pv2 [pv2,pv964219], .c 13, .c 3, .c 839, .c 5,
  .c 3, .c 59, .p pv2 [pv2,pv3,pv5,pv128563], .c 3, .c 5, .c 11, .c 3, .c 683,
  .p pv7 [pv2,pv3,pv7,pv131,pv701], .c 3, .p pv2 [pv2,pv163,pv11831], .c 7, .c 3, .c 29, .c 5,
  .c 3, .c 11, .p pv17 [pv2,pv3,pv5,pv32141], .c 3, .c 5, .c 31, .c 3, .c 13, .c 71, .c 3, .c 7,
  .c 23, .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv59,pv277], .c 7, .c 3, .c 5, .c 13, .c 3, .c 47,
  .c 11, .c 3, .p pv5 [pv2,pv1237,pv1559], .c 53, .c 3, .p pv2 [pv2,pv7,pv139,pv991], .c 5, .c 3,
  .c 7, .c 19, .c 3, .c 5,
]
private theorem h0471c18 : checkBlock 3856731 128 b0471c18 = true := by
  decide +kernel

private def b0471c19 : List Row := [
  .p pv2 [pv2,pv3,pv7,pv4373], .c 3, .c 37, .c 7, .c 3, .p pv2 [pv2,pv11,pv13,pv613],
  .p pv3 [pv2,pv3,pv642833], .c 3, .p pv2 [pv2,pv1928501], .c 5, .c 3, .c 13, .c 17, .c 3, .c 5,
  .c 79, .c 3, .c 7, .p pv5 [pv2,pv3,pv13,pv53,pv311], .c 3, .p pv2 [pv2,pv1928513], .c 11, .c 3,
  .c 131, .c 5, .c 3, .p pv7 [pv2,pv19,pv101501], .c 103, .c 3, .c 5, .c 229, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv293,pv1097], .c 3, .c 19, .c 1669, .c 3, .c 7, .c 5, .c 3, .c 163, .c 1949,
  .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv211,pv457], .c 379, .c 3, .c 13, .c 101, .c 3, .c 83,
  .c 5, .c 3, .c 313, .c 73, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv58441], .c 3, .c 139, .c 13, .c 3,
  .c 11, .c 7, .c 3, .c 23, .c 5, .c 3, .c 1901, .c 947, .c 3, .c 5, .p pv5 [pv2,pv3,pv107,pv751],
  .c 3, .p pv2 [pv2,pv5,pv7,pv27551], .c 43, .c 3, .c 7, .c 47, .c 3, .p pv3 [pv2,pv13,pv19,pv61],
  .c 5, .c 3, .c 941, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv71429], .c 3, .c 19, .c 1049, .c 3,
  .c 587, .p pv2 [pv2,pv3,pv13,pv49451], .c 3, .c 11, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5,
  .c 1093, .c 3, .c 443, .c 7, .c 3, .p pv5 [pv2,pv31,pv62213], .c 19, .c 3, .c 37, .c 5, .c 3,
  .c 401, .c 239, .c 3, .c 5, .c 11, .c 3, .c 7, .p pv5 [pv2,pv3,pv17,pv29,pv163], .c 3, .c 31,
  .c 41, .c 3,
]
private theorem h0471c19 : checkBlock 3856987 128 b0471c19 = true := by
  decide +kernel

private def b0471c20 : List Row := [
  .c 13, .c 5, .c 3, .c 11, .c 569, .c 3, .c 5, .c 67, .c 3, .c 23, .p pv5 [pv2,pv3,pv642877],
  .c 3, .p pv2 [pv2,pv7,pv17,pv19,pv853], .c 13, .c 3, .c 7, .c 5, .c 3, .c 409, .c 1697, .c 3,
  .c 5, .c 7, .c 3, .c 101, .c 11, .c 3, .p pv3 [pv2,pv491], .c 31, .c 3, .c 631, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv13,pv10597], .p pv3 [pv2,pv3,pv5,pv42859], .c 3, .c 5, .c 17, .c 3, .c 13,
  .c 19, .c 3, .p pv11 [pv2,pv11,pv175333], .c 7, .c 3, .c 79, .c 5, .c 3,
  .p pv2 [pv2,pv1021,pv1889], .p pv7 [pv2,pv3,pv5,pv53,pv1213], .c 3, .c 5, .c 13, .c 3, .c 17,
  .c 23, .c 3, .c 7, .c 11, .c 3, .c 967, .c 5, .c 3, .p pv3 [pv2,pv17,pv113,pv251], .c 7, .c 3,
  .c 5, .c 29, .c 3, .c 11, .p pv3 [pv2,pv3,pv7937], .c 3, .c 479, .c 139, .c 3, .c 53, .c 5,
  .c 3, .c 7, .c 43, .c 3, .c 5, .c 1009, .c 3, .c 227, .c 7, .c 3, .p pv3 [pv2,pv199,pv2423],
  .c 17, .c 3, .c 31, .c 5, .c 3, .p pv2 [pv2,pv964357], .c 47, .c 3, .c 5, .c 19, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv642907], .c 3, .c 11, .p pv11 [pv2,pv3,pv7,pv22961], .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv67,pv2617], .c 149, .c 3, .c 5, .p pv2 [pv2,pv3,pv73,pv8807], .c 3, .c 907,
  .p pv17 [pv2,pv3,pv37,pv181], .c 3, .c 13, .c 59, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv241093],
  .c 11, .c 3, .c 5, .c 7,
]
private theorem h0471c20 : checkBlock 3857243 128 b0471c20 = true := by
  decide +kernel

private def b0471c21 : List Row := [
  .c 3, .c 71, .c 13, .c 3, .c 503, .c 37, .c 3, .c 11, .c 5, .c 3, .p pv7 [pv2,pv7,pv61,pv4517],
  .c 17, .c 3, .c 5, .c 89, .c 3, .p pv2 [pv2,pv5,pv43,pv8971], .c 167, .c 3, .c 23, .c 7, .c 3,
  .p pv5 [pv2,pv13,pv148367], .c 5, .c 3, .p pv2 [pv2,pv233,pv4139], .c 19, .c 3, .c 5, .c 11,
  .c 3, .p pv3 [pv2,pv5,pv7,pv23,pv599], .c 887, .c 3, .c 7, .p pv29 [pv2,pv3,pv11,pv13,pv281],
  .c 3, .c 43, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 1879, .c 3, .c 83, .c 97, .c 3, .c 59,
  .c 347, .c 3, .c 701, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv149,pv863], .c 3, .c 5, .c 1627,
  .c 3, .p pv2 [pv2,pv5,pv13,pv37,pv401], .c 7, .c 3, .c 19, .c 23, .c 3, .c 13, .c 5, .c 3,
  .c 337, .p pv73 [pv2,pv3,pv5,pv17,pv31,pv61], .c 3, .c 5, .c 157, .c 3, .c 7, .c 181, .c 3,
  .c 17, .c 13, .c 3, .p pv5 [pv2,pv1928831], .c 5, .c 3, .c 709, .c 31, .c 3, .c 5, .c 223, .c 3,
  .p pv3 [pv2,pv5,pv48221], .p pv3 [pv2,pv3,pv642947], .c 3, .c 241, .c 11, .c 3, .c 7, .c 5,
  .c 3, .c 239, .c 61, .c 3, .c 5, .c 7, .c 3, .c 11, .c 47, .c 3, .p pv2 [pv2,pv463,pv2083],
  .p pv3 [pv2,pv3,pv642953], .c 3, .p pv2 [pv2,pv11,pv19,pv839], .c 5, .c 3, .c 269, .c 37, .c 3,
  .c 5, .c 13, .c 3, .c 19, .p pv3 [pv2,pv3,pv7,pv17,pv1801], .c 3, .p pv2 [pv2,pv1928873], .c 7,
  .c 3, .c 1423,
]
private theorem h0471c21 : checkBlock 3857499 128 b0471c21 = true := by
  decide +kernel

private def b0471c22 : List Row := [
  .c 5, .c 3, .c 17, .p pv7 [pv2,pv3,pv5,pv19,pv47], .c 3, .c 5, .c 23, .c 3, .c 1583,
  .p pv2 [pv2,pv3,pv41,pv7841], .c 3, .c 7, .c 19, .c 3, .c 29, .c 5, .c 3, .c 13, .c 7, .c 3,
  .c 5, .c 1723, .c 3, .p pv3 [pv2,pv5,pv19289], .p pv3 [pv2,pv3,pv13,pv49459], .c 3, .c 47,
  .p pv11 [pv2,pv3,pv179,pv449], .c 3, .c 23, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 17, .c 3,
  .c 43, .c 7, .c 3, .c 109, .p pv3 [pv2,pv3,pv642973], .c 3, .c 11, .c 5, .c 3, .c 281, .c 197,
  .c 3, .c 5, .c 31, .c 3, .c 7, .p pv5 [pv2,pv3,pv642977], .c 3, .c 13, .p pv23 [pv2,pv3,pv7],
  .c 3, .p pv3 [pv2,pv241117], .c 5, .c 3, .c 37, .c 431, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv317,pv1217], .c 13, .c 3, .c 101, .c 29, .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv23 [pv2,pv3,pv5,pv7,pv18371], .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv11,pv137], .c 53,
  .c 3, .c 67, .c 17, .c 3, .c 113, .c 5, .c 3, .c 373, .p pv2 [pv2,pv3,pv5,pv21433], .c 3, .c 5,
  .c 263, .c 3, .c 23, .c 11, .c 3, .c 29, .c 7, .c 3, .c 17, .c 5, .c 3, .c 19, .c 13, .c 3,
  .c 5, .c 41, .c 3, .c 31, .p pv3 [pv2,pv3,pv642997], .c 3, .c 7, .p pv13 [pv2,pv3,pv19,pv16921],
  .c 3, .p pv3 [pv2,pv107,pv4507], .c 5, .c 3, .c 1489, .c 7, .c 3, .c 5, .c 19, .c 3,
]
private theorem h0471c22 : checkBlock 3857755 128 b0471c22 = true := by
  decide +kernel

private def b0471c23 : List Row := [
  .p pv11 [pv2,pv5,pv13,pv59,pv503], .c 199, .c 3, .p pv3 [pv2,pv120563], .c 11, .c 3, .c 13,
  .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv13,pv3533], .c 3, .c 11, .c 7, .c 3,
  .c 163, .c 13, .c 3, .p pv2 [pv2,pv11,pv87683], .c 5, .c 3, .c 41, .c 67, .c 3, .c 5, .c 61,
  .c 3, .c 7, .c 29, .c 3, .c 1619, .p pv3 [pv2,pv3,pv7,pv97,pv947], .c 3, .c 19, .c 5, .c 3,
  .c 23, .p pv2 [pv2,pv3,pv5,pv128603], .c 3, .c 5, .c 409, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv19,pv29,pv389], .c 3, .c 11, .c 461, .c 3, .c 7, .c 5, .c 3, .c 853, .c 19,
  .c 3, .c 5, .c 7, .c 3, .c 29, .c 17, .c 3, .c 929, .c 283, .c 3, .p pv5 [pv2,pv1929071], .c 5,
  .c 3, .c 1097, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv107171], .c 3, .c 1249,
  .p pv2 [pv2,pv3,pv7,pv11,pv1193], .c 3, .c 17, .c 7, .c 3, .c 11, .c 5, .c 3, .c 13, .c 23,
  .c 3, .c 5, .c 59, .c 3, .p pv43 [pv2,pv5,pv7,pv55117], .p pv5 [pv2,pv3,pv13,pv229], .c 3, .c 7,
  .p pv3 [pv2,pv3,pv31,pv20743], .c 3, .c 1237, .c 5, .c 3, .c 1451, .c 7, .c 3, .c 5, .c 11,
  .c 3, .c 1051, .c 41, .c 3, .c 23, .c 31, .c 3, .p pv5 [pv2,pv7,pv68897], .c 5, .c 3, .c 7,
  .c 53, .c 3, .c 5, .c 29, .c 3, .p pv2 [pv2,pv5,pv11,pv23,pv61], .c 7, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv643043], .c 3, .c 193, .c 5,
]
private theorem h0471c23 : checkBlock 3858011 128 b0471c23 = true := by
  decide +kernel

private def b0471c24 : List Row := [
  .c 3, .c 17, .c 367, .c 3, .c 5, .c 47, .c 3, .c 7, .c 11, .c 3, .p pv5 [pv2,pv17,pv37,pv3067],
  .p pv11 [pv2,pv3,pv7,pv11483], .c 3, .c 347, .c 5, .c 3, .p pv2 [pv2,pv1929149], .c 101, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv643051], .c 3, .c 19, .c 107, .c 3, .p pv3 [pv2,pv7,pv11,pv12527],
  .c 23, .c 3, .c 7, .c 5, .c 3, .c 67, .c 137, .c 3, .c 5, .c 7, .c 3, .c 257, .c 131, .c 3,
  .c 43, .c 11, .c 3, .c 31, .c 5, .c 3, .c 1021, .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv643061],
  .c 3, .c 11, .c 163, .c 3, .c 181, .c 7, .c 3, .c 1847, .c 5, .c 3, .c 569, .c 191, .c 3, .c 5,
  .c 37, .c 3, .p pv11 [pv2,pv5,pv7,pv13,pv53], .p pv2 [pv2,pv3,pv101,pv6367], .c 3, .c 7,
  .c 1637, .c 3, .c 13, .c 5, .c 3, .c 173, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv13,pv1499],
  .c 3, .p pv19 [pv2,pv5,pv385843], .c 43, .c 3, .c 11, .c 13, .c 3, .c 397, .c 5, .c 3, .c 7,
  .c 457, .c 3, .c 5, .c 23, .c 3, .p pv7 [pv2,pv5,pv192923], .c 7, .c 3, .c 331, .c 41, .c 3,
  .c 17, .c 5, .c 3, .c 29, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv643081], .c 3, .c 7,
  .p pv17 [pv2,pv3,pv11,pv29231], .c 3, .p pv3 [pv2,pv60289], .p pv41 [pv2,pv3,pv7,pv113,pv271],
  .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv29,pv31,pv37], .p pv13 [pv2,pv3,pv5,pv41,pv3137], .c 3,
  .c 5, .c 13, .c 3, .c 1913,
]
private theorem h0471c24 : checkBlock 3858267 128 b0471c24 = true := by
  decide +kernel

private def b0471c25 : List Row := [
  .p pv2 [pv2,pv3,pv643087], .c 3, .c 107, .p pv7 [pv2,pv3,pv40193], .c 3, .c 7, .c 5, .c 3,
  .c 19, .c 17, .c 3, .c 5, .c 7, .c 3, .c 41, .c 1213, .c 3, .c 211, .c 47, .c 3, .c 97, .c 5,
  .c 3, .c 11, .c 419, .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv11,pv17539],
  .p pv29 [pv2,pv3,pv7,pv13,pv37,pv191], .c 3, .c 83, .c 7, .c 3, .p pv3 [pv2,pv17,pv41,pv173],
  .c 5, .c 3, .c 379, .c 31, .c 3, .c 5, .p pv3 [pv2,pv3,pv47,pv4561], .c 3, .c 113, .c 11, .c 3,
  .c 7, .c 37, .c 3, .c 251, .c 5, .c 3, .p pv2 [pv2,pv859,pv1123], .c 7, .c 3, .c 5, .c 71, .c 3,
  .c 23, .c 17, .c 3, .c 13, .c 193, .c 3, .c 19, .c 5, .c 3, .c 7, .c 787, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv91873], .c 3, .p pv11 [pv2,pv5,pv83,pv4649], .c 7, .c 3, .c 17, .c 11,
  .c 3, .c 307, .c 5, .c 3, .c 103, .c 19, .c 3, .c 5, .c 953, .c 3, .c 7, .c 179, .c 3, .c 73,
  .c 109, .c 3, .c 233, .c 5, .c 3, .p pv7 [pv2,pv53,pv59,pv617], .p pv29 [pv2,pv3,pv5,pv8039],
  .c 3, .c 5, .p pv3 [pv2,pv3,pv643121], .c 3, .c 67, .c 23, .c 3, .p pv3 [pv2,pv7,pv131,pv263],
  .c 181, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv19,pv50773], .c 13, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv96469], .p pv2 [pv2,pv3,pv17,pv37831], .c 3, .c 11, .c 29, .c 3, .c 89, .c 5,
  .c 3,
]
private theorem h0471c25 : checkBlock 3858523 128 b0471c25 = true := by
  decide +kernel

private def b0471c26 : List Row := [
  .c 17, .p pv7 [pv2,pv3,pv5,pv73,pv881], .c 3, .c 5, .c 31, .c 3, .p pv19 [pv2,pv5,pv13,pv29683],
  .p pv5 [pv2,pv3,pv7,pv103,pv223], .c 3, .c 41, .c 7, .c 3, .c 13, .c 5, .c 3, .c 199, .c 11,
  .c 3, .c 5, .p pv11 [pv2,pv3,pv13,pv773], .c 3, .c 467, .c 401, .c 3, .c 7, .c 13, .c 3, .c 11,
  .c 5, .c 3, .p pv29 [pv2,pv41,pv47059], .c 7, .c 3, .c 5, .c 17, .c 3,
  .p pv2 [pv2,pv5,pv71,pv1087], .c 73, .c 3, .c 1061, .p pv2 [pv2,pv3,pv214381], .c 3, .c 43,
  .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 11, .c 3, .c 13, .c 7, .c 3, .c 277,
  .p pv7 [pv2,pv3,pv11,pv47,pv311], .c 3, .c 349, .c 5, .c 3, .c 11,
  .p pv13 [pv2,pv3,pv5,pv19,pv677], .c 3, .c 5, .c 13, .c 3, .c 7, .c 79, .c 3, .c 23, .c 19,
  .c 3, .p pv2 [pv2,pv1129,pv1709], .c 5, .c 3, .p pv3 [pv2,pv241183],
  .p pv2 [pv2,pv3,pv5,pv53,pv809], .c 3, .c 5, .c 1187, .c 3, .p pv2 [pv2,pv5,pv23,pv8389], .c 11,
  .c 3, .p pv2 [pv2,pv7,pv13,pv233], .c 17, .c 3, .c 7, .c 5, .c 3, .c 13, .c 41, .c 3, .c 5,
  .c 7, .c 3, .p pv2 [pv2,pv5,pv385897], .c 31, .c 3, .c 313, .c 211, .c 3, .c 17, .c 5, .c 3,
  .c 37, .p pv11 [pv2,pv3,pv5,pv307,pv419], .c 3, .c 5, .p pv11 [pv2,pv3,pv353,pv911], .c 3,
  .c 29, .p pv2 [pv2,pv3,pv7,pv41,pv83], .c 3, .p pv5 [pv2,pv1929503], .c 7, .c 3, .c 59, .c 5,
  .c 3, .p pv2 [pv2,pv1929509], .c 601, .c 3, .c 5, .p pv5 [pv2,pv3,pv37,pv17383], .c 3, .c 11,
  .c 19,
]
private theorem h0471c26 : checkBlock 3858779 128 b0471c26 = true := by
  decide +kernel

private def b0471c27 : List Row := [
  .c 3, .c 7, .p pv7 [pv2,pv3,pv214391], .c 3, .c 41, .c 5, .c 3, .p pv3 [pv2,pv97,pv4973], .c 7,
  .c 3, .c 5, .c 139, .c 3, .c 179, .c 13, .c 3, .p pv2 [pv2,pv31,pv67,pv929], .c 1433, .c 3,
  .p pv3 [pv2,pv7,pv59,pv73], .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv32159], .c 3, .c 5, .c 709,
  .c 3, .c 1153, .c 7, .c 3, .c 11, .p pv2 [pv2,pv3,pv643183], .c 3, .c 293, .c 5, .c 3, .c 19,
  .c 173, .c 3, .c 5, .c 29, .c 3, .c 7, .c 47, .c 3, .p pv5 [pv2,pv1929563], .c 89, .c 3, .c 67,
  .c 5, .c 3, .p pv2 [pv2,pv1929569], .c 11, .c 3, .c 5, .c 19, .c 3, .p pv7 [pv2,pv5,pv79,pv977],
  .c 17, .c 3, .p pv2 [pv2,pv7,pv137827], .c 31, .c 3, .c 7, .c 5, .c 3, .c 107,
  .p pv7 [pv2,pv3,pv5,pv7,pv17,pv23,pv47], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv13,pv14843],
  .p pv5 [pv2,pv3,pv214399], .c 3, .c 17, .p pv2 [pv2,pv3,pv163,pv1973], .c 3, .c 13, .c 5, .c 3,
  .c 311, .p pv17 [pv2,pv3,pv5,pv67], .c 3, .c 5, .c 11, .c 3, .c 37,
  .p pv11 [pv2,pv3,pv7,pv45943], .c 3, .c 47, .c 7, .c 3, .c 19, .c 5, .c 3, .c 11,
  .p pv31 [pv2,pv3,pv5,pv197,pv653], .c 3, .c 5, .c 397, .c 3, .c 1811,
  .p pv3 [pv2,pv3,pv19,pv97,pv349], .c 3, .c 7, .c 59, .c 3, .p pv2 [pv2,pv31,pv31123], .c 5,
  .c 3, .p pv2 [pv2,pv13,pv151,pv983], .c 7, .c 3, .c 5, .c 67, .c 3, .c 13, .c 11, .c 3,
  .p pv2 [pv2,pv71,pv107,pv127], .p pv7 [pv2,pv3,pv643213], .c 3, .c 31, .c 5, .c 3, .c 7,
]
private theorem h0471c27 : checkBlock 3859035 128 b0471c27 = true := by
  decide +kernel

private def b0471c28 : List Row := [
  .c 29, .c 3, .c 5, .c 13, .c 3, .c 53, .c 7, .c 3, .c 89, .p pv2 [pv2,pv3,pv23,pv59,pv79], .c 3,
  .p pv3 [pv2,pv241207], .c 5, .c 3, .p pv7 [pv2,pv19,pv101561],
  .p pv19 [pv2,pv3,pv5,pv29,pv1109], .c 3, .c 5, .p pv37 [pv2,pv3,pv2647], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv321611], .c 3, .c 19, .c 11, .c 3, .c 269, .c 5, .c 3, .c 13, .c 163, .c 3,
  .c 5, .c 17, .c 3, .c 11, .c 109, .c 3, .c 59, .c 257, .c 3, .c 7, .c 5, .c 3, .c 43,
  .p pv73 [pv2,pv3,pv5,pv7,pv1021], .c 3, .c 5, .c 7, .c 3, .c 17, .p pv7 [pv2,pv3,pv20101], .c 3,
  .c 1103, .p pv3 [pv2,pv3,pv149,pv1439], .c 3, .c 127, .c 5, .c 3, .c 61,
  .p pv31 [pv2,pv3,pv5,pv103,pv1249], .c 3, .c 5, .c 83, .c 3, .c 193, .c 23, .c 3, .c 11, .c 7,
  .c 3, .c 37, .c 5, .c 3, .p pv11 [pv2,pv11,pv31,pv5659], .c 277, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv23,pv27967], .c 3, .c 19, .c 13, .c 3, .c 7, .c 17, .c 3, .c 181, .c 5, .c 3,
  .c 23, .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv17,pv18919], .c 3, .p pv7 [pv2,pv5,pv96487],
  .p pv5 [pv2,pv3,pv11,pv58477], .c 3, .c 859, .c 19, .c 3, .c 11, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv31,pv83], .c 3, .c 5, .c 37, .c 3, .p pv13 [pv2,pv5,pv17,pv73,pv311],
  .c 7, .c 3, .p pv2 [pv2,pv964879], .c 503, .c 3, .c 29, .c 5, .c 3, .p pv3 [pv2,pv482441],
  .c 13, .c 3, .c 5, .c 11, .c 3, .c 7, .c 1801, .c 3,
]
private theorem h0471c28 : checkBlock 3859291 128 b0471c28 = true := by
  decide +kernel

private def b0471c29 : List Row := [
  .c 149, .c 811, .c 3, .c 577, .c 5, .c 3, .c 11, .c 17, .c 3, .c 5, .p pv3 [pv2,pv3,pv53,pv229],
  .c 3, .c 1307, .p pv2 [pv2,pv3,pv321631], .c 3, .c 677, .c 661, .c 3, .c 7, .c 5, .c 3, .c 773,
  .c 349, .c 3, .c 5, .c 7, .c 3, .c 1621, .c 11, .c 3, .c 23, .c 13, .c 3, .c 139, .c 5, .c 3,
  .c 53, .p pv2 [pv2,pv3,pv5,pv64327], .c 3, .c 5, .c 251, .c 3, .c 71, .c 683, .c 3, .c 43, .c 7,
  .c 3, .c 727, .c 5, .c 3, .p pv3 [pv2,pv13,pv4639], .c 1531, .c 3, .c 5, .c 127, .c 3, .c 13,
  .c 17, .c 3, .c 7, .c 11, .c 3, .p pv5 [pv2,pv53,pv9103], .c 5, .c 3, .c 19, .c 7, .c 3, .c 5,
  .c 13, .c 3, .c 11, .p pv2 [pv2,pv3,pv37,pv8693], .c 3, .c 17, .c 23, .c 3, .c 79, .c 5, .c 3,
  .c 7, .c 151, .c 3, .c 5, .c 19, .c 3, .c 59, .c 7, .c 3, .c 97, .c 37, .c 3, .c 409, .c 5,
  .c 3, .c 13, .c 113, .c 3, .c 5, .c 509, .c 3, .c 7, .c 1063, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv7,pv10211], .c 3, .c 659, .c 5, .c 3, .p pv3 [pv2,pv11,pv23,pv1907],
  .p pv2 [pv2,pv3,pv5,pv128659], .c 3, .c 5, .c 179, .c 3, .c 41,
  .p pv5 [pv2,pv3,pv17,pv79,pv479], .c 3, .p pv5 [pv2,pv7,pv275699],
  .p pv2 [pv2,pv3,pv263,pv1223], .c 3, .c 7, .c 5, .c 3, .c 17, .c 11,
]
private theorem h0471c29 : checkBlock 3859547 128 b0471c29 = true := by
  decide +kernel

private def b0471c30 : List Row := [
  .c 3, .c 5, .c 7, .c 3, .c 107, .c 29, .c 3, .c 13, .p pv2 [pv2,pv3,pv643303], .c 3, .c 11,
  .c 5, .c 3, .p pv2 [pv2,pv7,pv47,pv419], .c 19, .c 3, .c 5, .c 23, .c 3, .c 31, .c 13, .c 3,
  .p pv5 [pv2,pv1929923], .c 7, .c 3, .c 271, .c 5, .c 3, .c 443, .c 79, .c 3, .c 5, .c 11, .c 3,
  .c 29, .c 1871, .c 3, .c 7, .p pv3 [pv2,pv3,pv11,pv233,pv251], .c 3, .c 23, .c 5, .c 3, .c 11,
  .c 7, .c 3, .c 5, .c 61, .c 3, .c 17, .c 31, .c 3, .c 19, .c 1613, .c 3, .c 607, .c 5, .c 3,
  .c 7, .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv19,pv691], .c 3, .p pv2 [pv2,pv5,pv89,pv4337],
  .c 7, .c 3, .c 53, .p pv3 [pv2,pv3,pv43,pv4987], .c 3, .c 757, .c 5, .c 3, .c 1597, .c 37, .c 3,
  .c 5, .c 59, .c 3, .c 7, .p pv2 [pv2,pv3,pv487,pv1321], .c 3, .c 113, .c 17, .c 3, .c 13, .c 5,
  .c 3, .p pv2 [pv2,pv733,pv2633], .c 43, .c 3, .c 5, .c 29, .c 3, .c 1609,
  .p pv5 [pv2,pv3,pv53611], .c 3, .c 1163, .c 11, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv482501],
  .c 1601, .c 3, .c 5, .c 7, .c 3, .c 11, .p pv3 [pv2,pv3,pv503,pv1279], .c 3, .c 31,
  .p pv2 [pv2,pv3,pv103,pv347], .c 3, .p pv3 [pv2,pv11,pv5483], .c 5, .c 3,
  .p pv7 [pv2,pv7,pv13,pv127,pv167], .p pv7 [pv2,pv3,pv5,pv19,pv1693], .c 3, .c 5, .c 389, .c 3,
  .c 13, .c 449, .c 3, .c 71,
]
private theorem h0471c30 : checkBlock 3859803 128 b0471c30 = true := by
  decide +kernel

private def b0471c31 : List Row := [
  .c 7, .c 3, .c 47, .c 5, .c 3, .c 1931, .c 17, .c 3, .c 5, .c 13, .c 3, .c 83,
  .p pv2 [pv2,pv3,pv71483], .c 3, .c 7, .c 31, .c 3, .p pv2 [pv2,pv965023], .c 5, .c 3, .c 37,
  .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv367,pv1753], .c 3, .c 233, .c 23, .c 3,
  .p pv2 [pv2,pv13,pv19,pv3907], .c 101, .c 3, .p pv2 [pv2,pv7,pv17,pv331], .c 5, .c 3, .c 7,
  .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv23,pv37], .c 3, .c 61, .c 7, .c 3,
  .p pv2 [pv2,pv1930073], .c 53, .c 3, .c 11, .c 5, .c 3, .c 23, .c 29, .c 3, .c 5, .c 73, .c 3,
  .c 7, .c 17, .c 3, .c 79, .c 547, .c 3, .p pv5 [pv2,pv23,pv31,pv2707], .c 5, .c 3,
  .p pv2 [pv2,pv965047], .c 41, .c 3, .c 5, .c 11, .c 3, .c 1933, .c 1721, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv11,pv2437], .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv19 [pv2,pv3,pv5,pv7,pv13,pv101], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv11,pv19,pv1847],
  .c 13, .c 3, .p pv2 [pv2,pv965059], .c 43, .c 3, .c 1327, .c 5, .c 3, .c 19, .c 23, .c 3, .c 5,
  .c 383, .c 3, .c 479, .c 11, .c 3, .p pv2 [pv2,pv1930133], .c 7, .c 3, .c 41, .c 5, .c 3,
  .c 457, .p pv7 [pv2,pv3,pv5,pv10723], .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv7,pv55147],
  .p pv2 [pv2,pv3,pv17,pv127,pv149], .c 3, .c 7, .p pv7 [pv2,pv3,pv13,pv47], .c 3,
  .p pv5 [pv2,pv443,pv4357], .c 5, .c 3, .c 17, .c 7, .c 3,
]
private theorem h0471c31 : checkBlock 3860059 128 b0471c31 = true := by
  decide +kernel

def rows0471 : List Row :=
  b0471c00 ++ b0471c01 ++ b0471c02 ++ b0471c03 ++ b0471c04 ++ b0471c05 ++ b0471c06 ++ b0471c07 ++
  b0471c08 ++ b0471c09 ++ b0471c10 ++ b0471c11 ++ b0471c12 ++ b0471c13 ++ b0471c14 ++ b0471c15 ++
  b0471c16 ++ b0471c17 ++ b0471c18 ++ b0471c19 ++ b0471c20 ++ b0471c21 ++ b0471c22 ++ b0471c23 ++
  b0471c24 ++ b0471c25 ++ b0471c26 ++ b0471c27 ++ b0471c28 ++ b0471c29 ++ b0471c30 ++ b0471c31

theorem checked0471 : checkBlock 3852123 4096 rows0471 = true :=
  checkBlock_append h0471c00 (
    checkBlock_append h0471c01 (
    checkBlock_append h0471c02 (
    checkBlock_append h0471c03 (
    checkBlock_append h0471c04 (
    checkBlock_append h0471c05 (
    checkBlock_append h0471c06 (
    checkBlock_append h0471c07 (
    checkBlock_append h0471c08 (
    checkBlock_append h0471c09 (
    checkBlock_append h0471c10 (
    checkBlock_append h0471c11 (
    checkBlock_append h0471c12 (
    checkBlock_append h0471c13 (
    checkBlock_append h0471c14 (
    checkBlock_append h0471c15 (
    checkBlock_append h0471c16 (
    checkBlock_append h0471c17 (
    checkBlock_append h0471c18 (
    checkBlock_append h0471c19 (
    checkBlock_append h0471c20 (
    checkBlock_append h0471c21 (
    checkBlock_append h0471c22 (
    checkBlock_append h0471c23 (
    checkBlock_append h0471c24 (
    checkBlock_append h0471c25 (
    checkBlock_append h0471c26 (
    checkBlock_append h0471c27 (
    checkBlock_append h0471c28 (
    checkBlock_append h0471c29 (
    checkBlock_append h0471c30 (
    h0471c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
