/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks06/Block0480
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks06/Block0480.checked0480
   digest: Kernel proof of checker success on extended consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table033
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table039
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table042
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table047
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table060
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table069
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table082
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table098
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table122
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table157
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table158
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table159
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table160
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table162
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table163
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table167
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table171
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table175
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table182
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table190
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table203
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table223
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table224
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables03.Table248

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0480c00 : List Row := [
  .c 3, .c 109, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 11, .c 3, .c 31, .c 7, .c 3,
  .p pv2 [pv2,pv461,pv2129], .c 89, .c 3, .c 13, .c 5, .c 3, .c 11, .c 251, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv12583], .c 3, .c 7, .p pv5 [pv2,pv3,pv31,pv21107], .c 3, .c 293, .c 13,
  .c 3, .c 19, .c 5, .c 3, .c 59, .c 277, .c 3, .c 5, .p pv3 [pv2,pv3,pv218107], .c 3, .c 1291,
  .c 11, .c 3, .c 107, .c 23, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv13,pv103,pv733], .c 19, .c 3,
  .c 5, .c 7, .c 3, .c 13, .c 17, .c 3, .p pv11 [pv2,pv11,pv16223], .p pv13 [pv2,pv3,pv89,pv919],
  .c 3, .p pv2 [pv2,pv981493], .c 5, .c 3, .c 431, .p pv2 [pv2,pv3,pv5,pv17,pv1283], .c 3, .c 5,
  .c 13, .c 3, .c 29, .p pv5 [pv2,pv3,pv7,pv23369], .c 3, .c 17, .c 7, .c 3, .c 167, .c 5, .c 3,
  .c 137, .c 433, .c 3, .c 5, .p pv5 [pv2,pv3,pv71], .c 3, .c 11, .p pv3 [pv2,pv3,pv797,pv821],
  .c 3, .c 7, .c 43, .c 3, .c 37, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv19,pv34439], .c 3, .c 47, .c 239, .c 3, .c 31, .c 283, .c 3, .c 79, .c 5,
  .c 3, .c 7, .c 109, .c 3, .c 5, .c 23, .c 3, .c 53, .c 7, .c 3, .c 11,
  .p pv17 [pv2,pv3,pv31,pv1759], .c 3, .p pv2 [pv2,pv981523], .c 5, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv5,pv23,pv569], .c 3, .c 5,
]
private theorem h0480c00 : checkBlock 3925851 128 b0480c00 = true := by
  decide +kernel

private def b0480c01 : List Row := [
  .c 29, .c 3, .c 7, .p pv17 [pv2,pv3,pv40897], .c 3, .c 13, .c 31, .c 3, .c 23, .c 5, .c 3,
  .p pv3 [pv2,pv245383], .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv29,pv5641], .c 3, .c 19, .c 13,
  .c 3, .p pv2 [pv2,pv7,pv23,pv89,pv137], .c 83, .c 3, .c 7, .c 5, .c 3, .c 73, .c 523, .c 3,
  .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv167,pv2351], .c 101, .c 3, .c 389, .c 19, .c 3, .c 1381,
  .c 5, .c 3, .c 257, .c 401, .c 3, .c 5, .c 11, .c 3, .c 17, .p pv3 [pv2,pv3,pv7,pv93481], .c 3,
  .c 1019, .c 7, .c 3, .p pv2 [pv2,pv31,pv31663], .c 5, .c 3, .c 11, .c 13, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv654371], .c 3, .p pv7 [pv2,pv5,pv7,pv11,pv5099], .p pv5 [pv2,pv3,pv73,pv83],
  .c 3, .c 7, .c 47, .c 3, .c 31, .c 5, .c 3, .p pv3 [pv2,pv271,pv1811], .c 7, .c 3, .c 5, .c 103,
  .c 3, .c 23, .c 11, .c 3, .c 67, .c 17, .c 3, .c 13, .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .c 43,
  .c 3, .p pv17 [pv2,pv5,pv392629], .c 7, .c 3, .p pv3 [pv2,pv11,pv44617], .c 13, .c 3, .c 17,
  .c 5, .c 3, .c 443, .p pv3 [pv2,pv3,pv5,pv29,pv4513], .c 3, .c 5, .c 619, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv331,pv659], .c 3, .c 263, .c 11, .c 3, .c 47, .c 5, .c 3, .c 29,
  .p pv2 [pv2,pv3,pv5,pv11,pv661], .c 3, .c 5, .p pv17 [pv2,pv3,pv53,pv12347], .c 3, .c 11, .c 23,
  .c 3, .p pv2 [pv2,pv7,pv140227], .c 853, .c 3,
]
private theorem h0480c01 : checkBlock 3926107 128 b0480c01 = true := by
  decide +kernel

private def b0480c02 : List Row := [
  .c 7, .c 5, .c 3, .c 19, .c 17, .c 3, .c 5, .c 7, .c 3, .c 1039, .c 359, .c 3, .c 61, .c 1699,
  .c 3, .c 251, .c 5, .c 3, .c 23, .c 67, .c 3, .c 5, .c 19, .c 3, .c 113, .c 89, .c 3, .c 11,
  .c 7, .c 3, .p pv5 [pv2,pv17,pv23,pv5021], .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv43627],
  .c 3, .c 5, .c 1069, .c 3, .p pv3 [pv2,pv5,pv7,pv37,pv379], .c 587, .c 3, .c 7, .c 419, .c 3,
  .c 151, .c 5, .c 3, .c 43, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv218137], .c 3,
  .p pv23 [pv2,pv5,pv392647], .c 17, .c 3, .c 37, .p pv3 [pv2,pv3,pv654413], .c 3, .c 11, .c 5,
  .c 3, .c 7, .c 23, .c 3, .c 5, .p pv19 [pv2,pv3,pv7,pv5843], .c 3, .p pv2 [pv2,pv5,pv7853],
  .c 7, .c 3, .c 13, .c 59, .c 3, .c 29, .c 5, .c 3, .c 271, .c 19, .c 3, .c 5, .c 11, .c 3, .c 7,
  .c 13, .c 3, .c 23, .p pv2 [pv2,pv3,pv7,pv11,pv2833], .c 3, .p pv5 [pv2,pv29,pv67699], .c 5,
  .c 3, .c 11, .c 37, .c 3, .c 5, .c 137, .c 3, .p pv3 [pv2,pv5,pv11,pv23,pv97], .c 977, .c 3,
  .c 683, .p pv37 [pv2,pv3,pv47,pv59], .c 3, .c 7, .c 5, .c 3, .c 107, .c 173, .c 3, .c 5, .c 7,
  .c 3, .c 89, .c 11, .c 3, .c 19, .c 349, .c 3, .p pv2 [pv2,pv67,pv29303], .c 5, .c 3, .c 17,
  .c 13, .c 3, .c 5, .c 881,
]
private theorem h0480c02 : checkBlock 3926363 128 b0480c02 = true := by
  decide +kernel

private def b0480c03 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv196331], .p pv3 [pv2,pv3,pv7,pv93491], .c 3, .c 59, .c 7, .c 3,
  .p pv3 [pv2,pv490829], .c 5, .c 3, .p pv13 [pv2,pv1963319], .p pv7 [pv2,pv3,pv5,pv16361], .c 3,
  .c 5, .c 83, .c 3, .p pv7 [pv2,pv5,pv7,pv13,pv863], .c 331, .c 3, .c 7, .c 11, .c 3, .c 13,
  .c 5, .c 3, .c 67, .c 7, .c 3, .c 5, .c 17, .c 3, .c 11, .c 607, .c 3, .c 29, .c 13, .c 3,
  .c 41, .c 5, .c 3, .c 7, .c 883, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv93493], .c 3, .c 17, .c 7,
  .c 3, .c 43, .p pv3 [pv2,pv3,pv24239], .c 3, .c 179, .c 5, .c 3, .p pv3 [pv2,pv13,pv17,pv2221],
  .p pv2 [pv2,pv3,pv5,pv19,pv83], .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv37,pv67], .c 3, .c 7, .c 73,
  .c 3, .c 11, .c 19, .c 3, .c 61, .c 5, .c 3, .p pv7 [pv2,pv11,pv178489], .c 1061, .c 3, .c 5,
  .c 13, .c 3, .p pv2 [pv2,pv5,pv31,pv53,pv239], .c 37, .c 3, .c 521, .c 17, .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv981697], .c 11, .c 3, .c 5, .c 7, .c 3, .c 31, .c 29, .c 3, .c 223, .c 409,
  .c 3, .c 11, .c 5, .c 3, .c 13, .c 1259, .c 3, .c 5, .p pv2 [pv2,pv3,pv72719], .c 3, .c 137,
  .c 163, .c 3, .c 307, .c 7, .c 3, .c 821, .c 5, .c 3, .p pv3 [pv2,pv61357], .c 97, .c 3, .c 5,
  .c 11, .c 3, .c 29, .c 19, .c 3, .c 7, .p pv13 [pv2,pv3,pv11,pv71,pv419], .c 3, .c 227,
]
private theorem h0480c03 : checkBlock 3926619 128 b0480c03 = true := by
  decide +kernel

private def b0480c04 : List Row := [
  .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 919, .c 3, .p pv2 [pv2,pv5,pv11,pv29,pv1231],
  .p pv2 [pv2,pv3,pv229,pv1429], .c 3, .c 13, .c 383, .c 3, .p pv5 [pv2,pv7,pv179,pv1567], .c 5,
  .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv13,pv10069], .c 3, .c 5, .p pv29 [pv2,pv3,pv7,pv15583], .c 3,
  .c 37, .c 7, .c 3, .c 173, .c 53, .c 3, .p pv2 [pv2,pv17,pv43,pv79], .c 5, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv5,pv65449], .c 3, .c 5, .c 89, .c 3, .c 7, .c 691, .c 3,
  .p pv2 [pv2,pv11,pv31,pv2879], .p pv7 [pv2,pv3,pv7,pv19,pv37], .c 3,
  .p pv2 [pv2,pv13,pv73,pv2069], .c 5, .c 3, .c 1109, .c 193, .c 3, .c 5, .c 19, .c 3, .c 59,
  .c 17, .c 3, .c 31, .c 11, .c 3, .c 7, .c 5, .c 3, .c 347, .c 13, .c 3, .c 5, .c 7, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv327251], .c 3, .c 17, .p pv2 [pv2,pv3,pv31,pv43,pv491], .c 3, .c 1597, .c 5,
  .c 3, .c 277, .c 1439, .c 3, .c 5, .p pv5 [pv2,pv3,pv89,pv3677], .c 3, .c 157, .c 23, .c 3,
  .p pv5 [pv2,pv739,pv2657], .c 7, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv61,pv32189], .c 43,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv13,pv23,pv199], .c 3, .c 67, .p pv13 [pv2,pv3,pv19,pv2153],
  .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv101,pv19441], .c 5, .c 3, .c 23, .c 7, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv18181], .c 3, .c 359, .c 41, .c 3, .p pv2 [pv2,pv37,pv53069],
  .p pv2 [pv2,pv3,pv73,pv4483], .c 3, .p pv3 [pv2,pv7,pv23,pv3049], .c 5, .c 3, .c 7, .c 11, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv7,pv93503], .c 3,
]
private theorem h0480c04 : checkBlock 3926875 128 b0480c04 = true := by
  decide +kernel

private def b0480c05 : List Row := [
  .c 13, .c 7, .c 3, .p pv3 [pv2,pv17,pv7219], .p pv2 [pv2,pv3,pv67,pv9769], .c 3, .c 11, .c 5,
  .c 3, .c 1093, .c 29, .c 3, .c 5, .c 13, .c 3, .c 7, .c 1637, .c 3, .c 19, .c 79, .c 3, .c 31,
  .c 5, .c 3, .c 47, .c 23, .c 3, .c 5, .c 11, .c 3, .c 283, .c 149, .c 3,
  .p pv3 [pv2,pv7,pv13,pv10789], .p pv3 [pv2,pv3,pv11,pv157,pv379], .c 3, .c 7, .c 5, .c 3, .c 11,
  .c 313, .c 3, .c 5, .c 7, .c 3, .c 17, .c 71, .c 3, .c 23, .c 1871, .c 3, .c 43, .c 5, .c 3,
  .c 97, .c 61, .c 3, .c 5, .c 53, .c 3, .p pv23 [pv2,pv5,pv23,pv683], .c 11, .c 3,
  .p pv3 [pv2,pv281,pv1747], .c 7, .c 3, .c 1283, .c 5, .c 3, .p pv2 [pv2,pv981817],
  .p pv3 [pv2,pv3,pv5,pv109,pv1201], .c 3, .c 5, .c 677, .c 3, .c 19, .c 769, .c 3, .c 7, .c 17,
  .c 3, .p pv2 [pv2,pv981823], .c 5, .c 3, .p pv2 [pv2,pv521,pv3769], .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv17,pv139,pv277], .c 3, .c 83, .c 13, .c 3, .c 373, .c 11, .c 3, .c 17, .c 5,
  .c 3, .c 7, .c 1087, .c 3, .c 5, .p pv29 [pv2,pv3,pv7,pv97,pv241], .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv347,pv5659], .c 41, .c 3, .c 53, .c 5, .c 3, .c 31, .p pv23 [pv2,pv3,pv5,pv4091],
  .c 3, .c 5, .c 47, .c 3, .c 7, .p pv2 [pv2,pv3,pv293,pv1117], .c 3, .p pv3 [pv2,pv19,pv12919],
  .c 109, .c 3, .c 29, .c 5,
]
private theorem h0480c05 : checkBlock 3927131 128 b0480c05 = true := by
  decide +kernel

private def b0480c06 : List Row := [
  .c 3, .c 1913, .c 13, .c 3, .c 5, .c 251, .c 3, .c 1013, .c 449, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv17,pv4813], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv11,pv16229], .c 31, .c 3,
  .c 5, .c 7, .c 3, .c 41, .c 19, .c 3, .p pv2 [pv2,pv71,pv13829], .c 37, .c 3, .c 13, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv43,pv233], .c 11, .c 3, .c 5, .c 23, .c 3, .c 47,
  .p pv11 [pv2,pv3,pv7,pv11,pv8501], .c 3, .p pv2 [pv2,pv1033,pv1901], .c 7, .c 3, .c 11, .c 5,
  .c 3, .p pv17 [pv2,pv353,pv5563], .c 89, .c 3, .c 5, .c 239, .c 3, .c 43, .c 17, .c 3, .c 7,
  .c 29, .c 3, .c 23, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 11, .c 3, .c 13,
  .p pv5 [pv2,pv3,pv654587], .c 3, .c 17, .p pv13 [pv2,pv3,pv11,pv19,pv29], .c 3, .c 191, .c 5,
  .c 3, .c 7, .c 113, .c 3, .c 5, .c 13, .c 3, .p pv11 [pv2,pv5,pv11,pv37,pv193], .c 7, .c 3,
  .c 29, .p pv3 [pv2,pv3,pv654593], .c 3, .p pv2 [pv2,pv1963781], .c 5, .c 3, .c 1609, .c 59,
  .c 3, .c 5, .c 43, .c 3, .c 7, .c 11, .c 3, .c 37, .c 197, .c 3, .p pv3 [pv2,pv490949], .c 5,
  .c 3, .c 13, .p pv11 [pv2,pv3,pv5,pv1091], .c 3, .c 5, .c 31, .c 3, .p pv2 [pv2,pv5,pv392761],
  .c 773, .c 3, .c 587, .c 73, .c 3, .c 7, .c 5, .c 3, .c 17, .c 857, .c 3, .c 5, .c 7, .c 3,
  .c 23,
]
private theorem h0480c06 : checkBlock 3927387 128 b0480c06 = true := by
  decide +kernel

private def b0480c07 : List Row := [
  .c 79, .c 3, .p pv5 [pv2,pv17,pv331,pv349], .c 11, .c 3, .c 137, .c 5, .c 3, .c 89, .c 19, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv654611], .c 3, .c 11, .c 29, .c 3, .c 13, .c 7, .c 3, .c 1621, .c 5,
  .c 3, .c 59, .p pv2 [pv2,pv3,pv5,pv13,pv373], .c 3, .c 5, .c 17, .c 3,
  .p pv2 [pv2,pv5,pv7,pv31,pv181], .c 13, .c 3, .c 7, .p pv2 [pv2,pv3,pv109103], .c 3,
  .p pv3 [pv2,pv122741], .c 5, .c 3, .c 1301, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv83,pv239],
  .c 3, .c 17, .c 23, .c 3, .c 11, .p pv23 [pv2,pv3,pv654623], .c 3, .c 47, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv5237], .c 3, .c 5, .c 283, .c 3, .p pv3 [pv2,pv5,pv29,pv1693], .c 7, .c 3,
  .c 113, .p pv7 [pv2,pv3,pv13,pv12589], .c 3, .c 131, .c 5, .c 3, .c 23, .c 11, .c 3, .c 5,
  .c 1021, .c 3, .c 7, .c 31, .c 3, .c 179, .c 17, .c 3, .c 11, .c 5, .c 3, .c 37, .c 163, .c 3,
  .c 5, .c 1523, .c 3, .c 97, .p pv3 [pv2,pv3,pv617,pv1061], .c 3, .p pv2 [pv2,pv7,pv157,pv1787],
  .p pv2 [pv2,pv3,pv327319], .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv73,pv26903], .c 41, .c 3,
  .c 5, .c 7, .c 3, .c 19, .c 1433, .c 3, .c 1451, .c 13, .c 3, .c 107, .c 5, .c 3, .c 11, .c 23,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv29,pv11287], .c 3, .c 181, .c 37, .c 3, .p pv5 [pv2,pv31,pv63353],
  .c 7, .c 3, .p pv2 [pv2,pv83,pv11831], .c 5, .c 3,
]
private theorem h0480c07 : checkBlock 3927643 128 b0480c07 = true := by
  decide +kernel

private def b0480c08 : List Row := [
  .c 251, .c 17, .c 3, .c 5, .p pv3 [pv2,pv3,pv72739], .c 3, .c 13, .c 11, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv17,pv97,pv397], .c 3, .c 41, .c 5, .c 3, .p pv3 [pv2,pv490991], .c 7, .c 3,
  .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv23,pv8539], .p pv13 [pv2,pv3,pv67,pv3257], .c 3, .c 317,
  .c 1783, .c 3, .c 509, .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv3637], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv93523], .c 3, .p pv2 [pv2,pv5,pv107,pv3671], .c 7, .c 3, .c 331, .c 11,
  .c 3, .c 127, .c 5, .c 3, .c 13, .c 101, .c 3, .c 5, .p pv2 [pv2,pv3,pv109111], .c 3, .c 7,
  .c 17, .c 3, .c 43, .c 23, .c 3, .p pv2 [pv2,pv11,pv89273], .c 5, .c 3, .p pv2 [pv2,pv1964009],
  .c 29, .c 3, .c 5, .p pv3 [pv2,pv3,pv654671], .c 3, .c 37, .c 109, .c 3, .c 17,
  .p pv11 [pv2,pv3,pv79,pv8287], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv383,pv641], .c 563, .c 3,
  .c 5, .c 7, .c 3, .c 199, .c 373, .c 3, .c 11, .p pv2 [pv2,pv3,pv37,pv983], .c 3, .c 757, .c 5,
  .c 3, .c 19, .c 443, .c 3, .c 5, .c 41, .c 3, .p pv2 [pv2,pv5,pv392809], .c 13, .c 3,
  .p pv3 [pv2,pv122753], .c 7, .c 3, .c 31, .c 5, .c 3, .p pv2 [pv2,pv29,pv33863], .c 11, .c 3,
  .c 5, .c 19, .c 3, .c 1231, .p pv5 [pv2,pv3,pv11,pv17,pv389], .c 3, .c 7, .c 193, .c 3, .c 11,
  .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 23, .c 3, .p pv13 [pv2,pv5,pv251,pv313], .c 1373,
]
private theorem h0480c08 : checkBlock 3927899 128 b0480c08 = true := by
  decide +kernel

private def b0480c09 : List Row := [
  .c 3, .p pv2 [pv2,pv17,pv61,pv947], .p pv3 [pv2,pv3,pv13,pv16787], .c 3,
  .p pv2 [pv2,pv7,pv280583], .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 11, .c 3, .c 461, .c 7, .c 3,
  .c 211, .p pv2 [pv2,pv3,pv11,pv29759], .c 3, .c 19, .c 5, .c 3, .c 11, .c 53, .c 3, .c 5, .c 17,
  .c 3, .c 7, .c 47, .c 3, .c 61, .c 113, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv982057], .c 19,
  .c 3, .c 5, .c 127, .c 3, .c 17, .c 11, .c 3, .p pv5 [pv2,pv7,pv280589], .c 13, .c 3, .c 7,
  .c 5, .c 3, .p pv2 [pv2,pv17,pv31,pv3727], .p pv2 [pv2,pv3,pv5,pv7,pv47,pv199], .c 3, .c 5,
  .c 7, .c 3, .c 1153, .p pv7 [pv2,pv3,pv81839], .c 3, .c 67, .c 59, .c 3,
  .p pv2 [pv2,pv29,pv89,pv761], .c 5, .c 3, .c 31, .c 107, .c 3, .c 5, .c 131, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv7,pv31177], .c 3, .c 19, .c 7, .c 3, .p pv3 [pv2,pv491039], .c 5, .c 3,
  .p pv13 [pv2,pv1964159], .c 1429, .c 3, .c 5, .c 13, .c 3, .c 11, .c 41, .c 3, .c 7, .c 61,
  .c 3, .c 17, .c 5, .c 3, .c 73, .c 7, .c 3, .c 5, .c 1097, .c 3,
  .p pv3 [pv2,pv5,pv17,pv53,pv109], .c 1151, .c 3, .p pv5 [pv2,pv13,pv151091], .c 29, .c 3,
  .p pv2 [pv2,pv7,pv307,pv457], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv233,pv281], .c 3, .c 5,
  .c 347, .c 3, .p pv17 [pv2,pv5,pv83,pv4733], .c 7, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv29,pv107,pv211], .c 3, .c 97, .c 5, .c 3, .c 337,
]
private theorem h0480c09 : checkBlock 3928155 128 b0480c09 = true := by
  decide +kernel

private def b0480c10 : List Row := [
  .c 17, .c 3, .c 5, .p pv7 [pv2,pv3,pv151,pv271], .c 3, .c 7, .c 23, .c 3, .c 29,
  .p pv2 [pv2,pv3,pv7,pv17,pv131], .c 3, .c 79, .c 5, .c 3, .c 617, .c 11, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv23,pv3163], .c 3, .p pv2 [pv2,pv5,pv78569], .p pv5 [pv2,pv3,pv11,pv29761],
  .c 3, .c 13, .c 19, .c 3, .c 7, .c 5, .c 3, .c 23, .c 1201, .c 3, .c 5, .c 7, .c 3, .c 751,
  .c 13, .c 3, .p pv5 [pv2,pv1964243], .c 1117, .c 3, .p pv2 [pv2,pv23,pv42701], .c 5, .c 3,
  .c 1033, .c 71, .c 3, .c 5, .c 11, .c 3, .c 389, .c 17, .c 3, .c 977, .c 7, .c 3, .c 43, .c 5,
  .c 3, .c 11, .c 1427, .c 3, .c 5, .c 31, .c 3, .c 241, .c 29, .c 3, .c 7, .c 37, .c 3,
  .p pv3 [pv2,pv311,pv1579], .c 5, .c 3, .c 131, .c 7, .c 3, .c 5, .c 151, .c 3, .c 1861, .c 11,
  .c 3, .p pv3 [pv2,pv7673], .c 41, .c 3, .c 61, .c 5, .c 3, .c 7, .c 79, .c 3, .c 5, .c 97, .c 3,
  .c 29, .c 7, .c 3, .c 23, .c 43, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv127,pv15467],
  .p pv2 [pv2,pv3,pv5,pv41,pv1597], .c 3, .c 5, .c 499, .c 3, .c 7, .c 59, .c 3,
  .p pv2 [pv2,pv47,pv20897], .c 11, .c 3, .c 71, .c 5, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv5,pv11,pv2381], .c 3, .c 5, .c 173, .c 3, .c 11, .p pv3 [pv2,pv3,pv24251],
  .c 3,
]
private theorem h0480c10 : checkBlock 3928411 128 b0480c10 = true := by
  decide +kernel

private def b0480c11 : List Row := [
  .p pv2 [pv2,pv7,pv17,pv971], .p pv2 [pv2,pv3,pv19,pv17231], .c 3, .c 7, .c 5, .c 3, .c 67,
  .p pv23 [pv2,pv3,pv5,pv7,pv1559], .c 3, .c 5, .c 7, .c 3, .c 13, .c 349, .c 3, .c 37, .c 23,
  .c 3, .p pv5 [pv2,pv41,pv47911], .c 5, .c 3, .p pv3 [pv2,pv7,pv193,pv727], .c 1733, .c 3, .c 5,
  .c 13, .c 3, .p pv3 [pv2,pv5,pv49109], .c 31, .c 3, .c 11, .c 7, .c 3, .p pv2 [pv2,pv982183],
  .c 5, .c 3, .p pv2 [pv2,pv11,pv43,pv4153], .c 929, .c 3, .c 5, .c 1657, .c 3, .c 17,
  .p pv5 [pv2,pv3,pv27283], .c 3, .c 7, .c 257, .c 3, .c 19, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .c 47, .c 3, .c 43, .p pv3 [pv2,pv3,pv11,pv13,pv19,pv241], .c 3, .c 73, .c 163, .c 3, .c 11,
  .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .p pv7 [pv2,pv3,pv7,pv31181], .c 3,
  .p pv2 [pv2,pv5,pv59,pv6659], .c 7, .c 3, .p pv3 [pv2,pv31,pv89], .c 17, .c 3,
  .p pv5 [pv2,pv1964411], .c 5, .c 3, .c 457, .p pv3 [pv2,pv3,pv5,pv173,pv757], .c 3, .c 5, .c 11,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv167,pv1307], .c 3, .c 13, .p pv19 [pv2,pv3,pv7,pv11,pv1063], .c 3,
  .c 17, .c 5, .c 3, .c 11, .c 521, .c 3, .c 5, .c 43, .c 3, .c 47, .c 13, .c 3, .c 19, .c 1499,
  .c 3, .c 7, .c 5, .c 3, .c 283, .c 29, .c 3, .c 5, .c 7, .c 3, .c 193, .c 11, .c 3, .c 41,
  .c 31, .c 3, .p pv3 [pv2,pv13,pv1453], .c 5, .c 3, .c 37, .c 17,
]
private theorem h0480c11 : checkBlock 3928667 128 b0480c11 = true := by
  decide +kernel

private def b0480c12 : List Row := [
  .c 3, .c 5, .c 71, .c 3, .p pv2 [pv2,pv5,pv392893], .c 73, .c 3, .p pv3 [pv2,pv11,pv44647],
  .c 7, .c 3, .c 53, .c 5, .c 3, .c 29, .c 13, .c 3, .c 5, .c 263, .c 3,
  .p pv3 [pv2,pv5,pv7,pv877], .c 419, .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv17,pv19,pv3041],
  .c 5, .c 3, .p pv2 [pv2,pv29,pv67741], .c 7, .c 3, .c 5, .c 59, .c 3, .c 11, .c 37, .c 3,
  .p pv2 [pv2,pv43,pv53,pv431], .c 127, .c 3, .c 13, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv19,pv61,pv113], .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv13,pv257], .c 3, .c 23,
  .c 7, .c 3, .p pv2 [pv2,pv691,pv2843], .c 13, .c 3, .c 31, .c 5, .c 3, .c 43, .c 1471, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv11,pv59,pv1009], .c 3, .c 7, .p pv2 [pv2,pv3,pv327421], .c 3, .c 11,
  .c 47, .c 3, .p pv5 [pv2,pv1964531], .c 5, .c 3, .c 71, .c 41, .c 3, .c 5, .c 827, .c 3, .c 13,
  .c 89, .c 3, .c 1459, .c 313, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv1964549], .c 11, .c 3, .c 5,
  .c 7, .c 3, .c 607, .c 23, .c 3, .p pv2 [pv2,pv487,pv2017], .c 1667, .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv70163], .p pv2 [pv2,pv3,pv5,pv149,pv293], .c 3, .c 5, .c 83, .c 3, .c 37,
  .c 19, .c 3, .c 107, .c 7, .c 3, .c 41, .c 5, .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv137,pv239],
  .c 3, .c 5, .c 11, .c 3, .c 151, .p pv7 [pv2,pv3,pv13,pv89,pv283], .c 3, .c 7,
]
private theorem h0480c12 : checkBlock 3928923 128 b0480c12 = true := by
  decide +kernel

private def b0480c13 : List Row := [
  .c 97, .c 3, .p pv5 [pv2,pv23,pv229,pv373], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 383, .c 3,
  .p pv3 [pv2,pv5,pv11,pv19,pv47], .c 101, .c 3, .c 1361, .p pv37 [pv2,pv3,pv53,pv3089], .c 3,
  .p pv2 [pv2,pv7,pv20047], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv83,pv263], .c 3, .c 5, .c 17,
  .c 3, .c 647, .c 7, .c 3, .c 13, .c 29, .c 3, .c 353, .c 5, .c 3, .p pv3 [pv2,pv122789], .c 23,
  .c 3, .c 5, .c 19, .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv11,pv178603],
  .p pv2 [pv2,pv3,pv7,pv29,pv1613], .c 3, .c 257, .c 5, .c 3, .c 149, .c 31, .c 3, .c 5, .c 193,
  .c 3, .p pv2 [pv2,pv5,pv392929], .c 307, .c 3, .c 23, .c 11, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv677,pv1451], .p pv3 [pv2,pv3,pv5,pv7,pv11], .c 3, .c 5, .c 7, .c 3, .c 11,
  .p pv13 [pv2,pv3,pv151,pv4337], .c 3, .p pv5 [pv2,pv29,pv37,pv1831], .c 17, .c 3, .c 19, .c 5,
  .c 3, .c 1259, .c 13, .c 3, .c 5, .c 103, .c 3, .p pv17 [pv2,pv5,pv89,pv883], .c 71, .c 3,
  .p pv2 [pv2,pv982339], .c 7, .c 3, .c 17, .c 5, .c 3, .p pv3 [pv2,pv491171], .c 19, .c 3, .c 5,
  .c 1123, .c 3, .c 79, .c 43, .c 3, .c 7, .c 23, .c 3, .c 13, .c 5, .c 3, .c 41, .c 7, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv13,pv50377], .c 3, .c 229, .c 29, .c 3, .p pv3 [pv2,pv67,pv7331], .c 13,
  .c 3, .c 293, .c 5, .c 3, .c 7, .c 11, .c 3,
]
private theorem h0480c13 : checkBlock 3929179 128 b0480c13 = true := by
  decide +kernel

private def b0480c14 : List Row := [
  .c 5, .c 37, .c 3, .c 163, .c 7, .c 3, .c 19, .p pv7 [pv2,pv3,pv17,pv9631], .c 3, .c 11, .c 5,
  .c 3, .c 59, .p pv29 [pv2,pv3,pv5,pv79,pv829], .c 3, .c 5, .c 31, .c 3, .c 7, .c 53, .c 3,
  .p pv2 [pv2,pv131,pv7499], .p pv11 [pv2,pv3,pv7,pv93559], .c 3, .c 67, .c 5, .c 3, .c 439,
  .c 787, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv29,pv271], .p pv3 [pv2,pv3,pv654917], .c 3,
  .c 127, .p pv7 [pv2,pv3,pv11,pv9923], .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv13 [pv2,pv3,pv5,pv7,pv2339], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv11,pv139,pv257],
  .c 17, .c 3, .p pv3 [pv2,pv13,pv4723], .c 79, .c 3, .p pv7 [pv2,pv19,pv103409], .c 5, .c 3,
  .c 13, .p pv3 [pv2,pv3,pv5,pv17,pv23,pv67], .c 3, .c 5, .p pv13 [pv2,pv3,pv327463], .c 3, .c 19,
  .c 11, .c 3, .c 17, .c 7, .c 3, .c 23, .c 5, .c 3, .c 53, .p pv2 [pv2,pv3,pv5,pv19,pv383], .c 3,
  .c 5, .c 29, .c 3, .c 31, .p pv5 [pv2,pv3,pv163733], .c 3, .c 7, .c 19, .c 3, .c 487, .c 5,
  .c 3, .p pv3 [pv2,pv491201], .c 7, .c 3, .c 5, .c 67, .c 3, .p pv2 [pv2,pv5,pv61,pv3221], .c 47,
  .c 3, .c 13, .c 11, .c 3, .p pv3 [pv2,pv7,pv53,pv331], .c 5, .c 3, .c 7, .c 43, .c 3, .c 5,
  .c 673, .c 3, .c 11, .c 7, .c 3, .p pv3 [pv2,pv19,pv103,pv251], .c 37, .c 3, .c 73, .c 5, .c 3,
  .c 17, .p pv3 [pv2,pv3,pv5,pv47,pv929], .c 3, .c 5, .c 167, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv107,pv6121], .c 3, .p pv5 [pv2,pv17,pv41,pv2819], .c 1051,
]
private theorem h0480c14 : checkBlock 3929435 128 b0480c14 = true := by
  decide +kernel

private def b0480c15 : List Row := [
  .c 3, .c 1217, .c 5, .c 3, .p pv2 [pv2,pv1964849], .c 1409, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv11,pv89,pv223], .c 3, .c 23, .c 19, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv13,pv83,pv607], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv11,pv2791], .c 13, .c 3,
  .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv349,pv563], .c 457, .c 3, .p pv2 [pv2,pv31,pv241,pv263],
  .p pv2 [pv2,pv3,pv327479], .c 3, .p pv3 [pv2,pv491219], .c 5, .c 3, .c 103, .c 11, .c 3, .c 5,
  .c 163, .c 3, .c 17, .p pv2 [pv2,pv3,pv7,pv11,pv4253], .c 3, .c 31, .c 7, .c 3, .c 11, .c 5,
  .c 3, .c 19, .c 53, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv311], .c 3, .c 83, .c 23, .c 3, .c 7,
  .c 13, .c 3, .c 43, .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .c 11, .c 3,
  .p pv11 [pv2,pv5,pv392983], .p pv5 [pv2,pv3,pv54581], .c 3, .c 877, .c 17, .c 3,
  .p pv2 [pv2,pv7,pv280703], .c 5, .c 3, .c 7, .c 379, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv17,pv43],
  .c 3, .c 13, .c 7, .c 3, .c 157, .c 131, .c 3, .c 17, .c 5, .c 3, .p pv7 [pv2,pv647,pv3037],
  .c 37, .c 3, .c 5, .c 13, .c 3, .c 7, .c 11, .c 3, .c 53, .c 43, .c 3, .c 19, .c 5, .c 3,
  .c 1439, .c 1063, .c 3, .c 5, .p pv2 [pv2,pv3,pv327493], .c 3, .c 71,
  .p pv2 [pv2,pv3,pv19,pv11491], .c 3, .p pv11 [pv2,pv7,pv11,pv13,pv151], .c 223, .c 3, .c 7,
  .c 5, .c 3, .c 13, .c 17, .c 3, .c 5,
]
private theorem h0480c15 : checkBlock 3929691 128 b0480c15 = true := by
  decide +kernel

private def b0480c16 : List Row := [
  .c 7, .c 3, .p pv7 [pv2,pv5,pv53,pv1483], .c 197, .c 3, .p pv2 [pv2,pv982489], .c 11, .c 3,
  .c 31, .c 5, .c 3, .p pv3 [pv2,pv7,pv35089], .c 641, .c 3, .c 5, .p pv5 [pv2,pv3,pv54583], .c 3,
  .c 11, .c 751, .c 3, .c 23, .c 7, .c 3, .c 29, .c 5, .c 3, .c 47, .p pv7 [pv2,pv3,pv5,pv131],
  .c 3, .c 5, .c 797, .c 3, .c 101, .c 79, .c 3, .c 7, .c 67, .c 3, .p pv5 [pv2,pv29,pv67759],
  .c 5, .c 3, .c 37, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv19,pv1567], .c 3, .c 173, .c 13,
  .c 3, .c 11, .c 59, .c 3, .c 181, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv17,pv3853], .c 3,
  .c 5, .c 389, .c 3, .c 43, .c 7, .c 3, .c 17, .c 23, .c 3, .c 569, .c 5, .c 3, .c 349, .c 11,
  .c 3, .c 5, .c 449, .c 3, .c 7, .c 37, .c 3, .c 311, .c 29, .c 3, .c 11, .c 5, .c 3, .c 137,
  .c 13, .c 3, .c 5, .c 821, .c 3, .c 19, .c 83, .c 3, .c 41, .p pv2 [pv2,pv3,pv29,pv7529], .c 3,
  .c 7, .c 5, .c 3, .c 31, .c 89, .c 3, .c 5, .c 7, .c 3, .c 1289, .c 1723, .c 3, .c 29, .c 19,
  .c 3, .c 13, .c 5, .c 3, .c 11, .c 157, .c 3, .c 5, .c 47, .c 3, .p pv13 [pv2,pv5,pv11,pv35729],
  .c 571, .c 3, .p pv3 [pv2,pv17,pv29,pv1993], .c 7, .c 3,
]
private theorem h0480c16 : checkBlock 3929947 128 b0480c16 = true := by
  decide +kernel

private def b0480c17 : List Row := [
  .c 367, .c 5, .c 3, .p pv3 [pv2,pv122819], .c 31, .c 3, .c 5, .c 23, .c 3,
  .p pv2 [pv2,pv5,pv7,pv67,pv419], .c 11, .c 3, .c 7, .p pv19 [pv2,pv3,pv151,pv241], .c 3, .c 883,
  .c 5, .c 3, .c 1559, .c 7, .c 3, .c 5, .c 17, .c 3, .c 13, .c 113, .c 3,
  .p pv3 [pv2,pv11,pv137,pv163], .p pv3 [pv2,pv3,pv655043], .c 3, .c 23, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv131009], .c 3, .c 5, .c 13, .c 3, .c 17, .c 7, .c 3, .c 67, .c 11, .c 3,
  .p pv2 [pv2,pv982573], .c 5, .c 3, .c 83, .c 41, .c 3, .c 5, .p pv2 [pv2,pv3,pv661,pv991], .c 3,
  .c 7, .c 271, .c 3, .p pv2 [pv2,pv13,pv75583], .p pv3 [pv2,pv3,pv7,pv31193], .c 3,
  .p pv5 [pv2,pv11,pv109,pv149], .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv131011], .c 3, .c 5,
  .p pv13 [pv2,pv3,pv4549], .c 3, .c 29, .c 97, .c 3, .c 71, .c 17, .c 3, .c 7, .c 5, .c 3, .c 19,
  .p pv13 [pv2,pv3,pv5,pv7,pv4679], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv29,pv13553],
  .p pv2 [pv2,pv3,pv43,pv2539], .c 3, .c 11, .c 151, .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv11,pv1823], .p pv3 [pv2,pv3,pv5,pv14557], .c 3, .c 5, .c 19, .c 3, .c 23,
  .c 59, .c 3, .c 13, .c 7, .c 3, .c 61, .c 5, .c 3, .c 163, .c 11, .c 3, .c 5, .c 53, .c 3,
  .c 107, .c 13, .c 3, .c 7, .p pv3 [pv2,pv3,pv349,pv1877], .c 3, .c 11, .c 5, .c 3, .c 199, .c 7,
  .c 3, .c 5, .c 29,
]
private theorem h0480c17 : checkBlock 3930203 128 b0480c17 = true := by
  decide +kernel

private def b0480c18 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv196523], .p pv5 [pv2,pv3,pv59,pv3701], .c 3, .p pv2 [pv2,pv73,pv26921],
  .c 47, .c 3, .c 19, .c 5, .c 3, .c 7, .p pv19 [pv2,pv3,pv5,pv53,pv103], .c 3, .c 5, .c 11, .c 3,
  .p pv11 [pv2,pv5,pv31,pv409], .c 7, .c 3, .p pv3 [pv2,pv30707], .c 631, .c 3, .c 139, .c 5,
  .c 3, .c 11, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv23,pv47,pv101], .c 3, .c 7, .c 127, .c 3,
  .p pv5 [pv2,pv1965263], .p pv17 [pv2,pv3,pv7,pv5849], .c 3, .c 53, .c 5, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv5,pv109,pv601], .c 3, .c 5, .c 37, .c 3, .c 1097, .c 11, .c 3, .c 941,
  .p pv3 [pv2,pv3,pv257,pv2549], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv19,pv1361],
  .p pv2 [pv2,pv3,pv5,pv7,pv17,pv367], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv59,pv3331],
  .c 31, .c 3, .c 17, .c 13, .c 3, .p pv3 [pv2,pv113,pv1087], .c 5, .c 3, .c 929,
  .p pv7 [pv2,pv3,pv5,pv6551], .c 3, .c 5, .p pv3 [pv2,pv3,pv19,pv1277], .c 3,
  .p pv2 [pv2,pv5,pv47,pv8363], .p pv23 [pv2,pv3,pv7,pv73,pv641], .c 3, .c 101, .c 7, .c 3,
  .c 499, .c 5, .c 3, .c 41, .c 23, .c 3, .c 5, .p pv2 [pv2,pv3,pv327553], .c 3, .c 11, .c 1553,
  .c 3, .c 7, .c 109, .c 3, .p pv2 [pv2,pv11,pv157,pv569], .c 5, .c 3, .c 643, .c 7, .c 3, .c 5,
  .c 13, .c 3, .p pv29 [pv2,pv5,pv41,pv9587], .c 43, .c 3, .c 23, .c 167, .c 3,
  .p pv2 [pv2,pv7,pv19,pv2111], .c 5, .c 3, .c 7, .c 359, .c 3, .c 5, .c 397, .c 3, .c 19, .c 7,
  .c 3, .c 11, .p pv2 [pv2,pv3,pv327559], .c 3, .c 1069,
]
private theorem h0480c18 : checkBlock 3930459 128 b0480c18 = true := by
  decide +kernel

private def b0480c19 : List Row := [
  .c 5, .c 3, .c 13, .p pv23 [pv2,pv3,pv5,pv19,pv431], .c 3, .c 5, .p pv3 [pv2,pv3,pv655121],
  .c 3, .c 7, .c 173, .c 3, .p pv3 [pv2,pv245671], .c 19, .c 3, .p pv5 [pv2,pv547,pv3593], .c 5,
  .c 3, .c 557, .c 11, .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv98269],
  .p pv2 [pv2,pv3,pv11,pv59557], .c 3, .p pv5 [pv2,pv7,pv280769], .c 23, .c 3, .c 7, .c 5, .c 3,
  .c 61, .c 139, .c 3, .c 5, .c 7, .c 3, .c 17, .c 41, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv47,pv53,pv263], .c 3, .c 79, .c 5, .c 3, .c 157,
  .p pv3 [pv2,pv3,pv5,pv13,pv10079], .c 3, .c 5, .c 11, .c 3, .c 223, .c 13, .c 3,
  .p pv2 [pv2,pv1965413], .c 7, .c 3, .c 239, .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv61,pv179],
  .c 3, .c 5, .c 199, .c 3, .c 53, .c 19, .c 3, .c 7, .c 17, .c 3, .c 29, .c 5, .c 3,
  .p pv2 [pv2,pv523,pv1879], .c 7, .c 3, .c 5, .c 421, .c 3, .c 1613, .c 11, .c 3,
  .p pv5 [pv2,pv1965443], .c 727, .c 3, .c 17, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 23, .c 3,
  .c 251, .c 7, .c 3, .c 37, .p pv3 [pv2,pv3,pv149,pv4397], .c 3, .p pv2 [pv2,pv1965461], .c 5,
  .c 3, .c 19, .c 43, .c 3, .c 5, .c 367, .c 3, .c 7, .c 233, .c 3, .c 461, .c 11, .c 3, .c 13,
  .c 5, .c 3, .c 227, .c 17, .c 3, .c 5, .c 19, .c 3,
]
private theorem h0480c19 : checkBlock 3930715 128 b0480c19 = true := by
  decide +kernel

private def b0480c20 : List Row := [
  .c 11, .p pv2 [pv2,pv3,pv327581], .c 3, .c 73, .c 13, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv379,pv2593], .c 37, .c 3, .c 5, .c 7, .c 3, .p pv11 [pv2,pv5,pv3931], .c 401,
  .c 3, .c 509, .c 1889, .c 3, .c 167, .c 5, .c 3, .c 179, .c 101, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv59561], .c 3, .c 13, .c 47, .c 3, .c 11, .c 7, .c 3, .c 19, .c 5, .c 3,
  .p pv3 [pv2,pv11,pv31,pv131], .p pv3 [pv2,pv3,pv5,pv73,pv359], .c 3, .c 5, .c 13, .c 3, .c 263,
  .c 17, .c 3, .c 7, .c 1493, .c 3, .c 107, .c 5, .c 3, .c 31, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv655181], .c 3, .c 23, .p pv2 [pv2,pv3,pv11,pv1103], .c 3, .c 17, .c 691, .c 3,
  .c 11, .c 5, .c 3, .c 7, .c 59, .c 3, .c 5, .c 317, .c 3, .c 41, .c 7, .c 3, .c 47, .c 83, .c 3,
  .c 1949, .c 5, .c 3, .c 37, .c 31, .c 3, .c 5, .c 11, .c 3, .c 7, .c 29, .c 3, .c 19,
  .p pv3 [pv2,pv3,pv7,pv11,pv67,pv127], .c 3, .c 347, .c 5, .c 3, .c 11, .c 997, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv19,pv37,pv233], .c 3, .c 293, .c 23, .c 3, .c 13, .c 43, .c 3, .c 7, .c 5,
  .c 3, .c 17, .c 103, .c 3, .c 5, .c 7, .c 3, .c 29, .c 11, .c 3, .c 193, .c 89, .c 3, .c 101,
  .c 5,
]
private theorem h0480c20 : checkBlock 3930971 128 b0480c20 = true := by
  decide +kernel

private def b0480c21 : List Row := [
  .c 3, .c 23, .p pv13 [pv2,pv3,pv5,pv131041], .c 3, .c 5, .c 599, .c 3,
  .p pv7 [pv2,pv5,pv29,pv3389], .c 229, .c 3, .p pv5 [pv2,pv11,pv178693], .c 7, .c 3, .c 641,
  .c 5, .c 3, .p pv2 [pv2,pv1965629], .p pv2 [pv2,pv3,pv5,pv65521], .c 3, .c 5, .c 17, .c 3,
  .c 19, .p pv5 [pv2,pv3,pv54601], .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv1965641], .c 5, .c 3,
  .c 547, .c 7, .c 3, .c 5, .c 991, .c 3, .c 11, .c 109, .c 3, .p pv2 [pv2,pv557,pv3529], .c 19,
  .c 3, .c 97, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 29, .c 3, .p pv2 [pv2,pv5,pv13,pv30241],
  .c 7, .c 3, .c 139, .c 677, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv683,pv1439], .c 311, .c 3,
  .c 5, .p pv17 [pv2,pv3,pv11,pv13,pv29,pv79], .c 3, .c 7, .p pv2 [pv2,pv3,pv47,pv1549], .c 3,
  .c 11, .c 13, .c 3, .p pv2 [pv2,pv982843], .c 5, .c 3, .p pv2 [pv2,pv11,pv83,pv2153], .c 53,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv38543], .c 3, .c 523, .p pv5 [pv2,pv3,pv5119], .c 3, .c 89,
  .p pv3 [pv2,pv3,pv37,pv5903], .c 3, .c 7, .c 5, .c 3, .c 47, .c 11, .c 3, .c 5, .c 7, .c 3,
  .c 13, .c 19, .c 3, .c 1873, .c 563, .c 3, .c 11, .c 5, .c 3, .p pv13 [pv2,pv7,pv280817],
  .c 131, .c 3, .c 5, .c 13, .c 3, .c 31, .c 1013, .c 3, .p pv3 [pv2,pv47,pv1307], .c 7, .c 3,
  .p pv5 [pv2,pv1965731], .c 5, .c 3, .p pv2 [pv2,pv982867], .c 17, .c 3, .c 5, .c 11, .c 3,
  .p pv13 [pv2,pv5,pv7,pv19,pv739],
]
private theorem h0480c21 : checkBlock 3931227 128 b0480c21 = true := by
  decide +kernel

private def b0480c22 : List Row := [
  .c 71, .c 3, .c 7, .c 137, .c 3, .c 67, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 97, .c 3, .c 61,
  .c 31, .c 3, .p pv2 [pv2,pv509,pv1931], .p pv3 [pv2,pv3,pv19,pv34487], .c 3,
  .p pv2 [pv2,pv7,pv17,pv16519], .c 5, .c 3, .c 7, .c 41, .c 3, .c 5, .c 19, .c 3,
  .p pv3 [pv2,pv5,pv53,pv3709], .c 7, .c 3, .p pv2 [pv2,pv37,pv53129], .c 1181, .c 3,
  .p pv3 [pv2,pv122861], .c 5, .c 3, .c 29, .c 73, .c 3, .c 5, .p pv5 [pv2,pv3,pv655261], .c 3,
  .c 7, .c 17, .c 3, .c 13, .c 971, .c 3, .c 37, .c 5, .c 3, .p pv2 [pv2,pv29,pv33893], .c 877,
  .c 3, .c 5, .c 23, .c 3, .c 797, .c 13, .c 3, .c 17, .c 11, .c 3, .c 7, .c 5, .c 3, .c 43,
  .c 499, .c 3, .c 5, .c 7, .c 3, .c 11, .c 61, .c 3, .c 31, .p pv3 [pv2,pv3,pv655273], .c 3,
  .c 23, .c 5, .c 3, .p pv3 [pv2,pv7,pv1097], .c 19, .c 3, .c 5, .c 37, .c 3,
  .p pv2 [pv2,pv5,pv196583], .c 149, .c 3, .p pv2 [pv2,pv23,pv127,pv673], .c 7, .c 3, .c 467,
  .c 5, .c 3, .c 1087, .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv6619], .c 3, .c 47,
  .p pv5 [pv2,pv3,pv17,pv19273], .c 3, .c 7, .c 31, .c 3, .c 131, .c 5, .c 3, .c 17, .c 7, .c 3,
  .c 5, .c 409, .c 3, .p pv3 [pv2,pv5,pv13,pv7561], .c 163, .c 3, .c 19,
  .p pv23 [pv2,pv3,pv101,pv811], .c 3, .c 13, .c 5, .c 3,
]
private theorem h0480c22 : checkBlock 3931483 128 b0480c22 = true := by
  decide +kernel

private def b0480c23 : List Row := [
  .c 7, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv13,pv19,pv379], .c 3, .c 79, .c 7, .c 3,
  .p pv2 [pv2,pv982939], .c 13, .c 3, .c 11, .c 5, .c 3, .c 821, .c 173, .c 3, .c 5, .c 17, .c 3,
  .c 7, .p pv3 [pv2,pv3,pv613,pv1069], .c 3, .p pv2 [pv2,pv1965893], .c 239, .c 3, .c 83, .c 5,
  .c 3, .p pv7 [pv2,pv13,pv97,pv1559], .p pv23 [pv2,pv3,pv5,pv6553], .c 3, .c 5, .c 11, .c 3,
  .c 13, .p pv2 [pv2,pv3,pv149,pv733], .c 3, .p pv3 [pv2,pv7,pv61,pv1151], .c 59, .c 3, .c 7,
  .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv7,pv79], .c 3, .c 5, .c 7, .c 3, .c 19, .c 257, .c 3,
  .p pv5 [pv2,pv1965923], .c 29, .c 3, .c 73, .c 5, .c 3, .c 41, .p pv2 [pv2,pv3,pv5,pv19,pv3449],
  .c 3, .c 5, .c 227, .c 3, .c 1021, .c 11, .c 3, .c 43, .c 7, .c 3, .c 1277, .c 5, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv5,pv131063], .c 3, .c 5, .c 769, .c 3, .c 1327, .c 881, .c 3, .c 7, .c 71,
  .c 3, .c 17, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv47,pv73,pv191], .c 3, .c 89,
  .p pv2 [pv2,pv3,pv327661], .c 3, .c 59, .c 11, .c 3, .p pv5 [pv2,pv7,pv23,pv12211], .c 5, .c 3,
  .c 7, .c 503, .c 3, .c 5, .c 109, .c 3, .c 11, .c 7, .c 3, .c 13, .p pv11 [pv2,pv3,pv20479],
  .c 3, .c 47, .c 5, .c 3, .c 1753, .c 17, .c 3, .c 5, .c 521, .c 3, .c 7, .c 13,
]
private theorem h0480c23 : checkBlock 3931739 128 b0480c23 = true := by
  decide +kernel

private def b0480c24 : List Row := [
  .c 3, .p pv2 [pv2,pv59,pv16661], .c 61, .c 3, .p pv2 [pv2,pv283,pv6947], .c 5, .c 3, .c 31,
  .c 23, .c 3, .c 5, .c 53, .c 3, .p pv13 [pv2,pv5,pv47,pv89], .c 29, .c 3, .c 11, .c 67, .c 3,
  .c 7, .c 5, .c 3, .p pv11 [pv2,pv11,pv367,pv487], .c 199, .c 3, .c 5, .c 7, .c 3, .c 71,
  .p pv7 [pv2,pv3,pv29,pv11299], .c 3, .c 23, .p pv2 [pv2,pv3,pv13,pv50411], .c 3,
  .p pv5 [pv2,pv1966031], .c 5, .c 3, .c 19, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv327673], .c 3,
  .c 29, .c 17, .c 3, .c 761, .c 7, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv1966049], .c 37, .c 3,
  .c 5, .c 19, .c 3, .c 479, .c 263, .c 3, .c 7, .p pv3 [pv2,pv3,pv72817], .c 3, .c 13, .c 5,
  .c 3, .p pv3 [pv2,pv103,pv1193], .c 7, .c 3, .c 5, .c 11, .c 3, .c 617, .c 107, .c 3,
  .p pv2 [pv2,pv41,pv79,pv607], .c 13, .c 3, .p pv3 [pv2,pv7,pv1433], .c 5, .c 3, .c 7, .c 47,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv251,pv373], .c 3, .c 139, .c 7, .c 3, .c 1733,
  .p pv3 [pv2,pv3,pv43,pv15241], .c 3, .c 19, .c 5, .c 3, .c 1973, .c 151, .c 3, .c 5, .c 29,
  .c 3, .c 7, .c 11, .c 3, .p pv5 [pv2,pv401,pv4903], .p pv11 [pv2,pv3,pv7,pv47,pv83], .c 3,
  .c 1571, .c 5, .c 3, .c 17, .c 19, .c 3, .c 5, .c 13, .c 3, .c 103, .c 101, .c 3,
  .p pv2 [pv2,pv7,pv11,pv17,pv751], .p pv3 [pv2,pv3,pv655373], .c 3, .c 7, .c 5, .c 3, .c 37,
]
private theorem h0480c24 : checkBlock 3931995 128 b0480c24 = true := by
  decide +kernel

private def b0480c25 : List Row := [
  .c 773, .c 3, .c 5, .c 7, .c 3, .c 383, .c 1847, .c 3, .c 239, .c 11, .c 3, .c 1979, .c 5, .c 3,
  .c 13, .p pv7 [pv2,pv3,pv5,pv11,pv331], .c 3, .c 5, .c 17, .c 3, .c 11, .c 1861, .c 3, .c 19,
  .c 7, .c 3, .p pv5 [pv2,pv11,pv47,pv3803], .c 5, .c 3, .p pv2 [pv2,pv191,pv5147], .c 137, .c 3,
  .c 5, .c 197, .c 3, .c 17, .c 37, .c 3, .c 7, .c 1607, .c 3, .c 23, .c 5, .c 3, .c 673, .c 7,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv59581], .c 3, .c 41, .c 293, .c 3, .c 11, .c 569, .c 3,
  .c 307, .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv89,pv263], .c 3, .c 31, .c 7,
  .c 3, .p pv2 [pv2,pv1291,pv1523], .c 17, .c 3, .c 43, .c 5, .c 3, .p pv7 [pv2,pv797,pv2467],
  .c 11, .c 3, .c 5, .c 211, .c 3, .c 7, .p pv5 [pv2,pv3,pv11,pv31], .c 3, .c 251, .c 491, .c 3,
  .c 11, .c 5, .c 3, .c 29, .c 67, .c 3, .c 5, .c 73, .c 3, .c 53, .c 31, .c 3,
  .p pv5 [pv2,pv7,pv40127], .c 19, .c 3, .c 7, .c 5, .c 3, .c 1627, .c 13, .c 3, .c 5, .c 7, .c 3,
  .c 23, .p pv5 [pv2,pv3,pv163853], .c 3, .c 71, .c 43, .c 3, .p pv2 [pv2,pv1966241], .c 5, .c 3,
  .c 11, .c 17, .c 3, .c 5, .c 1747, .c 3, .c 1777, .p pv3 [pv2,pv3,pv7,pv109,pv859], .c 3,
]
private theorem h0480c25 : checkBlock 3932251 128 b0480c25 = true := by
  decide +kernel

private def b0480c26 : List Row := [
  .c 619, .c 7, .c 3, .c 13, .c 5, .c 3, .c 1409, .p pv11 [pv2,pv3,pv5,pv32771], .c 3, .c 5,
  .c 59, .c 3, .c 1187, .c 11, .c 3, .c 7, .c 13, .c 3, .p pv5 [pv2,pv17,pv115663], .c 5, .c 3,
  .c 809, .c 7, .c 3, .c 5, .c 149, .c 3, .c 421, .c 19, .c 3, .c 31, .c 277, .c 3,
  .p pv2 [pv2,pv7,pv140449], .c 5, .c 3, .c 7, .p pv19 [pv2,pv3,pv5,pv65543], .c 3, .c 5, .c 181,
  .c 3, .c 13, .c 7, .c 3, .c 41, .c 11, .c 3, .c 29, .c 5, .c 3, .c 23, .c 109, .c 3, .c 5,
  .c 13, .c 3, .c 7, .c 83, .c 3, .c 17, .c 31, .c 3, .p pv5 [pv2,pv11,pv23,pv29,pv67], .c 5,
  .c 3, .c 19, .p pv7 [pv2,pv3,pv5,pv2731], .c 3, .c 5, .p pv5 [pv2,pv3,pv293,pv2237], .c 3,
  .c 43, .c 53, .c 3, .p pv3 [pv2,pv7,pv13,pv37,pv73], .p pv3 [pv2,pv3,pv19,pv3833], .c 3, .c 7,
  .c 5, .c 3, .c 13, .c 97, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv98317], .c 167, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv81931], .c 3, .c 37, .c 5, .c 3, .c 67, .c 23, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv53,pv83,pv149], .c 3, .c 197, .p pv5 [pv2,pv3,pv7,pv17], .c 3,
  .p pv2 [pv2,pv983179], .c 7, .c 3, .p pv2 [pv2,pv31,pv137,pv463], .c 5, .c 3, .c 17, .c 11,
  .c 3, .c 5, .c 43, .c 3, .p pv2 [pv2,pv5,pv7,pv4013], .p pv3 [pv2,pv3,pv11,pv5417], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv29,pv3767], .c 3, .c 11, .c 5, .c 3, .c 53, .c 7,
]
private theorem h0480c26 : checkBlock 3932507 128 b0480c26 = true := by
  decide +kernel

private def b0480c27 : List Row := [
  .c 3, .c 5, .c 37, .c 3, .p pv2 [pv2,pv5,pv23,pv17099], .c 13, .c 3, .c 29,
  .p pv7 [pv2,pv3,pv79,pv8297], .c 3, .p pv5 [pv2,pv7,pv280913], .c 5, .c 3, .c 7, .c 19, .c 3,
  .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv1229], .c 7, .c 3, .c 233, .c 127, .c 3,
  .p pv2 [pv2,pv13,pv53,pv1427], .c 5, .c 3, .c 11, .c 89, .c 3, .c 5, .p pv2 [pv2,pv3,pv655471],
  .c 3, .c 7, .c 67, .c 3, .c 199, .c 23, .c 3, .c 41, .c 5, .c 3, .c 103, .c 13, .c 3, .c 5,
  .c 79, .c 3, .p pv3 [pv2,pv5,pv196643], .c 11, .c 3, .c 19, .p pv2 [pv2,pv3,pv327739], .c 3,
  .c 7, .c 5, .c 3, .c 241, .c 59, .c 3, .c 5, .c 7, .c 3, .c 947, .c 29, .c 3,
  .p pv3 [pv2,pv11,pv11173], .c 17, .c 3, .c 13, .c 5, .c 3, .c 43, .c 1549, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv13,pv17,pv1483], .c 3, .p pv3 [pv2,pv5,pv98323], .c 1301, .c 3,
  .p pv5 [pv2,pv1966463], .c 7, .c 3, .c 17, .c 5, .c 3, .c 31,
  .p pv2 [pv2,pv3,pv5,pv11,pv59,pv101], .c 3, .c 5, .p pv2 [pv2,pv3,pv151,pv1447], .c 3, .c 11,
  .p pv5 [pv2,pv3,pv37,pv43,pv103], .c 3, .c 7, .p pv3 [pv2,pv3,pv739,pv887], .c 3,
  .p pv2 [pv2,pv11,pv19,pv97], .c 5, .c 3, .p pv7 [pv2,pv13,pv2909], .c 7, .c 3, .c 5, .c 23,
  .c 3, .c 13, .c 983, .c 3, .c 751, .c 37, .c 3, .p pv3 [pv2,pv7,pv8779], .c 5, .c 3, .c 7,
  .c 17, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv393301], .c 7, .c 3, .c 11,
]
private theorem h0480c27 : checkBlock 3932763 128 b0480c27 = true := by
  decide +kernel

private def b0480c28 : List Row := [
  .c 19, .c 3, .c 23, .c 5, .c 3, .c 521, .c 953, .c 3, .c 5, .p pv2 [pv2,pv3,pv61,pv199], .c 3,
  .c 7, .c 509, .c 3, .c 109, .c 269, .c 3, .p pv2 [pv2,pv17,pv57839], .c 5, .c 3, .c 13, .c 11,
  .c 3, .c 5, .c 29, .c 3, .p pv7 [pv2,pv5,pv541,pv727], .p pv5 [pv2,pv3,pv11,pv13,pv191], .c 3,
  .c 53, .c 397, .c 3, .c 7, .c 5, .c 3, .c 41, .p pv3 [pv2,pv3,pv5,pv7,pv2081], .c 3, .c 5, .c 7,
  .c 3, .c 47, .c 17, .c 3, .c 1543, .p pv19 [pv2,pv3,pv109253], .c 3, .c 647, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv499,pv563], .c 83, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv41,pv53,pv181],
  .c 19, .c 3, .c 13, .c 7, .c 3, .p pv5 [pv2,pv101,pv19471], .c 5, .c 3, .c 11,
  .p pv23 [pv2,pv3,pv5,pv13,pv2017], .c 3, .c 5, .c 281, .c 3, .c 23, .c 13, .c 3, .c 7, .c 1901,
  .c 3, .c 79, .c 5, .c 3, .c 389, .c 7, .c 3, .c 5, .c 31, .c 3, .c 113, .c 11, .c 3,
  .p pv2 [pv2,pv983299], .p pv3 [pv2,pv3,pv8093], .c 3, .p pv2 [pv2,pv7,pv13,pv21611], .c 5, .c 3,
  .c 7, .c 37, .c 3, .c 5, .c 311, .c 3, .p pv3 [pv2,pv5,pv196661], .c 7, .c 3,
  .p pv2 [pv2,pv11,pv16253], .c 227, .c 3, .p pv3 [pv2,pv293,pv839], .c 5, .c 3, .c 17, .c 13,
  .c 3, .c 5, .c 19, .c 3, .c 7, .c 23, .c 3, .p pv3 [pv2,pv17,pv28921], .c 11, .c 3, .c 191,
  .c 5, .c 3, .p pv2 [pv2,pv983317], .c 1453, .c 3,
]
private theorem h0480c28 : checkBlock 3933019 128 b0480c28 = true := by
  decide +kernel

private def b0480c29 : List Row := [
  .c 5, .p pv2 [pv2,pv3,pv23,pv14251], .c 3, .c 11, .c 139, .c 3, .c 83, .c 47, .c 3, .c 7, .c 5,
  .c 3, .c 23, .p pv17 [pv2,pv3,pv5,pv7,pv1873], .c 3, .c 5, .c 7, .c 3, .c 31, .c 73, .c 3,
  .c 127, .c 13, .c 3, .c 19, .c 5, .c 3, .c 71, .c 79, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv11,pv47,pv317], .c 3, .c 17, .p pv5 [pv2,pv3,pv7,pv19,pv31,pv53], .c 3,
  .c 11, .c 7, .c 3, .c 59, .c 5, .c 3, .c 37, .c 19, .c 3, .c 5, .p pv3 [pv2,pv3,pv655561], .c 3,
  .c 13, .c 31, .c 3, .c 7, .p pv2 [pv2,pv3,pv218521], .c 3, .c 47, .c 5, .c 3, .c 1171, .c 7,
  .c 3, .c 5, .c 13, .c 3, .c 491, .c 421, .c 3, .c 137, .c 17, .c 3, .c 11, .c 5, .c 3, .c 7,
  .c 251, .c 3, .c 5, .c 107, .c 3, .p pv13 [pv2,pv5,pv47,pv8369], .c 7, .c 3, .c 19,
  .p pv3 [pv2,pv3,pv281,pv2333], .c 3, .c 17, .c 5, .c 3, .c 13, .c 149, .c 3, .c 5, .c 11, .c 3,
  .c 7, .c 61, .c 3, .c 103, .p pv19 [pv2,pv3,pv7,pv11,pv43], .c 3, .c 29, .c 5, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv5,pv32779], .c 3, .c 5, .c 587, .c 3, .p pv2 [pv2,pv5,pv11,pv35759],
  .p pv13 [pv2,pv3,pv181,pv1811], .c 3, .c 31, .c 41, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv983377], .c 17, .c 3, .c 5, .c 7, .c 3, .c 971, .c 11, .c 3, .c 13, .c 23,
]
private theorem h0480c29 : checkBlock 3933275 128 b0480c29 = true := by
  decide +kernel

private def b0480c30 : List Row := [
  .c 3, .c 89, .c 5, .c 3, .p pv7 [pv2,pv7,pv280967], .c 467, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv101,pv6491], .c 3, .c 19, .c 13, .c 3, .p pv2 [pv2,pv11,pv89399], .c 7, .c 3,
  .c 359, .c 5, .c 3, .p pv3 [pv2,pv79,pv389], .c 47, .c 3, .c 5, .p pv5 [pv2,pv3,pv18211], .c 3,
  .c 37, .p pv3 [pv2,pv3,pv655597], .c 3, .c 7, .c 11, .c 3, .p pv3 [pv2,pv13,pv109,pv347], .c 5,
  .c 3, .p pv13 [pv2,pv23,pv85513], .c 7, .c 3, .c 5, .c 53, .c 3, .c 11, .c 17, .c 3, .c 499,
  .c 83, .c 3, .c 1109, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 67, .c 3, .c 97, .c 7, .c 3,
  .c 17, .c 719, .c 3, .c 317, .c 5, .c 3, .c 907, .c 1451, .c 3, .c 5, .c 23, .c 3, .c 7, .c 103,
  .c 3, .c 11, .c 163, .c 3, .c 13, .c 5, .c 3, .c 449, .c 263, .c 3, .c 5, .c 739, .c 3, .c 109,
  .c 19, .c 3, .c 59, .c 13, .c 3, .c 7, .c 5, .c 3, .c 281, .c 11, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv393373], .p pv2 [pv2,pv3,pv11,pv17,pv1753], .c 3, .c 431, .c 233, .c 3, .c 11,
  .c 5, .c 3, .c 17, .c 73, .c 3, .c 5, .c 1303, .c 3, .c 13, .c 29, .c 3,
  .p pv5 [pv2,pv17,pv37,pv53,pv59], .c 7, .c 3, .p pv2 [pv2,pv983443], .c 5, .c 3, .c 19,
  .p pv7 [pv2,pv3,pv5,pv65563], .c 3, .c 5,
]
private theorem h0480c30 : checkBlock 3933531 128 b0480c30 = true := by
  decide +kernel

private def b0480c31 : List Row := [
  .c 11, .c 3, .p pv7 [pv2,pv5,pv7,pv56197], .c 383, .c 3, .c 7, .c 131, .c 3, .c 37, .c 5, .c 3,
  .c 11, .c 7, .c 3, .c 5, .c 17, .c 3, .c 29, .p pv3 [pv2,pv3,pv655637], .c 3, .c 41, .c 61,
  .c 3, .c 1669, .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv37,pv443], .c 3, .c 5, .c 173, .c 3,
  .c 17, .c 7, .c 3, .p pv3 [pv2,pv269,pv457], .p pv2 [pv2,pv3,pv655643], .c 3, .c 691, .c 5,
  .c 3, .c 31, .p pv7 [pv2,pv3,pv5,pv131129], .c 3, .c 5, .c 37, .c 3, .c 7, .c 179, .c 3,
  .p pv5 [pv2,pv11,pv178813], .c 89, .c 3, .c 19, .c 5, .c 3, .c 257,
  .p pv19 [pv2,pv3,pv5,pv31,pv47], .c 3, .c 5, .p pv3 [pv2,pv3,pv655651], .c 3, .c 1181, .c 1021,
  .c 3, .c 13, .c 11, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv349,pv1409], .c 19, .c 3, .c 5, .c 7,
  .c 3, .c 11, .c 13, .c 3, .c 47, .c 157, .c 3, .c 17, .c 5, .c 3, .p pv7 [pv2,pv7,pv280997],
  .p pv13 [pv2,pv3,pv5,pv32783], .c 3, .c 5, .c 607, .c 3, .p pv2 [pv2,pv5,pv17,pv73,pv317],
  .p pv2 [pv2,pv3,pv7,pv67,pv233], .c 3, .p pv3 [pv2,pv491747], .c 7, .c 3, .c 283, .c 5, .c 3,
  .c 23, .c 41, .c 3, .c 5, .p pv13 [pv2,pv3,pv11,pv29803], .c 3, .p pv3 [pv2,pv5,pv7,pv281],
  .c 151, .c 3, .c 7, .p pv17 [pv2,pv3,pv13,pv467], .c 3, .p pv2 [pv2,pv23,pv61,pv701], .c 5,
  .c 3, .c 167, .c 7, .c 3, .c 5, .c 43, .c 3, .c 53, .p pv7 [pv2,pv3,pv41,pv1999], .c 3, .c 1429,
  .c 67, .c 3,
]
private theorem h0480c31 : checkBlock 3933787 128 b0480c31 = true := by
  decide +kernel

def rows0480 : List Row :=
  b0480c00 ++ b0480c01 ++ b0480c02 ++ b0480c03 ++ b0480c04 ++ b0480c05 ++ b0480c06 ++ b0480c07 ++
  b0480c08 ++ b0480c09 ++ b0480c10 ++ b0480c11 ++ b0480c12 ++ b0480c13 ++ b0480c14 ++ b0480c15 ++
  b0480c16 ++ b0480c17 ++ b0480c18 ++ b0480c19 ++ b0480c20 ++ b0480c21 ++ b0480c22 ++ b0480c23 ++
  b0480c24 ++ b0480c25 ++ b0480c26 ++ b0480c27 ++ b0480c28 ++ b0480c29 ++ b0480c30 ++ b0480c31

theorem checked0480 : checkBlock 3925851 4096 rows0480 = true :=
  checkBlock_append h0480c00 (
    checkBlock_append h0480c01 (
    checkBlock_append h0480c02 (
    checkBlock_append h0480c03 (
    checkBlock_append h0480c04 (
    checkBlock_append h0480c05 (
    checkBlock_append h0480c06 (
    checkBlock_append h0480c07 (
    checkBlock_append h0480c08 (
    checkBlock_append h0480c09 (
    checkBlock_append h0480c10 (
    checkBlock_append h0480c11 (
    checkBlock_append h0480c12 (
    checkBlock_append h0480c13 (
    checkBlock_append h0480c14 (
    checkBlock_append h0480c15 (
    checkBlock_append h0480c16 (
    checkBlock_append h0480c17 (
    checkBlock_append h0480c18 (
    checkBlock_append h0480c19 (
    checkBlock_append h0480c20 (
    checkBlock_append h0480c21 (
    checkBlock_append h0480c22 (
    checkBlock_append h0480c23 (
    checkBlock_append h0480c24 (
    checkBlock_append h0480c25 (
    checkBlock_append h0480c26 (
    checkBlock_append h0480c27 (
    checkBlock_append h0480c28 (
    checkBlock_append h0480c29 (
    checkBlock_append h0480c30 (
    h0480c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
