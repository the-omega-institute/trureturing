/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks06/Block0481
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks06/Block0481.checked0481
   digest: Kernel proof of checker success on extended consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table042
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table047
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table053
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table060
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table069
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table082
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table098
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table122
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table157
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table160
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table161
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table162
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table165
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table167
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table168
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table171
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table175
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table182
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table190
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table203
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table224
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables03.Table248

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0481c00 : List Row := [
  .c 73, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv23417], .c 3, .c 59, .c 7,
  .c 3, .c 89, .c 107, .c 3, .c 11, .c 5, .c 3, .c 127, .c 23, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv13,pv31,pv1627], .c 3, .c 7, .p pv5 [pv2,pv3,pv137,pv2393], .c 3, .c 313,
  .c 13, .c 3, .p pv5 [pv2,pv19,pv103529], .c 5, .c 3, .p pv2 [pv2,pv983527], .c 29, .c 3, .c 5,
  .c 11, .c 3, .c 19, .c 17, .c 3, .c 23, .c 757, .c 3, .c 7, .c 5, .c 3, .c 11, .c 1907, .c 3,
  .c 5, .c 7, .c 3, .c 13, .p pv19 [pv2,pv3,pv101,pv541], .c 3, .c 17, .c 19, .c 3, .c 1063, .c 5,
  .c 3, .c 29, .c 409, .c 3, .c 5, .c 13, .c 3, .c 71, .c 11, .c 3, .p pv2 [pv2,pv167,pv11779],
  .c 7, .c 3, .c 173, .c 5, .c 3, .c 43, .p pv11 [pv2,pv3,pv5,pv79,pv83], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv127,pv1721], .c 3, .c 401, .c 787, .c 3, .c 7, .c 23, .c 3, .c 97, .c 5, .c 3,
  .c 13, .c 7, .c 3, .c 5, .c 41, .c 3, .c 31, .c 53, .c 3, .c 37, .c 11, .c 3, .c 101, .c 5,
  .c 3, .c 7, .p pv37 [pv2,pv3,pv5,pv11,pv1987], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv283,pv331],
  .c 3, .c 11, .c 7, .c 3, .c 349, .c 79, .c 3, .c 83, .c 5, .c 3, .p pv3 [pv2,pv23,pv10691],
  .c 103, .c 3, .c 5, .c 59,
]
private theorem h0481c00 : checkBlock 3934043 128 b0481c00 = true := by
  decide +kernel

private def b0481c01 : List Row := [
  .c 3, .c 7, .c 31, .c 3, .c 13, .p pv31 [pv2,pv3,pv7,pv6691], .c 3, .c 457, .c 5, .c 3, .c 41,
  .c 37, .c 3, .c 5, .c 17, .c 3, .c 163, .c 13, .c 3, .c 11, .p pv3 [pv2,pv3,pv655723], .c 3,
  .c 7, .c 5, .c 3, .c 19, .p pv53 [pv2,pv3,pv5,pv7,pv1249], .c 3, .c 5, .c 7, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv655727], .c 3, .p pv5 [pv2,pv83,pv137,pv173], .p pv7 [pv2,pv3,pv19,pv719],
  .c 3, .p pv2 [pv2,pv13,pv29,pv2609], .c 5, .c 3, .c 977, .c 11, .c 3, .c 5, .c 19, .c 3,
  .c 1223, .c 1447, .c 3, .c 181, .c 7, .c 3, .c 11, .c 5, .c 3, .c 191, .c 13, .c 3, .c 5, .c 47,
  .c 3, .p pv3 [pv2,pv5,pv7,pv157,pv179], .c 89, .c 3, .c 7, .c 17, .c 3,
  .p pv3 [pv2,pv37,pv3323], .c 5, .c 3, .c 61, .c 7, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv13,pv6053], .p pv2 [pv2,pv3,pv327871], .c 3, .c 43, .c 29, .c 3, .c 13, .c 5,
  .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv131149], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv13,pv1201], .c 3,
  .c 73, .c 7, .c 3, .c 857, .c 13, .c 3, .p pv2 [pv2,pv971,pv1013], .c 5, .c 3,
  .p pv2 [pv2,pv193,pv10193], .c 19, .c 3, .c 5, .p pv2 [pv2,pv3,pv37,pv479], .c 3, .c 7, .c 11,
  .c 3, .c 29, .p pv7 [pv2,pv3,pv7,pv23,pv4073], .c 3, .p pv2 [pv2,pv1967261], .c 5, .c 3, .c 523,
  .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv71,pv2309], .c 3, .c 13, .c 37, .c 3, .c 113, .c 283, .c 3,
  .c 7,
]
private theorem h0481c01 : checkBlock 3934299 128 b0481c01 = true := by
  decide +kernel

private def b0481c02 : List Row := [
  .c 5, .c 3, .c 383, .c 53, .c 3, .c 5, .c 7, .c 3, .c 547, .c 109, .c 3, .c 19, .c 11, .c 3,
  .p pv7 [pv2,pv17,pv31,pv3733], .c 5, .c 3, .p pv2 [pv2,pv7,pv140521], .c 227, .c 3, .c 5,
  .c 331, .c 3, .c 11, .p pv2 [pv2,pv3,pv7,pv1487], .c 3, .c 71, .c 7, .c 3, .c 31, .c 5, .c 3,
  .c 13, .p pv2 [pv2,pv3,pv5,pv21859], .c 3, .c 5, .c 73, .c 3, .p pv7 [pv2,pv5,pv7,pv56209],
  .c 17, .c 3, .c 7, .p pv7 [pv2,pv3,pv218591], .c 3, .c 149, .c 5, .c 3, .c 271, .c 7, .c 3,
  .c 5, .c 101, .c 3, .c 587, .c 269, .c 3, .c 11, .p pv2 [pv2,pv3,pv327889], .c 3, .c 139, .c 5,
  .c 3, .c 7, .c 197, .c 3, .c 5, .c 167, .c 3, .c 19, .c 7, .c 3, .c 13, .c 47, .c 3, .c 103,
  .c 5, .c 3, .c 67, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv131,pv2503], .c 3, .c 7, .c 13, .c 3,
  .p pv5 [pv2,pv443,pv4441], .c 19, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv1967369],
  .p pv2 [pv2,pv3,pv5,pv65579], .c 3, .c 5, .c 601, .c 3, .p pv7 [pv2,pv5,pv15739], .c 79, .c 3,
  .c 439, .c 181, .c 3, .c 7, .c 5, .c 3, .c 17, .c 23, .c 3, .c 5, .c 7, .c 3, .c 83,
  .p pv3 [pv2,pv3,pv218599], .c 3, .c 1889, .c 797, .c 3, .c 47, .c 5, .c 3, .c 11, .c 13, .c 3,
  .c 5, .c 29, .c 3,
]
private theorem h0481c02 : checkBlock 3934555 128 b0481c02 = true := by
  decide +kernel

private def b0481c03 : List Row := [
  .c 41, .p pv2 [pv2,pv3,pv7,pv139,pv337], .c 3, .c 23, .c 7, .c 3, .p pv5 [pv2,pv1967411], .c 5,
  .c 3, .c 419, .c 599, .c 3, .c 5, .c 17, .c 3, .c 127, .c 11, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv10247], .c 3, .c 13, .c 5, .c 3, .c 101, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv13,pv61,pv827], .c 3, .c 17, .p pv5 [pv2,pv3,pv18217], .c 3,
  .p pv2 [pv2,pv11,pv37,pv2417], .c 13, .c 3, .c 1759, .c 5, .c 3, .c 7, .c 71, .c 3, .c 5,
  .c 1237, .c 3, .p pv2 [pv2,pv5,pv19,pv109], .c 7, .c 3, .c 229, .c 11, .c 3, .c 37, .c 5, .c 3,
  .c 19, .c 317, .c 3, .c 5, .c 61, .c 3, .c 7, .c 661, .c 3, .c 953, .c 17, .c 3,
  .p pv5 [pv2,pv11,pv383,pv467], .c 5, .c 3, .c 983, .c 139, .c 3, .c 5, .c 13, .c 3, .c 1283,
  .p pv2 [pv2,pv3,pv71,pv3079], .c 3, .p pv5 [pv2,pv7,pv281069], .c 503, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv23,pv131,pv653], .c 29, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv17,pv79,pv293],
  .p pv17 [pv2,pv3,pv73,pv1123], .c 3, .c 11, .c 97, .c 3, .p pv2 [pv2,pv1967501], .c 5, .c 3,
  .c 13, .p pv2 [pv2,pv3,pv5,pv29,pv4523], .c 3, .c 5, .c 1481, .c 3, .c 167,
  .p pv7 [pv2,pv3,pv7,pv13,pv7207], .c 3, .p pv2 [pv2,pv199,pv9887], .c 7, .c 3, .c 19, .c 5,
  .c 3, .c 29, .c 11, .c 3, .c 5, .c 23, .c 3, .c 137, .c 821, .c 3, .c 7, .c 43, .c 3, .c 11,
  .c 5,
]
private theorem h0481c03 : checkBlock 3934811 128 b0481c03 = true := by
  decide +kernel

private def b0481c04 : List Row := [
  .c 3, .c 79, .c 7, .c 3, .c 5, .c 193, .c 3, .c 1783, .c 311, .c 3, .c 13,
  .p pv17 [pv2,pv3,pv9109], .c 3, .c 23, .c 5, .c 3, .c 7, .p pv41 [pv2,pv3,pv5,pv13,pv1009],
  .c 3, .c 5, .c 11, .c 3, .c 67, .c 7, .c 3, .p pv2 [pv2,pv23,pv42773],
  .p pv17 [pv2,pv3,pv11,pv109,pv547], .c 3, .c 59, .c 5, .c 3, .c 11, .c 761, .c 3, .c 5, .c 233,
  .c 3, .c 7, .c 17, .c 3, .c 19, .c 337, .c 3, .p pv5 [pv2,pv13,pv18919], .c 5, .c 3, .c 997,
  .p pv41 [pv2,pv3,pv5,pv17,pv643], .c 3, .c 5, .c 1951, .c 3, .c 31, .c 11, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv13,pv67,pv251], .c 3, .c 7, .c 5, .c 3, .c 1153, .c 13, .c 3, .c 5, .c 7,
  .c 3, .c 269, .p pv2 [pv2,pv3,pv31,pv21157], .c 3, .p pv11 [pv2,pv11,pv178873], .c 37, .c 3,
  .c 29, .c 5, .c 3, .p pv2 [pv2,pv7,pv103,pv2729], .c 41, .c 3, .c 5, .c 79, .c 3, .c 23, .c 31,
  .c 3, .c 1091, .c 7, .c 3, .c 13, .c 5, .c 3, .c 1061, .c 727, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv12613], .c 3, .c 11, .c 47, .c 3, .c 7, .c 13, .c 3,
  .p pv3 [pv2,pv11,pv197,pv227], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv218627],
  .c 3, .p pv2 [pv2,pv5,pv97,pv4057], .c 61, .c 3, .p pv3 [pv2,pv17,pv3617], .c 19, .c 3, .c 41,
  .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv47,pv2791], .c 3, .c 5, .c 43, .c 3, .c 13,
]
private theorem h0481c04 : checkBlock 3935067 128 b0481c04 = true := by
  decide +kernel

private def b0481c05 : List Row := [
  .c 7, .c 3, .c 11, .c 29, .c 3, .p pv2 [pv2,pv571,pv1723], .c 5, .c 3, .c 277, .c 367, .c 3,
  .c 5, .c 13, .c 3, .c 7, .c 107, .c 3, .c 31, .c 59, .c 3, .p pv2 [pv2,pv83,pv151,pv157], .c 5,
  .c 3, .c 23, .c 11, .c 3, .c 5, .c 1307, .c 3, .c 17, .p pv5 [pv2,pv3,pv11,pv59627], .c 3,
  .c 29, .p pv2 [pv2,pv3,pv31,pv71,pv149], .c 3, .c 7, .c 5, .c 3, .c 13, .c 677, .c 3, .c 5,
  .c 7, .c 3, .p pv2 [pv2,pv5,pv393541], .c 19, .c 3, .p pv5 [pv2,pv29,pv16963], .c 31, .c 3,
  .p pv5 [pv2,pv1967711], .c 5, .c 3, .c 251, .c 37, .c 3, .c 5, .c 11, .c 3, .c 257,
  .p pv3 [pv2,pv3,pv7,pv93701], .c 3, .c 487, .c 7, .c 3, .p pv2 [pv2,pv983863], .c 5, .c 3,
  .c 11, .c 23, .c 3, .c 5, .c 41, .c 3, .p pv11 [pv2,pv5,pv7,pv11,pv19,pv269], .c 907, .c 3,
  .c 7, .p pv3 [pv2,pv3,pv655913], .c 3, .c 17, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv163979], .c 3, .p pv2 [pv2,pv5,pv17,pv463], .c 11, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv19,pv41,pv421], .c 3, .c 67, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv911],
  .c 3, .c 5, .c 19, .c 3, .c 883, .c 7, .c 3, .c 61, .p pv2 [pv2,pv3,pv218641], .c 3, .c 31,
  .c 5, .c 3, .c 41, .c 17, .c 3, .c 5, .c 461, .c 3, .c 7, .p pv2 [pv2,pv3,pv655927], .c 3,
  .c 107, .c 11, .c 3, .p pv2 [pv2,pv211,pv4663], .c 5, .c 3,
]
private theorem h0481c05 : checkBlock 3935323 128 b0481c05 = true := by
  decide +kernel

private def b0481c06 : List Row := [
  .c 37, .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv797,pv823], .c 3, .c 11, .c 1367, .c 3, .c 353,
  .c 23, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv491951], .c 83, .c 3, .c 5, .c 7, .c 3, .c 53,
  .c 199, .c 3, .p pv2 [pv2,pv1967813], .p pv2 [pv2,pv3,pv4049], .c 3, .c 13, .c 5, .c 3, .c 47,
  .c 19, .c 3, .c 5, .c 67, .c 3, .p pv2 [pv2,pv5,pv78713], .c 17, .c 3, .c 11, .c 7, .c 3,
  .c 109, .c 5, .c 3, .c 89, .c 743, .c 3, .c 5, .c 29, .c 3, .c 283, .p pv5 [pv2,pv3,pv72883],
  .c 3, .c 7, .c 167, .c 3, .c 827, .c 5, .c 3, .p pv2 [pv2,pv13,pv19,pv31,pv257], .c 7, .c 3,
  .c 5, .c 1193, .c 3, .c 13, .c 41, .c 3, .c 19, .p pv7 [pv2,pv3,pv218651], .c 3, .c 11, .c 5,
  .c 3, .c 7, .c 1171, .c 3, .c 5, .c 13, .c 3, .c 593, .c 7, .c 3, .c 43, .c 839, .c 3,
  .p pv3 [pv2,pv491969], .c 5, .c 3, .p pv7 [pv2,pv89,pv22111], .p pv17 [pv2,pv3,pv5,pv23,pv31],
  .c 3, .c 5, .c 11, .c 3, .c 7, .c 569, .c 3, .c 83, .p pv2 [pv2,pv3,pv7,pv11,pv1217], .c 3,
  .c 23, .c 5, .c 3, .c 11, .c 31, .c 3, .c 5, .p pv2 [pv2,pv3,pv327983], .c 3, .c 37, .c 643,
  .c 3, .c 409, .p pv7 [pv2,pv3,pv6833], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv1967909],
  .p pv2 [pv2,pv3,pv5,pv7,pv9371], .c 3, .c 5, .c 7, .c 3, .c 19, .c 11,
]
private theorem h0481c06 : checkBlock 3935579 128 b0481c06 = true := by
  decide +kernel

private def b0481c07 : List Row := [
  .c 3, .p pv2 [pv2,pv41,pv103,pv233], .p pv3 [pv2,pv3,pv37,pv17729], .c 3, .c 617, .c 5, .c 3,
  .c 193, .c 29, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv83,pv2371], .c 197, .c 3, .c 13, .c 7,
  .c 3, .c 137, .c 5, .c 3, .p pv17 [pv2,pv1967939], .c 109, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv53,pv12377], .c 3, .c 17, .c 13, .c 3, .c 7, .c 11, .c 3, .c 61, .c 5, .c 3,
  .c 29, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv109331], .c 3, .c 11, .c 173, .c 3, .c 1721, .c 421,
  .c 3, .c 563, .c 5, .c 3, .c 7, .c 73, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv31,pv3023], .c 3,
  .p pv13 [pv2,pv5,pv223,pv353], .c 7, .c 3, .c 1847, .c 17, .c 3, .c 463, .c 5, .c 3, .c 97,
  .c 13, .c 3, .c 5, .c 31, .c 3, .c 7, .c 19, .c 3, .c 11, .p pv2 [pv2,pv3,pv7,pv15619], .c 3,
  .c 17, .c 5, .c 3, .p pv7 [pv2,pv11,pv178909], .p pv19 [pv2,pv3,pv5,pv41], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv72889], .c 3, .p pv2 [pv2,pv5,pv13,pv17,pv137], .c 23, .c 3, .c 79,
  .p pv2 [pv2,pv3,pv461,pv1423], .c 3, .c 7, .c 5, .c 3, .c 599, .c 11, .c 3, .c 5, .c 7, .c 3,
  .c 41, .p pv5 [pv2,pv3,pv11,pv103,pv193], .c 3, .c 307, .c 13, .c 3, .c 11, .c 5, .c 3, .c 19,
  .c 17, .c 3, .c 5, .c 59, .c 3, .c 101, .c 613, .c 3, .c 919, .c 7, .c 3, .c 29, .c 5, .c 3,
  .c 1487,
]
private theorem h0481c07 : checkBlock 3935835 128 b0481c07 = true := by
  decide +kernel

private def b0481c08 : List Row := [
  .c 43, .c 3, .c 5, .c 11, .c 3, .c 13, .p pv5 [pv2,pv3,pv107,pv6131], .c 3, .c 7, .c 47, .c 3,
  .p pv3 [pv2,pv17,pv29,pv499], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 13, .c 3,
  .p pv2 [pv2,pv5,pv11,pv3253], .c 149, .c 3, .p pv3 [pv2,pv492017], .p pv2 [pv2,pv3,pv656023],
  .c 3, .c 863, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 131, .c 3, .p pv7 [pv2,pv5,pv73,pv337],
  .c 7, .c 3, .p pv7 [pv2,pv13,pv151391], .c 71, .c 3, .c 19, .c 5, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv5,pv17,pv227], .c 3, .c 5, .p pv2 [pv2,pv3,pv218677], .c 3, .c 7, .c 1543,
  .c 3, .c 17, .c 29, .c 3, .c 47, .c 5, .c 3, .c 107, .c 19, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv401,pv409], .c 3, .c 619, .p pv3 [pv2,pv3,pv72893], .c 3,
  .p pv2 [pv2,pv7,pv281159], .c 11, .c 3, .c 7, .c 5, .c 3, .p pv13 [pv2,pv127,pv15497],
  .p pv23 [pv2,pv3,pv5,pv7,pv11,pv71], .c 3, .c 5, .c 7, .c 3, .c 11, .c 241, .c 3, .c 13,
  .c 1291, .c 3, .c 43, .c 5, .c 3, .c 61, .p pv3 [pv2,pv3,pv5,pv13,pv10093], .c 3, .c 5, .c 269,
  .c 3, .c 229, .c 13, .c 3, .c 19, .c 7, .c 3, .p pv2 [pv2,pv89,pv11057], .c 5, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv5,pv13121], .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv19,pv43,pv73], .c 3, .c 71,
  .p pv5 [pv2,pv3,pv23,pv2377], .c 3, .c 7, .c 37, .c 3, .c 431, .c 5, .c 3,
  .p pv3 [pv2,pv11,pv41,pv1091], .c 7, .c 3, .c 5, .c 937, .c 3, .c 139, .c 467, .c 3,
]
private theorem h0481c08 : checkBlock 3936091 128 b0481c08 = true := by
  decide +kernel

private def b0481c09 : List Row := [
  .c 491, .c 31, .c 3, .p pv3 [pv2,pv7,pv17573], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 17, .c 3,
  .c 349, .c 7, .c 3, .c 673, .c 73, .c 3, .c 11, .c 5, .c 3, .c 179, .c 47, .c 3, .c 5, .c 1019,
  .c 3, .c 7, .c 433, .c 3, .c 227, .c 823, .c 3, .c 13, .c 5, .c 3, .c 131, .c 59, .c 3, .c 5,
  .c 11, .c 3, .c 29, .c 251, .c 3, .p pv3 [pv2,pv7,pv140587], .c 13, .c 3, .c 7, .c 5, .c 3,
  .c 11, .c 41, .c 3, .c 5, .c 7, .c 3, .c 157, .p pv3 [pv2,pv3,pv656077], .c 3, .c 37, .c 17,
  .c 3, .c 23, .c 5, .c 3, .c 461, .p pv17 [pv2,pv3,pv5,pv59,pv139], .c 3, .c 5, .c 1229, .c 3,
  .c 13, .c 11, .c 3, .c 337, .c 7, .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv984127], .c 769, .c 3,
  .c 5, .c 13, .c 3, .c 43, .p pv2 [pv2,pv3,pv53,pv12379], .c 3, .c 7, .c 281, .c 3, .c 41, .c 5,
  .c 3, .c 59, .c 7, .c 3, .c 5, .c 29, .c 3, .c 97, .c 19, .c 3, .c 103, .c 11, .c 3, .c 1451,
  .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .p pv17 [pv2,pv3,pv7,pv29,pv101], .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv1968293], .p pv13 [pv2,pv3,pv17,pv23,pv839], .c 3, .p pv3 [pv2,pv11,pv22367],
  .c 5, .c 3, .p pv7 [pv2,pv59,pv73,pv457], .c 313,
]
private theorem h0481c09 : checkBlock 3936347 128 b0481c09 = true := by
  decide +kernel

private def b0481c10 : List Row := [
  .c 3, .c 5, .c 43, .c 3, .c 7, .c 163, .c 3, .c 401, .c 127, .c 3, .p pv5 [pv2,pv17,pv115783],
  .c 5, .c 3, .c 19, .p pv3 [pv2,pv3,pv5,pv131221], .c 3, .c 5, .c 107, .c 3,
  .p pv13 [pv2,pv5,pv6151], .p pv5 [pv2,pv3,pv373,pv1759], .c 3, .c 11, .c 79, .c 3, .c 7, .c 5,
  .c 3, .c 31, .c 307, .c 3, .c 5, .c 7, .c 3, .c 73, .c 13, .c 3, .c 101, .c 947, .c 3,
  .p pv2 [pv2,pv1968341], .c 5, .c 3, .c 37, .c 11, .c 3, .c 5, .c 41, .c 3, .c 191, .c 23, .c 3,
  .c 17, .c 7, .c 3, .c 11, .c 5, .c 3, .c 67, .c 29, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv23,pv37,pv257], .c 3, .p pv7 [pv2,pv5,pv7,pv56239], .p pv5 [pv2,pv3,pv328061],
  .c 3, .c 7, .c 229, .c 3, .c 19, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 11, .c 3, .c 1787,
  .c 37, .c 3, .c 47, .p pv13 [pv2,pv3,pv11,pv233], .c 3, .c 83, .c 5, .c 3, .c 7, .c 19, .c 3,
  .c 5, .c 53, .c 3, .p pv11 [pv2,pv5,pv11,pv13,pv2753], .c 7, .c 3, .c 859,
  .p pv23 [pv2,pv3,pv218711], .c 3, .c 13, .c 5, .c 3, .c 17, .p pv7 [pv2,pv3,pv5,pv281,pv467],
  .c 3, .c 5, .c 73, .c 3, .c 7, .c 11, .c 3, .p pv5 [pv2,pv17,pv89,pv1301], .c 13, .c 3,
  .p pv3 [pv2,pv137,pv449], .c 5, .c 3, .p pv7 [pv2,pv19,pv211,pv491], .c 23, .c 3, .c 5, .c 263,
  .c 3, .c 107, .c 67, .c 3, .c 19,
]
private theorem h0481c10 : checkBlock 3936603 128 b0481c10 = true := by
  decide +kernel

private def b0481c11 : List Row := [
  .c 1601, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv13,pv75709], .c 577, .c 3, .c 5, .c 7, .c 3,
  .c 13, .p pv2 [pv2,pv3,pv656147], .c 3, .c 23, .c 11, .c 3, .c 53, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv281207], .c 479, .c 3, .c 5, .c 13, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv7,pv11717], .c 3, .p pv2 [pv2,pv661,pv1489], .c 7, .c 3,
  .p pv2 [pv2,pv11,pv178951], .c 5, .c 3, .p pv7 [pv2,pv17,pv7237], .c 181, .c 3, .c 5, .c 653,
  .c 3, .c 443, .c 41, .c 3, .c 7, .c 311, .c 3, .c 29, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv59651], .c 3, .c 19, .p pv2 [pv2,pv3,pv13,pv25237], .c 3, .c 11, .c 17,
  .c 3, .c 257, .c 5, .c 3, .c 7, .c 1277, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv17,pv919], .c 3,
  .c 61, .c 7, .c 3, .c 193, .c 19, .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv401,pv4909], .c 11,
  .c 3, .c 5, .c 149, .c 3, .c 7, .c 113, .c 3, .c 13, .p pv3 [pv2,pv3,pv7,pv93739], .c 3, .c 11,
  .c 5, .c 3, .c 47, .p pv2 [pv2,pv3,pv5,pv13,pv673], .c 3, .c 5, .p pv5 [pv2,pv3,pv41011], .c 3,
  .p pv2 [pv2,pv5,pv196853], .c 13, .c 3, .p pv2 [pv2,pv7,pv19,pv41], .c 29, .c 3, .c 7, .c 5,
  .c 3, .p pv11 [pv2,pv1968539], .c 17, .c 3, .c 5, .c 7, .c 3, .c 281, .c 31, .c 3,
  .p pv3 [pv2,pv37,pv47,pv283], .p pv2 [pv2,pv3,pv11,pv17,pv29], .c 3,
  .p pv5 [pv2,pv13,pv163,pv929], .c 5, .c 3, .c 11, .p pv71 [pv2,pv3,pv5,pv263,pv499], .c 3,
]
private theorem h0481c11 : checkBlock 3936859 128 b0481c11 = true := by
  decide +kernel

private def b0481c12 : List Row := [
  .c 5, .c 23, .c 3, .c 67, .c 19, .c 3, .c 29, .c 7, .c 3, .c 37, .c 5, .c 3,
  .p pv2 [pv2,pv1968569], .c 13, .c 3, .c 5, .p pv13 [pv2,pv3,pv113,pv5807], .c 3, .c 601, .c 11,
  .c 3, .c 7, .p pv3 [pv2,pv3,pv53,pv4127], .c 3, .c 23, .c 5, .c 3, .p pv3 [pv2,pv246073], .c 7,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv149,pv367], .c 3, .p pv2 [pv2,pv5,pv13,pv19,pv797], .c 17, .c 3,
  .p pv2 [pv2,pv11,pv23,pv31,pv251], .c 41, .c 3, .c 13, .c 5, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv5,pv17,pv193], .c 3, .c 5, .c 37, .c 3, .c 53, .c 7, .c 3, .c 17, .c 11,
  .c 3, .c 1609, .c 5, .c 3, .p pv2 [pv2,pv984307], .c 1381, .c 3, .c 5, .c 19, .c 3, .c 7, .c 29,
  .c 3, .c 59, .p pv23 [pv2,pv3,pv7,pv31], .c 3, .p pv2 [pv2,pv11,pv43,pv2081], .c 5, .c 3,
  .c 113, .p pv2 [pv2,pv3,pv5,pv211,pv311], .c 3, .c 5, .p pv2 [pv2,pv3,pv218737], .c 3, .c 13,
  .p pv5 [pv2,pv3,pv29,pv5657], .c 3, .c 467, .c 31, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv223,pv2207], .p pv3 [pv2,pv3,pv5,pv7,pv18749], .c 3, .c 5, .c 7, .c 3, .c 23,
  .p pv5 [pv2,pv3,pv17,pv4289], .c 3, .c 11, .c 1931, .c 3, .c 19, .c 5, .c 3, .c 17,
  .p pv13 [pv2,pv3,pv5,pv10937], .c 3, .c 5, .c 97, .c 3, .c 47, .c 1613, .c 3,
  .p pv3 [pv2,pv13,pv17,pv131], .c 7, .c 3, .c 419, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv36457], .c 3, .c 787, .p pv2 [pv2,pv3,pv11,pv13,pv353], .c 3, .c 7,
  .p pv19 [pv2,pv3,pv164057],
]
private theorem h0481c12 : checkBlock 3937115 128 b0481c12 = true := by
  decide +kernel

private def b0481c13 : List Row := [
  .c 3, .c 11, .c 5, .c 3, .c 283, .c 7, .c 3, .c 5, .c 17, .c 3, .c 439, .c 23, .c 3,
  .p pv2 [pv2,pv984349], .p pv3 [pv2,pv3,pv541,pv1213], .c 3, .c 31, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv4861], .c 3, .c 5, .c 11, .c 3, .c 17, .c 7, .c 3, .c 13, .c 37, .c 3,
  .c 557, .c 5, .c 3, .c 11, .c 1423, .c 3, .c 5, .c 71, .c 3, .c 7, .c 13, .c 3, .c 317, .c 619,
  .c 3, .c 179, .c 5, .c 3, .p pv2 [pv2,pv984367], .c 211, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv41,pv53,pv151], .c 3, .p pv3 [pv2,pv5,pv173,pv569], .c 11, .c 3,
  .p pv5 [pv2,pv7,pv281249], .c 17, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv1968749],
  .p pv2 [pv2,pv3,pv5,pv7], .c 3, .c 5, .c 7, .c 3, .c 223, .p pv5 [pv2,pv3,pv359,pv457], .c 3,
  .c 41, .c 47, .c 3, .c 17, .c 5, .c 3, .c 53, .c 13, .c 3, .c 5, .p pv11 [pv2,pv3,pv1709], .c 3,
  .c 19, .c 367, .c 3, .c 73, .c 7, .c 3, .c 43, .c 5, .c 3, .p pv13 [pv2,pv31,pv41,pv1549],
  .p pv7 [pv2,pv3,pv5,pv11,pv19,pv157], .c 3, .c 5, .p pv3 [pv2,pv3,pv47,pv13963], .c 3, .c 11,
  .p pv2 [pv2,pv3,pv4051], .c 3, .c 7, .c 19, .c 3, .c 13, .c 5, .c 3, .c 31, .c 7, .c 3, .c 5,
  .c 79, .c 3, .c 59, .c 83, .c 3, .p pv5 [pv2,pv1968803], .c 13, .c 3, .c 47, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv29,pv31,pv73], .c 3, .c 5,
]
private theorem h0481c13 : checkBlock 3937371 128 b0481c13 = true := by
  decide +kernel

private def b0481c14 : List Row := [
  .c 89, .c 3, .p pv11 [pv2,pv5,pv271,pv1453], .c 7, .c 3, .c 11, .c 43, .c 3,
  .p pv2 [pv2,pv17,pv179,pv647], .c 5, .c 3, .c 29, .c 31, .c 3, .c 5, .c 67, .c 3, .c 7, .c 641,
  .c 3, .c 523, .c 23, .c 3, .p pv3 [pv2,pv61,pv8069], .c 5, .c 3, .p pv7 [pv2,pv29,pv67891],
  .c 11, .c 3, .c 5, .c 13, .c 3, .p pv19 [pv2,pv5,pv103,pv3823], .c 17, .c 3,
  .p pv3 [pv2,pv7,pv17579], .c 241, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv984427], .c 113, .c 3,
  .c 5, .c 7, .c 3, .p pv11 [pv2,pv5,pv98443], .c 673, .c 3, .c 17, .c 131, .c 3, .c 61, .c 5,
  .c 3, .c 13, .c 53, .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv19,pv829],
  .p pv5 [pv2,pv3,pv7,pv13,pv601], .c 3, .p pv2 [pv2,pv347,pv2837], .c 7, .c 3, .c 41, .c 5, .c 3,
  .c 11, .p pv3 [pv2,pv3,pv5,pv43753], .c 3, .c 5, .p pv5 [pv2,pv3,pv82037], .c 3,
  .p pv17 [pv2,pv5,pv7,pv11,pv2557], .p pv3 [pv2,pv3,pv656297], .c 3, .c 7,
  .p pv13 [pv2,pv3,pv19,pv101], .c 3, .c 103, .c 5, .c 3, .c 37, .c 7, .c 3, .c 5, .c 19, .c 3,
  .c 43, .c 11, .c 3, .c 13, .p pv2 [pv2,pv3,pv656303], .c 3, .c 29, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv13,pv23,pv439], .c 3, .c 5, .c 31, .c 3, .c 1459, .c 7, .c 3, .c 53,
  .p pv7 [pv2,pv3,pv47,pv3491], .c 3, .c 23, .c 5, .c 3, .c 479,
  .p pv13 [pv2,pv3,pv5,pv131,pv167], .c 3, .c 5, .c 1471, .c 3, .c 7, .c 37, .c 3,
  .p pv2 [pv2,pv23,pv1861], .c 11, .c 3,
]
private theorem h0481c14 : checkBlock 3937627 128 b0481c14 = true := by
  decide +kernel

private def b0481c15 : List Row := [
  .c 19, .c 5, .c 3, .c 101, .c 269, .c 3, .c 5, .c 17, .c 3, .c 11,
  .p pv5 [pv2,pv3,pv19,pv34543], .c 3, .c 331, .c 97, .c 3, .c 7, .c 5, .c 3,
  .p pv13 [pv2,pv1163,pv1693], .c 13, .c 3, .c 5, .c 7, .c 3, .c 17, .c 233, .c 3, .c 113, .c 29,
  .c 3, .p pv5 [pv2,pv47,pv41893], .c 5, .c 3, .p pv2 [pv2,pv7,pv17,pv8273],
  .p pv19 [pv2,pv3,pv5,pv2917], .c 3, .c 5, .c 223, .c 3, .c 31, .c 719, .c 3, .c 11, .c 7, .c 3,
  .c 13, .c 5, .c 3, .c 1481, .p pv7 [pv2,pv3,pv5,pv65633], .c 3, .c 5, .c 503, .c 3, .c 23,
  .p pv7 [pv2,pv3,pv31,pv67,pv79], .c 3, .c 7, .c 13, .c 3, .c 239, .c 5, .c 3, .c 41, .c 7, .c 3,
  .c 5, .c 181, .c 3, .c 37, .c 31, .c 3, .c 167, .p pv11 [pv2,pv3,pv107,pv3067], .c 3, .c 11,
  .c 5, .c 3, .c 7, .c 1279, .c 3, .c 5, .c 431, .c 3, .c 13, .c 7, .c 3, .p pv3 [pv2,pv492257],
  .c 53, .c 3, .p pv5 [pv2,pv1969031], .c 5, .c 3, .c 43, .c 79, .c 3, .c 5, .c 11, .c 3, .c 7,
  .c 23, .c 3, .p pv5 [pv2,pv71,pv27733], .p pv17 [pv2,pv3,pv7,pv11,pv2131], .c 3, .c 1193, .c 5,
  .c 3, .c 11, .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv23,pv28537], .c 3, .c 19, .c 29, .c 3,
  .p pv2 [pv2,pv7,pv13,pv31,pv349], .p pv3 [pv2,pv3,pv17,pv38609], .c 3, .c 7, .c 5, .c 3, .c 13,
  .c 73, .c 3, .c 5, .c 7,
]
private theorem h0481c15 : checkBlock 3937883 128 b0481c15 = true := by
  decide +kernel

private def b0481c16 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv196907], .c 11, .c 3, .c 31, .c 19, .c 3, .p pv3 [pv2,pv17,pv23,pv1259],
  .c 5, .c 3, .c 727, .c 89, .c 3, .c 5, .p pv5 [pv2,pv3,pv233,pv313], .c 3, .c 29, .c 41, .c 3,
  .c 47, .c 7, .c 3, .c 587, .c 5, .c 3, .c 379, .c 59, .c 3, .c 5, .p pv2 [pv2,pv3,pv307,pv1069],
  .c 3, .c 1087, .c 17, .c 3, .c 7, .c 11, .c 3, .c 293, .c 5, .c 3, .c 149, .c 7, .c 3, .c 5,
  .c 197, .c 3, .c 11, .c 13, .c 3, .c 17, .c 521, .c 3, .c 37, .c 5, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv5,pv59,pv89], .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv3907], .c 3, .c 409, .c 7,
  .c 3, .c 23, .c 439, .c 3, .p pv3 [pv2,pv13,pv9467], .c 5, .c 3, .c 109,
  .p pv11 [pv2,pv3,pv5,pv37,pv887], .c 3, .c 5, .c 29, .c 3, .c 7, .c 101, .c 3, .c 11, .c 71,
  .c 3, .p pv5 [pv2,pv31,pv63521], .c 5, .c 3, .c 59, .c 13, .c 3, .c 5, .c 37, .c 3,
  .p pv3 [pv2,pv5,pv19,pv2591], .c 461, .c 3, .c 43, .p pv7 [pv2,pv3,pv18233], .c 3, .c 7, .c 5,
  .c 3, .c 17, .c 11, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv13,pv73,pv83], .c 601, .c 3,
  .p pv2 [pv2,pv17,pv57917], .c 23, .c 3, .c 11, .c 5, .c 3, .c 487,
  .p pv2 [pv2,pv3,pv5,pv43,pv71], .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv196919],
  .p pv3 [pv2,pv3,pv7,pv23,pv151], .c 3, .c 79, .c 7, .c 3, .p pv3 [pv2,pv492299],
]
private theorem h0481c16 : checkBlock 3938139 128 b0481c16 = true := by
  decide +kernel

private def b0481c17 : List Row := [
  .c 5, .c 3, .c 233, .c 1759, .c 3, .c 5, .c 11, .c 3, .c 103, .c 43, .c 3, .c 7, .c 41, .c 3,
  .c 73, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv36467], .c 3, .c 13, .c 271, .c 3,
  .p pv5 [pv2,pv1969223], .p pv13 [pv2,pv3,pv82051], .c 3, .c 19, .c 5, .c 3, .c 7, .c 29, .c 3,
  .c 5, .c 13, .c 3, .p pv29 [pv2,pv5,pv393847], .c 7, .c 3, .p pv2 [pv2,pv137,pv7187], .c 313,
  .c 3, .c 53, .c 5, .c 3, .p pv3 [pv2,pv31,pv15881], .c 19, .c 3, .c 5, .c 23, .c 3, .c 7,
  .c 307, .c 3, .c 373, .c 17, .c 3, .p pv3 [pv2,pv71,pv3467], .c 5, .c 3, .c 13,
  .p pv17 [pv2,pv3,pv5,pv23,pv1427], .c 3, .c 5, .p pv19 [pv2,pv3,pv17,pv61,pv211], .c 3,
  .p pv29 [pv2,pv5,pv393853], .c 151, .c 3, .c 179, .c 11, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv19,pv29,pv1787], .c 193, .c 3, .c 5, .c 7, .c 3, .c 11, .c 107, .c 3, .c 19,
  .c 73, .c 3, .c 947, .c 5, .c 3, .c 829, .c 31, .c 3, .c 5, .c 61, .c 3, .c 967,
  .p pv5 [pv2,pv3,pv7,pv5861], .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv577,pv3413], .c 5, .c 3,
  .p pv3 [pv2,pv199,pv1237], .c 17, .c 3, .c 5, .c 103, .c 3, .c 197, .c 13, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv17,pv43,pv449], .c 3, .p pv3 [pv2,pv233,pv2113], .c 5, .c 3,
  .p pv11 [pv2,pv11,pv179029], .c 7, .c 3, .c 5, .c 47, .c 3,
]
private theorem h0481c17 : checkBlock 3938395 128 b0481c17 = true := by
  decide +kernel

private def b0481c18 : List Row := [
  .c 127, .p pv2 [pv2,pv3,pv36469], .c 3, .p pv3 [pv2,pv123083], .c 157, .c 3, .c 59, .c 5, .c 3,
  .c 7, .c 11, .c 3, .c 5, .c 227, .c 3, .c 19, .c 7, .c 3, .c 37, .c 1657, .c 3, .c 11, .c 5,
  .c 3, .p pv2 [pv2,pv269,pv7321], .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv41,pv593], .c 3, .c 7,
  .c 17, .c 3, .p pv2 [pv2,pv179,pv5501], .c 19, .c 3, .p pv2 [pv2,pv29,pv59,pv1151], .c 5, .c 3,
  .c 67, .p pv11 [pv2,pv3,pv5,pv17,pv7723], .c 3, .c 5, .c 11, .c 3, .c 47,
  .p pv3 [pv2,pv3,pv218819], .c 3, .c 17, .c 953, .c 3, .c 7, .c 5, .c 3, .c 11, .c 37, .c 3,
  .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv11,pv61,pv587], .c 23, .c 3, .c 107, .c 13, .c 3,
  .p pv5 [pv2,pv79,pv97,pv257], .c 5, .c 3, .p pv11 [pv2,pv7,pv41,pv47,pv73],
  .p pv17 [pv2,pv3,pv5,pv131293], .c 3, .c 5, .c 347, .c 3, .c 53, .c 11, .c 3, .c 199, .c 7,
  .c 3, .c 1103, .c 5, .c 3, .c 23, .p pv2 [pv2,pv3,pv5,pv65647], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv656471], .c 3, .c 13, .c 19, .c 3, .c 7, .p pv3 [pv2,pv3,pv29,pv22637], .c 3,
  .c 43, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 13, .c 3, .c 73, .c 67, .c 3, .c 29, .c 11, .c 3,
  .c 89, .c 5, .c 3, .c 7, .c 983, .c 3, .c 5, .c 137, .c 3, .c 11, .c 7, .c 3,
  .p pv3 [pv2,pv13,pv29,pv653], .c 59, .c 3, .p pv5 [pv2,pv11,pv179041], .c 5,
]
private theorem h0481c18 : checkBlock 3938651 128 b0481c18 = true := by
  decide +kernel

private def b0481c19 : List Row := [
  .c 3, .c 13, .c 23, .c 3, .c 5, .c 17, .c 3, .c 7, .p pv2 [pv2,pv3,pv13,pv31,pv181], .c 3,
  .p pv5 [pv2,pv103,pv19121], .c 43, .c 3, .c 109, .c 5, .c 3, .p pv2 [pv2,pv71,pv27739],
  .p pv2 [pv2,pv3,pv5,pv79,pv277], .c 3, .c 5, .c 19, .c 3, .c 17, .c 31, .c 3, .c 11, .c 239,
  .c 3, .c 7, .c 5, .c 3, .c 1303, .p pv17 [pv2,pv3,pv5,pv7,pv18757], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv23,pv8563], .c 29, .c 3, .c 13, .c 1297, .c 3, .c 41, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv281357], .c 11, .c 3, .c 5, .c 73, .c 3, .c 367, .c 13, .c 3, .c 59, .c 7,
  .c 3, .c 11, .c 5, .c 3, .c 103, .p pv3 [pv2,pv3,pv5,pv1621], .c 3, .c 5, .c 173, .c 3, .c 29,
  .p pv3 [pv2,pv3,pv19,pv109,pv317], .c 3, .c 7, .c 23, .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv43,pv163,pv281], .c 7, .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv17,pv29,pv47],
  .c 97, .c 3, .c 31, .c 409, .c 3, .c 1453, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 83, .c 3,
  .c 43, .c 7, .c 3, .c 1549, .c 1733, .c 3, .c 149, .c 5, .c 3, .c 53, .c 17, .c 3, .c 5, .c 353,
  .c 3, .c 7, .c 11, .c 3, .c 19, .c 31, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv937,pv1051],
  .c 71, .c 3, .c 5, .c 29, .c 3, .c 137,
]
private theorem h0481c19 : checkBlock 3938907 128 b0481c19 = true := by
  decide +kernel

private def b0481c20 : List Row := [
  .c 349, .c 3, .c 887, .c 13, .c 3, .c 7, .c 5, .c 3, .c 577,
  .p pv23 [pv2,pv3,pv5,pv7,pv83,pv113], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv393919], .c 337,
  .c 3, .c 61, .c 11, .c 3, .p pv2 [pv2,pv101,pv19501], .c 5, .c 3, .p pv11 [pv2,pv7,pv13,pv773],
  .c 47, .c 3, .c 5, .c 277, .c 3, .c 11, .c 17, .c 3, .p pv2 [pv2,pv73,pv26981], .c 7, .c 3,
  .c 23, .c 5, .c 3, .c 41, .p pv7 [pv2,pv3,pv5,pv17,pv1931], .c 3, .c 5, .c 13, .c 3, .c 19,
  .c 59, .c 3, .c 7, .p pv2 [pv2,pv3,pv47,pv61,pv229], .c 3, .c 31, .c 5, .c 3,
  .p pv2 [pv2,pv984817], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv2713], .c 3, .c 521, .c 1223,
  .c 3, .c 11, .c 19, .c 3, .c 71, .c 5, .c 3, .c 7, .c 131, .c 3, .c 5, .c 359, .c 3, .c 563,
  .c 7, .c 3, .c 1433, .c 61, .c 3, .c 193, .c 5, .c 3, .c 571, .c 11, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv54713], .c 3, .c 7, .c 487, .c 3, .c 971, .p pv11 [pv2,pv3,pv7,pv23,pv2039],
  .c 3, .c 11, .c 5, .c 3, .c 17, .p pv7 [pv2,pv3,pv5,pv29,pv283], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv656561], .c 3, .c 23, .p pv19 [pv2,pv3,pv73,pv1499], .c 3, .c 13,
  .p pv2 [pv2,pv3,pv367,pv1789], .c 3, .c 7, .c 5, .c 3, .c 29, .c 691, .c 3, .c 5, .c 7, .c 3,
  .c 719, .c 13, .c 3, .c 89, .c 197, .c 3, .c 127, .c 5, .c 3,
]
private theorem h0481c20 : checkBlock 3939163 128 b0481c20 = true := by
  decide +kernel

private def b0481c21 : List Row := [
  .c 11, .p pv2 [pv2,pv3,pv5,pv65657], .c 3, .c 5, .c 17, .c 3, .c 397,
  .p pv5 [pv2,pv3,pv7,pv131,pv179], .c 3, .c 53, .c 7, .c 3, .p pv2 [pv2,pv13,pv151517], .c 5,
  .c 3, .c 31, .c 1031, .c 3, .c 5, .p pv5 [pv2,pv3,pv10259], .c 3, .c 17, .c 11, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv13,pv25253], .c 3, .p pv3 [pv2,pv246217], .c 5, .c 3, .c 19, .c 7, .c 3, .c 5,
  .c 229, .c 3, .c 347, .c 47, .c 3, .p pv3 [pv2,pv11,pv89,pv503], .p pv2 [pv2,pv3,pv19,pv11519],
  .c 3, .c 1823, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5, .c 19, .c 3, .p pv3 [pv2,pv5,pv13,pv947],
  .c 7, .c 3, .c 271, .c 11, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv37,pv139,pv383],
  .p pv31 [pv2,pv3,pv5,pv11,pv47,pv127], .c 3, .c 5, .c 163, .c 3, .c 7, .c 257, .c 3, .c 1013,
  .c 13, .c 3, .c 17, .c 5, .c 3, .p pv3 [pv2,pv246223], .c 797, .c 3, .c 5, .c 71, .c 3, .c 211,
  .c 647, .c 3, .c 47, .p pv2 [pv2,pv3,pv109433], .c 3, .c 7, .c 5, .c 3, .c 443, .c 23, .c 3,
  .c 5, .c 7, .c 3, .c 13, .c 727, .c 3, .c 11, .p pv2 [pv2,pv3,pv656603], .c 3, .c 599, .c 5,
  .c 3, .c 857, .c 17, .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv98491], .c 283, .c 3, .c 23,
  .c 7, .c 3, .c 1187, .c 5, .c 3, .c 1117, .c 11, .c 3, .c 5, .c 67, .c 3,
  .p pv7 [pv2,pv5,pv7,pv23,pv2447], .p pv41 [pv2,pv3,pv11,pv14923],
]
private theorem h0481c21 : checkBlock 3939419 128 b0481c21 = true := by
  decide +kernel

private def b0481c22 : List Row := [
  .c 3, .c 7, .c 29, .c 3, .c 11, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 31, .c 3, .c 823, .c 43,
  .c 3, .c 19, .c 137, .c 3, .p pv3 [pv2,pv7,pv4397], .c 5, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv5,pv32831], .c 3, .c 5, .c 11, .c 3, .c 41, .c 7, .c 3, .c 29, .c 23, .c 3,
  .p pv5 [pv2,pv673,pv2927], .c 5, .c 3, .c 11, .c 613, .c 3, .c 5, .c 191, .c 3, .c 7, .c 89,
  .c 3, .c 13, .p pv13 [pv2,pv3,pv7,pv7817], .c 3, .p pv2 [pv2,pv41,pv24023], .c 5, .c 3,
  .p pv2 [pv2,pv1969889], .p pv2 [pv2,pv3,pv5,pv13,pv5051], .c 3, .c 5, .p pv3 [pv2,pv3,pv72959],
  .c 3, .p pv11 [pv2,pv5,pv31,pv71,pv179], .c 11, .c 3, .c 37, .c 1597, .c 3, .c 7, .c 5, .c 3,
  .c 79, .p pv3 [pv2,pv3,pv5,pv7,pv73,pv257], .c 3, .c 5, .c 7, .c 3, .c 19, .c 1877, .c 3,
  .c 181, .p pv2 [pv2,pv3,pv397,pv827], .c 3, .c 353, .c 5, .c 3, .p pv7 [pv2,pv7,pv347,pv811],
  .p pv7 [pv2,pv3,pv5,pv19], .c 3, .c 5, .c 107, .c 3, .p pv11 [pv2,pv5,pv78797], .c 29, .c 3,
  .c 419, .c 7, .c 3, .c 1327, .c 5, .c 3, .c 17, .c 13, .c 3, .c 5, .c 23, .c 3, .c 11, .c 31,
  .c 3, .c 7, .c 929, .c 3, .c 331, .c 5, .c 3, .p pv2 [pv2,pv1969949], .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv656651], .c 3, .c 29, .c 709, .c 3, .p pv2 [pv2,pv19,pv47,pv1103],
  .p pv3 [pv2,pv3,pv43,pv15271], .c 3, .c 13, .c 5, .c 3, .c 7,
]
private theorem h0481c22 : checkBlock 3939675 128 b0481c22 = true := by
  decide +kernel

private def b0481c23 : List Row := [
  .p pv2 [pv2,pv3,pv5,pv43777], .c 3, .c 5, .c 17, .c 3, .c 89, .c 7, .c 3, .c 11, .c 13, .c 3,
  .p pv3 [pv2,pv246247], .c 5, .c 3, .p pv7 [pv2,pv11,pv179089], .c 43, .c 3, .c 5, .c 53, .c 3,
  .c 7, .c 19, .c 3, .c 41, .c 821, .c 3, .c 137, .c 5, .c 3, .p pv3 [pv2,pv13,pv17,pv4457],
  .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv328333], .c 3, .c 13, .c 71, .c 3, .c 31,
  .p pv11 [pv2,pv3,pv181,pv907], .c 3, .c 7, .c 5, .c 3, .c 37,
  .p pv13 [pv2,pv3,pv5,pv7,pv53,pv59], .c 3, .c 5, .c 7, .c 3, .c 167, .p pv5 [pv2,pv3,pv20521],
  .c 3, .c 607, .c 17, .c 3, .c 97, .c 5, .c 3, .c 19, .c 61, .c 3, .c 5, .c 11, .c 3, .c 23,
  .p pv3 [pv2,pv3,pv7,pv93811], .c 3, .c 257, .c 7, .c 3, .c 17, .c 5, .c 3, .c 11, .c 1973, .c 3,
  .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv7,pv11,pv17,pv43], .c 37, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv656683], .c 3, .c 541, .c 5, .c 3, .c 241, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv328343], .c 3, .p pv3 [pv2,pv5,pv137,pv719], .c 11, .c 3,
  .p pv5 [pv2,pv53,pv37171], .c 743, .c 3, .c 43, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv31271], .c 3, .c 47, .c 7, .c 3, .c 13, .p pv11 [pv2,pv3,pv17,pv38629],
  .c 3, .c 19, .c 5, .c 3, .c 509, .p pv23 [pv2,pv3,pv5,pv13,pv10103], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv23,pv43,pv83], .c 3, .c 7, .c 13, .c 3,
]
private theorem h0481c23 : checkBlock 3939931 128 b0481c23 = true := by
  decide +kernel

private def b0481c24 : List Row := [
  .c 223, .c 11, .c 3, .c 31, .c 5, .c 3, .c 23, .c 19, .c 3, .c 5, .p pv3 [pv2,pv3,pv656701],
  .c 3, .c 11, .p pv19 [pv2,pv3,pv101,pv3251], .c 3, .p pv5 [pv2,pv7,pv71,pv991], .c 43, .c 3,
  .c 7, .c 5, .c 3, .c 157, .p pv11 [pv2,pv3,pv5,pv7,pv29,pv647], .c 3, .c 5, .c 7, .c 3, .c 37,
  .c 17, .c 3, .p pv5 [pv2,pv1970123], .p pv17 [pv2,pv3,pv13,pv73,pv173], .c 3,
  .p pv2 [pv2,pv985063], .c 5, .c 3, .c 29, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv227,pv263],
  .c 3, .p pv11 [pv2,pv5,pv67,pv5881], .p pv11 [pv2,pv3,pv7,pv1303], .c 3, .c 11, .c 7, .c 3,
  .c 79, .c 5, .c 3, .p pv3 [pv2,pv11,pv29,pv193], .c 23, .c 3, .c 5, .c 89, .c 3,
  .p pv23 [pv2,pv5,pv7,pv13,pv433], .p pv19 [pv2,pv3,pv127,pv5171], .c 3, .c 7,
  .p pv11 [pv2,pv3,pv109453], .c 3, .c 13, .c 5, .c 3, .p pv11 [pv2,pv971,pv2029], .c 7, .c 3,
  .c 5, .c 179, .c 3, .c 1483, .c 577, .c 3, .c 23, .c 13, .c 3, .c 11, .c 5, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv5,pv109,pv241], .c 3, .c 5, .c 313, .c 3, .c 877, .c 7, .c 3,
  .p pv5 [pv2,pv1970183], .p pv7 [pv2,pv3,pv103,pv797], .c 3, .p pv2 [pv2,pv19,pv139,pv373], .c 5,
  .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv7297], .c 3, .c 5, .c 11, .c 3, .c 7, .c 239, .c 3,
  .p pv2 [pv2,pv17,pv57947], .c 199, .c 3, .c 229, .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv19,pv31,pv223], .c 3, .c 5, .c 13, .c 3, .c 173, .c 113, .c 3,
  .p pv2 [pv2,pv7,pv37,pv7607], .c 19, .c 3, .c 7, .c 5, .c 3, .p pv37 [pv2,pv1970219], .c 31,
]
private theorem h0481c24 : checkBlock 3940187 128 b0481c24 = true := by
  decide +kernel

private def b0481c25 : List Row := [
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv78809], .c 11, .c 3, .p pv3 [pv2,pv13,pv37889],
  .c 109, .c 3, .c 37, .c 5, .c 3, .c 13, .c 67, .c 3, .c 5, .c 43, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv7,pv13,pv1031], .c 3, .p pv11 [pv2,pv11,pv19,pv857], .c 7, .c 3, .c 227, .c 5,
  .c 3, .p pv2 [pv2,pv17,pv23,pv5039], .c 1723, .c 3, .c 5, .p pv2 [pv2,pv3,pv179,pv1223], .c 3,
  .c 139, .p pv5 [pv2,pv3,pv41047], .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv1970261], .c 5, .c 3,
  .c 263, .c 7, .c 3, .c 5, .c 37, .c 3, .c 11, .c 19, .c 3, .c 13, .c 17, .c 3,
  .p pv3 [pv2,pv7,pv11,pv6397], .c 5, .c 3, .c 7, .p pv29 [pv2,pv3,pv5,pv13,pv421], .c 3, .c 5,
  .c 23, .c 3, .c 71, .c 7, .c 3, .p pv3 [pv2,pv123143], .p pv2 [pv2,pv3,pv29,pv7549], .c 3,
  .c 17, .c 5, .c 3, .p pv2 [pv2,pv547,pv1801], .c 83, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv31,pv107], .c 3, .c 7, .c 53, .c 3, .c 11, .p pv29 [pv2,pv3,pv7,pv733],
  .c 3, .c 23, .c 5, .c 3, .c 19, .c 47, .c 3, .c 5, .c 31, .c 3, .p pv13 [pv2,pv5,pv394063],
  .c 41, .c 3, .p pv2 [pv2,pv7,pv23,pv29,pv211], .c 809, .c 3, .c 7, .c 5, .c 3, .c 43, .c 11,
  .c 3, .c 5, .c 7, .c 3, .c 61, .p pv11 [pv2,pv3,pv11,pv59707], .c 3, .p pv2 [pv2,pv1970333],
  .c 59, .c 3, .c 11, .c 5, .c 3, .p pv7 [pv2,pv7,pv79,pv509], .c 311, .c 3, .c 5, .c 383, .c 3,
  .p pv17 [pv2,pv5,pv13,pv30313], .p pv5 [pv2,pv3,pv7,pv43,pv1091], .c 3, .p pv3 [pv2,pv492587],
]
private theorem h0481c25 : checkBlock 3940443 128 b0481c25 = true := by
  decide +kernel

private def b0481c26 : List Row := [
  .c 7, .c 3, .c 13, .c 5, .c 3, .c 53, .c 457, .c 3, .c 5, .c 11, .c 3,
  .p pv3 [pv2,pv5,pv7,pv31,pv227], .c 29, .c 3, .c 7, .c 13, .c 3, .c 19, .c 5, .c 3, .c 11, .c 7,
  .c 3, .c 5, .p pv47 [pv2,pv3,pv656791], .c 3, .c 23, .c 17, .c 3, .c 79, .c 37, .c 3,
  .p pv2 [pv2,pv7,pv47,pv53,pv113], .c 5, .c 3, .c 7, .c 19, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv1117], .c 3, .c 13, .c 7, .c 3, .c 17, .c 139, .c 3,
  .p pv3 [pv2,pv263,pv1873], .c 5, .c 3, .p pv7 [pv2,pv151,pv13049], .p pv47 [pv2,pv3,pv5,pv821],
  .c 3, .c 5, .c 13, .c 3, .c 7, .c 31, .c 3, .c 677, .c 97, .c 3, .p pv5 [pv2,pv1277,pv1543],
  .c 5, .c 3, .c 883, .c 89, .c 3, .c 5, .p pv2 [pv2,pv3,pv79,pv4157], .c 3,
  .p pv13 [pv2,pv5,pv83,pv1187], .c 23, .c 3, .c 19, .c 11, .c 3, .c 7, .c 5, .c 3, .c 13, .c 229,
  .c 3, .c 5, .c 7, .c 3, .c 11, .c 67, .c 3, .c 647, .c 41, .c 3, .c 103, .c 5, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv5,pv131363], .c 3, .c 5, .c 29, .c 3, .c 149, .c 47, .c 3, .c 37, .c 7, .c 3,
  .c 181, .c 5, .c 3, .c 101, .c 53, .c 3, .c 5, .c 1039, .c 3, .p pv2 [pv2,pv5,pv7,pv56299],
  .p pv7 [pv2,pv3,pv328411], .c 3, .c 7, .p pv2 [pv2,pv3,pv218941], .c 3,
  .p pv5 [pv2,pv19,pv137,pv757], .c 5, .c 3, .c 151, .c 7, .c 3,
]
private theorem h0481c26 : checkBlock 3940699 128 b0481c26 = true := by
  decide +kernel

private def b0481c27 : List Row := [
  .c 5, .c 17, .c 3, .c 19, .c 13, .c 3, .p pv5 [pv2,pv61,pv32303], .p pv13 [pv2,pv3,pv31,pv5297],
  .c 3, .c 1409, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv103,pv911], .c 3,
  .c 17, .c 7, .c 3, .c 47, .c 19, .c 3, .c 11, .c 5, .c 3, .c 89, .p pv3 [pv2,pv3,pv5,pv43789],
  .c 3, .c 5, .p pv13 [pv2,pv3,pv164209], .c 3, .c 7, .c 59, .c 3, .c 23,
  .p pv41 [pv2,pv3,pv7,pv13,pv401], .c 3, .c 167, .c 5, .c 3, .p pv7 [pv2,pv1970519], .c 13, .c 3,
  .c 5, .c 11, .c 3, .c 73, .p pv2 [pv2,pv3,pv328421], .c 3, .p pv3 [pv2,pv7,pv19,pv463], .c 17,
  .c 3, .c 7, .c 5, .c 3, .c 11, .c 29, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv11,pv13,pv53],
  .p pv5 [pv2,pv3,pv59,pv1237], .c 3, .c 739, .c 83, .c 3, .c 13, .c 5, .c 3,
  .p pv13 [pv2,pv7,pv89,pv3163], .c 113, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv50527], .c 3,
  .p pv13 [pv2,pv5,pv17,pv97,pv239], .c 11, .c 3, .p pv2 [pv2,pv985279], .c 7, .c 3, .c 31, .c 5,
  .c 3, .c 29, .c 107, .c 3, .c 5, .p pv5 [pv2,pv3,pv3041], .c 3, .c 59, .c 293, .c 3, .c 7,
  .c 61, .c 3, .c 271, .c 5, .c 3, .p pv31 [pv2,pv13,pv29,pv5227], .c 7, .c 3, .c 5, .c 1789,
  .c 3, .c 13, .c 619, .c 3, .c 163, .c 11, .c 3, .p pv5 [pv2,pv7,pv197,pv1429], .c 5, .c 3, .c 7,
  .c 127, .c 3, .c 5, .c 13, .c 3, .c 11, .c 7, .c 3, .c 41, .p pv7 [pv2,pv3,pv19,pv43,pv67],
]
private theorem h0481c27 : checkBlock 3940955 128 b0481c27 = true := by
  decide +kernel

private def b0481c28 : List Row := [
  .c 3, .c 367, .c 5, .c 3, .c 761, .c 379, .c 3, .c 5, .c 19, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv47,pv1747], .c 3, .c 1867, .c 53, .c 3, .p pv2 [pv2,pv1970621], .c 5, .c 3,
  .c 13, .c 43, .c 3, .c 5, .c 23, .c 3, .c 317, .c 17, .c 3, .c 11, .c 211, .c 3, .c 7, .c 5,
  .c 3, .c 47, .c 71, .c 3, .c 5, .c 7, .c 3, .c 487, .p pv5 [pv2,pv3,pv53,pv6197], .c 3, .c 17,
  .p pv2 [pv2,pv3,pv24329], .c 3, .c 19, .c 5, .c 3, .c 31, .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv109481], .c 3, .c 863, .c 101, .c 3, .c 13, .c 7, .c 3, .c 11, .c 5, .c 3,
  .c 1129, .c 19, .c 3, .c 5, .c 823, .c 3, .c 37, .c 13, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv601,pv1093], .c 3, .p pv2 [pv2,pv1970681], .c 5, .c 3, .p pv3 [pv2,pv492671],
  .c 7, .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv43,pv4583], .c 1489, .c 3, .c 1933, .c 79,
  .c 3, .c 61, .c 5, .c 3, .c 7, .c 97, .c 3, .c 5, .c 1163, .c 3, .p pv2 [pv2,pv5,pv11,pv35831],
  .c 7, .c 3, .c 19, .c 29, .c 3, .c 43, .c 5, .c 3, .c 401, .c 13, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv19,pv59,pv293], .c 3, .c 7, .c 11, .c 3, .p pv5 [pv2,pv193,pv10211],
  .p pv47 [pv2,pv3,pv7,pv29,pv809], .c 3, .c 41, .c 5, .c 3, .c 173, .c 359, .c 3, .c 5,
]
private theorem h0481c28 : checkBlock 3941211 128 b0481c28 = true := by
  decide +kernel

private def b0481c29 : List Row := [
  .c 17, .c 3, .p pv7 [pv2,pv5,pv13,pv30319], .p pv11 [pv2,pv3,pv41057], .c 3, .c 29, .c 659,
  .c 3, .c 7, .c 5, .c 3, .c 73, .c 373, .c 3, .c 5, .c 7, .c 3, .c 17, .c 163, .c 3,
  .p pv2 [pv2,pv29,pv67957], .c 11, .c 3, .c 1031, .c 5, .c 3, .c 463, .c 1097, .c 3, .c 5,
  .c 773, .c 3, .c 11, .c 23, .c 3, .p pv3 [pv2,pv37,pv3329], .c 7, .c 3, .c 67, .c 5, .c 3,
  .c 109, .p pv47 [pv2,pv3,pv5,pv19,pv461], .c 3, .c 5, .c 31, .c 3, .c 13, .c 563, .c 3, .c 7,
  .c 17, .c 3, .c 37, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 13, .c 3, .c 919, .c 29, .c 3,
  .c 11, .c 433, .c 3, .c 17, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv37,pv53,pv67], .c 3, .c 5,
  .c 41, .c 3, .c 821, .c 7, .c 3, .c 137, .p pv7 [pv2,pv3,pv227,pv1447], .c 3,
  .p pv3 [pv2,pv89,pv173], .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 37, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv11,pv13,pv2297], .c 3, .c 269, .c 131, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv985417], .c 17, .c 3, .c 5, .c 67, .c 3, .c 31, .c 19, .c 3,
  .p pv5 [pv2,pv7,pv281549], .p pv7 [pv2,pv3,pv17,pv9661], .c 3, .c 7, .c 5, .c 3, .c 41, .c 167,
  .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv277,pv1423], .c 853, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv11,pv59723], .c 3,
]
private theorem h0481c29 : checkBlock 3941467 128 b0481c29 = true := by
  decide +kernel

private def b0481c30 : List Row := [
  .c 701, .c 5, .c 3, .c 11, .c 59, .c 3, .c 5, .c 389, .c 3,
  .p pv3 [pv2,pv5,pv11,pv19,pv23,pv41], .c 13, .c 3, .c 929, .c 7, .c 3, .c 83, .c 5, .c 3, .c 19,
  .c 673, .c 3, .c 5, .c 29, .c 3, .c 449, .c 11, .c 3, .c 7, .c 113, .c 3, .c 1091, .c 5, .c 3,
  .c 97, .c 7, .c 3, .c 5, .c 19, .c 3, .p pv3 [pv2,pv5,pv19709], .p pv2 [pv2,pv3,pv218989], .c 3,
  .c 17, .c 23, .c 3, .c 397, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 239, .c 3,
  .p pv11 [pv2,pv5,pv401,pv983], .c 7, .c 3, .p pv2 [pv2,pv31,pv83,pv383], .c 11, .c 3, .c 47,
  .c 5, .c 3, .c 59, .c 523, .c 3, .c 5, .c 631, .c 3, .c 7, .c 41, .c 3, .c 31, .c 37, .c 3,
  .c 13, .c 5, .c 3, .c 331, .c 61, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv97,pv521], .c 3,
  .p pv2 [pv2,pv5,pv47,pv8387], .c 1117, .c 3, .c 911, .c 13, .c 3, .c 7, .c 5, .c 3, .c 17,
  .c 19, .c 3, .c 5, .c 7, .c 3, .c 131, .p pv5 [pv2,pv3,pv313,pv2099], .c 3, .c 11, .c 31, .c 3,
  .p pv2 [pv2,pv985483], .c 5, .c 3, .c 43, .c 29, .c 3, .c 5, .c 23, .c 3, .c 13, .c 127, .c 3,
  .p pv2 [pv2,pv157,pv6277], .c 7, .c 3, .p pv2 [pv2,pv797,pv2473], .c 5, .c 3,
  .p pv3 [pv2,pv19,pv12967], .c 11, .c 3, .c 5, .c 13,
]
private theorem h0481c30 : checkBlock 3941723 128 b0481c30 = true := by
  decide +kernel

private def b0481c31 : List Row := [
  .c 3, .c 53, .c 97, .c 3, .c 7, .c 1453, .c 3, .c 11, .c 5, .c 3, .c 29, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv19,pv151,pv229], .c 3, .c 17, .c 617, .c 3, .c 37, .c 599, .c 3,
  .p pv5 [pv2,pv7,pv31,pv293], .c 5, .c 3, .c 7, .c 47, .c 3, .c 5, .c 11, .c 3,
  .p pv3 [pv2,pv5,pv139,pv709], .c 7, .c 3, .p pv5 [pv2,pv1971023], .c 191, .c 3, .c 31, .c 5,
  .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv65701], .c 3, .c 5, .p pv3 [pv2,pv3,pv239,pv2749], .c 3,
  .c 7, .c 73, .c 3, .c 89, .c 17, .c 3, .c 787, .c 5, .c 3, .p pv3 [pv2,pv492761], .c 37, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv17,pv4831], .c 3, .c 19, .c 11, .c 3, .c 13, .c 41, .c 3, .c 7, .c 5,
  .c 3, .c 103, .p pv31 [pv2,pv3,pv5,pv7,pv13,pv19], .c 3, .c 5, .c 7, .c 3, .c 23, .c 13, .c 3,
  .p pv3 [pv2,pv11,pv44797], .c 19, .c 3, .c 1831, .c 5, .c 3, .c 281, .c 173, .c 3, .c 5, .c 151,
  .c 3, .c 653, .c 1009, .c 3, .c 197, .c 7, .c 3, .c 29, .c 5, .c 3, .c 79, .c 17, .c 3, .c 5,
  .c 307, .c 3, .c 11, .c 53, .c 3, .c 7, .c 1511, .c 3, .c 59, .c 5, .c 3,
  .p pv3 [pv2,pv31,pv1987], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv18251], .c 3, .c 1627, .c 23,
  .c 3, .p pv2 [pv2,pv337,pv5849], .c 547, .c 3, .c 643,
]
private theorem h0481c31 : checkBlock 3941979 128 b0481c31 = true := by
  decide +kernel

def rows0481 : List Row :=
  b0481c00 ++ b0481c01 ++ b0481c02 ++ b0481c03 ++ b0481c04 ++ b0481c05 ++ b0481c06 ++ b0481c07 ++
  b0481c08 ++ b0481c09 ++ b0481c10 ++ b0481c11 ++ b0481c12 ++ b0481c13 ++ b0481c14 ++ b0481c15 ++
  b0481c16 ++ b0481c17 ++ b0481c18 ++ b0481c19 ++ b0481c20 ++ b0481c21 ++ b0481c22 ++ b0481c23 ++
  b0481c24 ++ b0481c25 ++ b0481c26 ++ b0481c27 ++ b0481c28 ++ b0481c29 ++ b0481c30 ++ b0481c31

theorem checked0481 : checkBlock 3934043 4096 rows0481 = true :=
  checkBlock_append h0481c00 (
    checkBlock_append h0481c01 (
    checkBlock_append h0481c02 (
    checkBlock_append h0481c03 (
    checkBlock_append h0481c04 (
    checkBlock_append h0481c05 (
    checkBlock_append h0481c06 (
    checkBlock_append h0481c07 (
    checkBlock_append h0481c08 (
    checkBlock_append h0481c09 (
    checkBlock_append h0481c10 (
    checkBlock_append h0481c11 (
    checkBlock_append h0481c12 (
    checkBlock_append h0481c13 (
    checkBlock_append h0481c14 (
    checkBlock_append h0481c15 (
    checkBlock_append h0481c16 (
    checkBlock_append h0481c17 (
    checkBlock_append h0481c18 (
    checkBlock_append h0481c19 (
    checkBlock_append h0481c20 (
    checkBlock_append h0481c21 (
    checkBlock_append h0481c22 (
    checkBlock_append h0481c23 (
    checkBlock_append h0481c24 (
    checkBlock_append h0481c25 (
    checkBlock_append h0481c26 (
    checkBlock_append h0481c27 (
    checkBlock_append h0481c28 (
    checkBlock_append h0481c29 (
    checkBlock_append h0481c30 (
    h0481c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
