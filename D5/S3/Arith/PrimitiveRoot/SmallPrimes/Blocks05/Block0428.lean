/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks05/Block0428
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks05/Block0428.checked0428
   digest: Kernel proof of checker success on extended consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table031
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table035
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table043
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table048
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table064
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table076
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table118
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table157
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table158
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table159
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table161
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table165
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table168
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table171
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table177
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table186
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table195
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table218
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table238

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0428c00 : List Row := [
  .c 7, .c 3, .p pv11 [pv2,pv5,pv11,pv31817], .c 13, .c 3, .p pv2 [pv2,pv19,pv46051], .c 67, .c 3,
  .c 41, .c 5, .c 3, .p pv3 [pv2,pv7,pv31249], .c 359, .c 3, .c 5, .p pv17 [pv2,pv3,pv145829],
  .c 3, .c 1291, .c 11, .c 3, .c 419, .c 7, .c 3, .p pv3 [pv2,pv13,pv73,pv461], .c 5, .c 3,
  .c 569, .p pv7 [pv2,pv3,pv5,pv4861], .c 3, .c 5, .c 131, .c 3, .c 31, .c 19, .c 3, .c 7, .c 59,
  .c 3, .c 17, .c 5, .c 3, .c 47, .c 7, .c 3, .c 5, .c 599, .c 3, .c 53, .c 173, .c 3,
  .p pv5 [pv2,pv313,pv5591], .c 11, .c 3, .p pv3 [pv2,pv7,pv2551], .c 5, .c 3, .c 7, .c 29, .c 3,
  .c 5, .c 179, .c 3, .c 11, .c 7, .c 3, .c 61, .p pv3 [pv2,pv3,pv59,pv9887], .c 3, .c 13, .c 5,
  .c 3, .c 19, .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv71,pv79], .c 3, .c 7,
  .p pv5 [pv2,pv3,pv583337], .c 3, .c 83, .c 13, .c 3, .p pv3 [pv2,pv1709], .c 5, .c 3, .c 29,
  .p pv7 [pv2,pv3,pv5,pv29167], .c 3, .c 5, .c 19, .c 3, .c 97, .c 479, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv61,pv73,pv131], .c 3, .c 7, .c 5, .c 3, .c 487, .c 23, .c 3, .c 5, .c 7, .c 3,
  .c 13, .c 257, .c 3, .c 71, .c 37, .c 3, .c 701, .c 5, .c 3, .c 109, .c 11, .c 3, .c 5, .c 13,
  .c 3, .p pv29 [pv2,pv5,pv83,pv4217], .c 17, .c 3, .c 23, .c 7, .c 3,
]
private theorem h0428c00 : checkBlock 3499867 128 b0428c00 = true := by
  decide +kernel

private def b0428c01 : List Row := [
  .c 11, .c 5, .c 3, .c 41, .c 73, .c 3, .c 5, .c 47, .c 3, .c 1459, .c 443, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv31,pv97], .c 3, .c 167, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 11, .c 3,
  .c 563, .c 53, .c 3, .p pv3 [pv2,pv218761], .c 31, .c 3, .p pv5 [pv2,pv7,pv250013], .c 5, .c 3,
  .c 7, .c 1151, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv41669], .c 3, .p pv3 [pv2,pv5,pv11,pv37,pv43],
  .c 7, .c 3, .p pv5 [pv2,pv1750103], .c 23, .c 3, .c 29, .c 5, .c 3, .c 823, .c 1009, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv53,pv1223], .c 3, .c 7, .c 11, .c 3, .c 13, .c 1061, .c 3, .c 43, .c 5, .c 3,
  .c 17, .p pv3 [pv2,pv3,pv5,pv13,pv359], .c 3, .c 5, .c 1277, .c 3, .p pv2 [pv2,pv5,pv175013],
  .c 13, .c 3, .c 263, .p pv7 [pv2,pv3,pv291689], .c 3, .c 7, .c 5, .c 3, .c 53, .c 67, .c 3,
  .c 5, .c 7, .c 3, .c 107, .c 41, .c 3, .p pv3 [pv2,pv197,pv2221], .c 11, .c 3, .c 31, .c 5,
  .c 3, .c 173, .c 37, .c 3, .c 5, .c 17, .c 3, .c 11, .p pv3 [pv2,pv3,pv7,pv83341], .c 3,
  .p pv5 [pv2,pv419,pv4177], .c 7, .c 3, .c 709, .c 5, .c 3, .c 491, .c 13, .c 3, .c 5, .c 23,
  .c 3, .c 17, .p pv7 [pv2,pv3,pv59,pv103], .c 3, .c 7, .c 83, .c 3, .c 61, .c 5, .c 3, .c 953,
  .c 7, .c 3, .c 5, .c 503,
]
private theorem h0428c01 : checkBlock 3500123 128 b0428c01 = true := by
  decide +kernel

private def b0428c02 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv13,pv13463], .p pv3 [pv2,pv3,pv583397], .c 3, .c 11, .c 19, .c 3, .c 13,
  .c 5, .c 3, .c 7, .c 113, .c 3, .c 5, .p pv7 [pv2,pv3,pv7,pv13,pv2137], .c 3, .c 59, .c 7, .c 3,
  .c 281, .c 13, .c 3, .c 73, .c 5, .c 3, .p pv2 [pv2,pv875107], .c 11, .c 3, .c 5, .c 139, .c 3,
  .c 7, .p pv3 [pv2,pv3,pv11,pv71,pv83], .c 3, .p pv5 [pv2,pv19,pv251,pv367], .c 277, .c 3, .c 11,
  .c 5, .c 3, .c 37, .p pv2 [pv2,pv3,pv5,pv19447], .c 3, .c 5, .c 997, .c 3, .c 13,
  .p pv5 [pv2,pv3,pv157,pv929], .c 3, .p pv2 [pv2,pv7,pv125017], .c 593, .c 3, .c 7, .c 5, .c 3,
  .c 31, .c 53, .c 3, .c 5, .c 7, .c 3, .c 43, .c 19, .c 3, .c 271,
  .p pv2 [pv2,pv3,pv11,pv23,pv1153], .c 3, .c 47, .c 5, .c 3, .c 11, .c 17, .c 3, .c 5, .c 1097,
  .c 3, .c 23, .c 37, .c 3, .p pv3 [pv2,pv13,pv97,pv347], .c 7, .c 3, .c 809, .c 5, .c 3, .c 13,
  .c 31, .c 3, .c 5, .p pv2 [pv2,pv3,pv487,pv599], .c 3, .c 29, .c 11, .c 3, .c 7, .c 73, .c 3,
  .p pv2 [pv2,pv17,pv51479], .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 43, .c 3, .c 977,
  .p pv7 [pv2,pv3,pv233,pv313], .c 3, .c 53, .c 521, .c 3, .c 1297, .c 5, .c 3, .c 7, .c 389,
  .c 3, .c 5, .c 19, .c 3, .c 41, .c 7, .c 3, .c 13, .c 11, .c 3, .c 97,
]
private theorem h0428c02 : checkBlock 3500379 128 b0428c02 = true := by
  decide +kernel

private def b0428c03 : List Row := [
  .c 5, .c 3, .c 1489, .c 1871, .c 3, .c 5, .c 59, .c 3, .c 7, .c 13, .c 3, .c 17, .c 577, .c 3,
  .c 1811, .c 5, .c 3, .c 23, .p pv3 [pv2,pv3,pv5,pv116689], .c 3, .c 5, .c 29, .c 3, .c 37,
  .c 67, .c 3, .p pv5 [pv2,pv7,pv250049], .p pv7 [pv2,pv3,pv72931], .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv281,pv6229], .c 47, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv283,pv1237], .c 131,
  .c 3, .c 11, .c 107, .c 3, .c 229, .c 5, .c 3, .c 61, .c 13, .c 3, .c 5, .c 31, .c 3, .c 1753,
  .c 463, .c 3, .p pv2 [pv2,pv397,pv4409], .c 7, .c 3, .c 109, .c 5, .c 3, .c 17, .c 11, .c 3,
  .c 5, .c 677, .c 3, .p pv2 [pv2,pv5,pv7,pv13,pv3847], .p pv2 [pv2,pv3,pv11,pv2411], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv271,pv2153], .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv19,pv73,pv631], .c 7,
  .c 3, .c 5, .c 71, .c 3, .c 571, .p pv3 [pv2,pv3,pv43,pv4523], .c 3, .c 19, .c 13, .c 3, .c 367,
  .c 5, .c 3, .c 7, .c 167, .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv23,pv31,pv491], .c 7,
  .c 3, .c 1033, .c 191, .c 3, .c 613, .c 5, .c 3, .c 11, .c 29, .c 3, .c 5, .c 83, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv53,pv101,pv109], .c 3, .c 41, .p pv13 [pv2,pv3,pv7,pv71,pv587], .c 3,
  .p pv3 [pv2,pv239,pv1831], .c 5, .c 3, .c 1093, .c 1051, .c 3, .c 5, .c 13, .c 3,
]
private theorem h0428c03 : checkBlock 3500635 128 b0428c03 = true := by
  decide +kernel

private def b0428c04 : List Row := [
  .p pv7 [pv2,pv5,pv350089], .c 11, .c 3, .p pv3 [pv2,pv7,pv15629], .c 23, .c 3, .c 7, .c 5, .c 3,
  .c 29, .c 1697, .c 3, .c 5, .c 7, .c 3, .c 19, .c 31, .c 3, .c 311, .c 17, .c 3, .c 107, .c 5,
  .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv19,pv37,pv83], .c 3, .c 5, .c 1249, .c 3, .c 67,
  .p pv29 [pv2,pv3,pv7,pv13,pv229], .c 3, .p pv2 [pv2,pv875239], .c 7, .c 3, .c 17, .c 5, .c 3,
  .p pv3 [pv2,pv23,pv53,pv359], .c 109, .c 3, .c 5, .c 37, .c 3, .c 11, .c 47, .c 3, .c 7, .c 887,
  .c 3, .c 89, .c 5, .c 3, .p pv13 [pv2,pv1750499], .c 7, .c 3, .c 5, .c 73, .c 3, .c 479, .c 431,
  .c 3, .c 13, .c 1091, .c 3, .c 83, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 23, .c 3,
  .p pv3 [pv2,pv5,pv107,pv409], .c 7, .c 3, .c 11, .c 271, .c 3, .c 149, .c 5, .c 3, .c 947,
  .c 179, .c 3, .c 5, .c 1543, .c 3, .c 7, .c 19, .c 3, .c 47, .c 113, .c 3, .c 23, .c 5, .c 3,
  .p pv3 [pv2,pv37,pv2957], .c 11, .c 3, .c 5, .p pv11 [pv2,pv3,pv145879], .c 3,
  .p pv3 [pv2,pv5,pv157,pv223], .c 43, .c 3, .p pv2 [pv2,pv7,pv23,pv83,pv131], .c 31, .c 3, .c 7,
  .c 5, .c 3, .c 59, .c 13, .c 3, .c 5, .c 7, .c 3, .c 401, .c 17, .c 3,
  .p pv3 [pv2,pv127,pv1723], .p pv3 [pv2,pv3,pv583523], .c 3, .c 397, .c 5,
]
private theorem h0428c04 : checkBlock 3500891 128 b0428c04 = true := by
  decide +kernel

private def b0428c05 : List Row := [
  .c 3, .c 19, .c 1741, .c 3, .c 5, .c 11, .c 3, .c 1303, .p pv2 [pv2,pv3,pv7,pv37,pv751], .c 3,
  .c 17, .c 7, .c 3, .c 13, .c 5, .c 3, .c 11, .c 229, .c 3, .c 5, .c 19, .c 3, .c 863,
  .p pv5 [pv2,pv3,pv113,pv1291], .c 3, .c 7, .c 13, .c 3, .c 991, .c 5, .c 3,
  .p pv3 [pv2,pv437651], .c 7, .c 3, .c 5, .c 61, .c 3, .c 23, .c 11, .c 3, .c 1087,
  .p pv2 [pv2,pv3,pv29,pv10061], .c 3, .c 31, .c 5, .c 3, .c 7, .c 1657, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv11909], .c 3, .c 13, .c 7, .c 3, .c 29, .p pv2 [pv2,pv3,pv583543], .c 3,
  .c 19, .c 5, .c 3, .c 17, .c 139, .c 3, .c 5, .c 13, .c 3, .c 7, .p pv3 [pv2,pv3,pv19,pv30713],
  .c 3, .p pv5 [pv2,pv17,pv29,pv53,pv67], .c 11, .c 3, .p pv2 [pv2,pv875323], .c 5, .c 3, .c 73,
  .c 19, .c 3, .c 5, .c 1283, .c 3, .c 11, .c 23, .c 3, .c 661, .c 263, .c 3, .c 7, .c 5, .c 3,
  .c 13, .p pv13 [pv2,pv3,pv5,pv7,pv16673], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv175067],
  .p pv3 [pv2,pv3,pv13,pv1151], .c 3, .c 37, .c 89, .c 3, .c 67, .c 5, .c 3, .c 23, .c 43, .c 3,
  .c 5, .c 101, .c 3, .c 17, .c 29, .c 3, .c 11, .c 7, .c 3, .c 503, .c 5, .c 3, .c 389,
  .p pv11 [pv2,pv3,pv5,pv127,pv919], .c 3, .c 5, .c 1531, .c 3, .c 929,
]
private theorem h0428c05 : checkBlock 3501147 128 b0428c05 = true := by
  decide +kernel

private def b0428c06 : List Row := [
  .c 163, .c 3, .c 7, .c 97, .c 3, .p pv2 [pv2,pv191,pv4583], .c 5, .c 3, .c 31, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv601,pv971], .c 3, .c 29, .c 13, .c 3, .p pv2 [pv2,pv71,pv12329], .c 17, .c 3,
  .c 11, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 421, .c 3, .c 61, .c 7, .c 3,
  .p pv2 [pv2,pv1750733], .p pv2 [pv2,pv3,pv101,pv107], .c 3, .c 17, .c 5, .c 3,
  .p pv7 [pv2,pv197,pv8887], .c 31, .c 3, .c 5, .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv291791],
  .c 3, .c 23, .c 131, .c 3, .p pv5 [pv2,pv1750751], .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 79,
  .c 3, .c 83, .c 41, .c 3, .c 89, .c 19, .c 3, .c 7, .c 5, .c 3, .c 151, .c 17, .c 3, .c 5, .c 7,
  .c 3, .c 53, .c 11, .c 3, .c 277, .c 283, .c 3, .c 13, .c 5, .c 3, .c 37, .c 157, .c 3, .c 5,
  .c 347, .c 3, .c 379, .c 61, .c 3, .p pv5 [pv2,pv11,pv19,pv8377], .c 7, .c 3,
  .p pv3 [pv2,pv17,pv25747], .c 5, .c 3, .c 193, .p pv19 [pv2,pv3,pv5,pv1459], .c 3, .c 5,
  .p pv7 [pv2,pv3,pv37,pv15773], .c 3, .p pv2 [pv2,pv5,pv7,pv50023], .p pv5 [pv2,pv3,pv23,pv4229],
  .c 3, .c 7, .c 11, .c 3, .p pv5 [pv2,pv1750811], .c 5, .c 3, .p pv2 [pv2,pv13,pv67339], .c 7,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv31,pv9413], .c 3, .c 11, .c 17, .c 3, .p pv5 [pv2,pv41,pv42703],
  .c 71, .c 3, .c 1607, .c 5, .c 3,
]
private theorem h0428c06 : checkBlock 3501403 128 b0428c06 = true := by
  decide +kernel

private def b0428c07 : List Row := [
  .c 7, .c 1153, .c 3, .c 5, .c 13, .c 3, .c 433, .c 7, .c 3, .c 17, .p pv43 [pv2,pv3,pv583613],
  .c 3, .c 619, .c 5, .c 3, .p pv3 [pv2,pv47,pv67,pv139], .c 103, .c 3, .c 5, .c 1399, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv227,pv857], .c 3, .c 11, .c 59, .c 3, .p pv3 [pv2,pv218857], .c 5, .c 3,
  .c 13, .c 29, .c 3, .c 5, .c 23, .c 3, .p pv7 [pv2,pv5,pv241,pv1453],
  .p pv2 [pv2,pv3,pv13,pv22447], .c 3, .c 73, .p pv13 [pv2,pv3,pv19,pv3413], .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv43,pv20359], .c 11, .c 3, .c 5, .c 7, .c 3, .c 131, .c 53, .c 3, .c 337,
  .c 41, .c 3, .c 11, .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv58363], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv583631], .c 3, .c 31, .c 1163, .c 3, .c 13, .c 7, .c 3, .c 199, .c 5, .c 3,
  .p pv3 [pv2,pv29,pv7547], .p pv29 [pv2,pv3,pv5,pv13,pv41,pv73], .c 3, .c 5, .c 11, .c 3,
  .p pv13 [pv2,pv5,pv7,pv25013], .c 13, .c 3, .c 7, .c 47, .c 3, .c 19, .c 5, .c 3, .c 11, .c 7,
  .c 3, .c 5, .c 17, .c 3, .c 41, .c 31, .c 3, .c 137, .c 557, .c 3,
  .p pv5 [pv2,pv7,pv13,pv71,pv271], .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 43, .c 3, .c 17, .c 7,
  .c 3, .p pv5 [pv2,pv59,pv503], .c 67, .c 3, .c 541, .c 5, .c 3, .c 317, .c 13, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv583651], .c 3, .c 7, .c 751,
]
private theorem h0428c07 : checkBlock 3501659 128 b0428c07 = true := by
  decide +kernel

private def b0428c08 : List Row := [
  .c 3, .p pv2 [pv2,pv11,pv79589], .p pv3 [pv2,pv3,pv7,pv27793], .c 3, .c 47, .c 5, .c 3, .c 227,
  .c 1213, .c 3, .c 5, .c 397, .c 3, .c 1013, .c 571, .c 3, .c 19, .c 11, .c 3, .c 7, .c 5, .c 3,
  .c 727, .p pv13 [pv2,pv3,pv5,pv7,pv11,pv379], .c 3, .c 5, .c 7, .c 3, .c 11, .c 101, .c 3,
  .c 31, .c 13, .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv7,pv181,pv691], .c 79, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv291833], .c 3, .p pv3 [pv2,pv5,pv17,pv103], .c 23, .c 3,
  .p pv5 [pv2,pv43,pv947], .c 7, .c 3, .c 37, .c 5, .c 3, .c 83, .p pv2 [pv2,pv3,pv5,pv58367],
  .c 3, .c 5, .c 601, .c 3, .c 13, .c 467, .c 3, .c 7, .c 31, .c 3, .p pv2 [pv2,pv19,pv157,pv587],
  .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 13, .c 3, .c 19, .c 59, .c 3, .c 239, .c 29, .c 3,
  .p pv3 [pv2,pv7,pv23,pv2719], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 37, .c 3,
  .p pv2 [pv2,pv5,pv67,pv5227], .c 7, .c 3, .c 41, .c 19, .c 3, .c 11, .c 5, .c 3, .c 13, .c 47,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv1201], .c 3, .c 7, .p pv3 [pv2,pv3,pv13,pv59,pv761], .c 3, .c 29,
  .p pv23 [pv2,pv3,pv7,pv1489], .c 3, .c 271, .c 5, .c 3, .c 257, .c 23, .c 3, .c 5, .c 11, .c 3,
  .p pv7 [pv2,pv5,pv89,pv787], .c 17, .c 3, .c 67, .p pv13 [pv2,pv3,pv11,pv47,pv1129], .c 3, .c 7,
  .c 5, .c 3, .c 11,
]
private theorem h0428c08 : checkBlock 3501915 128 b0428c08 = true := by
  decide +kernel

private def b0428c09 : List Row := [
  .c 311, .c 3, .c 5, .c 7, .c 3, .c 59, .p pv5 [pv2,pv3,pv583697], .c 3, .c 13,
  .p pv2 [pv2,pv3,pv97283], .c 3, .c 61, .c 5, .c 3, .c 157, .c 199, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv103,pv1889], .c 3, .c 647, .c 11, .c 3, .c 71, .c 7, .c 3, .c 233, .c 5, .c 3,
  .c 293, .p pv3 [pv2,pv3,pv5,pv116741], .c 3, .c 5, .p pv5 [pv2,pv3,pv291853], .c 3,
  .p pv3 [pv2,pv5,pv7,pv53,pv59], .c 29, .c 3, .c 7, .c 719, .c 3, .p pv2 [pv2,pv13,pv47,pv1433],
  .c 5, .c 3, .p pv2 [pv2,pv593,pv2953], .c 7, .c 3, .c 5, .c 409, .c 3, .c 347,
  .p pv5 [pv2,pv3,pv17,pv29,pv37], .c 3, .p pv2 [pv2,pv101,pv8669], .c 11, .c 3,
  .p pv5 [pv2,pv7,pv97,pv2579], .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv6949],
  .c 3, .c 11, .c 7, .c 3, .c 43, .c 37, .c 3, .p pv3 [pv2,pv11,pv39799], .c 5, .c 3,
  .p pv7 [pv2,pv31,pv56489], .c 73, .c 3, .c 5, .c 19, .c 3, .c 7, .p pv5 [pv2,pv3,pv32429], .c 3,
  .p pv3 [pv2,pv13681], .c 379, .c 3, .c 13, .c 5, .c 3, .c 31, .c 83, .c 3, .c 5, .c 17, .c 3,
  .c 1061, .p pv2 [pv2,pv3,pv583727], .c 3, .c 11, .c 13, .c 3, .c 7, .c 5, .c 3, .c 97, .c 163,
  .c 3, .c 5, .c 7, .c 3, .c 17, .c 43, .c 3, .c 971, .c 53, .c 3, .c 19, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv13,pv17,pv283], .c 11, .c 3, .c 5, .c 23, .c 3, .c 13, .c 563, .c 3,
]
private theorem h0428c09 : checkBlock 3502171 128 b0428c09 = true := by
  decide +kernel

private def b0428c10 : List Row := [
  .p pv2 [pv2,pv1751213], .c 7, .c 3, .c 11, .c 5, .c 3, .p pv13 [pv2,pv223,pv7853], .c 19, .c 3,
  .c 5, .c 13, .c 3, .c 1471, .c 241, .c 3, .c 7, .c 17, .c 3, .c 23, .c 5, .c 3, .c 1039, .c 7,
  .c 3, .c 5, .c 11, .c 3, .c 499, .c 1291, .c 3, .c 47, .p pv19 [pv2,pv3,pv11,pv13267], .c 3,
  .c 17, .c 5, .c 3, .c 7, .c 71, .c 3, .c 5, .c 41, .c 3, .p pv11 [pv2,pv5,pv11,pv17,pv1873],
  .c 7, .c 3, .c 19, .p pv3 [pv2,pv3,pv583753], .c 3, .c 1373, .c 5, .c 3, .p pv3 [pv2,pv54727],
  .c 37, .c 3, .c 5, .c 433, .c 3, .c 7, .c 11, .c 3, .c 131, .p pv2 [pv2,pv3,pv7,pv41,pv113],
  .c 3, .p pv3 [pv2,pv437819], .c 5, .c 3, .c 61, .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv31,pv6277],
  .c 3, .p pv2 [pv2,pv5,pv350257], .c 97, .c 3, .c 13, .c 101, .c 3, .c 7, .c 5, .c 3, .c 41,
  .c 29, .c 3, .c 5, .c 7, .c 3, .c 23, .c 13, .c 3, .p pv5 [pv2,pv109,pv16067], .c 11, .c 3,
  .c 73, .c 5, .c 3, .p pv7 [pv2,pv7,pv103,pv347], .p pv7 [pv2,pv3,pv5,pv11,pv29,pv61], .c 3,
  .c 5, .p pv5 [pv2,pv3,pv67,pv8713], .c 3, .c 11, .p pv5 [pv2,pv3,pv7,pv20849], .c 3, .c 1123,
  .c 7, .c 3, .c 71, .c 5, .c 3, .c 29, .c 43, .c 3, .c 5, .p pv5 [pv2,pv3,pv2027], .c 3, .c 113,
  .c 17, .c 3, .c 7, .c 19, .c 3, .p pv3 [pv2,pv179,pv1223], .c 5, .c 3, .c 37, .c 7,
]
private theorem h0428c10 : checkBlock 3502427 128 b0428c10 = true := by
  decide +kernel

private def b0428c11 : List Row := [
  .c 3, .c 5, .p pv11 [pv2,pv3,pv11,pv73,pv727], .c 3, .c 283, .c 23, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv583783], .c 3, .c 1831, .c 5, .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv12973], .c 3,
  .c 5, .c 53, .c 3, .c 31, .c 7, .c 3, .p pv5 [pv2,pv19,pv92177], .p pv11 [pv2,pv3,pv48649],
  .c 3, .c 13, .c 5, .c 3, .c 23, .c 11, .c 3, .c 5, .c 151, .c 3, .c 7, .c 37, .c 3, .c 193,
  .c 13, .c 3, .c 11, .c 5, .c 3, .c 47, .c 59, .c 3, .c 5, .p pv5 [pv2,pv3,pv145949], .c 3,
  .c 79, .c 19, .c 3, .c 127, .p pv2 [pv2,pv3,pv291899], .c 3, .c 7, .c 5, .c 3, .c 17, .c 443,
  .c 3, .c 5, .c 7, .c 3, .c 13, .p pv2 [pv2,pv3,pv291901], .c 3, .c 1693, .c 353, .c 3, .c 29,
  .c 5, .c 3, .c 11, .c 23, .c 3, .c 5, .c 13, .c 3, .c 149, .c 373, .c 3,
  .p pv5 [pv2,pv1181,pv1483], .c 7, .c 3, .p pv2 [pv2,pv29,pv30197], .c 5, .c 3, .c 19, .c 883,
  .c 3, .c 5, .c 17, .c 3, .p pv13 [pv2,pv5,pv7,pv163,pv307], .c 11, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv19,pv30727], .c 3, .c 761, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 19, .c 3,
  .c 17, .c 1033, .c 3, .c 31, .c 43, .c 3, .c 349, .c 5, .c 3, .c 7, .c 619, .c 3, .c 5, .c 71,
  .c 3, .c 1627, .c 7, .c 3, .c 787,
]
private theorem h0428c11 : checkBlock 3502683 128 b0428c11 = true := by
  decide +kernel

private def b0428c12 : List Row := [
  .c 11, .c 3, .p pv5 [pv2,pv277,pv6323], .c 5, .c 3, .p pv2 [pv2,pv59,pv14843], .c 89, .c 3,
  .c 5, .c 47, .c 3, .c 7, .p pv2 [pv2,pv3,pv194609], .c 3, .c 13, .c 17, .c 3, .c 19, .c 5, .c 3,
  .p pv2 [pv2,pv73,pv23993], .c 1621, .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv61,pv563], .c 3, .c 487,
  .c 13, .c 3, .c 29, .c 41, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv109469], .c 19, .c 3, .c 5,
  .c 7, .c 3, .p pv2 [pv2,pv5,pv17,pv10303], .c 239, .c 3, .c 11, .p pv2 [pv2,pv3,pv67,pv4357],
  .c 3, .c 163, .c 5, .c 3, .p pv7 [pv2,pv7,pv11,pv23,pv43], .c 127, .c 3, .c 5, .c 61, .c 3,
  .c 47, .p pv5 [pv2,pv3,pv7,pv13901], .c 3, .p pv3 [pv2,pv218941], .c 7, .c 3,
  .p pv5 [pv2,pv31,pv56501], .c 5, .c 3, .c 71, .c 11, .c 3, .c 5, .c 173, .c 3, .c 41,
  .p pv2 [pv2,pv3,pv11,pv53077], .c 3, .c 7, .p pv11 [pv2,pv3,pv17,pv53], .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv47,pv83,pv449], .c 7, .c 3, .c 5, .c 23, .c 3, .p pv17 [pv2,pv5,pv13,pv26947],
  .c 29, .c 3, .p pv2 [pv2,pv875779], .p pv7 [pv2,pv3,pv583853], .c 3, .c 13, .c 5, .c 3, .c 7,
  .c 191, .c 3, .c 5, .c 11, .c 3, .c 53, .c 7, .c 3, .p pv2 [pv2,pv1751573], .c 13, .c 3, .c 23,
  .c 5, .c 3, .c 11, .p pv11 [pv2,pv3,pv5,pv37,pv263], .c 3, .c 5, .c 43, .c 3, .c 7, .c 17, .c 3,
  .c 307, .c 1583, .c 3, .c 1453, .c 5, .c 3, .p pv2 [pv2,pv13,pv67369],
  .p pv19 [pv2,pv3,pv5,pv17,pv6869], .c 3,
]
private theorem h0428c12 : checkBlock 3502939 128 b0428c12 = true := by
  decide +kernel

private def b0428c13 : List Row := [
  .c 5, .c 37, .c 3, .c 13, .c 11, .c 3, .c 17, .c 179, .c 3, .c 7, .c 5, .c 3, .c 277,
  .p pv2 [pv2,pv3,pv5,pv7,pv19,pv439], .c 3, .c 5, .c 7, .c 3, .c 1669, .c 211, .c 3,
  .p pv2 [pv2,pv11,pv103,pv773], .c 19, .c 3, .c 59, .c 5, .c 3, .p pv11 [pv2,pv7,pv31,pv1009],
  .c 197, .c 3, .c 5, .c 283, .c 3, .p pv3 [pv2,pv5,pv109,pv1607],
  .p pv3 [pv2,pv3,pv7,pv239,pv349], .c 3, .p pv2 [pv2,pv13,pv134741], .c 7, .c 3,
  .p pv3 [pv2,pv437909], .c 5, .c 3, .c 13, .p pv17 [pv2,pv3,pv5,pv11,pv1327], .c 3, .c 5, .c 29,
  .c 3, .c 11, .p pv2 [pv2,pv3,pv13,pv17,pv1321], .c 3, .c 7, .p pv2 [pv2,pv3,pv157,pv3719], .c 3,
  .p pv5 [pv2,pv11,pv59,pv2699], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 1201, .c 3,
  .p pv7 [pv2,pv5,pv87583], .p pv2 [pv2,pv3,pv191,pv1019], .c 3, .c 41, .p pv13 [pv2,pv3,pv36493],
  .c 3, .c 47, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5, .c 83, .c 3, .c 151, .c 7, .c 3, .c 11,
  .c 163, .c 3, .c 67, .c 5, .c 3, .c 109, .p pv3 [pv2,pv3,pv5,pv13,pv691], .c 3, .c 5, .c 17,
  .c 3, .c 7, .c 13, .c 3, .c 101, .p pv11 [pv2,pv3,pv7,pv179,pv233], .c 3, .p pv3 [pv2,pv109481],
  .c 5, .c 3, .p pv7 [pv2,pv1751699], .c 11, .c 3, .c 5, .p pv13 [pv2,pv3,pv23,pv53,pv479], .c 3,
  .c 17, .c 61, .c 3, .c 241, .c 37, .c 3, .c 7, .c 5, .c 3, .c 19,
  .p pv7 [pv2,pv3,pv5,pv7,pv67,pv83], .c 3, .c 5, .c 7, .c 3, .c 967, .c 937, .c 3, .c 509,
  .p pv7 [pv2,pv3,pv13,pv19,pv197],
]
private theorem h0428c13 : checkBlock 3503195 128 b0428c13 = true := by
  decide +kernel

private def b0428c14 : List Row := [
  .c 3, .p pv2 [pv2,pv23,pv113,pv337], .c 5, .c 3, .c 53, .c 13, .c 3, .c 5, .c 11, .c 3, .c 229,
  .p pv5 [pv2,pv3,pv7,pv10427], .c 3, .p pv2 [pv2,pv379,pv2311], .c 7, .c 3,
  .p pv2 [pv2,pv1751741], .c 5, .c 3, .c 11, .c 41, .c 3, .c 5, .c 67, .c 3, .c 107,
  .p pv3 [pv2,pv3,pv151,pv1289], .c 3, .c 7, .p pv23 [pv2,pv3,pv281,pv1039], .c 3, .c 13, .c 5,
  .c 3, .c 29, .c 7, .c 3, .c 5, .c 31, .c 3, .p pv2 [pv2,pv5,pv17,pv37,pv557], .c 11, .c 3,
  .c 401, .c 13, .c 3, .c 19, .c 5, .c 3, .c 7, .c 599, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv13903],
  .c 3, .p pv3 [pv2,pv5,pv87589], .c 7, .c 3, .c 23, .p pv7 [pv2,pv3,pv47,pv1553], .c 3, .c 41,
  .c 5, .c 3, .p pv2 [pv2,pv13,pv134753], .c 17, .c 3, .c 5, .c 109, .c 3, .c 7, .c 1301, .c 3,
  .c 43, .c 11, .c 3, .p pv2 [pv2,pv1751801], .c 5, .c 3, .p pv3 [pv2,pv107,pv4093], .c 349, .c 3,
  .c 5, .c 13, .c 3, .c 11, .p pv13 [pv2,pv3,pv583937], .c 3, .p pv2 [pv2,pv7,pv250259],
  .p pv17 [pv2,pv3,pv32441], .c 3, .c 7, .c 5, .c 3, .p pv17 [pv2,pv19,pv137,pv673], .c 37, .c 3,
  .c 5, .c 7, .c 3, .c 31, .c 151, .c 3, .c 19, .c 23, .c 3, .c 89, .c 5, .c 3, .c 13, .c 53,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv19,pv127], .c 3, .c 257, .c 17, .c 3, .c 11, .c 7, .c 3,
  .c 29, .c 5, .c 3, .p pv11 [pv2,pv11,pv67,pv2377], .p pv29 [pv2,pv3,pv5,pv17,pv229], .c 3, .c 5,
]
private theorem h0428c14 : checkBlock 3503451 128 b0428c14 = true := by
  decide +kernel

private def b0428c15 : List Row := [
  .c 643, .c 3, .p pv7 [pv2,pv5,pv7,pv50053], .c 31, .c 3, .c 7, .p pv7 [pv2,pv3,pv61,pv3191],
  .c 3, .c 389, .c 5, .c 3, .c 79, .c 7, .c 3, .c 5, .c 41, .c 3, .c 907, .c 1217, .c 3, .c 13,
  .c 367, .c 3, .c 11, .c 5, .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv13,pv1123], .c 3, .c 5, .c 1303,
  .c 3, .c 19, .c 7, .c 3, .c 53, .c 61, .c 3, .p pv5 [pv2,pv1751891], .c 5, .c 3, .c 37, .c 101,
  .c 3, .c 5, .c 11, .c 3, .c 7, .c 47, .c 3, .p pv5 [pv2,pv31,pv1823], .c 19, .c 3,
  .p pv3 [pv2,pv13,pv43,pv1567], .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv23,pv2539], .c 3, .c 5,
  .c 167, .c 3, .p pv7 [pv2,pv5,pv11,pv53,pv601], .c 59, .c 3, .c 31,
  .p pv19 [pv2,pv3,pv13,pv29,pv1549], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv163,pv2687], .c 13,
  .c 3, .c 5, .c 7, .c 3, .c 859, .c 11, .c 3, .c 29, .p pv2 [pv2,pv3,pv31,pv9419], .c 3, .c 1283,
  .c 5, .c 3, .c 1229, .p pv11 [pv2,pv3,pv5,pv9733], .c 3, .c 5, .c 17, .c 3,
  .p pv19 [pv2,pv5,pv13,pv26953], .p pv5 [pv2,pv3,pv7,pv59,pv101], .c 3, .c 47, .c 7, .c 3, .c 13,
  .c 5, .c 3, .p pv2 [pv2,pv613,pv1429], .p pv3 [pv2,pv3,pv5,pv116797], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv13,pv7487], .c 3, .c 17, .c 19, .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv875983], .c 5, .c 3, .p pv19 [pv2,pv17,pv257,pv401], .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv583991], .c 3, .c 11, .p pv5 [pv2,pv3,pv8111], .c 3, .c 103,
  .p pv3 [pv2,pv3,pv23,pv25391], .c 3,
]
private theorem h0428c15 : checkBlock 3503707 128 b0428c15 = true := by
  decide +kernel

private def b0428c16 : List Row := [
  .p pv2 [pv2,pv7,pv11,pv61,pv373], .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv38933], .c 3, .c 5,
  .p pv17 [pv2,pv3,pv7,pv20857], .c 3, .c 13, .c 7, .c 3, .c 293, .c 17, .c 3, .c 101, .c 5, .c 3,
  .c 19, .p pv11 [pv2,pv3,pv5,pv73], .c 3, .c 5, .c 13, .c 3, .c 7, .p pv2 [pv2,pv3,pv29,pv10069],
  .c 3, .c 11, .c 89, .c 3, .c 17, .c 5, .c 3, .c 1117, .p pv23 [pv2,pv3,pv5,pv271,pv431], .c 3,
  .c 5, .c 19, .c 3, .c 29, .p pv2 [pv2,pv3,pv53,pv3673], .c 3, .p pv5 [pv2,pv7,pv13,pv1481],
  .c 137, .c 3, .c 7, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 7, .c 3, .c 1493, .c 23, .c 3,
  .c 211, .p pv3 [pv2,pv3,pv194671], .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv7,pv1277], .c 17,
  .c 3, .c 5, .c 419, .c 3, .p pv2 [pv2,pv5,pv67,pv523], .p pv5 [pv2,pv3,pv7,pv83431], .c 3,
  .p pv2 [pv2,pv41,pv151,pv283], .c 7, .c 3, .c 19, .c 5, .c 3, .c 23, .c 577, .c 3, .c 5, .c 11,
  .c 3, .p pv2 [pv2,pv5,pv7,pv113,pv443], .p pv2 [pv2,pv3,pv19,pv47,pv109], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv11,pv53093], .c 3, .c 107, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 29, .c 3,
  .c 167, .c 13, .c 3, .c 67, .p pv17 [pv2,pv3,pv16223], .c 3, .p pv3 [pv2,pv7,pv125149], .c 5,
  .c 3, .c 7, .c 953, .c 3, .c 5, .c 59, .c 3, .c 199, .c 7, .c 3, .c 89, .c 43, .c 3, .c 79,
  .c 5, .c 3, .c 31, .c 23, .c 3, .c 5, .p pv5 [pv2,pv3,pv146009],
]
private theorem h0428c16 : checkBlock 3503963 128 b0428c16 = true := by
  decide +kernel

private def b0428c17 : List Row := [
  .c 3, .c 7, .p pv5 [pv2,pv3,pv97,pv223], .c 3, .c 17, .c 41, .c 3, .c 37, .c 5, .c 3,
  .p pv7 [pv2,pv1752119], .c 13, .c 3, .c 5, .c 1753, .c 3, .p pv2 [pv2,pv5,pv107,pv131],
  .p pv2 [pv2,pv3,pv292021], .c 3, .c 23, .c 11, .c 3, .c 7, .c 5, .c 3, .c 433, .c 31, .c 3,
  .c 5, .c 7, .c 3, .c 11, .c 179, .c 3, .p pv13 [pv2,pv89,pv19687],
  .p pv11 [pv2,pv3,pv173,pv211], .c 3, .c 13, .c 5, .c 3, .c 701, .c 67, .c 3, .c 5, .c 37, .c 3,
  .c 41, .p pv5 [pv2,pv3,pv7,pv17,pv409], .c 3, .p pv2 [pv2,pv876079], .c 7, .c 3, .c 137, .c 5,
  .c 3, .c 17, .c 29, .c 3, .c 5, .c 163, .c 3, .c 19, .c 83, .c 3, .c 7, .c 23, .c 3, .c 347,
  .c 5, .c 3, .c 1867, .c 7, .c 3, .c 5, .c 47, .c 3, .c 13, .p pv7 [pv2,pv3,pv23,pv12697], .c 3,
  .p pv3 [pv2,pv438047], .c 19, .c 3, .c 1871, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 13, .c 3,
  .c 503, .c 7, .c 3, .p pv5 [pv2,pv719,pv2437], .c 797, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv23,pv29,pv37,pv71], .c 1237, .c 3, .c 5, .p pv3 [pv2,pv3,pv31,pv83,pv227], .c 3,
  .c 7, .c 197, .c 3, .p pv2 [pv2,pv13,pv19,pv3547], .p pv3 [pv2,pv3,pv7,pv73,pv127], .c 3,
  .p pv2 [pv2,pv1752221], .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv61,pv383], .c 3, .c 5, .c 11,
  .c 3, .c 47, .c 337, .c 3, .p pv2 [pv2,pv7,pv53,pv4723], .c 113, .c 3, .c 7,
]
private theorem h0428c17 : checkBlock 3504219 128 b0428c17 = true := by
  decide +kernel

private def b0428c18 : List Row := [
  .c 5, .c 3, .c 11, .p pv11 [pv2,pv3,pv5,pv7,pv149], .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv11,pv31859], .c 19, .c 3, .p pv3 [pv2,pv219031], .c 17, .c 3, .c 839, .c 5,
  .c 3, .c 83, .c 61, .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv41,pv419], .c 3, .c 613, .c 11, .c 3,
  .c 13, .c 7, .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv1752269], .c 59, .c 3, .c 5, .c 1039, .c 3,
  .p pv19 [pv2,pv5,pv7,pv17,pv19,pv31], .c 13, .c 3, .c 7, .c 151, .c 3, .c 29, .c 5, .c 3, .c 19,
  .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv18253], .c 3, .c 31, .c 1319, .c 3, .c 709, .c 11, .c 3,
  .p pv3 [pv2,pv7,pv13,pv29,pv83], .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 19, .c 3, .c 11, .c 7,
  .c 3, .c 911, .p pv31 [pv2,pv3,pv13,pv17,pv881], .c 3, .c 523, .c 5, .c 3, .c 43, .c 13, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv67,pv1453], .c 3, .c 7, .c 31, .c 3, .p pv5 [pv2,pv1752323], .c 47,
  .c 3, .c 227, .c 5, .c 3, .c 59, .c 313, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv53101], .c 3, .c 23,
  .p pv5 [pv2,pv3,pv43,pv283], .c 3, .c 11, .c 29, .c 3, .c 7, .c 5, .c 3,
  .p pv7 [pv2,pv11,pv19913], .p pv2 [pv2,pv3,pv5,pv7,pv5563], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv101,pv347], .c 17, .c 3, .c 97, .c 13, .c 3, .c 251, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv59,pv4243], .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv194707], .c 3,
]
private theorem h0428c18 : checkBlock 3504475 128 b0428c18 = true := by
  decide +kernel

private def b0428c19 : List Row := [
  .c 53, .c 457, .c 3, .c 17, .c 7, .c 3, .c 11, .c 5, .c 3, .c 599, .c 37, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv79,pv3697], .c 3, .c 13, .c 23, .c 3, .c 7, .p pv19 [pv2,pv3,pv9127], .c 3,
  .c 71, .c 5, .c 3, .p pv2 [pv2,pv19,pv149,pv619], .c 7, .c 3, .c 5, .c 11, .c 3, .c 1289,
  .p pv13 [pv2,pv3,pv146033], .c 3, .c 19, .c 647, .c 3, .c 41, .c 5, .c 3, .c 7,
  .p pv17 [pv2,pv3,pv5,pv116827], .c 3, .c 5, .c 1637, .c 3, .p pv3 [pv2,pv5,pv11,pv89,pv179],
  .c 7, .c 3, .c 197, .c 31, .c 3, .c 383, .c 5, .c 3, .c 13, .c 83, .c 3, .c 5, .c 947, .c 3,
  .c 7, .c 11, .c 3, .p pv3 [pv2,pv17,pv25771], .c 1487, .c 3, .c 241, .c 5, .c 3,
  .p pv2 [pv2,pv157,pv5581], .c 137, .c 3, .c 5, .c 61, .c 3, .c 277, .c 1123, .c 3, .c 43,
  .p pv7 [pv2,pv3,pv48679], .c 3, .c 7, .c 5, .c 3, .c 37, .c 23, .c 3, .c 5, .c 7, .c 3, .c 19,
  .c 281, .c 3, .c 13, .c 11, .c 3, .p pv2 [pv2,pv31,pv56531], .c 5, .c 3,
  .p pv3 [pv2,pv7,pv15647], .c 47, .c 3, .c 5, .c 353, .c 3, .c 11, .c 13, .c 3, .c 23, .c 7,
  .c 3, .c 31, .c 5, .c 3, .c 331, .p pv47 [pv2,pv3,pv5,pv1217], .c 3, .c 5, .c 41, .c 3, .c 67,
  .c 37, .c 3, .c 7, .p pv2 [pv2,pv3,pv47,pv1381], .c 3, .c 461, .c 5,
]
private theorem h0428c19 : checkBlock 3504731 128 b0428c19 = true := by
  decide +kernel

private def b0428c20 : List Row := [
  .c 3, .c 163, .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv11,pv53,pv167], .c 3, .c 263, .c 101, .c 3,
  .c 11, .c 17, .c 3, .c 59, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 29, .c 3,
  .p pv31 [pv2,pv5,pv350503], .c 7, .c 3, .c 1699, .c 23, .c 3, .c 17, .c 5, .c 3, .c 41, .c 11,
  .c 3, .c 5, .c 71, .c 3, .c 7, .c 19, .c 3, .p pv2 [pv2,pv919,pv1907], .c 317, .c 3, .c 11,
  .c 5, .c 3, .p pv7 [pv2,pv1752539], .c 373, .c 3, .c 5, .c 89, .c 3,
  .p pv2 [pv2,pv5,pv41,pv83,pv103], .c 1021, .c 3, .p pv3 [pv2,pv7,pv62591], .c 13, .c 3, .c 7,
  .c 5, .c 3, .p pv2 [pv2,pv23,pv31,pv1229], .c 17, .c 3, .c 5, .c 7, .c 3, .c 37,
  .p pv3 [pv2,pv3,pv194729], .c 3, .p pv5 [pv2,pv1752563], .p pv23 [pv2,pv3,pv11,pv17,pv71], .c 3,
  .p pv2 [pv2,pv211,pv4153], .c 5, .c 3, .c 11, .c 401, .c 3, .c 5, .c 113, .c 3, .c 13, .c 173,
  .c 3, .c 823, .c 7, .c 3, .c 139, .c 5, .c 3, .p pv3 [pv2,pv73,pv3001],
  .p pv3 [pv2,pv3,pv5,pv31,pv3769], .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv7,pv25037], .c 11,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv43,pv6793], .c 3, .c 103, .c 5, .c 3, .c 71, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv733,pv797], .c 3, .c 1187, .c 17, .c 3, .c 367, .p pv2 [pv2,pv3,pv584203],
  .c 3, .c 23, .c 5, .c 3, .c 7, .c 43, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv41729], .c 3, .c 73,
]
private theorem h0428c20 : checkBlock 3504987 128 b0428c20 = true := by
  decide +kernel

private def b0428c21 : List Row := [
  .c 7, .c 3, .c 17, .c 11, .c 3, .c 19, .c 5, .c 3, .c 29, .c 53, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv193,pv1009], .c 3, .c 7, .p pv5 [pv2,pv3,pv19,pv7687], .c 3,
  .p pv2 [pv2,pv359,pv2441], .c 389, .c 3, .c 661, .c 5, .c 3, .c 97, .c 19, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv103,pv709], .c 3, .p pv2 [pv2,pv5,pv35053], .c 229, .c 3, .c 13, .c 79, .c 3,
  .c 7, .c 5, .c 3, .p pv11 [pv2,pv1752659], .p pv11 [pv2,pv3,pv5,pv7,pv13,pv107], .c 3, .c 5,
  .c 7, .c 3, .c 109, .c 13, .c 3, .c 11, .c 83, .c 3, .c 37, .c 5, .c 3, .c 17,
  .p pv41 [pv2,pv3,pv5,pv23369], .c 3, .c 5, .c 179, .c 3, .c 23, .p pv2 [pv2,pv3,pv7,pv11923],
  .c 3, .c 19, .c 7, .c 3, .c 67, .c 5, .c 3, .c 1567, .c 11, .c 3, .c 5, .c 31, .c 3,
  .p pv7 [pv2,pv5,pv7,pv50077], .c 1471, .c 3, .c 7, .c 103, .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv13693], .c 7, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv53,pv3307], .c 191, .c 3,
  .c 107, .c 131, .c 3, .c 29, .c 5, .c 3, .c 7, .c 139, .c 3, .c 5, .c 11, .c 3, .c 17, .c 7,
  .c 3, .p pv3 [pv2,pv219091], .c 41, .c 3, .c 13, .c 5, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv5,pv116849], .c 3, .c 5, .p pv7 [pv2,pv3,pv13,pv23,pv977], .c 3, .c 7, .c 71,
  .c 3, .c 61, .c 13, .c 3, .p pv2 [pv2,pv876373], .c 5, .c 3,
]
private theorem h0428c21 : checkBlock 3505243 128 b0428c21 = true := by
  decide +kernel

private def b0428c22 : List Row := [
  .c 23, .p pv2 [pv2,pv3,pv5,pv19,pv41], .c 3, .c 5, .c 67, .c 3, .c 31, .c 11, .c 3,
  .p pv2 [pv2,pv7,pv125197], .c 17, .c 3, .c 7, .c 5, .c 3, .p pv7 [pv2,pv13,pv37,pv911],
  .p pv3 [pv2,pv3,pv5,pv7,pv16693], .c 3, .c 5, .c 7, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv31,pv47,pv401], .c 3, .p pv2 [pv2,pv11,pv79,pv2017], .c 29, .c 3, .c 17,
  .c 5, .c 3, .p pv7 [pv2,pv7,pv35771], .c 227, .c 3, .c 5, .c 13, .c 3,
  .p pv11 [pv2,pv5,pv17,pv1213], .c 31, .c 3, .p pv3 [pv2,pv19,pv23063], .c 7, .c 3,
  .p pv5 [pv2,pv41,pv42751], .c 5, .c 3, .c 47, .c 23, .c 3, .c 5, .p pv2 [pv2,pv3,pv292133],
  .c 3, .c 11, .c 59, .c 3, .c 7, .c 61, .c 3, .p pv2 [pv2,pv11,pv7243], .c 5, .c 3, .c 13, .c 7,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv64919], .c 3, .p pv17 [pv2,pv5,pv350563], .c 19, .c 3, .c 23,
  .c 37, .c 3, .c 353, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv23371], .c 3, .c 5, .c 673, .c 3,
  .c 43, .c 7, .c 3, .c 11, .c 523, .c 3, .p pv3 [pv2,pv17,pv149,pv173], .c 5, .c 3, .c 73,
  .p pv23 [pv2,pv3,pv5,pv541], .c 3, .c 5, .c 1759, .c 3, .c 7, .c 137, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv7,pv27823], .c 3, .c 317, .c 5, .c 3, .c 19, .c 11, .c 3, .c 5, .c 251, .c 3,
  .c 59, .c 13, .c 3, .p pv5 [pv2,pv7,pv250409], .c 23, .c 3, .c 7, .c 5, .c 3, .c 1279, .c 347,
  .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv37,pv379], .p pv5 [pv2,pv3,pv23,pv29,pv73],
]
private theorem h0428c22 : checkBlock 3505499 128 b0428c22 = true := by
  decide +kernel

private def b0428c23 : List Row := [
  .c 3, .c 17, .c 31, .c 3, .p pv2 [pv2,pv13,pv134837], .c 5, .c 3, .c 467,
  .p pv11 [pv2,pv3,pv5,pv38953], .c 3, .c 5, .c 11, .c 3, .c 29, .c 79, .c 3, .c 37, .c 7, .c 3,
  .p pv3 [pv2,pv61,pv449], .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv194767], .c 3,
  .c 101, .p pv5 [pv2,pv3,pv197,pv1483], .c 3, .c 7, .p pv3 [pv2,pv3,pv584303], .c 3, .c 19, .c 5,
  .c 3, .p pv3 [pv2,pv41,pv21377], .c 7, .c 3, .c 5, .c 83, .c 3, .c 829, .c 11, .c 3,
  .p pv5 [pv2,pv1752923], .p pv17 [pv2,pv3,pv146077], .c 3, .c 13, .c 5, .c 3, .c 7, .c 19, .c 3,
  .c 5, .c 23, .c 3, .c 47, .c 7, .c 3, .c 269, .c 13, .c 3, .c 31, .c 5, .c 3,
  .p pv3 [pv2,pv89,pv1231], .c 239, .c 3, .c 5, .c 29, .c 3, .c 7, .c 311, .c 3, .c 397, .c 11,
  .c 3, .c 23, .c 5, .c 3, .c 43, .p pv7 [pv2,pv3,pv5,pv11,pv83], .c 3, .c 5, .c 17, .c 3, .c 11,
  .p pv5 [pv2,pv3,pv97387], .c 3, .c 19, .c 733, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv409,pv2143], .c 41, .c 3, .c 5, .c 7, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv43,pv107,pv127], .c 3, .c 137, .p pv7 [pv2,pv3,pv97,pv251], .c 3,
  .p pv2 [pv2,pv37,pv23689], .c 5, .c 3, .p pv2 [pv2,pv7,pv17,pv14731],
  .p pv7 [pv2,pv3,pv5,pv71,pv823], .c 3, .c 5, .c 857, .c 3, .p pv11 [pv2,pv5,pv229,pv1531],
  .c 1013, .c 3, .c 11, .c 7, .c 3, .c 53, .c 5, .c 3, .c 13,
]
private theorem h0428c23 : checkBlock 3505755 128 b0428c23 = true := by
  decide +kernel

private def b0428c24 : List Row := [
  .c 1609, .c 3, .c 5, .c 103, .c 3, .c 1777, .p pv3 [pv2,pv3,pv13,pv14983], .c 3, .c 7, .c 17,
  .c 3, .c 41, .c 5, .c 3, .p pv11 [pv2,pv31,pv193,pv293], .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv17,pv37,pv929], .c 3, .c 19, .c 263, .c 3, .c 389, .c 47, .c 3, .c 11, .c 5,
  .c 3, .c 7, .c 29, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv13913], .c 3, .c 1447, .c 7, .c 3, .c 13,
  .c 19, .c 3, .c 647, .c 5, .c 3, .c 79, .p pv19 [pv2,pv3,pv5,pv13,pv29,pv31], .c 3, .c 5, .c 11,
  .c 3, .c 7, .c 13, .c 3, .c 73, .c 149, .c 3, .p pv2 [pv2,pv71,pv24691], .c 5, .c 3, .c 11,
  .c 17, .c 3, .c 5, .p pv7 [pv2,pv3,pv139,pv1051], .c 3, .p pv2 [pv2,pv5,pv11,pv15937], .c 23,
  .c 3, .p pv2 [pv2,pv7,pv19,pv269], .p pv2 [pv2,pv3,pv17,pv337], .c 3, .c 7, .c 5, .c 3,
  .p pv13 [pv2,pv29,pv61,pv991], .c 1499, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv350617],
  .c 11, .c 3, .c 43, .p pv2 [pv2,pv3,pv13,pv79,pv569], .c 3, .c 677, .c 5, .c 3, .c 23, .c 13,
  .c 3, .c 5, .c 41, .c 3, .p pv3 [pv2,pv5,pv47,pv373], .c 19, .c 3,
  .p pv5 [pv2,pv11,pv197,pv809], .c 7, .c 3, .p pv2 [pv2,pv23,pv1657], .c 5, .c 3, .c 61, .c 541,
  .c 3, .c 5, .c 1193, .c 3, .c 37, .c 17, .c 3, .c 7, .c 11, .c 3, .c 13, .c 5, .c 3,
  .p pv3 [pv2,pv438281], .c 7, .c 3, .c 5, .c 79, .c 3, .c 11, .c 43, .c 3,
]
private theorem h0428c24 : checkBlock 3506011 128 b0428c24 = true := by
  decide +kernel

private def b0428c25 : List Row := [
  .c 17, .c 13, .c 3, .c 1153, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv31,pv2693], .c 3, .p pv2 [pv2,pv5,pv350629], .c 7, .c 3,
  .p pv3 [pv2,pv438287], .c 463, .c 3, .c 29, .c 5, .c 3, .c 241, .c 59, .c 3, .c 5, .c 19, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv584387], .c 3, .c 11, .p pv17 [pv2,pv3,pv7,pv773], .c 3, .c 89, .c 5,
  .c 3, .p pv2 [pv2,pv11,pv14489], .c 47, .c 3, .c 5, .c 13, .c 3, .p pv7 [pv2,pv5,pv23,pv3049],
  .c 359, .c 3, .c 409, .c 1381, .c 3, .c 7, .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .c 7, .c 3,
  .p pv11 [pv2,pv5,pv199,pv881], .p pv3 [pv2,pv3,pv11,pv5903], .c 3,
  .p pv2 [pv2,pv13,pv17,pv7933], .c 1181, .c 3, .c 11, .c 5, .c 3, .c 13,
  .p pv11 [pv2,pv3,pv5,pv487], .c 3, .c 5, .p pv3 [pv2,pv3,pv71,pv8231], .c 3, .c 617, .c 503,
  .c 3, .c 101, .c 7, .c 3, .p pv5 [pv2,pv89,pv19699], .c 5, .c 3, .c 59, .c 19, .c 3, .c 5,
  .c 11, .c 3, .c 31, .c 41, .c 3, .c 7, .c 997, .c 3, .c 37, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5,
  .c 631, .c 3, .c 17, .c 499, .c 3, .c 13, .p pv3 [pv2,pv3,pv43,pv13591], .c 3,
  .p pv2 [pv2,pv7,pv47,pv73], .c 5, .c 3, .c 7, .c 821, .c 3, .c 5, .c 107, .c 3, .c 83, .c 7,
  .c 3, .c 19, .c 421, .c 3, .c 181, .c 5, .c 3, .p pv7 [pv2,pv101,pv17359], .c 43,
]
private theorem h0428c25 : checkBlock 3506267 128 b0428c25 = true := by
  decide +kernel

private def b0428c26 : List Row := [
  .c 3, .c 5, .c 37, .c 3, .c 7, .c 53, .c 3, .c 173, .c 17, .c 3, .c 277, .c 5, .c 3,
  .p pv2 [pv2,pv71,pv12347], .c 1433, .c 3, .c 5, .c 23, .c 3, .c 457, .c 719, .c 3,
  .p pv5 [pv2,pv7,pv41,pv149], .c 11, .c 3, .c 7, .c 5, .c 3, .c 67, .c 13, .c 3, .c 5, .c 7,
  .c 3, .c 11, .c 29, .c 3, .c 127, .c 281, .c 3, .c 23, .c 5, .c 3, .c 211, .c 419, .c 3, .c 5,
  .c 193, .c 3, .c 19, .c 47, .c 3, .c 31, .c 7, .c 3, .c 13, .c 5, .c 3, .c 53, .c 17, .c 3,
  .c 5, .c 97, .c 3, .c 29, .c 283, .c 3, .c 7, .c 13, .c 3, .p pv5 [pv2,pv1087,pv1613], .c 5,
  .c 3, .p pv2 [pv2,pv11,pv79697], .c 7, .c 3, .c 5, .c 229, .c 3, .c 1307, .c 853, .c 3,
  .p pv5 [pv2,pv1753343], .c 31, .c 3, .c 43, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 61, .c 3,
  .c 13, .c 7, .c 3, .c 47, .p pv3 [pv2,pv3,pv23,pv25411], .c 3, .c 11, .c 5, .c 3, .c 113, .c 79,
  .c 3, .c 5, .c 13, .c 3, .c 7, .c 17, .c 3, .c 569, .c 37, .c 3, .p pv3 [pv2,pv157,pv349], .c 5,
  .c 3, .c 479, .c 71, .c 3, .c 5, .c 11, .c 3, .c 41, .c 19, .c 3, .c 17,
]
private theorem h0428c26 : checkBlock 3506523 128 b0428c26 = true := by
  decide +kernel

private def b0428c27 : List Row := [
  .c 43, .c 3, .c 7, .c 5, .c 3, .c 11, .c 241, .c 3, .c 5, .c 7, .c 3,
  .p pv17 [pv2,pv5,pv11,pv797], .c 823, .c 3, .c 1049, .p pv7 [pv2,pv3,pv146117], .c 3, .c 31,
  .c 5, .c 3, .p pv2 [pv2,pv7,pv107,pv2341], .c 101, .c 3, .c 5, .c 461, .c 3, .c 139, .c 11,
  .c 3, .c 1063, .c 7, .c 3, .c 1439, .c 5, .c 3, .c 19, .c 53, .c 3, .c 5, .c 109, .c 3, .c 307,
  .p pv3 [pv2,pv3,pv17,pv34381], .c 3, .c 7, .p pv13 [pv2,pv3,pv19,pv1709], .c 3,
  .p pv3 [pv2,pv557,pv787], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 19, .c 3,
  .p pv2 [pv2,pv5,pv61,pv5749], .c 13, .c 3, .c 37, .c 11, .c 3, .c 71, .c 5, .c 3, .c 7, .c 641,
  .c 3, .c 5, .c 293, .c 3, .c 11, .c 7, .c 3, .c 563, .p pv7 [pv2,pv3,pv73061], .c 3,
  .p pv3 [pv2,pv11,pv13,pv6131], .c 5, .c 3, .p pv2 [pv2,pv97,pv18077], .c 29, .c 3, .c 5, .c 17,
  .c 3, .c 7, .c 269, .c 3, .c 53, .c 1579, .c 3, .c 19, .c 5, .c 3, .p pv3 [pv2,pv31,pv79,pv179],
  .c 13, .c 3, .c 5, .c 199, .c 3, .c 17, .p pv3 [pv2,pv3,pv19,pv30763], .c 3, .c 11,
  .p pv2 [pv2,pv3,pv292249], .c 3, .c 7, .c 5, .c 3, .c 29, .c 19, .c 3, .c 5, .c 7, .c 3, .c 271,
  .c 149, .c 3, .c 23, .c 59, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv7,pv29,pv617], .c 11, .c 3,
]
private theorem h0428c27 : checkBlock 3506779 128 b0428c27 = true := by
  decide +kernel

private def b0428c28 : List Row := [
  .c 5, .c 43, .c 3, .p pv3 [pv2,pv5,pv23,pv953], .p pv2 [pv2,pv3,pv7,pv11,pv7591], .c 3, .c 79,
  .c 7, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv19,pv41,pv2251], .c 31, .c 3, .c 5, .c 1451, .c 3,
  .c 359, .c 61, .c 3, .c 7, .p pv3 [pv2,pv3,pv59,pv9907], .c 3, .c 17, .c 5, .c 3,
  .p pv3 [pv2,pv13,pv1297], .c 7, .c 3, .c 5, .c 11, .c 3, .c 13, .c 701, .c 3, .c 941, .c 23,
  .c 3, .p pv3 [pv2,pv7,pv62627], .c 5, .c 3, .c 7, .c 223, .c 3, .c 5, .c 13, .c 3, .c 383, .c 7,
  .c 3, .c 59, .c 73, .c 3, .p pv5 [pv2,pv191,pv9181], .c 5, .c 3, .c 991, .c 17, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv37,pv2633], .c 3, .c 7, .c 11, .c 3, .c 167, .c 53, .c 3, .c 29, .c 5, .c 3,
  .c 13, .c 41, .c 3, .c 5, .c 47, .c 3, .c 19, .c 37, .c 3, .p pv2 [pv2,pv7,pv11,pv59,pv193],
  .p pv11 [pv2,pv3,pv659,pv887], .c 3, .c 7, .c 5, .c 3, .c 43,
  .p pv2 [pv2,pv3,pv5,pv7,pv19,pv293], .c 3, .c 5, .c 7, .c 3, .c 1319, .c 89, .c 3,
  .p pv2 [pv2,pv1753613], .c 11, .c 3, .p pv3 [pv2,pv127,pv863], .c 5, .c 3, .c 1543,
  .p pv7 [pv2,pv3,pv5,pv11,pv2657], .c 3, .c 5, .c 23, .c 3, .c 11, .c 17, .c 3, .c 13, .c 7,
  .c 3, .c 41, .c 5, .c 3, .p pv2 [pv2,pv876817], .c 163, .c 3, .c 5, .c 151, .c 3, .c 47, .c 13,
  .c 3, .c 7, .c 29,
]
private theorem h0428c28 : checkBlock 3507035 128 b0428c28 = true := by
  decide +kernel

private def b0428c29 : List Row := [
  .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv1753649], .c 7, .c 3, .c 5, .c 827, .c 3, .c 149,
  .p pv7 [pv2,pv3,pv89,pv821], .c 3, .c 11, .c 373, .c 3, .p pv2 [pv2,pv7,pv13,pv2753], .c 5,
  .c 3, .c 7, .c 83, .c 3, .c 5, .c 137, .c 3, .c 37, .c 7, .c 3, .c 29, .c 233, .c 3, .c 107,
  .c 5, .c 3, .c 127, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv584561], .c 3, .c 7, .c 59, .c 3,
  .c 227, .p pv2 [pv2,pv3,pv7,pv37,pv61], .c 3, .c 11, .c 5, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv5,pv38971], .c 3, .c 5, .p pv2 [pv2,pv3,pv292283], .c 3, .c 89,
  .p pv2 [pv2,pv3,pv31,pv109,pv173], .c 3, .c 113, .c 769, .c 3, .c 7, .c 5, .c 3, .c 19,
  .p pv37 [pv2,pv3,pv5,pv7,pv1193], .c 3, .c 5, .c 7, .c 3, .c 23, .c 31, .c 3, .c 1093, .c 13,
  .c 3, .p pv2 [pv2,pv79,pv281], .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv67,pv349], .c 3, .c 5,
  .c 17, .c 3, .p pv2 [pv2,pv5,pv11,pv107,pv149], .c 29, .c 3, .c 43, .c 7, .c 3,
  .p pv3 [pv2,pv219217], .c 5, .c 3, .p pv17 [pv2,pv13,pv313,pv431], .p pv17 [pv2,pv3,pv5,pv9743],
  .c 3, .c 5, .c 53, .c 3, .c 13, .c 11, .c 3, .c 7, .c 829, .c 3, .c 293, .c 5, .c 3, .c 41,
  .c 7, .c 3, .c 5, .c 13, .c 3, .c 29, .c 23, .c 3, .p pv7 [pv2,pv11,pv31,pv37,pv139],
  .p pv19 [pv2,pv3,pv101,pv1447], .c 3, .c 19, .c 5, .c 3, .c 7,
  .p pv19 [pv2,pv3,pv5,pv53,pv1103], .c 3, .c 5,
]
private theorem h0428c29 : checkBlock 3507291 128 b0428c29 = true := by
  decide +kernel

private def b0428c30 : List Row := [
  .c 401, .c 3, .p pv11 [pv2,pv5,pv29,pv41,pv59], .c 7, .c 3, .c 31, .c 11, .c 3, .c 37, .c 5,
  .c 3, .c 13, .c 19, .c 3, .c 5, .c 73, .c 3, .c 7, .c 577, .c 3, .p pv2 [pv2,pv613,pv2861],
  .p pv2 [pv2,pv3,pv7,pv31,pv449], .c 3, .c 17, .c 5, .c 3, .c 181,
  .p pv13 [pv2,pv3,pv5,pv37,pv79], .c 3, .c 5, .c 331, .c 3, .c 137, .c 71, .c 3, .c 97, .c 31,
  .c 3, .c 7, .c 5, .c 3, .c 101, .c 263, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv87691],
  .p pv2 [pv2,pv3,pv194869], .c 3, .c 11, .p pv11 [pv2,pv3,pv18269], .c 3, .c 571, .c 5, .c 3,
  .c 787, .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv19,pv29,pv1061], .c 3, .p pv13 [pv2,pv5,pv350767],
  .c 13, .c 3, .p pv2 [pv2,pv673,pv1303], .c 7, .c 3, .c 61, .c 5, .c 3, .p pv3 [pv2,pv463,pv947],
  .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv24359], .c 3, .c 857, .c 743, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv292309], .c 3, .c 11, .c 5, .c 3, .p pv13 [pv2,pv67,pv26177], .c 7, .c 3,
  .c 5, .c 59, .c 3, .p pv2 [pv2,pv5,pv23,pv101,pv151], .c 433, .c 3, .p pv3 [pv2,pv438467],
  .p pv7 [pv2,pv3,pv13,pv44971], .c 3, .c 31, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 11, .c 3,
  .c 19, .c 7, .c 3, .c 1109, .c 311, .c 3, .c 199, .c 5, .c 3, .c 11, .c 107, .c 3, .c 5, .c 131,
  .c 3, .c 7, .c 257, .c 3, .c 17, .c 19, .c 3,
]
private theorem h0428c30 : checkBlock 3507547 128 b0428c30 = true := by
  decide +kernel

private def b0428c31 : List Row := [
  .c 13, .c 5, .c 3, .p pv3 [pv2,pv109619], .c 29, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv11243],
  .c 3, .p pv2 [pv2,pv5,pv175391], .c 11, .c 3, .p pv2 [pv2,pv7,pv71,pv3529], .c 13, .c 3, .c 7,
  .c 5, .c 3, .p pv11 [pv2,pv109,pv16091], .p pv11 [pv2,pv3,pv5,pv7,pv29], .c 3, .c 5, .c 7, .c 3,
  .c 157, .c 607, .c 3, .c 659, .c 37, .c 3, .c 179, .c 5, .c 3, .c 29, .c 103, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv97441], .c 3, .c 13, .p pv2 [pv2,pv3,pv7,pv17], .c 3, .p pv5 [pv2,pv1753943],
  .c 7, .c 3, .c 521, .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv11,pv1063], .c 3, .c 5, .c 13,
  .c 3, .c 11, .c 19, .c 3, .c 7, .c 41, .c 3, .c 163, .c 5, .c 3, .c 31, .c 7, .c 3, .c 5, .c 23,
  .c 3, .p pv3 [pv2,pv5,pv43,pv4079], .c 139, .c 3, .c 109, .p pv2 [pv2,pv3,pv401], .c 3,
  .p pv3 [pv2,pv7,pv31321], .c 5, .c 3, .c 7, .c 181, .c 3, .c 5, .c 17, .c 3,
  .p pv2 [pv2,pv5,pv19,pv37,pv499], .c 7, .c 3, .c 11, .c 197, .c 3, .c 23, .c 5, .c 3, .c 19,
  .c 31, .c 3, .c 5, .p pv2 [pv2,pv3,pv241,pv1213], .c 3, .c 7, .p pv3 [pv2,pv3,pv167,pv389],
  .c 3, .c 37, .p pv11 [pv2,pv3,pv7,pv19,pv157], .c 3, .c 223, .c 5, .c 3, .c 1013, .c 11, .c 3,
  .c 5, .c 19, .c 3, .p pv7 [pv2,pv5,pv350803], .c 47, .c 3, .c 13, .c 71, .c 3, .c 7, .c 5, .c 3,
  .c 61, .c 229, .c 3, .c 5, .c 7,
]
private theorem h0428c31 : checkBlock 3507803 128 b0428c31 = true := by
  decide +kernel

def rows0428 : List Row :=
  b0428c00 ++ b0428c01 ++ b0428c02 ++ b0428c03 ++ b0428c04 ++ b0428c05 ++ b0428c06 ++ b0428c07 ++
  b0428c08 ++ b0428c09 ++ b0428c10 ++ b0428c11 ++ b0428c12 ++ b0428c13 ++ b0428c14 ++ b0428c15 ++
  b0428c16 ++ b0428c17 ++ b0428c18 ++ b0428c19 ++ b0428c20 ++ b0428c21 ++ b0428c22 ++ b0428c23 ++
  b0428c24 ++ b0428c25 ++ b0428c26 ++ b0428c27 ++ b0428c28 ++ b0428c29 ++ b0428c30 ++ b0428c31

theorem checked0428 : checkBlock 3499867 4096 rows0428 = true :=
  checkBlock_append h0428c00 (
    checkBlock_append h0428c01 (
    checkBlock_append h0428c02 (
    checkBlock_append h0428c03 (
    checkBlock_append h0428c04 (
    checkBlock_append h0428c05 (
    checkBlock_append h0428c06 (
    checkBlock_append h0428c07 (
    checkBlock_append h0428c08 (
    checkBlock_append h0428c09 (
    checkBlock_append h0428c10 (
    checkBlock_append h0428c11 (
    checkBlock_append h0428c12 (
    checkBlock_append h0428c13 (
    checkBlock_append h0428c14 (
    checkBlock_append h0428c15 (
    checkBlock_append h0428c16 (
    checkBlock_append h0428c17 (
    checkBlock_append h0428c18 (
    checkBlock_append h0428c19 (
    checkBlock_append h0428c20 (
    checkBlock_append h0428c21 (
    checkBlock_append h0428c22 (
    checkBlock_append h0428c23 (
    checkBlock_append h0428c24 (
    checkBlock_append h0428c25 (
    checkBlock_append h0428c26 (
    checkBlock_append h0428c27 (
    checkBlock_append h0428c28 (
    checkBlock_append h0428c29 (
    checkBlock_append h0428c30 (
    h0428c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
