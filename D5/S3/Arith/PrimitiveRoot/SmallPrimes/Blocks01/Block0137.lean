/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0137
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0137.checked0137
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table020
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table021
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table025
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table031
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table041
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table042
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table062
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table063
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table116
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table117

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0137c00 : List Row := [
  .c 821, .c 3, .c 19, .c 47, .c 3, .c 7, .c 11, .c 3, .c 17, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .c 241, .c 3, .c 11, .c 43, .c 3, .c 709, .c 19, .c 3, .c 79, .c 5, .c 3, .c 7, .c 233, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv7,pv26723], .c 3, .p pv2 [pv2,pv5,pv112237], .c 7, .c 3, .c 23, .c 89,
  .c 3, .c 151, .c 5, .c 3, .p pv2 [pv2,pv280597], .c 17, .c 3, .c 5, .p pv7 [pv2,pv3,pv11,pv773],
  .c 3, .c 7, .c 613, .c 3, .c 11, .c 83, .c 3, .c 101, .c 5, .c 3, .p pv7 [pv2,pv11,pv163,pv313],
  .c 331, .c 3, .c 5, .p pv2 [pv2,pv3,pv127,pv491], .c 3, .p pv7 [pv2,pv5,pv107,pv1049], .c 13,
  .c 3, .p pv2 [pv2,pv7,pv40087], .c 71, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv31,pv73], .c 11,
  .c 3, .c 5, .c 7, .c 3, .c 61, .c 19, .c 3, .p pv2 [pv2,pv677,pv829], .c 23, .c 3, .c 11, .c 5,
  .c 3, .c 31, .p pv7 [pv2,pv3,pv5,pv1559], .c 3, .c 5, .c 53, .c 3, .p pv2 [pv2,pv5,pv112249],
  .c 17, .c 3, .c 317, .c 7, .c 3, .c 29, .c 5, .c 3, .c 179, .c 13, .c 3, .c 5, .c 11, .c 3,
  .c 73, .c 439, .c 3, .c 7, .p pv29 [pv2,pv3,pv11,pv1063], .c 3, .p pv2 [pv2,pv29,pv9677], .c 5,
  .c 3, .c 11, .c 7, .c 3, .c 5, .c 337, .c 3, .p pv17 [pv2,pv5,pv11,pv13,pv157], .c 127, .c 3,
  .c 89, .c 199, .c 3,
]
private theorem h0137c00 : checkBlock 1122307 128 b0137c00 = true := by
  decide +kernel

private def b0137c01 : List Row := [
  .c 13, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv12473], .c 3, .c 5, .c 19, .c 3, .c 71, .c 7,
  .c 3, .p pv2 [pv2,pv571,pv983], .c 13, .c 3, .c 53, .c 5, .c 3, .p pv7 [pv2,pv379,pv1481],
  .c 43, .c 3, .c 5, .c 23, .c 3, .c 7, .c 941, .c 3, .c 37, .c 29, .c 3,
  .p pv5 [pv2,pv563,pv997], .c 5, .c 3, .c 17, .c 757, .c 3, .c 5, .c 569, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv47,pv1327], .c 3, .p pv5 [pv2,pv7,pv17,pv53,pv89], .c 11, .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv83,pv6763], .c 283, .c 3, .c 5, .c 7, .c 3, .c 11, .c 743, .c 3, .c 29,
  .p pv3 [pv2,pv3,pv97,pv643], .c 3, .p pv2 [pv2,pv11,pv51031], .c 5, .c 3, .c 47, .c 19, .c 3,
  .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv103,pv109], .c 41, .c 3, .c 157, .c 7, .c 3, .c 859, .c 5,
  .c 3, .c 13, .p pv7 [pv2,pv3,pv5,pv2339], .c 3, .c 5, .c 31, .c 3, .c 17, .c 349, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv187123], .c 3, .c 181, .c 5, .c 3, .p pv2 [pv2,pv11,pv17,pv19,pv79], .c 7,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv93563], .c 3, .p pv3 [pv2,pv5,pv28069], .c 863, .c 3, .c 19,
  .c 433, .c 3, .c 43, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 229, .c 3, .c 23, .c 7, .c 3,
  .c 13, .c 17, .c 3, .c 11, .c 5, .c 3, .c 109, .p pv3 [pv2,pv3,pv5,pv13,pv2879], .c 3, .c 5,
  .c 101,
]
private theorem h0137c01 : checkBlock 1122563 128 b0137c01 = true := by
  decide +kernel

private def b0137c02 : List Row := [
  .c 3, .c 7, .c 13, .c 3, .c 61, .c 59, .c 3, .c 17, .c 5, .c 3, .c 37,
  .p pv29 [pv2,pv3,pv5,pv3119], .c 3, .c 5, .c 11, .c 3, .c 29, .c 67, .c 3,
  .p pv3 [pv2,pv7,pv20051], .c 43, .c 3, .c 7, .c 5, .c 3, .c 11, .c 1033, .c 3, .c 5, .c 7, .c 3,
  .c 19, .c 23, .c 3, .p pv5 [pv2,pv73,pv7691], .c 191, .c 3, .c 353, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv80207], .c 13, .c 3, .c 5, .c 83, .c 3, .c 53, .c 11, .c 3, .c 491, .c 7,
  .c 3, .p pv2 [pv2,pv561461], .c 5, .c 3, .c 23, .c 587, .c 3, .c 5,
  .p pv19 [pv2,pv3,pv71,pv659], .c 3, .p pv3 [pv2,pv5,pv7,pv13,pv617], .c 173, .c 3, .c 7, .c 41,
  .c 3, .c 13, .c 5, .c 3, .c 73, .c 7, .c 3, .c 5, .c 29, .c 3, .c 47, .c 797, .c 3, .c 379,
  .c 11, .c 3, .p pv5 [pv2,pv7,pv1637], .c 5, .c 3, .c 7, .c 547, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv29,pv461], .c 3, .c 11, .c 7, .c 3, .c 71, .c 103, .c 3, .c 149, .c 5,
  .c 3, .c 101, .c 23, .c 3, .c 5, .c 109, .c 3, .c 7, .c 19, .c 3, .c 17, .c 661, .c 3, .c 389,
  .c 5, .c 3, .c 787, .p pv3 [pv2,pv3,pv5,pv7487], .c 3, .c 5, .c 13, .c 3, .c 37, .c 131, .c 3,
  .c 11, .c 293, .c 3, .c 7,
]
private theorem h0137c02 : checkBlock 1122819 128 b0137c02 = true := by
  decide +kernel

private def b0137c03 : List Row := [
  .c 5, .c 3, .p pv11 [pv2,pv11,pv71,pv719], .p pv19 [pv2,pv3,pv5,pv7,pv191], .c 3, .c 5, .c 7,
  .c 3, .c 89, .p pv2 [pv2,pv3,pv10399], .c 3, .c 197, .c 31, .c 3, .c 373, .c 5, .c 3, .c 13,
  .c 11, .c 3, .c 5, .c 43, .c 3, .c 67, .c 53, .c 3, .p pv5 [pv2,pv137,pv4099], .c 7, .c 3,
  .c 11, .c 5, .c 3, .c 17, .c 29, .c 3, .c 5, .c 19, .c 3, .p pv17 [pv2,pv5,pv7,pv3209], .c 211,
  .c 3, .c 7, .c 23, .c 3, .c 97, .c 5, .c 3, .c 773, .c 7, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv89,pv631], .c 59, .c 3, .c 13, .p pv2 [pv2,pv3,pv11,pv67,pv127], .c 3, .c 61,
  .c 5, .c 3, .c 7, .c 401, .c 3, .c 5, .c 17, .c 3, .p pv11 [pv2,pv5,pv11,pv10211], .c 7, .c 3,
  .p pv3 [pv2,pv70201], .p pv3 [pv2,pv3,pv62401], .c 3, .c 19, .c 5, .c 3, .c 53,
  .p pv29 [pv2,pv3,pv5,pv37441], .c 3, .c 5, .c 673, .c 3, .c 7, .c 11, .c 3,
  .p pv5 [pv2,pv37,pv43,pv353], .c 499, .c 3, .c 47, .c 5, .c 3, .c 139, .c 19, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv187211], .c 3, .c 191, .c 263, .c 3, .c 41, .p pv3 [pv2,pv3,pv13,pv14401],
  .c 3, .c 7, .c 5, .c 3, .c 43, .c 13, .c 3, .c 5, .c 7, .c 3, .c 59, .p pv3 [pv2,pv3,pv187217],
  .c 3, .p pv2 [pv2,pv457,pv1229], .c 11, .c 3, .c 307, .c 5, .c 3,
  .p pv13 [pv2,pv7,pv19,pv41,pv103], .c 643, .c 3, .c 5, .p pv3 [pv2,pv3,pv17,pv3671], .c 3,
]
private theorem h0137c03 : checkBlock 1123075 128 b0137c03 = true := by
  decide +kernel

private def b0137c04 : List Row := [
  .c 11, .c 113, .c 3, .c 19, .c 7, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv280837],
  .p pv11 [pv2,pv3,pv5,pv7489], .c 3, .c 5, .c 37, .c 3, .p pv29 [pv2,pv5,pv7,pv17,pv59], .c 509,
  .c 3, .c 7, .c 13, .c 3, .c 29, .c 5, .c 3, .p pv2 [pv2,pv31,pv18119], .c 7, .c 3, .c 5, .c 367,
  .c 3, .p pv11 [pv2,pv5,pv112339], .c 107, .c 3, .c 11, .p pv17 [pv2,pv3,pv139,pv449], .c 3,
  .p pv2 [pv2,pv7,pv29,pv2767], .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 1013, .c 3, .c 13, .c 7,
  .c 3, .p pv2 [pv2,pv561713], .p pv2 [pv2,pv3,pv17,pv5507], .c 3, .c 71, .c 5, .c 3,
  .p pv7 [pv2,pv281,pv1999], .c 11, .c 3, .c 5, .c 13, .c 3, .c 7, .c 193, .c 3, .c 461, .c 79,
  .c 3, .c 11, .c 5, .c 3, .c 557, .c 31, .c 3, .c 5, .p pv2 [pv2,pv3,pv251,pv373], .c 3, .c 23,
  .p pv5 [pv2,pv3,pv41,pv4567], .c 3, .p pv5 [pv2,pv7,pv13,pv6173], .c 19, .c 3, .c 7, .c 5, .c 3,
  .c 13, .p pv2 [pv2,pv3,pv5,pv7,pv107], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv283,pv397],
  .c 17, .c 3, .p pv2 [pv2,pv280879], .c 1051, .c 3, .c 41, .c 5, .c 3, .c 11,
  .p pv13 [pv2,pv3,pv5,pv17,pv2203], .c 3, .c 5, .c 59, .c 3, .p pv3 [pv2,pv5,pv11,pv5107], .c 73,
  .c 3, .c 17, .c 7, .c 3, .p pv3 [pv2,pv35111], .c 5, .c 3, .c 61, .p pv7 [pv2,pv3,pv5,pv3121],
  .c 3, .c 5, .p pv3 [pv2,pv3,pv271,pv691], .c 3, .c 83, .c 11, .c 3, .c 7, .c 37, .c 3, .c 179,
  .c 5,
]
private theorem h0137c04 : checkBlock 1123331 128 b0137c04 = true := by
  decide +kernel

private def b0137c05 : List Row := [
  .c 3, .p pv2 [pv2,pv280897], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv23,pv59], .c 3,
  .p pv3 [pv2,pv5,pv53], .c 13, .c 3, .c 107, .c 149, .c 3, .c 269, .c 5, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv5,pv61,pv307], .c 3, .c 5, .c 103, .c 3, .p pv11 [pv2,pv5,pv112363], .c 7,
  .c 3, .p pv2 [pv2,pv280909], .c 11, .c 3, .c 311, .c 5, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv5,pv11,pv227], .c 3, .c 5, .c 31, .c 3, .c 7, .c 29, .c 3,
  .p pv2 [pv2,pv17,pv33049], .p pv2 [pv2,pv3,pv7,pv13], .c 3, .c 641, .c 5, .c 3, .c 19, .c 13,
  .c 3, .c 5, .c 41, .c 3, .p pv2 [pv2,pv5,pv37,pv3037], .p pv2 [pv2,pv3,pv29,pv3229], .c 3,
  .c 223, .p pv2 [pv2,pv3,pv19,pv9857], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv280927], .c 23,
  .c 3, .c 5, .c 7, .c 3, .c 29, .c 47, .c 3, .c 11, .p pv11 [pv2,pv3,pv41,pv571], .c 3, .c 13,
  .c 5, .c 3, .p pv2 [pv2,pv7,pv11,pv7297], .p pv2 [pv2,pv3,pv5,pv2081], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv13,pv14407], .c 3, .c 17, .c 199, .c 3, .c 23, .c 7, .c 3, .c 457, .c 5, .c 3,
  .c 41, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv1951], .c 3, .c 31, .c 241, .c 3, .c 7, .c 277,
  .c 3, .c 11, .c 5, .c 3, .c 263, .c 7, .c 3, .c 5, .p pv11 [pv2,pv3,pv157,pv1193], .c 3, .c 13,
  .c 653, .c 3, .c 47, .c 17, .c 3, .c 127, .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 11, .c 3,
  .p pv3 [pv2,pv5,pv439],
]
private theorem h0137c05 : checkBlock 1123587 128 b0137c05 = true := by
  decide +kernel

private def b0137c06 : List Row := [
  .c 7, .c 3, .c 449, .c 23, .c 3, .c 17, .c 5, .c 3, .c 11, .c 257, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv29,pv2153], .c 3, .c 7, .p pv5 [pv2,pv3,pv23,pv509], .c 3, .c 227,
  .p pv3 [pv2,pv3,pv7,pv26759], .c 3, .p pv2 [pv2,pv269,pv2089], .c 5, .c 3, .c 13, .c 43, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv46829], .c 3, .p pv2 [pv2,pv5,pv11239], .c 11, .c 3, .c 19,
  .p pv7 [pv2,pv3,pv73,pv1283], .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv23,pv53,pv461], .c 17,
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv71,pv1583], .c 41, .c 3, .c 919, .c 97, .c 3,
  .p pv5 [pv2,pv727,pv773], .c 5, .c 3, .c 37, .p pv11 [pv2,pv3,pv5,pv59,pv127], .c 3, .c 5,
  .c 1019, .c 3, .p pv3 [pv2,pv5,pv28099], .c 157, .c 3, .c 13, .c 7, .c 3,
  .p pv5 [pv2,pv17,pv16529], .c 5, .c 3, .p pv2 [pv2,pv251,pv2239], .c 73, .c 3, .c 5, .c 23,
  .c 3, .c 11, .c 13, .c 3, .c 7, .p pv3 [pv2,pv3,pv31,pv6043], .c 3, .c 401, .c 5, .c 3, .c 59,
  .c 7, .c 3, .c 5, .c 239, .c 3, .c 19, .c 17, .c 3, .p pv2 [pv2,pv557,pv1009], .c 31, .c 3,
  .c 23, .c 5, .c 3, .c 7, .p pv31 [pv2,pv3,pv5,pv17,pv19,pv29], .c 3, .c 5, .c 61, .c 3,
  .p pv2 [pv2,pv5,pv22481], .c 7, .c 3, .c 11, .c 19, .c 3, .c 43, .c 5, .c 3, .c 29, .c 13, .c 3,
  .c 5, .c 53, .c 3, .c 7, .p pv2 [pv2,pv3,pv197,pv317], .c 3, .p pv5 [pv2,pv562043], .c 947,
  .c 3, .c 139, .c 5, .c 3,
]
private theorem h0137c06 : checkBlock 1123843 128 b0137c06 = true := by
  decide +kernel

private def b0137c07 : List Row := [
  .c 47, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv43,pv4357], .c 3, .c 131,
  .p pv17 [pv2,pv3,pv11,pv2129], .c 3, .c 109, .p pv3 [pv2,pv3,pv257], .c 3, .c 7, .c 5, .c 3,
  .c 349, .p pv2 [pv2,pv3,pv5,pv7,pv53,pv101], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv56207],
  .c 71, .c 3, .p pv2 [pv2,pv47,pv11959], .c 13, .c 3, .c 31, .c 5, .c 3, .c 17, .c 229, .c 3,
  .c 5, .c 11, .c 3, .c 23, .c 19, .c 3, .c 419, .c 7, .c 3, .c 53, .c 5, .c 3, .c 11, .c 181,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv93683], .c 3, .c 13, .p pv2 [pv2,pv3,pv187367], .c 3, .c 7,
  .p pv13 [pv2,pv3,pv37,pv211], .c 3, .c 479, .c 5, .c 3, .p pv2 [pv2,pv683,pv823], .c 7, .c 3,
  .c 5, .c 13, .c 3, .c 101, .c 11, .c 3, .c 113, .p pv3 [pv2,pv3,pv187373], .c 3, .c 29, .c 5,
  .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv1499], .c 3, .c 5, .c 691, .c 3, .c 17, .c 7, .c 3,
  .p pv5 [pv2,pv11,pv13,pv3931], .p pv7 [pv2,pv3,pv19,pv4931], .c 3, .c 73, .c 5, .c 3, .c 13,
  .c 281, .c 3, .c 5, .c 19, .c 3, .c 7, .p pv2 [pv2,pv3,pv13,pv7207], .c 3,
  .p pv3 [pv2,pv313,pv449], .c 11, .c 3, .p pv5 [pv2,pv41,pv13711], .c 5, .c 3, .c 23, .c 563,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv31231], .c 3, .c 11, .c 599, .c 3, .c 67, .c 17, .c 3, .c 7, .c 5,
  .c 3, .c 31, .c 409, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv113,pv199],
  .p pv5 [pv2,pv3,pv61],
]
private theorem h0137c07 : checkBlock 1124099 128 b0137c07 = true := by
  decide +kernel

private def b0137c08 : List Row := [
  .c 3, .c 13, .c 29, .c 3, .c 17, .c 5, .c 3, .p pv23 [pv2,pv7,pv10039], .c 139, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv4259], .c 3, .c 47, .c 13, .c 3, .c 11, .c 7, .c 3, .c 37, .c 5, .c 3,
  .c 317, .c 19, .c 3, .c 5, .c 43, .c 3, .c 167, .c 61, .c 3, .c 7, .c 73, .c 3,
  .p pv5 [pv2,pv13,pv59,pv733], .c 5, .c 3, .p pv2 [pv2,pv47,pv5981], .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv93703], .c 3, .p pv3 [pv2,pv5,pv28111], .p pv2 [pv2,pv3,pv11,pv631], .c 3,
  .c 23, .p pv11 [pv2,pv3,pv13,pv17,pv53], .c 3, .c 11, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5,
  .c 37, .c 3, .c 601, .c 7, .c 3, .c 19, .c 431, .c 3, .c 487, .c 5, .c 3, .c 863, .c 421, .c 3,
  .c 5, .c 11, .c 3, .c 7, .c 149, .c 3, .c 41, .p pv17 [pv2,pv3,pv7,pv11,pv1217], .c 3, .c 13,
  .c 5, .c 3, .c 11, .c 97, .c 3, .c 5, .c 977, .c 3, .p pv7 [pv2,pv5,pv11,pv10223], .c 17, .c 3,
  .c 163, .c 13, .c 3, .c 7, .c 5, .c 3, .c 199, .p pv7 [pv2,pv3,pv5,pv7,pv17], .c 3, .c 5, .c 7,
  .c 3, .p pv3 [pv2,pv5,pv14057], .c 11, .c 3, .c 17, .c 47, .c 3, .c 577, .c 5, .c 3, .c 43,
  .p pv2 [pv2,pv3,pv5,pv18743], .c 3, .c 5, .c 31, .c 3, .c 13, .p pv5 [pv2,pv3,pv7,pv3347], .c 3,
  .p pv2 [pv2,pv11,pv61,pv419], .c 7, .c 3, .p pv2 [pv2,pv562301], .c 5, .c 3, .c 313,
]
private theorem h0137c08 : checkBlock 1124355 128 b0137c08 = true := by
  decide +kernel

private def b0137c09 : List Row := [
  .c 193, .c 3, .c 5, .c 13, .c 3, .c 967, .c 787, .c 3, .c 7, .c 11, .c 3, .c 137, .c 5, .c 3,
  .p pv23 [pv2,pv73,pv7703], .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv187441], .c 3, .c 11,
  .p pv2 [pv2,pv3,pv17,pv37,pv149], .c 3, .c 61, .p pv7 [pv2,pv3,pv59,pv353], .c 3, .c 47, .c 5,
  .c 3, .c 7, .c 41, .c 3, .c 5, .c 23, .c 3, .p pv3 [pv2,pv5,pv31,pv907], .c 7, .c 3,
  .p pv5 [pv2,pv17,pv19,pv1741], .c 37, .c 3, .c 89, .c 5, .c 3, .p pv2 [pv2,pv562349], .c 397,
  .c 3, .c 5, .c 29, .c 3, .c 7, .c 53, .c 3, .c 11, .p pv41 [pv2,pv3,pv7,pv61,pv439], .c 3,
  .c 23, .c 5, .c 3, .c 67, .c 251, .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv56237], .c 19,
  .c 3, .c 13, .p pv2 [pv2,pv3,pv157,pv199], .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv739,pv761],
  .c 11, .c 3, .c 5, .c 7, .c 3, .c 17, .c 13, .c 3, .c 443, .c 61, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv17,pv139], .c 617, .c 3, .c 5, .p pv2 [pv2,pv3,pv67,pv1399], .c 3, .c 149,
  .p pv2 [pv2,pv3,pv7,pv79,pv113], .c 3, .p pv5 [pv2,pv562403], .c 7, .c 3,
  .p pv2 [pv2,pv13,pv97,pv223], .c 5, .c 3, .c 19, .c 1031, .c 3, .c 5, .c 11, .c 3,
  .p pv7 [pv2,pv5,pv7,pv16069], .p pv5 [pv2,pv3,pv11717], .c 3, .c 7, .c 17, .c 3, .c 281, .c 5,
  .c 3, .c 11, .c 7, .c 3, .c 5, .c 19, .c 3, .c 23, .c 67, .c 3,
]
private theorem h0137c09 : checkBlock 1124611 128 b0137c09 = true := by
  decide +kernel

private def b0137c10 : List Row := [
  .p pv5 [pv2,pv31,pv18143], .p pv13 [pv2,pv3,pv93739], .c 3, .c 17, .c 5, .c 3, .c 7, .c 29,
  .c 3, .c 5, .c 311, .c 3, .c 107, .c 7, .c 3, .c 31, .c 83, .c 3, .c 13, .c 5, .c 3, .c 97,
  .c 37, .c 3, .c 5, .c 41, .c 3, .c 7, .c 43, .c 3, .c 139, .c 13, .c 3, .c 19, .c 5, .c 3,
  .c 29, .c 17, .c 3, .c 5, .c 199, .c 3, .p pv7 [pv2,pv5,pv149,pv151], .c 23, .c 3,
  .p pv2 [pv2,pv7,pv40177], .c 11, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv13,pv29,pv373], .c 19,
  .c 3, .c 5, .c 7, .c 3, .c 11, .p pv3 [pv2,pv3,pv83,pv251], .c 3, .p pv2 [pv2,pv562493], .c 109,
  .c 3, .p pv3 [pv2,pv11,pv17,pv47], .c 5, .c 3, .c 23, .p pv7 [pv2,pv3,pv5], .c 3, .c 5, .c 13,
  .c 3, .c 353, .p pv2 [pv2,pv3,pv7,pv59,pv227], .c 3, .p pv3 [pv2,pv140627], .c 7, .c 3, .c 61,
  .c 5, .c 3, .p pv3 [pv2,pv19,pv113,pv131], .c 53, .c 3, .c 5, .c 881, .c 3, .c 823, .c 17, .c 3,
  .c 7, .c 89, .c 3, .p pv2 [pv2,pv31,pv43,pv211], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 197,
  .c 3, .c 59, .c 631, .c 3, .c 17, .c 167, .c 3, .c 31, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .p pv17 [pv2,pv3,pv7,pv37,pv181], .c 3, .c 151, .c 7, .c 3, .c 853, .p pv2 [pv2,pv3,pv31253],
  .c 3, .c 11, .c 5, .c 3, .c 653, .p pv11 [pv2,pv3,pv5,pv293],
]
private theorem h0137c10 : checkBlock 1124867 128 b0137c10 = true := by
  decide +kernel

private def b0137c11 : List Row := [
  .c 3, .c 5, .p pv3 [pv2,pv3,pv62507], .c 3, .c 7, .c 37, .c 3, .c 13,
  .p pv11 [pv2,pv3,pv7,pv43,pv89], .c 3, .p pv5 [pv2,pv19,pv29,pv1021], .c 5, .c 3, .c 73,
  .p pv17 [pv2,pv3,pv5,pv13,pv577], .c 3, .c 5, .c 11, .c 3, .c 19, .c 13, .c 3,
  .p pv17 [pv2,pv7,pv80369], .p pv7 [pv2,pv3,pv11,pv2131], .c 3, .c 7, .c 5, .c 3, .c 11, .c 43,
  .c 3, .c 5, .c 7, .c 3, .c 877, .p pv5 [pv2,pv3,pv173,pv271], .c 3, .c 79, .c 19, .c 3,
  .p pv2 [pv2,pv13,pv3329], .c 5, .c 3, .p pv3 [pv2,pv7,pv71,pv283], .c 503, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv3907], .c 3, .p pv2 [pv2,pv5,pv127,pv443], .c 11, .c 3, .c 47, .c 7, .c 3,
  .c 251, .c 5, .c 3, .c 227, .c 13, .c 3, .c 5, .c 17, .c 3, .c 379, .p pv2 [pv2,pv3,pv23,pv151],
  .c 3, .c 7, .p pv2 [pv2,pv3,pv29,pv223], .c 3, .c 211, .c 5, .c 3, .c 31, .c 7, .c 3, .c 5,
  .c 181, .c 3, .c 17, .p pv2 [pv2,pv3,pv187547], .c 3, .c 29, .c 11, .c 3, .c 13, .c 5, .c 3,
  .c 7, .c 461, .c 3, .c 5, .c 59, .c 3, .c 11, .c 7, .c 3, .p pv3 [pv2,pv29,pv89,pv109], .c 13,
  .c 3, .p pv2 [pv2,pv11,pv51151], .c 5, .c 3, .p pv3 [pv2,pv61,pv1153], .c 31, .c 3, .c 5,
  .c 937, .c 3, .c 7, .p pv5 [pv2,pv3,pv101,pv619], .c 3, .c 127, .c 17, .c 3, .c 43, .c 5, .c 3,
  .p pv7 [pv2,pv13,pv43283], .p pv11 [pv2,pv3,pv5,pv521], .c 3, .c 5, .c 23, .c 3, .c 13, .c 179,
  .c 3, .c 11,
]
private theorem h0137c11 : checkBlock 1125123 128 b0137c11 = true := by
  decide +kernel

private def b0137c12 : List Row := [
  .p pv2 [pv2,pv3,pv103,pv607], .c 3, .c 7, .c 5, .c 3, .c 19,
  .p pv3 [pv2,pv3,pv5,pv7,pv23,pv233], .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv17,pv331], .c 29,
  .c 3, .p pv5 [pv2,pv562703], .c 41, .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv7,pv80387], .c 11,
  .c 3, .c 5, .c 19, .c 3, .p pv13 [pv2,pv5,pv112543], .p pv5 [pv2,pv3,pv7,pv11,pv29], .c 3,
  .c 563, .c 7, .c 3, .c 11, .c 5, .c 3, .c 13, .c 17, .c 3, .c 5, .c 487, .c 3, .c 29, .c 271,
  .c 3, .c 7, .p pv13 [pv2,pv3,pv17,pv613], .c 3, .p pv3 [pv2,pv35171], .c 5, .c 3,
  .p pv11 [pv2,pv562739], .c 7, .c 3, .c 5, .c 11, .c 3, .c 41, .c 953, .c 3, .c 739,
  .p pv3 [pv2,pv3,pv11,pv17053], .c 3, .c 19, .c 5, .c 3, .c 7, .c 61, .c 3, .c 5, .c 31, .c 3,
  .c 599, .c 7, .c 3, .c 13, .p pv7 [pv2,pv3,pv23,pv2039], .c 3, .c 67, .c 5, .c 3,
  .p pv2 [pv2,pv173,pv3253], .c 19, .c 3, .c 5, .c 827, .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv47,pv5987], .p pv7 [pv2,pv3,pv7,pv8933], .c 3, .c 71, .c 5, .c 3,
  .p pv3 [pv2,pv43,pv409], .p pv2 [pv2,pv3,pv5,pv17,pv2207], .c 3, .c 5, .c 29, .c 3,
  .p pv2 [pv2,pv5,pv167,pv337], .c 89, .c 3, .c 17, .c 367, .c 3, .c 7, .c 5, .c 3,
  .p pv13 [pv2,pv19,pv1559], .c 127, .c 3, .c 5, .c 7, .c 3, .c 43, .c 997, .c 3, .c 19, .c 11,
  .c 3, .c 233, .c 5, .c 3, .p pv2 [pv2,pv7,pv5743], .c 13, .c 3,
]
private theorem h0137c12 : checkBlock 1125379 128 b0137c12 = true := by
  decide +kernel

private def b0137c13 : List Row := [
  .c 5, .c 383, .c 3, .c 11, .c 23, .c 3, .p pv5 [pv2,pv83,pv6781], .c 7, .c 3,
  .p pv2 [pv2,pv11,pv25583], .c 5, .c 3, .c 757, .c 59, .c 3, .c 5, .c 53, .c 3, .c 79, .c 601,
  .c 3, .c 7, .p pv3 [pv2,pv3,pv163,pv1151], .c 3, .c 13, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5,
  .c 43, .c 3, .p pv3 [pv2,pv5,pv11257], .c 31, .c 3, .c 11, .c 13, .c 3,
  .p pv3 [pv2,pv7,pv19,pv23], .c 5, .c 3, .c 7, .c 1061, .c 3, .c 5, .c 577, .c 3, .c 19, .c 7,
  .c 3, .c 41, .p pv2 [pv2,pv3,pv6949], .c 3, .c 199, .c 5, .c 3, .c 751, .c 11, .c 3, .c 5,
  .c 17, .c 3, .c 7, .p pv2 [pv2,pv3,pv11,pv37,pv461], .c 3, .p pv5 [pv2,pv389,pv1447], .c 19,
  .c 3, .c 11, .c 5, .c 3, .c 59, .c 23, .c 3, .c 5, .c 13, .c 3, .c 17, .p pv13 [pv2,pv3,pv1303],
  .c 3, .p pv2 [pv2,pv7,pv31,pv1297], .c 37, .c 3, .c 7, .c 5, .c 3, .c 29,
  .p pv7 [pv2,pv3,pv5,pv7,pv1787], .c 3, .c 5, .c 7, .c 3, .c 541, .p pv5 [pv2,pv3,pv187637],
  .c 3, .c 23, .c 79, .c 3, .p pv3 [pv2,pv140729], .c 5, .c 3, .c 11, .c 163, .c 3, .c 5, .c 71,
  .c 3, .c 677, .c 419, .c 3, .p pv3 [pv2,pv151,pv233], .c 7, .c 3, .c 491, .c 5, .c 3, .c 43,
  .p pv3 [pv2,pv3,pv5,pv37529], .c 3, .c 5, .c 61, .c 3, .c 521, .c 11, .c 3, .c 7, .c 31,
]
private theorem h0137c13 : checkBlock 1125635 128 b0137c13 = true := by
  decide +kernel

private def b0137c14 : List Row := [
  .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv562949], .c 7, .c 3, .c 5, .p pv17 [pv2,pv3,pv187651],
  .c 3, .p pv13 [pv2,pv5,pv17,pv37,pv179], .p pv23 [pv2,pv3,pv43,pv1091], .c 3, .c 13, .c 23,
  .c 3, .p pv2 [pv2,pv7,pv11489], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv13,pv2887], .c 3, .c 5,
  .c 467, .c 3, .p pv2 [pv2,pv5,pv19,pv2963], .c 7, .c 3, .c 37, .c 11, .c 3,
  .p pv3 [pv2,pv73,pv241], .c 5, .c 3, .c 19, .c 17, .c 3, .c 5, .c 281, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv31277], .c 3, .c 409, .c 47, .c 3, .c 29, .c 5, .c 3, .c 71,
  .p pv3 [pv2,pv3,pv5,pv12511], .c 3, .c 5, .c 19, .c 3, .c 181, .c 137, .c 3, .c 151, .c 379,
  .c 3, .c 7, .c 5, .c 3, .c 523, .c 13, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv112603],
  .p pv5 [pv2,pv3,pv23459], .c 3, .c 11, .c 139, .c 3, .p pv2 [pv2,pv563021], .c 5, .c 3, .c 101,
  .c 569, .c 3, .c 5, .c 23, .c 3, .c 83, .c 17, .c 3, .p pv2 [pv2,pv79,pv7127], .c 7, .c 3,
  .c 13, .c 5, .c 3, .c 109, .c 11, .c 3, .c 5, .c 373, .c 3, .c 53,
  .p pv7 [pv2,pv3,pv11,pv19,pv449], .c 3, .c 7, .c 13, .c 3, .c 11, .c 5, .c 3, .c 127, .c 7,
  .c 3, .c 5, .c 89, .c 3, .c 61, .c 727, .c 3, .c 43, .c 479, .c 3, .c 59, .c 5, .c 3, .c 7,
  .c 199, .c 3, .c 5,
]
private theorem h0137c14 : checkBlock 1125891 128 b0137c14 = true := by
  decide +kernel

private def b0137c15 : List Row := [
  .c 11, .c 3, .c 13, .c 7, .c 3, .c 29, .p pv3 [pv2,pv3,pv11,pv113,pv151], .c 3, .c 1021, .c 5,
  .c 3, .c 11, .c 73, .c 3, .c 5, .c 13, .c 3, .c 7, .c 359, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv7,pv41,pv109], .c 3, .c 241, .c 5, .c 3, .c 17, .p pv19 [pv2,pv3,pv5,pv1877],
  .c 3, .c 5, .c 131, .c 3, .p pv7 [pv2,pv5,pv112621], .c 11, .c 3, .c 503,
  .p pv3 [pv2,pv3,pv23,pv8161], .c 3, .c 7, .c 5, .c 3, .c 13, .c 659, .c 3, .c 5, .c 7, .c 3,
  .c 23, .c 37, .c 3, .p pv5 [pv2,pv11,pv51193], .c 197, .c 3, .p pv2 [pv2,pv281563], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv80447], .c 31, .c 3, .c 5, .c 17, .c 3, .c 113, .c 29, .c 3, .c 137, .c 7,
  .c 3, .p pv2 [pv2,pv19,pv107,pv277], .c 5, .c 3, .c 397, .c 149, .c 3, .c 5, .c 109, .c 3,
  .c 11, .c 53, .c 3, .c 7, .c 151, .c 3, .p pv3 [pv2,pv11,pv12799], .c 5, .c 3,
  .p pv23 [pv2,pv17,pv157,pv211], .c 7, .c 3, .c 5, .c 191, .c 3, .c 29, .c 13, .c 3, .c 67,
  .c 19, .c 3, .p pv5 [pv2,pv7,pv43,pv1871], .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv2503], .c 3,
  .c 5, .p pv13 [pv2,pv3,pv7,pv11,pv23,pv53], .c 3, .p pv3 [pv2,pv5,pv29,pv971], .c 7, .c 3,
  .c 11, .c 17, .c 3, .c 223, .c 5, .c 3, .c 23, .p pv17 [pv2,pv3,pv5,pv18773], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv17,pv409], .c 3, .c 7, .c 41, .c 3, .p pv2 [pv2,pv19,pv14821],
  .p pv3 [pv2,pv3,pv7,pv13,pv2063], .c 3,
]
private theorem h0137c15 : checkBlock 1126147 128 b0137c15 = true := by
  decide +kernel

private def b0137c16 : List Row := [
  .c 17, .c 5, .c 3, .c 53, .c 11, .c 3, .c 5, .c 509, .c 3, .p pv2 [pv2,pv5,pv17,pv3313], .c 353,
  .c 3, .c 647, .c 263, .c 3, .c 7, .c 5, .c 3, .p pv13 [pv2,pv563219],
  .p pv47 [pv2,pv3,pv5,pv7,pv149], .c 3, .c 5, .c 7, .c 3, .c 229, .c 19, .c 3,
  .p pv3 [pv2,pv139,pv1013], .p pv2 [pv2,pv3,pv62581], .c 3, .c 13, .c 5, .c 3, .c 131, .c 17,
  .c 3, .c 5, .c 11, .c 3, .c 977, .p pv2 [pv2,pv3,pv7,pv26821], .c 3, .c 59, .c 7, .c 3, .c 163,
  .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv751], .c 3, .c 5, .c 701, .c 3, .c 103,
  .p pv7 [pv2,pv3,pv7823], .c 3, .c 7, .p pv7 [pv2,pv3,pv191,pv983], .c 3,
  .p pv2 [pv2,pv17,pv1949], .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv73,pv643],
  .c 3, .c 13, .c 11, .c 3, .c 271, .c 443, .c 3, .p pv5 [pv2,pv7,pv20117], .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv2347], .c 3, .c 5, .c 13, .c 3, .c 31, .c 7, .c 3,
  .p pv3 [pv2,pv11,pv37,pv173], .p pv2 [pv2,pv3,pv187763], .c 3, .c 571, .c 5, .c 3, .c 149,
  .c 337, .c 3, .c 5, .p pv5 [pv2,pv3,pv223,pv421], .c 3, .c 7, .c 107, .c 3, .c 17, .c 11, .c 3,
  .c 37, .c 5, .c 3, .c 13, .c 29, .c 3, .c 5, .p pv2 [pv2,pv3,pv179,pv1049], .c 3, .c 11, .c 31,
  .c 3, .c 47, .c 41, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv140831], .c 89, .c 3, .c 5, .c 7,
]
private theorem h0137c16 : checkBlock 1126403 128 b0137c16 = true := by
  decide +kernel

private def b0137c17 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv56333], .p pv3 [pv2,pv3,pv19,pv9883], .c 3, .p pv2 [pv2,pv433,pv1301],
  .p pv2 [pv2,pv3,pv93889], .c 3, .c 719, .c 5, .c 3, .c 29, .c 19, .c 3, .c 5, .c 37, .c 3,
  .c 419, .p pv5 [pv2,pv3,pv7,pv17,pv263], .c 3, .c 11, .c 7, .c 3, .p pv5 [pv2,pv563351], .c 5,
  .c 3, .c 17, .p pv37 [pv2,pv3,pv5,pv13,pv107], .c 3, .c 5, .c 103, .c 3, .c 41, .c 13, .c 3,
  .c 7, .c 43, .c 3, .c 109, .c 5, .c 3, .c 67, .c 7, .c 3, .c 5, .c 23, .c 3,
  .p pv13 [pv2,pv5,pv4507], .c 311, .c 3, .c 19, .p pv3 [pv2,pv3,pv187793], .c 3, .c 11, .c 5,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv23,pv71], .c 3, .c 5, .c 17, .c 3,
  .p pv3 [pv2,pv5,pv53,pv1063], .c 7, .c 3, .p pv2 [pv2,pv383,pv1471], .c 157, .c 3, .c 23, .c 5,
  .c 3, .c 881, .c 13, .c 3, .c 5, .c 11, .c 3, .c 7, .c 853, .c 3, .c 107, .c 31, .c 3,
  .p pv5 [pv2,pv563411], .c 5, .c 3, .c 11, .p pv17 [pv2,pv3,pv5,pv37561], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv113,pv277], .c 3, .c 59, .p pv2 [pv2,pv3,pv109,pv1723], .c 3,
  .p pv5 [pv2,pv7,pv80489], .c 97, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv43,pv13103],
  .p pv29 [pv2,pv3,pv5,pv7,pv2683], .c 3, .c 5, .c 7, .c 3, .c 19, .c 11, .c 3, .c 929, .c 13,
  .c 3, .c 1031, .c 5, .c 3, .p pv3 [pv2,pv7,pv20123], .c 83, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv17,pv1381], .c 3, .c 43, .c 541, .c 3, .c 911, .c 7, .c 3, .c 17,
]
private theorem h0137c17 : checkBlock 1126659 128 b0137c17 = true := by
  decide +kernel

private def b0137c18 : List Row := [
  .c 5, .c 3, .c 47, .c 349, .c 3, .c 5, .c 193, .c 3, .c 13, .c 389, .c 3, .c 7, .c 11, .c 3,
  .c 31, .c 5, .c 3, .c 113, .c 7, .c 3, .c 5, .c 13, .c 3, .c 11, .p pv3 [pv2,pv3,pv137,pv457],
  .c 3, .c 41, .c 29, .c 3, .p pv2 [pv2,pv7,pv11,pv3659], .c 5, .c 3, .c 7, .c 17, .c 3, .c 5,
  .c 43, .c 3, .p pv13 [pv2,pv5,pv251,pv449], .c 7, .c 3, .c 307,
  .p pv11 [pv2,pv3,pv17,pv29,pv127], .c 3, .c 1033, .c 5, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv5,pv37567], .c 3, .c 5, .c 421, .c 3, .c 7, .c 19, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv7,pv13417], .c 3, .p pv3 [pv2,pv17,pv8287], .c 5, .c 3,
  .p pv7 [pv2,pv11,pv51229], .c 761, .c 3, .c 5, .c 73, .c 3, .p pv2 [pv2,pv5,pv22541], .c 1009,
  .c 3, .c 37, .c 101, .c 3, .c 7, .c 5, .c 3, .c 23, .c 11, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv19,pv1483], .c 17, .c 3, .c 13, .c 271, .c 3, .c 11, .c 5, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv5,pv13,pv17], .c 3, .c 5, .c 47, .c 3, .p pv13 [pv2,pv5,pv269,pv419], .c 13,
  .c 3, .c 17, .c 7, .c 3, .p pv2 [pv2,pv563561], .c 5, .c 3, .c 31, .c 37, .c 3, .c 5, .c 11,
  .c 3, .c 67, .c 29, .c 3, .c 7, .p pv19 [pv2,pv3,pv11,pv8539], .c 3, .p pv3 [pv2,pv13,pv5419],
  .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv187861], .c 3,
]
private theorem h0137c18 : checkBlock 1126915 128 b0137c18 = true := by
  decide +kernel

private def b0137c19 : List Row := [
  .c 293, .c 757, .c 3, .p pv3 [pv2,pv140897], .c 643, .c 3, .p pv5 [pv2,pv7,pv80513], .c 5, .c 3,
  .c 7, .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv71], .c 3, .c 29, .c 7, .c 3, .c 23,
  .p pv7 [pv2,pv3,pv67,pv701], .c 3, .c 19, .c 5, .c 3, .c 17, .p pv11 [pv2,pv3,pv5,pv18787],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv187871], .c 3, .c 7, .c 821, .c 3, .c 97,
  .p pv3 [pv2,pv3,pv7,pv26839], .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv47,pv1499], .c 19, .c 3,
  .c 5, .c 53, .c 3, .c 101, .p pv11 [pv2,pv3,pv187877], .c 3, .c 71, .c 11, .c 3, .c 7, .c 5,
  .c 3, .c 37, .p pv17 [pv2,pv3,pv5,pv7,pv11,pv61], .c 3, .c 5, .c 7, .c 3, .c 11, .c 593, .c 3,
  .p pv3 [pv2,pv8807], .c 23, .c 3, .p pv5 [pv2,pv11,pv51241], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv13,pv19,pv163], .p pv3 [pv2,pv3,pv5,pv53,pv709], .c 3, .c 5, .c 29, .c 3,
  .c 13, .p pv3 [pv2,pv3,pv7,pv23,pv389], .c 3, .c 19, .c 7, .c 3, .p pv2 [pv2,pv281833], .c 5,
  .c 3, .c 73, .c 61, .c 3, .c 5, .c 13, .c 3, .p pv7 [pv2,pv5,pv7,pv3221], .c 37, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv6959], .c 3, .c 53, .c 5, .c 3, .p pv3 [pv2,pv11,pv23,pv557], .c 7, .c 3,
  .c 5, .c 31, .c 3, .p pv2 [pv2,pv5,pv56369], .p pv11 [pv2,pv3,pv187897], .c 3, .c 109, .c 17,
  .c 3, .p pv3 [pv2,pv7,pv719], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv17,pv1579], .c 3, .p pv2 [pv2,pv5,pv112741], .c 7, .c 3, .c 43, .c 457,
  .c 3, .c 11, .c 5,
]
private theorem h0137c19 : checkBlock 1127171 128 b0137c19 = true := by
  decide +kernel

private def b0137c20 : List Row := [
  .c 3, .c 139, .c 59, .c 3, .c 5, .c 23, .c 3, .c 7, .p pv2 [pv2,pv3,pv187907], .c 3,
  .p pv5 [pv2,pv563723], .c 181, .c 3, .p pv2 [pv2,pv89,pv3167], .c 5, .c 3, .c 41,
  .p pv7 [pv2,pv3,pv5,pv19,pv23,pv43], .c 3, .c 5, .c 11, .c 3, .c 163, .c 191, .c 3, .c 13,
  .c 19, .c 3, .c 7, .c 5, .c 3, .c 11, .c 17, .c 3, .c 5, .c 7, .c 3, .c 31, .c 13, .c 3,
  .p pv2 [pv2,pv23,pv127,pv193], .c 227, .c 3, .p pv3 [pv2,pv140939], .c 5, .c 3, .c 641, .c 179,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv187921], .c 3, .p pv2 [pv2,pv5,pv47,pv2399], .c 11, .c 3,
  .p pv5 [pv2,pv19,pv3709], .c 7, .c 3, .c 67, .c 5, .c 3, .c 29, .c 71, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv31321], .c 3, .p pv3 [pv2,pv5,pv7,pv4027], .c 31, .c 3, .c 7, .c 317, .c 3,
  .p pv2 [pv2,pv281893], .c 5, .c 3, .c 373, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv187931], .c 3,
  .c 883, .c 17, .c 3, .c 631, .c 11, .c 3, .p pv2 [pv2,pv7,pv239,pv337], .c 5, .c 3, .c 7,
  .c 307, .c 3, .c 5, .p pv11 [pv2,pv3,pv7,pv839], .c 3, .c 11, .c 7, .c 3, .c 17,
  .p pv11 [pv2,pv3,pv53,pv197], .c 3, .c 13, .c 5, .c 3, .c 241, .p pv13 [pv2,pv3,pv5,pv9397],
  .c 3, .c 5, .c 137, .c 3, .c 7, .c 281, .c 3, .p pv3 [pv2,pv31,pv4547], .c 13, .c 3,
  .p pv5 [pv2,pv563831], .c 5, .c 3, .c 19, .c 47, .c 3, .c 5, .c 67, .c 3, .c 53,
]
private theorem h0137c20 : checkBlock 1127427 128 b0137c20 = true := by
  decide +kernel

private def b0137c21 : List Row := [
  .p pv5 [pv2,pv3,pv6961], .c 3, .c 11, .c 563, .c 3, .c 7, .c 5, .c 3, .c 193,
  .p pv37 [pv2,pv3,pv5,pv7,pv179], .c 3, .c 5, .c 7, .c 3, .c 13, .c 23, .c 3, .c 331, .c 89,
  .c 3, .c 29, .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv113,pv499],
  .c 251, .c 3, .c 103, .c 7, .c 3, .c 11, .c 5, .c 3, .c 23, .c 43, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv101,pv1861], .c 3, .c 787, .p pv2 [pv2,pv3,pv31327], .c 3, .c 7, .c 131, .c 3,
  .c 19, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv5639],
  .p pv3 [pv2,pv3,pv13,pv19,pv761], .c 3, .c 773, .p pv17 [pv2,pv3,pv11,pv89], .c 3,
  .p pv2 [pv2,pv7,pv47,pv857], .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 491, .c 3, .c 17, .c 7,
  .c 3, .p pv2 [pv2,pv281959], .c 29, .c 3, .c 1061, .c 5, .c 3, .p pv3 [pv2,pv17,pv8293], .c 23,
  .c 3, .c 5, .p pv7 [pv2,pv3,pv23497], .c 3, .c 7, .c 11, .c 3, .c 13, .c 41, .c 3, .c 31, .c 5,
  .c 3, .c 179, .p pv7 [pv2,pv3,pv5,pv13,pv241], .c 3, .c 5, .c 83, .c 3,
  .p pv2 [pv2,pv5,pv43,pv61], .c 13, .c 3, .c 19, .c 17, .c 3, .c 7, .c 5, .c 3, .c 701,
  .p pv7 [pv2,pv3,pv5,pv7,pv41,pv131], .c 3, .c 5, .c 7, .c 3, .c 137, .c 73, .c 3, .c 431, .c 11,
  .c 3, .c 17, .c 5, .c 3,
]
private theorem h0137c21 : checkBlock 1127683 128 b0137c21 = true := by
  decide +kernel

private def b0137c22 : List Row := [
  .c 337, .c 863, .c 3, .c 5, .p pv3 [pv2,pv3,pv53,pv3547], .c 3, .c 11, .c 47, .c 3,
  .p pv2 [pv2,pv281989], .c 7, .c 3, .c 227, .c 5, .c 3, .p pv3 [pv2,pv101,pv349], .c 13, .c 3,
  .c 5, .c 71, .c 3, .p pv17 [pv2,pv5,pv7,pv1151], .p pv5 [pv2,pv3,pv37,pv5081], .c 3, .c 7,
  .c 23, .c 3, .p pv3 [pv2,pv19,pv41,pv181], .c 5, .c 3, .c 53, .c 7, .c 3, .c 5, .c 263, .c 3,
  .c 19, .c 29, .c 3, .c 11, .c 37, .c 3, .c 13, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv19,pv1979], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv13,pv1033], .c 3, .c 79,
  .c 7, .c 3, .c 47, .c 13, .c 3, .c 83, .c 5, .c 3, .c 31, .c 11, .c 3, .c 5, .c 461, .c 3, .c 7,
  .c 61, .c 3, .c 601, .c 67, .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv13,pv10847],
  .p pv31 [pv2,pv3,pv5,pv31,pv1213], .c 3, .c 5, .c 347, .c 3, .c 13, .c 17, .c 3,
  .p pv2 [pv2,pv7,pv19,pv4241], .p pv2 [pv2,pv3,pv94009], .c 3, .c 7, .c 5, .c 3, .c 71, .c 31,
  .c 3, .c 5, .c 7, .c 3, .c 199, .c 173, .c 3, .c 17, .c 59, .c 3, .p pv5 [pv2,pv73,pv7727],
  .c 5, .c 3, .c 11, .p pv13 [pv2,pv3,pv5,pv23,pv109], .c 3, .c 5, .c 223, .c 3,
  .p pv3 [pv2,pv5,pv11,pv641], .c 19, .c 3, .c 37, .c 7, .c 3, .c 23, .c 5, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv5,pv18803], .c 3, .c 5, .c 29, .c 3, .c 43, .c 11,
]
private theorem h0137c22 : checkBlock 1127939 128 b0137c22 = true := by
  decide +kernel

private def b0137c23 : List Row := [
  .c 3, .c 7, .c 79, .c 3, .c 317, .c 5, .c 3, .p pv3 [pv2,pv107,pv659], .c 7, .c 3, .c 5, .c 211,
  .c 3, .c 277, .p pv3 [pv2,pv3,pv17,pv1229], .c 3, .p pv2 [pv2,pv11,pv51283], .c 503, .c 3,
  .p pv3 [pv2,pv7,pv20147], .c 5, .c 3, .c 7, .c 37, .c 3, .c 5, .p pv7 [pv2,pv3,pv7,pv26863],
  .c 3, .p pv2 [pv2,pv5,pv4513], .c 7, .c 3, .c 13, .c 11, .c 3, .c 139, .c 5, .c 3, .c 829,
  .c 101, .c 3, .c 5, .c 19, .c 3, .c 7, .c 13, .c 3, .p pv5 [pv2,pv163,pv3461],
  .p pv13 [pv2,pv3,pv7,pv23,pv73], .c 3, .p pv2 [pv2,pv11,pv25643], .c 5, .c 3,
  .p pv2 [pv2,pv564149], .p pv2 [pv2,pv3,pv5,pv3761], .c 3, .c 5, .c 17, .c 3, .c 23,
  .p pv11 [pv2,pv3,pv15671], .c 3, .c 53, .c 239, .c 3, .c 7, .c 5, .c 3, .c 47, .c 463, .c 3,
  .c 5, .c 7, .c 3, .c 17, .c 293, .c 3, .c 11, .p pv2 [pv2,pv3,pv13,pv2411], .c 3, .c 19, .c 5,
  .c 3, .c 157, .c 13, .c 3, .c 5, .c 419, .c 3, .p pv2 [pv2,pv5,pv53,pv2129],
  .p pv2 [pv2,pv3,pv7,pv19,pv101], .c 3, .c 149, .c 7, .c 3, .p pv5 [pv2,pv564191], .c 5, .c 3,
  .c 37, .c 11, .c 3, .c 5, .p pv23 [pv2,pv3,pv94033], .c 3, .c 97, .c 23, .c 3, .c 7, .c 17,
  .c 3, .c 11, .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv17,pv23,pv37], .c 3,
  .c 31, .p pv5 [pv2,pv3,pv23509], .c 3, .c 619, .c 13, .c 3, .c 17, .c 5, .c 3, .c 7,
]
private theorem h0137c23 : checkBlock 1128195 128 b0137c23 = true := by
  decide +kernel

private def b0137c24 : List Row := [
  .p pv2 [pv2,pv3,pv5,pv7523], .c 3, .c 5, .c 11, .c 3, .c 547, .c 7, .c 3, .c 19, .c 137, .c 3,
  .c 101, .c 5, .c 3, .c 11, .c 67, .c 3, .c 5, .c 257, .c 3, .c 7, .c 31, .c 3,
  .p pv3 [pv2,pv251,pv281], .p pv3 [pv2,pv3,pv7,pv97,pv277], .c 3, .p pv5 [pv2,pv564251], .c 5,
  .c 3, .p pv2 [pv2,pv282127], .c 17, .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv89,pv317], .c 11,
  .c 3, .p pv5 [pv2,pv7,pv149,pv541], .c 53, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv564269], .c 23,
  .c 3, .c 5, .c 7, .c 3, .c 83, .p pv7 [pv2,pv3,pv59,pv797], .c 3, .p pv2 [pv2,pv11,pv13,pv1973],
  .c 677, .c 3, .c 761, .c 5, .c 3, .c 13, .c 103, .c 3, .c 5, .p pv11 [pv2,pv3,pv2939], .c 3,
  .c 19, .p pv5 [pv2,pv3,pv7,pv13,pv53], .c 3, .c 23, .c 7, .c 3, .c 29, .c 5, .c 3,
  .p pv17 [pv2,pv564299], .p pv29 [pv2,pv3,pv5,pv11,pv19], .c 3, .c 5, .c 41, .c 3, .c 11, .c 17,
  .c 3, .c 7, .c 19, .c 3, .p pv5 [pv2,pv11,pv29,pv61], .c 5, .c 3, .p pv2 [pv2,pv282157], .c 7,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv107,pv293], .c 3, .p pv3 [pv2,pv5,pv3527],
  .p pv2 [pv2,pv3,pv188107], .c 3, .c 13, .c 127, .c 3, .c 73, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv13,pv1447], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv11,pv349], .c 3, .c 397,
  .c 7, .c 3, .c 11, .c 23, .c 3, .c 61, .c 5, .c 3, .c 41, .p pv2 [pv2,pv3,pv5,pv12541], .c 3,
  .c 5, .p pv5 [pv2,pv3,pv131,pv359], .c 3, .c 7, .p pv3 [pv2,pv3,pv23,pv8179], .c 3,
]
private theorem h0137c24 : checkBlock 1128451 128 b0137c24 = true := by
  decide +kernel

private def b0137c25 : List Row := [
  .c 43, .c 29, .c 3, .p pv5 [pv2,pv13,pv10853], .c 5, .c 3, .p pv7 [pv2,pv564359], .c 11, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv73,pv859], .c 3, .p pv2 [pv2,pv5,pv41,pv2753], .c 19, .c 3,
  .p pv5 [pv2,pv7,pv5039], .c 467, .c 3, .c 7, .c 5, .c 3, .c 17, .c 13, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv28219], .p pv3 [pv2,pv3,pv20903], .c 3, .c 29, .p pv23 [pv2,pv3,pv5879], .c 3,
  .p pv2 [pv2,pv31,pv9103], .c 5, .c 3, .p pv2 [pv2,pv7,pv80627], .p pv2 [pv2,pv3,pv5,pv6271],
  .c 3, .c 5, .c 11, .c 3, .c 347, .c 43, .c 3, .c 239, .c 7, .c 3, .c 13, .c 5, .c 3, .c 11,
  .p pv13 [pv2,pv3,pv5,pv191,pv197], .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv7,pv11,pv733],
  .p pv3 [pv2,pv3,pv188137], .c 3, .c 7, .c 13, .c 3, .c 37, .c 5, .c 3, .c 307, .c 7, .c 3, .c 5,
  .c 19, .c 3, .c 17, .c 11, .c 3, .c 193, .c 631, .c 3, .c 23, .c 5, .c 3, .c 7, .c 227, .c 3,
  .c 5, .c 101, .c 3, .c 13, .c 7, .c 3, .c 283, .p pv13 [pv2,pv3,pv15679], .c 3, .c 47, .c 5,
  .c 3, .p pv2 [pv2,pv564449], .p pv13 [pv2,pv3,pv5,pv53,pv71], .c 3, .c 5, .c 13, .c 3, .c 7,
  .c 109, .c 3, .p pv2 [pv2,pv282229], .c 11, .c 3, .c 19, .c 5, .c 3, .c 293,
  .p pv2 [pv2,pv3,pv5,pv11,pv311], .c 3, .c 5, .p pv11 [pv2,pv3,pv17,pv2767], .c 3, .c 11,
  .p pv3 [pv2,pv3,pv19,pv3301], .c 3, .p pv2 [pv2,pv7,pv13,pv6203], .p pv2 [pv2,pv3,pv94079],
  .c 3, .c 7, .c 5, .c 3, .c 13, .c 19,
]
private theorem h0137c25 : checkBlock 1128707 128 b0137c25 = true := by
  decide +kernel

private def b0137c26 : List Row := [
  .c 3, .c 5, .c 7, .c 3, .c 71, .c 149, .c 3, .p pv3 [pv2,pv41,pv1721],
  .p pv2 [pv2,pv3,pv23,pv101], .c 3, .c 97, .c 5, .c 3, .c 31, .c 313, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv2851], .c 3, .c 23, .c 479, .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv282253], .c 5, .c 3, .p pv2 [pv2,pv11,pv19,pv37,pv73], .c 17, .c 3, .c 5, .c 151,
  .c 3, .c 727, .p pv5 [pv2,pv3,pv5227], .c 3, .c 7, .c 557, .c 3, .p pv2 [pv2,pv71,pv7951], .c 5,
  .c 3, .c 61, .c 7, .c 3, .c 5, .c 29, .c 3, .c 211, .c 13, .c 3, .c 541, .c 1033, .c 3, .c 11,
  .c 5, .c 3, .c 7, .c 47, .c 3, .c 5, .c 167, .c 3, .c 73, .c 7, .c 3, .c 139, .c 41, .c 3,
  .p pv5 [pv2,pv13,pv43427], .c 5, .c 3, .p pv2 [pv2,pv439,pv643],
  .p pv3 [pv2,pv3,pv5,pv61,pv617], .c 3, .c 5, .c 11, .c 3, .c 7, .c 17, .c 3,
  .p pv5 [pv2,pv199,pv2837], .c 37, .c 3, .p pv2 [pv2,pv19,pv83,pv179], .c 5, .c 3, .c 11, .c 13,
  .c 3, .c 5, .c 79, .c 3, .c 19, .p pv23 [pv2,pv3,pv5881], .c 3, .c 17, .p pv3 [pv2,pv3,pv62731],
  .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv70573], .c 61, .c 3, .c 5, .c 7, .c 3, .c 41, .c 11, .c 3,
  .p pv2 [pv2,pv564593], .c 19, .c 3, .c 13, .c 5, .c 3, .c 229, .c 59, .c 3, .c 5, .c 443, .c 3,
  .p pv2 [pv2,pv5,pv112921], .p pv2 [pv2,pv3,pv7,pv4481], .c 3, .p pv3 [pv2,pv11,pv401],
]
private theorem h0137c26 : checkBlock 1128963 128 b0137c26 = true := by
  decide +kernel

private def b0137c27 : List Row := [
  .c 7, .c 3, .c 43, .c 5, .c 3, .p pv2 [pv2,pv282307], .c 23, .c 3, .c 5, .c 31, .c 3, .c 311,
  .c 193, .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv282313], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5,
  .c 389, .c 3, .c 11, .c 971, .c 3, .c 23, .c 601, .c 3, .p pv2 [pv2,pv7,pv11,pv7333], .c 5,
  .c 3, .c 7, .c 137, .c 3, .c 5, .c 13, .c 3, .c 157, .c 7, .c 3, .p pv2 [pv2,pv564653], .c 43,
  .c 3, .p pv3 [pv2,pv35291], .c 5, .c 3, .c 59, .c 89, .c 3, .c 5, .c 17, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv94111], .c 3, .c 11, .c 281, .c 3, .p pv5 [pv2,pv564671], .c 5, .c 3, .c 13,
  .c 37, .c 3, .c 5, .c 883, .c 3, .c 17, .c 47, .c 3, .p pv5 [pv2,pv7,pv80669], .c 23, .c 3,
  .c 7, .c 5, .c 3, .c 19, .c 11, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv112939], .c 1039,
  .c 3, .c 71, .p pv13 [pv2,pv3,pv19,pv9907], .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv7,pv2521],
  .c 127, .c 3, .c 5, .c 19, .c 3, .c 167, .c 31, .c 3, .c 13, .c 7, .c 3, .p pv3 [pv2,pv141179],
  .c 5, .c 3, .p pv11 [pv2,pv23,pv43,pv571], .p pv41 [pv2,pv3,pv5,pv13,pv181], .c 3, .c 5, .c 11,
  .c 3, .c 919, .c 13, .c 3, .c 7, .p pv7 [pv2,pv3,pv11,pv109,pv157], .c 3, .c 17, .c 5, .c 3,
  .c 11, .c 7, .c 3,
]
private theorem h0137c27 : checkBlock 1129219 128 b0137c27 = true := by
  decide +kernel

private def b0137c28 : List Row := [
  .c 5, .p pv5 [pv2,pv3,pv61,pv1543], .c 3, .c 43, .c 53, .c 3, .p pv5 [pv2,pv67,pv8429],
  .p pv19 [pv2,pv3,pv23531], .c 3, .c 19, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv251], .c 3,
  .c 5, .c 23, .c 3, .p pv11 [pv2,pv5,pv112951], .c 7, .c 3, .c 173,
  .p pv19 [pv2,pv3,pv13,pv1609], .c 3, .p pv2 [pv2,pv564761], .c 5, .c 3, .c 73, .c 13, .c 3,
  .c 5, .c 61, .c 3, .c 7, .c 421, .c 3, .c 31, .c 719, .c 3, .c 23, .c 5, .c 3,
  .p pv7 [pv2,pv564779], .p pv29 [pv2,pv3,pv5,pv9413], .c 3, .c 5, .c 43, .c 3,
  .p pv2 [pv2,pv5,pv13,pv8689], .c 37, .c 3, .p pv3 [pv2,pv7,pv23,pv877], .c 11, .c 3, .c 7, .c 5,
  .c 3, .c 53, .c 41, .c 3, .c 5, .c 7, .c 3, .c 11, .p pv2 [pv2,pv3,pv73,pv2579], .c 3, .c 19,
  .c 13, .c 3, .c 131, .c 5, .c 3, .p pv2 [pv2,pv7,pv80687], .c 79, .c 3, .c 5, .c 607, .c 3,
  .c 151, .c 17, .c 3, .c 29, .c 7, .c 3, .p pv2 [pv2,pv53,pv10657], .c 5, .c 3, .c 661, .c 431,
  .c 3, .c 5, .c 229, .c 3, .c 13, .p pv3 [pv2,pv3,pv97,pv647], .c 3, .c 7, .c 179, .c 3, .c 41,
  .c 5, .c 3, .p pv11 [pv2,pv11,pv51349], .c 7, .c 3, .c 5, .c 13, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv47,pv2003], .c 3, .c 433, .p pv2 [pv2,pv3,pv62761], .c 3, .c 331, .c 5, .c 3,
  .c 7, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv4483], .c 3, .c 19, .c 7, .c 3, .c 617,
  .p pv7 [pv2,pv3,pv1471],
]
private theorem h0137c28 : checkBlock 1129475 128 b0137c28 = true := by
  decide +kernel

private def b0137c29 : List Row := [
  .c 3, .c 11, .c 5, .c 3, .c 13, .p pv17 [pv2,pv3,pv5,pv19,pv991], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv188291], .c 3, .c 7, .c 29, .c 3, .p pv2 [pv2,pv282439], .c 19, .c 3,
  .p pv2 [pv2,pv564881], .c 5, .c 3, .c 17, .c 947, .c 3, .c 5, .c 11, .c 3, .c 61, .c 23, .c 3,
  .p pv5 [pv2,pv7,pv17,pv47,pv101], .p pv7 [pv2,pv3,pv11,pv317], .c 3, .c 7, .c 5, .c 3, .c 11,
  .c 53, .c 3, .c 5, .c 7, .c 3, .c 29, .c 107, .c 3, .c 13, .p pv2 [pv2,pv3,pv188303], .c 3,
  .c 71, .c 5, .c 3, .c 23, .p pv17 [pv2,pv3,pv5,pv13,pv2897], .c 3, .c 5, .c 17, .c 3,
  .p pv3 [pv2,pv5,pv29,pv487], .c 11, .c 3, .p pv5 [pv2,pv564923], .c 7, .c 3,
  .p pv2 [pv2,pv23,pv12281], .c 5, .c 3, .p pv2 [pv2,pv79,pv7151], .p pv2 [pv2,pv3,pv5,pv6277],
  .c 3, .c 5, .c 149, .c 3, .c 17, .c 19, .c 3, .c 7, .c 83, .c 3, .c 277, .c 5, .c 3,
  .p pv3 [pv2,pv17,pv31,pv67], .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv5231], .c 3, .c 281, .c 61,
  .c 3, .c 53, .c 11, .c 3, .c 677, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 29, .c 3, .c 11, .c 7,
  .c 3, .c 79, .c 17, .c 3, .c 37, .c 5, .c 3, .c 19, .p pv3 [pv2,pv3,pv5,pv31], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv17,pv29,pv191], .c 3, .c 7, .p pv2 [pv2,pv3,pv83,pv2269], .c 3, .c 23,
  .c 1063, .c 3, .c 13, .c 5, .c 3, .c 823, .c 31, .c 3, .c 5,
]
private theorem h0137c29 : checkBlock 1129731 128 b0137c29 = true := by
  decide +kernel

private def b0137c30 : List Row := [
  .c 19, .c 3, .p pv11 [pv2,pv5,pv17,pv23], .c 367, .c 3, .c 11, .c 13, .c 3, .c 7, .c 5, .c 3,
  .c 571, .p pv2 [pv2,pv3,pv5,pv7,pv5381], .c 3, .c 5, .c 7, .c 3, .c 47,
  .p pv3 [pv2,pv3,pv67,pv937], .c 3, .c 59, .c 257, .c 3, .c 89, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv13,pv887], .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv127,pv1483], .c 3, .c 13,
  .p pv13 [pv2,pv3,pv7,pv11,pv1223], .c 3, .p pv3 [pv2,pv141257], .c 7, .c 3, .c 11, .c 5, .c 3,
  .c 269, .c 1019, .c 3, .c 5, .c 13, .c 3, .p pv17 [pv2,pv5,pv7,pv1009], .c 41, .c 3, .c 7,
  .c 67, .c 3, .c 443, .c 5, .c 3, .p pv2 [pv2,pv565049], .c 7, .c 3, .c 5, .c 11, .c 3, .c 263,
  .c 73, .c 3, .p pv2 [pv2,pv13,pv103,pv211], .c 53, .c 3, .p pv5 [pv2,pv7,pv89,pv907], .c 5,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv29,pv433], .c 3, .c 5, .c 131, .c 3, .c 941, .c 7, .c 3,
  .c 61, .c 541, .c 3, .c 557, .c 5, .c 3, .c 29, .c 457, .c 3, .c 5, .c 31, .c 3, .c 7, .c 11,
  .c 3, .c 17, .c 347, .c 3, .c 463, .c 5, .c 3, .c 197, .p pv3 [pv2,pv3,pv5,pv101,pv373], .c 3,
  .c 5, .c 23, .c 3, .c 757, .c 523, .c 3, .c 13, .c 47, .c 3, .c 7, .c 5, .c 3, .c 103, .c 109,
  .c 3, .c 5, .c 7, .c 3, .c 239, .c 13, .c 3, .p pv2 [pv2,pv282559], .c 11, .c 3,
]
private theorem h0137c30 : checkBlock 1129987 128 b0137c30 = true := by
  decide +kernel

private def b0137c31 : List Row := [
  .c 23, .c 5, .c 3, .c 71, .p pv3 [pv2,pv3,pv5,pv11,pv137], .c 3, .c 5,
  .p pv13 [pv2,pv3,pv47,pv167], .c 3, .c 11, .c 59, .c 3, .p pv2 [pv2,pv23,pv24571], .c 7, .c 3,
  .p pv5 [pv2,pv11,pv13,pv19], .c 5, .c 3, .c 17, .p pv23 [pv2,pv3,pv5,pv9419], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv257,pv733], .c 3, .c 19, .p pv2 [pv2,pv3,pv31397], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv13,pv43,pv337], .c 3, .c 47, .c 5, .c 3, .c 647, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv8563], .c 3, .p pv3 [pv2,pv5,pv71,pv199], .c 881, .c 3, .c 11, .c 19,
  .c 3, .c 29, .c 5, .c 3, .c 7, .c 43, .c 3, .c 5, .c 17, .c 3, .p pv41 [pv2,pv5,pv13,pv37,pv47],
  .c 7, .c 3, .c 67, .p pv17 [pv2,pv3,pv23,pv8191], .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv8831],
  .c 11, .c 3, .c 5, .c 83, .c 3, .c 7, .c 857, .c 3, .c 37, .c 13, .c 3, .c 11, .c 5, .c 3,
  .c 131, .c 193, .c 3, .c 5, .p pv3 [pv2,pv3,pv188401], .c 3, .c 41, .p pv19 [pv2,pv3,pv94201],
  .c 3, .p pv3 [pv2,pv7,pv10093], .c 401, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv13,pv21739],
  .p pv3 [pv2,pv3,pv5,pv7,pv769], .c 3, .c 5, .c 7, .c 3, .c 13, .c 19, .c 3,
  .p pv5 [pv2,pv31,pv18233], .c 17, .c 3, .c 877, .c 5, .c 3, .c 11, .c 37, .c 3, .c 5, .c 13,
  .c 3, .p pv17 [pv2,pv5,pv11,pv43,pv239], .c 23, .c 3, .c 31, .c 7, .c 3, .c 17, .c 5, .c 3,
  .c 509, .c 47, .c 3, .c 5, .p pv5 [pv2,pv3,pv23],
]
private theorem h0137c31 : checkBlock 1130243 128 b0137c31 = true := by
  decide +kernel

def rows0137 : List Row :=
  b0137c00 ++ b0137c01 ++ b0137c02 ++ b0137c03 ++ b0137c04 ++ b0137c05 ++ b0137c06 ++ b0137c07 ++
  b0137c08 ++ b0137c09 ++ b0137c10 ++ b0137c11 ++ b0137c12 ++ b0137c13 ++ b0137c14 ++ b0137c15 ++
  b0137c16 ++ b0137c17 ++ b0137c18 ++ b0137c19 ++ b0137c20 ++ b0137c21 ++ b0137c22 ++ b0137c23 ++
  b0137c24 ++ b0137c25 ++ b0137c26 ++ b0137c27 ++ b0137c28 ++ b0137c29 ++ b0137c30 ++ b0137c31

attribute [local irreducible] checkBlock checkRows checkPrime

theorem checked0137 : checkBlock 1122307 4096 rows0137 = true :=
  checkBlock_append h0137c00 (
    checkBlock_append h0137c01 (
    checkBlock_append h0137c02 (
    checkBlock_append h0137c03 (
    checkBlock_append h0137c04 (
    checkBlock_append h0137c05 (
    checkBlock_append h0137c06 (
    checkBlock_append h0137c07 (
    checkBlock_append h0137c08 (
    checkBlock_append h0137c09 (
    checkBlock_append h0137c10 (
    checkBlock_append h0137c11 (
    checkBlock_append h0137c12 (
    checkBlock_append h0137c13 (
    checkBlock_append h0137c14 (
    checkBlock_append h0137c15 (
    checkBlock_append h0137c16 (
    checkBlock_append h0137c17 (
    checkBlock_append h0137c18 (
    checkBlock_append h0137c19 (
    checkBlock_append h0137c20 (
    checkBlock_append h0137c21 (
    checkBlock_append h0137c22 (
    checkBlock_append h0137c23 (
    checkBlock_append h0137c24 (
    checkBlock_append h0137c25 (
    checkBlock_append h0137c26 (
    checkBlock_append h0137c27 (
    checkBlock_append h0137c28 (
    checkBlock_append h0137c29 (
    checkBlock_append h0137c30 (
    h0137c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
