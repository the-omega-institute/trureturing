/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks04/Block0343
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks04/Block0343.checked0343
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table026
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table029
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table032
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table040
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table046
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table054
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table065
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table082
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table107
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table148

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0343c00 : List Row := [
  .c 13, .c 1153, .c 3, .c 5, .p pv3 [pv2,pv3,pv173,pv2707], .c 3, .c 31, .c 11, .c 3, .c 7,
  .c 17, .c 3, .p pv2 [pv2,pv83,pv16927], .c 5, .c 3, .p pv3 [pv2,pv277,pv317], .c 7, .c 3, .c 5,
  .c 29, .c 3, .c 53, .p pv23 [pv2,pv3,pv31,pv15107], .c 3, .c 283, .c 599, .c 3, .c 17, .c 5,
  .c 3, .c 7, .c 43, .c 3, .c 5, .c 107, .c 3, .p pv2 [pv2,pv5,pv17,pv16529], .c 7, .c 3, .c 13,
  .c 11, .c 3, .c 103, .c 5, .c 3, .c 443, .c 79, .c 3, .c 5, .c 163, .c 3, .c 7, .c 13, .c 3,
  .c 19, .c 587, .c 3, .p pv2 [pv2,pv11,pv63863], .c 5, .c 3, .c 23, .c 17, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv19,pv157], .c 3, .c 149, .c 59, .c 3, .c 89, .c 271, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv197,pv1783], .p pv3 [pv2,pv3,pv5,pv7,pv13381], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv109,pv1289], .c 223, .c 3, .c 11, .p pv7 [pv2,pv3,pv13,pv18013], .c 3, .c 227,
  .c 5, .c 3, .c 37, .c 13, .c 3, .c 5, .c 67, .c 3, .p pv2 [pv2,pv5,pv43,pv1307], .c 1217, .c 3,
  .c 31, .c 7, .c 3, .c 937, .c 5, .c 3, .p pv2 [pv2,pv702517], .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv37,pv6329], .c 3, .c 19, .c 17, .c 3, .c 7, .p pv11 [pv2,pv3,pv31,pv1259],
  .c 3, .c 11, .c 5, .c 3, .c 41, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv4003], .c 3, .c 59,
  .c 37,
]
private theorem h0343c00 : checkBlock 2809859 128 b0343c00 = true := by
  decide +kernel

private def b0343c01 : List Row := [
  .c 3, .c 17, .c 13, .c 3, .c 101, .c 5, .c 3, .c 7, .c 83, .c 3, .c 5, .c 11, .c 3, .c 107,
  .c 7, .c 3, .p pv2 [pv2,pv827,pv1699], .c 103, .c 3, .p pv3 [pv2,pv351269], .c 5, .c 3, .c 11,
  .p pv53 [pv2,pv3,pv5,pv1301], .c 3, .c 5, .p pv3 [pv2,pv3,pv53,pv8837], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv234181], .c 3, .c 47, .c 43, .c 3, .c 191, .c 5, .c 3, .c 509,
  .p pv3 [pv2,pv3,pv5,pv283,pv331], .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv14051], .c 11,
  .c 3, .p pv5 [pv2,pv7,pv181,pv1109], .c 23, .c 3, .c 7, .c 5, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv5,pv7,pv6691], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv281023], .c 19, .c 3,
  .p pv3 [pv2,pv11,pv13,pv17], .c 409, .c 3, .c 31, .c 5, .c 3, .c 13, .c 71, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv127,pv461], .c 3, .c 37, .c 41, .c 3, .c 79, .c 7, .c 3, .c 193, .c 5, .c 3,
  .p pv23 [pv2,pv23,pv199,pv307], .c 73, .c 3, .c 5, .c 17, .c 3, .c 11, .c 479, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv37,pv12659], .c 3, .c 29, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5,
  .p pv29 [pv2,pv3,pv234193], .c 3, .c 17, .p pv2 [pv2,pv3,pv71,pv733], .c 3, .c 13,
  .p pv13 [pv2,pv3,pv19,pv6163], .c 3, .p pv3 [pv2,pv7,pv29,pv3461], .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv13,pv1201], .c 3, .c 5, .c 19, .c 3, .c 43, .c 7, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv156131], .c 3, .c 397, .c 5, .c 3, .p pv17 [pv2,pv11,pv499],
]
private theorem h0343c01 : checkBlock 2810115 128 b0343c01 = true := by
  decide +kernel

private def b0343c02 : List Row := [
  .p pv3 [pv2,pv3,pv5,pv23,pv4073], .c 3, .c 5, .c 787, .c 3, .c 7, .c 127, .c 3, .c 181, .c 17,
  .c 3, .c 23, .c 5, .c 3, .p pv7 [pv2,pv31,pv45329], .c 11, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv17,pv59,pv467], .c 3, .p pv2 [pv2,pv5,pv463,pv607],
  .p pv2 [pv2,pv3,pv11,pv47,pv151], .c 3, .c 739, .c 29, .c 3, .c 7, .c 5, .c 3, .c 31, .c 13,
  .c 3, .c 5, .c 7, .c 3, .c 139, .c 167, .c 3, .c 251, .c 67, .c 3, .c 61, .c 5, .c 3, .c 47,
  .c 19, .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv13,pv1663], .c 283, .c 3, .c 29, .c 7, .c 3,
  .c 13, .c 5, .c 3, .c 11, .c 17, .c 3, .c 5, .c 349, .c 3, .p pv13 [pv2,pv5,pv7,pv11,pv73],
  .p pv3 [pv2,pv3,pv156139], .c 3, .c 7, .c 13, .c 3, .p pv3 [pv2,pv269,pv653], .c 5, .c 3,
  .c 1571, .c 7, .c 3, .c 5, .c 101, .c 3, .c 23, .c 11, .c 3, .c 19, .p pv2 [pv2,pv3,pv5783],
  .c 3, .c 997, .c 5, .c 3, .c 7, .c 431, .c 3, .c 5, .c 37, .c 3, .c 13, .c 7, .c 3, .c 577,
  .c 107, .c 3, .c 73, .c 5, .c 3, .p pv2 [pv2,pv1405289], .p pv2 [pv2,pv3,pv5,pv139,pv337], .c 3,
  .c 5, .c 13, .c 3, .c 7, .c 17, .c 3, .p pv2 [pv2,pv421,pv1669], .c 11, .c 3, .c 433, .c 5,
  .c 3, .c 43, .c 359, .c 3, .c 5, .p pv5 [pv2,pv3,pv117109], .c 3, .c 11, .c 23, .c 3,
]
private theorem h0343c02 : checkBlock 2810371 128 b0343c02 = true := by
  decide +kernel

private def b0343c03 : List Row := [
  .c 17, .c 83, .c 3, .c 7, .c 5, .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv7,pv239], .c 3, .c 5, .c 7,
  .c 3, .c 19, .p pv2 [pv2,pv3,pv13,pv43,pv419], .c 3, .p pv3 [pv2,pv87833], .c 193, .c 3,
  .p pv5 [pv2,pv79,pv17789], .c 5, .c 3, .c 23, .p pv13 [pv2,pv3,pv5,pv19,pv4931], .c 3, .c 5,
  .c 31, .c 3, .c 263, .p pv5 [pv2,pv3,pv7,pv22307], .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv23,pv137,pv223], .c 5, .c 3, .p pv2 [pv2,pv11,pv251,pv509], .c 59, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv468451], .c 3, .p pv13 [pv2,pv5,pv7,pv40153], .p pv5 [pv2,pv3,pv17,pv83],
  .c 3, .c 7, .c 73, .c 3, .c 1229, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv131,pv149], .c 3, .c 47, .c 13, .c 3, .p pv2 [pv2,pv17,pv19,pv229], .c 53,
  .c 3, .c 11, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 29, .c 3, .c 157, .c 7, .c 3, .c 167,
  .c 37, .c 3, .c 107, .c 5, .c 3, .c 1319, .c 863, .c 3, .c 5, .c 11, .c 3, .c 7, .c 19, .c 3,
  .c 23, .c 257, .c 3, .c 1021, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv156157],
  .c 3, .c 17, .p pv5 [pv2,pv3,pv31,pv1889], .c 3, .c 41, .c 317, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv17,pv5167], .c 67, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv13,pv19,pv569],
  .c 11, .c 3, .c 43, .c 1123, .c 3, .c 13, .c 5, .c 3, .c 19, .p pv7 [pv2,pv3,pv5,pv61],
]
private theorem h0343c03 : checkBlock 2810627 128 b0343c03 = true := by
  decide +kernel

private def b0343c04 : List Row := [
  .c 3, .c 5, .c 89, .c 3, .c 127, .p pv2 [pv2,pv3,pv7,pv109,pv307], .c 3,
  .p pv3 [pv2,pv11,pv15971], .c 7, .c 3, .c 887, .c 5, .c 3, .p pv2 [pv2,pv53,pv13259],
  .p pv17 [pv2,pv3,pv5,pv43,pv2179], .c 3, .c 5, .c 19, .c 3, .p pv3 [pv2,pv5,pv7,pv10039],
  .c 1609, .c 3, .c 7, .c 11, .c 3, .c 17, .c 5, .c 3, .c 353, .c 7, .c 3, .c 5, .c 191, .c 3,
  .c 11, .c 43, .c 3, .p pv2 [pv2,pv31,pv22669], .p pv7 [pv2,pv3,pv468493], .c 3, .c 97, .c 5,
  .c 3, .c 7, .c 1163, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv140549], .c 7, .c 3, .c 31,
  .p pv2 [pv2,pv3,pv113,pv691], .c 3, .c 19, .c 5, .c 3, .c 29, .c 17, .c 3, .c 5, .c 457, .c 3,
  .c 7, .p pv5 [pv2,pv3,pv19,pv12329], .c 3, .c 11, .c 797, .c 3, .c 47, .c 5, .c 3, .c 13, .c 19,
  .c 3, .c 5, .c 23, .c 3, .p pv3 [pv2,pv5,pv17569], .c 379, .c 3, .c 347, .c 31, .c 3, .c 7,
  .c 5, .c 3, .c 563, .c 11, .c 3, .c 5, .c 7, .c 3, .c 419, .p pv5 [pv2,pv3,pv11], .c 3, .c 173,
  .p pv13 [pv2,pv3,pv52057], .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv7,pv19,pv1321],
  .p pv3 [pv2,pv3,pv5,pv93703], .c 3, .c 5, .p pv5 [pv2,pv3,pv39043], .c 3, .c 113, .c 17, .c 3,
  .c 13, .c 7, .c 3, .p pv3 [pv2,pv37,pv9497], .c 5, .c 3, .c 67, .c 673, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv7,pv5737], .c 13, .c 3, .c 7,
]
private theorem h0343c04 : checkBlock 2810883 128 b0343c04 = true := by
  decide +kernel

private def b0343c05 : List Row := [
  .c 829, .c 3, .c 587, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 73, .c 3,
  .p pv3 [pv2,pv5,pv11,pv6389], .p pv5 [pv2,pv3,pv468527], .c 3, .c 151,
  .p pv23 [pv2,pv3,pv43,pv227], .c 3, .c 29, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv46853], .c 3,
  .c 5, .p pv3 [pv2,pv3,pv7,pv37,pv67], .c 3, .p pv11 [pv2,pv5,pv197,pv1427], .c 7, .c 3,
  .p pv2 [pv2,pv643,pv1093], .c 307, .c 3, .p pv2 [pv2,pv19,pv29,pv2551], .c 5, .c 3,
  .p pv3 [pv2,pv351401], .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv58567], .c 3, .c 7, .c 37, .c 3,
  .p pv2 [pv2,pv11,pv53,pv2411], .p pv17 [pv2,pv3,pv7,pv683], .c 3, .c 661, .c 5, .c 3, .c 17,
  .p pv43 [pv2,pv3,pv5,pv19,pv137], .c 3, .c 5, .c 41, .c 3, .c 479, .c 67, .c 3,
  .p pv3 [pv2,pv7,pv17,pv2953], .c 11, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv702817], .c 881,
  .c 3, .c 5, .c 7, .c 3, .c 11, .p pv3 [pv2,pv3,pv103,pv4549], .c 3, .p pv5 [pv2,pv1405643],
  .c 13, .c 3, .c 83, .c 5, .c 3, .p pv2 [pv2,pv7,pv200807], .c 373, .c 3, .c 5, .c 17, .c 3,
  .p pv31 [pv2,pv5,pv281131], .c 23, .c 3, .p pv3 [pv2,pv19,pv71,pv521], .c 7, .c 3, .c 257, .c 5,
  .c 3, .c 41, .p pv2 [pv2,pv3,pv5,pv31237], .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv23,pv463], .c 3,
  .c 13, .p pv3 [pv2,pv3,pv468557], .c 3, .c 7, .p pv13 [pv2,pv3,pv8677], .c 3,
  .p pv3 [pv2,pv47,pv7477], .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 13, .c 3, .c 37, .c 19, .c 3,
  .c 137, .p pv2 [pv2,pv3,pv233,pv2011], .c 3, .c 43, .c 5, .c 3, .c 7, .c 11, .c 3,
]
private theorem h0343c05 : checkBlock 2811139 128 b0343c05 = true := by
  decide +kernel

private def b0343c06 : List Row := [
  .c 5, .p pv5 [pv2,pv3,pv7,pv33469], .c 3, .c 773, .c 7, .c 3, .p pv5 [pv2,pv13,pv108131], .c 17,
  .c 3, .c 11, .c 5, .c 3, .c 13, .c 31, .c 3, .c 5, .p pv3 [pv2,pv3,pv17,pv43,pv641], .c 3, .c 7,
  .c 229, .c 3, .c 109, .p pv7 [pv2,pv3,pv7,pv53,pv421], .c 3, .c 17, .c 5, .c 3, .c 19, .c 23,
  .c 3, .c 5, .c 11, .c 3, .c 1301, .c 29, .c 3, .c 991, .c 43, .c 3, .c 7, .c 5, .c 3, .c 11,
  .c 149, .c 3, .c 5, .c 7, .c 3, .c 53, .c 41, .c 3, .c 13, .c 1249, .c 3,
  .p pv5 [pv2,pv1405751], .c 5, .c 3, .p pv2 [pv2,pv7,pv100411], .c 17, .c 3, .c 5,
  .p pv17 [pv2,pv3,pv234293], .c 3, .c 29, .c 11, .c 3, .c 59, .c 7, .c 3,
  .p pv2 [pv2,pv107,pv6569], .c 5, .c 3, .p pv2 [pv2,pv1405769], .c 1201, .c 3, .c 5, .c 1103,
  .c 3, .c 61, .c 113, .c 3, .c 7, .p pv3 [pv2,pv3,pv468593], .c 3, .c 19, .c 5, .c 3,
  .p pv3 [pv2,pv175723], .c 7, .c 3, .c 5, .c 541, .c 3, .c 677, .p pv3 [pv2,pv3,pv19,pv8221],
  .c 3, .c 47, .c 11, .c 3, .c 37, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 31, .c 3, .c 11, .c 7,
  .c 3, .p pv3 [pv2,pv41,pv2143], .p pv2 [pv2,pv3,pv52067], .c 3, .p pv5 [pv2,pv11,pv227,pv563],
  .c 5, .c 3, .p pv2 [pv2,pv293,pv2399], .p pv3 [pv2,pv3,pv5,pv17,pv37,pv149], .c 3, .c 5, .c 29,
  .c 3, .c 7, .c 947, .c 3, .c 17, .p pv19 [pv2,pv3,pv7,pv523],
]
private theorem h0343c06 : checkBlock 2811395 128 b0343c06 = true := by
  decide +kernel

private def b0343c07 : List Row := [
  .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv19,pv23,pv3217], .p pv7 [pv2,pv3,pv5,pv46861], .c 3,
  .c 5, .c 37, .c 3, .c 71, .c 61, .c 3, .c 11, .c 13, .c 3, .c 7, .c 5, .c 3, .c 79,
  .p pv7 [pv2,pv3,pv5,pv7,pv4463], .c 3, .c 5, .c 7, .c 3, .c 1237, .c 53, .c 3,
  .p pv2 [pv2,pv599,pv2347], .p pv2 [pv2,pv3,pv83,pv941], .c 3, .c 157, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv13,pv2207], .c 11, .c 3, .c 5, .c 23, .c 3, .c 13, .c 263, .c 3, .c 811, .c 7,
  .c 3, .c 11, .c 5, .c 3, .c 17, .c 311, .c 3, .c 5, .c 13, .c 3, .p pv17 [pv2,pv5,pv7,pv5021],
  .c 59, .c 3, .c 7, .c 173, .c 3, .c 23, .c 5, .c 3, .c 113, .c 7, .c 3, .c 5, .c 11, .c 3,
  .c 19, .c 31, .c 3, .c 103, .c 463, .c 3, .p pv2 [pv2,pv7,pv200843], .c 5, .c 3, .c 7, .c 29,
  .c 3, .c 5, .c 17, .c 3, .c 41, .c 7, .c 3, .c 277, .c 19, .c 3, .p pv3 [pv2,pv351479], .c 5,
  .c 3, .c 643, .p pv11 [pv2,pv3,pv5,pv29,pv101], .c 3, .c 5, .c 79, .c 3, .c 7, .c 11, .c 3,
  .c 269, .c 421, .c 3, .p pv5 [pv2,pv41,pv53,pv647], .c 5, .c 3, .c 29,
  .p pv17 [pv2,pv3,pv5,pv157,pv199], .c 3, .c 5, .p pv2 [pv2,pv3,pv234323], .c 3, .c 59,
  .p pv2 [pv2,pv3,pv468647], .c 3, .c 13, .c 37, .c 3, .c 7, .c 5, .c 3, .c 43, .c 1193, .c 3,
  .c 5,
]
private theorem h0343c07 : checkBlock 2811651 128 b0343c07 = true := by
  decide +kernel

private def b0343c08 : List Row := [
  .c 7, .c 3, .c 23, .c 13, .c 3, .c 31, .c 11, .c 3, .c 67, .c 5, .c 3, .c 1657,
  .p pv2 [pv2,pv3,pv5,pv11,pv8521], .c 3, .c 5, .c 937, .c 3, .c 11, .c 19, .c 3,
  .p pv2 [pv2,pv167,pv8419], .c 7, .c 3, .c 17, .c 5, .c 3, .p pv13 [pv2,pv1405979], .c 1181,
  .c 3, .c 5, .c 281, .c 3, .c 1511, .p pv2 [pv2,pv3,pv234331], .c 3, .c 7, .c 31, .c 3,
  .p pv5 [pv2,pv109,pv12899], .c 5, .c 3, .p pv2 [pv2,pv241,pv2917], .c 7, .c 3, .c 5, .c 211,
  .c 3, .p pv3 [pv2,pv5,pv19,pv37], .c 23, .c 3, .c 11, .c 719, .c 3, .p pv2 [pv2,pv7,pv14347],
  .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 157, .c 3, .p pv29 [pv2,pv5,pv13,pv97,pv223], .c 7,
  .c 3, .c 37, .c 61, .c 3, .c 13, .c 5, .c 3, .c 23, .c 11, .c 3, .c 5, .c 19, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv11,pv137,pv311], .c 3, .c 41, .c 13, .c 3, .c 11, .c 5, .c 3, .c 601, .c 389,
  .c 3, .c 5, .c 449, .c 3, .c 109, .c 191, .c 3, .c 71, .p pv2 [pv2,pv3,pv468683], .c 3, .c 7,
  .c 5, .c 3, .c 139, .c 37, .c 3, .c 5, .c 7, .c 3, .c 13, .c 17, .c 3, .c 53,
  .p pv13 [pv2,pv3,pv11,pv2663], .c 3, .c 19, .c 5, .c 3, .c 11, .c 23, .c 3, .c 5, .c 13, .c 3,
  .c 47, .p pv13 [pv2,pv3,pv7,pv19,pv881], .c 3, .c 17, .c 7, .c 3,
]
private theorem h0343c08 : checkBlock 2811907 128 b0343c08 = true := by
  decide +kernel

private def b0343c09 : List Row := [
  .c 79, .c 5, .c 3, .p pv3 [pv2,pv71,pv4951], .c 19, .c 3, .c 5, .c 131, .c 3,
  .p pv2 [pv2,pv5,pv7,pv53,pv379], .c 11, .c 3, .c 7, .p pv11 [pv2,pv3,pv29,pv8081], .c 3,
  .p pv3 [pv2,pv87881], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv83,pv5647], .c 3,
  .p pv2 [pv2,pv5,pv23,pv12227], .c 401, .c 3, .c 29, .p pv2 [pv2,pv3,pv468703], .c 3,
  .p pv5 [pv2,pv7,pv37,pv61,pv89], .c 5, .c 3, .c 7, .c 41, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv33479], .c 3, .p pv3 [pv2,pv5,pv35153], .c 7, .c 3, .c 19, .c 11, .c 3,
  .c 223, .c 5, .c 3, .c 17, .p pv31 [pv2,pv3,pv5,pv11,pv4261], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv19,pv2741], .c 3, .c 7, .c 503, .c 3, .c 13, .c 23, .c 3, .c 61, .c 5, .c 3,
  .c 31, .p pv3 [pv2,pv3,pv5,pv13,pv7211], .c 3, .c 5, .p pv5 [pv2,pv3,pv37,pv3167], .c 3,
  .p pv2 [pv2,pv5,pv28123], .c 13, .c 3, .p pv5 [pv2,pv7,pv28697], .c 109, .c 3, .c 7, .c 5, .c 3,
  .p pv11 [pv2,pv1406159], .c 79, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv281233], .c 29, .c 3,
  .c 11, .c 47, .c 3, .p pv5 [pv2,pv13,pv19,pv5693], .c 5, .c 3, .c 229, .c 31, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv78121], .c 3, .c 17, .c 983, .c 3, .c 631, .c 7, .c 3, .c 311, .c 5, .c 3,
  .p pv2 [pv2,pv17,pv181,pv457], .c 11, .c 3, .c 5, .c 139, .c 3, .c 29,
  .p pv5 [pv2,pv3,pv11,pv53,pv67], .c 3, .c 7, .c 19, .c 3, .c 11, .c 5, .c 3, .c 1321, .c 7,
  .c 3, .c 5, .c 23,
]
private theorem h0343c09 : checkBlock 2812163 128 b0343c09 = true := by
  decide +kernel

private def b0343c10 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv13,pv29,pv373], .p pv5 [pv2,pv3,pv468737], .c 3, .c 307, .c 17, .c 3,
  .c 13, .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv23,pv1019], .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv56249], .c 7, .c 3, .c 113, .c 13, .c 3, .c 17, .c 5, .c 3, .c 11, .c 59,
  .c 3, .c 5, .c 41, .c 3, .c 7, .c 1553, .c 3, .c 1217, .c 89, .c 3, .p pv2 [pv2,pv703123], .c 5,
  .c 3, .p pv2 [pv2,pv13,pv53,pv157], .c 43, .c 3, .c 5, .c 29, .c 3, .c 13, .c 11, .c 3, .c 863,
  .p pv3 [pv2,pv3,pv37,pv41,pv103], .c 3, .c 7, .c 5, .c 3, .c 281, .c 17, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv140627], .c 233, .c 3, .c 101, .p pv2 [pv2,pv3,pv17,pv811], .c 3,
  .p pv3 [pv2,pv239,pv1471], .c 5, .c 3, .c 41, .c 461, .c 3, .c 5, .c 569, .c 3,
  .p pv2 [pv2,pv5,pv19,pv113,pv131], .c 1039, .c 3, .p pv5 [pv2,pv13,pv6761], .c 7, .c 3,
  .p pv5 [pv2,pv17,pv82723], .c 5, .c 3, .c 13, .c 349, .c 3, .c 5, .p pv2 [pv2,pv3,pv234383],
  .c 3, .c 11, .c 709, .c 3, .c 7, .p pv13 [pv2,pv3,pv19,pv257], .c 3, .c 797, .c 5, .c 3,
  .p pv2 [pv2,pv313,pv4493], .c 7, .c 3, .c 5, .c 19, .c 3, .p pv19 [pv2,pv5,pv31,pv43,pv211],
  .c 17, .c 3, .c 79, .p pv3 [pv2,pv3,pv468773], .c 3, .p pv7 [pv2,pv7,pv200903], .c 5, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv5,pv17,pv1103], .c 3, .c 5, .c 53, .c 3, .c 31, .c 7, .c 3, .c 11,
  .c 127, .c 3, .c 43,
]
private theorem h0343c10 : checkBlock 2812419 128 b0343c10 = true := by
  decide +kernel

private def b0343c11 : List Row := [
  .c 5, .c 3, .p pv11 [pv2,pv11,pv127849], .c 29, .c 3, .c 5, .p pv3 [pv2,pv3,pv468781], .c 3,
  .c 7, .c 13, .c 3, .p pv3 [pv2,pv351587], .c 223, .c 3, .c 19, .c 5, .c 3, .c 97, .c 11, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv23,pv43,pv79], .c 3, .c 1489, .c 31, .c 3, .c 67,
  .p pv7 [pv2,pv3,pv163,pv719], .c 3, .c 7, .c 5, .c 3, .c 23, .c 19, .c 3, .c 5, .c 7, .c 3,
  .p pv13 [pv2,pv5,pv11251], .p pv7 [pv2,pv3,pv17,pv383], .c 3, .c 227, .c 43, .c 3, .c 53, .c 5,
  .c 3, .c 17, .c 13, .c 3, .c 5, .c 11, .c 3, .c 167, .c 977, .c 3, .c 83, .c 7, .c 3, .c 373,
  .c 5, .c 3, .c 11, .p pv11 [pv2,pv3,pv5,pv293], .c 3, .c 5, .c 71, .c 3,
  .p pv29 [pv2,pv5,pv7,pv11,pv13,pv281], .p pv2 [pv2,pv3,pv157,pv1493], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv468803], .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv151,pv4657], .c 7, .c 3, .c 5,
  .c 17, .c 3, .c 211, .c 11, .c 3, .c 31, .c 13, .c 3, .p pv2 [pv2,pv7,pv100459], .c 5, .c 3,
  .c 7, .c 67, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv66973], .c 3, .c 17, .c 7, .c 3, .c 23, .c 521,
  .c 3, .p pv2 [pv2,pv1406441], .c 5, .c 3, .c 1543, .c 163, .c 3, .c 5, .p pv5 [pv2,pv3,pv9767],
  .c 3, .c 7, .c 47, .c 3, .p pv2 [pv2,pv1406453], .c 11, .c 3, .c 29, .c 5, .c 3,
  .p pv7 [pv2,pv1406459], .c 181, .c 3, .c 5, .c 13, .c 3,
]
private theorem h0343c11 : checkBlock 2812675 128 b0343c11 = true := by
  decide +kernel

private def b0343c12 : List Row := [
  .c 11, .c 269, .c 3, .p pv3 [pv2,pv7,pv50231], .c 17, .c 3, .c 7, .c 5, .c 3, .c 71, .c 101,
  .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv17581], .c 109, .c 3, .p pv5 [pv2,pv13,pv108191],
  .c 19, .c 3, .c 17, .c 5, .c 3, .c 13, .c 1523, .c 3, .c 5, .c 971, .c 3, .c 1583,
  .p pv17 [pv2,pv3,pv7,pv13,pv23], .c 3, .c 11, .c 7, .c 3, .c 967, .c 5, .c 3, .c 233,
  .p pv3 [pv2,pv3,pv5,pv41,pv2287], .c 3, .c 5, .c 43, .c 3, .c 137, .c 89, .c 3, .c 7, .c 29,
  .c 3, .c 31, .c 5, .c 3, .p pv11 [pv2,pv23,pv61153], .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv468841], .c 3, .c 41, .p pv2 [pv2,pv3,pv11,pv101,pv211], .c 3, .c 13, .c 919,
  .c 3, .c 11, .c 5, .c 3, .c 7, .p pv31 [pv2,pv3,pv5,pv13,pv7213], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv61], .c 3, .c 53, .c 7, .c 3, .c 29, .c 1291, .c 3, .c 293, .c 5, .c 3,
  .p pv2 [pv2,pv1406549], .c 1013, .c 3, .c 5, .c 11, .c 3, .c 7, .c 701, .c 3,
  .p pv2 [pv2,pv29,pv24251], .c 83, .c 3, .p pv2 [pv2,pv13,pv257,pv421], .c 5, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv5,pv23,pv151], .c 3, .c 5, .c 61, .c 3, .p pv2 [pv2,pv5,pv11,pv19,pv673],
  .c 17, .c 3, .c 37, .p pv7 [pv2,pv3,pv13,pv6011], .c 3, .c 7, .c 5, .c 3, .c 19, .c 13, .c 3,
  .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv281317], .c 11, .c 3, .c 17, .c 59, .c 3,
  .p pv5 [pv2,pv1406591], .c 5,
]
private theorem h0343c12 : checkBlock 2812931 128 b0343c12 = true := by
  decide +kernel

private def b0343c13 : List Row := [
  .c 3, .c 43, .p pv3 [pv2,pv3,pv5,pv79,pv1187], .c 3, .c 5, .c 19, .c 3, .c 73, .c 29, .c 3,
  .p pv5 [pv2,pv11,pv127873], .c 7, .c 3, .c 13, .c 5, .c 3, .c 31, .c 37, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv13,pv36067], .c 3, .c 1277, .c 71, .c 3, .c 7, .c 11, .c 3, .c 509, .c 5,
  .c 3, .p pv3 [pv2,pv113,pv389], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv41,pv953], .c 3, .c 11,
  .c 67, .c 3, .p pv2 [pv2,pv1406633], .c 79, .c 3, .c 19, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv7,pv1367], .c 3, .c 13, .c 7, .c 3, .c 41, .p pv2 [pv2,pv3,pv468883], .c 3,
  .c 283, .c 5, .c 3, .p pv2 [pv2,pv703327], .c 19, .c 3, .c 5, .c 13, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv468887], .c 3, .c 11, .p pv11 [pv2,pv3,pv7,pv2791], .c 3,
  .p pv2 [pv2,pv37,pv19009], .c 5, .c 3, .p pv2 [pv2,pv11,pv41,pv3119],
  .p pv2 [pv2,pv3,pv5,pv46889], .c 3, .c 5, .c 17, .c 3, .c 107, .p pv17 [pv2,pv3,pv117223], .c 3,
  .c 197, .c 811, .c 3, .c 7, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 7, .c 3, .c 17, .c 23,
  .c 3, .c 19, .c 1399, .c 3, .c 11, .c 5, .c 3, .c 53, .p pv11 [pv2,pv3,pv5,pv521], .c 3, .c 5,
  .c 557, .c 3, .p pv2 [pv2,pv5,pv353,pv797], .p pv5 [pv2,pv3,pv7,pv33493], .c 3, .c 761, .c 7,
  .c 3, .p pv5 [pv2,pv367,pv3833], .c 5, .c 3, .c 23, .c 127, .c 3, .c 5, .c 11, .c 3,
  .p pv3 [pv2,pv5,pv7,pv157],
]
private theorem h0343c13 : checkBlock 2813187 128 b0343c13 = true := by
  decide +kernel

private def b0343c14 : List Row := [
  .c 37, .c 3, .c 7, .c 17, .c 3, .p pv2 [pv2,pv23,pv53,pv577], .c 5, .c 3, .c 11, .c 7, .c 3,
  .c 5, .c 31, .c 3, .c 269, .c 13, .c 3, .p pv2 [pv2,pv347,pv2027], .p pv3 [pv2,pv3,pv468913],
  .c 3, .c 17, .c 5, .c 3, .c 7, .c 587, .c 3, .c 5, .p pv13 [pv2,pv3,pv7,pv16747], .c 3, .c 19,
  .c 7, .c 3, .p pv2 [pv2,pv79,pv17807], .p pv2 [pv2,pv3,pv109,pv239], .c 3,
  .p pv5 [pv2,pv13,pv2081], .c 5, .c 3, .p pv7 [pv2,pv383,pv3673], .c 23, .c 3, .c 5, .c 1051,
  .c 3, .c 7, .c 43, .c 3, .c 947, .c 19, .c 3, .c 41, .c 5, .c 3, .p pv2 [pv2,pv103,pv6829],
  .c 13, .c 3, .c 5, .c 89, .c 3, .c 47, .p pv2 [pv2,pv3,pv52103], .c 3, .c 23, .c 11, .c 3, .c 7,
  .c 5, .c 3, .p pv2 [pv2,pv1406789], .p pv2 [pv2,pv3,pv5,pv7,pv11,pv29], .c 3, .c 5, .c 7, .c 3,
  .c 11, .p pv5 [pv2,pv3,pv59,pv1987], .c 3, .c 157, .c 1031, .c 3, .c 13, .c 5, .c 3, .c 29,
  .c 53, .c 3, .c 5, .c 83, .c 3, .c 191, .c 1499, .c 3, .p pv2 [pv2,pv829,pv1697], .c 7, .c 3,
  .p pv3 [pv2,pv43963], .c 5, .c 3, .c 73, .p pv7 [pv2,pv3,pv5,pv23447], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv89,pv479], .c 3, .c 59, .c 17, .c 3, .c 7, .c 23, .c 3,
  .p pv5 [pv2,pv43,pv32717], .c 5, .c 3, .p pv3 [pv2,pv11,pv13,pv4919], .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv234473], .c 3, .c 13, .p pv2 [pv2,pv3,pv23,pv20389], .c 3, .c 17, .c 1091,
  .c 3, .p pv2 [pv2,pv7,pv317], .c 5, .c 3,
]
private theorem h0343c14 : checkBlock 2813443 128 b0343c14 = true := by
  decide +kernel

private def b0343c15 : List Row := [
  .c 7, .c 11, .c 3, .c 5, .c 13, .c 3, .p pv19 [pv2,pv5,pv19,pv59,pv251], .c 7, .c 3, .c 53,
  .p pv31 [pv2,pv3,pv468953], .c 3, .c 11, .c 5, .c 3, .c 19, .p pv2 [pv2,pv3,pv5,pv71,pv1321],
  .c 3, .c 5, .p pv5 [pv2,pv3,pv117239], .c 3, .c 7, .c 79, .c 3, .c 61, .c 47, .c 3, .c 1103,
  .c 5, .c 3, .c 13, .c 1063, .c 3, .c 5, .c 11, .c 3, .c 769, .c 1409, .c 3, .c 31, .c 107, .c 3,
  .c 7, .c 5, .c 3, .c 11, .c 43, .c 3, .c 5, .c 7, .c 3, .c 71, .c 647, .c 3,
  .p pv5 [pv2,pv17,pv82759], .p pv7 [pv2,pv3,pv31,pv61], .c 3, .c 37, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv200987], .p pv7 [pv2,pv3,pv5,pv23,pv2039], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv181,pv2591], .c 3, .c 331, .c 11, .c 3, .c 13, .c 7, .c 3, .c 19, .c 5, .c 3,
  .p pv3 [pv2,pv351731], .p pv2 [pv2,pv3,pv5,pv13,pv37], .c 3, .c 5, .c 17, .c 3, .c 499, .c 13,
  .c 3, .c 7, .c 61, .c 3, .c 97, .c 5, .c 3, .p pv17 [pv2,pv1406939], .c 7, .c 3, .c 5, .c 37,
  .c 3, .c 17, .c 257, .c 3, .p pv3 [pv2,pv211,pv1667], .c 11, .c 3,
  .p pv5 [pv2,pv7,pv13,pv15461], .c 5, .c 3, .c 7, .c 157, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv139,pv241], .c 3, .c 11, .c 7, .c 3, .p pv5 [pv2,pv113,pv12451], .c 53,
  .c 3, .c 67, .c 5, .c 3, .c 127, .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv59,pv7949], .c 3, .c 7,
  .c 41,
]
private theorem h0343c15 : checkBlock 2813699 128 b0343c15 = true := by
  decide +kernel

private def b0343c16 : List Row := [
  .c 3, .c 19, .c 17, .c 3, .c 31, .c 5, .c 3, .p pv3 [pv2,pv175873], .c 1307, .c 3, .c 5,
  .p pv23 [pv2,pv3,pv11,pv17,pv19], .c 3, .c 23, .p pv3 [pv2,pv3,pv53,pv8849], .c 3, .c 11,
  .p pv7 [pv2,pv3,pv234499], .c 3, .c 7, .c 5, .c 3, .c 431, .p pv23 [pv2,pv3,pv5,pv7,pv67], .c 3,
  .c 5, .c 7, .c 3, .c 131, .p pv2 [pv2,pv3,pv78167], .c 3, .p pv3 [pv2,pv43969], .c 13, .c 3,
  .c 1471, .c 5, .c 3, .c 577, .c 11, .c 3, .c 5, .c 223, .c 3, .p pv7 [pv2,pv5,pv70351], .c 277,
  .c 3, .c 853, .c 7, .c 3, .c 11, .c 5, .c 3, .c 79, .c 17, .c 3, .c 5, .c 67, .c 3, .c 13,
  .c 23, .c 3, .c 7, .c 911, .c 3, .p pv2 [pv2,pv1407041], .c 5, .c 3, .p pv3 [pv2,pv53,pv6637],
  .c 7, .c 3, .c 5, .c 11, .c 3, .c 1009, .p pv31 [pv2,pv3,pv29,pv599], .c 3, .c 211, .c 19, .c 3,
  .c 61, .c 5, .c 3, .c 7, .c 883, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv67003], .c 3, .c 29, .c 7,
  .c 3, .c 617, .p pv3 [pv2,pv3,pv79,pv1979], .c 3, .p pv5 [pv2,pv23,pv131,pv467], .c 5, .c 3,
  .c 13, .p pv3 [pv2,pv3,pv5,pv73,pv257], .c 3, .c 5, .c 241, .c 3, .c 7, .c 11, .c 3,
  .p pv5 [pv2,pv19,pv103,pv719], .p pv11 [pv2,pv3,pv7,pv2393], .c 3, .p pv2 [pv2,pv47,pv14969],
  .c 5, .c 3, .p pv2 [pv2,pv43,pv761], .c 229, .c 3, .c 5, .c 151, .c 3, .c 173, .c 127, .c 3,
  .c 17, .c 41, .c 3, .c 7, .c 5, .c 3, .c 953,
]
private theorem h0343c16 : checkBlock 2813955 128 b0343c16 = true := by
  decide +kernel

private def b0343c17 : List Row := [
  .c 23, .c 3, .c 5, .c 7, .c 3, .c 43, .c 19, .c 3, .c 13, .c 11, .c 3, .p pv3 [pv2,pv351779],
  .c 5, .c 3, .c 311, .c 59, .c 3, .c 5, .c 29, .c 3, .c 11, .c 13, .c 3, .c 23, .c 7, .c 3,
  .c 523, .c 5, .c 3, .c 89, .c 109, .c 3, .c 5, .p pv5 [pv2,pv3,pv29,pv8087], .c 3, .c 41,
  .c 613, .c 3, .c 7, .c 677, .c 3, .c 877, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 43, .c 3,
  .p pv13 [pv2,pv5,pv281431], .c 47, .c 3, .c 11, .p pv29 [pv2,pv3,pv13,pv19,pv211], .c 3,
  .c 1181, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv140717], .c 7,
  .c 3, .p pv2 [pv2,pv227,pv6199], .c 23, .c 3, .c 53, .c 5, .c 3, .c 59, .c 11, .c 3, .c 5,
  .c 17, .c 3, .c 7, .c 487, .c 3, .c 1187, .c 443, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv821,pv857], .c 137, .c 3, .c 5, .c 31, .c 3, .c 17, .p pv2 [pv2,pv3,pv67,pv7001],
  .c 3, .c 47, .c 13, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv17,pv23,pv59,pv61], .c 29, .c 3, .c 5,
  .c 7, .c 3, .p pv7 [pv2,pv5,pv431,pv653], .p pv5 [pv2,pv3,pv19,pv1543], .c 3, .c 563,
  .p pv19 [pv2,pv3,pv11,pv42643], .c 3, .c 691, .c 5, .c 3, .c 11, .c 19, .c 3, .c 5, .c 199,
  .c 3, .c 13, .c 251, .c 3,
]
private theorem h0343c17 : checkBlock 2814211 128 b0343c17 = true := by
  decide +kernel

private def b0343c18 : List Row := [
  .c 1049, .c 7, .c 3, .c 1153, .c 5, .c 3, .c 29, .p pv11 [pv2,pv3,pv5,pv1303], .c 3, .c 5,
  .c 13, .c 3, .c 113, .c 11, .c 3, .c 7, .p pv37 [pv2,pv3,pv156361], .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv19,pv29,pv1277], .c 7, .c 3, .c 5, .c 347, .c 3, .c 31, .c 367, .c 3, .c 19,
  .c 211, .c 3, .c 23, .c 5, .c 3, .c 7, .p pv41 [pv2,pv3,pv5,pv61,pv769], .c 3, .c 5, .c 269,
  .c 3, .p pv11 [pv2,pv5,pv181,pv311], .c 7, .c 3, .p pv2 [pv2,pv23,pv30593], .c 11, .c 3,
  .p pv2 [pv2,pv1407281], .c 5, .c 3, .p pv3 [pv2,pv41,pv8581], .c 17, .c 3, .c 5, .c 463, .c 3,
  .c 7, .c 31, .c 3, .p pv2 [pv2,pv1407293], .c 659, .c 3, .c 619, .c 5, .c 3,
  .p pv7 [pv2,pv109,pv12911], .c 61, .c 3, .c 5, .p pv5 [pv2,pv3,pv271,pv577], .c 3, .c 139,
  .c 83, .c 3, .c 13, .c 401, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv703657], .c 641, .c 3, .c 5,
  .c 7, .c 3, .c 19, .c 13, .c 3, .c 11, .c 97, .c 3, .c 29, .c 5, .c 3, .c 607, .c 73, .c 3,
  .c 5, .c 383, .c 3, .c 23, .c 17, .c 3, .c 1069, .c 7, .c 3, .p pv2 [pv2,pv13,pv29,pv3733],
  .c 5, .c 3, .c 47, .c 11, .c 3, .c 5, .p pv17 [pv2,pv3,pv83,pv157], .c 3, .c 37, .c 239, .c 3,
  .c 7, .p pv23 [pv2,pv3,pv13,pv18043], .c 3, .c 11, .c 5, .c 3, .p pv13 [pv2,pv283,pv4973], .c 7,
]
private theorem h0343c18 : checkBlock 2814467 128 b0343c18 = true := by
  decide +kernel

private def b0343c19 : List Row := [
  .c 3, .c 5, .p pv3 [pv2,pv3,pv469121], .c 3, .c 181, .p pv5 [pv2,pv3,pv41,pv1907], .c 3, .c 43,
  .p pv2 [pv2,pv3,pv31,pv37,pv409], .c 3, .p pv5 [pv2,pv7,pv107,pv1879], .c 5, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv5,pv139], .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv13,pv5413], .c 7, .c 3,
  .c 191, .c 29, .c 3, .c 13, .c 5, .c 3, .c 11, .c 449, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv13,pv23,pv523], .c 3, .c 7, .c 19, .c 3, .c 131, .c 13, .c 3, .c 89, .c 5,
  .c 3, .c 17, .p pv41 [pv2,pv3,pv5,pv93827], .c 3, .c 5, .p pv7 [pv2,pv3,pv109,pv269], .c 3,
  .p pv3 [pv2,pv5,pv140741], .c 11, .c 3, .c 29, .p pv2 [pv2,pv3,pv127,pv1847], .c 3, .c 7, .c 5,
  .c 3, .p pv11 [pv2,pv13,pv108263], .p pv11 [pv2,pv3,pv5,pv7,pv1117], .c 3, .c 5, .c 7, .c 3,
  .c 13, .c 157, .c 3, .p pv3 [pv2,pv11,pv29,pv1103], .c 499, .c 3, .p pv5 [pv2,pv31,pv83,pv547],
  .c 5, .c 3, .c 19, .c 67, .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv73,pv241], .c 53, .c 3,
  .c 103, .c 7, .c 3, .c 31, .c 5, .c 3, .p pv2 [pv2,pv1407449], .c 23, .c 3, .c 5, .c 19, .c 3,
  .c 11, .p pv7 [pv2,pv3,pv181], .c 3, .c 7, .c 359, .c 3, .c 37, .c 5, .c 3, .c 13, .c 7, .c 3,
  .c 5, .c 41, .c 3, .p pv2 [pv2,pv5,pv97,pv1451], .c 29, .c 3, .c 23, .c 59, .c 3, .c 73, .c 5,
  .c 3, .c 7, .c 337, .c 3, .c 5, .c 61, .c 3, .c 47, .c 7, .c 3, .c 11,
]
private theorem h0343c19 : checkBlock 2814723 128 b0343c19 = true := by
  decide +kernel

private def b0343c20 : List Row := [
  .c 17, .c 3, .c 19, .c 5, .c 3, .c 53, .p pv11 [pv2,pv3,pv5,pv103,pv911], .c 3, .c 5, .c 37,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv19,pv8231], .c 3, .c 13, .p pv13 [pv2,pv3,pv7,pv59,pv71], .c 3,
  .c 17, .c 5, .c 3, .c 41, .c 11, .c 3, .c 5, .c 227, .c 3, .c 373, .c 13, .c 3, .c 97, .c 23,
  .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv31,pv11351], .c 1321, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv41,pv3433], .c 107, .c 3, .c 59, .p pv2 [pv2,pv3,pv234589], .c 3,
  .p pv3 [pv2,pv13,pv67,pv101], .c 5, .c 3, .c 31, .c 17, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv281509], .c 103, .c 3, .c 19, .c 7, .c 3, .p pv5 [pv2,pv1407551], .c 5, .c 3,
  .c 11, .c 13, .c 3, .c 5, .c 29, .c 3, .c 241, .p pv3 [pv2,pv3,pv313,pv1499], .c 3, .c 7,
  .p pv23 [pv2,pv3,pv13033], .c 3, .c 179, .c 5, .c 3, .c 67, .c 7, .c 3, .c 5, .c 409, .c 3,
  .c 277, .c 11, .c 3, .p pv2 [pv2,pv703789], .c 47, .c 3, .c 13, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv107,pv877], .c 3, .c 5, .c 23, .c 3, .c 239, .c 7, .c 3,
  .p pv2 [pv2,pv11,pv11633], .c 13, .c 3, .c 389, .c 5, .c 3, .c 661, .c 53, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv47,pv67,pv149], .c 3, .c 7, .c 137, .c 3, .c 17, .c 11, .c 3, .c 23, .c 5,
  .c 3, .c 173, .c 97, .c 3,
]
private theorem h0343c20 : checkBlock 2814979 128 b0343c20 = true := by
  decide +kernel

private def b0343c21 : List Row := [
  .c 5, .p pv2 [pv2,pv3,pv8689], .c 3, .c 11, .c 1657, .c 3, .p pv5 [pv2,pv7,pv23,pv1249], .c 19,
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv1407629], .c 419, .c 3, .c 5, .c 7, .c 3,
  .p pv17 [pv2,pv5,pv281527], .c 67, .c 3, .c 83, .c 509, .c 3, .c 757, .c 5, .c 3,
  .p pv23 [pv2,pv7,pv50273], .c 29, .c 3, .c 5, .c 1231, .c 3, .p pv2 [pv2,pv5,pv47,pv599], .c 59,
  .c 3, .c 11, .c 7, .c 3, .p pv3 [pv2,pv179,pv983], .c 5, .c 3, .c 13, .c 131, .c 3, .c 5, .c 31,
  .c 3, .p pv2 [pv2,pv5,pv7,pv37,pv1087], .c 61, .c 3, .c 7, .c 43, .c 3, .p pv5 [pv2,pv1407671],
  .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .c 1579, .c 3, .c 23, .c 19, .c 3, .c 37,
  .p pv13 [pv2,pv3,pv117307], .c 3, .c 11, .c 5, .c 3, .c 7, .c 1481, .c 3, .c 5, .c 17, .c 3,
  .c 73, .c 7, .c 3, .c 13, .p pv17 [pv2,pv3,pv1931], .c 3, .p pv2 [pv2,pv79,pv103,pv173], .c 5,
  .c 3, .c 547, .p pv7 [pv2,pv3,pv5,pv13,pv7219], .c 3, .c 5, .c 11, .c 3, .c 7, .c 13, .c 3,
  .p pv2 [pv2,pv89,pv15817], .c 41, .c 3, .c 383, .c 5, .c 3, .c 11, .c 37, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv469241], .c 3, .c 31, .c 23, .c 3, .p pv3 [pv2,pv7,pv12569], .c 1663, .c 3,
  .c 7, .c 5, .c 3, .p pv2 [pv2,pv43,pv16369], .c 1427, .c 3, .c 5, .c 7, .c 3, .c 79, .c 11,
  .c 3, .c 137, .c 17,
]
private theorem h0343c21 : checkBlock 2815235 128 b0343c21 = true := by
  decide +kernel

private def b0343c22 : List Row := [
  .c 3, .p pv2 [pv2,pv703873], .c 5, .c 3, .c 23, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv3067],
  .c 3, .c 41, .c 31, .c 3, .p pv2 [pv2,pv11,pv61,pv1049], .c 7, .c 3, .c 17, .c 5, .c 3,
  .p pv3 [pv2,pv353,pv997], .c 191, .c 3, .c 5, .c 73, .c 3, .c 67, .c 467, .c 3, .c 7, .c 11,
  .c 3, .c 13, .c 5, .c 3, .p pv13 [pv2,pv347,pv4057], .c 7, .c 3, .c 5, .c 283, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv19,pv53,pv233], .c 3, .c 61, .c 13, .c 3, .c 131, .c 5, .c 3, .c 7, .c 17,
  .c 3, .c 5, .c 43, .c 3, .c 571, .c 7, .c 3, .p pv5 [pv2,pv31,pv45413], .c 83, .c 3,
  .p pv2 [pv2,pv703903], .c 5, .c 3, .c 97, .c 113, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv37,pv1153],
  .c 3, .c 7, .p pv11 [pv2,pv3,pv19553], .c 3, .c 11, .c 29, .c 3, .c 677, .c 5, .c 3,
  .p pv3 [pv2,pv11,pv19,pv421], .c 199, .c 3, .c 5, .c 13, .c 3, .c 1031, .c 37, .c 3, .c 19,
  .p pv7 [pv2,pv3,pv29,pv31], .c 3, .c 7, .c 5, .c 3, .c 449, .c 11, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv271,pv1039], .c 17, .c 3, .c 29, .c 31, .c 3, .c 11, .c 5, .c 3, .c 13,
  .c 103, .c 3, .c 5, .c 127, .c 3, .c 197, .c 47, .c 3, .c 17, .c 7, .c 3,
  .p pv2 [pv2,pv349,pv2017], .c 5, .c 3, .p pv2 [pv2,pv1407869], .p pv7 [pv2,pv3,pv5,pv15643],
  .c 3, .c 5,
]
private theorem h0343c22 : checkBlock 2815491 128 b0343c22 = true := by
  decide +kernel

private def b0343c23 : List Row := [
  .c 11, .c 3, .c 1109, .c 853, .c 3, .c 7, .p pv7 [pv2,pv3,pv11,pv14221], .c 3,
  .p pv2 [pv2,pv19,pv74099], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 373, .c 3, .c 19, .c 1303,
  .c 3, .c 13, .c 71, .c 3, .p pv3 [pv2,pv7,pv31,pv811], .c 5, .c 3, .c 7, .c 797, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv67043], .c 3, .c 37, .c 7, .c 3, .c 47, .c 19, .c 3, .c 31, .c 5, .c 3,
  .c 17, .c 619, .c 3, .c 5, .c 53, .c 3, .c 7, .p pv2 [pv2,pv3,pv29,pv16183], .c 3, .c 113,
  .c 179, .c 3, .p pv2 [pv2,pv13,pv54151], .c 5, .c 3, .c 1381, .p pv2 [pv2,pv3,pv5,pv71,pv661],
  .c 3, .c 5, .c 23, .c 3, .c 29, .c 607, .c 3, .p pv2 [pv2,pv7,pv19,pv67,pv79], .c 11, .c 3,
  .c 7, .c 5, .c 3, .p pv3 [pv2,pv175993], .c 13, .c 3, .c 5, .c 7, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv73,pv2143], .c 3, .c 659, .c 1361, .c 3, .c 23, .c 5, .c 3, .c 107, .c 41,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv469321], .c 3, .c 17, .c 19, .c 3, .p pv3 [pv2,pv23,pv1913], .c 7,
  .c 3, .c 13, .c 5, .c 3, .c 257, .c 149, .c 3, .c 5, .c 1117, .c 3, .c 271,
  .p pv5 [pv2,pv3,pv41,pv11447], .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv337,pv2089], .c 5, .c 3,
  .p pv2 [pv2,pv11,pv31,pv4129], .c 7, .c 3, .c 5, .c 29, .c 3, .c 367, .p pv5 [pv2,pv3,pv13037],
  .c 3, .p pv2 [pv2,pv37,pv53,pv359], .c 17, .c 3,
]
private theorem h0343c23 : checkBlock 2815747 128 b0343c23 = true := by
  decide +kernel

private def b0343c24 : List Row := [
  .c 41, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv17,pv29], .c 3, .c 13, .c 7,
  .c 3, .c 43, .p pv2 [pv2,pv3,pv19,pv23,pv179], .c 3, .c 11, .c 5, .c 3, .c 773, .c 479, .c 3,
  .c 5, .c 13, .c 3, .c 7, .p pv5 [pv2,pv3,pv47,pv4993], .c 3, .p pv3 [pv2,pv352007],
  .p pv2 [pv2,pv3,pv7,pv67049], .c 3, .c 193, .c 5, .c 3, .c 421, .c 31, .c 3, .c 5, .c 11, .c 3,
  .c 349, .p pv2 [pv2,pv3,pv101,pv1549], .c 3, .p pv5 [pv2,pv7,pv13,pv15473],
  .p pv17 [pv2,pv3,pv11,pv10667], .c 3, .c 7, .c 5, .c 3, .c 11, .c 17, .c 3, .c 5, .c 7, .c 3,
  .c 307, .c 43, .c 3, .c 1423, .c 1009, .c 3, .c 19, .c 5, .c 3, .c 59,
  .p pv67 [pv2,pv3,pv5,pv93871], .c 3, .c 5, .c 239, .c 3, .p pv2 [pv2,pv5,pv139,pv1013], .c 11,
  .c 3, .p pv2 [pv2,pv47,pv29959], .c 7, .c 3, .c 631, .c 5, .c 3, .c 1601, .c 19, .c 3, .c 5,
  .c 41, .c 3, .p pv2 [pv2,pv5,pv7,pv40231], .p pv2 [pv2,pv3,pv137,pv571], .c 3, .c 7, .c 181,
  .c 3, .c 101, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv234683], .c 3, .c 97,
  .c 13, .c 3, .c 179, .c 11, .c 3, .p pv2 [pv2,pv7,pv23,pv4373], .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv11,pv17,pv251], .c 3, .c 5, .c 89, .c 3, .c 11, .c 7, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv131,pv3583], .c 3, .p pv2 [pv2,pv11,pv13,pv43,pv229], .c 5, .c 3, .c 41,
  .p pv2 [pv2,pv3,pv5,pv751], .c 3, .c 5, .c 31,
]
private theorem h0343c24 : checkBlock 2816003 128 b0343c24 = true := by
  decide +kernel

private def b0343c25 : List Row := [
  .c 3, .c 7, .p pv3 [pv2,pv3,pv52153], .c 3, .c 73, .p pv2 [pv2,pv3,pv7,pv13,pv2579], .c 3,
  .c 83, .c 5, .c 3, .c 139, .c 13, .c 3, .c 5, .c 47, .c 3, .p pv2 [pv2,pv5,pv41,pv6869],
  .p pv2 [pv2,pv3,pv37,pv6343], .c 3, .c 11, .c 113, .c 3, .c 7, .c 5, .c 3, .c 61,
  .p pv3 [pv2,pv3,pv5,pv7,pv13411], .c 3, .c 5, .c 7, .c 3, .c 487, .c 719, .c 3, .c 23, .c 37,
  .c 3, .c 13, .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .c 107, .c 3, .c 19,
  .p pv13 [pv2,pv3,pv7,pv11,pv127], .c 3, .c 71, .c 7, .c 3, .c 11, .c 5, .c 3, .c 131, .c 43,
  .c 3, .c 5, .p pv31 [pv2,pv3,pv239,pv491], .c 3, .c 31, .c 1259, .c 3, .c 7, .c 19, .c 3, .c 29,
  .c 5, .c 3, .p pv11 [pv2,pv13,pv149,pv727], .c 7, .c 3, .c 5, .c 11, .c 3, .c 13, .c 41, .c 3,
  .c 1087, .c 23, .c 3, .c 157, .c 5, .c 3, .c 7, .c 61, .c 3, .c 5, .c 13, .c 3, .c 17, .c 7,
  .c 3, .c 199, .c 193, .c 3, .p pv2 [pv2,pv151,pv4663], .c 5, .c 3, .p pv2 [pv2,pv17,pv82837],
  .c 761, .c 3, .c 5, .c 263, .c 3, .c 7, .c 11, .c 3, .c 37, .c 67, .c 3, .c 59, .c 5, .c 3,
  .c 13, .c 457, .c 3, .c 5, .c 1151, .c 3, .p pv2 [pv2,pv5,pv43,pv131], .c 19, .c 3,
  .p pv2 [pv2,pv7,pv11,pv18289], .c 17, .c 3, .c 7,
]
private theorem h0343c25 : checkBlock 2816259 128 b0343c25 = true := by
  decide +kernel

private def b0343c26 : List Row := [
  .c 5, .c 3, .p pv17 [pv2,pv419,pv3361], .c 661, .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv281653], .p pv23 [pv2,pv3,pv8693], .c 3, .p pv3 [pv2,pv31,pv41,pv277], .c 11,
  .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv7,pv100591], .c 37, .c 3, .c 5, .c 23, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv7,pv67061], .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv11,pv64013], .c 5, .c 3,
  .c 19, .p pv2 [pv2,pv3,pv5,pv13,pv23,pv157], .c 3, .c 5, .c 79, .c 3, .c 1409, .c 13, .c 3,
  .c 7, .c 347, .c 3, .c 23, .c 5, .c 3, .c 293, .c 7, .c 3, .c 5, .c 19, .c 3, .c 1499,
  .p pv5 [pv2,pv3,pv167,pv937], .c 3, .c 11, .c 31, .c 3, .p pv3 [pv2,pv7,pv13,pv53,pv73], .c 5,
  .c 3, .c 7, .c 71, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv199,pv337], .c 3, .p pv2 [pv2,pv5,pv56333],
  .c 7, .c 3, .p pv3 [pv2,pv176041], .c 41, .c 3, .c 47, .c 5, .c 3, .c 109, .c 11, .c 3, .c 5,
  .c 191, .c 3, .c 7, .c 29, .c 3, .c 313, .c 563, .c 3, .c 11, .c 5, .c 3, .c 37,
  .p pv2 [pv2,pv3,pv5,pv41,pv229], .c 3, .c 5, .p pv2 [pv2,pv3,pv197,pv2383], .c 3,
  .p pv7 [pv2,pv5,pv13,pv47,pv461], .c 17, .c 3, .p pv3 [pv2,pv7,pv2053], .c 59, .c 3, .c 7, .c 5,
  .c 3, .c 1039, .c 19, .c 3, .c 5, .c 7, .c 3, .c 23, .c 571, .c 3, .c 17, .c 13, .c 3, .c 31,
  .c 5, .c 3, .c 11, .c 89, .c 3, .c 5, .p pv3 [pv2,pv3,pv156487], .c 3,
]
private theorem h0343c26 : checkBlock 2816515 128 b0343c26 = true := by
  decide +kernel

private def b0343c27 : List Row := [
  .c 83, .c 37, .c 3, .p pv3 [pv2,pv352097], .c 7, .c 3, .c 71, .c 5, .c 3, .c 101, .c 53, .c 3,
  .c 5, .c 61, .c 3, .c 13, .c 11, .c 3, .c 7, .p pv11 [pv2,pv3,pv241,pv487], .c 3, .c 277, .c 5,
  .c 3, .p pv2 [pv2,pv1408409], .c 7, .c 3, .c 5, .c 13, .c 3, .p pv19 [pv2,pv5,pv281683], .c 23,
  .c 3, .c 59, .p pv3 [pv2,pv3,pv156491], .c 3, .c 227, .c 5, .c 3, .c 7, .c 47, .c 3, .c 5,
  .c 29, .c 3, .p pv2 [pv2,pv5,pv127,pv1109], .c 7, .c 3, .c 491, .c 11, .c 3,
  .p pv3 [pv2,pv352109], .c 5, .c 3, .c 13, .c 67, .c 3, .c 5, .c 43, .c 3, .c 7, .c 131, .c 3,
  .c 53, .p pv3 [pv2,pv3,pv7,pv47,pv1427], .c 3, .c 79, .c 5, .c 3, .p pv2 [pv2,pv31,pv22717],
  .c 421, .c 3, .c 5, .c 17, .c 3, .c 19, .c 179, .c 3, .p pv5 [pv2,pv7,pv201209], .c 229, .c 3,
  .c 7, .c 5, .c 3, .c 31, .p pv2 [pv2,pv3,pv5,pv7,pv19,pv353], .c 3, .c 5, .c 7, .c 3, .c 17,
  .p pv5 [pv2,pv3,pv117373], .c 3, .c 11, .c 19, .c 3, .p pv2 [pv2,pv1091,pv1291], .c 5, .c 3,
  .p pv19 [pv2,pv7,pv11,pv17,pv269], .c 23, .c 3, .c 5, .c 97, .c 3, .p pv3 [pv2,pv5,pv61,pv2309],
  .c 13, .c 3, .c 41, .c 7, .c 3, .c 263, .c 5, .c 3, .c 479, .c 11, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv469501], .c 3, .p pv2 [pv2,pv5,pv7,pv5749], .c 587, .c 3, .c 7, .c 17, .c 3,
  .c 11, .c 5,
]
private theorem h0343c27 : checkBlock 2816771 128 b0343c27 = true := by
  decide +kernel

private def b0343c28 : List Row := [
  .c 3, .p pv2 [pv2,pv41,pv89,pv193], .c 7, .c 3, .c 5, .c 443, .c 3, .c 61,
  .p pv2 [pv2,pv3,pv653,pv719], .c 3, .c 521, .c 241, .c 3, .c 17, .c 5, .c 3, .c 7, .c 13, .c 3,
  .c 5, .c 11, .c 3, .c 1607, .c 7, .c 3, .p pv2 [pv2,pv704269], .p pv3 [pv2,pv3,pv11,pv42683],
  .c 3, .p pv2 [pv2,pv67,pv21023], .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv113,pv277], .c 3,
  .c 5, .c 599, .c 3, .c 7, .c 83, .c 3, .c 379, .c 23, .c 3, .c 13, .c 5, .c 3, .c 569, .c 17,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv4013], .c 3, .c 137, .c 11, .c 3, .p pv3 [pv2,pv7,pv25153],
  .c 13, .c 3, .c 7, .c 5, .c 3, .c 19, .c 41, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv70429],
  .c 61, .c 3, .p pv11 [pv2,pv11,pv128053], .p pv7 [pv2,pv3,pv19,pv3089], .c 3,
  .p pv2 [pv2,pv17,pv2437], .c 5, .c 3, .c 317, .p pv19 [pv2,pv3,pv5,pv37,pv47], .c 3, .c 5,
  .c 19, .c 3, .c 13, .c 101, .c 3, .p pv2 [pv2,pv704299], .c 7, .c 3, .c 107, .c 5, .c 3, .c 71,
  .p pv2 [pv2,pv3,pv5,pv11,pv8537], .c 3, .c 5, .c 13, .c 3, .c 11, .c 17, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv234769], .c 3, .c 41, .c 5, .c 3, .p pv37 [pv2,pv1408619], .c 7, .c 3, .c 5,
  .c 23, .c 3, .p pv2 [pv2,pv5,pv59,pv191], .p pv2 [pv2,pv3,pv139,pv563], .c 3, .c 17,
  .p pv2 [pv2,pv3,pv469543], .c 3, .c 19, .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv23,pv1361],
  .c 3, .c 5, .c 1637, .c 3, .c 179,
]
private theorem h0343c28 : checkBlock 2817027 128 b0343c28 = true := by
  decide +kernel

private def b0343c29 : List Row := [
  .c 7, .c 3, .c 11, .c 73, .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv11,pv79,pv1621], .c 19, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv281,pv557], .c 3, .c 7, .c 313, .c 3, .c 43, .c 701, .c 3, .c 109, .c 5,
  .c 3, .c 1459, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv117389], .c 3, .p pv3 [pv2,pv5,pv140867],
  .c 593, .c 3, .c 13, .c 311, .c 3, .c 7, .c 5, .c 3, .c 17, .p pv11 [pv2,pv3,pv5,pv7,pv13,pv43],
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv281737], .c 13, .c 3, .c 19, .c 29, .c 3,
  .p pv5 [pv2,pv223,pv6317], .c 5, .c 3, .p pv2 [pv2,pv7,pv100621], .c 139, .c 3, .c 5, .c 11,
  .c 3, .c 523, .c 43, .c 3, .c 61, .c 7, .c 3, .c 991, .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv46957], .c 3, .c 5, .c 17, .c 3, .c 23, .p pv5 [pv2,pv3,pv109,pv359],
  .c 3, .c 7, .c 37, .c 3, .p pv2 [pv2,pv199,pv7079], .c 5, .c 3, .p pv3 [pv2,pv352181], .c 7,
  .c 3, .c 5, .c 167, .c 3, .c 17, .c 11, .c 3, .p pv2 [pv2,pv29,pv31,pv1567],
  .p pv11 [pv2,pv3,pv61,pv1283], .c 3, .c 89, .c 5, .c 3, .c 7, .p pv31 [pv2,pv3,pv5,pv53,pv443],
  .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv59,pv379], .c 3, .c 19, .c 7, .c 3, .c 31,
  .p pv2 [pv2,pv3,pv469583], .c 3, .c 13, .c 5, .c 3, .c 47, .p pv11 [pv2,pv3,pv5,pv19,pv4943],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv18061], .c 3, .c 7, .c 23, .c 3, .c 389, .c 11, .c 3, .c 53,
  .c 5, .c 3,
]
private theorem h0343c29 : checkBlock 2817283 128 b0343c29 = true := by
  decide +kernel

private def b0343c30 : List Row := [
  .p pv2 [pv2,pv1408769], .c 109, .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv23,pv1201], .c 3, .c 11,
  .c 29, .c 3, .p pv2 [pv2,pv7,pv47,pv2141], .c 31, .c 3, .c 7, .c 5, .c 3, .c 23, .c 239, .c 3,
  .c 5, .c 7, .c 3, .c 13, .p pv3 [pv2,pv3,pv29,pv16193], .c 3, .c 37, .c 827, .c 3,
  .p pv3 [pv2,pv23,pv15313], .c 5, .c 3, .p pv7 [pv2,pv7,pv28751], .c 83, .c 3, .c 5, .c 13, .c 3,
  .c 29, .p pv11 [pv2,pv3,pv7,pv3727], .c 3, .c 11, .c 7, .c 3, .p pv5 [pv2,pv127,pv11093], .c 5,
  .c 3, .p pv2 [pv2,pv11,pv64037], .c 17, .c 3, .c 5, .c 1279, .c 3, .c 199, .c 19, .c 3, .c 7,
  .p pv23 [pv2,pv3,pv17,pv1151], .c 3, .c 883, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv17393], .c 3, .p pv17 [pv2,pv5,pv281767], .p pv5 [pv2,pv3,pv11,pv13,pv821],
  .c 3, .p pv2 [pv2,pv704419], .c 131, .c 3, .c 11, .c 5, .c 3, .c 7, .c 197, .c 3, .c 5, .c 47,
  .c 3, .p pv2 [pv2,pv5,pv19,pv1483], .c 7, .c 3, .c 23, .p pv2 [pv2,pv3,pv234809], .c 3,
  .p pv3 [pv2,pv61,pv2887], .c 5, .c 3, .c 19, .p pv37 [pv2,pv3,pv5,pv2609], .c 3, .c 5, .c 11,
  .c 3, .c 7, .c 17, .c 3, .c 13, .c 149, .c 3, .p pv5 [pv2,pv1408871], .c 5, .c 3, .c 11, .c 227,
  .c 3, .c 5, .c 19, .c 3, .c 719, .c 13, .c 3, .c 17, .p pv7 [pv2,pv3,pv113,pv1039], .c 3, .c 7,
  .c 5, .c 3, .p pv2 [pv2,pv1408889], .c 59, .c 3, .c 5, .c 7, .c 3, .c 47, .c 11,
]
private theorem h0343c30 : checkBlock 2817539 128 b0343c30 = true := by
  decide +kernel

private def b0343c31 : List Row := [
  .c 3, .p pv2 [pv2,pv704449], .c 23, .c 3, .c 331, .c 5, .c 3, .c 37, .c 151, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv137,pv857], .c 3, .p pv2 [pv2,pv5,pv140891], .c 191, .c 3, .c 401, .c 7, .c 3,
  .c 19, .c 5, .c 3, .c 617, .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv37,pv4231], .c 3, .c 53, .c 499,
  .c 3, .c 7, .c 11, .c 3, .c 557, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv43,pv127], .c 3, .c 11, .c 37, .c 3, .p pv5 [pv2,pv17,pv67,pv1237], .c 41,
  .c 3, .c 13, .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv13,pv397], .c 3,
  .c 1613, .c 7, .c 3, .p pv2 [pv2,pv389,pv1811], .c 13, .c 3, .c 443, .c 5, .c 3,
  .p pv3 [pv2,pv19,pv18539], .c 31, .c 3, .c 5, .c 17, .c 3, .c 7, .p pv3 [pv2,pv3,pv469657],
  .c 3, .c 11, .c 1163, .c 3, .c 67, .c 5, .c 3, .c 29, .c 613, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv19,pv1301], .c 3, .c 13, .p pv2 [pv2,pv3,pv78277], .c 3, .c 103, .c 47, .c 3,
  .c 7, .c 5, .c 3, .c 181, .c 11, .c 3, .c 5, .c 7, .c 3, .c 101, .c 127, .c 3, .c 89, .c 79,
  .c 3, .c 11, .c 5, .c 3, .c 73, .c 953, .c 3, .c 5, .p pv2 [pv2,pv3,pv47,pv3331], .c 3, .c 37,
  .p pv5 [pv2,pv3,pv7,pv8387], .c 3, .c 149, .c 7, .c 3, .p pv2 [pv2,pv19,pv74159], .c 5, .c 3,
  .c 13,
]
private theorem h0343c31 : checkBlock 2817795 128 b0343c31 = true := by
  decide +kernel

def rows0343 : List Row :=
  b0343c00 ++ b0343c01 ++ b0343c02 ++ b0343c03 ++ b0343c04 ++ b0343c05 ++ b0343c06 ++ b0343c07 ++
  b0343c08 ++ b0343c09 ++ b0343c10 ++ b0343c11 ++ b0343c12 ++ b0343c13 ++ b0343c14 ++ b0343c15 ++
  b0343c16 ++ b0343c17 ++ b0343c18 ++ b0343c19 ++ b0343c20 ++ b0343c21 ++ b0343c22 ++ b0343c23 ++
  b0343c24 ++ b0343c25 ++ b0343c26 ++ b0343c27 ++ b0343c28 ++ b0343c29 ++ b0343c30 ++ b0343c31

attribute [local irreducible] checkBlock checkRows checkPrime

theorem checked0343 : checkBlock 2809859 4096 rows0343 = true :=
  checkBlock_append h0343c00 (
    checkBlock_append h0343c01 (
    checkBlock_append h0343c02 (
    checkBlock_append h0343c03 (
    checkBlock_append h0343c04 (
    checkBlock_append h0343c05 (
    checkBlock_append h0343c06 (
    checkBlock_append h0343c07 (
    checkBlock_append h0343c08 (
    checkBlock_append h0343c09 (
    checkBlock_append h0343c10 (
    checkBlock_append h0343c11 (
    checkBlock_append h0343c12 (
    checkBlock_append h0343c13 (
    checkBlock_append h0343c14 (
    checkBlock_append h0343c15 (
    checkBlock_append h0343c16 (
    checkBlock_append h0343c17 (
    checkBlock_append h0343c18 (
    checkBlock_append h0343c19 (
    checkBlock_append h0343c20 (
    checkBlock_append h0343c21 (
    checkBlock_append h0343c22 (
    checkBlock_append h0343c23 (
    checkBlock_append h0343c24 (
    checkBlock_append h0343c25 (
    checkBlock_append h0343c26 (
    checkBlock_append h0343c27 (
    checkBlock_append h0343c28 (
    checkBlock_append h0343c29 (
    checkBlock_append h0343c30 (
    h0343c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
