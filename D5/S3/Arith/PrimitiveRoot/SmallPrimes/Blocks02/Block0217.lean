/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks02/Block0217
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks02/Block0217.checked0217
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table027
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table031
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table037
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table046
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table060
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table084
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table085
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table134

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0217c00 : List Row := [
  .c 199, .c 257, .c 3, .c 17, .c 5, .c 3, .c 877, .c 47, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv89,pv3329], .c 3, .p pv2 [pv2,pv5,pv17,pv10457], .c 23, .c 3, .c 19, .c 7,
  .c 3, .p pv5 [pv2,pv37,pv24023], .c 5, .c 3, .c 1123, .c 13, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv19,pv23,pv113], .c 3, .c 11, .c 61, .c 3, .c 7, .c 29, .c 3,
  .p pv2 [pv2,pv11,pv3673], .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 1069, .c 3,
  .p pv23 [pv2,pv5,pv13,pv547], .p pv5 [pv2,pv3,pv24691], .c 3, .c 31, .c 443, .c 3, .c 13, .c 5,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv19753], .c 3, .c 5, .c 83, .c 3, .p pv2 [pv2,pv5,pv103,pv863],
  .c 7, .c 3, .c 11, .c 13, .c 3, .c 1033, .c 5, .c 3, .p pv7 [pv2,pv11,pv80809], .c 41, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv283,pv349], .c 3, .c 7, .c 37, .c 3, .c 419, .c 31, .c 3,
  .p pv5 [pv2,pv47,pv18913], .c 5, .c 3, .c 113, .c 11, .c 3, .c 5, .c 307, .c 3, .c 13, .c 17,
  .c 3, .c 59, .c 19, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv881,pv1009],
  .p pv23 [pv2,pv3,pv5,pv7,pv17,pv83], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv177787], .c 127,
  .c 3, .c 17, .p pv3 [pv2,pv3,pv43,pv2297], .c 3, .c 41, .c 5, .c 3, .c 379,
  .p pv2 [pv2,pv3,pv5,pv59263], .c 3, .c 5, .c 11, .c 3, .c 971, .c 29, .c 3,
  .p pv2 [pv2,pv13,pv19,pv59,pv61], .c 7, .c 3, .c 97, .c 5, .c 3, .c 11, .c 43,
]
private theorem h0217c00 : checkBlock 1777667 128 b0217c00 = true := by
  decide +kernel

private def b0217c01 : List Row := [
  .c 3, .c 5, .p pv7 [pv2,pv3,pv257,pv1153], .c 3, .p pv2 [pv2,pv5,pv7,pv11,pv2309],
  .p pv2 [pv2,pv3,pv13,pv29,pv131], .c 3, .c 7, .p pv3 [pv2,pv3,pv53,pv5591], .c 3, .c 31, .c 5,
  .c 3, .c 139, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv229,pv647], .c 3, .c 29, .c 11, .c 3, .c 61,
  .c 23, .c 3, .p pv2 [pv2,pv7,pv63499], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv29633], .c 3,
  .c 5, .c 311, .c 3, .c 53, .c 7, .c 3, .c 13, .c 743, .c 3, .p pv2 [pv2,pv889001], .c 5, .c 3,
  .p pv3 [pv2,pv109,pv2039], .p pv2 [pv2,pv3,pv5,pv13,pv47,pv97], .c 3, .c 5, .c 149, .c 3, .c 7,
  .c 13, .c 3, .p pv2 [pv2,pv83,pv10711], .c 11, .c 3, .p pv3 [pv2,pv111127], .c 5, .c 3, .c 19,
  .p pv17 [pv2,pv3,pv5,pv11,pv449], .c 3, .c 5, .c 17, .c 3, .c 11, .c 71, .c 3, .c 47,
  .p pv3 [pv2,pv3,pv19,pv1733], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv444517],
  .p pv31 [pv2,pv3,pv5,pv7,pv8467], .c 3, .c 5, .c 7, .c 3, .c 17, .c 59, .c 3, .c 719, .c 61,
  .c 3, .c 43, .c 5, .c 3, .p pv2 [pv2,pv7,pv17,pv31,pv241], .c 13, .c 3, .c 5, .c 23, .c 3,
  .p pv11 [pv2,pv5,pv177811], .c 67, .c 3, .c 11, .c 7, .c 3, .c 137, .c 5, .c 3, .c 31, .c 89,
  .c 3, .c 5, .p pv23 [pv2,pv3,pv43,pv1723], .c 3, .p pv2 [pv2,pv5,pv7,pv13,pv977], .c 263, .c 3,
  .c 7, .c 17, .c 3, .c 13, .c 5, .c 3, .p pv11 [pv2,pv631,pv1409], .c 7, .c 3, .c 5, .c 163,
  .c 3, .p pv13 [pv2,pv5,pv41,pv4337], .c 521, .c 3, .p pv3 [pv2,pv23,pv151],
]
private theorem h0217c01 : checkBlock 1777923 128 b0217c01 = true := by
  decide +kernel

private def b0217c02 : List Row := [
  .c 13, .c 3, .c 11, .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv21169], .c 3,
  .c 59, .c 7, .c 3, .c 73, .p pv19 [pv2,pv3,pv18523], .c 3, .p pv2 [pv2,pv444553], .c 5, .c 3,
  .p pv2 [pv2,pv13,pv5261], .p pv2 [pv2,pv3,pv5,pv37,pv89], .c 3, .c 5, .c 11, .c 3, .c 7, .c 107,
  .c 3, .c 1097, .p pv11 [pv2,pv3,pv7,pv11,pv1283], .c 3, .p pv2 [pv2,pv727,pv1223], .c 5, .c 3,
  .c 11, .c 17, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv11,pv59,pv137],
  .p pv3 [pv2,pv3,pv296377], .c 3, .c 19, .c 383, .c 3, .c 7, .c 5, .c 3, .p pv17 [pv2,pv889139],
  .c 113, .c 3, .c 5, .c 7, .c 3, .c 23, .c 11, .c 3, .c 547, .p pv2 [pv2,pv3,pv311,pv953], .c 3,
  .p pv5 [pv2,pv17,pv193,pv271], .c 5, .c 3, .c 13, .c 1093, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv148193], .c 3, .p pv3 [pv2,pv5,pv22229], .p pv2 [pv2,pv3,pv7,pv13,pv3257],
  .c 3, .c 151, .c 7, .c 3, .c 61, .c 5, .c 3, .c 47, .p pv17 [pv2,pv3,pv5,pv107,pv277], .c 3,
  .c 5, .p pv5 [pv2,pv3,pv31,pv3187], .c 3, .c 43, .c 17, .c 3, .c 7, .c 11, .c 3, .c 1229, .c 5,
  .c 3, .c 79, .c 7, .c 3, .c 5, .c 31, .c 3, .c 11, .c 23, .c 3, .c 13, .c 439, .c 3,
  .p pv3 [pv2,pv7,pv11,pv2887], .c 5, .c 3, .c 7, .c 191, .c 3, .c 5, .c 593, .c 3,
  .p pv2 [pv2,pv5,pv177841], .c 7, .c 3, .p pv3 [pv2,pv41,pv2711], .c 19, .c 3,
  .p pv5 [pv2,pv889211], .c 5, .c 3, .c 23, .c 599, .c 3,
]
private theorem h0217c02 : checkBlock 1778179 128 b0217c02 = true := by
  decide +kernel

private def b0217c03 : List Row := [
  .c 5, .c 43, .c 3, .c 7, .p pv2 [pv2,pv3,pv37,pv8011], .c 3, .c 11, .c 281, .c 3,
  .p pv2 [pv2,pv13,pv23,pv1487], .c 5, .c 3, .p pv2 [pv2,pv11,pv7349],
  .p pv17 [pv2,pv3,pv5,pv29641], .c 3, .c 5, .c 1301, .c 3, .p pv7 [pv2,pv5,pv31,pv5737],
  .p pv5 [pv2,pv3,pv17,pv1453], .c 3, .p pv2 [pv2,pv7,pv19,pv3343], .c 37, .c 3, .c 7, .c 5, .c 3,
  .c 17, .c 11, .c 3, .c 5, .c 7, .c 3, .c 31, .c 823, .c 3, .c 113, .c 101, .c 3, .c 11, .c 5,
  .c 3, .c 211, .c 23, .c 3, .c 5, .c 47, .c 3, .p pv2 [pv2,pv5,pv13,pv13681], .c 19, .c 3,
  .p pv3 [pv2,pv222317], .c 7, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv444637],
  .p pv11 [pv2,pv3,pv5,pv71,pv167], .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv7,pv397], .c 31,
  .c 3, .c 7, .c 13, .c 3, .c 271, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 131, .c 3, .c 17,
  .p pv5 [pv2,pv3,pv97,pv191], .c 3, .p pv2 [pv2,pv444649], .c 29, .c 3, .c 647, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv101,pv587], .c 3, .c 5, .c 277, .c 3, .c 13, .c 7, .c 3, .c 37, .c 151,
  .c 3, .p pv3 [pv2,pv222329], .c 5, .c 3, .p pv7 [pv2,pv61,pv239], .c 659, .c 3, .c 5, .c 13,
  .c 3, .c 7, .c 157, .c 3, .c 29, .c 17, .c 3, .p pv5 [pv2,pv41,pv109,pv199], .c 5, .c 3, .c 263,
  .c 137, .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv8719], .c 3, .c 1201, .p pv2 [pv2,pv3,pv23,pv12889],
  .c 3, .c 31, .c 11,
]
private theorem h0217c03 : checkBlock 1778435 128 b0217c03 = true := by
  decide +kernel

private def b0217c04 : List Row := [
  .c 3, .c 7, .c 5, .c 3, .c 13, .c 37, .c 3, .c 5, .c 7, .c 3, .c 11, .c 197, .c 3, .c 167,
  .p pv43 [pv2,pv3,pv31,pv73,pv131], .c 3, .c 19, .c 5, .c 3, .p pv11 [pv2,pv7,pv23,pv1381],
  .p pv2 [pv2,pv3,pv5,pv211,pv281], .c 3, .c 5, .c 431, .c 3, .c 409,
  .p pv5 [pv2,pv3,pv7,pv19,pv743], .c 3, .p pv2 [pv2,pv889373], .c 7, .c 3, .p pv3 [pv2,pv27793],
  .c 5, .c 3, .p pv11 [pv2,pv307,pv2897], .c 17, .c 3, .c 5, .c 353, .c 3, .c 109, .c 29, .c 3,
  .c 7, .c 313, .c 3, .c 67, .c 5, .c 3, .c 631, .c 7, .c 3, .c 5, .c 23, .c 3,
  .p pv3 [pv2,pv5,pv4447], .c 13, .c 3, .p pv5 [pv2,pv719,pv1237], .c 47, .c 3,
  .p pv2 [pv2,pv7,pv17,pv37,pv101], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 1307, .c 3, .c 29,
  .c 7, .c 3, .c 19, .c 53, .c 3, .c 11, .c 5, .c 3, .c 37, .p pv2 [pv2,pv3,pv5,pv59,pv67], .c 3,
  .c 5, .p pv5 [pv2,pv3,pv19,pv47,pv83], .c 3, .c 7, .c 17, .c 3, .c 41,
  .p pv2 [pv2,pv3,pv7,pv13,pv181], .c 3, .c 31, .c 5, .c 3, .p pv7 [pv2,pv889439], .c 13, .c 3,
  .c 5, .c 11, .c 3, .c 577, .c 491, .c 3, .c 17, .p pv2 [pv2,pv3,pv11,pv26953], .c 3, .c 7, .c 5,
  .c 3, .c 11, .c 149, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv11,pv13,pv311], .c 37, .c 3,
  .p pv5 [pv2,pv613,pv1451], .p pv7 [pv2,pv3,pv37061], .c 3, .c 13, .c 5, .c 3, .c 83, .c 211,
  .c 3, .c 5,
]
private theorem h0217c04 : checkBlock 1778691 128 b0217c04 = true := by
  decide +kernel

private def b0217c05 : List Row := [
  .c 29, .c 3, .c 19, .c 11, .c 3, .c 397, .c 7, .c 3, .p pv2 [pv2,pv889481], .c 5, .c 3, .c 727,
  .p pv2 [pv2,pv3,pv5,pv19,pv3121], .c 3, .c 5, .p pv5 [pv2,pv3,pv29,pv71], .c 3, .c 23,
  .p pv3 [pv2,pv3,pv17,pv107,pv163], .c 3, .c 7, .c 19, .c 3, .p pv3 [pv2,pv111187], .c 5, .c 3,
  .c 17, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv479,pv619], .c 3, .c 13, .p pv2 [pv2,pv3,pv49417],
  .c 3, .p pv3 [pv2,pv17,pv103,pv127], .c 11, .c 3, .c 337, .c 5, .c 3, .c 7, .c 41, .c 3, .c 5,
  .c 13, .c 3, .c 11, .c 7, .c 3, .c 71, .c 181, .c 3, .p pv2 [pv2,pv11,pv40433], .c 5, .c 3,
  .c 31, .c 139, .c 3, .c 5, .c 17, .c 3, .c 7, .c 23, .c 3, .c 97, .c 1153, .c 3, .c 73, .c 5,
  .c 3, .c 13, .c 47, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv23,pv293], .c 3, .c 17, .c 19, .c 3,
  .c 11, .p pv2 [pv2,pv3,pv37,pv4007], .c 3, .c 7, .c 5, .c 3, .c 23, .c 29, .c 3, .c 5, .c 7,
  .c 3, .p pv2 [pv2,pv5,pv177913], .p pv5 [pv2,pv3,pv173,pv857], .c 3, .p pv3 [pv2,pv27799],
  .c 1103, .c 3, .c 127, .c 5, .c 3, .p pv2 [pv2,pv7,pv63541], .c 11, .c 3, .c 5, .c 53, .c 3,
  .p pv3 [pv2,pv5,pv19,pv2341], .p pv5 [pv2,pv3,pv7,pv11,pv3851], .c 3, .c 13, .c 7, .c 3, .c 11,
  .c 5, .c 3, .c 19, .c 643, .c 3, .c 5, .c 61, .c 3, .p pv7 [pv2,pv5,pv7,pv3631], .c 13, .c 3,
  .c 7, .c 89, .c 3,
]
private theorem h0217c05 : checkBlock 1778947 128 b0217c05 = true := by
  decide +kernel

private def b0217c06 : List Row := [
  .c 17, .c 5, .c 3, .c 149, .c 7, .c 3, .c 5, .c 11, .c 3, .c 283,
  .p pv17 [pv2,pv3,pv103,pv2879], .c 3, .p pv2 [pv2,pv227,pv3919], .c 73, .c 3, .c 151, .c 5,
  .c 3, .c 7, .p pv23 [pv2,pv3,pv5,pv14827], .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv523], .c 3, .c 953,
  .c 7, .c 3, .c 23, .c 199, .c 3, .c 53, .c 5, .c 3, .p pv2 [pv2,pv444817], .c 13, .c 3, .c 5,
  .c 41, .c 3, .c 7, .c 11, .c 3, .p pv5 [pv2,pv389,pv2287], .p pv19 [pv2,pv3,pv7,pv17,pv89],
  .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv113,pv7873], .p pv2 [pv2,pv3,pv5,pv659], .c 3, .c 5,
  .c 31, .c 3, .p pv7 [pv2,pv5,pv13,pv13687], .c 1187, .c 3, .c 79, .c 67, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv13901], .c 19, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv43,pv2069], .c 1051,
  .c 3, .p pv2 [pv2,pv889673], .c 11, .c 3, .c 29, .c 5, .c 3, .c 41,
  .p pv7 [pv2,pv3,pv5,pv11,pv337], .c 3, .c 5, .c 37, .c 3, .c 11, .c 17, .c 3, .c 89, .c 7, .c 3,
  .c 43, .c 5, .c 3, .c 293, .c 547, .c 3, .c 5, .c 127, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv71,pv4177], .c 3, .c 7, .p pv13 [pv2,pv3,pv1373], .c 3, .c 947, .c 5, .c 3,
  .c 1087, .c 7, .c 3, .c 5, .c 13, .c 3, .c 31, .c 877, .c 3, .c 11, .c 179, .c 3,
  .p pv2 [pv2,pv7,pv127103], .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv11863], .c 3, .c 5,
  .p pv19 [pv2,pv3,pv7,pv331],
]
private theorem h0217c06 : checkBlock 1779203 128 b0217c06 = true := by
  decide +kernel

private def b0217c07 : List Row := [
  .c 3, .p pv3 [pv2,pv5,pv193,pv461], .c 7, .c 3, .c 47, .c 29, .c 3, .c 71, .c 5, .c 3, .c 13,
  .c 11, .c 3, .c 5, .c 23, .c 3, .c 7, .c 31, .c 3, .p pv3 [pv2,pv222437], .c 59, .c 3, .c 11,
  .c 5, .c 3, .c 17, .p pv3 [pv2,pv3,pv5,pv23,pv2579], .c 3, .c 5, .c 107, .c 3, .c 19, .c 41,
  .c 3, .c 29, .p pv7 [pv2,pv3,pv53,pv1399], .c 3, .c 7, .c 5, .c 3, .c 613,
  .p pv2 [pv2,pv3,pv5,pv7,pv19,pv223], .c 3, .c 5, .c 7, .c 3, .c 349, .c 61, .c 3, .c 13, .c 19,
  .c 3, .c 359, .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv13], .c 3, .c 5, .c 17, .c 3, .c 53,
  .c 13, .c 3, .c 67, .c 7, .c 3, .c 593, .c 5, .c 3, .c 431, .p pv11 [pv2,pv3,pv5,pv1483], .c 3,
  .c 5, .p pv3 [pv2,pv3,pv98867], .c 3, .c 17, .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv179,pv1657],
  .c 3, .p pv5 [pv2,pv13,pv68447], .c 5, .c 3, .c 599, .c 7, .c 3, .c 5, .c 113, .c 3, .c 43,
  .c 29, .c 3, .p pv5 [pv2,pv11,pv41,pv1973], .p pv19 [pv2,pv3,pv13,pv23,pv31], .c 3, .c 193,
  .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 73, .c 3, .c 23, .c 7, .c 3, .p pv2 [pv2,pv59,pv7541],
  .c 11, .c 3, .p pv2 [pv2,pv293,pv3037], .c 5, .c 3, .p pv3 [pv2,pv222461],
  .p pv2 [pv2,pv3,pv5,pv11,pv5393], .c 3, .c 5, .c 337, .c 3, .c 7, .p pv5 [pv2,pv3,pv47,pv6311],
  .c 3, .c 757, .p pv11 [pv2,pv3,pv7,pv21187], .c 3, .c 13,
]
private theorem h0217c07 : checkBlock 1779459 128 b0217c07 = true := by
  decide +kernel

private def b0217c08 : List Row := [
  .c 5, .c 3, .c 167, .c 67, .c 3, .c 5, .c 43, .c 3, .c 107, .c 89, .c 3, .c 37, .c 13, .c 3,
  .c 7, .c 5, .c 3, .c 19, .c 397, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv22247], .c 23, .c 3,
  .c 11, .c 41, .c 3, .c 181, .c 5, .c 3, .p pv7 [pv2,pv7,pv11,pv13,pv127], .c 17, .c 3, .c 5,
  .c 19, .c 3, .c 13, .c 53, .c 3, .c 61, .c 7, .c 3, .c 31, .c 5, .c 3, .c 23, .c 11, .c 3, .c 5,
  .c 13, .c 3, .p pv2 [pv2,pv5,pv7,pv12713], .p pv3 [pv2,pv3,pv11,pv89,pv101], .c 3, .c 7,
  .p pv11 [pv2,pv3,pv71,pv2089], .c 3, .c 11, .c 5, .c 3, .c 701, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv29,pv53,pv193], .c 3, .c 41, .c 59, .c 3, .p pv3 [pv2,pv13,pv43,pv199],
  .c 1033, .c 3, .c 19, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv79,pv751], .c 3, .c 5, .c 11,
  .c 3, .p pv7 [pv2,pv5,pv44497], .c 7, .c 3, .c 233, .p pv7 [pv2,pv3,pv11,pv3371], .c 3,
  .p pv2 [pv2,pv41,pv10853], .c 5, .c 3, .c 11, .c 19, .c 3, .c 5, .c 227, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv59,pv419], .c 3, .c 17, .c 61, .c 3, .c 101, .c 5, .c 3, .c 191,
  .p pv2 [pv2,pv3,pv5,pv19777], .c 3, .c 5, .c 47, .c 3, .p pv3 [pv2,pv5,pv88997], .c 11, .c 3,
  .c 13, .c 79, .c 3, .c 7, .c 5, .c 3, .c 37, .p pv19 [pv2,pv3,pv5,pv7,pv13,pv163], .c 3, .c 5,
  .c 7, .c 3,
]
private theorem h0217c08 : checkBlock 1779715 128 b0217c08 = true := by
  decide +kernel

private def b0217c09 : List Row := [
  .c 59, .c 13, .c 3, .c 19, .c 761, .c 3, .p pv5 [pv2,pv257,pv3463], .c 5, .c 3, .c 31, .c 29,
  .c 3, .c 5, .c 173, .c 3, .p pv3 [pv2,pv5,pv89], .p pv2 [pv2,pv3,pv7,pv17,pv277], .c 3,
  .p pv5 [pv2,pv890003], .c 7, .c 3, .p pv2 [pv2,pv13,pv34231], .c 5, .c 3, .c 17,
  .p pv23 [pv2,pv3,pv5,pv11,pv29,pv31], .c 3, .c 5, .p pv2 [pv2,pv3,pv241,pv1231], .c 3, .c 11,
  .c 37, .c 3, .c 7, .c 23, .c 3, .c 1237, .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .c 641, .c 3,
  .p pv2 [pv2,pv5,pv89003], .c 433, .c 3, .p pv2 [pv2,pv157,pv5669], .p pv2 [pv2,pv3,pv148339],
  .c 3, .c 661, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv7417], .c 3, .c 5, .c 17, .c 3, .c 19,
  .c 7, .c 3, .c 11, .p pv17 [pv2,pv3,pv296683], .c 3, .c 13, .c 5, .c 3, .c 1289, .c 53, .c 3,
  .c 5, .c 503, .c 3, .c 7, .c 67, .c 3, .p pv5 [pv2,pv890063], .c 13, .c 3,
  .p pv2 [pv2,pv445033], .c 5, .c 3, .c 151, .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv98897], .c 3,
  .p pv7 [pv2,pv5,pv35603], .c 1049, .c 3, .c 43, .c 107, .c 3, .c 7, .c 5, .c 3,
  .p pv7 [pv2,pv13,pv17117], .p pv2 [pv2,pv3,pv5,pv7,pv173], .c 3, .c 5, .c 7, .c 3, .c 13, .c 71,
  .c 3, .p pv2 [pv2,pv19,pv79,pv593], .c 17, .c 3, .c 1019, .c 5, .c 3, .c 271,
  .p pv13 [pv2,pv3,pv5,pv23,pv43], .c 3, .c 5, .c 11, .c 3, .c 853, .c 983, .c 3, .c 53, .c 7,
  .c 3, .c 17, .c 5,
]
private theorem h0217c09 : checkBlock 1779971 128 b0217c09 = true := by
  decide +kernel

private def b0217c10 : List Row := [
  .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv59341], .c 3, .c 5, .c 31, .c 3, .c 97, .c 19, .c 3, .c 7,
  .c 349, .c 3, .p pv2 [pv2,pv29,pv103,pv149], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 83, .c 3,
  .p pv11 [pv2,pv5,pv53,pv3359], .c 11, .c 3, .p pv2 [pv2,pv445069], .c 277, .c 3,
  .p pv5 [pv2,pv7,pv127163], .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 109, .c 3,
  .p pv3 [pv2,pv5,pv19,pv937], .c 7, .c 3, .p pv2 [pv2,pv11,pv80923],
  .p pv7 [pv2,pv3,pv17,pv2909], .c 3, .c 47, .c 5, .c 3, .c 19, .p pv31 [pv2,pv3,pv5,pv3709],
  .c 3, .c 5, .c 101, .c 3, .c 7, .p pv2 [pv2,pv3,pv148361], .c 3, .c 13, .c 11, .c 3, .c 41,
  .c 5, .c 3, .p pv2 [pv2,pv445087], .p pv37 [pv2,pv3,pv5,pv11,pv13,pv83], .c 3, .c 5, .c 19,
  .c 3, .c 11, .c 13, .c 3, .p pv5 [pv2,pv7,pv37,pv491], .c 863, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv571,pv1559], .p pv2 [pv2,pv3,pv5,pv7,pv157], .c 3, .c 5, .c 7, .c 3, .c 67, .c 17,
  .c 3, .c 29, .p pv11 [pv2,pv3,pv98911], .c 3, .c 37, .c 5, .c 3, .c 421,
  .p pv3 [pv2,pv3,pv5,pv17,pv3491], .c 3, .c 5, .c 443, .c 3, .c 131, .c 31, .c 3, .c 11, .c 7,
  .c 3, .c 19, .c 5, .c 3, .p pv13 [pv2,pv11,pv80929], .c 13, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv296741], .c 3, .c 139, .c 23, .c 3, .c 7, .p pv3 [pv2,pv3,pv43,pv67,pv103],
  .c 3, .p pv5 [pv2,pv890231], .c 5, .c 3, .p pv2 [pv2,pv61,pv7297], .c 7, .c 3, .c 5, .c 37,
  .c 3, .p pv7 [pv2,pv5,pv13,pv107],
]
private theorem h0217c10 : checkBlock 1780227 128 b0217c10 = true := by
  decide +kernel

private def b0217c11 : List Row := [
  .p pv2 [pv2,pv3,pv11,pv53,pv509], .c 3, .p pv5 [pv2,pv197,pv4519], .p pv11 [pv2,pv3,pv8243],
  .c 3, .c 11, .c 5, .c 3, .c 7, .c 43, .c 3, .c 5, .c 41, .c 3, .c 269, .c 7, .c 3,
  .p pv2 [pv2,pv31,pv83,pv173], .c 13, .c 3, .p pv2 [pv2,pv23,pv38707], .c 5, .c 3, .c 17, .c 827,
  .c 3, .c 5, .c 11, .c 3, .c 7, .c 73, .c 3, .c 19, .p pv2 [pv2,pv3,pv7,pv11,pv41,pv47], .c 3,
  .c 1163, .c 5, .c 3, .c 11, .c 59, .c 3, .c 5, .c 383, .c 3, .c 13, .p pv2 [pv2,pv3,pv148381],
  .c 3, .p pv3 [pv2,pv7,pv7949], .p pv3 [pv2,pv3,pv31,pv3191], .c 3, .c 7, .c 5, .c 3, .c 41,
  .c 23, .c 3, .c 5, .c 7, .c 3, .p pv31 [pv2,pv5,pv29,pv307], .c 11, .c 3, .p pv5 [pv2,pv890303],
  .c 31, .c 3, .p pv2 [pv2,pv163,pv2731], .c 5, .c 3, .p pv2 [pv2,pv7,pv193,pv659], .c 751, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv296771], .c 3, .c 17, .p pv11 [pv2,pv3,pv7,pv3533], .c 3, .c 23, .c 7,
  .c 3, .p pv2 [pv2,pv19,pv47,pv997], .c 5, .c 3, .c 13, .c 61, .c 3, .c 5, .c 313, .c 3, .c 19,
  .p pv5 [pv2,pv3,pv13,pv37,pv617], .c 3, .c 7, .c 11, .c 3, .c 43, .c 5, .c 3, .c 59, .c 7, .c 3,
  .c 5, .c 29, .c 3, .c 11, .c 191, .c 3, .c 281, .c 17, .c 3, .p pv7 [pv2,pv7,pv11,pv31,pv373],
  .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv59357], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv17,pv29,pv43],
  .c 3, .c 167, .c 7, .c 3, .c 13, .c 23, .c 3, .c 17, .c 5, .c 3,
]
private theorem h0217c11 : checkBlock 1780483 128 b0217c11 = true := by
  decide +kernel

private def b0217c12 : List Row := [
  .c 79, .c 271, .c 3, .c 5, .c 53, .c 3, .c 7, .c 13, .c 3, .c 11, .c 43, .c 3, .c 601, .c 5,
  .c 3, .c 563, .p pv3 [pv2,pv3,pv5,pv59359], .c 3, .c 5, .p pv5 [pv2,pv3,pv24733], .c 3, .c 1297,
  .c 47, .c 3, .p pv2 [pv2,pv7,pv311,pv409], .c 239, .c 3, .c 7, .c 5, .c 3,
  .p pv11 [pv2,pv23,pv38713], .c 11, .c 3, .c 5, .c 7, .c 3, .c 193, .c 19, .c 3,
  .p pv3 [pv2,pv111301], .c 233, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv7,pv63601], .c 13, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv148403], .c 3, .c 401, .c 461, .c 3, .c 37, .c 7, .c 3, .c 53, .c 5,
  .c 3, .c 181, .c 29, .c 3, .c 5, .c 11, .c 3, .c 179, .p pv5 [pv2,pv3,pv74203], .c 3, .c 7,
  .p pv11 [pv2,pv3,pv11,pv223], .c 3, .c 13, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 79, .c 3,
  .p pv2 [pv2,pv5,pv11,pv1619], .c 17, .c 3, .c 307, .c 13, .c 3, .c 23, .c 5, .c 3, .c 7, .c 37,
  .c 3, .c 5, .c 19, .c 3, .c 43, .c 7, .c 3, .c 17, .p pv2 [pv2,pv3,pv163,pv607], .c 3,
  .p pv5 [pv2,pv397,pv2243], .c 5, .c 3, .c 571, .c 109, .c 3, .c 5, .p pv2 [pv2,pv3,pv61,pv811],
  .c 3, .c 7, .c 719, .c 3, .p pv5 [pv2,pv11,pv80953], .p pv41 [pv2,pv3,pv7,pv10601], .c 3,
  .c 103, .c 5, .c 3, .c 89, .c 31, .c 3, .c 5, .c 13, .c 3, .c 509, .c 113,
]
private theorem h0217c12 : checkBlock 1780739 128 b0217c12 = true := by
  decide +kernel

private def b0217c13 : List Row := [
  .c 3, .c 149, .c 11, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv157,pv709], .c 883, .c 3, .c 5, .c 7,
  .c 3, .c 11, .c 439, .c 3, .p pv2 [pv2,pv13,pv68501], .p pv2 [pv2,pv3,pv23,pv239], .c 3, .c 59,
  .c 5, .c 3, .c 13, .c 19, .c 3, .c 5, .p pv5 [pv2,pv3,pv98947], .c 3, .c 23,
  .p pv29 [pv2,pv3,pv7,pv13,pv233], .c 3, .p pv3 [pv2,pv17,pv1637], .c 7, .c 3,
  .p pv5 [pv2,pv890531], .c 5, .c 3, .c 37, .c 977, .c 3, .c 5, .c 197, .c 3, .c 41, .c 1201,
  .c 3, .c 7, .p pv11 [pv2,pv3,pv18553], .c 3, .c 29, .c 5, .c 3, .p pv2 [pv2,pv11,pv19,pv4261],
  .c 7, .c 3, .c 5, .c 17, .c 3, .c 331, .p pv5 [pv2,pv3,pv47,pv1579], .c 3, .c 13,
  .p pv3 [pv2,pv3,pv53,pv1867], .c 3, .c 503, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 137, .c 3,
  .c 17, .c 7, .c 3, .c 293, .c 1193, .c 3, .c 11, .c 5, .c 3, .c 47, .c 463, .c 3, .c 5, .c 31,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv49477], .c 3, .c 71, .c 103, .c 3, .c 449, .c 5, .c 3, .c 23,
  .c 647, .c 3, .c 5, .c 11, .c 3, .c 1303, .p pv2 [pv2,pv3,pv283,pv1049], .c 3, .c 131, .c 17,
  .c 3, .c 7, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 7, .c 3, .c 19,
  .p pv7 [pv2,pv3,pv43,pv863], .c 3, .c 937, .p pv11 [pv2,pv3,pv29,pv353], .c 3, .c 17, .c 5,
  .c 3, .c 199,
]
private theorem h0217c13 : checkBlock 1780995 128 b0217c13 = true := by
  decide +kernel

private def b0217c14 : List Row := [
  .c 421, .c 3, .c 5, .c 1231, .c 3, .c 61, .c 11, .c 3, .c 29, .c 7, .c 3, .c 13, .c 5, .c 3,
  .c 617, .c 23, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv41,pv557], .c 3, .c 31,
  .p pv2 [pv2,pv3,pv79,pv1879], .c 3, .c 7, .c 13, .c 3, .c 443, .c 5, .c 3,
  .p pv2 [pv2,pv97,pv4591], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv49481], .c 3,
  .p pv3 [pv2,pv5,pv44533], .c 431, .c 3, .c 23, .c 11, .c 3, .c 383, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv11,pv2699], .c 3, .c 5, .c 47, .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv445339], .p pv3 [pv2,pv3,pv359,pv827], .c 3, .p pv2 [pv2,pv11,pv17,pv433], .c 5,
  .c 3, .p pv3 [pv2,pv41,pv5431], .c 79, .c 3, .c 5, .c 13, .c 3, .c 7, .c 19, .c 3, .c 59,
  .c 167, .c 3, .p pv3 [pv2,pv111337], .c 5, .c 3, .p pv7 [pv2,pv691,pv1289], .c 479, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv2999], .c 3, .c 137, .c 17, .c 3, .c 11, .c 23, .c 3, .c 7, .c 5, .c 3,
  .c 13, .c 673, .c 3, .c 5, .c 7, .c 3, .c 29, .c 107, .c 3, .c 17,
  .p pv11 [pv2,pv3,pv199,pv373], .c 3, .p pv2 [pv2,pv445363], .c 5, .c 3, .c 19, .c 11, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv296911], .c 3, .c 197, .c 211, .c 3, .c 31, .c 7, .c 3, .c 11, .c 5,
  .c 3, .c 53, .c 41, .c 3, .c 5, .c 19, .c 3, .c 761, .p pv5 [pv2,pv3,pv97,pv3061], .c 3,
]
private theorem h0217c14 : checkBlock 1781251 128 b0217c14 = true := by
  decide +kernel

private def b0217c15 : List Row := [
  .c 7, .p pv2 [pv2,pv3,pv31,pv4789], .c 3, .c 37, .c 5, .c 3, .p pv11 [pv2,pv233,pv3823], .c 7,
  .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv67,pv2659], .c 13, .c 3, .p pv3 [pv2,pv55673], .c 31,
  .c 3, .p pv5 [pv2,pv7,pv53], .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv37,pv107], .c 3, .c 5,
  .c 23, .c 3, .p pv3 [pv2,pv5,pv11,pv4049], .c 7, .c 3, .p pv5 [pv2,pv17,pv61,pv859],
  .p pv7 [pv2,pv3,pv1031], .c 3, .c 19, .c 5, .c 3, .c 547, .p pv2 [pv2,pv3,pv5,pv23,pv1291],
  .c 3, .c 5, .c 37, .c 3, .c 7, .c 11, .c 3, .c 67, .c 97, .c 3, .c 23, .c 5, .c 3,
  .p pv3 [pv2,pv79,pv2819], .c 13, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv229,pv389], .c 59,
  .c 3, .c 61, .c 47, .c 3, .c 7, .c 5, .c 3, .c 997, .p pv37 [pv2,pv3,pv5,pv7,pv101], .c 3, .c 5,
  .c 7, .c 3, .c 17, .p pv2 [pv2,pv3,pv148471], .c 3, .c 107, .c 11, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv17,pv19,pv197], .c 113, .c 3, .c 5, .p pv11 [pv2,pv3,pv13,pv47], .c 3, .c 11,
  .c 127, .c 3, .c 19, .c 7, .c 3, .p pv2 [pv2,pv11,pv40493], .c 5, .c 3,
  .p pv2 [pv2,pv37,pv24077], .c 53, .c 3, .c 5, .p pv3 [pv2,pv3,pv19,pv15629], .c 3, .c 73,
  .c 241, .c 3, .c 7, .c 17, .c 3, .c 47, .c 5, .c 3, .c 739, .c 7, .c 3, .c 5, .c 41, .c 3,
  .c 13, .p pv5 [pv2,pv3,pv149,pv1993], .c 3, .c 11, .c 61, .c 3, .c 17, .c 5, .c 3, .c 7, .c 83,
]
private theorem h0217c15 : checkBlock 1781507 128 b0217c15 = true := by
  decide +kernel

private def b0217c16 : List Row := [
  .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv17,pv47,pv223], .c 7, .c 3, .p pv3 [pv2,pv193,pv577],
  .p pv3 [pv2,pv3,pv41,pv7243], .c 3, .p pv5 [pv2,pv19,pv46889], .c 5, .c 3, .c 29, .c 11, .c 3,
  .c 5, .c 103, .c 3, .c 7, .p pv23 [pv2,pv3,pv11,pv8999], .c 3, .c 53, .c 37, .c 3, .c 11, .c 5,
  .c 3, .c 13, .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv296971], .c 3, .p pv7 [pv2,pv5,pv178183],
  .c 23, .c 3, .p pv2 [pv2,pv7,pv9091], .c 19, .c 3, .c 7, .c 5, .c 3, .c 31,
  .p pv2 [pv2,pv3,pv5,pv7,pv1697], .c 3, .c 5, .c 7, .c 3, .c 523, .p pv3 [pv2,pv3,pv131,pv2267],
  .c 3, .c 1013, .c 89, .c 3, .p pv3 [pv2,pv17,pv6551], .c 5, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv5,pv31,pv479], .c 3, .c 5, .c 71, .c 3, .c 149, .p pv2 [pv2,pv3,pv7,pv2357],
  .c 3, .c 13, .c 7, .c 3, .p pv7 [pv2,pv23,pv38737], .c 5, .c 3, .c 313, .c 31, .c 3, .c 5,
  .c 853, .c 3, .p pv3 [pv2,pv5,pv7,pv37,pv43], .c 11, .c 3, .c 7, .c 499, .c 3, .c 487, .c 5,
  .c 3, .p pv2 [pv2,pv890969], .c 7, .c 3, .c 5, .c 683, .c 3, .c 151, .c 19, .c 3, .c 17, .c 137,
  .c 3, .c 29, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 59, .c 3, .p pv2 [pv2,pv5,pv139,pv641],
  .c 7, .c 3, .c 97, .c 11, .c 3, .c 61, .c 5, .c 3, .c 67, .c 13, .c 3, .c 5, .c 419, .c 3, .c 7,
  .c 409, .c 3, .c 23,
]
private theorem h0217c16 : checkBlock 1781763 128 b0217c16 = true := by
  decide +kernel

private def b0217c17 : List Row := [
  .c 53, .c 3, .c 1069, .c 5, .c 3, .c 19, .c 37, .c 3, .c 5, .c 653, .c 3, .c 109,
  .p pv2 [pv2,pv3,pv17,pv17471], .c 3, .c 89, .c 43, .c 3, .c 7, .c 5, .c 3, .c 17,
  .p pv61 [pv2,pv3,pv5,pv7,pv4243], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv178207], .c 173,
  .c 3, .c 11, .c 13, .c 3, .p pv2 [pv2,pv79,pv11279], .c 5, .c 3, .c 691, .c 571, .c 3, .c 5,
  .c 31, .c 3, .c 619, .p pv3 [pv2,pv3,pv7,pv151,pv281], .c 3, .c 157, .c 7, .c 3,
  .p pv3 [pv2,pv55691], .c 5, .c 3, .c 139, .c 11, .c 3, .c 5, .c 17, .c 3, .c 13, .c 67, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv297023], .c 3, .c 11, .c 5, .c 3, .c 73, .c 7, .c 3, .c 5, .c 13, .c 3,
  .c 17, .c 1109, .c 3, .p pv5 [pv2,pv29,pv30727], .p pv23 [pv2,pv3,pv74257], .c 3,
  .p pv2 [pv2,pv7,pv63649], .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 11, .c 3, .c 127, .c 7, .c 3,
  .p pv2 [pv2,pv13,pv34273], .p pv3 [pv2,pv3,pv11,pv9001], .c 3, .p pv2 [pv2,pv891101], .c 5,
  .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv59407], .c 3, .c 5, .c 233, .c 3, .c 7, .c 239, .c 3, .c 809,
  .c 17, .c 3, .c 137, .c 5, .c 3, .p pv7 [pv2,pv19,pv46901], .p pv7 [pv2,pv3,pv5,pv47,pv79],
  .c 3, .c 5, .c 23, .c 3, .c 1049, .c 11, .c 3, .c 19, .c 83, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv445567], .p pv3 [pv2,pv3,pv5,pv7,pv23,pv41], .c 3,
]
private theorem h0217c17 : checkBlock 1782019 128 b0217c17 = true := by
  decide +kernel

private def b0217c18 : List Row := [
  .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv17,pv2621], .c 31, .c 3, .c 13, .p pv7 [pv2,pv3,pv12377],
  .c 3, .c 23, .c 5, .c 3, .c 107, .p pv43 [pv2,pv3,pv5,pv13,pv457], .c 3, .c 5, .c 43, .c 3,
  .c 29, .c 13, .c 3, .c 211, .c 7, .c 3, .c 1249, .c 5, .c 3, .p pv3 [pv2,pv222791], .c 17, .c 3,
  .c 5, .c 53, .c 3, .c 11, .c 349, .c 3, .c 7, .c 113, .c 3, .c 577, .c 5, .c 3, .c 61, .c 7,
  .c 3, .c 5, .c 271, .c 3, .c 19, .p pv5 [pv2,pv3,pv148531], .c 3, .p pv3 [pv2,pv31,pv7187],
  .p pv7 [pv2,pv3,pv13,pv2539], .c 3, .c 281, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 139, .c 3,
  .c 37, .c 7, .c 3, .c 11, .c 19, .c 3, .p pv2 [pv2,pv191,pv2333], .c 5, .c 3, .c 173, .c 157,
  .c 3, .c 5, .c 29, .c 3, .c 7, .c 17, .c 3, .c 379, .c 223, .c 3, .c 13, .c 5, .c 3, .c 59,
  .c 11, .c 3, .c 5, .c 743, .c 3, .p pv2 [pv2,pv5,pv89123], .p pv3 [pv2,pv3,pv11,pv113,pv239],
  .c 3, .c 17, .c 13, .c 3, .c 7, .c 5, .c 3, .c 43, .c 61, .c 3, .c 5, .c 7, .c 3, .c 317,
  .p pv7 [pv2,pv3,pv89,pv1669], .c 3, .p pv3 [pv2,pv53,pv1051], .p pv2 [pv2,pv3,pv297083], .c 3,
  .p pv5 [pv2,pv891251], .c 5, .c 3, .p pv2 [pv2,pv7,pv13,pv59,pv83],
  .p pv3 [pv2,pv3,pv5,pv59417], .c 3, .c 5, .c 11, .c 3, .c 13, .c 19, .c 3,
  .p pv5 [pv2,pv71,pv12553], .c 7,
]
private theorem h0217c18 : checkBlock 1782275 128 b0217c18 = true := by
  decide +kernel

private def b0217c19 : List Row := [
  .c 3, .p pv2 [pv2,pv445633], .c 5, .c 3, .c 11, .c 677, .c 3, .c 5, .c 13, .c 3,
  .p pv7 [pv2,pv5,pv7,pv11,pv463], .p pv5 [pv2,pv3,pv17,pv257], .c 3, .c 7,
  .p pv3 [pv2,pv3,pv167,pv593], .c 3, .p pv2 [pv2,pv31,pv28751], .c 5, .c 3, .c 17, .c 7, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv12379], .c 3, .c 89, .c 11, .c 3, .c 73, .p pv2 [pv2,pv3,pv148549],
  .c 3, .c 31, .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv42443], .c 3,
  .p pv2 [pv2,pv5,pv178261], .c 7, .c 3, .c 283, .p pv2 [pv2,pv3,pv19,pv823], .c 3, .c 37, .c 5,
  .c 3, .p pv2 [pv2,pv445657], .c 227, .c 3, .c 5, .c 17, .c 3, .c 7, .c 701, .c 3,
  .p pv5 [pv2,pv891323], .c 11, .c 3, .c 197, .c 5, .c 3, .c 29, .c 23, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv97,pv1021], .c 3, .c 11, .c 547, .c 3, .c 13, .p pv13 [pv2,pv3,pv297113],
  .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv17,pv29,pv113], .c 1129, .c 3, .c 5, .c 7, .c 3, .c 239,
  .c 13, .c 3, .c 23, .p pv7 [pv2,pv3,pv53,pv2803], .c 3, .c 19, .c 5, .c 3, .c 587, .c 41, .c 3,
  .c 5, .c 107, .c 3, .c 163, .c 73, .c 3, .c 11, .c 7, .c 3, .p pv5 [pv2,pv13,pv68567], .c 5,
  .c 3, .c 307, .c 19, .c 3, .c 5, .c 47, .c 3, .c 53, .c 97, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv13,pv2857], .c 3, .c 17, .c 5, .c 3, .c 31, .c 7, .c 3, .c 5,
]
private theorem h0217c19 : checkBlock 1782531 128 b0217c19 = true := by
  decide +kernel

private def b0217c20 : List Row := [
  .c 389, .c 3, .p pv37 [pv2,pv5,pv17,pv10487], .c 79, .c 3, .p pv2 [pv2,pv445699], .c 23, .c 3,
  .c 11, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv31,pv71], .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv379],
  .c 3, .c 491, .c 7, .c 3, .c 19, .p pv7 [pv2,pv3,pv49523], .c 3, .c 13, .c 5, .c 3,
  .p pv7 [pv2,pv479,pv1861], .c 17, .c 3, .c 5, .c 11, .c 3, .c 7, .c 251, .c 3, .c 151, .c 13,
  .c 3, .p pv5 [pv2,pv29,pv59,pv521], .c 5, .c 3, .c 11, .c 1291, .c 3, .c 5, .c 263, .c 3, .c 71,
  .p pv2 [pv2,pv3,pv37,pv2677], .c 3, .p pv5 [pv2,pv7,pv347,pv367], .c 797, .c 3, .c 7, .c 5,
  .c 3, .c 1151, .p pv11 [pv2,pv3,pv5,pv7,pv283], .c 3, .c 5, .c 7, .c 3, .c 13, .c 11, .c 3,
  .p pv2 [pv2,pv233,pv1913], .c 37, .c 3, .c 83, .c 5, .c 3, .p pv3 [pv2,pv7,pv15919],
  .p pv2 [pv2,pv3,pv5,pv103,pv577], .c 3, .c 5, .c 13, .c 3, .c 19, .c 17, .c 3,
  .p pv2 [pv2,pv11,pv81043], .c 7, .c 3, .c 101, .c 5, .c 3, .p pv29 [pv2,pv863,pv1033],
  .p pv7 [pv2,pv3,pv5,pv17,pv19,pv23], .c 3, .c 5, .c 41, .c 3, .p pv2 [pv2,pv5,pv7,pv25471],
  .c 53, .c 3, .c 7, .c 11, .c 3, .c 23, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv31,pv4793], .c 3, .c 11, .c 353, .c 3, .c 29, .p pv11 [pv2,pv3,pv41,pv151],
  .c 3, .c 463, .c 5, .c 3, .c 7, .c 563, .c 3, .c 5, .c 31, .c 3, .c 181, .c 7, .c 3,
  .p pv2 [pv2,pv19,pv29,pv809], .c 47, .c 3,
]
private theorem h0217c20 : checkBlock 1782787 128 b0217c20 = true := by
  decide +kernel

private def b0217c21 : List Row := [
  .p pv2 [pv2,pv891521], .c 5, .c 3, .c 41, .p pv7 [pv2,pv3,pv5,pv11887], .c 3, .c 5, .c 163,
  .c 3, .c 7, .c 953, .c 3, .c 11, .p pv2 [pv2,pv3,pv7,pv21227], .c 3, .p pv3 [pv2,pv55721], .c 5,
  .c 3, .c 17, .c 43, .c 3, .c 5, .p pv3 [pv2,pv3,pv47,pv6323], .c 3, .c 61, .c 13, .c 3, .c 331,
  .p pv2 [pv2,pv3,pv23,pv59,pv73], .c 3, .c 7, .c 5, .c 3, .c 79, .c 11, .c 3, .c 5, .c 7, .c 3,
  .c 23, .c 29, .c 3, .c 193, .p pv11 [pv2,pv3,pv74297], .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv67,pv1901], .c 37, .c 3, .c 5, .c 17, .c 3, .c 31, .c 359, .c 3, .c 59, .c 7,
  .c 3, .p pv2 [pv2,pv907,pv983], .c 5, .c 3, .c 19, .c 13, .c 3, .c 5, .c 11, .c 3, .c 17,
  .c 283, .c 3, .c 7, .p pv2 [pv2,pv3,pv11,pv19,pv79], .c 3, .p pv3 [pv2,pv137,pv1627], .c 5,
  .c 3, .c 11, .c 7, .c 3, .c 5, .c 19, .c 3, .p pv11 [pv2,pv5,pv11,pv13,pv29,pv43], .c 23, .c 3,
  .c 613, .p pv3 [pv2,pv3,pv439,pv677], .c 3, .c 13, .c 5, .c 3, .c 7, .c 139, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv13,pv23,pv71], .c 3, .p pv3 [pv2,pv5,pv109,pv409], .c 7, .c 3, .c 401,
  .c 13, .c 3, .c 43, .c 5, .c 3, .c 23, .p pv2 [pv2,pv3,pv5,pv9907], .c 3, .c 5, .c 79, .c 3,
  .c 7, .p pv11 [pv2,pv3,pv67,pv1109], .c 3, .p pv2 [pv2,pv11,pv40529], .c 1229, .c 3, .c 17,
  .c 5, .c 3, .c 37, .c 53, .c 3, .c 5, .c 29,
]
private theorem h0217c21 : checkBlock 1783043 128 b0217c21 = true := by
  decide +kernel

private def b0217c22 : List Row := [
  .c 3, .c 13, .c 131, .c 3, .c 71, .c 11, .c 3, .c 7, .c 5, .c 3, .p pv13 [pv2,pv891659], .c 19,
  .c 3, .c 5, .c 7, .c 3, .c 11, .p pv5 [pv2,pv3,pv49537], .c 3, .c 31, .c 43, .c 3, .c 653, .c 5,
  .c 3, .c 109, .c 17, .c 3, .c 5, .c 101, .c 3, .p pv3 [pv2,pv5,pv5573], .c 37, .c 3, .c 191,
  .c 7, .c 3, .p pv2 [pv2,pv211,pv2113], .c 5, .c 3, .c 13, .c 149, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv9007], .c 3, .p pv17 [pv2,pv5,pv7,pv73,pv349], .c 59, .c 3, .c 7, .c 31,
  .c 3, .c 263, .c 5, .c 3, .p pv3 [pv2,pv11,pv10133], .c 7, .c 3, .c 5, .c 857, .c 3, .c 83,
  .p pv3 [pv2,pv3,pv99079], .c 3, .p pv2 [pv2,pv499,pv1787], .p pv11 [pv2,pv3,pv331,pv449], .c 3,
  .c 1171, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv42463], .c 3, .c 271, .c 7,
  .c 3, .c 13, .c 41, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv43,pv10369], .c 29, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv107,pv463], .c 3, .c 7, .c 13, .c 3, .c 17, .c 23, .c 3,
  .p pv2 [pv2,pv19,pv31,pv757], .c 5, .c 3, .p pv2 [pv2,pv891749], .p pv2 [pv2,pv3,pv5,pv29,pv41],
  .c 3, .c 5, .c 11, .c 3, .c 19, .c 193, .c 3, .p pv2 [pv2,pv7,pv63697],
  .p pv3 [pv2,pv3,pv11,pv61,pv443], .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv7,pv19,pv149], .c 3, .c 5, .c 7, .c 3, .c 41, .p pv3 [pv2,pv3,pv297257],
  .c 3, .c 1051, .c 19, .c 3, .p pv3 [pv2,pv6967],
]
private theorem h0217c22 : checkBlock 1783299 128 b0217c22 = true := by
  decide +kernel

private def b0217c23 : List Row := [
  .c 5, .c 3, .c 101, .c 13, .c 3, .c 5, .c 109, .c 3, .p pv2 [pv2,pv5,pv59,pv3023], .c 11, .c 3,
  .p pv3 [pv2,pv222947], .c 7, .c 3, .c 79, .c 5, .c 3, .c 17, .c 71, .c 3, .c 5, .c 43, .c 3,
  .p pv11 [pv2,pv5,pv7,pv13], .c 47, .c 3, .c 7, .c 53, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv891809], .c 7, .c 3, .c 5, .c 23, .c 3, .c 383, .c 997, .c 3, .c 199, .c 11, .c 3,
  .p pv7 [pv2,pv7,pv127403], .c 5, .c 3, .c 7, .c 103, .c 3, .c 5, .c 17, .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv263,pv3391], .p pv2 [pv2,pv3,pv148639], .c 3, .c 23, .c 5, .c 3, .c 149, .c 229,
  .c 3, .c 5, .c 1021, .c 3, .c 7, .p pv5 [pv2,pv3,pv49547], .c 3, .c 47,
  .p pv3 [pv2,pv3,pv7,pv6067], .c 3, .c 29, .c 5, .c 3, .c 31, .p pv3 [pv2,pv3,pv5,pv19819], .c 3,
  .c 5, .c 13, .c 3, .c 397, .p pv3 [pv2,pv3,pv271,pv1097], .c 3, .c 11, .p pv7 [pv2,pv3,pv4129],
  .c 3, .c 7, .c 5, .c 3, .c 19, .c 67, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv1427], .c 83,
  .c 3, .c 887, .c 17, .c 3, .c 151, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 19, .c 3,
  .p pv3 [pv2,pv5,pv89189], .p pv11 [pv2,pv3,pv7,pv11,pv13], .c 3, .c 41, .c 7, .c 3, .c 11, .c 5,
  .c 3, .p pv17 [pv2,pv891899], .p pv7 [pv2,pv3,pv5,pv991], .c 3, .c 5, .c 37, .c 3,
]
private theorem h0217c23 : checkBlock 1783555 128 b0217c23 = true := by
  decide +kernel

private def b0217c24 : List Row := [
  .c 23, .p pv2 [pv2,pv3,pv43,pv3457], .c 3, .c 7, .c 29, .c 3, .c 61, .c 5, .c 3,
  .p pv2 [pv2,pv41,pv73,pv149], .c 7, .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv11149],
  .p pv2 [pv2,pv3,pv127,pv2341], .c 3, .c 13, .c 1117, .c 3, .c 19, .c 5, .c 3, .c 7, .c 17, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv7,pv42473], .c 3, .c 359, .c 7, .c 3, .c 29,
  .p pv13 [pv2,pv3,pv17,pv17489], .c 3, .p pv2 [pv2,pv241,pv3701], .c 5, .c 3,
  .p pv3 [pv2,pv111493], .c 19, .c 3, .c 5, .p pv5 [pv2,pv3,pv239,pv311], .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv29,pv30757], .c 431, .c 3, .c 659, .c 5, .c 3, .c 83, .p pv7 [pv2,pv3,pv5,pv7433],
  .c 3, .c 5, .c 53, .c 3, .c 113, .p pv2 [pv2,pv3,pv47,pv3163], .c 3,
  .p pv3 [pv2,pv7,pv11,pv181], .c 463, .c 3, .c 7, .c 5, .c 3, .c 23, .c 13, .c 3, .c 5, .c 7,
  .c 3, .c 443, .c 17, .c 3, .c 19, .c 11, .c 3, .c 607, .c 5, .c 3, .c 47,
  .p pv7 [pv2,pv3,pv5,pv11,pv17,pv53], .c 3, .c 5, .c 367, .c 3, .c 11, .c 29, .c 3, .c 17, .c 7,
  .c 3, .c 13, .c 5, .c 3, .c 67, .c 107, .c 3, .c 5, .c 71, .c 3, .p pv2 [pv2,pv5,pv7,pv12743],
  .p pv3 [pv2,pv3,pv29,pv10253], .c 3, .c 7, .c 13, .c 3, .c 41, .c 5, .c 3, .c 661, .c 7, .c 3,
  .c 5, .c 73, .c 3, .c 29, .p pv2 [pv2,pv3,pv16519], .c 3, .c 11, .c 373, .c 3, .c 103, .c 5,
]
private theorem h0217c24 : checkBlock 1783811 128 b0217c24 = true := by
  decide +kernel

private def b0217c25 : List Row := [
  .c 3, .c 7, .c 557, .c 3, .c 5, .c 293, .c 3, .c 13, .c 7, .c 3, .c 23, .c 131, .c 3, .c 179,
  .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .c 13, .c 3, .c 7, .c 43, .c 3, .c 181, .c 19, .c 3,
  .c 11, .c 5, .c 3, .c 787, .c 191, .c 3, .c 5, .p pv5 [pv2,pv3,pv79,pv941], .c 3, .c 503, .c 31,
  .c 3, .c 563, .c 173, .c 3, .c 7, .c 5, .c 3, .c 13, .c 1069, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv178417], .p pv5 [pv2,pv3,pv13,pv11437], .c 3, .c 37, .c 23, .c 3, .c 89, .c 5,
  .c 3, .c 11, .p pv23 [pv2,pv3,pv5,pv59473], .c 3, .c 5, .c 41, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv7,pv23,pv1847], .c 3, .c 311, .c 7, .c 3, .p pv2 [pv2,pv446053], .c 5, .c 3,
  .c 59, .c 109, .c 3, .c 5, .p pv3 [pv2,pv3,pv297371], .c 3, .p pv7 [pv2,pv5,pv7,pv71,pv359],
  .c 11, .c 3, .c 7, .p pv3 [pv2,pv3,pv41,pv7253], .c 3, .p pv2 [pv2,pv43,pv20747], .c 5, .c 3,
  .c 757, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv9293], .c 3, .c 47, .c 13, .c 3, .c 31, .c 17, .c 3,
  .p pv3 [pv2,pv7,pv89,pv179], .c 5, .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv14869], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv17], .c 3, .p pv2 [pv2,pv5,pv19,pv9391], .c 7, .c 3,
  .p pv3 [pv2,pv223037], .c 11, .c 3, .c 17, .c 5, .c 3, .c 19, .c 61, .c 3, .c 5, .c 23, .c 3,
  .c 7,
]
private theorem h0217c25 : checkBlock 1784067 128 b0217c25 = true := by
  decide +kernel

private def b0217c26 : List Row := [
  .c 1213, .c 3, .p pv5 [pv2,pv449,pv1987], .c 31, .c 3, .p pv2 [pv2,pv11,pv107,pv379], .c 5,
  .c 3, .c 73, .c 13, .c 3, .c 5, .c 19, .c 3, .c 53, .p pv29 [pv2,pv3,pv18587], .c 3, .c 1223,
  .c 251, .c 3, .c 7, .c 5, .c 3, .c 601, .c 17, .c 3, .c 5, .c 7, .c 3, .c 1109, .c 113, .c 3,
  .c 11, .p pv2 [pv2,pv3,pv17,pv8747], .c 3, .c 13, .c 5, .c 3, .c 29,
  .p pv7 [pv2,pv3,pv5,pv1487], .c 3, .c 5, .c 467, .c 3, .c 67, .c 313, .c 3, .c 83, .c 7, .c 3,
  .c 19, .c 5, .c 3, .p pv2 [pv2,pv29,pv15383], .c 11, .c 3, .c 5, .c 349, .c 3,
  .p pv3 [pv2,pv5,pv7,pv6373], .c 41, .c 3, .c 7, .c 47, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv68633], .c 7, .c 3, .c 5, .c 409, .c 3, .c 13, .c 17, .c 3, .c 127, .c 181,
  .c 3, .c 797, .c 5, .c 3, .c 7, .c 1181, .c 3, .c 5, .c 11, .c 3, .c 23, .c 7, .c 3, .c 17,
  .c 97, .c 3, .c 191, .c 5, .c 3, .c 11, .c 419, .c 3, .c 5, .p pv3 [pv2,pv3,pv297421], .c 3,
  .c 7, .p pv29 [pv2,pv3,pv148711], .c 3, .c 19, .c 89, .c 3, .c 43, .c 5, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv5,pv11897], .c 3, .c 5, .p pv2 [pv2,pv3,pv19,pv2609], .c 3,
  .p pv3 [pv2,pv5,pv22307], .c 11, .c 3, .p pv5 [pv2,pv7,pv41,pv3109], .c 101, .c 3, .c 7, .c 5,
  .c 3,
]
private theorem h0217c26 : checkBlock 1784323 128 b0217c26 = true := by
  decide +kernel

private def b0217c27 : List Row := [
  .p pv2 [pv2,pv103,pv8663], .p pv13 [pv2,pv3,pv5,pv7,pv607], .c 3, .c 5, .c 7, .c 3, .c 307,
  .c 23, .c 3, .c 229, .p pv3 [pv2,pv3,pv283,pv1051], .c 3, .p pv2 [pv2,pv29,pv1061], .c 5, .c 3,
  .c 17, .p pv2 [pv2,pv3,pv5,pv79,pv251], .c 3, .c 5, .p pv29 [pv2,pv3,pv23,pv53,pv61], .c 3,
  .c 37, .c 197, .c 3, .c 13, .c 7, .c 3, .p pv3 [pv2,pv19,pv59,pv199], .c 5, .c 3, .c 23,
  .p pv7 [pv2,pv3,pv5,pv11,pv13], .c 3, .c 5, .p pv3 [pv2,pv3,pv33049], .c 3, .c 11, .c 13, .c 3,
  .c 7, .p pv31 [pv2,pv3,pv37,pv8039], .c 3, .c 293, .c 5, .c 3, .c 53, .c 7, .c 3, .c 5, .c 17,
  .c 3, .c 103, .p pv2 [pv2,pv3,pv99149], .c 3, .c 163, .c 19, .c 3, .p pv2 [pv2,pv7,pv13,pv4903],
  .c 5, .c 3, .c 7, .c 31, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv11,pv3863], .c 3, .c 17, .c 7, .c 3,
  .c 11, .p pv3 [pv2,pv3,pv13,pv29,pv263], .c 3, .p pv2 [pv2,pv53,pv113,pv149], .c 5, .c 3,
  .c 167, .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv6197], .c 3, .c 7, .p pv3 [pv2,pv3,pv297457], .c 3,
  .c 29, .c 83, .c 3, .p pv3 [pv2,pv331,pv337], .c 5, .c 3, .c 541, .c 11, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv109,pv2729], .c 3, .c 41, .p pv5 [pv2,pv3,pv11,pv4507], .c 3, .c 23, .c 17,
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv446197], .c 991, .c 3, .c 5, .c 7, .c 3, .c 43, .c 19,
  .c 3, .p pv5 [pv2,pv37,pv89,pv271], .c 13, .c 3, .c 17, .c 5, .c 3, .c 1097, .c 1249, .c 3,
  .c 5, .c 11, .c 3, .c 199, .p pv43 [pv2,pv3,pv7,pv83],
]
private theorem h0217c27 : checkBlock 1784579 128 b0217c27 = true := by
  decide +kernel

private def b0217c28 : List Row := [
  .c 3, .c 829, .c 7, .c 3, .c 37, .c 5, .c 3, .c 11, .c 401, .c 3, .c 5, .c 773, .c 3, .c 13,
  .c 29, .c 3, .c 7, .c 23, .c 3, .p pv3 [pv2,pv47,pv101], .c 5, .c 3, .c 19, .c 7, .c 3, .c 5,
  .c 13, .c 3, .p pv2 [pv2,pv5,pv178489], .c 11, .c 3, .c 97, .c 139, .c 3,
  .p pv5 [pv2,pv7,pv127493], .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv59497], .c 3, .c 5, .c 19,
  .c 3, .c 29, .c 7, .c 3, .c 59, .p pv17 [pv2,pv3,pv18593], .c 3, .c 157, .c 5, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv5,pv71,pv419], .c 3, .c 5, .c 67, .c 3, .c 7, .c 569, .c 3,
  .p pv2 [pv2,pv293,pv1523], .c 11, .c 3, .p pv2 [pv2,pv892481], .c 5, .c 3, .c 953, .c 151, .c 3,
  .c 5, .p pv7 [pv2,pv3,pv41,pv907], .c 3, .c 11, .c 17, .c 3, .c 53,
  .p pv2 [pv2,pv3,pv179,pv277], .c 3, .c 7, .c 5, .c 3, .c 523, .p pv23 [pv2,pv3,pv5,pv7,pv17],
  .c 3, .c 5, .c 7, .c 3, .c 31, .c 47, .c 3, .c 13, .p pv2 [pv2,pv3,pv297503], .c 3,
  .p pv5 [pv2,pv181,pv4931], .c 5, .c 3, .p pv3 [pv2,pv7,pv37,pv1723], .c 19, .c 3, .c 5, .c 29,
  .c 3, .p pv3 [pv2,pv5,pv53,pv421], .c 13, .c 3, .c 11, .c 7, .c 3, .c 23, .c 5, .c 3, .c 43,
  .c 113, .c 3, .c 5, .c 587, .c 3, .p pv13 [pv2,pv5,pv7,pv3643], .c 31, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv3673], .c 3, .c 331, .c 5, .c 3, .c 337,
]
private theorem h0217c28 : checkBlock 1784835 128 b0217c28 = true := by
  decide +kernel

private def b0217c29 : List Row := [
  .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv24793], .c 3, .p pv2 [pv2,pv5,pv17851],
  .p pv11 [pv2,pv3,pv11,pv17,pv37,pv43], .c 3, .c 19, .p pv2 [pv2,pv3,pv13,pv11443], .c 3, .c 11,
  .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 751, .c 3, .c 857, .c 7, .c 3, .c 131, .c 37, .c 3,
  .p pv5 [pv2,pv73,pv12227], .c 5, .c 3, .p pv2 [pv2,pv67,pv6661], .p pv3 [pv2,pv3,pv5,pv3967],
  .c 3, .c 5, .c 11, .c 3, .c 7, .c 59, .c 3, .c 179, .c 149, .c 3, .c 13, .c 5, .c 3, .c 11,
  .c 41, .c 3, .c 5, .c 17, .c 3, .c 23, .c 281, .c 3, .c 31, .c 13, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv223151], .c 29, .c 3, .c 5, .c 7, .c 3, .c 17, .c 11, .c 3,
  .p pv2 [pv2,pv61,pv14633], .c 199, .c 3, .c 479, .c 5, .c 3, .c 127,
  .p pv11 [pv2,pv3,pv5,pv19,pv29], .c 3, .c 5, .c 83, .c 3, .c 13,
  .p pv5 [pv2,pv3,pv7,pv53,pv401], .c 3, .p pv3 [pv2,pv11,pv20287], .c 7, .c 3, .c 41, .c 5, .c 3,
  .c 29, .c 211, .c 3, .c 5, .c 13, .c 3, .c 59, .c 23, .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv446323], .c 5, .c 3, .c 103, .c 7, .c 3, .c 5, .c 359, .c 3, .c 11,
  .p pv5 [pv2,pv3,pv6199], .c 3, .c 43, .p pv3 [pv2,pv3,pv149,pv1997], .c 3, .c 17, .c 5, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv5,pv83,pv239], .c 3, .c 5, .p pv13 [pv2,pv3,pv7,pv10627], .c 3, .c 467,
  .c 7, .c 3,
]
private theorem h0217c29 : checkBlock 1785091 128 b0217c29 = true := by
  decide +kernel

private def b0217c30 : List Row := [
  .p pv2 [pv2,pv179,pv4987], .c 67, .c 3, .c 269, .c 5, .c 3, .c 419, .c 37, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv71,pv127], .c 3, .c 7, .c 19, .c 3, .c 11, .c 257, .c 3, .c 31, .c 5,
  .c 3, .c 47, .c 17, .c 3, .c 5, .c 167, .c 3, .p pv3 [pv2,pv5,pv79,pv113], .c 43, .c 3, .c 13,
  .c 61, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv892709], .c 11, .c 3, .c 5, .c 7, .c 3,
  .p pv17 [pv2,pv5,pv19,pv9397], .c 13, .c 3, .c 71, .p pv3 [pv2,pv3,pv99191], .c 3, .c 11, .c 5,
  .c 3, .c 19, .c 311, .c 3, .c 5, .p pv13 [pv2,pv3,pv4133], .c 3, .c 421, .c 809, .c 3, .c 23,
  .c 7, .c 3, .p pv3 [pv2,pv13,pv29,pv37], .c 5, .c 3, .c 79, .p pv7 [pv2,pv3,pv5,pv14879], .c 3,
  .c 5, .c 11, .c 3, .p pv7 [pv2,pv5,pv7,pv23,pv1109], .c 17, .c 3, .c 7, .c 457, .c 3,
  .p pv5 [pv2,pv163,pv5477], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 53, .c 3, .c 137, .c 593,
  .c 3, .c 17, .c 109, .c 3, .c 173, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv29759], .c 3, .c 5,
  .c 863, .c 3, .c 373, .c 7, .c 3, .p pv2 [pv2,pv446389], .c 23, .c 3, .c 13, .c 5, .c 3, .c 31,
  .c 601, .c 3, .c 5, .c 47, .c 3, .c 7, .c 37, .c 3, .p pv2 [pv2,pv11,pv81163], .c 13, .c 3,
  .p pv3 [pv2,pv61,pv3659], .c 5, .c 3, .p pv7 [pv2,pv617,pv1447], .c 19,
]
private theorem h0217c30 : checkBlock 1785347 128 b0217c30 = true := by
  decide +kernel

private def b0217c31 : List Row := [
  .c 3, .c 5, .c 89, .c 3, .c 643, .p pv5 [pv2,pv3,pv17,pv8753], .c 3, .c 29, .c 11, .c 3, .c 7,
  .c 5, .c 3, .c 17, .c 31, .c 3, .c 5, .c 7, .c 3, .c 11, .p pv5 [pv2,pv3,pv297607], .c 3,
  .p pv5 [pv2,pv17,pv29,pv1811], .c 1051, .c 3, .c 61, .c 5, .c 3, .c 191, .c 43, .c 3, .c 5,
  .c 13, .c 3, .c 47, .c 41, .c 3, .c 19, .c 7, .c 3, .p pv2 [pv2,pv892841], .c 5, .c 3,
  .p pv3 [pv2,pv223211], .p pv2 [pv2,pv3,pv5,pv19841], .c 3, .c 5, .c 17, .c 3,
  .p pv2 [pv2,pv5,pv7,pv2551], .c 787, .c 3, .c 7, .p pv11 [pv2,pv3,pv49603], .c 3,
  .p pv3 [pv2,pv233,pv479], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv73,pv151],
  .c 3, .c 17, .c 29, .c 3, .c 1229, .c 113, .c 3, .c 23, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .c 1103, .c 3, .p pv3 [pv2,pv5,pv11161], .c 7, .c 3, .c 491, .p pv11 [pv2,pv3,pv37,pv2011],
  .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv419,pv2131], .c 101, .c 3, .c 5, .c 881, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv71,pv131], .c 3, .c 13, .c 17, .c 3, .p pv2 [pv2,pv892901], .c 5, .c 3,
  .c 227, .p pv11 [pv2,pv3,pv5,pv13,pv19,pv241], .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv29,pv3079], .c 13, .c 3, .c 353, .c 19, .c 3, .c 7, .c 5, .c 3, .c 11, .c 541,
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv11,pv17,pv191], .p pv2 [pv2,pv3,pv113,pv439], .c 3,
  .p pv3 [pv2,pv109],
]
private theorem h0217c31 : checkBlock 1785603 128 b0217c31 = true := by
  decide +kernel

def rows0217 : List Row :=
  b0217c00 ++ b0217c01 ++ b0217c02 ++ b0217c03 ++ b0217c04 ++ b0217c05 ++ b0217c06 ++ b0217c07 ++
  b0217c08 ++ b0217c09 ++ b0217c10 ++ b0217c11 ++ b0217c12 ++ b0217c13 ++ b0217c14 ++ b0217c15 ++
  b0217c16 ++ b0217c17 ++ b0217c18 ++ b0217c19 ++ b0217c20 ++ b0217c21 ++ b0217c22 ++ b0217c23 ++
  b0217c24 ++ b0217c25 ++ b0217c26 ++ b0217c27 ++ b0217c28 ++ b0217c29 ++ b0217c30 ++ b0217c31

theorem checked0217 : checkBlock 1777667 4096 rows0217 = true :=
  checkBlock_append h0217c00 (
    checkBlock_append h0217c01 (
    checkBlock_append h0217c02 (
    checkBlock_append h0217c03 (
    checkBlock_append h0217c04 (
    checkBlock_append h0217c05 (
    checkBlock_append h0217c06 (
    checkBlock_append h0217c07 (
    checkBlock_append h0217c08 (
    checkBlock_append h0217c09 (
    checkBlock_append h0217c10 (
    checkBlock_append h0217c11 (
    checkBlock_append h0217c12 (
    checkBlock_append h0217c13 (
    checkBlock_append h0217c14 (
    checkBlock_append h0217c15 (
    checkBlock_append h0217c16 (
    checkBlock_append h0217c17 (
    checkBlock_append h0217c18 (
    checkBlock_append h0217c19 (
    checkBlock_append h0217c20 (
    checkBlock_append h0217c21 (
    checkBlock_append h0217c22 (
    checkBlock_append h0217c23 (
    checkBlock_append h0217c24 (
    checkBlock_append h0217c25 (
    checkBlock_append h0217c26 (
    checkBlock_append h0217c27 (
    checkBlock_append h0217c28 (
    checkBlock_append h0217c29 (
    checkBlock_append h0217c30 (
    h0217c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
