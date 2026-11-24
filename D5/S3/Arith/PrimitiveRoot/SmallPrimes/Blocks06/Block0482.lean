/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks06/Block0482
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks06/Block0482.checked0482
   digest: Kernel proof of checker success on extended consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table035
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table043
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table047
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table053
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table060
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table069
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table082
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table098
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table122
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table157
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table159
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table160
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table161
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table163
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table165
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

private def b0482c00 : List Row := [
  .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv43,pv191], .c 3, .c 5, .c 61, .c 3, .c 83, .c 7, .c 3,
  .c 11, .p pv2 [pv2,pv3,pv79,pv8317], .c 3, .c 13, .c 5, .c 3, .c 23, .c 811, .c 3, .c 5, .c 719,
  .c 3, .c 7, .c 17, .c 3, .p pv5 [pv2,pv1971143], .c 13, .c 3, .p pv2 [pv2,pv23,pv73,pv587],
  .c 5, .c 3, .c 53, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv219017], .c 3,
  .p pv7 [pv2,pv5,pv19,pv20749], .c 37, .c 3, .c 17, .c 1237, .c 3, .c 7, .c 5, .c 3, .c 19,
  .p pv17 [pv2,pv3,pv5,pv7,pv18773], .c 3, .c 5, .c 7, .c 3, .c 13, .c 1889, .c 3, .c 29,
  .p pv13 [pv2,pv3,pv19,pv17291], .c 3, .p pv5 [pv2,pv53,pv4649], .c 5, .c 3,
  .p pv7 [pv2,pv7,pv379,pv743], .c 23, .c 3, .c 5, .c 11, .c 3, .c 97,
  .p pv11 [pv2,pv3,pv7,pv46933], .c 3, .p pv3 [pv2,pv29,pv16993], .c 7, .c 3,
  .p pv5 [pv2,pv1399,pv1409], .c 5, .c 3, .c 11, .c 149, .c 3, .c 5, .p pv2 [pv2,pv3,pv41,pv2671],
  .c 3, .p pv3 [pv2,pv5,pv7,pv11], .p pv3 [pv2,pv3,pv17,pv38651], .c 3, .c 7,
  .p pv17 [pv2,pv3,pv164267], .c 3, .p pv2 [pv2,pv43,pv22921], .c 5, .c 3, .c 13, .c 7, .c 3,
  .c 5, .c 157, .c 3, .c 191, .c 11, .c 3, .c 41, .c 59, .c 3, .c 19, .c 5, .c 3, .c 7, .c 1093,
  .c 3, .c 5, .c 113, .c 3, .c 37, .c 7, .c 3, .p pv2 [pv2,pv11,pv179203],
  .p pv2 [pv2,pv3,pv97,pv1129], .c 3, .c 283, .c 5, .c 3, .p pv7 [pv2,pv41,pv48079], .c 19, .c 3,
  .c 5, .c 17, .c 3,
]
private theorem h0482c00 : checkBlock 3942235 128 b0482c00 = true := by
  decide +kernel

private def b0482c01 : List Row := [
  .c 7, .p pv2 [pv2,pv3,pv29,pv11329], .c 3, .c 13, .c 11, .c 3, .p pv5 [pv2,pv1971251], .c 5,
  .c 3, .p pv2 [pv2,pv271,pv3637], .c 53, .c 3, .c 5, .c 1327, .c 3, .c 11, .c 13, .c 3,
  .p pv5 [pv2,pv7,pv281609], .c 317, .c 3, .c 7, .c 5, .c 3, .c 457, .c 43, .c 3, .c 5, .c 7,
  .c 3, .p pv7 [pv2,pv5,pv29,pv2719], .p pv5 [pv2,pv3,pv61,pv2693], .c 3, .c 19, .c 71, .c 3,
  .c 337, .c 5, .c 3, .p pv3 [pv2,pv7,pv23,pv3061], .p pv2 [pv2,pv3,pv5,pv113,pv1163], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv19,pv131], .c 3, .p pv2 [pv2,pv5,pv31,pv6359], .c 83, .c 3, .c 11, .c 7,
  .c 3, .c 233, .c 5, .c 3, .c 499, .c 13, .c 3, .c 5, .c 397, .c 3, .c 31, .c 61, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv599,pv1097], .c 3, .c 17, .c 5, .c 3, .c 107, .c 7, .c 3, .c 5, .c 23, .c 3,
  .c 577, .p pv2 [pv2,pv3,pv11,pv31,pv41,pv47], .c 3, .p pv5 [pv2,pv37,pv53279], .c 479, .c 3,
  .c 11, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv23,pv2857], .c 3, .c 5, .c 1063, .c 3, .c 19,
  .c 7, .c 3, .p pv2 [pv2,pv929,pv1061], .c 13, .c 3, .c 23, .c 5, .c 3, .c 47, .c 17, .c 3, .c 5,
  .c 11, .c 3, .c 7, .c 167, .c 3, .c 131, .c 19, .c 3, .c 43, .c 5, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv5,pv37], .c 3, .c 5, .p pv3 [pv2,pv3,pv657121], .c 3, .c 13, .c 269, .c 3,
  .c 101, .p pv2 [pv2,pv3,pv219041], .c 3, .c 7, .c 5,
]
private theorem h0482c01 : checkBlock 3942491 128 b0482c01 = true := by
  decide +kernel

private def b0482c02 : List Row := [
  .c 3, .c 67, .p pv19 [pv2,pv3,pv5,pv7,pv751], .c 3, .c 5, .c 7, .c 3, .c 151, .c 11, .c 3,
  .p pv5 [pv2,pv19,pv31,pv3347], .p pv7 [pv2,pv3,pv82141], .c 3, .p pv2 [pv2,pv71,pv13883], .c 5,
  .c 3, .c 271, .p pv47 [pv2,pv3,pv5,pv65713], .c 3, .c 5, .c 199, .c 3, .c 641, .c 17, .c 3,
  .c 31, .c 7, .c 3, .c 73, .c 5, .c 3, .c 13, .c 29, .c 3, .c 5, .c 1361, .c 3, .c 23, .c 19,
  .c 3, .c 7, .c 11, .c 3, .c 179, .c 5, .c 3, .p pv17 [pv2,pv101,pv131,pv149], .c 7, .c 3, .c 5,
  .c 41, .c 3, .c 11, .c 1123, .c 3, .c 61, .c 31, .c 3, .c 223, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv167,pv787], .c 3, .c 5, .c 47, .c 3, .c 467, .c 7, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv41,pv4007], .c 3, .c 1231, .c 5, .c 3, .c 19, .c 293, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv5431], .c 3, .c 7, .c 13, .c 3, .c 11, .p pv3 [pv2,pv3,pv7,pv19,pv61],
  .c 3, .p pv2 [pv2,pv229,pv8609], .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv131431], .c 3, .c 5,
  .c 19, .c 3, .p pv2 [pv2,pv5,pv197147], .c 103, .c 3, .p pv2 [pv2,pv7,pv17,pv16567], .c 73,
  .c 3, .c 7, .c 5, .c 3, .c 23, .c 11, .c 3, .c 5, .c 7, .c 3, .c 43, .c 1663, .c 3,
  .p pv3 [pv2,pv61609], .c 37, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv7,pv53,pv2657], .c 13, .c 3,
  .c 5, .c 17, .c 3, .c 241,
]
private theorem h0482c02 : checkBlock 3942747 128 b0482c02 = true := by
  decide +kernel

private def b0482c03 : List Row := [
  .c 557, .c 3, .p pv5 [pv2,pv1971503], .c 7, .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv47,pv41947],
  .p pv2 [pv2,pv3,pv5,pv65717], .c 3, .c 5, .c 11, .c 3, .c 17, .c 401, .c 3, .c 7, .c 283, .c 3,
  .c 13, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 43, .c 3, .p pv2 [pv2,pv5,pv11,pv17923], .c 151,
  .c 3, .c 1553, .c 13, .c 3, .c 773, .c 5, .c 3, .c 7, .c 83, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv7,pv223,pv421], .c 3, .p pv2 [pv2,pv5,pv37,pv10657], .c 7, .c 3, .c 23,
  .c 17, .c 3, .p pv5 [pv2,pv1021,pv1931], .c 5, .c 3, .p pv2 [pv2,pv13,pv19,pv307],
  .p pv3 [pv2,pv3,pv5,pv131437], .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv379], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv657187], .c 3, .c 19, .p pv13 [pv2,pv3,pv7,pv479], .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv31,pv63599], .c 101, .c 3, .c 5, .c 13, .c 3, .c 67,
  .p pv13 [pv2,pv3,pv139,pv197], .c 3, .c 1279, .c 11, .c 3, .c 7, .c 5, .c 3, .c 31,
  .p pv3 [pv2,pv3,pv5,pv7,pv11,pv569], .c 3, .c 5, .c 7, .c 3, .c 11, .c 193, .c 3,
  .p pv2 [pv2,pv13,pv43,pv3527], .c 23, .c 3, .p pv3 [pv2,pv11,pv44809], .c 5, .c 3, .c 13, .c 17,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv47,pv59,pv79], .c 3, .p pv2 [pv2,pv5,pv251,pv1571], .c 757, .c 3,
  .c 29, .c 7, .c 3, .c 61, .c 5, .c 3, .c 43, .c 31, .c 3, .c 5, .c 337, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv101,pv241], .c 3, .c 7, .p pv11 [pv2,pv3,pv113,pv727], .c 3, .c 47, .c 5,
  .c 3,
]
private theorem h0482c03 : checkBlock 3943003 128 b0482c03 = true := by
  decide +kernel

private def b0482c04 : List Row := [
  .p pv11 [pv2,pv11,pv23,pv7793], .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv181,pv3631], .c 3, .c 107,
  .c 281, .c 3, .c 13, .c 19, .c 3, .p pv2 [pv2,pv7,pv281663], .c 5, .c 3, .c 7, .c 11, .c 3,
  .c 5, .c 1483, .c 3, .p pv2 [pv2,pv5,pv47,pv839], .c 7, .c 3, .p pv2 [pv2,pv53,pv37201], .c 223,
  .c 3, .c 11, .c 5, .c 3, .p pv7 [pv2,pv1971659], .c 271, .c 3, .c 5, .c 23, .c 3, .c 7, .c 29,
  .c 3, .c 17, .c 41, .c 3, .c 101, .c 5, .c 3, .c 37, .c 349, .c 3, .c 5, .c 11, .c 3, .c 113,
  .c 353, .c 3, .p pv5 [pv2,pv7,pv281669], .c 157, .c 3, .c 7, .c 5, .c 3, .c 11, .c 13, .c 3,
  .c 5, .c 7, .c 3, .c 29, .c 19, .c 3, .p pv2 [pv2,pv23,pv42863], .p pv13 [pv2,pv3,pv657233],
  .c 3, .p pv2 [pv2,pv109,pv18089], .c 5, .c 3, .p pv3 [pv2,pv7,pv137,pv257], .c 71, .c 3, .c 5,
  .c 31, .c 3, .c 41, .c 11, .c 3, .p pv2 [pv2,pv967,pv2039], .c 7, .c 3, .c 13, .c 5, .c 3,
  .c 17, .c 47, .c 3, .c 5, .c 181, .c 3, .p pv2 [pv2,pv5,pv7,pv19,pv593], .c 457, .c 3, .c 7,
  .c 13, .c 3, .c 1213, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 127, .c 3,
  .p pv3 [pv2,pv5,pv311,pv317], .c 241, .c 3, .c 43, .c 11, .c 3, .c 131, .c 5, .c 3, .c 7, .c 59,
  .c 3, .c 5, .c 17, .c 3, .c 11, .c 7,
]
private theorem h0482c04 : checkBlock 3943259 128 b0482c04 = true := by
  decide +kernel

private def b0482c05 : List Row := [
  .c 3, .p pv2 [pv2,pv151,pv6529], .c 643, .c 3, .p pv2 [pv2,pv11,pv79,pv2269], .c 5, .c 3,
  .p pv3 [pv2,pv61,pv8081], .p pv2 [pv2,pv3,pv5,pv43,pv1019], .c 3, .c 5, .c 13, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv657257], .c 3, .p pv2 [pv2,pv197,pv10009], .c 179, .c 3, .c 67, .c 5, .c 3,
  .p pv7 [pv2,pv17,pv115987], .c 103, .c 3, .c 5, .c 449, .c 3, .c 37, .c 43, .c 3, .c 11, .c 83,
  .c 3, .c 7, .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv7,pv89,pv211], .c 3, .c 5, .c 7, .c 3,
  .c 79, .c 23, .c 3, .c 479, .c 17, .c 3, .p pv2 [pv2,pv985903], .c 5, .c 3, .c 59, .c 11, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv17,pv23,pv41], .c 3, .p pv17 [pv2,pv5,pv394363],
  .p pv17 [pv2,pv3,pv7,pv11,pv97], .c 3, .p pv2 [pv2,pv907,pv1087], .c 7, .c 3, .c 11, .c 5, .c 3,
  .c 23, .p pv3 [pv2,pv3,pv5,pv61,pv431], .c 3, .c 5, .c 787, .c 3,
  .p pv2 [pv2,pv5,pv7,pv17,pv1657], .p pv3 [pv2,pv3,pv83,pv7919], .c 3, .c 7, .c 859, .c 3,
  .p pv3 [pv2,pv23,pv21433], .c 5, .c 3, .c 73, .c 7, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv394369], .c 13, .c 3, .c 19, .c 107, .c 3, .p pv7 [pv2,pv7,pv43,pv6551], .c 5,
  .c 3, .c 7, .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv19,pv353], .c 3,
  .p pv3 [pv2,pv5,pv11,pv8963], .c 7, .c 3, .c 31, .c 97, .c 3, .c 1163, .c 5, .c 3, .c 29, .c 23,
  .c 3, .c 5, .c 101, .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv37,pv26647], .c 79, .c 3,
  .p pv2 [pv2,pv17,pv193,pv601], .c 5, .c 3, .p pv3 [pv2,pv29,pv89,pv191],
]
private theorem h0482c05 : checkBlock 3943515 128 b0482c05 = true := by
  decide +kernel

private def b0482c06 : List Row := [
  .c 13, .c 3, .c 5, .p pv7 [pv2,pv3,pv41081], .c 3, .c 1399, .c 53, .c 3, .c 23, .c 31, .c 3,
  .c 7, .c 5, .c 3, .p pv13 [pv2,pv397,pv4967], .c 211, .c 3, .c 5, .c 7, .c 3, .c 19, .c 17,
  .c 3, .c 47, .c 11, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv7,pv83,pv1697], .c 41, .c 3, .c 5,
  .c 71, .c 3, .c 11, .p pv3 [pv2,pv3,pv7,pv93901], .c 3, .c 17, .c 7, .c 3,
  .p pv3 [pv2,pv11,pv89633], .c 5, .c 3, .p pv2 [pv2,pv127,pv15527], .c 1229, .c 3, .c 5, .c 37,
  .c 3, .p pv7 [pv2,pv5,pv7,pv103,pv547], .p pv13 [pv2,pv3,pv41,pv167], .c 3, .c 7, .c 23, .c 3,
  .p pv2 [pv2,pv31,pv63611], .c 5, .c 3, .c 53, .c 7, .c 3, .c 5, .c 571, .c 3, .c 13, .c 1481,
  .c 3, .c 11, .c 1787, .c 3, .c 29, .c 5, .c 3, .c 7, .p pv47 [pv2,pv3,pv5,pv16433], .c 3, .c 5,
  .c 13, .c 3, .p pv2 [pv2,pv5,pv394393], .c 7, .c 3, .p pv3 [pv2,pv7703],
  .p pv17 [pv2,pv3,pv657323], .c 3, .c 523, .c 5, .c 3, .c 17, .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv137,pv2399], .c 3, .c 7, .c 19, .c 3, .p pv11 [pv2,pv13,pv17,pv8923], .c 151,
  .c 3, .c 11, .c 5, .c 3, .c 13, .c 199, .c 3, .c 5, .c 409, .c 3, .c 233,
  .p pv5 [pv2,pv3,pv13,pv12641], .c 3, .c 157, .p pv3 [pv2,pv3,pv73037], .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv493001], .p pv3 [pv2,pv3,pv5,pv7,pv2683], .c 3, .c 5, .c 7, .c 3, .c 1879, .c 503,
  .c 3,
]
private theorem h0482c06 : checkBlock 3943771 128 b0482c06 = true := by
  decide +kernel

private def b0482c07 : List Row := [
  .c 1973, .c 29, .c 3, .p pv3 [pv2,pv59,pv2089], .c 5, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv5,pv23,pv1429], .c 3, .c 5, .c 419, .c 3, .c 17, .c 587, .c 3, .c 13, .c 7,
  .c 3, .c 23, .c 5, .c 3, .c 353, .c 389, .c 3, .c 5, .c 19, .c 3, .c 431, .c 11, .c 3, .c 7,
  .c 37, .c 3, .c 137, .c 5, .c 3, .c 31, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv73039], .c 3,
  .c 163, .c 313, .c 3, .c 73, .c 17, .c 3, .c 1021, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv31,pv4241], .c 3, .c 5, .c 197, .c 3, .p pv2 [pv2,pv5,pv197207], .c 7,
  .c 3, .c 1979, .c 11, .c 3, .c 17, .c 5, .c 3, .c 41, .c 13, .c 3, .c 5, .c 709, .c 3, .c 7,
  .p pv17 [pv2,pv3,pv19,pv17299], .c 3, .c 1297, .c 103, .c 3, .p pv5 [pv2,pv11,pv179281], .c 5,
  .c 3, .p pv2 [pv2,pv986047], .c 19, .c 3, .c 5, .c 433, .c 3, .c 23, .c 29, .c 3, .c 53, .c 59,
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv43,pv45863], .c 17, .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv137,pv2879], .c 79, .c 3, .c 11, .c 13, .c 3, .c 83, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv11,pv19,pv337], .p pv2 [pv2,pv3,pv5,pv1753], .c 3, .c 5,
  .p pv13 [pv2,pv3,pv20543], .c 3, .c 29, .c 71, .c 3, .c 19, .c 7, .c 3, .c 733, .c 5, .c 3,
  .c 131, .c 11,
]
private theorem h0482c07 : checkBlock 3944027 128 b0482c07 = true := by
  decide +kernel

private def b0482c08 : List Row := [
  .c 3, .c 5, .c 47, .c 3, .c 13, .c 23, .c 3, .c 7, .c 1439, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv569,pv1733], .c 7, .c 3, .c 5, .c 13, .c 3, .c 61, .c 17, .c 3, .c 59,
  .p pv29 [pv2,pv3,pv149,pv1103], .c 3, .c 359, .c 5, .c 3, .c 7, .c 107, .c 3, .c 5, .c 11, .c 3,
  .p pv11 [pv2,pv5,pv78887], .c 7, .c 3, .c 17, .p pv3 [pv2,pv3,pv11,pv1811], .c 3, .c 601, .c 5,
  .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv131479], .c 3, .c 5, .c 29, .c 3, .c 7, .c 109, .c 3,
  .p pv2 [pv2,pv59,pv33427], .p pv2 [pv2,pv3,pv7,pv46957], .c 3, .c 967, .c 5, .c 3,
  .p pv7 [pv2,pv349,pv5651], .c 1187, .c 3, .c 5, .p pv3 [pv2,pv3,pv29,pv22669], .c 3,
  .p pv2 [pv2,pv5,pv131,pv3011], .c 11, .c 3, .c 547, .c 19, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv47,pv20981], .c 23, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv31,pv3181], .c 61,
  .c 3, .c 13, .p pv13 [pv2,pv3,pv107], .c 3, .c 673, .c 5, .c 3, .c 17,
  .p pv29 [pv2,pv3,pv5,pv13,pv389], .c 3, .c 5, .c 953, .c 3, .c 31, .c 13, .c 3, .c 23, .c 7,
  .c 3, .p pv2 [pv2,pv73,pv27017], .c 5, .c 3, .c 887, .c 67, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv37,pv2221], .c 3, .c 11, .p pv5 [pv2,pv3,pv31,pv7069], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv328709], .c 3, .p pv3 [pv2,pv11,pv13,pv431], .c 5, .c 3, .c 43, .c 7, .c 3,
  .c 5, .c 17, .c 3, .c 197, .c 19, .c 3, .p pv3 [pv2,pv493067],
]
private theorem h0482c08 : checkBlock 3944283 128 b0482c08 = true := by
  decide +kernel

private def b0482c09 : List Row := [
  .p pv2 [pv2,pv3,pv13,pv1873], .c 3, .c 907, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv11,pv1423], .c 3, .c 17, .c 7, .c 3, .c 11, .c 23, .c 3, .c 151, .c 5,
  .c 3, .c 227, .p pv2 [pv2,pv3,pv5,pv29,pv2267], .c 3, .c 5, .c 743, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv23,pv397], .c 3, .p pv2 [pv2,pv986149], .p pv3 [pv2,pv3,pv7,pv13417], .c 3,
  .c 13, .c 5, .c 3, .c 19, .c 11, .c 3, .c 5, .p pv7 [pv2,pv3,pv13,pv47,pv269], .c 3,
  .p pv2 [pv2,pv5,pv127,pv1553], .c 179, .c 3, .p pv2 [pv2,pv7,pv31,pv61,pv149], .c 13, .c 3,
  .c 7, .c 5, .c 3, .c 823, .c 137, .c 3, .c 5, .c 7, .c 3, .c 41, .c 1277, .c 3, .c 31, .c 293,
  .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv7,pv13,pv10837], .p pv11 [pv2,pv3,pv5,pv131489], .c 3,
  .c 5, .c 11, .c 3, .c 13, .p pv2 [pv2,pv3,pv7,pv31307], .c 3, .c 61, .c 7, .c 3, .c 257, .c 5,
  .c 3, .c 11, .c 73, .c 3, .c 5, .c 13, .c 3, .p pv17 [pv2,pv5,pv7,pv11,pv47,pv109], .c 1109,
  .c 3, .c 7, .c 31, .c 3, .c 19, .c 5, .c 3, .p pv3 [pv2,pv197,pv2503], .c 7, .c 3, .c 5, .c 53,
  .c 3, .c 83, .c 11, .c 3, .c 89, .c 467, .c 3, .c 23, .c 5, .c 3, .c 7, .c 19, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv93923], .c 3, .c 857, .c 7, .c 3, .c 43, .c 983, .c 3, .c 29, .c 5, .c 3,
  .p pv2 [pv2,pv986197], .p pv3 [pv2,pv3,pv5,pv53,pv827], .c 3,
]
private theorem h0482c09 : checkBlock 3944539 128 b0482c09 = true := by
  decide +kernel

private def b0482c10 : List Row := [
  .c 5, .c 103, .c 3, .c 7, .c 131, .c 3, .p pv5 [pv2,pv227,pv8689], .c 11, .c 3,
  .p pv2 [pv2,pv29,pv31,pv1097], .c 5, .c 3, .c 109, .p pv7 [pv2,pv3,pv5,pv11,pv43,pv139], .c 3,
  .c 5, .p pv2 [pv2,pv3,pv67,pv3271], .c 3, .c 11, .c 17, .c 3, .c 13, .p pv3 [pv2,pv3,pv657473],
  .c 3, .c 7, .c 5, .c 3, .c 389, .c 47, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv197243], .c 13,
  .c 3, .c 17, .p pv2 [pv2,pv3,pv23,pv14293], .c 3, .p pv3 [pv2,pv493109], .c 5, .c 3, .c 677,
  .p pv7 [pv2,pv3,pv5,pv5479], .c 3, .c 5, .c 619, .c 3, .c 23, .c 67, .c 3, .c 11, .c 7, .c 3,
  .c 37, .c 5, .c 3, .p pv2 [pv2,pv11,pv89657], .p pv3 [pv2,pv3,pv5,pv131497], .c 3, .c 5, .c 59,
  .c 3, .p pv13 [pv2,pv5,pv7,pv73,pv193], .c 233, .c 3, .c 7, .c 241, .c 3,
  .p pv2 [pv2,pv19,pv51907], .c 5, .c 3, .c 157, .c 7, .c 3, .c 5, .c 271, .c 3, .c 19,
  .p pv7 [pv2,pv3,pv11,pv17,pv293], .c 3, .c 29, .c 101, .c 3, .c 11, .c 5, .c 3, .c 7, .c 1867,
  .c 3, .c 5, .c 37, .c 3, .c 179, .c 7, .c 3, .p pv2 [pv2,pv17,pv29,pv4001], .c 19, .c 3, .c 13,
  .c 5, .c 3, .p pv7 [pv2,pv31,pv63629], .c 127, .c 3, .c 5, .c 11, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv521,pv631], .c 3, .p pv3 [pv2,pv493127], .c 13, .c 3, .c 79, .c 5, .c 3,
  .c 11, .p pv3 [pv2,pv3,pv5,pv131501], .c 3, .c 5, .c 17, .c 3, .c 167, .c 347, .c 3,
  .p pv5 [pv2,pv7,pv19,pv14831], .c 1433,
]
private theorem h0482c10 : checkBlock 3944795 128 b0482c10 = true := by
  decide +kernel

private def b0482c11 : List Row := [
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv13,pv151733], .c 41, .c 3, .c 5, .c 7, .c 3, .c 13, .c 11,
  .c 3, .p pv2 [pv2,pv181,pv5449], .p pv3 [pv2,pv3,pv43,pv1699], .c 3, .c 1039, .c 5, .c 3,
  .c 163, .c 31, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv39451], .c 19, .c 3,
  .p pv2 [pv2,pv11,pv103,pv1741], .c 7, .c 3, .c 193, .c 5, .c 3, .p pv17 [pv2,pv881,pv2239],
  .c 23, .c 3, .c 5, .p pv3 [pv2,pv3,pv673,pv977], .c 3, .c 29, .c 47, .c 3, .c 7, .c 11, .c 3,
  .c 41, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv83,pv233], .c 3, .c 11,
  .p pv2 [pv2,pv3,pv13,pv37,pv1367], .c 3, .c 23, .c 113, .c 3, .c 17, .c 5, .c 3, .c 7, .c 79,
  .c 3, .c 5, .c 487, .c 3, .c 421, .c 7, .c 3, .c 107, .c 37, .c 3, .p pv2 [pv2,pv947,pv2083],
  .c 5, .c 3, .c 103, .c 829, .c 3, .c 5, .c 19, .c 3, .c 7, .c 463, .c 3, .c 11, .c 593, .c 3,
  .p pv3 [pv2,pv246577], .c 5, .c 3, .c 83, .c 17, .c 3, .c 5, .c 29, .c 3, .c 1193, .c 13, .c 3,
  .c 71, .c 23, .c 3, .c 7, .c 5, .c 3, .c 1451, .c 11, .c 3, .c 5, .c 7, .c 3, .c 89, .c 383,
  .c 3, .p pv5 [pv2,pv1972643], .c 1049, .c 3, .c 11, .c 5, .c 3, .p pv7 [pv2,pv7,pv281807],
  .p pv7 [pv2,pv3,pv5,pv13151], .c 3, .c 5,
]
private theorem h0482c11 : checkBlock 3945051 128 b0482c11 = true := by
  decide +kernel

private def b0482c12 : List Row := [
  .c 41, .c 3, .c 277, .p pv5 [pv2,pv3,pv7,pv19,pv103], .c 3, .c 1657, .c 7, .c 3,
  .p pv2 [pv2,pv83,pv23767], .c 5, .c 3, .p pv3 [pv2,pv23,pv71,pv151], .c 13, .c 3, .c 5, .c 11,
  .c 3, .p pv19 [pv2,pv5,pv7,pv28181], .c 17, .c 3, .c 7, .p pv2 [pv2,pv3,pv11,pv41], .c 3,
  .p pv3 [pv2,pv493169], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv219187], .c 3,
  .c 149, .c 53, .c 3, .c 17, .c 43, .c 3, .c 13, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv347,pv379], .c 3, .c 5, .c 23, .c 3, .c 31, .c 7, .c 3, .c 19, .c 13,
  .c 3, .p pv2 [pv2,pv239,pv4127], .c 5, .c 3, .c 61, .c 29, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv19,pv53,pv653], .c 3, .c 7, .c 659, .c 3, .c 1759, .c 401, .c 3, .c 23, .c 5,
  .c 3, .p pv11 [pv2,pv13,pv59,pv643], .c 1543, .c 3, .c 5, .p pv7 [pv2,pv3,pv9133], .c 3, .c 13,
  .c 31, .c 3, .p pv2 [pv2,pv7,pv23,pv12253], .c 11, .c 3, .c 7, .c 5, .c 3, .c 17, .c 353, .c 3,
  .c 5, .c 7, .c 3, .c 11, .c 809, .c 3, .c 79, .c 193, .c 3, .c 1619, .c 5, .c 3, .c 47, .c 547,
  .c 3, .c 5, .c 1381, .c 3, .c 19, .c 479, .c 3, .p pv11 [pv2,pv13,pv263,pv577], .c 7, .c 3,
  .c 521, .c 5, .c 3, .c 13, .c 61, .c 3, .c 5, .c 17, .c 3, .c 43, .c 41, .c 3, .c 7, .c 19,
  .c 3,
]
private theorem h0482c12 : checkBlock 3945307 128 b0482c12 = true := by
  decide +kernel

private def b0482c13 : List Row := [
  .c 67, .c 5, .c 3, .c 37, .c 7, .c 3, .c 5, .c 73, .c 3, .c 17, .c 1907, .c 3, .c 31, .c 131,
  .c 3, .c 499, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .p pv23 [pv2,pv3,pv7,pv37,pv2539], .c 3,
  .c 173, .c 7, .c 3, .c 13, .c 181, .c 3, .c 11, .c 5, .c 3, .c 1289,
  .p pv3 [pv2,pv3,pv5,pv13,pv67,pv151], .c 3, .c 5, .c 43, .c 3, .c 7, .c 13, .c 3,
  .p pv5 [pv2,pv1972823], .c 17, .c 3, .c 29, .c 5, .c 3, .p pv2 [pv2,pv1972829],
  .p pv2 [pv2,pv3,pv5,pv65761], .c 3, .c 5, .c 11, .c 3, .p pv7 [pv2,pv5,pv229,pv1723], .c 19,
  .c 3, .p pv2 [pv2,pv7,pv41,pv491], .c 1069, .c 3, .c 7, .c 5, .c 3, .c 11, .c 53, .c 3, .c 5,
  .c 7, .c 3, .p pv2 [pv2,pv5,pv11,pv17,pv211], .p pv3 [pv2,pv3,pv657617], .c 3, .c 937, .c 167,
  .c 3, .c 197, .c 5, .c 3, .c 23, .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv89,pv821], .c 3,
  .p pv2 [pv2,pv5,pv19,pv1093], .c 11, .c 3, .c 83, .c 7, .c 3, .c 59, .c 5, .c 3, .c 19, .c 17,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv328813], .c 3, .p pv11 [pv2,pv5,pv7,pv13,pv271], .c 127, .c 3,
  .c 7, .c 29, .c 3, .c 13, .c 5, .c 3, .c 1783, .c 7, .c 3, .c 5, .c 19, .c 3, .c 37, .c 139,
  .c 3, .c 53, .c 11, .c 3, .p pv5 [pv2,pv7,pv17,pv59,pv281], .c 5, .c 3, .c 7, .c 23, .c 3, .c 5,
  .c 839,
]
private theorem h0482c13 : checkBlock 3945563 128 b0482c13 = true := by
  decide +kernel

private def b0482c14 : List Row := [
  .c 3, .c 11, .c 7, .c 3, .c 29, .c 1559, .c 3, .c 1307, .c 5, .c 3, .c 107,
  .p pv31 [pv2,pv3,pv5,pv41,pv401], .c 3, .c 5, .c 113, .c 3, .c 7, .c 17, .c 3, .c 23, .c 1061,
  .c 3, .c 19, .c 5, .c 3, .c 73, .c 307, .c 3, .c 5, .c 13, .c 3, .c 41,
  .p pv2 [pv2,pv3,pv19,pv34613], .c 3, .c 11, .c 1213, .c 3, .c 7, .c 5, .c 3, .c 229, .c 19,
  .c 3, .c 5, .c 7, .c 3, .c 211, .p pv5 [pv2,pv3,pv164413], .c 3, .p pv3 [pv2,pv13,pv75883],
  .p pv3 [pv2,pv3,pv657653], .c 3, .p pv2 [pv2,pv41,pv48121], .c 5, .c 3, .c 13, .c 11, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv82207], .c 3, .c 227, .c 29, .c 3, .c 797, .c 7, .c 3, .c 11, .c 5,
  .c 3, .c 31, .c 269, .c 3, .c 5, .c 71, .c 3, .c 79, .p pv2 [pv2,pv3,pv17,pv23,pv29], .c 3,
  .c 7, .c 47, .c 3, .p pv5 [pv2,pv131,pv15061], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 11, .c 3,
  .c 29, .c 1753, .c 3, .c 13, .c 53, .c 3, .c 37, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv7,pv47,pv1999], .c 3, .c 271, .c 7, .c 3, .p pv2 [pv2,pv986509],
  .p pv3 [pv2,pv3,pv59,pv71,pv157], .c 3, .c 167, .c 5, .c 3, .c 383,
  .p pv13 [pv2,pv3,pv5,pv37,pv79], .c 3, .c 5, .c 17, .c 3, .c 7, .c 11, .c 3, .c 43, .c 83, .c 3,
  .c 47,
]
private theorem h0482c14 : checkBlock 3945819 128 b0482c14 = true := by
  decide +kernel

private def b0482c15 : List Row := [
  .c 5, .c 3, .c 653, .c 1709, .c 3, .c 5, .c 23, .c 3, .c 17, .c 1523, .c 3, .c 59, .c 67, .c 3,
  .c 7, .c 5, .c 3, .c 71, .c 13, .c 3, .c 5, .c 7, .c 3, .c 1889, .p pv2 [pv2,pv3,pv211,pv1039],
  .c 3, .c 41, .c 11, .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv7,pv281867],
  .p pv2 [pv2,pv3,pv5,pv11,pv1993], .c 3, .c 5, .c 1091, .c 3, .c 11, .c 43, .c 3,
  .p pv2 [pv2,pv23,pv59,pv727], .c 7, .c 3, .c 13, .c 5, .c 3, .c 1811, .c 89, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv17,pv31], .c 3, .c 571, .p pv3 [pv2,pv3,pv331,pv1987], .c 3, .c 7, .c 13,
  .c 3, .c 17, .c 5, .c 3, .c 1009, .c 7, .c 3, .c 5, .c 31, .c 3,
  .p pv2 [pv2,pv5,pv17,pv139,pv167], .p pv2 [pv2,pv3,pv61,pv599], .c 3, .c 11,
  .p pv2 [pv2,pv3,pv657703], .c 3, .p pv5 [pv2,pv7,pv251,pv1123], .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv163,pv269], .c 3, .c 5, .p pv37 [pv2,pv3,pv7,pv109,pv431], .c 3, .c 13,
  .c 7, .c 3, .p pv5 [pv2,pv859,pv2297], .p pv7 [pv2,pv3,pv23,pv2383], .c 3, .c 1721, .c 5, .c 3,
  .p pv2 [pv2,pv1973129], .c 11, .c 3, .c 5, .c 13, .c 3, .c 7, .c 61, .c 3, .c 509, .c 311, .c 3,
  .c 11, .c 5, .c 3, .p pv3 [pv2,pv246643], .c 29, .c 3, .c 5, .p pv71 [pv2,pv3,pv164429], .c 3,
  .c 691, .c 173, .c 3, .c 73, .c 37, .c 3, .c 7, .c 5, .c 3, .c 13, .c 233, .c 3, .c 5, .c 7,
  .c 3,
]
private theorem h0482c15 : checkBlock 3946075 128 b0482c15 = true := by
  decide +kernel

private def b0482c16 : List Row := [
  .c 31, .c 59, .c 3, .p pv3 [pv2,pv123323], .p pv13 [pv2,pv3,pv11,pv19,pv1049], .c 3, .c 181,
  .c 5, .c 3, .c 11, .c 367, .c 3, .c 5, .c 19, .c 3, .c 1117, .c 17, .c 3, .c 67, .c 7, .c 3,
  .c 41, .c 5, .c 3, .p pv2 [pv2,pv29,pv68041], .p pv2 [pv2,pv3,pv5,pv17,pv53,pv73], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv23,pv28597], .c 3, .p pv17 [pv2,pv5,pv7,pv56377], .c 11, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv127,pv5179], .c 3, .p pv2 [pv2,pv47,pv41983], .c 5, .c 3, .c 23, .c 7, .c 3,
  .c 5, .c 293, .c 3, .p pv2 [pv2,pv5,pv37,pv5333], .c 13, .c 3, .p pv2 [pv2,pv11,pv179383],
  .p pv2 [pv2,pv3,pv36541], .c 3, .c 19, .c 5, .c 3, .c 7, .c 409, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv31321], .c 3, .c 59, .c 7, .c 3, .c 37, .c 11, .c 3,
  .p pv5 [pv2,pv13,pv151787], .c 5, .c 3, .p pv2 [pv2,pv986617], .c 19, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv173,pv1901], .c 3, .c 7, .p pv3 [pv2,pv3,pv17,pv1433], .c 3, .c 359,
  .p pv23 [pv2,pv3,pv7,pv13,pv139], .c 3, .p pv2 [pv2,pv11,pv257,pv349], .c 5, .c 3, .c 17, .c 13,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv131,pv5021], .c 3, .p pv7 [pv2,pv5,pv59,pv6689], .c 331, .c 3,
  .c 31, .c 1913, .c 3, .c 7, .c 5, .c 3, .c 1367, .c 37, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv13,pv43,pv353], .c 47, .c 3, .c 11, .p pv2 [pv2,pv3,pv31,pv103], .c 3, .c 13,
  .c 5, .c 3, .c 137, .c 419, .c 3, .c 5, .c 17, .c 3, .p pv13 [pv2,pv5,pv23,pv17159], .c 271,
  .c 3, .c 397, .c 7, .c 3, .c 43, .c 5,
]
private theorem h0482c16 : checkBlock 3946331 128 b0482c16 = true := by
  decide +kernel

private def b0482c17 : List Row := [
  .c 3, .p pv2 [pv2,pv107,pv9221], .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv328883], .c 3, .c 17,
  .c 79, .c 3, .c 7, .c 1409, .c 3, .c 11, .c 5, .c 3, .c 41, .c 7, .c 3, .c 5, .c 139, .c 3,
  .c 13, .c 191, .c 3, .c 47, .c 23, .c 3, .p pv2 [pv2,pv7,pv19,pv37,pv401], .c 5, .c 3, .c 7,
  .c 103, .c 3, .c 5, .c 11, .c 3, .c 19, .c 7, .c 3, .c 431, .c 17, .c 3,
  .p pv3 [pv2,pv31,pv73,pv109], .c 5, .c 3, .c 11, .p pv13 [pv2,pv3,pv5,pv19,pv577], .c 3, .c 5,
  .c 59, .c 3, .c 7, .c 1471, .c 3, .c 29, .c 19, .c 3, .c 17, .c 5, .c 3, .c 13, .c 167, .c 3,
  .c 5, .c 1777, .c 3, .p pv19 [pv2,pv5,pv17,pv1451], .c 11, .c 3, .p pv5 [pv2,pv7,pv29,pv9721],
  .p pv7 [pv2,pv3,pv164447], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv1973369],
  .p pv13 [pv2,pv3,pv5,pv7,pv9397], .c 3, .c 5, .c 7, .c 3, .c 53, .c 37, .c 3,
  .p pv2 [pv2,pv11,pv19,pv4721], .p pv3 [pv2,pv3,pv657793], .c 3, .p pv2 [pv2,pv1973381], .c 5,
  .c 3, .c 67, .c 17, .c 3, .c 5, .c 23, .c 3, .c 109, .c 41, .c 3, .c 13, .c 7, .c 3,
  .p pv3 [pv2,pv307,pv1607], .c 5, .c 3, .p pv17 [pv2,pv43,pv45893],
  .p pv53 [pv2,pv3,pv5,pv11,pv13,pv23], .c 3, .c 5, .c 1637, .c 3, .c 11, .c 13, .c 3, .c 7,
  .c 71, .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv986707], .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv67,pv4909], .c 3, .c 43,
]
private theorem h0482c17 : checkBlock 3946587 128 b0482c17 = true := by
  decide +kernel

private def b0482c18 : List Row := [
  .p pv2 [pv2,pv3,pv29,pv7561], .c 3, .c 1741, .c 227, .c 3, .p pv2 [pv2,pv7,pv13,pv1549], .c 5,
  .c 3, .c 7, .c 149, .c 3, .c 5, .c 1499, .c 3, .c 29, .c 7, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv13,pv101,pv167], .c 3, .c 61, .c 5, .c 3, .c 19, .c 13, .c 3, .c 5, .c 1087,
  .c 3, .c 7, .c 67, .c 3, .c 17, .c 107, .c 3, .p pv3 [pv2,pv123341], .c 5, .c 3, .c 47, .c 11,
  .c 3, .c 5, .c 19, .c 3, .c 1109, .p pv2 [pv2,pv3,pv11,pv9967], .c 3, .p pv3 [pv2,pv7,pv70481],
  .p pv2 [pv2,pv3,pv23,pv37,pv773], .c 3, .c 7, .c 5, .c 3, .c 617, .c 31, .c 3, .c 5, .c 7, .c 3,
  .c 23, .c 53, .c 3, .c 317, .c 13, .c 3, .c 277, .c 5, .c 3, .c 101,
  .p pv17 [pv2,pv3,pv5,pv157,pv419], .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv394699],
  .p pv11 [pv2,pv3,pv7,pv17,pv691], .c 3, .p pv2 [pv2,pv986749], .c 7, .c 3, .c 19, .c 5, .c 3,
  .c 11, .c 1613, .c 3, .c 5, .p pv5 [pv2,pv3,pv29,pv53,pv107], .c 3, .c 13,
  .p pv5 [pv2,pv3,pv19,pv3847], .c 3, .c 7, .c 41, .c 3, .c 127, .c 5, .c 3, .c 1847, .c 7, .c 3,
  .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv78941], .c 11, .c 3, .c 683, .p pv2 [pv2,pv3,pv219281],
  .c 3, .c 103, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv41,pv3209], .c 3, .c 5, .c 17, .c 3,
  .c 523, .c 7, .c 3, .p pv5 [pv2,pv11,pv13,pv37,pv373], .p pv7 [pv2,pv3,pv82231], .c 3, .c 1033,
  .c 5, .c 3,
]
private theorem h0482c18 : checkBlock 3946843 128 b0482c18 = true := by
  decide +kernel

private def b0482c19 : List Row := [
  .c 13, .p pv13 [pv2,pv3,pv5,pv59,pv223], .c 3, .c 5, .c 47, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv13,pv4217], .c 3, .c 19, .c 11, .c 3, .c 37, .c 5, .c 3, .c 179,
  .p pv2 [pv2,pv3,pv5,pv11,pv443], .c 3, .c 5, .c 31, .c 3, .c 11, .p pv3 [pv2,pv3,pv43,pv15299],
  .c 3, .p pv2 [pv2,pv7,pv40277], .c 491, .c 3, .c 7, .c 5, .c 3, .c 59, .c 29, .c 3, .c 5, .c 7,
  .c 3, .c 67, .p pv7 [pv2,pv3,pv328931], .c 3, .c 13, .c 17, .c 3, .c 73, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv61,pv2311], .c 23, .c 3, .c 5, .c 37, .c 3, .c 47, .c 13, .c 3, .c 11, .c 7,
  .c 3, .c 17, .c 5, .c 3, .c 29, .c 97, .c 3, .c 5, .p pv2 [pv2,pv3,pv251,pv2621], .c 3, .c 19,
  .p pv5 [pv2,pv3,pv41117], .c 3, .c 7, .c 89, .c 3, .c 313, .c 5, .c 3, .c 61, .c 7, .c 3, .c 5,
  .c 577, .c 3, .c 31, .c 257, .c 3, .c 1237, .c 19, .c 3, .c 11, .c 5, .c 3, .c 7, .c 13, .c 3,
  .c 5, .c 127, .c 3, .c 151, .c 7, .c 3, .p pv3 [pv2,pv293,pv421], .p pv3 [pv2,pv3,pv17,pv38699],
  .c 3, .c 227, .c 5, .c 3, .p pv2 [pv2,pv37,pv149,pv179], .p pv7 [pv2,pv3,pv5,pv61,pv719], .c 3,
  .c 5, .c 11, .c 3, .c 7, .c 31, .c 3, .p pv5 [pv2,pv19,pv109,pv953], .c 23, .c 3, .c 13, .c 5,
  .c 3, .c 11, .c 173, .c 3, .c 5, .c 647, .c 3, .p pv7 [pv2,pv5,pv11,pv7177],
  .p pv13 [pv2,pv3,pv23,pv7151],
]
private theorem h0482c19 : checkBlock 3947099 128 b0482c19 = true := by
  decide +kernel

private def b0482c20 : List Row := [
  .c 3, .c 41, .c 13, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv601,pv821], .c 61, .c 3, .c 5, .c 7,
  .c 3, .c 137, .c 11, .c 3, .c 53, .c 47, .c 3, .c 29, .c 5, .c 3, .c 419,
  .p pv7 [pv2,pv3,pv5,pv17,pv43], .c 3, .c 5, .p pv3 [pv2,pv3,pv307,pv2143], .c 3, .c 13,
  .p pv11 [pv2,pv3,pv7,pv46993], .c 3, .c 17, .c 7, .c 3, .c 131, .c 5, .c 3, .c 113,
  .p pv11 [pv2,pv3,pv5,pv131581], .c 3, .c 5, .c 13, .c 3, .c 1171, .c 43, .c 3, .c 7, .c 11,
  .c 3, .p pv2 [pv2,pv367,pv2689], .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 23, .c 3, .c 11,
  .p pv5 [pv2,pv3,pv79,pv347], .c 3, .c 251, .p pv17 [pv2,pv3,pv19,pv31,pv1117], .c 3, .c 47,
  .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv23,pv1907], .c 3, .c 5, .c 19, .c 3,
  .p pv2 [pv2,pv5,pv1579], .c 7, .c 3, .p pv2 [pv2,pv67,pv89,pv331], .c 29, .c 3, .c 23, .c 5,
  .c 3, .c 17, .c 41, .c 3, .c 5, .c 277, .c 3, .c 7, .p pv5 [pv2,pv3,pv328961], .c 3, .c 11,
  .c 349, .c 3, .c 461, .c 5, .c 3, .p pv3 [pv2,pv11,pv73,pv1229], .c 79, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv313,pv1051], .c 3, .p pv3 [pv2,pv5,pv98689], .c 83, .c 3, .c 13,
  .p pv11 [pv2,pv3,pv82241], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv103,pv19163], .c 11, .c 3,
  .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv394759], .c 13, .c 3, .p pv2 [pv2,pv29,pv34031], .c 53,
  .c 3, .c 11, .c 5, .c 3, .c 97,
]
private theorem h0482c20 : checkBlock 3947355 128 b0482c20 = true := by
  decide +kernel

private def b0482c21 : List Row := [
  .c 19, .c 3, .c 5, .c 521, .c 3, .c 17, .p pv3 [pv2,pv3,pv7,pv193,pv487], .c 3,
  .p pv2 [pv2,pv1973813], .c 7, .c 3, .c 31, .c 5, .c 3, .p pv11 [pv2,pv17,pv116107], .c 37, .c 3,
  .c 5, .c 11, .c 3, .c 23, .c 109, .c 3, .c 7, .p pv2 [pv2,pv3,pv11,pv13,pv43,pv107], .c 3,
  .p pv5 [pv2,pv1973831], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 541, .c 3, .c 103, .c 29, .c 3,
  .c 19, .c 17, .c 3, .p pv2 [pv2,pv7,pv140989], .c 5, .c 3, .c 7, .c 43, .c 3, .c 5, .c 67, .c 3,
  .c 773, .c 7, .c 3, .c 421, .c 233, .c 3, .c 13, .c 5, .c 3, .c 83, .c 229, .c 3, .c 5, .c 61,
  .c 3, .c 7, .c 23, .c 3, .p pv2 [pv2,pv11,pv1483], .c 13, .c 3, .p pv3 [pv2,pv37,pv13337], .c 5,
  .c 3, .p pv7 [pv2,pv53,pv37243], .c 881, .c 3, .c 5, .c 41, .c 3,
  .p pv31 [pv2,pv5,pv29,pv13613], .c 89, .c 3, .c 257, .c 11, .c 3, .c 7, .c 5, .c 3, .c 23,
  .c 17, .c 3, .c 5, .c 7, .c 3, .c 11, .c 97, .c 3, .p pv5 [pv2,pv1973903],
  .p pv7 [pv2,pv3,pv17,pv41,pv59], .c 3, .c 71, .c 5, .c 3, .c 31, .c 241, .c 3, .c 5, .c 13,
  .c 3, .p pv19 [pv2,pv5,pv43,pv9181], .p pv11 [pv2,pv3,pv7,pv373], .c 3, .c 331, .c 7, .c 3,
  .p pv2 [pv2,pv17,pv116113], .c 5, .c 3, .c 41, .p pv2 [pv2,pv3,pv5,pv31,pv283], .c 3, .c 5,
  .c 29, .c 3, .p pv13 [pv2,pv5,pv7,pv163,pv173], .c 37, .c 3,
]
private theorem h0482c21 : checkBlock 3947611 128 b0482c21 = true := by
  decide +kernel

private def b0482c22 : List Row := [
  .c 7, .c 313, .c 3, .c 43, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 103, .c 3,
  .p pv2 [pv2,pv5,pv41,pv9629], .c 17, .c 3, .p pv3 [pv2,pv19,pv1367], .p pv3 [pv2,pv3,pv657983],
  .c 3, .p pv5 [pv2,pv7,pv281993], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 53, .c 3,
  .p pv7 [pv2,pv5,pv61,pv809], .c 7, .c 3, .c 17, .c 137, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv733,pv2693], .p pv2 [pv2,pv3,pv5,pv2437], .c 3, .c 5, .c 131, .c 3, .c 7, .c 19,
  .c 3, .c 13, .c 43, .c 3, .p pv2 [pv2,pv1187,pv1663], .c 5, .c 3, .c 601,
  .p pv3 [pv2,pv3,pv5,pv13,pv53,pv191], .c 3, .c 5, .c 11, .c 3, .c 61, .c 13, .c 3,
  .p pv2 [pv2,pv7,pv73,pv3863], .c 101, .c 3, .c 7, .c 5, .c 3, .c 11, .c 463, .c 3, .c 5, .c 7,
  .c 3, .c 37, .c 41, .c 3, .c 139, .c 23, .c 3, .c 53, .c 5, .c 3, .c 17, .c 29, .c 3, .c 5,
  .c 887, .c 3, .c 239, .c 11, .c 3, .c 47, .c 7, .c 3, .c 149, .c 5, .c 3, .c 73, .c 13, .c 3,
  .c 5, .c 19, .c 3, .p pv7 [pv2,pv5,pv7,pv56401], .p pv7 [pv2,pv3,pv164503], .c 3, .c 7, .c 157,
  .c 3, .c 1181, .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv13,pv3037],
  .c 59, .c 3, .c 113, .c 11, .c 3, .c 13, .c 5, .c 3, .c 7, .p pv23 [pv2,pv3,pv5,pv11,pv997],
]
private theorem h0482c22 : checkBlock 3947867 128 b0482c22 = true := by
  decide +kernel

private def b0482c23 : List Row := [
  .c 3, .c 5, .c 523, .c 3, .c 11, .c 7, .c 3, .p pv3 [pv2,pv41,pv12037], .c 13, .c 3, .c 19,
  .c 5, .c 3, .p pv2 [pv2,pv17,pv58061], .p pv3 [pv2,pv3,pv5,pv26321], .c 3, .c 5, .c 23, .c 3,
  .c 7, .p pv5 [pv2,pv3,pv19,pv59,pv587], .c 3, .c 631, .c 1987, .c 3, .p pv2 [pv2,pv987043],
  .c 5, .c 3, .p pv2 [pv2,pv13,pv11681], .c 19, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv163,pv367],
  .c 3, .c 13, .c 107, .c 3, .c 11, .c 17, .c 3, .c 7, .c 5, .c 3, .c 131, .c 227, .c 3, .c 5,
  .c 7, .c 3, .c 59, .p pv3 [pv2,pv3,pv31,pv21227], .c 3, .c 83, .p pv11 [pv2,pv3,pv109673], .c 3,
  .c 17, .c 5, .c 3, .c 71, .c 11, .c 3, .c 5, .p pv7 [pv2,pv3,pv401,pv547], .c 3,
  .p pv2 [pv2,pv5,pv17,pv929], .c 31, .c 3, .c 19, .c 7, .c 3, .c 11, .c 5, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv5,pv37,pv3557], .c 3, .c 5, .p pv5 [pv2,pv3,pv19,pv17317], .c 3,
  .p pv3 [pv2,pv5,pv7,pv59,pv239], .p pv3 [pv2,pv3,pv13,pv47,pv359], .c 3, .c 7,
  .p pv13 [pv2,pv3,pv53,pv97], .c 3, .p pv2 [pv2,pv29,pv101,pv337], .c 5, .c 3, .c 103, .c 7,
  .c 3, .c 5, .c 11, .c 3, .p pv17 [pv2,pv5,pv67,pv71,pv83], .c 509, .c 3, .p pv2 [pv2,pv987079],
  .c 563, .c 3, .c 1789, .c 5, .c 3, .c 7, .c 281, .c 3, .c 5, .c 727, .c 3, .c 23, .c 7, .c 3,
  .c 13, .c 163, .c 3, .p pv3 [pv2,pv17,pv19,pv191], .c 5, .c 3, .c 199,
  .p pv23 [pv2,pv3,pv5,pv13,pv2531], .c 3, .c 5, .p pv3 [pv2,pv3,pv439,pv1499], .c 3, .c 7, .c 11,
  .c 3, .c 31,
]
private theorem h0482c23 : checkBlock 3948123 128 b0482c23 = true := by
  decide +kernel

private def b0482c24 : List Row := [
  .c 29, .c 3, .p pv5 [pv2,pv41,pv179,pv269], .c 5, .c 3, .c 43, .c 431, .c 3, .c 5, .c 479, .c 3,
  .c 1549, .c 17, .c 3, .c 107, .c 19, .c 3, .c 7, .c 5, .c 3, .c 263, .c 709, .c 3, .c 5, .c 7,
  .c 3, .p pv7 [pv2,pv5,pv127,pv3109], .c 23, .c 3, .c 17, .c 11, .c 3, .c 211, .c 5, .c 3,
  .c 1531, .c 13, .c 3, .c 5, .c 59, .c 3, .c 11, .p pv5 [pv2,pv3,pv7,pv31337], .c 3,
  .p pv5 [pv2,pv19,pv29,pv3583], .c 7, .c 3, .p pv3 [pv2,pv11,pv4079], .c 5, .c 3, .c 23, .c 251,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv409,pv1609], .c 3, .c 673, .p pv2 [pv2,pv3,pv37,pv8893], .c 3,
  .c 7, .c 79, .c 3, .c 13, .c 5, .c 3, .c 1427, .c 7, .c 3, .c 5, .c 47, .c 3,
  .p pv3 [pv2,pv5,pv98713], .c 19, .c 3, .c 11, .c 13, .c 3, .p pv2 [pv2,pv7,pv31,pv4549], .c 5,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv65809], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv41,pv2293], .c 3,
  .p pv17 [pv2,pv5,pv157,pv503], .c 7, .c 3, .c 127, .c 83, .c 3, .c 31, .c 5, .c 3,
  .p pv3 [pv2,pv13,pv37967], .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv41131], .c 3, .c 7,
  .p pv3 [pv2,pv3,pv11,pv29,pv2063], .c 3, .c 41, .p pv2 [pv2,pv3,pv7,pv1741], .c 3, .c 11, .c 5,
  .c 3, .c 19, .c 619, .c 3, .c 5, .c 13, .c 3, .c 29, .p pv2 [pv2,pv3,pv281,pv1171], .c 3, .c 23,
  .p pv2 [pv2,pv3,pv19,pv1823], .c 3, .c 7, .c 5, .c 3, .c 337, .c 1657, .c 3,
]
private theorem h0482c24 : checkBlock 3948379 128 b0482c24 = true := by
  decide +kernel

private def b0482c25 : List Row := [
  .c 5, .c 7, .c 3, .c 17, .c 73, .c 3, .c 43, .c 149, .c 3, .p pv2 [pv2,pv61,pv16183], .c 5,
  .c 3, .c 11, .c 223, .c 3, .c 5, .p pv2 [pv2,pv3,pv658111], .c 3, .c 733,
  .p pv47 [pv2,pv3,pv7,pv13,pv113], .c 3, .c 37, .c 7, .c 3, .p pv2 [pv2,pv263,pv7507], .c 5,
  .c 3, .p pv3 [pv2,pv246793], .c 653, .c 3, .c 5, .p pv5 [pv2,pv3,pv101,pv181], .c 3,
  .p pv2 [pv2,pv5,pv7,pv5641], .c 11, .c 3, .c 7, .c 17, .c 3, .c 19, .c 5, .c 3,
  .p pv11 [pv2,pv31,pv63689], .c 7, .c 3, .c 5, .c 29, .c 3, .p pv2 [pv2,pv5,pv383,pv1031], .c 43,
  .c 3, .c 13, .c 389, .c 3, .c 17, .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 199, .c 3, .c 293,
  .c 7, .c 3, .c 311, .c 11, .c 3, .c 97, .c 5, .c 3, .c 67, .p pv2 [pv2,pv3,pv5,pv11,pv31,pv193],
  .c 3, .c 5, .c 593, .c 3, .c 7, .c 547, .c 3, .c 101, .c 47, .c 3,
  .p pv2 [pv2,pv11,pv13,pv13807], .c 5, .c 3, .p pv3 [pv2,pv19,pv83,pv313], .c 17, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv82267], .c 3, .p pv2 [pv2,pv5,pv197441], .c 859, .c 3, .c 19, .c 761, .c 3,
  .c 7, .c 5, .c 3, .p pv11 [pv2,pv163,pv12113], .c 13, .c 3, .c 5, .c 7, .c 3, .c 139,
  .p pv2 [pv2,pv3,pv109,pv3019], .c 3, .c 11, .p pv2 [pv2,pv3,pv73127], .c 3, .c 1447, .c 5, .c 3,
  .c 317, .c 53, .c 3, .c 5, .c 181, .c 3, .p pv3 [pv2,pv5,pv13,pv3797],
  .p pv2 [pv2,pv3,pv7,pv167,pv563], .c 3, .p pv5 [pv2,pv1069,pv1847], .c 7,
]
private theorem h0482c25 : checkBlock 3948635 128 b0482c25 = true := by
  decide +kernel

private def b0482c26 : List Row := [
  .c 3, .c 13, .c 5, .c 3, .c 37, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv50627], .c 3,
  .p pv7 [pv2,pv5,pv7,pv8059], .c 17, .c 3, .c 7, .c 13, .c 3, .c 11, .c 5, .c 3, .c 59, .c 7,
  .c 3, .c 5, .c 457, .c 3, .c 19, .c 919, .c 3, .c 17, .c 71, .c 3, .p pv3 [pv2,pv7,pv151,pv467],
  .c 5, .c 3, .c 7, .c 109, .c 3, .c 5, .c 11, .c 3, .c 13, .c 7, .c 3, .c 53, .c 19, .c 3,
  .c 251, .c 5, .c 3, .c 11, .c 43, .c 3, .c 5, .c 13, .c 3, .c 7, .p pv3 [pv2,pv3,pv219389],
  .c 3, .p pv5 [pv2,pv1974503], .c 1093, .c 3, .p pv2 [pv2,pv271,pv3643], .c 5, .c 3, .c 89,
  .c 157, .c 3, .c 5, .p pv2 [pv2,pv3,pv241,pv2731], .c 3, .c 23, .c 11, .c 3,
  .p pv3 [pv2,pv7,pv13,pv19,pv571], .p pv3 [pv2,pv3,pv41,pv5351], .c 3, .c 7, .c 5, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv5,pv7,pv3761], .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv197453],
  .p pv3 [pv2,pv3,pv13,pv197,pv257], .c 3, .c 1223, .p pv7 [pv2,pv3,pv329089], .c 3,
  .p pv3 [pv2,pv246817], .c 5, .c 3, .c 41, .c 47, .c 3, .c 5, .p pv29 [pv2,pv3,pv499,pv1319],
  .c 3, .c 71, .c 19, .c 3, .p pv3 [pv2,pv149,pv3313], .c 7, .c 3, .c 151, .c 5, .c 3,
  .p pv2 [pv2,pv89,pv11093], .p pv3 [pv2,pv3,pv5,pv11,pv3989], .c 3, .c 5, .c 17, .c 3, .c 11,
  .c 23, .c 3, .c 7, .c 139, .c 3, .c 29, .c 5, .c 3, .c 1523, .c 7, .c 3, .c 5,
]
private theorem h0482c26 : checkBlock 3948891 128 b0482c26 = true := by
  decide +kernel

private def b0482c27 : List Row := [
  .p pv5 [pv2,pv3,pv23,pv9539], .c 3, .c 17, .c 13, .c 3, .p pv2 [pv2,pv107,pv9227], .c 1033,
  .c 3, .c 43, .c 5, .c 3, .c 7, .c 601, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv11,pv2137], .c 3,
  .c 67, .c 7, .c 3, .c 11, .c 53, .c 3, .p pv5 [pv2,pv13,pv23,pv127], .c 5, .c 3,
  .p pv7 [pv2,pv11,pv16319], .c 61, .c 3, .c 5, .c 19, .c 3, .c 7, .p pv5 [pv2,pv3,pv329101],
  .c 3, .p pv3 [pv2,pv167,pv739], .c 17, .c 3, .c 83, .c 5, .c 3, .c 1483, .c 11, .c 3, .c 5,
  .c 113, .c 3, .p pv3 [pv2,pv5,pv98731], .c 41, .c 3, .p pv5 [pv2,pv7,pv282089], .c 29, .c 3,
  .c 7, .c 5, .c 3, .c 197, .c 23, .c 3, .c 5, .c 7, .c 3, .p pv37 [pv2,pv5,pv13,pv17,pv1787],
  .p pv5 [pv2,pv3,pv54851], .c 3, .c 179, .c 1553, .c 3, .c 13, .c 5, .c 3, .c 79,
  .p pv3 [pv2,pv3,pv5,pv14627], .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv73,pv541], .c 337,
  .c 3, .c 23, .c 7, .c 3, .p pv3 [pv2,pv15427], .c 5, .c 3, .c 11, .c 17, .c 3, .c 5, .c 163,
  .c 3, .c 509, .p pv2 [pv2,pv3,pv329111], .c 3, .c 7, .p pv2 [pv2,pv3,pv17,pv31,pv1249], .c 3,
  .c 37, .c 5, .c 3, .p pv3 [pv2,pv13,pv53,pv1433], .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv397,pv829], .c 3, .c 13, .c 11, .c 3, .p pv5 [pv2,pv41,pv48163], .c 31, .c 3,
  .c 73, .c 5, .c 3, .c 7, .c 1597, .c 3, .c 5, .c 13, .c 3, .p pv29 [pv2,pv5,pv463,pv853], .c 7,
  .c 3, .c 19, .c 23, .c 3,
]
private theorem h0482c27 : checkBlock 3949147 128 b0482c27 = true := by
  decide +kernel

private def b0482c28 : List Row := [
  .c 101, .c 5, .c 3, .p pv3 [pv2,pv123419], .p pv2 [pv2,pv3,pv5,pv47,pv2801], .c 3, .c 5, .c 37,
  .c 3, .c 7, .c 17, .c 3, .c 1409, .c 11, .c 3, .p pv3 [pv2,pv103,pv4793], .c 5, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv5,pv11,pv17], .c 3, .c 5, .c 79, .c 3, .c 11, .p pv2 [pv2,pv3,pv13,pv29,pv97],
  .c 3, .c 17, .p pv2 [pv2,pv3,pv269,pv2447], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv23,pv42929],
  .c 263, .c 3, .c 5, .c 7, .c 3, .c 29, .c 1259, .c 3, .p pv5 [pv2,pv1974743], .c 41, .c 3,
  .c 31, .c 5, .c 3, .c 1709, .p pv43 [pv2,pv3,pv5,pv2633], .c 3, .c 5, .c 43, .c 3, .c 19,
  .c 1459, .c 3, .c 11, .c 7, .c 3, .c 881, .c 5, .c 3, .p pv3 [pv2,pv11,pv37,pv1213],
  .p pv2 [pv2,pv3,pv5,pv13,pv19,pv41], .c 3, .c 5, .c 23, .c 3, .p pv3 [pv2,pv5,pv7,pv28211],
  .c 13, .c 3, .c 7, .c 19, .c 3, .c 89, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 61, .c 3, .c 41,
  .c 127, .c 3, .c 823, .p pv3 [pv2,pv3,pv59,pv3719], .c 3, .c 11, .c 5, .c 3, .c 7, .c 1123,
  .c 3, .c 5, .c 29, .c 3, .c 181, .c 7, .c 3, .c 571, .p pv7 [pv2,pv3,pv13,pv12659], .c 3, .c 53,
  .c 5, .c 3, .p pv2 [pv2,pv677,pv2917], .c 13, .c 3, .c 5, .c 11, .c 3, .c 7, .c 349, .c 3,
  .c 59, .c 37, .c 3, .p pv2 [pv2,pv89,pv22189], .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv67,pv131], .c 3, .c 5, .p pv7 [pv2,pv3,pv164569],
]
private theorem h0482c28 : checkBlock 3949403 128 b0482c28 = true := by
  decide +kernel

private def b0482c29 : List Row := [
  .c 3, .c 17, .c 19, .c 3, .c 1601, .p pv2 [pv2,pv3,pv36571], .c 3, .c 7, .c 5, .c 3, .c 31,
  .c 1871, .c 3, .c 5, .c 7, .c 3, .c 107, .c 11, .c 3, .c 373, .c 13, .c 3,
  .p pv5 [pv2,pv1974851], .c 5, .c 3, .c 211, .p pv3 [pv2,pv3,pv5,pv31,pv137], .c 3, .c 5, .c 67,
  .c 3, .c 23, .p pv2 [pv2,pv3,pv7,pv43], .c 3, .c 269, .c 7, .c 3, .p pv2 [pv2,pv987433], .c 5,
  .c 3, .c 19, .c 31, .c 3, .c 5, .c 313, .c 3, .c 13, .c 397, .c 3, .c 7, .c 11, .c 3, .c 17,
  .c 5, .c 3, .c 1693, .c 7, .c 3, .c 5, .c 13, .c 3, .c 11, .c 1171, .c 3, .c 37, .c 683, .c 3,
  .p pv3 [pv2,pv7,pv11,pv229], .c 5, .c 3, .c 7, .c 71, .c 3, .c 5, .c 101, .c 3, .c 61, .c 7,
  .c 3, .c 41, .p pv2 [pv2,pv3,pv658303], .c 3, .c 331, .c 5, .c 3, .c 13, .c 17, .c 3, .c 5,
  .c 673, .c 3, .c 7, .c 1103, .c 3, .c 11, .p pv11 [pv2,pv3,pv7,pv17,pv461], .c 3, .c 19, .c 5,
  .c 3, .c 23, .c 37, .c 3, .c 5, .p pv2 [pv2,pv3,pv219437], .c 3, .p pv7 [pv2,pv5,pv394987],
  .c 59, .c 3, .p pv2 [pv2,pv7,pv141067], .c 383, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv61717],
  .c 11, .c 3, .c 5, .c 7, .c 3, .c 347, .p pv3 [pv2,pv3,pv11,pv19949], .c 3, .c 13, .c 89, .c 3,
  .c 11,
]
private theorem h0482c29 : checkBlock 3949659 128 b0482c29 = true := by
  decide +kernel

private def b0482c30 : List Row := [
  .c 5, .c 3, .p pv7 [pv2,pv7,pv67,pv4211], .c 79, .c 3, .c 5, .c 31, .c 3, .c 53, .c 13, .c 3,
  .c 43, .c 7, .c 3, .c 71, .c 5, .c 3, .c 643, .c 23, .c 3, .c 5, .c 11, .c 3,
  .p pv3 [pv2,pv5,pv7,pv14107], .c 139, .c 3, .c 7, .p pv31 [pv2,pv3,pv11,pv7481], .c 3, .c 593,
  .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 251, .c 3, .c 59, .c 179, .c 3, .c 23, .c 223, .c 3,
  .c 29, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 281, .c 3, .c 47, .c 7, .c 3, .c 227,
  .p pv2 [pv2,pv3,pv113,pv971], .c 3, .p pv3 [pv2,pv29,pv8513], .c 5, .c 3,
  .p pv7 [pv2,pv1975019], .p pv17 [pv2,pv3,pv5,pv32917], .c 3, .c 5, .c 197, .c 3, .c 7, .c 83,
  .c 3, .c 487, .c 503, .c 3, .c 13, .c 5, .c 3, .c 17, .c 191, .c 3, .c 5, .c 359, .c 3, .c 19,
  .c 37, .c 3, .c 89, .c 11, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv1975049],
  .p pv29 [pv2,pv3,pv5,pv7,pv11,pv19], .c 3, .c 5, .c 7, .c 3, .c 11, .c 31, .c 3,
  .p pv2 [pv2,pv61,pv16189], .c 19, .c 3, .p pv2 [pv2,pv11,pv409,pv439], .c 5, .c 3,
  .p pv11 [pv2,pv7,pv13,pv2713], .c 97, .c 3, .c 5, .c 17, .c 3, .c 13, .c 53, .c 3,
  .p pv2 [pv2,pv1975073], .c 7, .c 3, .c 103, .c 5, .c 3, .p pv11 [pv2,pv23,pv79,pv1087],
  .p pv7 [pv2,pv3,pv5,pv109,pv151], .c 3, .c 5, .c 13, .c 3,
]
private theorem h0482c30 : checkBlock 3949915 128 b0482c30 = true := by
  decide +kernel

private def b0482c31 : List Row := [
  .c 17, .p pv2 [pv2,pv3,pv179,pv613], .c 3, .c 7, .p pv3 [pv2,pv3,pv571,pv1153], .c 3,
  .p pv5 [pv2,pv1975091], .c 5, .c 3, .p pv3 [pv2,pv11,pv17,pv5281], .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv53,pv6211], .c 3, .p pv3 [pv2,pv5,pv19751], .p pv3 [pv2,pv3,pv658367], .c 3,
  .p pv5 [pv2,pv13,pv29,pv31], .c 47, .c 3, .p pv2 [pv2,pv7,pv141079], .c 5, .c 3, .c 7, .c 11,
  .c 3, .c 5, .c 23, .c 3, .c 37, .c 7, .c 3, .c 31, .c 17, .c 3, .c 11, .c 5, .c 3, .c 53,
  .c 401, .c 3, .c 5, .p pv7 [pv2,pv3,pv17,pv47,pv103], .c 3, .c 7, .p pv3 [pv2,pv3,pv191,pv383],
  .c 3, .p pv2 [pv2,pv1975133], .c 109, .c 3, .c 17, .c 5, .c 3, .c 1231, .c 43, .c 3, .c 5,
  .c 11, .c 3, .p pv2 [pv2,pv5,pv17,pv19,pv1223], .c 29, .c 3, .c 13, .c 31, .c 3, .c 7, .c 5,
  .c 3, .c 11, .c 151, .c 3, .c 5, .c 7, .c 3, .p pv13 [pv2,pv5,pv11,pv67], .c 13, .c 3,
  .p pv5 [pv2,pv1975163], .c 1741, .c 3, .c 107, .c 5, .c 3, .p pv7 [pv2,pv7,pv282167], .c 17,
  .c 3, .c 5, .c 19, .c 3, .c 29, .c 11, .c 3, .c 1283, .c 7, .c 3, .p pv2 [pv2,pv13,pv151937],
  .c 5, .c 3, .c 71, .c 1129, .c 3, .c 5, .c 1621, .c 3, .c 811, .p pv3 [pv2,pv3,pv541,pv1217],
  .c 3, .c 7, .p pv2 [pv2,pv3,pv13,pv23,pv367], .c 3, .p pv3 [pv2,pv17,pv31,pv937], .c 5, .c 3,
  .p pv13 [pv2,pv1975199], .c 7, .c 3, .c 5, .c 1567, .c 3, .c 23, .c 101, .c 3,
  .p pv3 [pv2,pv37,pv6673], .c 11, .c 3, .c 19, .c 5,
]
private theorem h0482c31 : checkBlock 3950171 128 b0482c31 = true := by
  decide +kernel

def rows0482 : List Row :=
  b0482c00 ++ b0482c01 ++ b0482c02 ++ b0482c03 ++ b0482c04 ++ b0482c05 ++ b0482c06 ++ b0482c07 ++
  b0482c08 ++ b0482c09 ++ b0482c10 ++ b0482c11 ++ b0482c12 ++ b0482c13 ++ b0482c14 ++ b0482c15 ++
  b0482c16 ++ b0482c17 ++ b0482c18 ++ b0482c19 ++ b0482c20 ++ b0482c21 ++ b0482c22 ++ b0482c23 ++
  b0482c24 ++ b0482c25 ++ b0482c26 ++ b0482c27 ++ b0482c28 ++ b0482c29 ++ b0482c30 ++ b0482c31

theorem checked0482 : checkBlock 3942235 4096 rows0482 = true :=
  checkBlock_append h0482c00 (
    checkBlock_append h0482c01 (
    checkBlock_append h0482c02 (
    checkBlock_append h0482c03 (
    checkBlock_append h0482c04 (
    checkBlock_append h0482c05 (
    checkBlock_append h0482c06 (
    checkBlock_append h0482c07 (
    checkBlock_append h0482c08 (
    checkBlock_append h0482c09 (
    checkBlock_append h0482c10 (
    checkBlock_append h0482c11 (
    checkBlock_append h0482c12 (
    checkBlock_append h0482c13 (
    checkBlock_append h0482c14 (
    checkBlock_append h0482c15 (
    checkBlock_append h0482c16 (
    checkBlock_append h0482c17 (
    checkBlock_append h0482c18 (
    checkBlock_append h0482c19 (
    checkBlock_append h0482c20 (
    checkBlock_append h0482c21 (
    checkBlock_append h0482c22 (
    checkBlock_append h0482c23 (
    checkBlock_append h0482c24 (
    checkBlock_append h0482c25 (
    checkBlock_append h0482c26 (
    checkBlock_append h0482c27 (
    checkBlock_append h0482c28 (
    checkBlock_append h0482c29 (
    checkBlock_append h0482c30 (
    h0482c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
