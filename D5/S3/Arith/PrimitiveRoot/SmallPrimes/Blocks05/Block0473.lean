/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks05/Block0473
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks05/Block0473.checked0473
   digest: Kernel proof of checker success on extended consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table052
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table059
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table069
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table081
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table122
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table159
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table161
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table163
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table170
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table175
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table181
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table182
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table190
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table202
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table223
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables03.Table246
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables03.Table247

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0473c00 : List Row := [
  .c 307, .c 3, .c 1151, .c 11, .c 3, .p pv2 [pv2,pv967129], .c 109, .c 3, .c 47, .c 5, .c 3,
  .c 7, .c 23, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv13,pv14879], .c 7, .c 3, .c 83,
  .p pv2 [pv2,pv3,pv179,pv1801], .c 3, .c 13, .c 5, .c 3, .c 61, .c 131, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv49597], .c 3, .c 7, .c 503, .c 3, .c 23, .c 11, .c 3, .c 31, .c 5, .c 3,
  .c 491, .p pv3 [pv2,pv3,pv5,pv11,pv19,pv617], .c 3, .c 5, .c 1427, .c 3, .c 11, .c 101, .c 3,
  .c 1303, .c 19, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv13,pv148793], .c 257, .c 3, .c 5, .c 7,
  .c 3, .c 13, .c 1087, .c 3, .c 41, .c 17, .c 3, .c 613, .c 5, .c 3,
  .p pv13 [pv2,pv7,pv71,pv139], .c 97, .c 3, .c 5, .c 13, .c 3, .c 631, .c 251, .c 3, .c 11, .c 7,
  .c 3, .c 17, .c 5, .c 3, .p pv11 [pv2,pv11,pv41,pv4289], .c 61, .c 3, .c 5, .c 29, .c 3, .c 541,
  .c 239, .c 3, .c 7, .p pv7 [pv2,pv3,pv644783], .c 3, .c 347, .c 5, .c 3, .c 13, .c 7, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv29,pv11117], .c 3, .p pv3 [pv2,pv5,pv37,pv1307], .c 19, .c 3, .c 179,
  .p pv11 [pv2,pv3,pv331,pv487], .c 3, .c 11, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 499, .c 3,
  .p pv17 [pv2,pv5,pv619], .c 7, .c 3, .c 37, .c 199, .c 3,
]
private theorem h0473c00 : checkBlock 3868507 128 b0473c00 = true := by
  decide +kernel

private def b0473c01 : List Row := [
  .p pv2 [pv2,pv1934381], .c 5, .c 3, .c 31, .c 151, .c 3, .c 5, .c 11, .c 3, .c 7, .c 103, .c 3,
  .c 13, .p pv13 [pv2,pv3,pv7,pv11,pv53,pv79], .c 3, .p pv3 [pv2,pv17,pv28447], .c 5, .c 3, .c 11,
  .c 41, .c 3, .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv11,pv35171], .c 13, .c 3,
  .p pv3 [pv2,pv7,pv34543], .c 701, .c 3, .c 7, .c 5, .c 3, .c 863, .c 31, .c 3, .c 5, .c 7, .c 3,
  .c 53, .c 11, .c 3, .p pv5 [pv2,pv109,pv17747], .p pv11 [pv2,pv3,pv67,pv401], .c 3, .c 23, .c 5,
  .c 3, .c 277, .c 29, .c 3, .c 5, .c 79, .c 3, .c 1753, .c 937, .c 3, .c 17, .c 7, .c 3, .c 41,
  .c 5, .c 3, .c 167, .c 13, .c 3, .c 5, .p pv11 [pv2,pv3,pv191,pv211], .c 3,
  .p pv2 [pv2,pv5,pv7,pv5527], .c 1831, .c 3, .c 7, .c 11, .c 3, .c 19, .c 5, .c 3, .c 29, .c 7,
  .c 3, .c 5, .c 73, .c 3, .c 11, .p pv2 [pv2,pv3,pv19,pv71,pv239], .c 3,
  .p pv3 [pv2,pv563,pv859], .c 719, .c 3, .c 13, .c 5, .c 3, .c 7, .c 19, .c 3, .c 5,
  .p pv17 [pv2,pv3,pv7,pv13,pv1181], .c 3, .p pv3 [pv2,pv5,pv24181], .c 7, .c 3, .c 967, .c 13,
  .c 3, .p pv2 [pv2,pv173,pv5591], .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv64483], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv31,pv61], .c 3, .c 7, .c 47, .c 3, .c 11, .p pv7 [pv2,pv3,pv7,pv92119],
  .c 3, .c 71, .c 5, .c 3, .p pv3 [pv2,pv11,pv13,pv19,pv89], .c 43, .c 3, .c 5, .c 31,
]
private theorem h0473c01 : checkBlock 3868763 128 b0473c01 = true := by
  decide +kernel

private def b0473c02 : List Row := [
  .c 3, .c 13, .p pv5 [pv2,pv3,pv644837], .c 3, .c 19, .p pv11 [pv2,pv3,pv107473], .c 3, .c 7,
  .c 5, .c 3, .c 97, .c 11, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv223,pv347], .c 37, .c 3,
  .p pv3 [pv2,pv167,pv181], .c 331, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv7,pv138181], .c 193,
  .c 3, .c 5, .c 673, .c 3, .c 17, .c 23, .c 3, .c 47, .c 7, .c 3, .c 29, .c 5, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv5,pv1433], .c 3, .c 5, .c 11, .c 3, .p pv7 [pv2,pv5,pv7,pv31,pv1783],
  .p pv5 [pv2,pv3,pv13,pv12401], .c 3, .c 7, .c 1097, .c 3, .p pv11 [pv2,pv19,pv29,pv3511], .c 5,
  .c 3, .c 11, .c 7, .c 3, .c 5, .c 1423, .c 3, .c 19, .c 1019, .c 3, .c 1483, .c 17, .c 3,
  .p pv5 [pv2,pv7,pv23,pv751], .c 5, .c 3, .c 7, .c 59, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv17,pv5419], .c 3, .c 239, .c 7, .c 3, .c 13, .c 19, .c 3, .c 17, .c 5,
  .c 3, .p pv2 [pv2,pv967297], .p pv3 [pv2,pv3,pv5,pv13,pv3307], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv322433], .c 3, .c 7, .c 13, .c 3, .c 617, .c 29, .c 3,
  .p pv2 [pv2,pv53,pv18251], .c 5, .c 3, .c 73, .c 23, .c 3, .c 5, .c 107, .c 3,
  .p pv17 [pv2,pv5,pv61,pv6343], .c 97, .c 3, .c 181, .c 11, .c 3, .c 7, .c 5, .c 3, .c 401,
  .c 17, .c 3, .c 5, .c 7, .c 3, .c 11, .p pv3 [pv2,pv3,pv79,pv907], .c 3, .c 23, .c 43, .c 3,
  .c 223,
]
private theorem h0473c02 : checkBlock 3869019 128 b0473c02 = true := by
  decide +kernel

private def b0473c03 : List Row := [
  .c 5, .c 3, .c 59, .c 13, .c 3, .c 5, .c 71, .c 3, .c 61, .c 19, .c 3,
  .p pv3 [pv2,pv29,pv31,pv269], .c 7, .c 3, .c 1907, .c 5, .c 3, .c 127,
  .p pv3 [pv2,pv3,pv5,pv101,pv1277], .c 3, .c 5, .c 67, .c 3, .p pv3 [pv2,pv5,pv7,pv13,pv1063],
  .c 1361, .c 3, .c 7, .p pv11 [pv2,pv3,pv80611], .c 3, .c 13, .c 5, .c 3, .c 1453, .c 7, .c 3,
  .c 5, .c 131, .c 3, .p pv13 [pv2,pv5,pv19,pv4073], .c 17, .c 3, .c 997, .c 13, .c 3, .c 349,
  .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 83, .c 3, .c 149, .c 7, .c 3, .c 17, .c 31, .c 3, .c 11,
  .c 5, .c 3, .p pv7 [pv2,pv13,pv43,pv3461], .c 103, .c 3, .c 5, .c 19, .c 3, .c 7, .c 61, .c 3,
  .p pv3 [pv2,pv41,pv47,pv251], .c 457, .c 3, .c 37, .c 5, .c 3, .c 71, .c 233, .c 3, .c 5, .c 11,
  .c 3, .c 29, .c 179, .c 3, .c 809, .c 383, .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv23 [pv2,pv3,pv5,pv7,pv37,pv83], .c 3, .c 5, .c 7, .c 3, .c 1439,
  .p pv5 [pv2,pv3,pv17,pv2371], .c 3, .c 53, .c 557, .c 3, .c 19, .c 5, .c 3, .c 13, .c 173, .c 3,
  .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv71,pv109], .c 11, .c 3, .c 733, .c 7, .c 3, .c 31, .c 5,
  .c 3, .c 263, .c 19, .c 3, .c 5, .c 43, .c 3,
]
private theorem h0473c03 : checkBlock 3869275 128 b0473c03 = true := by
  decide +kernel

private def b0473c04 : List Row := [
  .c 1597, .c 827, .c 3, .c 7, .c 41, .c 3, .c 23, .c 5, .c 3, .c 409, .c 7, .c 3, .c 5, .c 17,
  .c 3, .p pv3 [pv2,pv5,pv96739], .c 127, .c 3, .c 13, .c 11, .c 3, .p pv3 [pv2,pv7,pv113,pv1223],
  .c 5, .c 3, .c 7, .p pv23 [pv2,pv3,pv5,pv11,pv13,pv41], .c 3, .c 5, .c 1613, .c 3, .c 11, .c 7,
  .c 3, .c 19, .c 181, .c 3, .p pv2 [pv2,pv11,pv175891], .c 5, .c 3, .c 109,
  .p pv7 [pv2,pv3,pv5,pv128987], .c 3, .c 5, .c 1601, .c 3, .c 7, .p pv3 [pv2,pv3,pv179,pv1201],
  .c 3, .p pv5 [pv2,pv83,pv23311], .p pv2 [pv2,pv3,pv7,pv6581], .c 3, .c 59, .c 5, .c 3,
  .p pv7 [pv2,pv773,pv2503], .p pv7 [pv2,pv3,pv5,pv3583], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv58631], .c 3, .c 47, .p pv13 [pv2,pv3,pv67,pv4813], .c 3, .c 11, .c 17,
  .c 3, .c 7, .c 5, .c 3, .c 227, .c 13, .c 3, .c 5, .c 7, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv37,pv17431], .c 3, .p pv5 [pv2,pv1934843], .c 53, .c 3, .c 17, .c 5, .c 3,
  .c 31, .c 11, .c 3, .c 5, .c 647, .c 3, .c 19, .c 71, .c 3, .c 641, .c 7, .c 3, .c 11, .c 5,
  .c 3, .p pv3 [pv2,pv120929], .c 29, .c 3, .c 5, .c 241, .c 3, .p pv2 [pv2,pv5,pv7,pv131,pv211],
  .p pv3 [pv2,pv3,pv43,pv53,pv283], .c 3, .c 7, .c 13, .c 3, .p pv3 [pv2,pv483719], .c 5, .c 3,
  .p pv11 [pv2,pv1934879], .c 7, .c 3, .c 5, .c 11, .c 3, .c 337, .c 23, .c 3, .c 1091, .c 61,
  .c 3, .c 163, .c 5,
]
private theorem h0473c04 : checkBlock 3869531 128 b0473c04 = true := by
  decide +kernel

private def b0473c05 : List Row := [
  .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv128993], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv23,pv2003], .c 3,
  .c 13, .c 7, .c 3, .p pv5 [pv2,pv19,pv101837], .c 89, .c 3, .c 103, .c 5, .c 3, .c 23, .c 727,
  .c 3, .c 5, .c 13, .c 3, .c 7, .c 11, .c 3, .c 173, .c 47, .c 3, .c 193, .c 5, .c 3,
  .p pv3 [pv2,pv53,pv9127], .c 191, .c 3, .c 5, .p pv5 [pv2,pv3,pv1493], .c 3,
  .p pv2 [pv2,pv5,pv193493], .c 17, .c 3, .c 37, .c 59, .c 3, .c 7, .c 5, .c 3, .c 13,
  .p pv31 [pv2,pv3,pv5,pv7,pv17,pv271], .c 3, .c 5, .c 7, .c 3, .c 167, .c 157, .c 3, .c 17,
  .c 11, .c 3, .c 751, .c 5, .c 3, .c 919, .c 23, .c 3, .c 5, .p pv2 [pv2,pv3,pv31,pv101,pv103],
  .c 3, .c 11, .c 631, .c 3, .c 509, .c 7, .c 3, .c 47, .c 5, .c 3, .c 19, .c 37, .c 3, .c 5,
  .c 31, .c 3, .c 211, .c 199, .c 3, .c 7, .p pv3 [pv2,pv3,pv19,pv83,pv409], .c 3, .c 29, .c 5,
  .c 3, .c 379, .c 7, .c 3, .c 5, .c 19, .c 3, .c 887, .c 13, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv521,pv619], .c 3, .p pv3 [pv2,pv7,pv29,pv2383], .c 5, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv5,pv43], .c 3, .c 5, .c 53, .c 3, .p pv2 [pv2,pv5,pv173,pv2237], .c 7, .c 3,
  .c 101, .c 103, .c 3, .c 61, .c 5, .c 3, .c 467, .c 11, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv193,pv557], .c 3, .c 7,
]
private theorem h0473c05 : checkBlock 3869787 128 b0473c05 = true := by
  decide +kernel

private def b0473c06 : List Row := [
  .c 43, .c 3, .p pv5 [pv2,pv59,pv32797], .c 23, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv167,pv11587], .c 13, .c 3, .c 5, .c 17, .c 3, .c 31,
  .p pv5 [pv2,pv3,pv19,pv23,pv41], .c 3, .p pv2 [pv2,pv7,pv89,pv1553], .c 29, .c 3, .c 7, .c 5,
  .c 3, .c 37, .c 19, .c 3, .c 5, .c 7, .c 3, .c 17, .c 269, .c 3, .c 1811, .c 163, .c 3, .c 13,
  .c 5, .c 3, .c 11, .c 47, .c 3, .c 5, .c 239, .c 3, .c 79, .c 31, .c 3, .c 29, .c 7, .c 3,
  .c 739, .c 5, .c 3, .p pv2 [pv2,pv19,pv50923], .c 271, .c 3, .c 5, .p pv2 [pv2,pv3,pv322513],
  .c 3, .c 389, .c 11, .c 3, .c 7, .c 17, .c 3, .p pv2 [pv2,pv43,pv22501], .c 5, .c 3,
  .p pv2 [pv2,pv13,pv148853], .c 7, .c 3, .c 5, .c 23, .c 3, .c 13, .p pv7 [pv2,pv3,pv80629],
  .c 3, .p pv2 [pv2,pv11,pv87959], .p pv7 [pv2,pv3,pv127,pv1693], .c 3, .c 17, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv23,pv71,pv79], .c 3, .c 5, .c 13, .c 3, .c 701, .c 7, .c 3,
  .p pv2 [pv2,pv31,pv62423], .c 11, .c 3, .c 23, .c 5, .c 3, .p pv7 [pv2,pv571,pv3389], .c 73,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv645041], .c 3, .c 7, .c 29, .c 3, .c 31,
  .p pv2 [pv2,pv3,pv7,pv43,pv2143], .c 3, .c 109, .c 5, .c 3, .c 13, .c 17, .c 3, .c 5, .c 41,
  .c 3, .c 19, .p pv5 [pv2,pv3,pv13,pv29,pv59], .c 3, .c 743, .c 79, .c 3, .c 7, .c 5, .c 3,
]
private theorem h0473c06 : checkBlock 3870043 128 b0473c06 = true := by
  decide +kernel

private def b0473c07 : List Row := [
  .p pv2 [pv2,pv1935149], .c 43, .c 3, .c 5, .c 7, .c 3, .c 29, .c 1093, .c 3, .c 11, .c 19, .c 3,
  .c 181, .c 5, .c 3, .c 229, .c 653, .c 3, .c 5, .p pv29 [pv2,pv3,pv10079], .c 3, .c 59, .c 89,
  .c 3, .c 13, .c 7, .c 3, .c 397, .c 5, .c 3, .c 41, .c 11, .c 3, .c 5, .c 409, .c 3, .c 23,
  .c 13, .c 3, .c 7, .c 359, .c 3, .c 11, .c 5, .c 3, .c 61, .c 7, .c 3, .c 5, .c 97, .c 3,
  .p pv3 [pv2,pv5,pv41,pv59], .c 47, .c 3, .c 17, .c 677, .c 3, .p pv2 [pv2,pv7,pv13,pv31], .c 5,
  .c 3, .c 7, .c 101, .c 3, .c 5, .c 11, .c 3, .c 53, .c 7, .c 3, .p pv2 [pv2,pv509,pv1901],
  .p pv3 [pv2,pv3,pv11,pv13,pv347], .c 3, .c 31, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv29,pv67,pv83], .c 3, .c 7, .c 23, .c 3, .p pv2 [pv2,pv787,pv2459],
  .p pv17 [pv2,pv3,pv7,pv15359], .c 3, .c 43, .c 5, .c 3, .p pv7 [pv2,pv1935239], .c 109, .c 3,
  .c 5, .c 1373, .c 3, .c 443, .c 11, .c 3, .c 47, .p pv2 [pv2,pv3,pv645083], .c 3, .c 7, .c 5,
  .c 3, .c 17, .c 61, .c 3, .c 5, .c 7, .c 3, .c 89, .c 41, .c 3,
  .p pv11 [pv2,pv11,pv17,pv79,pv131], .c 13, .c 3, .c 37, .c 5, .c 3, .c 83, .c 757, .c 3, .c 5,
  .c 19, .c 3, .p pv11 [pv2,pv5,pv199,pv389], .c 491,
]
private theorem h0473c07 : checkBlock 3870299 128 b0473c07 = true := by
  decide +kernel

private def b0473c08 : List Row := [
  .c 3, .p pv2 [pv2,pv461,pv2099], .c 7, .c 3, .p pv2 [pv2,pv1935281], .c 5, .c 3, .c 823, .c 263,
  .c 3, .c 5, .c 17, .c 3, .c 11, .c 151, .c 3, .c 7, .c 113, .c 3, .c 557, .c 5, .c 3,
  .p pv13 [pv2,pv31,pv163,pv383], .c 7, .c 3, .c 5, .c 13, .c 3, .c 17, .p pv5 [pv2,pv3,pv35839],
  .c 3, .p pv3 [pv2,pv483827], .p pv2 [pv2,pv3,pv107,pv6029], .c 3, .c 19, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv29,pv1483], .c 3, .c 5, .c 103, .c 3, .c 269, .c 7, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv53759], .c 3, .p pv2 [pv2,pv967663], .c 5, .c 3, .c 13, .c 19, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv23893], .c 3, .c 7, .c 1013, .c 3, .c 257, .c 17, .c 3, .c 1213, .c 5, .c 3,
  .p pv3 [pv2,pv29,pv43,pv97], .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv53,pv179], .c 3, .c 241,
  .p pv7 [pv2,pv3,pv11,pv113,pv173], .c 3, .c 71, .p pv2 [pv2,pv3,pv322559], .c 3, .c 7, .c 5,
  .c 3, .p pv13 [pv2,pv19,pv37,pv2753], .p pv41 [pv2,pv3,pv5,pv7], .c 3, .c 5, .c 7, .c 3, .c 43,
  .c 139, .c 3, .c 13, .c 23, .c 3, .c 499, .c 5, .c 3, .c 53, .p pv23 [pv2,pv3,pv5,pv13,pv397],
  .c 3, .c 5, .c 11, .c 3, .c 163, .c 13, .c 3, .p pv5 [pv2,pv1935383], .c 7, .c 3,
  .p pv2 [pv2,pv967693], .c 5, .c 3, .c 11, .c 17, .c 3, .c 5, .c 229, .c 3, .c 67,
  .p pv7 [pv2,pv3,pv37,pv1453], .c 3, .c 7, .c 479, .c 3, .p pv2 [pv2,pv13,pv53], .c 5, .c 3,
  .c 571,
]
private theorem h0473c08 : checkBlock 3870555 128 b0473c08 = true := by
  decide +kernel

private def b0473c09 : List Row := [
  .c 7, .c 3, .c 5, .c 43, .c 3, .p pv2 [pv2,pv5,pv193541], .c 11, .c 3,
  .p pv2 [pv2,pv47,pv41179], .c 37, .c 3, .c 29, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv7,pv31,pv991], .c 3, .c 19, .c 7, .c 3, .c 1697, .c 1327, .c 3,
  .p pv5 [pv2,pv29,pv66739], .c 5, .c 3, .p pv2 [pv2,pv887,pv1091], .c 83, .c 3, .c 5, .c 23,
  .c 3, .c 7, .c 17, .c 3, .c 317, .c 11, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv73,pv26513],
  .c 967, .c 3, .c 5, .c 569, .c 3, .c 11, .p pv5 [pv2,pv3,pv20161], .c 3, .c 17, .c 13, .c 3,
  .c 7, .c 5, .c 3, .p pv3 [pv2,pv113,pv2141], .c 59, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv37,pv5231], .c 1381, .c 3, .p pv2 [pv2,pv19,pv23,pv43,pv103], .c 29, .c 3,
  .p pv3 [pv2,pv483869], .c 5, .c 3, .p pv7 [pv2,pv7,pv13,pv21269], .c 53, .c 3, .c 5, .c 47,
  .c 3, .c 13, .c 733, .c 3, .c 11, .c 7, .c 3, .p pv5 [pv2,pv691,pv2801], .c 5, .c 3, .c 43,
  .c 71, .c 3, .c 5, .c 13, .c 3, .c 31, .c 19, .c 3, .c 7, .p pv11 [pv2,pv3,pv13441], .c 3,
  .p pv2 [pv2,pv967753], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 101, .c 3, .c 227, .c 1399, .c 3,
  .c 83, .p pv3 [pv2,pv3,pv23,pv28051], .c 3, .c 11, .c 5, .c 3, .c 7, .c 37, .c 3, .c 5, .c 223,
  .c 3, .c 23, .c 7, .c 3,
]
private theorem h0473c09 : checkBlock 3870811 128 b0473c09 = true := by
  decide +kernel

private def b0473c10 : List Row := [
  .c 53, .c 857, .c 3, .p pv3 [pv2,pv137,pv883], .c 5, .c 3, .c 19, .p pv19 [pv2,pv3,pv5,pv10753],
  .c 3, .c 5, .c 11, .c 3, .c 7, .c 577, .c 3, .c 41, .c 1871, .c 3, .p pv5 [pv2,pv439,pv4409],
  .c 5, .c 3, .c 11, .p pv17 [pv2,pv3,pv5,pv129037], .c 3, .c 5, .c 19, .c 3, .c 17, .c 29, .c 3,
  .c 13, .p pv7 [pv2,pv3,pv101,pv1597], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv17,pv41,pv2777],
  .c 419, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv139,pv557], .c 11, .c 3, .c 283,
  .p pv3 [pv2,pv3,pv79,pv8167], .c 3, .c 487, .c 5, .c 3, .c 149, .p pv2 [pv2,pv3,pv5,pv43013],
  .c 3, .c 5, .p pv5 [pv2,pv3,pv23,pv7013], .c 3, .c 29, .c 241, .c 3, .c 31, .c 7, .c 3, .c 19,
  .c 5, .c 3, .c 23, .p pv7 [pv2,pv3,pv5,pv1613], .c 3, .c 5, .c 761, .c 3,
  .p pv2 [pv2,pv5,pv7,pv29,pv1907], .c 1303, .c 3, .c 7, .c 11, .c 3, .c 17, .c 5, .c 3, .c 101,
  .c 7, .c 3, .c 5, .c 79, .c 3, .c 11, .c 61, .c 3, .c 43, .c 31, .c 3, .c 787, .c 5, .c 3, .c 7,
  .c 41, .c 3, .c 5, .c 113, .c 3, .p pv17 [pv2,pv5,pv13,pv97,pv307], .c 7, .c 3, .c 1217, .c 53,
  .c 3, .c 13, .c 5, .c 3, .c 139, .c 17, .c 3, .c 5, .c 29, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv41,pv15737], .c 3, .c 11, .c 13, .c 3, .c 1097, .c 5, .c 3,
  .p pv7 [pv2,pv11,pv149,pv1181], .p pv7 [pv2,pv3,pv5,pv32261],
]
private theorem h0473c10 : checkBlock 3871067 128 b0473c10 = true := by
  decide +kernel

private def b0473c11 : List Row := [
  .c 3, .c 5, .c 67, .c 3, .p pv2 [pv2,pv5,pv101,pv3833], .c 43, .c 3, .c 23,
  .p pv3 [pv2,pv3,pv151,pv4273], .c 3, .c 7, .c 5, .c 3, .c 1493, .c 11, .c 3, .c 5, .c 7, .c 3,
  .c 13, .p pv53 [pv2,pv3,pv11,pv58657], .c 3, .c 97, .c 83, .c 3, .c 11, .c 5, .c 3, .c 191,
  .p pv2 [pv2,pv3,pv5,pv113,pv571], .c 3, .c 5, .c 13, .c 3, .p pv31 [pv2,pv5,pv47,pv8237], .c 17,
  .c 3, .p pv2 [pv2,pv541,pv1789], .c 7, .c 3, .c 59, .c 5, .c 3, .c 73, .c 89, .c 3, .c 5, .c 11,
  .c 3, .c 19, .p pv5 [pv2,pv3,pv71693], .c 3, .c 7, .c 23, .c 3, .p pv3 [pv2,pv483929], .c 5,
  .c 3, .c 11, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv607,pv1063], .c 3, .c 1427, .c 433, .c 3,
  .c 349, .c 19, .c 3, .c 157, .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .c 661, .c 3,
  .p pv3 [pv2,pv5,pv96787], .c 7, .c 3, .c 61, .c 151, .c 3, .c 113, .c 5, .c 3,
  .p pv2 [pv2,pv23,pv84163], .p pv17 [pv2,pv3,pv5,pv29,pv89], .c 3, .c 5, .c 41, .c 3, .c 7,
  .c 859, .c 3, .c 13, .c 1109, .c 3, .p pv2 [pv2,pv1117,pv1733], .c 5, .c 3, .c 17, .c 47, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv80657], .c 3, .c 439, .c 13, .c 3, .p pv5 [pv2,pv7,pv17,pv16267], .c 11,
  .c 3, .c 7, .c 5, .c 3, .c 31, .c 97, .c 3, .c 5, .c 7, .c 3, .c 11, .c 19, .c 3, .c 307,
]
private theorem h0473c11 : checkBlock 3871323 128 b0473c11 = true := by
  decide +kernel

private def b0473c12 : List Row := [
  .p pv3 [pv2,pv3,pv47,pv13729], .c 3, .p pv5 [pv2,pv11,pv13,pv13537], .c 5, .c 3, .c 41, .c 43,
  .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv9679], .p pv2 [pv2,pv3,pv7,pv30727], .c 3,
  .p pv5 [pv2,pv37,pv113,pv463], .c 7, .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv83,pv281], .c 13,
  .c 3, .c 5, .c 1163, .c 3, .c 17, .c 101, .c 3, .c 7, .c 59, .c 3, .c 37, .c 5, .c 3, .c 19,
  .c 7, .c 3, .c 5, .p pv19 [pv2,pv3,pv53773], .c 3, .p pv2 [pv2,pv5,pv13,pv14891],
  .p pv3 [pv2,pv3,pv67,pv9631], .c 3, .c 103, .p pv2 [pv2,pv3,pv19,pv16981], .c 3, .c 13, .c 5,
  .c 3, .c 7, .c 11, .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv387169], .c 7, .c 3, .c 593,
  .c 13, .c 3, .c 11, .c 5, .c 3, .c 1291, .c 79, .c 3, .c 5, .c 37, .c 3, .c 7, .c 283, .c 3,
  .c 449, .c 67, .c 3, .c 17, .c 5, .c 3, .c 163, .c 499, .c 3, .c 5, .c 11, .c 3, .c 13, .c 41,
  .c 3, .c 59, .p pv3 [pv2,pv3,pv11,pv5333], .c 3, .c 7, .c 5, .c 3, .c 11, .c 181, .c 3, .c 5,
  .c 7, .c 3, .p pv2 [pv2,pv5,pv11,pv17599], .p pv3 [pv2,pv3,pv19,pv11321], .c 3,
  .p pv2 [pv2,pv1935893], .c 109, .c 3, .c 337, .c 5, .c 3, .c 1933, .c 17, .c 3, .c 5, .c 31,
  .c 3, .p pv2 [pv2,pv5,pv313,pv1237], .c 11, .c 3, .p pv3 [pv2,pv13,pv59,pv631], .c 7, .c 3,
  .p pv5 [pv2,pv1935911], .c 5, .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv129061], .c 3,
]
private theorem h0473c12 : checkBlock 3871579 128 b0473c12 = true := by
  decide +kernel

private def b0473c13 : List Row := [
  .c 5, .c 991, .c 3, .p pv3 [pv2,pv5,pv7,pv3457], .c 23, .c 3, .c 7, .c 43, .c 3, .c 61, .c 5,
  .c 3, .c 1049, .c 7, .c 3, .c 5, .c 83, .c 3, .p pv11 [pv2,pv5,pv387187], .c 103, .c 3, .c 19,
  .c 11, .c 3, .p pv2 [pv2,pv7,pv39509], .c 5, .c 3, .c 7, .c 1693, .c 3, .c 5, .c 467, .c 3,
  .c 11, .c 7, .c 3, .c 13, .p pv2 [pv2,pv3,pv35851], .c 3, .c 173, .c 5, .c 3,
  .p pv7 [pv2,pv1069,pv1811], .p pv37 [pv2,pv3,pv5,pv13,pv17,pv73], .c 3, .c 5, .c 683, .c 3,
  .c 7, .c 13, .c 3, .c 17, .c 37, .c 3, .c 199, .c 5, .c 3, .c 97, .c 571, .c 3, .c 5, .c 773,
  .c 3, .p pv3 [pv2,pv5,pv96799], .c 509, .c 3, .c 11, .p pv7 [pv2,pv3,pv53,pv761], .c 3, .c 7,
  .c 5, .c 3, .c 419, .c 23, .c 3, .c 5, .c 7, .c 3, .c 19, .c 29, .c 3, .c 67, .c 41, .c 3,
  .c 409, .c 5, .c 3, .c 107, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv8963], .c 3, .c 43,
  .p pv3 [pv2,pv3,pv7,pv11,pv17,pv29], .c 3, .c 23, .c 7, .c 3, .c 11, .c 5, .c 3, .c 17,
  .p pv19 [pv2,pv3,pv5,pv41,pv787], .c 3, .c 5, .p pv5 [pv2,pv3,pv97,pv6653], .c 3, .c 29, .c 607,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv113,pv5711], .c 3, .c 13, .c 5, .c 3, .c 463, .c 7, .c 3, .c 5,
  .c 11, .c 3, .c 41, .c 1777, .c 3, .c 37, .c 13,
]
private theorem h0473c13 : checkBlock 3871835 128 b0473c13 = true := by
  decide +kernel

private def b0473c14 : List Row := [
  .c 3, .c 151, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv12907], .c 3, .c 5, .c 17, .c 3, .c 59,
  .c 7, .c 3, .c 31, .c 23, .c 3, .c 89, .c 5, .c 3, .p pv3 [pv2,pv13,pv179], .c 67, .c 3, .c 5,
  .c 487, .c 3, .c 7, .c 11, .c 3, .c 241, .c 263, .c 3, .p pv3 [pv2,pv484019], .c 5, .c 3,
  .c 193, .c 37, .c 3, .c 5, .c 13, .c 3, .c 113, .c 347, .c 3, .c 251, .c 31, .c 3, .c 7, .c 5,
  .c 3, .c 47, .c 307, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv19,pv1019],
  .p pv2 [pv2,pv3,pv645367], .c 3, .p pv5 [pv2,pv13,pv148931], .c 11, .c 3, .c 547, .c 5, .c 3,
  .c 13, .p pv2 [pv2,pv3,pv5,pv11,pv5867], .c 3, .c 5, .c 233, .c 3, .c 11, .c 53, .c 3,
  .p pv2 [pv2,pv43,pv47,pv479], .c 7, .c 3, .c 17, .c 5, .c 3, .p pv3 [pv2,pv157,pv3083], .c 1877,
  .c 3, .c 5, .c 19, .c 3, .c 311, .c 443, .c 3, .c 7, .c 71, .c 3, .p pv3 [pv2,pv31,pv37,pv211],
  .c 5, .c 3, .c 43, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv41,pv53], .c 3,
  .p pv2 [pv2,pv5,pv593,pv653], .p pv5 [pv2,pv3,pv523,pv617], .c 3, .c 11,
  .p pv2 [pv2,pv3,pv645383], .c 3, .c 23, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv46099], .c 3, .c 613, .c 7, .c 3, .c 41, .p pv19 [pv2,pv3,pv17,pv9491],
  .c 3, .c 19, .c 5, .c 3, .c 53, .c 11, .c 3, .c 5,
]
private theorem h0473c14 : checkBlock 3872091 128 b0473c14 = true := by
  decide +kernel

private def b0473c15 : List Row := [
  .c 59, .c 3, .c 7, .c 1039, .c 3, .c 127, .p pv7 [pv2,pv3,pv7,pv73,pv421], .c 3, .c 11, .c 5,
  .c 3, .c 331, .c 19, .c 3, .c 5, .c 47, .c 3, .p pv2 [pv2,pv5,pv193619], .c 37, .c 3,
  .p pv2 [pv2,pv7,pv276599], .p pv23 [pv2,pv3,pv13,pv103,pv241], .c 3, .c 7, .c 5, .c 3, .c 29,
  .c 13, .c 3, .c 5, .c 7, .c 3, .c 71, .c 17, .c 3, .p pv3 [pv2,pv121013], .c 439, .c 3,
  .p pv5 [pv2,pv79,pv24509], .c 5, .c 3, .c 11, .c 73, .c 3, .c 5, .c 107, .c 3, .c 23, .c 109,
  .c 3, .c 17, .c 7, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv31,pv62459], .c 281, .c 3, .c 5,
  .c 337, .c 3, .c 47, .c 11, .c 3, .c 7, .c 13, .c 3, .c 211, .c 5, .c 3, .c 31, .c 7, .c 3,
  .c 5, .c 1171, .c 3, .c 79, .p pv3 [pv2,pv3,pv71713], .c 3, .p pv5 [pv2,pv11,pv176023], .c 1063,
  .c 3, .c 383, .c 5, .c 3, .c 7, .p pv23 [pv2,pv3,pv5,pv31,pv347], .c 3, .c 5,
  .p pv7 [pv2,pv3,pv7,pv92203], .c 3, .c 13, .c 7, .c 3, .c 43, .c 11, .c 3,
  .p pv5 [pv2,pv19,pv101,pv1009], .c 5, .c 3, .c 17, .c 31, .c 3, .c 5, .c 13, .c 3, .c 7, .c 167,
  .c 3, .p pv5 [pv2,pv17,pv113899], .c 1621, .c 3, .c 29, .c 5, .c 3, .c 23, .c 293, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv645431], .c 3, .p pv13 [pv2,pv5,pv271,pv1429], .c 521, .c 3, .c 503, .c 19,
  .c 3,
]
private theorem h0473c15 : checkBlock 3872347 128 b0473c15 = true := by
  decide +kernel

private def b0473c16 : List Row := [
  .c 7, .c 5, .c 3, .c 13, .c 127, .c 3, .c 5, .c 7, .c 3, .c 937, .c 43, .c 3, .c 11, .c 241,
  .c 3, .c 1103, .c 5, .c 3, .c 1117, .c 1307, .c 3, .c 5, .p pv3 [pv2,pv3,pv61,pv3527], .c 3,
  .c 17, .c 1021, .c 3, .c 53, .c 7, .c 3, .c 1949, .c 5, .c 3, .p pv2 [pv2,pv17,pv56951], .c 11,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv181,pv1783], .c 3, .p pv3 [pv2,pv5,pv7,pv13831], .c 809, .c 3,
  .c 7, .c 29, .c 3, .c 11, .c 5, .c 3, .c 1013, .c 7, .c 3, .c 5, .c 61, .c 3, .c 1367, .c 13,
  .c 3, .c 23, .c 17, .c 3, .c 73, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv167,pv773], .c 3, .c 5,
  .c 11, .c 3, .c 1861, .c 7, .c 3, .c 29, .c 313, .c 3, .c 17, .c 5, .c 3, .c 11,
  .p pv19 [pv2,pv3,pv5,pv59,pv547], .c 3, .c 5, .p pv3 [pv2,pv3,pv71,pv9091], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv11953], .c 3, .p pv3 [pv2,pv29,pv16693], .c 421, .c 3, .c 857, .c 5, .c 3,
  .c 19, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv73,pv4421], .c 3, .c 67, .c 11, .c 3,
  .p pv5 [pv2,pv7,pv276629], .c 23, .c 3, .c 7, .c 5, .c 3, .c 41, .c 17, .c 3, .c 5, .c 7, .c 3,
  .c 467, .p pv7 [pv2,pv3,pv23,pv877], .c 3, .c 71, .p pv3 [pv2,pv3,pv17,pv43,pv883], .c 3, .c 13,
  .c 5, .c 3, .c 113, .p pv2 [pv2,pv3,pv5,pv25819], .c 3, .c 5, .c 181,
]
private theorem h0473c16 : checkBlock 3872603 128 b0473c16 = true := by
  decide +kernel

private def b0473c17 : List Row := [
  .c 3, .c 31, .c 29, .c 3, .c 347, .c 7, .c 3, .p pv3 [pv2,pv17,pv28477], .c 5, .c 3, .c 109,
  .c 43, .c 3, .c 5, .p pv5 [pv2,pv3,pv645481], .c 3, .c 11, .p pv2 [pv2,pv3,pv29,pv31,pv359],
  .c 3, .c 7, .p pv2 [pv2,pv3,pv215161], .c 3, .c 19, .c 5, .c 3, .c 617, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv107581], .c 3, .c 13, .c 17, .c 3, .c 1153, .p pv13 [pv2,pv3,pv40343], .c 3,
  .p pv2 [pv2,pv7,pv138319], .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 13, .c 3, .c 61, .c 7, .c 3,
  .c 11, .p pv3 [pv2,pv3,pv645493], .c 3, .p pv2 [pv2,pv113,pv17137], .c 5, .c 3,
  .p pv3 [pv2,pv11,pv4001], .p pv2 [pv2,pv3,pv5,pv23,pv1871], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv80687], .c 3, .c 7, .c 41, .c 3, .c 1069, .c 1523, .c 3, .c 23, .c 5, .c 3,
  .c 13, .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv103,pv2089], .c 3, .p pv2 [pv2,pv5,pv43,pv9007],
  .c 89, .c 3, .c 19, .c 541, .c 3, .c 7, .c 5, .c 3, .c 83, .c 331, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv48413], .c 163, .c 3, .c 31, .c 37, .c 3, .c 43, .c 5, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv5,pv21517], .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv387307], .c 61, .c 3,
  .c 13, .c 7, .c 3, .c 619, .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv13,pv9931], .c 3, .c 5,
  .c 109, .c 3, .p pv3 [pv2,pv5,pv7,pv11,pv503], .c 13, .c 3, .c 7, .c 31, .c 3, .c 97,
]
private theorem h0473c17 : checkBlock 3872859 128 b0473c17 = true := by
  decide +kernel

private def b0473c18 : List Row := [
  .c 5, .c 3, .c 127, .c 7, .c 3, .c 5, .c 17, .c 3, .c 19, .c 11, .c 3, .c 199, .c 43, .c 3,
  .c 1471, .c 5, .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv19,pv151], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv941], .c 3, .c 17, .c 7, .c 3, .c 293, .c 19, .c 3, .c 59, .c 5, .c 3,
  .p pv2 [pv2,pv17,pv6701], .c 13, .c 3, .c 5, .c 53, .c 3, .c 7, .p pv5 [pv2,pv3,pv71,pv2273],
  .c 3, .c 37, .c 11, .c 3, .c 67, .c 5, .c 3, .p pv3 [pv2,pv484151], .c 29, .c 3, .c 5, .c 197,
  .c 3, .c 11, .c 23, .c 3, .c 1123, .c 17, .c 3, .c 7, .c 5, .c 3, .p pv13 [pv2,pv499,pv3881],
  .c 1223, .c 3, .c 5, .c 7, .c 3, .c 359, .c 719, .c 3, .p pv3 [pv2,pv61,pv7937], .c 13, .c 3,
  .c 17, .c 5, .c 3, .c 23, .c 37, .c 3, .c 5, .c 131, .c 3, .p pv3 [pv2,pv5,pv17,pv89], .c 19,
  .c 3, .c 11, .c 7, .c 3, .c 53, .c 5, .c 3, .p pv2 [pv2,pv11,pv13,pv29,pv467], .c 113, .c 3,
  .c 5, .c 73, .c 3, .c 13, .p pv7 [pv2,pv3,pv4483], .c 3, .c 7, .c 971, .c 3,
  .p pv2 [pv2,pv461,pv4201], .c 5, .c 3, .p pv3 [pv2,pv242083], .c 7, .c 3, .c 5, .c 13, .c 3,
  .c 1409, .p pv3 [pv2,pv3,pv11,pv58687], .c 3, .c 157, .p pv11 [pv2,pv3,pv17,pv6329], .c 3,
  .c 11, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv10247], .c 3,
]
private theorem h0473c18 : checkBlock 3873115 128 b0473c18 = true := by
  decide +kernel

private def b0473c19 : List Row := [
  .p pv2 [pv2,pv5,pv79,pv4903], .c 7, .c 3, .c 1283, .p pv2 [pv2,pv3,pv19,pv61,pv557], .c 3,
  .p pv5 [pv2,pv17,pv37,pv3079], .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv129113], .c 3, .c 5,
  .c 11, .c 3, .c 7, .c 271, .c 3, .c 23, .c 59, .c 3, .p pv2 [pv2,pv968353], .c 5, .c 3, .c 11,
  .c 283, .c 3, .c 5, .p pv2 [pv2,pv3,pv645571], .c 3, .p pv11 [pv2,pv5,pv11,pv23,pv1531], .c 17,
  .c 3, .p pv2 [pv2,pv7,pv138337], .c 61, .c 3, .c 7, .c 5, .c 3, .c 79, .c 101, .c 3, .c 5, .c 7,
  .c 3, .p pv2 [pv2,pv5,pv293,pv661], .c 11, .c 3, .c 13, .c 353, .c 3, .c 19, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv337,pv821], .c 31, .c 3, .c 5, .p pv3 [pv2,pv3,pv645581], .c 3,
  .p pv2 [pv2,pv5,pv509,pv761], .c 13, .c 3, .p pv3 [pv2,pv11,pv44017], .c 7, .c 3, .c 773, .c 5,
  .c 3, .p pv2 [pv2,pv968377], .c 19, .c 3, .c 5, .p pv2 [pv2,pv3,pv41,pv7873], .c 3, .c 103,
  .c 449, .c 3, .c 7, .c 11, .c 3, .c 109, .c 5, .c 3, .c 131, .c 7, .c 3, .c 5, .c 71, .c 3,
  .c 11, .c 149, .c 3, .c 41, .c 29, .c 3, .c 641, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5,
  .p pv29 [pv2,pv3,pv7,pv23057], .c 3, .c 181, .c 7, .c 3, .c 19, .c 647, .c 3, .c 241, .c 5,
  .c 3, .c 47, .c 1583, .c 3, .c 5, .c 79, .c 3, .c 7, .c 587, .c 3, .c 11, .c 1447, .c 3, .c 13,
  .c 5,
]
private theorem h0473c19 : checkBlock 3873371 128 b0473c19 = true := by
  decide +kernel

private def b0473c20 : List Row := [
  .c 3, .p pv2 [pv2,pv11,pv88037], .p pv3 [pv2,pv3,pv5,pv129121], .c 3, .c 5, .c 17, .c 3, .c 37,
  .c 173, .c 3, .p pv13 [pv2,pv7,pv29,pv47], .c 13, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv751,pv2579], .c 11, .c 3, .c 5, .c 7, .c 3, .c 17, .c 479, .c 3,
  .p pv2 [pv2,pv968419], .p pv3 [pv2,pv3,pv37,pv17449], .c 3, .c 11, .c 5, .c 3, .c 71,
  .p pv2 [pv2,pv3,pv5,pv14347], .c 3, .c 5, .p pv19 [pv2,pv3,pv40351], .c 3, .c 13, .c 193, .c 3,
  .p pv2 [pv2,pv23,pv84211], .c 7, .c 3, .p pv3 [pv2,pv239,pv1013], .c 5, .c 3,
  .p pv11 [pv2,pv1936859], .c 41, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv7,pv55339], .c 29,
  .c 3, .c 7, .c 17, .c 3, .p pv5 [pv2,pv1936871], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 881,
  .c 3, .c 257, .c 59, .c 3, .p pv5 [pv2,pv13,pv148991], .p pv23 [pv2,pv3,pv161407], .c 3, .c 17,
  .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv21521], .c 3, .c 5, .c 47, .c 3, .c 29, .c 7, .c 3,
  .c 907, .p pv3 [pv2,pv3,pv23,pv3119], .c 3, .c 41, .c 5, .c 3, .p pv3 [pv2,pv197,pv1229],
  .p pv2 [pv2,pv3,pv5,pv129127], .c 3, .c 5, .p pv7 [pv2,pv3,pv173,pv311], .c 3, .c 7, .c 53,
  .c 3, .c 43, .p pv2 [pv2,pv3,pv7,pv107,pv431], .c 3, .p pv3 [pv2,pv484229], .c 5, .c 3,
  .p pv7 [pv2,pv739,pv2621], .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv645641], .c 3, .c 149, .c 19,
  .c 3, .c 13, .c 11, .c 3, .c 7, .c 5, .c 3, .c 269, .p pv3 [pv2,pv3,pv5,pv7,pv11,pv13,pv43],
  .c 3, .c 5, .c 7, .c 3, .c 11,
]
private theorem h0473c20 : checkBlock 3873627 128 b0473c20 = true := by
  decide +kernel

private def b0473c21 : List Row := [
  .c 13, .c 3, .c 1627, .c 97, .c 3, .p pv2 [pv2,pv11,pv17,pv5179], .c 5, .c 3, .c 167,
  .p pv7 [pv2,pv3,pv5,pv37,pv349], .c 3, .c 5, .c 29, .c 3, .p pv13 [pv2,pv5,pv19,pv20389], .c 23,
  .c 3, .c 829, .c 7, .c 3, .c 79, .c 5, .c 3, .c 19, .p pv2 [pv2,pv3,pv5,pv139,pv929], .c 3,
  .c 5, .c 37, .c 3, .p pv2 [pv2,pv5,pv7,pv59,pv67], .c 17, .c 3, .c 7, .c 137, .c 3, .c 1163,
  .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 19, .c 3, .c 1721, .c 71, .c 3, .c 17, .c 113, .c 3,
  .p pv5 [pv2,pv7,pv23,pv53,pv227], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv15373], .c 3, .c 313, .c 7, .c 3, .c 67,
  .p pv29 [pv2,pv3,pv31,pv41,pv127], .c 3, .c 11, .c 5, .c 3, .c 1429, .c 163, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv13,pv49667], .c 3, .c 7, .c 307, .c 3, .c 73, .c 13, .c 3, .c 19, .c 5, .c 3,
  .c 41, .c 23, .c 3, .c 5, .c 11, .c 3, .c 401, .c 131, .c 3, .p pv2 [pv2,pv7,pv167,pv1657],
  .c 47, .c 3, .c 7, .c 5, .c 3, .c 11, .c 19, .c 3, .c 5, .c 7, .c 3, .c 13,
  .p pv17 [pv2,pv3,pv113,pv2857], .c 3, .c 23, .p pv2 [pv2,pv3,pv645683], .c 3,
  .p pv5 [pv2,pv1937051], .c 5, .c 3, .p pv2 [pv2,pv7,pv83,pv1667],
  .p pv3 [pv2,pv3,pv5,pv29,pv61,pv73], .c 3, .c 5, .c 13, .c 3, .c 661, .c 11, .c 3, .c 311, .c 7,
  .c 3, .p pv2 [pv2,pv31,pv157,pv199], .c 5, .c 3,
]
private theorem h0473c21 : checkBlock 3873883 128 b0473c21 = true := by
  decide +kernel

private def b0473c22 : List Row := [
  .c 29, .c 53, .c 3, .c 5, .c 17, .c 3, .p pv7 [pv2,pv5,pv7,pv11069],
  .p pv11 [pv2,pv3,pv337,pv479], .c 3, .c 7, .c 37, .c 3, .c 31, .c 5, .c 3, .c 13, .c 7, .c 3,
  .c 5, .c 947, .c 3, .c 17, .c 73, .c 3, .c 109, .c 11, .c 3, .p pv3 [pv2,pv7,pv34591], .c 5,
  .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv11,pv587], .c 3, .c 5, .c 151, .c 3, .c 11, .c 7, .c 3,
  .c 797, .p pv2 [pv2,pv3,pv645703], .c 3, .c 137, .c 5, .c 3, .p pv2 [pv2,pv968557],
  .p pv3 [pv2,pv3,pv5,pv4783], .c 3, .c 5, .p pv5 [pv2,pv3,pv499,pv647], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv103,pv6269], .c 3, .c 13, .c 17, .c 3, .c 263, .c 5, .c 3, .c 89, .c 659,
  .c 3, .c 5, .c 1619, .c 3, .c 19, .c 13, .c 3, .c 11, .p pv53 [pv2,pv3,pv645713], .c 3, .c 7,
  .c 5, .c 3, .c 157, .c 1291, .c 3, .c 5, .c 7, .c 3, .c 809, .c 1709, .c 3, .c 37, .c 19, .c 3,
  .c 29, .c 5, .c 3, .p pv7 [pv2,pv7,pv31,pv79,pv113], .c 11, .c 3, .c 5, .c 23, .c 3, .c 199,
  .p pv2 [pv2,pv3,pv7,pv11,pv599], .c 3, .p pv3 [pv2,pv41,pv2953], .c 7, .c 3, .c 11, .c 5, .c 3,
  .c 31, .c 13, .c 3, .c 5, .c 83, .c 3, .p pv3 [pv2,pv5,pv7,pv101,pv137], .c 107, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv17,pv1187], .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv1301,pv1489], .c 7, .c 3,
  .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv13,pv29803], .p pv5 [pv2,pv3,pv1993],
]
private theorem h0473c22 : checkBlock 3874139 128 b0473c22 = true := by
  decide +kernel

private def b0473c23 : List Row := [
  .c 3, .c 79, .c 71, .c 3, .c 13, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv7,pv13,pv887], .c 3, .c 449, .c 7, .c 3, .c 701, .c 13, .c 3,
  .p pv3 [pv2,pv30269], .c 5, .c 3, .p pv7 [pv2,pv311,pv6229], .p pv19 [pv2,pv3,pv5,pv83,pv389],
  .c 3, .c 5, .c 149, .c 3, .c 7, .c 11, .c 3, .c 409, .c 41, .c 3, .c 421, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv74509], .c 59, .c 3, .c 5, .c 1607, .c 3, .c 13, .c 911, .c 3, .c 17, .c 337,
  .c 3, .c 7, .c 5, .c 3, .c 19, .p pv13 [pv2,pv3,pv5,pv7,pv41], .c 3, .c 5, .c 7, .c 3, .c 23,
  .p pv5 [pv2,pv3,pv53,pv1523], .c 3, .c 379, .c 11, .c 3, .c 83, .c 5, .c 3, .c 37,
  .p pv11 [pv2,pv3,pv5,pv11,pv59,pv199], .c 3, .c 5, .c 19, .c 3, .c 11, .c 67, .c 3,
  .p pv2 [pv2,pv13,pv149021], .c 7, .c 3, .c 283, .c 5, .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv1009],
  .c 3, .c 5, .c 167, .c 3, .p pv2 [pv2,pv5,pv7,pv55351], .p pv2 [pv2,pv3,pv13,pv17,pv487], .c 3,
  .c 7, .p pv2 [pv2,pv3,pv645763], .c 3, .p pv5 [pv2,pv41,pv47251], .c 5, .c 3, .c 17, .c 7, .c 3,
  .c 5, .c 31, .c 3, .c 43, .c 23, .c 3, .c 11, .c 503, .c 3, .c 19, .c 5, .c 3, .c 7, .c 73,
  .c 3, .c 5, .c 313, .c 3, .c 479, .c 7, .c 3, .c 13, .p pv13 [pv2,pv3,pv733,pv881], .c 3,
  .c 127, .c 5, .c 3, .c 23,
]
private theorem h0473c23 : checkBlock 3874395 128 b0473c23 = true := by
  decide +kernel

private def b0473c24 : List Row := [
  .c 11, .c 3, .c 5, .c 17, .c 3, .c 7, .c 13, .c 3, .c 181, .p pv2 [pv2,pv3,pv7,pv193,pv239],
  .c 3, .c 11, .c 5, .c 3, .p pv7 [pv2,pv1937339], .c 173, .c 3, .c 5, .c 43, .c 3, .c 17,
  .p pv23 [pv2,pv3,pv322891], .c 3, .p pv3 [pv2,pv7,pv69191], .c 467, .c 3, .c 7, .c 5, .c 3,
  .c 281, .p pv11 [pv2,pv3,pv5,pv7,pv18451], .c 3, .c 5, .c 7, .c 3, .c 31,
  .p pv2 [pv2,pv3,pv645787], .c 3, .c 19, .c 199, .c 3, .p pv2 [pv2,pv109,pv8887], .c 5, .c 3,
  .c 11, .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv19,pv41,pv829], .c 3, .c 37,
  .p pv37 [pv2,pv3,pv7,pv31], .c 3, .c 103, .c 7, .c 3, .p pv2 [pv2,pv97,pv19973], .c 5, .c 3,
  .c 967, .c 137, .c 3, .c 5, .c 29, .c 3, .c 61, .c 11, .c 3, .c 7, .c 257, .c 3, .c 13, .c 5,
  .c 3, .p pv11 [pv2,pv241,pv8039], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv29,pv571], .c 3,
  .c 67, .c 179, .c 3, .c 191, .c 13, .c 3, .p pv7 [pv2,pv7,pv19,pv2081], .c 5, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv5,pv53,pv2437], .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv163,pv283], .c 3, .c 19,
  .c 7, .c 3, .c 463, .c 11, .c 3, .p pv2 [pv2,pv968713], .c 5, .c 3, .c 43, .c 17, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv409,pv1579], .c 3, .c 7, .c 1117, .c 3, .p pv2 [pv2,pv31,pv31249], .c 19,
  .c 3, .c 53, .c 5, .c 3, .p pv3 [pv2,pv484361], .p pv2 [pv2,pv3,pv5,pv227,pv569], .c 3, .c 5,
  .c 13, .c 3, .c 167, .c 61, .c 3,
]
private theorem h0473c24 : checkBlock 3874651 128 b0473c24 = true := by
  decide +kernel

private def b0473c25 : List Row := [
  .c 31, .c 229, .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv1937459], .c 443, .c 3, .c 5, .c 7, .c 3,
  .c 599, .p pv5 [pv2,pv3,pv35879], .c 3, .c 11, .p pv2 [pv2,pv3,pv31,pv83,pv251], .c 3, .c 59,
  .c 5, .c 3, .c 13, .c 29, .c 3, .c 5, .p pv2 [pv2,pv3,pv97,pv3329], .c 3, .c 1531, .c 17, .c 3,
  .c 71, .c 7, .c 3, .c 37, .c 5, .c 3, .p pv2 [pv2,pv1937489], .c 11, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv73,pv983], .c 3, .c 769, .c 19, .c 3, .c 7, .c 163, .c 3, .c 11, .c 5, .c 3,
  .c 29, .c 7, .c 3, .c 5, .c 23, .c 3, .c 83, .c 233, .c 3, .c 13, .c 79, .c 3, .c 41, .c 5,
  .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv13,pv23], .c 3, .c 5, .c 11, .c 3,
  .p pv11 [pv2,pv5,pv19,pv4079], .c 7, .c 3, .p pv3 [pv2,pv47,pv5153], .c 73, .c 3, .c 23, .c 5,
  .c 3, .c 11, .c 223, .c 3, .c 5, .c 1759, .c 3, .c 7, .c 757, .c 3,
  .p pv5 [pv2,pv23,pv61,pv1381], .p pv37 [pv2,pv3,pv7,pv19,pv607], .c 3, .c 31, .c 5, .c 3, .c 17,
  .p pv7 [pv2,pv3,pv5,pv12917], .c 3, .c 5, .c 19, .c 3, .c 131, .c 11, .c 3, .c 43, .c 283, .c 3,
  .c 7, .c 5, .c 3, .c 563, .c 13, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv193757],
  .p pv3 [pv2,pv3,pv645857], .c 3, .c 61, .c 89, .c 3, .c 367, .c 5, .c 3,
  .p pv13 [pv2,pv7,pv37,pv7481], .p pv47 [pv2,pv3,pv5,pv43,pv751],
]
private theorem h0473c25 : checkBlock 3874907 128 b0473c25 = true := by
  decide +kernel

private def b0473c26 : List Row := [
  .c 3, .c 5, .c 17, .c 3, .c 179, .p pv17 [pv2,pv3,pv7,pv46133], .c 3, .p pv3 [pv2,pv484397],
  .c 7, .c 3, .c 13, .c 5, .c 3, .c 251, .c 1567, .c 3, .c 5, .c 41, .c 3, .c 11, .c 43, .c 3,
  .c 7, .c 13, .c 3, .c 67, .c 5, .c 3, .c 107, .c 7, .c 3, .c 5, .c 1439, .c 3, .c 157, .c 1153,
  .c 3, .c 1873, .p pv3 [pv2,pv3,pv41,pv59,pv89], .c 3, .p pv2 [pv2,pv7,pv131,pv2113], .c 5, .c 3,
  .c 7, .c 71, .c 3, .c 5, .c 1019, .c 3, .c 13, .c 7, .c 3, .c 11, .c 17, .c 3,
  .p pv3 [pv2,pv103,pv4703], .c 5, .c 3, .c 31, .p pv29 [pv2,pv3,pv5,pv67,pv241], .c 3, .c 5,
  .c 13, .c 3, .c 7, .c 23, .c 3, .c 19, .c 29, .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv968827],
  .c 11, .c 3, .c 5, .p pv11 [pv2,pv3,pv19,pv23,pv739], .c 3, .p pv3 [pv2,pv5,pv17,pv41,pv139],
  .p pv2 [pv2,pv3,pv11,pv71,pv827], .c 3, .c 89, .p pv7 [pv2,pv3,pv29], .c 3, .c 7, .c 5, .c 3,
  .c 13, .c 31, .c 3, .c 5, .c 7, .c 3, .c 73, .c 83, .c 3, .c 29, .p pv3 [pv2,pv3,pv645893],
  .c 3, .p pv2 [pv2,pv23,pv84247], .c 5, .c 3, .p pv3 [pv2,pv7,pv69203], .c 17, .c 3, .c 5, .c 11,
  .c 3, .p pv2 [pv2,pv5,pv37,pv5237], .p pv3 [pv2,pv3,pv7,pv30757], .c 3,
  .p pv2 [pv2,pv29,pv109,pv613], .c 7, .c 3, .c 71, .c 5, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv5,pv2153], .c 3, .c 5, .p pv3 [pv2,pv3,pv645901], .c 3, .c 19, .c 53, .c 3,
  .c 7,
]
private theorem h0473c26 : checkBlock 3875163 128 b0473c26 = true := by
  decide +kernel

private def b0473c27 : List Row := [
  .c 1699, .c 3, .c 919, .c 5, .c 3, .p pv2 [pv2,pv968857], .c 7, .c 3, .c 5, .c 211, .c 3, .c 97,
  .c 11, .c 3, .p pv5 [pv2,pv1937723], .c 19, .c 3, .p pv5 [pv2,pv7,pv61,pv2269], .c 5, .c 3,
  .c 7, .c 43, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv53,pv1741], .c 3, .c 101, .c 7, .c 3, .c 23,
  .c 47, .c 3, .c 269, .c 5, .c 3, .c 233, .c 37, .c 3, .c 5, .c 73, .c 3, .c 7, .c 79, .c 3,
  .c 17, .c 11, .c 3, .c 61, .c 5, .c 3, .c 53, .c 13, .c 3, .c 5, .c 31, .c 3, .c 11, .c 59,
  .c 3, .p pv3 [pv2,pv7,pv34603], .p pv2 [pv2,pv3,pv97,pv6659], .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv67,pv14461], .p pv3 [pv2,pv3,pv5,pv7,pv3691], .c 3, .c 5, .c 7, .c 3, .c 113,
  .c 19, .c 3, .p pv5 [pv2,pv41,pv151,pv313], .c 23, .c 3, .c 13, .c 5, .c 3, .c 659, .c 103,
  .c 3, .c 5, .c 353, .c 3, .p pv11 [pv2,pv5,pv43,pv9013], .c 137, .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv37,pv83,pv631], .c 5, .c 3, .c 17, .c 907, .c 3, .c 5, .p pv5 [pv2,pv3,pv13457],
  .c 3, .c 1451, .p pv3 [pv2,pv3,pv645937], .c 3, .c 7, .p pv2 [pv2,pv3,pv322969], .c 3, .c 43,
  .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 29, .c 3, .c 13, .p pv7 [pv2,pv3,pv11,pv9787], .c 3,
  .c 1571, .c 127, .c 3, .c 11, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv43063], .c 3,
]
private theorem h0473c27 : checkBlock 3875419 128 b0473c27 = true := by
  decide +kernel

private def b0473c28 : List Row := [
  .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv24223], .c 7, .c 3, .c 1223, .c 41, .c 3,
  .p pv2 [pv2,pv563,pv1721], .c 5, .c 3, .p pv2 [pv2,pv1063,pv1823], .c 1097, .c 3, .c 5, .c 11,
  .c 3, .c 7, .c 31, .c 3, .c 151, .c 43, .c 3, .c 1657, .c 5, .c 3, .c 11, .c 53, .c 3, .c 5,
  .c 139, .c 3, .p pv3 [pv2,pv5,pv11,pv79,pv223], .p pv3 [pv2,pv3,pv13,pv5521], .c 3,
  .p pv2 [pv2,pv7,pv276839], .c 67, .c 3, .c 7, .c 5, .c 3, .c 977, .c 47, .c 3, .c 5, .c 7, .c 3,
  .c 41, .c 11, .c 3, .c 1481, .c 17, .c 3, .c 433, .c 5, .c 3, .c 73, .c 19, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv17,pv2111], .c 3, .c 991, .p pv5 [pv2,pv3,pv7,pv13183], .c 3, .c 13, .c 7,
  .c 3, .c 17, .c 5, .c 3, .c 71, .c 29, .c 3, .c 5, .p pv2 [pv2,pv3,pv193,pv3347], .c 3, .c 263,
  .c 13, .c 3, .c 7, .c 11, .c 3, .c 373, .c 5, .c 3, .c 601, .c 7, .c 3, .c 5, .c 1129, .c 3,
  .c 11, .c 239, .c 3, .c 19, .p pv2 [pv2,pv3,pv23,pv31,pv151], .c 3, .p pv3 [pv2,pv7,pv11,pv13],
  .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 59, .c 3, .c 23, .c 7, .c 3, .c 131, .c 31, .c 3,
  .c 167, .c 5, .c 3, .p pv2 [pv2,pv29,pv33413], .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv29363],
  .c 3, .c 7, .c 199, .c 3, .c 11, .p pv11 [pv2,pv3,pv7,pv23071],
]
private theorem h0473c28 : checkBlock 3875675 128 b0473c28 = true := by
  decide +kernel

private def b0473c29 : List Row := [
  .c 3, .p pv2 [pv2,pv17,pv56999], .c 5, .c 3, .p pv2 [pv2,pv11,pv176179], .c 821, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv59,pv10949], .c 3, .p pv7 [pv2,pv5,pv13,pv67,pv89], .c 523, .c 3,
  .p pv2 [pv2,pv7,pv138427], .c 317, .c 3, .c 7, .c 5, .c 3, .c 983, .c 11, .c 3, .c 5, .c 7,
  .c 3, .c 19, .c 17, .c 3, .p pv2 [pv2,pv1937993], .c 13, .c 3, .c 11, .c 5, .c 3, .c 613, .c 61,
  .c 3, .c 5, .p pv7 [pv2,pv3,pv23,pv28087], .c 3, .p pv2 [pv2,pv5,pv331,pv1171], .c 113, .c 3,
  .c 17, .c 7, .c 3, .c 31, .c 5, .c 3, .c 23, .p pv3 [pv2,pv3,pv5,pv43067], .c 3, .c 5, .c 11,
  .c 3, .c 13, .c 47, .c 3, .c 7, .c 53, .c 3, .c 29, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 13,
  .c 3, .c 947, .p pv5 [pv2,pv3,pv161503], .c 3, .c 101, .p pv3 [pv2,pv3,pv646013], .c 3, .c 37,
  .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv47,pv2749], .c 3, .c 5, .c 293, .c 3,
  .p pv2 [pv2,pv5,pv83,pv467], .c 7, .c 3, .p pv2 [pv2,pv13,pv43,pv3467],
  .p pv2 [pv2,pv3,pv323009], .c 3, .c 271, .c 5, .c 3, .c 13, .c 23, .c 3, .c 5, .c 641, .c 3,
  .c 7, .c 19, .c 3, .c 47, .c 1901, .c 3, .p pv5 [pv2,pv1938071], .c 5, .c 3, .c 43, .c 67, .c 3,
  .c 5, .c 37, .c 3, .p pv3 [pv2,pv5,pv12113], .c 557, .c 3, .c 23, .c 11, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv31,pv101,pv619], .c 41, .c 3, .c 5,
]
private theorem h0473c29 : checkBlock 3875931 128 b0473c29 = true := by
  decide +kernel

private def b0473c30 : List Row := [
  .c 7, .c 3, .c 11, .c 251, .c 3, .c 13, .c 103, .c 3, .p pv2 [pv2,pv11,pv176191], .c 5, .c 3,
  .c 19, .c 857, .c 3, .c 5, .c 89, .c 3, .c 17, .c 13, .c 3, .c 29, .c 7, .c 3, .c 631, .c 5,
  .c 3, .c 113, .c 59, .c 3, .c 5, .c 19, .c 3, .c 283, .p pv2 [pv2,pv3,pv227,pv1423], .c 3, .c 7,
  .c 23, .c 3, .c 41, .c 5, .c 3, .p pv2 [pv2,pv11,pv37,pv2381], .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv317,pv1019], .c 3, .c 211, .c 229, .c 3, .p pv5 [pv2,pv577,pv3359], .c 17,
  .c 3, .c 79, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv17,pv61,pv89], .c 3,
  .p pv17 [pv2,pv5,pv387631], .c 7, .c 3, .p pv2 [pv2,pv71,pv13649], .p pv3 [pv2,pv3,pv215351],
  .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv23,pv21067], .c 257, .c 3, .c 5, .c 347, .c 3, .c 7,
  .c 29, .c 3, .p pv2 [pv2,pv1938173], .c 83, .c 3, .c 13, .c 5, .c 3, .c 59, .c 19, .c 3, .c 5,
  .c 11, .c 3, .p pv2 [pv2,pv5,pv439,pv883], .c 73, .c 3, .c 1879, .c 13, .c 3, .c 7, .c 5, .c 3,
  .c 11, .c 17, .c 3, .c 5, .c 7, .c 3, .c 29, .p pv2 [pv2,pv3,pv646067], .c 3, .c 43, .c 223,
  .c 3, .p pv2 [pv2,pv379,pv2557], .c 5, .c 3, .c 47, .c 127, .c 3, .c 5, .c 41, .c 3, .c 13,
  .c 11, .c 3, .c 19, .c 7, .c 3,
]
private theorem h0473c30 : checkBlock 3876187 128 b0473c30 = true := by
  decide +kernel

private def b0473c31 : List Row := [
  .c 23, .c 5, .c 3, .p pv3 [pv2,pv121139], .c 79, .c 3, .c 5, .c 13, .c 3, .c 1259, .c 1861,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv41,pv7879], .c 3, .c 53, .c 5, .c 3, .c 227, .c 7, .c 3, .c 5,
  .c 157, .c 3, .p pv2 [pv2,pv5,pv37,pv10477], .c 17, .c 3, .p pv3 [pv2,pv13,pv18637], .c 11,
  .c 3, .c 107, .c 5, .c 3, .c 7, .c 337, .c 3, .c 5, .c 29, .c 3, .c 11, .c 7, .c 3, .c 17,
  .c 71, .c 3, .c 149, .c 5, .c 3, .p pv2 [pv2,pv1938269], .c 1319, .c 3, .c 5, .c 479, .c 3,
  .c 7, .c 67, .c 3, .p pv2 [pv2,pv969139], .c 269, .c 3, .c 1459, .c 5, .c 3,
  .p pv3 [pv2,pv421,pv1151], .c 139, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv3671], .c 3, .c 23,
  .p pv3 [pv2,pv3,pv101,pv6397], .c 3, .c 11, .c 19, .c 3, .c 7, .c 5, .c 3,
  .p pv23 [pv2,pv11,pv83,pv193], .c 37, .c 3, .c 5, .c 7, .c 3, .c 61, .c 13, .c 3,
  .p pv3 [pv2,pv484577], .p pv2 [pv2,pv3,pv646103], .c 3, .c 151, .c 5, .c 3, .c 17, .c 11, .c 3,
  .c 5, .c 1951, .c 3, .p pv3 [pv2,pv5,pv24229], .c 31, .c 3, .c 643, .c 7, .c 3, .c 11, .c 5,
  .c 3, .p pv2 [pv2,pv181,pv10709], .p pv2 [pv2,pv3,pv5,pv2393], .c 3, .c 5, .c 859, .c 3, .c 71,
  .c 23, .c 3, .c 7, .p pv11 [pv2,pv3,pv13,pv16567], .c 3, .c 101, .c 5, .c 3, .c 137, .c 7, .c 3,
  .c 5, .c 11,
]
private theorem h0473c31 : checkBlock 3876443 128 b0473c31 = true := by
  decide +kernel

def rows0473 : List Row :=
  b0473c00 ++ b0473c01 ++ b0473c02 ++ b0473c03 ++ b0473c04 ++ b0473c05 ++ b0473c06 ++ b0473c07 ++
  b0473c08 ++ b0473c09 ++ b0473c10 ++ b0473c11 ++ b0473c12 ++ b0473c13 ++ b0473c14 ++ b0473c15 ++
  b0473c16 ++ b0473c17 ++ b0473c18 ++ b0473c19 ++ b0473c20 ++ b0473c21 ++ b0473c22 ++ b0473c23 ++
  b0473c24 ++ b0473c25 ++ b0473c26 ++ b0473c27 ++ b0473c28 ++ b0473c29 ++ b0473c30 ++ b0473c31

theorem checked0473 : checkBlock 3868507 4096 rows0473 = true :=
  checkBlock_append h0473c00 (
    checkBlock_append h0473c01 (
    checkBlock_append h0473c02 (
    checkBlock_append h0473c03 (
    checkBlock_append h0473c04 (
    checkBlock_append h0473c05 (
    checkBlock_append h0473c06 (
    checkBlock_append h0473c07 (
    checkBlock_append h0473c08 (
    checkBlock_append h0473c09 (
    checkBlock_append h0473c10 (
    checkBlock_append h0473c11 (
    checkBlock_append h0473c12 (
    checkBlock_append h0473c13 (
    checkBlock_append h0473c14 (
    checkBlock_append h0473c15 (
    checkBlock_append h0473c16 (
    checkBlock_append h0473c17 (
    checkBlock_append h0473c18 (
    checkBlock_append h0473c19 (
    checkBlock_append h0473c20 (
    checkBlock_append h0473c21 (
    checkBlock_append h0473c22 (
    checkBlock_append h0473c23 (
    checkBlock_append h0473c24 (
    checkBlock_append h0473c25 (
    checkBlock_append h0473c26 (
    checkBlock_append h0473c27 (
    checkBlock_append h0473c28 (
    checkBlock_append h0473c29 (
    checkBlock_append h0473c30 (
    h0473c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
