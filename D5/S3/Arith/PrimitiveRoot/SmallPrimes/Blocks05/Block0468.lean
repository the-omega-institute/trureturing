/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks05/Block0468
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks05/Block0468.checked0468
   digest: Kernel proof of checker success on extended consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table034
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table038
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table046
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table052
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table059
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table068
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table097
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table121
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table157
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table158
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table159
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table160
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table163
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table165
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table170
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table174
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table181
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table189
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table201
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table222
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables03.Table245
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables03.Table246

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0468c00 : List Row := [
  .c 3, .c 11, .c 7, .c 3, .c 5, .c 179, .c 3, .p pv3 [pv2,pv5,pv11,pv8699],
  .p pv3 [pv2,pv3,pv241,pv2647], .c 3, .c 17, .c 19, .c 3, .p pv2 [pv2,pv7,pv223,pv613], .c 5,
  .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv63793], .c 3, .c 5, .c 1201, .c 3, .c 23, .c 7, .c 3, .c 101,
  .p pv3 [pv2,pv3,pv637933], .c 3, .c 13, .c 5, .c 3, .c 73, .p pv2 [pv2,pv3,pv5,pv71,pv599],
  .c 3, .c 5, .p pv47 [pv2,pv3,pv13,pv3067], .c 3, .c 7, .c 29, .c 3,
  .p pv5 [pv2,pv11,pv19,pv9157], .c 13, .c 3, .c 47, .c 5, .c 3, .p pv7 [pv2,pv1913819], .c 439,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv337,pv631], .c 3, .p pv2 [pv2,pv5,pv37,pv2069], .c 127, .c 3,
  .p pv3 [pv2,pv7,pv68351], .c 11, .c 3, .c 7, .c 5, .c 3, .c 17,
  .p pv31 [pv2,pv3,pv5,pv7,pv11,pv1657], .c 3, .c 5, .c 7, .c 3, .c 11, .c 19, .c 3, .c 37, .c 61,
  .c 3, .p pv2 [pv2,pv11,pv86993], .c 5, .c 3, .c 151, .p pv7 [pv2,pv3,pv5,pv4253], .c 3, .c 5,
  .c 13, .c 3, .c 83, .c 53, .c 3, .c 97, .c 7, .c 3, .p pv2 [pv2,pv1913861], .c 5, .c 3, .c 23,
  .c 43, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv7,pv19,pv1439], .c 59, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv318979], .c 3, .c 109, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv53,pv12037], .c 3, .c 17, .c 823, .c 3, .c 67, .c 643, .c 3,
  .p pv7 [pv2,pv7,pv139,pv281], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 19, .c 3, .c 41,
]
private theorem h0468c00 : checkBlock 3827547 128 b0468c00 = true := by
  decide +kernel

private def b0468c01 : List Row := [
  .c 7, .c 3, .c 167, .p pv11 [pv2,pv3,pv13291], .c 3, .c 11, .c 5, .c 3, .c 53, .c 23, .c 3,
  .c 5, .c 587, .c 3, .c 7, .p pv5 [pv2,pv3,pv349,pv457], .c 3, .c 13, .c 17, .c 3,
  .p pv2 [pv2,pv41,pv46681], .c 5, .c 3, .c 31, .c 661, .c 3, .c 5, .c 11, .c 3, .c 59, .c 13,
  .c 3, .c 23, .p pv13 [pv2,pv3,pv11,pv47,pv617], .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv5,pv7,pv31], .c 3, .c 5, .c 7, .c 3, .c 709,
  .p pv5 [pv2,pv3,pv19,pv103,pv163], .c 3, .p pv3 [pv2,pv619,pv773], .p pv2 [pv2,pv3,pv23629],
  .c 3, .c 43, .c 5, .c 3, .c 37, .c 19, .c 3, .c 5, .c 137, .c 3, .c 139, .c 11, .c 3,
  .p pv5 [pv2,pv1913963], .c 7, .c 3, .c 61, .c 5, .c 3, .p pv2 [pv2,pv1913969], .c 13, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv37,pv43,pv401], .c 3, .c 131, .p pv5 [pv2,pv3,pv8861], .c 3, .c 7,
  .c 23, .c 3, .c 443, .c 5, .c 3, .c 181, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv159499], .c 3,
  .p pv2 [pv2,pv5,pv13,pv14723], .c 37, .c 3, .c 19, .c 11, .c 3, .c 13, .c 5, .c 3, .c 7, .c 101,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv13,pv19,pv41], .c 3, .c 11, .c 7, .c 3, .c 359, .c 13, .c 3,
  .p pv5 [pv2,pv11,pv191,pv911], .c 5, .c 3, .c 29, .c 53, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv71,pv4493], .c 3, .c 7, .c 17, .c 3, .c 41, .p pv53 [pv2,pv3,pv7,pv11393],
  .c 3, .p pv2 [pv2,pv641,pv1493], .c 5, .c 3,
]
private theorem h0468c01 : checkBlock 3827803 128 b0468c01 = true := by
  decide +kernel

private def b0468c02 : List Row := [
  .p pv2 [pv2,pv13,pv29,pv5077], .p pv2 [pv2,pv3,pv5,pv17,pv139], .c 3, .c 5,
  .p pv17 [pv2,pv3,pv11,pv31,pv1871], .c 3, .c 13, .p pv5 [pv2,pv3,pv159503], .c 3, .c 11,
  .p pv13 [pv2,pv3,pv212671], .c 3, .c 7, .c 5, .c 3, .c 1069, .p pv3 [pv2,pv3,pv5,pv7,pv18229],
  .c 3, .c 5, .c 7, .c 3, .c 19, .c 47, .c 3, .c 71, .p pv2 [pv2,pv3,pv149,pv2141], .c 3,
  .p pv3 [pv2,pv67,pv3571], .c 5, .c 3, .p pv7 [pv2,pv7,pv43,pv6359], .c 11, .c 3, .c 5, .c 1013,
  .c 3, .c 37, .p pv2 [pv2,pv3,pv7,pv11,pv1381], .c 3, .c 53, .c 7, .c 3, .c 11, .c 5, .c 3,
  .c 13, .p pv3 [pv2,pv3,pv5,pv47,pv181], .c 3, .c 5, .c 89, .c 3, .c 43, .c 199, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv37,pv479], .c 3, .c 211, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 11, .c 3,
  .c 137, .c 73, .c 3, .c 47, .c 139, .c 3, .c 29, .c 5, .c 3, .c 7, .c 41, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv22787], .c 3, .c 31, .c 7, .c 3, .c 13, .p pv7 [pv2,pv3,pv263,pv1213],
  .c 3, .c 991, .c 5, .c 3, .p pv7 [pv2,pv61,pv31379], .c 223, .c 3, .c 5, .c 17, .c 3, .c 7,
  .c 11, .c 3, .c 149, .p pv13 [pv2,pv3,pv7,pv23,pv1321], .c 3, .p pv5 [pv2,pv1914131], .c 5,
  .c 3, .p pv2 [pv2,pv863,pv1109], .c 397, .c 3, .c 5, .c 631, .c 3, .c 17, .c 31, .c 3,
  .p pv5 [pv2,pv7,pv11,pv24859], .c 457, .c 3, .c 7, .c 5, .c 3, .c 61, .c 197, .c 3, .c 5, .c 7,
  .c 3, .p pv7 [pv2,pv5,pv19,pv20149], .c 67,
]
private theorem h0468c02 : checkBlock 3828059 128 b0468c02 = true := by
  decide +kernel

private def b0468c03 : List Row := [
  .c 3, .c 173, .c 11, .c 3, .c 821, .c 5, .c 3, .c 19, .c 13, .c 3, .c 5, .c 1193, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv7,pv91151], .c 3, .c 401, .c 7, .c 3, .c 37, .c 5, .c 3,
  .p pv13 [pv2,pv1914179], .p pv7 [pv2,pv3,pv5,pv61,pv523], .c 3, .c 5, .c 19, .c 3,
  .p pv2 [pv2,pv5,pv7,pv13,pv601], .c 23, .c 3, .c 7, .p pv2 [pv2,pv3,pv638063], .c 3, .c 13,
  .c 5, .c 3, .p pv2 [pv2,pv957097], .c 7, .c 3, .c 5, .p pv17 [pv2,pv3,pv11,pv13,pv23,pv97],
  .c 3, .p pv3 [pv2,pv5,pv17,pv563], .c 419, .c 3, .c 11, .c 13, .c 3,
  .p pv2 [pv2,pv7,pv73,pv1873], .c 5, .c 3, .c 7, .c 61, .c 3, .c 5, .c 37, .c 3,
  .p pv17 [pv2,pv5,pv382843], .c 7, .c 3, .p pv2 [pv2,pv957109], .c 1129, .c 3, .c 19, .c 5, .c 3,
  .p pv3 [pv2,pv13,pv9203], .c 11, .c 3, .c 5, .c 41, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv11,pv19,pv43,pv71], .c 3, .p pv2 [pv2,pv467,pv4099], .c 31, .c 3, .c 11, .c 5,
  .c 3, .c 47, .c 19, .c 3, .c 5, .c 13, .c 3, .c 263, .c 29, .c 3, .p pv3 [pv2,pv7,pv34183],
  .p pv3 [pv2,pv3,pv41,pv79,pv197], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv53,pv18059], .c 23,
  .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv95713], .p pv2 [pv2,pv3,pv29,pv22003], .c 3, .c 1571,
  .c 257, .c 3, .c 71, .c 5, .c 3, .c 11, .c 83, .c 3, .c 5, .c 463, .c 3, .c 29, .c 17, .c 3,
  .c 19, .c 7, .c 3, .c 859, .c 5, .c 3, .c 59,
]
private theorem h0468c03 : checkBlock 3828315 128 b0468c03 = true := by
  decide +kernel

private def b0468c04 : List Row := [
  .p pv2 [pv2,pv3,pv5,pv17,pv7507], .c 3, .c 5, .c 79, .c 3, .c 67, .c 11, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv319049], .c 3, .c 31, .c 5, .c 3, .p pv11 [pv2,pv751,pv2549], .c 7, .c 3,
  .c 5, .c 101, .c 3, .p pv2 [pv2,pv5,pv382861], .c 103, .c 3, .c 13, .c 1259, .c 3, .c 449, .c 5,
  .c 3, .c 7, .c 73, .c 3, .c 5, .p pv11 [pv2,pv3,pv7,pv15193], .c 3, .c 1427, .c 7, .c 3, .c 479,
  .c 11, .c 3, .c 971, .c 5, .c 3, .p pv2 [pv2,pv379,pv5051], .p pv2 [pv2,pv3,pv5,pv11,pv5801],
  .c 3, .c 5, .c 29, .c 3, .c 7, .p pv11 [pv2,pv3,pv17,pv23], .c 3, .c 43, .c 743, .c 3,
  .p pv2 [pv2,pv11,pv13,pv1217], .c 5, .c 3, .c 17, .c 89, .c 3, .c 5, .c 673, .c 3,
  .p pv2 [pv2,pv5,pv38287], .c 41, .c 3, .c 83, .c 19, .c 3, .c 7, .c 5, .c 3,
  .p pv11 [pv2,pv23,pv83233], .c 13, .c 3, .c 5, .c 7, .c 3, .c 811, .p pv2 [pv2,pv3,pv319061],
  .c 3, .c 11, .c 137, .c 3, .p pv5 [pv2,pv1914371], .c 5, .c 3, .p pv2 [pv2,pv7,pv11,pv31,pv401],
  .p pv3 [pv2,pv3,pv5,pv1021], .c 3, .c 5, .c 17, .c 3, .c 47, .c 43, .c 3, .c 241, .c 7, .c 3,
  .c 13, .c 5, .c 3, .c 31, .c 11, .c 3, .c 5, .c 23, .c 3, .c 17, .c 1051, .c 3, .c 7, .c 13,
  .c 3, .c 11, .c 5, .c 3, .c 101, .c 7, .c 3, .c 5, .c 71, .c 3, .p pv2 [pv2,pv5,pv191441],
  .c 19, .c 3,
]
private theorem h0468c04 : checkBlock 3828571 128 b0468c04 = true := by
  decide +kernel

private def b0468c05 : List Row := [
  .c 499, .c 521, .c 3, .c 23, .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .c 11, .c 3, .c 13, .c 7,
  .c 3, .p pv5 [pv2,pv23,pv20809], .c 17, .c 3, .c 977, .c 5, .c 3, .c 11, .c 37, .c 3, .c 5,
  .c 13, .c 3, .c 7, .c 523, .c 3, .p pv5 [pv2,pv1914443], .c 233, .c 3, .c 17, .c 5, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv5,pv12763], .c 3, .c 5, .c 151, .c 3, .c 367, .c 11, .c 3,
  .p pv2 [pv2,pv7,pv13,pv67,pv157], .p pv3 [pv2,pv3,pv19,pv33587], .c 3, .c 7, .c 5, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv5,pv7,pv18233], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv191447], .c 1637,
  .c 3, .p pv2 [pv2,pv11,pv269,pv647], .c 41, .c 3, .p pv3 [pv2,pv109,pv4391], .c 5, .c 3, .c 71,
  .c 17, .c 3, .c 5, .c 1367, .c 3, .c 23, .p pv2 [pv2,pv3,pv7,pv79,pv577], .c 3, .c 191, .c 7,
  .c 3, .c 67, .c 5, .c 3, .c 179, .c 353, .c 3, .c 5, .c 809, .c 3, .c 11, .c 1889, .c 3, .c 7,
  .c 173, .c 3, .c 19, .c 5, .c 3, .c 37, .c 7, .c 3, .c 5, .c 31, .c 3, .c 41, .c 13, .c 3,
  .c 379, .c 83, .c 3, .c 47, .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 1319, .c 3, .c 109, .c 7,
  .c 3, .c 11, .c 73, .c 3, .c 29, .c 5, .c 3, .p pv7 [pv2,pv11,pv174049],
  .p pv31 [pv2,pv3,pv5,pv17,pv1877],
]
private theorem h0468c05 : checkBlock 3828827 128 b0468c05 = true := by
  decide +kernel

private def b0468c06 : List Row := [
  .c 3, .c 5, .p pv5 [pv2,pv3,pv23,pv3083], .c 3, .c 7, .c 37, .c 3, .c 17, .c 1667, .c 3,
  .p pv5 [pv2,pv29,pv107,pv617], .c 5, .c 3, .c 23, .c 11, .c 3, .c 5, .c 67, .c 3,
  .p pv11 [pv2,pv5,pv31,pv193], .p pv2 [pv2,pv3,pv11,pv83,pv233], .c 3, .c 19,
  .p pv7 [pv2,pv3,pv103,pv1549], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv1914569],
  .p pv31 [pv2,pv3,pv5,pv7,pv1013], .c 3, .c 5, .c 7, .c 3, .c 31, .c 61, .c 3,
  .p pv2 [pv2,pv957289], .c 59, .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv7,pv179,pv191],
  .p pv13 [pv2,pv3,pv5,pv109,pv1171], .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv191459],
  .p pv5 [pv2,pv3,pv7,pv17,pv31,pv173], .c 3, .c 281, .c 7, .c 3, .c 43, .c 5, .c 3, .c 11, .c 23,
  .c 3, .c 5, .c 509, .c 3, .c 307, .c 31, .c 3, .c 7, .p pv2 [pv2,pv3,pv29,pv59,pv373], .c 3,
  .p pv17 [pv2,pv19,pv100769], .c 5, .c 3, .p pv2 [pv2,pv13,pv211,pv349], .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv41,pv43,pv181], .c 3, .c 13, .c 11, .c 3, .c 23, .c 241, .c 3,
  .p pv2 [pv2,pv7,pv2791], .c 5, .c 3, .c 7, .c 131, .c 3, .c 5, .c 13, .c 3,
  .p pv19 [pv2,pv5,pv23,pv16649], .c 7, .c 3, .c 41, .c 19, .c 3, .p pv2 [pv2,pv1914641], .c 5,
  .c 3, .p pv3 [pv2,pv73,pv79,pv83], .p pv2 [pv2,pv3,pv5,pv127643], .c 3, .c 5, .c 1373, .c 3,
  .c 7, .c 53, .c 3, .p pv2 [pv2,pv13,pv31,pv4751], .c 11, .c 3, .c 193, .c 5, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv5,pv11,pv967], .c 3, .c 5, .c 1657, .c 3, .c 11,
  .p pv5 [pv2,pv3,pv13,pv24547], .c 3, .c 31,
]
private theorem h0468c06 : checkBlock 3829083 128 b0468c06 = true := by
  decide +kernel

private def b0468c07 : List Row := [
  .c 23, .c 3, .c 7, .c 5, .c 3, .c 751, .p pv7 [pv2,pv3,pv5,pv7,pv521], .c 3, .c 5, .c 7, .c 3,
  .c 73, .c 29, .c 3, .c 79, .c 17, .c 3, .p pv2 [pv2,pv47,pv20369], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv273527], .p pv2 [pv2,pv3,pv5,pv63823], .c 3, .c 5, .c 157, .c 3,
  .p pv11 [pv2,pv5,pv382939], .c 19, .c 3, .c 11, .c 7, .c 3, .c 17, .c 5, .c 3, .c 53, .c 613,
  .c 3, .c 5, .c 181, .c 3, .c 29, .c 13, .c 3, .c 7, .p pv2 [pv2,pv3,pv106373], .c 3,
  .p pv3 [pv2,pv478679], .c 5, .c 3, .c 211, .c 7, .c 3, .c 5, .p pv19 [pv2,pv3,pv79,pv2693],
  .c 3, .c 43, .c 359, .c 3, .c 113, .p pv2 [pv2,pv3,pv61,pv10463], .c 3, .c 11, .c 5, .c 3, .c 7,
  .c 17, .c 3, .c 5, .c 23, .c 3, .c 1607, .c 7, .c 3, .p pv5 [pv2,pv1914743],
  .p pv53 [pv2,pv3,pv13,pv17,pv19], .c 3, .p pv2 [pv2,pv31,pv89,pv347], .c 5, .c 3,
  .p pv2 [pv2,pv739,pv2591], .c 13, .c 3, .c 5, .c 11, .c 3, .c 7, .c 47, .c 3, .c 1303, .c 61,
  .c 3, .c 23, .c 5, .c 3, .c 11, .p pv19 [pv2,pv3,pv5,pv107,pv1193], .c 3, .c 5, .c 29, .c 3,
  .c 1787, .c 263, .c 3, .c 547, .c 577, .c 3, .c 7, .c 5, .c 3, .p pv13 [pv2,pv127,pv15077],
  .c 137, .c 3, .c 5, .c 7, .c 3, .c 883, .c 11, .c 3, .c 349, .c 13, .c 3, .c 19, .c 5, .c 3,
  .c 139, .c 373, .c 3,
]
private theorem h0468c07 : checkBlock 3829339 128 b0468c07 = true := by
  decide +kernel

private def b0468c08 : List Row := [
  .c 5, .p pv11 [pv2,pv3,pv319133], .c 3, .p pv3 [pv2,pv5,pv4787],
  .p pv2 [pv2,pv3,pv7,pv19,pv4799], .c 3, .c 17, .c 7, .c 3, .p pv2 [pv2,pv957403], .c 5, .c 3,
  .c 1289, .c 19, .c 3, .c 5, .c 1097, .c 3, .c 13, .p pv7 [pv2,pv3,pv9973], .c 3, .c 7, .c 11,
  .c 3, .c 103, .c 5, .c 3, .p pv3 [pv2,pv37,pv6469], .c 7, .c 3, .c 5, .c 13, .c 3, .c 11,
  .c 757, .c 3, .p pv2 [pv2,pv43,pv44531], .c 71, .c 3, .p pv3 [pv2,pv7,pv11,pv6217], .c 5, .c 3,
  .c 7, .p pv19 [pv2,pv3,pv5,pv197], .c 3, .c 5, .c 41, .c 3, .p pv2 [pv2,pv5,pv59,pv6491], .c 7,
  .c 3, .c 19, .c 193, .c 3, .c 83, .c 5, .c 3, .c 13, .c 29, .c 3, .c 5, .c 227, .c 3, .c 7,
  .c 1277, .c 3, .c 11, .p pv11 [pv2,pv3,pv7,pv41,pv139], .c 3, .p pv2 [pv2,pv957433], .c 5, .c 3,
  .c 541, .c 191, .c 3, .c 5, .c 149, .c 3, .p pv7 [pv2,pv5,pv15319], .c 23, .c 3,
  .p pv2 [pv2,pv7,pv136777], .c 37, .c 3, .c 7, .c 5, .c 3, .c 29, .c 11, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv53,pv3613], .p pv11 [pv2,pv3,pv11,pv58027], .c 3, .c 13, .c 677, .c 3, .c 11,
  .c 5, .c 3, .c 23, .p pv7 [pv2,pv3,pv5,pv13,pv491], .c 3, .c 5, .p pv5 [pv2,pv3,pv263,pv809],
  .c 3, .c 17, .c 13, .c 3, .p pv3 [pv2,pv478727], .c 7, .c 3, .p pv5 [pv2,pv23,pv83257], .c 5,
  .c 3, .p pv2 [pv2,pv17,pv3313], .p pv11 [pv2,pv3,pv5,pv19,pv6719], .c 3, .c 5, .c 11, .c 3,
  .c 79, .p pv2 [pv2,pv3,pv47,pv503], .c 3, .c 7, .c 19,
]
private theorem h0468c08 : checkBlock 3829595 128 b0468c08 = true := by
  decide +kernel

private def b0468c09 : List Row := [
  .c 3, .p pv3 [pv2,pv13,pv73651], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 59, .c 3, .c 521,
  .p pv7 [pv2,pv3,pv73,pv1093], .c 3, .c 197, .c 17, .c 3, .p pv2 [pv2,pv7,pv71,pv3853], .c 5,
  .c 3, .c 7, .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv17,pv149], .c 3, .p pv3 [pv2,pv5,pv38299],
  .c 7, .c 3, .c 37, .c 113, .c 3, .c 17, .c 5, .c 3, .p pv7 [pv2,pv1914959], .c 67, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv31,pv59,pv349], .c 3, .c 7, .c 41, .c 3, .c 23, .c 53, .c 3, .c 13, .c 5,
  .c 3, .p pv2 [pv2,pv97,pv9871], .c 401, .c 3, .c 5, .c 31, .c 3, .p pv3 [pv2,pv5,pv23,pv181],
  .c 19, .c 3, .c 43, .c 11, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv167,pv11467], .c 17, .c 3,
  .c 5, .c 7, .c 3, .c 11, .p pv11 [pv2,pv3,pv53,pv3011], .c 3, .p pv2 [pv2,pv957499], .c 79,
  .c 3, .p pv2 [pv2,pv11,pv174091], .c 5, .c 3, .c 251, .c 163, .c 3, .c 5,
  .p pv23 [pv2,pv3,pv4987], .c 3, .c 13, .p pv5 [pv2,pv3,pv7,pv113,pv269], .c 3,
  .p pv2 [pv2,pv89,pv21517], .c 7, .c 3, .p pv5 [pv2,pv17,pv14081], .c 5, .c 3, .c 19, .c 1297,
  .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv7,pv31,pv353], .c 43, .c 3, .c 7, .c 29, .c 3,
  .c 179, .c 5, .c 3, .c 263, .c 7, .c 3, .c 5, .c 19, .c 3, .c 31, .c 17, .c 3,
  .p pv5 [pv2,pv13,pv147311], .c 563, .c 3, .p pv2 [pv2,pv7,pv37,pv3697], .c 5, .c 3, .c 7, .c 11,
  .c 3, .c 5,
]
private theorem h0468c09 : checkBlock 3829851 128 b0468c09 = true := by
  decide +kernel

private def b0468c10 : List Row := [
  .c 953, .c 3, .p pv17 [pv2,pv5,pv383011], .c 7, .c 3, .c 17, .p pv13 [pv2,pv3,pv83,pv7691],
  .c 3, .c 11, .c 5, .c 3, .c 37, .p pv2 [pv2,pv3,pv5,pv42557], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv159589], .c 3, .c 7, .c 31, .c 3, .p pv2 [pv2,pv29,pv66037],
  .p pv2 [pv2,pv3,pv7,pv15199], .c 3, .c 19, .c 5, .c 3, .p pv7 [pv2,pv103,pv18593],
  .p pv7 [pv2,pv3,pv5,pv15959], .c 3, .c 5, .c 11, .c 3, .c 47, .c 601, .c 3, .c 13, .c 41, .c 3,
  .c 7, .c 5, .c 3, .c 11, .c 19, .c 3, .c 5, .c 7, .c 3, .c 83, .c 13, .c 3,
  .p pv5 [pv2,pv1915103], .c 1447, .c 3, .c 23, .c 5, .c 3, .c 17, .c 59, .c 3, .c 5, .c 1069,
  .c 3, .p pv17 [pv2,pv5,pv383023], .c 11, .c 3, .c 71, .c 7, .c 3, .p pv5 [pv2,pv13,pv179,pv823],
  .c 5, .c 3, .c 1789, .c 61, .c 3, .c 5, .c 53, .c 3, .c 41, .p pv3 [pv2,pv3,pv29,pv22013], .c 3,
  .c 7, .p pv2 [pv2,pv3,pv13,pv43,pv571], .c 3, .p pv3 [pv2,pv7481], .c 5, .c 3, .c 107, .c 7,
  .c 3, .c 5, .c 17, .c 3, .c 29, .c 89, .c 3, .c 431, .c 11, .c 3, .p pv19 [pv2,pv7,pv41,pv6673],
  .c 5, .c 3, .c 7, .c 43, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv45599], .c 3, .c 11, .c 7, .c 3,
  .p pv5 [pv2,pv1915163], .c 31, .c 3, .c 13, .c 5, .c 3, .c 59, .c 1171, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv13,pv16369], .c 3, .c 7, .c 811, .c 3, .p pv2 [pv2,pv277,pv3457], .c 13, .c 3,
]
private theorem h0468c10 : checkBlock 3830107 128 b0468c10 = true := by
  decide +kernel

private def b0468c11 : List Row := [
  .c 53, .c 5, .c 3, .c 109, .p pv2 [pv2,pv3,pv5,pv127679], .c 3, .c 5,
  .p pv7 [pv2,pv3,pv11,pv1319], .c 3, .c 19, .c 73, .c 3, .c 11, .c 17, .c 3, .c 7, .c 5, .c 3,
  .c 463, .p pv41 [pv2,pv3,pv5,pv7,pv19], .c 3, .c 5, .c 7, .c 3, .c 13,
  .p pv5 [pv2,pv3,pv319201], .c 3, .c 151, .c 19, .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv19543], .c 11, .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv17,pv43,pv131],
  .c 23, .c 3, .c 127, .c 7, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv1915229],
  .p pv2 [pv2,pv3,pv5,pv63841], .c 3, .c 5, .c 103, .c 3, .c 89, .c 79, .c 3, .c 7, .c 167, .c 3,
  .c 43, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 11, .c 3, .c 1091, .c 181, .c 3, .c 41,
  .p pv2 [pv2,pv3,pv11,pv17,pv569], .c 3, .p pv3 [pv2,pv7,pv23,pv1487], .c 5, .c 3, .c 7, .c 71,
  .c 3, .c 5, .p pv7 [pv2,pv3,pv7,pv43,pv101], .c 3, .p pv2 [pv2,pv5,pv11,pv97,pv359], .c 7, .c 3,
  .p pv3 [pv2,pv37,pv12941], .p pv2 [pv2,pv3,pv638423], .c 3, .p pv5 [pv2,pv17,pv112663], .c 5,
  .c 3, .p pv2 [pv2,pv41,pv23357], .c 199, .c 3, .c 5, .p pv2 [pv2,pv3,pv61,pv5233], .c 3, .c 7,
  .c 11, .c 3, .c 13, .c 43, .c 3, .c 37, .c 5, .c 3, .p pv2 [pv2,pv1915289], .c 23, .c 3, .c 5,
  .c 109, .c 3, .c 67, .c 13, .c 3, .p pv2 [pv2,pv7,pv11,pv12437], .p pv11 [pv2,pv3,pv70937],
  .c 3, .c 7, .c 5, .c 3, .c 19, .p pv3 [pv2,pv3,pv5,pv7,pv17,pv29,pv37], .c 3, .c 5, .c 7,
]
private theorem h0468c11 : checkBlock 3830363 128 b0468c11 = true := by
  decide +kernel

private def b0468c12 : List Row := [
  .c 3, .c 443, .p pv3 [pv2,pv3,pv638437], .c 3, .c 17, .c 11, .c 3, .c 277, .c 5, .c 3, .c 29,
  .c 47, .c 3, .c 5, .c 19, .c 3, .c 11, .c 397, .c 3, .c 137, .c 7, .c 3, .c 71, .c 5, .c 3,
  .p pv2 [pv2,pv29,pv33023], .c 13, .c 3, .c 5, .c 1549, .c 3, .c 53, .c 1249, .c 3, .c 7,
  .p pv37 [pv2,pv3,pv47,pv283], .c 3, .c 59, .c 5, .c 3, .c 83, .c 7, .c 3, .c 5, .c 107, .c 3,
  .p pv19 [pv2,pv5,pv13,pv79,pv373], .p pv7 [pv2,pv3,pv17,pv41,pv229], .c 3, .c 11, .c 23, .c 3,
  .c 13, .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv127691], .c 3, .c 5,
  .p pv29 [pv2,pv3,pv7,pv13,pv877], .c 3, .c 43, .c 7, .c 3, .p pv2 [pv2,pv17,pv307,pv367], .c 13,
  .c 3, .c 41, .c 5, .c 3, .p pv7 [pv2,pv37,pv51767], .c 11, .c 3, .c 5, .c 659, .c 3, .c 7,
  .p pv19 [pv2,pv3,pv11,pv29021], .c 3, .c 607, .c 179, .c 3, .c 11, .c 5, .c 3, .c 79,
  .p pv3 [pv2,pv3,pv5,pv149,pv857], .c 3, .c 5, .c 17, .c 3, .c 13, .p pv2 [pv2,pv3,pv638467],
  .c 3, .c 313, .c 829, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv19,pv100811], .c 73, .c 3, .c 5,
  .c 7, .c 3, .c 17, .c 131, .c 3, .c 19, .c 571, .c 3, .p pv2 [pv2,pv29,pv257], .c 5, .c 3,
  .c 11, .c 751, .c 3, .c 5, .c 23, .c 3, .c 61, .p pv5 [pv2,pv3,pv7,pv197,pv463], .c 3,
  .p pv2 [pv2,pv13,pv147341], .c 7, .c 3, .c 281,
]
private theorem h0468c12 : checkBlock 3830619 128 b0468c12 = true := by
  decide +kernel

private def b0468c13 : List Row := [
  .c 5, .c 3, .c 13, .p pv7 [pv2,pv3,pv5,pv23,pv347], .c 3, .c 5, .c 31, .c 3,
  .p pv2 [pv2,pv5,pv7,pv54727], .c 11, .c 3, .c 7, .c 17, .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv743,pv1289], .c 7, .c 3, .c 5, .c 41, .c 3, .c 107, .c 47, .c 3,
  .p pv7 [pv2,pv11,pv23,pv67,pv113], .c 29, .c 3, .c 17, .c 5, .c 3, .c 7, .c 229, .c 3, .c 5,
  .c 71, .c 3, .c 19, .c 7, .c 3, .c 13, .c 11, .c 3, .p pv2 [pv2,pv1915481], .c 5, .c 3,
  .p pv3 [pv2,pv478871], .c 283, .c 3, .c 5, .p pv7 [pv2,pv3,pv739], .c 3, .c 7, .c 13, .c 3,
  .c 29, .c 19, .c 3, .c 67, .c 5, .c 3, .c 41, .c 17, .c 3, .c 5, .p pv3 [pv2,pv3,pv638501],
  .c 3, .c 31, .c 251, .c 3, .c 37, .p pv2 [pv2,pv3,pv17,pv23,pv71], .c 3, .c 7, .c 5, .c 3,
  .c 1609, .c 83, .c 3, .c 5, .c 7, .c 3, .c 23, .p pv5 [pv2,pv3,pv31,pv43,pv479], .c 3, .c 11,
  .c 1327, .c 3, .c 307, .c 5, .c 3, .c 197, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv212837], .c 3,
  .c 1409, .c 31, .c 3, .c 569, .c 7, .c 3, .c 373, .c 5, .c 3, .c 71, .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv159629], .c 3, .p pv3 [pv2,pv5,pv7,pv13,pv421], .c 17, .c 3, .c 7, .c 353,
  .c 3, .c 11, .c 5, .c 3, .p pv13 [pv2,pv139,pv13781], .c 7, .c 3, .c 5, .c 67, .c 3,
]
private theorem h0468c13 : checkBlock 3830875 128 b0468c13 = true := by
  decide +kernel

private def b0468c14 : List Row := [
  .p pv2 [pv2,pv5,pv383113], .c 23, .c 3, .c 17, .c 13, .c 3, .c 677, .c 5, .c 3, .c 7, .c 653,
  .c 3, .c 5, .c 11, .c 3, .c 29, .c 7, .c 3, .p pv5 [pv2,pv31,pv61,pv1013],
  .p pv7 [pv2,pv3,pv11,pv907], .c 3, .c 1009, .c 5, .c 3, .c 11, .p pv31 [pv2,pv3,pv5,pv63853],
  .c 3, .c 5, .c 277, .c 3, .c 7, .c 1601, .c 3, .c 31, .p pv3 [pv2,pv3,pv7,pv19,pv4801], .c 3,
  .c 1597, .c 5, .c 3, .c 97, .c 53, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv191561], .c 11,
  .c 3, .c 61, .c 487, .c 3, .c 7, .c 5, .c 3, .c 17, .c 109, .c 3, .c 5, .c 7, .c 3, .c 1553,
  .p pv2 [pv2,pv3,pv47,pv6793], .c 3, .c 43, .c 31, .c 3, .c 79, .c 5, .c 3, .c 13, .c 23, .c 3,
  .c 5, .c 29, .c 3, .c 1879, .c 59, .c 3, .p pv5 [pv2,pv41,pv46723], .c 7, .c 3, .c 19, .c 5,
  .c 3, .c 47, .p pv2 [pv2,pv3,pv5,pv11,pv43], .c 3, .c 5, .c 17, .c 3, .c 11, .c 37, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv212851], .c 3, .c 151, .c 5, .c 3, .p pv3 [pv2,pv67,pv1787], .c 7, .c 3, .c 5,
  .c 883, .c 3, .c 17, .c 43, .c 3, .c 13, .c 61, .c 3, .c 337, .c 5, .c 3, .c 7, .c 89, .c 3,
  .c 5, .c 269, .c 3, .c 461, .c 7, .c 3, .c 11, .p pv2 [pv2,pv3,pv113,pv5651], .c 3, .c 31, .c 5,
]
private theorem h0468c14 : checkBlock 3831131 128 b0468c14 = true := by
  decide +kernel

private def b0468c15 : List Row := [
  .c 3, .c 673, .c 733, .c 3, .c 5, .c 1033, .c 3, .c 7, .c 97, .c 3, .c 19, .c 17, .c 3,
  .p pv2 [pv2,pv13,pv73681], .c 5, .c 3, .c 1153, .c 11, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv17,pv19,pv659], .c 3, .c 173, .c 313, .c 3, .p pv2 [pv2,pv7,pv193,pv709],
  .p pv31 [pv2,pv3,pv13,pv49121], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv478931], .c 13, .c 3,
  .c 5, .c 7, .c 3, .c 37, .c 127, .c 3, .p pv2 [pv2,pv1915733], .c 881, .c 3,
  .p pv3 [pv2,pv43,pv5569], .c 5, .c 3, .c 137, .c 167, .c 3, .c 5, .c 11, .c 3, .c 41,
  .p pv11 [pv2,pv3,pv7,pv45613], .c 3, .c 103, .c 7, .c 3, .c 13, .c 5, .c 3, .c 11, .c 17, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv13,pv2729], .c 3, .c 19, .p pv2 [pv2,pv3,pv638587], .c 3, .c 7, .c 13,
  .c 3, .c 227, .c 5, .c 3, .c 89, .c 7, .c 3, .c 5, .c 23, .c 3, .c 73, .c 11, .c 3,
  .p pv2 [pv2,pv957889], .c 19, .c 3, .c 107, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv23,pv617],
  .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv22807], .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv11,pv71,pv223],
  .c 181, .c 3, .c 23, .c 5, .c 3, .p pv7 [pv2,pv1915799], .c 43, .c 3, .c 5, .c 13, .c 3, .c 7,
  .c 17, .c 3, .c 433, .c 11, .c 3, .p pv5 [pv2,pv1915811], .c 5, .c 3, .c 193, .c 31, .c 3, .c 5,
  .c 59, .c 3, .c 11,
]
private theorem h0468c15 : checkBlock 3831387 128 b0468c15 = true := by
  decide +kernel

private def b0468c16 : List Row := [
  .p pv2 [pv2,pv3,pv212869], .c 3, .c 17, .p pv11 [pv2,pv3,pv167,pv239], .c 3, .c 7, .c 5, .c 3,
  .c 13, .p pv13 [pv2,pv3,pv5,pv7,pv3041], .c 3, .c 5, .c 7, .c 3, .c 349, .c 19, .c 3, .c 109,
  .c 1151, .c 3, .c 29, .c 5, .c 3, .p pv3 [pv2,pv7,pv53,pv1291],
  .p pv2 [pv2,pv3,pv5,pv337,pv379], .c 3, .c 5, .c 73, .c 3, .c 1367, .c 103, .c 3, .c 11, .c 7,
  .c 3, .c 839, .c 5, .c 3, .p pv11 [pv2,pv11,pv174169], .p pv19 [pv2,pv3,pv5,pv37,pv863], .c 3,
  .c 5, .p pv3 [pv2,pv3,pv638621], .c 3, .c 23, .p pv2 [pv2,pv3,pv17,pv2087], .c 3, .c 7, .c 1913,
  .c 3, .p pv5 [pv2,pv157,pv12203], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 37, .c 3, .c 773,
  .c 13, .c 3, .p pv5 [pv2,pv17,pv251,pv449], .c 47, .c 3, .c 11, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv63863], .c 3, .c 5, .c 19, .c 3, .c 97, .c 7, .c 3, .c 67, .c 29, .c 3,
  .c 599, .c 5, .c 3, .c 223, .p pv3 [pv2,pv3,pv5,pv127727], .c 3, .c 5, .c 11, .c 3, .c 7, .c 23,
  .c 3, .p pv2 [pv2,pv1129,pv1697], .c 373, .c 3, .c 149, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5,
  .c 53, .c 3, .c 17, .c 179, .c 3, .c 29, .c 43, .c 3, .c 7, .c 5, .c 3, .c 23,
  .p pv17 [pv2,pv3,pv5,pv7,pv71,pv257], .c 3, .c 5, .c 7, .c 3, .c 131, .c 11, .c 3, .c 239,
  .p pv7 [pv2,pv3,pv97,pv823], .c 3, .c 13, .c 5, .c 3,
]
private theorem h0468c16 : checkBlock 3831643 128 b0468c16 = true := by
  decide +kernel

private def b0468c17 : List Row := [
  .c 157, .c 19, .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv3779], .c 3,
  .p pv13 [pv2,pv5,pv31,pv47,pv263], .p pv13 [pv2,pv3,pv7,pv7603], .c 3,
  .p pv2 [pv2,pv11,pv73,pv1193], .c 7, .c 3, .p pv2 [pv2,pv1915961], .c 5, .c 3,
  .p pv3 [pv2,pv478991], .c 67, .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv587], .c 3, .c 31, .c 113,
  .c 3, .c 7, .c 11, .c 3, .c 17, .c 5, .c 3, .c 61, .c 7, .c 3, .c 5, .c 163, .c 3, .c 11, .c 29,
  .c 3, .c 19, .c 37, .c 3, .c 41, .c 5, .c 3, .c 7, .c 59, .c 3, .c 5, .c 13, .c 3,
  .p pv3 [pv2,pv5,pv479], .c 7, .c 3, .c 23, .p pv7 [pv2,pv3,pv159667], .c 3, .c 953, .c 5, .c 3,
  .p pv2 [pv2,pv277,pv6917], .c 17, .c 3, .c 5, .c 83, .c 3, .c 7, .c 191, .c 3, .c 11, .c 389,
  .c 3, .c 1373, .c 5, .c 3, .c 13, .c 47, .c 3, .c 5, .c 1439, .c 3,
  .p pv2 [pv2,pv5,pv29,pv6607], .c 631, .c 3, .p pv5 [pv2,pv7,pv273719], .c 379, .c 3, .c 7, .c 5,
  .c 3, .p pv11 [pv2,pv151,pv12689], .c 11, .c 3, .c 5, .c 7, .c 3, .c 19, .c 1531, .c 3,
  .p pv3 [pv2,pv31,pv3863], .c 23, .c 3, .c 11, .c 5, .c 3, .c 59, .p pv3 [pv2,pv3,pv5,pv19,pv83],
  .c 3, .c 5, .c 43, .c 3, .p pv11 [pv2,pv5,pv95803], .c 17, .c 3, .c 13, .c 7, .c 3,
  .p pv2 [pv2,pv67,pv79,pv181], .c 5, .c 3, .c 1423, .c 241, .c 3, .c 5, .c 11, .c 3, .c 233,
  .c 13,
]
private theorem h0468c17 : checkBlock 3831899 128 b0468c17 = true := by
  decide +kernel

private def b0468c18 : List Row := [
  .c 3, .c 7, .p pv3 [pv2,pv3,pv11,pv31,pv1873], .c 3, .p pv2 [pv2,pv89,pv21529], .c 5, .c 3,
  .c 11, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv29,pv2753], .c 3, .c 647,
  .p pv5 [pv2,pv3,pv211,pv1009], .c 3, .c 617, .c 31, .c 3, .c 83, .c 5, .c 3, .c 7, .c 37, .c 3,
  .c 5, .p pv11 [pv2,pv3,pv7,pv91243], .c 3, .c 79, .c 7, .c 3, .c 1637,
  .p pv17 [pv2,pv3,pv13,pv53,pv103], .c 3, .p pv5 [pv2,pv109,pv17579], .c 5, .c 3, .c 41, .c 13,
  .c 3, .c 5, .c 23, .c 3, .c 7, .c 19, .c 3, .p pv5 [pv2,pv11,pv43,pv4051],
  .p pv17 [pv2,pv3,pv7,pv22811], .c 3, .p pv2 [pv2,pv958063], .c 5, .c 3, .c 17, .c 509, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv67,pv9533], .c 3, .c 53, .p pv5 [pv2,pv3,pv2957], .c 3, .c 1277, .c 11,
  .c 3, .c 7, .c 5, .c 3, .c 43, .p pv2 [pv2,pv3,pv5,pv7,pv11,pv79], .c 3, .c 5, .c 7, .c 3,
  .c 11, .p pv3 [pv2,pv3,pv638717], .c 3, .p pv2 [pv2,pv23,pv83311], .c 13, .c 3, .c 31, .c 5,
  .c 3, .c 19, .c 29, .c 3, .c 5, .c 17, .c 3, .c 109, .c 47, .c 3, .p pv3 [pv2,pv239521], .c 7,
  .c 3, .p pv5 [pv2,pv199,pv9629], .c 5, .c 3, .c 37, .p pv17 [pv2,pv3,pv5,pv29,pv881], .c 3,
  .c 5, .c 19, .c 3, .c 13, .c 421, .c 3, .c 7, .c 79, .c 3, .c 97, .c 5, .c 3, .c 29, .c 7, .c 3,
  .c 5, .c 13, .c 3, .c 1201, .c 41, .c 3, .p pv2 [pv2,pv761,pv1259],
  .p pv3 [pv2,pv3,pv23,pv9257], .c 3, .p pv2 [pv2,pv7,pv457,pv599], .c 5, .c 3, .c 7,
]
private theorem h0468c18 : checkBlock 3832155 128 b0468c18 = true := by
  decide +kernel

private def b0468c19 : List Row := [
  .c 11, .c 3, .c 5, .p pv11 [pv2,pv3,pv7,pv1901], .c 3, .c 23, .c 7, .c 3, .c 47, .c 17, .c 3,
  .c 11, .c 5, .c 3, .c 13, .c 227, .c 3, .c 5, .c 61, .c 3, .c 7, .c 311, .c 3, .c 653, .c 1019,
  .c 3, .c 17, .c 5, .c 3, .c 173, .c 19, .c 3, .c 5, .c 11, .c 3, .p pv19 [pv2,pv5,pv17,pv1409],
  .c 53, .c 3, .p pv7 [pv2,pv7,pv39107], .p pv7 [pv2,pv3,pv11,pv1613], .c 3, .c 7, .c 5, .c 3,
  .c 11, .p pv11 [pv2,pv3,pv5,pv7,pv73], .c 3, .c 5, .c 7, .c 3, .p pv13 [pv2,pv5,pv11,pv34841],
  .c 23, .c 3, .c 13, .c 251, .c 3, .c 587, .c 5, .c 3, .c 853, .c 17, .c 3, .c 5, .c 971, .c 3,
  .c 199, .c 11, .c 3, .c 19, .c 7, .c 3, .c 29, .c 5, .c 3, .c 23, .c 31, .c 3, .c 5, .c 97,
  .c 3, .c 37, .c 73, .c 3, .c 7, .p pv2 [pv2,pv3,pv149,pv1429], .c 3, .c 863, .c 5, .c 3, .c 53,
  .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv3943], .c 3, .c 67, .p pv3 [pv2,pv3,pv638767], .c 3, .c 89,
  .c 11, .c 3, .p pv2 [pv2,pv7,pv136879], .c 5, .c 3, .c 7, .c 13, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv91253], .c 3, .c 11, .c 7, .c 3, .p pv2 [pv2,pv958159], .c 41, .c 3,
  .p pv2 [pv2,pv11,pv19,pv53,pv173], .c 5, .c 3, .c 331, .c 23, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv79847], .c 3, .c 7, .p pv3 [pv2,pv3,pv47,pv13591], .c 3,
]
private theorem h0468c19 : checkBlock 3832411 128 b0468c19 = true := by
  decide +kernel

private def b0468c20 : List Row := [
  .c 17, .c 29, .c 3, .c 13, .c 5, .c 3, .p pv7 [pv2,pv1916339], .c 383, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv13,pv1489], .c 3, .c 61, .c 941, .c 3, .c 11, .c 13, .c 3, .c 7, .c 5,
  .c 3, .c 47, .c 823, .c 3, .c 5, .c 7, .c 3, .c 41, .p pv2 [pv2,pv3,pv71,pv2999], .c 3, .c 29,
  .p pv11 [pv2,pv3,pv159697], .c 3, .c 103, .c 5, .c 3, .c 409, .c 11, .c 3, .c 5, .c 31, .c 3,
  .c 13, .c 271, .c 3, .p pv2 [pv2,pv19,pv29,pv37,pv47], .c 7, .c 3, .c 11, .c 5, .c 3, .c 17,
  .c 977, .c 3, .c 5, .c 13, .c 3, .c 1889, .p pv3 [pv2,pv3,pv163,pv3919], .c 3, .c 7, .c 23,
  .c 3, .c 37, .c 5, .c 3, .c 1123, .c 7, .c 3, .c 5, .c 11, .c 3, .p pv13 [pv2,pv5,pv383281],
  .c 19, .c 3, .c 59, .c 499, .c 3, .c 1187, .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv37,pv1151],
  .c 3, .c 5, .c 17, .c 3, .c 157, .c 7, .c 3, .c 107, .c 101, .c 3, .p pv2 [pv2,pv958213], .c 5,
  .c 3, .c 457, .c 1759, .c 3, .c 5, .c 37, .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv59,pv109,pv149], .p pv3 [pv2,pv3,pv7,pv13037], .c 3, .c 431, .c 5, .c 3, .c 19,
  .c 43, .c 3, .c 5, .c 47, .c 3, .c 29, .p pv29 [pv2,pv3,pv31,pv6869], .c 3, .c 13, .c 439, .c 3,
  .c 7, .c 5, .c 3, .p pv17 [pv2,pv1097,pv1747], .p pv37 [pv2,pv3,pv5,pv7,pv13],
]
private theorem h0468c20 : checkBlock 3832667 128 b0468c20 = true := by
  decide +kernel

private def b0468c21 : List Row := [
  .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv29,pv13217], .c 13, .c 3, .p pv3 [pv2,pv67,pv7151],
  .c 11, .c 3, .c 1499, .c 5, .c 3, .p pv2 [pv2,pv7,pv367,pv373], .c 1867, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv17,pv6263], .c 3, .c 11, .c 89, .c 3, .c 41, .c 7, .c 3, .c 17, .c 5, .c 3,
  .c 1291, .c 269, .c 3, .c 5, .c 127, .c 3, .c 47, .p pv5 [pv2,pv3,pv13309], .c 3, .c 7,
  .p pv11 [pv2,pv3,pv13,pv157,pv313], .c 3, .c 19, .c 5, .c 3, .p pv3 [pv2,pv41,pv5843], .c 7,
  .c 3, .c 5, .c 29, .c 3, .c 251, .c 83, .c 3, .c 11, .c 197, .c 3, .p pv3 [pv2,pv7,pv68447],
  .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv29,pv1049], .c 3, .c 101, .c 7, .c 3,
  .c 31, .p pv67 [pv2,pv3,pv17,pv37579], .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv701,pv1367],
  .c 11, .c 3, .c 5, .c 71, .c 3, .c 7, .c 233, .c 3, .p pv5 [pv2,pv1916543], .c 13, .c 3, .c 11,
  .c 5, .c 3, .p pv2 [pv2,pv19,pv5309], .p pv7 [pv2,pv3,pv5,pv4259], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv43,pv83,pv179], .c 3, .c 23, .c 449, .c 3, .c 19, .c 31, .c 3, .c 7, .c 5,
  .c 3, .p pv7 [pv2,pv13,pv36857], .c 41, .c 3, .c 5, .c 7, .c 3, .c 13, .c 17, .c 3, .c 223,
  .c 43, .c 3, .p pv3 [pv2,pv101,pv593], .c 5, .c 3, .c 11, .c 173, .c 3, .c 5, .c 13, .c 3,
  .c 59, .c 193, .c 3, .c 17,
]
private theorem h0468c21 : checkBlock 3832923 128 b0468c21 = true := by
  decide +kernel

private def b0468c22 : List Row := [
  .c 7, .c 3, .p pv5 [pv2,pv1916591], .c 5, .c 3, .c 83, .c 29, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv319433], .c 3, .p pv3 [pv2,pv5,pv7,pv37], .c 11, .c 3, .c 7,
  .p pv29 [pv2,pv3,pv53239], .c 3, .c 41, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 353, .c 3,
  .c 19, .p pv5 [pv2,pv3,pv13,pv6143], .c 3, .c 37, .p pv7 [pv2,pv3,pv79,pv8087], .c 3, .c 31,
  .c 5, .c 3, .c 7, .c 1229, .c 3, .c 5, .p pv11 [pv2,pv3,pv7,pv22817], .c 3,
  .p pv2 [pv2,pv5,pv137,pv1399], .c 7, .c 3, .c 937, .c 11, .c 3, .c 47, .c 5, .c 3, .c 17,
  .p pv53 [pv2,pv3,pv5,pv11], .c 3, .c 5, .c 1709, .c 3, .c 7, .p pv2 [pv2,pv3,pv319441], .c 3,
  .c 13, .c 113, .c 3, .c 73, .c 5, .c 3, .c 347, .c 37, .c 3, .c 5, .c 79, .c 3, .c 43, .c 13,
  .c 3, .p pv17 [pv2,pv7,pv19,pv14411], .p pv7 [pv2,pv3,pv79861], .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv67,pv28607], .c 23, .c 3, .c 5, .c 7, .c 3, .c 103, .c 569, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv638893], .c 3, .c 503, .c 5, .c 3, .p pv3 [pv2,pv7,pv11,pv127],
  .p pv11 [pv2,pv3,pv5,pv191,pv223], .c 3, .c 5, .c 41, .c 3, .c 17, .c 19, .c 3, .c 23, .c 7,
  .c 3, .c 1061, .c 5, .c 3, .c 181, .c 11, .c 3, .c 5, .c 43, .c 3,
  .p pv2 [pv2,pv5,pv7,pv23,pv2381], .p pv2 [pv2,pv3,pv11,pv113,pv257], .c 3, .c 7,
  .p pv7 [pv2,pv3,pv41,pv15583], .c 3, .c 11, .c 5, .c 3, .c 31, .c 7, .c 3,
]
private theorem h0468c22 : checkBlock 3833179 128 b0468c22 = true := by
  decide +kernel

private def b0468c23 : List Row := [
  .c 5, .c 53, .c 3, .p pv7 [pv2,pv5,pv13,pv19,pv97], .p pv2 [pv2,pv3,pv212969], .c 3, .c 383,
  .c 17, .c 3, .c 13, .c 5, .c 3, .c 7, .c 47, .c 3, .c 5, .c 11, .c 3, .c 727, .c 7, .c 3,
  .c 787, .c 13, .c 3, .c 17, .c 5, .c 3, .c 11, .c 31, .c 3, .c 5, .c 19, .c 3, .c 7, .c 71,
  .c 3, .c 173, .c 307, .c 3, .p pv3 [pv2,pv479189], .c 5, .c 3, .c 269, .c 83, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv541,pv1181], .c 3, .c 13, .c 11, .c 3, .c 97, .c 29, .c 3, .c 7, .c 5, .c 3,
  .c 233, .c 17, .c 3, .c 5, .c 7, .c 3, .c 191, .c 709, .c 3, .p pv5 [pv2,pv11,pv271,pv643],
  .p pv19 [pv2,pv3,pv17,pv29], .c 3, .c 19, .c 5, .c 3, .c 43, .c 1559, .c 3, .c 5, .c 241, .c 3,
  .p pv11 [pv2,pv5,pv523,pv733], .c 223, .c 3, .c 29, .c 7, .c 3, .c 467, .c 5, .c 3, .c 13,
  .c 19, .c 3, .c 5, .c 23, .c 3, .c 11, .c 41, .c 3, .c 7, .p pv2 [pv2,pv3,pv319469], .c 3,
  .c 79, .c 5, .c 3, .c 109, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv31,pv20611], .c 3,
  .p pv2 [pv2,pv5,pv76673], .c 17, .c 3, .c 101, .c 211, .c 3, .c 23, .c 5, .c 3, .c 7, .c 137,
  .c 3, .c 5, .c 31, .c 3, .c 37, .c 7, .c 3, .c 11, .c 229,
]
private theorem h0468c23 : checkBlock 3833435 128 b0468c23 = true := by
  decide +kernel

private def b0468c24 : List Row := [
  .c 3, .c 1669, .c 5, .c 3, .p pv2 [pv2,pv11,pv174259], .p pv17 [pv2,pv3,pv5,pv13,pv983], .c 3,
  .c 5, .p pv3 [pv2,pv3,pv19,pv33629], .c 3, .c 7, .c 13, .c 3, .c 859,
  .p pv13 [pv2,pv3,pv7,pv37,pv2467], .c 3, .p pv2 [pv2,pv443,pv4327], .c 5, .c 3,
  .p pv3 [pv2,pv61,pv491], .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv159739], .c 3, .c 73, .c 47, .c 3,
  .p pv2 [pv2,pv7,pv41,pv6679], .c 127, .c 3, .c 7, .c 5, .c 3, .c 139, .c 59, .c 3, .c 5, .c 7,
  .c 3, .c 29, .c 457, .c 3, .p pv3 [pv2,pv239611], .c 601, .c 3, .c 157, .c 5, .c 3, .c 17,
  .c 13, .c 3, .c 5, .c 11, .c 3, .c 19, .c 227, .c 3, .c 67, .c 7, .c 3, .c 1109, .c 5, .c 3,
  .c 11, .c 641, .c 3, .c 5, .c 1789, .c 3, .c 557, .p pv5 [pv2,pv3,pv31,pv5153], .c 3, .c 7,
  .c 19, .c 3, .c 13, .c 5, .c 3, .c 1087, .c 7, .c 3, .c 5, .c 17, .c 3, .c 53, .c 11, .c 3,
  .p pv2 [pv2,pv37,pv103,pv503], .c 13, .c 3, .p pv5 [pv2,pv7,pv34231], .c 5, .c 3, .c 7,
  .p pv23 [pv2,pv3,pv5,pv43,pv743], .c 3, .c 5, .c 29, .c 3, .c 17, .c 7, .c 3,
  .p pv3 [pv2,pv11,pv19,pv2293], .p pv2 [pv2,pv3,pv139,pv4597], .c 3, .c 37, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv17,pv4337], .c 61, .c 3, .c 5, .c 107, .c 3, .c 7, .c 43, .c 3,
  .p pv5 [pv2,pv257,pv7459], .c 11, .c 3, .c 353, .c 5, .c 3, .c 23, .c 67, .c 3, .c 5,
]
private theorem h0468c24 : checkBlock 3833691 128 b0468c24 = true := by
  decide +kernel

private def b0468c25 : List Row := [
  .c 13, .c 3, .c 11, .c 19, .c 3, .c 277, .c 17, .c 3, .c 7, .c 5, .c 3, .c 103,
  .p pv7 [pv2,pv3,pv5,pv7,pv18257], .c 3, .c 5, .c 7, .c 3, .c 1151, .c 929, .c 3, .c 31,
  .p pv2 [pv2,pv3,pv319499], .c 3, .c 17, .c 5, .c 3, .c 13, .c 179, .c 3, .c 5, .c 1429, .c 3,
  .c 449, .p pv5 [pv2,pv3,pv7,pv13,pv3511], .c 3, .c 11, .c 7, .c 3, .p pv5 [pv2,pv97,pv19763],
  .c 5, .c 3, .c 19, .c 23, .c 3, .c 5, .c 139, .c 3, .c 151, .p pv2 [pv2,pv3,pv639007], .c 3,
  .c 7, .c 31, .c 3, .p pv2 [pv2,pv43,pv22291], .c 5, .c 3, .p pv2 [pv2,pv1917029], .c 7, .c 3,
  .c 5, .c 19, .c 3, .c 71, .c 53, .c 3, .c 13, .p pv7 [pv2,pv3,pv17,pv37589], .c 3, .c 11, .c 5,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv13,pv29,pv113], .c 3, .c 5, .c 157, .c 3, .c 1613, .c 7, .c 3,
  .c 79, .p pv2 [pv2,pv3,pv131,pv271], .c 3, .c 523, .c 5, .c 3, .c 29,
  .p pv13 [pv2,pv3,pv5,pv89,pv359], .c 3, .c 5, .c 11, .c 3, .c 7, .c 199, .c 3, .c 461,
  .p pv2 [pv2,pv3,pv7,pv11,pv43,pv193], .c 3, .c 19, .c 5, .c 3, .c 11, .c 487, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv41,pv7793], .c 3, .p pv3 [pv2,pv5,pv11,pv4357], .c 17, .c 3,
  .p pv5 [pv2,pv7,pv47,pv5827], .c 23, .c 3, .c 7, .c 5, .c 3, .c 53, .c 13, .c 3, .c 5, .c 7,
  .c 3, .p pv7 [pv2,pv5,pv383419], .c 11, .c 3, .c 17, .c 37, .c 3,
]
private theorem h0468c25 : checkBlock 3833947 128 b0468c25 = true := by
  decide +kernel

private def b0468c26 : List Row := [
  .c 113, .c 5, .c 3, .c 67, .c 197, .c 3, .c 5, .c 149, .c 3, .p pv3 [pv2,pv5,pv13,pv14747],
  .p pv3 [pv2,pv3,pv7,pv91291], .c 3, .p pv2 [pv2,pv11,pv397,pv439], .c 7, .c 3, .c 13, .c 5,
  .c 3, .c 131, .c 1063, .c 3, .c 5, .c 1609, .c 3, .p pv2 [pv2,pv5,pv7,pv313],
  .p pv2 [pv2,pv3,pv73,pv1459], .c 3, .c 7, .c 11, .c 3, .c 101, .c 5, .c 3, .c 419, .c 7, .c 3,
  .c 5, .c 61, .c 3, .c 11, .p pv2 [pv2,pv3,pv17,pv37591], .c 3, .p pv5 [pv2,pv353,pv5431],
  .c 1031, .c 3, .c 29, .c 5, .c 3, .c 7, .p pv29 [pv2,pv3,pv5,pv12781], .c 3, .c 5, .c 23, .c 3,
  .c 13, .c 7, .c 3, .c 1901, .c 311, .c 3, .c 733, .c 5, .c 3, .c 1801, .c 193, .c 3, .c 5,
  .c 13, .c 3, .c 7, .c 67, .c 3, .c 11, .c 1427, .c 3, .c 23, .c 5, .c 3, .c 31, .c 41, .c 3,
  .c 5, .c 17, .c 3, .c 19, .c 389, .c 3, .p pv3 [pv2,pv7,pv13,pv23,pv229], .c 271, .c 3, .c 7,
  .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 7, .c 3, .c 17, .c 947, .c 3, .p pv5 [pv2,pv1917203],
  .c 19, .c 3, .c 11, .c 5, .c 3, .c 607, .c 31, .c 3, .c 5, .c 719, .c 3,
  .p pv31 [pv2,pv5,pv307,pv1249], .p pv23 [pv2,pv3,pv7,pv317], .c 3, .p pv2 [pv2,pv958609], .c 7,
  .c 3, .c 41, .c 5, .c 3, .c 1567, .p pv2 [pv2,pv3,pv5,pv8521], .c 3, .c 5, .c 11,
]
private theorem h0468c26 : checkBlock 3834203 128 b0468c26 = true := by
  decide +kernel

private def b0468c27 : List Row := [
  .c 3, .c 661, .c 349, .c 3, .c 7, .c 17, .c 3, .p pv3 [pv2,pv479309], .c 5, .c 3, .c 11, .c 7,
  .c 3, .c 5, .c 167, .c 3, .c 23, .c 13, .c 3, .c 53, .p pv2 [pv2,pv3,pv639083], .c 3, .c 17,
  .c 5, .c 3, .c 7, .c 109, .c 3, .c 5, .c 83, .c 3, .c 61, .c 7, .c 3, .c 251,
  .p pv7 [pv2,pv3,pv59,pv677], .c 3, .p pv2 [pv2,pv13,pv37,pv1993], .c 5, .c 3,
  .p pv2 [pv2,pv179,pv10711], .p pv11 [pv2,pv3,pv5,pv263], .c 3, .c 5, .p pv2 [pv2,pv3,pv639091],
  .c 3, .c 7, .p pv13 [pv2,pv3,pv159773], .c 3, .p pv2 [pv2,pv11,pv87149], .c 107, .c 3, .c 313,
  .c 5, .c 3, .c 37, .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv31,pv859], .c 3, .c 79, .c 23, .c 3,
  .c 59, .c 11, .c 3, .c 7, .c 5, .c 3, .c 19, .p pv19 [pv2,pv3,pv5,pv7,pv11,pv83], .c 3, .c 5,
  .c 7, .c 3, .c 11, .p pv2 [pv2,pv3,pv29,pv3673], .c 3, .c 73, .p pv37 [pv2,pv3,pv19,pv33637],
  .c 3, .c 13, .c 5, .c 3, .c 23, .p pv11 [pv2,pv3,pv5,pv137,pv311], .c 3, .c 5, .c 19, .c 3,
  .c 29, .c 37, .c 3, .p pv5 [pv2,pv59,pv32497], .c 7, .c 3, .p pv2 [pv2,pv23,pv41681], .c 5,
  .c 3, .c 1399, .c 1117, .c 3, .c 5, .c 101, .c 3, .c 739, .c 17, .c 3, .c 7, .c 761, .c 3,
  .c 47, .c 5, .c 3, .c 41, .c 7, .c 3, .c 5, .c 43, .c 3, .c 13, .p pv3 [pv2,pv3,pv23671], .c 3,
  .c 17, .c 53, .c 3, .c 19,
]
private theorem h0468c27 : checkBlock 3834459 128 b0468c27 = true := by
  decide +kernel

private def b0468c28 : List Row := [
  .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 13, .c 3, .c 31, .c 7, .c 3, .c 307, .c 79, .c 3, .c 11,
  .c 5, .c 3, .c 317, .c 19, .c 3, .c 5, .c 29, .c 3, .c 7, .c 73, .c 3, .c 23, .c 647, .c 3,
  .c 107, .c 5, .c 3, .c 13, .c 71, .c 3, .c 5, .c 11, .c 3, .c 37, .c 31, .c 3,
  .p pv2 [pv2,pv7,pv151,pv907], .c 827, .c 3, .c 7, .c 5, .c 3, .c 11, .c 1571, .c 3, .c 5, .c 7,
  .c 3, .c 167, .c 59, .c 3, .c 19, .p pv7 [pv2,pv3,pv37,pv2879], .c 3, .p pv3 [pv2,pv89,pv2693],
  .c 5, .c 3, .c 1627, .p pv11 [pv2,pv3,pv5,pv31957], .c 3, .c 5, .c 181, .c 3,
  .p pv2 [pv2,pv5,pv76697], .c 11, .c 3, .c 13, .c 7, .c 3, .c 1321, .c 5, .c 3, .c 43, .c 47,
  .c 3, .c 5, .c 17, .c 3, .c 113, .c 13, .c 3, .c 7, .c 421, .c 3, .p pv2 [pv2,pv127,pv7549],
  .c 5, .c 3, .p pv2 [pv2,pv191,pv10039], .c 7, .c 3, .c 5, .p pv13 [pv2,pv3,pv639151], .c 3,
  .c 17, .p pv5 [pv2,pv3,pv43,pv929], .c 3, .c 31, .c 11, .c 3, .c 71, .c 5, .c 3, .c 7, .c 29,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv1087], .c 3, .c 11, .c 7, .c 3, .c 109, .c 1039, .c 3,
  .p pv3 [pv2,pv11,pv43579], .c 5, .c 3, .p pv7 [pv2,pv1917479], .c 13, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv331,pv1931], .c 3,
]
private theorem h0468c28 : checkBlock 3834715 128 b0468c28 = true := by
  decide +kernel

private def b0468c29 : List Row := [
  .c 7, .c 1487, .c 3, .c 1907, .c 17, .c 3, .p pv5 [pv2,pv73,pv26267], .c 5, .c 3, .c 29,
  .p pv3 [pv2,pv3,pv5,pv42611], .c 3, .c 5, .c 23, .c 3, .p pv3 [pv2,pv5,pv13,pv59], .c 769, .c 3,
  .c 11, .c 61, .c 3, .c 7, .c 5, .c 3, .c 127, .p pv29 [pv2,pv3,pv5,pv7,pv23,pv397], .c 3, .c 5,
  .c 7, .c 3, .p pv7 [pv2,pv5,pv17,pv1327], .c 241, .c 3, .c 1381, .c 13, .c 3, .c 23, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv68483], .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv109,pv733], .c 3,
  .p pv3 [pv2,pv5,pv337,pv569], .c 229, .c 3, .p pv2 [pv2,pv23,pv263,pv317], .c 7, .c 3, .c 11,
  .c 5, .c 3, .p pv19 [pv2,pv13,pv147503], .c 17, .c 3, .c 5, .c 37, .c 3, .c 13, .c 19, .c 3,
  .c 7, .c 41, .c 3, .c 31, .c 5, .c 3, .p pv2 [pv2,pv958777], .c 7, .c 3, .c 5, .c 11, .c 3,
  .c 877, .p pv2 [pv2,pv3,pv661,pv967], .c 3, .c 43, .c 1733, .c 3, .c 53, .c 5, .c 3, .c 7,
  .c 937, .c 3, .c 5, .c 67, .c 3, .c 389, .c 7, .c 3, .p pv2 [pv2,pv13,pv131,pv563], .c 523,
  .c 3, .c 29, .c 5, .c 3, .c 13, .c 701, .c 3, .c 5, .c 59, .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv53,pv97,pv373], .c 313, .c 3, .c 409, .c 5, .c 3, .p pv7 [pv2,pv37,pv51827],
  .c 73, .c 3, .c 5, .c 19, .c 3, .c 257, .c 43, .c 3, .c 17, .c 811, .c 3, .c 7, .c 5,
]
private theorem h0468c29 : checkBlock 3834971 128 b0468c29 = true := by
  decide +kernel

private def b0468c30 : List Row := [
  .c 3, .c 1297, .p pv7 [pv2,pv3,pv5,pv7,pv2609], .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv95881], .p pv2 [pv2,pv3,pv71023], .c 3, .c 13, .c 11, .c 3, .c 61, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv31,pv8837], .p pv2 [pv2,pv3,pv5,pv11,pv13,pv149], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv639211], .c 3, .c 11, .c 13, .c 3, .c 89, .c 7, .c 3, .c 19, .c 5, .c 3,
  .c 31, .p pv11 [pv2,pv3,pv5,pv127843], .c 3, .c 5, .c 331, .c 3, .p pv2 [pv2,pv5,pv7,pv5479],
  .p pv3 [pv2,pv3,pv17,pv19,pv1979], .c 3, .c 7, .c 37, .c 3, .p pv3 [pv2,pv13,pv18439], .c 5,
  .c 3, .c 17, .c 7, .c 3, .c 5, .c 199, .c 3, .p pv2 [pv2,pv5,pv383533], .c 113, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv13,pv49171], .c 3, .p pv5 [pv2,pv7,pv23,pv43,pv277], .c 5, .c 3, .c 7, .c 13,
  .c 3, .c 5, .c 751, .c 3, .p pv11 [pv2,pv5,pv23971], .c 7, .c 3, .p pv5 [pv2,pv29,pv89,pv743],
  .c 281, .c 3, .p pv2 [pv2,pv958843], .c 5, .c 3, .p pv2 [pv2,pv19,pv100931], .c 11, .c 3, .c 5,
  .c 17, .c 3, .c 7, .c 197, .c 3, .c 19, .p pv3 [pv2,pv3,pv7,pv53,pv1723], .c 3, .c 11, .c 5,
  .c 3, .c 149, .c 23, .c 3, .c 5, .c 397, .c 3, .c 17, .c 1741, .c 3, .c 41, .c 13, .c 3, .c 7,
  .c 5, .c 3, .p pv11 [pv2,pv17,pv112807], .p pv41 [pv2,pv3,pv5,pv7,pv761], .c 3, .c 5, .c 7,
  .c 3, .c 53, .c 29, .c 3, .c 23, .c 997, .c 3, .c 271, .c 5, .c 3, .c 11, .c 43, .c 3, .c 5,
  .c 97, .c 3, .c 13,
]
private theorem h0468c30 : checkBlock 3835227 128 b0468c30 = true := by
  decide +kernel

private def b0468c31 : List Row := [
  .p pv2 [pv2,pv3,pv7,pv29,pv47,pv67], .c 3, .p pv5 [pv2,pv1917743], .c 7, .c 3, .c 73, .c 5,
  .c 3, .c 283, .p pv2 [pv2,pv3,pv5,pv2557], .c 3, .c 5, .c 13, .c 3, .c 19, .c 11, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv639253], .c 3, .c 17, .c 5, .c 3, .c 47, .c 7, .c 3, .c 5, .c 31, .c 3,
  .c 613, .c 439, .c 3, .p pv2 [pv2,pv11,pv13,pv13411], .c 19, .c 3, .c 163, .c 5, .c 3, .c 7,
  .c 1291, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv73,pv139], .c 3, .c 181, .c 7, .c 3,
  .p pv3 [pv2,pv47,pv101], .c 11, .c 3, .c 173, .c 5, .c 3, .c 137, .c 17, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv83,pv3851], .c 3, .c 7, .p pv5 [pv2,pv3,pv409,pv521], .c 3,
  .p pv5 [pv2,pv19,pv100937], .c 1583, .c 3, .p pv2 [pv2,pv11,pv179,pv487], .c 5, .c 3, .c 61,
  .p pv2 [pv2,pv3,pv5,pv7103], .c 3, .c 5, .c 29, .c 3, .p pv13 [pv2,pv5,pv31,pv12373], .c 71,
  .c 3, .c 13, .c 73, .c 3, .c 7, .c 5, .c 3, .c 59, .p pv47 [pv2,pv3,pv5,pv7,pv13,pv281], .c 3,
  .c 5, .c 7, .c 3, .c 31, .c 13, .c 3, .c 11, .p pv2 [pv2,pv3,pv319639], .c 3, .c 41, .c 5, .c 3,
  .c 37, .p pv7 [pv2,pv3,pv5,pv61,pv131], .c 3, .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv541,pv709],
  .c 17, .c 3, .p pv3 [pv2,pv239731], .c 7, .c 3, .c 907, .c 5, .c 3, .c 1229, .c 11, .c 3, .c 5,
  .c 47, .c 3, .c 1279, .c 31, .c 3, .c 7, .c 43, .c 3, .c 11, .c 5, .c 3,
]
private theorem h0468c31 : checkBlock 3835483 128 b0468c31 = true := by
  decide +kernel

def rows0468 : List Row :=
  b0468c00 ++ b0468c01 ++ b0468c02 ++ b0468c03 ++ b0468c04 ++ b0468c05 ++ b0468c06 ++ b0468c07 ++
  b0468c08 ++ b0468c09 ++ b0468c10 ++ b0468c11 ++ b0468c12 ++ b0468c13 ++ b0468c14 ++ b0468c15 ++
  b0468c16 ++ b0468c17 ++ b0468c18 ++ b0468c19 ++ b0468c20 ++ b0468c21 ++ b0468c22 ++ b0468c23 ++
  b0468c24 ++ b0468c25 ++ b0468c26 ++ b0468c27 ++ b0468c28 ++ b0468c29 ++ b0468c30 ++ b0468c31

theorem checked0468 : checkBlock 3827547 4096 rows0468 = true :=
  checkBlock_append h0468c00 (
    checkBlock_append h0468c01 (
    checkBlock_append h0468c02 (
    checkBlock_append h0468c03 (
    checkBlock_append h0468c04 (
    checkBlock_append h0468c05 (
    checkBlock_append h0468c06 (
    checkBlock_append h0468c07 (
    checkBlock_append h0468c08 (
    checkBlock_append h0468c09 (
    checkBlock_append h0468c10 (
    checkBlock_append h0468c11 (
    checkBlock_append h0468c12 (
    checkBlock_append h0468c13 (
    checkBlock_append h0468c14 (
    checkBlock_append h0468c15 (
    checkBlock_append h0468c16 (
    checkBlock_append h0468c17 (
    checkBlock_append h0468c18 (
    checkBlock_append h0468c19 (
    checkBlock_append h0468c20 (
    checkBlock_append h0468c21 (
    checkBlock_append h0468c22 (
    checkBlock_append h0468c23 (
    checkBlock_append h0468c24 (
    checkBlock_append h0468c25 (
    checkBlock_append h0468c26 (
    checkBlock_append h0468c27 (
    checkBlock_append h0468c28 (
    checkBlock_append h0468c29 (
    checkBlock_append h0468c30 (
    h0468c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
