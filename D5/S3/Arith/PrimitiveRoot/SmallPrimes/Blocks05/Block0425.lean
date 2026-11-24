/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks05/Block0425
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks05/Block0425.checked0425
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table035
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table038
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table043
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table055
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table064
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table076
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table092
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table118
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table156

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0425c00 : List Row := [
  .c 727, .c 3, .c 151, .c 79, .c 3, .c 277, .c 5, .c 3, .c 47, .c 11, .c 3, .c 5, .c 71, .c 3,
  .c 1049, .p pv5 [pv2,pv3,pv7,pv11,pv157], .c 3, .p pv2 [pv2,pv19,pv61,pv751], .c 7, .c 3, .c 11,
  .c 5, .c 3, .c 59, .c 17, .c 3, .c 5, .p pv17 [pv2,pv3,pv145069], .c 3, .c 1087, .c 37, .c 3,
  .c 7, .c 883, .c 3, .c 13, .c 5, .c 3, .c 41, .c 7, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv397,pv877], .c 19, .c 3, .c 61, .c 13, .c 3, .c 31, .c 5, .c 3, .c 7, .c 29,
  .c 3, .c 5, .c 23, .c 3, .p pv3 [pv2,pv5,pv11,pv41,pv193], .c 7, .c 3, .c 241, .c 53, .c 3,
  .c 1069, .c 5, .c 3, .c 191, .p pv2 [pv2,pv3,pv5,pv23,pv29], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv580291], .c 3, .c 7, .c 11, .c 3, .c 1229, .p pv17 [pv2,pv3,pv7,pv61,pv151],
  .c 3, .c 23, .c 5, .c 3, .c 19, .c 1747, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv107,pv1627],
  .c 167, .c 3, .c 17, .c 67, .c 3, .c 7, .c 5, .c 3, .p pv17 [pv2,pv29,pv173,pv347],
  .p pv13 [pv2,pv3,pv5,pv7,pv829], .c 3, .c 5, .c 7, .c 3, .c 37, .p pv2 [pv2,pv3,pv103,pv313],
  .c 3, .c 409, .c 11, .c 3, .p pv5 [pv2,pv1740911], .c 5, .c 3, .c 13, .c 1481, .c 3, .c 5,
  .c 1217, .c 3, .c 11, .c 41, .c 3, .p pv5 [pv2,pv79,pv22037], .c 7, .c 3, .c 383, .c 5, .c 3,
]
private theorem h0425c00 : checkBlock 3481603 128 b0425c00 = true := by
  decide +kernel

private def b0425c01 : List Row := [
  .p pv2 [pv2,pv31,pv89,pv631], .c 821, .c 3, .c 5, .c 701, .c 3, .c 281, .c 379, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv23,pv1097], .c 3, .c 19, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 181, .c 3,
  .c 23, .c 199, .c 3, .c 11, .c 151, .c 3, .c 193, .c 5, .c 3, .c 7, .c 19, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv82903], .c 3, .c 1861, .c 7, .c 3, .p pv3 [pv2,pv269,pv809], .c 389, .c 3,
  .c 29, .c 5, .c 3, .c 691, .c 11, .c 3, .c 5, .c 17, .c 3, .c 7, .c 1051, .c 3,
  .p pv5 [pv2,pv41,pv42463], .p pv11 [pv2,pv3,pv7,pv43,pv241], .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv19,pv91631], .c 149, .c 3, .c 5, .c 599, .c 3, .c 17, .c 23, .c 3, .c 19,
  .p pv11 [pv2,pv3,pv13,pv44641], .c 3, .c 7, .c 5, .c 3, .c 97, .c 13, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv174101], .p pv5 [pv2,pv3,pv499,pv1163], .c 3, .c 73,
  .p pv2 [pv2,pv3,pv11,pv977], .c 3, .c 37, .c 5, .c 3, .c 11, .p pv29 [pv2,pv3,pv5,pv29017],
  .c 3, .c 5, .c 53, .c 3, .p pv2 [pv2,pv5,pv11,pv13,pv487], .c 71, .c 3, .c 67, .c 7, .c 3,
  .c 13, .c 5, .c 3, .c 509, .p pv3 [pv2,pv3,pv5,pv37,pv3137], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv13,pv17,pv101], .c 3, .c 1423, .c 11, .c 3, .c 7, .c 13, .c 3, .c 17, .c 5,
  .c 3, .c 83, .c 7, .c 3, .c 5, .c 37, .c 3, .c 19, .c 823,
]
private theorem h0425c01 : checkBlock 3481859 128 b0425c01 = true := by
  decide +kernel

private def b0425c02 : List Row := [
  .c 3, .c 29, .c 947, .c 3, .c 251, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 31, .c 3, .c 13,
  .c 7, .c 3, .p pv2 [pv2,pv29,pv60037], .c 11, .c 3, .c 53, .c 5, .c 3, .p pv7 [pv2,pv1741079],
  .c 17, .c 3, .c 5, .c 13, .c 3, .c 7, .c 73, .c 3, .c 23, .p pv7 [pv2,pv3,pv7,pv17,pv4877],
  .c 3, .c 43, .c 5, .c 3, .p pv2 [pv2,pv870547], .c 67, .c 3, .c 5, .p pv2 [pv2,pv3,pv290183],
  .c 3, .p pv17 [pv2,pv5,pv23,pv757], .c 97, .c 3, .p pv5 [pv2,pv7,pv13,pv19,pv53], .c 241, .c 3,
  .c 7, .c 5, .c 3, .c 13, .c 337, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv31,pv47,pv239],
  .c 29, .c 3, .c 11, .c 59, .c 3, .c 1033, .c 5, .c 3, .p pv3 [pv2,pv7,pv11,pv5653],
  .p pv2 [pv2,pv3,pv5,pv4643], .c 3, .c 5, .p pv5 [pv2,pv3,pv72547], .c 3, .c 31, .c 17, .c 3,
  .c 311, .c 7, .c 3, .p pv3 [pv2,pv108821], .c 5, .c 3, .c 149, .c 11, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv580381], .c 3, .c 29, .p pv2 [pv2,pv3,pv11,pv23,pv31,pv37], .c 3, .c 7,
  .c 193, .c 3, .c 11, .c 5, .c 3, .c 419, .c 7, .c 3, .c 5, .c 173, .c 3, .c 113, .c 13, .c 3,
  .c 103, .c 37, .c 3, .p pv2 [pv2,pv7,pv109,pv163], .c 5, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv5,pv127,pv457], .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv257,pv271], .c 7,
  .c 3, .c 59, .c 607, .c 3, .c 1667, .c 5, .c 3, .c 11,
]
private theorem h0425c02 : checkBlock 3482115 128 b0425c02 = true := by
  decide +kernel

private def b0425c03 : List Row := [
  .c 47, .c 3, .c 5, .c 19, .c 3, .c 7, .c 263, .c 3, .c 751, .p pv2 [pv2,pv3,pv7,pv13,pv1063],
  .c 3, .p pv3 [pv2,pv67,pv73,pv89], .c 5, .c 3, .c 17, .c 13, .c 3, .c 5, .c 23, .c 3,
  .p pv2 [pv2,pv5,pv348241], .c 11, .c 3, .c 41, .c 467, .c 3, .c 7, .c 5, .c 3, .c 61, .c 83,
  .c 3, .c 5, .c 7, .c 3, .c 43, .p pv2 [pv2,pv3,pv193469], .c 3, .c 31, .c 653, .c 3, .c 13,
  .c 5, .c 3, .c 67, .p pv7 [pv2,pv3,pv5,pv6449], .c 3, .c 5, .c 17, .c 3, .c 53, .c 1429, .c 3,
  .c 37, .c 7, .c 3, .c 733, .c 5, .c 3, .c 631, .c 19, .c 3, .c 5, .c 827, .c 3, .c 11, .c 191,
  .c 3, .c 7, .c 31, .c 3, .c 151, .c 5, .c 3, .p pv19 [pv2,pv13,pv17,pv7879], .c 7, .c 3, .c 5,
  .c 43, .c 3, .c 13, .c 103, .c 3, .c 487, .p pv2 [pv2,pv3,pv73,pv7951], .c 3,
  .p pv5 [pv2,pv7,pv248753], .c 5, .c 3, .c 7, .c 37, .c 3, .c 5, .c 13, .c 3,
  .p pv3 [pv2,pv5,pv10883], .c 7, .c 3, .c 11, .c 17, .c 3, .p pv2 [pv2,pv870643], .c 5, .c 3,
  .p pv2 [pv2,pv11,pv311,pv509], .c 29, .c 3, .c 5, .c 439, .c 3, .c 7, .c 59, .c 3, .c 83,
  .p pv3 [pv2,pv3,pv7,pv283,pv293], .c 3, .c 17, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 683,
  .c 3, .c 71, .p pv3 [pv2,pv3,pv11,pv13,pv41], .c 3,
]
private theorem h0425c03 : checkBlock 3482371 128 b0425c03 = true := by
  decide +kernel

private def b0425c04 : List Row := [
  .p pv2 [pv2,pv7,pv35537], .c 829, .c 3, .c 7, .c 5, .c 3, .c 29, .c 941, .c 3, .c 5, .c 7, .c 3,
  .c 233, .c 47, .c 3, .c 523, .c 89, .c 3, .c 41, .c 5, .c 3, .p pv2 [pv2,pv7,pv29,pv4289],
  .c 17, .c 3, .c 5, .c 11, .c 3, .c 19, .c 23, .c 3, .c 13, .c 7, .c 3,
  .p pv2 [pv2,pv71,pv12263], .c 5, .c 3, .c 11, .c 373, .c 3, .c 5, .p pv2 [pv2,pv3,pv23,pv25237],
  .c 3, .c 59, .c 13, .c 3, .c 7, .c 19, .c 3, .p pv2 [pv2,pv17,pv102433], .c 5, .c 3, .c 23,
  .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv37,pv53], .c 3, .p pv2 [pv2,pv5,pv174137], .c 11, .c 3,
  .c 47, .c 547, .c 3, .c 911, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv29023], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv131,pv211], .c 3, .c 1489, .c 7, .c 3, .c 1301,
  .p pv11 [pv2,pv3,pv13,pv44651], .c 3, .c 101, .c 5, .c 3, .c 53, .c 13, .c 3, .c 5, .c 457,
  .c 3, .c 7, .c 179, .c 3, .c 17, .c 11, .c 3, .c 29, .c 5, .c 3, .c 31, .c 23, .c 3, .c 5,
  .c 41, .c 3, .c 11, .c 19, .c 3, .c 89, .c 347, .c 3, .c 7, .c 5, .c 3, .c 569,
  .p pv7 [pv2,pv3,pv5,pv7,pv31,pv107], .c 3, .c 5, .c 7, .c 3, .c 67, .c 1787, .c 3, .c 23, .c 13,
  .c 3, .c 79, .c 5, .c 3, .c 317, .c 31,
]
private theorem h0425c04 : checkBlock 3482627 128 b0425c04 = true := by
  decide +kernel

private def b0425c05 : List Row := [
  .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv113,pv467], .c 3, .c 293, .c 449, .c 3, .c 11, .c 7, .c 3,
  .c 73, .c 5, .c 3, .c 17, .c 431, .c 3, .c 5, .c 61, .c 3, .c 13, .c 139, .c 3, .c 7, .c 29,
  .c 3, .c 421, .c 5, .c 3, .p pv2 [pv2,pv1741469], .c 7, .c 3, .c 5, .c 13, .c 3, .c 137,
  .p pv5 [pv2,pv3,pv11,pv79,pv167], .c 3, .c 43, .c 23, .c 3, .c 11, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv116099], .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv174149], .c 7, .c 3,
  .c 29, .p pv2 [pv2,pv3,pv290249], .c 3, .p pv3 [pv2,pv217687], .c 5, .c 3, .c 13, .c 53, .c 3,
  .c 5, .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv13,pv83,pv269], .c 3, .p pv3 [pv2,pv29,pv15013],
  .p pv2 [pv2,pv3,pv7,pv11,pv359], .c 3, .c 19, .c 5, .c 3, .c 11, .c 79, .c 3, .c 5, .c 223,
  .c 3, .p pv3 [pv2,pv5,pv11,pv1979], .c 43, .c 3, .c 71, .c 73, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv1741529], .c 19, .c 3, .c 5, .c 7, .c 3, .c 193, .c 11, .c 3, .c 13, .c 17, .c 3,
  .p pv2 [pv2,pv1741541], .c 5, .c 3, .p pv3 [pv2,pv7,pv137,pv227],
  .p pv3 [pv2,pv3,pv5,pv13,pv229], .c 3, .c 5, .c 23, .c 3, .c 1523, .c 13, .c 3, .c 53, .c 7,
  .c 3, .c 17, .c 5, .c 3, .c 167, .c 257, .c 3, .c 5, .c 251, .c 3, .c 643,
  .p pv7 [pv2,pv3,pv29,pv10009], .c 3, .c 7,
]
private theorem h0425c05 : checkBlock 3482883 128 b0425c05 = true := by
  decide +kernel

private def b0425c06 : List Row := [
  .c 11, .c 3, .c 23, .c 5, .c 3, .c 463, .c 7, .c 3, .c 5, .c 197, .c 3, .c 11, .c 271, .c 3,
  .p pv5 [pv2,pv23,pv75721], .c 1493, .c 3, .c 97, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 101,
  .c 3, .c 31, .c 7, .c 3, .c 367, .p pv3 [pv2,pv3,pv17,pv11383], .c 3, .c 1669, .c 5, .c 3,
  .p pv3 [pv2,pv435401], .c 1753, .c 3, .c 5, .c 37, .c 3, .c 7, .p pv5 [pv2,pv3,pv31,pv61,pv307],
  .c 3, .c 11, .c 127, .c 3, .c 13, .c 5, .c 3, .p pv7 [pv2,pv11,pv158329],
  .p pv7 [pv2,pv3,pv5,pv29027], .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv44657], .c 3, .c 19, .c 31,
  .c 3, .p pv3 [pv2,pv7,pv62201], .c 13, .c 3, .c 7, .c 5, .c 3, .c 701, .c 11, .c 3, .c 5, .c 7,
  .c 3, .c 23, .c 17, .c 3, .p pv5 [pv2,pv167,pv10429], .c 19, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv13,pv19139], .c 43, .c 3, .c 5, .c 1427, .c 3, .c 13, .c 109, .c 3, .c 17,
  .c 7, .c 3, .p pv2 [pv2,pv149,pv11689], .c 5, .c 3, .p pv3 [pv2,pv37,pv1471], .c 71, .c 3, .c 5,
  .c 11, .c 3, .c 73, .p pv5 [pv2,pv3,pv431,pv449], .c 3, .c 7, .c 577, .c 3, .c 467, .c 5, .c 3,
  .c 11, .c 7, .c 3, .c 5, .c 97, .c 3, .c 89, .c 23, .c 3, .c 31, .c 1553, .c 3,
  .p pv5 [pv2,pv7,pv248813], .c 5, .c 3, .c 7, .c 1093, .c 3,
]
private theorem h0425c06 : checkBlock 3483139 128 b0425c06 = true := by
  decide +kernel

private def b0425c07 : List Row := [
  .c 5, .c 67, .c 3, .c 41, .c 7, .c 3, .c 1627, .p pv7 [pv2,pv3,pv31,pv2341], .c 3,
  .p pv2 [pv2,pv870853], .c 5, .c 3, .c 17, .c 131, .c 3, .c 5, .c 83, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv16127], .c 3, .p pv2 [pv2,pv11,pv17,pv4657], .c 31, .c 3,
  .p pv2 [pv2,pv23,pv41,pv1847], .c 5, .c 3, .p pv3 [pv2,pv647,pv673], .c 29, .c 3, .c 5, .c 193,
  .c 3, .c 1249, .p pv3 [pv2,pv3,pv580577], .c 3, .c 13, .c 11, .c 3, .c 7, .c 5, .c 3, .c 19,
  .p pv31 [pv2,pv3,pv5,pv7,pv11,pv13,pv29],
]
private theorem h0425c07 : checkBlock 3483395 44 b0425c07 = true := by
  decide +kernel

def rows0425 : List Row :=
  b0425c00 ++ b0425c01 ++ b0425c02 ++ b0425c03 ++ b0425c04 ++ b0425c05 ++ b0425c06 ++ b0425c07

attribute [local irreducible] checkBlock checkRows checkPrime

theorem checked0425 : checkBlock 3481603 940 rows0425 = true :=
  checkBlock_append h0425c00 (
    checkBlock_append h0425c01 (
    checkBlock_append h0425c02 (
    checkBlock_append h0425c03 (
    checkBlock_append h0425c04 (
    checkBlock_append h0425c05 (
    checkBlock_append h0425c06 (
    h0425c07)))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
