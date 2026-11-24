/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks00/Block0068
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks00/Block0068.checked0068
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table013
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table016
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table022
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table035
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table036
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table081
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table082

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0068c00 : List Row := [
  .p pv2 [pv2,pv3,pv227,pv409], .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv139267], .c 97, .c 3, .c 5,
  .c 479, .c 3, .c 7, .c 23, .c 3, .p pv5 [pv2,pv278543], .c 13, .c 3, .p pv2 [pv2,pv139273],
  .c 5, .c 3, .c 19, .c 31, .c 3, .c 5, .c 17, .c 3, .c 149, .c 61, .c 3, .c 11, .c 29, .c 3,
  .c 7, .c 5, .c 3, .c 23, .c 467, .c 3, .c 5, .c 7, .c 3, .c 13, .c 131, .c 3, .c 191, .c 41,
  .c 3, .p pv3 [pv2,pv23,pv757], .c 5, .c 3, .p pv7 [pv2,pv7,pv17,pv2341], .c 11, .c 3, .c 5,
  .c 13, .c 3, .c 677, .c 631, .c 3, .c 29, .c 7, .c 3, .c 11, .c 5, .c 3, .c 53, .c 193, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv59,pv787], .c 3, .p pv13 [pv2,pv5,pv7,pv199], .c 113, .c 3, .c 7, .c 17,
  .c 3, .c 19, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 11, .c 3, .c 41, .c 173, .c 3, .c 43,
  .c 67, .c 3, .c 17, .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 37, .c 3,
  .p pv2 [pv2,pv5,pv11,pv17,pv149], .c 7, .c 3, .c 23, .p pv2 [pv2,pv3,pv46439], .c 3,
  .p pv3 [pv2,pv41,pv1699], .c 5, .c 3, .c 47, .p pv11 [pv2,pv3,pv5,pv43], .c 3, .c 5, .c 31,
  .c 3, .c 7, .c 11, .c 3, .c 13, .c 181, .c 3, .p pv5 [pv2,pv278651], .c 5, .c 3,
  .p pv2 [pv2,pv19,pv7333], .c 17, .c 3,
]
private theorem h0068c00 : checkBlock 557059 128 b0068c00 = true := by
  decide +kernel

private def b0068c01 : List Row := [
  .c 5, .c 109, .c 3, .p pv3 [pv2,pv5,pv13933], .c 13, .c 3, .c 19, .p pv7 [pv2,pv3,pv17,pv683],
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv191,pv1459], .c 151, .c 3, .c 5, .c 7, .c 3, .c 29,
  .c 349, .c 3, .c 61, .c 11, .c 3, .c 107, .c 5, .c 3, .p pv3 [pv2,pv7,pv37,pv269],
  .p pv3 [pv2,pv3,pv5,pv11,pv563], .c 3, .c 5, .p pv5 [pv2,pv3,pv2903], .c 3, .c 11, .c 499, .c 3,
  .c 353, .c 7, .c 3, .c 547, .c 5, .c 3, .c 199, .c 13, .c 3, .c 5, .c 89, .c 3, .c 31, .c 17,
  .c 3, .c 7, .c 101, .c 3, .p pv5 [pv2,pv19,pv14669], .c 5, .c 3, .c 113, .c 7, .c 3, .c 5,
  .c 389, .c 3, .c 19, .p pv3 [pv2,pv3,pv31,pv37], .c 3, .c 11, .p pv19 [pv2,pv3,pv23227], .c 3,
  .c 13, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv19,pv163], .c 3, .c 5, .c 29, .c 3, .c 251, .c 7,
  .c 3, .c 41, .c 13, .c 3, .p pv2 [pv2,pv278741], .c 5, .c 3, .p pv3 [pv2,pv34843], .c 11, .c 3,
  .c 5, .c 23, .c 3, .c 7, .c 79, .c 3, .c 53, .c 379, .c 3, .c 11, .c 5, .c 3,
  .p pv7 [pv2,pv13,pv41,pv523], .p pv11 [pv2,pv3,pv5,pv23,pv101], .c 3, .c 5, .c 359, .c 3, .c 13,
  .p pv5 [pv2,pv3,pv17,pv911], .c 3, .p pv3 [pv2,pv7,pv19,pv131], .c 103, .c 3, .c 7, .c 5, .c 3,
  .c 17, .p pv3 [pv2,pv3,pv5,pv7,pv59], .c 3, .c 5, .c 7, .c 3, .c 47, .c 71, .c 3,
  .p pv5 [pv2,pv17,pv23,pv31], .c 233,
]
private theorem h0068c01 : checkBlock 557315 128 b0068c01 = true := by
  decide +kernel

private def b0068c02 : List Row := [
  .c 3, .p pv2 [pv2,pv139393], .c 5, .c 3, .c 11, .c 43, .c 3, .c 5, .c 239, .c 3,
  .p pv11 [pv2,pv5,pv11,pv37,pv137], .c 19, .c 3, .c 31, .c 7, .c 3, .c 317, .c 5, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv5,pv18587], .c 3, .c 5, .c 17, .c 3, .c 101, .c 11, .c 3, .c 7, .c 347, .c 3,
  .p pv3 [pv2,pv8713], .c 5, .c 3, .p pv11 [pv2,pv278819], .c 7, .c 3, .c 5, .c 73, .c 3, .c 17,
  .c 97, .c 3, .c 127, .c 31, .c 3, .p pv7 [pv2,pv7,pv61,pv653], .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv29,pv641], .c 3, .c 5, .c 83, .c 3, .c 23, .c 7, .c 3, .c 13, .c 11,
  .c 3, .p pv2 [pv2,pv139423], .c 5, .c 3, .c 29, .c 37, .c 3, .c 5, .c 19, .c 3, .c 7, .c 13,
  .c 3, .p pv2 [pv2,pv139429], .c 17, .c 3, .c 41, .c 5, .c 3, .p pv3 [pv2,pv29,pv601],
  .p pv3 [pv2,pv3,pv5,pv6197], .c 3, .c 5, .c 443, .c 3, .p pv2 [pv2,pv5,pv79,pv353],
  .p pv5 [pv2,pv3,pv92957], .c 3, .p pv2 [pv2,pv7,pv39839], .c 47, .c 3, .c 7, .c 5, .c 3,
  .p pv11 [pv2,pv278879], .p pv11 [pv2,pv3,pv5,pv7,pv83], .c 3, .c 5, .c 7, .c 3, .c 541, .c 23,
  .c 3, .c 11, .p pv3 [pv2,pv3,pv13,pv7151], .c 3, .c 19, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv11,pv1811], .c 13, .c 3, .c 5, .c 199, .c 3, .p pv3 [pv2,pv5,pv2789],
  .p pv2 [pv2,pv3,pv7,pv19,pv233], .c 3, .c 139, .c 7, .c 3, .c 733, .c 5, .c 3, .c 23, .c 11,
  .c 3, .c 5,
]
private theorem h0068c02 : checkBlock 557571 128 b0068c02 = true := by
  decide +kernel

private def b0068c03 : List Row := [
  .c 503, .c 3, .p pv7 [pv2,pv5,pv7,pv13,pv613], .c 607, .c 3, .c 7, .c 43, .c 3, .c 11, .c 5,
  .c 3, .c 37, .c 7, .c 3, .c 5, .p pv31 [pv2,pv3,pv13,pv149], .c 3, .p pv3 [pv2,pv5,pv27893],
  .p pv3 [pv2,pv3,pv109,pv853], .c 3, .c 571, .c 13, .c 3, .c 29, .c 5, .c 3, .c 7, .c 113, .c 3,
  .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv47,pv1187], .c 7, .c 3, .c 19,
  .p pv3 [pv2,pv3,pv11,pv79,pv107], .c 3, .p pv5 [pv2,pv29,pv9619], .c 5, .c 3, .c 11, .c 23,
  .c 3, .c 5, .c 673, .c 3, .c 7, .c 17, .c 3, .p pv5 [pv2,pv83,pv3361], .c 131, .c 3, .c 563,
  .c 5, .c 3, .c 73, .c 89, .c 3, .c 5, .c 13, .c 3, .c 103, .c 11, .c 3, .c 17, .c 577, .c 3,
  .c 7, .c 5, .c 3, .c 31, .c 109, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv23,pv1213], .c 709,
  .c 3, .p pv2 [pv2,pv11,pv13,pv1951], .c 29, .c 3, .c 743, .c 5, .c 3, .c 13, .c 137, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv93001], .c 3, .c 19, .c 593, .c 3, .p pv3 [pv2,pv8719], .c 7, .c 3, .c 181,
  .c 5, .c 3, .p pv2 [pv2,pv61,pv2287], .c 31, .c 3, .c 5, .c 53, .c 3, .c 11, .c 67, .c 3, .c 7,
  .c 19, .c 3, .p pv3 [pv2,pv11,pv1153], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv281,pv331], .c 3, .c 37, .c 229, .c 3, .c 13, .c 313, .c 3,
]
private theorem h0068c03 : checkBlock 557827 128 b0068c03 = true := by
  decide +kernel

private def b0068c04 : List Row := [
  .p pv2 [pv2,pv7,pv39863], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv13,pv53], .c 3, .c 5, .c 43,
  .c 3, .c 197, .c 7, .c 3, .c 11, .p pv2 [pv2,pv3,pv37,pv419], .c 3, .p pv3 [pv2,pv107,pv163],
  .c 5, .c 3, .c 89, .p pv13 [pv2,pv3,pv5,pv4651], .c 3, .c 5, .c 17, .c 3, .c 7, .c 41, .c 3,
  .c 433, .p pv2 [pv2,pv3,pv7,pv97,pv137], .c 3, .c 53, .c 5, .c 3, .p pv2 [pv2,pv139537], .c 11,
  .c 3, .c 5, .c 103, .c 3, .c 17, .c 19, .c 3, .p pv5 [pv2,pv7,pv39869], .c 223, .c 3, .c 7,
  .c 5, .c 3, .p pv2 [pv2,pv17,pv16417], .c 13, .c 3, .c 5, .c 7, .c 3, .c 131, .c 227, .c 3,
  .p pv2 [pv2,pv53,pv2633], .c 59, .c 3, .p pv2 [pv2,pv71,pv3931], .c 5, .c 3,
  .p pv3 [pv2,pv7,pv89], .c 61, .c 3, .c 5, .c 11, .c 3, .c 29, .p pv5 [pv2,pv3,pv7,pv13291],
  .c 3, .c 101, .c 7, .c 3, .c 13, .c 5, .c 3, .c 11, .p pv11 [pv2,pv3,pv5,pv1163], .c 3, .c 5,
  .c 151, .c 3, .p pv7 [pv2,pv5,pv7,pv11,pv29], .p pv5 [pv2,pv3,pv1723], .c 3, .c 7, .c 13, .c 3,
  .c 17, .c 5, .c 3, .c 43, .c 7, .c 3, .c 5, .c 19, .c 3, .c 167, .c 11, .c 3,
  .p pv5 [pv2,pv279143], .p pv11 [pv2,pv3,pv3877], .c 3, .c 37, .c 5, .c 3, .c 7, .c 179, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv7,pv211], .c 3, .c 13, .c 7, .c 3, .c 59, .p pv11 [pv2,pv3,pv93053],
  .c 3, .c 347, .c 5, .c 3, .c 601, .c 17, .c 3, .c 5, .c 13,
]
private theorem h0068c04 : checkBlock 558083 128 b0068c04 = true := by
  decide +kernel

private def b0068c05 : List Row := [
  .c 3, .c 7, .p pv3 [pv2,pv3,pv31019], .c 3, .c 281, .c 11, .c 3, .c 19, .c 5, .c 3, .c 283,
  .c 647, .c 3, .c 5, .c 37, .c 3, .c 11, .c 509, .c 3, .c 73, .c 41, .c 3, .c 7, .c 5, .c 3,
  .c 13, .c 19, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv349], .c 31, .c 3, .c 47, .c 337, .c 3,
  .p pv2 [pv2,pv137,pv1019], .c 5, .c 3, .c 127, .p pv2 [pv2,pv3,pv5,pv41,pv227], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv8461], .c 3, .p pv31 [pv2,pv5,pv55843], .c 17, .c 3, .c 11, .c 7, .c 3,
  .c 613, .c 5, .c 3, .c 157, .c 79, .c 3, .c 5, .p pv5 [pv2,pv3,pv23269], .c 3, .c 41, .c 23,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv5171], .c 3, .p pv3 [pv2,pv69809], .c 5, .c 3,
  .p pv11 [pv2,pv37,pv7547], .c 7, .c 3, .c 5, .c 547, .c 3, .p pv2 [pv2,pv5,pv55849], .c 13,
  .c 3, .p pv3 [pv2,pv31,pv563], .p pv2 [pv2,pv3,pv93083], .c 3, .c 11, .c 5, .c 3, .c 7, .c 29,
  .c 3, .c 5, .c 211, .c 3, .p pv3 [pv2,pv5,pv13963], .c 7, .c 3, .c 31, .p pv7 [pv2,pv3,pv2909],
  .c 3, .p pv2 [pv2,pv13,pv23,pv467], .c 5, .c 3, .p pv2 [pv2,pv279269],
  .p pv2 [pv2,pv3,pv5,pv29,pv107], .c 3, .c 5, .c 11, .c 3, .c 7, .c 59, .c 3, .c 71, .c 113,
  .c 3, .p pv2 [pv2,pv19,pv14699], .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 61, .c 3, .c 19,
  .p pv3 [pv2,pv3,pv93097], .c 3, .p pv2 [pv2,pv7,pv17,pv2347], .c 31, .c 3, .c 7,
]
private theorem h0068c05 : checkBlock 558339 128 b0068c05 = true := by
  decide +kernel

private def b0068c06 : List Row := [
  .c 5, .c 3, .p pv13 [pv2,pv29,pv9631], .c 23, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv13,pv4297], .c 11, .c 3, .c 173, .c 19, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv71,pv281], .c 101, .c 3, .c 5, .c 17, .c 3, .c 139,
  .p pv2 [pv2,pv3,pv7,pv47,pv283], .c 3, .c 23, .c 7, .c 3, .c 89, .c 5, .c 3, .c 179,
  .p pv7 [pv2,pv3,pv5,pv9311], .c 3, .c 5, .c 421, .c 3, .c 17, .c 53, .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv31,pv9011], .c 5, .c 3, .c 47, .c 7, .c 3, .c 5, .c 701, .c 3, .c 11,
  .p pv5 [pv2,pv3,pv31039], .c 3, .c 41, .c 277, .c 3, .c 31, .c 5, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv5,pv97], .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv59,pv947], .c 7, .c 3,
  .c 37, .c 17, .c 3, .c 29, .c 5, .c 3, .c 349, .c 293, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv17,pv83], .c 3, .c 7, .c 157, .c 3, .c 11, .p pv11 [pv2,pv3,pv7,pv1663],
  .c 3, .c 17, .c 5, .c 3, .c 13, .p pv7 [pv2,pv3,pv5,pv67,pv139], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv93131], .c 3, .p pv29 [pv2,pv5,pv17,pv19,pv173], .p pv5 [pv2,pv3,pv13,pv199],
  .c 3, .c 383, .c 353, .c 3, .c 7, .c 5, .c 3, .c 19, .c 11, .c 3, .c 5, .c 7, .c 3, .c 61,
  .c 137, .c 3, .p pv2 [pv2,pv279413], .p pv11 [pv2,pv3,pv19,pv43], .c 3, .c 11, .c 5, .c 3,
  .c 83, .c 17, .c 3, .c 5, .c 19, .c 3,
]
private theorem h0068c06 : checkBlock 558595 128 b0068c06 = true := by
  decide +kernel

private def b0068c07 : List Row := [
  .c 151, .c 541, .c 3, .c 13, .c 7, .c 3, .p pv5 [pv2,pv279431], .c 5, .c 3,
  .p pv2 [pv2,pv31,pv4507], .c 41, .c 3, .c 5, .c 11, .c 3, .p pv13 [pv2,pv5,pv7,pv499], .c 13,
  .c 3, .c 7, .c 197, .c 3, .p pv2 [pv2,pv17,pv8219], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 59,
  .c 3, .c 457, .p pv7 [pv2,pv3,pv41,pv71], .c 3, .c 29, .c 139, .c 3, .c 19, .c 5, .c 3, .c 7,
  .p pv29 [pv2,pv3,pv5,pv31,pv601], .c 3, .c 5, .p pv37 [pv2,pv3,pv7,pv1109], .c 3, .c 367, .c 7,
  .c 3, .p pv2 [pv2,pv23,pv29,pv419], .c 167, .c 3, .c 41, .c 5, .c 3, .c 37, .c 13, .c 3, .c 5,
  .c 233, .c 3, .c 7, .p pv5 [pv2,pv3,pv15527], .c 3, .c 17, .p pv2 [pv2,pv3,pv7,pv13309], .c 3,
  .c 71, .c 5, .c 3, .c 229, .c 53, .c 3, .c 5, .p pv11 [pv2,pv3,pv37,pv1259], .c 3,
  .p pv17 [pv2,pv5,pv13,pv43], .c 433, .c 3, .c 431, .c 11, .c 3, .c 7, .c 5, .c 3, .c 691,
  .c 239, .c 3, .c 5, .c 7, .c 3, .c 11, .c 29, .c 3, .c 19, .c 13, .c 3, .c 43, .c 5, .c 3,
  .p pv11 [pv2,pv7,pv67,pv149], .p pv2 [pv2,pv3,pv5,pv3727], .c 3, .c 5, .c 191, .c 3, .c 23,
  .c 727, .c 3, .p pv2 [pv2,pv443,pv631], .c 7, .c 3, .c 271, .c 5, .c 3, .c 17,
  .p pv7 [pv2,pv3,pv5,pv1553], .c 3, .c 5, .c 523, .c 3, .c 13, .p pv2 [pv2,pv3,pv46591], .c 3,
  .c 7, .p pv2 [pv2,pv3,pv89,pv349], .c 3, .c 409, .c 5,
]
private theorem h0068c07 : checkBlock 558851 128 b0068c07 = true := by
  decide +kernel

private def b0068c08 : List Row := [
  .c 3, .c 181, .c 7, .c 3, .c 5, .c 13, .c 3, .c 193, .p pv3 [pv2,pv3,pv93187], .c 3, .c 373,
  .c 43, .c 3, .p pv2 [pv2,pv7,pv19,pv1051], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 17, .c 3,
  .c 19, .c 7, .c 3, .p pv2 [pv2,pv13,pv10753], .c 47, .c 3, .c 11, .c 5, .c 3, .c 13, .c 83,
  .c 3, .c 5, .p pv7 [pv2,pv3,pv23,pv1013], .c 3, .c 7, .p pv5 [pv2,pv3,pv13,pv67,pv107], .c 3,
  .c 61, .c 19, .c 3, .c 461, .c 5, .c 3, .c 23, .p pv7 [pv2,pv3,pv5,pv233], .c 3, .c 5, .c 11,
  .c 3, .p pv7 [pv2,pv5,pv55921], .p pv2 [pv2,pv3,pv46601], .c 3, .p pv11 [pv2,pv7,pv4993],
  .p pv2 [pv2,pv3,pv11,pv37,pv229], .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv5,pv7,pv2663], .c 3, .c 5, .c 7, .c 3, .c 79, .p pv5 [pv2,pv3,pv31069], .c 3,
  .c 13, .c 17, .c 3, .c 47, .c 5, .c 3, .p pv2 [pv2,pv7,pv43,pv929], .c 59, .c 3, .c 5, .c 71,
  .c 3, .c 31, .c 11, .c 3, .p pv2 [pv2,pv89,pv1571], .c 7, .c 3, .c 17, .c 5, .c 3, .c 107,
  .c 23, .c 3, .c 5, .p pv11 [pv2,pv3,pv971], .c 3, .c 43, .c 19, .c 3, .c 7, .c 53, .c 3,
  .p pv3 [pv2,pv13,pv2689], .c 5, .c 3, .p pv13 [pv2,pv279659], .c 7, .c 3, .c 5, .c 569, .c 3,
  .c 313, .c 31, .c 3, .c 23, .c 11, .c 3, .p pv5 [pv2,pv7,pv39953], .c 5, .c 3, .c 7, .c 13,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv6659], .c 3, .c 11,
]
private theorem h0068c08 : checkBlock 559107 128 b0068c08 = true := by
  decide +kernel

private def b0068c09 : List Row := [
  .c 7, .c 3, .p pv5 [pv2,pv37,pv7559], .p pv11 [pv2,pv3,pv17,pv457], .c 3, .c 397, .c 5, .c 3,
  .c 19, .c 29, .c 3, .c 5, .c 43, .c 3, .c 7, .c 103, .c 3, .p pv2 [pv2,pv107,pv1307], .c 73,
  .c 3, .c 13, .c 5, .c 3, .c 71, .c 587, .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv83,pv337],
  .c 739, .c 3, .c 11, .c 13, .c 3, .c 7, .c 5, .c 3, .c 29, .c 47, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv67,pv167], .c 17, .c 3, .c 31, .p pv2 [pv2,pv3,pv31081], .c 3, .c 113, .c 5,
  .c 3, .p pv2 [pv2,pv7,pv13,pv29,pv53], .c 11, .c 3, .c 5, .c 37, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv7,pv11,pv173], .c 3, .c 17, .c 7, .c 3, .c 11, .c 5, .c 3, .c 239, .c 131,
  .c 3, .c 5, .c 13, .c 3, .p pv7 [pv2,pv5,pv7,pv7993], .p pv5 [pv2,pv3,pv19,pv409], .c 3, .c 7,
  .c 31, .c 3, .p pv2 [pv2,pv279761], .c 5, .c 3, .p pv3 [pv2,pv69941], .c 7, .c 3, .c 5, .c 11,
  .c 3, .p pv2 [pv2,pv5,pv101,pv277], .c 89, .c 3, .p pv2 [pv2,pv13,pv21521],
  .p pv17 [pv2,pv3,pv11,pv157], .c 3, .c 61, .c 5, .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv4663], .c 3,
  .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv11,pv5087], .c 7, .c 3, .p pv3 [pv2,pv113,pv619], .c 163,
  .c 3, .p pv5 [pv2,pv47,pv5953], .c 5, .c 3, .c 17, .p pv3 [pv2,pv3,pv5,pv23,pv811], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv46633], .c 3, .c 7, .c 11, .c 3, .c 19, .c 41, .c 3, .c 23, .c 5, .c 3,
]
private theorem h0068c09 : checkBlock 559363 128 b0068c09 = true := by
  decide +kernel

private def b0068c10 : List Row := [
  .c 617, .c 653, .c 3, .c 5, .c 53, .c 3, .p pv13 [pv2,pv5,pv191,pv293],
  .p pv5 [pv2,pv3,pv89,pv131], .c 3, .c 13, .p pv3 [pv2,pv3,pv31091], .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv17489], .c 67, .c 3, .c 5, .c 7, .c 3, .c 307, .c 13, .c 3,
  .p pv2 [pv2,pv233,pv1201], .c 11, .c 3, .p pv3 [pv2,pv69959], .c 5, .c 3,
  .p pv7 [pv2,pv7,pv5711], .c 359, .c 3, .c 5, .p pv3 [pv2,pv3,pv93281], .c 3, .c 11, .c 71, .c 3,
  .c 631, .c 7, .c 3, .p pv5 [pv2,pv11,pv13,pv19,pv103], .c 5, .c 3, .p pv2 [pv2,pv17,pv8231],
  .c 347, .c 3, .c 5, .c 107, .c 3, .c 19, .c 47, .c 3, .c 7, .c 29, .c 3, .c 53, .c 5, .c 3,
  .p pv2 [pv2,pv239,pv1171], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv257], .c 3, .c 23, .c 139,
  .c 3, .c 11, .c 17, .c 3, .c 131, .c 5, .c 3, .c 7, .c 389, .c 3, .c 5,
  .p pv19 [pv2,pv3,pv7,pv17], .c 3, .p pv2 [pv2,pv5,pv13,pv2153], .c 7, .c 3, .c 29, .c 269, .c 3,
  .c 13, .c 5, .c 3, .p pv7 [pv2,pv31,pv9029], .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv7177],
  .c 3, .c 7, .p pv5 [pv2,pv3,pv11,pv4241], .c 3, .c 43, .c 13, .c 3, .c 11, .c 5, .c 3, .c 31,
  .p pv29 [pv2,pv3,pv5,pv18661], .c 3, .c 5, .c 73, .c 3, .p pv3 [pv2,pv5,pv3499], .c 23, .c 3,
  .c 37, .p pv7 [pv2,pv3,pv23327], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv13,pv61,pv353], .c 17,
  .c 3, .c 5, .c 7, .c 3, .c 13, .c 19,
]
private theorem h0068c10 : checkBlock 559619 128 b0068c10 = true := by
  decide +kernel

private def b0068c11 : List Row := [
  .c 3, .p pv2 [pv2,pv139969], .c 677, .c 3, .p pv2 [pv2,pv279941], .c 5, .c 3, .c 11, .c 31,
  .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv11,pv509], .c 29, .c 3, .p pv2 [pv2,pv71,pv3943],
  .c 7, .c 3, .p pv3 [pv2,pv17,pv23,pv179], .c 5, .c 3, .c 61, .c 37, .c 3, .c 5, .c 263, .c 3,
  .c 107, .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv93323], .c 3, .c 127, .c 5, .c 3, .c 13, .c 7,
  .c 3, .c 5, .c 313, .c 3, .c 29, .c 17, .c 3, .p pv5 [pv2,pv11,pv25453], .c 59, .c 3,
  .p pv2 [pv2,pv7,pv2857], .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 19, .c 3,
  .p pv11 [pv2,pv5,pv29,pv1931], .c 7, .c 3, .c 17, .c 11, .c 3, .c 257, .c 5, .c 3, .c 227,
  .c 103, .c 3, .c 5, .p pv5 [pv2,pv3,pv3889], .c 3, .c 7, .p pv3 [pv2,pv3,pv93337], .c 3, .c 13,
  .p pv2 [pv2,pv3,pv7,pv59,pv113], .c 3, .c 281, .c 5, .c 3, .p pv7 [pv2,pv107,pv2617], .c 61,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv31,pv3011], .c 3, .c 53, .c 13, .c 3, .c 283, .c 151, .c 3, .c 7,
  .c 5, .c 3, .c 37, .c 197, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv7001],
  .p pv3 [pv2,pv3,pv17,pv19], .c 3, .c 11, .p pv7 [pv2,pv3,pv2593], .c 3,
  .p pv2 [pv2,pv13,pv10771], .c 5, .c 3, .c 17, .c 19, .c 3, .c 5, .p pv2 [pv2,pv3,pv29,pv37],
  .c 3, .c 311, .p pv13 [pv2,pv3,pv7,pv1667], .c 3, .p pv2 [pv2,pv17,pv8237], .c 7, .c 3,
  .p pv2 [pv2,pv280061], .c 5, .c 3, .c 73,
]
private theorem h0068c11 : checkBlock 559875 128 b0068c11 = true := by
  decide +kernel

private def b0068c12 : List Row := [
  .c 11, .c 3, .c 5, .p pv13 [pv2,pv3,pv23339], .c 3, .c 113, .c 37, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv46679], .c 3, .c 11, .c 5, .c 3, .p pv13 [pv2,pv19,pv14741], .c 7, .c 3, .c 5,
  .c 17, .c 3, .p pv31 [pv2,pv5,pv13,pv31,pv139], .p pv2 [pv2,pv3,pv46681], .c 3, .c 19,
  .p pv3 [pv2,pv3,pv31121], .c 3, .c 13, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv71,pv263], .c 3,
  .c 5, .c 11, .c 3, .c 17, .c 7, .c 3, .p pv5 [pv2,pv280103], .c 13, .c 3, .p pv2 [pv2,pv140053],
  .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv9337], .c 3, .c 5, .p pv13 [pv2,pv3,pv93371], .c 3,
  .c 7, .p pv5 [pv2,pv3,pv31,pv251], .c 3, .p pv2 [pv2,pv227,pv617],
  .p pv11 [pv2,pv3,pv7,pv13339], .c 3, .p pv2 [pv2,pv280121], .c 5, .c 3,
  .p pv3 [pv2,pv13,pv5387], .c 29, .c 3, .c 5, .c 23, .c 3, .c 13, .c 11, .c 3, .c 577, .c 17,
  .c 3, .c 7, .c 5, .c 3, .c 193, .p pv11 [pv2,pv3,pv5,pv7,pv23,pv29], .c 3, .c 5, .c 7, .c 3,
  .c 19, .p pv2 [pv2,pv3,pv46691], .c 3, .p pv3 [pv2,pv11,pv6367], .p pv3 [pv2,pv3,pv93383], .c 3,
  .c 17, .c 5, .c 3, .c 29, .p pv11 [pv2,pv3,pv5,pv19,pv983], .c 3, .c 5,
  .p pv11 [pv2,pv3,pv53,pv881], .c 3, .c 67, .c 59, .c 3, .c 269, .c 7, .c 3, .c 43, .c 5, .c 3,
  .c 13, .p pv2 [pv2,pv3,pv5,pv11,pv283], .c 3, .c 5, .c 41, .c 3, .c 11,
  .p pv5 [pv2,pv3,pv13,pv449], .c 3, .c 7, .c 107, .c 3, .c 229, .c 5, .c 3, .c 53, .c 7, .c 3,
  .c 5, .c 499, .c 3, .c 47, .c 331, .c 3,
]
private theorem h0068c12 : checkBlock 560131 128 b0068c12 = true := by
  decide +kernel

private def b0068c13 : List Row := [
  .c 31, .c 149, .c 3, .p pv3 [pv2,pv7,pv10007], .c 5, .c 3, .c 7, .c 691, .c 3, .c 5, .c 61,
  .c 3, .p pv11 [pv2,pv5,pv56041], .c 7, .c 3, .c 11, .c 43, .c 3, .c 103, .c 5, .c 3, .c 41,
  .c 337, .c 3, .c 5, .p pv7 [pv2,pv3,pv46703], .c 3, .c 7, .c 13, .c 3, .p pv5 [pv2,pv280223],
  .c 31, .c 3, .c 263, .c 5, .c 3, .p pv2 [pv2,pv280229], .c 11, .c 3, .c 5, .c 137, .c 3,
  .p pv7 [pv2,pv5,pv41,pv1367], .c 17, .c 3, .p pv2 [pv2,pv7,pv37,pv541],
  .p pv43 [pv2,pv3,pv109,pv857], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv70061],
  .p pv2 [pv2,pv3,pv5,pv7,pv17,pv157], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv19,pv59],
  .p pv5 [pv2,pv3,pv31139], .c 3, .c 17, .c 293, .c 3, .c 37, .c 5, .c 3, .c 19, .c 13, .c 3,
  .c 5, .c 11, .c 3, .p pv17 [pv2,pv5,pv56053], .c 23, .c 3, .c 487, .c 7, .c 3,
  .p pv5 [pv2,pv31,pv9041], .c 5, .c 3, .c 11, .p pv29 [pv2,pv3,pv5,pv37,pv101], .c 3, .c 5,
  .c 19, .c 3, .p pv17 [pv2,pv5,pv7,pv11,pv13], .c 97, .c 3, .c 7, .c 47, .c 3, .c 13, .c 5, .c 3,
  .c 23, .c 7, .c 3, .c 5, .c 37, .c 3, .c 43, .c 11, .c 3, .p pv2 [pv2,pv269,pv521], .c 13, .c 3,
  .c 439, .c 5, .c 3, .c 7, .c 89, .c 3, .c 5, .p pv31 [pv2,pv3,pv7,pv47,pv71], .c 3,
  .p pv2 [pv2,pv5,pv28031], .c 7, .c 3, .c 211, .c 103, .c 3, .c 19, .c 5, .c 3,
  .p pv7 [pv2,pv13,pv21563], .p pv41 [pv2,pv3,pv5,pv73],
]
private theorem h0068c13 : checkBlock 560387 128 b0068c13 = true := by
  decide +kernel

private def b0068c14 : List Row := [
  .c 3, .c 5, .c 157, .c 3, .c 7, .p pv2 [pv2,pv3,pv19,pv2459], .c 3, .c 29, .c 11, .c 3, .c 47,
  .c 5, .c 3, .p pv2 [pv2,pv140167], .c 19, .c 3, .c 5, .c 13, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv3461], .c 3, .c 53, .p pv7 [pv2,pv3,pv11681], .c 3, .c 7, .c 5, .c 3, .c 271,
  .p pv13 [pv2,pv3,pv5,pv7,pv89], .c 3, .c 5, .c 7, .c 3, .c 17, .c 73, .c 3, .c 23,
  .p pv11 [pv2,pv3,pv31151], .c 3, .c 67, .c 5, .c 3, .c 13, .c 431, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv11,pv59], .c 3, .c 137, .c 683, .c 3, .c 11, .c 7, .c 3,
  .p pv3 [pv2,pv101,pv347], .c 5, .c 3, .c 31, .p pv7 [pv2,pv3,pv5,pv4673], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv19,pv4919], .c 3, .p pv2 [pv2,pv5,pv7,pv8011], .c 29, .c 3, .c 7, .c 17, .c 3,
  .p pv5 [pv2,pv199,pv1409], .c 5, .c 3, .c 89, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv2749],
  .c 3, .c 449, .p pv2 [pv2,pv3,pv11,pv29,pv293], .c 3, .c 13, .c 23, .c 3, .c 11, .c 5, .c 3,
  .c 7, .c 31, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv4451], .c 3, .c 29, .c 7, .c 3,
  .p pv2 [pv2,pv149,pv941], .c 41, .c 3, .c 349, .c 5, .c 3, .c 43, .c 47, .c 3, .c 5, .c 11,
  .c 3, .c 7, .p pv5 [pv2,pv3,pv31159], .c 3, .c 467, .p pv2 [pv2,pv3,pv7,pv11,pv607], .c 3,
  .p pv3 [pv2,pv13,pv5393], .c 5, .c 3, .c 11, .c 17, .c 3, .c 5, .p pv3 [pv2,pv3,pv93481], .c 3,
  .p pv2 [pv2,pv5,pv11,pv5099], .p pv5 [pv2,pv3,pv43,pv1087], .c 3, .p pv3 [pv2,pv7,pv313],
]
private theorem h0068c14 : checkBlock 560643 128 b0068c14 = true := by
  decide +kernel

private def b0068c15 : List Row := [
  .c 19, .c 3, .c 7, .c 5, .c 3, .c 479, .c 13, .c 3, .c 5, .c 7, .c 3, .c 41, .c 11, .c 3,
  .c 653, .p pv11 [pv2,pv3,pv5843], .c 3, .c 239, .c 5, .c 3, .p pv2 [pv2,pv7,pv103,pv389],
  .p pv2 [pv2,pv3,pv5,pv9349], .c 3, .c 5, .c 23, .c 3, .c 97, .c 167, .c 3, .c 37, .c 7, .c 3,
  .c 13, .c 5, .c 3, .p pv3 [pv2,pv70121], .c 71, .c 3, .c 5, .p pv17 [pv2,pv3,pv13,pv29,pv31],
  .c 3, .c 199, .c 17, .c 3, .c 7, .c 11, .c 3, .c 23, .c 5, .c 3, .c 401, .c 7, .c 3, .c 5,
  .c 31, .c 3, .c 11, .c 19, .c 3, .c 17, .p pv3 [pv2,pv3,pv93503], .c 3, .c 109, .c 5, .c 3,
  .c 7, .c 37, .c 3, .c 5, .c 461, .c 3, .c 13, .c 7, .c 3, .p pv5 [pv2,pv163,pv1721], .c 211,
  .c 3, .p pv2 [pv2,pv140263], .c 5, .c 3, .p pv2 [pv2,pv53,pv67,pv79],
  .p pv2 [pv2,pv3,pv5,pv1039], .c 3, .c 5, .c 13, .c 3, .c 7, .c 131, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv7,pv61,pv73], .c 3, .p pv2 [pv2,pv280541], .c 5, .c 3, .c 19,
  .p pv3 [pv2,pv3,pv5,pv59,pv317], .c 3, .c 5, .p pv17 [pv2,pv3,pv7793], .c 3,
  .p pv3 [pv2,pv5,pv31,pv181], .p pv3 [pv2,pv3,pv17,pv5501], .c 3, .c 43,
  .p pv11 [pv2,pv3,pv19,pv23,pv107], .c 3, .c 7, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 7, .c 3,
  .c 23, .c 47, .c 3, .c 79, .c 61, .c 3, .c 11, .c 5, .c 3, .c 59, .c 73, .c 3,
]
private theorem h0068c15 : checkBlock 560899 128 b0068c15 = true := by
  decide +kernel

private def b0068c16 : List Row := [
  .c 5, .c 281, .c 3, .p pv3 [pv2,pv5,pv14029], .c 83, .c 3, .c 41, .c 7, .c 3,
  .p pv2 [pv2,pv239,pv587], .c 5, .c 3, .c 29, .p pv2 [pv2,pv3,pv5,pv47,pv199], .c 3, .c 5, .c 11,
  .c 3, .p pv7 [pv2,pv5,pv7,pv8017], .c 31, .c 3, .c 7, .p pv3 [pv2,pv3,pv11,pv773], .c 3, .c 19,
  .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 53, .c 3, .c 17, .c 13, .c 3, .c 47,
  .p pv2 [pv2,pv3,pv46769], .c 3, .c 677, .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 103, .c 3,
  .p pv11 [pv2,pv5,pv449], .c 7, .c 3, .c 101, .c 67, .c 3, .c 599, .c 5, .c 3, .c 23, .c 113,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv5197], .c 3, .c 7, .c 149, .c 3, .c 167, .c 17, .c 3, .c 571,
  .c 5, .c 3, .c 379, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv5503], .c 3, .c 563,
  .p pv5 [pv2,pv3,pv1949], .c 3, .c 19, .c 11, .c 3, .c 7, .c 5, .c 3, .c 83, .c 41, .c 3, .c 5,
  .c 7, .c 3, .c 11, .p pv5 [pv2,pv3,pv93557], .c 3, .p pv2 [pv2,pv280673], .c 191, .c 3, .c 13,
  .c 5, .c 3, .p pv13 [pv2,pv7,pv101,pv397], .c 23, .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv2399],
  .c 3, .c 227, .p pv2 [pv2,pv3,pv7,pv41,pv163], .c 3, .p pv3 [pv2,pv53,pv331], .c 7, .c 3, .c 61,
  .c 5, .c 3, .p pv2 [pv2,pv293,pv479], .c 17, .c 3, .c 5, .c 71, .c 3, .c 37, .c 269, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv17,pv43],
]
private theorem h0068c16 : checkBlock 561155 128 b0068c16 = true := by
  decide +kernel

private def b0068c17 : List Row := [
  .c 3, .c 41, .c 5, .c 3, .p pv2 [pv2,pv11,pv13,pv151], .c 7, .c 3, .c 5, .c 509, .c 3, .c 13,
  .c 619, .c 3, .c 193, .p pv23 [pv2,pv3,pv37,pv281], .c 3, .c 73, .c 5, .c 3, .c 7, .c 11, .c 3,
  .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv67,pv419], .c 7, .c 3, .c 127, .c 19, .c 3, .c 11, .c 5,
  .c 3, .c 277, .c 439, .c 3, .c 5, .c 251, .c 3, .c 7, .c 17, .c 3, .c 113, .c 23, .c 3, .c 31,
  .c 5, .c 3, .c 13, .c 487, .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv7019], .c 179, .c 3,
  .c 17, .p pv7 [pv2,pv3,pv11,pv709], .c 3, .c 7, .c 5, .c 3, .c 11, .c 349, .c 3, .c 5, .c 7,
  .c 3, .p pv7 [pv2,pv5,pv11,pv1021], .p pv5 [pv2,pv3,pv11699], .c 3, .c 409,
  .p pv3 [pv2,pv3,pv173,pv541], .c 3, .c 137, .c 5, .c 3, .c 151, .c 593, .c 3, .c 5, .c 41, .c 3,
  .c 149, .c 11, .c 3, .c 13, .c 7, .c 3, .c 431, .c 5, .c 3, .p pv11 [pv2,pv227,pv1237], .c 433,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv93601], .c 3, .c 79, .c 13, .c 3, .c 7, .c 463, .c 3, .c 37, .c 5,
  .c 3, .c 17, .c 7, .c 3, .c 5, .c 23, .c 3, .c 53, .c 29, .c 3, .c 197, .c 11, .c 3, .c 457,
  .c 5, .c 3, .c 7, .c 67, .c 3, .c 5,
]
private theorem h0068c17 : checkBlock 561411 128 b0068c17 = true := by
  decide +kernel

private def b0068c18 : List Row := [
  .p pv3 [pv2,pv3,pv7,pv43,pv311], .c 3, .c 11, .c 7, .c 3, .c 109, .c 89, .c 3, .c 23, .c 5,
  .c 3, .c 31, .c 13, .c 3, .c 5, .c 17, .c 3, .c 7, .p pv3 [pv2,pv3,pv179,pv523], .c 3, .c 331,
  .c 43, .c 3, .p pv3 [pv2,pv35107], .c 5, .c 3, .c 281, .c 127, .c 3, .c 5, .c 97, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv46811], .c 3, .c 11, .c 59, .c 3, .c 7, .c 5, .c 3, .c 61, .c 31, .c 3, .c 5,
  .c 7, .c 3, .p pv3 [pv2,pv5,pv3511], .c 233, .c 3, .p pv5 [pv2,pv280883], .c 13, .c 3, .c 19,
  .c 5, .c 3, .c 337, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv109,pv859], .c 3, .c 47, .c 347, .c 3,
  .p pv2 [pv2,pv140449], .c 7, .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv13,pv37,pv73], .c 19, .c 3,
  .c 5, .c 29, .c 3, .c 13, .c 41, .c 3, .c 7, .p pv2 [pv2,pv3,pv46819], .c 3, .c 17, .c 5, .c 3,
  .p pv13 [pv2,pv43,pv47,pv139], .c 7, .c 3, .c 5, .c 11, .c 3, .c 503, .c 53, .c 3, .c 59,
  .c 131, .c 3, .c 101, .c 5, .c 3, .c 7, .c 61, .c 3, .c 5, .c 367, .c 3, .c 43, .c 7, .c 3,
  .c 19, .c 239, .c 3, .c 211, .c 5, .c 3, .c 13, .c 17, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv19,pv31,pv53], .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv59,pv2381], .c 37, .c 3,
]
private theorem h0068c18 : checkBlock 561667 128 b0068c18 = true := by
  decide +kernel

private def b0068c19 : List Row := [
  .p pv2 [pv2,pv191,pv1471], .c 5, .c 3, .c 67, .p pv2 [pv2,pv3,pv5,pv18731], .c 3, .c 5, .c 31,
  .c 3, .c 269, .p pv3 [pv2,pv3,pv31219], .c 3, .p pv2 [pv2,pv7,pv11,pv41,pv89], .c 113, .c 3,
  .c 7, .c 5, .c 3, .c 23, .p pv31 [pv2,pv3,pv5,pv7,pv223], .c 3, .c 5, .c 7, .c 3, .c 727,
  .p pv5 [pv2,pv3,pv46831], .c 3, .c 13, .c 11, .c 3, .p pv5 [pv2,pv19,pv23,pv643], .c 5, .c 3,
  .c 251, .c 29, .c 3, .c 5, .p pv2 [pv2,pv3,pv67,pv233], .c 3, .c 11, .c 13, .c 3,
  .p pv5 [pv2,pv79,pv3557], .c 7, .c 3, .c 557, .c 5, .c 3, .p pv2 [pv2,pv97,pv2897],
  .p pv31 [pv2,pv3,pv5,pv17,pv19,pv29], .c 3, .c 5, .c 73, .c 3, .c 263, .c 277, .c 3, .c 7,
  .c 19, .c 3, .p pv2 [pv2,pv13,pv21617], .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .c 379, .c 3,
  .c 31, .c 67, .c 3, .c 11, .c 41, .c 3, .c 47, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 617,
  .c 3, .p pv2 [pv2,pv5,pv56209], .c 7, .c 3, .c 23, .c 541, .c 3, .p pv5 [pv2,pv127,pv2213],
  .c 5, .c 3, .c 683, .c 11, .c 3, .c 5, .c 307, .c 3, .c 7, .c 31, .c 3, .c 659,
  .p pv11 [pv2,pv3,pv7,pv239], .c 3, .c 11, .c 5, .c 3, .c 17, .c 37, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv7207], .c 3, .c 41, .c 19, .c 3, .c 641, .c 13, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv70271], .c 53, .c 3, .c 5, .c 7,
]
private theorem h0068c19 : checkBlock 561923 128 b0068c19 = true := by
  decide +kernel

private def b0068c20 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv28109], .c 223, .c 3, .c 163, .c 23, .c 3, .p pv3 [pv2,pv41,pv857],
  .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv937], .c 3, .c 5, .c 17, .c 3, .c 13, .c 89, .c 3,
  .c 157, .c 7, .c 3, .c 29, .c 5, .c 3, .c 19, .p pv13 [pv2,pv3,pv5,pv6247], .c 3, .c 5, .c 13,
  .c 3, .c 17, .c 11, .c 3, .c 7, .c 71, .c 3, .c 241, .c 5, .c 3, .p pv2 [pv2,pv17,pv23,pv719],
  .c 7, .c 3, .c 5, .c 19, .c 3, .p pv13 [pv2,pv5,pv59,pv953], .p pv5 [pv2,pv3,pv5857], .c 3,
  .c 53, .c 227, .c 3, .p pv2 [pv2,pv7,pv40163], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv18743],
  .c 3, .c 5, .p pv17 [pv2,pv3,pv7,pv3347], .c 3, .p pv2 [pv2,pv5,pv5623], .c 7, .c 3,
  .p pv2 [pv2,pv281153], .c 11, .c 3, .p pv3 [pv2,pv70289], .c 5, .c 3, .c 73, .c 283, .c 3, .c 5,
  .c 23, .c 3, .c 7, .p pv5 [pv2,pv3,pv46861], .c 3, .p pv3 [pv2,pv17573], .c 29, .c 3, .c 17,
  .c 5, .c 3, .p pv2 [pv2,pv140587], .p pv11 [pv2,pv3,pv5,pv23,pv163], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv41,pv127], .c 3, .p pv3 [pv2,pv5,pv17,pv827], .c 37, .c 3, .c 13, .c 331,
  .c 3, .c 7, .c 5, .c 3, .c 739, .c 19, .c 3, .c 5, .c 7, .c 3, .c 71, .c 13, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv67,pv1399], .c 3, .p pv2 [pv2,pv31,pv47,pv193], .c 5, .c 3,
  .p pv29 [pv2,pv7,pv11,pv83], .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv11717], .c 3,
  .p pv2 [pv2,pv5,pv61,pv461], .c 173, .c 3, .p pv2 [pv2,pv29,pv9697], .c 7, .c 3, .c 31,
]
private theorem h0068c20 : checkBlock 562179 128 b0068c20 = true := by
  decide +kernel

private def b0068c21 : List Row := [
  .c 5, .c 3, .p pv11 [pv2,pv19,pv41], .c 11, .c 3, .c 5, .c 59, .c 3, .c 743, .c 337, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv13,pv7211], .c 3, .c 11, .c 5, .c 3, .c 101, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv19,pv2467], .c 3, .c 61, .c 43, .c 3, .c 347, .c 53, .c 3,
  .p pv2 [pv2,pv7,pv20089], .c 5, .c 3, .c 7, .p pv17 [pv2,pv3,pv5], .c 3, .c 5, .c 11, .c 3,
  .c 23, .c 7, .c 3, .p pv2 [pv2,pv140629], .p pv17 [pv2,pv3,pv11,pv947], .c 3, .c 13, .c 5, .c 3,
  .c 11, .c 157, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv601], .c 3, .c 7, .c 47, .c 3, .c 17, .c 13,
  .c 3, .c 359, .c 5, .c 3, .c 79, .c 41, .c 3, .c 5, .c 457, .c 3, .c 19, .c 11, .c 3,
  .p pv3 [pv2,pv7,pv5023], .p pv3 [pv2,pv3,pv93763], .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv31,pv349], .p pv7 [pv2,pv3,pv5,pv7,pv19,pv47], .c 3, .c 5, .c 7, .c 3, .c 13,
  .c 23, .c 3, .p pv5 [pv2,pv11,pv107,pv239], .c 19, .c 3, .p pv2 [pv2,pv43,pv3271], .c 5, .c 3,
  .c 31, .p pv7 [pv2,pv3,pv5,pv9377], .c 3, .c 5, .c 13, .c 3, .p pv11 [pv2,pv5,pv56263],
  .p pv5 [pv2,pv3,pv7,pv17,pv197], .c 3, .c 47, .c 7, .c 3, .c 41, .c 5, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv5,pv11,pv31], .c 3, .c 5, .c 83, .c 3, .c 11, .p pv3 [pv2,pv3,pv31259], .c 3,
  .c 7, .p pv11 [pv2,pv3,pv46889], .c 3, .p pv3 [pv2,pv11,pv23,pv139], .c 5, .c 3, .c 13, .c 7,
  .c 3, .c 5, .c 29, .c 3,
]
private theorem h0068c21 : checkBlock 562435 128 b0068c21 = true := by
  decide +kernel

private def b0068c22 : List Row := [
  .p pv2 [pv2,pv5,pv56269], .p pv2 [pv2,pv3,pv13,pv3607], .c 3, .c 97,
  .p pv3 [pv2,pv3,pv43,pv727], .c 3, .p pv5 [pv2,pv7,pv40193], .c 5, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv5,pv18757], .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv3517], .c 7, .c 3,
  .c 11, .c 181, .c 3, .c 37, .c 5, .c 3, .p pv2 [pv2,pv11,pv25579], .c 23, .c 3, .c 5, .c 89,
  .c 3, .c 7, .p pv5 [pv2,pv3,pv977], .c 3, .c 13, .p pv19 [pv2,pv3,pv7,pv13399], .c 3,
  .p pv2 [pv2,pv281381], .c 5, .c 3, .c 173, .c 11, .c 3, .c 5, .c 151, .c 3,
  .p pv2 [pv2,pv5,pv19,pv1481], .c 13, .c 3, .c 23, .p pv2 [pv2,pv3,pv193], .c 3, .c 7, .c 5,
  .c 3, .c 19, .c 59, .c 3, .c 5, .c 7, .c 3, .c 139, .p pv2 [pv2,pv3,pv46901], .c 3, .c 71,
  .c 17, .c 3, .c 83, .c 5, .c 3, .c 197, .p pv11 [pv2,pv3,pv5,pv73,pv257], .c 3, .c 5, .c 11,
  .c 3, .p pv3 [pv2,pv5,pv14071], .c 281, .c 3, .c 61, .c 7, .c 3, .c 17, .c 5, .c 3, .c 11,
  .c 13, .c 3, .c 5, .c 31, .c 3, .p pv31 [pv2,pv5,pv7,pv11,pv17,pv43], .c 101, .c 3, .c 7, .c 23,
  .c 3, .c 389, .c 5, .c 3, .c 41, .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv1303], .c 3,
  .p pv3 [pv2,pv5,pv13,pv433], .c 11, .c 3, .c 131, .p pv11 [pv2,pv3,pv61,pv769], .c 3, .c 13,
  .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 107, .c 3, .p pv2 [pv2,pv5,pv41,pv1373], .c 7, .c 3,
  .c 349, .c 13, .c 3, .p pv5 [pv2,pv173,pv1627], .c 5,
]
private theorem h0068c22 : checkBlock 562691 128 b0068c22 = true := by
  decide +kernel

private def b0068c23 : List Row := [
  .c 3, .p pv2 [pv2,pv23,pv29,pv211], .c 19, .c 3, .c 5, .c 167, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv93827], .c 3, .p pv5 [pv2,pv47,pv53,pv113], .c 11, .c 3,
  .p pv2 [pv2,pv17,pv487], .c 5, .c 3, .p pv2 [pv2,pv13,pv59,pv367], .c 193, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv31277], .c 3, .c 11, .c 251, .c 3, .p pv2 [pv2,pv7,pv20107], .c 43, .c 3,
  .c 7, .c 5, .c 3, .p pv3 [pv2,pv19,pv463], .p pv2 [pv2,pv3,pv5,pv7,pv383], .c 3, .c 5, .c 7,
  .c 3, .p pv2 [pv2,pv5,pv28151], .c 17, .c 3, .c 19, .c 37, .c 3, .c 79, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv131,pv307], .p pv13 [pv2,pv3,pv5,pv17,pv23], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv19,pv449], .c 3, .p pv13 [pv2,pv5,pv11261], .c 31, .c 3, .c 11, .c 7,
  .c 3, .c 23, .c 5, .c 3, .c 13, .c 149, .c 3, .c 5, .p pv2 [pv2,pv3,pv15641], .c 3,
  .p pv17 [pv2,pv5,pv7,pv2011], .c 263, .c 3, .c 7, .c 139, .c 3, .c 29, .c 5, .c 3,
  .p pv2 [pv2,pv281549], .c 7, .c 3, .c 5, .c 47, .c 3, .c 229, .p pv43 [pv2,pv3,pv11,pv79], .c 3,
  .p pv2 [pv2,pv140779], .p pv3 [pv2,pv3,pv127,pv739], .c 3, .c 11, .c 5, .c 3, .c 7,
  .p pv19 [pv2,pv3,pv5,pv6257], .c 3, .c 5, .c 601, .c 3, .c 19, .c 7, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv15643], .c 3, .p pv3 [pv2,pv61,pv577], .c 5, .c 3, .c 17, .c 233, .c 3, .c 5,
  .c 11, .c 3, .c 7, .c 13, .c 3, .c 31, .c 19, .c 3, .p pv5 [pv2,pv97,pv2903], .c 5, .c 3, .c 11,
  .c 79, .c 3, .c 5, .p pv5 [pv2,pv3,pv46933], .c 3, .c 23,
]
private theorem h0068c23 : checkBlock 562947 128 b0068c23 = true := by
  decide +kernel

private def b0068c24 : List Row := [
  .c 109, .c 3, .c 137, .c 29, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv281609], .c 311, .c 3, .c 5,
  .c 7, .c 3, .c 53, .c 11, .c 3, .c 439, .c 31, .c 3, .c 71, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv47,pv107], .c 13, .c 3, .c 5, .c 43, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv7,pv13411], .c 3, .c 29, .c 7, .c 3, .c 59, .c 5, .c 3, .c 97, .c 89, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv269,pv349], .c 3, .c 167, .c 19, .c 3, .c 7, .c 11, .c 3, .c 13, .c 5,
  .c 3, .c 317, .c 7, .c 3, .c 5, .c 431, .c 3, .c 11, .c 239, .c 3, .p pv5 [pv2,pv281663], .c 13,
  .c 3, .c 433, .c 5, .c 3, .c 7, .c 73, .c 3, .c 5, .c 613, .c 3, .p pv17 [pv2,pv5,pv19,pv593],
  .c 7, .c 3, .p pv2 [pv2,pv140839], .p pv3 [pv2,pv3,pv93893], .c 3, .c 17, .c 5, .c 3, .c 19,
  .c 499, .c 3, .c 5, .p pv23 [pv2,pv3,pv11,pv97], .c 3, .c 7, .c 29, .c 3, .c 11, .c 47, .c 3,
  .c 383, .c 5, .c 3, .c 37, .p pv7 [pv2,pv3,pv5,pv313], .c 3, .c 5, .c 13, .c 3,
  .p pv7 [pv2,pv5,pv103,pv547], .p pv5 [pv2,pv3,pv29,pv1619], .c 3, .p pv3 [pv2,pv7,pv10061],
  .p pv2 [pv2,pv3,pv113,pv277], .c 3, .c 7, .c 5, .c 3, .c 43, .c 11, .c 3, .c 5, .c 7, .c 3,
  .c 29, .c 53, .c 3, .p pv5 [pv2,pv13,pv1667], .p pv7 [pv2,pv3,pv17,pv1381], .c 3, .c 11, .c 5,
  .c 3,
]
private theorem h0068c24 : checkBlock 563203 128 b0068c24 = true := by
  decide +kernel

private def b0068c25 : List Row := [
  .c 13, .c 173, .c 3, .c 5, .p pv2 [pv2,pv3,pv93911], .c 3, .c 463, .c 37, .c 3, .c 23, .c 7,
  .c 3, .c 19, .c 5, .c 3, .p pv3 [pv2,pv17609], .c 163, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv7,pv23], .p pv3 [pv2,pv3,pv19,pv4943], .c 3, .c 7, .c 59, .c 3, .c 103, .c 5,
  .c 3, .c 11, .c 7, .c 3, .c 5, .c 71, .c 3, .c 113, .c 17, .c 3, .c 13, .c 653, .c 3,
  .p pv5 [pv2,pv7,pv40253], .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv13,pv17], .c 3, .c 5, .c 29,
  .c 3, .p pv3 [pv2,pv5,pv73,pv193], .c 7, .c 3, .c 17, .c 23, .c 3, .c 379, .c 5, .c 3, .c 61,
  .c 211, .c 3, .c 5, .p pv2 [pv2,pv3,pv29,pv41,pv79], .c 3, .c 7, .p pv5 [pv2,pv3,pv23,pv1021],
  .c 3, .c 19, .p pv3 [pv2,pv3,pv7,pv71], .c 3, .c 373, .c 5, .c 3, .c 263, .c 31, .c 3, .c 5,
  .c 197, .c 3, .c 37, .p pv3 [pv2,pv3,pv93937], .c 3, .c 41, .c 11, .c 3, .c 7, .c 5, .c 3,
  .c 109, .c 13, .c 3, .c 5, .c 7, .c 3, .c 11, .c 83, .c 3, .p pv3 [pv2,pv70457], .c 599, .c 3,
  .p pv5 [pv2,pv11,pv25621], .c 5, .c 3, .c 17, .c 47, .c 3, .c 5, .c 733, .c 3, .c 101, .c 151,
  .c 3, .c 43, .c 7, .c 3, .c 13, .c 5, .c 3, .c 241, .c 61, .c 3, .c 5, .c 23, .c 3, .c 19,
  .c 313,
]
private theorem h0068c25 : checkBlock 563459 128 b0068c25 = true := by
  decide +kernel

private def b0068c26 : List Row := [
  .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv521,pv541], .c 5, .c 3, .c 577, .c 7, .c 3, .c 5, .c 17,
  .c 3, .c 353, .p pv3 [pv2,pv3,pv31319], .c 3, .p pv2 [pv2,pv251,pv1123], .c 19, .c 3, .c 23,
  .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 199, .c 3, .c 13, .c 7, .c 3, .p pv3 [pv2,pv23,pv383],
  .c 73, .c 3, .c 11, .c 5, .c 3, .c 29, .c 41, .c 3, .c 5, .c 13, .c 3, .c 7, .c 461, .c 3,
  .c 173, .p pv23 [pv2,pv3,pv7,pv839], .c 3, .p pv2 [pv2,pv47,pv2999], .c 5, .c 3, .c 83,
  .p pv7 [pv2,pv3,pv5,pv9397], .c 3, .c 5, .c 11, .c 3, .p pv7 [pv2,pv5,pv56383], .c 661, .c 3,
  .p pv2 [pv2,pv7,pv13,pv1549], .c 17, .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv7,pv179], .c 3, .c 5, .c 7, .c 3, .c 97, .c 19, .c 3, .c 53,
  .p pv7 [pv2,pv3,pv23,pv227], .c 3, .c 17, .c 5, .c 3, .c 569, .p pv43 [pv2,pv3,pv5,pv37,pv127],
  .c 3, .c 5, .p pv5 [pv2,pv3,pv31327], .c 3, .c 23, .c 11, .c 3, .p pv3 [pv2,pv70487], .c 7,
  .c 3, .c 607, .c 5, .c 3, .c 619, .c 643, .c 3, .c 5, .c 37, .c 3, .c 31, .c 139, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv23497], .c 3, .p pv2 [pv2,pv140983], .c 5, .c 3, .c 19, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv193,pv487], .c 3, .c 271, .c 13, .c 3, .c 547, .c 11, .c 3, .c 29, .c 5, .c 3,
  .c 7,
]
private theorem h0068c26 : checkBlock 563715 128 b0068c26 = true := by
  decide +kernel

private def b0068c27 : List Row := [
  .p pv2 [pv2,pv3,pv5,pv11,pv1709], .c 3, .c 5, .c 19, .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv281993], .c 359, .c 3, .c 89, .c 5, .c 3, .p pv7 [pv2,pv73,pv3863], .c 751, .c 3,
  .c 5, .c 127, .c 3, .c 7, .p pv2 [pv2,pv3,pv15667], .c 3, .p pv3 [pv2,pv35251], .c 283, .c 3,
  .c 191, .c 5, .c 3, .c 23, .c 13, .c 3, .c 5, .c 41, .c 3, .p pv3 [pv2,pv5,pv59,pv239], .c 17,
  .c 3, .c 11, .p pv11 [pv2,pv3,pv3917], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv11,pv25639],
  .p pv2 [pv2,pv3,pv5,pv7,pv17,pv79], .c 3, .c 5, .c 7, .c 3, .c 73, .c 67, .c 3, .c 17, .c 29,
  .c 3, .c 13, .c 5, .c 3, .p pv13 [pv2,pv7,pv1439], .c 11, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv13,pv113], .c 3, .c 157, .p pv5 [pv2,pv3,pv7,pv11,pv37], .c 3, .c 31, .c 7,
  .c 3, .c 11, .c 5, .c 3, .c 41, .c 23, .c 3, .c 5, .p pv3 [pv2,pv3,pv167,pv563], .c 3, .c 103,
  .p pv2 [pv2,pv3,pv53,pv887], .c 3, .c 7, .c 37, .c 3, .c 163, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv19,pv571], .c 7, .c 3, .c 5, .c 11, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv17,pv5531], .c 3, .c 19, .c 31, .c 3, .p pv2 [pv2,pv7,pv20149], .c 5, .c 3,
  .c 7, .c 241, .c 3, .c 5, .c 13, .c 3, .p pv11 [pv2,pv5,pv11,pv23,pv223], .c 7, .c 3,
  .p pv2 [pv2,pv17,pv8297], .c 433, .c 3, .c 43, .c 5, .c 3, .c 113, .c 107, .c 3, .c 5, .c 59,
  .c 3, .c 7, .c 11, .c 3,
]
private theorem h0068c27 : checkBlock 563971 128 b0068c27 = true := by
  decide +kernel

private def b0068c28 : List Row := [
  .p pv2 [pv2,pv13,pv21701], .p pv2 [pv2,pv3,pv7,pv2239], .c 3, .p pv3 [pv2,pv70529], .c 5, .c 3,
  .c 13, .c 557, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv37,pv61], .c 29, .c 3,
  .p pv3 [pv2,pv7,pv11,pv229], .c 23, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv141067],
  .p pv7 [pv2,pv3,pv5,pv7,pv2687], .c 3, .c 5, .c 7, .c 3, .c 17, .c 41, .c 3, .c 37, .c 11, .c 3,
  .c 31, .c 5, .c 3, .p pv7 [pv2,pv7,pv17,pv2371], .p pv2 [pv2,pv3,pv5,pv11,pv19], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv163,pv577], .c 3, .c 11, .p pv11 [pv2,pv3,pv7,pv3359], .c 3, .c 13, .c 7,
  .c 3, .p pv2 [pv2,pv11,pv113,pv227], .c 5, .c 3, .c 47, .c 379, .c 3, .c 5, .c 103, .c 3, .c 67,
  .c 13, .c 3, .c 7, .c 17, .c 3, .p pv3 [pv2,pv4409], .c 5, .c 3, .p pv11 [pv2,pv181,pv1559],
  .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv17,pv503], .c 3, .p pv2 [pv2,pv5,pv56437],
  .p pv5 [pv2,pv3,pv61,pv257], .c 3, .c 11, .c 71, .c 3, .c 17, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv6271], .c 3, .c 5, .c 23, .c 3, .p pv7 [pv2,pv5,pv17,pv83], .c 7, .c 3,
  .p pv5 [pv2,pv41,pv6883], .p pv7 [pv2,pv3,pv13,pv67], .c 3, .c 223, .c 5, .c 3,
  .p pv2 [pv2,pv43,pv6563], .c 11, .c 3, .c 5, .c 29, .c 3, .c 7, .c 19, .c 3,
  .p pv2 [pv2,pv73,pv1933], .c 389, .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv31,pv569], .c 17, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv29,pv811], .c 3, .c 43, .p pv5 [pv2,pv3,pv10453], .c 3,
  .p pv2 [pv2,pv7,pv23,pv1753], .c 163, .c 3, .c 7, .c 5, .c 3, .c 31, .c 509,
]
private theorem h0068c28 : checkBlock 564227 128 b0068c28 = true := by
  decide +kernel

private def b0068c29 : List Row := [
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv19,pv2971], .c 271, .c 3, .p pv3 [pv2,pv35281], .c 13,
  .c 3, .c 53, .c 5, .c 3, .c 11, .c 109, .c 3, .c 5, .c 47, .c 3, .c 71,
  .p pv2 [pv2,pv3,pv7,pv13441], .c 3, .c 89, .c 7, .c 3, .p pv2 [pv2,pv107,pv1319], .c 5, .c 3,
  .c 181, .c 31, .c 3, .c 5, .c 19, .c 3, .c 13, .c 11, .c 3, .c 7, .c 233, .c 3, .c 199, .c 5,
  .c 3, .c 347, .c 7, .c 3, .c 5, .c 13, .c 3, .c 23, .c 37, .c 3, .c 17, .c 151, .c 3,
  .p pv3 [pv2,pv7,pv71], .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv4481], .c 3,
  .c 41, .c 7, .c 3, .p pv3 [pv2,pv13,pv61,pv89], .c 11, .c 3, .c 19, .c 5, .c 3, .c 13, .c 269,
  .c 3, .c 5, .c 97, .c 3, .c 7, .p pv5 [pv2,pv3,pv13,pv19,pv127], .c 3, .c 673, .c 83, .c 3,
  .p pv2 [pv2,pv11,pv41,pv313], .c 5, .c 3, .c 29, .c 19, .c 3, .c 5, .p pv3 [pv2,pv3,pv94111],
  .c 3, .p pv7 [pv2,pv5,pv56467], .c 23, .c 3, .c 61, .p pv3 [pv2,pv3,pv10457], .c 3, .c 7, .c 5,
  .c 3, .c 17, .c 101, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv5647], .p pv3 [pv2,pv3,pv94117],
  .c 3, .c 11, .p pv7 [pv2,pv3,pv47059], .c 3, .p pv3 [pv2,pv70589], .c 5, .c 3, .c 23, .c 641,
  .c 3, .c 5, .c 31, .c 3, .c 37, .c 13, .c 3, .c 19,
]
private theorem h0068c29 : checkBlock 564483 128 b0068c29 = true := by
  decide +kernel

private def b0068c30 : List Row := [
  .c 7, .c 3, .c 67, .c 5, .c 3, .c 103, .c 11, .c 3, .c 5, .c 17, .c 3,
  .p pv3 [pv2,pv5,pv7,pv2017], .c 659, .c 3, .c 7, .c 127, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv282389], .c 7, .c 3, .c 5, .c 191, .c 3, .c 17, .p pv5 [pv2,pv3,pv101,pv233],
  .c 3, .p pv2 [pv2,pv141199], .c 47, .c 3, .c 277, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 11,
  .c 3, .c 53, .c 7, .c 3, .p pv2 [pv2,pv282413], .c 409, .c 3, .c 29, .c 5, .c 3, .c 11, .c 683,
  .c 3, .c 5, .c 211, .c 3, .c 7, .c 107, .c 3, .c 23, .c 17, .c 3, .c 13, .c 5, .c 3, .c 503,
  .p pv13 [pv2,pv3,pv5,pv19,pv991], .c 3, .c 5, .c 67, .c 3, .p pv3 [pv2,pv5,pv23,pv307], .c 11,
  .c 3, .c 113, .c 13, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv41,pv83], .c 181, .c 3, .c 5, .c 7,
  .c 3, .c 193, .c 31, .c 3, .p pv2 [pv2,pv11,pv37,pv347], .p pv3 [pv2,pv3,pv94153], .c 3,
  .p pv2 [pv2,pv282461], .c 5, .c 3, .c 79, .c 397, .c 3, .c 5, .p pv5 [pv2,pv3,pv23539], .c 3,
  .c 13, .c 229, .c 3, .c 71, .c 7, .c 3, .c 37, .c 5, .c 3, .p pv13 [pv2,pv163,pv1733], .c 17,
  .c 3, .c 5, .c 13, .c 3, .c 11, .p pv5 [pv2,pv3,pv23,pv89], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv17,pv29,pv191], .c 3, .p pv5 [pv2,pv11,pv61,pv421], .c 5, .c 3,
  .p pv2 [pv2,pv137,pv1031], .c 7, .c 3,
]
private theorem h0068c30 : checkBlock 564739 128 b0068c30 = true := by
  decide +kernel

private def b0068c31 : List Row := [
  .c 5, .p pv5 [pv2,pv3,pv197,pv239], .c 3, .c 251, .c 19, .c 3, .c 29, .c 401, .c 3,
  .p pv2 [pv2,pv7,pv17,pv1187], .c 5, .c 3, .c 7, .c 41, .c 3, .c 5, .c 37, .c 3, .c 349, .c 7,
  .c 3, .c 11, .p pv17 [pv2,pv3,pv31391], .c 3, .c 59, .c 5, .c 3, .p pv3 [pv2,pv11,pv6421],
  .c 547, .c 3, .c 5, .p pv7 [pv2,pv3,pv109], .c 3, .c 7, .c 17, .c 3, .c 107,
  .p pv2 [pv2,pv3,pv7,pv31], .c 3, .c 709, .c 5, .c 3, .c 19, .c 11, .c 3, .c 5, .c 23, .c 3,
  .c 281, .c 73, .c 3, .c 13, .c 31, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv141277],
  .p pv17 [pv2,pv3,pv5,pv7,pv13,pv23], .c 3, .c 5, .c 7, .c 3, .c 163, .c 13, .c 3,
  .p pv5 [pv2,pv282563], .c 593, .c 3, .c 23, .c 5, .c 3, .c 53, .c 491, .c 3, .c 5, .c 11, .c 3,
  .c 283, .c 353, .c 3, .c 149, .c 7, .c 3, .p pv2 [pv2,pv13,pv21737], .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv18839], .c 3, .c 5, .p pv5 [pv2,pv3,pv23549], .c 3, .c 29,
  .p pv3 [pv2,pv3,pv17,pv1847], .c 3, .c 7, .p pv2 [pv2,pv3,pv13,pv3623], .c 3, .c 19, .c 5, .c 3,
  .c 17, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv94201], .c 3, .c 317, .c 11, .c 3, .c 389, .c 97,
  .c 3, .c 31, .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv2243], .c 3,
  .p pv19 [pv2,pv5,pv13,pv1087], .c 7, .c 3, .p pv5 [pv2,pv11,pv25693], .c 37,
]
private theorem h0068c31 : checkBlock 564995 128 b0068c31 = true := by
  decide +kernel

def rows0068 : List Row :=
  b0068c00 ++ b0068c01 ++ b0068c02 ++ b0068c03 ++ b0068c04 ++ b0068c05 ++ b0068c06 ++ b0068c07 ++
  b0068c08 ++ b0068c09 ++ b0068c10 ++ b0068c11 ++ b0068c12 ++ b0068c13 ++ b0068c14 ++ b0068c15 ++
  b0068c16 ++ b0068c17 ++ b0068c18 ++ b0068c19 ++ b0068c20 ++ b0068c21 ++ b0068c22 ++ b0068c23 ++
  b0068c24 ++ b0068c25 ++ b0068c26 ++ b0068c27 ++ b0068c28 ++ b0068c29 ++ b0068c30 ++ b0068c31

theorem checked0068 : checkBlock 557059 4096 rows0068 = true :=
  checkBlock_append h0068c00 (
    checkBlock_append h0068c01 (
    checkBlock_append h0068c02 (
    checkBlock_append h0068c03 (
    checkBlock_append h0068c04 (
    checkBlock_append h0068c05 (
    checkBlock_append h0068c06 (
    checkBlock_append h0068c07 (
    checkBlock_append h0068c08 (
    checkBlock_append h0068c09 (
    checkBlock_append h0068c10 (
    checkBlock_append h0068c11 (
    checkBlock_append h0068c12 (
    checkBlock_append h0068c13 (
    checkBlock_append h0068c14 (
    checkBlock_append h0068c15 (
    checkBlock_append h0068c16 (
    checkBlock_append h0068c17 (
    checkBlock_append h0068c18 (
    checkBlock_append h0068c19 (
    checkBlock_append h0068c20 (
    checkBlock_append h0068c21 (
    checkBlock_append h0068c22 (
    checkBlock_append h0068c23 (
    checkBlock_append h0068c24 (
    checkBlock_append h0068c25 (
    checkBlock_append h0068c26 (
    checkBlock_append h0068c27 (
    checkBlock_append h0068c28 (
    checkBlock_append h0068c29 (
    checkBlock_append h0068c30 (
    h0068c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
