/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks00/Block0070
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks00/Block0070.checked0070
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table011
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table013
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table017
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table023
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table036
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table083

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes
private noncomputable def b0070c00 : List Row := [
  .c 13, .c 5, .c 3, .c 109, .p pv3 [pv2,pv3,pv5,pv3823], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv919], .c 3, .c 7, .c 11, .c 3, .c 41, .c 13, .c 3, .p pv3 [pv2,pv17921],
  .c 5, .c 3, .p pv7 [pv2,pv17,pv101,pv167], .p pv7 [pv2,pv3,pv5,pv59], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv95581], .c 3, .c 43, .p pv2 [pv2,pv3,pv47791], .c 3,
  .p pv3 [pv2,pv7,pv11,pv19], .c 587, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv13,pv41,pv269],
  .p pv3 [pv2,pv3,pv5,pv7,pv2731], .c 3, .c 5, .c 7, .c 3, .c 13, .p pv2 [pv2,pv3,pv61,pv1567],
  .c 3, .p pv5 [pv2,pv286763], .c 11, .c 3, .c 29, .c 5, .c 3, .c 59, .c 47, .c 3, .c 5, .c 13,
  .c 3, .c 11, .c 19, .c 3, .p pv2 [pv2,pv223,pv643], .c 7, .c 3, .c 17, .c 5, .c 3,
  .p pv3 [pv2,pv4481],
]
private theorem h0070c00 : checkBlock 573443 64 b0070c00 = true := by decide +kernel
private noncomputable def b0070c01 : List Row := [
  .p pv3 [pv2,pv3,pv5,pv6373], .c 3, .c 5, .c 43, .c 3, .c 709, .c 61, .c 3, .c 7, .c 181, .c 3,
  .c 31, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 103, .c 3, .c 37, .c 83, .c 3, .c 11, .c 53,
  .c 3, .c 331, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv6829], .c 3, .c 283,
  .c 7, .c 3, .p pv5 [pv2,pv233,pv1231], .c 29, .c 3, .c 139, .c 5, .c 3, .c 127, .c 11, .c 3,
  .c 5, .c 19, .c 3, .c 7, .p pv5 [pv2,pv3,pv11,pv41,pv53], .c 3, .c 13,
  .p pv3 [pv2,pv3,pv7,pv29,pv157], .c 3, .c 11, .c 5, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv5,pv13,pv1471], .c 3, .c 5, .c 563,
]
private theorem h0070c01 : checkBlock 573571 64 b0070c01 = true := by decide +kernel
private noncomputable def b0070c02 : List Row := [
  .c 3, .c 113, .c 13, .c 3, .c 29, .c 211, .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv286859],
  .c 67, .c 3, .c 5, .c 7, .c 3, .c 523, .c 17, .c 3, .p pv3 [pv2,pv29,pv2473],
  .p pv3 [pv2,pv3,pv11,pv8693], .c 3, .c 19, .c 5, .c 3, .c 11, .c 71, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv137,pv349], .c 3, .p pv3 [pv2,pv5,pv11,pv163],
  .p pv5 [pv2,pv3,pv7,pv19,pv719], .c 3, .c 17, .c 7, .c 3, .c 439, .c 5, .c 3, .c 31, .c 13,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv127,pv251], .c 3, .p pv7 [pv2,pv5,pv7,pv1171], .c 11, .c 3, .c 7,
  .c 149, .c 3, .c 547, .c 5, .c 3, .p pv3 [pv2,pv35863], .c 7, .c 3, .c 5,
  .p pv41 [pv2,pv3,pv23909], .c 3, .c 241, .c 29, .c 3,
]
private theorem h0070c02 : checkBlock 573699 64 b0070c02 = true := by decide +kernel
private noncomputable def b0070c03 : List Row := [
  .c 23, .p pv2 [pv2,pv3,pv47819], .c 3, .c 13, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv13,pv1051], .c 3, .p pv2 [pv2,pv5,pv23,pv499], .c 7, .c 3, .c 19, .c 11,
  .c 3, .p pv5 [pv2,pv83,pv3457], .c 5, .c 3, .c 17, .p pv7 [pv2,pv3,pv5,pv11,pv37,pv47], .c 3,
  .c 5, .c 41, .c 3, .c 7, .p pv2 [pv2,pv3,pv101,pv947], .c 3, .p pv5 [pv2,pv17,pv16879], .c 647,
  .c 3, .c 59, .c 5, .c 3, .p pv2 [pv2,pv13,pv22073], .p pv2 [pv2,pv3,pv5,pv1913], .c 3, .c 5,
  .c 37, .c 3, .c 13, .c 127, .c 3, .c 47, .c 23, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv71741],
  .c 139, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv28697], .c 467, .c 3, .c 11, .c 61, .c 3,
  .p pv3 [pv2,pv19,pv59],
]
private theorem h0070c03 : checkBlock 573827 64 b0070c03 = true := by decide +kernel
private noncomputable def b0070c04 : List Row := [
  .c 5, .c 3, .c 41, .c 89, .c 3, .c 5, .p pv7 [pv2,pv3,pv1181], .c 3, .c 17,
  .p pv19 [pv2,pv3,pv7,pv6833], .c 3, .p pv3 [pv2,pv13,pv5519], .c 7, .c 3, .c 101, .c 5, .c 3,
  .c 13, .c 11, .c 3, .c 5, .c 29, .c 3, .c 541, .p pv2 [pv2,pv3,pv11,pv13,pv223], .c 3, .c 7,
  .c 19, .c 3, .c 11, .c 5, .c 3, .c 103, .c 7, .c 3, .c 5, .c 31, .c 3,
  .p pv31 [pv2,pv5,pv137,pv419], .p pv5 [pv2,pv3,pv11959], .c 3, .c 251, .c 17, .c 3, .c 53,
  .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv43,pv89], .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv28703], .c 7, .c 3, .c 13, .c 673, .c 3, .c 17, .c 5, .c 3, .c 11,
  .p pv19 [pv2,pv3,pv5,pv13,pv23],
]
private theorem h0070c04 : checkBlock 573955 64 b0070c04 = true := by decide +kernel
private noncomputable def b0070c05 : List Row := [
  .c 3, .c 5, .c 317, .c 3, .c 7, .c 13, .c 3, .c 149, .p pv3 [pv2,pv3,pv7,pv13669], .c 3, .c 23,
  .c 5, .c 3, .p pv2 [pv2,pv143527], .c 83, .c 3, .c 5, .c 383, .c 3, .c 569, .c 11, .c 3,
  .p pv5 [pv2,pv7,pv23,pv1783], .c 37, .c 3, .c 7, .c 5, .c 3, .c 89, .c 17, .c 3, .c 5, .c 7,
  .c 3, .c 31, .c 113, .c 3, .p pv2 [pv2,pv11,pv13049], .p pv3 [pv2,pv3,pv13,pv17,pv433], .c 3,
  .p pv2 [pv2,pv107,pv2683], .c 5, .c 3, .p pv3 [pv2,pv7,pv10253], .c 13, .c 3, .c 5, .c 71,
  .c 3, .p pv2 [pv2,pv5,pv19,pv1511], .p pv3 [pv2,pv3,pv7,pv31], .c 3, .c 173, .c 7, .c 3, .c 61,
  .c 5, .c 3, .c 19, .p pv19 [pv2,pv3,pv5,pv11,pv29], .c 3, .c 5, .c 283, .c 3,
]
private theorem h0070c05 : checkBlock 574083 64 b0070c05 = true := by decide +kernel
private noncomputable def b0070c06 : List Row := [
  .c 11, .c 31, .c 3, .c 7, .p pv7 [pv2,pv3,pv19,pv23,pv73], .c 3, .c 13, .c 5, .c 3, .c 29,
  .c 7, .c 3, .c 5, .c 19, .c 3, .c 23, .c 17, .c 3, .c 59, .c 13, .c 3, .c 151, .c 5, .c 3,
  .c 7, .p pv11 [pv2,pv3,pv5,pv17,pv563], .c 3, .c 5, .c 557, .c 3, .c 449, .c 7, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv95713], .c 3, .p pv2 [pv2,pv287141], .c 5, .c 3,
  .p pv17 [pv2,pv11,pv13,pv251], .c 73, .c 3, .c 5, .p pv5 [pv2,pv3,pv23929], .c 3, .c 7, .c 241,
  .c 3, .p pv2 [pv2,pv31,pv59,pv157], .p pv2 [pv2,pv3,pv7,pv43,pv53], .c 3, .c 19, .c 5, .c 3,
  .c 71, .c 11, .c 3, .c 5, .c 13, .c 3, .c 353, .c 23, .c 3, .c 31,
]
private theorem h0070c06 : checkBlock 574211 64 b0070c06 = true := by decide +kernel
private noncomputable def b0070c07 : List Row := [
  .c 743, .c 3, .c 7, .c 5, .c 3, .c 499, .c 19, .c 3, .c 5, .c 7, .c 3, .c 53,
  .p pv3 [pv2,pv3,pv17,pv1877], .c 3, .p pv5 [pv2,pv13,pv22091], .c 41, .c 3,
  .p pv2 [pv2,pv143593], .c 5, .c 3, .c 13, .c 613, .c 3, .c 5, .c 11, .c 3, .c 67,
  .p pv5 [pv2,pv3,pv7,pv13,pv263], .c 3, .c 307, .c 7, .c 3, .c 29, .c 5, .c 3, .c 11, .c 179,
  .c 3, .c 5, .c 311, .c 3, .c 127, .p pv5 [pv2,pv3,pv95737], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv47869], .c 3, .p pv3 [pv2,pv29,pv619], .c 5, .c 3, .p pv13 [pv2,pv287219],
  .c 7, .c 3, .c 5, .c 17, .c 3, .c 41, .c 11, .c 3, .c 13, .c 397, .c 3, .c 157, .c 5,
]
private theorem h0070c07 : checkBlock 574339 64 b0070c07 = true := by decide +kernel
private noncomputable def b0070c08 : List Row := [
  .c 3, .c 7, .c 23, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv977], .c 3, .c 17, .c 7, .c 3, .c 139,
  .p pv7 [pv2,pv3,pv79,pv101], .c 3, .p pv2 [pv2,pv31,pv41,pv113], .c 5, .c 3, .c 37,
  .p pv13 [pv2,pv3,pv5,pv383], .c 3, .c 5, .p pv2 [pv2,pv3,pv10639], .c 3, .c 7, .c 199, .c 3,
  .c 23, .c 11, .c 3, .c 31, .c 5, .c 3, .p pv3 [pv2,pv47,pv191], .c 97, .c 3, .c 5, .c 227,
  .c 3, .c 11, .p pv5 [pv2,pv3,pv59,pv541], .c 3, .p pv2 [pv2,pv7,pv41039], .c 17, .c 3, .c 7,
  .c 5, .c 3, .c 61, .c 13, .c 3, .c 5, .c 7, .c 3, .c 443, .c 37, .c 3, .c 29, .c 19, .c 3,
  .c 17, .c 5, .c 3, .c 101, .c 433, .c 3,
]
private theorem h0070c08 : checkBlock 574467 64 b0070c08 = true := by decide +kernel
private noncomputable def b0070c09 : List Row := [
  .c 5, .p pv2 [pv2,pv3,pv11,pv1451], .c 3, .c 59, .c 71, .c 3, .c 11, .c 7, .c 3, .c 13, .c 5,
  .c 3, .p pv11 [pv2,pv11,pv26119], .p pv7 [pv2,pv3,pv5,pv61,pv157], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv13,pv53,pv139], .c 3, .p pv7 [pv2,pv5,pv7,pv8209], .c 401, .c 3, .c 7, .c 13,
  .c 3, .p pv2 [pv2,pv287321], .c 5, .c 3, .c 197, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv41,pv73],
  .c 3, .c 509, .c 521, .c 3, .p pv2 [pv2,pv287333], .c 47, .c 3, .c 11, .c 5, .c 3, .c 7, .c 61,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv4561], .c 3, .c 13, .c 7, .c 3, .c 41,
  .p pv2 [pv2,pv3,pv95783], .c 3, .p pv5 [pv2,pv17,pv16903], .c 5, .c 3, .c 31,
  .p pv31 [pv2,pv3,pv5,pv19157], .c 3, .c 5, .c 11, .c 3, .c 7,
]
private theorem h0070c09 : checkBlock 574595 64 b0070c09 = true := by decide +kernel
private noncomputable def b0070c10 : List Row := [
  .p pv2 [pv2,pv3,pv29,pv367], .c 3, .p pv5 [pv2,pv67,pv4289], .c 73, .c 3,
  .p pv2 [pv2,pv53,pv2711], .c 5, .c 3, .c 11, .p pv17 [pv2,pv3,pv5,pv31,pv103], .c 3, .c 5,
  .c 23, .c 3, .c 29, .c 17, .c 3, .c 109, .c 359, .c 3, .c 7, .c 5, .c 3, .c 13, .c 31, .c 3,
  .c 5, .c 7, .c 3, .c 43, .c 11, .c 3, .c 17, .p pv2 [pv2,pv3,pv19,pv2521], .c 3, .c 23, .c 5,
  .c 3, .p pv7 [pv2,pv7,pv41057], .p pv7 [pv2,pv3,pv5,pv479], .c 3, .c 5, .c 19, .c 3, .c 233,
  .p pv5 [pv2,pv3,pv7,pv2281], .c 3, .p pv3 [pv2,pv11,pv23,pv71], .c 7, .c 3, .c 563, .c 5, .c 3,
  .c 607, .c 113, .c 3, .c 5, .c 59, .c 3, .c 631, .c 103, .c 3, .c 7, .c 11,
]
private theorem h0070c10 : checkBlock 574723 64 b0070c10 = true := by decide +kernel
private noncomputable def b0070c11 : List Row := [
  .c 3, .c 269, .c 5, .c 3, .p pv2 [pv2,pv83,pv3463], .c 7, .c 3, .c 5, .c 29, .c 3, .c 11,
  .c 13, .c 3, .c 467, .c 173, .c 3, .c 19, .c 5, .c 3, .c 7, .c 53, .c 3, .c 5, .c 547, .c 3,
  .c 163, .c 7, .c 3, .p pv2 [pv2,pv17,pv37,pv457], .c 257, .c 3, .p pv3 [pv2,pv13,pv691], .c 5,
  .c 3, .c 97, .c 19, .c 3, .c 5, .c 67, .c 3, .c 7, .p pv2 [pv2,pv3,pv47911], .c 3, .c 11,
  .p pv2 [pv2,pv3,pv7,pv13], .c 3, .c 37, .c 5, .c 3, .p pv3 [pv2,pv11,pv73,pv179], .c 13, .c 3,
  .c 5, .c 17, .c 3, .c 491, .p pv2 [pv2,pv3,pv79,pv1213], .c 3, .p pv5 [pv2,pv7,pv5867],
  .p pv7 [pv2,pv3,pv23957], .c 3, .c 7, .c 5, .c 3,
]
private theorem h0070c11 : checkBlock 574851 64 b0070c11 = true := by decide +kernel
private noncomputable def b0070c12 : List Row := [
  .c 347, .c 11, .c 3, .c 5, .c 7, .c 3, .c 17, .c 101, .c 3, .c 19, .c 709, .c 3, .c 11, .c 5,
  .c 3, .p pv3 [pv2,pv7,pv17,pv151], .c 307, .c 3, .c 5, .c 37, .c 3, .c 73, .c 23, .c 3,
  .p pv2 [pv2,pv241,pv1193], .c 7, .c 3, .p pv3 [pv2,pv71879], .c 5, .c 3, .c 43, .c 29, .c 3,
  .c 5, .c 11, .c 3, .c 619, .p pv11 [pv2,pv3,pv173,pv277], .c 3, .c 7, .c 17, .c 3,
  .p pv5 [pv2,pv271,pv1061], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv2819],
  .c 3, .c 13, .c 541, .c 3, .p pv5 [pv2,pv421,pv683], .c 367, .c 3, .c 17, .c 5, .c 3, .c 7,
  .c 191, .c 3, .c 5,
]
private theorem h0070c12 : checkBlock 574979 64 b0070c12 = true := by decide +kernel
private noncomputable def b0070c13 : List Row := [
  .c 13, .c 3, .c 19, .c 7, .c 3, .c 223, .p pv3 [pv2,pv3,pv89,pv359], .c 3,
  .p pv2 [pv2,pv269,pv1069], .c 5, .c 3, .p pv3 [pv2,pv29,pv37,pv67],
  .p pv2 [pv2,pv3,pv5,pv19,pv1009], .c 3, .c 5, .p pv5 [pv2,pv3,pv1997], .c 3, .c 7, .c 31, .c 3,
  .c 487, .c 19, .c 3, .p pv3 [pv2,pv103,pv349], .c 5, .c 3, .c 13, .c 17, .c 3, .c 5, .c 73,
  .c 3, .c 71, .p pv2 [pv2,pv3,pv13,pv1229], .c 3, .p pv5 [pv2,pv7,pv10271], .c 11, .c 3, .c 7,
  .c 5, .c 3, .c 41, .c 59, .c 3, .c 5, .c 7, .c 3, .c 11, .p pv13 [pv2,pv3,pv37,pv2591], .c 3,
  .c 23, .c 53, .c 3, .p pv3 [pv2,pv11,pv17,pv769], .c 5, .c 3, .p pv2 [pv2,pv7,pv181,pv227],
  .c 131, .c 3, .c 5, .c 163, .c 3, .p pv19 [pv2,pv5,pv23,pv41,pv61], .c 47,
]
private theorem h0070c13 : checkBlock 575107 64 b0070c13 = true := by decide +kernel
private noncomputable def b0070c14 : List Row := [
  .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv71,pv4051], .c 5, .c 3, .p pv3 [pv2,pv157,pv229],
  .p pv3 [pv2,pv3,pv5,pv13,pv59], .c 3, .c 5, .p pv13 [pv2,pv3,pv11,pv2179], .c 3,
  .p pv13 [pv2,pv5,pv7,pv587], .c 13, .c 3, .c 7, .c 577, .c 3, .c 29, .c 5, .c 3, .c 479, .c 7,
  .c 3, .c 5, .c 419, .c 3, .c 61, .c 653, .c 3, .c 17, .c 23, .c 3,
  .p pv5 [pv2,pv7,pv13,pv29,pv109], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv7,pv761], .c 3, .c 139, .c 7, .c 3, .c 47, .c 31, .c 3, .c 11, .c 5, .c 3,
  .c 19, .c 13, .c 3, .c 5, .c 499, .c 3, .c 7, .c 41, .c 3, .c 79,
  .p pv3 [pv2,pv3,pv7,pv19,pv103], .c 3,
]
private theorem h0070c14 : checkBlock 575235 64 b0070c14 = true := by decide +kernel
private noncomputable def b0070c15 : List Row := [
  .c 457, .c 5, .c 3, .p pv3 [pv2,pv23,pv53,pv59], .p pv3 [pv2,pv3,pv5,pv2131], .c 3, .c 5,
  .c 11, .c 3, .c 557, .c 43, .c 3, .c 37, .c 29, .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv5,pv7,pv137], .c 3, .c 5, .c 7, .c 3, .c 109, .c 61, .c 3,
  .p pv3 [pv2,pv17,pv4231], .c 13, .c 3, .c 257, .c 5, .c 3, .p pv2 [pv2,pv7,pv20551],
  .p pv3 [pv2,pv3,pv5,pv19181], .c 3, .c 5, .c 23, .c 3, .p pv3 [pv2,pv5,pv7193], .c 11, .c 3,
  .c 29, .c 7, .c 3, .c 19, .c 5, .c 3, .c 73, .c 37, .c 3, .c 5, .c 17, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv19,pv631], .c 3, .c 7, .p pv3 [pv2,pv3,pv10657], .c 3, .c 23, .c 5, .c 3,
  .p pv3 [pv2,pv281],
]
private theorem h0070c15 : checkBlock 575363 64 b0070c15 = true := by decide +kernel
private noncomputable def b0070c16 : List Row := [
  .c 7, .c 3, .c 5, .c 13, .c 3, .c 17, .p pv11 [pv2,pv3,pv95917], .c 3, .c 421, .c 11, .c 3,
  .p pv3 [pv2,pv7,pv43,pv239], .c 5, .c 3, .c 7, .c 701, .c 3, .c 5, .c 53, .c 3, .c 11, .c 7,
  .c 3, .c 137, .c 373, .c 3, .c 251, .c 5, .c 3, .c 13, .p pv47 [pv2,pv3,pv5,pv1279], .c 3,
  .c 5, .p pv7 [pv2,pv3,pv47963], .c 3, .c 7, .c 29, .c 3, .c 19, .c 17, .c 3,
  .p pv3 [pv2,pv37,pv3889], .c 5, .c 3, .p pv2 [pv2,pv287789], .p pv11 [pv2,pv3,pv5,pv53,pv181],
  .c 3, .c 5, .c 149, .c 3, .p pv11 [pv2,pv5,pv57559], .p pv11 [pv2,pv3,pv29,pv827], .c 3, .c 11,
  .c 41, .c 3, .c 7, .c 5, .c 3, .c 37, .p pv2 [pv2,pv3,pv5,pv7,pv2741], .c 3, .c 5, .c 7,
]
private theorem h0070c16 : checkBlock 575491 64 b0070c16 = true := by decide +kernel
private noncomputable def b0070c17 : List Row := [
  .c 3, .c 23, .p pv3 [pv2,pv3,pv113,pv283], .c 3, .c 13, .c 109, .c 3, .c 53, .c 5, .c 3, .c 31,
  .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv37,pv2593], .c 3, .p pv2 [pv2,pv5,pv29,pv397], .c 13,
  .c 3, .c 61, .c 7, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv71,pv2027], .c 17, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv15991], .c 3, .c 19, .c 37, .c 3, .c 7, .p pv19 [pv2,pv3,pv17,pv83], .c 3,
  .p pv2 [pv2,pv13,pv11071], .c 5, .c 3, .p pv2 [pv2,pv287849], .c 7, .c 3, .c 5, .c 11, .c 3,
  .p pv11 [pv2,pv5,pv57571], .c 23, .c 3, .p pv2 [pv2,pv163,pv883], .c 19, .c 3,
  .p pv7 [pv2,pv7,pv17,pv41,pv59], .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 29, .c 3, .c 89, .c 7,
  .c 3,
]
private theorem h0070c17 : checkBlock 575619 64 b0070c17 = true := by decide +kernel
private noncomputable def b0070c18 : List Row := [
  .p pv2 [pv2,pv287873], .c 241, .c 3, .p pv3 [pv2,pv79,pv911], .c 5, .c 3, .c 23, .c 181, .c 3,
  .c 5, .c 107, .c 3, .c 7, .c 11, .c 3, .p pv3 [pv2,pv19,pv947], .c 61, .c 3, .c 13, .c 5, .c 3,
  .c 461, .p pv3 [pv2,pv3,pv5,pv17,pv1129], .c 3, .c 5, .c 47, .c 3, .c 101, .c 593, .c 3, .c 17,
  .c 13, .c 3, .c 7, .c 5, .c 3, .c 211, .p pv29 [pv2,pv3,pv5,pv7,pv457], .c 3, .c 5, .c 7, .c 3,
  .c 37, .c 19, .c 3, .p pv2 [pv2,pv359,pv401], .c 11, .c 3, .c 179, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv13,pv113], .c 23, .c 3, .c 5, .p pv5 [pv2,pv3,pv31,pv43], .c 3, .c 11,
  .p pv3 [pv2,pv3,pv7,pv13711], .c 3, .p pv2 [pv2,pv287933], .c 7, .c 3, .c 103,
]
private theorem h0070c18 : checkBlock 575747 64 b0070c18 = true := by decide +kernel
private noncomputable def b0070c19 : List Row := [
  .c 5, .c 3, .c 163, .c 71, .c 3, .c 5, .c 13, .c 3, .c 47, .p pv5 [pv2,pv3,pv17,pv941], .c 3,
  .c 7, .c 43, .c 3, .p pv5 [pv2,pv101,pv2851], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 173,
  .c 3, .p pv3 [pv2,pv5,pv23,pv313], .p pv2 [pv2,pv3,pv95987], .c 3, .c 11, .c 269, .c 3, .c 337,
  .c 5, .c 3, .c 7, .p pv19 [pv2,pv3,pv5,pv29,pv331], .c 3, .c 5, .c 19, .c 3, .c 53, .c 7, .c 3,
  .p pv2 [pv2,pv109,pv1321], .p pv23 [pv2,pv3,pv59,pv1627], .c 3, .p pv2 [pv2,pv61,pv4721], .c 5,
  .c 3, .c 29, .c 11, .c 3, .c 5, .c 17, .c 3, .c 7, .c 167, .c 3, .p pv2 [pv2,pv97,pv2969],
  .c 23, .c 3, .c 11, .c 5, .c 3, .c 67, .p pv7 [pv2,pv3,pv5],
]
private theorem h0070c19 : checkBlock 575875 64 b0070c19 = true := by decide +kernel
private noncomputable def b0070c20 : List Row := [
  .c 3, .c 5, .c 131, .c 3, .c 17, .p pv2 [pv2,pv3,pv23,pv2087], .c 3, .c 13,
  .p pv2 [pv2,pv3,pv10667], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv17,pv43,pv197],
  .p pv17 [pv2,pv3,pv5,pv7,pv13,pv211], .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv14401], .c 13,
  .c 3, .c 397, .p pv23 [pv2,pv3,pv11,pv1091], .c 3, .c 37, .c 5, .c 3, .c 11, .c 19, .c 3, .c 5,
  .c 449, .c 3, .c 43, .c 31, .c 3, .c 757, .c 7, .c 3, .c 97, .c 5, .c 3,
  .p pv3 [pv2,pv107,pv673], .c 41, .c 3, .c 5, .c 89, .c 3, .p pv2 [pv2,pv5,pv7,pv823], .c 11,
  .c 3, .c 7, .c 389, .c 3, .c 17, .c 5, .c 3, .p pv11 [pv2,pv19,pv15161], .c 7, .c 3, .c 5,
  .c 23, .c 3,
]
private theorem h0070c20 : checkBlock 576003 64 b0070c20 = true := by decide +kernel
private noncomputable def b0070c21 : List Row := [
  .p pv2 [pv2,pv5,pv17,pv3389], .c 67, .c 3, .c 19, .c 571, .c 3, .c 29, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv23,pv167], .c 3, .c 5, .c 43, .c 3, .p pv3 [pv2,pv5,pv13,pv277], .c 7,
  .c 3, .p pv5 [pv2,pv31,pv9293], .c 11, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv288089], .c 17,
  .c 3, .c 5, .c 113, .c 3, .c 7, .p pv11 [pv2,pv3,pv3001], .c 3, .c 31, .c 13, .c 3,
  .p pv2 [pv2,pv11,pv2381], .c 5, .c 3, .c 233, .p pv2 [pv2,pv3,pv5,pv19207], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv53,pv151], .c 3, .p pv2 [pv2,pv5,pv47,pv613], .p pv3 [pv2,pv3,pv137,pv701],
  .c 3, .p pv2 [pv2,pv7,pv79,pv521], .c 239, .c 3, .c 7, .c 5, .c 3, .c 307, .c 211, .c 3, .c 5,
  .c 7, .c 3, .c 13, .c 59, .c 3, .c 11,
]
private theorem h0070c21 : checkBlock 576131 64 b0070c21 = true := by decide +kernel
private noncomputable def b0070c22 : List Row := [
  .c 29, .c 3, .c 173, .c 5, .c 3, .c 53, .c 331, .c 3, .c 5, .c 13, .c 3, .c 409, .c 17, .c 3,
  .p pv5 [pv2,pv43,pv6701], .c 7, .c 3, .p pv2 [pv2,pv144073], .c 5, .c 3,
  .p pv2 [pv2,pv193,pv1493], .c 11, .c 3, .c 5, .c 71, .c 3, .c 23,
  .p pv7 [pv2,pv3,pv11,pv37,pv59], .c 3, .c 7, .p pv3 [pv2,pv3,pv96053], .c 3, .c 11, .c 5, .c 3,
  .c 13, .c 7, .c 3, .c 5, .c 41, .c 3, .p pv2 [pv2,pv5,pv28817], .c 443, .c 3, .c 157, .c 37,
  .c 3, .c 227, .c 5, .c 3, .c 7, .c 47, .c 3, .c 5, .c 11, .c 3, .c 59, .c 7, .c 3,
  .p pv3 [pv2,pv72047], .p pv3 [pv2,pv3,pv11,pv41,pv71], .c 3, .c 31, .c 5,
]
private theorem h0070c22 : checkBlock 576259 64 b0070c22 = true := by decide +kernel
private noncomputable def b0070c23 : List Row := [
  .c 3, .c 11, .p pv61 [pv2,pv3,pv5,pv19213], .c 3, .c 5, .c 569, .c 3, .c 7, .c 19, .c 3, .c 13,
  .c 107, .c 3, .c 113, .c 5, .c 3, .c 17, .p pv73 [pv2,pv3,pv5,pv13,pv739], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv23,pv4177], .c 3, .p pv13 [pv2,pv5,pv59,pv977], .c 11, .c 3, .c 277,
  .p pv13 [pv2,pv3,pv191,pv503], .c 3, .c 7, .c 5, .c 3, .c 23, .c 257, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv19,pv37,pv41], .c 79, .c 3, .c 269, .p pv7 [pv2,pv3,pv67,pv239], .c 3,
  .p pv3 [pv2,pv13,pv23,pv241], .c 5, .c 3, .c 19, .c 53, .c 3, .c 5, .c 17, .c 3, .c 29,
  .p pv5 [pv2,pv3,pv7,pv6863], .c 3, .c 37, .c 7, .c 3, .c 199, .c 5, .c 3,
  .p pv2 [pv2,pv101,pv1427], .c 13, .c 3,
]
private theorem h0070c23 : checkBlock 576387 64 b0070c23 = true := by decide +kernel
private noncomputable def b0070c24 : List Row := [
  .c 5, .c 19, .c 3, .c 11, .p pv2 [pv2,pv3,pv32029], .c 3, .c 7, .p pv11 [pv2,pv3,pv12011],
  .c 3, .p pv2 [pv2,pv11,pv13103], .c 5, .c 3, .p pv2 [pv2,pv17,pv31,pv547], .c 7, .c 3, .c 5,
  .c 251, .c 3, .p pv29 [pv2,pv5,pv13,pv887], .p pv5 [pv2,pv3,pv24023], .c 3, .c 367, .c 179,
  .c 3, .c 13, .c 5, .c 3, .c 7, .c 37, .c 3, .c 5, .p pv17 [pv2,pv3,pv7,pv11,pv13], .c 3,
  .p pv3 [pv2,pv5,pv127,pv227], .c 7, .c 3, .c 11, .c 13, .c 3, .c 19, .c 5, .c 3, .c 653, .c 83,
  .c 3, .c 5, .c 29, .c 3, .c 7, .p pv2 [pv2,pv3,pv19,pv281], .c 3, .p pv3 [pv2,pv72077], .c 197,
  .c 3, .c 17, .c 5, .c 3, .c 191, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv29,pv1657], .c 3, .c 13,
]
private theorem h0070c24 : checkBlock 576515 64 b0070c24 = true := by decide +kernel
private noncomputable def b0070c25 : List Row := [
  .c 47, .c 3, .p pv5 [pv2,pv7,pv41189], .p pv7 [pv2,pv3,pv8009], .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv373,pv773], .c 157, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv57667], .c 43,
  .c 3, .p pv2 [pv2,pv144169], .c 23, .c 3, .p pv2 [pv2,pv37,pv7793], .c 5, .c 3,
  .p pv3 [pv2,pv7,pv19,pv271], .c 17, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv73,pv79],
  .p pv5 [pv2,pv3,pv7,pv23,pv199], .c 3, .c 19, .c 7, .c 3, .c 241, .c 5, .c 3, .c 11,
  .p pv13 [pv2,pv3,pv5,pv89], .c 3, .c 5, .p pv3 [pv2,pv3,pv19,pv5059], .c 3,
  .p pv2 [pv2,pv5,pv7,pv11,pv107], .c 71, .c 3, .c 7, .p pv2 [pv2,pv3,pv179], .c 3,
  .p pv5 [pv2,pv17,pv16963], .c 5, .c 3, .p pv2 [pv2,pv23,pv6269], .c 7, .c 3, .c 5,
  .p pv47 [pv2,pv3,pv37,pv433], .c 3, .c 673, .c 11, .c 3, .c 83, .p pv13 [pv2,pv3,pv751],
]
private theorem h0070c25 : checkBlock 576643 64 b0070c25 = true := by decide +kernel
private noncomputable def b0070c26 : List Row := [
  .c 3, .c 73, .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .p pv7 [pv2,pv3,pv7,pv31,pv443], .c 3,
  .p pv13 [pv2,pv5,pv57679], .c 7, .c 3, .c 13, .c 53, .c 3, .c 67, .c 5, .c 3, .c 89, .c 101,
  .c 3, .c 5, .c 23, .c 3, .c 7, .c 13, .c 3, .c 17, .c 11, .c 3, .c 613, .c 5, .c 3, .c 29,
  .c 397, .c 3, .c 5, .c 181, .c 3, .c 11, .c 307, .c 3, .c 163, .c 19, .c 3, .c 7, .c 5, .c 3,
  .c 523, .c 733, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv7211], .p pv2 [pv2,pv3,pv1187], .c 3,
  .c 389, .p pv7 [pv2,pv3,pv13,pv43], .c 3, .c 281, .c 5, .c 3,
]
private theorem h0070c26 : checkBlock 576771 64 b0070c26 = true := by decide +kernel
private noncomputable def b0070c27 : List Row := [
  .p pv2 [pv2,pv7,pv89,pv463], .c 13, .c 3, .c 5, .c 137, .c 3, .c 41, .c 359, .c 3, .c 11, .c 7,
  .c 3, .c 701, .c 5, .c 3, .c 17, .c 43, .c 3, .c 5, .c 67, .c 3, .c 31,
  .p pv3 [pv2,pv3,pv96157], .c 3, .c 7, .p pv2 [pv2,pv3,pv48079], .c 3, .c 13, .c 5, .c 3,
  .c 271, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv569], .c 3, .c 151, .c 19, .c 3,
  .p pv3 [pv2,pv36061], .c 13, .c 3, .c 11, .c 5, .c 3, .c 7, .c 277, .c 3, .c 5, .c 17, .c 3,
  .c 23, .c 7, .c 3, .p pv5 [pv2,pv103,pv2801], .p pv53 [pv2,pv3,pv4007], .c 3, .c 29, .c 5,
  .c 3, .c 47, .c 587, .c 3, .c 5,
]
private theorem h0070c27 : checkBlock 576899 64 b0070c27 = true := by decide +kernel
private noncomputable def b0070c28 : List Row := [
  .c 11, .c 3, .c 7, .p pv5 [pv2,pv3,pv24043], .c 3, .c 283, .c 401, .c 3,
  .p pv2 [pv2,pv29,pv9949], .c 5, .c 3, .c 11, .c 107, .c 3, .c 5, .c 13, .c 3, .c 347,
  .p pv5 [pv2,pv3,pv32059], .c 3, .p pv2 [pv2,pv7,pv47,pv877], .p pv7 [pv2,pv3,pv19,pv2531],
  .c 3, .c 7, .c 5, .c 3, .c 59, .p pv13 [pv2,pv3,pv5,pv7,pv229], .c 3, .c 5, .c 7, .c 3, .c 113,
  .c 11, .c 3, .p pv3 [pv2,pv13,pv31,pv179], .c 17, .c 3, .c 43, .c 5, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv5,pv19237], .c 3, .c 5, .c 53, .c 3, .c 61, .p pv2 [pv2,pv3,pv7,pv13,pv151],
  .c 3, .c 31, .c 7, .c 3, .c 17, .c 5, .c 3, .c 23, .c 233, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv43,pv2237], .c 3, .p pv11 [pv2,pv5,pv7,pv17,pv97], .p pv5 [pv2,pv3,pv167],
]
private theorem h0070c28 : checkBlock 577027 64 b0070c28 = true := by decide +kernel
private noncomputable def b0070c29 : List Row := [
  .c 3, .c 7, .c 11, .c 3, .c 19, .c 5, .c 3, .p pv3 [pv2,pv36073], .c 7, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv24049], .c 3, .c 11, .c 163, .c 3, .c 13, .c 31, .c 3,
  .p pv5 [pv2,pv7,pv11,pv937], .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 47, .c 3, .c 73, .c 7,
  .c 3, .c 379, .p pv2 [pv2,pv3,pv17,pv5659], .c 3, .c 53, .c 5, .c 3, .c 443, .c 23, .c 3, .c 5,
  .c 37, .c 3, .c 7, .c 61, .c 3, .c 11, .p pv11 [pv2,pv3,pv7,pv859], .c 3, .c 79, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv19,pv1381], .c 227, .c 3, .c 5, .c 139, .c 3, .p pv7 [pv2,pv5,pv57727],
  .c 151, .c 3, .c 19, .p pv31 [pv2,pv3,pv13,pv2467], .c 3,
]
private theorem h0070c29 : checkBlock 577155 64 b0070c29 = true := by decide +kernel
private noncomputable def b0070c30 : List Row := [
  .c 7, .c 5, .c 3, .c 157, .c 11, .c 3, .c 5, .c 7, .c 3, .c 47, .c 17, .c 3,
  .p pv2 [pv2,pv288653], .c 229, .c 3, .c 11, .c 5, .c 3, .c 167, .c 41, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv96221], .c 3, .p pv17 [pv2,pv5,pv13,pv4441], .p pv5 [pv2,pv3,pv7,pv29,pv79],
  .c 3, .c 17, .c 7, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv37,pv47,pv83],
  .p pv13 [pv2,pv3,pv5,pv1283], .c 3, .c 5, .c 11, .c 3, .c 29, .p pv3 [pv2,pv3,pv41,pv2347],
  .c 3, .c 7, .c 13, .c 3, .c 109, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv32077],
  .c 3, .c 19, .c 191, .c 3, .p pv2 [pv2,pv144349], .p pv3 [pv2,pv3,pv96233], .c 3, .c 41, .c 5,
  .c 3, .c 7,
]
private theorem h0070c30 : checkBlock 577283 64 b0070c30 = true := by decide +kernel
private noncomputable def b0070c31 : List Row := [
  .c 79, .c 3, .c 5, .c 101, .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv61,pv4733], .c 19, .c 3,
  .c 59, .c 5, .c 3, .c 17, .c 97, .c 3, .c 5, .c 13, .c 3, .c 7, .p pv2 [pv2,pv3,pv48121], .c 3,
  .p pv3 [pv2,pv11,pv17,pv193], .c 37, .c 3, .p pv5 [pv2,pv288731], .c 5, .c 3, .c 127,
  .p pv13 [pv2,pv3,pv5,pv19249], .c 3, .c 5, .c 29, .c 3, .c 677, .p pv3 [pv2,pv3,pv109,pv883],
  .c 3, .c 61, .c 11, .c 3, .c 7, .c 5, .c 3, .c 13, .c 271, .c 3, .c 5, .c 7, .c 3, .c 11,
  .p pv5 [pv2,pv3,pv13,pv617], .c 3, .p pv2 [pv2,pv144379], .c 751, .c 3,
  .p pv2 [pv2,pv11,pv26251], .c 5, .c 3, .p pv3 [pv2,pv7,pv10313],
  .p pv11 [pv2,pv3,pv5,pv23,pv31], .c 3, .c 5, .p pv5 [pv2,pv3,pv47],
]
private theorem h0070c31 : checkBlock 577411 64 b0070c31 = true := by decide +kernel
private noncomputable def b0070c32 : List Row := [
  .c 3, .c 17, .c 19, .c 3, .p pv2 [pv2,pv288773], .c 7, .c 3, .c 23, .c 5, .c 3,
  .p pv11 [pv2,pv17,pv16987], .c 31, .c 3, .c 5, .c 41, .c 3, .c 181, .p pv2 [pv2,pv3,pv48131],
  .c 3, .c 7, .c 131, .c 3, .c 47, .c 5, .c 3, .p pv2 [pv2,pv11,pv13127], .c 7, .c 3, .c 5,
  .c 83, .c 3, .p pv3 [pv2,pv5,pv19], .c 13, .c 3, .c 37, .c 17, .c 3, .p pv2 [pv2,pv7,pv421],
  .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .p pv31 [pv2,pv3,pv7,pv17,pv809], .c 3, .c 359, .c 7,
  .c 3, .p pv2 [pv2,pv144409], .p pv37 [pv2,pv3,pv19,pv563], .c 3, .c 11, .c 5, .c 3, .c 41,
  .c 29, .c 3, .c 5, .c 19, .c 3, .c 7, .c 239, .c 3,
]
private theorem h0070c32 : checkBlock 577539 64 b0070c32 = true := by decide +kernel
private noncomputable def b0070c33 : List Row := [
  .p pv2 [pv2,pv288833], .c 59, .c 3, .c 149, .c 5, .c 3, .c 467, .c 13, .c 3, .c 5, .c 11, .c 3,
  .c 23, .c 107, .c 3, .c 199, .c 89, .c 3, .c 7, .c 5, .c 3, .c 11, .c 17, .c 3, .c 5, .c 7,
  .c 3, .p pv3 [pv2,pv5,pv11,pv13,pv101], .c 127, .c 3, .c 71, .c 137, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv29,pv1423], .c 67, .c 3, .c 5, .c 31, .c 3, .p pv13 [pv2,pv5,pv2311], .c 11,
  .c 3, .p pv2 [pv2,pv144439], .c 7, .c 3, .c 83, .c 5, .c 3, .c 113, .c 19, .c 3, .c 5, .c 373,
  .c 3, .p pv2 [pv2,pv5,pv7,pv4127], .c 23, .c 3, .c 7, .c 521, .c 3, .c 223,
]
private theorem h0070c33 : checkBlock 577667 64 b0070c33 = true := by decide +kernel
private noncomputable def b0070c34 : List Row := [
  .c 5, .c 3, .p pv17 [pv2,pv13,pv71,pv313], .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv23,pv53,pv79],
  .c 3, .c 13, .c 17, .c 3, .p pv3 [pv2,pv72227], .c 11, .c 3, .c 139, .c 5, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv5,pv11,pv17,pv103], .c 3, .c 5, .c 13, .c 3, .c 11, .c 7, .c 3, .c 17,
  .p pv7 [pv2,pv3,pv24077], .c 3, .c 61, .c 5, .c 3, .c 53, .c 353, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv19,pv37,pv137], .c 3, .c 7, .p pv5 [pv2,pv3,pv4013], .c 3, .c 43,
  .p pv3 [pv2,pv3,pv7,pv13759], .c 3, .c 29, .c 5, .c 3, .c 13, .c 317, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv11,pv199], .c 3, .p pv2 [pv2,pv5,pv5779], .c 37, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5351], .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv11,pv109,pv241], .c 23,
]
private theorem h0070c34 : checkBlock 577795 64 b0070c34 = true := by decide +kernel
private noncomputable def b0070c35 : List Row := [
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv57793], .c 31, .c 3, .p pv3 [pv2,pv41,pv881],
  .p pv2 [pv2,pv3,pv96323], .c 3, .c 659, .c 5, .c 3, .c 17, .c 11, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv48163], .c 3, .c 19, .c 43, .c 3, .c 13, .c 7, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv288989], .p pv11 [pv2,pv3,pv5,pv13,pv19], .c 3, .c 5, .c 167, .c 3, .c 179,
  .c 13, .c 3, .c 7, .c 19, .c 3, .c 137, .c 5, .c 3, .c 67, .c 7, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv28901], .c 59, .c 3, .c 109, .p pv2 [pv2,pv3,pv11,pv29,pv151], .c 3, .c 421,
  .c 5, .c 3, .c 7, .p pv23 [pv2,pv3,pv5,pv4817], .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv13763], .c 3,
]
private theorem h0070c35 : checkBlock 577923 64 b0070c35 = true := by decide +kernel
private noncomputable def b0070c36 : List Row := [
  .c 17, .c 7, .c 3, .c 29, .c 23, .c 3, .p pv5 [pv2,pv289031], .c 5, .c 3, .c 487, .c 13, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv67,pv719], .c 3, .c 7, .c 11, .c 3, .c 73, .c 293, .c 3,
  .p pv2 [pv2,pv43,pv3361], .c 5, .c 3, .c 277, .c 139, .c 3, .c 5, .c 673, .c 3, .c 313, .c 19,
  .c 3, .p pv2 [pv2,pv7,pv11,pv1877], .c 17, .c 3, .c 7, .c 5, .c 3, .c 617,
  .p pv7 [pv2,pv3,pv5,pv7,pv2753], .c 3, .c 5, .c 7, .c 3, .c 41, .c 67, .c 3, .c 47, .c 11,
  .c 3, .c 17, .c 5, .c 3, .c 241, .c 163, .c 3, .c 5, .p pv13 [pv2,pv3,pv173,pv557], .c 3,
  .c 11, .c 29, .c 3, .c 53,
]
private theorem h0070c36 : checkBlock 578051 64 b0070c36 = true := by decide +kernel
private noncomputable def b0070c37 : List Row := [
  .c 7, .c 3, .p pv5 [pv2,pv11,pv41,pv641], .c 5, .c 3, .c 19, .p pv3 [pv2,pv3,pv5,pv19273],
  .c 3, .c 5, .c 23, .c 3, .c 13, .p pv2 [pv2,pv3,pv29,pv3323], .c 3, .c 7,
  .p pv13 [pv2,pv3,pv19,pv317], .c 3, .p pv2 [pv2,pv31,pv4663], .c 5, .c 3, .c 61, .c 7, .c 3,
  .c 5, .c 13, .c 3, .c 29, .c 73, .c 3, .c 11, .c 223, .c 3, .c 23, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv257], .c 3, .c 5, .c 331, .c 3, .c 83, .c 7, .c 3,
  .p pv2 [pv2,pv13,pv23,pv967], .c 149, .c 3, .c 37, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5,
  .c 463, .c 3, .c 7, .c 349, .c 3, .p pv3 [pv2,pv72287], .p pv2 [pv2,pv3,pv7,pv281], .c 3,
  .c 11, .c 5,
]
private theorem h0070c37 : checkBlock 578179 64 b0070c37 = true := by decide +kernel
private noncomputable def b0070c38 : List Row := [
  .c 3, .p pv2 [pv2,pv144577], .p pv43 [pv2,pv3,pv5,pv37,pv521], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv48193], .c 3, .c 167, .c 17, .c 3, .p pv5 [pv2,pv7,pv101,pv409], .c 541,
  .c 3, .c 7, .c 5, .c 3, .c 173, .c 19, .c 3, .c 5, .c 7, .c 3, .c 211,
  .p pv5 [pv2,pv3,pv12049], .c 3, .c 13, .c 79, .c 3, .p pv2 [pv2,pv289181], .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv13,pv1483], .c 3, .c 5, .c 59, .c 3, .c 23, .c 13, .c 3, .c 41, .c 7,
  .c 3, .c 43, .c 5, .c 3, .p pv19 [pv2,pv19,pv31,pv491], .p pv11 [pv2,pv3,pv5,pv241], .c 3,
  .c 5, .p pv3 [pv2,pv3,pv96401], .c 3, .c 67, .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv149,pv647],
  .c 3, .c 571, .c 5, .c 3, .c 31, .c 7, .c 3,
]
private theorem h0070c38 : checkBlock 578307 64 b0070c38 = true := by decide +kernel
private noncomputable def b0070c39 : List Row := [
  .c 5, .c 71, .c 3, .p pv3 [pv2,pv5,pv14461], .c 389, .c 3, .c 113, .c 347, .c 3,
  .p pv2 [pv2,pv7,pv73,pv283], .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv4591],
  .c 3, .c 607, .c 7, .c 3, .p pv2 [pv2,pv17,pv47,pv181], .c 11, .c 3, .p pv2 [pv2,pv289241],
  .c 5, .c 3, .p pv3 [pv2,pv167,pv433], .c 31, .c 3, .c 5, .p pv5 [pv2,pv3,pv23,pv131], .c 3,
  .c 7, .p pv5 [pv2,pv3,pv3571], .c 3, .c 257, .p pv11 [pv2,pv3,pv7,pv71,pv97], .c 3, .c 13,
  .c 5, .c 3, .c 23, .c 29, .c 3, .c 5, .c 17, .c 3, .c 19, .p pv17 [pv2,pv3,pv37,pv1303], .c 3,
  .p pv3 [pv2,pv7,pv10331], .c 13, .c 3, .c 7, .c 5, .c 3, .c 107, .c 41, .c 3, .c 5, .c 7, .c 3,
  .c 17,
]
private theorem h0070c39 : checkBlock 578435 64 b0070c39 = true := by decide +kernel
private noncomputable def b0070c40 : List Row := [
  .p pv2 [pv2,pv3,pv211,pv457], .c 3, .c 11, .c 19, .c 3, .p pv2 [pv2,pv109,pv1327], .c 5, .c 3,
  .c 29, .p pv19 [pv2,pv3,pv5,pv9643], .c 3, .c 5, .p pv3 [pv2,pv3,pv96431], .c 3, .c 13, .c 83,
  .c 3, .p pv2 [pv2,pv79,pv1831], .c 7, .c 3, .p pv2 [pv2,pv439,pv659], .c 5, .c 3,
  .p pv3 [pv2,pv29,pv43], .c 11, .c 3, .c 5, .c 13, .c 3, .p pv19 [pv2,pv5,pv7,pv4133], .c 227,
  .c 3, .c 7, .c 17, .c 3, .c 11, .c 5, .c 3, .c 419, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv17,pv31,pv61], .c 3, .c 43, .c 277, .c 3, .c 23, .p pv3 [pv2,pv3,pv96443],
  .c 3, .c 17, .c 5, .c 3, .c 7, .c 73, .c 3, .c 5, .c 11, .c 3, .c 109, .c 7, .c 3,
  .p pv5 [pv2,pv289343], .p pv13 [pv2,pv3,pv11,pv137],
]
private theorem h0070c40 : checkBlock 578563 64 b0070c40 = true := by decide +kernel
private noncomputable def b0070c41 : List Row := [
  .c 3, .p pv2 [pv2,pv199,pv727], .c 5, .c 3, .c 11, .p pv11 [pv2,pv3,pv5,pv643], .c 3, .c 5,
  .c 53, .c 3, .c 7, .c 383, .c 3, .c 37, .p pv7 [pv2,pv3,pv7,pv1531], .c 3, .c 557, .c 5, .c 3,
  .p pv3 [pv2,pv72341], .c 17, .c 3, .c 5, .c 43, .c 3, .p pv3 [pv2,pv5,pv19,pv1523], .c 11,
  .c 3, .c 13, .c 23, .c 3, .c 7, .c 5, .c 3, .c 19, .c 449, .c 3, .c 5, .c 7, .c 3, .c 311,
  .c 13, .c 3, .p pv3 [pv2,pv11,pv6577], .p pv2 [pv2,pv3,pv19,pv5077], .c 3, .c 151, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv2953], .c 37, .c 3, .c 5, .c 19, .c 3, .c 31, .p pv3 [pv2,pv3,pv7,pv13781],
  .c 3, .c 193, .c 7, .c 3, .c 53, .c 5, .c 3,
]
private theorem h0070c41 : checkBlock 578691 64 b0070c41 = true := by decide +kernel
private noncomputable def b0070c42 : List Row := [
  .p pv13 [pv2,pv23,pv12583], .p pv2 [pv2,pv3,pv5,pv11,pv877], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv397], .c 3, .c 11, .c 17, .c 3, .c 7, .p pv3 [pv2,pv3,pv13,pv41,pv181], .c 3,
  .p pv2 [pv2,pv11,pv83,pv317], .c 5, .c 3, .c 59, .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv89,pv271],
  .c 3, .p pv7 [pv2,pv5,pv103,pv281], .c 31, .c 3, .c 17, .c 29, .c 3, .c 19, .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv67], .c 3, .c 5, .c 23, .c 3, .c 199, .c 7, .c 3, .c 11, .c 47, .c 3,
  .c 13, .c 5, .c 3, .c 43, .c 19, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv1237], .c 3, .c 7,
  .p pv3 [pv2,pv3,pv96487], .c 3, .c 29, .c 13, .c 3, .c 23, .c 5, .c 3, .c 37, .c 11, .c 3,
  .c 5,
]
private theorem h0070c42 : checkBlock 578819 64 b0070c42 = true := by decide +kernel
private noncomputable def b0070c43 : List Row := [
  .c 67, .c 3, .c 61, .c 503, .c 3, .p pv2 [pv2,pv7,pv23,pv29,pv31], .p pv3 [pv2,pv3,pv96493],
  .c 3, .c 7, .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv7,pv919], .c 3, .c 5, .c 7, .c 3, .c 13,
  .c 197, .c 3, .c 19, .c 167, .c 3, .c 47, .c 5, .c 3, .p pv7 [pv2,pv7,pv41357], .c 443, .c 3,
  .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv57901], .c 37, .c 3, .p pv3 [pv2,pv157,pv461], .c 7, .c 3,
  .p pv5 [pv2,pv289511], .c 5, .c 3, .c 11, .c 173, .c 3, .c 5, .c 17, .c 3, .c 439, .c 29, .c 3,
  .c 7, .c 31, .c 3, .p pv2 [pv2,pv144763], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 359, .c 3,
  .c 17, .c 11,
]
private theorem h0070c43 : checkBlock 578947 64 b0070c43 = true := by decide +kernel
private noncomputable def b0070c44 : List Row := [
  .c 3, .c 227, .p pv7 [pv2,pv3,pv53,pv607], .c 3, .p pv2 [pv2,pv7,pv19,pv311], .c 5, .c 3, .c 7,
  .c 83, .c 3, .c 5, .c 239, .c 3, .c 19, .c 7, .c 3, .p pv2 [pv2,pv11,pv2393], .c 73, .c 3,
  .p pv3 [pv2,pv191,pv379], .c 5, .c 3, .p pv7 [pv2,pv289559], .c 761, .c 3, .c 5, .c 271, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv16087], .c 3, .c 13, .c 11, .c 3, .c 347, .c 5, .c 3, .c 79, .c 131,
  .c 3, .c 5, .c 269, .c 3, .c 11, .c 13, .c 3, .c 43, .c 103, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv289589], .c 47, .c 3, .c 5, .c 7, .c 3, .c 107, .c 193, .c 3,
  .p pv2 [pv2,pv19,pv7621], .p pv3 [pv2,pv3,pv37,pv2609], .c 3,
]
private theorem h0070c44 : checkBlock 579075 64 b0070c44 = true := by decide +kernel
private noncomputable def b0070c45 : List Row := [
  .c 59, .c 5, .c 3, .c 23, .c 653, .c 3, .c 5, .c 29, .c 3, .c 389, .c 397, .c 3, .c 11, .c 7,
  .c 3, .c 599, .c 5, .c 3, .p pv11 [pv2,pv11,pv113,pv233], .c 13, .c 3, .c 5, .c 127, .c 3,
  .p pv2 [pv2,pv5,pv7,pv331], .c 19, .c 3, .c 7, .p pv2 [pv2,pv3,pv17,pv631], .c 3,
  .p pv5 [pv2,pv59,pv4909], .c 5, .c 3, .c 373, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv16091], .c 3,
  .p pv11 [pv2,pv5,pv13,pv557], .p pv2 [pv2,pv3,pv11,pv67,pv131], .c 3, .p pv5 [pv2,pv289643],
  .c 41, .c 3, .c 11, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 79, .c 3,
  .p pv19 [pv2,pv5,pv19,pv3049], .c 7, .c 3, .c 61, .c 13, .c 3, .c 167, .c 5, .c 3, .c 19,
]
private theorem h0070c45 : checkBlock 579203 64 b0070c45 = true := by decide +kernel
private noncomputable def b0070c46 : List Row := [
  .p pv3 [pv2,pv3,pv5,pv41,pv157], .c 3, .c 5, .c 11, .c 3, .c 7, .c 17, .c 3, .c 23, .c 67,
  .c 3, .p pv5 [pv2,pv139,pv521], .c 5, .c 3, .c 11, .c 593, .c 3, .c 5, .c 19, .c 3, .c 13,
  .c 137, .c 3, .c 17, .p pv2 [pv2,pv3,pv61,pv1583], .c 3, .c 7, .c 5, .c 3, .c 263, .c 29, .c 3,
  .c 5, .c 7, .c 3, .c 73, .c 11, .c 3, .p pv5 [pv2,pv211,pv1373], .p pv11 [pv2,pv3,pv12071],
  .c 3, .c 131, .c 5, .c 3, .c 727, .c 31, .c 3, .c 5, .p pv2 [pv2,pv3,pv269,pv359], .c 3, .c 71,
  .p pv11 [pv2,pv3,pv7,pv3449], .c 3, .c 101, .c 7, .c 3, .c 19, .c 5, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv5,pv3863], .c 3, .c 5, .c 37,
]
private theorem h0070c46 : checkBlock 579331 64 b0070c46 = true := by decide +kernel
private noncomputable def b0070c47 : List Row := [
  .c 3, .c 149, .c 47, .c 3, .c 7, .c 11, .c 3, .p pv3 [pv2,pv36217], .c 5, .c 3, .c 17, .c 7,
  .c 3, .c 5, .c 157, .c 3, .c 11, .c 367, .c 3, .p pv3 [pv2,pv17,pv4261],
  .p pv2 [pv2,pv3,pv59,pv1637], .c 3, .p pv5 [pv2,pv7,pv11,pv53,pv71], .c 5, .c 3, .c 7, .c 43,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv6899], .c 3, .p pv3 [pv2,pv5,pv1811], .c 7, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv2683], .c 3, .p pv2 [pv2,pv144883], .c 5, .c 3,
  .p pv2 [pv2,pv19,pv101,pv151], .p pv2 [pv2,pv3,pv5,pv13,pv743], .c 3, .c 5, .c 17, .c 3, .c 7,
  .c 13, .c 3, .c 11, .c 251, .c 3, .p pv2 [pv2,pv181,pv1601], .c 5, .c 3,
  .p pv3 [pv2,pv11,pv37,pv89], .p pv2 [pv2,pv3,pv5,pv19319], .c 3, .c 5, .c 23, .c 3, .c 17,
  .p pv5 [pv2,pv3,pv10733], .c 3,
]
private theorem h0070c47 : checkBlock 579459 64 b0070c47 = true := by decide +kernel
private noncomputable def b0070c48 : List Row := [
  .p pv2 [pv2,pv7,pv41399], .c 83, .c 3, .c 7, .c 5, .c 3, .c 229, .c 11, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv149,pv389], .p pv2 [pv2,pv3,pv11,pv4391], .c 3, .c 41, .c 107, .c 3, .c 11,
  .c 5, .c 3, .p pv2 [pv2,pv7,pv127,pv163], .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv1789], .c 3,
  .p pv7 [pv2,pv5,pv43,pv337], .p pv2 [pv2,pv3,pv7,pv37,pv373], .c 3, .c 137, .c 7, .c 3,
  .p pv2 [pv2,pv19,pv29,pv263], .c 5, .c 3, .c 449, .c 53, .c 3, .c 5, .c 11, .c 3, .c 19,
  .p pv5 [pv2,pv3,pv83,pv97], .c 3, .c 7, .c 37, .c 3, .c 13, .c 5, .c 3, .c 11, .c 7, .c 3,
  .c 5, .c 661, .c 3, .p pv7 [pv2,pv5,pv11,pv17,pv31], .c 281, .c 3, .p pv2 [pv2,pv289853],
  .c 13, .c 3, .p pv5 [pv2,pv7,pv647],
]
private theorem h0070c48 : checkBlock 579587 64 b0070c48 = true := by decide +kernel
private noncomputable def b0070c49 : List Row := [
  .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv4831], .c 3, .c 5, .c 701, .c 3, .c 31, .c 7, .c 3,
  .p pv3 [pv2,pv72467], .c 29, .c 3, .c 181, .c 5, .c 3, .c 691, .c 17, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv48313], .c 3, .c 7, .p pv2 [pv2,pv3,pv31,pv1039], .c 3, .c 53, .c 43, .c 3,
  .p pv2 [pv2,pv193,pv751], .c 5, .c 3, .p pv2 [pv2,pv289889], .c 41, .c 3, .c 5, .c 13, .c 3,
  .c 163, .c 31, .c 3, .c 29, .c 11, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv18119], .c 569, .c 3,
  .c 5, .c 7, .c 3, .c 11, .c 19, .c 3, .c 37, .p pv2 [pv2,pv3,pv211,pv229], .c 3, .c 107, .c 5,
  .c 3, .c 13, .c 101,
]
private theorem h0070c49 : checkBlock 579715 64 b0070c49 = true := by decide +kernel
private noncomputable def b0070c50 : List Row := [
  .c 3, .c 5, .c 293, .c 3, .p pv2 [pv2,pv5,pv11597], .c 17, .c 3, .c 71, .c 7, .c 3, .c 41,
  .c 5, .c 3, .p pv2 [pv2,pv144967], .c 491, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv23,pv191], .c 3,
  .p pv3 [pv2,pv5,pv7,pv19,pv109], .p pv3 [pv2,pv3,pv127,pv761], .c 3, .c 7, .c 631, .c 3,
  .p pv2 [pv2,pv144973], .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv10739], .c 3,
  .c 59, .c 29, .c 3, .c 13, .c 439, .c 3, .c 307, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 19,
  .c 3, .c 43, .c 7, .c 3, .p pv2 [pv2,pv289973], .p pv2 [pv2,pv3,pv31,pv1559], .c 3, .c 11,
  .c 5, .c 3, .c 503, .p pv43 [pv2,pv3,pv5,pv179], .c 3, .c 5, .p pv5 [pv2,pv3,pv96661], .c 3,
]
private theorem h0070c50 : checkBlock 579843 64 b0070c50 = true := by decide +kernel
private noncomputable def b0070c51 : List Row := [
  .c 7, .p pv5 [pv2,pv3,pv17,pv2843], .c 3, .c 337, .c 31, .c 3, .p pv5 [pv2,pv13,pv22307], .c 5,
  .c 3, .c 17, .c 23, .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv29], .c 619, .c 3, .c 523,
  .c 127, .c 3, .c 7, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv11,pv5273], .p pv5 [pv2,pv3,pv19,pv53], .c 3, .c 23, .c 211, .c 3, .c 101,
  .c 5, .c 3, .c 37, .c 19, .c 3, .c 5, .c 17, .c 3, .c 251, .c 11, .c 3, .c 191, .c 7, .c 3,
  .c 13, .c 5, .c 3, .p pv11 [pv2,pv290039], .p pv13 [pv2,pv3,pv5,pv2417], .c 3, .c 5, .c 29,
  .c 3, .c 17, .p pv5 [pv2,pv3,pv48341], .c 3, .c 7,
]
private theorem h0070c51 : checkBlock 579971 64 b0070c51 = true := by decide +kernel
private noncomputable def b0070c52 : List Row := [
  .c 13, .c 3, .c 31, .c 5, .c 3, .c 41, .c 7, .c 3, .c 5, .c 163, .c 3, .c 47, .c 37, .c 3,
  .c 19, .c 11, .c 3, .p pv2 [pv2,pv7,pv20719], .c 5, .c 3, .c 7, .c 71, .c 3, .c 5, .c 59, .c 3,
  .c 11, .c 7, .c 3, .c 97, .c 17, .c 3, .p pv2 [pv2,pv11,pv26371], .c 5, .c 3,
  .p pv3 [pv2,pv47,pv1543], .c 61, .c 3, .c 5, .c 13, .c 3, .c 7, .p pv3 [pv2,pv3,pv96697], .c 3,
  .p pv2 [pv2,pv139,pv2087], .c 677, .c 3, .c 17, .c 5, .c 3, .c 43, .p pv7 [pv2,pv3,pv5,pv967],
  .c 3, .c 5, .c 109, .c 3, .c 271, .p pv2 [pv2,pv3,pv71,pv227], .c 3, .c 11,
  .p pv3 [pv2,pv3,pv96703], .c 3, .c 7, .c 5,
]
private theorem h0070c52 : checkBlock 580099 64 b0070c52 = true := by decide +kernel
private noncomputable def b0070c53 : List Row := [
  .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv7,pv307], .c 3, .c 5, .c 7, .c 3, .c 19, .c 331, .c 3,
  .c 401, .c 379, .c 3, .c 83, .c 5, .c 3, .p pv2 [pv2,pv7,pv31,pv191], .c 11, .c 3, .c 5, .c 23,
  .c 3, .c 37, .c 41, .c 3, .c 73, .c 7, .c 3, .c 11, .c 5, .c 3, .c 31,
  .p pv31 [pv2,pv3,pv5,pv23,pv29], .c 3, .c 5, .c 53, .c 3, .p pv2 [pv2,pv5,pv7,pv829],
  .p pv5 [pv2,pv3,pv103,pv313], .c 3, .c 7, .c 47, .c 3, .c 23, .c 5, .c 3, .c 29, .c 7, .c 3,
  .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv131,pv443], .c 13, .c 3, .c 499,
  .p pv2 [pv2,pv3,pv11,pv977], .c 3, .p pv5 [pv2,pv7,pv41453], .c 5, .c 3, .c 7, .c 31, .c 3,
]
private theorem h0070c53 : checkBlock 580227 64 b0070c53 = true := by decide +kernel
private noncomputable def b0070c54 : List Row := [
  .c 5, .p pv2 [pv2,pv3,pv7,pv47], .c 3, .p pv7 [pv2,pv5,pv11,pv1319], .c 7, .c 3, .c 547, .c 89,
  .c 3, .p pv2 [pv2,pv13,pv11161], .c 5, .c 3, .p pv2 [pv2,pv290189],
  .p pv11 [pv2,pv3,pv5,pv17,pv569], .c 3, .c 5, .c 349, .c 3, .c 7, .c 11, .c 3, .c 17, .c 461,
  .c 3, .c 47, .c 5, .c 3, .p pv3 [pv2,pv72551], .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv3023],
  .c 3, .c 67, .c 73, .c 3, .c 317, .c 157, .c 3, .c 7, .c 5, .c 3, .c 227, .c 263, .c 3, .c 5,
  .c 7, .c 3, .c 23, .c 563, .c 3, .c 43, .c 11, .c 3, .c 13, .c 5, .c 3, .c 19,
  .p pv13 [pv2,pv3,pv5,pv11,pv1759], .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv61], .c 3, .c 11,
]
private theorem h0070c54 : checkBlock 580355 64 b0070c54 = true := by decide +kernel
private noncomputable def b0070c55 : List Row := [
  .c 199, .c 3, .p pv5 [pv2,pv290243], .c 7, .c 3, .c 29, .c 5, .c 3, .c 17, .c 59, .c 3, .c 5,
  .c 19, .c 3, .c 613, .p pv11 [pv2,pv3,pv6047], .c 3, .c 7, .c 41, .c 3, .c 751, .c 5, .c 3,
  .p pv3 [pv2,pv13,pv2791], .c 7, .c 3, .c 5, .c 31, .c 3, .c 13, .c 23, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv101,pv479], .c 3, .p pv3 [pv2,pv7,pv1481], .c 5, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv5,pv41,pv59], .c 3, .c 5, .c 13, .c 3, .c 79, .c 7, .c 3,
  .p pv3 [pv2,pv18143], .c 659, .c 3, .c 19, .c 5, .c 3, .c 23, .c 11, .c 3, .c 5, .c 617, .c 3,
  .c 7, .c 139, .c 3, .p pv5 [pv2,pv13,pv137,pv163], .c 29,
]
private theorem h0070c55 : checkBlock 580483 64 b0070c55 = true := by decide +kernel
private noncomputable def b0070c56 : List Row := [
  .c 3, .c 11, .c 5, .c 3, .c 13, .c 19, .c 3, .c 5, .p pv2 [pv2,pv3,pv32257], .c 3,
  .p pv7 [pv2,pv5,pv31,pv1873], .p pv23 [pv2,pv3,pv13,pv1861], .c 3, .c 311,
  .p pv11 [pv2,pv3,pv29,pv47,pv71], .c 3, .c 7, .c 5, .c 3, .c 101, .c 337, .c 3, .c 5, .c 7,
  .c 3, .c 31, .p pv3 [pv2,pv3,pv10753], .c 3, .c 29, .c 17, .c 3, .p pv3 [pv2,pv43,pv211], .c 5,
  .c 3, .c 11, .c 23, .c 3, .c 5, .p pv7 [pv2,pv3,pv17,pv5693], .c 3,
  .p pv2 [pv2,pv5,pv11,pv5279], .p pv2 [pv2,pv3,pv7,pv31,pv223], .c 3, .c 13, .c 7, .c 3, .c 17,
  .c 5, .c 3, .c 71, .p pv3 [pv2,pv3,pv5,pv13,pv1489], .c 3, .c 5, .p pv2 [pv2,pv3,pv19,pv283],
  .c 3, .c 53, .c 11, .c 3, .c 7, .c 79, .c 3, .p pv2 [pv2,pv47,pv3089], .c 5, .c 3,
]
private theorem h0070c56 : checkBlock 580611 64 b0070c56 = true := by decide +kernel
private noncomputable def b0070c57 : List Row := [
  .c 97, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv151,pv641], .c 3, .c 83, .c 271, .c 3,
  .p pv2 [pv2,pv11,pv67,pv197], .p pv3 [pv2,pv3,pv43,pv2251], .c 3, .p pv2 [pv2,pv7,pv13,pv3191],
  .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 389, .c 3, .c 61, .c 7, .c 3, .p pv2 [pv2,pv290393],
  .c 11, .c 3, .p pv3 [pv2,pv19,pv3821], .c 5, .c 3, .c 673, .c 13, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv41,pv787], .c 3, .c 7, .p pv2 [pv2,pv3,pv29,pv1669], .c 3, .c 103, .c 23,
  .c 3, .c 67, .c 5, .c 3, .c 181, .c 191, .c 3, .c 5, .p pv5 [pv2,pv3,pv97,pv499], .c 3, .c 29,
  .p pv2 [pv2,pv3,pv23,pv61], .c 3, .c 31, .c 19, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv290429],
  .c 73, .c 3, .c 5,
]
private theorem h0070c57 : checkBlock 580739 64 b0070c57 = true := by decide +kernel
private noncomputable def b0070c58 : List Row := [
  .c 7, .c 3, .p pv7 [pv2,pv5,pv29,pv2003], .c 17, .c 3, .c 11, .c 13, .c 3, .c 211, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv11,pv23,pv41], .p pv2 [pv2,pv3,pv5,pv17,pv67], .c 3, .c 5, .c 151, .c 3,
  .p pv2 [pv2,pv5,pv37,pv157], .c 61, .c 3, .c 17, .c 7, .c 3, .p pv3 [pv2,pv36307], .c 5, .c 3,
  .p pv11 [pv2,pv13,pv22343], .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv96821], .c 3, .c 13, .c 53,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv96823], .c 3, .c 11, .c 5, .c 3, .c 569, .c 7, .c 3, .c 5, .c 13,
  .c 3, .c 367, .c 19, .c 3, .c 47, .p pv17 [pv2,pv3,pv8069], .c 3, .c 43, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv23,pv421], .c 3, .c 5, .c 11, .c 3, .c 487, .c 7,
]
private theorem h0070c58 : checkBlock 580867 64 b0070c58 = true := by decide +kernel
private noncomputable def b0070c59 : List Row := [
  .c 3, .p pv2 [pv2,pv13,pv11173], .c 283, .c 3, .c 23, .c 5, .c 3, .c 11, .c 37, .c 3, .c 5,
  .c 137, .c 3, .c 7, .c 103, .c 3, .c 479, .p pv17 [pv2,pv3,pv7,pv6917], .c 3, .c 31, .c 5,
  .c 3, .c 19, .p pv11 [pv2,pv3,pv5,pv269], .c 3, .c 5, .p pv5 [pv2,pv3,pv113,pv857], .c 3,
  .c 241, .c 11, .c 3, .c 157, .c 43, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv145267],
  .p pv17 [pv2,pv3,pv5,pv7,pv2767], .c 3, .c 5, .c 7, .c 3, .c 89, .c 83, .c 3, .c 13,
  .p pv19 [pv2,pv3,pv6053], .c 3, .c 41, .c 5, .c 3, .p pv2 [pv2,pv7,pv41507],
  .p pv43 [pv2,pv3,pv5,pv13,pv149], .c 3, .c 5, .c 173, .c 3, .c 17, .c 13, .c 3, .c 107, .c 7,
  .c 3,
]
private theorem h0070c59 : checkBlock 580995 64 b0070c59 = true := by decide +kernel
private noncomputable def b0070c60 : List Row := [
  .c 193, .c 5, .c 3, .c 701, .c 29, .c 3, .c 5, .p pv11 [pv2,pv3,pv12107], .c 3, .c 11,
  .p pv3 [pv2,pv3,pv96857], .c 3, .c 7, .p pv2 [pv2,pv3,pv5381], .c 3, .c 19, .c 5, .c 3, .c 37,
  .c 7, .c 3, .c 5, .c 601, .c 3, .p pv13 [pv2,pv5,pv89,pv653], .p pv2 [pv2,pv3,pv19,pv2549],
  .c 3, .p pv3 [pv2,pv72647], .c 17, .c 3, .p pv5 [pv2,pv7,pv41513], .c 5, .c 3, .c 7, .c 13,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv11,pv17,pv37], .c 3, .p pv3 [pv2,pv5,pv1453], .c 7, .c 3,
  .c 11, .c 59, .c 3, .c 17, .c 5, .c 3, .c 31, .c 359, .c 3, .c 5, .p pv3 [pv2,pv3,pv73,pv1327],
  .c 3, .c 7, .c 23, .c 3, .p pv2 [pv2,pv331,pv439], .p pv3 [pv2,pv3,pv7,pv659], .c 3, .c 13,
  .c 5, .c 3, .c 47,
]
private theorem h0070c60 : checkBlock 581123 64 b0070c60 = true := by decide +kernel
private noncomputable def b0070c61 : List Row := [
  .c 11, .c 3, .c 5, .c 41, .c 3, .p pv3 [pv2,pv5,pv29063], .p pv5 [pv2,pv3,pv11,pv8807], .c 3,
  .c 19, .c 13, .c 3, .c 7, .c 5, .c 3, .c 23, .c 17, .c 3, .c 5, .c 7, .c 3, .c 137,
  .p pv2 [pv2,pv3,pv67,pv241], .c 3, .c 109, .c 73, .c 3, .p pv5 [pv2,pv23,pv12637], .c 5, .c 3,
  .c 269, .p pv3 [pv2,pv3,pv5,pv2153], .c 3, .c 5, .c 11, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv7,pv13841], .c 3, .c 59, .c 7, .c 3, .p pv2 [pv2,pv17,pv83,pv103], .c 5,
  .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv9689], .c 3, .c 5, .c 13, .c 3,
  .p pv11 [pv2,pv5,pv7,pv11,pv151], .p pv5 [pv2,pv3,pv24223], .c 3, .c 7, .c 67, .c 3, .c 29,
  .c 5, .c 3, .p pv3 [pv2,pv72671], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv757],
]
private theorem h0070c61 : checkBlock 581251 64 b0070c61 = true := by decide +kernel
private noncomputable def b0070c62 : List Row := [
  .c 3, .c 19, .c 11, .c 3, .c 641, .c 281, .c 3, .p pv3 [pv2,pv7,pv29,pv179], .c 5, .c 3, .c 7,
  .c 421, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv109,pv127], .c 3, .p pv17 [pv2,pv5,pv53,pv1097],
  .c 7, .c 3, .c 17, .c 19, .c 3, .c 277, .c 5, .c 3, .p pv2 [pv2,pv137,pv1061], .c 229, .c 3,
  .c 5, .c 47, .c 3, .c 7, .p pv2 [pv2,pv3,pv96907], .c 3, .p pv5 [pv2,pv43,pv6761], .c 11, .c 3,
  .c 173, .c 5, .c 3, .p pv2 [pv2,pv307,pv947], .c 547, .c 3, .c 5, .c 31, .c 3, .c 11,
  .p pv5 [pv2,pv3,pv673], .c 3, .c 13, .c 29, .c 3, .c 7, .c 5, .c 3, .c 43,
  .p pv2 [pv2,pv3,pv5,pv7,pv13,pv71], .c 3, .c 5, .c 7, .c 3, .c 151, .c 13, .c 3,
]
private theorem h0070c62 : checkBlock 581379 64 b0070c62 = true := by decide +kernel
private noncomputable def b0070c63 : List Row := [
  .c 373, .c 23, .c 3, .c 61, .c 5, .c 3, .c 17, .p pv7 [pv2,pv3,pv5,pv2423], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv89], .c 3, .c 47, .c 19, .c 3, .c 11, .c 7, .c 3, .c 677, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv13217], .p pv3 [pv2,pv3,pv5,pv3877], .c 3, .c 5, .p pv2 [pv2,pv3,pv48463],
  .c 3, .c 71, .c 59, .c 3, .c 7, .c 53, .c 3, .p pv2 [pv2,pv347,pv419], .c 5, .c 3, .c 563,
  .c 7, .c 3, .c 5, .c 17, .c 3, .c 31, .c 739, .c 3, .p pv2 [pv2,pv145399],
  .p pv3 [pv2,pv3,pv79,pv409], .c 3, .c 11, .c 5, .c 3, .c 7, .c 113, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv577], .c 3, .c 17, .c 7, .c 3, .c 67, .c 599, .c 3, .c 13,
]
private theorem h0070c63 : checkBlock 581507 64 b0070c63 = true := by decide +kernel
noncomputable def rows0070 : List Row :=
  b0070c00 ++ ( b0070c01 ++ ( b0070c02 ++ ( b0070c03 ++ ( b0070c04 ++ ( b0070c05 ++ (
  b0070c06 ++ ( b0070c07 ++ ( b0070c08 ++ ( b0070c09 ++ ( b0070c10 ++ ( b0070c11 ++ (
  b0070c12 ++ ( b0070c13 ++ ( b0070c14 ++ ( b0070c15 ++ ( b0070c16 ++ ( b0070c17 ++ (
  b0070c18 ++ ( b0070c19 ++ ( b0070c20 ++ ( b0070c21 ++ ( b0070c22 ++ ( b0070c23 ++ (
  b0070c24 ++ ( b0070c25 ++ ( b0070c26 ++ ( b0070c27 ++ ( b0070c28 ++ ( b0070c29 ++ (
  b0070c30 ++ ( b0070c31 ++ ( b0070c32 ++ ( b0070c33 ++ ( b0070c34 ++ ( b0070c35 ++ (
  b0070c36 ++ ( b0070c37 ++ ( b0070c38 ++ ( b0070c39 ++ ( b0070c40 ++ ( b0070c41 ++ (
  b0070c42 ++ ( b0070c43 ++ ( b0070c44 ++ ( b0070c45 ++ ( b0070c46 ++ ( b0070c47 ++ (
  b0070c48 ++ ( b0070c49 ++ ( b0070c50 ++ ( b0070c51 ++ ( b0070c52 ++ ( b0070c53 ++ (
  b0070c54 ++ ( b0070c55 ++ ( b0070c56 ++ ( b0070c57 ++ ( b0070c58 ++ ( b0070c59 ++ (
  b0070c60 ++ ( b0070c61 ++ ( b0070c62 ++ ( b0070c63
  )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
attribute [local irreducible] checkBlock checkRows checkPrime
theorem checked0070 : checkBlock 573443 4096 rows0070 = true :=
  checkBlock_append h0070c00 ( checkBlock_append h0070c01 ( checkBlock_append h0070c02 (
  checkBlock_append h0070c03 ( checkBlock_append h0070c04 ( checkBlock_append h0070c05 (
  checkBlock_append h0070c06 ( checkBlock_append h0070c07 ( checkBlock_append h0070c08 (
  checkBlock_append h0070c09 ( checkBlock_append h0070c10 ( checkBlock_append h0070c11 (
  checkBlock_append h0070c12 ( checkBlock_append h0070c13 ( checkBlock_append h0070c14 (
  checkBlock_append h0070c15 ( checkBlock_append h0070c16 ( checkBlock_append h0070c17 (
  checkBlock_append h0070c18 ( checkBlock_append h0070c19 ( checkBlock_append h0070c20 (
  checkBlock_append h0070c21 ( checkBlock_append h0070c22 ( checkBlock_append h0070c23 (
  checkBlock_append h0070c24 ( checkBlock_append h0070c25 ( checkBlock_append h0070c26 (
  checkBlock_append h0070c27 ( checkBlock_append h0070c28 ( checkBlock_append h0070c29 (
  checkBlock_append h0070c30 ( checkBlock_append h0070c31 ( checkBlock_append h0070c32 (
  checkBlock_append h0070c33 ( checkBlock_append h0070c34 ( checkBlock_append h0070c35 (
  checkBlock_append h0070c36 ( checkBlock_append h0070c37 ( checkBlock_append h0070c38 (
  checkBlock_append h0070c39 ( checkBlock_append h0070c40 ( checkBlock_append h0070c41 (
  checkBlock_append h0070c42 ( checkBlock_append h0070c43 ( checkBlock_append h0070c44 (
  checkBlock_append h0070c45 ( checkBlock_append h0070c46 ( checkBlock_append h0070c47 (
  checkBlock_append h0070c48 ( checkBlock_append h0070c49 ( checkBlock_append h0070c50 (
  checkBlock_append h0070c51 ( checkBlock_append h0070c52 ( checkBlock_append h0070c53 (
  checkBlock_append h0070c54 ( checkBlock_append h0070c55 ( checkBlock_append h0070c56 (
  checkBlock_append h0070c57 ( checkBlock_append h0070c58 ( checkBlock_append h0070c59 (
  checkBlock_append h0070c60 ( checkBlock_append h0070c61 ( checkBlock_append h0070c62 ( h0070c63
  )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
end D5.S3.Arith.PrimitiveRoot.SmallPrimes
