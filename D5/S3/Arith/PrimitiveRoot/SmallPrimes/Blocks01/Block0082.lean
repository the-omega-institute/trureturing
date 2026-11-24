/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0082
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0082.checked0082
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table013
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table015
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table019
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table026
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table041
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table042
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table091

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0082c00 : List Row := [
  .c 191, .c 13, .c 3, .p pv3 [pv2,pv83969], .c 5, .c 3, .c 11, .c 23, .c 3, .c 5, .c 109, .c 3,
  .c 47, .c 373, .c 3, .p pv3 [pv2,pv7,pv2999], .p pv3 [pv2,pv3,pv37321], .c 3, .c 7, .c 5, .c 3,
  .c 17, .p pv37 [pv2,pv3,pv5,pv7,pv457], .c 3, .c 5, .c 7, .c 3, .c 13, .c 11, .c 3, .c 23,
  .c 37, .c 3, .c 463, .c 5, .c 3, .c 73, .c 19, .c 3, .c 5, .c 13, .c 3,
  .p pv23 [pv2,pv5,pv23,pv127], .c 59, .c 3, .p pv2 [pv2,pv11,pv15269], .c 7, .c 3, .c 29, .c 5,
  .c 3, .c 293, .p pv11 [pv2,pv3,pv5,pv1493], .c 3, .c 5, .c 17, .c 3, .c 89, .c 31, .c 3, .c 7,
  .c 11, .c 3, .c 71, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv163,pv229], .c 3,
  .c 11, .p pv2 [pv2,pv3,pv13,pv59,pv73], .c 3, .c 19, .c 23, .c 3, .p pv5 [pv2,pv7,pv11,pv4363],
  .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv22397], .c 3, .c 5, .p pv31 [pv2,pv3,pv7,pv19,pv421],
  .c 3, .p pv11 [pv2,pv5,pv37,pv227], .c 7, .c 3, .c 251, .c 431, .c 3, .p pv2 [pv2,pv173,pv971],
  .c 5, .c 3, .p pv2 [pv2,pv191,pv1759], .p pv23 [pv2,pv3,pv5,pv3733], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv10181], .c 3, .c 7, .c 101, .c 3, .c 11, .c 17, .c 3, .c 761, .c 5, .c 3,
  .p pv3 [pv2,pv11,pv23,pv83], .p pv2 [pv2,pv3,pv5,pv13,pv1723], .c 3, .c 5, .c 367, .c 3,
  .p pv2 [pv2,pv5,pv33599], .c 13, .c 3, .c 31, .c 569, .c 3, .c 7, .c 5, .c 3,
  .p pv11 [pv2,pv335999], .c 11,
]
private theorem h0082c00 : checkBlock 671747 128 b0082c00 = true := by
  decide +kernel

private def b0082c01 : List Row := [
  .c 3, .c 5, .c 7, .c 3, .c 19, .c 467, .c 3, .c 29, .p pv2 [pv2,pv3,pv31,pv3613], .c 3, .c 11,
  .c 5, .c 3, .p pv2 [pv2,pv7,pv24001], .c 37, .c 3, .c 5, .c 23, .c 3,
  .p pv7 [pv2,pv5,pv53,pv317], .p pv7 [pv2,pv3,pv7,pv16001], .c 3, .c 43, .c 7, .c 3, .c 47, .c 5,
  .c 3, .p pv2 [pv2,pv336029], .c 13, .c 3, .c 5, .c 11, .c 3, .c 311,
  .p pv5 [pv2,pv3,pv41,pv683], .c 3, .c 7, .p pv3 [pv2,pv3,pv11,pv17,pv599], .c 3, .c 23, .c 5,
  .c 3, .c 11, .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv7001], .c 3, .c 151, .p pv19 [pv2,pv3,pv37339],
  .c 3, .p pv2 [pv2,pv19,pv23,pv769], .c 439, .c 3, .c 13, .c 5, .c 3, .c 7, .c 397, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv13,pv1231], .c 3, .p pv2 [pv2,pv5,pv67213], .c 7, .c 3,
  .p pv3 [pv2,pv84017], .c 13, .c 3, .p pv5 [pv2,pv31,pv37,pv293], .c 5, .c 3, .c 241,
  .p pv3 [pv2,pv3,pv5,pv4481], .c 3, .c 5, .c 71, .c 3, .c 7, .c 17, .c 3,
  .p pv5 [pv2,pv11,pv30553], .p pv17 [pv2,pv3,pv7,pv4001], .c 3, .c 31, .c 5, .c 3, .c 37,
  .p pv41 [pv2,pv3,pv5,pv17,pv659], .c 3, .c 5, .c 59, .c 3, .c 13, .p pv5 [pv2,pv3,pv389], .c 3,
  .c 17, .c 11, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv42013], .c 67, .c 3, .c 5, .c 7, .c 3,
  .c 11, .p pv13 [pv2,pv3,pv199,pv563], .c 3, .p pv2 [pv2,pv336113], .p pv2 [pv2,pv3,pv71,pv263],
  .c 3, .c 647, .c 5, .c 3, .c 19, .c 47, .c 3, .c 5, .c 457, .c 3, .p pv2 [pv2,pv5,pv2689],
  .c 37, .c 3, .c 73,
]
private theorem h0082c01 : checkBlock 672003 128 b0082c01 = true := by
  decide +kernel

private def b0082c02 : List Row := [
  .c 7, .c 3, .c 547, .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv22409], .c 3, .c 5, .c 19, .c 3,
  .c 61, .p pv5 [pv2,pv3,pv13,pv17], .c 3, .c 7, .p pv23 [pv2,pv3,pv47,pv149], .c 3,
  .p pv2 [pv2,pv131,pv1283], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 29, .c 3,
  .p pv17 [pv2,pv5,pv67231], .c 23, .c 3, .p pv2 [pv2,pv17,pv9887], .c 811, .c 3,
  .p pv2 [pv2,pv7,pv48023], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 421, .c 3,
  .p pv2 [pv2,pv5,pv33617], .c 7, .c 3, .c 13, .p pv2 [pv2,pv3,pv43,pv1303], .c 3, .c 11, .c 5,
  .c 3, .c 23, .c 197, .c 3, .c 5, .c 17, .c 3, .c 7, .c 13, .c 3, .p pv3 [pv2,pv84047],
  .p pv3 [pv2,pv3,pv7,pv2287], .c 3, .c 83, .c 5, .c 3, .c 509, .c 19, .c 3, .c 5, .c 11, .c 3,
  .c 17, .c 61, .c 3, .c 359, .c 641, .c 3, .c 7, .c 5, .c 3, .c 11, .c 31, .c 3, .c 5, .c 7,
  .c 3, .c 157, .c 281, .c 3, .c 149, .p pv3 [pv2,pv3,pv13,pv37,pv233], .c 3,
  .p pv2 [pv2,pv336221], .c 5, .c 3, .c 433, .c 13, .c 3, .c 5, .c 211, .c 3, .c 613, .c 11, .c 3,
  .c 19, .c 7, .c 3, .p pv3 [pv2,pv84059], .c 5, .c 3, .c 67, .c 29, .c 3, .c 5, .c 103, .c 3,
  .c 263, .p pv2 [pv2,pv3,pv56041], .c 3, .c 7, .p pv2 [pv2,pv3,pv37361], .c 3, .c 13, .c 5, .c 3,
  .c 167, .c 7, .c 3,
]
private theorem h0082c02 : checkBlock 672259 128 b0082c02 = true := by
  decide +kernel

private def b0082c03 : List Row := [
  .c 5, .c 53, .c 3, .p pv3 [pv2,pv5,pv17,pv23,pv43], .c 41, .c 3, .c 79, .c 11, .c 3, .c 137,
  .c 5, .c 3, .c 7, .c 59, .c 3, .c 5, .c 487, .c 3, .c 11, .c 7, .c 3, .p pv2 [pv2,pv277,pv607],
  .c 101, .c 3, .c 43, .c 5, .c 3, .c 257, .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv31,pv113], .c 3,
  .c 7, .c 71, .c 3, .p pv2 [pv2,pv37,pv61,pv149], .c 23, .c 3, .p pv3 [pv2,pv127,pv331], .c 5,
  .c 3, .c 461, .c 227, .c 3, .c 5, .c 13, .c 3, .c 521, .c 67, .c 3, .c 11, .c 19, .c 3, .c 7,
  .c 5, .c 3, .p pv2 [pv2,pv11,pv15287], .c 241, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv1051],
  .p pv11 [pv2,pv3,pv37369], .c 3, .c 61, .c 43, .c 3, .p pv2 [pv2,pv337,pv499], .c 5, .c 3,
  .c 13, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv112111], .c 3, .c 233, .c 17, .c 3, .c 599, .c 7,
  .c 3, .c 11, .c 5, .c 3, .c 113, .c 283, .c 3, .c 5, .c 37, .c 3, .c 163,
  .p pv3 [pv2,pv3,pv191,pv587], .c 3, .c 7, .c 107, .c 3, .c 29, .c 5, .c 3, .c 127, .c 7, .c 3,
  .c 5, .c 11, .c 3, .c 31, .c 19, .c 3, .c 13, .c 463, .c 3, .p pv5 [pv2,pv7,pv29,pv1657], .c 5,
  .c 3, .c 7, .c 89, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv8009], .c 3, .c 101, .c 7, .c 3,
  .p pv5 [pv2,pv359,pv937], .c 41,
]
private theorem h0082c03 : checkBlock 672515 128 b0082c03 = true := by
  decide +kernel

private def b0082c04 : List Row := [
  .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv43,pv7823], .p pv11 [pv2,pv3,pv5,pv11213], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv4153], .c 3, .c 7, .c 11, .c 3, .c 173, .p pv7 [pv2,pv3,pv7,pv83,pv193], .c 3,
  .p pv2 [pv2,pv13,pv113,pv229], .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv41,pv547], .c 3, .c 5,
  .p pv11 [pv2,pv3,pv107,pv131], .c 3, .c 43, .p pv5 [pv2,pv3,pv37379], .c 3,
  .p pv2 [pv2,pv7,pv11,pv17,pv257], .c 29, .c 3, .c 7, .c 5, .c 3, .c 659, .c 13, .c 3, .c 5,
  .c 7, .c 3, .c 41, .c 619, .c 3, .c 109, .c 11, .c 3, .p pv5 [pv2,pv101,pv3331], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv3433], .p pv19 [pv2,pv3,pv5,pv11,pv2039], .c 3, .c 5, .c 17, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv7,pv37,pv433], .c 3, .c 29, .c 7, .c 3, .c 13, .c 5, .c 3, .c 47,
  .p pv2 [pv2,pv3,pv5,pv2243], .c 3, .c 5, .c 43, .c 3, .c 17, .p pv5 [pv2,pv3,pv4673], .c 3,
  .c 7, .c 13, .c 3, .c 19, .c 5, .c 3, .c 89, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv2549],
  .c 3, .c 53, .p pv5 [pv2,pv3,pv19,pv5903], .c 3, .c 11, .p pv11 [pv2,pv3,pv31,pv67], .c 3,
  .p pv3 [pv2,pv7,pv61,pv197], .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv109],
  .c 3, .c 13, .c 7, .c 3, .p pv3 [pv2,pv42061], .c 17, .c 3, .p pv5 [pv2,pv336491], .c 5, .c 3,
  .c 337, .c 11, .c 3, .c 5, .c 13, .c 3, .c 7, .c 23, .c 3, .c 151, .c 71, .c 3, .c 11, .c 5,
  .c 3, .p pv7 [pv2,pv19,pv89,pv199], .c 293, .c 3, .c 5,
]
private theorem h0082c04 : checkBlock 672771 128 b0082c04 = true := by
  decide +kernel

private def b0082c05 : List Row := [
  .c 163, .c 3, .c 229, .c 149, .c 3, .c 19, .p pv11 [pv2,pv3,pv139,pv269], .c 3, .c 7, .c 5,
  .c 3, .c 13, .c 449, .c 3, .c 5, .c 7, .c 3, .c 29, .p pv3 [pv2,pv3,pv13,pv8629], .c 3, .c 37,
  .p pv2 [pv2,pv3,pv11,pv5099], .c 3, .p pv3 [pv2,pv23,pv31,pv59], .c 5, .c 3, .c 11, .c 17, .c 3,
  .c 5, .c 47, .c 3, .p pv2 [pv2,pv5,pv11,pv29,pv211], .p pv5 [pv2,pv3,pv7,pv2671], .c 3, .c 41,
  .c 7, .c 3, .c 31, .c 5, .c 3, .p pv2 [pv2,pv168277], .p pv3 [pv2,pv3,pv5,pv277], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv56093], .c 3, .p pv3 [pv2,pv5,pv7,pv601], .c 11, .c 3, .c 7,
  .p pv29 [pv2,pv3,pv9349], .c 3, .c 73, .c 5, .c 3, .c 181, .c 7, .c 3, .c 5, .c 617, .c 3,
  .c 19, .c 13, .c 3, .p pv2 [pv2,pv11,pv15299], .c 79, .c 3, .c 607, .c 5, .c 3, .c 7, .c 353,
  .c 3, .c 5, .c 29, .c 3, .c 47, .c 7, .c 3, .c 23, .c 11, .c 3, .p pv3 [pv2,pv13,pv6473], .c 5,
  .c 3, .p pv7 [pv2,pv336599], .p pv23 [pv2,pv3,pv5,pv11,pv17], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv29,pv53,pv73], .c 3, .c 7, .c 83, .c 3, .c 17, .c 179, .c 3,
  .p pv5 [pv2,pv11,pv71,pv431], .c 5, .c 3, .c 739, .c 13, .c 3, .c 5, .c 223, .c 3,
  .p pv3 [pv2,pv5,pv16831], .c 653, .c 3, .p pv5 [pv2,pv7,pv19,pv2531], .c 59, .c 3, .c 7, .c 5,
  .c 3, .c 53, .c 41, .c 3, .c 5, .c 7, .c 3, .p pv11 [pv2,pv5,pv13,pv5179],
  .p pv5 [pv2,pv3,pv1039], .c 3, .c 11, .c 23, .c 3,
]
private theorem h0082c05 : checkBlock 673027 128 b0082c05 = true := by
  decide +kernel

private def b0082c06 : List Row := [
  .c 13, .c 5, .c 3, .c 31, .p pv2 [pv2,pv3,pv5,pv7481], .c 3, .c 5, .p pv17 [pv2,pv3,pv13,pv83],
  .c 3, .c 211, .c 19, .c 3, .c 269, .c 7, .c 3, .p pv3 [pv2,pv53,pv397], .c 5, .c 3, .c 17,
  .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv37,pv337], .c 3, .c 149, .c 419, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv112223], .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv13,pv23,pv563], .c 7, .c 3,
  .c 5, .c 547, .c 3, .c 13, .c 37, .c 3, .c 59, .c 47, .c 3, .c 157, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv29,pv43], .c 3, .c 5, .c 11, .c 3, .p pv29 [pv2,pv5,pv67339], .c 7, .c 3,
  .p pv2 [pv2,pv79,pv2131], .p pv3 [pv2,pv3,pv11,pv19,pv179], .c 3, .p pv2 [pv2,pv109,pv3089],
  .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv22447], .c 3, .c 5, .c 19, .c 3, .c 7, .c 43, .c 3,
  .p pv5 [pv2,pv13,pv59,pv439], .p pv2 [pv2,pv3,pv7,pv8017], .c 3, .c 251, .c 5, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv5,pv23,pv61], .c 3, .c 5, .p pv11 [pv2,pv3,pv112241], .c 3,
  .p pv2 [pv2,pv5,pv13469], .c 11, .c 3, .p pv5 [pv2,pv7,pv859], .p pv2 [pv2,pv3,pv107,pv1049],
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv101,pv1667], .c 53, .c 3, .c 5, .c 7, .c 3, .c 127,
  .c 379, .c 3, .p pv5 [pv2,pv11,pv23], .c 17, .c 3, .c 19, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv73,pv659], .c 61, .c 3, .c 5, .c 41, .c 3, .c 37,
  .p pv5 [pv2,pv3,pv7,pv19,pv211], .c 3, .c 13, .c 7, .c 3, .c 17, .c 5, .c 3,
  .p pv3 [pv2,pv84191], .c 19, .c 3, .c 5, .c 31,
]
private theorem h0082c06 : checkBlock 673283 128 b0082c06 = true := by
  decide +kernel

private def b0082c07 : List Row := [
  .c 3, .c 11, .c 13, .c 3, .c 7, .p pv11 [pv2,pv3,pv37,pv41], .c 3, .p pv3 [pv2,pv11,pv43,pv89],
  .c 5, .c 3, .c 661, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv112261], .c 3, .c 73,
  .p pv2 [pv2,pv3,pv56131], .c 3, .c 53, .p pv3 [pv2,pv3,pv23,pv1627], .c 3, .c 29, .c 5, .c 3,
  .c 7, .c 17, .c 3, .c 5, .c 257, .c 3, .c 23, .c 7, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv13,pv17,pv127], .c 3, .p pv2 [pv2,pv29,pv5807], .c 5, .c 3,
  .p pv2 [pv2,pv11,pv67,pv457], .c 13, .c 3, .c 5, .c 733, .c 3, .c 7, .c 79, .c 3,
  .p pv2 [pv2,pv168409], .p pv3 [pv2,pv3,pv7,pv43,pv373], .c 3, .p pv2 [pv2,pv17,pv19813], .c 5,
  .c 3, .p pv3 [pv2,pv71,pv593], .c 11, .c 3, .c 5, .c 191, .c 3, .c 31, .c 337, .c 3,
  .p pv2 [pv2,pv7,pv48119], .p pv2 [pv2,pv3,pv18713], .c 3, .c 7, .c 5, .c 3, .c 163, .c 43, .c 3,
  .c 5, .c 7, .c 3, .c 641, .c 17, .c 3, .c 383, .c 13, .c 3, .c 719, .c 5, .c 3, .c 397, .c 83,
  .c 3, .c 5, .c 11, .c 3, .c 19, .c 31, .c 3, .c 17, .c 7, .c 3, .c 37, .c 5, .c 3, .c 11,
  .c 239, .c 3, .c 5, .p pv2 [pv2,pv3,pv112291], .c 3, .c 13, .c 41, .c 3, .c 7, .c 19, .c 3,
  .c 193, .c 5, .c 3, .p pv3 [pv2,pv84221], .c 7, .c 3, .c 5, .c 13, .c 3,
  .p pv2 [pv2,pv5,pv59,pv571], .c 11, .c 3, .p pv2 [pv2,pv29,pv11617], .c 53, .c 3,
  .p pv3 [pv2,pv7,pv47],
]
private theorem h0082c07 : checkBlock 673539 128 b0082c07 = true := by
  decide +kernel

private def b0082c08 : List Row := [
  .c 5, .c 3, .c 7, .p pv29 [pv2,pv3,pv5,pv1123], .c 3, .c 5, .c 37, .c 3,
  .p pv2 [pv2,pv5,pv43,pv1567], .c 7, .c 3, .p pv3 [pv2,pv11,pv13,pv19,pv31], .c 67, .c 3, .c 283,
  .c 5, .c 3, .c 13, .c 23, .c 3, .c 5, .p pv2 [pv2,pv3,pv233,pv241], .c 3, .c 7, .c 359, .c 3,
  .c 31, .c 11, .c 3, .c 43, .c 5, .c 3, .c 97, .c 71, .c 3, .c 5, .c 61, .c 3, .c 11, .c 19,
  .c 3, .c 23, .p pv3 [pv2,pv3,pv31,pv3623], .c 3, .c 7, .c 5, .c 3, .c 313,
  .p pv2 [pv2,pv3,pv5,pv7,pv3209], .c 3, .c 5, .c 7, .c 3, .c 743, .c 137, .c 3, .c 13, .c 31,
  .c 3, .c 151, .c 5, .c 3, .c 349, .p pv7 [pv2,pv3,pv5,pv13], .c 3, .c 5, .c 149, .c 3, .c 17,
  .c 13, .c 3, .c 11, .c 7, .c 3, .p pv5 [pv2,pv317,pv1063], .c 5, .c 3, .c 19,
  .p pv11 [pv2,pv3,pv5,pv4493], .c 3, .c 5, .c 59, .c 3, .p pv3 [pv2,pv5,pv7,pv29,pv83], .c 227,
  .c 3, .c 7, .c 23, .c 3, .c 101, .c 5, .c 3, .p pv2 [pv2,pv336989], .c 7, .c 3, .c 5, .c 19,
  .c 3, .p pv13 [pv2,pv5,pv67399], .c 107, .c 3, .c 89, .c 17, .c 3, .c 11, .c 5, .c 3, .c 7,
  .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv17,pv59], .c 3, .c 421, .c 7, .c 3, .c 47, .c 37, .c 3,
  .c 17, .c 5, .c 3, .c 191, .c 821, .c 3, .c 5, .c 11, .c 3,
]
private theorem h0082c08 : checkBlock 673795 128 b0082c08 = true := by
  decide +kernel

private def b0082c09 : List Row := [
  .c 7, .c 97, .c 3, .p pv3 [pv2,pv109,pv773], .p pv2 [pv2,pv3,pv7,pv11,pv1459], .c 3, .c 13,
  .c 5, .c 3, .c 11, .p pv37 [pv2,pv3,pv5,pv22469], .c 3, .c 5, .c 241, .c 3, .c 41,
  .p pv2 [pv2,pv3,pv19,pv73], .c 3, .c 67, .c 13, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv337049],
  .c 17, .c 3, .c 5, .c 7, .c 3, .c 43, .c 11, .c 3, .p pv2 [pv2,pv127,pv1327], .c 281, .c 3,
  .p pv2 [pv2,pv41,pv8221], .c 5, .c 3, .c 223, .p pv2 [pv2,pv3,pv5,pv23,pv977], .c 3, .c 5,
  .c 389, .c 3, .c 13, .c 491, .c 3, .c 523, .c 7, .c 3, .c 23, .c 5, .c 3,
  .p pv13 [pv2,pv19,pv113,pv157], .p pv7 [pv2,pv3,pv5,pv53], .c 3, .c 5, .c 13, .c 3, .c 419,
  .p pv2 [pv2,pv3,pv61,pv307], .c 3, .c 7, .c 11, .c 3, .p pv5 [pv2,pv337091], .c 5, .c 3,
  .p pv2 [pv2,pv31,pv5437], .c 7, .c 3, .c 5, .c 43, .c 3, .c 11, .c 17, .c 3, .c 107, .c 83,
  .c 3, .c 53, .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .p pv7 [pv2,pv3,pv7,pv5351], .c 3,
  .p pv17 [pv2,pv5,pv191,pv353], .c 7, .c 3, .c 17, .p pv3 [pv2,pv3,pv103,pv1091], .c 3, .c 127,
  .c 5, .c 3, .p pv3 [pv2,pv271,pv311], .c 37, .c 3, .c 5, .c 131, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv47,pv797], .c 3, .c 11, .p pv2 [pv2,pv3,pv7,pv23,pv349], .c 3,
  .p pv3 [pv2,pv19,pv1109], .c 5, .c 3, .c 29, .c 31, .c 3, .c 5, .c 71, .c 3, .c 19, .c 179,
  .c 3, .c 13, .p pv3 [pv2,pv3,pv12487], .c 3, .c 7, .c 5,
]
private theorem h0082c09 : checkBlock 674051 128 b0082c09 = true := by
  decide +kernel

private def b0082c10 : List Row := [
  .c 3, .c 47, .c 11, .c 3, .c 5, .c 7, .c 3, .p pv11 [pv2,pv5,pv8429], .c 13, .c 3, .c 41, .c 19,
  .c 3, .c 11, .c 5, .c 3, .c 17, .c 103, .c 3, .c 5, .p pv2 [pv2,pv3,pv167,pv673], .c 3, .c 571,
  .c 89, .c 3, .p pv3 [pv2,pv17,pv47,pv211], .c 7, .c 3, .p pv2 [pv2,pv13,pv37,pv701], .c 5, .c 3,
  .c 43, .p pv3 [pv2,pv3,pv5,pv59,pv127], .c 3, .c 5, .c 11, .c 3, .c 617, .c 23, .c 3, .c 7,
  .c 283, .c 3, .p pv3 [pv2,pv84299], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 17, .c 3, .c 199,
  .c 769, .c 3, .c 227, .p pv7 [pv2,pv3,pv112403], .c 3, .c 79, .c 5, .c 3, .c 7,
  .p pv17 [pv2,pv3,pv5,pv22481], .c 3, .c 5, .c 251, .c 3, .c 17, .c 7, .c 3, .c 73,
  .p pv7 [pv2,pv3,pv14051], .c 3, .c 13, .c 5, .c 3, .c 787, .p pv13 [pv2,pv3,pv5,pv1249], .c 3,
  .c 5, .c 31, .c 3, .c 7, .c 37, .c 3, .c 61, .c 13, .c 3, .p pv2 [pv2,pv29,pv401], .c 5, .c 3,
  .c 67, .c 41, .c 3, .c 5, .c 47, .c 3, .p pv2 [pv2,pv5,pv19,pv71], .c 397, .c 3, .c 643, .c 11,
  .c 3, .c 7, .c 5, .c 3, .c 19, .c 23, .c 3, .c 5, .c 7, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv41,pv457], .c 3, .p pv3 [pv2,pv84317], .c 631, .c 3, .c 17, .c 5, .c 3,
  .c 653, .p pv11 [pv2,pv3,pv5,pv1499], .c 3, .c 5, .c 13, .c 3, .c 359,
]
private theorem h0082c10 : checkBlock 674307 128 b0082c10 = true := by
  decide +kernel

private def b0082c11 : List Row := [
  .p pv2 [pv2,pv3,pv7,pv16061], .c 3, .c 23, .c 7, .c 3, .c 41, .c 5, .c 3, .c 101, .c 79, .c 3,
  .c 5, .c 181, .c 3, .c 31, .c 73, .c 3, .c 7, .c 61, .c 3, .p pv2 [pv2,pv337301], .c 5, .c 3,
  .c 13, .c 7, .c 3, .c 5, .c 349, .c 3, .c 37, .c 67, .c 3, .c 29, .c 157, .c 3, .c 19, .c 5,
  .c 3, .c 7, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv16063], .c 3, .c 179, .c 7, .c 3, .c 163,
  .c 23, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv151,pv1117], .c 19, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv6247], .c 3, .c 7, .p pv5 [pv2,pv3,pv23,pv4889], .c 3, .c 13, .c 443, .c 3,
  .p pv2 [pv2,pv168673], .c 5, .c 3, .p pv2 [pv2,pv337349], .p pv127 [pv2,pv3,pv5,pv13,pv173],
  .c 3, .c 5, .c 11, .c 3, .p pv23 [pv2,pv5,pv109,pv619], .c 13, .c 3, .p pv2 [pv2,pv7,pv24097],
  .p pv3 [pv2,pv3,pv11,pv10223], .c 3, .c 7, .c 5, .c 3, .c 11, .p pv13 [pv2,pv3,pv5,pv7,pv17],
  .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv11,pv3067], .c 29, .c 3, .c 17,
  .p pv7 [pv2,pv3,pv18743], .c 3, .c 103, .c 5, .c 3, .p pv7 [pv2,pv7,pv48197],
  .p pv11 [pv2,pv3,pv5,pv5623], .c 3, .c 5, .p pv3 [pv2,pv3,pv19,pv1973], .c 3,
  .p pv11 [pv2,pv5,pv67477], .c 11, .c 3, .c 31, .c 7, .c 3, .c 59, .c 5, .c 3,
  .p pv2 [pv2,pv168697], .c 13, .c 3, .c 5, .c 23, .c 3, .c 29, .c 191, .c 3, .c 7, .c 199, .c 3,
  .p pv2 [pv2,pv73,pv2311], .c 5, .c 3,
]
private theorem h0082c11 : checkBlock 674563 128 b0082c11 = true := by
  decide +kernel

private def b0082c12 : List Row := [
  .c 41, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv47,pv2393], .c 3, .p pv41 [pv2,pv5,pv13,pv29,pv179],
  .p pv7 [pv2,pv3,pv17,pv827], .c 3, .p pv2 [pv2,pv113,pv1493], .c 11, .c 3, .c 13, .c 5, .c 3,
  .c 7, .p pv3 [pv2,pv3,pv5,pv11,pv409], .c 3, .c 5, .p pv11 [pv2,pv3,pv7,pv13,pv103], .c 3,
  .c 11, .c 7, .c 3, .p pv2 [pv2,pv17,pv23,pv863], .c 13, .c 3, .c 47, .c 5, .c 3,
  .p pv7 [pv2,pv127,pv2657], .c 661, .c 3, .c 5, .c 89, .c 3, .c 7, .c 317, .c 3, .c 79, .c 19,
  .c 3, .p pv5 [pv2,pv53,pv6367], .c 5, .c 3, .c 331, .c 479, .c 3, .c 5, .c 17, .c 3, .c 13,
  .c 601, .c 3, .c 11, .p pv7 [pv2,pv3,pv43,pv109], .c 3, .c 7, .c 5, .c 3, .c 251,
  .p pv13 [pv2,pv3,pv5,pv7,pv1607], .c 3, .c 5, .c 7, .c 3, .c 17, .p pv5 [pv2,pv3,pv28123], .c 3,
  .p pv2 [pv2,pv19,pv83,pv107], .c 103, .c 3, .c 31, .c 5, .c 3, .c 677, .c 11, .c 3, .c 5,
  .p pv19 [pv2,pv3,pv79,pv89], .c 3, .c 23, .c 41, .c 3, .p pv2 [pv2,pv13,pv1997], .c 7, .c 3,
  .c 11, .c 5, .c 3, .c 13, .c 233, .c 3, .c 5, .c 761, .c 3, .c 337, .c 19, .c 3, .c 7, .c 17,
  .c 3, .c 97, .c 5, .c 3, .p pv2 [pv2,pv37,pv4561], .c 7, .c 3, .c 5, .c 11, .c 3, .c 241,
  .c 131, .c 3, .c 433, .c 277, .c 3, .c 17, .c 5, .c 3, .c 7, .c 47, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv16073], .c 3, .p pv11 [pv2,pv5,pv11,pv17,pv19], .c 7,
]
private theorem h0082c12 : checkBlock 674819 128 b0082c12 = true := by
  decide +kernel

private def b0082c13 : List Row := [
  .c 3, .c 13, .p pv3 [pv2,pv3,pv59,pv1907], .c 3, .p pv2 [pv2,pv337541], .c 5, .c 3, .c 19,
  .c 29, .c 3, .c 5, .p pv7 [pv2,pv3,pv23,pv1223], .c 3, .c 7, .c 11, .c 3, .c 691,
  .p pv2 [pv2,pv3,pv7,pv19,pv47], .c 3, .p pv3 [pv2,pv84389], .c 5, .c 3, .c 23, .c 17, .c 3,
  .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv181,pv373], .p pv2 [pv2,pv3,pv127,pv443], .c 3, .c 59,
  .c 37, .c 3, .c 7, .c 5, .c 3, .c 29, .p pv3 [pv2,pv3,pv5,pv7,pv643], .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv16879], .p pv3 [pv2,pv3,pv12503], .c 3, .c 53, .c 11, .c 3,
  .p pv2 [pv2,pv17,pv9929], .c 5, .c 3, .p pv2 [pv2,pv7,pv29,pv1663], .c 13, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv43,pv2617], .c 3, .c 11, .c 523, .c 3, .p pv2 [pv2,pv59,pv2861], .c 7, .c 3,
  .c 19, .c 5, .c 3, .c 61, .c 23, .c 3, .c 5, .c 97, .c 3, .p pv3 [pv2,pv5,pv7,pv13,pv53], .c 17,
  .c 3, .c 7, .c 41, .c 3, .c 13, .c 5, .c 3, .p pv11 [pv2,pv283,pv1193], .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv13,pv787], .c 3, .p pv11 [pv2,pv5,pv37,pv73], .p pv11 [pv2,pv3,pv18757],
  .c 3, .c 11, .c 13, .c 3, .p pv5 [pv2,pv7,pv139,pv347], .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv41,pv61], .c 3, .c 5, .c 107, .c 3, .c 71, .c 7, .c 3, .c 37, .c 353,
  .c 3, .c 67, .c 5, .c 3, .p pv2 [pv2,pv13,pv19,pv1367], .c 11, .c 3, .c 5, .c 193, .c 3, .c 7,
  .p pv17 [pv2,pv3,pv11,pv1279], .c 3, .c 19, .p pv23 [pv2,pv3,pv7,pv2297], .c 3, .c 11, .c 5,
  .c 3, .c 619,
]
private theorem h0082c13 : checkBlock 675075 128 b0082c13 = true := by
  decide +kernel

private def b0082c14 : List Row := [
  .c 61, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv33767], .c 47, .c 3, .p pv2 [pv2,pv7,pv48239],
  .c 23, .c 3, .c 7, .c 5, .c 3, .c 17, .c 37, .c 3, .c 5, .c 7, .c 3, .c 79, .c 59, .c 3, .c 431,
  .c 53, .c 3, .c 727, .c 5, .c 3, .c 11, .p pv29 [pv2,pv3,pv5,pv47,pv479], .c 3, .c 5, .c 31,
  .c 3, .c 43, .c 569, .c 3, .p pv5 [pv2,pv199,pv1697], .c 7, .c 3, .p pv2 [pv2,pv19,pv8887],
  .c 5, .c 3, .p pv2 [pv2,pv23,pv14683], .c 89, .c 3, .c 5, .c 17, .c 3, .c 19, .c 11, .c 3, .c 7,
  .c 29, .c 3, .c 509, .c 5, .c 3, .p pv3 [pv2,pv84431], .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv1759], .c 3, .c 17, .p pv3 [pv2,pv3,pv112577], .c 3, .c 13, .c 19, .c 3,
  .c 109, .c 5, .c 3, .c 7, .p pv19 [pv2,pv3,pv5,pv13,pv433], .c 3, .c 5, .c 23, .c 3, .c 59,
  .c 7, .c 3, .c 29, .c 11, .c 3, .c 373, .c 5, .c 3, .c 37, .p pv7 [pv2,pv3,pv5,pv11,pv23,pv89],
  .c 3, .c 5, .c 463, .c 3, .c 7, .c 241, .c 3, .c 317, .c 17, .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv53,pv6373], .p pv2 [pv2,pv3,pv5,pv139], .c 3, .c 5, .c 137, .c 3,
  .p pv13 [pv2,pv5,pv59,pv229], .p pv11 [pv2,pv3,pv31,pv227], .c 3, .c 41,
  .p pv3 [pv2,pv3,pv13,pv2887], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv42223], .c 13, .c 3, .c 5,
  .c 7, .c 3, .p pv3 [pv2,pv5,pv17,pv1987], .c 19, .c 3,
]
private theorem h0082c14 : checkBlock 675331 128 b0082c14 = true := by
  decide +kernel

private def b0082c15 : List Row := [
  .c 11, .c 101, .c 3, .p pv3 [pv2,pv84449], .c 5, .c 3, .c 89, .p pv29 [pv2,pv3,pv5,pv563], .c 3,
  .c 5, .p pv3 [pv2,pv3,pv112601], .c 3, .p pv2 [pv2,pv5,pv13,pv5197], .c 29, .c 3,
  .p pv3 [pv2,pv43,pv491], .c 7, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv67,pv2521], .c 11, .c 3,
  .c 5, .c 587, .c 3, .c 557, .p pv2 [pv2,pv3,pv11,pv29,pv353], .c 3, .c 7, .c 13, .c 3, .c 11,
  .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 577, .c 3, .c 23, .c 181, .c 3, .c 709, .c 139, .c 3,
  .c 821, .c 5, .c 3, .c 7, .c 109, .c 3, .c 5, .c 11, .c 3, .c 13, .c 7, .c 3, .c 31, .c 541,
  .c 3, .p pv3 [pv2,pv5279], .c 5, .c 3, .c 11, .c 41, .c 3, .c 5, .c 13, .c 3, .c 7, .c 17, .c 3,
  .c 521, .p pv2 [pv2,pv3,pv7,pv31,pv173], .c 3, .p pv5 [pv2,pv337871], .c 5, .c 3, .c 467,
  .p pv3 [pv2,pv3,pv5,pv17,pv53], .c 3, .c 5, .c 379, .c 3, .c 73, .c 11, .c 3, .c 17, .c 31,
  .c 3, .c 7, .c 5, .c 3, .c 13, .p pv17 [pv2,pv3,pv5,pv7,pv1609], .c 3, .c 5, .c 7, .c 3, .c 101,
  .c 643, .c 3, .p pv2 [pv2,pv11,pv15359], .c 97, .c 3, .c 41, .c 5, .c 3, .c 23, .c 19, .c 3,
  .c 5, .p pv31 [pv2,pv3,pv29,pv971], .c 3, .c 137, .p pv7 [pv2,pv3,pv7,pv16091], .c 3,
  .p pv2 [pv2,pv461,pv733], .c 7, .c 3, .c 211, .c 5, .c 3, .p pv13 [pv2,pv337919],
  .p pv7 [pv2,pv3,pv5,pv11],
]
private theorem h0082c15 : checkBlock 675587 128 b0082c15 = true := by
  decide +kernel

private def b0082c16 : List Row := [
  .c 3, .c 5, .c 419, .c 3, .c 11, .c 113, .c 3, .c 7, .p pv13 [pv2,pv3,pv112643], .c 3,
  .p pv5 [pv2,pv11,pv31,pv991], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv151,pv373],
  .c 3, .p pv3 [pv2,pv5,pv61,pv277], .c 13, .c 3, .c 19, .p pv13 [pv2,pv3,pv14081], .c 3, .c 31,
  .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 47, .c 3, .c 173, .c 7, .c 3, .c 11, .c 107, .c 3,
  .p pv2 [pv2,pv13,pv25997], .c 5, .c 3, .p pv3 [pv2,pv11,pv7681], .p pv2 [pv2,pv3,pv5,pv22531],
  .c 3, .c 5, .c 17, .c 3, .c 7, .c 251, .c 3, .c 23, .c 191, .c 3, .c 37, .c 5, .c 3,
  .p pv7 [pv2,pv137,pv2467], .c 11, .c 3, .c 5, .c 41, .c 3, .c 17, .p pv5 [pv2,pv3,pv11,pv569],
  .c 3, .p pv3 [pv2,pv7,pv12071], .p pv2 [pv2,pv3,pv112663], .c 3, .c 7, .c 5, .c 3, .c 103,
  .c 71, .c 3, .c 5, .c 7, .c 3, .c 19, .c 43, .c 3, .p pv5 [pv2,pv227,pv1489],
  .p pv7 [pv2,pv3,pv41,pv229], .c 3, .c 13, .c 5, .c 3, .c 29, .c 127, .c 3, .c 5, .c 11, .c 3,
  .p pv11 [pv2,pv5,pv67,pv1009], .c 787, .c 3, .p pv2 [pv2,pv169009], .c 7, .c 3,
  .p pv2 [pv2,pv157,pv2153], .c 5, .c 3, .c 11, .p pv17 [pv2,pv3,pv5,pv4507], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv17,pv1657], .c 3, .p pv2 [pv2,pv5,pv7,pv11,pv439], .c 61, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv53,pv1063], .c 3, .c 17, .c 5, .c 3, .c 31, .c 7, .c 3, .c 5, .c 283, .c 3,
  .c 13, .c 11, .c 3, .c 67,
]
private theorem h0082c16 : checkBlock 675843 128 b0082c16 = true := by
  decide +kernel

private def b0082c17 : List Row := [
  .p pv2 [pv2,pv3,pv37561], .c 3, .p pv5 [pv2,pv7,pv6899], .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv31,pv727], .c 3, .c 5, .c 13, .c 3, .c 53, .c 7, .c 3, .c 109,
  .p pv7 [pv2,pv3,pv7043], .c 3, .c 71, .c 5, .c 3, .c 613, .c 17, .c 3, .c 5,
  .p pv29 [pv2,pv3,pv112691], .c 3, .c 7, .c 19, .c 3, .c 277, .c 11, .c 3, .c 563, .c 5, .c 3,
  .c 13, .p pv3 [pv2,pv3,pv5,pv11,pv683], .c 3, .c 5, .c 23, .c 3, .c 11, .c 167, .c 3, .c 97,
  .c 47, .c 3, .c 7, .c 5, .c 3, .c 59, .c 83, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv19,pv3559], .c 41, .c 3, .p pv3 [pv2,pv181,pv467],
  .p pv3 [pv2,pv3,pv43,pv2621], .c 3, .c 23, .c 5, .c 3, .c 19, .c 67, .c 3, .c 5, .c 229, .c 3,
  .p pv3 [pv2,pv5,pv79,pv107], .c 17, .c 3, .c 11, .c 7, .c 3, .p pv2 [pv2,pv169063], .c 5, .c 3,
  .p pv2 [pv2,pv11,pv59,pv521], .c 43, .c 3, .c 5, .c 19, .c 3, .c 599, .c 13, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv37571], .c 3, .c 47, .c 5, .c 3, .p pv3 [pv2,pv10567], .c 7, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv31,pv101], .c 3, .c 197, .c 347, .c 3, .c 61, .c 29, .c 3, .c 11, .c 5, .c 3,
  .c 7, .c 307, .c 3, .c 5, .c 31, .c 3, .c 191, .c 7, .c 3, .p pv3 [pv2,pv41,pv1031],
  .p pv3 [pv2,pv3,pv13,pv23,pv29], .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv353,pv479], .c 13, .c 3,
]
private theorem h0082c17 : checkBlock 676099 128 b0082c17 = true := by
  decide +kernel

private def b0082c18 : List Row := [
  .c 5, .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv17,pv19,pv349], .c 3, .c 29, .c 137, .c 3,
  .p pv2 [pv2,pv169093], .c 5, .c 3, .c 11, .c 19, .c 3, .c 5, .p pv2 [pv2,pv3,pv53,pv709], .c 3,
  .p pv7 [pv2,pv5,pv11,pv13,pv43], .c 313, .c 3, .c 37, .c 233, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv84551], .p pv2 [pv2,pv3,pv5,pv7,pv3221], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv31,pv1091], .c 11, .c 3, .p pv2 [pv2,pv338213], .c 13, .c 3, .c 43, .c 5,
  .c 3, .c 53, .c 179, .c 3, .c 5, .c 17, .c 3, .c 31, .c 23, .c 3, .c 19, .c 7, .c 3,
  .p pv5 [pv2,pv338231], .c 5, .c 3, .p pv2 [pv2,pv13,pv13009], .c 37, .c 3, .c 5, .c 79, .c 3,
  .c 13, .c 29, .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv53,pv3191], .c 5, .c 3, .c 23, .c 7, .c 3,
  .c 5, .c 13, .c 3, .c 11, .c 31, .c 3, .c 167, .c 43, .c 3, .p pv2 [pv2,pv7,pv11,pv23,pv191],
  .c 5, .c 3, .c 7, .c 113, .c 3, .c 5, .c 293, .c 3, .c 29, .c 7, .c 3, .c 421, .c 17, .c 3,
  .c 59, .c 5, .c 3, .c 13, .c 107, .c 3, .c 5, .c 619, .c 3, .c 7, .p pv2 [pv2,pv3,pv13,pv4337],
  .c 3, .c 11, .c 719, .c 3, .c 17, .c 5, .c 3, .p pv3 [pv2,pv11,pv15377], .c 23, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv56383], .c 3, .p pv3 [pv2,pv5,pv17,pv199], .c 173, .c 3, .c 103, .c 19,
]
private theorem h0082c18 : checkBlock 676355 128 b0082c18 = true := by
  decide +kernel

private def b0082c19 : List Row := [
  .c 3, .c 7, .c 5, .c 3, .c 37, .c 11, .c 3, .c 5, .c 7, .c 3, .c 151, .c 67, .c 3, .c 13,
  .c 547, .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv7,pv43,pv281], .c 17, .c 3, .c 5, .c 29, .c 3,
  .p pv3 [pv2,pv5,pv23,pv1471], .c 13, .c 3, .c 89, .c 7, .c 3, .c 61, .c 5, .c 3,
  .p pv11 [pv2,pv338339], .c 257, .c 3, .c 5, .c 11, .c 3, .c 43, .c 37, .c 3, .c 7, .c 31, .c 3,
  .p pv5 [pv2,pv13,pv17,pv1531], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv56393],
  .c 3, .p pv7 [pv2,pv5,pv11,pv769], .c 19, .c 3, .p pv5 [pv2,pv563,pv601], .c 23, .c 3,
  .p pv2 [pv2,pv7,pv24169], .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv41,pv131],
  .c 3, .p pv11 [pv2,pv5,pv2707], .c 7, .c 3, .c 53, .c 181, .c 3, .p pv2 [pv2,pv523,pv647], .c 5,
  .c 3, .c 97, .p pv3 [pv2,pv3,pv5,pv17,pv1327], .c 3, .c 5, .c 43, .c 3, .c 7, .c 73, .c 3,
  .c 17, .c 59, .c 3, .c 13, .c 5, .c 3, .c 19, .c 101, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv8677],
  .c 3, .c 587, .c 103, .c 3, .c 457, .c 11, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv41,pv4127],
  .c 29, .c 3, .c 5, .c 7, .c 3, .c 11, .c 71, .c 3, .c 47, .c 617, .c 3, .c 683, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv13,pv3719], .p pv2 [pv2,pv3,pv5,pv29,pv389], .c 3, .c 5,
]
private theorem h0082c19 : checkBlock 676611 128 b0082c19 = true := by
  decide +kernel

private def b0082c20 : List Row := [
  .c 23, .c 3, .c 13, .c 743, .c 3, .c 131, .c 7, .c 3, .p pv2 [pv2,pv107,pv3163], .c 5, .c 3,
  .c 17, .p pv2 [pv2,pv3,pv5,pv23,pv109], .c 3, .c 5, .c 13, .c 3, .c 67,
  .p pv3 [pv2,pv3,pv101,pv1117], .c 3, .c 7, .p pv2 [pv2,pv3,pv18803], .c 3, .c 19, .c 5, .c 3,
  .p pv11 [pv2,pv11,pv29,pv1061], .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv37607], .c 3,
  .p pv2 [pv2,pv5,pv139,pv487], .c 151, .c 3, .p pv3 [pv2,pv13,pv23,pv283], .c 163, .c 3,
  .p pv7 [pv2,pv7,pv48353], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 17, .c 3,
  .p pv3 [pv2,pv5,pv4231], .c 7, .c 3, .p pv5 [pv2,pv59,pv5737], .c 53, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv31,pv61,pv179], .p pv11 [pv2,pv3,pv5,pv3761], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv112831], .c 3, .c 7, .p pv13 [pv2,pv3,pv41,pv43], .c 3, .c 347, .c 109, .c 3,
  .c 101, .c 5, .c 3, .c 31, .p pv3 [pv2,pv3,pv5,pv22567], .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv33851], .c 89, .c 3, .c 13, .p pv43 [pv2,pv3,pv11,pv23,pv223], .c 3, .c 7,
  .c 5, .c 3, .c 11, .p pv61 [pv2,pv3,pv5,pv7,pv13,pv31], .c 3, .c 5, .c 7, .c 3, .c 23, .c 13,
  .c 3, .p pv3 [pv2,pv71,pv149], .c 17, .c 3, .c 29, .c 5, .c 3, .c 139, .c 31, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv17,pv3319], .c 3, .p pv3 [pv2,pv5,pv16927], .c 11, .c 3, .c 239, .c 7, .c 3,
  .c 17, .c 5, .c 3, .c 211, .c 431, .c 3, .c 5, .p pv2 [pv2,pv3,pv12539], .c 3,
  .p pv7 [pv2,pv5,pv7,pv17,pv569], .p pv5 [pv2,pv3,pv89,pv317], .c 3, .c 7,
  .p pv3 [pv2,pv3,pv13,pv8681], .c 3,
]
private theorem h0082c20 : checkBlock 676867 128 b0082c20 = true := by
  decide +kernel

private def b0082c21 : List Row := [
  .c 293, .c 5, .c 3, .c 47, .c 7, .c 3, .c 5, .c 37, .c 3, .c 19, .c 23, .c 3,
  .p pv2 [pv2,pv338573], .c 11, .c 3, .c 229, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv23,pv701], .c 3, .c 11, .c 7, .c 3, .p pv3 [pv2,pv47,pv1801], .c 19, .c 3,
  .c 13, .c 5, .c 3, .c 23, .c 137, .c 3, .c 5, .c 41, .c 3, .c 7, .c 107, .c 3, .c 43, .c 13,
  .c 3, .p pv2 [pv2,pv17,pv23,pv433], .c 5, .c 3, .c 283, .c 73, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv31,pv331], .c 3, .p pv7 [pv2,pv5,pv67723], .p pv5 [pv2,pv3,pv4703], .c 3,
  .c 11, .p pv17 [pv2,pv3,pv41,pv2753], .c 3, .c 7, .c 5, .c 3, .c 389, .c 223, .c 3, .c 5, .c 7,
  .c 3, .c 13, .c 17, .c 3, .c 79, .c 71, .c 3, .c 379, .c 5, .c 3, .c 41, .c 11, .c 3, .c 5,
  .c 13, .c 3, .c 127, .c 19, .c 3, .c 17, .c 7, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv169327],
  .p pv3 [pv2,pv3,pv5,pv107,pv211], .c 3, .c 5, .c 47, .c 3, .p pv3 [pv2,pv5,pv7,pv41,pv59],
  .p pv2 [pv2,pv3,pv37,pv113], .c 3, .c 7, .c 823, .c 3, .p pv2 [pv2,pv313,pv541], .c 5, .c 3,
  .c 13, .c 7, .c 3, .c 5, .c 11, .c 3, .c 97, .c 29, .c 3, .p pv2 [pv2,pv169339], .c 37, .c 3,
  .c 83, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv67,pv337], .c 3, .c 5, .c 439,
]
private theorem h0082c21 : checkBlock 677123 128 b0082c21 = true := by
  decide +kernel

private def b0082c22 : List Row := [
  .c 3, .c 31, .c 7, .c 3, .p pv2 [pv2,pv151,pv2243], .c 421, .c 3, .c 53, .c 5, .c 3, .c 17,
  .c 131, .c 3, .c 5, .c 19, .c 3, .c 7, .c 11, .c 3, .c 13, .c 23, .c 3,
  .p pv5 [pv2,pv43,pv7877], .c 5, .c 3, .c 317, .c 103, .c 3, .c 5, .c 67, .c 3,
  .p pv3 [pv2,pv5,pv29,pv73], .c 13, .c 3, .p pv5 [pv2,pv7,pv11,pv53,pv83], .c 251, .c 3, .c 7,
  .c 5, .c 3, .p pv2 [pv2,pv47,pv7207], .p pv13 [pv2,pv3,pv5,pv7,pv1613], .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv37,pv1831], .p pv17 [pv2,pv3,pv7057], .c 3, .c 191, .c 11, .c 3, .c 19, .c 5,
  .c 3, .c 769, .c 281, .c 3, .c 5, .c 59, .c 3, .c 11, .c 149, .c 3, .c 37, .c 7, .c 3, .c 73,
  .c 5, .c 3, .c 167, .c 13, .c 3, .c 5, .c 29, .c 3, .p pv2 [pv2,pv5,pv7,pv9679],
  .p pv5 [pv2,pv3,pv131,pv431], .c 3, .c 7, .p pv2 [pv2,pv3,pv12547], .c 3,
  .p pv5 [pv2,pv277,pv1223], .c 5, .c 3, .c 307, .c 7, .c 3, .c 5, .c 23, .c 3,
  .p pv3 [pv2,pv5,pv13,pv1303], .p pv2 [pv2,pv3,pv112927], .c 3, .c 11, .c 17, .c 3, .c 13, .c 5,
  .c 3, .c 7, .c 37, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv13,pv17,pv73], .c 3, .c 163, .c 7, .c 3,
  .c 19, .c 13, .c 3, .c 17, .c 5, .c 3, .c 101, .c 11, .c 3, .c 5, .c 467, .c 3, .c 7, .c 193,
  .c 3, .p pv2 [pv2,pv23,pv14731], .c 31, .c 3, .c 11,
]
private theorem h0082c22 : checkBlock 677379 128 b0082c22 = true := by
  decide +kernel

private def b0082c23 : List Row := [
  .c 5, .c 3, .p pv7 [pv2,pv13,pv67,pv389], .c 173, .c 3, .c 5, .p pv3 [pv2,pv3,pv47,pv89], .c 3,
  .c 13, .c 109, .c 3, .p pv3 [pv2,pv7,pv12101], .c 73, .c 3, .c 7, .c 5, .c 3, .c 311, .c 17,
  .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv43,pv197], .p pv3 [pv2,pv3,pv37649], .c 3,
  .p pv5 [pv2,pv167,pv2029], .c 41, .c 3, .c 47, .c 5, .c 3, .c 11, .c 29, .c 3, .c 5, .c 337,
  .c 3, .c 19, .c 409, .c 3, .p pv2 [pv2,pv13,pv13033], .c 7, .c 3, .c 43, .c 5, .c 3, .c 13,
  .c 457, .c 3, .c 5, .p pv5 [pv2,pv3,pv9413], .c 3, .c 23, .c 11, .c 3, .c 7, .c 19, .c 3, .c 31,
  .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv37,pv43,pv71], .c 3, .c 41, .c 17, .c 3,
  .c 571, .p pv2 [pv2,pv3,pv83,pv1361], .c 3, .p pv5 [pv2,pv7,pv48413], .c 5, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv5,pv17,pv443], .c 3, .c 5, .c 233, .c 3, .c 149, .c 7, .c 3, .c 13, .c 11,
  .c 3, .p pv2 [pv2,pv41,pv4133], .c 5, .c 3, .c 277, .c 521, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv37657], .c 3, .c 7, .c 13, .c 3, .c 71, .c 67, .c 3, .c 103, .c 5, .c 3,
  .c 367, .c 59, .c 3, .c 5, .p pv7 [pv2,pv3,pv23,pv307], .c 3, .c 83, .c 19, .c 3, .c 701,
  .c 557, .c 3, .c 7, .c 5, .c 3, .c 23, .c 47, .c 3, .c 5, .c 7, .c 3,
]
private theorem h0082c23 : checkBlock 677635 128 b0082c23 = true := by
  decide +kernel

private def b0082c24 : List Row := [
  .p pv7 [pv2,pv5,pv67789], .c 61, .c 3, .c 11, .c 79, .c 3, .c 139, .c 5, .c 3, .c 17, .c 13,
  .c 3, .c 5, .c 163, .c 3, .c 773, .c 53, .c 3, .p pv5 [pv2,pv17,pv127,pv157], .c 7, .c 3, .c 29,
  .c 5, .c 3, .c 19, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv103,pv1097], .c 3, .c 37,
  .p pv5 [pv2,pv3,pv11,pv107], .c 3, .c 7, .p pv19 [pv2,pv3,pv19,pv313], .c 3, .c 11, .c 5, .c 3,
  .c 59, .c 7, .c 3, .c 5, .c 17, .c 3, .c 43, .p pv5 [pv2,pv3,pv112997], .c 3, .c 173, .c 13,
  .c 3, .c 199, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5, .c 11, .c 3, .c 17, .c 7, .c 3, .c 23,
  .c 607, .c 3, .p pv5 [pv2,pv47,pv7213], .c 5, .c 3, .c 11, .c 379, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv56503], .c 3, .c 7, .c 239, .c 3, .p pv5 [pv2,pv339023], .c 29, .c 3, .c 19,
  .c 5, .c 3, .c 107, .p pv2 [pv2,pv3,pv5,pv3767], .c 3, .c 5, .c 13, .c 3, .c 491, .c 11, .c 3,
  .p pv2 [pv2,pv7,pv61,pv397], .c 17, .c 3, .c 7, .c 5, .c 3, .c 109, .c 19, .c 3, .c 5, .c 7,
  .c 3, .p pv2 [pv2,pv5,pv6781], .p pv17 [pv2,pv3,pv113017], .c 3, .c 29, .c 23, .c 3, .c 17,
  .c 5, .c 3, .c 13, .c 71, .c 3, .c 5, .c 97, .c 3, .c 461, .p pv2 [pv2,pv3,pv7,pv13,pv23], .c 3,
  .c 61, .c 7, .c 3, .c 223, .c 5,
]
private theorem h0082c24 : checkBlock 677891 128 b0082c24 = true := by
  decide +kernel

private def b0082c25 : List Row := [
  .c 3, .c 269, .c 359, .c 3, .c 5, .p pv2 [pv2,pv3,pv31,pv1823], .c 3, .c 11, .c 47, .c 3, .c 7,
  .p pv19 [pv2,pv3,pv9419], .c 3, .c 37, .c 5, .c 3, .p pv2 [pv2,pv23,pv641], .c 7, .c 3, .c 5,
  .c 31, .c 3, .p pv13 [pv2,pv5,pv67819], .c 83, .c 3, .c 13, .p pv7 [pv2,pv3,pv17,pv61,pv109],
  .c 3, .p pv2 [pv2,pv7,pv193,pv251], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv13,pv37,pv47], .c 3,
  .c 5, .p pv13 [pv2,pv3,pv7,pv11,pv367], .c 3, .p pv2 [pv2,pv5,pv33911], .c 7, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv56519], .c 3, .c 443, .c 5, .c 3, .c 43, .c 53, .c 3, .c 5, .c 23, .c 3, .c 7,
  .p pv19 [pv2,pv3,pv29,pv1949], .c 3, .c 47, .c 61, .c 3, .c 41, .c 5, .c 3, .c 89, .c 11, .c 3,
  .c 5, .c 263, .c 3, .c 19, .c 17, .c 3, .c 137, .p pv7 [pv2,pv3,pv13,pv1087], .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv229,pv1481], .c 13, .c 3, .c 5, .c 7, .c 3, .c 31, .c 271, .c 3, .c 17,
  .c 19, .c 3, .c 59, .c 5, .c 3, .p pv3 [pv2,pv7,pv12113], .c 523, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv13,pv2609], .p pv3 [pv2,pv3,pv7,pv31,pv521], .c 3, .c 53, .c 7, .c 3, .c 13,
  .c 5, .c 3, .c 11, .c 419, .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv223], .c 3,
  .p pv2 [pv2,pv5,pv7,pv11,pv881], .c 31, .c 3, .c 7, .c 13, .c 3, .p pv5 [pv2,pv59,pv5749], .c 5,
  .c 3, .c 73, .c 7, .c 3, .c 5, .c 29, .c 3, .p pv3 [pv2,pv5,pv53],
]
private theorem h0082c25 : checkBlock 678147 128 b0082c25 = true := by
  decide +kernel

private def b0082c26 : List Row := [
  .c 11, .c 3, .p pv5 [pv2,pv163,pv2081], .p pv17 [pv2,pv3,pv23,pv1229], .c 3,
  .p pv2 [pv2,pv7,pv24229], .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv3769], .c 3, .c 5, .c 41,
  .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv11,pv17,pv907], .c 449, .c 3, .c 151, .c 5, .c 3, .c 131,
  .p pv2 [pv2,pv3,pv5,pv4523], .c 3, .c 5, .c 13, .c 3, .c 7, .p pv7 [pv2,pv3,pv73,pv1549], .c 3,
  .c 653, .c 11, .c 3, .c 397, .c 5, .c 3, .p pv7 [pv2,pv339239],
  .p pv13 [pv2,pv3,pv5,pv11,pv257], .c 3, .c 5, .c 17, .c 3, .c 11, .p pv5 [pv2,pv3,pv47,pv401],
  .c 3, .c 31, .p pv2 [pv2,pv3,pv113083], .c 3, .c 7, .c 5, .c 3, .c 13, .c 433, .c 3, .c 5, .c 7,
  .c 3, .c 17, .c 23, .c 3, .c 229, .c 601, .c 3, .p pv2 [pv2,pv169633], .c 5, .c 3, .c 47,
  .p pv7 [pv2,pv3,pv5,pv43,pv263], .c 3, .c 5, .c 19, .c 3, .c 467, .p pv13 [pv2,pv3,pv7,pv577],
  .c 3, .c 11, .c 7, .c 3, .p pv2 [pv2,pv491,pv691], .c 5, .c 3, .c 23, .c 29, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv67,pv211], .c 3, .p pv3 [pv2,pv5,pv7,pv37,pv131], .c 43, .c 3, .c 7, .c 17,
  .c 3, .p pv3 [pv2,pv23,pv461], .c 5, .c 3, .p pv11 [pv2,pv139,pv2441], .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv17,pv6653], .c 3, .p pv2 [pv2,pv5,pv79,pv859], .c 13, .c 3, .c 37, .c 101,
  .c 3, .c 11, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv22621], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv2693], .c 3, .p pv3 [pv2,pv5,pv17,pv499], .c 7, .c 3,
  .p pv5 [pv2,pv339323], .p pv23 [pv2,pv3,pv28277], .c 3, .p pv2 [pv2,pv13,pv31,pv421], .c 5,
  .c 3,
]
private theorem h0082c26 : checkBlock 678403 128 b0082c26 = true := by
  decide +kernel

private def b0082c27 : List Row := [
  .p pv2 [pv2,pv29,pv11701], .c 19, .c 3, .c 5, .c 11, .c 3, .c 7, .c 41, .c 3, .c 59, .c 173,
  .c 3, .c 31, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 317, .c 3, .c 107, .c 647, .c 3, .c 23,
  .c 97, .c 3, .c 7, .c 5, .c 3, .p pv13 [pv2,pv19,pv53,pv337], .p pv23 [pv2,pv3,pv5,pv7,pv101],
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv13,pv23,pv227], .c 11, .c 3, .c 19,
  .p pv17 [pv2,pv3,pv113123], .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv7,pv3463], .c 809, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv13,pv19,pv229], .c 3, .p pv7 [pv2,pv5,pv71,pv239],
  .p pv2 [pv2,pv3,pv7,pv5387], .c 3, .p pv5 [pv2,pv11,pv30853], .c 7, .c 3, .p pv2 [pv2,pv169693],
  .c 5, .c 3, .p pv2 [pv2,pv339389], .c 193, .c 3, .c 5, .c 211, .c 3, .c 113, .c 17, .c 3, .c 7,
  .c 11, .c 3, .c 29, .c 5, .c 3, .p pv3 [pv2,pv13,pv61,pv107], .c 7, .c 3, .c 5, .c 569, .c 3,
  .c 11, .p pv3 [pv2,pv3,pv23,pv4919], .c 3, .c 17, .p pv2 [pv2,pv3,pv56569], .c 3,
  .p pv3 [pv2,pv7,pv11,pv19,pv29], .c 5, .c 3, .c 7, .c 43, .c 3, .c 5, .c 13, .c 3, .c 19, .c 7,
  .c 3, .c 83, .p pv3 [pv2,pv3,pv113143], .c 3, .c 521, .c 5, .c 3, .c 31,
  .p pv3 [pv2,pv3,pv5,pv19,pv397], .c 3, .c 5, .c 53, .c 3, .c 7, .p pv7 [pv2,pv3,pv113147], .c 3,
  .c 11, .c 19, .c 3, .c 401, .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv31,pv73], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv37717], .c 3, .c 67, .c 37,
]
private theorem h0082c27 : checkBlock 678659 128 b0082c27 = true := by
  decide +kernel

private def b0082c28 : List Row := [
  .c 3, .c 283, .c 29, .c 3, .c 7, .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv83,pv409], .p pv3 [pv2,pv3,pv11,pv127], .c 3, .c 179,
  .p pv2 [pv2,pv3,pv29,pv1951], .c 3, .c 11, .c 5, .c 3, .p pv13 [pv2,pv7,pv48497], .c 109, .c 3,
  .c 5, .c 821, .c 3, .p pv2 [pv2,pv5,pv43,pv1579], .c 71, .c 3, .c 13, .c 7, .c 3, .c 23, .c 5,
  .c 3, .p pv2 [pv2,pv199,pv853], .c 61, .c 3, .c 5, .c 11, .c 3, .c 41, .c 13, .c 3, .c 7, .c 47,
  .c 3, .c 43, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 769, .c 3, .c 17, .p pv7 [pv2,pv3,pv9431],
  .c 3, .p pv2 [pv2,pv53,pv3203], .p pv7 [pv2,pv3,pv113173], .c 3, .c 619, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv503], .c 3, .c 5, .c 673, .c 3, .c 37, .c 7, .c 3,
  .p pv2 [pv2,pv263,pv1291], .c 127, .c 3, .c 421, .c 5, .c 3, .c 19, .c 13, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv31,pv1217], .c 3, .c 7, .c 29, .c 3, .c 97, .c 17, .c 3, .c 47, .c 5, .c 3,
  .c 137, .p pv11 [pv2,pv3,pv5,pv22637], .c 3, .c 5, .c 19, .c 3, .c 23,
  .p pv3 [pv2,pv3,pv29,pv1301], .c 3, .p pv5 [pv2,pv7,pv179,pv271], .c 11, .c 3, .c 7, .c 5, .c 3,
  .c 499, .c 739, .c 3, .c 5, .c 7, .c 3, .c 11, .p pv5 [pv2,pv3,pv14149], .c 3,
  .p pv2 [pv2,pv169789], .c 13, .c 3, .c 79, .c 5, .c 3, .p pv3 [pv2,pv7,pv379],
]
private theorem h0082c28 : checkBlock 678915 128 b0082c28 = true := by
  decide +kernel

private def b0082c29 : List Row := [
  .p pv3 [pv2,pv3,pv5,pv22639], .c 3, .c 5, .c 281, .c 3, .c 787,
  .p pv3 [pv2,pv3,pv7,pv103,pv157], .c 3, .c 199, .c 7, .c 3, .c 19, .c 5, .c 3, .c 419, .c 17,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv41,pv251], .c 3, .c 13, .c 23, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv17,pv6659], .c 3, .p pv5 [pv2,pv479,pv709], .c 5, .c 3,
  .p pv2 [pv2,pv11,pv43,pv359], .c 7, .c 3, .c 5, .c 13, .c 3, .c 31, .c 113, .c 3, .c 41,
  .p pv17 [pv2,pv3,pv53,pv89], .c 3, .c 691, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 29, .c 3,
  .c 43, .c 7, .c 3, .p pv2 [pv2,pv13,pv13063], .p pv17 [pv2,pv3,pv113213], .c 3, .c 11, .c 5,
  .c 3, .c 13, .c 47, .c 3, .c 5, .p pv5 [pv2,pv3,pv29,pv61], .c 3, .c 7, .c 17, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv7,pv8087], .c 3, .c 67, .c 5, .c 3, .p pv7 [pv2,pv339659], .c 79, .c 3, .c 5,
  .c 11, .c 3, .c 317, .p pv5 [pv2,pv3,pv56611], .c 3, .c 17, .c 157, .c 3, .c 7, .c 5, .c 3,
  .c 11, .c 23, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv11,pv193], .p pv5 [pv2,pv3,pv113227],
  .c 3, .c 13, .p pv13 [pv2,pv3,pv28307], .c 3, .p pv2 [pv2,pv169843], .c 5, .c 3, .c 241,
  .p pv2 [pv2,pv3,pv5,pv13,pv67], .c 3, .c 5, .c 191, .c 3, .c 307, .c 11, .c 3, .c 23, .c 7,
  .c 3, .p pv2 [pv2,pv19,pv941], .c 5, .c 3, .p pv3 [pv2,pv42463], .c 41, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv28309], .c 3, .c 19, .p pv3 [pv2,pv3,pv17,pv6661], .c 3,
]
private theorem h0082c29 : checkBlock 679171 128 b0082c29 = true := by
  decide +kernel

private def b0082c30 : List Row := [
  .c 7, .c 659, .c 3, .p pv3 [pv2,pv13,pv47,pv139], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 67,
  .c 3, .p pv2 [pv2,pv5,pv107,pv127], .c 197, .c 3, .c 251, .c 11, .c 3, .p pv5 [pv2,pv7,pv48533],
  .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 239, .c 3, .c 11, .c 7, .c 3, .p pv5 [pv2,pv43,pv7901],
  .c 23, .c 3, .c 41, .c 5, .c 3, .c 29, .p pv2 [pv2,pv3,pv5,pv151], .c 3, .c 5, .c 17, .c 3,
  .c 7, .c 53, .c 3, .p pv2 [pv2,pv19,pv8941], .p pv3 [pv2,pv3,pv7,pv5393], .c 3, .c 13, .c 5,
  .c 3, .c 43, .p pv2 [pv2,pv3,pv5,pv22651], .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv13], .c 3, .c 17,
  .c 331, .c 3, .c 11, .c 13, .c 3, .c 7, .c 5, .c 3, .c 457, .p pv37 [pv2,pv3,pv5,pv7,pv809],
  .c 3, .c 5, .c 7, .c 3, .c 139, .c 19, .c 3, .c 127, .c 37, .c 3, .c 389, .c 5, .c 3, .c 149,
  .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv56633], .c 3, .c 13, .p pv2 [pv2,pv3,pv7,pv11,pv1471],
  .c 3, .p pv5 [pv2,pv373,pv911], .c 7, .c 3, .c 11, .c 5, .c 3, .c 53, .c 59, .c 3, .c 5, .c 13,
  .c 3, .c 211, .p pv5 [pv2,pv3,pv14159], .c 3, .c 7, .p pv3 [pv2,pv3,pv227,pv499], .c 3, .c 17,
  .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 11, .c 3, .c 233, .c 179, .c 3, .c 47,
  .p pv2 [pv2,pv3,pv11,pv19,pv271], .c 3, .c 23, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv59],
]
private theorem h0082c30 : checkBlock 679427 128 b0082c30 = true := by
  decide +kernel

private def b0082c31 : List Row := [
  .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv11,pv37,pv167], .c 7, .c 3, .c 103,
  .p pv3 [pv2,pv3,pv41,pv307], .c 3, .c 73, .c 5, .c 3, .p pv2 [pv2,pv251,pv677], .c 17, .c 3,
  .c 5, .c 173, .c 3, .c 7, .c 11, .c 3, .c 37, .c 337, .c 3, .p pv2 [pv2,pv169933], .c 5, .c 3,
  .c 41, .p pv23 [pv2,pv3,pv5,pv11329], .c 3, .c 5, .p pv5 [pv2,pv3,pv193,pv587], .c 3,
  .p pv13 [pv2,pv5,pv2719], .p pv5 [pv2,pv3,pv1049], .c 3, .c 13, .c 131, .c 3, .c 7, .c 5, .c 3,
  .c 191, .c 107, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv41,pv829], .c 13, .c 3, .c 43, .c 11,
  .c 3, .p pv3 [pv2,pv42487], .c 5, .c 3, .c 31, .c 19, .c 3, .c 5, .p pv3 [pv2,pv3,pv12589],
  .c 3, .c 11, .c 17, .c 3, .c 613, .c 7, .c 3, .p pv5 [pv2,pv11,pv13,pv2377], .c 5, .c 3,
  .p pv2 [pv2,pv169957], .c 53, .c 3, .c 5, .p pv5 [pv2,pv3,pv181,pv313], .c 3, .c 797,
  .p pv2 [pv2,pv3,pv179,pv211], .c 3, .c 7, .c 67, .c 3, .c 83, .c 5, .c 3,
  .p pv2 [pv2,pv19,pv17891], .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv10301], .c 3, .c 89, .c 43,
  .c 3, .c 11, .p pv3 [pv2,pv3,pv107,pv353], .c 3, .p pv2 [pv2,pv7,pv48563], .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv131,pv173], .c 3, .c 5, .p pv23 [pv2,pv3,pv7,pv19,pv71], .c 3, .c 229,
  .c 7, .c 3, .p pv2 [pv2,pv61,pv5573], .p pv2 [pv2,pv3,pv56659], .c 3, .c 13, .c 5, .c 3,
  .p pv7 [pv2,pv339959], .c 11, .c 3, .c 5, .c 223, .c 3, .c 7, .p pv5 [pv2,pv3,pv11,pv17,pv101],
  .c 3, .c 53,
]
private theorem h0082c31 : checkBlock 679683 128 b0082c31 = true := by
  decide +kernel

def rows0082 : List Row :=
  b0082c00 ++ b0082c01 ++ b0082c02 ++ b0082c03 ++ b0082c04 ++ b0082c05 ++ b0082c06 ++ b0082c07 ++
  b0082c08 ++ b0082c09 ++ b0082c10 ++ b0082c11 ++ b0082c12 ++ b0082c13 ++ b0082c14 ++ b0082c15 ++
  b0082c16 ++ b0082c17 ++ b0082c18 ++ b0082c19 ++ b0082c20 ++ b0082c21 ++ b0082c22 ++ b0082c23 ++
  b0082c24 ++ b0082c25 ++ b0082c26 ++ b0082c27 ++ b0082c28 ++ b0082c29 ++ b0082c30 ++ b0082c31

attribute [local irreducible] checkBlock checkRows checkPrime

theorem checked0082 : checkBlock 671747 4096 rows0082 = true :=
  checkBlock_append h0082c00 (
    checkBlock_append h0082c01 (
    checkBlock_append h0082c02 (
    checkBlock_append h0082c03 (
    checkBlock_append h0082c04 (
    checkBlock_append h0082c05 (
    checkBlock_append h0082c06 (
    checkBlock_append h0082c07 (
    checkBlock_append h0082c08 (
    checkBlock_append h0082c09 (
    checkBlock_append h0082c10 (
    checkBlock_append h0082c11 (
    checkBlock_append h0082c12 (
    checkBlock_append h0082c13 (
    checkBlock_append h0082c14 (
    checkBlock_append h0082c15 (
    checkBlock_append h0082c16 (
    checkBlock_append h0082c17 (
    checkBlock_append h0082c18 (
    checkBlock_append h0082c19 (
    checkBlock_append h0082c20 (
    checkBlock_append h0082c21 (
    checkBlock_append h0082c22 (
    checkBlock_append h0082c23 (
    checkBlock_append h0082c24 (
    checkBlock_append h0082c25 (
    checkBlock_append h0082c26 (
    checkBlock_append h0082c27 (
    checkBlock_append h0082c28 (
    checkBlock_append h0082c29 (
    checkBlock_append h0082c30 (
    h0082c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
