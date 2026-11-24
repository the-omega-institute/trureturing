/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0112
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0112.checked0112
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table106

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0112c00 : List Row := [
  .c 17, .c 59, .c 3, .p pv3 [pv2,pv114689], .c 5, .c 3, .p pv7 [pv2,pv7,pv65537], .c 11, .c 3,
  .c 5, .c 13, .c 3, .c 29, .c 71, .c 3, .c 73, .c 7, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv19,pv12073], .c 773, .c 3, .c 5, .p pv2 [pv2,pv3,pv76463], .c 3, .c 643, .c 37,
  .c 3, .c 7, .c 31, .c 3, .p pv2 [pv2,pv229393], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 11,
  .c 3, .p pv11 [pv2,pv5,pv89,pv1031], .p pv5 [pv2,pv3,pv13,pv17,pv173], .c 3, .c 571, .c 431,
  .c 3, .c 229, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv73,pv419], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv2731], .c 3, .c 41, .c 7, .c 3, .c 59, .p pv2 [pv2,pv3,pv47,pv1627], .c 3,
  .p pv3 [pv2,pv67,pv107], .c 5, .c 3, .c 211, .p pv11 [pv2,pv3,pv5,pv2549], .c 3, .c 5, .c 29,
  .c 3, .c 7, .c 11, .c 3, .c 13, .p pv7 [pv2,pv3,pv7,pv7283], .c 3, .c 43, .c 5, .c 3,
  .p pv2 [pv2,pv383,pv599], .c 109, .c 3, .c 5, .c 17, .c 3, .c 19, .c 13, .c 3,
  .p pv5 [pv2,pv7,pv11,pv59,pv101], .p pv7 [pv2,pv3,pv38237], .c 3, .c 7, .c 5, .c 3, .c 67,
  .c 277, .c 3, .c 5, .c 7, .c 3, .c 17, .p pv5 [pv2,pv3,pv6373], .c 3, .c 97, .c 11, .c 3, .c 23,
  .c 5, .c 3, .p pv3 [pv2,pv7,pv17,pv241], .c 83, .c 3, .c 5, .p pv5 [pv2,pv3,pv38239], .c 3,
  .c 11, .c 79, .c 3, .c 257, .c 7, .c 3, .p pv3 [pv2,pv11,pv10429], .c 5, .c 3,
  .p pv13 [pv2,pv458879], .c 13,
]
private theorem h0112c00 : checkBlock 917507 128 b0112c00 = true := by
  decide +kernel

private def b0112c01 : List Row := [
  .c 3, .c 5, .p pv3 [pv2,pv3,pv67,pv761], .c 3, .p pv7 [pv2,pv5,pv7,pv1873],
  .p pv2 [pv2,pv3,pv76481], .c 3, .c 7, .c 17, .c 3, .p pv5 [pv2,pv458891], .c 5, .c 3,
  .p pv2 [pv2,pv199,pv1153], .c 7, .c 3, .c 5, .c 569, .c 3, .c 53, .p pv2 [pv2,pv3,pv50989],
  .c 3, .c 11, .p pv11 [pv2,pv3,pv19121], .c 3, .c 13, .c 5, .c 3, .c 7, .c 29, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv13,pv41], .c 3, .p pv19 [pv2,pv5,pv17,pv5399], .c 7, .c 3,
  .p pv2 [pv2,pv229459], .c 13, .c 3, .p pv2 [pv2,pv458921], .c 5, .c 3, .p pv3 [pv2,pv31,pv3701],
  .c 11, .c 3, .c 5, .c 89, .c 3, .c 7, .c 47, .c 3, .c 41, .p pv17 [pv2,pv3,pv7,pv223], .c 3,
  .c 11, .c 5, .c 3, .c 29, .c 17, .c 3, .c 5, .p pv3 [pv2,pv3,pv152981], .c 3, .c 13,
  .p pv2 [pv2,pv3,pv2833], .c 3, .c 83, .c 113, .c 3, .c 7, .c 5, .c 3, .c 19, .c 97, .c 3, .c 5,
  .c 7, .c 3, .c 43, .p pv2 [pv2,pv3,pv59,pv2593], .c 3, .p pv5 [pv2,pv458963], .c 151, .c 3,
  .c 37, .c 5, .c 3, .c 11, .c 31, .c 3, .c 5, .c 19, .c 3, .p pv11 [pv2,pv5,pv11,pv1669], .c 23,
  .c 3, .c 47, .c 7, .c 3, .c 359, .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv37,pv827], .c 3, .c 5,
  .c 619, .c 3, .c 59, .c 11, .c 3, .c 7, .c 61, .c 3, .p pv3 [pv2,pv114749], .c 5, .c 3, .c 23,
  .c 7, .c 3, .c 5, .c 37, .c 3, .p pv2 [pv2,pv5,pv91801], .c 53, .c 3, .c 17,
]
private theorem h0112c01 : checkBlock 917763 128 b0112c01 = true := by
  decide +kernel

private def b0112c02 : List Row := [
  .p pv2 [pv2,pv3,pv51001], .c 3, .c 19, .c 5, .c 3, .c 7, .c 41, .c 3, .c 5, .c 137, .c 3,
  .p pv3 [pv2,pv5,pv59,pv389], .c 7, .c 3, .c 13, .c 11, .c 3, .c 29, .c 5, .c 3, .c 79, .c 19,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv53,pv2887], .c 3, .c 7, .c 13, .c 3, .c 541,
  .p pv3 [pv2,pv3,pv7,pv21859], .c 3, .c 127, .c 5, .c 3, .p pv3 [pv2,pv114761], .c 23, .c 3,
  .c 5, .c 269, .c 3, .c 67, .p pv3 [pv2,pv3,pv17,pv9001], .c 3, .c 109, .p pv2 [pv2,pv3,pv8501],
  .c 3, .c 7, .c 5, .c 3, .c 17, .c 73, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv91813], .c 263,
  .c 3, .c 11, .p pv3 [pv2,pv3,pv13,pv79,pv149], .c 3, .p pv5 [pv2,pv103,pv4457], .c 5, .c 3,
  .p pv13 [pv2,pv7,pv11,pv271], .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv19,pv4027], .c 3,
  .p pv7 [pv2,pv5,pv23,pv499], .c 719, .c 3, .c 107, .c 7, .c 3, .p pv2 [pv2,pv53,pv61,pv71],
  .c 5, .c 3, .c 43, .c 11, .c 3, .c 5, .c 17, .c 3, .c 101, .p pv5 [pv2,pv3,pv11,pv37,pv47],
  .c 3, .c 7, .p pv3 [pv2,pv3,pv29,pv1759], .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv14347], .c 7,
  .c 3, .c 5, .c 59, .c 3, .c 17, .p pv11 [pv2,pv3,pv43,pv3559], .c 3, .c 29, .c 13, .c 3, .c 61,
  .c 5, .c 3, .c 7, .c 757, .c 3, .c 5, .c 11, .c 3, .c 19, .c 7, .c 3, .p pv3 [pv2,pv29,pv1979],
  .p pv29 [pv2,pv3,pv11,pv13913], .c 3, .p pv5 [pv2,pv293,pv1567], .c 5, .c 3, .c 11, .c 859,
  .c 3,
]
private theorem h0112c02 : checkBlock 918019 128 b0112c02 = true := by
  decide +kernel

private def b0112c03 : List Row := [
  .c 5, .c 41, .c 3, .c 7, .p pv3 [pv2,pv3,pv31,pv4937], .c 3, .c 149, .c 17, .c 3, .c 157, .c 5,
  .c 3, .c 97, .p pv2 [pv2,pv3,pv5,pv3061], .c 3, .c 5, .c 13, .c 3, .c 137, .c 11, .c 3, .c 379,
  .p pv19 [pv2,pv3,pv41,pv3733], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv191,pv601], .c 53, .c 3,
  .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv17,pv37,pv73], .c 29, .c 3, .p pv2 [pv2,pv11,pv13,pv19],
  .c 317, .c 3, .p pv3 [pv2,pv57397], .c 5, .c 3, .c 13, .p pv7 [pv2,pv3,pv5,pv2551], .c 3, .c 5,
  .c 23, .c 3, .p pv2 [pv2,pv5,pv91837], .c 139, .c 3, .c 37, .c 7, .c 3, .c 311, .c 5, .c 3,
  .p pv2 [pv2,pv439,pv523], .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv97,pv263], .c 3, .c 11, .c 19,
  .c 3, .c 7, .c 251, .c 3, .c 23, .c 5, .c 3, .c 271, .c 7, .c 3, .c 5, .c 47, .c 3,
  .p pv13 [pv2,pv5,pv29,pv3167], .p pv5 [pv2,pv3,pv1063], .c 3, .c 13, .p pv3 [pv2,pv3,pv153073],
  .c 3, .p pv2 [pv2,pv7,pv17,pv227], .c 5, .c 3, .c 7, .c 37, .c 3, .c 5, .c 173, .c 3, .c 431,
  .c 7, .c 3, .c 11, .p pv7 [pv2,pv3,pv31,pv823], .c 3, .c 751, .c 5, .c 3, .c 19,
  .p pv13 [pv2,pv3,pv5,pv43,pv89], .c 3, .c 5, .c 193, .c 3, .c 7, .c 17, .c 3,
  .p pv3 [pv2,pv28703], .c 31, .c 3, .c 67, .c 5, .c 3, .c 347, .c 11, .c 3, .c 5, .c 19, .c 3,
  .c 47, .c 41, .c 3, .c 17, .p pv7 [pv2,pv3,pv13,pv23],
]
private theorem h0112c03 : checkBlock 918275 128 b0112c03 = true := by
  decide +kernel

private def b0112c04 : List Row := [
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv61,pv7529], .c 13, .c 3, .c 5, .c 7, .c 3, .c 23, .c 641,
  .c 3, .c 593, .c 73, .c 3, .p pv2 [pv2,pv37,pv12413], .c 5, .c 3, .c 89, .c 59, .c 3, .c 5,
  .c 11, .c 3, .p pv2 [pv2,pv5,pv13,pv3533], .p pv3 [pv2,pv3,pv7,pv21871], .c 3,
  .p pv2 [pv2,pv459293], .c 7, .c 3, .c 13, .c 5, .c 3, .c 11, .c 367, .c 3, .c 5, .c 157, .c 3,
  .c 197, .p pv5 [pv2,pv3,pv17,pv19,pv79], .c 3, .c 7, .c 13, .c 3, .c 31, .c 5, .c 3, .c 17,
  .c 7, .c 3, .c 5, .c 67, .c 3, .p pv3 [pv2,pv5,pv11483], .c 11, .c 3,
  .p pv7 [pv2,pv17,pv41,pv659], .c 53, .c 3, .p pv2 [pv2,pv7,pv43,pv109], .c 5, .c 3, .c 7,
  .c 491, .c 3, .c 5, .c 167, .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv11,pv20879],
  .p pv11 [pv2,pv3,pv153113], .c 3, .p pv2 [pv2,pv459341], .c 5, .c 3, .c 23, .c 29, .c 3, .c 5,
  .c 13, .c 3, .c 7, .c 131, .c 3, .c 19, .c 11, .c 3, .c 617, .c 5, .c 3, .c 233, .c 61, .c 3,
  .c 5, .c 83, .c 3, .c 11, .p pv2 [pv2,pv3,pv76561], .c 3, .p pv3 [pv2,pv7,pv13,pv631], .c 571,
  .c 3, .c 7, .c 5, .c 3, .c 13, .p pv7 [pv2,pv3,pv5,pv7], .c 3, .c 5, .c 7, .c 3, .c 109,
  .p pv2 [pv2,pv3,pv13,pv11779], .c 3, .p pv5 [pv2,pv459383], .c 41, .c 3, .c 461, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv29,pv31,pv73], .c 23, .c 3, .c 5,
]
private theorem h0112c04 : checkBlock 918531 128 b0112c04 = true := by
  decide +kernel

private def b0112c05 : List Row := [
  .p pv2 [pv2,pv3,pv11,pv13921], .c 3, .c 907, .p pv5 [pv2,pv3,pv7,pv1823], .c 3, .c 11, .c 7,
  .c 3, .c 47, .c 5, .c 3, .c 31, .c 71, .c 3, .c 5, .c 383, .c 3, .c 19,
  .p pv11 [pv2,pv3,pv153137], .c 3, .c 7, .p pv13 [pv2,pv3,pv25523], .c 3, .c 17, .c 5, .c 3,
  .p pv11 [pv2,pv67,pv6857], .c 7, .c 3, .c 5, .c 643, .c 3, .c 41, .c 13, .c 3,
  .p pv3 [pv2,pv331,pv347], .c 19, .c 3, .c 11, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv10939], .c 3, .c 97, .c 7, .c 3, .c 613, .p pv17 [pv2,pv3,pv38287], .c 3,
  .c 83, .c 5, .c 3, .p pv2 [pv2,pv101,pv4549], .c 17, .c 3, .c 5, .c 11, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv2393], .c 3, .c 349, .c 23, .c 3, .c 29, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5,
  .c 181, .c 3, .c 797, .p pv31 [pv2,pv3,pv23,pv6659], .c 3, .p pv2 [pv2,pv7,pv9377],
  .p pv2 [pv2,pv3,pv76579], .c 3, .c 7, .c 5, .c 3, .p pv13 [pv2,pv459479], .c 271, .c 3, .c 5,
  .c 7, .c 3, .p pv7 [pv2,pv5,pv13,pv7069], .c 11, .c 3, .c 229, .c 109, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv23,pv1427], .c 47, .c 3, .c 5, .c 73, .c 3, .c 167, .c 17, .c 3, .c 79, .c 7,
  .c 3, .p pv2 [pv2,pv229753], .c 5, .c 3, .p pv2 [pv2,pv459509], .p pv2 [pv2,pv3,pv5,pv17,pv53],
  .c 3, .c 5, .c 457, .c 3, .p pv7 [pv2,pv5,pv7,pv19,pv691], .p pv5 [pv2,pv3,pv149,pv257], .c 3,
  .c 7, .c 11, .c 3,
]
private theorem h0112c05 : checkBlock 918787 128 b0112c05 = true := by
  decide +kernel

private def b0112c06 : List Row := [
  .c 37, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 23, .c 3, .c 11, .p pv23 [pv2,pv3,pv51059], .c 3,
  .p pv2 [pv2,pv193,pv2381], .c 103, .c 3, .c 53, .c 5, .c 3, .c 7,
  .p pv31 [pv2,pv3,pv5,pv23,pv37], .c 3, .c 5, .c 13, .c 3, .c 743, .c 7, .c 3, .c 29, .c 127,
  .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv229777], .p pv3 [pv2,pv3,pv5,pv30637], .c 3, .c 5, .c 37,
  .c 3, .c 7, .c 227, .c 3, .c 11, .p pv17 [pv2,pv3,pv7,pv5471], .c 3, .c 137, .c 5, .c 3, .c 13,
  .c 293, .c 3, .c 5, .p pv2 [pv2,pv3,pv153191], .c 3, .c 281, .p pv5 [pv2,pv3,pv13,pv491], .c 3,
  .c 163, .c 541, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv43,pv167], .c 11, .c 3, .c 5, .c 7, .c 3,
  .c 31, .p pv11 [pv2,pv3,pv11,pv19,pv733], .c 3, .c 331, .p pv2 [pv2,pv3,pv2837], .c 3, .c 11,
  .c 5, .c 3, .c 911, .c 19, .c 3, .c 5, .c 17, .c 3, .c 43, .c 29, .c 3, .c 13, .c 7, .c 3,
  .p pv5 [pv2,pv459611], .c 5, .c 3, .p pv2 [pv2,pv37,pv6211], .p pv3 [pv2,pv3,pv5,pv13,pv2357],
  .c 3, .c 5, .c 11, .c 3, .c 17, .c 13, .c 3, .c 7, .p pv19 [pv2,pv3,pv11,pv1741], .c 3,
  .p pv2 [pv2,pv229813], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv349,pv439], .c 3,
  .c 29, .c 47, .c 3, .c 19, .c 59, .c 3, .c 191, .c 5, .c 3, .c 7, .c 823, .c 3, .c 5, .c 43,
]
private theorem h0112c06 : checkBlock 919043 128 b0112c06 = true := by
  decide +kernel

private def b0112c07 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv29,pv317], .c 7, .c 3, .c 67, .c 17, .c 3, .p pv3 [pv2,pv57457], .c 5,
  .c 3, .p pv7 [pv2,pv673,pv683], .c 13, .c 3, .c 5, .c 211, .c 3, .c 7, .c 23, .c 3,
  .p pv3 [pv2,pv11,pv31,pv337], .c 37, .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv229837],
  .p pv11 [pv2,pv3,pv5,pv227], .c 3, .c 5, .c 941, .c 3, .c 829, .c 277, .c 3, .c 31, .c 11, .c 3,
  .c 7, .c 5, .c 3, .c 23, .p pv2 [pv2,pv3,pv5,pv7,pv11,pv199], .c 3, .c 5, .c 7, .c 3, .c 11,
  .p pv13 [pv2,pv3,pv61,pv157], .c 3, .c 59, .c 13, .c 3, .c 101, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv8209], .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv29,pv1321], .c 3,
  .p pv2 [pv2,pv5,pv45971], .p pv13 [pv2,pv3,pv7,pv7297], .c 3, .p pv2 [pv2,pv43,pv10691], .c 7,
  .c 3, .c 239, .c 5, .c 3, .c 151, .c 67, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv13931], .c 3, .c 13,
  .c 61, .c 3, .c 7, .c 89, .c 3, .c 97, .c 5, .c 3, .c 43, .c 7, .c 3, .c 5, .c 13, .c 3, .c 79,
  .c 163, .c 3, .c 37, .c 131, .c 3, .c 401, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 41, .c 3,
  .p pv29 [pv2,pv5,pv91951], .c 7, .c 3, .c 23, .p pv17 [pv2,pv3,pv331,pv463], .c 3, .c 11, .c 5,
  .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv17,pv601], .c 3, .c 5, .c 947, .c 3, .c 7, .c 19, .c 3,
  .c 17, .c 157, .c 3, .c 31,
]
private theorem h0112c07 : checkBlock 919299 128 b0112c07 = true := by
  decide +kernel

private def b0112c08 : List Row := [
  .c 5, .c 3, .p pv7 [pv2,pv107,pv4297], .c 29, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv91957],
  .c 709, .c 3, .c 227, .c 199, .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv31 [pv2,pv3,pv5,pv7,pv29,pv151], .c 3, .c 5, .c 7, .c 3, .c 719, .c 53, .c 3, .c 13, .c 23,
  .c 3, .p pv2 [pv2,pv229903], .c 5, .c 3, .c 19, .p pv17 [pv2,pv3,pv5,pv13,pv131], .c 3, .c 5,
  .c 311, .c 3, .p pv11 [pv2,pv5,pv41,pv2243], .c 11, .c 3, .c 89, .c 7, .c 3, .c 491, .c 5, .c 3,
  .c 17, .c 233, .c 3, .c 5, .c 19, .c 3, .c 181, .c 71, .c 3, .c 7, .c 167, .c 3, .c 337, .c 5,
  .c 3, .p pv23 [pv2,pv23,pv19993], .c 7, .c 3, .c 5, .c 103, .c 3, .p pv2 [pv2,pv5,pv91969],
  .p pv2 [pv2,pv3,pv59,pv433], .c 3, .c 61, .c 11, .c 3, .p pv5 [pv2,pv7,pv179,pv367], .c 5, .c 3,
  .c 7, .c 13, .c 3, .c 5, .c 17, .c 3, .c 11, .c 7, .c 3, .c 43, .p pv7 [pv2,pv3,pv2129], .c 3,
  .c 19, .c 5, .c 3, .c 31, .c 151, .c 3, .c 5, .c 23, .c 3, .c 7, .c 41, .c 3,
  .p pv2 [pv2,pv229939], .p pv31 [pv2,pv3,pv7,pv61,pv359], .c 3, .c 13, .c 5, .c 3,
  .p pv3 [pv2,pv17,pv6763], .c 19, .c 3, .c 5, .c 149, .c 3, .p pv3 [pv2,pv5,pv45989], .c 37,
  .c 3, .c 11, .c 13, .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv11,pv41809], .c 31, .c 3, .c 5, .c 7,
  .c 3,
]
private theorem h0112c08 : checkBlock 919555 128 b0112c08 = true := by
  decide +kernel

private def b0112c09 : List Row := [
  .p pv2 [pv2,pv5,pv59,pv1559], .c 43, .c 3, .p pv3 [pv2,pv23,pv4999], .c 17, .c 3,
  .p pv5 [pv2,pv29,pv15859], .c 5, .c 3, .c 587, .c 11, .c 3, .c 5, .c 47, .c 3, .c 13, .c 67,
  .c 3, .c 19, .c 7, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv459929], .c 127, .c 3, .c 5, .c 13,
  .c 3, .p pv7 [pv2,pv5,pv7,pv17,pv773], .c 73, .c 3, .c 7, .c 107, .c 3,
  .p pv2 [pv2,pv131,pv3511], .c 5, .c 3, .c 83, .c 7, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv9199], .p pv5 [pv2,pv3,pv139,pv1103], .c 3, .c 313, .c 29, .c 3,
  .p pv5 [pv2,pv7,pv16427], .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv149], .c 3,
  .c 23, .c 7, .c 3, .p pv3 [pv2,pv7187], .p pv2 [pv2,pv3,pv17,pv29,pv311], .c 3, .c 487, .c 5,
  .c 3, .p pv2 [pv2,pv97,pv2371], .p pv7 [pv2,pv3,pv5,pv6133], .c 3, .c 5, .c 523, .c 3, .c 7,
  .c 11, .c 3, .c 29, .p pv11 [pv2,pv3,pv7,pv37], .c 3, .c 877, .c 5, .c 3,
  .p pv7 [pv2,pv47,pv9787], .c 463, .c 3, .c 5, .c 31, .c 3, .c 673, .c 89, .c 3, .c 13, .c 19,
  .c 3, .c 7, .c 5, .c 3, .c 101, .p pv7 [pv2,pv3,pv5,pv7,pv13,pv337], .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv157,pv293], .c 13, .c 3, .c 53, .c 11, .c 3, .c 283, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv65717], .c 139, .c 3, .c 5, .c 191, .c 3, .c 11, .p pv5 [pv2,pv3,pv7,pv1217],
  .c 3, .c 17, .c 7, .c 3, .c 61, .c 5,
]
private theorem h0112c09 : checkBlock 919811 128 b0112c09 = true := by
  decide +kernel

private def b0112c10 : List Row := [
  .c 3, .c 23, .c 43, .c 3, .c 5, .c 653, .c 3, .c 41, .c 29, .c 3, .c 7, .c 71, .c 3, .c 107,
  .c 5, .c 3, .c 103, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv1549], .c 3, .c 31, .c 19, .c 3,
  .c 11, .c 47, .c 3, .p pv2 [pv2,pv7,pv41,pv229], .c 5, .c 3, .c 7, .c 601, .c 3, .c 5,
  .p pv31 [pv2,pv3,pv7,pv5477], .c 3, .c 29, .c 7, .c 3, .p pv2 [pv2,pv460073],
  .p pv2 [pv2,pv3,pv76679], .c 3, .c 13, .c 5, .c 3, .c 17, .c 11, .c 3, .c 5,
  .p pv19 [pv2,pv3,pv13,pv47,pv251], .c 3, .c 7, .c 31, .c 3, .c 157, .c 13, .c 3, .c 11, .c 5,
  .c 3, .c 19, .c 373, .c 3, .c 5, .p pv5 [pv2,pv3,pv25561], .c 3, .p pv11 [pv2,pv5,pv43,pv107],
  .p pv2 [pv2,pv3,pv103,pv1489], .c 3, .c 23, .p pv7 [pv2,pv3,pv19,pv1009], .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv13,pv35393], .c 83, .c 3, .c 5, .c 7, .c 3, .c 13,
  .p pv11 [pv2,pv3,pv12781], .c 3, .c 263, .c 53, .c 3, .c 43, .c 5, .c 3, .c 11, .c 317, .c 3,
  .c 5, .c 13, .c 3, .c 17, .p pv3 [pv2,pv3,pv7,pv21911], .c 3, .p pv2 [pv2,pv31,pv14843], .c 7,
  .c 3, .p pv3 [pv2,pv113,pv509], .c 5, .c 3, .p pv23 [pv2,pv17,pv27067],
  .p pv7 [pv2,pv3,pv5,pv7669], .c 3, .c 5, .c 109, .c 3, .p pv2 [pv2,pv5,pv7,pv13147], .c 11,
  .c 3, .c 7, .c 23, .c 3, .c 19, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 257, .c 3, .c 223,
]
private theorem h0112c10 : checkBlock 920067 128 b0112c10 = true := by
  decide +kernel

private def b0112c11 : List Row := [
  .p pv3 [pv2,pv3,pv13,pv19,pv23], .c 3, .c 41, .c 17, .c 3, .p pv5 [pv2,pv7,pv32869], .c 5, .c 3,
  .c 7, .c 19, .c 3, .c 5, .c 337, .c 3, .c 229, .c 7, .c 3, .p pv2 [pv2,pv230089], .c 11, .c 3,
  .c 17, .c 5, .c 3, .c 127, .p pv2 [pv2,pv3,pv5,pv11,pv2789], .c 3, .c 5,
  .p pv7 [pv2,pv3,pv4261], .c 3, .c 7, .c 839, .c 3, .c 13, .c 239, .c 3,
  .p pv3 [pv2,pv11,pv10459], .c 5, .c 3, .p pv7 [pv2,pv19,pv53,pv457], .c 47, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv131,pv1171], .c 3, .p pv2 [pv2,pv5,pv92041], .c 13, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv179,pv857], .c 3, .c 7, .c 5, .c 3, .c 61, .c 17, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv23011], .p pv2 [pv2,pv3,pv153407], .c 3, .c 11, .c 37, .c 3, .c 619, .c 5,
  .c 3, .c 59, .c 163, .c 3, .c 5, .p pv3 [pv2,pv3,pv51137], .c 3, .c 277,
  .p pv5 [pv2,pv3,pv7,pv5479], .c 3, .p pv2 [pv2,pv359,pv641], .c 7, .c 3, .c 23, .c 5, .c 3,
  .c 29, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv127,pv151], .c 3, .c 43, .c 137, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv79,pv971], .c 3, .c 11, .c 5, .c 3, .p pv13 [pv2,pv29,pv59,pv269], .c 7, .c 3,
  .c 5, .c 89, .c 3, .c 19, .c 17, .c 3, .c 131, .p pv7 [pv2,pv3,pv17047], .c 3, .c 13, .c 5,
  .c 3, .c 7, .c 61, .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv37,pv311], .c 7, .c 3, .c 17,
  .c 13, .c 3, .c 41, .c 5, .c 3,
]
private theorem h0112c11 : checkBlock 920323 128 b0112c11 = true := by
  decide +kernel

private def b0112c12 : List Row := [
  .c 11, .c 197, .c 3, .c 5, .c 43, .c 3, .c 7, .c 211, .c 3, .c 37, .c 283, .c 3, .c 73, .c 5,
  .c 3, .p pv3 [pv2,pv13,pv2213], .c 113, .c 3, .c 5, .c 461, .c 3, .c 13, .c 11, .c 3, .c 97,
  .c 631, .c 3, .c 7, .c 5, .c 3, .c 929, .p pv23 [pv2,pv3,pv5,pv7,pv137], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv18413], .p pv5 [pv2,pv3,pv17,pv4513], .c 3, .c 71, .c 409, .c 3, .c 29, .c 5,
  .c 3, .c 17, .c 37, .c 3, .c 5, .p pv2 [pv2,pv3,pv73,pv1051], .c 3, .c 647, .c 19, .c 3,
  .p pv5 [pv2,pv13,pv17,pv2083], .c 7, .c 3, .c 307, .c 5, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv5,pv11,pv31], .c 3, .c 5, .p pv2 [pv2,pv3,pv173,pv887], .c 3, .c 11, .c 23,
  .c 3, .c 7, .c 83, .c 3, .c 109, .c 5, .c 3, .p pv3 [pv2,pv71,pv1621], .c 7, .c 3, .c 5, .c 17,
  .c 3, .p pv2 [pv2,pv5,pv19,pv2423], .p pv3 [pv2,pv3,pv153457], .c 3, .c 181, .c 73, .c 3,
  .p pv3 [pv2,pv7,pv8221], .c 5, .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv7673], .c 3, .c 5, .c 223,
  .c 3, .c 17, .c 7, .c 3, .c 11, .c 29, .c 3, .p pv13 [pv2,pv23,pv37,pv541], .c 5, .c 3,
  .p pv2 [pv2,pv11,pv17,pv1231], .p pv41 [pv2,pv3,pv5,pv13,pv787], .c 3, .c 5, .c 19, .c 3, .c 7,
  .c 13, .c 3, .p pv5 [pv2,pv460403], .c 229, .c 3, .c 59, .c 5, .c 3, .c 37, .c 11, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv51157], .c 3, .c 257, .p pv37 [pv2,pv3,pv11,pv109],
]
private theorem h0112c12 : checkBlock 920579 128 b0112c12 = true := by
  decide +kernel

private def b0112c13 : List Row := [
  .c 3, .c 29, .c 17, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv67,pv859], .c 23, .c 3, .c 5, .c 7,
  .c 3, .c 241, .p pv3 [pv2,pv3,pv17053], .c 3, .c 239, .p pv2 [pv2,pv3,pv13,pv5903], .c 3, .c 17,
  .c 5, .c 3, .c 173, .c 13, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv17,pv5417], .c 37, .c 3,
  .c 23, .c 7, .c 3, .c 79, .c 5, .c 3, .c 11, .c 19, .c 3, .c 5, .c 31, .c 3,
  .p pv3 [pv2,pv5,pv7,pv11,pv13,pv23], .c 103, .c 3, .c 7, .c 593, .c 3, .c 13, .c 5, .c 3,
  .c 227, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv11807], .c 3, .p pv11 [pv2,pv5,pv113,pv163],
  .c 11, .c 3, .p pv2 [pv2,pv230239], .c 13, .c 3, .p pv2 [pv2,pv7,pv157,pv419], .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv379], .c 3, .c 5, .c 353, .c 3, .c 53, .c 7, .c 3, .c 19, .c 23, .c 3,
  .c 503, .c 5, .c 3, .p pv7 [pv2,pv13,pv35423], .p pv19 [pv2,pv3,pv5,pv307], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv19,pv2693], .c 3, .c 7, .p pv2 [pv2,pv3,pv23,pv47,pv71], .c 3, .c 43, .c 11,
  .c 3, .c 571, .c 5, .c 3, .p pv2 [pv2,pv230257], .p pv3 [pv2,pv3,pv5,pv11,pv2791], .c 3, .c 5,
  .c 13, .c 3, .c 11, .c 17, .c 3, .c 431, .c 59, .c 3, .c 7, .c 5, .c 3, .c 47, .c 79, .c 3,
  .c 5, .c 7, .c 3, .c 937, .p pv5 [pv2,pv3,pv31,pv619], .c 3, .c 17, .p pv3 [pv2,pv3,pv37,pv461],
  .c 3, .c 71, .c 5, .c 3, .c 13,
]
private theorem h0112c13 : checkBlock 920835 128 b0112c13 = true := by
  decide +kernel

private def b0112c14 : List Row := [
  .p pv13 [pv2,pv3,pv5,pv30703], .c 3, .c 5, .c 401, .c 3, .c 19, .c 31, .c 3, .c 11, .c 7, .c 3,
  .c 163, .c 5, .c 3, .c 157, .p pv13 [pv2,pv3,pv5,pv19,pv101], .c 3, .c 5, .c 23, .c 3, .c 127,
  .p pv2 [pv2,pv3,pv2843], .c 3, .c 7, .c 19, .c 3, .p pv5 [pv2,pv460571], .c 5, .c 3,
  .p pv2 [pv2,pv421,pv547], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv29,pv2647], .c 3, .c 61, .c 107,
  .c 3, .c 13, .p pv11 [pv2,pv3,pv6397], .c 3, .c 11, .c 5, .c 3, .c 7, .c 617, .c 3, .c 5, .c 73,
  .c 3, .p pv13 [pv2,pv5,pv92119], .c 7, .c 3, .p pv2 [pv2,pv17,pv19,pv23,pv31],
  .p pv3 [pv2,pv3,pv153533], .c 3, .p pv2 [pv2,pv317,pv1453], .c 5, .c 3, .c 97, .c 569, .c 3,
  .c 5, .c 11, .c 3, .c 7, .p pv3 [pv2,pv3,pv61,pv839], .c 3, .c 31, .c 41, .c 3,
  .p pv3 [pv2,pv13,pv43,pv103], .c 5, .c 3, .c 11, .p pv11 [pv2,pv3,pv5,pv853], .c 3, .c 5, .c 17,
  .c 3, .c 151, .c 19, .c 3, .p pv5 [pv2,pv7,pv16451], .p pv2 [pv2,pv3,pv13,pv31,pv127], .c 3,
  .c 7, .c 5, .c 3, .c 757, .c 13, .c 3, .c 5, .c 7, .c 3, .c 17, .c 11, .c 3,
  .p pv5 [pv2,pv460643], .c 31, .c 3, .p pv2 [pv2,pv139,pv1657], .c 5, .c 3, .c 53, .c 29, .c 3,
  .c 5, .c 307, .c 3, .c 23, .c 179, .c 3, .c 67, .c 7, .c 3, .c 13, .c 5, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv5,pv29,pv353], .c 3, .c 5, .c 37, .c 3, .c 47, .c 241, .c 3,
]
private theorem h0112c14 : checkBlock 921091 128 b0112c14 = true := by
  decide +kernel

private def b0112c15 : List Row := [
  .c 7, .c 11, .c 3, .p pv3 [pv2,pv41,pv53], .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .c 19, .c 3,
  .c 11, .p pv2 [pv2,pv3,pv76781], .c 3, .c 79, .p pv2 [pv2,pv3,pv153563], .c 3, .c 17, .c 5,
  .c 3, .c 7, .c 467, .c 3, .c 5, .c 677, .c 3, .c 13, .c 7, .c 3, .p pv5 [pv2,pv73,pv6311],
  .p pv13 [pv2,pv3,pv4799], .c 3, .c 31, .c 5, .c 3, .c 643, .c 251, .c 3, .c 5, .c 13, .c 3,
  .c 7, .c 157, .c 3, .c 11, .c 163, .c 3, .c 19, .c 5, .c 3, .c 23, .c 17, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv79], .c 3, .c 439, .p pv3 [pv2,pv3,pv19,pv59,pv137], .c 3,
  .p pv2 [pv2,pv7,pv13,pv61,pv83], .c 577, .c 3, .c 7, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 7,
  .c 3, .p pv7 [pv2,pv5,pv43,pv2143], .c 311, .c 3, .p pv3 [pv2,pv229,pv503],
  .p pv3 [pv2,pv3,pv383,pv401], .c 3, .c 11, .c 5, .c 3, .c 71, .c 53, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv41,pv1873], .c 3, .c 59, .p pv2 [pv2,pv3,pv7,pv37,pv593], .c 3, .c 61, .c 7,
  .c 3, .c 29, .c 5, .c 3, .c 461, .c 23, .c 3, .c 5, .c 11, .c 3, .c 953, .c 17, .c 3, .c 7,
  .c 37, .c 3, .p pv2 [pv2,pv29,pv15889], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 787, .c 3,
  .p pv2 [pv2,pv5,pv11,pv59,pv71], .c 13, .c 3, .c 17, .p pv2 [pv2,pv3,pv61,pv1259], .c 3, .c 887,
  .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5],
]
private theorem h0112c15 : checkBlock 921347 128 b0112c15 = true := by
  decide +kernel

private def b0112c16 : List Row := [
  .c 3, .c 5, .c 491, .c 3, .p pv11 [pv2,pv5,pv23,pv4007], .c 7, .c 3, .c 53, .c 43, .c 3, .c 47,
  .c 5, .c 3, .p pv2 [pv2,pv113,pv2039], .c 563, .c 3, .c 5, .p pv2 [pv2,pv3,pv25601], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv153607], .c 3, .p pv5 [pv2,pv11,pv41893], .c 29, .c 3, .c 499, .c 5, .c 3,
  .c 223, .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv153611], .c 3, .c 19, .c 167, .c 3,
  .p pv2 [pv2,pv7,pv32917], .c 11, .c 3, .c 7, .c 5, .c 3, .c 17, .c 619, .c 3, .c 5, .c 7, .c 3,
  .c 11, .p pv3 [pv2,pv3,pv23,pv6679], .c 3, .c 29, .c 19, .c 3, .c 13, .c 5, .c 3, .c 67, .c 41,
  .c 3, .c 5, .c 877, .c 3, .c 283, .p pv5 [pv2,pv3,pv7,pv10973], .c 3, .p pv3 [pv2,pv29,pv137],
  .c 7, .c 3, .p pv5 [pv2,pv460871], .c 5, .c 3, .p pv3 [pv2,pv23,pv43,pv233],
  .p pv23 [pv2,pv3,pv5,pv1229], .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv7,pv823], .c 197, .c 3,
  .c 7, .c 457, .c 3, .c 89, .c 5, .c 3, .p pv2 [pv2,pv11,pv13,pv293], .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv67,pv2293], .c 3, .c 13, .c 71, .c 3, .c 449, .c 509, .c 3, .c 41, .c 5, .c 3,
  .c 7, .c 11, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv46091], .c 7, .c 3, .c 101, .c 53, .c 3,
  .c 11, .c 5, .c 3, .p pv7 [pv2,pv460919], .p pv43 [pv2,pv3,pv5,pv23,pv167], .c 3, .c 5, .c 31,
  .c 3, .c 7, .c 67, .c 3, .c 433,
]
private theorem h0112c16 : checkBlock 921603 128 b0112c16 = true := by
  decide +kernel

private def b0112c17 : List Row := [
  .c 17, .c 3, .c 23, .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv10243], .c 3, .c 5, .c 11, .c 3,
  .c 29, .c 443, .c 3, .p pv7 [pv2,pv7,pv23,pv409], .p pv29 [pv2,pv3,pv11,pv97], .c 3, .c 7, .c 5,
  .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv7,pv439], .c 3, .c 5, .c 7, .c 3,
  .p pv31 [pv2,pv5,pv11,pv17,pv29], .p pv5 [pv2,pv3,pv107,pv359], .c 3, .c 73,
  .p pv3 [pv2,pv3,pv19,pv8087], .c 3, .c 251, .c 5, .c 3, .c 37, .p pv3 [pv2,pv3,pv5,pv79,pv389],
  .c 3, .c 5, .c 19, .c 3, .c 659, .c 11, .c 3, .c 13, .c 7, .c 3, .c 103, .c 5, .c 3,
  .p pv11 [pv2,pv460979], .c 17, .c 3, .c 5, .c 41, .c 3, .c 31, .c 13, .c 3, .c 7, .c 347, .c 3,
  .c 821, .c 5, .c 3, .p pv2 [pv2,pv53,pv4349], .c 7, .c 3, .c 5, .c 29, .c 3, .c 23, .c 37, .c 3,
  .c 167, .c 11, .c 3, .c 19, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv11,pv127], .c 3, .c 5,
  .p pv7 [pv2,pv3,pv7,pv29,pv757], .c 3, .c 11, .c 7, .c 3, .p pv2 [pv2,pv353,pv653],
  .p pv59 [pv2,pv3,pv13,pv11821], .c 3, .p pv2 [pv2,pv11,pv41911], .c 5, .c 3, .c 41, .c 13, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv103,pv373], .c 3, .c 7, .c 17, .c 3, .p pv2 [pv2,pv241,pv1913],
  .p pv13 [pv2,pv3,pv7,pv3659], .c 3, .p pv3 [pv2,pv115259], .c 5, .c 3,
  .p pv7 [pv2,pv263,pv1753], .p pv7 [pv2,pv3,pv5,pv17,pv113], .c 3, .c 5,
  .p pv11 [pv2,pv3,pv11,pv4657], .c 3, .c 163, .c 23, .c 3, .c 11, .p pv2 [pv2,pv3,pv313,pv491],
  .c 3, .c 7, .c 5, .c 3, .c 131, .c 59, .c 3,
]
private theorem h0112c17 : checkBlock 921859 128 b0112c17 = true := by
  decide +kernel

private def b0112c18 : List Row := [
  .c 5, .c 7, .c 3, .c 67, .p pv2 [pv2,pv3,pv51229], .c 3, .c 19, .c 13, .c 3, .c 277, .c 5, .c 3,
  .c 23, .c 11, .c 3, .c 5, .c 53, .c 3, .c 37, .c 317, .c 3, .c 31, .c 7, .c 3, .c 11, .c 5,
  .c 3, .p pv3 [pv2,pv13,pv8867], .c 29, .c 3, .c 5, .c 587, .c 3, .c 13, .c 229, .c 3, .c 7,
  .c 773, .c 3, .c 113, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv92221], .c 41, .c 3, .p pv3 [pv2,pv17,pv6781], .c 31, .c 3,
  .p pv5 [pv2,pv7,pv19,pv3467], .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv10979],
  .c 3, .c 19, .c 7, .c 3, .p pv7 [pv2,pv13,pv79,pv449], .c 109, .c 3, .c 53, .c 5, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv5,pv19,pv809], .c 3, .c 5, .c 17, .c 3, .c 7, .c 11, .c 3, .c 23, .c 19, .c 3,
  .p pv2 [pv2,pv73,pv6317], .c 5, .c 3, .p pv3 [pv2,pv59,pv977], .p pv2 [pv2,pv3,pv5,pv71,pv433],
  .c 3, .c 5, .c 283, .c 3, .c 17, .p pv3 [pv2,pv3,pv51239], .c 3, .c 43,
  .p pv2 [pv2,pv3,pv151,pv509], .c 3, .c 7, .c 5, .c 3, .c 389, .p pv17 [pv2,pv3,pv5,pv7,pv61],
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv92233], .p pv2 [pv2,pv3,pv101,pv761], .c 3, .c 13,
  .c 11, .c 3, .c 31, .c 5, .c 3, .c 569, .p pv43 [pv2,pv3,pv5,pv11,pv13,pv43], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv25621], .c 3, .c 11, .c 13, .c 3, .p pv5 [pv2,pv461183], .c 7,
]
private theorem h0112c18 : checkBlock 922115 128 b0112c18 = true := by
  decide +kernel

private def b0112c19 : List Row := [
  .c 3, .c 37, .c 5, .c 3, .c 83, .c 61, .c 3, .c 5, .c 179, .c 3, .p pv7 [pv2,pv5,pv7,pv13177],
  .c 19, .c 3, .c 7, .c 641, .c 3, .c 17, .c 5, .c 3, .c 709, .c 7, .c 3, .c 5, .c 163, .c 3,
  .c 137, .p pv17 [pv2,pv3,pv47,pv3271], .c 3, .c 11, .c 373, .c 3, .c 101, .c 5, .c 3, .c 7,
  .c 13, .c 3, .c 5, .c 37, .c 3, .p pv17 [pv2,pv5,pv19,pv971], .c 7, .c 3,
  .p pv3 [pv2,pv67,pv1721], .c 41, .c 3, .p pv5 [pv2,pv83,pv5557], .c 5, .c 3, .c 19, .c 11, .c 3,
  .c 5, .c 719, .c 3, .c 7, .c 79, .c 3, .p pv5 [pv2,pv379,pv1217],
  .p pv11 [pv2,pv3,pv7,pv17,pv19], .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv31,pv14879], .c 73,
  .c 3, .c 5, .c 19, .c 3, .p pv7 [pv2,pv5,pv92251], .p pv5 [pv2,pv3,pv19219], .c 3,
  .p pv2 [pv2,pv7,pv47,pv701], .c 13, .c 3, .c 7, .c 5, .c 3, .c 31,
  .p pv2 [pv2,pv3,pv5,pv7,pv23,pv191], .c 3, .c 5, .c 7, .c 3, .c 41, .c 139, .c 3, .c 863,
  .p pv23 [pv2,pv3,pv11,pv29,pv241], .c 3, .c 23, .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv31],
  .c 3, .c 5, .c 97, .c 3, .c 13, .c 17, .c 3, .c 29, .c 7, .c 3, .c 19, .c 5, .c 3, .c 491,
  .c 31, .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv7,pv659], .c 11, .c 3, .c 7, .c 173, .c 3,
  .p pv2 [pv2,pv230653], .c 5, .c 3, .p pv2 [pv2,pv461309], .c 7, .c 3, .c 5,
]
private theorem h0112c19 : checkBlock 922371 128 b0112c19 = true := by
  decide +kernel

private def b0112c20 : List Row := [
  .p pv2 [pv2,pv3,pv51257], .c 3, .p pv13 [pv2,pv5,pv257,pv359], .c 131, .c 3,
  .p pv2 [pv2,pv11,pv13,pv1613], .p pv7 [pv2,pv3,pv367,pv419], .c 3, .p pv2 [pv2,pv7,pv59,pv1117],
  .c 5, .c 3, .c 7, .c 43, .c 3, .c 5, .c 47, .c 3, .c 107, .c 7, .c 3, .p pv2 [pv2,pv461333],
  .c 11, .c 3, .c 347, .c 5, .c 3, .p pv7 [pv2,pv19,pv24281], .p pv13 [pv2,pv3,pv5,pv11,pv233],
  .c 3, .c 5, .c 277, .c 3, .c 7, .c 29, .c 3, .c 19, .p pv7 [pv2,pv3,pv7,pv2441], .c 3, .c 211,
  .c 5, .c 3, .c 17, .c 83, .c 3, .c 5, .p pv2 [pv2,pv3,pv19,pv71], .c 3, .c 191, .c 433, .c 3,
  .c 13, .p pv7 [pv2,pv3,pv38447], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv181,pv2549],
  .p pv29 [pv2,pv3,pv5,pv7,pv13], .c 3, .c 5, .c 7, .c 3, .c 29, .c 13, .c 3, .c 11, .c 463, .c 3,
  .c 199, .c 5, .c 3, .c 443, .c 431, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv29,pv37,pv43],
  .c 23, .c 3, .c 41, .c 7, .c 3, .c 73, .c 5, .c 3, .c 79, .c 11, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv23,pv743], .c 3, .c 17, .p pv7 [pv2,pv3,pv11,pv6991], .c 3, .c 7, .c 59, .c 3,
  .c 11, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 101, .c 3, .c 89, .c 911, .c 3, .c 733, .c 19,
  .c 3, .p pv2 [pv2,pv7,pv23,pv1433], .c 5, .c 3, .c 7, .p pv61 [pv2,pv3,pv5,pv1709], .c 3, .c 5,
  .c 11, .c 3, .c 113, .c 7, .c 3, .c 83, .c 17, .c 3,
]
private theorem h0112c20 : checkBlock 922627 128 b0112c20 = true := by
  decide +kernel

private def b0112c21 : List Row := [
  .c 13, .c 5, .c 3, .c 11, .c 37, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv17,pv29], .c 3, .c 7,
  .c 109, .c 3, .p pv2 [pv2,pv19,pv149,pv163], .c 13, .c 3, .c 17, .c 5, .c 3, .c 181, .c 23,
  .c 3, .c 5, .c 251, .c 3, .p pv2 [pv2,pv5,pv17,pv61,pv89], .c 11, .c 3, .c 59, .c 47, .c 3,
  .c 7, .c 5, .c 3, .c 557, .c 41, .c 3, .c 5, .c 7, .c 3, .c 13, .c 19, .c 3, .c 23, .c 137,
  .c 3, .p pv2 [pv2,pv230743], .c 5, .c 3, .c 751, .c 17, .c 3, .c 5, .c 13, .c 3, .c 61,
  .p pv29 [pv2,pv3,pv7,pv41,pv67], .c 3, .c 223, .c 7, .c 3, .c 157, .c 5, .c 3, .c 167, .c 739,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv38459], .c 3, .c 11, .p pv3 [pv2,pv3,pv17093], .c 3, .c 7,
  .p pv11 [pv2,pv3,pv76919], .c 3, .c 41, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv153841], .c 3, .p pv2 [pv2,pv5,pv18461], .p pv5 [pv2,pv3,pv13,pv61,pv97],
  .c 3, .c 419, .c 23, .c 3, .c 151, .c 5, .c 3, .c 7, .c 71, .c 3, .c 5, .c 19, .c 3, .c 43,
  .c 7, .c 3, .c 11, .c 107, .c 3, .c 761, .c 5, .c 3, .c 29, .c 53, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv137,pv1123], .c 3, .c 7, .c 37, .c 3, .c 13, .c 193, .c 3,
  .p pv2 [pv2,pv461561], .c 5, .c 3, .p pv3 [pv2,pv23,pv29,pv173], .c 11, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv601],
]
private theorem h0112c21 : checkBlock 922883 128 b0112c21 = true := by
  decide +kernel

private def b0112c22 : List Row := [
  .c 3, .p pv3 [pv2,pv5,pv101,pv457], .c 13, .c 3, .p pv2 [pv2,pv7,pv233,pv283], .c 31, .c 3,
  .c 7, .c 5, .c 3, .c 331, .c 199, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv92317], .c 59, .c 3,
  .p pv3 [pv2,pv167,pv691], .p pv3 [pv2,pv3,pv251,pv613], .c 3, .p pv5 [pv2,pv13,pv35507], .c 5,
  .c 3, .c 103, .c 19, .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv577],
  .p pv2 [pv2,pv3,pv7,pv17,pv431], .c 3, .c 53, .c 7, .c 3, .c 71, .c 5, .c 3, .c 11, .c 13, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv153871], .c 3, .c 73, .p pv7 [pv2,pv3,pv59,pv163], .c 3, .c 7,
  .p pv3 [pv2,pv3,pv41,pv139], .c 3, .c 23, .c 5, .c 3, .p pv3 [pv2,pv19,pv3037], .c 7, .c 3,
  .c 5, .c 239, .c 3, .c 37, .c 11, .c 3, .c 19, .c 647, .c 3, .c 13, .c 5, .c 3, .c 7, .c 181,
  .c 3, .c 5, .c 17, .c 3, .c 59, .c 7, .c 3, .c 271, .c 13, .c 3, .c 107, .c 5, .c 3,
  .p pv2 [pv2,pv230827], .p pv7 [pv2,pv3,pv5,pv10259], .c 3, .c 5, .c 157, .c 3, .c 7, .c 113,
  .c 3, .c 67, .c 11, .c 3, .p pv2 [pv2,pv230833], .c 5, .c 3, .c 43,
  .p pv7 [pv2,pv3,pv5,pv11,pv1399], .c 3, .c 5, .p pv2 [pv2,pv3,pv17099], .c 3, .c 11, .c 149,
  .c 3, .c 61, .c 311, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv115421],
  .p pv13 [pv2,pv3,pv5,pv7,pv4397], .c 3, .c 5, .c 7, .c 3, .c 19, .c 461, .c 3,
  .p pv2 [pv2,pv461693], .c 17, .c 3, .c 263,
]
private theorem h0112c22 : checkBlock 923139 128 b0112c22 = true := by
  decide +kernel

private def b0112c23 : List Row := [
  .c 5, .c 3, .p pv7 [pv2,pv7,pv65957], .c 257, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv17,pv823],
  .c 3, .p pv2 [pv2,pv5,pv107,pv863], .c 383, .c 3, .c 11, .c 7, .c 3, .c 17, .c 5, .c 3, .c 13,
  .c 79, .c 3, .c 5, .p pv2 [pv2,pv3,pv113,pv227], .c 3, .p pv11 [pv2,pv5,pv7,pv17,pv97], .c 41,
  .c 3, .c 7, .p pv23 [pv2,pv3,pv109,pv353], .c 3, .p pv2 [pv2,pv230863], .c 5, .c 3, .c 31, .c 7,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv153911], .c 3, .p pv41 [pv2,pv5,pv92347], .c 23, .c 3, .c 269,
  .c 61, .c 3, .c 11, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 71, .c 3, .p pv2 [pv2,pv5,pv1847],
  .c 7, .c 3, .c 13, .p pv2 [pv2,pv3,pv17,pv503], .c 3, .p pv3 [pv2,pv241,pv479], .c 5, .c 3,
  .c 23, .c 31, .c 3, .c 5, .c 11, .c 3, .c 7, .c 13, .c 3, .c 97,
  .p pv2 [pv2,pv3,pv7,pv11,pv1999], .c 3, .p pv5 [pv2,pv17,pv23,pv1181], .c 5, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv5,pv47,pv131], .c 3, .c 5, .c 37, .c 3, .p pv29 [pv2,pv5,pv11,pv2099], .c 29,
  .c 3, .p pv5 [pv2,pv7,pv41,pv1609], .c 769, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv53,pv8713],
  .p pv2 [pv2,pv3,pv5,pv7,pv733], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv19,pv4861], .c 11,
  .c 3, .c 43, .p pv3 [pv2,pv3,pv13,pv3947], .c 3, .p pv2 [pv2,pv461801], .c 5, .c 3, .c 19,
  .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv1069], .c 3, .c 29, .c 379, .c 3, .c 17, .c 7, .c 3,
  .c 431, .c 5, .c 3, .c 71, .p pv7 [pv2,pv3,pv5,pv43,pv179], .c 3, .c 5, .c 19, .c 3,
]
private theorem h0112c23 : checkBlock 923395 128 b0112c23 = true := by
  decide +kernel

private def b0112c24 : List Row := [
  .c 149, .p pv2 [pv2,pv3,pv25657], .c 3, .c 7, .c 11, .c 3, .c 13, .c 5, .c 3, .c 73, .c 7, .c 3,
  .c 5, .c 167, .c 3, .c 11, .c 43, .c 3, .p pv5 [pv2,pv461843], .c 13, .c 3,
  .p pv5 [pv2,pv7,pv11,pv2999], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv3079], .c 3, .c 5, .c 31,
  .c 3, .p pv19 [pv2,pv5,pv71,pv1301], .c 7, .c 3, .c 337, .p pv11 [pv2,pv3,pv153953], .c 3,
  .c 19, .c 5, .c 3, .c 17, .c 89, .c 3, .c 5, .c 29, .c 3, .c 7, .p pv3 [pv2,pv3,pv19,pv37,pv73],
  .c 3, .c 11, .c 23, .c 3, .c 241, .c 5, .c 3, .c 827, .c 19, .c 3, .c 5, .c 13, .c 3, .c 41,
  .p pv2 [pv2,pv3,pv23,pv3347], .c 3, .c 577, .c 37, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv157,pv1471], .c 11, .c 3, .c 5, .c 7, .c 3, .c 353, .c 349, .c 3, .c 103,
  .p pv11 [pv2,pv3,pv9623], .c 3, .c 11, .c 5, .c 3, .c 13, .c 331, .c 3, .c 5, .c 709, .c 3,
  .c 17, .p pv19 [pv2,pv3,pv7,pv13,pv47], .c 3, .c 19, .c 7, .c 3, .c 53, .c 5, .c 3,
  .p pv3 [pv2,pv17,pv6793], .p pv2 [pv2,pv3,pv5,pv2053], .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv7,pv6599], .c 67, .c 3, .c 7, .p pv23 [pv2,pv3,pv11,pv2333], .c 3, .c 83,
  .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 23, .c 3, .c 193, .c 31, .c 3, .c 13, .c 17, .c 3,
  .p pv5 [pv2,pv7,pv65993], .c 5,
]
private theorem h0112c24 : checkBlock 923651 128 b0112c24 = true := by
  decide +kernel

private def b0112c25 : List Row := [
  .c 3, .c 7, .c 29, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv17,pv647], .c 3, .c 373, .c 7, .c 3, .c 37,
  .p pv7 [pv2,pv3,pv137,pv281], .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv587,pv787], .c 43, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv153991], .c 3, .c 7, .p pv5 [pv2,pv3,pv19249], .c 3, .c 199,
  .p pv3 [pv2,pv3,pv7,pv7333], .c 3, .p pv2 [pv2,pv13,pv35537], .c 5, .c 3, .c 29,
  .p pv19 [pv2,pv3,pv5,pv19,pv1621], .c 3, .c 5, .p pv5 [pv2,pv3,pv41,pv313], .c 3, .c 311,
  .p pv3 [pv2,pv3,pv153997], .c 3, .p pv5 [pv2,pv7,pv31,pv2129], .c 11, .c 3, .c 7, .c 5, .c 3,
  .c 59, .c 13, .c 3, .c 5, .c 7, .c 3, .c 11, .c 103, .c 3, .c 31, .p pv3 [pv2,pv3,pv17,pv9059],
  .c 3, .p pv5 [pv2,pv11,pv97,pv433], .c 5, .c 3, .c 673, .p pv11 [pv2,pv3,pv5,pv10267], .c 3,
  .c 5, .p pv2 [pv2,pv3,pv77003], .c 3, .p pv11 [pv2,pv5,pv13,pv1777], .p pv3 [pv2,pv3,pv7,pv449],
  .c 3, .c 163, .c 7, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv41,pv59,pv191], .c 347, .c 3, .c 5,
  .c 47, .c 3, .c 23, .p pv5 [pv2,pv3,pv139,pv277], .c 3, .c 7, .c 13, .c 3,
  .p pv2 [pv2,pv462041], .c 5, .c 3, .c 61, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv4813], .c 3,
  .p pv2 [pv2,pv5,pv9241], .c 17, .c 3, .c 73, .p pv2 [pv2,pv3,pv53,pv1453], .c 3, .c 43, .c 5,
  .c 3, .c 7, .c 11, .c 3, .c 5, .c 197, .c 3, .c 13, .c 7, .c 3, .c 17, .p pv3 [pv2,pv3,pv51341],
  .c 3, .c 11, .c 5, .c 3, .c 37, .p pv3 [pv2,pv3,pv5,pv61,pv101], .c 3, .c 5, .c 13, .c 3, .c 7,
]
private theorem h0112c25 : checkBlock 923907 128 b0112c25 = true := by
  decide +kernel

private def b0112c26 : List Row := [
  .c 23, .c 3, .c 619, .c 881, .c 3, .p pv2 [pv2,pv29,pv31,pv257], .c 5, .c 3, .c 19, .c 41, .c 3,
  .c 5, .c 11, .c 3, .p pv7 [pv2,pv5,pv92419], .c 467, .c 3, .p pv2 [pv2,pv7,pv13,pv2539], .c 43,
  .c 3, .c 7, .c 5, .c 3, .c 11, .c 61, .c 3, .c 5, .c 7, .c 3, .c 79, .c 37, .c 3, .c 113,
  .c 823, .c 3, .c 907, .c 5, .c 3, .c 17, .p pv11 [pv2,pv3,pv5,pv3851], .c 3, .c 5, .c 149, .c 3,
  .c 101, .c 11, .c 3, .c 599, .c 7, .c 3, .c 41, .c 5, .c 3, .p pv2 [pv2,pv231067], .c 151, .c 3,
  .c 5, .c 193, .c 3, .p pv43 [pv2,pv5,pv7,pv3301], .p pv17 [pv2,pv3,pv51349], .c 3, .c 7, .c 313,
  .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv462149], .c 7, .c 3, .c 5, .c 17, .c 3, .c 233, .c 13,
  .c 3, .c 29, .c 11, .c 3, .p pv2 [pv2,pv7,pv103,pv641], .c 5, .c 3, .c 7, .c 19, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv131], .c 3, .c 11, .c 7, .c 3, .c 23, .c 47, .c 3, .c 59, .c 5, .c 3,
  .p pv7 [pv2,pv17,pv31,pv877], .p pv23 [pv2,pv3,pv5,pv7703], .c 3, .c 5, .c 181, .c 3, .c 7,
  .c 53, .c 3, .c 307, .c 79, .c 3, .p pv5 [pv2,pv462191], .c 5, .c 3, .c 31, .c 13, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv47,pv149], .c 3, .p pv3 [pv2,pv5,pv2311], .p pv2 [pv2,pv3,pv154067],
  .c 3, .c 11, .c 17, .c 3, .c 7, .c 5, .c 3,
]
private theorem h0112c26 : checkBlock 924163 128 b0112c26 = true := by
  decide +kernel

private def b0112c27 : List Row := [
  .p pv2 [pv2,pv11,pv42019], .p pv17 [pv2,pv3,pv5,pv7,pv31,pv71], .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv13,pv547], .c 29, .c 3, .p pv2 [pv2,pv231109], .c 23, .c 3, .c 13, .c 5, .c 3,
  .c 571, .c 11, .c 3, .c 5, .c 43, .c 3, .c 607, .p pv3 [pv2,pv3,pv7,pv11,pv23,pv29], .c 3,
  .c 131, .c 7, .c 3, .c 11, .c 5, .c 3, .c 53, .c 751, .c 3, .c 5, .c 593, .c 3, .c 29,
  .p pv5 [pv2,pv3,pv77041], .c 3, .c 7, .p pv11 [pv2,pv3,pv51361], .c 3,
  .p pv5 [pv2,pv19,pv24329], .c 5, .c 3, .c 41, .c 7, .c 3, .c 5, .c 11, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv154087], .c 3, .p pv5 [pv2,pv462263], .p pv23 [pv2,pv3,pv11,pv17,pv103], .c 3,
  .c 67, .c 5, .c 3, .c 7, .c 443, .c 3, .c 5, .c 13, .c 3, .p pv19 [pv2,pv5,pv11,pv41], .c 7,
  .c 3, .p pv2 [pv2,pv37,pv6247], .c 19, .c 3, .c 647, .c 5, .c 3, .c 541, .c 227, .c 3, .c 5,
  .c 23, .c 3, .c 7, .c 11, .c 3, .c 107, .c 59, .c 3, .c 37, .c 5, .c 3, .c 13,
  .p pv11 [pv2,pv3,pv5,pv23,pv67], .c 3, .c 5, .c 29, .c 3, .c 463, .c 17, .c 3,
  .p pv3 [pv2,pv7,pv11,pv19,pv79], .c 701, .c 3, .c 7, .c 5, .c 3, .c 43, .c 47, .c 3, .c 5, .c 7,
  .c 3, .p pv3 [pv2,pv5,pv5779], .p pv3 [pv2,pv3,pv17123], .c 3, .c 17, .c 11, .c 3, .c 389, .c 5,
  .c 3, .p pv2 [pv2,pv7,pv66047], .p pv2 [pv2,pv3,pv5,pv11,pv467], .c 3, .c 5, .c 37, .c 3, .c 11,
  .c 19,
]
private theorem h0112c27 : checkBlock 924419 128 b0112c27 = true := by
  decide +kernel

private def b0112c28 : List Row := [
  .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv11,pv3821], .c 5, .c 3, .c 317, .c 53, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv1427], .c 3, .c 97, .c 13, .c 3, .c 7, .p pv2 [pv2,pv3,pv263,pv293], .c 3,
  .p pv3 [pv2,pv115589], .c 5, .c 3, .p pv11 [pv2,pv197,pv2347], .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv14011], .c 3, .p pv2 [pv2,pv5,pv19,pv31,pv157], .c 419, .c 3, .c 11,
  .c 661, .c 3, .p pv7 [pv2,pv7,pv13,pv5081], .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv137], .c 3,
  .c 5, .p pv2 [pv2,pv3,pv7,pv101,pv109], .c 3, .c 23, .c 7, .c 3, .c 139,
  .p pv11 [pv2,pv3,pv13,pv19], .c 3, .p pv2 [pv2,pv47,pv4919], .c 5, .c 3,
  .p pv2 [pv2,pv37,pv12497], .c 11, .c 3, .c 5, .c 19, .c 3, .c 7,
  .p pv17 [pv2,pv3,pv11,pv31,pv113], .c 3, .c 53, .c 89, .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv115601], .p pv17 [pv2,pv3,pv5,pv29,pv1063], .c 3, .c 5, .c 17, .c 3, .c 61, .c 31,
  .c 3, .p pv2 [pv2,pv7,pv9437], .p pv2 [pv2,pv3,pv77069], .c 3, .c 7, .c 5, .c 3, .c 29,
  .p pv13 [pv2,pv3,pv5,pv7,pv367], .c 3, .c 5, .c 7, .c 3, .c 17, .c 23, .c 3, .c 101, .c 13,
  .c 3, .c 19, .c 5, .c 3, .c 11, .p pv29 [pv2,pv3,pv5,pv30829], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv23,pv1117], .c 3, .p pv3 [pv2,pv5,pv11,pv1051], .c 617, .c 3, .c 43, .c 7,
  .c 3, .c 179, .c 5, .c 3, .c 23, .c 19, .c 3, .c 5, .p pv2 [pv2,pv3,pv139,pv1109], .c 3, .c 13,
  .c 11, .c 3, .c 7, .c 17, .c 3, .c 271, .c 5, .c 3, .p pv3 [pv2,pv3613],
]
private theorem h0112c28 : checkBlock 924675 128 b0112c28 = true := by
  decide +kernel

private def b0112c29 : List Row := [
  .c 7, .c 3, .c 5, .c 13, .c 3, .c 127, .c 59, .c 3, .c 31, .c 479, .c 3, .c 17, .c 5, .c 3,
  .c 7, .p pv13 [pv2,pv3,pv5,pv41,pv47], .c 3, .c 5, .p pv7 [pv2,pv3,pv7,pv2447], .c 3, .c 263,
  .c 7, .c 3, .c 19, .c 11, .c 3, .c 73, .c 5, .c 3, .c 13, .c 23, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv19,pv4057], .c 3, .c 7, .c 941, .c 3, .c 47, .c 31, .c 3, .c 29, .c 5, .c 3,
  .p pv2 [pv2,pv113,pv4093], .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv151,pv1021], .c 3, .c 173,
  .p pv5 [pv2,pv3,pv38543], .c 3, .c 23, .p pv11 [pv2,pv3,pv17,pv3023], .c 3, .c 7, .c 5, .c 3,
  .c 193, .p pv2 [pv2,pv3,pv5,pv7,pv881], .c 3, .c 5, .c 7, .c 3, .c 59,
  .p pv3 [pv2,pv3,pv53,pv2909], .c 3, .c 11, .c 67, .c 3, .p pv5 [pv2,pv17,pv19,pv179], .c 5,
  .c 3, .p pv7 [pv2,pv7,pv11,pv6007], .p pv7 [pv2,pv3,pv5,pv13,pv593], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv154181], .c 3, .c 19, .c 13, .c 3, .p pv3 [pv2,pv115637], .c 7, .c 3,
  .p pv5 [pv2,pv31,pv43,pv347], .c 5, .c 3, .p pv2 [pv2,pv231277], .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv77093], .c 3, .p pv23 [pv2,pv5,pv7,pv59], .c 17, .c 3, .c 7, .c 19, .c 3,
  .c 11, .c 5, .c 3, .c 379, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv103,pv499], .c 3, .c 199,
  .p pv5 [pv2,pv3,pv23,pv419], .c 3, .c 17, .p pv7 [pv2,pv3,pv13,pv29,pv409], .c 3,
  .p pv2 [pv2,pv7,pv66083], .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv167,pv277], .c 7, .c 3,
]
private theorem h0112c29 : checkBlock 924931 128 b0112c29 = true := by
  decide +kernel

private def b0112c30 : List Row := [
  .c 29, .p pv2 [pv2,pv3,pv11,pv43,pv163], .c 3, .p pv3 [pv2,pv109,pv1061], .c 5, .c 3, .c 11,
  .c 71, .c 3, .c 5, .c 367, .c 3, .c 7, .c 353, .c 3, .p pv3 [pv2,pv29,pv997], .c 947, .c 3,
  .c 13, .c 5, .c 3, .c 107, .c 43, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv659], .c 3,
  .p pv3 [pv2,pv5,pv23131], .c 11, .c 3, .c 41, .c 13, .c 3, .c 7, .c 5, .c 3, .c 17, .c 101,
  .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv67,pv1381], .p pv5 [pv2,pv3,pv71,pv181], .c 3, .c 643,
  .p pv3 [pv2,pv3,pv154213], .c 3, .c 97, .c 5, .c 3, .c 47, .p pv3 [pv2,pv3,pv5,pv23,pv149],
  .c 3, .c 5, .c 59, .c 3, .c 13, .c 29, .c 3, .p pv2 [pv2,pv462653], .c 7, .c 3, .c 23, .c 5,
  .c 3, .c 19, .c 433, .c 3, .c 5, .c 13, .c 3, .c 11, .c 37, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv19,pv8117], .c 3, .c 71, .c 5, .c 3, .p pv2 [pv2,pv73,pv3169], .c 7, .c 3,
  .c 5, .c 19, .c 3, .c 17, .c 953, .c 3, .c 83, .p pv19 [pv2,pv3,pv38557], .c 3,
  .p pv2 [pv2,pv7,pv33049], .c 5, .c 3, .c 7, .c 31, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv11,pv2003],
  .c 3, .p pv11 [pv2,pv5,pv29,pv3191], .c 7, .c 3, .c 11, .p pv3 [pv2,pv3,pv17137], .c 3, .c 43,
  .c 5, .c 3, .p pv3 [pv2,pv11,pv239], .c 41, .c 3, .c 5, .c 839, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv89,pv1733], .c 3, .c 443, .c 17, .c 3, .c 19, .c 5, .c 3, .c 149, .c 11,
]
private theorem h0112c30 : checkBlock 925187 128 b0112c30 = true := by
  decide +kernel

private def b0112c31 : List Row := [
  .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv43,pv211], .c 3, .c 23, .c 181, .c 3, .c 13, .c 677, .c 3,
  .c 7, .c 5, .c 3, .p pv2 [pv2,pv231367], .c 19, .c 3, .c 5, .c 7, .c 3, .c 37, .c 13, .c 3,
  .p pv5 [pv2,pv53,pv8731], .c 43, .c 3, .c 41, .c 5, .c 3, .p pv2 [pv2,pv7,pv66107],
  .p pv2 [pv2,pv3,pv5,pv617], .c 3, .c 5, .c 11, .c 3, .c 89, .p pv11 [pv2,pv3,pv7,pv787], .c 3,
  .p pv2 [pv2,pv231379], .c 7, .c 3, .p pv2 [pv2,pv13,pv35597], .c 5, .c 3, .c 11, .c 17, .c 3,
  .c 5, .c 463, .c 3, .c 313, .c 23, .c 3, .c 7, .c 199, .c 3, .c 61, .c 5, .c 3,
  .p pv13 [pv2,pv103,pv4493], .c 7, .c 3, .c 5, .c 31, .c 3, .c 47, .c 11, .c 3,
  .p pv3 [pv2,pv127,pv911], .p pv2 [pv2,pv3,pv51421], .c 3, .c 113, .c 5, .c 3, .c 7, .c 571,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv3673], .c 3, .c 139, .c 7, .c 3, .p pv5 [pv2,pv11,pv42073],
  .c 179, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv43,pv47,pv229], .p pv2 [pv2,pv3,pv5,pv15427],
  .c 3, .c 5, .c 71, .c 3, .c 7, .c 17, .c 3, .p pv2 [pv2,pv231409], .c 11, .c 3, .c 79, .c 5,
  .c 3, .p pv3 [pv2,pv57853], .c 29, .c 3, .c 5, .c 41, .c 3, .c 11, .p pv3 [pv2,pv3,pv154277],
  .c 3, .c 17, .p pv2 [pv2,pv3,pv2857], .c 3, .c 7, .c 5, .c 3, .p pv17 [pv2,pv13,pv35603], .c 23,
  .c 3, .c 5, .c 7, .c 3, .c 13, .c 283, .c 3, .p pv3 [pv2,pv113],
]
private theorem h0112c31 : checkBlock 925443 128 b0112c31 = true := by
  decide +kernel

def rows0112 : List Row :=
  b0112c00 ++ b0112c01 ++ b0112c02 ++ b0112c03 ++ b0112c04 ++ b0112c05 ++ b0112c06 ++ b0112c07 ++
  b0112c08 ++ b0112c09 ++ b0112c10 ++ b0112c11 ++ b0112c12 ++ b0112c13 ++ b0112c14 ++ b0112c15 ++
  b0112c16 ++ b0112c17 ++ b0112c18 ++ b0112c19 ++ b0112c20 ++ b0112c21 ++ b0112c22 ++ b0112c23 ++
  b0112c24 ++ b0112c25 ++ b0112c26 ++ b0112c27 ++ b0112c28 ++ b0112c29 ++ b0112c30 ++ b0112c31

theorem checked0112 : checkBlock 917507 4096 rows0112 = true :=
  checkBlock_append h0112c00 (
    checkBlock_append h0112c01 (
    checkBlock_append h0112c02 (
    checkBlock_append h0112c03 (
    checkBlock_append h0112c04 (
    checkBlock_append h0112c05 (
    checkBlock_append h0112c06 (
    checkBlock_append h0112c07 (
    checkBlock_append h0112c08 (
    checkBlock_append h0112c09 (
    checkBlock_append h0112c10 (
    checkBlock_append h0112c11 (
    checkBlock_append h0112c12 (
    checkBlock_append h0112c13 (
    checkBlock_append h0112c14 (
    checkBlock_append h0112c15 (
    checkBlock_append h0112c16 (
    checkBlock_append h0112c17 (
    checkBlock_append h0112c18 (
    checkBlock_append h0112c19 (
    checkBlock_append h0112c20 (
    checkBlock_append h0112c21 (
    checkBlock_append h0112c22 (
    checkBlock_append h0112c23 (
    checkBlock_append h0112c24 (
    checkBlock_append h0112c25 (
    checkBlock_append h0112c26 (
    checkBlock_append h0112c27 (
    checkBlock_append h0112c28 (
    checkBlock_append h0112c29 (
    checkBlock_append h0112c30 (
    h0112c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
