/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0130
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0130.checked0130
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table019
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table020
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table023
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table024
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table029
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table040
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table060
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table113
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table114

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0130c00 : List Row := [
  .c 97, .c 5, .c 3, .c 19, .c 37, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv2017], .c 3, .c 43, .c 307,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv19,pv173], .c 3, .c 251, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .c 19, .c 3, .p pv2 [pv2,pv5,pv106501], .p pv5 [pv2,pv3,pv13,pv6827], .c 3,
  .p pv3 [pv2,pv17,pv41,pv191], .p pv3 [pv2,pv3,pv139,pv1277], .c 3, .c 1031, .c 5, .c 3, .c 7,
  .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv31,pv409], .c 3, .p pv3 [pv2,pv5,pv13313], .c 7, .c 3,
  .p pv5 [pv2,pv532523], .c 733, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv532529], .c 23, .c 3,
  .c 5, .c 17, .c 3, .c 7, .p pv5 [pv2,pv3,pv22189], .c 3, .c 13, .c 229, .c 3, .c 19, .c 5, .c 3,
  .p pv3 [pv2,pv53,pv157], .p pv11 [pv2,pv3,pv5,pv13,pv2731], .c 3, .c 5, .c 11, .c 3, .c 17,
  .c 13, .c 3, .c 23, .p pv2 [pv2,pv3,pv11,pv8069], .c 3, .c 7, .c 5, .c 3, .c 11, .c 19, .c 3,
  .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv11,pv23,pv421], .p pv2 [pv2,pv3,pv29587], .c 3,
  .p pv3 [pv2,pv66571], .c 41, .c 3, .c 73, .c 5, .c 3, .c 127, .c 397, .c 3, .c 5, .c 79, .c 3,
  .c 47, .c 11, .c 3, .c 193, .c 7, .c 3, .p pv2 [pv2,pv266293], .c 5, .c 3, .c 197, .c 13, .c 3,
  .c 5, .c 971, .c 3, .c 31, .c 37, .c 3, .c 7, .c 23, .c 3, .c 17, .c 5, .c 3,
  .p pv3 [pv2,pv47,pv2833], .c 7, .c 3, .c 5, .p pv11 [pv2,pv3,pv19,pv73],
]
private theorem h0130c00 : checkBlock 1064963 128 b0130c00 = true := by
  decide +kernel

private def b0130c01 : List Row := [
  .c 3, .c 41, .c 239, .c 3, .c 467, .c 11, .c 3, .c 13, .c 5, .c 3, .c 7, .c 89, .c 3, .c 5,
  .c 53, .c 3, .c 11, .c 7, .c 3, .c 29, .c 13, .c 3, .p pv5 [pv2,pv11,pv41,pv1181], .c 5, .c 3,
  .p pv2 [pv2,pv23,pv11579], .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv127,pv233], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv43,pv4129], .c 3, .c 887, .c 73, .c 3, .c 167, .c 5, .c 3, .c 619, .c 271,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv16141], .c 3, .c 13, .p pv5 [pv2,pv3,pv137], .c 3, .c 11,
  .p pv13 [pv2,pv3,pv177553], .c 3, .c 7, .c 5, .c 3, .c 103, .p pv3 [pv2,pv3,pv5,pv7,pv19,pv89],
  .c 3, .c 5, .c 7, .c 3, .c 37, .p pv3 [pv2,pv3,pv277,pv641], .c 3, .p pv2 [pv2,pv31,pv17183],
  .c 19, .c 3, .c 53, .c 5, .c 3, .c 673, .c 11, .c 3, .c 5, .c 67, .c 3, .c 461, .c 17, .c 3,
  .c 31, .c 7, .c 3, .c 11, .c 5, .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv17,pv2089], .c 3, .c 5,
  .c 853, .c 3, .c 367, .c 127, .c 3, .c 7, .p pv13 [pv2,pv3,pv31,pv179], .c 3, .c 263, .c 5,
  .c 3, .c 89, .c 7, .c 3, .c 5, .c 11, .c 3, .c 29, .p pv5 [pv2,pv3,pv103,pv431], .c 3, .c 317,
  .c 31, .c 3, .c 47, .c 5, .c 3, .c 7, .c 643, .c 3, .c 5, .c 401, .c 3, .c 241, .c 7, .c 3,
  .c 13, .p pv2 [pv2,pv3,pv88789], .c 3, .c 79,
]
private theorem h0130c01 : checkBlock 1065219 128 b0130c01 = true := by
  decide +kernel

private def b0130c02 : List Row := [
  .c 5, .c 3, .p pv7 [pv2,pv532739], .c 59, .c 3, .c 5, .c 61, .c 3, .c 7, .c 11, .c 3, .c 43,
  .c 149, .c 3, .p pv5 [pv2,pv532751], .c 5, .c 3, .c 17, .p pv13 [pv2,pv3,pv5,pv11839], .c 3,
  .c 5, .c 419, .c 3, .c 23, .p pv3 [pv2,pv3,pv257,pv691], .c 3, .p pv5 [pv2,pv7,pv11,pv17,pv37],
  .p pv7 [pv2,pv3,pv4933], .c 3, .c 7, .c 5, .c 3, .c 19, .c 557, .c 3, .c 5, .c 7, .c 3, .c 421,
  .c 193, .c 3, .p pv2 [pv2,pv487,pv547], .c 11, .c 3, .c 31, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv67,pv71], .c 13, .c 3, .c 5, .c 17, .c 3, .c 11, .c 43, .c 3, .c 179, .c 7,
  .c 3, .p pv3 [pv2,pv11,pv12109], .c 5, .c 3, .c 59, .p pv23 [pv2,pv3,pv5,pv37], .c 3, .c 5,
  .c 151, .c 3, .c 17, .c 23, .c 3, .c 7, .c 277, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv17,pv15671], .c 7, .c 3, .c 5, .c 37, .c 3, .c 293, .p pv3 [pv2,pv3,pv97,pv1831],
  .c 3, .c 11, .c 13, .c 3, .c 19, .c 5, .c 3, .c 7, .c 373, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv25373], .c 3, .c 53, .c 7, .c 3, .p pv2 [pv2,pv263,pv1013], .c 17, .c 3,
  .p pv2 [pv2,pv23,pv23167], .c 5, .c 3, .p pv3 [pv2,pv13,pv10247], .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv17,pv653], .c 3, .c 7, .c 113, .c 3, .c 353, .p pv13 [pv2,pv3,pv7,pv4229],
  .c 3, .c 11, .c 5, .c 3, .c 577, .c 29, .c 3, .c 5, .c 13, .c 3,
]
private theorem h0130c02 : checkBlock 1065475 128 b0130c02 = true := by
  decide +kernel

private def b0130c03 : List Row := [
  .c 61, .p pv13 [pv2,pv3,pv88811], .c 3, .c 569, .c 97, .c 3, .c 7, .c 5, .c 3, .c 31, .c 23,
  .c 3, .c 5, .c 7, .c 3, .c 211, .p pv2 [pv2,pv3,pv59209], .c 3, .c 19, .c 67, .c 3,
  .p pv3 [pv2,pv47,pv5669], .c 5, .c 3, .c 11, .c 17, .c 3, .c 5, .p pv7 [pv2,pv3,pv19,pv9349],
  .c 3, .p pv17 [pv2,pv5,pv11,pv9689], .c 997, .c 3, .c 23, .c 7, .c 3, .c 83, .c 5, .c 3,
  .p pv3 [pv2,pv29,pv2297], .c 31, .c 3, .c 5, .p pv19 [pv2,pv3,pv113,pv131], .c 3,
  .p pv2 [pv2,pv5,pv7,pv23,pv331], .c 11, .c 3, .c 7, .p pv13 [pv2,pv3,pv88819], .c 3, .c 281,
  .c 5, .c 3, .p pv11 [pv2,pv532919], .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv349,pv509], .c 3,
  .p pv13 [pv2,pv5,pv21317], .c 61, .c 3, .c 13, .c 37, .c 3, .c 431, .c 5, .c 3, .c 7, .c 359,
  .c 3, .c 5, .c 41, .c 3, .c 19, .c 7, .c 3, .p pv5 [pv2,pv83,pv6421], .c 11, .c 3,
  .p pv2 [pv2,pv439,pv607], .c 5, .c 3, .p pv2 [pv2,pv532949],
  .p pv13 [pv2,pv3,pv5,pv11,pv17,pv19], .c 3, .c 5, .c 977, .c 3, .c 7, .c 47, .c 3, .c 17, .c 19,
  .c 3, .c 71, .c 5, .c 3, .c 113, .c 337, .c 3, .c 5, .p pv7 [pv2,pv3,pv53,pv419], .c 3,
  .p pv2 [pv2,pv5,pv223,pv239], .c 241, .c 3, .c 79, .p pv2 [pv2,pv3,pv13,pv6833], .c 3, .c 7,
  .c 5, .c 3, .c 41, .c 13, .c 3, .c 5, .c 7, .c 3, .c 191, .p pv2 [pv2,pv3,pv211,pv421], .c 3,
  .c 11, .p pv2 [pv2,pv3,pv59221], .c 3, .c 641, .c 5,
]
private theorem h0130c03 : checkBlock 1065731 128 b0130c03 = true := by
  decide +kernel

private def b0130c04 : List Row := [
  .c 3, .c 53, .c 139, .c 3, .c 5, .c 31, .c 3, .p pv3 [pv2,pv5,pv13,pv41], .c 827, .c 3, .c 37,
  .c 7, .c 3, .c 13, .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .c 23, .c 3,
  .p pv7 [pv2,pv5,pv7,pv97,pv157], .c 19, .c 3, .c 7, .c 13, .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv16657], .c 7, .c 3, .c 5, .c 571, .c 3, .c 283, .p pv3 [pv2,pv3,pv177677], .c 3,
  .p pv2 [pv2,pv533033], .c 29, .c 3, .c 23, .c 5, .c 3, .c 7, .c 37, .c 3, .c 5, .c 11, .c 3,
  .c 13, .c 7, .c 3, .c 61, .c 43, .c 3, .c 547, .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv35537],
  .c 3, .c 5, .c 13, .c 3, .c 7, .c 41, .c 3, .c 29, .c 109, .c 3, .p pv2 [pv2,pv193,pv1381],
  .c 5, .c 3, .p pv2 [pv2,pv17,pv31357], .p pv2 [pv2,pv3,pv5,pv5923], .c 3, .c 5, .c 19, .c 3,
  .c 331, .c 11, .c 3, .p pv2 [pv2,pv7,pv13,pv29,pv101], .p pv31 [pv2,pv3,pv61,pv971], .c 3, .c 7,
  .c 5, .c 3, .c 13, .c 67, .c 3, .c 5, .c 7, .c 3, .c 457, .c 31, .c 3, .c 157, .c 17, .c 3,
  .c 661, .c 5, .c 3, .c 173, .c 53, .c 3, .c 5, .c 71, .c 3, .c 23, .c 691, .c 3,
  .p pv3 [pv2,pv133277], .c 7, .c 3, .c 17, .c 5, .c 3, .c 37, .p pv11 [pv2,pv3,pv5,pv11,pv359],
  .c 3, .c 5, .p pv5 [pv2,pv3,pv88853], .c 3, .c 11,
]
private theorem h0130c04 : checkBlock 1065987 128 b0130c04 = true := by
  decide +kernel

private def b0130c05 : List Row := [
  .c 29, .c 3, .c 7, .c 389, .c 3, .p pv2 [pv2,pv11,pv2203], .c 5, .c 3, .c 401, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv37,pv1601], .c 3, .c 43, .c 13, .c 3, .c 719, .p pv3 [pv2,pv3,pv71,pv2503],
  .c 3, .p pv5 [pv2,pv7,pv76163], .c 5, .c 3, .c 7, .c 17, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv11,pv577], .c 3, .c 29, .c 7, .c 3, .c 11, .c 89, .c 3,
  .p pv3 [pv2,pv13,pv10253], .c 5, .c 3, .p pv7 [pv2,pv11,pv19,pv2551], .c 97, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv23,pv7727], .c 3, .c 7, .p pv2 [pv2,pv3,pv88861], .c 3, .c 19,
  .p pv3 [pv2,pv3,pv7,pv13,pv31], .c 3, .p pv5 [pv2,pv17,pv79,pv397], .c 5, .c 3, .c 23, .c 11,
  .c 3, .c 5, .c 43, .c 3, .c 197, .c 499, .c 3, .p pv5 [pv2,pv7,pv59,pv1291], .c 31, .c 3, .c 7,
  .c 5, .c 3, .p pv2 [pv2,pv533189], .c 113, .c 3, .c 5, .c 7, .c 3, .c 313, .c 17, .c 3, .c 523,
  .p pv3 [pv2,pv3,pv89,pv1997], .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv7,pv137,pv139],
  .p pv3 [pv2,pv3,pv5,pv17,pv41], .c 3, .c 5, .c 11, .c 3, .c 79, .p pv3 [pv2,pv3,pv7,pv25391],
  .c 3, .c 17, .c 7, .c 3, .p pv3 [pv2,pv19,pv877], .c 5, .c 3, .c 11, .c 23, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv29,pv227], .c 3, .c 19, .c 229, .c 3, .c 7, .c 101, .c 3, .c 61, .c 5, .c 3,
  .c 107, .c 7, .c 3, .c 5, .c 47, .c 3, .c 13, .c 11, .c 3, .c 23, .c 19, .c 3, .c 31, .c 5,
  .c 3,
]
private theorem h0130c05 : checkBlock 1066243 128 b0130c05 = true := by
  decide +kernel

private def b0130c06 : List Row := [
  .c 7, .c 157, .c 3, .c 5, .c 13, .c 3, .p pv23 [pv2,pv5,pv23,pv4637], .c 7, .c 3,
  .p pv2 [pv2,pv11,pv24239], .c 53, .c 3, .p pv2 [pv2,pv533261], .c 5, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv5,pv73,pv487], .c 3, .c 5, .c 619, .c 3, .c 7, .c 59, .c 3, .c 139, .c 11,
  .c 3, .p pv3 [pv2,pv133319], .c 5, .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv11,pv101], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv177761], .c 3, .c 11, .c 67, .c 3, .p pv3 [pv2,pv7,pv89,pv107], .c 23, .c 3,
  .c 7, .c 5, .c 3, .c 359, .c 29, .c 3, .c 5, .c 7, .c 3, .c 967, .c 19, .c 3, .c 113, .c 223,
  .c 3, .c 757, .c 5, .c 3, .p pv2 [pv2,pv7,pv47,pv1621], .p pv19 [pv2,pv3,pv5,pv29,pv613], .c 3,
  .c 5, .c 283, .c 3, .c 17, .c 71, .c 3, .c 11, .c 7, .c 3, .p pv2 [pv2,pv533321], .c 5, .c 3,
  .c 29, .p pv3 [pv2,pv3,pv5,pv13,pv547], .c 3, .c 5, .c 239, .c 3, .c 59, .c 13, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv103,pv863], .c 3, .c 37, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv139,pv1279], .c 3, .c 149, .p pv2 [pv2,pv3,pv11,pv8081], .c 3, .c 41, .c 17,
  .c 3, .c 11, .c 5, .c 3, .c 7, .c 193, .c 3, .c 5, .c 19, .c 3, .p pv7 [pv2,pv5,pv59,pv113],
  .c 7, .c 3, .c 277, .p pv7 [pv2,pv3,pv13,pv263], .c 3, .c 17, .c 5, .c 3, .c 397, .c 13, .c 3,
  .c 5, .c 11, .c 3, .c 7, .p pv5 [pv2,pv3,pv463],
]
private theorem h0130c06 : checkBlock 1066499 128 b0130c06 = true := by
  decide +kernel

private def b0130c07 : List Row := [
  .c 3, .p pv2 [pv2,pv266689], .c 47, .c 3, .c 23, .c 5, .c 3, .c 11, .c 103, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv44449], .c 3, .c 911, .c 109, .c 3, .c 43, .p pv17 [pv2,pv3,pv29633], .c 3,
  .c 7, .c 5, .c 3, .c 83, .c 17, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv106681], .c 11, .c 3,
  .p pv3 [pv2,pv79,pv211], .c 13, .c 3, .c 29, .c 5, .c 3, .c 61, .c 19, .c 3, .c 5, .c 53, .c 3,
  .c 67, .c 89, .c 3, .p pv5 [pv2,pv11,pv71,pv683], .c 7, .c 3, .c 47, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv37,pv1109], .c 41, .c 3, .c 5, .p pv23 [pv2,pv3,pv177811], .c 3, .c 13,
  .c 43, .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv83,pv6427], .c 5, .c 3, .p pv3 [pv2,pv19,pv7019],
  .c 7, .c 3, .c 5, .c 13, .c 3, .c 11, .c 17, .c 3, .c 19, .p pv2 [pv2,pv3,pv67,pv1327], .c 3,
  .p pv5 [pv2,pv7,pv11,pv433], .c 5, .c 3, .c 7, .c 659, .c 3, .c 5, .c 31, .c 3,
  .p pv2 [pv2,pv5,pv106693], .c 7, .c 3, .c 17, .c 29, .c 3, .c 41, .c 5, .c 3, .c 13, .c 61,
  .c 3, .c 5, .c 281, .c 3, .c 7, .c 167, .c 3, .c 11, .c 37, .c 3, .p pv2 [pv2,pv157,pv1699],
  .c 5, .c 3, .p pv2 [pv2,pv11,pv4409], .p pv17 [pv2,pv3,pv5,pv17783], .c 3, .c 5,
  .p pv11 [pv2,pv3,pv19759], .c 3, .c 263, .c 23, .c 3, .c 29, .p pv3 [pv2,pv3,pv163,pv1091],
  .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv521],
]
private theorem h0130c07 : checkBlock 1066755 128 b0130c07 = true := by
  decide +kernel

private def b0130c08 : List Row := [
  .c 11, .c 3, .c 5, .c 7, .c 3, .c 19, .p pv5 [pv2,pv3,pv11,pv17,pv317], .c 3, .c 13,
  .p pv7 [pv2,pv3,pv88919], .c 3, .c 11, .c 5, .c 3, .c 17, .c 47, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv177841], .c 3, .c 31, .c 13, .c 3, .p pv3 [pv2,pv17,pv3923], .c 7, .c 3,
  .p pv5 [pv2,pv23,pv23197], .c 5, .c 3, .p pv2 [pv2,pv266767], .c 809, .c 3, .c 5, .c 11, .c 3,
  .c 409, .p pv3 [pv2,pv3,pv31,pv5737], .c 3, .c 7, .c 1033, .c 3, .c 137, .c 5, .c 3, .c 11,
  .c 7, .c 3, .c 5, .c 17, .c 3, .c 107, .c 29, .c 3, .c 37, .c 353, .c 3, .c 269, .c 5, .c 3,
  .c 7, .c 13, .c 3, .c 5, .p pv53 [pv2,pv3,pv7,pv397], .c 3, .c 17, .c 7, .c 3,
  .p pv2 [pv2,pv533573], .c 197, .c 3, .c 373, .c 5, .c 3, .p pv7 [pv2,pv17,pv31387], .c 163,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv101,pv587], .c 3, .c 7, .c 19, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv7,pv25409], .c 3, .c 13, .c 5, .c 3, .c 41, .c 37, .c 3, .c 5, .c 547, .c 3,
  .c 71, .p pv2 [pv2,pv3,pv19763], .c 3, .p pv5 [pv2,pv7,pv31,pv2459], .c 11, .c 3, .c 7, .c 5,
  .c 3, .c 109, .p pv17 [pv2,pv3,pv5,pv7,pv11], .c 3, .c 5, .c 7, .c 3, .c 11, .c 613, .c 3,
  .c 31, .p pv3 [pv2,pv3,pv211,pv281], .c 3, .c 17, .c 5, .c 3, .c 19, .c 59, .c 3, .c 5, .c 131,
  .c 3, .c 13, .p pv3 [pv2,pv3,pv7,pv25411], .c 3,
]
private theorem h0130c08 : checkBlock 1067011 128 b0130c08 = true := by
  decide +kernel

private def b0130c09 : List Row := [
  .c 101, .c 7, .c 3, .c 449, .c 5, .c 3, .c 337, .c 277, .c 3, .c 5, .c 13, .c 3, .c 97,
  .p pv2 [pv2,pv3,pv23,pv1289], .c 3, .c 7, .c 31, .c 3, .c 43, .c 5, .c 3, .c 877, .c 7, .c 3,
  .c 5, .c 61, .c 3, .c 257, .c 47, .c 3, .p pv5 [pv2,pv13,pv41051], .p pv41 [pv2,pv3,pv17,pv109],
  .c 3, .c 73, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .p pv7 [pv2,pv3,pv7,pv43,pv197], .c 3,
  .p pv17 [pv2,pv5,pv21347], .c 7, .c 3, .c 181, .p pv3 [pv2,pv3,pv177893], .c 3, .c 11, .c 5,
  .c 3, .c 59, .p pv2 [pv2,pv3,pv5,pv47,pv757], .c 3, .c 5, .c 67, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv19,pv3121], .c 3, .p pv2 [pv2,pv533693], .c 43, .c 3, .c 541, .c 5, .c 3,
  .c 293, .c 19, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv173,pv617], .c 17, .c 3, .c 13,
  .c 151, .c 3, .c 7, .c 5, .c 3, .c 11, .c 823, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv11,pv1213], .c 13, .c 3, .c 17, .c 211, .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv19,pv4013], .c 29, .c 3, .c 5, .p pv2 [pv2,pv3,pv89,pv1999], .c 3,
  .p pv13 [pv2,pv5,pv106747], .c 11, .c 3, .c 19, .c 7, .c 3, .c 193, .c 5, .c 3,
  .p pv3 [pv2,pv33359], .p pv2 [pv2,pv3,pv5,pv29,pv409], .c 3, .c 5,
  .p pv11 [pv2,pv3,pv19,pv2341], .c 3, .c 223, .c 251, .c 3, .c 7, .p pv19 [pv2,pv3,pv13,pv2281],
  .c 3, .c 773, .c 5, .c 3, .c 29, .c 7,
]
private theorem h0130c09 : checkBlock 1067267 128 b0130c09 = true := by
  decide +kernel

private def b0130c10 : List Row := [
  .c 3, .c 5, .c 79, .c 3, .c 863, .c 397, .c 3, .p pv3 [pv2,pv66721], .c 11, .c 3, .c 197, .c 5,
  .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv11,pv647], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv71,pv179], .c 3,
  .c 11, .c 7, .c 3, .p pv5 [pv2,pv17,pv1847], .p pv7 [pv2,pv3,pv23,pv967], .c 3, .c 13, .c 5,
  .c 3, .c 53, .c 227, .c 3, .c 5, .c 431, .c 3, .c 7, .p pv5 [pv2,pv3,pv44483], .c 3,
  .p pv2 [pv2,pv266899], .c 13, .c 3, .c 367, .c 5, .c 3, .c 31, .p pv2 [pv2,pv3,pv5,pv19,pv1873],
  .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv53381], .c 701, .c 3, .c 11, .c 19, .c 3, .c 7, .c 5,
  .c 3, .p pv11 [pv2,pv11,pv13,pv3733], .c 137, .c 3, .c 5, .c 7, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv47,pv631], .c 3, .c 827, .c 139, .c 3, .c 311, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv17,pv2243], .c 11, .c 3, .c 5, .c 13, .c 3, .c 41, .c 23, .c 3,
  .p pv5 [pv2,pv19,pv28097], .c 7, .c 3, .c 11, .c 5, .c 3, .c 47, .p pv11 [pv2,pv3,pv5,pv3559],
  .c 3, .c 5, .p pv3 [pv2,pv3,pv23,pv2579], .c 3, .p pv7 [pv2,pv5,pv7,pv2179], .c 607, .c 3, .c 7,
  .c 17, .c 3, .c 59, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv197,pv271], .c 19, .c 3, .p pv2 [pv2,pv37,pv47,pv307],
  .p pv2 [pv2,pv3,pv11,pv8089], .c 3, .c 17, .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv1483], .c 3,
  .c 5, .p pv3 [pv2,pv3,pv7,pv25423], .c 3, .c 73, .c 7, .c 3, .p pv3 [pv2,pv43,pv97],
]
private theorem h0130c10 : checkBlock 1067523 128 b0130c10 = true := by
  decide +kernel

private def b0130c11 : List Row := [
  .c 67, .c 3, .c 37, .c 5, .c 3, .p pv2 [pv2,pv266947], .c 53, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv9887], .c 3, .c 7, .c 11, .c 3, .c 13, .c 29, .c 3, .c 163, .c 5, .c 3, .c 19,
  .c 17, .c 3, .c 5, .c 229, .c 3, .p pv7 [pv2,pv5,pv106783], .c 13, .c 3,
  .p pv2 [pv2,pv7,pv11,pv3467], .c 233, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv133481],
  .p pv3 [pv2,pv3,pv5,pv7,pv113], .c 3, .c 5, .c 7, .c 3, .c 977, .c 401, .c 3, .c 23, .c 11,
  .c 3, .c 97, .c 5, .c 3, .p pv7 [pv2,pv7,pv83,pv919], .c 191, .c 3, .c 5, .c 47, .c 3, .c 11,
  .p pv5 [pv2,pv3,pv7,pv12713], .c 3, .c 53, .c 7, .c 3, .p pv5 [pv2,pv11,pv48541], .c 5, .c 3,
  .p pv2 [pv2,pv266977], .c 13, .c 3, .c 5, .c 73, .c 3, .p pv3 [pv2,pv5,pv7,pv1907], .c 17, .c 3,
  .c 7, .c 173, .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv533969], .c 7, .c 3, .c 5, .c 223, .c 3,
  .p pv11 [pv2,pv5,pv13,pv31,pv53], .c 337, .c 3, .c 11, .c 23, .c 3, .c 13, .c 5, .c 3, .c 7,
  .c 19, .c 3, .c 5, .c 601, .c 3, .c 31, .c 7, .c 3, .p pv2 [pv2,pv533993], .c 13, .c 3, .c 593,
  .c 5, .c 3, .p pv7 [pv2,pv533999], .c 11, .c 3, .c 5, .c 103, .c 3, .c 7, .c 569, .c 3, .c 599,
  .p pv2 [pv2,pv3,pv7,pv59,pv431], .c 3, .c 11, .c 5, .c 3, .c 467, .c 419, .c 3,
]
private theorem h0130c11 : checkBlock 1067779 128 b0130c11 = true := by
  decide +kernel

private def b0130c12 : List Row := [
  .c 5, .p pv2 [pv2,pv3,pv89003], .c 3, .c 13, .c 31, .c 3, .c 19, .c 61, .c 3, .c 7, .c 5, .c 3,
  .c 17, .p pv19 [pv2,pv3,pv5,pv7,pv2543], .c 3, .c 5, .c 7, .c 3, .c 157, .c 443, .c 3, .c 43,
  .c 37, .c 3, .p pv2 [pv2,pv211,pv2531], .c 5, .c 3, .c 11, .c 41, .c 3, .c 5, .c 23, .c 3,
  .p pv2 [pv2,pv5,pv11,pv971], .p pv5 [pv2,pv3,pv7,pv173], .c 3, .p pv2 [pv2,pv13,pv41081], .c 7,
  .c 3, .p pv3 [pv2,pv241,pv277], .c 5, .c 3, .c 13, .c 821, .c 3, .c 5, .c 17, .c 3,
  .p pv2 [pv2,pv5,pv7,pv15259], .c 11, .c 3, .c 7, .c 163, .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv267037], .c 7, .c 3, .c 5, .c 29, .c 3, .c 17, .c 43, .c 3, .c 31, .c 47, .c 3,
  .c 41, .c 5, .c 3, .c 7, .c 67, .c 3, .c 5, .c 383, .c 3, .p pv11 [pv2,pv5,pv37,pv2887], .c 7,
  .c 3, .c 13, .c 11, .c 3, .p pv2 [pv2,pv534101], .c 5, .c 3, .c 73, .c 433, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv47,pv947], .c 3, .c 7, .c 13, .c 3, .c 37, .c 17, .c 3,
  .p pv3 [pv2,pv11,pv61,pv199], .c 5, .c 3, .c 659, .p pv7 [pv2,pv3,pv5,pv4451], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv17,pv3491], .c 3, .p pv13 [pv2,pv5,pv4273], .p pv5 [pv2,pv3,pv89021], .c 3,
  .p pv3 [pv2,pv7,pv19,pv251], .p pv11 [pv2,pv3,pv23,pv7741], .c 3, .c 7, .c 5, .c 3, .c 313,
  .p pv7 [pv2,pv3,pv5,pv7,pv5087], .c 3, .c 5, .c 7, .c 3, .c 23, .c 631, .c 3, .c 11, .c 349,
]
private theorem h0130c12 : checkBlock 1068035 128 b0130c12 = true := by
  decide +kernel

private def b0130c13 : List Row := [
  .c 3, .c 61, .c 5, .c 3, .c 167, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv263,pv677], .c 3,
  .p pv17 [pv2,pv5,pv47,pv2273], .c 19, .c 3, .c 79, .c 7, .c 3, .p pv2 [pv2,pv31,pv17231], .c 5,
  .c 3, .p pv3 [pv2,pv133541], .c 11, .c 3, .c 5, .c 41, .c 3, .c 571,
  .p pv11 [pv2,pv3,pv11,pv16187], .c 3, .c 7, .c 257, .c 3, .c 11, .c 5, .c 3, .c 499, .c 7, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv13,pv13697], .c 3, .p pv2 [pv2,pv5,pv19,pv5623], .c 23, .c 3,
  .p pv3 [pv2,pv83,pv1609], .c 13, .c 3, .p pv5 [pv2,pv7,pv17,pv67], .c 5, .c 3, .c 7, .c 509,
  .c 3, .c 5, .c 11, .c 3, .c 379, .c 7, .c 3, .p pv5 [pv2,pv534203],
  .p pv7 [pv2,pv3,pv11,pv19,pv71], .c 3, .c 347, .c 5, .c 3, .c 11, .c 43, .c 3, .c 5, .c 19,
  .c 3, .c 7, .c 17, .c 3, .p pv2 [pv2,pv131,pv2039], .p pv3 [pv2,pv3,pv7,pv25439], .c 3, .c 181,
  .c 5, .c 3, .c 37, .c 47, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv41,pv1303], .c 11, .c 3,
  .c 17, .p pv2 [pv2,pv3,pv269,pv331], .c 3, .c 7, .c 5, .c 3, .c 71,
  .p pv11 [pv2,pv3,pv5,pv7,pv53], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv59,pv1811], .c 139,
  .c 3, .p pv3 [pv2,pv11,pv13,pv467], .p pv37 [pv2,pv3,pv47,pv421], .c 3, .c 19, .c 5, .c 3,
  .c 13, .c 23, .c 3, .c 5, .p pv2 [pv2,pv3,pv67,pv443], .c 3, .c 983, .c 37, .c 3, .c 109, .c 7,
  .c 3, .c 53, .c 5, .c 3, .c 31, .c 19, .c 3, .c 5,
]
private theorem h0130c13 : checkBlock 1068291 128 b0130c13 = true := by
  decide +kernel

private def b0130c14 : List Row := [
  .c 641, .c 3, .c 11, .c 271, .c 3, .c 7, .p pv13 [pv2,pv3,pv178093], .c 3, .c 29, .c 5, .c 3,
  .c 17, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv11131], .c 3, .c 829, .c 41, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv29683], .c 3, .c 43, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5, .c 317, .c 3,
  .p pv2 [pv2,pv5,pv106861], .c 7, .c 3, .c 11, .p pv2 [pv2,pv3,pv178103], .c 3, .c 89, .c 5,
  .c 3, .p pv2 [pv2,pv11,pv149,pv163], .p pv3 [pv2,pv3,pv5,pv179,pv199], .c 3, .c 5, .c 17, .c 3,
  .c 7, .c 281, .c 3, .c 73, .c 23, .c 3, .c 881, .c 5, .c 3, .c 61, .c 11, .c 3, .c 5, .c 59,
  .c 3, .c 17, .c 751, .c 3, .p pv3 [pv2,pv7,pv38167], .c 29, .c 3, .c 7, .c 5, .c 3, .c 809,
  .c 13, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv10687], .p pv3 [pv2,pv3,pv178117], .c 3,
  .p pv2 [pv2,pv41,pv13033], .p pv7 [pv2,pv3,pv29,pv37,pv83], .c 3, .p pv3 [pv2,pv19,pv79,pv89],
  .c 5, .c 3, .p pv7 [pv2,pv7,pv23,pv3319], .p pv31 [pv2,pv3,pv5,pv61,pv73], .c 3, .c 5, .c 11,
  .c 3, .c 19, .c 47, .c 3, .c 29, .c 7, .c 3, .c 13, .c 5, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv5,pv19], .c 3, .c 5, .p pv11 [pv2,pv3,pv13,pv17,pv31], .c 3,
  .p pv13 [pv2,pv5,pv7,pv11,pv347], .c 71, .c 3, .c 7, .c 13, .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv151,pv3539], .c 7, .c 3, .c 5, .c 23, .c 3, .c 79, .c 11, .c 3, .c 919, .c 331,
  .c 3,
]
private theorem h0130c14 : checkBlock 1068547 128 b0130c14 = true := by
  decide +kernel

private def b0130c15 : List Row := [
  .p pv2 [pv2,pv7,pv76343], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv23,pv1549], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv3181], .c 3, .c 13, .c 7, .c 3, .c 47, .c 41, .c 3, .c 23, .c 5, .c 3,
  .c 223, .c 17, .c 3, .c 5, .c 13, .c 3, .c 7, .c 29, .c 3, .p pv5 [pv2,pv23,pv37,pv157], .c 11,
  .c 3, .c 257, .c 5, .c 3, .c 419, .p pv37 [pv2,pv3,pv5,pv11,pv41,pv79], .c 3, .c 5,
  .p pv7 [pv2,pv3,pv3299], .c 3, .c 11, .c 19, .c 3, .p pv7 [pv2,pv7,pv13,pv839],
  .p pv7 [pv2,pv3,pv44537], .c 3, .c 7, .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv7,pv509], .c 3,
  .c 5, .c 7, .c 3, .c 29, .p pv7 [pv2,pv3,pv13,pv571], .c 3, .p pv2 [pv2,pv267229], .c 421, .c 3,
  .c 457, .c 5, .c 3, .c 151, .c 1019, .c 3, .c 5, .c 43, .c 3, .p pv7 [pv2,pv5,pv19,pv29,pv97],
  .c 17, .c 3, .c 11, .c 7, .c 3, .c 383, .c 5, .c 3, .c 19, .c 653, .c 3, .c 5, .c 37, .c 3,
  .c 23, .c 31, .c 3, .c 7, .c 89, .c 3, .c 677, .c 5, .c 3, .p pv2 [pv2,pv179,pv1493], .c 7,
  .c 3, .c 5, .c 19, .c 3, .p pv3 [pv2,pv5,pv1069], .c 13, .c 3, .p pv5 [pv2,pv269,pv1987],
  .c 251, .c 3, .c 11, .c 5, .c 3, .c 7, .c 59, .c 3, .c 5, .c 29, .c 3,
  .p pv13 [pv2,pv5,pv106903], .c 7, .c 3, .c 97, .p pv11 [pv2,pv3,pv6599], .c 3,
  .p pv2 [pv2,pv13,pv41117], .c 5, .c 3, .c 139, .p pv2 [pv2,pv3,pv5,pv7127], .c 3, .c 5, .c 11,
]
private theorem h0130c15 : checkBlock 1068803 128 b0130c15 = true := by
  decide +kernel

private def b0130c16 : List Row := [
  .c 3, .c 7, .c 23, .c 3, .c 463, .c 449, .c 3, .c 19, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv23,pv61,pv127], .c 3, .c 131, .c 113, .c 3, .c 31, .p pv3 [pv2,pv3,pv178183],
  .c 3, .c 7, .c 5, .c 3, .c 23, .c 19, .c 3, .c 5, .c 7, .c 3, .c 397, .c 11, .c 3,
  .p pv5 [pv2,pv409,pv1307], .p pv7 [pv2,pv3,pv31,pv479], .c 3, .c 13, .c 5, .c 3, .c 59,
  .p pv2 [pv2,pv3,pv5,pv103,pv173], .c 3, .c 5, .c 17, .c 3, .c 569, .c 719, .c 3, .c 41, .c 7,
  .c 3, .c 947, .c 5, .c 3, .c 53, .p pv2 [pv2,pv3,pv5,pv157,pv227], .c 3, .c 5, .c 743, .c 3,
  .c 17, .p pv3 [pv2,pv3,pv59399], .c 3, .c 7, .c 11, .c 3, .p pv3 [pv2,pv133649], .c 5, .c 3,
  .p pv29 [pv2,pv13,pv17,pv41,pv59], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv19,pv83,pv113], .c 3,
  .c 11, .c 127, .c 3, .p pv3 [pv2,pv33413], .p pv3 [pv2,pv3,pv191,pv311], .c 3,
  .p pv5 [pv2,pv7,pv11,pv53,pv131], .c 5, .c 3, .c 7, .c 73, .c 3, .c 5, .c 13, .c 3, .c 317,
  .c 7, .c 3, .c 23, .c 17, .c 3, .c 67, .c 5, .c 3, .c 29, .c 617, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv11,pv17,pv953], .c 3, .c 7, .p pv5 [pv2,pv3,pv14851], .c 3, .c 11, .c 929,
  .c 3, .c 17, .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv109], .c 3, .c 5, .c 47, .c 3, .c 19,
  .p pv3 [pv2,pv3,pv13,pv13709], .c 3, .p pv2 [pv2,pv7,pv76379], .c 643, .c 3, .c 7,
]
private theorem h0130c16 : checkBlock 1069059 128 b0130c16 = true := by
  decide +kernel

private def b0130c17 : List Row := [
  .c 5, .c 3, .c 113, .c 11, .c 3, .c 5, .c 7, .c 3, .c 71, .c 739, .c 3, .c 37, .c 19, .c 3,
  .c 11, .c 5, .c 3, .p pv2 [pv2,pv7,pv181,pv211], .c 17, .c 3, .c 5, .c 499, .c 3, .c 389,
  .p pv2 [pv2,pv3,pv7,pv23,pv41], .c 3, .c 13, .c 7, .c 3, .c 149, .c 5, .c 3,
  .p pv2 [pv2,pv503,pv1063], .c 53, .c 3, .c 5, .c 11, .c 3, .c 47, .c 13, .c 3, .c 7, .c 109,
  .c 3, .c 41, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 727, .c 3, .p pv3 [pv2,pv5,pv11,pv4861],
  .c 79, .c 3, .p pv2 [pv2,pv199,pv2687], .p pv2 [pv2,pv3,pv89119], .c 3, .c 29, .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv557], .c 3, .c 5, .c 733, .c 3, .p pv2 [pv2,pv5,pv73,pv293], .c 7, .c 3,
  .c 283, .p pv2 [pv2,pv3,pv13,pv13711], .c 3, .p pv5 [pv2,pv29,pv18439], .c 5, .c 3, .c 31,
  .c 13, .c 3, .c 5, .c 23, .c 3, .c 7, .c 571, .c 3, .c 17, .c 101, .c 3, .c 59, .c 5, .c 3,
  .p pv2 [pv2,pv661,pv809], .p pv17 [pv2,pv3,pv5,pv23,pv31], .c 3, .c 5, .p pv3 [pv2,pv3,pv59417],
  .c 3, .c 251, .c 61, .c 3, .p pv2 [pv2,pv7,pv38197], .c 11, .c 3, .c 7, .c 5, .c 3, .c 19,
  .c 31, .c 3, .c 5, .c 7, .c 3, .c 11, .p pv3 [pv2,pv3,pv59419], .c 3, .p pv2 [pv2,pv23,pv23251],
  .c 13, .c 3, .p pv3 [pv2,pv11,pv59,pv103], .c 5, .c 3, .c 37, .p pv7 [pv2,pv3,pv5,pv2971], .c 3,
  .c 5, .c 19, .c 3,
]
private theorem h0130c17 : checkBlock 1069315 128 b0130c17 = true := by
  decide +kernel

private def b0130c18 : List Row := [
  .p pv2 [pv2,pv5,pv106957], .p pv5 [pv2,pv3,pv7,pv17,pv107], .c 3, .p pv3 [pv2,pv133697], .c 7,
  .c 3, .p pv5 [pv2,pv43,pv12437], .c 5, .c 3, .c 17, .p pv19 [pv2,pv3,pv5,pv101,pv353], .c 3,
  .c 5, .p pv2 [pv2,pv3,pv11,pv37,pv73], .c 3, .c 13, .p pv3 [pv2,pv3,pv89,pv2003], .c 3, .c 7,
  .p pv17 [pv2,pv3,pv41,pv1087], .c 3, .c 521, .c 5, .c 3, .c 97, .c 7, .c 3, .c 5, .c 13, .c 3,
  .p pv19 [pv2,pv5,pv106963], .c 37, .c 3, .c 271, .p pv7 [pv2,pv3,pv23,pv337], .c 3, .c 19, .c 5,
  .c 3, .c 7, .c 11, .c 3, .c 5, .c 17, .c 3, .c 23, .c 7, .c 3, .p pv2 [pv2,pv13,pv41141], .c 73,
  .c 3, .c 11, .c 5, .c 3, .c 13, .c 19, .c 3, .c 5, .p pv11 [pv2,pv3,pv31,pv71], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv13,pv6857], .c 3, .p pv3 [pv2,pv61,pv137], .c 53, .c 3, .c 233, .c 5, .c 3,
  .c 811, .c 43, .c 3, .c 5, .c 11, .c 3, .c 127, .c 29, .c 3, .p pv5 [pv2,pv7,pv109,pv701],
  .c 59, .c 3, .c 7, .c 5, .c 3, .c 11, .p pv23 [pv2,pv3,pv5,pv7,pv283], .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv11,pv389], .c 23, .c 3, .c 13, .c 17, .c 3, .c 821, .c 5, .c 3, .c 163,
  .c 113, .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv19,pv23], .c 3, .c 29, .c 11, .c 3, .c 83, .c 7,
  .c 3, .c 17, .c 5, .c 3, .c 23, .c 347, .c 3, .c 5, .p pv3 [pv2,pv3,pv178301], .c 3,
  .p pv7 [pv2,pv5,pv7,pv17,pv29,pv31], .c 41, .c 3, .c 7, .p pv2 [pv2,pv3,pv37,pv61,pv79], .c 3,
  .p pv5 [pv2,pv13,pv23,pv1789], .c 5,
]
private theorem h0130c18 : checkBlock 1069571 128 b0130c18 = true := by
  decide +kernel

private def b0130c19 : List Row := [
  .c 3, .c 641, .c 7, .c 3, .c 5, .c 457, .c 3, .c 31, .c 439, .c 3, .c 59, .c 11, .c 3,
  .p pv2 [pv2,pv7,pv19,pv2011], .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv1213],
  .c 3, .c 11, .c 7, .c 3, .c 131, .c 61, .c 3, .c 43, .c 5, .c 3, .c 491, .c 23, .c 3, .c 5,
  .c 29, .c 3, .c 7, .c 31, .c 3, .c 197, .c 19, .c 3, .c 13, .c 5, .c 3,
  .p pv7 [pv2,pv509,pv1051], .p pv7 [pv2,pv3,pv5,pv743], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv13,pv29,pv43], .c 3, .p pv2 [pv2,pv5,pv106993],
  .p pv2 [pv2,pv3,pv163,pv547], .c 3, .c 11, .c 13, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv24317], .p pv3 [pv2,pv3,pv5,pv7,pv1019], .c 3, .c 5, .c 7, .c 3, .c 73,
  .c 17, .c 3, .c 449, .c 43, .c 3, .p pv2 [pv2,pv267493], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv13,pv5879], .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv151,pv1181], .c 3, .c 13,
  .c 463, .c 3, .c 17, .c 7, .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv131,pv1021],
  .p pv3 [pv2,pv3,pv5,pv1321], .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv7,pv7643], .c 19, .c 3,
  .c 7, .c 23, .c 3, .p pv3 [pv2,pv66877], .c 5, .c 3, .p pv11 [pv2,pv535019], .c 7, .c 3, .c 5,
  .c 11, .c 3, .c 277, .c 109, .c 3, .c 67, .c 41, .c 3, .p pv5 [pv2,pv7,pv61,pv179], .c 5, .c 3,
  .c 7, .c 29, .c 3, .c 5, .c 37, .c 3, .p pv3 [pv2,pv5,pv11,pv19],
]
private theorem h0130c19 : checkBlock 1069827 128 b0130c19 = true := by
  decide +kernel

private def b0130c20 : List Row := [
  .c 7, .c 3, .p pv5 [pv2,pv479,pv1117], .c 31, .c 3, .p pv2 [pv2,pv267523], .c 5, .c 3, .c 17,
  .c 587, .c 3, .c 5, .c 73, .c 3, .c 7, .c 11, .c 3, .c 229, .c 83, .c 3, .c 53, .c 5, .c 3,
  .c 29, .p pv3 [pv2,pv3,pv5,pv35671], .c 3, .c 5, .c 19, .c 3, .c 41, .c 47, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv257,pv347], .c 3, .c 7, .c 5, .c 3, .c 661, .c 139, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv103,pv1039], .c 13, .c 3, .c 223, .c 11, .c 3, .c 71, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv37,pv1033], .c 67, .c 3, .c 5, .p pv2 [pv2,pv3,pv101,pv883], .c 3, .c 11,
  .p pv2 [pv2,pv3,pv7,pv83,pv307], .c 3, .p pv5 [pv2,pv535103], .c 7, .c 3, .c 19, .c 5, .c 3,
  .c 953, .p pv7 [pv2,pv3,pv5,pv17837], .c 3, .c 5, .c 43, .c 3, .p pv7 [pv2,pv5,pv7,pv15289],
  .p pv5 [pv2,pv3,pv19,pv2347], .c 3, .c 7, .c 829, .c 3, .p pv2 [pv2,pv239,pv2239], .c 5, .c 3,
  .p pv3 [pv2,pv133781], .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv11,pv2027], .c 3, .c 683, .c 563,
  .c 3, .c 11, .c 17, .c 3, .c 103, .c 5, .c 3, .c 7, .c 241, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv17,pv1499], .c 3, .p pv2 [pv2,pv5,pv13,pv8233], .c 7, .c 3, .c 101, .c 37,
  .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv19,pv14083], .c 11, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv13,pv2287], .c 3, .c 7, .p pv2 [pv2,pv3,pv11,pv16217], .c 3, .c 19, .c 13,
  .c 3, .c 11, .c 5, .c 3,
]
private theorem h0130c20 : checkBlock 1070083 128 b0130c20 = true := by
  decide +kernel

private def b0130c21 : List Row := [
  .p pv2 [pv2,pv535169], .p pv19 [pv2,pv3,pv5,pv17839], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv19,pv41,pv229], .c 3, .c 23, .c 409, .c 3, .p pv2 [pv2,pv7,pv43,pv127],
  .c 691, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv13,pv31,pv83], .c 17, .c 3, .c 5, .c 7, .c 3,
  .c 13, .c 349, .c 3, .c 41, .p pv13 [pv2,pv3,pv11,pv17,pv53], .c 3, .c 857, .c 5, .c 3, .c 11,
  .c 131, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv11,pv37,pv263], .c 599, .c 3,
  .p pv3 [pv2,pv149,pv449], .c 7, .c 3, .p pv5 [pv2,pv17,pv19,pv1657], .c 5, .c 3,
  .p pv2 [pv2,pv41,pv61,pv107], .p pv3 [pv2,pv3,pv5,pv31,pv1151], .c 3, .c 5, .c 59, .c 3, .c 19,
  .c 11, .c 3, .c 7, .c 113, .c 3, .p pv2 [pv2,pv267613], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .c 71, .c 3, .p pv19 [pv2,pv5,pv167,pv641], .c 17, .c 3, .c 29, .c 19, .c 3, .c 127, .c 5, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv5,pv17,pv2099], .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv59], .c 3,
  .p pv2 [pv2,pv5,pv2141], .c 7, .c 3, .c 17, .c 11, .c 3, .p pv3 [pv2,pv23,pv2909], .c 5, .c 3,
  .c 47, .c 37, .c 3, .c 5, .p pv3 [pv2,pv3,pv67,pv2663], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv131,pv227], .c 3, .c 13, .c 367, .c 3, .p pv5 [pv2,pv11,pv48661], .c 5, .c 3,
  .c 1009, .c 41, .c 3, .c 5, .p pv2 [pv2,pv3,pv89213], .c 3, .p pv3 [pv2,pv5,pv6691], .c 13,
  .c 3, .p pv5 [pv2,pv7,pv47,pv1627], .p pv7 [pv2,pv3,pv14869], .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv139,pv3851], .c 23, .c 3, .c 5, .c 7, .c 3, .c 719, .c 19,
]
private theorem h0130c21 : checkBlock 1070339 128 b0130c21 = true := by
  decide +kernel

private def b0130c22 : List Row := [
  .c 3, .c 11, .c 179, .c 3, .c 421, .c 5, .c 3, .c 17, .c 61, .c 3, .c 5, .c 83, .c 3,
  .p pv2 [pv2,pv5,pv199,pv269], .c 223, .c 3, .c 23, .c 7, .c 3, .c 41, .c 5, .c 3, .c 541, .c 11,
  .c 3, .c 5, .c 31, .c 3, .c 29, .c 53, .c 3, .c 7, .p pv2 [pv2,pv3,pv2203], .c 3, .c 11, .c 5,
  .c 3, .c 19, .c 7, .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv13,pv29,pv71],
  .p pv2 [pv2,pv3,pv178447], .c 3, .c 79, .p pv31 [pv2,pv3,pv19,pv587], .c 3, .c 13, .c 5, .c 3,
  .c 7, .c 101, .c 3, .c 5, .c 11, .c 3, .c 17, .c 7, .c 3, .c 139, .c 13, .c 3, .c 823, .c 5,
  .c 3, .c 11, .c 443, .c 3, .c 5, .c 127, .c 3, .c 7, .c 37, .c 3, .c 163, .c 107, .c 3,
  .p pv3 [pv2,pv33461], .c 5, .c 3, .c 53, .p pv7 [pv2,pv3,pv5,pv8923], .c 3, .c 5, .c 29, .c 3,
  .c 13, .c 11, .c 3, .p pv3 [pv2,pv7,pv19121], .c 17, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv23,pv103,pv113], .c 59, .c 3, .c 5, .c 7, .c 3, .c 47,
  .p pv2 [pv2,pv3,pv19,pv31,pv101], .c 3, .c 631, .c 433, .c 3, .c 17, .c 5, .c 3, .c 199, .c 19,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv317,pv563], .c 3, .c 467, .c 31, .c 3, .c 73, .c 7, .c 3,
  .p pv2 [pv2,pv347,pv1543], .c 5, .c 3, .c 13,
]
private theorem h0130c22 : checkBlock 1070595 128 b0130c22 = true := by
  decide +kernel

private def b0130c23 : List Row := [
  .p pv2 [pv2,pv3,pv5,pv11,pv59], .c 3, .c 5, .c 23, .c 3, .c 11, .c 149, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv233,pv383], .c 3, .p pv3 [pv2,pv11,pv43,pv283], .c 5, .c 3, .c 41, .c 7, .c 3,
  .c 5, .c 503, .c 3, .c 37, .c 71, .c 3, .c 19, .p pv3 [pv2,pv3,pv17,pv10499], .c 3, .c 23, .c 5,
  .c 3, .c 7, .c 613, .c 3, .c 5, .c 389, .c 3, .p pv3 [pv2,pv5,pv41,pv653], .c 7, .c 3, .c 11,
  .c 137, .c 3, .p pv2 [pv2,pv17,pv15749], .c 5, .c 3, .p pv11 [pv2,pv11,pv48679], .c 29, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv59497], .c 3, .c 7, .c 13, .c 3, .c 31, .c 239, .c 3, .c 107, .c 5,
  .c 3, .c 1019, .c 11, .c 3, .c 5, .c 61, .c 3, .p pv2 [pv2,pv5,pv53549], .c 17, .c 3,
  .p pv2 [pv2,pv7,pv227,pv337], .c 47, .c 3, .c 7, .c 5, .c 3, .c 29, .c 43, .c 3, .c 5, .c 7,
  .c 3, .c 19, .c 971, .c 3, .c 17, .c 31, .c 3, .p pv5 [pv2,pv535511], .c 5, .c 3, .c 1021,
  .c 13, .c 3, .c 5, .c 11, .c 3, .c 23, .c 41, .c 3, .p pv5 [pv2,pv535523], .c 7, .c 3,
  .p pv2 [pv2,pv267763], .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv17851], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv137,pv1303], .c 3, .c 401, .c 163, .c 3, .c 7, .c 883, .c 3, .c 13, .c 5,
  .c 3, .c 197, .c 7, .c 3, .c 5, .c 103, .c 3, .c 233, .c 11, .c 3,
]
private theorem h0130c23 : checkBlock 1070851 128 b0130c23 = true := by
  decide +kernel

private def b0130c24 : List Row := [
  .c 787, .c 13, .c 3, .c 37, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv4463], .c 3, .c 5, .c 113,
  .c 3, .p pv17 [pv2,pv5,pv43,pv47,pv53], .c 7, .c 3, .c 929, .p pv2 [pv2,pv3,pv167,pv1069], .c 3,
  .c 31, .c 5, .c 3, .p pv2 [pv2,pv13,pv20599], .p pv3 [pv2,pv3,pv5,pv37,pv193], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv23,pv3881], .c 3, .c 7, .c 19, .c 3, .c 907, .c 11, .c 3, .c 29, .c 5, .c 3,
  .c 23, .p pv7 [pv2,pv3,pv5,pv11,pv541], .c 3, .c 5, .c 13, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv44633], .c 3, .p pv2 [pv2,pv7,pv67,pv571], .c 263, .c 3, .c 7, .c 5, .c 3,
  .c 1031, .c 157, .c 3, .c 5, .c 7, .c 3, .c 17, .p pv3 [pv2,pv3,pv178537], .c 3,
  .p pv2 [pv2,pv13,pv41201], .p pv29 [pv2,pv3,pv89269], .c 3, .p pv3 [pv2,pv8369], .c 5, .c 3,
  .c 13, .p pv7 [pv2,pv3,pv5,pv79,pv113], .c 3, .c 5, .c 211, .c 3, .c 383,
  .p pv5 [pv2,pv3,pv7,pv13,pv109], .c 3, .c 11, .c 7, .c 3, .c 59, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv97,pv251], .c 23, .c 3, .c 5, .c 19, .c 3, .c 83,
  .p pv3 [pv2,pv3,pv61,pv2927], .c 3, .c 7, .c 17, .c 3, .c 89, .c 5, .c 3, .c 709, .c 7, .c 3,
  .c 5, .c 101, .c 3, .p pv13 [pv2,pv5,pv149,pv719], .p pv7 [pv2,pv3,pv11,pv2029], .c 3, .c 13,
  .c 71, .c 3, .c 11, .c 5, .c 3, .c 7, .c 811, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv911], .c 3,
  .p pv2 [pv2,pv5,pv17,pv23,pv137], .c 7, .c 3, .c 29, .p pv2 [pv2,pv3,pv73,pv1223], .c 3, .c 19,
  .c 5, .c 3, .p pv7 [pv2,pv535679], .c 109,
]
private theorem h0130c24 : checkBlock 1071107 128 b0130c24 = true := by
  decide +kernel

private def b0130c25 : List Row := [
  .c 3, .c 5, .c 11, .c 3, .c 7, .p pv5 [pv2,pv3,pv19,pv37,pv127], .c 3, .p pv3 [pv2,pv29,pv2309],
  .p pv2 [pv2,pv3,pv7,pv11,pv773], .c 3, .c 419, .c 5, .c 3, .c 11, .c 17, .c 3, .c 5, .c 67,
  .c 3, .p pv3 [pv2,pv5,pv11,pv487], .c 839, .c 3, .p pv5 [pv2,pv7,pv103,pv743], .c 23, .c 3,
  .c 7, .c 5, .c 3, .p pv2 [pv2,pv535709], .c 13, .c 3, .c 5, .c 7, .c 3, .c 43, .c 11, .c 3,
  .c 239, .p pv3 [pv2,pv3,pv283,pv631], .c 3, .p pv2 [pv2,pv17,pv31513], .c 5, .c 3, .c 131,
  .p pv3 [pv2,pv3,pv5,pv2381], .c 3, .c 5, .p pv11 [pv2,pv3,pv11161], .c 3, .c 71, .c 29, .c 3,
  .c 19, .c 7, .c 3, .c 13, .c 5, .c 3, .p pv13 [pv2,pv23,pv23293], .c 661, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv19,pv241], .c 3, .c 229, .c 17, .c 3, .c 7, .c 11, .c 3, .c 397, .c 5,
  .c 3, .c 101, .c 7, .c 3, .c 5, .c 43, .c 3, .c 11, .c 479, .c 3, .c 17,
  .p pv23 [pv2,pv3,pv44647], .c 3, .p pv2 [pv2,pv7,pv11,pv71], .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv5953], .c 3, .c 5, .c 23, .c 3, .c 13, .c 7, .c 3, .c 37, .c 97, .c 3,
  .p pv2 [pv2,pv19,pv163,pv173], .c 5, .c 3, .p pv3 [pv2,pv66973],
  .p pv7 [pv2,pv3,pv5,pv23,pv1553], .c 3, .c 5, .c 13, .c 3, .c 7, .c 601, .c 3, .c 11,
  .p pv17 [pv2,pv3,pv7,pv12757], .c 3, .c 23, .c 5, .c 3, .c 439, .p pv7 [pv2,pv3,pv5,pv19,pv47],
  .c 3, .c 5, .c 53, .c 3, .c 599, .c 83, .c 3, .c 41,
]
private theorem h0130c25 : checkBlock 1071363 128 b0130c25 = true := by
  decide +kernel

private def b0130c26 : List Row := [
  .c 19, .c 3, .c 7, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv73,pv367], .p pv2 [pv2,pv3,pv11,pv13,pv1249], .c 3, .c 47, .c 89, .c 3, .c 11,
  .c 5, .c 3, .p pv2 [pv2,pv7,pv41,pv1867], .p pv7 [pv2,pv3,pv5,pv53,pv337], .c 3, .c 5, .c 227,
  .c 3, .p pv23 [pv2,pv5,pv31,pv3457], .c 179, .c 3, .c 751, .c 7, .c 3,
  .p pv2 [pv2,pv157,pv3413], .c 5, .c 3, .c 43, .c 677, .c 3, .c 5, .c 11, .c 3, .c 31,
  .p pv5 [pv2,pv3,pv59539], .c 3, .c 7, .c 61, .c 3, .c 53, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5,
  .c 241, .c 3, .c 17, .c 13, .c 3, .c 307, .p pv2 [pv2,pv3,pv89,pv223], .c 3,
  .p pv5 [pv2,pv7,pv37,pv2069], .c 5, .c 3, .c 7, .c 137, .c 3, .c 5, .c 149, .c 3,
  .p pv23 [pv2,pv5,pv13397], .c 7, .c 3, .c 571, .c 977, .c 3, .p pv2 [pv2,pv13,pv20611], .c 5,
  .c 3, .c 37, .c 41, .c 3, .c 5, .p pv5 [pv2,pv3,pv73,pv2447], .c 3, .c 7, .c 79, .c 3, .c 109,
  .c 17, .c 3, .p pv2 [pv2,pv419,pv1279], .c 5, .c 3, .c 19, .c 13, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv17,pv37,pv71], .c 3, .p pv2 [pv2,pv5,pv53591], .c 23, .c 3, .c 89, .c 11,
  .c 3, .c 7, .c 5, .c 3, .c 157, .p pv41 [pv2,pv3,pv5,pv7,pv11,pv29], .c 3, .c 5, .c 7, .c 3,
  .c 11, .c 37, .c 3, .p pv3 [pv2,pv31,pv2161], .c 73, .c 3, .c 13, .c 5, .c 3, .c 23,
  .p pv11 [pv2,pv3,pv5,pv35729], .c 3,
]
private theorem h0130c26 : checkBlock 1071619 128 b0130c26 = true := by
  decide +kernel

private def b0130c27 : List Row := [
  .c 5, .c 197, .c 3, .c 643, .c 347, .c 3, .c 31, .c 7, .c 3, .c 503, .c 5, .c 3,
  .p pv2 [pv2,pv29,pv18481], .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv109,pv149], .c 3,
  .p pv7 [pv2,pv5,pv7,pv15313], .c 101, .c 3, .c 7, .p pv3 [pv2,pv3,pv17,pv31,pv113], .c 3, .c 19,
  .c 5, .c 3, .c 47, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv1861], .c 3, .c 13,
  .p pv5 [pv2,pv3,pv19,pv9403], .c 3, .c 43, .c 31, .c 3, .c 61, .c 5, .c 3, .c 7, .c 11, .c 3,
  .c 5, .c 13, .c 3, .c 59, .c 7, .c 3, .p pv3 [pv2,pv47,pv2851], .p pv2 [pv2,pv3,pv53,pv3371],
  .c 3, .c 11, .c 5, .c 3, .c 409, .p pv3 [pv2,pv3,pv5,pv43,pv277], .c 3, .c 5, .c 337, .c 3,
  .c 7, .c 17, .c 3, .c 23, .p pv19 [pv2,pv3,pv7,pv709], .c 3, .c 199, .c 5, .c 3, .c 13, .c 251,
  .c 3, .c 5, .c 11, .c 3, .c 53, .c 43, .c 3, .c 17, .p pv3 [pv2,pv3,pv11,pv37,pv439], .c 3,
  .c 7, .c 5, .c 3, .c 11, .c 163, .c 3, .c 5, .c 7, .c 3, .c 353, .c 181, .c 3, .c 67, .c 631,
  .c 3, .c 31, .c 5, .c 3, .c 647, .c 173, .c 3, .c 5, .c 293, .c 3, .c 211, .c 11, .c 3, .c 13,
  .c 7, .c 3, .p pv5 [pv2,pv536051], .c 5, .c 3, .c 41, .c 83, .c 3, .c 5, .c 47, .c 3, .c 227,
  .c 13, .c 3, .c 7, .p pv13 [pv2,pv3,pv349],
]
private theorem h0130c27 : checkBlock 1071875 128 b0130c27 = true := by
  decide +kernel

private def b0130c28 : List Row := [
  .c 3, .p pv2 [pv2,pv19,pv14107], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv178691],
  .c 3, .c 19, .c 157, .c 3, .p pv2 [pv2,pv17,pv15767], .c 11, .c 3,
  .p pv2 [pv2,pv7,pv13,pv43,pv137], .c 5, .c 3, .c 7, .c 71, .c 3, .c 5, .c 881, .c 3, .c 11,
  .c 7, .c 3, .p pv2 [pv2,pv37,pv14489], .c 19, .c 3, .c 659, .c 5, .c 3, .p pv7 [pv2,pv536099],
  .c 13, .c 3, .c 5, .c 17, .c 3, .c 7, .p pv2 [pv2,pv3,pv199,pv449], .c 3, .c 29,
  .p pv2 [pv2,pv3,pv7,pv521], .c 3, .c 37, .c 5, .c 3, .p pv2 [pv2,pv31,pv8647],
  .p pv3 [pv2,pv3,pv5,pv103,pv347], .c 3, .c 5, .c 23, .c 3, .c 17, .c 53, .c 3, .c 11, .c 761,
  .c 3, .c 7, .c 5, .c 3, .c 31, .c 127, .c 3, .c 5, .c 7, .c 3, .c 197, .c 41, .c 3, .c 83,
  .c 13, .c 3, .c 23, .c 5, .c 3, .c 739, .c 11, .c 3, .c 5, .c 37, .c 3,
  .p pv2 [pv2,pv5,pv10723], .c 19, .c 3, .c 167, .c 7, .c 3, .c 11, .c 5, .c 3, .c 61, .c 31,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv17,pv10513], .c 3, .c 13, .c 29, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv313,pv571], .c 3, .c 17, .c 5, .c 3, .c 53, .c 7, .c 3, .c 5, .c 11, .c 3,
  .c 89, .p pv3 [pv2,pv3,pv29,pv6163], .c 3, .p pv5 [pv2,pv131,pv4093], .c 823, .c 3,
  .p pv5 [pv2,pv7,pv38299], .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv61,pv293], .c 3, .c 5,
]
private theorem h0130c28 : checkBlock 1072131 128 b0130c28 = true := by
  decide +kernel

private def b0130c29 : List Row := [
  .p pv2 [pv2,pv3,pv7,pv2837], .c 3, .c 29, .c 7, .c 3, .p pv2 [pv2,pv13,pv41,pv503], .c 47, .c 3,
  .c 967, .c 5, .c 3, .c 13, .c 17, .c 3, .c 5, .c 19, .c 3, .c 7, .c 11, .c 3, .c 173,
  .p pv2 [pv2,pv3,pv7,pv17,pv751], .c 3, .p pv3 [pv2,pv97,pv691], .c 5, .c 3,
  .p pv7 [pv2,pv536219], .c 61, .c 3, .c 5, .p pv3 [pv2,pv3,pv47,pv3803], .c 3, .c 109, .c 983,
  .c 3, .p pv3 [pv2,pv7,pv11,pv1741], .p pv11 [pv2,pv3,pv59581], .c 3, .c 7, .c 5, .c 3, .c 67,
  .p pv7 [pv2,pv3,pv5,pv7,pv5107], .c 3, .c 5, .c 7, .c 3, .c 479, .c 113, .c 3, .c 13, .c 11,
  .c 3, .c 19, .c 5, .c 3, .c 233, .c 193, .c 3, .c 5, .c 29, .c 3, .c 11, .c 13, .c 3,
  .p pv2 [pv2,pv73,pv3673], .c 7, .c 3, .c 251, .c 5, .c 3, .c 97, .c 19, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv23,pv29,pv67], .c 3, .c 433, .p pv3 [pv2,pv3,pv178757], .c 3, .c 7, .c 43,
  .c 3, .c 151, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 1009, .c 3, .c 877, .c 137, .c 3, .c 11,
  .c 457, .c 3, .c 79, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 71, .c 3, .c 41, .c 7, .c 3, .c 19,
  .c 83, .c 3, .p pv2 [pv2,pv268153], .c 5, .c 3, .c 827, .c 11, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv19,pv97], .c 3, .c 7, .p pv5 [pv2,pv3,pv11,pv17,pv239], .c 3,
  .p pv2 [pv2,pv229,pv1171], .c 311, .c 3,
]
private theorem h0130c29 : checkBlock 1072387 128 b0130c29 = true := by
  decide +kernel

private def b0130c30 : List Row := [
  .c 11, .c 5, .c 3, .c 17, .c 23, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv191], .c 3, .c 449, .c 139,
  .c 3, .c 37, .c 13, .c 3, .c 7, .c 5, .c 3, .c 59, .c 29, .c 3, .c 5, .c 7, .c 3, .c 241, .c 31,
  .c 3, .c 23, .c 467, .c 3, .c 163, .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv29,pv137], .c 3,
  .c 5, .c 17, .c 3, .c 13, .c 97, .c 3, .c 619, .c 7, .c 3, .p pv2 [pv2,pv233,pv1151], .c 5,
  .c 3, .c 29, .c 37, .c 3, .c 5, .c 13, .c 3, .c 17, .c 11, .c 3, .c 7, .c 19, .c 3,
  .p pv2 [pv2,pv673,pv797], .c 5, .c 3, .c 127, .c 7, .c 3, .c 5, .c 263, .c 3, .c 157, .c 383,
  .c 3, .c 181, .c 23, .c 3, .p pv3 [pv2,pv7,pv19157], .c 5, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv5,pv149], .c 3, .c 5, .c 43, .c 3, .p pv2 [pv2,pv5,pv71,pv1511], .c 7, .c 3,
  .c 31, .c 11, .c 3, .p pv5 [pv2,pv47,pv101,pv113], .c 5, .c 3, .p pv2 [pv2,pv268207],
  .p pv7 [pv2,pv3,pv5,pv11,pv3251], .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv1753], .c 3, .c 7,
  .p pv3 [pv2,pv3,pv178807], .c 3, .c 41, .p pv11 [pv2,pv3,pv7,pv31,pv103], .c 3, .c 17, .c 5,
  .c 3, .p pv2 [pv2,pv23,pv83,pv281], .c 487, .c 3, .c 5, .p pv2 [pv2,pv3,pv163,pv1097], .c 3,
  .c 67, .c 19, .c 3, .c 13, .c 31, .c 3, .c 7, .c 5, .c 3, .c 37, .c 859, .c 3, .c 5, .c 7,
]
private theorem h0130c30 : checkBlock 1072643 128 b0130c30 = true := by
  decide +kernel

private def b0130c31 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv10729], .c 13, .c 3, .c 11, .c 571, .c 3, .c 29, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv11,pv6967], .c 17, .c 3, .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv19,pv5647],
  .p pv2 [pv2,pv3,pv7,pv53,pv241], .c 3, .p pv3 [pv2,pv43,pv3119], .c 7, .c 3,
  .p pv5 [pv2,pv13,pv29,pv1423], .c 5, .c 3, .c 19, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv89413],
  .c 3, .p pv13 [pv2,pv5,pv7,pv479], .c 37, .c 3, .c 7, .p pv11 [pv2,pv3,pv13,pv19,pv181], .c 3,
  .c 11, .c 5, .c 3, .c 43, .c 7, .c 3, .c 5, .c 19, .c 3, .p pv19 [pv2,pv5,pv61,pv1759], .c 683,
  .c 3, .p pv2 [pv2,pv23,pv107,pv109], .p pv3 [pv2,pv3,pv59611], .c 3, .c 31, .c 5, .c 3, .c 7,
  .c 41, .c 3, .c 5, .c 11, .c 3, .c 131, .c 7, .c 3, .c 73, .c 29, .c 3, .c 13, .c 5, .c 3,
  .c 11, .c 269, .c 3, .c 5, .c 821, .c 3, .c 7, .p pv2 [pv2,pv3,pv41,pv727], .c 3, .c 17, .c 13,
  .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv268267], .c 1021, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv223,pv401], .c 3, .c 839, .c 11, .c 3, .c 29, .p pv7 [pv2,pv3,pv23], .c 3,
  .c 7, .c 5, .c 3, .p pv2 [pv2,pv13,pv149,pv277], .c 19, .c 3, .c 5, .c 7, .c 3, .c 13,
  .p pv5 [pv2,pv3,pv61,pv733], .c 3, .p pv2 [pv2,pv11,pv29], .c 173, .c 3, .c 691, .c 5, .c 3,
  .c 421, .p pv3 [pv2,pv3,pv5,pv35771], .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv53657],
  .p pv7 [pv2,pv3,pv7,pv17,pv167], .c 3, .p pv2 [pv2,pv211,pv2543], .c 7, .c 3,
  .p pv3 [pv2,pv131],
]
private theorem h0130c31 : checkBlock 1072899 128 b0130c31 = true := by
  decide +kernel

def rows0130 : List Row :=
  b0130c00 ++ b0130c01 ++ b0130c02 ++ b0130c03 ++ b0130c04 ++ b0130c05 ++ b0130c06 ++ b0130c07 ++
  b0130c08 ++ b0130c09 ++ b0130c10 ++ b0130c11 ++ b0130c12 ++ b0130c13 ++ b0130c14 ++ b0130c15 ++
  b0130c16 ++ b0130c17 ++ b0130c18 ++ b0130c19 ++ b0130c20 ++ b0130c21 ++ b0130c22 ++ b0130c23 ++
  b0130c24 ++ b0130c25 ++ b0130c26 ++ b0130c27 ++ b0130c28 ++ b0130c29 ++ b0130c30 ++ b0130c31

attribute [local irreducible] checkBlock checkRows checkPrime

theorem checked0130 : checkBlock 1064963 4096 rows0130 = true :=
  checkBlock_append h0130c00 (
    checkBlock_append h0130c01 (
    checkBlock_append h0130c02 (
    checkBlock_append h0130c03 (
    checkBlock_append h0130c04 (
    checkBlock_append h0130c05 (
    checkBlock_append h0130c06 (
    checkBlock_append h0130c07 (
    checkBlock_append h0130c08 (
    checkBlock_append h0130c09 (
    checkBlock_append h0130c10 (
    checkBlock_append h0130c11 (
    checkBlock_append h0130c12 (
    checkBlock_append h0130c13 (
    checkBlock_append h0130c14 (
    checkBlock_append h0130c15 (
    checkBlock_append h0130c16 (
    checkBlock_append h0130c17 (
    checkBlock_append h0130c18 (
    checkBlock_append h0130c19 (
    checkBlock_append h0130c20 (
    checkBlock_append h0130c21 (
    checkBlock_append h0130c22 (
    checkBlock_append h0130c23 (
    checkBlock_append h0130c24 (
    checkBlock_append h0130c25 (
    checkBlock_append h0130c26 (
    checkBlock_append h0130c27 (
    checkBlock_append h0130c28 (
    checkBlock_append h0130c29 (
    checkBlock_append h0130c30 (
    h0130c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
