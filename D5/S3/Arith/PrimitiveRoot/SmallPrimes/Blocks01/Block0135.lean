/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0135
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0135.checked0135
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table017
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table020
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table024
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table030
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table041
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table061
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table062
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table115
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table116

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0135c00 : List Row := [
  .c 3, .c 5, .c 389, .c 3, .c 113, .c 19, .c 3, .c 7, .c 461, .c 3, .p pv5 [pv2,pv552971], .c 5,
  .c 3, .c 13, .c 7, .c 3, .c 5, .c 47, .c 3, .p pv7 [pv2,pv5,pv43,pv643],
  .p pv3 [pv2,pv3,pv11,pv13,pv1289], .c 3, .c 37, .c 17, .c 3, .c 11, .c 5, .c 3, .c 7, .c 349,
  .c 3, .c 5, .c 31, .c 3, .c 61, .c 7, .c 3, .p pv2 [pv2,pv276499], .p pv3 [pv2,pv3,pv184333],
  .c 3, .c 17, .c 5, .c 3, .c 19, .c 479, .c 3, .c 5, .c 11, .c 3, .c 7, .c 73, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv7,pv11,pv19], .c 3, .c 131, .c 5, .c 3, .c 11, .c 37, .c 3, .c 5, .c 19, .c 3,
  .c 47, .c 13, .c 3, .c 41, .c 107, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv276517], .c 17, .c 3,
  .c 5, .c 7, .c 3, .c 191, .c 11, .c 3, .p pv5 [pv2,pv553043], .c 29, .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv41,pv47], .p pv29 [pv2,pv3,pv5,pv1229], .c 3, .c 5, .c 463, .c 3, .c 31,
  .c 61, .c 3, .c 103, .c 7, .c 3, .c 19, .c 5, .c 3, .p pv3 [pv2,pv257,pv269], .c 13, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv569], .c 3, .c 83, .c 631, .c 3, .c 7, .c 11, .c 3, .c 619, .c 5, .c 3,
  .p pv13 [pv2,pv79,pv7001], .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv107,pv1723], .c 3, .c 11, .c 17,
  .c 3, .p pv3 [pv2,pv29,pv149],
]
private theorem h0135c00 : checkBlock 1105923 128 b0135c00 = true := by
  decide +kernel

private def b0135c01 : List Row := [
  .p pv2 [pv2,pv3,pv263,pv701], .c 3, .c 13, .c 5, .c 3, .c 7, .c 59, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv13,pv1013], .c 3, .p pv7 [pv2,pv5,pv5531], .c 7, .c 3, .c 17, .c 13, .c 3,
  .p pv2 [pv2,pv276553], .c 5, .c 3, .p pv2 [pv2,pv19,pv43,pv677], .c 41, .c 3, .c 5, .c 311,
  .c 3, .c 7, .p pv5 [pv2,pv3,pv46093], .c 3, .c 11, .c 47, .c 3, .p pv2 [pv2,pv73,pv7577], .c 5,
  .c 3, .p pv3 [pv2,pv11,pv13,pv967], .c 71, .c 3, .c 5, .p pv5 [pv2,pv3,pv19,pv1213], .c 3,
  .c 13, .c 29, .c 3, .p pv2 [pv2,pv7,pv31,pv2549], .c 53, .c 3, .c 7, .c 5, .c 3,
  .p pv11 [pv2,pv553139], .c 11, .c 3, .c 5, .c 7, .c 3, .c 691, .p pv5 [pv2,pv3,pv11,pv17,pv29],
  .c 3, .c 31, .c 229, .c 3, .c 11, .c 5, .c 3, .c 17, .p pv3 [pv2,pv3,pv5,pv36877], .c 3, .c 5,
  .p pv61 [pv2,pv3,pv79,pv389], .c 3, .c 29, .c 23, .c 3, .c 743, .c 7, .c 3, .c 47, .c 5, .c 3,
  .c 13, .c 853, .c 3, .c 5, .c 11, .c 3, .c 19, .c 599, .c 3, .c 7, .c 31, .c 3,
  .p pv2 [pv2,pv553181], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 17, .c 3,
  .p pv2 [pv2,pv5,pv11,pv47,pv107], .c 113, .c 3, .c 857, .c 19, .c 3, .c 71, .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv461], .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv2927], .c 3, .c 17, .c 7, .c 3,
  .c 13, .p pv3 [pv2,pv3,pv61,pv3023], .c 3, .p pv5 [pv2,pv553211], .c 5, .c 3,
  .p pv2 [pv2,pv17,pv53,pv307], .c 241, .c 3,
]
private theorem h0135c01 : checkBlock 1106179 128 b0135c01 = true := by
  decide +kernel

private def b0135c02 : List Row := [
  .c 5, .c 29, .c 3, .c 7, .c 13, .c 3, .p pv5 [pv2,pv11,pv19,pv2647],
  .p pv13 [pv2,pv3,pv7,pv37,pv89], .c 3, .c 181, .c 5, .c 3, .c 109, .c 23, .c 3, .c 5, .c 41,
  .c 3, .p pv7 [pv2,pv5,pv110647], .c 83, .c 3, .p pv5 [pv2,pv7,pv43,pv919], .c 11, .c 3, .c 7,
  .c 5, .c 3, .p pv3 [pv2,pv138311], .p pv2 [pv2,pv3,pv5,pv7,pv11,pv479], .c 3, .c 5, .c 7, .c 3,
  .c 11, .c 19, .c 3, .c 23, .p pv2 [pv2,pv3,pv13,pv41,pv173], .c 3, .c 17, .c 5, .c 3, .c 43,
  .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv223,pv827], .c 3, .p pv23 [pv2,pv5,pv17,pv23,pv283],
  .c 331, .c 3, .c 89, .c 7, .c 3, .p pv5 [pv2,pv167,pv3313], .c 5, .c 3, .c 41, .c 127, .c 3,
  .c 5, .c 131, .c 3, .c 607, .p pv2 [pv2,pv3,pv43,pv4289], .c 3, .c 7,
  .p pv11 [pv2,pv3,pv47,pv109], .c 3, .c 13, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 53, .c 3,
  .c 769, .p pv7 [pv2,pv3,pv11527], .c 3, .c 937, .c 13, .c 3, .c 643, .c 5, .c 3, .c 7, .c 11,
  .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv55331], .c 7, .c 3, .p pv2 [pv2,pv89,pv6217],
  .p pv2 [pv2,pv3,pv92219], .c 3, .c 11, .c 5, .c 3, .c 67, .c 839, .c 3, .c 5, .c 317, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv92221], .c 3, .c 101, .c 251, .c 3, .c 59, .c 5, .c 3, .c 29,
  .p pv3 [pv2,pv3,pv5,pv37,pv997], .c 3, .c 5, .c 11, .c 3, .c 173, .c 17, .c 3,
  .p pv7 [pv2,pv7,pv137,pv577], .p pv23 [pv2,pv3,pv11,pv131],
]
private theorem h0135c02 : checkBlock 1106435 128 b0135c02 = true := by
  decide +kernel

private def b0135c03 : List Row := [
  .c 3, .c 7, .c 5, .c 3, .c 11, .c 107, .c 3, .c 5, .c 7, .c 3, .c 79, .c 41, .c 3, .c 17,
  .c 439, .c 3, .c 61, .c 5, .c 3, .c 13, .c 19, .c 3, .c 5, .c 23, .c 3,
  .p pv2 [pv2,pv5,pv55337], .c 11, .c 3, .p pv2 [pv2,pv53,pv197], .c 7, .c 3, .c 73, .c 5, .c 3,
  .c 557, .p pv7 [pv2,pv3,pv5,pv23,pv401], .c 3, .c 5, .p pv3 [pv2,pv3,pv61487], .c 3,
  .p pv29 [pv2,pv5,pv7,pv97,pv163], .c 67, .c 3, .c 7, .p pv2 [pv2,pv3,pv184463], .c 3, .c 23,
  .c 5, .c 3, .p pv2 [pv2,pv19,pv14563], .c 7, .c 3, .c 5, .c 359, .c 3, .p pv3 [pv2,pv5,pv2767],
  .c 47, .c 3, .c 13, .c 11, .c 3, .c 283, .c 5, .c 3, .c 7, .p pv23 [pv2,pv3,pv5,pv11,pv13,pv43],
  .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv19,pv73], .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv17,pv41,pv397], .p pv3 [pv2,pv3,pv103,pv199], .c 3, .c 29, .c 5, .c 3, .c 311,
  .p pv2 [pv2,pv3,pv5,pv47,pv157], .c 3, .c 5, .c 139, .c 3, .c 7, .c 43, .c 3, .c 97, .c 79,
  .c 3, .c 1009, .c 5, .c 3, .c 701, .p pv7 [pv2,pv3,pv5,pv1153], .c 3, .c 5, .c 17, .c 3,
  .p pv2 [pv2,pv5,pv71,pv1559], .c 89, .c 3, .c 11, .c 59, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv2287], .c 13, .c 3, .c 5, .c 7, .c 3, .c 17, .p pv2 [pv2,pv3,pv184487], .c 3,
  .p pv5 [pv2,pv553463], .c 37, .c 3, .c 163, .c 5, .c 3, .p pv2 [pv2,pv7,pv17,pv4651], .c 11,
  .c 3, .c 5,
]
private theorem h0135c03 : checkBlock 1106691 128 b0135c03 = true := by
  decide +kernel

private def b0135c04 : List Row := [
  .c 991, .c 3, .c 487, .p pv37 [pv2,pv3,pv7,pv11,pv599], .c 3, .p pv2 [pv2,pv276739], .c 7, .c 3,
  .c 11, .c 5, .c 3, .c 479, .c 83, .c 3, .c 5, .p pv17 [pv2,pv3,pv13,pv887], .c 3, .c 151,
  .c 233, .c 3, .c 7, .c 13, .c 3, .p pv3 [pv2,pv43,pv1609], .c 5, .c 3,
  .p pv11 [pv2,pv419,pv1321], .c 7, .c 3, .c 5, .c 11, .c 3, .c 53, .c 23, .c 3, .c 29,
  .p pv2 [pv2,pv3,pv11,pv5591], .c 3, .c 17, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv36901], .c 3,
  .c 5, .c 199, .c 3, .c 13, .c 7, .c 3, .p pv5 [pv2,pv29,pv19087], .p pv7 [pv2,pv3,pv193,pv239],
  .c 3, .p pv2 [pv2,pv276763], .c 5, .c 3, .c 23, .c 97, .c 3, .c 5, .c 13, .c 3, .c 7, .c 11,
  .c 3, .c 37, .c 227, .c 3, .p pv2 [pv2,pv23,pv41,pv587], .c 5, .c 3, .c 61, .c 17, .c 3, .c 5,
  .c 137, .c 3, .p pv2 [pv2,pv5,pv11071], .c 31, .c 3, .p pv5 [pv2,pv7,pv11,pv13,pv79],
  .p pv7 [pv2,pv3,pv17,pv67], .c 3, .c 7, .c 5, .c 3, .c 13, .c 43, .c 3, .c 5, .c 7, .c 3,
  .c 593, .c 29, .c 3, .c 83, .c 11, .c 3, .c 683, .c 5, .c 3, .c 19, .c 23, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv257,pv359], .c 3, .c 11, .c 409, .c 3, .p pv5 [pv2,pv553583], .c 7, .c 3,
  .p pv2 [pv2,pv11,pv25163], .c 5, .c 3, .c 47, .c 433, .c 3, .c 5, .c 19, .c 3, .c 29, .c 17,
  .c 3, .c 7, .p pv7 [pv2,pv3,pv61511], .c 3,
]
private theorem h0135c04 : checkBlock 1106947 128 b0135c04 = true := by
  decide +kernel

private def b0135c05 : List Row := [
  .p pv2 [pv2,pv553601], .c 5, .c 3, .c 1013, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv233], .c 3,
  .c 727, .c 13, .c 3, .c 11, .c 863, .c 3, .c 397, .c 5, .c 3, .c 7, .c 193, .c 3, .c 5, .c 293,
  .c 3, .c 859, .c 7, .c 3, .c 467, .c 163, .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv276817], .c 11,
  .c 3, .c 5, .c 347, .c 3, .c 7, .c 151, .c 3, .c 41, .c 23, .c 3, .c 11, .c 5, .c 3, .c 37,
  .c 13, .c 3, .c 5, .c 29, .c 3, .c 457, .c 127, .c 3, .p pv3 [pv2,pv7,pv71,pv557],
  .p pv3 [pv2,pv3,pv184553], .c 3, .c 7, .c 5, .c 3, .c 17, .c 109, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv13,pv4259], .c 79, .c 3, .p pv2 [pv2,pv17,pv32569], .c 307, .c 3, .c 13, .c 5,
  .c 3, .c 11, .c 353, .c 3, .c 5, .c 47, .c 3, .c 59, .c 37, .c 3, .c 19, .c 7, .c 3,
  .p pv5 [pv2,pv31,pv53,pv337], .c 5, .c 3, .p pv2 [pv2,pv276847], .c 619, .c 3, .c 5, .c 17,
  .c 3, .p pv53 [pv2,pv5,pv7,pv113], .c 11, .c 3, .c 7, .p pv11 [pv2,pv3,pv23071], .c 3, .c 31,
  .c 5, .c 3, .p pv2 [pv2,pv13,pv191,pv223], .c 7, .c 3, .c 5, .c 23, .c 3, .c 13,
  .p pv5 [pv2,pv3,pv1709], .c 3, .c 373, .p pv3 [pv2,pv3,pv379,pv487], .c 3, .c 67, .c 5, .c 3,
  .c 7, .c 41, .c 3, .c 5, .c 13,
]
private theorem h0135c05 : checkBlock 1107203 128 b0135c05 = true := by
  decide +kernel

private def b0135c06 : List Row := [
  .c 3, .c 47, .c 7, .c 3, .p pv2 [pv2,pv553733], .c 11, .c 3, .c 23, .c 5, .c 3,
  .p pv7 [pv2,pv157,pv3527], .c 29, .c 3, .c 5, .p pv3 [pv2,pv3,pv20509], .c 3, .c 7, .c 263,
  .c 3, .p pv3 [pv2,pv13,pv23,pv463], .c 17, .c 3, .p pv5 [pv2,pv11,pv50341], .c 5, .c 3, .c 13,
  .p pv17 [pv2,pv3,pv5,pv19,pv29,pv67], .c 3, .c 5, .c 149, .c 3, .c 37,
  .p pv2 [pv2,pv3,pv13,pv4733], .c 3, .p pv5 [pv2,pv7,pv239,pv331], .c 19, .c 3, .c 7, .c 5, .c 3,
  .c 29, .c 53, .c 3, .c 5, .c 7, .c 3, .c 43, .p pv7 [pv2,pv3,pv83,pv139], .c 3, .c 11, .c 103,
  .c 3, .c 733, .c 5, .c 3, .p pv3 [pv2,pv7,pv11,pv29,pv31], .p pv2 [pv2,pv3,pv5,pv36919], .c 3,
  .c 5, .c 61, .c 3, .p pv2 [pv2,pv5,pv79,pv701], .p pv3 [pv2,pv3,pv7,pv26371], .c 3, .c 13, .c 7,
  .c 3, .p pv3 [pv2,pv138449], .c 5, .c 3, .c 31, .c 11, .c 3, .c 5, .c 59, .c 3, .c 23, .c 13,
  .c 3, .c 7, .p pv23 [pv2,pv3,pv17,pv10859], .c 3, .c 11, .c 5, .c 3, .c 73, .c 7, .c 3, .c 5,
  .c 43, .c 3, .c 223, .c 19, .c 3, .c 53, .c 47, .c 3, .c 1019, .c 5, .c 3, .c 7, .c 31, .c 3,
  .c 5, .c 11, .c 3, .c 71, .c 7, .c 3, .p pv2 [pv2,pv276919], .p pv3 [pv2,pv3,pv11,pv13,pv1291],
  .c 3, .c 449, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 41, .c 3, .c 7, .c 17, .c 3, .c 313,
  .c 773, .c 3, .c 29,
]
private theorem h0135c06 : checkBlock 1107459 128 b0135c06 = true := by
  decide +kernel

private def b0135c07 : List Row := [
  .c 5, .c 3, .c 19, .p pv7 [pv2,pv3,pv5,pv17,pv181], .c 3, .c 5, .p pv11 [pv2,pv3,pv23,pv349],
  .c 3, .c 197, .c 11, .c 3, .c 17, .c 113, .c 3, .c 7, .c 5, .c 3, .c 23,
  .p pv3 [pv2,pv3,pv5,pv7,pv211], .c 3, .c 5, .c 7, .c 3, .c 739, .p pv2 [pv2,pv3,pv184627], .c 3,
  .c 109, .c 13, .c 3, .p pv2 [pv2,pv23,pv12041], .c 5, .c 3, .c 41,
  .p pv29 [pv2,pv3,pv5,pv37,pv499], .c 3, .c 5, .p pv2 [pv2,pv3,pv184631], .c 3,
  .p pv11 [pv2,pv5,pv47,pv2357], .p pv5 [pv2,pv3,pv7,pv157], .c 3, .p pv2 [pv2,pv276949], .c 7,
  .c 3, .p pv2 [pv2,pv553901], .c 5, .c 3, .c 43, .p pv2 [pv2,pv3,pv5,pv11,pv373], .c 3, .c 5,
  .c 37, .c 3, .c 11, .p pv13 [pv2,pv3,pv17,pv10861], .c 3, .c 7, .c 29, .c 3, .c 19, .c 5, .c 3,
  .c 17, .c 7, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv22157],
  .p pv2 [pv2,pv3,pv19,pv43,pv113], .c 3, .c 331, .c 53, .c 3, .c 887, .c 5, .c 3, .c 7, .c 19,
  .c 3, .c 5, .c 241, .c 3, .p pv3 [pv2,pv5,pv27697], .c 7, .c 3, .c 11, .c 643, .c 3,
  .p pv2 [pv2,pv173,pv1601], .c 5, .c 3, .c 13, .c 181, .c 3, .c 5, .c 17, .c 3, .c 7,
  .p pv17 [pv2,pv3,pv13,pv53,pv67], .c 3, .p pv2 [pv2,pv29,pv9551], .c 137, .c 3,
  .p pv2 [pv2,pv553961], .c 5, .c 3, .p pv3 [pv2,pv19,pv37,pv197], .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv3847], .c 3, .c 17, .c 41, .c 3, .c 19, .c 157, .c 3, .c 7, .c 5, .c 3,
  .c 463, .c 59, .c 3, .c 5, .c 7, .c 3,
]
private theorem h0135c07 : checkBlock 1107715 128 b0135c07 = true := by
  decide +kernel

private def b0135c08 : List Row := [
  .c 31, .c 367, .c 3, .c 13, .c 23, .c 3, .c 281, .c 5, .c 3, .p pv2 [pv2,pv7,pv5653], .c 191,
  .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv277], .c 13, .c 3, .p pv5 [pv2,pv554003], .c 7, .c 3,
  .c 193, .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv59,pv313], .c 3, .c 5, .c 397, .c 3, .c 97,
  .c 31, .c 3, .c 7, .c 37, .c 3, .c 17, .c 5, .c 3, .p pv3 [pv2,pv23,pv3011], .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv137,pv337], .c 3, .c 19, .c 11, .c 3, .c 43, .p pv2 [pv2,pv3,pv13,pv7103],
  .c 3, .p pv3 [pv2,pv7,pv47,pv421], .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 223, .c 3,
  .p pv2 [pv2,pv5,pv29,pv3821], .c 7, .c 3, .c 71, .c 19, .c 3, .p pv5 [pv2,pv554051], .c 5, .c 3,
  .c 503, .c 17, .c 3, .c 5, .c 23, .c 3, .c 7, .p pv3 [pv2,pv3,pv184687], .c 3,
  .p pv5 [pv2,pv31,pv61,pv293], .c 11, .c 3, .c 13, .c 5, .c 3, .c 89, .c 653, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv13,pv14207], .c 3, .c 11, .c 43, .c 3, .c 31, .c 13, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv71,pv1951], .p pv3 [pv2,pv3,pv5,pv7,pv1759], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv67,pv827], .c 373, .c 3, .c 37, .c 41, .c 3, .c 137, .c 5, .c 3, .c 107,
  .p pv7 [pv2,pv3,pv5,pv1847], .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv29,pv193], .c 3, .c 13, .c 17,
  .c 3, .c 11, .c 7, .c 3, .p pv5 [pv2,pv547,pv1013], .c 5,
]
private theorem h0135c08 : checkBlock 1107971 128 b0135c08 = true := by
  decide +kernel

private def b0135c09 : List Row := [
  .c 3, .p pv7 [pv2,pv11,pv89,pv283], .c 199, .c 3, .c 5, .c 13, .c 3,
  .p pv3 [pv2,pv5,pv7,pv1979], .c 239, .c 3, .c 7, .c 677, .c 3, .p pv2 [pv2,pv277063], .c 5,
  .c 3, .p pv2 [pv2,pv554129], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv184711], .c 3, .c 41, .c 101,
  .c 3, .c 277, .c 499, .c 3, .c 11, .c 5, .c 3, .c 7, .c 79, .c 3, .c 5, .c 929, .c 3, .c 23,
  .c 7, .c 3, .c 47, .c 61, .c 3, .p pv3 [pv2,pv31,pv41,pv109], .c 5, .c 3, .c 839,
  .p pv17 [pv2,pv3,pv5,pv2309], .c 3, .c 5, .c 11, .c 3, .c 7, .c 313, .c 3,
  .p pv3 [pv2,pv53,pv1307], .c 953, .c 3, .c 31, .c 5, .c 3, .c 11, .c 29, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv92363], .c 3, .p pv13 [pv2,pv5,pv11,pv229], .p pv2 [pv2,pv3,pv184727], .c 3,
  .c 13, .p pv7 [pv2,pv3,pv43,pv179], .c 3, .c 7, .c 5, .c 3, .c 167, .c 67, .c 3, .c 5, .c 7,
  .c 3, .c 131, .c 11, .c 3, .p pv2 [pv2,pv277099], .c 193, .c 3, .c 19, .c 5, .c 3, .c 29, .c 43,
  .c 3, .c 5, .c 17, .c 3, .c 109, .p pv3 [pv2,pv3,pv7,pv19,pv463], .c 3,
  .p pv2 [pv2,pv11,pv50383], .c 7, .c 3, .c 59, .c 5, .c 3, .c 23, .c 19, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv37,pv4993], .c 3, .c 17, .p pv2 [pv2,pv3,pv71,pv1301], .c 3, .c 7, .c 11,
  .c 3, .p pv5 [pv2,pv23,pv24097], .c 5, .c 3, .p pv2 [pv2,pv17,pv16301], .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv41,pv751], .c 3, .c 11,
]
private theorem h0135c09 : checkBlock 1108227 128 b0135c09 = true := by
  decide +kernel

private def b0135c10 : List Row := [
  .c 37, .c 3, .p pv5 [pv2,pv103,pv5381], .p pv11 [pv2,pv3,pv46187], .c 3, .c 421, .c 5, .c 3,
  .c 7, .p pv37 [pv2,pv3,pv5,pv739], .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv26393], .c 3, .c 283, .c 7,
  .c 3, .c 19, .c 17, .c 3, .c 13, .c 5, .c 3, .c 31, .c 23, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv13,pv17,pv19], .c 3, .c 7, .p pv7 [pv2,pv3,pv47,pv3931], .c 3, .c 11,
  .c 13, .c 3, .c 17, .c 5, .c 3, .p pv7 [pv2,pv11,pv41,pv1229], .p pv47 [pv2,pv3,pv5,pv31,pv149],
  .c 3, .c 5, .p pv3 [pv2,pv3,pv2281], .c 3, .p pv7 [pv2,pv5,pv17,pv6521],
  .p pv2 [pv2,pv3,pv92381], .c 3, .c 23, .p pv2 [pv2,pv3,pv73,pv2531], .c 3, .c 7, .c 5, .c 3,
  .c 47, .c 11, .c 3, .c 5, .c 7, .c 3, .c 13, .p pv2 [pv2,pv3,pv11,pv509], .c 3, .c 79,
  .p pv7 [pv2,pv3,pv2887], .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv7,pv79187], .c 17, .c 3, .c 5,
  .c 13, .c 3, .c 19, .p pv5 [pv2,pv3,pv7,pv6599], .c 3, .c 811, .c 7, .c 3, .c 113, .c 5, .c 3,
  .c 67, .c 73, .c 3, .c 5, .c 11, .c 3, .c 271, .p pv3 [pv2,pv3,pv184777], .c 3, .c 7, .c 19,
  .c 3, .c 89, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 911, .c 3, .p pv2 [pv2,pv5,pv11,pv10079],
  .p pv2 [pv2,pv3,pv13,pv23,pv103], .c 3, .p pv3 [pv2,pv138587], .c 29, .c 3,
  .p pv5 [pv2,pv7,pv79193], .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv97,pv127], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv67,pv197], .c 3, .c 239, .c 7, .c 3, .p pv5 [pv2,pv19,pv163,pv179],
  .p pv7 [pv2,pv3,pv29,pv59], .c 3, .p pv2 [pv2,pv277183], .c 5, .c 3,
]
private theorem h0135c10 : checkBlock 1108483 128 b0135c10 = true := by
  decide +kernel

private def b0135c11 : List Row := [
  .p pv2 [pv2,pv23,pv24103], .c 137, .c 3, .c 5, .p pv2 [pv2,pv3,pv31,pv1987], .c 3, .c 7,
  .p pv5 [pv2,pv3,pv23099], .c 3, .c 13, .p pv3 [pv2,pv3,pv7,pv26399], .c 3, .c 41, .c 5, .c 3,
  .c 547, .p pv3 [pv2,pv3,pv5,pv13,pv2843], .c 3, .c 5, .c 31, .c 3, .p pv3 [pv2,pv5,pv55439],
  .c 13, .c 3, .c 59, .c 11, .c 3, .c 7, .c 5, .c 3, .c 409, .p pv19 [pv2,pv3,pv5,pv7,pv11], .c 3,
  .c 5, .c 7, .c 3, .c 11, .c 53, .c 3, .p pv3 [pv2,pv37,pv1873], .p pv2 [pv2,pv3,pv229,pv269],
  .c 3, .p pv5 [pv2,pv11,pv13,pv3877], .c 5, .c 3, .c 443, .c 277, .c 3, .c 5, .c 127, .c 3,
  .c 43, .c 587, .c 3, .c 233, .c 7, .c 3, .c 23, .c 5, .c 3, .c 17, .c 13, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv11,pv53,pv317], .c 3, .c 47, .c 29, .c 3, .c 7, .c 101, .c 3, .c 787, .c 5,
  .c 3, .c 163, .c 7, .c 3, .c 5, .c 19, .c 3, .c 31, .p pv5 [pv2,pv3,pv29,pv6373], .c 3,
  .p pv2 [pv2,pv554453], .p pv11 [pv2,pv3,pv30803], .c 3, .c 13, .c 5, .c 3, .c 7, .c 11, .c 3,
  .c 5, .c 17, .c 3, .c 29, .c 7, .c 3, .c 947, .c 13, .c 3, .c 11, .c 5, .c 3, .c 71, .c 359,
  .c 3, .c 5, .p pv13 [pv2,pv3,pv92413], .c 3, .c 7, .c 31, .c 3, .p pv5 [pv2,pv109,pv5087],
  .c 859, .c 3, .c 19, .c 5, .c 3, .c 223, .c 569, .c 3, .c 5, .c 11, .c 3, .c 13,
  .p pv5 [pv2,pv3,pv19],
]
private theorem h0135c11 : checkBlock 1108739 128 b0135c11 = true := by
  decide +kernel

private def b0135c12 : List Row := [
  .c 3, .p pv2 [pv2,pv7,pv39607], .p pv3 [pv2,pv3,pv11,pv1867], .c 3, .c 7, .c 5, .c 3, .c 11,
  .c 19, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv11,pv71], .c 59, .c 3, .c 199, .c 17, .c 3,
  .p pv3 [pv2,pv138629], .c 5, .c 3, .c 389, .c 61, .c 3, .c 5, .c 29, .c 3, .c 67, .c 11, .c 3,
  .p pv7 [pv2,pv13,pv31,pv43], .c 7, .c 3, .c 17, .c 5, .c 3, .c 13, .c 263, .c 3, .c 5, .c 283,
  .c 3, .c 79, .c 23, .c 3, .c 7, .c 73, .c 3, .c 419, .c 5, .c 3, .c 43, .c 7, .c 3, .c 5,
  .c 281, .c 3, .c 509, .p pv7 [pv2,pv3,pv37,pv1249], .c 3, .p pv2 [pv2,pv277279], .c 11, .c 3,
  .p pv5 [pv2,pv7,pv227,pv349], .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 191, .c 3, .c 11, .c 7,
  .c 3, .c 13, .c 31, .c 3, .c 47, .c 5, .c 3, .p pv7 [pv2,pv661,pv839],
  .p pv29 [pv2,pv3,pv5,pv13,pv79], .c 3, .c 5, .p pv3 [pv2,pv3,pv401,pv461], .c 3, .c 7, .c 13,
  .c 3, .c 131, .c 881, .c 3, .c 317, .c 5, .c 3, .p pv2 [pv2,pv277297], .c 307, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv11,pv2801], .c 3, .c 19, .c 271, .c 3, .c 11, .c 521, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv127,pv397], .c 23, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv110923], .c 17,
  .c 3, .c 53, .c 19, .c 3, .p pv2 [pv2,pv31,pv17891], .c 5, .c 3, .p pv13 [pv2,pv7,pv619],
]
private theorem h0135c12 : checkBlock 1108995 128 b0135c12 = true := by
  decide +kernel

private def b0135c13 : List Row := [
  .c 11, .c 3, .c 5, .p pv13 [pv2,pv3,pv46219], .c 3, .c 907, .c 179, .c 3, .c 17, .c 7, .c 3,
  .c 11, .c 5, .c 3, .c 29, .p pv23 [pv2,pv3,pv5,pv2311], .c 3, .c 5, .p pv3 [pv2,pv3,pv61627],
  .c 3, .p pv2 [pv2,pv5,pv7,pv13,pv23,pv53], .c 109, .c 3, .c 7, .c 743, .c 3, .c 13, .c 5, .c 3,
  .p pv7 [pv2,pv29,pv73,pv131], .c 7, .c 3, .c 5, .c 11, .c 3, .c 113, .c 241, .c 3,
  .p pv5 [pv2,pv554663], .c 13, .c 3, .c 379, .c 5, .c 3, .c 7, .c 47, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv61,pv433], .c 3, .p pv11 [pv2,pv5,pv11,pv2017], .c 7, .c 3, .c 43, .c 23,
  .c 3, .p pv2 [pv2,pv157,pv3533], .c 5, .c 3, .c 17, .c 37, .c 3, .c 5, .c 59, .c 3, .c 7, .c 11,
  .c 3, .p pv2 [pv2,pv17,pv67,pv487], .c 97, .c 3, .p pv3 [pv2,pv69337], .c 5, .c 3,
  .p pv7 [pv2,pv554699], .p pv7 [pv2,pv3,pv5,pv43], .c 3, .c 5, .c 13, .c 3,
  .p pv2 [pv2,pv5,pv19,pv5839], .c 103, .c 3, .c 719, .c 41, .c 3, .c 7, .c 5, .c 3, .c 19,
  .p pv11 [pv2,pv3,pv5,pv7,pv587], .c 3, .c 5, .c 7, .c 3, .c 367, .c 43, .c 3, .c 653, .c 11,
  .c 3, .c 29, .c 5, .c 3, .c 13, .c 83, .c 3, .c 5, .c 19, .c 3, .c 11,
  .p pv5 [pv2,pv3,pv7,pv13,pv127], .c 3, .p pv2 [pv2,pv79,pv3511], .c 7, .c 3, .c 107, .c 5, .c 3,
  .p pv3 [pv2,pv17,pv4079], .p pv3 [pv2,pv3,pv5,pv31,pv1193], .c 3, .c 5, .c 23, .c 3, .c 41,
  .c 593, .c 3,
]
private theorem h0135c13 : checkBlock 1109251 128 b0135c13 = true := by
  decide +kernel

private def b0135c14 : List Row := [
  .c 7, .p pv2 [pv2,pv3,pv92459], .c 3, .p pv3 [pv2,pv331,pv419], .c 5, .c 3, .c 37, .c 7, .c 3,
  .c 5, .c 73, .c 3, .p pv2 [pv2,pv5,pv181,pv613], .p pv5 [pv2,pv3,pv92461], .c 3, .c 11, .c 17,
  .c 3, .c 19, .c 5, .c 3, .c 7, .c 383, .c 3, .c 5, .c 193, .c 3, .p pv3 [pv2,pv5,pv27739], .c 7,
  .c 3, .c 401, .c 29, .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv554789], .c 11, .c 3, .c 5, .c 67,
  .c 3, .c 7, .c 37, .c 3, .c 263, .c 127, .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv53,pv2617],
  .p pv2 [pv2,pv3,pv5,pv12329], .c 3, .c 5, .c 409, .c 3, .c 179, .c 47, .c 3, .c 29,
  .p pv7 [pv2,pv3,pv13,pv2371], .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv19,pv29201], .c 13, .c 3,
  .c 5, .c 7, .c 3, .c 61, .p pv5 [pv2,pv3,pv89,pv1039], .c 3, .c 19, .c 71, .c 3,
  .p pv5 [pv2,pv277,pv2003], .c 5, .c 3, .c 11, .c 251, .c 3, .c 5, .c 239, .c 3, .c 23, .c 701,
  .c 3, .c 101, .c 7, .c 3, .c 13, .c 5, .c 3, .c 151, .c 43, .c 3, .c 5, .c 31, .c 3, .c 181,
  .c 11, .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv103,pv5387], .c 5, .c 3, .c 109, .c 7, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv15413], .c 3, .c 37, .c 17, .c 3, .c 41, .p pv2 [pv2,pv3,pv92479], .c 3,
  .c 853, .c 5, .c 3, .c 7, .p pv23 [pv2,pv3,pv5,pv17],
]
private theorem h0135c14 : checkBlock 1109507 128 b0135c14 = true := by
  decide +kernel

private def b0135c15 : List Row := [
  .c 3, .c 5, .c 53, .c 3, .c 13, .c 7, .c 3, .c 17, .c 11, .c 3, .p pv5 [pv2,pv554891], .c 5,
  .c 3, .p pv2 [pv2,pv41,pv67,pv101], .p pv7 [pv2,pv3,pv5,pv11,pv19,pv59], .c 3, .c 5, .c 13,
  .c 3, .c 7, .c 227, .c 3, .c 983, .c 19, .c 3, .p pv2 [pv2,pv11,pv2293], .c 5, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv5,pv53,pv349], .c 3, .c 5, .c 1021, .c 3, .c 31, .c 157, .c 3, .c 137,
  .p pv3 [pv2,pv3,pv109,pv1697], .c 3, .c 7, .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv7,pv151],
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv211,pv263], .c 547, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv92489], .c 3, .c 43, .c 5, .c 3, .c 17, .p pv13 [pv2,pv3,pv5,pv3083], .c 3,
  .c 5, .p pv5 [pv2,pv3,pv113,pv1637], .c 3, .p pv2 [pv2,pv5,pv110989], .c 31, .c 3,
  .p pv3 [pv2,pv17,pv8161], .c 7, .c 3, .p pv5 [pv2,pv554951], .c 5, .c 3,
  .p pv2 [pv2,pv59,pv4703], .c 11, .c 3, .c 5, .c 29, .c 3, .p pv11 [pv2,pv5,pv7,pv991], .c 19,
  .c 3, .c 7, .c 631, .c 3, .c 11, .c 5, .c 3, .c 277, .c 7, .c 3, .c 5, .c 17, .c 3,
  .p pv19 [pv2,pv5,pv79,pv281], .c 13, .c 3, .c 23, .c 43, .c 3, .c 37, .c 5, .c 3, .c 7, .c 97,
  .c 3, .c 5, .c 11, .c 3, .c 17, .c 7, .c 3, .p pv5 [pv2,pv31,pv17903], .c 67, .c 3, .c 41, .c 5,
  .c 3, .c 11, .c 151, .c 3, .c 5, .p pv3 [pv2,pv3,pv61667], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv233,pv397], .c 3, .c 31,
]
private theorem h0135c15 : checkBlock 1109763 128 b0135c15 = true := by
  decide +kernel

private def b0135c16 : List Row := [
  .p pv2 [pv2,pv3,pv7,pv13,pv19,pv107], .c 3, .p pv5 [pv2,pv199,pv2789], .c 5, .c 3, .c 79, .c 13,
  .c 3, .c 5, .c 19, .c 3, .p pv3 [pv2,pv5,pv27751], .c 11, .c 3, .c 601, .c 17, .c 3, .c 7, .c 5,
  .c 3, .c 467, .p pv2 [pv2,pv3,pv5,pv7,pv881], .c 3, .c 5, .c 7, .c 3, .c 211, .c 181, .c 3,
  .p pv2 [pv2,pv11,pv25229], .c 31, .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv7,pv43,pv461], .c 29,
  .c 3, .c 5, .c 89, .c 3, .c 557, .p pv3 [pv2,pv3,pv7,pv26431], .c 3, .c 127, .c 7, .c 3, .c 19,
  .c 5, .c 3, .c 569, .c 503, .c 3, .c 5, .p pv3 [pv2,pv3,pv185021], .c 3, .c 11,
  .p pv7 [pv2,pv3,pv19,pv541], .c 3, .c 7, .c 61, .c 3, .c 613, .c 5, .c 3, .c 29, .c 7, .c 3,
  .c 5, .c 41, .c 3, .c 13, .c 269, .c 3, .p pv5 [pv2,pv555083], .c 349, .c 3, .c 251, .c 5, .c 3,
  .c 7, .p pv29 [pv2,pv3,pv5,pv18503], .c 3, .c 5, .c 13, .c 3, .c 53, .c 7, .c 3, .c 11, .c 149,
  .c 3, .c 31, .c 5, .c 3, .c 283, .c 313, .c 3, .c 5, .c 43, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv37,pv1667], .c 3, .c 19, .p pv2 [pv2,pv3,pv7,pv13217], .c 3, .c 23, .c 5,
  .c 3, .c 13, .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv19,pv9739], .c 3, .c 521, .c 17, .c 3, .c 67,
  .c 37, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv277567], .p pv3 [pv2,pv3,pv5,pv7,pv17,pv311], .c 3,
]
private theorem h0135c16 : checkBlock 1110019 128 b0135c16 = true := by
  decide +kernel

private def b0135c17 : List Row := [
  .c 5, .c 7, .c 3, .c 47, .c 191, .c 3, .c 17, .p pv7 [pv2,pv3,pv23131], .c 3, .c 101, .c 5,
  .c 3, .c 761, .p pv2 [pv2,pv3,pv5,pv3701], .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv111031],
  .p pv11 [pv2,pv3,pv7,pv2203], .c 3, .c 13, .c 7, .c 3, .c 29, .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv13,pv73], .c 3, .c 5, .c 179, .c 3, .c 19, .c 13, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv23,pv149], .c 3, .p pv3 [pv2,pv29,pv2393], .c 5, .c 3, .c 97, .c 7, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv61687], .c 3, .c 23, .c 11, .c 3, .c 449, .c 19, .c 3, .c 61, .c 5,
  .c 3, .c 7, .c 67, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv13219], .c 3, .p pv3 [pv2,pv5,pv347], .c 7,
  .c 3, .c 37, .c 397, .c 3, .p pv2 [pv2,pv277603], .c 5, .c 3, .c 307, .c 13, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv185071], .c 3, .c 7, .p pv17 [pv2,pv3,pv43,pv269], .c 3, .c 691, .c 11, .c 3,
  .c 103, .c 5, .c 3, .p pv3 [pv2,pv69403], .c 31, .c 3, .c 5, .c 17, .c 3, .c 11, .c 23, .c 3,
  .p pv2 [pv2,pv7,pv79319], .c 47, .c 3, .c 7, .c 5, .c 3, .p pv13 [pv2,pv233,pv2383], .c 37,
  .c 3, .c 5, .c 7, .c 3, .c 17, .c 19, .c 3, .c 29, .c 13, .c 3, .c 79, .c 5, .c 3, .c 23, .c 71,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv47,pv179], .c 3, .p pv3 [pv2,pv5,pv27763],
  .p pv2 [pv2,pv3,pv7,pv137,pv193], .c 3, .c 11, .c 7,
]
private theorem h0135c17 : checkBlock 1110275 128 b0135c17 = true := by
  decide +kernel

private def b0135c18 : List Row := [
  .c 3, .p pv2 [pv2,pv23,pv12071], .c 5, .c 3, .p pv2 [pv2,pv11,pv13,pv353],
  .p pv2 [pv2,pv3,pv5,pv83,pv223], .c 3, .c 5, .p pv2 [pv2,pv3,pv103,pv599], .c 3, .c 13, .c 97,
  .c 3, .c 7, .c 17, .c 3, .c 47, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 13, .c 3, .c 311,
  .p pv3 [pv2,pv3,pv11,pv71,pv79], .c 3, .p pv2 [pv2,pv555293], .p pv23 [pv2,pv3,pv19,pv4871],
  .c 3, .c 11, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 19, .c 3,
  .p pv13 [pv2,pv5,pv17,pv47,pv139], .c 7, .c 3, .p pv3 [pv2,pv13,pv59,pv181], .c 199, .c 3,
  .c 83, .c 5, .c 3, .c 13, .c 89, .c 3, .c 5, .c 11, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv13,pv29,pv491], .c 3, .c 23, .c 41, .c 3, .c 71, .c 5, .c 3, .c 11, .c 17,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv37,pv5003], .c 3, .c 29, .c 541, .c 3, .c 113,
  .p pv3 [pv2,pv3,pv17,pv10889], .c 3, .c 7, .c 5, .c 3, .c 593, .c 1039, .c 3, .c 5, .c 7, .c 3,
  .c 269, .c 11, .c 3, .c 13, .p pv2 [pv2,pv3,pv30853], .c 3, .p pv3 [pv2,pv17,pv8167], .c 5,
  .c 3, .p pv7 [pv2,pv7,pv79337], .c 19, .c 3, .c 5, .p pv5 [pv2,pv3,pv67,pv307], .c 3, .c 41,
  .c 13, .c 3, .c 463, .c 7, .c 3, .p pv5 [pv2,pv127,pv4373], .c 5, .c 3, .c 61, .c 47, .c 3,
  .c 5, .c 809, .c 3, .c 31, .c 17, .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv13,pv41,pv521], .c 5,
  .c 3, .p pv2 [pv2,pv19,pv29231], .c 7, .c 3, .c 5,
]
private theorem h0135c18 : checkBlock 1110531 128 b0135c18 = true := by
  decide +kernel

private def b0135c19 : List Row := [
  .c 29, .c 3, .c 11, .c 59, .c 3, .c 17, .c 563, .c 3, .p pv7 [pv2,pv7,pv11,pv7213], .c 5, .c 3,
  .c 7, .c 13, .c 3, .c 5, .p pv17 [pv2,pv3,pv7,pv19,pv29], .c 3, .p pv2 [pv2,pv5,pv55541], .c 7,
  .c 3, .c 53, .c 271, .c 3, .c 173, .c 5, .c 3, .p pv7 [pv2,pv555419], .c 73, .c 3, .c 5, .c 487,
  .c 3, .c 7, .c 641, .c 3, .c 11, .p pv2 [pv2,pv3,pv7,pv26449], .c 3, .c 13, .c 5, .c 3, .c 127,
  .c 61, .c 3, .c 5, .c 23, .c 3, .p pv3 [pv2,pv5,pv53,pv131], .c 197, .c 3,
  .p pv5 [pv2,pv7,pv79349], .c 13, .c 3, .c 7, .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .c 7, .c 3,
  .c 19, .p pv5 [pv2,pv3,pv11,pv263], .c 3, .p pv3 [pv2,pv17,pv31], .p pv37 [pv2,pv3,pv185153],
  .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv7,pv13,pv109], .p pv2 [pv2,pv3,pv5,pv19,pv1949], .c 3,
  .c 5, .c 71, .c 3, .c 13, .p pv3 [pv2,pv3,pv7,pv2939], .c 3, .c 31, .c 7, .c 3,
  .p pv3 [pv2,pv138869], .c 5, .c 3, .p pv11 [pv2,pv103,pv5393], .c 29, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv7,pv59,pv269], .p pv2 [pv2,pv3,pv92581], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv11,pv31,pv181], .c 3, .p pv5 [pv2,pv555491], .c 5, .c 3, .c 11, .c 7, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv127], .c 3, .c 17, .c 709, .c 3, .p pv5 [pv2,pv13,pv19,pv173], .c 31,
  .c 3, .p pv2 [pv2,pv7,pv39679], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv18517], .c 3, .c 5,
  .c 139, .c 3, .p pv19 [pv2,pv5,pv111103], .c 7, .c 3, .c 109, .c 53, .c 3,
]
private theorem h0135c19 : checkBlock 1110787 128 b0135c19 = true := by
  decide +kernel

private def b0135c20 : List Row := [
  .p pv2 [pv2,pv555521], .c 5, .c 3, .p pv3 [pv2,pv29,pv4789], .c 167, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv79,pv293], .c 3, .c 7, .c 19, .c 3, .p pv2 [pv2,pv11,pv50503], .c 17, .c 3,
  .c 37, .c 5, .c 3, .c 71, .p pv7 [pv2,pv3,pv5,pv47,pv197], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv17,pv3631], .c 3, .p pv2 [pv2,pv5,pv111109], .c 149, .c 3, .c 13, .c 11, .c 3,
  .c 7, .c 5, .c 3, .c 439, .c 239, .c 3, .c 5, .c 7, .c 3, .c 11, .c 13, .c 3, .c 47, .c 113,
  .c 3, .c 31, .c 5, .c 3, .c 19, .c 41, .c 3, .c 5, .c 37, .c 3, .p pv13 [pv2,pv5,pv71,pv313],
  .c 23, .c 3, .p pv2 [pv2,pv277789], .c 7, .c 3, .c 43, .c 5, .c 3, .p pv3 [pv2,pv8681], .c 17,
  .c 3, .c 5, .c 19, .c 3, .p pv13 [pv2,pv5,pv7,pv7937], .p pv3 [pv2,pv3,pv41,pv4517], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv13,pv17,pv419], .c 3, .c 29, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 137,
  .c 3, .p pv2 [pv2,pv5,pv111121], .p pv2 [pv2,pv3,pv10289], .c 3, .c 617,
  .p pv3 [pv2,pv3,pv167,pv1109], .c 3, .c 41, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 61, .c 3,
  .c 683, .c 7, .c 3, .p pv5 [pv2,pv157,pv3539], .c 43, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv37,pv15017], .c 1013, .c 3, .c 5, .c 103, .c 3, .c 7, .c 17, .c 3, .c 197, .c 13,
  .c 3, .p pv2 [pv2,pv593,pv937], .c 5, .c 3, .p pv3 [pv2,pv31,pv4481], .c 19, .c 3, .c 5, .c 11,
]
private theorem h0135c20 : checkBlock 1111043 128 b0135c20 = true := by
  decide +kernel

private def b0135c21 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv11113], .c 101, .c 3, .c 17, .c 29, .c 3, .c 7, .c 5, .c 3, .c 11,
  .c 941, .c 3, .c 5, .c 7, .c 3, .c 13, .p pv5 [pv2,pv3,pv37,pv2503], .c 3, .c 23,
  .p pv2 [pv2,pv3,pv29,pv2129], .c 3, .c 89, .c 5, .c 3, .c 293, .p pv31 [pv2,pv3,pv5,pv31,pv239],
  .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv23,pv151], .c 11, .c 3, .c 19, .c 7, .c 3, .c 389,
  .c 5, .c 3, .p pv2 [pv2,pv43,pv12923], .c 31, .c 3, .c 5, .c 41, .c 3, .c 149,
  .p pv7 [pv2,pv3,pv17,pv227], .c 3, .c 7, .p pv3 [pv2,pv3,pv185233], .c 3, .c 157, .c 5, .c 3,
  .c 13, .c 7, .c 3, .c 5, .c 607, .c 3, .c 43, .p pv3 [pv2,pv3,pv13,pv14249], .c 3,
  .p pv2 [pv2,pv17,pv97,pv337], .c 11, .c 3, .p pv3 [pv2,pv7,pv89,pv223], .c 5, .c 3, .c 7,
  .c 347, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv8821], .c 3, .c 11, .c 7, .c 3,
  .p pv3 [pv2,pv47,pv739], .c 853, .c 3, .c 53, .c 5, .c 3, .c 41, .c 461, .c 3, .c 5, .c 17,
  .c 3, .c 7, .c 29, .c 3, .c 13, .p pv23 [pv2,pv3,pv7,pv827], .c 3, .p pv2 [pv2,pv241,pv1153],
  .c 5, .c 3, .p pv2 [pv2,pv23,pv73,pv331], .c 59, .c 3, .c 5, .c 43, .c 3, .c 17, .c 13, .c 3,
  .c 11, .c 19, .c 3, .c 7, .c 5, .c 3, .c 857, .p pv2 [pv2,pv3,pv5,pv7,pv67,pv79], .c 3, .c 5,
  .c 7, .c 3, .c 29, .p pv3 [pv2,pv3,pv61,pv3037], .c 3, .p pv2 [pv2,pv647,pv859], .c 431, .c 3,
  .p pv3 [pv2,pv13,pv167],
]
private theorem h0135c21 : checkBlock 1111299 128 b0135c21 = true := by
  decide +kernel

private def b0135c22 : List Row := [
  .c 5, .c 3, .p pv7 [pv2,pv7,pv79397], .c 11, .c 3, .c 5, .c 23, .c 3, .c 73,
  .p pv5 [pv2,pv3,pv7,pv11,pv401], .c 3, .p pv7 [pv2,pv19,pv71,pv103], .c 7, .c 3, .c 11, .c 5,
  .c 3, .c 239, .c 13, .c 3, .c 5, .c 47, .c 3, .c 277, .c 61, .c 3, .c 7, .c 79, .c 3, .c 17,
  .c 5, .c 3, .c 59, .c 7, .c 3, .c 5, .c 11, .c 3, .c 127, .c 19, .c 3,
  .p pv2 [pv2,pv23,pv43,pv281], .p pv3 [pv2,pv3,pv11,pv16843], .c 3, .c 13, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv7411], .c 3, .c 5, .c 29, .c 3, .p pv3 [pv2,pv5,pv11,pv31,pv163], .c 7,
  .c 3, .p pv2 [pv2,pv131,pv4243], .c 13, .c 3, .p pv3 [pv2,pv138959], .c 5, .c 3, .c 43, .c 17,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv29,pv6389], .c 3, .c 7, .c 11, .c 3, .c 883, .c 89, .c 3,
  .p pv5 [pv2,pv37,pv83,pv181], .c 5, .c 3, .c 19, .p pv3 [pv2,pv3,pv5,pv37057], .c 3, .c 5,
  .c 73, .c 3, .c 13, .p pv3 [pv2,pv3,pv31,pv43,pv139], .c 3, .p pv5 [pv2,pv7,pv11,pv7219],
  .c 1019, .c 3, .c 7, .c 5, .c 3, .c 37, .p pv19 [pv2,pv3,pv5,pv7,pv2647], .c 3, .c 5, .c 7,
  .c 3, .c 23, .c 31, .c 3, .p pv2 [pv2,pv41,pv6779], .c 11, .c 3, .c 337, .c 5, .c 3, .c 179,
  .p pv2 [pv2,pv3,pv5,pv11,pv1123], .c 3, .c 5, .c 269, .c 3, .c 11, .c 17, .c 3,
  .p pv2 [pv2,pv13,pv61,pv701], .c 7, .c 3, .p pv3 [pv2,pv11,pv6317], .c 5, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv5,pv17,pv109], .c 3, .c 5, .c 113, .c 3,
]
private theorem h0135c22 : checkBlock 1111555 128 b0135c22 = true := by
  decide +kernel

private def b0135c23 : List Row := [
  .c 191, .c 37, .c 3, .c 7, .c 691, .c 3, .c 19, .c 5, .c 3, .c 331, .c 7, .c 3, .c 5, .c 107,
  .c 3, .p pv3 [pv2,pv5,pv6949], .c 23, .c 3, .c 11, .c 383, .c 3, .p pv2 [pv2,pv7,pv39709], .c 5,
  .c 3, .c 7, .c 19, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv23,pv1151], .c 3, .c 173, .c 7, .c 3,
  .c 13, .c 41, .c 3, .c 181, .c 5, .c 3, .c 23, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv15443],
  .c 3, .c 7, .c 13, .c 3, .c 283, .c 101, .c 3, .c 11, .c 5, .c 3, .c 17,
  .p pv7 [pv2,pv3,pv5,pv41,pv113], .c 3, .c 5, .c 467, .c 3, .c 71, .p pv2 [pv2,pv3,pv67,pv461],
  .c 3, .c 19, .c 31, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv179,pv1553], .c 83, .c 3, .c 5, .c 7,
  .c 3, .c 37, .p pv2 [pv2,pv3,pv185327], .c 3, .p pv5 [pv2,pv89,pv6247], .c 61, .c 3, .c 47,
  .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 17, .c 3, .p pv11 [pv2,pv5,pv11,pv919], .c 53, .c 3,
  .c 397, .c 7, .c 3, .p pv2 [pv2,pv41,pv71,pv191], .c 5, .c 3, .c 73,
  .p pv2 [pv2,pv3,pv5,pv101,pv367], .c 3, .c 5, .p pv5 [pv2,pv3,pv23167], .c 3, .c 17, .c 11,
  .c 3, .c 7, .c 137, .c 3, .c 13, .c 5, .c 3, .c 257, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv13,pv53,pv269], .c 3, .c 19, .c 167, .c 3, .p pv3 [pv2,pv11,pv12637], .c 13,
  .c 3, .c 29, .c 5,
]
private theorem h0135c23 : checkBlock 1111811 128 b0135c23 = true := by
  decide +kernel

private def b0135c24 : List Row := [
  .c 3, .c 7, .c 409, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv1471], .c 3, .p pv7 [pv2,pv5,pv13901],
  .c 7, .c 3, .p pv5 [pv2,pv556043], .c 11, .c 3, .p pv2 [pv2,pv29,pv9587], .c 5, .c 3, .c 53,
  .c 223, .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv10903], .c 3, .c 7, .p pv11 [pv2,pv3,pv7723], .c 3,
  .c 83, .c 23, .c 3, .c 17, .c 5, .c 3, .p pv3 [pv2,pv17377], .p pv13 [pv2,pv3,pv5,pv1373], .c 3,
  .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv17,pv3271], .p pv7 [pv2,pv3,pv23,pv8059], .c 3,
  .p pv2 [pv2,pv7,pv19,pv37,pv113], .c 163, .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv107,pv5197],
  .c 47, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv111217], .c 449, .c 3, .c 11, .c 29, .c 3,
  .c 37, .c 5, .c 3, .c 13, .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv92683], .c 3,
  .p pv7 [pv2,pv5,pv67,pv83], .c 19, .c 3, .c 41, .c 7, .c 3, .c 61, .c 5, .c 3, .c 937, .c 11,
  .c 3, .c 5, .c 263, .c 3, .c 751, .c 89, .c 3, .c 7, .p pv3 [pv2,pv3,pv43,pv479], .c 3, .c 11,
  .c 5, .c 3, .c 31, .c 7, .c 3, .c 5, .c 23, .c 3, .c 307, .c 349, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv59,pv1571], .c 3, .p pv3 [pv2,pv7,pv9931], .c 5, .c 3, .c 7, .c 43, .c 3,
  .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv111229], .c 7, .c 3, .c 103, .c 97, .c 3, .c 23, .c 5,
  .c 3, .c 11, .c 31, .c 3, .c 5, .c 19, .c 3, .c 7,
]
private theorem h0135c24 : checkBlock 1112067 128 b0135c24 = true := by
  decide +kernel

private def b0135c25 : List Row := [
  .p pv2 [pv2,pv3,pv89,pv2083], .c 3, .c 17, .c 557, .c 3, .p pv2 [pv2,pv13,pv21391], .c 5, .c 3,
  .p pv2 [pv2,pv457,pv1217], .p pv11 [pv2,pv3,pv5,pv18539], .c 3, .c 5, .c 773, .c 3,
  .p pv7 [pv2,pv5,pv22247], .c 11, .c 3, .c 71, .p pv3 [pv2,pv3,pv13,pv1097], .c 3, .c 7, .c 5,
  .c 3, .p pv3 [pv2,pv37,pv1879], .c 13, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv55619],
  .p pv5 [pv2,pv3,pv29,pv2131], .c 3, .c 167, .p pv2 [pv2,pv3,pv92699], .c 3, .c 19, .c 5, .c 3,
  .c 79, .c 67, .c 3, .c 5, .c 863, .c 3, .c 29, .p pv2 [pv2,pv3,pv7,pv17,pv19,pv41], .c 3, .c 53,
  .c 7, .c 3, .c 13, .c 5, .c 3, .c 17, .c 19, .c 3, .c 5, .c 337, .c 3, .c 11, .c 47, .c 3, .c 7,
  .c 13, .c 3, .c 41, .c 5, .c 3, .c 197, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv31,pv5981], .c 3,
  .p pv47 [pv2,pv5,pv53,pv2099], .c 283, .c 3, .p pv2 [pv2,pv278119], .c 37, .c 3,
  .p pv2 [pv2,pv7,pv229,pv347], .c 5, .c 3, .c 7, .c 331, .c 3, .c 5, .c 17, .c 3, .c 13, .c 7,
  .c 3, .c 11, .p pv2 [pv2,pv3,pv10301], .c 3, .p pv3 [pv2,pv17383], .c 5, .c 3,
  .p pv7 [pv2,pv11,pv61,pv829], .c 293, .c 3, .c 5, .c 13, .c 3, .c 7, .c 23, .c 3, .c 47, .c 43,
  .c 3, .p pv5 [pv2,pv556271], .c 5, .c 3, .p pv2 [pv2,pv17,pv16361], .c 11, .c 3, .c 5, .c 79,
  .c 3, .p pv11 [pv2,pv5,pv13907], .c 59, .c 3, .p pv11 [pv2,pv7,pv13,pv6113],
  .p pv41 [pv2,pv3,pv151,pv307], .c 3, .c 7, .c 5, .c 3,
]
private theorem h0135c25 : checkBlock 1112323 128 b0135c25 = true := by
  decide +kernel

private def b0135c26 : List Row := [
  .c 13, .p pv59 [pv2,pv3,pv5,pv7,pv883], .c 3, .c 5, .c 7, .c 3,
  .p pv23 [pv2,pv5,pv31,pv37,pv97], .c 73, .c 3, .p pv2 [pv2,pv278149], .c 17, .c 3, .c 211, .c 5,
  .c 3, .c 199, .p pv11 [pv2,pv3,pv5,pv37087], .c 3, .c 5, .c 11, .c 3, .c 19,
  .p pv3 [pv2,pv3,pv7,pv59,pv449], .c 3, .c 37, .c 7, .c 3, .c 17, .c 5, .c 3, .c 11, .c 71, .c 3,
  .c 5, .c 127, .c 3, .p pv2 [pv2,pv5,pv7,pv11,pv17], .p pv2 [pv2,pv3,pv31,pv997], .c 3, .c 7,
  .c 19, .c 3, .p pv5 [pv2,pv556331], .c 5, .c 3, .c 67, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv92723], .c 3, .c 59, .c 11, .c 3, .c 97, .p pv13 [pv2,pv3,pv7727], .c 3,
  .c 107, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv8831], .c 3, .c 43, .c 7,
  .c 3, .c 23, .c 151, .c 3, .p pv2 [pv2,pv13,pv42797], .c 5, .c 3, .p pv3 [pv2,pv139091],
  .p pv7 [pv2,pv3,pv5,pv29,pv1279], .c 3, .c 5, .p pv5 [pv2,pv3,pv67,pv173], .c 3, .c 7, .c 769,
  .c 3, .p pv2 [pv2,pv556373], .c 11, .c 3, .c 263, .c 5, .c 3, .c 29, .c 13, .c 3, .c 5, .c 89,
  .c 3, .c 11, .c 19, .c 3, .p pv3 [pv2,pv7,pv31,pv641], .p pv13 [pv2,pv3,pv6869], .c 3, .c 7,
  .c 5, .c 3, .p pv2 [pv2,pv29,pv53,pv181], .c 397, .c 3, .c 5, .c 7, .c 3, .c 163, .c 17, .c 3,
  .c 31, .c 23, .c 3, .c 13, .c 5, .c 3, .c 47, .p pv7 [pv2,pv3,pv5,pv17,pv1091], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv13,pv1297], .c 3, .p pv11 [pv2,pv5,pv19,pv5857],
  .p pv11 [pv2,pv3,pv7,pv23],
]
private theorem h0135c26 : checkBlock 1112579 128 b0135c26 = true := by
  decide +kernel

private def b0135c27 : List Row := [
  .c 3, .c 11, .c 7, .c 3, .c 179, .c 5, .c 3, .c 19, .c 137, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv89,pv521], .c 3, .c 467, .c 41, .c 3, .c 7, .c 31, .c 3, .c 79, .c 5, .c 3,
  .c 571, .c 7, .c 3, .c 5, .c 19, .c 3, .c 13, .c 991, .c 3, .p pv3 [pv2,pv17389],
  .p pv3 [pv2,pv3,pv185483], .c 3, .c 11, .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv37097], .c 3,
  .c 5, .c 13, .c 3, .p pv7 [pv2,pv5,pv27823], .c 7, .c 3, .c 1009, .c 389, .c 3, .c 29, .c 5,
  .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv229], .c 3, .c 5, .c 11, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv79,pv587], .c 3, .c 191, .p pv3 [pv2,pv3,pv7,pv11,pv73], .c 3, .c 19, .c 5,
  .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv23,pv1613], .c 3, .c 5, .p pv5 [pv2,pv3,pv59,pv131], .c 3,
  .c 227, .p pv3 [pv2,pv3,pv13,pv19,pv751], .c 3, .c 317, .c 1049, .c 3, .c 7, .c 5, .c 3, .c 109,
  .c 19, .c 3, .c 5, .c 7, .c 3, .p pv11 [pv2,pv5,pv111301], .c 11, .c 3, .c 967,
  .p pv17 [pv2,pv3,pv103,pv1801], .c 3, .c 239, .c 5, .c 3, .p pv3 [pv2,pv7,pv127,pv313], .c 73,
  .c 3, .c 5, .c 727, .c 3, .c 17, .p pv3 [pv2,pv3,pv7,pv26501], .c 3, .c 13, .c 7, .c 3, .c 53,
  .c 5, .c 3, .p pv2 [pv2,pv17,pv19,pv1723], .c 593, .c 3, .c 5, .c 61, .c 3, .c 37, .c 13, .c 3,
  .c 7, .c 11, .c 3, .p pv2 [pv2,pv173,pv3217], .c 5, .c 3, .p pv3 [pv2,pv1087],
]
private theorem h0135c27 : checkBlock 1112835 128 b0135c27 = true := by
  decide +kernel

private def b0135c28 : List Row := [
  .c 7, .c 3, .c 5, .c 491, .c 3, .c 11, .p pv5 [pv2,pv3,pv6871], .c 3, .c 29, .c 17, .c 3, .c 83,
  .c 5, .c 3, .c 7, .c 101, .c 3, .c 5, .c 163, .c 3, .c 23, .c 7, .c 3, .p pv3 [pv2,pv29,pv2399],
  .c 503, .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv31,pv47,pv191], .c 13, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv937], .c 3, .c 7, .c 113, .c 3, .c 11, .c 229, .c 3,
  .p pv2 [pv2,pv19,pv97,pv151], .c 5, .c 3, .c 31, .p pv2 [pv2,pv3,pv5,pv18553], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv185531], .c 3, .c 19, .p pv47 [pv2,pv3,pv15461], .c 3,
  .p pv3 [pv2,pv7,pv83,pv479], .p pv3 [pv2,pv3,pv185533], .c 3, .c 7, .c 5, .c 3, .c 71, .c 11,
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv55661], .c 23, .c 3, .c 43, .c 13, .c 3, .c 11, .c 5,
  .c 3, .p pv7 [pv2,pv7,pv131,pv607], .c 31, .c 3, .c 5, .c 197, .c 3, .c 139,
  .p pv5 [pv2,pv3,pv7,pv29,pv457], .c 3, .p pv3 [pv2,pv37,pv3761], .c 7, .c 3, .c 277, .c 5, .c 3,
  .c 23, .c 59, .c 3, .c 5, .c 11, .c 3, .c 13, .c 419, .c 3, .c 7, .c 47, .c 3, .c 37, .c 5,
  .c 3, .c 11, .c 7, .c 3, .c 5, .c 13, .c 3, .c 61, .c 17, .c 3, .p pv2 [pv2,pv278329],
  .p pv3 [pv2,pv3,pv53,pv389], .c 3, .c 73, .c 5, .c 3, .c 7, .c 181, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv47], .c 3, .c 313, .c 7, .c 3,
]
private theorem h0135c28 : checkBlock 1113091 128 b0135c28 = true := by
  decide +kernel

private def b0135c29 : List Row := [
  .c 17, .p pv7 [pv2,pv3,pv92779], .c 3, .c 839, .c 5, .c 3, .c 13, .c 23, .c 3, .c 5, .c 37,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv13,pv61], .c 3, .c 521, .p pv3 [pv2,pv3,pv7,pv541], .c 3, .c 47,
  .c 5, .c 3, .c 59, .c 269, .c 3, .c 5, .c 29, .c 3, .p pv3 [pv2,pv5,pv19,pv293],
  .p pv3 [pv2,pv3,pv185567], .c 3, .c 23, .c 11, .c 3, .c 7, .c 5, .c 3, .c 19,
  .p pv17 [pv2,pv3,pv5,pv7,pv11,pv241], .c 3, .c 5, .c 7, .c 3, .c 11, .c 61, .c 3, .c 13, .c 223,
  .c 3, .c 557, .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv13,pv571], .c 3, .c 5, .c 19, .c 3,
  .p pv7 [pv2,pv5,pv55673], .c 13, .c 3, .c 523, .c 7, .c 3, .c 67, .c 5, .c 3, .c 89,
  .p pv11 [pv2,pv3,pv5,pv1031], .c 3, .c 5, .c 647, .c 3, .p pv7 [pv2,pv5,pv7,pv15907], .c 71,
  .c 3, .c 7, .c 23, .c 3, .c 811, .c 5, .c 3, .p pv2 [pv2,pv11,pv25307], .c 7, .c 3, .c 5, .c 17,
  .c 3, .p pv3 [pv2,pv5,pv31,pv449], .c 347, .c 3, .p pv5 [pv2,pv556763], .c 139, .c 3, .c 19,
  .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 757, .c 3, .c 17, .c 7, .c 3, .p pv2 [pv2,pv167,pv1667],
  .c 179, .c 3, .c 11, .c 5, .c 3, .p pv11 [pv2,pv17,pv23,pv89], .c 19, .c 3, .c 5, .c 401, .c 3,
  .c 7, .c 53, .c 3, .p pv2 [pv2,pv556793], .c 37, .c 3, .c 13, .c 5, .c 3, .p pv7 [pv2,pv556799],
  .c 41,
]
private theorem h0135c29 : checkBlock 1113347 128 b0135c29 = true := by
  decide +kernel

private def b0135c30 : List Row := [
  .c 3, .c 5, .c 11, .c 3, .c 83, .c 31, .c 3, .p pv3 [pv2,pv7,pv61,pv163], .c 13, .c 3, .c 7,
  .c 5, .c 3, .c 11, .c 131, .c 3, .c 5, .c 7, .c 3, .c 197, .p pv2 [pv2,pv3,pv41,pv503], .c 3,
  .c 19, .c 997, .c 3, .c 17, .c 5, .c 3, .c 349, .c 241, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv19,pv9769], .c 3, .c 13, .c 11, .c 3, .c 61, .c 7, .c 3, .c 23, .c 5, .c 3,
  .c 53, .c 311, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv7,pv37,pv43],
  .p pv3 [pv2,pv3,pv419,pv443], .c 3, .c 7, .c 457, .c 3, .p pv5 [pv2,pv47,pv1481], .c 5, .c 3,
  .p pv23 [pv2,pv556859], .c 7, .c 3, .c 5, .c 101, .c 3, .c 719, .c 751, .c 3, .c 31, .c 11,
  .c 3, .c 43, .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv11], .c 3, .c 5, .c 743, .c 3, .c 11,
  .c 7, .c 3, .c 1019, .c 487, .c 3, .p pv2 [pv2,pv11,pv17,pv1489], .c 5, .c 3, .c 163,
  .p pv2 [pv2,pv3,pv5,pv19,pv977], .c 3, .c 5, .p pv2 [pv2,pv3,pv43,pv1439], .c 3, .c 7,
  .p pv5 [pv2,pv3,pv5801], .c 3, .p pv2 [pv2,pv307,pv907], .c 19, .c 3, .c 29, .c 5, .c 3,
  .p pv3 [pv2,pv67,pv1039], .c 37, .c 3, .c 5, .c 277, .c 3, .c 23, .c 17, .c 3, .c 11, .c 43,
  .c 3, .c 7, .c 5, .c 3, .c 709, .c 113, .c 3, .c 5, .c 7, .c 3, .c 97, .c 13, .c 3, .c 17,
]
private theorem h0135c30 : checkBlock 1113603 128 b0135c30 = true := by
  decide +kernel

private def b0135c31 : List Row := [
  .p pv2 [pv2,pv3,pv20627], .c 3, .p pv5 [pv2,pv556931], .c 5, .c 3, .c 211, .c 11, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv30941], .c 3, .c 379, .p pv2 [pv2,pv3,pv7,pv11,pv2411], .c 3,
  .p pv5 [pv2,pv556943], .c 7, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv521,pv1069], .c 53, .c 3,
  .c 5, .c 73, .c 3, .c 1021, .c 19, .c 3, .c 7, .c 29, .c 3, .c 31, .c 5, .c 3, .c 41, .c 7,
  .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv55697], .c 83, .c 3, .c 47,
  .p pv2 [pv2,pv3,pv11,pv29,pv97], .c 3, .p pv3 [pv2,pv7,pv4973], .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv9283], .c 3, .c 5, .c 313, .c 3, .p pv2 [pv2,pv5,pv11,pv13,pv19,pv41],
  .c 7, .c 3, .c 29, .c 59, .c 3, .c 13, .c 5, .c 3, .c 19, .p pv23 [pv2,pv3,pv5,pv71,pv523],
  .c 3, .c 5, .p pv7 [pv2,pv3,pv13,pv37,pv193], .c 3, .c 7, .c 11, .c 3, .c 53, .c 13, .c 3,
  .c 89, .c 5, .c 3, .p pv2 [pv2,pv653,pv853], .c 571, .c 3, .c 5, .c 17, .c 3,
  .p pv7 [pv2,pv5,pv101,pv1103], .c 37, .c 3, .p pv5 [pv2,pv7,pv11,pv3617],
  .p pv17 [pv2,pv3,pv59,pv1049], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv13,pv103], .c 23, .c 3,
  .c 5, .c 7, .c 3, .c 13, .p pv3 [pv2,pv3,pv185677], .c 3, .c 113, .c 11, .c 3, .c 149, .c 5,
  .c 3, .c 491, .c 271, .c 3, .c 5, .c 13, .c 3, .c 11, .c 29, .c 3, .c 23, .c 7, .c 3, .c 19,
  .c 5, .c 3, .c 31, .p pv3 [pv2,pv3,pv5,pv12379], .c 3,
]
private theorem h0135c31 : checkBlock 1113859 128 b0135c31 = true := by
  decide +kernel

def rows0135 : List Row :=
  b0135c00 ++ b0135c01 ++ b0135c02 ++ b0135c03 ++ b0135c04 ++ b0135c05 ++ b0135c06 ++ b0135c07 ++
  b0135c08 ++ b0135c09 ++ b0135c10 ++ b0135c11 ++ b0135c12 ++ b0135c13 ++ b0135c14 ++ b0135c15 ++
  b0135c16 ++ b0135c17 ++ b0135c18 ++ b0135c19 ++ b0135c20 ++ b0135c21 ++ b0135c22 ++ b0135c23 ++
  b0135c24 ++ b0135c25 ++ b0135c26 ++ b0135c27 ++ b0135c28 ++ b0135c29 ++ b0135c30 ++ b0135c31

theorem checked0135 : checkBlock 1105923 4096 rows0135 = true :=
  checkBlock_append h0135c00 (
    checkBlock_append h0135c01 (
    checkBlock_append h0135c02 (
    checkBlock_append h0135c03 (
    checkBlock_append h0135c04 (
    checkBlock_append h0135c05 (
    checkBlock_append h0135c06 (
    checkBlock_append h0135c07 (
    checkBlock_append h0135c08 (
    checkBlock_append h0135c09 (
    checkBlock_append h0135c10 (
    checkBlock_append h0135c11 (
    checkBlock_append h0135c12 (
    checkBlock_append h0135c13 (
    checkBlock_append h0135c14 (
    checkBlock_append h0135c15 (
    checkBlock_append h0135c16 (
    checkBlock_append h0135c17 (
    checkBlock_append h0135c18 (
    checkBlock_append h0135c19 (
    checkBlock_append h0135c20 (
    checkBlock_append h0135c21 (
    checkBlock_append h0135c22 (
    checkBlock_append h0135c23 (
    checkBlock_append h0135c24 (
    checkBlock_append h0135c25 (
    checkBlock_append h0135c26 (
    checkBlock_append h0135c27 (
    checkBlock_append h0135c28 (
    checkBlock_append h0135c29 (
    checkBlock_append h0135c30 (
    h0135c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
