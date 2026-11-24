/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks02/Block0213
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks02/Block0213.checked0213
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table026
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table030
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table031
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table036
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table037
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table045
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table059
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table083
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table084
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table134

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0213c00 : List Row := [
  .c 3, .c 29, .c 19, .c 3, .c 503, .c 83, .c 3, .c 193, .c 5, .c 3, .c 11, .c 487, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv290821], .c 3, .c 17, .c 97, .c 3, .c 233, .c 7, .c 3, .c 953, .c 5, .c 3,
  .c 227, .c 13, .c 3, .c 5, .c 37, .c 3, .c 619, .c 11, .c 3, .c 7, .c 47, .c 3, .c 761, .c 5,
  .c 3, .c 19, .c 7, .c 3, .c 5, .c 23, .c 3, .p pv23 [pv2,pv5,pv13,pv31,pv433],
  .p pv5 [pv2,pv3,pv73,pv83], .c 3, .c 479, .c 17, .c 3, .c 13, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv23,pv281], .c 3, .c 5, .c 19, .c 3, .c 31, .c 7, .c 3, .c 61, .c 11, .c 3,
  .c 17, .c 5, .c 3, .p pv7 [pv2,pv71,pv12289], .c 1321, .c 3, .c 5, .c 463, .c 3, .c 7, .c 1201,
  .c 3, .p pv3 [pv2,pv23,pv2371], .c 113, .c 3, .c 47, .c 5, .c 3, .c 43, .c 179, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv145423], .c 3, .c 13, .c 31, .c 3, .p pv5 [pv2,pv7,pv17807], .c 673, .c 3,
  .c 7, .c 5, .c 3, .c 359, .c 17, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv47,pv79],
  .p pv5 [pv2,pv3,pv19,pv43,pv89], .c 3, .c 11, .c 431, .c 3, .c 569, .c 5, .c 3, .c 103, .c 19,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv12119], .c 3, .p pv2 [pv2,pv5,pv87257],
  .p pv3 [pv2,pv3,pv7,pv37,pv1123], .c 3, .p pv2 [pv2,pv13,pv67121], .c 7, .c 3,
  .p pv3 [pv2,pv17,pv401],
]
private theorem h0213c00 : checkBlock 1744899 128 b0213c00 = true := by
  decide +kernel

private def b0213c01 : List Row := [
  .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 191, .c 3, .c 23, .p pv2 [pv2,pv3,pv11,pv13,pv113],
  .c 3, .c 7, .c 37, .c 3, .c 11, .c 5, .c 3, .c 79, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv145433],
  .c 3, .c 89, .c 17, .c 3, .c 19, .c 229, .c 3, .p pv2 [pv2,pv7,pv157,pv397], .c 5, .c 3, .c 7,
  .c 1223, .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv199,pv877], .c 7, .c 3, .c 13,
  .p pv11 [pv2,pv3,pv11,pv31,pv853], .c 3, .c 137, .c 5, .c 3, .c 11, .c 47, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv72719], .c 3, .c 7, .c 13, .c 3, .c 373, .c 31, .c 3, .c 733, .c 5, .c 3,
  .c 59, .p pv7 [pv2,pv3,pv5,pv101], .c 3, .c 5, .c 257, .c 3, .c 281, .c 11, .c 3,
  .p pv3 [pv2,pv7,pv15583], .c 193, .c 3, .c 7, .c 5, .c 3, .c 23,
  .p pv3 [pv2,pv3,pv5,pv7,pv8311], .c 3, .c 5, .c 7, .c 3, .c 19, .c 337, .c 3, .c 37, .c 41,
  .c 3, .p pv2 [pv2,pv23,pv61,pv311], .c 5, .c 3, .c 17, .c 13, .c 3, .c 5, .c 79, .c 3,
  .p pv17 [pv2,pv5,pv67,pv521], .p pv19 [pv2,pv3,pv7,pv3463], .c 3, .c 73, .c 7, .c 3, .c 331,
  .c 5, .c 3, .c 157, .p pv3 [pv2,pv3,pv5,pv11,pv41,pv43], .c 3, .c 5, .c 277, .c 3, .c 11,
  .c 181, .c 3, .c 7, .p pv2 [pv2,pv3,pv5387], .c 3, .c 13, .c 5, .c 3, .c 1013, .c 7, .c 3, .c 5,
  .c 17, .c 3,
]
private theorem h0213c01 : checkBlock 1745155 128 b0213c01 = true := by
  decide +kernel

private def b0213c02 : List Row := [
  .c 41, .c 43, .c 3, .c 67, .c 13, .c 3, .c 29, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv73,pv797], .c 3, .c 5, .p pv19 [pv2,pv3,pv7,pv11,pv1889], .c 3, .c 17,
  .c 7, .c 3, .c 11, .c 53, .c 3, .p pv2 [pv2,pv29,pv41,pv367], .c 5, .c 3,
  .p pv2 [pv2,pv11,pv13,pv17,pv359], .p pv2 [pv2,pv3,pv5,pv9697], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv421,pv691], .c 3, .c 7, .c 19, .c 3, .c 547, .p pv13 [pv2,pv3,pv7,pv1979],
  .c 3, .c 1031, .c 5, .c 3, .p pv3 [pv2,pv127,pv859], .c 11, .c 3, .c 5, .c 13, .c 3,
  .p pv2 [pv2,pv5,pv3491], .c 73, .c 3, .c 1213, .c 17, .c 3, .c 7, .c 5, .c 3,
  .p pv17 [pv2,pv739,pv1181], .c 1093, .c 3, .c 5, .c 7, .c 3, .c 263, .c 47, .c 3,
  .p pv7 [pv2,pv13,pv1049], .c 23, .c 3, .c 17, .c 5, .c 3, .c 13, .c 67, .c 3, .c 5, .c 11, .c 3,
  .p pv3 [pv2,pv5,pv17,pv151], .c 241, .c 3, .c 163, .c 7, .c 3, .c 83, .c 5, .c 3, .c 11,
  .p pv13 [pv2,pv3,pv5,pv47,pv619], .c 3, .c 5, .c 19, .c 3, .c 929, .p pv5 [pv2,pv3,pv72733],
  .c 3, .c 7, .p pv3 [pv2,pv3,pv107,pv2719], .c 3, .c 211, .c 5, .c 3, .c 397, .c 7, .c 3, .c 5,
  .c 197, .c 3, .p pv2 [pv2,pv5,pv87281], .c 11, .c 3, .c 13, .p pv2 [pv2,pv3,pv17,pv43,pv199],
  .c 3, .c 59, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv89,pv467], .c 3, .c 167,
  .c 7, .c 3, .c 41, .c 1277, .c 3, .c 19, .c 5,
]
private theorem h0213c02 : checkBlock 1745411 128 b0213c02 = true := by
  decide +kernel

private def b0213c03 : List Row := [
  .c 3, .p pv2 [pv2,pv436417], .c 43, .c 3, .c 5, .c 23, .c 3, .c 7, .c 157, .c 3,
  .p pv5 [pv2,pv872843], .c 11, .c 3, .p pv2 [pv2,pv13,pv59,pv569], .c 5, .c 3,
  .p pv2 [pv2,pv41,pv61,pv349], .c 19, .c 3, .c 5, .p pv3 [pv2,pv3,pv131,pv2221], .c 3, .c 11,
  .c 17, .c 3, .p pv3 [pv2,pv7,pv62347], .c 317, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv27277],
  .c 13, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv191,pv457], .c 173, .c 3, .c 17,
  .p pv7 [pv2,pv3,pv71,pv683], .c 3, .p pv3 [pv2,pv67,pv3257], .c 5, .c 3, .c 61,
  .p pv11 [pv2,pv3,pv5,pv3637], .c 3, .c 5, .c 53, .c 3, .c 29, .p pv5 [pv2,pv3,pv7,pv2969], .c 3,
  .c 11, .c 7, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv11,pv3607], .c 137, .c 3, .c 5, .c 827,
  .c 3, .c 257, .p pv3 [pv2,pv3,pv96989], .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv107,pv4079],
  .c 5, .c 3, .c 67, .c 7, .c 3, .c 5, .c 31, .c 3, .p pv19 [pv2,pv5,pv174583], .c 149, .c 3,
  .c 131, .p pv3 [pv2,pv3,pv23,pv4217], .c 3, .c 11, .c 5, .c 3, .c 7,
  .p pv47 [pv2,pv3,pv5,pv103,pv113], .c 3, .c 5, .c 227, .c 3, .c 13, .c 7, .c 3, .c 223, .c 59,
  .c 3, .c 53, .c 5, .c 3, .p pv7 [pv2,pv193,pv4523], .c 61, .c 3, .c 5, .c 11, .c 3, .c 7,
  .c 163, .c 3, .p pv3 [pv2,pv229,pv953], .c 977, .c 3, .c 41, .c 5, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv5,pv19,pv1021], .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv11,pv31],
]
private theorem h0213c03 : checkBlock 1745667 128 b0213c03 = true := by
  decide +kernel

private def b0213c04 : List Row := [
  .p pv5 [pv2,pv3,pv290987], .c 3, .p pv5 [pv2,pv7,pv13,pv53,pv181], .c 19, .c 3, .c 7, .c 5,
  .c 3, .c 13, .c 73, .c 3, .c 5, .c 7, .c 3, .c 17, .c 11, .c 3, .p pv2 [pv2,pv37,pv47,pv251],
  .c 839, .c 3, .c 113, .c 5, .c 3, .p pv47 [pv2,pv7,pv17,pv131], .p pv3 [pv2,pv3,pv5,pv58199],
  .c 3, .c 5, .c 631, .c 3, .c 431, .c 677, .c 3, .c 59, .c 7, .c 3, .c 37, .c 5, .c 3, .c 23,
  .c 499, .c 3, .c 5, .p pv5 [pv2,pv3,pv397,pv733], .c 3, .c 197, .c 31, .c 3, .c 7, .c 11, .c 3,
  .p pv5 [pv2,pv23,pv37957], .c 5, .c 3, .p pv2 [pv2,pv436507], .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv17,pv317], .c 3, .c 11, .c 13, .c 3, .c 349, .c 1103, .c 3, .c 17, .c 5, .c 3,
  .c 7, .c 29, .c 3, .c 5, .c 37, .c 3, .c 83, .c 7, .c 3, .c 1187, .c 269, .c 3, .c 811, .c 5,
  .c 3, .c 173, .c 23, .c 3, .c 5, .c 47, .c 3, .c 7, .c 71, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv7,pv13,pv41], .c 3, .c 467, .c 5, .c 3, .c 19, .c 13, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv97007], .c 3, .c 149, .c 107, .c 3, .c 23, .p pv3 [pv2,pv3,pv17,pv19,pv53],
  .c 3, .c 7, .c 5, .c 3, .c 41, .c 11, .c 3, .c 5, .c 7, .c 3, .c 449, .c 1283, .c 3,
  .p pv5 [pv2,pv873083], .p pv7 [pv2,pv3,pv31,pv2347], .c 3, .c 11, .c 5, .c 3,
]
private theorem h0213c04 : checkBlock 1745923 128 b0213c04 = true := by
  decide +kernel

private def b0213c05 : List Row := [
  .p pv2 [pv2,pv7,pv37,pv3371], .p pv2 [pv2,pv3,pv5,pv89,pv109], .c 3, .c 5, .c 43, .c 3, .c 47,
  .p pv23 [pv2,pv3,pv7,pv5197], .c 3, .c 457, .c 7, .c 3, .p pv2 [pv2,pv137,pv6373], .c 5, .c 3,
  .p pv3 [pv2,pv197,pv277], .p pv2 [pv2,pv3,pv5,pv58207], .c 3, .c 5, .c 11, .c 3, .c 67, .c 17,
  .c 3, .c 7, .c 23, .c 3, .c 19, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 61, .c 3, .c 13, .c 647,
  .c 3, .c 17, .p pv3 [pv2,pv3,pv291043], .c 3, .p pv5 [pv2,pv7,pv103,pv173], .c 5, .c 3, .c 7,
  .c 19, .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv149,pv293], .c 7, .c 3,
  .p pv5 [pv2,pv241,pv3623], .c 37, .c 3, .c 29, .c 5, .c 3, .p pv2 [pv2,pv23,pv37963],
  .p pv2 [pv2,pv3,pv5,pv5821], .c 3, .c 5, .p pv2 [pv2,pv3,pv73,pv443], .c 3, .c 7, .c 41, .c 3,
  .p pv2 [pv2,pv11,pv13,pv43,pv71], .c 167, .c 3, .c 31, .c 5, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv5,pv58211], .c 3, .c 5, .p pv5 [pv2,pv3,pv18191], .c 3, .c 59,
  .p pv3 [pv2,pv3,pv13,pv17,pv439], .c 3, .c 19, .c 11, .c 3, .c 7, .c 5, .c 3, .c 17, .c 131,
  .c 3, .c 5, .c 7, .c 3, .c 11, .c 239, .c 3, .c 127, .c 47, .c 3, .p pv5 [pv2,pv11,pv163,pv487],
  .c 5, .c 3, .p pv2 [pv2,pv7,pv97,pv643], .c 101, .c 3, .c 5, .p pv19 [pv2,pv3,pv139,pv349],
  .c 3, .p pv7 [pv2,pv5,pv37,pv59], .c 53, .c 3, .c 13, .c 7, .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv873209], .p pv11 [pv2,pv3,pv5,pv13,pv2239], .c 3, .c 5, .c 17, .c 3, .c 683,
  .c 13,
]
private theorem h0213c05 : checkBlock 1746179 128 b0213c05 = true := by
  decide +kernel

private def b0213c06 : List Row := [
  .c 3, .c 7, .p pv3 [pv2,pv3,pv29,pv10037], .c 3, .p pv2 [pv2,pv19,pv45959], .c 5, .c 3,
  .p pv3 [pv2,pv11,pv9923], .c 7, .c 3, .c 5, .c 193, .c 3, .c 17, .p pv3 [pv2,pv3,pv291077],
  .c 3, .c 29, .c 181, .c 3, .c 47, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 491, .c 3, .c 61,
  .c 7, .c 3, .p pv3 [pv2,pv29,pv941], .c 19, .c 3, .c 11, .c 5, .c 3, .c 31, .c 13, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv145543], .c 3, .c 7, .c 307, .c 3, .c 241, .c 17, .c 3,
  .p pv2 [pv2,pv79,pv5527], .c 5, .c 3, .p pv2 [pv2,pv227,pv3847],
  .p pv2 [pv2,pv3,pv5,pv31,pv313], .c 3, .c 5, .c 11, .c 3, .c 23, .c 367, .c 3,
  .p pv2 [pv2,pv7,pv19,pv67], .c 41, .c 3, .c 7, .c 5, .c 3, .c 11, .c 31, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv11,pv17,pv467], .c 29, .c 3, .p pv2 [pv2,pv873293], .c 13, .c 3, .c 101, .c 5,
  .c 3, .p pv19 [pv2,pv7,pv73,pv1709], .p pv7 [pv2,pv3,pv5,pv41,pv71], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv291101], .c 3, .c 79, .c 11, .c 3, .c 43, .c 7, .c 3, .c 67, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv33589], .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv59,pv2467], .c 3, .c 13, .c 23,
  .c 3, .c 7, .p pv13 [pv2,pv3,pv17,pv1427], .c 3, .c 167, .c 5, .c 3, .c 37, .c 7, .c 3, .c 5,
  .c 13, .c 3, .c 71, .p pv5 [pv2,pv3,pv36389], .c 3, .p pv2 [pv2,pv283,pv1543], .c 11, .c 3,
  .p pv2 [pv2,pv7,pv17,pv41,pv179], .c 5, .c 3, .c 7,
]
private theorem h0213c06 : checkBlock 1746435 128 b0213c06 = true := by
  decide +kernel

private def b0213c07 : List Row := [
  .c 1091, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv37,pv281], .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv13,pv67181], .c 251, .c 3, .p pv3 [pv2,pv11,pv23,pv863], .c 5, .c 3, .c 13, .c 53,
  .c 3, .c 5, .c 19, .c 3, .c 7, .c 17, .c 3, .p pv3 [pv2,pv109171], .c 733, .c 3,
  .p pv5 [pv2,pv71,pv12301], .c 5, .c 3, .c 443, .p pv3 [pv2,pv3,pv5,pv17,pv137], .c 3, .c 5,
  .c 29, .c 3, .p pv3 [pv2,pv5,pv43669], .p pv2 [pv2,pv3,pv277,pv1051], .c 3, .c 11, .c 79, .c 3,
  .c 7, .c 5, .c 3, .p pv2 [pv2,pv11,pv79399], .c 23, .c 3, .c 5, .c 7, .c 3, .c 983, .c 743,
  .c 3, .c 13, .c 197, .c 3, .c 19, .c 5, .c 3, .c 1087, .c 11, .c 3, .c 5, .c 73, .c 3,
  .p pv3 [pv2,pv5,pv167,pv523], .c 13, .c 3, .c 23, .c 7, .c 3, .c 11, .c 5, .c 3, .c 409, .c 19,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv41,pv263], .c 3, .c 239, .c 313, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv291143], .c 3, .c 383, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 11, .c 3,
  .c 31, .p pv2 [pv2,pv3,pv107,pv907], .c 3, .c 41, .c 541, .c 3, .p pv2 [pv2,pv7,pv89,pv701],
  .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv41593], .c 3,
  .p pv11 [pv2,pv5,pv11,pv15881], .c 7, .c 3, .c 19, .c 23, .c 3, .p pv2 [pv2,pv873461], .c 5,
  .c 3, .p pv3 [pv2,pv41,pv2663], .c 29, .c 3, .c 5, .c 17, .c 3, .c 7, .c 11, .c 3,
]
private theorem h0213c07 : checkBlock 1746691 128 b0213c07 = true := by
  decide +kernel

private def b0213c08 : List Row := [
  .p pv2 [pv2,pv607,pv1439], .p pv11 [pv2,pv3,pv7,pv2971], .c 3, .c 13, .c 5, .c 3, .c 283, .c 43,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv22397], .c 3, .c 17, .p pv5 [pv2,pv3,pv48527], .c 3, .c 281,
  .c 13, .c 3, .c 7, .c 5, .c 3, .c 29, .p pv3 [pv2,pv3,pv5,pv7,pv47,pv59], .c 3, .c 5, .c 7,
  .c 3, .p pv3 [pv2,pv5,pv1747], .p pv2 [pv2,pv3,pv291167], .c 3, .p pv5 [pv2,pv79,pv11057],
  .c 11, .c 3, .p pv2 [pv2,pv19,pv127,pv181], .c 5, .c 3, .c 919, .c 199, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv71,pv1367], .c 3, .c 11, .p pv11 [pv2,pv3,pv7,pv10399], .c 3, .c 47, .c 7,
  .c 3, .p pv7 [pv2,pv11,pv79411], .c 5, .c 3, .c 59, .c 41, .c 3, .c 5, .c 13, .c 3,
  .p pv11 [pv2,pv5,pv7,pv12479], .p pv3 [pv2,pv3,pv32353], .c 3, .c 7, .c 19, .c 3, .c 17, .c 5,
  .c 3, .p pv11 [pv2,pv873539], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv103,pv257], .c 3, .c 139,
  .c 113, .c 3, .c 11, .p pv3 [pv2,pv3,pv31,pv101], .c 3, .c 23, .c 5, .c 3, .c 7, .c 457, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv7,pv2311], .c 3, .p pv7 [pv2,pv5,pv21839], .c 7, .c 3, .c 173, .c 31,
  .c 3, .c 41, .c 5, .c 3, .c 127, .c 11, .c 3, .c 5, .c 131, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv11,pv1103], .c 3, .c 401, .c 67, .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv71,pv769], .p pv2 [pv2,pv3,pv5,pv719], .c 3, .c 5, .c 37, .c 3,
  .p pv2 [pv2,pv5,pv87359], .c 19, .c 3, .c 13, .c 103, .c 3, .c 7, .c 5, .c 3, .c 101,
  .p pv41 [pv2,pv3,pv5,pv7,pv13],
]
private theorem h0213c08 : checkBlock 1746947 128 b0213c08 = true := by
  decide +kernel

private def b0213c09 : List Row := [
  .c 3, .c 5, .c 7, .c 3, .c 251, .c 13, .c 3, .p pv3 [pv2,pv109201], .c 43, .c 3, .c 61, .c 5,
  .c 3, .c 11, .p pv17 [pv2,pv3,pv5,pv139,pv419], .c 3, .c 5, .p pv5 [pv2,pv3,pv145603], .c 3,
  .c 23, .c 17, .c 3, .p pv5 [pv2,pv383,pv2281], .c 7, .c 3, .c 31, .c 5, .c 3, .c 19, .c 97,
  .c 3, .c 5, .c 233, .c 3, .p pv7 [pv2,pv5,pv7,pv109,pv229], .c 11, .c 3, .c 7, .c 29, .c 3,
  .c 599, .c 5, .c 3, .p pv3 [pv2,pv37,pv5903], .c 7, .c 3, .c 5, .c 19, .c 3,
  .p pv3 [pv2,pv5,pv101,pv173], .p pv3 [pv2,pv3,pv291217], .c 3, .p pv2 [pv2,pv11,pv79423],
  .c 557, .c 3, .p pv3 [pv2,pv7,pv15601], .c 5, .c 3, .c 7, .c 167, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv41603], .c 3, .p pv2 [pv2,pv5,pv13,pv13441], .c 7, .c 3, .c 29, .c 11,
  .c 3, .c 13, .c 5, .c 3, .c 331, .c 1249, .c 3, .c 5, .c 53, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv17,pv37,pv463], .c 3, .p pv13 [pv2,pv29,pv47,pv641], .c 13, .c 3, .c 19, .c 5,
  .c 3, .c 17, .c 71, .c 3, .c 5, .p pv2 [pv2,pv3,pv32359], .c 3, .c 43, .c 127, .c 3, .c 509,
  .c 37, .c 3, .c 7, .c 5, .c 3, .c 131, .c 19, .c 3, .c 5, .c 7, .c 3, .c 13, .c 857, .c 3,
  .c 11, .p pv19 [pv2,pv3,pv223,pv653], .c 3, .p pv3 [pv2,pv113,pv1933], .c 5, .c 3, .c 31,
  .p pv13 [pv2,pv3,pv5,pv809], .c 3, .c 5, .c 13, .c 3, .c 827, .c 29, .c 3, .c 883,
]
private theorem h0213c09 : checkBlock 1747203 128 b0213c09 = true := by
  decide +kernel

private def b0213c10 : List Row := [
  .c 7, .c 3, .c 53, .c 5, .c 3, .c 491, .c 11, .c 3, .c 5, .c 43, .c 3, .c 17,
  .p pv5 [pv2,pv3,pv11,pv29,pv83], .c 3, .c 7, .p pv47 [pv2,pv3,pv109,pv167], .c 3, .c 11, .c 5,
  .c 3, .c 13, .c 7, .c 3, .c 5, .c 47, .c 3, .c 29, .p pv7 [pv2,pv3,pv13,pv1867], .c 3, .c 23,
  .p pv7 [pv2,pv3,pv291253], .c 3, .c 71, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv19417], .c 3,
  .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv23,pv29,pv131], .c 7, .c 3, .c 37, .c 17, .c 3, .c 607,
  .c 5, .c 3, .c 11, .c 67, .c 3, .c 5, .c 157, .c 3, .c 7, .p pv2 [pv2,pv3,pv137,pv1063], .c 3,
  .c 13, .p pv2 [pv2,pv3,pv7,pv41609], .c 3, .c 17, .c 5, .c 3, .c 61,
  .p pv3 [pv2,pv3,pv5,pv13,pv4481], .c 3, .c 5, .c 109, .c 3, .c 19, .c 11, .c 3,
  .p pv5 [pv2,pv7,pv43,pv2903], .c 23, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv199,pv4391], .c 37,
  .c 3, .c 5, .c 7, .c 3, .c 107, .p pv7 [pv2,pv3,pv23,pv1583], .c 3, .c 839, .c 19, .c 3,
  .p pv2 [pv2,pv13,pv67217], .c 5, .c 3, .c 43, .c 17, .c 3, .c 5, .c 409, .c 3,
  .p pv2 [pv2,pv5,pv87383], .c 613, .c 3, .c 1223, .c 7, .c 3, .c 227, .c 5, .c 3, .c 271, .c 13,
  .c 3, .c 5, .c 31, .c 3, .c 11, .c 73, .c 3, .c 7, .p pv2 [pv2,pv3,pv59,pv4937], .c 3, .c 353,
  .c 5, .c 3, .c 137, .c 7, .c 3,
]
private theorem h0213c10 : checkBlock 1747459 128 b0213c10 = true := by
  decide +kernel

private def b0213c11 : List Row := [
  .c 5, .c 79, .c 3, .p pv3 [pv2,pv5,pv13,pv3361], .p pv3 [pv2,pv3,pv291287], .c 3,
  .p pv5 [pv2,pv873863], .p pv19 [pv2,pv3,pv53,pv229], .c 3, .c 13, .c 5, .c 3, .c 7, .c 997,
  .c 3, .c 5, .c 23, .c 3, .c 307, .c 7, .c 3, .c 11, .c 13, .c 3, .p pv2 [pv2,pv67,pv13043],
  .c 5, .c 3, .c 37, .c 113, .c 3, .c 5, .c 389, .c 3, .c 7, .p pv3 [pv2,pv3,pv89,pv1091], .c 3,
  .c 17, .c 41, .c 3, .c 23, .c 5, .c 3, .p pv7 [pv2,pv13,pv5171], .c 11, .c 3, .c 5, .c 71, .c 3,
  .c 13, .c 1051, .c 3, .c 199, .c 173, .c 3, .c 7, .c 5, .c 3, .c 19, .c 571, .c 3, .c 5, .c 7,
  .c 3, .c 191, .c 37, .c 3, .p pv5 [pv2,pv137,pv6379], .c 163, .c 3, .c 977, .c 5, .c 3, .c 29,
  .c 877, .c 3, .c 5, .c 11, .c 3, .c 41, .c 31, .c 3, .p pv2 [pv2,pv13,pv33613], .c 7, .c 3,
  .c 47, .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv19421], .c 3, .c 5, .c 83, .c 3, .c 127,
  .p pv3 [pv2,pv3,pv13,pv22409], .c 3, .c 7, .c 821, .c 3, .c 757, .c 5, .c 3, .c 149, .c 7, .c 3,
  .c 5, .c 787, .c 3, .c 23, .c 11, .c 3, .c 769, .p pv2 [pv2,pv3,pv317,pv919], .c 3, .c 19, .c 5,
  .c 3, .c 7, .p pv31 [pv2,pv3,pv5,pv43,pv271], .c 3, .c 5, .c 17, .c 3, .c 617, .c 7, .c 3,
  .c 13, .p pv7 [pv2,pv3,pv569],
]
private theorem h0213c11 : checkBlock 1747715 128 b0213c11 = true := by
  decide +kernel

private def b0213c12 : List Row := [
  .c 3, .c 241, .c 5, .c 3, .p pv2 [pv2,pv873989], .c 19, .c 3, .c 5, .p pv5 [pv2,pv3,pv291331],
  .c 3, .c 7, .c 13, .c 3, .c 31, .c 11, .c 3, .p pv2 [pv2,pv874001], .c 5, .c 3,
  .p pv11 [pv2,pv17,pv12853], .c 331, .c 3, .c 5, .c 761, .c 3, .c 11, .c 23, .c 3,
  .p pv2 [pv2,pv7,pv17837], .p pv2 [pv2,pv3,pv31,pv37,pv127], .c 3, .c 7, .c 5, .c 3,
  .p pv13 [pv2,pv19,pv157,pv293], .p pv19 [pv2,pv3,pv5,pv7,pv2081], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv34961], .p pv2 [pv2,pv3,pv59,pv823], .c 3, .c 19, .c 17, .c 3, .c 83, .c 5,
  .c 3, .c 23, .c 13, .c 3, .c 5, .c 61, .c 3, .c 653, .p pv2 [pv2,pv3,pv7,pv41621], .c 3, .c 11,
  .c 7, .c 3, .c 17, .c 5, .c 3, .c 53, .c 281, .c 3, .c 5, .p pv2 [pv2,pv3,pv97117], .c 3, .c 59,
  .p pv17 [pv2,pv3,pv79,pv461], .c 3, .c 7, .p pv3 [pv2,pv3,pv47,pv6199], .c 3, .c 13, .c 5, .c 3,
  .p pv3 [pv2,pv54629], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv431], .c 3, .c 349,
  .p pv3 [pv2,pv3,pv11,pv109], .c 3, .c 277, .c 13, .c 3, .c 11, .c 5, .c 3, .c 7, .c 17, .c 3,
  .c 5, .p pv11 [pv2,pv3,pv7,pv107,pv389], .c 3, .c 19, .c 7, .c 3, .p pv3 [pv2,pv37,pv2953],
  .p pv23 [pv2,pv3,pv17,pv29,pv197], .c 3, .c 31, .c 5, .c 3, .p pv2 [pv2,pv13,pv33619], .c 79,
  .c 3, .c 5, .c 11, .c 3, .c 7, .c 139, .c 3, .c 23, .c 19, .c 3, .c 37, .c 5, .c 3, .c 11,
  .c 271, .c 3, .c 5,
]
private theorem h0213c12 : checkBlock 1747971 128 b0213c12 = true := by
  decide +kernel

private def b0213c13 : List Row := [
  .c 13, .c 3, .c 67, .c 71, .c 3, .p pv2 [pv2,pv7,pv29,pv2153], .p pv3 [pv2,pv3,pv291373], .c 3,
  .c 7, .c 5, .c 3, .c 809, .c 43, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv61,pv1433], .c 11,
  .c 3, .p pv2 [pv2,pv13,pv19,pv3539], .p pv7 [pv2,pv3,pv48563], .c 3, .c 107, .c 5, .c 3, .c 13,
  .c 41, .c 3, .c 5, .c 37, .c 3, .p pv2 [pv2,pv5,pv174829], .c 179, .c 3, .c 17, .c 7, .c 3,
  .c 1171, .c 5, .c 3, .c 601, .c 53, .c 3, .c 5, .c 643, .c 3, .c 61, .c 19, .c 3, .c 7, .c 11,
  .c 3, .p pv2 [pv2,pv437083], .c 5, .c 3, .p pv13 [pv2,pv31,pv163,pv173], .c 7, .c 3, .c 5,
  .c 59, .c 3, .c 11, .c 47, .c 3, .c 13, .p pv3 [pv2,pv3,pv32377], .c 3, .c 41, .c 5, .c 3, .c 7,
  .c 257, .c 3, .c 5, .p pv59 [pv2,pv3,pv7,pv3469], .c 3, .c 29, .c 7, .c 3, .c 193, .c 523, .c 3,
  .c 1279, .c 5, .c 3, .c 17, .p pv11 [pv2,pv3,pv5,pv31,pv47], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv59,pv449], .c 3, .c 7, .c 421, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv7,pv19,pv313], .c 3, .c 43, .c 5, .c 3, .c 151, .c 31, .c 3, .c 5, .c 19,
  .c 3, .p pv11 [pv2,pv5,pv43711], .c 61, .c 3, .c 47, .c 113, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv874229], .c 11, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv53,pv3299],
  .p pv5 [pv2,pv3,pv11,pv37,pv179], .c 3, .p pv2 [pv2,pv521,pv839], .p pv3 [pv2,pv3,pv83,pv3511],
  .c 3,
]
private theorem h0213c13 : checkBlock 1748227 128 b0213c13 = true := by
  decide +kernel

private def b0213c14 : List Row := [
  .c 11, .c 5, .c 3, .p pv3 [pv2,pv7,pv31223], .p pv3 [pv2,pv3,pv5,pv167,pv349], .c 3, .c 5,
  .c 29, .c 3, .c 17, .p pv3 [pv2,pv3,pv7,pv13877], .c 3, .c 79, .c 7, .c 3, .c 13, .c 5, .c 3,
  .p pv11 [pv2,pv17,pv51427], .c 443, .c 3, .c 5, .c 11, .c 3, .c 137, .c 347, .c 3, .c 7, .c 13,
  .c 3, .c 223, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 211, .c 3, .c 83,
  .p pv2 [pv2,pv3,pv113,pv2579], .c 3, .c 431, .c 17, .c 3, .c 461, .c 5, .c 3, .c 7, .c 227,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv17,pv31,pv79], .c 3, .c 13, .c 7, .c 3, .c 1009,
  .p pv3 [pv2,pv3,pv23,pv12671], .c 3, .c 17, .c 5, .c 3, .c 41, .p pv3 [pv2,pv3,pv5,pv19429],
  .c 3, .c 5, .c 13, .c 3, .c 7, .p pv3 [pv2,pv3,pv291437], .c 3, .c 19, .c 53, .c 3, .c 67, .c 5,
  .c 3, .p pv7 [pv2,pv43,pv20333], .c 181, .c 3, .c 5, .p pv5 [pv2,pv3,pv19,pv5113], .c 3, .c 179,
  .p pv2 [pv2,pv3,pv145721], .c 3, .c 37, .c 11, .c 3, .c 7, .c 5, .c 3, .c 13, .c 17, .c 3, .c 5,
  .c 7, .c 3, .c 11, .c 1049, .c 3, .c 61, .c 359, .c 3, .c 337, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv124907], .c 59, .c 3, .c 5, .p pv3 [pv2,pv3,pv379,pv769], .c 3,
  .p pv17 [pv2,pv5,pv31,pv5641], .c 23, .c 3, .c 251, .c 7, .c 3, .p pv2 [pv2,pv17,pv19,pv2707],
  .c 5, .c 3, .c 29, .c 37, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv23],
]
private theorem h0213c14 : checkBlock 1748483 128 b0213c14 = true := by
  decide +kernel

private def b0213c15 : List Row := [
  .c 3, .c 19, .p pv3 [pv2,pv3,pv291457], .c 3, .c 7, .p pv2 [pv2,pv3,pv61,pv2389], .c 3, .c 311,
  .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 43, .c 3, .c 971, .c 13, .c 3, .p pv3 [pv2,pv47,pv4651],
  .c 19, .c 3, .p pv5 [pv2,pv7,pv23,pv5431], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv109,pv191], .c 3, .c 71, .c 7, .c 3, .c 17, .c 61, .c 3, .c 11, .c 5,
  .c 3, .c 59, .c 1129, .c 3, .c 5, .c 163, .c 3, .c 7, .p pv13 [pv2,pv3,pv18217], .c 3, .c 103,
  .c 349, .c 3, .p pv2 [pv2,pv37,pv23633], .c 5, .c 3, .p pv3 [pv2,pv109303], .c 13, .c 3, .c 5,
  .c 11, .c 3, .c 73, .p pv3 [pv2,pv3,pv97159], .c 3, .c 1229, .c 1033, .c 3, .c 7, .c 5, .c 3,
  .c 11, .p pv11 [pv2,pv3,pv5,pv7,pv347], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv11,pv13,pv1223], .c 19, .c 3, .c 23, .p pv2 [pv2,pv3,pv139,pv233], .c 3,
  .c 13, .c 5, .c 3, .c 17, .p pv3 [pv2,pv3,pv5,pv97,pv601], .c 3, .c 5, .c 47, .c 3, .c 691,
  .c 11, .c 3, .c 31, .c 7, .c 3, .p pv2 [pv2,pv29,pv15077], .c 5, .c 3, .c 43,
  .p pv2 [pv2,pv3,pv5,pv103,pv283], .c 3, .c 5, .c 53, .c 3, .p pv7 [pv2,pv5,pv7,pv19,pv263],
  .c 37, .c 3, .c 7, .p pv3 [pv2,pv3,pv31,pv9403], .c 3, .p pv2 [pv2,pv149,pv5869], .c 5, .c 3,
  .c 19, .c 7, .c 3, .c 5, .c 17, .c 3, .c 13, .c 1087, .c 3, .c 191, .c 11, .c 3,
  .p pv3 [pv2,pv7,pv61],
]
private theorem h0213c15 : checkBlock 1748739 128 b0213c15 = true := by
  decide +kernel

private def b0213c16 : List Row := [
  .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv11,pv53], .c 3, .c 5, .c 13, .c 3, .c 11, .c 7, .c 3,
  .c 101, .c 29, .c 3, .p pv5 [pv2,pv11,pv107,pv743], .c 5, .c 3, .p pv2 [pv2,pv17,pv89],
  .p pv11 [pv2,pv3,pv5,pv173,pv337], .c 3, .c 5, .c 139, .c 3, .c 7, .c 103, .c 3,
  .p pv5 [pv2,pv13,pv67271], .p pv41 [pv2,pv3,pv7,pv29,pv359], .c 3, .c 53, .c 5, .c 3, .c 13,
  .c 1181, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv26501], .c 3, .p pv7 [pv2,pv5,pv174907],
  .p pv11 [pv2,pv3,pv13,pv2803], .c 3, .c 11, .c 17, .c 3, .c 7, .c 5, .c 3,
  .p pv7 [pv2,pv11,pv4969], .p pv2 [pv2,pv3,pv5,pv7,pv8329], .c 3, .c 5, .c 7, .c 3, .c 37,
  .c 709, .c 3, .p pv2 [pv2,pv29,pv53,pv569], .c 947, .c 3, .c 17, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv101,pv1237], .c 11, .c 3, .c 5, .c 23, .c 3, .c 233,
  .p pv2 [pv2,pv3,pv7,pv11,pv631], .c 3, .c 13, .c 7, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv437287], .p pv19 [pv2,pv3,pv5,pv13,pv23], .c 3, .c 5,
  .p pv23 [pv2,pv3,pv71,pv2053], .c 3, .c 383, .c 13, .c 3, .c 7, .c 67, .c 3, .c 23, .c 5, .c 3,
  .p pv11 [pv2,pv19,pv191,pv241], .c 7, .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv211,pv829],
  .c 29, .c 3, .c 19, .c 47, .c 3, .c 173, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv199,pv293],
  .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv19,pv137], .c 3, .p pv2 [pv2,pv5,pv11,pv7951], .c 7, .c 3,
  .c 71, .p pv2 [pv2,pv3,pv13,pv11213], .c 3, .p pv3 [pv2,pv17,pv59,pv109], .c 5, .c 3,
  .p pv7 [pv2,pv874619], .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv47,pv6203], .c 3,
]
private theorem h0213c16 : checkBlock 1748995 128 b0213c16 = true := by
  decide +kernel

private def b0213c17 : List Row := [
  .c 7, .c 11, .c 3, .p pv3 [pv2,pv218657], .p pv2 [pv2,pv3,pv7,pv13883], .c 3,
  .p pv5 [pv2,pv227,pv3853], .c 5, .c 3, .p pv2 [pv2,pv31,pv14107], .p pv3 [pv2,pv3,pv5,pv58309],
  .c 3, .c 5, .p pv5 [pv2,pv3,pv5399], .c 3, .p pv3 [pv2,pv5,pv13,pv29], .c 17, .c 3,
  .p pv11 [pv2,pv7,pv11,pv37,pv307], .c 641, .c 3, .c 7, .c 5, .c 3, .c 31, .c 863, .c 3, .c 5,
  .c 7, .c 3, .c 19, .p pv5 [pv2,pv3,pv3037], .c 3, .c 17, .c 11, .c 3, .c 37, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv15619], .c 229, .c 3, .c 5, .p pv17 [pv2,pv3,pv72889], .c 3, .c 11, .c 107,
  .c 3, .c 41, .c 7, .c 3, .c 113, .c 5, .c 3, .p pv23 [pv2,pv13,pv61,pv1103], .c 31, .c 3, .c 5,
  .c 29, .c 3, .c 13, .p pv2 [pv2,pv3,pv73,pv1997], .c 3, .c 7, .c 937, .c 3,
  .p pv5 [pv2,pv467,pv1873], .c 5, .c 3, .p pv2 [pv2,pv41,pv10667], .c 7, .c 3, .c 5, .c 13, .c 3,
  .c 211, .c 23, .c 3, .c 11, .c 59, .c 3, .p pv2 [pv2,pv7,pv43,pv1453], .c 5, .c 3, .c 7, .c 101,
  .c 3, .c 5, .c 757, .c 3, .p pv13 [pv2,pv5,pv174943], .c 7, .c 3, .c 67,
  .p pv23 [pv2,pv3,pv10799], .c 3, .p pv2 [pv2,pv874721], .c 5, .c 3, .c 13, .c 11, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv12149], .c 3, .c 7, .c 19, .c 3, .p pv2 [pv2,pv113,pv7741],
  .p pv2 [pv2,pv3,pv7,pv59,pv353], .c 3, .c 11, .c 5, .c 3, .c 163, .c 47, .c 3, .c 5, .c 17,
  .c 3, .p pv2 [pv2,pv5,pv137,pv1277], .p pv2 [pv2,pv3,pv97,pv167], .c 3, .p pv5 [pv2,pv7,pv4463],
  .p pv2 [pv2,pv3,pv43,pv6781], .c 3, .c 7, .c 5,
]
private theorem h0213c17 : checkBlock 1749251 128 b0213c17 = true := by
  decide +kernel

private def b0213c18 : List Row := [
  .c 3, .p pv2 [pv2,pv37,pv11821], .c 41, .c 3, .c 5, .c 7, .c 3, .c 17, .c 317, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv11,pv47], .c 3, .p pv2 [pv2,pv277,pv1579], .c 5, .c 3, .c 11, .c 23, .c 3,
  .c 5, .c 31, .c 3, .c 821, .c 13, .c 3, .c 83, .c 7, .c 3, .c 401, .c 5, .c 3,
  .p pv3 [pv2,pv27337], .c 67, .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv7,pv12497], .c 11, .c 3,
  .c 7, .c 17, .c 3, .c 41, .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .c 1031, .c 3,
  .p pv2 [pv2,pv5,pv23,pv7607], .c 79, .c 3, .p pv3 [pv2,pv11,pv9941], .c 37, .c 3, .c 17, .c 5,
  .c 3, .c 7, .c 13, .c 3, .c 5, .c 151, .c 3, .p pv3 [pv2,pv5,pv17,pv31,pv83], .c 7, .c 3,
  .p pv5 [pv2,pv874823], .c 11, .c 3, .c 19, .c 5, .c 3, .c 167, .c 103, .c 3, .c 5, .c 661, .c 3,
  .c 7, .p pv11 [pv2,pv3,pv19,pv1279], .c 3, .c 463, .c 23, .c 3, .c 13, .c 5, .c 3, .c 53, .c 17,
  .c 3, .c 5, .p pv17 [pv2,pv3,pv13,pv701], .c 3, .p pv2 [pv2,pv5,pv17497],
  .p pv5 [pv2,pv3,pv23,pv31,pv409], .c 3, .c 149, .c 13, .c 3, .c 7, .c 5, .c 3, .c 239, .c 251,
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv37,pv4729], .c 31, .c 3, .c 11, .c 263, .c 3, .c 373,
  .c 5, .c 3, .p pv3 [pv2,pv7,pv11,pv13,pv19,pv23], .c 191, .c 3, .c 5, .c 41, .c 3, .c 13,
]
private theorem h0213c18 : checkBlock 1749507 128 b0213c18 = true := by
  decide +kernel

private def b0213c19 : List Row := [
  .c 47, .c 3, .c 19, .c 7, .c 3, .c 29, .c 5, .c 3, .p pv2 [pv2,pv874889], .c 11, .c 3, .c 5,
  .c 13, .c 3, .c 487, .c 17, .c 3, .c 7, .c 43, .c 3, .c 11, .c 5, .c 3, .c 277, .c 7, .c 3,
  .c 5, .c 23, .c 3, .c 353, .c 211, .c 3, .c 17, .c 89, .c 3, .p pv5 [pv2,pv7,pv31247], .c 5,
  .c 3, .c 7, .c 37, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv79,pv443], .c 7, .c 3, .c 31,
  .p pv2 [pv2,pv3,pv11,pv26513], .c 3, .c 23, .c 5, .c 3, .c 11, .c 139, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv145823], .c 3, .c 7, .c 73, .c 3, .p pv5 [pv2,pv23,pv109,pv349], .c 29, .c 3,
  .c 1093, .c 5, .c 3, .p pv2 [pv2,pv131,pv6679], .c 53, .c 3, .c 5, .c 61, .c 3,
  .p pv7 [pv2,pv5,pv174991], .c 11, .c 3, .c 13, .c 19, .c 3, .c 7, .c 5, .c 3, .c 17, .c 193,
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv59,pv1483], .c 13, .c 3, .c 29,
  .p pv7 [pv2,pv3,pv145829], .c 3, .c 1069, .c 5, .c 3, .p pv7 [pv2,pv7,pv239,pv523],
  .p pv13 [pv2,pv3,pv5,pv4861], .c 3, .c 5, .p pv3 [pv2,pv3,pv291661], .c 3, .c 43, .c 67, .c 3,
  .c 97, .c 7, .c 3, .c 313, .c 5, .c 3, .c 37, .p pv3 [pv2,pv3,pv5,pv11,pv5303], .c 3, .c 5,
  .c 17, .c 3, .c 11, .c 41, .c 3, .c 7, .p pv17 [pv2,pv3,pv13,pv71,pv79], .c 3,
  .p pv2 [pv2,pv11,pv31,pv1283], .c 5, .c 3,
]
private theorem h0213c19 : checkBlock 1749763 128 b0213c19 = true := by
  decide +kernel

private def b0213c20 : List Row := [
  .c 829, .c 7, .c 3, .c 5, .c 101, .c 3, .c 17, .c 19, .c 3, .p pv2 [pv2,pv437509], .c 521, .c 3,
  .c 31, .c 5, .c 3, .c 7, .c 887, .c 3, .c 5, .c 43, .c 3, .p pv3 [pv2,pv5,pv13,pv53,pv127],
  .c 7, .c 3, .c 11, .p pv2 [pv2,pv3,pv173,pv281], .c 3, .c 13, .c 5, .c 3, .c 71,
  .p pv13 [pv2,pv3,pv5,pv1823], .c 3, .c 5, .c 79, .c 3, .c 7, .c 23, .c 3, .c 421, .c 13, .c 3,
  .p pv5 [pv2,pv73,pv11987], .c 5, .c 3, .c 19, .c 11, .c 3, .c 5, .c 59, .c 3, .c 29,
  .p pv2 [pv2,pv3,pv11,pv8839], .c 3, .p pv5 [pv2,pv7,pv41,pv3049], .p pv7 [pv2,pv3,pv19,pv101],
  .c 3, .c 7, .c 5, .c 3, .c 23, .p pv11 [pv2,pv3,pv5,pv7,pv463], .c 3, .c 5, .c 7, .c 3, .c 13,
  .p pv5 [pv2,pv3,pv72923], .c 3, .c 317, .p pv3 [pv2,pv3,pv97231], .c 3, .c 419, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv31253], .c 97, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv87509],
  .p pv5 [pv2,pv3,pv7,pv5953], .c 3, .c 127, .c 7, .c 3, .p pv3 [pv2,pv109387], .c 5, .c 3, .c 11,
  .c 17, .c 3, .c 5, .c 307, .c 3, .c 37, .c 109, .c 3, .c 7, .c 53, .c 3, .c 19, .c 5, .c 3,
  .c 13, .c 7, .c 3, .c 5, .c 29, .c 3, .c 67, .c 11, .c 3, .c 229, .c 41, .c 3,
  .p pv2 [pv2,pv7,pv17,pv3677], .c 5, .c 3, .c 7, .c 19, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv29,pv479], .c 3, .p pv37 [pv2,pv5,pv181,pv967], .c 7,
]
private theorem h0213c20 : checkBlock 1750019 128 b0213c20 = true := by
  decide +kernel

private def b0213c21 : List Row := [
  .c 3, .c 23, .c 103, .c 3, .p pv2 [pv2,pv875141], .c 5, .c 3, .p pv3 [pv2,pv139,pv787], .c 31,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv233,pv313], .c 3, .c 7, .c 17, .c 3, .c 13, .c 11, .c 3, .c 1319,
  .c 5, .c 3, .p pv7 [pv2,pv19,pv46061], .c 73, .c 3, .c 5, .c 47, .c 3, .c 11, .c 13, .c 3,
  .c 17, .c 1117, .c 3, .c 7, .c 5, .c 3, .c 281, .p pv7 [pv2,pv3,pv5,pv7,pv1667], .c 3, .c 5,
  .c 7, .c 3, .p pv3 [pv2,pv5,pv43759], .c 71, .c 3, .c 563, .c 23, .c 3, .c 397, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv53,pv337], .p pv17 [pv2,pv3,pv5,pv29173], .c 3, .c 5, .c 83, .c 3,
  .p pv13 [pv2,pv5,pv175039], .c 157, .c 3, .c 11, .c 7, .c 3, .c 79, .c 5, .c 3,
  .p pv3 [pv2,pv11,pv19891], .c 13, .c 3, .c 5, .c 461, .c 3, .c 47, .p pv3 [pv2,pv3,pv17,pv131],
  .c 3, .c 7, .c 617, .c 3, .c 37, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv31,pv3137], .c 3, .c 19, .p pv2 [pv2,pv3,pv11,pv89,pv149], .c 3, .c 163,
  .p pv2 [pv2,pv3,pv291743], .c 3, .c 11, .c 5, .c 3, .c 7, .c 59, .c 3, .c 5, .c 31, .c 3,
  .c 523, .c 7, .c 3, .c 43, .c 13, .c 3, .p pv2 [pv2,pv499,pv877], .c 5, .c 3,
  .p pv2 [pv2,pv29,pv30181], .p pv17 [pv2,pv3,pv5,pv389], .c 3, .c 5, .c 11, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv36469], .c 3, .c 61, .p pv3 [pv2,pv3,pv7,pv11,pv421], .c 3,
  .p pv2 [pv2,pv875261], .c 5, .c 3, .c 11,
]
private theorem h0213c21 : checkBlock 1750275 128 b0213c21 = true := by
  decide +kernel

private def b0213c22 : List Row := [
  .p pv2 [pv2,pv3,pv5,pv23,pv43,pv59], .c 3, .c 5, .c 53, .c 3, .c 13, .c 151, .c 3, .c 881,
  .p pv2 [pv2,pv3,pv145879], .c 3, .c 7, .c 5, .c 3, .c 97, .c 79, .c 3, .c 5, .c 7, .c 3, .c 641,
  .c 11, .c 3, .c 41, .p pv2 [pv2,pv3,pv61,pv4783], .c 3, .p pv5 [pv2,pv419,pv2089], .c 5, .c 3,
  .c 59, .p pv13 [pv2,pv3,pv5,pv53,pv367], .c 3, .c 5, .p pv2 [pv2,pv3,pv113,pv1291], .c 3, .c 31,
  .c 19, .c 3, .p pv11 [pv2,pv11,pv13,pv6121], .c 7, .c 3, .c 73, .c 5, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv5,pv163,pv179], .c 3, .c 5, .c 107, .c 3, .p pv11 [pv2,pv5,pv7,pv89,pv281],
  .c 101, .c 3, .c 7, .c 11, .c 3, .c 17, .c 5, .c 3, .c 109, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv47,pv97], .c 3, .c 11, .c 31, .c 3, .c 211, .p pv2 [pv2,pv3,pv23,pv6343],
  .c 3, .p pv3 [pv2,pv7,pv11,pv29], .c 5, .c 3, .c 7, .p pv41 [pv2,pv3,pv5,pv1621], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv73,pv571], .c 3, .c 23, .c 7, .c 3, .c 13, .p pv2 [pv2,pv3,pv19,pv5119],
  .c 3, .c 47, .c 5, .c 3, .c 113, .c 17, .c 3, .c 5, .c 19, .c 3, .c 7, .c 13, .c 3, .c 11,
  .c 37, .c 3, .p pv2 [pv2,pv439,pv997], .c 5, .c 3, .c 197, .c 41, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv291791], .c 3, .p pv7 [pv2,pv5,pv47,pv149], .c 97, .c 3, .c 1123, .c 29, .c 3,
  .c 7, .c 5, .c 3, .p pv3 [pv2,pv109423], .c 11, .c 3, .c 5, .c 7, .c 3, .c 1049, .c 23, .c 3,
]
private theorem h0213c22 : checkBlock 1750531 128 b0213c22 = true := by
  decide +kernel

private def b0213c23 : List Row := [
  .c 31, .c 71, .c 3, .c 11, .c 5, .c 3, .c 179, .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv23,pv4229],
  .c 3, .p pv2 [pv2,pv5,pv175081], .c 17, .c 3, .c 29, .c 7, .c 3, .c 41, .c 5, .c 3, .c 23,
  .c 19, .c 3, .c 5, .c 11, .c 3, .c 107, .c 359, .c 3, .c 7, .c 31, .c 3, .c 13, .c 5, .c 3,
  .c 11, .c 7, .c 3, .c 5, .c 109, .c 3, .p pv13 [pv2,pv5,pv11,pv1447], .p pv7 [pv2,pv3,pv72953],
  .c 3, .c 37, .c 13, .c 3, .c 61, .c 5, .c 3, .c 7, .c 47, .c 3, .c 5, .c 89, .c 3,
  .p pv2 [pv2,pv5,pv17509], .c 7, .c 3, .c 19, .p pv2 [pv2,pv3,pv53,pv2753], .c 3,
  .p pv3 [pv2,pv13679], .c 5, .c 3, .p pv7 [pv2,pv13,pv67343], .c 23, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv19,pv15359], .c 3, .c 7, .c 29, .c 3, .p pv3 [pv2,pv11,pv101,pv197], .c 421,
  .c 3, .c 59, .c 5, .c 3, .c 17, .c 37, .c 3, .c 5, .c 13, .c 3, .c 53, .c 659, .c 3, .c 23,
  .c 11, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv67,pv73,pv179],
  .p pv61 [pv2,pv3,pv5,pv7,pv11,pv379], .c 3, .c 5, .c 7, .c 3, .c 11, .c 839, .c 3, .c 137,
  .p pv19 [pv2,pv3,pv291833], .c 3, .c 43, .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv58367], .c 3,
  .c 5, .c 17, .c 3, .c 19, .p pv5 [pv2,pv3,pv7,pv13,pv1069], .c 3, .c 863, .c 7, .c 3,
  .p pv3 [pv2,pv47,pv4657], .c 5, .c 3, .p pv11 [pv2,pv875519], .p pv7 [pv2,pv3,pv5,pv19],
]
private theorem h0213c23 : checkBlock 1750787 128 b0213c23 = true := by
  decide +kernel

private def b0213c24 : List Row := [
  .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv43,pv617], .c 3, .c 17, .p pv2 [pv2,pv3,pv337,pv433], .c 3,
  .c 7, .c 19, .c 3, .p pv5 [pv2,pv37,pv23663], .c 5, .c 3, .c 41, .c 7, .c 3, .c 5, .c 131, .c 3,
  .c 521, .p pv2 [pv2,pv3,pv23,pv12689], .c 3, .c 13, .c 43, .c 3, .p pv2 [pv2,pv7,pv62539], .c 5,
  .c 3, .c 7, .c 11, .c 3, .c 5, .c 29, .c 3, .c 1109, .c 7, .c 3, .p pv2 [pv2,pv19,pv23041],
  .c 17, .c 3, .c 11, .c 5, .c 3, .c 593, .p pv2 [pv2,pv3,pv5,pv19457], .c 3, .c 5, .c 733, .c 3,
  .c 7, .p pv3 [pv2,pv3,pv291857], .c 3, .c 151, .p pv2 [pv2,pv3,pv7,pv6949], .c 3, .c 17, .c 5,
  .c 3, .c 31, .c 113, .c 3, .c 5, .c 11, .c 3, .c 439, .c 19, .c 3, .p pv3 [pv2,pv7,pv31271],
  .c 59, .c 3, .c 7, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 7, .c 3, .c 941, .c 127, .c 3,
  .p pv5 [pv2,pv103,pv8501], .c 853, .c 3, .p pv2 [pv2,pv641,pv683], .c 5, .c 3, .c 223, .c 17,
  .c 3, .c 5, .c 251, .c 3, .p pv11 [pv2,pv5,pv13,pv19,pv709], .c 11, .c 3, .c 967, .c 7, .c 3,
  .c 13, .c 5, .c 3, .c 19, .c 743, .c 3, .c 5, .c 571, .c 3, .c 43, .c 1217, .c 3, .c 7, .c 13,
  .c 3, .p pv3 [pv2,pv17,pv79,pv163], .c 5, .c 3, .c 53, .c 7, .c 3, .c 5, .c 19, .c 3,
  .p pv2 [pv2,pv5,pv175129], .p pv2 [pv2,pv3,pv48647], .c 3, .c 59,
]
private theorem h0213c24 : checkBlock 1751043 128 b0213c24 = true := by
  decide +kernel

private def b0213c25 : List Row := [
  .c 11, .c 3, .c 109, .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv11,pv29,pv61], .c 3, .c 5, .c 263,
  .c 3, .c 11, .c 7, .c 3, .p pv5 [pv2,pv875663], .c 167, .c 3, .p pv2 [pv2,pv11,pv53,pv751],
  .c 5, .c 3, .c 29, .c 613, .c 3, .c 5, .c 13, .c 3, .c 7, .p pv5 [pv2,pv3,pv72973], .c 3, .c 17,
  .c 379, .c 3, .c 19, .c 5, .c 3, .c 877, .c 61, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv31,pv107],
  .c 3, .c 23, .c 83, .c 3, .c 11, .c 337, .c 3, .c 7, .c 5, .c 3, .c 13, .c 19, .c 3, .c 5, .c 7,
  .c 3, .p pv2 [pv2,pv5,pv175141], .p pv2 [pv2,pv3,pv13,pv103,pv109], .c 3, .c 907,
  .p pv3 [pv2,pv3,pv97301], .c 3, .c 1181, .c 5, .c 3, .c 647, .c 11, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv16217], .c 3, .c 101, .p pv2 [pv2,pv3,pv7,pv11,pv17,pv223], .c 3, .c 67, .c 7,
  .c 3, .c 11, .c 5, .c 3, .c 17, .c 233, .c 3, .c 5, .p pv3 [pv2,pv3,pv83,pv3517], .c 3, .c 277,
  .c 23, .c 3, .c 7, .c 41, .c 3, .c 107, .c 5, .c 3, .c 73, .c 7, .c 3, .c 5, .c 11, .c 3,
  .c 859, .c 13, .c 3, .p pv2 [pv2,pv37,pv23669], .c 79, .c 3, .c 29, .c 5, .c 3, .c 7, .c 109,
  .c 3, .c 5, .c 17, .c 3, .c 31, .c 7, .c 3, .c 181, .c 139, .c 3, .c 37, .c 5, .c 3, .c 47,
  .p pv3 [pv2,pv3,pv5,pv11677], .c 3,
]
private theorem h0213c25 : checkBlock 1751299 128 b0213c25 = true := by
  decide +kernel

private def b0213c26 : List Row := [
  .c 5, .p pv5 [pv2,pv3,pv145963], .c 3, .c 7, .c 11, .c 3, .p pv5 [pv2,pv875783],
  .p pv29 [pv2,pv3,pv7,pv13,pv401], .c 3, .p pv2 [pv2,pv19,pv1213], .c 5, .c 3,
  .p pv2 [pv2,pv17,pv51517], .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv353,pv827], .c 3, .c 19, .c 31,
  .c 3, .c 53, .p pv11 [pv2,pv3,pv163,pv199], .c 3, .c 7, .c 5, .c 3, .c 89, .c 23, .c 3, .c 5,
  .c 7, .c 3, .c 229, .p pv5 [pv2,pv3,pv443,pv659], .c 3, .p pv2 [pv2,pv97,pv9029], .c 11, .c 3,
  .c 13, .c 5, .c 3, .p pv7 [pv2,pv7,pv125117], .c 71, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv13,pv17,pv1321], .c 3, .c 11, .p pv2 [pv2,pv3,pv7,pv331], .c 3, .c 23, .c 7,
  .c 3, .c 17, .c 5, .c 3, .c 1031, .p pv3 [pv2,pv3,pv5,pv19463], .c 3, .c 5, .c 829, .c 3,
  .c 457, .p pv2 [pv2,pv3,pv137,pv2131], .c 3, .c 7, .p pv19 [pv2,pv3,pv24329], .c 3,
  .p pv2 [pv2,pv437923], .c 5, .c 3, .p pv2 [pv2,pv13,pv89,pv757], .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv983], .c 3, .c 13, .c 1231, .c 3, .c 11, .p pv3 [pv2,pv3,pv181,pv1613],
  .c 3, .c 97, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv87587], .c 7,
  .c 3, .c 409, .c 23, .c 3, .p pv3 [pv2,pv218969], .c 5, .c 3, .c 227, .c 11, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv41,pv7121], .c 3, .c 7, .p pv2 [pv2,pv3,pv11,pv23,pv577], .c 3, .c 43, .c 31,
  .c 3, .c 11, .c 5, .c 3, .c 13, .p pv43 [pv2,pv3,pv5,pv58393], .c 3, .c 5, .c 199, .c 3,
  .p pv3 [pv2,pv5,pv19,pv461], .c 29, .c 3, .c 41, .c 53,
]
private theorem h0213c26 : checkBlock 1751555 128 b0213c26 = true := by
  decide +kernel

private def b0213c27 : List Row := [
  .c 3, .c 7, .c 5, .c 3, .c 19, .p pv2 [pv2,pv3,pv5,pv7,pv43,pv97], .c 3, .c 5, .c 7, .c 3,
  .c 47, .c 17, .c 3, .p pv2 [pv2,pv437959], .c 37, .c 3, .c 263, .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv17,pv229], .c 3, .c 5, .c 19, .c 3, .c 29, .c 43, .c 3, .c 13, .c 7, .c 3,
  .c 179, .c 5, .c 3, .p pv17 [pv2,pv47,pv18637], .c 83, .c 3, .c 5, .c 23, .c 3,
  .p pv2 [pv2,pv5,pv7,pv29,pv863], .c 11, .c 3, .c 7, .c 181, .c 3, .c 31, .c 5, .c 3, .c 1097,
  .c 7, .c 3, .c 5, .c 97, .c 3, .c 197, .p pv5 [pv2,pv3,pv32443], .c 3, .c 73,
  .p pv17 [pv2,pv3,pv72997], .c 3, .c 19, .c 5, .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv9733], .c 3,
  .c 5, .p pv2 [pv2,pv3,pv7,pv59,pv101], .c 3, .c 569, .c 7, .c 3, .c 109, .c 11, .c 3, .c 157,
  .c 5, .c 3, .c 17, .c 13, .c 3, .c 5, .c 29, .c 3, .c 7, .c 67, .c 3, .c 37, .c 499, .c 3,
  .p pv3 [pv2,pv11,pv43,pv463], .c 5, .c 3, .c 653, .p pv23 [pv2,pv3,pv5,pv73], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv29,pv10069], .c 3, .p pv7 [pv2,pv5,pv13,pv13477],
  .p pv2 [pv2,pv3,pv41,pv1187], .c 3, .c 1051, .c 47, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv19,pv23053], .p pv7 [pv2,pv3,pv5,pv7,pv103], .c 3, .c 5, .c 7, .c 3, .c 547,
  .c 191, .c 3, .c 11, .c 13, .c 3, .c 41, .c 5, .c 3, .c 317, .c 37, .c 3, .c 5,
]
private theorem h0213c27 : checkBlock 1751811 128 b0213c27 = true := by
  decide +kernel

private def b0213c28 : List Row := [
  .c 71, .c 3, .c 17, .c 73, .c 3, .p pv2 [pv2,pv647,pv677], .c 7, .c 3, .c 751, .c 5, .c 3,
  .c 31, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv18251], .c 3, .c 13, .c 61, .c 3, .c 7, .c 239,
  .c 3, .c 11, .c 5, .c 3, .p pv13 [pv2,pv197,pv4447], .c 7, .c 3, .c 5, .c 13, .c 3,
  .p pv2 [pv2,pv5,pv83,pv2111], .c 103, .c 3, .p pv3 [pv2,pv219017], .c 17, .c 3, .c 89, .c 5,
  .c 3, .c 7, .c 29, .c 3, .c 5, .c 11, .c 3, .c 19, .c 7, .c 3, .c 823, .c 739, .c 3, .c 17,
  .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv19,pv29,pv53], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv23,pv12697], .c 3, .c 7, .p pv5 [pv2,pv3,pv13], .c 3, .p pv2 [pv2,pv438049],
  .c 19, .c 3, .c 719, .c 5, .c 3, .c 23, .p pv2 [pv2,pv3,pv5,pv19469], .c 3, .c 5, .c 41, .c 3,
  .p pv2 [pv2,pv5,pv79,pv1109], .c 11, .c 3, .p pv2 [pv2,pv7,pv257,pv487],
  .p pv11 [pv2,pv3,pv48673], .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv29,pv30211], .c 17, .c 3,
  .c 5, .c 7, .c 3, .c 67, .p pv2 [pv2,pv3,pv146021], .c 3, .c 13, .c 1201, .c 3,
  .p pv5 [pv2,pv876131], .c 5, .c 3, .p pv2 [pv2,pv7,pv62581], .p pv3 [pv2,pv3,pv5,pv13,pv4493],
  .c 3, .c 5, .c 157, .c 3, .c 659, .c 13, .c 3, .c 631, .c 7, .c 3, .c 43, .c 5, .c 3, .c 41,
  .c 23, .c 3, .c 5, .p pv3 [pv2,pv3,pv31,pv9421], .c 3, .c 11, .c 19, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv67,pv1453], .c 3,
]
private theorem h0213c28 : checkBlock 1752067 128 b0213c28 = true := by
  decide +kernel

private def b0213c29 : List Row := [
  .p pv2 [pv2,pv11,pv13,pv557], .c 5, .c 3, .c 349, .c 7, .c 3, .c 5, .c 31, .c 3,
  .p pv2 [pv2,pv5,pv41,pv2137], .c 17, .c 3, .c 23, .c 577, .c 3, .p pv3 [pv2,pv7,pv7823], .c 5,
  .c 3, .c 7, .c 13, .c 3, .c 5, .c 137, .c 3, .p pv2 [pv2,pv5,pv19,pv23,pv401], .c 7, .c 3,
  .c 11, .c 43, .c 3, .c 29, .c 5, .c 3, .c 19, .c 773, .c 3, .c 5, .p pv5 [pv2,pv3,pv146033],
  .c 3, .c 7, .p pv2 [pv2,pv3,pv97,pv3011], .c 3, .p pv5 [pv2,pv876203], .c 607, .c 3, .c 13,
  .c 5, .c 3, .p pv2 [pv2,pv59,pv14851], .c 11, .c 3, .c 5, .c 19, .c 3, .c 37, .c 293, .c 3,
  .p pv2 [pv2,pv7,pv8941], .c 13, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv13691], .c 101, .c 3,
  .c 5, .c 7, .c 3, .c 31, .c 41, .c 3, .p pv2 [pv2,pv876233], .c 61, .c 3, .c 127, .c 5, .c 3,
  .c 17, .p pv7 [pv2,pv3,pv5,pv1217], .c 3, .c 5, .c 11, .c 3, .c 13, .c 71, .c 3,
  .p pv3 [pv2,pv17,pv379], .c 7, .c 3, .c 19, .c 5, .c 3, .c 11, .c 73, .c 3, .c 5, .c 13, .c 3,
  .p pv3 [pv2,pv5,pv7,pv11,pv569], .c 31, .c 3, .c 7, .p pv23 [pv2,pv3,pv29,pv1259], .c 3, .c 919,
  .c 5, .c 3, .p pv2 [pv2,pv149,pv5881], .c 7, .c 3, .c 5, .c 17, .c 3, .c 43, .c 11, .c 3, .c 29,
  .c 1223, .c 3, .p pv2 [pv2,pv7,pv125183], .c 5, .c 3, .c 7, .c 811, .c 3, .c 5, .c 23,
]
private theorem h0213c29 : checkBlock 1752323 128 b0213c29 = true := by
  decide +kernel

private def b0213c30 : List Row := [
  .c 3, .c 17, .c 7, .c 3, .c 239, .c 179, .c 3, .c 199, .c 5, .c 3,
  .p pv7 [pv2,pv17,pv19,pv2713], .p pv13 [pv2,pv3,pv5,pv23,pv127], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv97367], .c 3, .c 7, .p pv5 [pv2,pv3,pv146051], .c 3, .c 19, .c 11, .c 3,
  .c 23, .c 5, .c 3, .p pv2 [pv2,pv83,pv5279], .p pv3 [pv2,pv3,pv5,pv11,pv47,pv113], .c 3, .c 5,
  .c 43, .c 3, .c 11, .p pv3 [pv2,pv3,pv97369], .c 3, .c 13, .c 17, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv876329], .c 479, .c 3, .c 5, .c 7, .c 3, .c 839, .c 13, .c 3, .c 47,
  .p pv11 [pv2,pv3,pv31,pv349], .c 3, .c 17, .c 5, .c 3, .c 983, .p pv2 [pv2,pv3,pv5,pv37,pv1579],
  .c 3, .c 5, .c 347, .c 3, .p pv2 [pv2,pv5,pv17,pv1031], .p pv3 [pv2,pv3,pv7,pv29,pv1439], .c 3,
  .c 11, .c 7, .c 3, .c 59, .c 5, .c 3, .p pv11 [pv2,pv11,pv79669],
  .p pv7 [pv2,pv3,pv5,pv67,pv109], .c 3, .c 5, .c 37, .c 3, .c 19, .c 251, .c 3, .c 7, .c 163,
  .c 3, .c 113, .c 5, .c 3, .p pv2 [pv2,pv157,pv2791], .c 7, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv146063], .c 3, .c 23, .c 53, .c 3, .c 107, .c 19, .c 3, .c 11, .c 5, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv5,pv131,pv223], .c 3, .c 5, .c 67, .c 3, .c 41, .c 7, .c 3, .c 727,
  .p pv3 [pv2,pv3,pv292133], .c 3, .c 13, .c 5, .c 3, .c 43, .p pv2 [pv2,pv3,pv5,pv58427], .c 3,
  .c 5, .c 11, .c 3, .c 7, .p pv7 [pv2,pv3,pv97379], .c 3, .p pv2 [pv2,pv19,pv193,pv239], .c 13,
  .c 3, .c 31,
]
private theorem h0213c30 : checkBlock 1752579 128 b0213c30 = true := by
  decide +kernel

private def b0213c31 : List Row := [
  .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv541], .c 3, .c 5, .c 29, .c 3,
  .p pv7 [pv2,pv5,pv11,pv3187], .c 17, .c 3, .p pv3 [pv2,pv7,pv113,pv277], .c 233, .c 3, .c 7,
  .c 5, .c 3, .c 53, .p pv19 [pv2,pv3,pv5,pv7,pv17,pv491], .c 3, .c 5, .c 7, .c 3, .c 13, .c 11,
  .c 3, .c 17, .p pv11 [pv2,pv3,pv73037], .c 3, .p pv2 [pv2,pv438223], .c 5, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv5,pv5843], .c 3, .c 5, .c 13, .c 3, .c 131, .p pv5 [pv2,pv3,pv7,pv37,pv47],
  .c 3, .p pv2 [pv2,pv11,pv39839], .c 7, .c 3, .p pv2 [pv2,pv23,pv53,pv719], .c 5, .c 3, .c 139,
  .c 79, .c 3, .c 5, .p pv5 [pv2,pv3,pv73039], .c 3, .p pv2 [pv2,pv5,pv7,pv19,pv659],
  .p pv3 [pv2,pv3,pv292157], .c 3, .c 7, .c 11, .c 3, .p pv3 [pv2,pv219119], .c 5, .c 3, .c 13,
  .c 7, .c 3, .c 5, .c 1321, .c 3, .c 11, .c 1151, .c 3, .p pv3 [pv2,pv331],
  .p pv2 [pv2,pv3,pv19,pv15377], .c 3, .p pv5 [pv2,pv7,pv11,pv11383], .c 5, .c 3, .c 7, .c 23,
  .c 3, .c 5, .c 19, .c 3, .c 1033, .c 7, .c 3, .p pv5 [pv2,pv17,pv47,pv1097], .c 173, .c 3,
  .p pv2 [pv2,pv438253], .c 5, .c 3, .c 31, .c 29, .c 3, .c 5, .c 349, .c 3, .c 7, .c 89, .c 3,
  .c 11, .p pv3 [pv2,pv3,pv7,pv13913], .c 3, .c 83, .c 5, .c 3, .p pv3 [pv2,pv11,pv1811],
  .p pv2 [pv2,pv3,pv5,pv13,pv29,pv31], .c 3, .c 5, .c 17, .c 3, .c 71, .c 13, .c 3, .c 43,
  .p pv2 [pv2,pv3,pv139,pv1051], .c 3, .c 7, .c 5, .c 3, .c 29, .c 11, .c 3, .c 5, .c 7, .c 3,
]
private theorem h0213c31 : checkBlock 1752835 128 b0213c31 = true := by
  decide +kernel

def rows0213 : List Row :=
  b0213c00 ++ b0213c01 ++ b0213c02 ++ b0213c03 ++ b0213c04 ++ b0213c05 ++ b0213c06 ++ b0213c07 ++
  b0213c08 ++ b0213c09 ++ b0213c10 ++ b0213c11 ++ b0213c12 ++ b0213c13 ++ b0213c14 ++ b0213c15 ++
  b0213c16 ++ b0213c17 ++ b0213c18 ++ b0213c19 ++ b0213c20 ++ b0213c21 ++ b0213c22 ++ b0213c23 ++
  b0213c24 ++ b0213c25 ++ b0213c26 ++ b0213c27 ++ b0213c28 ++ b0213c29 ++ b0213c30 ++ b0213c31

attribute [local irreducible] checkBlock checkRows checkPrime

theorem checked0213 : checkBlock 1744899 4096 rows0213 = true :=
  checkBlock_append h0213c00 (
    checkBlock_append h0213c01 (
    checkBlock_append h0213c02 (
    checkBlock_append h0213c03 (
    checkBlock_append h0213c04 (
    checkBlock_append h0213c05 (
    checkBlock_append h0213c06 (
    checkBlock_append h0213c07 (
    checkBlock_append h0213c08 (
    checkBlock_append h0213c09 (
    checkBlock_append h0213c10 (
    checkBlock_append h0213c11 (
    checkBlock_append h0213c12 (
    checkBlock_append h0213c13 (
    checkBlock_append h0213c14 (
    checkBlock_append h0213c15 (
    checkBlock_append h0213c16 (
    checkBlock_append h0213c17 (
    checkBlock_append h0213c18 (
    checkBlock_append h0213c19 (
    checkBlock_append h0213c20 (
    checkBlock_append h0213c21 (
    checkBlock_append h0213c22 (
    checkBlock_append h0213c23 (
    checkBlock_append h0213c24 (
    checkBlock_append h0213c25 (
    checkBlock_append h0213c26 (
    checkBlock_append h0213c27 (
    checkBlock_append h0213c28 (
    checkBlock_append h0213c29 (
    checkBlock_append h0213c30 (
    h0213c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
