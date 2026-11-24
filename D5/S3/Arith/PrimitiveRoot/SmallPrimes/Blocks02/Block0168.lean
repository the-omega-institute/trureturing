/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks02/Block0168
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks02/Block0168.checked0168
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table021
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table025
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table029
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table030
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table037
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table049
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table072
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table124

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0168c00 : List Row := [
  .c 3, .c 313, .c 7, .c 3, .c 811, .c 17, .c 3, .c 491, .c 5, .c 3, .c 263, .c 307, .c 3, .c 5,
  .c 11, .c 3, .c 7, .c 59, .c 3, .c 13, .c 127, .c 3, .c 17, .c 5, .c 3, .c 11, .c 29, .c 3,
  .c 5, .p pv11 [pv2,pv3,pv38231], .c 3, .p pv3 [pv2,pv5,pv11,pv17,pv23], .c 13, .c 3, .c 101,
  .c 41, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv31,pv79,pv281], .c 19, .c 3, .c 5, .c 7, .c 3,
  .c 241, .c 11, .c 3, .c 53, .p pv3 [pv2,pv3,pv229393], .c 3, .c 37, .c 5, .c 3, .c 29, .c 17,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv57349], .c 3, .c 67, .p pv13 [pv2,pv3,pv7,pv32771], .c 3, .c 43,
  .c 7, .c 3, .p pv3 [pv2,pv172049], .c 5, .c 3, .c 397, .c 13, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv71,pv359], .c 3, .c 41, .c 277, .c 3, .c 7, .c 11, .c 3,
  .p pv5 [pv2,pv17,pv40483], .c 5, .c 3, .p pv2 [pv2,pv101,pv3407], .c 7, .c 3, .c 5, .c 37, .c 3,
  .c 11, .p pv2 [pv2,pv3,pv47,pv1627], .c 3, .p pv5 [pv2,pv688223], .p pv11 [pv2,pv3,pv67,pv107],
  .c 3, .c 13, .c 5, .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv2549], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv13,pv2521], .c 3, .p pv13 [pv2,pv5,pv59,pv2333], .c 7, .c 3, .c 71, .c 13,
  .c 3, .c 199, .c 5, .c 3, .c 47, .p pv3 [pv2,pv3,pv5,pv17,pv2699], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv79], .c 3, .c 7, .p pv13 [pv2,pv3,pv383,pv599], .c 3, .c 11,
  .p pv2 [pv2,pv3,pv7,pv2341], .c 3, .p pv3 [pv2,pv19,pv283],
]
private theorem h0168c00 : checkBlock 1376259 128 b0168c00 = true := by
  decide +kernel

private def b0168c01 : List Row := [
  .c 5, .c 3, .c 229, .c 911, .c 3, .c 5, .c 23, .c 3, .c 13, .p pv5 [pv2,pv3,pv38237], .c 3,
  .c 191, .p pv3 [pv2,pv3,pv229423], .c 3, .c 7, .c 5, .c 3, .c 347, .c 11, .c 3, .c 5, .c 7,
  .c 3, .c 73, .c 89, .c 3, .p pv5 [pv2,pv113,pv6091], .c 19, .c 3, .c 11, .c 5, .c 3, .c 223,
  .c 167, .c 3, .c 5, .c 61, .c 3, .p pv13 [pv2,pv5,pv137659], .c 977, .c 3, .c 883, .c 7, .c 3,
  .p pv2 [pv2,pv43,pv16007], .c 5, .c 3, .c 13, .c 149, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv7,pv9833], .p pv17 [pv2,pv3,pv13,pv37,pv53], .c 3, .c 7, .c 331, .c 3, .c 401,
  .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 59, .c 3, .c 659, .p pv2 [pv2,pv3,pv89,pv1289], .c 3,
  .c 41, .c 29, .c 3, .c 643, .c 5, .c 3, .c 7, .c 389, .c 3, .c 5, .c 17, .c 3, .c 571, .c 7,
  .c 3, .c 13, .c 179, .c 3, .p pv2 [pv2,pv344173], .c 5, .c 3, .p pv2 [pv2,pv41,pv103,pv163],
  .p pv11 [pv2,pv3,pv5,pv13,pv353], .c 3, .c 5, .c 73, .c 3, .c 7, .c 13, .c 3, .c 29,
  .p pv3 [pv2,pv3,pv7,pv32779], .c 3, .p pv2 [pv2,pv577,pv1193], .c 5, .c 3,
  .p pv3 [pv2,pv17,pv53,pv191], .c 43, .c 3, .c 5, .p pv5 [pv2,pv3,pv14341], .c 3, .c 31, .c 373,
  .c 3, .p pv2 [pv2,pv7,pv29,pv3391], .c 11, .c 3, .c 7, .c 5, .c 3, .c 19, .c 71, .c 3, .c 5,
  .c 7, .c 3,
]
private theorem h0168c01 : checkBlock 1376515 128 b0168c01 = true := by
  decide +kernel

private def b0168c02 : List Row := [
  .c 11, .p pv2 [pv2,pv3,pv31,pv3701], .c 3, .p pv3 [pv2,pv172097], .c 17, .c 3, .c 67, .c 5,
  .c 3, .p pv2 [pv2,pv7,pv49171], .c 13, .c 3, .c 5, .c 19, .c 3, .c 103, .c 23, .c 3, .c 37,
  .c 7, .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv47,pv97,pv151], .c 41, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv23,pv907], .c 3, .c 61, .c 29, .c 3, .c 7, .p pv3 [pv2,pv3,pv2833], .c 3,
  .c 13, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 997, .c 3, .c 163, .c 661, .c 3, .c 181, .c 13,
  .c 3, .c 19, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 53, .c 3, .c 29, .c 7, .c 3,
  .p pv5 [pv2,pv31,pv347], .p pv2 [pv2,pv3,pv17,pv13499], .c 3, .c 11, .c 5, .c 3, .c 149, .c 19,
  .c 3, .c 5, .c 67, .c 3, .c 7, .p pv2 [pv2,pv3,pv229487], .c 3, .c 31,
  .p pv13 [pv2,pv3,pv7,pv683], .c 3, .c 101, .c 5, .c 3, .p pv2 [pv2,pv727,pv947], .c 23, .c 3,
  .c 5, .c 11, .c 3, .c 271, .c 61, .c 3, .p pv2 [pv2,pv7,pv49177], .c 47, .c 3, .c 7, .c 5, .c 3,
  .c 11, .p pv2 [pv2,pv3,pv5,pv7,pv79,pv83], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv11,pv569],
  .c 17, .c 3, .c 19, .c 31, .c 3, .c 53, .c 5, .c 3, .c 13, .c 59, .c 3, .c 5, .c 29, .c 3,
  .c 269, .c 11, .c 3, .c 17, .c 7, .c 3, .p pv5 [pv2,pv688511], .c 5,
]
private theorem h0168c02 : checkBlock 1376771 128 b0168c02 = true := by
  decide +kernel

private def b0168c03 : List Row := [
  .c 3, .c 37, .p pv3 [pv2,pv3,pv5,pv197,pv233], .c 3, .c 5, .p pv5 [pv2,pv3,pv29,pv1319], .c 3,
  .p pv11 [pv2,pv5,pv7,pv2459], .p pv2 [pv2,pv3,pv229507], .c 3, .c 7, .c 79, .c 3, .c 47, .c 5,
  .c 3, .c 523, .c 7, .c 3, .c 5, .c 41, .c 3, .p pv11 [pv2,pv5,pv137707], .c 139, .c 3, .c 13,
  .c 11, .c 3, .c 449, .c 5, .c 3, .c 7, .c 421, .c 3, .c 5, .c 89, .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv109,pv6317], .c 97, .c 3, .c 31, .c 5, .c 3, .c 17,
  .p pv13 [pv2,pv3,pv5,pv19,pv151], .c 3, .c 5, .p pv3 [pv2,pv3,pv76507], .c 3, .c 7,
  .p pv5 [pv2,pv3,pv114761], .c 3, .p pv3 [pv2,pv17,pv61,pv83], .c 19, .c 3, .c 439, .c 5, .c 3,
  .c 41, .p pv23 [pv2,pv3,pv5,pv9181], .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv10433], .c 3, .c 43,
  .c 691, .c 3, .c 11, .p pv11 [pv2,pv3,pv13,pv2207], .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv59,pv1061], .c 13, .c 3, .c 5, .c 7, .c 3, .p pv31 [pv2,pv5,pv41,pv3359],
  .c 397, .c 3, .c 61, .c 857, .c 3, .c 131, .c 5, .c 3, .c 227, .c 11, .c 3, .c 5, .c 23, .c 3,
  .c 17, .p pv5 [pv2,pv3,pv7,pv11,pv271], .c 3, .c 197, .c 7, .c 3, .c 11, .c 5, .c 3, .c 29,
  .c 47, .c 3, .c 5, .c 43, .c 3, .c 37, .c 19, .c 3, .c 7, .c 13, .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv29,pv31,pv383], .c 7, .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv269],
]
private theorem h0168c03 : checkBlock 1377027 128 b0168c03 = true := by
  decide +kernel

private def b0168c04 : List Row := [
  .c 607, .c 3, .c 443, .c 17, .c 3, .p pv2 [pv2,pv7,pv7027], .c 5, .c 3, .c 7, .c 191, .c 3,
  .c 5, .c 733, .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv103,pv3343], .c 61, .c 3, .c 17, .c 5,
  .c 3, .c 19, .c 263, .c 3, .c 5, .c 13, .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv547,pv1259],
  .p pv11 [pv2,pv3,pv7,pv19,pv863], .c 3, .p pv3 [pv2,pv172169], .c 5, .c 3,
  .p pv7 [pv2,pv688679], .c 31, .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv137737], .c 433, .c 3,
  .p pv5 [pv2,pv7,pv11,pv13,pv43], .p pv2 [pv2,pv3,pv23,pv1109], .c 3, .c 7, .c 5, .c 3, .c 13,
  .c 17, .c 3, .c 5, .c 7, .c 3, .c 23, .p pv5 [pv2,pv3,pv13,pv17659], .c 3,
  .p pv5 [pv2,pv353,pv1951], .c 11, .c 3, .c 29, .c 5, .c 3, .c 43,
  .p pv7 [pv2,pv3,pv5,pv11,pv2087], .c 3, .c 5, .p pv2 [pv2,pv3,pv173,pv1327], .c 3, .c 11,
  .c 109, .c 3, .c 73, .c 7, .c 3, .c 19, .c 5, .c 3, .c 389, .p pv3 [pv2,pv3,pv5,pv3061], .c 3,
  .c 5, .p pv5 [pv2,pv3,pv28697], .c 3, .c 557, .c 647, .c 3, .c 7, .p pv2 [pv2,pv3,pv83,pv461],
  .c 3, .c 37, .c 5, .c 3, .p pv11 [pv2,pv199,pv3461], .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv773], .c 3, .p pv2 [pv2,pv5,pv139,pv991], .c 13, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv229583], .c 3, .c 349, .c 5, .c 3, .c 7, .c 887, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv23,pv31], .c 3, .c 277, .c 7, .c 3, .c 17, .c 29, .c 3,
  .p pv2 [pv2,pv13,pv59,pv449], .c 5, .c 3,
]
private theorem h0168c04 : checkBlock 1377283 128 b0168c04 = true := by
  decide +kernel

private def b0168c05 : List Row := [
  .c 23, .c 11, .c 3, .c 5, .c 31, .c 3, .c 7, .p pv5 [pv2,pv3,pv11,pv2609], .c 3, .c 19, .c 41,
  .c 3, .c 11, .c 5, .c 3, .c 127, .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv19,pv53], .c 3, .c 919,
  .c 73, .c 3, .c 29, .p pv2 [pv2,pv3,pv114799], .c 3, .c 7, .c 5, .c 3, .c 173,
  .p pv29 [pv2,pv3,pv5,pv7,pv41], .c 3, .c 5, .c 7, .c 3, .c 683, .c 71, .c 3, .c 47, .c 211,
  .c 3, .c 13, .c 5, .c 3, .c 11, .c 23, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv8831], .c 3, .c 41,
  .p pv3 [pv2,pv3,pv7,pv32801], .c 3, .c 1103, .c 7, .c 3, .p pv2 [pv2,pv19,pv18127], .c 5, .c 3,
  .p pv2 [pv2,pv37,pv18617], .c 563, .c 3, .c 5, .p pv2 [pv2,pv3,pv76537], .c 3, .c 19, .c 11,
  .c 3, .c 7, .p pv3 [pv2,pv3,pv229613], .c 3, .c 191, .c 5, .c 3, .c 587, .c 7, .c 3, .c 5,
  .c 17, .c 3, .c 13, .c 29, .c 3, .c 929, .c 19, .c 3, .p pv3 [pv2,pv7,pv12301], .c 5, .c 3,
  .c 7, .c 67, .c 3, .c 5, .c 13, .c 3, .c 17, .c 7, .c 3, .p pv3 [pv2,pv172217], .c 11, .c 3,
  .c 281, .c 5, .c 3, .p pv2 [pv2,pv17,pv20261], .p pv7 [pv2,pv3,pv5,pv11,pv167], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv12757], .c 3, .c 7, .c 43, .c 3, .c 877, .c 23, .c 3,
  .p pv2 [pv2,pv11,pv173,pv181], .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv22963], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv229631], .c 3, .p pv7 [pv2,pv5,pv29,pv4751], .p pv5 [pv2,pv3,pv13,pv23],
]
private theorem h0168c05 : checkBlock 1377539 128 b0168c05 = true := by
  decide +kernel

private def b0168c06 : List Row := [
  .c 3, .c 241, .c 17, .c 3, .c 7, .c 5, .c 3, .c 89, .p pv2 [pv2,pv3,pv5,pv7], .c 3, .c 5, .c 7,
  .c 3, .p pv2 [pv2,pv5,pv68891], .c 19, .c 3, .c 11, .p pv7 [pv2,pv3,pv38273], .c 3, .c 17, .c 5,
  .c 3, .c 79, .c 53, .c 3, .c 5, .p pv3 [pv2,pv3,pv41,pv1867], .c 3,
  .p pv13 [pv2,pv5,pv17,pv1621], .p pv2 [pv2,pv3,pv7,pv47,pv349], .c 3, .c 13, .c 7, .c 3, .c 509,
  .c 5, .c 3, .c 109, .c 11, .c 3, .c 5, .c 29, .c 3, .p pv3 [pv2,pv5,pv7,pv19,pv37], .c 13, .c 3,
  .c 7, .c 811, .c 3, .c 11, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 23, .c 3,
  .p pv17 [pv2,pv5,pv137791], .p pv5 [pv2,pv3,pv57413], .c 3, .c 37, .c 31, .c 3,
  .p pv7 [pv2,pv7,pv13,pv67,pv113], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv23,pv1997], .c 3,
  .c 5, .c 11, .c 3, .c 1069, .c 7, .c 3, .c 53, .c 643, .c 3, .c 23, .c 5, .c 3, .c 11, .c 13,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv83,pv2767], .c 3, .c 7, .p pv2 [pv2,pv3,pv4253], .c 3,
  .p pv3 [pv2,pv23,pv7489], .c 293, .c 3, .p pv5 [pv2,pv97,pv7103], .c 5, .c 3, .c 67, .c 37,
  .c 3, .c 5, .c 79, .c 3, .p pv29 [pv2,pv5,pv13,pv53], .c 11, .c 3, .p pv5 [pv2,pv7,pv98429],
  .p pv11 [pv2,pv3,pv19139], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv557,pv1237], .c 43, .c 3, .c 5,
  .c 7, .c 3, .p pv7 [pv2,pv5,pv137803], .p pv5 [pv2,pv3,pv19,pv1511], .c 3, .c 17, .c 13, .c 3,
  .c 31, .c 5, .c 3, .c 83,
]
private theorem h0168c06 : checkBlock 1377795 128 b0168c06 = true := by
  decide +kernel

private def b0168c07 : List Row := [
  .c 19, .c 3, .c 5, .p pv5 [pv2,pv3,pv67,pv857], .c 3, .p pv2 [pv2,pv5,pv68903], .c 59, .c 3,
  .p pv2 [pv2,pv689033], .c 7, .c 3, .p pv3 [pv2,pv172259], .c 5, .c 3, .c 97,
  .p pv7 [pv2,pv3,pv5,pv11,pv29], .c 3, .c 5, .c 47, .c 3, .c 11, .c 601, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv76561], .c 3, .p pv23 [pv2,pv11,pv37,pv1693], .c 5, .c 3, .c 29, .c 7, .c 3,
  .c 5, .c 13, .c 3, .c 179, .c 67, .c 3, .c 19, .p pv17 [pv2,pv3,pv28711], .c 3, .c 41, .c 5,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv103,pv223], .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv11,pv19,pv157],
  .c 3, .p pv11 [pv2,pv5,pv43,pv641], .c 7, .c 3, .c 11, .c 53, .c 3, .p pv2 [pv2,pv689081], .c 5,
  .c 3, .c 13, .c 761, .c 3, .c 5, .c 151, .c 3, .c 7, .c 23, .c 3, .p pv2 [pv2,pv689093],
  .p pv13 [pv2,pv3,pv7,pv1823], .c 3, .c 43, .c 5, .c 3, .p pv7 [pv2,pv31,pv22229], .c 11, .c 3,
  .c 5, .c 17, .c 3, .c 863, .c 37, .c 3, .p pv3 [pv2,pv7,pv24611], .p pv23 [pv2,pv3,pv229703],
  .c 3, .c 7, .c 5, .c 3, .c 23, .p pv17 [pv2,pv3,pv5,pv7,pv6563], .c 3, .c 5, .c 7, .c 3, .c 17,
  .c 103, .c 3, .c 13, .p pv7 [pv2,pv3,pv57427], .c 3, .p pv2 [pv2,pv23,pv71,pv211], .c 5, .c 3,
  .c 773, .c 113, .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv137827], .c 13, .c 3,
  .p pv2 [pv2,pv587], .c 7, .c 3, .c 29, .c 5, .c 3, .c 11, .c 31, .c 3, .c 5, .c 41, .c 3,
  .p pv13 [pv2,pv5,pv7,pv11,pv179], .c 157, .c 3,
]
private theorem h0168c07 : checkBlock 1378051 128 b0168c07 = true := by
  decide +kernel

private def b0168c08 : List Row := [
  .c 7, .c 17, .c 3, .c 73, .c 5, .c 3, .p pv13 [pv2,pv53,pv13003], .c 7, .c 3, .c 5, .c 937,
  .c 3, .c 127, .c 11, .c 3, .p pv3 [pv2,pv19,pv2267], .p pv2 [pv2,pv3,pv13,pv41,pv431], .c 3,
  .c 17, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 137, .c 3, .c 37, .c 7, .c 3, .c 23, .c 47, .c 3,
  .p pv2 [pv2,pv509,pv677], .c 5, .c 3, .c 41, .c 83, .c 3, .c 5, .p pv2 [pv2,pv3,pv73,pv1049],
  .c 3, .c 7, .c 19, .c 3, .p pv2 [pv2,pv344599], .c 11, .c 3, .c 13, .c 5, .c 3, .c 197, .c 17,
  .c 3, .c 5, .c 59, .c 3, .c 11, .c 379, .c 3, .p pv5 [pv2,pv7,pv98459], .c 13, .c 3, .c 7, .c 5,
  .c 3, .p pv17 [pv2,pv689219], .p pv19 [pv2,pv3,pv5,pv7,pv547], .c 3, .c 5, .c 7, .c 3, .c 43,
  .c 577, .c 3, .c 29, .c 23, .c 3, .c 47, .c 5, .c 3, .c 19, .c 79, .c 3, .c 5, .c 31, .c 3,
  .c 13, .c 653, .c 3, .c 11, .c 7, .c 3, .c 283, .c 5, .c 3, .p pv2 [pv2,pv11,pv62659],
  .p pv2 [pv2,pv3,pv5,pv919], .c 3, .c 5, .c 13, .c 3, .p pv7 [pv2,pv5,pv7,pv47,pv419], .c 17,
  .c 3, .c 7, .p pv7 [pv2,pv3,pv229753], .c 3, .c 109, .c 5, .c 3, .p pv3 [pv2,pv23,pv1873], .c 7,
  .c 3, .c 5, .c 43, .c 3, .p pv2 [pv2,pv5,pv68927], .c 41, .c 3, .c 17, .c 101, .c 3, .c 11,
  .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv359],
]
private theorem h0168c08 : checkBlock 1378307 128 b0168c08 = true := by
  decide +kernel

private def b0168c09 : List Row := [
  .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv521], .c 3, .c 227, .c 7, .c 3, .c 271,
  .p pv2 [pv2,pv3,pv229763], .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv107,pv3221],
  .p pv3 [pv2,pv3,pv5,pv45953], .c 3, .c 5, .c 11, .c 3, .c 7, .p pv7 [pv2,pv3,pv19,pv29,pv139],
  .c 3, .c 71, .c 827, .c 3, .p pv2 [pv2,pv344653], .c 5, .c 3, .c 11, .c 19, .c 3, .c 5, .c 829,
  .c 3, .c 29, .c 317, .c 3, .c 13, .p pv3 [pv2,pv3,pv191,pv401], .c 3, .c 7, .c 5, .c 3, .c 17,
  .c 47, .c 3, .c 5, .c 7, .c 3, .c 61, .c 11, .c 3, .c 337, .p pv2 [pv2,pv3,pv114889], .c 3,
  .p pv3 [pv2,pv199,pv433], .c 5, .c 3, .p pv11 [pv2,pv7,pv19,pv71,pv73],
  .p pv7 [pv2,pv3,pv5,pv11489], .c 3, .c 5, .c 569, .c 3, .p pv2 [pv2,pv5,pv137869], .c 1013,
  .c 3, .c 19, .c 7, .c 3, .p pv5 [pv2,pv13,pv4079], .c 5, .c 3, .c 43, .c 1063, .c 3, .c 5,
  .c 17, .c 3, .p pv3 [pv2,pv5,pv7,pv1231], .c 503, .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv344683], .c 5, .c 3, .c 409, .c 7, .c 3, .c 5, .c 29, .c 3, .c 11, .c 1039, .c 3,
  .c 647, .p pv13 [pv2,pv3,pv23,pv97,pv103], .c 3, .p pv2 [pv2,pv7,pv11,pv1279], .c 5, .c 3, .c 7,
  .c 59, .c 3, .c 5, .p pv23 [pv2,pv3,pv7,pv29,pv283], .c 3, .c 23, .c 7, .c 3, .c 31, .c 41,
  .c 3, .c 13, .c 5, .c 3, .p pv7 [pv2,pv227,pv3037], .p pv11 [pv2,pv3,pv5,pv383], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv13,pv1607], .c 3, .c 7, .p pv2 [pv2,pv3,pv114901], .c 3, .c 11,
]
private theorem h0168c09 : checkBlock 1378563 128 b0168c09 = true := by
  decide +kernel

private def b0168c10 : List Row := [
  .c 13, .c 3, .p pv5 [pv2,pv689411], .c 5, .c 3, .c 191, .p pv3 [pv2,pv3,pv5,pv19,pv41,pv59],
  .c 3, .c 5, .c 179, .c 3, .p pv3 [pv2,pv5,pv34471], .p pv3 [pv2,pv3,pv37,pv6211], .c 3,
  .p pv5 [pv2,pv7,pv149,pv661], .c 19, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv13,pv181,pv293],
  .c 11, .c 3, .c 5, .c 7, .c 3, .c 13, .c 23, .c 3, .c 89, .c 37, .c 3, .c 11, .c 5, .c 3, .c 59,
  .c 71, .c 3, .c 5, .c 13, .c 3, .c 53, .p pv5 [pv2,pv3,pv7,pv32831], .c 3,
  .p pv2 [pv2,pv19,pv131,pv277], .c 7, .c 3, .c 857, .c 5, .c 3, .c 23, .c 17, .c 3, .c 5, .c 11,
  .c 3, .c 157, .c 47, .c 3, .c 7, .c 113, .c 3, .p pv5 [pv2,pv23,pv31,pv967], .c 5, .c 3, .c 11,
  .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv114913], .c 3, .p pv3 [pv2,pv5,pv11,pv1567], .c 19, .c 3,
  .c 43, .p pv13 [pv2,pv3,pv57457], .c 3, .c 31, .c 5, .c 3, .c 7, .c 373, .c 3, .c 5, .c 547,
  .c 3, .c 953, .c 7, .c 3, .p pv2 [pv2,pv344749], .p pv3 [pv2,pv3,pv25537], .c 3,
  .p pv2 [pv2,pv241,pv2861], .c 5, .c 3, .c 541, .c 23, .c 3, .c 5, .p pv31 [pv2,pv3,pv107,pv179],
  .c 3, .c 7, .c 17, .c 3, .c 13, .p pv2 [pv2,pv3,pv7,pv16417], .c 3, .c 71, .c 5, .c 3, .c 19,
  .c 479, .c 3, .c 5, .p pv13 [pv2,pv3,pv229841], .c 3, .c 467, .c 13, .c 3, .c 17, .c 11, .c 3,
  .c 7, .c 5, .c 3, .p pv2 [pv2,pv109,pv3163], .p pv31 [pv2,pv3,pv5,pv7,pv11,pv199], .c 3,
]
private theorem h0168c10 : checkBlock 1378819 128 b0168c10 = true := by
  decide +kernel

private def b0168c11 : List Row := [
  .c 5, .c 7, .c 3, .c 11, .c 151, .c 3, .c 521, .p pv7 [pv2,pv3,pv61,pv157], .c 3, .c 127, .c 5,
  .c 3, .p pv2 [pv2,pv7,pv98507], .c 37, .c 3, .c 5, .p pv5 [pv2,pv3,pv8513], .c 3,
  .p pv17 [pv2,pv5,pv137911], .c 53, .c 3, .c 41, .c 7, .c 3, .c 107, .c 5, .c 3,
  .p pv7 [pv2,pv31,pv67,pv83], .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv653], .c 3,
  .p pv2 [pv2,pv5,pv7,pv9851], .c 163, .c 3, .c 7, .c 23, .c 3, .c 19, .c 5, .c 3, .c 17, .c 7,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv53,pv4337], .c 3, .c 353, .p pv5 [pv2,pv3,pv19,pv23,pv263], .c 3,
  .c 109, .c 137, .c 3, .c 13, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 197, .c 3,
  .p pv3 [pv2,pv5,pv431], .c 7, .c 3, .p pv5 [pv2,pv689603], .c 13, .c 3, .c 11, .c 5, .c 3,
  .c 53, .c 31, .c 3, .c 5, .c 17, .c 3, .c 7, .c 89, .c 3, .p pv2 [pv2,pv499,pv691],
  .p pv7 [pv2,pv3,pv7,pv32839], .c 3, .c 59, .c 5, .c 3, .c 37, .p pv2 [pv2,pv3,pv5,pv613], .c 3,
  .c 5, .c 11, .c 3, .c 13, .p pv3 [pv2,pv3,pv47,pv67,pv73], .c 3, .c 19, .c 29, .c 3, .c 7, .c 5,
  .c 3, .c 11, .c 41, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv11,pv12539], .c 149, .c 3, .c 139,
  .c 131, .c 3, .c 1009, .c 5, .c 3, .c 47, .c 43, .c 3, .c 5, .c 71, .c 3,
  .p pv3 [pv2,pv5,pv34483], .c 11, .c 3, .c 29, .c 7,
]
private theorem h0168c11 : checkBlock 1379075 128 b0168c11 = true := by
  decide +kernel

private def b0168c12 : List Row := [
  .c 3, .c 23, .c 5, .c 3, .c 13, .c 337, .c 3, .c 5, .c 127, .c 3, .c 307,
  .p pv5 [pv2,pv3,pv13,pv4421], .c 3, .c 7, .p pv3 [pv2,pv3,pv76631], .c 3, .c 17, .c 5, .c 3,
  .p pv3 [pv2,pv172421], .c 7, .c 3, .c 5, .c 83, .c 3, .c 19, .p pv3 [pv2,pv3,pv229897], .c 3,
  .p pv2 [pv2,pv689693], .c 11, .c 3, .c 61, .c 5, .c 3, .c 7, .c 181, .c 3, .c 5, .c 31, .c 3,
  .c 11, .c 7, .c 3, .c 13, .c 19, .c 3, .p pv5 [pv2,pv11,pv62701], .c 5, .c 3, .c 281, .c 17,
  .c 3, .c 5, .c 97, .c 3, .c 7, .c 13, .c 3, .p pv5 [pv2,pv689723],
  .p pv31 [pv2,pv3,pv7,pv17,pv23], .c 3, .c 137, .c 5, .c 3, .c 71,
  .p pv11 [pv2,pv3,pv5,pv83,pv277], .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv6967], .c 3, .c 23,
  .p pv37 [pv2,pv3,pv29,pv991], .c 3, .c 11, .c 59, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv11,pv3919], .p pv7 [pv2,pv3,pv5,pv7,pv6569], .c 3, .c 5, .c 7, .c 3, .c 29,
  .p pv3 [pv2,pv3,pv173,pv443], .c 3, .c 661, .p pv7 [pv2,pv3,pv13,pv37,pv239], .c 3,
  .p pv3 [pv2,pv172439], .c 5, .c 3, .p pv13 [pv2,pv7,pv211,pv467], .c 11, .c 3, .c 5, .c 41,
  .c 3, .c 31, .c 17, .c 3, .c 53, .c 7, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv344887], .c 107,
  .c 3, .c 5, .c 409, .c 3, .c 131, .c 23, .c 3, .c 7, .c 43, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv689789], .c 7, .c 3, .c 5,
]
private theorem h0168c12 : checkBlock 1379331 128 b0168c12 = true := by
  decide +kernel

private def b0168c13 : List Row := [
  .c 11, .c 3, .c 47, .c 31, .c 3, .c 59, .c 13, .c 3, .p pv2 [pv2,pv7,pv98543], .c 5, .c 3, .c 7,
  .c 787, .c 3, .c 5, .c 29, .c 3, .p pv2 [pv2,pv5,pv11,pv6271], .c 7, .c 3, .c 73,
  .p pv17 [pv2,pv3,pv19,pv2017], .c 3, .p pv3 [pv2,pv23,pv163], .c 5, .c 3,
  .p pv7 [pv2,pv13,pv47,pv1129], .p pv11 [pv2,pv3,pv5,pv11497], .c 3, .c 5, .c 19, .c 3, .c 7,
  .c 11, .c 3, .p pv3 [pv2,pv37,pv59,pv79], .p pv7 [pv2,pv3,pv7,pv107,pv307], .c 3,
  .p pv5 [pv2,pv689831], .c 5, .c 3, .c 17, .c 487, .c 3, .c 5, .c 13, .c 3,
  .p pv3 [pv2,pv5,pv8623], .c 457, .c 3, .c 151, .c 557, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv43,pv61,pv263], .c 23, .c 3, .c 5, .c 7, .c 3, .c 607, .c 739, .c 3, .c 31, .c 11,
  .c 3, .c 19, .c 5, .c 3, .c 13, .c 67, .c 3, .c 5, .c 17, .c 3, .c 11, .c 71, .c 3, .c 23, .c 7,
  .c 3, .p pv3 [pv2,pv11,pv15679], .c 5, .c 3, .c 61, .c 19, .c 3, .c 5, .c 37, .c 3, .c 17,
  .c 41, .c 3, .c 7, .c 31, .c 3, .c 389, .c 5, .c 3, .c 653, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv10453], .c 3, .p pv3 [pv2,pv5,pv6899], .p pv2 [pv2,pv3,pv53,pv4339],
  .c 3, .c 11, .p pv11 [pv2,pv3,pv1597], .c 3, .p pv2 [pv2,pv7,pv49279], .c 5, .c 3, .c 7,
  .p pv41 [pv2,pv3,pv5,pv13,pv29,pv61], .c 3, .c 5, .c 43, .c 3, .c 109, .c 7, .c 3, .c 19, .c 17,
  .c 3,
]
private theorem h0168c13 : checkBlock 1379587 128 b0168c13 = true := by
  decide +kernel

private def b0168c14 : List Row := [
  .c 113, .c 5, .c 3, .c 29, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv19,pv89], .c 3, .c 7,
  .c 613, .c 3, .p pv2 [pv2,pv199,pv3467], .p pv19 [pv2,pv3,pv7,pv16427], .c 3, .c 11, .c 5, .c 3,
  .p pv7 [pv2,pv29,pv37,pv643], .c 61, .c 3, .c 5, .p pv5 [pv2,pv3,pv229981], .c 3, .c 103, .c 79,
  .c 3, .p pv3 [pv2,pv7,pv41,pv601], .c 509, .c 3, .c 7, .c 5, .c 3, .c 967, .c 13, .c 3, .c 5,
  .c 7, .c 3, .c 167, .p pv2 [pv2,pv3,pv97,pv2371], .c 3, .c 691, .p pv7 [pv2,pv3,pv11,pv5227],
  .c 3, .c 227, .c 5, .c 3, .c 11, .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv349,pv659], .c 3, .c 19,
  .p pv5 [pv2,pv3,pv7,pv37], .c 3, .p pv2 [pv2,pv43,pv71,pv113], .c 7, .c 3, .c 13, .c 5, .c 3,
  .p pv3 [pv2,pv10781], .c 433, .c 3, .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv7,pv9857], .c 11, .c 3,
  .c 7, .c 13, .c 3, .p pv3 [pv2,pv17,pv73,pv139], .c 5, .c 3, .c 43, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv76667], .c 3, .c 757, .p pv5 [pv2,pv3,pv115001], .c 3, .c 313, .c 41, .c 3,
  .c 23, .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv157,pv293], .c 3, .c 5, .c 587, .c 3, .c 13,
  .c 7, .c 3, .p pv5 [pv2,pv19,pv23,pv1579], .c 11, .c 3, .p pv3 [pv2,pv29,pv11897], .c 5, .c 3,
  .c 233, .c 47, .c 3, .c 5, .c 13, .c 3, .c 7, .c 641, .c 3, .c 17, .c 1069, .c 3,
  .p pv2 [pv2,pv11,pv62731], .c 5, .c 3, .c 31, .c 541, .c 3, .c 5, .c 103,
]
private theorem h0168c14 : checkBlock 1379843 128 b0168c14 = true := by
  decide +kernel

private def b0168c15 : List Row := [
  .c 3, .c 41, .c 19, .c 3, .c 571, .c 127, .c 3, .c 7, .c 5, .c 3, .c 13, .c 163, .c 3, .c 5,
  .c 7, .c 3, .c 139, .c 67, .c 3, .c 11, .c 29, .c 3, .c 193, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv11,pv4481], .c 31, .c 3, .c 5, .p pv5 [pv2,pv3,pv115013], .c 3, .c 23,
  .p pv3 [pv2,pv3,pv7,pv17,pv1933], .c 3, .c 1123, .c 7, .c 3, .c 53, .c 5, .c 3, .c 17, .c 11,
  .c 3, .c 5, .c 59, .c 3, .c 283, .c 107, .c 3, .c 7, .p pv7 [pv2,pv3,pv19,pv12107], .c 3, .c 11,
  .c 5, .c 3, .c 79, .c 7, .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv69011], .c 13, .c 3,
  .p pv2 [pv2,pv29,pv53,pv449], .c 617, .c 3, .p pv3 [pv2,pv7,pv503], .c 5, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv5,pv71], .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv5521], .c 7, .c 3, .c 43,
  .p pv2 [pv2,pv3,pv11,pv6971], .c 3, .c 827, .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv139,pv331],
  .c 3, .c 5, .p pv13 [pv2,pv3,pv23,pv1667], .c 3, .c 7, .p pv2 [pv2,pv3,pv230047], .c 3, .c 367,
  .p pv73 [pv2,pv3,pv7,pv13,pv79], .c 3, .c 19, .c 5, .c 3, .c 23, .c 13, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv31,pv41,pv181], .c 3, .c 71, .c 11, .c 3, .p pv3 [pv2,pv7,pv49297],
  .p pv3 [pv2,pv3,pv379,pv607], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv172541], .c 19, .c 3, .c 5,
  .c 7, .c 3, .p pv3 [pv2,pv5,pv13,pv5309], .c 43, .c 3, .c 41, .c 17, .c 3, .c 13,
]
private theorem h0168c15 : checkBlock 1380099 128 b0168c15 = true := by
  decide +kernel

private def b0168c16 : List Row := [
  .c 5, .c 3, .c 37, .c 1061, .c 3, .c 5, .c 79, .c 3, .c 29, .c 83, .c 3,
  .p pv3 [pv2,pv109,pv1583], .c 7, .c 3, .c 17, .c 5, .c 3, .p pv3 [pv2,pv19,pv41,pv443], .c 23,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv37,pv3109], .c 3, .c 11, .c 677, .c 3, .c 7, .c 139, .c 3, .c 859,
  .c 5, .c 3, .p pv2 [pv2,pv13,pv53093], .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv19,pv12109], .c 3,
  .c 13, .c 37, .c 3, .c 23, .p pv3 [pv2,pv3,pv53,pv1447], .c 3, .p pv7 [pv2,pv7,pv151,pv653],
  .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 13, .c 3, .c 31, .c 7, .c 3, .c 11,
  .p pv29 [pv2,pv3,pv17,pv67,pv101], .c 3, .c 373, .c 5, .c 3, .c 89, .c 1163, .c 3, .c 5, .c 29,
  .c 3, .c 7, .c 431, .c 3, .c 601, .p pv29 [pv2,pv3,pv7,pv32869], .c 3, .c 73, .c 5, .c 3, .c 13,
  .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv29,pv3967], .c 3, .c 19, .c 31, .c 3, .c 881, .c 23, .c 3,
  .c 7, .c 5, .c 3, .c 83, .c 59, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv27611], .c 17, .c 3,
  .p pv2 [pv2,pv345139], .c 19, .c 3, .p pv2 [pv2,pv690281], .c 5, .c 3, .c 101,
  .p pv3 [pv2,pv3,pv5,pv17,pv2707], .c 3, .c 5, .c 11, .c 3, .c 37, .c 353, .c 3, .c 13, .c 7,
  .c 3, .c 41, .c 5, .c 3, .c 11, .c 43, .c 3, .c 5, .p pv5 [pv2,pv3,pv230101], .c 3,
]
private theorem h0168c16 : checkBlock 1380355 128 b0168c16 = true := by
  decide +kernel

private def b0168c17 : List Row := [
  .p pv7 [pv2,pv5,pv7,pv11,pv163], .c 13, .c 3, .c 7, .p pv2 [pv2,pv3,pv37,pv691], .c 3,
  .p pv5 [pv2,pv83,pv8317], .c 5, .c 3, .p pv2 [pv2,pv547,pv631], .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv38351], .c 3, .c 229, .c 11, .c 3, .c 31, .c 73, .c 3,
  .p pv2 [pv2,pv7,pv13,pv3793], .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .c 23, .c 3,
  .p pv13 [pv2,pv5,pv101,pv1367], .c 7, .c 3, .p pv2 [pv2,pv11,pv31379],
  .p pv19 [pv2,pv3,pv13,pv31,pv571], .c 3, .c 79, .c 5, .c 3, .c 17, .c 13, .c 3, .c 5, .c 379,
  .c 3, .c 7, .c 53, .c 3, .p pv2 [pv2,pv17,pv40609], .c 11, .c 3, .c 23, .c 5, .c 3, .c 29,
  .p pv31 [pv2,pv3,pv5,pv11,pv523], .c 3, .c 5, .p pv3 [pv2,pv3,pv947], .c 3, .c 11, .c 499, .c 3,
  .c 71, .c 191, .c 3, .c 7, .c 5, .c 3, .c 19, .c 251, .c 3, .c 5, .c 7, .c 3, .c 577,
  .p pv2 [pv2,pv3,pv79,pv971], .c 3, .c 1129, .c 13, .c 3, .c 43, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv98627], .p pv2 [pv2,pv3,pv5,pv2557], .c 3, .c 5, .c 19, .c 3, .c 17,
  .p pv5 [pv2,pv3,pv7,pv8219], .c 3, .c 11, .c 7, .c 3, .c 37, .c 5, .c 3, .c 53,
  .p pv2 [pv2,pv3,pv5,pv46027], .c 3, .c 5, .p pv5 [pv2,pv3,pv43,pv223], .c 3, .c 13, .c 137,
  .c 3, .c 7, .c 661, .c 3, .c 31, .c 5, .c 3, .c 41, .c 7, .c 3, .c 5, .c 13, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv11,pv317], .c 3, .c 61, .c 17, .c 3, .c 11, .c 5,
]
private theorem h0168c17 : checkBlock 1380611 128 b0168c17 = true := by
  decide +kernel

private def b0168c18 : List Row := [
  .c 3, .c 7, .c 83, .c 3, .c 5, .c 37, .c 3, .p pv3 [pv2,pv5,pv41,pv421], .c 7, .c 3,
  .p pv5 [pv2,pv13,pv173,pv307], .p pv7 [pv2,pv3,pv2131], .c 3, .c 17, .c 5, .c 3, .c 13, .c 19,
  .c 3, .c 5, .c 11, .c 3, .c 7, .p pv17 [pv2,pv3,pv13,pv2213], .c 3, .c 509, .c 467, .c 3,
  .c 167, .c 5, .c 3, .c 11, .p pv19 [pv2,pv3,pv5,pv191,pv241], .c 3, .c 5, .c 67, .c 3, .c 73,
  .c 23, .c 3, .p pv2 [pv2,pv7,pv98639], .p pv17 [pv2,pv3,pv115079], .c 3, .c 7, .c 5, .c 3,
  .p pv13 [pv2,pv19,pv36341], .c 17, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv197,pv701], .c 11,
  .c 3, .c 13, .c 61, .c 3, .p pv5 [pv2,pv690491], .c 5, .c 3, .c 23, .c 233, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv19,pv673], .c 3, .c 47, .c 13, .c 3, .c 853, .c 7, .c 3, .c 59, .c 5, .c 3,
  .c 31, .c 53, .c 3, .c 5, .p pv2 [pv2,pv3,pv337,pv683], .c 3, .c 43, .p pv7 [pv2,pv3,pv19181],
  .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv13,pv53117], .c 5, .c 3, .c 107, .c 7, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv7193], .c 3, .c 11, .c 17, .c 3, .c 29, .p pv2 [pv2,pv3,pv13,pv227], .c 3,
  .c 359, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 73, .c 3, .c 19, .c 7, .c 3, .c 17, .c 37, .c 3,
  .p pv5 [pv2,pv89,pv7759], .c 5, .c 3, .p pv2 [pv2,pv193,pv1789],
  .p pv7 [pv2,pv3,pv5,pv19,pv2423], .c 3, .c 5, .c 43, .c 3, .c 7,
]
private theorem h0168c18 : checkBlock 1380867 128 b0168c18 = true := by
  decide +kernel

private def b0168c19 : List Row := [
  .c 1097, .c 3, .c 11, .c 19, .c 3, .c 13, .c 5, .c 3, .c 109, .p pv2 [pv2,pv3,pv5,pv7673], .c 3,
  .c 5, .p pv2 [pv2,pv3,pv13,pv17707], .c 3, .c 311, .p pv5 [pv2,pv3,pv14387], .c 3, .c 79, .c 13,
  .c 3, .c 7, .c 5, .c 3, .c 317, .c 11, .c 3, .c 5, .c 7, .c 3, .c 239, .c 29, .c 3,
  .p pv2 [pv2,pv19,pv1913], .c 47, .c 3, .c 11, .c 5, .c 3, .c 17, .c 797, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv211,pv1091], .c 3, .c 13, .p pv2 [pv2,pv3,pv7,pv29], .c 3,
  .p pv3 [pv2,pv17,pv2539], .c 7, .c 3, .c 61, .c 5, .c 3, .p pv2 [pv2,pv345307],
  .p pv11 [pv2,pv3,pv5,pv103,pv149], .c 3, .c 5, .c 11, .c 3, .c 29, .c 19, .c 3, .c 7, .c 41,
  .c 3, .c 251, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 17, .c 3,
  .p pv11 [pv2,pv5,pv11,pv29,pv433], .p pv7 [pv2,pv3,pv67,pv859], .c 3,
  .p pv2 [pv2,pv13,pv101,pv263], .p pv3 [pv2,pv3,pv230213], .c 3, .c 47, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv41,pv1123], .c 3, .c 5, .p pv13 [pv2,pv3,pv7,pv4111], .c 3, .c 17, .c 7,
  .c 3, .p pv2 [pv2,pv73,pv9461], .c 691, .c 3, .p pv3 [pv2,pv113,pv191], .c 5, .c 3, .c 19,
  .c 37, .c 3, .c 5, .p pv3 [pv2,pv3,pv230221], .c 3, .c 7, .c 103, .c 3,
  .p pv3 [pv2,pv11,pv1427], .c 53, .c 3, .c 179, .c 5, .c 3, .p pv2 [pv2,pv151,pv2287], .c 773,
  .c 3, .c 5, .c 19, .c 3, .c 907, .c 337, .c 3, .c 13, .c 11, .c 3, .c 7, .c 5, .c 3,
]
private theorem h0168c19 : checkBlock 1381123 128 b0168c19 = true := by
  decide +kernel

private def b0168c20 : List Row := [
  .c 73, .p pv2 [pv2,pv3,pv5,pv7,pv11,pv13,pv23], .c 3, .c 5, .c 7, .c 3, .c 11, .c 13, .c 3,
  .p pv2 [pv2,pv281,pv1229], .c 277, .c 3, .c 17, .c 5, .c 3, .p pv3 [pv2,pv7,pv881],
  .p pv3 [pv2,pv3,pv5,pv15349], .c 3, .c 5, .c 211, .c 3, .p pv2 [pv2,pv5,pv17,pv239], .c 929,
  .c 3, .p pv2 [pv2,pv23,pv59,pv509], .c 7, .c 3, .c 19, .c 5, .c 3, .p pv11 [pv2,pv690719],
  .p pv7 [pv2,pv3,pv5,pv1439], .c 3, .c 5, .c 71, .c 3, .p pv2 [pv2,pv5,pv7,pv3947], .c 31, .c 3,
  .c 7, .p pv3 [pv2,pv3,pv13,pv89,pv199], .c 3, .c 617, .c 5, .c 3, .c 37, .c 7, .c 3, .c 5,
  .c 107, .c 3, .c 383, .p pv5 [pv2,pv3,pv25583], .c 3, .p pv5 [pv2,pv317,pv2179],
  .p pv11 [pv2,pv3,pv17,pv1693], .c 3, .p pv2 [pv2,pv7,pv49339], .c 5, .c 3, .c 7, .c 11, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv7,pv37,pv127], .c 3, .c 457, .c 7, .c 3, .p pv2 [pv2,pv345379],
  .p pv23 [pv2,pv3,pv23,pv47,pv71], .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv19,pv61,pv149], .c 29,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv41], .c 3, .c 7, .c 37, .c 3, .c 19, .c 13, .c 3,
  .p pv3 [pv2,pv79,pv1093], .c 5, .c 3, .p pv7 [pv2,pv271,pv2549], .c 197, .c 3, .c 5, .c 11,
  .c 3, .c 97, .c 17, .c 3, .c 31, .c 101, .c 3, .c 7, .c 5, .c 3, .c 11, .c 167, .c 3, .c 5,
  .c 7, .c 3, .c 13, .c 59, .c 3, .c 17, .p pv7 [pv2,pv3,pv31,pv619], .c 3,
  .p pv2 [pv2,pv47,pv7349], .c 5, .c 3, .c 487, .p pv7 [pv2,pv3,pv5,pv23027], .c 3, .c 5, .c 13,
  .c 3, .c 79, .c 11,
]
private theorem h0168c20 : checkBlock 1381379 128 b0168c20 = true := by
  decide +kernel

private def b0168c21 : List Row := [
  .c 3, .p pv2 [pv2,pv89,pv3881], .c 7, .c 3, .p pv2 [pv2,pv19,pv103,pv353], .c 5, .c 3,
  .p pv3 [pv2,pv86353], .c 113, .c 3, .c 5, .c 53, .c 3, .c 19, .c 863, .c 3, .c 7, .c 673, .c 3,
  .c 947, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 193, .c 3, .c 37,
  .p pv2 [pv2,pv3,pv13,pv17,pv521], .c 3, .p pv3 [pv2,pv21589], .c 11, .c 3, .c 433, .c 5, .c 3,
  .c 7, .c 61, .c 3, .c 5, .c 443, .c 3, .c 11, .c 7, .c 3, .p pv5 [pv2,pv17,pv40639], .c 1117,
  .c 3, .c 971, .c 5, .c 3, .p pv2 [pv2,pv690869], .c 41, .c 3, .c 5, .p pv2 [pv2,pv3,pv230291],
  .c 3, .c 7, .c 47, .c 3, .c 13, .p pv11 [pv2,pv3,pv7,pv167,pv197], .c 3, .c 29, .c 5, .c 3,
  .p pv3 [pv2,pv172721], .c 23, .c 3, .c 5, .c 17, .c 3, .c 101, .c 13, .c 3, .c 11, .c 79, .c 3,
  .c 7, .c 5, .c 3, .c 139, .c 151, .c 3, .c 5, .c 7, .c 3, .c 17, .c 19, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv230303], .c 3, .c 41, .c 5, .c 3, .c 271, .c 11, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv115153], .c 3, .c 709, .c 967, .c 3, .c 47, .c 7, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv690929], .c 13, .c 3, .c 5, .c 83, .c 3, .p pv7 [pv2,pv5,pv7,pv19,pv1039], .c 71,
  .c 3, .c 7, .c 17, .c 3, .p pv2 [pv2,pv101,pv6841], .c 5, .c 3, .c 19,
]
private theorem h0168c21 : checkBlock 1381635 128 b0168c21 = true := by
  decide +kernel

private def b0168c22 : List Row := [
  .c 7, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv13,pv1063], .c 89, .c 3, .p pv2 [pv2,pv690953],
  .c 23, .c 3, .c 13, .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv2879], .c 3, .c 5, .c 19, .c 3,
  .c 223, .c 7, .c 3, .c 29, .c 13, .c 3, .c 829, .c 5, .c 3, .c 31, .c 103, .c 3, .c 5, .c 59,
  .c 3, .c 7, .c 11, .c 3, .p pv5 [pv2,pv29,pv23827], .p pv17 [pv2,pv3,pv7,pv457], .c 3,
  .p pv2 [pv2,pv439,pv787], .c 5, .c 3, .p pv7 [pv2,pv13,pv23,pv2311], .c 17, .c 3, .c 5, .c 37,
  .c 3, .c 13, .p pv5 [pv2,pv3,pv89,pv647], .c 3, .p pv2 [pv2,pv7,pv11,pv641],
  .p pv11 [pv2,pv3,pv17,pv797], .c 3, .c 7, .c 5, .c 3, .c 67, .c 31, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv43,pv1607], .p pv5 [pv2,pv3,pv19,pv449], .c 3, .c 727, .c 11, .c 3, .c 83,
  .c 5, .c 3, .p pv7 [pv2,pv7,pv98717], .c 19, .c 3, .c 5, .c 23, .c 3, .c 11, .c 29, .c 3,
  .p pv3 [pv2,pv13,pv97,pv137], .c 7, .c 3, .c 43, .c 5, .c 3, .c 13, .c 157, .c 3, .c 5, .c 61,
  .c 3, .c 53, .c 17, .c 3, .c 7, .p pv19 [pv2,pv3,pv57587], .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv19,pv37,pv983], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv43,pv487], .c 3, .c 29,
  .p pv5 [pv2,pv3,pv4799], .c 3, .c 11, .c 107, .c 3, .p pv2 [pv2,pv7,pv269,pv367], .c 5, .c 3,
  .c 7, .c 859, .c 3, .c 5, .c 239, .c 3, .c 127, .c 7, .c 3,
]
private theorem h0168c22 : checkBlock 1381891 128 b0168c22 = true := by
  decide +kernel

private def b0168c23 : List Row := [
  .c 13, .c 43, .c 3, .c 97, .c 5, .c 3, .p pv7 [pv2,pv691079], .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv31,pv2477], .c 3, .c 7, .c 13, .c 3, .p pv3 [pv2,pv47,pv919],
  .p pv2 [pv2,pv3,pv7,pv32909], .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv345547],
  .p pv3 [pv2,pv3,pv5,pv46073], .c 3, .c 5, .c 31, .c 3, .p pv3 [pv2,pv5,pv6911], .c 227, .c 3,
  .p pv5 [pv2,pv7,pv98729], .c 37, .c 3, .c 7, .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv7,pv1097],
  .c 3, .c 5, .c 7, .c 3, .c 19, .c 41, .c 3, .p pv2 [pv2,pv17,pv20327], .c 281, .c 3,
  .p pv2 [pv2,pv691121], .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 251, .c 3, .c 211, .c 79, .c 3,
  .c 191, .c 7, .c 3, .c 149, .c 5, .c 3, .p pv13 [pv2,pv43,pv16073], .c 419, .c 3, .c 5, .c 17,
  .c 3, .p pv2 [pv2,pv5,pv7,pv13,pv31], .c 11, .c 3, .c 7, .c 71, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv345577], .c 7, .c 3, .c 5, .c 47, .c 3, .c 17, .c 23, .c 3,
  .p pv5 [pv2,pv11,pv19,pv3307], .c 13, .c 3, .c 107, .c 5, .c 3, .c 7, .c 857, .c 3, .c 5, .c 97,
  .c 3, .c 1151, .c 7, .c 3, .c 37, .c 11, .c 3, .c 103, .c 5, .c 3, .c 23, .c 271, .c 3, .c 5,
  .c 223, .c 3, .c 7, .c 19, .c 3, .c 101, .c 17, .c 3, .p pv3 [pv2,pv11,pv23,pv683], .c 5, .c 3,
  .c 53, .c 29,
]
private theorem h0168c23 : checkBlock 1382147 128 b0168c23 = true := by
  decide +kernel

private def b0168c24 : List Row := [
  .c 3, .c 5, .c 13, .c 3, .c 47, .c 1123, .c 3, .c 179, .p pv3 [pv2,pv3,pv76801], .c 3, .c 7,
  .c 5, .c 3, .c 59, .c 37, .c 3, .c 5, .c 7, .c 3, .c 71, .c 61, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv83,pv347], .c 3, .c 199, .c 5, .c 3, .c 13, .c 23, .c 3, .c 5, .c 137, .c 3,
  .c 449, .c 229, .c 3, .p pv2 [pv2,pv31,pv11149], .c 7, .c 3, .c 1061, .c 5, .c 3, .c 367, .c 11,
  .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv7,pv79], .p pv3 [pv2,pv3,pv11,pv20947], .c 3, .c 7,
  .c 359, .c 3, .c 11, .c 5, .c 3, .p pv13 [pv2,pv463,pv1493], .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv89,pv863], .c 3, .c 83, .p pv5 [pv2,pv3,pv115211], .c 3, .c 13, .c 461, .c 3,
  .p pv5 [pv2,pv7,pv17,pv37,pv157], .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv13,pv709], .c 3, .c 5,
  .c 11, .c 3, .c 41, .c 7, .c 3, .p pv5 [pv2,pv163,pv4241], .c 31, .c 3, .c 19, .c 5, .c 3,
  .c 11, .c 809, .c 3, .c 5, .c 331, .c 3, .c 7, .c 17, .c 3, .p pv2 [pv2,pv179,pv1931], .c 23,
  .c 3, .c 443, .c 5, .c 3, .p pv3 [pv2,pv86413], .c 19, .c 3, .c 5, .c 241, .c 3,
  .p pv2 [pv2,pv5,pv73,pv947], .c 11, .c 3, .c 17, .p pv7 [pv2,pv3,pv13,pv8863], .c 3, .c 7, .c 5,
  .c 3, .c 647, .c 13, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv27653], .c 37, .c 3, .c 227,
]
private theorem h0168c24 : checkBlock 1382403 128 b0168c24 = true := by
  decide +kernel

private def b0168c25 : List Row := [
  .c 181, .c 3, .p pv5 [pv2,pv29,pv31,pv769], .c 5, .c 3, .c 739, .p pv3 [pv2,pv3,pv5,pv569],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv115223], .c 3, .p pv3 [pv2,pv5,pv13,pv2659], .c 211, .c 3, .c 19,
  .c 7, .c 3, .c 13, .c 5, .c 3, .c 157, .c 353, .c 3, .c 5, .c 151, .c 3, .c 11, .c 853, .c 3,
  .c 7, .c 13, .c 3, .c 743, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 23, .c 3, .c 137, .c 197,
  .c 3, .c 503, .c 29, .c 3, .p pv3 [pv2,pv7,pv6173], .c 5, .c 3, .c 7, .c 107, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv11,pv41,pv73], .c 3, .c 13, .c 7, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv29,pv883], .c 3, .c 23, .c 5, .c 3, .c 173, .c 101, .c 3, .c 5, .c 13, .c 3,
  .c 7, .c 953, .c 3, .c 29, .c 61, .c 3, .c 67, .c 5, .c 3, .p pv2 [pv2,pv691409], .c 11, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv230471], .c 3, .c 17, .c 887, .c 3, .c 43, .c 19, .c 3, .c 7, .c 5,
  .c 3, .c 13, .c 199, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv69143], .c 83, .c 3, .c 71,
  .c 149, .c 3, .c 479, .c 5, .c 3, .c 31, .c 47, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv138289], .p pv5 [pv2,pv3,pv7,pv101,pv163], .c 3, .c 773, .c 7, .c 3, .c 127,
  .c 5, .c 3, .c 11, .c 139, .c 3,
]
private theorem h0168c25 : checkBlock 1382659 128 b0168c25 = true := by
  decide +kernel

private def b0168c26 : List Row := [
  .c 5, .c 257, .c 3, .c 23, .c 29, .c 3, .c 7, .c 53, .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv71,pv9739], .c 7, .c 3, .c 5, .c 67, .c 3, .c 1171, .c 11, .c 3,
  .p pv2 [pv2,pv345739], .p pv3 [pv2,pv3,pv76831], .c 3, .c 1063, .c 5, .c 3, .c 7, .c 41, .c 3,
  .c 5, .p pv17 [pv2,pv3,pv7], .c 3, .c 29, .c 7, .c 3, .p pv5 [pv2,pv11,pv37,pv1699],
  .p pv2 [pv2,pv3,pv115249], .c 3, .c 101, .c 5, .c 3, .p pv7 [pv2,pv691499], .c 17, .c 3, .c 5,
  .c 113, .c 3, .c 7, .c 23, .c 3, .c 311, .c 11, .c 3, .c 37, .c 5, .c 3, .c 19, .c 13, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv23,pv5011], .c 3, .c 11, .p pv3 [pv2,pv3,pv230507], .c 3,
  .p pv5 [pv2,pv7,pv223,pv443], .c 401, .c 3, .c 7, .c 5, .c 3, .c 23, .c 277, .c 3, .c 5, .c 7,
  .c 3, .c 317, .c 701, .c 3, .p pv2 [pv2,pv345769], .c 431, .c 3, .c 13, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv53,pv233], .c 599, .c 3, .c 5, .c 29, .c 3, .c 109, .c 17, .c 3, .c 11, .c 7,
  .c 3, .p pv3 [pv2,pv83,pv2083], .c 5, .c 3, .c 419, .p pv59 [pv2,pv3,pv5,pv17,pv113], .c 3,
  .c 5, .c 31, .c 3, .c 73, .c 179, .c 3, .c 7, .p pv2 [pv2,pv3,pv43,pv1787], .c 3, .c 19, .c 5,
  .c 3, .c 89, .c 7, .c 3, .c 5, .c 127, .c 3, .c 13, .c 47, .c 3, .c 149,
  .p pv11 [pv2,pv3,pv1801],
]
private theorem h0168c26 : checkBlock 1382915 128 b0168c26 = true := by
  decide +kernel

private def b0168c27 : List Row := [
  .c 3, .c 11, .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 13, .c 3, .p pv17 [pv2,pv5,pv138319], .c 7,
  .c 3, .c 23, .p pv3 [pv2,pv3,pv269,pv857], .c 3, .p pv2 [pv2,pv181,pv3821], .c 5, .c 3,
  .p pv3 [pv2,pv37,pv4673], .c 79, .c 3, .c 5, .c 11, .c 3, .c 7, .c 367, .c 3, .c 359, .c 131,
  .c 3, .c 113, .c 5, .c 3, .c 11, .c 659, .c 3, .c 5, .c 53, .c 3, .c 31, .c 293, .c 3, .c 19,
  .c 709, .c 3, .c 7, .c 5, .c 3, .c 223, .c 29, .c 3, .c 5, .c 7, .c 3, .c 929, .c 11, .c 3,
  .p pv5 [pv2,pv647,pv1069], .c 23, .c 3, .c 71, .c 5, .c 3, .c 41,
  .p pv7 [pv2,pv3,pv5,pv29,pv53], .c 3, .c 5, .c 17, .c 3, .c 151, .c 31, .c 3, .c 13, .c 7, .c 3,
  .p pv2 [pv2,pv691661], .c 5, .c 3, .c 29, .p pv29 [pv2,pv3,pv5,pv13,pv3547], .c 3, .c 5, .c 541,
  .c 3, .c 17, .c 13, .c 3, .c 7, .c 11, .c 3, .c 43, .c 5, .c 3,
  .p pv19 [pv2,pv17,pv23,pv29,pv61], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv230561], .c 3, .c 11,
  .c 59, .c 3, .p pv3 [pv2,pv86461], .p pv2 [pv2,pv3,pv230563], .c 3, .c 181, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv19,pv809], .c 3, .c 5, .c 101, .c 3, .p pv7 [pv2,pv5,pv6917], .c 7, .c 3,
  .c 353, .c 17, .c 3, .c 191, .c 5, .c 3, .c 61, .c 13, .c 3, .c 5,
]
private theorem h0168c27 : checkBlock 1383171 128 b0168c27 = true := by
  decide +kernel

private def b0168c28 : List Row := [
  .c 23, .c 3, .c 7, .p pv11 [pv2,pv3,pv59,pv977], .c 3, .c 11, .c 43, .c 3, .c 17, .c 5, .c 3,
  .p pv13 [pv2,pv11,pv79,pv199], .p pv31 [pv2,pv3,pv5,pv23,pv401], .c 3, .c 5, .c 373, .c 3,
  .c 461, .c 41, .c 3, .c 37, .c 593, .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv691739], .c 11, .c 3,
  .c 5, .c 7, .c 3, .c 59, .p pv2 [pv2,pv3,pv11,pv47,pv223], .c 3, .p pv3 [pv2,pv23,pv73,pv103],
  .c 13, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv7,pv49411], .c 17, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv38431], .c 3, .p pv3 [pv2,pv5,pv8647], .c 19, .c 3, .c 79, .c 7, .c 3, .c 571,
  .c 5, .c 3, .c 47, .c 37, .c 3, .c 5, .c 11, .c 3, .c 13, .p pv5 [pv2,pv3,pv1201], .c 3, .c 7,
  .c 587, .c 3, .c 137, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 13, .c 3, .c 241,
  .p pv13 [pv2,pv3,pv230597], .c 3, .c 283, .p pv2 [pv2,pv3,pv23,pv557], .c 3,
  .p pv3 [pv2,pv7,pv31,pv797], .c 5, .c 3, .c 7, .c 829, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv79,pv139], .c 3, .c 23, .c 7, .c 3, .c 67, .c 29, .c 3, .c 31, .c 5, .c 3,
  .c 13, .c 1049, .c 3, .c 5, .c 19, .c 3, .c 7, .c 263, .c 3, .c 17, .c 307, .c 3,
  .p pv2 [pv2,pv37,pv9349], .c 5, .c 3, .p pv2 [pv2,pv691829], .c 883, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv230611], .c 3, .c 53, .c 389, .c 3, .c 29, .c 11, .c 3,
]
private theorem h0168c28 : checkBlock 1383427 128 b0168c28 = true := by
  decide +kernel

private def b0168c29 : List Row := [
  .c 7, .c 5, .c 3, .c 37, .p pv3 [pv2,pv3,pv5,pv7,pv11,pv599], .c 3, .c 5, .c 7, .c 3, .c 11,
  .c 23, .c 3, .c 13, .c 41, .c 3, .c 19, .c 5, .c 3, .c 71, .c 467, .c 3, .c 5, .c 47, .c 3,
  .p pv2 [pv2,pv5,pv138373], .c 13, .c 3, .p pv3 [pv2,pv269,pv643], .c 7, .c 3,
  .p pv5 [pv2,pv691871], .c 5, .c 3, .c 17, .c 19, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv953], .c 3,
  .p pv3 [pv2,pv5,pv7,pv353], .c 37, .c 3, .c 7, .p pv11 [pv2,pv3,pv19219], .c 3, .c 313, .c 5,
  .c 3, .c 383, .c 7, .c 3, .c 5, .c 233, .c 3, .c 41, .c 29, .c 3, .p pv2 [pv2,pv457,pv757],
  .p pv3 [pv2,pv3,pv13,pv113,pv157], .c 3, .p pv2 [pv2,pv7,pv97,pv1019], .c 5, .c 3, .c 7, .c 11,
  .c 3, .c 5, .c 17, .c 3, .c 47, .c 7, .c 3, .c 19, .p pv2 [pv2,pv3,pv115319], .c 3, .c 11, .c 5,
  .c 3, .c 293, .c 23, .c 3, .c 5, .c 229, .c 3, .c 7, .p pv2 [pv2,pv3,pv115321], .c 3,
  .p pv3 [pv2,pv86491], .c 83, .c 3, .c 13, .c 5, .c 3, .c 43, .c 31, .c 3, .c 5, .c 11, .c 3,
  .p pv3 [pv2,pv5,pv29,pv1193], .c 53, .c 3, .c 23, .c 13, .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv7,pv659], .c 3, .c 5, .c 7, .c 3, .c 37, .p pv5 [pv2,pv3,pv43,pv149],
  .c 3, .p pv2 [pv2,pv345979], .c 17, .c 3, .p pv2 [pv2,pv19,pv79,pv461], .c 5, .c 3, .c 167,
  .c 617, .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv53],
]
private theorem h0168c29 : checkBlock 1383683 128 b0168c29 = true := by
  decide +kernel

private def b0168c30 : List Row := [
  .c 3, .c 13, .c 11, .c 3, .p pv2 [pv2,pv691973], .c 7, .c 3, .c 17, .c 5, .c 3,
  .p pv11 [pv2,pv691979], .p pv7 [pv2,pv3,pv5,pv19,pv607], .c 3, .c 5, .c 13, .c 3, .c 509,
  .c 109, .c 3, .c 7, .c 19, .c 3, .p pv5 [pv2,pv691991], .c 5, .c 3, .c 53, .c 7, .c 3, .c 5,
  .c 271, .c 3, .c 79, .c 71, .c 3, .c 73, .c 11, .c 3, .p pv3 [pv2,pv7,pv49429], .c 5, .c 3,
  .c 7, .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv31,pv1063], .c 3, .c 11, .c 7, .c 3, .c 41,
  .c 89, .c 3, .p pv2 [pv2,pv11,pv53,pv1187], .c 5, .c 3, .c 239, .c 881, .c 3, .c 5, .c 31, .c 3,
  .c 7, .c 241, .c 3, .p pv2 [pv2,pv151,pv4583], .p pv2 [pv2,pv3,pv7,pv16477], .c 3, .c 691, .c 5,
  .c 3, .p pv7 [pv2,pv41,pv16879], .c 59, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv67,pv313], .c 3,
  .p pv2 [pv2,pv5,pv61,pv2269], .c 19, .c 3, .c 11, .p pv2 [pv2,pv3,pv230683], .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv11,pv83,pv379], .c 137, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv34603],
  .c 13, .c 3, .c 43, .c 491, .c 3, .c 37, .c 5, .c 3, .p pv2 [pv2,pv7,pv98867], .c 11, .c 3,
  .c 5, .c 739, .c 3, .c 61, .c 67, .c 3, .c 17, .c 7, .c 3, .c 11, .c 5, .c 3, .c 19,
  .p pv17 [pv2,pv3,pv5,pv29,pv37,pv43], .c 3, .c 5, .c 191, .c 3, .c 31, .c 347, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv13,pv19,pv467], .c 3, .p pv3 [pv2,pv5407],
]
private theorem h0168c30 : checkBlock 1383939 128 b0168c30 = true := by
  decide +kernel

private def b0168c31 : List Row := [
  .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .c 11, .c 3, .c 941, .c 43, .c 3, .c 89,
  .p pv2 [pv2,pv3,pv11,pv6991], .c 3, .c 577, .c 5, .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv46141],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv1831], .c 3, .p pv3 [pv2,pv5,pv11,pv13], .c 7, .c 3,
  .p pv5 [pv2,pv227,pv3049], .p pv17 [pv2,pv3,pv137,pv421], .c 3, .c 13, .c 5, .c 3, .c 17,
  .c 311, .c 3, .c 5, .c 449, .c 3, .c 7, .c 11, .c 3, .c 131, .c 13, .c 3, .c 19, .c 5, .c 3,
  .c 599, .c 47, .c 3, .c 5, .c 521, .c 3, .c 23, .p pv19 [pv2,pv3,pv19,pv12143], .c 3, .c 53,
  .p pv7 [pv2,pv3,pv38453], .c 3, .c 7, .c 5, .c 3, .c 197, .c 19, .c 3, .c 5, .c 7, .c 3, .c 13,
  .c 787, .c 3, .p pv3 [pv2,pv31,pv2791], .c 11, .c 3, .p pv5 [pv2,pv43,pv16097], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv1009], .p pv11 [pv2,pv3,pv5,pv11,pv839], .c 3, .c 5, .c 13, .c 3, .c 11,
  .c 113, .c 3, .c 31, .c 7, .c 3, .c 29, .c 5, .c 3, .c 643, .c 523, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv179,pv1289], .c 3, .p pv13 [pv2,pv5,pv7,pv19777], .c 23, .c 3, .c 7, .c 313,
  .c 3, .p pv2 [pv2,pv29,pv23869], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 563, .c 3, .c 67,
  .c 103, .c 3, .c 11, .c 17, .c 3, .p pv3 [pv2,pv7,pv47,pv263], .c 5, .c 3, .c 7, .c 683, .c 3,
  .c 5, .c 41, .c 3,
]
private theorem h0168c31 : checkBlock 1384195 128 b0168c31 = true := by
  decide +kernel

def rows0168 : List Row :=
  b0168c00 ++ b0168c01 ++ b0168c02 ++ b0168c03 ++ b0168c04 ++ b0168c05 ++ b0168c06 ++ b0168c07 ++
  b0168c08 ++ b0168c09 ++ b0168c10 ++ b0168c11 ++ b0168c12 ++ b0168c13 ++ b0168c14 ++ b0168c15 ++
  b0168c16 ++ b0168c17 ++ b0168c18 ++ b0168c19 ++ b0168c20 ++ b0168c21 ++ b0168c22 ++ b0168c23 ++
  b0168c24 ++ b0168c25 ++ b0168c26 ++ b0168c27 ++ b0168c28 ++ b0168c29 ++ b0168c30 ++ b0168c31

attribute [local irreducible] checkBlock checkRows checkPrime

theorem checked0168 : checkBlock 1376259 4096 rows0168 = true :=
  checkBlock_append h0168c00 (
    checkBlock_append h0168c01 (
    checkBlock_append h0168c02 (
    checkBlock_append h0168c03 (
    checkBlock_append h0168c04 (
    checkBlock_append h0168c05 (
    checkBlock_append h0168c06 (
    checkBlock_append h0168c07 (
    checkBlock_append h0168c08 (
    checkBlock_append h0168c09 (
    checkBlock_append h0168c10 (
    checkBlock_append h0168c11 (
    checkBlock_append h0168c12 (
    checkBlock_append h0168c13 (
    checkBlock_append h0168c14 (
    checkBlock_append h0168c15 (
    checkBlock_append h0168c16 (
    checkBlock_append h0168c17 (
    checkBlock_append h0168c18 (
    checkBlock_append h0168c19 (
    checkBlock_append h0168c20 (
    checkBlock_append h0168c21 (
    checkBlock_append h0168c22 (
    checkBlock_append h0168c23 (
    checkBlock_append h0168c24 (
    checkBlock_append h0168c25 (
    checkBlock_append h0168c26 (
    checkBlock_append h0168c27 (
    checkBlock_append h0168c28 (
    checkBlock_append h0168c29 (
    checkBlock_append h0168c30 (
    h0168c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
