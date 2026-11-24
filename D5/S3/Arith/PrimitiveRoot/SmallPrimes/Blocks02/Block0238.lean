/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks02/Block0238
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks02/Block0238.checked0238
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table023
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table026
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table029
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table034
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table040
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table050
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table064
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table089
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table137

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0238c00 : List Row := [
  .c 29, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv43,pv229], .c 3, .c 53, .c 17, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv324953], .c 3, .c 19, .c 5, .c 3, .c 359, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv81239], .c 3, .p pv2 [pv2,pv5,pv13,pv7499], .c 61, .c 3, .c 17, .c 43, .c 3,
  .c 13, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 67, .c 3, .p pv2 [pv2,pv5,pv194977], .c 7, .c 3,
  .p pv3 [pv2,pv31,pv3931], .c 13, .c 3, .c 11, .c 5, .c 3, .c 37,
  .p pv3 [pv2,pv3,pv5,pv103,pv631], .c 3, .c 5, .c 97, .c 3, .c 7, .c 277, .c 3, .c 31,
  .p pv17 [pv2,pv3,pv7,pv829], .c 3, .p pv2 [pv2,pv89,pv5477], .c 5, .c 3,
  .p pv2 [pv2,pv13,pv19,pv3947], .p pv2 [pv2,pv3,pv5,pv32497], .c 3, .c 5, .c 11, .c 3, .c 13,
  .p pv11 [pv2,pv3,pv17,pv59], .c 3, .c 19, .p pv3 [pv2,pv3,pv11,pv31,pv953], .c 3, .c 7, .c 5,
  .c 3, .c 11, .c 211, .c 3, .c 5, .c 7, .c 3, .c 107, .c 37, .c 3, .c 317, .c 31, .c 3, .c 29,
  .c 5, .c 3, .c 193, .p pv7 [pv2,pv3,pv5,pv16249], .c 3, .c 5, .p pv5 [pv2,pv3,pv36109], .c 3,
  .c 59, .c 11, .c 3, .c 937, .c 7, .c 3, .c 73, .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv64997],
  .c 3, .c 5, .c 17, .c 3, .c 43, .c 53, .c 3, .c 7, .p pv43 [pv2,pv3,pv113,pv719], .c 3,
  .p pv2 [pv2,pv19,pv25657], .c 5, .c 3, .p pv2 [pv2,pv974969], .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv324991], .c 3, .c 17, .c 613,
]
private theorem h0238c00 : checkBlock 1949699 128 b0238c00 = true := by
  decide +kernel

private def b0238c01 : List Row := [
  .c 3, .c 79, .c 11, .c 3, .c 23, .c 5, .c 3, .c 7, .c 929, .c 3, .c 5, .c 233, .c 3, .c 11,
  .c 7, .c 3, .c 13, .c 19, .c 3, .c 31, .c 5, .c 3, .p pv7 [pv2,pv974999], .c 41, .c 3, .c 5,
  .c 43, .c 3, .c 7, .c 13, .c 3, .p pv3 [pv2,pv30469], .c 17, .c 3, .p pv5 [pv2,pv975011], .c 5,
  .c 3, .c 53, .c 139, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv17,pv79], .c 3, .c 113,
  .p pv2 [pv2,pv3,pv41,pv7927], .c 3, .c 11, .c 73, .c 3, .c 7, .c 5, .c 3, .c 167,
  .p pv2 [pv2,pv3,pv5,pv7,pv4643], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv17,pv11471],
  .p pv5 [pv2,pv3,pv193,pv421], .c 3, .c 47, .c 89, .c 3, .c 41, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv97,pv359], .c 11, .c 3, .c 5, .c 157, .c 3, .c 23, .c 19, .c 3,
  .p pv2 [pv2,pv975053], .c 7, .c 3, .c 11, .c 5, .c 3, .c 109, .c 17, .c 3, .c 5, .c 59, .c 3,
  .c 503, .p pv2 [pv2,pv3,pv163,pv997], .c 3, .c 7, .p pv3 [pv2,pv3,pv17,pv6373], .c 3, .c 13,
  .c 5, .c 3, .p pv2 [pv2,pv31,pv15727], .c 7, .c 3, .c 5, .c 11, .c 3,
  .p pv7 [pv2,pv5,pv19,pv1283], .c 29, .c 3, .p pv5 [pv2,pv975083], .c 13, .c 3,
  .p pv2 [pv2,pv7,pv17,pv241], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv32503], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv59,pv787], .c 3, .c 1259, .c 7, .c 3, .c 131, .c 1301, .c 3, .c 1039,
  .c 5, .c 3, .c 101,
]
private theorem h0238c01 : checkBlock 1949955 128 b0238c01 = true := by
  decide +kernel

private def b0238c02 : List Row := [
  .p pv2 [pv2,pv3,pv5,pv31,pv233], .c 3, .c 5, .c 19, .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv167,pv5839], .c 173, .c 3, .c 37, .c 5, .c 3, .c 23, .c 31, .c 3, .c 5, .c 13,
  .c 3, .c 83, .p pv2 [pv2,pv3,pv331,pv491], .c 3, .c 17, .c 797, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv73,pv6679], .p pv3 [pv2,pv3,pv5,pv7,pv37,pv251], .c 3, .c 5, .c 7, .c 3, .c 311,
  .p pv2 [pv2,pv3,pv97,pv1117], .c 3, .p pv5 [pv2,pv13,pv75011], .c 11, .c 3, .c 19, .c 5, .c 3,
  .c 13, .c 191, .c 3, .c 5, .c 37, .c 3, .c 11, .c 1361, .c 3, .p pv2 [pv2,pv151,pv3229], .c 7,
  .c 3, .p pv2 [pv2,pv11,pv88651], .c 5, .c 3, .c 41, .c 19, .c 3, .c 5, .c 29, .c 3, .c 73,
  .p pv3 [pv2,pv3,pv17,pv19121], .c 3, .c 7, .p pv2 [pv2,pv3,pv162529], .c 3, .c 61, .c 5, .c 3,
  .c 17, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv29,pv1019], .c 3, .c 307, .c 257, .c 3, .c 11,
  .c 97, .c 3, .p pv5 [pv2,pv7,pv139313], .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv13,pv1667],
  .c 3, .c 5, .c 1009, .c 3, .p pv7 [pv2,pv5,pv23,pv53], .c 7, .c 3, .c 19,
  .p pv31 [pv2,pv3,pv103,pv263], .c 3, .c 241, .c 5, .c 3, .p pv2 [pv2,pv37,pv26357], .c 11, .c 3,
  .c 5, .c 17, .c 3, .c 7, .p pv17 [pv2,pv3,pv11,pv1847], .c 3, .c 43, .c 967, .c 3, .c 11, .c 5,
  .c 3, .p pv3 [pv2,pv139,pv877], .c 911, .c 3, .c 5, .p pv5 [pv2,pv3,pv181,pv449], .c 3, .c 17,
  .p pv5 [pv2,pv3,pv108359], .c 3,
]
private theorem h0238c02 : checkBlock 1950211 128 b0238c02 = true := by
  decide +kernel

private def b0238c03 : List Row := [
  .c 151, .c 23, .c 3, .c 7, .c 5, .c 3, .c 239, .c 13, .c 3, .c 5, .c 7, .c 3, .c 461, .c 41,
  .c 3, .c 197, .c 809, .c 3, .c 107, .c 5, .c 3, .c 11, .c 29, .c 3, .c 5,
  .p pv19 [pv2,pv3,pv54181], .c 3, .c 19, .c 43, .c 3, .p pv5 [pv2,pv975263], .c 7, .c 3, .c 13,
  .c 5, .c 3, .p pv2 [pv2,pv23,pv42403], .c 727, .c 3, .c 5, .c 47, .c 3, .c 31, .c 11, .c 3,
  .c 7, .c 13, .c 3, .c 17, .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv40637], .c 3,
  .c 223, .c 71, .c 3, .c 139, .c 79, .c 3, .c 127, .c 5, .c 3, .c 7, .c 587, .c 3, .c 5, .c 23,
  .c 3, .c 13, .c 7, .c 3, .p pv3 [pv2,pv19,pv41,pv313], .c 11, .c 3, .p pv5 [pv2,pv229,pv4259],
  .c 5, .c 3, .p pv2 [pv2,pv487657], .c 17, .c 3, .c 5, .c 13, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv12041], .c 3, .c 719, .p pv11 [pv2,pv3,pv7,pv17,pv683], .c 3, .c 23, .c 5,
  .c 3, .c 467, .p pv2 [pv2,pv3,pv5,pv10837], .c 3, .c 5, .p pv2 [pv2,pv3,pv83,pv3917], .c 3,
  .c 263, .c 19, .c 3, .c 37, .p pv3 [pv2,pv3,pv307,pv353], .c 3, .c 7, .c 5, .c 3, .c 13,
  .p pv37 [pv2,pv3,pv5,pv7,pv1327], .c 3, .c 5, .c 7, .c 3, .c 1291,
  .p pv5 [pv2,pv3,pv13,pv89,pv281], .c 3, .c 11, .c 1367, .c 3, .c 379, .c 5, .c 3, .c 61, .c 131,
]
private theorem h0238c03 : checkBlock 1950467 128 b0238c03 = true := by
  decide +kernel

private def b0238c04 : List Row := [
  .c 3, .c 5, .c 167, .c 3, .c 1109, .c 17, .c 3, .c 31, .c 7, .c 3, .c 29, .c 5, .c 3, .c 19,
  .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv162563], .c 3, .p pv3 [pv2,pv5,pv7,pv6967],
  .p pv2 [pv2,pv3,pv11,pv2687], .c 3, .c 7, .c 151, .c 3, .c 11, .c 5, .c 3, .c 73, .c 7, .c 3,
  .c 5, .c 19, .c 3, .c 23, .c 13, .c 3, .c 199, .c 31, .c 3, .p pv2 [pv2,pv7,pv139343], .c 5,
  .c 3, .c 7, .c 853, .c 3, .c 5, .c 11, .c 3, .c 41, .c 7, .c 3, .p pv2 [pv2,pv79,pv12347],
  .c 47, .c 3, .p pv3 [pv2,pv13,pv83,pv113], .c 5, .c 3, .c 11, .c 61, .c 3, .c 5, .c 127, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv17,pv73,pv131], .c 3, .c 149, .c 29, .c 3, .c 19, .c 5, .c 3, .c 17,
  .c 13, .c 3, .c 5, .c 53, .c 3, .p pv3 [pv2,pv5,pv89,pv137], .c 11, .c 3, .c 257,
  .p pv11 [pv2,pv3,pv29,pv2803], .c 3, .c 7, .c 5, .c 3, .c 37, .c 19, .c 3, .c 5, .c 7, .c 3,
  .c 277, .p pv5 [pv2,pv3,pv1129], .c 3, .c 29, .p pv3 [pv2,pv3,pv325153], .c 3, .c 13, .c 5,
  .c 3, .c 23, .c 107, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv97547], .c 599, .c 3, .c 163,
  .c 7, .c 3, .c 43, .c 5, .c 3, .p pv17 [pv2,pv19,pv51341], .c 97, .c 3, .c 5, .c 479, .c 3,
  .c 11, .c 37, .c 3, .c 7,
]
private theorem h0238c04 : checkBlock 1950723 128 b0238c04 = true := by
  decide +kernel

private def b0238c05 : List Row := [
  .p pv2 [pv2,pv3,pv325163], .c 3, .c 53, .c 5, .c 3, .p pv2 [pv2,pv13,pv17,pv2207], .c 7, .c 3,
  .c 5, .c 509, .c 3, .c 13, .p pv5 [pv2,pv3,pv283,pv383], .c 3, .p pv5 [pv2,pv149,pv6547], .c 71,
  .c 3, .p pv2 [pv2,pv7,pv59,pv1181], .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 13, .c 3, .c 353,
  .c 7, .c 3, .c 11, .c 17, .c 3, .p pv2 [pv2,pv975521], .c 5, .c 3, .p pv3 [pv2,pv11,pv22171],
  .p pv2 [pv2,pv3,pv5,pv13007], .c 3, .c 5, .c 269, .c 3, .c 7, .c 79, .c 3, .c 23, .c 977, .c 3,
  .c 17, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 293, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv11,pv13,pv379], .c 3, .p pv3 [pv2,pv7,pv34841], .p pv2 [pv2,pv3,pv433,pv751],
  .c 3, .c 7, .c 5, .c 3, .c 31, .c 47, .c 3, .c 5, .c 7, .c 3, .c 37, .p pv2 [pv2,pv3,pv325187],
  .c 3, .p pv5 [pv2,pv467,pv2089], .c 19, .c 3, .p pv2 [pv2,pv487783], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv139367], .c 17, .c 3, .c 5, .c 11, .c 3, .c 71, .p pv5 [pv2,pv3,pv7,pv5807],
  .c 3, .c 13, .c 7, .c 3, .c 373, .c 5, .c 3, .c 11, .c 31, .c 3, .c 5, .p pv5 [pv2,pv3,pv81299],
  .c 3, .c 347, .c 13, .c 3, .c 7, .c 59, .c 3, .p pv3 [pv2,pv17,pv14347], .c 5, .c 3,
  .p pv17 [pv2,pv975599], .c 7, .c 3, .c 5, .c 29, .c 3, .c 43, .c 11, .c 3, .c 73, .c 101, .c 3,
  .p pv23 [pv2,pv7,pv13,pv71,pv151], .c 5, .c 3, .c 7, .c 41, .c 3,
]
private theorem h0238c05 : checkBlock 1950979 128 b0238c05 = true := by
  decide +kernel

private def b0238c06 : List Row := [
  .c 5, .p pv2 [pv2,pv3,pv7,pv29,pv89], .c 3, .c 67, .c 7, .c 3, .c 83,
  .p pv17 [pv2,pv3,pv13,pv53,pv59], .c 3, .p pv2 [pv2,pv47,pv97,pv107], .c 5, .c 3, .c 349, .c 13,
  .c 3, .c 5, .c 173, .c 3, .c 7, .c 163, .c 3, .c 17, .c 11, .c 3, .c 419, .c 5, .c 3,
  .p pv3 [pv2,pv243911], .c 137, .c 3, .c 5, .c 23, .c 3, .c 11, .p pv3 [pv2,pv3,pv325217], .c 3,
  .c 59, .c 229, .c 3, .c 7, .c 5, .c 3, .c 19, .p pv17 [pv2,pv3,pv5,pv7,pv23,pv101], .c 3, .c 5,
  .c 7, .c 3, .c 683, .c 823, .c 3, .c 1033, .c 13, .c 3, .c 23, .c 5, .c 3, .c 97, .c 1307, .c 3,
  .c 5, .c 19, .c 3, .c 181, .c 73, .c 3, .c 11, .c 7, .c 3, .c 151, .c 5, .c 3, .c 17, .c 29,
  .c 3, .c 5, .c 541, .c 3, .c 13, .c 47, .c 3, .c 7, .c 1117, .c 3, .p pv2 [pv2,pv975701], .c 5,
  .c 3, .c 487, .c 7, .c 3, .c 5, .c 13, .c 3, .c 101, .c 193, .c 3, .c 109,
  .p pv2 [pv2,pv3,pv137,pv1187], .c 3, .c 11, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv47,pv173],
  .c 3, .c 5, .c 17, .c 3, .c 61, .c 7, .c 3, .p pv3 [pv2,pv13,pv4691],
  .p pv2 [pv2,pv3,pv23,pv79,pv179], .c 3, .p pv5 [pv2,pv975731], .c 5, .c 3, .c 13, .c 19, .c 3,
  .c 5, .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv13,pv127,pv197], .c 3, .c 47,
  .p pv19 [pv2,pv3,pv7,pv11],
]
private theorem h0238c06 : checkBlock 1951235 128 b0238c06 = true := by
  decide +kernel

private def b0238c07 : List Row := [
  .c 3, .p pv2 [pv2,pv487873], .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv1301], .c 3, .c 5, .c 131,
  .c 3, .p pv7 [pv2,pv5,pv11,pv113,pv157], .c 53, .c 3, .c 821, .c 227, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv19,pv37,pv347], .c 433, .c 3, .c 5, .c 7, .c 3, .c 103, .c 11, .c 3, .c 13, .c 17,
  .c 3, .p pv3 [pv2,pv30493], .c 5, .c 3, .c 41, .p pv17 [pv2,pv3,pv5,pv13,pv139], .c 3, .c 5,
  .c 337, .c 3, .c 617, .c 13, .c 3, .c 71, .c 7, .c 3, .c 17, .c 5, .c 3, .c 499,
  .p pv61 [pv2,pv3,pv5,pv65053], .c 3, .c 5, .p pv2 [pv2,pv3,pv23,pv2357], .c 3,
  .p pv13 [pv2,pv5,pv7,pv17,pv41], .p pv2 [pv2,pv3,pv37,pv59,pv149], .c 3, .c 7, .c 11, .c 3,
  .c 29, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv325271], .c 3, .c 11,
  .p pv5 [pv2,pv3,pv13553], .c 3, .c 179, .c 37, .c 3, .c 67, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv7,pv11617], .c 3, .c 19, .c 7, .c 3, .c 31, .p pv2 [pv2,pv3,pv17,pv1063],
  .c 3, .c 293, .c 5, .c 3, .c 197, .c 89, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv9857], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv162641], .c 3, .c 11, .c 19, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv44357], .c 23, .c 3, .c 5, .c 1213, .c 3, .p pv3 [pv2,pv5,pv59,pv827], .c 41,
  .c 3, .c 43, .c 13, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv975869], .c 11, .c 3, .c 5,
]
private theorem h0238c07 : checkBlock 1951491 128 b0238c07 = true := by
  decide +kernel

private def b0238c08 : List Row := [
  .c 7, .c 3, .c 149, .c 17, .c 3, .c 23, .p pv3 [pv2,pv3,pv29,pv3739], .c 3, .c 11, .c 5, .c 3,
  .c 47, .c 937, .c 3, .c 5, .c 67, .c 3, .c 13, .p pv7 [pv2,pv3,pv7,pv46471], .c 3, .c 17, .c 7,
  .c 3, .p pv3 [pv2,pv199,pv613], .c 5, .c 3, .c 1091, .c 73, .c 3, .c 5, .c 11, .c 3,
  .p pv11 [pv2,pv5,pv7,pv27883], .c 19, .c 3, .c 7, .p pv2 [pv2,pv3,pv11,pv29573], .c 3,
  .p pv5 [pv2,pv31,pv31481], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv311,pv523],
  .c 3, .c 233, .p pv2 [pv2,pv3,pv325307], .c 3, .c 457, .c 23, .c 3, .c 31, .c 5, .c 3, .c 7,
  .c 37, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv2213], .c 3, .p pv11 [pv2,pv5,pv19,pv10273], .c 7,
  .c 3, .c 709, .p pv17 [pv2,pv3,pv61,pv5333], .c 3, .c 359, .c 5, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv5,pv65063], .c 3, .c 5, .c 59, .c 3, .c 7, .c 29, .c 3, .c 331, .c 373, .c 3,
  .c 239, .c 5, .c 3, .c 223, .c 563, .c 3, .c 5, .c 19, .c 3, .c 97, .c 661, .c 3, .c 13, .c 11,
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv89,pv5483], .p pv3 [pv2,pv3,pv5,pv7,pv11,pv13], .c 3,
  .c 5, .c 7, .c 3, .c 11, .c 13, .c 3, .p pv5 [pv2,pv293,pv3331], .c 41, .c 3, .c 227, .c 5,
  .c 3, .c 733, .c 157, .c 3, .c 5, .c 23, .c 3, .c 17, .p pv41 [pv2,pv3,pv7,pv1291], .c 3,
  .p pv2 [pv2,pv229,pv2131], .c 7, .c 3,
]
private theorem h0238c08 : checkBlock 1951747 128 b0238c08 = true := by
  decide +kernel

private def b0238c09 : List Row := [
  .c 19, .c 5, .c 3, .c 37, .c 79, .c 3, .c 5, .c 1327, .c 3, .p pv2 [pv2,pv5,pv7,pv73,pv191],
  .p pv3 [pv2,pv3,pv19,pv17123], .c 3, .c 7, .c 1153, .c 3, .c 23, .c 5, .c 3, .c 31, .c 7, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv37,pv977], .c 3, .c 41, .p pv5 [pv2,pv3,pv162671], .c 3, .c 1171, .c 17,
  .c 3, .c 167, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 29, .c 3, .c 109, .c 7, .c 3,
  .p pv5 [pv2,pv317,pv3079], .p pv7 [pv2,pv3,pv163,pv499], .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv19,pv47,pv1093], .c 31, .c 3, .c 5, .c 281, .c 3, .c 7, .c 137, .c 3, .c 19,
  .c 13, .c 3, .p pv2 [pv2,pv61,pv16001], .c 5, .c 3, .p pv3 [pv2,pv101,pv151],
  .p pv2 [pv2,pv3,pv5,pv65071], .c 3, .c 5, .c 11, .c 3, .c 599, .c 503, .c 3, .c 311, .c 53,
  .c 3, .c 7, .c 5, .c 3, .c 11, .c 17, .c 3, .c 5, .c 7, .c 3, .c 13,
  .p pv5 [pv2,pv3,pv211,pv257], .c 3, .c 421, .c 67, .c 3, .c 61, .c 5, .c 3, .c 1049,
  .p pv13 [pv2,pv3,pv5,pv109,pv199], .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv43,pv227], .c 11,
  .c 3, .p pv5 [pv2,pv976103], .c 7, .c 3, .c 307, .c 5, .c 3, .p pv2 [pv2,pv976109],
  .p pv7 [pv2,pv3,pv5,pv32537], .c 3, .c 5, .p pv2 [pv2,pv3,pv108457], .c 3, .c 19, .c 439, .c 3,
  .c 7, .c 47, .c 3, .c 43, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv31,pv41],
]
private theorem h0238c09 : checkBlock 1952003 128 b0238c09 = true := by
  decide +kernel

private def b0238c10 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv97613], .c 17, .c 3, .p pv2 [pv2,pv181,pv5393], .c 11, .c 3, .c 911,
  .c 5, .c 3, .c 7, .c 1039, .c 3, .c 5, .c 31, .c 3, .c 11, .c 7, .c 3, .c 17, .c 109, .c 3,
  .c 757, .c 5, .c 3, .c 23, .p pv11 [pv2,pv3,pv5,pv59,pv1103], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv18077], .c 3, .c 7, .p pv3 [pv2,pv3,pv107,pv3041], .c 3, .c 13, .c 43, .c 3,
  .c 47, .c 5, .c 3, .p pv2 [pv2,pv29,pv41,pv821], .c 241, .c 3, .c 5, .c 149, .c 3,
  .p pv7 [pv2,pv5,pv39047], .c 13, .c 3, .c 11, .c 523, .c 3, .c 7, .c 5, .c 3, .c 59, .c 127,
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv31,pv47,pv67], .c 19, .c 3, .c 137, .c 199, .c 3,
  .c 89, .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv79,pv1373], .c 3, .c 31,
  .p pv2 [pv2,pv3,pv7,pv11,pv2113], .c 3, .c 283, .c 7, .c 3, .c 11, .c 5, .c 3, .c 71, .c 13,
  .c 3, .c 5, .p pv13 [pv2,pv3,pv162703], .c 3, .p pv3 [pv2,pv5,pv7,pv19,pv367], .c 353, .c 3,
  .c 7, .p pv41 [pv2,pv3,pv10169], .c 3, .c 37, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 11, .c 3,
  .c 463, .c 31, .c 3, .p pv2 [pv2,pv488119], .p pv3 [pv2,pv3,pv11,pv19,pv173], .c 3, .c 13, .c 5,
  .c 3, .c 7, .c 769, .c 3, .c 5, .c 19, .c 3, .c 17, .c 7, .c 3, .c 859, .c 13, .c 3, .c 97,
]
private theorem h0238c10 : checkBlock 1952259 128 b0238c10 = true := by
  decide +kernel

private def b0238c11 : List Row := [
  .c 5, .c 3, .p pv7 [pv2,pv17,pv57427], .c 47, .c 3, .c 5, .c 37, .c 3, .c 7, .c 11, .c 3,
  .p pv3 [pv2,pv107,pv2281], .c 23, .c 3, .c 41, .c 5, .c 3, .c 61, .p pv19 [pv2,pv3,pv5,pv4339],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv162713], .c 3, .c 13, .p pv3 [pv2,pv3,pv23,pv14149], .c 3,
  .p pv5 [pv2,pv7,pv11,pv31,pv409], .c 17, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv337,pv2897],
  .c 67, .c 3, .c 5, .c 7, .c 3, .p pv11 [pv2,pv5,pv195259], .c 191, .c 3, .c 31, .c 11, .c 3,
  .c 17, .c 5, .c 3, .c 157, .c 19, .c 3, .c 5, .c 659, .c 3, .c 11, .p pv3 [pv2,pv3,pv7,pv15497],
  .c 3, .p pv2 [pv2,pv13,pv53,pv109], .c 7, .c 3, .c 101, .c 5, .c 3, .c 13,
  .p pv31 [pv2,pv3,pv5,pv113], .c 3, .c 5, .p pv3 [pv2,pv3,pv503,pv647], .c 3, .c 173,
  .p pv2 [pv2,pv3,pv13,pv12517], .c 3, .c 7, .c 31, .c 3, .p pv5 [pv2,pv47,pv20773], .c 5, .c 3,
  .c 281, .c 7, .c 3, .c 5, .c 23, .c 3, .c 971, .c 229, .c 3, .c 11,
  .p pv13 [pv2,pv3,pv17,pv2393], .c 3, .p pv2 [pv2,pv7,pv69739], .c 5, .c 3, .c 7, .c 449, .c 3,
  .c 5, .c 41, .c 3, .c 179, .c 7, .c 3, .c 13, .c 607, .c 3, .c 23, .c 5, .c 3,
  .p pv3 [pv2,pv244091], .c 11, .c 3, .c 5, .p pv7 [pv2,pv3,pv20341], .c 3, .c 7, .c 13, .c 3,
  .p pv2 [pv2,pv23,pv42451], .c 37, .c 3, .c 11, .c 5, .c 3, .c 43, .c 457, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv157,pv691], .c 3,
]
private theorem h0238c11 : checkBlock 1952515 128 b0238c11 = true := by
  decide +kernel

private def b0238c12 : List Row := [
  .c 907, .c 17, .c 3, .c 103, .p pv11 [pv2,pv3,pv325463], .c 3, .c 7, .c 5, .c 3, .c 41, .c 643,
  .c 3, .c 5, .c 7, .c 3, .c 19, .c 47, .c 3, .c 17, .c 181, .c 3, .p pv2 [pv2,pv488203], .c 5,
  .c 3, .c 11, .c 13, .c 3, .c 5, .c 307, .c 3, .c 29, .p pv19 [pv2,pv3,pv7,pv1453], .c 3,
  .p pv2 [pv2,pv488209], .c 7, .c 3, .c 397, .c 5, .c 3, .c 67, .p pv3 [pv2,pv3,pv5,pv47,pv277],
  .c 3, .c 5, .c 107, .c 3, .c 23, .c 11, .c 3, .c 7, .c 239, .c 3, .c 13, .c 5, .c 3, .c 127,
  .c 7, .c 3, .c 5, .p pv29 [pv2,pv3,pv13,pv25037], .c 3, .c 53, .p pv5 [pv2,pv3,pv17,pv3191],
  .c 3, .c 37, .c 13, .c 3, .c 163, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv2411], .c 3, .c 5,
  .c 383, .c 3, .p pv3 [pv2,pv5,pv48823], .c 7, .c 3, .c 89, .c 11, .c 3, .p pv2 [pv2,pv488233],
  .c 5, .c 3, .p pv2 [pv2,pv13,pv31,pv2423], .c 1193, .c 3, .c 5, .c 29, .c 3, .c 7, .c 19, .c 3,
  .p pv2 [pv2,pv488239], .c 59, .c 3, .p pv2 [pv2,pv11,pv88771], .c 5, .c 3, .c 31, .c 37, .c 3,
  .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv97649], .c 67, .c 3, .c 379, .p pv2 [pv2,pv3,pv162749],
  .c 3, .c 7, .c 5, .c 3, .c 23, .p pv11 [pv2,pv3,pv5,pv7,pv31], .c 3, .c 5, .c 7, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv162751], .c 3, .c 11, .c 421, .c 3, .c 977, .c 5,
]
private theorem h0238c12 : checkBlock 1952771 128 b0238c12 = true := by
  decide +kernel

private def b0238c13 : List Row := [
  .c 3, .c 13, .c 31, .c 3, .c 5, .c 61, .c 3, .p pv7 [pv2,pv5,pv24413],
  .p pv2 [pv2,pv3,pv7,pv13,pv73], .c 3, .c 563, .c 7, .c 3, .p pv2 [pv2,pv488263], .c 5, .c 3,
  .p pv2 [pv2,pv197,pv4957], .c 11, .c 3, .c 5, .c 19, .c 3, .c 107, .c 83, .c 3, .c 7, .c 17,
  .c 3, .c 11, .c 5, .c 3, .c 139, .c 7, .c 3, .c 5, .c 271, .c 3, .p pv2 [pv2,pv5,pv19531],
  .c 43, .c 3, .c 13, .p pv13 [pv2,pv3,pv227,pv239], .c 3, .c 17, .c 5, .c 3, .c 7, .c 29, .c 3,
  .c 5, .c 11, .c 3, .c 1223, .c 7, .c 3, .c 23, .c 71, .c 3, .c 19, .c 5, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv5,pv29,pv449], .c 3, .c 5, .p pv7 [pv2,pv3,pv37,pv53,pv83], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv19,pv5711], .c 3, .p pv5 [pv2,pv191,pv5113], .c 389, .c 3, .c 1021, .c 5,
  .c 3, .c 29, .c 17, .c 3, .c 5, .c 443, .c 3, .c 1093, .c 11, .c 3, .c 1303, .c 41, .c 3, .c 7,
  .c 5, .c 3, .c 53, .c 13, .c 3, .c 5, .c 7, .c 3, .c 983, .c 1237, .c 3, .c 211, .c 23, .c 3,
  .p pv3 [pv2,pv17,pv43,pv167], .c 5, .c 3, .c 83, .c 149, .c 3, .c 5, .c 1151, .c 3, .c 67,
  .p pv41 [pv2,pv3,pv7,pv23,pv337], .c 3, .c 19, .c 7, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv488317], .c 401, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv19,pv659], .c 3, .c 11,
]
private theorem h0238c13 : checkBlock 1953027 128 b0238c13 = true := by
  decide +kernel

private def b0238c14 : List Row := [
  .c 17, .c 3, .c 7, .c 13, .c 3, .c 647, .c 5, .c 3, .p pv2 [pv2,pv23,pv42463], .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv108517], .c 3, .p pv17 [pv2,pv5,pv31,pv6301], .c 59, .c 3, .c 17, .c 359,
  .c 3, .p pv2 [pv2,pv7,pv41,pv83], .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv65111], .c 3, .c 5,
  .c 547, .c 3, .c 13, .c 7, .c 3, .c 11, .p pv2 [pv2,pv3,pv162779], .c 3, .c 29, .c 5, .c 3,
  .p pv7 [pv2,pv11,pv88789], .c 43, .c 3, .c 5, .c 13, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv31,pv59,pv89], .c 3, .c 569, .p pv3 [pv2,pv3,pv7,pv37,pv419], .c 3,
  .p pv5 [pv2,pv29,pv33679], .c 5, .c 3, .c 109, .c 11, .c 3, .c 5, .c 463, .c 3, .c 373, .c 31,
  .c 3, .c 73, .c 19, .c 3, .c 7, .c 5, .c 3, .c 13, .c 53, .c 3, .c 5, .c 7, .c 3, .c 59, .c 79,
  .c 3, .p pv2 [pv2,pv17,pv23,pv1249], .c 1319, .c 3, .c 1367, .c 5, .c 3, .c 727,
  .p pv2 [pv2,pv3,pv5,pv1447], .c 3, .c 5, .c 11, .c 3, .c 47, .p pv5 [pv2,pv3,pv7,pv46511], .c 3,
  .p pv2 [pv2,pv19,pv51407], .c 7, .c 3, .p pv3 [pv2,pv131,pv233], .c 5, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv5,pv73,pv223], .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv7,pv11,pv43,pv59],
  .p pv2 [pv2,pv3,pv162791], .c 3, .c 7, .c 107, .c 3, .p pv5 [pv2,pv353,pv2767], .c 5, .c 3,
  .p pv2 [pv2,pv47,pv10391], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv173,pv941], .c 3, .c 17, .c 11,
  .c 3, .c 29, .p pv29 [pv2,pv3,pv23,pv3539], .c 3, .c 43, .c 5, .c 3,
]
private theorem h0238c14 : checkBlock 1953283 128 b0238c14 = true := by
  decide +kernel

private def b0238c15 : List Row := [
  .c 7, .c 367, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv193,pv241], .c 3, .c 23, .c 7, .c 3,
  .p pv3 [pv2,pv11,pv29,pv1531], .p pv19 [pv2,pv3,pv31,pv389], .c 3, .c 37, .c 5, .c 3,
  .p pv3 [pv2,pv41,pv1489], .c 83, .c 3, .c 5, .p pv7 [pv2,pv3,pv43,pv631], .c 3, .c 7, .c 199,
  .c 3, .p pv2 [pv2,pv61,pv67,pv239], .c 11, .c 3, .p pv3 [pv2,pv244199], .c 5, .c 3, .c 19,
  .c 13, .c 3, .c 5, .c 109, .c 3, .c 11, .p pv2 [pv2,pv3,pv18089], .c 3,
  .p pv3 [pv2,pv7,pv17443], .c 43, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv488407], .c 613, .c 3,
  .c 5, .c 7, .c 3, .c 127, .c 23, .c 3, .c 61, .c 47, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv139547], .c 947, .c 3, .c 5, .c 59, .c 3, .c 317,
  .p pv5 [pv2,pv3,pv7,pv29,pv401], .c 3, .c 11, .c 7, .c 3, .c 383, .c 5, .c 3, .c 23, .c 17,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv47,pv433], .c 3, .c 29, .c 223, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv17,pv61,pv157], .c 3, .c 19, .c 5, .c 3, .c 673, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv59,pv5519], .c 3, .c 13, .c 167, .c 3, .c 83, .c 53, .c 3, .c 11, .c 5, .c 3,
  .c 7, .c 19, .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv12211], .c 7, .c 3,
  .p pv5 [pv2,pv976883], .c 61, .c 3, .c 41, .c 5, .c 3, .c 1373, .c 23, .c 3, .c 5, .c 11, .c 3,
  .c 7, .c 17,
]
private theorem h0238c15 : checkBlock 1953539 128 b0238c15 = true := by
  decide +kernel

private def b0238c16 : List Row := [
  .c 3, .c 419, .p pv23 [pv2,pv3,pv7,pv11,pv4229], .c 3, .p pv2 [pv2,pv823,pv1187], .c 5, .c 3,
  .c 11, .p pv3 [pv2,pv3,pv5,pv17,pv1277], .c 3, .c 5, .c 29, .c 3,
  .p pv3 [pv2,pv5,pv11,pv83,pv107], .p pv3 [pv2,pv3,pv13,pv37,pv677], .c 3, .c 17,
  .p pv2 [pv2,pv3,pv79,pv229], .c 3, .c 7, .c 5, .c 3, .p pv17 [pv2,pv976919], .c 479, .c 3, .c 5,
  .c 7, .c 3, .c 601, .c 11, .c 3, .p pv3 [pv2,pv30529], .c 37, .c 3, .p pv5 [pv2,pv173,pv5647],
  .c 5, .c 3, .p pv2 [pv2,pv7,pv31,pv2251], .c 97, .c 3, .c 5, .c 43, .c 3, .c 163, .c 113, .c 3,
  .c 13, .c 7, .c 3, .c 331, .c 5, .c 3, .c 31, .p pv17 [pv2,pv3,pv5,pv13,pv167], .c 3, .c 5,
  .c 79, .c 3, .p pv7 [pv2,pv5,pv7,pv103,pv271], .c 13, .c 3, .c 7, .c 11, .c 3, .c 139, .c 5,
  .c 3, .c 17, .c 7, .c 3, .c 5, .c 41, .c 3, .c 11, .p pv3 [pv2,pv3,pv23,pv14159], .c 3, .c 389,
  .p pv2 [pv2,pv3,pv162829], .c 3, .c 829, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv46523], .c 3, .c 257, .c 7, .c 3, .p pv3 [pv2,pv244247], .c 19, .c 3,
  .p pv5 [pv2,pv976991], .c 5, .c 3, .c 439, .c 13, .c 3, .c 5, .c 17, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv325667], .c 3, .c 11, .c 1283, .c 3, .c 61, .c 5, .c 3, .c 41, .c 59, .c 3,
  .c 5, .c 1201, .c 3, .c 17, .p pv5 [pv2,pv3,pv40709], .c 3, .c 359, .c 617, .c 3, .c 7, .c 5,
  .c 3, .c 29,
]
private theorem h0238c16 : checkBlock 1953795 128 b0238c16 = true := by
  decide +kernel

private def b0238c17 : List Row := [
  .c 11, .c 3, .c 5, .c 7, .c 3, .c 887, .c 683, .c 3, .c 167, .c 13, .c 3, .c 11, .c 5, .c 3,
  .c 883, .c 37, .c 3, .c 5, .p pv5 [pv2,pv3,pv325681], .c 3, .c 151, .c 19, .c 3,
  .p pv3 [pv2,pv122131], .c 7, .c 3, .c 23, .c 5, .c 3, .c 113, .p pv17 [pv2,pv3,pv5,pv53,pv1229],
  .c 3, .c 5, .c 11, .c 3, .c 13, .c 587, .c 3, .c 7, .c 433, .c 3, .c 17, .c 5, .c 3, .c 11,
  .c 7, .c 3, .c 5, .c 13, .c 3, .p pv19 [pv2,pv5,pv11,pv17,pv19], .p pv5 [pv2,pv3,pv83,pv109],
  .c 3, .p pv2 [pv2,pv488539], .p pv3 [pv2,pv3,pv325693], .c 3, .c 53, .c 5, .c 3, .c 7, .c 233,
  .c 3, .c 5, .p pv19 [pv2,pv3,pv7,pv727], .c 3, .c 271, .c 7, .c 3, .p pv2 [pv2,pv13,pv75161],
  .c 67, .c 3, .p pv3 [pv2,pv37,pv3301], .c 5, .c 3, .c 13, .c 17, .c 3, .c 5, .c 19, .c 3, .c 7,
  .c 47, .c 3, .p pv3 [pv2,pv11,pv53,pv419], .c 103, .c 3, .c 29, .c 5, .c 3, .c 37,
  .p pv3 [pv2,pv3,pv5,pv65141], .c 3, .c 5, .p pv2 [pv2,pv3,pv162853], .c 3, .c 23, .c 227, .c 3,
  .p pv5 [pv2,pv7,pv139589], .c 11, .c 3, .c 7, .c 5, .c 3, .c 97, .c 109, .c 3, .c 5, .c 7, .c 3,
  .c 11, .p pv5 [pv2,pv3,pv20357], .c 3, .c 13, .p pv13 [pv2,pv3,pv108571], .c 3, .c 19, .c 5,
  .c 3, .p pv11 [pv2,pv7,pv17449], .p pv17 [pv2,pv3,pv5,pv13,pv5011], .c 3, .c 5,
  .p pv17 [pv2,pv3,pv27143], .c 3, .p pv3 [pv2,pv5,pv19543], .c 13, .c 3,
]
private theorem h0238c17 : checkBlock 1954051 128 b0238c17 = true := by
  decide +kernel

private def b0238c18 : List Row := [
  .c 43, .c 7, .c 3, .p pv3 [pv2,pv191,pv1279], .c 5, .c 3, .p pv11 [pv2,pv61,pv83,pv193], .c 19,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv29611], .c 3, .c 487, .c 23, .c 3, .c 7, .c 29, .c 3,
  .p pv5 [pv2,pv13,pv75167], .c 5, .c 3, .p pv2 [pv2,pv11,pv44417], .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv23,pv73,pv97], .c 3, .p pv3 [pv2,pv5,pv48859], .p pv2 [pv2,pv3,pv307,pv1061],
  .c 3, .p pv5 [pv2,pv977183], .p pv11 [pv2,pv3,pv13,pv29], .c 3, .p pv2 [pv2,pv7,pv223,pv313],
  .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv15511], .c 3,
  .p pv17 [pv2,pv5,pv67,pv2917], .c 7, .c 3, .c 19, .c 1171, .c 3, .c 11, .c 5, .c 3, .c 641,
  .p pv2 [pv2,pv3,pv5,pv65147], .c 3, .c 5, .c 71, .c 3, .c 7, .p pv3 [pv2,pv3,pv17,pv2129], .c 3,
  .p pv2 [pv2,pv29,pv31,pv1087], .c 41, .c 3, .c 13, .c 5, .c 3, .c 17,
  .p pv47 [pv2,pv3,pv5,pv61,pv89], .c 3, .c 5, .c 11, .c 3, .c 37, .c 97, .c 3, .c 31, .c 13,
  .c 3, .c 7, .c 5, .c 3, .c 11, .c 23, .c 3, .c 5, .c 7, .c 3, .c 53, .p pv3 [pv2,pv3,pv325747],
  .c 3, .p pv5 [pv2,pv977243], .p pv41 [pv2,pv3,pv31,pv37,pv71], .c 3, .c 59, .c 5, .c 3, .c 677,
  .c 61, .c 3, .c 5, .c 17, .c 3, .c 13, .c 11, .c 3, .c 23, .c 7, .c 3,
  .p pv2 [pv2,pv43,pv22727], .c 5, .c 3, .c 89, .p pv3 [pv2,pv3,pv5,pv19,pv127], .c 3, .c 5,
  .c 13, .c 3, .c 17, .p pv13 [pv2,pv3,pv29,pv47,pv239], .c 3, .c 7, .c 19, .c 3,
  .p pv3 [pv2,pv41,pv59,pv101], .c 5, .c 3, .c 71, .c 7,
]
private theorem h0238c18 : checkBlock 1954307 128 b0238c18 = true := by
  decide +kernel

private def b0238c19 : List Row := [
  .c 3, .c 5, .c 83, .c 3, .c 29, .p pv2 [pv2,pv3,pv162881], .c 3, .c 661, .c 11, .c 3, .c 499,
  .c 5, .c 3, .c 7, .c 67, .c 3, .c 5, .p pv11 [pv2,pv3,pv7,pv23269], .c 3, .c 11, .c 7, .c 3,
  .p pv5 [pv2,pv19,pv51437], .c 17, .c 3, .p pv2 [pv2,pv11,pv31,pv1433], .c 5, .c 3, .c 181,
  .p pv13 [pv2,pv3,pv5,pv10859], .c 3, .c 5, .p pv23 [pv2,pv3,pv17,pv19163], .c 3, .c 7, .c 541,
  .c 3, .c 233, .p pv3 [pv2,pv3,pv7,pv5171], .c 3, .c 17, .c 5, .c 3, .p pv3 [pv2,pv73,pv3347],
  .c 43, .c 3, .c 5, .c 127, .c 3, .p pv2 [pv2,pv5,pv17,pv5749], .c 19, .c 3, .c 11, .c 307, .c 3,
  .c 7, .c 5, .c 3, .p pv11 [pv2,pv11,pv23,pv3863], .c 283, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv195469], .c 13, .c 3, .c 79, .p pv2 [pv2,pv3,pv325783], .c 3, .c 421, .c 5,
  .c 3, .p pv2 [pv2,pv7,pv9973], .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv29,pv41,pv137], .c 3, .c 73,
  .c 271, .c 3, .c 173, .c 7, .c 3, .c 11, .c 5, .c 3, .c 19, .p pv2 [pv2,pv3,pv5,pv32579], .c 3,
  .c 5, .c 23, .c 3, .c 241, .p pv5 [pv2,pv3,pv10181], .c 3, .c 7,
  .p pv3 [pv2,pv3,pv13,pv19,pv1319], .c 3, .p pv2 [pv2,pv17,pv57493], .c 5, .c 3,
  .p pv3 [pv2,pv122173], .c 7, .c 3, .c 5, .c 11, .c 3, .c 239, .c 107, .c 3, .c 113, .c 277,
  .c 3, .c 23, .c 5, .c 3, .c 7, .c 821, .c 3, .c 5, .c 157, .c 3,
  .p pv11 [pv2,pv5,pv11,pv13,pv1367], .c 7, .c 3, .c 857,
]
private theorem h0238c19 : checkBlock 1954563 128 b0238c19 = true := by
  decide +kernel

private def b0238c20 : List Row := [
  .p pv3 [pv2,pv3,pv223,pv487], .c 3, .c 13, .c 5, .c 3, .c 31, .c 197, .c 3, .c 5, .c 103, .c 3,
  .c 7, .c 11, .c 3, .c 17, .c 13, .c 3, .c 19, .c 5, .c 3, .c 67, .c 29, .c 3, .c 5, .c 61, .c 3,
  .c 47, .p pv11 [pv2,pv3,pv19,pv1429], .c 3, .p pv2 [pv2,pv7,pv11,pv577], .c 263, .c 3, .c 7,
  .c 5, .c 3, .p pv3 [pv2,pv13,pv18797], .c 19, .c 3, .c 5, .c 7, .c 3, .c 13, .c 727, .c 3,
  .p pv2 [pv2,pv59,pv16567], .c 11, .c 3, .c 131, .c 5, .c 3, .c 29, .c 41, .c 3, .c 5, .c 13,
  .c 3, .c 11, .p pv5 [pv2,pv3,pv7,pv17,pv37], .c 3, .c 337, .c 7, .c 3,
  .p pv5 [pv2,pv11,pv88861], .c 5, .c 3, .c 17, .p pv11 [pv2,pv3,pv5,pv13033], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv101,pv1613], .c 3, .c 719, .p pv2 [pv2,pv3,pv41,pv883], .c 3, .c 7, .c 37,
  .c 3, .c 229, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv19,pv1559], .c 3,
  .p pv19 [pv2,pv5,pv137,pv1427], .c 67, .c 3, .c 11, .c 257, .c 3, .c 41, .c 5, .c 3, .c 7,
  .c 53, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv239,pv409], .c 7, .c 3, .p pv2 [pv2,pv977513],
  .c 149, .c 3, .p pv3 [pv2,pv244379], .c 5, .c 3, .c 251, .c 11, .c 3, .c 5,
  .p pv23 [pv2,pv3,pv23,pv31,pv457], .c 3, .c 7, .c 601, .c 3, .c 13, .c 47, .c 3, .c 11, .c 5,
  .c 3, .c 23, .p pv3 [pv2,pv3,pv5,pv13,pv557], .c 3,
]
private theorem h0238c20 : checkBlock 1954819 128 b0238c20 = true := by
  decide +kernel

private def b0238c21 : List Row := [
  .c 5, .c 31, .c 3, .c 19, .c 13, .c 3, .c 1277, .c 701, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv349,pv2801], .c 461, .c 3, .c 5, .c 7, .c 3, .c 61, .p pv5 [pv2,pv3,pv81463],
  .c 3, .c 37, .c 17, .c 3, .p pv2 [pv2,pv13,pv29,pv2593], .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv65171], .c 3, .c 5, .p pv11 [pv2,pv3,pv17,pv599], .c 3,
  .p pv2 [pv2,pv5,pv11,pv8887], .c 1123, .c 3, .c 607, .c 7, .c 3, .c 17, .c 5, .c 3, .c 73,
  .c 13, .c 3, .c 5, .c 41, .c 3, .c 79, .c 11, .c 3, .c 7, .p pv3 [pv2,pv3,pv149], .c 3,
  .p pv5 [pv2,pv977591], .c 5, .c 3, .c 293, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv54311], .c 3,
  .c 31, .p pv2 [pv2,pv3,pv229,pv1423], .c 3, .c 23, .c 29, .c 3, .c 13, .c 5, .c 3, .c 7, .c 17,
  .c 3, .c 5, .c 1259, .c 3, .c 83, .c 7, .c 3, .p pv2 [pv2,pv167,pv2927], .c 11, .c 3, .c 991,
  .c 5, .c 3, .c 41, .p pv2 [pv2,pv3,pv5,pv11,pv79], .c 3, .c 5, .c 311, .c 3, .c 7, .c 31, .c 3,
  .c 29, .c 71, .c 3, .c 617, .c 5, .c 3, .p pv7 [pv2,pv13,pv157,pv479],
  .p pv7 [pv2,pv3,pv5,pv8147], .c 3, .c 5, .p pv3 [pv2,pv3,pv36209], .c 3, .c 13,
  .p pv2 [pv2,pv3,pv127,pv1283], .c 3, .c 587, .c 23, .c 3, .c 7, .c 5, .c 3, .c 19, .c 313, .c 3,
  .c 5, .c 7, .c 3, .c 811, .c 17, .c 3, .c 11, .c 53,
]
private theorem h0238c21 : checkBlock 1955075 128 b0238c21 = true := by
  decide +kernel

private def b0238c22 : List Row := [
  .c 3, .p pv2 [pv2,pv488833], .c 5, .c 3, .c 37, .c 47, .c 3, .c 5, .c 19, .c 3, .c 109, .c 809,
  .c 3, .c 17, .c 7, .c 3, .c 643, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 1093, .c 3,
  .p pv2 [pv2,pv5,pv7,pv13967], .c 29, .c 3, .c 7, .p pv2 [pv2,pv3,pv47,pv3467], .c 3, .c 11,
  .c 5, .c 3, .p pv23 [pv2,pv941,pv1039], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv325901], .c 3,
  .c 71, .c 37, .c 3, .p pv3 [pv2,pv61,pv4007], .c 89, .c 3, .c 19, .c 5, .c 3, .c 7, .c 229,
  .c 3, .c 5, .c 11, .c 3, .c 29, .c 7, .c 3, .c 13, .c 31, .c 3, .c 577, .c 5, .c 3, .c 11,
  .c 19, .c 3, .c 5, .p pv2 [pv2,pv3,pv108637], .c 3, .c 7, .c 13, .c 3, .c 61, .c 281, .c 3,
  .c 23, .c 5, .c 3, .p pv3 [pv2,pv53,pv1153], .p pv3 [pv2,pv3,pv5,pv65183], .c 3, .c 5, .c 523,
  .c 3, .p pv13 [pv2,pv5,pv3911], .c 11, .c 3, .p pv2 [pv2,pv7,pv23,pv6073],
  .p pv2 [pv2,pv3,pv89,pv1831], .c 3, .c 7, .c 5, .c 3, .c 937, .p pv17 [pv2,pv3,pv5,pv7,pv97],
  .c 3, .c 5, .c 7, .c 3, .p pv13 [pv2,pv5,pv283,pv691], .p pv2 [pv2,pv3,pv107,pv1523], .c 3,
  .c 19, .p pv2 [pv2,pv3,pv13,pv61,pv137], .c 3, .p pv5 [pv2,pv31,pv31541], .c 5, .c 3, .c 1151,
  .c 13, .c 3, .c 5, .c 29, .c 3, .c 17, .c 83, .c 3, .c 769, .c 7, .c 3, .c 31, .c 5, .c 3,
  .p pv2 [pv2,pv17,pv113,pv509], .c 499, .c 3, .c 5,
]
private theorem h0238c22 : checkBlock 1955331 128 b0238c22 = true := by
  decide +kernel

private def b0238c23 : List Row := [
  .p pv3 [pv2,pv3,pv29,pv11239], .c 3, .c 11, .p pv11 [pv2,pv3,pv157,pv173], .c 3, .c 7, .c 61,
  .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv244451], .c 7, .c 3, .c 5, .c 97, .c 3, .c 23, .c 47,
  .c 3, .c 557, .c 13, .c 3, .p pv3 [pv2,pv7,pv19,pv919], .c 5, .c 3, .c 7,
  .p pv17 [pv2,pv3,pv5,pv43,pv379], .c 3, .c 5, .c 53, .c 3, .c 19, .c 7, .c 3, .c 11, .c 41,
  .c 3, .c 17, .c 5, .c 3, .c 193, .p pv3 [pv2,pv3,pv5,pv19,pv47,pv73], .c 3, .c 5, .c 401, .c 3,
  .c 7, .c 43, .c 3, .p pv5 [pv2,pv89,pv10987], .c 19, .c 3, .p pv2 [pv2,pv347,pv1409], .c 5,
  .c 3, .c 131, .c 11, .c 3, .c 5, .c 13, .c 3, .p pv7 [pv2,pv5,pv223,pv877], .c 23, .c 3, .c 47,
  .c 1217, .c 3, .c 7, .c 5, .c 3, .c 83, .c 17, .c 3, .c 5, .c 7, .c 3, .c 41, .c 73, .c 3,
  .p pv2 [pv2,pv13,pv19,pv37,pv107], .c 157, .c 3, .c 53, .c 5, .c 3, .c 13,
  .p pv37 [pv2,pv3,pv5,pv29,pv281], .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv257,pv761],
  .p pv2 [pv2,pv3,pv7,pv13,pv199], .c 3, .p pv3 [pv2,pv30559], .c 7, .c 3, .c 37, .c 5, .c 3,
  .c 11, .c 59, .c 3, .c 5, .c 67, .c 3, .p pv3 [pv2,pv5,pv7,pv11,pv127], .c 19, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv6791], .c 3, .c 283, .c 5, .c 3, .p pv2 [pv2,pv29,pv33721], .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv12073], .c 3, .p pv11 [pv2,pv5,pv131,pv1493], .c 11, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv409,pv797], .c 3,
]
private theorem h0238c23 : checkBlock 1955587 128 b0238c23 = true := by
  decide +kernel

private def b0238c24 : List Row := [
  .c 61, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 37, .c 3, .c 433, .c 7, .c 3, .c 17, .c 139,
  .c 3, .p pv3 [pv2,pv61121], .c 5, .c 3, .c 19, .c 647, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv181,pv1801], .c 3, .c 7, .p pv5 [pv2,pv3,pv389,pv419], .c 3, .c 23, .c 11,
  .c 3, .c 151, .c 5, .c 3, .c 59, .c 1051, .c 3, .c 5, .c 19, .c 3, .c 11, .c 149, .c 3, .c 127,
  .c 853, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv173,pv5653], .c 13, .c 3, .c 5, .c 7, .c 3,
  .c 1097, .c 89, .c 3, .p pv2 [pv2,pv241,pv2029], .p pv11 [pv2,pv3,pv325993], .c 3, .c 29, .c 5,
  .c 3, .c 17, .c 199, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv31,pv239], .c 3, .c 383,
  .p pv17 [pv2,pv3,pv7,pv6653], .c 3, .c 11, .c 7, .c 3, .c 13, .c 5, .c 3, .c 47,
  .p pv41 [pv2,pv3,pv5,pv163], .c 3, .c 5, .c 31, .c 3, .p pv2 [pv2,pv5,pv7,pv27943], .c 197,
  .c 3, .c 7, .c 13, .c 3, .c 461, .c 5, .c 3, .p pv2 [pv2,pv41,pv11927], .c 7, .c 3, .c 5, .c 17,
  .c 3, .c 281, .c 251, .c 3, .p pv5 [pv2,pv47,pv20809], .p pv11 [pv2,pv3,pv40751], .c 3, .c 11,
  .c 5, .c 3, .c 7, .c 83, .c 3, .c 5, .c 101, .c 3, .c 13, .c 7, .c 3, .c 1319, .c 29, .c 3,
  .c 613, .c 5, .c 3, .p pv3 [pv2,pv17,pv19,pv757], .p pv2 [pv2,pv3,pv5,pv65203], .c 3, .c 5,
  .c 11,
]
private theorem h0238c24 : checkBlock 1955843 128 b0238c24 = true := by
  decide +kernel

private def b0238c25 : List Row := [
  .c 3, .c 7, .c 1013, .c 3, .c 19, .p pv23 [pv2,pv3,pv7,pv11,pv29,pv73], .c 3, .c 43, .c 5, .c 3,
  .c 11, .c 71, .c 3, .c 5, .c 23, .c 3, .c 31, .c 739, .c 3, .c 29, .c 17, .c 3, .c 7, .c 5,
  .c 3, .c 13, .c 41, .c 3, .c 5, .c 7, .c 3, .p pv17 [pv2,pv5,pv6113], .c 11, .c 3, .c 503,
  .p pv7 [pv2,pv3,pv101,pv269], .c 3, .c 17, .c 5, .c 3, .p pv7 [pv2,pv7,pv19961], .c 73, .c 3,
  .c 5, .c 47, .c 3, .c 359, .c 31, .c 3, .c 241, .c 7, .c 3, .p pv2 [pv2,pv19,pv51479], .c 5,
  .c 3, .c 61, .p pv2 [pv2,pv3,pv5,pv197,pv331], .c 3, .c 5, .p pv17 [pv2,pv3,pv81509], .c 3,
  .c 19, .c 109, .c 3, .c 7, .c 11, .c 3, .c 41, .c 5, .c 3, .p pv29 [pv2,pv167,pv5857], .c 7,
  .c 3, .c 5, .c 409, .c 3, .c 11, .c 13, .c 3, .p pv3 [pv2,pv113,pv541], .c 19, .c 3, .c 59,
  .c 5, .c 3, .c 7, .c 823, .c 3, .c 5, .c 79, .c 3, .c 47, .c 7, .c 3,
  .p pv5 [pv2,pv31,pv139,pv227], .p pv17 [pv2,pv3,pv23,pv443], .c 3, .c 449, .c 5, .c 3,
  .p pv2 [pv2,pv978149], .c 37, .c 3, .c 5, .c 593, .c 3, .c 7, .p pv5 [pv2,pv3,pv3019], .c 3,
  .c 11, .c 743, .c 3, .p pv5 [pv2,pv59,pv281], .c 5, .c 3, .p pv3 [pv2,pv11,pv43,pv47], .c 13,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv53,pv769], .c 3, .p pv2 [pv2,pv5,pv29,pv3373], .c 17, .c 3,
  .c 229, .c 271, .c 3, .c 7,
]
private theorem h0238c25 : checkBlock 1956099 128 b0238c25 = true := by
  decide +kernel

private def b0238c26 : List Row := [
  .c 5, .c 3, .p pv11 [pv2,pv978179], .c 11, .c 3, .c 5, .c 7, .c 3, .c 43, .c 19, .c 3, .c 17,
  .c 31, .c 3, .c 11, .c 5, .c 3, .c 53, .p pv41 [pv2,pv3,pv5,pv65213], .c 3, .c 5, .c 41, .c 3,
  .c 1321, .c 23, .c 3, .c 197, .c 7, .c 3, .c 191, .c 5, .c 3, .p pv2 [pv2,pv978209], .c 863,
  .c 3, .c 5, .c 11, .c 3, .p pv17 [pv2,pv5,pv7,pv19,pv1471], .p pv7 [pv2,pv3,pv40759], .c 3,
  .c 7, .p pv3 [pv2,pv3,pv11,pv41,pv241], .c 3, .c 821, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5,
  .c 43, .c 3, .c 13, .c 773, .c 3, .c 67, .c 47, .c 3, .c 73, .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv1019], .c 3, .c 5, .c 13, .c 3, .c 701, .c 7, .c 3, .c 137, .c 59, .c 3,
  .c 31, .c 5, .c 3, .c 953, .c 307, .c 3, .c 5, .p pv2 [pv2,pv3,pv47,pv3469], .c 3, .c 7, .c 37,
  .c 3, .p pv5 [pv2,pv11,pv13,pv6841], .p pv29 [pv2,pv3,pv7,pv647], .c 3, .p pv2 [pv2,pv489133],
  .c 5, .c 3, .c 13, .c 23, .c 3, .c 5, .c 17, .c 3, .c 919, .p pv5 [pv2,pv3,pv13,pv6271], .c 3,
  .c 1129, .c 11, .c 3, .c 7, .c 5, .c 3, .c 1213, .c 659, .c 3, .c 5, .c 7, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv19,pv1907], .c 3, .c 23, .p pv7 [pv2,pv3,pv103,pv1583], .c 3, .c 79, .c 5,
  .c 3, .p pv7 [pv2,pv7,pv17,pv8221], .c 19, .c 3, .c 5, .c 577, .c 3,
]
private theorem h0238c26 : checkBlock 1956355 128 b0238c26 = true := by
  decide +kernel

private def b0238c27 : List Row := [
  .p pv13 [pv2,pv5,pv23,pv47,pv181], .p pv2 [pv2,pv3,pv7,pv23293], .c 3, .c 13, .c 7, .c 3,
  .c 439, .c 5, .c 3, .c 43, .p pv3 [pv2,pv3,pv5,pv13,pv29,pv173], .c 3, .c 5,
  .p pv17 [pv2,pv3,pv11,pv61], .c 3, .c 1153, .c 13, .c 3, .c 7, .c 17, .c 3,
  .p pv2 [pv2,pv163,pv3001], .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv19183],
  .c 3, .c 37, .c 101, .c 3, .c 19, .c 23, .c 3, .c 17, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .c 61, .c 3, .c 881, .c 7, .c 3, .c 53, .c 107, .c 3, .c 11, .c 5, .c 3, .p pv7 [pv2,pv978359],
  .c 13, .c 3, .c 5, .c 433, .c 3, .c 7, .c 347, .c 3, .p pv3 [pv2,pv15287], .c 167, .c 3,
  .p pv5 [pv2,pv449,pv2179], .c 5, .c 3, .p pv2 [pv2,pv23,pv21269], .c 17, .c 3, .c 5, .c 11,
  .c 3, .p pv3 [pv2,pv5,pv13,pv53,pv71], .p pv37 [pv2,pv3,pv108709], .c 3, .c 199,
  .p pv7 [pv2,pv3,pv11,pv17,pv109], .c 3, .c 7, .c 5, .c 3, .c 11, .c 97, .c 3, .c 5, .c 7, .c 3,
  .c 19, .p pv5 [pv2,pv3,pv81533], .c 3, .c 541, .c 13, .c 3, .c 173, .c 5, .c 3, .c 151,
  .p pv2 [pv2,pv3,pv5,pv19,pv3433], .c 3, .c 5, .c 23, .c 3, .c 113, .c 11, .c 3, .c 193, .c 7,
  .c 3, .c 29, .c 5, .c 3, .p pv11 [pv2,pv13,pv73,pv1031], .c 317, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv326141], .c 3, .c 13, .c 17, .c 3, .c 7, .p pv2 [pv2,pv3,pv326143], .c 3,
  .c 23, .c 5,
]
private theorem h0238c27 : checkBlock 1956611 128 b0238c27 = true := by
  decide +kernel

private def b0238c28 : List Row := [
  .c 3, .c 67, .c 7, .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv61,pv401],
  .p pv3 [pv2,pv3,pv326147], .c 3, .c 17, .c 11, .c 3, .c 37, .c 5, .c 3, .c 7,
  .p pv17 [pv2,pv3,pv5,pv11,pv593], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv31,pv167], .c 3, .c 11,
  .c 7, .c 3, .c 1181, .c 53, .c 3, .c 107, .c 5, .c 3, .c 13, .c 977, .c 3, .c 5, .c 31, .c 3,
  .c 7, .c 19, .c 3, .c 293, .c 29, .c 3, .p pv3 [pv2,pv244619], .c 5, .c 3, .c 337,
  .p pv7 [pv2,pv3,pv5,pv151], .c 3, .c 5, .c 37, .c 3, .c 41, .c 43, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv23,pv29,pv163], .c 3, .c 7, .c 5, .c 3, .c 17,
  .p pv7 [pv2,pv3,pv5,pv7,pv9319], .c 3, .c 5, .c 7, .c 3, .c 23, .c 67, .c 3, .c 13, .c 131,
  .c 3, .p pv2 [pv2,pv41,pv11933], .c 5, .c 3, .c 19, .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv326171], .c 3, .p pv13 [pv2,pv5,pv31,pv59,pv107], .c 13, .c 3,
  .p pv2 [pv2,pv29,pv16871], .c 7, .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv223,pv1097],
  .p pv13 [pv2,pv3,pv5,pv4349], .c 3, .c 5, .c 17, .c 3, .c 31, .c 61, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv18121], .c 3, .c 167, .c 5, .c 3, .p pv13 [pv2,pv37,pv53,pv499], .c 7, .c 3,
  .c 5, .c 11, .c 3, .c 17, .c 23, .c 3, .p pv3 [pv2,pv244637], .p pv2 [pv2,pv3,pv11,pv13,pv2281],
  .c 3, .c 103, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv23,pv1013], .c 3,
  .p pv7 [pv2,pv5,pv11,pv139],
]
private theorem h0238c28 : checkBlock 1956867 128 b0238c28 = true := by
  decide +kernel

private def b0238c29 : List Row := [
  .c 7, .c 3, .c 47, .p pv7 [pv2,pv3,pv81547], .c 3, .c 19, .c 5, .c 3, .c 23, .c 163, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv79,pv4129], .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv379,pv1291], .c 17, .c 3,
  .c 13, .c 5, .c 3, .c 97, .c 19, .c 3, .c 5, .c 191, .c 3, .c 29, .c 1249, .c 3,
  .p pv2 [pv2,pv7,pv11,pv71,pv179], .c 13, .c 3, .c 7, .c 5, .c 3, .c 89, .c 1399, .c 3, .c 5,
  .c 7, .c 3, .c 367, .c 193, .c 3, .c 41, .c 11, .c 3, .c 83, .c 5, .c 3, .c 421, .c 23, .c 3,
  .c 5, .c 53, .c 3, .c 11, .p pv2 [pv2,pv3,pv7,pv46601], .c 3, .c 19, .c 7, .c 3, .c 487, .c 5,
  .c 3, .c 139, .c 17, .c 3, .c 5, .c 13, .c 3, .c 67, .c 113, .c 3, .c 7, .c 101, .c 3,
  .p pv2 [pv2,pv277,pv3533], .c 5, .c 3, .p pv3 [pv2,pv89,pv2749], .c 7, .c 3, .c 5, .c 29, .c 3,
  .p pv2 [pv2,pv5,pv23,pv37], .p pv3 [pv2,pv3,pv108739], .c 3, .c 11, .c 31, .c 3, .c 109, .c 5,
  .c 3, .c 7, .p pv23 [pv2,pv3,pv5,pv5437], .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv29,pv1607], .c 3,
  .c 457, .c 7, .c 3, .c 37, .c 1069, .c 3, .c 53, .c 5, .c 3, .c 73, .c 11, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv54371], .c 3, .c 7, .c 17, .c 3, .p pv5 [pv2,pv978683], .c 23, .c 3, .c 11,
  .c 5, .c 3,
]
private theorem h0238c29 : checkBlock 1957123 128 b0238c29 = true := by
  decide +kernel

private def b0238c30 : List Row := [
  .p pv2 [pv2,pv978689], .c 41, .c 3, .c 5, .c 839, .c 3, .p pv7 [pv2,pv5,pv195739], .c 937, .c 3,
  .c 13, .c 19, .c 3, .c 7, .c 5, .c 3, .c 47, .c 37, .c 3, .c 5, .c 7, .c 3, .c 227, .c 13, .c 3,
  .c 347, .c 61, .c 3, .c 31, .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv2039], .c 3, .c 5, .c 211,
  .c 3, .c 127, .p pv2 [pv2,pv3,pv7,pv3329], .c 3, .c 601, .c 7, .c 3, .c 41, .c 5, .c 3,
  .p pv2 [pv2,pv489367], .c 29, .c 3, .c 5, .p pv2 [pv2,pv3,pv157,pv1039], .c 3, .c 101, .c 11,
  .c 3, .c 7, .c 43, .c 3, .c 593, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 23, .c 3, .c 283,
  .c 19, .c 3, .p pv2 [pv2,pv11,pv17,pv2617], .p pv3 [pv2,pv3,pv108751], .c 3,
  .p pv2 [pv2,pv7,pv37,pv3779], .c 5, .c 3, .c 7, .c 109, .c 3, .c 5, .c 139, .c 3, .c 71, .c 7,
  .c 3, .p pv2 [pv2,pv978773], .c 11, .c 3, .c 13, .c 5, .c 3, .c 37, .c 59, .c 3, .c 5, .c 17,
  .c 3, .c 7, .p pv5 [pv2,pv3,pv54377], .c 3, .c 499, .c 13, .c 3, .p pv5 [pv2,pv11,pv101,pv881],
  .c 5, .c 3, .c 19, .p pv17 [pv2,pv3,pv5,pv21751], .c 3, .c 5, .c 47, .c 3, .c 17, .c 691, .c 3,
  .c 397, .c 887, .c 3, .c 7, .c 5, .c 3, .c 31, .p pv11 [pv2,pv3,pv5,pv7,pv59,pv79], .c 3, .c 5,
  .c 7, .c 3, .c 13, .c 37,
]
private theorem h0238c30 : checkBlock 1957379 128 b0238c30 = true := by
  decide +kernel

private def b0238c31 : List Row := [
  .c 3, .c 11, .p pv3 [pv2,pv3,pv83,pv3931], .c 3, .c 241, .c 5, .c 3, .c 239,
  .p pv11 [pv2,pv3,pv5,pv31,pv421], .c 3, .c 5, .c 13, .c 3, .c 43, .p pv7 [pv2,pv3,pv7,pv5179],
  .c 3, .p pv2 [pv2,pv233,pv4201], .c 7, .c 3, .c 61, .c 5, .c 3, .c 59, .c 11, .c 3, .c 5,
  .c 1087, .c 3, .c 23, .p pv5 [pv2,pv3,pv11,pv14831], .c 3, .c 7, .c 79, .c 3, .c 11, .c 5, .c 3,
  .c 13, .c 7, .c 3, .c 5, .c 223, .c 3, .c 83, .c 179, .c 3, .c 281, .p pv13 [pv2,pv3,pv20393],
  .c 3, .c 89, .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 11, .c 3, .c 97, .c 7, .c 3, .c 673,
  .p pv11 [pv2,pv3,pv11,pv29663], .c 3, .p pv2 [pv2,pv199,pv4919], .c 5, .c 3, .c 11, .c 17, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv40787], .c 3, .c 7, .c 23, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv7,pv17,pv457], .c 3, .c 163, .c 5, .c 3, .p pv7 [pv2,pv19,pv51521],
  .p pv7 [pv2,pv3,pv5,pv13,pv251], .c 3, .c 5, .c 67, .c 3, .c 727, .c 11, .c 3, .c 19, .c 29,
  .c 3, .c 7, .c 5, .c 3, .c 23, .p pv23 [pv2,pv3,pv5,pv7,pv9323], .c 3, .c 5, .c 7, .c 3, .c 173,
  .c 733, .c 3, .p pv5 [pv2,pv11,pv88993], .p pv7 [pv2,pv3,pv29,pv97], .c 3,
  .p pv2 [pv2,pv13,pv23,pv1637], .c 5, .c 3, .p pv2 [pv2,pv7,pv109,pv1283],
  .p pv17 [pv2,pv3,pv5,pv73,pv149], .c 3, .c 5, .c 31, .c 3, .p pv11 [pv2,pv5,pv195787], .c 17,
  .c 3, .c 29, .c 7, .c 3, .c 409, .c 5, .c 3, .c 659,
]
private theorem h0238c31 : checkBlock 1957635 128 b0238c31 = true := by
  decide +kernel

def rows0238 : List Row :=
  b0238c00 ++ b0238c01 ++ b0238c02 ++ b0238c03 ++ b0238c04 ++ b0238c05 ++ b0238c06 ++ b0238c07 ++
  b0238c08 ++ b0238c09 ++ b0238c10 ++ b0238c11 ++ b0238c12 ++ b0238c13 ++ b0238c14 ++ b0238c15 ++
  b0238c16 ++ b0238c17 ++ b0238c18 ++ b0238c19 ++ b0238c20 ++ b0238c21 ++ b0238c22 ++ b0238c23 ++
  b0238c24 ++ b0238c25 ++ b0238c26 ++ b0238c27 ++ b0238c28 ++ b0238c29 ++ b0238c30 ++ b0238c31

theorem checked0238 : checkBlock 1949699 4096 rows0238 = true :=
  checkBlock_append h0238c00 (
    checkBlock_append h0238c01 (
    checkBlock_append h0238c02 (
    checkBlock_append h0238c03 (
    checkBlock_append h0238c04 (
    checkBlock_append h0238c05 (
    checkBlock_append h0238c06 (
    checkBlock_append h0238c07 (
    checkBlock_append h0238c08 (
    checkBlock_append h0238c09 (
    checkBlock_append h0238c10 (
    checkBlock_append h0238c11 (
    checkBlock_append h0238c12 (
    checkBlock_append h0238c13 (
    checkBlock_append h0238c14 (
    checkBlock_append h0238c15 (
    checkBlock_append h0238c16 (
    checkBlock_append h0238c17 (
    checkBlock_append h0238c18 (
    checkBlock_append h0238c19 (
    checkBlock_append h0238c20 (
    checkBlock_append h0238c21 (
    checkBlock_append h0238c22 (
    checkBlock_append h0238c23 (
    checkBlock_append h0238c24 (
    checkBlock_append h0238c25 (
    checkBlock_append h0238c26 (
    checkBlock_append h0238c27 (
    checkBlock_append h0238c28 (
    checkBlock_append h0238c29 (
    checkBlock_append h0238c30 (
    h0238c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
