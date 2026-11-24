/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0145
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0145.checked0145
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table022
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table026
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table032
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table033
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table043
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table044
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table065
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table119

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0145c00 : List Row := [
  .c 67, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 11, .c 3, .c 19,
  .p pv3 [pv2,pv3,pv13,pv97,pv157], .c 3, .p pv2 [pv2,pv593933], .c 29, .c 3,
  .p pv5 [pv2,pv7,pv5303], .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv28283],
  .c 3, .c 227, .c 7, .c 3, .p pv3 [pv2,pv83,pv1789], .c 19, .c 3, .c 181, .c 5, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv5,pv67,pv197], .c 3, .c 5, .c 151, .c 3, .c 7, .c 11, .c 3, .c 13, .c 73,
  .c 3, .p pv2 [pv2,pv296983], .c 5, .c 3, .p pv2 [pv2,pv593969],
  .p pv2 [pv2,pv3,pv5,pv13,pv1523], .c 3, .c 5, .p pv2 [pv2,pv3,pv7333], .c 3, .c 31, .c 13, .c 3,
  .c 829, .c 37, .c 3, .c 7, .c 5, .c 3, .c 113, .c 263, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv59399], .c 251, .c 3, .c 821, .c 11, .c 3, .p pv3 [pv2,pv13,pv11423], .c 5,
  .c 3, .p pv7 [pv2,pv7,pv84857], .p pv7 [pv2,pv3,pv5,pv11], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv389,pv509], .c 3, .c 11, .c 19, .c 3, .p pv3 [pv2,pv41,pv1811], .c 7, .c 3,
  .c 179, .c 5, .c 3, .p pv3 [pv2,pv17,pv17471], .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv61,pv541],
  .c 3, .p pv11 [pv2,pv5,pv7,pv4243], .c 29, .c 3, .c 7, .p pv23 [pv2,pv3,pv53,pv467], .c 3,
  .c 277, .c 5, .c 3, .p pv2 [pv2,pv463,pv1283], .c 7, .c 3, .c 5, .c 233, .c 3,
  .p pv11 [pv2,pv5,pv13,pv19,pv37], .p pv5 [pv2,pv3,pv29,pv569], .c 3, .c 11, .c 17, .c 3, .c 13,
  .c 5, .c 3, .c 7, .c 1087, .c 3, .c 5, .c 61,
]
private theorem h0145c00 : checkBlock 1187843 128 b0145c00 = true := by
  decide +kernel

private def b0145c01 : List Row := [
  .c 3, .c 29, .c 7, .c 3, .c 37, .c 13, .c 3, .c 17, .c 5, .c 3, .c 499, .c 11, .c 3, .c 5,
  .c 19, .c 3, .c 7, .c 43, .c 3, .c 31, .c 41, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv73,pv313], .p pv3 [pv2,pv3,pv5,pv89], .c 3, .c 5, .c 23, .c 3, .c 13, .c 401,
  .c 3, .p pv5 [pv2,pv7,pv84869], .p pv29 [pv2,pv3,pv31,pv1597], .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv67,pv8867], .c 17, .c 3, .c 5, .c 7, .c 3, .c 929, .c 733, .c 3,
  .p pv2 [pv2,pv297049], .c 31, .c 3, .c 19, .c 5, .c 3, .c 11, .c 191, .c 3, .c 5, .c 29, .c 3,
  .c 41, .p pv3 [pv2,pv3,pv7,pv19,pv1489], .c 3, .p pv5 [pv2,pv13,pv23,pv1987], .c 7, .c 3,
  .p pv3 [pv2,pv17,pv8737], .c 5, .c 3, .c 13, .c 19, .c 3, .c 5, .p pv3 [pv2,pv3,pv29,pv6829],
  .c 3, .c 571, .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv198043], .c 3, .p pv5 [pv2,pv41,pv43,pv337],
  .c 5, .c 3, .p pv2 [pv2,pv297067], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv99023], .c 3, .c 229,
  .c 17, .c 3, .p pv5 [pv2,pv11,pv54013], .p pv13 [pv2,pv3,pv2063], .c 3,
  .p pv2 [pv2,pv7,pv31,pv37], .c 5, .c 3, .c 7, .c 47, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv9431],
  .c 3, .c 83, .c 7, .c 3, .c 13, .c 11, .c 3, .c 31, .c 5, .c 3, .c 37, .c 311, .c 3, .c 5,
  .c 173, .c 3, .c 7, .c 13, .c 3, .c 97, .c 281, .c 3, .p pv3 [pv2,pv11,pv211],
]
private theorem h0145c01 : checkBlock 1188099 128 b0145c01 = true := by
  decide +kernel

private def b0145c02 : List Row := [
  .c 5, .c 3, .p pv7 [pv2,pv594179], .p pv17 [pv2,pv3,pv5,pv3301], .c 3, .c 5, .c 73, .c 3,
  .c 241, .c 439, .c 3, .p pv3 [pv2,pv7,pv21221], .c 67, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv297097], .c 29, .c 3, .c 5, .c 7, .c 3, .c 521, .c 37, .c 3, .c 11,
  .p pv17 [pv2,pv3,pv13,pv293], .c 3, .p pv2 [pv2,pv19,pv823], .c 5, .c 3, .c 17, .c 13, .c 3,
  .c 5, .c 109, .c 3, .c 19, .c 23, .c 3, .c 59, .c 7, .c 3, .c 967, .c 5, .c 3, .c 29, .c 11,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv23,pv2153], .c 3, .c 313, .c 61, .c 3, .c 7, .c 19, .c 3, .c 11,
  .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv157,pv757], .c 563, .c 3,
  .c 263, .c 13, .c 3, .c 449, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv173,pv229], .c 3, .c 5,
  .c 11, .c 3, .c 17, .c 7, .c 3, .p pv5 [pv2,pv19,pv31277], .p pv7 [pv2,pv3,pv11,pv2251], .c 3,
  .c 233, .c 5, .c 3, .c 11, .c 97, .c 3, .c 5, .c 239, .c 3, .c 7, .p pv5 [pv2,pv3,pv49523],
  .c 3, .p pv2 [pv2,pv107,pv2777], .p pv7 [pv2,pv3,pv7,pv9433], .c 3, .c 43, .c 5, .c 3, .c 443,
  .c 23, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv67,pv887], .c 11, .c 3,
  .p pv2 [pv2,pv7,pv73,pv1163], .c 17, .c 3, .c 7, .c 5, .c 3, .c 337,
  .p pv11 [pv2,pv3,pv5,pv7,pv283], .c 3, .c 5, .c 7, .c 3,
]
private theorem h0145c02 : checkBlock 1188355 128 b0145c02 = true := by
  decide +kernel

private def b0145c03 : List Row := [
  .c 71, .p pv2 [pv2,pv3,pv137,pv241], .c 3, .c 23, .p pv3 [pv2,pv3,pv397,pv499], .c 3, .c 17,
  .c 5, .c 3, .c 13, .c 41, .c 3, .c 5, .p pv5 [pv2,pv3,pv99053], .c 3, .c 569, .c 83, .c 3,
  .c 67, .c 7, .c 3, .p pv2 [pv2,pv29,pv10247], .c 5, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv5,pv11,pv1801], .c 3, .c 5, .p pv2 [pv2,pv3,pv66037], .c 3, .c 11, .c 59,
  .c 3, .c 7, .p pv7 [pv2,pv3,pv19,pv10427], .c 3, .c 173, .c 5, .c 3, .p pv3 [pv2,pv74293], .c 7,
  .c 3, .c 5, .c 19, .c 3, .c 293, .c 419, .c 3, .c 13, .c 23, .c 3, .c 41, .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv13,pv127], .c 3, .c 5, .p pv11 [pv2,pv3,pv7,pv11,pv31,pv83], .c 3,
  .p pv2 [pv2,pv5,pv118873], .c 7, .c 3, .c 11, .c 29, .c 3, .c 1031, .c 5, .c 3, .c 137, .c 373,
  .c 3, .c 5, .c 31, .c 3, .c 7, .p pv11 [pv2,pv3,pv198127], .c 3, .c 487,
  .p pv11 [pv2,pv3,pv7,pv29,pv61], .c 3, .c 19, .c 5, .c 3, .c 523, .c 11, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv239,pv829], .c 3, .c 59, .c 17, .c 3, .c 29, .c 227, .c 3, .c 7, .c 5, .c 3,
  .c 83, .c 13, .c 3, .c 5, .c 7, .c 3, .c 43, .c 151, .c 3, .c 17, .c 61, .c 3, .c 751, .c 5,
  .c 3, .p pv7 [pv2,pv7,pv1733], .p pv7 [pv2,pv3,pv5,pv9907], .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv13,pv31,pv59], .c 241, .c 3, .p pv3 [pv2,pv173,pv859], .c 7, .c 3, .c 13,
  .c 5,
]
private theorem h0145c03 : checkBlock 1188611 128 b0145c03 = true := by
  decide +kernel

private def b0145c04 : List Row := [
  .c 3, .c 11, .c 79, .c 3, .c 5, .c 41, .c 3, .c 31, .c 283, .c 3, .c 7, .c 13, .c 3, .c 23,
  .c 5, .c 3, .p pv2 [pv2,pv594449], .c 7, .c 3, .c 5, .c 43, .c 3, .c 281, .c 11, .c 3,
  .p pv2 [pv2,pv23,pv12923], .c 461, .c 3, .c 379, .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv39631],
  .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv337], .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv11,pv17], .c 53,
  .c 3, .c 311, .c 5, .c 3, .c 41, .c 157, .c 3, .c 5, .c 13, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv101,pv109], .c 3, .p pv3 [pv2,pv74311], .c 11, .c 3, .c 1033, .c 5, .c 3,
  .c 181, .p pv3 [pv2,pv3,pv5,pv11,pv1201], .c 3, .c 5, .c 17, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv53,pv3739], .c 3, .p pv5 [pv2,pv7,pv13,pv47,pv139], .c 977, .c 3, .c 7, .c 5,
  .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv7,pv19,pv149], .c 3, .c 5, .c 7, .c 3, .c 17,
  .p pv7 [pv2,pv3,pv13,pv37,pv103], .c 3, .c 71, .c 19, .c 3, .c 349, .c 5, .c 3, .c 67, .c 739,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv563], .c 3, .p pv2 [pv2,pv5,pv59453],
  .p pv3 [pv2,pv3,pv7,pv9437], .c 3, .c 11, .c 7, .c 3, .c 61, .c 5, .c 3, .c 43, .c 109, .c 3,
  .c 5, .c 29, .c 3, .c 107, .p pv2 [pv2,pv3,pv197,pv503], .c 3, .c 7, .c 17, .c 3, .c 683, .c 5,
  .c 3, .p pv2 [pv2,pv53,pv71,pv79], .c 7, .c 3, .c 5, .c 499, .c 3, .p pv3 [pv2,pv5,pv929],
]
private theorem h0145c04 : checkBlock 1188867 128 b0145c04 = true := by
  decide +kernel

private def b0145c05 : List Row := [
  .c 13, .c 3, .p pv5 [pv2,pv594563], .c 31, .c 3, .c 11, .c 5, .c 3, .c 7, .c 83, .c 3, .c 5,
  .c 47, .c 3, .p pv19 [pv2,pv5,pv17,pv1399], .c 7, .c 3, .c 787, .p pv3 [pv2,pv3,pv198193], .c 3,
  .p pv2 [pv2,pv13,pv45737], .c 5, .c 3, .c 23, .p pv2 [pv2,pv3,pv5,pv73,pv181], .c 3, .c 5,
  .c 11, .c 3, .c 7, .c 67, .c 3, .c 79, .p pv2 [pv2,pv3,pv7,pv11,pv13], .c 3,
  .p pv3 [pv2,pv23,pv281], .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 167, .c 3, .c 691,
  .p pv2 [pv2,pv3,pv113,pv877], .c 3, .c 37, .p pv3 [pv2,pv3,pv17,pv89,pv131], .c 3, .c 7, .c 5,
  .c 3, .c 19, .p pv3 [pv2,pv3,pv5,pv7,pv809], .c 3, .c 5, .c 7, .c 3, .c 47, .c 11, .c 3, .c 757,
  .c 269, .c 3, .c 13, .c 5, .c 3, .c 223, .c 23, .c 3, .c 5, .c 19, .c 3,
  .p pv13 [pv2,pv5,pv118927], .c 337, .c 3, .p pv2 [pv2,pv11,pv151,pv179], .c 7, .c 3, .c 331,
  .c 5, .c 3, .c 197, .c 37, .c 3, .c 5, .c 137, .c 3, .p pv3 [pv2,pv5,pv7,pv1699], .c 17, .c 3,
  .c 7, .c 11, .c 3, .p pv3 [pv2,pv18583], .c 5, .c 3, .c 29, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv198221], .c 3, .c 11, .p pv2 [pv2,pv3,pv33037], .c 3, .c 17,
  .p pv3 [pv2,pv3,pv198223], .c 3, .c 19, .c 5, .c 3, .c 7, .c 181, .c 3, .c 5, .c 13, .c 3,
  .p pv3 [pv2,pv5,pv14867], .c 7, .c 3, .c 359, .c 41, .c 3, .c 53, .c 5, .c 3,
]
private theorem h0145c05 : checkBlock 1189123 128 b0145c05 = true := by
  decide +kernel

private def b0145c06 : List Row := [
  .c 601, .c 19, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv6007], .c 3, .c 7, .c 571, .c 3, .c 11, .c 23,
  .c 3, .p pv2 [pv2,pv37,pv16073], .c 5, .c 3, .c 13, .c 163, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv49559], .c 3, .c 997, .c 43, .c 3, .c 151, .c 47, .c 3, .c 7, .c 5, .c 3,
  .c 17, .c 11, .c 3, .c 5, .c 7, .c 3, .c 41, .p pv5 [pv2,pv3,pv11,pv9011], .c 3, .c 19, .c 193,
  .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv7,pv23,pv1847], .p pv31 [pv2,pv3,pv5,pv31,pv1279], .c 3,
  .c 5, .c 101, .c 3, .p pv7 [pv2,pv5,pv131,pv227], .p pv2 [pv2,pv3,pv7,pv127,pv223], .c 3, .c 13,
  .c 7, .c 3, .c 29, .c 5, .c 3, .c 59, .c 31, .c 3, .c 5, .c 11, .c 3, .c 97, .c 13, .c 3, .c 7,
  .c 107, .c 3, .c 47, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 23, .c 3, .c 17, .c 743, .c 3,
  .c 103, .c 263, .c 3, .p pv3 [pv2,pv7,pv13,pv19,pv43], .c 5, .c 3, .c 7, .c 61, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv7,pv1049], .c 3, .c 19, .c 7, .c 3, .p pv3 [pv2,pv241,pv617],
  .p pv2 [pv2,pv3,pv13,pv101,pv151], .c 3, .c 23, .c 5, .c 3, .c 157, .c 13, .c 3, .c 5, .c 701,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv66089], .c 3, .p pv5 [pv2,pv11,pv23,pv2351], .c 17, .c 3,
  .p pv2 [pv2,pv297403], .c 5, .c 3, .c 563, .p pv2 [pv2,pv3,pv5,pv2203], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv17,pv107,pv109], .c 3, .p pv7 [pv2,pv5,pv13,pv9151], .p pv17 [pv2,pv3,pv1549],
]
private theorem h0145c06 : checkBlock 1189379 128 b0145c06 = true := by
  decide +kernel

private def b0145c07 : List Row := [
  .c 3, .p pv2 [pv2,pv7,pv42487], .c 11, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv74353],
  .p pv11 [pv2,pv3,pv5,pv7,pv11,pv103], .c 3, .c 5, .c 7, .c 3, .c 11, .c 89, .c 3, .c 29, .c 13,
  .c 3, .p pv3 [pv2,pv11,pv1229], .c 5, .c 3, .c 101, .c 43, .c 3, .c 5, .c 31, .c 3, .c 53,
  .c 491, .c 3, .c 41, .c 7, .c 3, .p pv5 [pv2,pv709,pv839], .c 5, .c 3,
  .p pv2 [pv2,pv13,pv137,pv167], .c 17, .c 3, .c 5, .p pv19 [pv2,pv3,pv11,pv9013], .c 3, .c 13,
  .c 19, .c 3, .c 7, .c 151, .c 3, .c 107, .c 5, .c 3, .c 191, .c 7, .c 3, .c 5, .c 13, .c 3,
  .p pv17 [pv2,pv5,pv4759], .c 103, .c 3, .p pv2 [pv2,pv297439], .p pv3 [pv2,pv3,pv47,pv4219],
  .c 3, .p pv2 [pv2,pv7,pv17,pv4999], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 113, .c 3, .c 409,
  .c 7, .c 3, .c 269, .p pv2 [pv2,pv3,pv99149], .c 3, .c 11, .c 5, .c 3, .c 13,
  .p pv17 [pv2,pv3,pv5,pv661], .c 3, .c 5, .p pv3 [pv2,pv3,pv198301], .c 3, .c 7, .c 17, .c 3,
  .c 241, .c 79, .c 3, .p pv5 [pv2,pv594911], .c 5, .c 3, .c 211,
  .p pv3 [pv2,pv3,pv5,pv17,pv2333], .c 3, .c 5, .c 11, .c 3, .c 29, .p pv2 [pv2,pv3,pv31,pv6397],
  .c 3, .c 17, .c 587, .c 3, .c 7, .c 5, .c 3, .c 11, .c 41, .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv11,pv29,pv373], .c 31, .c 3, .c 13, .p pv11 [pv2,pv3,pv198313], .c 3, .c 37,
  .c 5, .c 3, .c 71,
]
private theorem h0145c07 : checkBlock 1189635 128 b0145c07 = true := by
  decide +kernel

private def b0145c08 : List Row := [
  .p pv19 [pv2,pv3,pv5,pv13,pv113], .c 3, .c 5, .p pv5 [pv2,pv3,pv43,pv1153], .c 3,
  .p pv2 [pv2,pv5,pv73,pv163], .c 11, .c 3, .p pv2 [pv2,pv594953], .c 7, .c 3, .c 19, .c 5, .c 3,
  .p pv11 [pv2,pv594959], .c 797, .c 3, .c 5, .c 61, .c 3, .c 233,
  .p pv2 [pv2,pv3,pv17,pv19,pv307], .c 3, .c 7, .c 43, .c 3, .c 41, .c 5, .c 3, .c 17, .c 7, .c 3,
  .c 5, .c 29, .c 3, .c 271, .c 353, .c 3, .p pv5 [pv2,pv17,pv31,pv1129], .c 11, .c 3, .c 73,
  .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 67, .c 3, .c 11, .c 7, .c 3, .c 23,
  .p pv3 [pv2,pv3,pv22037], .c 3, .c 113, .c 5, .c 3, .c 53, .p pv7 [pv2,pv3,pv5,pv39667], .c 3,
  .c 5, .c 17, .c 3, .c 7, .p pv3 [pv2,pv3,pv198337], .c 3, .c 19,
  .p pv2 [pv2,pv3,pv7,pv31,pv457], .c 3, .c 13, .c 5, .c 3, .c 809,
  .p pv7 [pv2,pv3,pv5,pv47,pv211], .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv13,pv19,pv73], .c 3, .c 17,
  .c 827, .c 3, .c 11, .c 13, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv11,pv17,pv37,pv43],
  .p pv7 [pv2,pv3,pv5,pv7,pv1889], .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv3719], .c 101, .c 3,
  .c 47, .c 23, .c 3, .c 97, .c 5, .c 3, .c 727, .c 11, .c 3, .c 5, .c 41, .c 3, .c 13, .c 229,
  .c 3, .c 127, .c 7, .c 3, .c 11, .c 5, .c 3, .c 439, .c 29, .c 3, .c 5, .c 13, .c 3, .c 19,
  .p pv5 [pv2,pv3,pv37,pv1787], .c 3,
]
private theorem h0145c08 : checkBlock 1189891 128 b0145c08 = true := by
  decide +kernel

private def b0145c09 : List Row := [
  .c 7, .p pv2 [pv2,pv3,pv41,pv59], .c 3, .c 17, .c 5, .c 3, .p pv11 [pv2,pv23,pv25873], .c 7,
  .c 3, .c 5, .c 11, .c 3, .c 61, .c 71, .c 3, .p pv5 [pv2,pv13,pv2861], .c 19, .c 3, .c 31, .c 5,
  .c 3, .c 7, .c 991, .c 3, .c 5, .c 43, .c 3, .p pv7 [pv2,pv5,pv11,pv541], .c 7, .c 3, .c 59,
  .c 167, .c 3, .c 599, .c 5, .c 3, .c 199, .c 17, .c 3, .c 5, .c 23, .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv19,pv15661], .c 307, .c 3, .c 373, .c 5, .c 3, .p pv3 [pv2,pv148781], .c 211,
  .c 3, .c 5, .c 139, .c 3, .p pv2 [pv2,pv5,pv59513], .p pv5 [pv2,pv3,pv198377], .c 3, .c 13,
  .c 277, .c 3, .c 7, .c 5, .c 3, .p pv17 [pv2,pv595139], .c 1091, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv37,pv3217], .c 13, .c 3, .c 953, .c 11, .c 3, .c 83, .c 5, .c 3, .c 557,
  .p pv11 [pv2,pv3,pv5,pv11,pv3607], .c 3, .c 5, .c 433, .c 3, .c 11, .c 17, .c 3, .c 37, .c 7,
  .c 3, .c 151, .c 5, .c 3, .c 313, .c 443, .c 3, .c 5, .p pv2 [pv2,pv3,pv198391], .c 3, .c 577,
  .c 41, .c 3, .c 7, .p pv3 [pv2,pv3,pv13,pv5087], .c 3, .c 29, .c 5, .c 3, .c 19, .c 7, .c 3,
  .c 5, .c 967, .c 3, .p pv2 [pv2,pv5,pv53,pv1123], .c 467, .c 3, .c 11, .c 67, .c 3, .c 137,
  .c 5, .c 3, .c 7, .c 37,
]
private theorem h0145c09 : checkBlock 1190147 128 b0145c09 = true := by
  decide +kernel

private def b0145c10 : List Row := [
  .c 3, .c 5, .c 19, .c 3, .c 23, .c 7, .c 3, .p pv3 [pv2,pv47,pv1583], .c 653, .c 3, .c 13, .c 5,
  .c 3, .p pv2 [pv2,pv297607], .c 11, .c 3, .c 5, .c 181, .c 3, .c 7, .c 59, .c 3,
  .p pv5 [pv2,pv613,pv971], .c 13, .c 3, .c 11, .c 5, .c 3, .c 17, .c 661, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv66137], .c 3, .c 197, .p pv17 [pv2,pv3,pv49603], .c 3,
  .p pv2 [pv2,pv7,pv17,pv41,pv61], .c 29, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv13,pv11447],
  .p pv2 [pv2,pv3,pv5,pv7,pv5669], .c 3, .c 5, .c 7, .c 3, .c 13, .c 23, .c 3,
  .p pv2 [pv2,pv595253], .p pv2 [pv2,pv3,pv11,pv29,pv311], .c 3, .p pv3 [pv2,pv37,pv2011], .c 5,
  .c 3, .c 11, .c 19, .c 3, .c 5, .c 13, .c 3, .c 157, .p pv17 [pv2,pv3,pv7,pv14173], .c 3, .c 29,
  .c 7, .c 3, .c 167, .c 5, .c 3, .c 23, .c 509, .c 3, .c 5, .c 47, .c 3, .c 17, .c 11, .c 3,
  .c 7, .c 401, .c 3, .p pv2 [pv2,pv23,pv12941], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv31,pv37,pv173], .c 3, .p pv31 [pv2,pv5,pv67,pv1777], .c 691, .c 3, .c 19,
  .c 41, .c 3, .c 397, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv13229], .c 3, .c 5, .c 31, .c 3,
  .c 337, .c 7, .c 3, .c 43, .c 11, .c 3, .p pv3 [pv2,pv148829], .c 5, .c 3,
  .p pv7 [pv2,pv595319], .c 23, .c 3, .c 5, .p pv23 [pv2,pv3,pv17,pv1297], .c 3, .c 7, .c 29,
  .c 3, .c 13,
]
private theorem h0145c10 : checkBlock 1190403 128 b0145c10 = true := by
  decide +kernel

private def b0145c11 : List Row := [
  .c 61, .c 3, .c 17, .c 5, .c 3, .c 353, .p pv11 [pv2,pv3,pv5,pv13,pv43,pv71], .c 3, .c 5,
  .c 911, .c 3, .c 41, .c 13, .c 3, .c 23, .c 101, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv47,pv53,pv239], .p pv11 [pv2,pv3,pv5,pv7], .c 3, .c 5, .c 7, .c 3, .c 19, .c 43,
  .c 3, .c 11, .p pv3 [pv2,pv3,pv83,pv797], .c 3, .p pv2 [pv2,pv13,pv41,pv1117], .c 5, .c 3,
  .c 389, .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv8269], .c 3, .c 31, .p pv3 [pv2,pv3,pv7,pv28351],
  .c 3, .c 383, .c 7, .c 3, .p pv3 [pv2,pv127,pv293], .c 5, .c 3, .c 173, .c 11, .c 3, .c 5,
  .c 79, .c 3, .c 37, .p pv5 [pv2,pv3,pv11,pv31,pv97], .c 3, .c 7, .c 23, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv349,pv853], .c 7, .c 3, .c 5, .c 59, .c 3, .c 83, .c 31, .c 3,
  .p pv5 [pv2,pv19,pv31337], .p pv17 [pv2,pv3,pv37,pv149], .c 3, .c 13, .c 5, .c 3, .c 7,
  .p pv17 [pv2,pv3,pv5,pv89,pv223], .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv119083], .c 7,
  .c 3, .p pv2 [pv2,pv463,pv643], .c 13, .c 3, .c 677, .c 5, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv5,pv17,pv467], .c 3, .c 5, .c 53, .c 3, .c 7, .c 19, .c 3, .c 17, .c 97, .c 3,
  .p pv3 [pv2,pv148859], .c 5, .c 3, .c 127, .c 823, .c 3, .c 5, .c 179, .c 3, .c 13, .c 11, .c 3,
  .p pv3 [pv2,pv7,pv31], .p pv2 [pv2,pv3,pv66161], .c 3, .c 7, .c 5, .c 3, .c 89,
  .p pv7 [pv2,pv3,pv5,pv7,pv53,pv107], .c 3,
]
private theorem h0145c11 : checkBlock 1190659 128 b0145c11 = true := by
  decide +kernel

private def b0145c12 : List Row := [
  .c 5, .c 7, .c 3, .c 131, .p pv2 [pv2,pv3,pv73,pv2719], .c 3, .c 31,
  .p pv7 [pv2,pv3,pv43,pv577], .c 3, .c 47, .c 5, .c 3, .c 19, .c 137, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv198491], .c 3, .p pv37 [pv2,pv5,pv23819], .p pv19 [pv2,pv3,pv7,pv17,pv139],
  .c 3, .c 149, .c 7, .c 3, .c 23, .c 5, .c 3, .c 13, .c 43, .c 3, .c 5, .c 19, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv13,pv15269], .c 3, .c 7, .c 31, .c 3, .c 37, .c 5, .c 3, .c 701, .c 7, .c 3,
  .c 5, .c 439, .c 3, .p pv2 [pv2,pv5,pv119101], .p pv2 [pv2,pv3,pv99251], .c 3, .c 107,
  .p pv2 [pv2,pv3,pv198503], .c 3, .c 587, .c 5, .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv29,pv37],
  .c 3, .c 5, .c 17, .c 3, .c 163, .c 7, .c 3, .c 11, .c 1033, .c 3, .c 19, .c 5, .c 3, .c 29,
  .p pv17 [pv2,pv3,pv5,pv13,pv509], .c 3, .c 5, .c 37, .c 3, .c 7, .c 13, .c 3,
  .p pv2 [pv2,pv191,pv1559], .p pv3 [pv2,pv3,pv7,pv23,pv137], .c 3, .c 79, .c 5, .c 3,
  .p pv3 [pv2,pv17,pv29,pv151], .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv71,pv233], .c 3, .c 23,
  .p pv3 [pv2,pv3,pv11,pv18047], .c 3, .p pv5 [pv2,pv7,pv149,pv571], .p pv7 [pv2,pv3,pv99259],
  .c 3, .c 7, .c 5, .c 3, .p pv13 [pv2,pv389,pv1531], .c 47, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv311,pv383], .c 83, .c 3, .c 349, .c 17, .c 3, .c 43, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv19,pv2239], .c 13, .c 3, .c 5, .c 11, .c 3, .c 181,
  .p pv3 [pv2,pv3,pv7,pv79,pv359], .c 3, .c 19, .c 7,
]
private theorem h0145c12 : checkBlock 1190915 128 b0145c12 = true := by
  decide +kernel

private def b0145c13 : List Row := [
  .c 3, .c 17, .c 5, .c 3, .c 11, .c 769, .c 3, .c 5, .p pv3 [pv2,pv3,pv19,pv43], .c 3,
  .p pv11 [pv2,pv5,pv7,pv11,pv13,pv17], .c 23, .c 3, .c 7, .p pv3 [pv2,pv3,pv198533], .c 3, .c 13,
  .c 5, .c 3, .p pv3 [pv2,pv61,pv2441], .c 7, .c 3, .c 5, .c 419, .c 3, .p pv3 [pv2,pv5,pv59561],
  .c 11, .c 3, .c 443, .c 13, .c 3, .c 29, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv113,pv251], .c 3, .c 347, .c 7, .c 3, .c 97, .c 197, .c 3, .c 241, .c 5,
  .c 3, .c 59, .c 821, .c 3, .c 5, .p pv2 [pv2,pv3,pv33091], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv367,pv541], .c 3, .c 73, .c 11, .c 3, .p pv2 [pv2,pv17,pv17519], .c 5, .c 3,
  .c 31, .p pv2 [pv2,pv3,pv5,pv11,pv19], .c 3, .c 5, .c 13, .c 3, .c 11, .p pv5 [pv2,pv3,pv8273],
  .c 3, .c 467, .c 19, .c 3, .c 7, .c 5, .c 3, .c 233, .c 23, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv59567], .c 17, .c 3, .p pv2 [pv2,pv13,pv45821], .c 29, .c 3,
  .p pv3 [pv2,pv137,pv1087], .c 5, .c 3, .c 13, .c 31, .c 3, .c 5, .c 163, .c 3, .c 401,
  .p pv11 [pv2,pv3,pv7,pv13,pv1091], .c 3, .c 11, .c 7, .c 3, .c 719, .c 5, .c 3, .c 193, .c 61,
  .c 3, .c 5, .c 397, .c 3, .c 43, .c 47, .c 3, .c 7, .p pv13 [pv2,pv3,pv24821], .c 3, .c 199,
  .c 5, .c 3, .c 41, .c 7, .c 3, .c 5,
]
private theorem h0145c13 : checkBlock 1191171 128 b0145c13 = true := by
  decide +kernel

private def b0145c14 : List Row := [
  .c 617, .c 3, .p pv13 [pv2,pv5,pv283,pv421], .c 19, .c 3, .c 13, .p pv3 [pv2,pv3,pv66191], .c 3,
  .c 11, .c 5, .c 3, .c 7, .c 71, .c 3, .c 5, .p pv23 [pv2,pv3,pv7,pv197], .c 3, .c 67, .c 7,
  .c 3, .c 307, .c 23, .c 3, .c 157, .c 5, .c 3, .c 17, .p pv19 [pv2,pv3,pv5,pv9929], .c 3, .c 5,
  .c 11, .c 3, .c 7, .c 53, .c 3, .c 47, .p pv7 [pv2,pv3,pv7,pv11,pv2579], .c 3, .c 1061, .c 5,
  .c 3, .c 11, .c 37, .c 3, .c 5, .c 211, .c 3, .c 359, .c 29, .c 3, .c 521,
  .p pv7 [pv2,pv3,pv13,pv19,pv67], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv23,pv25903], .c 13, .c 3,
  .c 5, .c 7, .c 3, .p pv19 [pv2,pv5,pv23831], .c 11, .c 3, .c 79, .p pv13 [pv2,pv3,pv198593],
  .c 3, .p pv2 [pv2,pv233,pv2557], .c 5, .c 3, .c 509, .p pv2 [pv2,pv3,pv5,pv39719], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv131,pv379], .c 3, .c 17, .c 41, .c 3, .c 271, .c 7, .c 3, .c 13, .c 5, .c 3,
  .c 53, .p pv7 [pv2,pv3,pv5,pv331], .c 3, .c 5, .c 23, .c 3, .p pv11 [pv2,pv5,pv7,pv29,pv587],
  .p pv7 [pv2,pv3,pv199,pv499], .c 3, .c 7, .c 11, .c 3, .c 19, .c 5, .c 3, .c 1009, .c 7, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv79,pv419], .c 3, .c 11, .p pv2 [pv2,pv3,pv19,pv10453], .c 3, .c 139,
  .c 17, .c 3, .c 23, .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv17,pv1669], .c 3,
  .c 13, .c 7, .c 3, .c 571, .p pv3 [pv2,pv3,pv198613], .c 3,
]
private theorem h0145c14 : checkBlock 1191427 128 b0145c14 = true := by
  decide +kernel

private def b0145c15 : List Row := [
  .c 17, .c 5, .c 3, .c 487, .p pv19 [pv2,pv3,pv5,pv13241], .c 3, .c 5, .c 13, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv31,pv43,pv149], .c 3, .c 11, .c 257, .c 3, .c 283, .c 5, .c 3,
  .p pv7 [pv2,pv11,pv19,pv2851], .c 281, .c 3, .c 5, .p pv3 [pv2,pv3,pv29,pv761], .c 3,
  .p pv13 [pv2,pv5,pv119173], .c 31, .c 3, .c 19, .p pv3 [pv2,pv3,pv198623], .c 3, .c 7, .c 5,
  .c 3, .c 13, .c 11, .c 3, .c 5, .c 7, .c 3, .p pv11 [pv2,pv5,pv14897], .c 137, .c 3,
  .p pv5 [pv2,pv107,pv5569], .p pv7 [pv2,pv3,pv17,pv23,pv127], .c 3, .c 11, .c 5, .c 3, .c 47,
  .p pv13 [pv2,pv3,pv5,pv2207], .c 3, .c 5, .c 157, .c 3, .c 23, .p pv59 [pv2,pv3,pv7,pv3547],
  .c 3, .c 83, .c 7, .c 3, .c 863, .c 5, .c 3, .p pv3 [pv2,pv9311], .c 53, .c 3, .c 5, .c 11,
  .c 3, .p pv2 [pv2,pv5,pv7,pv8513], .c 541, .c 3, .c 7, .c 41, .c 3, .p pv3 [pv2,pv19,pv7841],
  .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv198641], .c 3, .c 19, .c 13, .c 3, .c 31,
  .c 59, .c 3, .c 67, .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .c 71, .c 3, .c 37, .c 7, .c 3, .c 17,
  .c 19, .c 3, .c 239, .c 5, .c 3, .p pv2 [pv2,pv595949], .c 101, .c 3, .c 5, .c 929, .c 3, .c 7,
  .c 547, .c 3, .c 43, .c 31, .c 3, .p pv2 [pv2,pv595961], .c 5, .c 3, .c 23, .c 13, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv97],
]
private theorem h0145c15 : checkBlock 1191683 128 b0145c15 = true := by
  decide +kernel

private def b0145c16 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv61,pv977], .c 919, .c 3, .p pv2 [pv2,pv7,pv19,pv4481], .c 11, .c 3,
  .c 7, .c 5, .c 3, .c 631, .c 179, .c 3, .c 5, .c 7, .c 3, .c 11, .p pv2 [pv2,pv3,pv17,pv5843],
  .c 3, .c 59, .p pv2 [pv2,pv3,pv66221], .c 3, .c 13, .c 5, .c 3, .c 17,
  .p pv13 [pv2,pv3,pv5,pv39733], .c 3, .c 5, .c 67, .c 3, .c 61, .c 19, .c 3, .c 739, .c 7, .c 3,
  .p pv2 [pv2,pv31,pv9613], .c 5, .c 3, .c 71, .c 23, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv18061],
  .c 3, .c 79, .c 97, .c 3, .c 7, .p pv3 [pv2,pv3,pv198673], .c 3, .c 31, .c 5, .c 3, .c 433,
  .c 7, .c 3, .c 5, .c 17, .c 3, .c 13, .c 311, .c 3, .c 23, .p pv31 [pv2,pv3,pv33113], .c 3,
  .p pv3 [pv2,pv7,pv3041], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 13, .c 3, .c 17, .c 7, .c 3,
  .p pv3 [pv2,pv37253], .p pv2 [pv2,pv3,pv19,pv10457], .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv17,pv47,pv373], .c 499, .c 3, .c 5, .c 19, .c 3, .c 7, .c 61, .c 3,
  .p pv5 [pv2,pv13,pv3527], .c 53, .c 3, .c 109, .c 5, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv5,pv37,pv179], .c 3, .c 5, .c 11, .c 3, .p pv7 [pv2,pv5,pv113,pv211],
  .p pv11 [pv2,pv3,pv13,pv3821], .c 3, .c 41, .c 17, .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv7,pv811], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv11,pv5419],
  .p pv5 [pv2,pv3,pv23,pv53,pv163], .c 3, .p pv2 [pv2,pv596093], .c 79, .c 3, .c 17,
]
private theorem h0145c16 : checkBlock 1191939 128 b0145c16 = true := by
  decide +kernel

private def b0145c17 : List Row := [
  .c 5, .c 3, .p pv13 [pv2,pv7,pv31,pv41,pv67], .p pv7 [pv2,pv3,pv5,pv1987], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv198701], .c 3, .p pv2 [pv2,pv5,pv17,pv7013], .c 11, .c 3, .c 13, .c 7, .c 3,
  .c 257, .c 5, .c 3, .c 31, .c 19, .c 3, .c 5, .c 317, .c 3, .p pv3 [pv2,pv5,pv7,pv2129], .c 13,
  .c 3, .c 7, .c 47, .c 3, .p pv2 [pv2,pv298063], .c 5, .c 3, .p pv2 [pv2,pv157,pv3797], .c 7,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv22079], .c 3, .p pv11 [pv2,pv5,pv119227], .c 947, .c 3, .c 29,
  .c 11, .c 3, .c 281, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5, .c 23, .c 3, .c 11, .c 7, .c 3, .c 19,
  .c 73, .c 3, .c 457, .c 5, .c 3, .c 179, .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv19,pv10459], .c 3,
  .c 7, .c 89, .c 3, .p pv3 [pv2,pv74521], .p pv3 [pv2,pv3,pv7,pv9463], .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv298087], .c 109, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv3011], .c 3, .c 211, .c 17,
  .c 3, .c 11, .p pv7 [pv2,pv3,pv24841], .c 3, .c 7, .c 5, .c 3, .c 983, .c 223, .c 3, .c 5, .c 7,
  .c 3, .p pv7 [pv2,pv5,pv43,pv47,pv59], .c 29, .c 3, .c 17, .c 13, .c 3, .c 41, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv107,pv199], .c 11, .c 3, .c 5, .p pv11 [pv2,pv3,pv12421], .c 3, .c 19,
  .p pv3 [pv2,pv3,pv7,pv11,pv29,pv89], .c 3, .p pv2 [pv2,pv79,pv7547], .c 7, .c 3, .c 11, .c 5,
  .c 3, .c 1087, .c 197, .c 3, .c 5, .c 53, .c 3,
]
private theorem h0145c17 : checkBlock 1192195 128 b0145c17 = true := by
  decide +kernel

private def b0145c18 : List Row := [
  .c 13, .p pv17 [pv2,pv3,pv99371], .c 3, .c 7, .c 19, .c 3, .c 1091, .c 5, .c 3,
  .p pv2 [pv2,pv241,pv1237], .c 7, .c 3, .c 5, .c 11, .c 3, .c 23, .p pv3 [pv2,pv3,pv17,pv433],
  .c 3, .c 761, .c 61, .c 3, .c 131, .c 5, .c 3, .c 7, .c 251, .c 3, .c 5, .c 101, .c 3, .c 89,
  .c 7, .c 3, .p pv2 [pv2,pv13,pv17,pv19,pv71], .c 43, .c 3, .c 593, .c 5, .c 3, .c 13, .c 47,
  .c 3, .c 5, .c 557, .c 3, .c 7, .c 11, .c 3, .c 37, .p pv11 [pv2,pv3,pv7,pv14197], .c 3, .c 53,
  .c 5, .c 3, .p pv7 [pv2,pv596279], .p pv11 [pv2,pv3,pv5,pv4969], .c 3, .c 5, .c 17, .c 3,
  .p pv2 [pv2,pv5,pv31,pv3847], .c 19, .c 3, .c 431, .p pv2 [pv2,pv3,pv47,pv4229], .c 3, .c 7,
  .c 5, .c 3, .p pv2 [pv2,pv397,pv751], .c 733, .c 3, .c 5, .c 7, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv113,pv1759], .c 3, .c 13, .c 11, .c 3, .c 503, .c 5, .c 3, .c 23, .c 37, .c 3,
  .c 5, .c 83, .c 3, .c 11, .c 13, .c 3, .c 103, .c 7, .c 3, .c 337, .c 5, .c 3, .c 19,
  .p pv3 [pv2,pv3,pv5,pv7951], .c 3, .c 5, .c 127, .c 3, .c 617, .c 31, .c 3, .c 7, .c 17, .c 3,
  .p pv3 [pv2,pv13,pv47,pv61], .c 5, .c 3, .p pv11 [pv2,pv109,pv5471], .c 7, .c 3, .c 5, .c 19,
  .c 3, .c 43, .c 421, .c 3, .c 11, .p pv2 [pv2,pv3,pv13,pv1699], .c 3, .c 17, .c 5,
]
private theorem h0145c18 : checkBlock 1192451 128 b0145c18 = true := by
  decide +kernel

private def b0145c19 : List Row := [
  .c 3, .c 7, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv4733], .c 3, .p pv3 [pv2,pv5,pv17,pv877],
  .c 7, .c 3, .c 233, .c 71, .c 3, .c 61, .c 5, .c 3, .c 773, .c 11, .c 3, .c 5, .c 73, .c 3,
  .c 7, .p pv5 [pv2,pv3,pv11,pv251], .c 3, .c 23, .c 139, .c 3, .c 11, .c 5, .c 3, .c 37, .c 17,
  .c 3, .c 5, .c 43, .c 3, .p pv2 [pv2,pv5,pv23,pv2593], .c 211, .c 3, .c 31, .c 13, .c 3, .c 7,
  .c 5, .c 3, .c 29, .c 19, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv101,pv1181], .c 41, .c 3,
  .p pv3 [pv2,pv74551], .c 571, .c 3, .p pv5 [pv2,pv17,pv35083], .c 5, .c 3, .c 11,
  .p pv43 [pv2,pv3,pv5,pv39761], .c 3, .c 5, .p pv2 [pv2,pv3,pv107,pv929], .c 3, .c 13, .c 37,
  .c 3, .p pv5 [pv2,pv596423], .c 7, .c 3, .p pv2 [pv2,pv298213], .c 5, .c 3, .c 137, .c 229,
  .c 3, .c 5, .c 13, .c 3, .c 53, .c 11, .c 3, .c 7, .p pv3 [pv2,pv3,pv66271], .c 3,
  .p pv2 [pv2,pv349,pv1709], .c 5, .c 3, .p pv3 [pv2,pv149111], .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv19,pv109], .c 3, .c 641, .p pv3 [pv2,pv3,pv198817], .c 3, .c 17,
  .p pv41 [pv2,pv3,pv99409], .c 3, .c 821, .c 5, .c 3, .c 7, .c 59, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv28403], .c 3, .c 829, .c 7, .c 3, .p pv3 [pv2,pv41,pv3637], .c 11, .c 3,
  .c 107, .c 5, .c 3, .c 43, .p pv11 [pv2,pv3,pv5,pv11,pv241], .c 3, .c 5, .c 359, .c 3, .c 7,
]
private theorem h0145c19 : checkBlock 1192707 128 b0145c19 = true := by
  decide +kernel

private def b0145c20 : List Row := [
  .c 523, .c 3, .p pv5 [pv2,pv73,pv8171], .p pv17 [pv2,pv3,pv7,pv263], .c 3, .c 29, .c 5, .c 3,
  .c 79, .c 811, .c 3, .c 5, .c 23, .c 3, .c 19, .c 449, .c 3, .c 13, .c 443, .c 3, .c 7, .c 5,
  .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv7,pv13,pv19,pv23], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv59651], .c 13, .c 3, .c 11, .c 19, .c 3, .c 23, .c 5, .c 3, .c 59,
  .p pv7 [pv2,pv3,pv5,pv1657], .c 3, .c 5, .p pv3 [pv2,pv3,pv198841], .c 3, .c 151, .c 409, .c 3,
  .p pv3 [pv2,pv23,pv1621], .c 7, .c 3, .c 389, .c 5, .c 3, .c 67, .c 11, .c 3, .c 5, .c 17, .c 3,
  .p pv3 [pv2,pv5,pv7,pv4261], .c 53, .c 3, .c 7, .c 29, .c 3, .c 11, .c 5, .c 3, .c 61, .c 7,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv198851], .c 3, .c 17, .c 101, .c 3, .c 367,
  .p pv3 [pv2,pv3,pv29,pv6857], .c 3, .p pv2 [pv2,pv7,pv85223], .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv491], .c 3, .c 5, .c 11, .c 3, .c 41, .c 7, .c 3, .c 29,
  .p pv2 [pv2,pv3,pv11,pv23,pv131], .c 3, .c 13, .c 5, .c 3, .c 11,
  .p pv13 [pv2,pv3,pv5,pv61,pv163], .c 3, .c 5, .c 113, .c 3, .c 7, .p pv5 [pv2,pv3,pv99431],
  .c 3, .c 191, .c 13, .c 3, .p pv5 [pv2,pv41,pv14551], .c 5, .c 3, .c 47, .c 241, .c 3, .c 5,
  .c 97, .c 3, .c 683, .c 11, .c 3, .c 43, .p pv7 [pv2,pv3,pv83,pv599], .c 3, .c 7, .c 5, .c 3,
]
private theorem h0145c20 : checkBlock 1192963 128 b0145c20 = true := by
  decide +kernel

private def b0145c21 : List Row := [
  .c 19, .c 31, .c 3, .c 5, .c 7, .c 3, .c 13, .p pv5 [pv2,pv3,pv24859], .c 3,
  .p pv2 [pv2,pv11,pv47,pv577], .p pv3 [pv2,pv3,pv19,pv1163], .c 3, .p pv2 [pv2,pv53,pv11257],
  .c 5, .c 3, .c 1019, .c 257, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv59663], .c 23, .c 3,
  .p pv2 [pv2,pv596633], .c 7, .c 3, .c 223, .c 5, .c 3, .c 131, .c 17, .c 3, .c 5, .c 37, .c 3,
  .c 11, .c 43, .c 3, .c 7, .p pv3 [pv2,pv3,pv17,pv11699], .c 3, .p pv5 [pv2,pv11,pv4931], .c 5,
  .c 3, .c 13, .c 7, .c 3, .c 5, .c 337, .c 3, .c 29, .c 163, .c 3, .c 239,
  .p pv13 [pv2,pv3,pv8287], .c 3, .c 19, .c 5, .c 3, .c 7, .c 149, .c 3, .c 5, .c 853, .c 3,
  .p pv11 [pv2,pv5,pv29,pv823], .c 7, .c 3, .c 11, .c 971, .c 3, .p pv2 [pv2,pv607,pv983], .c 5,
  .c 3, .p pv3 [pv2,pv11,pv71,pv191], .c 19, .c 3, .c 5, .c 47, .c 3, .c 7, .c 17, .c 3, .c 13,
  .c 293, .c 3, .c 59, .c 5, .c 3, .p pv7 [pv2,pv37,pv16127], .c 11, .c 3, .c 5, .c 31, .c 3,
  .c 283, .c 13, .c 3, .c 17, .c 127, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv19,pv41,pv383],
  .p pv3 [pv2,pv3,pv5,pv7,pv5683], .c 3, .c 5, .c 7, .c 3, .c 109, .p pv2 [pv2,pv3,pv443,pv449],
  .c 3, .c 19, .c 659, .c 3, .c 79, .c 5, .c 3, .p pv2 [pv2,pv7,pv85247], .c 103, .c 3, .c 5,
  .c 11, .c 3, .c 47, .p pv5 [pv2,pv3,pv7,pv37],
]
private theorem h0145c21 : checkBlock 1193219 128 b0145c21 = true := by
  decide +kernel

private def b0145c22 : List Row := [
  .c 3, .c 73, .c 7, .c 3, .p pv2 [pv2,pv596741], .c 5, .c 3, .c 11, .c 13, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv223], .c 3, .p pv2 [pv2,pv5,pv7,pv11,pv31], .p pv3 [pv2,pv3,pv17,pv11701],
  .c 3, .c 7, .c 37, .c 3, .p pv3 [pv2,pv193,pv773], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 173,
  .c 3, .c 31, .c 11, .c 3, .p pv3 [pv2,pv17,pv1097], .c 23, .c 3, .c 13, .c 5, .c 3, .c 7, .c 41,
  .c 3, .c 5, .p pv11 [pv2,pv3,pv7,pv13,pv1093], .c 3, .c 19, .c 7, .c 3,
  .p pv5 [pv2,pv11,pv227,pv239], .c 13, .c 3, .p pv2 [pv2,pv179,pv1667], .c 5, .c 3, .c 89, .c 71,
  .c 3, .c 5, .c 17, .c 3, .c 7, .c 31, .c 3, .c 877, .c 11, .c 3, .p pv2 [pv2,pv199,pv2999],
  .c 5, .c 3, .p pv11 [pv2,pv13,pv23,pv499], .c 29, .c 3, .c 5, .p pv7 [pv2,pv3,pv307], .c 3,
  .c 11, .c 73, .c 3, .c 211, .c 59, .c 3, .c 7, .c 5, .c 3, .c 149, .c 439, .c 3, .c 5, .c 7,
  .c 3, .c 557, .p pv2 [pv2,pv3,pv71,pv467], .c 3, .c 37, .c 47, .c 3, .p pv5 [pv2,pv596831],
  .c 5, .c 3, .c 29, .c 157, .c 3, .c 5, .c 23, .c 3, .c 137, .p pv5 [pv2,pv3,pv7,pv97,pv293],
  .c 3, .c 11, .c 7, .c 3, .p pv2 [pv2,pv107,pv2789], .c 5, .c 3, .c 13,
  .p pv17 [pv2,pv3,pv5,pv23,pv173], .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv47,pv83], .c 3,
  .p pv17 [pv2,pv5,pv7,pv17053], .c 19, .c 3, .c 7, .c 53, .c 3, .c 17, .c 5, .c 3,
  .p pv3 [pv2,pv4663],
]
private theorem h0145c22 : checkBlock 1193475 128 b0145c22 = true := by
  decide +kernel

private def b0145c23 : List Row := [
  .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv49739], .c 3, .p pv2 [pv2,pv5,pv17,pv3511],
  .p pv11 [pv2,pv3,pv11,pv6029], .c 3, .c 59, .c 1063, .c 3, .c 11, .c 5, .c 3, .c 7,
  .p pv19 [pv2,pv3,pv5,pv829], .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv43,pv661], .c 3,
  .p pv2 [pv2,pv5,pv19,pv61,pv103], .c 7, .c 3, .c 13, .c 31, .c 3, .p pv5 [pv2,pv313,pv1907],
  .c 5, .c 3, .c 19, .c 17, .c 3, .c 5, .c 11, .c 3, .c 7, .c 13, .c 3, .c 599, .c 43, .c 3,
  .c 577, .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv101,pv197], .c 3, .c 5, .c 19, .c 3, .c 61,
  .p pv29 [pv2,pv3,pv5527], .c 3, .p pv2 [pv2,pv7,pv6091], .p pv3 [pv2,pv3,pv23,pv41,pv211], .c 3,
  .c 7, .c 5, .c 3, .p pv3 [pv2,pv79,pv1889], .c 367, .c 3, .c 5, .c 7, .c 3, .c 23, .c 11, .c 3,
  .p pv2 [pv2,pv596933], .p pv47 [pv2,pv3,pv13,pv2551], .c 3, .c 67, .c 5, .c 3, .c 37, .c 13,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv22109], .c 3, .c 449, .c 17, .c 3, .c 839, .c 7, .c 3, .c 19,
  .c 5, .c 3, .p pv2 [pv2,pv298477], .p pv3 [pv2,pv3,pv5,pv17,pv2341], .c 3, .c 5, .c 331, .c 3,
  .c 101, .c 307, .c 3, .c 7, .c 11, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv43,pv13883], .c 7,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv15307], .c 3, .c 11, .c 23, .c 3, .c 151, .c 13, .c 3,
  .p pv5 [pv2,pv7,pv11,pv7753], .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv39799], .c 3, .c 5,
  .c 283, .c 3, .c 43, .c 7, .c 3,
]
private theorem h0145c23 : checkBlock 1193731 128 b0145c23 = true := by
  decide +kernel

private def b0145c24 : List Row := [
  .c 541, .p pv2 [pv2,pv3,pv29,pv47,pv73], .c 3, .p pv3 [pv2,pv149249], .c 5, .c 3, .c 23, .c 743,
  .c 3, .c 5, .c 67, .c 3, .c 7, .c 107, .c 3, .c 11, .p pv7 [pv2,pv3,pv7,pv28429], .c 3,
  .p pv5 [pv2,pv23,pv101,pv257], .c 5, .c 3, .c 17, .p pv3 [pv2,pv3,pv5,pv13267], .c 3, .c 5,
  .c 13, .c 3, .p pv3 [pv2,pv5,pv29851], .c 41, .c 3, .p pv5 [pv2,pv7,pv17,pv29,pv173], .c 211,
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv31,pv19259], .c 11, .c 3, .c 5, .c 7, .c 3, .c 113,
  .c 1069, .c 3, .c 463, .c 103, .c 3, .c 11, .c 5, .c 3, .c 13, .c 23, .c 3, .c 5, .c 17, .c 3,
  .c 37, .p pv7 [pv2,pv3,pv7,pv13], .c 3, .c 499, .c 7, .c 3, .c 89, .c 5, .c 3, .c 467, .c 83,
  .c 3, .c 5, .c 11, .c 3, .c 17, .c 29, .c 3, .c 7, .c 317, .c 3, .c 53, .c 5, .c 3, .c 11, .c 7,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv11057], .c 3, .p pv3 [pv2,pv5,pv11,pv23,pv59],
  .p pv3 [pv2,pv3,pv29,pv6863], .c 3, .c 13, .c 19, .c 3, .c 823, .c 5, .c 3, .c 7, .c 127, .c 3,
  .c 5, .c 601, .c 3, .c 29, .c 7, .c 3, .c 61, .c 17, .c 3, .p pv2 [pv2,pv89,pv6709], .c 5, .c 3,
  .p pv3 [pv2,pv67,pv557], .p pv3 [pv2,pv3,pv5,pv4423], .c 3, .c 5, .c 167, .c 3, .c 7, .c 47,
  .c 3, .c 107, .c 23, .c 3, .c 17, .c 5, .c 3, .c 43, .p pv7 [pv2,pv3,pv5,pv311],
]
private theorem h0145c24 : checkBlock 1193987 128 b0145c24 = true := by
  decide +kernel

private def b0145c25 : List Row := [
  .c 3, .c 5, .c 227, .c 3, .p pv2 [pv2,pv5,pv17,pv281], .p pv5 [pv2,pv3,pv23,pv4327], .c 3,
  .c 769, .c 11, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv293,pv1019], .c 13, .c 3, .c 5, .c 7, .c 3,
  .c 11, .c 19, .c 3, .c 83, .c 41, .c 3, .p pv2 [pv2,pv11,pv27143], .c 5, .c 3, .c 157, .c 17,
  .c 3, .c 5, .c 29, .c 3, .p pv19 [pv2,pv5,pv13,pv9187], .c 109, .c 3, .c 47, .c 7, .c 3, .c 13,
  .c 5, .c 3, .p pv3 [pv2,pv337,pv443], .c 569, .c 3, .c 5, .c 31, .c 3,
  .p pv13 [pv2,pv5,pv7,pv19,pv449], .p pv5 [pv2,pv3,pv67,pv2971], .c 3, .c 7, .c 13, .c 3, .c 73,
  .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 23, .c 3, .c 41, .p pv2 [pv2,pv3,pv11059], .c 3, .c 421,
  .p pv2 [pv2,pv3,pv19,pv10477], .c 3, .p pv5 [pv2,pv7,pv85313], .c 5, .c 3, .c 7, .c 11, .c 3,
  .c 5, .c 19, .c 3, .c 13, .c 7, .c 3, .p pv5 [pv2,pv599,pv997], .c 67, .c 3, .c 11, .c 5, .c 3,
  .c 181, .p pv11 [pv2,pv3,pv5,pv17,pv1171], .c 3, .c 5, .c 13, .c 3, .c 7, .c 71, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv7,pv28439], .c 3, .p pv2 [pv2,pv597221], .c 5, .c 3, .p pv3 [pv2,pv74653],
  .c 461, .c 3, .c 5, .c 11, .c 3, .c 31, .p pv5 [pv2,pv3,pv66359], .c 3, .c 179, .c 89, .c 3,
  .c 7, .c 5, .c 3, .c 11, .c 29, .c 3, .c 5, .c 7, .c 3, .c 103,
  .p pv37 [pv2,pv3,pv13,pv19,pv31], .c 3, .c 43,
]
private theorem h0145c25 : checkBlock 1194243 128 b0145c25 = true := by
  decide +kernel

private def b0145c26 : List Row := [
  .c 73, .c 3, .c 137, .c 5, .c 3, .c 251, .c 19, .c 3, .c 5, .p pv2 [pv2,pv3,pv33181], .c 3,
  .p pv19 [pv2,pv5,pv29863], .c 11, .c 3, .c 101, .c 7, .c 3, .c 149, .c 5, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv5,pv43,pv463], .c 3, .c 5, .p pv2 [pv2,pv3,pv263,pv757], .c 3, .c 23,
  .p pv5 [pv2,pv3,pv47,pv353], .c 3, .c 7, .c 79, .c 3, .c 61, .c 5, .c 3, .c 419, .c 7, .c 3,
  .c 5, .c 383, .c 3, .p pv2 [pv2,pv5,pv59729], .c 13, .c 3, .c 19, .c 11, .c 3,
  .p pv5 [pv2,pv7,pv5333], .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv11,pv181], .c 3, .c 5, .c 17,
  .c 3, .c 11, .c 7, .c 3, .c 41, .c 37, .c 3, .c 509, .c 5, .c 3, .c 269,
  .p pv11 [pv2,pv3,pv5,pv39821], .c 3, .c 5, .c 241, .c 3, .c 7, .c 23, .c 3, .c 31, .c 1093,
  .c 3, .c 521, .c 5, .c 3, .p pv2 [pv2,pv17,pv41,pv857], .c 13, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv23,pv787], .c 3, .p pv7 [pv2,pv5,pv193,pv619], .c 53, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv31,pv2141], .c 3, .c 7, .c 5, .c 3, .c 23, .c 59, .c 3, .c 5, .c 7, .c 3,
  .c 19, .c 797, .c 3, .p pv2 [pv2,pv597353], .c 17, .c 3, .c 13, .c 5, .c 3, .c 373, .c 11, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv13,pv17,pv53], .c 3, .p pv2 [pv2,pv5,pv37,pv3229],
  .p pv19 [pv2,pv3,pv7,pv11,pv431], .c 3, .c 613, .c 7, .c 3, .c 11, .c 5, .c 3, .c 97,
  .p pv23 [pv2,pv3,pv5,pv59], .c 3,
]
private theorem h0145c26 : checkBlock 1194499 128 b0145c26 = true := by
  decide +kernel

private def b0145c27 : List Row := [
  .c 5, .p pv5 [pv2,pv3,pv99563], .c 3, .c 239, .p pv3 [pv2,pv3,pv107,pv1861], .c 3, .c 7,
  .p pv29 [pv2,pv3,pv8297], .c 3, .c 317, .c 5, .c 3, .c 53, .c 7, .c 3, .c 5, .c 11, .c 3, .c 13,
  .c 257, .c 3, .p pv2 [pv2,pv19,pv79,pv199], .p pv7 [pv2,pv3,pv11,pv43,pv421], .c 3,
  .p pv2 [pv2,pv7,pv31,pv2753], .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 13, .c 3,
  .p pv3 [pv2,pv5,pv11,pv5431], .c 7, .c 3, .c 23, .c 29, .c 3, .c 31, .c 5, .c 3, .c 271, .c 37,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv97,pv2053], .c 3, .c 7, .c 11, .c 3, .p pv3 [pv2,pv13,pv11489],
  .c 71, .c 3, .c 41, .c 5, .c 3, .c 13, .c 977, .c 3, .c 5, .p pv2 [pv2,pv3,pv33191], .c 3,
  .c 47, .p pv2 [pv2,pv3,pv13,pv15319], .c 3, .c 29, .p pv29 [pv2,pv3,pv49787], .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv269,pv2221], .p pv29 [pv2,pv3,pv5,pv7,pv569], .c 3, .c 5, .c 7, .c 3,
  .c 173, .c 17, .c 3, .p pv2 [pv2,pv29,pv10301], .c 11, .c 3, .p pv2 [pv2,pv229,pv2609], .c 5,
  .c 3, .c 19, .c 101, .c 3, .c 5, .c 73, .c 3, .c 11, .c 97, .c 3, .c 13, .c 7, .c 3, .c 163,
  .c 5, .c 3, .p pv17 [pv2,pv439,pv1361], .p pv23 [pv2,pv3,pv5,pv13,pv383], .c 3, .c 5, .c 19,
  .c 3, .p pv2 [pv2,pv5,pv7,pv43,pv397], .c 13, .c 3, .c 7, .p pv2 [pv2,pv3,pv277,pv719], .c 3,
  .c 139, .c 5, .c 3, .c 37, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv823], .c 3, .c 71, .c 29,
  .c 3, .c 11, .c 647,
]
private theorem h0145c27 : checkBlock 1194755 128 b0145c27 = true := by
  decide +kernel

private def b0145c28 : List Row := [
  .c 3, .c 43, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv2213], .c 3, .c 5, .c 41, .c 3,
  .p pv13 [pv2,pv5,pv119503], .c 7, .c 3, .p pv2 [pv2,pv298759], .p pv3 [pv2,pv3,pv13,pv5107],
  .c 3, .c 19, .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .c 23, .c 3, .c 7, .c 37, .c 3,
  .p pv2 [pv2,pv17,pv35149], .c 47, .c 3, .c 11, .c 5, .c 3, .c 67, .c 19, .c 3, .c 5, .c 191,
  .c 3, .p pv2 [pv2,pv5,pv13,pv29,pv317], .c 281, .c 3, .c 53, .c 43, .c 3, .c 7, .c 5, .c 3,
  .c 41, .c 359, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv14939], .p pv2 [pv2,pv3,pv139,pv1433],
  .c 3, .p pv5 [pv2,pv23,pv25981], .c 13, .c 3, .c 101, .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv19919], .c 3, .c 5, .c 293, .c 3, .c 17, .p pv5 [pv2,pv3,pv7,pv3557],
  .c 3, .c 19, .c 7, .c 3, .c 47, .c 5, .c 3, .p pv3 [pv2,pv13,pv17],
  .p pv2 [pv2,pv3,pv5,pv39839], .c 3, .c 5, .c 29, .c 3, .c 13, .c 11, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv137,pv727], .c 3, .p pv3 [pv2,pv149399], .c 5, .c 3, .c 197, .c 7, .c 3,
  .c 5, .c 13, .c 3, .c 37, .c 67, .c 3, .p pv3 [pv2,pv11,pv6791], .c 17, .c 3,
  .p pv5 [pv2,pv7,pv59,pv1447], .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv39841], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv17,pv31], .c 3, .c 23, .c 7, .c 3, .p pv5 [pv2,pv13,pv45971], .c 11, .c 3,
  .c 17, .c 5, .c 3, .c 13, .c 139, .c 3, .c 5,
]
private theorem h0145c28 : checkBlock 1195011 128 b0145c28 = true := by
  decide +kernel

private def b0145c29 : List Row := [
  .c 31, .c 3, .c 7, .c 41, .c 3, .p pv2 [pv2,pv298819], .c 163, .c 3, .c 83, .c 5, .c 3, .c 619,
  .p pv2 [pv2,pv3,pv5,pv19,pv233], .c 3, .c 5, .c 107, .c 3, .c 971, .c 757, .c 3, .c 257, .c 19,
  .c 3, .c 7, .c 5, .c 3, .c 367, .c 17, .c 3, .c 5, .c 7, .c 3, .c 97, .c 23, .c 3, .c 11,
  .c 337, .c 3, .c 383, .c 5, .c 3, .c 79, .c 29, .c 3, .c 5, .c 43, .c 3,
  .p pv7 [pv2,pv5,pv31,pv241], .c 13, .c 3, .c 397, .c 7, .c 3, .c 461, .c 5, .c 3, .c 23, .c 11,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv167,pv1193], .c 3, .c 31, .c 199, .c 3, .c 7, .c 59, .c 3, .c 11,
  .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .c 61, .c 3, .p pv2 [pv2,pv5,pv59771], .c 17, .c 3, .c 71,
  .p pv17 [pv2,pv3,pv13,pv79,pv97], .c 3, .c 37, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 11, .c 3,
  .c 127, .c 7, .c 3, .c 17, .p pv2 [pv2,pv3,pv11,pv59,pv307], .c 3, .p pv5 [pv2,pv137,pv4363],
  .c 5, .c 3, .c 11, .c 23, .c 3, .c 5, .p pv11 [pv2,pv3,pv99623], .c 3, .c 7,
  .p pv3 [pv2,pv3,pv199247], .c 3, .c 743, .p pv37 [pv2,pv3,pv7,pv593], .c 3, .c 13, .c 5, .c 3,
  .c 19, .p pv7 [pv2,pv3,pv5,pv797], .c 3, .c 5, .c 37, .c 3, .c 107, .c 11, .c 3, .c 23, .c 13,
  .c 3,
]
private theorem h0145c29 : checkBlock 1195267 128 b0145c29 = true := by
  decide +kernel

private def b0145c30 : List Row := [
  .c 7, .c 5, .c 3, .c 43, .c 761, .c 3, .c 5, .c 7, .c 3, .c 179, .p pv3 [pv2,pv3,pv17,pv3907],
  .c 3, .p pv2 [pv2,pv11,pv31,pv1753], .p pv2 [pv2,pv3,pv67,pv1487], .c 3, .c 167, .c 5, .c 3,
  .c 17, .p pv23 [pv2,pv3,pv5,pv41], .c 3, .c 5, .p pv3 [pv2,pv3,pv199261], .c 3, .c 13,
  .p pv5 [pv2,pv3,pv7,pv43,pv331], .c 3, .c 31, .c 7, .c 3, .c 29, .c 5, .c 3,
  .p pv2 [pv2,pv298897], .c 1021, .c 3, .c 5, .c 13, .c 3, .c 11, .c 173, .c 3, .c 7, .c 23, .c 3,
  .c 19, .c 5, .c 3, .c 919, .c 7, .c 3, .c 5, .c 17, .c 3, .c 503, .c 47, .c 3, .c 131, .c 31,
  .c 3, .c 653, .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 443, .c 3, .c 17, .c 7, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv11071], .c 3, .p pv3 [pv2,pv149459], .c 5, .c 3,
  .p pv7 [pv2,pv11,pv17,pv23,pv139], .p pv17 [pv2,pv3,pv5,pv47,pv53], .c 3, .c 5, .c 449, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv37,pv2693], .c 3, .c 719, .c 29, .c 3, .p pv5 [pv2,pv739,pv809], .c 5,
  .c 3, .p pv2 [pv2,pv19,pv15733], .c 11, .c 3, .c 5, .c 239, .c 3, .p pv3 [pv2,pv5,pv167,pv179],
  .p pv2 [pv2,pv3,pv11,pv61], .c 3, .c 13, .c 17, .c 3, .c 7, .c 5, .c 3, .c 101,
  .p pv11 [pv2,pv3,pv5,pv7,pv13,pv73], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv4783], .c 13,
  .c 3, .c 29, .p pv3 [pv2,pv3,pv66431], .c 3, .c 17, .c 5, .c 3, .c 151,
  .p pv3 [pv2,pv3,pv5,pv23,pv1733], .c 3, .c 5, .c 11,
]
private theorem h0145c30 : checkBlock 1195523 128 b0145c30 = true := by
  decide +kernel

private def b0145c31 : List Row := [
  .c 3, .c 83, .c 61, .c 3, .c 43, .c 7, .c 3, .c 23, .c 5, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv5,pv1993], .c 3, .c 5, .p pv3 [pv2,pv3,pv41,pv4861], .c 3,
  .p pv2 [pv2,pv5,pv7,pv11,pv1553], .c 73, .c 3, .c 7, .c 823, .c 3, .c 79, .c 5, .c 3, .c 359,
  .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv227,pv439], .c 3, .c 19, .c 11, .c 3, .c 41,
  .p pv19 [pv2,pv3,pv17,pv977], .c 3, .c 71, .c 5, .c 3, .c 7, .c 263, .c 3, .c 5, .c 181, .c 3,
  .c 59, .c 7, .c 3, .c 37, .c 19, .c 3, .c 13, .c 5, .c 3, .c 1039, .p pv2 [pv2,pv3,pv5,pv39863],
  .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv3833], .c 3, .c 7, .c 331, .c 3, .p pv2 [pv2,pv701,pv853],
  .c 11, .c 3, .c 97, .c 5, .c 3, .p pv7 [pv2,pv31,pv19289], .c 673, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv199321], .c 3, .c 11, .c 17, .c 3, .p pv3 [pv2,pv7,pv19,pv281], .c 107, .c 3,
  .c 7, .c 5, .c 3, .c 31, .c 37, .c 3, .c 5, .c 7, .c 3, .c 13, .c 613, .c 3, .c 17, .c 457,
  .c 3, .c 313, .c 5, .c 3, .p pv2 [pv2,pv7,pv85427], .c 79, .c 3, .c 5, .c 13, .c 3,
  .p pv11 [pv2,pv5,pv199,pv601], .c 19, .c 3, .c 11, .c 7, .c 3, .p pv2 [pv2,pv43,pv13907], .c 5,
  .c 3, .c 47, .c 31, .c 3, .c 5, .c 67, .c 3, .c 193, .c 23, .c 3, .c 7,
  .p pv17 [pv2,pv3,pv33223], .c 3, .p pv3 [pv2,pv73],
]
private theorem h0145c31 : checkBlock 1195779 128 b0145c31 = true := by
  decide +kernel

def rows0145 : List Row :=
  b0145c00 ++ b0145c01 ++ b0145c02 ++ b0145c03 ++ b0145c04 ++ b0145c05 ++ b0145c06 ++ b0145c07 ++
  b0145c08 ++ b0145c09 ++ b0145c10 ++ b0145c11 ++ b0145c12 ++ b0145c13 ++ b0145c14 ++ b0145c15 ++
  b0145c16 ++ b0145c17 ++ b0145c18 ++ b0145c19 ++ b0145c20 ++ b0145c21 ++ b0145c22 ++ b0145c23 ++
  b0145c24 ++ b0145c25 ++ b0145c26 ++ b0145c27 ++ b0145c28 ++ b0145c29 ++ b0145c30 ++ b0145c31

attribute [local irreducible] checkBlock checkRows checkPrime

theorem checked0145 : checkBlock 1187843 4096 rows0145 = true :=
  checkBlock_append h0145c00 (
    checkBlock_append h0145c01 (
    checkBlock_append h0145c02 (
    checkBlock_append h0145c03 (
    checkBlock_append h0145c04 (
    checkBlock_append h0145c05 (
    checkBlock_append h0145c06 (
    checkBlock_append h0145c07 (
    checkBlock_append h0145c08 (
    checkBlock_append h0145c09 (
    checkBlock_append h0145c10 (
    checkBlock_append h0145c11 (
    checkBlock_append h0145c12 (
    checkBlock_append h0145c13 (
    checkBlock_append h0145c14 (
    checkBlock_append h0145c15 (
    checkBlock_append h0145c16 (
    checkBlock_append h0145c17 (
    checkBlock_append h0145c18 (
    checkBlock_append h0145c19 (
    checkBlock_append h0145c20 (
    checkBlock_append h0145c21 (
    checkBlock_append h0145c22 (
    checkBlock_append h0145c23 (
    checkBlock_append h0145c24 (
    checkBlock_append h0145c25 (
    checkBlock_append h0145c26 (
    checkBlock_append h0145c27 (
    checkBlock_append h0145c28 (
    checkBlock_append h0145c29 (
    checkBlock_append h0145c30 (
    h0145c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
