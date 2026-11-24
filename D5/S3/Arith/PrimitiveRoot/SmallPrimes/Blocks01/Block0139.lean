/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0139
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0139.checked0139
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table018
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table021
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table025
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table031
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table042
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table063
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table117

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0139c00 : List Row := [
  .c 151, .c 41, .c 3, .c 7, .c 599, .c 3, .p pv5 [pv2,pv431,pv1321], .c 5, .c 3, .c 11, .c 7,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv47,pv673], .c 3, .c 157, .c 31, .c 3, .c 19,
  .p pv13 [pv2,pv3,pv17,pv2791], .c 3, .p pv3 [pv2,pv7,pv67,pv607], .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv18979], .c 3, .c 5, .c 277, .c 3, .p pv11 [pv2,pv5,pv911], .c 7, .c 3,
  .p pv2 [pv2,pv284689], .c 59, .c 3, .c 47, .c 5, .c 3, .c 43, .p pv23 [pv2,pv3,pv5,pv12653],
  .c 3, .c 5, .p pv5 [pv2,pv3,pv23,pv2063], .c 3, .c 7, .c 131, .c 3, .c 13, .c 787, .c 3,
  .p pv3 [pv2,pv283,pv503], .c 5, .c 3, .c 23, .c 29, .c 3, .c 5, .c 149, .c 3, .c 53, .c 13,
  .c 3, .c 229, .c 11, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv284707],
  .p pv13 [pv2,pv3,pv5,pv7,pv11,pv17,pv29], .c 3, .c 5, .c 7, .c 3, .c 11, .c 83, .c 3, .c 17,
  .p pv7 [pv2,pv3,pv11863], .c 3, .p pv2 [pv2,pv11,pv13,pv181], .c 5, .c 3, .c 29, .c 223, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv67,pv2833], .c 3, .c 103, .c 73, .c 3, .c 59, .c 7, .c 3,
  .p pv2 [pv2,pv311,pv1831], .c 5, .c 3, .c 769, .c 13, .c 3, .c 5, .c 37, .c 3,
  .p pv2 [pv2,pv5,pv7,pv1627], .c 661, .c 3, .c 7, .c 31, .c 3, .c 797, .c 5, .c 3,
  .p pv13 [pv2,pv11,pv51769], .c 7, .c 3, .c 5, .c 113, .c 3, .c 61, .c 67, .c 3, .c 23, .c 41,
  .c 3, .c 13, .c 5,
]
private theorem h0139c00 : checkBlock 1138691 128 b0139c00 = true := by
  decide +kernel

private def b0139c01 : List Row := [
  .c 3, .c 7, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv13,pv149], .c 3,
  .p pv3 [pv2,pv5,pv23,pv619], .c 7, .c 3, .p pv5 [pv2,pv17,pv139,pv241], .c 13, .c 3, .c 11,
  .c 5, .c 3, .p pv2 [pv2,pv211,pv2699], .c 317, .c 3, .c 5, .p pv5 [pv2,pv3,pv63277], .c 3, .c 7,
  .c 19, .c 3, .p pv2 [pv2,pv284749], .p pv3 [pv2,pv3,pv7,pv47,pv577], .c 3,
  .p pv2 [pv2,pv31,pv18371], .c 5, .c 3, .c 83, .p pv2 [pv2,pv3,pv5,pv37967], .c 3, .c 5, .c 11,
  .c 3, .c 13, .c 53, .c 3, .c 43, .c 23, .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv5,pv7,pv113], .c 3, .c 5, .c 7, .c 3, .c 17, .c 61, .c 3, .c 641,
  .p pv2 [pv2,pv3,pv63281], .c 3, .c 127, .c 5, .c 3, .c 19, .c 97, .c 3, .c 5, .c 103, .c 3,
  .p pv3 [pv2,pv5,pv28477], .c 11, .c 3, .p pv5 [pv2,pv13,pv193,pv227], .c 7, .c 3, .c 487, .c 5,
  .c 3, .c 13, .c 79, .c 3, .c 5, .c 19, .c 3, .c 89, .c 43, .c 3, .c 7, .c 17, .c 3,
  .p pv2 [pv2,pv107,pv5323], .c 5, .c 3, .c 53, .c 7, .c 3, .c 5, .c 233, .c 3,
  .p pv2 [pv2,pv5,pv56957], .p pv3 [pv2,pv3,pv373,pv509], .c 3, .p pv2 [pv2,pv569573], .c 11,
  .c 3, .c 17, .c 5, .c 3, .c 7, .c 1009, .c 3, .c 5, .c 23, .c 3, .c 11, .c 7, .c 3, .c 13,
  .c 101, .c 3, .c 19, .c 5, .c 3, .c 211, .p pv23 [pv2,pv3,pv5,pv13,pv23,pv127], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv94933], .c 3, .c 7,
]
private theorem h0139c01 : checkBlock 1138947 128 b0139c01 = true := by
  decide +kernel

private def b0139c02 : List Row := [
  .c 13, .c 3, .c 29, .c 727, .c 3, .c 23, .c 5, .c 3, .c 31, .c 17, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv11,pv41,pv421], .c 3, .c 59, .c 47, .c 3, .c 11, .p pv29 [pv2,pv3,pv17,pv73],
  .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv11,pv6473], .c 197, .c 3, .c 5, .c 7, .c 3, .c 419,
  .p pv3 [pv2,pv3,pv189877], .c 3, .c 37, .p pv2 [pv2,pv3,pv13,pv67,pv109], .c 3,
  .p pv3 [pv2,pv17,pv8377], .c 5, .c 3, .c 193, .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv189881],
  .c 3, .p pv2 [pv2,pv5,pv59,pv1931], .p pv5 [pv2,pv3,pv7,pv11,pv137], .c 3, .c 19, .c 7, .c 3,
  .c 11, .c 5, .c 3, .p pv2 [pv2,pv41,pv6947], .c 73, .c 3, .c 5, .c 127, .c 3,
  .p pv11 [pv2,pv5,pv7,pv13,pv313], .c 17, .c 3, .c 7, .p pv17 [pv2,pv3,pv23,pv43], .c 3, .c 13,
  .c 5, .c 3, .c 607, .c 7, .c 3, .c 5, .c 11, .c 3, .c 23, .p pv5 [pv2,pv3,pv29,pv1637], .c 3,
  .c 17, .c 13, .c 3, .c 709, .c 5, .c 3, .c 7, .c 43, .c 3, .c 5, .c 109, .c 3, .c 29, .c 7,
  .c 3, .p pv2 [pv2,pv103,pv5531], .c 673, .c 3, .p pv3 [pv2,pv19,pv937], .c 5, .c 3, .c 1033,
  .c 547, .c 3, .c 5, .p pv3 [pv2,pv3,pv189901], .c 3, .c 7, .c 11, .c 3, .c 79, .c 61, .c 3,
  .p pv5 [pv2,pv569711], .c 5, .c 3, .c 137, .c 41, .c 3, .c 5, .c 13, .c 3, .c 167, .c 23, .c 3,
  .c 53, .c 19, .c 3, .c 7, .c 5, .c 3,
]
private theorem h0139c02 : checkBlock 1139203 128 b0139c02 = true := by
  decide +kernel

private def b0139c03 : List Row := [
  .c 17, .p pv13 [pv2,pv3,pv5,pv7,pv2713], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv113947],
  .p pv5 [pv2,pv3,pv41,pv193], .c 3, .c 293, .c 11, .c 3, .p pv2 [pv2,pv101,pv5641], .c 5, .c 3,
  .c 13, .p pv2 [pv2,pv3,pv5,pv11,pv1151], .c 3, .c 5, .c 29, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv7,pv13,pv2087], .c 3, .c 83, .c 7, .c 3, .c 41, .c 5, .c 3,
  .p pv41 [pv2,pv569759], .p pv7 [pv2,pv3,pv5,pv1187], .c 3, .c 5, .c 17, .c 3,
  .p pv2 [pv2,pv5,pv7,pv73,pv223], .c 163, .c 3, .c 7, .p pv3 [pv2,pv3,pv257,pv739], .c 3, .c 43,
  .c 5, .c 3, .p pv2 [pv2,pv347,pv821], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv89,pv97], .c 3,
  .c 17, .c 19, .c 3, .c 11, .c 131, .c 3, .p pv2 [pv2,pv7,pv40699], .c 5, .c 3, .c 7, .c 23,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv43,pv631], .c 3, .c 31, .c 7, .c 3, .c 151, .c 617, .c 3,
  .c 67, .c 5, .c 3, .c 47, .c 11, .c 3, .c 5, .c 523, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv11,pv31,pv557], .c 3, .c 23, .c 17, .c 3, .c 11, .c 5, .c 3, .c 19, .c 283,
  .c 3, .c 5, .c 421, .c 3, .c 509, .c 31, .c 3, .c 107, .c 53, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv284917], .c 13, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv17,pv419],
  .p pv3 [pv2,pv3,pv189947], .c 3, .p pv5 [pv2,pv569843], .c 241, .c 3, .c 179, .c 5, .c 3, .c 11,
  .c 149, .c 3, .c 5, .c 569, .c 3, .c 37, .p pv23 [pv2,pv3,pv7,pv53],
]
private theorem h0139c03 : checkBlock 1139459 128 b0139c03 = true := by
  decide +kernel

private def b0139c04 : List Row := [
  .c 3, .p pv2 [pv2,pv499,pv571], .c 7, .c 3, .c 13, .c 5, .c 3, .c 29, .c 17, .c 3, .c 5, .c 67,
  .c 3, .p pv3 [pv2,pv5,pv7,pv1163], .c 11, .c 3, .c 7, .c 13, .c 3, .c 19, .c 5, .c 3, .c 41,
  .c 7, .c 3, .c 5, .c 227, .c 3, .p pv23 [pv2,pv5,pv293,pv389], .p pv2 [pv2,pv3,pv19,pv4999],
  .c 3, .c 31, .p pv3 [pv2,pv3,pv21107], .c 3, .c 1039, .c 5, .c 3, .c 7, .c 19, .c 3, .c 5,
  .c 47, .c 3, .c 13, .c 7, .c 3, .p pv5 [pv2,pv569903], .c 11, .c 3, .c 109, .c 5, .c 3,
  .p pv2 [pv2,pv53,pv10753], .c 59, .c 3, .c 5, .c 13, .c 3, .c 7, .c 17, .c 3, .c 353, .c 31,
  .c 3, .p pv2 [pv2,pv11,pv197,pv263], .c 5, .c 3, .p pv3 [pv2,pv19,pv7499],
  .p pv3 [pv2,pv3,pv5,pv17,pv149], .c 3, .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv56993],
  .p pv3 [pv2,pv3,pv189977], .c 3, .c 17, .p pv31 [pv2,pv3,pv31663], .c 3, .c 7, .c 5, .c 3,
  .c 13, .c 809, .c 3, .c 5, .c 7, .c 3, .c 47, .c 859, .c 3, .c 11, .c 151, .c 3, .c 23, .c 5,
  .c 3, .p pv3 [pv2,pv7,pv11,pv3701], .p pv13 [pv2,pv3,pv5,pv37997], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv94993], .c 3, .p pv3 [pv2,pv5,pv14249], .c 41, .c 3, .c 683, .c 7, .c 3,
  .c 37, .c 5, .c 3, .c 59, .c 11, .c 3, .c 5, .c 467, .c 3, .p pv7 [pv2,pv5,pv7,pv3257], .c 883,
  .c 3, .c 7, .p pv13 [pv2,pv3,pv63331], .c 3, .c 11, .c 5, .c 3, .c 17,
]
private theorem h0139c04 : checkBlock 1139715 128 b0139c04 = true := by
  decide +kernel

private def b0139c05 : List Row := [
  .c 7, .c 3, .c 5, .c 53, .c 3, .c 19, .c 13, .c 3, .c 101, .p pv19 [pv2,pv3,pv94999], .c 3,
  .p pv5 [pv2,pv7,pv20357], .c 5, .c 3, .c 7, .c 89, .c 3, .c 5, .c 11, .c 3, .c 449, .c 7, .c 3,
  .c 281, .c 19, .c 3, .c 863, .c 5, .c 3, .c 11, .c 109, .c 3, .c 5, .c 17, .c 3, .c 7, .c 401,
  .c 3, .c 71, .c 79, .c 3, .c 461, .c 5, .c 3, .c 43, .c 13, .c 3, .c 5, .c 487, .c 3, .c 17,
  .c 11, .c 3, .c 29, .c 47, .c 3, .c 7, .c 5, .c 3, .c 433, .p pv2 [pv2,pv3,pv5,pv7,pv61,pv89],
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv13,pv877], .p pv23 [pv2,pv3,pv43,pv491], .c 3, .c 103,
  .c 167, .c 3, .c 13, .c 5, .c 3, .c 181, .p pv13 [pv2,pv3,pv5,pv3167], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv13,pv47,pv311], .c 3, .p pv2 [pv2,pv5,pv114013], .c 19, .c 3,
  .p pv3 [pv2,pv53,pv2689], .c 7, .c 3, .p pv5 [pv2,pv570071], .c 5, .c 3, .c 31, .c 61, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv17,pv23], .c 3, .c 11, .p pv2 [pv2,pv3,pv190027], .c 3, .c 7, .c 41,
  .c 3, .c 17, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 73, .c 3, .c 13, .c 29, .c 3,
  .p pv2 [pv2,pv285049], .c 223, .c 3, .p pv2 [pv2,pv7,pv23,pv3541], .c 5, .c 3, .c 7, .c 31,
  .c 3, .c 5, .c 13, .c 3, .c 227, .c 7, .c 3,
]
private theorem h0139c05 : checkBlock 1139971 128 b0139c05 = true := by
  decide +kernel

private def b0139c06 : List Row := [
  .c 11, .c 37, .c 3, .p pv3 [pv2,pv142529], .c 5, .c 3, .p pv7 [pv2,pv11,pv51829], .c 17, .c 3,
  .c 5, .c 19, .c 3, .c 7, .p pv2 [pv2,pv3,pv95021], .c 3, .p pv3 [pv2,pv13,pv2741], .c 313, .c 3,
  .c 1049, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 739, .c 3, .p pv3 [pv2,pv5,pv29,pv983],
  .c 113, .c 3, .c 571, .p pv7 [pv2,pv3,pv5939], .c 3, .c 7, .c 5, .c 3, .c 107, .c 503, .c 3,
  .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv114031], .c 103, .c 3, .c 23, .p pv13 [pv2,pv3,pv7039],
  .c 3, .c 19, .c 5, .c 3, .c 937, .c 71, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv23,pv37,pv67], .c 17, .c 3, .c 13, .c 7, .c 3, .p pv3 [pv2,pv59,pv151], .c 5,
  .c 3, .c 11, .c 19, .c 3, .c 5, .c 29, .c 3, .p pv2 [pv2,pv5,pv7,pv11,pv1481], .c 13, .c 3,
  .c 7, .p pv3 [pv2,pv3,pv190063], .c 3, .p pv5 [pv2,pv570191], .c 5, .c 3,
  .p pv2 [pv2,pv137,pv2081], .c 7, .c 3, .c 5, .c 31, .c 3, .c 53, .c 11, .c 3, .c 67, .c 23,
  .c 3, .p pv2 [pv2,pv7,pv13,pv241], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv83,pv229], .c 3,
  .c 5, .c 769, .c 3, .p pv13 [pv2,pv5,pv114043], .c 7, .c 3, .c 19,
  .p pv11 [pv2,pv3,pv13,pv14621], .c 3, .c 167, .c 5, .c 3, .p pv3 [pv2,pv157,pv227], .c 13, .c 3,
  .c 5, .c 1021, .c 3, .c 7, .p pv3 [pv2,pv3,pv17,pv3727], .c 3, .c 109, .c 11, .c 3, .c 71, .c 5,
  .c 3, .c 17, .c 181,
]
private theorem h0139c06 : checkBlock 1140227 128 b0139c06 = true := by
  decide +kernel

private def b0139c07 : List Row := [
  .c 3, .c 5, .p pv5 [pv2,pv3,pv131,pv1451], .c 3, .c 11, .p pv2 [pv2,pv3,pv101,pv941], .c 3,
  .c 41, .c 479, .c 3, .c 7, .c 5, .c 3, .c 113, .c 163, .c 3, .c 5, .c 7, .c 3, .c 31, .c 79,
  .c 3, .c 701, .c 13, .c 3, .p pv2 [pv2,pv19,pv43,pv349], .c 5, .c 3,
  .p pv7 [pv2,pv7,pv41,pv1987], .c 29, .c 3, .c 5, .c 17, .c 3, .c 19, .c 607, .c 3, .c 11, .c 7,
  .c 3, .p pv2 [pv2,pv37,pv15413], .c 5, .c 3, .p pv3 [pv2,pv11,pv13,pv997],
  .p pv2 [pv2,pv3,pv5,pv19,pv23,pv29], .c 3, .c 5, .p pv5 [pv2,pv3,pv109], .c 3, .c 13, .c 31,
  .c 3, .c 7, .c 19, .c 3, .c 23, .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .c 13, .c 3,
  .p pv29 [pv2,pv5,pv167,pv683], .c 53, .c 3, .c 131, .p pv2 [pv2,pv3,pv43,pv4421], .c 3, .c 11,
  .c 5, .c 3, .c 7, .c 263, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv37,pv367], .c 3, .c 991, .c 7, .c 3,
  .c 59, .c 17, .c 3, .c 241, .c 5, .c 3, .c 13, .c 41, .c 3, .c 5, .c 11, .c 3, .c 7, .c 37,
  .c 3, .p pv2 [pv2,pv31,pv9199], .p pv7 [pv2,pv3,pv7,pv11,pv823], .c 3, .c 17, .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv47,pv809], .c 3, .c 5, .p pv11 [pv2,pv3,pv5281], .c 3, .c 409, .c 19,
  .c 3, .c 31, .p pv2 [pv2,pv3,pv23,pv4133], .c 3, .c 7, .c 5, .c 3, .c 53,
  .p pv47 [pv2,pv3,pv5,pv7,pv97], .c 3, .c 5, .c 7, .c 3, .c 23, .c 11, .c 3, .c 13,
]
private theorem h0139c07 : checkBlock 1140483 128 b0139c07 = true := by
  decide +kernel

private def b0139c08 : List Row := [
  .c 761, .c 3, .c 41, .c 5, .c 3, .p pv2 [pv2,pv7,pv131,pv311], .c 17, .c 3, .c 5, .c 71, .c 3,
  .c 61, .c 13, .c 3, .c 179, .c 7, .c 3, .c 29, .c 5, .c 3, .c 19, .c 709, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv63377], .c 3, .c 653, .c 613, .c 3, .c 7, .c 11, .c 3,
  .p pv5 [pv2,pv13,pv17,pv29,pv89], .c 5, .c 3, .c 67, .c 7, .c 3, .c 5, .c 19, .c 3, .c 11,
  .c 23, .c 3, .c 197, .c 269, .c 3, .c 43, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv7,pv23,pv1181], .c 3, .p pv2 [pv2,pv5,pv22817], .c 7, .c 3, .c 431,
  .p pv2 [pv2,pv3,pv37,pv571], .c 3, .p pv5 [pv2,pv31,pv18401], .c 5, .c 3, .c 23,
  .p pv19 [pv2,pv3,pv5,pv17,pv2237], .c 3, .c 5, .c 211, .c 3, .c 7, .c 59, .c 3, .c 11, .c 29,
  .c 3, .c 13, .c 5, .c 3, .c 71, .p pv2 [pv2,pv3,pv5,pv3803], .c 3, .c 5, .c 41, .c 3,
  .p pv17 [pv2,pv5,pv271,pv421], .p pv13 [pv2,pv3,pv19,pv139], .c 3, .c 73, .c 13, .c 3, .c 7,
  .c 5, .c 3, .p pv3 [pv2,pv17827], .c 11, .c 3, .c 5, .c 7, .c 3, .c 107, .c 67, .c 3, .c 29,
  .p pv2 [pv2,pv3,pv41,pv773], .c 3, .c 11, .c 5, .c 3, .p pv7 [pv2,pv7,pv13,pv6269], .c 23, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv7043], .c 3, .c 13, .p pv59 [pv2,pv3,pv7,pv17,pv47], .c 3, .c 877, .c 7,
  .c 3, .p pv5 [pv2,pv570491], .c 5, .c 3, .c 17, .p pv3 [pv2,pv3,pv5,pv73,pv521], .c 3,
]
private theorem h0139c08 : checkBlock 1140739 128 b0139c08 = true := by
  decide +kernel

private def b0139c09 : List Row := [
  .c 5, .c 11, .c 3, .c 59, .c 367, .c 3, .c 7, .p pv17 [pv2,pv3,pv11,pv2161], .c 3,
  .p pv2 [pv2,pv109,pv2617], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv19,pv10009],
  .c 3, .p pv11 [pv2,pv5,pv11,pv23,pv41], .p pv5 [pv2,pv3,pv47543], .c 3, .c 53,
  .p pv7 [pv2,pv3,pv63391], .c 3, .c 37, .c 5, .c 3, .c 7, .c 139, .c 3, .c 5, .c 17, .c 3,
  .p pv3 [pv2,pv5,pv59,pv967], .c 7, .c 3, .p pv2 [pv2,pv47,pv61,pv199], .c 89, .c 3, .c 137,
  .c 5, .c 3, .c 31, .p pv11 [pv2,pv3,pv5,pv37,pv257], .c 3, .c 5, .p pv5 [pv2,pv3,pv190181],
  .c 3, .c 7, .p pv2 [pv2,pv3,pv29,pv1093], .c 3, .p pv3 [pv2,pv11,pv12967], .c 23, .c 3,
  .p pv5 [pv2,pv19,pv30029], .c 5, .c 3, .p pv2 [pv2,pv17,pv97,pv173], .c 167, .c 3, .c 5, .c 37,
  .c 3, .c 19, .p pv3 [pv2,pv3,pv23,pv8269], .c 3, .c 13, .c 11, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv570569], .c 31, .c 3, .c 5, .c 7, .c 3, .c 11, .c 13, .c 3, .c 263, .c 17, .c 3,
  .c 163, .c 5, .c 3, .c 379, .p pv2 [pv2,pv3,pv5,pv38039], .c 3, .c 5, .c 43, .c 3, .c 271,
  .c 71, .c 3, .c 113, .c 7, .c 3, .c 17, .c 5, .c 3, .c 101, .c 563, .c 3, .c 5, .c 47, .c 3,
  .c 67, .c 499, .c 3, .c 7, .p pv7 [pv2,pv3,pv13,pv4877], .c 3, .p pv5 [pv2,pv127,pv4493], .c 5,
  .c 3, .p pv2 [pv2,pv11,pv37,pv701], .c 7, .c 3, .c 5, .c 23, .c 3, .p pv3 [pv2,pv5,pv103,pv277],
  .p pv3 [pv2,pv3,pv190207], .c 3, .c 89, .c 53,
]
private theorem h0139c09 : checkBlock 1140995 128 b0139c09 = true := by
  decide +kernel

private def b0139c10 : List Row := [
  .c 3, .p pv2 [pv2,pv7,pv40759], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv29,pv937], .c 3, .p pv19 [pv2,pv5,pv13,pv8779], .c 7, .c 3,
  .p pv2 [pv2,pv41,pv6959], .p pv19 [pv2,pv3,pv17,pv67,pv167], .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv331,pv431], .p pv2 [pv2,pv3,pv5,pv1409], .c 3, .c 5, .c 251, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv37,pv53,pv97], .c 3, .c 503, .c 13, .c 3, .c 79, .c 5, .c 3,
  .p pv7 [pv2,pv570659], .p pv23 [pv2,pv3,pv5,pv9511], .c 3, .c 5, .c 11, .c 3, .c 421, .c 83,
  .c 3, .c 257, .c 37, .c 3, .c 7, .c 5, .c 3, .c 11, .p pv17 [pv2,pv3,pv5,pv7,pv1087], .c 3,
  .c 5, .c 7, .c 3, .c 13, .c 17, .c 3, .c 269, .c 107, .c 3, .p pv2 [pv2,pv285343], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv81527], .p pv7 [pv2,pv3,pv5,pv17,pv373], .c 3, .c 5, .c 13, .c 3,
  .p pv17 [pv2,pv5,pv157,pv727], .c 11, .c 3, .c 17, .c 7, .c 3, .c 131, .c 5, .c 3, .c 151,
  .c 29, .c 3, .c 5, .p pv11 [pv2,pv3,pv83,pv191], .c 3, .c 23, .p pv3 [pv2,pv3,pv281,pv677],
  .c 3, .c 7, .c 571, .c 3, .c 941, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv103,pv1847], .c 3, .c 31, .p pv47 [pv2,pv3,pv13,pv271], .c 3, .c 479, .c 11,
  .c 3, .c 19, .c 5, .c 3, .c 7, .c 79, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv107,pv127], .c 3, .c 11,
  .c 7, .c 3, .c 37, .c 47, .c 3, .c 61, .c 5, .c 3, .c 17, .c 19, .c 3, .c 5,
]
private theorem h0139c10 : checkBlock 1141251 128 b0139c10 = true := by
  decide +kernel

private def b0139c11 : List Row := [
  .p pv2 [pv2,pv3,pv21139], .c 3, .c 7, .c 23, .c 3, .c 13, .c 409, .c 3,
  .p pv2 [pv2,pv41,pv13921], .c 5, .c 3, .p pv3 [pv2,pv293,pv487],
  .p pv19 [pv2,pv3,pv5,pv13,pv2927], .c 3, .c 5, .c 223, .c 3, .p pv3 [pv2,pv5,pv57077], .c 13,
  .c 3, .c 11, .c 103, .c 3, .c 7, .c 5, .c 3, .c 23, .c 37, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv114157], .p pv19 [pv2,pv3,pv95131], .c 3, .c 19, .c 349, .c 3, .c 47, .c 5,
  .c 3, .c 547, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv19,pv1669], .c 3, .c 17, .c 89, .c 3, .c 43,
  .c 7, .c 3, .c 11, .c 5, .c 3, .c 331, .c 13, .c 3, .c 5, .c 173, .c 3,
  .p pv7 [pv2,pv5,pv7,pv47,pv347], .p pv7 [pv2,pv3,pv991], .c 3, .c 7, .c 113, .c 3, .c 29, .c 5,
  .c 3, .p pv3 [pv2,pv71353], .c 7, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv13,pv4391], .c 199,
  .c 3, .p pv2 [pv2,pv109,pv5237], .c 17, .c 3, .c 13, .c 5, .c 3, .c 7, .c 311, .c 3, .c 5,
  .c 509, .c 3, .c 19, .c 7, .c 3, .c 23, .c 13, .c 3, .c 17, .c 5, .c 3, .c 37, .c 151, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv95143], .c 3, .c 7, .c 11, .c 3, .c 41, .c 19, .c 3, .c 307, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv43913], .c 929, .c 3, .c 5, .c 67, .c 3, .c 13, .c 373, .c 3,
  .p pv2 [pv2,pv7,pv11,pv337], .c 29, .c 3,
]
private theorem h0139c11 : checkBlock 1141507 128 b0139c11 = true := by
  decide +kernel

private def b0139c12 : List Row := [
  .c 7, .c 5, .c 3, .p pv3 [pv2,pv41,pv59], .c 17, .c 3, .c 5, .c 7, .c 3, .c 89, .c 37, .c 3,
  .c 79, .c 11, .c 3, .c 73, .c 5, .c 3, .c 251, .p pv7 [pv2,pv3,pv5,pv11,pv173], .c 3, .c 5,
  .c 449, .c 3, .c 11, .p pv2 [pv2,pv3,pv7,pv23,pv197], .c 3, .c 29, .c 7, .c 3, .c 31, .c 5,
  .c 3, .c 13, .c 83, .c 3, .c 5, .p pv2 [pv2,pv3,pv95153], .c 3, .c 179, .c 19, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv15859], .c 3, .p pv2 [pv2,pv285463], .c 5, .c 3, .c 61, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv73,pv79], .c 3, .p pv11 [pv2,pv5,pv89,pv1283], .c 17, .c 3, .c 11,
  .c 839, .c 3, .c 577, .c 5, .c 3, .c 7, .c 41, .c 3, .c 5, .c 461, .c 3,
  .p pv2 [pv2,pv5,pv19,pv601], .c 7, .c 3, .c 13, .p pv2 [pv2,pv3,pv43,pv2213], .c 3, .c 907,
  .c 5, .c 3, .c 19, .c 11, .c 3, .c 5, .c 23, .c 3, .c 7, .c 13, .c 3, .c 787, .c 73, .c 3,
  .c 11, .c 5, .c 3, .p pv2 [pv2,pv67,pv4261], .c 43, .c 3, .c 5, .c 19, .c 3, .c 103,
  .p pv2 [pv2,pv3,pv29,pv6563], .c 3, .p pv5 [pv2,pv7,pv81569], .p pv19 [pv2,pv3,pv37,pv643],
  .c 3, .c 7, .c 5, .c 3, .c 359, .c 61, .c 3, .c 5, .c 7, .c 3, .c 29, .c 109, .c 3, .c 83,
  .p pv29 [pv2,pv3,pv11,pv13], .c 3, .p pv2 [pv2,pv571001], .c 5, .c 3, .c 11, .c 13, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv1487],
]
private theorem h0139c12 : checkBlock 1141763 128 b0139c12 = true := by
  decide +kernel

private def b0139c13 : List Row := [
  .c 3, .p pv7 [pv2,pv5,pv11,pv29,pv179], .c 229, .c 3, .c 967, .c 7, .c 3, .c 19, .c 5, .c 3,
  .p pv13 [pv2,pv571019], .p pv19 [pv2,pv3,pv5,pv31,pv307], .c 3, .c 5, .c 659, .c 3, .c 541,
  .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv131,pv1453], .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv285517], .c 7, .c 3, .c 5, .c 17, .c 3, .c 673, .p pv2 [pv2,pv3,pv67,pv947], .c 3,
  .c 827, .c 13, .c 3, .c 337, .c 5, .c 3, .c 7, .c 797, .c 3, .c 5, .c 29, .c 3, .c 17, .c 7,
  .c 3, .c 727, .c 11, .c 3, .c 43, .c 5, .c 3, .p pv3 [pv2,pv13,pv17,pv19],
  .p pv2 [pv2,pv3,pv5,pv11,pv3461], .c 3, .c 5, .c 41, .c 3, .c 7, .c 211, .c 3, .c 19, .c 67,
  .c 3, .c 37, .c 5, .c 3, .p pv7 [pv2,pv73,pv7823], .p pv41 [pv2,pv3,pv5,pv4759], .c 3, .c 5,
  .c 13, .c 3, .p pv2 [pv2,pv5,pv114217], .c 421, .c 3, .c 71, .c 17, .c 3, .c 7, .c 5, .c 3,
  .c 131, .p pv13 [pv2,pv3,pv5,pv7,pv37], .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv5711], .c 23,
  .c 3, .c 11, .c 43, .c 3, .c 17, .c 5, .c 3, .c 13, .c 463, .c 3, .c 5, .c 37, .c 3, .c 73,
  .p pv5 [pv2,pv3,pv7,pv13,pv523], .c 3, .p pv2 [pv2,pv285559], .c 7, .c 3,
  .p pv5 [pv2,pv19,pv30059], .c 5, .c 3, .c 23, .c 11, .c 3, .c 5, .c 31, .c 3, .c 19,
  .p pv11 [pv2,pv3,pv11,pv641], .c 3, .c 7, .p pv2 [pv2,pv3,pv95189], .c 3, .c 11,
]
private theorem h0139c13 : checkBlock 1142019 128 b0139c13 = true := by
  decide +kernel

private def b0139c14 : List Row := [
  .c 5, .c 3, .p pv13 [pv2,pv439,pv1301], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv61,pv3121], .c 3,
  .c 181, .c 599, .c 3, .c 13, .c 19, .c 3, .c 311, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv13,pv29,pv101], .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv109,pv131],
  .c 7, .c 3, .c 563, .c 83, .c 3, .p pv2 [pv2,pv17,pv107,pv157], .c 5, .c 3, .c 11, .c 23, .c 3,
  .c 5, .c 61, .c 3, .c 7, .p pv5 [pv2,pv3,pv7933], .c 3, .p pv2 [pv2,pv19,pv15031],
  .p pv3 [pv2,pv3,pv7,pv59,pv461], .c 3, .p pv2 [pv2,pv13,pv53,pv829], .c 5, .c 3, .c 97, .c 191,
  .c 3, .c 5, .c 73, .c 3, .c 31, .c 11, .c 3, .c 23, .p pv7 [pv2,pv3,pv13,pv2441], .c 3, .c 7,
  .c 5, .c 3, .c 233, .c 13, .c 3, .c 5, .c 7, .c 3, .c 101, .c 19, .c 3, .c 17, .c 79, .c 3,
  .p pv5 [pv2,pv571211], .c 5, .c 3, .c 47, .p pv11 [pv2,pv3,pv5,pv113,pv337], .c 3, .c 5,
  .c 1051, .c 3, .c 139, .c 31, .c 3, .c 167, .c 7, .c 3, .c 13, .c 5, .c 3, .c 199, .c 71, .c 3,
  .c 5, .c 43, .c 3, .c 11, .p pv7 [pv2,pv3,pv181,pv263], .c 3, .c 7, .c 13, .c 3,
  .p pv2 [pv2,pv11,pv4721], .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 443, .c 3, .c 601,
  .p pv3 [pv2,pv3,pv17,pv23,pv487], .c 3, .p pv2 [pv2,pv41,pv13933], .p pv2 [pv2,pv3,pv19,pv5011],
  .c 3, .c 29, .c 5, .c 3, .c 7, .c 53, .c 3, .c 5, .c 19, .c 3,
]
private theorem h0139c14 : checkBlock 1142275 128 b0139c14 = true := by
  decide +kernel

private def b0139c15 : List Row := [
  .c 13, .c 7, .c 3, .c 11, .p pv2 [pv2,pv3,pv109,pv1747], .c 3, .c 113, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv23,pv1129], .c 67, .c 3, .c 5, .c 13, .c 3, .c 7, .c 97, .c 3, .c 31,
  .p pv11 [pv2,pv3,pv7,pv2267], .c 3, .p pv2 [pv2,pv285643], .c 5, .c 3, .c 103, .c 11, .c 3,
  .c 5, .c 17, .c 3, .c 61, .p pv5 [pv2,pv3,pv11,pv541], .c 3, .c 37,
  .p pv3 [pv2,pv3,pv31,pv6143], .c 3, .c 7, .c 5, .c 3, .c 13, .c 643, .c 3, .c 5, .c 7, .c 3,
  .c 17, .c 991, .c 3, .c 53, .c 29, .c 3, .p pv3 [pv2,pv233,pv613], .c 5, .c 3, .c 43, .c 19,
  .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv22853], .c 59, .c 3, .c 881, .c 7, .c 3, .c 23, .c 5,
  .c 3, .c 11, .c 37, .c 3, .c 5, .p pv29 [pv2,pv3,pv31741], .c 3, .c 149, .c 547, .c 3, .c 7,
  .c 17, .c 3, .p pv2 [pv2,pv285673], .c 5, .c 3, .c 811, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv17,pv659], .c 3, .c 41, .c 11, .c 3, .c 19, .c 139, .c 3, .c 17, .c 5, .c 3,
  .c 7, .c 877, .c 3, .c 5, .p pv13 [pv2,pv3,pv7,pv19,pv179], .c 3, .c 631, .c 7, .c 3, .c 733,
  .c 467, .c 3, .c 31, .c 5, .c 3, .p pv7 [pv2,pv47,pv12157], .c 1069, .c 3, .c 5, .c 337, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv95231], .c 3, .p pv3 [pv2,pv211,pv677], .c 11, .c 3,
  .p pv5 [pv2,pv37,pv15443], .c 5,
]
private theorem h0139c15 : checkBlock 1142531 128 b0139c15 = true := by
  decide +kernel

private def b0139c16 : List Row := [
  .c 3, .p pv2 [pv2,pv285697], .c 13, .c 3, .c 5, .c 197, .c 3, .c 11, .c 29, .c 3, .c 271,
  .p pv7 [pv2,pv3,pv17,pv2801], .c 3, .c 7, .c 5, .c 3, .c 37, .p pv29 [pv2,pv3,pv5,pv7,pv907],
  .c 3, .c 5, .c 7, .c 3, .c 19, .p pv5 [pv2,pv3,pv29,pv821], .c 3, .p pv2 [pv2,pv285709], .c 53,
  .c 3, .c 13, .c 5, .c 3, .c 89, .p pv2 [pv2,pv3,pv5,pv19,pv401], .c 3, .c 5, .c 199, .c 3,
  .c 29, .p pv5 [pv2,pv3,pv7,pv27211], .c 3, .c 11, .c 7, .c 3, .c 127, .c 5, .c 3, .c 257,
  .p pv7 [pv2,pv3,pv5,pv2381], .c 3, .c 5, .c 71, .c 3, .p pv2 [pv2,pv5,pv7,pv29,pv563], .c 17,
  .c 3, .c 7, .c 47, .c 3, .c 641, .c 5, .c 3, .p pv2 [pv2,pv13,pv31,pv709], .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv23,pv41,pv101], .c 3, .c 13, .p pv2 [pv2,pv3,pv11,pv17317], .c 3, .c 17,
  .p pv13 [pv2,pv3,pv7937], .c 3, .c 11, .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv43,pv443], .c 3,
  .c 5, .c 13, .c 3, .c 97, .c 7, .c 3, .c 41, .p pv3 [pv2,pv3,pv71,pv2683], .c 3, .c 397, .c 5,
  .c 3, .p pv3 [pv2,pv142871], .p pv3 [pv2,pv3,pv5,pv31,pv1229], .c 3, .c 5, .c 11, .c 3, .c 7,
  .c 19, .c 3, .c 211, .c 487, .c 3, .c 47, .c 5, .c 3, .c 11, .c 31, .c 3, .c 5, .c 59, .c 3,
  .c 173, .p pv5 [pv2,pv3,pv13,pv17,pv431], .c 3, .c 101, .p pv2 [pv2,pv3,pv61,pv347], .c 3, .c 7,
  .c 5, .c 3, .c 17, .c 23, .c 3, .c 5, .c 7, .c 3, .c 37,
]
private theorem h0139c16 : checkBlock 1142787 128 b0139c16 = true := by
  decide +kernel

private def b0139c17 : List Row := [
  .c 11, .c 3, .p pv5 [pv2,pv17,pv33619], .p pv11 [pv2,pv3,pv97,pv491], .c 3,
  .p pv2 [pv2,pv285763], .c 5, .c 3, .c 19, .p pv2 [pv2,pv3,pv5,pv19051], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv59,pv3229], .c 3, .p pv13 [pv2,pv5,pv151,pv757], .p pv5 [pv2,pv3,pv7], .c 3,
  .c 13, .c 7, .c 3, .c 109, .c 5, .c 3, .p pv3 [pv2,pv71443], .p pv29 [pv2,pv3,pv5,pv13,pv977],
  .c 3, .c 5, .c 17, .c 3, .p pv13 [pv2,pv5,pv7,pv23,pv71], .c 13, .c 3, .c 7, .c 11, .c 3,
  .p pv3 [pv2,pv43,pv3323], .c 5, .c 3, .c 163, .c 7, .c 3, .c 5, .c 127, .c 3, .c 11, .c 541,
  .c 3, .c 239, .c 193, .c 3, .p pv5 [pv2,pv7,pv11,pv13,pv571], .c 5, .c 3, .c 7, .c 29, .c 3,
  .c 5, .c 53, .c 3, .p pv11 [pv2,pv5,pv28579], .c 7, .c 3, .p pv5 [pv2,pv571583], .c 23, .c 3,
  .c 19, .c 5, .c 3, .c 277, .c 13, .c 3, .c 5, .c 31, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv19,pv23,pv109], .c 3, .c 11, .c 17, .c 3, .c 41, .c 5, .c 3, .c 29, .c 19,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv467], .c 3, .c 67, .p pv3 [pv2,pv3,pv190537], .c 3,
  .p pv2 [pv2,pv7,pv37,pv2207], .c 983, .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv23,pv29,pv857],
  .c 11, .c 3, .c 5, .c 7, .c 3, .c 401, .c 73, .c 3, .p pv3 [pv2,pv142907], .c 13, .c 3, .c 11,
  .c 5, .c 3, .p pv2 [pv2,pv7,pv19,pv307], .c 389, .c 3, .c 5, .c 149, .c 3,
  .p pv3 [pv2,pv5,pv31,pv461], .p pv7 [pv2,pv3,pv7,pv163,pv167], .c 3, .c 19, .c 7, .c 3, .c 619,
  .c 5, .c 3,
]
private theorem h0139c17 : checkBlock 1143043 128 b0139c17 = true := by
  decide +kernel

private def b0139c18 : List Row := [
  .p pv2 [pv2,pv13,pv43973], .c 17, .c 3, .c 5, .c 11, .c 3, .c 13, .c 71, .c 3, .c 7, .c 503,
  .c 3, .c 61, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv11,pv5197],
  .c 887, .c 3, .p pv2 [pv2,pv571673], .c 271, .c 3, .c 23, .c 5, .c 3, .c 7, .c 59, .c 3, .c 5,
  .c 41, .c 3, .p pv11 [pv2,pv5,pv43,pv2659], .c 7, .c 3, .c 181, .c 1031, .c 3, .c 29, .c 5,
  .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv38113], .c 3, .c 5, .c 229, .c 3, .c 7, .c 17, .c 3,
  .p pv5 [pv2,pv11,pv51973], .c 211, .c 3, .c 43, .c 5, .c 3, .c 317, .c 101, .c 3, .c 5, .c 673,
  .c 3, .c 157, .p pv13 [pv2,pv3,pv15881], .c 3, .c 17, .c 11, .c 3, .c 7, .c 5, .c 3, .c 41,
  .c 419, .c 3, .c 5, .c 7, .c 3, .c 11, .c 47, .c 3, .c 13, .p pv2 [pv2,pv3,pv23,pv1381], .c 3,
  .p pv3 [pv2,pv11,pv73,pv89], .c 5, .c 3, .c 59, .p pv7 [pv2,pv3,pv5,pv13,pv733], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv63527], .c 3, .c 23, .c 13, .c 3, .c 31, .c 7, .c 3, .c 769, .c 5, .c 3,
  .c 107, .c 787, .c 3, .c 5, .c 191, .c 3, .c 557, .c 151, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv29,pv31,pv53], .c 3, .c 97, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 311,
  .c 3, .p pv17 [pv2,pv5,pv22871], .c 19,
]
private theorem h0139c18 : checkBlock 1143299 128 b0139c18 = true := by
  decide +kernel

private def b0139c19 : List Row := [
  .c 3, .c 29, .c 31, .c 3, .p pv2 [pv2,pv7,pv1667], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv2269], .c 3, .c 53, .c 7, .c 3, .p pv2 [pv2,pv29,pv19717],
  .p pv7 [pv2,pv3,pv157,pv607], .c 3, .c 11, .c 5, .c 3, .c 929, .p pv17 [pv2,pv3,pv5,pv953],
  .c 3, .c 5, .c 17, .c 3, .c 7, .c 41, .c 3, .c 709, .p pv3 [pv2,pv3,pv7,pv73,pv373], .c 3,
  .c 13, .c 5, .c 3, .c 19, .c 179, .c 3, .c 5, .c 11, .c 3, .c 17, .p pv2 [pv2,pv3,pv190607],
  .c 3, .p pv5 [pv2,pv7,pv81689], .c 13, .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv19 [pv2,pv3,pv5,pv7,pv389], .c 3, .c 5, .c 7, .c 3, .c 43, .c 29, .c 3, .c 1013,
  .p pv11 [pv2,pv3,pv190613], .c 3, .c 31, .c 5, .c 3, .c 61, .c 73, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv23827], .c 3, .c 13, .c 11, .c 3, .c 37, .c 7, .c 3, .c 571, .c 5, .c 3,
  .p pv11 [pv2,pv193,pv2963], .c 23, .c 3, .c 5, .c 13, .c 3, .c 29, .c 277, .c 3, .c 7, .c 71,
  .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv285937], .c 7, .c 3, .c 5, .c 43, .c 3, .c 131,
  .p pv2 [pv2,pv3,pv19,pv79,pv127], .c 3, .c 23, .c 11, .c 3, .c 751, .c 5, .c 3, .c 7, .c 19,
  .c 3, .c 5, .c 263, .c 3, .c 11, .c 7, .c 3, .c 233, .p pv3 [pv2,pv3,pv190633], .c 3,
  .p pv2 [pv2,pv11,pv51991], .c 5, .c 3, .p pv3 [pv2,pv1117],
]
private theorem h0139c19 : checkBlock 1143555 128 b0139c19 = true := by
  decide +kernel

private def b0139c20 : List Row := [
  .c 17, .c 3, .c 5, .p pv7 [pv2,pv3,pv47659], .c 3, .c 7, .c 83, .c 3, .c 757,
  .p pv2 [pv2,pv3,pv7,pv17,pv89], .c 3, .c 59, .c 5, .c 3, .c 47, .c 79, .c 3, .c 5, .c 29, .c 3,
  .p pv2 [pv2,pv5,pv22877], .c 227, .c 3, .c 11, .c 23, .c 3, .c 7, .c 5, .c 3, .c 31, .c 457,
  .c 3, .c 5, .c 7, .c 3, .c 71, .c 13, .c 3, .p pv5 [pv2,pv43,pv47,pv283], .c 127, .c 3,
  .p pv2 [pv2,pv37,pv59,pv131], .c 5, .c 3, .c 53, .c 11, .c 3, .c 5, .c 257, .c 3, .c 193, .c 17,
  .c 3, .c 89, .c 7, .c 3, .c 11, .c 5, .c 3, .c 37, .c 31, .c 3, .c 5, .c 107, .c 3, .c 41,
  .p pv3 [pv2,pv3,pv190657], .c 3, .c 7, .p pv23 [pv2,pv3,pv13,pv7333], .c 3,
  .p pv3 [pv2,pv19,pv53,pv71], .c 5, .c 3, .p pv11 [pv2,pv67,pv8537], .c 7, .c 3, .c 5, .c 11,
  .c 3, .c 19, .c 409, .c 3, .p pv3 [pv2,pv151,pv947], .c 197, .c 3, .c 73, .c 5, .c 3, .c 7,
  .c 373, .c 3, .c 5, .c 23, .c 3, .p pv3 [pv2,pv5,pv11,pv13], .c 7, .c 3,
  .p pv5 [pv2,pv89,pv6427], .c 19, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv97,pv5897], .c 29, .c 3,
  .c 5, .c 47, .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv286009], .c 13, .c 3, .c 23, .c 5, .c 3,
  .c 17, .c 199, .c 3, .c 5, .c 269, .c 3, .p pv2 [pv2,pv5,pv57203], .c 587, .c 3,
]
private theorem h0139c20 : checkBlock 1143811 128 b0139c20 = true := by
  decide +kernel

private def b0139c21 : List Row := [
  .c 977, .c 59, .c 3, .c 7, .c 5, .c 3, .c 29, .p pv19 [pv2,pv3,pv5,pv7,pv227], .c 3, .c 5, .c 7,
  .c 3, .c 13, .c 239, .c 3, .c 163, .c 11, .c 3, .p pv5 [pv2,pv572051], .c 5, .c 3, .c 139,
  .c 53, .c 3, .c 5, .c 13, .c 3, .c 11, .c 19, .c 3, .c 151, .c 7, .c 3, .c 359, .c 5, .c 3,
  .p pv2 [pv2,pv572069], .p pv2 [pv2,pv3,pv5,pv19069], .c 3, .c 5, .p pv3 [pv2,pv3,pv41,pv4651],
  .c 3, .c 17, .p pv67 [pv2,pv3,pv5297], .c 3, .c 7, .c 67, .c 3, .p pv2 [pv2,pv271,pv2111], .c 5,
  .c 3, .c 13, .c 7, .c 3, .c 5, .c 61, .c 3, .c 23, .p pv3 [pv2,pv3,pv13,pv14669], .c 3, .c 11,
  .c 307, .c 3, .p pv3 [pv2,pv7,pv1277], .c 5, .c 3, .c 7, .c 379, .c 3, .c 5, .c 499, .c 3,
  .p pv2 [pv2,pv5,pv31,pv3691], .c 7, .c 3, .c 53, .c 17, .c 3, .p pv5 [pv2,pv173,pv3307], .c 5,
  .c 3, .c 101, .c 11, .c 3, .c 5, .c 19, .c 3, .c 7, .p pv5 [pv2,pv3,pv11,pv5779], .c 3, .c 13,
  .p pv13 [pv2,pv3,pv7,pv139], .c 3, .c 11, .c 5, .c 3, .c 569, .p pv11 [pv2,pv3,pv5,pv13,pv163],
  .c 3, .c 5, .c 331, .c 3, .p pv7 [pv2,pv5,pv17,pv53,pv127], .c 13, .c 3,
  .p pv2 [pv2,pv7,pv40867], .p pv3 [pv2,pv3,pv151,pv421], .c 3, .c 7, .c 5, .c 3, .c 419,
  .p pv7 [pv2,pv3,pv5,pv7,pv5449], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv11443], .c 31, .c 3,
  .c 71, .c 47, .c 3, .c 19, .c 5, .c 3, .c 11, .c 17,
]
private theorem h0139c21 : checkBlock 1144067 128 b0139c21 = true := by
  decide +kernel

private def b0139c22 : List Row := [
  .c 3, .c 5, .p pv3 [pv2,pv3,pv269,pv709], .c 3, .c 479, .p pv2 [pv2,pv3,pv7,pv19,pv239], .c 3,
  .c 1019, .c 7, .c 3, .p pv7 [pv2,pv23,pv24877], .c 5, .c 3, .p pv2 [pv2,pv73,pv3919], .c 13,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv47,pv2029], .c 3, .c 137, .c 11, .c 3, .c 7, .c 29, .c 3, .c 37,
  .c 5, .c 3, .p pv2 [pv2,pv71,pv8059], .c 7, .c 3, .c 5, .c 139, .c 3, .c 109,
  .p pv5 [pv2,pv3,pv41,pv1163], .c 3, .c 127, .p pv3 [pv2,pv3,pv29,pv6577], .c 3, .c 13, .c 5,
  .c 3, .c 7, .c 23, .c 3, .c 5, .p pv17 [pv2,pv3,pv7,pv13,pv131], .c 3, .c 61, .c 7, .c 3, .c 19,
  .c 11, .c 3, .c 41, .c 5, .c 3, .p pv7 [pv2,pv389,pv1471], .p pv23 [pv2,pv3,pv5,pv11,pv17],
  .c 3, .c 5, .c 37, .c 3, .c 7, .p pv2 [pv2,pv3,pv283,pv337], .c 3, .c 17, .c 1049, .c 3, .c 181,
  .c 5, .c 3, .c 149, .c 613, .c 3, .c 5, .p pv2 [pv2,pv3,pv10597], .c 3, .c 13,
  .p pv3 [pv2,pv3,pv53,pv59,pv61], .c 3, .c 83, .c 31, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv137,pv4177], .c 449, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv114451], .c 281,
  .c 3, .c 11, .p pv3 [pv2,pv3,pv190753], .c 3, .p pv2 [pv2,pv19,pv30119], .c 5, .c 3,
  .p pv3 [pv2,pv7,pv11,pv929], .c 43, .c 3, .c 5, .p pv17 [pv2,pv3,pv103,pv463], .c 3, .c 19,
  .c 29, .c 3, .c 131, .c 7, .c 3, .c 953, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 73, .c 3,
  .c 239, .p pv7 [pv2,pv3,pv11,pv13,pv23,pv29], .c 3, .c 7,
]
private theorem h0139c22 : checkBlock 1144323 128 b0139c22 = true := by
  decide +kernel

private def b0139c23 : List Row := [
  .c 19, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv53,pv5399], .c 7, .c 3, .c 5, .c 41, .c 3, .c 29,
  .p pv2 [pv2,pv3,pv63589], .c 3, .p pv5 [pv2,pv572303], .c 109, .c 3, .c 31, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv6359], .c 3, .c 5, .c 11, .c 3, .c 79, .c 7, .c 3, .c 13, .c 103, .c 3,
  .p pv2 [pv2,pv572321], .c 5, .c 3, .c 11, .c 127, .c 3, .c 5, .p pv7 [pv2,pv3,pv7949], .c 3,
  .c 7, .c 13, .c 3, .p pv2 [pv2,pv572333], .c 37, .c 3, .c 367, .c 5, .c 3, .c 41,
  .p pv7 [pv2,pv3,pv5,pv9539], .c 3, .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv113,pv1013], .c 11,
  .c 3, .c 97, .c 421, .c 3, .c 7, .c 5, .c 3, .c 653, .c 739, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv41,pv349], .p pv5 [pv2,pv3,pv190787], .c 3, .p pv5 [pv2,pv11,pv61,pv853],
  .c 17, .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv7,pv11681], .c 13, .c 3, .c 5, .c 53, .c 3,
  .c 293, .c 347, .c 3, .p pv2 [pv2,pv23,pv541], .c 7, .c 3, .c 17, .c 5, .c 3, .c 19, .c 229,
  .c 3, .c 5, .c 59, .c 3, .c 11, .p pv3 [pv2,pv3,pv63599], .c 3, .c 7, .c 43, .c 3, .c 13, .c 5,
  .c 3, .c 31, .c 7, .c 3, .c 5, .c 19, .c 3, .c 251, .c 773, .c 3, .c 37, .c 13, .c 3,
  .p pv5 [pv2,pv7,pv81773], .c 5, .c 3, .c 7, .c 17, .c 3,
]
private theorem h0139c23 : checkBlock 1144579 128 b0139c23 = true := by
  decide +kernel

private def b0139c24 : List Row := [
  .c 5, .p pv2 [pv2,pv3,pv7,pv11,pv59], .c 3, .c 277, .c 7, .c 3, .c 11, .c 829, .c 3, .c 53,
  .c 5, .c 3, .c 73, .c 31, .c 3, .c 5, .p pv3 [pv2,pv3,pv190811], .c 3, .c 7, .c 47, .c 3,
  .p pv2 [pv2,pv193,pv1483], .p pv3 [pv2,pv3,pv7,pv27259], .c 3, .c 19, .c 5, .c 3,
  .p pv3 [pv2,pv143111], .c 11, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv107],
  .p pv5 [pv2,pv3,pv11,pv19,pv83], .c 3, .p pv2 [pv2,pv7,pv53,pv1543], .c 61, .c 3, .c 7, .c 5,
  .c 3, .p pv17 [pv2,pv43,pv13313], .c 19, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv114493],
  .c 17, .c 3, .c 487, .p pv11 [pv2,pv3,pv190823], .c 3, .c 139, .c 5, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv5,pv17,pv449], .c 3, .c 5, .c 11, .c 3, .c 43, .c 23, .c 3, .c 17, .c 7, .c 3,
  .p pv2 [pv2,pv286243], .c 5, .c 3, .c 11, .p pv11 [pv2,pv3,pv5,pv6361], .c 3, .c 5, .c 691,
  .c 3, .c 241, .p pv5 [pv2,pv3,pv11927], .c 3, .c 7, .c 463, .c 3, .p pv2 [pv2,pv37,pv15473],
  .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 71, .c 3, .p pv2 [pv2,pv5,pv57251], .c 11, .c 3, .c 13,
  .c 113, .c 3, .c 151, .c 5, .c 3, .c 7, .c 769, .c 3, .c 5, .c 31, .c 3, .c 103, .c 7, .c 3,
  .p pv5 [pv2,pv11,pv3253], .p pv2 [pv2,pv3,pv190843], .c 3, .c 179, .c 5, .c 3, .c 17, .c 131,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv37,pv2579], .c 3, .c 7, .c 593, .c 3, .c 173, .c 11,
]
private theorem h0139c24 : checkBlock 1144835 128 b0139c24 = true := by
  decide +kernel

private def b0139c25 : List Row := [
  .c 3, .p pv2 [pv2,pv13,pv19,pv61], .c 5, .c 3, .p pv2 [pv2,pv572549], .c 23, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv63617], .c 3, .c 11, .c 37, .c 3, .c 887, .c 167, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv143141], .c 13, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv31,pv1847],
  .p pv17 [pv2,pv3,pv113,pv563], .c 3, .c 23, .c 19, .c 3, .c 61, .c 5, .c 3, .c 71, .c 197, .c 3,
  .c 5, .c 431, .c 3, .c 17, .p pv2 [pv2,pv3,pv7,pv13633], .c 3, .c 11, .c 7, .c 3, .c 13, .c 5,
  .c 3, .p pv3 [pv2,pv11,pv17,pv1531], .p pv3 [pv2,pv3,pv5,pv59,pv647], .c 3, .c 5, .c 941, .c 3,
  .c 863, .p pv2 [pv2,pv3,pv31,pv47,pv131], .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv41,pv6983],
  .c 5, .c 3, .c 43, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv190871], .c 3, .c 67, .c 31, .c 3,
  .c 587, .c 17, .c 3, .c 11, .c 5, .c 3, .c 7, .c 883, .c 3, .c 5, .c 103, .c 3, .c 13, .c 7,
  .c 3, .c 313, .p pv13 [pv2,pv3,pv29,pv1097], .c 3, .c 17, .c 5, .c 3, .c 97,
  .p pv13 [pv2,pv3,pv5,pv1193], .c 3, .c 5, .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv95441], .c 3,
  .c 29, .p pv2 [pv2,pv3,pv7,pv11,pv37,pv67], .c 3, .p pv5 [pv2,pv572651], .c 5, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv5,pv38177], .c 3, .c 5, .c 83, .c 3, .c 317, .p pv2 [pv2,pv3,pv63629], .c 3,
  .p pv5 [pv2,pv7,pv13,pv29,pv31], .p pv7 [pv2,pv3,pv107,pv223], .c 3, .c 7, .c 5, .c 3, .c 13,
  .c 17, .c 3, .c 5,
]
private theorem h0139c25 : checkBlock 1145091 128 b0139c25 = true := by
  decide +kernel

private def b0139c26 : List Row := [
  .c 7, .c 3, .c 439, .c 11, .c 3, .c 31, .p pv13 [pv2,pv3,pv17,pv19,pv197], .c 3, .c 149, .c 5,
  .c 3, .p pv3 [pv2,pv7,pv113,pv181], .p pv2 [pv2,pv3,pv5,pv73,pv523], .c 3, .c 5, .c 19, .c 3,
  .p pv2 [pv2,pv5,pv57269], .c 53, .c 3, .p pv2 [pv2,pv11,pv4733], .c 7, .c 3,
  .p pv3 [pv2,pv17,pv4211], .c 5, .c 3, .c 449, .c 163, .c 3, .c 5, .c 367, .c 3,
  .p pv2 [pv2,pv5,pv7,pv16363], .c 29, .c 3, .c 7, .c 11, .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv233,pv1229], .c 7, .c 3, .c 5, .c 47, .c 3, .c 11, .c 13, .c 3, .c 347, .c 257,
  .c 3, .c 19, .c 5, .c 3, .c 7, .p pv29 [pv2,pv3,pv5,pv17,pv1123], .c 3, .c 5, .c 641, .c 3,
  .c 29, .c 7, .c 3, .c 17, .p pv11 [pv2,pv3,pv190913], .c 3, .c 37, .c 5, .c 3, .c 53, .c 19,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv4339], .c 3, .c 7, .c 491, .c 3, .c 11,
  .p pv19 [pv2,pv3,pv7,pv13,pv1049], .c 3, .c 661, .c 5, .c 3, .c 61, .c 13, .c 3, .c 5, .c 239,
  .c 3, .c 47, .p pv17 [pv2,pv3,pv95461], .c 3, .p pv3 [pv2,pv7,pv2557],
  .p pv2 [pv2,pv3,pv23,pv2767], .c 3, .c 7, .c 5, .c 3, .c 181, .c 11, .c 3, .c 5, .c 7, .c 3,
  .c 23, .c 43, .c 3, .c 19, .c 359, .c 3, .c 11, .c 5, .c 3, .c 17, .c 41, .c 3, .c 5, .c 29,
  .c 3, .c 331, .p pv5 [pv2,pv3,pv7,pv2273], .c 3, .c 1033, .c 7, .c 3,
]
private theorem h0139c26 : checkBlock 1145347 128 b0139c26 = true := by
  decide +kernel

private def b0139c27 : List Row := [
  .c 59, .c 5, .c 3, .c 409, .p pv3 [pv2,pv3,pv5,pv4243], .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv7,pv167], .p pv3 [pv2,pv3,pv41,pv4657], .c 3, .c 7, .c 157, .c 3, .c 67, .c 5,
  .c 3, .c 11, .c 7, .c 3, .c 5, .c 17, .c 3, .c 13, .c 23, .c 3, .c 401,
  .p pv2 [pv2,pv3,pv79,pv2417], .c 3, .c 41, .c 5, .c 3, .c 7, .c 269, .c 3, .c 5, .c 13, .c 3,
  .c 17, .c 7, .c 3, .c 229, .p pv7 [pv2,pv3,pv47737], .c 3, .p pv2 [pv2,pv43,pv6661], .c 5, .c 3,
  .c 23, .c 53, .c 3, .c 5, .c 113, .c 3, .c 7, .p pv5 [pv2,pv3,pv23869], .c 3, .c 379, .c 19,
  .c 3, .p pv2 [pv2,pv23,pv24907], .c 5, .c 3, .c 13, .c 137, .c 3, .c 5, .c 79, .c 3,
  .p pv2 [pv2,pv5,pv57287], .p pv3 [pv2,pv3,pv13,pv37,pv397], .c 3, .p pv2 [pv2,pv7,pv81839],
  .c 11, .c 3, .c 7, .c 5, .c 3, .c 509, .c 29, .c 3, .c 5, .c 7, .c 3, .c 11,
  .p pv5 [pv2,pv3,pv103], .c 3, .c 139, .c 37, .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv151,pv271], .c 23, .c 3, .c 5, .p pv17 [pv2,pv3,pv95483], .c 3,
  .p pv3 [pv2,pv5,pv17,pv337], .p pv2 [pv2,pv3,pv7,pv27281], .c 3, .c 13, .c 7, .c 3, .c 47, .c 5,
  .c 3, .c 29, .c 43, .c 3, .c 5, .c 41, .c 3, .p pv7 [pv2,pv5,pv7,pv16369], .c 13, .c 3, .c 7,
  .c 59, .c 3, .p pv2 [pv2,pv199,pv2879], .c 5, .c 3, .p pv7 [pv2,pv11,pv29,pv449], .c 7, .c 3,
  .c 5, .c 131,
]
private theorem h0139c27 : checkBlock 1145603 128 b0139c27 = true := by
  decide +kernel

private def b0139c28 : List Row := [
  .c 3, .c 97, .c 107, .c 3, .c 283, .c 71, .c 3, .p pv3 [pv2,pv7,pv13,pv787], .c 5, .c 3, .c 7,
  .c 11, .c 3, .c 5, .c 599, .c 3, .c 263, .c 7, .c 3, .p pv3 [pv2,pv227,pv631],
  .p pv2 [pv2,pv3,pv13,pv59,pv83], .c 3, .c 11, .c 5, .c 3, .c 19, .c 13, .c 3, .c 5, .c 109,
  .c 3, .c 7, .c 293, .c 3, .c 37, .c 23, .c 3, .c 113, .c 5, .c 3, .c 151, .c 211, .c 3, .c 5,
  .c 11, .c 3, .c 937, .c 17, .c 3, .c 59, .c 149, .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv7,pv17,pv107], .c 3, .c 5, .c 7, .c 3, .c 83, .p pv5 [pv2,pv3,pv190997],
  .c 3, .c 17, .c 13, .c 3, .c 29, .c 5, .c 3, .p pv7 [pv2,pv7,pv23,pv3559], .c 37, .c 3, .c 5,
  .c 61, .c 3, .c 71, .c 11, .c 3, .c 1039, .c 7, .c 3, .c 19, .c 5, .c 3, .c 431, .c 307, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv43,pv2221], .c 3, .c 13, .p pv2 [pv2,pv3,pv19,pv1117], .c 3, .c 7,
  .p pv13 [pv2,pv3,pv47,pv127], .c 3, .c 79, .c 5, .c 3, .c 271, .c 7, .c 3, .c 5, .c 13, .c 3,
  .p pv11 [pv2,pv5,pv31,pv3697], .c 41, .c 3, .c 107, .c 11, .c 3, .p pv2 [pv2,pv7,pv71,pv1153],
  .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv11,pv23,pv151], .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv379],
  .c 3, .c 11, .c 7, .c 3, .c 601, .c 29, .c 3, .c 23,
]
private theorem h0139c28 : checkBlock 1145859 128 b0139c28 = true := by
  decide +kernel

private def b0139c29 : List Row := [
  .c 5, .c 3, .c 13, .c 167, .c 3, .c 5, .c 233, .c 3, .c 7, .p pv11 [pv2,pv3,pv13,pv31,pv79],
  .c 3, .c 19, .c 397, .c 3, .p pv5 [pv2,pv47,pv89,pv137], .c 5, .c 3, .c 37, .c 433, .c 3, .c 5,
  .c 17, .c 3, .c 677, .c 31, .c 3, .c 11, .c 67, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv53,pv983], .c 881, .c 3, .c 5, .c 7, .c 3, .c 17, .c 59, .c 3, .c 13, .c 281,
  .c 3, .c 499, .c 5, .c 3, .c 269, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv163,pv293], .c 3,
  .p pv2 [pv2,pv5,pv223,pv257], .c 13, .c 3, .c 193, .c 7, .c 3, .c 11, .c 5, .c 3, .c 877,
  .c 151, .c 3, .c 5, .c 479, .c 3, .c 19, .c 331, .c 3, .c 7, .c 17, .c 3,
  .p pv5 [pv2,pv13,pv44087], .c 5, .c 3, .c 593, .c 7, .c 3, .c 5, .c 11, .c 3,
  .p pv7 [pv2,pv5,pv28657], .c 29, .c 3, .c 31, .c 19, .c 3, .c 17, .c 5, .c 3, .c 7, .c 13, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv7,pv557], .c 3, .c 59, .c 7, .c 3, .c 251, .c 41, .c 3,
  .p pv2 [pv2,pv573161], .c 5, .c 3, .p pv3 [pv2,pv143291], .p pv7 [pv2,pv3,pv5,pv47,pv271], .c 3,
  .c 5, .c 43, .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv19,pv97,pv311], .c 31, .c 3, .c 13, .c 5,
  .c 3, .c 773, .c 17, .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv23,pv71], .c 3,
]
private theorem h0139c29 : checkBlock 1146115 128 b0139c29 = true := by
  decide +kernel

private def b0139c30 : List Row := [
  .c 37, .c 61, .c 3, .c 47, .c 13, .c 3, .c 7, .c 5, .c 3, .c 23,
  .p pv29 [pv2,pv3,pv5,pv7,pv53,pv103], .c 3, .c 5, .c 7, .c 3, .c 41, .c 19, .c 3,
  .p pv5 [pv2,pv149,pv3847], .c 11, .c 3, .p pv2 [pv2,pv17,pv23,pv733], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv13,pv6299], .p pv19 [pv2,pv3,pv5,pv11,pv193], .c 3, .c 5, .c 409, .c 3, .c 11,
  .c 283, .c 3, .c 67, .c 7, .c 3, .c 53, .c 5, .c 3, .c 743, .c 101, .c 3, .c 5, .c 13, .c 3,
  .p pv2 [pv2,pv5,pv7,pv19,pv431], .c 17, .c 3, .c 7, .c 643, .c 3, .c 31, .c 5, .c 3, .c 19,
  .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv29,pv599], .c 3, .p pv2 [pv2,pv5,pv114649], .c 103,
  .c 3, .c 11, .c 577, .c 3, .c 277, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv12739], .c 3, .c 5,
  .c 19, .c 3, .p pv3 [pv2,pv5,pv28663], .c 7, .c 3, .c 23, .p pv7 [pv2,pv3,pv1327], .c 3,
  .p pv2 [pv2,pv286633], .c 5, .c 3, .p pv2 [pv2,pv73,pv7853], .c 11, .c 3, .c 5, .c 59, .c 3,
  .c 7, .c 137, .c 3, .c 1049, .p pv19 [pv2,pv3,pv7,pv27299], .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv251,pv571], .c 67, .c 3, .c 5, .c 227, .c 3, .p pv2 [pv2,pv5,pv57329], .c 1021,
  .c 3, .c 13, .c 317, .c 3, .c 7, .c 5, .c 3, .c 17, .c 271, .c 3, .c 5, .c 7, .c 3, .c 73,
  .c 13, .c 3, .c 61, .c 23, .c 3, .c 607, .c 5,
]
private theorem h0139c30 : checkBlock 1146371 128 b0139c30 = true := by
  decide +kernel

private def b0139c31 : List Row := [
  .c 3, .c 11, .c 19, .c 3, .c 5, .c 97, .c 3, .c 1051, .c 131, .c 3, .c 41, .c 7, .c 3, .c 101,
  .c 5, .c 3, .c 31, .p pv2 [pv2,pv3,pv5,pv29,pv659], .c 3, .c 5, .c 17, .c 3,
  .p pv7 [pv2,pv5,pv7,pv16381], .c 11, .c 3, .c 7, .p pv17 [pv2,pv3,pv13,pv61,pv241], .c 3,
  .c 127, .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv47779], .c 3, .c 17,
  .p pv3 [pv2,pv3,pv383,pv499], .c 3, .c 19, .p pv2 [pv2,pv3,pv53,pv601], .c 3,
  .p pv3 [pv2,pv7,pv20477], .c 5, .c 3, .c 7, .c 31, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv19,pv479],
  .c 3, .p pv2 [pv2,pv5,pv13,pv8821], .c 7, .c 3, .c 197, .c 11, .c 3, .c 13, .c 5, .c 3, .c 641,
  .c 971, .c 3, .c 5, .c 23, .c 3, .c 7, .p pv3 [pv2,pv3,pv63709], .c 3, .c 43, .c 13, .c 3,
  .p pv2 [pv2,pv11,pv67,pv389], .c 5, .c 3, .p pv2 [pv2,pv37,pv15497],
  .p pv17 [pv2,pv3,pv5,pv23,pv277], .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv11243], .c 3,
  .p pv17 [pv2,pv5,pv114679], .p pv5 [pv2,pv3,pv71,pv673], .c 3, .p pv2 [pv2,pv7,pv5851],
  .p pv11 [pv2,pv3,pv7079], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv13,pv11027], .c 41, .c 3, .c 5,
  .c 7, .c 3, .c 13, .p pv3 [pv2,pv3,pv191137], .c 3, .c 11, .p pv2 [pv2,pv3,pv95569], .c 3,
  .p pv3 [pv2,pv229,pv313], .c 5, .c 3, .c 67, .p pv7 [pv2,pv3,pv5,pv19,pv503], .c 3, .c 5, .c 13,
  .c 3, .c 463, .c 43, .c 3, .p pv3 [pv2,pv143357], .c 7, .c 3, .c 29, .c 5, .c 3,
  .p pv2 [pv2,pv163,pv1759], .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv31,pv3083], .c 3,
  .p pv3 [pv2,pv5,pv7],
]
private theorem h0139c31 : checkBlock 1146627 128 b0139c31 = true := by
  decide +kernel

def rows0139 : List Row :=
  b0139c00 ++ b0139c01 ++ b0139c02 ++ b0139c03 ++ b0139c04 ++ b0139c05 ++ b0139c06 ++ b0139c07 ++
  b0139c08 ++ b0139c09 ++ b0139c10 ++ b0139c11 ++ b0139c12 ++ b0139c13 ++ b0139c14 ++ b0139c15 ++
  b0139c16 ++ b0139c17 ++ b0139c18 ++ b0139c19 ++ b0139c20 ++ b0139c21 ++ b0139c22 ++ b0139c23 ++
  b0139c24 ++ b0139c25 ++ b0139c26 ++ b0139c27 ++ b0139c28 ++ b0139c29 ++ b0139c30 ++ b0139c31

attribute [local irreducible] checkBlock checkRows checkPrime

theorem checked0139 : checkBlock 1138691 4096 rows0139 = true :=
  checkBlock_append h0139c00 (
    checkBlock_append h0139c01 (
    checkBlock_append h0139c02 (
    checkBlock_append h0139c03 (
    checkBlock_append h0139c04 (
    checkBlock_append h0139c05 (
    checkBlock_append h0139c06 (
    checkBlock_append h0139c07 (
    checkBlock_append h0139c08 (
    checkBlock_append h0139c09 (
    checkBlock_append h0139c10 (
    checkBlock_append h0139c11 (
    checkBlock_append h0139c12 (
    checkBlock_append h0139c13 (
    checkBlock_append h0139c14 (
    checkBlock_append h0139c15 (
    checkBlock_append h0139c16 (
    checkBlock_append h0139c17 (
    checkBlock_append h0139c18 (
    checkBlock_append h0139c19 (
    checkBlock_append h0139c20 (
    checkBlock_append h0139c21 (
    checkBlock_append h0139c22 (
    checkBlock_append h0139c23 (
    checkBlock_append h0139c24 (
    checkBlock_append h0139c25 (
    checkBlock_append h0139c26 (
    checkBlock_append h0139c27 (
    checkBlock_append h0139c28 (
    checkBlock_append h0139c29 (
    checkBlock_append h0139c30 (
    h0139c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
