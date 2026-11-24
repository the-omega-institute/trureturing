/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0142
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0142.checked0142
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table018
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table021
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table025
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table032
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table043
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table064
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table118

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0142c00 : List Row := [
  .c 7, .c 431, .c 3, .p pv3 [pv2,pv11,pv13219], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 181,
  .c 3, .c 139, .c 17, .c 3, .c 47, .c 751, .c 3, .c 59, .c 5, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv5,pv17,pv2281], .c 3, .c 5, .c 23, .c 3, .c 67, .c 7, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv73,pv83], .c 3, .p pv3 [pv2,pv19,pv15307], .c 5, .c 3,
  .p pv2 [pv2,pv11,pv52879], .c 1049, .c 3, .c 5, .c 911, .c 3, .c 7, .p pv19 [pv2,pv3,pv48473],
  .c 3, .c 13, .c 449, .c 3, .c 23, .c 5, .c 3, .c 233, .c 11, .c 3, .c 5, .c 1009, .c 3, .c 191,
  .c 13, .c 3, .c 373, .c 19, .c 3, .c 7, .c 5, .c 3, .c 31, .c 73, .c 3, .c 5, .c 7, .c 3, .c 83,
  .c 283, .c 3, .p pv3 [pv2,pv41,pv3547], .c 101, .c 3, .p pv5 [pv2,pv13,pv29,pv1543], .c 5, .c 3,
  .c 17, .p pv41 [pv2,pv3,pv5,pv31,pv139], .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv14543],
  .c 487, .c 3, .c 127, .c 7, .c 3, .c 61, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv109,pv593], .c 3, .c 433, .p pv7 [pv2,pv3,pv24239], .c 3, .c 7,
  .p pv3 [pv2,pv3,pv23,pv8431], .c 3, .p pv2 [pv2,pv197,pv2953], .c 5, .c 3, .c 167, .c 7, .c 3,
  .c 5, .c 17, .c 3, .c 23, .c 11, .c 3, .p pv2 [pv2,pv581753], .c 29, .c 3, .c 13, .c 5, .c 3,
  .c 7, .p pv13 [pv2,pv3,pv5,pv101],
]
private theorem h0142c00 : checkBlock 1163267 128 b0142c00 = true := by
  decide +kernel

private def b0142c01 : List Row := [
  .c 3, .c 5, .c 157, .c 3, .c 17, .c 7, .c 3, .c 43, .c 13, .c 3, .p pv5 [pv2,pv131,pv4441],
  .c 5, .c 3, .c 229, .p pv3 [pv2,pv3,pv5,pv7757], .c 3, .c 5, .p pv2 [pv2,pv3,pv32321], .c 3,
  .c 7, .c 419, .c 3, .c 29, .c 11, .c 3, .c 557, .c 5, .c 3, .c 19,
  .p pv7 [pv2,pv3,pv5,pv11,pv41,pv43], .c 3, .c 5, .p pv3 [pv2,pv3,pv89,pv2179], .c 3, .c 11,
  .c 23, .c 3, .c 193, .c 17, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv145451],
  .p pv2 [pv2,pv3,pv5,pv7,pv1847], .c 3, .c 5, .c 7, .c 3, .c 41, .c 43, .c 3,
  .p pv2 [pv2,pv47,pv12379], .p pv7 [pv2,pv3,pv32323], .c 3, .c 17, .c 5, .c 3, .c 23,
  .p pv7 [pv2,pv3,pv5,pv9697], .c 3, .c 5, .c 31, .c 3, .p pv2 [pv2,pv5,pv17,pv37],
  .p pv2 [pv2,pv3,pv7,pv1979], .c 3, .c 11, .c 7, .c 3, .p pv5 [pv2,pv23,pv41,pv617], .c 5, .c 3,
  .c 13, .p pv3 [pv2,pv3,pv5,pv79,pv491], .c 3, .c 5, .c 277, .c 3, .c 907, .c 29, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv48487], .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv571,pv1019], .c 7, .c 3, .c 5,
  .c 317, .c 3, .p pv17 [pv2,pv5,pv116371], .p pv5 [pv2,pv3,pv11,pv19,pv29], .c 3,
  .p pv2 [pv2,pv59,pv4931], .p pv3 [pv2,pv3,pv17,pv3803], .c 3, .c 11, .c 5, .c 3, .c 7, .c 19,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv2309], .c 3, .c 29, .c 7, .c 3, .c 13, .c 79, .c 3,
  .p pv3 [pv2,pv17,pv43,pv199], .c 5, .c 3, .p pv7 [pv2,pv61,pv9539], .c 37, .c 3, .c 5, .c 11,
  .c 3, .c 7, .c 13, .c 3, .c 23,
]
private theorem h0142c01 : checkBlock 1163523 128 b0142c01 = true := by
  decide +kernel

private def b0142c02 : List Row := [
  .c 877, .c 3, .p pv5 [pv2,pv581891], .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv67,pv193], .c 3,
  .c 5, .c 103, .c 3, .c 881, .c 17, .c 3, .c 19, .c 577, .c 3, .c 7, .c 5, .c 3, .c 61,
  .p pv11 [pv2,pv3,pv5,pv7,pv17,pv163], .c 3, .c 5, .c 7, .c 3, .p pv11 [pv2,pv5,pv181,pv643],
  .c 11, .c 3, .c 17, .c 73, .c 3, .p pv2 [pv2,pv581921], .c 5, .c 3, .p pv3 [pv2,pv7,pv2969],
  .c 13, .c 3, .c 5, .c 29, .c 3, .c 47, .c 947, .c 3, .c 41, .c 7, .c 3, .p pv3 [pv2,pv37,pv983],
  .c 5, .c 3, .p pv13 [pv2,pv359,pv1621], .c 43, .c 3, .c 5, .c 251, .c 3,
  .p pv7 [pv2,pv5,pv7,pv13,pv1279], .c 59, .c 3, .c 7, .c 11, .c 3, .c 13, .c 5, .c 3, .c 37,
  .c 7, .c 3, .c 5, .c 1061, .c 3, .c 11, .p pv2 [pv2,pv3,pv17,pv11411], .c 3, .c 727, .c 13,
  .c 3, .c 53, .c 5, .c 3, .c 7, .c 61, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv37,pv107], .c 3, .c 199,
  .c 7, .c 3, .c 31, .c 19, .c 3, .c 269, .c 5, .c 3, .p pv3 [pv2,pv13,pv1399],
  .p pv2 [pv2,pv3,pv5,pv479], .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv4409], .c 3, .c 7, .c 37, .c 3,
  .c 11, .p pv2 [pv2,pv3,pv7,pv31,pv149], .c 3, .p pv3 [pv2,pv83,pv1753], .c 5, .c 3, .c 1031,
  .p pv17 [pv2,pv3,pv5,pv97], .c 3, .c 5, .c 13, .c 3, .c 59, .c 113, .c 3, .c 941, .c 31, .c 3,
  .c 7, .c 5, .c 3, .p pv2 [pv2,pv291007], .c 11, .c 3,
]
private theorem h0142c02 : checkBlock 1163779 128 b0142c02 = true := by
  decide +kernel

private def b0142c03 : List Row := [
  .c 5, .c 7, .c 3, .c 17, .p pv5 [pv2,pv3,pv11,pv5879], .c 3, .c 313, .c 47, .c 3, .c 11, .c 5,
  .c 3, .c 13, .c 719, .c 3, .c 5, .p pv2 [pv2,pv3,pv131,pv1481], .c 3,
  .p pv19 [pv2,pv5,pv59,pv1973], .c 19, .c 3, .p pv2 [pv2,pv23,pv12653], .c 7, .c 3, .c 509, .c 5,
  .c 3, .c 29, .p pv3 [pv2,pv3,pv5,pv38803], .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv7,pv1663],
  .c 401, .c 3, .c 7, .c 17, .c 3, .c 41, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 331, .c 3,
  .c 37, .c 373, .c 3, .c 13, .c 43, .c 3, .c 17, .c 5, .c 3, .c 7, .c 809, .c 3, .c 5, .c 167,
  .c 3, .c 491, .c 7, .c 3, .c 499, .c 239, .c 3, .p pv2 [pv2,pv291043], .c 5, .c 3,
  .p pv2 [pv2,pv709,pv821], .p pv2 [pv2,pv3,pv5,pv19403], .c 3, .c 5, .c 19, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv67,pv181], .c 3, .c 131, .p pv3 [pv2,pv3,pv7,pv53,pv523], .c 3,
  .p pv2 [pv2,pv13,pv44777], .c 5, .c 3, .c 89, .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv179,pv271],
  .c 3, .p pv2 [pv2,pv5,pv58211], .c 79, .c 3, .c 101, .c 11, .c 3, .c 7, .c 5, .c 3, .c 113,
  .c 13, .c 3, .c 5, .c 7, .c 3, .c 11, .p pv2 [pv2,pv3,pv97021], .c 3, .c 449, .c 67, .c 3,
  .c 19, .c 5, .c 3, .c 571, .c 241, .c 3, .c 5, .c 41, .c 3, .c 743, .c 23, .c 3,
  .p pv5 [pv2,pv149,pv3907], .c 7,
]
private theorem h0142c03 : checkBlock 1164035 128 b0142c03 = true := by
  decide +kernel

private def b0142c04 : List Row := [
  .c 3, .c 13, .c 5, .c 3, .c 653, .c 19, .c 3, .c 5, .c 61, .c 3, .c 43, .c 17, .c 3, .c 7,
  .c 13, .c 3, .p pv2 [pv2,pv582161], .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 433, .c 3, .c 317,
  .p pv5 [pv2,pv3,pv194057], .c 3, .c 17, .c 199, .c 3, .c 37, .c 5, .c 3, .c 7, .c 11, .c 3,
  .c 5, .p pv7 [pv2,pv3,pv7,pv9241], .c 3, .c 13, .c 7, .c 3, .c 19, .c 29, .c 3, .c 11, .c 5,
  .c 3, .c 251, .c 31, .c 3, .c 5, .c 13, .c 3, .c 7, .c 139, .c 3, .c 83,
  .p pv19 [pv2,pv3,pv7,pv29,pv239], .c 3, .p pv2 [pv2,pv291103], .c 5, .c 3,
  .p pv2 [pv2,pv582209], .c 23, .c 3, .c 5, .c 11, .c 3, .p pv7 [pv2,pv5,pv116443],
  .p pv5 [pv2,pv3,pv17,pv1427], .c 3, .c 29, .p pv17 [pv2,pv3,pv11,pv5881], .c 3, .c 7, .c 5,
  .c 3, .c 11, .c 307, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv11,pv67,pv79], .c 53, .c 3,
  .c 23, .c 157, .c 3, .c 643, .c 5, .c 3, .p pv7 [pv2,pv7,pv83177], .c 107, .c 3, .c 5, .c 271,
  .c 3, .c 19, .c 11, .c 3, .p pv3 [pv2,pv73,pv997], .c 7, .c 3, .p pv5 [pv2,pv582251], .c 5,
  .c 3, .c 211, .p pv59 [pv2,pv3,pv5,pv19,pv227], .c 3, .c 5, .c 17, .c 3,
  .p pv3 [pv2,pv5,pv7,pv4159], .c 41, .c 3, .c 7, .c 19, .c 3, .p pv2 [pv2,pv347,pv839], .c 5,
  .c 3, .c 79, .c 7, .c 3, .c 5,
]
private theorem h0142c04 : checkBlock 1164291 128 b0142c04 = true := by
  decide +kernel

private def b0142c05 : List Row := [
  .c 353, .c 3, .c 17, .c 13, .c 3, .p pv2 [pv2,pv109,pv2671], .c 11, .c 3, .c 547, .c 5, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv5,pv11,pv3529], .c 3, .c 5, .c 31, .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv19,pv1613], .p pv2 [pv2,pv3,pv107,pv907], .c 3, .p pv3 [pv2,pv11,pv13,pv509],
  .c 5, .c 3, .p pv7 [pv2,pv582299], .c 59, .c 3, .c 5, .p pv5 [pv2,pv3,pv194101], .c 3, .c 7,
  .c 47, .c 3, .p pv3 [pv2,pv145577], .c 17, .c 3, .p pv5 [pv2,pv53,pv10987], .c 5, .c 3,
  .p pv2 [pv2,pv23,pv12659], .c 13, .c 3, .c 5, .c 137, .c 3, .p pv17 [pv2,pv5,pv29,pv251], .c 19,
  .c 3, .c 11, .c 37, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv11,pv167,pv317], .c 67, .c 3, .c 5,
  .c 7, .c 3, .p pv7 [pv2,pv5,pv13,pv17,pv31], .c 61, .c 3, .c 883, .c 97, .c 3, .c 13, .c 5,
  .c 3, .p pv3 [pv2,pv7,pv10399], .c 11, .c 3, .c 5, .c 23, .c 3, .c 31, .c 383, .c 3, .c 47,
  .c 7, .c 3, .c 11, .c 5, .c 3, .c 19, .c 17, .c 3, .c 5, .c 29, .c 3,
  .p pv7 [pv2,pv5,pv7,pv2377], .c 149, .c 3, .c 7, .c 83, .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv1723], .c 7, .c 3, .c 5, .c 11, .c 3, .c 13, .c 31, .c 3, .c 233, .c 41,
  .c 3, .c 541, .c 5, .c 3, .c 7, .c 53, .c 3, .c 5, .c 13, .c 3, .p pv23 [pv2,pv5,pv11,pv10589],
  .c 7, .c 3, .c 37, .p pv3 [pv2,pv3,pv163,pv397], .c 3,
]
private theorem h0142c05 : checkBlock 1164547 128 b0142c05 = true := by
  decide +kernel

private def b0142c06 : List Row := [
  .p pv2 [pv2,pv107,pv5443], .c 5, .c 3, .c 173, .p pv7 [pv2,pv3,pv5,pv41,pv947], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv8089], .c 3, .c 7, .c 11, .c 3, .c 43, .p pv2 [pv2,pv3,pv7,pv283], .c 3,
  .c 19, .c 5, .c 3, .c 13, .p pv11 [pv2,pv3,pv5,pv17,pv571], .c 3, .c 5, .c 563, .c 3, .c 41,
  .p pv2 [pv2,pv3,pv13,pv19,pv131], .c 3, .c 17, .p pv2 [pv2,pv3,pv23,pv367], .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv291217], .c 19, .c 3, .c 5, .c 7, .c 3, .c 23, .c 109, .c 3, .c 31, .c 11,
  .c 3, .c 457, .c 5, .c 3, .p pv2 [pv2,pv7,pv83207], .c 29, .c 3, .c 5, .c 421, .c 3, .c 11,
  .c 43, .c 3, .c 13, .c 7, .c 3, .c 229, .c 5, .c 3, .c 67, .c 211, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv48539], .c 3, .p pv2 [pv2,pv5,pv7,pv53,pv157], .c 13, .c 3, .c 7, .c 31, .c 3,
  .p pv3 [pv2,pv223,pv653], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv19,pv929],
  .c 3, .c 127, .c 23, .c 3, .c 11, .p pv2 [pv2,pv3,pv61,pv1061], .c 3, .c 131, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv38833], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv23,pv67], .c 3,
  .p pv3 [pv2,pv5,pv233], .c 7, .c 3, .c 73, .c 337, .c 3, .c 79, .c 5, .c 3, .c 23, .c 11, .c 3,
  .c 5, .c 17, .c 3, .c 7, .c 103, .c 3, .p pv2 [pv2,pv47,pv6197], .c 61, .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv137,pv1063], .p pv2 [pv2,pv3,pv5,pv863], .c 3, .c 5, .p pv5 [pv2,pv3,pv37,pv41],
]
private theorem h0142c06 : checkBlock 1164803 128 b0142c06 = true := by
  decide +kernel

private def b0142c07 : List Row := [
  .c 3, .c 17, .c 67, .c 3, .c 97, .p pv2 [pv2,pv3,pv32363], .c 3, .c 7, .c 5, .c 3,
  .p pv11 [pv2,pv17,pv34267], .p pv43 [pv2,pv3,pv5,pv7,pv19,pv73], .c 3, .c 5, .c 7, .c 3, .c 761,
  .c 37, .c 3, .c 41, .c 13, .c 3, .p pv5 [pv2,pv582551], .c 5, .c 3, .c 11, .c 23, .c 3, .c 5,
  .c 677, .c 3, .p pv19 [pv2,pv5,pv11,pv331], .c 107, .c 3, .p pv5 [pv2,pv582563], .c 7, .c 3,
  .c 29, .c 5, .c 3, .p pv2 [pv2,pv13,pv41,pv1093], .c 193, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv17,pv11423], .c 3, .c 13, .c 11, .c 3, .c 7, .c 167, .c 3, .c 17, .c 5, .c 3,
  .c 911, .c 7, .c 3, .c 5, .c 13, .c 3, .c 71, .p pv5 [pv2,pv3,pv194197], .c 3,
  .p pv2 [pv2,pv11,pv52963], .p pv2 [pv2,pv3,pv89,pv1091], .c 3, .p pv3 [pv2,pv7,pv20807], .c 5,
  .c 3, .c 7, .p pv29 [pv2,pv3,pv5,pv971], .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv27743], .c 3,
  .p pv2 [pv2,pv5,pv109,pv1069], .c 7, .c 3, .p pv3 [pv2,pv13,pv2801], .c 11, .c 3,
  .p pv5 [pv2,pv61,pv9551], .c 5, .c 3, .c 13, .c 17, .c 3, .c 5, .c 83, .c 3, .c 7, .c 827, .c 3,
  .c 647, .c 23, .c 3, .c 353, .c 5, .c 3, .c 31, .c 41, .c 3, .c 5, .c 151, .c 3, .c 47,
  .p pv11 [pv2,pv3,pv23,pv2111], .c 3, .c 89, .p pv11 [pv2,pv3,pv29,pv37,pv181], .c 3, .c 7, .c 5,
  .c 3, .c 19, .c 191, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv43,pv271],
  .p pv3 [pv2,pv3,pv41,pv1579], .c 3, .c 11, .c 59, .c 3, .c 613,
]
private theorem h0142c07 : checkBlock 1165059 128 b0142c07 = true := by
  decide +kernel

private def b0142c08 : List Row := [
  .c 5, .c 3, .c 109, .c 31, .c 3, .c 5, .c 19, .c 3, .c 67, .c 13, .c 3, .c 107, .c 7, .c 3,
  .c 41, .c 5, .c 3, .p pv2 [pv2,pv291337], .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv32371], .c 3,
  .p pv3 [pv2,pv5,pv7,pv2081], .p pv2 [pv2,pv3,pv11,pv17657], .c 3, .c 7, .c 113, .c 3, .c 11,
  .c 5, .c 3, .p pv2 [pv2,pv582689], .c 7, .c 3, .c 5, .c 23, .c 3, .c 487, .c 251, .c 3,
  .p pv2 [pv2,pv291349], .p pv11 [pv2,pv3,pv13,pv67,pv223], .c 3, .c 19, .c 5, .c 3, .c 7, .c 13,
  .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv58271], .c 7, .c 3, .c 59, .c 43, .c 3, .c 23, .c 5,
  .c 3, .c 11, .c 19, .c 3, .c 5, .p pv3 [pv2,pv3,pv64747], .c 3, .c 7,
  .p pv5 [pv2,pv3,pv17,pv29,pv197], .c 3, .c 631, .c 47, .c 3, .c 13, .c 5, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv5,pv53,pv733], .c 3, .c 5, .c 521, .c 3, .c 29, .c 11, .c 3, .c 79, .c 13,
  .c 3, .c 7, .c 5, .c 3, .c 719, .c 173, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv29,pv4019],
  .c 617, .c 3, .c 19, .c 953, .c 3, .c 53, .c 5, .c 3, .p pv3 [pv2,pv7,pv13,pv1601],
  .p pv3 [pv2,pv3,pv5,pv38851], .c 3, .c 5, .c 17, .c 3, .c 13, .c 199, .c 3, .c 787, .c 7, .c 3,
  .c 47, .c 5, .c 3, .c 1051, .c 977, .c 3, .c 5, .c 13, .c 3,
]
private theorem h0142c08 : checkBlock 1165315 128 b0142c08 = true := by
  decide +kernel

private def b0142c09 : List Row := [
  .c 11, .c 347, .c 3, .c 7, .p pv3 [pv2,pv3,pv194263], .c 3, .p pv5 [pv2,pv11,pv52981], .c 5,
  .c 3, .c 41, .c 7, .c 3, .c 5, .c 29, .c 3, .c 43, .c 239, .c 3, .c 71, .c 317, .c 3, .c 163,
  .c 5, .c 3, .c 7, .c 223, .c 3, .c 5, .c 149, .c 3, .c 19, .c 7, .c 3, .c 11, .c 17, .c 3,
  .p pv2 [pv2,pv582821], .c 5, .c 3, .c 61, .c 103, .c 3, .c 5, .c 547, .c 3, .c 7, .c 23, .c 3,
  .p pv2 [pv2,pv67,pv8699], .c 19, .c 3, .c 17, .c 5, .c 3, .c 307, .c 11, .c 3, .c 5, .c 43,
  .c 3, .p pv2 [pv2,pv5,pv17,pv6857], .c 31, .c 3, .c 13, .c 233, .c 3, .c 7, .c 5, .c 3, .c 23,
  .p pv3 [pv2,pv3,pv5,pv7,pv13,pv61], .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv151,pv193], .c 13,
  .c 3, .p pv5 [pv2,pv19,pv30677], .p pv7 [pv2,pv3,pv12143], .c 3, .c 67, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv83267], .c 17, .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv4663], .c 41, .c 3,
  .c 947, .c 7, .c 3, .c 701, .c 5, .c 3, .c 11, .c 29, .c 3, .c 5, .p pv5 [pv2,pv3,pv149,pv163],
  .c 3, .c 59, .c 19, .c 3, .c 7, .p pv23 [pv2,pv3,pv13,pv47,pv53], .c 3, .c 139, .c 5, .c 3,
  .p pv13 [pv2,pv582899], .c 7, .c 3, .c 5, .c 457, .c 3, .c 89, .c 11, .c 3, .c 31,
  .p pv2 [pv2,pv3,pv83,pv2341], .c 3, .p pv5 [pv2,pv7,pv83273], .c 5,
]
private theorem h0142c09 : checkBlock 1165571 128 b0142c09 = true := by
  decide +kernel

private def b0142c10 : List Row := [
  .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv38861], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv13879], .c 3, .c 53,
  .c 7, .c 3, .c 23, .p pv7 [pv2,pv3,pv31,pv1567], .c 3, .c 13, .c 5, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv5,pv17,pv127], .c 3, .c 5, .c 67, .c 3, .c 7, .p pv5 [pv2,pv3,pv107,pv227],
  .c 3, .c 17, .c 11, .c 3, .c 73, .c 5, .c 3, .p pv3 [pv2,pv18217], .c 71, .c 3, .c 5, .c 19,
  .c 3, .c 11, .p pv5 [pv2,pv3,pv43,pv4519], .c 3, .c 37, .p pv2 [pv2,pv3,pv97159], .c 3, .c 7,
  .c 5, .c 3, .p pv23 [pv2,pv13,pv44843], .p pv17 [pv2,pv3,pv5,pv7,pv347], .c 3, .c 5, .c 7, .c 3,
  .c 13, .p pv5 [pv2,pv3,pv139,pv233], .c 3, .p pv3 [pv2,pv72871], .c 23, .c 3,
  .p pv5 [pv2,pv582971], .c 5, .c 3, .p pv2 [pv2,pv7,pv41641], .p pv13 [pv2,pv3,pv5,pv2591], .c 3,
  .c 5, .c 13, .c 3, .c 79, .c 1013, .c 3, .c 11, .c 7, .c 3, .c 19, .c 5, .c 3, .c 17, .c 37,
  .c 3, .c 5, .c 127, .c 3, .p pv7 [pv2,pv5,pv7,pv16657], .p pv5 [pv2,pv3,pv19,pv2557], .c 3,
  .c 7, .c 41, .c 3, .c 29, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 59, .c 3,
  .p pv2 [pv2,pv5,pv173,pv337], .c 47, .c 3, .p pv2 [pv2,pv583013], .c 73, .c 3, .c 11, .c 5,
  .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv41,pv79], .c 3, .c 5, .c 17, .c 3, .c 853, .c 7, .c 3,
  .p pv3 [pv2,pv145757], .c 409, .c 3, .c 103, .c 5, .c 3, .c 433, .c 139, .c 3, .c 5, .c 11,
  .c 3, .c 7,
]
private theorem h0142c10 : checkBlock 1165827 128 b0142c10 = true := by
  decide +kernel

private def b0142c11 : List Row := [
  .p pv2 [pv2,pv3,pv109,pv1783], .c 3, .c 13, .p pv19 [pv2,pv3,pv7,pv11,pv631], .c 3,
  .p pv2 [pv2,pv37,pv7879], .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv13,pv23], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv19,pv53,pv193], .c 3, .c 1063, .c 13, .c 3, .c 43, .c 29, .c 3, .c 7, .c 5,
  .c 3, .c 37, .p pv3 [pv2,pv3,pv5,pv7,pv617], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv199,pv293], .c 11, .c 3, .p pv2 [pv2,pv23,pv101,pv251], .c 17, .c 3,
  .p pv3 [pv2,pv13,pv11213], .c 5, .c 3, .c 53, .c 167, .c 3, .c 5, .c 89, .c 3, .c 971, .c 151,
  .c 3, .c 29, .c 7, .c 3, .c 17, .c 5, .c 3, .c 31, .c 13, .c 3, .c 5, .c 211, .c 3, .c 19,
  .c 37, .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv53,pv5501], .c 5, .c 3, .p pv2 [pv2,pv719,pv811],
  .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv194371], .c 3, .c 11, .c 83, .c 3, .p pv2 [pv2,pv291559],
  .c 19, .c 3, .c 13, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 1033, .c 3, .c 23, .c 7, .c 3,
  .c 347, .c 13, .c 3, .c 113, .c 5, .c 3, .c 1069, .c 137, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv41,pv431], .c 3, .c 7, .c 29, .c 3, .c 11, .c 193, .c 3, .c 751, .c 5,
  .c 3, .c 673, .p pv3 [pv2,pv3,pv5,pv12959], .c 3, .c 5, .c 71, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv29,pv6703], .c 3, .c 41, .p pv7 [pv2,pv3,pv97,pv167], .c 3, .c 7, .c 5, .c 3,
]
private theorem h0142c11 : checkBlock 1166083 128 b0142c11 = true := by
  decide +kernel

private def b0142c12 : List Row := [
  .c 199, .c 11, .c 3, .c 5, .c 7, .c 3, .c 29, .c 17, .c 3, .c 337, .p pv3 [pv2,pv3,pv349,pv557],
  .c 3, .c 11, .c 5, .c 3, .c 587, .c 53, .c 3, .c 5, .c 857, .c 3, .c 61,
  .p pv3 [pv2,pv3,pv7,pv9257], .c 3, .c 17, .c 7, .c 3, .p pv3 [pv2,pv145799], .c 5, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv5], .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv7,pv19,pv877],
  .p pv5 [pv2,pv3,pv13,pv7477], .c 3, .c 7, .c 443, .c 3, .c 439, .c 5, .c 3, .c 11, .c 7, .c 3,
  .c 5, .c 31, .c 3, .p pv3 [pv2,pv5,pv11,pv241], .c 883, .c 3, .c 277, .c 101, .c 3,
  .p pv2 [pv2,pv7,pv41659], .c 5, .c 3, .c 7, .c 43, .c 3, .c 5, .c 19, .c 3, .c 677, .c 7, .c 3,
  .c 13, .p pv3 [pv2,pv3,pv194413], .c 3, .p pv2 [pv2,pv83,pv7027], .c 5, .c 3, .c 17, .c 23,
  .c 3, .c 5, .p pv11 [pv2,pv3,pv29,pv419], .c 3, .c 7, .c 13, .c 3,
  .p pv2 [pv2,pv11,pv17,pv3119], .c 401, .c 3, .c 223, .c 5, .c 3, .c 521, .c 149, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv229,pv283], .c 3, .p pv2 [pv2,pv5,pv31,pv53,pv71],
  .p pv5 [pv2,pv3,pv41,pv2371], .c 3, .c 23, .c 11, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv59,pv4943], .c 313, .c 3, .c 5, .c 7, .c 3, .c 11, .p pv3 [pv2,pv3,pv19,pv379],
  .c 3, .p pv5 [pv2,pv467,pv1249], .p pv7 [pv2,pv3,pv13,pv3739], .c 3, .c 37, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv103,pv809], .c 13, .c 3, .c 5, .c 47, .c 3, .c 17, .c 79,
]
private theorem h0142c12 : checkBlock 1166339 128 b0142c12 = true := by
  decide +kernel

private def b0142c13 : List Row := [
  .c 3, .p pv2 [pv2,pv291649], .c 7, .c 3, .p pv2 [pv2,pv583301], .c 5, .c 3,
  .p pv3 [pv2,pv17,pv4289], .c 389, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv491], .c 3, .c 107, .c 31,
  .c 3, .c 7, .c 23, .c 3, .c 13, .c 5, .c 3, .p pv11 [pv2,pv11,pv19,pv2791], .c 7, .c 3, .c 5,
  .c 37, .c 3, .c 101, .c 269, .c 3, .c 19, .c 13, .c 3, .p pv7 [pv2,pv7,pv167,pv499], .c 5, .c 3,
  .c 7, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv17,pv19,pv43], .c 3, .c 47, .c 7, .c 3,
  .p pv5 [pv2,pv61,pv73,pv131], .c 53, .c 3, .c 11, .c 5, .c 3, .c 29, .c 89, .c 3, .c 5, .c 349,
  .c 3, .c 7, .p pv5 [pv2,pv3,pv173,pv281], .c 3, .c 431, .c 43, .c 3, .p pv2 [pv2,pv179,pv3259],
  .c 5, .c 3, .p pv3 [pv2,pv29,pv47,pv107], .c 83, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv58337], .c 71, .c 3, .c 31, .c 127, .c 3, .c 7, .c 5, .c 3, .c 11, .c 17,
  .c 3, .c 5, .c 7, .c 3, .c 19, .p pv2 [pv2,pv3,pv97231], .c 3, .c 151,
  .p pv3 [pv2,pv3,pv17,pv31,pv41], .c 3, .c 397, .c 5, .c 3, .c 13, .c 461, .c 3, .c 5, .c 1039,
  .c 3, .p pv7 [pv2,pv5,pv2917], .c 11, .c 3, .p pv5 [pv2,pv583403], .c 7, .c 3, .c 23, .c 5,
  .c 3, .c 41, .c 983, .c 3, .c 5, .p pv2 [pv2,pv3,pv194471], .c 3, .c 197,
  .p pv5 [pv2,pv3,pv37,pv73], .c 3, .c 7, .p pv7 [pv2,pv3,pv113,pv1721], .c 3, .c 59, .c 5, .c 3,
  .p pv3 [pv2,pv43,pv53],
]
private theorem h0142c13 : checkBlock 1166595 128 b0142c13 = true := by
  decide +kernel

private def b0142c14 : List Row := [
  .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv48619], .c 3, .p pv2 [pv2,pv5,pv41,pv1423], .c 17, .c 3,
  .c 13, .c 11, .c 3, .c 29, .c 5, .c 3, .c 7, .c 739, .c 3, .c 5, .c 103, .c 3, .c 11, .c 7,
  .c 3, .c 17, .c 251, .c 3, .p pv5 [pv2,pv11,pv29,pv31,pv59], .c 5, .c 3, .c 79, .c 653, .c 3,
  .c 5, .c 163, .c 3, .c 7, .c 19, .c 3, .p pv5 [pv2,pv271,pv2153],
  .p pv31 [pv2,pv3,pv7,pv23,pv151], .c 3, .c 31, .c 5, .c 3, .c 67, .c 379, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv17681], .c 3, .c 23, .p pv5 [pv2,pv3,pv48623], .c 3, .c 11, .c 223, .c 3,
  .c 7, .c 5, .c 3, .p pv3 [pv2,pv11,pv89,pv149], .c 13, .c 3, .c 5, .c 7, .c 3, .c 157, .c 41,
  .c 3, .p pv2 [pv2,pv583493], .c 29, .c 3, .c 281, .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .c 53,
  .c 3, .p pv2 [pv2,pv5,pv13,pv47,pv191], .p pv2 [pv2,pv3,pv7,pv11,pv421], .c 3, .c 37, .c 7,
  .c 3, .c 11, .c 5, .c 3, .c 811, .c 337, .c 3, .c 5, .c 19, .c 3, .c 211, .c 23, .c 3, .c 7,
  .c 13, .c 3, .p pv2 [pv2,pv61,pv4783], .c 5, .c 3, .p pv2 [pv2,pv173,pv3373], .c 7, .c 3, .c 5,
  .c 11, .c 3, .c 193, .c 67, .c 3, .p pv2 [pv2,pv29,pv10061], .c 59, .c 3,
  .p pv2 [pv2,pv7,pv11909], .c 5, .c 3, .c 7, .c 37, .c 3, .c 5, .c 233, .c 3, .c 13, .c 7, .c 3,
]
private theorem h0142c14 : checkBlock 1166851 128 b0142c14 = true := by
  decide +kernel

private def b0142c15 : List Row := [
  .c 491, .c 359, .c 3, .c 19, .c 5, .c 3, .c 31, .c 787, .c 3, .c 5, .c 13, .c 3, .c 7, .c 11,
  .c 3, .c 509, .p pv53 [pv2,pv3,pv7,pv59,pv157], .c 3, .p pv5 [pv2,pv601,pv971], .c 5, .c 3,
  .c 43, .c 19, .c 3, .c 5, .p pv2 [pv2,pv3,pv101,pv107], .c 3, .c 499, .c 29, .c 3,
  .p pv5 [pv2,pv7,pv11,pv13,pv53], .c 17, .c 3, .c 7, .c 5, .c 3, .c 13, .c 23, .c 3, .c 5, .c 7,
  .c 3, .c 269, .p pv5 [pv2,pv3,pv13,pv29,pv43], .c 3, .c 59, .c 11, .c 3, .c 17, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv19,pv1097], .p pv3 [pv2,pv3,pv5,pv11,pv131], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv24317], .c 3, .c 11, .c 463, .c 3, .c 19, .c 7, .c 3, .p pv3 [pv2,pv11,pv829],
  .c 5, .c 3, .c 37, .p pv7 [pv2,pv3,pv5,pv71,pv137], .c 3, .c 5, .c 683, .c 3,
  .p pv2 [pv2,pv5,pv7,pv23,pv29], .c 743, .c 3, .c 7, .c 179, .c 3, .c 107, .c 5, .c 3, .c 181,
  .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv37,pv239], .c 3, .c 109, .c 13, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv17,pv2861], .c 3, .p pv2 [pv2,pv7,pv47,pv887], .c 5, .c 3, .c 7, .c 439,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv27793], .c 3, .c 41, .c 7, .c 3, .p pv2 [pv2,pv291829], .c 23,
  .c 3, .c 479, .c 5, .c 3, .p pv3 [pv2,pv36479], .c 11, .c 3, .c 5, .c 29, .c 3, .c 7, .c 73,
  .c 3, .p pv2 [pv2,pv583673], .p pv2 [pv2,pv3,pv7,pv13,pv1069], .c 3, .c 11, .c 5, .c 3,
  .p pv7 [pv2,pv101,pv5779], .c 13,
]
private theorem h0142c15 : checkBlock 1167107 128 b0142c15 = true := by
  decide +kernel

private def b0142c16 : List Row := [
  .c 3, .c 5, .c 31, .c 3, .c 353, .c 17, .c 3, .c 137, .c 19, .c 3, .c 7, .c 5, .c 3, .c 389,
  .p pv79 [pv2,pv3,pv5,pv7,pv17,pv109], .c 3, .c 5, .c 7, .c 3, .c 251, .c 113, .c 3, .c 17,
  .p pv7 [pv2,pv3,pv11,pv67], .c 3, .c 13, .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv19457], .c 3,
  .c 5, .c 367, .c 3, .c 53, .c 47, .c 3, .c 331, .c 7, .c 3, .p pv2 [pv2,pv229,pv2549], .c 5,
  .c 3, .p pv3 [pv2,pv145931], .c 599, .c 3, .c 5, .c 23, .c 3, .c 37, .c 11, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv271,pv359], .c 3, .p pv3 [pv2,pv131,pv557], .c 5, .c 3, .c 61, .c 7, .c 3,
  .c 5, .c 997, .c 3, .c 13, .c 19, .c 3, .c 167, .c 109, .c 3, .c 23, .c 5, .c 3, .c 7, .c 29,
  .c 3, .c 5, .c 13, .c 3, .c 307, .c 7, .c 3, .c 47, .c 11, .c 3, .c 199, .c 5, .c 3,
  .p pv2 [pv2,pv583769], .c 79, .c 3, .c 5, .p pv2 [pv2,pv3,pv194591], .c 3, .c 7, .c 31, .c 3,
  .c 41, .p pv3 [pv2,pv3,pv7,pv27799], .c 3, .c 233, .c 5, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv5,pv12973], .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv58379], .c 191, .c 3,
  .p pv2 [pv2,pv7,pv83399], .c 97, .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv29,pv41,pv491], .c 61,
  .c 3, .c 5, .c 7, .c 3, .c 17, .p pv2 [pv2,pv3,pv97301], .c 3, .c 11,
]
private theorem h0142c16 : checkBlock 1167363 128 b0142c16 = true := by
  decide +kernel

private def b0142c17 : List Row := [
  .c 197, .c 3, .p pv5 [pv2,pv43,pv13577], .c 5, .c 3, .c 113, .c 181, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv97303], .c 3, .c 23, .c 53, .c 3, .c 13, .c 7, .c 3,
  .p pv2 [pv2,pv251,pv1163], .c 5, .c 3, .p pv2 [pv2,pv283,pv2063], .c 11, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv71,pv2741], .c 3, .c 229, .c 13, .c 3, .c 7, .c 17, .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv227,pv643], .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv17,pv53], .c 3,
  .p pv2 [pv2,pv5,pv11677], .p pv5 [pv2,pv3,pv19,pv10243], .c 3, .p pv2 [pv2,pv583853],
  .p pv2 [pv2,pv3,pv31,pv43,pv73], .c 3, .c 17, .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv17,pv6869], .c 7, .c 3, .c 71, .c 31, .c 3, .c 29, .c 5, .c 3, .c 11, .c 13,
  .c 3, .c 5, .c 37, .c 3, .c 7, .p pv2 [pv2,pv3,pv41,pv47,pv101], .c 3, .c 383, .c 89, .c 3,
  .p pv2 [pv2,pv29,pv10067], .c 5, .c 3, .c 23, .c 17, .c 3, .c 5, .c 59, .c 3,
  .p pv7 [pv2,pv5,pv13,pv691], .c 11, .c 3, .c 19, .p pv3 [pv2,pv3,pv17,pv107], .c 3, .c 7, .c 5,
  .c 3, .c 47, .p pv3 [pv2,pv3,pv5,pv7,pv67,pv83], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv58391], .p pv3 [pv2,pv3,pv64879], .c 3, .c 359, .c 13, .c 3,
  .p pv3 [pv2,pv17,pv31,pv277], .c 5, .c 3, .p pv7 [pv2,pv7,pv83417], .p pv7 [pv2,pv3,pv5,pv811],
  .c 3, .c 5, .p pv3 [pv2,pv3,pv59,pv3299], .c 3, .c 223, .p pv2 [pv2,pv3,pv7,pv13903], .c 3,
  .c 79, .c 7, .c 3, .c 31, .c 5, .c 3, .p pv2 [pv2,pv13,pv37,pv607], .c 23, .c 3,
]
private theorem h0142c17 : checkBlock 1167619 128 b0142c17 = true := by
  decide +kernel

private def b0142c18 : List Row := [
  .c 5, .c 67, .c 3, .c 11, .c 17, .c 3, .c 7, .p pv13 [pv2,pv3,pv29,pv839], .c 3, .c 83, .c 5,
  .c 3, .p pv2 [pv2,pv293,pv1993], .c 7, .c 3, .c 5, .c 13, .c 3, .c 19, .p pv5 [pv2,pv3,pv5407],
  .c 3, .c 17, .p pv3 [pv2,pv3,pv194653], .c 3, .c 43, .c 5, .c 3, .c 7, .c 199, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv11,pv79], .c 3, .c 283, .c 7, .c 3, .c 11, .c 19, .c 3,
  .p pv3 [pv2,pv72997], .c 5, .c 3, .c 13, .c 53, .c 3, .c 5, .c 41, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv13,pv7487], .c 3, .c 97, .c 37, .c 3, .c 263, .c 5, .c 3, .c 1013, .c 11,
  .c 3, .c 5, .c 47, .c 3, .p pv3 [pv2,pv5,pv73], .c 773, .c 3, .p pv5 [pv2,pv7,pv19,pv4391],
  .c 23, .c 3, .c 7, .c 5, .c 3, .c 17, .c 71, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv116803],
  .c 29, .c 3, .c 13, .p pv13 [pv2,pv3,pv64891], .c 3, .p pv2 [pv2,pv337,pv1733], .c 5, .c 3,
  .c 31, .c 757, .c 3, .c 5, .c 11, .c 3, .c 829, .c 13, .c 3, .c 53, .c 7, .c 3, .c 73, .c 5,
  .c 3, .c 11, .c 113, .c 3, .c 5, .c 17, .c 3, .c 29, .p pv2 [pv2,pv3,pv71,pv457], .c 3, .c 7,
  .c 331, .c 3, .c 349, .c 5, .c 3, .c 277, .c 7, .c 3, .c 5, .c 281, .c 3, .c 17, .c 11, .c 3,
  .c 37, .c 229,
]
private theorem h0142c18 : checkBlock 1167875 128 b0142c18 = true := by
  decide +kernel

private def b0142c19 : List Row := [
  .c 3, .p pv2 [pv2,pv7,pv41719], .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 23, .c 3,
  .p pv23 [pv2,pv5,pv61,pv383], .c 7, .c 3, .c 569, .c 499, .c 3, .c 71, .c 5, .c 3,
  .p pv3 [pv2,pv146021], .c 97, .c 3, .c 5, .c 19, .c 3, .c 7, .p pv7 [pv2,pv3,pv7211], .c 3,
  .p pv2 [pv2,pv359,pv1627], .c 11, .c 3, .c 13, .c 5, .c 3, .c 137, .c 37, .c 3, .c 5, .c 29,
  .c 3, .c 11, .c 41, .c 3, .c 653, .c 13, .c 3, .c 7, .c 5, .c 3, .c 193,
  .p pv3 [pv2,pv3,pv5,pv7,pv5563], .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv17,pv859],
  .p pv2 [pv2,pv3,pv194707], .c 3, .p pv5 [pv2,pv263,pv2221], .p pv7 [pv2,pv3,pv48677], .c 3,
  .c 19, .c 5, .c 3, .c 59, .p pv2 [pv2,pv3,pv5,pv19471], .c 3, .c 5, .c 43, .c 3, .c 13, .c 127,
  .c 3, .c 11, .c 7, .c 3, .c 821, .c 5, .c 3, .c 727, .c 17, .c 3, .c 5, .c 13, .c 3,
  .p pv2 [pv2,pv5,pv7,pv1669], .c 89, .c 3, .c 7, .c 149, .c 3, .c 487, .c 5, .c 3,
  .p pv11 [pv2,pv59,pv9901], .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv47,pv1381], .c 3, .c 23, .c 61,
  .c 3, .p pv5 [pv2,pv13,pv41,pv137], .p pv3 [pv2,pv3,pv194723], .c 3, .c 11, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv7789], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv1987], .c 3,
  .p pv3 [pv2,pv5,pv29209], .c 7, .c 3, .c 19, .c 227, .c 3, .c 47, .c 5, .c 3, .c 337, .c 29,
  .c 3, .c 5,
]
private theorem h0142c19 : checkBlock 1168131 128 b0142c19 = true := by
  decide +kernel

private def b0142c20 : List Row := [
  .c 11, .c 3, .c 7, .c 17, .c 3, .p pv2 [pv2,pv43,pv6793], .p pv11 [pv2,pv3,pv7,pv11,pv281],
  .c 3, .p pv2 [pv2,pv733,pv797], .c 5, .c 3, .c 11, .p pv41 [pv2,pv3,pv5,pv17,pv29,pv79], .c 3,
  .c 5, .c 1069, .c 3, .c 31, .c 23, .c 3, .c 13, .c 313, .c 3, .c 7, .c 5, .c 3, .c 29, .c 431,
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv23369], .c 11, .c 3, .c 379, .c 41, .c 3,
  .p pv5 [pv2,pv19,pv97,pv317], .c 5, .c 3, .c 23, .c 239, .c 3, .c 5, .p pv2 [pv2,pv3,pv97373],
  .c 3, .c 19, .c 31, .c 3, .p pv5 [pv2,pv11,pv53113], .c 7, .c 3, .p pv2 [pv2,pv13,pv23,pv977],
  .c 5, .c 3, .c 167, .p pv17 [pv2,pv3,pv5,pv19,pv41], .c 3, .c 5, .c 283, .c 3, .c 73, .c 409,
  .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv584261], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv181,pv269], .c 3, .c 11, .c 641, .c 3, .c 67, .c 457, .c 3,
  .p pv3 [pv2,pv7,pv11,pv271], .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 701, .c 3, .c 37, .c 7,
  .c 3, .c 61, .c 257, .c 3, .c 13, .c 5, .c 3, .c 71, .c 419, .c 3, .c 5, .c 17, .c 3, .c 7,
  .c 521, .c 3, .c 11, .c 13, .c 3, .c 29, .c 5, .c 3, .p pv2 [pv2,pv11,pv439],
  .p pv2 [pv2,pv3,pv5,pv19477], .c 3, .c 5, .p pv2 [pv2,pv3,pv194771], .c 3, .c 17, .c 19, .c 3,
  .p pv5 [pv2,pv7,pv41737], .p pv3 [pv2,pv3,pv31,pv61,pv103], .c 3,
]
private theorem h0142c20 : checkBlock 1168387 128 b0142c20 = true := by
  decide +kernel

private def b0142c21 : List Row := [
  .c 7, .c 5, .c 3, .c 599, .c 11, .c 3, .c 5, .c 7, .c 3, .c 13, .c 277, .c 3, .c 433, .c 31,
  .c 3, .c 11, .c 5, .c 3, .c 281, .c 67, .c 3, .c 5, .c 13, .c 3, .c 179,
  .p pv17 [pv2,pv3,pv7,pv13913], .c 3, .c 43, .c 7, .c 3, .c 53, .c 5, .c 3, .c 19,
  .p pv11 [pv2,pv3,pv5,pv163,pv239], .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv7,pv2087], .c 83,
  .c 3, .c 7, .c 29, .c 3, .c 17, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 19, .c 3,
  .p pv19 [pv2,pv5,pv11,pv17], .c 97, .c 3, .p pv2 [pv2,pv37,pv53,pv149], .c 113, .c 3,
  .p pv5 [pv2,pv7,pv31,pv2693], .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv38959], .c 3, .c 5,
  .c 293, .c 3, .c 127, .c 7, .c 3, .c 29, .p pv13 [pv2,pv3,pv173,pv563], .c 3, .c 31, .c 5, .c 3,
  .p pv7 [pv2,pv584399], .c 17, .c 3, .c 5, .c 109, .c 3, .c 7, .c 911, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv7,pv17,pv1637], .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv41,pv7127],
  .p pv3 [pv2,pv3,pv5,pv13,pv37], .c 3, .c 5, .c 23, .c 3, .p pv3 [pv2,pv5,pv29221], .c 13, .c 3,
  .p pv5 [pv2,pv7,pv11927], .c 11, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv584429], .c 19, .c 3,
  .c 5, .c 7, .c 3, .c 11, .c 71, .c 3, .p pv2 [pv2,pv73,pv4003], .p pv3 [pv2,pv3,pv194813], .c 3,
  .c 23, .c 5, .c 3, .c 83, .c 151, .c 3, .c 5, .p pv13 [pv2,pv3,pv761],
]
private theorem h0142c21 : checkBlock 1168643 128 b0142c21 = true := by
  decide +kernel

private def b0142c22 : List Row := [
  .c 3, .c 467, .c 17, .c 3, .c 251, .c 7, .c 3, .c 131, .c 5, .c 3, .p pv11 [pv2,pv19,pv1619],
  .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv89,pv199], .c 3, .p pv23 [pv2,pv5,pv7,pv16699],
  .p pv2 [pv2,pv3,pv29,pv3359], .c 3, .c 7, .c 547, .c 3, .c 61, .c 5, .c 3, .c 67, .c 7, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv19,pv1709], .c 3, .c 29, .c 79, .c 3, .c 59,
  .p pv23 [pv2,pv3,pv53,pv919], .c 3, .c 13, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv13,pv2141], .c 3, .c 613, .c 7, .c 3, .p pv2 [pv2,pv292249], .c 13, .c 3,
  .c 11, .c 5, .c 3, .p pv3 [pv2,pv73063], .p pv2 [pv2,pv3,pv5,pv31,pv419], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv67,pv727], .c 3, .c 7, .p pv7 [pv2,pv3,pv17,pv73,pv157], .c 3,
  .p pv2 [pv2,pv59,pv9907], .p pv2 [pv2,pv3,pv7,pv4639], .c 3, .c 41, .c 5, .c 3, .c 17, .c 31,
  .c 3, .c 5, .c 11, .c 3, .c 13, .c 337, .c 3, .c 439, .p pv3 [pv2,pv3,pv11,pv17713], .c 3, .c 7,
  .c 5, .c 3, .c 11, .c 491, .c 3, .c 5, .c 7, .c 3, .p pv23 [pv2,pv5,pv11,pv2657], .c 67, .c 3,
  .c 881, .c 19, .c 3, .c 257, .c 5, .c 3, .c 859, .c 541, .c 3, .c 5, .c 17, .c 3, .c 191, .c 11,
  .c 3, .c 421, .c 7, .c 3, .c 907, .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv38971], .c 3, .c 5,
  .p pv19 [pv2,pv3,pv23,pv353], .c 3, .c 17, .c 557, .c 3, .c 7, .p pv2 [pv2,pv3,pv97429], .c 3,
  .c 103,
]
private theorem h0142c22 : checkBlock 1168899 128 b0142c22 = true := by
  decide +kernel

private def b0142c23 : List Row := [
  .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 167, .c 3, .p pv2 [pv2,pv5,pv43,pv2719], .c 509, .c 3,
  .p pv3 [pv2,pv101,pv1447], .c 11, .c 3, .p pv5 [pv2,pv7,pv23,pv3631], .c 5, .c 3, .c 7,
  .p pv41 [pv2,pv3,pv5,pv11,pv1181], .c 3, .c 5, .c 41, .c 3, .c 11, .c 7, .c 3, .c 13, .c 17,
  .c 3, .c 43, .c 5, .c 3, .c 47, .c 83, .c 3, .c 5, .c 31, .c 3, .c 7, .c 13, .c 3, .c 37,
  .c 479, .c 3, .c 17, .c 5, .c 3, .p pv3 [pv2,pv61,pv599], .c 23, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv43,pv103], .c 3, .p pv2 [pv2,pv5,pv17,pv19,pv181], .c 359, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv139,pv701], .c 3, .c 7, .c 5, .c 3, .c 19, .p pv23 [pv2,pv3,pv5,pv7,pv29],
  .c 3, .c 5, .c 7, .c 3, .c 619, .p pv2 [pv2,pv3,pv97441], .c 3, .c 23, .c 43, .c 3, .c 431,
  .c 5, .c 3, .c 29, .c 11, .c 3, .c 5, .c 19, .c 3, .c 59, .p pv7 [pv2,pv3,pv7,pv11,pv2531],
  .c 3, .p pv5 [pv2,pv584663], .c 7, .c 3, .c 11, .c 5, .c 3, .c 53, .p pv2 [pv2,pv3,pv5,pv19489],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv194891], .c 3, .c 31, .p pv29 [pv2,pv3,pv109,pv149], .c 3, .c 7,
  .c 103, .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv313,pv467], .c 7, .c 3, .c 5, .c 11, .c 3,
  .p pv3 [pv2,pv5,pv59,pv991], .p pv3 [pv2,pv3,pv31,pv6287], .c 3, .c 73, .c 13, .c 3, .c 19,
  .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv1949], .c 3, .c 5, .c 47, .c 3,
]
private theorem h0142c23 : checkBlock 1169155 128 b0142c23 = true := by
  decide +kernel

private def b0142c24 : List Row := [
  .p pv2 [pv2,pv5,pv11,pv10631], .c 7, .c 3, .p pv3 [pv2,pv127,pv1151],
  .p pv2 [pv2,pv3,pv67,pv2909], .c 3, .c 331, .c 5, .c 3, .c 419, .c 19, .c 3, .c 5, .c 79, .c 3,
  .c 7, .c 11, .c 3, .c 17, .p pv11 [pv2,pv3,pv7,pv6961], .c 3, .p pv2 [pv2,pv292363], .c 5, .c 3,
  .c 37, .c 109, .c 3, .c 5, .c 13, .c 3, .c 43, .p pv11 [pv2,pv3,pv6091], .c 3,
  .p pv5 [pv2,pv7,pv11,pv3797], .c 101, .c 3, .c 7, .c 5, .c 3, .c 353,
  .p pv2 [pv2,pv3,pv5,pv7,pv5569], .c 3, .c 5, .c 7, .c 3, .c 47, .c 229, .c 3, .c 19, .c 11,
  .c 3, .p pv3 [pv2,pv29,pv71], .c 5, .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv11,pv443], .c 3, .c 5,
  .c 23, .c 3, .c 11, .c 37, .c 3, .c 31, .c 7, .c 3, .c 127, .c 5, .c 3, .c 17, .c 53, .c 3,
  .c 5, .c 43, .c 3, .c 263, .p pv2 [pv2,pv3,pv397,pv491], .c 3, .c 7, .c 137, .c 3, .c 23, .c 5,
  .c 3, .c 577, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv179], .c 3, .p pv11 [pv2,pv5,pv116959],
  .p pv5 [pv2,pv3,pv48733], .c 3, .c 11, .c 29, .c 3, .p pv2 [pv2,pv7,pv19,pv4397], .c 5, .c 3,
  .c 7, .c 929, .c 3, .c 5, .c 17, .c 3, .c 19, .c 7, .c 3, .p pv2 [pv2,pv97,pv6029], .c 367,
  .c 3, .p pv3 [pv2,pv36551], .c 5, .c 3, .c 283, .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv151,pv1291], .c 3, .c 7, .c 173, .c 3, .c 29, .c 19, .c 3, .c 11, .c 5,
]
private theorem h0142c24 : checkBlock 1169411 128 b0142c24 = true := by
  decide +kernel

private def b0142c25 : List Row := [
  .c 3, .p pv2 [pv2,pv17,pv103,pv167], .c 311, .c 3, .c 5, .p pv2 [pv2,pv3,pv32491], .c 3, .c 37,
  .p pv5 [pv2,pv3,pv383,pv509], .c 3, .p pv5 [pv2,pv7,pv29,pv43,pv67], .c 41, .c 3, .c 7, .c 5,
  .c 3, .c 131, .c 13, .c 3, .c 5, .c 7, .c 3, .c 23, .p pv11 [pv2,pv3,pv8123], .c 3, .c 401,
  .c 17, .c 3, .c 31, .c 5, .c 3, .c 11, .c 227, .c 3, .c 5, .c 347, .c 3,
  .p pv7 [pv2,pv5,pv11,pv13,pv409], .c 727, .c 3, .p pv2 [pv2,pv584873], .c 7, .c 3, .c 13, .c 5,
  .c 3, .p pv13 [pv2,pv584879], .p pv11 [pv2,pv3,pv5,pv2437], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv13,pv4999], .c 3, .c 41, .c 11, .c 3, .c 7, .c 13, .c 3, .c 47, .c 5, .c 3,
  .p pv2 [pv2,pv109,pv2683], .c 7, .c 3, .c 5, .c 61, .c 3, .p pv3 [pv2,pv5,pv5849], .c 23, .c 3,
  .c 157, .p pv17 [pv2,pv3,pv24371], .c 3, .c 719, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv23,pv173], .c 3, .c 13, .c 7, .c 3, .c 739, .c 11, .c 3, .c 137, .c 5,
  .c 3, .c 19, .c 163, .c 3, .c 5, .c 13, .c 3, .c 7, .c 691, .c 3, .c 71, .c 53, .c 3,
  .p pv5 [pv2,pv11,pv17,pv23], .c 5, .c 3, .p pv7 [pv2,pv31,pv18869], .c 269, .c 3, .c 5, .c 19,
  .c 3, .c 587, .c 233, .c 3, .c 109, .p pv2 [pv2,pv3,pv73,pv2671], .c 3, .c 7, .c 5, .c 3, .c 13,
  .c 59, .c 3, .c 5, .c 7, .c 3, .c 199,
]
private theorem h0142c25 : checkBlock 1169667 128 b0142c25 = true := by
  decide +kernel

private def b0142c26 : List Row := [
  .c 17, .c 3, .c 11, .p pv7 [pv2,pv3,pv16249], .c 3, .p pv2 [pv2,pv292483], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv11,pv71,pv107], .c 23, .c 3, .c 5, .c 29, .c 3, .c 523, .c 887, .c 3, .c 17,
  .c 7, .c 3, .c 19, .c 5, .c 3, .c 701, .c 11, .c 3, .c 5, .c 37, .c 3, .c 359, .c 197, .c 3,
  .c 7, .c 593, .c 3, .c 11, .c 5, .c 3, .c 173, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv109,pv1789],
  .c 3, .p pv2 [pv2,pv5,pv23,pv5087], .c 13, .c 3, .c 41, .p pv3 [pv2,pv3,pv47,pv461], .c 3,
  .p pv5 [pv2,pv7,pv11939], .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv43,pv907], .c 3, .c 5, .c 11,
  .c 3, .c 61, .c 7, .c 3, .c 317, .p pv17 [pv2,pv3,pv11,pv277], .c 3, .c 491, .c 5, .c 3, .c 11,
  .p pv23 [pv2,pv3,pv5,pv19501], .c 3, .c 5, .p pv3 [pv2,pv3,pv191,pv1021], .c 3, .c 7, .c 43,
  .c 3, .c 19, .c 23, .c 3, .c 89, .c 5, .c 3, .p pv3 [pv2,pv37,pv59,pv67], .c 13, .c 3, .c 5,
  .c 149, .c 3, .c 373, .c 11, .c 3, .p pv2 [pv2,pv7,pv83579], .p pv11 [pv2,pv3,pv32503], .c 3,
  .c 7, .c 5, .c 3, .p pv11 [pv2,pv401,pv1459], .c 29, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv13,pv9001], .p pv5 [pv2,pv3,pv97511], .c 3, .p pv3 [pv2,pv11,pv13297],
  .p pv2 [pv2,pv3,pv195023], .c 3, .c 13, .c 5, .c 3, .c 409, .c 71, .c 3, .c 5, .c 31, .c 3,
  .c 17, .c 61, .c 3, .p pv5 [pv2,pv521,pv1123], .c 7, .c 3, .p pv2 [pv2,pv19,pv89,pv173], .c 5,
  .c 3,
]
private theorem h0142c26 : checkBlock 1169923 128 b0142c26 = true := by
  decide +kernel

private def b0142c27 : List Row := [
  .c 29, .c 41, .c 3, .c 5, .c 53, .c 3, .c 11, .p pv11 [pv2,pv3,pv24379], .c 3, .c 7, .c 37,
  .c 3, .p pv2 [pv2,pv11,pv43,pv1237], .c 5, .c 3, .p pv3 [pv2,pv13,pv29,pv97], .c 7, .c 3, .c 5,
  .c 23, .c 3, .c 13, .c 131, .c 3, .c 79, .c 17, .c 3, .p pv3 [pv2,pv7,pv20897], .c 5, .c 3,
  .c 7, .c 139, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv31,pv151], .c 7, .c 3, .c 11, .c 107,
  .c 3, .c 17, .c 5, .c 3, .c 787, .p pv3 [pv2,pv3,pv5,pv13003], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv97523], .c 3, .c 7, .c 1061, .c 3, .c 101, .c 67, .c 3, .c 53, .c 5, .c 3,
  .c 13, .c 11, .c 3, .c 5, .c 313, .c 3, .p pv7 [pv2,pv5,pv37,pv3163], .c 937, .c 3,
  .p pv2 [pv2,pv7,pv853], .c 199, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv146291], .c 17, .c 3,
  .c 5, .c 7, .c 3, .c 113, .c 19, .c 3, .c 37, .p pv7 [pv2,pv3,pv17,pv5737], .c 3, .c 29, .c 5,
  .c 3, .c 233, .p pv7 [pv2,pv3,pv5,pv3251], .c 3, .c 5, .c 11, .c 3, .c 991,
  .p pv2 [pv2,pv3,pv7,pv13933], .c 3, .c 13, .c 7, .c 3, .c 59, .c 5, .c 3, .c 11, .c 137, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv10837], .c 3, .c 23, .c 13, .c 3, .c 7, .c 73, .c 3, .c 251, .c 5, .c 3,
  .c 19, .c 7, .c 3, .c 5, .c 41, .c 3, .c 347, .c 11,
]
private theorem h0142c27 : checkBlock 1170179 128 b0142c27 = true := by
  decide +kernel

private def b0142c28 : List Row := [
  .c 3, .p pv2 [pv2,pv31,pv9439], .c 89, .c 3, .p pv2 [pv2,pv7,pv13,pv59,pv109], .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv17], .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv43,pv1361], .c 7, .c 3,
  .c 17, .c 29, .c 3, .c 107, .c 5, .c 3, .c 461, .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv65027],
  .c 3, .c 7, .c 23, .c 3, .p pv3 [pv2,pv18289], .c 11, .c 3, .c 43, .c 5, .c 3, .c 41,
  .p pv11 [pv2,pv3,pv5,pv11,pv3547], .c 3, .c 5, .p pv2 [pv2,pv3,pv23,pv4241], .c 3, .c 11,
  .p pv2 [pv2,pv3,pv65029], .c 3, .c 29, .c 31, .c 3, .c 7, .c 5, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv5,pv7,pv929], .c 3, .c 5, .c 7, .c 3, .c 109,
  .p pv7 [pv2,pv3,pv17,pv19,pv151], .c 3, .c 67, .c 13, .c 3, .p pv2 [pv2,pv23,pv25447], .c 5,
  .c 3, .c 17, .c 19, .c 3, .c 5, .c 71, .c 3, .p pv2 [pv2,pv5,pv107,pv547],
  .p pv5 [pv2,pv3,pv7,pv47,pv593], .c 3, .c 11, .c 7, .c 3, .p pv3 [pv2,pv157,pv233], .c 5, .c 3,
  .p pv11 [pv2,pv11,pv13,pv4093], .c 733, .c 3, .c 5, .p pv3 [pv2,pv3,pv37,pv5273], .c 3, .c 13,
  .c 263, .c 3, .c 7, .c 59, .c 3, .c 809, .c 5, .c 3, .c 47, .c 7, .c 3, .c 5, .c 13, .c 3,
  .p pv3 [pv2,pv5,pv14633], .c 29, .c 3, .c 19, .p pv11 [pv2,pv3,pv71,pv229], .c 3, .c 11, .c 5,
  .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv109,pv179], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv19,pv163],
  .c 3, .c 17, .c 7, .c 3, .c 23, .p pv3 [pv2,pv3,pv59,pv3307], .c 3, .p pv2 [pv2,pv585341], .c 5,
  .c 3, .c 13,
]
private theorem h0142c28 : checkBlock 1170435 128 b0142c28 = true := by
  decide +kernel

private def b0142c29 : List Row := [
  .c 67, .c 3, .c 5, .c 11, .c 3, .c 7, .c 151, .c 3, .p pv2 [pv2,pv89,pv6577],
  .p pv2 [pv2,pv3,pv7,pv11,pv181], .c 3, .p pv3 [pv2,pv61,pv2399], .c 5, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv5,pv271], .c 3, .c 5, .p pv3 [pv2,pv3,pv195121], .c 3, .c 379, .c 577, .c 3,
  .c 59, .c 17, .c 3, .c 7, .c 5, .c 3, .c 157, .p pv7 [pv2,pv3,pv5,pv7,pv223], .c 3, .c 5, .c 7,
  .c 3, .c 19, .c 11, .c 3, .c 13, .c 23, .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv7,pv241,pv347],
  .p pv2 [pv2,pv3,pv5,pv13,pv19,pv79], .c 3, .c 5, .p pv2 [pv2,pv3,pv195131], .c 3, .c 37, .c 13,
  .c 3, .c 139, .c 7, .c 3, .p pv2 [pv2,pv137,pv4273], .c 5, .c 3, .c 751,
  .p pv2 [pv2,pv3,pv5,pv13009], .c 3, .c 5, .c 29, .c 3, .p pv2 [pv2,pv5,pv7,pv8363], .c 53, .c 3,
  .c 7, .c 11, .c 3, .p pv3 [pv2,pv13,pv433], .c 5, .c 3, .c 31, .c 7, .c 3, .c 5, .c 43, .c 3,
  .c 11, .p pv2 [pv2,pv3,pv97571], .c 3, .p pv3 [pv2,pv19,pv7703], .c 79, .c 3,
  .p pv5 [pv2,pv7,pv11,pv7603], .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 229, .c 3, .c 83, .c 7,
  .c 3, .c 97, .c 181, .c 3, .c 101, .c 5, .c 3, .p pv2 [pv2,pv307,pv1907], .c 31, .c 3, .c 5,
  .c 23, .c 3, .c 7, .c 19, .c 3, .c 11, .c 41, .c 3, .c 13, .c 5, .c 3, .c 53, .c 193, .c 3,
  .c 5, .c 907, .c 3, .p pv2 [pv2,pv5,pv127,pv461], .c 17, .c 3,
]
private theorem h0142c29 : checkBlock 1170691 128 b0142c29 = true := by
  decide +kernel

private def b0142c30 : List Row := [
  .p pv2 [pv2,pv7,pv83639], .c 13, .c 3, .c 7, .c 5, .c 3, .c 67, .c 11, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv19,pv6163], .c 59, .c 3, .c 17, .p pv2 [pv2,pv3,pv195163], .c 3, .c 11, .c 5,
  .c 3, .c 19, .c 29, .c 3, .c 5, .c 523, .c 3, .c 13, .c 71, .c 3, .c 103, .c 7, .c 3, .c 37,
  .c 5, .c 3, .c 43, .c 191, .c 3, .c 5, .c 11, .c 3, .p pv7 [pv2,pv5,pv7,pv16729],
  .p pv7 [pv2,pv3,pv59,pv827], .c 3, .c 7, .p pv7 [pv2,pv3,pv11,pv1613], .c 3, .c 659, .c 5, .c 3,
  .c 11, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv31,pv787], .c 3, .p pv3 [pv2,pv5,pv11,pv5323],
  .c 157, .c 3, .c 127, .p pv2 [pv2,pv3,pv23,pv4243], .c 3, .p pv3 [pv2,pv7,pv1307], .c 5, .c 3,
  .c 7, .c 97, .c 3, .c 5, .c 31, .c 3, .c 23, .c 7, .c 3, .c 367, .c 47, .c 3, .c 19, .c 5, .c 3,
  .p pv2 [pv2,pv292777], .p pv3 [pv2,pv3,pv5,pv103,pv379], .c 3, .c 5, .p pv2 [pv2,pv3,pv32531],
  .c 3, .c 7, .p pv2 [pv2,pv3,pv19,pv10273], .c 3, .c 547, .c 823, .c 3,
  .p pv2 [pv2,pv113,pv2591], .c 5, .c 3, .c 61, .c 19, .c 3, .c 5, .c 17, .c 3, .c 89, .c 499,
  .c 3, .c 13, .c 11, .c 3, .c 7, .c 5, .c 3, .c 853, .c 167, .c 3, .c 5, .c 7, .c 3, .c 11,
  .c 13, .c 3, .c 769, .p pv2 [pv2,pv3,pv32533], .c 3, .c 47, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv17,pv19,pv37], .p pv7 [pv2,pv3,pv5,pv61],
]
private theorem h0142c30 : checkBlock 1170947 128 b0142c30 = true := by
  decide +kernel

private def b0142c31 : List Row := [
  .c 3, .c 5, .p pv3 [pv2,pv3,pv23,pv41], .c 3, .c 31, .c 83, .c 3, .c 19, .c 7, .c 3, .c 29,
  .c 5, .c 3, .c 23, .p pv3 [pv2,pv3,pv5,pv39041], .c 3, .c 5, .c 953, .c 3,
  .p pv3 [pv2,pv5,pv7,pv47,pv89], .p pv2 [pv2,pv3,pv31,pv2099], .c 3, .c 7, .c 17, .c 3,
  .p pv2 [pv2,pv23,pv29,pv439], .c 5, .c 3, .p pv2 [pv2,pv11,pv53239], .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv17,pv11483], .c 3, .c 131, .c 31, .c 3, .c 43, .c 389, .c 3, .c 17, .c 5,
  .c 3, .c 7, .c 11, .c 3, .c 5, .c 101, .c 3, .p pv2 [pv2,pv5,pv13,pv17,pv53], .c 7, .c 3,
  .c 151, .c 37, .c 3, .c 11, .c 5, .c 3, .p pv7 [pv2,pv163,pv3593], .c 23, .c 3, .c 5, .c 59,
  .c 3, .c 7, .c 79, .c 3, .c 283, .c 13, .c 3, .p pv5 [pv2,pv585671], .c 5, .c 3, .c 601, .c 17,
  .c 3, .c 5, .c 11, .c 3, .c 67, .c 43, .c 3, .c 23, .c 19, .c 3, .c 7, .c 5, .c 3, .c 11, .c 47,
  .c 3, .c 5, .c 7, .c 3, .c 13, .p pv5 [pv2,pv3,pv6101], .c 3, .c 29,
  .p pv3 [pv2,pv3,pv101,pv1933], .c 3, .c 191, .c 5, .c 3, .c 331, .c 41, .c 3, .c 5, .c 13, .c 3,
  .p pv3 [pv2,pv5,pv37,pv1583], .c 11, .c 3, .p pv2 [pv2,pv19,pv29,pv1063], .c 7, .c 3, .c 277,
  .c 5, .c 3, .c 947, .c 449, .c 3, .c 5, .p pv5 [pv2,pv3,pv195241], .c 3,
  .p pv2 [pv2,pv5,pv7,pv3347], .c 17, .c 3, .c 7,
]
private theorem h0142c31 : checkBlock 1171203 128 b0142c31 = true := by
  decide +kernel

def rows0142 : List Row :=
  b0142c00 ++ b0142c01 ++ b0142c02 ++ b0142c03 ++ b0142c04 ++ b0142c05 ++ b0142c06 ++ b0142c07 ++
  b0142c08 ++ b0142c09 ++ b0142c10 ++ b0142c11 ++ b0142c12 ++ b0142c13 ++ b0142c14 ++ b0142c15 ++
  b0142c16 ++ b0142c17 ++ b0142c18 ++ b0142c19 ++ b0142c20 ++ b0142c21 ++ b0142c22 ++ b0142c23 ++
  b0142c24 ++ b0142c25 ++ b0142c26 ++ b0142c27 ++ b0142c28 ++ b0142c29 ++ b0142c30 ++ b0142c31

attribute [local irreducible] checkBlock checkRows checkPrime

theorem checked0142 : checkBlock 1163267 4096 rows0142 = true :=
  checkBlock_append h0142c00 (
    checkBlock_append h0142c01 (
    checkBlock_append h0142c02 (
    checkBlock_append h0142c03 (
    checkBlock_append h0142c04 (
    checkBlock_append h0142c05 (
    checkBlock_append h0142c06 (
    checkBlock_append h0142c07 (
    checkBlock_append h0142c08 (
    checkBlock_append h0142c09 (
    checkBlock_append h0142c10 (
    checkBlock_append h0142c11 (
    checkBlock_append h0142c12 (
    checkBlock_append h0142c13 (
    checkBlock_append h0142c14 (
    checkBlock_append h0142c15 (
    checkBlock_append h0142c16 (
    checkBlock_append h0142c17 (
    checkBlock_append h0142c18 (
    checkBlock_append h0142c19 (
    checkBlock_append h0142c20 (
    checkBlock_append h0142c21 (
    checkBlock_append h0142c22 (
    checkBlock_append h0142c23 (
    checkBlock_append h0142c24 (
    checkBlock_append h0142c25 (
    checkBlock_append h0142c26 (
    checkBlock_append h0142c27 (
    checkBlock_append h0142c28 (
    checkBlock_append h0142c29 (
    checkBlock_append h0142c30 (
    h0142c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
