/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks03/Block0271
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks03/Block0271.checked0271
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table023
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table029
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table033
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table038
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table045
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table055
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table070
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table095
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table140

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0271c00 : List Row := [
  .c 5, .c 29, .c 3, .p pv3 [pv2,pv5,pv55501], .c 7, .c 3, .c 17, .c 13, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv79,pv14051], .c 293, .c 3, .c 5, .c 701, .c 3, .c 7, .p pv5 [pv2,pv3,pv92503],
  .c 3, .p pv2 [pv2,pv73,pv7603], .c 193, .c 3, .p pv2 [pv2,pv1110041], .c 5, .c 3,
  .p pv3 [pv2,pv13,pv21347], .c 1487, .c 3, .c 5, .c 11, .c 3, .c 13, .c 769, .c 3, .c 911, .c 41,
  .c 3, .c 7, .c 5, .c 3, .c 11, .c 23, .c 3, .c 5, .c 7, .c 3, .c 19, .c 43, .c 3, .c 79, .c 47,
  .c 3, .c 107, .c 5, .c 3, .c 17, .p pv29 [pv2,pv3,pv5,pv19,pv41], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv61,pv337], .c 3, .c 887, .c 11, .c 3, .c 23, .c 7, .c 3, .c 1193, .c 5, .c 3,
  .c 13, .c 281, .c 3, .c 5, .p pv7 [pv2,pv3,pv47,pv7873], .c 3, .c 41,
  .p pv5 [pv2,pv3,pv13,pv593], .c 3, .c 7, .p pv7 [pv2,pv3,pv370033], .c 3,
  .p pv2 [pv2,pv557,pv1993], .c 5, .c 3, .p pv3 [pv2,pv138763], .c 7, .c 3, .c 5, .c 17, .c 3,
  .c 109, .c 53, .c 3, .c 673, .c 11, .c 3, .c 47, .c 5, .c 3, .c 7, .c 71, .c 3, .c 5, .c 139,
  .c 3, .c 11, .c 7, .c 3, .c 13, .c 23, .c 3, .p pv5 [pv2,pv11,pv43,pv2347], .c 5, .c 3, .c 29,
  .p pv3 [pv2,pv3,pv5,pv13,pv5693], .c 3, .c 5, .p pv2 [pv2,pv3,pv53,pv3491], .c 3, .c 7, .c 13,
  .c 3, .c 227, .p pv23 [pv2,pv3,pv7,pv59],
]
private theorem h0271c00 : checkBlock 2220035 128 b0271c00 = true := by
  decide +kernel

private def b0271c01 : List Row := [
  .c 3, .p pv2 [pv2,pv555073], .c 5, .c 3, .c 661, .p pv2 [pv2,pv3,pv5,pv2467], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv33641], .c 3, .p pv11 [pv2,pv5,pv239,pv929], .c 31, .c 3, .c 11, .c 17,
  .c 3, .c 7, .c 5, .c 3, .c 53, .p pv2 [pv2,pv3,pv5,pv7,pv97,pv109], .c 3, .c 5, .c 7, .c 3,
  .c 127, .c 1039, .c 3, .c 59, .p pv2 [pv2,pv3,pv13,pv43,pv331], .c 3, .c 17, .c 5, .c 3, .c 19,
  .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv370061], .c 3, .c 103, .p pv5 [pv2,pv3,pv7,pv11,pv89],
  .c 3, .c 1439, .c 7, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv555097], .c 43, .c 3, .c 5, .c 19,
  .c 3, .c 1019, .p pv3 [pv2,pv3,pv370067], .c 3, .c 7, .p pv17 [pv2,pv3,pv30839], .c 3, .c 13,
  .c 5, .c 3, .p pv2 [pv2,pv283,pv3923], .c 7, .c 3, .c 5, .c 11, .c 3,
  .p pv11 [pv2,pv5,pv222043], .c 683, .c 3, .c 31, .c 13, .c 3, .c 23, .c 5, .c 3, .c 7, .c 157,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv13217], .c 3, .c 61, .c 7, .c 3, .p pv2 [pv2,pv23,pv48271],
  .c 373, .c 3, .c 19, .c 5, .c 3, .p pv7 [pv2,pv13,pv41,pv2083], .c 37, .c 3, .c 5, .c 857, .c 3,
  .c 7, .c 11, .c 3, .p pv3 [pv2,pv137,pv1013], .c 31, .c 3, .p pv5 [pv2,pv521,pv2131], .c 5,
  .c 3, .c 263, .c 19, .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv43,pv1291], .c 17, .c 3,
  .p pv5 [pv2,pv7,pv11,pv14419], .p pv19 [pv2,pv3,pv46261], .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv1110269], .c 53, .c 3, .c 5,
]
private theorem h0271c01 : checkBlock 2220291 128 b0271c01 = true := by
  decide +kernel

private def b0271c02 : List Row := [
  .c 7, .c 3, .p pv7 [pv2,pv5,pv89,pv499], .p pv5 [pv2,pv3,pv30841], .c 3, .c 17, .c 11, .c 3,
  .c 43, .c 5, .c 3, .c 13, .c 107, .c 3, .c 5, .c 103, .c 3, .c 11, .c 59, .c 3, .c 19, .c 7,
  .c 3, .c 1307, .c 5, .c 3, .c 167, .c 41, .c 3, .c 5, .c 1063, .c 3, .c 79, .c 229, .c 3, .c 7,
  .c 571, .c 3, .c 31, .c 5, .c 3, .c 37, .c 7, .c 3, .c 5, .c 461, .c 3, .c 199,
  .p pv2 [pv2,pv3,pv17,pv41,pv59], .c 3, .c 11, .c 43, .c 3, .p pv2 [pv2,pv7,pv79309], .c 5, .c 3,
  .c 7, .p pv29 [pv2,pv3,pv5,pv13,pv73], .c 3, .c 5, .c 71, .c 3, .p pv13 [pv2,pv5,pv222067],
  .c 7, .c 3, .c 971, .c 331, .c 3, .c 41, .c 5, .c 3, .c 181, .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv23,pv149], .c 3, .c 7, .c 37, .c 3, .c 751, .c 277, .c 3, .c 11, .c 5, .c 3,
  .c 23, .c 977, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv222073], .c 29, .c 3, .c 257, .c 19,
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv83,pv6689], .c 13, .c 3, .c 5, .c 7, .c 3, .c 17, .c 1051,
  .c 3, .c 509, .c 79, .c 3, .p pv2 [pv2,pv263,pv2111], .c 5, .c 3, .c 11, .c 197, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv123377], .c 3, .c 29, .c 491, .c 3, .c 47, .c 7, .c 3,
]
private theorem h0271c02 : checkBlock 2220547 128 b0271c02 = true := by
  decide +kernel

private def b0271c03 : List Row := [
  .c 13, .c 5, .c 3, .c 31, .c 23, .c 3, .c 5, .c 89, .c 3, .c 43, .c 11, .c 3, .c 7, .c 13, .c 3,
  .c 839, .c 5, .c 3, .p pv11 [pv2,pv307,pv3617], .c 7, .c 3, .c 5, .c 41, .c 3, .c 37, .c 19,
  .c 3, .c 23, .c 53, .c 3, .c 17, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5, .c 1187, .c 3, .c 13,
  .c 7, .c 3, .p pv5 [pv2,pv103,pv10781], .c 11, .c 3, .p pv2 [pv2,pv107,pv5189], .c 5, .c 3,
  .c 613, .c 439, .c 3, .c 5, .c 13, .c 3, .c 7, .p pv5 [pv2,pv3,pv53,pv97], .c 3,
  .p pv2 [pv2,pv67,pv8287], .p pv3 [pv2,pv3,pv7,pv52879], .c 3, .p pv2 [pv2,pv11,pv157,pv643],
  .c 5, .c 3, .c 19, .c 17, .c 3, .c 5, .c 59, .c 3, .p pv2 [pv2,pv5,pv293,pv379], .c 431, .c 3,
  .c 1289, .c 23, .c 3, .c 7, .c 5, .c 3, .c 13, .p pv11 [pv2,pv3,pv5,pv7,pv661], .c 3, .c 5,
  .c 7, .c 3, .p pv7 [pv2,pv5,pv41,pv5417], .p pv7 [pv2,pv3,pv13,pv23,pv619], .c 3, .c 11,
  .p pv2 [pv2,pv3,pv197,pv1879], .c 3, .c 67, .c 5, .c 3, .c 103, .c 719, .c 3, .c 5, .c 83, .c 3,
  .c 881, .c 1213, .c 3, .p pv5 [pv2,pv79,pv14057], .c 7, .c 3, .c 607, .c 5, .c 3,
  .p pv11 [pv2,pv23,pv53,pv911], .c 11, .c 3, .c 5, .c 239, .c 3, .p pv7 [pv2,pv5,pv7,pv31729],
  .c 17, .c 3, .c 7, .c 199, .c 3, .c 11, .c 5, .c 3, .c 499, .c 7, .c 3, .c 5, .c 31,
]
private theorem h0271c03 : checkBlock 2220803 128 b0271c03 = true := by
  decide +kernel

private def b0271c04 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv111053], .c 13, .c 3, .c 17, .p pv2 [pv2,pv3,pv185089], .c 3, .c 37,
  .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 11, .c 3, .c 101, .c 7, .c 3, .p pv3 [pv2,pv277637],
  .c 251, .c 3, .c 127, .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv23,pv29,pv37], .c 3, .c 5, .c 67,
  .c 3, .c 7, .c 479, .c 3, .p pv5 [pv2,pv47,pv23629], .p pv23 [pv2,pv3,pv7,pv13,pv113], .c 3,
  .c 23, .c 5, .c 3, .c 29, .c 13, .c 3, .c 5, .c 37, .c 3, .c 647, .c 11, .c 3, .c 19,
  .p pv3 [pv2,pv3,pv370193], .c 3, .c 7, .c 5, .c 3, .c 17, .c 73, .c 3, .c 5, .c 7, .c 3, .c 31,
  .p pv3 [pv2,pv3,pv13711], .c 3, .p pv2 [pv2,pv11,pv17,pv5939], .c 233, .c 3, .c 13, .c 5, .c 3,
  .c 967, .c 163, .c 3, .c 5, .c 487, .c 3, .c 179, .c 107, .c 3, .p pv3 [pv2,pv41,pv1693], .c 7,
  .c 3, .c 919, .c 5, .c 3, .p pv2 [pv2,pv555307], .p pv11 [pv2,pv3,pv5,pv11,pv53,pv127], .c 3,
  .c 5, .c 17, .c 3, .c 11, .c 31, .c 3, .c 7, .p pv11 [pv2,pv3,pv23,pv503], .c 3,
  .p pv2 [pv2,pv11,pv19,pv2657], .c 5, .c 3, .p pv2 [pv2,pv13,pv37,pv2309], .c 7, .c 3, .c 5,
  .c 47, .c 3, .c 13, .p pv5 [pv2,pv3,pv30851], .c 3, .c 823, .c 409, .c 3, .c 53, .c 5, .c 3,
  .c 7, .c 59, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv97,pv229], .c 7, .c 3, .c 11, .c 19,
  .c 3, .c 29,
]
private theorem h0271c04 : checkBlock 2221059 128 b0271c04 = true := by
  decide +kernel

private def b0271c05 : List Row := [
  .c 5, .c 3, .c 379, .p pv19 [pv2,pv3,pv5,pv107,pv173], .c 3, .c 5, .c 1109, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv37,pv5003], .c 3, .c 43, .c 17, .c 3, .p pv11 [pv2,pv29,pv38299], .c 5, .c 3,
  .c 13, .c 11, .c 3, .c 5, .c 127, .c 3, .c 47, .c 23, .c 3, .c 31, .c 37, .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv593,pv1873], .p pv13 [pv2,pv3,pv5,pv7,pv41,pv43], .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv17,pv73,pv179], .c 157, .c 3, .c 97, .p pv13 [pv2,pv3,pv31,pv1327], .c 3,
  .p pv2 [pv2,pv269,pv4129], .c 5, .c 3, .c 23, .p pv2 [pv2,pv3,pv5,pv74047], .c 3, .c 5, .c 11,
  .c 3, .c 41, .c 19, .c 3, .c 13, .c 7, .c 3, .p pv3 [pv2,pv23,pv12073], .c 5, .c 3, .c 11,
  .c 17, .c 3, .c 5, .p pv3 [pv2,pv3,pv370241], .c 3, .c 367, .c 13, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv17,pv29,pv751], .c 3, .c 73, .c 5, .c 3, .c 701, .c 7, .c 3, .c 5, .c 457,
  .c 3, .c 1451, .c 11, .c 3, .c 29, .c 659, .c 3, .c 173, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv653], .c 3, .p pv13 [pv2,pv5,pv222151], .c 7, .c 3, .c 37, .c 67, .c 3,
  .p pv2 [pv2,pv31,pv35831], .c 5, .c 3, .c 89, .c 13, .c 3, .c 5, .c 19, .c 3, .c 7, .c 17, .c 3,
  .c 23, .c 11, .c 3, .c 31, .c 5, .c 3, .c 61, .c 263, .c 3, .c 5, .p pv3 [pv2,pv3,pv370261],
  .c 3,
]
private theorem h0271c05 : checkBlock 2221315 128 b0271c05 = true := by
  decide +kernel

private def b0271c06 : List Row := [
  .c 11, .c 673, .c 3, .c 17, .c 389, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv373,pv1489], .c 37,
  .c 3, .c 5, .c 7, .c 3, .c 53, .c 29, .c 3, .c 103, .c 13, .c 3, .c 19, .c 5, .c 3, .c 211,
  .c 661, .c 3, .c 5, .c 937, .c 3, .p pv11 [pv2,pv5,pv222163], .p pv5 [pv2,pv3,pv7,pv19,pv29],
  .c 3, .c 11, .c 7, .c 3, .c 47, .c 5, .c 3, .c 227, .c 19, .c 3, .c 5, .p pv5 [pv2,pv3,pv92569],
  .c 3, .c 13, .c 151, .c 3, .c 7, .p pv13 [pv2,pv3,pv6857], .c 3, .p pv3 [pv2,pv331,pv839], .c 5,
  .c 3, .c 17, .c 7, .c 3, .c 5, .c 13, .c 3, .c 599, .c 113, .c 3, .c 101,
  .p pv2 [pv2,pv3,pv379,pv977], .c 3, .c 11, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv103,pv719],
  .c 3, .c 5, .c 79, .c 3, .p pv3 [pv2,pv5,pv67,pv829], .c 7, .c 3, .c 19, .c 137, .c 3,
  .p pv2 [pv2,pv71,pv7823], .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv12343], .c 3, .c 5, .c 11,
  .c 3, .c 7, .p pv5 [pv2,pv3,pv13,pv7121], .c 3, .p pv2 [pv2,pv555439], .c 307, .c 3, .c 59,
  .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv31,pv2389], .c 3, .c 5, .c 23, .c 3, .c 17, .c 383,
  .c 3, .c 67, .p pv2 [pv2,pv3,pv185149], .c 3, .c 7, .c 5, .c 3, .c 683, .c 31, .c 3, .c 5, .c 7,
  .c 3, .c 1291, .c 11, .c 3, .c 13, .c 293, .c 3, .c 23, .c 5,
]
private theorem h0271c06 : checkBlock 2221571 128 b0271c06 = true := by
  decide +kernel

private def b0271c07 : List Row := [
  .c 3, .p pv3 [pv2,pv7,pv73,pv1087], .c 41, .c 3, .c 5, .p pv5 [pv2,pv3,pv185153], .c 3, .c 19,
  .c 13, .c 3, .p pv5 [pv2,pv11,pv23,pv4391], .c 7, .c 3, .c 43, .c 5, .c 3,
  .p pv2 [pv2,pv1110929], .p pv7 [pv2,pv3,pv5,pv19,pv1949], .c 3, .c 5, .c 281, .c 3,
  .p pv13 [pv2,pv5,pv7,pv31741], .c 557, .c 3, .c 7, .c 11, .c 3, .c 17, .c 5, .c 3,
  .p pv3 [pv2,pv149,pv233], .c 7, .c 3, .c 5, .c 601, .c 3, .c 11, .c 191, .c 3,
  .p pv2 [pv2,pv1110953], .p pv2 [pv2,pv3,pv13,pv14243], .c 3, .c 41, .c 5, .c 3, .c 7, .c 13,
  .c 3, .c 5, .c 179, .c 3, .p pv2 [pv2,pv5,pv222193], .c 7, .c 3, .c 463, .c 43, .c 3,
  .p pv5 [pv2,pv1110971], .c 5, .c 3, .p pv2 [pv2,pv555487], .c 17, .c 3, .c 5, .c 419, .c 3,
  .c 7, .c 197, .c 3, .c 11, .p pv19 [pv2,pv3,pv7,pv17,pv389], .c 3, .c 13, .c 5, .c 3, .c 97,
  .p pv2 [pv2,pv3,pv5,pv29,pv1277], .c 3, .c 5, .c 31, .c 3, .p pv7 [pv2,pv5,pv222199], .c 19,
  .c 3, .p pv3 [pv2,pv7,pv79357], .c 13, .c 3, .c 7, .c 5, .c 3, .c 29, .c 11, .c 3, .c 5, .c 7,
  .c 3, .c 157, .p pv13 [pv2,pv3,pv11,pv131,pv257], .c 3, .c 577, .c 1381, .c 3, .c 11, .c 5,
  .c 3, .p pv17 [pv2,pv7,pv13,pv29,pv421], .c 211, .c 3, .c 5, .c 61, .c 3, .c 13, .c 17, .c 3,
  .c 1459, .c 7, .c 3, .c 89, .c 5, .c 3, .c 19, .p pv3 [pv2,pv3,pv5,pv17,pv4357], .c 3, .c 5,
  .c 11, .c 3, .c 479,
]
private theorem h0271c07 : checkBlock 2221827 128 b0271c07 = true := by
  decide +kernel

private def b0271c08 : List Row := [
  .c 349, .c 3, .c 7, .p pv37 [pv2,pv3,pv11,pv19,pv443], .c 3, .p pv2 [pv2,pv555523], .c 5, .c 3,
  .c 11, .c 7, .c 3, .c 5, .c 19, .c 3, .c 31, .c 47, .c 3, .c 59, .c 127, .c 3,
  .p pv2 [pv2,pv7,pv23,pv67,pv103], .c 5, .c 3, .c 7, .c 53, .c 3, .c 5, .c 181, .c 3,
  .p pv3 [pv2,pv5,pv137,pv811], .c 7, .c 3, .p pv2 [pv2,pv37,pv30029], .c 827, .c 3, .c 131, .c 5,
  .c 3, .c 41, .c 563, .c 3, .c 5, .p pv3 [pv2,pv3,pv383,pv967], .c 3, .c 7, .c 31, .c 3,
  .p pv3 [pv2,pv11,pv59,pv107], .c 163, .c 3, .c 19, .c 5, .c 3, .c 17, .c 23, .c 3, .c 5, .c 43,
  .c 3, .c 857, .p pv5 [pv2,pv3,pv19,pv101,pv193], .c 3, .c 13, .c 11, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv439,pv2531], .c 19, .c 3, .c 5, .c 7, .c 3, .c 11, .c 13, .c 3, .c 23,
  .p pv3 [pv2,pv3,pv370373], .c 3, .p pv2 [pv2,pv11,pv83,pv1217], .c 5, .c 3,
  .p pv3 [pv2,pv7,pv5669], .p pv2 [pv2,pv3,pv5,pv2963], .c 3, .c 5, .c 17, .c 3, .c 241,
  .p pv5 [pv2,pv3,pv7,pv5879], .c 3, .c 151, .c 7, .c 3, .p pv3 [pv2,pv13,pv2671], .c 5, .c 3,
  .c 257, .p pv17 [pv2,pv3,pv5,pv6173], .c 3, .c 5, .p pv7 [pv2,pv3,pv11,pv3061], .c 3, .c 17,
  .p pv2 [pv2,pv3,pv109,pv1699], .c 3, .c 7, .c 29, .c 3, .c 101, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv17,pv2971], .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv19], .c 3,
  .p pv3 [pv2,pv5,pv27779], .c 41, .c 3, .p pv5 [pv2,pv43,pv25841], .c 23, .c 3,
  .p pv2 [pv2,pv7,pv139,pv571], .c 5, .c 3,
]
private theorem h0271c08 : checkBlock 2222083 128 b0271c08 = true := by
  decide +kernel

private def b0271c09 : List Row := [
  .c 7, .c 11, .c 3, .c 5, .c 641, .c 3, .p pv19 [pv2,pv5,pv13,pv263], .c 7, .c 3, .c 29, .c 17,
  .c 3, .c 11, .c 5, .c 3, .c 43, .c 71, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv17,pv419], .c 3, .c 7,
  .p pv5 [pv2,pv3,pv587,pv631], .c 3, .p pv2 [pv2,pv29,pv38317], .c 13, .c 3, .c 17, .c 5, .c 3,
  .c 283, .c 109, .c 3, .c 5, .c 11, .c 3, .c 19, .c 61, .c 3, .c 1123, .c 89, .c 3, .c 7, .c 5,
  .c 3, .c 11, .c 103, .c 3, .c 5, .c 7, .c 3, .c 13, .p pv2 [pv2,pv3,pv37,pv47,pv71], .c 3,
  .c 821, .c 19, .c 3, .c 467, .c 5, .c 3, .c 421, .c 17, .c 3, .c 5, .c 13, .c 3, .c 59, .c 11,
  .c 3, .p pv2 [pv2,pv191,pv2909], .c 7, .c 3, .c 31, .c 5, .c 3, .c 47, .c 83, .c 3, .c 5,
  .c 107, .c 3, .p pv3 [pv2,pv5,pv7,pv127], .p pv3 [pv2,pv3,pv29,pv53,pv241], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv89,pv2081], .c 3, .c 23, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv370421], .c 3, .c 29, .p pv2 [pv2,pv3,pv13,pv1583], .c 3,
  .p pv3 [pv2,pv23,pv47,pv257], .c 11, .c 3, .p pv5 [pv2,pv7,pv22679], .c 5, .c 3, .c 7, .c 137,
  .c 3, .c 5, .c 227, .c 3, .c 11, .c 7, .c 3, .p pv5 [pv2,pv1111283], .c 41, .c 3,
  .p pv2 [pv2,pv11,pv50513], .c 5, .c 3, .p pv2 [pv2,pv1111289], .c 1151, .c 3, .c 5, .c 233,
  .c 3, .c 7, .p pv11 [pv2,pv3,pv1447],
]
private theorem h0271c09 : checkBlock 2222339 128 b0271c09 = true := by
  decide +kernel

private def b0271c10 : List Row := [
  .c 3, .c 13, .p pv3 [pv2,pv3,pv7,pv52919], .c 3, .c 167, .c 5, .c 3, .c 947,
  .p pv2 [pv2,pv3,pv5,pv13,pv41,pv139], .c 3, .c 5, .p pv13 [pv2,pv3,pv11,pv8419], .c 3,
  .p pv2 [pv2,pv5,pv19,pv5849], .c 13, .c 3, .c 11, .p pv2 [pv2,pv3,pv23,pv8053], .c 3, .c 7,
  .c 5, .c 3, .c 19, .c 223, .c 3, .c 5, .c 7, .c 3, .c 23, .p pv5 [pv2,pv3,pv185221], .c 3,
  .c 61, .p pv23 [pv2,pv3,pv19,pv67,pv97], .c 3, .p pv5 [pv2,pv13,pv85487], .c 5, .c 3, .c 31,
  .c 11, .c 3, .c 5, .c 19, .c 3, .c 1471, .p pv2 [pv2,pv3,pv7,pv11,pv17,pv283], .c 3,
  .p pv5 [pv2,pv89,pv12487], .c 7, .c 3, .c 11, .c 5, .c 3, .c 17, .c 13, .c 3, .c 5, .c 59, .c 3,
  .c 107, .c 43, .c 3, .c 7, .p pv11 [pv2,pv3,pv61,pv6073], .c 3, .p pv2 [pv2,pv1111361], .c 5,
  .c 3, .p pv3 [pv2,pv109,pv2549], .c 7, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv13,pv83,pv103], .c 23, .c 3, .c 269, .c 139, .c 3, .c 13, .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv18523], .c 3, .c 5, .c 17, .c 3, .c 47, .c 7, .c 3, .c 73, .c 13, .c 3,
  .p pv5 [pv2,pv149,pv7459], .c 5, .c 3, .c 23, .c 19, .c 3, .c 5, .c 71, .c 3, .c 7, .c 11, .c 3,
  .c 659, .p pv11 [pv2,pv3,pv7,pv101,pv131], .c 3, .c 991, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv17,pv47,pv107], .c 29, .c 3, .c 5, .c 1009, .c 3, .c 13, .c 797, .c 3,
  .c 109, .p pv3 [pv2,pv3,pv123491], .c 3, .c 7, .c 5, .c 3, .c 37,
]
private theorem h0271c10 : checkBlock 2222595 128 b0271c10 = true := by
  decide +kernel

private def b0271c11 : List Row := [
  .c 643, .c 3, .c 5, .c 7, .c 3, .c 181, .c 463, .c 3, .c 19, .c 11, .c 3, .c 53, .c 5, .c 3,
  .c 29, .c 23, .c 3, .c 5, .c 1373, .c 3, .c 11, .p pv5 [pv2,pv3,pv7,pv8821], .c 3, .c 41, .c 7,
  .c 3, .c 17, .c 5, .c 3, .c 13, .p pv11 [pv2,pv3,pv5,pv8233], .c 3, .c 5, .c 31, .c 3,
  .p pv3 [pv2,pv5,pv7,pv17,pv467], .c 37, .c 3, .c 7, .p pv13 [pv2,pv3,pv43,pv359], .c 3,
  .p pv2 [pv2,pv383,pv1451], .c 5, .c 3, .c 71, .c 7, .c 3, .c 5, .c 691, .c 3, .c 811, .c 89,
  .c 3, .c 11, .c 47, .c 3, .c 157, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv827], .c 3, .c 19, .c 7, .c 3, .c 13, .c 83, .c 3, .c 67, .c 5, .c 3,
  .c 449, .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv47,pv7883], .c 3, .c 7, .c 13, .c 3, .c 1483,
  .c 19, .c 3, .c 11, .c 5, .c 3, .c 199, .p pv3 [pv2,pv3,pv5,pv74101], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv61751], .c 3, .c 31, .p pv2 [pv2,pv3,pv23,pv89,pv181], .c 3,
  .p pv5 [pv2,pv7,pv97,pv1637], .c 103, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv857,pv1297], .c 41,
  .c 3, .c 5, .c 7, .c 3, .c 37, .c 17, .c 3, .c 1489, .p pv3 [pv2,pv3,pv11,pv13,pv2591], .c 3,
  .c 569, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 929, .c 3, .p pv2 [pv2,pv5,pv11,pv43,pv47],
  .c 31, .c 3,
]
private theorem h0271c11 : checkBlock 2222851 128 b0271c11 = true := by
  decide +kernel

private def b0271c12 : List Row := [
  .c 17, .c 7, .c 3, .p pv3 [pv2,pv277889], .c 5, .c 3, .p pv13 [pv2,pv1111559], .c 317, .c 3,
  .c 5, .c 67, .c 3, .c 89, .c 11, .c 3, .c 7, .c 79, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv719,pv773], .c 7, .c 3, .c 5, .c 23, .c 3, .p pv3 [pv2,pv5,pv55579],
  .p pv2 [pv2,pv3,pv113,pv1093], .c 3, .c 193, .c 13, .c 3, .c 151, .c 5, .c 3, .c 7, .c 577,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv43,pv1231], .c 3, .c 53, .c 7, .c 3,
  .p pv3 [pv2,pv31,pv17929], .c 11, .c 3, .c 23, .c 5, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv5,pv11,pv6737], .c 3, .c 5, .p pv5 [pv2,pv3,pv15439], .c 3, .c 7, .c 71, .c 3,
  .c 29, .c 43, .c 3, .p pv3 [pv2,pv11,pv1579], .c 5, .c 3, .c 313, .c 47, .c 3, .c 5, .c 13,
  .c 3, .c 1187, .p pv11 [pv2,pv3,pv61757], .c 3, .c 1277, .p pv3 [pv2,pv3,pv31,pv11953], .c 3,
  .c 7, .c 5, .c 3, .p pv2 [pv2,pv677,pv821], .c 167, .c 3, .c 5, .c 7, .c 3,
  .p pv13 [pv2,pv5,pv27791], .p pv2 [pv2,pv3,pv370547], .c 3, .c 11, .c 31, .c 3, .c 37, .c 5,
  .c 3, .c 13, .c 421, .c 3, .c 5, .c 41, .c 3, .c 17, .c 101, .c 3, .p pv2 [pv2,pv555829], .c 7,
  .c 3, .c 19, .c 5, .c 3, .p pv3 [pv2,pv17,pv61,pv67], .c 11, .c 3, .c 5, .c 97, .c 3, .c 23,
  .c 29, .c 3, .c 7, .c 953, .c 3, .c 11, .c 5, .c 3, .c 179, .c 7,
]
private theorem h0271c12 : checkBlock 2223107 128 b0271c12 = true := by
  decide +kernel

private def b0271c13 : List Row := [
  .c 3, .c 5, .c 37, .c 3, .p pv2 [pv2,pv5,pv222337], .c 137, .c 3, .c 13, .c 17, .c 3,
  .p pv7 [pv2,pv7,pv31,pv47,pv109], .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv13,pv5701], .c 3,
  .c 5, .c 11, .c 3, .c 29, .c 7, .c 3, .p pv5 [pv2,pv1111703], .c 1301, .c 3, .c 17, .c 5, .c 3,
  .c 11, .p pv2 [pv2,pv3,pv5,pv37057], .c 3, .c 5, .c 199, .c 3, .c 7, .c 23, .c 3, .c 19,
  .c 1283, .c 3, .p pv5 [pv2,pv13,pv85517], .c 5, .c 3, .p pv3 [pv2,pv449,pv619],
  .p pv53 [pv2,pv3,pv5,pv61], .c 3, .c 5, .p pv13 [pv2,pv3,pv19,pv23,pv53], .c 3, .c 103, .c 11,
  .c 3, .p pv2 [pv2,pv7,pv241,pv659], .p pv2 [pv2,pv3,pv13,pv4751], .c 3, .c 7, .c 5, .c 3, .c 23,
  .c 13, .c 3, .c 5, .c 7, .c 3, .c 109, .p pv11 [pv2,pv3,pv185291], .c 3,
  .p pv3 [pv2,pv11,pv2297], .p pv2 [pv2,pv3,pv17,pv21799], .c 3, .p pv5 [pv2,pv23,pv48337], .c 5,
  .c 3, .c 53, .c 61, .c 3, .c 5, .c 29, .c 3, .p pv17 [pv2,pv5,pv13,pv1069], .c 47, .c 3, .c 149,
  .c 7, .c 3, .c 13, .c 5, .c 3, .c 197, .p pv2 [pv2,pv3,pv5,pv11,pv1123], .c 3, .c 5, .c 353,
  .c 3, .c 11, .c 41, .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv11,pv53,pv1907], .c 5, .c 3, .c 173,
  .c 7, .c 3, .c 5, .c 293, .c 3, .p pv2 [pv2,pv5,pv73,pv1523], .c 17, .c 3,
  .p pv2 [pv2,pv1111793], .c 19, .c 3, .c 379, .c 5, .c 3, .c 7, .c 307, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv7,pv11,pv4813], .c 3, .c 13, .c 7, .c 3, .c 11,
]
private theorem h0271c13 : checkBlock 2223363 128 b0271c13 = true := by
  decide +kernel

private def b0271c14 : List Row := [
  .c 1097, .c 3, .p pv5 [pv2,pv191,pv5821], .c 5, .c 3, .c 641, .p pv13 [pv2,pv3,pv5,pv31,pv797],
  .c 3, .c 5, .c 13, .c 3, .c 7, .c 127, .c 3, .c 137, .c 71, .c 3, .c 73, .c 5, .c 3, .c 43,
  .c 11, .c 3, .c 5, .c 103, .c 3, .p pv13 [pv2,pv5,pv222367], .p pv17 [pv2,pv3,pv11,pv8423],
  .c 3, .p pv2 [pv2,pv7,pv13,pv41,pv149], .p pv3 [pv2,pv3,pv370613], .c 3, .c 7, .c 5, .c 3,
  .c 13, .c 29, .c 3, .c 5, .c 7, .c 3, .p pv11 [pv2,pv5,pv37,pv601], .c 19, .c 3, .c 241, .c 23,
  .c 3, .p pv3 [pv2,pv69491], .c 5, .c 3, .c 17, .c 53, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv67,pv3319], .c 409, .c 3, .c 37, .c 7, .c 3, .p pv5 [pv2,pv173,pv6427], .c 5,
  .c 3, .c 11, .c 911, .c 3, .c 5, .p pv5 [pv2,pv3,pv223,pv277], .c 3,
  .p pv13 [pv2,pv5,pv7,pv11,pv19], .c 503, .c 3, .c 7, .c 59, .c 3, .p pv2 [pv2,pv167,pv3329],
  .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 17, .c 3, .c 71, .c 11, .c 3, .c 67, .c 41, .c 3,
  .c 827, .c 5, .c 3, .c 7, .c 37, .c 3, .c 5, .c 19, .c 3, .c 17, .c 7, .c 3, .c 53,
  .p pv2 [pv2,pv3,pv59,pv349], .c 3, .p pv3 [pv2,pv13,pv21383], .c 5, .c 3,
  .p pv7 [pv2,pv17,pv65407], .p pv17 [pv2,pv3,pv5,pv41,pv113], .c 3, .c 5, .c 23, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv47,pv3943], .c 3, .p pv3 [pv2,pv131,pv1061], .c 11, .c 3, .c 337, .c 5, .c 3,
  .p pv2 [pv2,pv555967], .c 13, .c 3,
]
private theorem h0271c14 : checkBlock 2223619 128 b0271c14 = true := by
  decide +kernel

private def b0271c15 : List Row := [
  .c 5, .c 61, .c 3, .c 11, .p pv17 [pv2,pv3,pv41183], .c 3, .c 59, .c 17, .c 3, .c 7, .c 5, .c 3,
  .c 47, .p pv2 [pv2,pv3,pv5,pv7,pv353], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv13,pv17107],
  .c 389, .c 3, .c 43, .c 97, .c 3, .c 13, .c 5, .c 3, .c 79, .c 19, .c 3, .c 5,
  .p pv23 [pv2,pv3,pv11,pv13], .c 3, .c 809, .p pv3 [pv2,pv3,pv7,pv52951], .c 3, .c 11, .c 7,
  .c 3, .c 113, .c 5, .c 3, .c 37, .c 311, .c 3, .c 5, .p pv3 [pv2,pv3,pv370661], .c 3, .c 31,
  .p pv5 [pv2,pv3,pv163,pv379], .c 3, .c 7, .c 223, .c 3, .p pv5 [pv2,pv1111991], .c 5, .c 3,
  .c 331, .c 7, .c 3, .c 5, .c 479, .c 3, .c 13, .c 43, .c 3, .c 19,
  .p pv11 [pv2,pv3,pv17,pv23,pv79], .c 3, .c 11, .c 5, .c 3, .c 7, .c 89, .c 3, .c 5, .c 13, .c 3,
  .c 23, .c 7, .c 3, .p pv2 [pv2,pv109,pv5101], .c 29, .c 3, .c 499, .c 5, .c 3, .c 1033, .c 541,
  .c 3, .c 5, .c 11, .c 3, .c 7, .p pv3 [pv2,pv3,pv157,pv787], .c 3, .c 619,
  .p pv2 [pv2,pv3,pv7,pv11,pv29,pv83], .c 3, .p pv3 [pv2,pv317,pv877], .c 5, .c 3, .c 11, .c 383,
  .c 3, .c 5, .c 47, .c 3, .c 73, .c 17, .c 3, .c 29, .p pv2 [pv2,pv3,pv13729], .c 3, .c 7, .c 5,
  .c 3, .c 1367, .c 251, .c 3, .c 5, .c 7, .c 3, .c 19, .c 11, .c 3, .c 17, .c 487,
]
private theorem h0271c15 : checkBlock 2223875 128 b0271c15 = true := by
  decide +kernel

private def b0271c16 : List Row := [
  .c 3, .c 709, .c 5, .c 3, .c 139, .p pv2 [pv2,pv3,pv5,pv19,pv1951], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv23,pv71,pv227], .c 3, .c 83, .p pv11 [pv2,pv3,pv7,pv1471], .c 3, .c 13, .c 7,
  .c 3, .c 293, .c 5, .c 3, .c 23, .p pv2 [pv2,pv3,pv5,pv13,pv1901], .c 3, .c 5, .c 349, .c 3,
  .c 37, .c 13, .c 3, .c 7, .c 11, .c 3, .p pv3 [pv2,pv23,pv1511], .c 5, .c 3, .c 67, .c 7, .c 3,
  .c 5, .c 829, .c 3, .c 11, .c 29, .c 3, .c 71, .c 31, .c 3, .c 199, .c 5, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv5,pv151,pv491], .c 3, .c 5, .c 73, .c 3, .c 59, .c 7, .c 3,
  .p pv5 [pv2,pv17,pv65419], .c 131, .c 3, .c 353, .c 5, .c 3, .p pv2 [pv2,pv1112129], .c 13,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv67,pv503], .c 3, .c 7, .c 19, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv7,pv127,pv139], .c 3, .p pv2 [pv2,pv1112141], .c 5, .c 3,
  .p pv3 [pv2,pv11,pv71,pv89], .c 41, .c 3, .c 5, .c 17, .c 3, .c 601, .c 443, .c 3, .c 23,
  .c 181, .c 3, .c 7, .c 5, .c 3, .c 523, .c 11, .c 3, .c 5, .c 7, .c 3, .c 17, .c 67, .c 3,
  .p pv3 [pv2,pv139021], .c 13, .c 3, .c 11, .c 5, .c 3, .c 19, .c 379, .c 3, .c 5, .c 53, .c 3,
  .c 269, .c 109, .c 3, .p pv5 [pv2,pv37,pv30059], .c 7, .c 3, .c 41, .c 5, .c 3,
  .p pv11 [pv2,pv13,pv6581], .c 151, .c 3, .c 5,
]
private theorem h0271c16 : checkBlock 2224131 128 b0271c16 = true := by
  decide +kernel

private def b0271c17 : List Row := [
  .c 11, .c 3, .c 13, .c 1291, .c 3, .c 7, .c 17, .c 3, .c 37, .c 5, .c 3, .c 11, .c 7, .c 3,
  .c 5, .c 13, .c 3, .c 149, .c 107, .c 3, .c 797, .p pv2 [pv2,pv3,pv185369], .c 3, .c 17, .c 5,
  .c 3, .c 7, .p pv23 [pv2,pv3,pv5,pv37,pv167], .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv52963], .c 3,
  .c 233, .c 7, .c 3, .p pv3 [pv2,pv13,pv73,pv293], .p pv2 [pv2,pv3,pv123581], .c 3, .c 19, .c 5,
  .c 3, .c 13, .c 419, .c 3, .c 5, .c 37, .c 3, .c 7, .c 83, .c 3, .c 61,
  .p pv13 [pv2,pv3,pv7,pv13241], .c 3, .p pv2 [pv2,pv556123], .c 5, .c 3, .c 1039, .c 17, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv229,pv1619], .c 3, .c 131, .p pv5 [pv2,pv3,pv1931], .c 3,
  .p pv2 [pv2,pv7,pv53,pv1499], .c 11, .c 3, .c 7, .c 5, .c 3, .c 31, .c 683, .c 3, .c 5, .c 7,
  .c 3, .c 11, .c 1453, .c 3, .c 13, .c 1091, .c 3, .p pv3 [pv2,pv11,pv17,pv1487], .c 5, .c 3,
  .p pv7 [pv2,pv7,pv19,pv8363], .c 29, .c 3, .c 5, .p pv5 [pv2,pv3,pv83,pv1489], .c 3,
  .p pv2 [pv2,pv5,pv149,pv1493], .c 13, .c 3, .c 19, .c 7, .c 3, .c 23, .c 5, .c 3, .c 1069,
  .c 31, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv19,pv887], .c 3, .c 67, .c 17, .c 3, .c 7, .c 61,
  .c 3, .c 251, .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .p pv13 [pv2,pv3,pv101,pv3671], .c 3, .c 113,
  .p pv5 [pv2,pv3,pv92693], .c 3, .c 17, .c 271, .c 3,
]
private theorem h0271c17 : checkBlock 2224387 128 b0271c17 = true := by
  decide +kernel

private def b0271c18 : List Row := [
  .c 71, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .p pv11 [pv2,pv3,pv7,pv2207], .c 3,
  .p pv2 [pv2,pv5,pv41,pv2713], .c 7, .c 3, .p pv2 [pv2,pv1112333], .p pv2 [pv2,pv3,pv67,pv2767],
  .c 3, .c 11, .c 5, .c 3, .p pv7 [pv2,pv1112339], .p pv11 [pv2,pv3,pv5,pv18539], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv599,pv619], .c 3, .c 7, .c 1427, .c 3, .c 103, .c 37, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv556177], .c 193, .c 3, .c 5, .c 11, .c 3, .c 23, .c 359, .c 3, .c 101, .c 13,
  .c 3, .c 7, .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv7,pv5297], .c 3, .c 5, .c 7, .c 3, .c 1103,
  .p pv5 [pv2,pv3,pv46349], .c 3, .p pv2 [pv2,pv17,pv32717], .c 1021, .c 3,
  .p pv2 [pv2,pv1112381], .c 5, .c 3, .c 503, .c 653, .c 3, .c 5, .c 31, .c 3, .c 13, .c 11, .c 3,
  .c 163, .c 7, .c 3, .c 29, .c 5, .c 3, .c 109, .p pv13 [pv2,pv3,pv5,pv103], .c 3, .c 5, .c 13,
  .c 3, .c 1409, .c 23, .c 3, .c 7, .c 1163, .c 3, .c 757, .c 5, .c 3, .c 307, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv23,pv2687], .c 3, .c 17, .c 19, .c 3, .c 37, .c 11, .c 3, .c 61, .c 5, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv5,pv11,pv3371], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv52973], .c 3, .c 11,
  .c 7, .c 3, .c 79, .p pv3 [pv2,pv3,pv370813], .c 3, .c 1151, .c 5, .c 3, .c 97,
  .p pv2 [pv2,pv3,pv5,pv59,pv419], .c 3, .c 5, .p pv5 [pv2,pv3,pv2897],
]
private theorem h0271c18 : checkBlock 2224643 128 b0271c18 = true := by
  decide +kernel

private def b0271c19 : List Row := [
  .c 3, .c 7, .c 103, .c 3, .p pv2 [pv2,pv41,pv43,pv631], .c 17, .c 3, .c 127, .c 5, .c 3, .c 19,
  .c 37, .c 3, .c 5, .c 71, .c 3, .p pv11 [pv2,pv5,pv222493], .c 47, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv19,pv29,pv673], .c 3, .c 7, .c 5, .c 3, .c 43, .c 23, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv17,pv409], .c 13, .c 3, .c 29, .p pv7 [pv2,pv3,pv92707], .c 3, .c 139, .c 5,
  .c 3, .p pv2 [pv2,pv7,pv158927], .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv97,pv3823], .c 3,
  .p pv13 [pv2,pv5,pv222499], .c 53, .c 3, .c 23, .c 7, .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv59,pv2357], .c 17, .c 3, .c 5, .c 109, .c 3, .p pv2 [pv2,pv5,pv7,pv23,pv691],
  .c 317, .c 3, .c 7, .c 41, .c 3, .c 19, .c 5, .c 3, .p pv11 [pv2,pv1112519], .c 7, .c 3, .c 5,
  .c 11, .c 3, .p pv2 [pv2,pv5,pv44501], .p pv5 [pv2,pv3,pv19,pv3253], .c 3,
  .p pv3 [pv2,pv31,pv2243], .p pv3 [pv2,pv3,pv11,pv33713], .c 3, .p pv5 [pv2,pv7,pv17,pv9349],
  .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .p pv23 [pv2,pv3,pv7,pv26489], .c 3,
  .p pv3 [pv2,pv5,pv11,pv13,pv389], .c 7, .c 3, .c 31, .c 23, .c 3, .c 13, .c 5, .c 3, .c 53,
  .p pv13 [pv2,pv3,pv5,pv7417], .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv37,pv257], .c 3, .c 7, .c 11,
  .c 3, .c 313, .c 13, .c 3, .p pv2 [pv2,pv1112561], .c 5, .c 3, .c 739, .c 101, .c 3, .c 5,
  .c 67, .c 3, .c 29, .c 37, .c 3, .c 17, .c 31, .c 3, .c 7,
]
private theorem h0271c19 : checkBlock 2224899 128 b0271c19 = true := by
  decide +kernel

private def b0271c20 : List Row := [
  .c 5, .c 3, .p pv17 [pv2,pv13,pv23,pv61], .c 157, .c 3, .c 5, .c 7, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv107,pv1733], .c 3, .p pv3 [pv2,pv278147], .c 11, .c 3, .p pv5 [pv2,pv1112591],
  .c 5, .c 3, .c 443, .c 521, .c 3, .c 5, .c 13, .c 3, .c 11, .p pv3 [pv2,pv3,pv7,pv52981], .c 3,
  .c 43, .c 7, .c 3, .c 751, .c 5, .c 3, .c 61, .p pv13 [pv2,pv3,pv5,pv37087], .c 3, .c 5, .c 23,
  .c 3, .p pv13 [pv2,pv5,pv7,pv83,pv383], .p pv11 [pv2,pv3,pv17,pv101], .c 3, .c 7, .c 281, .c 3,
  .c 263, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 29, .c 3, .c 19,
  .p pv3 [pv2,pv3,pv13,pv47,pv607], .c 3, .c 11, .p pv2 [pv2,pv3,pv61813], .c 3, .c 23, .c 5,
  .c 3, .c 7, .c 227, .c 3, .c 5, .c 151, .c 3, .c 37, .c 7, .c 3, .c 131, .c 19, .c 3, .c 59,
  .c 5, .c 3, .c 47, .c 11, .c 3, .c 5, .c 17, .c 3, .c 7, .p pv2 [pv2,pv3,pv11,pv11239], .c 3,
  .c 13, .c 239, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv67,pv16607], .c 61, .c 3, .c 5, .c 727,
  .c 3, .c 17, .c 13, .c 3, .c 41, .c 569, .c 3, .c 7, .c 5, .c 3, .c 409,
  .p pv2 [pv2,pv3,pv5,pv7,pv10597], .c 3, .c 5, .c 7, .c 3, .p pv41 [pv2,pv5,pv111269], .c 233,
  .c 3, .p pv2 [pv2,pv107,pv10399], .p pv2 [pv2,pv3,pv11,pv23,pv733], .c 3,
  .p pv3 [pv2,pv13,pv823], .c 5, .c 3, .c 11, .p pv11 [pv2,pv3,pv5,pv3709], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv421,pv881], .c 3,
]
private theorem h0271c20 : checkBlock 2225155 128 b0271c20 = true := by
  decide +kernel

private def b0271c21 : List Row := [
  .c 23, .c 19, .c 3, .c 53, .c 7, .c 3, .c 643, .c 5, .c 3, .p pv2 [pv2,pv31,pv131,pv137], .c 13,
  .c 3, .c 5, .c 269, .c 3, .c 359, .c 11, .c 3, .c 7, .c 1433, .c 3, .c 17, .c 5, .c 3, .c 31,
  .c 7, .c 3, .c 5, .c 773, .c 3, .c 97, .p pv7 [pv2,pv3,pv67,pv173], .c 3, .c 853, .c 83, .c 3,
  .c 13, .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv31,pv2393], .c 3, .c 5, .c 47, .c 3,
  .p pv2 [pv2,pv5,pv4451], .c 7, .c 3, .c 179, .c 11, .c 3, .c 37, .c 5, .c 3, .c 617, .c 17,
  .c 3, .c 5, .c 19, .c 3, .c 7, .p pv2 [pv2,pv3,pv191,pv971], .c 3, .c 631, .c 59, .c 3,
  .p pv5 [pv2,pv11,pv101161], .c 5, .c 3, .c 23, .c 43, .c 3, .c 5, .p pv2 [pv2,pv3,pv6869], .c 3,
  .c 13, .p pv3 [pv2,pv3,pv41,pv83,pv109], .c 3, .p pv5 [pv2,pv7,pv71,pv2239],
  .p pv7 [pv2,pv3,pv97,pv239], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv1112789],
  .p pv11 [pv2,pv3,pv5,pv7,pv757], .c 3, .c 5, .c 7, .c 3, .c 47, .p pv11 [pv2,pv3,pv30911], .c 3,
  .c 11, .p pv3 [pv2,pv3,pv59,pv6287], .c 3, .c 19, .c 5, .c 3, .c 167, .c 673, .c 3, .c 5,
  .c 251, .c 3, .p pv2 [pv2,pv5,pv257,pv433], .c 17, .c 3, .p pv2 [pv2,pv13,pv85601], .c 7, .c 3,
  .c 1373, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv61,pv2027], .c 3, .c 229,
  .p pv5 [pv2,pv3,pv11,pv13,pv1297], .c 3, .c 7, .p pv2 [pv2,pv3,pv347,pv1069], .c 3, .c 11, .c 5,
]
private theorem h0271c21 : checkBlock 2225411 128 b0271c21 = true := by
  decide +kernel

private def b0271c22 : List Row := [
  .c 3, .c 859, .c 7, .c 3, .c 5, .c 863, .c 3, .p pv3 [pv2,pv5,pv43,pv647],
  .p pv2 [pv2,pv3,pv53,pv2333], .c 3, .c 23, .p pv13 [pv2,pv3,pv92737], .c 3, .c 449, .c 5, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv5,pv2473], .c 3, .c 5, .c 11, .c 3, .c 691, .c 7, .c 3, .c 13, .c 1229,
  .c 3, .c 43, .c 5, .c 3, .c 11, .c 821, .c 3, .c 5, .c 101, .c 3, .c 7, .c 13, .c 3,
  .p pv2 [pv2,pv79,pv14087], .p pv17 [pv2,pv3,pv7,pv26497], .c 3, .p pv3 [pv2,pv278219], .c 5,
  .c 3, .c 17, .c 113, .c 3, .c 5, .c 41, .c 3, .p pv2 [pv2,pv5,pv73,pv3049], .c 11, .c 3,
  .p pv5 [pv2,pv7,pv17,pv167], .c 23, .c 3, .c 7, .c 5, .c 3, .c 157,
  .p pv7 [pv2,pv3,pv5,pv7,pv3533], .c 3, .c 5, .c 7, .c 3, .c 89, .c 613, .c 3, .c 67, .c 37,
  .c 3, .c 1097, .c 5, .c 3, .p pv2 [pv2,pv7,pv173,pv919], .c 13, .c 3, .c 5, .c 17, .c 3, .c 19,
  .p pv17 [pv2,pv3,pv7,pv13249], .c 3, .c 29, .c 7, .c 3, .c 73, .c 5, .c 3, .c 41,
  .p pv2 [pv2,pv3,pv5,pv11,pv19,pv71], .c 3, .c 5, .c 509, .c 3, .c 11,
  .p pv29 [pv2,pv3,pv31,pv3989], .c 3, .c 7, .c 19, .c 3, .c 13, .c 5, .c 3,
  .p pv23 [pv2,pv17,pv3851], .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv28537], .c 3, .c 151, .c 31,
  .c 3, .c 683, .c 13, .c 3, .c 197, .c 5, .c 3, .c 7, .c 149, .c 3, .c 5, .c 23, .c 3, .c 71,
]
private theorem h0271c22 : checkBlock 2225667 128 b0271c22 = true := by
  decide +kernel

private def b0271c23 : List Row := [
  .c 7, .c 3, .c 11, .c 17, .c 3, .c 103, .c 5, .c 3, .c 101, .c 67, .c 3, .c 5, .c 53, .c 3,
  .c 7, .c 29, .c 3, .c 37, .p pv3 [pv2,pv3,pv7,pv52999], .c 3, .c 17, .c 5, .c 3,
  .p pv3 [pv2,pv139123], .c 11, .c 3, .c 5, .c 13, .c 3, .c 43, .c 19, .c 3, .c 113, .c 73, .c 3,
  .c 7, .c 5, .c 3, .p pv19 [pv2,pv109,pv10211], .p pv11 [pv2,pv3,pv5,pv7,pv53], .c 3, .c 5, .c 7,
  .c 3, .c 29, .c 41, .c 3, .c 31, .p pv2 [pv2,pv3,pv353,pv1051], .c 3, .p pv5 [pv2,pv1113011],
  .c 5, .c 3, .c 13, .c 17, .c 3, .c 5, .c 11, .c 3, .p pv7 [pv2,pv5,pv19,pv29,pv101], .c 883,
  .c 3, .c 457, .c 7, .c 3, .c 53, .c 5, .c 3, .c 11, .c 47, .c 3, .c 5, .c 43, .c 3, .c 1171,
  .c 61, .c 3, .c 7, .c 31, .c 3, .c 131, .c 5, .c 3, .p pv3 [pv2,pv278261], .c 7, .c 3, .c 5,
  .c 19, .c 3, .c 23, .c 11, .c 3, .c 13, .c 229, .c 3, .c 137, .c 5, .c 3, .c 7, .c 733, .c 3,
  .c 5, .c 29, .c 3, .p pv2 [pv2,pv5,pv222613], .c 7, .c 3, .p pv3 [pv2,pv11,pv41,pv617], .c 103,
  .c 3, .c 83, .c 5, .c 3, .p pv2 [pv2,pv556537], .p pv7 [pv2,pv3,pv5,pv17,pv97], .c 3, .c 5,
  .c 89, .c 3, .c 7, .p pv2 [pv2,pv3,pv371027], .c 3, .c 17, .c 11, .c 3, .c 19, .c 5, .c 3,
]
private theorem h0271c23 : checkBlock 2225923 128 b0271c23 = true := by
  decide +kernel

private def b0271c24 : List Row := [
  .c 37, .c 1117, .c 3, .c 5, .c 409, .c 3, .c 11, .c 23, .c 3, .p pv2 [pv2,pv7,pv43],
  .p pv23 [pv2,pv3,pv13,pv28541], .c 3, .c 7, .c 5, .c 3, .c 67, .c 13, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv79,pv1409], .c 179, .c 3, .p pv2 [pv2,pv83,pv13411],
  .p pv2 [pv2,pv3,pv185519], .c 3, .c 521, .c 5, .c 3, .c 23, .p pv7 [pv2,pv3,pv5,pv773], .c 3,
  .c 5, .c 59, .c 3, .p pv2 [pv2,pv5,pv13,pv137], .c 37, .c 3, .c 11, .c 7, .c 3, .c 13, .c 5,
  .c 3, .c 17, .c 349, .c 3, .c 5, .c 167, .c 3, .c 73, .p pv3 [pv2,pv3,pv43,pv8629], .c 3, .c 7,
  .c 13, .c 3, .p pv2 [pv2,pv556573], .c 5, .c 3, .c 79, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv19,pv59,pv331], .c 3, .p pv19 [pv2,pv5,pv127,pv1753],
  .p pv5 [pv2,pv3,pv11,pv937], .c 3, .c 61, .p pv3 [pv2,pv3,pv53,pv7001], .c 3, .c 11, .c 5, .c 3,
  .c 7, .c 23, .c 3, .c 5, .c 17, .c 3, .c 13, .c 7, .c 3, .c 71, .c 107, .c 3,
  .p pv3 [pv2,pv347,pv401], .c 5, .c 3, .c 29, .c 283, .c 3, .c 5, .c 11, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv185531], .c 3, .c 23, .c 383, .c 3, .p pv11 [pv2,pv19,pv41,pv1429], .c 5,
  .c 3, .c 11, .c 257, .c 3, .c 5, .c 947, .c 3, .c 19, .p pv2 [pv2,pv3,pv179,pv691], .c 3,
  .p pv5 [pv2,pv7,pv13,pv941], .p pv37 [pv2,pv3,pv92767], .c 3, .c 7, .c 5, .c 3, .c 13,
  .p pv11 [pv2,pv3,pv5,pv7,pv19,pv31], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv222643], .c 11,
]
private theorem h0271c24 : checkBlock 2226179 128 b0271c24 = true := by
  decide +kernel

private def b0271c25 : List Row := [
  .c 3, .c 47, .c 17, .c 3, .c 1153, .c 5, .c 3, .c 311, .c 31, .c 3, .c 5, .c 79, .c 3,
  .p pv2 [pv2,pv5,pv111323], .p pv3 [pv2,pv3,pv7,pv7573], .c 3, .p pv2 [pv2,pv11,pv101203], .c 7,
  .c 3, .c 17, .c 5, .c 3, .p pv13 [pv2,pv1113239], .c 181, .c 3, .c 5, .c 191, .c 3, .c 587,
  .p pv2 [pv2,pv3,pv23,pv2689], .c 3, .c 7, .c 11, .c 3, .c 971, .c 5, .c 3,
  .p pv2 [pv2,pv556627], .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv185543], .c 3, .c 11, .c 13, .c 3,
  .p pv5 [pv2,pv277,pv4019], .p pv11 [pv2,pv3,pv859], .c 3, .c 29, .c 5, .c 3, .c 7, .c 17, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv7,pv41,pv431], .c 3, .c 103, .c 7, .c 3, .p pv2 [pv2,pv556639], .c 337,
  .c 3, .c 107, .c 5, .c 3, .p pv3 [pv2,pv278321], .p pv2 [pv2,pv3,pv5,pv74219], .c 3, .c 5,
  .c 1039, .c 3, .c 7, .c 43, .c 3, .c 11, .c 367, .c 3, .p pv3 [pv2,pv17,pv4093], .c 5, .c 3,
  .c 241, .c 13, .c 3, .c 5, .c 23, .c 3, .c 67, .p pv19 [pv2,pv3,pv185551], .c 3,
  .p pv5 [pv2,pv7,pv39761], .p pv3 [pv2,pv3,pv123701], .c 3, .c 7, .c 5, .c 3, .c 19, .c 11, .c 3,
  .c 5, .c 7, .c 3, .c 83, .c 17, .c 3, .p pv11 [pv2,pv73,pv101,pv151], .c 29, .c 3, .c 11, .c 5,
  .c 3, .p pv2 [pv2,pv7,pv22721], .c 137, .c 3, .c 5, .c 19, .c 3, .c 307,
  .p pv5 [pv2,pv3,pv7,pv47], .c 3, .c 17, .c 7, .c 3, .c 61, .c 5, .c 3, .c 53,
]
private theorem h0271c25 : checkBlock 2226435 128 b0271c25 = true := by
  decide +kernel

private def b0271c26 : List Row := [
  .c 89, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv7,pv3181], .c 877, .c 3, .c 7, .c 643, .c 3,
  .p pv3 [pv2,pv43,pv6473], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 1069, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv97,pv1913], .c 3, .c 919, .c 1279, .c 3, .c 19, .c 5, .c 3, .c 7, .c 41, .c 3,
  .c 5, .c 13, .c 3, .c 31, .c 7, .c 3, .p pv5 [pv2,pv47,pv23689], .p pv11 [pv2,pv3,pv23,pv2017],
  .c 3, .c 71, .c 5, .c 3, .c 17, .c 19, .c 3, .c 5, .p pv19 [pv2,pv3,pv371131], .c 3, .c 7,
  .p pv11 [pv2,pv3,pv31,pv41,pv73], .c 3, .c 151, .c 631, .c 3, .c 277, .c 5, .c 3, .c 13,
  .p pv19 [pv2,pv3,pv5,pv199,pv373], .c 3, .c 5, .p pv13 [pv2,pv3,pv1933], .c 3, .c 263, .c 29,
  .c 3, .c 1303, .c 11, .c 3, .c 7, .c 5, .c 3, .p pv19 [pv2,pv19,pv58601], .c 43, .c 3, .c 5,
  .c 7, .c 3, .c 11, .p pv2 [pv2,pv3,pv29,pv79], .c 3, .c 19, .p pv2 [pv2,pv3,pv371143], .c 3,
  .c 1009, .c 5, .c 3, .c 89, .c 479, .c 3, .c 5, .c 359, .c 3, .c 17, .c 23, .c 3, .c 13, .c 7,
  .c 3, .p pv2 [pv2,pv556723], .c 5, .c 3, .p pv2 [pv2,pv17,pv65497], .c 53, .c 3, .c 5, .c 47,
  .c 3, .p pv7 [pv2,pv5,pv7,pv29,pv1097], .c 13, .c 3, .c 7, .c 37, .c 3, .p pv2 [pv2,pv1113461],
  .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv92789], .c 3, .p pv2 [pv2,pv5,pv111347],
  .p pv3 [pv2,pv3,pv123719], .c 3,
]
private theorem h0271c26 : checkBlock 2226691 128 b0271c26 = true := by
  decide +kernel

private def b0271c27 : List Row := [
  .c 31, .c 17, .c 3, .p pv29 [pv2,pv7,pv13,pv19,pv23], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .c 1249, .c 3, .c 19, .c 7, .c 3, .c 431, .c 109, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv61,pv9127], .c 13, .c 3, .c 5, .c 29, .c 3, .c 7, .p pv3 [pv2,pv3,pv239,pv1553],
  .c 3, .c 53, .c 19, .c 3, .c 43, .c 5, .c 3, .p pv2 [pv2,pv1113509], .c 23, .c 3, .c 5, .c 11,
  .c 3, .p pv7 [pv2,pv5,pv13,pv37,pv463], .p pv5 [pv2,pv3,pv30931], .c 3, .c 499, .c 1061, .c 3,
  .c 7, .c 5, .c 3, .c 11, .c 17, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv11,pv53,pv191],
  .p pv3 [pv2,pv3,pv371177], .c 3, .c 23, .c 13, .c 3, .c 59, .c 5, .c 3, .c 41, .c 241, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv123727], .c 3, .c 461, .c 11, .c 3, .c 227, .c 7, .c 3, .c 149, .c 5,
  .c 3, .p pv2 [pv2,pv13,pv42829], .c 827, .c 3, .c 5, .c 113, .c 3, .c 13, .c 19, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv71,pv1307], .c 3, .c 31, .c 5, .c 3, .c 83, .c 7, .c 3, .c 5, .c 13, .c 3,
  .c 101, .c 17, .c 3, .c 73, .c 11, .c 3, .p pv2 [pv2,pv7,pv257,pv619], .c 5, .c 3, .c 7, .c 29,
  .c 3, .c 5, .c 809, .c 3, .c 11, .c 7, .c 3, .c 17, .c 47, .c 3, .p pv3 [pv2,pv11,pv25309],
  .c 5, .c 3, .c 13, .p pv17 [pv2,pv3,pv5,pv29],
]
private theorem h0271c27 : checkBlock 2226947 128 b0271c27 = true := by
  decide +kernel

private def b0271c28 : List Row := [
  .c 3, .c 5, .p pv3 [pv2,pv3,pv281,pv1321], .c 3, .c 7, .p pv2 [pv2,pv3,pv13,pv4759], .c 3,
  .c 97, .c 53, .c 3, .p pv5 [pv2,pv83,pv13417], .c 5, .c 3, .c 29,
  .p pv3 [pv2,pv3,pv5,pv73,pv113], .c 3, .c 5, .c 19, .c 3, .c 239, .c 41, .c 3, .c 11, .c 937,
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv11,pv29,pv3491], .p pv59 [pv2,pv3,pv5,pv7,pv5303], .c 3,
  .c 5, .c 7, .c 3, .c 43, .p pv29 [pv2,pv3,pv17,pv53,pv103], .c 3, .c 13, .c 167, .c 3, .c 47,
  .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv22273], .c 13, .c 3,
  .p pv2 [pv2,pv17,pv109,pv601], .c 7, .c 3, .c 11, .c 5, .c 3, .c 31,
  .p pv11 [pv2,pv3,pv5,pv23,pv269], .c 3, .c 5, .p pv3 [pv2,pv3,pv37,pv79,pv127], .c 3, .c 1193,
  .p pv2 [pv2,pv3,pv19,pv9769], .c 3, .c 7, .p pv2 [pv2,pv3,pv4583], .c 3, .c 23, .c 5, .c 3,
  .c 271, .c 7, .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv13921], .c 37, .c 3,
  .p pv5 [pv2,pv23,pv41,pv1181], .p pv17 [pv2,pv3,pv11,pv13,pv59], .c 3, .c 821, .c 5, .c 3, .c 7,
  .c 13, .c 3, .c 5, .c 859, .c 3, .c 17, .c 7, .c 3, .p pv2 [pv2,pv556849],
  .p pv3 [pv2,pv3,pv371233], .c 3, .c 29, .c 5, .c 3, .p pv3 [pv2,pv17,pv19,pv431], .c 97, .c 3,
  .c 5, .p pv23 [pv2,pv3,pv92809], .c 3, .c 7, .c 11, .c 3, .c 19, .p pv19 [pv2,pv3,pv7,pv8839],
  .c 3, .c 13, .c 5, .c 3, .p pv7 [pv2,pv1113719], .p pv7 [pv2,pv3,pv5,pv9281], .c 3, .c 5,
  .c 761, .c 3, .p pv2 [pv2,pv5,pv44549], .c 127, .c 3, .c 523,
]
private theorem h0271c28 : checkBlock 2227203 128 b0271c28 = true := by
  decide +kernel

private def b0271c29 : List Row := [
  .c 13, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv556867], .c 47, .c 3, .c 5, .c 7, .c 3, .c 23,
  .c 71, .c 3, .c 281, .c 11, .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv7,pv13,pv12239],
  .p pv2 [pv2,pv3,pv5,pv11], .c 3, .c 5, .p pv2 [pv2,pv3,pv371251], .c 3, .c 11,
  .p pv5 [pv2,pv3,pv7,pv13259], .c 3, .c 1129, .c 7, .c 3, .c 829, .c 5, .c 3, .c 43,
  .p pv11 [pv2,pv3,pv5,pv41,pv1811], .c 3, .c 5, .c 13, .c 3, .c 19, .p pv3 [pv2,pv3,pv371257],
  .c 3, .c 7, .c 67, .c 3, .c 1381, .c 5, .c 3, .c 317, .c 7, .c 3, .c 5, .c 31, .c 3, .c 41,
  .c 23, .c 3, .c 11, .c 19, .c 3, .p pv5 [pv2,pv7,pv159113], .c 5, .c 3, .c 7,
  .p pv23 [pv2,pv3,pv5,pv53,pv467], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv23,pv1153], .c 3,
  .p pv3 [pv2,pv5,pv5569], .c 7, .c 3, .p pv5 [pv2,pv29,pv193,pv199], .p pv7 [pv2,pv3,pv10313],
  .c 3, .c 167, .c 5, .c 3, .c 23, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv123757], .c 3, .c 7,
  .c 107, .c 3, .c 83, .p pv13 [pv2,pv3,pv7,pv7577], .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv34807], .p pv2 [pv2,pv3,pv5,pv14851], .c 3, .c 5, .p pv5 [pv2,pv3,pv101,pv919],
  .c 3, .p pv2 [pv2,pv5,pv31,pv3593], .c 17, .c 3, .c 13, .p pv13 [pv2,pv3,pv73,pv2543], .c 3,
  .c 7, .c 5, .c 3, .c 293, .c 599, .c 3, .c 5, .c 7, .c 3, .c 31, .c 13, .c 3, .c 17, .c 149,
  .c 3, .c 151, .c 5, .c 3, .c 11, .c 23, .c 3,
]
private theorem h0271c29 : checkBlock 2227459 128 b0271c29 = true := by
  decide +kernel

private def b0271c30 : List Row := [
  .c 5, .p pv5 [pv2,pv3,pv20627], .c 3, .c 79, .p pv2 [pv2,pv3,pv7,pv29,pv31,pv59], .c 3,
  .p pv5 [pv2,pv1113863], .c 7, .c 3, .c 37, .c 5, .c 3, .p pv2 [pv2,pv211,pv5279], .c 73, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv371291], .c 3, .c 29, .c 11, .c 3, .c 7, .c 89, .c 3,
  .p pv2 [pv2,pv379,pv2939], .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv41,pv283],
  .c 3, .c 59, .c 353, .c 3, .c 43, .p pv2 [pv2,pv3,pv19,pv3257], .c 3, .c 769, .c 5, .c 3, .c 7,
  .p pv37 [pv2,pv3,pv5,pv47,pv79], .c 3, .c 5, .c 19, .c 3, .c 1429, .c 7, .c 3, .c 41, .c 11,
  .c 3, .c 13, .c 5, .c 3, .c 479, .p pv3 [pv2,pv3,pv5,pv11,pv43,pv157], .c 3, .c 5, .c 1237,
  .c 3, .c 7, .p pv5 [pv2,pv3,pv61,pv2029], .c 3, .c 47, .c 13, .c 3, .p pv2 [pv2,pv11,pv4603],
  .c 5, .c 3, .p pv2 [pv2,pv41,pv101,pv269], .c 823, .c 3, .c 5, .c 17, .c 3,
  .p pv7 [pv2,pv5,pv222787], .c 43, .c 3, .c 31, .c 79, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv13,pv10711], .c 271, .c 3, .c 5, .c 7, .c 3, .c 13, .c 61, .c 3, .c 11, .c 71,
  .c 3, .p pv3 [pv2,pv278489], .c 5, .c 3, .p pv7 [pv2,pv7,pv11,pv17,pv23,pv37], .c 19, .c 3,
  .c 5, .c 13, .c 3, .c 547, .c 257, .c 3, .c 89, .c 7, .c 3, .p pv5 [pv2,pv1113971], .c 5, .c 3,
  .c 211, .c 11, .c 3, .c 5, .c 1361, .c 3, .c 53, .p pv3 [pv2,pv3,pv11,pv33757], .c 3, .c 7,
  .c 17,
]
private theorem h0271c30 : checkBlock 2227715 128 b0271c30 = true := by
  decide +kernel

private def b0271c31 : List Row := [
  .c 3, .c 11, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 23, .c 3, .c 1031, .c 97, .c 3, .c 19,
  .c 1187, .c 3, .c 17, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv23,pv3229], .c 3, .c 5, .c 11,
  .c 3, .c 113, .c 7, .c 3, .p pv2 [pv2,pv89,pv12517], .c 37, .c 3, .c 23, .c 5, .c 3, .c 11,
  .c 29, .c 3, .c 5, .c 163, .c 3, .c 7, .p pv2 [pv2,pv3,pv83,pv2237], .c 3, .c 13, .c 283, .c 3,
  .c 31, .c 5, .c 3, .c 109, .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv59,pv1049], .c 3,
  .p pv13 [pv2,pv5,pv27851], .c 11, .c 3, .c 347, .p pv7 [pv2,pv3,pv17,pv43,pv127], .c 3, .c 7,
  .c 5, .c 3, .c 29, .p pv11 [pv2,pv3,pv5,pv7,pv1061], .c 3, .c 5, .c 7, .c 3, .c 19,
  .p pv5 [pv2,pv3,pv15473], .c 3, .p pv2 [pv2,pv11,pv79,pv641], .p pv3 [pv2,pv3,pv371353], .c 3,
  .p pv2 [pv2,pv13,pv17,pv71], .c 5, .c 3, .c 47, .c 43, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv263,pv353], .c 3, .c 379, .p pv5 [pv2,pv3,pv7,pv53051], .c 3, .c 61, .c 7,
  .c 3, .p pv3 [pv2,pv67,pv4157], .c 5, .c 3, .p pv13 [pv2,pv491,pv2269], .c 13, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv123787], .c 3, .c 11, .c 17, .c 3, .c 7, .c 73, .c 3,
  .p pv5 [pv2,pv11,pv101281], .c 5, .c 3, .p pv2 [pv2,pv277,pv2011], .c 7, .c 3, .c 5, .c 239,
  .c 3, .p pv3 [pv2,pv5,pv13,pv857], .c 199, .c 3, .c 17, .p pv19 [pv2,pv3,pv61,pv761], .c 3,
  .c 13, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv12379], .c 3, .c 5,
]
private theorem h0271c31 : checkBlock 2227971 128 b0271c31 = true := by
  decide +kernel

def rows0271 : List Row :=
  b0271c00 ++ b0271c01 ++ b0271c02 ++ b0271c03 ++ b0271c04 ++ b0271c05 ++ b0271c06 ++ b0271c07 ++
  b0271c08 ++ b0271c09 ++ b0271c10 ++ b0271c11 ++ b0271c12 ++ b0271c13 ++ b0271c14 ++ b0271c15 ++
  b0271c16 ++ b0271c17 ++ b0271c18 ++ b0271c19 ++ b0271c20 ++ b0271c21 ++ b0271c22 ++ b0271c23 ++
  b0271c24 ++ b0271c25 ++ b0271c26 ++ b0271c27 ++ b0271c28 ++ b0271c29 ++ b0271c30 ++ b0271c31

theorem checked0271 : checkBlock 2220035 4096 rows0271 = true :=
  checkBlock_append h0271c00 (
    checkBlock_append h0271c01 (
    checkBlock_append h0271c02 (
    checkBlock_append h0271c03 (
    checkBlock_append h0271c04 (
    checkBlock_append h0271c05 (
    checkBlock_append h0271c06 (
    checkBlock_append h0271c07 (
    checkBlock_append h0271c08 (
    checkBlock_append h0271c09 (
    checkBlock_append h0271c10 (
    checkBlock_append h0271c11 (
    checkBlock_append h0271c12 (
    checkBlock_append h0271c13 (
    checkBlock_append h0271c14 (
    checkBlock_append h0271c15 (
    checkBlock_append h0271c16 (
    checkBlock_append h0271c17 (
    checkBlock_append h0271c18 (
    checkBlock_append h0271c19 (
    checkBlock_append h0271c20 (
    checkBlock_append h0271c21 (
    checkBlock_append h0271c22 (
    checkBlock_append h0271c23 (
    checkBlock_append h0271c24 (
    checkBlock_append h0271c25 (
    checkBlock_append h0271c26 (
    checkBlock_append h0271c27 (
    checkBlock_append h0271c28 (
    checkBlock_append h0271c29 (
    checkBlock_append h0271c30 (
    h0271c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
