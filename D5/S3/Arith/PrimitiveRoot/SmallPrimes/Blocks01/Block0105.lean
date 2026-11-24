/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0105
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0105.checked0105
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table014
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table016
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table019
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table024
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table033
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table051
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table103

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0105c00 : List Row := [
  .c 3, .c 5, .c 7, .c 3, .c 13, .c 107, .c 3, .c 23, .c 257, .c 3, .c 17, .c 5, .c 3, .c 11,
  .c 787, .c 3, .c 5, .c 13, .c 3, .c 193, .c 157, .c 3, .c 419, .c 7, .c 3, .c 37, .c 5, .c 3,
  .c 31, .c 41, .c 3, .c 5, .c 29, .c 3, .c 79, .c 11, .c 3, .c 7, .p pv3 [pv2,pv3,pv47791], .c 3,
  .c 53, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv29,pv103], .c 3, .c 353, .c 19,
  .c 3, .p pv2 [pv2,pv11,pv39103], .c 23, .c 3, .c 263, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5,
  .c 37, .c 3, .p pv11 [pv2,pv5,pv86029], .c 7, .c 3, .p pv3 [pv2,pv53,pv2029], .c 11, .c 3,
  .c 41, .c 5, .c 3, .p pv2 [pv2,pv215077], .p pv37 [pv2,pv3,pv5,pv11,pv79], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv71693], .c 3, .c 7, .p pv2 [pv2,pv3,pv143387], .c 3, .c 13, .c 173, .c 3,
  .p pv2 [pv2,pv11,pv19553], .c 5, .c 3, .c 19, .p pv2 [pv2,pv3,pv5,pv13,pv1103], .c 3, .c 5,
  .c 67, .c 3, .p pv7 [pv2,pv5,pv17207], .c 13, .c 3, .p pv2 [pv2,pv7,pv30727], .c 103, .c 3,
  .c 7, .c 5, .c 3, .p pv3 [pv2,pv53773], .c 433, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv43019], .p pv3 [pv2,pv3,pv47,pv113], .c 3, .c 11, .c 79, .c 3,
  .p pv3 [pv2,pv13,pv8273], .c 5, .c 3, .p pv13 [pv2,pv7,pv11,pv37,pv151], .c 29, .c 3, .c 5,
  .c 23, .c 3, .c 863, .p pv2 [pv2,pv3,pv7,pv10243], .c 3, .p pv3 [pv2,pv3361],
]
private theorem h0105c00 : checkBlock 860163 128 b0105c00 = true := by
  decide +kernel

private def b0105c01 : List Row := [
  .c 7, .c 3, .p pv5 [pv2,pv281,pv1531], .c 5, .c 3, .c 47, .c 11, .c 3, .c 5, .c 313, .c 3,
  .p pv3 [pv2,pv5,pv7,pv439], .c 593, .c 3, .c 7, .c 71, .c 3, .c 11, .c 5, .c 3, .c 29, .c 7,
  .c 3, .c 5, .c 31, .c 3, .c 811, .c 43, .c 3, .c 163, .p pv3 [pv2,pv3,pv143413], .c 3, .c 13,
  .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv1721], .c 7, .c 3,
  .p pv2 [pv2,pv17,pv25309], .c 13, .c 3, .p pv3 [pv2,pv26891], .c 5, .c 3, .c 11, .c 307, .c 3,
  .c 5, .c 61, .c 3, .c 7, .p pv2 [pv2,pv3,pv71711], .c 3, .c 311, .c 131, .c 3,
  .p pv5 [pv2,pv587,pv733], .c 5, .c 3, .c 41, .c 167, .c 3, .c 5, .c 17, .c 3, .c 13, .c 11,
  .c 3, .c 19, .p pv17 [pv2,pv3,pv23,pv1559], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv430289],
  .p pv13 [pv2,pv3,pv5,pv7,pv683], .c 3, .c 5, .c 7, .c 3, .c 17, .p pv5 [pv2,pv3,pv17929], .c 3,
  .c 73, .p pv11 [pv2,pv3,pv15937], .c 3, .c 283, .c 5, .c 3, .p pv3 [pv2,pv7,pv17,pv113], .c 241,
  .c 3, .c 5, .c 47, .c 3, .c 101, .p pv5 [pv2,pv3,pv7,pv31,pv661], .c 3, .c 83, .c 7, .c 3,
  .c 29, .c 5, .c 3, .c 13, .p pv43 [pv2,pv3,pv5,pv11,pv163], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv191,pv751], .c 3, .c 11, .c 31, .c 3, .c 7, .c 17, .c 3,
  .p pv5 [pv2,pv11,pv19,pv29,pv71], .c 5, .c 3, .c 211, .c 7, .c 3,
]
private theorem h0105c01 : checkBlock 860419 128 b0105c01 = true := by
  decide +kernel

private def b0105c02 : List Row := [
  .c 5, .c 853, .c 3, .c 19, .c 23, .c 3, .c 461, .p pv13 [pv2,pv3,pv43,pv139], .c 3, .c 17, .c 5,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv19,pv151], .c 3, .c 5, .c 431, .c 3, .c 47, .c 7, .c 3, .c 11,
  .c 19, .c 3, .c 491, .c 5, .c 3, .c 23, .c 37, .c 3, .c 5, .c 881, .c 3, .c 7, .c 13, .c 3,
  .p pv2 [pv2,pv31,pv13883], .c 29, .c 3, .p pv3 [pv2,pv23,pv2339], .c 5, .c 3,
  .p pv7 [pv2,pv47,pv9157], .c 11, .c 3, .c 5, .c 673, .c 3, .c 61, .c 53, .c 3, .c 31,
  .p pv2 [pv2,pv3,pv17,pv29,pv97], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv215197],
  .p pv3 [pv2,pv3,pv5,pv7,pv4099], .c 3, .c 5, .c 7, .c 3, .c 131, .c 163, .c 3, .c 29,
  .p pv7 [pv2,pv3,pv13,pv31,pv89], .c 3, .p pv2 [pv2,pv17,pv12659], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv61487], .c 13, .c 3, .c 5, .c 11, .c 3, .c 157, .c 19, .c 3, .c 191, .c 7,
  .c 3, .p pv2 [pv2,pv37,pv11633], .c 5, .c 3, .c 11, .c 151, .c 3, .c 5, .c 389, .c 3,
  .p pv2 [pv2,pv5,pv7,pv11,pv13,pv43], .c 17, .c 3, .c 7, .c 59, .c 3, .c 13, .c 5, .c 3, .c 37,
  .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv283], .c 3, .p pv2 [pv2,pv5,pv19,pv23,pv197], .c 11,
  .c 3, .c 17, .c 13, .c 3, .c 43, .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv28697], .c 3, .c 5,
  .p pv13 [pv2,pv3,pv7,pv37,pv277], .c 3, .p pv3 [pv2,pv5,pv21523], .c 7, .c 3,
  .p pv5 [pv2,pv11,pv39133], .p pv7 [pv2,pv3,pv19,pv59],
]
private theorem h0105c02 : checkBlock 860675 128 b0105c02 = true := by
  decide +kernel

private def b0105c03 : List Row := [
  .c 3, .c 127, .c 5, .c 3, .p pv2 [pv2,pv13,pv33113], .p pv2 [pv2,pv3,pv5,pv4783], .c 3, .c 5,
  .c 19, .c 3, .c 7, .c 37, .c 3, .p pv2 [pv2,pv215239], .c 11, .c 3, .c 31, .c 5, .c 3,
  .p pv3 [pv2,pv107621], .p pv2 [pv2,pv3,pv5,pv11,pv2609], .c 3, .c 5, .c 13, .c 3, .c 11, .c 349,
  .c 3, .c 59, .c 43, .c 3, .c 7, .c 5, .c 3, .c 17, .p pv13 [pv2,pv3,pv5,pv7,pv41], .c 3, .c 5,
  .c 7, .c 3, .c 227, .p pv2 [pv2,pv3,pv23917], .c 3, .c 67, .p pv2 [pv2,pv3,pv143503], .c 3,
  .c 19, .c 5, .c 3, .c 13, .p pv29 [pv2,pv3,pv5,pv1063], .c 3, .c 5,
  .p pv13 [pv2,pv3,pv11,pv593], .c 3, .c 41, .p pv2 [pv2,pv3,pv7,pv13,pv19,pv83], .c 3, .c 11,
  .c 7, .c 3, .p pv2 [pv2,pv167,pv1289], .c 5, .c 3, .p pv2 [pv2,pv11,pv39139], .c 19, .c 3, .c 5,
  .c 17, .c 3, .c 149, .c 199, .c 3, .c 7, .p pv7 [pv2,pv3,pv143513], .c 3,
  .p pv2 [pv2,pv41,pv10501], .c 5, .c 3, .p pv3 [pv2,pv71,pv379], .c 7, .c 3, .c 5, .c 23, .c 3,
  .c 17, .c 919, .c 3, .c 13, .p pv11 [pv2,pv3,pv73,pv983], .c 3, .c 11, .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv13,pv23], .c 3, .c 5, .c 293, .c 3, .p pv2 [pv2,pv5,pv86113], .c 7, .c 3,
  .c 19, .p pv2 [pv2,pv3,pv37,pv431], .c 3, .c 23, .c 5, .c 3, .c 31, .c 67, .c 3, .c 5, .c 11,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv143527], .c 3, .p pv5 [pv2,pv23,pv97,pv193], .c 17, .c 3, .c 113,
  .c 5, .c 3, .c 11, .c 47, .c 3, .c 5,
]
private theorem h0105c03 : checkBlock 860931 128 b0105c03 = true := by
  decide +kernel

private def b0105c04 : List Row := [
  .c 127, .c 3, .p pv7 [pv2,pv5,pv11,pv7829], .c 277, .c 3, .c 53,
  .p pv19 [pv2,pv3,pv13,pv61,pv181], .c 3, .c 7, .c 5, .c 3, .c 109, .c 13, .c 3, .c 5, .c 7,
  .c 3, .p pv2 [pv2,pv5,pv17,pv149], .c 11, .c 3, .c 101, .c 821, .c 3, .c 601, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv227,pv271], .c 359, .c 3, .c 5, .c 43, .c 3, .c 19, .c 89, .c 3, .c 373, .c 7,
  .c 3, .c 13, .c 5, .c 3, .c 229, .c 17, .c 3, .c 5, .c 887, .c 3, .c 23, .c 661, .c 3, .c 7,
  .c 11, .c 3, .p pv2 [pv2,pv163,pv1321], .c 5, .c 3, .p pv2 [pv2,pv430649], .c 7, .c 3, .c 5,
  .c 653, .c 3, .c 11, .c 659, .c 3, .p pv2 [pv2,pv215329], .c 137, .c 3, .c 37, .c 5, .c 3, .c 7,
  .c 829, .c 3, .c 5, .c 79, .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv19,pv1193], .c 367, .c 3,
  .p pv3 [pv2,pv67,pv1607], .c 5, .c 3, .c 193, .p pv11 [pv2,pv3,pv5,pv37,pv97], .c 3, .c 5,
  .c 13, .c 3, .c 7, .c 17, .c 3, .c 11, .c 181, .c 3, .c 139, .c 5, .c 3, .c 103,
  .p pv3 [pv2,pv3,pv5,pv17,pv563], .c 3, .c 5, .c 31, .c 3, .c 233, .c 19, .c 3, .c 17, .c 53,
  .c 3, .c 7, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 7, .c 3, .c 89,
  .p pv5 [pv2,pv3,pv11,pv13,pv251], .c 3, .p pv2 [pv2,pv215359], .p pv3 [pv2,pv3,pv143573], .c 3,
]
private theorem h0105c04 : checkBlock 861187 128 b0105c04 = true := by
  decide +kernel

private def b0105c05 : List Row := [
  .c 11, .c 5, .c 3, .c 223, .c 41, .c 3, .c 5, .c 83, .c 3, .c 577, .c 47, .c 3, .c 379, .c 7,
  .c 3, .c 73, .c 5, .c 3, .c 19, .c 197, .c 3, .c 5, .c 11, .c 3,
  .p pv7 [pv2,pv5,pv7,pv31,pv397], .p pv7 [pv2,pv3,pv17,pv41,pv103], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv11,pv19,pv229], .c 3, .c 29, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 19, .c 3,
  .c 31, .c 13, .c 3, .c 179, .c 701, .c 3, .c 41, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv83,pv173], .c 3, .c 5, .p pv7 [pv2,pv3,pv7,pv73,pv281], .c 3,
  .p pv11 [pv2,pv5,pv17231], .c 7, .c 3, .c 23, .p pv3 [pv2,pv3,pv143593], .c 3,
  .p pv2 [pv2,pv13,pv2549], .c 5, .c 3, .c 431, .p pv7 [pv2,pv3,pv5,pv3191], .c 3, .c 5, .c 17,
  .c 3, .c 7, .c 31, .c 3, .c 131, .p pv2 [pv2,pv3,pv7,pv13,pv263], .c 3, .c 19, .c 5, .c 3,
  .p pv7 [pv2,pv430799], .c 13, .c 3, .c 5, .c 269, .c 3, .c 17, .p pv2 [pv2,pv3,pv19,pv3779],
  .c 3, .p pv5 [pv2,pv7,pv157], .c 11, .c 3, .c 7, .c 5, .c 3, .c 593, .c 19, .c 3, .c 5, .c 7,
  .c 3, .c 11, .c 463, .c 3, .p pv5 [pv2,pv430823], .c 23, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv61547], .c 139, .c 3, .c 5, .c 149, .c 3, .c 107, .c 353, .c 3, .c 29, .c 7,
  .c 3, .c 251, .c 5, .c 3, .c 313, .p pv2 [pv2,pv3,pv5,pv28723], .c 3, .c 5, .c 41,
]
private theorem h0105c05 : checkBlock 861443 128 b0105c05 = true := by
  decide +kernel

private def b0105c06 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv7,pv1231], .p pv3 [pv2,pv3,pv143617], .c 3, .c 7, .c 337, .c 3, .c 17,
  .c 5, .c 3, .p pv17 [pv2,pv11,pv13,pv23,pv131], .c 7, .c 3, .c 5, .c 53, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv79,pv101], .c 3, .c 509, .p pv7 [pv2,pv3,pv31,pv41,pv113], .c 3,
  .p pv7 [pv2,pv7,pv61553], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 13, .c 3,
  .p pv3 [pv2,pv5,pv2693], .c 7, .c 3, .c 37, .c 31, .c 3, .c 11, .c 5, .c 3, .c 41, .c 17, .c 3,
  .c 5, .c 23, .c 3, .c 7, .c 29, .c 3, .p pv3 [pv2,pv13,pv16573], .p pv3 [pv2,pv3,pv7,pv17,pv71],
  .c 3, .p pv2 [pv2,pv19,pv22679], .c 5, .c 3, .c 13, .c 79, .c 3, .c 5, .c 11, .c 3, .c 19,
  .p pv3 [pv2,pv3,pv13,pv29,pv127], .c 3, .c 281, .p pv2 [pv2,pv3,pv11,pv6529], .c 3, .c 7, .c 5,
  .c 3, .c 11, .c 37, .c 3, .c 5, .c 7, .c 3, .c 29, .p pv2 [pv2,pv3,pv71821], .c 3,
  .p pv3 [pv2,pv23,pv1171], .c 19, .c 3, .c 109, .c 5, .c 3, .c 61, .p pv3 [pv2,pv3,pv5,pv28729],
  .c 3, .c 5, .p pv17 [pv2,pv3,pv89,pv269], .c 3, .p pv3 [pv2,pv5,pv29,pv743], .c 11, .c 3, .c 13,
  .c 7, .c 3, .c 31, .c 5, .c 3, .p pv2 [pv2,pv430949], .p pv2 [pv2,pv3,pv5,pv13,pv17], .c 3,
  .c 5, .p pv3 [pv2,pv3,pv143651], .c 3, .c 73, .c 13, .c 3, .c 7, .c 227, .c 3, .c 317, .c 5,
  .c 3, .p pv3 [pv2,pv107741], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv17957], .c 3,
  .p pv2 [pv2,pv5,pv71,pv607], .c 41, .c 3, .p pv2 [pv2,pv631,pv683], .c 11, .c 3, .c 563,
]
private theorem h0105c06 : checkBlock 861699 128 b0105c06 = true := by
  decide +kernel

private def b0105c07 : List Row := [
  .c 5, .c 3, .c 7, .c 599, .c 3, .c 5, .c 29, .c 3, .c 11, .c 7, .c 3, .p pv3 [pv2,pv107747],
  .p pv3 [pv2,pv3,pv13,pv43,pv257], .c 3, .c 191, .c 5, .c 3, .c 37, .c 13, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv29,pv2477], .c 3, .c 7, .c 373, .c 3, .c 103, .p pv17 [pv2,pv3,pv7,pv733],
  .c 3, .p pv2 [pv2,pv215503], .c 5, .c 3, .c 17, .c 43, .c 3, .c 5, .c 47, .c 3,
  .p pv7 [pv2,pv5,pv13,pv19,pv349], .p pv11 [pv2,pv3,pv17959], .c 3, .c 11, .c 97, .c 3, .c 7,
  .c 5, .c 3, .c 19, .c 271, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv43103], .c 23, .c 3,
  .p pv2 [pv2,pv41,pv10513], .c 13, .c 3, .c 239, .c 5, .c 3, .c 31, .c 11, .c 3, .c 5, .c 17,
  .c 3, .c 877, .c 811, .c 3, .p pv3 [pv2,pv53881], .c 7, .c 3, .c 11, .c 5, .c 3, .c 23, .c 131,
  .c 3, .c 5, .p pv37 [pv2,pv3,pv71843], .c 3, .c 13, .p pv13 [pv2,pv3,pv143687], .c 3, .c 7,
  .p pv13 [pv2,pv3,pv5987], .c 3, .c 383, .c 5, .c 3, .p pv2 [pv2,pv17,pv25357], .c 7, .c 3, .c 5,
  .c 11, .c 3, .c 53, .c 71, .c 3, .p pv2 [pv2,pv67,pv3217], .p pv23 [pv2,pv3,pv11,pv13063], .c 3,
  .c 19, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv29,pv991], .c 3, .c 5,
  .p pv11 [pv2,pv3,pv7,pv1283], .c 3, .p pv2 [pv2,pv5,pv11,pv3919], .c 7, .c 3,
  .p pv2 [pv2,pv13,pv33161], .c 17, .c 3, .c 43, .c 5, .c 3, .c 13, .c 19, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv17,pv79,pv107], .c 3,
]
private theorem h0105c07 : checkBlock 861955 128 b0105c07 = true := by
  decide +kernel

private def b0105c08 : List Row := [
  .c 7, .c 11, .c 3, .c 139, .p pv23 [pv2,pv3,pv7,pv2281], .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv29,pv7433], .p pv3 [pv2,pv3,pv5,pv41,pv701], .c 3, .c 5, .c 101, .c 3,
  .p pv3 [pv2,pv5,pv17,pv317], .c 179, .c 3, .c 23, .p pv29 [pv2,pv3,pv37,pv971], .c 3, .c 7,
  .c 5, .c 3, .p pv2 [pv2,pv19,pv22691], .p pv2 [pv2,pv3,pv5,pv7,pv2053], .c 3, .c 5, .c 7, .c 3,
  .c 41, .p pv5 [pv2,pv3,pv499], .c 3, .c 13, .c 11, .c 3, .p pv2 [pv2,pv431141], .c 5, .c 3,
  .p pv3 [pv2,pv7,pv7699], .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv19,pv31,pv61], .c 3, .c 11, .c 13,
  .c 3, .p pv2 [pv2,pv431153], .c 7, .c 3, .c 107, .c 5, .c 3, .p pv17 [pv2,pv359,pv1201], .c 89,
  .c 3, .c 5, .c 31, .c 3, .p pv2 [pv2,pv5,pv7,pv97,pv127], .c 233, .c 3, .c 7, .c 23, .c 3,
  .p pv5 [pv2,pv13,pv17,pv1951], .c 5, .c 3, .c 73, .c 7, .c 3, .c 5, .c 61, .c 3, .c 151, .c 53,
  .c 3, .c 11, .p pv23 [pv2,pv3,pv13,pv691], .c 3, .c 29, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv20533], .c 3, .c 19, .c 7, .c 3, .p pv2 [pv2,pv37,pv5827],
  .p pv13 [pv2,pv3,pv47911], .c 3, .c 47, .c 5, .c 3, .p pv3 [pv2,pv23,pv43,pv109], .c 11, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv53,pv113], .c 3, .c 7, .p pv5 [pv2,pv3,pv11,pv73,pv179], .c 3, .c 17,
  .c 19, .c 3, .c 11, .c 5, .c 3, .c 101, .p pv11 [pv2,pv3,pv5,pv7187], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv11057], .c 3, .c 31, .c 83, .c 3, .c 127, .c 13, .c 3, .c 7, .c 5,
]
private theorem h0105c08 : checkBlock 862211 128 b0105c08 = true := by
  decide +kernel

private def b0105c09 : List Row := [
  .c 3, .c 53, .p pv31 [pv2,pv3,pv5,pv7,pv37], .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv10781],
  .p pv3 [pv2,pv3,pv31,pv4637], .c 3, .p pv5 [pv2,pv19,pv22697], .c 29, .c 3,
  .p pv2 [pv2,pv257,pv839], .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv23], .c 3, .c 5, .c 37, .c 3,
  .c 13, .c 31, .c 3, .c 41, .c 7, .c 3, .c 23, .c 5, .c 3, .c 17, .c 461, .c 3, .c 5, .c 13,
  .c 3, .p pv2 [pv2,pv5,pv7,pv61,pv101], .c 11, .c 3, .c 7, .c 467, .c 3,
  .p pv3 [pv2,pv137,pv787], .c 5, .c 3, .p pv11 [pv2,pv41,pv67,pv157], .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv233,pv617], .c 3, .p pv2 [pv2,pv5,pv86257], .p pv2 [pv2,pv3,pv71881], .c 3,
  .c 631, .c 71, .c 3, .p pv5 [pv2,pv7,pv61613], .c 5, .c 3, .c 7, .c 47, .c 3, .c 5, .c 17, .c 3,
  .c 61, .c 7, .c 3, .p pv5 [pv2,pv31,pv13913], .c 11, .c 3, .c 653, .c 5, .c 3, .c 19, .c 97,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv109,pv1319], .c 3, .c 7, .p pv5 [pv2,pv3,pv11981], .c 3, .c 31,
  .c 59, .c 3, .c 229, .c 5, .c 3, .p pv3 [pv2,pv17,pv6343], .p pv11 [pv2,pv3,pv5,pv71], .c 3,
  .c 5, .c 19, .c 3, .c 23, .c 29, .c 3, .c 13, .p pv19 [pv2,pv3,pv31,pv773], .c 3, .c 7, .c 5,
  .c 3, .c 479, .c 41, .c 3, .c 5, .c 7, .c 3, .c 883, .c 13, .c 3, .c 11, .c 17, .c 3,
  .p pv5 [pv2,pv83,pv5197], .c 5, .c 3, .c 43, .c 127, .c 3, .c 5, .c 911, .c 3, .c 29,
]
private theorem h0105c09 : checkBlock 862467 128 b0105c09 = true := by
  decide +kernel

private def b0105c10 : List Row := [
  .c 61, .c 3, .p pv5 [pv2,pv431363], .c 7, .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv431369], .c 11,
  .c 3, .c 5, .c 191, .c 3, .c 173, .c 23, .c 3, .c 7, .c 67, .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv53923], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv23,pv521], .c 3, .c 571,
  .p pv11 [pv2,pv3,pv143797], .c 3, .c 53, .p pv2 [pv2,pv3,pv71899], .c 3, .c 557, .c 5, .c 3,
  .c 7, .c 17, .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv13,pv6637], .c 7, .c 3, .c 367,
  .p pv29 [pv2,pv3,pv11,pv17,pv769], .c 3, .c 13, .c 5, .c 3, .c 11, .c 103, .c 3, .c 5, .c 29,
  .c 3, .c 7, .c 101, .c 3, .c 19, .c 13, .c 3, .c 709, .c 5, .c 3, .c 149,
  .p pv7 [pv2,pv3,pv5,pv73,pv197], .c 3, .c 5, .c 283, .c 3, .c 821, .c 11, .c 3, .c 37,
  .p pv3 [pv2,pv3,pv143813], .c 3, .c 7, .c 5, .c 3, .c 167, .c 23, .c 3, .c 5, .c 7, .c 3, .c 13,
  .c 17, .c 3, .p pv2 [pv2,pv11,pv61,pv643], .p pv13 [pv2,pv3,pv71909], .c 3,
  .p pv3 [pv2,pv97,pv139], .c 5, .c 3, .p pv13 [pv2,pv7,pv61637], .p pv7 [pv2,pv3,pv5,pv17,pv47],
  .c 3, .c 5, .c 13, .c 3, .c 701, .c 73, .c 3, .c 17, .c 7, .c 3, .p pv5 [pv2,pv19,pv22709],
  .c 5, .c 3, .c 727, .c 37, .c 3, .c 5, .p pv2 [pv2,pv3,pv23971], .c 3, .c 11, .c 137, .c 3,
  .c 7, .c 433, .c 3, .p pv3 [pv2,pv11,pv1783], .c 5, .c 3,
]
private theorem h0105c10 : checkBlock 862723 128 b0105c10 = true := by
  decide +kernel

private def b0105c11 : List Row := [
  .c 13, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv143831], .c 3, .p pv17 [pv2,pv5,pv211,pv409], .c 59,
  .c 3, .p pv2 [pv2,pv79,pv2731], .c 19, .c 3, .p pv2 [pv2,pv7,pv61643], .c 5, .c 3, .c 7, .c 29,
  .c 3, .c 5, .p pv17 [pv2,pv3,pv7,pv11,pv467], .c 3, .c 241, .c 7, .c 3, .c 11, .c 23, .c 3,
  .c 89, .c 5, .c 3, .c 17, .c 929, .c 3, .c 5, .p pv3 [pv2,pv3,pv47947], .c 3, .c 7, .c 43, .c 3,
  .c 13, .c 691, .c 3, .c 199, .c 5, .c 3, .c 29, .c 11, .c 3, .c 5, .c 349, .c 3,
  .p pv3 [pv2,pv5,pv21577], .c 13, .c 3, .p pv5 [pv2,pv7,pv8807], .c 61, .c 3, .c 7, .c 5, .c 3,
  .c 37, .c 229, .c 3, .c 5, .c 7, .c 3, .c 59, .c 19, .c 3, .c 83, .p pv11 [pv2,pv3,pv47951],
  .c 3, .p pv2 [pv2,pv13,pv89,pv373], .c 5, .c 3, .c 191, .p pv3 [pv2,pv3,pv5,pv28771], .c 3,
  .c 5, .c 11, .c 3, .c 17, .p pv5 [pv2,pv3,pv7,pv20551], .c 3, .c 71, .c 7, .c 3,
  .p pv3 [pv2,pv73,pv739], .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 23, .c 3, .c 109, .c 37, .c 3,
  .c 7, .p pv11 [pv2,pv3,pv293,pv491], .c 3, .c 617, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv71933], .c 3, .c 211, .c 11, .c 3, .c 113, .c 17, .c 3, .c 13, .c 5, .c 3,
  .c 7, .c 269, .c 3, .c 5, .c 19, .c 3, .p pv19 [pv2,pv5,pv86323], .c 7,
]
private theorem h0105c11 : checkBlock 862979 128 b0105c11 = true := by
  decide +kernel

private def b0105c12 : List Row := [
  .c 3, .c 137, .c 13, .c 3, .c 17, .c 5, .c 3, .c 47, .p pv2 [pv2,pv3,pv5,pv1151], .c 3, .c 5,
  .c 31, .c 3, .c 7, .c 257, .c 3, .c 151, .c 11, .c 3, .c 457, .c 5, .c 3,
  .p pv37 [pv2,pv13,pv33203], .c 227, .c 3, .c 5, .p pv3 [pv2,pv3,pv143881], .c 3, .c 11, .c 431,
  .c 3, .c 521, .p pv2 [pv2,pv3,pv73], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv215827], .c 17, .c 3,
  .c 5, .c 7, .c 3, .c 37, .p pv2 [pv2,pv3,pv19,pv7573], .c 3, .c 823, .c 139, .c 3, .c 61, .c 5,
  .c 3, .c 787, .c 19, .c 3, .c 5, .c 59, .c 3, .c 23, .c 401, .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv17,pv67,pv379], .c 5, .c 3, .c 13, .c 73, .c 3, .c 5, .p pv13 [pv2,pv3,pv17987],
  .c 3, .c 31, .c 107, .c 3, .c 7, .c 89, .c 3, .p pv3 [pv2,pv26981], .c 5, .c 3, .c 409, .c 7,
  .c 3, .c 5, .c 443, .c 3, .c 163, .c 17, .c 3, .c 19, .c 41, .c 3, .c 11, .c 5, .c 3, .c 7,
  .c 71, .c 3, .c 5, .c 47, .c 3, .c 773, .c 7, .c 3, .c 13, .c 83, .c 3, .c 461, .c 5, .c 3,
  .c 673, .c 199, .c 3, .c 5, .c 11, .c 3, .c 7, .c 13, .c 3, .c 587,
  .p pv7 [pv2,pv3,pv7,pv11,pv89], .c 3, .c 43, .c 5, .c 3, .c 11,
]
private theorem h0105c12 : checkBlock 863235 128 b0105c12 = true := by
  decide +kernel

private def b0105c13 : List Row := [
  .p pv13 [pv2,pv3,pv5,pv107,pv269], .c 3, .c 5, .p pv5 [pv2,pv3,pv67,pv179], .c 3, .c 41, .c 241,
  .c 3, .c 239, .p pv7 [pv2,pv3,pv227,pv317], .c 3, .c 7, .c 5, .c 3, .c 719,
  .p pv59 [pv2,pv3,pv5,pv7,pv257], .c 3, .c 5, .c 7, .c 3, .c 19, .c 11, .c 3,
  .p pv3 [pv2,pv31,pv1741], .p pv2 [pv2,pv3,pv13,pv11071], .c 3, .c 37, .c 5, .c 3, .c 17, .c 13,
  .c 3, .c 5, .c 167, .c 3, .p pv3 [pv2,pv5,pv21589], .c 67, .c 3, .c 31, .c 7, .c 3, .c 71, .c 5,
  .c 3, .c 331, .c 23, .c 3, .c 5, .c 769, .c 3, .c 29, .p pv17 [pv2,pv3,pv35983], .c 3, .c 7,
  .c 11, .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv107951], .c 7, .c 3, .c 5, .c 17, .c 3, .c 11,
  .c 211, .c 3, .c 23, .c 13, .c 3, .p pv3 [pv2,pv7,pv11,pv701], .c 5, .c 3, .c 7,
  .p pv17 [pv2,pv3,pv5,pv2399], .c 3, .c 5, .c 311, .c 3, .c 17, .c 7, .c 3, .c 157, .c 113, .c 3,
  .c 73, .c 5, .c 3, .c 491, .p pv17 [pv2,pv3,pv5,pv28789], .c 3, .c 5, .c 271, .c 3, .c 7, .c 19,
  .c 3, .c 11, .p pv13 [pv2,pv3,pv7,pv53,pv97], .c 3, .p pv2 [pv2,pv263,pv821], .c 5, .c 3, .c 61,
  .c 59, .c 3, .c 5, .c 13, .c 3, .p pv7 [pv2,pv5,pv86371], .c 547, .c 3, .c 613, .c 17, .c 3,
  .c 7, .c 5, .c 3, .p pv3 [pv2,pv37,pv1459], .c 11, .c 3, .c 5, .c 7, .c 3, .c 43,
  .p pv5 [pv2,pv3,pv11,pv23,pv569], .c 3,
]
private theorem h0105c13 : checkBlock 863491 128 b0105c13 = true := by
  decide +kernel

private def b0105c14 : List Row := [
  .c 41, .p pv23 [pv2,pv3,pv23993], .c 3, .c 11, .c 5, .c 3, .c 13, .c 607, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv47,pv1021], .c 3, .p pv23 [pv2,pv5,pv17,pv5081], .c 509, .c 3, .c 257, .c 7,
  .c 3, .p pv5 [pv2,pv431891], .c 5, .c 3, .c 173, .c 353, .c 3, .c 5, .c 11, .c 3,
  .p pv3 [pv2,pv5,pv7,pv617], .p pv2 [pv2,pv3,pv37,pv1297], .c 3, .c 7, .c 73, .c 3, .c 47, .c 5,
  .c 3, .c 11, .c 7, .c 3, .c 5, .c 43, .c 3, .c 67, .p pv5 [pv2,pv3,pv35993], .c 3, .c 13, .c 37,
  .c 3, .p pv2 [pv2,pv7,pv61703], .c 5, .c 3, .c 7, .p pv19 [pv2,pv3,pv5,pv13,pv443], .c 3, .c 5,
  .c 23, .c 3, .c 103, .c 7, .c 3, .p pv2 [pv2,pv431933], .p pv2 [pv2,pv3,pv193,pv373], .c 3,
  .c 19, .c 5, .c 3, .p pv7 [pv2,pv59,pv7321], .c 29, .c 3, .c 5, .p pv13 [pv2,pv3,pv143981],
  .c 3, .c 7, .c 191, .c 3, .p pv3 [pv2,pv11,pv9817], .p pv2 [pv2,pv3,pv7,pv67,pv307], .c 3,
  .c 23, .c 5, .c 3, .p pv2 [pv2,pv31,pv6967], .c 19, .c 3, .c 5, .p pv7 [pv2,pv3,pv71993], .c 3,
  .p pv3 [pv2,pv5,pv10799], .c 17, .c 3, .c 661, .c 11, .c 3, .c 7, .c 5, .c 3, .c 29, .c 13,
  .c 3, .c 5, .c 7, .c 3, .c 11, .c 53, .c 3, .c 17, .p pv13 [pv2,pv3,pv311,pv463], .c 3, .c 277,
  .c 5, .c 3, .c 389, .c 157, .c 3, .c 5, .c 541, .c 3, .c 127, .p pv3 [pv2,pv3,pv7,pv6857], .c 3,
  .c 19, .c 7, .c 3, .c 13, .c 5, .c 3, .c 43, .c 31,
]
private theorem h0105c14 : checkBlock 863747 128 b0105c14 = true := by
  decide +kernel

private def b0105c15 : List Row := [
  .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv13,pv19,pv53], .c 3, .p pv2 [pv2,pv5,pv7,pv12343],
  .p pv5 [pv2,pv3,pv89,pv809], .c 3, .c 7, .c 13, .c 3, .c 79, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv73,pv269], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv24001], .c 3, .c 23, .c 109,
  .c 3, .p pv5 [pv2,pv432023], .p pv11 [pv2,pv3,pv47,pv383], .c 3, .p pv2 [pv2,pv7,pv30859], .c 5,
  .c 3, .c 7, .c 11, .c 3, .c 5, .c 103, .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv17,pv97,pv131],
  .p pv3 [pv2,pv3,pv144013], .c 3, .c 11, .c 5, .c 3, .c 853, .p pv2 [pv2,pv3,pv5,pv9601], .c 3,
  .c 5, .c 13, .c 3, .c 7, .p pv3 [pv2,pv3,pv79,pv1823], .c 3, .p pv2 [pv2,pv432053], .c 743,
  .c 3, .c 29, .c 5, .c 3, .p pv7 [pv2,pv432059], .p pv17 [pv2,pv3,pv5,pv19,pv379], .c 3, .c 5,
  .c 11, .c 3, .p pv2 [pv2,pv5,pv86413], .c 23, .c 3, .p pv3 [pv2,pv7,pv13,pv1187], .c 19, .c 3,
  .c 7, .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv7,pv823], .c 3, .c 5, .c 7, .c 3, .c 17, .c 139,
  .c 3, .p pv5 [pv2,pv67,pv6449], .p pv7 [pv2,pv3,pv36007], .c 3, .c 59, .c 5, .c 3, .c 23, .c 79,
  .c 3, .c 5, .c 31, .c 3, .p pv11 [pv2,pv5,pv89,pv971], .c 11, .c 3, .c 233, .c 7, .c 3,
  .p pv2 [pv2,pv23,pv18787], .c 5, .c 3, .c 37, .p pv23 [pv2,pv3,pv5,pv28807], .c 3, .c 5, .c 409,
  .c 3, .p pv11 [pv2,pv5,pv7,pv6173], .p pv31 [pv2,pv3,pv144037], .c 3, .c 7, .c 17, .c 3, .c 67,
  .c 5, .c 3, .c 41, .c 7, .c 3, .c 5, .c 73, .c 3, .p pv2 [pv2,pv5,pv3457], .c 13, .c 3, .c 43,
]
private theorem h0105c15 : checkBlock 864003 128 b0105c15 = true := by
  decide +kernel

private def b0105c16 : List Row := [
  .c 11, .c 3, .c 17, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv10289], .c 3,
  .c 11, .c 7, .c 3, .c 29, .p pv7 [pv2,pv3,pv3001], .c 3, .c 443, .c 5, .c 3,
  .p pv2 [pv2,pv432149], .p pv2 [pv2,pv3,pv5,pv43,pv67], .c 3, .c 5, .p pv2 [pv2,pv3,pv48017],
  .c 3, .c 7, .c 421, .c 3, .c 23, .p pv3 [pv2,pv3,pv7,pv13,pv1583], .c 3, .p pv2 [pv2,pv432161],
  .c 5, .c 3, .c 19, .c 13, .c 3, .c 5, .c 113, .c 3, .p pv2 [pv2,pv5,pv23,pv1879], .c 43, .c 3,
  .c 11, .c 149, .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv11,pv101,pv389],
  .p pv23 [pv2,pv3,pv5,pv7], .c 3, .c 5, .c 7, .c 3, .c 907, .c 31, .c 3, .c 47,
  .p pv23 [pv2,pv3,pv16007], .c 3, .c 13, .c 5, .c 3, .c 163, .c 11, .c 3, .c 5, .c 419, .c 3,
  .c 751, .c 29, .c 3, .p pv5 [pv2,pv432203], .c 7, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv79,pv5471], .c 463, .c 3, .c 5, .p pv2 [pv2,pv3,pv144071], .c 3, .c 37, .c 17,
  .c 3, .c 7, .p pv3 [pv2,pv3,pv144073], .c 3, .c 19, .c 5, .c 3, .p pv3 [pv2,pv13,pv1039], .c 7,
  .c 3, .c 5, .c 11, .c 3, .c 13, .c 239, .c 3, .c 17, .c 131, .c 3, .c 349, .c 5, .c 3, .c 7,
  .c 19, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv11,pv29,pv271], .c 7, .c 3, .c 31, .c 379,
  .c 3, .p pv5 [pv2,pv432251], .c 5, .c 3, .p pv2 [pv2,pv216127], .p pv3 [pv2,pv3,pv5,pv28817],
  .c 3,
]
private theorem h0105c16 : checkBlock 864259 128 b0105c16 = true := by
  decide +kernel

private def b0105c17 : List Row := [
  .c 5, .c 277, .c 3, .c 7, .c 11, .c 3, .c 59, .c 677, .c 3, .p pv2 [pv2,pv216133], .c 5, .c 3,
  .c 13, .p pv17 [pv2,pv3,pv5,pv1601], .c 3, .c 5, .c 23, .c 3, .p pv7 [pv2,pv5,pv17291], .c 61,
  .c 3, .c 19, .c 31, .c 3, .c 7, .c 5, .c 3, .c 17, .c 223, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv139,pv311], .p pv5 [pv2,pv3,pv103,pv1399], .c 3, .p pv2 [pv2,pv17,pv59,pv431],
  .c 11, .c 3, .c 23, .c 5, .c 3, .c 157, .c 43, .c 3, .c 5, .c 137, .c 3, .c 11,
  .p pv19 [pv2,pv3,pv7,pv47,pv73], .c 3, .c 13, .c 7, .c 3, .p pv5 [pv2,pv11,pv39301], .c 5, .c 3,
  .p pv2 [pv2,pv216157], .p pv3 [pv2,pv3,pv5,pv13,pv739], .c 3, .c 5, .c 17, .c 3,
  .p pv3 [pv2,pv5,pv7,pv193], .c 13, .c 3, .c 7, .c 41, .c 3, .c 37, .c 5, .c 3, .c 47, .c 7,
  .c 3, .c 5, .c 107, .c 3, .c 17, .p pv5 [pv2,pv3,pv9007], .c 3, .c 11,
  .p pv3 [pv2,pv3,pv211,pv683], .c 3, .c 31, .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv19,pv37,pv41], .c 3, .c 5, .c 109, .c 3, .c 433, .c 7, .c 3,
  .p pv2 [pv2,pv47,pv9199], .c 19, .c 3, .c 857, .c 5, .c 3, .c 139, .c 11, .c 3, .c 5, .c 37,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv11,pv6551], .c 3, .p pv3 [pv2,pv61,pv443], .c 17, .c 3, .c 11,
  .c 5, .c 3, .c 179, .c 29, .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv157], .c 3, .c 271, .c 59, .c 3,
  .c 499, .c 67,
]
private theorem h0105c17 : checkBlock 864515 128 b0105c17 = true := by
  decide +kernel

private def b0105c18 : List Row := [
  .c 3, .c 7, .c 5, .c 3, .c 919, .p pv43 [pv2,pv3,pv5,pv7,pv29,pv71], .c 3, .c 5, .c 7, .c 3,
  .c 509, .p pv7 [pv2,pv3,pv12011], .c 3, .c 61, .c 13, .c 3, .p pv2 [pv2,pv432401], .c 5, .c 3,
  .c 11, .p pv2 [pv2,pv3,pv5,pv3203], .c 3, .c 5, .p pv5 [pv2,pv3,pv43,pv419], .c 3, .c 809,
  .c 19, .c 3, .c 173, .c 7, .c 3, .c 193, .c 5, .c 3, .c 601, .c 17, .c 3, .c 5, .c 47, .c 3,
  .c 13, .c 11, .c 3, .c 7, .c 43, .c 3, .c 101, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 13, .c 3,
  .c 59, .p pv2 [pv2,pv3,pv48049], .c 3, .p pv5 [pv2,pv11,pv39313], .c 211, .c 3, .c 167, .c 5,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv31], .c 3, .c 5, .c 53, .c 3, .p pv11 [pv2,pv5,pv86491], .c 7,
  .c 3, .p pv2 [pv2,pv13,pv16633], .c 11, .c 3, .c 577, .c 5, .c 3, .c 13, .c 31, .c 3, .c 5,
  .c 19, .c 3, .c 7, .c 17, .c 3, .p pv2 [pv2,pv251,pv1723], .c 37, .c 3,
  .p pv3 [pv2,pv11,pv9829], .c 5, .c 3, .p pv7 [pv2,pv432479], .c 23, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv144161], .c 3, .c 79, .c 823, .c 3, .c 17, .p pv3 [pv2,pv3,pv144163], .c 3,
  .c 7, .c 5, .c 3, .p pv2 [pv2,pv43,pv47,pv107], .c 89, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv173], .p pv3 [pv2,pv3,pv144167], .c 3, .c 11, .c 839, .c 3, .c 19, .c 5, .c 3,
  .c 367, .c 557, .c 3, .c 5,
]
private theorem h0105c18 : checkBlock 864771 128 b0105c18 = true := by
  decide +kernel

private def b0105c19 : List Row := [
  .c 197, .c 3, .c 43, .c 13, .c 3, .c 67, .c 7, .c 3, .p pv2 [pv2,pv523,pv827], .c 5, .c 3,
  .p pv3 [pv2,pv108131], .c 11, .c 3, .c 5, .p pv11 [pv2,pv3,pv9011], .c 3,
  .p pv3 [pv2,pv5,pv7,pv37,pv167], .c 397, .c 3, .c 7, .p pv2 [pv2,pv3,pv72089], .c 3, .c 11,
  .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv31,pv4651], .c 3,
  .p pv2 [pv2,pv5,pv86509], .c 317, .c 3, .c 37, .c 23, .c 3, .p pv5 [pv2,pv7,pv61,pv1013], .c 5,
  .c 3, .c 7, .c 13, .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv5407], .c 7, .c 3, .c 19, .c 47,
  .c 3, .c 109, .c 5, .c 3, .c 11, .c 41, .c 3, .c 5, .c 17, .c 3, .c 7, .p pv5 [pv2,pv3,pv751],
  .c 3, .c 29, .p pv7 [pv2,pv3,pv7,pv20599], .c 3, .c 13, .c 5, .c 3, .c 89, .c 37, .c 3, .c 5,
  .p pv19 [pv2,pv3,pv13,pv47,pv59], .c 3, .c 17, .c 11, .c 3, .c 593, .c 13, .c 3, .c 7, .c 5,
  .c 3, .c 281, .p pv23 [pv2,pv3,pv5,pv7,pv103], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv31,pv2791], .p pv2 [pv2,pv3,pv72101], .c 3, .p pv3 [pv2,pv11,pv1229], .c 193,
  .c 3, .c 41, .c 5, .c 3, .c 293, .p pv37 [pv2,pv3,pv5,pv151,pv191], .c 3, .c 5, .c 23, .c 3,
  .c 13, .c 149, .c 3, .p pv5 [pv2,pv43,pv10061], .c 7, .c 3, .p pv2 [pv2,pv199,pv1087], .c 5,
  .c 3, .p pv2 [pv2,pv89,pv4861], .p pv13 [pv2,pv3,pv5,pv11,pv19,pv23], .c 3, .c 5, .c 13, .c 3,
  .c 11, .c 29, .c 3, .c 7, .c 19, .c 3,
]
private theorem h0105c19 : checkBlock 865027 128 b0105c19 = true := by
  decide +kernel

private def b0105c20 : List Row := [
  .c 17, .c 5, .c 3, .c 43, .c 7, .c 3, .c 5, .c 461, .c 3, .p pv2 [pv2,pv5,pv17,pv509], .c 31,
  .c 3, .p pv5 [pv2,pv13,pv23,pv1447], .c 107, .c 3, .p pv3 [pv2,pv7,pv3863], .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv7211], .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv11,pv1873], .c 3, .c 29, .c 7,
  .c 3, .c 11, .p pv2 [pv2,pv3,pv144223], .c 3, .p pv5 [pv2,pv73,pv5927], .c 5, .c 3,
  .p pv2 [pv2,pv11,pv71,pv277], .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv37,pv1949], .c 3, .c 7,
  .p pv3 [pv2,pv3,pv233,pv619], .c 3, .c 163, .c 739, .c 3, .c 269, .c 5, .c 3,
  .p pv2 [pv2,pv127,pv3407], .c 11, .c 3, .c 5, .c 41, .c 3, .c 229, .c 19, .c 3, .c 13, .c 487,
  .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv6761], .c 47, .c 3, .c 5, .c 7, .c 3, .c 23, .c 13, .c 3,
  .c 31, .c 137, .c 3, .c 307, .c 5, .c 3, .c 67, .c 83, .c 3, .c 5, .c 11, .c 3, .c 199, .c 17,
  .c 3, .p pv3 [pv2,pv54091], .c 7, .c 3, .c 223, .c 5, .c 3, .c 11, .c 59, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv29,pv829], .c 3, .p pv3 [pv2,pv5,pv7,pv11,pv281], .p pv11 [pv2,pv3,pv144247],
  .c 3, .c 7, .c 31, .c 3, .p pv2 [pv2,pv216373], .c 5, .c 3, .p pv2 [pv2,pv432749], .c 7, .c 3,
  .c 5, .c 19, .c 3, .p pv11 [pv2,pv5,pv41,pv2111], .c 11, .c 3, .c 131, .c 173, .c 3, .c 107,
  .c 5, .c 3, .c 7, .c 97, .c 3, .c 5, .p pv41 [pv2,pv3,pv7,pv23],
]
private theorem h0105c20 : checkBlock 865283 128 b0105c20 = true := by
  decide +kernel

private def b0105c21 : List Row := [
  .c 3, .c 37, .c 7, .c 3, .c 43, .c 359, .c 3, .c 13, .c 5, .c 3, .c 23, .c 71, .c 3, .c 5,
  .c 433, .c 3, .c 7, .c 67, .c 3, .p pv3 [pv2,pv257,pv421], .c 11, .c 3, .c 19, .c 5, .c 3,
  .c 17, .p pv3 [pv2,pv3,pv5,pv11,pv43,pv61], .c 3, .c 5, .p pv2 [pv2,pv3,pv53,pv1361], .c 3,
  .c 11, .c 79, .c 3, .c 83, .p pv29 [pv2,pv3,pv36067], .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv197], .c 19, .c 3, .c 5, .c 7, .c 3, .c 13, .c 41, .c 3,
  .p pv2 [pv2,pv379,pv571], .p pv3 [pv2,pv3,pv48091], .c 3, .p pv2 [pv2,pv269,pv1609], .c 5, .c 3,
  .c 53, .c 23, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv43283], .c 503, .c 3, .c 11, .c 7,
  .c 3, .c 733, .c 5, .c 3, .c 29, .p pv13 [pv2,pv3,pv5,pv3607], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv223,pv647], .c 3, .c 17, .c 47, .c 3, .c 7, .c 251, .c 3, .c 71, .c 5, .c 3,
  .c 13, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv19,pv3797], .c 3, .p pv3 [pv2,pv5,pv23,pv941],
  .c 181, .c 3, .c 317, .p pv11 [pv2,pv3,pv167], .c 3, .c 11, .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv47,pv307], .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv6871], .c 3,
  .p pv19 [pv2,pv5,pv3463], .c 7, .c 3, .p pv2 [pv2,pv41,pv5279], .c 17, .c 3, .c 37, .c 5, .c 3,
  .p pv3 [pv2,pv31,pv3491], .p pv19 [pv2,pv3,pv5,pv28859], .c 3, .c 5, .c 11, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv16033], .c 3, .c 13, .c 23, .c 3, .c 17,
]
private theorem h0105c21 : checkBlock 865539 128 b0105c21 = true := by
  decide +kernel

private def b0105c22 : List Row := [
  .c 5, .c 3, .c 11, .p pv11 [pv2,pv3,pv5,pv13,pv37], .c 3, .c 5, .p pv13 [pv2,pv3,pv113,pv1277],
  .c 3, .c 19, .c 13, .c 3, .p pv3 [pv2,pv7,pv15461], .p pv3 [pv2,pv3,pv103,pv467], .c 3, .c 7,
  .c 5, .c 3, .p pv2 [pv2,pv233,pv929], .c 139, .c 3, .c 5, .c 7, .c 3, .c 67, .c 11, .c 3,
  .p pv5 [pv2,pv432923], .c 19, .c 3, .c 29, .c 5, .c 3, .p pv7 [pv2,pv7,pv23,pv2689], .c 17,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv144311], .c 3, .p pv13 [pv2,pv5,pv86587], .c 101, .c 3,
  .p pv2 [pv2,pv11,pv1789], .c 7, .c 3, .c 677, .c 5, .c 3, .p pv3 [pv2,pv27059], .c 13, .c 3,
  .c 5, .c 239, .c 3, .c 547, .c 751, .c 3, .c 7, .c 11, .c 3, .c 241, .c 5, .c 3, .c 79, .c 7,
  .c 3, .c 5, .c 23, .c 3, .c 11, .p pv2 [pv2,pv3,pv72161], .c 3, .p pv3 [pv2,pv54121], .c 83,
  .c 3, .c 13, .c 5, .c 3, .c 7, .c 107, .c 3, .c 5, .p pv17 [pv2,pv3,pv7,pv13,pv61], .c 3, .c 41,
  .c 7, .c 3, .c 53, .c 13, .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv432989], .c 619, .c 3, .c 5,
  .c 71, .c 3, .c 7, .p pv5 [pv2,pv3,pv36083], .c 3, .c 11, .c 73, .c 3,
  .p pv2 [pv2,pv41,pv59,pv179], .c 5, .c 3, .p pv3 [pv2,pv11,pv13,pv757],
  .p pv3 [pv2,pv3,pv5,pv28867], .c 3, .c 5, .c 61, .c 3, .c 13, .c 881, .c 3, .c 29,
  .p pv2 [pv2,pv3,pv72169], .c 3, .c 7, .c 5, .c 3, .c 19, .c 11, .c 3, .c 5, .c 7, .c 3,
]
private theorem h0105c22 : checkBlock 865795 128 b0105c22 = true := by
  decide +kernel

private def b0105c23 : List Row := [
  .p pv7 [pv2,pv5,pv17321], .p pv5 [pv2,pv3,pv11], .c 3, .p pv3 [pv2,pv29,pv3733], .c 37, .c 3,
  .c 11, .c 5, .c 3, .c 47, .c 313, .c 3, .c 5, .c 19, .c 3, .p pv3 [pv2,pv5,pv5413],
  .p pv7 [pv2,pv3,pv7,pv17,pv1213], .c 3, .p pv5 [pv2,pv13,pv33311], .c 7, .c 3,
  .p pv2 [pv2,pv216523], .c 5, .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv2887], .c 3, .c 5, .c 11, .c 3,
  .c 23, .c 97, .c 3, .c 7, .p pv7 [pv2,pv3,pv11,pv1193], .c 3, .p pv2 [pv2,pv433061], .c 5, .c 3,
  .c 11, .c 7, .c 3, .c 5, .c 149, .c 3, .c 541, .c 29, .c 3, .c 439, .c 43, .c 3, .c 19, .c 5,
  .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv401], .c 3, .c 5, .c 17, .c 3, .c 31, .c 7, .c 3, .c 13,
  .c 53, .c 3, .p pv5 [pv2,pv163,pv2657], .c 5, .c 3, .c 607, .c 19, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv24061], .c 3, .c 7, .c 13, .c 3, .c 37, .c 197, .c 3, .p pv2 [pv2,pv216553],
  .c 5, .c 3, .c 461, .p pv2 [pv2,pv3,pv5,pv14437], .c 3, .c 5, .c 331, .c 3,
  .p pv7 [pv2,pv5,pv29,pv103], .c 31, .c 3, .c 89, .c 11, .c 3, .c 7, .c 5, .c 3, .c 23, .c 137,
  .c 3, .c 5, .c 7, .c 3, .c 11, .c 283, .c 3, .c 19, .c 17, .c 3, .c 463, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv43,pv1439], .c 13, .c 3, .c 5, .c 151, .c 3, .c 73,
  .p pv11 [pv2,pv3,pv7,pv10313], .c 3, .c 59, .c 7, .c 3, .c 17, .c 5,
]
private theorem h0105c23 : checkBlock 866051 128 b0105c23 = true := by
  decide +kernel

private def b0105c24 : List Row := [
  .c 3, .p pv2 [pv2,pv216577], .p pv3 [pv2,pv3,pv5,pv67,pv431], .c 3, .c 5, .c 29, .c 3, .c 43,
  .c 281, .c 3, .c 7, .p pv11 [pv2,pv3,pv36097], .c 3, .c 13, .c 5, .c 3, .c 797, .c 7, .c 3,
  .c 5, .c 257, .c 3, .c 47, .p pv5 [pv2,pv3,pv18049], .c 3, .c 31, .c 13, .c 3, .c 631, .c 5,
  .c 3, .c 7, .c 11, .c 3, .c 5, .c 67, .c 3, .c 19, .c 7, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv17,pv31,pv137], .c 3, .c 11, .c 5, .c 3, .p pv7 [pv2,pv13,pv47,pv709], .c 293,
  .c 3, .c 5, .c 43, .c 3, .c 7, .c 71, .c 3, .p pv3 [pv2,pv54151], .c 19, .c 3, .c 521, .c 5,
  .c 3, .c 37, .p pv3 [pv2,pv3,pv5,pv3209], .c 3, .c 5, .c 11, .c 3, .c 109,
  .p pv2 [pv2,pv3,pv144407], .c 3, .c 181, .c 269, .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv7,pv2063], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv11,pv7877], .c 17,
  .c 3, .p pv2 [pv2,pv13,pv19,pv877], .c 23, .c 3, .c 157, .c 5, .c 3, .c 13, .c 29, .c 3, .c 5,
  .c 53, .c 3, .c 97, .c 11, .c 3, .c 17, .c 7, .c 3, .p pv3 [pv2,pv31,pv1747], .c 5, .c 3,
  .p pv11 [pv2,pv433259], .c 127, .c 3, .c 5, .c 233, .c 3, .c 653, .c 19, .c 3, .c 7, .c 47,
  .c 3, .c 31, .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .c 173, .c 3, .c 401,
]
private theorem h0105c24 : checkBlock 866307 128 b0105c24 = true := by
  decide +kernel

private def b0105c25 : List Row := [
  .c 167, .c 3, .c 13, .c 11, .c 3, .p pv2 [pv2,pv7,pv30949], .c 5, .c 3, .c 7,
  .p pv19 [pv2,pv3,pv5,pv11,pv13,pv101], .c 3, .c 5, .c 569, .c 3, .c 11, .c 7, .c 3, .c 113,
  .c 887, .c 3, .c 53, .c 5, .c 3, .c 17, .c 523, .c 3, .c 5, .c 23, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv43,pv3359], .c 3, .c 61, .p pv2 [pv2,pv3,pv7,pv19,pv181], .c 3, .c 47, .c 5,
  .c 3, .p pv7 [pv2,pv433319], .p pv7 [pv2,pv3,pv5,pv23,pv157], .c 3, .c 5, .c 19, .c 3, .c 37,
  .p pv13 [pv2,pv3,pv72221], .c 3, .c 11, .c 109, .c 3, .c 7, .c 5, .c 3, .c 503, .c 13, .c 3,
  .c 5, .c 7, .c 3, .c 101, .p pv2 [pv2,pv3,pv89,pv541], .c 3, .c 839,
  .p pv11 [pv2,pv3,pv37,pv61], .c 3, .p pv2 [pv2,pv389,pv557], .c 5, .c 3, .c 41, .c 11, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv144451], .c 3, .c 17, .p pv5 [pv2,pv3,pv7,pv11,pv67], .c 3,
  .p pv2 [pv2,pv216679], .c 7, .c 3, .c 11, .c 5, .c 3, .c 31, .c 859, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv463], .c 3, .c 431, .p pv3 [pv2,pv3,pv19,pv7603], .c 3, .c 7, .c 13,
  .c 3, .c 599, .c 5, .c 3, .p pv11 [pv2,pv191,pv2269], .c 7, .c 3, .c 5, .c 11, .c 3, .c 89,
  .c 379, .c 3, .p pv3 [pv2,pv108347], .c 17, .c 3, .p pv5 [pv2,pv7,pv101,pv613], .c 5, .c 3,
  .c 7, .c 31, .c 3, .c 5, .c 157, .c 3, .c 13, .c 7, .c 3, .c 107, .c 181, .c 3, .c 17, .c 5,
  .c 3,
]
private theorem h0105c25 : checkBlock 866563 128 b0105c25 = true := by
  decide +kernel

private def b0105c26 : List Row := [
  .p pv2 [pv2,pv19,pv22811], .c 47, .c 3, .c 5, .c 13, .c 3, .c 7, .c 11, .c 3, .c 19, .c 29,
  .c 3, .p pv2 [pv2,pv433421], .c 5, .c 3, .p pv3 [pv2,pv103,pv263], .p pv2 [pv2,pv3,pv5,pv5779],
  .c 3, .c 5, .p pv5 [pv2,pv3,pv19,pv1901], .c 3, .c 257, .c 41, .c 3, .c 79,
  .p pv17 [pv2,pv3,pv29,pv47,pv53], .c 3, .c 7, .c 5, .c 3, .c 13, .c 17, .c 3, .c 5, .c 7, .c 3,
  .c 151, .c 23, .c 3, .c 29, .c 11, .c 3, .c 173, .c 5, .c 3, .p pv2 [pv2,pv7,pv4423], .c 419,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv23,pv349], .c 3, .c 11, .c 43, .c 3, .p pv5 [pv2,pv29,pv14947],
  .c 7, .c 3, .p pv2 [pv2,pv11,pv17,pv19,pv61], .c 5, .c 3, .c 23, .p pv2 [pv2,pv3,pv5,pv14449],
  .c 3, .c 5, .c 37, .c 3, .c 19, .p pv5 [pv2,pv3,pv12041], .c 3, .c 7, .c 811, .c 3,
  .p pv2 [pv2,pv23,pv47,pv401], .c 5, .c 3, .p pv3 [pv2,pv307,pv353], .c 7, .c 3, .c 5, .c 31,
  .c 3, .c 71, .c 13, .c 3, .c 11, .c 19, .c 3, .c 61, .c 5, .c 3, .c 7,
  .p pv19 [pv2,pv3,pv5,pv17], .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv983], .c 3,
  .p pv13 [pv2,pv5,pv277,pv313], .c 7, .c 3, .c 17, .c 449, .c 3, .p pv5 [pv2,pv13,pv33347], .c 5,
  .c 3, .c 127, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv72253], .c 3, .c 7, .c 199, .c 3, .c 67,
  .c 113, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv37,pv11717], .c 13, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv144511], .c 3, .c 29, .c 137,
]
private theorem h0105c26 : checkBlock 866819 128 b0105c26 = true := by
  decide +kernel

private def b0105c27 : List Row := [
  .c 3, .c 23, .p pv3 [pv2,pv3,pv16057], .c 3, .c 7, .c 5, .c 3, .c 131,
  .p pv2 [pv2,pv3,pv5,pv7,pv4129], .c 3, .c 5, .c 7, .c 3, .c 31, .c 19, .c 3, .c 709, .c 41,
  .c 3, .c 13, .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv3613], .c 3, .c 5, .c 89, .c 3,
  .p pv2 [pv2,pv5,pv11,pv7883], .c 53, .c 3, .c 701, .c 7, .c 3, .p pv5 [pv2,pv433571], .c 5,
  .c 3, .c 193, .p pv3 [pv2,pv3,pv5,pv41,pv47], .c 3, .c 5, .c 103, .c 3,
  .p pv37 [pv2,pv5,pv7,pv19,pv163], .c 11, .c 3, .c 7, .c 23, .c 3, .p pv2 [pv2,pv431,pv503],
  .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 17, .c 3, .c 13, .c 151, .c 3, .c 47, .c 463, .c 3,
  .p pv2 [pv2,pv7,pv8849], .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv137,pv211], .c 3, .c 5, .c 13,
  .c 3, .c 17, .c 7, .c 3, .p pv2 [pv2,pv233,pv1861], .c 11, .c 3, .p pv3 [pv2,pv41,pv661], .c 5,
  .c 3, .c 53, .c 59, .c 3, .c 5, .c 223, .c 3, .c 7, .p pv2 [pv2,pv3,pv72271], .c 3,
  .p pv3 [pv2,pv13,pv31,pv269], .p pv7 [pv2,pv3,pv7,pv6883], .c 3, .p pv5 [pv2,pv11,pv79,pv499],
  .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv28909], .c 3, .c 5, .c 97, .c 3,
  .p pv3 [pv2,pv5,pv37,pv293], .c 127, .c 3, .c 31, .c 17, .c 3, .c 7, .c 5, .c 3, .c 433,
  .p pv2 [pv2,pv3,pv5,pv7,pv59], .c 3, .c 5, .c 7, .c 3, .c 727, .c 73, .c 3, .c 11,
  .p pv13 [pv2,pv3,pv31,pv4663], .c 3, .c 17, .c 5, .c 3, .c 149,
]
private theorem h0105c27 : checkBlock 867075 128 b0105c27 = true := by
  decide +kernel

private def b0105c28 : List Row := [
  .c 19, .c 3, .c 5, .p pv5 [pv2,pv3,pv71,pv509], .c 3, .c 79, .p pv3 [pv2,pv3,pv7,pv107,pv193],
  .c 3, .c 13, .c 7, .c 3, .c 23, .c 5, .c 3, .c 59, .c 11, .c 3, .c 5, .c 227, .c 3,
  .p pv2 [pv2,pv5,pv7,pv12391], .c 13, .c 3, .c 7, .c 311, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv19,pv101,pv113], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv41,pv43], .c 3,
  .p pv3 [pv2,pv5,pv4337], .c 607, .c 3, .c 19, .p pv23 [pv2,pv3,pv17,pv1063], .c 3,
  .p pv2 [pv2,pv7,pv13,pv2383], .c 5, .c 3, .c 7, .c 211, .c 3, .c 5, .c 11, .c 3,
  .p pv11 [pv2,pv5,pv86743], .c 7, .c 3, .c 41, .c 43, .c 3, .p pv2 [pv2,pv17,pv31,pv823], .c 5,
  .c 3, .c 11, .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv251], .c 3, .c 7, .p pv5 [pv2,pv3,pv144577],
  .c 3, .p pv2 [pv2,pv103,pv4211], .c 479, .c 3, .c 31, .c 5, .c 3, .c 47, .c 61, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv163,pv887], .c 3, .c 23, .c 11, .c 3, .c 673, .c 79, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv216877], .p pv19 [pv2,pv3,pv5,pv7,pv17], .c 3, .c 5, .c 7, .c 3, .c 19, .c 827,
  .c 3, .c 17, .c 13, .c 3, .c 181, .c 5, .c 3, .c 37, .p pv2 [pv2,pv3,pv5,pv19,pv761], .c 3,
  .c 5, .p pv5 [pv2,pv3,pv48197], .c 3, .c 331, .p pv19 [pv2,pv3,pv7,pv1291], .c 3, .c 53, .c 7,
  .c 3, .p pv2 [pv2,pv433781], .c 5, .c 3, .c 103, .p pv17 [pv2,pv3,pv5,pv11,pv239], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv37,pv977], .c 3, .c 11, .c 23, .c 3,
]
private theorem h0105c28 : checkBlock 867331 128 b0105c28 = true := by
  decide +kernel

private def b0105c29 : List Row := [
  .c 7, .p pv2 [pv2,pv3,pv197,pv367], .c 3, .c 29, .c 5, .c 3, .c 83, .c 7, .c 3, .c 5, .c 13,
  .c 3, .c 43, .c 37, .c 3, .p pv3 [pv2,pv19,pv1427], .p pv3 [pv2,pv3,pv16067], .c 3,
  .p pv5 [pv2,pv7,pv29,pv2137], .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv28921], .c 3, .c 5,
  .c 263, .c 3, .p pv3 [pv2,pv5,pv109,pv199], .c 7, .c 3, .c 11, .c 163, .c 3,
  .p pv2 [pv2,pv23,pv9431], .c 5, .c 3, .c 13, .c 89, .c 3, .c 5, .c 47, .c 3, .c 7, .c 19, .c 3,
  .p pv2 [pv2,pv216919], .p pv3 [pv2,pv3,pv7,pv73,pv283], .c 3, .c 41, .c 5, .c 3,
  .p pv3 [pv2,pv108461], .c 11, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv8677], .c 359, .c 3,
  .c 251, .c 29, .c 3, .c 7, .c 5, .c 3, .p pv13 [pv2,pv433859], .c 23, .c 3, .c 5, .c 7, .c 3,
  .c 17, .p pv5 [pv2,pv3,pv167,pv433], .c 3, .c 13, .c 157, .c 3, .p pv5 [pv2,pv271,pv1601], .c 5,
  .c 3, .c 19, .c 73, .c 3, .c 5, .c 11, .c 3, .c 37, .c 13, .c 3, .c 23, .c 7, .c 3,
  .p pv2 [pv2,pv59,pv3677], .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv1607], .c 3, .c 5, .c 19,
  .c 3, .c 127, .p pv5 [pv2,pv3,pv101,pv179], .c 3, .c 7, .c 17, .c 3, .p pv2 [pv2,pv13,pv33377],
  .c 5, .c 3, .c 239, .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv17,pv709], .c 3, .c 227, .c 11, .c 3,
  .p pv2 [pv2,pv43,pv10091], .p pv2 [pv2,pv3,pv13,pv5563], .c 3, .c 17, .c 5, .c 3, .c 7, .c 13,
]
private theorem h0105c29 : checkBlock 867587 128 b0105c29 = true := by
  decide +kernel

private def b0105c30 : List Row := [
  .c 3, .c 5, .c 41, .c 3, .c 67, .c 7, .c 3, .p pv3 [pv2,pv11,pv4931], .c 23, .c 3, .c 19, .c 5,
  .c 3, .c 43, .p pv11 [pv2,pv3,pv5,pv9643], .c 3, .c 5, .c 107, .c 3, .c 7, .c 29, .c 3,
  .p pv5 [pv2,pv433943], .c 11, .c 3, .c 13, .c 5, .c 3, .c 167, .c 17, .c 3, .c 5, .c 31, .c 3,
  .c 11, .p pv5 [pv2,pv3,pv29,pv43], .c 3, .c 449, .c 13, .c 3, .c 7, .c 5, .c 3, .c 41, .c 83,
  .c 3, .c 5, .c 7, .c 3, .c 29, .p pv3 [pv2,pv3,pv16073], .c 3, .p pv2 [pv2,pv37,pv317], .c 47,
  .c 3, .c 113, .c 5, .c 3, .p pv7 [pv2,pv7,pv13,pv19,pv251], .c 283, .c 3, .c 5, .c 109, .c 3,
  .c 13, .c 79, .c 3, .c 11, .c 7, .c 3, .c 37, .c 5, .c 3, .c 883, .p pv11 [pv2,pv3,pv5,pv28933],
  .c 3, .c 5, .c 13, .c 3, .c 311, .c 17, .c 3, .c 7, .c 281, .c 3, .c 271, .c 5, .c 3,
  .p pv2 [pv2,pv434009], .c 7, .c 3, .c 5, .c 353, .c 3, .c 31, .p pv5 [pv2,pv3,pv11,pv137], .c 3,
  .c 17, .p pv7 [pv2,pv3,pv199,pv727], .c 3, .c 11, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv643],
  .c 3, .c 5, .c 29, .c 3, .c 787, .c 7, .c 3, .c 59, .p pv2 [pv2,pv3,pv24113], .c 3,
  .p pv3 [pv2,pv19,pv5711], .c 5, .c 3, .c 773, .p pv13 [pv2,pv3,pv5,pv3617], .c 3, .c 5, .c 11,
  .c 3, .c 7, .c 31, .c 3, .c 83,
]
private theorem h0105c30 : checkBlock 867843 128 b0105c30 = true := by
  decide +kernel

private def b0105c31 : List Row := [
  .c 151, .c 3, .p pv5 [pv2,pv421,pv1031], .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv19,pv1523],
  .c 3, .c 5, .c 71, .c 3, .p pv41 [pv2,pv5,pv11,pv1973], .p pv2 [pv2,pv3,pv17,pv2837], .c 3,
  .c 13, .c 19, .c 3, .c 7, .c 5, .c 3, .c 17, .c 857, .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv97,pv179], .c 11, .c 3, .p pv2 [pv2,pv17,pv751], .c 293, .c 3, .c 263, .c 5,
  .c 3, .c 137, .p pv3 [pv2,pv3,pv5,pv43,pv673], .c 3, .c 5, .p pv5 [pv2,pv3,pv6029], .c 3, .c 23,
  .c 911, .c 3, .c 103, .c 7, .c 3, .c 53, .c 5, .c 3, .p pv13 [pv2,pv107,pv4057], .c 769, .c 3,
  .c 5, .c 17, .c 3, .p pv7 [pv2,pv5,pv7,pv79,pv157], .c 43, .c 3, .c 7, .c 11, .c 3, .c 149,
  .c 5, .c 3, .p pv2 [pv2,pv217057], .c 7, .c 3, .c 5, .c 199, .c 3, .c 11, .c 19, .c 3, .c 97,
  .p pv11 [pv2,pv3,pv31,pv389], .c 3, .c 67, .c 5, .c 3, .c 7, .c 383, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv2297], .c 3, .p pv19 [pv2,pv5,pv13,pv6679], .c 7, .c 3,
  .p pv2 [pv2,pv217069], .c 31, .c 3, .c 13, .c 5, .c 3, .c 29, .p pv2 [pv2,pv3,pv5,pv103,pv281],
  .c 3, .c 5, .c 101, .c 3, .c 7, .c 59, .c 3, .c 11, .c 13, .c 3, .p pv3 [pv2,pv311,pv349], .c 5,
  .c 3, .c 19, .c 487, .c 3, .c 5, .p pv3 [pv2,pv3,pv17,pv8513], .c 3,
  .p pv2 [pv2,pv5,pv71,pv1223], .c 139, .c 3, .p pv3 [pv2,pv7,pv7753], .c 41, .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv13,pv16699], .c 11, .c 3,
]
private theorem h0105c31 : checkBlock 868099 128 b0105c31 = true := by
  decide +kernel

def rows0105 : List Row :=
  b0105c00 ++ b0105c01 ++ b0105c02 ++ b0105c03 ++ b0105c04 ++ b0105c05 ++ b0105c06 ++ b0105c07 ++
  b0105c08 ++ b0105c09 ++ b0105c10 ++ b0105c11 ++ b0105c12 ++ b0105c13 ++ b0105c14 ++ b0105c15 ++
  b0105c16 ++ b0105c17 ++ b0105c18 ++ b0105c19 ++ b0105c20 ++ b0105c21 ++ b0105c22 ++ b0105c23 ++
  b0105c24 ++ b0105c25 ++ b0105c26 ++ b0105c27 ++ b0105c28 ++ b0105c29 ++ b0105c30 ++ b0105c31

attribute [local irreducible] checkBlock checkRows checkPrime

theorem checked0105 : checkBlock 860163 4096 rows0105 = true :=
  checkBlock_append h0105c00 (
    checkBlock_append h0105c01 (
    checkBlock_append h0105c02 (
    checkBlock_append h0105c03 (
    checkBlock_append h0105c04 (
    checkBlock_append h0105c05 (
    checkBlock_append h0105c06 (
    checkBlock_append h0105c07 (
    checkBlock_append h0105c08 (
    checkBlock_append h0105c09 (
    checkBlock_append h0105c10 (
    checkBlock_append h0105c11 (
    checkBlock_append h0105c12 (
    checkBlock_append h0105c13 (
    checkBlock_append h0105c14 (
    checkBlock_append h0105c15 (
    checkBlock_append h0105c16 (
    checkBlock_append h0105c17 (
    checkBlock_append h0105c18 (
    checkBlock_append h0105c19 (
    checkBlock_append h0105c20 (
    checkBlock_append h0105c21 (
    checkBlock_append h0105c22 (
    checkBlock_append h0105c23 (
    checkBlock_append h0105c24 (
    checkBlock_append h0105c25 (
    checkBlock_append h0105c26 (
    checkBlock_append h0105c27 (
    checkBlock_append h0105c28 (
    checkBlock_append h0105c29 (
    checkBlock_append h0105c30 (
    h0105c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
