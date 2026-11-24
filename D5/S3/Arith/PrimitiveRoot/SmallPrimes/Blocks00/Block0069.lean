/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks00/Block0069
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks00/Block0069.checked0069
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table013
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table016
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table017
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table022
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table023
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table036
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table082
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table083

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0069c00 : List Row := [
  .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv233,pv1213], .p pv13 [pv2,pv3,pv5,pv9421], .c 3, .c 5,
  .c 17, .c 3, .c 7, .p pv5 [pv2,pv3,pv2617], .c 3, .c 127, .c 11, .c 3,
  .p pv2 [pv2,pv179,pv1579], .c 5, .c 3, .p pv3 [pv2,pv19,pv3719], .c 449, .c 3, .c 5, .c 29,
  .c 3, .c 11, .p pv3 [pv2,pv3,pv71,pv1327], .c 3, .c 19, .c 457, .c 3, .c 7, .c 5, .c 3,
  .p pv23 [pv2,pv13,pv17,pv1279], .c 43, .c 3, .c 5, .c 7, .c 3, .c 13, .p pv2 [pv2,pv3,pv47111],
  .c 3, .p pv3 [pv2,pv70667], .c 113, .c 3, .p pv5 [pv2,pv282671], .c 5, .c 3, .c 41, .c 53, .c 3,
  .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv37,pv191], .c 23, .c 3, .c 11, .c 7, .c 3, .c 71, .c 5,
  .c 3, .p pv2 [pv2,pv11,pv31,pv829], .p pv2 [pv2,pv3,pv5,pv349], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv17,pv23,pv241], .c 3, .p pv7 [pv2,pv5,pv7,pv41,pv197],
  .p pv5 [pv2,pv3,pv11779], .c 3, .c 7, .c 137, .c 3, .c 17, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .c 89, .c 3, .c 19, .c 743, .c 3, .p pv2 [pv2,pv282713], .p pv2 [pv2,pv3,pv47119], .c 3, .c 11,
  .c 5, .c 3, .c 7, .p pv43 [pv2,pv3,pv5,pv19,pv31], .c 3, .c 5, .c 163, .c 3,
  .p pv2 [pv2,pv5,pv43,pv263], .c 7, .c 3, .c 47, .c 19, .c 3, .p pv5 [pv2,pv167,pv1693], .c 5,
  .c 3, .p pv2 [pv2,pv373,pv379], .c 17, .c 3, .c 5, .c 11, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv79,pv1193], .c 3, .c 13, .p pv13 [pv2,pv3,pv7,pv11,pv17], .c 3, .c 43, .c 5,
  .c 3, .c 11, .c 23, .c 3, .c 5,
]
private theorem h0069c00 : checkBlock 565251 128 b0069c00 = true := by
  decide +kernel

private def b0069c01 : List Row := [
  .p pv2 [pv2,pv3,pv89,pv353], .c 3, .p pv7 [pv2,pv5,pv11,pv53,pv97], .c 13, .c 3,
  .p pv2 [pv2,pv7,pv19,pv1063], .p pv3 [pv2,pv3,pv94253], .c 3, .c 7, .c 5, .c 3, .c 29, .c 61,
  .c 3, .c 5, .c 7, .c 3, .c 601, .c 11, .c 3, .c 23, .p pv7 [pv2,pv3,pv47129], .c 3,
  .p pv3 [pv2,pv13,pv2719], .c 5, .c 3, .p pv7 [pv2,pv7,pv29,pv199], .c 79, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv94261], .c 3, .p pv2 [pv2,pv5,pv23,pv2459], .c 17, .c 3, .c 271, .c 7, .c 3,
  .p pv5 [pv2,pv37,pv7643], .c 5, .c 3, .p pv2 [pv2,pv141397], .c 13, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv5237], .c 3, .c 109, .p pv2 [pv2,pv3,pv107,pv881], .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv141403], .c 5, .c 3, .c 37, .c 7, .c 3, .c 5, .c 241, .c 3, .c 11, .c 59, .c 3,
  .p pv2 [pv2,pv41,pv3449], .c 23, .c 3, .c 13, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv419],
  .c 3, .c 5, .c 31, .c 3, .p pv2 [pv2,pv5,pv28283], .c 7, .c 3, .p pv2 [pv2,pv282833], .c 13,
  .c 3, .c 137, .c 5, .c 3, .c 331, .c 67, .c 3, .c 5, .c 19, .c 3, .c 7, .c 37, .c 3, .c 11,
  .c 479, .c 3, .c 29, .c 5, .c 3, .c 17, .c 443, .c 3, .c 5, .c 283, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv53,pv593], .c 3, .p pv5 [pv2,pv7,pv17,pv2377], .c 349, .c 3, .c 7, .c 5, .c 3,
  .c 47, .c 11, .c 3, .c 5, .c 7, .c 3, .c 43, .c 149, .c 3, .c 199, .c 41, .c 3,
]
private theorem h0069c01 : checkBlock 565507 128 b0069c01 = true := by
  decide +kernel

private def b0069c02 : List Row := [
  .c 11, .c 5, .c 3, .p pv3 [pv2,pv7,pv10103], .p pv17 [pv2,pv3,pv5,pv18859], .c 3, .c 5, .c 17,
  .c 3, .c 31, .c 293, .c 3, .p pv2 [pv2,pv13,pv47,pv463], .c 7, .c 3, .p pv3 [pv2,pv17681], .c 5,
  .c 3, .c 13, .c 19, .c 3, .c 5, .c 11, .c 3, .c 17, .p pv2 [pv2,pv3,pv13,pv31], .c 3, .c 7,
  .c 29, .c 3, .c 23, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 43, .c 3, .c 37, .c 31, .c 3,
  .c 379, .p pv19 [pv2,pv3,pv29,pv271], .c 3, .c 719, .c 5, .c 3, .c 7, .c 571, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv499], .c 3, .c 439, .c 7, .c 3, .c 13, .c 17, .c 3, .c 173, .c 5, .c 3,
  .p pv3 [pv2,pv4421], .p pv3 [pv2,pv3,pv5,pv13,pv1451], .c 3, .c 5, .c 61, .c 3, .c 7, .c 13,
  .c 3, .p pv2 [pv2,pv11,pv29,pv887], .p pv2 [pv2,pv3,pv7,pv6737], .c 3, .c 17, .c 5, .c 3,
  .p pv7 [pv2,pv282959], .p pv7 [pv2,pv3,pv5,pv131], .c 3, .c 5, .c 47, .c 3, .c 433, .c 191,
  .c 3, .p pv3 [pv2,pv7,pv31,pv163], .c 11, .c 3, .c 7, .c 5, .c 3, .c 67, .c 89, .c 3, .c 5,
  .c 7, .c 3, .c 11, .c 167, .c 3, .c 31, .c 73, .c 3, .p pv3 [pv2,pv11,pv19,pv677], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv40427], .c 13, .c 3, .c 5, .c 53, .c 3, .c 19, .c 29, .c 3,
  .p pv2 [pv2,pv141499], .c 7, .c 3, .c 641, .c 5, .c 3, .c 43, .p pv2 [pv2,pv3,pv5,pv19,pv331],
  .c 3, .c 5, .c 113,
]
private theorem h0069c02 : checkBlock 565763 128 b0069c02 = true := by
  decide +kernel

private def b0069c03 : List Row := [
  .c 3, .c 47, .p pv3 [pv2,pv3,pv29,pv3253], .c 3, .c 7, .c 19, .c 3, .c 13, .c 5, .c 3, .c 127,
  .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv41,pv59], .c 3, .c 29, .c 23, .c 3,
  .p pv3 [pv2,pv173,pv409], .c 13, .c 3, .c 37, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv23,pv293], .c 3, .c 659, .c 7, .c 3, .c 41, .p pv11 [pv2,pv3,pv103,pv229],
  .c 3, .c 11, .c 5, .c 3, .c 23, .p pv2 [pv2,pv3,pv5,pv17,pv37], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv94351], .c 3, .c 7, .c 211, .c 3, .c 17, .c 271, .c 3, .c 491, .c 5, .c 3,
  .c 89, .p pv2 [pv2,pv3,pv5,pv113,pv167], .c 3, .c 5, .c 11, .c 3, .c 61, .c 19, .c 3, .c 139,
  .p pv2 [pv2,pv3,pv11,pv4289], .c 3, .c 7, .c 5, .c 3, .c 11, .p pv11 [pv2,pv3,pv5,pv7,pv337],
  .c 3, .c 5, .c 7, .c 3, .c 257, .p pv2 [pv2,pv3,pv15727], .c 3, .c 179,
  .p pv3 [pv2,pv3,pv197,pv479], .c 3, .p pv5 [pv2,pv131,pv2161], .c 5, .c 3, .c 13, .c 23, .c 3,
  .c 5, .c 223, .c 3, .p pv3 [pv2,pv5,pv19,pv149], .c 11, .c 3, .c 683, .c 7, .c 3,
  .p pv2 [pv2,pv353,pv401], .c 5, .c 3, .c 17, .c 137, .c 3, .c 5, .p pv2 [pv2,pv3,pv83,pv379],
  .c 3, .p pv7 [pv2,pv5,pv7,pv8089], .p pv5 [pv2,pv3,pv23593], .c 3, .c 7, .c 263, .c 3, .c 113,
  .c 5, .c 3, .c 463, .c 7, .c 3, .c 5, .c 19, .c 3, .c 73, .c 61, .c 3, .c 13, .c 11, .c 3,
  .p pv3 [pv2,pv7,pv79],
]
private theorem h0069c03 : checkBlock 566019 128 b0069c03 = true := by
  decide +kernel

private def b0069c04 : List Row := [
  .c 5, .c 3, .c 7, .c 367, .c 3, .c 5, .c 17, .c 3, .c 11, .c 7, .c 3, .c 167, .c 157, .c 3,
  .c 47, .c 5, .c 3, .c 83, .p pv13 [pv2,pv3,pv5,pv43,pv439], .c 3, .c 5, .c 229, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv37,pv2551], .c 3, .c 521, .c 23, .c 3, .c 19, .c 5, .c 3, .c 31, .c 29, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv11,pv8581], .c 3, .c 67, .c 43, .c 3, .c 11, .c 37, .c 3, .c 7, .c 5,
  .c 3, .c 293, .c 13, .c 3, .c 5, .c 7, .c 3, .c 487, .c 97, .c 3, .p pv2 [pv2,pv283193], .c 17,
  .c 3, .p pv3 [pv2,pv83,pv853], .c 5, .c 3, .c 29, .c 11, .c 3, .c 5, .c 73, .c 3, .c 53,
  .p pv2 [pv2,pv3,pv7,pv11,pv613], .c 3, .p pv3 [pv2,pv35401], .c 7, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv19,pv29,pv257], .p pv3 [pv2,pv3,pv5,pv79,pv239], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv13,pv3631], .c 3, .p pv3 [pv2,pv5,pv7,pv17], .p pv3 [pv2,pv3,pv31469], .c 3,
  .c 7, .c 13, .c 3, .p pv2 [pv2,pv141613], .c 5, .c 3, .c 59, .c 7, .c 3, .c 5, .c 11, .c 3,
  .c 467, .c 109, .c 3, .c 661, .c 317, .c 3, .c 643, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 41,
  .c 3, .c 13, .c 7, .c 3, .c 37, .c 71, .c 3, .c 23, .c 5, .c 3, .c 397,
  .p pv11 [pv2,pv3,pv5,pv4721], .c 3, .c 5, .c 13, .c 3,
]
private theorem h0069c04 : checkBlock 566275 128 b0069c04 = true := by
  decide +kernel

private def b0069c05 : List Row := [
  .c 7, .c 11, .c 3, .p pv3 [pv2,pv23,pv3079], .p pv2 [pv2,pv3,pv7,pv41,pv47], .c 3,
  .p pv5 [pv2,pv17,pv19,pv877], .c 5, .c 3, .p pv2 [pv2,pv141637], .p pv3 [pv2,pv3,pv5,pv1259],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv31,pv1523], .c 3, .c 19, .p pv2 [pv2,pv3,pv94427], .c 3,
  .p pv5 [pv2,pv7,pv11,pv13,pv283], .c 461, .c 3, .c 7, .c 5, .c 3, .c 13, .c 37, .c 3, .c 5,
  .c 7, .c 3, .c 241, .c 17, .c 3, .c 443, .c 11, .c 3, .c 103, .c 5, .c 3, .c 733, .c 43, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv23609], .c 3, .c 11, .c 53, .c 3, .c 17, .c 7, .c 3,
  .p pv3 [pv2,pv11,pv47,pv137], .c 5, .c 3, .p pv13 [pv2,pv449,pv631], .c 83, .c 3, .c 5, .c 149,
  .c 3, .c 23, .p pv2 [pv2,pv3,pv47221], .c 3, .c 7, .p pv2 [pv2,pv3,pv31481], .c 3, .c 89, .c 5,
  .c 3, .c 239, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv53], .c 3, .p pv3 [pv2,pv5,pv31,pv457],
  .c 13, .c 3, .c 11, .c 29, .c 3, .p pv2 [pv2,pv7,pv37,pv547], .c 5, .c 3, .c 7,
  .p pv17 [pv2,pv3,pv5,pv1889], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv103,pv131], .c 3, .c 31, .c 7,
  .c 3, .p pv2 [pv2,pv141679], .p pv3 [pv2,pv3,pv29,pv3257], .c 3, .p pv2 [pv2,pv13,pv71,pv307],
  .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv11807], .c 3, .c 7, .c 23, .c 3, .c 29,
  .c 439, .c 3, .c 11, .c 5, .c 3, .p pv7 [pv2,pv251,pv1129], .c 13, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv23,pv37], .c 3, .c 97, .c 31, .c 3, .c 281, .c 107, .c 3, .c 7, .c 5,
]
private theorem h0069c05 : checkBlock 566531 128 b0069c05 = true := by
  decide +kernel

private def b0069c06 : List Row := [
  .c 3, .c 19, .p pv7 [pv2,pv3,pv5,pv7,pv2699], .c 3, .c 5, .c 7, .c 3, .c 127, .c 37, .c 3,
  .c 83, .c 103, .c 3, .c 13, .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv47,pv67], .c 3, .c 5,
  .c 19, .c 3, .c 17, .p pv5 [pv2,pv3,pv7,pv241], .c 3, .c 131, .c 7, .c 3, .c 313, .c 5, .c 3,
  .c 283, .p pv2 [pv2,pv3,pv5,pv3779], .c 3, .c 5, .p pv13 [pv2,pv3,pv7873], .c 3, .c 359, .c 11,
  .c 3, .c 7, .c 43, .c 3, .c 61, .c 5, .c 3, .p pv11 [pv2,pv13,pv21803], .c 7, .c 3, .c 5, .c 67,
  .c 3, .c 13, .c 179, .c 3, .c 31, .c 17, .c 3, .c 19, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv6299], .c 3, .c 5, .c 13, .c 3, .c 29, .c 7, .c 3, .c 23, .c 11, .c 3,
  .c 17, .c 5, .c 3, .p pv2 [pv2,pv467,pv607], .c 19, .c 3, .c 5, .p pv3 [pv2,pv3,pv10499], .c 3,
  .c 7, .c 311, .c 3, .c 211, .c 31, .c 3, .p pv2 [pv2,pv11,pv25771], .c 5, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv5,pv18899], .c 3, .c 5, .p pv5 [pv2,pv3,pv2953], .c 3, .c 139, .c 79, .c 3,
  .p pv2 [pv2,pv7,pv40499], .c 41, .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv19,pv43,pv347], .c 17,
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv56701], .p pv2 [pv2,pv3,pv47251], .c 3, .c 11, .c 23,
  .c 3, .c 617, .c 5, .c 3, .c 307, .p pv3 [pv2,pv3,pv5,pv41,pv461], .c 3, .c 5, .c 29, .c 3,
  .c 43,
]
private theorem h0069c06 : checkBlock 566787 128 b0069c06 = true := by
  decide +kernel

private def b0069c07 : List Row := [
  .c 137, .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv17,pv31,pv269], .c 5, .c 3,
  .p pv2 [pv2,pv281,pv1009], .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv29,pv3259], .c 3, .c 41, .c 13,
  .c 3, .c 7, .c 191, .c 3, .c 11, .c 5, .c 3, .c 223, .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv23629],
  .c 3, .p pv2 [pv2,pv5,pv53,pv107], .c 17, .c 3, .p pv2 [pv2,pv283553], .c 701, .c 3, .c 317,
  .c 5, .c 3, .c 7, .p pv29 [pv2,pv3,pv5,pv17,pv139], .c 3, .c 5, .c 11, .c 3, .c 19, .c 7, .c 3,
  .c 17, .c 83, .c 3, .p pv5 [pv2,pv283571], .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 23, .c 3,
  .c 7, .c 197, .c 3, .c 59, .c 19, .c 3, .c 37, .c 5, .c 3, .p pv2 [pv2,pv61,pv4649],
  .p pv11 [pv2,pv3,pv5,pv23,pv137], .c 3, .c 5, .p pv3 [pv2,pv3,pv94531], .c 3, .c 577, .c 11,
  .c 3, .c 89, .c 257, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv70901], .c 29, .c 3, .c 5, .c 7,
  .c 3, .c 103, .c 383, .c 3, .c 193, .c 13, .c 3, .c 229, .c 5, .c 3, .c 17, .c 157, .c 3, .c 5,
  .c 37, .c 3, .c 179, .c 599, .c 3, .p pv3 [pv2,pv17,pv43,pv97], .c 7, .c 3,
  .p pv5 [pv2,pv283631], .c 5, .c 3, .c 29, .c 353, .c 3, .c 5, .p pv2 [pv2,pv3,pv41,pv1153],
  .c 3, .c 11, .c 19, .c 3, .c 7, .c 67, .c 3, .c 569, .c 5, .c 3,
]
private theorem h0069c07 : checkBlock 567043 128 b0069c07 = true := by
  decide +kernel

private def b0069c08 : List Row := [
  .c 43, .c 7, .c 3, .c 5, .c 13, .c 3, .c 691, .c 397, .c 3, .c 41, .p pv3 [pv2,pv3,pv23,pv4111],
  .c 3, .p pv2 [pv2,pv7,pv827], .c 5, .c 3, .c 7, .c 31, .c 3, .c 5, .c 47, .c 3, .c 17, .c 7,
  .c 3, .c 11, .c 199, .c 3, .c 97, .c 5, .c 3, .c 13, .c 61, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv94561], .c 3, .c 7, .c 113, .c 3, .p pv3 [pv2,pv35461], .c 211, .c 3,
  .p pv5 [pv2,pv367,pv773], .c 5, .c 3, .p pv2 [pv2,pv83,pv1709], .c 11, .c 3, .c 5, .c 19, .c 3,
  .p pv11 [pv2,pv5,pv2837], .c 59, .c 3, .p pv7 [pv2,pv7,pv40529], .c 17, .c 3, .c 7, .c 5, .c 3,
  .c 647, .c 107, .c 3, .c 5, .c 7, .c 3, .c 47, .c 23, .c 3, .c 13, .p pv3 [pv2,pv3,pv94573],
  .c 3, .c 17, .c 5, .c 3, .p pv3 [pv2,pv7,pv10133], .p pv2 [pv2,pv3,pv5,pv13,pv97], .c 3, .c 5,
  .c 11, .c 3, .c 191, .c 13, .c 3, .p pv2 [pv2,pv167,pv1699], .c 7, .c 3, .c 19, .c 5, .c 3,
  .c 11, .c 41, .c 3, .c 5, .p pv7 [pv2,pv3,pv31,pv113], .c 3, .c 461,
  .p pv7 [pv2,pv3,pv19,pv131], .c 3, .c 7, .p pv3 [pv2,pv3,pv94583], .c 3, .c 71, .c 5, .c 3,
  .c 541, .c 7, .c 3, .c 5, .c 31, .c 3, .c 59, .c 11, .c 3, .p pv5 [pv2,pv283763],
  .p pv11 [pv2,pv3,pv13,pv17,pv107], .c 3, .p pv2 [pv2,pv7,pv20269], .c 5, .c 3, .c 7, .c 13,
  .c 3, .c 5, .c 97, .c 3, .c 389, .c 7,
]
private theorem h0069c08 : checkBlock 567299 128 b0069c08 = true := by
  decide +kernel

private def b0069c09 : List Row := [
  .c 3, .c 43, .c 29, .c 3, .c 41, .c 5, .c 3, .p pv3 [pv2,pv19,pv1867], .c 23, .c 3, .c 5, .c 53,
  .c 3, .c 7, .c 557, .c 3, .c 19, .c 11, .c 3, .c 13, .c 5, .c 3, .c 113,
  .p pv7 [pv2,pv3,pv5,pv11,pv43], .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv19,pv383], .c 3, .c 11,
  .c 17, .c 3, .c 23, .c 13, .c 3, .c 7, .c 5, .c 3, .c 587, .p pv37 [pv2,pv3,pv5,pv7,pv17,pv53],
  .c 3, .c 5, .c 7, .c 3, .c 31, .c 43, .c 3, .c 17, .p pv7 [pv2,pv3,pv73], .c 3,
  .p pv2 [pv2,pv191,pv743], .c 5, .c 3, .p pv2 [pv2,pv7,pv13,pv3119], .p pv2 [pv2,pv3,pv5,pv9461],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv47,pv61], .c 3, .c 13, .p pv11 [pv2,pv3,pv7,pv31,pv109],
  .c 3, .c 11, .c 7, .c 3, .c 53, .c 5, .c 3, .p pv3 [pv2,pv11,pv6451], .c 37, .c 3, .c 5, .c 13,
  .c 3, .c 19, .c 31, .c 3, .c 7, .c 23, .c 3, .c 47, .c 5, .c 3, .p pv11 [pv2,pv283859], .c 7,
  .c 3, .c 5, .c 41, .c 3, .c 89, .c 29, .c 3, .p pv3 [pv2,pv13,pv53,pv103], .c 19, .c 3, .c 11,
  .c 5, .c 3, .c 7, .p pv37 [pv2,pv3,pv5,pv757], .c 3, .c 5, .c 59, .c 3,
  .p pv3 [pv2,pv5,pv47,pv151], .c 7, .c 3, .p pv5 [pv2,pv17,pv16699], .c 643, .c 3, .c 79, .c 5,
  .c 3, .p pv2 [pv2,pv23,pv12343], .c 109, .c 3, .c 5, .c 11, .c 3, .c 7, .p pv5 [pv2,pv3,pv3943],
  .c 3, .c 181, .c 661, .c 3, .c 83, .c 5, .c 3, .c 11,
]
private theorem h0069c09 : checkBlock 567555 128 b0069c09 = true := by
  decide +kernel

private def b0069c10 : List Row := [
  .p pv2 [pv2,pv3,pv5,pv701], .c 3, .c 5, .c 17, .c 3, .c 233, .c 349, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv15773], .c 3, .c 7, .c 5, .c 3, .c 37, .p pv17 [pv2,pv3,pv5,pv7,pv13], .c 3,
  .c 5, .c 7, .c 3, .c 17, .c 11, .c 3, .p pv3 [pv2,pv35491], .c 269, .c 3,
  .p pv5 [pv2,pv499,pv569], .c 5, .c 3, .c 157, .p pv3 [pv2,pv3,pv5,pv23,pv823], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv37,pv1279], .c 3, .p pv7 [pv2,pv5,pv14197], .p pv2 [pv2,pv3,pv7,pv4507], .c 3,
  .c 503, .c 7, .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv283949], .c 43, .c 3, .c 5, .c 29, .c 3,
  .c 151, .c 37, .c 3, .c 7, .c 11, .c 3, .c 101, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv17,pv29], .c 3, .c 11, .p pv3 [pv2,pv3,pv103,pv919], .c 3,
  .p pv2 [pv2,pv199,pv1427], .p pv2 [pv2,pv3,pv19,pv47,pv53], .c 3, .c 17, .c 5, .c 3, .c 7,
  .p pv19 [pv2,pv3,pv5,pv4733], .c 3, .c 5, .c 19, .c 3, .c 61, .c 7, .c 3, .c 353,
  .p pv3 [pv2,pv3,pv181,pv523], .c 3, .c 13, .c 5, .c 3, .c 383, .p pv3 [pv2,pv3,pv5,pv6311],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv13,pv331], .c 3, .c 7, .c 677, .c 3, .c 11, .c 13, .c 3,
  .c 31, .c 5, .c 3, .p pv7 [pv2,pv11,pv25819], .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv67,pv157],
  .c 3, .c 23, .p pv5 [pv2,pv3,pv61,pv97], .c 3, .c 241, .c 347, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv13,pv2731], .c 11, .c 3, .c 5, .c 7, .c 3, .c 13, .c 107, .c 3,
]
private theorem h0069c10 : checkBlock 567811 128 b0069c10 = true := by
  decide +kernel

private def b0069c11 : List Row := [
  .c 563, .p pv2 [pv2,pv3,pv47339], .c 3, .c 11, .c 5, .c 3, .c 373, .c 19, .c 3, .c 5, .c 13,
  .c 3, .p pv2 [pv2,pv5,pv56809], .c 61, .c 3, .p pv3 [pv2,pv41,pv433], .c 7, .c 3, .c 239, .c 5,
  .c 3, .p pv2 [pv2,pv109,pv1303], .c 59, .c 3, .c 5, .c 11, .c 3, .c 379, .c 17, .c 3, .c 7,
  .c 97, .c 3, .p pv2 [pv2,pv173,pv821], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 131, .c 3,
  .p pv17 [pv2,pv5,pv11,pv1033], .p pv5 [pv2,pv3,pv13,pv607], .c 3, .c 17, .c 43, .c 3,
  .p pv2 [pv2,pv7,pv40583], .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv59,pv107], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv19,pv89], .c 3, .c 227, .c 7, .c 3, .p pv2 [pv2,pv284093],
  .p pv2 [pv2,pv3,pv5261], .c 3, .p pv3 [pv2,pv23,pv193], .c 5, .c 3, .c 31,
  .p pv11 [pv2,pv3,pv5,pv947], .c 3, .c 5, .p pv3 [pv2,pv3,pv31567], .c 3, .c 7, .c 53, .c 3,
  .c 13, .c 41, .c 3, .c 211, .c 5, .c 3, .c 59, .p pv11 [pv2,pv3,pv5,pv13,pv31,pv47], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv47353], .c 3, .p pv3 [pv2,pv5,pv7103], .c 13, .c 3, .c 79, .c 11, .c 3, .c 7,
  .c 5, .c 3, .c 17, .c 23, .c 3, .c 5, .c 7, .c 3, .c 11, .p pv11 [pv2,pv3,pv11839], .c 3, .c 47,
  .p pv17 [pv2,pv3,pv131,pv241], .c 3, .c 37, .c 5, .c 3, .p pv3 [pv2,pv7,pv43,pv59], .c 739,
  .c 3, .c 5, .c 359, .c 3, .c 41, .p pv3 [pv2,pv3,pv7,pv1933], .c 3, .c 23, .c 7, .c 3, .c 29,
  .c 5, .c 3, .c 53, .c 13,
]
private theorem h0069c11 : checkBlock 568067 128 b0069c11 = true := by
  decide +kernel

private def b0069c12 : List Row := [
  .c 3, .c 5, .c 17, .c 3, .c 43, .c 547, .c 3, .c 7, .c 467, .c 3, .c 263, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv12917], .c 7, .c 3, .c 5, .c 37, .c 3, .c 17, .p pv3 [pv2,pv3,pv94727], .c 3,
  .p pv5 [pv2,pv19,pv14957], .c 443, .c 3, .c 13, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv13,pv347], .c 3, .p pv13 [pv2,pv5,pv113,pv503], .c 7, .c 3, .c 269, .c 13,
  .c 3, .c 11, .c 5, .c 3, .c 131, .c 521, .c 3, .c 5, .c 43, .c 3, .c 7, .c 19, .c 3, .c 223,
  .c 17, .c 3, .p pv3 [pv2,pv35527], .c 5, .c 3, .p pv7 [pv2,pv13,pv21863],
  .p pv23 [pv2,pv3,pv5,pv1579], .c 3, .c 5, .c 11, .c 3, .c 13, .p pv11 [pv2,pv3,pv127,pv373],
  .c 3, .c 103, .c 61, .c 3, .c 7, .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv7,pv2707], .c 3, .c 5,
  .c 7, .c 3, .p pv3 [pv2,pv5,pv11,pv17,pv19], .c 367, .c 3, .c 29, .c 431, .c 3,
  .p pv2 [pv2,pv142123], .c 5, .c 3, .c 19, .c 523, .c 3, .c 5, .c 751, .c 3, .c 701, .c 11, .c 3,
  .c 97, .c 7, .c 3, .p pv2 [pv2,pv284261], .c 5, .c 3, .c 13, .c 17, .c 3, .c 5, .c 19, .c 3,
  .p pv11 [pv2,pv5,pv7,pv31,pv131], .c 199, .c 3, .c 7, .p pv2 [pv2,pv3,pv17,pv929], .c 3, .c 509,
  .c 5, .c 3, .c 47, .c 7, .c 3, .c 5, .c 641, .c 3, .c 31, .c 479, .c 3, .p pv3 [pv2,pv2221],
]
private theorem h0069c12 : checkBlock 568323 128 b0069c12 = true := by
  decide +kernel

private def b0069c13 : List Row := [
  .c 11, .c 3, .c 23, .c 5, .c 3, .c 7, .c 541, .c 3, .c 5, .c 73, .c 3, .c 11, .c 7, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv5923], .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv401,pv709], .c 89, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv94771], .c 3, .c 7, .c 13, .c 3, .c 53, .c 71, .c 3,
  .p pv2 [pv2,pv59,pv61,pv79], .c 5, .c 3, .c 139, .c 19, .c 3, .c 5, .p pv7 [pv2,pv3,pv11,pv359],
  .c 3, .c 29, .c 103, .c 3, .c 11, .p pv7 [pv2,pv3,pv47389], .c 3, .c 7, .c 5, .c 3,
  .p pv11 [pv2,pv11,pv25849], .c 277, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv29,pv37,pv53],
  .c 691, .c 3, .c 557, .p pv31 [pv2,pv3,pv13,pv23,pv317], .c 3, .c 61, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv19,pv1069], .c 11, .c 3, .c 5, .c 659, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv7,pv11,pv1231], .c 3, .c 19, .c 7, .c 3, .c 11, .c 5, .c 3, .c 197, .c 257,
  .c 3, .c 5, .c 47, .c 3, .p pv7 [pv2,pv5,pv7,pv13], .c 233, .c 3, .c 7, .c 607, .c 3, .c 13,
  .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 11, .c 3, .c 71, .p pv3 [pv2,pv3,pv3511], .c 3,
  .p pv2 [pv2,pv17,pv16729], .c 13, .c 3, .c 41, .c 5, .c 3, .c 7, .c 37, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv29,pv467], .c 3, .c 157, .c 7, .c 3, .c 151, .c 31, .c 3,
  .p pv5 [pv2,pv19,pv14969], .c 5, .c 3, .c 271, .p pv3 [pv2,pv3,pv5,pv67,pv283], .c 3,
]
private theorem h0069c13 : checkBlock 568579 128 b0069c13 = true := by
  decide +kernel

private def b0069c14 : List Row := [
  .c 5, .c 17, .c 3, .c 7, .c 11, .c 3, .c 43, .c 53, .c 3, .p pv2 [pv2,pv71,pv2003], .c 5, .c 3,
  .c 23, .c 619, .c 3, .c 5, .c 13, .c 3, .c 17, .c 223, .c 3, .p pv2 [pv2,pv7,pv11,pv1847],
  .c 19, .c 3, .c 7, .c 5, .c 3, .c 73, .p pv7 [pv2,pv3,pv5,pv7,pv43], .c 3, .c 5, .c 7, .c 3,
  .c 397, .p pv3 [pv2,pv3,pv53,pv1789], .c 3, .p pv2 [pv2,pv13,pv21881], .c 11, .c 3,
  .p pv3 [pv2,pv31,pv37], .c 5, .c 3, .c 13, .p pv47 [pv2,pv3,pv5,pv11,pv431], .c 3, .c 5, .c 139,
  .c 3, .c 11, .c 43, .c 3, .c 59, .c 7, .c 3, .c 31, .c 5, .c 3, .c 37, .c 23, .c 3, .c 5, .c 41,
  .c 3, .c 137, .p pv2 [pv2,pv3,pv73,pv433], .c 3, .c 7, .c 167, .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv284489], .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv37,pv233], .c 3,
  .p pv13 [pv2,pv5,pv17,pv3347], .c 19, .c 3, .c 11, .p pv3 [pv2,pv3,pv41,pv257], .c 3,
  .p pv2 [pv2,pv7,pv97,pv419], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv13,pv1459], .c 3, .c 5,
  .c 251, .c 3, .p pv2 [pv2,pv5,pv23,pv1237], .c 7, .c 3, .c 463, .c 47, .c 3, .c 163, .c 5, .c 3,
  .c 41, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv94841], .c 3, .c 7, .p pv5 [pv2,pv3,pv11,pv479],
  .c 3, .p pv3 [pv2,pv17783], .c 239, .c 3, .c 11, .c 5, .c 3, .c 19, .p pv3 [pv2,pv3,pv5,pv6323],
  .c 3, .c 5, .p pv5 [pv2,pv3,pv47,pv1009], .c 3, .p pv3 [pv2,pv5,pv41,pv347],
  .p pv3 [pv2,pv3,pv94847], .c 3, .c 127, .c 23,
]
private theorem h0069c14 : checkBlock 568835 128 b0069c14 = true := by
  decide +kernel

private def b0069c15 : List Row := [
  .c 3, .c 7, .c 5, .c 3, .c 97, .c 13, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv56911], .c 283,
  .c 3, .p pv2 [pv2,pv79,pv1801], .c 151, .c 3, .c 47, .c 5, .c 3, .c 11, .c 83, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv71,pv167], .c 3, .p pv3 [pv2,pv5,pv11,pv13,pv199], .c 17, .c 3, .c 601, .c 7,
  .c 3, .c 13, .c 5, .c 3, .p pv13 [pv2,pv23,pv12373], .p pv7 [pv2,pv3,pv5,pv17,pv31], .c 3, .c 5,
  .c 53, .c 3, .c 37, .c 11, .c 3, .c 7, .c 13, .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv142297],
  .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv97,pv163], .c 3, .p pv3 [pv2,pv5,pv1423], .c 41, .c 3,
  .c 71, .p pv29 [pv2,pv3,pv37,pv641], .c 3, .p pv2 [pv2,pv7,pv29,pv701], .c 5, .c 3, .c 7, .c 19,
  .c 3, .c 5, .c 23, .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv101,pv1409], .c 11, .c 3,
  .p pv2 [pv2,pv241,pv1181], .c 5, .c 3, .p pv3 [pv2,pv17789], .p pv3 [pv2,pv3,pv5,pv11,pv23],
  .c 3, .c 5, .c 13, .c 3, .c 7, .p pv3 [pv2,pv3,pv17,pv5581], .c 3, .p pv2 [pv2,pv284633],
  .p pv2 [pv2,pv3,pv7,pv251], .c 3, .c 23, .c 5, .c 3, .c 17, .c 103, .c 3, .c 5, .c 571, .c 3,
  .c 59, .c 97, .c 3, .c 19, .c 29, .c 3, .c 7, .c 5, .c 3, .c 13, .c 47, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv43,pv331], .p pv2 [pv2,pv3,pv13,pv811], .c 3, .c 11, .c 149, .c 3, .c 89,
  .c 5, .c 3, .c 199, .c 127, .c 3, .c 5,
]
private theorem h0069c15 : checkBlock 569091 128 b0069c15 = true := by
  decide +kernel

private def b0069c16 : List Row := [
  .c 17, .c 3, .c 431, .c 79, .c 3, .c 29, .c 7, .c 3, .c 43, .c 5, .c 3, .p pv3 [pv2,pv71171],
  .c 11, .c 3, .c 5, .c 31, .c 3, .c 17, .c 439, .c 3, .c 7, .c 353, .c 3, .c 11, .c 5, .c 3,
  .c 179, .c 7, .c 3, .c 5, .c 113, .c 3, .c 19, .c 13, .c 3, .p pv3 [pv2,pv109,pv653],
  .p pv2 [pv2,pv3,pv94903], .c 3, .p pv5 [pv2,pv7,pv89,pv457], .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv19,pv37], .c 3, .c 5, .c 11, .c 3, .c 311, .c 7, .c 3,
  .p pv5 [pv2,pv284723], .c 17, .c 3, .c 521, .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv9491],
  .c 3, .c 5, .c 37, .c 3, .c 7, .c 29, .c 3, .c 613, .p pv3 [pv2,pv3,pv7,pv13,pv149], .c 3,
  .c 17, .c 5, .c 3, .c 211, .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv61,pv389], .c 3, .c 31, .c 11,
  .c 3, .p pv2 [pv2,pv7,pv19,pv2141], .c 137, .c 3, .c 7, .c 5, .c 3, .c 251, .c 383, .c 3, .c 5,
  .c 7, .c 3, .c 29, .p pv2 [pv2,pv3,pv31,pv1531], .c 3, .c 239, .c 101, .c 3, .c 13, .c 5, .c 3,
  .c 23, .c 17, .c 3, .c 5, .c 61, .c 3, .c 107, .c 19, .c 3, .c 67, .c 7, .c 3,
  .p pv2 [pv2,pv23,pv41,pv151], .c 5, .c 3, .p pv2 [pv2,pv37,pv43,pv179],
  .p pv2 [pv2,pv3,pv5,pv11,pv863], .c 3, .c 5, .c 281, .c 3, .c 11, .c 47, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv94933], .c 3,
]
private theorem h0069c16 : checkBlock 569347 128 b0069c16 = true := by
  decide +kernel

private def b0069c17 : List Row := [
  .p pv5 [pv2,pv11,pv17,pv1523], .c 5, .c 3, .p pv7 [pv2,pv13,pv5477], .c 7, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv11867], .c 3, .c 13, .p pv3 [pv2,pv3,pv139,pv683], .c 3, .c 149, .c 83, .c 3,
  .c 71, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 13, .c 3, .c 331, .c 7, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv19,pv263], .c 3, .p pv5 [pv2,pv284831], .c 5, .c 3, .c 79,
  .p pv3 [pv2,pv3,pv5,pv17,pv1117], .c 3, .c 5, .c 19, .c 3, .c 7, .p pv3 [pv2,pv3,pv31649], .c 3,
  .c 17, .c 37, .c 3, .c 103, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 43, .c 3,
  .p pv7 [pv2,pv5,pv23,pv2477], .p pv29 [pv2,pv3,pv11,pv13,pv83], .c 3, .p pv2 [pv2,pv7,pv20347],
  .c 131, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv4451], .p pv2 [pv2,pv3,pv5,pv7,pv2713], .c 3,
  .c 5, .c 7, .c 3, .c 101, .c 109, .c 3, .p pv2 [pv2,pv113,pv2521], .c 31, .c 3, .c 19, .c 5,
  .c 3, .p pv7 [pv2,pv7,pv40697], .c 139, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv227,pv251],
  .p pv2 [pv2,pv3,pv7,pv17,pv19], .c 3, .c 13, .c 7, .c 3, .c 137, .c 5, .c 3, .c 11, .c 19, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv103,pv461], .c 3, .c 61, .c 13, .c 3, .c 7, .p pv17 [pv2,pv3,pv1319],
  .c 3, .p pv2 [pv2,pv142453], .c 5, .c 3, .p pv2 [pv2,pv41,pv6949], .c 7, .c 3, .c 5, .c 79,
  .c 3, .p pv11 [pv2,pv5,pv56983], .c 11, .c 3, .c 37, .p pv3 [pv2,pv3,pv73,pv1301], .c 3,
  .p pv2 [pv2,pv7,pv13,pv31,pv101], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv29,pv131], .c 3, .c 5,
  .c 17,
]
private theorem h0069c17 : checkBlock 569603 128 b0069c17 = true := by
  decide +kernel

private def b0069c18 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv28493], .c 7, .c 3, .c 19, .p pv19 [pv2,pv3,pv13,pv281], .c 3, .c 31,
  .c 5, .c 3, .c 29, .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv19,pv4999], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv47491], .c 3, .p pv3 [pv2,pv71237], .c 11, .c 3, .p pv5 [pv2,pv67,pv4253],
  .c 5, .c 3, .c 53, .c 37, .c 3, .c 5, .c 23, .c 3, .c 11, .c 61, .c 3, .p pv5 [pv2,pv7,pv40709],
  .c 193, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv284969], .c 41, .c 3, .c 5, .c 7, .c 3, .c 367,
  .c 463, .c 3, .p pv2 [pv2,pv89,pv1601], .c 13, .c 3, .c 23, .c 5, .c 3, .c 47, .c 167, .c 3,
  .c 5, .c 587, .c 3, .c 19, .p pv3 [pv2,pv3,pv7,pv41,pv331], .c 3, .c 11, .c 7, .c 3, .c 17,
  .c 5, .c 3, .c 59, .p pv41 [pv2,pv3,pv5,pv19], .c 3, .c 5, .c 647, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv47501], .c 3, .c 7, .c 19, .c 3, .c 41, .c 5, .c 3, .p pv2 [pv2,pv31,pv4597],
  .c 7, .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv14251], .p pv3 [pv2,pv3,pv11,pv2879], .c 3,
  .p pv5 [pv2,pv285023], .p pv23 [pv2,pv3,pv2969], .c 3, .c 11, .c 5, .c 3, .c 7, .c 17, .c 3,
  .c 5, .c 157, .c 3, .p pv13 [pv2,pv5,pv109,pv523], .c 7, .c 3, .p pv2 [pv2,pv13,pv19,pv577],
  .p pv3 [pv2,pv3,pv17,pv23], .c 3, .p pv2 [pv2,pv29,pv9829], .c 5, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv5,pv31,pv613], .c 3, .c 5, .c 11, .c 3, .c 7, .c 67, .c 3,
  .p pv2 [pv2,pv61,pv4673], .p pv2 [pv2,pv3,pv7,pv11,pv617], .c 3, .p pv3 [pv2,pv17,pv131],
]
private theorem h0069c18 : checkBlock 569859 128 b0069c18 = true := by
  decide +kernel

private def b0069c19 : List Row := [
  .c 5, .c 3, .c 11, .c 31, .c 3, .c 5, .c 83, .c 3, .p pv11 [pv2,pv5,pv11,pv71,pv73], .c 19,
  .c 3, .c 43, .p pv2 [pv2,pv3,pv167,pv569], .c 3, .c 7, .c 5, .c 3, .c 281, .c 233, .c 3, .c 5,
  .c 7, .c 3, .p pv3 [pv2,pv5,pv7127], .c 11, .c 3, .c 13, .c 29, .c 3, .p pv2 [pv2,pv142543],
  .c 5, .c 3, .c 109, .p pv7 [pv2,pv3,pv5,pv13,pv17,pv43], .c 3, .c 5, .c 41, .c 3,
  .p pv13 [pv2,pv5,pv19,pv3001], .c 13, .c 3, .c 17, .c 7, .c 3, .c 73, .c 5, .c 3, .c 19, .c 223,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv23,pv1033], .c 3, .p pv2 [pv2,pv5,pv7,pv4073], .c 43, .c 3, .c 7,
  .c 11, .c 3, .p pv3 [pv2,pv13,pv5483], .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 19, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv47521], .c 3, .c 461, .c 419, .c 3, .c 97, .c 5, .c 3, .c 7, .c 13, .c 3,
  .c 5, .c 487, .c 3, .c 37, .c 7, .c 3, .c 383, .c 61, .c 3, .c 83, .c 5, .c 3, .c 17, .c 79,
  .c 3, .c 5, .c 31, .c 3, .c 7, .c 331, .c 3, .c 11, .c 563, .c 3, .c 13, .c 5, .c 3,
  .p pv3 [pv2,pv11,pv6481], .c 23, .c 3, .c 5, .c 163, .c 3, .c 643, .c 29, .c 3, .c 101, .c 13,
  .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv285179], .c 11, .c 3, .c 5, .c 7, .c 3,
]
private theorem h0069c19 : checkBlock 570115 128 b0069c19 = true := by
  decide +kernel

private def b0069c20 : List Row := [
  .c 67, .p pv2 [pv2,pv3,pv11,pv29,pv149], .c 3, .c 23, .p pv3 [pv2,pv3,pv95063], .c 3, .c 11,
  .c 5, .c 3, .p pv11 [pv2,pv7,pv13,pv1567], .p pv17 [pv2,pv3,pv5,pv19013], .c 3, .c 5, .c 109,
  .c 3, .c 13, .p pv3 [pv2,pv3,pv7,pv503], .c 3, .p pv5 [pv2,pv307,pv929], .c 7, .c 3,
  .p pv2 [pv2,pv59,pv2417], .c 5, .c 3, .p pv2 [pv2,pv17,pv19,pv883], .p pv7 [pv2,pv3,pv5,pv3169],
  .c 3, .c 5, .c 11, .c 3, .c 31, .c 41, .c 3, .c 7, .c 47, .c 3, .c 661, .c 5, .c 3, .c 11, .c 7,
  .c 3, .c 5, .c 97, .c 3, .p pv7 [pv2,pv5,pv11,pv2593], .p pv3 [pv2,pv3,pv31,pv3067], .c 3,
  .p pv2 [pv2,pv13,pv37,pv593], .c 17, .c 3, .c 179, .c 5, .c 3, .c 7, .c 43, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv17,pv47], .c 3, .p pv11 [pv2,pv5,pv89,pv641], .c 7, .c 3,
  .p pv3 [pv2,pv4457], .p pv2 [pv2,pv3,pv95083], .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv193,pv739], .p pv3 [pv2,pv3,pv5,pv2113], .c 3, .c 5, .c 29, .c 3, .c 7, .c 251,
  .c 3, .p pv5 [pv2,pv11,pv25933], .p pv13 [pv2,pv3,pv7,pv283], .c 3, .c 47, .c 5, .c 3,
  .p pv2 [pv2,pv23,pv79,pv157], .c 337, .c 3, .c 5, .p pv2 [pv2,pv3,pv29,pv1093], .c 3, .c 19,
  .p pv19 [pv2,pv3,pv23773], .c 3, .c 13, .c 11, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv73,pv977],
  .c 17, .c 3, .c 5, .c 7, .c 3, .c 11, .c 13, .c 3, .p pv2 [pv2,pv31,pv9203], .c 19, .c 3,
  .c 523, .c 5, .c 3, .c 313, .p pv29 [pv2,pv3,pv5,pv317], .c 3, .c 5, .c 23, .c 3, .c 127,
  .p pv2 [pv2,pv3,pv7,pv6793], .c 3, .c 31, .c 7, .c 3, .c 401, .c 5,
]
private theorem h0069c20 : checkBlock 570371 128 b0069c20 = true := by
  decide +kernel

private def b0069c21 : List Row := [
  .c 3, .c 151, .c 107, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv131], .c 3, .c 73,
  .p pv5 [pv2,pv3,pv95107], .c 3, .c 7, .p pv11 [pv2,pv3,pv13,pv31,pv59], .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv25939], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv95111], .c 3,
  .p pv19 [pv2,pv5,pv149,pv383], .c 17, .c 3, .p pv2 [pv2,pv23,pv6203], .c 31, .c 3,
  .p pv2 [pv2,pv7,pv40763], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .p pv17 [pv2,pv3,pv7,pv43,pv79],
  .c 3, .c 193, .c 7, .c 3, .c 17, .c 197, .c 3, .c 11, .c 5, .c 3, .p pv7 [pv2,pv461,pv619],
  .c 47, .c 3, .c 5, .c 173, .c 3, .c 7, .p pv2 [pv2,pv3,pv199,pv239], .c 3, .p pv3 [pv2,pv35671],
  .c 13, .c 3, .p pv5 [pv2,pv137,pv2083], .c 5, .c 3, .c 29, .c 101, .c 3, .c 5, .c 11, .c 3,
  .c 41, .c 113, .c 3, .c 131, .c 71, .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv17 [pv2,pv3,pv5,pv7,pv151], .c 3, .c 5, .c 7, .c 3, .c 13, .c 457, .c 3, .c 257, .c 37,
  .c 3, .c 31, .c 5, .c 3, .c 17, .c 283, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv28541],
  .c 11, .c 3, .p pv2 [pv2,pv17,pv103,pv163], .c 7, .c 3, .c 109, .c 5, .c 3,
  .p pv11 [pv2,pv61,pv4679], .p pv7 [pv2,pv3,pv5,pv67,pv71], .c 3, .c 5, .c 599, .c 3,
  .p pv7 [pv2,pv5,pv7,pv233], .p pv5 [pv2,pv3,pv101,pv157], .c 3, .c 7, .p pv3 [pv2,pv3,pv95143],
  .c 3, .c 53, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv223],
]
private theorem h0069c21 : checkBlock 570627 128 b0069c21 = true := by
  decide +kernel

private def b0069c22 : List Row := [
  .c 23, .c 3, .p pv5 [pv2,pv397,pv719], .c 11, .c 3, .c 19, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv11,pv173], .c 3, .c 5, .c 67, .c 3, .c 11, .c 7, .c 3, .c 317,
  .p pv13 [pv2,pv3,pv95153], .c 3, .c 29, .c 5, .c 3, .c 23, .c 19, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv23789], .c 3, .c 7, .c 59, .c 3, .c 13, .p pv13 [pv2,pv3,pv7,pv971], .c 3,
  .c 101, .c 5, .c 3, .p pv7 [pv2,pv31,pv9209], .p pv7 [pv2,pv3,pv5,pv13,pv61], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv41,pv211], .c 3, .c 239, .c 13, .c 3, .c 11, .c 17, .c 3, .c 7, .c 5,
  .c 3, .c 31, .p pv3 [pv2,pv3,pv5,pv7,pv2719], .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv571],
  .c 47, .c 3, .c 19, .c 157, .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv7,pv40787], .c 11, .c 3,
  .c 5, .c 443, .c 3, .p pv13 [pv2,pv5,pv17,pv3359], .c 491, .c 3, .p pv2 [pv2,pv142759], .c 7,
  .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv41,pv1741], .c 13, .c 3, .c 5, .c 293, .c 3, .c 59,
  .c 373, .c 3, .c 7, .p pv2 [pv2,pv3,pv29,pv547], .c 3, .c 173, .c 5, .c 3, .c 73, .c 7, .c 3,
  .c 5, .c 11, .c 3, .c 79, .p pv2 [pv2,pv3,pv47591], .c 3, .c 29,
  .p pv7 [pv2,pv3,pv11,pv17,pv509], .c 3, .c 13, .c 5, .c 3, .c 7, .p pv19 [pv2,pv3,pv5,pv19037],
  .c 3, .c 5, .c 149, .c 3, .c 19, .c 7, .c 3, .c 433, .c 13, .c 3, .p pv2 [pv2,pv17,pv37,pv227],
  .c 5, .c 3,
]
private theorem h0069c22 : checkBlock 570883 128 b0069c22 = true := by
  decide +kernel

private def b0069c23 : List Row := [
  .c 439, .c 467, .c 3, .c 5, .p pv2 [pv2,pv3,pv95191], .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv142789], .c 19, .c 3, .p pv2 [pv2,pv347,pv823], .c 5, .c 3, .c 37, .c 41, .c 3,
  .c 5, .c 211, .c 3, .c 13, .c 17, .c 3, .c 607, .c 179, .c 3, .c 7, .c 5, .c 3,
  .p pv13 [pv2,pv285599], .p pv29 [pv2,pv3,pv5,pv7,pv17], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv239], .c 29, .c 3, .c 17, .c 11, .c 3, .p pv5 [pv2,pv285611], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv23,pv887], .p pv13 [pv2,pv3,pv5,pv11,pv577], .c 3, .c 5, .c 31, .c 3, .c 11,
  .c 37, .c 3, .c 739, .c 7, .c 3, .c 41, .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv9521], .c 3,
  .c 5, .p pv3 [pv2,pv3,pv71,pv149], .c 3, .c 29, .c 19, .c 3, .c 7, .p pv3 [pv2,pv3,pv95213],
  .c 3, .c 397, .c 5, .c 3, .c 83, .c 7, .c 3, .c 5, .c 23, .c 3, .c 647,
  .p pv3 [pv2,pv3,pv17,pv1867], .c 3, .c 11, .c 67, .c 3, .c 349, .c 5, .c 3, .c 7,
  .p pv19 [pv2,pv3,pv5,pv23], .c 3, .c 5, .c 307, .c 3, .p pv2 [pv2,pv5,pv19,pv31,pv97], .c 7,
  .c 3, .c 13, .p pv3 [pv2,pv3,pv31741], .c 3, .c 23, .c 5, .c 3, .c 19, .c 11, .c 3, .c 5,
  .c 101, .c 3, .c 7, .c 13, .c 3, .c 743, .p pv11 [pv2,pv3,pv7,pv19,pv179], .c 3, .c 11, .c 5,
  .c 3, .c 47, .p pv2 [pv2,pv3,pv5,pv89,pv107], .c 3, .c 5, .c 17, .c 3, .c 37, .c 53,
]
private theorem h0069c23 : checkBlock 571139 128 b0069c23 = true := by
  decide +kernel

private def b0069c24 : List Row := [
  .c 3, .p pv2 [pv2,pv7,pv20407], .p pv3 [pv2,pv3,pv95233], .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv71,pv503], .c 241, .c 3, .c 5, .c 7, .c 3, .c 17, .c 31, .c 3, .c 43, .c 139,
  .c 3, .p pv3 [pv2,pv71429], .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 479, .c 3, .c 277,
  .p pv5 [pv2,pv3,pv7,pv6803], .c 3, .c 691, .c 7, .c 3, .c 19, .c 5, .c 3, .c 89,
  .p pv3 [pv2,pv3,pv5,pv43,pv443], .c 3, .c 5, .p pv2 [pv2,pv3,pv47623], .c 3, .c 23, .c 11, .c 3,
  .c 7, .c 17, .c 3, .c 13, .c 5, .c 3, .c 41, .c 7, .c 3, .c 5, .c 353, .c 3, .c 751, .c 43,
  .c 3, .c 73, .c 13, .c 3, .c 17, .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv19051], .c 3, .c 5,
  .c 521, .c 3, .p pv7 [pv2,pv5,pv17,pv41], .c 7, .c 3, .c 31, .c 11, .c 3, .c 131, .c 5, .c 3,
  .c 101, .c 29, .c 3, .c 5, .c 47, .c 3, .c 7, .c 23, .c 3, .c 19,
  .p pv7 [pv2,pv3,pv7,pv31,pv439], .c 3, .p pv5 [pv2,pv11,pv25981], .c 5, .c 3,
  .p pv2 [pv2,pv142897], .c 17, .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv1429],
  .p pv2 [pv2,pv3,pv95267], .c 3, .c 509, .c 31, .c 3, .c 7, .c 5, .c 3, .c 23, .c 71, .c 3, .c 5,
  .c 7, .c 3, .c 61, .p pv5 [pv2,pv3,pv11909], .c 3, .c 11, .c 523, .c 3, .c 293, .c 5, .c 3,
  .c 13,
]
private theorem h0069c24 : checkBlock 571395 128 b0069c24 = true := by
  decide +kernel

private def b0069c25 : List Row := [
  .c 59, .c 3, .c 5, .p pv13 [pv2,pv3,pv23819], .c 3, .c 47, .c 41, .c 3, .c 113, .c 7, .c 3,
  .p pv3 [pv2,pv19,pv3761], .c 5, .c 3, .p pv11 [pv2,pv285839], .c 11, .c 3, .c 5, .c 37, .c 3,
  .c 19, .c 17, .c 3, .c 7, .p pv7 [pv2,pv3,pv3529], .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv47,pv3041], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv15881], .c 3,
  .p pv3 [pv2,pv5,pv14293], .c 79, .c 3, .c 13, .c 19, .c 3, .c 31, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv13,pv733], .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv2287], .c 7, .c 3,
  .c 23, .p pv3 [pv2,pv3,pv11,pv8663], .c 3, .c 71, .c 5, .c 3, .c 11, .c 43, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv1489], .c 3, .c 7, .p pv3 [pv2,pv3,pv233,pv409], .c 3, .c 83,
  .p pv71 [pv2,pv3,pv7,pv2269], .c 3, .c 29, .c 5, .c 3, .p pv7 [pv2,pv37,pv7727],
  .p pv11 [pv2,pv3,pv5,pv953], .c 3, .c 5, .c 577, .c 3, .p pv2 [pv2,pv5,pv211,pv271], .c 11,
  .c 3, .c 53, .c 383, .c 3, .c 7, .c 5, .c 3, .c 17, .c 13, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv1787], .c 19, .c 3, .p pv5 [pv2,pv11,pv17,pv139], .c 23, .c 3,
  .p pv2 [pv2,pv142963], .c 5, .c 3, .c 193, .p pv2 [pv2,pv3,pv5,pv353], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv95311], .c 3, .p pv11 [pv2,pv5,pv13,pv53,pv83],
  .p pv5 [pv2,pv3,pv7,pv23,pv37], .c 3, .p pv2 [pv2,pv142969], .c 7, .c 3, .c 13, .c 5, .c 3,
  .c 337, .c 197, .c 3, .c 5, .c 17, .c 3, .c 11, .p pv13 [pv2,pv3,pv95317], .c 3,
]
private theorem h0069c25 : checkBlock 571651 128 b0069c25 = true := by
  decide +kernel

private def b0069c26 : List Row := [
  .c 7, .c 13, .c 3, .c 443, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 239, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv15887], .c 3, .c 431, .p pv2 [pv2,pv3,pv19,pv29,pv173], .c 3, .c 43, .c 5,
  .c 3, .c 7, .c 157, .c 3, .c 5, .c 19, .c 3, .c 13, .c 7, .c 3, .c 11, .p pv13 [pv2,pv3,pv331],
  .c 3, .p pv2 [pv2,pv142993], .c 5, .c 3, .c 67, .c 31, .c 3, .c 5, .c 13, .c 3, .c 7, .c 433,
  .c 3, .c 61, .c 17, .c 3, .c 89, .c 5, .c 3, .c 97, .c 11, .c 3, .c 5, .c 439, .c 3, .c 211,
  .p pv5 [pv2,pv3,pv11,pv107], .c 3, .p pv2 [pv2,pv7,pv13,pv449], .c 43, .c 3, .c 7, .c 5, .c 3,
  .c 13, .p pv11 [pv2,pv3,pv5,pv7,pv227], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv17,pv673],
  .p pv2 [pv2,pv3,pv13,pv19,pv193], .c 3, .c 37, .p pv2 [pv2,pv3,pv61,pv521], .c 3,
  .p pv5 [pv2,pv103,pv2777], .c 5, .c 3, .p pv2 [pv2,pv7,pv20431], .c 19, .c 3, .c 5, .c 11, .c 3,
  .c 271, .c 29, .c 3, .p pv5 [pv2,pv286043], .c 7, .c 3, .p pv2 [pv2,pv89,pv1607], .c 5, .c 3,
  .c 11, .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv97,pv983], .c 3, .c 173, .c 67, .c 3, .c 7, .c 61,
  .c 3, .c 59, .c 5, .c 3, .c 107, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv31,pv769], .c 3, .c 29,
  .c 11, .c 3, .c 19, .c 727, .c 3, .c 367, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv149],
]
private theorem h0069c26 : checkBlock 571907 128 b0069c26 = true := by
  decide +kernel

private def b0069c27 : List Row := [
  .c 3, .c 5, .c 31, .c 3, .c 23, .c 7, .c 3, .p pv3 [pv2,pv11,pv3251],
  .p pv2 [pv2,pv3,pv47,pv2029], .c 3, .p pv5 [pv2,pv13,pv59,pv373], .c 5, .c 3, .c 71, .c 409,
  .c 3, .c 5, .c 79, .c 3, .c 7, .c 17, .c 3, .p pv5 [pv2,pv286103], .c 11, .c 3, .c 353, .c 5,
  .c 3, .c 389, .c 13, .c 3, .c 5, .c 401, .c 3, .c 11, .p pv11 [pv2,pv3,pv113,pv211], .c 3,
  .c 17, .p pv13 [pv2,pv3,pv10597], .c 3, .c 7, .c 5, .c 3, .c 137,
  .p pv11 [pv2,pv3,pv5,pv7,pv109], .c 3, .c 5, .c 7, .c 3, .c 19, .c 23, .c 3, .c 227,
  .p pv7 [pv2,pv3,pv103,pv463], .c 3, .c 13, .c 5, .c 3, .c 37, .p pv7 [pv2,pv3,pv5,pv19,pv251],
  .c 3, .c 5, .c 43, .c 3, .c 31, .c 163, .c 3, .c 11, .c 7, .c 3, .p pv5 [pv2,pv61,pv4691], .c 5,
  .c 3, .c 23, .p pv3 [pv2,pv3,pv5,pv6359], .c 3, .c 5, .c 631, .c 3, .p pv3 [pv2,pv5,pv7,pv73],
  .p pv2 [pv2,pv3,pv17,pv31,pv181], .c 3, .c 7, .p pv23 [pv2,pv3,pv7949], .c 3,
  .p pv2 [pv2,pv23,pv6221], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 53, .c 3, .c 13, .c 31, .c 3,
  .p pv2 [pv2,pv17,pv19,pv443], .c 59, .c 3, .c 11, .c 5, .c 3, .c 7, .c 103, .c 3, .c 5, .c 13,
  .c 3, .c 67, .c 7, .c 3, .p pv2 [pv2,pv137,pv2089], .c 127, .c 3, .c 73, .c 5, .c 3,
  .p pv7 [pv2,pv286199], .c 23, .c 3, .c 5, .c 11, .c 3, .c 7, .c 19, .c 3,
  .p pv3 [pv2,pv13,pv43],
]
private theorem h0069c27 : checkBlock 572163 128 b0069c27 = true := by
  decide +kernel

private def b0069c28 : List Row := [
  .p pv3 [pv2,pv3,pv7,pv11,pv59], .c 3, .p pv5 [pv2,pv157,pv1823], .c 5, .c 3, .c 11, .c 29, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv15901], .c 3, .c 17, .c 211, .c 3, .c 23, .p pv7 [pv2,pv3,pv67,pv89],
  .c 3, .c 7, .c 5, .c 3, .c 43, .p pv23 [pv2,pv3,pv5,pv7,pv29,pv47], .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv19,pv23,pv131], .c 11, .c 3, .c 31, .p pv3 [pv2,pv3,pv95413], .c 3, .c 41,
  .c 5, .c 3, .c 19, .p pv2 [pv2,pv3,pv5,pv6361], .c 3, .c 5, .p pv5 [pv2,pv3,pv11927], .c 3,
  .c 37, .c 181, .c 3, .c 13, .c 7, .c 3, .c 79, .c 5, .c 3, .p pv17 [pv2,pv29,pv9871],
  .p pv7 [pv2,pv3,pv5,pv13,pv367], .c 3, .c 5, .c 19, .c 3, .c 251, .c 13, .c 3, .c 7, .c 11,
  .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv143137], .c 7, .c 3, .c 5, .c 107, .c 3, .c 11, .c 337,
  .c 3, .p pv5 [pv2,pv353,pv811], .c 101, .c 3, .p pv2 [pv2,pv7,pv11,pv13], .c 5, .c 3, .c 7,
  .p pv37 [pv2,pv3,pv5,pv3181], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv13633], .c 3, .c 97, .c 7, .c 3,
  .p pv2 [pv2,pv257,pv557], .p pv17 [pv2,pv3,pv13,pv2447], .c 3, .c 19, .c 5, .c 3,
  .p pv3 [pv2,pv23,pv389], .c 13, .c 3, .c 5, .c 83, .c 3, .c 7, .c 271, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv7,pv17,pv401], .c 3, .p pv3 [pv2,pv31,pv2309], .c 5, .c 3,
  .p pv7 [pv2,pv11,pv26029], .c 19, .c 3, .c 5, .c 41, .c 3, .p pv2 [pv2,pv5,pv13,pv881],
  .p pv2 [pv2,pv3,pv15907], .c 3, .p pv3 [pv2,pv7,pv5113], .p pv2 [pv2,pv3,pv95443], .c 3, .c 7,
  .c 5, .c 3, .c 379, .c 11, .c 3,
]
private theorem h0069c28 : checkBlock 572419 128 b0069c28 = true := by
  decide +kernel

private def b0069c29 : List Row := [
  .c 5, .c 7, .c 3, .c 653, .p pv2 [pv2,pv3,pv11,pv8677], .c 3, .p pv5 [pv2,pv37,pv71,pv109],
  .c 13, .c 3, .c 11, .c 5, .c 3, .p pv7 [pv2,pv7,pv19,pv2153], .c 269, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv31817], .c 3, .p pv29 [pv2,pv5,pv57271], .c 17, .c 3, .c 19, .c 7, .c 3,
  .c 23, .c 5, .c 3, .c 41, .c 463, .c 3, .c 5, .c 11, .c 3, .c 13, .c 151, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv11,pv4339], .c 3, .c 601, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 13, .c 3,
  .c 53, .c 419, .c 3, .p pv3 [pv2,pv71597], .c 29, .c 3, .c 67, .c 5, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv5,pv61,pv313], .c 3, .c 5, .c 37, .c 3, .p pv3 [pv2,pv5,pv179], .c 7, .c 3,
  .p pv5 [pv2,pv13,pv22031], .c 191, .c 3, .p pv2 [pv2,pv19,pv7537], .c 5, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv5,pv9547], .c 3, .c 5, .p pv2 [pv2,pv3,pv95471], .c 3, .c 7,
  .p pv11 [pv2,pv3,pv13,pv17], .c 3, .c 29, .c 691, .c 3, .p pv2 [pv2,pv286421], .c 5, .c 3,
  .c 17, .c 61, .c 3, .c 5, .c 241, .c 3, .c 23, .c 131, .c 3, .p pv2 [pv2,pv7,pv17,pv29,pv83],
  .c 11, .c 3, .c 7, .c 5, .c 3, .p pv13 [pv2,pv107,pv2677], .p pv23 [pv2,pv3,pv5,pv7,pv11,pv31],
  .c 3, .c 5, .c 7, .c 3, .c 11, .c 41, .c 3, .c 13, .c 71, .c 3, .p pv5 [pv2,pv11,pv26041], .c 5,
  .c 3, .p pv2 [pv2,pv7,pv37,pv79], .c 31, .c 3, .c 5, .c 17, .c 3, .c 199, .c 13, .c 3,
  .p pv5 [pv2,pv19,pv15077], .c 7,
]
private theorem h0069c29 : checkBlock 572675 128 b0069c29 = true := by
  decide +kernel

private def b0069c30 : List Row := [
  .c 3, .p pv2 [pv2,pv43,pv3331], .c 5, .c 3, .p pv2 [pv2,pv286469], .p pv11 [pv2,pv3,pv5,pv1061],
  .c 3, .c 5, .c 233, .c 3, .c 17, .c 23, .c 3, .c 7, .c 281, .c 3, .p pv5 [pv2,pv13,pv22037],
  .c 5, .c 3, .p pv3 [pv2,pv11,pv17,pv383], .c 7, .c 3, .c 5, .c 47, .c 3, .c 421, .c 19, .c 3,
  .c 79, .c 103, .c 3, .p pv3 [pv2,pv7,pv1279], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv1949], .c 3, .c 29, .c 7, .c 3, .c 193, .c 17, .c 3, .c 11, .c 5, .c 3,
  .c 401, .p pv17 [pv2,pv3,pv5,pv6367], .c 3, .c 5, .c 683, .c 3, .c 7, .c 719, .c 3,
  .p pv5 [pv2,pv181,pv1583], .c 757, .c 3, .c 13, .c 5, .c 3, .c 19, .c 43, .c 3, .c 5, .c 11,
  .c 3, .c 47, .c 197, .c 3, .c 263, .c 13, .c 3, .c 7, .c 5, .c 3, .c 11, .c 23, .c 3, .c 5,
  .c 7, .c 3, .p pv2 [pv2,pv5,pv11,pv521], .c 313, .c 3, .p pv2 [pv2,pv286553],
  .p pv2 [pv2,pv3,pv163,pv293], .c 3, .c 277, .c 5, .c 3, .p pv7 [pv2,pv7,pv13,pv47,pv67], .c 17,
  .c 3, .c 5, .c 29, .c 3, .c 13, .c 11, .c 3, .c 23, .c 7, .c 3, .p pv5 [pv2,pv53,pv5407], .c 5,
  .c 3, .c 173, .c 127, .c 3, .c 5, .c 13, .c 3, .p pv11 [pv2,pv5,pv7,pv23,pv89],
  .p pv2 [pv2,pv3,pv95527], .c 3, .c 7, .c 307, .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv286589],
  .c 7, .c 3, .c 5,
]
private theorem h0069c30 : checkBlock 572931 128 b0069c30 = true := by
  decide +kernel

private def b0069c31 : List Row := [
  .c 229, .c 3, .c 191, .c 617, .c 3, .p pv2 [pv2,pv13,pv73,pv151], .c 11, .c 3, .c 149, .c 5,
  .c 3, .c 7, .c 19, .c 3, .c 5, .c 61, .c 3, .c 11, .c 7, .c 3, .c 181, .c 23, .c 3, .c 43, .c 5,
  .c 3, .c 269, .c 37, .c 3, .c 5, .p pv3 [pv2,pv3,pv31847], .c 3, .c 7,
  .p pv11 [pv2,pv3,pv23,pv31,pv67], .c 3, .c 17, .c 47, .c 3, .p pv5 [pv2,pv41,pv6991], .c 5,
  .c 3, .c 73, .c 163, .c 3, .c 5, .p pv7 [pv2,pv3,pv11,pv43,pv101], .c 3, .c 83, .c 31, .c 3,
  .c 11, .p pv7 [pv2,pv3,pv23887], .c 3, .c 7, .c 5, .c 3, .p pv23 [pv2,pv11,pv23,pv103], .c 29,
  .c 3, .c 5, .c 7, .c 3, .c 167, .c 13, .c 3, .p pv2 [pv2,pv143329], .c 43, .c 3, .c 359, .c 5,
  .c 3, .p pv3 [pv2,pv7,pv5119], .c 11, .c 3, .c 5, .c 179, .c 3, .p pv2 [pv2,pv5,pv109,pv263],
  .p pv5 [pv2,pv3,pv7,pv11,pv17,pv73], .c 3, .c 151, .c 7, .c 3, .c 11, .c 5, .c 3, .c 17, .c 239,
  .c 3, .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv7,pv8191], .c 449, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv13,pv7351], .c 3, .p pv5 [pv2,pv19,pv79,pv191], .c 5, .c 3, .c 37, .c 7, .c 3,
  .c 5, .c 11, .c 3, .c 19, .c 193, .c 3, .c 31, .p pv13 [pv2,pv3,pv11,pv181], .c 3, .c 23, .c 5,
  .c 3, .c 7, .c 59, .c 3, .c 5, .c 17, .c 3, .c 593, .c 7, .c 3, .p pv2 [pv2,pv23,pv271], .c 19,
  .c 3,
]
private theorem h0069c31 : checkBlock 573187 128 b0069c31 = true := by
  decide +kernel

def rows0069 : List Row :=
  b0069c00 ++ b0069c01 ++ b0069c02 ++ b0069c03 ++ b0069c04 ++ b0069c05 ++ b0069c06 ++ b0069c07 ++
  b0069c08 ++ b0069c09 ++ b0069c10 ++ b0069c11 ++ b0069c12 ++ b0069c13 ++ b0069c14 ++ b0069c15 ++
  b0069c16 ++ b0069c17 ++ b0069c18 ++ b0069c19 ++ b0069c20 ++ b0069c21 ++ b0069c22 ++ b0069c23 ++
  b0069c24 ++ b0069c25 ++ b0069c26 ++ b0069c27 ++ b0069c28 ++ b0069c29 ++ b0069c30 ++ b0069c31

theorem checked0069 : checkBlock 565251 4096 rows0069 = true :=
  checkBlock_append h0069c00 (
    checkBlock_append h0069c01 (
    checkBlock_append h0069c02 (
    checkBlock_append h0069c03 (
    checkBlock_append h0069c04 (
    checkBlock_append h0069c05 (
    checkBlock_append h0069c06 (
    checkBlock_append h0069c07 (
    checkBlock_append h0069c08 (
    checkBlock_append h0069c09 (
    checkBlock_append h0069c10 (
    checkBlock_append h0069c11 (
    checkBlock_append h0069c12 (
    checkBlock_append h0069c13 (
    checkBlock_append h0069c14 (
    checkBlock_append h0069c15 (
    checkBlock_append h0069c16 (
    checkBlock_append h0069c17 (
    checkBlock_append h0069c18 (
    checkBlock_append h0069c19 (
    checkBlock_append h0069c20 (
    checkBlock_append h0069c21 (
    checkBlock_append h0069c22 (
    checkBlock_append h0069c23 (
    checkBlock_append h0069c24 (
    checkBlock_append h0069c25 (
    checkBlock_append h0069c26 (
    checkBlock_append h0069c27 (
    checkBlock_append h0069c28 (
    checkBlock_append h0069c29 (
    checkBlock_append h0069c30 (
    h0069c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
