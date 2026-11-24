/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks00/Block0042
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks00/Block0042.checked0042
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table011
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table014
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table023
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table058
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table059

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0042c00 : List Row := [
  .c 3, .c 11, .c 7, .c 3, .c 5, .c 337, .c 3, .c 181, .p pv2 [pv2,pv3,pv57347], .c 3, .c 47,
  .c 223, .c 3, .c 163, .c 5, .c 3, .c 7, .c 61, .c 3, .c 5, .c 101, .c 3,
  .p pv11 [pv2,pv5,pv13,pv2647], .c 7, .c 3, .p pv2 [pv2,pv86029], .c 193, .c 3, .c 13, .c 5,
  .c 3, .c 43, .c 17, .c 3, .c 5, .c 37, .c 3, .c 7, .c 29, .c 3, .c 19, .c 13, .c 3,
  .p pv3 [pv2,pv43019], .c 5, .c 3, .c 197, .p pv29 [pv2,pv3,pv5,pv239], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv19,pv3019], .c 3, .p pv2 [pv2,pv5,pv127,pv271],
  .p pv2 [pv2,pv3,pv23,pv29,pv43], .c 3, .p pv3 [pv2,pv7,pv439], .c 11, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv6619], .c 491, .c 3, .c 5, .c 7, .c 3, .c 11, .c 79, .c 3,
  .p pv5 [pv2,pv59,pv2917], .p pv13 [pv2,pv3,pv71,pv101], .c 3, .p pv2 [pv2,pv11,pv7823], .c 5,
  .c 3, .c 107, .p pv2 [pv2,pv3,pv5,pv5737], .c 3, .c 5, .c 13, .c 3,
  .p pv23 [pv2,pv5,pv29,pv1187], .c 17, .c 3, .p pv2 [pv2,pv41,pv2099], .c 7, .c 3,
  .p pv2 [pv2,pv19,pv9059], .c 5, .c 3, .p pv3 [pv2,pv37,pv1163], .p pv3 [pv2,pv3,pv5,pv17], .c 3,
  .c 5, .p pv19 [pv2,pv3,pv11,pv163], .c 3, .c 19, .p pv31 [pv2,pv3,pv181,pv317], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv73,pv131], .c 3, .p pv3 [pv2,pv21517], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .c 23, .c 3, .p pv2 [pv2,pv5,pv34429], .p pv5 [pv2,pv3,pv13,pv2207], .c 3, .c 127, .c 19, .c 3,
  .c 139, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 29, .c 3, .p pv3 [pv2,pv5,pv269],
]
private theorem h0042c00 : checkBlock 344067 128 b0042c00 = true := by
  decide +kernel

private def b0042c01 : List Row := [
  .c 7, .c 3, .p pv5 [pv2,pv107,pv1609], .c 103, .c 3, .c 11, .c 5, .c 3, .c 149, .c 53, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv29,pv1979], .c 3, .c 7, .p pv23 [pv2,pv3,pv17,pv211], .c 3, .c 13,
  .c 37, .c 3, .p pv2 [pv2,pv172181], .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv13,pv883], .c 3,
  .c 5, .c 11, .c 3, .c 521, .c 13, .c 3, .c 43, .c 241, .c 3, .c 7, .c 5, .c 3, .c 11, .c 479,
  .c 3, .c 5, .c 7, .c 3, .c 283, .c 19, .c 3, .p pv3 [pv2,pv47,pv229], .c 163, .c 3,
  .p pv5 [pv2,pv13,pv1019], .c 5, .c 3, .p pv2 [pv2,pv7,pv12301], .c 151, .c 3, .c 5, .c 17, .c 3,
  .c 31, .c 11, .c 3, .c 53, .c 7, .c 3, .p pv2 [pv2,pv86113], .c 5, .c 3, .c 401, .c 13, .c 3,
  .c 5, .c 61, .c 3, .c 17, .c 43, .c 3, .c 7, .p pv11 [pv2,pv3,pv57413], .c 3,
  .p pv2 [pv2,pv41,pv4201], .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv7177], .c 3,
  .c 59, .c 31, .c 3, .c 37, .c 11, .c 3, .c 13, .c 5, .c 3, .c 7, .c 167, .c 3, .c 5, .c 19,
  .c 3, .c 11, .c 7, .c 3, .c 113, .c 13, .c 3, .p pv5 [pv2,pv11,pv15661], .c 5, .c 3, .c 29,
  .c 127, .c 3, .c 5, .c 47, .c 3, .c 7, .c 23, .c 3, .p pv5 [pv2,pv172283], .c 587, .c 3, .c 17,
  .c 5, .c 3,
]
private theorem h0042c01 : checkBlock 344323 128 b0042c01 = true := by
  decide +kernel

private def b0042c02 : List Row := [
  .c 317, .c 37, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv23,pv227], .c 3, .c 13, .c 509, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv79,pv727], .c 3, .c 7, .c 5, .c 3, .c 23, .p pv2 [pv2,pv3,pv5,pv7,pv547],
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv17231], .c 251, .c 3, .c 31, .p pv2 [pv2,pv3,pv3191],
  .c 3, .c 73, .c 5, .c 3, .p pv7 [pv2,pv7,pv103,pv239], .c 11, .c 3, .c 5, .c 107, .c 3, .c 47,
  .p pv17 [pv2,pv3,pv7,pv11,pv373], .c 3, .c 523, .c 7, .c 3, .c 11, .c 5, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv5,pv11489], .c 3, .c 5, .c 79, .c 3, .p pv3 [pv2,pv5,pv7,pv1231],
  .p pv2 [pv2,pv3,pv13,pv491], .c 3, .c 7, .c 31, .c 3, .p pv2 [pv2,pv17,pv37,pv137], .c 5, .c 3,
  .c 83, .c 7, .c 3, .c 5, .c 11, .c 3, .c 61, .c 101, .c 3, .c 19, .p pv3 [pv2,pv3,pv11,pv1741],
  .c 3, .c 29, .c 5, .c 3, .c 7, .c 43, .c 3, .c 5, .c 59, .c 3, .c 103, .c 7, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv28729], .c 3, .p pv3 [pv2,pv29,pv743], .c 5, .c 3, .p pv7 [pv2,pv223,pv773],
  .c 307, .c 3, .c 5, .c 109, .c 3, .c 7, .c 11, .c 3, .c 17, .c 73, .c 3, .c 557, .c 5, .c 3,
  .c 173, .p pv3 [pv2,pv3,pv5,pv1277], .c 3, .c 5, .p pv5 [pv2,pv3,pv59,pv487], .c 3,
  .p pv3 [pv2,pv5,pv431], .c 37, .c 3, .p pv7 [pv2,pv7,pv11,pv2239], .c 499, .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv53,pv3253], .p pv17 [pv2,pv3,pv5,pv7,pv821], .c 3, .c 5, .c 7, .c 3, .c 19,
  .c 61,
]
private theorem h0042c02 : checkBlock 344579 128 b0042c02 = true := by
  decide +kernel

private def b0042c03 : List Row := [
  .c 3, .c 419, .c 11, .c 3, .p pv2 [pv2,pv172421], .c 5, .c 3, .c 67, .c 13, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv14369], .c 3, .c 11, .p pv3 [pv2,pv3,pv7,pv17,pv23], .c 3, .c 199, .c 7, .c 3,
  .p pv3 [pv2,pv11,pv3919], .c 5, .c 3, .c 17, .c 353, .c 3, .c 5, .p pv3 [pv2,pv3,pv47,pv1223],
  .c 3, .c 193, .p pv7 [pv2,pv3,pv41,pv701], .c 3, .c 7, .c 311, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv23,pv163], .c 7, .c 3, .c 5, .p pv31 [pv2,pv3,pv11,pv13,pv67], .c 3,
  .p pv13 [pv2,pv5,pv8623], .c 131, .c 3, .c 11, .c 13, .c 3, .c 41, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv5749], .c 3, .c 5, .c 17, .c 3, .c 37, .c 7, .c 3, .p pv2 [pv2,pv86239],
  .p pv3 [pv2,pv3,pv57493], .c 3, .p pv2 [pv2,pv173,pv997], .c 5, .c 3,
  .p pv17 [pv2,pv13,pv31,pv107], .c 11, .c 3, .c 5, .c 23, .c 3, .c 7, .c 19, .c 3,
  .p pv2 [pv2,pv181,pv953], .c 43, .c 3, .c 11, .c 5, .c 3, .c 31, .p pv7 [pv2,pv3,pv5,pv23],
  .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv34501], .c 29, .c 3, .p pv3 [pv2,pv7,pv61,pv101],
  .p pv3 [pv2,pv3,pv57503], .c 3, .c 7, .c 5, .c 3, .c 97, .c 83, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv19,pv227], .c 389, .c 3, .p pv5 [pv2,pv13,pv23,pv577], .c 17, .c 3, .c 89,
  .c 5, .c 3, .c 11, .c 31, .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv199], .c 3, .c 29, .c 233, .c 3,
  .c 61, .c 7, .c 3, .c 17, .c 5, .c 3, .p pv3 [pv2,pv337],
]
private theorem h0042c03 : checkBlock 344835 128 b0042c03 = true := by
  decide +kernel

private def b0042c04 : List Row := [
  .c 59, .c 3, .c 5, .c 19, .c 3, .c 433, .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv28759], .c 3,
  .c 467, .c 5, .c 3, .c 563, .c 7, .c 3, .c 5, .c 269, .c 3, .c 71, .p pv2 [pv2,pv3,pv9587],
  .c 3, .c 13, .p pv2 [pv2,pv3,pv23,pv41,pv61], .c 3, .p pv5 [pv2,pv7,pv89,pv277], .c 5, .c 3,
  .c 7, .c 17, .c 3, .c 5, .c 547, .c 3, .c 23, .c 7, .c 3, .c 181, .c 11, .c 3, .c 19, .c 5,
  .c 3, .c 41, .p pv13 [pv2,pv3,pv5,pv11,pv523], .c 3, .c 5, .c 29, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv19,pv757], .c 3, .c 83, .c 61, .c 3, .c 109, .c 5, .c 3, .c 59, .c 19, .c 3,
  .c 5, .c 73, .c 3, .p pv3 [pv2,pv5,pv41,pv421], .c 97, .c 3, .p pv2 [pv2,pv7,pv24659],
  .p pv7 [pv2,pv3,pv13,pv2213], .c 3, .c 7, .c 5, .c 3, .c 313, .c 13, .c 3, .c 5, .c 7, .c 3,
  .c 67, .c 17, .c 3, .c 11, .p pv2 [pv2,pv3,pv19181], .c 3, .p pv5 [pv2,pv47,pv3673], .c 5, .c 3,
  .c 379, .p pv3 [pv2,pv3,pv5,pv17,pv677], .c 3, .c 5, .c 193, .c 3, .c 449, .c 487, .c 3, .c 17,
  .c 7, .c 3, .c 13, .c 5, .c 3, .c 23, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv19,pv233], .c 3,
  .p pv13 [pv2,pv5,pv7,pv4933], .c 127, .c 3, .c 7, .c 13, .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv113,pv191], .c 7, .c 3, .c 5, .c 151, .c 3, .c 197, .c 41, .c 3,
]
private theorem h0042c04 : checkBlock 345091 128 b0042c04 = true := by
  decide +kernel

private def b0042c05 : List Row := [
  .c 367, .c 281, .c 3, .c 241, .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .c 11, .c 3, .c 13, .c 7,
  .c 3, .c 137, .p pv19 [pv2,pv3,pv11,pv5233], .c 3, .c 569, .c 5, .c 3, .c 11, .c 23, .c 3, .c 5,
  .c 13, .c 3, .c 7, .c 47, .c 3, .c 211, .c 89, .c 3, .p pv2 [pv2,pv86353], .c 5, .c 3, .c 29,
  .c 109, .c 3, .c 5, .c 223, .c 3, .p pv7 [pv2,pv5,pv34543], .c 11, .c 3, .c 23, .c 19, .c 3,
  .c 7, .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv7,pv47], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv23,pv751], .p pv3 [pv2,pv3,pv13,pv43,pv103], .c 3, .c 79, .c 37, .c 3,
  .p pv3 [pv2,pv2699], .c 5, .c 3, .p pv7 [pv2,pv7,pv24677], .c 173, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv71,pv811], .c 3, .c 17, .c 439, .c 3, .c 47, .c 7, .c 3, .c 107, .c 5, .c 3,
  .c 73, .p pv3 [pv2,pv3,pv5,pv11,pv349], .c 3, .c 5, .p pv2 [pv2,pv3,pv28793], .c 3, .c 11,
  .c 167, .c 3, .c 7, .c 23, .c 3, .p pv2 [pv2,pv11,pv7853], .c 5, .c 3, .c 233, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv79], .c 3, .p pv13 [pv2,pv5,pv6911], .c 13, .c 3, .c 31, .c 17, .c 3, .c 59,
  .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv11519], .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv11,pv17],
  .c 3, .p pv2 [pv2,pv5,pv37,pv467], .c 7, .c 3, .c 11, .c 41, .c 3, .c 17, .c 5, .c 3,
  .p pv11 [pv2,pv11,pv23,pv683], .p pv29 [pv2,pv3,pv5],
]
private theorem h0042c05 : checkBlock 345347 128 b0042c05 = true := by
  decide +kernel

private def b0042c06 : List Row := [
  .c 3, .c 5, .p pv3 [pv2,pv3,pv57601], .c 3, .c 7, .c 53, .c 3, .c 37, .c 31, .c 3, .c 577, .c 5,
  .c 3, .c 19, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv9601], .c 3, .c 421,
  .p pv2 [pv2,pv3,pv11,pv5237], .c 3, .p pv5 [pv2,pv7,pv3527], .c 179, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv172829], .c 17, .c 3, .c 5, .c 7, .c 3, .c 41, .p pv7 [pv2,pv3,pv4801], .c 3,
  .c 43, .p pv3 [pv2,pv3,pv17,pv3389], .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv7,pv6173], .c 37,
  .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv3457], .c 523, .c 3, .p pv2 [pv2,pv172853], .c 7,
  .c 3, .c 23, .c 5, .c 3, .c 11, .c 227, .c 3, .c 5, .p pv3 [pv2,pv3,pv19207], .c 3,
  .p pv2 [pv2,pv5,pv7,pv11,pv449], .p pv2 [pv2,pv3,pv47,pv613], .c 3, .c 7,
  .p pv7 [pv2,pv3,pv29,pv1987], .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv13,pv61,pv109], .c 7, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv28813], .c 3, .c 13, .c 11, .c 3, .c 29, .p pv11 [pv2,pv3,pv14407],
  .c 3, .p pv2 [pv2,pv7,pv53,pv233], .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 13, .c 3,
  .p pv17 [pv2,pv5,pv151,pv229], .c 7, .c 3, .c 17, .c 59, .c 3, .p pv2 [pv2,pv37,pv4673], .c 5,
  .c 3, .c 61, .p pv3 [pv2,pv3,pv5,pv11527], .c 3, .c 5, .p pv7 [pv2,pv3,pv1601], .c 3, .c 7,
  .p pv7 [pv2,pv3,pv57637], .c 3, .c 173, .c 11, .c 3, .c 239, .c 5, .c 3, .c 13, .c 71, .c 3,
  .c 5, .c 317, .c 3, .c 11, .p pv19 [pv2,pv3,pv13,pv739], .c 3, .c 19,
]
private theorem h0042c06 : checkBlock 345603 128 b0042c06 = true := by
  decide +kernel

private def b0042c07 : List Row := [
  .c 349, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv86467], .c 157, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv8647], .c 29, .c 3, .p pv5 [pv2,pv163,pv1061], .p pv23 [pv2,pv3,pv1201], .c 3,
  .c 113, .c 5, .c 3, .c 17, .c 191, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv1747], .c 3, .c 281,
  .c 37, .c 3, .c 11, .c 7, .c 3, .p pv2 [pv2,pv257,pv673], .c 5, .c 3, .c 31, .c 53, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7207], .c 3, .c 29, .c 13, .c 3, .c 7, .c 457, .c 3, .p pv3 [pv2,pv19,pv569],
  .c 5, .c 3, .c 347, .c 7, .c 3, .c 5, .c 17, .c 3, .c 19, .c 277, .c 3, .c 103,
  .p pv3 [pv2,pv3,pv43,pv149], .c 3, .c 11, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv1373], .c 3, .c 17, .c 7, .c 3, .c 179, .c 19, .c 3,
  .p pv2 [pv2,pv23,pv3761], .c 5, .c 3, .c 229, .c 13, .c 3, .c 5, .c 11, .c 3, .c 7, .c 293,
  .c 3, .c 53, .p pv3 [pv2,pv3,pv7,pv11,pv107], .c 3, .p pv2 [pv2,pv173021], .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv769], .c 3, .c 5, .c 29, .c 3, .c 37, .c 401, .c 3, .c 271, .c 17, .c 3,
  .c 7, .c 5, .c 3, .p pv13 [pv2,pv173039], .c 23, .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv53,pv653], .c 11, .c 3, .p pv3 [pv2,pv97,pv223], .c 13, .c 3, .c 17, .c 5,
  .c 3, .c 283, .p pv3 [pv2,pv3,pv5,pv83,pv139], .c 3,
]
private theorem h0042c07 : checkBlock 345859 128 b0042c07 = true := by
  decide +kernel

private def b0042c08 : List Row := [
  .c 5, .p pv2 [pv2,pv3,pv28843], .c 3, .c 89, .c 19, .c 3, .c 23, .c 7, .c 3,
  .p pv2 [pv2,pv86533], .c 5, .c 3, .p pv2 [pv2,pv13,pv13313], .p pv23 [pv2,pv3,pv5,pv641], .c 3,
  .c 5, .p pv3 [pv2,pv3,pv31,pv1861], .c 3, .c 13, .c 59, .c 3, .c 7, .c 11, .c 3, .c 41, .c 5,
  .c 3, .p pv3 [pv2,pv43271], .c 7, .c 3, .c 5, .c 13, .c 3, .c 11, .c 103, .c 3,
  .p pv2 [pv2,pv179,pv967], .c 67, .c 3, .c 43, .c 5, .c 3, .c 7, .p pv19 [pv2,pv3,pv5,pv577],
  .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv8243], .c 3, .c 461, .c 7, .c 3, .p pv3 [pv2,pv13,pv3329],
  .c 23, .c 3, .p pv5 [pv2,pv17,pv599], .c 5, .c 3, .c 13, .c 29, .c 3, .c 5, .c 19, .c 3, .c 7,
  .c 151, .c 3, .c 11, .c 47, .c 3, .c 181, .c 5, .c 3, .p pv2 [pv2,pv11,pv15739],
  .p pv2 [pv2,pv3,pv5,pv29,pv199], .c 3, .c 5, .c 71, .c 3, .c 59, .c 17, .c 3,
  .p pv2 [pv2,pv7,pv83,pv149], .c 43, .c 3, .c 7, .c 5, .c 3, .c 29, .c 11, .c 3, .c 5, .c 7,
  .c 3, .c 31, .p pv3 [pv2,pv3,pv11,pv53], .c 3, .c 13, .p pv11 [pv2,pv3,pv28859], .c 3, .c 11,
  .c 5, .c 3, .c 223, .p pv17 [pv2,pv3,pv5,pv13,pv37], .c 3, .c 5, .c 41, .c 3,
  .p pv2 [pv2,pv5,pv59,pv587], .c 13, .c 3, .p pv3 [pv2,pv79,pv137], .c 7, .c 3, .c 47, .c 5,
  .c 3, .p pv2 [pv2,pv86587], .c 19, .c 3, .c 5, .c 11, .c 3, .p pv17 [pv2,pv5,pv7,pv1237], .c 31,
  .c 3, .c 7, .p pv19 [pv2,pv3,pv11,pv41],
]
private theorem h0042c08 : checkBlock 346115 128 b0042c08 = true := by
  decide +kernel

private def b0042c09 : List Row := [
  .c 3, .p pv2 [pv2,pv13,pv6661], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 97, .c 3,
  .p pv13 [pv2,pv5,pv11,pv47,pv67], .p pv5 [pv2,pv3,pv17,pv283], .c 3, .p pv2 [pv2,pv86599],
  .p pv3 [pv2,pv3,pv13,pv4441], .c 3, .c 23, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv1031], .c 3, .p pv2 [pv2,pv5,pv17321], .c 7, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv9623], .c 3, .p pv3 [pv2,pv5413], .c 5, .c 3, .p pv7 [pv2,pv173219],
  .p pv53 [pv2,pv3,pv5,pv2887], .c 3, .c 5, .p pv3 [pv2,pv3,pv19,pv1013], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv28871], .c 3, .c 67, .c 199, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv37,pv2341], .c 233, .c 3, .c 5, .c 17, .c 3, .c 317, .c 421, .c 3, .c 31, .c 11,
  .c 3, .c 7, .c 5, .c 3, .c 157, .p pv17 [pv2,pv3,pv5,pv7,pv11], .c 3, .c 5, .c 7, .c 3, .c 11,
  .c 419, .c 3, .c 373, .c 173, .c 3, .c 197, .c 5, .c 3, .p pv3 [pv2,pv7,pv13,pv17], .c 47, .c 3,
  .c 5, .c 43, .c 3, .c 13, .p pv3 [pv2,pv3,pv7,pv37,pv223], .c 3, .p pv2 [pv2,pv173273], .c 7,
  .c 3, .p pv3 [pv2,pv43319], .c 5, .c 3, .p pv11 [pv2,pv241,pv719], .p pv29 [pv2,pv3,pv5,pv19],
  .c 3, .c 5, .c 13, .c 3, .c 113, .c 41, .c 3, .c 7, .c 17, .c 3, .c 127, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv7877], .c 7, .c 3, .c 5, .c 571, .c 3, .p pv3 [pv2,pv5,pv1733], .c 307, .c 3,
  .p pv5 [pv2,pv13,pv13331], .c 271, .c 3, .c 17, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
]
private theorem h0042c09 : checkBlock 346371 128 b0042c09 = true := by
  decide +kernel

private def b0042c10 : List Row := [
  .p pv5 [pv2,pv3,pv7,pv131], .c 3, .c 251, .c 7, .c 3, .c 29, .p pv3 [pv2,pv3,pv57773], .c 3,
  .c 11, .c 5, .c 3, .p pv3 [pv2,pv43331], .p pv2 [pv2,pv3,pv5,pv2311], .c 3, .c 5,
  .p pv7 [pv2,pv3,pv23,pv157], .c 3, .c 7, .c 61, .c 3, .p pv2 [pv2,pv29,pv43,pv139],
  .p pv17 [pv2,pv3,pv7,pv4127], .c 3, .c 31, .c 5, .c 3, .c 23, .c 17, .c 3, .c 5, .c 11, .c 3,
  .c 83, .c 19, .c 3, .c 13, .p pv13 [pv2,pv3,pv11,pv17,pv103], .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv23 [pv2,pv3,pv5,pv7,pv13,pv127], .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv11,pv197],
  .c 13, .c 3, .c 37, .c 109, .c 3, .c 101, .c 5, .c 3, .p pv2 [pv2,pv7,pv24767], .c 269, .c 3,
  .c 5, .c 137, .c 3, .p pv11 [pv2,pv5,pv19,pv73], .c 11, .c 3, .c 131, .c 7, .c 3,
  .p pv2 [pv2,pv13,pv13337], .c 5, .c 3, .c 19, .c 23, .c 3, .c 5, .c 577, .c 3, .c 541, .c 17,
  .c 3, .c 7, .c 239, .c 3, .p pv3 [pv2,pv67,pv647], .c 5, .c 3, .c 241, .c 7, .c 3, .c 5, .c 19,
  .c 3, .c 29, .c 47, .c 3, .c 17, .c 11, .c 3, .c 73, .c 5, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv5,pv11,pv1051], .c 3, .c 5, .c 127, .c 3, .c 11, .c 7, .c 3, .c 151,
  .p pv7 [pv2,pv3,pv3613], .c 3, .c 13, .c 5, .c 3, .c 31, .c 59, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv4447], .c 3, .c 7, .p pv17 [pv2,pv3,pv97,pv149], .c 3,
  .p pv2 [pv2,pv86719], .c 13, .c 3,
]
private theorem h0042c10 : checkBlock 346627 128 b0042c10 = true := by
  decide +kernel

private def b0042c11 : List Row := [
  .c 19, .c 5, .c 3, .c 79, .p pv43 [pv2,pv3,pv5,pv31,pv373], .c 3, .c 5, .c 263, .c 3, .c 41,
  .p pv5 [pv2,pv3,pv17,pv19,pv179], .c 3, .c 11, .c 23, .c 3, .c 7, .c 5, .c 3, .c 17, .c 19,
  .c 3, .c 5, .c 7, .c 3, .c 13, .p pv2 [pv2,pv3,pv23,pv419], .c 3, .c 233,
  .p pv3 [pv2,pv3,pv53,pv1091], .c 3, .p pv5 [pv2,pv41,pv4231], .c 5, .c 3, .c 37, .c 11, .c 3,
  .c 5, .c 13, .c 3, .p pv7 [pv2,pv5,pv4337], .p pv2 [pv2,pv3,pv7,pv11,pv751], .c 3, .c 43, .c 7,
  .c 3, .c 11, .c 5, .c 3, .c 59, .c 467, .c 3, .c 5, .c 17, .c 3, .c 53, .c 67, .c 3, .c 7,
  .c 353, .c 3, .p pv2 [pv2,pv173501], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 11, .c 3, .c 17,
  .c 37, .c 3, .c 163, .c 61, .c 3, .p pv3 [pv2,pv7,pv6197], .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv241], .c 3, .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv11,pv631], .c 7, .c 3,
  .p pv3 [pv2,pv109,pv199], .p pv2 [pv2,pv3,pv6427], .c 3, .p pv5 [pv2,pv173531], .c 5, .c 3,
  .p pv2 [pv2,pv86767], .p pv7 [pv2,pv3,pv5,pv23,pv503], .c 3, .c 5, .c 449, .c 3, .c 7, .c 11,
  .c 3, .c 13, .c 17, .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv173549], .c 29, .c 3, .c 5, .c 31,
  .c 3, .c 19, .c 13, .c 3, .c 313, .c 71, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv43391],
  .p pv11 [pv2,pv3,pv5,pv7,pv19,pv29], .c 3, .c 5, .c 7,
]
private theorem h0042c11 : checkBlock 346883 128 b0042c11 = true := by
  decide +kernel

private def b0042c12 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv17,pv1021], .p pv3 [pv2,pv3,pv47,pv1231], .c 3, .c 41, .c 11, .c 3,
  .c 359, .c 5, .c 3, .c 29, .p pv7 [pv2,pv3,pv5,pv11,pv263], .c 3, .c 5, .p pv3 [pv2,pv3,pv2143],
  .c 3, .c 11, .p pv2 [pv2,pv3,pv7,pv4133], .c 3, .p pv3 [pv2,pv43397], .c 7, .c 3,
  .p pv5 [pv2,pv11,pv43,pv367], .c 5, .c 3, .c 47, .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv28933],
  .c 3, .p pv41 [pv2,pv5,pv7,pv31], .c 53, .c 3, .c 7, .p pv13 [pv2,pv3,pv17,pv23,pv37], .c 3,
  .c 103, .c 5, .c 3, .c 331, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv5261], .c 3, .c 23,
  .p pv7 [pv2,pv3,pv3617], .c 3, .c 11, .p pv7 [pv2,pv3,pv101,pv191], .c 3, .c 13, .c 5, .c 3,
  .c 7, .p pv3 [pv2,pv3,pv5,pv463], .c 3, .c 5, .p pv19 [pv2,pv3,pv7,pv13,pv53], .c 3, .c 67,
  .c 7, .c 3, .c 239, .c 13, .c 3, .c 61, .c 5, .c 3, .c 269, .c 11, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv57881], .c 3, .c 7, .c 17, .c 3, .p pv3 [pv2,pv10853],
  .p pv2 [pv2,pv3,pv7,pv8269], .c 3, .c 11, .c 5, .c 3, .c 53, .c 41, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv103,pv281], .c 3, .c 13, .c 23, .c 3, .c 17, .p pv7 [pv2,pv3,pv67], .c 3,
  .c 7, .c 5, .c 3, .c 19, .p pv17 [pv2,pv3,pv5,pv7,pv827], .c 3, .c 5, .c 7, .c 3, .c 419,
  .c 163, .c 3, .c 97, .p pv3 [pv2,pv3,pv11,pv19,pv277], .c 3, .c 79, .c 5, .c 3, .c 11, .c 563,
  .c 3, .c 5, .c 19, .c 3, .c 383, .c 109, .c 3, .c 311, .c 7, .c 3, .c 37,
]
private theorem h0042c12 : checkBlock 347139 128 b0042c12 = true := by
  decide +kernel

private def b0042c13 : List Row := [
  .c 5, .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv193], .c 3, .c 5, .c 73, .c 3,
  .p pv2 [pv2,pv5,pv7,pv709], .c 11, .c 3, .c 7, .c 103, .c 3, .c 263, .c 5, .c 3, .c 17, .c 7,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv3217], .c 3, .c 157, .p pv2 [pv2,pv3,pv79,pv733], .c 3, .c 337,
  .c 29, .c 3, .c 19, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 37, .c 3, .c 47, .c 7, .c 3, .c 13,
  .c 11, .c 3, .c 43, .c 5, .c 3, .p pv3 [pv2,pv10859], .c 19, .c 3, .c 5, .c 17, .c 3, .c 7,
  .c 13, .c 3, .c 23, .p pv2 [pv2,pv3,pv7,pv197], .c 3, .p pv3 [pv2,pv11,pv359], .c 5, .c 3,
  .p pv7 [pv2,pv47,pv3697], .c 53, .c 3, .c 5, .c 167, .c 3, .c 17, .p pv2 [pv2,pv3,pv28961],
  .c 3, .c 227, .p pv3 [pv2,pv3,pv57923], .c 3, .c 7, .c 5, .c 3, .c 367, .c 97, .c 3, .c 5, .c 7,
  .c 3, .p pv13 [pv2,pv5,pv8689], .p pv2 [pv2,pv3,pv19309], .c 3, .c 11, .c 43, .c 3, .c 503,
  .c 5, .c 3, .p pv2 [pv2,pv7,pv11,pv37,pv61], .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv19,pv3049],
  .c 3, .p pv19 [pv2,pv5,pv34759], .c 193, .c 3, .c 281, .c 7, .c 3, .c 31, .c 5, .c 3,
  .p pv3 [pv2,pv43451], .c 11, .c 3, .c 5, .c 149, .c 3, .p pv3 [pv2,pv5,pv7,pv13,pv191], .c 29,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv59,pv491], .c 3, .c 11, .c 5, .c 3, .c 41, .c 7, .c 3, .c 5,
  .c 509, .c 3,
]
private theorem h0042c13 : checkBlock 347395 128 b0042c13 = true := by
  decide +kernel

private def b0042c14 : List Row := [
  .p pv2 [pv2,pv5,pv17,pv409], .c 199, .c 3, .c 223, .c 13, .c 3, .c 67, .c 5, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv5,pv3863], .c 3, .c 5, .c 11, .c 3, .c 19, .c 7, .c 3, .c 59, .c 37, .c 3,
  .c 271, .c 5, .c 3, .c 11, .c 17, .c 3, .c 5, .p pv3 [pv2,pv3,pv47,pv137], .c 3, .c 7, .c 463,
  .c 3, .p pv2 [pv2,pv86929], .c 19, .c 3, .c 89, .c 5, .c 3, .p pv3 [pv2,pv103,pv211],
  .p pv2 [pv2,pv3,pv5,pv67,pv173], .c 3, .c 5, .c 13, .c 3, .c 43, .c 11, .c 3,
  .p pv2 [pv2,pv7,pv59,pv421], .c 317, .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv31,pv71,pv79],
  .c 61, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv83,pv419], .p pv2 [pv2,pv3,pv73,pv397], .c 3,
  .c 457, .p pv3 [pv2,pv3,pv139], .c 3, .c 23, .c 5, .c 3, .c 13, .c 293, .c 3, .c 5, .c 29, .c 3,
  .p pv3 [pv2,pv5,pv37,pv47], .c 17, .c 3, .c 283, .c 7, .c 3, .p pv2 [pv2,pv89,pv977], .c 5,
  .c 3, .c 109, .p pv2 [pv2,pv3,pv5,pv11,pv17,pv31], .c 3, .c 5, .c 43, .c 3, .c 11, .c 19, .c 3,
  .c 7, .c 53, .c 3, .c 137, .c 5, .c 3, .p pv3 [pv2,pv43481], .c 7, .c 3, .c 5, .c 107, .c 3,
  .c 167, .c 541, .c 3, .c 13, .c 233, .c 3, .p pv3 [pv2,pv7,pv1553], .c 5, .c 3, .c 7, .c 331,
  .c 3, .c 5, .p pv7 [pv2,pv3,pv7,pv11,pv251], .c 3, .p pv2 [pv2,pv5,pv19,pv1831], .c 7, .c 3,
  .c 11, .p pv3 [pv2,pv3,pv23,pv2521], .c 3, .c 173, .c 5,
]
private theorem h0042c14 : checkBlock 347651 128 b0042c14 = true := by
  decide +kernel

private def b0042c15 : List Row := [
  .c 3, .c 19, .c 37, .c 3, .c 5, .c 139, .c 3, .c 7, .c 59, .c 3, .c 113,
  .p pv11 [pv2,pv3,pv7,pv19,pv109], .c 3, .p pv2 [pv2,pv13,pv6691], .c 5, .c 3, .c 17, .c 11,
  .c 3, .c 5, .c 19, .c 3, .p pv7 [pv2,pv5,pv6959], .c 349, .c 3, .p pv2 [pv2,pv7,pv17,pv43],
  .p pv3 [pv2,pv3,pv13,pv1487], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv5437], .c 13, .c 3, .c 5,
  .c 7, .c 3, .p pv11 [pv2,pv5,pv127,pv137], .p pv5 [pv2,pv3,pv59,pv983], .c 3,
  .p pv2 [pv2,pv173993], .p pv13 [pv2,pv3,pv47,pv617], .c 3, .p pv3 [pv2,pv43499], .c 5, .c 3,
  .c 43, .p pv7 [pv2,pv3,pv5,pv29], .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv13,pv2677], .c 23,
  .c 3, .p pv3 [pv2,pv21751], .c 7, .c 3, .c 13, .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv1289],
  .c 3, .c 5, .c 31, .c 3, .c 17, .p pv5 [pv2,pv3,pv19,pv43,pv71], .c 3, .c 7, .c 13, .c 3,
  .p pv2 [pv2,pv87013], .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 131, .c 3, .c 107, .c 11, .c 3,
  .p pv2 [pv2,pv173,pv503], .c 89, .c 3, .p pv2 [pv2,pv7,pv23,pv47], .c 5, .c 3, .c 7, .c 587,
  .c 3, .c 5, .p pv11 [pv2,pv3,pv7,pv37], .c 3, .c 13, .c 7, .c 3, .c 127, .c 17, .c 3, .c 71,
  .c 5, .c 3, .c 491, .c 337, .c 3, .c 5, .c 13, .c 3, .c 7, .c 37, .c 3, .c 19, .c 11, .c 3,
  .c 17, .c 5, .c 3, .p pv2 [pv2,pv87037], .c 23, .c 3, .c 5, .c 53, .c 3, .c 11,
]
private theorem h0042c15 : checkBlock 347907 128 b0042c15 = true := by
  decide +kernel

private def b0042c16 : List Row := [
  .p pv2 [pv2,pv3,pv58027], .c 3, .c 421, .c 397, .c 3, .c 7, .c 5, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv5,pv7,pv829], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv34819], .c 191, .c 3,
  .c 23, .c 67, .c 3, .c 29, .c 5, .c 3, .p pv3 [pv2,pv7,pv3109], .c 17, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv1319], .c 3, .p pv3 [pv2,pv5,pv23,pv757], .c 31, .c 3, .c 11, .c 7, .c 3,
  .c 479, .c 5, .c 3, .p pv11 [pv2,pv11,pv1439], .p pv7 [pv2,pv3,pv5,pv1451], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv6449], .c 3, .c 19, .p pv2 [pv2,pv3,pv29021], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv58043], .c 3, .c 53, .c 5, .c 3, .p pv2 [pv2,pv83,pv1049], .c 7, .c 3, .c 5,
  .c 59, .c 3, .c 37, .c 13, .c 3, .p pv5 [pv2,pv174143], .c 19, .c 3, .c 11, .c 5, .c 3, .c 7,
  .c 379, .c 3, .c 5, .p pv11 [pv2,pv3,pv7,pv8293], .c 3, .c 79, .c 7, .c 3, .c 47, .c 29, .c 3,
  .p pv2 [pv2,pv13,pv13397], .c 5, .c 3, .c 131, .c 163, .c 3, .c 5, .c 11, .c 3, .c 7, .c 43,
  .c 3, .c 17, .c 101, .c 3, .p pv3 [pv2,pv5443], .c 5, .c 3, .c 11, .c 13, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv58061], .c 3, .c 61, .c 283, .c 3, .c 29, .c 113, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv251,pv347], .c 137, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv13,pv67], .c 11,
  .c 3, .p pv5 [pv2,pv29,pv6007], .c 31, .c 3, .c 13, .c 5, .c 3,
]
private theorem h0042c16 : checkBlock 348163 128 b0042c16 = true := by
  decide +kernel

private def b0042c17 : List Row := [
  .p pv7 [pv2,pv7,pv41,pv607], .p pv2 [pv2,pv3,pv5,pv5807], .c 3, .c 5, .c 23, .c 3,
  .p pv13 [pv2,pv5,pv34843], .p pv11 [pv2,pv3,pv7,pv17,pv61], .c 3, .p pv3 [pv2,pv11,pv7919],
  .c 7, .c 3, .p pv2 [pv2,pv174221], .c 5, .c 3, .c 17, .p pv11 [pv2,pv3,pv5,pv23,pv101], .c 3,
  .c 5, .p pv5 [pv2,pv3,pv14519], .c 3, .p pv3 [pv2,pv5,pv7,pv19,pv131], .p pv3 [pv2,pv3,pv239],
  .c 3, .c 7, .c 11, .c 3, .c 23, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv241],
  .c 3, .c 11, .c 29, .c 3, .c 563, .c 107, .c 3, .c 37, .c 5, .c 3, .c 7, .c 149, .c 3, .c 5,
  .c 13, .c 3, .c 97, .c 7, .c 3, .p pv5 [pv2,pv174263], .c 167, .c 3, .c 31, .c 5, .c 3, .c 71,
  .c 41, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv5281], .c 3, .c 7, .p pv5 [pv2,pv3,pv47,pv103], .c 3,
  .c 11, .p pv19 [pv2,pv3,pv7,pv43,pv193], .c 3, .p pv2 [pv2,pv174281], .c 5, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv5,pv1291], .c 3, .c 5, .c 37, .c 3, .c 53, .p pv3 [pv2,pv3,pv13,pv41,pv109],
  .c 3, .p pv2 [pv2,pv7,pv3557], .c 359, .c 3, .c 7, .c 5, .c 3, .c 47, .c 11, .c 3, .c 5, .c 7,
  .c 3, .c 23, .c 89, .c 3, .p pv3 [pv2,pv43577], .c 17, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv12451], .c 19, .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv1709], .c 3, .c 443,
  .p pv2 [pv2,pv3,pv7,pv2767], .c 3, .c 13, .c 7, .c 3, .c 17, .c 5, .c 3, .c 151,
  .p pv41 [pv2,pv3,pv5,pv13,pv149], .c 3, .c 5, .c 11, .c 3, .p pv41 [pv2,pv5,pv7,pv17,pv293],
  .c 13,
]
private theorem h0042c17 : checkBlock 348419 128 b0042c17 = true := by
  decide +kernel

private def b0042c18 : List Row := [
  .c 3, .c 7, .c 431, .c 3, .c 83, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 157, .c 3, .c 239,
  .c 23, .c 3, .c 19, .p pv17 [pv2,pv3,pv29059], .c 3, .c 107, .c 5, .c 3, .c 7, .c 17, .c 3,
  .c 5, .c 241, .c 3, .p pv2 [pv2,pv5,pv43,pv811], .c 7, .c 3, .c 61,
  .p pv3 [pv2,pv3,pv13,pv17,pv263], .c 3, .c 277, .c 5, .c 3, .c 23, .c 13, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv29063], .c 3, .c 7, .p pv7 [pv2,pv3,pv37,pv1571], .c 3, .c 229,
  .p pv17 [pv2,pv3,pv7,pv173], .c 3, .c 43, .c 5, .c 3, .p pv2 [pv2,pv174389], .c 31, .c 3, .c 5,
  .c 41, .c 3, .c 89, .c 53, .c 3, .c 569, .c 11, .c 3, .c 7, .c 5, .c 3, .c 149,
  .p pv11 [pv2,pv3,pv5,pv7,pv11,pv151], .c 3, .c 5, .c 7, .c 3, .c 11, .c 17, .c 3,
  .p pv2 [pv2,pv174413], .c 13, .c 3, .p pv3 [pv2,pv11,pv991], .c 5, .c 3,
  .p pv7 [pv2,pv7,pv24917], .c 23, .c 3, .c 5, .c 199, .c 3, .p pv2 [pv2,pv5,pv6977], .c 131,
  .c 3, .c 17, .c 7, .c 3, .c 167, .c 5, .c 3, .c 41, .c 179, .c 3, .c 5, .c 409, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv58147], .c 3, .c 7, .p pv11 [pv2,pv3,pv14537], .c 3, .c 269, .c 5, .c 3,
  .c 29, .c 7, .c 3, .c 5, .c 13, .c 3, .p pv17 [pv2,pv5,pv23,pv37,pv41], .c 383, .c 3,
  .p pv2 [pv2,pv19,pv4591], .p pv3 [pv2,pv3,pv58153], .c 3, .p pv2 [pv2,pv7,pv24923], .c 5, .c 3,
  .c 7,
]
private theorem h0042c18 : checkBlock 348675 128 b0042c18 = true := by
  decide +kernel

private def b0042c19 : List Row := [
  .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv31,pv67], .c 3, .c 173, .c 7, .c 3, .c 37,
  .p pv2 [pv2,pv3,pv359], .c 3, .c 11, .c 5, .c 3, .c 13, .c 151, .c 3, .c 5, .c 31, .c 3, .c 7,
  .c 19, .c 3, .c 461, .c 23, .c 3, .c 163, .c 5, .c 3, .p pv3 [pv2,pv43,pv2029],
  .p pv23 [pv2,pv3,pv5,pv11633], .c 3, .c 5, .c 11, .c 3, .c 263, .c 67, .c 3,
  .p pv5 [pv2,pv7,pv97,pv257], .c 421, .c 3, .c 7, .c 5, .c 3, .c 11, .c 37, .c 3, .c 5, .c 7,
  .c 3, .c 43, .c 41, .c 3, .c 13, .p pv3 [pv2,pv3,pv19391], .c 3, .p pv2 [pv2,pv61,pv2861], .c 5,
  .c 3, .c 19, .p pv17 [pv2,pv3,pv5,pv13,pv179], .c 3, .c 5, .c 113, .c 3, .c 17, .c 11, .c 3,
  .c 103, .c 7, .c 3, .c 29, .c 5, .c 3, .p pv11 [pv2,pv17,pv10267], .p pv7 [pv2,pv3,pv5,pv2909],
  .c 3, .c 5, .c 19, .c 3, .c 31, .p pv2 [pv2,pv3,pv9697], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv83,pv701], .c 3, .c 59, .c 5, .c 3, .p pv2 [pv2,pv87277], .c 7, .c 3, .c 5,
  .c 23, .c 3, .p pv3 [pv2,pv5,pv1091], .c 127, .c 3, .c 109, .c 11, .c 3,
  .p pv2 [pv2,pv7,pv37,pv337], .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 89, .c 3, .c 11, .c 7,
  .c 3, .c 101, .c 73, .c 3, .c 17, .c 5, .c 3, .c 37, .p pv2 [pv2,pv3,pv5,pv103,pv113], .c 3,
  .c 5, .p pv5 [pv2,pv3,pv14549], .c 3, .c 7, .p pv3 [pv2,pv3,pv19,pv1021], .c 3,
]
private theorem h0042c19 : checkBlock 348931 128 b0042c19 = true := by
  decide +kernel

private def b0042c20 : List Row := [
  .p pv2 [pv2,pv23,pv7591], .c 29, .c 3, .c 13, .c 5, .c 3, .p pv7 [pv2,pv174599], .c 19, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv11,pv13,pv37], .c 3, .p pv2 [pv2,pv5,pv47,pv743], .c 137, .c 3, .c 11,
  .c 13, .c 3, .c 7, .c 5, .c 3, .c 179, .c 17, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv8731],
  .c 37, .c 3, .c 29, .c 71, .c 3, .c 311, .c 5, .c 3, .c 79, .c 11, .c 3, .c 5, .c 233, .c 3,
  .c 13, .c 103, .c 3, .c 19, .c 7, .c 3, .c 11, .c 5, .c 3, .c 43, .p pv3 [pv2,pv3,pv5,pv3881],
  .c 3, .c 5, .c 13, .c 3, .c 23, .p pv3 [pv2,pv3,pv58217], .c 3, .c 7, .c 163, .c 3,
  .p pv3 [pv2,pv2729], .c 5, .c 3, .c 271, .c 7, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv181,pv193], .c 17, .c 3, .p pv3 [pv2,pv13,pv3359], .c 31, .c 3,
  .p pv5 [pv2,pv7,pv24953], .c 5, .c 3, .c 7, .c 47, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv4159],
  .c 3, .c 41, .c 7, .c 3, .c 17, .p pv7 [pv2,pv3,pv14557], .c 3, .p pv2 [pv2,pv19,pv4597], .c 5,
  .c 3, .p pv2 [pv2,pv73,pv2393], .p pv2 [pv2,pv3,pv5,pv647], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv58231], .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv113,pv773],
  .p pv7 [pv2,pv3,pv7,pv47,pv59], .c 3, .p pv2 [pv2,pv41,pv4261], .c 5, .c 3,
  .p pv3 [pv2,pv61,pv179], .p pv3 [pv2,pv3,pv5,pv19,pv613], .c 3, .c 5, .c 79, .c 3, .c 29,
  .p pv3 [pv2,pv3,pv58237], .c 3, .c 13, .c 19, .c 3, .c 7, .c 5, .c 3, .c 23, .c 223,
]
private theorem h0042c20 : checkBlock 349187 128 b0042c20 = true := by
  decide +kernel

private def b0042c21 : List Row := [
  .c 3, .c 5, .c 7, .c 3, .c 73, .c 13, .c 3, .c 59, .c 11, .c 3, .c 31, .c 5, .c 3, .c 17,
  .p pv11 [pv2,pv3,pv5,pv11,pv353], .c 3, .c 5, .p pv2 [pv2,pv3,pv29123], .c 3, .c 11,
  .p pv2 [pv2,pv3,pv7,pv53,pv157], .c 3, .c 137, .c 7, .c 3, .p pv2 [pv2,pv11,pv13,pv47], .c 5,
  .c 3, .p pv2 [pv2,pv174749], .c 373, .c 3, .c 5, .p pv2 [pv2,pv3,pv19417], .c 3, .c 181, .c 83,
  .c 3, .c 7, .p pv11 [pv2,pv3,pv13,pv4481], .c 3, .c 193, .c 5, .c 3, .p pv3 [pv2,pv43691], .c 7,
  .c 3, .c 5, .c 17, .c 3, .c 431, .c 19, .c 3, .c 11, .c 293, .c 3, .p pv3 [pv2,pv7,pv3121],
  .c 5, .c 3, .c 7, .c 101, .c 3, .c 5, .p pv7 [pv2,pv3,pv7,pv29,pv41], .c 3, .c 17, .c 7, .c 3,
  .c 23, .p pv2 [pv2,pv3,pv19421], .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv17,pv53,pv97], .c 11,
  .c 3, .c 5, .c 73, .c 3, .c 7, .p pv2 [pv2,pv3,pv11,pv5297], .c 3, .c 41, .c 13, .c 3, .c 11,
  .c 5, .c 3, .c 19, .c 313, .c 3, .c 5, .c 211, .c 3, .c 127, .c 43, .c 3,
  .p pv2 [pv2,pv7,pv12487], .c 17, .c 3, .c 7, .c 5, .c 3, .c 31, .c 317, .c 3, .c 5, .c 7, .c 3,
  .c 13, .p pv3 [pv2,pv3,pv101,pv577], .c 3, .p pv2 [pv2,pv359,pv487], .c 23, .c 3, .c 17, .c 5,
  .c 3, .c 11, .c 89, .c 3, .c 5, .c 13, .c 3, .c 241, .c 59, .c 3, .p pv3 [pv2,pv683],
]
private theorem h0042c21 : checkBlock 349443 128 b0042c21 = true := by
  decide +kernel

private def b0042c22 : List Row := [
  .c 7, .c 3, .c 149, .c 5, .c 3, .p pv2 [pv2,pv87427], .c 29, .c 3, .c 5,
  .p pv67 [pv2,pv3,pv151,pv193], .c 3, .c 191, .c 11, .c 3, .c 7, .p pv11 [pv2,pv3,pv3643], .c 3,
  .c 19, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 53, .c 3, .c 367,
  .p pv5 [pv2,pv3,pv13,pv19,pv59], .c 3, .c 397, .p pv7 [pv2,pv3,pv17,pv127], .c 3, .c 101, .c 5,
  .c 3, .c 7, .c 19, .c 3, .c 5, .c 257, .c 3, .c 109, .c 7, .c 3, .p pv2 [pv2,pv174893], .c 11,
  .c 3, .p pv3 [pv2,pv17,pv643], .c 5, .c 3, .c 499, .p pv29 [pv2,pv3,pv5,pv11,pv53], .c 3, .c 5,
  .c 23, .c 3, .c 7, .p pv5 [pv2,pv3,pv41,pv79], .c 3, .c 13, .p pv2 [pv2,pv3,pv7,pv8329], .c 3,
  .c 353, .c 5, .c 3, .p pv2 [pv2,pv19,pv4603], .p pv11 [pv2,pv3,pv5,pv13,pv23], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv29153], .c 3, .p pv11 [pv2,pv5,pv4373], .c 13, .c 3, .c 19,
  .p pv7 [pv2,pv3,pv43,pv113], .c 3, .c 7, .c 5, .c 3, .c 89, .c 271, .c 3, .c 5, .c 7, .c 3,
  .p pv11 [pv2,pv5,pv59,pv593], .c 181, .c 3, .c 11, .c 97, .c 3, .c 439, .c 5, .c 3, .c 73,
  .c 43, .c 3, .c 5, .c 31, .c 3, .c 131, .p pv3 [pv2,pv3,pv7,pv2777], .c 3,
  .p pv2 [pv2,pv53,pv3301], .c 7, .c 3, .p pv3 [pv2,pv191,pv229], .c 5, .c 3,
  .p pv11 [pv2,pv174959], .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv58321], .c 3,
  .p pv7 [pv2,pv5,pv7,pv4999], .p pv2 [pv2,pv3,pv11,pv241], .c 3, .c 7, .p pv2 [pv2,pv3,pv19441],
  .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv89,pv983], .c 7, .c 3,
]
private theorem h0042c22 : checkBlock 349699 128 b0042c22 = true := by
  decide +kernel

private def b0042c23 : List Row := [
  .c 5, .c 61, .c 3, .c 19, .p pv2 [pv2,pv3,pv17,pv47,pv73], .c 3, .p pv5 [pv2,pv233,pv751],
  .c 269, .c 3, .c 13, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv19,pv307], .c 3, .c 5, .c 11, .c 3,
  .c 23, .c 7, .c 3, .c 107, .c 13, .c 3, .p pv2 [pv2,pv139,pv1259], .c 5, .c 3, .c 11, .c 83,
  .c 3, .c 5, .c 41, .c 3, .c 7, .c 571, .c 3, .c 541, .p pv23 [pv2,pv3,pv7,pv463], .c 3,
  .p pv3 [pv2,pv131,pv167], .c 5, .c 3, .p pv7 [pv2,pv13,pv13463], .c 199, .c 3, .c 5, .c 17,
  .c 3, .c 13, .c 11, .c 3, .c 37, .c 29, .c 3, .c 7, .c 5, .c 3, .c 197, .c 283, .c 3, .c 5,
  .c 7, .c 3, .c 17, .c 23, .c 3, .p pv5 [pv2,pv11,pv15913], .p pv7 [pv2,pv3,pv29,pv503], .c 3,
  .p pv2 [pv2,pv87523], .c 5, .c 3, .c 41, .c 71, .c 3, .c 5, .p pv2 [pv2,pv3,pv23,pv43,pv59],
  .c 3, .p pv11 [pv2,pv5,pv157,pv223], .c 19, .c 3, .c 29, .c 7, .c 3, .c 347, .c 5, .c 3, .c 13,
  .c 37, .c 3, .c 5, .p pv5 [pv2,pv3,pv1621], .c 3, .c 11, .c 337, .c 3, .c 7, .c 17, .c 3,
  .c 487, .c 5, .c 3, .p pv17 [pv2,pv175079], .c 7, .c 3, .c 5, .c 101, .c 3, .c 53, .c 241, .c 3,
  .c 83, .p pv3 [pv2,pv3,pv58363], .c 3, .c 17, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv1297],
  .c 3, .c 5, .c 47, .c 3, .c 61, .c 7, .c 3, .c 11, .c 67,
]
private theorem h0042c23 : checkBlock 349955 128 b0042c23 = true := by
  decide +kernel

private def b0042c24 : List Row := [
  .c 3, .p pv2 [pv2,pv87553], .c 5, .c 3, .p pv2 [pv2,pv11,pv15919], .c 23, .c 3, .c 5, .c 19,
  .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv87559], .c 577, .c 3, .c 71, .c 5, .c 3,
  .p pv3 [pv2,pv43781], .c 11, .c 3, .c 5, .p pv11 [pv2,pv3,pv7297], .c 3, .c 227, .c 41, .c 3,
  .c 23, .c 31, .c 3, .c 7, .c 5, .c 3, .c 37, .p pv29 [pv2,pv3,pv5,pv7,pv139], .c 3, .c 5, .c 7,
  .c 3, .c 29, .p pv2 [pv2,pv3,pv29191], .c 3, .c 433, .c 149, .c 3, .c 19, .c 5, .c 3, .c 137,
  .c 13, .c 3, .c 5, .c 11, .c 3, .c 43, .c 61, .c 3, .c 73, .c 7, .c 3, .c 223, .c 5, .c 3,
  .c 11, .c 19, .c 3, .c 5, .p pv2 [pv2,pv3,pv58391], .c 3, .p pv7 [pv2,pv5,pv7,pv11,pv13], .c 17,
  .c 3, .c 7, .c 23, .c 3, .c 13, .c 5, .c 3, .c 101, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv1123], .c 3, .p pv2 [pv2,pv5,pv17519], .c 11, .c 3, .c 17, .c 13, .c 3,
  .c 31, .c 5, .c 3, .c 7, .c 59, .c 3, .c 5, .c 29, .c 3, .p pv2 [pv2,pv5,pv67,pv523], .c 7,
  .c 3, .c 19, .c 139, .c 3, .p pv5 [pv2,pv175211], .c 5, .c 3, .p pv2 [pv2,pv13,pv23,pv293],
  .p pv3 [pv2,pv3,pv5,pv11681], .c 3, .c 5, .p pv7 [pv2,pv3,pv19,pv29,pv53], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv19469], .c 3, .p pv5 [pv2,pv137,pv1279], .c 11, .c 3, .p pv2 [pv2,pv87613],
  .c 5, .c 3, .p pv2 [pv2,pv175229], .c 97, .c 3, .c 5,
]
private theorem h0042c24 : checkBlock 350211 128 b0042c24 = true := by
  decide +kernel

private def b0042c25 : List Row := [
  .c 13, .c 3, .c 11, .c 73, .c 3, .c 67, .c 47, .c 3, .c 7, .c 5, .c 3, .c 17, .c 463, .c 3,
  .c 5, .c 7, .c 3, .c 37, .p pv3 [pv2,pv3,pv58417], .c 3, .c 269, .c 41, .c 3, .c 409, .c 5,
  .c 3, .c 13, .p pv7 [pv2,pv3,pv5,pv23,pv127], .c 3, .c 5, .c 71, .c 3, .c 19, .c 167, .c 3,
  .c 11, .c 7, .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv11,pv31,pv257], .c 397, .c 3, .c 5, .c 17,
  .c 3, .p pv11 [pv2,pv5,pv7,pv313], .p pv3 [pv2,pv3,pv58427], .c 3, .c 7, .c 19, .c 3, .c 47,
  .c 5, .c 3, .c 31, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv19477], .c 3, .c 17,
  .p pv7 [pv2,pv3,pv11,pv83], .c 3, .c 13, .c 229, .c 3, .c 11, .c 5, .c 3, .c 7, .c 67, .c 3,
  .c 5, .p pv13 [pv2,pv3,pv7,pv2087], .c 3, .p pv3 [pv2,pv5,pv47,pv373], .c 7, .c 3, .c 547,
  .p pv23 [pv2,pv3,pv61,pv479], .c 3, .c 521, .c 5, .c 3, .c 29, .c 31, .c 3, .c 5, .c 11, .c 3,
  .c 7, .c 109, .c 3, .p pv3 [pv2,pv5479], .c 17, .c 3, .p pv5 [pv2,pv13,pv13487], .c 5, .c 3,
  .c 11, .c 173, .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv191], .c 3, .c 23, .c 19, .c 3, .c 131, .c 61,
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv175349], .c 13, .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv17,pv2063], .c 11, .c 3, .c 467, .p pv3 [pv2,pv3,pv58453], .c 3,
]
private theorem h0042c25 : checkBlock 350467 128 b0042c25 = true := by
  decide +kernel

private def b0042c26 : List Row := [
  .c 37, .c 5, .c 3, .p pv13 [pv2,pv7,pv6263], .p pv2 [pv2,pv3,pv5,pv433], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7307], .c 3, .p pv3 [pv2,pv5,pv13,pv19,pv71], .c 359, .c 3,
  .p pv2 [pv2,pv11,pv107,pv149], .c 7, .c 3, .c 13, .c 5, .c 3, .c 19, .c 17, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv13,pv1499], .c 3, .p pv2 [pv2,pv5,pv7,pv5011], .c 23, .c 3, .c 7, .c 11, .c 3,
  .p pv5 [pv2,pv175391], .c 5, .c 3, .p pv2 [pv2,pv87697], .c 7, .c 3, .c 5, .c 19, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv19489], .c 3, .c 53, .p pv11 [pv2,pv3,pv47,pv311], .c 3, .c 29, .c 5, .c 3,
  .c 7, .c 461, .c 3, .c 5, .c 31, .c 3, .c 13, .c 7, .c 3, .c 41, .c 79, .c 3,
  .p pv2 [pv2,pv23,pv29,pv263], .c 5, .c 3, .c 97, .p pv2 [pv2,pv3,pv5,pv2339], .c 3, .c 5, .c 13,
  .c 3, .c 7, .c 17, .c 3, .c 11, .p pv2 [pv2,pv3,pv7,pv4177], .c 3, .c 19, .c 5, .c 3, .c 67,
  .p pv13 [pv2,pv3,pv5,pv17,pv43], .c 3, .c 5, .p pv5 [pv2,pv3,pv58481], .c 3,
  .p pv2 [pv2,pv5,pv35089], .c 211, .c 3, .c 17, .p pv2 [pv2,pv3,pv233,pv251], .c 3, .c 7, .c 5,
  .c 3, .c 13, .c 11, .c 3, .c 5, .c 7, .c 3, .c 103, .c 43, .c 3, .c 89, .c 29, .c 3, .c 11,
  .c 5, .c 3, .c 163, .p pv11 [pv2,pv3,pv5,pv5849], .c 3, .c 5, .p pv2 [pv2,pv3,pv67,pv97], .c 3,
  .c 31, .c 71, .c 3, .c 23, .c 7, .c 3, .p pv2 [pv2,pv175481], .c 5, .c 3, .c 281,
  .p pv2 [pv2,pv3,pv5,pv11699], .c 3, .c 5, .c 11,
]
private theorem h0042c26 : checkBlock 350723 128 b0042c26 = true := by
  decide +kernel

private def b0042c27 : List Row := [
  .c 3, .p pv3 [pv2,pv5,pv7,pv23,pv109], .p pv5 [pv2,pv3,pv17,pv31,pv37], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv11,pv2659], .c 3, .c 373, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 83, .c 3,
  .p pv2 [pv2,pv5,pv11,pv3191], .c 13, .c 3, .c 173, .c 37, .c 3, .p pv7 [pv2,pv7,pv25073], .c 5,
  .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv11701], .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv199], .c 3,
  .p pv3 [pv2,pv5,pv1097], .c 7, .c 3, .p pv5 [pv2,pv175523], .c 23, .c 3,
  .p pv2 [pv2,pv13,pv43,pv157], .c 5, .c 3, .p pv2 [pv2,pv191,pv919],
  .p pv11 [pv2,pv3,pv5,pv5851], .c 3, .c 5, .c 17, .c 3, .c 7, .c 569, .c 3,
  .p pv2 [pv2,pv11,pv79,pv101], .p pv3 [pv2,pv3,pv7,pv13,pv643], .c 3, .c 41, .c 5, .c 3, .c 109,
  .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv14629], .c 3, .c 17, .c 29, .c 3, .c 479, .c 11, .c 3,
  .c 7, .c 5, .c 3, .c 311, .p pv29 [pv2,pv3,pv5,pv7,pv11,pv19], .c 3, .c 5, .c 7, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv29,pv1009], .c 3, .c 31, .c 19, .c 3, .c 13, .c 5, .c 3, .c 251,
  .p pv3 [pv2,pv3,pv5,pv2341], .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv2251], .c 3, .c 29, .c 433,
  .c 3, .c 37, .c 7, .c 3, .c 83, .c 5, .c 3, .p pv2 [pv2,pv53,pv3313], .c 43, .c 3, .c 5, .c 23,
  .c 3, .c 331, .c 149, .c 3, .c 7, .c 31, .c 3, .c 17, .c 5, .c 3, .c 157, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv271], .c 3, .c 13, .p pv3 [pv2,pv3,pv58537], .c 3, .c 59,
  .p pv11 [pv2,pv3,pv29269], .c 3, .c 23,
]
private theorem h0042c27 : checkBlock 350979 128 b0042c27 = true := by
  decide +kernel

private def b0042c28 : List Row := [
  .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 13, .c 3, .c 197, .c 7, .c 3, .p pv3 [pv2,pv23,pv83],
  .p pv3 [pv2,pv3,pv58543], .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv137,pv641], .c 17, .c 3, .c 5,
  .c 29, .c 3, .c 7, .c 89, .c 3, .p pv5 [pv2,pv13,pv59,pv229], .p pv23 [pv2,pv3,pv7,pv17,pv41],
  .c 3, .p pv2 [pv2,pv31,pv2833], .c 5, .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv1171], .c 3, .c 5,
  .c 11, .c 3, .p pv7 [pv2,pv5,pv19,pv43], .c 79, .c 3, .c 113, .c 257, .c 3, .c 7, .c 5, .c 3,
  .c 11, .c 409, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv11,pv1597],
  .p pv3 [pv2,pv3,pv131,pv149], .c 3, .p pv2 [pv2,pv175673], .c 73, .c 3, .c 43, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv25097], .p pv19 [pv2,pv3,pv5,pv61], .c 3, .c 5, .c 19, .c 3, .c 23, .c 11,
  .c 3, .c 13, .c 7, .c 3, .p pv5 [pv2,pv175691], .c 5, .c 3, .c 37,
  .p pv19 [pv2,pv3,pv5,pv13,pv17,pv53], .c 3, .c 5, .p pv2 [pv2,pv3,pv43,pv227], .c 3,
  .p pv3 [pv2,pv5,pv7,pv251], .c 13, .c 3, .c 7, .c 127, .c 3, .p pv2 [pv2,pv87853], .c 5, .c 3,
  .c 47, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv37,pv1583], .c 3, .c 97, .c 457, .c 3,
  .p pv2 [pv2,pv103,pv853], .c 11, .c 3, .c 19, .c 5, .c 3, .c 7, .c 29, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv523], .c 3, .c 11, .c 7, .c 3, .c 557, .p pv7 [pv2,pv3,pv13,pv751], .c 3,
  .c 131, .c 5, .c 3, .p pv13 [pv2,pv31,pv5669], .c 13, .c 3, .c 5, .c 271, .c 3,
]
private theorem h0042c28 : checkBlock 351235 128 b0042c28 = true := by
  decide +kernel

private def b0042c29 : List Row := [
  .c 7, .c 41, .c 3, .p pv3 [pv2,pv53,pv829], .c 313, .c 3, .p pv5 [pv2,pv181,pv971], .c 5, .c 3,
  .c 17, .c 347, .c 3, .c 5, .p pv7 [pv2,pv3,pv11,pv2663], .c 3, .c 71, .c 157, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv97,pv151], .c 3, .c 7, .c 5, .c 3, .c 103, .c 419, .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv79,pv89], .c 317, .c 3, .c 19, .c 13, .c 3, .p pv2 [pv2,pv175781], .c 5, .c 3,
  .c 239, .c 11, .c 3, .c 5, .c 17, .c 3, .c 59, .c 269, .c 3, .p pv2 [pv2,pv367,pv479], .c 7,
  .c 3, .c 11, .c 5, .c 3, .p pv17 [pv2,pv13,pv13523], .c 23, .c 3, .c 5, .c 47, .c 3, .c 13,
  .c 587, .c 3, .c 7, .c 241, .c 3, .c 227, .c 5, .c 3, .c 79, .c 7, .c 3, .c 5, .c 11, .c 3,
  .c 73, .p pv2 [pv2,pv3,pv103,pv569], .c 3, .c 23, .c 593, .c 3, .p pv2 [pv2,pv7,pv19,pv661],
  .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv5861], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv2791], .c 3,
  .c 19, .c 7, .c 3, .c 401, .c 17, .c 3, .c 29, .c 5, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv5,pv19,pv617], .c 3, .c 5, .c 43, .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv175853], .c 19, .c 3, .c 17, .c 5, .c 3, .c 509, .c 547, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv31,pv61], .c 3, .p pv2 [pv2,pv5,pv17,pv2069], .p pv5 [pv2,pv3,pv29311], .c 3,
  .c 211, .c 23, .c 3, .c 7, .c 5,
]
private theorem h0042c29 : checkBlock 351491 128 b0042c29 = true := by
  decide +kernel

private def b0042c30 : List Row := [
  .c 3, .p pv2 [pv2,pv47,pv1871], .p pv3 [pv2,pv3,pv5,pv7,pv67], .c 3, .c 5, .c 7, .c 3, .c 53,
  .p pv3 [pv2,pv3,pv23,pv2549], .c 3, .c 13, .c 11, .c 3, .p pv2 [pv2,pv87943], .c 5, .c 3,
  .p pv7 [pv2,pv7,pv25127], .c 17, .c 3, .c 5, .c 61, .c 3, .c 11, .c 13, .c 3,
  .p pv2 [pv2,pv37,pv2377], .c 7, .c 3, .p pv2 [pv2,pv11,pv15991], .c 5, .c 3, .c 139,
  .p pv2 [pv2,pv3,pv5,pv1303], .c 3, .c 5, .c 59, .c 3, .c 41, .c 19, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv29,pv337], .c 3, .c 37, .c 5, .c 3, .c 193, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv1777], .c 3, .p pv2 [pv2,pv5,pv31,pv227], .c 331, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv13,pv347], .c 3, .p pv5 [pv2,pv7,pv41,pv613], .c 5, .c 3, .c 7, .c 13, .c 3,
  .c 5, .c 23, .c 3, .c 31, .c 7, .c 3, .p pv5 [pv2,pv29,pv6067], .c 47, .c 3, .c 293, .c 5, .c 3,
  .c 19, .c 11, .c 3, .c 5, .c 37, .c 3, .c 7, .p pv29 [pv2,pv3,pv11,pv31,pv43], .c 3, .c 17,
  .p pv7 [pv2,pv3,pv7,pv19], .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv43991],
  .p pv2 [pv2,pv3,pv5,pv11731], .c 3, .c 5, .c 19, .c 3, .c 353, .c 31, .c 3, .c 71, .c 13, .c 3,
  .c 7, .c 5, .c 3, .p pv11 [pv2,pv175979], .c 109, .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv61,pv577], .c 29, .c 3, .c 383, .c 523, .c 3, .c 47, .c 5, .c 3, .c 11,
  .p pv19 [pv2,pv3,pv5,pv3911], .c 3, .c 5, .c 131, .c 3, .c 13,
]
private theorem h0042c30 : checkBlock 351747 128 b0042c30 = true := by
  decide +kernel

private def b0042c31 : List Row := [
  .c 83, .c 3, .p pv5 [pv2,pv73,pv2411], .c 7, .c 3, .c 19, .c 5, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv5,pv5867], .c 3, .c 5, .c 13, .c 3, .c 29, .c 11, .c 3, .c 7, .c 197, .c 3,
  .p pv2 [pv2,pv176021], .c 5, .c 3, .p pv3 [pv2,pv22003], .c 7, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv14669], .c 3, .c 23, .c 233, .c 3, .c 31, .p pv2 [pv2,pv3,pv29339], .c 3,
  .p pv3 [pv2,pv7,pv6287], .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv163], .c 3, .c 5, .c 17, .c 3,
  .c 379, .c 7, .c 3, .p pv3 [pv2,pv11003], .c 11, .c 3, .c 79, .c 5, .c 3,
  .p pv11 [pv2,pv19,pv41,pv113], .p pv3 [pv2,pv3,pv5,pv11,pv97], .c 3, .c 5, .c 223, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv58687], .c 3, .c 19, .c 31, .c 3, .p pv2 [pv2,pv11,pv53,pv151], .c 5, .c 3,
  .c 397, .c 349, .c 3, .c 5, .c 29, .c 3, .c 157, .c 23, .c 3, .c 13, .c 211, .c 3, .c 7, .c 5,
  .c 3, .c 83, .c 47, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv17609], .c 13, .c 3, .c 11, .c 17,
  .c 3, .p pv3 [pv2,pv5503], .c 5, .c 3, .c 23, .p pv7 [pv2,pv3,pv5,pv587], .c 3, .c 5, .c 97,
  .c 3, .c 569, .c 43, .c 3, .p pv3 [pv2,pv44027], .c 7, .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv173,pv509], .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv149,pv197], .c 3, .c 19, .c 163,
  .c 3, .c 7, .p pv11 [pv2,pv3,pv13,pv1129], .c 3, .c 11, .c 5, .c 3,
]
private theorem h0042c31 : checkBlock 352003 128 b0042c31 = true := by
  decide +kernel

def rows0042 : List Row :=
  b0042c00 ++ b0042c01 ++ b0042c02 ++ b0042c03 ++ b0042c04 ++ b0042c05 ++ b0042c06 ++ b0042c07 ++
  b0042c08 ++ b0042c09 ++ b0042c10 ++ b0042c11 ++ b0042c12 ++ b0042c13 ++ b0042c14 ++ b0042c15 ++
  b0042c16 ++ b0042c17 ++ b0042c18 ++ b0042c19 ++ b0042c20 ++ b0042c21 ++ b0042c22 ++ b0042c23 ++
  b0042c24 ++ b0042c25 ++ b0042c26 ++ b0042c27 ++ b0042c28 ++ b0042c29 ++ b0042c30 ++ b0042c31

attribute [local irreducible] checkBlock checkRows checkPrime

theorem checked0042 : checkBlock 344067 4096 rows0042 = true :=
  checkBlock_append h0042c00 (
    checkBlock_append h0042c01 (
    checkBlock_append h0042c02 (
    checkBlock_append h0042c03 (
    checkBlock_append h0042c04 (
    checkBlock_append h0042c05 (
    checkBlock_append h0042c06 (
    checkBlock_append h0042c07 (
    checkBlock_append h0042c08 (
    checkBlock_append h0042c09 (
    checkBlock_append h0042c10 (
    checkBlock_append h0042c11 (
    checkBlock_append h0042c12 (
    checkBlock_append h0042c13 (
    checkBlock_append h0042c14 (
    checkBlock_append h0042c15 (
    checkBlock_append h0042c16 (
    checkBlock_append h0042c17 (
    checkBlock_append h0042c18 (
    checkBlock_append h0042c19 (
    checkBlock_append h0042c20 (
    checkBlock_append h0042c21 (
    checkBlock_append h0042c22 (
    checkBlock_append h0042c23 (
    checkBlock_append h0042c24 (
    checkBlock_append h0042c25 (
    checkBlock_append h0042c26 (
    checkBlock_append h0042c27 (
    checkBlock_append h0042c28 (
    checkBlock_append h0042c29 (
    checkBlock_append h0042c30 (
    h0042c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
