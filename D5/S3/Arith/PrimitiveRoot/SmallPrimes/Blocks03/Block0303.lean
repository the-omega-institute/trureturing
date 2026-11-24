/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks03/Block0303
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks03/Block0303.checked0303
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table026
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table036
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table042
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table049
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table060
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table075
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table076
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table101
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table143
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table144

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0303c00 : List Row := [
  .c 3, .c 13, .c 11, .c 3, .c 17, .c 59, .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv19,pv83,pv787],
  .c 31, .c 3, .c 5, .c 7, .c 3, .c 47, .c 223, .c 3, .c 19, .c 37, .c 3, .c 383, .c 5, .c 3,
  .c 23, .c 71, .c 3, .c 5, .p pv5 [pv2,pv3,pv19,pv191], .c 3, .c 701,
  .p pv3 [pv2,pv3,pv7,pv8443], .c 3, .p pv5 [pv2,pv13,pv95471], .c 7, .c 3,
  .p pv2 [pv2,pv23,pv26981], .c 5, .c 3, .c 13, .c 43, .c 3, .c 5, .c 563, .c 3, .c 11, .c 61,
  .c 3, .c 7, .p pv3 [pv2,pv3,pv413713], .c 3, .c 67, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv293,pv353], .c 3, .c 739, .c 137, .c 3, .c 59, .p pv23 [pv2,pv3,pv53,pv1301],
  .c 3, .c 29, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 97, .c 3, .c 19, .c 7, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv79,pv5237], .c 3, .p pv5 [pv2,pv29,pv127,pv337], .c 5, .c 3,
  .p pv2 [pv2,pv11,pv56417], .p pv17 [pv2,pv3,pv5,pv13,pv19,pv67], .c 3, .c 5, .c 17, .c 3, .c 7,
  .c 13, .c 3, .c 23, .c 19, .c 3, .c 71, .c 5, .c 3, .p pv2 [pv2,pv101,pv12289], .c 11, .c 3,
  .c 5, .c 31, .c 3, .c 17, .c 509, .c 3, .c 197, .c 47, .c 3, .c 7, .c 5, .c 3, .c 1153,
  .p pv7 [pv2,pv3,pv5,pv7,pv11821], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv124121], .c 587,
  .c 3, .c 41, .c 29, .c 3, .c 43,
]
private theorem h0303c00 : checkBlock 2482179 128 b0303c00 = true := by
  decide +kernel

private def b0303c01 : List Row := [
  .c 5, .c 3, .p pv7 [pv2,pv7,pv73,pv347], .c 13, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv131,pv379], .c 659, .c 3, .c 263, .c 7, .c 3, .p pv5 [pv2,pv1051,pv1181],
  .c 5, .c 3, .c 11, .c 811, .c 3, .c 5, .c 89, .c 3, .p pv23 [pv2,pv5,pv7,pv11,pv13,pv31], .c 19,
  .c 3, .c 7, .c 149, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv1241249], .c 7, .c 3, .c 5, .c 107,
  .c 3, .c 31, .c 11, .c 3, .c 61, .c 13, .c 3, .p pv2 [pv2,pv7,pv177323], .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv83,pv997], .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv2111], .c 3, .c 241, .c 7,
  .c 3, .c 569, .c 557, .c 3, .p pv3 [pv2,pv37,pv8387], .c 5, .c 3, .c 19, .c 17, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv89,pv4649], .c 3, .c 7, .c 31, .c 3, .c 137, .c 11, .c 3,
  .p pv5 [pv2,pv1241291], .c 5, .c 3, .c 37, .c 41, .c 3, .c 5, .c 13, .c 3, .c 11, .c 29, .c 3,
  .p pv5 [pv2,pv7,pv383,pv463], .c 103, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv67,pv97,pv191],
  .p pv41 [pv2,pv3,pv5,pv7,pv23,pv257], .c 3, .c 5, .c 7, .c 3, .c 271, .c 1193, .c 3, .c 421,
  .c 61, .c 3, .c 23, .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv613], .c 3, .c 5, .c 71, .c 3,
  .c 29, .c 17, .c 3, .c 11, .c 7, .c 3, .c 19, .c 5, .c 3, .c 53, .c 47, .c 3, .c 5, .c 1543,
  .c 3,
]
private theorem h0303c01 : checkBlock 2482435 128 b0303c01 = true := by
  decide +kernel

private def b0303c02 : List Row := [
  .c 43, .c 109, .c 3, .c 7, .c 227, .c 3, .p pv5 [pv2,pv1241351], .c 5, .c 3, .c 307, .c 7, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv313,pv661], .c 3, .c 107, .c 113, .c 3, .c 13, .c 857, .c 3, .c 11,
  .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv13,pv1061], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv59113],
  .c 3, .c 277, .c 7, .c 3, .p pv2 [pv2,pv620689], .c 31, .c 3, .c 691, .c 5, .c 3,
  .p pv3 [pv2,pv19,pv8167], .p pv3 [pv2,pv3,pv5,pv82759], .c 3, .c 5, .c 11, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv17,pv101,pv241], .c 3, .c 19, .c 167, .c 3, .p pv3 [pv2,pv13,pv23873], .c 5,
  .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv2069], .c 3, .c 5, .p pv3 [pv2,pv3,pv19,pv29,pv751], .c 3,
  .c 37, .p pv5 [pv2,pv3,pv79,pv97], .c 3, .c 1327, .c 67, .c 3, .c 7, .c 5, .c 3, .c 379, .c 13,
  .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv62071], .c 11, .c 3, .c 971,
  .p pv7 [pv2,pv3,pv37,pv233], .c 3, .c 1103, .c 5, .c 3, .c 1493, .p pv2 [pv2,pv3,pv5,pv41381],
  .c 3, .c 5, .c 17, .c 3, .p pv41 [pv2,pv5,pv13,pv71,pv269], .c 23, .c 3, .c 257, .c 7, .c 3,
  .c 13, .c 5, .c 3, .p pv3 [pv2,pv310361], .c 53, .c 3, .c 5, .c 59, .c 3, .c 17,
  .p pv11 [pv2,pv3,pv271,pv509], .c 3, .c 7, .c 11, .c 3, .p pv3 [pv2,pv77591], .c 5, .c 3, .c 23,
  .c 7, .c 3, .c 5, .c 1231, .c 3, .c 11, .p pv2 [pv2,pv3,pv206911], .c 3,
  .p pv3 [pv2,pv149,pv2083], .c 19, .c 3, .p pv5 [pv2,pv7,pv11,pv23,pv701], .c 5,
]
private theorem h0303c02 : checkBlock 2482691 128 b0303c02 = true := by
  decide +kernel

private def b0303c03 : List Row := [
  .c 3, .c 7, .c 29, .c 3, .c 5, .c 139, .c 3, .c 13, .c 7, .c 3, .p pv5 [pv2,pv1241483], .c 17,
  .c 3, .p pv2 [pv2,pv620743], .c 5, .c 3, .c 163, .p pv13 [pv2,pv3,pv5,pv29,pv1427], .c 3, .c 5,
  .c 13, .c 3, .c 7, .p pv5 [pv2,pv3,pv43,pv401], .c 3, .c 11, .p pv3 [pv2,pv3,pv7,pv59119], .c 3,
  .c 17, .c 5, .c 3, .c 29, .c 23, .c 3, .c 5, .p pv5 [pv2,pv3,pv307,pv337], .c 3, .c 103, .c 241,
  .c 3, .p pv2 [pv2,pv7,pv13,pv1949], .c 313, .c 3, .c 7, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5,
  .c 7, .c 3, .c 1109, .c 19, .c 3, .c 23, .p pv3 [pv2,pv3,pv421,pv983], .c 3, .c 11, .c 5, .c 3,
  .c 31, .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv206923], .c 3, .c 233, .c 41, .c 3, .c 67, .c 7,
  .c 3, .p pv2 [pv2,pv620773], .c 5, .c 3, .p pv2 [pv2,pv1241549], .c 769, .c 3, .c 5, .c 11,
  .c 3, .c 83, .p pv7 [pv2,pv3,pv157,pv659], .c 3, .c 7, .p pv7 [pv2,pv3,pv11,pv12541], .c 3,
  .c 167, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv479], .c 3,
  .p pv2 [pv2,pv5,pv11,pv11287], .c 13, .c 3, .p pv2 [pv2,pv1241573], .c 23, .c 3, .c 227, .c 5,
  .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv20693], .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv248317],
  .c 7, .c 3, .c 1453, .p pv2 [pv2,pv3,pv413863], .c 3, .c 29, .c 5, .c 3, .c 89, .c 191, .c 3,
  .c 5, .c 281, .c 3, .c 7,
]
private theorem h0303c03 : checkBlock 2482947 128 b0303c03 = true := by
  decide +kernel

private def b0303c04 : List Row := [
  .c 359, .c 3, .c 17, .c 53, .c 3, .c 487, .c 5, .c 3, .p pv2 [pv2,pv23,pv37,pv1459], .c 13,
  .c 3, .c 5, .c 103, .c 3, .c 127, .p pv23 [pv2,pv3,pv25867], .c 3, .c 607, .c 11, .c 3, .c 7,
  .c 5, .c 3, .c 61, .c 59, .c 3, .c 5, .c 7, .c 3, .c 11, .c 613, .c 3, .c 179, .c 157, .c 3,
  .c 13, .c 5, .c 3, .c 571, .c 19, .c 3, .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv167,pv1487], .c 43,
  .c 3, .c 97, .c 7, .c 3, .c 1019, .c 5, .c 3, .c 17, .c 503, .c 3, .c 5, .c 31, .c 3, .c 199,
  .c 307, .c 3, .c 7, .c 37, .c 3, .c 23, .c 5, .c 3, .c 47, .c 7, .c 3, .c 5, .c 109, .c 3,
  .c 13, .c 337, .c 3, .c 19, .c 653, .c 3, .c 107, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 13,
  .c 3, .p pv2 [pv2,pv5,pv227,pv547], .c 7, .c 3, .c 73, .c 1433, .c 3, .c 11, .c 5, .c 3, .c 137,
  .c 113, .c 3, .c 5, .c 461, .c 3, .c 7, .c 419, .c 3, .p pv3 [pv2,pv13,pv23879], .c 449, .c 3,
  .c 439, .c 5, .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv82781], .c 3, .c 5, .c 11, .c 3, .c 31, .c 83,
  .c 3, .p pv5 [pv2,pv7,pv179,pv991], .c 239, .c 3, .c 7, .c 5, .c 3,
]
private theorem h0303c04 : checkBlock 2483203 128 b0303c04 = true := by
  decide +kernel

private def b0303c05 : List Row := [
  .c 11, .p pv43 [pv2,pv3,pv5,pv7,pv73], .c 3, .c 5, .c 7, .c 3, .c 19, .c 29, .c 3, .c 37, .c 17,
  .c 3, .p pv2 [pv2,pv1241741], .c 5, .c 3, .c 67, .c 97, .c 3, .c 5, .c 151, .c 3, .c 181, .c 11,
  .c 3, .c 13, .c 7, .c 3, .c 17, .c 5, .c 3, .p pv11 [pv2,pv953,pv1303],
  .p pv29 [pv2,pv3,pv5,pv13,pv199], .c 3, .c 5, .c 47, .c 3, .c 29, .c 13, .c 3, .c 7, .c 881,
  .c 3, .p pv5 [pv2,pv1241771], .c 5, .c 3, .p pv2 [pv2,pv620887], .c 7, .c 3, .c 5, .c 751, .c 3,
  .p pv3 [pv2,pv5,pv29,pv2141], .c 23, .c 3, .p pv7 [pv2,pv19,pv65357], .c 11, .c 3, .c 191, .c 5,
  .c 3, .c 7, .c 17, .c 3, .c 5, .c 379, .c 3, .c 11, .c 7, .c 3, .c 587,
  .p pv3 [pv2,pv3,pv13,pv17,pv1873], .c 3, .p pv2 [pv2,pv11,pv79,pv1429], .c 5, .c 3, .c 23,
  .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv41,pv631], .c 3, .c 7, .c 19, .c 3, .c 31, .c 131, .c 3,
  .c 53, .c 5, .c 3, .c 103, .p pv7 [pv2,pv3,pv5,pv6899], .c 3, .c 5, .c 29, .c 3, .c 71,
  .p pv5 [pv2,pv3,pv139,pv1489], .c 3, .c 11, .p pv2 [pv2,pv3,pv31,pv4451], .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv11,pv47,pv1201], .p pv3 [pv2,pv3,pv5,pv7,pv11827], .c 3, .c 5, .c 7, .c 3,
  .c 79, .c 17, .c 3, .p pv5 [pv2,pv53,pv23431], .c 13, .c 3, .p pv2 [pv2,pv83,pv7481], .c 5,
  .c 3, .c 19, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv413951], .c 3, .p pv17 [pv2,pv5,pv248371],
  .p pv13 [pv2,pv3,pv7,pv11],
]
private theorem h0303c05 : checkBlock 2483459 128 b0303c05 = true := by
  decide +kernel

private def b0303c06 : List Row := [
  .c 3, .c 17, .c 7, .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv13,pv11941], .c 541, .c 3, .c 5,
  .c 19, .c 3, .c 13, .p pv11 [pv2,pv3,pv103,pv4019], .c 3, .c 7, .p pv2 [pv2,pv3,pv68993], .c 3,
  .p pv3 [pv2,pv73,pv4253], .c 5, .c 3, .c 281, .c 7, .c 3, .c 5, .c 11, .c 3, .c 659, .c 37,
  .c 3, .p pv3 [pv2,pv197], .c 739, .c 3, .c 109, .c 5, .c 3, .c 7, .c 107, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv29569], .c 3, .c 1061, .c 7, .c 3, .c 373, .c 43, .c 3, .c 19, .c 5, .c 3,
  .c 13, .c 29, .c 3, .c 5, .p pv2 [pv2,pv3,pv347,pv1193], .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv17,pv36527], .c 23, .c 3, .c 1499, .c 5, .c 3, .c 743, .c 19, .c 3, .c 5, .c 409,
  .c 3, .p pv2 [pv2,pv5,pv124193], .c 181, .c 3, .p pv7 [pv2,pv7,pv11,pv127],
  .p pv2 [pv2,pv3,pv449,pv461], .c 3, .c 7, .c 5, .c 3, .c 29, .p pv17 [pv2,pv3,pv5,pv7,pv2957],
  .c 3, .c 5, .c 7, .c 3, .c 67, .c 101, .c 3, .c 13, .c 11, .c 3, .c 41, .c 5, .c 3, .c 643,
  .p pv3 [pv2,pv3,pv5,pv11,pv13,pv193], .c 3, .c 5, .p pv5 [pv2,pv3,pv206993], .c 3, .c 11, .c 13,
  .c 3, .c 19, .c 7, .c 3, .c 601, .c 5, .c 3, .p pv23 [pv2,pv17,pv43,pv1699], .c 83, .c 3, .c 5,
  .c 137, .c 3, .c 53, .p pv5 [pv2,pv3,pv51749], .c 3, .c 7, .c 59, .c 3, .c 229, .c 5, .c 3,
  .c 491,
]
private theorem h0303c06 : checkBlock 2483715 128 b0303c06 = true := by
  decide +kernel

private def b0303c07 : List Row := [
  .c 7, .c 3, .c 5, .c 23, .c 3, .c 43, .c 179, .c 3, .c 11, .c 17, .c 3, .c 127, .c 5, .c 3,
  .c 7, .c 13, .c 3, .c 5, .c 1259, .c 3, .p pv41 [pv2,pv5,pv248401], .c 7, .c 3,
  .p pv3 [pv2,pv155251], .p pv19 [pv2,pv3,pv59,pv2339], .c 3, .c 17, .c 5, .c 3, .c 397, .c 11,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv69001], .c 3, .c 7, .c 673, .c 3, .c 619,
  .p pv11 [pv2,pv3,pv7,pv7393], .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv1242029], .c 31, .c 3,
  .c 5, .c 41, .c 3, .c 683, .c 97, .c 3, .c 59, .c 13, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv310511], .c 17, .c 3, .c 5, .c 7, .c 3, .c 151, .c 61, .c 3, .c 83,
  .p pv2 [pv2,pv3,pv11,pv17,pv41], .c 3, .p pv3 [pv2,pv107,pv1451], .c 5, .c 3, .c 11, .c 433,
  .c 3, .c 5, .p pv23 [pv2,pv3,pv138007], .c 3, .c 13, .p pv5 [pv2,pv3,pv7,pv29573], .c 3, .c 733,
  .c 7, .c 3, .c 37, .c 5, .c 3, .c 41, .p pv3 [pv2,pv3,pv5,pv16561], .c 3, .c 5, .c 13, .c 3,
  .c 23, .c 11, .c 3, .c 7, .c 29, .c 3, .c 347, .c 5, .c 3, .p pv2 [pv2,pv1242089], .c 7, .c 3,
  .c 5, .c 487, .c 3, .p pv19 [pv2,pv5,pv41,pv73,pv83], .c 17, .c 3,
  .p pv2 [pv2,pv11,pv13,pv43,pv101], .p pv3 [pv2,pv3,pv29,pv4759], .c 3, .p pv2 [pv2,pv7,pv25349],
  .c 5, .c 3, .c 7, .c 157, .c 3, .c 5, .c 37, .c 3, .c 137, .c 7, .c 3,
]
private theorem h0303c07 : checkBlock 2483971 128 b0303c07 = true := by
  decide +kernel

private def b0303c08 : List Row := [
  .c 17, .c 11, .c 3, .p pv3 [pv2,pv47,pv6607], .c 5, .c 3, .c 43,
  .p pv13 [pv2,pv3,pv5,pv11,pv941], .c 3, .c 5, .c 31, .c 3, .c 7, .c 23, .c 3, .c 89,
  .p pv3 [pv2,pv3,pv7,pv59149], .c 3, .c 73, .c 5, .c 3, .c 19, .p pv11 [pv2,pv3,pv5,pv3067],
  .c 3, .c 5, .c 149, .c 3, .c 313, .c 163, .c 3, .c 13, .p pv7 [pv2,pv3,pv19,pv227], .c 3, .c 7,
  .c 5, .c 3, .c 23, .c 439, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv248431], .c 13, .c 3,
  .c 11, .p pv17 [pv2,pv3,pv414053], .c 3, .p pv2 [pv2,pv23,pv53,pv1019], .c 5, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv5,pv82811], .c 3, .c 5, .c 191, .c 3, .c 179, .c 29, .c 3, .c 61, .c 7, .c 3,
  .p pv3 [pv2,pv13,pv1493], .c 5, .c 3, .p pv11 [pv2,pv137,pv9067], .c 11, .c 3, .c 5, .c 197,
  .c 3, .c 31, .c 47, .c 3, .c 7, .p pv3 [pv2,pv3,pv13,pv3539], .c 3, .c 11, .c 5, .c 3, .c 1093,
  .c 7, .c 3, .c 5, .c 17, .c 3, .c 29, .c 151, .c 3, .c 1427, .c 73, .c 3, .c 277, .c 5, .c 3,
  .c 7, .c 19, .c 3, .c 5, .c 11, .c 3, .c 17, .c 7, .c 3, .c 23, .c 37, .c 3, .c 13, .c 5, .c 3,
  .c 11, .c 607, .c 3, .c 5, .c 283, .c 3, .c 7, .c 103, .c 3, .c 47, .c 13, .c 3,
  .p pv3 [pv2,pv310559], .c 5, .c 3, .c 233, .c 53,
]
private theorem h0303c08 : checkBlock 2484227 128 b0303c08 = true := by
  decide +kernel

private def b0303c09 : List Row := [
  .c 3, .c 5, .c 887, .c 3, .p pv2 [pv2,pv5,pv59,pv4211], .c 11, .c 3, .c 19, .c 17, .c 3, .c 7,
  .c 5, .c 3, .p pv2 [pv2,pv13,pv47779], .c 977, .c 3, .c 5, .c 7, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv83,pv1663], .c 3, .p pv5 [pv2,pv11,pv31,pv3643], .c 23, .c 3, .c 17, .c 5,
  .c 3, .p pv2 [pv2,pv7,pv177467], .c 877, .c 3, .c 5, .c 13, .c 3, .c 307, .c 373, .c 3, .c 31,
  .c 7, .c 3, .p pv2 [pv2,pv577,pv2153], .c 5, .c 3, .p pv3 [pv2,pv310571],
  .p pv11 [pv2,pv3,pv5,pv11,pv7529], .c 3, .c 5, .c 863, .c 3, .c 11, .c 43, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv31,pv6679], .c 3, .p pv3 [pv2,pv11,pv19,pv743], .c 5, .c 3, .c 13, .c 7, .c 3,
  .c 5, .c 1307, .c 3, .c 19, .c 89, .c 3, .p pv3 [pv2,pv310577], .c 31, .c 3,
  .p pv5 [pv2,pv7,pv177473], .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv19,pv1453], .c 3, .c 5,
  .c 823, .c 3, .c 41, .c 7, .c 3, .c 11, .c 19, .c 3, .p pv2 [pv2,pv17,pv61,pv599], .c 5, .c 3,
  .c 617, .c 37, .c 3, .c 5, .c 23, .c 3, .c 7, .p pv5 [pv2,pv3,pv12941], .c 3, .c 13,
  .p pv3 [pv2,pv3,pv7,pv59159], .c 3, .p pv2 [pv2,pv41,pv157,pv193], .c 5, .c 3,
  .p pv3 [pv2,pv83,pv1871], .c 11, .c 3, .c 5, .p pv7 [pv2,pv3,pv103529], .c 3, .c 73, .c 13,
  .c 3, .p pv2 [pv2,pv7,pv19,pv9341], .c 457, .c 3, .c 7, .c 5, .c 3, .c 191,
  .p pv19 [pv2,pv3,pv5,pv7,pv17,pv29], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv248473],
  .p pv7 [pv2,pv3,pv207061], .c 3, .c 17,
]
private theorem h0303c09 : checkBlock 2484483 128 b0303c09 = true := by
  decide +kernel

private def b0303c10 : List Row := [
  .p pv2 [pv2,pv3,pv138041], .c 3, .c 31, .c 5, .c 3, .c 29, .p pv17 [pv2,pv3,pv5,pv3313], .c 3,
  .c 5, .c 11, .c 3, .c 197, .c 19, .c 3, .c 353, .c 7, .c 3, .c 523, .c 5, .c 3, .c 11, .c 13,
  .c 3, .c 5, .c 71, .c 3, .c 89, .c 167, .c 3, .c 7, .c 53, .c 3, .p pv2 [pv2,pv101,pv12301],
  .c 5, .c 3, .c 37, .c 7, .c 3, .c 5, .c 331, .c 3, .c 1303, .c 11, .c 3, .p pv2 [pv2,pv1242413],
  .c 67, .c 3, .c 13, .c 5, .c 3, .c 7, .c 43, .c 3, .c 5, .c 73, .c 3, .c 23, .c 7, .c 3,
  .p pv3 [pv2,pv11,pv17,pv151], .c 13, .c 3, .p pv5 [pv2,pv1061,pv1171], .c 5, .c 3, .c 1201,
  .p pv3 [pv2,pv3,pv5,pv113,pv733], .c 3, .c 5, .c 19, .c 3, .c 7, .c 37, .c 3, .c 41, .c 11,
  .c 3, .p pv2 [pv2,pv621223], .c 5, .c 3, .p pv2 [pv2,pv13,pv31,pv3083],
  .p pv31 [pv2,pv3,pv5,pv11,pv251], .c 3, .c 5, .c 17, .c 3, .c 11, .c 199, .c 3,
  .p pv2 [pv2,pv7,pv88747], .p pv3 [pv2,pv3,pv5113], .c 3, .c 7, .c 5, .c 3, .c 31,
  .p pv2 [pv2,pv3,pv5,pv7,pv11833], .c 3, .c 5, .c 7, .c 3, .c 17, .c 23, .c 3, .c 211, .c 181,
  .c 3, .c 19, .c 5, .c 3, .p pv7 [pv2,pv7,pv17,pv53,pv197], .p pv13 [pv2,pv3,pv5,pv31,pv167],
  .c 3, .c 5, .c 277, .c 3, .p pv2 [pv2,pv5,pv43,pv5779], .p pv2 [pv2,pv3,pv7,pv19,pv173], .c 3,
  .c 11, .c 7, .c 3, .c 113, .c 5, .c 3, .c 13, .c 19, .c 3,
]
private theorem h0303c10 : checkBlock 2484739 128 b0303c10 = true := by
  decide +kernel

private def b0303c11 : List Row := [
  .c 5, .c 401, .c 3, .p pv3 [pv2,pv5,pv7,pv71], .p pv5 [pv2,pv3,pv13,pv31859], .c 3, .c 7, .c 17,
  .c 3, .c 43, .c 5, .c 3, .c 1193, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv17,pv2707], .c 3, .c 37,
  .p pv7 [pv2,pv3,pv11,pv9413], .c 3, .p pv2 [pv2,pv621259], .c 29, .c 3, .c 11, .c 5, .c 3, .c 7,
  .c 41, .c 3, .c 5, .c 179, .c 3, .p pv3 [pv2,pv5,pv17,pv7309], .c 7, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv29,pv37,pv193], .c 3, .p pv3 [pv2,pv155317], .c 5, .c 3, .c 61, .c 23, .c 3,
  .c 5, .c 11, .c 3, .c 7, .c 13, .c 3, .c 29, .c 43, .c 3, .c 79, .c 5, .c 3, .c 11, .c 17, .c 3,
  .c 5, .c 53, .c 3, .p pv3 [pv2,pv5,pv11,pv353], .p pv2 [pv2,pv3,pv239,pv1733], .c 3, .c 23,
  .p pv7 [pv2,pv3,pv17,pv6091], .c 3, .c 7, .c 5, .c 3, .c 59, .c 1489, .c 3, .c 5, .c 7, .c 3,
  .c 251, .c 11, .c 3, .c 641, .p pv3 [pv2,pv3,pv13,pv151,pv211], .c 3, .c 421, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv22189], .c 13, .c 3, .c 5, .c 31, .c 3, .c 19,
  .p pv3 [pv2,pv3,pv7,pv79,pv107], .c 3, .p pv2 [pv2,pv11,pv83,pv1361], .c 7, .c 3,
  .p pv3 [pv2,pv241,pv1289], .c 5, .c 3, .c 1123, .c 61, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv101,pv1367], .c 3, .p pv2 [pv2,pv5,pv7,pv13,pv2731], .c 17, .c 3, .c 7, .c 11,
  .c 3, .c 13, .c 5, .c 3, .c 349, .c 7, .c 3, .c 5, .c 97, .c 3, .c 11,
  .p pv13 [pv2,pv3,pv23,pv29], .c 3, .c 17, .c 13,
]
private theorem h0303c11 : checkBlock 2484995 128 b0303c11 = true := by
  decide +kernel

private def b0303c12 : List Row := [
  .c 3, .c 37, .c 5, .c 3, .c 7, .c 79, .c 3, .c 5, .c 677, .c 3, .c 29, .c 7, .c 3,
  .p pv2 [pv2,pv19,pv53,pv617], .p pv3 [pv2,pv3,pv138071], .c 3, .p pv2 [pv2,pv1242641], .c 5,
  .c 3, .c 107, .c 269, .c 3, .c 5, .c 41, .c 3, .c 7, .p pv5 [pv2,pv3,pv414217], .c 3, .c 11,
  .c 109, .c 3, .c 47, .c 5, .c 3, .p pv7 [pv2,pv11,pv173,pv653], .c 389, .c 3, .c 5, .c 13, .c 3,
  .c 1163, .c 19, .c 3, .c 229, .p pv2 [pv2,pv3,pv41,pv10103], .c 3, .c 7, .c 5, .c 3, .c 17,
  .c 11, .c 3, .c 5, .c 7, .c 3, .c 239, .c 31, .c 3, .p pv5 [pv2,pv13,pv17,pv5623], .c 211, .c 3,
  .c 11, .c 5, .c 3, .c 13, .p pv7 [pv2,pv3,pv5,pv23,pv1801], .c 3, .c 5, .c 29, .c 3,
  .p pv19 [pv2,pv5,pv19,pv103,pv127], .p pv5 [pv2,pv3,pv7,pv13,pv569], .c 3,
  .p pv2 [pv2,pv107,pv5807], .c 7, .c 3, .c 23, .c 5, .c 3, .c 19, .c 233, .c 3, .c 5, .c 11,
  .c 3, .p pv2 [pv2,pv5,pv7,pv41,pv433], .c 227, .c 3, .c 7, .p pv2 [pv2,pv3,pv11,pv19,pv991],
  .c 3, .c 241, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 19, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv207121], .c 3, .c 13, .c 139, .c 3, .c 131, .c 5, .c 3, .c 7, .c 1327, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv7,pv1409], .c 3, .p pv3 [pv2,pv5,pv62137], .c 7, .c 3, .c 31,
  .p pv7 [pv2,pv3,pv53,pv977], .c 3, .c 59, .c 5, .c 3, .c 67, .c 47, .c 3, .c 5,
]
private theorem h0303c12 : checkBlock 2485251 128 b0303c12 = true := by
  decide +kernel

private def b0303c13 : List Row := [
  .p pv2 [pv2,pv3,pv61,pv6791], .c 3, .c 7, .p pv5 [pv2,pv3,pv37,pv311], .c 3, .c 127, .c 17,
  .c 3, .c 19, .c 5, .c 3, .c 43, .c 479, .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv1523], .c 3, .c 23,
  .c 41, .c 3, .p pv2 [pv2,pv7,pv177539], .c 11, .c 3, .c 7, .c 5, .c 3,
  .p pv13 [pv2,pv223,pv5573], .c 13, .c 3, .c 5, .c 7, .c 3, .c 11, .p pv5 [pv2,pv3,pv43,pv4817],
  .c 3, .c 73, .p pv2 [pv2,pv3,pv349,pv1187], .c 3, .c 719, .c 5, .c 3, .c 283, .c 137, .c 3,
  .c 5, .c 317, .c 3, .c 83, .c 733, .c 3, .p pv5 [pv2,pv1242803], .c 7, .c 3, .c 13, .c 5, .c 3,
  .c 29, .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv13,pv2897], .c 3, .p pv7 [pv2,pv5,pv7,pv35509],
  .c 23, .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv31,pv47,pv853], .c 5, .c 3,
  .p pv3 [pv2,pv11,pv29,pv487], .c 7, .c 3, .c 5, .p pv13 [pv2,pv3,pv19,pv23,pv79], .c 3, .c 113,
  .p pv3 [pv2,pv3,pv414277], .c 3, .p pv2 [pv2,pv41,pv30313], .p pv2 [pv2,pv3,pv207139], .c 3,
  .c 31, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv59183], .c 3, .c 13, .c 7,
  .c 3, .c 37, .c 103, .c 3, .c 11, .c 5, .c 3, .c 199, .c 101, .c 3, .c 5, .c 13, .c 3, .c 7,
  .c 17, .c 3, .p pv5 [pv2,pv281,pv4423], .c 59, .c 3, .p pv2 [pv2,pv19,pv32707], .c 5, .c 3,
  .p pv2 [pv2,pv1242869], .c 1031, .c 3, .c 5, .c 11, .c 3, .c 19, .c 53, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv11,pv37663], .c 3,
]
private theorem h0303c13 : checkBlock 2485507 128 b0303c13 = true := by
  decide +kernel

private def b0303c14 : List Row := [
  .c 7, .c 5, .c 3, .c 11, .c 23, .c 3, .c 5, .c 7, .c 3, .c 71, .c 47, .c 3, .c 43, .c 19, .c 3,
  .c 29, .c 5, .c 3, .c 401, .p pv13 [pv2,pv3,pv5,pv1381], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv53,pv7817], .c 3, .c 61, .c 11, .c 3, .c 23, .c 7, .c 3, .c 311, .c 5, .c 3,
  .c 269, .p pv3 [pv2,pv3,pv5,pv41,pv43,pv47], .c 3, .c 5, .c 173, .c 3, .c 467, .c 797, .c 3,
  .c 7, .p pv13 [pv2,pv3,pv103577], .c 3, .c 433, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv414311], .c 3, .c 41, .c 13, .c 3, .c 47, .c 11, .c 3, .c 271, .c 5, .c 3,
  .c 7, .c 557, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv14797], .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv59,pv21067], .c 23, .c 3, .c 101, .c 5, .c 3, .c 37, .c 31, .c 3, .c 5, .c 17,
  .c 3, .c 7, .c 61, .c 3, .p pv3 [pv2,pv155371], .p pv11 [pv2,pv3,pv7,pv13,pv29,pv157], .c 3,
  .c 197, .c 5, .c 3, .p pv2 [pv2,pv89,pv6983], .c 13, .c 3, .c 5, .c 839, .c 3, .c 17, .c 109,
  .c 3, .c 11, .c 1087, .c 3, .c 7, .c 5, .c 3, .c 19, .c 1423, .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv13,pv1471], .c 37, .c 3, .p pv2 [pv2,pv29,pv739],
  .p pv29 [pv2,pv3,pv19,pv2423], .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv7,pv103,pv431], .c 11,
  .c 3, .c 5, .c 19,
]
private theorem h0303c14 : checkBlock 2485763 128 b0303c14 = true := by
  decide +kernel

private def b0303c15 : List Row := [
  .c 3, .c 661, .c 1399, .c 3, .p pv2 [pv2,pv1243013], .c 7, .c 3, .c 11, .c 5, .c 3,
  .p pv17 [pv2,pv107,pv11617], .p pv7 [pv2,pv3,pv5,pv20717], .c 3, .c 5, .c 23, .c 3, .c 79,
  .c 383, .c 3, .c 7, .p pv2 [pv2,pv3,pv367,pv1129], .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv47809], .c 7, .c 3, .c 5, .c 11, .c 3, .c 13, .c 29, .c 3, .c 907,
  .p pv83 [pv2,pv3,pv11,pv43,pv73], .c 3, .c 19, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv8287],
  .c 3, .c 5, .c 13, .c 3, .c 103, .c 7, .c 3, .c 41, .c 911, .c 3, .p pv2 [pv2,pv941,pv1321],
  .c 5, .c 3, .c 167, .c 17, .c 3, .c 5, .p pv7 [pv2,pv3,pv71,pv1459], .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv13,pv95621], .p pv2 [pv2,pv3,pv7,pv17,pv1741], .c 3, .p pv3 [pv2,pv127,pv2447],
  .c 5, .c 3, .c 13, .c 73, .c 3, .c 5, .p pv3 [pv2,pv3,pv414361], .c 3, .c 829, .c 461, .c 3,
  .c 53, .c 353, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv19,pv32713],
  .p pv7 [pv2,pv3,pv5,pv7,pv11839], .c 3, .c 5, .c 7, .c 3, .c 59, .p pv2 [pv2,pv3,pv414367],
  .c 3, .c 19, .c 11, .c 3, .c 211, .c 5, .c 3, .p pv2 [pv2,pv7,pv257,pv691],
  .p pv19 [pv2,pv3,pv5,pv11,pv3767], .c 3, .c 5, .c 223, .c 3, .c 11, .c 17, .c 3, .c 13, .c 7,
  .c 3, .p pv2 [pv2,pv11,pv113011], .c 5, .c 3, .c 131, .p pv2 [pv2,pv3,pv5,pv13,pv17], .c 3,
  .c 5, .c 29, .c 3, .c 887, .c 13, .c 3, .c 7, .p pv2 [pv2,pv3,pv23021], .c 3,
  .p pv3 [pv2,pv607],
]
private theorem h0303c15 : checkBlock 2486019 128 b0303c15 = true := by
  decide +kernel

private def b0303c16 : List Row := [
  .c 5, .c 3, .c 127, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv29,pv433], .c 3,
  .p pv2 [pv2,pv5,pv109,pv2281], .c 31, .c 3, .c 11, .c 61, .c 3, .c 43, .c 5, .c 3, .c 7, .c 409,
  .c 3, .c 5, .c 101, .c 3, .c 19, .c 7, .c 3, .c 1039, .c 503, .c 3, .p pv2 [pv2,pv621583], .c 5,
  .c 3, .c 113, .c 11, .c 3, .c 5, .c 47, .c 3, .c 7, .c 1553, .c 3, .c 1063, .c 19, .c 3, .c 11,
  .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv67,pv1237], .c 3, .c 5, .c 953, .c 3,
  .p pv2 [pv2,pv5,pv13,pv73,pv131], .p pv3 [pv2,pv3,pv414397], .c 3,
  .p pv7 [pv2,pv7,pv17,pv31,pv337], .c 43, .c 3, .c 7, .c 5, .c 3, .c 109, .c 97, .c 3, .c 5,
  .c 7, .c 3, .c 397, .c 137, .c 3, .c 31, .c 13, .c 3, .p pv5 [pv2,pv1243211], .c 5, .c 3, .c 11,
  .c 29, .c 3, .c 5, .c 17, .c 3, .c 47, .p pv2 [pv2,pv3,pv7,pv53,pv1117], .c 3, .c 701, .c 7,
  .c 3, .c 73, .c 5, .c 3, .p pv2 [pv2,pv13,pv95633], .c 23, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv107,pv1291], .c 3, .c 13, .c 11, .c 3, .c 7, .c 31, .c 3,
  .p pv2 [pv2,pv61,pv89,pv229], .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .c 13, .c 3,
  .p pv2 [pv2,pv5,pv4973], .c 1373, .c 3, .c 23, .p pv2 [pv2,pv3,pv109,pv1901], .c 3,
  .p pv3 [pv2,pv7,pv149], .c 5, .c 3, .c 7, .p pv29 [pv2,pv3,pv5,pv6907], .c 3, .c 5, .c 41, .c 3,
]
private theorem h0303c16 : checkBlock 2486275 128 b0303c16 = true := by
  decide +kernel

private def b0303c17 : List Row := [
  .p pv2 [pv2,pv5,pv19,pv23,pv569], .c 7, .c 3, .c 457, .c 11, .c 3, .c 61, .c 5, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv5,pv11,pv137], .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv239], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv13,pv71,pv449], .c 3, .p pv5 [pv2,pv157,pv7919], .c 281, .c 3, .c 17, .c 5,
  .c 3, .p pv2 [pv2,pv181,pv6869], .p pv2 [pv2,pv3,pv5,pv41443], .c 3, .c 5, .c 19, .c 3,
  .p pv7 [pv2,pv5,pv17,pv14627], .p pv11 [pv2,pv3,pv1439], .c 3, .c 83, .c 23, .c 3, .c 7, .c 5,
  .c 3, .c 41, .p pv2 [pv2,pv3,pv5,pv7,pv3947], .c 3, .c 5, .c 7, .c 3, .c 677,
  .p pv5 [pv2,pv3,pv23,pv37,pv487], .c 3, .c 11, .c 47, .c 3, .c 71, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv11,pv67,pv241], .c 17, .c 3, .c 5, .c 43, .c 3, .p pv2 [pv2,pv5,pv41,pv1213],
  .c 13, .c 3, .c 251, .c 7, .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv23,pv151,pv179], .c 11, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv47,pv4409], .c 3, .p pv3 [pv2,pv5,pv7,pv83,pv107], .c 79, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv25903], .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv1243349], .c 7, .c 3, .c 5,
  .c 53, .c 3, .c 229, .p pv7 [pv2,pv3,pv103613], .c 3, .p pv2 [pv2,pv621679], .c 433, .c 3,
  .c 47, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 11, .c 3, .c 773, .c 7, .c 3,
  .p pv2 [pv2,pv1243373], .c 89, .c 3, .p pv3 [pv2,pv77711], .c 5, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv5,pv17,pv23,pv53], .c 3, .c 5, .p pv5 [pv2,pv3,pv414461], .c 3, .c 7, .c 41,
  .c 3, .c 17, .c 29, .c 3, .c 13, .c 5,
]
private theorem h0303c17 : checkBlock 2486531 128 b0303c17 = true := by
  decide +kernel

private def b0303c18 : List Row := [
  .c 3, .c 31, .c 59, .c 3, .c 5, .c 167, .c 3, .p pv3 [pv2,pv5,pv6217], .c 11, .c 3, .c 37,
  .c 13, .c 3, .c 7, .c 5, .c 3, .c 43, .c 743, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv248683],
  .p pv5 [pv2,pv3,pv103,pv503], .c 3, .c 29, .c 67, .c 3, .p pv2 [pv2,pv1243421], .c 5, .c 3,
  .c 139, .c 31, .c 3, .c 5, .p pv5 [pv2,pv3,pv103619], .c 3, .c 13,
  .p pv3 [pv2,pv3,pv7,pv17,pv43], .c 3, .p pv2 [pv2,pv29,pv53,pv809], .c 7, .c 3,
  .p pv3 [pv2,pv19,pv16361], .c 5, .c 3, .c 17, .c 37, .c 3, .c 5, .c 13, .c 3, .c 11, .c 1571,
  .c 3, .c 7, .c 1097, .c 3, .c 199, .c 5, .c 3, .c 59, .c 7, .c 3, .c 5, .c 71, .c 3, .c 23,
  .c 101, .c 3, .c 89, .c 19, .c 3, .c 929, .c 5, .c 3, .c 7, .c 613, .c 3, .c 5, .c 17, .c 3,
  .p pv11 [pv2,pv5,pv49739], .c 7, .c 3, .c 11, .c 149, .c 3, .p pv2 [pv2,pv1243481], .c 5, .c 3,
  .p pv19 [pv2,pv11,pv59,pv479], .p pv2 [pv2,pv3,pv5,pv61,pv151], .c 3, .c 5, .c 541, .c 3, .c 7,
  .c 97, .c 3, .p pv2 [pv2,pv19,pv65447], .c 257, .c 3, .p pv3 [pv2,pv37,pv4201], .c 5, .c 3,
  .c 79, .c 11, .c 3, .c 5, .c 307, .c 3, .c 29, .c 23, .c 3, .c 13, .c 41, .c 3, .c 7, .c 5,
  .c 3, .c 37, .c 61, .c 3, .c 5, .c 7, .c 3, .c 127,
]
private theorem h0303c18 : checkBlock 2486787 128 b0303c18 = true := by
  decide +kernel

private def b0303c19 : List Row := [
  .c 13, .c 3, .p pv5 [pv2,pv1243523], .c 17, .c 3, .c 109, .c 5, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv5,pv41,pv337], .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv248707],
  .p pv5 [pv2,pv3,pv7,pv3701], .c 3, .c 43, .c 7, .c 3, .c 17, .c 5, .c 3, .c 11,
  .p pv43 [pv2,pv3,pv5,pv82903], .c 3, .c 5, .p pv5 [pv2,pv3,pv34543], .c 3, .c 41, .c 37, .c 3,
  .c 7, .c 487, .c 3, .p pv3 [pv2,pv310889], .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 29, .c 3,
  .c 53, .c 11, .c 3, .p pv3 [pv2,pv77723], .p pv2 [pv2,pv3,pv19,pv21817], .c 3,
  .p pv5 [pv2,pv7,pv41,pv619], .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 19, .c 3, .c 31, .c 7,
  .c 3, .p pv5 [pv2,pv11,pv131,pv863], .c 229, .c 3, .c 13, .c 5, .c 3, .c 1049, .c 1381, .c 3,
  .c 5, .c 1129, .c 3, .c 7, .c 47, .c 3, .c 23, .c 11, .c 3, .p pv2 [pv2,pv17,pv191,pv383], .c 5,
  .c 3, .c 547, .p pv11 [pv2,pv3,pv5,pv11,pv7537], .c 3, .c 5, .c 163, .c 3, .c 11, .c 31, .c 3,
  .p pv2 [pv2,pv7,pv101,pv1759], .p pv2 [pv2,pv3,pv207269], .c 3, .c 7, .c 5, .c 3, .c 227, .c 67,
  .c 3, .c 5, .c 7, .c 3, .c 13, .c 17, .c 3, .c 149, .p pv2 [pv2,pv3,pv138181], .c 3, .c 59,
  .c 5, .c 3, .p pv2 [pv2,pv7,pv211,pv421], .c 19, .c 3, .c 5, .c 13, .c 3,
  .p pv3 [pv2,pv5,pv31091], .c 89, .c 3, .c 11, .c 7, .c 3, .p pv2 [pv2,pv43,pv14461], .c 5, .c 3,
]
private theorem h0303c19 : checkBlock 2487043 128 b0303c19 = true := by
  decide +kernel

private def b0303c20 : List Row := [
  .p pv2 [pv2,pv11,pv167,pv677], .c 29, .c 3, .c 5, .p pv5 [pv2,pv3,pv41,pv10111], .c 3, .c 1151,
  .p pv5 [pv2,pv3,pv23,pv751], .c 3, .c 7, .p pv3 [pv2,pv3,pv414553], .c 3, .c 349, .c 5, .c 3,
  .c 13, .c 7, .c 3, .c 5, .c 811, .c 3, .p pv2 [pv2,pv5,pv124367], .c 53, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv853], .c 3, .c 11, .c 5, .c 3, .c 7, .c 241, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv19,pv1039], .c 3, .c 97, .c 7, .c 3, .c 379, .c 1019, .c 3,
  .p pv5 [pv2,pv1243691], .c 5, .c 3, .c 17, .p pv7 [pv2,pv3,pv5,pv82913], .c 3, .c 5, .c 11,
  .c 3, .c 7, .c 401, .c 3, .c 13, .c 31, .c 3, .p pv2 [pv2,pv281,pv2213], .c 5, .c 3, .c 11,
  .c 43, .c 3, .c 5, .c 23, .c 3, .p pv7 [pv2,pv5,pv11,pv22613], .c 13, .c 3, .c 797,
  .p pv3 [pv2,pv3,pv138191], .c 3, .c 7, .c 5, .c 3, .c 53, .c 457, .c 3, .c 5, .c 7, .c 3, .c 19,
  .c 11, .c 3, .p pv2 [pv2,pv227,pv5479], .c 113, .c 3, .c 23, .c 5, .c 3, .c 211,
  .p pv17 [pv2,pv3,pv5,pv19,pv1091], .c 3, .c 5, .c 1109, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv7,pv9871], .c 3, .p pv3 [pv2,pv11,pv23,pv1229], .c 7, .c 3, .c 257, .c 5,
  .c 3, .c 67, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv207293], .c 3, .p pv3 [pv2,pv5,pv7,pv2221],
  .p pv2 [pv2,pv3,pv47,pv8821], .c 3, .c 7, .c 11, .c 3, .c 29, .c 5, .c 3, .c 601, .c 7, .c 3,
  .c 5, .c 37, .c 3, .c 11, .c 103,
]
private theorem h0303c20 : checkBlock 2487299 128 b0303c20 = true := by
  decide +kernel

private def b0303c21 : List Row := [
  .c 3, .p pv2 [pv2,pv19,pv71,pv461], .c 17, .c 3, .c 13, .c 5, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv5,pv283,pv293], .c 3, .c 5, .c 193, .c 3, .p pv2 [pv2,pv5,pv61,pv2039], .c 7,
  .c 3, .p pv2 [pv2,pv1243793], .c 13, .c 3, .c 17, .c 5, .c 3, .p pv7 [pv2,pv109,pv11411],
  .p pv11 [pv2,pv3,pv5,pv691], .c 3, .c 5, .c 1237, .c 3, .c 7, .c 19, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv7,pv6581], .c 3, .p pv5 [pv2,pv1243811], .c 5, .c 3,
  .p pv3 [pv2,pv11,pv13,pv4349], .c 79, .c 3, .c 5, .p pv2 [pv2,pv3,pv43,pv1607], .c 3, .c 13,
  .c 67, .c 3, .c 599, .c 29, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv37,pv33617], .c 11, .c 3,
  .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv19,pv13093], .p pv5 [pv2,pv3,pv11,pv349], .c 3,
  .p pv2 [pv2,pv59,pv83,pv127], .c 43, .c 3, .c 11, .c 5, .c 3, .c 19,
  .p pv13 [pv2,pv3,pv5,pv131,pv211], .c 3, .c 5, .p pv5 [pv2,pv3,pv51827], .c 3,
  .p pv2 [pv2,pv5,pv24877], .c 23, .c 3, .c 29, .c 7, .c 3, .p pv3 [pv2,pv17,pv269], .c 5, .c 3,
  .c 13, .c 641, .c 3, .c 5, .c 11, .c 3, .c 101, .c 919, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv11,pv37693], .c 3, .p pv5 [pv2,pv179,pv6949], .c 5, .c 3, .c 11, .c 7, .c 3,
  .c 5, .c 41, .c 3, .c 619, .c 17, .c 3, .c 53, .c 37, .c 3, .p pv3 [pv2,pv7,pv23,pv3863], .c 5,
  .c 3, .c 7, .c 31, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv59233], .c 3, .p pv11 [pv2,pv5,pv248779],
  .c 7, .c 3, .c 13, .c 167, .c 3, .c 19, .c 5, .c 3, .p pv3 [pv2,pv43,pv113],
]
private theorem h0303c21 : checkBlock 2487555 128 b0303c21 = true := by
  decide +kernel

private def b0303c22 : List Row := [
  .p pv7 [pv2,pv3,pv5,pv13,pv6379], .c 3, .c 5, .c 89, .c 3, .c 7, .c 13, .c 3,
  .p pv2 [pv2,pv11,pv113083], .c 829, .c 3, .p pv3 [pv2,pv101,pv3079], .c 5, .c 3, .c 41, .c 19,
  .c 3, .c 5, .c 571, .c 3, .c 43, .c 59, .c 3, .c 107, .c 11, .c 3, .c 7, .c 5, .c 3, .c 163,
  .c 857, .c 3, .c 5, .c 7, .c 3, .c 11, .p pv2 [pv2,pv3,pv17,pv24391], .c 3, .c 23, .c 1429,
  .c 3, .c 367, .c 5, .c 3, .c 17, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv89,pv1553], .c 3, .c 67,
  .c 73, .c 3, .c 19, .c 7, .c 3, .p pv2 [pv2,pv1243961], .c 5, .c 3, .c 823,
  .p pv3 [pv2,pv3,pv5,pv127,pv653], .c 3, .c 5, .c 43, .c 3, .c 911, .p pv3 [pv2,pv3,pv46073],
  .c 3, .c 7, .p pv2 [pv2,pv3,pv207329], .c 3, .c 13, .c 5, .c 3, .p pv11 [pv2,pv11,pv113089],
  .c 7, .c 3, .c 5, .c 17, .c 3, .c 59, .c 983, .c 3, .p pv3 [pv2,pv310997], .c 13, .c 3,
  .p pv5 [pv2,pv7,pv71,pv2503], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 29, .c 3, .c 17, .c 7,
  .c 3, .c 61, .p pv7 [pv2,pv3,pv83,pv1249], .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv17,pv433], .c 349, .c 3, .c 5, .c 151, .c 3, .c 7, .c 631, .c 3, .c 313,
  .c 47, .c 3, .p pv2 [pv2,pv1244021], .c 5, .c 3, .c 877, .c 271, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv31,pv4013], .c 751, .c 3,
]
private theorem h0303c22 : checkBlock 2487811 128 b0303c22 = true := by
  decide +kernel

private def b0303c23 : List Row := [
  .p pv2 [pv2,pv7,pv43,pv4133], .c 17, .c 3, .c 7, .c 5, .c 3, .c 11, .c 673, .c 3, .c 5, .c 7,
  .c 3, .c 31, .c 607, .c 3, .c 199, .p pv3 [pv2,pv3,pv414683], .c 3, .c 17, .c 5, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv5,pv197,pv421], .c 3, .c 5, .c 23, .c 3, .p pv3 [pv2,pv5,pv17,pv3659], .c 11,
  .c 3, .c 331, .c 7, .c 3, .c 47, .c 5, .c 3, .c 37, .p pv11 [pv2,pv3,pv5,pv23,pv601], .c 3,
  .c 5, .c 97, .c 3, .c 149, .c 31, .c 3, .c 7, .p pv3 [pv2,pv3,pv15359], .c 3, .c 23, .c 5, .c 3,
  .c 683, .c 7, .c 3, .c 5, .c 1021, .c 3, .p pv3 [pv2,pv5,pv47,pv2647], .c 19, .c 3, .c 13,
  .c 11, .c 3, .p pv5 [pv2,pv7,pv2777], .c 5, .c 3, .c 7, .c 853, .c 3, .c 5, .c 59, .c 3, .c 11,
  .c 7, .c 3, .p pv3 [pv2,pv311027], .p pv2 [pv2,pv3,pv414703], .c 3,
  .p pv5 [pv2,pv11,pv17,pv6653], .c 5, .c 3, .c 29, .p pv3 [pv2,pv3,pv5,pv27647], .c 3, .c 5,
  .c 569, .c 3, .c 7, .c 263, .c 3, .p pv5 [pv2,pv31,pv67,pv599], .c 41, .c 3,
  .p pv2 [pv2,pv13,pv109,pv439], .c 5, .c 3, .c 19, .p pv2 [pv2,pv3,pv5,pv113,pv367], .c 3, .c 5,
  .p pv11 [pv2,pv3,pv11,pv59,pv71], .c 3, .p pv7 [pv2,pv5,pv248827], .c 17, .c 3, .c 11, .c 179,
  .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv11,pv7069], .c 13, .c 3, .c 5, .c 7, .c 3, .c 23, .c 547,
  .c 3, .c 17, .p pv13 [pv2,pv3,pv31,pv6689], .c 3, .c 67, .c 5, .c 3, .p pv7 [pv2,pv7,pv25391],
  .c 11,
]
private theorem h0303c23 : checkBlock 2488067 128 b0303c23 = true := by
  decide +kernel

private def b0303c24 : List Row := [
  .c 3, .c 5, .p pv3 [pv2,pv3,pv414721], .c 3, .c 41, .p pv5 [pv2,pv3,pv7,pv11,pv2693], .c 3,
  .c 71, .c 7, .c 3, .c 11, .c 5, .c 3, .c 193, .c 73, .c 3, .c 5, .p pv29 [pv2,pv3,pv13,pv409],
  .c 3, .c 37, .p pv2 [pv2,pv3,pv641,pv647], .c 3, .c 7, .c 13, .c 3, .c 19, .c 5, .c 3,
  .p pv2 [pv2,pv139,pv8951], .c 7, .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv248839], .c 23,
  .c 3, .p pv2 [pv2,pv397,pv1567], .p pv3 [pv2,pv3,pv11,pv37,pv1019], .c 3, .c 29, .c 5, .c 3,
  .c 7, .c 19, .c 3, .c 5, .p pv11 [pv2,pv3,pv7,pv23], .c 3, .c 13, .c 7, .c 3,
  .p pv2 [pv2,pv17,pv73189], .p pv13 [pv2,pv3,pv23041], .c 3, .c 389, .c 5, .c 3, .c 23, .c 419,
  .c 3, .c 5, .c 13, .c 3, .c 7, .c 11, .c 3, .c 223, .c 719, .c 3, .c 31, .c 5, .c 3,
  .p pv2 [pv2,pv19,pv137,pv239], .p pv3 [pv2,pv3,pv5,pv109,pv761], .c 3, .c 5, .c 17, .c 3,
  .p pv11 [pv2,pv5,pv103,pv151], .c 1063, .c 3, .c 19, .p pv7 [pv2,pv3,pv103687], .c 3, .c 7,
  .c 5, .c 3, .c 13, .c 509, .c 3, .c 5, .c 7, .c 3, .c 17, .c 499, .c 3, .c 139, .c 11, .c 3,
  .c 859, .c 5, .c 3, .c 89, .c 23, .c 3, .c 5, .p pv11 [pv2,pv3,pv41,pv281], .c 3, .c 11, .c 229,
  .c 3, .p pv2 [pv2,pv37,pv33629], .c 7, .c 3, .p pv3 [pv2,pv11,pv28279], .c 5, .c 3,
  .p pv13 [pv2,pv1244279], .c 59, .c 3, .c 5, .p pv7 [pv2,pv3,pv241,pv1721], .c 3, .c 1091,
  .p pv2 [pv2,pv3,pv69127], .c 3, .c 7,
]
private theorem h0303c24 : checkBlock 2488323 128 b0303c24 = true := by
  decide +kernel

private def b0303c25 : List Row := [
  .c 17, .c 3, .c 37, .c 5, .c 3, .c 83, .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv11,pv17,pv1109],
  .c 3, .c 19, .c 13, .c 3, .c 11, .p pv11 [pv2,pv3,pv8641], .c 3, .c 17, .c 5, .c 3, .c 7, .c 71,
  .c 3, .c 5, .c 367, .c 3, .c 151, .c 7, .c 3, .c 179, .c 19, .c 3, .c 73, .c 5, .c 3, .c 31,
  .c 11, .c 3, .c 5, .c 37, .c 3, .c 7, .c 313, .c 3, .p pv2 [pv2,pv1244333], .c 23, .c 3, .c 11,
  .c 5, .c 3, .c 59, .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv103,pv4027], .c 3, .c 439, .c 29, .c 3,
  .c 47, .p pv3 [pv2,pv3,pv17,pv2711], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv622177], .c 31, .c 3,
  .c 5, .c 7, .c 3, .c 53, .p pv2 [pv2,pv3,pv29,pv14303], .c 3, .p pv5 [pv2,pv1244363], .c 97,
  .c 3, .c 13, .c 5, .c 3, .c 11, .c 41, .c 3, .c 5, .c 149, .c 3, .c 29, .c 19, .c 3,
  .p pv2 [pv2,pv622189], .c 7, .c 3, .c 71, .c 5, .c 3, .c 263, .p pv2 [pv2,pv3,pv5,pv27653],
  .c 3, .c 5, .p pv5 [pv2,pv3,pv103699], .c 3, .p pv2 [pv2,pv5,pv7,pv29,pv613], .c 11, .c 3, .c 7,
  .c 73, .c 3, .c 397, .c 5, .c 3, .p pv11 [pv2,pv13,pv95723], .c 7, .c 3, .c 5, .c 23, .c 3,
  .c 13, .c 1301, .c 3, .c 17, .c 127, .c 3, .c 41, .c 5, .c 3, .c 7, .c 1493, .c 3,
]
private theorem h0303c25 : checkBlock 2488579 128 b0303c25 = true := by
  decide +kernel

private def b0303c26 : List Row := [
  .c 5, .c 13, .c 3, .p pv7 [pv2,pv5,pv43,pv1447], .c 7, .c 3, .c 163, .c 11, .c 3, .c 23, .c 5,
  .c 3, .c 1543, .c 61, .c 3, .c 5, .c 19, .c 3, .c 7, .c 1277, .c 3,
  .p pv2 [pv2,pv13,pv23,pv2081], .c 37, .c 3, .c 43, .c 5, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv5,pv82963], .c 3, .c 5, .c 31, .c 3, .p pv2 [pv2,pv5,pv24889], .c 223, .c 3,
  .p pv2 [pv2,pv7,pv109,pv233], .p pv13 [pv2,pv3,pv207409], .c 3, .c 7, .c 5, .c 3, .c 17, .c 83,
  .c 3, .c 5, .c 7, .c 3, .c 181, .c 53, .c 3, .c 11, .c 461, .c 3, .c 19, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv11,pv8081], .c 173, .c 3, .c 5, .c 523, .c 3, .p pv7 [pv2,pv5,pv3889],
  .p pv2 [pv2,pv3,pv7,pv19,pv3119], .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv622243], .c 5, .c 3,
  .c 47, .c 11, .c 3, .c 5, .c 17, .c 3, .c 23, .c 13, .c 3, .c 7, .c 619, .c 3, .c 11, .c 5,
  .c 3, .c 647, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv137,pv757], .c 3, .c 17, .c 563, .c 3, .c 37,
  .c 373, .c 3, .c 59, .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .c 11, .c 3, .c 113, .c 7, .c 3,
  .c 19, .c 1289, .c 3, .c 89, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv19,pv1213],
  .c 3, .c 7, .c 23, .c 3, .c 83, .c 17,
]
private theorem h0303c26 : checkBlock 2488835 128 b0303c26 = true := by
  decide +kernel

private def b0303c27 : List Row := [
  .c 3, .c 1097, .c 5, .c 3, .c 29, .c 37, .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv23,pv1061], .c 3,
  .p pv7 [pv2,pv5,pv13,pv41,pv467], .c 11, .c 3, .c 67, .p pv3 [pv2,pv3,pv71,pv5843], .c 3, .c 7,
  .c 5, .c 3, .c 23, .c 131, .c 3, .c 5, .c 7, .c 3, .c 43, .p pv5 [pv2,pv3,pv414857], .c 3,
  .p pv2 [pv2,pv11,pv113143], .c 13, .c 3, .c 137, .c 5, .c 3, .p pv7 [pv2,pv7,pv177797],
  .p pv37 [pv2,pv3,pv5,pv20743], .c 3, .c 5, .c 47, .c 3, .c 19, .c 163, .c 3, .c 883, .c 7, .c 3,
  .p pv5 [pv2,pv1244591], .c 5, .c 3, .c 71, .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv207433], .c 3,
  .c 11, .c 1009, .c 3, .c 7, .c 19, .c 3, .p pv2 [pv2,pv11,pv37,pv139], .c 5, .c 3,
  .p pv2 [pv2,pv1244609], .c 7, .c 3, .c 5, .c 13, .c 3, .c 761, .c 41, .c 3,
  .p pv2 [pv2,pv653,pv953], .p pv7 [pv2,pv3,pv31,pv1487], .c 3, .c 1549, .c 5, .c 3, .c 7, .c 53,
  .c 3, .c 5, .c 1249, .c 3, .c 47, .c 7, .c 3, .c 11, .c 31, .c 3, .c 29, .c 5, .c 3, .c 13,
  .c 787, .c 3, .c 5, .p pv3 [pv2,pv3,pv37,pv11213], .c 3, .c 7, .c 17, .c 3, .c 173, .c 709,
  .c 3, .c 191, .c 5, .c 3, .p pv2 [pv2,pv47,pv13241], .c 11, .c 3, .c 5, .c 433, .c 3,
  .p pv3 [pv2,pv5,pv62233], .c 19, .c 3, .c 17, .c 677, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv521,pv2389], .p pv2 [pv2,pv3,pv5,pv7,pv5927], .c 3, .c 5,
]
private theorem h0303c27 : checkBlock 2489091 128 b0303c27 = true := by
  decide +kernel

private def b0303c28 : List Row := [
  .c 7, .c 3, .c 139, .c 179, .c 3, .c 13, .c 23, .c 3, .c 479, .c 5, .c 3, .c 79,
  .p pv17 [pv2,pv3,pv5,pv13,pv491], .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv19,pv6551], .c 13,
  .c 3, .c 59, .c 7, .c 3, .c 31, .c 5, .c 3, .c 11, .c 317, .c 3, .c 5, .c 103, .c 3,
  .p pv7 [pv2,pv5,pv7,pv11,pv53,pv61], .p pv2 [pv2,pv3,pv17,pv12203], .c 3, .c 7, .c 83, .c 3,
  .p pv5 [pv2,pv13,pv95747], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 19, .c 3,
  .p pv3 [pv2,pv5,pv15559], .c 11, .c 3, .c 29, .c 47, .c 3, .p pv2 [pv2,pv7,pv67,pv1327], .c 5,
  .c 3, .c 7, .c 13, .c 3, .c 5, .c 587, .c 3, .c 37, .c 7, .c 3, .p pv3 [pv2,pv11,pv29,pv1951],
  .c 41, .c 3, .p pv2 [pv2,pv1244741], .c 5, .c 3, .c 197, .p pv3 [pv2,pv3,pv5,pv139,pv199], .c 3,
  .c 5, .c 17, .c 3, .c 7, .c 113, .c 3, .c 193, .c 11, .c 3, .c 13, .c 5, .c 3, .c 67,
  .p pv13 [pv2,pv3,pv5,pv11,pv23,pv41], .c 3, .c 5, .c 79, .c 3, .c 11,
  .p pv5 [pv2,pv3,pv19,pv61,pv179], .c 3, .c 151, .c 13, .c 3, .c 7, .c 5, .c 3, .c 101, .c 19,
  .c 3, .c 5, .c 7, .c 3, .c 41, .c 29, .c 3, .p pv5 [pv2,pv23,pv54121], .c 53, .c 3,
  .p pv2 [pv2,pv223,pv2791], .c 5, .c 3, .c 31, .c 127, .c 3, .c 5, .c 397, .c 3, .c 13, .c 61,
  .c 3, .c 11, .c 7, .c 3,
]
private theorem h0303c28 : checkBlock 2489347 128 b0303c28 = true := by
  decide +kernel

private def b0303c29 : List Row := [
  .p pv2 [pv2,pv41,pv97,pv313], .c 5, .c 3, .c 937, .p pv2 [pv2,pv3,pv5,pv31,pv2677], .c 3, .c 5,
  .c 13, .c 3, .c 29, .c 59, .c 3, .c 7, .c 139, .c 3, .c 17, .c 5, .c 3, .p pv11 [pv2,pv1244819],
  .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv19,pv21839], .c 3, .c 379, .c 67, .c 3, .c 43,
  .p pv7 [pv2,pv3,pv23,pv18041], .c 3, .c 11, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv9221], .c 3,
  .c 5, .c 271, .c 3, .c 23, .c 7, .c 3, .p pv5 [pv2,pv71,pv89,pv197], .c 199, .c 3, .c 37, .c 5,
  .c 3, .c 97, .c 17, .c 3, .c 5, .c 11, .c 3, .c 7, .p pv11 [pv2,pv3,pv51869], .c 3,
  .p pv2 [pv2,pv103,pv6043], .p pv3 [pv2,pv3,pv7,pv11,pv17,pv317], .c 3, .c 1559, .c 5, .c 3,
  .c 11, .c 47, .c 3, .c 5, .c 29, .c 3, .c 19, .c 43, .c 3, .c 13, .p pv7 [pv2,pv3,pv207479],
  .c 3, .c 7, .c 5, .c 3, .p pv17 [pv2,pv1244879], .p pv31 [pv2,pv3,pv5,pv7,pv13,pv19], .c 3,
  .c 5, .c 7, .c 3, .c 241, .c 11, .c 3, .p pv3 [pv2,pv61,pv2551], .c 19, .c 3, .c 107, .c 5,
  .c 3, .p pv2 [pv2,pv7,pv12703], .c 1193, .c 3, .c 5, .p pv29 [pv2,pv3,pv23,pv31,pv97], .c 3,
  .p pv3 [pv2,pv5,pv59,pv211], .c 17, .c 3, .c 41, .c 7, .c 3, .p pv2 [pv2,pv13,pv47881], .c 5,
  .c 3, .c 23, .c 263, .c 3, .c 5, .c 31, .c 3, .p pv13 [pv2,pv5,pv7,pv35569], .c 773, .c 3, .c 7,
  .c 11, .c 3, .c 79, .c 5, .c 3, .p pv3 [pv2,pv41,pv7591], .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv1621],
]
private theorem h0303c29 : checkBlock 2489603 128 b0303c29 = true := by
  decide +kernel

private def b0303c30 : List Row := [
  .c 3, .c 11, .c 157, .c 3, .p pv2 [pv2,pv311,pv4003], .p pv2 [pv2,pv3,pv69163], .c 3,
  .p pv3 [pv2,pv7,pv11,pv43,pv47], .c 5, .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv20749], .c 3, .c 5,
  .c 53, .c 3, .p pv17 [pv2,pv5,pv13,pv107,pv179], .c 7, .c 3, .c 719, .c 71, .c 3, .c 13, .c 5,
  .c 3, .p pv2 [pv2,pv622477], .c 23, .c 3, .c 5, .c 83, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv17,pv79,pv103], .c 3, .c 11, .c 13, .c 3, .p pv2 [pv2,pv622483], .c 5, .c 3,
  .c 17, .c 281, .c 3, .c 5, .p pv3 [pv2,pv3,pv414991], .c 3, .c 31, .c 89, .c 3, .c 23, .c 61,
  .c 3, .c 7, .c 5, .c 3, .c 19, .c 11, .c 3, .c 5, .c 7, .c 3, .c 13, .c 1163, .c 3, .c 661,
  .c 37, .c 3, .c 11, .c 5, .c 3, .p pv7 [pv2,pv7,pv29,pv6133], .c 43, .c 3, .c 5, .c 13, .c 3,
  .c 211, .c 31, .c 3, .c 181, .c 7, .c 3, .p pv5 [pv2,pv769,pv1619], .c 5, .c 3,
  .p pv2 [pv2,pv509,pv1223], .c 487, .c 3, .c 5, .c 11, .c 3, .c 17, .c 599, .c 3, .c 7, .c 23,
  .c 3, .c 41, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 191, .c 3, .c 233, .c 257, .c 3, .c 307,
  .p pv7 [pv2,pv3,pv415013], .c 3, .c 19, .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv83003], .c 3,
  .c 5, .c 827, .c 3, .p pv2 [pv2,pv5,pv37,pv673], .c 7, .c 3, .c 47, .c 17, .c 3, .c 331,
]
private theorem h0303c30 : checkBlock 2489859 128 b0303c30 = true := by
  decide +kernel

private def b0303c31 : List Row := [
  .c 5, .c 3, .p pv11 [pv2,pv23,pv54133], .c 19, .c 3, .c 5, .p pv3 [pv2,pv3,pv17,pv24413], .c 3,
  .c 7, .c 269, .c 3, .c 13, .p pv2 [pv2,pv3,pv7,pv19763], .c 3, .c 17, .c 5, .c 3, .c 563,
  .c 163, .c 3, .c 5, .p pv7 [pv2,pv3,pv23057], .c 3, .p pv3 [pv2,pv5,pv17,pv1831], .c 13, .c 3,
  .c 1061, .c 11, .c 3, .c 7, .c 5, .c 3, .c 131, .c 113, .c 3, .c 5, .c 7, .c 3, .c 11, .c 457,
  .c 3, .c 19, .c 31, .c 3, .c 61, .c 5, .c 3, .p pv3 [pv2,pv7,pv11117], .c 17, .c 3, .c 5, .c 41,
  .c 3, .p pv2 [pv2,pv5,pv89,pv1399], .c 541, .c 3, .p pv2 [pv2,pv1245113], .c 7, .c 3, .c 23,
  .c 5, .c 3, .p pv11 [pv2,pv79,pv15761], .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv12577], .c 3,
  .p pv2 [pv2,pv5,pv7,pv1423], .c 241, .c 3, .c 7, .c 29, .c 3, .p pv5 [pv2,pv17,pv73243], .c 5,
  .c 3, .p pv2 [pv2,pv11,pv56597], .c 7, .c 3, .c 5, .c 197, .c 3, .c 97,
  .p pv2 [pv2,pv3,pv138349], .c 3, .c 1447, .c 1213, .c 3, .c 13, .c 5, .c 3, .c 7, .c 11, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv7,pv13,pv4561], .c 3, .c 19, .c 7, .c 3, .c 29, .c 13, .c 3, .c 11,
  .c 5, .c 3, .p pv3 [pv2,pv311291], .c 59, .c 3, .c 5, .p pv7 [pv2,pv3,pv8647], .c 3, .c 7,
  .c 127, .c 3, .c 17, .c 19, .c 3, .c 503, .c 5, .c 3, .c 37, .c 659, .c 3, .c 5, .c 11, .c 3,
]
private theorem h0303c31 : checkBlock 2490115 128 b0303c31 = true := by
  decide +kernel

def rows0303 : List Row :=
  b0303c00 ++ b0303c01 ++ b0303c02 ++ b0303c03 ++ b0303c04 ++ b0303c05 ++ b0303c06 ++ b0303c07 ++
  b0303c08 ++ b0303c09 ++ b0303c10 ++ b0303c11 ++ b0303c12 ++ b0303c13 ++ b0303c14 ++ b0303c15 ++
  b0303c16 ++ b0303c17 ++ b0303c18 ++ b0303c19 ++ b0303c20 ++ b0303c21 ++ b0303c22 ++ b0303c23 ++
  b0303c24 ++ b0303c25 ++ b0303c26 ++ b0303c27 ++ b0303c28 ++ b0303c29 ++ b0303c30 ++ b0303c31

attribute [local irreducible] checkBlock checkRows checkPrime

theorem checked0303 : checkBlock 2482179 4096 rows0303 = true :=
  checkBlock_append h0303c00 (
    checkBlock_append h0303c01 (
    checkBlock_append h0303c02 (
    checkBlock_append h0303c03 (
    checkBlock_append h0303c04 (
    checkBlock_append h0303c05 (
    checkBlock_append h0303c06 (
    checkBlock_append h0303c07 (
    checkBlock_append h0303c08 (
    checkBlock_append h0303c09 (
    checkBlock_append h0303c10 (
    checkBlock_append h0303c11 (
    checkBlock_append h0303c12 (
    checkBlock_append h0303c13 (
    checkBlock_append h0303c14 (
    checkBlock_append h0303c15 (
    checkBlock_append h0303c16 (
    checkBlock_append h0303c17 (
    checkBlock_append h0303c18 (
    checkBlock_append h0303c19 (
    checkBlock_append h0303c20 (
    checkBlock_append h0303c21 (
    checkBlock_append h0303c22 (
    checkBlock_append h0303c23 (
    checkBlock_append h0303c24 (
    checkBlock_append h0303c25 (
    checkBlock_append h0303c26 (
    checkBlock_append h0303c27 (
    checkBlock_append h0303c28 (
    checkBlock_append h0303c29 (
    checkBlock_append h0303c30 (
    h0303c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
