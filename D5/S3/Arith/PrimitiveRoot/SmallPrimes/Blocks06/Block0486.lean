/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks06/Block0486
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks06/Block0486.checked0486
   digest: Kernel proof of checker success on extended consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table043
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table048
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table053
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table061
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table070
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table082
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table099
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table123
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table158
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table161
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table162
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table163
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table165
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table168
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table171
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table175
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table183
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table191
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table203
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table204
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table224
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables03.Table249

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes
private noncomputable def b0486c00 : List Row := [
  .c 3, .c 5, .c 59, .c 3, .p pv2 [pv2,pv5,pv13,pv30577], .c 7, .c 3, .p pv3 [pv2,pv496877],
  .c 257, .c 3, .c 13, .c 5, .c 3, .c 211, .p pv3 [pv2,pv3,pv5,pv29,pv1523], .c 3, .c 5, .c 11,
  .c 3, .c 7, .c 67, .c 3, .c 19, .c 13, .c 3, .c 53, .c 5, .c 3, .c 11, .c 373, .c 3, .c 5,
  .c 23, .c 3, .c 409, .c 41, .c 3, .c 71, .c 103, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv13,pv29,pv659], .p pv3 [pv2,pv3,pv5,pv7,pv23,pv823], .c 3, .c 5, .c 7, .c 3,
  .c 13, .c 11, .c 3, .p pv2 [pv2,pv53,pv37501], .p pv7 [pv2,pv3,pv331259], .c 3, .c 23, .c 5,
  .c 3, .c 47, .c 109, .c 3, .c 5, .c 13, .c 3,
]
private theorem h0486c00 : checkBlock 3975003 64 b0486c00 = true := by decide +kernel
private noncomputable def b0486c01 : List Row := [
  .c 293, .c 353, .c 3, .c 787, .c 7, .c 3, .c 1657, .c 5, .c 3, .c 1777,
  .p pv11 [pv2,pv3,pv5,pv26501], .c 3, .c 5, .c 97, .c 3, .c 17, .p pv2 [pv2,pv3,pv662527], .c 3,
  .c 7, .c 11, .c 3, .p pv2 [pv2,pv993793], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 61, .c 3,
  .c 11, .p pv5 [pv2,pv3,pv13,pv31,pv137], .c 3, .p pv2 [pv2,pv41,pv24239], .c 19, .c 3, .c 461,
  .c 5, .c 3, .c 7, .c 229, .c 3, .c 5, .p pv17 [pv2,pv3,pv7,pv11831], .c 3, .c 43, .c 7, .c 3,
  .c 113, .c 17, .c 3, .c 29, .c 5, .c 3, .p pv7 [pv2,pv1987619], .c 1093, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv17,pv1181], .c 3, .c 7, .p pv2 [pv2,pv3,pv337,pv983], .c 3, .c 11,
]
private theorem h0486c01 : checkBlock 3975131 64 b0486c01 = true := by decide +kernel
private noncomputable def b0486c02 : List Row := [
  .c 101, .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv11,pv167,pv541],
  .p pv11 [pv2,pv3,pv5,pv13,pv10193], .c 3, .c 5, .p pv2 [pv2,pv3,pv257,pv1289], .c 3,
  .p pv11 [pv2,pv5,pv17,pv37,pv79], .c 13, .c 3, .c 239, .p pv7 [pv2,pv3,pv73,pv2269], .c 3,
  .c 7, .c 5, .c 3, .c 271, .c 11, .c 3, .c 5, .c 7, .c 3, .c 67, .c 19, .c 3, .c 37, .c 41,
  .c 3, .c 11, .c 5, .c 3, .c 137, .c 17, .c 3, .c 5, .c 967, .c 3,
  .p pv7 [pv2,pv5,pv113,pv1759], .c 23, .c 3, .c 31, .c 7, .c 3, .p pv3 [pv2,pv496919], .c 5,
  .c 3, .c 79, .c 13, .c 3, .c 5, .c 11, .c 3, .c 53, .c 433, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv11,pv29,pv31,pv67], .c 3, .p pv5 [pv2,pv17,pv116923], .c 5,
]
private theorem h0486c02 : checkBlock 3975259 64 b0486c02 = true := by decide +kernel
private noncomputable def b0486c03 : List Row := [
  .c 3, .c 11, .c 7, .c 3, .c 5, .c 157, .c 3, .c 41, .c 1117, .c 3, .c 29, .c 31, .c 3, .c 13,
  .c 5, .c 3, .c 7, .c 223, .c 3, .c 5, .c 19, .c 3, .c 61, .c 7, .c 3,
  .p pv2 [pv2,pv29,pv43,pv797], .c 13, .c 3, .c 457, .c 5, .c 3, .p pv3 [pv2,pv47,pv97,pv109],
  .c 83, .c 3, .c 5, .c 131, .c 3, .c 7, .p pv3 [pv2,pv3,pv220859], .c 3, .c 17, .c 149, .c 3,
  .p pv3 [pv2,pv419,pv593], .c 5, .c 3, .c 43, .c 23, .c 3, .c 5, .p pv3 [pv2,pv3,pv353,pv1877],
  .c 3, .c 13, .p pv2 [pv2,pv3,pv61,pv5431], .c 3, .c 317, .c 11, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv263,pv3779], .p pv3 [pv2,pv3,pv5,pv7,pv11,pv1721], .c 3,
]
private theorem h0486c03 : checkBlock 3975387 64 b0486c03 = true := by decide +kernel
private noncomputable def b0486c04 : List Row := [
  .c 5, .c 7, .c 3, .c 11, .c 29, .c 3, .c 23, .p pv7 [pv2,pv3,pv151,pv1097], .c 3, .c 31, .c 5,
  .c 3, .c 37, .c 19, .c 3, .c 5, .p pv2 [pv2,pv3,pv662591], .c 3, .c 269, .c 61, .c 3, .c 109,
  .c 7, .c 3, .c 599, .c 5, .c 3, .c 13, .c 467, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv37], .c 3,
  .c 29, .c 53, .c 3, .c 7, .c 47, .c 3, .p pv3 [pv2,pv496949], .c 5, .c 3,
  .p pv11 [pv2,pv11,pv19,pv9511], .c 7, .c 3, .c 5, .c 193, .c 3, .c 1069, .c 37, .c 3, .c 19,
  .c 23, .c 3, .c 857, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 17, .c 3, .c 331,
]
private theorem h0486c04 : checkBlock 3975515 64 b0486c04 = true := by decide +kernel
private noncomputable def b0486c05 : List Row := [
  .c 7, .c 3, .c 13, .p pv7 [pv2,pv3,pv41413], .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv1987829],
  .p pv2 [pv2,pv3,pv5,pv13,pv1699], .c 3, .c 5, .p pv2 [pv2,pv3,pv109,pv6079], .c 3, .c 7, .c 13,
  .c 3, .p pv2 [pv2,pv993919], .c 113, .c 3, .c 47, .c 5, .c 3, .c 53, .c 937, .c 3, .c 5, .c 11,
  .c 3, .p pv2 [pv2,pv5,pv83,pv479], .p pv5 [pv2,pv3,pv662617], .c 3, .p pv2 [pv2,pv7,pv283979],
  .p pv2 [pv2,pv3,pv11,pv30119], .c 3, .c 7, .c 5, .c 3, .c 11, .p pv11 [pv2,pv3,pv5,pv7,pv4733],
  .c 3, .c 5, .c 7, .c 3, .c 19, .c 163, .c 3, .c 43, .c 17, .c 3, .c 683, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv141991], .c 13, .c 3, .c 5, .c 23, .c 3, .c 37, .c 11, .c 3, .c 149, .c 7,
]
private theorem h0486c05 : checkBlock 3975643 64 b0486c05 = true := by decide +kernel
private noncomputable def b0486c06 : List Row := [
  .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv1987889], .c 31, .c 3, .c 5, .c 71, .c 3,
  .p pv7 [pv2,pv5,pv7,pv13,pv17,pv257], .c 743, .c 3, .c 7, .c 73, .c 3, .c 13, .c 5, .c 3,
  .c 541, .c 7, .c 3, .c 5, .c 139, .c 3, .c 199, .c 43, .c 3, .p pv2 [pv2,pv19,pv23,pv4549],
  .c 11, .c 3, .c 59, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 67, .c 3, .c 11, .c 7, .c 3,
  .p pv3 [pv2,pv191,pv1301], .c 1493, .c 3, .p pv5 [pv2,pv11,pv127,pv1423], .c 5, .c 3, .c 281,
  .c 29, .c 3, .c 5, .c 137, .c 3, .c 7, .c 19, .c 3, .p pv5 [pv2,pv173,pv11491], .c 409, .c 3,
  .c 41, .c 5, .c 3,
]
private theorem h0486c06 : checkBlock 3975771 64 b0486c06 = true := by decide +kernel
private noncomputable def b0486c07 : List Row := [
  .c 1381, .c 53, .c 3, .c 5, .c 13, .c 3, .p pv7 [pv2,pv5,pv397591], .c 823, .c 3, .c 11, .c 61,
  .c 3, .c 7, .c 5, .c 3, .c 29, .c 631, .c 3, .c 5, .c 7, .c 3, .c 23, .c 17, .c 3,
  .p pv2 [pv2,pv13,pv37,pv4133], .c 83, .c 3, .c 881, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5,
  .c 31, .c 3, .p pv2 [pv2,pv5,pv397597], .c 1223, .c 3, .c 17, .c 7, .c 3, .c 11, .c 5, .c 3,
  .c 127, .c 79, .c 3, .c 5, .c 19, .c 3, .p pv3 [pv2,pv5,pv7,pv71], .p pv2 [pv2,pv3,pv220889],
  .c 3, .c 7, .p pv19 [pv2,pv3,pv165667], .c 3, .c 107, .c 5, .c 3,
  .p pv2 [pv2,pv73,pv113,pv241], .c 7, .c 3, .c 5,
]
private theorem h0486c07 : checkBlock 3975899 64 b0486c07 = true := by decide +kernel
private noncomputable def b0486c08 : List Row := [
  .c 11, .c 3, .p pv11 [pv2,pv5,pv97,pv4099], .c 23, .c 3, .c 13, .c 313, .c 3,
  .p pv2 [pv2,pv7,pv284003], .c 5, .c 3, .c 7, .c 197, .c 3, .c 5, .c 37, .c 3,
  .p pv2 [pv2,pv5,pv11,pv31,pv53], .c 7, .c 3, .c 101, .c 59, .c 3, .c 19, .c 5, .c 3, .c 17,
  .c 43, .c 3, .c 5, .p pv5 [pv2,pv3,pv662681], .c 3, .c 7, .c 11, .c 3,
  .p pv3 [pv2,pv17,pv7309], .p pv2 [pv2,pv3,pv7,pv41,pv2309], .c 3, .c 29, .c 5, .c 3, .c 103,
  .c 19, .c 3, .c 5, .c 653, .c 3, .p pv3 [pv2,pv5,pv107,pv929], .c 641, .c 3, .c 97,
  .p pv19 [pv2,pv3,pv13,pv59], .c 3, .c 7, .c 5, .c 3, .c 41, .c 13, .c 3, .c 5, .c 7, .c 3,
  .c 137, .c 31,
]
private theorem h0486c08 : checkBlock 3976027 64 b0486c08 = true := by decide +kernel
private noncomputable def b0486c09 : List Row := [
  .c 3, .c 349, .c 11, .c 3, .c 61, .c 5, .c 3, .p pv3 [pv2,pv7,pv19,pv37,pv101], .c 23, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv82837], .c 3, .c 11, .p pv5 [pv2,pv3,pv7,pv67,pv157], .c 3, .c 19,
  .c 7, .c 3, .c 13, .c 5, .c 3, .p pv13 [pv2,pv17,pv83,pv1409], .c 1571, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv13,pv19,pv2683], .c 3, .c 109, .c 71, .c 3, .c 7, .c 13, .c 3,
  .p pv5 [pv2,pv163,pv12197], .c 5, .c 3, .p pv2 [pv2,pv79,pv12583], .c 7, .c 3, .c 5, .c 73,
  .c 3, .p pv3 [pv2,pv5,pv23,pv2161], .c 127, .c 3, .c 11, .c 17, .c 3, .c 43, .c 5, .c 3, .c 7,
  .p pv31 [pv2,pv3,pv5,pv66271], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv17,pv5569], .c 3, .c 13, .c 7,
  .c 3, .c 29, .c 37, .c 3,
]
private theorem h0486c09 : checkBlock 3976155 64 b0486c09 = true := by decide +kernel
private noncomputable def b0486c10 : List Row := [
  .c 17, .c 5, .c 3, .p pv3 [pv2,pv137,pv907], .c 11, .c 3, .c 5, .c 13, .c 3, .c 7, .c 41, .c 3,
  .c 79, .c 23, .c 3, .c 11, .c 5, .c 3, .p pv7 [pv2,pv877,pv2267], .c 97, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv220907], .c 3, .p pv2 [pv2,pv5,pv397633], .c 811, .c 3,
  .p pv3 [pv2,pv7,pv13,pv2731], .c 19, .c 3, .c 7, .c 5, .c 3, .c 13, .c 17, .c 3, .c 5, .c 7,
  .c 3, .p pv17 [pv2,pv5,pv99409], .c 149, .c 3, .p pv5 [pv2,pv1988183], .c 523, .c 3, .c 139,
  .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv22091], .c 3, .c 5, .p pv7 [pv2,pv3,pv79,pv8389],
  .c 3, .p pv29 [pv2,pv5,pv11,pv37,pv977], .c 29, .c 3, .p pv2 [pv2,pv19,pv52321], .c 7, .c 3,
  .p pv2 [pv2,pv17,pv116953], .c 5, .c 3, .p pv3 [pv2,pv497051],
]
private theorem h0486c10 : checkBlock 3976283 64 b0486c10 = true := by decide +kernel
private noncomputable def b0486c11 : List Row := [
  .c 1279, .c 3, .c 5, .p pv5 [pv2,pv3,pv13807], .c 3, .c 887, .c 11, .c 3, .c 7, .c 109, .c 3,
  .c 283, .c 5, .c 3, .p pv11 [pv2,pv1988219], .c 7, .c 3, .c 5, .c 23, .c 3, .c 29, .c 13, .c 3,
  .c 607, .p pv2 [pv2,pv3,pv662743], .c 3, .c 31, .c 5, .c 3, .c 7, .c 101, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv47339], .c 3, .p pv7 [pv2,pv5,pv29,pv857], .c 7, .c 3, .c 17, .c 11,
  .c 3, .c 23, .c 5, .c 3, .c 769, .c 37, .c 3, .c 5, .p pv5 [pv2,pv3,pv211,pv349], .c 3, .c 7,
  .c 919, .c 3, .c 67, .p pv23 [pv2,pv3,pv7,pv13,pv7283], .c 3, .p pv2 [pv2,pv11,pv180751], .c 5,
  .c 3, .c 19, .c 13, .c 3, .c 5, .c 53,
]
private theorem h0486c11 : checkBlock 3976411 64 b0486c11 = true := by decide +kernel
private noncomputable def b0486c12 : List Row := [
  .c 3, .c 59, .c 1123, .c 3, .p pv2 [pv2,pv7,pv40577], .c 41, .c 3, .c 7, .c 5, .c 3, .c 739,
  .c 257, .c 3, .c 5, .c 7, .c 3, .c 307, .p pv5 [pv2,pv3,pv17,pv101,pv193], .c 3, .c 11,
  .p pv3 [pv2,pv3,pv173,pv1277], .c 3, .c 13, .c 5, .c 3, .c 17, .c 1847, .c 3, .c 5, .c 43,
  .c 3, .p pv3 [pv2,pv5,pv59,pv337], .c 1367, .c 3, .p pv5 [pv2,pv17,pv116959], .c 7, .c 3,
  .c 83, .c 5, .c 3, .p pv2 [pv2,pv31,pv2069], .c 11, .c 3, .c 5, .c 269, .c 3, .c 23,
  .p pv5 [pv2,pv3,pv11,pv5021], .c 3, .c 7, .c 71, .c 3, .c 11, .c 5, .c 3, .c 31, .c 7, .c 3,
  .c 5, .c 17, .c 3, .c 13, .p pv13 [pv2,pv3,pv19,pv34883], .c 3,
]
private theorem h0486c12 : checkBlock 3976539 64 b0486c12 = true := by decide +kernel
private noncomputable def b0486c13 : List Row := [
  .p pv2 [pv2,pv941,pv2113], .p pv13 [pv2,pv3,pv36821], .c 3, .c 101, .c 5, .c 3, .c 7, .c 19,
  .c 3, .c 5, .c 11, .c 3, .c 17, .c 7, .c 3, .c 1153, .c 137, .c 3, .p pv5 [pv2,pv79,pv25169],
  .c 5, .c 3, .c 11, .c 31, .c 3, .c 5, .c 47, .c 3, .c 7, .c 23, .c 3, .c 103, .c 419, .c 3,
  .p pv2 [pv2,pv994183], .c 5, .c 3, .c 13, .c 29, .c 3, .c 5, .c 389, .c 3, .c 127, .c 11, .c 3,
  .c 19, .c 17, .c 3, .c 7, .c 5, .c 3, .c 23, .c 167, .c 3, .c 5, .c 7, .c 3, .c 71,
  .p pv5 [pv2,pv3,pv662797], .c 3, .c 89, .c 719, .c 3, .c 17,
]
private theorem h0486c13 : checkBlock 3976667 64 b0486c13 = true := by decide +kernel
private noncomputable def b0486c14 : List Row := [
  .c 5, .c 3, .c 29, .p pv7 [pv2,pv3,pv5,pv1657], .c 3, .c 5, .p pv3 [pv2,pv3,pv97,pv6833], .c 3,
  .c 47, .c 227, .c 3, .c 13, .c 7, .c 3, .c 263, .c 5, .c 3, .p pv2 [pv2,pv29,pv34283],
  .p pv3 [pv2,pv3,pv5,pv11,pv13,pv103], .c 3, .c 5, .c 431, .c 3, .c 11, .c 13, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv27617], .c 3, .p pv2 [pv2,pv11,pv19,pv67,pv71], .c 5, .c 3,
  .p pv2 [pv2,pv47,pv42307], .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv31,pv7127], .c 3, .c 19,
  .p pv5 [pv2,pv3,pv165703], .c 3, .c 41, .p pv3 [pv2,pv3,pv17,pv127,pv307], .c 3, .c 991, .c 5,
  .c 3, .c 7, .c 541, .c 3, .c 5, .c 31, .c 3, .c 439, .c 7, .c 3, .c 11, .c 19, .c 3,
  .p pv3 [pv2,pv17,pv14621], .c 5, .c 3, .c 67, .c 13,
]
private theorem h0486c14 : checkBlock 3976795 64 b0486c14 = true := by decide +kernel
private noncomputable def b0486c15 : List Row := [
  .c 3, .c 5, .p pv3 [pv2,pv3,pv373,pv1777], .c 3, .c 7, .c 103, .c 3, .c 337, .c 79, .c 3,
  .p pv5 [pv2,pv1988471], .c 5, .c 3, .p pv2 [pv2,pv994237], .c 11, .c 3, .c 5, .c 1861, .c 3,
  .c 53, .c 17, .c 3, .c 73, .p pv7 [pv2,pv3,pv165707], .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv313,pv6353], .p pv13 [pv2,pv3,pv5,pv7,pv17,pv557], .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv31,pv12829], .c 281, .c 3, .c 17, .c 13, .c 3, .p pv2 [pv2,pv29,pv191,pv359],
  .c 5, .c 3, .c 1559, .p pv2 [pv2,pv3,pv5,pv44189], .c 3, .c 5, .c 11, .c 3, .c 31, .c 19, .c 3,
  .c 43, .c 7, .c 3, .c 997, .c 5, .c 3, .c 11, .c 41, .c 3, .c 5, .c 461, .c 3,
]
private theorem h0486c15 : checkBlock 3976923 64 b0486c15 = true := by decide +kernel
private noncomputable def b0486c16 : List Row := [
  .c 13, .c 67, .c 3, .c 7, .p pv2 [pv2,pv3,pv662843], .c 3, .p pv5 [pv2,pv1988531], .c 5, .c 3,
  .p pv2 [pv2,pv23,pv139,pv311], .c 7, .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv19,pv5233],
  .c 11, .c 3, .p pv5 [pv2,pv263,pv7561], .c 29, .c 3, .c 37, .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv491], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv94693], .c 3, .c 83, .c 7, .c 3,
  .p pv2 [pv2,pv11,pv13,pv17,pv409], .c 1489, .c 3, .c 41, .c 5, .c 3, .c 13, .c 59, .c 3, .c 5,
  .c 19, .c 3, .c 7, .c 89, .c 3, .c 29, .c 11, .c 3, .p pv3 [pv2,pv62143], .c 5, .c 3,
  .p pv7 [pv2,pv1988579], .p pv17 [pv2,pv3,pv5,pv11,pv23,pv131], .c 3, .c 5, .c 17, .c 3, .c 11,
  .c 53, .c 3, .p pv3 [pv2,pv7,pv29,pv31,pv79],
]
private theorem h0486c16 : checkBlock 3977051 64 b0486c16 = true := by decide +kernel
private noncomputable def b0486c17 : List Row := [
  .c 367, .c 3, .c 7, .c 5, .c 3, .c 151, .c 1451, .c 3, .c 5, .c 7, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv662867], .c 3, .c 13, .p pv7 [pv2,pv3,pv18413], .c 3, .c 19, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv17,pv983], .c 503, .c 3, .c 5, .c 1669, .c 3, .c 1721, .c 13, .c 3, .c 11,
  .c 7, .c 3, .p pv2 [pv2,pv43,pv103,pv449], .c 5, .c 3, .c 59, .c 19, .c 3, .c 5, .c 149, .c 3,
  .c 61, .c 29, .c 3, .c 7, .c 17, .c 3, .p pv3 [pv2,pv13,pv167,pv229], .c 5, .c 3, .c 53, .c 7,
  .c 3, .c 5, .c 41, .c 3, .c 97, .p pv7 [pv2,pv3,pv11,pv29,pv1039], .c 3, .c 107, .c 373, .c 3,
  .c 11, .c 5,
]
private theorem h0486c17 : checkBlock 3977179 64 b0486c17 = true := by decide +kernel
private noncomputable def b0486c18 : List Row := [
  .c 3, .c 7, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv5261], .c 3, .c 23, .c 7, .c 3, .c 19,
  .c 487, .c 3, .c 1087, .c 5, .c 3, .p pv2 [pv2,pv1988669], .p pv19 [pv2,pv3,pv5,pv151,pv439],
  .c 3, .c 5, .c 11, .c 3, .c 7, .p pv5 [pv2,pv3,pv37,pv1493], .c 3, .c 1399, .c 1699, .c 3,
  .c 13, .c 5, .c 3, .c 11, .c 17, .c 3, .c 5, .p pv11 [pv2,pv3,pv13,pv3187], .c 3,
  .p pv2 [pv2,pv5,pv11,pv101,pv179], .c 61, .c 3, .p pv2 [pv2,pv7,pv127,pv2237], .c 13, .c 3,
  .c 7, .c 5, .c 3, .c 317, .p pv59 [pv2,pv3,pv5,pv7,pv947], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv41,pv89,pv109], .c 11, .c 3, .c 727, .p pv2 [pv2,pv3,pv601,pv1103], .c 3,
  .c 653, .c 5, .c 3, .p pv2 [pv2,pv7,pv13,pv223], .p pv3 [pv2,pv3,pv5,pv197,pv673], .c 3,
]
private theorem h0486c18 : checkBlock 3977307 64 b0486c18 = true := by decide +kernel
private noncomputable def b0486c19 : List Row := [
  .c 5, .c 29, .c 3, .c 13, .c 83, .c 3, .p pv5 [pv2,pv11,pv180793], .c 7, .c 3,
  .p pv2 [pv2,pv994363], .c 5, .c 3, .c 23, .p pv2 [pv2,pv3,pv5,pv19,pv1163], .c 3, .c 5, .c 13,
  .c 3, .p pv7 [pv2,pv5,pv7,pv56821], .c 17, .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv23,pv86467],
  .c 5, .c 3, .p pv3 [pv2,pv248593], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv55243], .c 3, .c 11,
  .p pv3 [pv2,pv3,pv662917], .c 3, .c 17, .p pv29 [pv2,pv3,pv461,pv719], .c 3, .c 127, .c 5,
  .c 3, .c 7, .c 137, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv83,pv163], .c 3, .c 1321, .c 7, .c 3,
  .c 37, .c 853, .c 3, .c 43, .c 5, .c 3, .p pv2 [pv2,pv31,pv32077], .c 23, .c 3, .c 5, .c 1753,
  .c 3, .c 7,
]
private theorem h0486c19 : checkBlock 3977435 64 b0486c19 = true := by decide +kernel
private noncomputable def b0486c20 : List Row := [
  .c 47, .c 3, .c 11, .p pv11 [pv2,pv3,pv7,pv1973], .c 3, .p pv2 [pv2,pv994393], .c 5, .c 3,
  .c 31, .c 1373, .c 3, .c 5, .p pv2 [pv2,pv3,pv43,pv571], .c 3, .c 491, .c 19, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv643,pv1031], .c 3, .c 7, .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv23,pv8647], .c 13, .c 3, .c 61, .c 43, .c 3, .c 11, .c 5, .c 3,
  .p pv41 [pv2,pv7,pv284117], .c 31, .c 3, .c 5, .p pv3 [pv2,pv3,pv662941], .c 3, .c 223,
  .p pv2 [pv2,pv3,pv7,pv47353], .c 3, .c 47, .c 7, .c 3, .p pv5 [pv2,pv13,pv59,pv2593], .c 5,
  .c 3, .c 19, .c 607, .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv7,pv7103], .c 101, .c 3, .c 7,
  .c 23,
]
private theorem h0486c20 : checkBlock 3977563 64 b0486c20 = true := by decide +kernel
private noncomputable def b0486c21 : List Row := [
  .c 3, .p pv2 [pv2,pv83,pv11981], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 19, .c 3, .c 17,
  .c 113, .c 3, .p pv2 [pv2,pv317,pv3137], .p pv11 [pv2,pv3,pv662953], .c 3, .c 67, .c 5, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv5,pv193,pv229], .c 3, .c 5, .c 109, .c 3,
  .p pv3 [pv2,pv5,pv13,pv15299], .c 7, .c 3, .c 761, .c 61, .c 3, .c 13, .c 5, .c 3, .c 37,
  .p pv11 [pv2,pv3,pv5,pv8287], .c 3, .c 5, .c 127, .c 3, .c 7, .c 167, .c 3,
  .p pv3 [pv2,pv11,pv97,pv233], .c 13, .c 3, .c 19, .c 5, .c 3, .c 173,
  .p pv11 [pv2,pv3,pv5,pv67,pv1979], .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv31,pv37], .c 3, .c 43,
  .c 1447, .c 3, .p pv5 [pv2,pv7,pv284129], .c 11, .c 3, .c 7, .c 5, .c 3,
]
private theorem h0486c21 : checkBlock 3977691 64 b0486c21 = true := by decide +kernel
private noncomputable def b0486c22 : List Row := [
  .p pv2 [pv2,pv13,pv152993], .c 19, .c 3, .c 5, .c 7, .c 3, .c 11, .c 37, .c 3, .c 181, .c 59,
  .c 3, .c 29, .c 5, .c 3, .p pv11 [pv2,pv7,pv251,pv283], .p pv37 [pv2,pv3,pv5,pv23,pv1153],
  .c 3, .c 5, .c 13, .c 3, .c 41, .p pv3 [pv2,pv3,pv7,pv53,pv1787], .c 3, .p pv2 [pv2,pv1988933],
  .c 7, .c 3, .c 23, .c 5, .c 3, .c 569, .c 17, .c 3, .c 5, .c 43, .c 3,
  .p pv7 [pv2,pv5,pv7,pv56827], .p pv5 [pv2,pv3,pv47,pv2351], .c 3, .c 7, .c 1297, .c 3,
  .p pv5 [pv2,pv41,pv139,pv349], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 71, .c 3,
  .p pv7 [pv2,pv5,pv31,pv401], .c 193, .c 3, .p pv5 [pv2,pv1988963], .p pv11 [pv2,pv3,pv55249],
  .c 3, .p pv2 [pv2,pv7,pv17,pv61,pv137], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
]
private theorem h0486c22 : checkBlock 3977819 64 b0486c22 = true := by decide +kernel
private noncomputable def b0486c23 : List Row := [
  .p pv2 [pv2,pv3,pv7,pv131,pv241], .c 3, .c 31, .c 7, .c 3, .c 59, .c 29, .c 3, .c 11, .c 5,
  .c 3, .c 461, .c 433, .c 3, .c 5, .p pv7 [pv2,pv3,pv165749], .c 3, .c 7, .c 17, .c 3, .c 13,
  .c 73, .c 3, .c 61, .c 5, .c 3, .p pv7 [pv2,pv1988999], .c 311, .c 3, .c 5, .c 11, .c 3, .c 19,
  .c 13, .c 3, .c 17, .c 601, .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv13 [pv2,pv3,pv5,pv7,pv19,pv997], .c 3, .c 5, .c 7, .c 3, .c 139,
  .p pv2 [pv2,pv3,pv663007], .c 3, .c 751, .c 19, .c 3, .p pv3 [pv2,pv13,pv113,pv677], .c 5,
  .c 3, .c 43, .c 293, .c 3, .c 5, .c 97, .c 3, .p pv11 [pv2,pv5,pv397807], .c 11,
]
private theorem h0486c23 : checkBlock 3977947 64 b0486c23 = true := by decide +kernel
private noncomputable def b0486c24 : List Row := [
  .c 3, .c 131, .c 7, .c 3, .c 1033, .c 5, .c 3, .c 1951, .c 13, .c 3, .c 5, .c 223, .c 3,
  .p pv2 [pv2,pv5,pv7,pv5683], .c 23, .c 3, .c 7, .p pv2 [pv2,pv3,pv110503], .c 3,
  .p pv3 [pv2,pv31079], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 47, .c 3, .c 283, .c 29, .c 3,
  .c 31, .c 11, .c 3, .c 13, .c 5, .c 3, .c 7, .c 149, .c 3, .c 5, .c 571, .c 3, .c 11, .c 7,
  .c 3, .p pv5 [pv2,pv37,pv53759], .c 13, .c 3, .c 109, .c 5, .c 3, .p pv2 [pv2,pv163,pv12203],
  .p pv17 [pv2,pv3,pv5,pv53,pv139], .c 3, .c 5, .c 17, .c 3, .c 7, .c 59, .c 3,
  .p pv2 [pv2,pv994549], .c 31, .c 3,
]
private theorem h0486c24 : checkBlock 3978075 64 b0486c24 = true := by decide +kernel
private noncomputable def b0486c25 : List Row := [
  .c 37, .c 5, .c 3, .c 199, .c 89, .c 3, .c 5, .p pv7 [pv2,pv3,pv11,pv5023], .c 3, .c 13,
  .c 157, .c 3, .c 11, .p pv2 [pv2,pv3,pv331519], .c 3, .c 7, .c 5, .c 3, .c 19, .c 23, .c 3,
  .c 5, .c 7, .c 3, .c 349, .p pv5 [pv2,pv3,pv59,pv1873], .c 3, .p pv3 [pv2,pv248641], .c 67,
  .c 3, .p pv5 [pv2,pv1989131], .c 5, .c 3, .p pv2 [pv2,pv7,pv47,pv3023], .c 11, .c 3, .c 5,
  .c 19, .c 3, .c 73, .p pv2 [pv2,pv3,pv7,pv11,pv79,pv109], .c 3, .c 23, .c 7, .c 3, .c 11, .c 5,
  .c 3, .c 13, .p pv7 [pv2,pv3,pv5,pv89,pv149], .c 3, .c 5, .c 29, .c 3, .c 59, .c 619, .c 3,
  .c 7, .c 139, .c 3, .c 17, .c 5, .c 3, .p pv3 [pv2,pv497291],
]
private theorem h0486c25 : checkBlock 3978203 64 b0486c25 = true := by decide +kernel
private noncomputable def b0486c26 : List Row := [
  .c 7, .c 3, .c 5, .c 11, .c 3, .c 163, .c 71, .c 3, .c 947, .p pv2 [pv2,pv3,pv11,pv30139],
  .c 3, .c 19, .c 5, .c 3, .c 7, .c 79, .c 3, .c 5, .c 107, .c 3, .c 829, .c 7, .c 3, .c 13,
  .c 23, .c 3, .c 659, .c 5, .c 3, .c 89, .c 17, .c 3, .c 5, .c 151, .c 3, .c 7, .c 11, .c 3,
  .c 1723, .c 47, .c 3, .c 307, .c 5, .c 3, .c 1223, .p pv13 [pv2,pv3,pv5,pv61,pv1087], .c 3,
  .c 5, .c 73, .c 3, .p pv23 [pv2,pv5,pv461,pv863], .p pv5 [pv2,pv3,pv6907], .c 3, .c 593, .c 83,
  .c 3, .c 7, .c 5, .c 3, .c 149, .p pv3 [pv2,pv3,pv5,pv7,pv421], .c 3, .c 5, .c 7,
]
private theorem h0486c26 : checkBlock 3978331 64 b0486c26 = true := by decide +kernel
private noncomputable def b0486c27 : List Row := [
  .c 3, .c 523, .c 1511, .c 3, .c 19, .c 11, .c 3, .p pv3 [pv2,pv497309], .c 5, .c 3,
  .p pv7 [pv2,pv7,pv31,pv89,pv103], .c 13, .c 3, .c 5, .c 1009, .c 3, .c 11, .c 17, .c 3,
  .p pv3 [pv2,pv15541], .c 7, .c 3, .c 47, .c 5, .c 3, .c 31,
  .p pv3 [pv2,pv3,pv5,pv17,pv29,pv269], .c 3, .c 5, .c 23, .c 3, .c 1103,
  .p pv2 [pv2,pv3,pv83,pv2663], .c 3, .c 7, .c 127, .c 3, .c 13, .c 5, .c 3, .c 29, .c 7, .c 3,
  .c 5, .c 59, .c 3, .c 53, .p pv5 [pv2,pv3,pv97,pv1709], .c 3, .c 11, .c 13, .c 3, .c 23, .c 5,
  .c 3, .c 7, .c 31, .c 3, .c 5, .c 1867, .c 3, .c 19, .c 7, .c 3,
]
private theorem h0486c27 : checkBlock 3978459 64 b0486c27 = true := by decide +kernel
private noncomputable def b0486c28 : List Row := [
  .p pv2 [pv2,pv23,pv86491], .c 449, .c 3, .p pv3 [pv2,pv101,pv1231], .c 5, .c 3, .c 41, .c 11,
  .c 3, .c 5, .c 199, .c 3, .c 7, .c 1567, .c 3, .c 113, .c 19, .c 3, .c 11, .c 5, .c 3, .c 17,
  .c 773, .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv41,pv1213], .p pv3 [pv2,pv3,pv457,pv1451],
  .c 3, .c 37, .c 97, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv1989329], .c 43, .c 3, .c 5, .c 7,
  .c 3, .p pv11 [pv2,pv5,pv397867], .p pv5 [pv2,pv3,pv82889], .c 3, .c 79, .c 281, .c 3,
  .p pv2 [pv2,pv1989341], .c 5, .c 3, .c 11, .c 47, .c 3, .c 5, .c 17, .c 3, .c 23, .c 1777,
  .c 3, .p pv2 [pv2,pv1989353], .c 7, .c 3, .c 29,
]
private theorem h0486c28 : checkBlock 3978587 64 b0486c28 = true := by decide +kernel
private noncomputable def b0486c29 : List Row := [
  .c 5, .c 3, .c 73, .c 37, .c 3, .c 5, .p pv3 [pv2,pv3,pv31,pv21391], .c 3, .c 17, .c 11, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv47,pv4703], .c 3, .p pv5 [pv2,pv29,pv181,pv379], .c 5, .c 3,
  .p pv2 [pv2,pv17,pv58511], .c 7, .c 3, .c 5, .c 31, .c 3, .p pv7 [pv2,pv5,pv99469], .c 41,
  .c 3, .c 13, .c 71, .c 3, .p pv3 [pv2,pv7,pv142099], .c 5, .c 3, .c 7,
  .p pv31 [pv2,pv3,pv5,pv13,pv5101], .c 3, .c 5, .c 103, .c 3, .c 373, .c 7, .c 3, .c 359, .c 11,
  .c 3, .p pv2 [pv2,pv1989401], .c 5, .c 3, .c 19, .p pv3 [pv2,pv3,pv5,pv11,pv4019], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv17,pv23,pv53], .c 3, .c 7, .p pv3 [pv2,pv3,pv271,pv2447], .c 3, .c 109,
  .c 29, .c 3, .c 17, .c 5, .c 3, .c 23, .p pv59 [pv2,pv3,pv5,pv71,pv467],
]
private theorem h0486c29 : checkBlock 3978715 64 b0486c29 = true := by decide +kernel
private noncomputable def b0486c30 : List Row := [
  .c 3, .c 5, .c 19, .c 3, .c 157, .c 509, .c 3, .c 1049, .p pv3 [pv2,pv3,pv13,pv29,pv1759],
  .c 3, .c 7, .c 5, .c 3, .c 37, .c 13, .c 3, .c 5, .c 7, .c 3, .c 31, .p pv5 [pv2,pv3,pv2729],
  .c 3, .c 11, .c 1483, .c 3, .p pv2 [pv2,pv994723], .c 5, .c 3, .p pv7 [pv2,pv7,pv11,pv3691],
  .c 17, .c 3, .c 5, .c 929, .c 3, .c 71, .c 1201, .c 3, .p pv2 [pv2,pv29,pv34301], .c 7, .c 3,
  .c 13, .c 5, .c 3, .c 67, .c 11, .c 3, .c 5, .c 83, .c 3, .c 233, .c 31, .c 3, .c 7, .c 13,
  .c 3, .c 11, .c 5, .c 3, .c 337, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv663161], .c 3,
]
private theorem h0486c30 : checkBlock 3978843 64 b0486c30 = true := by decide +kernel
private noncomputable def b0486c31 : List Row := [
  .p pv2 [pv2,pv5,pv397897], .c 47, .c 3, .c 23, .p pv2 [pv2,pv3,pv663163], .c 3, .c 613, .c 5,
  .c 3, .c 7, .c 179, .c 3, .c 5, .c 11, .c 3, .c 13, .c 7, .c 3, .c 1151, .c 41, .c 3,
  .p pv2 [pv2,pv89,pv11177], .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv17,pv47,pv83], .c 3, .c 5,
  .c 13, .c 3, .c 7, .c 617, .c 3, .c 17, .p pv3 [pv2,pv3,pv7,pv211,pv449], .c 3,
  .p pv2 [pv2,pv659,pv3019], .c 5, .c 3, .c 347, .c 857, .c 3, .c 5, .c 1609, .c 3, .c 29, .c 11,
  .c 3, .c 31, .c 23, .c 3, .c 7, .c 5, .c 3, .c 13, .c 53, .c 3, .c 5, .c 7, .c 3, .c 37,
  .c 271, .c 3, .c 101,
]
private theorem h0486c31 : checkBlock 3978971 64 b0486c31 = true := by decide +kernel
private noncomputable def b0486c32 : List Row := [
  .c 457, .c 3, .c 83, .c 5, .c 3, .c 167, .c 239, .c 3, .c 5, .p pv17 [pv2,pv3,pv107,pv1033],
  .c 3, .c 379, .c 401, .c 3, .p pv5 [pv2,pv1989563], .c 7, .c 3, .p pv2 [pv2,pv19,pv41,pv1277],
  .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv11,pv6029], .c 3, .c 5, .p pv2 [pv2,pv3,pv663191],
  .c 3, .c 11, .c 139, .c 3, .c 7, .p pv3 [pv2,pv3,pv683,pv971], .c 3,
  .p pv2 [pv2,pv11,pv180871], .c 5, .c 3, .c 313, .c 7, .c 3, .c 5, .c 29, .c 3,
  .p pv2 [pv2,pv5,pv198959], .c 13, .c 3, .c 53, .c 19, .c 3, .p pv3 [pv2,pv7,pv10151], .c 5,
  .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv829], .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv397921],
  .c 7, .c 3, .c 11, .p pv2 [pv2,pv3,pv663203], .c 3, .c 107, .c 5,
]
private theorem h0486c32 : checkBlock 3979099 64 b0486c32 = true := by decide +kernel
private noncomputable def b0486c33 : List Row := [
  .c 3, .p pv2 [pv2,pv11,pv90437], .c 97, .c 3, .c 5, .p pv2 [pv2,pv3,pv331603], .c 3, .c 7,
  .c 419, .c 3, .p pv5 [pv2,pv19,pv104717], .c 211, .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv17,pv117037], .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv71,pv9341], .c 3, .c 1613,
  .c 587, .c 3, .c 487, .c 89, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv497411], .c 127, .c 3, .c 5,
  .c 7, .c 3, .c 317, .c 19, .c 3, .c 467, .c 17, .c 3, .c 13, .c 5, .c 3, .c 163, .c 977, .c 3,
  .c 5, .c 11, .c 3, .c 67, .c 229, .c 3, .c 41, .c 7, .c 3, .c 17, .c 5, .c 3, .c 11, .c 29,
  .c 3,
]
private theorem h0486c33 : checkBlock 3979227 64 b0486c33 = true := by decide +kernel
private noncomputable def b0486c34 : List Row := [
  .c 5, .p pv11 [pv2,pv3,pv331613], .c 3, .p pv31 [pv2,pv5,pv7,pv11,pv17,pv19],
  .p pv2 [pv2,pv3,pv509,pv1303], .c 3, .c 7, .c 353, .c 3, .c 59, .c 5, .c 3, .c 19, .c 7, .c 3,
  .c 5, .c 37, .c 3, .c 13, .c 11, .c 3, .c 1543, .c 53, .c 3, .c 199, .c 5, .c 3, .c 7, .c 17,
  .c 3, .c 5, .c 13, .c 3, .c 797, .c 7, .c 3, .p pv2 [pv2,pv11,pv180883], .c 1237, .c 3,
  .p pv3 [pv2,pv59,pv8431], .c 5, .c 3, .c 31, .c 1433, .c 3, .c 5, .c 1481, .c 3, .c 7, .c 263,
  .c 3, .c 61, .c 11, .c 3, .p pv11 [pv2,pv17,pv117043], .c 5, .c 3, .c 13, .c 809, .c 3, .c 5,
  .c 881, .c 3, .c 11,
]
private theorem h0486c34 : checkBlock 3979355 64 b0486c34 = true := by decide +kernel
private noncomputable def b0486c35 : List Row := [
  .c 23, .c 3, .c 449, .c 941, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv37,pv53777], .c 31, .c 3,
  .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv397951], .c 17, .c 3, .p pv2 [pv2,pv994879], .c 173, .c 3,
  .p pv2 [pv2,pv73,pv97,pv281], .c 5, .c 3, .c 23, .c 19, .c 3, .c 5, .c 47, .c 3, .c 1973,
  .p pv5 [pv2,pv3,pv7,pv41,pv2311], .c 3, .c 11, .c 7, .c 3, .p pv3 [pv2,pv23,pv5407], .c 5,
  .c 3, .c 1663, .p pv7 [pv2,pv3,pv5,pv13,pv2551], .c 3, .c 5, .p pv3 [pv2,pv3,pv221087], .c 3,
  .p pv2 [pv2,pv5,pv7,pv139,pv409], .c 13, .c 3, .c 7, .c 61, .c 3, .c 29, .c 5, .c 3, .c 239,
  .c 7, .c 3, .c 5, .c 197, .c 3, .c 83, .p pv11 [pv2,pv3,pv11,pv101,pv199], .c 3, .c 19, .c 37,
]
private theorem h0486c35 : checkBlock 3979483 64 b0486c35 = true := by decide +kernel
private noncomputable def b0486c36 : List Row := [
  .c 3, .c 11, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv19,pv4987], .c 3,
  .c 47, .c 7, .c 3, .p pv2 [pv2,pv157,pv6337], .p pv11 [pv2,pv3,pv13,pv5669], .c 3,
  .p pv2 [pv2,pv1223,pv1627], .c 5, .c 3, .c 17, .c 13, .c 3, .c 5, .c 11, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv419,pv1583], .c 3, .c 23, .p pv13 [pv2,pv3,pv7,pv11,pv59,pv73], .c 3,
  .c 1327, .c 5, .c 3, .c 11, .c 883, .c 3, .c 5, .c 31, .c 3, .p pv2 [pv2,pv5,pv11,pv13,pv23],
  .c 43, .c 3, .c 647, .c 29, .c 3, .c 7, .c 5, .c 3, .c 139, .p pv3 [pv2,pv3,pv5,pv7,pv6317],
  .c 3, .c 5, .c 7, .c 3, .c 19, .c 11, .c 3, .c 59, .c 13, .c 3, .c 67, .c 5, .c 3,
]
private theorem h0486c36 : checkBlock 3979611 64 b0486c36 = true := by decide +kernel
private noncomputable def b0486c37 : List Row := [
  .p pv2 [pv2,pv7,pv284267], .c 73, .c 3, .c 5, .c 41, .c 3, .c 17, .c 383, .c 3, .c 29, .c 7,
  .c 3, .c 71, .c 5, .c 3, .c 1979, .p pv2 [pv2,pv3,pv5,pv53,pv2503], .c 3, .c 5, .c 167, .c 3,
  .c 13, .c 79, .c 3, .c 7, .c 11, .c 3, .c 157, .c 5, .c 3, .c 127, .c 7, .c 3, .c 5, .c 13,
  .c 3, .c 11, .c 89, .c 3, .c 103, .c 17, .c 3, .c 53, .c 5, .c 3, .c 7, .c 37, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv17,pv929], .c 3, .c 683, .c 7, .c 3, .c 563,
  .p pv7 [pv2,pv3,pv139,pv1193], .c 3, .c 17, .c 5, .c 3, .c 13,
  .p pv11 [pv2,pv3,pv5,pv113,pv587], .c 3, .c 5,
]
private theorem h0486c37 : checkBlock 3979739 64 b0486c37 = true := by decide +kernel
private noncomputable def b0486c38 : List Row := [
  .c 67, .c 3, .c 7, .c 19, .c 3, .c 11, .c 379, .c 3, .p pv2 [pv2,pv211,pv9431], .c 5, .c 3,
  .p pv3 [pv2,pv11,pv22613], .p pv3 [pv2,pv3,pv5,pv44221], .c 3, .c 5, .c 23, .c 3,
  .p pv2 [pv2,pv5,pv39799], .c 1427, .c 3, .c 151, .c 1907, .c 3, .c 7, .c 5, .c 3, .c 521,
  .c 11, .c 3, .c 5, .c 7, .c 3, .c 29, .c 83, .c 3, .c 13, .c 149, .c 3, .c 11, .c 5, .c 3,
  .c 19, .c 43, .c 3, .c 5, .p pv2 [pv2,pv3,pv331663], .c 3, .c 1987, .c 13, .c 3,
  .p pv5 [pv2,pv23,pv31,pv2791], .c 7, .c 3, .c 113, .c 5, .c 3, .c 37,
  .p pv2 [pv2,pv3,pv5,pv22111], .c 3, .c 5, .c 11, .c 3, .c 89, .c 41,
]
private theorem h0486c38 : checkBlock 3979867 64 b0486c38 = true := by decide +kernel
private noncomputable def b0486c39 : List Row := [
  .c 3, .c 7, .p pv3 [pv2,pv3,pv11,pv20101], .c 3, .p pv2 [pv2,pv13,pv153077], .c 5, .c 3, .c 11,
  .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv37,pv83], .c 3, .c 1993, .c 17, .c 3,
  .p pv2 [pv2,pv109,pv18257], .c 829, .c 3, .c 73, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 29,
  .c 3, .p pv2 [pv2,pv5,pv79601], .c 7, .c 3, .c 17, .c 31, .c 3, .c 19, .c 5, .c 3,
  .p pv2 [pv2,pv67,pv14851], .p pv3 [pv2,pv3,pv5,pv14741], .c 3, .c 5, .c 1013, .c 3, .c 7,
  .c 677, .c 3, .p pv5 [pv2,pv11,pv113,pv1601], .p pv47 [pv2,pv3,pv7,pv53,pv149], .c 3, .c 13,
  .c 5, .c 3, .c 79, .c 19, .c 3, .c 5, .c 101, .c 3, .c 167, .p pv5 [pv2,pv3,pv283,pv293], .c 3,
  .p pv2 [pv2,pv7,pv41,pv3467], .c 11, .c 3,
]
private theorem h0486c39 : checkBlock 3979995 64 b0486c39 = true := by decide +kernel
private noncomputable def b0486c40 : List Row := [
  .c 7, .c 5, .c 3, .c 971, .c 1423, .c 3, .c 5, .c 7, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv17,pv13007], .c 3, .p pv2 [pv2,pv577,pv3449], .c 1033, .c 3, .c 1291, .c 5,
  .c 3, .c 17, .p pv19 [pv2,pv3,pv5,pv691], .c 3, .c 5, .c 983, .c 3, .c 13, .c 23, .c 3, .c 19,
  .c 7, .c 3, .c 31, .c 5, .c 3, .c 61, .p pv3 [pv2,pv3,pv5,pv181,pv733], .c 3, .c 5, .c 13,
  .c 3, .c 37, .p pv3 [pv2,pv3,pv67,pv9901], .c 3, .c 7, .c 43, .c 3, .c 277, .c 5, .c 3, .c 23,
  .c 7, .c 3, .c 5, .c 17, .c 3, .p pv13 [pv2,pv5,pv398023], .c 359, .c 3, .c 149, .c 41, .c 3,
  .c 1693, .c 5, .c 3, .c 7,
]
private theorem h0486c40 : checkBlock 3980123 64 b0486c40 = true := by decide +kernel
private noncomputable def b0486c41 : List Row := [
  .c 11, .c 3, .c 5, .c 79, .c 3, .c 17, .c 7, .c 3, .c 617, .c 67, .c 3, .c 11, .c 5, .c 3,
  .c 29, .p pv11 [pv2,pv3,pv5,pv41,pv809], .c 3, .c 5, .p pv5 [pv2,pv3,pv73709], .c 3, .c 7,
  .c 107, .c 3, .c 163, .p pv3 [pv2,pv3,pv7,pv97,pv977], .c 3, .p pv5 [pv2,pv1990151], .c 5,
  .c 3, .c 101, .c 23, .c 3, .c 5, .c 11, .c 3, .c 41, .p pv2 [pv2,pv3,pv397,pv557], .c 3, .c 13,
  .c 17, .c 3, .c 7, .c 5, .c 3, .c 11, .p pv11 [pv2,pv3,pv5,pv7,pv13], .c 3, .c 5, .c 7, .c 3,
  .c 827, .c 13, .c 3, .c 23, .p pv3 [pv2,pv3,pv251,pv881], .c 3, .c 17, .c 5, .c 3, .c 31,
  .c 181, .c 3, .c 5, .p pv13 [pv2,pv3,pv59,pv937],
]
private theorem h0486c41 : checkBlock 3980251 64 b0486c41 = true := by decide +kernel
private noncomputable def b0486c42 : List Row := [
  .c 3, .c 43, .c 11, .c 3, .p pv2 [pv2,pv19,pv37,pv149], .c 7, .c 3, .c 269, .c 5, .c 3,
  .p pv11 [pv2,pv73,pv137,pv199], .p pv19 [pv2,pv3,pv5,pv31,pv107], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv53,pv12517], .c 3, .c 463, .c 439, .c 3, .c 7, .p pv3 [pv2,pv3,pv13,pv51031],
  .c 3, .c 37, .c 5, .c 3, .p pv2 [pv2,pv353,pv2819], .c 7, .c 3, .c 5, .c 347, .c 3, .c 571,
  .c 19, .c 3, .c 587, .c 11, .c 3, .c 29, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv11,pv37,pv163], .c 3, .c 5, .c 43, .c 3, .c 11, .c 7, .c 3, .c 47,
  .p pv3 [pv2,pv3,pv229,pv2897], .c 3, .c 13, .c 5, .c 3, .c 311,
  .p pv2 [pv2,pv3,pv5,pv277,pv479], .c 3, .c 5, .c 37, .c 3, .c 7, .p pv3 [pv2,pv3,pv24571],
  .c 3,
]
private theorem h0486c42 : checkBlock 3980379 64 b0486c42 = true := by decide +kernel
private noncomputable def b0486c43 : List Row := [
  .c 107, .c 13, .c 3, .p pv3 [pv2,pv53,pv2347], .c 5, .c 3, .c 19,
  .p pv11 [pv2,pv3,pv5,pv11057], .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv41,pv1471], .c 3,
  .p pv2 [pv2,pv5,pv398053], .c 17, .c 3, .c 11, .c 1607, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv13,pv6959], .p pv3 [pv2,pv3,pv5,pv7,pv17,pv223], .c 3, .c 5, .c 7, .c 3,
  .c 13, .c 1249, .c 3, .c 17, .c 29, .c 3, .c 79, .c 5, .c 3, .p pv2 [pv2,pv7,pv157,pv1811],
  .c 11, .c 3, .c 5, .c 13, .c 3, .p pv17 [pv2,pv5,pv398059], .p pv5 [pv2,pv3,pv7,pv11,pv359],
  .c 3, .c 83, .c 7, .c 3, .c 11, .c 5, .c 3, .c 251, .p pv13 [pv2,pv3,pv5,pv23,pv641], .c 3,
  .c 5, .c 31, .c 3, .p pv2 [pv2,pv5,pv7,pv28433], .c 163, .c 3, .c 7,
  .p pv19 [pv2,pv3,pv110573], .c 3, .c 19,
]
private theorem h0486c43 : checkBlock 3980507 64 b0486c43 = true := by decide +kernel
private noncomputable def b0486c44 : List Row := [
  .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 11, .c 3, .c 113, .p pv2 [pv2,pv3,pv13,pv17,pv19,pv79],
  .c 3, .p pv3 [pv2,pv23,pv29,pv373], .c 1579, .c 3, .p pv7 [pv2,pv7,pv151,pv269], .c 5, .c 3,
  .c 7, .c 19, .c 3, .c 5, .c 61, .c 3, .c 953, .c 7, .c 3, .p pv5 [pv2,pv17,pv71,pv97],
  .p pv17 [pv2,pv3,pv127,pv653], .c 3, .p pv2 [pv2,pv995173], .c 5, .c 3, .c 1487, .c 1733, .c 3,
  .c 5, .c 229, .c 3, .c 7, .c 11, .c 3, .c 13, .c 37, .c 3, .c 577, .c 5, .c 3,
  .p pv3 [pv2,pv19,pv26189], .c 41, .c 3, .c 5, .c 17, .c 3, .c 31, .c 13, .c 3, .c 19,
  .p pv7 [pv2,pv3,pv23,pv14423], .c 3, .c 7, .c 5, .c 3, .c 47, .p pv37 [pv2,pv3,pv5,pv7,pv677],
]
private theorem h0486c44 : checkBlock 3980635 64 b0486c44 = true := by decide +kernel
private noncomputable def b0486c45 : List Row := [
  .c 3, .c 5, .c 7, .c 3, .c 17, .c 223, .c 3, .c 53, .c 11, .c 3, .c 97, .c 5, .c 3, .c 59,
  .c 761, .c 3, .c 5, .c 409, .c 3, .c 11, .c 31, .c 3, .c 1217, .c 7, .c 3, .c 41, .c 5, .c 3,
  .p pv2 [pv2,pv193,pv10313], .c 13, .c 3, .c 5, .p pv7 [pv2,pv3,pv8191], .c 3,
  .p pv7 [pv2,pv5,pv7,pv29,pv37,pv53], .c 149, .c 3, .c 7, .c 17, .c 3,
  .p pv2 [pv2,pv19,pv104759], .c 5, .c 3, .c 367, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv17,pv887], .c 3, .c 19, .c 23, .c 3, .c 11, .c 307, .c 3, .c 13, .c 5,
  .c 3, .c 7, .c 89, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv13,pv23,pv317], .c 3,
]
private theorem h0486c45 : checkBlock 3980763 64 b0486c45 = true := by decide +kernel
private noncomputable def b0486c46 : List Row := [
  .p pv13 [pv2,pv5,pv17,pv23417], .c 7, .c 3, .c 43, .c 13, .c 3, .c 173, .c 5, .c 3, .c 23,
  .c 11, .c 3, .c 5, .c 29, .c 3, .c 7, .c 733, .c 3, .c 31, .c 83, .c 3, .c 11, .c 5, .c 3,
  .c 67, .c 17, .c 3, .c 5, .c 47, .c 3, .c 13, .c 1913, .c 3, .p pv3 [pv2,pv7,pv19,pv1069],
  .c 131, .c 3, .c 7, .c 5, .c 3, .c 479, .p pv41 [pv2,pv3,pv5,pv7,pv71,pv89], .c 3, .c 5, .c 7,
  .c 3, .c 337, .c 43, .c 3, .p pv2 [pv2,pv1990493], .c 31, .c 3, .c 739, .c 5, .c 3, .c 11,
  .c 23, .c 3, .c 5, .c 109, .c 3, .c 193, .c 19, .c 3, .p pv3 [pv2,pv13,pv101,pv379],
]
private theorem h0486c46 : checkBlock 3980891 64 b0486c46 = true := by decide +kernel
private noncomputable def b0486c47 : List Row := [
  .c 7, .c 3, .c 239, .c 5, .c 3, .c 13, .c 263, .c 3, .c 5, .p pv5 [pv2,pv3,pv331753], .c 3,
  .c 47, .c 11, .c 3, .c 7, .c 157, .c 3, .c 103, .c 5, .c 3, .c 41, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv547,pv1213], .c 3, .p pv17 [pv2,pv5,pv19,pv23,pv911], .c 67, .c 3, .c 17,
  .c 241, .c 3, .c 137, .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .p pv37 [pv2,pv3,pv7,pv2633], .c 3,
  .p pv2 [pv2,pv5,pv41,pv971], .c 7, .c 3, .c 13, .c 11, .c 3, .c 31, .c 5, .c 3,
  .p pv7 [pv2,pv1990559], .c 1619, .c 3, .c 5, .c 19, .c 3, .c 7, .c 13, .c 3,
  .p pv3 [pv2,pv248821], .c 23, .c 3, .c 59, .c 5,
]
private theorem h0486c47 : checkBlock 3981019 64 b0486c47 = true := by decide +kernel
private noncomputable def b0486c48 : List Row := [
  .c 3, .c 29, .c 1181, .c 3, .c 5, .p pv5 [pv2,pv3,pv103,pv3221], .c 3,
  .p pv3 [pv2,pv5,pv99529], .c 37, .c 3, .p pv5 [pv2,pv7,pv284369], .p pv17 [pv2,pv3,pv27647],
  .c 3, .c 7, .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv7,pv9479], .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv398119], .p pv5 [pv2,pv3,pv165883], .c 3, .c 11, .c 811, .c 3, .c 19, .c 5,
  .c 3, .p pv3 [pv2,pv7,pv11,pv23,pv281], .c 13, .c 3, .c 5, .p pv29 [pv2,pv3,pv113,pv367], .c 3,
  .c 131, .c 41, .c 3, .p pv2 [pv2,pv61,pv32633], .c 7, .c 3, .c 1019, .c 5, .c 3, .c 881, .c 11,
  .c 3, .c 5, .c 17, .c 3, .c 641, .p pv2 [pv2,pv3,pv11,pv30161], .c 3, .c 7, .c 103, .c 3,
  .c 11, .c 5, .c 3, .c 1627, .c 7, .c 3,
]
private theorem h0486c48 : checkBlock 3981147 64 b0486c48 = true := by decide +kernel
private noncomputable def b0486c49 : List Row := [
  .c 5, .c 23, .c 3, .c 17, .c 449, .c 3, .c 61, .c 13, .c 3, .c 569, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv23,pv577], .c 3, .c 5, .c 11, .c 3, .c 37, .c 7, .c 3, .c 19, .c 101,
  .c 3, .c 23, .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv31,pv1427], .c 3, .c 5, .c 463, .c 3,
  .c 7, .p pv3 [pv2,pv3,pv663557], .c 3, .c 73, .c 17, .c 3, .c 227, .c 5, .c 3, .c 211, .c 31,
  .c 3, .c 5, .c 13, .c 3, .c 941, .c 11, .c 3, .c 139, .c 59, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv995347], .p pv7 [pv2,pv3,pv5,pv7,pv18959], .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv17,pv1171],
]
private theorem h0486c49 : checkBlock 3981275 64 b0486c49 = true := by decide +kernel
private noncomputable def b0486c50 : List Row := [
  .p pv2 [pv2,pv3,pv373,pv593], .c 3, .p pv5 [pv2,pv11,pv13,pv13921], .c 61, .c 3, .c 43, .c 5,
  .c 3, .c 13, .p pv41 [pv2,pv3,pv5,pv73,pv101], .c 3, .c 5, .c 83, .c 3, .c 19, .c 787, .c 3,
  .c 677, .c 7, .c 3, .c 109, .c 5, .c 3, .p pv3 [pv2,pv479,pv1039], .c 17, .c 3, .c 5, .c 181,
  .c 3, .c 11, .p pv17 [pv2,pv3,pv97,pv6841], .c 3, .c 7, .c 19, .c 3, .p pv3 [pv2,pv11,pv11311],
  .c 5, .c 3, .p pv13 [pv2,pv347,pv5737], .c 7, .c 3, .c 5, .c 353, .c 3,
  .p pv2 [pv2,pv5,pv398149], .c 73, .c 3, .c 13, .c 43, .c 3, .p pv5 [pv2,pv7,pv17,pv16729],
  .c 5, .c 3, .c 7, .c 47, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv11,pv31,pv139], .c 3, .c 79, .c 7,
  .c 3, .c 11, .c 401,
]
private theorem h0486c50 : checkBlock 3981403 64 b0486c50 = true := by decide +kernel
private noncomputable def b0486c51 : List Row := [
  .c 3, .c 37, .c 5, .c 3, .p pv2 [pv2,pv11,pv71,pv2549], .p pv13 [pv2,pv3,pv5,pv66359], .c 3,
  .c 5, .c 31, .c 3, .c 7, .c 17, .c 3, .c 263, .c 97, .c 3, .p pv2 [pv2,pv13,pv153137], .c 5,
  .c 3, .p pv3 [pv2,pv103,pv151], .c 11, .c 3, .c 5, .c 107, .c 3, .p pv2 [pv2,pv5,pv227,pv877],
  .c 19, .c 3, .c 17, .p pv2 [pv2,pv3,pv13,pv25523], .c 3, .c 7, .c 5, .c 3, .c 23, .c 13, .c 3,
  .c 5, .c 7, .c 3, .c 1459, .c 29, .c 3, .p pv3 [pv2,pv248851], .p pv13 [pv2,pv3,pv221201],
  .c 3, .c 229, .c 5, .c 3, .p pv2 [pv2,pv7,pv43,pv3307], .c 137, .c 3, .c 5, .c 11, .c 3,
  .p pv3 [pv2,pv5,pv13,pv19,pv31], .p pv3 [pv2,pv3,pv7,pv29,pv467], .c 3, .p pv5 [pv2,pv1990823],
  .c 7, .c 3, .c 13, .c 5, .c 3,
]
private theorem h0486c51 : checkBlock 3981531 64 b0486c51 = true := by decide +kernel
private noncomputable def b0486c52 : List Row := [
  .c 11, .c 109, .c 3, .c 5, .c 1741, .c 3, .c 29, .c 313, .c 3, .c 7, .c 13, .c 3,
  .p pv2 [pv2,pv89,pv22369], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 19, .c 3, .c 257, .c 11,
  .c 3, .p pv2 [pv2,pv17,pv117109], .p pv2 [pv2,pv3,pv110603], .c 3, .c 1439, .c 5, .c 3, .c 7,
  .c 1289, .c 3, .c 5, .c 149, .c 3, .c 13, .c 7, .c 3, .c 23, .p pv11 [pv2,pv3,pv269,pv2467],
  .c 3, .c 67, .c 5, .c 3, .p pv2 [pv2,pv503,pv1979], .c 71, .c 3, .c 5, .c 13, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv221209], .c 3, .p pv5 [pv2,pv1990883], .c 11, .c 3, .c 19, .c 5, .c 3,
  .c 727, .c 113, .c 3, .c 5,
]
private theorem h0486c52 : checkBlock 3981659 64 b0486c52 = true := by decide +kernel
private noncomputable def b0486c53 : List Row := [
  .c 29, .c 3, .c 11, .c 47, .c 3, .c 41, .c 1093, .c 3, .c 7, .c 5, .c 3, .c 13, .c 19, .c 3,
  .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv263,pv757], .p pv3 [pv2,pv3,pv13,pv71,pv719], .c 3,
  .p pv2 [pv2,pv31,pv64223], .c 23, .c 3, .p pv3 [pv2,pv497729], .c 5, .c 3,
  .p pv11 [pv2,pv7,pv41,pv991], .c 457, .c 3, .c 5, .p pv11 [pv2,pv3,pv11,pv60331], .c 3, .c 59,
  .c 1723, .c 3, .c 11, .c 7, .c 3, .p pv5 [pv2,pv569,pv3499], .c 5, .c 3,
  .p pv2 [pv2,pv11,pv19,pv433], .p pv3 [pv2,pv3,pv5,pv151,pv293], .c 3, .c 5, .c 67, .c 3,
  .p pv3 [pv2,pv5,pv7,pv14221], .p pv3 [pv2,pv3,pv769,pv863], .c 3, .c 7,
  .p pv19 [pv2,pv3,pv31,pv223], .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv23,pv107,pv809], .c 7,
  .c 3, .c 5, .c 509, .c 3, .p pv13 [pv2,pv5,pv17,pv59,pv397], .c 13,
]
private theorem h0486c53 : checkBlock 3981787 64 b0486c53 = true := by decide +kernel
private noncomputable def b0486c54 : List Row := [
  .c 3, .p pv2 [pv2,pv79,pv12601], .c 31, .c 3, .c 11, .c 5, .c 3, .c 7, .c 73, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv7,pv1693], .c 3, .c 173, .c 7, .c 3, .c 97, .c 89, .c 3,
  .p pv3 [pv2,pv13,pv2393], .c 5, .c 3, .p pv7 [pv2,pv61,pv127,pv257], .c 17, .c 3, .c 5, .c 11,
  .c 3, .c 7, .p pv11 [pv2,pv3,pv43,pv7717], .c 3, .c 37, .c 239, .c 3, .c 1129, .c 5, .c 3,
  .c 11, .c 13, .c 3, .c 5, .c 1471, .c 3, .c 19, .c 521, .c 3, .c 113, .c 431, .c 3, .c 7, .c 5,
  .c 3, .c 29, .c 151, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv13,pv30631], .c 11, .c 3,
  .p pv2 [pv2,pv23,pv43283], .c 19, .c 3,
]
private theorem h0486c54 : checkBlock 3981915 64 b0486c54 = true := by decide +kernel
private noncomputable def b0486c55 : List Row := [
  .c 13, .c 5, .c 3, .c 53, .c 37, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv12763], .c 3, .c 1319,
  .c 17, .c 3, .p pv2 [pv2,pv11,pv181003], .c 7, .c 3, .p pv3 [pv2,pv139,pv3581], .c 5, .c 3,
  .p pv29 [pv2,pv67,pv29717], .c 229, .c 3, .c 5, .c 59, .c 3, .c 83, .c 283, .c 3, .c 7, .c 11,
  .c 3, .c 1013, .c 5, .c 3, .c 467, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv331843], .c 3, .c 11,
  .p pv2 [pv2,pv3,pv47,pv523], .c 3, .c 89, .p pv11 [pv2,pv3,pv23,pv3607], .c 3, .c 983, .c 5,
  .c 3, .c 7, .c 61, .c 3, .c 5, .c 13, .c 3, .c 23, .c 7, .c 3, .p pv2 [pv2,pv995539], .c 191,
  .c 3, .c 293, .c 5, .c 3, .c 47,
]
private theorem h0486c55 : checkBlock 3982043 64 b0486c55 = true := by decide +kernel
private noncomputable def b0486c56 : List Row := [
  .p pv3 [pv2,pv3,pv5,pv132739], .c 3, .c 5, .c 71, .c 3, .c 7, .p pv3 [pv2,pv3,pv17,pv39041],
  .c 3, .c 11, .c 199, .c 3, .c 29, .c 5, .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv6637], .c 3, .c 5,
  .c 41, .c 3, .c 139, .c 179, .c 3, .c 1259, .c 107, .c 3, .c 7, .c 5, .c 3, .c 19, .c 11, .c 3,
  .c 5, .c 7, .c 3, .c 631, .c 23, .c 3, .p pv5 [pv2,pv1991123], .p pv7 [pv2,pv3,pv19,pv41,pv71],
  .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv7,pv284447], .c 53, .c 3, .c 5, .c 17, .c 3,
  .p pv13 [pv2,pv5,pv398227], .c 37, .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv167,pv11923], .c 5,
  .c 3, .c 23, .c 31, .c 3, .c 5, .c 11,
]
private theorem h0486c56 : checkBlock 3982171 64 b0486c56 = true := by decide +kernel
private noncomputable def b0486c57 : List Row := [
  .c 3, .c 17, .c 13, .c 3, .c 7, .c 29, .c 3, .c 761, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5,
  .c 1327, .c 3, .c 401, .p pv5 [pv2,pv3,pv281,pv1181], .c 3, .c 659, .c 127, .c 3, .c 19, .c 5,
  .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv139,pv191], .c 3, .c 5, .c 47, .c 3, .c 1301, .c 7, .c 3,
  .c 29, .c 17, .c 3, .p pv2 [pv2,pv995593], .c 5, .c 3, .p pv2 [pv2,pv1991189], .c 13, .c 3,
  .c 5, .c 359, .c 3, .c 7, .p pv5 [pv2,pv3,pv103,pv179], .c 3, .p pv2 [pv2,pv11,pv29,pv3121],
  .p pv3 [pv2,pv3,pv7,pv94819], .c 3, .c 17, .c 5, .c 3, .c 1481, .p pv3 [pv2,pv3,pv5,pv44249],
  .c 3, .c 5, .p pv5 [pv2,pv3,pv163,pv509], .c 3, .c 37, .c 83, .c 3,
]
private theorem h0486c57 : checkBlock 3982299 64 b0486c57 = true := by decide +kernel
private noncomputable def b0486c58 : List Row := [
  .c 23, .c 11, .c 3, .c 7, .c 5, .c 3, .c 349, .c 59, .c 3, .c 5, .c 7, .c 3, .c 11, .c 41,
  .c 3, .c 19, .c 13, .c 3, .c 1667, .c 5, .c 3, .c 79, .c 17, .c 3, .c 5, .c 31, .c 3,
  .p pv3 [pv2,pv5,pv67,pv743], .c 29, .c 3, .c 1039, .c 7, .c 3, .p pv2 [pv2,pv995623], .c 5,
  .c 3, .p pv2 [pv2,pv13,pv47,pv3259], .c 491, .c 3, .c 5, .c 61, .c 3, .c 13,
  .p pv5 [pv2,pv3,pv29,pv2861], .c 3, .c 7, .c 23, .c 3, .c 1009, .c 5, .c 3, .c 97, .c 7, .c 3,
  .c 5, .c 13, .c 3, .c 29, .c 181, .c 3, .c 67, .p pv2 [pv2,pv3,pv79,pv4201], .c 3, .c 751,
]
private theorem h0486c58 : checkBlock 3982427 64 b0486c58 = true := by decide +kernel
private noncomputable def b0486c59 : List Row := [
  .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv94823], .c 3, .c 19, .c 7, .c 3,
  .c 757, .c 53, .c 3, .c 11, .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv17,pv19,pv137], .c 3,
  .c 5, .p pv5 [pv2,pv3,pv331883], .c 3, .c 7, .c 71, .c 3, .c 17, .c 19, .c 3, .c 281, .c 5,
  .c 3, .c 157, .c 149, .c 3, .c 5, .c 11, .c 3, .p pv7 [pv2,pv5,pv449,pv887], .c 173, .c 3,
  .c 907, .c 47, .c 3, .c 7, .c 5, .c 3, .c 11, .c 769, .c 3, .c 5, .c 7, .c 3, .c 73, .c 31,
  .c 3, .c 13, .c 233, .c 3, .c 1453, .c 5, .c 3, .p pv31 [pv2,pv7,pv284477], .c 67,
]
private theorem h0486c59 : checkBlock 3982555 64 b0486c59 = true := by decide +kernel
private noncomputable def b0486c60 : List Row := [
  .c 3, .c 5, .p pv3 [pv2,pv3,pv29,pv47,pv487], .c 3, .p pv2 [pv2,pv5,pv61,pv6529], .c 11, .c 3,
  .p pv3 [pv2,pv239,pv2083], .c 7, .c 3, .c 23, .c 5, .c 3, .c 17, .c 307, .c 3, .c 5, .c 37,
  .c 3, .p pv13 [pv2,pv5,pv7,pv127], .c 19, .c 3, .c 7, .c 257, .c 3, .c 47, .c 5, .c 3,
  .p pv2 [pv2,pv53,pv37573], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv43,pv359], .c 3, .c 61, .c 1031,
  .c 3, .c 1427, .c 11, .c 3, .p pv2 [pv2,pv7,pv284483], .c 5, .c 3, .c 7, .c 13, .c 3, .c 5,
  .c 17, .c 3, .c 11, .c 7, .c 3, .c 31, .c 43, .c 3, .c 131, .c 5, .c 3, .c 19,
  .p pv19 [pv2,pv3,pv5,pv3319], .c 3, .c 5, .c 73, .c 3,
]
private theorem h0486c60 : checkBlock 3982683 64 b0486c60 = true := by decide +kernel
private noncomputable def b0486c61 : List Row := [
  .c 7, .p pv2 [pv2,pv3,pv61,pv5441], .c 3, .c 383, .p pv11 [pv2,pv3,pv7,pv19,pv23,pv31], .c 3,
  .c 13, .c 5, .c 3, .c 991, .c 29, .c 3, .c 5, .c 19, .c 3, .c 23, .c 1499, .c 3, .c 11, .c 13,
  .c 3, .c 7, .c 5, .c 3, .c 1697, .c 107, .c 3, .c 5, .c 7, .c 3, .c 431, .c 61, .c 3,
  .p pv2 [pv2,pv995719], .c 17, .c 3, .p pv2 [pv2,pv67,pv29723], .c 5, .c 3, .c 29, .c 11, .c 3,
  .c 5, .c 53, .c 3, .c 13, .p pv7 [pv2,pv3,pv7,pv11,pv37,pv233], .c 3, .c 103, .c 7, .c 3,
  .c 11, .c 5, .c 3, .c 149, .c 47, .c 3, .c 5, .c 13, .c 3, .p pv7 [pv2,pv5,pv7,pv17,pv3347],
  .c 23, .c 3, .c 7,
]
private theorem h0486c61 : checkBlock 3982811 64 b0486c61 = true := by decide +kernel
private noncomputable def b0486c62 : List Row := [
  .c 37, .c 3, .c 79, .c 5, .c 3, .c 67, .c 7, .c 3, .c 5, .c 11, .c 3, .c 43, .c 1277, .c 3,
  .p pv5 [pv2,pv13,pv153191], .c 109, .c 3, .c 31, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv41,pv257], .c 3, .p pv17 [pv2,pv5,pv11,pv36209], .c 7, .c 3, .c 229,
  .p pv11 [pv2,pv3,pv17,pv2297], .c 3, .c 53, .c 5, .c 3, .p pv3 [pv2,pv19,pv6551],
  .p pv3 [pv2,pv3,pv5,pv103,pv1289], .c 3, .c 5, .c 89, .c 3, .c 7, .c 11, .c 3, .c 19, .c 71,
  .c 3, .p pv5 [pv2,pv17,pv29287], .c 5, .c 3, .p pv7 [pv2,pv1991519],
  .p pv11 [pv2,pv3,pv5,pv461], .c 3, .c 5, .c 43, .c 3, .c 367, .c 1049, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv221281], .c 3, .c 7, .c 5,
]
private theorem h0486c62 : checkBlock 3982939 64 b0486c62 = true := by decide +kernel
private noncomputable def b0486c63 : List Row := [
  .c 3, .p pv2 [pv2,pv41,pv149,pv163], .c 23, .c 3, .c 5, .c 7, .c 3, .c 421, .c 13, .c 3, .c 37,
  .c 11, .c 3, .p pv2 [pv2,pv29,pv34337], .c 5, .c 3, .c 73, .c 79, .c 3, .c 5, .c 557, .c 3,
  .c 11, .c 103, .c 3, .c 17, .c 7, .c 3, .p pv2 [pv2,pv11,pv13,pv19,pv733], .c 5, .c 3,
  .p pv3 [pv2,pv31,pv16061], .p pv2 [pv2,pv3,pv5,pv44257], .c 3, .c 5, .c 101, .c 3, .c 19,
  .c 197, .c 3, .c 7, .c 59, .c 3, .p pv3 [pv2,pv173,pv1439], .c 5, .c 3, .c 31, .c 7, .c 3,
  .c 5, .c 433, .c 3, .c 71, .c 487, .c 3, .c 11, .c 19, .c 3, .c 859, .c 5, .c 3, .c 7, .c 41,
  .c 3,
]
private theorem h0486c63 : checkBlock 3983067 64 b0486c63 = true := by decide +kernel
noncomputable def rows0486 : List Row :=
  b0486c00 ++ ( b0486c01 ++ ( b0486c02 ++ ( b0486c03 ++ ( b0486c04 ++ ( b0486c05 ++ (
  b0486c06 ++ ( b0486c07 ++ ( b0486c08 ++ ( b0486c09 ++ ( b0486c10 ++ ( b0486c11 ++ (
  b0486c12 ++ ( b0486c13 ++ ( b0486c14 ++ ( b0486c15 ++ ( b0486c16 ++ ( b0486c17 ++ (
  b0486c18 ++ ( b0486c19 ++ ( b0486c20 ++ ( b0486c21 ++ ( b0486c22 ++ ( b0486c23 ++ (
  b0486c24 ++ ( b0486c25 ++ ( b0486c26 ++ ( b0486c27 ++ ( b0486c28 ++ ( b0486c29 ++ (
  b0486c30 ++ ( b0486c31 ++ ( b0486c32 ++ ( b0486c33 ++ ( b0486c34 ++ ( b0486c35 ++ (
  b0486c36 ++ ( b0486c37 ++ ( b0486c38 ++ ( b0486c39 ++ ( b0486c40 ++ ( b0486c41 ++ (
  b0486c42 ++ ( b0486c43 ++ ( b0486c44 ++ ( b0486c45 ++ ( b0486c46 ++ ( b0486c47 ++ (
  b0486c48 ++ ( b0486c49 ++ ( b0486c50 ++ ( b0486c51 ++ ( b0486c52 ++ ( b0486c53 ++ (
  b0486c54 ++ ( b0486c55 ++ ( b0486c56 ++ ( b0486c57 ++ ( b0486c58 ++ ( b0486c59 ++ (
  b0486c60 ++ ( b0486c61 ++ ( b0486c62 ++ ( b0486c63
  )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
attribute [local irreducible] checkBlock checkRows checkPrime
theorem checked0486 : checkBlock 3975003 4096 rows0486 = true :=
  checkBlock_append h0486c00 ( checkBlock_append h0486c01 ( checkBlock_append h0486c02 (
  checkBlock_append h0486c03 ( checkBlock_append h0486c04 ( checkBlock_append h0486c05 (
  checkBlock_append h0486c06 ( checkBlock_append h0486c07 ( checkBlock_append h0486c08 (
  checkBlock_append h0486c09 ( checkBlock_append h0486c10 ( checkBlock_append h0486c11 (
  checkBlock_append h0486c12 ( checkBlock_append h0486c13 ( checkBlock_append h0486c14 (
  checkBlock_append h0486c15 ( checkBlock_append h0486c16 ( checkBlock_append h0486c17 (
  checkBlock_append h0486c18 ( checkBlock_append h0486c19 ( checkBlock_append h0486c20 (
  checkBlock_append h0486c21 ( checkBlock_append h0486c22 ( checkBlock_append h0486c23 (
  checkBlock_append h0486c24 ( checkBlock_append h0486c25 ( checkBlock_append h0486c26 (
  checkBlock_append h0486c27 ( checkBlock_append h0486c28 ( checkBlock_append h0486c29 (
  checkBlock_append h0486c30 ( checkBlock_append h0486c31 ( checkBlock_append h0486c32 (
  checkBlock_append h0486c33 ( checkBlock_append h0486c34 ( checkBlock_append h0486c35 (
  checkBlock_append h0486c36 ( checkBlock_append h0486c37 ( checkBlock_append h0486c38 (
  checkBlock_append h0486c39 ( checkBlock_append h0486c40 ( checkBlock_append h0486c41 (
  checkBlock_append h0486c42 ( checkBlock_append h0486c43 ( checkBlock_append h0486c44 (
  checkBlock_append h0486c45 ( checkBlock_append h0486c46 ( checkBlock_append h0486c47 (
  checkBlock_append h0486c48 ( checkBlock_append h0486c49 ( checkBlock_append h0486c50 (
  checkBlock_append h0486c51 ( checkBlock_append h0486c52 ( checkBlock_append h0486c53 (
  checkBlock_append h0486c54 ( checkBlock_append h0486c55 ( checkBlock_append h0486c56 (
  checkBlock_append h0486c57 ( checkBlock_append h0486c58 ( checkBlock_append h0486c59 (
  checkBlock_append h0486c60 ( checkBlock_append h0486c61 ( checkBlock_append h0486c62 ( h0486c63
  )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
end D5.S3.Arith.PrimitiveRoot.SmallPrimes
