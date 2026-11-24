/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks03/Block0302
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks03/Block0302.checked0302
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table032
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table036
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table041
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table042
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table049
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table060
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table075
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table100
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table101
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table143

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0302c00 : List Row := [
  .c 53, .c 3, .c 13, .c 17, .c 3, .p pv2 [pv2,pv7,pv149,pv593], .c 11, .c 3, .c 7, .c 5, .c 3,
  .c 19, .c 761, .c 3, .c 5, .c 7, .c 3, .c 11, .c 191, .c 3, .c 17, .c 1103, .c 3, .c 47, .c 5,
  .c 3, .p pv7 [pv2,pv7,pv61,pv2897], .c 23, .c 3, .c 5, .c 19, .c 3, .p pv13 [pv2,pv5,pv49481],
  .p pv2 [pv2,pv3,pv7,pv29453], .c 3, .p pv3 [pv2,pv13,pv23789], .c 7, .c 3, .c 41, .c 5, .c 3,
  .c 13, .p pv17 [pv2,pv3,pv5,pv82469], .c 3, .c 5, .c 29, .c 3, .c 547, .c 137, .c 3, .c 7,
  .c 181, .c 3, .c 53, .c 5, .c 3, .c 61, .c 7, .c 3, .c 5, .c 251, .c 3, .c 89, .c 307, .c 3,
  .p pv2 [pv2,pv37,pv73,pv229], .p pv3 [pv2,pv3,pv45817], .c 3, .c 19, .c 5, .c 3, .c 7, .c 11,
  .c 3, .c 5, .c 71, .c 3, .c 31, .c 7, .c 3, .c 13, .c 491, .c 3, .c 11, .c 5, .c 3, .c 857,
  .c 19, .c 3, .c 5, .c 199, .c 3, .c 7, .c 13, .c 3, .c 43, .c 23, .c 3, .p pv5 [pv2,pv1237091],
  .c 5, .c 3, .c 73, .c 109, .c 3, .c 5, .c 11, .c 3, .c 79, .c 31, .c 3,
  .p pv7 [pv2,pv7,pv25247], .p pv23 [pv2,pv3,pv11,pv71], .c 3, .c 7, .c 5, .c 3, .c 11, .c 47,
  .c 3, .c 5, .c 7, .c 3, .c 17, .c 1321, .c 3, .c 19, .p pv31 [pv2,pv3,pv13,pv31721], .c 3,
]
private theorem h0302c00 : checkBlock 2473987 128 b0302c00 = true := by
  decide +kernel

private def b0302c01 : List Row := [
  .c 67, .c 5, .c 3, .c 509, .c 13, .c 3, .c 5, .c 503, .c 3, .p pv7 [pv2,pv5,pv193,pv641], .c 11,
  .c 3, .p pv2 [pv2,pv103,pv12011], .c 7, .c 3, .p pv3 [pv2,pv167,pv463], .c 5, .c 3, .c 71,
  .p pv7 [pv2,pv3,pv5,pv29,pv79], .c 3, .c 5, .p pv3 [pv2,pv3,pv151,pv2731], .c 3,
  .p pv2 [pv2,pv5,pv7,pv13,pv2719], .c 1567, .c 3, .c 7, .c 17, .c 3, .c 13, .c 5, .c 3, .c 29,
  .c 7, .c 3, .c 5, .c 23, .c 3, .p pv13 [pv2,pv5,pv157,pv197], .c 1171, .c 3, .c 31, .c 11, .c 3,
  .c 17, .c 5, .c 3, .c 7, .c 127, .c 3, .c 5, .c 241, .c 3, .c 11, .c 7, .c 3, .c 137, .c 79,
  .c 3, .c 23, .c 5, .c 3, .c 103, .c 431, .c 3, .c 5, .c 67, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv412397], .c 3, .p pv2 [pv2,pv23,pv53791], .c 19, .c 3,
  .p pv3 [pv2,pv43,pv7193], .c 5, .c 3, .c 101, .c 17, .c 3, .c 5, .c 13, .c 3, .c 53,
  .p pv5 [pv2,pv3,pv37,pv5573], .c 3, .c 11, .c 173, .c 3, .c 7, .c 5, .c 3, .c 389,
  .p pv7 [pv2,pv3,pv5,pv7,pv11783], .c 3, .c 5, .c 7, .c 3, .c 277, .c 149, .c 3, .c 487, .c 37,
  .c 3, .c 193, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 89, .c 3, .c 691, .c 41, .c 3, .c 157,
  .c 7, .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv309311], .c 379, .c 3, .c 5,
  .p pv23 [pv2,pv3,pv179],
]
private theorem h0302c01 : checkBlock 2474243 128 b0302c01 = true := by
  decide +kernel

private def b0302c02 : List Row := [
  .c 3, .c 23, .c 17, .c 3, .c 7, .c 683, .c 3, .c 31, .c 5, .c 3, .c 59, .c 7, .c 3, .c 5, .c 11,
  .c 3, .c 269, .p pv2 [pv2,pv3,pv68737], .c 3, .c 13, .p pv7 [pv2,pv3,pv11,pv37493], .c 3,
  .p pv5 [pv2,pv7,pv176753], .c 5, .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv13,pv47], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv89,pv331], .c 3, .p pv3 [pv2,pv5,pv11,pv19,pv37], .c 7, .c 3, .c 97,
  .p pv7 [pv2,pv3,pv34369], .c 3, .p pv2 [pv2,pv618643], .c 5, .c 3, .c 19, .c 569, .c 3, .c 5,
  .c 61, .c 3, .c 7, .c 11, .c 3, .c 37, .c 29, .c 3, .p pv2 [pv2,pv13,pv95177], .c 5, .c 3,
  .c 251, .p pv2 [pv2,pv3,pv5,pv82487], .c 3, .c 5, .c 19, .c 3, .c 673, .c 53, .c 3, .c 73,
  .p pv17 [pv2,pv3,pv13,pv29,pv547], .c 3, .c 7, .c 5, .c 3, .c 17, .c 13, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv43,pv1151], .c 257, .c 3, .c 29, .c 11, .c 3, .p pv5 [pv2,pv23,pv2339], .c 5,
  .c 3, .p pv2 [pv2,pv7,pv31,pv2851], .c 37, .c 3, .c 5, .p pv2 [pv2,pv3,pv53,pv1297], .c 3,
  .c 11, .p pv19 [pv2,pv3,pv7,pv58921], .c 3, .p pv5 [pv2,pv29,pv42667], .c 7, .c 3, .c 13, .c 5,
  .c 3, .c 31, .p pv2 [pv2,pv3,pv5,pv73,pv113], .c 3, .c 5, .c 17, .c 3,
  .p pv7 [pv2,pv5,pv7,pv35353], .p pv7 [pv2,pv3,pv19,pv67], .c 3, .c 7, .c 13, .c 3,
  .p pv2 [pv2,pv127,pv9743], .c 5, .c 3, .c 53, .c 7, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv11,pv43,pv109], .c 3, .c 17, .p pv5 [pv2,pv3,pv412457], .c 3, .c 11,
  .p pv2 [pv2,pv3,pv68743], .c 3, .c 577,
]
private theorem h0302c02 : checkBlock 2474499 128 b0302c02 = true := by
  decide +kernel

private def b0302c03 : List Row := [
  .c 5, .c 3, .c 7, .c 31, .c 3, .c 5, .c 281, .c 3, .c 13, .c 7, .c 3, .c 23, .c 43, .c 3,
  .p pv5 [pv2,pv37,pv53,pv631], .c 5, .c 3, .p pv2 [pv2,pv19,pv32563], .c 11, .c 3, .c 5, .c 13,
  .c 3, .c 7, .c 101, .c 3, .c 19, .c 17, .c 3, .c 11, .c 5, .c 3, .c 37,
  .p pv11 [pv2,pv3,pv5,pv4583], .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv19,pv1277], .c 3, .c 29, .c 79,
  .c 3, .p pv3 [pv2,pv7,pv13,pv523], .c 193, .c 3, .c 7, .c 5, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv5,pv7,pv2357], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv17,pv29,pv251],
  .p pv3 [pv2,pv3,pv13,pv31729], .c 3, .c 919, .c 23, .c 3, .c 59, .c 5, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv5,pv1289], .c 3, .c 5, .c 331, .c 3, .c 313, .c 37, .c 3,
  .p pv3 [pv2,pv154681], .c 7, .c 3, .p pv5 [pv2,pv19,pv65129], .c 5, .c 3,
  .p pv2 [pv2,pv43,pv14389], .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv31,pv6653], .c 3, .c 19, .c 11,
  .c 3, .c 7, .p pv11 [pv2,pv3,pv17,pv337], .c 3, .c 743, .c 5, .c 3,
  .p pv2 [pv2,pv23,pv173,pv311], .c 7, .c 3, .c 5, .c 29, .c 3, .c 43, .c 13, .c 3,
  .p pv2 [pv2,pv11,pv56249], .c 19, .c 3, .c 199, .c 5, .c 3, .c 7, .c 293, .c 3, .c 5, .c 83,
  .c 3, .c 227, .c 7, .c 3, .c 103, .c 11, .c 3, .c 479, .c 5, .c 3, .p pv7 [pv2,pv1237499],
  .c 89, .c 3, .c 5, .c 23, .c 3,
]
private theorem h0302c03 : checkBlock 2474755 128 b0302c03 = true := by
  decide +kernel

private def b0302c04 : List Row := [
  .c 7, .c 17, .c 3, .c 107, .p pv2 [pv2,pv3,pv7,pv13,pv1511], .c 3, .p pv5 [pv2,pv11,pv112501],
  .c 5, .c 3, .p pv2 [pv2,pv433,pv1429], .c 13, .c 3, .c 5, .c 43, .c 3, .c 37, .c 271, .c 3,
  .c 17, .c 883, .c 3, .c 7, .c 5, .c 3, .c 421, .p pv2 [pv2,pv3,pv5,pv7,pv71,pv83], .c 3, .c 5,
  .c 7, .c 3, .c 31, .c 19, .c 3, .c 11, .c 971, .c 3, .c 13, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv11,pv41], .p pv2 [pv2,pv3,pv5,pv89,pv103], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv7933], .c 3, .p pv7 [pv2,pv5,pv53,pv467], .c 127, .c 3, .c 167, .c 7,
  .c 3, .p pv3 [pv2,pv457,pv677], .c 5, .c 3, .c 709, .c 11, .c 3, .c 5, .c 1483, .c 3, .c 71,
  .c 31, .c 3, .c 7, .p pv3 [pv2,pv3,pv73,pv5651], .c 3, .c 11, .c 5, .c 3, .c 17, .c 7, .c 3,
  .c 5, .p pv7 [pv2,pv3,pv206263], .c 3, .c 13, .p pv2 [pv2,pv3,pv199,pv691], .c 3, .c 257,
  .c 191, .c 3, .c 139, .c 5, .c 3, .c 7, .c 67, .c 3, .c 5, .c 11, .c 3, .c 23, .c 7, .c 3,
  .c 61, .p pv31 [pv2,pv3,pv11,pv463], .c 3, .c 907, .c 5, .c 3, .c 11, .c 41, .c 3, .c 5, .c 17,
  .c 3, .c 7, .p pv3 [pv2,pv3,pv412537], .c 3, .c 59, .p pv2 [pv2,pv3,pv7,pv79,pv373], .c 3,
  .c 431, .c 5, .c 3, .c 13, .c 211, .c 3, .c 5, .p pv3 [pv2,pv3,pv97,pv4253], .c 3, .c 17, .c 11,
  .c 3, .c 31, .c 53, .c 3, .c 7, .c 5,
]
private theorem h0302c04 : checkBlock 2475011 128 b0302c04 = true := by
  decide +kernel

private def b0302c05 : List Row := [
  .c 3, .p pv2 [pv2,pv17,pv89,pv409], .c 521, .c 3, .c 5, .c 7, .c 3, .c 109, .c 23, .c 3,
  .p pv5 [pv2,pv11,pv59,pv1907], .p pv53 [pv2,pv3,pv31,pv1109], .c 3, .c 41, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv176807], .c 19, .c 3, .c 5, .c 79, .c 3, .c 241, .c 1061, .c 3, .c 13, .c 7,
  .c 3, .c 239, .c 5, .c 3, .c 23, .p pv11 [pv2,pv3,pv5,pv11,pv13,pv577], .c 3, .c 5, .c 37, .c 3,
  .c 11, .c 13, .c 3, .c 7, .c 47, .c 3, .c 17, .c 5, .c 3, .c 523, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv412561], .c 3, .p pv2 [pv2,pv5,pv17,pv14561], .c 401, .c 3, .c 19, .c 587,
  .c 3, .p pv5 [pv2,pv7,pv13,pv29,pv67], .c 5, .c 3, .c 7, .c 179, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv11,pv19,pv47], .c 3, .c 283, .c 7, .c 3, .c 11, .c 101, .c 3, .c 631,
  .c 5, .c 3, .c 157, .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv412571], .c 3, .c 7,
  .p pv17 [pv2,pv3,pv34381], .c 3, .p pv2 [pv2,pv618859], .p pv7 [pv2,pv3,pv7,pv17,pv3467], .c 3,
  .c 31, .c 5, .c 3, .c 67, .c 11, .c 3, .c 5, .c 41, .c 3, .c 433, .c 59, .c 3, .c 23, .c 29,
  .c 3, .c 7, .c 5, .c 3, .c 1091, .c 163, .c 3, .c 5, .c 7, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv206291], .c 3, .p pv3 [pv2,pv309437], .c 13, .c 3, .c 73, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv88411], .c 563, .c 3, .c 5, .c 11, .c 3, .c 439,
]
private theorem h0302c05 : checkBlock 2475267 128 b0302c05 = true := by
  decide +kernel

private def b0302c06 : List Row := [
  .c 17, .c 3, .c 29, .c 7, .c 3, .c 761, .c 5, .c 3, .c 11, .c 1231, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv412591], .c 3, .c 13, .c 43, .c 3, .c 7, .c 23, .c 3, .c 61, .c 5, .c 3,
  .c 457, .c 7, .c 3, .c 5, .c 13, .c 3, .c 59, .c 11, .c 3, .p pv2 [pv2,pv19,pv65147], .c 353,
  .c 3, .p pv3 [pv2,pv7,pv44207], .c 5, .c 3, .c 7, .c 373, .c 3, .c 5, .c 269, .c 3, .c 101,
  .c 7, .c 3, .c 887, .c 263, .c 3, .c 79, .c 5, .c 3, .c 13, .c 47, .c 3, .c 5, .c 1367, .c 3,
  .c 7, .c 19, .c 3, .p pv5 [pv2,pv1237823], .c 11, .c 3, .p pv2 [pv2,pv618913], .c 5, .c 3,
  .c 17, .c 463, .c 3, .c 5, .c 599, .c 3, .c 11, .p pv5 [pv2,pv3,pv29,pv3557], .c 3, .c 409,
  .p pv13 [pv2,pv3,pv47,pv8779], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv309461], .c 31, .c 3, .c 5,
  .c 7, .c 3, .c 29, .c 41, .c 3, .c 13, .p pv29 [pv2,pv3,pv103,pv2003], .c 3, .c 89, .c 5, .c 3,
  .c 19, .p pv7 [pv2,pv3,pv5,pv13,pv23], .c 3, .c 5, .c 17, .c 3, .c 97, .c 13, .c 3, .c 11, .c 7,
  .c 3, .c 23, .c 5, .c 3, .c 179, .p pv11 [pv2,pv3,pv5,pv3301], .c 3, .c 5, .c 19, .c 3, .c 17,
  .c 1319, .c 3, .c 7, .c 131, .c 3, .p pv2 [pv2,pv13,pv47,pv1013], .c 5, .c 3,
]
private theorem h0302c06 : checkBlock 2475523 128 b0302c06 = true := by
  decide +kernel

private def b0302c07 : List Row := [
  .p pv2 [pv2,pv17,pv72817], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv449,pv919], .c 3,
  .p pv13 [pv2,pv5,pv247579], .c 241, .c 3, .p pv2 [pv2,pv151,pv4099],
  .p pv7 [pv2,pv3,pv13,pv31741], .c 3, .c 11, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 29, .c 3,
  .p pv2 [pv2,pv5,pv123791], .c 7, .c 3, .p pv2 [pv2,pv41,pv109,pv277], .c 17, .c 3, .c 19, .c 5,
  .c 3, .p pv7 [pv2,pv1237919], .c 71, .c 3, .c 5, .c 11, .c 3, .c 7, .c 691, .c 3,
  .p pv3 [pv2,pv271,pv571], .p pv2 [pv2,pv3,pv7,pv11,pv23,pv233], .c 3, .c 13, .c 5, .c 3, .c 11,
  .c 19, .c 3, .c 5, .c 31, .c 3, .c 23, .p pv3 [pv2,pv3,pv263,pv523], .c 3,
  .p pv5 [pv2,pv7,pv176849], .c 13, .c 3, .c 7, .c 5, .c 3, .c 181, .c 421, .c 3, .c 5, .c 7,
  .c 3, .p pv7 [pv2,pv5,pv247591], .c 11, .c 3, .p pv2 [pv2,pv618979], .c 773, .c 3, .c 1459,
  .c 5, .c 3, .c 37, .c 17, .c 3, .c 5, .c 1039, .c 3, .c 13, .c 113, .c 3, .c 19, .c 7, .c 3,
  .c 607, .c 5, .c 3, .p pv13 [pv2,pv199,pv6221], .p pv31 [pv2,pv3,pv5,pv47,pv439], .c 3, .c 5,
  .c 13, .c 3, .p pv7 [pv2,pv5,pv7,pv31,pv163], .c 23, .c 3, .c 7, .c 11, .c 3, .c 43, .c 5, .c 3,
  .p pv2 [pv2,pv618997], .c 7, .c 3, .c 5, .c 193, .c 3, .c 11, .c 37, .c 3, .c 47,
  .p pv11 [pv2,pv3,pv3821], .c 3, .p pv2 [pv2,pv7,pv11,pv8039], .c 5, .c 3, .c 7, .c 617, .c 3,
  .c 5, .c 1163, .c 3, .c 41, .c 7,
]
private theorem h0302c07 : checkBlock 2475779 128 b0302c07 = true := by
  decide +kernel

private def b0302c08 : List Row := [
  .c 3, .p pv2 [pv2,pv619009], .p pv3 [pv2,pv3,pv499,pv827], .c 3, .p pv2 [pv2,pv19,pv23,pv2833],
  .c 5, .c 3, .c 29, .c 61, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv83,pv113], .c 3, .c 7, .c 31, .c 3,
  .c 11, .c 43, .c 3, .p pv3 [pv2,pv41,pv7549], .c 5, .c 3, .p pv7 [pv2,pv11,pv29,pv3881],
  .p pv29 [pv2,pv3,pv5,pv19,pv181], .c 3, .c 5, .c 73, .c 3, .c 233, .c 197, .c 3, .c 13, .c 19,
  .c 3, .c 7, .c 5, .c 3, .c 167, .c 11, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv103,pv601],
  .c 13, .c 3, .c 271, .p pv7 [pv2,pv3,pv25793], .c 3, .c 11, .c 5, .c 3, .c 83,
  .p pv2 [pv2,pv3,pv5,pv41269], .c 3, .c 5, .c 757, .c 3, .c 37, .c 109, .c 3, .c 23, .c 7, .c 3,
  .p pv2 [pv2,pv13,pv131,pv727], .c 5, .c 3, .c 17, .c 59, .c 3, .c 5, .c 11, .c 3,
  .p pv13 [pv2,pv5,pv7,pv23,pv769], .c 641, .c 3, .c 7, .p pv43 [pv2,pv3,pv11,pv13,pv37], .c 3,
  .c 643, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 1489, .c 3, .c 331, .c 19, .c 3, .c 101,
  .p pv2 [pv2,pv3,pv31,pv13313], .c 3, .c 29, .c 5, .c 3, .c 7, .c 149, .c 3, .c 5, .c 17, .c 3,
  .c 43, .c 7, .c 3, .c 89, .c 23, .c 3, .c 13, .c 5, .c 3, .c 853, .c 181, .c 3, .c 5, .c 71,
  .c 3, .c 7, .p pv5 [pv2,pv3,pv23,pv2243], .c 3, .c 41, .c 13, .c 3, .p pv2 [pv2,pv113,pv10957],
  .c 5, .c 3, .c 19,
]
private theorem h0302c08 : checkBlock 2476035 128 b0302c08 = true := by
  decide +kernel

private def b0302c09 : List Row := [
  .p pv11 [pv2,pv3,pv5,pv197,pv419], .c 3, .c 5, .p pv5 [pv2,pv3,pv163,pv211], .c 3, .c 107,
  .p pv3 [pv2,pv3,pv412717], .c 3, .p pv2 [pv2,pv7,pv73,pv2423], .c 11, .c 3, .c 7, .c 5, .c 3,
  .c 53, .p pv19 [pv2,pv3,pv5,pv7,pv11,pv67], .c 3, .c 5, .c 7, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv7643], .c 3, .p pv3 [pv2,pv37,pv47,pv89], .c 17, .c 3, .c 227, .c 5, .c 3,
  .c 809, .p pv3 [pv2,pv3,pv5,pv5503], .c 3, .c 5, .c 13, .c 3, .c 157,
  .p pv7 [pv2,pv3,pv7,pv8423], .c 3, .p pv5 [pv2,pv251,pv4933], .c 7, .c 3, .c 17, .c 5, .c 3,
  .c 73, .p pv23 [pv2,pv3,pv5,pv149,pv277], .c 3, .c 5, .c 23, .c 3,
  .p pv7 [pv2,pv5,pv7,pv17,pv2081], .p pv5 [pv2,pv3,pv103183], .c 3, .c 7, .c 439, .c 3, .c 19,
  .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 61, .c 3, .p pv2 [pv2,pv5,pv123821],
  .p pv5 [pv2,pv3,pv13,pv19,pv557], .c 3, .c 571, .c 103, .c 3, .c 23, .c 5, .c 3, .c 7, .c 11,
  .c 3, .c 5, .c 37, .c 3, .p pv2 [pv2,pv5,pv49529], .c 7, .c 3, .c 1429, .c 163, .c 3, .c 11,
  .c 5, .c 3, .p pv2 [pv2,pv619117], .c 83, .c 3, .c 5, .c 47, .c 3, .c 7, .c 457, .c 3, .c 13,
  .p pv19 [pv2,pv3,pv7,pv14741], .c 3, .c 311, .c 5, .c 3, .c 43, .c 467, .c 3, .c 5, .c 11, .c 3,
  .p pv7 [pv2,pv5,pv247651], .c 13, .c 3, .c 19, .c 1439, .c 3, .c 7, .c 5, .c 3, .c 11, .c 53,
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv11,pv11257], .c 17, .c 3,
]
private theorem h0302c09 : checkBlock 2476291 128 b0302c09 = true := by
  decide +kernel

private def b0302c10 : List Row := [
  .p pv2 [pv2,pv1238273], .c 137, .c 3, .c 587, .c 5, .c 3, .c 31,
  .p pv7 [pv2,pv3,pv5,pv17,pv607], .c 3, .c 5, .p pv3 [pv2,pv3,pv137587], .c 3, .c 23, .c 11,
  .c 3, .c 17, .c 7, .c 3, .p pv5 [pv2,pv1238291], .c 5, .c 3, .c 109, .c 13, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv206383], .c 3, .p pv23 [pv2,pv5,pv7,pv29,pv61], .c 89, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv12899], .c 3, .c 337, .c 5, .c 3, .c 619, .c 7, .c 3, .c 5, .c 127, .c 3,
  .c 19, .c 701, .c 3, .c 53, .c 11, .c 3, .c 13, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv11,pv19,pv79], .c 3, .c 5, .c 277, .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv1238333], .c 13, .c 3, .p pv3 [pv2,pv11,pv1759], .c 5, .c 3, .c 17,
  .p pv19 [pv2,pv3,pv5,pv20639], .c 3, .c 5, .c 29, .c 3, .c 7, .c 71, .c 3, .c 191,
  .p pv7 [pv2,pv3,pv7,pv109,pv541], .c 3, .p pv5 [pv2,pv59,pv139,pv151], .c 5, .c 3, .c 23,
  .p pv19 [pv2,pv3,pv5,pv9173], .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv29,pv647], .c 3, .c 13,
  .p pv2 [pv2,pv3,pv61,pv67,pv101], .c 3, .c 11, .c 79, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv103,pv1093], .c 359, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv9907],
  .p pv5 [pv2,pv3,pv51599], .c 3, .c 43, .c 47, .c 3, .c 389, .c 5, .c 3, .c 41, .c 11, .c 3,
  .c 5, .c 167, .c 3, .c 17, .c 19, .c 3, .p pv2 [pv2,pv13,pv95261], .c 7, .c 3, .c 11, .c 5,
  .c 3, .c 13, .c 23,
]
private theorem h0302c10 : checkBlock 2476547 128 b0302c10 = true := by
  decide +kernel

private def b0302c11 : List Row := [
  .c 3, .c 5, .c 31, .c 3, .p pv2 [pv2,pv5,pv7,pv41,pv863], .c 443, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv15289], .c 3, .c 101, .c 5, .c 3, .c 653, .c 7, .c 3, .c 5, .c 11, .c 3,
  .c 103, .c 43, .c 3, .c 23, .c 17, .c 3, .c 47, .c 5, .c 3, .c 7, .c 29, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv17,pv3469], .c 3, .p pv11 [pv2,pv5,pv11,pv23,pv89], .c 7, .c 3, .c 13,
  .c 59, .c 3, .c 17, .c 5, .c 3, .c 727, .c 37, .c 3, .c 5, .c 19, .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv71,pv17443], .c 479, .c 3, .p pv3 [pv2,pv154807], .c 5, .c 3, .c 29,
  .p pv7 [pv2,pv3,pv5,pv20641], .c 3, .c 5, .p pv3 [pv2,pv3,pv45869], .c 3, .c 31, .c 41, .c 3,
  .p pv3 [pv2,pv7,pv11,pv4021], .c 23, .c 3, .c 7, .c 5, .c 3, .c 769, .c 17, .c 3, .c 5, .c 7,
  .c 3, .c 593, .c 73, .c 3, .p pv5 [pv2,pv61,pv79,pv257], .c 11, .c 3, .c 19, .c 5, .c 3, .c 557,
  .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv412831], .c 3, .c 11, .c 31, .c 3, .c 59, .c 7, .c 3,
  .c 1303, .c 5, .c 3, .c 911, .c 19, .c 3, .c 5, .c 907, .c 3, .c 971, .c 233, .c 3, .c 7,
  .p pv17 [pv2,pv3,pv206419], .c 3, .c 13, .c 5, .c 3, .c 37, .c 7, .c 3, .c 5, .c 103, .c 3,
  .p pv2 [pv2,pv5,pv107,pv463], .c 17, .c 3, .c 11,
]
private theorem h0302c11 : checkBlock 2476803 128 b0302c11 = true := by
  decide +kernel

private def b0302c12 : List Row := [
  .c 13, .c 3, .p pv7 [pv2,pv7,pv176933], .c 5, .c 3, .c 7, .p pv37 [pv2,pv3,pv5,pv17,pv1619],
  .c 3, .c 5, .c 23, .c 3, .p pv3 [pv2,pv5,pv61927], .c 7, .c 3, .c 17, .c 97, .c 3, .c 29, .c 5,
  .c 3, .c 283, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv19,pv7243], .c 3, .c 7, .c 37, .c 3, .c 31,
  .c 71, .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv419,pv739], .p pv3 [pv2,pv3,pv5,pv82571], .c 3,
  .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv211,pv587], .c 677, .c 3, .p pv5 [pv2,pv7,pv23,pv157],
  .c 61, .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv809,pv1531], .p pv17 [pv2,pv3,pv5,pv7,pv983],
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv247717], .p pv5 [pv2,pv3,pv17,pv12143], .c 3,
  .p pv3 [pv2,pv13,pv23819], .c 31, .c 3, .c 307, .c 5, .c 3, .c 11, .c 67, .c 3, .c 5, .c 263,
  .c 3, .c 19, .c 79, .c 3, .c 1051, .c 7, .c 3, .p pv2 [pv2,pv619303], .c 5, .c 3,
  .p pv2 [pv2,pv83,pv14923], .c 269, .c 3, .c 5, .c 101, .c 3, .p pv7 [pv2,pv5,pv7,pv43,pv823],
  .c 11, .c 3, .c 7, .c 19, .c 3, .c 109, .c 5, .c 3, .p pv3 [pv2,pv38707], .c 7, .c 3, .c 5,
  .c 17, .c 3, .c 23, .p pv5 [pv2,pv3,pv127,pv3251], .c 3, .c 13, .c 1187, .c 3, .c 43, .c 5,
  .c 3, .c 7, .p pv29 [pv2,pv3,pv5,pv13,pv397], .c 3, .c 5, .c 337, .c 3, .c 17, .c 7, .c 3,
  .p pv3 [pv2,pv19,pv29,pv281], .c 11, .c 3, .c 31, .c 5, .c 3, .p pv2 [pv2,pv17,pv2143],
  .p pv3 [pv2,pv3,pv5,pv11,pv7507], .c 3,
]
private theorem h0302c12 : checkBlock 2477059 128 b0302c12 = true := by
  decide +kernel

private def b0302c13 : List Row := [
  .c 5, .p pv2 [pv2,pv3,pv43,pv4801], .c 3, .c 7, .c 47, .c 3, .p pv5 [pv2,pv53,pv23371],
  .p pv11 [pv2,pv3,pv7,pv73,pv101], .c 3, .p pv2 [pv2,pv11,pv13,pv61,pv71], .c 5, .c 3,
  .p pv2 [pv2,pv1103,pv1123], .c 131, .c 3, .c 5, .c 181, .c 3, .c 59, .c 19, .c 3,
  .p pv2 [pv2,pv7,pv103,pv859], .c 17, .c 3, .c 7, .c 5, .c 3, .c 487, .c 13, .c 3, .c 5, .c 7,
  .c 3, .p pv2 [pv2,pv5,pv97,pv1277], .c 29, .c 3, .c 11, .c 127, .c 3, .c 17, .c 5, .c 3, .c 23,
  .c 73, .c 3, .c 5, .p pv5 [pv2,pv3,pv412901], .c 3, .p pv2 [pv2,pv5,pv13,pv17,pv19,pv59],
  .p pv5 [pv2,pv3,pv7,pv29,pv113], .c 3, .c 47, .c 7, .c 3, .c 13, .c 5, .c 3, .c 19, .c 11, .c 3,
  .c 5, .c 163, .c 3, .c 29, .c 1423, .c 3, .c 7, .c 13, .c 3, .c 11, .c 5, .c 3, .c 67, .c 7,
  .c 3, .c 5, .c 19, .c 3, .p pv17 [pv2,pv5,pv29,pv8543], .c 1283, .c 3, .c 97, .c 643, .c 3,
  .c 37, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 11, .c 3, .c 13, .c 7, .c 3, .c 41, .c 1327,
  .c 3, .c 463, .c 5, .c 3, .c 11, .p pv41 [pv2,pv3,pv5,pv31,pv37], .c 3, .c 5, .c 13, .c 3, .c 7,
  .c 173, .c 3, .c 23, .c 179, .c 3, .c 19, .c 5, .c 3, .c 751, .c 31, .c 3, .c 5, .c 29, .c 3,
  .p pv3 [pv2,pv5,pv23,pv2693], .c 11, .c 3, .c 839, .c 571,
]
private theorem h0302c13 : checkBlock 2477315 128 b0302c13 = true := by
  decide +kernel

private def b0302c14 : List Row := [
  .c 3, .c 7, .c 5, .c 3, .c 13, .c 19, .c 3, .c 5, .c 7, .c 3, .c 53, .c 67, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv79,pv5227], .c 3, .c 131, .c 5, .c 3, .p pv3 [pv2,pv7,pv151,pv293],
  .p pv2 [pv2,pv3,pv5,pv27529], .c 3, .c 5, .c 43, .c 3, .c 251, .p pv3 [pv2,pv3,pv7,pv58991],
  .c 3, .c 383, .c 7, .c 3, .c 83, .c 5, .c 3, .p pv13 [pv2,pv19,pv113,pv577],
  .p pv19 [pv2,pv3,pv5,pv11,pv1877], .c 3, .c 5, .p pv5 [pv2,pv3,pv59,pv2333], .c 3, .c 11,
  .c 941, .c 3, .c 7, .p pv2 [pv2,pv3,pv412943], .c 3, .c 1201, .c 5, .c 3, .c 197, .c 7, .c 3,
  .c 5, .c 79, .c 3, .p pv7 [pv2,pv5,pv30971], .c 13, .c 3, .c 71, .p pv13 [pv2,pv3,pv103237],
  .c 3, .c 73, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv2753], .c 3, .c 5, .c 353, .c 3, .c 1237,
  .c 7, .c 3, .c 11, .p pv19 [pv2,pv3,pv179,pv769], .c 3, .c 263, .c 5, .c 3,
  .p pv3 [pv2,pv11,pv7039], .c 29, .c 3, .c 5, .c 31, .c 3, .c 7, .p pv7 [pv2,pv3,pv37,pv11161],
  .c 3, .p pv2 [pv2,pv43,pv47,pv613], .c 199, .c 3, .c 41, .c 5, .c 3, .c 61, .c 11, .c 3, .c 5,
  .c 17, .c 3, .c 19, .c 211, .c 3, .p pv3 [pv2,pv7,pv22123], .c 37, .c 3, .c 7, .c 5, .c 3,
  .c 29, .p pv7 [pv2,pv3,pv5,pv7,pv19,pv23], .c 3, .c 5, .c 7, .c 3, .c 17, .c 53, .c 3,
  .p pv5 [pv2,pv1238903], .c 19, .c 3, .c 13, .c 5, .c 3, .c 431,
  .p pv17 [pv2,pv3,pv5,pv61,pv677], .c 3, .c 5,
]
private theorem h0302c14 : checkBlock 2477571 128 b0302c14 = true := by
  decide +kernel

private def b0302c15 : List Row := [
  .c 11, .c 3, .c 1093, .c 101, .c 3, .p pv2 [pv2,pv23,pv1171], .c 7, .c 3, .c 191, .c 5, .c 3,
  .c 11, .p pv3 [pv2,pv3,pv5,pv16519], .c 3, .c 5, .c 619, .c 3, .c 31, .p pv3 [pv2,pv3,pv137659],
  .c 3, .c 7, .c 17, .c 3, .c 797, .c 5, .c 3, .c 173, .c 7, .c 3, .c 5, .c 47, .c 3, .c 13,
  .c 11, .c 3, .c 109, .p pv2 [pv2,pv3,pv45887], .c 3, .c 17, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv151,pv547], .c 3, .c 5, .c 13, .c 3, .c 1523, .c 7, .c 3, .c 37,
  .p pv7 [pv2,pv3,pv23,pv67], .c 3, .p pv2 [pv2,pv227,pv2729], .c 5, .c 3,
  .p pv2 [pv2,pv89,pv13921], .c 59, .c 3, .c 5, .p pv2 [pv2,pv3,pv167,pv2473], .c 3, .c 7, .c 139,
  .c 3, .p pv2 [pv2,pv13,pv47653], .c 11, .c 3, .c 29, .c 5, .c 3, .c 13, .c 17, .c 3, .c 5,
  .c 113, .c 3, .c 11, .p pv3 [pv2,pv3,pv13,pv31769], .c 3, .p pv2 [pv2,pv7,pv263,pv673], .c 317,
  .c 3, .c 7, .c 5, .c 3, .c 19, .c 37, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv383,pv647],
  .c 107, .c 3, .p pv3 [pv2,pv31,pv1249], .c 149, .c 3, .p pv5 [pv2,pv17,pv72883], .c 5, .c 3,
  .p pv13 [pv2,pv7,pv47,pv269], .c 449, .c 3, .c 5, .c 19, .c 3, .p pv3 [pv2,pv5,pv41,pv1511],
  .c 23, .c 3, .c 11, .c 7, .c 3, .c 823, .c 5, .c 3, .c 59, .c 151, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv23,pv17957], .c 3, .c 181, .c 13, .c 3, .c 7, .c 29, .c 3,
]
private theorem h0302c15 : checkBlock 2477827 128 b0302c15 = true := by
  decide +kernel

private def b0302c16 : List Row := [
  .p pv2 [pv2,pv1239041], .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv17209], .c 3,
  .p pv2 [pv2,pv5,pv24781], .c 1151, .c 3, .c 17, .c 31, .c 3, .c 11, .c 5, .c 3, .c 7, .c 53,
  .c 3, .c 5, .c 131, .c 3, .c 73, .c 7, .c 3, .c 29, .c 281, .c 3, .c 983, .c 5, .c 3, .c 37,
  .c 13, .c 3, .c 5, .c 11, .c 3, .c 7, .c 41, .c 3, .c 1033, .c 47, .c 3, .p pv2 [pv2,pv619543],
  .c 5, .c 3, .c 11, .c 23, .c 3, .c 5, .p pv19 [pv2,pv3,pv37,pv61], .c 3, .c 239, .c 137, .c 3,
  .c 331, .c 223, .c 3, .c 7, .c 5, .c 3, .c 17, .p pv3 [pv2,pv3,pv5,pv7,pv11801], .c 3, .c 5,
  .c 7, .c 3, .p pv2 [pv2,pv5,pv123911], .c 11, .c 3, .c 19, .c 13, .c 3, .c 31, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv229,pv773], .p pv7 [pv2,pv3,pv5,pv1721], .c 3, .c 5, .c 61, .c 3, .c 257,
  .c 29, .c 3, .p pv3 [pv2,pv11,pv14081], .c 7, .c 3, .c 47, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv47659], .p pv3 [pv2,pv3,pv5,pv82609], .c 3, .c 5, .c 17, .c 3, .c 13, .c 103,
  .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv619573], .c 5, .c 3, .c 947, .c 7, .c 3, .c 5, .c 13,
  .c 3, .c 11, .c 193, .c 3, .c 149, .c 23, .c 3, .p pv2 [pv2,pv7,pv11,pv19], .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv67,pv137], .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv461],
]
private theorem h0302c16 : checkBlock 2478083 128 b0302c16 = true := by
  decide +kernel

private def b0302c17 : List Row := [
  .c 3, .c 19, .c 7, .c 3, .p pv2 [pv2,pv13,pv199,pv479], .p pv7 [pv2,pv3,pv43,pv1601], .c 3,
  .c 1163, .c 5, .c 3, .c 13, .p pv11 [pv2,pv3,pv5,pv19,pv1087], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv12517], .c 3, .c 7, .p pv2 [pv2,pv3,pv13,pv15887], .c 3, .c 11, .c 17,
  .c 3, .c 89, .c 5, .c 3, .c 131, .c 43, .c 3, .c 5, .c 67, .c 3, .c 1319,
  .p pv2 [pv2,pv3,pv157,pv877], .c 3, .p pv5 [pv2,pv7,pv211,pv839], .c 41, .c 3, .c 7, .c 5, .c 3,
  .c 31, .c 11, .c 3, .c 5, .c 7, .c 3, .c 1409, .c 181, .c 3, .c 13, .c 53, .c 3, .c 11, .c 5,
  .c 3, .p pv3 [pv2,pv7,pv22129], .c 47, .c 3, .c 5, .c 23, .c 3, .c 1123, .c 13, .c 3, .c 79,
  .c 7, .c 3, .p pv3 [pv2,pv59,pv89], .c 5, .c 3, .p pv11 [pv2,pv1239239], .c 17, .c 3, .c 5,
  .c 11, .c 3, .c 41, .c 19, .c 3, .c 7, .c 659, .c 3, .c 23, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv206543], .c 3, .p pv3 [pv2,pv5,pv11,pv43,pv131], .p pv3 [pv2,pv3,pv413087],
  .c 3, .p pv5 [pv2,pv23,pv53881], .p pv29 [pv2,pv3,pv13,pv331], .c 3, .c 499, .c 5, .c 3, .c 7,
  .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv79,pv83], .c 3, .c 109, .c 7, .c 3,
  .p pv2 [pv2,pv37,pv16747], .c 157, .c 3, .c 43, .c 5, .c 3, .c 19, .c 173, .c 3, .c 5, .c 761,
  .c 3, .c 7, .c 17, .c 3, .p pv2 [pv2,pv11,pv112663], .p pv2 [pv2,pv3,pv7,pv19,pv1553], .c 3,
  .c 13,
]
private theorem h0302c17 : checkBlock 2478339 128 b0302c17 = true := by
  decide +kernel

private def b0302c18 : List Row := [
  .c 5, .c 3, .c 821, .c 29, .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv71,pv3491], .c 61, .c 3,
  .c 17, .c 11, .c 3, .c 7, .c 5, .c 3, .c 83, .p pv43 [pv2,pv3,pv5,pv7,pv11,pv29,pv37], .c 3,
  .c 5, .c 7, .c 3, .c 11, .p pv2 [pv2,pv3,pv73,pv5659], .c 3, .c 313, .c 43, .c 3,
  .p pv2 [pv2,pv11,pv56333], .c 5, .c 3, .c 29, .p pv2 [pv2,pv3,pv5,pv109,pv379], .c 3, .c 5,
  .c 31, .c 3, .c 13, .p pv5 [pv2,pv3,pv7,pv2459], .c 3, .p pv2 [pv2,pv619669], .c 7, .c 3, .c 19,
  .c 5, .c 3, .c 1531, .p pv13 [pv2,pv3,pv5,pv27541], .c 3, .c 5, .c 13, .c 3, .c 281,
  .p pv5 [pv2,pv3,pv17,pv19,pv1279], .c 3, .c 7, .p pv2 [pv2,pv3,pv59,pv389], .c 3,
  .p pv3 [pv2,pv83,pv3733], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv137707], .c 3,
  .p pv2 [pv2,pv5,pv247873], .c 23, .c 3, .c 41, .c 89, .c 3, .p pv5 [pv2,pv7,pv101,pv1753], .c 5,
  .c 3, .c 7, .c 11, .c 3, .c 5, .c 53, .c 3, .p pv3 [pv2,pv5,pv31,pv1999], .c 7, .c 3, .c 59,
  .c 109, .c 3, .c 11, .c 5, .c 3, .c 23, .c 167, .c 3, .c 5, .c 17, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv179,pv577], .c 3, .c 19, .c 67, .c 3, .p pv2 [pv2,pv23,pv53887], .c 5, .c 3,
  .p pv3 [pv2,pv309851], .c 1013, .c 3, .c 5, .c 11, .c 3, .c 17, .c 71, .c 3, .c 13, .c 1487,
  .c 3, .c 7, .c 5, .c 3, .c 11, .c 1459, .c 3, .c 5, .c 7, .c 3,
]
private theorem h0302c18 : checkBlock 2478595 128 b0302c18 = true := by
  decide +kernel

private def b0302c19 : List Row := [
  .c 197, .c 13, .c 3, .c 61, .c 331, .c 3, .c 53, .c 5, .c 3, .c 107, .c 23, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv251,pv823], .c 3, .c 113, .c 11, .c 3, .c 233, .c 7, .c 3, .c 1229, .c 5,
  .c 3, .p pv2 [pv2,pv1239449], .c 41, .c 3, .c 5, .c 43, .c 3, .c 19, .c 127, .c 3, .c 7,
  .c 1181, .c 3, .c 17, .c 5, .c 3, .c 449, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv103289], .c 3,
  .c 79, .c 199, .c 3, .c 349, .c 11, .c 3, .p pv3 [pv2,pv7,pv44267], .c 5, .c 3, .c 7, .c 83,
  .c 3, .c 5, .c 151, .c 3, .c 11, .c 7, .c 3, .c 31, .c 61, .c 3, .c 13, .c 5, .c 3, .c 191,
  .c 17, .c 3, .c 5, .p pv7 [pv2,pv3,pv13,pv5297], .c 3, .c 7, .c 59, .c 3, .c 29, .c 13, .c 3,
  .p pv2 [pv2,pv619753], .c 5, .c 3, .p pv2 [pv2,pv1239509], .c 1223, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv37561], .c 3, .p pv7 [pv2,pv5,pv157,pv1579], .c 439, .c 3, .c 11, .c 31,
  .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv11,pv13,pv197], .c 751, .c 3, .c 5, .c 7, .c 3, .c 13,
  .c 19, .c 3, .c 67, .p pv11 [pv2,pv3,pv68863], .c 3, .c 293, .c 5, .c 3, .c 43, .c 11, .c 3,
  .c 5, .c 13, .c 3, .c 223, .c 17, .c 3, .c 389, .c 7, .c 3, .c 11, .c 5,
]
private theorem h0302c19 : checkBlock 2478851 128 b0302c19 = true := by
  decide +kernel

private def b0302c20 : List Row := [
  .c 3, .c 47, .c 37, .c 3, .c 5, .p pv2 [pv2,pv3,pv206593], .c 3, .c 59, .c 29, .c 3, .c 7,
  .p pv37 [pv2,pv3,pv53,pv1949], .c 3, .c 569, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 11, .c 3,
  .p pv17 [pv2,pv5,pv179,pv277], .c 73, .c 3, .c 181, .c 383, .c 3, .c 31, .c 5, .c 3, .c 7,
  .p pv29 [pv2,pv3,pv5,pv23,pv3593], .c 3, .c 5, .c 19, .c 3, .c 29, .c 7, .c 3, .c 157,
  .p pv2 [pv2,pv3,pv41,pv5039], .c 3, .c 23, .c 5, .c 3, .c 631, .c 67, .c 3, .c 5, .c 557, .c 3,
  .c 7, .c 11, .c 3, .c 13, .p pv3 [pv2,pv3,pv7,pv59029], .c 3, .c 61, .c 5, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv5,pv13,pv163], .c 3, .c 5, .p pv2 [pv2,pv3,pv206603], .c 3,
  .p pv3 [pv2,pv5,pv61981], .c 13, .c 3, .c 101, .c 71, .c 3, .c 7, .c 5, .c 3, .c 37, .c 599,
  .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv41,pv6047], .c 89, .c 3, .p pv2 [pv2,pv619819], .c 11,
  .c 3, .p pv2 [pv2,pv13,pv167,pv571], .c 5, .c 3, .c 137, .c 19, .c 3, .c 5, .c 17, .c 3, .c 11,
  .c 467, .c 3, .p pv2 [pv2,pv131,pv9463], .c 7, .c 3, .c 103, .c 5, .c 3,
  .p pv13 [pv2,pv31,pv39989], .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv29,pv14249], .c 3, .c 17,
  .c 37, .c 3, .c 7, .c 509, .c 3, .c 139, .c 5, .c 3, .c 31, .c 7, .c 3, .c 5, .c 59, .c 3,
  .p pv7 [pv2,pv5,pv13,pv149],
]
private theorem h0302c20 : checkBlock 2479107 128 b0302c20 = true := by
  decide +kernel

private def b0302c21 : List Row := [
  .c 283, .c 3, .c 11, .c 577, .c 3, .c 13, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv31,pv43],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv13,pv19,pv239], .c 3, .c 47, .c 7, .c 3, .c 1439, .c 13, .c 3,
  .c 541, .c 5, .c 3, .p pv3 [pv2,pv241,pv643], .c 11, .c 3, .c 5, .c 97, .c 3, .c 7, .c 23, .c 3,
  .c 277, .p pv11 [pv2,pv3,pv7,pv9839], .c 3, .c 11, .c 5, .c 3, .c 521, .c 653, .c 3, .c 5,
  .c 1087, .c 3, .c 13, .p pv5 [pv2,pv3,pv367,pv563], .c 3, .p pv3 [pv2,pv7,pv11069], .c 83, .c 3,
  .c 7, .c 5, .c 3, .c 23, .c 29, .c 3, .c 5, .c 7, .c 3, .c 19, .p pv2 [pv2,pv3,pv139,pv991],
  .c 3, .p pv5 [pv2,pv389,pv3187], .p pv17 [pv2,pv3,pv11,pv587], .c 3, .p pv2 [pv2,pv23,pv26951],
  .c 5, .c 3, .c 11, .c 17, .c 3, .c 5, .p pv7 [pv2,pv3,pv413251], .c 3, .c 107,
  .p pv17 [pv2,pv3,pv7,pv14759], .c 3, .c 1321, .c 7, .c 3, .p pv2 [pv2,pv1239761], .c 5, .c 3,
  .c 13, .c 499, .c 3, .c 5, .c 223, .c 3, .p pv2 [pv2,pv5,pv7,pv89,pv199], .c 11, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv127,pv1627], .c 3, .p pv3 [pv2,pv17,pv43,pv53], .c 5, .c 3, .c 113, .c 7,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv31,pv13331], .c 3, .c 151, .c 79, .c 3,
  .p pv5 [pv2,pv11,pv19,pv1483], .c 47, .c 3, .p pv5 [pv2,pv7,pv177113], .c 5, .c 3, .c 7, .c 73,
  .c 3, .c 5, .c 31, .c 3, .c 1543, .c 7, .c 3, .c 13, .c 11, .c 3, .c 359, .c 5, .c 3,
]
private theorem h0302c21 : checkBlock 2479363 128 b0302c21 = true := by
  decide +kernel

private def b0302c22 : List Row := [
  .p pv2 [pv2,pv107,pv11587], .c 139, .c 3, .c 5, .p pv5 [pv2,pv3,pv47,pv977], .c 3, .c 7, .c 13,
  .c 3, .c 17, .c 41, .c 3, .c 1187, .c 5, .c 3, .c 241, .c 101, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv103319], .c 3, .p pv2 [pv2,pv5,pv123983], .p pv5 [pv2,pv3,pv347,pv397], .c 3,
  .p pv2 [pv2,pv7,pv37,pv4787], .p pv7 [pv2,pv3,pv206639], .c 3, .c 7, .c 5, .c 3,
  .p pv11 [pv2,pv1239839], .c 43, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv19,pv31,pv421],
  .p pv2 [pv2,pv3,pv206641], .c 3, .c 11, .c 23, .c 3, .c 29, .c 5, .c 3, .c 19, .c 13, .c 3,
  .c 5, .p pv13 [pv2,pv3,pv68881], .c 3, .c 31, .c 617, .c 3, .p pv5 [pv2,pv601,pv2063], .c 7,
  .c 3, .p pv2 [pv2,pv29,pv21377], .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .c 19, .c 3,
  .p pv7 [pv2,pv5,pv7,pv13,pv109], .c 191, .c 3, .c 7, .c 1451, .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv23,pv13477], .c 7, .c 3, .c 5, .c 37, .c 3, .p pv7 [pv2,pv5,pv123989], .c 31,
  .c 3, .p pv2 [pv2,pv1239893], .c 13, .c 3, .c 257, .c 5, .c 3, .c 7,
  .p pv23 [pv2,pv3,pv5,pv4133], .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv43,pv73,pv79], .c 7,
  .c 3, .c 53, .c 29, .c 3, .c 19, .c 5, .c 3, .c 11, .c 719, .c 3, .c 5, .c 23, .c 3, .c 7,
  .c 1091, .c 3, .p pv5 [pv2,pv1239923], .p pv37 [pv2,pv3,pv7,pv29,pv509], .c 3, .c 43, .c 5,
  .c 3, .c 109, .c 19, .c 3, .c 5, .c 13, .c 3, .c 67, .c 11,
]
private theorem h0302c22 : checkBlock 2479619 128 b0302c22 = true := by
  decide +kernel

private def b0302c23 : List Row := [
  .c 3, .c 29, .p pv29 [pv2,pv3,pv137771], .c 3, .c 7, .c 5, .c 3, .c 79, .c 317, .c 3, .c 5,
  .c 7, .c 3, .p pv2 [pv2,pv5,pv24799], .p pv5 [pv2,pv3,pv97,pv4261], .c 3, .c 31, .c 17, .c 3,
  .p pv3 [pv2,pv309989], .c 5, .c 3, .c 13, .c 271, .c 3, .c 5, .p pv3 [pv2,pv3,pv17,pv41,pv593],
  .c 3, .c 103, .c 859, .c 3, .c 19, .c 7, .c 3, .c 17, .c 5, .c 3, .c 1549, .c 647, .c 3, .c 5,
  .c 83, .c 3, .c 11, .p pv2 [pv2,pv3,pv37,pv11171], .c 3, .c 7, .c 31, .c 3, .c 683, .c 5, .c 3,
  .c 1063, .c 7, .c 3, .c 5, .p pv17 [pv2,pv3,pv137777], .c 3, .p pv13 [pv2,pv5,pv247999], .c 29,
  .c 3, .c 13, .c 37, .c 3, .p pv7 [pv2,pv7,pv47,pv3769], .c 5, .c 3, .c 7, .c 17, .c 3, .c 5,
  .c 1093, .c 3, .c 23, .c 7, .c 3, .c 11, .c 53, .c 3, .c 197, .c 5, .c 3, .c 1283, .c 491, .c 3,
  .c 5, .c 79, .c 3, .c 7, .p pv2 [pv2,pv3,pv233,pv887], .c 3, .p pv3 [pv2,pv127,pv2441], .c 397,
  .c 3, .p pv5 [pv2,pv13,pv17,pv31,pv181], .c 5, .c 3, .p pv2 [pv2,pv43,pv14419], .c 11, .c 3,
  .c 5, .c 61, .c 3, .p pv13 [pv2,pv5,pv29,pv1069], .p pv3 [pv2,pv3,pv11,pv53,pv709], .c 3,
  .p pv5 [pv2,pv7,pv25307], .c 19, .c 3, .c 7, .c 5, .c 3, .c 761, .c 13, .c 3, .c 5, .c 7, .c 3,
  .c 43, .c 17, .c 3, .c 167, .p pv3 [pv2,pv3,pv413353], .c 3, .c 83, .c 5, .c 3, .c 157,
]
private theorem h0302c23 : checkBlock 2479875 128 b0302c23 = true := by
  decide +kernel

private def b0302c24 : List Row := [
  .c 41, .c 3, .c 5, .c 11, .c 3, .c 1553, .c 47, .c 3, .c 17, .c 7, .c 3, .c 13, .c 5, .c 3,
  .c 11, .p pv19 [pv2,pv3,pv5,pv5167], .c 3, .c 5, .c 29, .c 3, .p pv7 [pv2,pv5,pv7,pv11,pv3221],
  .c 827, .c 3, .c 7, .c 13, .c 3, .c 59, .c 5, .c 3, .p pv2 [pv2,pv53,pv11699], .c 7, .c 3, .c 5,
  .c 43, .c 3, .p pv3 [pv2,pv5,pv12401], .c 11, .c 3, .p pv5 [pv2,pv67,pv83,pv223],
  .p pv17 [pv2,pv3,pv163,pv317], .c 3, .c 41, .c 5, .c 3, .c 7, .c 37, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv59053], .c 3, .c 13, .c 7, .c 3, .c 47, .c 937, .c 3, .c 71, .c 5, .c 3,
  .c 17, .c 23, .c 3, .c 5, .c 13, .c 3, .c 7, .p pv3 [pv2,pv3,pv479,pv863], .c 3,
  .p pv2 [pv2,pv17,pv72949], .c 11, .c 3, .c 67, .c 5, .c 3, .c 19,
  .p pv23 [pv2,pv3,pv5,pv11,pv1879], .c 3, .c 5, .p pv5 [pv2,pv3,pv157,pv2633], .c 3, .c 11,
  .c 503, .c 3, .c 23, .c 229, .c 3, .c 7, .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv7,pv31,pv127],
  .c 3, .c 5, .c 7, .c 3, .c 61, .p pv2 [pv2,pv3,pv13,pv31799], .c 3, .c 601,
  .p pv17 [pv2,pv3,pv11483], .c 3, .c 619, .c 5, .c 3, .p pv2 [pv2,pv7,pv177167], .c 29, .c 3,
  .c 5, .c 53, .c 3, .c 17, .c 263, .c 3, .c 11, .c 7, .c 3, .c 79, .c 5, .c 3, .c 37, .c 163,
  .c 3, .c 5, .c 41, .c 3, .c 919, .p pv3 [pv2,pv3,pv61,pv251], .c 3,
]
private theorem h0302c24 : checkBlock 2480131 128 b0302c24 = true := by
  decide +kernel

private def b0302c25 : List Row := [
  .c 7, .c 23, .c 3, .c 19, .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .c 67, .c 3,
  .p pv2 [pv2,pv5,pv248041], .c 13, .c 3, .p pv3 [pv2,pv77513], .c 17, .c 3, .c 11, .c 5, .c 3,
  .c 7, .c 19, .c 3, .c 5, .c 127, .c 3, .p pv3 [pv2,pv5,pv62011], .c 7, .c 3,
  .p pv5 [pv2,pv103,pv12041], .c 269, .c 3, .c 17, .c 5, .c 3, .c 41, .c 631, .c 3, .c 5, .c 11,
  .c 3, .c 7, .c 991, .c 3, .c 151, .p pv103 [pv2,pv3,pv7,pv11,pv13,pv59], .c 3,
  .p pv2 [pv2,pv1240241], .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv31,pv1667],
  .c 3, .p pv2 [pv2,pv5,pv11,pv41], .p pv3 [pv2,pv3,pv413417], .c 3, .c 19,
  .p pv2 [pv2,pv3,pv68903], .c 3, .c 7, .c 5, .c 3, .c 47, .c 17, .c 3, .c 5, .c 7, .c 3, .c 353,
  .c 11, .c 3, .c 59, .p pv2 [pv2,pv3,pv17,pv83,pv293], .c 3, .c 13, .c 5, .c 3, .c 103,
  .p pv13 [pv2,pv3,pv5,pv23,pv719], .c 3, .c 5, .c 773, .c 3, .c 1567,
  .p pv2 [pv2,pv3,pv7,pv19687], .c 3, .p pv5 [pv2,pv11,pv47,pv2399], .c 7, .c 3, .c 23, .c 5,
  .c 3, .p pv2 [pv2,pv563,pv2203], .c 97, .c 3, .c 5, .p pv2 [pv2,pv3,pv401,pv1031], .c 3, .c 37,
  .p pv7 [pv2,pv3,pv51679], .c 3, .c 7, .c 11, .c 3, .c 977, .c 5, .c 3, .c 1571, .c 7, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv131,pv263], .c 3, .c 11, .c 17, .c 3, .c 43, .c 193, .c 3, .c 251, .c 5,
  .c 3, .c 7, .c 461,
]
private theorem h0302c25 : checkBlock 2480387 128 b0302c25 = true := by
  decide +kernel

private def b0302c26 : List Row := [
  .c 3, .c 5, .c 13, .c 3, .c 31, .c 7, .c 3, .c 17, .c 19, .c 3, .p pv5 [pv2,pv587,pv2113], .c 5,
  .c 3, .c 71, .p pv3 [pv2,pv3,pv5,pv43,pv641], .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv18793], .c 3,
  .c 7, .p pv2 [pv2,pv3,pv31,pv13337], .c 3, .c 11, .c 29, .c 3, .p pv2 [pv2,pv349,pv1777], .c 5,
  .c 3, .c 13, .c 149, .c 3, .c 5, .c 47, .c 3, .c 23, .c 31, .c 3, .p pv2 [pv2,pv7,pv19,pv4663],
  .p pv3 [pv2,pv3,pv29,pv53,pv269], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv310091], .c 11, .c 3,
  .c 5, .c 7, .c 3, .c 479, .p pv23 [pv2,pv3,pv11,pv17,pv67], .c 3, .c 29,
  .p pv2 [pv2,pv3,pv61,pv3389], .c 3, .c 11, .c 5, .c 3, .c 17, .c 179, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv413461], .c 3, .c 53, .c 19, .c 3, .c 13, .c 7, .c 3, .p pv5 [pv2,pv1240391],
  .c 5, .c 3, .c 439, .c 709, .c 3, .c 5, .c 11, .c 3, .c 47, .c 13, .c 3, .c 7, .c 61, .c 3,
  .c 37, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 17, .c 3, .c 293, .c 1109, .c 3, .c 31, .c 701,
  .c 3, .p pv2 [pv2,pv7,pv13,pv43,pv317], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv37,pv149], .c 3,
  .c 5, .c 1117, .c 3, .c 17, .c 7, .c 3, .c 307, .c 41, .c 3, .p pv3 [pv2,pv23,pv97,pv139], .c 5,
  .c 3, .c 263, .c 13, .c 3, .c 5, .c 19, .c 3, .c 7, .p pv2 [pv2,pv3,pv29,pv7129], .c 3,
  .p pv5 [pv2,pv11,pv881],
]
private theorem h0302c26 : checkBlock 2480643 128 b0302c26 = true := by
  decide +kernel

private def b0302c27 : List Row := [
  .c 31, .c 3, .p pv5 [pv2,pv107,pv11593], .c 5, .c 3, .p pv2 [pv2,pv620227],
  .p pv19 [pv2,pv3,pv5,pv41,pv2017], .c 3, .c 5, .p pv2 [pv2,pv3,pv79,pv2617], .c 3, .c 29,
  .c 839, .c 3, .p pv5 [pv2,pv7,pv177209], .c 11, .c 3, .c 7, .c 5, .c 3, .c 887, .c 23, .c 3,
  .c 5, .c 7, .c 3, .c 11, .c 71, .c 3, .c 617, .c 13, .c 3, .c 17, .c 5, .c 3, .c 97, .c 43,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv5743], .c 3, .p pv2 [pv2,pv5,pv17,pv7297], .c 53, .c 3, .c 23,
  .c 7, .c 3, .c 173, .c 5, .c 3, .c 149, .c 19, .c 3, .c 5, .c 1301, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv68917], .c 3, .c 7, .p pv2 [pv2,pv3,pv197,pv2099], .c 3, .c 31, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv113,pv499], .c 7, .c 3, .c 5, .c 13, .c 3, .c 349,
  .p pv2 [pv2,pv3,pv389,pv1063], .c 3, .p pv5 [pv2,pv1240523], .c 359, .c 3, .c 61, .c 5, .c 3,
  .c 7, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv29,pv97], .c 3, .c 157, .c 7, .c 3, .c 19, .c 23,
  .c 3, .c 11, .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv191,pv433], .c 3, .c 5,
  .p pv7 [pv2,pv3,pv19,pv5441], .c 3, .c 7, .c 1361, .c 3, .p pv2 [pv2,pv1240553], .c 37, .c 3,
  .p pv3 [pv2,pv523,pv593], .c 5, .c 3, .c 83, .p pv13 [pv2,pv3,pv5,pv1723], .c 3, .c 5, .c 11,
  .c 3, .c 1009, .c 17, .c 3, .p pv3 [pv2,pv7,pv22153], .p pv3 [pv2,pv3,pv11,pv4177], .c 3, .c 7,
  .c 5, .c 3, .c 11, .c 313, .c 3,
]
private theorem h0302c27 : checkBlock 2480899 128 b0302c27 = true := by
  decide +kernel

private def b0302c28 : List Row := [
  .c 5, .c 7, .c 3, .c 1297, .c 97, .c 3, .c 13, .p pv7 [pv2,pv3,pv51691], .c 3,
  .p pv2 [pv2,pv19,pv32647], .c 5, .c 3, .p pv2 [pv2,pv7,pv31,pv5717],
  .p pv2 [pv2,pv3,pv5,pv13,pv3181], .c 3, .c 5, .p pv2 [pv2,pv3,pv43,pv59,pv163], .c 3, .c 19,
  .c 11, .c 3, .c 41, .c 7, .c 3, .c 809, .c 5, .c 3, .c 31, .c 29, .c 3, .c 5, .c 23, .c 3,
  .p pv2 [pv2,pv5,pv7,pv37,pv479], .c 107, .c 3, .c 7, .c 19, .c 3, .p pv3 [pv2,pv13,pv79,pv151],
  .c 5, .c 3, .p pv13 [pv2,pv41,pv30259], .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv45949], .c 3,
  .c 727, .p pv2 [pv2,pv3,pv17,pv12163], .c 3, .c 37, .c 11, .c 3, .c 23, .c 5, .c 3, .c 7, .c 13,
  .c 3, .c 5, .p pv11 [pv2,pv3,pv7,pv109,pv271], .c 3, .c 11, .c 7, .c 3, .c 367, .c 139, .c 3,
  .p pv2 [pv2,pv11,pv56393], .c 5, .c 3, .c 503, .c 53, .c 3, .c 5, .p pv2 [pv2,pv3,pv413551],
  .c 3, .c 7, .c 379, .c 3, .p pv2 [pv2,pv620329], .p pv11 [pv2,pv3,pv7,pv47,pv419], .c 3, .c 13,
  .c 5, .c 3, .c 181, .c 37, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv124067], .c 19, .c 3,
  .c 11, .c 13, .c 3, .c 7, .c 5, .c 3, .c 929, .c 41, .c 3, .c 5, .c 7, .c 3, .c 17, .c 103,
  .c 3, .c 853, .c 71, .c 3, .c 151, .c 5, .c 3, .p pv3 [pv2,pv7,pv13,pv17,pv401], .c 11, .c 3,
  .c 5, .c 347, .c 3, .c 13, .c 409, .c 3, .c 53, .c 7,
]
private theorem h0302c28 : checkBlock 2481155 128 b0302c28 = true := by
  decide +kernel

private def b0302c29 : List Row := [
  .c 3, .c 11, .c 5, .c 3, .c 19, .p pv2 [pv2,pv3,pv5,pv41357], .c 3, .c 5, .c 13, .c 3, .c 389,
  .p pv7 [pv2,pv3,pv103393], .c 3, .c 7, .c 17, .c 3, .c 29, .c 5, .c 3, .p pv3 [pv2,pv310181],
  .c 7, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv53,pv2341], .c 1217, .c 3, .c 1223, .c 79,
  .c 3, .c 17, .c 5, .c 3, .c 7, .c 59, .c 3, .c 5, .c 43, .c 3,
  .p pv11 [pv2,pv5,pv11,pv17,pv1327], .c 7, .c 3, .p pv3 [pv2,pv310187],
  .p pv13 [pv2,pv3,pv89,pv1549], .c 3, .p pv5 [pv2,pv1240751], .c 5, .c 3, .p pv2 [pv2,pv620377],
  .c 281, .c 3, .c 5, .p pv2 [pv2,pv3,pv23,pv37], .c 3, .c 7, .c 11, .c 3, .c 499, .c 601, .c 3,
  .c 19, .c 5, .c 3, .c 23, .c 17, .c 3, .c 5, .c 271, .c 3, .c 97, .c 37, .c 3, .c 13, .c 29,
  .c 3, .c 7, .c 5, .c 3, .c 373, .c 19, .c 3, .c 5, .c 7, .c 3, .c 31, .c 13, .c 3, .c 89, .c 11,
  .c 3, .c 113, .c 5, .c 3, .c 59, .p pv41 [pv2,pv3,pv5,pv11,pv47], .c 3, .c 5, .c 41, .c 3,
  .c 11, .c 67, .c 3, .c 29, .c 7, .c 3, .c 449, .c 5, .c 3, .p pv2 [pv2,pv19,pv32653], .c 23,
  .c 3, .c 5, .c 251, .c 3, .p pv3 [pv2,pv5,pv7,pv8863], .c 17, .c 3, .c 7,
  .p pv17 [pv2,pv3,pv13,pv41,pv97], .c 3, .p pv2 [pv2,pv620413], .c 5, .c 3, .c 43, .c 7, .c 3,
  .c 5,
]
private theorem h0302c29 : checkBlock 2481411 128 b0302c29 = true := by
  decide +kernel

private def b0302c30 : List Row := [
  .c 439, .c 3, .c 101, .c 229, .c 3, .c 11, .c 1061, .c 3, .c 233, .c 5, .c 3, .c 7, .c 181,
  .c 3, .c 5, .p pv19 [pv2,pv3,pv7,pv1231], .c 3, .c 37, .c 7, .c 3, .c 127,
  .p pv2 [pv2,pv3,pv73,pv2833], .c 3, .c 13, .c 5, .c 3, .p pv7 [pv2,pv1240859], .c 11, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv13,pv31817], .c 3, .c 7, .c 29, .c 3, .c 419, .c 13, .c 3, .c 11, .c 5,
  .c 3, .p pv2 [pv2,pv620437], .c 1531, .c 3, .c 5, .p pv5 [pv2,pv3,pv206813], .c 3, .c 19,
  .c 1249, .c 3, .c 31, .c 23, .c 3, .c 7, .c 5, .c 3, .c 17, .c 73, .c 3, .c 5, .c 7, .c 3,
  .c 13, .c 317, .c 3, .p pv2 [pv2,pv17,pv36497], .c 19, .c 3, .c 1487, .c 5, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv5,pv82727], .c 3, .c 5, .c 13, .c 3, .c 109, .p pv5 [pv2,pv3,pv7,pv19697],
  .c 3, .c 827, .c 7, .c 3, .p pv3 [pv2,pv310229], .c 5, .c 3, .p pv23 [pv2,pv23,pv163,pv331],
  .p pv7 [pv2,pv3,pv5,pv383], .c 3, .c 5, .c 17, .c 3, .p pv7 [pv2,pv5,pv7,pv1013], .c 11, .c 3,
  .c 7, .p pv3 [pv2,pv3,pv173,pv797], .c 3, .p pv5 [pv2,pv1240931], .c 5, .c 3, .c 13, .c 7, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv71,pv971], .c 3, .c 17, .c 821, .c 3, .p pv5 [pv2,pv11,pv37,pv3049],
  .p pv19 [pv2,pv3,pv103,pv251], .c 3, .c 149, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv8273],
  .c 3, .c 5, .c 23, .c 3, .p pv23 [pv2,pv5,pv283,pv877], .c 7, .c 3, .c 43, .c 11, .c 3,
]
private theorem h0302c30 : checkBlock 2481667 128 b0302c30 = true := by
  decide +kernel

private def b0302c31 : List Row := [
  .c 37, .c 5, .c 3, .c 47, .c 263, .c 3, .c 5, .c 53, .c 3, .c 7, .c 79, .c 3, .c 13, .c 17,
  .c 3, .c 23, .c 5, .c 3, .p pv7 [pv2,pv1240979], .c 127, .c 3, .c 5, .c 457, .c 3,
  .p pv2 [pv2,pv5,pv19,pv13063], .c 13, .c 3, .p pv3 [pv2,pv7,pv23,pv41,pv47],
  .p pv11 [pv2,pv3,pv569,pv727], .c 3, .c 7, .c 5, .c 3, .c 19, .c 103, .c 3, .c 5, .c 7, .c 3,
  .c 163, .c 43, .c 3, .c 11, .p pv7 [pv2,pv3,pv19,pv5443], .c 3, .c 157, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv11,pv71,pv227], .c 367, .c 3, .c 5, .c 19, .c 3, .c 173,
  .p pv13 [pv2,pv3,pv7,pv83,pv89], .c 3, .c 613, .c 7, .c 3, .c 53, .c 5, .c 3,
  .p pv3 [pv2,pv19391], .c 11, .c 3, .c 5, .c 131, .c 3, .p pv2 [pv2,pv5,pv7,pv17729], .c 269,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv17,pv23], .c 3, .c 11, .c 5, .c 3, .c 107, .c 7, .c 3, .c 5,
  .c 947, .c 3, .c 23, .p pv2 [pv2,pv3,pv68947], .c 3, .p pv3 [pv2,pv53,pv2927], .c 41, .c 3,
  .c 13, .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv29,pv317], .c 3, .c 5, .c 11, .c 3, .c 89, .c 7,
  .c 3, .c 199, .c 13, .c 3, .c 97, .c 5, .c 3, .c 11, .c 19, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv73,pv1889], .c 3, .c 7, .c 17, .c 3, .p pv2 [pv2,pv419,pv1481], .c 1321, .c 3,
  .c 1489, .c 5, .c 3, .c 331, .c 1039, .c 3, .c 5, .p pv5 [pv2,pv3,pv101],
]
private theorem h0302c31 : checkBlock 2481923 128 b0302c31 = true := by
  decide +kernel

def rows0302 : List Row :=
  b0302c00 ++ b0302c01 ++ b0302c02 ++ b0302c03 ++ b0302c04 ++ b0302c05 ++ b0302c06 ++ b0302c07 ++
  b0302c08 ++ b0302c09 ++ b0302c10 ++ b0302c11 ++ b0302c12 ++ b0302c13 ++ b0302c14 ++ b0302c15 ++
  b0302c16 ++ b0302c17 ++ b0302c18 ++ b0302c19 ++ b0302c20 ++ b0302c21 ++ b0302c22 ++ b0302c23 ++
  b0302c24 ++ b0302c25 ++ b0302c26 ++ b0302c27 ++ b0302c28 ++ b0302c29 ++ b0302c30 ++ b0302c31

attribute [local irreducible] checkBlock checkRows checkPrime

theorem checked0302 : checkBlock 2473987 4096 rows0302 = true :=
  checkBlock_append h0302c00 (
    checkBlock_append h0302c01 (
    checkBlock_append h0302c02 (
    checkBlock_append h0302c03 (
    checkBlock_append h0302c04 (
    checkBlock_append h0302c05 (
    checkBlock_append h0302c06 (
    checkBlock_append h0302c07 (
    checkBlock_append h0302c08 (
    checkBlock_append h0302c09 (
    checkBlock_append h0302c10 (
    checkBlock_append h0302c11 (
    checkBlock_append h0302c12 (
    checkBlock_append h0302c13 (
    checkBlock_append h0302c14 (
    checkBlock_append h0302c15 (
    checkBlock_append h0302c16 (
    checkBlock_append h0302c17 (
    checkBlock_append h0302c18 (
    checkBlock_append h0302c19 (
    checkBlock_append h0302c20 (
    checkBlock_append h0302c21 (
    checkBlock_append h0302c22 (
    checkBlock_append h0302c23 (
    checkBlock_append h0302c24 (
    checkBlock_append h0302c25 (
    checkBlock_append h0302c26 (
    checkBlock_append h0302c27 (
    checkBlock_append h0302c28 (
    checkBlock_append h0302c29 (
    checkBlock_append h0302c30 (
    h0302c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
