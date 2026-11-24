/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0102
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0102.checked0102
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table016
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table019
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table024
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table032
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table049
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table050
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table101
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table102

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0102c00 : List Row := [
  .c 3, .c 449, .p pv17 [pv2,pv3,pv5,pv7,pv23,pv173], .c 3, .c 5, .c 7, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv139267], .c 3, .p pv5 [pv2,pv29,pv14407], .p pv13 [pv2,pv3,pv37,pv941], .c 3,
  .c 23, .c 5, .c 3, .c 43, .c 41, .c 3, .c 5, .c 13, .c 3, .c 73, .p pv11 [pv2,pv3,pv7,pv829],
  .c 3, .c 11, .c 7, .c 3, .p pv2 [pv2,pv417821], .c 5, .c 3, .c 131, .c 53, .c 3, .c 5, .c 311,
  .c 3, .p pv2 [pv2,pv5,pv7,pv47,pv127], .p pv3 [pv2,pv3,pv41,pv43,pv79], .c 3, .c 7, .c 17, .c 3,
  .p pv3 [pv2,pv104459], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv2731], .c 3,
  .c 67, .c 29, .c 3, .c 809, .c 283, .c 3, .c 11, .c 5, .c 3, .c 7, .c 157, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv9949], .c 3, .p pv3 [pv2,pv5,pv17,pv1229], .c 7, .c 3, .c 83, .c 31, .c 3,
  .p pv2 [pv2,pv208933], .c 5, .c 3, .p pv2 [pv2,pv417869], .c 71, .c 3, .c 5, .c 11, .c 3, .c 7,
  .c 19, .c 3, .c 13, .p pv3 [pv2,pv3,pv7,pv11,pv67], .c 3, .c 173, .c 5, .c 3, .c 11, .c 17,
  .c 3, .c 5, .c 73, .c 3, .c 877, .c 13, .c 3, .c 127, .p pv2 [pv2,pv3,pv17,pv241], .c 3, .c 7,
  .c 5, .c 3, .c 89, .c 47, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv19,pv53,pv83], .c 11, .c 3,
  .p pv3 [pv2,pv191,pv547], .p pv2 [pv2,pv3,pv139303], .c 3, .p pv5 [pv2,pv13,pv17,pv31,pv61],
  .c 5, .c 3, .c 19, .p pv3 [pv2,pv3,pv5,pv37,pv251], .c 3, .c 5, .c 137, .c 3,
  .p pv3 [pv2,pv5,pv653],
]
private theorem h0102c00 : checkBlock 835587 128 b0102c00 = true := by
  decide +kernel

private def b0102c01 : List Row := [
  .c 23, .c 3, .p pv5 [pv2,pv11,pv37993], .c 7, .c 3, .c 31, .c 5, .c 3,
  .p pv2 [pv2,pv181,pv2309], .c 13, .c 3, .c 5, .c 19, .c 3, .c 197, .c 17, .c 3, .c 7, .c 11,
  .c 3, .c 61, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv29,pv1201], .c 3, .c 11,
  .c 769, .c 3, .c 17, .p pv2 [pv2,pv3,pv41,pv1699], .c 3, .c 13, .c 5, .c 3, .c 7, .c 109, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv7,pv13,pv1531], .c 3, .p pv2 [pv2,pv5,pv179,pv467], .c 7, .c 3,
  .p pv3 [pv2,pv151,pv173], .c 13, .c 3, .c 19, .c 5, .c 3, .c 41, .p pv3 [pv2,pv3,pv5,pv5573],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv2111], .c 3, .c 7, .c 43, .c 3, .c 11, .c 53, .c 3,
  .p pv2 [pv2,pv208993], .c 5, .c 3, .p pv2 [pv2,pv11,pv13,pv37,pv79], .c 19, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv277,pv503], .c 3, .c 13, .p pv5 [pv2,pv3,pv17,pv683], .c 3,
  .p pv2 [pv2,pv7,pv73,pv409], .c 199, .c 3, .c 7, .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .c 7,
  .c 3, .c 257, .c 313, .c 3, .c 23, .c 241, .c 3, .c 11, .c 5, .c 3, .c 31, .c 29, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv46447], .c 3, .c 103, .c 797, .c 3, .c 19, .c 7, .c 3, .p pv5 [pv2,pv418031],
  .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv29,pv31], .c 3, .c 5, .c 11, .c 3, .c 251, .c 47, .c 3,
  .c 7, .c 37, .c 3, .c 67, .c 5, .c 3,
]
private theorem h0102c01 : checkBlock 835843 128 b0102c01 = true := by
  decide +kernel

private def b0102c02 : List Row := [
  .c 11, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv331,pv421], .c 3, .c 17, .c 41, .c 3,
  .p pv2 [pv2,pv209029], .c 23, .c 3, .c 433, .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv47,pv593],
  .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv79], .c 3, .c 811, .c 7, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv59,pv1181], .c 3, .p pv3 [pv2,pv19,pv5501], .c 5, .c 3, .p pv7 [pv2,pv418079],
  .p pv23 [pv2,pv3,pv5,pv13,pv67], .c 3, .c 5, .c 71, .c 3, .c 7, .c 13, .c 3, .c 47, .c 17, .c 3,
  .p pv5 [pv2,pv157,pv2663], .c 5, .c 3, .p pv2 [pv2,pv23,pv61,pv149],
  .p pv11 [pv2,pv3,pv5,pv19,pv163], .c 3, .c 5, .c 719, .c 3, .c 883, .p pv3 [pv2,pv3,pv139367],
  .c 3, .c 59, .c 11, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv418109], .c 43, .c 3, .c 5, .c 7,
  .c 3, .c 11, .p pv7 [pv2,pv3,pv34843], .c 3, .c 37, .p pv3 [pv2,pv3,pv13,pv71,pv151], .c 3,
  .p pv2 [pv2,pv11,pv38011], .c 5, .c 3, .c 61, .c 13, .c 3, .c 5, .c 23, .c 3, .c 239, .c 277,
  .c 3, .p pv2 [pv2,pv19,pv59,pv373], .c 7, .c 3, .c 29, .c 5, .c 3, .c 311, .c 17, .c 3, .c 5,
  .c 31, .c 3, .p pv17 [pv2,pv5,pv7,pv13,pv919], .c 701, .c 3, .c 7, .p pv2 [pv2,pv3,pv17,pv911],
  .c 3, .c 13, .c 5, .c 3, .c 71, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv1787], .c 3, .c 269,
  .c 19, .c 3, .p pv5 [pv2,pv23,pv18181], .c 13, .c 3, .c 89, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv19913], .c 3, .p pv19 [pv2,pv5,pv43,pv389], .c 7,
]
private theorem h0102c02 : checkBlock 836099 128 b0102c02 = true := by
  decide +kernel

private def b0102c03 : List Row := [
  .c 3, .c 109, .c 41, .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv13,pv4021], .c 61, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv34849], .c 3, .c 7, .c 17, .c 3, .p pv2 [pv2,pv541,pv773], .c 29, .c 3, .c 43,
  .c 5, .c 3, .c 19, .c 181, .c 3, .c 5, .c 11, .c 3, .c 31, .p pv2 [pv2,pv3,pv47,pv1483], .c 3,
  .c 17, .c 107, .c 3, .c 7, .c 5, .c 3, .c 11, .c 97, .c 3, .c 5, .c 7, .c 3, .c 23, .c 59, .c 3,
  .c 29, .p pv7 [pv2,pv3,pv8713], .c 3, .c 379, .c 5, .c 3, .c 13, .c 829, .c 3, .c 5, .c 179,
  .c 3, .p pv41 [pv2,pv5,pv233,pv359], .c 11, .c 3, .p pv2 [pv2,pv29,pv7211], .c 7, .c 3, .c 839,
  .c 5, .c 3, .c 503, .p pv13 [pv2,pv3,pv5,pv27883], .c 3, .c 5, .p pv17 [pv2,pv3,pv37,pv157],
  .c 3, .p pv2 [pv2,pv5,pv7,pv239], .c 167, .c 3, .c 7, .p pv2 [pv2,pv3,pv69709], .c 3, .c 19,
  .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 421, .c 3, .c 79, .c 23, .c 3, .c 13, .c 11, .c 3,
  .c 643, .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 83, .c 3, .c 11, .c 7, .c 3,
  .p pv5 [pv2,pv31,pv103,pv131], .p pv13 [pv2,pv3,pv1291], .c 3, .p pv2 [pv2,pv11,pv19013], .c 5,
  .c 3, .c 23, .c 787, .c 3, .c 5, .c 17, .c 3, .c 7, .c 71, .c 3, .c 31, .c 821, .c 3, .c 263,
  .c 5, .c 3, .p pv3 [pv2,pv19,pv43],
]
private theorem h0102c03 : checkBlock 836355 128 b0102c03 = true := by
  decide +kernel

private def b0102c04 : List Row := [
  .p pv3 [pv2,pv3,pv5,pv79,pv353], .c 3, .c 5, .c 347, .c 3, .c 17, .p pv3 [pv2,pv3,pv15493],
  .c 3, .c 11, .c 67, .c 3, .c 7, .c 5, .c 3, .c 373, .c 13, .c 3, .c 5, .c 7, .c 3, .c 43, .c 73,
  .c 3, .p pv3 [pv2,pv52291], .c 31, .c 3, .p pv5 [pv2,pv418331], .c 5, .c 3, .c 103, .c 11, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv61,pv127], .c 3, .c 37, .p pv7 [pv2,pv3,pv7,pv11,pv1811], .c 3, .c 41,
  .c 7, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv418349], .p pv7 [pv2,pv3,pv5,pv2789], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv13,pv17,pv631], .c 3, .c 53, .p pv5 [pv2,pv3,pv11621], .c 3, .c 7, .c 13,
  .c 3, .c 17, .c 5, .c 3, .p pv3 [pv2,pv41,pv2551], .c 7, .c 3, .c 5, .c 11, .c 3, .c 19, .c 419,
  .c 3, .p pv2 [pv2,pv418373], .p pv2 [pv2,pv3,pv11,pv2113], .c 3, .p pv3 [pv2,pv7,pv31,pv241],
  .c 5, .c 3, .c 7, .p pv47 [pv2,pv3,pv5,pv19,pv367], .c 3, .c 5, .c 457, .c 3, .c 13, .c 7, .c 3,
  .c 727, .c 19, .c 3, .c 31, .c 5, .c 3, .p pv2 [pv2,pv47,pv4451], .c 17, .c 3, .c 5, .c 13,
  .c 3, .c 7, .c 11, .c 3, .p pv5 [pv2,pv71,pv83], .c 23, .c 3, .c 479, .c 5, .c 3, .c 97,
  .p pv7 [pv2,pv3,pv5,pv4649], .c 3, .c 5, .c 443, .c 3, .c 283, .p pv5 [pv2,pv3,pv23,pv379],
  .c 3, .c 167, .p pv3 [pv2,pv3,pv15497], .c 3, .c 7, .c 5, .c 3, .c 13, .c 41, .c 3, .c 5, .c 7,
  .c 3, .p pv2 [pv2,pv5,pv41843], .p pv11 [pv2,pv3,pv13,pv10729], .c 3,
]
private theorem h0102c04 : checkBlock 836611 128 b0102c04 = true := by
  decide +kernel

private def b0102c05 : List Row := [
  .c 89, .c 11, .c 3, .p pv3 [pv2,pv73,pv1433], .c 5, .c 3, .p pv17 [pv2,pv7,pv23,pv113],
  .p pv13 [pv2,pv3,pv5,pv11,pv317], .c 3, .c 5, .c 401, .c 3, .c 11, .c 17, .c 3, .c 67, .c 7,
  .c 3, .c 37, .c 5, .c 3, .c 43, .c 29, .c 3, .c 5, .p pv2 [pv2,pv3,pv97,pv719], .c 3,
  .p pv3 [pv2,pv5,pv7,pv61], .c 53, .c 3, .c 7, .c 47, .c 3, .c 41, .c 5, .c 3,
  .p pv2 [pv2,pv31,pv13499], .c 7, .c 3, .c 5, .c 23, .c 3, .p pv17 [pv2,pv5,pv19,pv881], .c 13,
  .c 3, .c 11, .c 131, .c 3, .c 353, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv23,pv1213], .c 3,
  .c 5, .c 37, .c 3, .c 61, .c 7, .c 3, .c 101, .c 433, .c 3, .c 23, .c 5, .c 3, .c 569, .c 11,
  .c 3, .c 5, .c 19, .c 3, .c 7, .c 97, .c 3, .p pv3 [pv2,pv23,pv4549], .c 71, .c 3, .c 11, .c 5,
  .c 3, .c 17, .c 13, .c 3, .c 5, .c 211, .c 3, .c 193, .p pv2 [pv2,pv3,pv61,pv2287], .c 3,
  .p pv23 [pv2,pv7,pv17,pv3517], .c 257, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv139,pv3011],
  .c 107, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv13,pv47,pv137], .p pv7 [pv2,pv3,pv5813], .c 3,
  .p pv2 [pv2,pv209269], .p pv3 [pv2,pv3,pv11,pv1153], .c 3, .c 13, .c 5, .c 3, .c 11, .c 73,
  .c 3, .c 5, .c 17, .c 3, .c 293, .c 61, .c 3, .p pv2 [pv2,pv418553], .c 7, .c 3,
  .p pv3 [pv2,pv104639], .c 5, .c 3, .c 271, .c 19,
]
private theorem h0102c05 : checkBlock 836867 128 b0102c05 = true := by
  decide +kernel

private def b0102c06 : List Row := [
  .c 3, .c 5, .c 367, .c 3, .c 17, .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv41,pv83], .c 3, .c 29,
  .c 5, .c 3, .p pv2 [pv2,pv13,pv17,pv947], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv69763], .c 3,
  .c 13, .c 79, .c 3, .c 43, .c 233, .c 3, .c 439, .c 5, .c 3, .c 7, .c 563, .c 3, .c 5, .c 13,
  .c 3, .p pv11 [pv2,pv5,pv83719], .c 7, .c 3, .c 19, .c 11, .c 3, .p pv2 [pv2,pv418601], .c 5,
  .c 3, .c 911, .c 47, .c 3, .c 5, .c 31, .c 3, .c 7, .c 23, .c 3, .c 577, .c 109, .c 3, .c 17,
  .c 5, .c 3, .c 13, .c 53, .c 3, .c 5, .c 521, .c 3, .c 349, .c 43, .c 3,
  .p pv3 [pv2,pv7,pv14951], .c 29, .c 3, .c 7, .c 5, .c 3, .c 23, .p pv3 [pv2,pv3,pv5,pv7,pv443],
  .c 3, .c 5, .c 7, .c 3, .c 157, .p pv2 [pv2,pv3,pv139547], .c 3, .c 11, .c 857, .c 3,
  .p pv2 [pv2,pv19,pv23,pv479], .c 5, .c 3, .c 67, .c 17, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv181,pv257], .c 3, .c 19, .p pv5 [pv2,pv3,pv7,pv89], .c 3, .c 13, .c 7, .c 3,
  .c 523, .c 5, .c 3, .c 709, .c 11, .c 3, .c 5, .c 631, .c 3, .c 31, .c 13, .c 3, .c 7, .c 19,
  .c 3, .c 11, .c 5, .c 3, .p pv17 [pv2,pv613,pv683], .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv67,pv2083], .c 3, .c 277, .p pv5 [pv2,pv3,pv31,pv2251], .c 3,
  .p pv3 [pv2,pv3271],
]
private theorem h0102c06 : checkBlock 837123 128 b0102c06 = true := by
  decide +kernel

private def b0102c07 : List Row := [
  .p pv2 [pv2,pv3,pv1723], .c 3, .c 73, .c 5, .c 3, .c 7, .c 101, .c 3, .c 5, .c 11, .c 3, .c 89,
  .c 7, .c 3, .c 23, .p pv7 [pv2,pv3,pv11,pv13,pv61], .c 3, .p pv2 [pv2,pv209353], .c 5, .c 3,
  .c 11, .c 13, .c 3, .c 5, .c 193, .c 3, .c 7, .c 29, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv7,pv127,pv157], .c 3, .c 113, .c 5, .c 3, .c 677, .p pv2 [pv2,pv3,pv5,pv1861],
  .c 3, .c 5, .c 547, .c 3, .p pv2 [pv2,pv5,pv13,pv3221], .c 11, .c 3,
  .p pv2 [pv2,pv7,pv41,pv1459], .c 61, .c 3, .c 7, .c 5, .c 3, .c 79, .c 137, .c 3, .c 5, .c 7,
  .c 3, .c 29, .c 47, .c 3, .p pv3 [pv2,pv11,pv31,pv307], .c 13, .c 3, .p pv5 [pv2,pv418751],
  .c 5, .c 3, .p pv2 [pv2,pv7,pv4273], .c 43, .c 3, .c 5, .c 389, .c 3,
  .p pv3 [pv2,pv5,pv19,pv29], .c 311, .c 3, .c 31, .c 7, .c 3, .p pv2 [pv2,pv37,pv5659], .c 5,
  .c 3, .c 17, .c 179, .c 3, .c 5, .c 359, .c 3, .c 11, .c 83, .c 3, .c 7, .c 53, .c 3, .c 257,
  .c 5, .c 3, .c 37, .c 7, .c 3, .c 5, .c 13, .c 3, .c 419, .p pv5 [pv2,pv3,pv139597], .c 3,
  .c 47, .c 31, .c 3, .c 101, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv349], .c 3, .c 5, .c 17,
  .c 3, .p pv2 [pv2,pv5,pv83761], .c 7, .c 3, .c 11, .p pv2 [pv2,pv3,pv137,pv1019], .c 3, .c 59,
  .c 5, .c 3, .c 13, .p pv11 [pv2,pv3,pv5,pv41,pv227], .c 3,
]
private theorem h0102c07 : checkBlock 837379 128 b0102c07 = true := by
  decide +kernel

private def b0102c08 : List Row := [
  .c 5, .c 23, .c 3, .c 7, .c 37, .c 3, .c 797, .c 587, .c 3, .c 19, .c 5, .c 3,
  .p pv2 [pv2,pv17,pv71,pv347], .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv173,pv269], .c 3, .c 41,
  .p pv13 [pv2,pv3,pv11,pv19,pv167], .c 3, .p pv2 [pv2,pv7,pv29917],
  .p pv29 [pv2,pv3,pv149,pv937], .c 3, .c 7, .c 5, .c 3, .c 401, .c 19, .c 3, .c 5, .c 7, .c 3,
  .c 67, .c 107, .c 3, .c 13, .c 17, .c 3, .c 31, .c 5, .c 3, .c 83,
  .p pv7 [pv2,pv3,pv5,pv13,pv179], .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv83773], .c 13, .c 3,
  .p pv3 [pv2,pv104717], .c 7, .c 3, .c 17, .c 5, .c 3, .c 11, .c 827, .c 3, .c 5, .c 89, .c 3,
  .c 331, .c 811, .c 3, .c 7, .c 43, .c 3, .p pv2 [pv2,pv13,pv16111], .c 5, .c 3,
  .p pv2 [pv2,pv418889], .c 7, .c 3, .c 5, .c 641, .c 3, .c 37, .c 11, .c 3,
  .p pv2 [pv2,pv209449], .c 653, .c 3, .c 307, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv4987], .c 3, .c 23, .c 7, .c 3, .c 149, .c 643, .c 3,
  .p pv3 [pv2,pv104729], .c 5, .c 3, .c 29, .c 197, .c 3, .c 5, .p pv3 [pv2,pv3,pv89,pv523], .c 3,
  .c 7, .p pv2 [pv2,pv3,pv69821], .c 3, .c 227, .c 11, .c 3, .c 13, .c 5, .c 3, .c 47, .c 71,
  .c 3, .c 5, .c 53, .c 3, .c 11, .c 109, .c 3, .p pv5 [pv2,pv7,pv97,pv617], .c 13,
]
private theorem h0102c08 : checkBlock 837635 128 b0102c08 = true := by
  decide +kernel

private def b0102c09 : List Row := [
  .c 3, .c 7, .c 5, .c 3, .c 31, .c 313, .c 3, .c 5, .c 7, .c 3, .c 229, .c 17, .c 3, .c 41,
  .c 19, .c 3, .p pv2 [pv2,pv418961], .c 5, .c 3, .p pv3 [pv2,pv7,pv13,pv1151],
  .p pv31 [pv2,pv3,pv5,pv17,pv31,pv53], .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv23], .c 3, .c 13,
  .p pv7 [pv2,pv3,pv7,pv71,pv281], .c 3, .c 11, .c 7, .c 3, .c 79, .c 5, .c 3, .c 23, .c 31, .c 3,
  .c 5, .c 13, .c 3, .c 613, .c 863, .c 3, .c 7, .p pv7 [pv2,pv3,pv139663], .c 3, .c 53, .c 5,
  .c 3, .c 199, .c 7, .c 3, .c 5, .c 101, .c 3, .c 599, .p pv2 [pv2,pv3,pv11,pv12697], .c 3,
  .c 131, .c 541, .c 3, .c 11, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv13967], .c 3, .c 5, .c 43,
  .c 3, .c 139, .c 7, .c 3, .p pv3 [pv2,pv53,pv59,pv67], .p pv11 [pv2,pv3,pv197,pv709], .c 3,
  .p pv2 [pv2,pv29,pv14449], .c 5, .c 3, .c 17, .c 23, .c 3, .c 5, .c 11, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv46559], .c 3, .c 397, .p pv13 [pv2,pv3,pv7,pv11,pv907], .c 3, .c 127, .c 5,
  .c 3, .c 11, .c 41, .c 3, .c 5, .c 37, .c 3, .p pv2 [pv2,pv5,pv11,pv19,pv401],
  .p pv5 [pv2,pv3,pv211,pv331], .c 3, .c 13, .p pv2 [pv2,pv3,pv101,pv461], .c 3, .c 7, .c 5, .c 3,
  .c 19, .c 79, .c 3, .c 5, .c 7, .c 3, .c 113, .c 11, .c 3, .c 487, .c 29, .c 3,
  .p pv2 [pv2,pv209533], .c 5, .c 3, .p pv2 [pv2,pv7,pv131,pv457],
  .p pv2 [pv2,pv3,pv5,pv61,pv229], .c 3, .c 5,
]
private theorem h0102c09 : checkBlock 837891 128 b0102c09 = true := by
  decide +kernel

private def b0102c10 : List Row := [
  .c 19, .c 3, .c 17, .p pv5 [pv2,pv3,pv7,pv1663], .c 3, .p pv2 [pv2,pv11,pv43,pv443], .c 7, .c 3,
  .c 41, .c 5, .c 3, .p pv3 [pv2,pv17,pv6163], .p pv3 [pv2,pv3,pv5,pv67,pv139], .c 3, .c 5, .c 97,
  .c 3, .c 263, .c 691, .c 3, .c 7, .c 11, .c 3, .p pv3 [pv2,pv52387], .c 5, .c 3, .c 43, .c 7,
  .c 3, .c 5, .p pv13 [pv2,pv3,pv46567], .c 3, .c 11, .c 59, .c 3, .c 83, .c 17, .c 3, .c 19,
  .c 5, .c 3, .c 7, .c 727, .c 3, .c 5, .c 67, .c 3, .c 821, .c 7, .c 3,
  .p pv5 [pv2,pv283,pv1481], .p pv7 [pv2,pv3,pv53,pv659], .c 3, .c 13, .c 5, .c 3, .c 73, .c 19,
  .c 3, .c 5, .c 607, .c 3, .c 7, .c 293, .c 3, .c 11, .c 13, .c 3, .c 449, .c 5, .c 3, .c 521,
  .c 89, .c 3, .c 5, .c 71, .c 3, .c 53, .c 29, .c 3, .c 563, .c 37, .c 3, .c 7, .c 5, .c 3,
  .c 109, .c 11, .c 3, .c 5, .c 7, .c 3, .c 13, .c 31, .c 3, .c 19, .c 47, .c 3, .c 11, .c 5,
  .c 3, .p pv2 [pv2,pv7,pv79,pv379], .p pv3 [pv2,pv3,pv5,pv23], .c 3, .c 5, .c 13, .c 3, .c 29,
  .p pv2 [pv2,pv3,pv7,pv19961], .c 3, .p pv5 [pv2,pv419183], .c 7, .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv419189], .c 577, .c 3, .c 5, .c 11, .c 3, .p pv7 [pv2,pv5,pv7,pv29,pv59],
  .p pv7 [pv2,pv3,pv181,pv193], .c 3, .c 7, .p pv3 [pv2,pv3,pv11,pv12703], .c 3,
]
private theorem h0102c10 : checkBlock 838147 128 b0102c10 = true := by
  decide +kernel

private def b0102c11 : List Row := [
  .p pv2 [pv2,pv419201], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 307, .c 3,
  .p pv2 [pv2,pv5,pv11,pv37,pv103], .c 17, .c 3, .c 79, .p pv17 [pv2,pv3,pv109,pv641], .c 3,
  .c 47, .c 5, .c 3, .c 7, .p pv31 [pv2,pv3,pv5,pv17,pv137], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv19963], .c 3, .c 19, .c 7, .c 3, .c 17, .p pv2 [pv2,pv3,pv15527], .c 3,
  .p pv5 [pv2,pv419231], .c 5, .c 3, .c 89, .p pv3 [pv2,pv3,pv5,pv19,pv1471], .c 3, .c 5, .c 29,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv139747], .c 3, .c 13, .c 19, .c 3, .c 463, .c 5, .c 3, .c 853,
  .c 503, .c 3, .c 5, .c 167, .c 3, .c 23, .c 13, .c 3, .p pv3 [pv2,pv7,pv29947], .c 11, .c 3,
  .c 7, .c 5, .c 3, .c 283, .c 37, .c 3, .c 5, .c 7, .c 3, .c 11, .c 43, .c 3,
  .p pv2 [pv2,pv19,pv22067], .c 83, .c 3, .p pv3 [pv2,pv11,pv13,pv733], .c 5, .c 3, .c 17,
  .p pv7 [pv2,pv3,pv5,pv1747], .c 3, .c 5, .c 59, .c 3, .p pv2 [pv2,pv5,pv83857], .c 41, .c 3,
  .c 137, .c 7, .c 3, .p pv5 [pv2,pv419291], .c 5, .c 3, .p pv2 [pv2,pv209647], .c 13, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv6353], .c 3, .p pv3 [pv2,pv5,pv7,pv599], .c 19, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv17471], .c 3, .p pv2 [pv2,pv31,pv6763], .c 5, .c 3, .c 53, .c 7, .c 3, .c 5,
  .c 17, .c 3, .p pv31 [pv2,pv5,pv13,pv6451], .p pv23 [pv2,pv3,pv83,pv421], .c 3, .c 823, .c 67,
  .c 3, .c 13, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .p pv61 [pv2,pv3,pv7,pv13],
]
private theorem h0102c11 : checkBlock 838403 128 b0102c11 = true := by
  decide +kernel

private def b0102c12 : List Row := [
  .c 3, .c 17, .c 7, .c 3, .p pv2 [pv2,pv107,pv3919], .c 13, .c 3, .c 11, .c 5, .c 3, .c 19,
  .c 191, .c 3, .c 5, .p pv5 [pv2,pv3,pv113,pv1237], .c 3, .c 7, .p pv2 [pv2,pv3,pv23297], .c 3,
  .c 73, .c 347, .c 3, .c 223, .c 5, .c 3, .c 29, .p pv3 [pv2,pv3,pv5,pv9319], .c 3, .c 5, .c 11,
  .c 3, .c 13, .c 71, .c 3, .c 379, .c 17, .c 3, .c 7, .c 5, .c 3, .c 11, .c 23, .c 3, .c 5, .c 7,
  .c 3, .p pv7 [pv2,pv5,pv11,pv61], .c 37, .c 3, .p pv2 [pv2,pv277,pv757], .c 97, .c 3, .c 17,
  .c 5, .c 3, .p pv3 [pv2,pv7,pv7489], .p pv3 [pv2,pv3,pv5,pv73,pv383], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv34949], .c 3, .p pv2 [pv2,pv5,pv17,pv2467], .c 11, .c 3, .c 23, .c 7, .c 3,
  .c 19, .c 5, .c 3, .c 13, .c 43, .c 3, .c 5, .p pv5 [pv2,pv3,pv139801], .c 3, .c 61,
  .p pv2 [pv2,pv3,pv13,pv19,pv283], .c 3, .c 7, .c 41, .c 3, .c 587, .c 5, .c 3, .c 31, .c 7,
  .c 3, .c 5, .p pv11 [pv2,pv3,pv863], .c 3, .c 167, .c 73, .c 3, .c 743, .c 11, .c 3,
  .p pv3 [pv2,pv7,pv29959], .c 5, .c 3, .c 7, .c 397, .c 3, .c 5, .c 751, .c 3, .c 11, .c 7, .c 3,
  .c 13, .c 23, .c 3, .c 29, .c 5, .c 3, .p pv3 [pv2,pv19,pv5519], .c 31, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv17477], .c 3, .c 7, .c 13, .c 3, .c 19, .p pv13 [pv2,pv3,pv7,pv3329], .c 3,
  .p pv3 [pv2,pv29,pv113],
]
private theorem h0102c12 : checkBlock 838659 128 b0102c12 = true := by
  decide +kernel

private def b0102c13 : List Row := [
  .c 5, .c 3, .p pv7 [pv2,pv419459], .c 59, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv19,pv223], .c 3,
  .p pv2 [pv2,pv5,pv43,pv1951], .c 17, .c 3, .c 11, .p pv2 [pv2,pv3,pv37,pv3779], .c 3, .c 7,
  .c 5, .c 3, .p pv2 [pv2,pv11,pv23,pv829], .p pv19 [pv2,pv3,pv5,pv7,pv17,pv47], .c 3, .c 5, .c 7,
  .c 3, .c 163, .p pv2 [pv2,pv3,pv127,pv367], .c 3, .c 17, .p pv7 [pv2,pv3,pv13,pv2689], .c 3,
  .c 43, .c 5, .c 3, .c 769, .c 11, .c 3, .c 5, .c 107, .c 3, .p pv17 [pv2,pv5,pv53,pv1583],
  .p pv5 [pv2,pv3,pv7,pv11,pv227], .c 3, .c 47, .c 7, .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv157,pv167], .c 269, .c 3, .c 5, .c 23, .c 3, .c 19, .c 197, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv29,pv2411], .c 3, .c 13, .c 5, .c 3, .c 59, .c 7, .c 3, .c 5, .c 11, .c 3,
  .p pv13 [pv2,pv5,pv97,pv173], .c 421, .c 3, .c 29, .c 13, .c 3, .c 23, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv9323], .c 3, .c 5, .c 31, .c 3, .c 353, .c 7, .c 3,
  .p pv5 [pv2,pv17,pv23,pv29,pv37], .c 127, .c 3, .c 251, .c 5, .c 3, .c 317, .c 487, .c 3, .c 5,
  .c 151, .c 3, .c 7, .c 11, .c 3, .p pv3 [pv2,pv19,pv61,pv181], .c 491, .c 3, .c 37, .c 5, .c 3,
  .c 239, .p pv2 [pv2,pv3,pv5,pv83,pv337], .c 3, .c 5, .c 13, .c 3, .c 103, .c 139, .c 3, .c 41,
  .c 53, .c 3, .c 7, .c 5, .c 3, .c 647, .p pv17 [pv2,pv3,pv5,pv7,pv37], .c 3, .c 5, .c 7, .c 3,
]
private theorem h0102c13 : checkBlock 838915 128 b0102c13 = true := by
  decide +kernel

private def b0102c14 : List Row := [
  .c 17, .c 19, .c 3, .c 61, .c 11, .c 3, .c 199, .c 5, .c 3, .c 13, .c 109, .c 3, .c 5, .c 37,
  .c 3, .c 11, .p pv2 [pv2,pv3,pv7,pv13,pv29,pv53], .c 3, .p pv5 [pv2,pv419603], .c 7, .c 3,
  .c 83, .c 5, .c 3, .c 227, .p pv13 [pv2,pv3,pv5,pv71,pv197], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv139871], .c 3, .c 29, .c 263, .c 3, .c 7, .c 17, .c 3, .c 859, .c 5, .c 3,
  .c 19, .c 7, .c 3, .c 5, .c 419, .c 3, .p pv2 [pv2,pv5,pv29,pv1447], .c 31, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv19,pv409], .c 3, .c 17, .c 5, .c 3, .c 7, .c 73, .c 3, .c 5, .c 19, .c 3,
  .c 71, .c 7, .c 3, .c 181, .c 61, .c 3, .p pv5 [pv2,pv419651], .c 5, .c 3, .c 67, .c 11, .c 3,
  .c 5, .c 43, .c 3, .c 7, .p pv3 [pv2,pv3,pv11,pv157], .c 3, .p pv5 [pv2,pv47,pv8929], .c 367,
  .c 3, .c 11, .c 5, .c 3, .c 23, .c 17, .c 3, .c 5, .c 29, .c 3, .p pv7 [pv2,pv5,pv16787],
  .p pv5 [pv2,pv3,pv41,pv853], .c 3, .c 193, .c 89, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv239,pv439], .c 13, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv41969], .c 761, .c 3,
  .c 31, .c 311, .c 3, .c 41, .c 5, .c 3, .c 11, .c 19, .c 3, .c 5, .c 683, .c 3, .c 101,
  .p pv5 [pv2,pv3,pv7,pv3331], .c 3, .c 197, .c 7, .c 3, .c 13, .c 5,
]
private theorem h0102c14 : checkBlock 839171 128 b0102c14 = true := by
  decide +kernel

private def b0102c15 : List Row := [
  .c 3, .p pv2 [pv2,pv209857], .c 23, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv5381], .c 3,
  .p pv3 [pv2,pv5,pv7,pv1499], .c 11, .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv59,pv3557], .c 5,
  .c 3, .p pv2 [pv2,pv19,pv22091], .c 7, .c 3, .c 5, .c 47, .c 3, .p pv17 [pv2,pv5,pv127,pv661],
  .p pv7 [pv2,pv3,pv17489], .c 3, .c 17, .c 157, .c 3, .p pv2 [pv2,pv7,pv61,pv983], .c 5, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv5,pv27983], .c 3, .c 5, .p pv17 [pv2,pv3,pv7,pv19,pv263], .c 3, .c 13,
  .c 7, .c 3, .c 503, .c 11, .c 3, .c 757, .c 5, .c 3, .p pv7 [pv2,pv109,pv3851], .c 29, .c 3,
  .c 5, .c 13, .c 3, .c 7, .c 79, .c 3, .c 89, .p pv2 [pv2,pv3,pv7,pv2221], .c 3, .c 61, .c 5,
  .c 3, .c 269, .p pv17 [pv2,pv3,pv5,pv29,pv193], .c 3, .c 5, .c 41, .c 3, .c 47,
  .p pv2 [pv2,pv3,pv17,pv8231], .c 3, .c 37, .c 23, .c 3, .c 7, .c 5, .c 3, .c 13, .c 199, .c 3,
  .c 5, .c 7, .c 3, .c 19, .c 881, .c 3, .c 11, .p pv3 [pv2,pv3,pv41,pv3413], .c 3,
  .p pv2 [pv2,pv419801], .c 5, .c 3, .p pv3 [pv2,pv7,pv11,pv29,pv47],
  .p pv13 [pv2,pv3,pv5,pv19,pv491], .c 3, .c 5, .p pv5 [pv2,pv3,pv4373], .c 3,
  .p pv2 [pv2,pv5,pv41981], .c 373, .c 3, .c 109, .c 7, .c 3, .p pv3 [pv2,pv97,pv541], .c 5, .c 3,
  .c 41, .c 11, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv7,pv2399],
  .p pv5 [pv2,pv3,pv11,pv6361], .c 3, .c 7, .c 181, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv209917], .c 7, .c 3, .c 5, .c 409, .c 3, .c 17,
]
private theorem h0102c15 : checkBlock 839427 128 b0102c15 = true := by
  decide +kernel

private def b0102c16 : List Row := [
  .c 13, .c 3, .c 479, .c 179, .c 3, .p pv2 [pv2,pv7,pv29989], .c 5, .c 3, .c 7, .c 359, .c 3,
  .c 5, .c 11, .c 3, .c 67, .c 7, .c 3, .c 71, .c 73, .c 3, .p pv2 [pv2,pv13,pv32297], .c 5, .c 3,
  .c 11, .p pv3 [pv2,pv3,pv5,pv23,pv1217], .c 3, .c 5, .c 617, .c 3, .c 7, .c 19, .c 3, .c 43,
  .c 17, .c 3, .c 23, .c 5, .c 3, .c 31, .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv17,pv8233], .c 3,
  .p pv2 [pv2,pv5,pv79,pv1063], .c 11, .c 3, .c 829, .c 313, .c 3, .c 7, .c 5, .c 3, .c 37,
  .p pv3 [pv2,pv3,pv5,pv7,pv31,pv43], .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv13,pv17,pv19],
  .c 41, .c 3, .c 439, .p pv7 [pv2,pv3], .c 3, .c 13, .c 5, .c 3, .c 19, .c 31, .c 3, .c 5,
  .c 191, .c 3, .p pv11 [pv2,pv5,pv83983], .c 43, .c 3, .p pv2 [pv2,pv209959], .c 7, .c 3, .c 47,
  .c 5, .c 3, .c 79, .c 17, .c 3, .c 5, .c 19, .c 3, .c 11, .c 37, .c 3, .c 7, .c 29, .c 3,
  .p pv3 [pv2,pv11,pv1193], .c 5, .c 3, .p pv17 [pv2,pv13,pv32303], .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv139981], .c 3, .c 13, .c 89, .c 3, .p pv3 [pv2,pv104987],
  .p pv11 [pv2,pv3,pv29,pv1609], .c 3, .p pv5 [pv2,pv7,pv17,pv3529], .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv27997], .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv10499], .c 7, .c 3,
  .c 11, .c 113, .c 3, .c 19, .c 5, .c 3,
]
private theorem h0102c16 : checkBlock 839683 128 b0102c16 = true := by
  decide +kernel

private def b0102c17 : List Row := [
  .c 163, .c 571, .c 3, .c 5, .c 137, .c 3, .c 7, .c 17, .c 3, .p pv2 [pv2,pv13,pv29,pv557],
  .p pv7 [pv2,pv3,pv7,pv2857], .c 3, .p pv2 [pv2,pv43,pv9767], .c 5, .c 3, .c 13, .c 11, .c 3,
  .c 5, .c 139, .c 3, .p pv3 [pv2,pv5,pv41999], .c 23, .c 3, .c 17, .c 887, .c 3, .c 7, .c 5,
  .c 3, .p pv17 [pv2,pv419999], .c 71, .c 3, .c 5, .c 7, .c 3, .c 37, .c 151, .c 3, .c 101,
  .c 431, .c 3, .p pv5 [pv2,pv263,pv1597], .c 5, .c 3, .c 23, .c 47, .c 3, .c 5, .c 11, .c 3,
  .c 223, .c 29, .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv23,pv397], .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv13,pv359], .c 3, .c 5, .p pv3 [pv2,pv3,pv19,pv7369], .c 3, .c 89, .c 13,
  .c 3, .c 7, .c 449, .c 3, .p pv2 [pv2,pv420041], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 251,
  .c 3, .c 29, .c 11, .c 3, .c 157, .p pv2 [pv2,pv3,pv70009], .c 3, .c 67, .c 5, .c 3, .c 7,
  .c 23, .c 3, .c 5, .c 227, .c 3, .c 31, .c 7, .c 3, .p pv3 [pv2,pv11,pv9547],
  .p pv2 [pv2,pv3,pv13,pv10771], .c 3, .c 71, .c 5, .c 3, .p pv2 [pv2,pv210037], .c 13, .c 3,
  .c 5, .c 17, .c 3, .c 7, .p pv2 [pv2,pv3,pv31,pv4517], .c 3, .c 23, .c 11, .c 3, .c 541, .c 5,
  .c 3, .p pv2 [pv2,pv199,pv2111], .p pv2 [pv2,pv3,pv5,pv11,pv19,pv67], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv15559], .c 3, .c 11, .c 31,
]
private theorem h0102c17 : checkBlock 839939 128 b0102c17 = true := by
  decide +kernel

private def b0102c18 : List Row := [
  .c 3, .p pv2 [pv2,pv7,pv37,pv811], .c 19, .c 3, .c 7, .c 5, .c 3, .c 53, .c 149, .c 3, .c 5,
  .c 7, .c 3, .c 137, .p pv3 [pv2,pv3,pv46679], .c 3, .c 283, .c 13, .c 3, .c 37, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv60017], .p pv41 [pv2,pv3,pv5,pv389], .c 3, .c 5, .c 67, .c 3, .c 773,
  .p pv5 [pv2,pv3,pv7,pv1429], .c 3, .c 11, .c 7, .c 3, .c 43, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv13,pv113], .c 107, .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv1373], .c 3, .c 13,
  .c 823, .c 3, .c 7, .p pv11 [pv2,pv3,pv8753], .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv420149],
  .c 7, .c 3, .c 5, .c 13, .c 3, .c 97, .c 19, .c 3, .c 31, .p pv3 [pv2,pv3,pv140053], .c 3,
  .c 11, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv9337], .c 3, .c 5, .c 59, .c 3,
  .p pv2 [pv2,pv5,pv42017], .c 7, .c 3, .p pv2 [pv2,pv13,pv32321], .c 43, .c 3,
  .p pv3 [pv2,pv26261], .c 5, .c 3, .c 13, .c 17, .c 3, .c 5, .c 11, .c 3, .c 7, .c 521, .c 3,
  .c 41, .c 31, .c 3, .c 181, .c 5, .c 3, .c 11, .c 29, .c 3, .c 5, .c 23, .c 3, .c 643, .c 461,
  .c 3, .c 47, .c 331, .c 3, .c 7, .c 5, .c 3, .c 359, .c 53, .c 3, .c 5, .c 7, .c 3, .c 233,
  .c 11, .c 3, .c 13, .p pv13 [pv2,pv3,pv46691], .c 3, .c 23, .c 5, .c 3, .c 29,
]
private theorem h0102c18 : checkBlock 840195 128 b0102c18 = true := by
  decide +kernel

private def b0102c19 : List Row := [
  .p pv17 [pv2,pv3,pv5,pv13,pv431], .c 3, .c 5, .p pv5 [pv2,pv3,pv1297], .c 3, .c 523, .c 13,
  .c 3, .p pv2 [pv2,pv11,pv23,pv151], .c 7, .c 3, .p pv3 [pv2,pv31,pv3389], .c 5, .c 3,
  .p pv23 [pv2,pv29,pv43,pv337], .c 79, .c 3, .c 5, .c 223, .c 3, .p pv2 [pv2,pv5,pv7,pv12007],
  .c 353, .c 3, .c 7, .c 11, .c 3, .c 19, .c 5, .c 3, .c 149, .c 7, .c 3, .c 5, .c 769, .c 3,
  .c 11, .p pv2 [pv2,pv3,pv19,pv73,pv101], .c 3, .c 53, .c 37, .c 3, .c 139, .c 5, .c 3, .c 7,
  .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv953], .c 3, .c 809, .c 7, .c 3, .p pv2 [pv2,pv210139],
  .c 563, .c 3, .c 239, .c 5, .c 3, .c 71, .p pv2 [pv2,pv3,pv5,pv28019], .c 3, .c 5, .c 673, .c 3,
  .c 7, .c 103, .c 3, .c 11, .p pv2 [pv2,pv3,pv7,pv10007], .c 3, .c 13, .c 5, .c 3, .c 17,
  .p pv7 [pv2,pv3,pv5,pv467], .c 3, .c 5, .c 43, .c 3, .p pv13 [pv2,pv5,pv84061], .c 127, .c 3,
  .c 19, .c 13, .c 3, .c 7, .c 5, .c 3, .c 389, .c 11, .c 3, .c 5, .c 7, .c 3, .c 61,
  .p pv2 [pv2,pv3,pv11,pv47,pv271], .c 3, .c 257, .c 67, .c 3, .c 11, .c 5, .c 3, .c 229,
  .p pv7 [pv2,pv3,pv5,pv14011], .c 3, .c 5, .c 17, .c 3, .c 13, .c 23, .c 3, .c 37, .c 7, .c 3,
  .p pv2 [pv2,pv420341], .c 5, .c 3, .c 31, .c 59, .c 3, .c 5, .c 11, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv61,pv2297], .c 3,
]
private theorem h0102c19 : checkBlock 840451 128 b0102c19 = true := by
  decide +kernel

private def b0102c20 : List Row := [
  .c 7, .p pv2 [pv2,pv3,pv11,pv193], .c 3, .p pv3 [pv2,pv19,pv5531], .c 5, .c 3, .c 11, .c 7,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv15569], .c 3, .c 19, .p pv5 [pv2,pv3,pv70061], .c 3, .c 421,
  .c 29, .c 3, .p pv5 [pv2,pv7,pv23,pv373], .c 5, .c 3, .c 7, .c 31, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv7,pv10009], .c 3, .p pv3 [pv2,pv5,pv21019], .c 7, .c 3,
  .p pv5 [pv2,pv420383], .c 17, .c 3, .c 683, .c 5, .c 3, .c 43, .c 347, .c 3, .c 5, .c 41, .c 3,
  .c 7, .c 283, .c 3, .c 29, .c 601, .c 3, .c 17, .c 5, .c 3, .c 59, .c 23, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv5839], .c 3, .p pv2 [pv2,pv5,pv17,pv2473], .p pv3 [pv2,pv3,pv43,pv3259], .c 3,
  .c 13, .c 11, .c 3, .c 7, .c 5, .c 3, .p pv37 [pv2,pv420419],
  .p pv41 [pv2,pv3,pv5,pv7,pv11,pv13], .c 3, .c 5, .c 7, .c 3, .c 11, .c 13, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv140143], .c 3, .p pv7 [pv2,pv11,pv37,pv1033], .c 5, .c 3, .c 41, .c 17, .c 3,
  .c 5, .c 47, .c 3, .c 431, .c 19, .c 3, .c 73, .c 7, .c 3, .c 97, .c 5, .c 3, .c 37, .c 193,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv31,pv137], .c 3, .p pv7 [pv2,pv5,pv7,pv41,pv293], .c 29,
  .c 3, .c 7, .c 151, .c 3, .p pv2 [pv2,pv17,pv24733], .c 5, .c 3, .p pv3 [pv2,pv11,pv2389], .c 7,
  .c 3, .c 5, .c 31, .c 3, .p pv2 [pv2,pv5,pv19,pv2213], .p pv3 [pv2,pv3,pv29,pv179], .c 3,
  .c 691, .c 23, .c 3, .c 173, .c 5, .c 3, .c 7, .c 11,
]
private theorem h0102c20 : checkBlock 840707 128 b0102c20 = true := by
  decide +kernel

private def b0102c21 : List Row := [
  .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv20023], .c 3, .c 29, .c 7, .c 3, .c 449,
  .p pv2 [pv2,pv3,pv19,pv2459], .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv210247],
  .p pv7 [pv2,pv3,pv5,pv17,pv97], .c 3, .c 5, .c 19, .c 3, .c 7, .p pv2 [pv2,pv3,pv140167], .c 3,
  .c 17, .c 13, .c 3, .p pv2 [pv2,pv167,pv1259], .c 5, .c 3, .p pv2 [pv2,pv23,pv47,pv389],
  .p pv2 [pv2,pv3,pv5,pv107,pv131], .c 3, .c 5, .c 11, .c 3, .c 313, .c 41, .c 3, .c 43, .c 83,
  .c 3, .c 7, .c 5, .c 3, .c 11, .c 67, .c 3, .c 5, .c 7, .c 3, .c 13, .p pv3 [pv2,pv3,pv140177],
  .c 3, .c 467, .p pv2 [pv2,pv3,pv61,pv383], .c 3, .c 19, .c 5, .c 3, .p pv7 [pv2,pv7,pv60077],
  .p pv11 [pv2,pv3,pv5,pv43,pv163], .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv241,pv349], .c 11,
  .c 3, .p pv3 [pv2,pv105137], .c 7, .c 3, .p pv5 [pv2,pv420551], .c 5, .c 3, .c 17, .c 19, .c 3,
  .c 5, .c 229, .c 3, .c 37, .c 31, .c 3, .c 7, .c 61, .c 3, .c 23, .c 5, .c 3, .c 13, .c 7, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv140191], .c 3, .c 131, .c 109, .c 3, .p pv2 [pv2,pv23,pv41,pv223],
  .c 11, .c 3, .c 53, .c 5, .c 3, .c 7, .c 587, .c 3, .c 5, .c 17, .c 3, .c 11, .c 7, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv70099], .c 3, .p pv3 [pv2,pv11,pv79], .c 5, .c 3, .c 353, .c 103, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv19,pv47,pv157], .c 3, .c 7, .p pv2 [pv2,pv3,pv7789], .c 3, .c 13,
]
private theorem h0102c21 : checkBlock 840963 128 b0102c21 = true := by
  decide +kernel

private def b0102c22 : List Row := [
  .p pv3 [pv2,pv3,pv7,pv20029], .c 3, .p pv5 [pv2,pv59,pv7129], .c 5, .c 3, .c 101,
  .p pv23 [pv2,pv3,pv5,pv13,pv719], .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv6373], .c 3,
  .p pv3 [pv2,pv5,pv21031], .c 13, .c 3, .c 11, .c 277, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv38239], .c 29, .c 3, .c 5, .c 7, .c 3, .c 23, .p pv5 [pv2,pv3,pv35053], .c 3,
  .p pv2 [pv2,pv210319], .c 17, .c 3, .p pv2 [pv2,pv13,pv19,pv131], .c 5, .c 3,
  .p pv3 [pv2,pv7,pv83,pv181], .c 11, .c 3, .c 5, .p pv43 [pv2,pv3,pv17,pv1031], .c 3, .c 19,
  .c 787, .c 3, .p pv2 [pv2,pv37,pv11369], .c 7, .c 3, .c 11, .c 5, .c 3, .c 29, .c 13, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv140221], .c 3, .c 241, .p pv2 [pv2,pv3,pv70111], .c 3, .c 7, .c 19,
  .c 3, .c 37, .c 5, .c 3, .p pv2 [pv2,pv29,pv7253], .c 7, .c 3, .c 5, .c 11, .c 3, .c 41, .c 23,
  .c 3, .c 139, .p pv29 [pv2,pv3,pv11,pv3187], .c 3, .c 13, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5,
  .c 197, .c 3, .p pv17 [pv2,pv5,pv11,pv7649], .c 7, .c 3, .p pv3 [pv2,pv19,pv11071], .c 13, .c 3,
  .c 149, .c 5, .c 3, .c 23, .p pv2 [pv2,pv3,pv5,pv9349], .c 3, .c 5, .c 37, .c 3, .c 7, .c 11,
  .c 3, .p pv2 [pv2,pv449,pv937], .c 79, .c 3, .c 31, .c 5, .c 3, .c 349, .c 47, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv46747], .c 3, .c 13, .c 19, .c 3, .p pv3 [pv2,pv7,pv11,pv683],
  .p pv2 [pv2,pv3,pv59,pv2377], .c 3, .c 7, .c 5, .c 3, .c 181, .c 73, .c 3,
]
private theorem h0102c22 : checkBlock 841219 128 b0102c22 = true := by
  decide +kernel

private def b0102c23 : List Row := [
  .c 5, .c 7, .c 3, .c 53, .c 17, .c 3, .c 307, .c 11, .c 3, .c 29, .c 5, .c 3, .c 883, .c 23,
  .c 3, .c 5, .c 523, .c 3, .c 11, .c 167, .c 3, .c 17, .c 7, .c 3, .c 151, .c 5, .c 3, .c 13,
  .c 367, .c 3, .c 5, .c 83, .c 3, .p pv2 [pv2,pv5,pv7,pv6011], .c 659, .c 3, .c 7,
  .p pv41 [pv2,pv3,pv19,pv3691], .c 3, .c 43, .c 5, .c 3, .p pv11 [pv2,pv420779], .c 7, .c 3,
  .c 5, .c 19, .c 3, .c 199, .p pv2 [pv2,pv3,pv97,pv241], .c 3, .c 11, .c 421, .c 3, .c 709, .c 5,
  .c 3, .c 7, .c 137, .c 3, .c 5, .p pv17 [pv2,pv3,pv7,pv43,pv233], .c 3, .p pv3 [pv2,pv5,pv263],
  .c 7, .c 3, .c 13, .c 29, .c 3, .c 103, .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .c 557, .c 3,
  .c 7, .c 13, .c 3, .p pv2 [pv2,pv17,pv12377], .c 23, .c 3, .c 11, .c 5, .c 3, .c 613,
  .p pv3 [pv2,pv3,pv5,pv31,pv181], .c 3, .c 5, .c 313, .c 3, .p pv2 [pv2,pv5,pv42083],
  .p pv5 [pv2,pv3,pv19,pv23,pv107], .c 3, .c 29, .c 97, .c 3, .c 7, .c 5, .c 3, .c 211, .c 19,
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv73,pv1153], .c 53, .c 3, .p pv3 [pv2,pv29,pv907],
  .c 401, .c 3, .c 83, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 653, .c 3, .c 17, .c 47, .c 3,
  .p pv5 [pv2,pv271,pv1553], .c 7,
]
private theorem h0102c23 : checkBlock 841475 128 b0102c23 = true := by
  decide +kernel

private def b0102c24 : List Row := [
  .c 3, .c 331, .c 5, .c 3, .c 61, .p pv11 [pv2,pv3,pv5,pv14029], .c 3, .c 5, .c 647, .c 3,
  .p pv7 [pv2,pv5,pv7,pv13,pv37], .c 11, .c 3, .c 7, .c 379, .c 3, .c 13, .c 5, .c 3, .c 107,
  .c 7, .c 3, .c 5, .c 23, .c 3, .c 197, .c 29, .c 3, .c 37, .c 13, .c 3, .p pv5 [pv2,pv7,pv1879],
  .c 5, .c 3, .c 7, .p pv37 [pv2,pv3,pv5,pv23,pv61], .c 3, .c 5, .c 109, .c 3, .c 43, .c 7, .c 3,
  .c 47, .c 11, .c 3, .c 17, .c 5, .c 3, .c 233, .c 181, .c 3, .c 5, .c 179, .c 3, .c 7, .c 577,
  .c 3, .c 71, .p pv31 [pv2,pv3,pv7,pv5011], .c 3, .c 41, .c 5, .c 3, .p pv2 [pv2,pv420929],
  .c 37, .c 3, .c 5, .c 13, .c 3, .c 19, .p pv5 [pv2,pv3,pv17539], .c 3, .c 311,
  .p pv3 [pv2,pv3,pv46771], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv26309], .c 17, .c 3, .c 5, .c 7,
  .c 3, .c 701, .c 79, .c 3, .c 11, .c 19, .c 3, .p pv3 [pv2,pv105239], .c 5, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv5,pv877], .c 3, .c 5, .p pv3 [pv2,pv3,pv140321], .c 3,
  .p pv2 [pv2,pv5,pv59,pv1427], .p pv5 [pv2,pv3,pv7,pv13,pv257], .c 3, .c 131, .c 7, .c 3, .c 227,
  .c 5, .c 3, .c 719, .c 11, .c 3, .c 5, .c 29, .c 3, .c 23, .c 113, .c 3, .c 7, .c 199, .c 3,
  .c 11, .c 5, .c 3, .p pv2 [pv2,pv197,pv2137], .c 7, .c 3, .c 5,
]
private theorem h0102c24 : checkBlock 841731 128 b0102c24 = true := by
  decide +kernel

private def b0102c25 : List Row := [
  .p pv2 [pv2,pv3,pv29,pv1613], .c 3, .c 31, .c 17, .c 3, .c 13, .c 149, .c 3,
  .p pv2 [pv2,pv7,pv137,pv439], .c 5, .c 3, .c 7, .c 53, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv42101], .c 7, .c 3, .c 17, .c 89, .c 3, .c 229, .c 5, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv5,pv2339], .c 3, .c 5, .p pv3 [pv2,pv3,pv37,pv3793], .c 3, .c 7, .c 23, .c 3,
  .c 97, .c 193, .c 3, .p pv29 [pv2,pv13,pv139,pv233], .c 5, .c 3, .c 43,
  .p pv3 [pv2,pv3,pv5,pv28069], .c 3, .c 5, .p pv2 [pv2,pv3,pv23,pv113], .c 3,
  .p pv17 [pv2,pv5,pv19,pv277], .c 11, .c 3, .p pv5 [pv2,pv7,pv60149],
  .p pv11 [pv2,pv3,pv13,pv2699], .c 3, .c 7, .c 5, .c 3, .c 19, .c 13, .c 3, .c 5, .c 7, .c 3,
  .p pv41 [pv2,pv5,pv84211], .p pv7 [pv2,pv3,pv17,pv43], .c 3, .c 53, .c 191, .c 3, .c 67, .c 5,
  .c 3, .c 17, .c 29, .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv13,pv41,pv79], .c 443, .c 3,
  .p pv2 [pv2,pv17,pv31,pv47], .c 7, .c 3, .c 13, .c 5, .c 3, .p pv13 [pv2,pv421079],
  .p pv13 [pv2,pv3,pv5,pv11,pv29], .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv59,pv61], .c 3, .c 11,
  .p pv2 [pv2,pv3,pv70181], .c 3, .c 7, .c 13, .c 3, .p pv5 [pv2,pv11,pv38281], .c 5, .c 3, .c 29,
  .c 7, .c 3, .c 5, .c 17, .c 3, .c 73, .p pv3 [pv2,pv3,pv71,pv659], .c 3, .c 89,
  .p pv17 [pv2,pv3,pv31,pv283], .c 3, .c 19, .c 5, .c 3, .c 7, .c 163, .c 3, .c 5, .c 61, .c 3,
  .c 13, .c 7, .c 3, .c 11, .c 31, .c 3,
]
private theorem h0102c25 : checkBlock 841987 128 b0102c25 = true := by
  decide +kernel

private def b0102c26 : List Row := [
  .c 109, .c 5, .c 3, .p pv3 [pv2,pv11,pv17,pv563], .c 19, .c 3, .c 5, .c 13, .c 3, .c 7, .c 41,
  .c 3, .p pv2 [pv2,pv421133], .c 317, .c 3, .c 71, .c 5, .c 3, .p pv7 [pv2,pv151,pv2789], .c 11,
  .c 3, .c 5, .c 47, .c 3, .p pv2 [pv2,pv5,pv84229], .p pv5 [pv2,pv3,pv11,pv709], .c 3, .c 149,
  .c 17, .c 3, .c 7, .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv7,pv191], .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv10529], .p pv5 [pv2,pv3,pv13,pv10799], .c 3, .c 19, .c 23, .c 3, .c 17, .c 5,
  .c 3, .p pv2 [pv2,pv7,pv60167], .p pv2 [pv2,pv3,pv5,pv101,pv139], .c 3, .c 5, .c 11, .c 3,
  .p pv11 [pv2,pv5,pv17,pv991], .p pv11 [pv2,pv3,pv7,pv23,pv109], .c 3, .c 277, .c 7, .c 3, .c 29,
  .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv43,pv653], .c 3, .c 5, .c 79, .c 3, .c 47,
  .p pv3 [pv2,pv3,pv53,pv883], .c 3, .c 7, .c 263, .c 3, .p pv3 [pv2,pv29,pv3631], .c 5, .c 3,
  .p pv23 [pv2,pv23,pv18313], .c 7, .c 3, .c 5, .p pv11 [pv2,pv3,pv140401], .c 3, .c 107, .c 11,
  .c 3, .p pv3 [pv2,pv37,pv1423], .p pv3 [pv2,pv3,pv17,pv2753], .c 3,
  .p pv7 [pv2,pv7,pv19,pv3167], .c 5, .c 3, .c 7, .c 857, .c 3, .c 5, .c 103, .c 3, .c 19, .c 7,
  .c 3, .p pv5 [pv2,pv11,pv149,pv257], .p pv7 [pv2,pv3,pv17551], .c 3, .c 37, .c 5, .c 3, .c 619,
  .c 59, .c 3, .c 5, .c 23, .c 3, .c 7, .p pv5 [pv2,pv3,pv11701], .c 3, .p pv2 [pv2,pv210619],
  .c 11, .c 3, .p pv2 [pv2,pv421241], .c 5, .c 3, .p pv3 [pv2,pv53,pv1987], .c 13, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv1097],
]
private theorem h0102c26 : checkBlock 842243 128 b0102c26 = true := by
  decide +kernel

private def b0102c27 : List Row := [
  .c 3, .c 11, .c 17, .c 3, .p pv2 [pv2,pv7,pv8597], .c 41, .c 3, .c 7, .c 5, .c 3,
  .p pv13 [pv2,pv31,pv107,pv127], .p pv31 [pv2,pv3,pv5,pv7,pv17,pv59], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv13,pv6481], .c 83, .c 3, .c 17, .c 271, .c 3, .c 13, .c 5, .c 3, .c 31,
  .p pv13 [pv2,pv3,pv5,pv41,pv137], .c 3, .c 5, .c 71, .c 3, .c 479, .c 89, .c 3, .c 11, .c 7,
  .c 3, .c 359, .c 5, .c 3, .c 59, .p pv2 [pv2,pv3,pv5,pv31,pv151], .c 3, .c 5,
  .p pv7 [pv2,pv3,pv317,pv443], .c 3, .c 41, .c 19, .c 3, .c 7, .p pv7 [pv2,pv3,pv46811], .c 3,
  .c 907, .c 5, .c 3, .c 419, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv47,pv83], .c 3, .c 13,
  .p pv3 [pv2,pv3,pv11,pv17,pv751], .c 3, .p pv2 [pv2,pv421313], .c 811, .c 3, .c 11, .c 5, .c 3,
  .c 7, .c 113, .c 3, .c 5, .c 13, .c 3, .c 23, .c 7, .c 3, .p pv5 [pv2,pv17,pv1549], .c 67, .c 3,
  .c 47, .c 5, .c 3, .c 19, .c 43, .c 3, .c 5, .c 11, .c 3, .c 7, .c 173, .c 3, .c 137, .c 569,
  .c 3, .c 79, .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv53], .c 3, .c 5, .c 17, .c 3, .c 29,
  .c 827, .c 3, .c 223, .c 281, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv105341], .c 151, .c 3, .c 5,
  .c 7, .c 3, .c 17, .c 11, .c 3, .p pv2 [pv2,pv103,pv4091], .c 37, .c 3, .c 53,
]
private theorem h0102c27 : checkBlock 842499 128 b0102c27 = true := by
  decide +kernel

private def b0102c28 : List Row := [
  .c 5, .c 3, .p pv7 [pv2,pv7,pv17,pv3541], .c 233, .c 3, .c 5, .p pv7 [pv2,pv3,pv23,pv31,pv197],
  .c 3, .p pv13 [pv2,pv5,pv71,pv1187], .c 449, .c 3, .c 13, .c 7, .c 3, .c 19, .c 5, .c 3, .c 23,
  .p pv3 [pv2,pv3,pv5,pv13,pv2161], .c 3, .c 5, .c 31, .c 3, .p pv3 [pv2,pv5,pv7,pv43], .c 13,
  .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv23,pv9161], .c 5, .c 3, .p pv2 [pv2,pv421409], .c 7,
  .c 3, .c 5, .c 29, .c 3, .c 11, .c 97, .c 3, .c 41, .c 107, .c 3, .c 17, .c 5, .c 3, .c 7,
  .c 47, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv29,pv173], .c 3, .c 659, .c 7, .c 3, .c 113,
  .p pv2 [pv2,pv3,pv13,pv1801], .c 3, .c 163, .c 5, .c 3, .p pv7 [pv2,pv19,pv41,pv541], .c 13,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv43], .c 3, .c 7, .c 149, .c 3, .c 11, .c 127, .c 3, .c 317,
  .c 5, .c 3, .c 313, .c 17, .c 3, .c 5, .c 181, .c 3, .c 31, .p pv2 [pv2,pv3,pv46829], .c 3,
  .c 23, .c 43, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv421469], .c 11, .c 3, .c 5, .c 7, .c 3,
  .p pv13 [pv2,pv5,pv23,pv733], .c 239, .c 3, .p pv2 [pv2,pv210739], .c 13, .c 3, .c 11, .c 5,
  .c 3, .p pv3 [pv2,pv7,pv15053], .c 37, .c 3, .c 5, .p pv13 [pv2,pv3,pv2927], .c 3,
  .p pv2 [pv2,pv5,pv113,pv373], .c 31, .c 3, .p pv2 [pv2,pv421493], .c 7, .c 3,
  .p pv3 [pv2,pv19,pv47,pv59], .c 5, .c 3, .c 367, .c 29, .c 3, .c 5, .c 11, .c 3,
]
private theorem h0102c28 : checkBlock 842755 128 b0102c28 = true := by
  decide +kernel

private def b0102c29 : List Row := [
  .c 13, .c 17, .c 3, .c 7, .c 23, .c 3, .c 653, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 13, .c 3,
  .c 647, .p pv2 [pv2,pv3,pv23,pv41,pv149], .c 3, .c 17, .c 19, .c 3, .c 107, .c 5, .c 3, .c 7,
  .c 67, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv6691], .c 3, .c 53, .c 7, .c 3, .c 73,
  .p pv3 [pv2,pv3,pv227,pv619], .c 3, .c 41, .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv157,pv179],
  .c 3, .c 5, .c 89, .c 3, .c 7, .p pv17 [pv2,pv3,pv13,pv1201], .c 3, .c 31, .c 251, .c 3,
  .p pv3 [pv2,pv105389], .c 5, .c 3, .c 37, .c 311, .c 3, .c 5, .p pv3 [pv2,pv3,pv140521], .c 3,
  .p pv2 [pv2,pv5,pv84313], .c 47, .c 3, .p pv3 [pv2,pv7,pv941], .c 11, .c 3, .c 7, .c 5, .c 3,
  .c 17, .c 863, .c 3, .c 5, .c 7, .c 3, .c 11, .c 19, .c 3, .c 13, .c 31, .c 3,
  .p pv2 [pv2,pv11,pv19163], .c 5, .c 3, .p pv2 [pv2,pv7,pv229,pv263],
  .p pv2 [pv2,pv3,pv5,pv13,pv23,pv47], .c 3, .c 5, .c 43, .c 3, .c 149, .c 13, .c 3, .c 83, .c 7,
  .c 3, .c 23, .c 5, .c 3, .p pv3 [pv2,pv105401], .p pv2 [pv2,pv3,pv5,pv347], .c 3, .c 5, .c 17,
  .c 3, .c 97, .c 73, .c 3, .c 7, .p pv2 [pv2,pv3,pv59,pv397], .c 3, .c 29, .c 5, .c 3, .c 19,
  .c 7, .c 3, .c 5, .c 41, .c 3, .c 17, .p pv2 [pv2,pv3,pv70271], .c 3, .p pv3 [pv2,pv105407],
  .c 241, .c 3, .c 421, .c 5,
]
private theorem h0102c29 : checkBlock 843011 128 b0102c29 = true := by
  decide +kernel

private def b0102c30 : List Row := [
  .c 3, .c 7, .c 11, .c 3, .c 5, .c 19, .c 3, .c 281, .c 7, .c 3, .c 59,
  .p pv7 [pv2,pv3,pv41,pv857], .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv557,pv757],
  .p pv29 [pv2,pv3,pv5,pv937], .c 3, .c 5, .p pv2 [pv2,pv3,pv140551], .c 3, .c 7, .c 139, .c 3,
  .c 353, .c 17, .c 3, .c 13, .c 5, .c 3, .c 41, .p pv11 [pv2,pv3,pv5,pv28111], .c 3, .c 5, .c 11,
  .c 3, .c 23, .c 773, .c 3, .p pv2 [pv2,pv7,pv59,pv1021], .c 13, .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv5,pv7,pv251], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv11,pv17,pv41],
  .c 751, .c 3, .p pv3 [pv2,pv52711], .p pv2 [pv2,pv3,pv29,pv37,pv131], .c 3,
  .p pv5 [pv2,pv421691], .c 5, .c 3, .c 53, .c 19, .c 3, .c 5, .p pv2 [pv2,pv3,pv67,pv1049], .c 3,
  .c 13, .c 11, .c 3, .c 29, .c 7, .c 3, .c 509, .c 5, .c 3, .c 541, .c 17, .c 3, .c 5, .c 13,
  .c 3, .c 239, .c 23, .c 3, .c 7, .c 617, .c 3, .p pv2 [pv2,pv53,pv73,pv109], .c 5, .c 3,
  .p pv3 [pv2,pv19,pv31,pv179], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv23,pv191], .c 3,
  .p pv2 [pv2,pv5,pv181,pv233], .c 67, .c 3, .c 19, .c 11, .c 3, .p pv3 [pv2,pv7,pv17,pv443],
  .c 5, .c 3, .c 7, .c 107, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv19,pv151], .c 3, .c 11, .c 7, .c 3,
  .p pv3 [pv2,pv105437], .c 521, .c 3, .p pv5 [pv2,pv11,pv23,pv1667], .c 5, .c 3, .c 47, .c 337,
  .c 3, .c 5, .c 167, .c 3, .c 7,
]
private theorem h0102c30 : checkBlock 843267 128 b0102c30 = true := by
  decide +kernel

private def b0102c31 : List Row := [
  .c 17, .c 3, .p pv5 [pv2,pv37,pv11399], .c 83, .c 3, .c 349, .c 5, .c 3,
  .p pv2 [pv2,pv491,pv859], .c 31, .c 3, .c 5, .c 293, .c 3, .c 71, .p pv11 [pv2,pv3,pv29,pv101],
  .c 3, .c 11, .p pv13 [pv2,pv3,pv140593], .c 3, .c 7, .c 5, .c 3, .c 61, .c 23, .c 3, .c 5, .c 7,
  .c 3, .c 19, .c 13, .c 3, .p pv2 [pv2,pv463,pv911], .p pv13 [pv2,pv3,pv73,pv107], .c 3, .c 769,
  .c 5, .c 3, .c 523, .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv46867], .c 3, .c 251,
  .p pv5 [pv2,pv3,pv7,pv11,pv83], .c 3, .c 23, .c 7, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv210907], .c 89, .c 3, .c 5, .c 37, .c 3, .c 59, .p pv13 [pv2,pv3,pv17,pv919],
  .c 3, .c 7, .p pv17 [pv2,pv3,pv13], .c 3, .c 101, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 11,
  .c 3, .c 449, .c 103, .c 3, .p pv2 [pv2,pv17,pv19,pv653], .p pv3 [pv2,pv3,pv11,pv4261], .c 3,
  .c 733, .c 5, .c 3, .c 7, .c 61, .c 3, .c 5, .c 29, .c 3, .p pv2 [pv2,pv5,pv11,pv13,pv59], .c 7,
  .c 3, .c 53, .c 23, .c 3, .c 13, .c 5, .c 3, .c 331, .c 173, .c 3, .c 5, .c 17, .c 3, .c 7,
  .c 11, .c 3, .p pv3 [pv2,pv105467], .c 13, .c 3, .c 311, .c 5, .c 3, .c 383, .c 197, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv70313], .c 3, .c 17, .p pv2 [pv2,pv3,pv140627], .c 3, .c 409, .c 109, .c 3,
  .c 7, .c 5, .c 3,
]
private theorem h0102c31 : checkBlock 843523 128 b0102c31 = true := by
  decide +kernel

def rows0102 : List Row :=
  b0102c00 ++ b0102c01 ++ b0102c02 ++ b0102c03 ++ b0102c04 ++ b0102c05 ++ b0102c06 ++ b0102c07 ++
  b0102c08 ++ b0102c09 ++ b0102c10 ++ b0102c11 ++ b0102c12 ++ b0102c13 ++ b0102c14 ++ b0102c15 ++
  b0102c16 ++ b0102c17 ++ b0102c18 ++ b0102c19 ++ b0102c20 ++ b0102c21 ++ b0102c22 ++ b0102c23 ++
  b0102c24 ++ b0102c25 ++ b0102c26 ++ b0102c27 ++ b0102c28 ++ b0102c29 ++ b0102c30 ++ b0102c31

attribute [local irreducible] checkBlock checkRows checkPrime

theorem checked0102 : checkBlock 835587 4096 rows0102 = true :=
  checkBlock_append h0102c00 (
    checkBlock_append h0102c01 (
    checkBlock_append h0102c02 (
    checkBlock_append h0102c03 (
    checkBlock_append h0102c04 (
    checkBlock_append h0102c05 (
    checkBlock_append h0102c06 (
    checkBlock_append h0102c07 (
    checkBlock_append h0102c08 (
    checkBlock_append h0102c09 (
    checkBlock_append h0102c10 (
    checkBlock_append h0102c11 (
    checkBlock_append h0102c12 (
    checkBlock_append h0102c13 (
    checkBlock_append h0102c14 (
    checkBlock_append h0102c15 (
    checkBlock_append h0102c16 (
    checkBlock_append h0102c17 (
    checkBlock_append h0102c18 (
    checkBlock_append h0102c19 (
    checkBlock_append h0102c20 (
    checkBlock_append h0102c21 (
    checkBlock_append h0102c22 (
    checkBlock_append h0102c23 (
    checkBlock_append h0102c24 (
    checkBlock_append h0102c25 (
    checkBlock_append h0102c26 (
    checkBlock_append h0102c27 (
    checkBlock_append h0102c28 (
    checkBlock_append h0102c29 (
    checkBlock_append h0102c30 (
    h0102c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
