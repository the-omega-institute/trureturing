/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks02/Block0226
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks02/Block0226.checked0226
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table135

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0226c00 : List Row := [
  .c 5, .c 179, .c 3, .p pv7 [pv2,pv5,pv9257], .p pv7 [pv2,pv3,pv7,pv17,pv2593], .c 3,
  .p pv5 [pv2,pv37,pv127,pv197], .c 7, .c 3, .c 31, .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .c 1091,
  .c 3, .c 23, .p pv5 [pv2,pv3,pv11,pv7013], .c 3, .c 7, .c 97, .c 3, .c 11, .c 5, .c 3, .c 53,
  .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv9643], .c 3, .c 661, .p pv5 [pv2,pv3,pv102859], .c 3, .c 71,
  .p pv2 [pv2,pv3,pv277,pv557], .c 3, .c 13, .c 5, .c 3, .c 7, .c 83, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv185149], .c 7, .c 3, .c 929, .c 13, .c 3, .p pv5 [pv2,pv53,pv17467], .c 5,
  .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv61717], .c 3, .c 5, .c 37, .c 3, .c 7, .c 23, .c 3, .c 269,
  .c 167, .c 3, .c 61, .c 5, .c 3, .p pv2 [pv2,pv13,pv17,pv59,pv71], .p pv2 [pv2,pv3,pv5,pv30859],
  .c 3, .c 5, .p pv3 [pv2,pv3,pv23,pv13417], .c 3, .c 13, .c 11, .c 3,
  .p pv2 [pv2,pv7,pv89,pv743], .p pv13 [pv2,pv3,pv421,pv733], .c 3, .c 7, .c 5, .c 3, .c 19,
  .p pv29 [pv2,pv3,pv5,pv7,pv2939], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv43,pv2153], .c 109,
  .c 3, .p pv2 [pv2,pv11,pv84163], .c 17, .c 3, .c 577, .c 5, .c 3, .c 31, .c 41, .c 3, .c 5,
  .c 19, .c 3, .p pv2 [pv2,pv5,pv185161], .c 683, .c 3, .c 617, .c 7, .c 3, .c 17, .c 5, .c 3,
  .c 13, .c 103, .c 3, .c 5, .p pv2 [pv2,pv3,pv154303], .c 3, .c 11,
  .p pv2 [pv2,pv3,pv13,pv41,pv193], .c 3, .c 7, .p pv11 [pv2,pv3,pv2411],
]
private theorem h0226c00 : checkBlock 1851395 128 b0226c00 = true := by
  decide +kernel

private def b0226c01 : List Row := [
  .c 3, .c 827, .c 5, .c 3, .c 47, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv43,pv7177], .c 3,
  .p pv17 [pv2,pv5,pv185167], .c 839, .c 3, .p pv2 [pv2,pv449,pv1031], .c 29, .c 3, .c 19, .c 5,
  .c 3, .c 7, .c 17, .c 3, .c 5, .c 971, .c 3, .p pv3 [pv2,pv5,pv18517], .c 7, .c 3, .c 11, .c 43,
  .c 3, .c 151, .c 5, .c 3, .p pv7 [pv2,pv11,pv73,pv1153], .c 19, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv308621], .c 3, .c 7, .c 13, .c 3, .c 29, .c 37, .c 3, .c 271, .c 5, .c 3,
  .p pv2 [pv2,pv462937], .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv154313], .c 3,
  .p pv3 [pv2,pv5,pv79,pv293], .p pv3 [pv2,pv3,pv11,pv28057], .c 3, .c 53,
  .p pv7 [pv2,pv3,pv8573], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv19,pv48731],
  .p pv2 [pv2,pv3,pv5,pv7,pv4409], .c 3, .c 5, .c 7, .c 3, .c 73, .c 17, .c 3, .c 19, .c 23, .c 3,
  .p pv2 [pv2,pv925901], .c 5, .c 3, .p pv3 [pv2,pv7,pv1181], .c 13, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv53,pv1747], .c 89, .c 3, .c 17, .c 7, .c 3, .c 59, .c 5, .c 3, .c 11,
  .p pv17 [pv2,pv3,pv5,pv643], .c 3, .c 5, .c 31, .c 3, .p pv7 [pv2,pv5,pv7,pv11,pv13,pv37],
  .c 29, .c 3, .c 7, .p pv2 [pv2,pv3,pv102881], .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv23,pv20129], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv1319], .c 3, .c 43, .c 11,
  .c 3, .c 37, .c 13, .c 3, .c 71, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv6173], .c 3, .c 5,
]
private theorem h0226c01 : checkBlock 1851651 128 b0226c01 = true := by
  decide +kernel

private def b0226c02 : List Row := [
  .p pv2 [pv2,pv3,pv7,pv6299], .c 3, .c 19, .c 7, .c 3, .p pv2 [pv2,pv11,pv42089],
  .p pv3 [pv2,pv3,pv79,pv3907], .c 3, .c 229, .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv19], .c 3,
  .c 5, .c 23, .c 3, .c 7, .c 523, .c 3, .c 67, .c 11, .c 3, .p pv3 [pv2,pv283,pv409], .c 5, .c 3,
  .c 1151, .c 37, .c 3, .c 5, .c 13, .c 3, .c 11, .p pv2 [pv2,pv3,pv157,pv983], .c 3, .c 857,
  .c 53, .c 3, .c 7, .c 5, .c 3, .c 1259, .p pv3 [pv2,pv3,pv5,pv7,pv8819], .c 3, .c 5, .c 7, .c 3,
  .c 89, .p pv2 [pv2,pv3,pv31,pv3319], .c 3, .c 431, .p pv7 [pv2,pv3,pv77167], .c 3,
  .p pv2 [pv2,pv463003], .c 5, .c 3, .c 13, .c 61, .c 3, .c 5, .c 29, .c 3, .c 17, .c 31, .c 3,
  .c 11, .c 7, .c 3, .c 103, .c 5, .c 3, .p pv3 [pv2,pv11,pv17,pv619],
  .p pv2 [pv2,pv3,pv5,pv12347], .c 3, .c 5, .p pv23 [pv2,pv3,pv29,pv887], .c 3, .c 487, .c 19,
  .c 3, .c 7, .c 59, .c 3, .p pv3 [pv2,pv37,pv6257], .c 5, .c 3, .p pv11 [pv2,pv131,pv7069], .c 7,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv308681], .c 3, .p pv2 [pv2,pv5,pv89,pv2081], .c 41, .c 3, .c 13,
  .c 17, .c 3, .c 11, .c 5, .c 3, .c 7, .p pv37 [pv2,pv3,pv5,pv13,pv1583], .c 3, .c 5, .c 233,
  .c 3, .c 23, .c 7, .c 3, .c 191, .c 47, .c 3, .c 17, .c 5, .c 3, .c 19, .c 439, .c 3, .c 5,
  .c 11, .c 3, .c 7, .p pv5 [pv2,pv3,pv229,pv337], .c 3, .c 31,
  .p pv7 [pv2,pv3,pv7,pv11,pv19,pv211], .c 3,
]
private theorem h0226c02 : checkBlock 1851907 128 b0226c02 = true := by
  decide +kernel

private def b0226c03 : List Row := [
  .p pv2 [pv2,pv13,pv71237], .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv107,pv577], .c 3, .c 5,
  .c 19, .c 3, .p pv2 [pv2,pv5,pv11,pv8419], .c 37, .c 3, .c 59, .p pv2 [pv2,pv3,pv13,pv31,pv383],
  .c 3, .c 7, .c 5, .c 3, .c 257, .c 13, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv185221], .c 11,
  .c 3, .p pv3 [pv2,pv41,pv5647], .c 31, .c 3, .c 47, .c 5, .c 3, .c 73, .c 317, .c 3, .c 5,
  .c 109, .c 3, .p pv3 [pv2,pv5,pv13,pv137], .p pv3 [pv2,pv3,pv7,pv44101], .c 3,
  .p pv5 [pv2,pv11,pv59,pv1427], .c 7, .c 3, .c 13, .c 5, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv5,pv30871], .c 3, .c 5, .c 1249, .c 3, .p pv7 [pv2,pv5,pv7,pv47,pv563],
  .p pv5 [pv2,pv3,pv19,pv677], .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv23,pv67,pv601], .c 5, .c 3,
  .p pv3 [pv2,pv29,pv499], .c 7, .c 3, .c 5, .c 53, .c 3, .c 11, .c 17, .c 3,
  .p pv2 [pv2,pv926153], .c 263, .c 3, .c 79, .c 5, .c 3, .c 7, .c 1361, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv61,pv241], .c 3, .c 13, .c 7, .c 3, .c 17, .c 41, .c 3, .c 31, .c 5, .c 3,
  .c 67, .c 23, .c 3, .c 5, .c 13, .c 3, .c 7, .p pv3 [pv2,pv3,pv34303], .c 3, .c 11, .c 211,
  .c 3, .p pv2 [pv2,pv463093], .c 5, .c 3, .c 757, .c 229, .c 3, .c 5, .c 61, .c 3, .c 197,
  .p pv5 [pv2,pv3,pv79,pv977], .c 3, .c 23, .c 419, .c 3, .c 7, .c 5, .c 3, .c 13, .c 11, .c 3,
  .c 5, .c 7,
]
private theorem h0226c03 : checkBlock 1852163 128 b0226c03 = true := by
  decide +kernel

private def b0226c04 : List Row := [
  .c 3, .c 41, .c 59, .c 3, .p pv2 [pv2,pv929,pv997], .p pv7 [pv2,pv3,pv154369], .c 3, .c 11,
  .c 5, .c 3, .c 17, .c 101, .c 3, .c 5, .p pv3 [pv2,pv3,pv89,pv3469], .c 3,
  .p pv2 [pv2,pv5,pv37049], .c 139, .c 3, .p pv3 [pv2,pv17,pv53,pv257], .c 7, .c 3, .c 463, .c 5,
  .c 3, .p pv2 [pv2,pv151,pv3067], .c 79, .c 3, .c 5, .c 11, .c 3, .c 19, .c 43, .c 3, .c 7,
  .c 23, .c 3, .p pv2 [pv2,pv349,pv1327], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 17, .c 3,
  .p pv11 [pv2,pv5,pv11,pv1531], .c 13, .c 3, .c 149, .c 19, .c 3, .p pv2 [pv2,pv7,pv113,pv1171],
  .c 5, .c 3, .c 7, .c 167, .c 3, .c 5, .c 1039, .c 3, .c 17, .c 7, .c 3, .c 227, .c 29, .c 3,
  .c 37, .c 5, .c 3, .p pv7 [pv2,pv17,pv23,pv103], .c 653, .c 3, .c 5, .c 241, .c 3, .c 7, .c 823,
  .c 3, .c 1069, .p pv3 [pv2,pv3,pv7,pv13,pv29], .c 3, .c 233, .c 5, .c 3, .c 467, .c 13, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv51461], .c 3, .p pv3 [pv2,pv5,pv59,pv157], .c 71, .c 3, .c 29, .c 11,
  .c 3, .c 7, .c 5, .c 3, .c 151, .p pv17 [pv2,pv3,pv5,pv7,pv11,pv401], .c 3, .c 5, .c 7, .c 3,
  .c 11, .c 19, .c 3, .p pv2 [pv2,pv29,pv15971], .c 293, .c 3, .c 13, .c 5, .c 3,
  .p pv11 [pv2,pv7,pv33083], .c 137, .c 3, .c 5, .c 173, .c 3, .c 103,
  .p pv3 [pv2,pv3,pv7,pv44111], .c 3, .c 41, .c 7, .c 3, .c 23,
]
private theorem h0226c04 : checkBlock 1852419 128 b0226c04 = true := by
  decide +kernel

private def b0226c05 : List Row := [
  .c 5, .c 3, .p pv11 [pv2,pv457,pv2027], .p pv11 [pv2,pv3,pv5,pv15439], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv3119], .c 3, .c 373, .c 47, .c 3, .c 7, .p pv2 [pv2,pv3,pv43,pv167],
  .c 3, .p pv5 [pv2,pv926351], .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 751, .c 3, .c 13, .c 29,
  .c 3, .p pv5 [pv2,pv83,pv11161], .c 1193, .c 3, .c 131, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .c 13, .c 3, .c 67, .c 7, .c 3, .c 157, .c 461, .c 3, .c 11, .c 5, .c 3, .c 673,
  .p pv2 [pv2,pv3,pv5,pv151,pv409], .c 3, .c 5, .c 31, .c 3, .c 7, .c 661, .c 3, .c 47,
  .p pv29 [pv2,pv3,pv7,pv23,pv137], .c 3, .p pv3 [pv2,pv231599], .c 5, .c 3, .c 13, .c 283, .c 3,
  .c 5, .c 11, .c 3, .c 23, .c 17, .c 3, .p pv3 [pv2,pv7,pv71,pv233],
  .p pv2 [pv2,pv3,pv11,pv67,pv419], .c 3, .c 7, .c 5, .c 3, .c 11, .c 41, .c 3, .c 5, .c 7, .c 3,
  .c 349, .p pv2 [pv2,pv3,pv19,pv16253], .c 3, .c 17, .c 37, .c 3, .c 277, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv132347], .c 19, .c 3, .c 5, .c 103, .c 3, .c 1153, .c 11, .c 3, .c 13, .c 7,
  .c 3, .c 601, .c 5, .c 3, .c 199, .c 89, .c 3, .c 5, .c 29, .c 3, .c 31, .c 13, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv154409], .c 3, .c 41, .c 5, .c 3, .c 107, .c 7, .c 3, .c 5, .c 1277, .c 3,
]
private theorem h0226c05 : checkBlock 1852675 128 b0226c05 = true := by
  decide +kernel

private def b0226c06 : List Row := [
  .c 379, .c 53, .c 3, .c 19, .c 11, .c 3, .c 887, .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv11,pv1123], .c 3, .c 5, .p pv11 [pv2,pv3,pv7,pv19,pv43], .c 3, .c 11,
  .c 7, .c 3, .c 239, .p pv7 [pv2,pv3,pv13,pv5939], .c 3, .p pv2 [pv2,pv11,pv23,pv1831], .c 5,
  .c 3, .c 683, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv53,pv5827], .c 3, .c 7, .c 193, .c 3, .c 37,
  .c 43, .c 3, .c 173, .c 5, .c 3, .c 139, .p pv2 [pv2,pv3,pv5,pv6863], .c 3, .c 5, .c 17, .c 3,
  .c 401, .c 449, .c 3, .c 11, .c 71, .c 3, .c 7, .c 5, .c 3, .c 53, .c 23, .c 3, .c 5, .c 7,
  .c 3, .c 17, .p pv5 [pv2,pv3,pv307,pv503], .c 3, .c 127, .c 13, .c 3, .p pv5 [pv2,pv137,pv6763],
  .c 5, .c 3, .c 47, .c 11, .c 3, .c 5, .c 41, .c 3, .p pv3 [pv2,pv5,pv46327],
  .p pv2 [pv2,pv3,pv7,pv11,pv191], .c 3, .c 23, .c 7, .c 3, .c 11, .c 5, .c 3, .c 613, .c 877,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv308851], .c 3, .c 13, .c 149, .c 3, .c 7, .c 17, .c 3, .c 727,
  .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .c 11, .c 3, .c 83, .c 1201, .c 3, .c 163, .c 31, .c 3,
  .c 17, .c 5, .c 3, .c 7, .p pv19 [pv2,pv3,pv5,pv15443], .c 3, .c 5,
  .p pv31 [pv2,pv3,pv7,pv44123], .c 3, .c 43, .c 7, .c 3, .p pv3 [pv2,pv13,pv103,pv173], .c 23,
  .c 3, .p pv5 [pv2,pv37,pv79,pv317], .c 5,
]
private theorem h0226c06 : checkBlock 1852931 128 b0226c06 = true := by
  decide +kernel

private def b0226c07 : List Row := [
  .c 3, .c 13, .p pv7 [pv2,pv3,pv5,pv59,pv349], .c 3, .c 5, .c 521, .c 3, .c 7, .c 11, .c 3,
  .p pv5 [pv2,pv239,pv3877], .p pv11 [pv2,pv3,pv7,pv3677], .c 3, .c 211, .c 5, .c 3, .c 37, .c 17,
  .c 3, .c 5, .c 257, .c 3, .p pv7 [pv2,pv5,pv185323], .c 569, .c 3, .c 419,
  .p pv19 [pv2,pv3,pv17,pv18169], .c 3, .c 7, .c 5, .c 3, .c 59, .c 53, .c 3, .c 5, .c 7, .c 3,
  .c 79, .p pv3 [pv2,pv3,pv149,pv691], .c 3, .c 13, .c 11, .c 3, .c 31, .c 5, .c 3, .c 19,
  .p pv7 [pv2,pv3,pv5,pv11,pv13], .c 3, .c 5, .c 67, .c 3, .c 11, .c 13, .c 3, .c 229, .c 7, .c 3,
  .c 29, .c 5, .c 3, .p pv2 [pv2,pv59,pv7853], .c 127, .c 3, .c 5, .c 19, .c 3,
  .p pv13 [pv2,pv5,pv7,pv6619], .c 17, .c 3, .c 7, .p pv17 [pv2,pv3,pv38611], .c 3,
  .p pv2 [pv2,pv13,pv29,pv1229], .c 5, .c 3, .p pv2 [pv2,pv926669], .c 7, .c 3, .c 5, .c 107,
  .c 3, .c 47, .c 223, .c 3, .c 11, .c 307, .c 3, .c 23, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5,
  .p pv17 [pv2,pv3,pv7,pv197], .c 3, .p pv2 [pv2,pv5,pv92669], .c 7, .c 3,
  .p pv2 [pv2,pv23,pv43,pv937], .c 463, .c 3, .c 19, .c 5, .c 3, .p pv7 [pv2,pv47,pv19717], .c 11,
  .c 3, .c 5, .c 277, .c 3, .c 7, .c 1297, .c 3, .c 883, .c 29, .c 3, .c 11, .c 5, .c 3, .c 43,
  .c 19, .c 3, .c 5, .c 373, .c 3, .c 37,
]
private theorem h0226c07 : checkBlock 1853187 128 b0226c07 = true := by
  decide +kernel

private def b0226c08 : List Row := [
  .p pv3 [pv2,pv3,pv17,pv673], .c 3, .p pv5 [pv2,pv7,pv41,pv3229], .c 13, .c 3, .c 7, .c 5, .c 3,
  .c 17, .p pv37 [pv2,pv3,pv5,pv7,pv1471], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv73,pv2539],
  .c 83, .c 3, .c 29, .p pv3 [pv2,pv3,pv11,pv23,pv37], .c 3, .p pv2 [pv2,pv926741], .c 5, .c 3,
  .c 11, .c 1217, .c 3, .c 5, .p pv5 [pv2,pv3,pv8581], .c 3, .c 13, .p pv3 [pv2,pv3,pv7,pv44131],
  .c 3, .c 19, .c 7, .c 3, .p pv3 [pv2,pv443,pv523], .c 5, .c 3, .c 131, .c 31, .c 3, .c 5, .c 13,
  .c 3, .c 241, .c 11, .c 3, .c 7, .c 47, .c 3, .c 73, .c 5, .c 3, .p pv2 [pv2,pv463387], .c 7,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv83,pv1861], .c 3, .c 17, .p pv2 [pv2,pv3,pv308927], .c 3, .c 1061,
  .c 41, .c 3, .c 97, .c 5, .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv30893], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv47,pv313], .c 3, .p pv11 [pv2,pv5,pv185359], .c 7, .c 3, .c 71, .c 11,
  .c 3, .c 59, .c 5, .c 3, .c 1091, .p pv3 [pv2,pv3,pv5,pv11,pv41,pv137], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv23,pv73], .c 3, .c 7, .c 919, .c 3, .p pv5 [pv2,pv37,pv677], .c 17, .c 3,
  .c 47, .c 5, .c 3, .c 23, .p pv17 [pv2,pv3,pv5,pv19,pv271], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv17,pv1069], .c 3, .c 29, .c 101, .c 3, .c 13, .c 19, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv61,pv71,pv107], .p pv3 [pv2,pv3,pv5,pv7,pv13,pv97], .c 3, .c 5, .c 7, .c 3,
  .c 461, .c 13, .c 3, .c 11, .c 67, .c 3, .c 1171, .c 5, .c 3,
]
private theorem h0226c08 : checkBlock 1853443 128 b0226c08 = true := by
  decide +kernel

private def b0226c09 : List Row := [
  .c 157, .p pv2 [pv2,pv3,pv5,pv37,pv167], .c 3, .c 5, .c 31, .c 3, .p pv23 [pv2,pv5,pv185371],
  .p pv5 [pv2,pv3,pv7,pv613], .c 3, .c 367, .c 7, .c 3, .p pv2 [pv2,pv13,pv83,pv859], .c 5, .c 3,
  .c 61, .c 11, .c 3, .c 5, .c 37, .c 3, .c 257, .p pv5 [pv2,pv3,pv11,pv28087], .c 3, .c 7,
  .p pv29 [pv2,pv3,pv13,pv17,pv233], .c 3, .c 11, .c 5, .c 3, .p pv13 [pv2,pv926879], .c 7, .c 3,
  .c 5, .c 29, .c 3, .p pv2 [pv2,pv5,pv197,pv941], .c 19, .c 3, .c 23,
  .p pv3 [pv2,pv3,pv509,pv607], .c 3, .c 547, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv61,pv1013],
  .c 3, .c 5, .c 11, .c 3, .p pv7 [pv2,pv5,pv13,pv23,pv31], .c 7, .c 3, .p pv5 [pv2,pv926903],
  .p pv7 [pv2,pv3,pv11,pv3511], .c 3, .c 13, .c 5, .c 3, .c 11, .c 47, .c 3, .c 5, .c 151, .c 3,
  .c 7, .c 17, .c 3, .c 337, .c 13, .c 3, .c 139, .c 5, .c 3, .c 19, .c 61, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv41,pv157], .c 3, .p pv17 [pv2,pv5,pv92693], .c 11, .c 3, .c 17, .c 23, .c 3,
  .c 7, .c 5, .c 3, .p pv11 [pv2,pv13,pv113,pv631], .c 71, .c 3, .c 5, .c 7, .c 3, .c 13, .c 31,
  .c 3, .c 41, .c 313, .c 3, .c 179, .c 5, .c 3, .c 227, .c 271, .c 3, .c 5, .c 13, .c 3, .c 449,
  .c 239, .c 3, .p pv5 [pv2,pv926963], .c 7, .c 3, .c 283, .c 5, .c 3,
  .p pv2 [pv2,pv23,pv41,pv983], .c 29, .c 3, .c 5, .p pv3 [pv2,pv3,pv127,pv811], .c 3, .c 11,
  .c 691,
]
private theorem h0226c09 : checkBlock 1853699 128 b0226c09 = true := by
  decide +kernel

private def b0226c10 : List Row := [
  .c 3, .c 7, .c 37, .c 3, .c 19, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .p pv13 [pv2,pv3,pv77249],
  .c 3, .c 73, .c 181, .c 3, .p pv2 [pv2,pv17,pv31,pv1759], .c 107, .c 3, .c 53, .c 5, .c 3, .c 7,
  .c 19, .c 3, .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv185401], .c 7, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv103001], .c 3, .c 71, .c 5, .c 3, .p pv3 [pv2,pv11,pv29,pv1453], .c 43, .c 3,
  .c 5, .c 17, .c 3, .c 7, .c 131, .c 3, .c 13, .c 457, .c 3, .c 23, .c 5, .c 3, .c 769, .c 11,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv309011], .c 3, .c 17, .c 13, .c 3, .c 19, .c 31, .c 3, .c 7, .c 5,
  .c 3, .p pv3 [pv2,pv17,pv13633], .c 67, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv18541], .c 47,
  .c 3, .c 37, .p pv2 [pv2,pv3,pv51503], .c 3, .p pv3 [pv2,pv13,pv4457], .c 5, .c 3,
  .p pv7 [pv2,pv7,pv132437], .c 139, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv79,pv2347],
  .c 317, .c 3, .c 83, .c 7, .c 3, .c 41, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv17,pv61,pv149], .c 3, .c 991, .p pv3 [pv2,pv3,pv239,pv431], .c 3, .c 7,
  .c 1303, .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv927089], .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv309031], .c 3, .c 19, .c 11, .c 3, .c 47, .c 109, .c 3, .c 13, .c 5, .c 3,
  .c 7,
]
private theorem h0226c10 : checkBlock 1853955 128 b0226c10 = true := by
  decide +kernel

private def b0226c11 : List Row := [
  .p pv2 [pv2,pv3,pv5,pv19,pv3253], .c 3, .c 5, .c 61, .c 3, .p pv2 [pv2,pv5,pv83,pv1117], .c 7,
  .c 3, .p pv5 [pv2,pv11,pv89,pv947], .c 13, .c 3, .p pv3 [pv2,pv231779], .c 5, .c 3, .c 521,
  .c 17, .c 3, .c 5, .p pv3 [pv2,pv3,pv43,pv7187], .c 3, .c 7, .c 557, .c 3,
  .p pv3 [pv2,pv115891], .c 11, .c 3, .c 1237, .c 5, .c 3, .p pv2 [pv2,pv13,pv211],
  .p pv19 [pv2,pv3,pv5,pv11,pv1873], .c 3, .c 5, .p pv7 [pv2,pv3,pv154523], .c 3, .c 11, .c 23,
  .c 3, .c 509, .c 29, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv927149], .c 719, .c 3, .c 5, .c 7,
  .c 3, .c 53, .p pv7 [pv2,pv3,pv77263], .c 3, .p pv2 [pv2,pv463579], .c 281, .c 3, .c 937, .c 5,
  .c 3, .c 23, .p pv3 [pv2,pv3,pv5,pv113,pv547], .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv439], .c 3,
  .p pv3 [pv2,pv5,pv92717], .c 17, .c 3, .c 11, .c 7, .c 3, .p pv3 [pv2,pv23,pv5039], .c 5, .c 3,
  .c 13, .c 197, .c 3, .c 5, .c 79, .c 3, .c 569, .p pv2 [pv2,pv3,pv13,pv11887], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv71,pv1451], .c 3, .p pv5 [pv2,pv927191], .c 5, .c 3, .c 31, .c 7, .c 3, .c 5,
  .c 293, .c 3, .c 239, .c 37, .c 3, .p pv5 [pv2,pv409,pv2267], .p pv13 [pv2,pv3,pv77267], .c 3,
  .c 11, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 773, .c 3, .c 151, .c 7, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv19,pv16267], .c 3, .c 113, .c 5, .c 3, .c 71, .c 31, .c 3, .c 5, .c 11, .c 3,
  .c 7, .c 13, .c 3,
]
private theorem h0226c11 : checkBlock 1854211 128 b0226c11 = true := by
  decide +kernel

private def b0226c12 : List Row := [
  .c 23, .c 83, .c 3, .c 829, .c 5, .c 3, .c 11, .c 199, .c 3, .c 5, .p pv3 [pv2,pv3,pv269,pv383],
  .c 3, .p pv2 [pv2,pv5,pv11,pv23,pv733], .c 67, .c 3, .p pv3 [pv2,pv7,pv17,pv487], .c 283, .c 3,
  .c 7, .c 5, .c 3, .c 631, .c 337, .c 3, .c 5, .c 7, .c 3, .c 29, .c 11, .c 3,
  .p pv5 [pv2,pv47,pv109,pv181], .p pv11 [pv2,pv3,pv13,pv743], .c 3, .c 19, .c 5, .c 3, .c 433,
  .c 13, .c 3, .c 5, .c 17, .c 3, .c 37, .c 41, .c 3, .c 761, .c 7, .c 3,
  .p pv2 [pv2,pv101,pv9181], .c 5, .c 3, .c 137, .c 19, .c 3, .c 5, .c 727, .c 3, .c 17, .c 61,
  .c 3, .c 7, .c 11, .c 3, .c 13, .c 5, .c 3, .p pv13 [pv2,pv17,pv54547], .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv13,pv31,pv59], .c 3, .c 11, .p pv11 [pv2,pv3,pv51517], .c 3,
  .p pv3 [pv2,pv231827], .c 13, .c 3, .p pv5 [pv2,pv7,pv11,pv12043], .c 5, .c 3, .c 7, .c 107,
  .c 3, .c 5, .c 29, .c 3, .c 157, .c 7, .c 3, .c 19, .c 17, .c 3, .p pv2 [pv2,pv463663], .c 5,
  .c 3, .p pv2 [pv2,pv13,pv71333], .p pv2 [pv2,pv3,pv5,pv30911], .c 3, .c 5, .c 47, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv38639], .c 3, .c 11, .p pv3 [pv2,pv3,pv7,pv44159], .c 3, .c 17, .c 5, .c 3,
  .p pv3 [pv2,pv11,pv479], .c 223, .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv17,pv1091],
  .p pv5 [pv2,pv3,pv167,pv617], .c 3, .c 181, .p pv7 [pv2,pv3,pv127,pv1217], .c 3, .c 7, .c 5,
  .c 3, .c 43, .c 11,
]
private theorem h0226c12 : checkBlock 1854467 128 b0226c12 = true := by
  decide +kernel

private def b0226c13 : List Row := [
  .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv31,pv193], .c 71, .c 3, .c 97, .p pv2 [pv2,pv3,pv107],
  .c 3, .c 11, .c 5, .c 3, .c 13, .c 17, .c 3, .c 5, .c 811, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv7,pv13,pv43,pv79], .c 3, .c 317, .c 7, .c 3, .c 37, .c 5, .c 3,
  .p pv2 [pv2,pv463,pv2003], .p pv7 [pv2,pv3,pv5,pv19,pv1627], .c 3, .c 5, .c 11, .c 3,
  .p pv7 [pv2,pv5,pv7,pv26497], .p pv5 [pv2,pv3,pv31,pv277], .c 3, .c 7, .c 19, .c 3, .c 1013,
  .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 227, .c 3, .c 1093, .c 31, .c 3, .c 13, .c 131, .c 3,
  .p pv3 [pv2,pv7,pv16561], .c 5, .c 3, .c 7, .c 53, .c 3, .c 5, .c 37, .c 3,
  .p pv2 [pv2,pv5,pv37097], .c 7, .c 3, .c 73, .p pv2 [pv2,pv3,pv23,pv13441], .c 3,
  .p pv5 [pv2,pv927431], .c 5, .c 3, .c 29, .c 1289, .c 3, .c 5, .c 547, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv103049], .c 3, .c 17, .p pv59 [pv2,pv3,pv7,pv61,pv181], .c 3,
  .p pv2 [pv2,pv13,pv35671], .c 5, .c 3, .p pv2 [pv2,pv29,pv31981], .c 59, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv173,pv1787], .c 3, .p pv11 [pv2,pv5,pv185491], .c 19, .c 3,
  .p pv2 [pv2,pv7,pv31,pv2137], .c 11, .c 3, .c 7, .c 5, .c 3, .c 373, .c 13, .c 3, .c 5, .c 7,
  .c 3, .c 11, .p pv5 [pv2,pv3,pv309157], .c 3, .c 31, .c 47, .c 3, .c 359, .c 5, .c 3, .c 787,
  .c 827, .c 3, .c 5, .c 83, .c 3, .p pv2 [pv2,pv5,pv13,pv19,pv751], .c 23, .c 3, .c 43,
]
private theorem h0226c13 : checkBlock 1854723 128 b0226c13 = true := by
  decide +kernel

private def b0226c14 : List Row := [
  .c 7, .c 3, .c 13, .c 5, .c 3, .c 17, .p pv13 [pv2,pv3,pv5,pv20611], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv13,pv23,pv47], .c 3, .p pv3 [pv2,pv5,pv7,pv53], .c 73, .c 3, .c 7, .c 13,
  .c 3, .p pv2 [pv2,pv463753], .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 19, .c 3,
  .p pv23 [pv2,pv5,pv103,pv1801], .p pv7 [pv2,pv3,pv37,pv2089], .c 3, .c 809,
  .p pv3 [pv2,pv3,pv309173], .c 3, .c 29, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 17, .c 3, .c 13,
  .c 7, .c 3, .c 101, .c 37, .c 3, .c 11, .c 5, .c 3, .c 173, .c 523, .c 3, .c 5, .c 13, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv154591], .c 3, .p pv3 [pv2,pv67,pv3461], .p pv3 [pv2,pv3,pv7,pv14723],
  .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv17,pv27281], .c 23, .c 3, .c 5, .c 11, .c 3, .c 113,
  .p pv5 [pv2,pv3,pv19,pv16273], .c 3, .c 41, .c 229, .c 3, .c 7, .c 5, .c 3, .c 11, .c 19, .c 3,
  .c 5, .c 7, .c 3, .c 313, .p pv5 [pv2,pv3,pv13,pv991], .c 3, .c 23, .c 17, .c 3, .c 67, .c 5,
  .c 3, .p pv11 [pv2,pv7,pv41,pv101], .p pv3 [pv2,pv3,pv5,pv6871], .c 3, .c 5, .c 1153, .c 3,
  .c 397, .c 11, .c 3, .p pv2 [pv2,pv151,pv6143], .c 7, .c 3, .c 17, .c 5, .c 3, .c 149, .c 307,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv103067], .c 3, .p pv2 [pv2,pv5,pv7,pv17,pv1559], .c 929, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv241,pv1283], .c 3, .c 733, .c 5, .c 3, .p pv2 [pv2,pv463807], .c 7,
  .c 3,
]
private theorem h0226c14 : checkBlock 1854979 128 b0226c14 = true := by
  decide +kernel

private def b0226c15 : List Row := [
  .c 5, .p pv5 [pv2,pv3,pv19,pv79,pv103], .c 3, .c 463, .c 13, .c 3, .p pv5 [pv2,pv29,pv1103],
  .c 11, .c 3, .p pv2 [pv2,pv7,pv173,pv383], .c 5, .c 3, .c 7, .c 17, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv163,pv271], .c 3, .c 11, .c 7, .c 3, .c 199,
  .p pv19 [pv2,pv3,pv17,pv43,pv47], .c 3, .c 257, .c 5, .c 3, .c 109, .c 37, .c 3, .c 5, .c 67,
  .c 3, .c 7, .p pv3 [pv2,pv3,pv373,pv829], .c 3, .p pv2 [pv2,pv927653], .c 193, .c 3,
  .p pv5 [pv2,pv17,pv19,pv359], .c 5, .c 3, .c 31, .c 13, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv28111], .c 3, .c 19, .c 29, .c 3, .c 11, .c 103, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv149,pv283], .c 1181, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv13,pv223],
  .c 17, .c 3, .c 557, .c 19, .c 3, .c 13, .c 5, .c 3, .c 233, .c 11, .c 3, .c 5, .c 23, .c 3,
  .c 29, .p pv5 [pv2,pv3,pv7,pv11,pv251], .c 3, .c 17, .c 7, .c 3, .c 11, .c 5, .c 3, .c 347,
  .p pv3 [pv2,pv3,pv5,pv23,pv2689], .c 3, .c 5, .c 997, .c 3, .p pv2 [pv2,pv5,pv7,pv29,pv457],
  .p pv5 [pv2,pv3,pv103079], .c 3, .c 7, .c 163, .c 3, .c 23, .c 5, .c 3, .c 37, .c 7, .c 3, .c 5,
  .c 11, .c 3, .c 13, .c 709, .c 3, .p pv3 [pv2,pv23,pv2521], .c 241, .c 3,
  .p pv5 [pv2,pv7,pv132533], .c 5, .c 3, .c 7, .c 101, .c 3, .c 5, .c 13, .c 3, .c 1277, .c 7,
  .c 3, .c 107, .c 491,
]
private theorem h0226c15 : checkBlock 1855235 128 b0226c15 = true := by
  decide +kernel

private def b0226c16 : List Row := [
  .c 3, .c 43, .c 5, .c 3, .c 17, .p pv13 [pv2,pv3,pv5,pv1237], .c 3, .c 5, .c 29, .c 3, .c 7,
  .c 11, .c 3, .p pv2 [pv2,pv13,pv17,pv2099], .p pv3 [pv2,pv3,pv7,pv44179], .c 3,
  .p pv2 [pv2,pv337,pv2753], .c 5, .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv53,pv389], .c 3, .c 5,
  .c 41, .c 3, .p pv2 [pv2,pv5,pv19,pv257], .c 197, .c 3, .c 701, .p pv2 [pv2,pv3,pv23,pv83],
  .c 3, .c 7, .c 5, .c 3, .c 19, .c 89, .c 3, .c 5, .c 7, .c 3, .c 23, .c 113, .c 3,
  .p pv3 [pv2,pv231947], .c 11, .c 3, .c 53, .c 5, .c 3, .p pv2 [pv2,pv7,pv66271],
  .p pv17 [pv2,pv3,pv5,pv11,pv5623], .c 3, .c 5, .c 19, .c 3, .c 11, .p pv5 [pv2,pv3,pv7,pv4909],
  .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv11,pv181,pv233], .c 5, .c 3, .c 41,
  .p pv7 [pv2,pv3,pv5,pv13,pv61], .c 3, .c 5, .p pv2 [pv2,pv3,pv309271], .c 3, .c 79, .c 13, .c 3,
  .c 7, .c 151, .c 3, .c 251, .c 5, .c 3, .p pv3 [pv2,pv103,pv563], .c 7, .c 3, .c 5, .c 677,
  .c 3, .c 37, .c 23, .c 3, .c 11, .c 17, .c 3, .c 19, .c 5, .c 3, .c 7, .c 29, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv17,pv23,pv113], .c 3, .c 31, .c 7, .c 3, .p pv3 [pv2,pv115981], .c 67,
  .c 3, .c 17, .c 5, .c 3, .c 23, .c 11, .c 3, .c 5, .c 449, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv11,pv31,pv907], .c 3, .c 59, .p pv11 [pv2,pv3,pv7,pv263], .c 3, .c 11, .c 5,
  .c 3, .c 29, .p pv7 [pv2,pv3,pv5,pv157,pv197], .c 3, .c 5,
]
private theorem h0226c16 : checkBlock 1855491 128 b0226c16 = true := by
  decide +kernel

private def b0226c17 : List Row := [
  .p pv3 [pv2,pv3,pv131,pv787], .c 3, .c 43, .c 31, .c 3, .p pv2 [pv2,pv7,pv191,pv347],
  .p pv11 [pv2,pv3,pv309293], .c 3, .c 7, .c 5, .c 3, .p pv7 [pv2,pv19,pv29,pv421], .c 17, .c 3,
  .c 5, .c 7, .c 3, .c 499, .c 41, .c 3, .c 19, .c 13, .c 3, .c 181, .c 5, .c 3, .c 11, .c 23,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv19,pv73,pv223], .c 3, .p pv11 [pv2,pv5,pv11,pv16871],
  .p pv5 [pv2,pv3,pv7,pv22093], .c 3, .p pv3 [pv2,pv229,pv1013], .c 7, .c 3,
  .p pv5 [pv2,pv17,pv54583], .c 5, .c 3, .c 1279, .c 269, .c 3, .c 5, .c 43, .c 3, .c 13, .c 11,
  .c 3, .c 7, .p pv11 [pv2,pv3,pv53,pv1459], .c 3, .p pv2 [pv2,pv463963], .c 5, .c 3, .c 337,
  .c 7, .c 3, .c 5, .c 13, .c 3, .c 167, .c 17, .c 3, .c 31, .c 73, .c 3, .c 37, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv17,pv1213], .c 3, .c 5, .c 157, .c 3, .c 19, .c 7, .c 3, .c 17, .c 11,
  .c 3, .c 29, .c 5, .c 3, .c 13, .p pv23 [pv2,pv3,pv5,pv11,pv19,pv37], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv34369], .c 3, .c 7, .p pv19 [pv2,pv3,pv13,pv11897], .c 3, .c 197, .c 19, .c 3,
  .c 109, .c 5, .c 3, .p pv2 [pv2,pv463987], .p pv3 [pv2,pv3,pv5,pv12373], .c 3, .c 5, .c 37,
  .c 3, .p pv3 [pv2,pv5,pv46399], .c 59, .c 3, .c 67, .p pv7 [pv2,pv3,pv19333], .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv127,pv7307], .p pv11 [pv2,pv3,pv5,pv7,pv491], .c 3, .c 5, .c 7, .c 3,
  .c 263, .p pv47 [pv2,pv3,pv17,pv4549], .c 3, .c 11, .p pv3 [pv2,pv3,pv97,pv1063], .c 3,
]
private theorem h0226c17 : checkBlock 1855747 128 b0226c17 = true := by
  decide +kernel

private def b0226c18 : List Row := [
  .p pv2 [pv2,pv928001], .c 5, .c 3, .c 17, .c 71, .c 3, .c 5, .p pv5 [pv2,pv3,pv12889], .c 3,
  .p pv2 [pv2,pv5,pv92801], .c 13, .c 3, .p pv2 [pv2,pv17,pv79,pv691], .c 7, .c 3,
  .p pv3 [pv2,pv31,pv1871], .c 5, .c 3, .p pv11 [pv2,pv167,pv5557], .c 11, .c 3, .c 5, .c 61,
  .c 3, .c 179, .c 19, .c 3, .c 7, .p pv2 [pv2,pv3,pv29,pv10667], .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv37,pv12541], .c 7, .c 3, .c 5, .c 17, .c 3, .c 59, .p pv2 [pv2,pv3,pv71,pv4357],
  .c 3, .c 29, .p pv17 [pv2,pv3,pv13,pv661], .c 3, .c 149, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5,
  .c 11, .c 3, .c 17, .c 7, .c 3, .c 173, .p pv3 [pv2,pv3,pv11,pv28123], .c 3, .c 23, .c 5, .c 3,
  .c 11, .c 829, .c 3, .c 5, .p pv5 [pv2,pv3,pv77339], .c 3, .c 7, .c 991, .c 3,
  .p pv2 [pv2,pv23,pv40351], .p pv2 [pv2,pv3,pv7,pv19,pv1163], .c 3, .c 13, .c 5, .c 3,
  .p pv7 [pv2,pv928079], .c 109, .c 3, .c 5, .c 19, .c 3, .c 47, .c 11, .c 3, .c 277, .c 13, .c 3,
  .c 7, .c 5, .c 3, .c 421, .p pv7 [pv2,pv3,pv5,pv7,pv8839], .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv9281], .c 29, .c 3, .p pv5 [pv2,pv11,pv139,pv607], .c 577, .c 3, .c 17, .c 5,
  .c 3, .c 53, .p pv2 [pv2,pv3,pv5,pv30937], .c 3, .c 5, .p pv2 [pv2,pv3,pv309371], .c 3, .c 13,
  .p pv5 [pv2,pv3,pv7,pv29,pv127], .c 3, .p pv2 [pv2,pv107,pv4337], .c 7, .c 3, .c 19, .c 5, .c 3,
  .c 31, .c 113, .c 3, .c 5, .c 13,
]
private theorem h0226c18 : checkBlock 1856003 128 b0226c18 = true := by
  decide +kernel

private def b0226c19 : List Row := [
  .c 3, .c 11, .c 79, .c 3, .c 7, .p pv11 [pv2,pv3,pv51563], .c 3, .c 89, .c 5, .c 3, .c 101,
  .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv281,pv367], .c 3, .c 61, .p pv7 [pv2,pv3,pv154691], .c 3,
  .p pv3 [pv2,pv13,pv1373], .c 859, .c 3, .p pv5 [pv2,pv7,pv67,pv1979], .c 5, .c 3, .c 7, .c 31,
  .c 3, .c 5, .c 59, .c 3, .c 571, .c 7, .c 3, .c 11, .c 191, .c 3, .p pv2 [pv2,pv17,pv27299],
  .c 5, .c 3, .p pv2 [pv2,pv11,pv19,pv4441], .c 643, .c 3, .c 5, .p pv3 [pv2,pv3,pv309391], .c 3,
  .c 7, .c 23, .c 3, .c 19, .c 47, .c 3, .p pv2 [pv2,pv89,pv10429], .c 5, .c 3, .c 67, .c 11,
  .c 3, .c 5, .c 29, .c 3, .c 619, .c 17, .c 3, .c 13, .c 359, .c 3, .c 7, .c 5, .c 3, .c 23,
  .c 37, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv185641], .c 13, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv309403], .c 3, .c 241, .c 5, .c 3, .c 307, .c 53, .c 3, .c 5, .c 11, .c 3,
  .p pv7 [pv2,pv5,pv46411], .p pv2 [pv2,pv3,pv7,pv44201], .c 3, .c 461, .c 7, .c 3, .c 47, .c 5,
  .c 3, .c 11, .c 83, .c 3, .c 5, .c 193, .c 3, .c 19, .c 1327, .c 3, .c 7, .c 653, .c 3, .c 97,
  .c 5, .c 3, .c 601, .c 7, .c 3, .c 5, .c 31, .c 3, .c 1283, .c 11, .c 3, .p pv2 [pv2,pv928253],
  .c 19, .c 3, .p pv3 [pv2,pv7,pv37],
]
private theorem h0226c19 : checkBlock 1856259 128 b0226c19 = true := by
  decide +kernel

private def b0226c20 : List Row := [
  .c 5, .c 3, .c 7, .c 41, .c 3, .c 5, .c 1301, .c 3, .c 439, .c 7, .c 3, .c 23, .c 167, .c 3,
  .c 13, .c 5, .c 3, .c 37, .c 29, .c 3, .c 5, .c 107, .c 3, .c 7, .c 1151, .c 3, .c 281, .c 11,
  .c 3, .c 503, .c 5, .c 3, .c 71, .p pv7 [pv2,pv3,pv5,pv11,pv29,pv97], .c 3, .c 5, .c 17, .c 3,
  .c 11, .c 941, .c 3, .c 109, .p pv17 [pv2,pv3,pv309433], .c 3, .c 7, .c 5, .c 3, .c 29, .c 43,
  .c 3, .c 5, .c 7, .c 3, .c 13, .c 19, .c 3, .c 83, .c 23, .c 3, .c 227, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv17,pv29,pv269], .c 47, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv71,pv523],
  .c 367, .c 3, .c 11, .c 7, .c 3, .c 131, .c 5, .c 3, .c 317, .c 59, .c 3, .c 5, .c 97, .c 3,
  .c 587, .c 31, .c 3, .c 7, .c 17, .c 3, .c 1039, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 839,
  .c 3, .c 191, .p pv17 [pv2,pv3,pv11,pv13,pv541], .c 3, .c 691, .p pv3 [pv2,pv3,pv19,pv61,pv89],
  .c 3, .c 11, .c 5, .c 3, .c 7, .c 277, .c 3, .c 5, .c 19, .c 3, .c 293, .c 7, .c 3,
  .p pv2 [pv2,pv773,pv1201], .c 53, .c 3, .p pv3 [pv2,pv116047], .c 5, .c 3,
  .p pv7 [pv2,pv727,pv1277], .c 137, .c 3, .c 5, .c 11, .c 3,
]
private theorem h0226c20 : checkBlock 1856515 128 b0226c20 = true := by
  decide +kernel

private def b0226c21 : List Row := [
  .c 7, .p pv2 [pv2,pv3,pv51577], .c 3, .c 13, .c 61, .c 3, .c 29, .c 5, .c 3, .c 11, .c 17, .c 3,
  .c 5, .c 347, .c 3, .p pv13 [pv2,pv5,pv11,pv211], .c 13, .c 3, .c 31, .c 173, .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv928409], .p pv2 [pv2,pv3,pv5,pv7,pv4421], .c 3, .c 5, .c 7, .c 3, .c 1031,
  .c 11, .c 3, .p pv3 [pv2,pv23,pv20183], .c 157, .c 3, .p pv2 [pv2,pv13,pv17,pv4201], .c 5, .c 3,
  .c 41, .c 19, .c 3, .c 5, .p pv5 [pv2,pv3,pv77369], .c 3, .p pv3 [pv2,pv5,pv227,pv409], .c 71,
  .c 3, .c 127, .c 7, .c 3, .c 167, .c 5, .c 3, .c 181, .c 13, .c 3, .c 5, .c 983, .c 3,
  .p pv7 [pv2,pv5,pv7,pv41,pv647], .c 17, .c 3, .c 7, .c 11, .c 3, .p pv5 [pv2,pv191,pv4861],
  .c 5, .c 3, .p pv2 [pv2,pv19,pv53,pv461], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv51581], .c 3,
  .c 11, .c 47, .c 3, .c 17, .c 113, .c 3, .c 13, .c 5, .c 3, .c 7, .p pv37 [pv2,pv3,pv5,pv30949],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv13,pv19,pv179], .c 3, .c 23, .c 7, .c 3, .c 29, .c 13, .c 3,
  .p pv2 [pv2,pv31,pv61,pv491], .c 5, .c 3, .p pv3 [pv2,pv97,pv2393],
  .p pv2 [pv2,pv3,pv5,pv47,pv439], .c 3, .c 5, .c 641, .c 3, .c 7, .p pv3 [pv2,pv3,pv173,pv1789],
  .c 3, .c 11, .p pv2 [pv2,pv3,pv7,pv7369], .c 3, .c 31, .c 5, .c 3,
  .p pv11 [pv2,pv11,pv13,pv43,pv151], .p pv7 [pv2,pv3,pv5,pv619], .c 3, .c 5, .c 1093, .c 3,
  .c 13, .c 41, .c 3, .c 47, .c 1229, .c 3, .c 7, .c 5,
]
private theorem h0226c21 : checkBlock 1856771 128 b0226c21 = true := by
  decide +kernel

private def b0226c22 : List Row := [
  .c 3, .c 17, .c 11, .c 3, .c 5, .c 7, .c 3, .c 19, .c 23, .c 3, .c 73, .p pv7 [pv2,pv3,pv77377],
  .c 3, .c 11, .c 5, .c 3, .c 163, .c 1063, .c 3, .c 5, .c 37, .c 3, .c 929, .c 29, .c 3, .c 683,
  .c 7, .c 3, .c 479, .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv103,pv601], .c 3, .c 5, .c 11,
  .c 3, .p pv3 [pv2,pv5,pv7,pv379], .c 1213, .c 3, .c 7, .p pv13 [pv2,pv3,pv11,pv1279], .c 3,
  .p pv3 [pv2,pv23,pv10093], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 43, .c 3, .c 17, .c 353,
  .c 3, .c 433, .p pv2 [pv2,pv3,pv309523], .c 3, .c 59, .c 5, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv5,pv4127], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv22109], .c 3,
  .p pv3 [pv2,pv5,pv29,pv1601], .c 7, .c 3, .c 13, .p pv11 [pv2,pv3,pv1433], .c 3, .c 53, .c 5,
  .c 3, .c 31, .c 23, .c 3, .c 5, .c 131, .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv11,pv42209],
  .c 17, .c 3, .p pv2 [pv2,pv59,pv15739], .c 5, .c 3, .p pv3 [pv2,pv83,pv2797], .c 79, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv17,pv569], .c 3, .c 1097, .c 751, .c 3, .c 23, .c 11, .c 3, .c 7, .c 5, .c 3,
  .c 193, .c 31, .c 3, .c 5, .c 7, .c 3, .c 11, .c 541, .c 3, .p pv3 [pv2,pv43,pv5399], .c 41,
  .c 3, .c 1249, .c 5, .c 3, .c 19, .c 13, .c 3, .c 5, .c 977, .c 3, .p pv3 [pv2,pv5,pv1451],
]
private theorem h0226c22 : checkBlock 1857027 128 b0226c22 = true := by
  decide +kernel

private def b0226c23 : List Row := [
  .p pv2 [pv2,pv3,pv7,pv44221], .c 3, .p pv5 [pv2,pv928643], .c 7, .c 3,
  .p pv2 [pv2,pv311,pv1493], .c 5, .c 3, .c 43, .c 17, .c 3, .c 5, .c 19, .c 3, .c 1163,
  .p pv5 [pv2,pv3,pv6449], .c 3, .c 7, .c 23, .c 3, .c 13, .c 5, .c 3, .c 283, .c 7, .c 3, .c 5,
  .c 563, .c 3, .c 41, .p pv3 [pv2,pv3,pv23,pv43,pv313], .c 3, .p pv2 [pv2,pv47,pv19759], .c 13,
  .c 3, .p pv3 [pv2,pv7,pv17,pv1951], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 223, .c 3,
  .p pv2 [pv2,pv5,pv185737], .c 7, .c 3, .p pv3 [pv2,pv58043], .c 59, .c 3, .c 11, .c 5, .c 3,
  .c 61, .p pv3 [pv2,pv3,pv5,pv101,pv613], .c 3, .c 5, .c 953, .c 3, .c 7, .c 17, .c 3,
  .p pv5 [pv2,pv928703], .c 439, .c 3, .c 107, .c 5, .c 3, .c 229, .c 19, .c 3, .c 5, .c 11, .c 3,
  .c 71, .c 211, .c 3, .c 17, .p pv3 [pv2,pv3,pv11,pv53,pv59], .c 3, .c 7, .c 5, .c 3, .c 11,
  .c 151, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv11,pv8443], .c 571, .c 3, .c 157, .c 109,
  .c 3, .p pv3 [pv2,pv29023], .c 5, .c 3, .c 13, .p pv7 [pv2,pv3,pv5,pv23,pv673], .c 3, .c 5,
  .c 47, .c 3, .c 53, .c 11, .c 3, .c 19, .c 7, .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv29,pv67,pv239], .c 37, .c 3, .c 5, .p pv2 [pv2,pv3,pv19,pv8147], .c 3,
  .p pv3 [pv2,pv5,pv7,pv31,pv107], .c 971, .c 3, .c 7, .c 911, .c 3, .p pv2 [pv2,pv464383], .c 5,
  .c 3,
]
private theorem h0226c23 : checkBlock 1857283 128 b0226c23 = true := by
  decide +kernel

private def b0226c24 : List Row := [
  .c 17, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv41,pv839], .c 3, .c 31, .p pv5 [pv2,pv3,pv38699],
  .c 3, .c 13, .c 11, .c 3, .c 397, .c 5, .c 3, .c 7, .c 1117, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv11057], .c 3, .c 11, .c 7, .c 3, .c 41, .p pv2 [pv2,pv3,pv154799], .c 3,
  .p pv3 [pv2,pv11,pv19,pv101], .c 5, .c 3, .p pv7 [pv2,pv928799], .c 761, .c 3, .c 5, .c 17,
  .c 3, .c 7, .c 31, .c 3, .p pv3 [pv2,pv116101], .c 619, .c 3, .c 83, .c 5, .c 3, .c 127, .c 73,
  .c 3, .c 5, .c 1019, .c 3, .c 17, .c 43, .c 3, .c 11, .c 19, .c 3, .c 7, .c 5, .c 3, .c 37,
  .c 13, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv185767], .p pv43 [pv2,pv3,pv25801], .c 3,
  .p pv2 [pv2,pv464419], .p pv3 [pv2,pv3,pv409,pv757], .c 3, .c 1087, .c 5, .c 3,
  .p pv13 [pv2,pv7,pv677], .c 11, .c 3, .c 5, .c 89, .c 3, .p pv2 [pv2,pv5,pv13,pv1429], .c 53,
  .c 3, .p pv2 [pv2,pv19,pv31,pv83], .c 7, .c 3, .c 11, .c 5, .c 3, .p pv13 [pv2,pv928859],
  .c 659, .c 3, .c 5, .c 349, .c 3, .p pv2 [pv2,pv5,pv7,pv26539], .c 23, .c 3, .c 7, .c 13, .c 3,
  .c 17, .c 5, .c 3, .c 1291, .c 7, .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv17,pv683], .c 19,
  .c 3, .p pv5 [pv2,pv928883], .c 29, .c 3, .p pv2 [pv2,pv7,pv43,pv1543], .c 5, .c 3, .c 7,
  .c 157, .c 3, .c 5, .c 617, .c 3, .c 13, .c 7,
]
private theorem h0226c24 : checkBlock 1857539 128 b0226c24 = true := by
  decide +kernel

private def b0226c25 : List Row := [
  .c 3, .p pv2 [pv2,pv109,pv4261], .c 31, .c 3, .p pv2 [pv2,pv23,pv40387], .c 5, .c 3, .c 53,
  .c 17, .c 3, .c 5, .c 13, .c 3, .c 7, .c 11, .c 3, .c 29, .p pv11 [pv2,pv3,pv7,pv17,pv1301],
  .c 3, .c 41, .c 5, .c 3, .c 19, .c 97, .c 3, .c 5, .c 173, .c 3, .c 59, .c 257, .c 3, .c 71,
  .p pv2 [pv2,pv3,pv19,pv43,pv379], .c 3, .c 7, .c 5, .c 3, .c 13, .c 23, .c 3, .c 5, .c 7, .c 3,
  .c 37, .c 127, .c 3, .p pv5 [pv2,pv521,pv1783], .c 11, .c 3, .p pv2 [pv2,pv31,pv14983], .c 5,
  .c 3, .p pv2 [pv2,pv7,pv132707], .c 43, .c 3, .c 5, .c 197, .c 3, .c 11, .c 17, .c 3, .c 23,
  .c 7, .c 3, .c 31, .c 5, .c 3, .p pv3 [pv2,pv71,pv3271], .p pv2 [pv2,pv3,pv5,pv17,pv3643], .c 3,
  .c 5, .c 317, .c 3, .p pv2 [pv2,pv5,pv7,pv23,pv577], .c 29, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv107,pv1447], .c 3, .c 19, .c 5, .c 3, .p pv11 [pv2,pv928979], .c 7, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv11,pv28151], .c 3, .p pv2 [pv2,pv5,pv185797], .c 13, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv3823], .c 3, .c 269, .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 41, .c 3, .c 29,
  .c 7, .c 3, .p pv5 [pv2,pv929003], .c 23, .c 3, .c 139, .c 5, .c 3, .c 463, .c 11, .c 3, .c 5,
  .c 607, .c 3, .c 7, .p pv31 [pv2,pv3,pv11,pv17,pv23], .c 3, .c 163, .c 863, .c 3, .c 11, .c 5,
  .c 3, .c 17,
]
private theorem h0226c25 : checkBlock 1857795 128 b0226c25 = true := by
  decide +kernel

private def b0226c26 : List Row := [
  .c 13, .c 3, .c 5, .p pv13 [pv2,pv3,pv77419], .c 3, .p pv2 [pv2,pv5,pv61,pv1523], .c 199, .c 3,
  .c 19, .c 73, .c 3, .c 7, .c 5, .c 3, .c 41, .p pv47 [pv2,pv3,pv5,pv7,pv79], .c 3, .c 5, .c 7,
  .c 3, .p pv7 [pv2,pv5,pv13,pv14293], .p pv2 [pv2,pv3,pv154841], .c 3, .c 101, .c 691, .c 3,
  .c 13, .c 5, .c 3, .c 11, .c 67, .c 3, .c 5, .c 17, .c 3, .c 61, .c 109, .c 3, .c 53, .c 7,
  .c 3, .p pv2 [pv2,pv97,pv4789], .c 5, .c 3, .p pv2 [pv2,pv929069], .c 71, .c 3, .c 5, .c 23,
  .c 3, .c 17, .c 11, .c 3, .c 7, .c 43, .c 3, .p pv2 [pv2,pv19,pv107,pv457], .c 5, .c 3,
  .p pv3 [pv2,pv13,pv17,pv1051], .c 7, .c 3, .c 5, .c 37, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv61,pv5077], .c 3, .p pv2 [pv2,pv11,pv84463], .p pv23 [pv2,pv3,pv154849], .c 3,
  .c 23, .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv19,pv163], .c 3, .c 5, .c 13, .c 3,
  .p pv11 [pv2,pv5,pv185821], .c 7, .c 3, .p pv3 [pv2,pv23,pv10099], .c 11, .c 3, .c 103, .c 5,
  .c 3, .c 97, .c 89, .c 3, .c 5, .c 379, .c 3, .c 7, .c 41, .c 3, .c 271,
  .p pv11 [pv2,pv3,pv7,pv1229], .c 3, .c 17, .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv30971],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv103237], .c 3, .c 307, .c 809, .c 3, .c 211,
  .p pv3 [pv2,pv3,pv309713], .c 3, .c 7, .c 5, .c 3, .c 709, .c 29, .c 3, .c 5, .c 7, .c 3,
  .c 197, .p pv5 [pv2,pv3,pv11471], .c 3,
]
private theorem h0226c26 : checkBlock 1858051 128 b0226c26 = true := by
  decide +kernel

private def b0226c27 : List Row := [
  .c 11, .p pv2 [pv2,pv3,pv23,pv6733], .c 3, .p pv3 [pv2,pv67,pv3467], .c 5, .c 3,
  .p pv7 [pv2,pv7,pv11,pv1097], .c 17, .c 3, .c 5, .c 181, .c 3, .c 23, .c 19, .c 3, .c 13, .c 7,
  .c 3, .p pv5 [pv2,pv929171], .c 5, .c 3, .c 29, .c 11, .c 3, .c 5, .c 31, .c 3, .c 73, .c 13,
  .c 3, .c 7, .p pv11 [pv2,pv3,pv9679], .c 3, .c 11, .c 5, .c 3, .c 67, .c 7, .c 3, .c 5, .c 1279,
  .c 3, .c 127, .c 277, .c 3, .c 193, .c 37, .c 3, .p pv5 [pv2,pv7,pv13,pv10211], .c 5, .c 3,
  .c 7, .c 449, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv92921], .c 7, .c 3, .c 47, .c 103,
  .c 3, .p pv3 [pv2,pv14519], .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 19, .c 3, .c 7, .c 83,
  .c 3, .c 17, .p pv2 [pv2,pv3,pv7,pv44249], .c 3, .c 563, .c 5, .c 3, .c 23, .c 1319, .c 3, .c 5,
  .c 149, .c 3, .c 31, .c 11, .c 3, .c 61, .c 41, .c 3, .c 7, .c 5, .c 3, .c 293, .c 101, .c 3,
  .c 5, .c 7, .c 3, .c 113, .c 67, .c 3, .c 577, .c 13, .c 3, .c 19, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv8297], .p pv2 [pv2,pv3,pv5,pv41,pv1511], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv83,pv311], .c 3, .p pv2 [pv2,pv5,pv92927], .c 31, .c 3, .c 37, .c 7, .c 3,
  .p pv3 [pv2,pv29,pv8011], .c 5, .c 3, .c 17, .c 19,
]
private theorem h0226c27 : checkBlock 1858307 128 b0226c27 = true := by
  decide +kernel

private def b0226c28 : List Row := [
  .c 3, .c 5, .c 71, .c 3, .c 11, .p pv11 [pv2,pv3,pv17209], .c 3, .c 7,
  .p pv7 [pv2,pv3,pv307,pv1009], .c 3, .p pv5 [pv2,pv11,pv84481], .c 5, .c 3, .c 43, .c 7, .c 3,
  .c 5, .c 13, .c 3, .c 1297, .p pv2 [pv2,pv3,pv101,pv3067], .c 3, .c 23, .c 61, .c 3,
  .p pv2 [pv2,pv7,pv41,pv1619], .c 5, .c 3, .c 7, .c 37, .c 3, .c 5, .c 17, .c 3,
  .p pv11 [pv2,pv5,pv23,pv8081], .c 7, .c 3, .c 11, .c 29, .c 3, .p pv2 [pv2,pv389,pv2389], .c 5,
  .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv12391], .c 3, .c 5, .c 53, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv13,pv47], .c 3, .c 31, .p pv2 [pv2,pv3,pv7,pv29,pv109], .c 3, .c 769, .c 5,
  .c 3, .c 137, .c 11, .c 3, .c 5, .c 853, .c 3, .p pv2 [pv2,pv5,pv185869],
  .p pv2 [pv2,pv3,pv11,pv14081], .c 3, .c 29, .c 23, .c 3, .c 7, .c 5, .c 3, .c 47,
  .p pv3 [pv2,pv3,pv5,pv7,pv53,pv167], .c 3, .c 5, .c 7, .c 3, .p pv11 [pv2,pv5,pv11617], .c 157,
  .c 3, .c 13, .c 17, .c 3, .p pv2 [pv2,pv19,pv37,pv661], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv103,pv1289], .p pv23 [pv2,pv3,pv5,pv13,pv2383], .c 3, .c 5, .c 11, .c 3,
  .c 19, .c 13, .c 3, .p pv2 [pv2,pv47,pv9887], .c 7, .c 3, .c 17, .c 5, .c 3, .c 11, .c 1039,
  .c 3, .c 5, .c 109, .c 3, .c 67, .c 193, .c 3, .c 7, .c 19, .c 3, .c 229, .c 5, .c 3, .c 73,
  .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv37,pv2791], .c 3, .c 97, .c 11, .c 3, .c 41,
]
private theorem h0226c28 : checkBlock 1858563 128 b0226c28 = true := by
  decide +kernel

private def b0226c29 : List Row := [
  .p pv3 [pv2,pv3,pv13,pv23831], .c 3, .p pv5 [pv2,pv7,pv31,pv4283], .c 5, .c 3, .c 7, .c 13,
  .c 3, .c 5, .c 23, .c 3, .c 103, .c 7, .c 3, .c 43, .p pv7 [pv2,pv3,pv17,pv67], .c 3, .c 31,
  .c 5, .c 3, .c 199, .p pv2 [pv2,pv3,pv5,pv23,pv449], .c 3, .c 5, .p pv37 [pv2,pv3,pv309811],
  .c 3, .c 7, .p pv5 [pv2,pv3,pv73,pv1061], .c 3, .c 167, .c 11, .c 3, .c 13, .c 5, .c 3,
  .p pv3 [pv2,pv317,pv733], .p pv2 [pv2,pv3,pv5,pv11,pv43,pv131], .c 3, .c 5, .c 47, .c 3, .c 11,
  .c 19, .c 3, .c 313, .c 13, .c 3, .c 7, .c 5, .c 3, .p pv17 [pv2,pv929459],
  .p pv19 [pv2,pv3,pv5,pv7,pv2213], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv185893], .c 17,
  .c 3, .p pv3 [pv2,pv232367], .c 727, .c 3, .c 89, .c 5, .c 3, .c 79, .c 83, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv14083], .c 3, .c 13, .c 113, .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv59,pv7877], .c 5, .c 3, .c 19, .c 41, .c 3, .c 5, .c 13, .c 3, .c 37, .c 71, .c 3,
  .c 7, .c 479, .c 3, .c 191, .c 5, .c 3, .p pv3 [pv2,pv31,pv937], .c 7, .c 3, .c 5, .c 19, .c 3,
  .c 23, .p pv3 [pv2,pv3,pv11,pv41,pv229], .c 3, .c 283, .c 587, .c 3, .c 11, .c 5, .c 3, .c 7,
  .p pv23 [pv2,pv3,pv5,pv1291], .c 3, .c 5, .c 103, .c 3, .c 181, .c 7, .c 3,
  .p pv3 [pv2,pv116191], .c 269, .c 3, .c 41, .c 5, .c 3, .c 17, .p pv7 [pv2,pv3,pv5,pv31,pv1999],
  .c 3,
]
private theorem h0226c29 : checkBlock 1858819 128 b0226c29 = true := by
  decide +kernel

private def b0226c30 : List Row := [
  .c 5, .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv383,pv809], .c 3, .p pv37 [pv2,pv17,pv54679], .c 197,
  .c 3, .c 19, .c 5, .c 3, .c 11, .c 31, .c 3, .c 5, .c 79, .c 3, .p pv11 [pv2,pv5,pv11,pv16901],
  .c 23, .c 3, .c 13, .p pv11 [pv2,pv3,pv309853], .c 3, .c 7, .c 5, .c 3, .c 1301, .c 19, .c 3,
  .c 5, .c 7, .c 3, .p pv13 [pv2,pv5,pv92957], .c 11, .c 3, .c 263, .c 59, .c 3, .c 127, .c 5,
  .c 3, .c 23, .c 29, .c 3, .c 5, .p pv5 [pv2,pv3,pv34429], .c 3, .c 17,
  .p pv2 [pv2,pv3,pv7,pv22133], .c 3, .p pv3 [pv2,pv11,pv37,pv571], .c 7, .c 3, .c 67, .c 5, .c 3,
  .c 113, .c 43, .c 3, .c 5, .p pv5 [pv2,pv3,pv154933], .c 3, .p pv3 [pv2,pv5,pv7,pv83],
  .p pv2 [pv2,pv3,pv103289], .c 3, .c 7, .c 11, .c 3, .c 37, .c 5, .c 3, .c 29, .c 7, .c 3, .c 5,
  .c 41, .c 3, .c 11, .p pv5 [pv2,pv3,pv107,pv181], .c 3, .c 73, .c 17, .c 3,
  .p pv2 [pv2,pv7,pv11,pv12073], .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 199, .c 3, .c 359, .c 7,
  .c 3, .c 59, .p pv2 [pv2,pv3,pv41,pv3779], .c 3, .c 13, .c 5, .c 3, .p pv7 [pv2,pv929639],
  .p pv11 [pv2,pv3,pv5,pv61,pv127], .c 3, .c 5, .c 31, .c 3, .c 7, .c 53, .c 3, .c 11, .c 13,
  .c 3, .c 953, .c 5, .c 3, .c 41, .p pv11 [pv2,pv3,pv5,pv73,pv283], .c 3, .c 5, .c 67, .c 3,
  .c 19, .p pv2 [pv2,pv3,pv109,pv2843], .c 3, .p pv5 [pv2,pv7,pv59,pv2251],
  .p pv7 [pv2,pv3,pv269],
]
private theorem h0226c30 : checkBlock 1859075 128 b0226c30 = true := by
  decide +kernel

private def b0226c31 : List Row := [
  .c 3, .c 7, .c 5, .c 3, .c 107, .c 11, .c 3, .c 5, .c 7, .c 3, .c 13,
  .p pv17 [pv2,pv3,pv11,pv7043], .c 3, .c 227, .c 19, .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv33203], .c 149, .c 3, .c 5, .c 13, .c 3, .c 1303, .c 73, .c 3,
  .p pv2 [pv2,pv929693], .c 7, .c 3, .c 29, .c 5, .c 3, .c 53, .c 797, .c 3, .c 5, .c 11, .c 3,
  .c 31, .c 181, .c 3, .c 7, .c 71, .c 3, .c 79, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 401,
  .c 3, .p pv3 [pv2,pv5,pv11,pv2113], .c 17, .c 3, .c 829, .c 43, .c 3,
  .p pv2 [pv2,pv7,pv53,pv179], .c 5, .c 3, .c 7, .c 47, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv44273],
  .c 3, .p pv11 [pv2,pv5,pv185947], .c 7, .c 3, .c 17, .p pv13 [pv2,pv3,pv479,pv647], .c 3,
  .c 197, .c 5, .c 3, .p pv3 [pv2,pv58109], .p pv3 [pv2,pv3,pv5,pv71,pv97], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv77479], .c 3, .c 7, .c 59, .c 3, .c 13, .c 29, .c 3, .p pv3 [pv2,pv232439],
  .c 5, .c 3, .p pv7 [pv2,pv67,pv13877], .p pv7 [pv2,pv3,pv5,pv13,pv149], .c 3, .c 5, .c 23, .c 3,
  .p pv11 [pv2,pv5,pv19,pv9787], .c 13, .c 3, .p pv5 [pv2,pv7,pv16603], .c 11, .c 3, .c 7, .c 5,
  .c 3, .c 19, .p pv3 [pv2,pv3,pv5,pv7,pv11,pv23], .c 3, .c 5, .c 7, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv17,pv59,pv103], .c 3, .c 29, .p pv7 [pv2,pv3,pv19,pv2039], .c 3, .c 23, .c 5,
  .c 3, .c 17, .c 79, .c 3, .c 5,
]
private theorem h0226c31 : checkBlock 1859331 128 b0226c31 = true := by
  decide +kernel

def rows0226 : List Row :=
  b0226c00 ++ b0226c01 ++ b0226c02 ++ b0226c03 ++ b0226c04 ++ b0226c05 ++ b0226c06 ++ b0226c07 ++
  b0226c08 ++ b0226c09 ++ b0226c10 ++ b0226c11 ++ b0226c12 ++ b0226c13 ++ b0226c14 ++ b0226c15 ++
  b0226c16 ++ b0226c17 ++ b0226c18 ++ b0226c19 ++ b0226c20 ++ b0226c21 ++ b0226c22 ++ b0226c23 ++
  b0226c24 ++ b0226c25 ++ b0226c26 ++ b0226c27 ++ b0226c28 ++ b0226c29 ++ b0226c30 ++ b0226c31

theorem checked0226 : checkBlock 1851395 4096 rows0226 = true :=
  checkBlock_append h0226c00 (
    checkBlock_append h0226c01 (
    checkBlock_append h0226c02 (
    checkBlock_append h0226c03 (
    checkBlock_append h0226c04 (
    checkBlock_append h0226c05 (
    checkBlock_append h0226c06 (
    checkBlock_append h0226c07 (
    checkBlock_append h0226c08 (
    checkBlock_append h0226c09 (
    checkBlock_append h0226c10 (
    checkBlock_append h0226c11 (
    checkBlock_append h0226c12 (
    checkBlock_append h0226c13 (
    checkBlock_append h0226c14 (
    checkBlock_append h0226c15 (
    checkBlock_append h0226c16 (
    checkBlock_append h0226c17 (
    checkBlock_append h0226c18 (
    checkBlock_append h0226c19 (
    checkBlock_append h0226c20 (
    checkBlock_append h0226c21 (
    checkBlock_append h0226c22 (
    checkBlock_append h0226c23 (
    checkBlock_append h0226c24 (
    checkBlock_append h0226c25 (
    checkBlock_append h0226c26 (
    checkBlock_append h0226c27 (
    checkBlock_append h0226c28 (
    checkBlock_append h0226c29 (
    checkBlock_append h0226c30 (
    h0226c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
