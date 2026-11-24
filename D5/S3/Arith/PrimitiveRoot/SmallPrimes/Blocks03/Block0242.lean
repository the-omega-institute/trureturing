/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks03/Block0242
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks03/Block0242.checked0242
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table137

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0242c00 : List Row := [
  .p pv2 [pv2,pv3,pv241,pv457], .c 3, .p pv7 [pv2,pv5,pv7,pv127,pv223], .c 41, .c 3, .c 7, .c 19,
  .c 3, .c 1223, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv13,pv61],
  .c 1171, .c 3, .c 47, .p pv17 [pv2,pv3,pv11,pv23,pv653], .c 3, .c 13, .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv5507], .c 3, .c 5, .c 29, .c 3, .c 23, .c 7, .c 3,
  .p pv3 [pv2,pv19,pv13043], .c 13, .c 3, .c 31, .c 5, .c 3, .c 379, .p pv3 [pv2,pv3,pv5,pv13217],
  .c 3, .c 5, .c 17, .c 3, .c 7, .c 11, .c 3, .p pv5 [pv2,pv463,pv2141], .c 163, .c 3,
  .p pv2 [pv2,pv577,pv859], .c 5, .c 3, .p pv2 [pv2,pv13,pv76253], .c 479, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv330431], .c 3, .c 13, .c 19, .c 3, .c 67, .p pv11 [pv2,pv3,pv330433], .c 3,
  .c 7, .c 5, .c 3, .p pv7 [pv2,pv17,pv37,pv197], .p pv2 [pv2,pv3,pv5,pv7,pv1049], .c 3, .c 5,
  .c 7, .c 3, .c 83, .c 23, .c 3, .p pv2 [pv2,pv991313], .c 11, .c 3, .p pv3 [pv2,pv247829], .c 5,
  .c 3, .p pv7 [pv2,pv7,pv20231], .p pv7 [pv2,pv3,pv5,pv11,pv751], .c 3, .c 5, .c 103, .c 3,
  .c 11, .c 89, .c 3, .c 619, .c 7, .c 3, .c 79, .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv66089],
  .c 3, .c 5, .c 53, .c 3, .p pv3 [pv2,pv5,pv7,pv73,pv97], .c 61, .c 3, .c 7, .c 193, .c 3, .c 17,
  .c 5, .c 3, .c 601, .c 7, .c 3, .c 5, .c 19, .c 3, .c 983, .p pv5 [pv2,pv3,pv82613], .c 3,
  .c 11, .c 37, .c 3,
]
private theorem h0242c00 : checkBlock 1982467 128 b0242c00 = true := by
  decide +kernel

private def b0242c01 : List Row := [
  .p pv2 [pv2,pv7,pv141623], .c 5, .c 3, .c 7, .c 67, .c 3, .c 5, .c 739, .c 3,
  .p pv2 [pv2,pv5,pv99137], .c 7, .c 3, .c 13, .c 683, .c 3, .c 73, .c 5, .c 3, .c 29, .c 11,
  .c 3, .c 5, .c 211, .c 3, .c 7, .c 13, .c 3, .c 97, .p pv2 [pv2,pv3,pv7,pv17,pv2777], .c 3,
  .c 11, .c 5, .c 3, .c 47, .c 31, .c 3, .c 5, .p pv2 [pv2,pv3,pv165233], .c 3, .c 41,
  .p pv2 [pv2,pv3,pv19,pv17393], .c 3, .c 23, .p pv7 [pv2,pv3,pv27539], .c 3, .c 7, .c 5, .c 3,
  .c 109, .c 19, .c 3, .c 5, .c 7, .c 3, .c 89, .p pv5 [pv2,pv3,pv101,pv409], .c 3,
  .p pv2 [pv2,pv47,pv53,pv199], .p pv11 [pv2,pv3,pv11,pv13,pv2311], .c 3,
  .p pv2 [pv2,pv41,pv24181], .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv82619], .c 3,
  .p pv2 [pv2,pv5,pv11,pv9013], .c 17, .c 3, .c 37, .c 7, .c 3, .p pv3 [pv2,pv59,pv4201], .c 5,
  .c 3, .p pv13 [pv2,pv19,pv52181], .p pv19 [pv2,pv3,pv5,pv17], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv563,pv587], .c 3, .p pv7 [pv2,pv5,pv7,pv13,pv2179], .c 11, .c 3, .c 7, .c 23,
  .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv337,pv1471], .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv13,pv19,pv223], .c 3, .p pv3 [pv2,pv5,pv89,pv557], .c 457, .c 3, .c 61, .c 13,
  .c 3, .c 29, .c 5, .c 3, .c 7, .c 37, .c 3, .c 5, .c 131, .c 3, .p pv11 [pv2,pv5,pv39659], .c 7,
  .c 3, .p pv2 [pv2,pv103,pv4813], .c 11, .c 3, .c 439, .c 5, .c 3, .p pv3 [pv2,pv13,pv23,pv829],
  .c 97, .c 3, .c 5, .c 31,
]
private theorem h0242c01 : checkBlock 1982723 128 b0242c01 = true := by
  decide +kernel

private def b0242c02 : List Row := [
  .c 3, .c 7, .c 239, .c 3, .p pv2 [pv2,pv991493], .p pv17 [pv2,pv3,pv7,pv43,pv61], .c 3,
  .p pv5 [pv2,pv11,pv19,pv593], .c 5, .c 3, .c 17, .p pv7 [pv2,pv3,pv5,pv661], .c 3, .c 5, .c 13,
  .c 3, .c 19, .p pv5 [pv2,pv3,pv257,pv643], .c 3, .c 281, .p pv3 [pv2,pv3,pv349,pv947], .c 3,
  .c 7, .c 5, .c 3, .c 463, .c 43, .c 3, .c 5, .c 7, .c 3, .c 149, .c 277, .c 3, .c 11, .c 19,
  .c 3, .p pv2 [pv2,pv37,pv13399], .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv23,pv479], .c 3, .c 5,
  .c 17, .c 3, .c 47, .c 709, .c 3, .p pv2 [pv2,pv495769], .c 7, .c 3, .c 23, .c 5, .c 3, .c 37,
  .c 11, .c 3, .c 5, .p pv11 [pv2,pv3,pv9181], .c 3, .c 17, .p pv3 [pv2,pv3,pv11,pv30047], .c 3,
  .c 7, .p pv2 [pv2,pv3,pv59,pv2801], .c 3, .c 11, .c 5, .c 3, .c 83, .c 7, .c 3, .c 5, .c 419,
  .c 3, .c 881, .c 67, .c 3, .c 13, .c 223, .c 3, .p pv5 [pv2,pv7,pv141653], .c 5, .c 3, .c 7,
  .c 251, .c 3, .c 5, .c 11, .c 3, .c 653, .c 7, .c 3, .c 59, .c 17, .c 3, .c 1151, .c 5, .c 3,
  .c 11, .c 1277, .c 3, .c 5, .c 89, .c 3, .c 7, .c 953, .c 3, .p pv2 [pv2,pv495799], .c 197,
  .c 3, .c 17, .c 5, .c 3, .c 131, .c 41, .c 3, .c 5, .c 181, .c 3, .c 23, .c 11, .c 3,
  .p pv2 [pv2,pv7,pv59], .p pv11 [pv2,pv3,pv13,pv12713], .c 3, .c 7,
]
private theorem h0242c02 : checkBlock 1982979 128 b0242c02 = true := by
  decide +kernel

private def b0242c03 : List Row := [
  .c 5, .c 3, .c 19, .c 13, .c 3, .c 5, .c 7, .c 3, .c 769, .p pv2 [pv2,pv3,pv29,pv41,pv139],
  .c 3, .p pv3 [pv2,pv11,pv31,pv727], .c 47, .c 3, .c 113, .c 5, .c 3, .c 257, .c 17, .c 3, .c 5,
  .c 19, .c 3, .c 29, .c 263, .c 3, .c 31, .c 7, .c 3, .c 13, .c 5, .c 3, .c 227,
  .p pv2 [pv2,pv3,pv5,pv11,pv601], .c 3, .c 5, .c 379, .c 3, .c 11, .c 23, .c 3, .c 7, .c 13,
  .c 3, .p pv2 [pv2,pv11,pv17,pv5303], .c 5, .c 3, .c 503, .c 7, .c 3, .c 5, .c 73, .c 3,
  .p pv2 [pv2,pv5,pv131,pv757], .p pv19 [pv2,pv3,pv330557], .c 3, .p pv2 [pv2,pv401,pv2473],
  .c 31, .c 3, .c 19, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv1033], .c 3, .c 5, .c 349, .c 3,
  .c 13, .c 7, .c 3, .c 11, .p pv2 [pv2,pv3,pv330563], .c 3, .p pv5 [pv2,pv23,pv43117], .c 5,
  .c 3, .p pv2 [pv2,pv11,pv45077], .c 19, .c 3, .c 5, .c 13, .c 3, .c 7, .c 59, .c 3, .c 17,
  .p pv11 [pv2,pv3,pv7,pv5903], .c 3, .p pv2 [pv2,pv397,pv1249], .c 5, .c 3, .c 53, .c 11, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv29,pv11399], .c 3, .c 859, .c 199, .c 3, .p pv2 [pv2,pv7,pv13,pv5449],
  .p pv3 [pv2,pv3,pv101,pv1091], .c 3, .c 7, .c 5, .c 3, .c 13, .c 23, .c 3, .c 5, .c 7, .c 3,
  .c 43, .p pv5 [pv2,pv3,pv13,pv59,pv431], .c 3, .c 19, .c 317, .c 3, .c 31, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv141677], .c 313, .c 3, .c 5, .c 11, .c 3,
]
private theorem h0242c03 : checkBlock 1983235 128 b0242c03 = true := by
  decide +kernel

private def b0242c04 : List Row := [
  .p pv11 [pv2,pv5,pv198349], .p pv2 [pv2,pv3,pv7,pv17,pv463], .c 3, .c 23, .c 7, .c 3,
  .p pv5 [pv2,pv991751], .c 5, .c 3, .c 11, .c 389, .c 3, .c 5, .c 1367, .c 3, .c 59,
  .p pv3 [pv2,pv3,pv330587], .c 3, .c 7, .c 233, .c 3, .c 37, .c 5, .c 3, .c 41, .c 7, .c 3, .c 5,
  .c 43, .c 3, .c 487, .c 11, .c 3, .c 383, .p pv3 [pv2,pv3,pv311,pv1063], .c 3,
  .p pv2 [pv2,pv7,pv19,pv7457], .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .c 17, .c 3, .c 19, .c 7,
  .c 3, .p pv2 [pv2,pv11,pv90163], .c 23, .c 3, .c 197, .c 5, .c 3, .p pv7 [pv2,pv61,pv71,pv229],
  .p pv17 [pv2,pv3,pv5,pv19,pv29], .c 3, .c 5, .c 37, .c 3, .c 7, .c 127, .c 3, .c 83, .c 11,
  .c 3, .c 137, .c 5, .c 3, .c 29, .c 13, .c 3, .c 5, .c 149, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv330607], .c 3, .p pv5 [pv2,pv7,pv141689], .p pv11 [pv2,pv3,pv20663], .c 3,
  .c 7, .c 5, .c 3, .c 31, .c 661, .c 3, .c 5, .c 7, .c 3, .c 241, .c 107, .c 3, .c 103, .c 17,
  .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv7,pv35423], .c 109, .c 3, .c 5,
  .p pv41 [pv2,pv3,pv11,pv13,pv17], .c 3, .p pv2 [pv2,pv5,pv83,pv239], .c 41, .c 3, .c 11, .c 7,
  .c 3, .c 17, .c 5, .c 3, .c 43, .c 31, .c 3, .c 5, .c 23, .c 3,
  .p pv19 [pv2,pv5,pv7,pv17,pv1667], .c 19, .c 3, .c 7, .c 523, .c 3, .p pv5 [pv2,pv991871], .c 5,
]
private theorem h0242c04 : checkBlock 1983491 128 b0242c04 = true := by
  decide +kernel

private def b0242c05 : List Row := [
  .c 3, .p pv2 [pv2,pv13,pv38149], .c 7, .c 3, .c 5, .c 59, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv11,pv43,pv233], .c 3, .p pv5 [pv2,pv991883], .c 79, .c 3, .c 11, .c 5, .c 3,
  .c 7, .c 17, .c 3, .c 5, .c 13, .c 3, .c 173, .c 7, .c 3, .c 829, .c 347, .c 3, .c 29, .c 5,
  .c 3, .c 19, .c 71, .c 3, .c 5, .c 11, .c 3, .c 7, .c 47, .c 3, .c 229, .c 37, .c 3,
  .p pv3 [pv2,pv17,pv29,pv503], .c 5, .c 3, .c 11, .c 439, .c 3, .c 5, .c 19, .c 3,
  .p pv2 [pv2,pv5,pv11,pv3607], .p pv5 [pv2,pv3,pv13,pv157], .c 3, .c 179,
  .p pv2 [pv2,pv3,pv330643], .c 3, .c 7, .c 5, .c 3, .c 311, .p pv7 [pv2,pv3,pv5,pv7,pv47,pv67],
  .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv49597], .c 11, .c 3, .c 107,
  .p pv7 [pv2,pv3,pv23,pv599], .c 3, .c 431, .c 5, .c 3, .c 89, .c 601, .c 3, .c 5, .c 31, .c 3,
  .c 23, .p pv5 [pv2,pv3,pv7,pv241], .c 3, .c 13, .c 7, .c 3, .c 19, .c 5, .c 3,
  .p pv3 [pv2,pv247991], .p pv3 [pv2,pv3,pv5,pv13,pv5087], .c 3, .c 5, .c 67, .c 3, .c 97, .c 13,
  .c 3, .c 7, .c 11, .c 3, .c 71, .c 5, .c 3, .c 1193, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv330661], .c 3, .c 11, .c 827, .c 3, .c 29, .p pv2 [pv2,pv3,pv110221], .c 3,
  .c 727, .c 5, .c 3, .c 7, .c 271, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv7873], .c 3, .c 1109,
]
private theorem h0242c05 : checkBlock 1983747 128 b0242c05 = true := by
  decide +kernel

private def b0242c06 : List Row := [
  .c 7, .c 3, .p pv11 [pv2,pv29,pv79,pv433], .c 157, .c 3, .p pv2 [pv2,pv563,pv881], .c 5, .c 3,
  .c 17, .c 13, .c 3, .c 5, .c 787, .c 3, .c 7, .c 211, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv7,pv97,pv487], .c 3, .p pv2 [pv2,pv992021], .c 5, .c 3, .c 23, .c 37, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv19,pv229], .c 3, .p pv2 [pv2,pv5,pv13,pv587], .c 43, .c 3, .c 73,
  .p pv7 [pv2,pv3,pv18371], .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv853,pv1163], .c 11, .c 3, .c 5,
  .c 7, .c 3, .p pv2 [pv2,pv5,pv198409], .c 29, .c 3, .c 757, .c 13, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv53,pv191], .c 59, .c 3, .c 5, .p pv2 [pv2,pv3,pv165343], .c 3, .c 17,
  .p pv2 [pv2,pv3,pv7,pv29,pv181], .c 3, .c 109, .c 7, .c 3, .p pv2 [pv2,pv19,pv26107], .c 5,
  .c 3, .p pv2 [pv2,pv13,pv17,pv67], .c 23, .c 3, .c 5, .c 11, .c 3, .c 13, .c 241, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv11,pv911], .c 3, .p pv2 [pv2,pv37,pv26813], .c 5, .c 3, .c 11, .c 7, .c 3,
  .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv11,pv29,pv311], .p pv3 [pv2,pv3,pv330697], .c 3, .c 23,
  .c 17, .c 3, .c 359, .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv3307], .c 3, .c 5, .c 227, .c 3,
  .p pv2 [pv2,pv5,pv23,pv8627], .c 7, .c 3, .c 31, .c 887, .c 3, .c 17, .c 5, .c 3, .c 13, .c 733,
  .c 3, .c 5, .c 71, .c 3, .c 7, .c 79, .c 3, .p pv5 [pv2,pv11,pv19,pv47,pv101], .c 659, .c 3,
  .c 823, .c 5, .c 3,
]
private theorem h0242c06 : checkBlock 1984003 128 b0242c06 = true := by
  decide +kernel

private def b0242c07 : List Row := [
  .p pv2 [pv2,pv992129], .p pv2 [pv2,pv3,pv5,pv33071], .c 3, .c 5, .c 29, .c 3,
  .p pv7 [pv2,pv5,pv198427], .c 37, .c 3, .c 41, .c 11, .c 3, .c 7, .c 5, .c 3, .c 389, .c 17,
  .c 3, .c 5, .c 7, .c 3, .c 11, .c 19, .c 3, .c 13, .p pv7 [pv2,pv3,pv17,pv71,pv137], .c 3,
  .c 1153, .c 5, .c 3, .p pv7 [pv2,pv7,pv41,pv3457], .c 43, .c 3, .c 5, .p pv5 [pv2,pv3,pv330721],
  .c 3, .p pv2 [pv2,pv5,pv61,pv3253], .c 13, .c 3, .p pv3 [pv2,pv124021], .c 7, .c 3,
  .p pv7 [pv2,pv17,pv58363], .c 5, .c 3, .c 647, .p pv3 [pv2,pv3,pv5,pv13229], .c 3, .c 5, .c 821,
  .c 3, .p pv59 [pv2,pv5,pv7,pv19,pv373], .p pv2 [pv2,pv3,pv163,pv2029], .c 3, .c 7, .c 367, .c 3,
  .c 53, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 47, .c 3, .c 61, .c 17, .c 3,
  .p pv2 [pv2,pv283,pv1753], .p pv3 [pv2,pv3,pv13,pv19,pv103], .c 3, .c 31, .c 5, .c 3, .c 7,
  .c 11, .c 3, .c 5, .c 19, .c 3, .c 37, .c 7, .c 3, .c 17, .p pv7 [pv2,pv3,pv199,pv277], .c 3,
  .c 11, .c 5, .c 3, .c 433, .c 29, .c 3, .c 5, .c 83, .c 3, .c 7, .p pv29 [pv2,pv3,pv61,pv2711],
  .c 3, .p pv3 [pv2,pv248057], .p pv2 [pv2,pv3,pv7,pv37,pv1277], .c 3, .c 13, .c 5, .c 3, .c 1303,
  .p pv11 [pv2,pv3,pv5,pv29,pv2281], .c 3, .c 5, .c 11, .c 3, .c 47, .c 173, .c 3, .c 599, .c 13,
  .c 3, .c 7, .c 5, .c 3, .c 11, .c 103, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv11,pv18041],
  .c 61,
]
private theorem h0242c07 : checkBlock 1984259 128 b0242c07 = true := by
  decide +kernel

private def b0242c08 : List Row := [
  .c 3, .c 811, .c 131, .c 3, .c 41, .c 5, .c 3, .c 17, .c 19, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv43,pv641], .c 3, .c 13, .c 11, .c 3, .p pv2 [pv2,pv17,pv58369], .c 7, .c 3,
  .c 743, .c 5, .c 3, .c 79, .p pv7 [pv2,pv3,pv5,pv8269], .c 3, .c 5, .c 13, .c 3,
  .p pv2 [pv2,pv5,pv7,pv28351], .c 179, .c 3, .c 7, .c 43, .c 3, .c 59, .c 5, .c 3, .c 31, .c 7,
  .c 3, .c 5, .c 17, .c 3, .c 23, .c 397, .c 3, .c 19, .c 11, .c 3, .c 83, .c 5, .c 3, .c 7,
  .c 1063, .c 3, .c 5, .c 199, .c 3, .c 11, .c 7, .c 3, .c 157, .p pv3 [pv2,pv3,pv53,pv79], .c 3,
  .c 37, .c 5, .c 3, .p pv3 [pv2,pv17,pv14593], .c 31, .c 3, .c 5, .c 251, .c 3, .c 7, .c 71,
  .c 3, .p pv2 [pv2,pv211,pv4703], .c 47, .c 3, .c 29, .c 5, .c 3, .c 283, .c 191, .c 3, .c 5,
  .c 41, .c 3, .c 53, .c 23, .c 3, .c 11, .c 17, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv11,pv43,pv1049], .p pv7 [pv2,pv3,pv5,pv7,pv13,pv727], .c 3, .c 5, .c 7, .c 3,
  .c 19, .c 13, .c 3, .p pv5 [pv2,pv992363], .p pv7 [pv2,pv3,pv41,pv2017], .c 3, .c 17, .c 5,
  .c 3, .c 23, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv330791], .c 3, .c 43,
  .p pv5 [pv2,pv3,pv7,pv11,pv179], .c 3, .c 61, .c 7, .c 3, .c 11, .c 5, .c 3, .c 41,
]
private theorem h0242c08 : checkBlock 1984515 128 b0242c08 = true := by
  decide +kernel

private def b0242c09 : List Row := [
  .c 593, .c 3, .c 5, .p pv5 [pv2,pv3,pv82699], .c 3, .c 109, .p pv5 [pv2,pv3,pv293,pv1129], .c 3,
  .c 7, .c 29, .c 3, .p pv3 [pv2,pv248099], .c 5, .c 3, .p pv11 [pv2,pv683,pv1453], .c 7, .c 3,
  .c 5, .c 11, .c 3, .c 257, .p pv2 [pv2,pv3,pv193,pv857], .c 3, .p pv3 [pv2,pv19,pv6529], .c 59,
  .c 3, .c 379, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 31, .c 3,
  .p pv3 [pv2,pv5,pv11,pv13,pv347], .c 7, .c 3, .c 29, .p pv7 [pv2,pv3,pv41351], .c 3, .c 13,
  .c 5, .c 3, .p pv2 [pv2,pv992429], .c 263, .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv25447], .c 3,
  .c 7, .c 11, .c 3, .c 23, .c 13, .c 3, .c 127, .c 5, .c 3, .c 617,
  .p pv2 [pv2,pv3,pv5,pv109,pv607], .c 3, .c 5, .p pv5 [pv2,pv3,pv1723], .c 3,
  .p pv2 [pv2,pv5,pv23,pv863], .c 17, .c 3, .p pv2 [pv2,pv7,pv11,pv12889], .c 1117, .c 3, .c 7,
  .c 5, .c 3, .c 353, .p pv19 [pv2,pv3,pv5,pv7,pv17,pv139], .c 3, .c 5, .c 7, .c 3, .c 13, .c 41,
  .c 3, .c 17, .c 11, .c 3, .c 73, .c 5, .c 3, .c 19, .c 47, .c 3, .c 5, .c 13, .c 3, .c 11,
  .c 29, .c 3, .c 89, .c 7, .c 3, .c 991, .c 5, .c 3, .p pv2 [pv2,pv149,pv6661],
  .p pv7 [pv2,pv3,pv5,pv33083], .c 3, .c 5, .c 19, .c 3, .p pv7 [pv2,pv5,pv7,pv4051], .c 137,
  .c 3, .c 7, .c 109, .c 3, .p pv2 [pv2,pv173,pv5737], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv73,pv103], .c 3, .c 29, .c 31, .c 3,
]
private theorem h0242c09 : checkBlock 1984771 128 b0242c09 = true := by
  decide +kernel

private def b0242c10 : List Row := [
  .c 11, .c 449, .c 3, .c 79, .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv919], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv151,pv313], .c 3, .p pv2 [pv2,pv5,pv29,pv37], .c 7, .c 3,
  .p pv3 [pv2,pv17,pv41,pv89], .c 139, .c 3, .c 19, .c 5, .c 3, .c 911, .c 11, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv67,pv823], .c 3, .c 7, .c 443, .c 3, .c 13, .c 71, .c 3, .c 11, .c 5, .c 3,
  .c 953, .c 19, .c 3, .c 5, .c 17, .c 3, .c 83, .c 13, .c 3, .c 241, .c 103, .c 3, .c 7, .c 5,
  .c 3, .c 167, .c 1061, .c 3, .c 5, .c 7, .c 3, .c 17, .c 67, .c 3, .c 31, .c 859, .c 3, .c 23,
  .c 5, .c 3, .c 11, .c 37, .c 3, .c 5, .p pv3 [pv2,pv3,pv29,pv3803], .c 3, .c 107, .c 59, .c 3,
  .c 19, .c 7, .c 3, .p pv5 [pv2,pv992591], .c 5, .c 3, .p pv2 [pv2,pv496297], .c 13, .c 3, .c 5,
  .c 151, .c 3, .c 229, .c 11, .c 3, .c 7, .c 17, .c 3, .p pv2 [pv2,pv496303], .c 5, .c 3,
  .p pv2 [pv2,pv992609], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv19463], .c 3, .c 71, .c 47,
  .c 3, .p pv2 [pv2,pv11,pv45119], .p pv3 [pv2,pv3,pv110291], .c 3, .c 13, .c 5, .c 3, .c 7,
  .c 967, .c 3, .c 5, .p pv31 [pv2,pv3,pv7,pv13,pv101], .c 3, .c 41, .c 7, .c 3, .c 43, .c 11,
  .c 3, .c 929, .c 5, .c 3, .p pv7 [pv2,pv107,pv9277], .c 1409,
]
private theorem h0242c10 : checkBlock 1985027 128 b0242c10 = true := by
  decide +kernel

private def b0242c11 : List Row := [
  .c 3, .c 5, .p pv5 [pv2,pv3,pv409,pv809], .c 3, .c 7, .p pv2 [pv2,pv3,pv55147], .c 3, .c 113,
  .c 97, .c 3, .p pv11 [pv2,pv11,pv31,pv41,pv71], .c 5, .c 3, .c 37, .c 17, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv165443], .c 3, .c 13, .c 89, .c 3, .c 47, .c 19, .c 3, .c 7, .c 5, .c 3,
  .c 1051, .c 503, .c 3, .c 5, .c 7, .c 3, .c 401, .c 43, .c 3, .c 11, .c 313, .c 3,
  .p pv2 [pv2,pv17,pv58393], .c 5, .c 3, .c 29, .c 317, .c 3, .c 5, .p pv19 [pv2,pv3,pv20681],
  .c 3, .c 73, .c 23, .c 3, .c 263, .c 7, .c 3, .c 233, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv23,pv14387], .c 3, .c 67, .c 17, .c 3, .c 7, .p pv3 [pv2,pv3,pv36767], .c 3,
  .c 11, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 727, .c 3, .p pv3 [pv2,pv5,pv12409], .c 19, .c 3,
  .c 17, .c 761, .c 3, .p pv2 [pv2,pv7,pv23,pv3083], .c 5, .c 3, .c 7, .c 349, .c 3, .c 5, .c 11,
  .c 3, .p pv11 [pv2,pv5,pv367,pv541], .c 7, .c 3, .c 13, .c 373, .c 3, .p pv2 [pv2,pv43,pv23087],
  .c 5, .c 3, .c 11, .p pv17 [pv2,pv3,pv5,pv13,pv1697], .c 3, .c 5, .c 607, .c 3, .c 7, .c 13,
  .c 3, .c 41, .p pv2 [pv2,pv3,pv7,pv7879], .c 3, .p pv3 [pv2,pv248189], .c 5, .c 3, .c 19, .c 23,
  .c 3, .c 5, .c 59, .c 3, .c 37, .c 11, .c 3, .p pv13 [pv2,pv7,pv277],
]
private theorem h0242c11 : checkBlock 1985283 128 b0242c11 = true := by
  decide +kernel

private def b0242c12 : List Row := [
  .c 53, .c 3, .c 7, .c 5, .c 3, .c 17, .p pv3 [pv2,pv3,pv5,pv7,pv31,pv61], .c 3, .c 5, .c 7,
  .c 3, .p pv3 [pv2,pv5,pv49639], .c 197, .c 3, .c 23, .c 227, .c 3, .p pv2 [pv2,pv29,pv17117],
  .c 5, .c 3, .c 157, .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv59,pv71,pv79], .c 3,
  .p pv11 [pv2,pv5,pv23,pv89,pv97], .p pv5 [pv2,pv3,pv7,pv53,pv223], .c 3, .c 439, .c 7, .c 3,
  .c 1231, .c 5, .c 3, .c 47, .c 43, .c 3, .c 5, .c 17, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv199,pv1663], .c 3, .c 7, .c 359, .c 3, .c 13, .c 5, .c 3,
  .p pv13 [pv2,pv992819], .c 7, .c 3, .c 5, .c 179, .c 3, .c 17, .c 109, .c 3, .c 71, .c 13, .c 3,
  .p pv5 [pv2,pv7,pv141833], .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv11,pv307],
  .c 3, .c 1213, .c 7, .c 3, .c 11, .p pv7 [pv2,pv3,pv29,pv317], .c 3, .c 739, .c 5, .c 3,
  .c 1361, .c 563, .c 3, .c 5, .c 1297, .c 3, .c 7, .p pv5 [pv2,pv3,pv41,pv1009], .c 3, .c 29,
  .c 17, .c 3, .c 149, .c 5, .c 3, .p pv13 [pv2,pv19,pv23,pv71], .c 11, .c 3, .c 5, .c 13, .c 3,
  .p pv2 [pv2,pv5,pv43,pv2309], .p pv5 [pv2,pv3,pv11,pv3343], .c 3, .c 19, .c 113, .c 3, .c 7,
  .c 5, .c 3, .p pv17 [pv2,pv269,pv3691], .c 101, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv17,pv11681], .c 653, .c 3, .c 193, .p pv3 [pv2,pv3,pv110321], .c 3, .c 43,
  .c 5, .c 3, .c 13, .p pv59 [pv2,pv3,pv5,pv37,pv1789], .c 3,
]
private theorem h0242c12 : checkBlock 1985539 128 b0242c12 = true := by
  decide +kernel

private def b0242c13 : List Row := [
  .c 5, .c 11, .c 3, .c 151, .p pv7 [pv2,pv3,pv7,pv13,pv3637], .c 3, .c 463, .c 7, .c 3, .c 67,
  .c 5, .c 3, .c 11, .c 17, .c 3, .c 5, .c 37, .c 3, .c 523, .c 29, .c 3, .c 7, .c 257, .c 3,
  .c 23, .c 5, .c 3, .p pv3 [pv2,pv248231], .c 7, .c 3, .c 5, .c 53, .c 3, .c 19, .c 11, .c 3,
  .c 13, .c 43, .c 3, .p pv3 [pv2,pv7,pv17,pv149], .c 5, .c 3, .c 7, .c 59, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv15761], .c 3, .c 29, .c 7, .c 3, .p pv3 [pv2,pv11,pv22567], .c 19, .c 3,
  .p pv5 [pv2,pv79,pv12569], .c 5, .c 3, .c 709, .c 1129, .c 3, .c 5, .c 41, .c 3, .c 7, .c 17,
  .c 3, .c 449, .c 11, .c 3, .c 701, .c 5, .c 3, .p pv2 [pv2,pv37,pv47,pv571], .c 71, .c 3, .c 5,
  .c 67, .c 3, .c 11, .c 31, .c 3, .c 17, .c 919, .c 3, .c 7, .c 5, .c 3, .c 443, .c 13, .c 3,
  .c 5, .c 7, .c 3, .c 23, .c 307, .c 3, .p pv2 [pv2,pv487,pv2039], .p pv37 [pv2,pv3,pv359,pv461],
  .c 3, .c 887, .c 5, .c 3, .c 41, .p pv7 [pv2,pv3,pv5,pv331], .c 3, .c 5, .c 29, .c 3, .c 541,
  .c 19, .c 3, .c 11, .c 7, .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv11,pv45137], .c 1019, .c 3,
  .c 5, .p pv23 [pv2,pv3,pv13,pv29,pv439], .c 3, .c 43, .p pv3 [pv2,pv3,pv17,pv19471], .c 3, .c 7,
  .c 13,
]
private theorem h0242c13 : checkBlock 1985795 128 b0242c13 = true := by
  decide +kernel

private def b0242c14 : List Row := [
  .c 3, .p pv2 [pv2,pv521,pv953], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv36779],
  .c 3, .p pv17 [pv2,pv5,pv19,pv10453], .c 23, .c 3, .c 31, .c 47, .c 3, .c 11, .c 5, .c 3, .c 7,
  .c 131, .c 3, .c 5, .p pv19 [pv2,pv3,pv7,pv23,pv257], .c 3, .c 13, .c 7, .c 3, .c 83,
  .p pv2 [pv2,pv3,pv19,pv31,pv281], .c 3, .c 181, .c 5, .c 3, .c 23, .p pv13 [pv2,pv3,pv5,pv613],
  .c 3, .c 5, .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv165511], .c 3, .p pv3 [pv2,pv248267], .c 31,
  .c 3, .c 211, .c 5, .c 3, .c 11, .c 467, .c 3, .c 5, .c 547, .c 3, .c 17, .c 41, .c 3,
  .p pv17 [pv2,pv7,pv13,pv1559], .p pv7 [pv2,pv3,pv82757], .c 3, .c 7, .c 5, .c 3, .c 13, .c 29,
  .c 3, .c 5, .c 7, .c 3, .c 397, .c 11, .c 3, .c 37, .p pv13 [pv2,pv3,pv109,pv3037], .c 3, .c 19,
  .c 5, .c 3, .c 191, .c 23, .c 3, .c 5, .p pv5 [pv2,pv3,pv82759], .c 3, .c 61,
  .p pv5 [pv2,pv3,pv7,pv19,pv131], .c 3, .c 643, .c 7, .c 3, .p pv3 [pv2,pv31,pv8009], .c 5, .c 3,
  .c 29, .c 19, .c 3, .c 5, .c 293, .c 3, .c 1367, .p pv5 [pv2,pv3,pv103,pv1607], .c 3, .c 7,
  .c 11, .c 3, .c 17, .c 5, .c 3, .c 97, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv165523], .c 3, .c 11,
  .c 13, .c 3, .c 1279, .p pv13 [pv2,pv3,pv41381], .c 3, .p pv3 [pv2,pv7,pv11,pv6449], .c 5, .c 3,
  .c 7, .p pv13 [pv2,pv3,pv5,pv2207], .c 3, .c 5,
]
private theorem h0242c14 : checkBlock 1986051 128 b0242c14 = true := by
  decide +kernel

private def b0242c15 : List Row := [
  .c 109, .c 3, .p pv13 [pv2,pv5,pv139,pv1429], .c 7, .c 3, .c 19, .c 149, .c 3,
  .p pv2 [pv2,pv13,pv241,pv317], .c 5, .c 3, .c 239, .c 17, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv11,pv19], .c 3, .c 7, .c 61, .c 3, .c 11, .c 23, .c 3, .c 59, .c 5, .c 3,
  .p pv7 [pv2,pv11,pv90289], .c 13, .c 3, .c 5, .c 71, .c 3, .c 619,
  .p pv31 [pv2,pv3,pv23,pv2399], .c 3, .c 283, .c 569, .c 3, .c 7, .c 5, .c 3, .c 281, .c 11,
  .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv13,pv191], .c 73, .c 3, .c 127, .c 41, .c 3, .c 11,
  .c 5, .c 3, .c 37, .p pv2 [pv2,pv3,pv5,pv33107], .c 3, .c 5, .c 113, .c 3, .c 19, .c 17, .c 3,
  .p pv2 [pv2,pv496609], .c 7, .c 3, .p pv2 [pv2,pv29,pv1181], .c 5, .c 3, .c 31, .c 941, .c 3,
  .c 5, .c 11, .c 3, .p pv29 [pv2,pv5,pv7,pv2027], .c 97, .c 3, .c 7, .c 19, .c 3, .c 487, .c 5,
  .c 3, .c 11, .c 7, .c 3, .c 5, .c 23, .c 3, .c 13, .c 37, .c 3, .p pv3 [pv2,pv31039],
  .p pv7 [pv2,pv3,pv36787], .c 3, .c 1103, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5, .c 13, .c 3,
  .c 157, .c 7, .c 3, .p pv7 [pv2,pv19,pv61,pv857], .c 29, .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv993269], .p pv2 [pv2,pv3,pv5,pv113,pv293], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv53,pv6247], .c 3, .c 7, .p pv5 [pv2,pv3,pv17,pv541], .c 3, .c 43, .c 173,
  .c 3,
]
private theorem h0242c15 : checkBlock 1986307 128 b0242c15 = true := by
  decide +kernel

private def b0242c16 : List Row := [
  .c 241, .c 5, .c 3, .c 13, .c 367, .c 3, .c 5, .p pv7 [pv2,pv3,pv41387], .c 3,
  .p pv2 [pv2,pv5,pv71,pv1399], .c 19, .c 3, .c 29, .c 11, .c 3, .c 7, .c 5, .c 3, .c 53,
  .p pv13 [pv2,pv3,pv5,pv7,pv11,pv43], .c 3, .c 5, .c 7, .c 3, .c 11, .c 79, .c 3, .c 67, .c 1153,
  .c 3, .c 389, .c 5, .c 3, .p pv2 [pv2,pv7,pv70951], .p pv23 [pv2,pv3,pv5,pv66221], .c 3, .c 5,
  .c 17, .c 3, .c 37, .c 43, .c 3, .c 13, .c 7, .c 3, .c 113, .c 5, .c 3, .c 19, .c 127, .c 3,
  .c 5, .c 1097, .c 3, .c 17, .c 13, .c 3, .c 7, .p pv3 [pv2,pv3,pv19,pv37,pv157], .c 3,
  .p pv2 [pv2,pv993341], .c 5, .c 3, .p pv3 [pv2,pv11,pv17,pv83], .c 7, .c 3, .c 5, .c 19, .c 3,
  .c 271, .c 29, .c 3, .c 59, .c 61, .c 3, .p pv3 [pv2,pv7,pv13,pv2729], .c 5, .c 3, .c 7, .c 11,
  .c 3, .c 5, .c 139, .c 3, .c 1373, .c 7, .c 3, .c 41, .c 17, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv496687], .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv9739], .c 3, .c 7, .c 23, .c 3,
  .c 103, .p pv13 [pv2,pv3,pv7,pv73], .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv41,pv24229],
  .p pv19 [pv2,pv3,pv5,pv33113], .c 3, .c 5, .c 11, .c 3, .c 233, .c 71, .c 3,
  .p pv2 [pv2,pv7,pv70957], .c 167, .c 3, .c 7, .c 5, .c 3, .c 11, .c 19, .c 3, .c 5, .c 7,
]
private theorem h0242c16 : checkBlock 1986563 128 b0242c16 = true := by
  decide +kernel

private def b0242c17 : List Row := [
  .c 3, .c 31, .p pv3 [pv2,pv3,pv36793], .c 3, .c 563, .c 13, .c 3, .c 293, .c 5, .c 3,
  .p pv19 [pv2,pv7,pv141917], .c 17, .c 3, .c 5, .c 683, .c 3, .c 97, .c 11, .c 3, .c 349, .c 7,
  .c 3, .c 37, .c 5, .c 3, .p pv2 [pv2,pv13,pv19,pv2011], .p pv3 [pv2,pv3,pv5,pv103,pv643], .c 3,
  .c 5, .c 29, .c 3, .c 13, .c 31, .c 3, .c 7, .p pv13 [pv2,pv3,pv82787], .c 3,
  .p pv2 [pv2,pv17,pv61,pv479], .c 5, .c 3, .p pv2 [pv2,pv419,pv2371], .c 7, .c 3, .c 5, .c 13,
  .c 3, .c 137, .p pv5 [pv2,pv3,pv6899], .c 3, .c 53, .c 11, .c 3, .p pv2 [pv2,pv7,pv347,pv409],
  .c 5, .c 3, .c 7, .c 227, .c 3, .c 5, .c 37, .c 3, .c 11, .c 7, .c 3, .c 23,
  .p pv7 [pv2,pv3,pv97,pv569], .c 3, .c 61, .c 5, .c 3, .c 13, .c 109, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv167,pv661], .c 3, .c 7, .c 101, .c 3, .c 17, .c 311, .c 3, .c 41, .c 5, .c 3,
  .p pv2 [pv2,pv496747], .p pv43 [pv2,pv3,pv5,pv107,pv619], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv15053], .c 3, .c 19, .p pv3 [pv2,pv3,pv59,pv1871], .c 3, .c 11, .c 151,
  .c 3, .c 7, .c 5, .c 3, .c 47, .c 997, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv43,pv4621],
  .c 229, .c 3, .c 13, .c 19, .c 3, .p pv2 [pv2,pv127,pv7823], .c 5, .c 3,
  .p pv19 [pv2,pv7,pv37,pv137], .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv13799], .c 3, .c 59, .c 13,
  .c 3, .p pv2 [pv2,pv47,pv21139], .c 7, .c 3, .c 11,
]
private theorem h0242c17 : checkBlock 1986819 128 b0242c17 = true := by
  decide +kernel

private def b0242c18 : List Row := [
  .c 5, .c 3, .c 17, .p pv7 [pv2,pv3,pv5,pv29,pv571], .c 3, .c 5, .c 79, .c 3,
  .p pv7 [pv2,pv5,pv7,pv28387], .c 541, .c 3, .c 7, .p pv2 [pv2,pv3,pv331183], .c 3, .c 83, .c 5,
  .c 3, .c 29, .c 7, .c 3, .c 5, .c 11, .c 3, .p pv7 [pv2,pv5,pv59,pv421],
  .p pv2 [pv2,pv3,pv37,pv8951], .c 3, .p pv5 [pv2,pv293,pv3391], .c 53, .c 3, .c 73, .c 5, .c 3,
  .c 7, .c 13, .c 3, .c 5, .c 17, .c 3, .p pv11 [pv2,pv5,pv11,pv3613], .c 7, .c 3,
  .p pv2 [pv2,pv496789], .c 37, .c 3, .c 733, .c 5, .c 3, .c 127, .c 739, .c 3, .c 5, .c 23, .c 3,
  .c 7, .c 11, .c 3, .c 1171, .p pv31 [pv2,pv3,pv7,pv41,pv577], .c 3, .c 13, .c 5, .c 3, .c 181,
  .p pv7 [pv2,pv3,pv5,pv23], .c 3, .c 5, .c 47, .c 3, .c 307, .c 149, .c 3,
  .p pv3 [pv2,pv7,pv11,pv1613], .c 13, .c 3, .c 7, .c 5, .c 3, .c 19,
  .p pv37 [pv2,pv3,pv5,pv7,pv9463], .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv49681], .c 271,
  .c 3, .p pv5 [pv2,pv23,pv43201], .c 11, .c 3, .c 1061, .c 5, .c 3, .c 1381,
  .p pv17 [pv2,pv3,pv5,pv11,pv3011], .c 3, .c 5, .c 19, .c 3, .c 11, .c 317, .c 3,
  .p pv2 [pv2,pv101,pv4919], .c 7, .c 3, .c 17, .c 5, .c 3, .c 337,
  .p pv2 [pv2,pv3,pv5,pv71,pv311], .c 3, .c 5, .c 13, .c 3, .c 47, .p pv13 [pv2,pv3,pv331217],
  .c 3, .c 7, .p pv2 [pv2,pv3,pv18401], .c 3, .p pv3 [pv2,pv29,pv4283], .c 5, .c 3, .c 61, .c 7,
  .c 3, .c 5, .c 709, .c 3,
]
private theorem h0242c18 : checkBlock 1987075 128 b0242c18 = true := by
  decide +kernel

private def b0242c19 : List Row := [
  .c 43, .p pv2 [pv2,pv3,pv165611], .c 3, .c 11, .p pv2 [pv2,pv3,pv23,pv14401], .c 3, .c 19, .c 5,
  .c 3, .c 7, .c 17, .c 3, .c 5, .c 617, .c 3, .c 23, .c 7, .c 3, .c 1283, .c 673, .c 3,
  .p pv2 [pv2,pv269,pv1847], .c 5, .c 3, .c 31, .c 11, .c 3, .c 5, .c 383, .c 3, .c 7, .c 41,
  .c 3, .c 109, .c 29, .c 3, .c 11, .c 5, .c 3, .c 211, .p pv2 [pv2,pv3,pv5,pv31,pv2137], .c 3,
  .c 5, .c 43, .c 3, .c 67, .c 127, .c 3, .c 13, .p pv2 [pv2,pv3,pv29,pv5711], .c 3, .c 7, .c 5,
  .c 3, .p pv11 [pv2,pv19,pv52301], .c 31, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv39749],
  .c 13, .c 3, .c 19, .c 89, .c 3, .c 157, .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv17,pv433],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv19,pv23,pv379], .c 3, .p pv3 [pv2,pv5,pv11,pv4517],
  .p pv2 [pv2,pv3,pv7,pv79,pv599], .c 3, .c 17, .c 7, .c 3, .c 457, .c 5, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv5,pv53], .c 3, .c 5, .c 601, .c 3, .c 149, .c 11, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv13,pv83,pv307], .c 3, .p pv2 [pv2,pv23,pv43207], .c 5, .c 3, .c 37, .c 7,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv47,pv881], .c 3, .c 421, .p pv3 [pv2,pv3,pv110419], .c 3,
  .p pv2 [pv2,pv11,pv43,pv191], .p pv2 [pv2,pv3,pv89,pv1861], .c 3, .c 53, .c 5, .c 3, .c 7,
  .c 79, .c 3, .c 5, .c 1163, .c 3, .c 19, .c 7, .c 3, .p pv3 [pv2,pv248447], .c 11, .c 3, .c 13,
  .c 5,
]
private theorem h0242c19 : checkBlock 1987331 128 b0242c19 = true := by
  decide +kernel

private def b0242c20 : List Row := [
  .c 3, .c 17, .c 23, .c 3, .c 5, .c 173, .c 3, .c 7, .c 37, .c 3, .c 1039, .c 13, .c 3, .c 151,
  .c 5, .c 3, .p pv2 [pv2,pv727,pv1367], .p pv7 [pv2,pv3,pv5,pv157,pv211], .c 3, .c 5, .c 31,
  .c 3, .c 29, .c 883, .c 3, .c 23, .c 41, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv13,pv2389],
  .c 59, .c 3, .c 5, .c 7, .c 3, .c 13, .c 131, .c 3, .c 11, .c 251, .c 3,
  .p pv3 [pv2,pv367,pv677], .c 5, .c 3, .p pv7 [pv2,pv7,pv11,pv12907],
  .p pv7 [pv2,pv3,pv5,pv41,pv101], .c 3, .c 5, .c 13, .c 3, .c 17, .p pv2 [pv2,pv3,pv7,pv23663],
  .c 3, .p pv3 [pv2,pv124231], .c 7, .c 3, .p pv5 [pv2,pv993851], .c 5, .c 3,
  .p pv2 [pv2,pv17,pv29231], .c 11, .c 3, .c 5, .c 73, .c 3, .c 41, .c 19, .c 3, .c 7, .c 23,
  .c 3, .c 11, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 29, .c 3, .c 31, .c 947, .c 3, .c 401,
  .c 17, .c 3, .c 239, .c 5, .c 3, .c 7, .c 47, .c 3, .c 5, .c 11, .c 3, .c 101, .c 7, .c 3,
  .c 71, .p pv2 [pv2,pv3,pv11,pv37], .c 3, .c 17, .c 5, .c 3, .c 11, .c 167, .c 3, .c 5, .c 61,
  .c 3, .c 7, .c 31, .c 3, .c 13, .p pv7 [pv2,pv3,pv7,pv19,pv47,pv53], .c 3, .c 67, .c 5, .c 3,
  .p pv2 [pv2,pv59,pv8423], .c 211, .c 3, .c 5, .c 19, .c 3, .p pv3 [pv2,pv5,pv1553],
]
private theorem h0242c20 : checkBlock 1987587 128 b0242c20 = true := by
  decide +kernel

private def b0242c21 : List Row := [
  .c 11, .c 3, .c 43, .p pv11 [pv2,pv3,pv9203], .c 3, .c 7, .c 5, .c 3, .c 1237, .c 17, .c 3,
  .c 5, .c 7, .c 3, .c 53, .p pv5 [pv2,pv3,pv20707], .c 3, .c 79, .p pv19 [pv2,pv3,pv17,pv19489],
  .c 3, .p pv2 [pv2,pv13,pv101,pv757], .c 5, .c 3, .p pv3 [pv2,pv7,pv17749],
  .p pv2 [pv2,pv3,pv5,pv23,pv43,pv67], .c 3, .c 5, .c 751, .c 3, .p pv2 [pv2,pv5,pv103,pv193],
  .c 433, .c 3, .c 317, .c 7, .c 3, .c 19, .c 5, .c 3, .p pv13 [pv2,pv97,pv10247], .c 13, .c 3,
  .c 5, .c 197, .c 3, .c 11, .c 43, .c 3, .c 7, .p pv2 [pv2,pv3,pv110441], .c 3, .c 173, .c 5,
  .c 3, .c 229, .c 7, .c 3, .c 5, .c 67, .c 3, .c 1259, .c 17, .c 3, .c 41,
  .p pv19 [pv2,pv3,pv31,pv167], .c 3, .c 13, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv17,pv1949],
  .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv11,pv13,pv331], .c 3, .p pv11 [pv2,pv5,pv61,pv3259], .c 7,
  .c 3, .c 11, .c 13, .c 3, .c 103, .c 5, .c 3, .c 73, .p pv2 [pv2,pv3,pv5,pv37,pv199], .c 3,
  .c 5, .c 263, .c 3, .c 7, .p pv3 [pv2,pv3,pv331337], .c 3, .c 19, .c 277, .c 3,
  .p pv3 [pv2,pv31063], .c 5, .c 3, .c 367, .c 11, .c 3, .c 5, .c 37, .c 3, .c 13, .c 47, .c 3,
  .p pv13 [pv2,pv7,pv131,pv271], .c 491, .c 3, .c 7, .c 5, .c 3, .c 1019, .c 71, .c 3, .c 5, .c 7,
  .c 3, .c 599, .c 53, .c 3, .p pv5 [pv2,pv569,pv1747], .p pv7 [pv2,pv3,pv82837], .c 3, .c 193,
  .c 5, .c 3,
]
private theorem h0242c21 : checkBlock 1987843 128 b0242c21 = true := by
  decide +kernel

private def b0242c22 : List Row := [
  .c 17, .p pv13 [pv2,pv3,pv5,pv47], .c 3, .c 5, .c 11, .c 3, .c 163,
  .p pv5 [pv2,pv3,pv7,pv61,pv97], .c 3, .c 139, .c 7, .c 3, .c 31, .c 5, .c 3, .c 11, .c 41, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv53,pv521], .c 3, .c 19, .c 23, .c 3, .c 7, .c 409, .c 3, .c 29, .c 5,
  .c 3, .c 877, .c 7, .c 3, .c 5, .c 17, .c 3, .c 89, .c 11, .c 3, .p pv3 [pv2,pv313,pv397],
  .c 19, .c 3, .p pv5 [pv2,pv7,pv29,pv59,pv83], .c 5, .c 3, .c 7, .c 43, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv23669], .c 3, .c 17, .c 7, .c 3, .c 13, .c 97, .c 3, .c 41, .c 5, .c 3,
  .p pv2 [pv2,pv17,pv58477], .p pv17 [pv2,pv3,pv5,pv13,pv2549], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv4091], .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv19,pv26161], .c 11, .c 3,
  .p pv2 [pv2,pv53,pv18757], .c 5, .c 3, .p pv3 [pv2,pv157,pv1583],
  .p pv2 [pv2,pv3,pv5,pv11,pv241], .c 3, .c 5, .p pv7 [pv2,pv3,pv139,pv149], .c 3, .c 11,
  .p pv5 [pv2,pv3,pv110459], .c 3, .p pv2 [pv2,pv7,pv142019], .c 17, .c 3, .c 7, .c 5, .c 3,
  .p pv13 [pv2,pv31,pv32069], .c 23, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv198829], .c 19,
  .c 3, .p pv3 [pv2,pv248537], .p pv3 [pv2,pv3,pv13,pv29,pv293], .c 3, .c 17, .c 5, .c 3, .c 31,
  .c 13, .c 3, .c 5, .c 331, .c 3, .c 197, .p pv3 [pv2,pv3,pv7,pv6763], .c 3, .c 11, .c 7, .c 3,
  .c 941, .c 5, .c 3, .p pv2 [pv2,pv11,pv90379], .p pv2 [pv2,pv3,pv5,pv31,pv1069], .c 3, .c 5,
  .p pv17 [pv2,pv3,pv331391], .c 3, .c 79, .p pv19 [pv2,pv3,pv863],
]
private theorem h0242c22 : checkBlock 1988099 128 b0242c22 = true := by
  decide +kernel

private def b0242c23 : List Row := [
  .c 3, .c 7, .c 59, .c 3, .c 13, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 41, .c 3, .c 107,
  .c 421, .c 3, .c 101, .c 13, .c 3, .c 11, .c 5, .c 3, .c 7, .c 53, .c 3, .c 5, .c 19, .c 3,
  .p pv2 [pv2,pv5,pv198841], .c 7, .c 3, .c 37, .c 23, .c 3, .p pv13 [pv2,pv17,pv233,pv251], .c 5,
  .c 3, .c 47, .c 83, .c 3, .c 5, .c 11, .c 3, .c 7, .c 29, .c 3, .c 73, .c 43, .c 3,
  .p pv2 [pv2,pv497113], .c 5, .c 3, .c 11, .c 113, .c 3, .c 5, .c 13, .c 3,
  .p pv7 [pv2,pv5,pv11,pv18077], .c 17, .c 3, .c 59, .c 193, .c 3, .c 7, .c 5, .c 3, .c 313,
  .c 37, .c 3, .c 5, .c 7, .c 3, .c 29, .c 11, .c 3, .c 17, .c 79, .c 3, .p pv3 [pv2,pv62141],
  .c 5, .c 3, .c 13, .c 19, .c 3, .c 5, .c 89, .c 3, .p pv17 [pv2,pv5,pv29,pv6857],
  .p pv11 [pv2,pv3,pv7,pv13,pv607], .c 3, .p pv3 [pv2,pv11,pv59,pv383], .c 7, .c 3, .c 263, .c 5,
  .c 3, .p pv2 [pv2,pv497137], .p pv3 [pv2,pv3,pv5,pv491], .c 3, .c 5, .c 23, .c 3,
  .p pv3 [pv2,pv5,pv7,pv53,pv67], .p pv2 [pv2,pv3,pv157,pv2111], .c 3, .c 7, .c 11, .c 3, .c 397,
  .c 5, .c 3, .p pv2 [pv2,pv19,pv43,pv1217], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv110477], .c 3,
  .c 11, .c 73, .c 3, .c 13, .p pv7 [pv2,pv3,pv271,pv1223], .c 3, .c 23, .c 5, .c 3, .c 7,
]
private theorem h0242c23 : checkBlock 1988355 128 b0242c23 = true := by
  decide +kernel

private def b0242c24 : List Row := [
  .p pv41 [pv2,pv3,pv5,pv13,pv5099], .c 3, .c 5, .c 29, .c 3, .c 43, .c 7, .c 3, .c 67, .c 733,
  .c 3, .p pv3 [pv2,pv248579], .c 5, .c 3, .c 37, .c 283, .c 3, .c 5, .c 181, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv165721], .c 3, .c 11, .p pv2 [pv2,pv3,pv7,pv5261], .c 3, .c 509, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv45197], .p pv3 [pv2,pv3,pv5,pv151,pv439], .c 3, .c 5, .c 17, .c 3, .c 31,
  .p pv3 [pv2,pv3,pv331447], .c 3, .c 113, .p pv11 [pv2,pv3,pv13,pv3187], .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv691,pv1439], .c 11, .c 3, .c 5, .c 7, .c 3, .c 17, .c 37, .c 3, .c 269, .c 53,
  .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv7,pv17,pv2089], .c 1193, .c 3, .c 5, .c 701, .c 3, .c 23,
  .c 31, .c 3, .c 227, .c 7, .c 3, .c 13, .c 5, .c 3, .p pv11 [pv2,pv47,pv21157], .c 67, .c 3,
  .c 5, .c 11, .c 3, .c 829, .c 367, .c 3, .c 7, .c 13, .c 3, .c 61, .c 5, .c 3, .c 11, .c 7,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv9749], .c 3, .p pv3 [pv2,pv5,pv11,pv113], .c 167, .c 3,
  .p pv5 [pv2,pv19,pv199,pv263], .c 107, .c 3, .c 17, .c 5, .c 3, .c 7, .c 151, .c 3, .c 5,
  .c 103, .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv31,pv43,pv373], .p pv13 [pv2,pv3,pv110491], .c 3,
  .p pv2 [pv2,pv131,pv7591], .c 5, .c 3, .c 29, .p pv3 [pv2,pv3,pv5,pv13259], .c 3, .c 5, .c 13,
  .c 3, .c 7, .c 19, .c 3,
]
private theorem h0242c24 : checkBlock 1988611 128 b0242c24 = true := by
  decide +kernel

private def b0242c25 : List Row := [
  .c 31, .c 41, .c 3, .c 1063, .c 5, .c 3, .c 23, .c 17, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv211,pv1571], .c 3, .p pv2 [pv2,pv5,pv59,pv3371], .c 1091, .c 3,
  .p pv5 [pv2,pv7,pv13,pv683], .c 11, .c 3, .c 7, .c 5, .c 3, .c 13, .c 953, .c 3, .c 5, .c 7,
  .c 3, .c 11, .c 71, .c 3, .c 1289, .c 31, .c 3, .p pv2 [pv2,pv11,pv17,pv2659], .c 5, .c 3,
  .c 19, .p pv13 [pv2,pv3,pv5,pv33149], .c 3, .c 5, .c 127, .c 3, .c 41, .c 467, .c 3, .c 389,
  .c 7, .c 3, .p pv2 [pv2,pv67,pv14843], .c 5, .c 3, .c 523, .c 23, .c 3, .c 5, .c 19, .c 3,
  .c 173, .c 17, .c 3, .c 7, .c 929, .c 3, .c 47, .c 5, .c 3, .p pv11 [pv2,pv11,pv8219], .c 7,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv331501], .c 3, .c 743, .c 13, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv110501], .c 3, .c 29, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 53, .c 3,
  .c 491, .c 7, .c 3, .c 557, .p pv7 [pv2,pv3,pv179,pv463], .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv193,pv5153], .c 89, .c 3, .c 5, .c 59, .c 3, .c 7, .p pv13 [pv2,pv3,pv19,pv727],
  .c 3, .p pv2 [pv2,pv497269], .c 563, .c 3, .c 37, .c 5, .c 3, .c 163, .c 13, .c 3, .c 5, .c 11,
  .c 3, .p pv2 [pv2,pv5,pv19891], .c 137, .c 3, .p pv2 [pv2,pv7,pv20297], .c 23, .c 3, .c 7, .c 5,
  .c 3, .c 11, .c 233,
]
private theorem h0242c25 : checkBlock 1988867 128 b0242c25 = true := by
  decide +kernel

private def b0242c26 : List Row := [
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv11,pv13,pv107], .p pv2 [pv2,pv3,pv23,pv7207], .c 3,
  .c 43, .c 29, .c 3, .c 13, .c 5, .c 3, .c 61, .p pv3 [pv2,pv3,pv5,pv89,pv149], .c 3, .c 5,
  .c 37, .c 3, .p pv3 [pv2,pv5,pv223], .c 11, .c 3, .c 19, .c 7, .c 3, .c 1327, .c 5, .c 3, .c 97,
  .c 47, .c 3, .c 5, .c 17, .c 3, .c 823, .p pv11 [pv2,pv3,pv82883], .c 3, .c 7, .c 281, .c 3,
  .p pv2 [pv2,pv433,pv2297], .c 5, .c 3, .c 373, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv6907], .c 3,
  .c 13, .c 43, .c 3, .c 179, .c 11, .c 3, .p pv3 [pv2,pv7,pv17761], .c 5, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv5,pv11,pv137], .c 3, .c 5, .c 13, .c 3, .c 11, .c 7, .c 3, .c 541,
  .p pv19 [pv2,pv3,pv331543], .c 3, .p pv5 [pv2,pv11,pv19,pv4759], .c 5, .c 3, .c 839, .c 61,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv97,pv1709], .c 3, .c 7, .c 821, .c 3, .c 479, .c 17, .c 3, .c 23,
  .c 5, .c 3, .c 13, .c 31, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv17,pv197], .c 3, .c 337, .c 29,
  .c 3, .c 11, .c 19, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv11,pv89,pv127], .c 809, .c 3, .c 5,
  .c 7, .c 3, .p pv2 [pv2,pv5,pv17,pv5851], .c 587, .c 3, .c 157, .c 71, .c 3,
  .p pv3 [pv2,pv43,pv5783], .c 5, .c 3, .c 109, .c 11, .c 3, .c 5, .c 397, .c 3, .c 29, .c 97,
  .c 3, .c 13,
]
private theorem h0242c26 : checkBlock 1989123 128 b0242c26 = true := by
  decide +kernel

private def b0242c27 : List Row := [
  .c 7, .c 3, .c 11, .c 5, .c 3, .c 691, .c 17, .c 3, .c 5, .c 101, .c 3,
  .p pv3 [pv2,pv5,pv7,pv29], .c 13, .c 3, .c 7, .c 1069, .c 3, .p pv2 [pv2,pv419,pv1187], .c 5,
  .c 3, .p pv2 [pv2,pv994709], .c 7, .c 3, .c 5, .c 11, .c 3, .c 23, .c 19, .c 3, .c 257, .c 547,
  .c 3, .c 41, .c 5, .c 3, .c 7, .c 107, .c 3, .c 5, .c 79, .c 3, .c 53, .c 7, .c 3, .c 311,
  .c 73, .c 3, .c 719, .c 5, .c 3, .p pv7 [pv2,pv113,pv8803], .c 13, .c 3, .c 5, .c 29, .c 3,
  .c 7, .c 11, .c 3, .c 131, .p pv2 [pv2,pv3,pv7,pv67,pv101], .c 3, .c 197, .c 5, .c 3, .c 19,
  .c 463, .c 3, .c 5, .p pv2 [pv2,pv3,pv29,pv5717], .c 3, .c 659, .c 23, .c 3, .c 17, .c 1171,
  .c 3, .c 7, .c 5, .c 3, .c 59, .c 887, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv39791],
  .p pv5 [pv2,pv3,pv181,pv229], .c 3, .c 47, .c 11, .c 3, .p pv2 [pv2,pv71,pv14011], .c 5, .c 3,
  .c 23, .p pv2 [pv2,pv3,pv5,pv11,pv6029], .c 3, .c 5, .c 109, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv7,pv127,pv373], .c 3, .c 233, .c 7, .c 3, .c 83, .c 5, .c 3, .c 101, .c 37,
  .c 3, .c 5, .c 41, .c 3, .c 13, .p pv2 [pv2,pv3,pv17,pv3251], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv331603], .c 3, .c 19, .c 5, .c 3, .c 17, .c 7, .c 3,
]
private theorem h0242c27 : checkBlock 1989379 128 b0242c27 = true := by
  decide +kernel

private def b0242c28 : List Row := [
  .c 5, .c 13, .c 3, .c 331, .p pv2 [pv2,pv3,pv19,pv31,pv563], .c 3, .c 11, .c 349, .c 3, .c 43,
  .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 307, .c 3, .p pv13 [pv2,pv5,pv198967], .c 7, .c 3,
  .c 251, .p pv3 [pv2,pv3,pv331613], .c 3, .p pv5 [pv2,pv271,pv3671], .c 5, .c 3, .c 13, .c 11,
  .c 3, .c 5, .c 17, .c 3, .c 7, .c 677, .c 3, .c 23, .c 127, .c 3, .c 11, .c 5, .c 3, .c 29,
  .p pv13 [pv2,pv3,pv5,pv5527], .c 3, .c 5, .c 151, .c 3, .c 17, .c 181, .c 3, .c 19, .c 43, .c 3,
  .c 7, .c 5, .c 3, .c 37, .c 1229, .c 3, .c 5, .c 7, .c 3, .c 73, .c 293, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv11,pv7537], .c 3, .c 79, .c 5, .c 3, .c 11, .c 229, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv37,pv8963], .c 3, .p pv11 [pv2,pv5,pv11,pv18089], .c 13, .c 3, .c 31, .c 7,
  .c 3, .p pv2 [pv2,pv994901], .c 5, .c 3, .c 317, .p pv19 [pv2,pv3,pv5,pv22109], .c 3, .c 5,
  .c 113, .c 3, .c 1223, .c 11, .c 3, .c 7, .c 223, .c 3, .c 17, .c 5, .c 3, .c 47, .c 7, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv71,pv173], .c 3, .c 19, .c 41, .c 3, .c 103, .c 31, .c 3,
  .p pv5 [pv2,pv7,pv89,pv1597], .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv23689],
  .c 3, .c 61, .c 7, .c 3, .c 467, .c 11,
]
private theorem h0242c28 : checkBlock 1989635 128 b0242c28 = true := by
  decide +kernel

private def b0242c29 : List Row := [
  .c 3, .c 29, .c 5, .c 3, .p pv2 [pv2,pv994949], .c 17, .c 3, .c 5, .c 73, .c 3, .c 7, .c 877,
  .c 3, .c 71, .p pv3 [pv2,pv3,pv7,pv17,pv929], .c 3, .c 13, .c 5, .c 3, .c 1021, .c 79, .c 3,
  .c 5, .c 23, .c 3, .c 211, .c 179, .c 3, .p pv2 [pv2,pv7,pv19,pv7481], .c 13, .c 3, .c 7, .c 5,
  .c 3, .p pv11 [pv2,pv907,pv1097], .p pv19 [pv2,pv3,pv5,pv7,pv23,pv103], .c 3, .c 5, .c 7, .c 3,
  .c 37, .p pv2 [pv2,pv3,pv167,pv331], .c 3, .c 11, .p pv3 [pv2,pv3,pv331663], .c 3, .c 23, .c 5,
  .c 3, .p pv17 [pv2,pv7,pv11,pv13,pv71], .c 53, .c 3, .c 5, .c 43, .c 3, .c 13, .c 17, .c 3,
  .p pv5 [pv2,pv23,pv43261], .c 7, .c 3, .c 109, .c 5, .c 3, .c 173, .c 11, .c 3, .c 5, .c 13,
  .c 3, .p pv7 [pv2,pv5,pv7,pv28429], .p pv5 [pv2,pv3,pv11,pv3769], .c 3, .c 7,
  .p pv19 [pv2,pv3,pv29,pv11437], .c 3, .c 11, .c 5, .c 3, .c 853, .c 7, .c 3, .c 5, .c 1201,
  .c 3, .c 673, .c 103, .c 3, .c 29, .p pv23 [pv2,pv3,pv383,pv433], .c 3, .c 577, .c 5, .c 3,
  .c 7, .p pv19 [pv2,pv3,pv5,pv691], .c 3, .c 5, .c 11, .c 3, .c 83, .c 7, .c 3, .c 53, .c 41,
  .c 3, .p pv5 [pv2,pv995051], .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv66337], .c 3, .c 5, .c 19,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv17,pv109,pv179], .c 3, .c 739, .c 59, .c 3,
  .p pv2 [pv2,pv157,pv3169], .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv41,pv809], .c 3, .c 5,
]
private theorem h0242c29 : checkBlock 1989891 128 b0242c29 = true := by
  decide +kernel

private def b0242c30 : List Row := [
  .p pv2 [pv2,pv3,pv331691], .c 3, .p pv7 [pv2,pv5,pv53,pv751], .c 11, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv331693], .c 3, .c 7, .c 5, .c 3, .c 31, .p pv3 [pv2,pv3,pv5,pv7,pv13], .c 3,
  .c 5, .c 7, .c 3, .c 41, .c 13, .c 3, .p pv5 [pv2,pv11,pv61,pv1483],
  .p pv2 [pv2,pv3,pv59,pv937], .c 3, .c 19, .c 5, .c 3, .c 73, .c 71, .c 3, .c 5, .c 17, .c 3,
  .p pv2 [pv2,pv5,pv199021], .c 23, .c 3, .c 127, .c 7, .c 3, .p pv7 [pv2,pv13,pv41,pv1867], .c 5,
  .c 3, .p pv2 [pv2,pv497557], .c 19, .c 3, .c 5, .p pv2 [pv2,pv3,pv23,pv7211], .c 3, .c 11,
  .p pv2 [pv2,pv3,pv110569], .c 3, .c 7, .p pv11 [pv2,pv3,pv13,pv6379], .c 3,
  .p pv3 [pv2,pv11,pv45233], .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 37, .c 3, .c 661,
  .p pv5 [pv2,pv3,pv71,pv73], .c 3, .p pv2 [pv2,pv181,pv2749], .p pv3 [pv2,pv3,pv36857], .c 3,
  .c 131, .c 5, .c 3, .c 7, .c 197, .c 3, .c 5, .c 1087, .c 3, .c 179, .c 7, .c 3, .c 11, .c 17,
  .c 3, .c 13, .c 5, .c 3, .p pv7 [pv2,pv11,pv90469], .p pv13 [pv2,pv3,pv5,pv8293], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv13,pv17,pv19,pv79], .c 3, .c 7, .c 1237, .c 3, .p pv3 [pv2,pv137,pv227],
  .c 13, .c 3, .c 17, .c 5, .c 3, .c 293, .c 11, .c 3, .c 5, .c 29, .c 3,
  .p pv3 [pv2,pv5,pv17,pv2927], .c 211, .c 3, .c 313, .c 61, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv37,pv2069], .p pv2 [pv2,pv3,pv5,pv7,pv677], .c 3, .c 5, .c 7, .c 3, .c 13,
  .c 163, .c 3, .c 23, .c 443, .c 3,
]
private theorem h0242c30 : checkBlock 1990147 128 b0242c30 = true := by
  decide +kernel

private def b0242c31 : List Row := [
  .c 47, .c 5, .c 3, .c 193, .c 17, .c 3, .c 5, .c 11, .c 3, .c 19, .c 83, .c 3, .c 41, .c 7,
  .c 3, .p pv3 [pv2,pv62201], .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv19,pv97], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv157,pv2113], .c 3, .c 383, .p pv2 [pv2,pv3,pv37,pv4483], .c 3, .c 7, .c 19,
  .c 3, .p pv5 [pv2,pv17,pv58543], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 599, .c 3,
  .p pv3 [pv2,pv5,pv139,pv179], .c 11, .c 3, .p pv5 [pv2,pv995243], .c 23, .c 3,
  .p pv2 [pv2,pv7,pv71089], .c 5, .c 3, .c 7, .c 433, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv83,pv571],
  .c 3, .c 499, .c 7, .c 3, .c 587, .c 233, .c 3, .p pv2 [pv2,pv277,pv3593], .c 5, .c 3,
  .p pv3 [pv2,pv15551], .c 29, .c 3, .c 5, .c 97, .c 3, .c 7, .p pv3 [pv2,pv3,pv59,pv5623], .c 3,
  .c 13, .c 11, .c 3, .p pv3 [pv2,pv61,pv4079], .c 5, .c 3, .p pv7 [pv2,pv23,pv109,pv397],
  .c 1307, .c 3, .c 5, .c 353, .c 3, .c 11, .c 13, .c 3, .p pv3 [pv2,pv7,pv2539],
  .p pv2 [pv2,pv3,pv103,pv3221], .c 3, .c 7, .c 5, .c 3, .c 29, .c 41, .c 3, .c 5, .c 7, .c 3,
  .c 59, .c 31, .c 3, .p pv5 [pv2,pv995303], .c 101, .c 3, .c 61, .c 5, .c 3, .c 139,
  .p pv2 [pv2,pv3,pv5,pv11059], .c 3, .c 5, .c 23, .c 3, .c 239, .c 151, .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv43,pv79,pv293], .c 5, .c 3, .c 17, .c 13, .c 3, .c 5, .p pv5 [pv2,pv3],
]
private theorem h0242c31 : checkBlock 1990403 128 b0242c31 = true := by
  decide +kernel

def rows0242 : List Row :=
  b0242c00 ++ b0242c01 ++ b0242c02 ++ b0242c03 ++ b0242c04 ++ b0242c05 ++ b0242c06 ++ b0242c07 ++
  b0242c08 ++ b0242c09 ++ b0242c10 ++ b0242c11 ++ b0242c12 ++ b0242c13 ++ b0242c14 ++ b0242c15 ++
  b0242c16 ++ b0242c17 ++ b0242c18 ++ b0242c19 ++ b0242c20 ++ b0242c21 ++ b0242c22 ++ b0242c23 ++
  b0242c24 ++ b0242c25 ++ b0242c26 ++ b0242c27 ++ b0242c28 ++ b0242c29 ++ b0242c30 ++ b0242c31

theorem checked0242 : checkBlock 1982467 4096 rows0242 = true :=
  checkBlock_append h0242c00 (
    checkBlock_append h0242c01 (
    checkBlock_append h0242c02 (
    checkBlock_append h0242c03 (
    checkBlock_append h0242c04 (
    checkBlock_append h0242c05 (
    checkBlock_append h0242c06 (
    checkBlock_append h0242c07 (
    checkBlock_append h0242c08 (
    checkBlock_append h0242c09 (
    checkBlock_append h0242c10 (
    checkBlock_append h0242c11 (
    checkBlock_append h0242c12 (
    checkBlock_append h0242c13 (
    checkBlock_append h0242c14 (
    checkBlock_append h0242c15 (
    checkBlock_append h0242c16 (
    checkBlock_append h0242c17 (
    checkBlock_append h0242c18 (
    checkBlock_append h0242c19 (
    checkBlock_append h0242c20 (
    checkBlock_append h0242c21 (
    checkBlock_append h0242c22 (
    checkBlock_append h0242c23 (
    checkBlock_append h0242c24 (
    checkBlock_append h0242c25 (
    checkBlock_append h0242c26 (
    checkBlock_append h0242c27 (
    checkBlock_append h0242c28 (
    checkBlock_append h0242c29 (
    checkBlock_append h0242c30 (
    h0242c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
