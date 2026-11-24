/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0141
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0141.checked0141
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table018
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table021
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table025
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table032
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table042
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table043
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table064
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table118

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0141c00 : List Row := [
  .c 3, .c 7, .c 73, .c 3, .c 23, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv61,pv263], .c 3, .p pv2 [pv2,pv5,pv11551], .c 37, .c 3,
  .p pv2 [pv2,pv23,pv25111], .c 43, .c 3, .c 241, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .p pv31 [pv2,pv3,pv7,pv3929], .c 3, .c 89, .c 7, .c 3, .c 101, .c 167, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv317,pv911], .p pv47 [pv2,pv3,pv5,pv17,pv151], .c 3, .c 5, .c 29, .c 3, .c 7,
  .c 347, .c 3, .c 13, .p pv13 [pv2,pv3,pv7,pv191], .c 3, .c 97, .c 5, .c 3,
  .p pv2 [pv2,pv577589], .c 19, .c 3, .c 5, .c 11, .c 3, .c 281, .c 13, .c 3, .c 149, .c 113,
  .c 3, .c 7, .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv7,pv5501], .c 3, .c 5, .c 7, .c 3, .c 23,
  .p pv11 [pv2,pv3,pv2377], .c 3, .c 659, .c 139, .c 3, .p pv3 [pv2,pv13,pv2777], .c 5, .c 3,
  .p pv7 [pv2,pv7,pv19,pv43,pv101], .c 53, .c 3, .c 5, .p pv11 [pv2,pv3,pv31,pv6211], .c 3, .c 37,
  .c 11, .c 3, .c 19, .c 7, .c 3, .p pv5 [pv2,pv359,pv1609], .c 5, .c 3, .c 17, .c 13, .c 3, .c 5,
  .c 31, .c 3, .c 43, .c 313, .c 3, .c 7, .c 131, .c 3, .p pv2 [pv2,pv288823], .c 5, .c 3, .c 293,
  .c 7, .c 3, .c 5, .c 47, .c 3, .p pv11 [pv2,pv5,pv13,pv8887], .c 23, .c 3,
  .p pv2 [pv2,pv367,pv787], .c 11, .c 3, .c 13, .c 5, .c 3, .c 7,
]
private theorem h0141c00 : checkBlock 1155075 128 b0141c00 = true := by
  decide +kernel

private def b0141c01 : List Row := [
  .c 29, .c 3, .c 5, .c 17, .c 3, .c 11, .c 7, .c 3, .c 53, .c 13, .c 3, .c 251, .c 5, .c 3,
  .c 23, .c 631, .c 3, .c 5, .c 43, .c 3, .c 7, .p pv2 [pv2,pv3,pv96281], .c 3,
  .p pv3 [pv2,pv72211], .p pv2 [pv2,pv3,pv7,pv27509], .c 3, .c 71, .c 5, .c 3, .c 29, .c 503,
  .c 3, .c 5, .c 59, .c 3, .c 13, .p pv2 [pv2,pv3,pv64189], .c 3, .c 11, .c 19, .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv11,pv29,pv1811], .c 41, .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv227,pv509], .c 719, .c 3, .p pv2 [pv2,pv37,pv211], .c 17, .c 3, .c 83, .c 5,
  .c 3, .p pv17 [pv2,pv7,pv47,pv439], .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv59], .c 3,
  .p pv2 [pv2,pv5,pv57773], .c 31, .c 3, .c 173, .c 7, .c 3, .c 11, .c 5, .c 3, .c 13, .c 1063,
  .c 3, .c 5, .c 89, .c 3, .c 193, .c 107, .c 3, .c 7, .p pv2 [pv2,pv3,pv192583], .c 3, .c 41,
  .c 5, .c 3, .c 109, .c 7, .c 3, .c 5, .c 11, .c 3, .c 331, .c 19, .c 3,
  .p pv5 [pv2,pv83,pv6961], .p pv13 [pv2,pv3,pv11,pv1459], .c 3, .c 79, .c 5, .c 3, .c 7, .c 17,
  .c 3, .c 5, .c 37, .c 3, .c 131, .c 7, .c 3, .c 13, .c 53, .c 3, .c 29, .c 5, .c 3,
  .p pv3 [pv2,pv72223], .c 379, .c 3, .c 5, .p pv7 [pv2,pv3,pv89,pv541], .c 3, .c 7, .c 11, .c 3,
]
private theorem h0141c01 : checkBlock 1155331 128 b0141c01 = true := by
  decide +kernel

private def b0141c02 : List Row := [
  .c 31, .c 23, .c 3, .c 199, .c 5, .c 3, .c 19, .p pv7 [pv2,pv3,pv5,pv107], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv192601], .c 3, .p pv2 [pv2,pv5,pv115561], .p pv2 [pv2,pv3,pv23,pv53,pv79],
  .c 3, .p pv5 [pv2,pv7,pv11,pv67], .p pv3 [pv2,pv3,pv19,pv31,pv109], .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv288907], .p pv3 [pv2,pv3,pv5,pv7,pv5503], .c 3, .c 5, .c 7, .c 3, .c 617, .c 17,
  .c 3, .c 211, .c 11, .c 3, .p pv2 [pv2,pv288913], .c 5, .c 3, .p pv2 [pv2,pv7,pv23,pv37,pv97],
  .c 13, .c 3, .c 5, .c 41, .c 3, .c 11, .c 619, .c 3, .c 17, .c 7, .c 3, .c 47, .c 5, .c 3,
  .p pv3 [pv2,pv144461], .c 79, .c 3, .c 5, .p pv29 [pv2,pv3,pv24077], .c 3,
  .p pv2 [pv2,pv5,pv7,pv13,pv127], .p pv19 [pv2,pv3,pv192617], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv29,pv41], .c 3, .c 13, .c 5, .c 3, .c 389, .c 7, .c 3, .c 5, .c 23, .c 3,
  .c 577, .p pv13 [pv2,pv3,pv19,pv37,pv137], .c 3, .c 11, .c 13, .c 3, .c 101, .c 5, .c 3, .c 7,
  .c 19, .c 3, .c 5, .c 593, .c 3, .c 887, .c 7, .c 3, .c 61, .c 37, .c 3, .c 23, .c 5, .c 3,
  .c 17, .c 11, .c 3, .c 5, .c 443, .c 3, .c 7, .c 149, .c 3, .c 43, .c 197, .c 3, .c 11, .c 5,
  .c 3, .c 71, .c 547, .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv57791],
  .p pv5 [pv2,pv3,pv192637], .c 3, .c 19, .p pv7 [pv2,pv3,pv61,pv1579], .c 3, .c 7, .c 5, .c 3,
  .c 563, .p pv13 [pv2,pv3,pv5,pv7,pv43],
]
private theorem h0141c02 : checkBlock 1155587 128 b0141c02 = true := by
  decide +kernel

private def b0141c03 : List Row := [
  .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv23117], .c 29, .c 3, .c 347,
  .p pv3 [pv2,pv3,pv11,pv83,pv211], .c 3, .p pv5 [pv2,pv577931], .c 5, .c 3, .c 11, .c 47, .c 3,
  .c 5, .c 53, .c 3, .c 17, .c 43, .c 3, .c 439, .c 7, .c 3, .c 269, .c 5, .c 3,
  .p pv2 [pv2,pv17,pv33997], .p pv2 [pv2,pv3,pv5,pv3853], .c 3, .c 5, .p pv3 [pv2,pv3,pv64217],
  .c 3, .c 23, .c 11, .c 3, .c 7, .p pv3 [pv2,pv3,pv47,pv4099], .c 3, .p pv2 [pv2,pv19,pv1601],
  .c 5, .c 3, .p pv3 [pv2,pv31,pv59,pv79], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv12041], .c 3,
  .c 19, .p pv3 [pv2,pv3,pv149,pv431], .c 3, .c 13, .c 17, .c 3, .p pv3 [pv2,pv7,pv10321], .c 5,
  .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv13,pv19], .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv17,pv1619], .c 3,
  .p pv2 [pv2,pv5,pv115597], .c 7, .c 3, .p pv3 [pv2,pv144497], .c 11, .c 3, .c 17, .c 5, .c 3,
  .c 953, .c 37, .c 3, .c 5, .p pv5 [pv2,pv3,pv163,pv197], .c 3, .c 7, .c 23, .c 3, .c 79,
  .p pv11 [pv2,pv3,pv7,pv983], .c 3, .p pv2 [pv2,pv11,pv13,pv43,pv47], .c 5, .c 3,
  .p pv2 [pv2,pv67,pv8627], .c 31, .c 3, .c 5, .c 29, .c 3, .p pv7 [pv2,pv5,pv115603],
  .p pv5 [pv2,pv3,pv223], .c 3, .p pv2 [pv2,pv7,pv19,pv41,pv53], .p pv11 [pv2,pv3,pv13,pv14821],
  .c 3, .c 7, .c 5, .c 3, .c 23, .c 13, .c 3, .c 5, .c 7, .c 3, .c 809, .c 139, .c 3, .c 11,
  .c 211, .c 3, .p pv3 [pv2,pv23,pv61,pv103], .c 5, .c 3, .p pv7 [pv2,pv7,pv11,pv7507], .c 127,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv79,pv271], .c 3, .c 149, .c 19, .c 3, .p pv3 [pv2,pv1129],
]
private theorem h0141c03 : checkBlock 1155843 128 b0141c03 = true := by
  decide +kernel

private def b0141c04 : List Row := [
  .c 7, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv389,pv743], .c 11, .c 3, .c 5, .c 541, .c 3,
  .p pv11 [pv2,pv5,pv7,pv4129], .c 191, .c 3, .c 7, .c 13, .c 3, .c 11, .c 5, .c 3, .c 37, .c 7,
  .c 3, .c 5, .c 101, .c 3, .p pv19 [pv2,pv5,pv19,pv1217], .c 17, .c 3, .p pv2 [pv2,pv289039],
  .c 41, .c 3, .c 109, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv17,pv2267], .c 3, .c 5, .c 11,
  .c 3, .c 13, .c 7, .c 3, .c 17, .c 647, .c 3, .c 197, .c 5, .c 3, .c 11, .c 29, .c 3, .c 5,
  .c 13, .c 3, .c 7, .c 37, .c 3, .p pv3 [pv2,pv113,pv1279], .c 67, .c 3, .c 59, .c 5, .c 3,
  .p pv2 [pv2,pv181,pv1597], .p pv13 [pv2,pv3,pv5,pv29,pv443], .c 3, .c 5, .c 349, .c 3, .c 41,
  .c 11, .c 3, .c 47, .p pv7 [pv2,pv3,pv53,pv101], .c 3, .c 7, .c 5, .c 3, .c 13,
  .p pv11 [pv2,pv3,pv5,pv7,pv2753], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv43,pv2689], .c 83,
  .c 3, .c 383, .c 23, .c 3, .c 19, .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv38543], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv48179], .c 3, .c 53, .p pv5 [pv2,pv3,pv7,pv19,pv23], .c 3,
  .p pv2 [pv2,pv17,pv71,pv479], .c 7, .c 3, .c 43, .c 5, .c 3, .c 683, .c 19, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv439], .c 3, .c 11, .p pv2 [pv2,pv3,pv173,pv557], .c 3, .c 7, .c 359, .c 3,
  .p pv5 [pv2,pv11,pv52561], .c 5, .c 3, .c 101, .c 7, .c 3,
]
private theorem h0141c04 : checkBlock 1156099 128 b0141c04 = true := by
  decide +kernel

private def b0141c05 : List Row := [
  .c 5, .c 17, .c 3, .c 37, .c 13, .c 3, .p pv5 [pv2,pv578183], .p pv13 [pv2,pv3,pv24091], .c 3,
  .c 431, .c 5, .c 3, .c 7, .c 103, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv11,pv2503], .c 3, .c 17,
  .c 7, .c 3, .c 11, .c 43, .c 3, .p pv2 [pv2,pv13,pv79,pv563], .c 5, .c 3, .c 181, .c 263, .c 3,
  .c 5, .c 23, .c 3, .c 7, .p pv3 [pv2,pv3,pv192737], .c 3, .p pv2 [pv2,pv578213],
  .p pv2 [pv2,pv3,pv7,pv13,pv353], .c 3, .c 29, .c 5, .c 3, .c 83, .c 11, .c 3, .c 5, .c 797,
  .c 3, .p pv2 [pv2,pv5,pv101,pv229], .p pv2 [pv2,pv3,pv11,pv8761], .c 3,
  .p pv5 [pv2,pv7,pv107,pv193], .c 17, .c 3, .c 7, .c 5, .c 3, .c 307, .c 293, .c 3, .c 5, .c 7,
  .c 3, .c 79, .p pv2 [pv2,pv3,pv47,pv1367], .c 3, .c 41, .c 941, .c 3, .c 13, .c 5, .c 3, .c 61,
  .p pv23 [pv2,pv3,pv5,pv257], .c 3, .c 5, .c 11, .c 3, .c 19, .c 53, .c 3, .c 31, .c 7, .c 3,
  .p pv2 [pv2,pv83,pv6967], .c 5, .c 3, .c 11, .c 97, .c 3, .c 5, .p pv5 [pv2,pv3,pv16063], .c 3,
  .p pv2 [pv2,pv5,pv7,pv11,pv751], .c 433, .c 3, .c 7, .c 19, .c 3, .p pv3 [pv2,pv144569], .c 5,
  .c 3, .c 241, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv53,pv3637], .c 3, .c 13, .c 11, .c 3, .c 59,
  .c 31, .c 3, .c 37, .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv71,pv181], .c 3, .c 5, .c 13, .c 3,
  .c 23, .c 7, .c 3, .c 29, .c 311,
]
private theorem h0141c05 : checkBlock 1156355 128 b0141c05 = true := by
  decide +kernel

private def b0141c06 : List Row := [
  .c 3, .p pv2 [pv2,pv17,pv73,pv233], .c 5, .c 3, .c 53, .c 61, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv21419], .c 3, .c 7, .p pv29 [pv2,pv3,pv48193], .c 3,
  .p pv2 [pv2,pv13,pv29,pv59], .c 11, .c 3, .p pv2 [pv2,pv167,pv3463], .c 5, .c 3, .c 13, .c 41,
  .c 3, .c 5, .c 37, .c 3, .c 11, .c 17, .c 3, .c 457, .c 599, .c 3, .c 7, .c 5, .c 3, .c 229,
  .p pv37 [pv2,pv3,pv5,pv7,pv17], .c 3, .c 5, .c 7, .c 3, .c 137, .c 23, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv179,pv359], .c 3, .c 31, .c 5, .c 3, .p pv2 [pv2,pv7,pv109,pv379],
  .p pv17 [pv2,pv3,pv5,pv38557], .c 3, .c 5, .c 47, .c 3, .p pv3 [pv2,pv5,pv19,pv761], .c 29,
  .c 3, .c 11, .c 7, .c 3, .c 41, .c 5, .c 3, .c 19, .p pv7 [pv2,pv3,pv5,pv13,pv1483], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv192791], .c 3, .p pv13 [pv2,pv5,pv7,pv661], .c 13, .c 3, .c 7, .c 467, .c 3,
  .c 877, .c 5, .c 3, .p pv3 [pv2,pv37,pv977], .c 7, .c 3, .c 5, .c 19, .c 3, .c 29,
  .p pv3 [pv2,pv3,pv11,pv17,pv1031], .c 3, .c 199, .c 821, .c 3, .c 11, .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv241], .c 3, .c 5, .p pv11 [pv2,pv3,pv7,pv9181], .c 3, .c 47, .c 7, .c 3,
  .c 109, .p pv2 [pv2,pv3,pv13,pv14831], .c 3, .p pv5 [pv2,pv67,pv89,pv97], .c 5, .c 3, .c 43,
  .c 13, .c 3, .c 5, .c 11, .c 3, .c 7, .c 127, .c 3, .p pv5 [pv2,pv571,pv1013],
  .p pv67 [pv2,pv3,pv7,pv11,pv313], .c 3, .c 19, .c 5, .c 3, .c 11, .c 131, .c 3, .c 5,
]
private theorem h0141c06 : checkBlock 1156611 128 b0141c06 = true := by
  decide +kernel

private def b0141c07 : List Row := [
  .c 17, .c 3, .c 719, .p pv5 [pv2,pv3,pv19,pv43,pv59], .c 3, .c 23, .c 37, .c 3, .c 7, .c 5,
  .c 3, .c 31, .c 19, .c 3, .c 5, .c 7, .c 3, .c 17, .c 11, .c 3, .p pv2 [pv2,pv578453], .c 13,
  .c 3, .c 211, .c 5, .c 3, .c 97, .c 337, .c 3, .c 5, .p pv5 [pv2,pv3,pv29,pv61,pv109], .c 3,
  .c 59, .c 157, .c 3, .c 53, .c 7, .c 3, .c 593, .c 5, .c 3, .p pv2 [pv2,pv13,pv19,pv1171],
  .c 31, .c 3, .c 5, .c 509, .c 3, .c 13, .p pv2 [pv2,pv3,pv151,pv1277], .c 3, .c 7, .c 11, .c 3,
  .c 827, .c 5, .c 3, .c 41, .c 7, .c 3, .c 5, .c 13, .c 3, .c 11, .c 677, .c 3,
  .p pv2 [pv2,pv289249], .c 47, .c 3, .c 17, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv38567], .c 3,
  .c 5, .p pv5 [pv2,pv3,pv7,pv71,pv97], .c 3, .c 919, .c 7, .c 3, .c 37, .c 277, .c 3,
  .p pv3 [pv2,pv144629], .c 5, .c 3, .c 13, .c 241, .c 3, .c 5, .c 1049, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv13,pv7417], .c 3, .c 11, .p pv2 [pv2,pv3,pv7,pv3061], .c 3,
  .p pv13 [pv2,pv19,pv30449], .c 5, .c 3, .p pv2 [pv2,pv11,pv26297], .c 17, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv32141], .c 3, .c 19, .c 307, .c 3, .c 43, .c 89, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv107,pv5407], .c 11, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv251,pv461], .c 79,
  .c 3, .c 13, .c 19, .c 3,
]
private theorem h0141c07 : checkBlock 1156867 128 b0141c07 = true := by
  decide +kernel

private def b0141c08 : List Row := [
  .c 11, .c 5, .c 3, .c 29, .p pv31 [pv2,pv3,pv5,pv13,pv23,pv43], .c 3, .c 5, .c 31, .c 3, .c 521,
  .c 13, .c 3, .c 223, .c 7, .c 3, .c 23, .c 5, .c 3, .p pv11 [pv2,pv29,pv71,pv281], .c 313, .c 3,
  .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv7,pv61,pv271], .c 17, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv11,pv89,pv197], .c 3, .p pv5 [pv2,pv13,pv44507], .c 5, .c 3, .c 11, .c 7,
  .c 3, .c 5, .c 173, .c 3, .p pv3 [pv2,pv5,pv11,pv263], .p pv2 [pv2,pv3,pv53,pv1213], .c 3,
  .c 17, .p pv19 [pv2,pv3,pv13,pv3709], .c 3, .p pv5 [pv2,pv7,pv37,pv1117], .c 5, .c 3, .c 7,
  .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv59,pv467], .c 3, .c 61, .c 7, .c 3,
  .p pv2 [pv2,pv289309], .c 137, .c 3, .p pv2 [pv2,pv578621], .c 5, .c 3, .c 37,
  .p pv3 [pv2,pv3,pv5,pv1543], .c 3, .c 5, .p pv5 [pv2,pv3,pv16073], .c 3, .c 7,
  .p pv17 [pv2,pv3,pv192877], .c 3, .c 89, .c 73, .c 3, .c 13, .c 5, .c 3,
  .p pv7 [pv2,pv419,pv1381], .c 47, .c 3, .c 5, .c 491, .c 3, .c 23,
  .p pv5 [pv2,pv3,pv17,pv31,pv61], .c 3, .c 811, .c 11, .c 3, .c 7, .c 5, .c 3, .c 17, .c 233,
  .c 3, .c 5, .c 7, .c 3, .c 11, .c 31, .c 3, .p pv5 [pv2,pv17,pv34039], .c 421, .c 3,
  .p pv3 [pv2,pv11,pv29,pv907], .c 5, .c 3, .p pv2 [pv2,pv7,pv13,pv6359],
  .p pv7 [pv2,pv3,pv5,pv19289], .c 3, .c 5, .c 19, .c 3, .c 13, .c 61, .c 3,
  .p pv2 [pv2,pv89,pv3251], .c 7, .c 3, .p pv2 [pv2,pv109,pv5309], .c 5, .c 3,
  .p pv3 [pv2,pv144671], .c 71, .c 3, .c 5, .c 13,
]
private theorem h0141c08 : checkBlock 1157123 128 b0141c08 = true := by
  decide +kernel

private def b0141c09 : List Row := [
  .c 3, .p pv3 [pv2,pv5,pv7,pv1181], .c 23, .c 3, .c 7, .c 41, .c 3, .p pv3 [pv2,pv72337], .c 5,
  .c 3, .c 523, .c 7, .c 3, .c 5, .c 733, .c 3, .c 17, .p pv2 [pv2,pv3,pv96451], .c 3, .c 571,
  .c 29, .c 3, .c 19, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv1531], .c 3,
  .c 271, .c 7, .c 3, .c 31, .p pv37 [pv2,pv3,pv29,pv1663], .c 3, .c 11, .c 5, .c 3, .c 113,
  .c 19, .c 3, .c 5, .c 53, .c 3, .c 7, .c 227, .c 3, .c 29, .c 17, .c 3, .c 647, .c 5, .c 3,
  .p pv3 [pv2,pv73,pv991], .p pv2 [pv2,pv3,pv5,pv1429], .c 3, .c 5, .c 11, .c 3, .c 97,
  .p pv3 [pv2,pv3,pv192917], .c 3, .c 13, .c 31, .c 3, .c 7, .c 5, .c 3, .c 11, .c 23, .c 3, .c 5,
  .c 7, .c 3, .p pv7 [pv2,pv5,pv11,pv17,pv619], .c 13, .c 3, .c 19, .p pv2 [pv2,pv3,pv192923],
  .c 3, .c 173, .c 5, .c 3, .c 607, .c 1061, .c 3, .c 5, .p pv2 [pv2,pv3,pv19,pv5077], .c 3,
  .c 73, .c 11, .c 3, .c 23, .c 7, .c 3, .c 53, .c 5, .c 3, .p pv2 [pv2,pv578789], .c 17, .c 3,
  .c 5, .c 79, .c 3, .p pv7 [pv2,pv5,pv7,pv23,pv719], .c 29, .c 3, .c 7, .c 487, .c 3, .c 43,
  .c 5, .c 3, .p pv3 [pv2,pv144701], .c 7, .c 3, .c 5, .c 103, .c 3, .p pv2 [pv2,pv5,pv57881],
  .c 89, .c 3, .p pv2 [pv2,pv53,pv67,pv163], .c 11, .c 3, .c 31,
]
private theorem h0141c09 : checkBlock 1157379 128 b0141c09 = true := by
  decide +kernel

private def b0141c10 : List Row := [
  .c 5, .c 3, .c 7, .p pv23 [pv2,pv3,pv5,pv11,pv877], .c 3, .c 5, .c 131, .c 3, .c 11, .c 7, .c 3,
  .c 47, .c 23, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv289417], .p pv13 [pv2,pv3,pv5,pv19,pv677],
  .c 3, .c 5, .c 787, .c 3, .c 7, .c 17, .c 3, .c 401, .c 13, .c 3, .c 37, .c 5, .c 3,
  .p pv2 [pv2,pv59,pv9811], .p pv11 [pv2,pv3,pv5,pv17,pv227], .c 3, .c 5, .c 73, .c 3,
  .p pv7 [pv2,pv5,pv115771], .p pv37 [pv2,pv3,pv89,pv271], .c 3, .c 11, .c 61, .c 3, .c 7, .c 5,
  .c 3, .p pv3 [pv2,pv11,pv13,pv23], .c 139, .c 3, .c 5, .c 7, .c 3, .c 13, .c 479, .c 3,
  .p pv2 [pv2,pv19,pv30467], .p pv2 [pv2,pv3,pv96479], .c 3, .c 283, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv41,pv2017], .c 11, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv115777],
  .p pv23 [pv2,pv3,pv7,pv11,pv179], .c 3, .c 233, .c 7, .c 3, .c 11, .c 5, .c 3, .c 163,
  .p pv19 [pv2,pv3,pv5,pv38593], .c 3, .c 5, .c 23, .c 3, .c 89, .c 19, .c 3, .c 7, .c 383, .c 3,
  .c 1031, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv115783],
  .p pv7 [pv2,pv3,pv13,pv1237], .c 3, .p pv2 [pv2,pv17,pv17027],
  .p pv11 [pv2,pv3,pv11,pv53,pv331], .c 3, .c 23, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv31,pv83], .c 3, .c 5, .c 181, .c 3, .c 43, .c 7, .c 3, .c 599,
  .p pv2 [pv2,pv3,pv71,pv151], .c 3, .p pv3 [pv2,pv72367], .c 5, .c 3, .c 19, .c 31, .c 3, .c 5,
  .c 17, .c 3,
]
private theorem h0141c10 : checkBlock 1157635 128 b0141c10 = true := by
  decide +kernel

private def b0141c11 : List Row := [
  .c 7, .c 11, .c 3, .c 13, .p pv2 [pv2,pv3,pv7,pv19,pv1451], .c 3, .c 79, .c 5, .c 3, .c 131,
  .c 113, .c 3, .c 5, .c 19, .c 3, .c 17, .c 13, .c 3, .c 227, .p pv7 [pv2,pv3,pv48247], .c 3,
  .c 7, .c 5, .c 3, .c 47, .c 29, .c 3, .c 5, .c 7, .c 3, .c 179, .p pv5 [pv2,pv3,pv37,pv163],
  .c 3, .c 613, .c 11, .c 3, .c 41, .c 5, .c 3, .p pv3 [pv2,pv7,pv211], .c 449, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv1787], .c 3, .c 11, .c 271, .c 3, .p pv2 [pv2,pv47,pv97,pv127], .c 7, .c 3,
  .c 19, .c 5, .c 3, .c 29, .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv11353], .c 3,
  .p pv2 [pv2,pv5,pv7,pv71,pv233], .c 739, .c 3, .c 7, .c 151, .c 3, .c 17, .c 5, .c 3, .c 103,
  .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv31,pv283], .c 3, .c 797, .c 643, .c 3, .c 11, .c 397,
  .c 3, .c 13, .c 5, .c 3, .c 7, .c 79, .c 3, .c 5, .c 31, .c 3, .p pv13 [pv2,pv5,pv115807], .c 7,
  .c 3, .p pv2 [pv2,pv43,pv6733], .c 13, .c 3, .c 97, .c 5, .c 3, .p pv29 [pv2,pv19,pv401], .c 11,
  .c 3, .c 5, .c 431, .c 3, .c 7, .c 53, .c 3, .c 19, .c 617, .c 3, .c 11, .c 5, .c 3, .c 23,
  .p pv31 [pv2,pv3,pv5,pv3217], .c 3, .c 5, .c 41, .c 3, .c 13, .p pv5 [pv2,pv3,pv103,pv937],
  .c 3, .c 37, .p pv2 [pv2,pv3,pv2383], .c 3, .c 7, .c 5,
]
private theorem h0141c11 : checkBlock 1157891 128 b0141c11 = true := by
  decide +kernel

private def b0141c12 : List Row := [
  .c 3, .c 619, .c 587, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv31,pv467], .c 197, .c 3, .c 101,
  .c 331, .c 3, .c 29, .c 5, .c 3, .c 11, .c 947, .c 3, .c 5, .p pv2 [pv2,pv3,pv193031], .c 3,
  .c 31, .c 17, .c 3, .p pv2 [pv2,pv13,pv22273], .c 7, .c 3, .p pv2 [pv2,pv19,pv29,pv1051], .c 5,
  .c 3, .c 13, .c 23, .c 3, .c 5, .p pv5 [pv2,pv3,pv48259], .c 3, .c 19, .c 11, .c 3, .c 7, .c 59,
  .c 3, .c 673, .c 5, .c 3, .c 907, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv89,pv241], .c 3,
  .p pv17 [pv2,pv5,pv41,pv113], .c 31, .c 3, .c 23, .c 19, .c 3, .p pv5 [pv2,pv7,pv53,pv223],
  .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv38609], .c 3, .c 5, .c 97, .c 3, .c 541, .c 7, .c 3,
  .c 13, .c 11, .c 3, .p pv2 [pv2,pv289573], .c 5, .c 3, .c 257, .p pv47 [pv2,pv3,pv5,pv11,pv13],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv193051], .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv19,pv15241],
  .c 283, .c 3, .p pv2 [pv2,pv11,pv37,pv1423], .c 5, .c 3, .c 17, .c 349, .c 3, .c 5, .c 743,
  .c 3, .p pv3 [pv2,pv5,pv57917], .c 109, .c 3, .c 29, .c 23, .c 3, .c 7, .c 5, .c 3, .c 37,
  .p pv11 [pv2,pv3,pv5,pv7,pv197], .c 3, .c 5, .c 7, .c 3, .c 941, .c 19, .c 3, .c 11, .c 199,
  .c 3, .p pv5 [pv2,pv107,pv5413], .c 5, .c 3, .p pv2 [pv2,pv7,pv11,pv3761], .c 13, .c 3, .c 5,
  .c 17, .c 3, .p pv7 [pv2,pv5,pv181],
]
private theorem h0141c12 : checkBlock 1158147 128 b0141c12 = true := by
  decide +kernel

private def b0141c13 : List Row := [
  .c 971, .c 3, .p pv5 [pv2,pv59,pv9817], .c 7, .c 3, .c 313, .c 5, .c 3,
  .p pv2 [pv2,pv23,pv25183], .c 11, .c 3, .c 5, .p pv7 [pv2,pv3,pv139,pv463], .c 3, .c 17, .c 37,
  .c 3, .c 7, .c 31, .c 3, .c 11, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5,
  .p pv19 [pv2,pv3,pv13,pv47,pv79], .c 3, .p pv2 [pv2,pv5,pv57923], .c 29, .c 3,
  .p pv2 [pv2,pv599,pv967], .c 13, .c 3, .p pv3 [pv2,pv7,pv137,pv151], .c 5, .c 3, .c 7,
  .p pv19 [pv2,pv3,pv5,pv1609], .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv115849], .c 7, .c 3,
  .c 67, .c 17, .c 3, .c 47, .c 5, .c 3, .c 11, .c 229, .c 3, .c 5, .c 877, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv293,pv659], .c 3, .c 53, .p pv13 [pv2,pv3,pv7,pv431], .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv373,pv1553], .p pv7 [pv2,pv3,pv5,pv19309], .c 3, .c 5, .c 13, .c 3,
  .p pv7 [pv2,pv5,pv17,pv29,pv47], .c 11, .c 3, .c 197, .c 571, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv97,pv1493], .c 101, .c 3, .c 5, .c 7, .c 3, .c 37, .c 59, .c 3,
  .p pv2 [pv2,pv11,pv13,pv4051], .c 113, .c 3, .p pv3 [pv2,pv43,pv421], .c 5, .c 3, .c 13, .c 17,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv191,pv337], .c 3, .p pv2 [pv2,pv5,pv115861],
  .p pv2 [pv2,pv3,pv7,pv13,pv1061], .c 3, .p pv3 [pv2,pv251,pv577], .c 7, .c 3, .c 151, .c 5,
  .c 3, .p pv2 [pv2,pv289657], .c 67, .c 3, .c 5, .c 29, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv59,pv1091], .c 3, .c 7, .c 71, .c 3, .p pv3 [pv2,pv11,pv17,pv1549], .c 5,
  .c 3,
]
private theorem h0141c13 : checkBlock 1158403 128 b0141c13 = true := by
  decide +kernel

private def b0141c14 : List Row := [
  .c 839, .c 7, .c 3, .c 5, .c 179, .c 3, .c 23, .p pv5 [pv2,pv3,pv101,pv239], .c 3, .c 13,
  .p pv3 [pv2,pv3,pv43,pv499], .c 3, .p pv2 [pv2,pv7,pv82763], .c 5, .c 3, .c 7, .c 47, .c 3,
  .c 5, .c 409, .c 3, .c 41, .c 7, .c 3, .c 11, .c 233, .c 3, .p pv3 [pv2,pv144839], .c 5, .c 3,
  .p pv7 [pv2,pv11,pv31,pv1699], .c 43, .c 3, .c 5, .c 773, .c 3, .c 7, .c 661, .c 3, .c 17,
  .c 53, .c 3, .p pv5 [pv2,pv13,pv41,pv1087], .c 5, .c 3, .c 31, .c 11, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv61,pv1583], .c 3, .p pv3 [pv2,pv5,pv59,pv491], .c 23, .c 3, .c 163,
  .p pv11 [pv2,pv3,pv13,pv619], .c 3, .c 7, .c 5, .c 3, .c 109, .c 13, .c 3, .c 5, .c 7, .c 3,
  .c 19, .c 751, .c 3, .c 191, .p pv3 [pv2,pv3,pv193133], .c 3, .c 37, .c 5, .c 3, .c 23, .c 29,
  .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv13,pv4457], .p pv3 [pv2,pv3,pv7,pv17,pv541], .c 3,
  .p pv2 [pv2,pv131,pv4423], .c 7, .c 3, .c 13, .c 5, .c 3, .c 11,
  .p pv13 [pv2,pv3,pv5,pv29,pv37], .c 3, .c 5, .p pv7 [pv2,pv3,pv13,pv83,pv179], .c 3, .c 79,
  .c 103, .c 3, .c 7, .c 13, .c 3, .p pv5 [pv2,pv71,pv8161], .c 5, .c 3, .c 29, .c 7, .c 3, .c 5,
  .c 37, .c 3, .p pv3 [pv2,pv5,pv7243], .c 11, .c 3, .p pv7 [pv2,pv19,pv30497], .c 463, .c 3,
  .c 43, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 17, .c 3, .c 13, .c 7,
]
private theorem h0141c14 : checkBlock 1158659 128 b0141c14 = true := by
  decide +kernel

private def b0141c15 : List Row := [
  .c 3, .c 107, .c 811, .c 3, .p pv2 [pv2,pv149,pv3889], .c 5, .c 3, .c 83, .c 223, .c 3, .c 5,
  .c 13, .c 3, .c 7, .c 19, .c 3, .c 23, .c 11, .c 3, .p pv3 [pv2,pv317,pv457], .c 5, .c 3,
  .c 431, .p pv7 [pv2,pv3,pv5,pv11,pv439], .c 3, .c 5, .c 757, .c 3, .c 11, .c 47, .c 3,
  .p pv3 [pv2,pv7,pv13,pv199], .c 43, .c 3, .c 7, .c 5, .c 3, .c 13,
  .p pv41 [pv2,pv3,pv5,pv7,pv5519], .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv19,pv61], .c 761,
  .c 3, .p pv5 [pv2,pv579503], .c 17, .c 3, .c 421, .c 5, .c 3, .c 19, .c 73, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv17,pv1033], .c 3, .p pv17 [pv2,pv5,pv115903], .c 67, .c 3, .c 11, .c 7,
  .c 3, .c 17, .c 5, .c 3, .p pv3 [pv2,pv11,pv13171], .c 683, .c 3, .c 5, .c 19, .c 3, .c 61,
  .p pv3 [pv2,pv3,pv23,pv37,pv227], .c 3, .c 7, .c 937, .c 3, .p pv3 [pv2,pv29,pv1249], .c 5,
  .c 3, .p pv11 [pv2,pv579539], .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv193181], .c 3,
  .p pv2 [pv2,pv5,pv31,pv3739], .c 13, .c 3, .c 311, .c 37, .c 3, .c 11, .c 5, .c 3, .c 7, .c 17,
  .c 3, .c 5, .c 557, .c 3, .c 31, .c 7, .c 3, .p pv5 [pv2,pv579563], .c 127, .c 3, .c 19, .c 5,
  .c 3, .p pv2 [pv2,pv579569], .c 433, .c 3, .c 5, .c 11, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv19,pv31,pv41], .c 3, .c 137, .c 29, .c 3, .c 53, .c 5, .c 3, .c 11,
]
private theorem h0141c15 : checkBlock 1158915 128 b0141c15 = true := by
  decide +kernel

private def b0141c16 : List Row := [
  .c 13, .c 3, .c 5, .c 23, .c 3, .c 659, .c 31, .c 3, .p pv5 [pv2,pv7,pv82799],
  .p pv2 [pv2,pv3,pv29,pv3331], .c 3, .c 7, .c 5, .c 3, .p pv13 [pv2,pv229,pv2531],
  .p pv11 [pv2,pv3,pv5,pv7,pv23], .c 3, .c 5, .c 7, .c 3, .c 359, .c 11, .c 3, .c 29, .c 131,
  .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv7,pv19,pv2179], .p pv13 [pv2,pv3,pv5,pv17,pv2273], .c 3,
  .c 5, .c 43, .c 3, .p pv7 [pv2,pv5,pv73,pv397], .p pv2 [pv2,pv3,pv7,pv3943], .c 3, .c 17, .c 7,
  .c 3, .c 1051, .c 5, .c 3, .p pv2 [pv2,pv579629], .c 83, .c 3, .c 5, .c 113, .c 3,
  .p pv7 [pv2,pv5,pv7,pv16561], .c 173, .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv579641], .c 5,
  .c 3, .c 227, .c 7, .c 3, .c 5, .c 809, .c 3, .c 11, .p pv13 [pv2,pv3,pv47,pv4111], .c 3, .c 31,
  .c 887, .c 3, .c 73, .c 5, .c 3, .c 7, .c 37, .c 3, .c 5, .c 13, .c 3, .c 443, .c 7, .c 3,
  .p pv3 [pv2,pv144917], .p pv2 [pv2,pv3,pv23,pv31,pv271], .c 3, .c 617, .c 5, .c 3, .c 17,
  .c 193, .c 3, .c 5, .c 41, .c 3, .c 7, .c 541, .c 3, .c 11, .c 31, .c 3, .c 419, .c 5, .c 3,
  .c 13, .p pv2 [pv2,pv3,pv5,pv19,pv113], .c 3, .c 5, .c 619, .c 3, .c 29,
  .p pv5 [pv2,pv3,pv13,pv929], .c 3, .p pv3 [pv2,pv7,pv47,pv881], .c 19, .c 3, .c 7, .c 5, .c 3,
  .c 43, .c 11, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv29,pv1999],
  .p pv11 [pv2,pv3,pv11,pv1597], .c 3,
]
private theorem h0141c16 : checkBlock 1159171 128 b0141c16 = true := by
  decide +kernel

private def b0141c17 : List Row := [
  .c 61, .p pv2 [pv2,pv3,pv53,pv1823], .c 3, .c 11, .c 5, .c 3, .c 41, .c 97, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv173,pv1117], .c 3, .c 17, .c 23, .c 3, .c 13, .c 7, .c 3,
  .p pv5 [pv2,pv31,pv18701], .c 5, .c 3, .c 37, .c 103, .c 3, .c 5, .c 11, .c 3, .c 53, .c 13,
  .c 3, .c 7, .p pv19 [pv2,pv3,pv11,pv61], .c 3, .c 31, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5,
  .c 29, .c 3, .c 997, .c 19, .c 3, .p pv2 [pv2,pv227,pv1277], .c 17, .c 3,
  .p pv2 [pv2,pv7,pv13,pv23,pv277], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv38651], .c 3, .c 5,
  .c 47, .c 3, .p pv2 [pv2,pv5,pv57977], .c 7, .c 3, .c 487, .c 61, .c 3, .c 17, .c 5, .c 3,
  .c 107, .c 13, .c 3, .c 5, .c 263, .c 3, .c 7, .c 199, .c 3, .p pv3 [pv2,pv11,pv13177], .c 673,
  .c 3, .p pv5 [pv2,pv163,pv3557], .c 5, .c 3, .c 19, .c 23, .c 3, .c 5, .p pv2 [pv2,pv3,pv1193],
  .c 3, .p pv3 [pv2,pv5,pv13,pv223], .c 41, .c 3, .c 823, .c 11, .c 3, .c 7, .c 5, .c 3, .c 173,
  .c 17, .c 3, .c 5, .c 7, .c 3, .c 11, .p pv5 [pv2,pv3,pv8053], .c 3, .c 23, .c 13, .c 3, .c 71,
  .c 5, .c 3, .p pv3 [pv2,pv7,pv31,pv167], .c 109, .c 3, .c 5, .c 373, .c 3,
  .p pv2 [pv2,pv5,pv23,pv2521], .p pv3 [pv2,pv3,pv7,pv27611], .c 3, .c 43, .c 7, .c 3, .c 1061,
  .c 5, .c 3, .c 31, .c 29,
]
private theorem h0141c17 : checkBlock 1159427 128 b0141c17 = true := by
  decide +kernel

private def b0141c18 : List Row := [
  .c 3, .c 5, .c 281, .c 3, .c 13, .c 53, .c 3, .c 7, .c 977, .c 3, .c 19, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv26357], .c 7, .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv79,pv367], .c 17,
  .c 3, .c 349, .c 23, .c 3, .c 1063, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 719, .c 3, .c 73,
  .c 7, .c 3, .c 17, .c 83, .c 3, .c 11, .c 5, .c 3, .c 13, .c 829, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv4027], .c 3, .c 7, .c 101, .c 3, .p pv2 [pv2,pv579893],
  .p pv23 [pv2,pv3,pv7,pv13807], .c 3, .c 61, .c 5, .c 3, .c 53, .c 953, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv115981], .p pv5 [pv2,pv3,pv10739], .c 3, .c 19, .c 47, .c 3, .c 7, .c 5, .c 3,
  .c 11, .c 151, .c 3, .c 5, .c 7, .c 3, .c 257, .p pv3 [pv2,pv3,pv17,pv83,pv137], .c 3, .c 13,
  .c 41, .c 3, .p pv2 [pv2,pv53,pv5471], .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv13,pv1487],
  .c 3, .c 5, .c 23, .c 3, .c 251, .c 11, .c 3, .p pv2 [pv2,pv17,pv37,pv461], .c 7, .c 3, .c 103,
  .c 5, .c 3, .p pv3 [pv2,pv72493], .c 127, .c 3, .c 5, .c 73, .c 3, .p pv2 [pv2,pv5,pv7,pv1657],
  .c 317, .c 3, .c 7, .p pv23 [pv2,pv3,pv163,pv593], .c 3, .c 23, .c 5, .c 3,
  .p pv13 [pv2,pv503,pv1153], .c 7, .c 3, .c 5, .c 17, .c 3, .c 19, .c 241, .c 3, .c 89,
]
private theorem h0141c18 : checkBlock 1159683 128 b0141c18 = true := by
  decide +kernel

private def b0141c19 : List Row := [
  .c 11, .c 3, .c 191, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 79, .c 3, .c 11, .c 7, .c 3,
  .p pv5 [pv2,pv579983], .c 19, .c 3, .p pv2 [pv2,pv11,pv41,pv643], .c 5, .c 3, .c 137,
  .p pv2 [pv2,pv3,pv5,pv19333], .c 3, .c 5, .c 37, .c 3, .c 7, .p pv5 [pv2,pv3,pv16111], .c 3,
  .p pv2 [pv2,pv289999], .c 59, .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv83,pv1747], .c 43, .c 3,
  .c 5, .c 283, .c 3, .c 347, .c 97, .c 3, .c 11, .c 13, .c 3, .c 7, .c 5, .c 3,
  .p pv11 [pv2,pv11,pv67,pv787], .p pv19 [pv2,pv3,pv5,pv7,pv1381], .c 3, .c 5, .c 7, .c 3, .c 23,
  .c 907, .c 3, .p pv3 [pv2,pv145007], .c 1033, .c 3, .c 17, .c 5, .c 3, .c 71, .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv277,pv349], .c 3, .c 13, .c 19, .c 3, .c 29, .c 7, .c 3, .c 11, .c 5, .c 3,
  .c 179, .c 47, .c 3, .c 5, .c 13, .c 3, .p pv7 [pv2,pv5,pv7,pv16573], .c 31, .c 3, .c 7, .c 379,
  .c 3, .c 193, .c 5, .c 3, .p pv3 [pv2,pv18127], .c 7, .c 3, .c 5, .c 11, .c 3,
  .p pv3 [pv2,pv5,pv19,pv43,pv71], .c 23, .c 3, .p pv2 [pv2,pv13,pv44621], .c 167, .c 3, .c 307,
  .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv2417], .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv23,pv1201],
  .c 3, .c 113, .c 7, .c 3, .c 41, .p pv13 [pv2,pv3,pv19,pv10177], .c 3, .c 43, .c 5, .c 3, .c 23,
  .c 569, .c 3,
]
private theorem h0141c19 : checkBlock 1159939 128 b0141c19 = true := by
  decide +kernel

private def b0141c20 : List Row := [
  .c 5, .c 19, .c 3, .c 7, .c 11, .c 3, .p pv5 [pv2,pv31,pv18713], .c 37, .c 3,
  .p pv2 [pv2,pv23,pv12611], .c 5, .c 3, .p pv2 [pv2,pv41,pv14149],
  .p pv17 [pv2,pv3,pv5,pv61,pv317], .c 3, .c 5, .p pv2 [pv2,pv3,pv43,pv1499], .c 3, .c 557, .c 17,
  .c 3, .c 13, .c 67, .c 3, .c 7, .c 5, .c 3, .c 281, .p pv3 [pv2,pv3,pv5,pv7,pv13,pv17], .c 3,
  .c 5, .c 7, .c 3, .c 29, .c 13, .c 3, .c 17, .c 11, .c 3, .c 19, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv179,pv463], .c 23, .c 3, .c 5, .p pv5 [pv2,pv3,pv193381], .c 3, .c 11, .c 89,
  .c 3, .p pv3 [pv2,pv145037], .c 7, .c 3, .p pv5 [pv2,pv11,pv13,pv4057], .c 5, .c 3,
  .p pv2 [pv2,pv107,pv2711], .c 19, .c 3, .c 5, .p pv2 [pv2,pv3,pv167,pv193], .c 3, .c 929,
  .c 457, .c 3, .c 7, .c 53, .c 3, .c 409, .c 5, .c 3, .c 733, .c 7, .c 3, .c 5, .c 577, .c 3,
  .p pv11 [pv2,pv5,pv23,pv1009], .c 59, .c 3, .c 11, .p pv7 [pv2,pv3,pv193393], .c 3,
  .p pv2 [pv2,pv7,pv82883], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv12893], .c 3, .c 5, .c 29,
  .c 3, .c 653, .c 7, .c 3, .c 19, .c 101, .c 3, .c 13, .c 5, .c 3, .c 127, .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv19,pv29], .c 3, .c 7, .p pv5 [pv2,pv3,pv11,pv59,pv149], .c 3, .c 683,
  .c 13, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv290107], .c 37, .c 3, .c 5, .c 17, .c 3, .c 43,
  .p pv2 [pv2,pv3,pv23,pv2803], .c 3, .p pv5 [pv2,pv7,pv82889], .p pv23 [pv2,pv3,pv1511],
]
private theorem h0141c20 : checkBlock 1160195 128 b0141c20 = true := by
  decide +kernel

private def b0141c21 : List Row := [
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv13,pv44633], .c 991, .c 3, .c 5, .c 7, .c 3, .c 13,
  .p pv5 [pv2,pv3,pv48353], .c 3, .c 47, .p pv11 [pv2,pv3,pv11,pv5861], .c 3, .c 167, .c 5, .c 3,
  .c 11, .p pv2 [pv2,pv3,pv5,pv101,pv383], .c 3, .c 5, .c 13, .c 3, .c 19,
  .p pv3 [pv2,pv3,pv7,pv27631], .c 3, .c 67, .c 7, .c 3, .p pv3 [pv2,pv18133], .c 5, .c 3,
  .p pv17 [pv2,pv580259], .c 487, .c 3, .c 5, .c 43, .c 3, .c 601, .c 11, .c 3, .c 7, .c 17, .c 3,
  .p pv5 [pv2,pv37,pv15683], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 23, .c 3, .c 149, .c 1039,
  .c 3, .p pv5 [pv2,pv11,pv71,pv743], .p pv13 [pv2,pv3,pv199], .c 3, .c 17, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv23,pv29], .c 3, .c 5, .c 41, .c 3, .c 101, .c 7, .c 3,
  .p pv2 [pv2,pv19,pv15271], .c 11, .c 3, .c 23, .c 5, .c 3, .c 29,
  .p pv3 [pv2,pv3,pv5,pv11,pv3517], .c 3, .c 5, .c 479, .c 3, .c 7, .c 113, .c 3, .c 13, .c 107,
  .c 3, .c 709, .c 5, .c 3, .p pv7 [pv2,pv29,pv20011], .c 17, .c 3, .c 5, .c 53, .c 3, .c 227,
  .c 13, .c 3, .c 173, .p pv2 [pv2,pv3,pv17,pv3793], .c 3, .c 7, .c 5, .c 3, .c 41, .c 31, .c 3,
  .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv29017], .c 431, .c 3, .c 11, .p pv7 [pv2,pv3,pv24181], .c 3,
  .c 271, .c 5, .c 3, .c 43, .c 157, .c 3, .c 5,
]
private theorem h0141c21 : checkBlock 1160451 128 b0141c21 = true := by
  decide +kernel

private def b0141c22 : List Row := [
  .c 59, .c 3, .c 211, .p pv5 [pv2,pv3,pv7,pv47], .c 3, .p pv2 [pv2,pv439,pv661], .c 7, .c 3,
  .c 163, .c 5, .c 3, .c 19, .c 11, .c 3, .c 5, .c 151, .c 3, .c 23, .c 17, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv19,pv1697], .c 3, .c 11, .c 5, .c 3, .c 47, .c 7, .c 3, .c 5, .c 19, .c 3,
  .p pv2 [pv2,pv5,pv13,pv8929], .c 73, .c 3, .c 17, .c 71, .c 3, .c 13, .c 5, .c 3, .c 7, .c 131,
  .c 3, .c 5, .c 11, .c 3, .c 37, .c 7, .c 3, .p pv5 [pv2,pv47,pv53,pv233], .c 13, .c 3,
  .p pv2 [pv2,pv29,pv10007], .c 5, .c 3, .c 11, .c 367, .c 3, .c 5, .c 89, .c 3, .c 7, .c 23,
  .c 3, .p pv2 [pv2,pv290209], .p pv3 [pv2,pv3,pv7,pv37,pv83], .c 3, .c 19, .c 5, .c 3, .c 113,
  .c 641, .c 3, .c 5, .c 31, .c 3, .c 13, .c 11, .c 3, .p pv5 [pv2,pv7,pv283,pv293], .c 257, .c 3,
  .c 7, .c 5, .c 3, .c 17, .c 19, .c 3, .c 5, .c 7, .c 3, .c 61, .p pv2 [pv2,pv3,pv3583], .c 3,
  .c 241, .c 29, .c 3, .p pv5 [pv2,pv23,pv25237], .c 5, .c 3, .c 67, .p pv3 [pv2,pv3,pv5,pv12899],
  .c 3, .c 5, .c 313, .c 3, .c 71, .c 983, .c 3, .p pv5 [pv2,pv13,pv44651], .c 7, .c 3, .c 853,
  .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv11,pv1759], .c 3, .c 5, .c 17, .c 3, .c 11,
  .p pv5 [pv2,pv3,pv13,pv61], .c 3, .c 7, .c 109, .c 3,
]
private theorem h0141c22 : checkBlock 1160707 128 b0141c22 = true := by
  decide +kernel

private def b0141c23 : List Row := [
  .c 311, .c 5, .c 3, .c 739, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv19,pv67], .c 3, .c 17,
  .p pv3 [pv2,pv3,pv64499], .c 3, .p pv2 [pv2,pv29,pv37,pv541], .p pv13 [pv2,pv3,pv96749], .c 3,
  .c 97, .c 5, .c 3, .c 7, .p pv37 [pv2,pv3,pv5,pv43], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv11,pv359], .c 3, .p pv13 [pv2,pv5,pv116101], .c 7, .c 3, .c 11, .c 727,
  .c 3, .c 37, .c 5, .c 3, .c 509, .p pv3 [pv2,pv3,pv5,pv13,pv229], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv32251], .c 3, .c 7, .c 13, .c 3, .p pv5 [pv2,pv751,pv773], .c 17, .c 3,
  .c 131, .c 5, .c 3, .p pv2 [pv2,pv580529], .c 11, .c 3, .c 5, .c 139, .c 3, .c 19, .c 29, .c 3,
  .p pv2 [pv2,pv7,pv41467], .c 41, .c 3, .c 7, .c 5, .c 3, .c 191,
  .p pv19 [pv2,pv3,pv5,pv7,pv19,pv97], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv17,pv683],
  .c 443, .c 3, .p pv2 [pv2,pv580553], .c 19, .c 3, .p pv3 [pv2,pv145139], .c 5, .c 3, .c 103,
  .c 13, .c 3, .c 5, .c 11, .c 3, .c 29, .c 211, .c 3, .p pv3 [pv2,pv31,pv2341], .c 7, .c 3,
  .p pv5 [pv2,pv79,pv7349], .c 5, .c 3, .c 11, .c 17, .c 3, .c 5, .c 149, .c 3, .c 41,
  .p pv2 [pv2,pv3,pv21503], .c 3, .c 7, .p pv19 [pv2,pv3,pv17,pv1423], .c 3, .c 13, .c 5, .c 3,
  .c 59, .c 7, .c 3, .c 5, .c 97, .c 3, .c 607, .c 11, .c 3, .c 101, .c 13, .c 3,
  .p pv2 [pv2,pv7,pv17,pv41], .c 5, .c 3, .c 7, .c 73, .c 3, .c 5, .p pv13 [pv2,pv3,pv7],
]
private theorem h0141c23 : checkBlock 1160963 128 b0141c23 = true := by
  decide +kernel

private def b0141c24 : List Row := [
  .c 3, .c 79, .c 7, .c 3, .p pv2 [pv2,pv11,pv52783], .c 31, .c 3, .p pv3 [pv2,pv72577], .c 5,
  .c 3, .p pv7 [pv2,pv13,pv59,pv757], .p pv17 [pv2,pv3,pv5,pv9677], .c 3, .c 5, .c 23, .c 3, .c 7,
  .c 17, .c 3, .c 61, .c 11, .c 3, .p pv5 [pv2,pv580631], .c 5, .c 3, .p pv2 [pv2,pv290317],
  .c 107, .c 3, .c 5, .c 13, .c 3, .c 11, .c 53, .c 3, .c 17, .p pv7 [pv2,pv3,pv127], .c 3, .c 7,
  .c 5, .c 3, .c 19, .c 43, .c 3, .c 5, .c 7, .c 3, .c 67, .p pv23 [pv2,pv3,pv12097], .c 3,
  .p pv2 [pv2,pv13,pv23,pv971], .c 37, .c 3, .c 47, .c 5, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv5,pv38711], .c 3, .c 5, .c 19, .c 3, .c 151, .p pv3 [pv2,pv3,pv7,pv13,pv709],
  .c 3, .c 11, .c 7, .c 3, .c 31, .c 5, .c 3, .c 1009, .c 89, .c 3, .c 5, .c 967, .c 3,
  .p pv2 [pv2,pv5,pv7,pv47,pv353], .c 281, .c 3, .c 7, .c 61, .c 3, .c 257, .c 5, .c 3, .c 17,
  .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv32261], .c 3, .p pv3 [pv2,pv5,pv5807],
  .p pv2 [pv2,pv3,pv11,pv17597], .c 3, .c 13, .c 347, .c 3, .c 11, .c 5, .c 3, .c 7, .c 29, .c 3,
  .c 5, .c 503, .c 3, .c 23, .c 7, .c 3, .p pv2 [pv2,pv290359], .p pv3 [pv2,pv3,pv193573], .c 3,
  .p pv2 [pv2,pv53,pv10957], .c 5, .c 3, .p pv3 [pv2,pv41,pv3541], .c 19, .c 3, .c 5, .c 11, .c 3,
  .c 7, .p pv3 [pv2,pv3,pv193577], .c 3, .c 37, .c 563, .c 3, .c 43,
]
private theorem h0141c24 : checkBlock 1161219 128 b0141c24 = true := by
  decide +kernel

private def b0141c25 : List Row := [
  .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv9679], .c 3, .c 5, .p pv13 [pv2,pv3,pv137,pv157], .c 3,
  .c 17, .p pv2 [pv2,pv3,pv151,pv641], .c 3, .p pv3 [pv2,pv7,pv2963],
  .p pv59 [pv2,pv3,pv13,pv14891], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv17,pv19,pv29,pv31], .c 13,
  .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv14519], .c 11, .c 3, .c 19, .p pv7 [pv2,pv3,pv48397],
  .c 3, .c 59, .c 5, .c 3, .c 31, .c 37, .c 3, .c 5, .p pv7 [pv2,pv3,pv19,pv23,pv443], .c 3,
  .p pv19 [pv2,pv5,pv13,pv1787], .p pv11 [pv2,pv3,pv7,pv3457], .c 3, .c 701, .c 7, .c 3, .c 13,
  .c 5, .c 3, .c 23, .c 41, .c 3, .c 5, .c 131, .c 3, .p pv2 [pv2,pv5,pv7,pv8297], .c 523, .c 3,
  .c 7, .c 11, .c 3, .c 17, .c 5, .c 3, .p pv17 [pv2,pv673,pv863], .c 7, .c 3, .c 5, .c 223, .c 3,
  .c 11, .c 109, .c 3, .p pv3 [pv2,pv79,pv919], .p pv2 [pv2,pv3,pv193603], .c 3, .c 61, .c 5,
  .c 3, .c 7, .c 71, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv13829], .c 3, .c 13, .c 7, .c 3,
  .p pv5 [pv2,pv67,pv8669], .c 73, .c 3, .c 29, .c 5, .c 3, .p pv2 [pv2,pv181,pv3209], .c 17,
  .c 3, .c 5, .c 13, .c 3, .c 7, .c 587, .c 3, .c 11, .c 19, .c 3, .p pv2 [pv2,pv29,pv20029],
  .c 5, .c 3, .c 37, .p pv2 [pv2,pv3,pv5,pv38723], .c 3, .c 5, .c 401, .c 3, .c 163,
  .p pv7 [pv2,pv3,pv71,pv101], .c 3, .c 23, .c 197, .c 3, .c 7, .c 5, .c 3, .c 13, .c 11, .c 3,
  .c 5, .c 7, .c 3,
]
private theorem h0141c25 : checkBlock 1161475 128 b0141c25 = true := by
  decide +kernel

private def b0141c26 : List Row := [
  .c 43, .c 601, .c 3, .c 103, .c 433, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv7,pv41491], .c 83,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv31,pv347], .c 3, .p pv3 [pv2,pv5,pv53,pv137], .c 17, .c 3,
  .p pv5 [pv2,pv211,pv2753], .c 7, .c 3, .c 71, .c 5, .c 3, .c 239,
  .p pv7 [pv2,pv3,pv5,pv17,pv67], .c 3, .c 5, .c 11, .c 3, .p pv7 [pv2,pv5,pv7,pv2371], .c 19,
  .c 3, .c 7, .c 23, .c 3, .c 101, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 41, .c 3, .c 349,
  .c 13, .c 3, .c 29, .p pv2 [pv2,pv3,pv59,pv547], .c 3, .p pv3 [pv2,pv7,pv20747], .c 5, .c 3,
  .c 7, .p pv13 [pv2,pv3,pv5,pv47,pv103], .c 3, .c 5, .c 67, .c 3, .p pv2 [pv2,pv5,pv19,pv1223],
  .c 7, .c 3, .p pv3 [pv2,pv29,pv313], .c 1063, .c 3, .c 619, .c 5, .c 3, .c 19,
  .p pv17 [pv2,pv3,pv5,pv38729], .c 3, .c 5, .p pv2 [pv2,pv3,pv96823], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv17,pv3797], .c 3, .c 47, .c 179, .c 3, .p pv2 [pv2,pv290473], .c 5, .c 3,
  .c 17, .c 13, .c 3, .c 5, .c 19, .c 3, .c 31, .c 107, .c 3, .c 83, .c 11, .c 3, .c 7, .c 5,
  .c 3, .p pv3 [pv2,pv61,pv2381], .p pv2 [pv2,pv3,pv5,pv7,pv11,pv503], .c 3, .c 5, .c 7, .c 3,
  .c 11, .c 29, .c 3, .p pv2 [pv2,pv43,pv59,pv229], .p pv2 [pv2,pv3,pv37,pv2617], .c 3, .c 13,
  .c 5, .c 3, .c 769, .c 199, .c 3, .c 5, .c 17, .c 3, .c 233, .c 31, .c 3, .c 211, .c 7, .c 3,
  .c 19, .c 5,
]
private theorem h0141c26 : checkBlock 1161731 128 b0141c26 = true := by
  decide +kernel

private def b0141c27 : List Row := [
  .c 3, .c 43, .p pv23 [pv2,pv3,pv5,pv12911], .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv8803], .c 3,
  .c 17, .c 1069, .c 3, .c 7, .p pv11 [pv2,pv3,pv16139], .c 3, .c 227, .c 5, .c 3, .c 397, .c 7,
  .c 3, .c 5, .c 163, .c 3, .c 13, .c 439, .c 3, .p pv2 [pv2,pv290509], .c 881, .c 3,
  .p pv5 [pv2,pv7,pv83003], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 13, .c 3,
  .p pv2 [pv2,pv5,pv97,pv599], .c 7, .c 3, .p pv2 [pv2,pv31,pv18743], .c 17, .c 3, .c 11, .c 5,
  .c 3, .p pv7 [pv2,pv19,pv53,pv577], .p pv11 [pv2,pv3,pv5,pv269], .c 3, .c 5, .c 73, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv113,pv857], .c 3, .c 19, .p pv7 [pv2,pv3,pv7,pv23,pv401], .c 3, .c 17, .c 5,
  .c 3, .c 13, .c 61, .c 3, .c 5, .c 11, .c 3, .c 23, .c 59, .c 3, .c 107,
  .p pv7 [pv2,pv3,pv11,pv31,pv71], .c 3, .c 7, .c 5, .c 3, .c 11, .c 331, .c 3, .c 5, .c 7, .c 3,
  .c 457, .c 167, .c 3, .c 97, .c 31, .c 3, .c 811, .c 5, .c 3, .c 47, .c 17, .c 3, .c 5, .c 127,
  .c 3, .c 461, .c 11, .c 3, .c 13, .c 7, .c 3, .p pv5 [pv2,pv19,pv3823], .c 5, .c 3, .c 71,
  .c 181, .c 3, .c 5, .c 37, .c 3, .c 19, .c 13, .c 3, .c 7, .p pv3 [pv2,pv3,pv193703], .c 3,
  .p pv5 [pv2,pv17,pv34183], .c 5, .c 3, .p pv2 [pv2,pv290557], .c 7, .c 3, .c 5, .c 53, .c 3,
  .c 59,
]
private theorem h0141c27 : checkBlock 1161987 128 b0141c27 = true := by
  decide +kernel

private def b0141c28 : List Row := [
  .p pv3 [pv2,pv3,pv21523], .c 3, .c 43, .c 11, .c 3, .p pv2 [pv2,pv7,pv13,pv31,pv103], .c 5,
  .c 3, .c 7, .p pv37 [pv2,pv3,pv5,pv11,pv587], .c 3, .c 5, .c 109, .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv223,pv1303], .p pv79 [pv2,pv3,pv13,pv4967], .c 3, .c 31, .c 5, .c 3, .c 367,
  .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv5381], .c 3, .c 7, .p pv3 [pv2,pv3,pv307,pv631], .c 3,
  .c 17, .c 41, .c 3, .c 337, .c 5, .c 3, .c 271, .p pv7 [pv2,pv3,pv5,pv29,pv167], .c 3, .c 5,
  .c 79, .c 3, .c 293, .c 43, .c 3, .c 11, .p pv3 [pv2,pv3,pv193723], .c 3, .c 7, .c 5, .c 3,
  .c 29, .c 23, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv29059], .c 19, .c 3,
  .p pv5 [pv2,pv581183], .c 13, .c 3, .p pv2 [pv2,pv290593], .c 5, .c 3, .c 73, .c 11, .c 3, .c 5,
  .c 173, .c 3, .c 41, .c 379, .c 3, .c 23, .c 7, .c 3, .c 11, .c 5, .c 3, .c 17, .c 257, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv61,pv397], .c 3, .c 13, .p pv3 [pv2,pv3,pv64579], .c 3, .c 7, .c 37,
  .c 3, .c 503, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 11, .c 3, .c 47,
  .p pv2 [pv2,pv3,pv73,pv1327], .c 3, .c 139, .c 557, .c 3, .p pv5 [pv2,pv7,pv43,pv1931], .c 5,
  .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv38749], .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv11,pv1321],
  .c 7, .c 3, .c 167, .c 23, .c 3, .p pv2 [pv2,pv290623], .c 5, .c 3,
]
private theorem h0141c28 : checkBlock 1162243 128 b0141c28 = true := by
  decide +kernel

private def b0141c29 : List Row := [
  .c 13, .p pv2 [pv2,pv3,pv5,pv31], .c 3, .c 5, .p pv2 [pv2,pv3,pv193751], .c 3, .c 7, .c 11,
  .c 3, .c 67, .c 349, .c 3, .c 29, .c 5, .c 3, .p pv3 [pv2,pv17,pv2137], .c 31, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv59,pv821], .c 3, .p pv2 [pv2,pv5,pv37,pv1571], .p pv3 [pv2,pv3,pv193757],
  .c 3, .p pv2 [pv2,pv7,pv11,pv7549], .c 151, .c 3, .c 7, .c 5, .c 3,
  .p pv13 [pv2,pv23,pv127,pv199], .c 103, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv116257],
  .p pv2 [pv2,pv3,pv19,pv5099], .c 3, .c 13, .c 11, .c 3, .p pv5 [pv2,pv137,pv4243], .c 5, .c 3,
  .p pv3 [pv2,pv7,pv41521], .c 19, .c 3, .c 5, .p pv11 [pv2,pv3,pv17,pv41,pv139], .c 3, .c 11,
  .c 13, .c 3, .c 89, .c 7, .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv269,pv2161],
  .p pv7 [pv2,pv3,pv5,pv2153], .c 3, .c 5, .c 23, .c 3, .p pv23 [pv2,pv5,pv7,pv17,pv977], .c 229,
  .c 3, .c 7, .c 29, .c 3, .c 79, .c 5, .c 3, .p pv3 [pv2,pv19,pv7649], .c 7, .c 3, .c 5, .c 113,
  .c 3, .c 53, .p pv3 [pv2,pv3,pv107,pv1811], .c 3, .c 11, .p pv2 [pv2,pv3,pv13,pv29,pv257], .c 3,
  .c 23, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv19,pv31,pv47], .c 3,
  .p pv2 [pv2,pv5,pv116269], .c 7, .c 3, .c 29, .c 661, .c 3, .c 109, .c 5, .c 3,
  .p pv2 [pv2,pv290677], .c 11, .c 3, .c 5, .c 31, .c 3, .c 7, .c 263, .c 3,
  .p pv5 [pv2,pv29,pv20047], .p pv11 [pv2,pv3,pv7,pv769], .c 3, .c 11, .c 5, .c 3, .c 97,
  .p pv2 [pv2,pv3,pv5,pv19379], .c 3, .c 5, .c 83, .c 3, .p pv7 [pv2,pv5,pv4651],
  .p pv5 [pv2,pv3,pv757],
]
private theorem h0141c29 : checkBlock 1162499 128 b0141c29 = true := by
  decide +kernel

private def b0141c30 : List Row := [
  .c 3, .c 199, .c 13, .c 3, .c 7, .c 5, .c 3, .c 107, .p pv7 [pv2,pv3,pv5,pv7,pv113], .c 3, .c 5,
  .c 7, .c 3, .c 19, .c 17, .c 3, .c 409, .p pv7 [pv2,pv3,pv11,pv23,pv383], .c 3,
  .p pv3 [pv2,pv145349], .c 5, .c 3, .c 11, .c 41, .c 3, .c 5, .p pv5 [pv2,pv3,pv43,pv4507], .c 3,
  .c 13, .c 29, .c 3, .c 17, .c 7, .c 3, .c 797, .c 5, .c 3, .c 311, .c 59, .c 3, .c 5, .c 13,
  .c 3, .c 31, .c 11, .c 3, .c 7, .c 43, .c 3, .p pv2 [pv2,pv67,pv4339], .c 5, .c 3,
  .p pv2 [pv2,pv581429], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv193811], .c 3, .c 29, .c 37, .c 3,
  .p pv2 [pv2,pv11,pv13,pv19,pv107], .p pv7 [pv2,pv3,pv193813], .c 3, .c 41, .c 5, .c 3, .c 7,
  .c 197, .c 3, .c 5, .p pv11 [pv2,pv3,pv7,pv3461], .c 3, .p pv3 [pv2,pv5,pv29,pv401], .c 7, .c 3,
  .p pv2 [pv2,pv173,pv3361], .c 11, .c 3, .c 83, .c 5, .c 3, .c 17, .c 47, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv23,pv53], .c 3, .c 7, .c 19, .c 3, .p pv3 [pv2,pv17,pv503], .c 127, .c 3,
  .p pv5 [pv2,pv11,pv52861], .c 5, .c 3, .c 23, .p pv107 [pv2,pv3,pv5,pv7753], .c 3, .c 5,
  .p pv7 [pv2,pv3,pv199,pv487], .c 3, .p pv13 [pv2,pv5,pv14537], .c 73, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv47,pv1031], .c 3, .c 7, .c 5, .c 3, .c 53, .p pv2 [pv2,pv3,pv5,pv7,pv13,pv71],
  .c 3, .c 5, .c 7, .c 3, .p pv11 [pv2,pv5,pv19,pv6121], .c 13, .c 3, .c 11, .c 191, .c 3,
  .p pv2 [pv2,pv151,pv3851], .c 5, .c 3, .c 19,
]
private theorem h0141c30 : checkBlock 1162755 128 b0141c30 = true := by
  decide +kernel

private def b0141c31 : List Row := [
  .p pv2 [pv2,pv3,pv5,pv38767], .c 3, .c 5, .p pv41 [pv2,pv3,pv29,pv557], .c 3, .c 17, .c 367,
  .c 3, .c 31, .c 7, .c 3, .p pv3 [pv2,pv13,pv53,pv211], .c 5, .c 3,
  .p pv11 [pv2,pv17,pv79,pv433], .c 11, .c 3, .c 5, .c 19, .c 3, .c 71, .c 67, .c 3, .c 7, .c 281,
  .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv290767], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv103,pv941],
  .c 3, .p pv3 [pv2,pv5,pv29077], .p pv2 [pv2,pv3,pv193847], .c 3, .c 23, .c 17, .c 3,
  .p pv3 [pv2,pv7,pv41539], .c 5, .c 3, .c 7, .c 619, .c 3, .c 5, .c 11, .c 3,
  .p pv11 [pv2,pv5,pv13,pv23,pv389], .c 7, .c 3, .c 79, .p pv3 [pv2,pv3,pv11,pv17623], .c 3,
  .c 13, .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv137,pv283], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv233], .c 3, .c 7, .p pv3 [pv2,pv3,pv19,pv179], .c 3,
  .p pv2 [pv2,pv581573], .c 13, .c 3, .c 151, .c 5, .c 3, .p pv7 [pv2,pv563,pv1033], .c 19, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv193861], .c 3, .c 383, .c 11, .c 3, .p pv3 [pv2,pv7,pv20771], .c 23,
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv13,pv22369], .c 17, .c 3, .c 5, .c 7, .c 3, .c 13, .c 47,
  .c 3, .p pv11 [pv2,pv11,pv37,pv1429], .c 61, .c 3, .c 31, .c 5, .c 3, .c 29,
  .p pv2 [pv2,pv3,pv5,pv19387], .c 3, .c 5, .c 13, .c 3, .p pv11 [pv2,pv5,pv89,pv1307],
  .p pv5 [pv2,pv3,pv7,pv577], .c 3, .c 19, .c 7, .c 3, .c 37, .c 5, .c 3, .c 263,
  .p pv47 [pv2,pv3,pv5,pv11,pv47], .c 3, .c 5, .p pv37 [pv2,pv3,pv19,pv2551], .c 3, .c 11,
  .p pv3 [pv2,pv3,pv193877], .c 3,
]
private theorem h0141c31 : checkBlock 1163011 128 b0141c31 = true := by
  decide +kernel

def rows0141 : List Row :=
  b0141c00 ++ b0141c01 ++ b0141c02 ++ b0141c03 ++ b0141c04 ++ b0141c05 ++ b0141c06 ++ b0141c07 ++
  b0141c08 ++ b0141c09 ++ b0141c10 ++ b0141c11 ++ b0141c12 ++ b0141c13 ++ b0141c14 ++ b0141c15 ++
  b0141c16 ++ b0141c17 ++ b0141c18 ++ b0141c19 ++ b0141c20 ++ b0141c21 ++ b0141c22 ++ b0141c23 ++
  b0141c24 ++ b0141c25 ++ b0141c26 ++ b0141c27 ++ b0141c28 ++ b0141c29 ++ b0141c30 ++ b0141c31

theorem checked0141 : checkBlock 1155075 4096 rows0141 = true :=
  checkBlock_append h0141c00 (
    checkBlock_append h0141c01 (
    checkBlock_append h0141c02 (
    checkBlock_append h0141c03 (
    checkBlock_append h0141c04 (
    checkBlock_append h0141c05 (
    checkBlock_append h0141c06 (
    checkBlock_append h0141c07 (
    checkBlock_append h0141c08 (
    checkBlock_append h0141c09 (
    checkBlock_append h0141c10 (
    checkBlock_append h0141c11 (
    checkBlock_append h0141c12 (
    checkBlock_append h0141c13 (
    checkBlock_append h0141c14 (
    checkBlock_append h0141c15 (
    checkBlock_append h0141c16 (
    checkBlock_append h0141c17 (
    checkBlock_append h0141c18 (
    checkBlock_append h0141c19 (
    checkBlock_append h0141c20 (
    checkBlock_append h0141c21 (
    checkBlock_append h0141c22 (
    checkBlock_append h0141c23 (
    checkBlock_append h0141c24 (
    checkBlock_append h0141c25 (
    checkBlock_append h0141c26 (
    checkBlock_append h0141c27 (
    checkBlock_append h0141c28 (
    checkBlock_append h0141c29 (
    checkBlock_append h0141c30 (
    h0141c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
