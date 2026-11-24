/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0136
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0136.checked0136
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table116

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0136c00 : List Row := [
  .c 5, .p pv2 [pv2,pv3,pv227,pv409], .c 3, .c 419, .c 859, .c 3, .c 7, .c 17, .c 3, .c 863, .c 5,
  .c 3, .c 13, .c 7, .c 3, .c 5, .c 383, .c 3, .c 29, .c 911, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv185693], .c 3, .c 17, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5, .c 563, .c 3,
  .c 37, .c 7, .c 3, .c 577, .c 23, .c 3, .p pv3 [pv2,pv83,pv839], .c 5, .c 3, .c 73, .c 11, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv233,pv797], .c 3, .c 7, .p pv2 [pv2,pv3,pv11,pv23,pv367], .c 3, .c 13,
  .c 53, .c 3, .c 11, .c 5, .c 3, .c 47, .c 17, .c 3, .c 5, .c 461, .c 3, .p pv3 [pv2,pv5,pv1741],
  .c 13, .c 3, .c 593, .p pv7 [pv2,pv3,pv17,pv2731], .c 3, .c 7, .c 5, .c 3, .c 43,
  .p pv2 [pv2,pv3,pv5,pv7,pv379], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv111427],
  .p pv5 [pv2,pv3,pv53,pv73], .c 3, .c 67, .c 293, .c 3, .p pv2 [pv2,pv13,pv17,pv2521], .c 5,
  .c 3, .c 11, .c 211, .c 3, .c 5, .p pv5 [pv2,pv3,pv29,pv1601], .c 3,
  .p pv7 [pv2,pv5,pv11,pv1013], .p pv7 [pv2,pv3,pv7,pv43,pv617], .c 3, .c 109, .c 7, .c 3, .c 311,
  .c 5, .c 3, .c 643, .c 13, .c 3, .c 5, .c 23, .c 3, .c 19, .c 11, .c 3, .c 7, .c 41, .c 3,
  .c 227, .c 5, .c 3, .p pv2 [pv2,pv61,pv4567], .c 7, .c 3, .c 5, .c 31, .c 3,
  .p pv17 [pv2,pv5,pv13,pv2143], .c 139, .c 3, .c 17, .c 19,
]
private theorem h0136c00 : checkBlock 1114115 128 b0136c00 = true := by
  decide +kernel

private def b0136c01 : List Row := [
  .c 3, .c 13, .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv41,pv151], .c 3, .c 5, .c 421, .c 3,
  .c 167, .c 7, .c 3, .p pv3 [pv2,pv23,pv12113], .c 11, .c 3, .c 37, .c 5, .c 3, .c 61, .c 67,
  .c 3, .c 5, .c 47, .c 3, .c 7, .p pv3 [pv2,pv3,pv185737], .c 3, .p pv2 [pv2,pv19,pv29327],
  .c 197, .c 3, .c 97, .c 5, .c 3, .c 233, .c 29, .c 3, .c 5, .p pv11 [pv2,pv3,pv281,pv661], .c 3,
  .c 13, .c 79, .c 3, .c 239, .c 337, .c 3, .c 7, .c 5, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv5,pv7,pv29,pv61], .c 3, .c 5, .c 7, .c 3, .c 31, .c 19, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv23,pv673], .c 3, .p pv2 [pv2,pv278623], .c 5, .c 3, .c 29,
  .p pv7 [pv2,pv3,pv5,pv743], .c 3, .c 5, .p pv3 [pv2,pv3,pv20639], .c 3, .c 23, .c 523, .c 3,
  .c 43, .c 7, .c 3, .p pv2 [pv2,pv557261], .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 17, .c 3,
  .p pv3 [pv2,pv5,pv7,pv19,pv419], .c 31, .c 3, .c 7, .p pv13 [pv2,pv3,pv131,pv709], .c 3, .c 11,
  .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv431], .c 3, .c 17,
  .p pv2 [pv2,pv3,pv293,pv317], .c 3, .p pv3 [pv2,pv69661], .c 367, .c 3, .c 691, .c 5, .c 3,
  .c 7, .p pv7 [pv2,pv3,pv5,pv53,pv701], .c 3, .c 5, .c 11, .c 3, .p pv7 [pv2,pv5,pv5573], .c 7,
  .c 3, .c 13, .c 257, .c 3, .p pv2 [pv2,pv67,pv4159], .c 5, .c 3, .c 11, .c 439, .c 3, .c 5,
]
private theorem h0136c01 : checkBlock 1114371 128 b0136c01 = true := by
  decide +kernel

private def b0136c02 : List Row := [
  .c 97, .c 3, .c 7, .c 13, .c 3, .c 73, .c 17, .c 3, .c 53, .c 5, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv5,pv2477], .c 3, .c 5, .p pv13 [pv2,pv3,pv17,pv683], .c 3,
  .p pv2 [pv2,pv5,pv55733], .c 11, .c 3, .c 31, .c 149, .c 3, .c 7, .c 5, .c 3, .c 67,
  .p pv29 [pv2,pv3,pv5,pv7,pv1327], .c 3, .c 5, .c 7, .c 3, .c 251, .p pv2 [pv2,pv3,pv19,pv4889],
  .c 3, .p pv5 [pv2,pv11,pv53,pv239], .c 37, .c 3, .c 907, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv41,pv971], .c 13, .c 3, .c 5, .c 307, .c 3, .p pv3 [pv2,pv5,pv6967],
  .p pv3 [pv2,pv3,pv7,pv983], .c 3, .c 281, .c 7, .c 3, .p pv2 [pv2,pv43,pv6481], .c 5, .c 3,
  .c 599, .c 17, .c 3, .c 5, .c 919, .c 3, .c 11, .p pv7 [pv2,pv3,pv2903], .c 3, .c 7,
  .p pv3 [pv2,pv3,pv17,pv3643], .c 3, .c 13, .c 5, .c 3, .c 79, .c 7, .c 3, .c 5, .c 223, .c 3,
  .c 647, .c 73, .c 3, .c 19, .c 13, .c 3, .c 47, .c 5, .c 3, .c 7, .p pv23 [pv2,pv3,pv5,pv929],
  .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv11,pv19,pv127], .c 3, .p pv2 [pv2,pv5,pv23,pv37,pv131], .c 7,
  .c 3, .c 11, .c 619, .c 3, .c 197, .c 5, .c 3, .p pv2 [pv2,pv11,pv13,pv1949], .c 41, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv61,pv1523], .c 3, .c 7, .c 17, .c 3, .c 29, .p pv11 [pv2,pv3,pv7,pv79], .c 3,
  .c 31, .c 5, .c 3, .p pv2 [pv2,pv113,pv4933], .c 11, .c 3, .c 5, .c 13, .c 3, .c 853,
  .p pv19 [pv2,pv3,pv11,pv41,pv103], .c 3, .c 17, .c 23, .c 3,
]
private theorem h0136c02 : checkBlock 1114627 128 b0136c02 = true := by
  decide +kernel

private def b0136c03 : List Row := [
  .c 7, .c 5, .c 3, .c 317, .p pv13 [pv2,pv3,pv5,pv7,pv5309], .c 3, .c 5, .c 7, .c 3, .c 19,
  .c 89, .c 3, .p pv2 [pv2,pv13,pv137,pv313], .p pv2 [pv2,pv3,pv53,pv1753], .c 3, .c 41, .c 5,
  .c 3, .c 13, .c 37, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv111493], .c 127, .c 3,
  .p pv3 [pv2,pv139367], .c 7, .c 3, .p pv5 [pv2,pv251,pv2221], .c 5, .c 3, .c 11, .c 967, .c 3,
  .c 5, .c 857, .c 3, .c 53, .c 29, .c 3, .c 7, .p pv23 [pv2,pv3,pv46457], .c 3,
  .p pv2 [pv2,pv278743], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv185831], .c 3,
  .c 179, .c 11, .c 3, .c 13, .p pv3 [pv2,pv3,pv185833], .c 3, .c 797, .c 5, .c 3, .c 7,
  .p pv29 [pv2,pv3,pv5,pv13,pv953], .c 3, .c 5, .c 23, .c 3, .c 29, .c 7, .c 3,
  .p pv2 [pv2,pv11,pv50683], .p pv2 [pv2,pv3,pv47,pv659], .c 3, .c 43, .c 5, .c 3, .c 31, .c 59,
  .c 3, .c 5, .c 17, .c 3, .c 7, .c 19, .c 3, .p pv3 [pv2,pv69691], .c 11, .c 3, .c 23, .c 5,
  .c 3, .c 37, .p pv11 [pv2,pv3,pv5,pv11,pv31,pv109], .c 3, .c 5, .c 41, .c 3, .c 11, .c 163,
  .c 3, .c 1049, .p pv7 [pv2,pv3,pv13,pv1787], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv17,pv32797],
  .c 13, .c 3, .c 5, .c 7, .c 3, .c 1051, .p pv5 [pv2,pv3,pv97,pv479], .c 3,
  .p pv2 [pv2,pv149,pv1871], .c 43, .c 3, .c 257, .c 5, .c 3, .c 19, .p pv2 [pv2,pv3,pv5,pv37171],
  .c 3, .c 5, .c 29,
]
private theorem h0136c03 : checkBlock 1114883 128 b0136c03 = true := by
  decide +kernel

private def b0136c04 : List Row := [
  .c 3, .c 61, .c 37, .c 3, .c 11, .c 7, .c 3, .c 13, .c 5, .c 3, .c 41, .c 673, .c 3, .c 5,
  .c 19, .c 3, .c 157, .c 53, .c 3, .c 7, .c 13, .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv83,pv3359], .c 7, .c 3, .c 5, .c 71, .c 3, .c 23, .c 131, .c 3,
  .p pv5 [pv2,pv317,pv1759], .c 97, .c 3, .c 11, .c 5, .c 3, .c 7, .c 73, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv53,pv167], .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv278809],
  .p pv11 [pv2,pv3,pv185873], .c 3, .c 19, .c 5, .c 3, .c 191, .c 17, .c 3, .c 5, .c 11, .c 3,
  .c 7, .c 47, .c 3, .p pv2 [pv2,pv557633], .p pv2 [pv2,pv3,pv7,pv11,pv17,pv71], .c 3,
  .p pv3 [pv2,pv139409], .c 5, .c 3, .c 11, .c 19, .c 3, .c 5, .c 31, .c 3, .c 37, .c 23, .c 3,
  .p pv3 [pv2,pv7,pv13,pv383], .p pv3 [pv2,pv3,pv61961], .c 3, .c 7, .c 5, .c 3, .c 13, .c 29,
  .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv27883], .c 11, .c 3, .p pv5 [pv2,pv557663],
  .p pv7 [pv2,pv3,pv37,pv157], .c 3, .c 547, .c 5, .c 3, .c 23, .c 577, .c 3, .c 5, .c 193, .c 3,
  .p pv23 [pv2,pv5,pv22307], .c 17, .c 3, .c 19, .c 7, .c 3, .p pv2 [pv2,pv23,pv24247], .c 5,
  .c 3, .c 29, .c 233, .c 3, .c 5, .c 43, .c 3, .p pv2 [pv2,pv5,pv7,pv31,pv257], .c 263, .c 3,
  .c 7, .c 11, .c 3, .c 167,
]
private theorem h0136c04 : checkBlock 1115139 128 b0136c04 = true := by
  decide +kernel

private def b0136c05 : List Row := [
  .c 5, .c 3, .p pv17 [pv2,pv29,pv19231], .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv61967], .c 3, .c 11,
  .c 13, .c 3, .p pv3 [pv2,pv67,pv2081], .p pv2 [pv2,pv3,pv185903], .c 3, .c 113, .c 5, .c 3,
  .c 7, .c 23, .c 3, .c 5, .c 83, .c 3, .c 127, .c 7, .c 3, .p pv5 [pv2,pv41,pv61,pv223],
  .p pv7 [pv2,pv3,pv46477], .c 3, .p pv2 [pv2,pv13,pv19,pv1129], .c 5, .c 3, .c 229, .c 521, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv11,pv16901], .c 3, .c 7, .c 31, .c 3, .c 11, .c 277, .c 3, .c 67, .c 5,
  .c 3, .c 17, .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv15493], .c 3, .p pv2 [pv2,pv5,pv23,pv97],
  .c 181, .c 3, .c 61, .c 19, .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv557759], .c 11, .c 3, .c 5,
  .c 7, .c 3, .p pv7 [pv2,pv5,pv13,pv8581], .p pv2 [pv2,pv3,pv11,pv313], .c 3, .c 457,
  .p pv2 [pv2,pv3,pv185923], .c 3, .c 11, .c 5, .c 3, .c 43, .p pv17 [pv2,pv3,pv5,pv37,pv67],
  .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv167], .c 149, .c 3, .p pv5 [pv2,pv19,pv31,pv947],
  .c 7, .c 3, .p pv3 [pv2,pv29,pv59,pv163], .c 5, .c 3, .p pv2 [pv2,pv557789],
  .p pv2 [pv2,pv3,pv5,pv18593], .c 3, .c 5, .c 11, .c 3, .c 17, .c 103, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv11,pv16903], .c 3, .c 83, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 67, .c 3,
  .c 13, .c 19, .c 3, .p pv2 [pv2,pv733,pv761], .c 61, .c 3, .p pv5 [pv2,pv7,pv1423], .c 5, .c 3,
  .c 7, .p pv11 [pv2,pv3,pv5,pv1033], .c 3, .c 5, .c 13, .c 3,
]
private theorem h0136c05 : checkBlock 1115395 128 b0136c05 = true := by
  decide +kernel

private def b0136c06 : List Row := [
  .c 41, .c 7, .c 3, .p pv3 [pv2,pv139457], .c 17, .c 3, .c 467, .c 5, .c 3, .c 223, .c 557, .c 3,
  .c 5, .c 173, .c 3, .c 7, .p pv2 [pv2,pv3,pv185947], .c 3, .c 659, .c 107, .c 3, .c 17, .c 5,
  .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv3719], .c 3, .c 5, .c 23, .c 3, .p pv7 [pv2,pv5,pv17,pv6563],
  .p pv5 [pv2,pv3,pv13,pv149], .c 3, .c 29, .c 11, .c 3, .c 7, .c 5, .c 3, .c 929,
  .p pv2 [pv2,pv3,pv5,pv7,pv11,pv23], .c 3, .c 5, .c 7, .c 3, .c 11, .p pv3 [pv2,pv3,pv185957],
  .c 3, .c 101, .c 59, .c 3, .c 23, .c 5, .c 3, .p pv7 [pv2,pv7,pv79697], .c 17, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv61987], .c 3, .p pv2 [pv2,pv5,pv111577], .p pv2 [pv2,pv3,pv7,pv37,pv359],
  .c 3, .c 13, .c 7, .c 3, .c 31, .c 5, .c 3, .p pv2 [pv2,pv278947], .c 97, .c 3, .c 5, .c 419,
  .c 3, .c 331, .c 13, .c 3, .c 7, .c 37, .c 3, .c 19, .c 5, .c 3, .c 769, .c 7, .c 3, .c 5,
  .c 47, .c 3, .p pv13 [pv2,pv5,pv241,pv463], .c 29, .c 3, .c 233, .p pv17 [pv2,pv3,pv61991],
  .c 3, .p pv2 [pv2,pv7,pv13,pv6131], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv41], .c 3, .c 149, .c 7, .c 3, .c 59, .c 283, .c 3, .c 11, .c 5, .c 3,
  .p pv7 [pv2,pv73,pv7643], .c 13, .c 3, .c 5, .c 587, .c 3, .c 7, .c 43, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv7,pv163], .c 3, .c 107, .c 5,
]
private theorem h0136c06 : checkBlock 1115651 128 b0136c06 = true := by
  decide +kernel

private def b0136c07 : List Row := [
  .c 3, .c 263, .p pv47 [pv2,pv3,pv5,pv4133], .c 3, .c 5, .c 11, .c 3, .c 47,
  .p pv2 [pv2,pv3,pv185987], .c 3, .c 19, .p pv19 [pv2,pv3,pv11,pv1409], .c 3, .c 7, .c 5, .c 3,
  .c 11, .p pv2 [pv2,pv3,pv5,pv7,pv2657], .c 3, .c 5, .c 7, .c 3, .c 73, .c 1021, .c 3, .c 37,
  .c 13, .c 3, .c 953, .c 5, .c 3, .c 31, .c 89, .c 3, .c 5, .c 653, .c 3, .c 641, .c 11, .c 3,
  .p pv2 [pv2,pv743,pv751], .c 7, .c 3, .p pv3 [pv2,pv199,pv701], .c 5, .c 3, .c 17,
  .p pv7 [pv2,pv3,pv5,pv31], .c 3, .c 5, .c 29, .c 3, .c 13, .c 191, .c 3, .c 7, .c 67, .c 3,
  .c 173, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 13, .c 3, .c 19, .c 491, .c 3, .c 367, .c 11,
  .c 3, .p pv2 [pv2,pv7,pv23,pv1733], .c 5, .c 3, .c 7, .c 41, .c 3, .c 5, .c 17, .c 3, .c 11,
  .c 7, .c 3, .p pv2 [pv2,pv13,pv127], .c 19, .c 3, .c 541, .c 5, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv5,pv12401], .c 3, .c 5, .c 73, .c 3, .c 7, .c 59, .c 3, .p pv2 [pv2,pv558053],
  .c 47, .c 3, .c 157, .c 5, .c 3, .c 193, .c 23, .c 3, .c 5, .c 53, .c 3, .c 359,
  .p pv2 [pv2,pv3,pv281,pv331], .c 3, .c 11, .c 137, .c 3, .c 7, .c 5, .c 3, .c 89, .c 43, .c 3,
  .c 5, .c 7, .c 3, .c 409,
]
private theorem h0136c07 : checkBlock 1115907 128 b0136c07 = true := by
  decide +kernel

private def b0136c08 : List Row := [
  .p pv2 [pv2,pv3,pv59,pv1051], .c 3, .c 13, .c 17, .c 3, .p pv2 [pv2,pv263,pv1061], .c 5, .c 3,
  .c 37, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv31,pv353], .c 3, .c 71, .c 13, .c 3, .c 251,
  .c 7, .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv69763], .c 103, .c 3, .c 5, .c 31, .c 3, .c 59,
  .p pv3 [pv2,pv3,pv186037], .c 3, .c 7, .p pv2 [pv2,pv3,pv167,pv557], .c 3, .c 53, .c 5, .c 3,
  .c 29, .c 7, .c 3, .c 5, .c 11, .c 3, .c 131, .c 37, .c 3, .p pv3 [pv2,pv34883], .c 23, .c 3,
  .c 499, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv97,pv137], .c 3,
  .p pv3 [pv2,pv5,pv11,pv43,pv59], .c 7, .c 3, .c 67, .p pv7 [pv2,pv3,pv17,pv19], .c 3, .c 463,
  .c 5, .c 3, .c 347, .p pv2 [pv2,pv3,pv5,pv61], .c 3, .c 5, .c 19, .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv73,pv3823], .p pv3 [pv2,pv3,pv7,pv3797], .c 3, .c 13, .c 5, .c 3,
  .p pv3 [pv2,pv23,pv6067], .c 107, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv1789], .c 3, .c 31, .c 151,
  .c 3, .p pv2 [pv2,pv7,pv11,pv659], .c 13, .c 3, .c 7, .c 5, .c 3, .c 733, .c 61, .c 3, .c 5,
  .c 7, .c 3, .p pv2 [pv2,pv5,pv111637], .c 17, .c 3, .c 439, .c 11, .c 3, .c 19, .c 5, .c 3,
  .c 41, .c 47, .c 3, .c 5, .c 23, .c 3, .c 11, .c 31, .c 3, .c 17, .c 7, .c 3, .c 29, .c 5, .c 3,
]
private theorem h0136c08 : checkBlock 1116163 128 b0136c08 = true := by
  decide +kernel

private def b0136c09 : List Row := [
  .p pv2 [pv2,pv558209], .c 19, .c 3, .c 5, .c 13, .c 3, .p pv7 [pv2,pv5,pv7,pv41,pv389], .c 83,
  .c 3, .c 7, .p pv7 [pv2,pv3,pv37,pv47,pv107], .c 3, .c 23, .c 5, .c 3, .p pv3 [pv2,pv139,pv251],
  .c 7, .c 3, .c 5, .c 59, .c 3, .p pv3 [pv2,pv5,pv55823], .c 331, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv31013], .c 3, .p pv3 [pv2,pv7,pv19937], .c 5, .c 3, .c 7, .c 337, .c 3, .c 5,
  .c 109, .c 3, .p pv2 [pv2,pv5,pv311,pv359], .c 7, .c 3, .c 19, .p pv2 [pv2,pv3,pv53,pv3511],
  .c 3, .c 521, .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .c 907, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv11,pv5639], .c 3, .c 31, .c 29, .c 3, .c 11, .c 5, .c 3, .c 353,
  .p pv7 [pv2,pv3,pv5,pv6203], .c 3, .c 5, .p pv2 [pv2,pv3,pv71,pv2621], .c 3, .c 53, .c 41, .c 3,
  .c 13, .c 307, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv139571],
  .p pv2 [pv2,pv3,pv5,pv7,pv13,pv409], .c 3, .c 5, .c 7, .c 3, .c 23, .c 13, .c 3, .c 29, .c 31,
  .c 3, .p pv3 [pv2,pv19,pv3673], .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv1861], .c 3, .c 5,
  .c 719, .c 3, .c 17, .c 227, .c 3, .c 71, .c 7, .c 3, .c 37, .c 5, .c 3, .c 739,
  .p pv3 [pv2,pv3,pv5,pv19,pv653], .c 3, .c 5, .p pv5 [pv2,pv3,pv93053], .c 3,
  .p pv3 [pv2,pv5,pv7,pv997], .c 11, .c 3, .c 7, .c 19, .c 3, .p pv2 [pv2,pv107,pv2609], .c 5,
  .c 3, .p pv2 [pv2,pv601,pv929], .c 7, .c 3, .c 5, .c 43, .c 3, .c 857, .c 23,
]
private theorem h0136c09 : checkBlock 1116419 128 b0136c09 = true := by
  decide +kernel

private def b0136c10 : List Row := [
  .c 3, .p pv2 [pv2,pv11,pv41,pv619], .c 17, .c 3, .c 89, .c 5, .c 3, .c 7, .c 487, .c 3, .c 5,
  .c 37, .c 3, .p pv2 [pv2,pv5,pv13,pv859], .c 7, .c 3, .c 433, .c 11, .c 3, .c 13, .c 5, .c 3,
  .c 23, .c 431, .c 3, .c 5, .c 61, .c 3, .c 7, .c 887, .c 3, .c 751, .c 13, .c 3,
  .p pv5 [pv2,pv11,pv23,pv2207], .c 5, .c 3, .p pv2 [pv2,pv279187], .p pv11 [pv2,pv3,pv5,pv1489],
  .c 3, .c 5, .c 101, .c 3, .c 29, .c 19, .c 3, .c 47, .c 233, .c 3, .c 7, .c 5, .c 3, .c 113,
  .c 17, .c 3, .c 5, .c 7, .c 3, .c 13, .c 197, .c 3, .c 11, .c 41, .c 3, .c 443, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv11,pv37], .c 23, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv19,pv2939], .c 67,
  .c 3, .c 73, .c 7, .c 3, .c 229, .c 5, .c 3, .c 19, .c 11, .c 3, .c 5, .c 239, .c 3,
  .p pv2 [pv2,pv5,pv7,pv3191], .p pv2 [pv2,pv3,pv11,pv8461], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv19,pv97,pv101], .c 3, .c 11, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 19, .c 3,
  .c 41, .c 17, .c 3, .p pv5 [pv2,pv613,pv911], .p pv13 [pv2,pv3,pv173,pv269], .c 3,
  .p pv3 [pv2,pv7,pv113,pv353], .c 5, .c 3, .c 7, .c 71, .c 3, .c 5, .c 11, .c 3,
  .p pv11 [pv2,pv5,pv61,pv1831], .c 7, .c 3, .c 17, .c 37, .c 3, .c 109, .c 5, .c 3, .c 11,
]
private theorem h0136c10 : checkBlock 1116675 128 b0136c10 = true := by
  decide +kernel

private def b0136c11 : List Row := [
  .c 83, .c 3, .c 5, .p pv5 [pv2,pv3,pv5171], .c 3, .c 7, .p pv5 [pv2,pv3,pv186157], .c 3, .c 13,
  .c 23, .c 3, .c 19, .c 5, .c 3, .c 101, .c 31, .c 3, .c 5, .c 941, .c 3, .c 61, .c 11, .c 3,
  .p pv5 [pv2,pv7,pv9973], .c 409, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv59,pv4733], .c 19, .c 3,
  .c 5, .c 7, .c 3, .c 283, .c 461, .c 3, .c 223, .p pv7 [pv2,pv3,pv7757], .c 3,
  .p pv2 [pv2,pv13,pv21481], .c 5, .c 3, .c 17, .p pv31 [pv2,pv3,pv5,pv18617], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv62057], .c 3, .p pv11 [pv2,pv5,pv37,pv3019], .p pv13 [pv2,pv3,pv7,pv61,pv109],
  .c 3, .c 131, .c 7, .c 3, .c 71, .c 5, .c 3, .c 47, .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv2909],
  .c 3, .c 11, .c 167, .c 3, .c 7, .p pv2 [pv2,pv3,pv93089], .c 3, .p pv3 [pv2,pv11,pv577], .c 5,
  .c 3, .p pv13 [pv2,pv558539], .c 7, .c 3, .c 5, .c 17, .c 3, .c 67, .c 61, .c 3, .c 43,
  .p pv2 [pv2,pv3,pv137,pv151], .c 3, .c 13, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv23,pv1619],
  .c 3, .c 5, .p pv23 [pv2,pv3,pv7,pv11,pv13,pv31], .c 3, .c 17, .c 7, .c 3, .c 11, .c 13, .c 3,
  .c 23, .c 5, .c 3, .c 79, .c 37, .c 3, .c 5, .c 31, .c 3, .c 7, .p pv29 [pv2,pv3,pv431], .c 3,
  .c 269, .c 191, .c 3, .c 503, .c 5, .c 3, .p pv3 [pv2,pv13,pv41,pv131], .c 11, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv46549], .c 3, .c 13, .c 43, .c 3,
]
private theorem h0136c11 : checkBlock 1116931 128 b0136c11 = true := by
  decide +kernel

private def b0136c12 : List Row := [
  .c 53, .c 17, .c 3, .c 7, .c 5, .c 3, .p pv13 [pv2,pv558599], .c 251, .c 3, .c 5, .c 7, .c 3,
  .c 383, .c 1051, .c 3, .c 89, .c 19, .c 3, .c 17, .c 5, .c 3, .c 809, .c 113, .c 3, .c 5, .c 11,
  .c 3, .c 103, .p pv2 [pv2,pv3,pv7,pv8867], .c 3, .p pv5 [pv2,pv13,pv97,pv443], .c 7, .c 3,
  .p pv2 [pv2,pv37,pv7549], .c 5, .c 3, .c 11, .c 499, .c 3, .c 5, .p pv3 [pv2,pv3,pv186211],
  .c 3, .c 23, .p pv5 [pv2,pv3,pv13,pv3581], .c 3, .c 7, .p pv3 [pv2,pv3,pv62071], .c 3, .c 29,
  .c 5, .c 3, .c 37, .c 7, .c 3, .c 5, .c 79, .c 3, .p pv2 [pv2,pv5,pv11173], .c 11, .c 3,
  .p pv2 [pv2,pv89,pv6277], .p pv2 [pv2,pv3,pv17,pv5477], .c 3, .c 181, .c 5, .c 3, .c 7,
  .p pv37 [pv2,pv3,pv5,pv9311], .c 3, .c 5, .c 71, .c 3, .c 47, .c 7, .c 3, .c 13, .c 1013, .c 3,
  .c 97, .c 5, .c 3, .p pv2 [pv2,pv279337], .c 149, .c 3, .c 5, .c 769, .c 3, .c 7, .c 13, .c 3,
  .p pv5 [pv2,pv558683], .c 11, .c 3, .c 41, .c 5, .c 3, .p pv2 [pv2,pv47,pv11887], .c 821, .c 3,
  .c 5, .c 617, .c 3, .c 11, .c 17, .c 3, .c 167, .c 29, .c 3, .c 7, .c 5, .c 3, .c 19, .c 73,
  .c 3, .c 5, .c 7, .c 3, .c 139, .c 311, .c 3, .c 17, .c 83, .c 3, .p pv3 [pv2,pv23,pv6073],
  .c 5, .c 3, .p pv11 [pv2,pv7,pv79817], .c 13,
]
private theorem h0136c12 : checkBlock 1117187 128 b0136c12 = true := by
  decide +kernel

private def b0136c13 : List Row := [
  .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv22349], .c 223, .c 3, .c 11, .c 7, .c 3,
  .p pv5 [pv2,pv558731], .c 5, .c 3, .c 71, .p pv11 [pv2,pv3,pv5,pv193], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv3449], .c 3, .p pv3 [pv2,pv5,pv7,pv13,pv307], .p pv3 [pv2,pv3,pv186247], .c 3,
  .c 7, .p pv11 [pv2,pv3,pv31,pv751], .c 3, .c 13, .c 5, .c 3, .c 613, .c 7, .c 3, .c 5, .c 479,
  .c 3, .c 37, .p pv5 [pv2,pv3,pv11,pv17,pv83], .c 3, .c 241, .c 13, .c 3, .c 11, .c 5, .c 3,
  .c 7, .c 467, .c 3, .c 5, .c 41, .c 3, .c 191, .c 7, .c 3, .c 23, .p pv2 [pv2,pv3,pv37,pv839],
  .c 3, .p pv3 [pv2,pv69847], .c 5, .c 3, .c 859, .c 19, .c 3, .c 5, .c 11, .c 3, .c 7, .c 29,
  .c 3, .c 109, .p pv2 [pv2,pv3,pv7,pv11,pv41,pv59], .c 3, .c 431, .c 5, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv5,pv37253], .c 3, .c 5, .c 13, .c 3, .p pv19 [pv2,pv5,pv11,pv127],
  .p pv3 [pv2,pv3,pv29,pv2141], .c 3, .p pv5 [pv2,pv7,pv79829], .p pv7 [pv2,pv3,pv46567], .c 3,
  .c 7, .c 5, .c 3, .c 41, .c 971, .c 3, .c 5, .c 7, .c 3, .c 17, .c 11, .c 3, .c 19, .c 23, .c 3,
  .c 31, .c 5, .c 3, .c 13, .c 523, .c 3, .c 5, .p pv5 [pv2,pv3,pv19,pv43], .c 3,
  .p pv3 [pv2,pv5,pv29,pv41,pv47], .c 193, .c 3, .c 211, .c 7, .c 3, .p pv3 [pv2,pv139709], .c 5,
  .c 3, .p pv17 [pv2,pv83,pv6733], .p pv37 [pv2,pv3,pv5,pv4657], .c 3, .c 5, .c 347, .c 3, .c 163,
  .c 257, .c 3, .c 7,
]
private theorem h0136c13 : checkBlock 1117443 128 b0136c13 = true := by
  decide +kernel

private def b0136c14 : List Row := [
  .c 11, .c 3, .c 61, .c 5, .c 3, .p pv2 [pv2,pv23,pv12149], .c 7, .c 3, .c 5, .c 53, .c 3, .c 11,
  .c 313, .c 3, .c 13, .p pv23 [pv2,pv3,pv3881], .c 3, .c 17, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv13,pv1433], .c 3, .c 5, .c 29, .c 3, .c 19, .c 7, .c 3,
  .p pv2 [pv2,pv103,pv2713], .p pv3 [pv2,pv3,pv241,pv773], .c 3, .p pv2 [pv2,pv558881], .c 5,
  .c 3, .p pv3 [pv2,pv139721], .c 79, .c 3, .c 5, .c 23, .c 3, .c 7, .c 41, .c 3, .c 11, .c 19,
  .c 3, .p pv3 [pv2,pv13,pv2687], .c 5, .c 3, .p pv7 [pv2,pv11,pv31,pv149], .c 17, .c 3, .c 5,
  .c 37, .c 3, .p pv13 [pv2,pv5,pv111781], .p pv5 [pv2,pv3,pv93151], .c 3,
  .p pv3 [pv2,pv7,pv19961], .p pv3 [pv2,pv3,pv13,pv17,pv281], .c 3, .c 7, .c 5, .c 3, .c 31,
  .c 11, .c 3, .c 5, .c 7, .c 3, .c 937, .c 1019, .c 3, .c 349, .c 73, .c 3, .c 11, .c 5, .c 3,
  .c 103, .p pv19 [pv2,pv3,pv5,pv31,pv601], .c 3, .c 5, .p pv2 [pv2,pv3,pv186311], .c 3, .c 43,
  .c 59, .c 3, .p pv2 [pv2,pv53,pv5273], .c 7, .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv17467],
  .c 31, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv7,pv1597], .c 17, .c 3, .c 7, .c 13, .c 3,
  .p pv3 [pv2,pv139739], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 83, .c 3,
  .p pv17 [pv2,pv5,pv11,pv10163], .p pv5 [pv2,pv3,pv59,pv1579], .c 3, .c 17,
  .p pv2 [pv2,pv3,pv23,pv8101], .c 3, .p pv5 [pv2,pv7,pv47,pv1699], .c 5, .c 3, .c 7, .c 353,
  .c 3,
]
private theorem h0136c14 : checkBlock 1117699 128 b0136c14 = true := by
  decide +kernel

private def b0136c15 : List Row := [
  .c 5, .c 43, .c 3, .c 13, .c 7, .c 3, .p pv5 [pv2,pv71,pv7873], .c 101, .c 3,
  .p pv2 [pv2,pv277,pv1009], .c 5, .c 3, .c 19, .c 127, .c 3, .c 5, .c 13, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv37,pv1259], .c 3, .c 157, .c 241, .c 3, .p pv2 [pv2,pv559001], .c 5, .c 3,
  .p pv3 [pv2,pv29,pv61,pv79], .p pv2 [pv2,pv3,pv5,pv83,pv449], .c 3, .c 5, .c 19, .c 3,
  .p pv2 [pv2,pv5,pv55901], .p pv7 [pv2,pv3,pv17,pv97,pv113], .c 3, .p pv2 [pv2,pv7,pv13,pv6143],
  .c 11, .c 3, .c 7, .c 5, .c 3, .c 13, .p pv31 [pv2,pv3,pv5,pv7,pv11], .c 3, .c 5, .c 7, .c 3,
  .c 11, .c 23, .c 3, .c 137, .c 317, .c 3, .p pv5 [pv2,pv11,pv50821], .c 5, .c 3, .c 61, .c 683,
  .c 3, .c 5, .c 31, .c 3, .p pv3 [pv2,pv5,pv1747], .c 47, .c 3, .c 79, .c 7, .c 3, .c 19, .c 5,
  .c 3, .c 23, .p pv2 [pv2,pv3,pv5,pv3727], .c 3, .c 5, .c 17, .c 3, .c 41,
  .p pv5 [pv2,pv3,pv19,pv613], .c 3, .c 7, .c 97, .c 3, .p pv2 [pv2,pv23,pv109,pv223], .c 5, .c 3,
  .c 43, .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv46589], .c 3, .c 17, .c 13, .c 3,
  .p pv2 [pv2,pv271,pv2063], .p pv2 [pv2,pv3,pv93179], .c 3, .c 29, .c 5, .c 3, .c 7, .c 11, .c 3,
  .c 5, .c 233, .c 3, .c 101, .c 7, .c 3, .c 37, .c 71, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv19,pv14713], .c 23, .c 3, .c 5, .p pv2 [pv2,pv3,pv89,pv349], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv227,pv821], .c 3, .c 19, .c 17,
]
private theorem h0136c15 : checkBlock 1117955 128 b0136c15 = true := by
  decide +kernel

private def b0136c16 : List Row := [
  .c 3, .c 179, .c 5, .c 3, .p pv2 [pv2,pv181,pv3089], .c 13, .c 3, .c 5, .c 11, .c 3, .c 109,
  .c 269, .c 3, .c 23, .c 751, .c 3, .c 7, .c 5, .c 3, .c 11, .c 37, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv11,pv13,pv17,pv23], .c 31, .c 3, .p pv2 [pv2,pv559133], .c 29, .c 3, .c 13,
  .c 5, .c 3, .c 457, .c 239, .c 3, .c 5, .c 73, .c 3, .p pv2 [pv2,pv5,pv111829], .c 11, .c 3,
  .c 67, .c 7, .c 3, .p pv5 [pv2,pv19,pv29429], .c 5, .c 3, .p pv2 [pv2,pv279577], .c 17, .c 3,
  .c 5, .p pv13 [pv2,pv3,pv41,pv2273], .c 3, .c 19, .c 659, .c 3, .c 7, .c 23, .c 3, .c 599, .c 5,
  .c 3, .p pv2 [pv2,pv13,pv43013], .c 7, .c 3, .c 5, .c 131, .c 3, .c 13, .c 53, .c 3, .c 41,
  .c 11, .c 3, .p pv2 [pv2,pv7,pv17,pv37,pv127], .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv11,pv3389], .c 3, .c 5, .c 13, .c 3, .c 11, .c 7, .c 3, .c 31, .c 401,
  .c 3, .p pv3 [pv2,pv11,pv71,pv179], .c 5, .c 3, .c 37, .c 307, .c 3, .c 5, .c 947, .c 3, .c 7,
  .c 17, .c 3, .c 271, .p pv3 [pv2,pv3,pv7,pv31,pv859], .c 3, .c 919, .c 5, .c 3, .c 13, .c 67,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv37,pv229], .c 3, .p pv3 [pv2,pv5,pv27961], .c 29, .c 3,
  .c 11, .c 31, .c 3, .c 7, .c 5, .c 3, .c 47, .c 601, .c 3, .c 5,
]
private theorem h0136c16 : checkBlock 1118211 128 b0136c16 = true := by
  decide +kernel

private def b0136c17 : List Row := [
  .c 7, .c 3, .c 107, .c 19, .c 3, .c 103, .p pv3 [pv2,pv3,pv131,pv1423], .c 3,
  .p pv2 [pv2,pv79,pv7079], .c 5, .c 3, .c 127, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv61,pv191],
  .c 3, .c 29, .c 337, .c 3, .c 13, .c 7, .c 3, .c 11, .c 5, .c 3, .p pv23 [pv2,pv559259], .c 41,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv277,pv673], .c 3, .c 773, .c 13, .c 3, .c 7, .c 263, .c 3, .c 149,
  .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 11, .c 3, .c 79, .p pv3 [pv2,pv3,pv41,pv4547], .c 3,
  .p pv5 [pv2,pv17,pv167,pv197], .p pv41 [pv2,pv3,pv11,pv19,pv223], .c 3, .c 31, .c 5, .c 3, .c 7,
  .c 59, .c 3, .c 5, .c 19, .c 3, .c 83, .c 7, .c 3, .c 421, .p pv3 [pv2,pv3,pv13,pv14341], .c 3,
  .c 41, .c 5, .c 3, .c 131, .c 13, .c 3, .c 5, .c 17, .c 3, .c 7, .c 11, .c 3, .c 373,
  .p pv2 [pv2,pv3,pv7,pv23,pv193], .c 3, .c 233, .c 5, .c 3, .c 487, .c 89, .c 3, .c 5, .c 47,
  .c 3, .c 17, .p pv5 [pv2,pv3,pv73,pv1277], .c 3, .c 353, .p pv2 [pv2,pv3,pv37,pv5039], .c 3,
  .c 7, .c 5, .c 3, .c 163, .c 53, .c 3, .c 5, .c 7, .c 3, .c 563, .c 103, .c 3, .c 191, .c 11,
  .c 3, .c 317, .c 5, .c 3, .c 59, .c 19, .c 3, .c 5, .c 251, .c 3, .c 11,
  .p pv13 [pv2,pv3,pv7,pv6659], .c 3, .p pv2 [pv2,pv279679], .c 7, .c 3,
]
private theorem h0136c17 : checkBlock 1118467 128 b0136c17 = true := by
  decide +kernel

private def b0136c18 : List Row := [
  .p pv2 [pv2,pv11,pv211,pv241], .c 5, .c 3, .c 691, .c 43, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv17,pv457], .c 3, .c 13, .c 23, .c 3, .c 7, .p pv2 [pv2,pv3,pv93229], .c 3,
  .c 17, .c 5, .c 3, .c 31, .c 7, .c 3, .c 5, .c 13, .c 3, .c 269, .p pv2 [pv2,pv3,pv1151], .c 3,
  .c 11, .p pv2 [pv2,pv3,pv199,pv937], .c 3, .p pv7 [pv2,pv7,pv157,pv509], .c 5, .c 3, .c 7,
  .c 29, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv19,pv701], .c 3, .c 61, .c 7, .c 3,
  .p pv5 [pv2,pv13,pv37,pv1163], .p pv7 [pv2,pv3,pv41,pv379], .c 3, .c 113, .c 5, .c 3, .c 13,
  .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv20719], .c 3, .c 7, .c 67, .c 3, .p pv2 [pv2,pv279709],
  .c 991, .c 3, .c 11, .c 5, .c 3, .c 29, .p pv2 [pv2,pv3,pv5,pv7459], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv46619], .c 3, .p pv2 [pv2,pv5,pv43,pv1301], .p pv5 [pv2,pv3,pv61,pv1019],
  .c 3, .p pv2 [pv2,pv7,pv233], .p pv7 [pv2,pv3,pv93239], .c 3, .c 7, .c 5, .c 3, .c 137, .c 23,
  .c 3, .c 5, .c 7, .c 3, .c 19, .p pv2 [pv2,pv3,pv93241], .c 3, .c 13, .c 107, .c 3, .c 43, .c 5,
  .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv13,pv19,pv151], .c 3, .c 5, .c 37, .c 3,
  .p pv3 [pv2,pv5,pv11,pv2543], .c 13, .c 3, .c 23, .c 7, .c 3, .c 211, .c 5, .c 3, .c 157,
  .p pv13 [pv2,pv3,pv5,pv17,pv1097], .c 3, .c 5, .p pv2 [pv2,pv3,pv43,pv4337], .c 3,
  .p pv7 [pv2,pv5,pv7,pv23,pv139], .c 11, .c 3, .c 7, .c 271, .c 3, .c 241, .c 5, .c 3,
  .p pv3 [pv2,pv139871], .c 7, .c 3, .c 5, .c 199,
]
private theorem h0136c18 : checkBlock 1118723 128 b0136c18 = true := by
  decide +kernel

private def b0136c19 : List Row := [
  .c 3, .c 1009, .c 367, .c 3, .p pv2 [pv2,pv11,pv19,pv2677], .c 43, .c 3,
  .p pv3 [pv2,pv7,pv97,pv103], .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 31, .c 3, .c 439, .c 7,
  .c 3, .c 73, .c 11, .c 3, .c 29, .c 5, .c 3, .p pv2 [pv2,pv37,pv7561], .c 71, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv93253], .c 3, .c 7, .c 19, .c 3, .p pv5 [pv2,pv559523],
  .p pv31 [pv2,pv3,pv7,pv6661], .c 3, .c 13, .c 5, .c 3, .c 17, .c 151, .c 3, .c 5, .c 167, .c 3,
  .c 463, .c 661, .c 3, .p pv2 [pv2,pv7,pv17,pv2351], .c 13, .c 3, .c 7, .c 5, .c 3, .c 83,
  .p pv7 [pv2,pv3,pv5,pv7,pv73], .c 3, .c 5, .c 7, .c 3, .c 67, .c 109, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv179,pv521], .c 3, .c 107, .c 5, .c 3, .c 19, .p pv23 [pv2,pv3,pv5,pv4663],
  .c 3, .c 5, .c 17, .c 3, .c 13, .c 131, .c 3, .c 173, .c 7, .c 3, .c 397, .c 5, .c 3, .c 419,
  .c 11, .c 3, .c 5, .c 13, .c 3, .c 17, .c 73, .c 3, .c 7, .p pv11 [pv2,pv3,pv29,pv67], .c 3,
  .c 11, .c 5, .c 3, .p pv2 [pv2,pv17,pv32917], .c 7, .c 3, .c 5, .c 379, .c 3, .c 401, .c 31,
  .c 3, .c 29, .c 673, .c 3, .c 23, .c 5, .c 3, .c 7, .c 47, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv107,pv523], .c 7, .c 3, .p pv2 [pv2,pv23,pv29,pv839], .c 17, .c 3, .c 19,
]
private theorem h0136c19 : checkBlock 1118979 128 b0136c19 = true := by
  decide +kernel

private def b0136c20 : List Row := [
  .c 5, .c 3, .c 11, .p pv11 [pv2,pv3,pv5,pv3109], .c 3, .c 5, .c 43, .c 3, .c 7, .c 157, .c 3,
  .c 499, .c 41, .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv279817], .c 19, .c 3, .c 5, .c 859, .c 3,
  .p pv3 [pv2,pv5,pv17,pv823], .c 11, .c 3, .c 13, .c 59, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv559649], .c 103, .c 3, .c 5, .c 7, .c 3, .c 863, .c 13, .c 3, .c 31,
  .p pv3 [pv2,pv3,pv23,pv8111], .c 3, .p pv2 [pv2,pv307,pv1823], .c 5, .c 3, .c 541, .c 17, .c 3,
  .c 5, .c 227, .c 3, .c 23, .p pv7 [pv2,pv3,pv7,pv29,pv919], .c 3, .c 19, .c 7, .c 3, .c 89,
  .c 5, .c 3, .p pv13 [pv2,pv559679], .c 37, .c 3, .c 5, .c 139, .c 3, .c 11, .c 373, .c 3, .c 7,
  .c 31, .c 3, .c 101, .c 5, .c 3, .p pv2 [pv2,pv279847], .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv93283], .c 3, .c 167, .p pv3 [pv2,pv3,pv62189], .c 3, .c 59, .c 587, .c 3,
  .c 53, .c 5, .c 3, .c 7, .c 83, .c 3, .c 5, .c 137, .c 3, .c 761, .c 7, .c 3, .c 11, .c 421,
  .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv11,pv12721], .c 191, .c 3, .c 5, .c 71, .c 3, .c 7,
  .c 643, .c 3, .c 17, .c 13, .c 3, .p pv3 [pv2,pv31,pv37,pv61], .c 5, .c 3, .c 23, .c 11, .c 3,
  .c 5, .c 29, .c 3,
]
private theorem h0136c20 : checkBlock 1119235 128 b0136c20 = true := by
  decide +kernel

private def b0136c21 : List Row := [
  .c 113, .c 47, .c 3, .c 701, .c 19, .c 3, .c 7, .c 5, .c 3, .c 37, .c 709, .c 3, .c 5, .c 7,
  .c 3, .c 13, .p pv2 [pv2,pv3,pv186587], .c 3, .p pv5 [pv2,pv131,pv4273],
  .p pv17 [pv2,pv3,pv71,pv73], .c 3, .c 61, .c 5, .c 3, .c 109, .c 107, .c 3, .c 5, .c 11, .c 3,
  .c 197, .c 293, .c 3, .p pv2 [pv2,pv19,pv14731], .c 7, .c 3, .c 971, .c 5, .c 3, .c 11, .c 23,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv46649], .c 3, .c 229, .c 37, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv79,pv1181], .c 3, .c 193, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv186601], .c 3, .p pv2 [pv2,pv5,pv103,pv1087], .c 11, .c 3, .c 23, .c 911,
  .c 3, .p pv5 [pv2,pv7,pv79973], .c 5, .c 3, .c 7, .c 997, .c 3, .c 5, .c 17, .c 3, .c 659, .c 7,
  .c 3, .c 163, .p pv13 [pv2,pv3,pv107,pv109], .c 3, .p pv2 [pv2,pv279913], .c 5, .c 3,
  .p pv2 [pv2,pv31,pv18059], .c 29, .c 3, .c 5, .c 79, .c 3, .c 7, .p pv23 [pv2,pv3,pv15551],
  .c 3, .c 13, .c 11, .c 3, .c 223, .c 5, .c 3, .c 19, .p pv3 [pv2,pv3,pv5,pv11,pv13,pv29], .c 3,
  .c 5, .p pv5 [pv2,pv3,pv23327], .c 3, .c 11, .c 13, .c 3, .p pv2 [pv2,pv7,pv79979], .c 23, .c 3,
  .c 7, .c 5, .c 3, .c 29, .c 359, .c 3, .c 5, .c 7, .c 3, .c 37, .p pv2 [pv2,pv3,pv23,pv4057],
  .c 3, .p pv3 [pv2,pv139967], .c 17, .c 3, .c 523, .c 5,
]
private theorem h0136c21 : checkBlock 1119491 128 b0136c21 = true := by
  decide +kernel

private def b0136c22 : List Row := [
  .c 3, .c 257, .c 31, .c 3, .c 5, .c 109, .c 3, .c 59, .c 43, .c 3, .c 11, .c 7, .c 3, .c 17,
  .c 5, .c 3, .p pv2 [pv2,pv11,pv23,pv2213], .c 13, .c 3, .c 5, .c 101, .c 3, .c 227,
  .p pv5 [pv2,pv3,pv41,pv569], .c 3, .c 7, .p pv3 [pv2,pv3,pv89,pv233], .c 3, .c 19, .c 5, .c 3,
  .p pv3 [pv2,pv17497], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv103,pv151], .c 3,
  .p pv2 [pv2,pv5,pv13,pv59,pv73], .p pv3 [pv2,pv3,pv11,pv19,pv47], .c 3, .c 641, .c 173, .c 3,
  .c 11, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 23, .c 3, .c 337, .c 7, .c 3,
  .p pv3 [pv2,pv69991], .c 13, .c 3, .p pv5 [pv2,pv107,pv5233], .c 5, .c 3, .c 47,
  .p pv11 [pv2,pv3,pv5,pv23,pv541], .c 3, .c 5, .c 11, .c 3, .c 7, .c 71, .c 3, .c 89, .c 439,
  .c 3, .c 23, .c 5, .c 3, .c 11, .c 787, .c 3, .c 5, .p pv2 [pv2,pv3,pv31,pv223], .c 3, .c 13,
  .p pv19 [pv2,pv3,pv46663], .c 3, .c 19, .c 83, .c 3, .c 7, .c 5, .c 3, .c 877, .c 389, .c 3,
  .c 5, .c 7, .c 3, .c 349, .c 11, .c 3, .p pv2 [pv2,pv559973], .p pv11 [pv2,pv3,pv93329], .c 3,
  .c 37, .c 5, .c 3, .p pv7 [pv2,pv7,pv79997], .c 317, .c 3, .c 5, .c 151, .c 3, .c 491, .c 163,
  .c 3, .c 17, .c 7, .c 3, .c 79, .c 5, .c 3, .c 13, .c 811, .c 3, .c 5, .c 41, .c 3,
  .p pv3 [pv2,pv5,pv7],
]
private theorem h0136c22 : checkBlock 1119747 128 b0136c22 = true := by
  decide +kernel

private def b0136c23 : List Row := [
  .c 179, .c 3, .c 7, .c 11, .c 3, .c 127, .c 5, .c 3, .p pv2 [pv2,pv227,pv2467], .c 7, .c 3,
  .c 5, .c 37, .c 3, .c 11, .c 149, .c 3, .c 1021, .c 67, .c 3, .c 271, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv19,pv131], .c 3, .c 5, .c 47, .c 3, .c 31, .c 7, .c 3, .c 13, .c 19, .c 3,
  .p pv3 [pv2,pv140009], .c 5, .c 3, .c 17, .p pv11 [pv2,pv3,pv5,pv13,pv359], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv5657], .c 3, .c 7, .c 13, .c 3, .c 11, .c 857, .c 3, .c 823, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv25457], .c 691, .c 3, .c 5, .c 263, .c 3, .p pv11 [pv2,pv5,pv41,pv683],
  .c 23, .c 3, .c 557, .c 223, .c 3, .c 7, .c 5, .c 3, .c 293, .c 11, .c 3, .c 5, .c 7, .c 3,
  .c 47, .p pv5 [pv2,pv3,pv11,pv4243], .c 3, .p pv2 [pv2,pv97,pv2887],
  .p pv3 [pv2,pv3,pv13,pv4787], .c 3, .c 11, .c 5, .c 3, .c 23, .c 13, .c 3, .c 5, .c 593, .c 3,
  .c 17, .c 19, .c 3, .p pv2 [pv2,pv560093], .c 7, .c 3, .c 43, .c 5, .c 3, .c 211, .c 139, .c 3,
  .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv7,pv13,pv1231], .c 251, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv11,pv1543], .c 3, .c 13, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv13,pv43,pv167], .c 3, .c 29, .c 41, .c 3, .c 31, .c 13, .c 3, .c 97, .c 5,
  .c 3,
]
private theorem h0136c23 : checkBlock 1120003 128 b0136c23 = true := by
  decide +kernel

private def b0136c24 : List Row := [
  .c 7, .c 23, .c 3, .c 5, .c 127, .c 3, .p pv11 [pv2,pv5,pv29,pv3863], .c 7, .c 3,
  .p pv2 [pv2,pv280069], .c 43, .c 3, .c 17, .c 5, .c 3, .p pv3 [pv2,pv13,pv2693],
  .p pv3 [pv2,pv3,pv5,pv107,pv349], .c 3, .c 5, .c 19, .c 3, .c 7, .p pv3 [pv2,pv3,pv109,pv571],
  .c 3, .c 23, .c 31, .c 3, .p pv3 [pv2,pv131,pv1069], .c 5, .c 3, .p pv7 [pv2,pv560159],
  .p pv7 [pv2,pv3,pv5,pv389], .c 3, .c 5, .c 13, .c 3, .c 73, .c 467, .c 3,
  .p pv3 [pv2,pv7,pv1429], .c 11, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv173,pv1619], .c 17, .c 3,
  .c 5, .c 7, .c 3, .c 11, .p pv2 [pv2,pv3,pv186727], .c 3, .c 53, .p pv7 [pv2,pv3,pv17,pv1373],
  .c 3, .c 19, .c 5, .c 3, .c 13, .c 479, .c 3, .c 5, .c 61, .c 3, .p pv17 [pv2,pv5,pv181,pv619],
  .c 101, .c 3, .c 37, .c 7, .c 3, .c 167, .c 5, .c 3, .c 241, .c 19, .c 3, .c 5, .c 83, .c 3,
  .c 89, .p pv3 [pv2,pv3,pv23,pv353], .c 3, .c 7, .p pv2 [pv2,pv3,pv31123], .c 3, .c 31, .c 5,
  .c 3, .c 359, .c 7, .c 3, .c 5, .c 97, .c 3, .c 43, .c 17, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv186743], .c 3, .c 347, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 73, .c 3,
  .p pv7 [pv2,pv5,pv47,pv149], .c 7, .c 3, .c 17, .c 41, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv560249], .p pv11 [pv2,pv3,pv5,pv83], .c 3, .c 5, .p pv2 [pv2,pv3,pv19,pv9829],
  .c 3, .c 7, .p pv23 [pv2,pv3,pv1459],
]
private theorem h0136c24 : checkBlock 1120259 128 b0136c24 = true := by
  decide +kernel

private def b0136c25 : List Row := [
  .c 3, .p pv2 [pv2,pv280129], .p pv3 [pv2,pv3,pv7,pv8893], .c 3, .c 137, .c 5, .c 3,
  .p pv3 [pv2,pv59,pv1187], .c 29, .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv179,pv313],
  .p pv3 [pv2,pv3,pv186757], .c 3, .p pv2 [pv2,pv7,pv80039], .p pv2 [pv2,pv3,pv11,pv13,pv653],
  .c 3, .c 7, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 7, .c 3, .c 41,
  .p pv2 [pv2,pv3,pv17,pv1831], .c 3, .p pv3 [pv2,pv17509], .c 53, .c 3, .c 23, .c 5, .c 3, .c 17,
  .p pv19 [pv2,pv3,pv5,pv12451], .c 3, .c 5, .c 191, .c 3, .c 19, .c 11, .c 3,
  .p pv5 [pv2,pv17,pv23,pv1433], .c 7, .c 3, .c 13, .c 5, .c 3, .c 31, .c 47, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv13,pv4789], .c 3, .c 61, .p pv5 [pv2,pv3,pv53,pv881], .c 3, .c 7, .c 13, .c 3,
  .c 263, .c 5, .c 3, .p pv3 [pv2,pv127,pv1103], .c 7, .c 3, .c 5, .c 17, .c 3,
  .p pv2 [pv2,pv5,pv137,pv409], .p pv3 [pv2,pv3,pv20753], .c 3, .p pv5 [pv2,pv43,pv83,pv157],
  .c 11, .c 3, .p pv3 [pv2,pv7,pv5003], .c 5, .c 3, .c 7, .c 31, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv26683], .c 3, .c 11, .c 7, .c 3, .c 1031, .c 227, .c 3, .c 379, .c 5,
  .c 3, .c 43, .p pv3 [pv2,pv3,pv5,pv37357], .c 3, .c 5, .c 13, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv151,pv1237], .c 3, .p pv5 [pv2,pv229,pv2447], .c 599, .c 3, .c 197, .c 5,
  .c 3, .p pv2 [pv2,pv53,pv97,pv109], .p pv2 [pv2,pv3,pv5,pv18679], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv16981], .c 3, .c 193, .c 19, .c 3, .c 11, .c 17, .c 3, .c 7, .c 5, .c 3,
  .c 13,
]
private theorem h0136c25 : checkBlock 1120515 128 b0136c25 = true := by
  decide +kernel

private def b0136c26 : List Row := [
  .p pv3 [pv2,pv3,pv5,pv7,pv593], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv56039],
  .p pv3 [pv2,pv3,pv13,pv14369], .c 3, .p pv2 [pv2,pv560393], .c 523, .c 3, .c 17, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv223,pv359], .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv71,pv877], .c 3,
  .p pv2 [pv2,pv5,pv17,pv19,pv347], .c 23, .c 3, .c 41, .c 7, .c 3, .c 11, .c 5, .c 3, .c 19,
  .p pv23 [pv2,pv3,pv5,pv37361], .c 3, .c 5, .p pv17 [pv2,pv3,pv23,pv31,pv131], .c 3, .c 37,
  .c 67, .c 3, .c 7, .p pv17 [pv2,pv3,pv19,pv1229], .c 3, .c 313, .c 5, .c 3, .c 23, .c 7, .c 3,
  .c 5, .c 11, .c 3, .p pv13 [pv2,pv5,pv112087], .c 13, .c 3, .c 71, .c 29, .c 3,
  .p pv5 [pv2,pv7,pv23,pv59], .c 5, .c 3, .c 7, .c 241, .c 3, .c 5, .c 53, .c 3,
  .p pv3 [pv2,pv5,pv11,pv1019], .c 7, .c 3, .p pv2 [pv2,pv263,pv2131], .c 281, .c 3,
  .p pv3 [pv2,pv13,pv17,pv317], .c 5, .c 3, .p pv7 [pv2,pv560459], .c 719, .c 3, .c 5, .c 149,
  .c 3, .c 7, .c 11, .c 3, .c 29, .p pv2 [pv2,pv3,pv7,pv13,pv2053], .c 3, .c 19, .c 5, .c 3,
  .c 103, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv109,pv857], .c 3, .p pv3 [pv2,pv5,pv31,pv113],
  .c 17, .c 3, .c 43, .p pv7 [pv2,pv3,pv15569], .c 3, .c 7, .c 5, .c 3, .c 191, .c 19, .c 3, .c 5,
  .c 7, .c 3, .c 31, .p pv5 [pv2,pv3,pv11677], .c 3, .c 17, .c 11, .c 3, .c 13, .c 5, .c 3,
  .c 619, .p pv3 [pv2,pv3,pv5,pv11,pv43,pv79], .c 3, .c 5, .p pv43 [pv2,pv3,pv13,pv3593], .c 3,
  .c 11, .p pv3 [pv2,pv3,pv7,pv31,pv41], .c 3,
]
private theorem h0136c26 : checkBlock 1120771 128 b0136c26 = true := by
  decide +kernel

private def b0136c27 : List Row := [
  .p pv2 [pv2,pv37,pv15149], .c 7, .c 3, .p pv3 [pv2,pv11,pv12739], .c 5, .c 3, .c 107, .c 383,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv186841], .c 3, .p pv2 [pv2,pv5,pv7,pv3203], .c 29, .c 3, .c 7,
  .c 59, .c 3, .c 37, .c 5, .c 3, .c 409, .c 7, .c 3, .c 5, .c 179, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv17,pv29,pv379], .c 3, .c 11, .c 23, .c 3, .p pv2 [pv2,pv7,pv40039], .c 5,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv37,pv101], .c 3, .c 5, .c 13, .c 3, .c 29, .c 7, .c 3, .c 757,
  .c 61, .c 3, .c 421, .c 5, .c 3, .c 607, .c 11, .c 3, .c 5, .c 37, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv11,pv16987], .c 3, .p pv2 [pv2,pv13,pv31,pv107], .c 239, .c 3, .c 11, .c 5,
  .c 3, .c 13, .c 71, .c 3, .c 5, .c 17, .c 3, .c 19, .p pv5 [pv2,pv3,pv13,pv7187], .c 3, .c 31,
  .p pv2 [pv2,pv3,pv67,pv2789], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv280297],
  .p pv3 [pv2,pv3,pv5,pv7,pv19,pv281], .c 3, .c 5, .c 7, .c 3, .c 17, .p pv3 [pv2,pv3,pv769],
  .c 3, .c 73, .c 19, .c 3, .c 173, .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv6229], .c 3, .c 5,
  .c 23, .c 3, .p pv13 [pv2,pv5,pv11,pv10193], .c 443, .c 3, .c 13, .c 7, .c 3, .c 751, .c 5,
  .c 3, .p pv3 [pv2,pv37,pv947], .c 647, .c 3, .c 5, .p pv5 [pv2,pv3,pv29,pv179], .c 3,
  .p pv13 [pv2,pv5,pv7,pv8009], .c 11, .c 3, .c 7, .c 17, .c 3, .c 23, .c 5, .c 3, .c 47, .c 7,
]
private theorem h0136c27 : checkBlock 1121027 128 b0136c27 = true := by
  decide +kernel

private def b0136c28 : List Row := [
  .c 3, .c 5, .c 631, .c 3, .c 257, .p pv2 [pv2,pv3,pv31147], .c 3, .p pv3 [pv2,pv11,pv23,pv277],
  .c 113, .c 3, .c 17, .c 5, .c 3, .c 7, .c 43, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv1907], .c 3,
  .c 53, .c 7, .c 3, .c 509, .c 11, .c 3, .p pv2 [pv2,pv31,pv9043], .c 5, .c 3, .c 479, .c 13,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv62297], .c 3, .c 7, .c 73, .c 3, .p pv2 [pv2,pv280339], .c 37,
  .c 3, .c 31, .c 5, .c 3, .p pv3 [pv2,pv140171], .c 17, .c 3, .c 5, .p pv17 [pv2,pv3,pv11681],
  .c 3, .c 1049, .p pv3 [pv2,pv3,pv62299], .c 3, .p pv2 [pv2,pv7,pv173,pv463],
  .p pv7 [pv2,pv3,pv17,pv23,pv239], .c 3, .c 7, .c 5, .c 3, .c 19, .c 29, .c 3, .c 5, .c 7, .c 3,
  .c 23, .c 59, .c 3, .c 11, .c 13, .c 3, .p pv5 [pv2,pv17,pv32983], .c 5, .c 3, .c 233,
  .p pv61 [pv2,pv3,pv5,pv29,pv1289], .c 3, .c 5, .c 19, .c 3, .c 911,
  .p pv2 [pv2,pv3,pv7,pv26701], .c 3, .p pv5 [pv2,pv67,pv8369], .c 7, .c 3,
  .p pv2 [pv2,pv139,pv2017], .c 5, .c 3, .c 29, .c 11, .c 3, .c 5, .c 47, .c 3, .c 13, .c 17,
  .c 3, .c 7, .c 313, .c 3, .c 11, .c 5, .c 3, .c 89, .c 7, .c 3, .c 5, .c 13, .c 3, .c 109,
  .c 23, .c 3, .c 17, .p pv31 [pv2,pv3,pv31153], .c 3, .c 19, .c 5, .c 3, .c 7, .c 197, .c 3,
  .c 5, .c 11, .c 3, .c 59, .c 7, .c 3, .c 127,
]
private theorem h0136c28 : checkBlock 1121283 128 b0136c28 = true := by
  decide +kernel

private def b0136c29 : List Row := [
  .p pv23 [pv2,pv3,pv11,pv16993], .c 3, .p pv5 [pv2,pv560771], .c 5, .c 3, .c 11, .c 19, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv93463], .c 3, .c 7, .c 79, .c 3, .c 103, .c 43, .c 3, .c 277, .c 5,
  .c 3, .c 83, .c 37, .c 3, .c 5, .c 71, .c 3, .c 139, .c 11, .c 3, .c 401,
  .p pv13 [pv2,pv3,pv62311], .c 3, .c 7, .c 5, .c 3, .c 17, .c 31, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv56081], .c 773, .c 3, .c 13, .p pv2 [pv2,pv3,pv151,pv619], .c 3, .c 29, .c 5,
  .c 3, .c 53, .c 23, .c 3, .c 5, .c 67, .c 3, .p pv2 [pv2,pv5,pv22433], .c 13, .c 3, .c 181,
  .c 7, .c 3, .c 419, .c 5, .c 3, .c 271, .p pv13 [pv2,pv3,pv5,pv11,pv103], .c 3, .c 5, .c 17,
  .c 3, .c 11, .c 877, .c 3, .c 7, .p pv11 [pv2,pv3,pv577], .c 3,
  .p pv3 [pv2,pv11,pv13,pv37,pv53], .c 5, .c 3, .p pv2 [pv2,pv43,pv13043], .c 7, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv101,pv617], .c 3, .c 17, .c 521, .c 3, .c 661, .c 41, .c 3,
  .p pv2 [pv2,pv7,pv19,pv4217], .c 5, .c 3, .c 7, .c 13, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv7,pv11,pv607], .c 3, .c 19, .c 7, .c 3, .c 11, .c 29, .c 3, .c 131, .c 5,
  .c 3, .c 331, .c 727, .c 3, .c 5, .c 59, .c 3, .c 7, .c 103, .c 3, .c 311, .c 17, .c 3, .c 13,
  .c 5, .c 3, .c 677, .c 11, .c 3,
]
private theorem h0136c29 : checkBlock 1121539 128 b0136c29 = true := by
  decide +kernel

private def b0136c30 : List Row := [
  .c 5, .c 31, .c 3, .c 41, .c 37, .c 3, .c 29, .c 13, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv479,pv1171], .c 149, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv17,pv6599],
  .p pv5 [pv2,pv3,pv15581], .c 3, .p pv2 [pv2,pv19,pv29,pv509], .p pv3 [pv2,pv3,pv181,pv1033],
  .c 3, .c 47, .c 5, .c 3, .c 463, .c 53, .c 3, .c 5, .c 11, .c 3, .c 13, .c 317, .c 3,
  .p pv2 [pv2,pv239,pv2347], .c 7, .c 3, .c 337, .c 5, .c 3, .c 11, .c 17, .c 3, .c 5, .c 13,
  .c 3, .c 673, .c 19, .c 3, .c 7, .p pv2 [pv2,pv3,pv17,pv647], .c 3, .c 433, .c 5, .c 3, .c 193,
  .c 7, .c 3, .c 5, .c 23, .c 3, .c 31, .c 11, .c 3, .c 599, .c 163, .c 3,
  .p pv2 [pv2,pv7,pv17,pv2357], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv23,pv271], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv26713], .c 3, .c 37, .c 7, .c 3, .c 53, .c 907, .c 3, .c 23, .c 5, .c 3,
  .c 19, .c 769, .c 3, .c 5, .c 113, .c 3, .c 7, .c 17, .c 3, .p pv2 [pv2,pv23,pv24391], .c 11,
  .c 3, .p pv3 [pv2,pv140249], .c 5, .c 3, .c 43, .p pv7 [pv2,pv3,pv5,pv11,pv17], .c 3, .c 5,
  .c 19, .c 3, .c 11, .c 71, .c 3, .c 13, .c 181, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv280507],
  .c 47, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv28051], .c 13, .c 3, .c 41, .c 67,
]
private theorem h0136c30 : checkBlock 1121795 128 b0136c30 = true := by
  decide +kernel

private def b0136c31 : List Row := [
  .c 3, .p pv2 [pv2,pv280513], .c 5, .c 3, .c 563, .c 227, .c 3, .c 5, .c 601, .c 3,
  .p pv11 [pv2,pv5,pv112207], .c 167, .c 3, .c 11, .c 7, .c 3, .c 19, .c 5, .c 3,
  .p pv3 [pv2,pv11,pv41,pv311], .p pv3 [pv2,pv3,pv5,pv113,pv331], .c 3, .c 5, .c 29, .c 3, .c 23,
  .p pv5 [pv2,pv3,pv17,pv19,pv193], .c 3, .c 7, .c 107, .c 3, .p pv3 [pv2,pv89,pv197], .c 5, .c 3,
  .c 17, .c 7, .c 3, .c 5, .c 277, .c 3, .p pv2 [pv2,pv5,pv112213], .p pv2 [pv2,pv3,pv11,pv8501],
  .c 3, .p pv3 [pv2,pv17,pv37,pv223], .p pv13 [pv2,pv3,pv31,pv2011], .c 3, .c 11, .c 5, .c 3,
  .c 7, .c 179, .c 3, .c 5, .p pv23 [pv2,pv3,pv7,pv61,pv73], .c 3, .c 199, .c 7, .c 3, .c 137,
  .c 31, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv19,pv29531], .p pv2 [pv2,pv3,pv5,pv59,pv317],
  .c 3, .c 5, .c 11, .c 3, .c 7, .c 23, .c 3, .c 19, .c 13, .c 3, .c 113, .c 5, .c 3, .c 11,
  .c 41, .c 3, .c 5, .c 61, .c 3, .c 17, .c 733, .c 3, .p pv2 [pv2,pv7,pv71,pv1129], .c 73, .c 3,
  .c 7, .c 5, .c 3, .c 23, .p pv41 [pv2,pv3,pv5,pv7,pv167], .c 3, .c 5, .c 7, .c 3, .c 13, .c 11,
  .c 3, .c 43, .p pv2 [pv2,pv3,pv187043], .c 3, .p pv5 [pv2,pv23,pv31,pv787], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv149,pv269], .c 29, .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv28057],
  .p pv2 [pv2,pv3,pv7,pv2969], .c 3, .p pv5 [pv2,pv11,pv139,pv367], .c 7, .c 3, .c 31, .c 5, .c 3,
  .c 127, .c 701, .c 3, .c 5,
]
private theorem h0136c31 : checkBlock 1122051 128 b0136c31 = true := by
  decide +kernel

def rows0136 : List Row :=
  b0136c00 ++ b0136c01 ++ b0136c02 ++ b0136c03 ++ b0136c04 ++ b0136c05 ++ b0136c06 ++ b0136c07 ++
  b0136c08 ++ b0136c09 ++ b0136c10 ++ b0136c11 ++ b0136c12 ++ b0136c13 ++ b0136c14 ++ b0136c15 ++
  b0136c16 ++ b0136c17 ++ b0136c18 ++ b0136c19 ++ b0136c20 ++ b0136c21 ++ b0136c22 ++ b0136c23 ++
  b0136c24 ++ b0136c25 ++ b0136c26 ++ b0136c27 ++ b0136c28 ++ b0136c29 ++ b0136c30 ++ b0136c31

theorem checked0136 : checkBlock 1114115 4096 rows0136 = true :=
  checkBlock_append h0136c00 (
    checkBlock_append h0136c01 (
    checkBlock_append h0136c02 (
    checkBlock_append h0136c03 (
    checkBlock_append h0136c04 (
    checkBlock_append h0136c05 (
    checkBlock_append h0136c06 (
    checkBlock_append h0136c07 (
    checkBlock_append h0136c08 (
    checkBlock_append h0136c09 (
    checkBlock_append h0136c10 (
    checkBlock_append h0136c11 (
    checkBlock_append h0136c12 (
    checkBlock_append h0136c13 (
    checkBlock_append h0136c14 (
    checkBlock_append h0136c15 (
    checkBlock_append h0136c16 (
    checkBlock_append h0136c17 (
    checkBlock_append h0136c18 (
    checkBlock_append h0136c19 (
    checkBlock_append h0136c20 (
    checkBlock_append h0136c21 (
    checkBlock_append h0136c22 (
    checkBlock_append h0136c23 (
    checkBlock_append h0136c24 (
    checkBlock_append h0136c25 (
    checkBlock_append h0136c26 (
    checkBlock_append h0136c27 (
    checkBlock_append h0136c28 (
    checkBlock_append h0136c29 (
    checkBlock_append h0136c30 (
    h0136c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
