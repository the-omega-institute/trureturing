/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks02/Block0227
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks02/Block0227.checked0227
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table135

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0227c00 : List Row := [
  .c 19, .c 3, .c 503, .c 283, .c 3, .c 31, .c 7, .c 3, .p pv2 [pv2,pv47,pv73,pv271], .c 5, .c 3,
  .p pv3 [pv2,pv232451], .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv587], .c 3, .c 43, .c 811,
  .c 3, .c 7, .p pv11 [pv2,pv3,pv31,pv4999], .c 3, .p pv3 [pv2,pv71,pv1637], .c 5, .c 3,
  .p pv11 [pv2,pv11,pv137,pv617], .c 7, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv13,pv2861],
  .p pv2 [pv2,pv3,pv67,pv257], .c 3, .c 37, .c 31, .c 3, .c 13, .c 5, .c 3, .c 7, .c 11, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv7,pv13,pv131], .c 3, .c 17, .c 7, .c 3, .p pv5 [pv2,pv929843], .c 13,
  .c 3, .c 11, .c 5, .c 3, .p pv7 [pv2,pv17,pv83,pv659], .c 19, .c 3, .c 5, .c 43, .c 3, .c 7,
  .c 101, .c 3, .c 53, .c 41, .c 3, .c 409, .c 5, .c 3, .c 743, .c 37, .c 3, .c 5, .c 11, .c 3,
  .c 13, .c 47, .c 3, .c 571, .c 17, .c 3, .c 7, .c 5, .c 3, .c 11, .c 1249, .c 3, .c 5, .c 7,
  .c 3, .p pv2 [pv2,pv5,pv11,pv29,pv53], .c 499, .c 3, .c 19, .p pv2 [pv2,pv3,pv277,pv373], .c 3,
  .c 17, .c 5, .c 3, .c 1153, .c 881, .c 3, .c 5, .c 241, .c 3, .c 41, .c 11, .c 3, .c 131, .c 7,
  .c 3, .p pv2 [pv2,pv464953], .c 5, .c 3, .c 13, .c 73, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv23,pv13477], .c 3, .p pv17 [pv2,pv5,pv7,pv163], .c 89, .c 3, .c 7, .c 317,
  .c 3,
]
private theorem h0227c00 : checkBlock 1859587 128 b0227c00 = true := by
  decide +kernel

private def b0227c01 : List Row := [
  .p pv2 [pv2,pv37,pv41,pv613], .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 29, .c 3, .c 1307,
  .p pv3 [pv2,pv3,pv309977], .c 3, .c 109, .c 11, .c 3, .c 271, .c 5, .c 3, .c 7,
  .p pv37 [pv2,pv3,pv5,pv11,pv1409], .c 3, .c 5, .c 1193, .c 3, .c 11, .c 7, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv239,pv1297], .c 3, .c 337, .c 5, .c 3, .c 257,
  .p pv7 [pv2,pv3,pv5,pv13,pv19,pv251], .c 3, .c 5, .p pv5 [pv2,pv3,pv37,pv59,pv71], .c 3, .c 7,
  .c 13, .c 3, .p pv5 [pv2,pv929963], .c 19, .c 3, .c 1061, .c 5, .c 3, .c 281, .c 23, .c 3, .c 5,
  .c 83, .c 3, .c 61, .c 17, .c 3, .c 11, .c 139, .c 3, .c 7, .c 5, .c 3, .c 31,
  .p pv11 [pv2,pv3,pv5,pv7,pv17,pv521], .c 3, .c 5, .c 7, .c 3, .c 107,
  .p pv3 [pv2,pv3,pv53,pv5849], .c 3, .c 17, .c 179, .c 3, .c 163, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv132857], .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv41,pv7561], .c 3, .c 89,
  .p pv29 [pv2,pv3,pv7,pv11,pv61], .c 3, .p pv3 [pv2,pv101,pv1151], .c 7, .c 3, .c 11, .c 5, .c 3,
  .c 1187, .c 29, .c 3, .c 5, .p pv5 [pv2,pv3,pv155003], .c 3, .c 1231, .c 19, .c 3, .c 7, .c 137,
  .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv71,pv13099], .c 7, .c 3, .c 5, .c 11, .c 3,
  .p pv11 [pv2,pv5,pv186007], .c 61, .c 3, .c 103, .c 13, .c 3, .p pv2 [pv2,pv7,pv132863], .c 5,
  .c 3, .c 7, .c 311, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv173],
]
private theorem h0227c01 : checkBlock 1859843 128 b0227c01 = true := by
  decide +kernel

private def b0227c02 : List Row := [
  .c 3, .c 37, .c 7, .c 3, .c 991, .p pv2 [pv2,pv3,pv155009], .c 3, .c 73, .c 5, .c 3, .c 19,
  .c 67, .c 3, .c 5, .p pv3 [pv2,pv3,pv310021], .c 3, .c 7, .c 11, .c 3, .c 43,
  .p pv19 [pv2,pv3,pv7,pv19,pv37], .c 3, .p pv5 [pv2,pv930071], .c 5, .c 3, .c 191, .c 373, .c 3,
  .c 5, .c 13, .c 3, .c 251, .p pv2 [pv2,pv3,pv310027], .c 3, .c 229, .c 97, .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv930089], .p pv17 [pv2,pv3,pv5,pv7,pv43,pv103], .c 3, .c 5, .c 7, .c 3,
  .c 17, .p pv5 [pv2,pv3,pv2153], .c 3, .p pv2 [pv2,pv13,pv83,pv431], .c 11, .c 3, .c 587, .c 5,
  .c 3, .c 13, .c 41, .c 3, .c 5, .c 23, .c 3, .c 11, .c 43, .c 3, .c 751, .c 7, .c 3, .c 19,
  .c 5, .c 3, .c 401, .c 593, .c 3, .c 5, .c 53, .c 3, .p pv2 [pv2,pv5,pv7,pv1063],
  .p pv2 [pv2,pv3,pv19,pv41,pv199], .c 3, .c 7, .c 17, .c 3, .c 23, .c 5, .c 3, .c 173, .c 7,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv17,pv829], .c 3, .p pv7 [pv2,pv5,pv46507], .c 103, .c 3,
  .c 11, .p pv11 [pv2,pv3,pv9689], .c 3, .c 17, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv13,pv53],
  .c 3, .c 5, .c 47, .c 3, .c 523, .c 7, .c 3, .c 61, .c 101, .c 3, .c 37, .c 5, .c 3, .c 59,
  .c 11, .c 3, .c 5, .p pv7 [pv2,pv3,pv12919], .c 3, .c 7, .p pv11 [pv2,pv3,pv11,pv71,pv397],
  .c 3, .c 19, .c 1201, .c 3, .c 11,
]
private theorem h0227c02 : checkBlock 1860099 128 b0227c02 = true := by
  decide +kernel

private def b0227c03 : List Row := [
  .c 5, .c 3, .p pv7 [pv2,pv930179], .c 17, .c 3, .c 5, .c 89, .c 3, .c 79,
  .p pv2 [pv2,pv3,pv31,pv1667], .c 3, .p pv3 [pv2,pv7,pv139,pv239], .c 29, .c 3, .c 7, .c 5, .c 3,
  .c 67, .c 13, .c 3, .c 5, .c 7, .c 3, .c 23, .c 31, .c 3, .p pv5 [pv2,pv53,pv17551], .c 107,
  .c 3, .c 71, .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv101,pv307], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv103357], .c 3, .p pv11 [pv2,pv5,pv11,pv13,pv1301], .c 1033, .c 3, .c 29, .c 7,
  .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv47,pv1237], .c 199, .c 3, .c 5, .c 41, .c 3, .c 19,
  .c 11, .c 3, .c 7, .c 13, .c 3, .c 317, .c 5, .c 3, .p pv11 [pv2,pv73,pv12743], .c 7, .c 3,
  .c 5, .c 1361, .c 3, .c 521, .c 23, .c 3, .c 17, .c 19, .c 3, .p pv5 [pv2,pv7,pv132893], .c 5,
  .c 3, .c 7, .c 379, .c 3, .c 5, .p pv31 [pv2,pv3,pv7,pv23,pv107], .c 3, .c 13, .c 7, .c 3,
  .c 31, .c 11, .c 3, .p pv2 [pv2,pv465133], .c 5, .c 3, .c 23, .c 409, .c 3, .c 5, .c 13, .c 3,
  .c 7, .c 29, .c 3, .c 97, .p pv17 [pv2,pv3,pv7,pv31,pv1429], .c 3, .c 149, .c 5, .c 3,
  .p pv3 [pv2,pv232571], .p pv11 [pv2,pv3,pv5,pv2297], .c 3, .c 5, .c 337, .c 3,
  .p pv3 [pv2,pv5,pv41,pv2269], .p pv5 [pv2,pv3,pv17,pv29,pv37], .c 3, .c 389, .c 31, .c 3, .c 7,
  .c 5, .c 3, .c 13, .c 433, .c 3, .c 5, .c 7, .c 3,
]
private theorem h0227c03 : checkBlock 1860355 128 b0227c03 = true := by
  decide +kernel

private def b0227c04 : List Row := [
  .c 29, .c 19, .c 3, .c 11, .c 37, .c 3, .c 107, .c 5, .c 3, .p pv2 [pv2,pv7,pv11,pv863], .c 23,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv47,pv3299], .c 3, .p pv11 [pv2,pv5,pv29,pv401],
  .p pv2 [pv2,pv3,pv7,pv14767], .c 3, .p pv5 [pv2,pv930323], .c 7, .c 3, .c 43, .c 5, .c 3,
  .p pv2 [pv2,pv113,pv8233], .c 11, .c 3, .c 5, .c 17, .c 3, .c 53, .c 269, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv34457], .c 3, .c 11, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 71, .c 3, .c 17,
  .c 13, .c 3, .p pv2 [pv2,pv757,pv1229], .p pv2 [pv2,pv3,pv19,pv8161], .c 3, .c 31, .c 5, .c 3,
  .c 7, .p pv13 [pv2,pv3,pv5,pv7753], .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv37,pv47,pv107],
  .c 7, .c 3, .p pv3 [pv2,pv14537], .c 43, .c 3, .p pv5 [pv2,pv13,pv59,pv1213], .c 5, .c 3, .c 11,
  .c 97, .c 3, .c 5, .p pv2 [pv2,pv3,pv29,pv5347], .c 3, .c 7, .p pv2 [pv2,pv3,pv310127], .c 3,
  .c 37, .c 17, .c 3, .c 151, .c 5, .c 3, .c 419, .c 13, .c 3, .c 5, .c 929, .c 3, .c 67, .c 11,
  .c 3, .c 463, .p pv3 [pv2,pv3,pv103,pv3011], .c 3, .c 7, .c 5, .c 3, .c 211, .c 1123, .c 3,
  .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv13,pv17,pv421], .c 641, .c 3, .c 487,
  .p pv2 [pv2,pv3,pv155069], .c 3, .c 13, .c 5, .c 3, .c 71, .c 19, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv23857], .c 3, .p pv2 [pv2,pv5,pv37217], .p pv2 [pv2,pv3,pv7,pv22153],
  .c 3, .p pv3 [pv2,pv232607], .c 7, .c 3, .c 691, .c 5,
]
private theorem h0227c04 : checkBlock 1860611 128 b0227c04 = true := by
  decide +kernel

private def b0227c05 : List Row := [
  .c 3, .p pv2 [pv2,pv31,pv43,pv349], .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv51691], .c 3, .c 11,
  .c 53, .c 3, .c 7, .c 571, .c 3, .p pv2 [pv2,pv11,pv42293], .c 5, .c 3, .c 31, .c 7, .c 3, .c 5,
  .c 23, .c 3, .c 13, .c 191, .c 3, .c 19, .c 59, .c 3, .p pv2 [pv2,pv7,pv17,pv1117], .c 5, .c 3,
  .c 7, .c 127, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv93047], .c 7, .c 3, .c 11, .c 41, .c 3,
  .c 23, .c 5, .c 3, .c 29, .c 31, .c 3, .c 5, .p pv3 [pv2,pv3,pv103387], .c 3, .c 7, .c 17, .c 3,
  .p pv3 [pv2,pv13,pv23,pv389], .p pv19 [pv2,pv3,pv7,pv59,pv751], .c 3, .p pv5 [pv2,pv930491],
  .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 43, .c 3, .p pv3 [pv2,pv5,pv1861], .c 79, .c 3, .c 17,
  .p pv23 [pv2,pv3,pv137,pv283], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv930509],
  .p pv2 [pv2,pv3,pv5,pv7,pv211], .c 3, .c 5, .c 7, .c 3, .c 19, .p pv5 [pv2,pv3,pv77543], .c 3,
  .c 59, .p pv3 [pv2,pv3,pv103391], .c 3, .c 443, .c 5, .c 3, .c 61, .c 107, .c 3, .c 5, .c 11,
  .c 3, .p pv2 [pv2,pv5,pv93053], .c 37, .c 3, .c 13, .c 7, .c 3, .c 677, .c 5, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv5,pv13,pv1193], .c 3, .c 5, .c 733, .c 3, .c 23, .c 13, .c 3, .c 7, .c 193,
  .c 3, .p pv5 [pv2,pv930551], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 131, .c 3,
  .p pv3 [pv2,pv5,pv727],
]
private theorem h0227c05 : checkBlock 1860867 128 b0227c05 = true := by
  decide +kernel

private def b0227c06 : List Row := [
  .c 11, .c 3, .c 101, .c 1069, .c 3, .c 29, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv31019], .c 3,
  .c 5, .c 31, .c 3, .p pv13 [pv2,pv5,pv37223], .c 7, .c 3, .p pv2 [pv2,pv11,pv42299], .c 149,
  .c 3, .c 277, .c 5, .c 3, .c 43, .c 13, .c 3, .c 5, .c 17, .c 3, .c 7, .c 19, .c 3,
  .p pv2 [pv2,pv930593], .c 11, .c 3, .c 67, .c 5, .c 3, .c 569, .c 53, .c 3, .c 5, .c 821, .c 3,
  .c 11, .c 331, .c 3, .c 349, .p pv2 [pv2,pv3,pv11489], .c 3, .c 7, .c 5, .c 3, .c 23, .c 211,
  .c 3, .c 5, .c 7, .c 3, .c 421, .c 241, .c 3, .c 47, .c 13, .c 3, .p pv2 [pv2,pv23,pv20231],
  .c 5, .c 3, .c 19, .p pv11 [pv2,pv3,pv5,pv67,pv463], .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv28201],
  .c 3, .c 31, .c 59, .c 3, .c 11, .c 7, .c 3, .c 1021, .c 5, .c 3, .c 1321, .c 283, .c 3, .c 5,
  .c 19, .c 3, .c 13, .p pv3 [pv2,pv3,pv31,pv10007], .c 3, .c 7, .p pv11 [pv2,pv3,pv149,pv347],
  .c 3, .c 17, .c 5, .c 3, .c 79, .c 7, .c 3, .c 5, .c 13, .c 3, .p pv41 [pv2,pv5,pv17,pv10949],
  .c 31, .c 3, .p pv3 [pv2,pv29,pv71,pv113], .p pv2 [pv2,pv3,pv310223], .c 3, .c 11, .c 5, .c 3,
  .c 7, .p pv3 [pv2,pv3,pv5,pv12409], .c 3, .c 5, .c 523, .c 3, .c 457, .c 7, .c 3, .c 23, .c 353,
  .c 3, .c 19, .c 5, .c 3,
]
private theorem h0227c06 : checkBlock 1861123 128 b0227c06 = true := by
  decide +kernel

private def b0227c07 : List Row := [
  .c 13, .c 17, .c 3, .c 5, .c 11, .c 3, .c 7, .c 109, .c 3, .p pv2 [pv2,pv37,pv12577], .c 997,
  .c 3, .p pv2 [pv2,pv577,pv1613], .c 5, .c 3, .c 11, .c 19, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv103,pv251], .c 3, .c 179, .c 29, .c 3, .c 43, .c 293, .c 3, .c 7, .c 5, .c 3,
  .c 127, .c 41, .c 3, .c 5, .c 7, .c 3, .c 257, .c 11, .c 3, .c 13, .c 23, .c 3, .c 757, .c 5,
  .c 3, .p pv2 [pv2,pv7,pv19,pv3499], .p pv17 [pv2,pv3,pv5,pv13,pv37,pv43], .c 3, .c 5, .c 79,
  .c 3, .c 29, .c 13, .c 3, .c 19, .c 7, .c 3, .p pv2 [pv2,pv465373], .c 5, .c 3, .c 271,
  .p pv2 [pv2,pv3,pv5,pv17,pv73], .c 3, .c 5, .c 37, .c 3, .p pv7 [pv2,pv5,pv7,pv29,pv131], .c 43,
  .c 3, .c 7, .c 11, .c 3, .c 41, .c 5, .c 3, .c 47, .c 7, .c 3, .c 5, .c 61, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv11491], .c 3, .p pv2 [pv2,pv930773], .c 71, .c 3, .c 881, .c 5, .c 3, .c 7,
  .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv127,pv349], .c 3, .c 239, .c 7, .c 3, .c 827,
  .p pv2 [pv2,pv3,pv103421], .c 3, .p pv5 [pv2,pv19,pv48989], .c 5, .c 3,
  .p pv2 [pv2,pv337,pv1381], .p pv19 [pv2,pv3,pv5,pv62053], .c 3, .c 5, .c 23, .c 3, .c 7, .c 503,
  .c 3, .c 11, .c 1097, .c 3, .c 13, .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv19,pv23,pv71], .c 3,
  .c 5, .c 59, .c 3, .p pv7 [pv2,pv5,pv186163], .c 1283,
]
private theorem h0227c07 : checkBlock 1861379 128 b0227c07 = true := by
  decide +kernel

private def b0227c08 : List Row := [
  .c 3, .p pv2 [pv2,pv7,pv17,pv3911], .c 13, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv307,pv379],
  .c 11, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv93083], .p pv3 [pv2,pv3,pv11,pv67,pv421], .c 3,
  .c 251, .c 607, .c 3, .c 11, .c 5, .c 3, .c 151, .c 613, .c 3, .c 5, .c 17, .c 3, .c 13, .c 107,
  .c 3, .p pv3 [pv2,pv19,pv1531], .c 7, .c 3, .c 653, .c 5, .c 3, .p pv2 [pv2,pv257,pv1811],
  .p pv11 [pv2,pv3,pv5,pv62057], .c 3, .c 5, .c 11, .c 3, .c 17, .c 463, .c 3, .c 7, .c 37, .c 3,
  .c 101, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv310291], .c 3,
  .p pv13 [pv2,pv5,pv11,pv677], .c 19, .c 3, .p pv2 [pv2,pv13,pv35803],
  .p pv3 [pv2,pv3,pv23,pv1499], .c 3, .c 383, .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .c 263, .c 3,
  .c 23, .c 7, .c 3, .p pv2 [pv2,pv163,pv5711], .c 17, .c 3, .c 79, .c 5, .c 3, .c 439, .c 487,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv17,pv18253], .c 3, .c 7, .c 887, .c 3, .p pv5 [pv2,pv11,pv21157],
  .c 937, .c 3, .c 17, .c 5, .c 3, .c 19, .p pv11 [pv2,pv3,pv5,pv137,pv151], .c 3, .c 5, .c 53,
  .c 3, .c 563, .c 401, .c 3, .c 13, .c 11, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv29,pv47,pv683],
  .p pv2 [pv2,pv3,pv5,pv7,pv11,pv13,pv31], .c 3, .c 5, .c 7, .c 3, .c 11, .c 13, .c 3, .c 37,
  .p pv3 [pv2,pv3,pv310313], .c 3, .c 167, .c 5, .c 3, .p pv3 [pv2,pv7,pv1039],
]
private theorem h0227c08 : checkBlock 1861635 128 b0227c08 = true := by
  decide +kernel

private def b0227c09 : List Row := [
  .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv23,pv3373], .c 3, .c 113, .c 61, .c 3, .c 107, .c 7, .c 3,
  .p pv3 [pv2,pv13,pv17903], .c 5, .c 3, .c 23, .p pv7 [pv2,pv3,pv5,pv431], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv28211], .c 3, .c 103, .c 41, .c 3, .c 7, .c 83, .c 3, .c 19, .c 5, .c 3,
  .c 163, .c 7, .c 3, .c 5, .c 311, .c 3, .p pv7 [pv2,pv5,pv46549], .c 1163, .c 3, .c 137, .c 89,
  .c 3, .p pv2 [pv2,pv7,pv66499], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 1303, .c 3,
  .p pv29 [pv2,pv5,pv13,pv14323], .c 7, .c 3, .c 67, .c 47, .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv232751], .c 23, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv373], .c 3, .c 7,
  .p pv5 [pv2,pv3,pv83,pv3739], .c 3, .c 17, .c 13, .c 3, .p pv3 [pv2,pv29,pv4013], .c 5, .c 3,
  .c 1117, .c 271, .c 3, .c 5, .c 11, .c 3, .c 557, .c 149, .c 3, .c 19, .c 191, .c 3, .c 7, .c 5,
  .c 3, .c 11, .c 907, .c 3, .c 5, .c 7, .c 3, .c 13, .c 421, .c 3, .p pv5 [pv2,pv61,pv15263],
  .c 991, .c 3, .c 47, .c 5, .c 3, .c 37, .p pv2 [pv2,pv3,pv5,pv2069], .c 3, .c 5, .c 13, .c 3,
  .p pv11 [pv2,pv5,pv186211], .c 11, .c 3, .c 71, .c 7, .c 3, .p pv2 [pv2,pv541,pv1721], .c 5,
  .c 3, .c 17, .c 67, .c 3, .c 5, .c 101, .c 3, .p pv2 [pv2,pv5,pv7,pv47,pv283], .c 389, .c 3,
]
private theorem h0227c09 : checkBlock 1861891 128 b0227c09 = true := by
  decide +kernel

private def b0227c10 : List Row := [
  .c 7, .c 23, .c 3, .p pv3 [pv2,pv19,pv12251], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 761, .c 3,
  .c 19, .c 37, .c 3, .c 29, .c 11, .c 3, .c 139, .c 5, .c 3, .c 7, .c 673, .c 3, .c 5, .c 17,
  .c 3, .c 11, .c 7, .c 3, .c 241, .c 19, .c 3, .p pv2 [pv2,pv11,pv42323], .c 5, .c 3,
  .p pv2 [pv2,pv23,pv40483], .p pv2 [pv2,pv3,pv5,pv41,pv757], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv103457], .c 3, .c 7, .p pv5 [pv2,pv3,pv31,pv2503], .c 3, .c 13, .c 941, .c 3,
  .p pv2 [pv2,pv199,pv4679], .c 5, .c 3, .p pv3 [pv2,pv17,pv13693],
  .p pv2 [pv2,pv3,pv5,pv13,pv191], .c 3, .c 5, .c 193, .c 3, .c 41, .c 13, .c 3, .c 11, .c 61,
  .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv11,pv84649], .c 47, .c 3, .c 5, .c 7, .c 3, .c 599,
  .c 29, .c 3, .p pv3 [pv2,pv131,pv1777], .c 17, .c 3, .c 73, .c 5, .c 3, .c 181, .c 11, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv17,pv179], .c 3, .c 37, .c 19, .c 3, .c 397, .c 7, .c 3, .c 11, .c 5,
  .c 3, .c 101, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv79,pv3929], .c 3, .c 29, .c 113, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv37,pv8389], .c 3, .c 491, .c 5, .c 3, .c 233, .c 7, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv13,pv19,pv29], .p pv5 [pv2,pv3,pv310397], .c 3, .c 31, .c 373, .c 3, .c 13,
  .c 5, .c 3, .c 7, .c 17,
]
private theorem h0227c10 : checkBlock 1862147 128 b0227c10 = true := by
  decide +kernel

private def b0227c11 : List Row := [
  .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv13,pv379], .c 3, .p pv17 [pv2,pv5,pv11,pv16931], .c 7, .c 3,
  .p pv3 [pv2,pv43,pv2707], .c 13, .c 3, .c 283, .c 5, .c 3, .p pv2 [pv2,pv353,pv1319], .c 509,
  .c 3, .c 5, .c 19, .c 3, .c 7, .c 11, .c 3, .p pv5 [pv2,pv103,pv9041], .c 31, .c 3, .c 59, .c 5,
  .c 3, .c 43, .c 139, .c 3, .c 5, .c 29, .c 3, .c 13, .c 53, .c 3, .p pv3 [pv2,pv7,pv11,pv6047],
  .c 257, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv232811], .c 157, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv149], .c 17, .c 3, .c 41, .c 11, .c 3, .c 19, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv173,pv769], .p pv7 [pv2,pv3,pv5,pv11,pv17,pv83], .c 3, .c 5, .c 239, .c 3,
  .c 11, .c 67, .c 3, .c 17, .c 7, .c 3, .c 37, .c 5, .c 3, .c 13, .c 19, .c 3, .c 5, .c 701,
  .c 3, .p pv3 [pv2,pv5,pv7,pv1663], .c 23, .c 3, .c 7, .c 307, .c 3, .c 31, .c 5, .c 3, .c 53,
  .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv23,pv409], .c 3, .p pv11 [pv2,pv5,pv186259],
  .p pv5 [pv2,pv3,pv89,pv109], .c 3, .c 11, .c 337, .c 3, .c 83, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv47,pv1321], .c 3, .c 5, .c 37, .c 3, .p pv2 [pv2,pv5,pv93131], .c 7, .c 3,
  .c 13, .c 1223, .c 3, .p pv3 [pv2,pv23,pv53,pv191], .c 5, .c 3, .c 17, .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv19,pv16339], .c 3, .c 7, .c 13, .c 3, .c 47,
]
private theorem h0227c11 : checkBlock 1862403 128 b0227c11 = true := by
  decide +kernel

private def b0227c12 : List Row := [
  .p pv2 [pv2,pv3,pv7,pv14783], .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv73,pv6379], .c 41, .c 3,
  .c 5, .c 439, .c 3, .c 89, .p pv5 [pv2,pv3,pv310447], .c 3, .p pv17 [pv2,pv7,pv83,pv229], .c 59,
  .c 3, .c 7, .c 5, .c 3, .c 29, .c 23, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv186271], .c 647,
  .c 3, .c 43, .c 223, .c 3, .c 617, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5,
  .p pv43 [pv2,pv3,pv151,pv257], .c 3, .c 17, .c 101, .c 3, .c 23, .c 7, .c 3, .c 41, .c 5, .c 3,
  .c 31, .p pv7 [pv2,pv3,pv5,pv19,pv43], .c 3, .c 5, .c 499, .c 3, .c 643, .c 11, .c 3, .c 7,
  .c 19, .c 3, .c 13, .c 5, .c 3, .c 137, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv11941], .c 3,
  .c 67, .c 43, .c 3, .c 59, .c 13, .c 3, .c 919, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5, .c 71,
  .c 3, .c 479, .c 7, .c 3, .p pv2 [pv2,pv19,pv127,pv193], .c 11, .c 3, .c 17, .c 5, .c 3, .c 821,
  .c 359, .c 3, .c 5, .p pv5 [pv2,pv3,pv25873], .c 3, .c 7, .c 467, .c 3, .c 811,
  .p pv2 [pv2,pv3,pv7,pv67,pv331], .c 3, .c 29, .c 5, .c 3, .c 61, .p pv7 [pv2,pv3,pv5,pv3881],
  .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv311,pv599], .c 19, .c 3, .c 53, .c 79, .c 3, .c 7,
  .c 5, .c 3, .p pv2 [pv2,pv23,pv20249], .c 17, .c 3,
]
private theorem h0227c12 : checkBlock 1862659 128 b0227c12 = true := by
  decide +kernel

private def b0227c13 : List Row := [
  .c 5, .c 7, .c 3, .c 389, .p pv2 [pv2,pv3,pv251,pv1237], .c 3, .c 11, .c 719, .c 3,
  .p pv2 [pv2,pv43,pv10831], .c 5, .c 3, .c 13, .p pv7 [pv2,pv3,pv5,pv61,pv509], .c 3, .c 5,
  .c 149, .c 3, .c 131, .p pv23 [pv2,pv3,pv7,pv13,pv853], .c 3, .p pv2 [pv2,pv465739], .c 7, .c 3,
  .c 127, .c 5, .c 3, .c 19, .c 11, .c 3, .c 5, .c 23, .c 3, .p pv11 [pv2,pv5,pv7,pv1901],
  .p pv5 [pv2,pv3,pv11,pv97], .c 3, .c 7, .c 29, .c 3, .c 11, .c 5, .c 3, .c 41, .c 7, .c 3, .c 5,
  .c 19, .c 3, .p pv2 [pv2,pv5,pv186301], .c 17, .c 3, .c 13, .c 739, .c 3, .c 23, .c 5, .c 3,
  .c 7, .c 113, .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv41,pv71], .c 7, .c 3, .c 17,
  .p pv7 [pv2,pv3,pv11,pv7057], .c 3, .p pv2 [pv2,pv167,pv2789], .c 5, .c 3, .c 11, .c 37, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv310511], .c 3, .c 7, .p pv5 [pv2,pv3,pv6469], .c 3,
  .p pv2 [pv2,pv29,pv16061], .c 97, .c 3, .c 19, .c 5, .c 3, .p pv3 [pv2,pv116443],
  .p pv3 [pv2,pv3,pv5,pv127,pv163], .c 3, .c 5, .p pv5 [pv2,pv3,pv149,pv521], .c 3, .c 83, .c 11,
  .c 3, .p pv2 [pv2,pv7,pv73,pv1823], .c 53, .c 3, .c 7, .c 5, .c 3, .c 157, .c 13, .c 3, .c 5,
  .c 7, .c 3, .c 31, .c 577, .c 3, .c 109, .c 977, .c 3, .c 1277, .c 5, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv5,pv12421], .c 3, .c 5, .p pv2 [pv2,pv3,pv139,pv1117], .c 3, .c 23, .c 29,
  .c 3, .c 103, .c 7,
]
private theorem h0227c13 : checkBlock 1862915 128 b0227c13 = true := by
  decide +kernel

private def b0227c14 : List Row := [
  .c 3, .c 13, .c 5, .c 3, .c 73, .p pv23 [pv2,pv3,pv5,pv11,pv941], .c 3, .c 5, .c 293, .c 3,
  .c 11, .c 31, .c 3, .c 7, .c 13, .c 3, .c 67, .c 5, .c 3, .c 37, .c 7, .c 3, .c 5, .c 17, .c 3,
  .c 29, .p pv3 [pv2,pv3,pv193,pv1609], .c 3, .c 1217, .p pv2 [pv2,pv3,pv155269], .c 3, .c 43,
  .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv15527], .c 3, .c 5,
  .p pv29 [pv2,pv3,pv7,pv11,pv37,pv109], .c 3, .c 13, .c 7, .c 3, .c 11, .c 367, .c 3,
  .p pv5 [pv2,pv487,pv1913], .c 5, .c 3, .p pv2 [pv2,pv11,pv17,pv47,pv53],
  .p pv11 [pv2,pv3,pv5,pv67,pv103], .c 3, .c 5, .c 13, .c 3, .c 7, .c 37, .c 3, .c 769, .c 313,
  .c 3, .c 419, .c 5, .c 3, .c 23, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv61,pv1697], .c 3, .c 19,
  .p pv5 [pv2,pv3,pv11,pv3529], .c 3, .c 31, .c 17, .c 3, .c 7, .c 5, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv5,pv7,pv19,pv467], .c 3, .c 5, .c 7, .c 3, .c 211, .c 631, .c 3,
  .p pv2 [pv2,pv421,pv2213], .c 19, .c 3, .c 17, .c 5, .c 3, .c 661, .p pv19 [pv2,pv3,pv5,pv647],
  .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv17,pv97,pv113], .c 79, .c 3, .p pv3 [pv2,pv116461],
  .c 7, .c 3, .c 173, .c 5, .c 3, .c 11, .c 23, .c 3, .c 5, .c 59, .c 3,
  .p pv13 [pv2,pv5,pv7,pv11], .p pv2 [pv2,pv3,pv310567], .c 3, .c 7, .c 41, .c 3,
  .p pv2 [pv2,pv241,pv1933], .c 5, .c 3, .c 839, .c 7, .c 3, .c 5,
]
private theorem h0227c14 : checkBlock 1863171 128 b0227c14 = true := by
  decide +kernel

private def b0227c15 : List Row := [
  .c 53, .c 3, .c 37, .c 11, .c 3, .c 23, .c 1063, .c 3, .c 227, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv41,pv101], .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv47,pv59], .c 3,
  .p pv2 [pv2,pv5,pv23,pv4051], .c 7, .c 3, .c 97, .c 1151, .c 3, .p pv3 [pv2,pv13,pv17,pv31],
  .c 5, .c 3, .p pv7 [pv2,pv931739], .p pv19 [pv2,pv3,pv5,pv53,pv293], .c 3, .c 5, .c 353, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv155291], .c 3, .p pv3 [pv2,pv232937], .c 11, .c 3, .c 31, .c 5, .c 3,
  .p pv2 [pv2,pv373,pv1249], .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv83,pv1871], .c 3, .c 11, .c 17,
  .c 3, .p pv5 [pv2,pv7,pv133109], .c 23, .c 3, .c 7, .c 5, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv5,pv7,pv17,pv29], .c 3, .c 5, .c 7, .c 3, .c 101, .c 167, .c 3, .c 17,
  .p pv11 [pv2,pv3,pv19,pv5449], .c 3, .c 13, .c 5, .c 3, .c 29, .c 89, .c 3, .c 5, .c 19, .c 3,
  .p pv2 [pv2,pv5,pv93179], .p pv3 [pv2,pv3,pv7,pv44371], .c 3, .c 11, .c 7, .c 3,
  .p pv3 [pv2,pv281,pv829], .c 5, .c 3, .c 83, .p pv7 [pv2,pv3,pv5,pv1553], .c 3, .c 5,
  .p pv11 [pv2,pv3,pv131,pv2371], .c 3, .c 61, .p pv2 [pv2,pv3,pv51767], .c 3, .c 7, .c 107, .c 3,
  .c 1009, .c 5, .c 3, .c 547, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv155303], .c 3, .c 13, .c 317,
  .c 3, .p pv5 [pv2,pv457,pv2039], .p pv11 [pv2,pv3,pv719], .c 3, .c 11, .c 5, .c 3, .c 7, .c 97,
  .c 3, .c 5, .c 13, .c 3, .p pv23 [pv2,pv5,pv227,pv821], .c 7, .c 3, .p pv2 [pv2,pv17,pv27407],
  .c 71, .c 3,
]
private theorem h0227c15 : checkBlock 1863427 128 b0227c15 = true := by
  decide +kernel

private def b0227c16 : List Row := [
  .p pv2 [pv2,pv83,pv103,pv109], .c 5, .c 3, .c 31, .c 19, .c 3, .c 5, .c 11, .c 3, .c 7, .c 773,
  .c 3, .p pv2 [pv2,pv13,pv43,pv1667], .c 113, .c 3, .c 23, .c 5, .c 3, .c 11,
  .p pv13 [pv2,pv3,pv5,pv31,pv167], .c 3, .c 5, .c 17, .c 3, .p pv7 [pv2,pv5,pv11,pv16943], .c 61,
  .c 3, .c 41, .c 67, .c 3, .c 7, .c 5, .c 3, .c 43, .c 31, .c 3, .c 5, .c 7, .c 3, .c 17, .c 11,
  .c 3, .c 19, .p pv11 [pv2,pv3,pv79,pv983], .c 3, .c 293, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv17,pv41,pv191], .c 677, .c 3, .c 5, .p pv2 [pv2,pv3,pv19,pv16349], .c 3,
  .c 109, .c 151, .c 3, .c 13, .c 7, .c 3, .c 1097, .c 5, .c 3, .c 619,
  .p pv2 [pv2,pv3,pv5,pv13,pv59], .c 3, .c 5, .c 197, .c 3, .c 71, .c 13, .c 3, .c 7, .c 11, .c 3,
  .c 107, .c 5, .c 3, .p pv17 [pv2,pv37,pv89,pv283], .c 7, .c 3, .c 5, .c 79, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv127,pv1223], .c 3, .p pv3 [pv2,pv116491], .c 29, .c 3, .c 17, .c 5, .c 3,
  .c 7, .p pv29 [pv2,pv3,pv5,pv62129], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv22189], .c 3, .c 19,
  .c 7, .c 3, .c 167, .p pv7 [pv2,pv3,pv13,pv29,pv103], .c 3, .p pv2 [pv2,pv71,pv6563], .c 5,
  .c 3, .p pv2 [pv2,pv931949], .c 13, .c 3, .c 5, .c 683, .c 3, .c 7,
  .p pv41 [pv2,pv3,pv37,pv2099], .c 3, .c 11, .c 19, .c 3, .p pv2 [pv2,pv379,pv2459], .c 5, .c 3,
  .p pv3 [pv2,pv11,pv59,pv359], .c 17, .c 3, .c 5, .c 31,
]
private theorem h0227c16 : checkBlock 1863683 128 b0227c16 = true := by
  decide +kernel

private def b0227c17 : List Row := [
  .c 3, .p pv3 [pv2,pv5,pv13,pv67,pv107], .c 23, .c 3, .c 337, .c 37, .c 3, .c 7, .c 5, .c 3,
  .c 701, .c 11, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv186397], .c 47, .c 3, .c 61, .c 13,
  .c 3, .c 11, .c 5, .c 3, .c 23, .c 103, .c 3, .c 5, .p pv5 [pv2,pv3,pv155333], .c 3,
  .p pv3 [pv2,pv5,pv233], .p pv2 [pv2,pv3,pv7,pv44381], .c 3, .c 43, .c 7, .c 3, .c 883, .c 5,
  .c 3, .c 733, .c 257, .c 3, .c 5, .c 11, .c 3, .c 13, .c 17, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv11,pv61,pv463], .c 3, .p pv2 [pv2,pv932021], .c 5, .c 3, .c 11, .c 7, .c 3,
  .c 5, .c 13, .c 3, .c 31, .c 53, .c 3, .c 17, .p pv2 [pv2,pv3,pv163,pv953], .c 3, .c 1049, .c 5,
  .c 3, .c 7, .c 23, .c 3, .c 5, .p pv11 [pv2,pv3,pv7,pv44383], .c 3, .c 29, .c 7, .c 3, .c 37,
  .c 61, .c 3, .c 457, .c 5, .c 3, .c 13, .p pv31 [pv2,pv3,pv5,pv62137], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv53,pv977], .c 3, .c 7, .c 31, .c 3, .c 23, .c 139, .c 3, .c 613, .c 5, .c 3,
  .c 149, .c 67, .c 3, .c 5, .c 19, .c 3, .p pv11 [pv2,pv5,pv23,pv1621],
  .p pv5 [pv2,pv3,pv17,pv1523], .c 3, .c 101, .c 11, .c 3, .c 7, .c 5, .c 3, .c 17, .c 37, .c 3,
  .c 5, .c 7, .c 3, .c 11, .c 797, .c 3, .c 13, .p pv17 [pv2,pv3,pv41,pv421], .c 3, .c 353,
]
private theorem h0227c17 : checkBlock 1863939 128 b0227c17 = true := by
  decide +kernel

private def b0227c18 : List Row := [
  .c 5, .c 3, .c 1283, .c 73, .c 3, .c 5, .c 29, .c 3, .c 197, .c 13, .c 3,
  .p pv3 [pv2,pv31,pv7517], .c 7, .c 3, .c 19, .c 5, .c 3, .c 41, .c 163, .c 3, .c 5, .c 17, .c 3,
  .p pv13 [pv2,pv5,pv7,pv3329], .c 97, .c 3, .c 7, .c 401, .c 3, .p pv2 [pv2,pv13,pv35851], .c 5,
  .c 3, .p pv2 [pv2,pv11,pv101,pv839], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv310711], .c 3, .c 17,
  .c 1117, .c 3, .c 317, .c 557, .c 3, .c 89, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv137], .c 3, .c 379, .c 7, .c 3, .p pv2 [pv2,pv932153], .c 31, .c 3, .c 11,
  .c 5, .c 3, .c 37, .c 79, .c 3, .c 5, .c 491, .c 3, .c 7, .c 1301, .c 3, .c 19, .c 17, .c 3,
  .c 13, .c 5, .c 3, .c 47, .c 43, .c 3, .c 5, .c 11, .c 3, .p pv13 [pv2,pv5,pv127,pv367],
  .p pv2 [pv2,pv3,pv310727], .c 3, .c 719, .c 13, .c 3, .c 7, .c 5, .c 3, .c 11, .c 29, .c 3,
  .c 5, .c 7, .c 3, .p pv29 [pv2,pv5,pv11,pv17,pv997], .c 37, .c 3, .c 151,
  .p pv3 [pv2,pv3,pv310733], .c 3, .c 23, .c 5, .c 3, .c 67, .c 307, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv19421], .c 3, .c 13, .c 11, .c 3, .p pv2 [pv2,pv23,pv40531], .c 7, .c 3,
  .c 31, .c 5, .c 3, .c 29, .c 17, .c 3, .c 5, .c 13, .c 3,
]
private theorem h0227c18 : checkBlock 1864195 128 b0227c18 = true := by
  decide +kernel

private def b0227c19 : List Row := [
  .c 19, .p pv2 [pv2,pv3,pv155371], .c 3, .c 7, .c 59, .c 3, .p pv5 [pv2,pv932231], .c 5, .c 3,
  .p pv2 [pv2,pv29,pv16073], .c 7, .c 3, .c 5, .c 389, .c 3, .c 181, .p pv2 [pv2,pv3,pv310747],
  .c 3, .c 53, .c 11, .c 3, .c 73, .c 5, .c 3, .c 7, .c 463, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv103,pv431], .c 3, .c 11, .c 7, .c 3, .p pv2 [pv2,pv41,pv11369], .c 1091,
  .c 3, .c 43, .c 5, .c 3, .p pv3 [pv2,pv116533], .c 71, .c 3, .c 5, .c 47, .c 3, .c 7, .c 17,
  .c 3, .p pv2 [pv2,pv19,pv139,pv353], .p pv2 [pv2,pv3,pv7,pv151], .c 3, .p pv3 [pv2,pv233069],
  .c 5, .c 3, .p pv7 [pv2,pv79,pv11801], .c 101, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv43,pv73],
  .c 3, .p pv2 [pv2,pv5,pv137,pv1361], .c 193, .c 3, .c 11, .c 1259, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv31,pv1367], .p pv3 [pv2,pv3,pv5,pv7,pv13,pv683], .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv9323], .c 13, .c 3, .c 211, .c 43, .c 3, .c 29, .c 5, .c 3, .c 31, .c 11,
  .c 3, .c 5, .c 373, .c 3, .c 47, .c 23, .c 3, .c 79, .c 7, .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv61,pv3821], .c 919, .c 3, .c 5, .p pv13 [pv2,pv3,pv23,pv563], .c 3,
  .p pv2 [pv2,pv5,pv7,pv19,pv701], .c 109, .c 3, .c 7, .c 641, .c 3, .c 71, .c 5, .c 3, .c 17,
  .c 7, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv186469], .p pv2 [pv2,pv3,pv51797], .c 3,
  .c 449, .c 53, .c 3, .p pv5 [pv2,pv7,pv23,pv5791], .c 5,
]
private theorem h0227c19 : checkBlock 1864451 128 b0227c19 = true := by
  decide +kernel

private def b0227c20 : List Row := [
  .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv20719], .c 3, .c 5, .c 19, .c 3, .c 41, .c 7, .c 3, .c 367,
  .c 29, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv43,pv21683], .c 127, .c 3, .c 5, .c 17, .c 3,
  .c 7, .c 11, .c 3, .c 1249, .c 13, .c 3, .c 37, .c 5, .c 3, .p pv3 [pv2,pv29137], .c 23, .c 3,
  .c 5, .c 1187, .c 3, .c 17, .p pv3 [pv2,pv3,pv1279], .c 3, .c 29, .p pv7 [pv2,pv3,pv155399],
  .c 3, .c 7, .c 5, .c 3, .c 1181, .p pv17 [pv2,pv3,pv5,pv7,pv37], .c 3, .c 5, .c 7, .c 3, .c 13,
  .c 59, .c 3, .c 23, .c 11, .c 3, .p pv5 [pv2,pv179,pv5209], .c 5, .c 3, .c 199, .c 19, .c 3,
  .c 5, .c 13, .c 3, .c 11, .c 181, .c 3, .p pv5 [pv2,pv157,pv5939], .c 7, .c 3,
  .p pv2 [pv2,pv11,pv3853], .c 5, .c 3, .p pv2 [pv2,pv53,pv73,pv241],
  .p pv7 [pv2,pv3,pv5,pv31081], .c 3, .c 5, .c 31, .c 3, .p pv7 [pv2,pv5,pv7,pv26641],
  .p pv5 [pv2,pv3,pv59,pv439], .c 3, .c 7, .p pv7 [pv2,pv3,pv67,pv4639], .c 3, .c 17, .c 5, .c 3,
  .c 13, .c 7, .c 3, .c 5, .p pv13 [pv2,pv3,pv11,pv883], .c 3, .p pv3 [pv2,pv5,pv17,pv1097],
  .c 29, .c 3, .c 11, .c 23, .c 3, .c 47, .c 5, .c 3, .c 7, .p pv19 [pv2,pv3,pv5,pv15541], .c 3,
  .c 5, .c 83, .c 3, .c 59, .c 7, .c 3, .c 431, .p pv2 [pv2,pv3,pv310823], .c 3, .c 863, .c 5,
  .c 3, .c 223, .c 11, .c 3, .c 5, .c 71, .c 3, .c 7,
]
private theorem h0227c20 : checkBlock 1864707 128 b0227c20 = true := by
  decide +kernel

private def b0227c21 : List Row := [
  .c 139, .c 3, .c 13, .c 419, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv23,pv40543], .c 137, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv310831], .c 3, .c 31, .c 13, .c 3, .c 281, .c 197, .c 3, .c 7, .c 5,
  .c 3, .c 691, .p pv3 [pv2,pv3,pv5,pv7,pv83,pv107], .c 3, .c 5, .c 7, .c 3, .c 19,
  .p pv3 [pv2,pv3,pv31,pv37,pv271], .c 3, .p pv2 [pv2,pv932513], .c 211, .c 3, .c 149, .c 5, .c 3,
  .c 11, .c 277, .c 3, .c 5, .c 23, .c 3, .c 401, .c 17, .c 3, .p pv3 [pv2,pv167,pv349], .c 7,
  .c 3, .p pv5 [pv2,pv941,pv991], .c 5, .c 3, .p pv2 [pv2,pv466267], .c 13, .c 3, .c 5, .c 29,
  .c 3, .p pv17 [pv2,pv5,pv7,pv6661], .c 11, .c 3, .c 7, .c 1307, .c 3, .c 23, .c 5, .c 3, .c 71,
  .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv29,pv397], .c 3, .c 79, .c 173, .c 3, .c 107,
  .p pv3 [pv2,pv3,pv137,pv2269], .c 3, .c 13, .c 5, .c 3, .c 7, .c 41, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv13,pv61], .c 3, .p pv13 [pv2,pv5,pv93257], .c 7, .c 3,
  .p pv2 [pv2,pv31,pv67,pv449], .c 11, .c 3, .c 1201, .c 5, .c 3, .p pv7 [pv2,pv932579],
  .p pv29 [pv2,pv3,pv5,pv11,pv157], .c 3, .c 5, .c 59, .c 3, .c 7, .c 19, .c 3, .c 31,
  .p pv17 [pv2,pv3,pv7,pv113,pv131], .c 3, .c 1289, .c 5, .c 3, .c 17, .c 617, .c 3, .c 5, .c 61,
  .c 3, .c 13, .p pv3 [pv2,pv3,pv310867], .c 3, .c 37, .c 163, .c 3, .c 7, .c 5, .c 3,
]
private theorem h0227c21 : checkBlock 1864963 128 b0227c21 = true := by
  decide +kernel

private def b0227c22 : List Row := [
  .c 563, .p pv13 [pv2,pv3,pv5,pv7,pv4441], .c 3, .c 5, .c 7, .c 3, .c 23,
  .p pv7 [pv2,pv3,pv12953], .c 3, .c 11, .c 31, .c 3, .p pv5 [pv2,pv47,pv19843], .c 5, .c 3,
  .c 19, .c 29, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv93263],
  .p pv5 [pv2,pv3,pv7,pv89,pv499], .c 3, .p pv2 [pv2,pv13,pv71741], .c 7, .c 3, .c 683, .c 5,
  .c 3, .c 13, .c 11, .c 3, .c 5, .c 19, .c 3, .c 17, .c 271, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv310883], .c 3, .c 11, .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .c 109, .c 3,
  .p pv3 [pv2,pv5,pv46633], .c 23, .c 3, .p pv5 [pv2,pv932663], .p pv13 [pv2,pv3,pv38861], .c 3,
  .p pv3 [pv2,pv7,pv31,pv307], .c 5, .c 3, .c 7, .p pv29 [pv2,pv3,pv5,pv43,pv241], .c 3, .c 5,
  .c 11, .c 3, .c 89, .c 7, .c 3, .c 13, .c 17, .c 3, .c 19, .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv13,pv4783], .c 3, .c 5, .c 41, .c 3, .c 7, .c 13, .c 3, .c 997,
  .p pv23 [pv2,pv3,pv7,pv53,pv419], .c 3, .c 17, .c 5, .c 3, .p pv7 [pv2,pv233,pv4003], .c 19,
  .c 3, .c 5, .c 97, .c 3, .p pv2 [pv2,pv5,pv17,pv10973], .c 11, .c 3, .p pv3 [pv2,pv7,pv33311],
  .p pv2 [pv2,pv3,pv41,pv7583], .c 3, .c 7, .c 5, .c 3, .c 37, .p pv3 [pv2,pv3,pv5,pv7,pv47],
  .c 3, .c 5, .c 7, .c 3, .c 53, .p pv2 [pv2,pv3,pv73,pv4259], .c 3, .p pv5 [pv2,pv11,pv84793],
  .c 409, .c 3, .p pv2 [pv2,pv401,pv1163], .c 5, .c 3, .c 41, .c 13, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv37,pv2801], .c 3, .p pv11 [pv2,pv5,pv101,pv1847], .c 443,
]
private theorem h0227c22 : checkBlock 1865219 128 b0227c22 = true := by
  decide +kernel

private def b0227c23 : List Row := [
  .c 3, .c 19, .c 7, .c 3, .c 29, .c 5, .c 3, .p pv3 [pv2,pv116593],
  .p pv2 [pv2,pv3,pv5,pv11,pv5653], .c 3, .c 5, .c 191, .c 3, .c 11, .c 37, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv83,pv1873], .c 3, .c 13, .c 5, .c 3, .c 139, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv13,pv23917], .c 3, .c 293, .p pv2 [pv2,pv3,pv155461], .c 3,
  .p pv3 [pv2,pv103,pv283], .c 13, .c 3, .p pv5 [pv2,pv7,pv133253], .c 5, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv5,pv12437], .c 3, .c 5, .c 167, .c 3, .p pv3 [pv2,pv5,pv46639], .c 7, .c 3,
  .c 11, .p pv7 [pv2,pv3,pv19433], .c 3, .p pv2 [pv2,pv19,pv24547], .c 5, .c 3,
  .p pv2 [pv2,pv11,pv13,pv593], .c 241, .c 3, .c 5, .p pv2 [pv2,pv3,pv310931], .c 3, .c 7, .c 383,
  .c 3, .c 17, .c 23, .c 3, .p pv2 [pv2,pv932801], .c 5, .c 3, .p pv3 [pv2,pv233201], .c 11, .c 3,
  .c 5, .c 13, .c 3, .c 653, .c 41, .c 3, .c 503, .c 19, .c 3, .c 7, .c 5, .c 3, .c 59, .c 43,
  .c 3, .c 5, .c 7, .c 3, .c 37, .c 53, .c 3, .c 29, .p pv11 [pv2,pv3,pv139,pv2237], .c 3, .c 229,
  .c 5, .c 3, .c 13, .p pv11 [pv2,pv3,pv5,pv62189], .c 3, .c 5, .c 11, .c 3,
  .p pv3 [pv2,pv5,pv23321], .c 251, .c 3, .p pv5 [pv2,pv19,pv29,pv1693], .c 7, .c 3,
  .p pv2 [pv2,pv466423], .c 5, .c 3, .c 11, .c 521, .c 3, .c 5, .c 89, .c 3,
  .p pv17 [pv2,pv5,pv7,pv11,pv2423], .c 227, .c 3, .c 7, .p pv3 [pv2,pv3,pv103651], .c 3, .c 359,
  .c 5, .c 3, .p pv3 [pv2,pv911],
]
private theorem h0227c23 : checkBlock 1865475 128 b0227c23 = true := by
  decide +kernel

private def b0227c24 : List Row := [
  .c 7, .c 3, .c 5, .c 23, .c 3, .c 823, .c 11, .c 3, .c 13, .c 67, .c 3, .c 109, .c 5, .c 3,
  .c 7, .c 499, .c 3, .c 5, .c 17, .c 3, .c 1151, .c 7, .c 3, .c 797, .c 883, .c 3, .c 23, .c 5,
  .c 3, .c 1019, .p pv23 [pv2,pv3,pv5,pv20731], .c 3, .c 5, .c 31, .c 3, .c 7, .c 137, .c 3,
  .c 61, .c 11, .c 3, .c 43, .c 5, .c 3, .c 19, .p pv2 [pv2,pv3,pv5,pv11,pv257], .c 3, .c 5,
  .p pv43 [pv2,pv3,pv103657], .c 3, .c 11, .c 131, .c 3, .p pv5 [pv2,pv7,pv37,pv1801],
  .p pv3 [pv2,pv3,pv13,pv19,pv1259], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv233231], .c 13, .c 3,
  .c 5, .c 7, .c 3, .c 163, .p pv3 [pv2,pv3,pv109,pv317], .c 3, .c 631, .c 17, .c 3, .c 37, .c 5,
  .c 3, .c 191, .p pv37 [pv2,pv3,pv5,pv71,pv73], .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv17,pv1663],
  .c 3, .c 167, .p pv2 [pv2,pv3,pv7,pv97,pv229], .c 3, .c 11, .c 7, .c 3, .c 13, .c 5, .c 3,
  .c 541, .p pv3 [pv2,pv3,pv5,pv37,pv41], .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv443], .c 3, .c 23,
  .c 83, .c 3, .c 7, .c 13, .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv932969], .c 7, .c 3, .c 5,
  .c 29, .c 3, .c 41, .c 73, .c 3, .p pv2 [pv2,pv683], .p pv3 [pv2,pv3,pv353,pv881], .c 3, .c 11,
  .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 787, .c 3, .c 13, .c 7, .c 3,
]
private theorem h0227c24 : checkBlock 1865731 128 b0227c24 = true := by
  decide +kernel

private def b0227c25 : List Row := [
  .p pv2 [pv2,pv643,pv1451], .c 97, .c 3, .c 59, .c 5, .c 3, .p pv7 [pv2,pv932999],
  .p pv37 [pv2,pv3,pv5,pv311], .c 3, .c 5, .c 11, .c 3, .c 7, .c 23, .c 3, .c 67,
  .p pv11 [pv2,pv3,pv7,pv11,pv577], .c 3, .c 199, .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv62201],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv23,pv6761], .c 3, .c 47, .p pv2 [pv2,pv3,pv103669], .c 3, .c 19,
  .p pv7 [pv2,pv3,pv9719], .c 3, .c 7, .c 5, .c 3, .c 13, .c 1279, .c 3, .c 5, .c 7, .c 3, .c 43,
  .c 11, .c 3, .c 53, .c 829, .c 3, .p pv2 [pv2,pv23,pv113,pv359], .c 5, .c 3, .c 83,
  .p pv2 [pv2,pv3,pv5,pv17,pv3659], .c 3, .c 5, .c 233, .c 3, .p pv2 [pv2,pv5,pv18661], .c 349,
  .c 3, .c 17, .c 7, .c 3, .p pv3 [pv2,pv61,pv239], .c 5, .c 3, .c 373, .c 29, .c 3, .c 5,
  .p pv17 [pv2,pv3,pv311021], .c 3, .p pv2 [pv2,pv5,pv7,pv53,pv503], .c 821, .c 3, .c 7, .c 11,
  .c 3, .p pv5 [pv2,pv19,pv49109], .c 5, .c 3, .c 277, .c 7, .c 3, .c 5, .c 43, .c 3, .c 11,
  .c 13, .c 3, .c 227, .c 31, .c 3, .c 61, .c 5, .c 3, .c 7, .c 197, .c 3, .c 5, .c 107, .c 3,
  .p pv13 [pv2,pv5,pv186619], .c 7, .c 3, .c 23, .c 19, .c 3, .p pv2 [pv2,pv13,pv71777], .c 5,
  .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv62207], .c 3, .c 5, .c 79, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv199,pv521], .c 3, .c 11, .c 47, .c 3, .p pv3 [pv2,pv233279], .c 5, .c 3,
  .p pv7 [pv2,pv11,pv41,pv2069], .c 13,
]
private theorem h0227c25 : checkBlock 1865987 128 b0227c25 = true := by
  decide +kernel

private def b0227c26 : List Row := [
  .c 3, .c 5, .p pv3 [pv2,pv3,pv311041], .c 3, .p pv2 [pv2,pv5,pv1493], .c 307, .c 3, .c 103,
  .c 157, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv466567], .c 11, .c 3, .c 5, .c 7, .c 3,
  .p pv11 [pv2,pv5,pv13,pv37,pv97], .p pv2 [pv2,pv3,pv11,pv28277], .c 3, .c 223, .c 23, .c 3,
  .c 11, .c 5, .c 3, .c 1061, .p pv11 [pv2,pv3,pv5,pv6221], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv13,pv71,pv337], .c 3, .c 17, .c 19, .c 3, .c 37, .c 7, .c 3, .c 47, .c 5,
  .c 3, .c 43, .p pv37 [pv2,pv3,pv5,pv89,pv233], .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv7,pv13331], .p pv3 [pv2,pv3,pv53,pv5869], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv11,pv1571], .c 3, .c 29, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv103687], .c 3, .c 13, .p pv5 [pv2,pv3,pv43,pv3617], .c 3, .c 71, .c 17, .c 3,
  .c 1297, .c 5, .c 3, .c 7, .c 37, .c 3, .c 5, .c 13, .c 3, .c 107, .c 7, .c 3, .c 109,
  .p pv23 [pv2,pv3,pv19,pv4093], .c 3, .c 17, .c 5, .c 3, .c 67, .c 83, .c 3, .c 5, .c 19, .c 3,
  .c 7, .c 179, .c 3, .p pv2 [pv2,pv11,pv13,pv251], .p pv3 [pv2,pv3,pv7,pv14813], .c 3, .c 41,
  .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv23,pv541], .c 3, .c 5, .p pv5 [pv2,pv3,pv8641], .c 3,
  .p pv2 [pv2,pv5,pv93323], .c 103, .c 3, .p pv2 [pv2,pv7,pv133319], .c 11, .c 3, .c 7, .c 5,
  .c 3, .c 31, .c 17, .c 3, .c 5, .c 7, .c 3, .c 11, .c 449, .c 3, .c 173,
]
private theorem h0227c26 : checkBlock 1866243 128 b0227c26 = true := by
  decide +kernel

private def b0227c27 : List Row := [
  .p pv2 [pv2,pv3,pv17,pv29,pv631], .c 3, .c 19, .c 5, .c 3, .c 331, .c 47, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv109,pv1427], .c 3, .p pv3 [pv2,pv5,pv46663], .c 149, .c 3, .c 13, .c 7, .c 3,
  .c 79, .c 5, .c 3, .c 37, .c 19, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv857], .c 3,
  .p pv7 [pv2,pv5,pv7,pv5333], .c 13, .c 3, .c 7, .c 167, .c 3, .c 233, .c 5, .c 3,
  .p pv3 [pv2,pv11,pv21211], .c 7, .c 3, .c 5, .p pv13 [pv2,pv3,pv37,pv1051], .c 3, .c 101, .c 17,
  .c 3, .c 43, .c 461, .c 3, .p pv3 [pv2,pv7,pv13,pv641], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .c 41, .c 3, .c 23, .c 7, .c 3, .c 17, .c 131, .c 3, .c 11, .c 5, .c 3, .c 643, .c 13, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv19,pv2729], .c 3, .c 7, .c 29, .c 3, .c 113,
  .p pv13 [pv2,pv3,pv7,pv41,pv271], .c 3, .c 181, .c 5, .c 3, .p pv2 [pv2,pv933329], .c 61, .c 3,
  .c 5, .c 11, .c 3, .c 487, .c 43, .c 3, .p pv3 [pv2,pv7,pv163,pv409],
  .p pv3 [pv2,pv3,pv11,pv28283], .c 3, .c 7, .c 5, .c 3, .c 11, .c 79, .c 3, .c 5, .c 7, .c 3,
  .c 29, .c 23, .c 3, .c 1153, .c 13, .c 3, .c 53, .c 5, .c 3, .c 17,
  .p pv43 [pv2,pv3,pv5,pv3889], .c 3, .c 5, .c 31, .c 3, .c 19, .c 11, .c 3,
  .p pv3 [pv2,pv17,pv6863], .c 7, .c 3, .c 521, .c 5, .c 3, .c 23,
  .p pv3 [pv2,pv3,pv5,pv19,pv131], .c 3,
]
private theorem h0227c27 : checkBlock 1866499 128 b0227c27 = true := by
  decide +kernel

private def b0227c28 : List Row := [
  .c 5, .p pv5 [pv2,pv3,pv73,pv2131], .c 3, .c 13, .c 701, .c 3, .c 7, .c 19, .c 3, .c 127, .c 5,
  .c 3, .p pv2 [pv2,pv933389], .c 7, .c 3, .c 5, .c 13, .c 3, .c 179, .c 47, .c 3, .c 709, .c 11,
  .c 3, .c 71, .c 5, .c 3, .c 7, .c 389, .c 3, .c 5, .c 29, .c 3, .c 11, .c 7, .c 3,
  .p pv5 [pv2,pv13,pv19,pv3779], .c 73, .c 3, .p pv3 [pv2,pv11,pv10607], .c 5, .c 3, .c 13, .c 23,
  .c 3, .c 5, .p pv23 [pv2,pv3,pv29,pv10729], .c 3, .c 7, .c 41, .c 3, .p pv3 [pv2,pv233357],
  .p pv3 [pv2,pv3,pv7,pv44449], .c 3, .p pv5 [pv2,pv97,pv9623], .c 5, .c 3, .p pv2 [pv2,pv466717],
  .p pv3 [pv2,pv3,pv5,pv20743], .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv14143], .c 3, .c 131, .c 19,
  .c 3, .c 11, .c 17, .c 3, .c 7, .c 5, .c 3, .c 137, .p pv2 [pv2,pv3,pv5,pv7,pv127], .c 3, .c 5,
  .c 7, .c 3, .c 547, .c 31, .c 3, .c 13, .c 83, .c 3, .c 17, .c 5, .c 3, .c 367, .c 11, .c 3,
  .c 5, .c 59, .c 3, .p pv3 [pv2,pv5,pv17,pv19], .c 13, .c 3, .c 659, .c 7, .c 3, .c 11, .c 5,
  .c 3, .c 19, .p pv13 [pv2,pv3,pv5,pv2593], .c 3, .c 5, .p pv11 [pv2,pv3,pv61,pv5101], .c 3,
  .p pv7 [pv2,pv5,pv7,pv149,pv179], .p pv2 [pv2,pv3,pv155581], .c 3, .c 7, .c 23, .c 3, .c 37,
  .c 5, .c 3, .p pv2 [pv2,pv466747], .c 7, .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv1867],
  .p pv2 [pv2,pv3,pv23,pv83,pv163], .c 3, .c 79, .p pv19 [pv2,pv3,pv11,pv13,pv17],
]
private theorem h0227c28 : checkBlock 1866755 128 b0227c28 = true := by
  decide +kernel

private def b0227c29 : List Row := [
  .c 3, .p pv3 [pv2,pv7,pv131,pv509], .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 61, .c 3, .c 53,
  .c 7, .c 3, .c 31, .p pv3 [pv2,pv3,pv311173], .c 3, .c 107, .c 5, .c 3, .c 29,
  .p pv3 [pv2,pv3,pv5,pv461], .c 3, .c 5, .c 37, .c 3, .c 7, .c 11, .c 3, .c 439,
  .p pv2 [pv2,pv3,pv7,pv31,pv239], .c 3, .c 13, .c 5, .c 3, .p pv7 [pv2,pv29,pv32191], .c 103,
  .c 3, .c 5, .c 71, .c 3, .c 397, .c 17, .c 3, .c 1259, .c 13, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv466777], .c 19, .c 3, .c 5, .c 7, .c 3, .c 73, .p pv2 [pv2,pv3,pv47,pv2207], .c 3,
  .c 17, .c 11, .c 3, .c 877, .c 5, .c 3, .c 211, .c 1031, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv43,pv7237], .c 3, .c 11, .c 97, .c 3, .p pv2 [pv2,pv67,pv6967], .c 7, .c 3,
  .c 23, .c 5, .c 3, .c 47, .c 331, .c 3, .c 5, .c 13, .c 3, .c 41, .p pv3 [pv2,pv3,pv311197],
  .c 3, .c 7, .c 43, .c 3, .p pv3 [pv2,pv31,pv7529], .c 5, .c 3, .c 1303, .c 7, .c 3, .c 5,
  .c 347, .c 3, .p pv2 [pv2,pv5,pv61,pv3061], .p pv5 [pv2,pv3,pv17,pv113], .c 3, .c 11,
  .p pv2 [pv2,pv3,pv311203], .c 3, .c 29, .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv20747], .c 3,
  .c 5, .p pv13 [pv2,pv3,pv7,pv22229], .c 3, .p pv29 [pv2,pv5,pv46681], .c 7, .c 3, .c 587,
  .p pv7 [pv2,pv3,pv12967], .c 3, .p pv2 [pv2,pv29,pv16097], .c 5, .c 3,
  .p pv2 [pv2,pv499,pv1871], .c 11, .c 3, .c 5,
]
private theorem h0227c29 : checkBlock 1867011 128 b0227c29 = true := by
  decide +kernel

private def b0227c30 : List Row := [
  .c 73, .c 3, .c 7, .c 491, .c 3, .c 967, .c 37, .c 3, .c 11, .c 5, .c 3, .c 293, .c 59, .c 3,
  .c 5, .c 17, .c 3, .c 19, .p pv3 [pv2,pv3,pv227,pv457], .c 3, .c 13, .c 89, .c 3, .c 7, .c 5,
  .c 3, .p pv17 [pv2,pv43,pv21713], .p pv29 [pv2,pv3,pv5,pv7,pv13,pv19], .c 3, .c 5, .c 7, .c 3,
  .c 17, .c 13, .c 3, .p pv3 [pv2,pv233417], .c 19, .c 3, .p pv5 [pv2,pv933671], .c 5, .c 3,
  .c 11, .p pv23 [pv2,pv3,pv5,pv59,pv211], .c 3, .c 5, .c 47, .c 3, .c 43, .c 197, .c 3,
  .p pv5 [pv2,pv827,pv1129], .c 7, .c 3, .p pv2 [pv2,pv13,pv35911], .c 5, .c 3, .c 1103, .c 997,
  .c 3, .c 5, .c 823, .c 3, .c 449, .c 11, .c 3, .c 7, .c 17, .c 3, .c 857, .c 5, .c 3, .c 31,
  .c 7, .c 3, .c 5, .c 83, .c 3, .p pv2 [pv2,pv5,pv93371], .p pv3 [pv2,pv3,pv311237], .c 3, .c 37,
  .p pv29 [pv2,pv3,pv17291], .c 3, .c 17, .c 5, .c 3, .c 7, .c 937, .c 3, .c 5, .c 43, .c 3,
  .c 47, .c 7, .c 3, .c 401, .c 11, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv41,pv59,pv193], .c 31,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv11971], .c 3, .c 7, .c 419, .c 3, .c 89, .c 13, .c 3, .c 103,
  .c 5, .c 3, .c 349, .c 17, .c 3, .c 5, .c 179, .c 3, .c 461, .c 29, .c 3, .c 283, .c 757, .c 3,
]
private theorem h0227c30 : checkBlock 1867267 128 b0227c30 = true := by
  decide +kernel

private def b0227c31 : List Row := [
  .c 7, .c 5, .c 3, .c 19, .c 23, .c 3, .c 5, .c 7, .c 3, .c 13, .c 1069, .c 3, .c 11, .c 1123,
  .c 3, .p pv3 [pv2,pv17,pv3433], .c 5, .c 3, .c 73, .c 53, .c 3, .c 5, .c 13, .c 3, .c 29,
  .p pv2 [pv2,pv3,pv7,pv7411], .c 3, .c 23, .c 7, .c 3, .c 83, .c 5, .c 3, .c 389, .c 11, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv103,pv1511], .c 3, .p pv3 [pv2,pv5,pv7,pv23,pv29], .c 17, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv25939], .c 3, .c 11, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 1051, .c 3,
  .p pv17 [pv2,pv5,pv186763], .c 523, .c 3, .c 17, .c 47, .c 3, .c 19, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv12451], .c 3, .c 5, .c 11, .c 3, .c 193, .c 7, .c 3, .c 53, .c 23, .c 3,
  .c 41, .c 5, .c 3, .c 11, .c 19, .c 3, .c 5, .c 29, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv23,pv67,pv101], .c 3, .c 13, .c 103, .c 3, .c 1307, .c 5, .c 3,
  .p pv2 [pv2,pv173,pv2699], .p pv3 [pv2,pv3,pv5,pv13,pv4789], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv29,pv1789], .c 3, .c 137, .c 11, .c 3, .p pv5 [pv2,pv7,pv71,pv1879],
  .p pv11 [pv2,pv3,pv167,pv233], .c 3, .c 7, .c 5, .c 3, .c 17, .c 571, .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv31,pv241], .p pv7 [pv2,pv3,pv8647], .c 3, .c 19, .c 61, .c 3, .c 59, .c 5,
  .c 3, .p pv3 [pv2,pv7,pv33353], .p pv2 [pv2,pv3,pv5,pv20753], .c 3, .c 5, .c 113,
]
private theorem h0227c31 : checkBlock 1867523 128 b0227c31 = true := by
  decide +kernel

def rows0227 : List Row :=
  b0227c00 ++ b0227c01 ++ b0227c02 ++ b0227c03 ++ b0227c04 ++ b0227c05 ++ b0227c06 ++ b0227c07 ++
  b0227c08 ++ b0227c09 ++ b0227c10 ++ b0227c11 ++ b0227c12 ++ b0227c13 ++ b0227c14 ++ b0227c15 ++
  b0227c16 ++ b0227c17 ++ b0227c18 ++ b0227c19 ++ b0227c20 ++ b0227c21 ++ b0227c22 ++ b0227c23 ++
  b0227c24 ++ b0227c25 ++ b0227c26 ++ b0227c27 ++ b0227c28 ++ b0227c29 ++ b0227c30 ++ b0227c31

theorem checked0227 : checkBlock 1859587 4096 rows0227 = true :=
  checkBlock_append h0227c00 (
    checkBlock_append h0227c01 (
    checkBlock_append h0227c02 (
    checkBlock_append h0227c03 (
    checkBlock_append h0227c04 (
    checkBlock_append h0227c05 (
    checkBlock_append h0227c06 (
    checkBlock_append h0227c07 (
    checkBlock_append h0227c08 (
    checkBlock_append h0227c09 (
    checkBlock_append h0227c10 (
    checkBlock_append h0227c11 (
    checkBlock_append h0227c12 (
    checkBlock_append h0227c13 (
    checkBlock_append h0227c14 (
    checkBlock_append h0227c15 (
    checkBlock_append h0227c16 (
    checkBlock_append h0227c17 (
    checkBlock_append h0227c18 (
    checkBlock_append h0227c19 (
    checkBlock_append h0227c20 (
    checkBlock_append h0227c21 (
    checkBlock_append h0227c22 (
    checkBlock_append h0227c23 (
    checkBlock_append h0227c24 (
    checkBlock_append h0227c25 (
    checkBlock_append h0227c26 (
    checkBlock_append h0227c27 (
    checkBlock_append h0227c28 (
    checkBlock_append h0227c29 (
    checkBlock_append h0227c30 (
    h0227c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
