/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks04/Block0382
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks04/Block0382.checked0382
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table032
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table039
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table044
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table050
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table059
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table070
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table087
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table112
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table151
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table152

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0382c00 : List Row := [
  .c 13, .c 37, .c 3, .c 1481, .c 5, .c 3, .c 223, .c 29, .c 3, .c 5, .c 467, .c 3, .c 7, .c 13,
  .c 3, .c 17, .c 11, .c 3, .p pv5 [pv2,pv337,pv4643], .c 5, .c 3, .c 1409,
  .p pv11 [pv2,pv3,pv5,pv11,pv29,pv109], .c 3, .c 5, .c 173, .c 3, .c 11, .c 23, .c 3, .c 41,
  .c 367, .c 3, .c 7, .c 5, .c 3, .c 29, .p pv17 [pv2,pv3,pv5,pv7,pv7451], .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv312943], .c 19, .c 3, .c 73, .p pv3 [pv2,pv3,pv13,pv53,pv757], .c 3,
  .p pv2 [pv2,pv1564721], .c 5, .c 3, .c 23, .c 13, .c 3, .c 5, .c 179, .c 3,
  .p pv2 [pv2,pv5,pv37,pv4229], .p pv7 [pv2,pv3,pv7,pv17,pv487], .c 3, .c 11, .c 7, .c 3, .c 1087,
  .c 5, .c 3, .c 17, .c 31, .c 3, .c 5, .p pv3 [pv2,pv3,pv521581], .c 3, .c 53, .c 383, .c 3,
  .c 7, .c 109, .c 3, .c 13, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv743],
  .c 3, .p pv7 [pv2,pv5,pv39119], .p pv2 [pv2,pv3,pv11,pv47417], .c 3, .c 1619, .c 13, .c 3,
  .c 11, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 17, .c 3, .c 397, .c 7, .c 3,
  .p pv2 [pv2,pv782389], .p pv3 [pv2,pv3,pv307,pv1699], .c 3, .c 1399, .c 5, .c 3, .c 1151, .c 37,
  .c 3, .c 5, .c 11, .c 3, .c 7, .c 43, .c 3, .c 23, .c 47, .c 3, .c 29, .c 5, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv5,pv163],
]
private theorem h0382c00 : checkBlock 3129347 128 b0382c00 = true := by
  decide +kernel

private def b0382c01 : List Row := [
  .c 3, .c 5, .c 13, .c 3, .p pv11 [pv2,pv5,pv11,pv23,pv1237], .p pv61 [pv2,pv3,pv41,pv6361],
  .c 3, .p pv3 [pv2,pv7,pv27943], .p pv2 [pv2,pv3,pv521603], .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv137,pv5711], .c 439, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv78241], .c 11,
  .c 3, .c 521, .c 17, .c 3, .c 41, .c 5, .c 3, .c 13, .c 19, .c 3, .c 5, .c 31, .c 3, .c 181,
  .c 199, .c 3, .p pv2 [pv2,pv11,pv71129], .c 7, .c 3, .c 17, .c 5, .c 3,
  .p pv3 [pv2,pv193,pv2027], .p pv2 [pv2,pv3,pv5,pv104323], .c 3, .c 5, .c 283, .c 3,
  .p pv2 [pv2,pv5,pv7,pv17,pv263], .c 53, .c 3, .c 7, .c 11, .c 3, .c 1279, .c 5, .c 3, .c 37,
  .c 7, .c 3, .c 5, .c 61, .c 3, .c 11, .p pv2 [pv2,pv3,pv28979], .c 3, .c 13, .c 197, .c 3,
  .c 79, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv19,pv37,pv53], .c 3, .c 113,
  .c 7, .c 3, .c 29, .p pv7 [pv2,pv3,pv17,pv2557], .c 3, .c 59, .c 5, .c 3, .c 271,
  .p pv29 [pv2,pv3,pv5,pv52163], .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv479], .c 3, .c 7, .c 37, .c 3,
  .c 11, .p pv3 [pv2,pv3,pv7,pv43,pv1733], .c 3, .p pv2 [pv2,pv13,pv17,pv73,pv97], .c 5, .c 3,
  .c 53, .p pv2 [pv2,pv3,pv5,pv104327], .c 3, .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv156491],
  .c 277, .c 3, .p pv2 [pv2,pv7,pv109,pv293], .c 653, .c 3, .c 7, .c 5, .c 3,
  .p pv11 [pv2,pv67,pv23357], .c 11, .c 3, .c 5, .c 7, .c 3, .c 19, .c 17, .c 3, .c 107,
]
private theorem h0382c01 : checkBlock 3129603 128 b0382c01 = true := by
  decide +kernel

private def b0382c02 : List Row := [
  .p pv2 [pv2,pv3,pv41,pv4241], .c 3, .c 11, .c 5, .c 3, .c 823, .c 47, .c 3, .c 5, .c 773, .c 3,
  .c 193, .c 29, .c 3, .c 17, .c 7, .c 3, .c 13, .c 5, .c 3, .c 41, .c 79, .c 3, .c 5, .c 11,
  .c 3, .p pv11 [pv2,pv5,pv7,pv61,pv733], .p pv7 [pv2,pv3,pv29,pv1499], .c 3, .c 7, .c 13, .c 3,
  .p pv2 [pv2,pv431,pv3631], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv197,pv331],
  .c 3, .c 29, .p pv3 [pv2,pv3,pv521657], .c 3, .p pv2 [pv2,pv19,pv31,pv2657], .c 487, .c 3,
  .p pv3 [pv2,pv7,pv89,pv157], .c 5, .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv26083], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv24841], .c 3, .c 13, .c 7, .c 3, .c 31, .c 449, .c 3, .c 131, .c 5, .c 3,
  .c 17, .p pv7 [pv2,pv3,pv5,pv101,pv1033], .c 3, .c 5, .c 13, .c 3, .c 7, .c 19, .c 3,
  .p pv5 [pv2,pv11,pv17,pv8369], .c 59, .c 3, .c 43, .c 5, .c 3, .p pv2 [pv2,pv1565009], .c 53,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv521671], .c 3, .p pv7 [pv2,pv5,pv313003], .c 181, .c 3,
  .p pv2 [pv2,pv7,pv13,pv8599], .c 11, .c 3, .c 7, .c 5, .c 3, .c 13, .c 353, .c 3, .c 5, .c 7,
  .c 3, .c 11, .c 41, .c 3, .c 103, .c 569, .c 3, .c 1657, .c 5, .c 3, .c 19, .c 167, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv29,pv17989], .c 3, .c 17, .c 23, .c 3, .p pv3 [pv2,pv83,pv2357], .c 7, .c 3,
  .c 227, .c 5, .c 3, .c 157, .p pv3 [pv2,pv3,pv5,pv11593], .c 3,
]
private theorem h0382c02 : checkBlock 3129859 128 b0382c02 = true := by
  decide +kernel

private def b0382c03 : List Row := [
  .c 5, .c 19, .c 3, .c 359, .c 673, .c 3, .c 7, .p pv11 [pv2,pv3,pv21737], .c 3, .c 197, .c 5,
  .c 3, .c 23, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv173897], .c 3, .c 1621, .c 13, .c 3, .c 433,
  .c 17, .c 3, .c 31, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 71, .c 3, .c 349, .c 7, .c 3,
  .p pv2 [pv2,pv41,pv59,pv647], .c 683, .c 3, .c 11, .c 5, .c 3, .p pv7 [pv2,pv1565099], .c 229,
  .c 3, .c 5, .p pv11 [pv2,pv3,pv401,pv1301], .c 3, .c 7, .c 113, .c 3, .c 79, .c 89, .c 3,
  .c 887, .c 5, .c 3, .p pv2 [pv2,pv43,pv18199], .c 13, .c 3, .c 5, .c 11, .c 3,
  .p pv3 [pv2,pv5,pv67,pv73], .p pv2 [pv2,pv3,pv521707], .c 3, .c 47,
  .p pv13 [pv2,pv3,pv11,pv71,pv167], .c 3, .c 7, .c 5, .c 3, .c 11, .c 17, .c 3, .c 5, .c 7, .c 3,
  .c 43, .c 103, .c 3, .c 23, .p pv3 [pv2,pv3,pv17,pv30689], .c 3, .c 13, .c 5, .c 3, .c 29,
  .p pv2 [pv2,pv3,pv5,pv34781], .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv79,pv127], .c 3, .c 467, .c 11,
  .c 3, .c 19, .c 7, .c 3, .c 73, .c 5, .c 3, .c 71, .c 271, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv19,pv113], .c 3, .p pv19 [pv2,pv5,pv7,pv197,pv227], .p pv5 [pv2,pv3,pv260861],
  .c 3, .c 7, .c 53, .c 3, .c 463, .c 5, .c 3, .c 31, .c 7, .c 3, .c 5, .c 43, .c 3, .c 13, .c 17,
  .c 3, .p pv5 [pv2,pv1565183], .c 11,
]
private theorem h0382c03 : checkBlock 3130115 128 b0382c03 = true := by
  decide +kernel

private def b0382c04 : List Row := [
  .c 3, .p pv2 [pv2,pv7,pv111799], .c 5, .c 3, .c 7, .c 151, .c 3, .c 5, .c 13, .c 3, .c 11, .c 7,
  .c 3, .c 17, .p pv19 [pv2,pv3,pv61,pv2851], .c 3, .p pv2 [pv2,pv11,pv19,pv7489], .c 5, .c 3,
  .p pv3 [pv2,pv391301], .c 31, .c 3, .c 5, .p pv5 [pv2,pv3,pv21739], .c 3, .c 7, .c 127, .c 3,
  .p pv2 [pv2,pv13,pv120401], .p pv2 [pv2,pv3,pv7,pv83,pv449], .c 3, .c 1231, .c 5, .c 3, .c 13,
  .c 67, .c 3, .c 5, .c 593, .c 3, .p pv11 [pv2,pv5,pv137,pv457], .p pv2 [pv2,pv3,pv13,pv6689],
  .c 3, .c 11, .c 19, .c 3, .c 7, .c 5, .c 3, .c 199, .c 587, .c 3, .c 5, .c 7, .c 3, .c 59,
  .p pv3 [pv2,pv3,pv17,pv47,pv653], .c 3, .p pv5 [pv2,pv43,pv89,pv409], .c 263, .c 3,
  .p pv2 [pv2,pv29,pv26987], .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .c 23, .c 3, .c 83,
  .p pv5 [pv2,pv3,pv7,pv11], .c 3, .c 13, .c 7, .c 3, .c 11, .c 5, .c 3, .c 43, .c 179, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv130439], .c 3, .p pv3 [pv2,pv5,pv7,pv59,pv379], .c 13, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv260879], .c 3, .c 23, .c 5, .c 3, .p pv11 [pv2,pv139,pv11261], .c 7, .c 3,
  .c 5, .c 11, .c 3, .p pv13 [pv2,pv5,pv37,pv8461], .c 19, .c 3, .p pv3 [pv2,pv23,pv47,pv181],
  .c 29, .c 3, .p pv5 [pv2,pv7,pv13,pv103,pv167], .c 5, .c 3, .c 7, .c 613, .c 3, .c 5, .c 31,
  .c 3, .c 17, .c 7, .c 3, .c 37, .c 601, .c 3, .c 1483, .c 5, .c 3, .p pv2 [pv2,pv17,pv92077],
  .c 13, .c 3, .c 5,
]
private theorem h0382c04 : checkBlock 3130371 128 b0382c04 = true := by
  decide +kernel

private def b0382c05 : List Row := [
  .p pv2 [pv2,pv3,pv313,pv1667], .c 3, .c 7, .c 11, .c 3, .c 29, .c 149, .c 3, .c 733, .c 5, .c 3,
  .c 19, .c 461, .c 3, .c 5, .c 53, .c 3, .c 239, .p pv5 [pv2,pv3,pv521777], .c 3,
  .p pv5 [pv2,pv7,pv11,pv29,pv701], .c 17, .c 3, .c 7, .c 5, .c 3, .p pv13 [pv2,pv41,pv73,pv523],
  .c 37, .c 3, .c 5, .c 7, .c 3, .c 23, .p pv2 [pv2,pv3,pv317,pv823], .c 3, .c 101, .c 11, .c 3,
  .c 17, .c 5, .c 3, .c 67, .p pv11 [pv2,pv3,pv5,pv11,pv53,pv179], .c 3, .c 5, .c 47, .c 3, .c 11,
  .c 251, .c 3, .c 1381, .c 7, .c 3, .p pv2 [pv2,pv11,pv71153], .c 5, .c 3,
  .p pv2 [pv2,pv13,pv120413], .c 163, .c 3, .c 5, .c 1543, .c 3, .c 13, .c 29, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv57977], .c 3, .c 19, .c 5, .c 3, .c 131, .c 7, .c 3, .c 5, .c 13, .c 3,
  .c 173, .c 23, .c 3, .c 11, .p pv2 [pv2,pv3,pv17,pv103,pv149], .c 3, .c 571, .c 5, .c 3, .c 7,
  .c 19, .c 3, .c 5, .c 109, .c 3, .c 29, .c 7, .c 3, .p pv3 [pv2,pv13,pv53,pv71],
  .p pv2 [pv2,pv3,pv211,pv2473], .c 3, .p pv5 [pv2,pv17,pv92083], .c 5, .c 3, .c 13, .c 11, .c 3,
  .c 5, .c 311, .c 3, .c 7, .c 67, .c 3, .c 1237, .c 79, .c 3, .c 11, .c 5, .c 3, .c 509, .c 137,
  .c 3, .c 5, .c 199, .c 3, .p pv7 [pv2,pv5,pv313087], .c 17, .c 3, .c 19, .c 349, .c 3,
]
private theorem h0382c05 : checkBlock 3130627 128 b0382c05 = true := by
  decide +kernel

private def b0382c06 : List Row := [
  .c 7, .c 5, .c 3, .c 179, .c 103, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv131,pv239], .c 37,
  .c 3, .c 13, .c 659, .c 3, .p pv3 [pv2,pv97841], .c 5, .c 3, .c 11, .c 23, .c 3, .c 5, .c 29,
  .c 3, .c 89, .c 13, .c 3, .c 149, .c 7, .c 3, .p pv5 [pv2,pv1565471], .c 5, .c 3,
  .p pv2 [pv2,pv439,pv1783], .c 1117, .c 3, .c 5, .p pv2 [pv2,pv3,pv29,pv2999], .c 3,
  .p pv19 [pv2,pv5,pv7,pv5591], .c 11, .c 3, .c 7, .c 31, .c 3, .c 599, .c 5, .c 3,
  .p pv2 [pv2,pv1565489], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv521831], .c 3, .c 19,
  .p pv5 [pv2,pv3,pv17,pv1279], .c 3, .p pv2 [pv2,pv11,pv6469], .c 47, .c 3, .c 1571, .c 5, .c 3,
  .c 7, .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv18637], .c 3, .p pv2 [pv2,pv5,pv89,pv1759], .c 7,
  .c 3, .p pv2 [pv2,pv17,pv5417], .c 11, .c 3, .c 919, .c 5, .c 3, .c 193,
  .p pv41 [pv2,pv3,pv5,pv11,pv593], .c 3, .c 5, .c 41, .c 3, .c 7, .p pv5 [pv2,pv3,pv260921],
  .c 3, .p pv3 [pv2,pv195691], .c 23, .c 3, .c 13, .c 5, .c 3, .c 61, .c 59, .c 3, .c 5, .c 17,
  .c 3, .c 53, .c 167, .c 3, .p pv5 [pv2,pv7,pv19,pv79,pv149], .c 13, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv1565549], .c 29, .c 3, .c 5, .c 7, .c 3, .c 17, .p pv5 [pv2,pv3,pv283,pv461],
  .c 3, .c 11, .c 181, .c 3, .p pv2 [pv2,pv1565561], .c 5, .c 3, .c 41, .c 43, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv151],
]
private theorem h0382c06 : checkBlock 3130883 128 b0382c06 = true := by
  decide +kernel

private def b0382c07 : List Row := [
  .c 3, .c 13, .c 19, .c 3, .c 1031, .c 7, .c 3, .p pv3 [pv2,pv195697], .c 5, .c 3, .c 29, .c 11,
  .c 3, .c 5, .c 13, .c 3, .c 71, .p pv2 [pv2,pv3,pv11,pv7907], .c 3, .c 7, .c 17, .c 3, .c 11,
  .c 5, .c 3, .c 59, .c 7, .c 3, .c 5, .c 23, .c 3, .c 523, .p pv3 [pv2,pv3,pv101,pv5167], .c 3,
  .c 569, .p pv53 [pv2,pv3,pv157,pv277], .c 3, .c 17, .c 5, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv5,pv23,pv2269], .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv17,pv113,pv163],
  .c 7, .c 3, .p pv2 [pv2,pv37,pv21157], .p pv3 [pv2,pv3,pv11,pv19,pv227], .c 3, .c 23, .c 5,
  .c 3, .c 11, .p pv13 [pv2,pv3,pv5,pv167], .c 3, .c 5, .c 19, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv73,pv2383], .c 3, .p pv2 [pv2,pv23,pv68071], .c 463, .c 3, .c 37, .c 5, .c 3,
  .c 31, .c 17, .c 3, .c 5, .c 89, .c 3, .c 293, .c 11, .c 3, .c 13, .p pv2 [pv2,pv3,pv17,pv379],
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv541,pv1447], .p pv3 [pv2,pv3,pv5,pv7,pv13,pv31,pv37],
  .c 3, .c 5, .c 7, .c 3, .p pv11 [pv2,pv5,pv78283], .c 13, .c 3, .p pv5 [pv2,pv11,pv317,pv449],
  .p pv17 [pv2,pv3,pv47,pv347], .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv7,pv223667], .c 31, .c 3,
  .c 5, .c 37, .c 3, .p pv11 [pv2,pv5,pv62627], .p pv31 [pv2,pv3,pv7,pv19,pv109], .c 3,
  .p pv2 [pv2,pv782839], .c 7, .c 3, .c 853, .c 5, .c 3, .p pv3 [pv2,pv509,pv769], .c 19, .c 3,
  .c 5, .p pv11 [pv2,pv3,pv89,pv733], .c 3, .c 11, .c 17, .c 3, .c 7, .c 43, .c 3, .c 163,
]
private theorem h0382c07 : checkBlock 3131139 128 b0382c07 = true := by
  decide +kernel

private def b0382c08 : List Row := [
  .c 5, .c 3, .c 53, .c 7, .c 3, .c 5, .c 1021, .c 3, .c 1499, .c 797, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv521903], .c 3, .c 773, .c 5, .c 3, .c 7, .p pv23 [pv2,pv3,pv5,pv104381], .c 3,
  .c 5, .p pv23 [pv2,pv3,pv7,pv11,pv3389], .c 3, .p pv3 [pv2,pv5,pv13,pv3011], .c 7, .c 3, .c 11,
  .c 29, .c 3, .c 13, .c 5, .c 3, .c 311, .c 109, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv19,pv2113],
  .c 3, .c 7, .c 23, .c 3, .p pv2 [pv2,pv251,pv3119], .c 13, .c 3, .p pv2 [pv2,pv1565741], .c 5,
  .c 3, .p pv3 [pv2,pv97859], .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv23,pv31,pv61], .c 3,
  .p pv2 [pv2,pv5,pv6263], .p pv11 [pv2,pv3,pv11,pv17,pv2791], .c 3, .c 29, .c 103, .c 3, .c 7,
  .c 5, .c 3, .c 17, .c 619, .c 3, .c 5, .c 7, .c 3, .c 13, .c 149, .c 3,
  .p pv3 [pv2,pv17,pv29,pv397], .c 41, .c 3, .c 59, .c 5, .c 3, .p pv2 [pv2,pv7,pv97,pv1153],
  .p pv3 [pv2,pv3,pv5,pv6959], .c 3, .c 5, .c 11, .c 3, .c 19, .c 47, .c 3, .c 443, .c 7, .c 3,
  .c 461, .c 5, .c 3, .c 11, .c 1637, .c 3, .c 5, .c 17, .c 3, .c 331, .p pv17 [pv2,pv3,pv130483],
  .c 3, .c 7, .c 19, .c 3, .p pv2 [pv2,pv59,pv26539], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 239,
  .c 3, .c 17, .c 11, .c 3, .c 73, .p pv2 [pv2,pv3,pv260969], .c 3, .c 593, .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv8699], .c 3, .c 5, .c 43, .c 3,
]
private theorem h0382c08 : checkBlock 3131395 128 b0382c08 = true := by
  decide +kernel

private def b0382c09 : List Row := [
  .c 31, .c 7, .c 3, .c 23, .c 929, .c 3, .c 199, .c 5, .c 3, .p pv2 [pv2,pv71,pv11027],
  .p pv11 [pv2,pv3,pv5,pv139,pv751], .c 3, .c 5, .c 379, .c 3, .c 7, .c 137, .c 3, .c 13, .c 11,
  .c 3, .c 127, .c 5, .c 3, .p pv2 [pv2,pv269,pv5821], .p pv2 [pv2,pv3,pv5,pv11,pv13,pv73], .c 3,
  .c 5, .c 101, .c 3, .c 11, .c 13, .c 3, .c 37, .c 163, .c 3, .c 7, .c 5, .c 3, .c 947, .c 521,
  .c 3, .c 5, .c 7, .c 3, .c 337, .p pv19 [pv2,pv3,pv97,pv5381], .c 3, .p pv2 [pv2,pv1565873],
  .c 23, .c 3, .c 233, .c 5, .c 3, .c 1471, .p pv11 [pv2,pv3,pv5,pv13049], .c 3, .c 5, .c 877,
  .c 3, .p pv11 [pv2,pv5,pv19,pv53,pv311], .c 73, .c 3, .c 11, .c 7, .c 3, .c 107, .c 5, .c 3,
  .c 19, .c 13, .c 3, .c 5, .c 29, .c 3, .c 61, .c 1283, .c 3, .c 7, .c 139, .c 3, .c 1373, .c 5,
  .c 3, .c 43, .c 7, .c 3, .c 5, .c 19, .c 3, .c 149, .p pv7 [pv2,pv3,pv11,pv11863], .c 3, .c 31,
  .c 83, .c 3, .c 11, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv20879], .c 3, .c 5,
  .p pv37 [pv2,pv3,pv7,pv13,pv239], .c 3, .p pv7 [pv2,pv5,pv156593], .c 7, .c 3, .c 41, .c 13,
  .c 3, .c 211, .c 5, .c 3, .p pv7 [pv2,pv313,pv5003], .c 71, .c 3, .c 5, .c 11, .c 3, .c 7,
  .c 17, .c 3, .c 59, .c 31, .c 3, .c 19, .c 5,
]
private theorem h0382c09 : checkBlock 3131651 128 b0382c09 = true := by
  decide +kernel

private def b0382c10 : List Row := [
  .c 3, .c 11, .p pv23 [pv2,pv3,pv5,pv17,pv23,pv89], .c 3, .c 5, .p pv2 [pv2,pv3,pv359,pv727],
  .c 3, .c 13, .c 61, .c 3, .c 17, .c 53, .c 3, .c 7, .c 5, .c 3, .c 37, .c 19, .c 3, .c 5, .c 7,
  .c 3, .p pv7 [pv2,pv5,pv62639], .c 11, .c 3, .c 137, .c 1163, .c 3, .c 179, .c 5, .c 3, .c 563,
  .c 29, .c 3, .c 5, .p pv5 [pv2,pv3,pv37,pv3527], .c 3, .p pv3 [pv2,pv5,pv149,pv1051],
  .p pv3 [pv2,pv3,pv7,pv53,pv67], .c 3, .c 839, .c 7, .c 3, .c 157, .c 5, .c 3, .c 13, .c 883,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv109,pv4789], .c 3, .c 557, .c 37, .c 3, .c 7, .c 11, .c 3, .c 31,
  .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv19,pv241], .c 3, .c 11, .c 1607, .c 3,
  .c 1123, .c 67, .c 3, .c 643, .c 5, .c 3, .c 7, .c 199, .c 3, .c 5, .c 263, .c 3, .c 23, .c 7,
  .c 3, .c 13, .c 131, .c 3, .p pv2 [pv2,pv811,pv1931], .c 5, .c 3, .c 491, .c 1321, .c 3, .c 5,
  .c 17, .c 3, .c 7, .c 13, .c 3, .c 11, .c 733, .c 3, .c 41, .c 5, .c 3,
  .p pv7 [pv2,pv11,pv142369], .p pv7 [pv2,pv3,pv5,pv43,pv607], .c 3, .c 5, .c 47, .c 3, .c 17,
  .c 59, .c 3, .c 769, .p pv2 [pv2,pv3,pv73,pv7151], .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv17,pv46061], .c 11, .c 3, .c 5, .c 7, .c 3, .c 37,
]
private theorem h0382c10 : checkBlock 3131907 128 b0382c10 = true := by
  decide +kernel

private def b0382c11 : List Row := [
  .c 23, .c 3, .c 61, .c 19, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv7,pv31,pv1031], .c 13, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv23,pv22697], .c 3, .c 313, .c 151, .c 3, .c 193, .c 7, .c 3, .c 29,
  .c 5, .c 3, .c 23, .c 73, .c 3, .c 5, .c 11, .c 3, .c 47, .c 499, .c 3, .c 7, .c 251, .c 3,
  .c 13, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 53, .c 3, .c 59, .c 331, .c 3,
  .p pv3 [pv2,pv97883], .c 13, .c 3, .p pv5 [pv2,pv7,pv229,pv977], .c 5, .c 3, .c 7, .c 31, .c 3,
  .c 5, .c 41, .c 3, .p pv3 [pv2,pv5,pv78307], .c 7, .c 3, .p pv5 [pv2,pv1566143], .c 61, .c 3,
  .c 1667, .c 5, .c 3, .p pv2 [pv2,pv13,pv120473], .c 17, .c 3, .c 5, .c 71, .c 3, .c 7, .c 101,
  .c 3, .c 67, .c 29, .c 3, .p pv2 [pv2,pv433,pv3617], .c 5, .c 3, .p pv3 [pv2,pv127,pv3083],
  .p pv2 [pv2,pv3,pv5,pv263,pv397], .c 3, .c 5, .c 13, .c 3, .c 131, .p pv3 [pv2,pv3,pv174019],
  .c 3, .c 23, .c 11, .c 3, .c 7, .c 5, .c 3, .c 19, .c 1399, .c 3, .c 5, .c 7, .c 3, .c 11,
  .c 227, .c 3, .c 29, .p pv2 [pv2,pv3,pv19,pv43,pv71], .c 3, .c 37, .c 5, .c 3, .c 13, .c 937,
  .c 3, .c 5, .c 19, .c 3, .c 1553, .c 17, .c 3, .p pv5 [pv2,pv29,pv53,pv1019], .c 7, .c 3,
  .p pv2 [pv2,pv601,pv1303], .c 5, .c 3,
]
private theorem h0382c11 : checkBlock 3132163 128 b0382c11 = true := by
  decide +kernel

private def b0382c12 : List Row := [
  .c 167, .c 43, .c 3, .c 5, .c 149, .c 3, .p pv7 [pv2,pv5,pv7,pv73,pv613], .c 1567, .c 3, .c 7,
  .c 23, .c 3, .p pv5 [pv2,pv109,pv14369], .c 5, .c 3, .c 71, .c 7, .c 3, .c 5, .c 31, .c 3,
  .p pv2 [pv2,pv5,pv156623], .c 293, .c 3, .c 13, .p pv11 [pv2,pv3,pv87013], .c 3, .c 19, .c 5,
  .c 3, .c 7, .c 11, .c 3, .c 5, .c 59, .c 3, .c 229, .c 7, .c 3, .c 197,
  .p pv2 [pv2,pv3,pv522083], .c 3, .c 11, .c 5, .c 3, .c 617, .c 19, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv261043], .c 3, .c 7, .c 41, .c 3, .c 283, .p pv17 [pv2,pv3,pv7,pv9323], .c 3,
  .c 61, .c 5, .c 3, .c 17, .p pv7 [pv2,pv3,pv5,pv5801], .c 3, .c 5, .c 11, .c 3, .c 29,
  .p pv5 [pv2,pv3,pv130523], .c 3, .c 383, .p pv3 [pv2,pv3,pv11,pv13,pv1217], .c 3, .c 7, .c 5,
  .c 3, .c 11, .c 13, .c 3, .c 5, .c 7, .c 3, .c 31, .c 193, .c 3, .c 19, .c 941, .c 3, .c 43,
  .c 5, .c 3, .p pv13 [pv2,pv7,pv223757], .p pv19 [pv2,pv3,pv5,pv23,pv227], .c 3, .c 5, .c 17,
  .c 3, .c 1753, .c 11, .c 3, .c 389, .c 7, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv307,pv2551],
  .p pv3 [pv2,pv3,pv5,pv34807], .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv43,pv467], .c 3, .c 17, .c 31,
  .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv67,pv11689], .c 5, .c 3, .p pv2 [pv2,pv17,pv199,pv463],
  .c 7, .c 3, .c 5, .c 29, .c 3, .c 53, .c 449,
]
private theorem h0382c12 : checkBlock 3132419 128 b0382c12 = true := by
  decide +kernel

private def b0382c13 : List Row := [
  .c 3, .p pv2 [pv2,pv827,pv947], .c 11, .c 3, .c 719, .c 5, .c 3, .c 7, .c 47, .c 3, .c 5,
  .c 163, .c 3, .c 11, .c 7, .c 3, .p pv2 [pv2,pv1566353], .c 17, .c 3, .c 1669, .c 5, .c 3,
  .c 67, .c 1229, .c 3, .c 5, .c 13, .c 3, .c 7, .c 71, .c 3, .p pv3 [pv2,pv31,pv1579], .c 19,
  .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv181,pv4327], .p pv3 [pv2,pv3,pv5,pv4177], .c 3, .c 5,
  .c 1583, .c 3, .c 23, .p pv2 [pv2,pv3,pv522127], .c 3, .c 11, .c 41, .c 3, .c 7, .c 5, .c 3,
  .c 13, .p pv2 [pv2,pv3,pv5,pv7,pv7459], .c 3, .c 5, .c 7, .c 3, .c 829,
  .p pv7 [pv2,pv3,pv13,pv3347], .c 3, .c 151, .p pv3 [pv2,pv3,pv31,pv16843], .c 3,
  .p pv2 [pv2,pv1566401], .c 5, .c 3, .c 97, .c 11, .c 3, .c 5, .c 313, .c 3, .c 983,
  .p pv3 [pv2,pv3,pv7,pv11,pv6781], .c 3, .c 37, .c 7, .c 3, .c 11, .c 5, .c 3,
  .p pv13 [pv2,pv61,pv25679], .c 29, .c 3, .c 5, .p pv3 [pv2,pv3,pv174047], .c 3, .c 41, .c 19,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv179,pv2917], .c 3, .c 419, .c 5, .c 3, .c 281, .c 7, .c 3, .c 5,
  .c 11, .c 3, .p pv3 [pv2,pv5,pv39161], .c 13, .c 3, .p pv5 [pv2,pv659,pv2377], .c 89, .c 3,
  .c 811, .c 5, .c 3, .c 7, .c 37, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv97,pv769], .c 3, .c 317,
  .c 7, .c 3, .p pv2 [pv2,pv137,pv5717], .c 101, .c 3, .p pv2 [pv2,pv13,pv23,pv31], .c 5, .c 3,
  .c 19,
]
private theorem h0382c13 : checkBlock 3132675 128 b0382c13 = true := by
  decide +kernel

private def b0382c14 : List Row := [
  .c 541, .c 3, .c 5, .c 43, .c 3, .c 7, .c 11, .c 3, .c 17, .c 229, .c 3, .c 31, .c 5, .c 3,
  .c 59, .c 13, .c 3, .c 5, .c 19, .c 3, .p pv7 [pv2,pv5,pv313297], .c 47, .c 3,
  .p pv3 [pv2,pv7,pv11,pv2543], .p pv3 [pv2,pv3,pv89,pv5867], .c 3, .c 7, .c 5, .c 3, .c 53,
  .c 23, .c 3, .c 5, .c 7, .c 3, .c 83, .c 97, .c 3, .c 797, .c 11, .c 3, .c 13, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv59,pv3793], .c 61, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv4463], .c 3, .c 11,
  .p pv5 [pv2,pv3,pv7,pv17,pv1097], .c 3, .c 23, .c 7, .c 3, .c 19, .c 5, .c 3, .c 17, .c 239,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv41,pv199], .c 3, .c 79, .c 347, .c 3, .c 7, .c 853, .c 3, .c 29,
  .c 5, .c 3, .c 367, .c 7, .c 3, .c 5, .c 73, .c 3, .c 13, .c 283, .c 3, .c 11, .c 151, .c 3,
  .c 467, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv181,pv577], .c 3, .c 5, .c 13, .c 3, .c 67,
  .c 7, .c 3, .c 131, .c 23, .c 3, .c 1061, .c 5, .c 3, .c 31, .c 11, .c 3, .c 5, .c 277, .c 3,
  .c 7, .p pv47 [pv2,pv3,pv11,pv23,pv43], .c 3, .c 19, .c 71, .c 3, .c 11, .c 5, .c 3, .c 13,
  .p pv17 [pv2,pv3,pv5,pv31,pv1123], .c 3, .c 5, .p pv7 [pv2,pv3,pv19,pv6871], .c 3,
  .p pv2 [pv2,pv5,pv156659], .p pv3 [pv2,pv3,pv13,pv40169], .c 3,
]
private theorem h0382c14 : checkBlock 3132931 128 b0382c14 = true := by
  decide +kernel

private def b0382c15 : List Row := [
  .c 503, .c 29, .c 3, .c 7, .c 5, .c 3, .c 139, .c 31, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv313321], .p pv2 [pv2,pv3,pv261101], .c 3, .c 127, .c 17, .c 3, .c 757, .c 5,
  .c 3, .c 11, .c 743, .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv15359], .c 3, .c 241,
  .p pv2 [pv2,pv3,pv7,pv307], .c 3, .c 13, .c 7, .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv131,pv11959], .c 41, .c 3, .c 5, .c 23, .c 3, .c 19, .c 11, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv174071], .c 3, .p pv2 [pv2,pv419,pv3739], .c 5, .c 3, .p pv3 [pv2,pv391661],
  .c 7, .c 3, .c 5, .p pv11 [pv2,pv3,pv7253], .c 3, .c 71, .p pv3 [pv2,pv3,pv41,pv47,pv271], .c 3,
  .c 53, .c 19, .c 3, .c 23, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 137, .c 3,
  .p pv2 [pv2,pv5,pv313333], .c 7, .c 3, .p pv3 [pv2,pv23,pv17029], .c 11, .c 3, .c 41, .c 5,
  .c 3, .c 47, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv31,pv8423], .c 3, .c 7, .c 29, .c 3, .c 43,
  .c 599, .c 3, .c 223, .c 5, .c 3, .c 73, .p pv7 [pv2,pv3,pv5,pv52223], .c 3, .c 5, .c 31, .c 3,
  .c 97, .c 1621, .c 3, .p pv2 [pv2,pv7,pv47,pv2381], .p pv3 [pv2,pv3,pv522233], .c 3, .c 7, .c 5,
  .c 3, .c 1201, .p pv3 [pv2,pv3,pv5,pv7,pv43,pv347], .c 3, .c 5, .c 7, .c 3, .c 29, .c 17, .c 3,
  .c 11, .c 13, .c 3, .p pv3 [pv2,pv391679], .c 5, .c 3, .p pv7 [pv2,pv7,pv11,pv20347],
  .p pv31 [pv2,pv3,pv5,pv17],
]
private theorem h0382c15 : checkBlock 3133187 128 b0382c15 = true := by
  decide +kernel

private def b0382c16 : List Row := [
  .c 3, .c 5, .p pv3 [pv2,pv3,pv367,pv1423], .c 3, .c 23, .c 43, .c 3, .c 17, .c 7, .c 3,
  .p pv5 [pv2,pv1566731], .c 5, .c 3, .p pv2 [pv2,pv13,pv60259], .c 11, .c 3, .c 5, .c 139, .c 3,
  .c 13, .c 569, .c 3, .c 7, .c 1381, .c 3, .c 11, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 13,
  .c 3, .c 31, .p pv5 [pv2,pv3,pv89,pv163], .c 3, .c 929, .c 53, .c 3, .c 67, .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv37,pv941], .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv156677], .c 7,
  .c 3, .p pv2 [pv2,pv13,pv191,pv631], .c 59, .c 3, .c 863, .c 5, .c 3, .c 11, .c 211, .c 3, .c 5,
  .c 37, .c 3, .c 7, .c 31, .c 3, .c 331, .c 1483, .c 3, .p pv5 [pv2,pv43,pv83,pv439], .c 5, .c 3,
  .c 23, .p pv3 [pv2,pv3,pv5,pv67,pv1559], .c 3, .c 5, .p pv2 [pv2,pv3,pv223,pv1171], .c 3, .c 89,
  .c 11, .c 3, .p pv7 [pv2,pv7,pv223829], .p pv11 [pv2,pv3,pv59,pv2213], .c 3, .c 7, .c 5, .c 3,
  .c 149, .c 433, .c 3, .c 5, .c 7, .c 3, .c 47, .p pv5 [pv2,pv3,pv19,pv859], .c 3, .c 13,
  .p pv11 [pv2,pv3,pv174091], .c 3, .p pv2 [pv2,pv1566821], .c 5, .c 3, .c 457, .c 19, .c 3, .c 5,
  .c 67, .c 3, .c 17, .c 13, .c 3, .c 59, .c 7, .c 3, .p pv3 [pv2,pv103,pv3803], .c 5, .c 3,
  .c 197, .c 23, .c 3, .c 5, .c 577, .c 3, .c 11, .c 79, .c 3, .c 7,
]
private theorem h0382c16 : checkBlock 3133443 128 b0382c16 = true := by
  decide +kernel

private def b0382c17 : List Row := [
  .p pv2 [pv2,pv3,pv522283], .c 3, .c 151, .c 5, .c 3, .c 107, .c 7, .c 3, .c 5, .c 881, .c 3,
  .p pv3 [pv2,pv5,pv157,pv499], .c 241, .c 3, .c 19, .c 17, .c 3, .p pv2 [pv2,pv7,pv111919], .c 5,
  .c 3, .c 7, .c 13, .c 3, .c 5, .c 653, .c 3, .p pv11 [pv2,pv5,pv23,pv109], .c 7, .c 3, .c 11,
  .c 31, .c 3, .c 17, .c 5, .c 3, .c 29, .c 887, .c 3, .c 5, .p pv5 [pv2,pv3,pv65287], .c 3, .c 7,
  .p pv3 [pv2,pv3,pv131,pv443], .c 3, .p pv2 [pv2,pv1566893], .c 37, .c 3, .c 13, .c 5, .c 3,
  .p pv7 [pv2,pv29,pv71,pv761], .c 11, .c 3, .c 5, .c 1493, .c 3, .p pv2 [pv2,pv5,pv313381],
  .c 367, .c 3, .c 73, .c 13, .c 3, .c 7, .c 5, .c 3, .c 113, .c 17, .c 3, .c 5, .c 7, .c 3,
  .c 19, .p pv5 [pv2,pv3,pv23,pv22709], .c 3, .p pv5 [pv2,pv1566923], .c 641, .c 3,
  .p pv2 [pv2,pv31,pv127,pv199], .c 5, .c 3, .c 109, .p pv7 [pv2,pv3,pv5,pv19,pv2749], .c 3, .c 5,
  .c 11, .c 3, .c 13, .p pv5 [pv2,pv3,pv7,pv3109], .c 3, .c 157, .c 7, .c 3, .c 31, .c 5, .c 3,
  .c 11, .p pv3 [pv2,pv3,pv5,pv53,pv73], .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv7,pv11,pv37],
  .c 59, .c 3, .c 7, .p pv2 [pv2,pv3,pv263,pv331], .c 3, .c 47, .c 5, .c 3,
  .p pv17 [pv2,pv397,pv3947], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv43,pv4049], .c 3,
  .p pv2 [pv2,pv5,pv79,pv3967], .c 11, .c 3, .c 37, .p pv2 [pv2,pv3,pv522323], .c 3, .c 29, .c 5,
  .c 3, .c 7, .c 379, .c 3,
]
private theorem h0382c17 : checkBlock 3133699 128 b0382c17 = true := by
  decide +kernel

private def b0382c18 : List Row := [
  .c 5, .c 23, .c 3, .p pv3 [pv2,pv5,pv47,pv1667], .c 7, .c 3, .c 17, .c 43, .c 3, .c 97, .c 5,
  .c 3, .c 127, .c 103, .c 3, .c 5, .p pv2 [pv2,pv3,pv251,pv2081], .c 3, .c 7, .c 19, .c 3, .c 61,
  .c 11, .c 3, .c 23, .c 5, .c 3, .c 79, .c 37, .c 3, .c 5, .p pv7 [pv2,pv3,pv5441], .c 3, .c 11,
  .p pv3 [pv2,pv3,pv522337], .c 3, .c 13, .p pv2 [pv2,pv3,pv261169], .c 3, .c 7, .c 5, .c 3,
  .p pv23 [pv2,pv31,pv50549], .p pv17 [pv2,pv3,pv5,pv7,pv13,pv41], .c 3, .c 5, .c 7, .c 3, .c 199,
  .c 13, .c 3, .p pv3 [pv2,pv391757], .c 29, .c 3, .p pv5 [pv2,pv1567031], .c 5, .c 3, .c 17,
  .p pv31 [pv2,pv3,pv5,pv97,pv359], .c 3, .c 5, .c 109, .c 3, .c 41, .c 233, .c 3, .c 11, .c 7,
  .c 3, .p pv2 [pv2,pv13,pv60271], .c 5, .c 3, .c 739, .c 47, .c 3, .c 5, .c 19, .c 3, .c 179,
  .p pv7 [pv2,pv3,pv32647], .c 3, .c 7, .c 61, .c 3, .p pv2 [pv2,pv37,pv41,pv1033], .c 5, .c 3,
  .c 1097, .c 7, .c 3, .c 5, .c 17, .c 3, .c 23, .p pv3 [pv2,pv3,pv11,pv1439], .c 3,
  .p pv2 [pv2,pv29,pv54037], .c 137, .c 3, .c 11, .c 5, .c 3, .c 7, .c 673, .c 3, .c 5, .c 79,
  .c 3, .c 17, .c 7, .c 3, .c 631, .c 317, .c 3, .c 13, .c 5, .c 3, .c 227, .c 157, .c 3, .c 5,
  .c 11, .c 3, .c 7, .p pv3 [pv2,pv3,pv19,pv1447], .c 3, .p pv5 [pv2,pv1567103], .c 13,
]
private theorem h0382c18 : checkBlock 3133955 128 b0382c18 = true := by
  decide +kernel

private def b0382c19 : List Row := [
  .c 3, .p pv2 [pv2,pv783553], .c 5, .c 3, .c 11, .c 19, .c 3, .c 5, .c 43, .c 3,
  .p pv7 [pv2,pv5,pv11,pv28493], .c 23, .c 3, .c 251, .c 17, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv13,pv30137], .p pv2 [pv2,pv3,pv5,pv7,pv199], .c 3, .c 5, .c 7, .c 3, .c 13, .c 11,
  .c 3, .p pv2 [pv2,pv1567133], .c 613, .c 3, .c 17, .c 5, .c 3, .c 23, .c 113, .c 3, .c 5, .c 13,
  .c 3, .c 29, .c 1123, .c 3, .c 19, .c 7, .c 3, .p pv5 [pv2,pv23,pv61,pv1117], .c 5, .c 3,
  .p pv2 [pv2,pv733,pv1069], .c 139, .c 3, .c 5, .c 31, .c 3, .p pv3 [pv2,pv5,pv7,pv29,pv193],
  .c 229, .c 3, .c 7, .c 11, .c 3, .c 101, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv522391], .c 3, .c 11, .p pv5 [pv2,pv3,pv13,pv5023], .c 3,
  .p pv2 [pv2,pv43,pv18223], .c 1697, .c 3, .c 61, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 181,
  .c 3, .c 37, .c 7, .c 3, .p pv2 [pv2,pv271,pv5783], .p pv2 [pv2,pv3,pv269,pv971], .c 3, .c 103,
  .c 5, .c 3, .c 43, .c 73, .c 3, .c 5, .c 29, .c 3, .c 7, .p pv2 [pv2,pv3,pv83,pv1049], .c 3,
  .c 11, .p pv2 [pv2,pv3,pv7,pv37,pv2017], .c 3, .c 137, .c 5, .c 3, .c 359,
  .p pv17 [pv2,pv3,pv5,pv13,pv19,pv47], .c 3, .c 5, .c 71, .c 3, .c 31, .c 13, .c 3,
  .p pv5 [pv2,pv7,pv241,pv929], .c 19, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv97,pv107,pv151],
  .c 11, .c 3, .c 5,
]
private theorem h0382c19 : checkBlock 3134211 128 b0382c19 = true := by
  decide +kernel

private def b0382c20 : List Row := [
  .c 7, .c 3, .c 941, .c 53, .c 3, .c 17, .p pv3 [pv2,pv3,pv522413], .c 3, .c 11, .c 5, .c 3,
  .c 709, .c 41, .c 3, .c 5, .p pv5 [pv2,pv3,pv103,pv317], .c 3, .c 191, .c 31, .c 3, .c 113,
  .c 7, .c 3, .c 109, .c 5, .c 3, .p pv11 [pv2,pv1567259], .c 13, .c 3, .c 5, .c 11, .c 3,
  .c 1367, .c 991, .c 3, .c 7, .c 419, .c 3, .p pv5 [pv2,pv1567271], .c 5, .c 3, .c 11, .c 7,
  .c 3, .c 5, .p pv11 [pv2,pv3,pv87071], .c 3, .p pv3 [pv2,pv5,pv11,pv13,pv137], .c 19, .c 3,
  .c 599, .c 311, .c 3, .c 13, .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .c 173, .c 3,
  .p pv11 [pv2,pv5,pv167,pv1877], .c 7, .c 3, .p pv2 [pv2,pv17,pv31,pv1487], .c 13, .c 3, .c 37,
  .c 5, .c 3, .c 151, .c 59, .c 3, .c 5, .c 401, .c 3, .c 7, .p pv3 [pv2,pv3,pv109,pv4793], .c 3,
  .c 31, .c 257, .c 3, .p pv3 [pv2,pv53,pv7393], .c 5, .c 3, .c 19, .c 79, .c 3, .c 5, .c 17,
  .c 3, .c 13, .c 163, .c 3, .c 43, .c 11, .c 3, .c 7, .c 5, .c 3, .c 89,
  .p pv3 [pv2,pv3,pv5,pv7,pv11,pv23,pv59], .c 3, .c 5, .c 7, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv174149], .c 3, .c 241, .c 31, .c 3, .c 23, .c 5, .c 3, .c 131, .c 1471, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv193,pv2707], .c 3, .c 223, .p pv5 [pv2,pv3,pv7,pv47,pv397], .c 3,
  .c 743, .c 7, .c 3,
]
private theorem h0382c20 : checkBlock 3134467 128 b0382c20 = true := by
  decide +kernel

private def b0382c21 : List Row := [
  .p pv2 [pv2,pv1567361], .c 5, .c 3, .c 13, .c 109, .c 3, .c 5, .c 41, .c 3, .c 127, .c 43, .c 3,
  .c 7, .c 17, .c 3, .c 19, .c 5, .c 3, .c 47, .c 7, .c 3, .c 5, .c 1171, .c 3,
  .p pv2 [pv2,pv5,pv313477], .p pv2 [pv2,pv3,pv19,pv4583], .c 3, .c 307, .c 107, .c 3, .c 17,
  .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .p pv11 [pv2,pv3,pv7,pv67,pv557], .c 3,
  .p pv3 [pv2,pv5,pv17,pv461], .c 7, .c 3, .c 13, .c 277, .c 3, .c 11, .c 5, .c 3, .c 41,
  .p pv2 [pv2,pv3,pv5,pv13,pv4019], .c 3, .c 5, .c 83, .c 3, .c 7, .c 13, .c 3,
  .p pv2 [pv2,pv281,pv2789], .c 73, .c 3, .p pv2 [pv2,pv29,pv54049], .c 5, .c 3, .c 1297, .c 17,
  .c 3, .c 5, .c 11, .c 3, .c 197, .c 67, .c 3, .c 19, .c 1423, .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv19 [pv2,pv3,pv5,pv7,pv311], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv11,pv28499],
  .p pv2 [pv2,pv3,pv261241], .c 3, .c 53, .c 37, .c 3, .p pv5 [pv2,pv17,pv92203], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv103,pv1087], .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv29027], .c 3,
  .p pv7 [pv2,pv5,pv181,pv433], .c 11, .c 3, .p pv5 [pv2,pv269,pv5827], .c 7, .c 3, .c 173, .c 5,
  .c 3, .c 101, .p pv17 [pv2,pv3,pv5,pv52249], .c 3, .c 5, .c 47, .c 3, .c 389, .c 17, .c 3, .c 7,
  .c 113, .c 3, .c 13, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 617,
]
private theorem h0382c21 : checkBlock 3134723 128 b0382c21 = true := by
  decide +kernel

private def b0382c22 : List Row := [
  .c 3, .c 19, .c 41, .c 3, .c 17, .c 11, .c 3, .c 83, .c 5, .c 3, .c 7, .c 43, .c 3, .c 5,
  .c 1153, .c 3, .c 11, .c 7, .c 3, .p pv3 [pv2,pv29,pv13513], .c 19, .c 3,
  .p pv5 [pv2,pv11,pv142501], .c 5, .c 3, .p pv2 [pv2,pv13,pv60289],
  .p pv3 [pv2,pv3,pv5,pv31,pv3371], .c 3, .c 5, .p pv2 [pv2,pv3,pv79,pv3307], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv174169], .c 3, .c 37, .p pv17 [pv2,pv3,pv7,pv18661], .c 3, .c 653, .c 5, .c 3,
  .p pv2 [pv2,pv73,pv109,pv197], .c 23, .c 3, .c 5, .c 13, .c 3, .p pv29 [pv2,pv5,pv313507],
  .p pv13 [pv2,pv3,pv17,pv113], .c 3, .c 11, .p pv17 [pv2,pv3,pv58057], .c 3, .c 7, .c 5, .c 3,
  .c 17, .c 167, .c 3, .c 5, .c 7, .c 3, .c 181, .c 29, .c 3, .c 23, .c 53, .c 3,
  .p pv3 [pv2,pv391889], .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv522521], .c 3,
  .c 67, .c 19, .c 3, .c 97, .c 7, .c 3, .c 11, .c 5, .c 3, .c 1559, .p pv29 [pv2,pv3,pv5,pv6967],
  .c 3, .c 5, .c 17, .c 3, .c 29, .p pv3 [pv2,pv3,pv53,pv9859], .c 3, .c 7, .c 241, .c 3, .c 43,
  .c 5, .c 3, .c 1229, .c 7, .c 3, .c 5, .c 11, .c 3, .c 17, .c 977, .c 3, .c 13, .c 23, .c 3,
  .c 89, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv13,pv8039], .c 3, .c 5, .c 61, .c 3,
  .p pv2 [pv2,pv5,pv11,pv14251], .c 7, .c 3, .p pv2 [pv2,pv1097,pv1429], .c 41, .c 3, .c 1129,
]
private theorem h0382c22 : checkBlock 3134979 128 b0382c22 = true := by
  decide +kernel

private def b0382c23 : List Row := [
  .c 5, .c 3, .c 229, .c 251, .c 3, .c 5, .c 19, .c 3, .c 7, .c 11, .c 3, .c 1607, .c 17, .c 3,
  .c 1319, .c 5, .c 3, .c 37, .c 1031, .c 3, .c 5, .c 29, .c 3, .c 367,
  .p pv2 [pv2,pv3,pv181,pv2887], .c 3, .p pv5 [pv2,pv7,pv11,pv20359], .c 71, .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv113,pv13873], .c 13, .c 3, .c 5, .c 7, .c 3, .c 41,
  .p pv5 [pv2,pv3,pv21773], .c 3, .p pv2 [pv2,pv783829], .c 11, .c 3, .c 19, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv13997], .c 97, .c 3, .c 5, .c 23, .c 3, .c 11, .c 37, .c 3, .c 563, .c 7,
  .c 3, .c 13, .c 5, .c 3, .c 971, .c 17, .c 3, .c 5, .c 449, .c 3, .c 31,
  .p pv2 [pv2,pv3,pv261281], .c 3, .c 7, .c 13, .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv43,pv18229], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv23753], .c 3,
  .p pv3 [pv2,pv5,pv61,pv257], .p pv2 [pv2,pv3,pv31,pv1873], .c 3, .c 11,
  .p pv11 [pv2,pv3,pv83,pv787], .c 3, .p pv2 [pv2,pv7,pv17,pv941], .c 5, .c 3, .c 7, .c 107, .c 3,
  .c 5, .c 53, .c 3, .c 13, .c 7, .c 3, .c 19, .c 631, .c 3, .p pv2 [pv2,pv1567721], .c 5, .c 3,
  .p pv3 [pv2,pv337,pv1163], .c 11, .c 3, .c 5, .c 13, .c 3, .c 7, .c 17, .c 3, .c 379,
  .p pv17 [pv2,pv3,pv7,pv163,pv229], .c 3, .c 11, .c 5, .c 3, .c 881, .c 233, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv263,pv1987], .c 3,
]
private theorem h0382c23 : checkBlock 3135235 128 b0382c23 = true := by
  decide +kernel

private def b0382c24 : List Row := [
  .c 37, .c 1307, .c 3, .c 17, .c 907, .c 3, .c 7, .c 5, .c 3, .c 13, .c 47, .c 3, .c 5, .c 7,
  .c 3, .c 23, .p pv3 [pv2,pv3,pv13,pv61,pv659], .c 3, .p pv5 [pv2,pv31,pv103,pv491],
  .p pv7 [pv2,pv3,pv11,pv37,pv107], .c 3, .c 53, .c 5, .c 3, .c 11, .c 1741, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv174197], .c 3, .c 19, .p pv19 [pv2,pv3,pv7,pv2333], .c 3, .c 31, .c 7, .c 3,
  .c 331, .c 5, .c 3, .c 73, .p pv3 [pv2,pv3,pv5,pv19,pv5501], .c 3, .c 5, .c 739, .c 3, .c 1439,
  .c 11, .c 3, .c 7, .c 19, .c 3, .p pv3 [pv2,pv167,pv2347], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv522601], .c 3, .c 1451, .c 13, .c 3, .p pv3 [pv2,pv11,pv17,pv131], .c 31,
  .c 3, .p pv5 [pv2,pv7,pv97,pv2309], .c 5, .c 3, .c 7, .c 163, .c 3, .c 5, .c 113, .c 3,
  .p pv3 [pv2,pv5,pv277,pv283], .c 7, .c 3, .c 191, .c 11, .c 3, .c 683, .c 5, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv5,pv11,pv4751], .c 3, .c 5, .c 17, .c 3, .c 7, .c 59, .c 3,
  .p pv2 [pv2,pv37,pv21187], .c 281, .c 3, .c 29, .c 5, .c 3, .c 43, .c 13, .c 3, .c 5, .c 229,
  .c 3, .c 17, .c 19, .c 3, .p pv2 [pv2,pv7,pv653], .p pv2 [pv2,pv3,pv87103], .c 3, .c 7, .c 5,
  .c 3, .c 97, .c 41, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv13,pv24121], .c 269, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv522623], .c 3, .c 13, .c 5,
]
private theorem h0382c24 : checkBlock 3135491 128 b0382c24 = true := by
  decide +kernel

private def b0382c25 : List Row := [
  .c 3, .c 263, .c 23, .c 3, .c 5, .c 127, .c 3, .c 157, .c 857, .c 3, .p pv5 [pv2,pv61,pv25703],
  .c 7, .c 3, .p pv2 [pv2,pv641,pv1223], .c 5, .c 3, .c 19, .c 11, .c 3, .c 5, .c 37, .c 3, .c 59,
  .c 47, .c 3, .c 7, .c 29, .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv13,pv3769], .c 7, .c 3, .c 5,
  .c 19, .c 3, .c 13, .c 83, .c 3, .c 61, .c 1103, .c 3, .p pv3 [pv2,pv7,pv55997], .c 5, .c 3,
  .c 7, .p pv13 [pv2,pv3,pv5,pv47,pv139], .c 3, .c 5, .c 11, .c 3, .c 53, .c 7, .c 3, .c 29,
  .p pv2 [pv2,pv3,pv11,pv47513], .c 3, .c 113, .c 5, .c 3, .c 11, .c 17, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv261323], .c 3, .c 7, .p pv11 [pv2,pv3,pv211,pv2477], .c 3, .c 47, .c 23, .c 3,
  .c 19, .c 5, .c 3, .c 13, .c 179, .c 3, .c 5, .c 709, .c 3, .c 643, .c 11, .c 3, .c 277, .c 239,
  .c 3, .c 7, .c 5, .c 3, .c 31, .c 19, .c 3, .c 5, .c 7, .c 3, .c 1609, .p pv5 [pv2,pv3,pv58073],
  .c 3, .c 43, .c 61, .c 3, .p pv3 [pv2,pv195997], .c 5, .c 3, .p pv7 [pv2,pv7,pv23,pv9739],
  .p pv29 [pv2,pv3,pv5,pv31,pv281], .c 3, .c 5, .c 41, .c 3, .c 173, .c 17, .c 3, .c 13, .c 7,
  .c 3, .p pv5 [pv2,pv769,pv2039], .c 5, .c 3, .c 83, .c 31, .c 3, .c 5, .c 443, .c 3, .c 11,
]
private theorem h0382c25 : checkBlock 3135747 128 b0382c25 = true := by
  decide +kernel

private def b0382c26 : List Row := [
  .c 13, .c 3, .c 7, .c 37, .c 3, .c 479, .c 5, .c 3, .p pv2 [pv2,pv601,pv2609], .c 7, .c 3, .c 5,
  .c 23, .c 3, .c 29, .c 43, .c 3, .p pv2 [pv2,pv784009], .c 109, .c 3, .c 197, .c 5, .c 3, .c 7,
  .c 1669, .c 3, .c 5, .c 193, .c 3, .c 773, .c 7, .c 3, .c 11, .c 67, .c 3, .c 23, .c 5, .c 3,
  .p pv7 [pv2,pv11,pv12959], .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv59,pv2953], .c 3, .c 7, .c 89,
  .c 3, .p pv3 [pv2,pv23,pv4261], .p pv2 [pv2,pv3,pv7,pv10667], .c 3, .p pv5 [pv2,pv19,pv82529],
  .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .c 1753, .c 3, .c 19, .p pv2 [pv2,pv3,pv11,pv47,pv337],
  .c 3, .p pv5 [pv2,pv7,pv17,pv13177], .p pv7 [pv2,pv3,pv8167], .c 3, .c 7, .c 5, .c 3, .c 937,
  .c 71, .c 3, .c 5, .c 7, .c 3, .c 101, .c 73, .c 3, .c 37, .c 13, .c 3,
  .p pv2 [pv2,pv43,pv36467], .c 5, .c 3, .c 47, .c 257, .c 3, .c 5, .c 11, .c 3, .c 659, .c 461,
  .c 3, .c 181, .c 7, .c 3, .c 61, .c 5, .c 3, .c 11, .p pv11 [pv2,pv3,pv5,pv5227], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv283,pv1847], .c 3, .c 13, .c 41, .c 3, .c 7, .c 433, .c 3,
  .p pv5 [pv2,pv53,pv29587], .c 5, .c 3, .p pv2 [pv2,pv17,pv2713], .c 7, .c 3, .c 5, .c 13, .c 3,
  .c 281, .c 11, .c 3, .c 103, .p pv11 [pv2,pv3,pv43,pv1013], .c 3, .p pv2 [pv2,pv7,pv101,pv1109],
  .c 5, .c 3,
]
private theorem h0382c26 : checkBlock 3136003 128 b0382c26 = true := by
  decide +kernel

private def b0382c27 : List Row := [
  .c 7, .p pv2 [pv2,pv3,pv5,pv167,pv313], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv8297], .c 3, .c 89,
  .c 7, .c 3, .c 107, .c 17, .c 3, .c 71, .c 5, .c 3, .c 13, .c 43, .c 3, .c 5, .c 1759, .c 3,
  .c 7, .c 23, .c 3, .p pv2 [pv2,pv1568153], .c 11, .c 3, .c 17, .c 5, .c 3,
  .p pv7 [pv2,pv1568159], .c 29, .c 3, .c 5, .p pv3 [pv2,pv3,pv23,pv22727], .c 3, .c 11,
  .p pv2 [pv2,pv3,pv31,pv8431], .c 3, .c 67, .p pv2 [pv2,pv3,pv174241], .c 3, .c 7, .c 5, .c 3,
  .c 19, .p pv3 [pv2,pv3,pv5,pv7,pv29,pv103], .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv89,pv881],
  .c 31, .c 3, .c 13, .c 607, .c 3, .p pv2 [pv2,pv23,pv73,pv467], .c 5, .c 3, .c 29, .c 17, .c 3,
  .c 5, .c 19, .c 3, .c 457, .c 13, .c 3, .c 11, .c 7, .c 3, .p pv2 [pv2,pv131,pv11971], .c 5,
  .c 3, .p pv3 [pv2,pv11,pv29,pv1229], .c 191, .c 3, .c 5, .p pv23 [pv2,pv3,pv37,pv883], .c 3,
  .c 151, .p pv5 [pv2,pv3,pv522737], .c 3, .c 7, .p pv2 [pv2,pv3,pv113,pv257], .c 3,
  .p pv3 [pv2,pv13,pv17,pv887], .c 5, .c 3, .c 199, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv163,pv1069], .c 3, .c 47, .c 37, .c 3, .p pv3 [pv2,pv31,pv12647], .c 41, .c 3,
  .c 11, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv37339], .c 3, .c 853, .c 7,
  .c 3, .c 23, .c 283, .c 3, .c 809, .c 5, .c 3, .c 59, .c 19, .c 3, .c 5, .c 11, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv1021],
]
private theorem h0382c27 : checkBlock 3136259 128 b0382c27 = true := by
  decide +kernel

private def b0382c28 : List Row := [
  .c 3, .c 17, .c 127, .c 3, .c 13, .c 5, .c 3, .c 11, .p pv17 [pv2,pv3,pv5,pv104551], .c 3, .c 5,
  .c 79, .c 3, .c 41, .p pv3 [pv2,pv3,pv522757], .c 3, .c 919, .c 13, .c 3, .c 7, .c 5, .c 3,
  .c 61, .p pv17 [pv2,pv3,pv5,pv7,pv1867], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv83,pv3779],
  .c 11, .c 3, .c 19, .c 23, .c 3, .c 359, .c 5, .c 3, .p pv2 [pv2,pv7,pv13,pv1231], .c 73, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv19,pv13757], .c 3, .c 13, .p pv2 [pv2,pv3,pv7,pv17,pv23,pv191], .c 3,
  .p pv5 [pv2,pv11,pv142573], .c 7, .c 3, .c 229, .c 5, .c 3, .c 17, .c 409, .c 3, .c 5, .c 13,
  .c 3, .p pv7 [pv2,pv5,pv7,pv44809], .p pv5 [pv2,pv3,pv130693], .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv31,pv50591], .c 5, .c 3, .p pv3 [pv2,pv23,pv17047], .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv101,pv647], .c 3, .c 11, .c 173, .c 3, .p pv2 [pv2,pv13,pv120641], .c 29,
  .c 3, .c 31, .c 5, .c 3, .c 7, .c 61, .c 3, .c 5, .c 17, .c 3, .c 19, .c 7, .c 3, .c 397, .c 53,
  .c 3, .c 157, .c 5, .c 3, .c 71, .c 1301, .c 3, .c 5, .c 23, .c 3, .c 7, .c 151, .c 3, .c 11,
  .c 19, .c 3, .c 47, .c 5, .c 3, .c 67, .c 1039, .c 3, .c 5, .c 251, .c 3, .c 769, .c 983, .c 3,
  .c 13, .p pv3 [pv2,pv3,pv353,pv1481], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv12253],
]
private theorem h0382c28 : checkBlock 3136515 128 b0382c28 = true := by
  decide +kernel

private def b0382c29 : List Row := [
  .c 11, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv47,pv71], .c 13, .c 3, .c 41, .c 17, .c 3,
  .c 11, .c 5, .c 3, .p pv7 [pv2,pv7,pv224057], .c 263, .c 3, .c 5, .c 43, .c 3, .c 827, .c 139,
  .c 3, .p pv3 [pv2,pv196051], .c 7, .c 3, .c 17, .c 5, .c 3, .c 193, .c 197, .c 3, .c 5, .c 11,
  .c 3, .p pv3 [pv2,pv5,pv7,pv17,pv659], .c 19, .c 3, .c 7, .p pv23 [pv2,pv3,pv11,pv13,pv457],
  .c 3, .c 59, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv522811], .c 3, .c 421,
  .c 67, .c 3, .p pv2 [pv2,pv784219], .c 233, .c 3, .c 73, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5,
  .c 37, .c 3, .c 23, .c 7, .c 3, .p pv2 [pv2,pv1568453], .p pv2 [pv2,pv3,pv17,pv15377], .c 3,
  .c 13, .c 5, .c 3, .c 19, .c 31, .c 3, .c 5, .c 751, .c 3, .c 7, .p pv11 [pv2,pv3,pv79,pv1103],
  .c 3, .c 211, .c 13, .c 3, .p pv5 [pv2,pv17,pv257,pv359], .c 5, .c 3, .p pv2 [pv2,pv811,pv967],
  .c 41, .c 3, .c 5, .c 19, .c 3, .p pv3 [pv2,pv5,pv9803], .c 599, .c 3, .c 509, .c 11, .c 3,
  .c 7, .c 5, .c 3, .c 43, .c 1009, .c 3, .c 5, .c 7, .c 3, .c 11, .c 17, .c 3, .c 719, .c 491,
  .c 3, .p pv2 [pv2,pv11,pv142591], .c 5, .c 3, .c 173, .c 79, .c 3, .c 5, .c 13, .c 3, .c 839,
  .c 401, .c 3,
]
private theorem h0382c29 : checkBlock 3136771 128 b0382c29 = true := by
  decide +kernel

private def b0382c30 : List Row := [
  .c 17, .c 7, .c 3, .c 19, .c 5, .c 3, .c 23, .c 821, .c 3, .c 5, .c 61, .c 3,
  .p pv2 [pv2,pv5,pv7,pv8963], .c 419, .c 3, .c 7, .p pv2 [pv2,pv3,pv174281], .c 3,
  .p pv5 [pv2,pv23,pv47,pv1451], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 97, .c 3,
  .p pv7 [pv2,pv5,pv78427], .p pv11 [pv2,pv3,pv13,pv37,pv1087], .c 3, .p pv5 [pv2,pv1568543],
  .c 59, .c 3, .p pv2 [pv2,pv7,pv181,pv619], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 31, .c 3,
  .c 353, .c 7, .c 3, .p pv2 [pv2,pv367,pv2137], .c 37, .c 3, .c 11, .c 5, .c 3, .c 17, .c 23,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv65357], .c 3, .c 7, .p pv5 [pv2,pv3,pv522857], .c 3, .c 13,
  .c 577, .c 3, .c 383, .c 5, .c 3, .p pv7 [pv2,pv1568579], .c 89, .c 3, .c 5, .c 11, .c 3,
  .p pv7 [pv2,pv5,pv313717], .c 13, .c 3, .c 23, .p pv3 [pv2,pv3,pv11,pv47533], .c 3, .c 7, .c 5,
  .c 3, .c 11, .c 29, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv11,pv23,pv31], .c 47, .c 3, .c 59,
  .p pv7 [pv2,pv3,pv67,pv1951], .c 3, .c 499, .c 5, .c 3, .c 113, .c 1033, .c 3, .c 5, .c 347,
  .c 3, .c 17, .c 11, .c 3, .c 43, .c 7, .c 3, .p pv5 [pv2,pv19,pv82559], .c 5, .c 3, .c 29,
  .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv43573], .c 3, .c 19, .p pv29 [pv2,pv3,pv31,pv101,pv167],
  .c 3, .c 7, .c 23, .c 3, .c 181, .c 5, .c 3, .c 41, .c 7,
]
private theorem h0382c30 : checkBlock 3137027 128 b0382c30 = true := by
  decide +kernel

private def b0382c31 : List Row := [
  .c 3, .c 5, .c 1571, .c 3, .c 61, .c 31, .c 3, .c 47, .c 11, .c 3, .c 13, .c 5, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv5,pv11,pv3169], .c 3, .c 5, .c 83, .c 3, .c 11, .c 7, .c 3, .c 79, .c 13,
  .c 3, .c 17, .c 5, .c 3, .c 89, .c 37, .c 3, .c 5, .c 107, .c 3, .c 7, .c 239, .c 3,
  .p pv2 [pv2,pv19,pv41281], .c 211, .c 3, .c 101, .c 5, .c 3, .c 139,
  .p pv3 [pv2,pv3,pv5,pv104579], .c 3, .c 5, .c 1061, .c 3, .c 13, .c 1721, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv53,pv4933], .c 3, .c 7, .c 5, .c 3, .p pv13 [pv2,pv11,pv142609], .c 17, .c 3,
  .c 5, .c 7, .c 3, .c 947, .c 19, .c 3, .c 31, .c 71, .c 3, .c 29, .c 5, .c 3, .c 167, .c 11,
  .c 3, .c 5, .c 137, .c 3, .c 53, .c 41, .c 3, .p pv5 [pv2,pv13,pv120671], .c 7, .c 3, .c 11,
  .c 5, .c 3, .c 13, .p pv11 [pv2,pv3,pv5,pv52291], .c 3, .c 5, .c 73, .c 3,
  .p pv7 [pv2,pv5,pv7,pv19,pv337], .c 1579, .c 3, .c 7, .c 31, .c 3, .c 83, .c 5, .c 3, .c 19,
  .c 7, .c 3, .c 5, .c 11, .c 3, .c 1019, .c 17, .c 3, .p pv2 [pv2,pv991,pv1583],
  .p pv2 [pv2,pv3,pv11,pv19,pv139], .c 3, .p pv3 [pv2,pv7,pv179,pv313], .c 5, .c 3, .c 7,
  .p pv31 [pv2,pv3,pv5,pv17,pv769], .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv11,pv2593], .c 7,
  .c 3, .c 13,
]
private theorem h0382c31 : checkBlock 3137283 128 b0382c31 = true := by
  decide +kernel

def rows0382 : List Row :=
  b0382c00 ++ b0382c01 ++ b0382c02 ++ b0382c03 ++ b0382c04 ++ b0382c05 ++ b0382c06 ++ b0382c07 ++
  b0382c08 ++ b0382c09 ++ b0382c10 ++ b0382c11 ++ b0382c12 ++ b0382c13 ++ b0382c14 ++ b0382c15 ++
  b0382c16 ++ b0382c17 ++ b0382c18 ++ b0382c19 ++ b0382c20 ++ b0382c21 ++ b0382c22 ++ b0382c23 ++
  b0382c24 ++ b0382c25 ++ b0382c26 ++ b0382c27 ++ b0382c28 ++ b0382c29 ++ b0382c30 ++ b0382c31

attribute [local irreducible] checkBlock checkRows checkPrime

theorem checked0382 : checkBlock 3129347 4096 rows0382 = true :=
  checkBlock_append h0382c00 (
    checkBlock_append h0382c01 (
    checkBlock_append h0382c02 (
    checkBlock_append h0382c03 (
    checkBlock_append h0382c04 (
    checkBlock_append h0382c05 (
    checkBlock_append h0382c06 (
    checkBlock_append h0382c07 (
    checkBlock_append h0382c08 (
    checkBlock_append h0382c09 (
    checkBlock_append h0382c10 (
    checkBlock_append h0382c11 (
    checkBlock_append h0382c12 (
    checkBlock_append h0382c13 (
    checkBlock_append h0382c14 (
    checkBlock_append h0382c15 (
    checkBlock_append h0382c16 (
    checkBlock_append h0382c17 (
    checkBlock_append h0382c18 (
    checkBlock_append h0382c19 (
    checkBlock_append h0382c20 (
    checkBlock_append h0382c21 (
    checkBlock_append h0382c22 (
    checkBlock_append h0382c23 (
    checkBlock_append h0382c24 (
    checkBlock_append h0382c25 (
    checkBlock_append h0382c26 (
    checkBlock_append h0382c27 (
    checkBlock_append h0382c28 (
    checkBlock_append h0382c29 (
    checkBlock_append h0382c30 (
    h0382c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
