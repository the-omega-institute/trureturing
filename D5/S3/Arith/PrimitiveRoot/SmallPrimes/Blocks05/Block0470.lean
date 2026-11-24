/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks05/Block0470
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks05/Block0470.checked0470
   digest: Kernel proof of checker success on extended consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table046
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table052
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table059
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table068
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table080
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table081
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table097
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table121
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table160
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table163
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table165
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table170
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table174
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table181
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table189
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table202
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table222
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables03.Table246

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0470c00 : List Row := [
  .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv1483], .c 3, .p pv2 [pv2,pv5,pv71,pv2707],
  .p pv3 [pv2,pv3,pv43,pv47,pv317], .c 3, .c 19, .c 257, .c 3, .c 313, .c 5, .c 3, .c 7, .c 11,
  .c 3, .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv13,pv29569], .c 7, .c 3, .p pv3 [pv2,pv61,pv7877],
  .c 29, .c 3, .c 11, .c 5, .c 3, .c 17, .c 67, .c 3, .c 5, .c 1213, .c 3, .c 7, .c 1061, .c 3,
  .c 151, .c 13, .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv227,pv8467], .p pv2 [pv2,pv3,pv5,pv64067],
  .c 3, .c 5, .c 11, .c 3, .c 31, .c 691, .c 3, .c 29, .c 491, .c 3, .c 7, .c 5, .c 3, .c 11,
  .c 149, .c 3, .c 5, .c 7, .c 3, .c 13, .c 103, .c 3, .p pv2 [pv2,pv29,pv191,pv347],
  .p pv7 [pv2,pv3,pv320339], .c 3, .c 829, .c 5, .c 3, .p pv7 [pv2,pv7,pv37,pv41,pv181], .c 1093,
  .c 3, .c 5, .c 13, .c 3, .c 17, .c 11, .c 3, .p pv3 [pv2,pv1877], .c 7, .c 3, .c 109, .c 5,
  .c 3, .p pv2 [pv2,pv17,pv56531], .p pv13 [pv2,pv3,pv5,pv97,pv1321], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv106781], .c 3, .p pv3 [pv2,pv5,pv7,pv13729], .c 613, .c 3, .c 7, .c 773, .c 3,
  .p pv2 [pv2,pv961033], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 113, .c 3, .c 23, .c 29, .c 3,
  .c 43, .c 11, .c 3, .c 127, .c 5, .c 3, .c 7, .c 383, .c 3, .c 5, .c 47, .c 3, .c 11, .c 7,
  .c 3,
]
private theorem h0470c00 : checkBlock 3843931 128 b0470c00 = true := by
  decide +kernel

private def b0470c01 : List Row := [
  .p pv2 [pv2,pv31,pv62003], .c 37, .c 3, .c 17, .c 5, .c 3, .p pv7 [pv2,pv709,pv2711], .c 41,
  .c 3, .c 5, .c 97, .c 3, .c 7, .c 19, .c 3, .c 13, .c 79, .c 3, .c 229, .c 5, .c 3,
  .p pv2 [pv2,pv83,pv11579], .c 769, .c 3, .c 5, .c 1571, .c 3, .p pv13 [pv2,pv5,pv29,pv1657],
  .c 13, .c 3, .c 11, .c 53, .c 3, .c 7, .c 5, .c 3, .c 67, .c 17, .c 3, .c 5, .c 7, .c 3, .c 47,
  .p pv5 [pv2,pv3,pv283], .c 3, .p pv2 [pv2,pv961069], .c 31, .c 3, .c 41, .c 5, .c 3, .c 19,
  .c 11, .c 3, .c 5, .c 223, .c 3, .p pv2 [pv2,pv5,pv37,pv1039],
  .p pv3 [pv2,pv3,pv7,pv11,pv53,pv157], .c 3, .p pv2 [pv2,pv1922153], .c 7, .c 3, .c 11, .c 5,
  .c 3, .c 1327, .c 13, .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv7,pv54919],
  .p pv5 [pv2,pv3,pv106787], .c 3, .c 7, .p pv2 [pv2,pv3,pv449,pv1427], .c 3,
  .p pv5 [pv2,pv61,pv31511], .c 5, .c 3, .c 149, .c 7, .c 3, .c 5, .c 11, .c 3, .c 281, .c 17,
  .c 3, .c 193, .c 751, .c 3, .c 13, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 401, .c 3,
  .p pv13 [pv2,pv5,pv11,pv34949], .c 7, .c 3, .c 17, .c 13, .c 3, .c 19, .c 5, .c 3,
  .p pv3 [pv2,pv53,pv9067], .c 37, .c 3, .c 5, .c 127, .c 3, .c 7, .c 11, .c 3, .c 23, .c 503,
  .c 3, .p pv3 [pv2,pv241,pv997], .c 5, .c 3, .p pv7 [pv2,pv13,pv147863], .c 19,
]
private theorem h0470c01 : checkBlock 3844187 128 b0470c01 = true := by
  decide +kernel

private def b0470c02 : List Row := [
  .c 3, .c 5, .c 41, .c 3, .c 13, .c 293, .c 3, .c 131, .c 47, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv961117], .c 853, .c 3, .c 5, .c 7, .c 3, .c 199, .c 277, .c 3, .c 389, .c 11,
  .c 3, .c 719, .c 5, .c 3, .c 17, .c 29, .c 3, .c 5, .c 167, .c 3, .c 11, .c 983, .c 3, .c 19,
  .c 7, .c 3, .c 353, .c 5, .c 3, .c 13, .c 359, .c 3, .c 5, .p pv13 [pv2,pv3,pv19,pv8431], .c 3,
  .p pv23 [pv2,pv5,pv7,pv3923], .c 571, .c 3, .c 7, .p pv2 [pv2,pv3,pv269,pv397], .c 3, .c 47,
  .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv41,pv9377], .c 523, .c 3,
  .c 11, .c 71, .c 3, .p pv7 [pv2,pv7,pv311,pv883], .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv128153], .c 3, .c 5, .c 601, .c 3, .c 17, .c 7, .c 3, .c 13, .c 619, .c 3,
  .p pv2 [pv2,pv19,pv50587], .c 5, .c 3, .p pv2 [pv2,pv17,pv73,pv1549], .c 11, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv640771], .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv961159], .c 191, .c 3, .c 11,
  .c 5, .c 3, .p pv3 [pv2,pv109,pv4409], .c 31, .c 3, .c 5, .c 23, .c 3, .c 67,
  .p pv3 [pv2,pv3,pv640777], .c 3, .p pv2 [pv2,pv7,pv101,pv2719], .c 17, .c 3, .c 7, .c 5, .c 3,
  .c 1447, .c 103, .c 3, .c 5, .c 7, .c 3, .c 73, .c 41, .c 3, .p pv3 [pv2,pv480587],
]
private theorem h0470c02 : checkBlock 3844443 128 b0470c02 = true := by
  decide +kernel

private def b0470c03 : List Row := [
  .c 227, .c 3, .c 17, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .p pv13 [pv2,pv3,pv43,pv7451], .c 3,
  .c 71, .c 827, .c 3, .c 563, .c 7, .c 3, .c 29, .c 5, .c 3, .c 1433, .c 47, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv293], .c 3, .p pv11 [pv2,pv5,pv7,pv13], .c 11, .c 3, .c 7, .c 43, .c 3, .c 13,
  .c 5, .c 3, .c 61, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv12323], .c 3, .c 37, .c 19, .c 3,
  .c 449, .c 13, .c 3, .c 239, .c 5, .c 3, .c 7, .p pv19 [pv2,pv3,pv5,pv89], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv31,pv2953], .c 3, .c 467, .c 7, .c 3, .c 269, .c 11, .c 3,
  .p pv5 [pv2,pv17,pv113083], .c 5, .c 3, .p pv2 [pv2,pv13,pv73939], .c 107, .c 3, .c 5, .c 31,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv211,pv3037], .c 3, .p pv5 [pv2,pv1922423], .c 29, .c 3, .c 59,
  .c 5, .c 3, .c 19, .p pv7 [pv2,pv3,pv5,pv64081], .c 3, .c 5, .c 13, .c 3, .c 1063, .c 17, .c 3,
  .p pv2 [pv2,pv7,pv353,pv389], .c 139, .c 3, .c 7, .c 5, .c 3, .c 89, .c 61, .c 3, .c 5, .c 7,
  .c 3, .p pv3 [pv2,pv5,pv38449], .c 1109, .c 3, .c 11, .p pv11 [pv2,pv3,pv11867], .c 3, .c 151,
  .c 5, .c 3, .c 13, .p pv7 [pv2,pv3,pv5,pv179], .c 3, .c 5, .p pv3 [pv2,pv3,pv227,pv941], .c 3,
  .c 43, .c 23, .c 3, .c 383, .c 7, .c 3, .p pv5 [pv2,pv1922471], .c 5, .c 3,
  .p pv2 [pv2,pv271,pv3547], .c 11, .c 3,
]
private theorem h0470c03 : checkBlock 3844699 128 b0470c03 = true := by
  decide +kernel

private def b0470c04 : List Row := [
  .c 5, .p pv5 [pv2,pv3,pv23,pv13931], .c 3, .c 31, .p pv2 [pv2,pv3,pv11,pv6473], .c 3, .c 7,
  .c 101, .c 3, .c 11, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv509,pv1259], .c 3,
  .c 53, .c 421, .c 3, .c 13, .p pv7 [pv2,pv3,pv213611], .c 3, .c 37, .c 5, .c 3, .c 7, .c 19,
  .c 3, .c 5, .c 11, .c 3, .c 41, .c 7, .c 3, .p pv2 [pv2,pv17,pv113089],
  .p pv13 [pv2,pv3,pv11,pv29129], .c 3, .p pv3 [pv2,pv239,pv2011], .c 5, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv5,pv37,pv433], .c 3, .c 5, .c 1277, .c 3, .c 7, .c 211, .c 3,
  .p pv3 [pv2,pv73,pv823], .c 367, .c 3, .c 67, .c 5, .c 3, .c 251, .c 23, .c 3, .c 5, .c 17,
  .c 3, .c 29, .c 11, .c 3, .c 19, .c 59, .c 3, .c 7, .c 5, .c 3, .c 179, .c 13, .c 3, .c 5, .c 7,
  .c 3, .c 17, .p pv5 [pv2,pv3,pv131,pv1223], .c 3, .c 23, .p pv3 [pv2,pv3,pv640853], .c 3,
  .p pv2 [pv2,pv1922561], .c 5, .c 3, .c 73, .c 929, .c 3, .c 5, .c 839, .c 3, .c 83,
  .p pv3 [pv2,pv3,pv7,pv30517], .c 3, .c 31, .c 7, .c 3, .c 13, .c 5, .c 3,
  .p pv13 [pv2,pv1922579], .c 1409, .c 3, .c 5, .c 79, .c 3, .c 11, .p pv2 [pv2,pv3,pv320431],
  .c 3, .c 7, .c 13, .c 3, .p pv5 [pv2,pv11,pv19,pv9199], .c 5, .c 3, .c 43, .c 7, .c 3, .c 5,
  .c 29, .c 3, .c 19, .c 53, .c 3, .c 59, .c 23,
]
private theorem h0470c04 : checkBlock 3844955 128 b0470c04 = true := by
  decide +kernel

private def b0470c05 : List Row := [
  .c 3, .c 17, .c 5, .c 3, .c 7, .p pv89 [pv2,pv3,pv5,pv19,pv3373], .c 3, .c 5, .c 331, .c 3,
  .c 13, .c 7, .c 3, .c 11, .c 19, .c 3, .c 131, .c 5, .c 3, .c 359, .p pv2 [pv2,pv3,pv5,pv1709],
  .c 3, .c 5, .c 13, .c 3, .c 7, .p pv3 [pv2,pv3,pv37,pv17321], .c 3, .c 41, .c 1873, .c 3,
  .p pv3 [pv2,pv101,pv4759], .c 5, .c 3, .p pv7 [pv2,pv23,pv179,pv467], .c 11, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv71209], .c 3, .p pv2 [pv2,pv5,pv563,pv683], .p pv5 [pv2,pv3,pv11,pv29131],
  .c 3, .p pv5 [pv2,pv7,pv13,pv19,pv139], .c 37, .c 3, .c 7, .c 5, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv5,pv7,pv18311], .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv251,pv383], .c 263,
  .c 3, .p pv5 [pv2,pv1922663], .p pv7 [pv2,pv3,pv80111], .c 3, .c 31, .c 5, .c 3, .c 1039,
  .p pv2 [pv2,pv3,pv5,pv7121], .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv76907], .c 19, .c 3,
  .p pv2 [pv2,pv961339], .c 7, .c 3, .p pv2 [pv2,pv53,pv36277], .c 5, .c 3, .c 11, .c 29, .c 3,
  .c 5, .c 1949, .c 3, .p pv2 [pv2,pv5,pv7,pv11,pv227], .c 17, .c 3, .c 7,
  .p pv17 [pv2,pv3,pv320449], .c 3, .c 23, .c 5, .c 3, .c 47, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv640901], .c 3, .c 109, .c 11, .c 3, .c 17, .c 1483, .c 3, .c 89, .c 5, .c 3,
  .c 7, .c 41, .c 3, .c 5, .c 587, .c 3, .p pv3 [pv2,pv5,pv61,pv197], .c 7, .c 3, .c 37,
  .p pv23 [pv2,pv3,pv19,pv937], .c 3, .c 137, .c 5, .c 3, .p pv2 [pv2,pv29,pv66301],
  .p pv17 [pv2,pv3,pv5,pv64091], .c 3, .c 5,
]
private theorem h0470c05 : checkBlock 3845211 128 b0470c05 = true := by
  decide +kernel

private def b0470c06 : List Row := [
  .c 19, .c 3, .c 7, .c 83, .c 3, .p pv2 [pv2,pv199,pv4831], .c 11, .c 3, .c 79, .c 5, .c 3,
  .p pv3 [pv2,pv31,pv7753], .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv163,pv983], .c 3, .c 11, .c 113,
  .c 3, .c 337, .c 167, .c 3, .c 7, .c 5, .c 3, .c 17, .c 37, .c 3, .c 5, .c 7, .c 3, .c 23,
  .c 43, .c 3, .p pv3 [pv2,pv17,pv7069], .p pv2 [pv2,pv3,pv213641], .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv137341], .c 1607, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv13,pv83], .c 3, .c 59,
  .p pv2 [pv2,pv3,pv7,pv19,pv61,pv79], .c 3, .c 11, .c 7, .c 3, .c 71, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv174799], .c 19, .c 3, .c 5, .c 17, .c 3, .c 277, .p pv13 [pv2,pv3,pv53411],
  .c 3, .c 7, .c 67, .c 3, .c 29, .c 5, .c 3, .c 1051, .c 7, .c 3, .c 5, .c 173, .c 3, .c 13,
  .c 23, .c 3, .c 53, .c 109, .c 3, .c 11, .c 5, .c 3, .c 7, .c 79, .c 3, .c 5, .c 13, .c 3,
  .p pv29 [pv2,pv5,pv76913], .c 7, .c 3, .c 19, .c 163, .c 3, .p pv5 [pv2,pv43,pv97,pv461], .c 5,
  .c 3, .c 23, .c 1249, .c 3, .c 5, .c 11, .c 3, .c 7, .c 443, .c 3, .c 107, .c 17, .c 3,
  .p pv2 [pv2,pv23,pv41801], .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv4273], .c 3, .c 5, .c 181,
  .c 3, .c 103, .c 73, .c 3, .p pv2 [pv2,pv7,pv2803], .c 29, .c 3,
]
private theorem h0470c06 : checkBlock 3845467 128 b0470c06 = true := by
  decide +kernel

private def b0470c07 : List Row := [
  .c 7, .c 5, .c 3, .c 113, .c 829, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv17,pv11311], .c 11,
  .c 3, .p pv2 [pv2,pv1922873], .c 239, .c 3, .p pv3 [pv2,pv19,pv25301], .c 5, .c 3, .c 41, .c 23,
  .c 3, .c 5, .c 31, .c 3, .c 19, .c 1373, .c 3, .c 13, .c 7, .c 3, .c 643, .c 5, .c 3, .c 307,
  .c 17, .c 3, .c 5, .c 59, .c 3, .c 347, .c 13, .c 3, .c 7, .c 11, .c 3, .c 431, .c 5, .c 3,
  .c 151, .c 7, .c 3, .c 5, .c 409, .c 3, .c 11, .c 1237, .c 3, .p pv2 [pv2,pv961459], .c 53,
  .c 3, .c 167, .c 5, .c 3, .c 7, .c 1399, .c 3, .c 5, .c 71, .c 3, .p pv2 [pv2,pv5,pv31,pv6203],
  .c 7, .c 3, .c 61, .c 47, .c 3, .p pv3 [pv2,pv157,pv1531], .c 5, .c 3, .c 823, .c 13, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv11,pv58271], .c 3, .c 7, .c 17, .c 3, .c 11, .c 23, .c 3,
  .p pv5 [pv2,pv1922951], .c 5, .c 3, .p pv2 [pv2,pv11,pv87407], .c 193, .c 3, .c 5, .c 103, .c 3,
  .p pv3 [pv2,pv5,pv13,pv43], .c 19, .c 3, .c 17, .p pv7 [pv2,pv3,pv37,pv61,pv71], .c 3, .c 7,
  .c 5, .c 3, .p pv2 [pv2,pv503,pv3823], .c 11, .c 3, .c 5, .c 7, .c 3, .c 29, .c 31, .c 3, .c 79,
  .c 13, .c 3, .c 11, .c 5, .c 3, .c 541, .c 83, .c 3, .c 5, .p pv13 [pv2,pv3,pv191,pv839],
]
private theorem h0470c07 : checkBlock 3845723 128 b0470c07 = true := by
  decide +kernel

private def b0470c08 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv19,pv29,pv349], .p pv7 [pv2,pv3,pv7,pv91571], .c 3,
  .p pv2 [pv2,pv809,pv2377], .c 7, .c 3, .p pv3 [pv2,pv480749], .c 5, .c 3, .c 19, .c 67, .c 3,
  .c 5, .c 11, .c 3, .c 13, .p pv2 [pv2,pv3,pv17,pv1109], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv11,pv19,pv3067], .c 3, .p pv5 [pv2,pv521,pv3691], .c 5, .c 3, .c 11, .c 7,
  .c 3, .c 5, .c 13, .c 3, .c 1163, .c 389, .c 3, .c 281, .c 43, .c 3, .c 1559, .c 5, .c 3, .c 7,
  .c 227, .c 3, .c 5, .c 29, .c 3, .c 991, .c 7, .c 3, .c 31, .c 439, .c 3, .c 23, .c 5, .c 3,
  .c 13, .c 1453, .c 3, .c 5, .c 17, .c 3, .c 7, .p pv7 [pv2,pv3,pv13,pv3793], .c 3, .c 1021,
  .p pv2 [pv2,pv3,pv7,pv31,pv211], .c 3, .c 19, .c 5, .c 3, .c 241, .c 151, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv443,pv1447], .c 3, .c 17, .p pv2 [pv2,pv3,pv19,pv5623], .c 3, .c 83, .c 11,
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv17,pv163,pv347], .c 19, .c 3, .c 5, .c 7, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv269,pv2383], .c 3, .c 13, .c 41, .c 3, .c 179, .c 5, .c 3, .c 599, .c 101,
  .c 3, .c 5, .c 37, .c 3, .p pv13 [pv2,pv5,pv384619], .c 13, .c 3, .p pv2 [pv2,pv961549], .c 7,
  .c 3, .p pv2 [pv2,pv67,pv28703], .c 5, .c 3, .p pv3 [pv2,pv19,pv3163], .c 293, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv11,pv17,pv857], .c 3, .c 23, .p pv3 [pv2,pv3,pv107,pv1997], .c 3, .c 7,
  .p pv11 [pv2,pv3,pv197,pv1627], .c 3, .c 17,
]
private theorem h0470c08 : checkBlock 3845979 128 b0470c08 = true := by
  decide +kernel

private def b0470c09 : List Row := [
  .c 5, .c 3, .p pv11 [pv2,pv11,pv174829], .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv19,pv33739], .c 3,
  .c 41, .c 283, .c 3, .p pv3 [pv2,pv421,pv571], .p pv2 [pv2,pv3,pv13,pv5479], .c 3, .c 31, .c 5,
  .c 3, .c 7, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv15263], .c 3, .p pv3 [pv2,pv5,pv96157],
  .c 7, .c 3, .p pv5 [pv2,pv149,pv12907], .p pv7 [pv2,pv3,pv227,pv353], .c 3, .c 11, .c 5, .c 3,
  .c 29, .c 17, .c 3, .c 5, .c 43, .c 3, .c 7, .c 23, .c 3, .c 757, .c 211, .c 3, .c 13, .c 5,
  .c 3, .c 103, .p pv2 [pv2,pv3,pv5,pv42737], .c 3, .c 5, .c 11, .c 3, .c 19, .c 157, .c 3,
  .p pv2 [pv2,pv7,pv274739], .c 13, .c 3, .c 7, .c 5, .c 3, .c 11, .c 1013, .c 3, .c 5, .c 7,
  .c 3, .p pv2 [pv2,pv5,pv11,pv73,pv479], .p pv5 [pv2,pv3,pv37,pv8663], .c 3, .c 827, .c 19, .c 3,
  .c 101, .c 5, .c 3, .p pv2 [pv2,pv7,pv13,pv10567], .c 863, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv320533], .c 3, .c 13, .c 11, .c 3, .c 113, .c 7, .c 3,
  .p pv2 [pv2,pv137,pv7019], .c 5, .c 3, .c 1907, .p pv2 [pv2,pv3,pv5,pv17,pv419], .c 3, .c 5,
  .c 13, .c 3, .c 79, .c 47, .c 3, .c 7, .p pv3 [pv2,pv3,pv97,pv2203], .c 3, .c 73, .c 5, .c 3,
  .c 31, .c 7, .c 3, .c 5, .c 313, .c 3, .p pv2 [pv2,pv5,pv192323], .p pv3 [pv2,pv3,pv641077],
  .c 3, .p pv2 [pv2,pv13,pv239,pv619], .c 11, .c 3, .c 29, .c 5, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv5,pv11,pv31,pv47], .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv91583], .c 3,
]
private theorem h0470c09 : checkBlock 3846235 128 b0470c09 = true := by
  decide +kernel

private def b0470c10 : List Row := [
  .c 11, .c 7, .c 3, .c 23, .p pv3 [pv2,pv3,pv641083], .c 3, .c 1129, .c 5, .c 3,
  .p pv2 [pv2,pv961627], .c 31, .c 3, .c 5, .c 1181, .c 3, .c 7,
  .p pv29 [pv2,pv3,pv17,pv43,pv877], .c 3, .c 47, .p pv13 [pv2,pv3,pv7,pv53], .c 3, .c 397, .c 5,
  .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv64109], .c 3, .c 5, .c 139, .c 3, .c 331, .c 131, .c 3,
  .c 11, .c 607, .c 3, .c 7, .c 5, .c 3, .c 19, .p pv7 [pv2,pv3,pv5,pv7,pv13,pv1409], .c 3, .c 5,
  .c 7, .c 3, .c 53, .c 13, .c 3, .c 907, .c 23, .c 3, .p pv3 [pv2,pv60103], .c 5, .c 3, .c 61,
  .c 11, .c 3, .c 5, .c 17, .c 3, .c 587, .p pv2 [pv2,pv3,pv7,pv11,pv23,pv181], .c 3,
  .p pv3 [pv2,pv480827], .c 7, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv961657], .c 37, .c 3, .c 5,
  .c 163, .c 3, .c 17, .p pv2 [pv2,pv3,pv557,pv1151], .c 3, .c 7, .p pv29 [pv2,pv3,pv13,pv12329],
  .c 3, .p pv2 [pv2,pv961663], .c 5, .c 3, .p pv2 [pv2,pv17,pv23,pv4919], .c 7, .c 3, .c 5, .c 11,
  .c 3, .c 67, .p pv7 [pv2,pv3,pv26713], .c 3, .c 421, .c 467, .c 3, .c 19, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv1583], .c 3, .c 5, .c 31, .c 3, .p pv3 [pv2,pv5,pv11,pv13,pv269], .c 7,
  .c 3, .p pv2 [pv2,pv1923353], .c 17, .c 3, .c 13, .c 5, .c 3, .c 109, .c 19, .c 3, .c 5, .c 23,
  .c 3, .c 7, .c 11, .c 3, .c 43, .c 13, .c 3, .c 17, .c 5,
]
private theorem h0470c10 : checkBlock 3846491 128 b0470c10 = true := by
  decide +kernel

private def b0470c11 : List Row := [
  .c 3, .c 373, .p pv3 [pv2,pv3,pv5,pv23,pv223], .c 3, .c 5, .c 107, .c 3,
  .p pv3 [pv2,pv5,pv17,pv5657], .c 29, .c 3, .p pv5 [pv2,pv7,pv11,pv24979],
  .p pv23 [pv2,pv3,pv80141], .c 3, .c 7, .c 5, .c 3, .c 37, .c 1553, .c 3, .c 5, .c 7, .c 3,
  .c 13, .c 53, .c 3, .c 19, .c 11, .c 3, .c 1201, .c 5, .c 3, .c 47, .c 17, .c 3, .c 5, .c 13,
  .c 3, .c 11, .c 43, .c 3, .c 571, .c 7, .c 3, .p pv3 [pv2,pv11,pv1987], .c 5, .c 3, .c 419,
  .p pv13 [pv2,pv3,pv5,pv32057], .c 3, .c 5, .c 89, .c 3, .c 71, .c 37, .c 3, .c 7, .c 59, .c 3,
  .p pv5 [pv2,pv17,pv113143], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv11,pv151,pv193], .c 3, .c 73, .c 31, .c 3, .c 11, .c 179, .c 3, .c 1087, .c 5,
  .c 3, .c 7, .c 263, .c 3, .c 5, .c 41, .c 3, .c 19, .c 7, .c 3, .p pv2 [pv2,pv961729], .c 887,
  .c 3, .c 97, .c 5, .c 3, .p pv3 [pv2,pv240433], .c 11, .c 3, .c 5, .c 29, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv11,pv19429], .c 3, .c 13, .c 19, .c 3, .c 11, .c 5, .c 3, .c 1709,
  .p pv11 [pv2,pv3,pv5,pv13,pv137], .c 3, .c 5, .c 83, .c 3, .c 107, .c 13, .c 3, .c 59, .c 563,
  .c 3, .c 7, .c 5, .c 3, .c 41, .p pv97 [pv2,pv3,pv5,pv7,pv2617], .c 3, .c 5, .c 7, .c 3, .c 37,
]
private theorem h0470c11 : checkBlock 3846747 128 b0470c11 = true := by
  decide +kernel

private def b0470c12 : List Row := [
  .c 23, .c 3, .c 31, .c 569, .c 3, .p pv2 [pv2,pv13,pv167,pv443], .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv97,pv661], .c 3, .c 5, .c 73, .c 3, .c 149, .c 257, .c 3,
  .p pv2 [pv2,pv59,pv16301], .c 7, .c 3, .c 1913, .c 5, .c 3, .c 17, .c 13, .c 3, .c 5, .c 1301,
  .c 3, .p pv3 [pv2,pv5,pv7,pv27479], .c 11, .c 3, .c 7, .c 31, .c 3, .c 67, .c 5, .c 3,
  .p pv11 [pv2,pv107,pv17977], .c 7, .c 3, .c 5, .c 61, .c 3, .c 47, .p pv5 [pv2,pv3,pv320591],
  .c 3, .c 137, .c 1697, .c 3, .c 13, .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .c 17, .c 3, .c 1109,
  .c 7, .c 3, .p pv5 [pv2,pv163,pv11801], .c 11, .c 3, .c 83, .c 5, .c 3, .c 19, .c 23, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv467,pv1373], .c 3, .c 7, .c 41, .c 3, .p pv2 [pv2,pv961789],
  .p pv19 [pv2,pv3,pv7,pv19,pv1607], .c 3, .c 211, .c 5, .c 3, .c 29, .c 281, .c 3, .c 5, .c 19,
  .c 3, .c 13, .c 239, .c 3, .c 23, .c 347, .c 3, .c 7, .c 5, .c 3, .c 557,
  .p pv37 [pv2,pv3,pv5,pv7,pv229], .c 3, .c 5, .c 7, .c 3, .c 127, .c 59, .c 3, .c 11, .c 17,
  .c 3, .c 37, .c 5, .c 3, .c 379, .c 883, .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv18859], .c 3,
  .p pv3 [pv2,pv5,pv96181], .p pv2 [pv2,pv3,pv7,pv139,pv659], .c 3, .c 179, .c 7, .c 3, .c 17,
  .c 5, .c 3,
]
private theorem h0470c12 : checkBlock 3847003 128 b0470c12 = true := by
  decide +kernel

private def b0470c13 : List Row := [
  .c 13, .c 11, .c 3, .c 5, .c 199, .c 3, .p pv29 [pv2,pv5,pv7,pv17,pv53,pv61],
  .p pv5 [pv2,pv3,pv11,pv13,pv19,pv59], .c 3, .c 7, .c 23, .c 3, .c 11, .c 5, .c 3, .c 163, .c 7,
  .c 3, .c 5, .c 37, .c 3, .c 1847, .p pv3 [pv2,pv3,pv23,pv9293], .c 3, .c 769,
  .p pv2 [pv2,pv3,pv320609], .c 3, .c 191, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 11, .c 3,
  .c 59, .c 7, .c 3, .c 13, .c 43, .c 3, .c 29, .c 5, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv5,pv13,pv1973], .c 3, .c 5, .p pv5 [pv2,pv3,pv106871], .c 3, .c 7, .c 13,
  .c 3, .c 19, .c 719, .c 3, .c 47, .c 5, .c 3, .c 31, .c 89, .c 3, .c 5, .c 271, .c 3, .c 677,
  .c 11, .c 3, .p pv2 [pv2,pv7,pv313,pv439], .c 41, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv37,pv67,pv97], .c 1787, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv47,pv4093],
  .c 17, .c 3, .c 263, .c 53, .c 3, .p pv3 [pv2,pv480929], .c 5, .c 3, .p pv7 [pv2,pv7,pv274817],
  .c 13, .c 3, .c 5, .c 503, .c 3, .p pv2 [pv2,pv5,pv76949], .c 61, .c 3, .c 17, .c 7, .c 3,
  .c 23, .c 5, .c 3, .p pv2 [pv2,pv43,pv22369], .p pv3 [pv2,pv3,pv5,pv11,pv89,pv131], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv491,pv653], .c 3, .c 11, .c 457, .c 3, .c 7, .p pv31 [pv2,pv3,pv29,pv691],
  .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv1923749], .c 7, .c 3, .c 5, .c 269, .c 3, .c 43, .c 167,
]
private theorem h0470c13 : checkBlock 3847259 128 b0470c13 = true := by
  decide +kernel

private def b0470c14 : List Row := [
  .c 3, .c 29, .c 13, .c 3, .c 1319, .c 5, .c 3, .c 7, .c 509, .c 3, .c 5, .c 79, .c 3, .c 673,
  .c 7, .c 3, .c 11, .p pv2 [pv2,pv3,pv83,pv3863], .c 3, .p pv3 [pv2,pv30059], .c 5, .c 3, .c 17,
  .c 47, .c 3, .c 5, .c 59, .c 3, .c 7, .c 1447, .c 3, .p pv3 [pv2,pv17,pv19,pv1489], .c 251,
  .c 3, .p pv5 [pv2,pv1923791], .c 5, .c 3, .p pv2 [pv2,pv53,pv18149], .c 11, .c 3, .c 5, .c 13,
  .c 3, .c 23, .p pv2 [pv2,pv3,pv11,pv97,pv601], .c 3, .c 197, .c 67, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv383,pv5023], .p pv13 [pv2,pv3,pv5,pv7,pv9161], .c 3, .c 5, .c 7, .c 3, .c 83,
  .c 19, .c 3, .p pv3 [pv2,pv13,pv61,pv1213], .p pv3 [pv2,pv3,pv433,pv1481], .c 3, .c 787, .c 5,
  .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv113,pv227], .c 3, .c 5, .c 11, .c 3, .c 17,
  .p pv5 [pv2,pv3,pv7,pv13,pv29], .c 3, .c 37, .c 7, .c 3, .p pv3 [pv2,pv480959], .c 5, .c 3,
  .c 11, .c 661, .c 3, .c 5, .p pv3 [pv2,pv3,pv41,pv15641], .c 3, .c 29, .c 23, .c 3, .c 7, .c 97,
  .c 3, .c 71, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 1283, .c 3,
  .p pv3 [pv2,pv5,pv29,pv31,pv107], .c 11, .c 3, .c 13, .c 17, .c 3, .c 281, .c 5, .c 3, .c 7,
  .c 37, .c 3, .c 5, .c 19, .c 3, .c 31, .c 7, .c 3, .c 73, .c 1303, .c 3, .c 17, .c 5, .c 3,
  .c 43,
]
private theorem h0470c14 : checkBlock 3847515 128 b0470c14 = true := by
  decide +kernel

private def b0470c15 : List Row := [
  .c 103, .c 3, .c 5, .p pv11 [pv2,pv3,pv149,pv269], .c 3, .c 7,
  .p pv3 [pv2,pv3,pv31,pv137,pv151], .c 3, .c 487, .c 11, .c 3, .c 1151, .c 5, .c 3,
  .p pv7 [pv2,pv139,pv13841], .c 613, .c 3, .c 5, .c 29, .c 3, .c 11, .c 31, .c 3,
  .p pv3 [pv2,pv7,pv68711], .c 61, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv961957], .c 13, .c 3,
  .c 5, .c 7, .c 3, .c 193, .c 47, .c 3, .c 167, .p pv13 [pv2,pv3,pv17,pv9431], .c 3, .c 53, .c 5,
  .c 3, .p pv2 [pv2,pv7,pv274847], .c 19, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv173,pv337], .c 3,
  .p pv11 [pv2,pv5,pv13,pv29599], .p pv5 [pv2,pv3,pv7,pv409], .c 3, .c 11, .c 7, .c 3, .c 13,
  .c 5, .c 3, .c 37, .c 41, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv4111], .c 3, .c 659, .c 73, .c 3,
  .c 7, .c 13, .c 3, .c 157, .c 5, .c 3, .c 137, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv37,pv17333],
  .c 3, .p pv23 [pv2,pv5,pv449,pv857], .c 17, .c 3, .c 19, .p pv2 [pv2,pv3,pv307,pv2089], .c 3,
  .c 11, .c 5, .c 3, .c 7, .c 283, .c 3, .c 5, .c 1091, .c 3, .c 13, .c 7, .c 3, .c 17, .c 23,
  .c 3, .c 41, .c 5, .c 3, .c 1409, .c 29, .c 3, .c 5, .c 11, .c 3, .c 7, .c 463, .c 3, .c 743,
  .c 31, .c 3, .c 311, .c 5, .c 3, .c 11, .c 67, .c 3, .c 5, .p pv5 [pv2,pv3,pv80167], .c 3,
  .p pv2 [pv2,pv5,pv11,pv17491], .c 1579, .c 3,
]
private theorem h0470c15 : checkBlock 3847771 128 b0470c15 = true := by
  decide +kernel

private def b0470c16 : List Row := [
  .c 43, .p pv2 [pv2,pv3,pv320669], .c 3, .c 7, .c 5, .c 3, .c 13, .c 107, .c 3, .c 5, .c 7, .c 3,
  .c 19, .c 11, .c 3, .p pv3 [pv2,pv137,pv3511], .p pv2 [pv2,pv3,pv71,pv3011], .c 3, .c 61, .c 5,
  .c 3, .c 17, .c 433, .c 3, .c 5, .c 191, .c 3, .c 251, .p pv3 [pv2,pv3,pv7,pv91621], .c 3,
  .c 97, .c 7, .c 3, .c 89, .c 5, .c 3, .p pv2 [pv2,pv59,pv32611],
  .p pv7 [pv2,pv3,pv5,pv101,pv127], .c 3, .c 5, .c 23, .c 3, .c 37, .c 43, .c 3, .c 7, .c 11,
  .c 3, .c 31, .c 5, .c 3, .c 71, .c 7, .c 3, .c 5, .c 17, .c 3, .c 11, .c 13, .c 3, .c 569,
  .c 1021, .c 3, .c 23, .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv8017], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv4363], .c 3, .c 17, .c 7, .c 3, .p pv3 [pv2,pv23,pv10457], .c 691, .c 3,
  .c 103, .c 5, .c 3, .c 1693, .p pv7 [pv2,pv3,pv5,pv128273], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv29153], .c 3, .c 7, .c 19, .c 3, .c 11, .p pv11 [pv2,pv3,pv7,pv13,pv881],
  .c 3, .c 29, .c 5, .c 3, .c 41, .c 13, .c 3, .c 5, .c 127, .c 3, .p pv7 [pv2,pv5,pv347,pv1109],
  .p pv17 [pv2,pv3,pv160343], .c 3, .p pv2 [pv2,pv7,pv137437], .c 17, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv79,pv6089], .c 11, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv13,pv19,pv41],
  .p pv3 [pv2,pv3,pv11,pv199,pv293], .c 3, .c 163, .p pv2 [pv2,pv3,pv23,pv73,pv191], .c 3, .c 11,
  .c 5, .c 3, .c 19, .c 97,
]
private theorem h0470c16 : checkBlock 3848027 128 b0470c16 = true := by
  decide +kernel

private def b0470c17 : List Row := [
  .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv103,pv479], .c 3, .c 23, .p pv2 [pv2,pv3,pv7,pv15271], .c 3,
  .c 1429, .c 7, .c 3, .p pv5 [pv2,pv101,pv19051], .c 5, .c 3, .c 31, .c 223, .c 3, .c 5, .c 11,
  .c 3, .c 179, .c 619, .c 3, .c 7, .c 29, .c 3, .c 37, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv67,pv3191], .c 3, .c 13, .c 1823, .c 3, .p pv2 [pv2,pv647,pv1487],
  .p pv3 [pv2,pv3,pv17,pv29,pv1301], .c 3, .c 1619, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5, .c 13,
  .c 3, .p pv2 [pv2,pv5,pv317,pv607], .c 7, .c 3, .c 29, .c 103, .c 3, .c 19, .c 5, .c 3, .c 431,
  .c 907, .c 3, .c 5, .c 37, .c 3, .c 7, .c 67, .c 3, .p pv3 [pv2,pv11,pv13,pv29],
  .p pv2 [pv2,pv3,pv7,pv10181], .c 3, .c 349, .c 5, .c 3, .c 13, .c 19, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv53,pv2017], .c 3, .c 113, .c 17, .c 3, .p pv7 [pv2,pv7,pv274889], .c 11, .c 3,
  .c 7, .c 5, .c 3, .c 191, .c 83, .c 3, .c 5, .c 7, .c 3, .c 11, .p pv7 [pv2,pv3,pv5939], .c 3,
  .c 17, .c 263, .c 3, .c 1931, .c 5, .c 3, .c 53, .p pv2 [pv2,pv3,pv5,pv61,pv701], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv80177], .c 3, .c 47, .c 29, .c 3, .c 13, .c 7, .c 3, .p pv3 [pv2,pv60133],
  .c 5, .c 3, .c 1373, .c 23, .c 3, .c 5, .p pv7 [pv2,pv3,pv11,pv19,pv31], .c 3,
  .p pv2 [pv2,pv5,pv7,pv54979], .c 13, .c 3, .c 7,
]
private theorem h0470c17 : checkBlock 3848283 128 b0470c17 = true := by
  decide +kernel

private def b0470c18 : List Row := [
  .p pv2 [pv2,pv3,pv89,pv7207], .c 3, .c 43, .c 5, .c 3, .c 509, .c 7, .c 3, .c 5, .c 31, .c 3,
  .c 29, .p pv3 [pv2,pv3,pv17,pv12577], .c 3, .c 23, .p pv37 [pv2,pv3,pv160357], .c 3,
  .p pv3 [pv2,pv7,pv13,pv97,pv109], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 1637, .c 3,
  .p pv13 [pv2,pv5,pv23,pv29,pv577], .c 7, .c 3, .p pv2 [pv2,pv17,pv56597],
  .p pv3 [pv2,pv3,pv13,pv16447], .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv127,pv947], .c 13, .c 3,
  .c 5, .c 239, .c 3, .c 7, .p pv3 [pv2,pv3,pv641437], .c 3, .c 83, .c 37, .c 3, .c 73, .c 5,
  .c 3, .p pv7 [pv2,pv277,pv6947], .c 1747, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv13,pv31,pv191], .p pv2 [pv2,pv3,pv106907], .c 3, .p pv3 [pv2,pv7,pv4909],
  .c 19, .c 3, .c 7, .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv7,pv41,pv149], .c 3, .c 5, .c 7,
  .c 3, .c 17, .c 107, .c 3, .p pv5 [pv2,pv1924343], .c 13, .c 3, .c 887, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv17,pv103,pv157], .c 53, .c 3, .c 5, .p pv2 [pv2,pv3,pv29,pv73,pv101], .c 3,
  .c 41, .c 11, .c 3, .p pv2 [pv2,pv19,pv89,pv569], .c 7, .c 3, .c 1031, .c 5, .c 3, .c 367,
  .c 173, .c 3, .c 5, .c 1801, .c 3, .c 13, .c 31, .c 3, .c 7, .c 17, .c 3,
  .p pv3 [pv2,pv41,pv5867], .c 5, .c 3, .c 353, .c 7, .c 3, .c 5, .c 13, .c 3, .c 139, .c 19,
  .c 3, .c 37, .c 11, .c 3, .c 17, .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv11,pv107,pv109], .c 3,
]
private theorem h0470c18 : checkBlock 3848539 128 b0470c18 = true := by
  decide +kernel

private def b0470c19 : List Row := [
  .c 5, .c 23, .c 3, .c 11, .c 7, .c 3, .c 53, .p pv7 [pv2,pv3,pv160367], .c 3,
  .p pv2 [pv2,pv11,pv87473], .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv23,pv2789], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv641471], .c 3, .c 7, .p pv5 [pv2,pv3,pv13,pv257], .c 3,
  .p pv2 [pv2,pv31,pv31039], .c 71, .c 3, .c 23, .c 5, .c 3, .c 19, .c 17, .c 3, .c 5, .c 281,
  .c 3, .p pv2 [pv2,pv5,pv53,pv3631], .c 97, .c 3, .c 11, .p pv2 [pv2,pv3,pv17,pv19,pv331], .c 3,
  .c 7, .c 5, .c 3, .c 1181, .p pv23 [pv2,pv3,pv5,pv7,pv29,pv79], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv384889], .c 113, .c 3, .c 13, .c 109, .c 3, .p pv5 [pv2,pv17,pv6659], .c 5,
  .c 3, .c 29, .c 11, .c 3, .c 5, .c 61, .c 3, .p pv3 [pv2,pv5,pv96223], .c 13, .c 3, .c 233,
  .c 7, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv29,pv66361], .p pv2 [pv2,pv3,pv5,pv21383], .c 3,
  .c 5, .p pv3 [pv2,pv3,pv641491], .c 3, .p pv7 [pv2,pv5,pv7,pv1571], .c 17, .c 3, .c 7, .c 79,
  .c 3, .c 19, .c 5, .c 3, .p pv3 [pv2,pv149,pv3229], .c 7, .c 3, .c 5, .c 11, .c 3, .c 23, .c 59,
  .c 3, .c 17, .c 127, .c 3, .c 1733, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 103, .c 3, .c 241,
  .c 7, .c 3, .p pv3 [pv2,pv43,pv67,pv167], .c 53, .c 3, .p pv5 [pv2,pv31,pv62081], .c 5, .c 3,
  .p pv2 [pv2,pv962257], .p pv3 [pv2,pv3,pv5,pv42767], .c 3, .c 5, .c 179, .c 3, .c 7, .c 11,
  .c 3, .c 829, .c 139,
]
private theorem h0470c19 : checkBlock 3848795 128 b0470c19 = true := by
  decide +kernel

private def b0470c20 : List Row := [
  .c 3, .c 13, .c 5, .c 3, .c 43, .p pv11 [pv2,pv3,pv5,pv64151], .c 3, .c 5, .c 1087, .c 3, .c 73,
  .c 23, .c 3, .c 19, .c 13, .c 3, .c 7, .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv7,pv18329],
  .c 3, .c 5, .c 7, .c 3, .c 59, .c 1667, .c 3, .p pv2 [pv2,pv17,pv113209], .c 11, .c 3,
  .p pv3 [pv2,pv29,pv47,pv353], .c 5, .c 3, .c 23, .c 41, .c 3, .c 5, .p pv3 [pv2,pv3,pv641521],
  .c 3, .c 11, .p pv5 [pv2,pv3,pv7,pv45823], .c 3, .p pv3 [pv2,pv240571], .c 7, .c 3,
  .p pv5 [pv2,pv11,pv23,pv7607], .c 5, .c 3, .p pv2 [pv2,pv521,pv1847],
  .p pv3 [pv2,pv3,pv5,pv67,pv383], .c 3, .c 5, .c 13, .c 3, .c 61, .c 593, .c 3, .c 7, .c 157,
  .c 3, .c 131, .c 5, .c 3, .c 859, .c 7, .c 3, .c 5, .p pv11 [pv2,pv3,pv11,pv58321], .c 3, .c 17,
  .p pv5 [pv2,pv3,pv193,pv277], .c 3, .c 11, .c 29, .c 3, .c 41, .c 5, .c 3, .c 7, .c 23, .c 3,
  .c 5, .c 67, .c 3, .c 37, .c 7, .c 3, .c 443, .c 19, .c 3, .p pv3 [pv2,pv113,pv2129], .c 5,
  .c 3, .c 31, .c 11, .c 3, .c 5, .c 311, .c 3, .c 7, .c 47, .c 3, .c 23, .c 17, .c 3, .c 11,
  .c 5, .c 3, .p pv2 [pv2,pv263,pv3659], .c 347, .c 3, .c 5, .c 449, .c 3,
  .p pv3 [pv2,pv5,pv23,pv523], .c 61, .c 3, .c 13, .c 137, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv1924649], .c 31, .c 3, .c 5,
]
private theorem h0470c20 : checkBlock 3849051 128 b0470c20 = true := by
  decide +kernel

private def b0470c21 : List Row := [
  .c 7, .c 3, .c 457, .c 13, .c 3, .c 43, .p pv3 [pv2,pv3,pv11,pv19441], .c 3, .c 1951, .c 5,
  .c 3, .c 11, .c 317, .c 3, .c 5, .c 53, .c 3, .p pv2 [pv2,pv5,pv11,pv17497], .c 19, .c 3, .c 47,
  .c 7, .c 3, .c 419, .c 5, .c 3, .p pv13 [pv2,pv1924679], .c 17, .c 3, .c 5, .c 41, .c 3,
  .c 1217, .c 11, .c 3, .c 7, .p pv7 [pv2,pv3,pv13,pv17,pv2903], .c 3, .p pv5 [pv2,pv463,pv4157],
  .c 5, .c 3, .p pv2 [pv2,pv683,pv1409], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv59,pv5437], .c 3,
  .p pv3 [pv2,pv5,pv19,pv1013], .c 43, .c 3, .c 71, .p pv13 [pv2,pv3,pv41,pv163], .c 3, .c 101,
  .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv64157], .c 3, .c 5, .c 557, .c 3, .c 29, .c 7, .c 3,
  .p pv2 [pv2,pv73,pv13183], .c 11, .c 3, .c 13, .c 5, .c 3, .c 41, .c 739, .c 3, .c 5, .c 19,
  .c 3, .c 7, .c 17, .c 3, .p pv2 [pv2,pv61,pv139,pv227], .c 13, .c 3, .c 307, .c 5, .c 3,
  .p pv7 [pv2,pv71,pv27109], .c 467, .c 3, .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv41,pv229], .c 241,
  .c 3, .c 17, .p pv3 [pv2,pv3,pv71287], .c 3, .c 7, .c 5, .c 3, .c 73,
  .p pv101 [pv2,pv3,pv5,pv7,pv23,pv797], .c 3, .c 5, .c 7, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv103,pv6229], .c 3, .c 11, .p pv11 [pv2,pv3,pv160397], .c 3, .c 19, .c 5, .c 3,
  .c 107, .p pv2 [pv2,pv3,pv5,pv83,pv773], .c 3, .c 5, .c 13, .c 3, .c 337, .c 109, .c 3, .c 359,
  .c 7, .c 3,
]
private theorem h0470c21 : checkBlock 3849307 128 b0470c21 = true := by
  decide +kernel

private def b0470c22 : List Row := [
  .c 137, .c 5, .c 3, .p pv3 [pv2,pv120299], .c 11, .c 3, .c 5, .c 197, .c 3,
  .p pv2 [pv2,pv5,pv7,pv31,pv887], .p pv3 [pv2,pv3,pv11,pv17,pv47,pv73], .c 3, .c 7, .c 853, .c 3,
  .c 11, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 1471, .c 3, .c 31, .c 41, .c 3,
  .p pv3 [pv2,pv17,pv14153], .c 67, .c 3, .c 83, .c 5, .c 3, .c 7, .c 941, .c 3, .c 5, .c 11,
  .c 3, .c 643, .c 7, .c 3, .c 19, .c 61, .c 3, .p pv2 [pv2,pv962413], .c 5, .c 3, .c 11, .c 43,
  .c 3, .c 5, .c 17, .c 3, .c 7, .c 31, .c 3, .c 13, .p pv3 [pv2,pv3,pv7,pv30553], .c 3,
  .p pv2 [pv2,pv571,pv3371], .c 5, .c 3, .c 181, .c 59, .c 3, .c 5, .c 131, .c 3, .c 17, .c 11,
  .c 3, .p pv2 [pv2,pv7,pv83,pv3313], .c 397, .c 3, .c 7, .c 5, .c 3, .c 229, .c 29, .c 3, .c 5,
  .c 7, .c 3, .c 631, .c 373, .c 3, .p pv3 [pv2,pv11,pv41,pv97], .c 37, .c 3,
  .p pv5 [pv2,pv13,pv19,pv7793], .c 5, .c 3, .c 79, .c 127, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv541,pv593], .c 3, .c 19, .c 23, .c 3, .p pv5 [pv2,pv31,pv2003], .c 7, .c 3,
  .c 599, .c 5, .c 3, .c 29, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv23,pv547], .c 3, .c 11,
  .p pv5 [pv2,pv3,pv20051], .c 3, .c 7, .c 19, .c 3, .c 17, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5,
  .c 47,
]
private theorem h0470c22 : checkBlock 3849563 128 b0470c22 = true := by
  decide +kernel

private def b0470c23 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv13,pv17,pv67], .p pv5 [pv2,pv3,pv71293], .c 3,
  .p pv2 [pv2,pv271,pv7103], .p pv41 [pv2,pv3,pv31,pv79,pv131], .c 3, .c 13, .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv5347], .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv11,pv13,pv641], .c 3, .c 167,
  .c 7, .c 3, .c 11, .c 13, .c 3, .p pv5 [pv2,pv149,pv12919], .c 5, .c 3, .c 311, .c 17, .c 3,
  .c 5, .c 1721, .c 3, .c 7, .c 139, .c 3, .c 37, .p pv11 [pv2,pv3,pv7,pv17,pv337], .c 3, .c 61,
  .c 5, .c 3, .c 761, .c 11, .c 3, .c 5, .c 79, .c 3, .c 13, .c 19, .c 3, .c 409, .c 43, .c 3,
  .c 7, .c 5, .c 3, .p pv3 [pv2,pv269,pv1789], .c 491, .c 3, .c 5, .c 7, .c 3, .c 41,
  .p pv3 [pv2,pv3,pv173,pv3709], .c 3, .c 23, .p pv2 [pv2,pv3,pv229,pv467], .c 3, .c 29, .c 5,
  .c 3, .c 131, .c 37, .c 3, .c 5, .c 11, .c 3, .c 197, .c 17, .c 3, .p pv3 [pv2,pv13,pv37019],
  .c 7, .c 3, .c 31, .c 5, .c 3, .c 11, .c 1033, .c 3, .c 5, .p pv2 [pv2,pv3,pv320833], .c 3,
  .c 401, .p pv2 [pv2,pv3,pv13,pv16453], .c 3, .c 7, .p pv13 [pv2,pv3,pv19,pv8443], .c 3,
  .p pv2 [pv2,pv962503], .c 5, .c 3, .c 101, .c 7, .c 3, .c 5, .c 19, .c 3, .c 809, .c 11, .c 3,
  .c 103, .c 23, .c 3, .p pv5 [pv2,pv7,pv275003], .c 5, .c 3, .c 7, .c 89, .c 3, .c 5, .c 263,
  .c 3, .p pv3 [pv2,pv5,pv163,pv1181], .c 7, .c 3, .c 13, .c 29, .c 3, .p pv3 [pv2,pv37,pv13007],
]
private theorem h0470c23 : checkBlock 3849819 128 b0470c23 = true := by
  decide +kernel

private def b0470c24 : List Row := [
  .c 5, .c 3, .c 53, .p pv29 [pv2,pv3,pv5,pv13,pv617], .c 3, .c 5, .c 307, .c 3, .c 7, .c 13,
  .c 3, .c 271, .c 11, .c 3, .c 19, .c 5, .c 3, .c 17, .c 137, .c 3, .c 5, .c 71, .c 3, .c 11,
  .c 431, .c 3, .c 29, .p pv7 [pv2,pv3,pv26737], .c 3, .c 7, .c 5, .c 3, .c 1091, .c 19, .c 3,
  .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv77003], .p pv5 [pv2,pv3,pv160423], .c 3, .c 193,
  .p pv3 [pv2,pv3,pv13,pv3797], .c 3, .c 59, .c 5, .c 3, .c 31, .c 13, .c 3, .c 5, .c 17, .c 3,
  .c 107, .c 37, .c 3, .c 11, .c 7, .c 3, .c 47, .c 5, .c 3, .p pv11 [pv2,pv11,pv19,pv61,pv151],
  .c 607, .c 3, .c 5, .c 109, .c 3, .c 17, .c 313, .c 3, .c 7, .p pv2 [pv2,pv3,pv213901], .c 3,
  .c 13, .c 5, .c 3, .c 89, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv19,pv433], .c 3,
  .p pv3 [pv2,pv5,pv47], .c 29, .c 3, .p pv5 [pv2,pv23,pv83701], .c 13, .c 3, .c 11, .c 5, .c 3,
  .c 7, .c 379, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv91673], .c 3, .p pv19 [pv2,pv5,pv385027], .c 7,
  .c 3, .p pv2 [pv2,pv962569], .c 17, .c 3, .c 1283, .c 5, .c 3, .c 67, .c 53, .c 3, .c 5, .c 11,
  .c 3, .c 7, .p pv5 [pv2,pv3,pv79,pv8123], .c 3, .c 797, .c 149, .c 3, .c 17, .c 5, .c 3, .c 11,
  .c 577, .c 3, .c 5, .c 13, .c 3,
]
private theorem h0470c24 : checkBlock 3850075 128 b0470c24 = true := by
  decide +kernel

private def b0470c25 : List Row := [
  .c 19, .c 547, .c 3, .c 1609, .p pv2 [pv2,pv3,pv23,pv27901], .c 3, .c 7, .c 5, .c 3, .c 43,
  .c 41, .c 3, .c 5, .c 7, .c 3, .c 23, .c 11, .c 3, .c 1597, .c 19, .c 3,
  .p pv2 [pv2,pv599,pv1607], .c 5, .c 3, .c 13, .c 17, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv31,pv127,pv163], .c 3, .p pv17 [pv2,pv5,pv385039],
  .p pv71 [pv2,pv3,pv7,pv13,pv41,pv43], .c 3, .c 53, .c 7, .c 3, .p pv2 [pv2,pv401,pv4801], .c 5,
  .c 3, .c 1861, .c 983, .c 3, .c 5, .c 29, .c 3, .p pv2 [pv2,pv5,pv7,pv3929], .c 67, .c 3, .c 7,
  .c 11, .c 3, .c 41, .c 5, .c 3, .c 139, .c 7, .c 3, .c 5, .c 1493, .c 3, .c 11, .c 23, .c 3,
  .c 13, .p pv2 [pv2,pv3,pv59,pv73,pv149], .c 3, .p pv5 [pv2,pv7,pv11,pv2273], .c 5, .c 3, .c 7,
  .c 1433, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv23,pv1993], .c 3, .p pv3 [pv2,pv5,pv48131], .c 7,
  .c 3, .c 641, .p pv7 [pv2,pv3,pv53479], .c 3, .c 1697, .c 5, .c 3, .c 23, .c 857, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv19447], .c 3, .c 7, .c 127, .c 3, .c 11, .c 167, .c 3, .c 331, .c 5,
  .c 3, .c 239, .c 73, .c 3, .c 5, .c 659, .c 3, .c 31, .c 71, .c 3, .p pv5 [pv2,pv7,pv275039],
  .c 163, .c 3, .c 7, .c 5, .c 3, .c 19, .c 11, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv385057],
  .c 1103, .c 3, .c 277, .c 709, .c 3, .c 11, .c 5,
]
private theorem h0470c25 : checkBlock 3850331 128 b0470c25 = true := by
  decide +kernel

private def b0470c26 : List Row := [
  .c 3, .p pv3 [pv2,pv7,pv113,pv1217], .c 23, .c 3, .c 5, .c 19, .c 3, .c 227, .c 31, .c 3, .c 43,
  .c 7, .c 3, .c 13, .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv29,pv2213], .c 3, .c 5, .c 11, .c 3,
  .c 257, .p pv5 [pv2,pv3,pv17827], .c 3, .c 7, .c 13, .c 3, .c 109, .c 5, .c 3, .c 11, .c 7,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv40111], .c 3, .p pv2 [pv2,pv5,pv11,pv23,pv761], .c 47, .c 3,
  .c 1249, .c 433, .c 3, .c 19, .c 5, .c 3, .c 7, .c 479, .c 3, .c 5, .c 17, .c 3, .c 13, .c 7,
  .c 3, .c 79, .p pv17 [pv2,pv3,pv241,pv2663], .c 3, .p pv5 [pv2,pv83,pv23197], .c 5, .c 3,
  .c 487, .c 19, .c 3, .c 5, .c 13, .c 3, .c 7, .p pv13 [pv2,pv3,pv213929], .c 3, .c 31, .c 23,
  .c 3, .c 461, .c 5, .c 3, .c 157, .c 653, .c 3, .c 5, .c 61, .c 3, .c 191, .c 59, .c 3, .c 47,
  .c 11, .c 3, .c 7, .c 5, .c 3, .c 13, .c 463, .c 3, .c 5, .c 7, .c 3, .c 11, .c 499, .c 3,
  .c 19, .c 17, .c 3, .c 1297, .c 5, .c 3, .c 619, .c 1019, .c 3, .c 5, .c 173, .c 3,
  .p pv2 [pv2,pv5,pv385081], .p pv5 [pv2,pv3,pv7,pv37,pv59], .c 3, .c 823, .c 7, .c 3, .c 17,
  .c 5, .c 3, .p pv2 [pv2,pv227,pv4241], .p pv19 [pv2,pv3,pv5,pv42787], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv29173], .c 3, .p pv3 [pv2,pv5,pv7,pv17,pv809],
]
private theorem h0470c26 : checkBlock 3850587 128 b0470c26 = true := by
  decide +kernel

private def b0470c27 : List Row := [
  .c 41, .c 3, .c 7, .c 37, .c 3, .c 167, .c 5, .c 3, .c 757, .c 7, .c 3, .c 5, .c 23, .c 3,
  .c 59, .c 13, .c 3, .c 353, .c 1049, .c 3, .p pv2 [pv2,pv7,pv19,pv31,pv467], .c 5, .c 3, .c 7,
  .c 11, .c 3, .c 5, .c 859, .c 3, .c 19, .c 7, .c 3, .c 877, .p pv2 [pv2,pv3,pv17,pv43,pv439],
  .c 3, .c 11, .c 5, .c 3, .c 727, .p pv47 [pv2,pv3,pv5,pv19,pv563], .c 3, .c 5, .c 53, .c 3,
  .c 7, .c 137, .c 3, .p pv3 [pv2,pv23,pv20929], .c 19, .c 3, .c 691, .c 5, .c 3,
  .p pv2 [pv2,pv962737], .c 13, .c 3, .c 5, .c 11, .c 3, .c 211, .p pv2 [pv2,pv3,pv641827], .c 3,
  .p pv5 [pv2,pv7,pv41,pv6709], .c 71, .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv17 [pv2,pv3,pv5,pv7,pv53,pv173], .c 3, .c 5, .c 7, .c 3, .c 61, .c 17, .c 3, .c 29, .c 443,
  .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv7,pv307], .p pv2 [pv2,pv3,pv5,pv17,pv839], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv12343], .c 3, .c 127, .c 11, .c 3, .c 17, .c 7, .c 3, .c 53, .c 5, .c 3,
  .c 47, .p pv11 [pv2,pv3,pv5,pv71,pv113], .c 3, .c 5, .p pv3 [pv2,pv3,pv213947], .c 3, .c 23,
  .c 19, .c 3, .c 7, .p pv2 [pv2,pv3,pv641843], .c 3, .p pv5 [pv2,pv1925531], .c 5, .c 3, .c 1279,
  .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv320923], .c 3, .c 13, .p pv2 [pv2,pv3,pv213949], .c 3,
  .p pv5 [pv2,pv47,pv53,pv773], .c 11, .c 3, .c 67, .c 5, .c 3,
]
private theorem h0470c27 : checkBlock 3850843 128 b0470c27 = true := by
  decide +kernel

private def b0470c28 : List Row := [
  .c 7, .p pv19 [pv2,pv3,pv5,pv11,pv389], .c 3, .c 5, .c 13, .c 3, .c 11, .c 7, .c 3, .c 83,
  .c 89, .c 3, .c 43, .c 5, .c 3, .c 17, .c 277, .c 3, .c 5, .c 181, .c 3, .c 7, .c 23, .c 3,
  .p pv2 [pv2,pv13,pv17,pv8713], .p pv41 [pv2,pv3,pv7,pv19,pv127], .c 3, .c 113, .c 5, .c 3,
  .c 13, .c 31, .c 3, .c 5, .c 19, .c 3, .c 29, .p pv2 [pv2,pv3,pv13,pv211], .c 3, .c 11,
  .p pv2 [pv2,pv3,pv641863], .c 3, .c 7, .c 5, .c 3, .c 23, .c 97, .c 3, .c 5, .c 7, .c 3, .c 163,
  .c 149, .c 3, .c 137, .c 43, .c 3, .p pv2 [pv2,pv23,pv41,pv1021], .c 5, .c 3, .c 37, .c 11,
  .c 3, .c 5, .c 47, .c 3, .c 17, .c 317, .c 3, .c 13, .c 7, .c 3, .c 11, .c 5, .c 3, .c 1063,
  .c 107, .c 3, .c 5, .c 233, .c 3, .c 73, .c 13, .c 3, .c 7, .c 131, .c 3, .c 103, .c 5, .c 3,
  .p pv11 [pv2,pv1925639], .c 7, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv385129], .c 37, .c 3,
  .c 89, .c 17, .c 3, .p pv5 [pv2,pv7,pv13,pv3023], .c 5, .c 3, .c 7, .c 821, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv17,pv29,pv31], .c 3, .c 47, .c 7, .c 3, .c 23, .c 79, .c 3, .c 17, .c 5,
  .c 3, .c 827, .c 13, .c 3, .c 5, .c 31, .c 3, .c 7, .c 11,
]
private theorem h0470c28 : checkBlock 3851099 128 b0470c28 = true := by
  decide +kernel

private def b0470c29 : List Row := [
  .c 3, .c 19, .p pv3 [pv2,pv3,pv7,pv107,pv857], .c 3, .p pv2 [pv2,pv1925681], .c 5, .c 3,
  .p pv3 [pv2,pv47,pv10243], .p pv47 [pv2,pv3,pv5,pv42793], .c 3, .c 5,
  .p pv7 [pv2,pv3,pv19,pv41,pv103], .c 3, .c 43, .c 211, .c 3, .p pv2 [pv2,pv7,pv11,pv89,pv281],
  .p pv2 [pv2,pv3,pv11887], .c 3, .c 7, .c 5, .c 3, .p pv13 [pv2,pv379,pv5081], .c 17, .c 3, .c 5,
  .c 7, .c 3, .c 997, .p pv2 [pv2,pv3,pv139,pv2309], .c 3, .c 41, .c 11, .c 3,
  .p pv5 [pv2,pv1925711], .c 5, .c 3, .p pv2 [pv2,pv7,pv67,pv2053],
  .p pv11 [pv2,pv3,pv5,pv11,pv1061], .c 3, .c 5, .c 683, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv7,pv23,pv443], .c 3, .c 1399, .c 7, .c 3, .c 677, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv41,pv3613], .c 29, .c 3, .c 5, .c 43, .c 3, .c 13, .c 1427, .c 3, .c 7,
  .c 61, .c 3, .c 563, .c 5, .c 3, .c 389, .c 7, .c 3, .c 5, .c 13, .c 3, .c 149, .c 17, .c 3,
  .c 11, .c 19, .c 3, .c 941, .c 5, .c 3, .c 7, .c 167, .c 3, .c 5, .c 163, .c 3, .c 131, .c 7,
  .c 3, .c 17, .c 1511, .c 3, .c 179, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 23, .c 3, .c 7,
  .c 53, .c 3, .c 1097, .c 863, .c 3, .c 11, .c 5, .c 3, .c 59, .c 41, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv213977], .c 3, .c 647, .p pv5 [pv2,pv3,pv160483], .c 3,
  .p pv2 [pv2,pv7,pv43,pv457], .p pv3 [pv2,pv3,pv373,pv1721], .c 3, .c 7, .c 5, .c 3, .c 1381,
]
private theorem h0470c29 : checkBlock 3851355 128 b0470c29 = true := by
  decide +kernel

private def b0470c30 : List Row := [
  .p pv2 [pv2,pv3,pv5,pv7,pv18341], .c 3, .c 5, .c 7, .c 3, .c 1867, .c 19, .c 3, .c 13, .c 67,
  .c 3, .c 1699, .c 5, .c 3, .c 11, .p pv23 [pv2,pv3,pv5,pv13,pv823], .c 3, .c 5, .c 661, .c 3,
  .p pv11 [pv2,pv5,pv11,pv47,pv149], .c 13, .c 3, .c 31, .c 7, .c 3, .c 37, .c 5, .c 3, .c 53,
  .c 1889, .c 3, .c 5, .p pv2 [pv2,pv3,pv97,pv1103], .c 3, .c 157, .c 11, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv31,pv167], .c 3, .c 29, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 17, .c 3,
  .c 359, .p pv5 [pv2,pv3,pv743], .c 3, .c 1789, .c 31, .c 3, .c 61, .c 5, .c 3, .c 7, .c 13,
  .c 3, .c 5, .c 19, .c 3, .c 17, .c 7, .c 3, .p pv2 [pv2,pv1925873], .c 11, .c 3, .c 521, .c 5,
  .c 3, .p pv7 [pv2,pv17,pv113287], .p pv17 [pv2,pv3,pv5,pv11,pv1459], .c 3, .c 5,
  .p pv19 [pv2,pv3,pv71329], .c 3, .c 7, .c 97, .c 3, .c 379, .p pv3 [pv2,pv3,pv7,pv293,pv313],
  .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv103,pv9349], .c 47, .c 3, .c 5,
  .p pv29 [pv2,pv3,pv13,pv24691], .c 3, .p pv3 [pv2,pv5,pv19259], .c 79, .c 3,
  .p pv5 [pv2,pv7,pv275129], .c 13, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv1925909], .c 71, .c 3,
  .c 5, .c 7, .c 3, .c 89, .c 23, .c 3, .c 11, .p pv23 [pv2,pv3,pv29,pv47,pv157], .c 3, .c 17,
  .c 5, .c 3, .c 839, .c 19, .c 3, .c 5, .p pv5 [pv2,pv3,pv23,pv1163], .c 3, .c 13,
  .p pv5 [pv2,pv3,pv7,pv91711], .c 3,
]
private theorem h0470c30 : checkBlock 3851611 128 b0470c30 = true := by
  decide +kernel

private def b0470c31 : List Row := [
  .c 29, .c 7, .c 3, .p pv3 [pv2,pv120371], .c 5, .c 3, .c 23, .c 11, .c 3, .c 5, .c 13, .c 3,
  .c 103, .c 107, .c 3, .c 7, .p pv3 [pv2,pv3,pv263,pv2441], .c 3, .c 11, .c 5, .c 3, .c 41, .c 7,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv257,pv1249], .c 3, .c 769, .p pv3 [pv2,pv3,pv37,pv17351], .c 3,
  .c 19, .c 307, .c 3, .c 59, .c 5, .c 3, .c 7, .c 197, .c 3, .c 5, .c 11, .c 3, .c 109, .c 7,
  .c 3, .c 971, .c 37, .c 3, .c 71, .c 5, .c 3, .c 11, .c 23, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv160499], .c 3, .c 7, .c 29, .c 3, .c 53, .p pv2 [pv2,pv3,pv7,pv6551], .c 3,
  .p pv3 [pv2,pv59,pv8161], .c 5, .c 3, .c 1823, .p pv7 [pv2,pv3,pv5,pv107], .c 3, .c 5, .c 937,
  .c 3, .p pv2 [pv2,pv5,pv151,pv2551], .c 11, .c 3, .c 13, .p pv17 [pv2,pv3,pv173,pv1237], .c 3,
  .c 7, .c 5, .c 3, .c 31, .c 67, .c 3, .c 5, .c 7, .c 3, .c 19, .c 13, .c 3, .c 17,
  .p pv13 [pv2,pv3,pv80251], .c 3, .c 457, .c 5, .c 3, .p pv2 [pv2,pv7,pv275147], .c 1423, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv642011], .c 3, .c 293, .c 41, .c 3, .p pv2 [pv2,pv963019], .c 7, .c 3,
  .p pv2 [pv2,pv13,pv148157], .c 5, .c 3, .c 61, .c 31, .c 3, .c 5, .c 103, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv223,pv2879], .c 3, .c 7, .c 23, .c 3, .c 83, .c 5, .c 3, .c 79, .c 7,
]
private theorem h0470c31 : checkBlock 3851867 128 b0470c31 = true := by
  decide +kernel

def rows0470 : List Row :=
  b0470c00 ++ b0470c01 ++ b0470c02 ++ b0470c03 ++ b0470c04 ++ b0470c05 ++ b0470c06 ++ b0470c07 ++
  b0470c08 ++ b0470c09 ++ b0470c10 ++ b0470c11 ++ b0470c12 ++ b0470c13 ++ b0470c14 ++ b0470c15 ++
  b0470c16 ++ b0470c17 ++ b0470c18 ++ b0470c19 ++ b0470c20 ++ b0470c21 ++ b0470c22 ++ b0470c23 ++
  b0470c24 ++ b0470c25 ++ b0470c26 ++ b0470c27 ++ b0470c28 ++ b0470c29 ++ b0470c30 ++ b0470c31

theorem checked0470 : checkBlock 3843931 4096 rows0470 = true :=
  checkBlock_append h0470c00 (
    checkBlock_append h0470c01 (
    checkBlock_append h0470c02 (
    checkBlock_append h0470c03 (
    checkBlock_append h0470c04 (
    checkBlock_append h0470c05 (
    checkBlock_append h0470c06 (
    checkBlock_append h0470c07 (
    checkBlock_append h0470c08 (
    checkBlock_append h0470c09 (
    checkBlock_append h0470c10 (
    checkBlock_append h0470c11 (
    checkBlock_append h0470c12 (
    checkBlock_append h0470c13 (
    checkBlock_append h0470c14 (
    checkBlock_append h0470c15 (
    checkBlock_append h0470c16 (
    checkBlock_append h0470c17 (
    checkBlock_append h0470c18 (
    checkBlock_append h0470c19 (
    checkBlock_append h0470c20 (
    checkBlock_append h0470c21 (
    checkBlock_append h0470c22 (
    checkBlock_append h0470c23 (
    checkBlock_append h0470c24 (
    checkBlock_append h0470c25 (
    checkBlock_append h0470c26 (
    checkBlock_append h0470c27 (
    checkBlock_append h0470c28 (
    checkBlock_append h0470c29 (
    checkBlock_append h0470c30 (
    h0470c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
