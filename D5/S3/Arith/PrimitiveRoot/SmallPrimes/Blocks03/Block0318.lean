/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks03/Block0318
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks03/Block0318.checked0318
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table027
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table033
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table038
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table043
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table051
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table062
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table078
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table103
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table145

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0318c00 : List Row := [
  .c 3, .c 71, .c 17, .c 3, .c 1429, .c 43, .c 3, .p pv3 [pv2,pv23,pv7079], .c 5, .c 3, .c 1481,
  .p pv7 [pv2,pv3,pv5,pv17,pv1277], .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv59,pv223], .c 3,
  .p pv13 [pv2,pv5,pv19,pv13711], .c 101, .c 3, .c 11, .c 7, .c 3, .p pv5 [pv2,pv113,pv11527],
  .c 5, .c 3, .c 13, .c 461, .c 3, .c 5, .c 881, .c 3, .c 83, .c 271, .c 3, .c 7, .c 97, .c 3,
  .c 37, .c 5, .c 3, .p pv2 [pv2,pv139,pv9371], .c 7, .c 3, .c 5, .c 19, .c 3, .c 73, .c 1069,
  .c 3, .c 29, .p pv3 [pv2,pv3,pv144731], .c 3, .c 11, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv37,pv2347], .c 3, .c 5, .p pv17 [pv2,pv3,pv7,pv1723], .c 3, .c 41, .c 7,
  .c 3, .c 13, .p pv2 [pv2,pv3,pv61,pv3559], .c 3, .c 971, .c 5, .c 3, .c 17,
  .p pv23 [pv2,pv3,pv5,pv13,pv167], .c 3, .c 5, .c 11, .c 3, .c 7, .c 13, .c 3, .c 211, .c 751,
  .c 3, .c 19, .c 5, .c 3, .c 11, .p pv13 [pv2,pv3,pv5,pv9649], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv107,pv2029], .c 3, .c 43, .p pv2 [pv2,pv3,pv19,pv22853], .c 3, .c 311, .c 61,
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv157,pv8297], .c 19, .c 3, .c 5, .c 7, .c 3, .c 31, .c 11,
  .c 3, .c 139, .c 23, .c 3, .c 443, .c 5, .c 3, .p pv13 [pv2,pv7,pv46523], .c 13, .c 3, .c 5,
  .c 73, .c 3, .c 17, .p pv3 [pv2,pv3,pv7,pv23,pv29,pv31], .c 3, .c 193, .c 7, .c 3,
  .p pv3 [pv2,pv10177],
]
private theorem h0318c00 : checkBlock 2605059 128 b0318c00 = true := by
  decide +kernel

private def b0318c01 : List Row := [
  .c 5, .c 3, .p pv13 [pv2,pv17,pv19,pv37,pv109], .c 53, .c 3, .c 5, .c 43, .c 3, .c 29, .c 31,
  .c 3, .c 7, .c 11, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv23,pv28319], .c 7, .c 3, .c 5, .c 457,
  .c 3, .c 11, .p pv2 [pv2,pv3,pv67,pv6481], .c 3, .c 167, .c 13, .c 3,
  .p pv2 [pv2,pv7,pv11,pv769], .c 5, .c 3, .c 7, .c 59, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv17,pv41,pv89], .c 3, .p pv17 [pv2,pv5,pv260539], .c 7, .c 3, .c 863,
  .c 631, .c 3, .c 17, .c 5, .c 3, .p pv3 [pv2,pv13,pv6263], .p pv2 [pv2,pv3,pv5,pv28949], .c 3,
  .c 5, .c 23, .c 3, .c 7, .c 317, .c 3, .c 11, .c 37, .c 3, .p pv3 [pv2,pv19,pv61,pv281], .c 5,
  .c 3, .p pv7 [pv2,pv11,pv118429], .c 113, .c 3, .c 5, .c 13, .c 3, .c 19, .c 83, .c 3, .c 31,
  .c 131, .c 3, .c 7, .c 5, .c 3, .c 647, .c 11, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv53,pv1229], .p pv2 [pv2,pv3,pv11,pv13159], .c 3, .c 71, .c 19, .c 3, .c 11,
  .c 5, .c 3, .c 13, .p pv19 [pv2,pv3,pv5,pv193], .c 3, .c 5, .c 199, .c 3, .c 397, .c 1423, .c 3,
  .c 97, .c 7, .c 3, .p pv2 [pv2,pv17,pv197,pv389], .c 5, .c 3, .p pv3 [pv2,pv325691],
  .p pv3 [pv2,pv3,pv5,pv86851], .c 3, .c 5, .c 11, .c 3, .c 263, .p pv5 [pv2,pv3,pv43,pv10099],
  .c 3, .c 7, .c 383, .c 3, .c 173, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 877, .c 3,
]
private theorem h0318c01 : checkBlock 2605315 128 b0318c01 = true := by
  decide +kernel

private def b0318c02 : List Row := [
  .c 509, .c 17, .c 3, .c 13, .p pv7 [pv2,pv3,pv23,pv79,pv239], .c 3, .c 1019, .c 5, .c 3, .c 7,
  .c 41, .c 3, .c 5, .c 1217, .c 3, .c 23, .c 7, .c 3, .c 17, .p pv7 [pv2,pv3,pv4021], .c 3,
  .p pv2 [pv2,pv31,pv21013], .c 5, .c 3, .c 83, .c 29, .c 3, .c 5, .p pv2 [pv2,pv3,pv144757],
  .c 3, .c 7, .c 47, .c 3, .p pv2 [pv2,pv11,pv59219], .c 53, .c 3, .c 31, .c 5, .c 3, .c 293,
  .c 37, .c 3, .c 5, .c 79, .c 3, .p pv2 [pv2,pv5,pv19,pv6857], .p pv3 [pv2,pv3,pv73,pv661], .c 3,
  .c 113, .c 11, .c 3, .c 7, .c 5, .c 3, .c 19, .c 13, .c 3, .c 5, .c 7, .c 3, .c 11, .c 23, .c 3,
  .c 67, .c 101, .c 3, .c 179, .c 5, .c 3, .c 17, .c 97, .c 3, .c 5, .c 19, .c 3, .c 131, .c 257,
  .c 3, .c 47, .c 7, .c 3, .c 13, .c 5, .c 3, .c 23, .p pv7 [pv2,pv3,pv5,pv137,pv317], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv13,pv3037], .c 3, .p pv7 [pv2,pv5,pv7,pv1489], .p pv7 [pv2,pv3,pv36191],
  .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv23,pv37,pv1531], .c 5, .c 3, .p pv3 [pv2,pv11,pv29611],
  .c 7, .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv113,pv1153], .c 773, .c 3,
  .p pv2 [pv2,pv127,pv10259], .c 809, .c 3, .c 19, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 151,
  .c 3, .c 13, .c 7, .c 3, .c 239, .p pv2 [pv2,pv3,pv434303], .c 3, .c 11, .c 5,
]
private theorem h0318c02 : checkBlock 2605571 128 b0318c02 = true := by
  decide +kernel

private def b0318c03 : List Row := [
  .c 3, .c 31, .c 19, .c 3, .c 5, .c 13, .c 3, .c 7, .c 43, .c 3, .p pv5 [pv2,pv353,pv3691],
  .p pv59 [pv2,pv3,pv7,pv15511], .c 3, .c 29, .c 5, .c 3, .c 61, .c 149, .c 3, .c 5, .c 11, .c 3,
  .p pv7 [pv2,pv5,pv260587], .c 37, .c 3, .c 23, .c 17, .c 3, .c 7, .c 5, .c 3, .c 11, .c 31,
  .c 3, .c 5, .c 7, .c 3, .c 101, .c 1301, .c 3, .c 19, .p pv2 [pv2,pv3,pv397,pv547], .c 3, .c 17,
  .c 5, .c 3, .c 41, .c 1567, .c 3, .c 5, .p pv3 [pv2,pv3,pv19,pv22859], .c 3,
  .p pv23 [pv2,pv5,pv17,pv15329], .c 11, .c 3, .c 487, .c 7, .c 3, .p pv5 [pv2,pv293,pv4447],
  .c 5, .c 3, .p pv2 [pv2,pv651487], .c 83, .c 3, .c 5, .c 53, .c 3, .c 1117, .c 331, .c 3, .c 7,
  .c 23, .c 3, .c 79, .c 5, .c 3, .p pv2 [pv2,pv223,pv5843], .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv48259], .c 3, .p pv11 [pv2,pv5,pv421,pv619], .c 13, .c 3, .c 541, .c 11, .c 3,
  .c 103, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv11,pv53,pv149], .c 3, .c 5,
  .p pv11 [pv2,pv3,pv7,pv277], .c 3, .c 11, .c 7, .c 3, .c 29, .c 1439, .c 3, .c 461, .c 5, .c 3,
  .p pv7 [pv2,pv23,pv181,pv313], .p pv29 [pv2,pv3,pv5,pv19,pv127], .c 3, .c 5, .c 1447, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv79,pv2749], .c 3, .c 317, .c 19, .c 3, .c 53, .c 5, .c 3,
  .p pv2 [pv2,pv651517], .c 13, .c 3, .c 5, .c 31, .c 3, .c 109,
]
private theorem h0318c03 : checkBlock 2605827 128 b0318c03 = true := by
  decide +kernel

private def b0318c04 : List Row := [
  .c 17, .c 3, .c 11, .c 59, .c 3, .c 7, .c 5, .c 3, .c 67, .c 43, .c 3, .c 5, .c 7, .c 3, .c 139,
  .c 197, .c 3, .c 17, .c 113, .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv7,pv23269], .c 11, .c 3,
  .c 5, .c 857, .c 3, .c 769, .c 29, .c 3, .c 283, .c 7, .c 3, .c 11, .c 5, .c 3, .c 149,
  .p pv7 [pv2,pv3,pv5,pv10859], .c 3, .c 5, .c 127, .c 3, .p pv2 [pv2,pv5,pv7,pv31,pv1201], .c 19,
  .c 3, .c 7, .p pv3 [pv2,pv3,pv434363], .c 3, .p pv5 [pv2,pv1303091], .c 5, .c 3,
  .p pv2 [pv2,pv13,pv50119], .c 7, .c 3, .c 5, .c 11, .c 3, .c 13, .c 557, .c 3, .c 59, .c 103,
  .c 3, .c 1223, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv14479], .c 3, .c 5, .c 13, .c 3,
  .p pv11 [pv2,pv5,pv11,pv19,pv29,pv43], .c 7, .c 3, .c 257, .c 479, .c 3, .c 37, .c 5, .c 3,
  .c 19, .p pv2 [pv2,pv3,pv5,pv139], .c 3, .c 5, .c 431, .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv13,pv59,pv1699], .p pv2 [pv2,pv3,pv7,pv19,pv23,pv71], .c 3, .c 43, .c 5, .c 3,
  .c 13, .p pv7 [pv2,pv3,pv5,pv37,pv587], .c 3, .c 5, .c 17, .c 3, .c 23, .c 97, .c 3,
  .p pv3 [pv2,pv7,pv11,pv4231], .c 109, .c 3, .c 7, .c 5, .c 3, .c 577,
  .p pv17 [pv2,pv3,pv5,pv7,pv197], .c 3, .c 5, .c 7, .c 3, .c 17, .c 661, .c 3, .c 467, .c 11,
  .c 3, .c 1321, .c 5, .c 3,
]
private theorem h0318c04 : checkBlock 2606083 128 b0318c04 = true := by
  decide +kernel

private def b0318c05 : List Row := [
  .c 71, .c 269, .c 3, .c 5, .c 61, .c 3, .c 11, .p pv41 [pv2,pv3,pv7,pv7757], .c 3, .c 13, .c 7,
  .c 3, .c 19, .c 5, .c 3, .c 167, .c 911, .c 3, .c 5, .p pv5 [pv2,pv3,pv131,pv829], .c 3, .c 53,
  .c 13, .c 3, .c 7, .c 17, .c 3, .p pv3 [pv2,pv73,pv4463], .c 5, .c 3, .c 1091, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv17,pv23,pv101], .c 3, .c 41, .c 107, .c 3, .c 11, .c 179, .c 3, .c 17,
  .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv283,pv307], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv10343],
  .c 3, .c 823, .c 7, .c 3, .c 79, .c 31, .c 3, .c 739, .c 5, .c 3, .p pv2 [pv2,pv19,pv113,pv607],
  .c 11, .c 3, .c 5, .c 1181, .c 3, .c 7, .p pv5 [pv2,pv3,pv11,pv1097], .c 3, .c 19, .c 47, .c 3,
  .c 11, .c 5, .c 3, .p pv3 [pv2,pv43,pv7577], .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv19,pv1429],
  .c 3, .c 67, .p pv5 [pv2,pv3,pv37,pv59,pv199], .c 3, .c 101, .p pv19 [pv2,pv3,pv17,pv4259],
  .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv103,pv12653], .c 23, .c 3, .c 5, .c 7, .c 3, .c 43,
  .c 163, .c 3, .c 601, .c 13, .c 3, .c 89, .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv17377], .c 3,
  .c 5, .c 409, .c 3, .c 59, .c 521, .c 3, .c 23, .c 7, .c 3, .c 31, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv29,pv3457], .c 181, .c 3, .c 5, .p pv2 [pv2,pv3,pv434431], .c 3, .c 13,
  .c 11,
]
private theorem h0318c05 : checkBlock 2606339 128 b0318c05 = true := by
  decide +kernel

private def b0318c06 : List Row := [
  .c 3, .c 7, .c 419, .c 3, .p pv2 [pv2,pv1019,pv1279], .c 5, .c 3, .c 619, .c 7, .c 3, .c 5,
  .c 13, .c 3, .c 103, .c 71, .c 3, .c 17, .c 19, .c 3, .p pv5 [pv2,pv7,pv89,pv523], .c 5, .c 3,
  .c 7, .c 227, .c 3, .c 5, .c 223, .c 3, .p pv2 [pv2,pv5,pv37,pv1409], .c 7, .c 3, .c 41, .c 11,
  .c 3, .c 1249, .c 5, .c 3, .c 13, .c 157, .c 3, .c 5, .p pv2 [pv2,pv3,pv217223], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv13,pv23,pv1453], .c 3, .c 37, .c 389, .c 3, .p pv2 [pv2,pv11,pv59243], .c 5,
  .c 3, .c 53, .c 199, .c 3, .c 5, .c 229, .c 3, .c 1487, .c 61, .c 3, .p pv2 [pv2,pv7,pv93097],
  .c 491, .c 3, .c 7, .c 5, .c 3, .c 17, .p pv7 [pv2,pv3,pv5,pv7,pv12413], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv130337], .c 19, .c 3, .c 11, .c 271, .c 3, .p pv3 [pv2,pv29,pv53], .c 5, .c 3,
  .c 31, .c 37, .c 3, .c 5, .p pv3 [pv2,pv3,pv434461], .c 3, .p pv2 [pv2,pv5,pv260677], .c 13,
  .c 3, .c 179, .c 7, .c 3, .p pv5 [pv2,pv439,pv2969], .c 5, .c 3, .c 43, .c 11, .c 3, .c 5,
  .c 17, .c 3, .c 367, .p pv3 [pv2,pv3,pv11,pv127,pv311], .c 3, .c 7,
  .p pv17 [pv2,pv3,pv47,pv2311], .c 3, .c 11, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 103, .c 3,
  .c 17, .p pv19 [pv2,pv3,pv43,pv421], .c 3, .c 281, .c 29, .c 3, .c 23, .c 5, .c 3, .c 7,
]
private theorem h0318c06 : checkBlock 2606595 128 b0318c06 = true := by
  decide +kernel

private def b0318c07 : List Row := [
  .c 13, .c 3, .c 5, .c 11, .c 3, .c 1129, .c 7, .c 3, .c 587, .c 1367, .c 3,
  .p pv3 [pv2,pv37,pv8807], .c 5, .c 3, .c 11, .p pv11 [pv2,pv3,pv5,pv5431], .c 3, .c 5,
  .p pv19 [pv2,pv3,pv251,pv577], .c 3, .c 7, .c 887, .c 3, .c 29, .c 17, .c 3, .c 13, .c 5, .c 3,
  .c 37, .c 53, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv17,pv983], .c 3, .c 79, .c 11, .c 3,
  .p pv5 [pv2,pv7,pv29,pv6421], .c 13, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv1303469],
  .p pv2 [pv2,pv3,pv5,pv7,pv2069], .c 3, .c 5, .c 7, .c 3, .p pv23 [pv2,pv5,pv17,pv3067], .c 109,
  .c 3, .c 61, .c 191, .c 3, .p pv2 [pv2,pv1303481], .c 5, .c 3, .p pv3 [pv2,pv7,pv13,pv3581],
  .c 19, .c 3, .c 5, .c 313, .c 3, .c 13, .c 37, .c 3, .c 797, .c 7, .c 3, .c 709, .c 5, .c 3,
  .p pv13 [pv2,pv1303499], .c 17, .c 3, .c 5, .c 13, .c 3, .c 11, .c 29, .c 3, .c 7, .c 701, .c 3,
  .c 113, .c 5, .c 3, .p pv2 [pv2,pv19,pv34303], .c 7, .c 3, .c 5, .c 67, .c 3,
  .p pv3 [pv2,pv5,pv8147], .c 47, .c 3, .c 19, .c 71, .c 3, .c 149, .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv43451], .c 3, .c 5, .c 41, .c 3, .c 29, .c 7, .c 3, .c 11, .c 61, .c 3,
  .p pv2 [pv2,pv1303541], .c 5, .c 3, .c 613, .c 947, .c 3, .c 5, .p pv7 [pv2,pv3,pv23,pv4723],
  .c 3, .c 7, .c 17, .c 3,
]
private theorem h0318c07 : checkBlock 2606851 128 b0318c07 = true := by
  decide +kernel

private def b0318c08 : List Row := [
  .p pv2 [pv2,pv1303553], .p pv2 [pv2,pv3,pv7,pv41,pv757], .c 3, .c 83, .c 5, .c 3, .c 23, .c 11,
  .c 3, .c 5, .c 677, .c 3, .c 31, .c 43, .c 3, .c 13, .p pv3 [pv2,pv3,pv241,pv601], .c 3, .c 7,
  .c 5, .c 3, .c 41, .c 59, .c 3, .c 5, .c 7, .c 3, .c 19, .c 13, .c 3,
  .p pv5 [pv2,pv89,pv97,pv151], .p pv13 [pv2,pv3,pv37,pv367], .c 3, .p pv2 [pv2,pv651793], .c 5,
  .c 3, .p pv2 [pv2,pv7,pv186227], .p pv43 [pv2,pv3,pv5,pv19,pv2287], .c 3, .c 5, .c 11, .c 3,
  .c 71, .c 31, .c 3, .c 479, .c 7, .c 3, .c 919, .c 5, .c 3, .c 11, .c 23, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv29,pv1873], .c 3, .c 439, .c 139, .c 3, .c 7, .c 53, .c 3, .c 1459, .c 5,
  .c 3, .c 17, .c 7, .c 3, .c 5, .c 137, .c 3, .c 239, .c 11, .c 3, .c 23, .c 1109, .c 3, .c 97,
  .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv233,pv373], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv31039],
  .c 3, .c 733, .c 7, .c 3, .c 331, .p pv41 [pv2,pv3,pv108637], .c 3, .c 13, .c 5, .c 3, .c 157,
  .p pv13 [pv2,pv3,pv5,pv2897], .c 3, .c 5, .c 17, .c 3, .c 7, .c 19, .c 3, .c 31, .c 11, .c 3,
  .c 61, .c 5, .c 3, .c 773, .c 787, .c 3, .c 5, .p pv5 [pv2,pv3,pv12071], .c 3, .c 11, .c 449,
  .c 3, .p pv5 [pv2,pv7,pv186239], .c 23, .c 3, .c 7, .c 5, .c 3, .p pv29 [pv2,pv13,pv17,pv347],
  .c 29,
]
private theorem h0318c08 : checkBlock 2607107 128 b0318c08 = true := by
  decide +kernel

private def b0318c09 : List Row := [
  .c 3, .c 5, .c 7, .c 3, .c 13, .p pv2 [pv2,pv3,pv23,pv47,pv67], .c 3, .p pv3 [pv2,pv107,pv1523],
  .c 31, .c 3, .p pv5 [pv2,pv263,pv4957], .c 5, .c 3, .c 19, .c 43, .c 3, .c 5, .c 13, .c 3,
  .c 277, .p pv3 [pv2,pv3,pv7,pv62081], .c 3, .c 11, .c 7, .c 3, .p pv2 [pv2,pv651853], .c 5,
  .c 3, .c 29, .c 593, .c 3, .c 5, .c 19, .c 3, .p pv7 [pv2,pv5,pv7,pv193], .c 89, .c 3, .c 7,
  .c 67, .c 3, .c 17, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 97, .c 3,
  .p pv3 [pv2,pv5,pv17,pv7669], .c 577, .c 3, .c 389, .p pv13 [pv2,pv3,pv151,pv1439], .c 3, .c 11,
  .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv7243], .c 3, .c 5, .c 23, .c 3,
  .p pv17 [pv2,pv5,pv239,pv1091], .c 7, .c 3, .c 199, .c 883, .c 3, .c 19, .c 5, .c 3,
  .p pv2 [pv2,pv651877], .c 17, .c 3, .c 5, .c 11, .c 3, .c 7, .p pv3 [pv2,pv3,pv19,pv89,pv257],
  .c 3, .c 13, .p pv31 [pv2,pv3,pv7,pv11,pv17,pv83], .c 3, .c 23, .c 5, .c 3, .c 11, .c 19, .c 3,
  .c 5, .c 53, .c 3, .p pv7 [pv2,pv5,pv11,pv431], .c 13, .c 3, .p pv2 [pv2,pv7,pv23,pv4049],
  .c 41, .c 3, .c 7, .c 5, .c 3, .c 1097, .p pv7 [pv2,pv3,pv5,pv7,pv4139], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv130379], .c 11, .c 3, .p pv2 [pv2,pv1303793], .p pv2 [pv2,pv3,pv113,pv641],
  .c 3, .c 29, .c 5, .c 3, .p pv7 [pv2,pv7,pv19,pv9803], .p pv11 [pv2,pv3,pv5,pv41,pv53], .c 3,
  .c 5, .c 47, .c 3, .c 83, .c 17, .c 3, .c 19,
]
private theorem h0318c09 : checkBlock 2607363 128 b0318c09 = true := by
  decide +kernel

private def b0318c10 : List Row := [
  .c 7, .c 3, .c 59, .c 5, .c 3, .c 173, .c 13, .c 3, .c 5, .p pv11 [pv2,pv3,pv19,pv11437], .c 3,
  .c 41, .c 373, .c 3, .c 7, .c 11, .c 3, .c 53, .c 5, .c 3, .p pv2 [pv2,pv31,pv137,pv307], .c 7,
  .c 3, .c 5, .c 181, .c 3, .c 11, .p pv5 [pv2,pv3,pv179,pv607], .c 3, .p pv2 [pv2,pv479,pv1361],
  .c 769, .c 3, .c 13, .c 5, .c 3, .c 7, .c 127, .c 3, .c 5, .c 107, .c 3, .c 47, .c 7, .c 3,
  .c 67, .c 13, .c 3, .c 1087, .c 5, .c 3, .c 101, .p pv11 [pv2,pv3,pv5,pv31,pv701], .c 3, .c 5,
  .c 569, .c 3, .c 7, .p pv5 [pv2,pv3,pv17,pv4261], .c 3, .c 11, .c 601, .c 3,
  .p pv5 [pv2,pv1303871], .c 5, .c 3, .c 17, .c 31, .c 3, .c 5, .c 571, .c 3, .c 13, .c 23, .c 3,
  .c 29, .c 19, .c 3, .c 7, .c 5, .c 3, .c 73, .c 11, .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv79,pv3301], .p pv7 [pv2,pv3,pv11,pv449], .c 3, .c 37,
  .p pv3 [pv2,pv3,pv149,pv2917], .c 3, .c 11, .c 5, .c 3, .c 23, .c 61, .c 3, .c 5, .c 17, .c 3,
  .c 43, .p pv3 [pv2,pv3,pv7,pv6899], .c 3, .p pv2 [pv2,pv13,pv19,pv5279], .c 7, .c 3, .c 271,
  .c 5, .c 3, .c 13, .c 67, .c 3, .c 5, .c 11, .c 3, .c 17, .p pv2 [pv2,pv3,pv13,pv73,pv229],
  .c 3, .c 7, .c 59, .c 3, .p pv5 [pv2,pv1303931], .c 5, .c 3, .c 11, .c 7, .c 3,
]
private theorem h0318c10 : checkBlock 2607619 128 b0318c10 = true := by
  decide +kernel

private def b0318c11 : List Row := [
  .c 5, .c 461, .c 3, .c 1279, .c 19, .c 3, .c 41, .c 47, .c 3, .c 397, .c 5, .c 3, .c 7, .c 23,
  .c 3, .c 5, .c 43, .c 3, .c 107, .c 7, .c 3, .c 13, .c 17, .c 3, .c 631, .c 5, .c 3,
  .p pv3 [pv2,pv41,pv7951], .c 739, .c 3, .c 5, .c 31, .c 3, .c 7, .c 13, .c 3, .c 23, .c 331,
  .c 3, .c 17, .c 5, .c 3, .c 19, .c 281, .c 3, .c 5, .c 89, .c 3, .c 53,
  .p pv2 [pv2,pv3,pv71,pv3061], .c 3, .c 59, .c 11, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv651997],
  .p pv11 [pv2,pv3,pv5,pv7,pv11,pv1129], .c 3, .c 5, .c 7, .c 3, .c 11, .c 227, .c 3,
  .p pv5 [pv2,pv1304003], .c 193, .c 3, .p pv2 [pv2,pv11,pv59273], .c 5, .c 3, .c 37, .c 13, .c 3,
  .c 5, .c 79, .c 3, .c 1217, .p pv11 [pv2,pv3,pv7,pv3881], .c 3, .p pv2 [pv2,pv43,pv59,pv257],
  .c 7, .c 3, .c 71, .c 5, .c 3, .p pv3 [pv2,pv163003], .c 41, .c 3, .c 5, .c 29, .c 3, .c 31,
  .c 103, .c 3, .c 7, .c 137, .c 3, .c 13, .c 5, .c 3, .c 43, .c 7, .c 3, .c 5, .c 823, .c 3,
  .p pv23 [pv2,pv5,pv260809], .c 37, .c 3, .p pv3 [pv2,pv149,pv547], .c 13, .c 3,
  .p pv5 [pv2,pv7,pv241,pv773], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv61,pv509], .c 3, .p pv7 [pv2,pv5,pv65203], .c 7, .c 3,
  .p pv5 [pv2,pv521,pv2503], .p pv7 [pv2,pv3,pv283],
]
private theorem h0318c11 : checkBlock 2607875 128 b0318c11 = true := by
  decide +kernel

private def b0318c12 : List Row := [
  .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv13,pv100313], .c 251, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv48299], .c 3, .c 7, .c 113, .c 3, .c 17, .p pv3 [pv2,pv3,pv7,pv62099], .c 3,
  .c 163, .c 5, .c 3, .p pv3 [pv2,pv19,pv17159], .c 47, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv130409], .c 53, .c 3, .c 19, .c 1609, .c 3, .c 7, .c 5, .c 3, .c 11, .c 523,
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv11,pv131,pv181], .c 59, .c 3, .c 73,
  .p pv29 [pv2,pv3,pv47,pv3083], .c 3, .c 23, .c 5, .c 3, .c 13, .c 29, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv53,pv1367], .c 3, .c 37, .c 11, .c 3, .c 31, .c 7, .c 3,
  .p pv2 [pv2,pv652063], .c 5, .c 3, .c 17, .c 109, .c 3, .c 5, .c 1297, .c 3, .c 1493, .c 499,
  .c 3, .c 7, .c 607, .c 3, .p pv2 [pv2,pv19,pv68639], .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .c 41,
  .c 3, .c 19, .p pv5 [pv2,pv3,pv434717], .c 3, .c 13, .c 11, .c 3, .p pv5 [pv2,pv7,pv47,pv991],
  .c 5, .c 3, .c 7, .c 173, .c 3, .c 5, .c 17, .c 3, .c 11, .c 7, .c 3, .c 43, .c 19, .c 3, .c 79,
  .c 5, .c 3, .p pv2 [pv2,pv652087], .p pv3 [pv2,pv3,pv5,pv17389], .c 3, .c 5, .c 311, .c 3, .c 7,
  .c 73, .c 3, .p pv5 [pv2,pv1304183], .p pv31 [pv2,pv3,pv7,pv1109], .c 3, .c 167, .c 5, .c 3,
  .c 41, .p pv7 [pv2,pv3,pv5,pv43,pv337], .c 3, .c 5,
]
private theorem h0318c12 : checkBlock 2608131 128 b0318c12 = true := by
  decide +kernel

private def b0318c13 : List Row := [
  .p pv3 [pv2,pv3,pv11,pv39521], .c 3, .c 181, .p pv5 [pv2,pv3,pv251,pv433], .c 3, .c 11, .c 347,
  .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv11,pv29641], .c 13, .c 3, .c 5, .c 7, .c 3, .c 61, .c 43,
  .c 3, .c 97, .c 17, .c 3, .c 31, .c 5, .c 3, .p pv7 [pv2,pv7,pv186317], .c 11, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv17,pv107,pv239], .c 3, .c 839, .c 19, .c 3, .c 227, .c 7, .c 3, .c 11, .c 5,
  .c 3, .c 71, .p pv3 [pv2,pv3,pv5,pv9661], .c 3, .c 5, .c 197, .c 3, .c 677,
  .p pv2 [pv2,pv3,pv61,pv7127], .c 3, .c 7, .c 13, .c 3, .c 269, .c 5, .c 3, .c 23, .c 7, .c 3,
  .c 5, .c 11, .c 3, .c 67, .p pv5 [pv2,pv3,pv6793], .c 3, .p pv2 [pv2,pv421,pv1549],
  .p pv3 [pv2,pv3,pv11,pv3593], .c 3, .c 281, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 37, .c 3,
  .c 13, .c 7, .c 3, .c 47, .p pv7 [pv2,pv3,pv17,pv19,pv673], .c 3, .c 107, .c 5, .c 3,
  .p pv7 [pv2,pv503,pv2593], .p pv11 [pv2,pv3,pv5,pv3623], .c 3, .c 5, .c 13, .c 3, .c 7, .c 11,
  .c 3, .p pv3 [pv2,pv40759], .c 29, .c 3, .p pv5 [pv2,pv17,pv73,pv1051], .c 5, .c 3,
  .p pv2 [pv2,pv31,pv109,pv193], .c 23, .c 3, .c 5, .c 1483, .c 3, .p pv11 [pv2,pv5,pv13043],
  .c 131, .c 3, .c 53, .c 1163, .c 3, .c 7, .c 5, .c 3, .c 13, .c 97, .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv260863], .c 17, .c 3, .c 23, .c 11, .c 3,
]
private theorem h0318c13 : checkBlock 2608387 128 b0318c13 = true := by
  decide +kernel

private def b0318c14 : List Row := [
  .c 19, .c 5, .c 3, .p pv3 [pv2,pv7,pv37,pv1259], .c 643, .c 3, .c 5, .c 379, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv7,pv19,pv467], .c 3, .c 17, .c 7, .c 3, .c 743, .c 5, .c 3, .c 89, .c 19,
  .c 3, .c 5, .c 397, .c 3, .c 199, .p pv5 [pv2,pv3,pv149,pv1459], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv434783], .c 3, .p pv5 [pv2,pv541,pv2411], .c 5, .c 3, .c 1381, .c 7, .c 3,
  .c 5, .c 337, .c 3, .p pv3 [pv2,pv5,pv32609], .c 13, .c 3, .c 11, .c 23, .c 3,
  .p pv2 [pv2,pv7,pv93169], .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv4831], .c 3, .c 5, .c 733,
  .c 3, .p pv13 [pv2,pv5,pv2087], .c 7, .c 3, .c 19, .c 37, .c 3, .p pv2 [pv2,pv13,pv269,pv373],
  .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv19,pv1907], .c 3, .c 7, .c 859, .c 3,
  .c 61, .c 41, .c 3, .c 11, .c 5, .c 3, .c 461, .c 13, .c 3, .c 5, .c 257, .c 3, .c 29,
  .p pv2 [pv2,pv3,pv72467], .c 3, .c 79, .c 53, .c 3, .c 7, .c 5, .c 3, .c 47, .c 113, .c 3, .c 5,
  .c 7, .c 3, .c 149, .c 431, .c 3, .p pv5 [pv2,pv67,pv19469], .c 863, .c 3, .c 13, .c 5, .c 3,
  .c 11, .p pv29 [pv2,pv3,pv5,pv43481], .c 3, .c 5, .c 23, .c 3, .c 17,
  .p pv13 [pv2,pv3,pv7,pv53,pv293], .c 3, .c 223, .c 7, .c 3, .p pv2 [pv2,pv983,pv1327], .c 5,
  .c 3, .p pv3 [pv2,pv17,pv19183], .c 137, .c 3, .c 5, .p pv5 [pv2,pv3,pv43,pv79],
]
private theorem h0318c14 : checkBlock 2608643 128 b0318c14 = true := by
  decide +kernel

private def b0318c15 : List Row := [
  .c 3, .c 233, .c 11, .c 3, .c 7, .c 19, .c 3, .c 23, .c 5, .c 3, .p pv11 [pv2,pv13,pv100343],
  .c 7, .c 3, .c 5, .c 29, .c 3, .c 13, .p pv5 [pv2,pv3,pv217411], .c 3, .c 421, .c 17, .c 3,
  .p pv5 [pv2,pv7,pv331,pv563], .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv17393], .c 3, .c 5, .c 13,
  .c 3, .c 127, .c 7, .c 3, .c 661, .c 11, .c 3, .c 17, .c 5, .c 3, .c 311, .c 37, .c 3, .c 5,
  .c 811, .c 3, .c 7, .p pv5 [pv2,pv3,pv9059], .c 3, .c 229, .c 1061, .c 3, .c 367, .c 5, .c 3,
  .c 13, .c 409, .c 3, .c 5, .c 47, .c 3, .p pv2 [pv2,pv5,pv73,pv1787], .c 19, .c 3,
  .p pv2 [pv2,pv7,pv157,pv1187], .p pv7 [pv2,pv3,pv23,pv137], .c 3, .c 7, .c 5, .c 3, .c 59,
  .c 17, .c 3, .c 5, .c 7, .c 3, .c 23, .c 31, .c 3, .c 11, .p pv2 [pv2,pv3,pv17,pv25579], .c 3,
  .c 277, .c 5, .c 3, .p pv2 [pv2,pv7,pv11,pv43,pv197], .p pv31 [pv2,pv3,pv5,pv86969], .c 3, .c 5,
  .c 971, .c 3, .p pv3 [pv2,pv5,pv19,pv3433], .p pv2 [pv2,pv3,pv7,pv20707], .c 3, .c 13, .c 7,
  .c 3, .c 73, .c 5, .c 3, .c 19, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv97,pv4483], .c 3, .c 43,
  .c 13, .c 3, .c 7, .c 1129, .c 3, .c 11, .c 5, .c 3, .c 37, .c 7, .c 3, .c 5, .c 19, .c 3,
  .c 163, .c 17, .c 3, .p pv2 [pv2,pv31,pv42083], .c 997, .c 3, .c 61,
]
private theorem h0318c15 : checkBlock 2608899 128 b0318c15 = true := by
  decide +kernel

private def b0318c16 : List Row := [
  .c 5, .c 3, .c 7, .c 1249, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv113,pv2309], .c 7, .c 3,
  .c 17, .c 71, .c 3, .c 157, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 43, .c 3, .c 7, .c 37,
  .c 3, .p pv5 [pv2,pv1304603], .p pv23 [pv2,pv3,pv7,pv31,pv167], .c 3, .c 19, .c 5, .c 3,
  .p pv2 [pv2,pv1304609], .c 673, .c 3, .c 5, .c 317, .c 3, .p pv7 [pv2,pv5,pv13,pv20071], .c 11,
  .c 3, .p pv2 [pv2,pv7,pv93187], .c 31, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv67,pv1217], .c 19,
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv283,pv461], .p pv3 [pv2,pv3,pv17,pv8527], .c 3,
  .p pv2 [pv2,pv11,pv118603], .c 13, .c 3, .c 331, .c 5, .c 3, .c 17, .c 23, .c 3, .c 5,
  .p pv19 [pv2,pv3,pv434881], .c 3, .c 79, .c 617, .c 3, .p pv3 [pv2,pv17,pv53,pv181], .c 7, .c 3,
  .c 991, .c 5, .c 3, .p pv2 [pv2,pv13,pv19,pv139], .p pv41 [pv2,pv3,pv5,pv11,pv7907], .c 3, .c 5,
  .c 1151, .c 3, .c 11, .c 223, .c 3, .c 7, .p pv11 [pv2,pv3,pv54361], .c 3, .c 29, .c 5, .c 3,
  .p pv2 [pv2,pv1304669], .c 7, .c 3, .c 5, .c 13, .c 3, .c 37, .p pv7 [pv2,pv3,pv36241], .c 3,
  .p pv2 [pv2,pv652339], .c 173, .c 3, .c 31, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv79,pv367],
  .c 3, .c 5, .p pv19 [pv2,pv3,pv7,pv11,pv353], .c 3, .c 17, .c 7, .c 3, .c 11, .c 131, .c 3,
  .c 47, .c 5, .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv4349], .c 3, .c 5, .p pv3 [pv2,pv3,pv144967],
  .c 3,
]
private theorem h0318c16 : checkBlock 2609155 128 b0318c16 = true := by
  decide +kernel

private def b0318c17 : List Row := [
  .c 7, .p pv2 [pv2,pv3,pv13,pv43,pv389], .c 3, .p pv3 [pv2,pv439,pv743], .c 23, .c 3,
  .p pv5 [pv2,pv19,pv68669], .c 5, .c 3, .c 1069, .c 11, .c 3, .c 5, .c 83, .c 3, .c 19,
  .p pv3 [pv2,pv3,pv11,pv23,pv191], .c 3, .c 139, .c 17, .c 3, .c 7, .c 5, .c 3, .c 271, .c 1031,
  .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv457,pv571], .c 349, .c 3, .c 13, .c 19, .c 3, .c 17,
  .c 5, .c 3, .p pv3 [pv2,pv7,pv23,pv1013], .p pv11 [pv2,pv3,pv5,pv13,pv6691], .c 3, .c 5, .c 11,
  .c 3, .p pv2 [pv2,pv5,pv17,pv307], .c 13, .c 3, .c 29, .c 7, .c 3, .p pv3 [pv2,pv326189], .c 5,
  .c 3, .c 11, .p pv13 [pv2,pv3,pv5,pv83,pv131], .c 3, .c 5, .c 41, .c 3, .c 73,
  .p pv2 [pv2,pv3,pv173,pv419], .c 3, .c 7, .p pv2 [pv2,pv3,pv434923], .c 3, .c 283, .c 5, .c 3,
  .c 31, .c 7, .c 3, .c 5, .c 23, .c 3, .c 53, .c 11, .c 3, .c 977, .c 89, .c 3, .c 37, .c 5,
  .c 3, .c 7, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv139,pv149], .c 3, .c 97, .c 7, .c 3,
  .p pv2 [pv2,pv11,pv127,pv467], .p pv11 [pv2,pv3,pv434933], .c 3, .c 23, .c 5, .c 3, .c 41,
  .c 31, .c 3, .c 5, .c 277, .c 3, .c 7, .c 29, .c 3, .c 43, .c 11, .c 3, .c 13, .c 5, .c 3,
  .p pv7 [pv2,pv101,pv12919], .c 61, .c 3, .c 5, .c 37, .c 3, .c 11, .c 17, .c 3,
  .p pv3 [pv2,pv7,pv46601], .c 13, .c 3, .c 7, .c 5,
]
private theorem h0318c17 : checkBlock 2609411 128 b0318c17 = true := by
  decide +kernel

private def b0318c18 : List Row := [
  .c 3, .c 19, .p pv11 [pv2,pv3,pv5,pv7,pv17,pv43], .c 3, .c 5, .c 7, .c 3, .c 29,
  .p pv2 [pv2,pv3,pv434947], .c 3, .c 17, .c 521, .c 3, .p pv2 [pv2,pv787,pv829], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv13,pv1103], .p pv2 [pv2,pv3,pv5,pv8699], .c 3, .c 5, .c 19, .c 3, .c 13,
  .c 43, .c 3, .c 11, .c 7, .c 3, .c 127, .c 5, .c 3, .c 353, .p pv2 [pv2,pv3,pv5,pv107,pv271],
  .c 3, .c 5, .c 13, .c 3, .c 23, .c 683, .c 3, .c 7, .c 263, .c 3, .p pv3 [pv2,pv326219], .c 5,
  .c 3, .c 1499, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv31,pv1559], .c 3, .c 577, .c 41, .c 3,
  .p pv3 [pv2,pv13,pv12547], .c 421, .c 3, .c 11, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv86993],
  .c 3, .c 5, .c 29, .c 3, .c 389, .c 7, .c 3, .c 307, .p pv7 [pv2,pv3,pv54371], .c 3,
  .p pv2 [pv2,pv652453], .c 5, .c 3, .c 227, .c 19, .c 3, .c 5, .c 11, .c 3, .c 7, .c 23, .c 3,
  .c 107, .c 181, .c 3, .c 599, .c 5, .c 3, .c 11, .c 67, .c 3, .c 5, .c 17, .c 3, .c 317, .c 47,
  .c 3, .c 13, .c 37, .c 3, .c 7, .c 5, .c 3, .c 23, .c 373, .c 3, .c 5, .c 7, .c 3, .c 17, .c 11,
  .c 3, .c 19, .p pv2 [pv2,pv3,pv251,pv1733], .c 3, .p pv5 [pv2,pv23,pv56737], .c 5, .c 3,
  .c 1303, .p pv3 [pv2,pv3,pv5,pv47,pv617], .c 3, .c 5, .c 103, .c 3, .c 31,
]
private theorem h0318c18 : checkBlock 2609667 128 b0318c18 = true := by
  decide +kernel

private def b0318c19 : List Row := [
  .c 79, .c 3, .c 457, .c 7, .c 3, .c 967, .c 5, .c 3, .c 193, .c 101, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv61,pv2377], .c 3, .c 419, .p pv7 [pv2,pv3,pv31,pv877], .c 3, .c 7, .c 11,
  .c 3, .p pv2 [pv2,pv1304981], .c 5, .c 3, .c 73, .c 7, .c 3, .c 5, .c 127, .c 3, .c 11, .c 31,
  .c 3, .c 137, .p pv2 [pv2,pv3,pv217499], .c 3, .c 17, .c 5, .c 3, .c 7, .c 271, .c 3, .c 5,
  .c 61, .c 3, .c 19, .c 7, .c 3, .c 23, .c 41, .c 3, .c 13, .c 5, .c 3, .c 29, .c 71, .c 3, .c 5,
  .c 449, .c 3, .c 7, .c 167, .c 3, .c 11, .c 13, .c 3, .c 197, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv29,pv4091], .c 17, .c 3, .c 5, .c 503, .c 3, .c 479, .c 1373, .c 3,
  .p pv2 [pv2,pv7,pv31,pv97], .c 1307, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv13,pv25097], .c 11,
  .c 3, .c 5, .c 7, .c 3, .c 13, .c 89, .c 3, .c 31, .c 23, .c 3, .c 11, .c 5, .c 3, .c 67,
  .p pv13 [pv2,pv3,pv5,pv21751], .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv261013],
  .p pv2 [pv2,pv3,pv7,pv23,pv193], .c 3, .p pv3 [pv2,pv431,pv757], .c 7, .c 3, .c 43, .c 5, .c 3,
  .c 251, .c 1459, .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv7,pv59,pv79], .c 17, .c 3, .c 7,
  .c 31, .c 3, .c 71, .c 5, .c 3,
]
private theorem h0318c19 : checkBlock 2609923 128 b0318c19 = true := by
  decide +kernel

private def b0318c20 : List Row := [
  .c 11, .c 7, .c 3, .c 5, .c 113, .c 3, .p pv11 [pv2,pv5,pv11,pv61,pv389],
  .p pv5 [pv2,pv3,pv13,pv47,pv89], .c 3, .c 17, .p pv3 [pv2,pv3,pv48337], .c 3, .c 29, .c 5, .c 3,
  .c 7, .p pv3 [pv2,pv3,pv5,pv167,pv521], .c 3, .c 5, .c 1489, .c 3, .p pv2 [pv2,pv5,pv19,pv6869],
  .c 7, .c 3, .p pv2 [pv2,pv103,pv12671], .c 43, .c 3, .p pv3 [pv2,pv29,pv11251], .c 5, .c 3,
  .c 19, .p pv11 [pv2,pv3,pv5,pv2719], .c 3, .c 5, .c 23, .c 3, .c 7, .c 67, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv7,pv19,pv3271], .c 3, .p pv5 [pv2,pv31,pv42101], .c 5, .c 3, .c 499, .c 241,
  .c 3, .c 5, .c 19, .c 3, .c 89, .c 13, .c 3, .p pv7 [pv2,pv7,pv47,pv3967], .c 11, .c 3, .c 7,
  .c 5, .c 3, .c 17, .c 1319, .c 3, .c 5, .c 7, .c 3, .c 11, .c 37, .c 3,
  .p pv2 [pv2,pv17,pv23,pv1669], .c 29, .c 3, .c 619, .c 5, .c 3, .c 103, .c 149, .c 3, .c 5,
  .c 59, .c 3, .p pv2 [pv2,pv5,pv130517], .p pv3 [pv2,pv3,pv7,pv20717], .c 3, .c 41, .c 7, .c 3,
  .c 19, .c 5, .c 3, .p pv11 [pv2,pv43,pv127,pv239], .c 13, .c 3, .c 5, .c 17, .c 3, .c 229,
  .c 61, .c 3, .c 7, .p pv2 [pv2,pv3,pv145021], .c 3, .p pv5 [pv2,pv181,pv7211], .c 5, .c 3,
  .c 587, .c 7, .c 3, .c 5, .c 79, .c 3, .c 17, .c 881, .c 3, .c 73, .c 53, .c 3, .c 13, .c 5,
  .c 3, .c 7, .c 11, .c 3, .c 5, .c 47, .c 3, .c 23, .c 7,
]
private theorem h0318c20 : checkBlock 2610179 128 b0318c20 = true := by
  decide +kernel

private def b0318c21 : List Row := [
  .c 3, .c 131, .c 13, .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv19,pv31,pv277],
  .p pv41 [pv2,pv3,pv5,pv5801], .c 3, .c 5, .c 71, .c 3, .c 7, .p pv3 [pv2,pv3,pv53,pv8209], .c 3,
  .c 19, .c 17, .c 3, .p pv3 [pv2,pv326309], .c 5, .c 3, .c 31, .c 347, .c 3, .c 5, .c 11, .c 3,
  .c 13, .c 29, .c 3, .p pv3 [pv2,pv7,pv5827], .p pv11 [pv2,pv3,pv11,pv37,pv1069], .c 3, .c 7,
  .c 5, .c 3, .c 11, .c 41, .c 3, .c 5, .c 7, .c 3, .c 47, .c 23, .c 3, .c 617,
  .p pv7 [pv2,pv3,pv71,pv383], .c 3, .p pv2 [pv2,pv233,pv2801], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv263,pv709], .c 31, .c 3, .c 5, .c 101, .c 3, .c 29, .c 11, .c 3, .c 433, .c 7,
  .c 3, .c 181, .c 5, .c 3, .c 13, .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv6043], .c 3, .c 19,
  .p pv3 [pv2,pv3,pv13,pv33469], .c 3, .c 7, .p pv13 [pv2,pv3,pv17,pv67,pv191], .c 3, .c 41, .c 5,
  .c 3, .c 71, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv257,pv1693], .c 3, .p pv2 [pv2,pv5,pv261061],
  .p pv2 [pv2,pv3,pv127,pv571], .c 3, .c 61, .c 11, .c 3, .p pv5 [pv2,pv7,pv17,pv1567], .c 5,
  .c 3, .c 7, .c 563, .c 3, .c 5, .c 89, .c 3, .c 11, .c 7, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv101,pv359], .c 3, .p pv2 [pv2,pv11,pv59333], .c 5, .c 3, .c 43, .c 23, .c 3,
  .c 5, .c 29, .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv19,pv34351],
  .p pv7 [pv2,pv3,pv7,pv61,pv1019], .c 3, .c 37, .c 5, .c 3, .c 719,
]
private theorem h0318c21 : checkBlock 2610435 128 b0318c21 = true := by
  decide +kernel

private def b0318c22 : List Row := [
  .c 59, .c 3, .c 5, .c 1021, .c 3, .p pv2 [pv2,pv5,pv26107], .c 211, .c 3, .c 11, .c 47, .c 3,
  .c 7, .c 5, .c 3, .p pv11 [pv2,pv11,pv118669], .p pv43 [pv2,pv3,pv5,pv7,pv37], .c 3, .c 5, .c 7,
  .c 3, .c 521, .c 19, .c 3, .p pv3 [pv2,pv163171], .c 61, .c 3, .c 173, .c 5, .c 3, .c 101,
  .c 11, .c 3, .c 5, .c 37, .c 3, .p pv3 [pv2,pv5,pv65269], .c 1091, .c 3, .c 613, .c 7, .c 3,
  .c 11, .c 5, .c 3, .c 191, .p pv11 [pv2,pv3,pv5,pv53,pv821], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv435131], .c 3, .p pv7 [pv2,pv5,pv7,pv13,pv19,pv151], .c 641, .c 3, .c 7,
  .c 23, .c 3, .c 13, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 11, .c 3,
  .p pv3 [pv2,pv5,pv31,pv4211], .p pv3 [pv2,pv3,pv23,pv18919], .c 3, .p pv2 [pv2,pv17,pv4517],
  .c 13, .c 3, .c 53, .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .c 19, .c 3, .c 31, .c 7, .c 3, .c 463,
  .p pv2 [pv2,pv3,pv435143], .c 3, .c 257, .c 5, .c 3, .c 349, .c 79, .c 3, .c 5, .c 17, .c 3,
  .c 7, .c 11, .c 3, .c 739, .p pv11 [pv2,pv3,pv7,pv15541], .c 3, .c 757, .c 5, .c 3, .c 29,
  .p pv2 [pv2,pv3,pv5,pv967], .c 3, .c 5, .c 13, .c 3, .c 17, .c 31, .c 3, .c 43,
  .p pv3 [pv2,pv3,pv73,pv1987], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv17,pv29,pv331], .c 83, .c 3,
  .c 5, .c 7, .c 3, .c 151, .p pv3 [pv2,pv3,pv19,pv37,pv619], .c 3,
]
private theorem h0318c22 : checkBlock 2610691 128 b0318c22 = true := by
  decide +kernel

private def b0318c23 : List Row := [
  .c 103, .c 11, .c 3, .p pv3 [pv2,pv326369], .c 5, .c 3, .c 13, .c 19, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv435161], .c 3, .c 11, .p pv17 [pv2,pv3,pv7,pv13,pv797], .c 3,
  .p pv3 [pv2,pv139,pv587], .c 7, .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv652747], .c 47, .c 3,
  .c 5, .c 467, .c 3, .p pv11 [pv2,pv5,pv7,pv373], .c 41, .c 3, .c 7, .p pv13 [pv2,pv3,pv1511],
  .c 3, .c 17, .c 5, .c 3, .c 971, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv13187], .c 3, .c 883,
  .c 853, .c 3, .c 11, .p pv3 [pv2,pv3,pv47,pv197], .c 3, .p pv2 [pv2,pv7,pv421,pv443], .c 5,
  .c 3, .c 7, .p pv41 [pv2,pv3,pv5,pv13,pv103], .c 3, .c 5, .c 67, .c 3,
  .p pv2 [pv2,pv5,pv130553], .c 7, .c 3, .c 157, .c 397, .c 3, .c 29, .c 5, .c 3, .c 199, .c 11,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv435181], .c 3, .c 7, .p pv17 [pv2,pv3,pv11,pv131,pv151], .c 3,
  .c 83, .c 31, .c 3, .c 11, .c 5, .c 3, .c 683, .p pv23 [pv2,pv3,pv5,pv87037], .c 3, .c 5,
  .p pv13 [pv2,pv3,pv8059], .c 3, .c 23, .p pv2 [pv2,pv3,pv435187], .c 3, .c 37, .c 317, .c 3,
  .c 7, .c 5, .c 3, .p pv2 [pv2,pv491,pv2659], .c 13, .c 3, .c 5, .c 7, .c 3, .c 19, .c 101, .c 3,
  .p pv2 [pv2,pv311,pv2099], .p pv11 [pv2,pv3,pv11,pv39563], .c 3, .c 59, .c 5, .c 3, .c 11,
  .c 89, .c 3, .c 5, .c 1093, .c 3, .c 227, .c 17, .c 3, .c 79, .c 7, .c 3, .c 13, .c 5, .c 3,
  .p pv13 [pv2,pv1305599], .c 37,
]
private theorem h0318c23 : checkBlock 2610947 128 b0318c23 = true := by
  decide +kernel

private def b0318c24 : List Row := [
  .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv11159], .c 3, .p pv2 [pv2,pv5,pv7,pv73], .c 11, .c 3, .c 7,
  .c 13, .c 3, .c 31, .c 5, .c 3, .p pv2 [pv2,pv107,pv6101], .c 7, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv23,pv9461], .c 3, .c 283, .c 151, .c 3, .c 29, .c 41, .c 3, .c 907, .c 5,
  .c 3, .c 7, .c 43, .c 3, .c 5, .c 499, .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv29,pv22511],
  .c 11, .c 3, .c 73, .c 5, .c 3, .c 691, .p pv11 [pv2,pv3,pv5,pv11,pv41,pv193], .c 3, .c 5,
  .c 13, .c 3, .c 7, .c 19, .c 3, .c 1237, .c 71, .c 3, .c 109, .c 5, .c 3, .c 17,
  .p pv19 [pv2,pv3,pv5,pv47,pv463], .c 3, .c 5, .c 263, .c 3, .c 41, .c 281, .c 3, .c 97, .c 523,
  .c 3, .c 7, .c 5, .c 3, .c 13, .c 23, .c 3, .c 5, .c 7, .c 3, .p pv23 [pv2,pv5,pv19,pv859],
  .c 29, .c 3, .c 11, .p pv31 [pv2,pv3,pv36269], .c 3, .c 373, .c 5, .c 3, .c 19, .c 157, .c 3,
  .c 5, .c 17, .c 3, .p pv37 [pv2,pv5,pv43,pv6073], .c 139, .c 3, .c 23, .c 7, .c 3,
  .p pv2 [pv2,pv1305701], .c 5, .c 3, .c 31, .c 11, .c 3, .c 5, .c 19, .c 3, .c 17, .c 37, .c 3,
  .c 7, .c 73, .c 3, .c 11, .c 5, .c 3, .p pv29 [pv2,pv17,pv89,pv863], .c 7, .c 3, .c 5, .c 1613,
  .c 3, .c 71, .c 13, .c 3, .p pv3 [pv2,pv101],
]
private theorem h0318c24 : checkBlock 2611203 128 b0318c24 = true := by
  decide +kernel

private def b0318c25 : List Row := [
  .c 67, .c 3, .c 421, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv65287],
  .c 7, .c 3, .p pv5 [pv2,pv1305743], .c 17, .c 3, .c 19, .c 5, .c 3, .c 11, .c 127, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv17,pv25603], .c 3, .c 7, .p pv5 [pv2,pv3,pv19,pv23,pv83], .c 3, .c 59, .c 43,
  .c 3, .c 17, .c 5, .c 3, .p pv3 [pv2,pv326441], .c 13, .c 3, .c 5, .c 29, .c 3,
  .p pv2 [pv2,pv5,pv17,pv7681], .c 11, .c 3, .c 211, .c 107, .c 3, .c 7, .c 5, .c 3,
  .p pv11 [pv2,pv23,pv56773], .c 619, .c 3, .c 5, .c 7, .c 3, .c 37, .p pv2 [pv2,pv3,pv367,pv593],
  .c 3, .c 41, .p pv2 [pv2,pv3,pv435263], .c 3, .c 13, .c 5, .c 3, .c 1213, .c 17, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv13,pv16741], .c 3, .c 821, .p pv2 [pv2,pv3,pv7,pv47], .c 3, .c 19, .c 7, .c 3,
  .p pv2 [pv2,pv652903], .c 5, .c 3, .c 1151, .p pv2 [pv2,pv3,pv5,pv11,pv1319], .c 3, .c 5, .c 23,
  .c 3, .c 11, .p pv7 [pv2,pv3,pv54409], .c 3, .c 7, .p pv3 [pv2,pv3,pv145091], .c 3,
  .p pv2 [pv2,pv11,pv17,pv6983], .c 5, .c 3, .c 47, .c 7, .c 3, .c 5, .c 31, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv435277], .c 3, .p pv2 [pv2,pv827,pv1579], .p pv2 [pv2,pv3,pv103,pv2113], .c 3,
  .c 23, .c 5, .c 3, .c 7, .c 53, .c 3, .c 5, .c 13, .c 3, .c 43, .c 7, .c 3, .c 11,
  .p pv17 [pv2,pv3,pv435283], .c 3, .p pv5 [pv2,pv19,pv68729], .c 5, .c 3, .c 631, .c 29, .c 3,
]
private theorem h0318c25 : checkBlock 2611459 128 b0318c25 = true := by
  decide +kernel

private def b0318c26 : List Row := [
  .c 5, .c 241, .c 3, .c 7, .p pv3 [pv2,pv3,pv435287], .c 3, .c 17, .p pv11 [pv2,pv3,pv7,pv2591],
  .c 3, .p pv2 [pv2,pv652933], .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 131, .c 3,
  .p pv7 [pv2,pv5,pv31,pv337], .c 59, .c 3, .c 563, .c 19, .c 3, .c 7, .c 5, .c 3, .c 29, .c 103,
  .c 3, .c 5, .c 7, .c 3, .c 31, .c 463, .c 3, .c 53, .c 179, .c 3, .c 37, .c 5, .c 3,
  .p pv11 [pv2,pv7,pv29,pv919], .p pv7 [pv2,pv3,pv5,pv1451], .c 3, .c 5, .c 11, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv7,pv17,pv31,pv59], .c 3, .c 13, .c 7, .c 3, .c 41, .c 5, .c 3, .c 11, .c 983,
  .c 3, .c 5, .c 47, .c 3, .p pv17 [pv2,pv5,pv7,pv11,pv53], .c 13, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv108827], .c 3, .c 263, .c 5, .c 3, .p pv2 [pv2,pv109,pv11981], .c 7, .c 3,
  .c 5, .c 37, .c 3, .c 59, .c 11, .c 3, .c 71, .p pv3 [pv2,pv3,pv131,pv3323], .c 3, .c 89, .c 5,
  .c 3, .c 7, .c 257, .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv26119], .c 7, .c 3,
  .p pv2 [pv2,pv11,pv43,pv251], .p pv59 [pv2,pv3,pv13,pv5581], .c 3, .c 673, .c 5, .c 3, .c 97,
  .c 13, .c 3, .c 5, .c 83, .c 3, .c 7, .c 1399, .c 3, .p pv3 [pv2,pv31,pv2633], .c 11, .c 3,
  .c 29, .c 5, .c 3, .c 19, .p pv3 [pv2,pv3,pv5,pv11,pv1583], .c 3, .c 5, .c 1097, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv145109], .c 3, .c 31, .c 211,
]
private theorem h0318c26 : checkBlock 2611715 128 b0318c26 = true := by
  decide +kernel

private def b0318c27 : List Row := [
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv37,pv47,pv751], .p pv2 [pv2,pv3,pv5,pv7,pv691], .c 3,
  .c 5, .c 7, .c 3, .p pv13 [pv2,pv5,pv269,pv971], .c 613, .c 3, .p pv2 [pv2,pv652999], .c 13,
  .c 3, .p pv2 [pv2,pv1306001], .c 5, .c 3, .c 127, .c 181, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv17,pv97], .c 3, .p pv2 [pv2,pv5,pv61,pv2141], .c 197, .c 3, .c 11, .c 7,
  .c 3, .c 17, .c 5, .c 3, .p pv31 [pv2,pv11,pv13,pv9133], .c 23, .c 3, .c 5, .c 167, .c 3, .c 13,
  .c 787, .c 3, .c 7, .c 29, .c 3, .c 19, .c 5, .c 3, .c 41, .c 7, .c 3, .c 5, .c 13, .c 3, .c 61,
  .p pv2 [pv2,pv3,pv11,pv19,pv2083], .c 3, .c 23, .c 37, .c 3, .c 11, .c 5, .c 3, .c 7, .c 17,
  .c 3, .c 5, .c 59, .c 3, .c 727, .c 7, .c 3, .c 29, .c 47, .c 3, .p pv2 [pv2,pv31,pv42131],
  .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv87071], .c 3, .c 5, .c 11, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv13,pv61], .c 3, .c 179, .c 151, .c 3, .c 31, .c 5, .c 3, .c 11, .c 71, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv47,pv59,pv157], .c 3, .p pv2 [pv2,pv5,pv11,pv23747], .c 953, .c 3,
  .c 19, .c 23, .c 3, .c 7, .c 5, .c 3, .c 1567, .c 107, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv37,pv353], .c 11, .c 3, .c 13, .p pv7 [pv2,pv3,pv54421], .c 3, .c 47, .c 5,
  .c 3, .c 859, .c 113, .c 3, .c 5,
]
private theorem h0318c27 : checkBlock 2611971 128 b0318c27 = true := by
  decide +kernel

private def b0318c28 : List Row := [
  .c 139, .c 3, .c 811, .c 13, .c 3, .c 17, .c 7, .c 3, .p pv2 [pv2,pv1306121], .c 5, .c 3,
  .p pv3 [pv2,pv23,pv14197], .p pv11 [pv2,pv3,pv5,pv43], .c 3, .c 5, .p pv11 [pv2,pv3,pv27211],
  .c 3, .c 809, .c 67, .c 3, .c 7, .c 11, .c 3, .c 199, .c 5, .c 3, .c 569, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv103,pv1409], .c 3, .c 11, .c 43, .c 3, .p pv3 [pv2,pv326537], .c 1543, .c 3,
  .c 71, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 23, .c 3, .p pv3 [pv2,pv5,pv29,pv563], .c 7,
  .c 3, .p pv5 [pv2,pv179,pv7297], .c 19, .c 3, .p pv2 [pv2,pv653083], .c 5, .c 3, .c 17,
  .p pv41 [pv2,pv3,pv5,pv23,pv631], .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv39581], .c 3, .c 7,
  .p pv17 [pv2,pv3,pv6803], .c 3, .c 11, .c 1433, .c 3, .c 13, .c 5, .c 3,
  .p pv3 [pv2,pv11,pv14843], .c 443, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv2791], .c 3, .c 167,
  .p pv3 [pv2,pv3,pv435397], .c 3, .c 277, .c 13, .c 3, .c 7, .c 5, .c 3,
  .p pv11 [pv2,pv467,pv2797], .c 11, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv261241],
  .p pv2 [pv2,pv3,pv11,pv733], .c 3, .c 89, .p pv2 [pv2,pv3,pv435403], .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv13,pv7177], .p pv19 [pv2,pv3,pv5,pv29027], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv29,pv7507], .c 3, .c 13, .c 19, .c 3, .c 61, .c 7, .c 3, .c 137, .c 5, .c 3,
  .c 37, .c 59, .c 3, .c 5, .c 11, .c 3, .p pv7 [pv2,pv5,pv7,pv37321], .c 173, .c 3, .c 7, .c 41,
  .c 3,
]
private theorem h0318c28 : checkBlock 2612227 128 b0318c28 = true := by
  decide +kernel

private def b0318c29 : List Row := [
  .p pv2 [pv2,pv1306241], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv37,pv1471], .c 3,
  .c 23, .p pv3 [pv2,pv3,pv145139], .c 3, .p pv2 [pv2,pv13,pv89,pv1129], .c 17, .c 3, .c 761,
  .c 5, .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv41,pv59], .c 3, .c 5, .c 1013, .c 3, .c 67, .c 7, .c 3,
  .p pv3 [pv2,pv326567], .p pv2 [pv2,pv3,pv19,pv7639], .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv167,pv3911], .c 43, .c 3, .c 5, .c 19, .c 3, .c 7, .c 347, .c 3, .c 101, .c 61,
  .c 3, .c 1571, .c 5, .c 3, .c 59, .c 29, .c 3, .c 5, .c 31, .c 3, .c 83, .c 23, .c 3, .c 13,
  .c 11, .c 3, .c 7, .c 5, .c 3, .c 79, .c 17, .c 3, .c 5, .c 7, .c 3, .c 11, .c 13, .c 3, .c 701,
  .c 233, .c 3, .c 19, .c 5, .c 3, .c 23, .c 193, .c 3, .c 5, .p pv5 [pv2,pv3,pv173,pv839], .c 3,
  .p pv2 [pv2,pv5,pv52253], .c 653, .c 3, .c 397, .c 7, .c 3, .c 1117, .c 5, .c 3, .c 457, .c 19,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv19793], .c 3, .c 37, .c 47, .c 3, .c 7, .c 191, .c 3,
  .c 1307, .c 5, .c 3, .p pv2 [pv2,pv11,pv103,pv1153], .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv435451], .c 3, .c 31, .c 17, .c 3, .c 919, .p pv3 [pv2,pv3,pv37,pv3923], .c 3,
  .c 43, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 587,
]
private theorem h0318c29 : checkBlock 2612483 128 b0318c29 = true := by
  decide +kernel

private def b0318c30 : List Row := [
  .c 3, .c 53, .c 7, .c 3, .c 17, .p pv2 [pv2,pv3,pv239,pv911], .c 3, .c 11, .c 5, .c 3,
  .p pv7 [pv2,pv593,pv2203], .c 337, .c 3, .c 5, .c 79, .c 3, .c 7, .c 31, .c 3, .c 23, .c 13,
  .c 3, .c 139, .c 5, .c 3, .p pv2 [pv2,pv653197], .p pv3 [pv2,pv3,pv5,pv9677], .c 3, .c 5, .c 11,
  .c 3, .c 103, .c 1289, .c 3, .c 41, .c 43, .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv31 [pv2,pv3,pv5,pv7,pv6221], .c 3, .c 5, .c 7, .c 3, .c 13, .c 107, .c 3, .c 1427, .c 109,
  .c 3, .p pv2 [pv2,pv19,pv29,pv2371], .c 5, .c 3, .c 17, .p pv13 [pv2,pv3,pv5,pv17419], .c 3,
  .c 5, .c 13, .c 3, .c 19, .c 11, .c 3, .p pv2 [pv2,pv17,pv31,pv37,pv67], .c 7, .c 3,
  .p pv3 [pv2,pv326609], .c 5, .c 3, .p pv11 [pv2,pv1306439], .p pv11 [pv2,pv3,pv5,pv19,pv191],
  .c 3, .c 5, .c 557, .c 3, .c 223, .p pv2 [pv2,pv3,pv23,pv9467], .c 3, .c 7, .c 19, .c 3, .c 37,
  .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv65323], .c 83, .c 3,
  .p pv5 [pv2,pv131,pv9973], .c 11, .c 3, .c 59, .c 5, .c 3, .c 7, .c 277, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv62213], .c 3, .c 11, .c 7, .c 3, .p pv2 [pv2,pv19,pv34381], .c 31, .c 3,
  .c 349, .c 5, .c 3, .p pv3 [pv2,pv17,pv19213], .c 41, .c 3, .c 5, .c 37, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv271,pv1607], .c 3, .c 13, .p pv2 [pv2,pv3,pv7,pv10369], .c 3, .c 857,
]
private theorem h0318c30 : checkBlock 2612739 128 b0318c30 = true := by
  decide +kernel

private def b0318c31 : List Row := [
  .c 5, .c 3, .p pv7 [pv2,pv1306499], .c 137, .c 3, .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv261301],
  .c 13, .c 3, .c 11, .c 17, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv11,pv59387], .c 317, .c 3,
  .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv89,pv367], .p pv2 [pv2,pv3,pv179,pv811], .c 3, .c 107,
  .c 167, .c 3, .c 17, .c 5, .c 3, .c 47, .c 11, .c 3, .c 5, .c 43, .c 3, .c 191,
  .p pv13 [pv2,pv3,pv7,pv11,pv101], .c 3, .p pv2 [pv2,pv23,pv28403], .c 7, .c 3, .c 11, .c 5,
  .c 3, .c 19, .c 13, .c 3, .c 5, .c 181, .c 3, .c 409, .c 29, .c 3, .c 7,
  .p pv31 [pv2,pv3,pv19,pv73,pv157], .c 3, .p pv3 [pv2,pv53,pv6163], .c 5, .c 3, .c 229, .c 7,
  .c 3, .c 5, .c 11, .c 3, .c 743, .p pv2 [pv2,pv3,pv29,pv2503], .c 3, .c 997,
  .p pv2 [pv2,pv3,pv11,pv17,pv137], .c 3, .c 13, .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv5807],
  .c 3, .c 5, .c 941, .c 3, .c 29, .c 7, .c 3, .p pv5 [pv2,pv109,pv11987], .c 13, .c 3, .c 101,
  .c 5, .c 3, .c 61, .c 73, .c 3, .c 5, .p pv2 [pv2,pv3,pv145177], .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv43,pv15193], .c 37, .c 3, .c 19, .c 5, .c 3, .c 383, .p pv2 [pv2,pv3,pv5,pv87107],
  .c 3, .c 5, .c 41, .c 3, .c 13, .c 17, .c 3, .p pv2 [pv2,pv7,pv11,pv71,pv239],
  .p pv2 [pv2,pv3,pv59,pv3691], .c 3, .c 7, .c 5, .c 3, .c 43, .c 19, .c 3, .c 5, .c 7, .c 3,
]
private theorem h0318c31 : checkBlock 2612995 128 b0318c31 = true := by
  decide +kernel

def rows0318 : List Row :=
  b0318c00 ++ b0318c01 ++ b0318c02 ++ b0318c03 ++ b0318c04 ++ b0318c05 ++ b0318c06 ++ b0318c07 ++
  b0318c08 ++ b0318c09 ++ b0318c10 ++ b0318c11 ++ b0318c12 ++ b0318c13 ++ b0318c14 ++ b0318c15 ++
  b0318c16 ++ b0318c17 ++ b0318c18 ++ b0318c19 ++ b0318c20 ++ b0318c21 ++ b0318c22 ++ b0318c23 ++
  b0318c24 ++ b0318c25 ++ b0318c26 ++ b0318c27 ++ b0318c28 ++ b0318c29 ++ b0318c30 ++ b0318c31

attribute [local irreducible] checkBlock checkRows checkPrime

theorem checked0318 : checkBlock 2605059 4096 rows0318 = true :=
  checkBlock_append h0318c00 (
    checkBlock_append h0318c01 (
    checkBlock_append h0318c02 (
    checkBlock_append h0318c03 (
    checkBlock_append h0318c04 (
    checkBlock_append h0318c05 (
    checkBlock_append h0318c06 (
    checkBlock_append h0318c07 (
    checkBlock_append h0318c08 (
    checkBlock_append h0318c09 (
    checkBlock_append h0318c10 (
    checkBlock_append h0318c11 (
    checkBlock_append h0318c12 (
    checkBlock_append h0318c13 (
    checkBlock_append h0318c14 (
    checkBlock_append h0318c15 (
    checkBlock_append h0318c16 (
    checkBlock_append h0318c17 (
    checkBlock_append h0318c18 (
    checkBlock_append h0318c19 (
    checkBlock_append h0318c20 (
    checkBlock_append h0318c21 (
    checkBlock_append h0318c22 (
    checkBlock_append h0318c23 (
    checkBlock_append h0318c24 (
    checkBlock_append h0318c25 (
    checkBlock_append h0318c26 (
    checkBlock_append h0318c27 (
    checkBlock_append h0318c28 (
    checkBlock_append h0318c29 (
    checkBlock_append h0318c30 (
    h0318c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
