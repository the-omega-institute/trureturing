/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks03/Block0286
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks03/Block0286.checked0286
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table142

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0286c00 : List Row := [
  .c 5, .c 239, .c 3, .c 7, .c 11, .c 3, .c 509, .c 71, .c 3, .p pv2 [pv2,pv585733], .c 5, .c 3,
  .c 29, .c 23, .c 3, .c 5, .c 19, .c 3, .c 13, .p pv5 [pv2,pv3,pv10847], .c 3, .c 17,
  .p pv3 [pv2,pv3,pv390493], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv29,pv10099], .c 53, .c 3, .c 5,
  .c 7, .c 3, .p pv2 [pv2,pv5,pv31,pv3779], .p pv5 [pv2,pv3,pv79,pv4943], .c 3, .c 23, .c 11,
  .c 3, .p pv3 [pv2,pv146437], .c 5, .c 3, .c 1259, .p pv7 [pv2,pv3,pv5,pv11,pv71], .c 3, .c 5,
  .c 83, .c 3, .c 11, .p pv2 [pv2,pv3,pv7,pv27893], .c 3, .p pv3 [pv2,pv13,pv1733], .c 7, .c 3,
  .c 19, .c 5, .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv78101], .c 3, .c 5, .p pv2 [pv2,pv3,pv195253],
  .c 3, .c 967, .c 401, .c 3, .c 7, .p pv13 [pv2,pv3,pv233,pv419], .c 3,
  .p pv2 [pv2,pv491,pv1193], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 59, .c 3, .c 61, .c 31, .c 3,
  .c 11, .c 23, .c 3, .p pv2 [pv2,pv7,pv23909], .c 5, .c 3, .c 7, .c 47, .c 3, .c 5, .c 677, .c 3,
  .c 1301, .c 7, .c 3, .c 13, .c 41, .c 3, .c 29, .c 5, .c 3, .c 761, .c 11, .c 3, .c 5, .c 17,
  .c 3, .c 7, .c 13, .c 3, .c 19, .p pv2 [pv2,pv3,pv7,pv47,pv1187], .c 3, .c 11, .c 5, .c 3,
  .c 331, .c 1201, .c 3, .c 5, .p pv2 [pv2,pv3,pv19,pv43,pv239], .c 3, .c 17,
  .p pv2 [pv2,pv3,pv390527], .c 3, .c 1409, .p pv7 [pv2,pv3,pv113],
]
private theorem h0286c00 : checkBlock 2342915 128 b0286c00 = true := by
  decide +kernel

private def b0286c01 : List Row := [
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv17,pv68917], .c 691, .c 3, .c 5, .c 7, .c 3, .c 41, .c 61,
  .c 3, .c 31, .c 43, .c 3, .p pv2 [pv2,pv1171601], .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 23,
  .c 3, .c 719, .p pv3 [pv2,pv3,pv7,pv6199], .c 3, .c 73, .c 7, .c 3, .p pv3 [pv2,pv19,pv41,pv47],
  .c 5, .c 3, .p pv13 [pv2,pv1171619], .p pv11 [pv2,pv3,pv5,pv23,pv283], .c 3, .c 5, .c 37, .c 3,
  .c 19, .c 11, .c 3, .c 7, .c 31, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv479,pv1223], .c 7, .c 3,
  .c 5, .c 127, .c 3, .c 89, .p pv2 [pv2,pv3,pv109,pv3583], .c 3, .c 29, .c 13, .c 3,
  .p pv2 [pv2,pv7,pv83689], .c 5, .c 3, .c 7, .c 101, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv55793],
  .c 3, .p pv23 [pv2,pv5,pv234331], .c 7, .c 3, .c 1109, .c 11, .c 3, .c 149, .c 5, .c 3,
  .p pv3 [pv2,pv13,pv43,pv131], .c 17, .c 3, .c 5, .c 271, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv53,pv7369], .c 3, .c 431, .p pv19 [pv2,pv3,pv7,pv17,pv547], .c 3, .c 103,
  .c 5, .c 3, .p pv7 [pv2,pv37,pv31667], .p pv13 [pv2,pv3,pv5,pv2441], .c 3, .c 5, .c 13, .c 3,
  .c 43, .c 47, .c 3, .c 79, .c 191, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv585847], .c 109, .c 3,
  .c 5, .c 7, .c 3, .c 23, .c 19, .c 3, .c 11, .p pv11 [pv2,pv3,pv48821], .c 3,
  .p pv2 [pv2,pv585853], .c 5, .c 3, .c 13, .c 59, .c 3, .c 5,
]
private theorem h0286c01 : checkBlock 2343171 128 b0286c01 = true := by
  decide +kernel

private def b0286c02 : List Row := [
  .c 953, .c 3, .c 313, .c 17, .c 3, .c 41, .c 7, .c 3, .c 701, .c 5, .c 3,
  .p pv3 [pv2,pv53,pv5527], .c 11, .c 3, .c 5, .c 43, .c 3, .c 29, .c 1031, .c 3, .c 7, .c 37,
  .c 3, .c 11, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv390581], .c 3, .c 397,
  .c 23, .c 3, .c 13, .c 613, .c 3, .c 101, .c 5, .c 3, .c 7, .c 167, .c 3, .c 5, .c 11, .c 3,
  .p pv3 [pv2,pv5,pv97,pv151], .c 7, .c 3, .p pv5 [pv2,pv67,pv17489],
  .p pv17 [pv2,pv3,pv11,pv269], .c 3, .p pv2 [pv2,pv585883], .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv139,pv281], .c 3, .c 5, .p pv3 [pv2,pv3,pv43399], .c 3, .c 7,
  .p pv31 [pv2,pv3,pv17,pv359], .c 3, .c 1381, .c 61, .c 3, .c 523, .c 5, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv5,pv191,pv409], .c 3, .c 5, .c 29, .c 3, .c 317, .c 11, .c 3, .c 251,
  .p pv2 [pv2,pv3,pv13,pv83,pv181], .c 3, .c 7, .c 5, .c 3, .c 193, .c 13, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv234361], .p pv2 [pv2,pv3,pv19,pv541], .c 3, .c 37, .p pv11 [pv2,pv3,pv130201],
  .c 3, .c 199, .c 5, .c 3, .c 43, .c 19, .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv13,pv4507],
  .p pv3 [pv2,pv3,pv7,pv41,pv1361], .c 3, .c 179, .c 7, .c 3, .c 13, .c 5, .c 3, .c 137,
  .p pv2 [pv2,pv3,pv5,pv11,pv53,pv67], .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv30047], .c 3, .c 11,
  .c 809, .c 3, .c 7, .c 13, .c 3,
]
private theorem h0286c02 : checkBlock 2343427 128 b0286c02 = true := by
  decide +kernel

private def b0286c03 : List Row := [
  .c 41, .c 5, .c 3, .c 1453, .c 7, .c 3, .c 5, .c 277, .c 3, .c 1123, .c 1229, .c 3, .c 19,
  .c 197, .c 3, .c 53, .c 5, .c 3, .c 7, .c 131, .c 3, .c 5, .c 67, .c 3, .c 13, .c 7, .c 3,
  .c 11, .c 17, .c 3, .p pv5 [pv2,pv61,pv19211], .c 5, .c 3, .c 47, .c 29, .c 3, .c 5, .c 13,
  .c 3, .c 7, .p pv3 [pv2,pv3,pv43403], .c 3, .p pv5 [pv2,pv53,pv22111], .c 23, .c 3, .c 17, .c 5,
  .c 3, .p pv2 [pv2,pv431,pv2719], .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv31,pv12601], .c 3,
  .p pv7 [pv2,pv5,pv17,pv811], .p pv5 [pv2,pv3,pv11,pv23,pv193], .c 3, .c 269,
  .p pv3 [pv2,pv3,pv130211], .c 3, .c 7, .c 5, .c 3, .c 13, .c 73, .c 3, .c 5, .c 7, .c 3, .c 19,
  .c 977, .c 3, .c 109, .c 433, .c 3, .p pv3 [pv2,pv292979], .c 5, .c 3, .c 37, .c 17, .c 3, .c 5,
  .c 11, .c 3, .c 79, .c 157, .c 3, .p pv3 [pv2,pv263,pv557], .c 7, .c 3, .c 1319, .c 5, .c 3,
  .c 11, .c 751, .c 3, .c 5, .c 1033, .c 3, .p pv13 [pv2,pv5,pv7,pv11,pv761],
  .p pv2 [pv2,pv3,pv390647], .c 3, .c 7, .p pv13 [pv2,pv3,pv41,pv397], .c 3, .c 59, .c 5, .c 3,
  .p pv2 [pv2,pv317,pv3697], .c 7, .c 3, .c 5, .c 23, .c 3, .c 359, .c 11, .c 3,
  .p pv2 [pv2,pv19,pv30841], .c 149, .c 3, .c 71, .c 5, .c 3, .c 7, .c 487, .c 3, .c 5, .c 47,
]
private theorem h0286c03 : checkBlock 2343683 128 b0286c03 = true := by
  decide +kernel

private def b0286c04 : List Row := [
  .c 3, .c 31, .c 7, .c 3, .c 997, .p pv2 [pv2,pv3,pv195329], .c 3, .c 23, .c 5, .c 3, .c 113,
  .c 1531, .c 3, .c 5, .p pv3 [pv2,pv3,pv241,pv1621], .c 3, .c 7, .c 19, .c 3, .c 17, .c 11, .c 3,
  .c 29, .c 5, .c 3, .p pv2 [pv2,pv585997], .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv65111], .c 3,
  .c 11, .c 31, .c 3, .c 311, .c 79, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv1172009], .c 199, .c 3,
  .c 5, .c 7, .c 3, .c 47, .p pv5 [pv2,pv3,pv2713], .c 3, .p pv2 [pv2,pv586009], .c 127, .c 3,
  .c 13, .c 5, .c 3, .c 19, .p pv13 [pv2,pv3,pv5,pv5209], .c 3, .c 5, .c 313, .c 3, .c 37, .c 659,
  .c 3, .c 11, .c 7, .c 3, .p pv3 [pv2,pv113,pv2593], .c 5, .c 3, .c 17, .c 647, .c 3, .c 5,
  .c 19, .c 3, .c 23, .c 41, .c 3, .c 7, .c 29, .c 3, .c 73, .c 5, .c 3, .c 101, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv195343], .c 3, .c 13, .p pv13 [pv2,pv3,pv11,pv11839], .c 3, .c 31, .c 59,
  .c 3, .c 11, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv1447], .c 3, .c 5, .c 13, .c 3,
  .p pv19 [pv2,pv5,pv173,pv271], .c 7, .c 3, .c 29, .p pv3 [pv2,pv3,pv31,pv4201], .c 3, .c 19,
  .c 5, .c 3, .c 61, .c 89, .c 3, .c 5, .c 11, .c 3, .c 7, .c 23, .c 3,
  .p pv2 [pv2,pv13,pv29,pv3109], .c 31, .c 3, .p pv3 [pv2,pv9157],
]
private theorem h0286c04 : checkBlock 2343939 128 b0286c04 = true := by
  decide +kernel

private def b0286c05 : List Row := [
  .c 5, .c 3, .c 11, .c 19, .c 3, .c 5, .c 71, .c 3, .c 859, .c 233, .c 3, .c 149, .c 47, .c 3,
  .c 7, .c 5, .c 3, .c 23, .c 43, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv29303], .c 11, .c 3,
  .c 59, .c 17, .c 3, .p pv2 [pv2,pv23,pv83,pv307], .c 5, .c 3, .p pv2 [pv2,pv7,pv19,pv1259],
  .p pv2 [pv2,pv3,pv5,pv89,pv439], .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv47,pv163], .c 3,
  .p pv17 [pv2,pv5,pv359,pv653], .c 29, .c 3, .c 13, .c 7, .c 3, .c 17, .c 5, .c 3, .c 1097,
  .c 61, .c 3, .c 5, .p pv13 [pv2,pv3,pv19,pv53,pv97], .c 3, .p pv3 [pv2,pv5,pv7,pv17,pv197],
  .c 13, .c 3, .c 7, .c 11, .c 3, .c 31, .c 5, .c 3, .p pv19 [pv2,pv311,pv3769], .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv390721], .c 3, .c 11, .p pv2 [pv2,pv3,pv347,pv563], .c 3,
  .p pv3 [pv2,pv146521], .c 41, .c 3, .c 383, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 37, .c 3,
  .p pv7 [pv2,pv5,pv29,pv43,pv47], .c 7, .c 3, .c 23, .c 919, .c 3, .c 1249, .c 5, .c 3,
  .p pv2 [pv2,pv643,pv1823], .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv35521], .c 3, .c 7, .c 97,
  .c 3, .c 11, .c 223, .c 3, .c 43, .c 5, .c 3, .p pv3 [pv2,pv11,pv26641], .c 113, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv24421], .c 3, .c 41, .c 1481, .c 3, .p pv2 [pv2,pv7,pv151,pv1109], .c 19,
  .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv89,pv13171], .c 11, .c 3, .c 5, .c 7, .c 3,
]
private theorem h0286c05 : checkBlock 2344195 128 b0286c05 = true := by
  decide +kernel

private def b0286c06 : List Row := [
  .c 677, .c 17, .c 3, .p pv3 [pv2,pv227,pv1291], .c 13, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv31,pv37,pv73], .p pv3 [pv2,pv3,pv5,pv17,pv4597], .c 3, .c 5, .c 107, .c 3,
  .c 109, .c 59, .c 3, .c 17, .c 7, .c 3, .c 181, .c 5, .c 3, .c 31, .c 47, .c 3, .c 5, .c 11,
  .c 3, .c 13, .c 101, .c 3, .c 7, .p pv3 [pv2,pv3,pv11,pv3947], .c 3, .p pv2 [pv2,pv1172261],
  .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 13, .c 3, .c 73, .c 19, .c 3, .c 127, .c 421, .c 3,
  .p pv3 [pv2,pv7,pv5981], .c 5, .c 3, .c 7, .c 31, .c 3, .c 5, .c 661, .c 3,
  .p pv11 [pv2,pv5,pv234457], .c 7, .c 3, .c 151, .c 37, .c 3, .c 1117, .c 5, .c 3, .c 13, .c 251,
  .c 3, .c 5, .c 23, .c 3, .c 7, .p pv2 [pv2,pv3,pv13,pv30059], .c 3,
  .p pv5 [pv2,pv11,pv17,pv6269], .c 523, .c 3, .c 1459, .c 5, .c 3, .c 19, .c 29, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv41,pv353], .c 3, .p pv7 [pv2,pv5,pv234463], .c 71, .c 3, .c 113, .c 11, .c 3,
  .c 7, .c 5, .c 3, .p pv3 [pv2,pv293081], .p pv2 [pv2,pv3,pv5,pv7,pv11,pv29], .c 3, .c 5, .c 7,
  .c 3, .c 11, .c 709, .c 3, .c 13, .c 173, .c 3, .p pv3 [pv2,pv11,pv6661], .c 5, .c 3, .c 29,
  .c 769, .c 3, .c 5, .c 73, .c 3, .c 17, .c 13, .c 3, .p pv3 [pv2,pv293087], .c 7, .c 3,
  .p pv5 [pv2,pv1172351], .c 5,
]
private theorem h0286c06 : checkBlock 2344451 128 b0286c06 = true := by
  decide +kernel

private def b0286c07 : List Row := [
  .c 3, .p pv2 [pv2,pv17,pv29,pv41], .p pv3 [pv2,pv3,pv5,pv78157], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv31,pv191], .c 3, .c 179, .p pv2 [pv2,pv3,pv593,pv659], .c 3, .c 7,
  .c 1213, .c 3, .c 19, .c 5, .c 3, .c 683, .c 7, .c 3, .c 5, .c 31, .c 3,
  .p pv13 [pv2,pv5,pv83,pv113], .p pv5 [pv2,pv3,pv19,pv857], .c 3, .c 193, .c 17, .c 3, .c 367,
  .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .p pv13 [pv2,pv3,pv7,pv17,pv821], .c 3, .c 23, .c 7, .c 3,
  .p pv2 [pv2,pv1172393], .p pv7 [pv2,pv3,pv7237], .c 3, .c 11, .c 5, .c 3, .c 67, .c 37, .c 3,
  .c 5, .c 467, .c 3, .c 7, .c 149, .c 3, .c 199, .p pv3 [pv2,pv3,pv7,pv55829], .c 3, .c 13, .c 5,
  .c 3, .c 239, .c 41, .c 3, .c 5, .c 11, .c 3, .c 607, .c 211, .c 3, .c 19, .c 13, .c 3, .c 7,
  .c 5, .c 3, .c 11, .c 17, .c 3, .c 5, .c 7, .c 3, .c 31, .c 23, .c 3, .c 47, .c 53, .c 3, .c 89,
  .c 5, .c 3, .p pv3 [pv2,pv7,pv13,pv3221], .c 197, .c 3, .c 5, .c 853, .c 3, .c 13, .c 11, .c 3,
  .c 191, .c 7, .c 3, .c 41, .c 5, .c 3, .c 23, .p pv13 [pv2,pv3,pv5,pv19541], .c 3, .c 5, .c 13,
  .c 3, .c 349, .c 31, .c 3, .c 7, .p pv3 [pv2,pv3,pv283,pv1381], .c 3,
  .p pv5 [pv2,pv19,pv23,pv2683], .c 5, .c 3, .c 37, .c 7, .c 3, .c 5, .c 79, .c 3, .c 19,
]
private theorem h0286c07 : checkBlock 2344707 128 b0286c07 = true := by
  decide +kernel

private def b0286c08 : List Row := [
  .c 17, .c 3, .p pv5 [pv2,pv13,pv90191], .c 11, .c 3, .p pv2 [pv2,pv7,pv89,pv941], .c 5, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv5,pv11,pv17,pv19], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv37,pv503], .c 3,
  .c 11, .c 7, .c 3, .c 17, .c 19, .c 3, .c 1361, .c 5, .c 3, .p pv3 [pv2,pv146563], .c 23, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv199,pv491], .c 3, .c 7, .c 37, .c 3, .c 29, .c 137, .c 3,
  .p pv3 [pv2,pv293129], .c 5, .c 3, .p pv7 [pv2,pv53,pv22123], .p pv17 [pv2,pv3,pv5,pv3257],
  .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv35531], .c 3, .c 373, .p pv2 [pv2,pv3,pv73,pv2677], .c 3,
  .c 11, .c 71, .c 3, .c 7, .c 5, .c 3, .c 139, .c 431, .c 3, .c 5, .c 7, .c 3, .c 163, .c 13,
  .c 3, .p pv5 [pv2,pv1172543], .c 113, .c 3, .c 251, .c 5, .c 3, .c 17, .c 11, .c 3, .c 5,
  .c 461, .c 3, .c 149, .c 19, .c 3, .p pv2 [pv2,pv17,pv34487], .c 7, .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv433,pv677], .p pv2 [pv2,pv3,pv5,pv71,pv367], .c 3, .c 5, .c 227, .c 3,
  .p pv11 [pv2,pv5,pv7,pv2393], .c 29, .c 3, .c 7, .c 23, .c 3, .p pv3 [pv2,pv36643], .c 5, .c 3,
  .c 41, .c 7, .c 3, .c 5, .c 11, .c 3, .c 37, .c 307, .c 3, .c 43,
  .p pv13 [pv2,pv3,pv11,pv35533], .c 3, .c 337, .c 5, .c 3, .c 7, .c 59, .c 3, .c 5, .c 53, .c 3,
  .c 17, .c 7, .c 3, .c 103, .p pv23 [pv2,pv3,pv19,pv37,pv139], .c 3, .c 13, .c 5, .c 3,
]
private theorem h0286c08 : checkBlock 2344963 128 b0286c08 = true := by
  decide +kernel

private def b0286c09 : List Row := [
  .p pv2 [pv2,pv17,pv23,pv2999], .c 283, .c 3, .c 5, .c 19, .c 3, .c 7, .c 11, .c 3, .c 1021,
  .c 13, .c 3, .c 31, .c 5, .c 3, .p pv3 [pv2,pv83,pv883], .c 311, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv32573], .c 3, .p pv2 [pv2,pv5,pv149,pv787], .c 43, .c 3, .c 61, .c 17, .c 3,
  .c 7, .c 5, .c 3, .p pv17 [pv2,pv13,pv90203], .c 389, .c 3, .c 5, .c 7, .c 3, .c 13, .c 131,
  .c 3, .p pv3 [pv2,pv146581], .c 11, .c 3, .c 17, .c 5, .c 3, .c 59, .c 937, .c 3, .c 5, .c 13,
  .c 3, .c 11, .c 41, .c 3, .p pv5 [pv2,pv1172663], .c 7, .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv613,pv1913], .c 19, .c 3, .c 5, .c 47, .c 3, .p pv7 [pv2,pv5,pv7,pv6701], .c 109,
  .c 3, .c 7, .c 277, .c 3, .c 97, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv11,pv2221], .c 3, .c 659, .p pv3 [pv2,pv3,pv13,pv257], .c 3, .c 11, .c 61,
  .c 3, .c 37, .c 5, .c 3, .c 7, .p pv19 [pv2,pv3,pv5,pv1303], .c 3, .c 5, .c 163, .c 3, .c 269,
  .c 7, .c 3, .c 19, .c 641, .c 3, .c 157, .c 5, .c 3, .c 31, .c 11, .c 3, .c 5, .c 179, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv11,pv35537], .c 3, .c 13, .c 401, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv563,pv2083], .p pv2 [pv2,pv3,pv5,pv13,pv31,pv97], .c 3, .c 5, .c 37, .c 3, .c 23,
  .c 13,
]
private theorem h0286c09 : checkBlock 2345219 128 b0286c09 = true := by
  decide +kernel

private def b0286c10 : List Row := [
  .c 3, .p pv2 [pv2,pv7,pv211,pv397], .p pv3 [pv2,pv3,pv43,pv9091], .c 3, .c 7, .c 5, .c 3,
  .c 503, .c 29, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv4691], .c 1493, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv11,pv5923], .c 3, .c 1171, .c 5, .c 3, .c 11, .c 43, .c 3, .c 5, .c 557, .c 3,
  .c 19, .p pv2 [pv2,pv3,pv7,pv3989], .c 3, .p pv3 [pv2,pv67,pv547], .c 7, .c 3,
  .p pv5 [pv2,pv521,pv2251], .c 5, .c 3, .c 29, .c 13, .c 3, .c 5, .c 97, .c 3, .c 433, .c 11,
  .c 3, .c 7, .c 19, .c 3, .p pv2 [pv2,pv61,pv9613], .c 5, .c 3, .c 181, .c 7, .c 3, .c 5,
  .c 1447, .c 3, .c 227, .p pv5 [pv2,pv3,pv17,pv5749], .c 3, .c 821, .p pv3 [pv2,pv3,pv14479],
  .c 3, .c 13, .c 5, .c 3, .c 7, .c 233, .c 3, .c 5, .p pv11 [pv2,pv3,pv7,pv13,pv179], .c 3,
  .c 53, .c 7, .c 3, .c 71, .c 11, .c 3, .c 61, .c 5, .c 3, .c 257,
  .p pv19 [pv2,pv3,pv5,pv11,pv1777], .c 3, .c 5, .c 229, .c 3, .c 7, .c 241, .c 3,
  .p pv3 [pv2,pv293207], .p pv2 [pv2,pv3,pv7,pv55849], .c 3, .c 59, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv79,pv571], .c 191, .c 3, .c 5, .c 17, .c 3, .c 13, .c 19, .c 3, .c 211,
  .c 37, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv71,pv16519], .c 23, .c 3, .c 5, .c 7, .c 3, .c 17,
  .p pv5 [pv2,pv3,pv48869], .c 3, .c 11, .c 947, .c 3, .c 29, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv11,pv17],
]
private theorem h0286c10 : checkBlock 2345475 128 b0286c10 = true := by
  decide +kernel

private def b0286c11 : List Row := [
  .p pv3 [pv2,pv3,pv5,pv78191], .c 3, .c 5, .c 67, .c 3, .c 467, .p pv5 [pv2,pv3,pv7,pv18617],
  .c 3, .c 23, .c 7, .c 3, .p pv3 [pv2,pv29,pv10111], .c 5, .c 3, .c 13, .c 11, .c 3, .c 5,
  .c 113, .c 3, .c 1163, .c 89, .c 3, .c 7, .c 17, .c 3, .c 11, .c 5, .c 3, .c 109, .c 7, .c 3,
  .c 5, .c 19, .c 3, .c 31, .p pv2 [pv2,pv3,pv390967], .c 3, .p pv5 [pv2,pv1172903],
  .p pv13 [pv2,pv3,pv48871], .c 3, .c 17, .c 5, .c 3, .c 7, .c 1433, .c 3, .c 5, .c 11, .c 3,
  .p pv13 [pv2,pv5,pv17,pv13799], .c 7, .c 3, .c 13, .c 23, .c 3, .p pv2 [pv2,pv1172921], .c 5,
  .c 3, .c 11, .c 137, .c 3, .c 5, .c 337, .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv1172933],
  .p pv2 [pv2,pv3,pv7,pv29,pv107], .c 3, .c 19, .c 5, .c 3, .c 487, .c 17, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv53,pv2459], .c 3, .p pv7 [pv2,pv5,pv234589], .c 11, .c 3, .c 29, .c 59, .c 3,
  .c 7, .c 5, .c 3, .p pv2 [pv2,pv23,pv43,pv593], .c 19, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv7331], .p pv5 [pv2,pv3,pv1609], .c 3, .c 101, .c 859, .c 3, .c 431, .c 5,
  .c 3, .c 53, .c 13, .c 3, .c 5, .c 1123, .c 3, .c 43, .p pv5 [pv2,pv3,pv7,pv3491], .c 3,
  .p pv2 [pv2,pv31,pv18919], .c 7, .c 3, .p pv2 [pv2,pv1172981], .c 5, .c 3,
  .p pv7 [pv2,pv19,pv7717], .p pv2 [pv2,pv3,pv5,pv11,pv7109], .c 3, .c 5, .c 23, .c 3, .c 11,
  .c 17, .c 3,
]
private theorem h0286c11 : checkBlock 2345731 128 b0286c11 = true := by
  decide +kernel

private def b0286c12 : List Row := [
  .c 7, .p pv2 [pv2,pv3,pv137,pv1427], .c 3, .c 13, .c 5, .c 3, .c 61, .c 7, .c 3, .c 5, .c 109,
  .c 3, .c 199, .c 29, .c 3, .c 17, .c 13, .c 3, .c 23, .c 5, .c 3, .c 7, .c 103, .c 3, .c 5,
  .c 43, .c 3, .c 1063, .c 7, .c 3, .c 11, .c 31, .c 3, .c 71, .c 5, .c 3, .c 37, .c 41, .c 3,
  .c 5, .c 347, .c 3, .c 7, .c 197, .c 3, .c 233, .c 131, .c 3, .c 547, .c 5, .c 3,
  .p pv3 [pv2,pv293261], .c 11, .c 3, .c 5, .c 13, .c 3, .c 19, .c 881, .c 3,
  .p pv5 [pv2,pv7,pv113,pv1483], .c 211, .c 3, .c 7, .c 5, .c 3, .c 17, .c 61, .c 3, .c 5, .c 7,
  .c 3, .c 883, .c 37, .c 3, .p pv3 [pv2,pv13,pv17,pv1327], .c 19, .c 3, .c 41, .c 5, .c 3, .c 13,
  .c 53, .c 3, .c 5, .c 11, .c 3, .c 23, .c 761, .c 3, .p pv5 [pv2,pv43,pv27281], .c 7, .c 3,
  .c 31, .c 5, .c 3, .c 11, .c 139, .c 3, .c 5, .c 17, .c 3, .p pv7 [pv2,pv5,pv7,pv11,pv277],
  .c 47, .c 3, .c 7, .c 827, .c 3, .p pv2 [pv2,pv1173101], .c 5, .c 3, .c 43, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv29,pv3371], .c 3, .c 17, .c 11, .c 3, .c 13, .c 653, .c 3, .c 421, .c 5, .c 3,
  .c 7, .p pv17 [pv2,pv3,pv5,pv13,pv47],
]
private theorem h0286c12 : checkBlock 2345987 128 b0286c12 = true := by
  decide +kernel

private def b0286c13 : List Row := [
  .c 3, .c 5, .c 701, .c 3, .c 401, .c 7, .c 3, .c 53, .p pv3 [pv2,pv3,pv383,pv1021], .c 3,
  .c 239, .c 5, .c 3, .p pv2 [pv2,pv586567], .p pv7 [pv2,pv3,pv5,pv197,pv397], .c 3, .c 5,
  .p pv7 [pv2,pv3,pv23,pv8501], .c 3, .c 7, .c 599, .c 3, .c 47, .c 11, .c 3, .c 73, .c 5, .c 3,
  .c 23, .c 193, .c 3, .c 5, .c 41, .c 3, .c 11, .p pv13 [pv2,pv3,pv59,pv1657], .c 3, .c 541,
  .c 1381, .c 3, .c 7, .c 5, .c 3, .c 19, .c 13, .c 3, .c 5, .c 7, .c 3, .c 131,
  .p pv3 [pv2,pv3,pv391057], .c 3, .p pv2 [pv2,pv1173173], .p pv13 [pv2,pv3,pv19,pv41,pv251],
  .c 3, .c 283, .c 5, .c 3, .c 31, .c 29, .c 3, .c 5, .c 19, .c 3, .c 59, .c 823, .c 3, .c 11,
  .c 7, .c 3, .c 13, .c 5, .c 3, .c 41, .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv89], .c 3,
  .c 307, .c 107, .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv586603], .c 5, .c 3, .c 29, .c 7, .c 3,
  .c 5, .c 433, .c 3, .p pv17 [pv2,pv5,pv41,pv59,pv97], .c 409, .c 3, .c 23, .c 73, .c 3, .c 11,
  .c 5, .c 3, .c 7, .c 617, .c 3, .c 5, .c 1373, .c 3, .c 13, .c 7, .c 3, .c 43, .c 53, .c 3,
  .p pv3 [pv2,pv131,pv2239], .c 5, .c 3, .c 71, .c 19, .c 3, .c 5, .c 11, .c 3, .c 7, .c 17, .c 3,
  .c 863,
]
private theorem h0286c13 : checkBlock 2346243 128 b0286c13 = true := by
  decide +kernel

private def b0286c14 : List Row := [
  .c 227, .c 3, .c 37, .c 5, .c 3, .c 11, .c 179, .c 3, .c 5, .c 167, .c 3,
  .p pv13 [pv2,pv5,pv11,pv5333], .p pv2 [pv2,pv3,pv47,pv53,pv157], .c 3, .c 17, .c 23, .c 3, .c 7,
  .c 5, .c 3, .c 13, .c 67, .c 3, .c 5, .c 7, .c 3, .p pv11 [pv2,pv5,pv71,pv661], .c 11, .c 3,
  .c 19, .p pv3 [pv2,pv3,pv113,pv3461], .c 3, .c 229, .c 5, .c 3, .c 47, .c 443, .c 3, .c 5,
  .c 37, .c 3, .p pv2 [pv2,pv5,pv117329], .c 1511, .c 3, .p pv2 [pv2,pv11,pv106663], .c 7, .c 3,
  .c 29, .c 5, .c 3, .c 251, .c 149, .c 3, .c 5, .c 31, .c 3, .p pv2 [pv2,pv5,pv7,pv4789],
  .c 1049, .c 3, .c 7, .c 11, .c 3, .p pv5 [pv2,pv29,pv40459], .c 5, .c 3, .c 17, .c 7, .c 3,
  .c 5, .c 293, .c 3, .c 11, .c 13, .c 3, .c 1181, .c 103, .c 3, .p pv3 [pv2,pv7,pv11,pv19,pv401],
  .c 5, .c 3, .c 7, .c 109, .c 3, .c 5, .c 23, .c 3, .c 19, .c 7, .c 3, .p pv2 [pv2,pv41,pv349],
  .c 157, .c 3, .c 839, .c 5, .c 3, .c 631, .c 151, .c 3, .c 5, .c 17, .c 3, .c 7, .c 1303, .c 3,
  .c 11, .c 19, .c 3, .c 23, .c 5, .c 3, .p pv7 [pv2,pv11,pv106669], .c 13, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv227,pv1723], .c 3, .c 17, .p pv23 [pv2,pv3,pv7243], .c 3, .c 139,
  .p pv13 [pv2,pv3,pv29,pv13487], .c 3, .c 7, .c 5, .c 3, .c 263, .c 11, .c 3,
]
private theorem h0286c14 : checkBlock 2346499 128 b0286c14 = true := by
  decide +kernel

private def b0286c15 : List Row := [
  .c 5, .c 7, .c 3, .c 347, .c 71, .c 3, .c 29, .p pv7 [pv2,pv3,pv43,pv379], .c 3, .c 11, .c 5,
  .c 3, .p pv2 [pv2,pv7,pv167627], .p pv2 [pv2,pv3,pv5,pv39113], .c 3, .c 5, .c 53, .c 3,
  .p pv13 [pv2,pv5,pv331,pv709], .c 31, .c 3, .c 499, .c 7, .c 3, .p pv2 [pv2,pv1173401], .c 5,
  .c 3, .c 67, .c 43, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv7,pv16763], .c 19, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv11,pv23,pv773], .c 3, .c 17, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv181,pv2161], .c 3, .c 13, .c 61, .c 3, .p pv3 [pv2,pv293357],
  .p pv2 [pv2,pv3,pv241,pv541], .c 3, .p pv23 [pv2,pv7,pv167633], .c 5, .c 3, .c 7, .c 1249, .c 3,
  .c 5, .c 13, .c 3, .c 41, .c 7, .c 3, .p pv5 [pv2,pv31,pv37853], .c 1151, .c 3, .c 53, .c 5,
  .c 3, .c 19, .c 17, .c 3, .c 5, .c 971, .c 3, .c 7, .p pv5 [pv2,pv3,pv29,pv281], .c 3, .c 31,
  .c 283, .c 3, .c 449, .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv89,pv293], .c 3, .c 5, .c 19,
  .c 3, .c 29, .c 23, .c 3, .c 37, .c 11, .c 3, .c 7, .c 5, .c 3, .p pv17 [pv2,pv103,pv11393],
  .c 59, .c 3, .c 5, .c 7, .c 3, .c 11, .p pv2 [pv2,pv3,pv195581], .c 3, .p pv3 [pv2,pv71,pv1033],
  .c 31, .c 3, .c 43, .c 5, .c 3, .c 23, .c 83, .c 3, .c 5, .p pv17 [pv2,pv3,pv131,pv1493], .c 3,
  .p pv3 [pv2,pv5,pv2347], .c 17, .c 3, .c 13, .c 7,
]
private theorem h0286c15 : checkBlock 2346755 128 b0286c15 = true := by
  decide +kernel

private def b0286c16 : List Row := [
  .c 3, .c 19, .c 5, .c 3, .c 89, .c 37, .c 3, .c 5, .c 181, .c 3, .p pv7 [pv2,pv5,pv7,pv33529],
  .c 13, .c 3, .c 7, .c 47, .c 3, .p pv2 [pv2,pv1173521], .c 5, .c 3,
  .p pv3 [pv2,pv11,pv149,pv179], .c 7, .c 3, .c 5, .c 29, .c 3, .c 103, .p pv5 [pv2,pv3,pv391177],
  .c 3, .p pv2 [pv2,pv733,pv1601], .c 43, .c 3, .c 193, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .c 127, .c 3, .c 173, .c 7, .c 3, .c 61, .c 241, .c 3, .c 11, .c 5, .c 3, .c 97, .c 13, .c 3,
  .c 5, .c 311, .c 3, .c 7, .c 113, .c 3, .c 19, .p pv13 [pv2,pv3,pv7,pv4657], .c 3, .c 47, .c 5,
  .c 3, .c 17, .p pv7 [pv2,pv3,pv5,pv39119], .c 3, .c 5, .c 11, .c 3,
  .p pv11 [pv2,pv5,pv13,pv23,pv157], .p pv11 [pv2,pv3,pv107,pv457], .c 3, .c 83, .c 677, .c 3,
  .c 7, .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv7,pv11177], .c 3, .c 5, .c 7, .c 3, .c 257,
  .p pv3 [pv2,pv3,pv130399], .c 3, .c 313, .c 13, .c 3, .c 281, .c 5, .c 3, .c 191,
  .p pv7 [pv2,pv3,pv5,pv163], .c 3, .c 5, .c 17, .c 3, .c 53, .c 11, .c 3, .p pv3 [pv2,pv146701],
  .c 7, .c 3, .c 293, .c 5, .c 3, .p pv2 [pv2,pv13,pv45139], .c 29, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv113,pv577], .c 3, .c 13, .c 37, .c 3, .c 7, .p pv13 [pv2,pv3,pv79,pv619],
  .c 3, .p pv2 [pv2,pv586813], .c 5, .c 3, .c 107, .c 7, .c 3, .c 5,
]
private theorem h0286c16 : checkBlock 2347011 128 b0286c16 = true := by
  decide +kernel

private def b0286c17 : List Row := [
  .c 13, .c 3, .p pv11 [pv2,pv5,pv234727], .p pv5 [pv2,pv3,pv10867], .c 3, .p pv2 [pv2,pv586819],
  .c 11, .c 3, .p pv2 [pv2,pv7,pv167663], .c 5, .c 3, .c 7, .c 41, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv499], .c 3, .c 11, .c 7, .c 3, .c 157, .c 17, .c 3,
  .p pv3 [pv2,pv11,pv13337], .c 5, .c 3, .c 13, .c 47, .c 3, .c 5, .c 43, .c 3, .c 7, .c 439,
  .c 3, .p pv3 [pv2,pv19,pv15443], .p pv2 [pv2,pv3,pv7,pv55889], .c 3, .c 17, .c 5, .c 3, .c 113,
  .c 31, .c 3, .c 5, .c 23, .c 3, .p pv3 [pv2,pv5,pv17,pv863], .c 163, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv47,pv2081], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv11,pv106699], .c 571, .c 3,
  .c 5, .c 7, .c 3, .c 37, .c 19, .c 3, .c 13, .c 541, .c 3, .c 23, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv20959], .c 11, .c 3, .c 5, .c 1321, .c 3, .p pv2 [pv2,pv5,pv117371], .c 13,
  .c 3, .p pv2 [pv2,pv23,pv51031], .c 7, .c 3, .c 11, .c 5, .c 3, .p pv17 [pv2,pv257,pv4567],
  .p pv13 [pv2,pv3,pv5,pv9781], .c 3, .c 5, .p pv3 [pv2,pv3,pv151,pv2591], .c 3,
  .p pv2 [pv2,pv5,pv7,pv19,pv353], .p pv2 [pv2,pv3,pv197,pv331], .c 3, .c 7, .c 193, .c 3, .c 29,
  .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 11, .c 3, .c 599, .c 727, .c 3, .p pv5 [pv2,pv1173743],
  .c 83, .c 3, .p pv2 [pv2,pv7,pv29,pv59], .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 19, .c 3,
  .p pv19 [pv2,pv5,pv11,pv21341], .c 7, .c 3, .c 1231, .c 167, .c 3,
]
private theorem h0286c17 : checkBlock 2347267 128 b0286c17 = true := by
  decide +kernel

private def b0286c18 : List Row := [
  .p pv2 [pv2,pv839,pv1399], .c 5, .c 3, .c 53, .c 1459, .c 3, .c 5, .c 31, .c 3, .c 7, .c 11,
  .c 3, .c 17, .p pv11 [pv2,pv3,pv7,pv27947], .c 3, .c 13, .c 5, .c 3, .p pv7 [pv2,pv1173779],
  .p pv13 [pv2,pv3,pv5,pv6521], .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv30097], .c 3, .c 139,
  .p pv2 [pv2,pv3,pv83,pv2357], .c 3, .p pv5 [pv2,pv7,pv11,pv37,pv103], .c 13, .c 3, .c 7, .c 5,
  .c 3, .c 1483, .p pv7 [pv2,pv3,pv5,pv7,pv1597], .c 3, .c 5, .c 7, .c 3, .c 773, .c 47, .c 3,
  .c 73, .c 11, .c 3, .c 37, .c 5, .c 3, .c 41, .c 19, .c 3, .c 5, .p pv2 [pv2,pv3,pv521,pv751],
  .c 3, .c 11, .c 23, .c 3, .c 29, .c 7, .c 3, .c 79, .c 5, .c 3, .c 17, .c 131, .c 3, .c 5,
  .c 13, .c 3, .c 31, .p pv3 [pv2,pv3,pv373,pv1049], .c 3, .c 7, .c 59, .c 3, .c 271, .c 5, .c 3,
  .c 23, .c 7, .c 3, .c 5, .c 37, .c 3, .c 97, .p pv2 [pv2,pv3,pv31,pv6311], .c 3, .c 11, .c 367,
  .c 3, .p pv23 [pv2,pv7,pv23,pv317], .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv139,pv563], .c 3,
  .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv58693], .c 7, .c 3, .p pv5 [pv2,pv433,pv2711], .c 877,
  .c 3, .p pv2 [pv2,pv586933], .c 5, .c 3, .c 311, .c 11, .c 3, .c 5, .c 67, .c 3, .c 7, .c 29,
  .c 3, .c 43, .p pv7 [pv2,pv3,pv7,pv6211], .c 3, .c 11, .c 5, .c 3, .c 137, .c 23, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv1019],
]
private theorem h0286c18 : checkBlock 2347523 128 b0286c18 = true := by
  decide +kernel

private def b0286c19 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv117389], .c 41, .c 3, .c 13, .p pv13 [pv2,pv3,pv97,pv2017], .c 3, .c 7,
  .c 5, .c 3, .c 733, .c 79, .c 3, .c 5, .c 7, .c 3, .c 19, .c 13, .c 3, .c 23, .c 17, .c 3,
  .p pv5 [pv2,pv241,pv4871], .c 5, .c 3, .c 11, .p pv13 [pv2,pv3,pv5,pv19,pv1373], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv17,pv677], .c 3, .p pv3 [pv2,pv5,pv11,pv23,pv29], .c 43, .c 3, .c 31, .c 7,
  .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv397,pv2957], .c 227, .c 3, .c 5, .c 619, .c 3,
  .p pv7 [pv2,pv5,pv7,pv17,pv1973], .c 11, .c 3, .c 7, .c 337, .c 3, .p pv2 [pv2,pv1173941], .c 5,
  .c 3, .c 887, .c 7, .c 3, .c 5, .c 883, .c 3, .c 107, .p pv3 [pv2,pv3,pv130439], .c 3,
  .p pv2 [pv2,pv11,pv19,pv41,pv137], .c 23, .c 3, .c 131, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5,
  .c 29, .c 3, .p pv11 [pv2,pv5,pv13,pv18061], .c 7, .c 3, .c 229, .c 11, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv67,pv8761], .c 61, .c 3, .c 5, .p pv11 [pv2,pv3,pv13,pv29,pv173], .c 3, .c 7,
  .c 19, .c 3, .c 223, .c 13, .c 3, .c 1487, .c 5, .c 3, .c 47, .p pv19 [pv2,pv3,pv5,pv39133],
  .c 3, .c 5, .c 83, .c 3, .p pv7 [pv2,pv5,pv234799], .c 1061, .c 3, .p pv2 [pv2,pv7,pv83857],
  .p pv11 [pv2,pv3,pv89,pv4397], .c 3, .c 7, .c 5, .c 3, .c 1033, .p pv2 [pv2,pv3,pv5,pv7,pv3727],
  .c 3, .c 5, .c 7, .c 3, .c 13, .c 17, .c 3, .c 11, .c 41, .c 3, .c 31,
]
private theorem h0286c19 : checkBlock 2347779 128 b0286c19 = true := by
  decide +kernel

private def b0286c20 : List Row := [
  .c 5, .c 3, .c 19, .c 71, .c 3, .c 5, .c 13, .c 3, .c 283, .p pv2 [pv2,pv3,pv7,pv27953], .c 3,
  .c 17, .c 7, .c 3, .c 241, .c 5, .c 3, .c 409, .c 11, .c 3, .c 5, .c 19, .c 3,
  .p pv11 [pv2,pv5,pv7,pv599], .p pv2 [pv2,pv3,pv11,pv59,pv67], .c 3, .c 7,
  .p pv19 [pv2,pv3,pv227,pv431], .c 3, .c 11, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 601, .c 3,
  .c 41, .c 181, .c 3, .c 79, .p pv11 [pv2,pv3,pv73,pv1787], .c 3, .p pv2 [pv2,pv7,pv179,pv937],
  .c 5, .c 3, .c 7, .c 37, .c 3, .c 5, .c 11, .c 3, .c 59, .c 7, .c 3, .c 521, .c 67, .c 3, .c 19,
  .c 5, .c 3, .c 11, .p pv11 [pv2,pv3,pv5,pv1223], .c 3, .c 5, .c 47, .c 3, .c 7, .c 383, .c 3,
  .c 13, .p pv3 [pv2,pv3,pv7,pv163], .c 3, .c 71, .c 5, .c 3, .p pv2 [pv2,pv29,pv31,pv653], .c 19,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv79,pv2477], .c 3, .c 151, .c 11, .c 3, .p pv5 [pv2,pv7,pv167729],
  .c 257, .c 3, .c 7, .c 5, .c 3, .c 31, .p pv2 [pv2,pv3,pv5,pv7,pv5591], .c 3, .c 5, .c 7, .c 3,
  .c 23, .p pv5 [pv2,pv3,pv97843], .c 3, .p pv2 [pv2,pv11,pv83,pv643], .p pv11 [pv2,pv3,pv391373],
  .c 3, .c 307, .c 5, .c 3, .c 157, .p pv2 [pv2,pv3,pv5,pv31,pv101], .c 3, .c 5,
  .p pv11 [pv2,pv3,pv61,pv401], .c 3, .c 17, .c 569, .c 3, .c 19, .c 7, .c 3, .c 43, .c 5, .c 3,
  .c 37, .c 13, .c 3, .c 5, .c 1103, .c 3,
]
private theorem h0286c20 : checkBlock 2348035 128 b0286c20 = true := by
  decide +kernel

private def b0286c21 : List Row := [
  .c 11, .p pv2 [pv2,pv3,pv195691], .c 3, .c 7, .p pv13 [pv2,pv3,pv43487], .c 3,
  .p pv5 [pv2,pv11,pv173,pv617], .c 5, .c 3, .c 853, .c 7, .c 3, .c 5, .c 61, .c 3,
  .p pv3 [pv2,pv5,pv13,pv1129], .c 23, .c 3, .c 263, .c 17, .c 3, .c 13, .c 5, .c 3, .c 7, .c 163,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv11,pv13,pv17,pv23], .c 3, .c 101, .c 7, .c 3, .c 11, .c 13,
  .c 3, .c 17, .c 5, .c 3, .c 23, .p pv2 [pv2,pv3,pv5,pv97,pv269], .c 3, .c 5, .c 53, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv391397], .c 3, .c 983, .c 149, .c 3, .c 389, .c 5, .c 3, .c 199, .c 11, .c 3,
  .c 5, .c 233, .c 3, .c 13, .c 223, .c 3, .c 67, .c 19, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv587107], .c 17, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv58711], .c 89, .c 3,
  .p pv5 [pv2,pv761,pv1543], .c 29, .c 3, .c 491, .c 5, .c 3, .p pv2 [pv2,pv7,pv167747], .c 23,
  .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv234847], .p pv5 [pv2,pv3,pv7,pv1997], .c 3,
  .p pv2 [pv2,pv13,pv19,pv2377], .c 7, .c 3, .c 53, .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv78283], .c 3, .c 5, .p pv5 [pv2,pv3,pv47,pv347], .c 3, .c 37, .c 103,
  .c 3, .c 7, .c 353, .c 3, .c 677, .c 5, .c 3, .c 431, .c 7, .c 3, .c 5, .c 809, .c 3, .c 43,
  .c 11, .c 3, .c 479, .p pv3 [pv2,pv3,pv37,pv71,pv149], .c 3, .c 47, .c 5,
]
private theorem h0286c21 : checkBlock 2348291 128 b0286c21 = true := by
  decide +kernel

private def b0286c22 : List Row := [
  .c 3, .c 7, .c 67, .c 3, .c 5, .c 829, .c 3, .c 61, .c 7, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv83,pv131], .c 3, .p pv2 [pv2,pv587143], .c 5, .c 3, .p pv2 [pv2,pv359,pv3271],
  .p pv17 [pv2,pv3,pv5,pv13,pv3011], .c 3, .c 5, .c 587, .c 3, .c 7, .c 13, .c 3,
  .p pv2 [pv2,pv587149], .c 11, .c 3, .c 41, .c 5, .c 3, .c 19, .c 127, .c 3, .c 5, .c 43, .c 3,
  .c 11, .c 29, .c 3, .p pv2 [pv2,pv7,pv167759], .c 73, .c 3, .c 7, .c 5, .c 3, .c 269, .c 211,
  .c 3, .c 5, .c 7, .c 3, .c 83, .c 31, .c 3, .c 401, .c 179, .c 3, .c 379, .c 5, .c 3, .c 17,
  .c 13, .c 3, .c 5, .c 1097, .c 3, .c 29, .c 61, .c 3, .c 11, .c 7, .c 3, .p pv2 [pv2,pv587173],
  .c 5, .c 3, .c 131, .p pv2 [pv2,pv3,pv5,pv7829], .c 3, .c 5, .p pv2 [pv2,pv3,pv391451], .c 3,
  .c 1049, .p pv5 [pv2,pv3,pv32621], .c 3, .c 7, .c 449, .c 3, .c 13, .c 5, .c 3,
  .p pv3 [pv2,pv137,pv2143], .c 7, .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv117437],
  .p pv3 [pv2,pv3,pv11,pv19,pv1873], .c 3, .p pv2 [pv2,pv31,pv43,pv881], .c 13, .c 3, .c 11, .c 5,
  .c 3, .c 7, .c 19, .c 3, .c 5, .c 41, .c 3, .c 17, .c 7, .c 3, .c 31,
  .p pv2 [pv2,pv3,pv47,pv8329], .c 3, .c 23, .c 5, .c 3, .c 43, .p pv19 [pv2,pv3,pv5,pv59,pv1327],
  .c 3, .c 5, .c 11, .c 3, .c 7,
]
private theorem h0286c22 : checkBlock 2348547 128 b0286c22 = true := by
  decide +kernel

private def b0286c23 : List Row := [
  .c 1409, .c 3, .p pv5 [pv2,pv23,pv51061], .p pv29 [pv2,pv3,pv7,pv11,pv31,pv41], .c 3,
  .p pv2 [pv2,pv103,pv5701], .c 5, .c 3, .c 11, .c 173, .c 3, .c 5, .c 13, .c 3, .c 197,
  .p pv5 [pv2,pv3,pv43,pv569], .c 3, .c 19, .c 17, .c 3, .c 7, .c 5, .c 3, .c 41,
  .p pv2 [pv2,pv3,pv5,pv7,pv2237], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv117443], .c 11, .c 3,
  .c 1297, .c 557, .c 3, .c 17, .c 5, .c 3, .c 13, .c 821, .c 3, .c 5, .c 409, .c 3,
  .p pv2 [pv2,pv5,pv17,pv41,pv337], .c 71, .c 3, .p pv3 [pv2,pv11,pv6673], .c 7, .c 3,
  .p pv5 [pv2,pv1174451], .c 5, .c 3, .p pv3 [pv2,pv37,pv59,pv269], .p pv11 [pv2,pv3,pv5,pv26099],
  .c 3, .c 5, .c 709, .c 3, .c 23, .c 1091, .c 3, .c 7, .c 11, .c 3, .c 1499, .c 5, .c 3, .c 383,
  .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv43499], .c 3, .c 11, .c 67, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv17,pv23029], .c 3, .c 31, .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .c 89, .c 3,
  .c 293, .c 7, .c 3, .p pv2 [pv2,pv79,pv14867], .c 19, .c 3, .c 163, .c 5, .c 3,
  .p pv7 [pv2,pv1174499], .p pv11 [pv2,pv3,pv5,pv29], .c 3, .c 5, .c 1087, .c 3, .c 7, .c 23,
  .c 3, .c 11, .c 37, .c 3, .p pv5 [pv2,pv13,pv167,pv541], .c 5, .c 3, .c 29,
  .p pv23 [pv2,pv3,pv5,pv78301], .c 3, .c 5, .c 857, .c 3, .p pv3 [pv2,pv5,pv29363], .c 17, .c 3,
  .c 43, .c 61, .c 3, .c 7, .c 5, .c 3,
]
private theorem h0286c23 : checkBlock 2348803 128 b0286c23 = true := by
  decide +kernel

private def b0286c24 : List Row := [
  .c 23, .c 11, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv234907], .c 1187, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv107,pv3659], .c 3, .c 11, .c 5, .c 3, .c 439,
  .p pv17 [pv2,pv3,pv5,pv43,pv607], .c 3, .c 5, .p pv17 [pv2,pv3,pv97879], .c 3,
  .p pv2 [pv2,pv5,pv13,pv139], .c 19, .c 3, .c 47, .c 7, .c 3, .c 13, .c 5, .c 3, .c 53, .c 103,
  .c 3, .c 5, .c 11, .c 3, .c 239, .c 43, .c 3, .c 7, .c 13, .c 3, .p pv5 [pv2,pv1174571], .c 5,
  .c 3, .c 11, .c 7, .c 3, .c 5, .c 113, .c 3, .p pv3 [pv2,pv5,pv11,pv19,pv281],
  .p pv2 [pv2,pv3,pv17,pv853], .c 3, .c 37, .c 1451, .c 3, .c 1283, .c 5, .c 3, .c 7,
  .p pv19 [pv2,pv3,pv5,pv31,pv421], .c 3, .c 5, .c 1471, .c 3, .c 13, .c 7, .c 3, .c 23, .c 181,
  .c 3, .c 29, .c 5, .c 3, .p pv3 [pv2,pv293651], .c 31, .c 3, .c 5, .c 13, .c 3, .c 7, .c 79,
  .c 3, .c 337, .c 443, .c 3, .p pv3 [pv2,pv29,pv61,pv83], .c 5, .c 3, .c 139, .c 37, .c 3, .c 5,
  .c 17, .c 3, .p pv2 [pv2,pv5,pv9397], .p pv5 [pv2,pv3,pv65257], .c 3, .c 647, .c 11, .c 3, .c 7,
  .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv7,pv11,pv113], .c 3, .c 5, .c 7, .c 3, .c 11, .c 149,
  .c 3, .c 317, .c 23, .c 3, .c 19, .c 5, .c 3, .c 271, .p pv13 [pv2,pv3,pv5,pv41,pv191], .c 3,
  .c 5, .p pv2 [pv2,pv3,pv130517], .c 3, .c 229, .p pv5 [pv2,pv3,pv7,pv19,pv23],
]
private theorem h0286c24 : checkBlock 2349059 128 b0286c24 = true := by
  decide +kernel

private def b0286c25 : List Row := [
  .c 3, .p pv2 [pv2,pv523,pv1123], .c 7, .c 3, .p pv2 [pv2,pv383,pv3067], .c 5, .c 3,
  .p pv3 [pv2,pv146833], .c 19, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv809], .c 3, .c 41,
  .p pv3 [pv2,pv3,pv47,pv2777], .c 3, .c 7, .c 17, .c 3, .p pv3 [pv2,pv37,pv7937], .c 5, .c 3,
  .c 73, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv17,pv31,pv743], .c 3, .p pv2 [pv2,pv5,pv239,pv983],
  .c 13, .c 3, .c 29, .c 263, .c 3, .c 17, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 31, .c 3,
  .c 569, .c 7, .c 3, .c 19, .c 151, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv1174709], .c 379,
  .c 3, .c 5, .c 23, .c 3, .c 7, .p pv5 [pv2,pv3,pv73,pv149], .c 3, .c 53, .c 59, .c 3, .c 673,
  .c 5, .c 3, .c 1129, .c 13, .c 3, .c 5, .c 11, .c 3, .c 71, .c 37, .c 3, .c 811, .c 911, .c 3,
  .c 7, .c 5, .c 3, .c 11, .c 83, .c 3, .c 5, .c 7, .c 3, .c 191, .c 29, .c 3,
  .p pv3 [pv2,pv23,pv113], .p pv2 [pv2,pv3,pv59,pv6637], .c 3, .c 13, .c 5, .c 3, .c 241, .c 89,
  .c 3, .c 5, .c 139, .c 3, .c 19, .c 11, .c 3, .c 373, .c 7, .c 3, .c 103, .c 5, .c 3, .c 79,
  .p pv2 [pv2,pv3,pv5,pv19,pv229], .c 3, .c 5, .p pv2 [pv2,pv3,pv41,pv9551], .c 3, .c 29, .c 17,
  .c 3, .c 7, .c 19, .c 3, .c 43, .c 5, .c 3, .p pv3 [pv2,pv13,pv353],
]
private theorem h0286c25 : checkBlock 2349315 128 b0286c25 = true := by
  decide +kernel

private def b0286c26 : List Row := [
  .c 7, .c 3, .c 5, .c 47, .c 3, .c 13, .c 31, .c 3, .c 17, .c 11, .c 3, .c 199, .c 5, .c 3, .c 7,
  .c 421, .c 3, .c 5, .c 13, .c 3, .c 11, .c 7, .c 3, .c 449, .c 197, .c 3, .c 67, .c 5, .c 3,
  .c 613, .c 97, .c 3, .c 5, .p pv2 [pv2,pv3,pv103,pv1901], .c 3, .c 7,
  .p pv3 [pv2,pv3,pv263,pv1489], .c 3, .c 83, .c 43, .c 3, .p pv2 [pv2,pv587413], .c 5, .c 3,
  .c 13, .c 991, .c 3, .c 5, .c 29, .c 3, .c 47, .c 19, .c 3, .c 11, .p pv3 [pv2,pv3,pv391613],
  .c 3, .c 7, .c 5, .c 3, .c 17, .c 313, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv23497], .c 23,
  .c 3, .c 31, .p pv2 [pv2,pv3,pv195809], .c 3, .c 109, .c 5, .c 3, .p pv7 [pv2,pv7,pv47,pv3571],
  .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv23,pv17027], .c 3, .p pv2 [pv2,pv5,pv19,pv83,pv149],
  .c 179, .c 3, .c 13, .c 7, .c 3, .c 11, .c 5, .c 3, .c 19, .c 41, .c 3, .c 5, .c 17, .c 3,
  .c 587, .c 13, .c 3, .c 7, .c 31, .c 3, .p pv2 [pv2,pv23,pv25541], .c 5, .c 3,
  .p pv2 [pv2,pv43,pv89,pv307], .c 7, .c 3, .c 5, .c 11, .c 3, .c 17, .c 59, .c 3, .c 73,
  .p pv11 [pv2,pv3,pv11,pv35603], .c 3, .p pv2 [pv2,pv7,pv13,pv12911], .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv967], .c 3, .c 5, .c 349, .c 3, .c 43, .c 7, .c 3,
]
private theorem h0286c26 : checkBlock 2349571 128 b0286c26 = true := by
  decide +kernel

private def b0286c27 : List Row := [
  .c 107, .p pv2 [pv2,pv3,pv13,pv5021], .c 3, .c 37, .c 5, .c 3, .c 523, .c 13, .c 3, .c 5,
  .c 1289, .c 3, .c 7, .c 11, .c 3, .c 167, .c 17, .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv587467],
  .p pv3 [pv2,pv3,pv5,pv29,pv37,pv73], .c 3, .c 5, .c 599, .c 3, .c 127, .c 919, .c 3, .c 23,
  .p pv7 [pv2,pv3,pv12239], .c 3, .c 7, .c 5, .c 3, .c 29, .c 19, .c 3, .c 5, .c 7, .c 3, .c 59,
  .p pv5 [pv2,pv3,pv179,pv547], .c 3, .p pv2 [pv2,pv311,pv1889], .c 11, .c 3, .c 181, .c 5, .c 3,
  .c 997, .c 109, .c 3, .c 5, .p pv13 [pv2,pv3,pv16319], .c 3, .c 11, .c 73, .c 3,
  .p pv2 [pv2,pv1174973], .c 7, .c 3, .c 47, .c 5, .c 3, .p pv19 [pv2,pv13,pv19,pv67,pv71], .c 17,
  .c 3, .c 5, .c 53, .c 3, .c 13, .p pv7 [pv2,pv3,pv7253], .c 3, .c 7, .c 23, .c 3, .c 557, .c 5,
  .c 3, .c 1523, .c 7, .c 3, .c 5, .c 13, .c 3, .p pv7 [pv2,pv5,pv47], .c 281, .c 3, .c 11,
  .c 131, .c 3, .c 79, .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv53,pv739], .c 3, .c 5, .c 1217,
  .c 3, .p pv19 [pv2,pv5,pv235003], .c 7, .c 3, .c 907, .c 839, .c 3, .p pv2 [pv2,pv1175021],
  .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv97919], .c 3, .c 7, .c 17, .c 3,
  .p pv2 [pv2,pv449,pv2617], .p pv11 [pv2,pv3,pv7,pv101,pv277], .c 3, .c 11, .c 5, .c 3, .c 31,
  .p pv13 [pv2,pv3,pv5,pv17],
]
private theorem h0286c27 : checkBlock 2349827 128 b0286c27 = true := by
  decide +kernel

private def b0286c28 : List Row := [
  .c 3, .c 5, .c 239, .c 3, .c 19, .p pv2 [pv2,pv3,pv37,pv67,pv79], .c 3, .c 17,
  .p pv3 [pv2,pv3,pv137,pv953], .c 3, .c 7, .c 5, .c 3, .c 743,
  .p pv7 [pv2,pv3,pv5,pv7,pv19,pv31], .c 3, .c 5, .c 7, .c 3, .c 577,
  .p pv2 [pv2,pv3,pv43,pv9109], .c 3, .c 13, .c 19, .c 3, .c 157, .c 5, .c 3, .c 11, .c 31, .c 3,
  .c 5, .c 59, .c 3, .c 103, .c 13, .c 3, .p pv2 [pv2,pv587539], .c 7, .c 3, .c 23, .c 5, .c 3,
  .c 101, .c 71, .c 3, .c 5, .c 149, .c 3, .p pv2 [pv2,pv5,pv7,pv16787], .c 11, .c 3, .c 7, .c 29,
  .c 3, .p pv5 [pv2,pv13,pv11299], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv59,pv2213], .c 3, .p pv2 [pv2,pv5,pv197,pv1193], .c 97, .c 3,
  .p pv3 [pv2,pv11,pv17,pv1571], .p pv2 [pv2,pv3,pv13,pv29,pv1039], .c 3, .c 89, .c 5, .c 3, .c 7,
  .c 13, .c 3, .c 5, .p pv13 [pv2,pv3,pv7,pv571], .c 3, .p pv3 [pv2,pv5,pv37,pv397], .c 7, .c 3,
  .c 29, .c 11, .c 3, .c 269, .c 5, .c 3, .p pv2 [pv2,pv109,pv10781], .c 401, .c 3, .c 5, .c 17,
  .c 3, .c 7, .c 373, .c 3, .c 37, .p pv7 [pv2,pv3,pv7,pv23,pv811], .c 3, .c 13, .c 5, .c 3,
  .p pv3 [pv2,pv146893], .p pv17 [pv2,pv3,pv5,pv157,pv499], .c 3, .c 5, .c 163, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv391717], .c 3, .p pv2 [pv2,pv7,pv167879], .c 13, .c 3, .c 7, .c 5, .c 3,
  .c 19, .p pv11 [pv2,pv3,pv5,pv7,pv1399], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv61,pv3853],
  .p pv2 [pv2,pv3,pv65287], .c 3, .c 11,
]
private theorem h0286c28 : checkBlock 2350083 128 b0286c28 = true := by
  decide +kernel

private def b0286c29 : List Row := [
  .p pv2 [pv2,pv3,pv19,pv53,pv389], .c 3, .c 619, .c 5, .c 3, .p pv2 [pv2,pv7,pv11,pv13,pv587],
  .c 37, .c 3, .c 5, .c 19, .c 3, .c 13, .c 29, .c 3, .c 109, .c 7, .c 3, .c 359, .c 5, .c 3,
  .p pv2 [pv2,pv173,pv6793], .c 11, .c 3, .c 5, .c 13, .c 3, .c 53, .c 23, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv391733], .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv79,pv3719], .c 7, .c 3, .c 5,
  .c 491, .c 3, .c 29, .c 43, .c 3, .c 67, .p pv2 [pv2,pv3,pv195869], .c 3, .c 19, .c 5, .c 3,
  .c 7, .p pv13 [pv2,pv3,pv5,pv6529], .c 3, .c 5, .c 11, .c 3, .c 31, .c 7, .c 3,
  .p pv3 [pv2,pv229,pv1283], .c 547, .c 3, .p pv5 [pv2,pv23,pv37,pv1381], .c 5, .c 3, .c 11,
  .c 17, .c 3, .c 5, .c 83, .c 3, .c 7, .p pv3 [pv2,pv3,pv31,pv12637], .c 3, .c 79, .c 41, .c 3,
  .c 1103, .c 5, .c 3, .c 37, .c 59, .c 3, .c 5, .p pv2 [pv2,pv3,pv391751], .c 3, .c 601, .c 11,
  .c 3, .c 13, .c 503, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv19,pv1933], .c 23, .c 3, .c 5, .c 7,
  .c 3, .p pv2 [pv2,pv5,pv211,pv557], .c 13, .c 3, .c 19, .p pv7 [pv2,pv3,pv65293], .c 3, .c 1259,
  .c 5, .c 3, .p pv7 [pv2,pv7,pv379,pv443], .c 67, .c 3, .c 5, .p pv3 [pv2,pv3,pv19,pv29,pv79],
  .c 3, .c 41, .c 17, .c 3, .c 23, .c 7, .c 3, .p pv5 [pv2,pv13,pv90407], .c 5, .c 3,
  .p pv2 [pv2,pv199,pv2953], .p pv19 [pv2,pv3,pv5,pv11,pv17,pv419], .c 3,
]
private theorem h0286c29 : checkBlock 2350339 128 b0286c29 = true := by
  decide +kernel

private def b0286c30 : List Row := [
  .c 5, .c 71, .c 3, .c 11, .c 53, .c 3, .c 7, .p pv11 [pv2,pv3,pv13,pv3767], .c 3,
  .p pv2 [pv2,pv11,pv41,pv1303], .c 5, .c 3, .c 59, .c 7, .c 3, .c 5, .c 353, .c 3,
  .p pv23 [pv2,pv5,pv313,pv751], .p pv5 [pv2,pv3,pv97943], .c 3, .c 31, .c 461, .c 3, .c 83, .c 5,
  .c 3, .c 7, .c 463, .c 3, .c 5, .p pv23 [pv2,pv3,pv7,pv11,pv53], .c 3, .c 19, .c 7, .c 3, .c 11,
  .c 23, .c 3, .c 13, .c 5, .c 3, .p pv7 [pv2,pv11,pv59,pv1811], .c 43, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv13,pv30137], .c 3, .c 7, .c 773, .c 3, .p pv3 [pv2,pv61,pv4817], .c 13, .c 3,
  .p pv5 [pv2,pv1175351], .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv195893], .c 3,
  .c 37, .p pv2 [pv2,pv3,pv11,pv35617], .c 3, .c 389, .c 761, .c 3, .c 7, .c 5, .c 3, .c 71,
  .p pv11 [pv2,pv3,pv5,pv7,pv29,pv193], .c 3, .c 5, .c 7, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv47,pv521], .c 3, .c 61, .c 739, .c 3, .p pv2 [pv2,pv53,pv67,pv331], .c 5,
  .c 3, .c 29, .p pv2 [pv2,pv3,pv5,pv127,pv617], .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv117539], .c 137, .c 3, .c 199, .c 7, .c 3, .p pv3 [pv2,pv31,pv9479], .c 5,
  .c 3, .c 11, .c 197, .c 3, .c 5, .c 23, .c 3, .c 17, .c 19, .c 3, .c 7, .c 73, .c 3, .c 31,
  .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv21767], .c 3, .p pv3 [pv2,pv5,pv58771],
  .c 11, .c 3, .p pv5 [pv2,pv47,pv89,pv281], .c 311,
]
private theorem h0286c30 : checkBlock 2350595 128 b0286c30 = true := by
  decide +kernel

private def b0286c31 : List Row := [
  .c 3, .c 23, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv39181], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv223,pv251], .c 3, .c 1097, .c 7, .c 3, .p pv2 [pv2,pv11,pv23,pv101],
  .c 17, .c 3, .p pv2 [pv2,pv79,pv14879], .c 5, .c 3, .c 19, .p pv11 [pv2,pv3,pv5,pv8707], .c 3,
  .c 5, .c 107, .c 3, .c 7, .p pv5 [pv2,pv3,pv391817], .c 3, .c 13, .c 11, .c 3, .c 17, .c 5,
  .c 3, .c 151, .c 53, .c 3, .c 5, .c 19, .c 3, .c 11, .c 13, .c 3, .c 379, .c 43, .c 3, .c 7,
  .c 5, .c 3, .c 163, .p pv7 [pv2,pv3,pv5,pv7,pv2239], .c 3, .c 5, .c 7, .c 3, .c 79, .c 67, .c 3,
  .c 1153, .p pv7 [pv2,pv3,pv23,pv4259], .c 3, .c 59, .c 5, .c 3, .p pv2 [pv2,pv7,pv31,pv5417],
  .c 17, .c 3, .c 5, .c 47, .c 3, .c 23, .p pv11 [pv2,pv3,pv7,pv6997], .c 3, .c 11, .c 7, .c 3,
  .c 19, .c 5, .c 3, .c 31, .c 13, .c 3, .c 5, .c 37, .c 3, .c 109, .c 71, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv195919], .c 3, .p pv3 [pv2,pv17,pv59,pv293], .c 5, .c 3, .c 227, .c 7, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv139,pv2819], .c 3, .c 953, .p pv31 [pv2,pv3,pv11,pv1979], .c 3, .c 131,
  .c 29, .c 3, .c 11, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5, .c 1229, .c 3, .c 47, .c 7, .c 3,
  .c 1051, .c 13, .c 3, .c 331, .c 5, .c 3, .p pv2 [pv2,pv19,pv61871],
  .p pv2 [pv2,pv3,pv5,pv17,pv461], .c 3, .c 5,
]
private theorem h0286c31 : checkBlock 2350851 128 b0286c31 = true := by
  decide +kernel

def rows0286 : List Row :=
  b0286c00 ++ b0286c01 ++ b0286c02 ++ b0286c03 ++ b0286c04 ++ b0286c05 ++ b0286c06 ++ b0286c07 ++
  b0286c08 ++ b0286c09 ++ b0286c10 ++ b0286c11 ++ b0286c12 ++ b0286c13 ++ b0286c14 ++ b0286c15 ++
  b0286c16 ++ b0286c17 ++ b0286c18 ++ b0286c19 ++ b0286c20 ++ b0286c21 ++ b0286c22 ++ b0286c23 ++
  b0286c24 ++ b0286c25 ++ b0286c26 ++ b0286c27 ++ b0286c28 ++ b0286c29 ++ b0286c30 ++ b0286c31

theorem checked0286 : checkBlock 2342915 4096 rows0286 = true :=
  checkBlock_append h0286c00 (
    checkBlock_append h0286c01 (
    checkBlock_append h0286c02 (
    checkBlock_append h0286c03 (
    checkBlock_append h0286c04 (
    checkBlock_append h0286c05 (
    checkBlock_append h0286c06 (
    checkBlock_append h0286c07 (
    checkBlock_append h0286c08 (
    checkBlock_append h0286c09 (
    checkBlock_append h0286c10 (
    checkBlock_append h0286c11 (
    checkBlock_append h0286c12 (
    checkBlock_append h0286c13 (
    checkBlock_append h0286c14 (
    checkBlock_append h0286c15 (
    checkBlock_append h0286c16 (
    checkBlock_append h0286c17 (
    checkBlock_append h0286c18 (
    checkBlock_append h0286c19 (
    checkBlock_append h0286c20 (
    checkBlock_append h0286c21 (
    checkBlock_append h0286c22 (
    checkBlock_append h0286c23 (
    checkBlock_append h0286c24 (
    checkBlock_append h0286c25 (
    checkBlock_append h0286c26 (
    checkBlock_append h0286c27 (
    checkBlock_append h0286c28 (
    checkBlock_append h0286c29 (
    checkBlock_append h0286c30 (
    h0286c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
