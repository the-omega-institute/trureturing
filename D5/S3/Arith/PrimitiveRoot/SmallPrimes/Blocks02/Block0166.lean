/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks02/Block0166
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks02/Block0166.checked0166
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table021
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table029
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table037
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table049
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table071
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table124

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0166c00 : List Row := [
  .c 5, .c 31, .c 3, .c 17, .c 7, .c 3, .c 19, .c 1031, .c 3, .c 347, .c 5, .c 3, .c 67,
  .p pv2 [pv2,pv3,pv5,pv1511], .c 3, .c 5, .c 761, .c 3, .c 7, .p pv5 [pv2,pv3,pv56663], .c 3,
  .c 13, .c 11, .c 3, .c 149, .c 5, .c 3, .c 41, .c 953, .c 3, .c 5, .p pv7 [pv2,pv3,pv787], .c 3,
  .c 11, .c 13, .c 3, .p pv2 [pv2,pv7,pv13877], .c 17, .c 3, .c 7, .c 5, .c 3,
  .p pv17 [pv2,pv373,pv1823], .c 43, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv31,pv41,pv107],
  .c 263, .c 3, .p pv3 [pv2,pv139,pv1223], .p pv2 [pv2,pv3,pv226663], .c 3, .c 17, .c 5, .c 3,
  .c 577, .p pv23 [pv2,pv3,pv5,pv23,pv73], .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv10303], .c 3, .c 19,
  .c 311, .c 3, .c 11, .c 7, .c 3, .c 23, .c 5, .c 3, .c 839, .c 13, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv75557], .c 3, .c 229, .c 53, .c 3, .c 7, .c 19, .c 3, .c 127, .c 5, .c 3,
  .p pv3 [pv2,pv167,pv509], .c 7, .c 3, .c 5, .c 151, .c 3, .c 751, .c 31, .c 3,
  .p pv2 [pv2,pv101,pv6733], .p pv2 [pv2,pv3,pv17,pv59,pv113], .c 3, .c 11, .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv1889], .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv13,pv47,pv53], .c 3, .c 157,
  .c 7, .c 3, .p pv3 [pv2,pv19,pv2237], .c 13, .c 3, .p pv5 [pv2,pv17,pv109,pv367], .c 5, .c 3,
  .c 353, .c 191, .c 3, .c 5, .c 11, .c 3, .c 7, .c 911, .c 3, .c 59, .c 29,
]
private theorem h0166c00 : checkBlock 1359875 128 b0166c00 = true := by
  decide +kernel

private def b0166c01 : List Row := [
  .c 3, .c 43, .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv22669], .c 3, .c 5, .c 71, .c 3, .c 13,
  .c 17, .c 3, .c 37, .p pv3 [pv2,pv3,pv29,pv7817], .c 3, .c 7, .c 5, .c 3, .c 251,
  .p pv7 [pv2,pv3,pv5,pv7,pv17,pv127], .c 3, .c 5, .c 7, .c 3, .c 113, .c 11, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv37783], .c 3, .p pv3 [pv2,pv53,pv401], .c 5, .c 3, .c 653,
  .p pv7 [pv2,pv3,pv5,pv2267], .c 3, .c 5, .p pv3 [pv2,pv3,pv25189], .c 3, .c 109,
  .p pv2 [pv2,pv3,pv7,pv16193], .c 3, .c 727, .c 7, .c 3, .p pv5 [pv2,pv79,pv8609], .c 5, .c 3,
  .c 13, .c 37, .c 3, .c 5, .p pv13 [pv2,pv3,pv263,pv431], .c 3, .p pv17 [pv2,pv5,pv7,pv347],
  .c 23, .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv340063], .c 5, .c 3, .p pv2 [pv2,pv680129], .c 7,
  .c 3, .c 5, .c 19, .c 3, .c 11, .c 137, .c 3, .p pv3 [pv2,pv89,pv3821],
  .p pv3 [pv2,pv3,pv75571], .c 3, .p pv5 [pv2,pv7,pv11,pv73], .c 5, .c 3, .c 7, .c 107, .c 3,
  .c 5, .c 127, .c 3, .c 67, .c 7, .c 3, .c 13, .p pv7 [pv2,pv3,pv113359], .c 3,
  .p pv3 [pv2,pv23,pv7393], .c 5, .c 3, .p pv7 [pv2,pv680159], .c 47, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv20611], .c 3, .c 7, .c 13, .c 3, .c 11, .c 41, .c 3, .c 19, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv43,pv719], .c 53, .c 3, .c 5, .c 17, .c 3, .c 29, .c 59, .c 3,
  .p pv5 [pv2,pv7,pv97169], .c 101, .c 3, .c 7, .c 5, .c 3, .c 37, .c 11, .c 3, .c 5,
]
private theorem h0166c01 : checkBlock 1360131 128 b0166c01 = true := by
  decide +kernel

private def b0166c02 : List Row := [
  .c 7, .c 3, .c 17, .c 139, .c 3, .c 821, .c 293, .c 3, .c 11, .c 5, .c 3,
  .p pv11 [pv2,pv7,pv17,pv1429], .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv37,pv383], .c 3, .c 41,
  .p pv3 [pv2,pv3,pv7,pv59,pv61], .c 3, .c 23, .c 7, .c 3, .c 743, .c 5, .c 3,
  .p pv11 [pv2,pv19,pv35801], .p pv23 [pv2,pv3,pv5,pv3779], .c 3, .c 5, .c 11, .c 3,
  .p pv11 [pv2,pv5,pv7,pv13,pv23], .c 37, .c 3, .c 7, .c 17, .c 3, .c 13, .c 5, .c 3, .c 11, .c 7,
  .c 3, .c 5, .c 29, .c 3, .c 59, .c 61, .c 3, .c 233, .c 13, .c 3, .c 17, .c 5, .c 3, .c 7,
  .c 73, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv29,pv1117], .c 3, .p pv11 [pv2,pv5,pv17,pv53,pv151],
  .c 7, .c 3, .p pv2 [pv2,pv340129], .c 23, .c 3, .c 223, .c 5, .c 3,
  .p pv3 [pv2,pv13,pv31,pv211], .p pv2 [pv2,pv3,pv5,pv5039], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv83,pv683], .c 3, .c 7, .c 89, .c 3, .c 137, .c 167, .c 3, .c 1049, .c 5, .c 3,
  .c 31, .c 17, .c 3, .c 5, .c 13, .c 3, .c 19, .c 71, .c 3, .c 181, .c 11, .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv23,pv643], .p pv3 [pv2,pv3,pv5,pv7,pv11,pv19,pv31], .c 3, .c 5, .c 7, .c 3,
  .c 11, .c 47, .c 3, .p pv5 [pv2,pv13,pv43,pv1217], .c 19, .c 3, .p pv3 [pv2,pv11,pv17,pv107],
  .c 5, .c 3, .c 13, .c 31, .c 3, .c 5, .c 239, .c 3, .p pv47 [pv2,pv5,pv103,pv1321], .c 113,
  .c 3, .p pv2 [pv2,pv67,pv5077], .c 7, .c 3,
]
private theorem h0166c02 : checkBlock 1360387 128 b0166c02 = true := by
  decide +kernel

private def b0166c03 : List Row := [
  .c 991, .c 5, .c 3, .c 43, .c 29, .c 3, .c 5, .c 23, .c 3, .c 151, .c 17, .c 3, .c 7, .c 53,
  .c 3, .p pv3 [pv2,pv101,pv421], .c 5, .c 3, .c 197, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv241,pv941], .c 3, .c 271, .c 571, .c 3, .c 13, .p pv7 [pv2,pv3,pv226783],
  .c 3, .c 23, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 59, .c 3, .c 89, .c 7, .c 3, .c 61,
  .p pv7 [pv2,pv3,pv18899], .c 3, .c 11, .c 5, .c 3, .c 211, .c 331, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv113,pv223], .c 3, .c 7, .p pv17 [pv2,pv3,pv28349], .c 3, .c 463,
  .p pv7 [pv2,pv3,pv7,pv179,pv181], .c 3, .p pv2 [pv2,pv13,pv199,pv263], .c 5, .c 3,
  .p pv3 [pv2,pv10631], .c 563, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv19,pv3581],
  .p pv5 [pv2,pv3,pv17,pv4447], .c 3, .p pv2 [pv2,pv7,pv37,pv71], .p pv7 [pv2,pv3,pv11,pv13,pv61],
  .c 3, .c 7, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv11,pv89,pv139],
  .c 97, .c 3, .c 149, .p pv2 [pv2,pv3,pv19,pv23,pv173], .c 3, .c 37, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv53,pv131], .c 41, .c 3, .c 5, .c 19, .c 3, .c 23, .c 11, .c 3,
  .p pv5 [pv2,pv523,pv1301], .c 7, .c 3, .c 13, .c 5, .c 3, .c 113,
  .p pv2 [pv2,pv3,pv5,pv37,pv613], .c 3, .c 5, .c 17, .c 3, .c 269, .p pv5 [pv2,pv3,pv41,pv461],
  .c 3, .c 7, .c 13, .c 3, .c 29, .c 5, .c 3, .p pv3 [pv2,pv170111], .c 7, .c 3, .c 5, .c 37,
]
private theorem h0166c03 : checkBlock 1360643 128 b0166c03 = true := by
  decide +kernel

private def b0166c04 : List Row := [
  .c 3, .c 17, .p pv3 [pv2,pv3,pv226817], .c 3, .c 43, .c 11, .c 3, .c 19, .c 5, .c 3, .c 7,
  .p pv23 [pv2,pv3,pv5,pv11,pv1031], .c 3, .c 5, .c 241, .c 3, .c 11, .c 7, .c 3, .c 179, .c 73,
  .c 3, .p pv5 [pv2,pv11,pv61861], .c 5, .c 3, .c 139, .c 19, .c 3, .c 5, .c 13, .c 3, .c 7,
  .c 151, .c 3, .p pv5 [pv2,pv149,pv4567], .c 17, .c 3, .p pv2 [pv2,pv113,pv3011], .c 5, .c 3,
  .c 23, .p pv2 [pv2,pv3,pv5,pv7561], .c 3, .c 5, .c 53, .c 3, .c 173, .c 31, .c 3, .c 11, .c 29,
  .c 3, .c 7, .c 5, .c 3, .c 13, .p pv11 [pv2,pv3,pv5,pv7,pv6481], .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv17,pv4003], .p pv3 [pv2,pv3,pv13,pv17449], .c 3, .c 19,
  .p pv2 [pv2,pv3,pv29,pv3911], .c 3, .c 157, .c 5, .c 3, .c 919, .c 11, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv19,pv11939], .c 3, .p pv17 [pv2,pv5,pv163,pv167],
  .p pv2 [pv2,pv3,pv7,pv11,pv491], .c 3, .c 29, .c 7, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv340267], .c 17, .c 3, .c 5, .c 41, .c 3, .p pv3 [pv2,pv5,pv7,pv4861], .c 109,
  .c 3, .c 7, .p pv29 [pv2,pv3,pv17,pv139], .c 3, .c 53, .c 5, .c 3, .p pv2 [pv2,pv431,pv1579],
  .c 7, .c 3, .c 5, .c 11, .c 3, .c 389, .c 13, .c 3, .c 23, .c 37, .c 3,
  .p pv2 [pv2,pv7,pv17,pv19,pv43], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv59,pv769], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv4051], .c 3, .c 19, .c 7, .c 3, .c 107, .p pv2 [pv2,pv3,pv31,pv3659],
  .c 3, .p pv3 [pv2,pv13,pv409],
]
private theorem h0166c04 : checkBlock 1360899 128 b0166c04 = true := by
  decide +kernel

private def b0166c05 : List Row := [
  .c 5, .c 3, .c 41, .c 211, .c 3, .c 5, .c 47, .c 3, .c 7, .c 11, .c 3, .c 101, .c 19, .c 3,
  .p pv5 [pv2,pv383,pv1777], .c 5, .c 3, .c 59, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv37811], .c 3,
  .c 97, .c 367, .c 3, .c 17, .c 23, .c 3, .c 7, .c 5, .c 3, .c 683, .c 131, .c 3, .c 5, .c 7,
  .c 3, .c 29, .c 271, .c 3, .c 313, .c 11, .c 3, .c 13, .c 5, .c 3, .c 79, .c 43, .c 3, .c 5,
  .c 191, .c 3, .c 11, .c 1061, .c 3, .c 37, .c 7, .c 3, .p pv3 [pv2,pv11,pv31,pv499], .c 5, .c 3,
  .p pv19 [pv2,pv23,pv101,pv293], .c 347, .c 3, .c 5, .p pv3 [pv2,pv3,pv2801], .c 3,
  .p pv19 [pv2,pv5,pv7,pv19447], .c 19, .c 3, .c 7, .p pv3 [pv2,pv3,pv97,pv2339], .c 3, .c 31,
  .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv11,pv10313], .c 3, .c 13, .c 41, .c 3,
  .c 11, .c 257, .c 3, .c 461, .c 5, .c 3, .c 7, .c 37, .c 3, .c 5, .c 13, .c 3, .c 103, .c 7,
  .c 3, .p pv2 [pv2,pv340339], .c 199, .c 3, .p pv2 [pv2,pv680681], .c 5, .c 3, .c 19, .c 11,
  .c 3, .c 5, .c 17, .c 3, .c 7, .p pv3 [pv2,pv3,pv11,pv20627], .c 3, .p pv2 [pv2,pv13,pv52361],
  .p pv2 [pv2,pv3,pv7,pv19,pv853], .c 3, .c 11, .c 5, .c 3, .c 13, .p pv11 [pv2,pv3,pv5,pv2269],
  .c 3, .c 5, .c 19, .c 3,
]
private theorem h0166c05 : checkBlock 1361155 128 b0166c05 = true := by
  decide +kernel

private def b0166c06 : List Row := [
  .c 17, .c 149, .c 3, .p pv11 [pv2,pv7,pv23,pv151], .c 233, .c 3, .c 7, .c 5, .c 3, .c 761,
  .p pv3 [pv2,pv3,pv5,pv7,pv2161], .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv67,pv127],
  .p pv3 [pv2,pv3,pv226907], .c 3, .c 677, .c 47, .c 3, .p pv2 [pv2,pv37,pv9199], .c 5, .c 3,
  .c 11, .c 937, .c 3, .c 5, .c 197, .c 3, .p pv11 [pv2,pv5,pv11,pv12377], .c 613, .c 3, .c 13,
  .c 7, .c 3, .c 19, .c 5, .c 3, .c 31, .p pv17 [pv2,pv3,pv5,pv13,pv3491], .c 3, .c 5,
  .p pv19 [pv2,pv3,pv17,pv47,pv71], .c 3, .c 607, .c 11, .c 3, .c 7, .c 43, .c 3, .c 17, .c 5,
  .c 3, .c 109, .c 7, .c 3, .c 5, .c 599, .c 3, .c 23, .p pv5 [pv2,pv3,pv83,pv1367], .c 3, .c 113,
  .c 163, .c 3, .c 47, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5, .c 103, .c 3, .c 409, .c 7, .c 3,
  .c 71, .c 11, .c 3, .p pv2 [pv2,pv340393], .c 5, .c 3, .c 29, .c 13, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv257,pv883], .c 3, .c 7, .p pv5 [pv2,pv3,pv18911], .c 3, .c 19,
  .p pv7 [pv2,pv3,pv7,pv17,pv1907], .c 3, .p pv2 [pv2,pv11,pv59,pv1049], .c 5, .c 3,
  .p pv3 [pv2,pv29,pv5869], .c 89, .c 3, .c 5, .c 569, .c 3, .c 503, .c 23, .c 3, .c 941,
  .p pv2 [pv2,pv3,pv109,pv347], .c 3, .c 7, .c 5, .c 3, .c 191, .c 67, .c 3, .c 5, .c 7, .c 3,
  .c 41, .c 179, .c 3, .c 11, .c 13, .c 3, .c 181, .c 5,
]
private theorem h0166c06 : checkBlock 1361411 128 b0166c06 = true := by
  decide +kernel

private def b0166c07 : List Row := [
  .c 3, .c 23, .c 727, .c 3, .c 5, .p pv2 [pv2,pv3,pv53,pv2141], .c 3, .c 43, .c 17, .c 3, .c 359,
  .c 7, .c 3, .c 1153, .c 5, .c 3, .p pv2 [pv2,pv13,pv83,pv631], .c 11, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv31,pv7321], .c 3, .c 13, .p pv13 [pv2,pv3,pv11,pv2579], .c 3, .c 7, .c 617,
  .c 3, .c 11, .c 5, .c 3, .c 53, .c 7, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv68087],
  .p pv5 [pv2,pv3,pv73,pv3109], .c 3, .c 379, .c 19, .c 3, .c 29, .c 5, .c 3, .c 7, .c 23, .c 3,
  .c 5, .c 11, .c 3, .c 499, .c 7, .c 3, .p pv3 [pv2,pv13,pv6547], .c 59, .c 3, .c 97, .c 5, .c 3,
  .c 11, .p pv7 [pv2,pv3,pv5,pv15131], .c 3, .c 5, .c 479, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv13,pv17,pv79], .c 3, .c 23, .p pv17 [pv2,pv3,pv7,pv193], .c 3,
  .p pv2 [pv2,pv340453], .c 5, .c 3, .c 17, .c 127, .c 3, .c 5, .p pv2 [pv2,pv3,pv25219], .c 3,
  .p pv7 [pv2,pv5,pv23,pv31,pv191], .c 11, .c 3, .c 953, .p pv3 [pv2,pv3,pv59,pv3847], .c 3, .c 7,
  .c 5, .c 3, .p pv3 [pv2,pv170231], .c 71, .c 3, .c 5, .c 7, .c 3, .c 31, .c 19, .c 3, .c 13,
  .c 29, .c 3, .c 1163, .c 5, .c 3, .p pv7 [pv2,pv7,pv89,pv1093], .c 79, .c 3, .c 5, .c 17, .c 3,
  .c 241, .c 13, .c 3, .c 41, .c 7, .c 3, .p pv5 [pv2,pv683,pv997], .c 5, .c 3, .c 67,
  .p pv13 [pv2,pv3,pv5,pv11,pv4127], .c 3, .c 5, .c 137, .c 3, .c 11,
]
private theorem h0166c07 : checkBlock 1361667 128 b0166c07 = true := by
  decide +kernel

private def b0166c08 : List Row := [
  .c 31, .c 3, .c 7, .p pv11 [pv2,pv3,pv56747], .c 3, .c 37, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5,
  .c 61, .c 3, .c 1031, .p pv7 [pv2,pv3,pv4729], .c 3, .p pv2 [pv2,pv29,pv59,pv199],
  .p pv3 [pv2,pv3,pv13,pv19,pv919], .c 3, .p pv2 [pv2,pv7,pv97283], .c 5, .c 3, .c 7, .c 13, .c 3,
  .c 5, .c 19, .c 3, .c 877, .c 7, .c 3, .c 11, .c 17, .c 3, .c 71, .c 5, .c 3,
  .p pv7 [pv2,pv11,pv61909], .c 193, .c 3, .c 5, .c 37, .c 3, .c 7, .c 47, .c 3,
  .p pv3 [pv2,pv31,pv1373], .p pv2 [pv2,pv3,pv7,pv32429], .c 3, .c 13, .c 5, .c 3, .c 173, .c 11,
  .c 3, .c 5, .c 23, .c 3, .p pv3 [pv2,pv5,pv17,pv2003], .c 29, .c 3, .c 31, .c 13, .c 3, .c 7,
  .c 5, .c 3, .p pv2 [pv2,pv197,pv3457], .c 41, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv136207],
  .c 797, .c 3, .c 263, .c 283, .c 3, .c 23, .c 5, .c 3, .p pv3 [pv2,pv7,pv13,pv1871], .c 17,
  .c 3, .c 5, .c 11, .c 3, .c 13, .p pv3 [pv2,pv3,pv7,pv41,pv113], .c 3, .c 47, .c 7, .c 3, .c 83,
  .c 5, .c 3, .c 11, .c 593, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv7,pv11,pv29,pv61], .c 59,
  .c 3, .c 7, .c 487, .c 3, .c 41, .c 5, .c 3, .c 317, .c 7, .c 3, .c 5, .c 293, .c 3,
  .p pv7 [pv2,pv5,pv17027], .c 11, .c 3, .c 19, .c 419, .c 3, .c 109, .c 5, .c 3,
]
private theorem h0166c08 : checkBlock 1361923 128 b0166c08 = true := by
  decide +kernel

private def b0166c09 : List Row := [
  .c 7, .p pv11 [pv2,pv3,pv5,pv73,pv311], .c 3, .c 5, .c 101, .c 3, .c 61, .c 7, .c 3, .c 43,
  .c 1123, .c 3, .p pv2 [pv2,pv31,pv127,pv173], .c 5, .c 3, .p pv3 [pv2,pv42569],
  .p pv2 [pv2,pv3,pv5,pv17,pv2671], .c 3, .c 5, .c 29, .c 3, .c 7, .p pv3 [pv2,pv3,pv75679], .c 3,
  .c 17, .c 11, .c 3, .c 31, .c 5, .c 3, .c 467, .c 853, .c 3, .c 5, .p pv3 [pv2,pv3,pv29,pv7829],
  .c 3, .c 11, .c 73, .c 3, .c 13, .c 53, .c 3, .c 7, .c 5, .c 3, .c 131,
  .p pv3 [pv2,pv3,pv5,pv7,pv13,pv499], .c 3, .c 5, .c 7, .c 3, .c 19, .c 13, .c 3,
  .p pv5 [pv2,pv277,pv2459], .c 157, .c 3, .p pv2 [pv2,pv340573], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv13901], .p pv7 [pv2,pv3,pv5,pv19,pv239], .c 3, .c 5, .c 41, .c 3, .c 67,
  .c 23, .c 3, .c 11, .c 7, .c 3, .c 89, .c 5, .c 3, .c 17, .c 383, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv23,pv617], .c 3, .p pv2 [pv2,pv5,pv7,pv37,pv263],
  .p pv3 [pv2,pv3,pv47,pv4831], .c 3, .c 7, .p pv2 [pv2,pv3,pv13,pv41,pv71], .c 3,
  .p pv3 [pv2,pv85147], .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv25229], .c 3,
  .p pv2 [pv2,pv5,pv136237], .c 241, .c 3, .c 37, .c 409, .c 3, .c 11, .c 5, .c 3, .c 7, .c 29,
  .c 3, .c 5, .c 17, .c 3, .p pv7 [pv2,pv5,pv13,pv131], .c 7, .c 3, .p pv5 [pv2,pv571,pv1193],
  .p pv19 [pv2,pv3,pv56767], .c 3, .c 13, .c 5, .c 3, .c 31, .p pv17 [pv2,pv3,pv5,pv29], .c 3,
  .c 5, .c 11, .c 3, .c 7, .c 19,
]
private theorem h0166c09 : checkBlock 1362179 128 b0166c09 = true := by
  decide +kernel

private def b0166c10 : List Row := [
  .c 3, .p pv2 [pv2,pv47,pv7247], .c 13, .c 3, .p pv2 [pv2,pv681221], .c 5, .c 3, .c 11, .c 23,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv127,pv149], .c 3, .p pv2 [pv2,pv5,pv11,pv563],
  .p pv3 [pv2,pv3,pv97,pv2341], .c 3, .c 601, .c 883, .c 3, .c 7, .c 5, .c 3,
  .p pv17 [pv2,pv13,pv29,pv139], .c 31, .c 3, .c 5, .c 7, .c 3, .c 13, .c 11, .c 3, .c 23, .c 17,
  .c 3, .c 967, .c 5, .c 3, .c 19, .p pv3 [pv2,pv3,pv5,pv15139], .c 3, .c 5, .c 13, .c 3,
  .p pv3 [pv2,pv5,pv23,pv1481], .p pv2 [pv2,pv3,pv7,pv32441], .c 3, .c 1033, .c 7, .c 3, .c 17,
  .c 5, .c 3, .c 239, .c 43, .c 3, .c 5, .c 19, .c 3, .p pv7 [pv2,pv5,pv7,pv17,pv229], .c 41,
  .c 3, .c 7, .c 11, .c 3, .c 277, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 47, .c 3, .c 11,
  .c 127, .c 3, .c 103, .c 23, .c 3, .c 509, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv32443], .c 3, .c 83, .c 7, .c 3, .c 139, .p pv3 [pv2,pv3,pv17,pv61,pv73],
  .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv340657], .p pv3 [pv2,pv3,pv5,pv53,pv857], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv31,pv37], .c 3, .c 7, .p pv3 [pv2,pv3,pv19,pv11953], .c 3, .c 11, .c 197,
  .c 3, .p pv2 [pv2,pv17,pv29,pv691], .c 5, .c 3, .c 1091, .c 19, .c 3, .c 5, .c 31, .c 3, .c 47,
  .c 13, .c 3, .c 863, .c 61, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv5323],
]
private theorem h0166c10 : checkBlock 1362435 128 b0166c10 = true := by
  decide +kernel

private def b0166c11 : List Row := [
  .c 11, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv13627], .c 17, .c 3, .p pv2 [pv2,pv467,pv1459],
  .p pv7 [pv2,pv3,pv37853], .c 3, .c 11, .c 5, .c 3, .p pv7 [pv2,pv7,pv19,pv47,pv109], .c 173,
  .c 3, .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv136273], .c 947, .c 3, .c 17, .c 7, .c 3, .c 293,
  .c 5, .c 3, .c 181, .c 13, .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv7,pv31,pv157],
  .p pv2 [pv2,pv3,pv75709], .c 3, .c 7, .c 499, .c 3, .c 23, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv227131], .c 3, .c 31, .c 101, .c 3, .c 29, .c 41, .c 3, .c 13, .c 5, .c 3,
  .c 7, .c 653, .c 3, .c 5, .c 233, .c 3, .c 37, .c 7, .c 3, .c 109, .c 13, .c 3,
  .p pv3 [pv2,pv19,pv4483], .c 5, .c 3, .c 17, .c 59, .c 3, .c 5, .c 67, .c 3, .c 7, .c 31, .c 3,
  .c 89, .c 47, .c 3, .p pv5 [pv2,pv61,pv11171], .c 5, .c 3, .p pv2 [pv2,pv13,pv26209], .c 257,
  .c 3, .c 5, .c 919, .c 3, .c 13, .p pv2 [pv2,pv3,pv227147], .c 3, .c 167, .c 11, .c 3, .c 7,
  .c 5, .c 3, .c 997, .c 397, .c 3, .c 5, .c 7, .c 3, .c 11, .c 29, .c 3, .c 157,
  .p pv3 [pv2,pv3,pv227153], .c 3, .c 61, .c 5, .c 3, .p pv11 [pv2,pv7,pv43,pv283],
  .p pv17 [pv2,pv3,pv5,pv181,pv251], .c 3, .c 5, .p pv19 [pv2,pv3,pv109,pv521], .c 3, .c 17,
  .c 83, .c 3,
]
private theorem h0166c11 : checkBlock 1362691 128 b0166c11 = true := by
  decide +kernel

private def b0166c12 : List Row := [
  .c 97, .c 7, .c 3, .c 47, .c 5, .c 3, .c 13, .c 1109, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv107,pv193], .c 3, .c 29, .p pv2 [pv2,pv3,pv13,pv8737], .c 3, .c 7,
  .c 557, .c 3, .c 73, .c 5, .c 3, .p pv2 [pv2,pv11,pv30977], .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv37861], .c 3, .c 53, .c 19, .c 3, .c 419, .c 17, .c 3, .c 137, .c 5, .c 3,
  .c 7, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv17,pv23,pv83], .c 3, .p pv13 [pv2,pv5,pv136303],
  .c 7, .c 3, .c 13, .c 31, .c 3, .c 11, .c 5, .c 3, .c 23, .p pv3 [pv2,pv3,pv5,pv13,pv233], .c 3,
  .c 5, .c 43, .c 3, .c 7, .c 13, .c 3, .c 173, .p pv13 [pv2,pv3,pv7,pv601], .c 3, .c 107, .c 5,
  .c 3, .c 19, .p pv7 [pv2,pv3,pv5,pv37,pv307], .c 3, .c 5, .c 11, .c 3, .c 127,
  .p pv5 [pv2,pv3,pv113591], .c 3, .c 383, .p pv3 [pv2,pv3,pv11,pv19,pv1087], .c 3, .c 7, .c 5,
  .c 3, .c 11, .c 17, .c 3, .c 5, .c 7, .c 3, .p pv13 [pv2,pv5,pv11,pv1549], .c 359, .c 3, .c 41,
  .c 71, .c 3, .p pv2 [pv2,pv31,pv10993], .c 5, .c 3, .p pv2 [pv2,pv7,pv97367], .c 13, .c 3, .c 5,
  .c 1051, .c 3, .p pv17 [pv2,pv5,pv137,pv199], .c 11, .c 3, .p pv2 [pv2,pv340789], .c 7, .c 3,
  .c 31, .c 5, .c 3, .c 163, .p pv19 [pv2,pv3,pv5,pv45439], .c 3, .c 5, .c 461, .c 3, .c 251,
  .p pv5 [pv2,pv3,pv67,pv3391], .c 3, .c 7, .p pv2 [pv2,pv3,pv47,pv2417], .c 3, .c 13, .c 5, .c 3,
  .c 223, .c 7,
]
private theorem h0166c12 : checkBlock 1362947 128 b0166c12 = true := by
  decide +kernel

private def b0166c13 : List Row := [
  .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv17477], .c 3, .c 283, .c 17, .c 3, .p pv3 [pv2,pv85201],
  .c 11, .c 3, .p pv5 [pv2,pv7,pv97373], .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 229, .c 3, .c 11,
  .c 7, .c 3, .c 17, .c 67, .c 3, .c 431, .c 5, .c 3, .p pv2 [pv2,pv13,pv52433], .c 29, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv53,pv1429], .c 3, .c 7, .p pv5 [pv2,pv3,pv43,pv1321], .c 3,
  .p pv2 [pv2,pv340819], .c 23, .c 3, .c 233, .c 5, .c 3, .c 61, .c 41, .c 3, .c 5, .c 13, .c 3,
  .p pv2 [pv2,pv5,pv13633], .c 79, .c 3, .c 11, .p pv2 [pv2,pv3,pv103,pv1103], .c 3, .c 7, .c 5,
  .c 3, .c 29, .p pv13 [pv2,pv3,pv5,pv7,pv541], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv136333],
  .p pv2 [pv2,pv3,pv17,pv41,pv163], .c 3, .c 241, .c 37, .c 3, .c 691, .c 5, .c 3, .c 13, .c 11,
  .c 3, .c 5, .c 757, .c 3, .p pv3 [pv2,pv5,pv8521], .c 347, .c 3, .p pv5 [pv2,pv17,pv40099],
  .c 7, .c 3, .c 11, .c 5, .c 3, .c 151, .p pv7 [pv2,pv3,pv5,pv31,pv733], .c 3, .c 5, .c 307,
  .c 3, .c 89, .p pv17 [pv2,pv3,pv263], .c 3, .c 7, .c 101, .c 3, .p pv2 [pv2,pv19,pv35879], .c 5,
  .c 3, .p pv3 [pv2,pv85213], .c 7, .c 3, .c 5, .c 11, .c 3, .c 19, .c 47, .c 3, .c 13,
  .p pv19 [pv2,pv3,pv11,pv313], .c 3, .p pv3 [pv2,pv7,pv97,pv251], .c 5, .c 3, .c 7, .c 83, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv7,pv3607], .c 3, .c 17, .c 7, .c 3, .c 521,
]
private theorem h0166c13 : checkBlock 1363203 128 b0166c13 = true := by
  decide +kernel

private def b0166c14 : List Row := [
  .c 19, .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv17,pv20051], .c 659, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv113623], .c 3, .c 7, .c 11, .c 3, .c 37, .p pv37 [pv2,pv3,pv7,pv2029], .c 3,
  .c 29, .c 5, .c 3, .c 149, .c 107, .c 3, .c 5, .c 491, .c 3, .p pv7 [pv2,pv5,pv136351],
  .p pv11 [pv2,pv3,pv56813], .c 3, .c 47, .c 17, .c 3, .c 7, .c 5, .c 3, .c 97, .c 13, .c 3, .c 5,
  .c 7, .c 3, .p pv3 [pv2,pv5,pv79,pv863], .c 349, .c 3, .p pv2 [pv2,pv681773], .c 11, .c 3,
  .c 17, .c 5, .c 3, .p pv7 [pv2,pv7,pv97397], .c 37, .c 3, .c 5, .c 73, .c 3, .c 11, .c 19, .c 3,
  .p pv3 [pv2,pv170447], .c 7, .c 3, .c 13, .c 5, .c 3, .c 227, .c 631, .c 3, .c 5, .c 31, .c 3,
  .c 23, .p pv2 [pv2,pv3,pv227267], .c 3, .c 7, .c 13, .c 3, .c 449, .c 5, .c 3, .c 41, .c 7,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv71,pv97], .c 3, .p pv11 [pv2,pv5,pv19,pv7177], .c 503, .c 3,
  .c 11, .c 353, .c 3, .c 661, .c 5, .c 3, .c 7, .c 67, .c 3, .c 5, .c 619, .c 3, .c 13, .c 7,
  .c 3, .c 29, .c 601, .c 3, .p pv3 [pv2,pv17,pv37,pv271], .c 5, .c 3, .p pv7 [pv2,pv681839],
  .c 11, .c 3, .c 5, .c 13, .c 3, .c 7, .c 23, .c 3, .c 71, .c 109, .c 3, .c 11, .c 5, .c 3,
  .c 37, .c 823, .c 3,
]
private theorem h0166c14 : checkBlock 1363459 128 b0166c14 = true := by
  decide +kernel

private def b0166c15 : List Row := [
  .c 5, .p pv2 [pv2,pv3,pv23,pv61], .c 3, .c 31, .c 17, .c 3, .p pv5 [pv2,pv7,pv13,pv59,pv127],
  .c 139, .c 3, .c 7, .c 5, .c 3, .c 13, .c 313, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv1091],
  .p pv11 [pv2,pv3,pv13,pv31,pv47], .c 3, .c 17, .c 173, .c 3, .c 19, .c 5, .c 3, .c 11,
  .p pv13 [pv2,pv3,pv5,pv5051], .c 3, .c 5, .c 61, .c 3, .p pv3 [pv2,pv5,pv11,pv6199], .c 29,
  .c 3, .p pv2 [pv2,pv73,pv9341], .c 7, .c 3, .p pv3 [pv2,pv85237], .c 5, .c 3, .c 47, .c 19,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv75767], .c 3, .p pv23 [pv2,pv5,pv7,pv19483], .c 11, .c 3, .c 7,
  .c 241, .c 3, .c 103, .c 5, .c 3, .c 1063, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv89,pv1277], .c 3,
  .c 29, .c 13, .c 3, .p pv5 [pv2,pv11,pv47,pv1319], .c 53, .c 3, .c 127, .c 5, .c 3, .c 7,
  .c 541, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv4639], .c 3, .c 787, .c 7, .c 3, .c 19, .c 11, .c 3,
  .p pv2 [pv2,pv13,pv52457], .c 5, .c 3, .c 167, .p pv41 [pv2,pv3,pv5,pv11,pv4133], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv19,pv997], .c 3, .c 7, .c 59, .c 3, .c 31, .p pv11 [pv2,pv3,pv7,pv13,pv1249],
  .c 3, .p pv3 [pv2,pv11,pv1409], .c 5, .c 3, .c 67, .c 13, .c 3, .c 5, .c 17, .c 3, .c 37,
  .p pv5 [pv2,pv3,pv73,pv173], .c 3, .p pv3 [pv2,pv7,pv6089], .c 83, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv277,pv1231], .c 683, .c 3, .c 5, .c 7, .c 3, .c 17, .p pv2 [pv2,pv3,pv59,pv3853],
  .c 3, .c 11, .c 23,
]
private theorem h0166c15 : checkBlock 1363715 128 b0166c15 = true := by
  decide +kernel

private def b0166c16 : List Row := [
  .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv7,pv11,pv17,pv521], .c 71, .c 3, .c 5, .c 47, .c 3,
  .c 19, .p pv13 [pv2,pv3,pv7,pv23,pv353], .c 3, .c 443, .c 7, .c 3, .c 43, .c 5, .c 3,
  .p pv3 [pv2,pv53,pv3217], .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv157,pv181], .c 3, .c 59, .c 113,
  .c 3, .c 7, .c 17, .c 3, .c 11, .c 5, .c 3, .p pv17 [pv2,pv13,pv23,pv2281], .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv17,pv43,pv311], .c 3, .c 13, .c 67, .c 3, .c 347, .p pv2 [pv2,pv3,pv75781],
  .c 3, .c 17, .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv41,pv1109], .c 3, .c 5, .c 11, .c 3, .c 47,
  .c 7, .c 3, .c 487, .c 43, .c 3, .c 31, .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv4547], .c 3,
  .c 5, .c 23, .c 3, .c 7, .c 733, .c 3, .c 653, .c 571, .c 3, .c 71, .c 5, .c 3, .c 13, .c 17,
  .c 3, .c 5, .p pv7 [pv2,pv3,pv113,pv503], .c 3, .p pv2 [pv2,pv5,pv68207], .c 11, .c 3, .c 163,
  .c 563, .c 3, .c 7, .c 5, .c 3, .c 179, .p pv11 [pv2,pv3,pv5,pv7,pv29], .c 3, .c 5, .c 7, .c 3,
  .c 673, .c 157, .c 3, .p pv3 [pv2,pv11,pv23,pv337], .p pv2 [pv2,pv3,pv227363], .c 3,
  .p pv5 [pv2,pv17,pv40123], .c 5, .c 3, .c 29, .p pv29 [pv2,pv3,pv5,pv37,pv1229], .c 3, .c 5,
  .c 181, .c 3, .p pv3 [pv2,pv5,pv19,pv359], .p pv2 [pv2,pv3,pv7,pv401], .c 3, .c 13, .c 7, .c 3,
  .p pv2 [pv2,pv239,pv1427], .c 5, .c 3, .c 19, .p pv2 [pv2,pv3,pv5,pv11,pv13,pv53], .c 3, .c 5,
]
private theorem h0166c16 : checkBlock 1363971 128 b0166c16 = true := by
  decide +kernel

private def b0166c17 : List Row := [
  .c 37, .c 3, .c 11, .c 13, .c 3, .c 7, .p pv3 [pv2,pv3,pv19,pv3989], .c 3,
  .p pv2 [pv2,pv11,pv62011], .c 5, .c 3, .c 113, .c 7, .c 3, .c 5, .c 19, .c 3, .c 43,
  .p pv19 [pv2,pv3,pv227377], .c 3, .c 17, .c 47, .c 3, .c 53, .c 5, .c 3, .c 7, .c 89, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv7,pv11,pv2953], .c 3, .c 23, .c 7, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv13,pv17491], .c 3, .p pv5 [pv2,pv682151], .c 5, .c 3,
  .p pv2 [pv2,pv11,pv101,pv307], .c 13, .c 3, .c 5, .c 193, .c 3, .c 7, .p pv2 [pv2,pv3,pv227387],
  .c 3, .p pv5 [pv2,pv53,pv61,pv211], .p pv13 [pv2,pv3,pv7,pv2707], .c 3, .c 19, .c 5, .c 3,
  .p pv2 [pv2,pv37,pv103,pv179], .c 11, .c 3, .c 5, .c 43, .c 3, .p pv7 [pv2,pv5,pv13,pv2099],
  .c 109, .c 3, .c 41, .p pv3 [pv2,pv3,pv227393], .c 3, .c 7, .c 5, .c 3, .c 17, .c 19, .c 3,
  .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv68219], .c 23, .c 3, .c 61, .c 13, .c 3, .c 149, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv41,pv2377], .p pv7 [pv2,pv3,pv5,pv379], .c 3, .c 5, .c 11, .c 3, .c 1103,
  .c 257, .c 3, .p pv3 [pv2,pv21319], .c 7, .c 3, .p pv5 [pv2,pv197,pv3463], .c 5, .c 3, .c 11,
  .p pv17 [pv2,pv3,pv5,pv45481], .c 3, .c 5, .c 17, .c 3, .c 13, .c 73, .c 3, .c 7, .c 37, .c 3,
  .p pv2 [pv2,pv23,pv14831], .c 5, .c 3, .c 89, .c 7, .c 3, .c 5, .c 13, .c 3, .c 17, .c 11, .c 3,
  .p pv3 [pv2,pv43,pv7933], .c 29, .c 3,
]
private theorem h0166c17 : checkBlock 1364227 128 b0166c17 = true := by
  decide +kernel

private def b0166c18 : List Row := [
  .p pv2 [pv2,pv7,pv97463], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv15161], .c 3, .c 5, .c 227,
  .c 3, .c 293, .c 7, .c 3, .c 523, .c 61, .c 3, .c 337, .c 5, .c 3, .c 13, .c 23, .c 3, .c 5,
  .c 31, .c 3, .c 7, .p pv5 [pv2,pv3,pv13,pv8747], .c 3, .c 29, .c 11, .c 3, .c 199, .c 5, .c 3,
  .c 71, .c 47, .c 3, .c 5, .c 167, .c 3, .c 11, .c 139, .c 3, .c 23, .p pv7 [pv2,pv3,pv56857],
  .c 3, .c 7, .c 5, .c 3, .c 727, .p pv2 [pv2,pv3,pv5,pv7,pv19], .c 3, .c 5, .c 7, .c 3, .c 53,
  .c 1033, .c 3, .c 13, .c 19, .c 3, .c 41, .c 5, .c 3, .p pv3 [pv2,pv7,pv1523], .c 59, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv11,pv1723], .c 3, .p pv2 [pv2,pv5,pv31,pv71], .c 13, .c 3, .c 11, .c 7,
  .c 3, .p pv3 [pv2,pv170579], .c 5, .c 3, .c 503, .c 17, .c 3, .c 5, .c 103, .c 3, .c 31, .c 29,
  .c 3, .c 7, .c 23, .c 3, .p pv5 [pv2,pv13,pv73,pv719], .c 5, .c 3, .c 881, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv113723], .c 3, .c 233, .c 419, .c 3, .c 251, .c 641, .c 3, .c 11, .c 5, .c 3,
  .c 7, .c 13, .c 3, .c 5, .c 263, .c 3, .c 29, .c 7, .c 3, .p pv2 [pv2,pv341179],
  .p pv3 [pv2,pv3,pv227453], .c 3, .c 67, .c 5, .c 3, .c 59, .p pv2 [pv2,pv3,pv5,pv45491], .c 3,
  .c 5, .c 11,
]
private theorem h0166c18 : checkBlock 1364483 128 b0166c18 = true := by
  decide +kernel

private def b0166c19 : List Row := [
  .c 3, .c 7, .c 17, .c 3, .p pv2 [pv2,pv682373], .c 1049, .c 3, .c 13, .c 5, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv5,pv17,pv223], .c 3, .c 5, .c 41, .c 3, .p pv2 [pv2,pv5,pv11,pv19,pv653],
  .p pv2 [pv2,pv3,pv113731], .c 3, .c 17, .c 13, .c 3, .c 7, .c 5, .c 3, .c 19,
  .p pv3 [pv2,pv3,pv5,pv7,pv67,pv97], .c 3, .c 5, .c 7, .c 3, .c 157, .c 11, .c 3, .c 373,
  .p pv7 [pv2,pv3,pv19,pv41,pv73], .c 3, .c 101, .c 5, .c 3, .c 37,
  .p pv7 [pv2,pv3,pv5,pv23,pv43], .c 3, .c 5, .c 19, .c 3, .c 13, .c 47, .c 3, .c 31, .c 7, .c 3,
  .c 23, .c 5, .c 3, .c 41, .c 439, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv7,pv9749], .c 43,
  .c 3, .c 7, .c 11, .c 3, .c 367, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 97, .c 3, .c 11, .c 37,
  .c 3, .p pv3 [pv2,pv13,pv17,pv193], .c 31, .c 3, .c 19, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv45497], .c 3, .c 5, .p pv13 [pv2,pv3,pv7,pv16249], .c 3, .c 181, .c 7,
  .c 3, .c 47, .c 239, .c 3, .c 739, .c 5, .c 3, .c 349, .c 19, .c 3, .c 5, .c 17, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv56873], .c 3, .c 11, .c 211, .c 3, .p pv2 [pv2,pv53,pv79,pv163], .c 5, .c 3,
  .p pv13 [pv2,pv11,pv15511], .p pv3 [pv2,pv3,pv5,pv173,pv263], .c 3, .c 5, .c 431, .c 3, .c 17,
  .c 223, .c 3, .c 13, .c 149, .c 3, .c 7,
]
private theorem h0166c19 : checkBlock 1364739 128 b0166c19 = true := by
  decide +kernel

private def b0166c20 : List Row := [
  .c 5, .c 3, .c 107, .c 11, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv136501], .c 13, .c 3,
  .c 19, .p pv2 [pv2,pv3,pv83,pv2741], .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv7,pv48751], .c 569,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv19,pv5987], .c 3, .c 37, .p pv3 [pv2,pv3,pv7,pv4643], .c 3,
  .p pv5 [pv2,pv71,pv9613], .c 7, .c 3, .c 839, .c 5, .c 3, .c 29, .c 487, .c 3, .c 5, .c 11,
  .c 3, .p pv7 [pv2,pv5,pv7,pv19501], .c 23, .c 3, .c 7, .p pv7 [pv2,pv3,pv11,pv13,pv37,pv43],
  .c 3, .c 17, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv23,pv2473], .c 3, .c 83,
  .p pv3 [pv2,pv3,pv181,pv419], .c 3, .p pv2 [pv2,pv107,pv6379], .p pv2 [pv2,pv3,pv113759], .c 3,
  .c 1069, .c 5, .c 3, .c 7, .c 43, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv32503], .c 3, .c 19, .c 7,
  .c 3, .p pv5 [pv2,pv41,pv2081], .p pv2 [pv2,pv3,pv149,pv509], .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv341287], .c 17, .c 3, .c 5, .c 1093, .c 3, .c 7, .p pv3 [pv2,pv3,pv47,pv103],
  .c 3, .p pv5 [pv2,pv11,pv62053], .c 13, .c 3, .c 73, .c 5, .c 3, .c 1109,
  .p pv2 [pv2,pv3,pv5,pv61,pv373], .c 3, .c 5, .c 337, .c 3, .c 151, .p pv23 [pv2,pv3,pv67,pv283],
  .c 3, .p pv2 [pv2,pv7,pv48757], .c 11, .c 3, .c 7, .c 5, .c 3, .c 31, .c 23, .c 3, .c 5, .c 7,
  .c 3, .c 11, .p pv5 [pv2,pv3,pv227537], .c 3, .c 53, .c 307, .c 3, .c 29, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv13931], .c 61, .c 3, .c 5, .c 13, .c 3,
]
private theorem h0166c20 : checkBlock 1364995 128 b0166c20 = true := by
  decide +kernel

private def b0166c21 : List Row := [
  .p pv2 [pv2,pv5,pv43,pv127], .c 17, .c 3, .c 23, .c 7, .c 3, .c 37, .c 5, .c 3,
  .p pv2 [pv2,pv191,pv1787], .c 31, .c 3, .c 5, .c 359, .c 3, .p pv3 [pv2,pv5,pv7,pv23,pv53],
  .c 19, .c 3, .c 7, .p pv29 [pv2,pv3,pv163,pv349], .c 3, .c 43, .c 5, .c 3, .c 13, .c 7, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv313,pv727], .c 3, .p pv17 [pv2,pv5,pv136531],
  .p pv5 [pv2,pv3,pv13,pv547], .c 3, .c 683, .c 59, .c 3, .c 821, .c 5, .c 3, .c 7, .c 11, .c 3,
  .c 5, .c 37, .c 3, .c 41, .c 7, .c 3, .p pv2 [pv2,pv682673], .c 23, .c 3, .c 11, .c 5, .c 3,
  .c 19, .p pv11 [pv2,pv3,pv5,pv5689], .c 3, .c 5, .p pv5 [pv2,pv3,pv227561], .c 3, .c 7,
  .p pv5 [pv2,pv3,pv17,pv23,pv97], .c 3, .c 13, .c 43, .c 3, .p pv5 [pv2,pv41,pv16651], .c 5,
  .c 3, .c 17, .c 941, .c 3, .c 5, .c 11, .c 3, .c 71, .c 13, .c 3, .c 29, .c 449, .c 3, .c 7,
  .c 5, .c 3, .c 11, .c 617, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv11,pv12413], .c 83, .c 3,
  .c 59, .c 53, .c 3, .c 109, .c 5, .c 3, .p pv3 [pv2,pv7,pv37,pv659], .c 163, .c 3, .c 5, .c 17,
  .c 3, .p pv2 [pv2,pv5,pv67,pv1019], .c 11, .c 3, .p pv2 [pv2,pv682733], .c 7, .c 3, .c 19, .c 5,
  .c 3, .c 137, .c 13, .c 3, .c 5, .c 23, .c 3, .c 17, .c 151, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv8429], .c 3, .p pv5 [pv2,pv682751], .c 5,
]
private theorem h0166c21 : checkBlock 1365251 128 b0166c21 = true := by
  decide +kernel

private def b0166c22 : List Row := [
  .c 3, .c 677, .c 7, .c 3, .c 5, .c 673, .c 3, .c 419, .c 29, .c 3, .c 67, .c 11, .c 3, .c 13,
  .c 5, .c 3, .c 7, .c 521, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv13,pv41,pv61], .c 3, .c 11, .c 7,
  .c 3, .p pv2 [pv2,pv23,pv14843], .c 13, .c 3, .p pv2 [pv2,pv11,pv62071], .c 5, .c 3, .c 271,
  .p pv2 [pv2,pv3,pv5,pv15173], .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv3347], .c 3, .c 7,
  .p pv3 [pv2,pv3,pv227597], .c 3, .c 19, .c 911, .c 3, .c 17, .c 5, .c 3, .c 83, .c 311, .c 3,
  .c 5, .c 61, .c 3, .c 13, .c 233, .c 3, .c 11, .c 313, .c 3, .c 7, .c 5, .c 3, .c 479, .c 127,
  .c 3, .c 5, .c 7, .c 3, .c 107, .c 31, .c 3, .c 509, .c 953, .c 3, .c 853, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv97547], .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv227611], .c 3, .c 23, .c 59,
  .c 3, .c 103, .c 7, .c 3, .c 11, .c 5, .c 3, .c 13, .c 251, .c 3, .c 5, .c 29, .c 3, .c 19,
  .p pv5 [pv2,pv3,pv13,pv17509], .c 3, .c 7, .p pv2 [pv2,pv3,pv113809], .c 3, .c 269, .c 5, .c 3,
  .p pv11 [pv2,pv113,pv6043], .c 7, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv136573],
  .p pv5 [pv2,pv3,pv59,pv643], .c 3, .c 199, .c 19, .c 3, .c 157, .c 5, .c 3, .c 7, .c 41, .c 3,
  .c 5, .c 53, .c 3, .p pv13 [pv2,pv5,pv11,pv97],
]
private theorem h0166c22 : checkBlock 1365507 128 b0166c22 = true := by
  decide +kernel

private def b0166c23 : List Row := [
  .c 7, .c 3, .c 13, .c 443, .c 3, .c 47, .c 5, .c 3, .c 389, .c 37, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv23,pv3299], .c 3, .c 7, .c 11, .c 3, .c 17, .p pv7 [pv2,pv3,pv7,pv31,pv1049],
  .c 3, .c 211, .c 5, .c 3, .c 23, .p pv2 [pv2,pv3,pv5,pv53,pv859], .c 3, .c 5, .c 647, .c 3,
  .p pv2 [pv2,pv5,pv47,pv1453], .c 101, .c 3, .c 71, .c 31, .c 3, .c 7, .c 5, .c 3, .c 431,
  .c 191, .c 3, .c 5, .c 7, .c 3, .c 61, .c 19, .c 3, .c 97, .c 11, .c 3, .c 53, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv48781], .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv12647], .c 3, .c 11, .c 89, .c 3,
  .c 277, .c 7, .c 3, .c 167, .c 5, .c 3, .c 17, .c 23, .c 3, .c 5, .p pv3 [pv2,pv3,pv227651],
  .c 3, .p pv17 [pv2,pv5,pv7,pv13,pv19,pv79], .p pv5 [pv2,pv3,pv61,pv311], .c 3, .c 7,
  .p pv3 [pv2,pv3,pv227653], .c 3, .c 13, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 131, .c 3,
  .c 281, .c 461, .c 3, .c 11, .c 13, .c 3, .c 31, .c 5, .c 3, .c 7, .c 47, .c 3, .c 5, .c 17,
  .c 3, .c 641, .c 7, .c 3, .p pv3 [pv2,pv73,pv2339], .p pv2 [pv2,pv3,pv227663], .c 3,
  .p pv5 [pv2,pv269,pv2539], .c 5, .c 3, .c 79, .c 11, .c 3, .c 5, .c 41, .c 3, .c 7, .c 37, .c 3,
  .c 181, .p pv11 [pv2,pv3,pv7,pv47,pv173], .c 3, .c 11, .c 5, .c 3,
]
private theorem h0166c23 : checkBlock 1365763 128 b0166c23 = true := by
  decide +kernel

private def b0166c24 : List Row := [
  .p pv2 [pv2,pv17,pv40177], .p pv17 [pv2,pv3,pv5,pv7589], .c 3, .c 5, .c 13, .c 3,
  .p pv7 [pv2,pv5,pv136603], .c 727, .c 3, .c 331, .c 23, .c 3, .c 7, .c 5, .c 3, .c 73, .c 97,
  .c 3, .c 5, .c 7, .c 3, .c 89, .c 67, .c 3, .c 43, .c 17, .c 3, .c 601, .c 5, .c 3, .c 11,
  .c 19, .c 3, .c 5, .p pv3 [pv2,pv3,pv17,pv59,pv227], .c 3, .c 1117,
  .p pv5 [pv2,pv3,pv7,pv13,pv139], .c 3, .c 83, .c 7, .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv23,pv31,pv479], .c 71, .c 3, .c 5, .p pv5 [pv2,pv3,pv113843], .c 3,
  .p pv3 [pv2,pv5,pv7,pv17,pv41], .c 11, .c 3, .c 7, .c 863, .c 3, .c 619, .c 5, .c 3, .c 31,
  .c 7, .c 3, .c 5, .c 79, .c 3, .c 37, .c 43, .c 3, .c 13, .p pv11 [pv2,pv3,pv227693], .c 3,
  .p pv2 [pv2,pv7,pv97583], .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 23, .c 3, .c 53, .c 7, .c 3,
  .p pv2 [pv2,pv677,pv1009], .c 11, .c 3, .c 251, .c 5, .c 3, .c 131, .c 31, .c 3, .c 5, .c 401,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv257,pv443], .c 3, .c 61, .c 29, .c 3, .c 23, .c 5, .c 3, .c 241,
  .c 139, .c 3, .c 5, .c 1151, .c 3, .p pv3 [pv2,pv5,pv8539], .c 41, .c 3, .c 193, .c 701, .c 3,
  .c 7, .c 5, .c 3, .c 293, .c 13, .c 3, .c 5, .c 7, .c 3, .c 19, .c 17,
]
private theorem h0166c24 : checkBlock 1366019 128 b0166c24 = true := by
  decide +kernel

private def b0166c25 : List Row := [
  .c 3, .c 11, .p pv17 [pv2,pv3,pv61,pv3733], .c 3, .c 107, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv11,pv1109], .p pv3 [pv2,pv3,pv5,pv17,pv19,pv47], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv56929], .c 3, .c 137, .p pv3 [pv2,pv3,pv7,pv32531], .c 3, .c 17, .c 7, .c 3,
  .c 13, .c 5, .c 3, .c 599, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv5839], .c 3, .c 67,
  .p pv5 [pv2,pv3,pv11,pv941], .c 3, .c 7, .c 13, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv341587],
  .c 7, .c 3, .c 5, .c 607, .c 3, .c 23, .c 239, .c 3, .p pv5 [pv2,pv19,pv41,pv877], .c 181, .c 3,
  .c 37, .c 5, .c 3, .c 7, .c 59, .c 3, .c 5, .c 11, .c 3, .c 13, .c 7, .c 3,
  .p pv2 [pv2,pv113,pv3023], .c 151, .c 3, .c 571, .c 5, .c 3, .c 11, .c 43, .c 3, .c 5, .c 13,
  .c 3, .c 7, .c 19, .c 3, .p pv2 [pv2,pv17,pv40189], .c 83, .c 3, .p pv3 [pv2,pv42701], .c 5,
  .c 3, .c 97, .c 277, .c 3, .c 5, .c 37, .c 3, .c 29, .c 11, .c 3, .c 307,
  .p pv2 [pv2,pv3,pv227743], .c 3, .c 7, .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv7,pv241], .c 3,
  .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv19,pv29,pv31], .p pv2 [pv2,pv3,pv13,pv17519], .c 3, .c 73,
  .c 41, .c 3, .p pv2 [pv2,pv341623], .c 5, .c 3, .c 19, .c 103, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv89,pv853], .c 3, .c 17, .c 769, .c 3, .p pv2 [pv2,pv341629], .c 7, .c 3,
  .p pv2 [pv2,pv23,pv61,pv487], .c 5, .c 3, .p pv3 [pv2,pv17,pv157],
]
private theorem h0166c25 : checkBlock 1366275 128 b0166c25 = true := by
  decide +kernel

private def b0166c26 : List Row := [
  .p pv2 [pv2,pv3,pv5,pv11,pv41,pv101], .c 3, .c 5, .c 19, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv31,pv79], .c 3, .c 7, .p pv2 [pv2,pv3,pv263,pv433], .c 3, .c 919, .c 5, .c 3,
  .c 929, .c 7, .c 3, .c 5, .c 29, .c 3, .c 41, .c 13, .c 3, .p pv3 [pv2,pv85411], .c 17, .c 3,
  .c 43, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv11,pv17,pv29], .c 3,
  .p pv3 [pv2,pv5,pv6833], .c 7, .c 3, .c 11, .p pv7 [pv2,pv3,pv71,pv401], .c 3, .c 17, .c 5,
  .c 3, .c 47, .c 79, .c 3, .c 5, .p pv2 [pv2,pv3,pv43,pv5297], .c 3, .c 7, .c 73, .c 3, .c 23,
  .p pv7 [pv2,pv3,pv7,pv13,pv2503], .c 3, .p pv2 [pv2,pv109,pv6269], .c 5, .c 3,
  .p pv3 [pv2,pv139,pv1229], .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv3559], .c 3,
  .p pv2 [pv2,pv5,pv23,pv2971], .p pv3 [pv2,pv3,pv11,pv20707], .c 3,
  .p pv2 [pv2,pv7,pv31,pv47,pv67], .c 37, .c 3, .c 7, .c 5, .c 3, .c 71, .c 17, .c 3, .c 5, .c 7,
  .c 3, .c 1123, .p pv7 [pv2,pv3,pv113891], .c 3, .c 31, .c 331, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv19,pv367], .c 53, .c 3, .c 5, .c 11, .c 3, .p pv7 [pv2,pv5,pv4271], .c 131,
  .c 3, .c 19, .c 7, .c 3, .c 67, .c 5, .c 3, .c 11, .c 29, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv19,pv631], .c 3, .c 109, .p pv7 [pv2,pv3,pv23,pv619], .c 3, .c 7, .c 31, .c 3,
  .p pv2 [pv2,pv683381], .c 5, .c 3, .p pv3 [pv2,pv13,pv6571], .c 7, .c 3, .c 5, .c 149, .c 3,
  .c 13, .c 11, .c 3,
]
private theorem h0166c26 : checkBlock 1366531 128 b0166c26 = true := by
  decide +kernel

private def b0166c27 : List Row := [
  .c 139, .c 269, .c 3, .p pv3 [pv2,pv7,pv24407], .c 5, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv5,pv17,pv67], .c 3, .c 5, .c 13, .c 3, .c 263, .c 7, .c 3, .c 17, .c 719,
  .c 3, .c 977, .c 5, .c 3, .p pv2 [pv2,pv29,pv11783], .p pv29 [pv2,pv3,pv5,pv15187], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv113903], .c 3, .c 7, .p pv2 [pv2,pv3,pv157,pv1451], .c 3, .c 1049, .c 11,
  .c 3, .c 59, .c 5, .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv11,pv19,pv109], .c 3, .c 5, .c 23, .c 3,
  .c 11, .c 173, .c 3, .p pv2 [pv2,pv7,pv48817], .c 19, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv61,pv2801], .c 37, .c 3, .c 5, .c 7, .c 3, .c 47, .p pv3 [pv2,pv3,pv17,pv1489],
  .c 3, .p pv2 [pv2,pv683453], .c 467, .c 3, .c 23, .c 5, .c 3, .c 17,
  .p pv7 [pv2,pv3,pv5,pv3797], .c 3, .c 5, .c 43, .c 3, .c 199, .p pv11 [pv2,pv3,pv7,pv16273],
  .c 3, .c 11, .c 7, .c 3, .p pv5 [pv2,pv683471], .c 5, .c 3, .c 61, .c 89, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv4219], .c 3, .c 113, .c 13, .c 3, .c 7, .c 109, .c 3, .c 29, .c 5, .c 3,
  .p pv2 [pv2,pv683489], .c 7, .c 3, .c 5, .c 17, .c 3, .p pv13 [pv2,pv5,pv223,pv613], .c 19,
  .c 3, .p pv2 [pv2,pv341749], .c 157, .c 3, .c 11, .c 5, .c 3, .c 7, .c 233, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv79,pv103], .c 3, .c 17, .c 7, .c 3, .p pv2 [pv2,pv683513], .c 53, .c 3,
  .c 349, .c 5, .c 3, .c 37, .c 13,
]
private theorem h0166c27 : checkBlock 1366787 128 b0166c27 = true := by
  decide +kernel

private def b0166c28 : List Row := [
  .c 3, .c 5, .c 11, .c 3, .c 7, .c 379, .c 3, .p pv3 [pv2,pv43,pv1987],
  .p pv2 [pv2,pv3,pv7,pv11,pv269], .c 3, .c 41, .c 5, .c 3, .c 11, .c 61, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv37,pv3079], .c 3, .c 163, .c 937, .c 3, .p pv5 [pv2,pv7,pv97649], .c 17, .c 3,
  .c 7, .c 5, .c 3, .c 43, .p pv2 [pv2,pv3,pv5,pv7,pv31], .c 3, .c 5, .c 7, .c 3, .c 647, .c 11,
  .c 3, .p pv2 [pv2,pv131,pv2609], .c 13, .c 3, .c 17, .c 5, .c 3, .c 89, .c 31, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv47,pv101], .c 3, .p pv2 [pv2,pv5,pv17,pv4021], .c 23, .c 3, .c 29, .c 7,
  .c 3, .p pv3 [pv2,pv85447], .c 5, .c 3, .p pv23 [pv2,pv13,pv52583],
  .p pv7 [pv2,pv3,pv5,pv11393], .c 3, .c 5, .p pv5 [pv2,pv3,pv23,pv9907], .c 3, .c 13, .c 283,
  .c 3, .c 7, .c 11, .c 3, .c 19, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 13, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv19,pv67,pv179], .c 3, .c 59, .c 337, .c 3, .c 223, .c 5, .c 3, .c 7, .c 19,
  .c 3, .c 5, .c 41, .c 3, .p pv17 [pv2,pv5,pv47,pv2909], .c 7, .c 3, .c 101, .c 463, .c 3,
  .c 877, .c 5, .c 3, .c 13, .c 1069, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv5179], .c 3, .c 7, .c 29,
  .c 3, .c 11, .c 67, .c 3, .c 941, .c 5, .c 3, .p pv7 [pv2,pv11,pv19,pv3271], .c 23, .c 3, .c 5,
  .c 409, .c 3, .p pv2 [pv2,pv5,pv73,pv1873], .c 17, .c 3, .c 19,
]
private theorem h0166c28 : checkBlock 1367043 128 b0166c28 = true := by
  decide +kernel

private def b0166c29 : List Row := [
  .p pv2 [pv2,pv3,pv37,pv2053], .c 3, .c 7, .c 5, .c 3, .c 41, .c 11, .c 3, .c 5, .c 7, .c 3,
  .c 29, .p pv3 [pv2,pv3,pv11,pv20717], .c 3, .c 13, .c 199, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv101,pv967], .p pv2 [pv2,pv3,pv5,pv13,pv1753], .c 3, .c 5, .c 53, .c 3,
  .c 1051, .c 13, .c 3, .c 43, .c 7, .c 3, .c 73, .c 5, .c 3, .c 191, .c 47, .c 3, .c 5, .c 11,
  .c 3, .c 179, .p pv5 [pv2,pv3,pv349,pv653], .c 3, .c 7, .c 71, .c 3,
  .p pv3 [pv2,pv13,pv19,pv173], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 163, .c 3, .c 19, .c 113,
  .c 3, .p pv3 [pv2,pv170927], .c 23, .c 3, .p pv5 [pv2,pv7,pv97673], .c 5, .c 3, .c 7, .c 13,
  .c 3, .c 5, .c 29, .c 3, .c 31, .c 7, .c 3, .p pv5 [pv2,pv17,pv37,pv1087], .c 19, .c 3, .c 53,
  .c 5, .c 3, .p pv2 [pv2,pv593,pv1153], .p pv2 [pv2,pv3,pv5,pv71,pv107], .c 3, .c 5, .c 311,
  .c 3, .c 7, .c 41, .c 3, .c 233, .p pv3 [pv2,pv3,pv7,pv10853], .c 3, .c 13, .c 5, .c 3, .c 691,
  .c 211, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv547], .c 31, .c 3,
  .p pv2 [pv2,pv7,pv19,pv53,pv97], .c 11, .c 3, .c 7, .c 5, .c 3, .p pv17 [pv2,pv683759],
  .p pv17 [pv2,pv3,pv5,pv7,pv11,pv37], .c 3, .c 5, .c 7, .c 3, .c 11, .p pv5 [pv2,pv3,pv37987],
  .c 3, .c 67, .p pv2 [pv2,pv3,pv317,pv719], .c 3, .p pv7 [pv2,pv11,pv5651], .c 5, .c 3, .c 277,
  .p pv11 [pv2,pv3,pv5,pv1013], .c 3,
]
private theorem h0166c29 : checkBlock 1367299 128 b0166c29 = true := by
  decide +kernel

private def b0166c30 : List Row := [
  .c 5, .c 23, .c 3, .c 13, .c 19, .c 3, .c 107, .c 7, .c 3, .p pv2 [pv2,pv43,pv7951], .c 5, .c 3,
  .p pv2 [pv2,pv683789], .p pv7 [pv2,pv3,pv5,pv23,pv991], .c 3, .c 5, .c 13, .c 3, .c 83,
  .p pv7 [pv2,pv3,pv56983], .c 3, .c 7, .c 17, .c 3, .c 23, .c 5, .c 3, .c 661, .c 7, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv17,pv419], .c 3, .c 139, .c 109, .c 3, .c 31, .c 1061, .c 3, .c 17, .c 5,
  .c 3, .c 7, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv32563], .c 3, .c 701, .c 7, .c 3, .c 503,
  .c 223, .c 3, .c 11, .c 5, .c 3, .c 29, .c 67, .c 3, .c 5, .c 19, .c 3, .c 7, .c 509, .c 3,
  .p pv5 [pv2,pv683843], .c 31, .c 3, .c 383, .c 5, .c 3, .c 251, .c 17, .c 3, .c 5, .c 11, .c 3,
  .p pv7 [pv2,pv5,pv233,pv587], .p pv5 [pv2,pv3,pv1583], .c 3, .c 13, .c 41, .c 3, .c 7, .c 5,
  .c 3, .c 11, .c 349, .c 3, .c 5, .c 7, .c 3, .c 23, .c 13, .c 3, .c 47,
  .p pv2 [pv2,pv3,pv37993], .c 3, .c 19, .c 5, .c 3, .c 499, .p pv7 [pv2,pv3,pv5,pv41,pv139],
  .c 3, .c 5, .c 883, .c 3, .c 53, .c 11, .c 3, .p pv3 [pv2,pv42743], .c 7, .c 3,
  .p pv7 [pv2,pv13,pv31,pv1697], .c 5, .c 3, .p pv2 [pv2,pv341947], .c 19, .c 3, .c 5, .c 59,
  .c 3, .c 41, .c 17, .c 3, .c 7, .c 367,
]
private theorem h0166c30 : checkBlock 1367555 128 b0166c30 = true := by
  decide +kernel

private def b0166c31 : List Row := [
  .c 3, .c 31, .c 5, .c 3, .p pv2 [pv2,pv683909], .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv277,pv823],
  .c 3, .p pv31 [pv2,pv5,pv43,pv3181], .c 23, .c 3, .c 17, .c 11, .c 3, .c 29, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv11,pv829], .c 3, .c 5, .p pv17 [pv2,pv3,pv7,pv23,pv59], .c 3, .c 11, .c 7,
  .c 3, .c 19, .p pv2 [pv2,pv3,pv113989], .c 3, .c 13, .c 5, .c 3, .c 23,
  .p pv13 [pv2,pv3,pv5,pv11399], .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv19,pv71], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv37997], .c 3, .c 167, .c 13, .c 3, .p pv5 [pv2,pv23,pv131,pv227], .c 5, .c 3,
  .c 151, .c 173, .c 3, .c 5, .c 127, .c 3, .p pv3 [pv2,pv5,pv17099], .c 83, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv2111], .c 3, .c 7, .c 5, .c 3, .c 17, .c 157, .c 3, .c 5, .c 7, .c 3, .c 13,
  .p pv5 [pv2,pv3,pv28499], .c 3, .c 71, .c 29, .c 3, .p pv2 [pv2,pv19,pv35999], .c 5, .c 3,
  .c 149, .c 11, .c 3, .c 5, .c 13, .c 3, .c 19, .c 53, .c 3, .p pv2 [pv2,pv61,pv11213], .c 7,
  .c 3, .c 11, .c 5, .c 3, .c 31, .c 37, .c 3, .c 5, .c 17, .c 3, .c 257,
  .p pv2 [pv2,pv3,pv114001], .c 3, .c 7, .c 19, .c 3, .c 331, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .c 11, .c 3, .c 17, .c 79, .c 3, .c 41, .c 683, .c 3, .p pv2 [pv2,pv7,pv48859], .c 5, .c 3,
  .c 7, .c 31, .c 3, .c 5,
]
private theorem h0166c31 : checkBlock 1367811 128 b0166c31 = true := by
  decide +kernel

def rows0166 : List Row :=
  b0166c00 ++ b0166c01 ++ b0166c02 ++ b0166c03 ++ b0166c04 ++ b0166c05 ++ b0166c06 ++ b0166c07 ++
  b0166c08 ++ b0166c09 ++ b0166c10 ++ b0166c11 ++ b0166c12 ++ b0166c13 ++ b0166c14 ++ b0166c15 ++
  b0166c16 ++ b0166c17 ++ b0166c18 ++ b0166c19 ++ b0166c20 ++ b0166c21 ++ b0166c22 ++ b0166c23 ++
  b0166c24 ++ b0166c25 ++ b0166c26 ++ b0166c27 ++ b0166c28 ++ b0166c29 ++ b0166c30 ++ b0166c31

attribute [local irreducible] checkBlock checkRows checkPrime

theorem checked0166 : checkBlock 1359875 4096 rows0166 = true :=
  checkBlock_append h0166c00 (
    checkBlock_append h0166c01 (
    checkBlock_append h0166c02 (
    checkBlock_append h0166c03 (
    checkBlock_append h0166c04 (
    checkBlock_append h0166c05 (
    checkBlock_append h0166c06 (
    checkBlock_append h0166c07 (
    checkBlock_append h0166c08 (
    checkBlock_append h0166c09 (
    checkBlock_append h0166c10 (
    checkBlock_append h0166c11 (
    checkBlock_append h0166c12 (
    checkBlock_append h0166c13 (
    checkBlock_append h0166c14 (
    checkBlock_append h0166c15 (
    checkBlock_append h0166c16 (
    checkBlock_append h0166c17 (
    checkBlock_append h0166c18 (
    checkBlock_append h0166c19 (
    checkBlock_append h0166c20 (
    checkBlock_append h0166c21 (
    checkBlock_append h0166c22 (
    checkBlock_append h0166c23 (
    checkBlock_append h0166c24 (
    checkBlock_append h0166c25 (
    checkBlock_append h0166c26 (
    checkBlock_append h0166c27 (
    checkBlock_append h0166c28 (
    checkBlock_append h0166c29 (
    checkBlock_append h0166c30 (
    h0166c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
