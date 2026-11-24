/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks00/Block0038
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks00/Block0038.checked0038
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table055

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0038c00 : List Row := [
  .p pv7 [pv2,pv3,pv13,pv307], .c 3, .p pv5 [pv2,pv31,pv5021], .c 5, .c 3, .c 193, .c 7, .c 3,
  .c 5, .c 419, .c 3, .c 17, .p pv5 [pv2,pv3,pv11,pv53,pv89], .c 3, .c 433,
  .p pv19 [pv2,pv3,pv23,pv47], .c 3, .c 11, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv5189], .c 3,
  .c 5, .p pv3 [pv2,pv3,pv7,pv353], .c 3, .c 23, .c 7, .c 3, .c 503, .p pv3 [pv2,pv3,pv51893],
  .c 3, .c 13, .c 5, .c 3, .c 103, .p pv2 [pv2,pv3,pv5,pv97,pv107], .c 3, .c 5, .c 11, .c 3, .c 7,
  .c 101, .c 3, .c 131, .c 13, .c 3, .p pv3 [pv2,pv37,pv263], .c 5, .c 3, .c 11, .c 137, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv17,pv43,pv71], .c 3, .c 89, .c 109, .c 3, .c 239,
  .p pv2 [pv2,pv3,pv73,pv79], .c 3, .c 7, .c 5, .c 3, .c 19, .c 29, .c 3, .c 5, .c 7, .c 3, .c 13,
  .c 11, .c 3, .p pv5 [pv2,pv155723], .c 43, .c 3, .p pv2 [pv2,pv77863], .c 5, .c 3, .c 293,
  .c 59, .c 3, .c 5, .c 13, .c 3, .c 331, .p pv5 [pv2,pv3,pv7,pv103], .c 3, .c 41, .c 7, .c 3,
  .c 67, .c 5, .c 3, .c 23, .c 17, .c 3, .c 5, .c 79, .c 3, .c 181, .c 37, .c 3, .c 7, .c 11,
  .c 3, .c 151, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 61, .c 3, .c 11,
  .p pv23 [pv2,pv3,pv13,pv1997], .c 3, .p pv3 [pv2,pv19471], .p pv3 [pv2,pv3,pv137,pv379], .c 3,
  .c 19, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv31,pv67], .c 3,
]
private theorem h0038c00 : checkBlock 311299 128 b0038c00 = true := by
  decide +kernel

private def b0038c01 : List Row := [
  .c 5, .p pv2 [pv2,pv3,pv7,pv3709], .c 3, .p pv3 [pv2,pv5,pv7789], .c 7, .c 3,
  .p pv5 [pv2,pv155783], .p pv7 [pv2,pv3,pv6491], .c 3, .c 173, .c 5, .c 3, .c 59, .c 19, .c 3,
  .c 5, .c 53, .c 3, .c 7, .c 17, .c 3, .c 11, .c 463, .c 3, .p pv2 [pv2,pv155801], .c 5, .c 3,
  .p pv3 [pv2,pv11,pv3541], .c 317, .c 3, .c 5, .c 67, .c 3, .c 43, .c 13, .c 3, .c 17, .c 281,
  .c 3, .c 7, .c 5, .c 3, .c 179, .c 11, .c 3, .c 5, .c 7, .c 3, .c 37,
  .p pv5 [pv2,pv3,pv11,pv787], .c 3, .c 19, .p pv2 [pv2,pv3,pv127,pv409], .c 3, .c 11, .c 5, .c 3,
  .c 229, .c 227, .c 3, .c 5, .p pv2 [pv2,pv3,pv19,pv1367], .c 3, .p pv3 [pv2,pv5,pv487],
  .p pv2 [pv2,pv3,pv7,pv41,pv181], .c 3, .p pv5 [pv2,pv101,pv1543], .c 7, .c 3, .c 53, .c 5, .c 3,
  .c 353, .c 13, .c 3, .c 5, .c 11, .c 3, .p pv7 [pv2,pv5,pv7,pv61,pv73],
  .p pv7 [pv2,pv3,pv17,pv191], .c 3, .c 7, .c 23, .c 3, .c 41, .c 5, .c 3, .c 11, .c 7, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv31,pv419], .c 3, .c 257, .p pv3 [pv2,pv3,pv23,pv251], .c 3,
  .p pv2 [pv2,pv17,pv53,pv173], .p pv17 [pv2,pv3,pv83,pv313], .c 3, .c 13, .c 5, .c 3, .c 7,
  .c 71, .c 3, .c 5, .c 31, .c 3, .c 19, .c 7, .c 3, .c 139, .c 13, .c 3, .c 73, .c 5, .c 3,
  .c 167, .p pv7 [pv2,pv3,pv5,pv19,pv547], .c 3, .c 5, .c 17, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv157,pv331], .c 3, .p pv5 [pv2,pv11,pv14173], .c 19,
]
private theorem h0038c01 : checkBlock 311555 128 b0038c01 = true := by
  decide +kernel

private def b0038c02 : List Row := [
  .c 3, .c 79, .c 5, .c 3, .c 163, .p pv7 [pv2,pv3,pv5,pv5197], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv51971], .c 3, .c 13, .c 199, .c 3, .c 29, .c 11, .c 3, .c 7, .c 5, .c 3,
  .c 109, .c 197, .c 3, .c 5, .c 7, .c 3, .c 11, .c 181, .c 3, .p pv5 [pv2,pv19,pv29,pv283],
  .p pv7 [pv2,pv3,pv8663], .c 3, .c 37, .c 5, .c 3, .c 43, .p pv13 [pv2,pv3,pv5,pv23,pv113], .c 3,
  .c 5, .c 41, .c 3, .c 31, .c 61, .c 3, .p pv3 [pv2,pv13,pv2999], .c 7, .c 3, .c 23, .c 5, .c 3,
  .c 13, .c 131, .c 3, .c 5, .c 379, .c 3, .c 271, .c 19, .c 3, .c 7, .c 73, .c 3, .c 17, .c 5,
  .c 3, .c 47, .c 7, .c 3, .c 5, .c 37, .c 3, .p pv19 [pv2,pv5,pv17,pv367], .c 29, .c 3,
  .p pv2 [pv2,pv167,pv467], .c 157, .c 3, .p pv2 [pv2,pv7,pv22283], .c 5, .c 3, .c 7, .c 11, .c 3,
  .c 5, .c 223, .c 3, .p pv2 [pv2,pv5,pv19,pv821], .c 7, .c 3, .c 13, .c 101, .c 3, .c 11, .c 5,
  .c 3, .c 19, .c 17, .c 3, .c 5, .p pv3 [pv2,pv3,pv149,pv349], .c 3, .c 7, .c 13, .c 3, .c 509,
  .c 67, .c 3, .p pv5 [pv2,pv156011], .c 5, .c 3, .p pv2 [pv2,pv78007],
  .p pv3 [pv2,pv3,pv5,pv3467], .c 3, .c 5, .c 11, .c 3, .c 23, .p pv3 [pv2,pv3,pv131,pv397], .c 3,
  .p pv5 [pv2,pv7,pv31,pv719], .c 97, .c 3, .c 7, .c 5, .c 3, .c 11, .c 313, .c 3, .c 5,
]
private theorem h0038c02 : checkBlock 311811 128 b0038c02 = true := by
  decide +kernel

private def b0038c03 : List Row := [
  .c 7, .c 3, .p pv7 [pv2,pv5,pv11,pv2837], .p pv7 [pv2,pv3,pv13003], .c 3, .c 31, .c 521, .c 3,
  .p pv2 [pv2,pv156041], .c 5, .c 3, .p pv3 [pv2,pv7,pv5573], .c 13, .c 3, .c 5, .c 461, .c 3,
  .p pv2 [pv2,pv5,pv3121], .c 11, .c 3, .p pv2 [pv2,pv113,pv1381], .c 7, .c 3, .c 19, .c 5, .c 3,
  .c 107, .p pv7 [pv2,pv3,pv5,pv17], .c 3, .c 5, .c 29, .c 3, .c 457, .c 23, .c 3, .c 7, .c 31,
  .c 3, .c 13, .c 5, .c 3, .c 283, .c 7, .c 3, .c 5, .c 541, .c 3, .p pv3 [pv2,pv5,pv1951], .c 83,
  .c 3, .c 487, .c 11, .c 3, .c 131, .c 5, .c 3, .c 7, .c 263, .c 3, .c 5, .c 71, .c 3, .c 11,
  .c 7, .c 3, .p pv2 [pv2,pv78049], .p pv3 [pv2,pv3,pv61,pv853], .c 3,
  .p pv2 [pv2,pv11,pv23,pv617], .c 5, .c 3, .p pv3 [pv2,pv13,pv19,pv79],
  .p pv11 [pv2,pv3,pv5,pv3469], .c 3, .c 5, .p pv5 [pv2,pv3,pv13009], .c 3, .c 7, .c 43, .c 3,
  .c 19, .p pv2 [pv2,pv3,pv7,pv59], .c 3, .p pv3 [pv2,pv31,pv1259], .c 5, .c 3, .c 17,
  .p pv7 [pv2,pv3,pv5,pv1301], .c 3, .c 5, .c 13, .c 3, .p pv7 [pv2,pv5,pv1249],
  .p pv2 [pv2,pv3,pv26021], .c 3, .c 11, .c 61, .c 3, .c 7, .c 5, .c 3,
  .p pv7 [pv2,pv11,pv47,pv151], .c 23, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv37,pv211],
  .p pv2 [pv2,pv3,pv5783], .c 3, .c 59, .p pv29 [pv2,pv3,pv3253], .c 3, .c 127, .c 5, .c 3, .c 13,
  .c 11, .c 3, .c 5, .c 17, .c 3, .p pv29 [pv2,pv5,pv31231], .p pv5 [pv2,pv3,pv7,pv11,pv13], .c 3,
  .c 23, .c 7, .c 3,
]
private theorem h0038c03 : checkBlock 312067 128 b0038c03 = true := by
  decide +kernel

private def b0038c04 : List Row := [
  .c 11, .c 5, .c 3, .c 53, .p pv13 [pv2,pv3,pv5,pv29,pv359], .c 3, .c 5, .c 547, .c 3, .c 17,
  .p pv5 [pv2,pv3,pv52057], .c 3, .c 7, .p pv31 [pv2,pv3,pv26029], .c 3, .p pv3 [pv2,pv43,pv227],
  .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv31237], .c 239, .c 3, .c 13,
  .c 19, .c 3, .p pv5 [pv2,pv7,pv53,pv421], .c 5, .c 3, .c 7, .c 37, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv7,pv3719], .c 3, .p pv3 [pv2,pv5,pv11,pv71], .c 7, .c 3,
  .p pv5 [pv2,pv181,pv863], .c 17, .c 3, .p pv2 [pv2,pv83,pv941], .c 5, .c 3, .c 151, .c 67, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv17,pv1021], .c 3, .c 7, .c 11, .c 3, .c 97, .c 397, .c 3, .c 17, .c 5,
  .c 3, .c 31, .p pv2 [pv2,pv3,pv5,pv2083], .c 3, .c 5, .c 167, .c 3, .c 41, .c 271, .c 3, .c 193,
  .p pv2 [pv2,pv3,pv13,pv2003], .c 3, .c 7, .c 5, .c 3, .c 89, .c 13, .c 3, .c 5, .c 7, .c 3,
  .c 211, .c 19, .c 3, .c 137, .c 11, .c 3, .c 47, .c 5, .c 3, .p pv2 [pv2,pv7,pv11161], .c 17,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv8681], .c 3, .c 11, .c 59, .c 3, .p pv5 [pv2,pv307,pv509], .c 7,
  .c 3, .c 13, .c 5, .c 3, .c 37, .c 53, .c 3, .c 5, .c 23, .c 3, .p pv17 [pv2,pv5,pv7,pv19,pv47],
  .p pv7 [pv2,pv3,pv1447], .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv17,pv29,pv317], .c 5, .c 3,
  .c 19, .c 7, .c 3, .c 5, .c 241,
]
private theorem h0038c04 : checkBlock 312323 128 b0038c04 = true := by
  decide +kernel

private def b0038c05 : List Row := [
  .c 3, .p pv3 [pv2,pv5,pv15629], .p pv13 [pv2,pv3,pv59,pv883], .c 3, .c 11,
  .p pv11 [pv2,pv3,pv19,pv457], .c 3, .c 23, .c 5, .c 3, .c 7, .p pv19 [pv2,pv3,pv5,pv521], .c 3,
  .c 5, .c 19, .c 3, .c 13, .c 7, .c 3, .p pv3 [pv2,pv23,pv1699], .p pv2 [pv2,pv3,pv52103], .c 3,
  .p pv5 [pv2,pv67,pv2333], .c 5, .c 3, .c 199, .c 11, .c 3, .c 5, .c 13, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv11,pv1579], .c 3, .c 17, .c 29, .c 3, .c 11, .c 5, .c 3, .c 73, .c 83, .c 3,
  .c 5, .c 191, .c 3, .c 113, .p pv37 [pv2,pv3,pv3257], .c 3, .p pv2 [pv2,pv7,pv13,pv859],
  .p pv11 [pv2,pv3,pv29,pv599], .c 3, .c 7, .c 5, .c 3, .c 13, .c 47, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv53,pv59], .p pv17 [pv2,pv3,pv13,pv19,pv211], .c 3, .c 29,
  .p pv7 [pv2,pv3,pv11,pv23,pv103], .c 3, .c 179, .c 5, .c 3, .c 11, .c 19, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv52121], .c 3, .c 23, .c 277, .c 3, .p pv3 [pv2,pv29,pv337], .c 7, .c 3,
  .p pv5 [pv2,pv156371], .c 5, .c 3, .c 17, .c 149, .c 3, .c 5, .p pv2 [pv2,pv3,pv67,pv389], .c 3,
  .c 37, .c 11, .c 3, .c 7, .c 257, .c 3, .p pv2 [pv2,pv78193], .c 5, .c 3,
  .p pv2 [pv2,pv19,pv8231], .c 7, .c 3, .c 5, .c 479, .c 3, .c 167, .c 13, .c 3, .c 19,
  .p pv3 [pv2,pv3,pv37,pv1409], .c 3, .c 421, .c 5, .c 3, .c 7, .c 103, .c 3, .c 5, .c 17, .c 3,
  .c 31, .c 7, .c 3, .c 83, .c 11, .c 3, .c 307,
]
private theorem h0038c05 : checkBlock 312579 128 b0038c05 = true := by
  decide +kernel

private def b0038c06 : List Row := [
  .c 5, .c 3, .p pv7 [pv2,pv156419], .p pv29 [pv2,pv3,pv5,pv11,pv79], .c 3, .c 5, .c 269, .c 3,
  .c 7, .c 193, .c 3, .p pv3 [pv2,pv39107], .c 53, .c 3, .p pv5 [pv2,pv11,pv14221], .c 5, .c 3,
  .c 23, .c 13, .c 3, .c 5, .c 59, .c 3, .c 29, .c 31, .c 3, .p pv5 [pv2,pv7,pv22349], .c 139,
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv101,pv1549], .c 157, .c 3, .c 5, .c 7, .c 3, .c 19,
  .c 211, .c 3, .c 11, .c 17, .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv7,pv11,pv127],
  .p pv3 [pv2,pv3,pv5,pv19,pv61], .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv17,pv59], .c 3,
  .p pv2 [pv2,pv5,pv15647], .p pv3 [pv2,pv3,pv7,pv7451], .c 3, .c 373, .c 7, .c 3, .c 17, .c 5,
  .c 3, .c 131, .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv17387], .c 3,
  .p pv2 [pv2,pv5,pv7,pv17,pv263], .c 47, .c 3, .c 7, .p pv2 [pv2,pv3,pv52163], .c 3, .c 11, .c 5,
  .c 3, .p pv2 [pv2,pv13,pv463], .c 7, .c 3, .c 5, .c 29, .c 3, .c 13, .p pv2 [pv2,pv3,pv17389],
  .c 3, .c 23, .p pv17 [pv2,pv3,pv6521], .c 3, .c 89, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 11,
  .c 3, .p pv11 [pv2,pv5,pv23,pv1361], .c 7, .c 3, .p pv2 [pv2,pv78259], .c 71, .c 3, .c 229,
  .c 5, .c 3, .c 11, .c 367, .c 3, .c 5, .c 37, .c 3, .c 7, .c 19, .c 3, .c 47, .c 31, .c 3,
  .c 337, .c 5, .c 3, .c 13, .p pv11 [pv2,pv3,pv5,pv2609], .c 3, .c 5, .p pv5 [pv2,pv3,pv52181],
  .c 3,
]
private theorem h0038c06 : checkBlock 312835 128 b0038c06 = true := by
  decide +kernel

private def b0038c07 : List Row := [
  .c 67, .c 11, .c 3, .c 73, .c 23, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv78277], .c 353, .c 3,
  .c 5, .c 7, .c 3, .c 521, .c 17, .c 3, .p pv5 [pv2,pv11,pv43,pv331], .p pv7 [pv2,pv3,pv4349],
  .c 3, .p pv2 [pv2,pv78283], .c 5, .c 3, .c 19, .c 487, .c 3, .c 5, .p pv2 [pv2,pv3,pv1933],
  .c 3, .p pv13 [pv2,pv5,pv6263], .p pv19 [pv2,pv3,pv7,pv233], .c 3, .c 13, .c 7, .c 3,
  .p pv2 [pv2,pv31,pv5051], .c 5, .c 3, .c 43, .c 29, .c 3, .c 5, .c 19, .c 3, .c 11, .c 13, .c 3,
  .c 7, .c 107, .c 3, .c 31, .c 5, .c 3, .c 41, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv52201], .c 3,
  .p pv2 [pv2,pv5,pv31321], .c 97, .c 3, .c 293, .p pv3 [pv2,pv3,pv17401], .c 3, .c 103, .c 5,
  .c 3, .c 7, .c 59, .c 3, .c 5, .c 23, .c 3, .p pv3 [pv2,pv5,pv41,pv191], .c 7, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv13,pv251], .c 3, .c 19, .c 5, .c 3, .c 17, .c 13, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv109,pv479], .c 3, .c 7, .p pv5 [pv2,pv3,pv19,pv229], .c 3, .c 523, .c 37,
  .c 3, .c 23, .c 5, .c 3, .p pv3 [pv2,pv39161], .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv61,pv107],
  .c 3, .p pv2 [pv2,pv5,pv13,pv241], .c 173, .c 3, .p pv5 [pv2,pv7,pv23,pv139], .c 127, .c 3,
  .c 7, .c 5, .c 3, .c 137, .p pv13 [pv2,pv3,pv5,pv7,pv373], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv31333], .p pv2 [pv2,pv3,pv26111], .c 3, .c 431, .c 13, .c 3,
  .p pv5 [pv2,pv156671], .c 5,
]
private theorem h0038c07 : checkBlock 313091 128 b0038c07 = true := by
  decide +kernel

private def b0038c08 : List Row := [
  .c 3, .c 47, .p pv17 [pv2,pv3,pv5,pv2089], .c 3, .c 5, .c 11, .c 3, .c 17, .c 41, .c 3, .c 19,
  .c 7, .c 3, .p pv2 [pv2,pv157,pv499], .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv1741], .c 3,
  .c 5, .p pv2 [pv2,pv3,pv19,pv2749], .c 3, .c 13, .c 79, .c 3, .c 7, .p pv3 [pv2,pv3,pv23,pv757],
  .c 3, .c 29, .c 5, .c 3, .p pv3 [pv2,pv59,pv83], .c 7, .c 3, .c 5, .c 13, .c 3, .c 23, .c 11,
  .c 3, .c 37, .c 17, .c 3, .c 379, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5, .c 307, .c 3, .c 463,
  .c 7, .c 3, .c 331, .c 167, .c 3, .c 17, .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv43], .c 3,
  .c 5, .p pv2 [pv2,pv3,pv151,pv173], .c 3, .c 7, .c 131, .c 3, .c 227, .c 11, .c 3, .c 67, .c 5,
  .c 3, .c 251, .c 37, .c 3, .c 5, .p pv2 [pv2,pv3,pv17417], .c 3, .c 11, .c 23, .c 3,
  .p pv3 [pv2,pv7,pv11197], .c 19, .c 3, .c 7, .c 5, .c 3, .c 157, .c 17, .c 3, .c 5, .c 7, .c 3,
  .c 241, .p pv3 [pv2,pv3,pv17419], .c 3, .c 13, .p pv2 [pv2,pv3,pv17,pv29,pv53], .c 3,
  .p pv3 [pv2,pv19597], .c 5, .c 3, .c 23, .p pv11 [pv2,pv3,pv5,pv13,pv67], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv4751], .c 3, .p pv2 [pv2,pv5,pv31357], .c 13, .c 3, .c 11, .c 7, .c 3,
  .p pv5 [pv2,pv17,pv23,pv401], .c 5, .c 3, .p pv2 [pv2,pv11,pv7127], .c 557, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv31,pv281], .c 3, .c 53,
]
private theorem h0038c08 : checkBlock 313347 128 b0038c08 = true := by
  decide +kernel

private def b0038c09 : List Row := [
  .p pv2 [pv2,pv3,pv52267], .c 3, .c 7, .c 41, .c 3, .p pv2 [pv2,pv13,pv37,pv163], .c 5, .c 3,
  .p pv2 [pv2,pv233,pv673], .c 7, .c 3, .c 5, .c 31, .c 3, .c 47, .c 17, .c 3,
  .p pv2 [pv2,pv89,pv881], .p pv3 [pv2,pv3,pv13,pv4021], .c 3, .c 11, .c 5, .c 3, .c 7, .c 13,
  .c 3, .c 5, .c 83, .c 3, .p pv2 [pv2,pv5,pv15683], .c 7, .c 3, .c 17, .p pv7 [pv2,pv3,pv8713],
  .c 3, .c 181, .c 5, .c 3, .p pv7 [pv2,pv47,pv71], .c 73, .c 3, .c 5, .c 11, .c 3, .c 7, .c 29,
  .c 3, .c 23, .p pv3 [pv2,pv3,pv7,pv11,pv97], .c 3, .c 13, .c 5, .c 3, .c 11,
  .p pv29 [pv2,pv3,pv5,pv10457], .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv2011], .c 3,
  .p pv3 [pv2,pv5,pv11,pv23,pv31], .c 37, .c 3, .p pv7 [pv2,pv7,pv22409], .c 13, .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv103,pv1523], .p pv2 [pv2,pv3,pv5,pv7,pv83], .c 3, .c 5, .c 7, .c 3, .c 29,
  .c 11, .c 3, .c 211, .c 263, .c 3, .p pv2 [pv2,pv59,pv2659], .c 5, .c 3, .c 17, .c 43, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv2179], .c 3, .c 13, .p pv13 [pv2,pv3,pv7,pv31,pv241], .c 3, .c 179,
  .c 7, .c 3, .c 167, .c 5, .c 3, .c 311, .c 113, .c 3, .c 5, .c 13, .c 3, .c 109, .c 31, .c 3,
  .c 7, .c 11, .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv67,pv1171], .c 7, .c 3, .c 5, .c 17, .c 3,
  .c 11, .c 157, .c 3, .c 283, .p pv23 [pv2,pv3,pv1453], .c 3, .p pv2 [pv2,pv7,pv11,pv1019], .c 5,
  .c 3,
]
private theorem h0038c09 : checkBlock 313603 128 b0038c09 = true := by
  decide +kernel

private def b0038c10 : List Row := [
  .c 7, .c 19, .c 3, .c 5, .c 29, .c 3, .c 17, .c 7, .c 3, .c 281, .p pv3 [pv2,pv3,pv52313], .c 3,
  .p pv2 [pv2,pv156941], .c 5, .c 3, .p pv3 [pv2,pv17,pv577], .c 71, .c 3, .c 5,
  .p pv67 [pv2,pv3,pv11,pv29,pv41], .c 3, .c 7, .c 89, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv7,pv37,pv101], .c 3, .c 47, .c 5, .c 3, .c 53, .p pv7 [pv2,pv3,pv5,pv109],
  .c 3, .c 5, .c 23, .c 3, .p pv7 [pv2,pv5,pv31393], .p pv2 [pv2,pv3,pv26161], .c 3, .c 13, .c 17,
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv78487], .c 11, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv47,pv167], .c 13, .c 3, .c 61, .p pv7 [pv2,pv3,pv31,pv211], .c 3, .c 11, .c 5,
  .c 3, .p pv2 [pv2,pv7,pv41,pv547], .p pv7 [pv2,pv3,pv5,pv5233], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv43,pv1217], .c 3, .p pv13 [pv2,pv5,pv17,pv1847], .p pv5 [pv2,pv3,pv7,pv89],
  .c 3, .p pv3 [pv2,pv23,pv3413], .c 7, .c 3, .p pv2 [pv2,pv13,pv929], .c 5, .c 3, .c 101, .c 193,
  .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv7,pv2243], .c 241, .c 3, .c 7, .c 43, .c 3, .c 71,
  .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 103, .c 3, .c 19, .c 509, .c 3, .c 59,
  .p pv11 [pv2,pv3,pv17,pv3079], .c 3, .p pv5 [pv2,pv7,pv22433], .c 5, .c 3, .c 7, .c 127, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv7,pv3739], .c 3, .c 89, .c 7, .c 3, .c 443, .c 19, .c 3, .c 13, .c 5,
  .c 3, .c 29, .c 41, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv4027], .c 3, .c 7,
  .p pv5 [pv2,pv3,pv409],
]
private theorem h0038c10 : checkBlock 313859 128 b0038c10 = true := by
  decide +kernel

private def b0038c11 : List Row := [
  .c 3, .p pv2 [pv2,pv11,pv59], .c 13, .c 3, .c 31, .c 5, .c 3, .p pv3 [pv2,pv29,pv677], .c 53,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv4363], .c 3, .c 137, .c 17, .c 3, .c 317, .c 11, .c 3, .c 7, .c 5,
  .c 3, .p pv23 [pv2,pv13,pv43,pv281], .p pv37 [pv2,pv3,pv5,pv7,pv11,pv17], .c 3, .c 5, .c 7,
  .c 3, .c 11, .p pv2 [pv2,pv3,pv2909], .c 3, .c 17, .c 211, .c 3, .c 41, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv229], .c 379, .c 3, .c 5, .c 13, .c 3, .c 43, .c 19, .c 3, .c 223, .c 7, .c 3,
  .p pv2 [pv2,pv78553], .c 5, .c 3, .p pv2 [pv2,pv157109], .c 199, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv23], .c 3, .c 151, .p pv5 [pv2,pv3,pv13093], .c 3, .c 7,
  .p pv3 [pv2,pv3,pv83,pv631], .c 3, .p pv2 [pv2,pv47,pv3343], .c 5, .c 3, .c 13, .c 7, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv6547], .c 3, .p pv2 [pv2,pv5,pv19,pv827],
  .p pv5 [pv2,pv3,pv13,pv17,pv79], .c 3, .p pv2 [pv2,pv157133], .c 131, .c 3, .c 29, .c 5, .c 3,
  .c 7, .c 11, .c 3, .c 5, .c 43, .c 3, .c 467, .c 7, .c 3, .c 67, .p pv23 [pv2,pv3,pv19,pv919],
  .c 3, .c 11, .c 5, .c 3, .c 31, .c 257, .c 3, .c 5, .c 19, .c 3, .c 7, .c 523, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv7,pv1871], .c 3, .c 61, .c 5, .c 3, .p pv2 [pv2,pv73,pv2153], .c 23, .c 3,
  .c 5, .c 11, .c 3, .p pv7 [pv2,pv5,pv6287], .c 13, .c 3, .p pv2 [pv2,pv7,pv103,pv109],
  .p pv3 [pv2,pv3,pv11,pv433], .c 3, .c 7, .c 5, .c 3, .c 11,
]
private theorem h0038c11 : checkBlock 314115 128 b0038c11 = true := by
  decide +kernel

private def b0038c12 : List Row := [
  .c 31, .c 3, .c 5, .c 7, .c 3, .c 17, .c 47, .c 3, .c 23, .c 29, .c 3, .c 19, .c 5, .c 3,
  .p pv13 [pv2,pv7,pv17,pv1321], .p pv7 [pv2,pv3,pv5,pv131], .c 3, .c 5,
  .p pv13 [pv2,pv3,pv17467], .c 3, .c 59, .c 11, .c 3, .c 229, .c 7, .c 3, .p pv5 [pv2,pv157211],
  .c 5, .c 3, .c 41, .c 13, .c 3, .c 5, .c 89, .c 3, .p pv11 [pv2,pv5,pv7,pv1123], .c 383, .c 3,
  .c 7, .c 17, .c 3, .p pv2 [pv2,pv127,pv619], .c 5, .c 3, .c 43, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv17,pv3083], .c 3, .c 157, .c 107, .c 3, .c 47, .c 11, .c 3, .c 13, .c 5, .c 3,
  .c 7, .p pv3 [pv2,pv3,pv5,pv11,pv953], .c 3, .c 5, .p pv53 [pv2,pv3,pv7,pv13], .c 3, .c 11,
  .c 7, .c 3, .c 19, .c 13, .c 3, .p pv3 [pv2,pv11,pv1787], .c 5, .c 3, .c 367, .c 409, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv19,pv31,pv89], .c 3, .c 7, .c 151, .c 3, .c 37, .c 149, .c 3,
  .p pv5 [pv2,pv157271], .c 5, .c 3, .p pv2 [pv2,pv13,pv23,pv263], .c 17, .c 3, .c 5, .c 31, .c 3,
  .c 13, .c 29, .c 3, .c 11, .p pv7 [pv2,pv3,pv17,pv257], .c 3, .c 7, .c 5, .c 3, .c 127,
  .p pv13 [pv2,pv3,pv5,pv7,pv107], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv163,pv193], .c 41,
  .c 3, .p pv2 [pv2,pv78649], .p pv3 [pv2,pv3,pv52433], .c 3, .p pv2 [pv2,pv17,pv19,pv487], .c 5,
  .c 3, .c 197, .c 11, .c 3, .c 5, .c 23, .c 3, .c 19, .p pv5 [pv2,pv3,pv7,pv11,pv227], .c 3,
]
private theorem h0038c12 : checkBlock 314371 128 b0038c12 = true := by
  decide +kernel

private def b0038c13 : List Row := [
  .p pv2 [pv2,pv13,pv12101], .c 7, .c 3, .c 11, .c 5, .c 3, .c 13,
  .p pv11 [pv2,pv3,pv5,pv19,pv23], .c 3, .c 5, .c 59, .c 3, .p pv7 [pv2,pv5,pv7,pv29,pv31], .c 17,
  .c 3, .c 7, .c 19, .c 3, .c 23, .c 5, .c 3, .c 419, .c 7, .c 3, .c 5, .c 11, .c 3, .c 31,
  .c 109, .c 3, .c 17, .c 137, .c 3, .p pv2 [pv2,pv7,pv11239], .c 5, .c 3, .c 7, .c 389, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv7,pv59,pv127], .c 3, .p pv11 [pv2,pv5,pv11,pv2861], .c 7, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv52453], .c 3, .p pv2 [pv2,pv37,pv4253], .c 5, .c 3, .c 347, .c 491, .c 3,
  .c 5, .c 29, .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv241,pv653], .c 449, .c 3, .c 163, .c 5,
  .c 3, .c 37, .p pv7 [pv2,pv3,pv5,pv43,pv61], .c 3, .c 5, .c 53, .c 3, .p pv2 [pv2,pv5,pv31477],
  .c 19, .c 3, .p pv3 [pv2,pv7,pv11,pv73], .p pv3 [pv2,pv3,pv23,pv2281], .c 3, .c 7, .c 5, .c 3,
  .c 17, .c 433, .c 3, .c 5, .c 7, .c 3, .c 23, .c 43, .c 3, .p pv5 [pv2,pv17,pv47,pv197], .c 11,
  .c 3, .p pv2 [pv2,pv211,pv373], .c 5, .c 3, .c 83, .c 13, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv137,pv383], .c 3, .c 11, .c 37, .c 3, .c 149, .c 7, .c 3, .c 359, .c 5, .c 3,
  .c 19, .p pv2 [pv2,pv3,pv5,pv2099], .c 3, .c 5, .c 17, .c 3, .c 179, .c 461, .c 3, .c 7, .c 499,
  .c 3, .c 13, .c 5, .c 3, .p pv11 [pv2,pv313,pv503], .c 7,
]
private theorem h0038c13 : checkBlock 314627 128 b0038c13 = true := by
  decide +kernel

private def b0038c14 : List Row := [
  .c 3, .c 5, .c 19, .c 3, .c 17, .c 23, .c 3, .c 11, .c 13, .c 3, .p pv5 [pv2,pv7,pv83,pv271],
  .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv23,pv163], .c 3, .c 41, .c 7, .c 3,
  .p pv5 [pv2,pv53,pv2971], .c 31, .c 3, .p pv2 [pv2,pv43,pv1831], .c 5, .c 3, .c 23, .c 11, .c 3,
  .c 5, .c 47, .c 3, .c 7, .p pv13 [pv2,pv3,pv11,pv1193], .c 3, .p pv2 [pv2,pv71,pv1109], .c 17,
  .c 3, .c 11, .c 5, .c 3, .c 29, .c 89, .c 3, .c 5, .c 13, .c 3, .c 37,
  .p pv5 [pv2,pv3,pv19,pv307], .c 3, .c 241, .p pv2 [pv2,pv3,pv26249], .c 3, .c 7, .c 5, .c 3,
  .c 269, .c 19, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv17,pv109], .p pv2 [pv2,pv3,pv26251],
  .c 3, .c 199, .c 101, .c 3, .c 211, .c 5, .c 3, .c 11, .c 23, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv2917], .c 3, .c 47, .c 311, .c 3, .p pv5 [pv2,pv157523], .c 7, .c 3, .c 31,
  .c 5, .c 3, .p pv2 [pv2,pv19,pv8291], .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv52511], .c 3, .c 509,
  .c 11, .c 3, .c 7, .c 163, .c 3, .p pv2 [pv2,pv257,pv613], .c 5, .c 3, .c 487, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv19,pv691], .c 3, .c 67, .p pv5 [pv2,pv3,pv52517], .c 3, .c 13,
  .p pv2 [pv2,pv3,pv8753], .c 3, .c 139, .c 5, .c 3, .c 7, .c 181, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv41,pv61], .c 3, .c 79, .c 7, .c 3, .c 151,
]
private theorem h0038c14 : checkBlock 314883 128 b0038c14 = true := by
  decide +kernel

private def b0038c15 : List Row := [
  .c 11, .c 3, .c 29, .c 5, .c 3, .c 89, .c 83, .c 3, .c 5, .c 113, .c 3, .c 7, .c 17, .c 3,
  .c 41, .c 23, .c 3, .c 271, .c 5, .c 3, .p pv2 [pv2,pv59,pv2671],
  .p pv7 [pv2,pv3,pv5,pv17,pv103], .c 3, .c 5, .c 61, .c 3, .c 19, .p pv5 [pv2,pv3,pv23,pv571],
  .c 3, .c 17, .p pv11 [pv2,pv3,pv13,pv449], .c 3, .c 7, .c 5, .c 3, .c 383, .c 13, .c 3, .c 5,
  .c 7, .c 3, .c 101, .p pv5 [pv2,pv3,pv107,pv491], .c 3, .c 11, .c 19, .c 3, .c 43, .c 5, .c 3,
  .c 31, .c 239, .c 3, .c 5, .p pv5 [pv2,pv3,pv52541], .c 3, .p pv2 [pv2,pv5,pv13,pv97], .c 367,
  .c 3, .p pv3 [pv2,pv157,pv251], .c 7, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv269,pv293], .c 11,
  .c 3, .c 5, .c 37, .c 3, .p pv3 [pv2,pv5,pv7,pv563], .c 103, .c 3, .c 7, .c 13, .c 3, .c 11,
  .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 23, .c 3, .c 71, .p pv5 [pv2,pv3,pv6569], .c 3, .c 29,
  .c 43, .c 3, .c 47, .c 5, .c 3, .c 7, .c 41, .c 3, .c 5, .c 11, .c 3, .c 13, .c 7, .c 3, .c 97,
  .p pv13 [pv2,pv3,pv11,pv2389], .c 3, .c 23, .c 5, .c 3, .c 11, .p pv11 [pv2,pv3,pv5,pv73], .c 3,
  .c 5, .c 13, .c 3, .c 7, .p pv2 [pv2,pv3,pv41,pv641], .c 3, .p pv3 [pv2,pv23,pv857], .c 173,
  .c 3, .c 113, .c 5, .c 3, .p pv2 [pv2,pv37,pv2131], .c 139, .c 3,
]
private theorem h0038c15 : checkBlock 315139 128 b0038c15 = true := by
  decide +kernel

private def b0038c16 : List Row := [
  .c 5, .c 197, .c 3, .c 17, .c 11, .c 3, .p pv5 [pv2,pv7,pv13,pv1733], .p pv11 [pv2,pv3,pv6571],
  .c 3, .c 7, .c 5, .c 3, .c 13, .p pv17 [pv2,pv3,pv5,pv7,pv751], .c 3, .c 5, .c 7, .c 3, .c 61,
  .c 29, .c 3, .p pv2 [pv2,pv11,pv67,pv107], .c 151, .c 3, .c 331, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv43,pv131], .p pv3 [pv2,pv3,pv5,pv701], .c 3, .c 5, .c 19, .c 3,
  .p pv2 [pv2,pv5,pv15773], .c 167, .c 3, .p pv2 [pv2,pv157733], .c 7, .c 3, .c 59, .c 5, .c 3,
  .c 389, .p pv7 [pv2,pv3,pv5,pv11,pv239], .c 3, .c 5, .c 31, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv61,pv431], .c 3, .c 7, .c 37, .c 3, .c 17, .c 5, .c 3, .c 53, .c 7, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv26293], .c 3, .p pv3 [pv2,pv5,pv17,pv29], .c 13, .c 3,
  .p pv5 [pv2,pv79,pv1997], .p pv13 [pv2,pv3,pv13147], .c 3, .c 19, .c 5, .c 3, .c 7, .c 97, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv7,pv11,pv683], .c 3, .p pv11 [pv2,pv5,pv6311], .c 7, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv47,pv373], .c 3, .c 281, .c 5, .c 3, .p pv3 [pv2,pv11,pv163], .c 17, .c 3,
  .c 5, .c 41, .c 3, .c 7, .c 23, .c 3, .c 401, .p pv73 [pv2,pv3,pv7,pv13,pv17], .c 3,
  .p pv3 [pv2,pv103,pv383], .c 5, .c 3, .p pv7 [pv2,pv157799], .c 11, .c 3, .c 5, .c 29, .c 3,
  .c 31, .p pv2 [pv2,pv3,pv11,pv797], .c 3, .p pv3 [pv2,pv7,pv1409], .c 547, .c 3, .c 7, .c 5,
  .c 3, .c 23, .p pv23 [pv2,pv3,pv5,pv7,pv167], .c 3, .c 5, .c 7, .c 3, .c 439,
  .p pv5 [pv2,pv3,pv31,pv1697], .c 3, .c 19, .c 83,
]
private theorem h0038c16 : checkBlock 315395 128 b0038c16 = true := by
  decide +kernel

private def b0038c17 : List Row := [
  .c 3, .c 13, .c 5, .c 3, .c 41, .c 479, .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv31567],
  .c 17, .c 3, .p pv2 [pv2,pv78919], .c 7, .c 3, .c 89, .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv17,pv619], .c 3, .c 5, .p pv11 [pv2,pv3,pv6577], .c 3,
  .p pv2 [pv2,pv5,pv7,pv11,pv41], .p pv5 [pv2,pv3,pv17539], .c 3, .c 7, .c 59, .c 3, .c 491, .c 5,
  .c 3, .c 239, .c 7, .c 3, .c 5, .c 157, .c 3, .c 13, .c 11, .c 3, .c 71,
  .p pv2 [pv2,pv3,pv1949], .c 3, .p pv5 [pv2,pv7,pv19,pv1187], .c 5, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv5,pv421], .c 3, .c 5, .c 13, .c 3, .c 19, .c 7, .c 3, .c 23, .c 337, .c 3,
  .c 109, .c 5, .c 3, .p pv2 [pv2,pv157889], .c 29, .c 3, .c 5, .c 457, .c 3, .c 7, .c 47, .c 3,
  .c 31, .c 11, .c 3, .p pv2 [pv2,pv157901], .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv11,pv29],
  .c 3, .c 5, .c 313, .c 3, .c 11, .c 41, .c 3, .c 53, .p pv2 [pv2,pv3,pv31,pv283], .c 3, .c 7,
  .c 5, .c 3, .c 29, .c 131, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv6317], .c 257, .c 3,
  .p pv3 [pv2,pv19,pv1039], .c 23, .c 3, .c 263, .c 5, .c 3, .c 37, .c 73, .c 3, .c 5, .c 17,
  .c 3, .p pv3 [pv2,pv5,pv53,pv149], .p pv3 [pv2,pv3,pv7,pv23,pv109], .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv151,pv523], .c 5, .c 3, .p pv2 [pv2,pv11,pv83,pv173], .c 103, .c 3, .c 5,
]
private theorem h0038c17 : checkBlock 315651 128 b0038c17 = true := by
  decide +kernel

private def b0038c18 : List Row := [
  .p pv2 [pv2,pv3,pv37,pv1423], .c 3, .c 17, .c 13, .c 3, .c 7, .c 61, .c 3, .c 431, .c 5, .c 3,
  .c 97, .c 7, .c 3, .c 5, .p pv11 [pv2,pv3,pv1097], .c 3, .c 193, .c 37, .c 3, .c 139,
  .p pv2 [pv2,pv3,pv113,pv233], .c 3, .c 11, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv2633], .c 3,
  .c 5, .p pv5 [pv2,pv3,pv7,pv7523], .c 3, .c 107, .c 7, .c 3, .p pv3 [pv2,pv127,pv311], .c 17,
  .c 3, .c 31, .c 5, .c 3, .c 19, .c 13, .c 3, .c 5, .c 11, .c 3, .c 7, .p pv3 [pv2,pv3,pv52667],
  .c 3, .c 43, .c 251, .c 3, .c 17, .c 5, .c 3, .c 11, .c 71, .c 3, .c 5, .c 19, .c 3,
  .p pv19 [pv2,pv5,pv11,pv13,pv17], .p pv5 [pv2,pv3,pv823], .c 3, .p pv5 [pv2,pv7,pv11287], .c 53,
  .c 3, .c 7, .c 5, .c 3, .c 317, .p pv3 [pv2,pv3,pv5,pv7,pv43], .c 3, .c 5, .c 7, .c 3, .c 113,
  .c 11, .c 3, .p pv2 [pv2,pv23,pv6871], .c 13, .c 3, .p pv3 [pv2,pv39509], .c 5, .c 3, .c 79,
  .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv139,pv379], .c 3, .c 37, .c 43, .c 3,
  .p pv3 [pv2,pv11,pv449], .c 7, .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv13,pv6079], .c 283, .c 3,
  .c 5, .c 347, .c 3, .c 13, .c 97, .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv17,pv4649], .c 5, .c 3,
  .p pv2 [pv2,pv31,pv5099], .c 7, .c 3, .c 5, .c 13, .c 3, .c 11, .p pv11 [pv2,pv3,pv4391], .c 3,
  .c 409, .c 467, .c 3,
]
private theorem h0038c18 : checkBlock 315907 128 b0038c18 = true := by
  decide +kernel

private def b0038c19 : List Row := [
  .c 61, .c 5, .c 3, .c 7, .c 421, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv941], .c 3, .c 23, .c 7,
  .c 3, .c 29, .p pv2 [pv2,pv3,pv8783], .c 3, .p pv3 [pv2,pv41,pv241], .c 5, .c 3, .c 13,
  .p pv11 [pv2,pv3,pv5,pv17,pv31], .c 3, .c 5, .c 181, .c 3, .c 7, .p pv5 [pv2,pv3,pv13,pv2027],
  .c 3, .c 11, .p pv2 [pv2,pv3,pv7,pv7529], .c 3, .p pv5 [pv2,pv43,pv3677], .c 5, .c 3, .c 463,
  .c 31, .c 3, .c 5, .c 79, .c 3, .p pv3 [pv2,pv5,pv59,pv67], .p pv5 [pv2,pv3,pv17569], .c 3,
  .c 521, .c 229, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv158129], .c 11, .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv31627], .c 23, .c 3, .c 13, .c 359, .c 3, .c 11, .c 5, .c 3, .c 211,
  .p pv2 [pv2,pv3,pv5,pv13,pv811], .c 3, .c 5, .p pv5 [pv2,pv3,pv23,pv191], .c 3,
  .p pv2 [pv2,pv5,pv3163], .c 13, .c 3, .c 67, .c 7, .c 3, .c 37, .c 5, .c 3, .c 17,
  .p pv13 [pv2,pv3,pv5,pv659], .c 3, .c 5, .c 11, .c 3, .c 19, .c 137, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv11,pv4793], .c 3, .p pv5 [pv2,pv13,pv23], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5,
  .c 47, .c 3, .c 29, .p pv2 [pv2,pv3,pv52727], .c 3, .c 257, .c 19, .c 3,
  .p pv2 [pv2,pv7,pv11299], .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 17, .c 3,
  .p pv11 [pv2,pv5,pv29,pv1091], .c 7, .c 3, .c 41, .c 107, .c 3, .p pv2 [pv2,pv158201], .c 5,
  .c 3, .c 397, .c 23, .c 3, .c 5, .c 31,
]
private theorem h0038c19 : checkBlock 316163 128 b0038c19 = true := by
  decide +kernel

private def b0038c20 : List Row := [
  .c 3, .c 7, .p pv3 [pv2,pv3,pv17579], .c 3, .c 109, .p pv31 [pv2,pv3,pv7,pv3767], .c 3, .c 13,
  .c 5, .c 3, .p pv13 [pv2,pv17,pv41,pv227], .c 67, .c 3, .c 5, .c 71, .c 3, .c 47,
  .p pv23 [pv2,pv3,pv26371], .c 3, .c 23, .c 11, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv61,pv1297],
  .p pv3 [pv2,pv3,pv5,pv7,pv11,pv137], .c 3, .c 5, .c 7, .c 3, .c 11, .c 19, .c 3, .c 191, .c 17,
  .c 3, .p pv2 [pv2,pv11,pv7193], .c 5, .c 3, .p pv2 [pv2,pv7,pv13,pv37,pv47],
  .p pv7 [pv2,pv3,pv5,pv211], .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv29,pv107], .c 3, .c 13, .c 113,
  .c 3, .c 307, .c 7, .c 3, .c 17, .c 5, .c 3, .c 61, .p pv2 [pv2,pv3,pv5,pv3517], .c 3, .c 5,
  .c 13, .c 3, .c 31, .c 349, .c 3, .c 7, .c 23, .c 3, .c 79, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv43,pv409], .c 3, .p pv2 [pv2,pv5,pv31657], .c 89, .c 3,
  .p pv3 [pv2,pv13,pv761], .c 197, .c 3, .p pv5 [pv2,pv7,pv22613], .c 5, .c 3, .c 7, .c 11, .c 3,
  .c 5, .c 19, .c 3, .c 73, .c 7, .c 3, .c 137, .c 37, .c 3, .c 11, .c 5, .c 3, .c 479,
  .p pv2 [pv2,pv3,pv5,pv1759], .c 3, .c 5, .c 131, .c 3, .c 7, .p pv5 [pv2,pv3,pv79,pv167], .c 3,
  .p pv2 [pv2,pv79159], .c 47, .c 3, .c 41, .c 5, .c 3, .p pv3 [pv2,pv39581], .c 29, .c 3, .c 5,
  .c 11, .c 3, .p pv2 [pv2,pv5,pv71,pv223], .p pv3 [pv2,pv3,pv89,pv593], .c 3, .c 13, .c 157,
  .c 3, .c 7,
]
private theorem h0038c20 : checkBlock 316419 128 b0038c20 = true := by
  decide +kernel

private def b0038c21 : List Row := [
  .c 5, .c 3, .c 11, .p pv37 [pv2,pv3,pv5,pv7,pv13,pv29], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv11,pv2879], .c 13, .c 3, .p pv3 [pv2,pv31,pv1277], .p pv13 [pv2,pv3,pv52783],
  .c 3, .p pv5 [pv2,pv158351], .c 5, .c 3, .c 29, .c 19, .c 3, .c 5, .p pv5 [pv2,pv3,pv26393],
  .c 3, .c 367, .c 11, .c 3, .c 17, .c 7, .c 3, .c 23, .c 5, .c 3, .c 113, .c 383, .c 3, .c 5,
  .c 73, .c 3, .c 89, .p pv5 [pv2,pv3,pv6599], .c 3, .c 7, .p pv7 [pv2,pv3,pv13,pv31,pv131], .c 3,
  .c 173, .c 5, .c 3, .p pv3 [pv2,pv19,pv521], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv67,pv197],
  .c 3, .c 43, .p pv3 [pv2,pv3,pv17599], .c 3, .c 19, .c 11, .c 3, .p pv3 [pv2,pv7,pv5657], .c 5,
  .c 3, .c 7, .p pv31 [pv2,pv3,pv5,pv11], .c 3, .c 5, .c 41, .c 3, .c 11, .c 7, .c 3,
  .p pv3 [pv2,pv19801], .p pv17 [pv2,pv3,pv5867], .c 3, .c 13, .c 5, .c 3, .c 17, .c 37, .c 3,
  .c 5, .c 101, .c 3, .c 7, .c 67, .c 3, .p pv13 [pv2,pv17,pv9319], .c 13, .c 3,
  .p pv2 [pv2,pv113,pv701], .c 5, .c 3, .p pv2 [pv2,pv158429], .p pv2 [pv2,pv3,pv5,pv5281], .c 3,
  .c 5, .c 43, .c 3, .c 23, .c 71, .c 3, .c 11, .p pv3 [pv2,pv3,pv52813], .c 3, .c 7, .c 5, .c 3,
  .c 41, .p pv2 [pv2,pv3,pv5,pv7,pv503], .c 3, .c 5, .c 7, .c 3, .c 13, .p pv5 [pv2,pv3,pv52817],
  .c 3, .p pv2 [pv2,pv193,pv821], .c 311, .c 3, .c 31, .c 5, .c 3, .p pv7 [pv2,pv7,pv22637],
  .c 11, .c 3, .c 5, .c 13, .c 3,
]
private theorem h0038c21 : checkBlock 316675 128 b0038c21 = true := by
  decide +kernel

private def b0038c22 : List Row := [
  .c 17, .c 557, .c 3, .p pv3 [pv2,pv173,pv229], .c 7, .c 3, .c 11, .c 5, .c 3, .c 151,
  .p pv3 [pv2,pv3,pv5,pv2113], .c 3, .c 5, .p pv5 [pv2,pv3,pv61,pv433], .c 3,
  .p pv3 [pv2,pv5,pv7,pv283], .c 23, .c 3, .c 7, .c 563, .c 3, .c 197, .c 5, .c 3, .c 13, .c 7,
  .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv31699], .c 53, .c 3, .c 359, .c 17, .c 3,
  .p pv5 [pv2,pv7,pv22643], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv10567], .c 3, .c 5, .c 61,
  .c 3, .p pv2 [pv2,pv5,pv11,pv131], .c 7, .c 3, .c 79, .p pv2 [pv2,pv3,pv29,pv911], .c 3, .c 17,
  .c 5, .c 3, .c 43, .c 107, .c 3, .c 5, .p pv3 [pv2,pv3,pv53,pv997], .c 3, .c 7, .c 11, .c 3,
  .c 13, .c 139, .c 3, .p pv5 [pv2,pv47,pv3373], .c 5, .c 3, .c 313,
  .p pv3 [pv2,pv3,pv5,pv13,pv271], .c 3, .c 5, .p pv5 [pv2,pv3,pv26423], .c 3, .c 109, .c 13,
  .c 3, .p pv7 [pv2,pv7,pv11,pv29,pv71], .p pv17 [pv2,pv3,pv367], .c 3, .c 7, .c 5, .c 3, .c 31,
  .c 17, .c 3, .c 5, .c 7, .c 3, .c 67, .c 233, .c 3, .c 337, .c 11, .c 3,
  .p pv2 [pv2,pv13,pv12197], .c 5, .c 3, .c 19, .c 307, .c 3, .c 5, .c 103, .c 3, .c 11, .c 83,
  .c 3, .c 23, .c 7, .c 3, .c 239, .c 5, .c 3, .p pv13 [pv2,pv347,pv457], .c 13, .c 3, .c 5,
  .c 19, .c 3, .p pv19 [pv2,pv5,pv7,pv23,pv197], .c 29, .c 3, .c 7, .p pv3 [pv2,pv3,pv67,pv263],
  .c 3, .c 419, .c 5,
]
private theorem h0038c22 : checkBlock 316931 128 b0038c22 = true := by
  decide +kernel

private def b0038c23 : List Row := [
  .c 3, .p pv2 [pv2,pv179,pv443], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv89], .c 3, .c 37,
  .c 17, .c 3, .c 11, .p pv11 [pv2,pv3,pv13217], .c 3, .c 13, .c 5, .c 3, .c 7, .c 149, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv7,pv13,pv83], .c 3, .c 29, .c 7, .c 3, .c 17, .c 13, .c 3, .c 19, .c 5,
  .c 3, .c 281, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv13219], .c 3, .c 7,
  .p pv3 [pv2,pv3,pv11,pv19,pv23], .c 3, .p pv2 [pv2,pv158633], .p pv2 [pv2,pv3,pv7,pv1259], .c 3,
  .c 11, .c 5, .c 3, .p pv7 [pv2,pv13,pv12203], .c 19, .c 3, .c 5, .c 97, .c 3, .c 13, .c 181,
  .c 3, .c 43, .c 41, .c 3, .c 7, .c 5, .c 3, .c 83, .c 53, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv7933], .p pv2 [pv2,pv3,pv17,pv61], .c 3, .p pv5 [pv2,pv158663], .c 223, .c 3,
  .p pv2 [pv2,pv79333], .c 5, .c 3, .c 11, .c 271, .c 3, .c 5, .c 29, .c 3,
  .p pv17 [pv2,pv5,pv11,pv577], .p pv5 [pv2,pv3,pv7,pv1889], .c 3, .c 19, .c 7, .c 3,
  .p pv2 [pv2,pv107,pv1483], .c 5, .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv71,pv149], .c 3, .c 5,
  .c 23, .c 3, .c 41, .c 11, .c 3, .c 7, .c 433, .c 3, .c 503, .c 5, .c 3, .p pv11 [pv2,pv158699],
  .c 7, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv31741], .c 131, .c 3, .c 53,
  .p pv3 [pv2,pv3,pv52903], .c 3, .c 23, .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv3527], .c 3,
  .c 5, .p pv37 [pv2,pv3,pv7,pv3779], .c 3, .c 17,
]
private theorem h0038c23 : checkBlock 317187 128 b0038c23 = true := by
  decide +kernel

private def b0038c24 : List Row := [
  .c 7, .c 3, .c 13, .c 11, .c 3, .p pv2 [pv2,pv19,pv4177], .c 5, .c 3, .p pv2 [pv2,pv17,pv9337],
  .c 523, .c 3, .c 5, .c 167, .c 3, .c 7, .c 13, .c 3, .c 73, .c 59, .c 3,
  .p pv2 [pv2,pv11,pv14431], .c 5, .c 3, .p pv3 [pv2,pv19843], .p pv3 [pv2,pv3,pv5,pv19,pv557],
  .c 3, .c 5, .c 37, .c 3, .c 79, .p pv3 [pv2,pv3,pv31,pv569], .c 3, .c 383, .c 17, .c 3, .c 7,
  .c 5, .c 3, .c 149, .c 29, .c 3, .c 5, .c 7, .c 3, .c 311, .c 31, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv13,pv23,pv59], .c 3, .c 17, .c 5, .c 3, .c 103, .c 13, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv8821], .c 3, .c 23, .p pv2 [pv2,pv3,pv7,pv7561], .c 3, .c 541, .c 7, .c 3,
  .c 227, .c 5, .c 3, .c 29, .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv41,pv1291], .c 3,
  .p pv7 [pv2,pv5,pv7,pv13,pv349], .p pv5 [pv2,pv3,pv11,pv401], .c 3, .c 7,
  .p pv3 [pv2,pv3,pv43,pv1231], .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv29,pv37], .c 7, .c 3, .c 5,
  .p pv17 [pv2,pv3,pv13,pv509], .c 3, .p pv3 [pv2,pv5,pv15881], .c 19, .c 3, .c 41, .c 13, .c 3,
  .c 191, .c 5, .c 3, .c 7, .c 43, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv6353], .c 7, .c 3,
  .c 31, .c 79, .c 3, .p pv5 [pv2,pv17,pv9343], .c 5, .c 3, .c 11, .p pv31 [pv2,pv3,pv5,pv10589],
  .c 3, .c 5, .c 491, .c 3, .c 7, .c 107, .c 3, .c 163, .c 269, .c 3, .p pv2 [pv2,pv79423], .c 5,
  .c 3,
]
private theorem h0038c24 : checkBlock 317443 128 b0038c24 = true := by
  decide +kernel

private def b0038c25 : List Row := [
  .c 19, .p pv2 [pv2,pv3,pv5,pv353], .c 3, .c 5, .c 13, .c 3, .p pv7 [pv2,pv5,pv31771], .c 11,
  .c 3, .p pv2 [pv2,pv7,pv1621], .c 31, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv9929],
  .p pv2 [pv2,pv3,pv5,pv7,pv17,pv89], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv15887],
  .p pv5 [pv2,pv3,pv52957], .c 3, .c 17, .c 61, .c 3, .c 29, .c 5, .c 3, .c 13, .c 197, .c 3,
  .c 5, .c 47, .c 3, .p pv2 [pv2,pv5,pv43,pv739], .p pv5 [pv2,pv3,pv7,pv13,pv97], .c 3,
  .p pv3 [pv2,pv19861], .c 7, .c 3, .p pv5 [pv2,pv29,pv5479], .c 5, .c 3,
  .p pv2 [pv2,pv53,pv1499], .c 23, .c 3, .c 5, .p pv2 [pv2,pv3,pv71,pv373], .c 3, .c 11, .c 199,
  .c 3, .c 7, .c 283, .c 3, .c 19, .c 5, .c 3, .c 89, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv17657],
  .c 3, .p pv31 [pv2,pv5,pv37,pv859], .c 59, .c 3, .c 13, .p pv11 [pv2,pv3,pv52973], .c 3, .c 31,
  .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .p pv13 [pv2,pv3,pv7,pv11,pv43], .c 3, .c 47, .c 7, .c 3,
  .c 11, .c 29, .c 3, .c 41, .c 5, .c 3, .c 241, .c 127, .c 3, .c 5, .p pv3 [pv2,pv3,pv52981],
  .c 3, .c 7, .c 139, .c 3, .c 107, .c 43, .c 3, .p pv5 [pv2,pv13,pv12227], .c 5, .c 3, .c 257,
  .c 11, .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv1987], .p pv2 [pv2,pv3,pv11,pv4817], .c 3,
  .c 19, .c 23, .c 3, .c 7, .c 5, .c 3, .c 349, .c 13, .c 3, .c 5, .c 7, .c 3, .c 17, .c 109,
]
private theorem h0038c25 : checkBlock 317699 128 b0038c25 = true := by
  decide +kernel

private def b0038c26 : List Row := [
  .c 3, .p pv2 [pv2,pv29,pv2741], .p pv3 [pv2,pv3,pv197,pv269], .c 3, .p pv2 [pv2,pv158981], .c 5,
  .c 3, .p pv3 [pv2,pv7,pv17,pv167], .p pv2 [pv2,pv3,pv5,pv3533], .c 3, .c 5, .c 11, .c 3, .c 379,
  .p pv3 [pv2,pv3,pv7,pv67,pv113], .c 3, .p pv2 [pv2,pv158993], .c 7, .c 3, .c 13, .c 5, .c 3,
  .c 11, .p pv13 [pv2,pv3,pv5,pv53], .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv151], .c 3, .c 487,
  .c 163, .c 3, .c 7, .c 13, .c 3, .p pv19 [pv2,pv19,pv8369], .c 5, .c 3, .c 31, .c 7, .c 3, .c 5,
  .c 41, .c 3, .c 19, .c 11, .c 3, .c 557, .c 47, .c 3, .c 17, .c 5, .c 3, .c 7, .c 73, .c 3,
  .c 5, .c 23, .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv11,pv7229], .c 19, .c 3, .c 179, .c 5, .c 3,
  .c 37, .c 31, .c 3, .c 5, .c 13, .c 3, .c 7, .p pv3 [pv2,pv3,pv53017], .c 3,
  .p pv2 [pv2,pv53,pv3001], .c 11, .c 3, .c 23, .c 5, .c 3, .c 41, .c 17, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv37,pv1433], .c 3, .c 11, .c 79, .c 3, .p pv3 [pv2,pv7,pv13,pv19,pv23], .c 83,
  .c 3, .c 7, .c 5, .c 3, .c 13, .c 71, .c 3, .c 5, .c 7, .c 3, .p pv11 [pv2,pv5,pv41,pv97],
  .c 37, .c 3, .c 103, .c 373, .c 3, .p pv2 [pv2,pv17,pv4679], .c 5, .c 3,
  .p pv7 [pv2,pv7,pv22727], .p pv2 [pv2,pv3,pv5,pv5303], .c 3, .c 5, .c 59, .c 3,
  .p pv11 [pv2,pv5,pv47,pv677], .c 19, .c 3, .c 11, .c 7, .c 3, .p pv2 [pv2,pv389,pv409], .c 5,
  .c 3, .p pv3 [pv2,pv11,pv113],
]
private theorem h0038c26 : checkBlock 317955 128 b0038c26 = true := by
  decide +kernel

private def b0038c27 : List Row := [
  .p pv3 [pv2,pv3,pv5,pv10607], .c 3, .c 5, .c 29, .c 3, .c 223, .c 17, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv23,pv1153], .c 3, .p pv3 [pv2,pv39779], .c 5, .c 3, .c 157, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv29,pv31,pv59], .c 3, .c 23, .c 13, .c 3, .c 17, .p pv2 [pv2,pv3,pv17681],
  .c 3, .c 11, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv103], .c 3, .c 5, .c 31, .c 3,
  .p pv3 [pv2,pv5,pv73,pv109], .c 7, .c 3, .p pv5 [pv2,pv43,pv3701], .p pv23 [pv2,pv3,pv19,pv349],
  .c 3, .c 71, .c 5, .c 3, .p pv2 [pv2,pv61,pv2609], .p pv2 [pv2,pv3,pv5,pv1061], .c 3, .c 5,
  .c 11, .c 3, .c 7, .p pv5 [pv2,pv3,pv4421], .c 3, .c 67, .p pv3 [pv2,pv3,pv7,pv11,pv13,pv53],
  .c 3, .p pv2 [pv2,pv159161], .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv829], .c 3,
  .c 449, .c 23, .c 3, .p pv5 [pv2,pv7,pv22739], .p pv2 [pv2,pv3,pv37,pv239], .c 3, .c 7, .c 5,
  .c 3, .c 17, .c 241, .c 3, .c 5, .c 7, .c 3, .c 53, .c 11, .c 3, .p pv3 [pv2,pv17,pv2341],
  .c 181, .c 3, .c 13, .c 5, .c 3, .c 23, .c 29, .c 3, .c 5, .c 191, .c 3, .c 31,
  .p pv2 [pv2,pv3,pv7,pv19], .c 3, .p pv5 [pv2,pv11,pv41,pv353], .c 7, .c 3, .c 149, .c 5, .c 3,
  .p pv2 [pv2,pv159209], .c 19, .c 3, .c 5, .c 17, .c 3, .p pv7 [pv2,pv5,pv7,pv4549], .c 359,
  .c 3, .c 7, .c 11, .c 3, .p pv5 [pv2,pv89,pv1789], .c 5, .c 3, .c 29, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv4423], .c 3, .c 11, .c 31, .c 3,
]
private theorem h0038c27 : checkBlock 318211 128 b0038c27 = true := by
  decide +kernel

private def b0038c28 : List Row := [
  .p pv2 [pv2,pv159233], .c 167, .c 3, .p pv17 [pv2,pv7,pv11,pv47], .c 5, .c 3, .c 7, .c 23, .c 3,
  .c 5, .c 13, .c 3, .c 293, .c 7, .c 3, .c 19, .c 73, .c 3, .p pv5 [pv2,pv163,pv977], .c 5, .c 3,
  .c 431, .c 233, .c 3, .c 5, .c 443, .c 3, .c 7, .p pv5 [pv2,pv3,pv53087], .c 3, .c 11, .c 17,
  .c 3, .c 37, .c 5, .c 3, .c 13, .c 59, .c 3, .c 5, .c 113, .c 3, .c 461, .c 157, .c 3,
  .p pv2 [pv2,pv7,pv31,pv367], .p pv3 [pv2,pv3,pv53093], .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv39821], .c 11, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv17,pv937], .c 53, .c 3,
  .c 31, .p pv2 [pv2,pv3,pv139,pv191], .c 3, .c 11, .c 5, .c 3, .c 199,
  .p pv23 [pv2,pv3,pv5,pv59], .c 3, .c 5, .c 37, .c 3, .c 19, .c 47, .c 3, .c 13, .c 7, .c 3,
  .c 29, .c 5, .c 3, .p pv2 [pv2,pv79657], .c 17, .c 3, .c 5, .c 11, .c 3,
  .p pv3 [pv2,pv5,pv7,pv569], .c 13, .c 3, .c 7, .c 19, .c 3, .p pv2 [pv2,pv29,pv41,pv67], .c 5,
  .c 3, .c 11, .c 7, .c 3, .c 5, .c 223, .c 3, .p pv13 [pv2,pv5,pv11,pv2897], .c 43, .c 3,
  .p pv2 [pv2,pv79669], .p pv11 [pv2,pv3,pv53113], .c 3, .p pv2 [pv2,pv7,pv13,pv17,pv103], .c 5,
  .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv3541], .c 3, .c 5, .c 421, .c 3, .p pv2 [pv2,pv5,pv3187],
  .c 7, .c 3, .c 47, .c 89, .c 3, .p pv3 [pv2,pv39839], .c 5, .c 3, .c 67, .c 13,
]
private theorem h0038c28 : checkBlock 318467 128 b0038c28 = true := by
  decide +kernel

private def b0038c29 : List Row := [
  .c 3, .c 5, .c 139, .c 3, .c 7, .c 17, .c 3, .p pv3 [pv2,pv11,pv1811], .c 29, .c 3,
  .p pv5 [pv2,pv31,pv53,pv97], .c 5, .c 3, .p pv2 [pv2,pv79687], .p pv3 [pv2,pv3,pv5,pv17], .c 3,
  .c 5, .c 23, .c 3, .c 151, .c 19, .c 3, .c 17, .c 11, .c 3, .c 7, .c 5, .c 3, .c 191,
  .p pv41 [pv2,pv3,pv5,pv7,pv11,pv23], .c 3, .c 5, .c 7, .c 3, .c 11, .p pv7 [pv2,pv3,pv37,pv359],
  .c 3, .c 29, .c 13, .c 3, .c 23, .c 5, .c 3, .p pv3 [pv2,pv7,pv5693],
  .p pv2 [pv2,pv3,pv5,pv10627], .c 3, .c 5, .p pv5 [pv2,pv3,pv41], .c 3, .c 211,
  .p pv5 [pv2,pv3,pv7,pv7591], .c 3, .c 277, .c 7, .c 3, .p pv3 [pv2,pv19927], .c 5, .c 3, .c 19,
  .p pv7 [pv2,pv3,pv5,pv2657], .c 3, .c 5, .c 61, .c 3, .c 13, .c 67, .c 3, .c 7, .c 419, .c 3,
  .p pv5 [pv2,pv159431], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 13, .c 3,
  .p pv3 [pv2,pv5,pv1993], .p pv3 [pv2,pv3,pv53147], .c 3, .c 89, .p pv11 [pv2,pv3,pv43,pv103],
  .c 3, .c 347, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv2531], .c 3,
  .p pv13 [pv2,pv5,pv31891], .c 7, .c 3, .p pv2 [pv2,pv13,pv6133], .p pv19 [pv2,pv3,pv23,pv2311],
  .c 3, .c 11, .c 5, .c 3, .c 13, .c 43, .c 3, .c 5, .c 17, .c 3, .c 7, .c 197, .c 3, .c 313,
  .p pv2 [pv2,pv3,pv7,pv3797], .c 3, .c 19, .c 5, .c 3, .c 31, .c 467, .c 3, .c 5, .c 11, .c 3,
  .c 17, .c 307, .c 3, .c 37,
]
private theorem h0038c29 : checkBlock 318723 128 b0038c29 = true := by
  decide +kernel

private def b0038c30 : List Row := [
  .p pv3 [pv2,pv3,pv11,pv179], .c 3, .c 7, .c 5, .c 3, .c 11, .c 19, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv11,pv29], .c 71, .c 3, .c 13, .c 149, .c 3, .c 59, .c 5, .c 3, .c 263, .c 31,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv53171], .c 3, .p pv11 [pv2,pv5,pv61,pv523], .c 11, .c 3,
  .p pv2 [pv2,pv47,pv1697], .c 7, .c 3, .c 109, .c 5, .c 3, .p pv3 [pv2,pv19,pv2099], .c 37, .c 3,
  .c 5, .p pv67 [pv2,pv3,pv17,pv23], .c 3, .p pv3 [pv2,pv5,pv7,pv43,pv53], .c 151, .c 3, .c 7,
  .p pv19 [pv2,pv3,pv8863], .c 3, .c 17, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 29, .c 3, .c 61,
  .p pv2 [pv2,pv3,pv26591], .c 3, .p pv3 [pv2,pv39887], .c 11, .c 3, .c 41, .c 5, .c 3, .c 7,
  .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv29,pv131], .c 3, .c 11, .c 7, .c 3,
  .p pv5 [pv2,pv159563], .p pv11 [pv2,pv3,pv13297], .c 3, .p pv2 [pv2,pv11,pv7253], .c 5, .c 3,
  .c 337, .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv43,pv1237], .c 3, .c 7, .c 439, .c 3, .c 179,
  .p pv3 [pv2,pv3,pv7,pv17,pv149], .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv4987], .c 23, .c 3,
  .c 5, .c 47, .c 3, .c 19, .p pv3 [pv2,pv3,pv53197], .c 3, .c 11, .c 13, .c 3, .c 7, .c 5, .c 3,
  .c 37, .p pv23 [pv2,pv3,pv5,pv7,pv19], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv137,pv233],
  .c 61, .c 3, .c 23, .c 19, .c 3, .p pv5 [pv2,pv193,pv827], .c 5, .c 3, .c 73, .c 11, .c 3,
]
private theorem h0038c30 : checkBlock 318979 128 b0038c30 = true := by
  decide +kernel

private def b0038c31 : List Row := [
  .c 5, .p pv2 [pv2,pv3,pv37,pv719], .c 3, .c 13, .c 17, .c 3, .c 131, .c 7, .c 3, .c 11, .c 5,
  .c 3, .p pv2 [pv2,pv159629], .c 29, .c 3, .c 5, .c 13, .c 3, .c 47, .c 37, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv127,pv419], .c 3, .c 139, .c 5, .c 3, .p pv3 [pv2,pv107,pv373], .c 7, .c 3,
  .c 5, .c 11, .c 3, .c 83, .c 269, .c 3, .c 149, .c 23, .c 3, .p pv5 [pv2,pv7,pv2851], .c 5,
  .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv887], .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv7603], .c 3, .c 31,
  .c 7, .c 3, .c 197, .p pv2 [pv2,pv3,pv113,pv157], .c 3, .p pv5 [pv2,pv159671], .c 5, .c 3,
  .c 41, .p pv7 [pv2,pv3,pv5,pv2129], .c 3, .c 5, .p pv2 [pv2,pv3,pv2957], .c 3, .c 7, .c 11,
  .c 3, .c 59, .c 389, .c 3, .c 521, .c 5, .c 3, .c 17, .c 277, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv53231], .c 3, .p pv13 [pv2,pv5,pv19,pv41], .c 31, .c 3, .c 13,
  .p pv11 [pv2,pv3,pv53233], .c 3, .c 7, .c 5, .c 3, .c 19, .p pv2 [pv2,pv3,pv5,pv7,pv13], .c 3,
  .c 5, .c 7, .c 3, .c 37, .c 13, .c 3, .p pv2 [pv2,pv59,pv2707], .c 11, .c 3,
  .p pv3 [pv2,pv39929], .c 5, .c 3, .p pv7 [pv2,pv7,pv22817], .p pv7 [pv2,pv3,pv5,pv11], .c 3,
  .c 5, .c 17, .c 3, .c 11, .p pv2 [pv2,pv3,pv7,pv3803], .c 3, .c 61, .c 7, .c 3, .c 101, .c 5,
  .c 3, .p pv2 [pv2,pv79867], .c 167, .c 3, .c 5, .p pv2 [pv2,pv3,pv79,pv337], .c 3, .c 17,
  .p pv2 [pv2,pv3,pv17749], .c 3, .c 7, .p pv23 [pv2,pv3,pv13],
]
private theorem h0038c31 : checkBlock 319235 128 b0038c31 = true := by
  decide +kernel

def rows0038 : List Row :=
  b0038c00 ++ b0038c01 ++ b0038c02 ++ b0038c03 ++ b0038c04 ++ b0038c05 ++ b0038c06 ++ b0038c07 ++
  b0038c08 ++ b0038c09 ++ b0038c10 ++ b0038c11 ++ b0038c12 ++ b0038c13 ++ b0038c14 ++ b0038c15 ++
  b0038c16 ++ b0038c17 ++ b0038c18 ++ b0038c19 ++ b0038c20 ++ b0038c21 ++ b0038c22 ++ b0038c23 ++
  b0038c24 ++ b0038c25 ++ b0038c26 ++ b0038c27 ++ b0038c28 ++ b0038c29 ++ b0038c30 ++ b0038c31

theorem checked0038 : checkBlock 311299 4096 rows0038 = true :=
  checkBlock_append h0038c00 (
    checkBlock_append h0038c01 (
    checkBlock_append h0038c02 (
    checkBlock_append h0038c03 (
    checkBlock_append h0038c04 (
    checkBlock_append h0038c05 (
    checkBlock_append h0038c06 (
    checkBlock_append h0038c07 (
    checkBlock_append h0038c08 (
    checkBlock_append h0038c09 (
    checkBlock_append h0038c10 (
    checkBlock_append h0038c11 (
    checkBlock_append h0038c12 (
    checkBlock_append h0038c13 (
    checkBlock_append h0038c14 (
    checkBlock_append h0038c15 (
    checkBlock_append h0038c16 (
    checkBlock_append h0038c17 (
    checkBlock_append h0038c18 (
    checkBlock_append h0038c19 (
    checkBlock_append h0038c20 (
    checkBlock_append h0038c21 (
    checkBlock_append h0038c22 (
    checkBlock_append h0038c23 (
    checkBlock_append h0038c24 (
    checkBlock_append h0038c25 (
    checkBlock_append h0038c26 (
    checkBlock_append h0038c27 (
    checkBlock_append h0038c28 (
    checkBlock_append h0038c29 (
    checkBlock_append h0038c30 (
    h0038c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
