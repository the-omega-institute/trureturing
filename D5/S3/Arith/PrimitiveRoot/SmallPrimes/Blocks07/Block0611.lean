/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks07/Block0611
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks07/Block0611.checked0611
   digest: Kernel proof of checker success on extended consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table166
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table170
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table174
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table185
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table191
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table218
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table237
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables03.Table273

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0611c00 : List Row := [
  .c 17, .c 3, .c 13, .c 761, .c 3, .c 53, .c 5, .c 3, .c 277,
  .p pv23 [pv2,pv3,pv5,pv13,pv17,pv29], .c 3, .c 5, .c 11, .c 3, .p pv7 [pv2,pv5,pv499903], .c 13,
  .c 3, .c 17, .c 71, .c 3, .c 7, .c 5, .c 3, .c 11, .c 43, .c 3, .c 5, .c 7, .c 3, .c 47, .c 241,
  .c 3, .c 109, .c 821, .c 3, .c 23, .c 5, .c 3, .c 199, .p pv7 [pv2,pv3,pv5,pv41659], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv193,pv1439], .c 3, .c 31, .c 11, .c 3, .p pv3 [pv2,pv23,pv101,pv269], .c 7,
  .c 3, .p pv5 [pv2,pv2499551], .c 5, .c 3, .c 19, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv416593],
  .c 3, .p pv3 [pv2,pv5,pv7,pv79,pv113], .c 457, .c 3, .c 7, .c 59, .c 3, .c 61, .c 5, .c 3,
  .c 17, .c 7, .c 3, .c 5, .c 19, .c 3, .p pv11 [pv2,pv5,pv13,pv7691], .c 31, .c 3, .c 151, .c 11,
  .c 3, .c 13, .c 5, .c 3, .c 7, .c 41, .c 3, .c 5, .p pv29 [pv2,pv3,pv7,pv13,pv109], .c 3, .c 11,
  .c 7, .c 3, .p pv2 [pv2,pv73,pv97,pv353], .c 13, .c 3, .c 1483, .c 5, .c 3, .c 79,
  .p pv37 [pv2,pv3,pv5,pv2083], .c 3, .c 5, .c 17, .c 3, .c 7, .c 947, .c 3,
  .p pv3 [pv2,pv312451], .c 89, .c 3, .c 19, .c 5, .c 3, .c 347, .p pv3 [pv2,pv3,pv5,pv55547],
  .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv313], .c 3, .c 13, .p pv2 [pv2,pv3,pv19,pv43853], .c 3,
  .c 11, .c 47, .c 3, .c 7, .c 5, .c 3,
]
private theorem h0611c00 : checkBlock 4999003 128 b0611c00 = true := by
  decide +kernel

private def b0611c01 : List Row := [
  .c 73, .c 19, .c 3, .c 5, .c 7, .c 3, .c 281, .p pv5 [pv2,pv3,pv67,pv3109], .c 3, .c 31, .c 193,
  .c 3, .c 97, .c 5, .c 3, .c 1063, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv47,pv277], .c 3,
  .p pv2 [pv2,pv5,pv49993], .c 23, .c 3, .p pv2 [pv2,pv13,pv59,pv3259], .c 7, .c 3, .c 11, .c 5,
  .c 3, .c 13, .p pv11 [pv2,pv3,pv5,pv1543], .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv23,pv2131], .c 3,
  .c 53, .c 1667, .c 3, .c 7, .c 29, .c 3, .c 17, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 11,
  .c 3, .c 107, .p pv3 [pv2,pv3,pv491,pv1697], .c 3, .c 263, .c 647, .c 3, .c 163, .c 5, .c 3,
  .c 7, .c 541, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv119033], .c 3,
  .p pv11 [pv2,pv5,pv11,pv47,pv967], .c 7, .c 3, .c 13, .c 101, .c 3, .c 37, .c 5, .c 3,
  .p pv3 [pv2,pv271,pv1153], .c 17, .c 3, .c 5, .c 41, .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv29,pv86197], .c 1693, .c 3, .c 853, .c 5, .c 3, .p pv7 [pv2,pv43,pv61,pv953],
  .c 23, .c 3, .c 5, .p pv3 [pv2,pv3,pv277747], .c 3, .c 19, .p pv2 [pv2,pv3,pv416621], .c 3,
  .p pv3 [pv2,pv7,pv11,pv2029], .c 113, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv107,pv11681],
  .c 2221, .c 3, .c 5, .c 7, .c 3, .c 43, .c 59, .c 3, .c 23, .c 11, .c 3, .p pv2 [pv2,pv1249873],
  .c 5, .c 3, .c 41, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv833251], .c 3, .c 11, .c 17,
]
private theorem h0611c01 : checkBlock 4999259 128 b0611c01 = true := by
  decide +kernel

private def b0611c02 : List Row := [
  .c 3, .c 103, .c 7, .c 3, .p pv2 [pv2,pv11,pv227251], .c 5, .c 3, .p pv3 [pv2,pv229,pv2729],
  .c 47, .c 3, .c 5, .p pv5 [pv2,pv3,pv71,pv163], .c 3, .c 137, .c 53, .c 3, .c 7, .c 313, .c 3,
  .c 13, .c 5, .c 3, .p pv11 [pv2,pv2499779], .c 7, .c 3, .c 5, .c 43, .c 3, .c 29, .c 277, .c 3,
  .c 11, .c 13, .c 3, .c 593, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv18517], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv53,pv1123], .c 3, .c 59, .c 7, .c 3, .c 67, .c 127, .c 3,
  .p pv2 [pv2,pv109,pv11467], .c 5, .c 3, .c 2143, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv277757],
  .c 3, .c 7, .p pv37 [pv2,pv3,pv11,pv17,pv557], .c 3, .p pv2 [pv2,pv311,pv4019],
  .p pv3 [pv2,pv3,pv7,pv119039], .c 3, .c 11, .c 5, .c 3, .c 17, .p pv3 [pv2,pv3,pv5,pv33331],
  .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv19,pv59,pv223], .c 41, .c 3,
  .p pv5 [pv2,pv7,pv17,pv3001], .c 251, .c 3, .c 7, .c 5, .c 3, .c 19,
  .p pv19 [pv2,pv3,pv5,pv7,pv31], .c 3, .c 5, .c 7, .c 3, .c 139, .p pv2 [pv2,pv3,pv373,pv1117],
  .c 3, .c 73, .c 37, .c 3, .p pv5 [pv2,pv53,pv101,pv467], .c 5, .c 3, .c 11, .c 31, .c 3, .c 5,
  .c 17, .c 3, .c 109, .c 103, .c 3, .p pv5 [pv2,pv2499863], .c 7, .c 3,
  .p pv2 [pv2,pv337,pv3709], .c 5, .c 3, .c 43, .c 67, .c 3, .c 5, .c 1249, .c 3, .c 17, .c 11,
  .c 3, .c 7, .p pv7 [pv2,pv3,pv833293], .c 3, .c 23, .c 5, .c 3, .p pv3 [pv2,pv17,pv97,pv379],
]
private theorem h0611c02 : checkBlock 4999515 128 b0611c02 = true := by
  decide +kernel

private def b0611c03 : List Row := [
  .c 7, .c 3, .c 5, .c 877, .c 3, .p pv2 [pv2,pv5,pv249989], .p pv3 [pv2,pv3,pv43,pv19379], .c 3,
  .c 13, .c 107, .c 3, .c 19, .c 5, .c 3, .c 7, .p pv19 [pv2,pv3,pv5,pv13,pv641], .c 3, .c 5,
  .c 191, .c 3, .c 787, .c 7, .c 3, .c 389, .c 11, .c 3, .p pv5 [pv2,pv157,pv15923], .c 5, .c 3,
  .c 1847, .c 19, .c 3, .c 5, .c 59, .c 3, .c 7, .c 73, .c 3, .c 37,
  .p pv11 [pv2,pv3,pv7,pv29761], .c 3, .c 17, .c 5, .c 3, .c 607, .c 29, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv31,pv26881], .c 3, .p pv7 [pv2,pv5,pv17,pv29411], .c 173, .c 3, .c 131,
  .p pv11 [pv2,pv3,pv13,pv23,pv929], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv19,pv16447], .c 13,
  .c 3, .c 5, .c 7, .c 3, .c 23, .c 269, .c 3, .c 11, .c 41, .c 3, .p pv3 [pv2,pv151,pv4139],
  .c 5, .c 3, .c 29, .c 17, .c 3, .c 5, .c 419, .c 3, .c 89, .p pv29 [pv2,pv3,pv7,pv19841], .c 3,
  .c 463, .c 7, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv29,pv43103], .c 11, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv13,pv32051], .c 3, .p pv11 [pv2,pv5,pv7,pv2551],
  .p pv2 [pv2,pv3,pv11,pv71,pv97], .c 3, .c 7, .c 13, .c 3, .c 11, .c 5, .c 3, .c 157, .c 7, .c 3,
  .c 5, .c 61, .c 3, .c 41, .c 23, .c 3, .c 43, .p pv3 [pv2,pv3,pv191,pv4363],
]
private theorem h0611c03 : checkBlock 4999771 115 b0611c03 = true := by
  decide +kernel

def rows0611 : List Row :=
  b0611c00 ++ b0611c01 ++ b0611c02 ++ b0611c03

theorem checked0611 : checkBlock 4999003 499 rows0611 = true :=
  checkBlock_append h0611c00 (
    checkBlock_append h0611c01 (
    checkBlock_append h0611c02 (
    h0611c03)))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
