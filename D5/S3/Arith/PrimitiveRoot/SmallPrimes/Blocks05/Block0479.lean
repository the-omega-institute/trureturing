/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks05/Block0479
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks05/Block0479.checked0479
   digest: Kernel proof of checker success on extended consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table042
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table047
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table053
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table069
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table081
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table098
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table122
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table157
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table158
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table159
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table160
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table161
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table162
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table163
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table165
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table167
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table170
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table171
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table175
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table182
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table190
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table203
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table223
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables03.Table248

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0479c00 : List Row := [
  .c 23, .c 3, .c 467, .c 5, .c 3, .c 7, .c 37, .c 3, .c 5, .c 1543, .c 3,
  .p pv3 [pv2,pv5,pv13,pv3767], .c 7, .c 3, .c 31, .c 79, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv107,pv18307], .c 17, .c 3, .c 5, .c 53, .c 3, .c 7, .c 199, .c 3,
  .p pv2 [pv2,pv11,pv269,pv331], .c 13, .c 3, .c 379, .c 5, .c 3, .p pv3 [pv2,pv23,pv5323],
  .p pv19 [pv2,pv3,pv5,pv43,pv3037], .c 3, .c 5, .p pv11 [pv2,pv3,pv54413], .c 3, .c 479, .c 19,
  .c 3, .c 661, .c 11, .c 3, .c 7, .c 5, .c 3, .p pv19 [pv2,pv13,pv67,pv173],
  .p pv23 [pv2,pv3,pv5,pv7,pv11,pv53], .c 3, .c 5, .c 7, .c 3, .c 11, .c 43, .c 3, .c 59, .c 47,
  .c 3, .c 953, .c 5, .c 3, .c 137, .p pv3 [pv2,pv3,pv5,pv101,pv431], .c 3, .c 5, .c 13, .c 3,
  .p pv7 [pv2,pv5,pv19,pv1031], .c 17, .c 3, .c 881, .c 7, .c 3, .c 29, .c 5, .c 3, .c 19, .c 313,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv47,pv421], .c 3, .c 719, .p pv11 [pv2,pv3,pv163243], .c 3,
  .c 7, .c 743, .c 3, .c 23, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 19, .c 3, .c 457,
  .p pv3 [pv2,pv3,pv13,pv5581], .c 3, .c 503, .c 89, .c 3, .c 31, .c 5, .c 3, .c 7, .c 11, .c 3,
  .c 5, .c 223, .c 3, .c 101, .c 7, .c 3, .c 1381, .c 859, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv61,pv16057], .c 263, .c 3,
]
private theorem h0479c00 : checkBlock 3917659 128 b0479c00 = true := by
  decide +kernel

private def b0479c01 : List Row := [
  .c 5, .c 563, .c 3, .c 7, .p pv2 [pv2,pv3,pv17,pv71,pv541], .c 3, .c 13, .c 29, .c 3, .c 19,
  .c 5, .c 3, .c 17, .c 811, .c 3, .c 5, .c 11, .c 3, .c 593, .c 13, .c 3, .c 1621, .c 67, .c 3,
  .c 7, .c 5, .c 3, .c 11, .c 19, .c 3, .c 5, .c 7, .c 3, .c 23, .c 73, .c 3, .c 29,
  .p pv7 [pv2,pv3,pv43,pv2531], .c 3, .c 71, .c 5, .c 3, .c 1931, .c 41, .c 3, .c 5, .c 17, .c 3,
  .p pv2 [pv2,pv5,pv391801], .c 11, .c 3, .c 103, .c 7, .c 3, .c 1511, .c 5, .c 3,
  .p pv2 [pv2,pv19,pv31,pv1663], .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv326503], .c 3, .c 17,
  .p pv2 [pv2,pv3,pv41,pv5309], .c 3, .c 7, .c 113, .c 3, .p pv2 [pv2,pv797,pv1229], .c 5, .c 3,
  .c 31, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv19,pv34369], .c 3, .p pv11 [pv2,pv5,pv13,pv30139],
  .c 23, .c 3, .c 127, .c 11, .c 3, .c 13, .c 5, .c 3, .c 7, .c 61, .c 3, .c 5, .c 1109, .c 3,
  .c 11, .c 7, .c 3, .c 181, .c 13, .c 3, .c 1249, .c 5, .c 3, .c 23, .c 31, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv17,pv107,pv359], .c 3, .c 7, .c 197, .c 3, .p pv3 [pv2,pv89,pv5503],
  .p pv3 [pv2,pv3,pv7,pv13327], .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv13,pv151,pv499],
  .p pv19 [pv2,pv3,pv5,pv8707], .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv29683], .c 3, .c 13, .c 79,
  .c 3, .c 11, .c 1033,
]
private theorem h0479c01 : checkBlock 3917915 128 b0479c01 = true := by
  decide +kernel

private def b0479c02 : List Row := [
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv11,pv241,pv739], .c 83, .c 3, .c 5, .c 7, .c 3, .c 1933,
  .p pv5 [pv2,pv3,pv81629], .c 3, .p pv2 [pv2,pv979549], .c 19, .c 3, .c 43, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv4373], .c 11, .c 3, .c 5, .c 433, .c 3, .c 431, .c 103, .c 3, .c 67, .c 7,
  .c 3, .c 11, .c 5, .c 3, .c 13, .c 307, .c 3, .c 5, .c 41, .c 3, .p pv2 [pv2,pv5,pv7,pv2239],
  .c 149, .c 3, .c 7, .p pv2 [pv2,pv3,pv217681], .c 3, .c 37, .c 5, .c 3, .p pv2 [pv2,pv979567],
  .c 7, .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv23,pv4259], .p pv2 [pv2,pv3,pv509,pv1283],
  .c 3, .c 1187, .c 43, .c 3, .p pv2 [pv2,pv7,pv139939], .c 5, .c 3, .c 7,
  .p pv17 [pv2,pv3,pv5,pv37,pv353], .c 3, .c 5, .c 31, .c 3, .p pv11 [pv2,pv5,pv11,pv179,pv199],
  .c 7, .c 3, .c 13, .c 1361, .c 3, .p pv2 [pv2,pv1959161], .c 5, .c 3, .c 41, .c 127, .c 3, .c 5,
  .c 37, .c 3, .c 7, .c 11, .c 3, .c 17, .c 23, .c 3, .p pv3 [pv2,pv244897], .c 5, .c 3,
  .p pv7 [pv2,pv1959179], .c 67, .c 3, .c 5, .c 59, .c 3, .c 683, .c 1697, .c 3,
  .p pv5 [pv2,pv7,pv11,pv6361], .p pv2 [pv2,pv3,pv331,pv1973], .c 3, .c 7, .c 5, .c 3, .c 19,
  .p pv11 [pv2,pv3,pv5,pv7,pv47,pv397], .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv31,pv79], .c 89,
  .c 3, .c 577, .c 11, .c 3, .p pv2 [pv2,pv97,pv10099], .c 5, .c 3, .c 71, .c 13, .c 3, .c 5,
]
private theorem h0479c02 : checkBlock 3918171 128 b0479c02 = true := by
  decide +kernel

private def b0479c03 : List Row := [
  .c 19, .c 3, .c 11, .c 641, .c 3, .c 47, .c 7, .c 3, .p pv5 [pv2,pv11,pv277,pv643], .c 5, .c 3,
  .c 17, .c 29, .c 3, .c 5, .c 61, .c 3, .c 43, .c 541, .c 3, .c 7, .c 181, .c 3, .c 13, .c 5,
  .c 3, .c 79, .c 7, .c 3, .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv71,pv5519], .c 31, .c 3, .c 11,
  .c 13, .c 3, .c 19, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv23,pv631], .c 3, .c 5, .c 17, .c 3,
  .c 1747, .c 7, .c 3, .c 197, .p pv7 [pv2,pv3,pv6803], .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv29,pv5197], .c 11, .c 3, .c 5, .c 43, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv11,pv14843], .c 3, .p pv2 [pv2,pv23,pv191,pv223], .c 37, .c 3, .c 11, .c 5,
  .c 3, .p pv3 [pv2,pv17,pv28813], .p pv3 [pv2,pv3,pv5,pv130619], .c 3, .c 5, .c 13, .c 3, .c 89,
  .p pv3 [pv2,pv3,pv293,pv743], .c 3, .p pv5 [pv2,pv7,pv31,pv9029], .p pv2 [pv2,pv3,pv326549],
  .c 3, .c 7, .c 5, .c 3, .c 1399, .c 151, .c 3, .c 5, .c 7, .c 3, .c 137,
  .p pv2 [pv2,pv3,pv251,pv1301], .c 3, .c 19, .c 17, .c 3, .c 173, .c 5, .c 3, .c 11, .c 1327,
  .c 3, .c 5, .c 79, .c 3, .p pv3 [pv2,pv5,pv11,pv61,pv73], .c 709, .c 3, .c 499, .c 7, .c 3,
  .c 17, .c 5, .c 3, .c 109, .c 53, .c 3, .c 5, .p pv2 [pv2,pv3,pv653111], .c 3, .c 23, .c 11,
  .c 3, .c 7, .c 31, .c 3,
]
private theorem h0479c03 : checkBlock 3918427 128 b0479c03 = true := by
  decide +kernel

private def b0479c04 : List Row := [
  .c 29, .c 5, .c 3, .p pv3 [pv2,pv139,pv881], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv67,pv2437],
  .c 3, .c 61, .c 71, .c 3, .c 13, .c 331, .c 3, .c 73, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5,
  .c 113, .c 3, .c 19, .c 7, .c 3, .c 1709, .c 11, .c 3, .p pv5 [pv2,pv1959371], .c 5, .c 3,
  .c 1319, .p pv11 [pv2,pv3,pv5,pv11,pv19], .c 3, .c 5, .p pv5 [pv2,pv3,pv326563], .c 3, .c 7,
  .c 23, .c 3, .c 53, .c 19, .c 3, .c 571, .c 5, .c 3, .c 223, .c 37, .c 3, .c 5, .c 397, .c 3,
  .c 509, .p pv13 [pv2,pv3,pv269,pv607], .c 3, .p pv2 [pv2,pv7,pv173,pv809], .c 29, .c 3, .c 7,
  .c 5, .c 3, .c 23, .c 13, .c 3, .c 5, .c 7, .c 3, .c 41, .c 17, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv29,pv11261], .c 3, .c 1867, .c 5, .c 3, .c 59, .c 103, .c 3, .c 5, .c 179,
  .c 3, .p pv2 [pv2,pv5,pv13,pv6029], .p pv5 [pv2,pv3,pv7,pv15551], .c 3, .c 17, .c 7, .c 3,
  .c 13, .c 5, .c 3, .p pv2 [pv2,pv979717], .c 11, .c 3, .c 5, .c 109, .c 3,
  .p pv11 [pv2,pv5,pv7,pv3499], .c 19, .c 3, .c 7, .c 13, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv59,pv33211], .c 7, .c 3, .c 5, .c 47, .c 3, .c 311, .p pv5 [pv2,pv3,pv20411],
  .c 3, .c 739, .p pv3 [pv2,pv3,pv653153], .c 3, .p pv2 [pv2,pv7,pv39989], .c 5, .c 3, .c 7,
  .c 271, .c 3, .c 5, .c 11,
]
private theorem h0479c04 : checkBlock 3918683 128 b0479c04 = true := by
  decide +kernel

private def b0479c05 : List Row := [
  .c 3, .c 13, .c 7, .c 3, .c 23, .p pv2 [pv2,pv3,pv11,pv2699], .c 3, .c 79, .c 5, .c 3, .c 11,
  .c 461, .c 3, .c 5, .c 13, .c 3, .c 7, .c 29, .c 3, .c 43, .c 53, .c 3,
  .p pv5 [pv2,pv107,pv18313], .c 5, .c 3, .c 31, .c 1741, .c 3, .c 5, .c 19, .c 3, .c 47, .c 11,
  .c 3, .p pv11 [pv2,pv7,pv13,pv61,pv353], .c 163, .c 3, .c 7, .c 5, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv5,pv7,pv31,pv43], .c 3, .c 5, .c 7, .c 3, .c 29,
  .p pv5 [pv2,pv3,pv13,pv53,pv79], .c 3, .p pv2 [pv2,pv11,pv89069], .c 23, .c 3, .c 563, .c 5,
  .c 3, .p pv17 [pv2,pv7,pv47,pv1489], .c 31, .c 3, .c 5, .p pv11 [pv2,pv3,pv81647], .c 3, .c 17,
  .c 43, .c 3, .c 41, .c 7, .c 3, .c 19, .c 5, .c 3, .p pv13 [pv2,pv17,pv73,pv1579],
  .p pv7 [pv2,pv3,pv5,pv11,pv2969], .c 3, .c 5, .p pv3 [pv2,pv3,pv217727], .c 3, .c 11, .c 127,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv67,pv9749], .c 3, .c 101, .c 5, .c 3,
  .p pv2 [pv2,pv23,pv41,pv1039], .c 7, .c 3, .c 5, .c 1667, .c 3, .c 601, .c 13, .c 3, .c 131,
  .c 17, .c 3, .p pv3 [pv2,pv7,pv139969], .c 5, .c 3, .c 7, .c 631, .c 3, .c 5, .c 29, .c 3,
  .c 37, .c 7, .c 3, .c 11, .c 137, .c 3, .c 17, .c 5, .c 3, .p pv3 [pv2,pv11,pv19,pv293],
  .p pv2 [pv2,pv3,pv5,pv130639], .c 3, .c 5, .c 23, .c 3, .c 7, .p pv5 [pv2,pv3,pv653197], .c 3,
  .c 19, .c 47, .c 3, .c 59,
]
private theorem h0479c05 : checkBlock 3918939 128 b0479c05 = true := by
  decide +kernel

private def b0479c06 : List Row := [
  .c 5, .c 3, .p pv7 [pv2,pv1959599], .c 11, .c 3, .c 5, .c 997, .c 3, .p pv2 [pv2,pv5,pv391921],
  .p pv5 [pv2,pv3,pv11,pv3299], .c 3, .p pv3 [pv2,pv7,pv4999], .p pv2 [pv2,pv3,pv653203], .c 3,
  .c 7, .c 5, .c 3, .p pv2 [pv2,pv979807], .c 17, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv13,pv7537], .p pv17 [pv2,pv3,pv653207], .c 3, .p pv5 [pv2,pv23,pv85201],
  .p pv7 [pv2,pv3,pv17,pv1601], .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv7,pv131,pv2137],
  .p pv2 [pv2,pv3,pv5,pv83,pv787], .c 3, .c 5, .c 11, .c 3, .c 71, .c 277, .c 3,
  .p pv2 [pv2,pv979819], .c 7, .c 3, .c 47, .c 5, .c 3, .c 11, .c 701, .c 3, .c 5, .c 53, .c 3,
  .c 19, .c 107, .c 3, .c 7, .p pv2 [pv2,pv3,pv326609], .c 3, .c 41, .c 5, .c 3,
  .p pv17 [pv2,pv13,pv150743], .c 7, .c 3, .c 5, .p pv17 [pv2,pv3,pv419,pv1559], .c 3, .c 13,
  .c 11, .c 3, .c 1171, .c 19, .c 3, .c 83, .c 5, .c 3, .c 7, .c 733, .c 3, .c 5, .c 13, .c 3,
  .c 23, .c 7, .c 3, .c 17, .p pv41 [pv2,pv3,pv163307], .c 3, .c 37, .c 5, .c 3, .c 29,
  .p pv2 [pv2,pv3,pv5,pv65323], .c 3, .c 5, .p pv2 [pv2,pv3,pv313,pv2087], .c 3, .c 7,
  .p pv5 [pv2,pv3,pv31,pv439], .c 3, .p pv2 [pv2,pv13,pv19,pv3967], .c 11, .c 3, .c 53, .c 5,
  .c 3, .c 13, .p pv17 [pv2,pv3,pv5,pv11,pv37,pv107], .c 3, .c 5, .p pv5 [pv2,pv3,pv163309], .c 3,
  .c 11, .c 31, .c 3, .c 79, .c 59, .c 3, .c 7, .c 5, .c 3, .c 1949,
  .p pv37 [pv2,pv3,pv5,pv7,pv2333], .c 3, .c 5, .c 7, .c 3,
]
private theorem h0479c06 : checkBlock 3919195 128 b0479c06 = true := by
  decide +kernel

private def b0479c07 : List Row := [
  .c 929, .c 19, .c 3, .p pv3 [pv2,pv53,pv2311], .c 103, .c 3, .p pv5 [pv2,pv1959731], .c 5, .c 3,
  .c 17, .c 47, .c 3, .c 5, .c 41, .c 3, .p pv3 [pv2,pv5,pv97987], .c 521, .c 3, .c 11, .c 7,
  .c 3, .c 43, .c 5, .c 3, .c 23, .p pv7 [pv2,pv3,pv5,pv13,pv67], .c 3, .c 5, .c 101, .c 3,
  .c 191, .c 13, .c 3, .c 7, .p pv7 [pv2,pv3,pv41,pv47,pv113], .c 3,
  .p pv2 [pv2,pv23,pv139,pv613], .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 17, .c 3,
  .p pv2 [pv2,pv5,pv195977], .p pv5 [pv2,pv3,pv11,pv59387], .c 3, .c 31,
  .p pv17 [pv2,pv3,pv19,pv17191], .c 3, .c 11, .c 5, .c 3, .c 7, .c 577, .c 3, .c 5, .c 19, .c 3,
  .c 17, .c 7, .c 3, .p pv3 [pv2,pv97,pv5051], .c 43, .c 3, .p pv5 [pv2,pv29,pv67579], .c 5, .c 3,
  .c 73, .c 13, .c 3, .c 5, .c 11, .c 3, .c 7, .p pv5 [pv2,pv3,pv653267], .c 3,
  .p pv5 [pv2,pv59,pv563], .c 31, .c 3, .p pv2 [pv2,pv47,pv20849], .c 5, .c 3, .c 11,
  .p pv23 [pv2,pv3,pv5,pv65327], .c 3, .c 5, .p pv3 [pv2,pv3,pv71,pv3067], .c 3, .c 113, .c 947,
  .c 3, .c 23, .c 17, .c 3, .c 7, .c 5, .c 3, .c 89, .c 131, .c 3, .c 5, .c 7, .c 3, .c 139,
  .c 11, .c 3, .p pv2 [pv2,pv1959833], .c 13, .c 3, .c 17, .c 5, .c 3, .p pv11 [pv2,pv7,pv279977],
  .c 19, .c 3, .c 5, .p pv3 [pv2,pv3,pv653281], .c 3, .c 1663, .c 1307, .c 3, .c 71, .c 7, .c 3,
  .c 199, .c 5,
]
private theorem h0479c07 : checkBlock 3919451 128 b0479c07 = true := by
  decide +kernel

private def b0479c08 : List Row := [
  .c 3, .c 101, .p pv11 [pv2,pv3,pv5,pv130657], .c 3, .c 5, .p pv2 [pv2,pv3,pv108881], .c 3,
  .c 13, .c 41, .c 3, .c 7, .c 11, .c 3, .c 31, .c 5, .c 3, .c 1181, .c 7, .c 3, .c 5, .c 13,
  .c 3, .c 11, .c 47, .c 3, .c 19, .c 233, .c 3, .p pv2 [pv2,pv7,pv11,pv25453], .c 5, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv5,pv97,pv449], .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv19,pv307], .c 3,
  .p pv2 [pv2,pv5,pv37,pv5297], .c 7, .c 3, .p pv2 [pv2,pv13,pv11597], .p pv2 [pv2,pv3,pv108883],
  .c 3, .c 229, .c 5, .c 3, .c 13, .c 617, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv6599], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv13,pv25127], .c 3, .c 11, .c 157, .c 3, .p pv5 [pv2,pv79,pv24809], .c 5, .c 3,
  .p pv2 [pv2,pv11,pv89087], .c 439, .c 3, .c 5, .c 43, .c 3, .c 83, .c 17, .c 3, .c 47, .c 1289,
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv109,pv17981], .c 11, .c 3, .c 5, .c 7, .c 3, .c 19,
  .p pv5 [pv2,pv3,pv11,pv29], .c 3, .c 13, .c 503, .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv31,pv1129], .c 37, .c 3, .c 5, .p pv5 [pv2,pv3,pv54443], .c 3, .c 29, .c 13,
  .c 3, .p pv2 [pv2,pv197,pv9949], .c 7, .c 3, .c 23, .c 5, .c 3, .c 31, .c 61, .c 3, .c 5, .c 11,
  .c 3, .c 421, .c 53, .c 3, .c 7, .c 139, .c 3, .p pv5 [pv2,pv13,pv150767], .c 5, .c 3, .c 11,
  .c 7, .c 3, .c 5, .c 1217, .c 3, .p pv3 [pv2,pv5,pv11,pv59,pv151],
]
private theorem h0479c08 : checkBlock 3919707 128 b0479c08 = true := by
  decide +kernel

private def b0479c09 : List Row := [
  .c 1091, .c 3, .c 109, .c 41, .c 3, .p pv2 [pv2,pv7,pv139999], .c 5, .c 3, .c 7, .c 13, .c 3,
  .c 5, .c 163, .c 3, .c 167, .c 7, .c 3, .c 379, .p pv3 [pv2,pv3,pv467,pv1399], .c 3,
  .p pv2 [pv2,pv37,pv52973], .c 5, .c 3, .c 43, .p pv2 [pv2,pv3,pv5,pv41,pv3187], .c 3, .c 5,
  .c 29, .c 3, .c 7, .c 19, .c 3, .c 73, .p pv31 [pv2,pv3,pv7,pv23,pv2029], .c 3, .c 13, .c 5,
  .c 3, .c 37, .c 149, .c 3, .c 5, .c 17, .c 3, .c 23, .c 1237, .c 3, .p pv3 [pv2,pv7,pv70001],
  .c 11, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv743,pv1319], .p pv31 [pv2,pv3,pv5,pv7,pv11,pv1697],
  .c 3, .c 5, .c 7, .c 3, .c 11, .c 113, .c 3, .p pv5 [pv2,pv541,pv3623],
  .p pv7 [pv2,pv3,pv163337], .c 3, .c 1019, .c 5, .c 3, .c 19, .c 199, .c 3, .c 5, .c 443, .c 3,
  .c 13, .c 37, .c 3, .c 223, .c 7, .c 3, .c 71, .c 5, .c 3, .c 47, .p pv13 [pv2,pv3,pv5,pv14519],
  .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv7,pv28001], .c 23, .c 3, .c 7, .c 17, .c 3,
  .p pv3 [pv2,pv490019], .c 5, .c 3, .c 107, .c 7, .c 3, .c 5, .c 31, .c 3, .c 1831, .c 73, .c 3,
  .p pv3 [pv2,pv13,pv47,pv401], .p pv2 [pv2,pv3,pv653363], .c 3, .c 17, .c 5, .c 3, .c 7, .c 11,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv59,pv113], .c 3, .p pv3 [pv2,pv5,pv17,pv1153], .c 7, .c 3,
  .c 1481, .p pv13 [pv2,pv3,pv81671], .c 3, .c 11, .c 5, .c 3,
]
private theorem h0479c09 : checkBlock 3919963 128 b0479c09 = true := by
  decide +kernel

private def b0479c10 : List Row := [
  .c 449, .c 463, .c 3, .c 5, .p pv2 [pv2,pv3,pv61,pv10711], .c 3, .c 7,
  .p pv23 [pv2,pv3,pv19,pv8597], .c 3, .c 67, .p pv3 [pv2,pv3,pv7,pv3457], .c 3,
  .p pv2 [pv2,pv1960121], .c 5, .c 3, .c 29, .c 17, .c 3, .c 5, .c 11, .c 3, .c 37,
  .p pv3 [pv2,pv3,pv151,pv4327], .c 3, .c 13, .p pv2 [pv2,pv3,pv11,pv17,pv1747], .c 3, .c 7, .c 5,
  .c 3, .c 11, .c 23, .c 3, .c 5, .c 7, .c 3, .c 31, .c 13, .c 3, .c 41,
  .p pv2 [pv2,pv3,pv37,pv17659], .c 3, .p pv7 [pv2,pv17,pv115303], .c 5, .c 3, .c 113,
  .p pv3 [pv2,pv3,pv5,pv43,pv1013], .c 3, .c 5, .c 47, .c 3, .c 337, .c 11, .c 3, .c 19, .c 7,
  .c 3, .c 1459, .c 5, .c 3, .c 83, .c 829, .c 3, .c 5, .c 241, .c 3, .c 1973, .c 17, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv13,pv50261], .c 3, .c 127, .c 5, .c 3, .c 251, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv379,pv431], .c 3, .c 277, .p pv5 [pv2,pv3,pv433,pv503], .c 3, .c 17, .c 11,
  .c 3, .c 1123, .c 5, .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv11], .c 3, .c 5, .c 71, .c 3, .c 11,
  .c 7, .c 3, .p pv3 [pv2,pv101,pv1213], .c 23, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv980107],
  .p pv3 [pv2,pv3,pv5,pv130681], .c 3, .c 5, .c 131, .c 3, .c 7, .c 797, .c 3, .c 157, .c 13,
  .c 3, .p pv2 [pv2,pv29,pv33797], .c 5, .c 3, .p pv2 [pv2,pv47,pv179,pv233], .c 41, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv191,pv311], .c 3, .p pv19 [pv2,pv5,pv61,pv6427], .c 1163,
]
private theorem h0479c10 : checkBlock 3920219 128 b0479c10 = true := by
  decide +kernel

private def b0479c11 : List Row := [
  .c 3, .c 11, .c 19, .c 3, .c 7, .c 5, .c 3, .c 17, .c 59, .c 3, .c 5, .c 7, .c 3, .c 13, .c 757,
  .c 3, .c 677, .p pv2 [pv2,pv3,pv31,pv1171], .c 3, .p pv3 [pv2,pv109,pv281], .c 5, .c 3, .c 1549,
  .c 11, .c 3, .c 5, .c 13, .c 3, .c 61, .c 79, .c 3, .c 1489, .c 7, .c 3, .c 11, .c 5, .c 3,
  .c 71, .p pv13 [pv2,pv3,pv5,pv59,pv443], .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv7,pv7001],
  .c 223, .c 3, .c 7, .c 53, .c 3, .c 587, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 11, .c 3,
  .c 17, .c 19, .c 3, .c 29, .c 47, .c 3, .c 23, .c 5, .c 3, .c 7, .c 43, .c 3, .c 5, .c 127,
  .c 3, .c 109, .c 7, .c 3, .c 541, .p pv7 [pv2,pv3,pv89,pv3671], .c 3, .c 293, .c 5, .c 3, .c 67,
  .c 181, .c 3, .c 5, .c 839, .c 3, .c 7, .c 11, .c 3, .c 13, .c 17, .c 3, .c 31, .c 5, .c 3,
  .c 19, .c 83, .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv19219], .c 3, .p pv11 [pv2,pv5,pv98017], .c 13,
  .c 3, .p pv5 [pv2,pv7,pv11,pv3637], .p pv13 [pv2,pv3,pv19,pv1433], .c 3, .c 7, .c 5, .c 3,
  .c 131, .c 977, .c 3, .c 5, .c 7, .c 3, .c 727, .c 29, .c 3, .c 89, .c 11, .c 3, .c 557, .c 5,
  .c 3, .p pv3 [pv2,pv7,pv53,pv1321],
]
private theorem h0479c11 : checkBlock 3920475 128 b0479c11 = true := by
  decide +kernel

private def b0479c12 : List Row := [
  .c 389, .c 3, .c 5, .p pv5 [pv2,pv3,pv40841], .c 3, .c 11, .p pv5 [pv2,pv3,pv7,pv29,pv37], .c 3,
  .p pv2 [pv2,pv619,pv3167], .c 7, .c 3, .c 347, .c 5, .c 3, .p pv13 [pv2,pv1960379], .c 13, .c 3,
  .c 5, .c 1291, .c 3, .c 29, .c 67, .c 3, .c 7, .c 37, .c 3, .c 19, .c 5, .c 3, .c 41, .c 7,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv9901], .c 3, .c 107, .c 137, .c 3, .c 11, .c 1087, .c 3,
  .c 13, .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 509, .c 3, .c 1297, .c 7, .c 3, .c 83, .c 13,
  .c 3, .p pv2 [pv2,pv1960421], .c 5, .c 3, .c 31, .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv23,pv7103], .c 3, .c 7, .c 17, .c 3, .p pv2 [pv2,pv151,pv12983], .c 43, .c 3,
  .c 11, .c 5, .c 3, .c 23, .c 47, .c 3, .c 5, .c 29, .c 3, .c 13, .c 1031, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv673,pv971], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv107,pv9161], .c 31, .c 3,
  .c 5, .c 7, .c 3, .c 101, .p pv2 [pv2,pv3,pv217829], .c 3, .c 37,
  .p pv7 [pv2,pv3,pv11,pv47,pv79], .c 3, .p pv2 [pv2,pv467,pv2099], .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv53,pv137], .c 3, .c 5, .p pv7 [pv2,pv3,pv653491], .c 3, .c 313, .c 41,
  .c 3, .p pv2 [pv2,pv13,pv75403], .c 7, .c 3, .c 59, .c 5, .c 3, .c 13, .c 23, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv73,pv373], .c 3, .p pv3 [pv2,pv5,pv7,pv4001], .c 11, .c 3,
]
private theorem h0479c12 : checkBlock 3920731 128 b0479c12 = true := by
  decide +kernel

private def b0479c13 : List Row := [
  .c 7, .p pv2 [pv2,pv3,pv193,pv1693], .c 3, .c 53, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 79,
  .c 3, .c 19, .c 211, .c 3, .c 23, .c 61, .c 3, .p pv5 [pv2,pv7,pv47,pv59,pv101], .c 5, .c 3,
  .c 7, .c 97, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv46679], .c 3, .c 43, .c 7, .c 3, .c 13, .c 11,
  .c 3, .c 1877, .c 5, .c 3, .p pv2 [pv2,pv1960529], .c 29, .c 3, .c 5, .c 17, .c 3, .c 7, .c 13,
  .c 3, .c 137, .p pv3 [pv2,pv3,pv7,pv13337], .c 3, .c 409, .c 5, .c 3, .p pv3 [pv2,pv197,pv311],
  .c 1583, .c 3, .c 5, .c 31, .c 3, .c 17, .c 683, .c 3, .c 103, .c 23, .c 3, .c 7, .c 5, .c 3,
  .c 29, .p pv17 [pv2,pv3,pv5,pv7,pv389], .c 3, .c 5, .c 7, .c 3, .c 769, .c 1609, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv13,pv1289], .c 3, .p pv5 [pv2,pv499,pv3929], .c 5, .c 3, .c 37, .c 13, .c 3,
  .c 5, .c 233, .c 3, .p pv3 [pv2,pv5,pv167,pv587], .c 19, .c 3, .c 229, .c 7, .c 3,
  .p pv2 [pv2,pv980293], .c 5, .c 3, .p pv2 [pv2,pv23,pv85243], .c 11, .c 3, .c 5, .c 983, .c 3,
  .p pv7 [pv2,pv5,pv7,pv13,pv31,pv139], .p pv7 [pv2,pv3,pv11,pv4951], .c 3, .c 7, .c 41, .c 3,
  .c 11, .c 5, .c 3, .p pv3 [pv2,pv490151], .c 7, .c 3, .c 5, .p pv17 [pv2,pv3,pv13,pv1571], .c 3,
  .c 31, .c 37, .c 3, .p pv2 [pv2,pv1960613], .c 13, .c 3, .c 149, .c 5, .c 3, .c 7, .c 853,
]
private theorem h0479c13 : checkBlock 3920987 128 b0479c13 = true := by
  decide +kernel

private def b0479c14 : List Row := [
  .c 3, .c 5, .c 11, .c 3, .c 89, .c 7, .c 3, .c 47, .c 71, .c 3, .c 61, .c 5, .c 3, .c 11, .c 17,
  .c 3, .c 5, .c 19, .c 3, .c 7, .c 31, .c 3, .p pv5 [pv2,pv1960643],
  .p pv19 [pv2,pv3,pv7,pv17,pv1373], .c 3, .c 23, .c 5, .c 3, .c 43, .p pv2 [pv2,pv3,pv5,pv4357],
  .c 3, .c 5, .c 13, .c 3, .c 53, .c 11, .c 3, .c 59, .c 151, .c 3, .c 7, .c 5, .c 3, .c 139,
  .c 881, .c 3, .c 5, .c 7, .c 3, .c 73, .p pv3 [pv2,pv3,pv43,pv15199], .c 3,
  .p pv2 [pv2,pv11,pv13,pv13711], .c 373, .c 3, .c 19, .c 5, .c 3, .c 13, .c 613, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv653561], .c 3, .c 37, .c 17, .c 3, .p pv3 [pv2,pv31,pv59,pv67], .c 7, .c 3,
  .p pv5 [pv2,pv149,pv13159], .c 5, .c 3, .c 157, .c 19, .c 3, .c 5, .c 1399, .c 3, .c 11, .c 883,
  .c 3, .c 7, .c 29, .c 3, .p pv2 [pv2,pv11,pv89123], .c 5, .c 3, .c 97, .c 7, .c 3, .c 5, .c 887,
  .c 3, .c 23, .c 761, .c 3, .c 13, .c 113, .c 3, .c 67, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv13,pv2011], .c 3, .c 5, .c 1151, .c 3, .c 1753, .c 7, .c 3, .c 11, .c 31,
  .c 3, .c 1879, .c 5, .c 3, .c 709, .c 79, .c 3, .c 5, .c 73, .c 3, .c 7, .c 109, .c 3,
  .p pv3 [pv2,pv29,pv16903],
]
private theorem h0479c14 : checkBlock 3921243 128 b0479c14 = true := by
  decide +kernel

private def b0479c15 : List Row := [
  .p pv2 [pv2,pv3,pv7,pv31123], .c 3, .p pv5 [pv2,pv13,pv150827], .c 5, .c 3, .c 17, .c 11, .c 3,
  .c 5, .c 457, .c 3, .p pv3 [pv2,pv5,pv49019], .c 23, .c 3, .c 41,
  .p pv17 [pv2,pv3,pv13,pv12569], .c 3, .c 7, .c 5, .c 3, .c 47, .c 13, .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv107,pv733], .c 59, .c 3, .c 43, .p pv3 [pv2,pv3,pv653593], .c 3, .c 257, .c 5,
  .c 3, .c 23, .c 673, .c 3, .c 5, .c 11, .c 3, .c 19, .c 29, .c 3, .c 439, .c 7, .c 3, .c 13,
  .c 5, .c 3, .c 11, .p pv11 [pv2,pv3,pv5,pv19,pv43], .c 3, .c 5, .c 89, .c 3, .c 17, .c 97, .c 3,
  .c 7, .c 13, .c 3, .c 233, .c 5, .c 3, .c 53, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv281,pv1163],
  .c 3, .c 29, .c 11, .c 3, .c 1453, .p pv11 [pv2,pv3,pv81701], .c 3, .c 599, .c 5, .c 3, .c 7,
  .c 23, .c 3, .c 5, .c 37, .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv11,pv19,pv4691], .c 17, .c 3,
  .p pv2 [pv2,pv53,pv36997], .c 5, .c 3, .p pv3 [pv2,pv331,pv1481], .c 41, .c 3, .c 5, .c 13,
  .c 3, .c 7, .c 157, .c 3, .c 23, .c 11, .c 3, .c 17, .c 5, .c 3, .p pv7 [pv2,pv79,pv24821],
  .p pv37 [pv2,pv3,pv5,pv11,pv2971], .c 3, .c 5, .c 47, .c 3, .c 11, .c 19, .c 3, .c 173, .c 1229,
  .c 3, .c 7, .c 5, .c 3, .c 13, .c 61, .c 3,
]
private theorem h0479c15 : checkBlock 3921499 128 b0479c15 = true := by
  decide +kernel

private def b0479c16 : List Row := [
  .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv127,pv193], .c 1901, .c 3, .c 1697,
  .p pv7 [pv2,pv3,pv54469], .c 3, .c 41, .c 5, .c 3, .c 31, .c 17, .c 3, .c 5, .c 1117, .c 3,
  .p pv17 [pv2,pv5,pv19,pv20641], .c 241, .c 3, .c 11, .c 7, .c 3, .c 191, .c 5, .c 3, .c 19,
  .c 487, .c 3, .c 5, .p pv19 [pv2,pv3,pv163409], .c 3, .c 47, .p pv11 [pv2,pv3,pv23,pv9473],
  .c 3, .c 7, .c 149, .c 3, .c 83, .c 5, .c 3, .c 1777, .c 7, .c 3, .c 5, .c 19, .c 3,
  .p pv2 [pv2,pv5,pv78437], .c 13, .c 3, .c 211, .p pv3 [pv2,pv3,pv43,pv563], .c 3, .c 11, .c 5,
  .c 3, .c 7, .c 107, .c 3, .c 5, .p pv13 [pv2,pv3,pv7,pv79,pv197], .c 3,
  .p pv3 [pv2,pv5,pv98047], .c 7, .c 3, .c 127, .c 37, .c 3, .p pv2 [pv2,pv13,pv199,pv379], .c 5,
  .c 3, .c 137, .c 43, .c 3, .c 5, .c 11, .c 3, .c 7, .p pv5 [pv2,pv3,pv67,pv271], .c 3, .c 17,
  .p pv3 [pv2,pv3,pv7,pv11,pv13,pv653], .c 3, .c 19, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 23,
  .c 3, .p pv2 [pv2,pv5,pv11,pv17827], .c 163, .c 3, .c 53, .p pv2 [pv2,pv3,pv108943], .c 3, .c 7,
  .c 5, .c 3, .p pv13 [pv2,pv1960979], .c 19, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv13,pv30169], .c 11, .c 3, .c 523, .c 67, .c 3, .c 13, .c 5, .c 3, .c 29,
  .p pv3 [pv2,pv3,pv5,pv239,pv547], .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv31,pv811], .c 3, .c 97,
  .p pv5 [pv2,pv3,pv7,pv17,pv1831], .c 3, .p pv5 [pv2,pv11,pv23,pv337], .c 7,
]
private theorem h0479c16 : checkBlock 3921755 128 b0479c16 = true := by
  decide +kernel

private def b0479c17 : List Row := [
  .c 3, .p pv2 [pv2,pv980503], .c 5, .c 3, .c 17, .c 311, .c 3, .c 5, .c 31, .c 3,
  .p pv11 [pv2,pv5,pv7,pv43,pv1303], .p pv7 [pv2,pv3,pv101,pv809], .c 3, .c 7, .c 11, .c 3,
  .c 277, .c 5, .c 3, .c 1321, .c 7, .c 3, .c 5, .c 1933, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv349,pv1873], .c 3, .p pv2 [pv2,pv1961033], .c 179, .c 3, .c 43, .c 5, .c 3,
  .c 7, .p pv13 [pv2,pv3,pv5,pv8171], .c 3, .c 5, .c 13, .c 3, .c 199, .c 7, .c 3, .c 283,
  .p pv2 [pv2,pv3,pv23,pv97,pv293], .c 3, .c 47, .c 5, .c 3, .p pv2 [pv2,pv491,pv1997], .c 37,
  .c 3, .c 5, .c 61, .c 3, .c 7, .p pv3 [pv2,pv3,pv653687], .c 3, .c 11, .c 367, .c 3, .c 101,
  .c 5, .c 3, .c 13, .c 89, .c 3, .c 5, .c 109, .c 3, .c 19, .p pv5 [pv2,pv3,pv13,pv967], .c 3,
  .p pv3 [pv2,pv7,pv20011], .c 43, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv490271], .c 11, .c 3,
  .c 5, .c 7, .c 3, .c 401, .c 41, .c 3, .p pv2 [pv2,pv1961093], .c 17, .c 3, .c 11, .c 5, .c 3,
  .c 571, .c 1567, .c 3, .c 5, .p pv11 [pv2,pv3,pv17,pv38453], .c 3, .c 1049, .c 23, .c 3, .c 13,
  .c 7, .c 3, .c 17, .c 5, .c 3, .c 239, .p pv3 [pv2,pv3,pv5,pv13,pv89,pv113], .c 3, .c 5, .c 11,
  .c 3, .c 317, .c 13, .c 3, .c 7, .p pv19 [pv2,pv3,pv11,pv83,pv179], .c 3, .c 71, .c 5, .c 3,
  .c 11, .c 7, .c 3, .c 5,
]
private theorem h0479c17 : checkBlock 3922011 128 b0479c17 = true := by
  decide +kernel

private def b0479c18 : List Row := [
  .p pv2 [pv2,pv3,pv653711], .c 3, .c 79, .p pv5 [pv2,pv3,pv13619], .c 3,
  .p pv2 [pv2,pv149,pv6581], .c 29, .c 3, .c 733, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 743,
  .c 3, .c 1033, .c 7, .c 3, .c 1307, .p pv2 [pv2,pv3,pv13,pv17,pv29], .c 3,
  .p pv3 [pv2,pv229,pv2141], .c 5, .c 3, .c 89, .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv217907],
  .c 3, .c 7, .c 37, .c 3, .c 29, .c 193, .c 3, .c 103, .c 5, .c 3, .p pv2 [pv2,pv980587], .c 23,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv326863], .c 3, .c 61, .c 73, .c 3, .p pv5 [pv2,pv7,pv29,pv9661],
  .c 11, .c 3, .c 7, .c 5, .c 3, .c 19, .c 67, .c 3, .c 5, .c 7, .c 3, .c 11, .c 17, .c 3, .c 23,
  .c 13, .c 3, .p pv5 [pv2,pv11,pv131,pv1361], .c 5, .c 3, .p pv11 [pv2,pv7,pv89,pv787], .c 349,
  .c 3, .c 5, .c 19, .c 3, .c 563, .p pv3 [pv2,pv3,pv7,pv61,pv1531], .c 3, .c 17, .c 7, .c 3,
  .p pv3 [pv2,pv47,pv163], .c 5, .c 3, .p pv11 [pv2,pv13,pv59,pv2557], .c 139, .c 3, .c 5, .c 137,
  .c 3, .c 13, .c 29, .c 3, .c 7, .p pv7 [pv2,pv3,pv653743], .c 3, .p pv5 [pv2,pv1961231], .c 5,
  .c 3, .c 683, .c 7, .c 3, .c 5, .c 13, .c 3, .c 37, .c 61, .c 3, .p pv5 [pv2,pv97,pv20219],
  .c 23, .c 3, .c 19, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv1153], .c 3,
  .c 29, .c 7, .c 3, .c 1061, .p pv3 [pv2,pv3,pv37,pv17669], .c 3,
]
private theorem h0479c18 : checkBlock 3922267 128 b0479c18 = true := by
  decide +kernel

private def b0479c19 : List Row := [
  .c 11, .c 5, .c 3, .c 13, .c 19, .c 3, .c 5, .c 71, .c 3, .c 7, .p pv3 [pv2,pv3,pv13,pv16763],
  .c 3, .c 433, .c 103, .c 3, .p pv3 [pv2,pv41,pv11959], .c 5, .c 3,
  .p pv7 [pv2,pv23,pv269,pv317], .p pv37 [pv2,pv3,pv5,pv227], .c 3, .c 5, .c 11, .c 3, .c 653,
  .c 47, .c 3, .p pv3 [pv2,pv7,pv35023], .p pv13 [pv2,pv3,pv11,pv1801], .c 3, .c 7, .c 5, .c 3,
  .c 11, .c 257, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv11,pv1783], .c 619, .c 3, .c 13,
  .c 521, .c 3, .p pv2 [pv2,pv739,pv1327], .c 5, .c 3, .p pv2 [pv2,pv7,pv280187],
  .p pv11 [pv2,pv3,pv5,pv13,pv47,pv107], .c 3, .c 5, .c 23, .c 3, .c 17, .c 11, .c 3,
  .p pv2 [pv2,pv53,pv18503], .c 7, .c 3, .c 311, .c 5, .c 3, .c 67,
  .p pv2 [pv2,pv3,pv5,pv23,pv379], .c 3, .c 5, .p pv5 [pv2,pv3,pv29,pv1409], .c 3, .c 1373, .c 83,
  .c 3, .c 7, .c 769, .c 3, .c 23, .c 5, .c 3, .c 71, .c 7, .c 3, .c 5, .c 1607, .c 3,
  .p pv2 [pv2,pv5,pv392269], .c 1279, .c 3, .c 1627, .c 11, .c 3, .c 37, .c 5, .c 3, .c 7, .c 13,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv17,pv41,pv67], .c 3, .c 11, .c 7, .c 3, .c 61,
  .p pv11 [pv2,pv3,pv73,pv2239], .c 3, .c 17, .c 5, .c 3, .c 101,
  .p pv2 [pv2,pv3,pv5,pv19,pv31,pv37], .c 3, .c 5, .p pv3 [pv2,pv3,pv83,pv7877], .c 3, .c 7,
  .p pv5 [pv2,pv3,pv20431], .c 3, .c 41, .c 19, .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv245173],
  .c 31, .c 3, .c 5, .c 37,
]
private theorem h0479c19 : checkBlock 3922523 128 b0479c19 = true := by
  decide +kernel

private def b0479c20 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv196139], .c 67, .c 3, .c 11, .c 13, .c 3, .c 7, .c 5, .c 3, .c 1163,
  .c 17, .c 3, .c 5, .c 7, .c 3, .c 23, .c 181, .c 3, .c 1447, .p pv2 [pv2,pv3,pv17,pv38459],
  .c 3, .c 1427, .c 5, .c 3, .c 83, .c 11, .c 3, .c 5, .c 1619, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv7,pv11,pv1213], .c 3, .c 43, .c 7, .c 3, .c 11, .c 5, .c 3, .c 29, .c 197,
  .c 3, .c 5, .c 13, .c 3, .p pv7 [pv2,pv5,pv7,pv56041], .c 19, .c 3, .c 7, .c 251, .c 3, .c 1499,
  .c 5, .c 3, .c 353, .c 7, .c 3, .c 5, .c 11, .c 3, .c 53, .c 17, .c 3,
  .p pv5 [pv2,pv13,pv150881], .p pv2 [pv2,pv3,pv11,pv113,pv263], .c 3, .c 449, .c 5, .c 3, .c 7,
  .c 41, .c 3, .c 5, .c 631, .c 3, .p pv2 [pv2,pv5,pv11,pv19,pv1877], .c 7, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv72647], .c 3, .c 643, .c 5, .c 3, .c 19, .c 557, .c 3, .c 5, .c 31, .c 3,
  .c 7, .c 11, .c 3, .p pv5 [pv2,pv1961483], .c 59, .c 3, .p pv2 [pv2,pv23,pv42641], .c 5, .c 3,
  .p pv2 [pv2,pv1961489], .p pv2 [pv2,pv3,pv5,pv151,pv433], .c 3, .c 5, .c 19, .c 3, .c 1699,
  .p pv17 [pv2,pv3,pv1009], .c 3, .c 13, .c 37, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv61297],
  .p pv3 [pv2,pv3,pv5,pv7,pv13,pv479], .c 3, .c 5, .c 7, .c 3, .c 113, .c 13, .c 3, .c 659, .c 11,
  .c 3, .c 29,
]
private theorem h0479c20 : checkBlock 3922779 128 b0479c20 = true := by
  decide +kernel

private def b0479c21 : List Row := [
  .c 5, .c 3, .c 17, .c 23, .c 3, .c 5, .p pv5 [pv2,pv3,pv72649], .c 3, .c 11, .c 859, .c 3,
  .c 131, .c 7, .c 3, .c 19, .c 5, .c 3, .c 383, .p pv3 [pv2,pv3,pv5,pv130769], .c 3, .c 5,
  .p pv13 [pv2,pv3,pv326923], .c 3, .c 31, .p pv2 [pv2,pv3,pv19,pv11471], .c 3, .c 7,
  .p pv43 [pv2,pv3,pv13,pv6287], .c 3, .c 61, .c 5, .c 3, .p pv2 [pv2,pv1961549], .c 7, .c 3,
  .c 5, .c 17, .c 3, .c 193, .c 53, .c 3, .c 11, .c 967, .c 3, .c 211, .c 5, .c 3, .c 7, .c 151,
  .c 3, .c 5, .c 47, .c 3, .c 17, .c 7, .c 3, .c 37, .c 29, .c 3, .c 13, .c 5, .c 3,
  .p pv11 [pv2,pv17,pv19,pv6073], .c 11, .c 3, .c 5, .c 41, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv11,pv9907], .c 3, .c 19, .c 13, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv131,pv7487], .c 43, .c 3, .c 5, .c 1231, .c 3, .c 887,
  .p pv3 [pv2,pv3,pv23,pv28429], .c 3, .c 29, .c 17, .c 3, .c 7, .c 5, .c 3, .c 53, .c 37, .c 3,
  .c 5, .c 7, .c 3, .c 13, .p pv11 [pv2,pv3,pv40867], .c 3, .c 109, .c 73, .c 3, .c 17, .c 5,
  .c 3, .c 11, .c 1459, .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv11,pv17,pv1049],
  .p pv3 [pv2,pv3,pv7,pv97,pv107], .c 3, .c 31, .c 7, .c 3, .c 157, .c 5, .c 3,
  .p pv19 [pv2,pv47,pv41737], .p pv13 [pv2,pv3,pv5,pv5449], .c 3, .c 5, .p pv3 [pv2,pv3,pv653881],
  .c 3,
]
private theorem h0479c21 : checkBlock 3923035 128 b0479c21 = true := by
  decide +kernel

private def b0479c22 : List Row := [
  .c 19, .c 11, .c 3, .c 7, .c 421, .c 3, .p pv5 [pv2,pv1961651], .c 5, .c 3, .c 13, .c 7, .c 3,
  .c 5, .c 23, .c 3, .p pv3 [pv2,pv5,pv43,pv2281], .c 29, .c 3, .c 83, .c 19, .c 3, .c 1303, .c 5,
  .c 3, .c 7, .c 571, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv109,pv857], .c 3, .c 739, .c 7, .c 3,
  .p pv2 [pv2,pv181,pv5419], .c 11, .c 3, .c 23, .c 5, .c 3, .c 37, .c 1103, .c 3, .c 5, .c 79,
  .c 3, .c 7, .c 1051, .c 3, .c 13, .c 71, .c 3, .c 431, .c 5, .c 3, .p pv7 [pv2,pv61,pv32159],
  .p pv17 [pv2,pv3,pv5,pv13,pv503], .c 3, .c 5, .p pv5 [pv2,pv3,pv37,pv43,pv137], .c 3, .c 127,
  .c 13, .c 3, .p pv3 [pv2,pv7,pv70061], .c 47, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv277,pv3541],
  .c 53, .c 3, .c 5, .c 7, .c 3, .c 59, .c 19, .c 3, .c 11, .c 43, .c 3, .c 31, .c 5, .c 3, .c 61,
  .c 1951, .c 3, .c 5, .c 173, .c 3, .p pv13 [pv2,pv5,pv392347], .c 113, .c 3,
  .p pv2 [pv2,pv89,pv103,pv107], .c 7, .c 3, .p pv2 [pv2,pv1961741], .c 5, .c 3, .c 479, .c 11,
  .c 3, .c 5, .c 29, .c 3, .c 23, .c 617, .c 3, .c 7, .c 317, .c 3, .c 11, .c 5, .c 3, .c 19,
  .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv29,pv22549], .c 3, .c 71, .c 1063, .c 3, .c 53,
  .p pv2 [pv2,pv3,pv19,pv127,pv271], .c 3, .c 13, .c 5,
]
private theorem h0479c22 : checkBlock 3923291 128 b0479c22 = true := by
  decide +kernel

private def b0479c23 : List Row := [
  .c 3, .c 7, .c 397, .c 3, .c 5, .c 11, .c 3, .c 641, .c 7, .c 3, .p pv5 [pv2,pv17,pv115399],
  .c 13, .c 3, .c 163, .c 5, .c 3, .c 11, .c 61, .c 3, .c 5, .c 67, .c 3, .c 7, .c 23, .c 3,
  .c 367, .p pv3 [pv2,pv3,pv7,pv93419], .c 3, .c 281, .c 5, .c 3, .p pv3 [pv2,pv13,pv31,pv1217],
  .p pv19 [pv2,pv3,pv5,pv130787], .c 3, .c 5, .c 17, .c 3, .c 13, .c 11, .c 3,
  .p pv7 [pv2,pv7,pv40037], .p pv2 [pv2,pv3,pv37,pv8837], .c 3, .c 7, .c 5, .c 3, .c 23,
  .p pv37 [pv2,pv3,pv5,pv7,pv173], .c 3, .c 5, .c 7, .c 3, .c 17, .p pv11 [pv2,pv3,pv19,pv17209],
  .c 3, .c 829, .c 41, .c 3, .c 239, .c 5, .c 3, .p pv2 [pv2,pv7,pv17,pv8243], .c 19, .c 3, .c 5,
  .c 59, .c 3, .p pv7 [pv2,pv5,pv137,pv179], .c 199, .c 3, .p pv5 [pv2,pv13,pv229,pv659], .c 7,
  .c 3, .c 79, .c 5, .c 3, .c 13, .c 31, .c 3, .c 5, .c 43, .c 3, .c 11, .c 191, .c 3, .c 7,
  .c 17, .c 3, .p pv2 [pv2,pv11,pv178351], .c 5, .c 3, .c 29, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv17,pv59,pv163], .c 3, .c 41, .c 89, .c 3, .c 19, .c 53, .c 3, .c 17, .c 5,
  .c 3, .c 7, .p pv19 [pv2,pv3,pv5,pv16349], .c 3, .c 5, .c 307, .c 3,
  .p pv2 [pv2,pv5,pv17,pv23081], .c 7, .c 3, .c 11, .p pv2 [pv2,pv3,pv653963], .c 3, .c 743, .c 5,
  .c 3, .p pv2 [pv2,pv11,pv67], .p pv7 [pv2,pv3,pv5,pv13,pv10061], .c 3, .c 5, .c 107, .c 3, .c 7,
]
private theorem h0479c23 : checkBlock 3923547 128 b0479c23 = true := by
  decide +kernel

private def b0479c24 : List Row := [
  .c 13, .c 3, .c 349, .c 271, .c 3, .c 37, .c 5, .c 3, .c 1669, .c 11, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv317,pv2063], .c 3, .c 139, .c 1831, .c 3, .p pv2 [pv2,pv7,pv43,pv3259],
  .p pv3 [pv2,pv3,pv17,pv12823], .c 3, .c 7, .c 5, .c 3, .c 1543, .c 79, .c 3, .c 5, .c 7, .c 3,
  .c 19, .p pv3 [pv2,pv3,pv653977], .c 3, .p pv2 [pv2,pv1961933], .c 23, .c 3, .c 541, .c 5, .c 3,
  .c 43, .c 13, .c 3, .c 5, .c 11, .c 3, .c 109, .p pv5 [pv2,pv3,pv7,pv23,pv677], .c 3,
  .p pv3 [pv2,pv73,pv6719], .c 7, .c 3, .c 29, .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv14533],
  .c 3, .c 5, .p pv5 [pv2,pv3,pv326993], .c 3, .c 89, .c 17, .c 3, .c 7, .c 601, .c 3, .c 13,
  .c 5, .c 3, .c 1327, .c 7, .c 3, .c 5, .c 61, .c 3, .c 101, .c 11, .c 3, .c 17, .c 13, .c 3,
  .p pv2 [pv2,pv7,pv241,pv1163], .c 5, .c 3, .c 7, .p pv29 [pv2,pv3,pv5,pv139,pv941], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv23357], .c 3, .p pv3 [pv2,pv5,pv31,pv6329], .c 7, .c 3, .c 41, .c 67,
  .c 3, .p pv3 [pv2,pv490499], .c 5, .c 3, .c 167, .c 1009, .c 3, .c 5, .c 23, .c 3, .c 7, .c 19,
  .c 3, .p pv3 [pv2,pv245251], .c 11, .c 3, .p pv5 [pv2,pv1962011], .c 5, .c 3,
  .p pv2 [pv2,pv41,pv71,pv337], .c 59, .c 3, .c 5, .c 13, .c 3, .c 11, .c 197, .c 3,
  .p pv17 [pv2,pv7,pv127,pv2207], .c 599, .c 3, .c 7, .c 5, .c 3,
]
private theorem h0479c24 : checkBlock 3923803 128 b0479c24 = true := by
  decide +kernel

private def b0479c25 : List Row := [
  .c 17, .c 863, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv19,pv1087], .c 31, .c 3, .c 29,
  .p pv47 [pv2,pv3,pv283,pv2311], .c 3, .p pv2 [pv2,pv1962041], .c 5, .c 3, .c 13, .c 137, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv11,pv929], .c 3, .p pv2 [pv2,pv5,pv39241],
  .p pv3 [pv2,pv3,pv7,pv13,pv7187], .c 3, .c 11, .c 7, .c 3, .p pv3 [pv2,pv245257], .c 5, .c 3,
  .p pv11 [pv2,pv11,pv107,pv1667], .p pv13 [pv2,pv3,pv5,pv53,pv617], .c 3, .c 5, .c 17, .c 3,
  .c 223, .c 257, .c 3, .c 7, .p pv2 [pv2,pv3,pv654023], .c 3, .c 317, .c 5, .c 3, .c 59, .c 7,
  .c 3, .c 5, .c 83, .c 3, .c 17, .p pv2 [pv2,pv3,pv11,pv19819], .c 3, .c 13, .c 1019, .c 3,
  .c 11, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv13,pv43], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv233,pv401], .c 3, .c 23, .c 7, .c 3, .c 31, .p pv11 [pv2,pv3,pv311,pv701],
  .c 3, .c 19, .c 5, .c 3, .p pv3 [pv2,pv59,pv4157], .p pv2 [pv2,pv3,pv5,pv130807], .c 3, .c 5,
  .c 11, .c 3, .c 7, .c 43, .c 3, .p pv2 [pv2,pv53,pv37021], .c 17, .c 3, .c 41, .c 5, .c 3,
  .c 11, .c 19, .c 3, .c 5, .p pv13 [pv2,pv3,pv17,pv79,pv487], .c 3, .c 29,
  .p pv5 [pv2,pv3,pv61,pv1787], .c 3, .c 37, .c 31, .c 3, .c 7, .c 5, .c 3, .c 193, .c 13, .c 3,
  .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv17,pv29,pv199], .c 11, .c 3, .p pv5 [pv2,pv191,pv10273],
  .p pv7 [pv2,pv3,pv757], .c 3, .p pv2 [pv2,pv981073], .c 5, .c 3, .c 1069, .c 353, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv23,pv9479], .c 3, .p pv37 [pv2,pv5,pv13,pv30187], .c 61,
]
private theorem h0479c25 : checkBlock 3924059 128 b0479c25 = true := by
  decide +kernel

private def b0479c26 : List Row := [
  .c 3, .c 19, .c 7, .c 3, .c 13, .c 5, .c 3, .c 23, .c 17, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv13,pv19,pv331], .c 3, .p pv2 [pv2,pv5,pv7,pv28031], .p pv5 [pv2,pv3,pv72673],
  .c 3, .c 7, .c 11, .c 3, .p pv3 [pv2,pv23,pv31,pv43], .c 5, .c 3, .c 47, .c 7, .c 3, .c 5,
  .c 29, .c 3, .c 11, .c 229, .c 3, .c 113, .c 1801, .c 3, .c 31, .c 5, .c 3, .c 7, .c 67, .c 3,
  .c 5, .c 41, .c 3, .c 13, .c 7, .c 3, .c 73, .p pv7 [pv2,pv3,pv163517], .c 3,
  .p pv2 [pv2,pv19,pv51637], .c 5, .c 3, .c 233, .c 23, .c 3, .c 5, .c 13, .c 3, .c 7, .c 17,
  .c 3, .c 11, .c 107, .c 3, .p pv2 [pv2,pv37,pv181,pv293], .c 5, .c 3, .p pv3 [pv2,pv11,pv11149],
  .p pv2 [pv2,pv3,pv5,pv17,pv19], .c 3, .c 5, .p pv5 [pv2,pv3,pv101,pv1619], .c 3,
  .p pv2 [pv2,pv5,pv317,pv619], .c 1181, .c 3, .c 17, .c 19, .c 3, .c 7, .c 5, .c 3, .c 13, .c 11,
  .c 3, .c 5, .c 7, .c 3, .c 53, .c 461, .c 3, .p pv3 [pv2,pv61,pv4021],
  .p pv2 [pv2,pv3,pv131,pv4993], .c 3, .c 11, .c 5, .c 3, .c 311, .c 149, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv37,pv8839], .c 3, .c 773, .c 97, .c 3, .p pv5 [pv2,pv19,pv139,pv743], .c 7,
  .c 3, .p pv2 [pv2,pv981133], .c 5, .c 3, .p pv2 [pv2,pv31,pv63299], .c 29, .c 3, .c 5, .c 11,
  .c 3, .c 163, .c 37, .c 3, .c 7, .c 23, .c 3, .c 491, .c 5, .c 3, .c 11,
]
private theorem h0479c26 : checkBlock 3924315 128 b0479c26 = true := by
  decide +kernel

private def b0479c27 : List Row := [
  .c 7, .c 3, .c 5, .c 223, .c 3, .p pv2 [pv2,pv5,pv11,pv17839], .c 13, .c 3, .c 401, .c 907,
  .c 3, .p pv3 [pv2,pv7,pv67,pv523], .c 5, .c 3, .c 7, .c 383, .c 3, .c 5, .c 1223, .c 3,
  .p pv2 [pv2,pv5,pv43,pv9127], .c 7, .c 3, .p pv3 [pv2,pv490577], .c 239, .c 3, .c 181, .c 5,
  .c 3, .c 131, .c 31, .c 3, .c 5, .c 17, .c 3, .c 7, .c 41, .c 3, .c 257,
  .p pv23 [pv2,pv3,pv7,pv13,pv599], .c 3, .c 43, .c 5, .c 3, .c 19, .c 13, .c 3, .c 5, .c 71,
  .c 3, .c 17, .c 563, .c 3, .p pv2 [pv2,pv7,pv140167], .c 11, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv17,pv47,pv307], .c 1321, .c 3, .c 5, .c 7, .c 3, .c 11, .c 53, .c 3, .c 313,
  .c 449, .c 3, .c 13, .c 5, .c 3, .p pv7 [pv2,pv7,pv280337], .p pv13 [pv2,pv3,pv5,pv23,pv79],
  .c 3, .c 5, .c 281, .c 3, .p pv2 [pv2,pv5,pv392473], .c 487, .c 3, .c 617, .c 7, .c 3, .c 23,
  .c 5, .c 3, .c 263, .c 1109, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv17,pv53], .c 3,
  .p pv3 [pv2,pv5,pv7,pv107,pv131], .c 109, .c 3, .c 7, .c 787, .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv13,pv13723], .c 7, .c 3, .c 5, .p pv11 [pv2,pv3,pv31,pv21101], .c 3, .c 13,
  .c 67, .c 3, .p pv2 [pv2,pv981199], .c 79, .c 3, .p pv2 [pv2,pv7,pv29,pv1381], .c 5, .c 3, .c 7,
  .c 11, .c 3, .c 5, .c 13, .c 3, .c 83, .c 7, .c 3,
]
private theorem h0479c27 : checkBlock 3924571 128 b0479c27 = true := by
  decide +kernel

private def b0479c28 : List Row := [
  .p pv2 [pv2,pv1962413], .c 47, .c 3, .c 11, .c 5, .c 3, .p pv7 [pv2,pv1962419], .c 17, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv218047], .c 3, .c 7, .p pv2 [pv2,pv3,pv327071], .c 3, .c 59, .c 191,
  .c 3, .p pv5 [pv2,pv53,pv61,pv607], .c 5, .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv130829], .c 3,
  .c 5, .c 11, .c 3, .c 23, .p pv3 [pv2,pv3,pv13,pv5591], .c 3, .c 19, .c 29, .c 3, .c 7, .c 5,
  .c 3, .c 11, .p pv23 [pv2,pv3,pv5,pv7,pv89], .c 3, .c 5, .c 7, .c 3, .c 43, .c 137, .c 3,
  .c 347, .c 1823, .c 3, .c 37, .c 5, .c 3, .p pv3 [pv2,pv7,pv8761],
  .p pv17 [pv2,pv3,pv5,pv41,pv3191], .c 3, .c 5, .p pv5 [pv2,pv3,pv673], .c 3, .c 31, .c 11, .c 3,
  .c 13, .c 7, .c 3, .p pv3 [pv2,pv490619], .c 5, .c 3, .p pv11 [pv2,pv149,pv13171], .c 101, .c 3,
  .c 5, .c 1753, .c 3, .c 41, .c 13, .c 3, .c 7, .c 269, .c 3, .c 421, .c 5, .c 3, .c 89, .c 7,
  .c 3, .c 5, .c 37, .c 3, .c 19, .c 31, .c 3, .c 353, .c 11, .c 3,
  .p pv2 [pv2,pv7,pv13,pv41,pv263], .c 5, .c 3, .c 7, .c 53, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv31151], .c 3, .c 11, .c 7, .c 3, .p pv2 [pv2,pv79,pv12421], .c 19, .c 3,
  .p pv2 [pv2,pv11,pv23,pv7757], .c 5, .c 3, .c 919, .c 13, .c 3, .c 5, .c 227, .c 3, .c 7, .c 29,
  .c 3, .c 593, .p pv2 [pv2,pv3,pv7,pv46727], .c 3, .c 727, .c 5, .c 3, .c 17, .c 107,
]
private theorem h0479c28 : checkBlock 3924827 128 b0479c28 = true := by
  decide +kernel

private def b0479c29 : List Row := [
  .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv59471], .c 3, .p pv7 [pv2,pv5,pv13,pv109,pv277], .c 59, .c 3,
  .c 11, .c 439, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv11,pv37,pv2411], .c 23, .c 3, .c 5, .c 7,
  .c 3, .c 29, .p pv5 [pv2,pv3,pv654187], .c 3, .c 31, .c 13, .c 3, .p pv2 [pv2,pv981283], .c 5,
  .c 3, .c 397, .c 11, .c 3, .c 5, .c 17, .c 3, .p pv19 [pv2,pv5,pv29,pv2707], .c 19, .c 3, .c 23,
  .c 7, .c 3, .c 11, .c 5, .c 3, .c 43, .p pv3 [pv2,pv3,pv5,pv43613], .c 3, .c 5,
  .p pv23 [pv2,pv3,pv41,pv3989], .c 3, .c 13, .c 653, .c 3, .c 7, .c 31, .c 3,
  .p pv3 [pv2,pv419,pv1171], .c 5, .c 3, .c 109, .c 7, .c 3, .c 5, .c 11, .c 3, .c 59,
  .p pv2 [pv2,pv3,pv43,pv7607], .c 3, .c 41, .c 37, .c 3, .p pv5 [pv2,pv7,pv280373], .c 5, .c 3,
  .c 7, .c 1879, .c 3, .c 5, .c 29, .c 3, .c 191, .c 7, .c 3, .c 599, .c 17, .c 3,
  .p pv2 [pv2,pv47,pv20879], .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv2423], .c 3, .c 5, .c 19,
  .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv981319], .p pv13 [pv2,pv3,pv7,pv31153], .c 3, .c 17,
  .c 5, .c 3, .c 61, .c 179, .c 3, .c 5, .p pv5 [pv2,pv3,pv27259], .c 3,
  .p pv2 [pv2,pv5,pv17,pv2309], .c 379, .c 3, .p pv5 [pv2,pv7,pv11,pv71,pv359],
  .p pv13 [pv2,pv3,pv109,pv3001], .c 3, .c 7, .c 5, .c 3, .c 83, .c 293, .c 3, .c 5, .c 7, .c 3,
  .c 577, .c 313, .c 3, .c 13,
]
private theorem h0479c29 : checkBlock 3925083 128 b0479c29 = true := by
  decide +kernel

private def b0479c30 : List Row := [
  .c 11, .c 3, .c 19, .c 5, .c 3, .c 647, .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv73,pv4481], .c 3,
  .c 11, .c 13, .c 3, .c 37, .c 7, .c 3, .p pv2 [pv2,pv11,pv89213], .c 5, .c 3,
  .p pv2 [pv2,pv1962689], .c 19, .c 3, .c 5, .c 23, .c 3, .p pv17 [pv2,pv5,pv7,pv8011], .c 47,
  .c 3, .c 7, .c 389, .c 3, .p pv2 [pv2,pv13,pv17,pv83,pv107], .c 5, .c 3, .c 1187, .c 7, .c 3,
  .c 5, .c 109, .c 3, .p pv2 [pv2,pv5,pv196271], .c 443, .c 3, .c 11, .c 73, .c 3, .c 23, .c 5,
  .c 3, .c 7, .c 13, .c 3, .c 5, .c 59, .c 3, .c 631, .c 7, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv218081], .c 3, .c 41, .c 5, .c 3, .c 29, .c 11, .c 3, .c 5, .c 751, .c 3,
  .c 7, .p pv5 [pv2,pv3,pv11,pv5407], .c 3, .c 17, .p pv11 [pv2,pv3,pv7,pv1669], .c 3, .c 11,
  .c 5, .c 3, .c 31, .c 1483, .c 3, .c 5, .c 113, .c 3, .c 227, .c 43, .c 3, .c 269, .c 13, .c 3,
  .c 7, .c 5, .c 3, .c 163, .c 569, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv196277], .c 173,
  .c 3, .c 151, .p pv2 [pv2,pv3,pv11,pv23,pv431], .c 3, .p pv3 [pv2,pv19,pv37,pv349], .c 5, .c 3,
  .c 11, .c 31, .c 3, .c 5, .c 101, .c 3, .c 13, .c 1709, .c 3, .c 1103, .c 7, .c 3,
  .p pv5 [pv2,pv409,pv4799], .c 5, .c 3, .c 17, .p pv3 [pv2,pv3,pv5,pv19,pv71,pv97], .c 3,
]
private theorem h0479c30 : checkBlock 3925339 128 b0479c30 = true := by
  decide +kernel

private def b0479c31 : List Row := [
  .c 5, .c 13, .c 3, .c 1721, .c 11, .c 3, .c 7, .c 19, .c 3, .p pv2 [pv2,pv89,pv11027], .c 5,
  .c 3, .c 197, .c 7, .c 3, .c 5, .c 41, .c 3, .p pv13 [pv2,pv5,pv457,pv859], .c 499, .c 3,
  .p pv2 [pv2,pv11,pv13,pv6863], .c 103, .c 3, .c 29, .c 5, .c 3, .c 7, .c 83, .c 3, .c 5, .c 17,
  .c 3, .c 71, .c 7, .c 3, .p pv2 [pv2,pv19,pv103307], .c 11, .c 3, .c 199, .c 5, .c 3, .c 661,
  .c 839, .c 3, .c 5, .c 97, .c 3, .c 7, .p pv2 [pv2,pv3,pv163,pv223], .c 3, .c 127,
  .p pv2 [pv2,pv3,pv7,pv151,pv619], .c 3, .c 149, .c 5, .c 3, .c 23, .c 1447, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv31,pv61,pv173], .c 3, .c 73, .c 19, .c 3, .c 13, .p pv7 [pv2,pv3,pv43,pv317],
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv227,pv8647], .p pv19 [pv2,pv3,pv5,pv7,pv13,pv719], .c 3,
  .c 5, .c 7, .c 3, .p pv11 [pv2,pv5,pv41,pv383], .c 13, .c 3, .c 11, .c 17, .c 3, .c 53, .c 5,
  .c 3, .c 47, .c 43, .c 3, .c 5, .c 61, .c 3, .p pv2 [pv2,pv5,pv19,pv10331],
  .p pv3 [pv2,pv3,pv7,pv4451], .c 3, .c 863, .c 7, .c 3, .c 17, .c 5, .c 3, .c 19, .c 11, .c 3,
  .c 5, .p pv7 [pv2,pv3,pv654301], .c 3, .c 37, .c 193, .c 3, .c 7, .c 547, .c 3, .c 11, .c 5,
  .c 3, .p pv2 [pv2,pv179,pv5483], .c 7, .c 3, .c 5, .c 19, .c 3, .p pv7 [pv2,pv5,pv31,pv1583],
  .p pv2 [pv2,pv3,pv654307], .c 3, .c 23, .c 151,
]
private theorem h0479c31 : checkBlock 3925595 128 b0479c31 = true := by
  decide +kernel

def rows0479 : List Row :=
  b0479c00 ++ b0479c01 ++ b0479c02 ++ b0479c03 ++ b0479c04 ++ b0479c05 ++ b0479c06 ++ b0479c07 ++
  b0479c08 ++ b0479c09 ++ b0479c10 ++ b0479c11 ++ b0479c12 ++ b0479c13 ++ b0479c14 ++ b0479c15 ++
  b0479c16 ++ b0479c17 ++ b0479c18 ++ b0479c19 ++ b0479c20 ++ b0479c21 ++ b0479c22 ++ b0479c23 ++
  b0479c24 ++ b0479c25 ++ b0479c26 ++ b0479c27 ++ b0479c28 ++ b0479c29 ++ b0479c30 ++ b0479c31

theorem checked0479 : checkBlock 3917659 4096 rows0479 = true :=
  checkBlock_append h0479c00 (
    checkBlock_append h0479c01 (
    checkBlock_append h0479c02 (
    checkBlock_append h0479c03 (
    checkBlock_append h0479c04 (
    checkBlock_append h0479c05 (
    checkBlock_append h0479c06 (
    checkBlock_append h0479c07 (
    checkBlock_append h0479c08 (
    checkBlock_append h0479c09 (
    checkBlock_append h0479c10 (
    checkBlock_append h0479c11 (
    checkBlock_append h0479c12 (
    checkBlock_append h0479c13 (
    checkBlock_append h0479c14 (
    checkBlock_append h0479c15 (
    checkBlock_append h0479c16 (
    checkBlock_append h0479c17 (
    checkBlock_append h0479c18 (
    checkBlock_append h0479c19 (
    checkBlock_append h0479c20 (
    checkBlock_append h0479c21 (
    checkBlock_append h0479c22 (
    checkBlock_append h0479c23 (
    checkBlock_append h0479c24 (
    checkBlock_append h0479c25 (
    checkBlock_append h0479c26 (
    checkBlock_append h0479c27 (
    checkBlock_append h0479c28 (
    checkBlock_append h0479c29 (
    checkBlock_append h0479c30 (
    h0479c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
