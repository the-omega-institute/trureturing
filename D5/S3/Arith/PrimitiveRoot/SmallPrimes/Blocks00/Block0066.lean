/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks00/Block0066
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks00/Block0066.checked0066
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table013
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table016
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table022
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table034
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table035
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table080

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0066c00 : List Row := [
  .c 3, .p pv2 [pv2,pv29,pv59,pv79], .p pv17 [pv2,pv3,pv97,pv929], .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv47,pv719], .p pv2 [pv2,pv3,pv5,pv67,pv269], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv1733], .c 3, .c 7, .p pv3 [pv2,pv3,pv17,pv19,pv31], .c 3, .c 23, .c 13,
  .c 3, .p pv3 [pv2,pv67589], .c 5, .c 3, .c 17, .c 19, .c 3, .c 5, .c 11, .c 3, .c 151, .c 31,
  .c 3, .c 571, .c 137, .c 3, .c 7, .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv7,pv103], .c 3, .c 5,
  .c 7, .c 3, .c 13, .c 29, .c 3, .c 631, .p pv13 [pv2,pv3,pv43,pv131], .c 3,
  .p pv2 [pv2,pv135193], .c 5, .c 3, .p pv2 [pv2,pv7,pv19,pv107], .p pv2 [pv2,pv3,pv5,pv9013],
  .c 3, .c 5, .c 13, .c 3, .c 479, .c 11, .c 3, .c 19, .c 7, .c 3, .p pv2 [pv2,pv317,pv853], .c 5,
  .c 3, .p pv3 [pv2,pv67601], .c 43, .c 3, .c 5, .c 433, .c 3, .c 17,
  .p pv5 [pv2,pv3,pv23,pv3919], .c 3, .c 7, .c 37, .c 3, .c 379, .c 5, .c 3, .c 13, .c 7, .c 3,
  .c 5, .c 557, .c 3, .p pv2 [pv2,pv5,pv29,pv373], .c 59, .c 3, .c 31, .c 11, .c 3,
  .p pv5 [pv2,pv7,pv5519], .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv11,pv149], .c 3, .c 5,
  .p pv53 [pv2,pv3,pv7,pv47,pv137], .c 3, .c 11, .c 7, .c 3, .c 61, .c 17, .c 3, .c 127, .c 5,
  .c 3, .c 131, .p pv2 [pv2,pv3,pv5,pv601], .c 3, .c 5, .p pv3 [pv2,pv3,pv17,pv5303], .c 3, .c 7,
  .c 41, .c 3, .c 13, .c 31, .c 3, .c 17, .c 5, .c 3, .c 419,
]
private theorem h0066c00 : checkBlock 540675 128 b0066c00 = true := by
  decide +kernel

private def b0066c01 : List Row := [
  .c 113, .c 3, .c 5, .c 23, .c 3, .c 227, .c 13, .c 3, .c 11, .c 19, .c 3, .c 7, .c 5, .c 3,
  .c 269, .p pv13 [pv2,pv3,pv5,pv7,pv23], .c 3, .c 5, .c 7, .c 3, .c 53, .c 347, .c 3, .c 37,
  .c 193, .c 3, .c 23, .c 5, .c 3, .p pv3 [pv2,pv7,pv139], .c 11, .c 3, .c 5, .c 163, .c 3,
  .p pv3 [pv2,pv5,pv541], .c 73, .c 3, .p pv5 [pv2,pv19,pv23,pv619], .c 7, .c 3, .c 11, .c 5,
  .c 3, .c 149, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv43,pv233], .c 3, .c 89, .c 151, .c 3, .c 7,
  .c 659, .c 3, .c 31, .c 5, .c 3, .p pv3 [pv2,pv67631], .c 7, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv13,pv2081], .c 19, .c 3, .c 509, .c 43, .c 3, .c 13, .c 5, .c 3, .c 7, .c 199,
  .c 3, .c 5, .p pv19 [pv2,pv3,pv7,pv13,pv991], .c 3, .c 71, .c 7, .c 3, .p pv3 [pv2,pv239,pv283],
  .c 13, .c 3, .c 191, .c 5, .c 3, .c 617, .c 29, .c 3, .c 5, .c 179, .c 3, .c 7, .c 11, .c 3,
  .c 17, .p pv11 [pv2,pv3,pv7,pv3221], .c 3, .p pv2 [pv2,pv135283], .c 5, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv5,pv29,pv311], .c 3, .c 5, .c 127, .c 3, .c 13, .p pv5 [pv2,pv3,pv1879], .c 3,
  .c 113, .c 41, .c 3, .c 7, .c 5, .c 3, .c 29, .c 293, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv27059], .c 53, .c 3,
]
private theorem h0066c01 : checkBlock 540931 128 b0066c01 = true := by
  decide +kernel

private def b0066c02 : List Row := [
  .c 271, .c 11, .c 3, .p pv3 [pv2,pv61,pv1109], .c 5, .c 3, .c 37,
  .p pv17 [pv2,pv3,pv5,pv11,pv41], .c 3, .c 5, .c 59, .c 3, .c 11, .c 23, .c 3,
  .p pv3 [pv2,pv13,pv1301], .c 7, .c 3, .c 373, .c 5, .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv18041],
  .c 3, .c 5, .p pv5 [pv2,pv3,pv23,pv37,pv53], .c 3, .c 41, .c 83, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv2819], .c 3, .c 19, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv59,pv139], .c 3, .p pv11 [pv2,pv5,pv113,pv479], .c 37, .c 3, .c 11,
  .c 613, .c 3, .p pv2 [pv2,pv7,pv23,pv41], .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 17, .c 3,
  .p pv3 [pv2,pv5,pv5413], .c 7, .c 3, .c 13, .p pv2 [pv2,pv3,pv79,pv571], .c 3, .c 107, .c 5,
  .c 3, .c 521, .c 11, .c 3, .c 5, .c 43, .c 3, .c 7, .c 13, .c 3, .c 653,
  .p pv7 [pv2,pv3,pv7,pv12889], .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv17,pv19,pv419], .c 23,
  .c 3, .c 5, .c 97, .c 3, .p pv3 [pv2,pv5,pv67,pv101], .p pv3 [pv2,pv3,pv90227], .c 3, .c 19,
  .p pv7 [pv2,pv3,pv73,pv103], .c 3, .c 7, .c 5, .c 3, .c 283, .p pv41 [pv2,pv3,pv5,pv7,pv1289],
  .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv54139], .c 47, .c 3, .c 23, .c 17, .c 3, .c 109, .c 5,
  .c 3, .c 11, .c 13, .c 3, .c 5, .p pv11 [pv2,pv3,pv17,pv1327], .c 3, .c 37, .c 131, .c 3, .c 67,
  .c 7, .c 3, .c 17, .c 5, .c 3, .p pv13 [pv2,pv270719], .c 73,
]
private theorem h0066c02 : checkBlock 541187 128 b0066c02 = true := by
  decide +kernel

private def b0066c03 : List Row := [
  .c 3, .c 5, .p pv7 [pv2,pv3,pv31,pv41,pv71], .c 3, .c 311, .c 11, .c 3, .c 7, .c 29, .c 3,
  .c 13, .c 5, .c 3, .p pv2 [pv2,pv135367], .c 7, .c 3, .c 5, .c 31, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv90247], .c 3, .c 41, .c 13, .c 3, .c 157, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv12893], .c 3, .p pv11 [pv2,pv5,pv54151], .c 7, .c 3, .c 29, .c 11, .c 3,
  .p pv2 [pv2,pv270761], .c 5, .c 3, .p pv3 [pv2,pv13,pv41,pv127],
  .p pv7 [pv2,pv3,pv5,pv11,pv547], .c 3, .c 5, .p pv11 [pv2,pv3,pv5641], .c 3, .c 7,
  .p pv3 [pv2,pv3,pv43,pv2099], .c 3, .p pv2 [pv2,pv29,pv9337], .p pv13 [pv2,pv3,pv7,pv307], .c 3,
  .c 197, .c 5, .c 3, .c 337, .c 59, .c 3, .c 5, .c 13, .c 3, .p pv7 [pv2,pv5,pv31,pv1747],
  .c 491, .c 3, .p pv5 [pv2,pv7,pv19,pv509], .p pv2 [pv2,pv3,pv90263], .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv71,pv1907], .c 379, .c 3, .c 5, .c 7, .c 3, .c 31, .c 17, .c 3, .c 11, .c 113,
  .c 3, .p pv2 [pv2,pv135403], .c 5, .c 3, .c 13, .c 109, .c 3, .c 5, .c 23, .c 3,
  .p pv19 [pv2,pv5,pv54163], .c 19, .c 3, .c 17, .c 7, .c 3, .c 37, .c 5, .c 3, .c 163, .c 11,
  .c 3, .c 5, .p pv23 [pv2,pv3,pv7523], .c 3, .p pv2 [pv2,pv5,pv7,pv53,pv73], .c 31, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv45139], .c 3, .c 11, .c 5, .c 3, .c 59, .c 7, .c 3, .c 5, .c 733, .c 3,
  .c 29, .p pv2 [pv2,pv3,pv41,pv367], .c 3, .c 13,
]
private theorem h0066c03 : checkBlock 541443 128 b0066c03 = true := by
  decide +kernel

private def b0066c04 : List Row := [
  .p pv2 [pv2,pv3,pv137,pv659], .c 3, .c 79, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv13,pv463],
  .c 3, .c 5, .c 11, .c 3, .p pv13 [pv2,pv5,pv29,pv467], .c 7, .c 3, .p pv5 [pv2,pv439,pv617],
  .c 271, .c 3, .c 41, .c 5, .c 3, .c 11, .c 61, .c 3, .c 5, .c 19, .c 3, .c 7, .c 317, .c 3,
  .c 43, .p pv3 [pv2,pv3,pv7,pv12899], .c 3, .p pv5 [pv2,pv13,pv67,pv311], .c 5, .c 3, .c 47,
  .p pv2 [pv2,pv3,pv5,pv18059], .c 3, .c 5, .p pv5 [pv2,pv3,pv11287], .c 3,
  .p pv2 [pv2,pv5,pv103,pv263], .c 11, .c 3, .c 31, .c 443, .c 3, .c 7, .c 5, .c 3,
  .p pv11 [pv2,pv270899], .c 13, .c 3, .c 5, .c 7, .c 3, .c 23, .c 239, .c 3,
  .p pv3 [pv2,pv11,pv47,pv131], .c 53, .c 3, .c 19, .c 5, .c 3, .c 67,
  .p pv3 [pv2,pv3,pv5,pv18061], .c 3, .c 5, .p pv5 [pv2,pv3,pv29,pv173], .c 3, .c 17, .c 43, .c 3,
  .c 331, .c 7, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv17,pv15937], .c 19, .c 3, .c 5, .c 191,
  .c 3, .c 11, .c 701, .c 3, .c 7, .c 13, .c 3, .c 103, .c 5, .c 3, .p pv3 [pv2,pv8467], .c 7,
  .c 3, .c 5, .c 41, .c 3, .p pv2 [pv2,pv5,pv5419], .c 23, .c 3, .c 83, .c 17, .c 3, .c 149, .c 5,
  .c 3, .c 7, .c 89, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv11,pv17,pv23], .c 3, .c 13, .c 7, .c 3,
  .c 11, .c 37, .c 3, .c 17, .c 5, .c 3, .c 23, .p pv7 [pv2,pv3,pv5,pv3613], .c 3,
]
private theorem h0066c04 : checkBlock 541699 128 b0066c04 = true := by
  decide +kernel

private def b0066c05 : List Row := [
  .c 5, .c 13, .c 3, .c 7, .c 67, .c 3, .p pv5 [pv2,pv101,pv2683], .c 373, .c 3, .c 31, .c 5,
  .c 3, .c 41, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv103,pv877], .c 3, .p pv7 [pv2,pv5,pv83,pv653],
  .p pv5 [pv2,pv3,pv11,pv2053], .c 3, .c 349, .p pv17 [pv2,pv3,pv10037], .c 3, .c 7, .c 5, .c 3,
  .c 13, .c 17, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv41,pv661], .p pv3 [pv2,pv3,pv13,pv6949],
  .c 3, .p pv2 [pv2,pv271013], .c 631, .c 3, .c 59, .c 5, .c 3, .c 29, .c 23, .c 3, .c 5, .c 11,
  .c 3, .c 19, .p pv2 [pv2,pv3,pv7,pv239], .c 3, .c 109, .c 7, .c 3,
  .p pv5 [pv2,pv17,pv107,pv149], .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv19,pv317], .c 3, .c 5,
  .c 547, .c 3, .p pv23 [pv2,pv5,pv7,pv11], .p pv2 [pv2,pv3,pv167,pv541], .c 3, .c 7, .c 19, .c 3,
  .p pv2 [pv2,pv59,pv2297], .c 5, .c 3, .c 89, .c 7, .c 3, .c 5, .c 61, .c 3,
  .p pv11 [pv2,pv5,pv23,pv2357], .c 11, .c 3, .p pv2 [pv2,pv313,pv433], .p pv3 [pv2,pv3,pv90353],
  .c 3, .p pv2 [pv2,pv7,pv38723], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv17,pv1063], .c 3, .c 5,
  .c 53, .c 3, .p pv3 [pv2,pv5,pv27107], .c 7, .c 3, .c 17, .p pv7 [pv2,pv3,pv45179], .c 3,
  .p pv3 [pv2,pv13,pv401], .c 5, .c 3, .c 31, .c 37, .c 3, .c 5, .p pv3 [pv2,pv3,pv109,pv829],
  .c 3, .c 7, .c 463, .c 3, .c 79, .c 11, .c 3, .p pv5 [pv2,pv173,pv1567], .c 5, .c 3,
  .p pv2 [pv2,pv89,pv1523], .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv15061], .c 3, .c 11, .c 19, .c 3,
  .p pv5 [pv2,pv7,pv38729], .c 131,
]
private theorem h0066c05 : checkBlock 541955 128 b0066c05 = true := by
  decide +kernel

private def b0066c06 : List Row := [
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv271109], .c 31, .c 3, .c 5, .c 7, .c 3, .c 67, .c 337,
  .c 3, .p pv2 [pv2,pv135559], .c 47, .c 3, .c 13, .c 5, .c 3, .c 17, .p pv13 [pv2,pv3,pv5,pv241],
  .c 3, .c 5, .c 569, .c 3, .p pv2 [pv2,pv5,pv19,pv1427], .p pv5 [pv2,pv3,pv7,pv12911], .c 3,
  .c 11, .c 7, .c 3, .c 43, .c 5, .c 3, .c 19, .p pv7 [pv2,pv3,pv5,pv4519], .c 3, .c 5, .c 113,
  .c 3, .c 239, .p pv2 [pv2,pv3,pv45191], .c 3, .c 7, .p pv2 [pv2,pv3,pv19,pv67,pv71], .c 3,
  .c 227, .c 5, .c 3, .c 37, .c 7, .c 3, .c 5, .c 17, .c 3, .c 13, .p pv2 [pv2,pv3,pv11,pv83],
  .c 3, .c 97, .c 29, .c 3, .c 11, .c 5, .c 3, .c 7, .c 197, .c 3, .c 5, .c 13, .c 3, .c 17, .c 7,
  .c 3, .c 659, .c 43, .c 3, .c 23, .c 5, .c 3, .c 71, .p pv3 [pv2,pv3,pv5,pv101,pv179], .c 3,
  .c 5, .c 11, .c 3, .c 7, .c 37, .c 3, .c 29, .c 41, .c 3, .c 19, .c 5, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv5,pv113], .c 3, .c 5, .c 31, .c 3, .c 251, .c 499, .c 3, .c 127, .c 17, .c 3,
  .c 7, .c 5, .c 3, .c 313, .c 19, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv71,pv191], .c 11,
  .c 3, .p pv5 [pv2,pv59,pv4597], .c 359, .c 3, .c 17, .c 5, .c 3, .c 457,
  .p pv7 [pv2,pv3,pv5,pv9041], .c 3, .c 5,
]
private theorem h0066c06 : checkBlock 542211 128 b0066c06 = true := by
  decide +kernel

private def b0066c07 : List Row := [
  .p pv2 [pv2,pv3,pv30137], .c 3, .c 41, .c 61, .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv271241],
  .c 5, .c 3, .p pv3 [pv2,pv19,pv43,pv83], .c 241, .c 3, .c 5, .p pv5 [pv2,pv3,pv5651], .c 3,
  .c 23, .c 13, .c 3, .c 7, .c 11, .c 3, .c 113, .c 5, .c 3, .p pv23 [pv2,pv487,pv557], .c 7,
  .c 3, .c 5, .c 257, .c 3, .c 11, .p pv2 [pv2,pv3,pv29,pv1559], .c 3, .p pv3 [pv2,pv73,pv929],
  .p pv2 [pv2,pv3,pv17,pv197], .c 3, .c 151, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv3617], .c 3,
  .c 5, .p pv2 [pv2,pv3,pv7,pv2153], .c 3, .c 29, .c 7, .c 3, .p pv5 [pv2,pv67,pv4049], .c 263,
  .c 3, .c 269, .c 5, .c 3, .p pv2 [pv2,pv271289], .c 13, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv8221], .c 3, .c 7, .c 23, .c 3, .c 11, .p pv3 [pv2,pv3,pv7,pv12919],
  .c 3, .p pv2 [pv2,pv19,pv109,pv131], .c 5, .c 3, .c 73, .c 281, .c 3, .c 5, .c 43, .c 3, .c 19,
  .c 17, .c 3, .c 163, .c 431, .c 3, .c 7, .c 5, .c 3, .c 23, .c 11, .c 3, .c 5, .c 7, .c 3,
  .c 79, .c 71, .c 3, .c 17, .c 13, .c 3, .c 11, .c 5, .c 3, .c 421, .c 127, .c 3, .c 5, .c 29,
  .c 3, .c 661, .p pv2 [pv2,pv3,pv7,pv59,pv73], .c 3, .p pv5 [pv2,pv31,pv8753], .c 7, .c 3,
  .p pv2 [pv2,pv211,pv643], .c 5, .c 3, .c 397, .c 173, .c 3, .c 5, .c 11, .c 3, .c 13,
  .p pv5 [pv2,pv3,pv22613], .c 3, .c 7, .p pv7 [pv2,pv3,pv11,pv2741], .c 3,
]
private theorem h0066c07 : checkBlock 542467 128 b0066c07 = true := by
  decide +kernel

private def b0066c08 : List Row := [
  .p pv2 [pv2,pv89,pv3049], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 13, .c 3, .c 59, .c 409, .c 3,
  .p pv2 [pv2,pv43,pv6311], .c 157, .c 3, .c 37, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv4523],
  .c 3, .c 5, .c 67, .c 3, .p pv2 [pv2,pv5,pv54277], .c 7, .c 3, .c 23, .c 31, .c 3,
  .p pv5 [pv2,pv223,pv1217], .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv37,pv163], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv45233], .c 3, .c 7, .c 47, .c 3, .c 149, .c 79, .c 3, .c 271, .c 5, .c 3,
  .c 181, .p pv2 [pv2,pv3,pv5,pv83,pv109], .c 3, .c 5, .c 17, .c 3, .p pv7 [pv2,pv5,pv19,pv2857],
  .c 647, .c 3, .p pv2 [pv2,pv7,pv19387], .c 11, .c 3, .c 7, .c 5, .c 3, .c 19, .c 29, .c 3, .c 5,
  .c 7, .c 3, .c 11, .c 619, .c 3, .c 13, .c 23, .c 3, .p pv5 [pv2,pv11,pv31,pv199], .c 5, .c 3,
  .c 53, .c 41, .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv233], .c 13, .c 3, .c 47, .c 7, .c 3,
  .c 31, .c 5, .c 3, .c 29, .p pv3 [pv2,pv3,pv5,pv18097], .c 3, .c 5, .c 167, .c 3,
  .p pv13 [pv2,pv5,pv7,pv277], .p pv2 [pv2,pv3,pv41,pv2207], .c 3, .c 7, .c 17, .c 3,
  .p pv2 [pv2,pv13,pv53,pv197], .c 5, .c 3, .p pv11 [pv2,pv11,pv23,pv29,pv37], .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv17,pv5323], .c 3, .p pv13 [pv2,pv5,pv10859], .c 163, .c 3, .c 577, .c 229,
  .c 3, .c 17, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 59,
]
private theorem h0066c08 : checkBlock 542723 128 b0066c08 = true := by
  decide +kernel

private def b0066c09 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv17,pv1597], .c 7, .c 3, .p pv2 [pv2,pv83,pv3271], .c 89, .c 3, .c 11,
  .c 5, .c 3, .p pv7 [pv2,pv271499], .c 19, .c 3, .c 5, .c 23, .c 3, .c 7, .c 191, .c 3,
  .p pv3 [pv2,pv103,pv659], .p pv3 [pv2,pv3,pv7,pv1847], .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv135757], .c 17, .c 3, .c 5, .c 11, .c 3, .c 257, .c 439, .c 3, .c 43, .c 13, .c 3,
  .c 7, .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv7,pv431], .c 3, .c 5, .c 7, .c 3, .c 199, .c 139,
  .c 3, .c 19, .c 71, .c 3, .c 29, .c 5, .c 3, .c 31, .c 53, .c 3, .c 5,
  .p pv29 [pv2,pv3,pv19,pv397], .c 3, .c 13, .c 11, .c 3, .c 379, .c 7, .c 3,
  .p pv3 [pv2,pv29,pv2341], .c 5, .c 3, .c 103, .c 467, .c 3, .c 5, .c 13, .c 3,
  .p pv2 [pv2,pv5,pv7,pv7759], .c 17, .c 3, .c 7, .p pv3 [pv2,pv3,pv90523], .c 3,
  .p pv5 [pv2,pv271571], .c 5, .c 3, .p pv2 [pv2,pv135787], .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv45263], .c 3, .p pv3 [pv2,pv5,pv37,pv367], .p pv2 [pv2,pv3,pv90527], .c 3,
  .c 17, .c 11, .c 3, .c 281, .c 5, .c 3, .c 7, .c 181, .c 3, .c 5, .p pv7 [pv2,pv3,pv7,pv479],
  .c 3, .c 11, .c 7, .c 3, .c 37, .c 29, .c 3, .p pv2 [pv2,pv11,pv24691], .c 5, .c 3, .c 41,
  .c 227, .c 3, .c 5, .p pv7 [pv2,pv3,pv11317], .c 3, .c 7, .p pv3 [pv2,pv3,pv103,pv293], .c 3,
  .p pv2 [pv2,pv47,pv5779], .c 19, .c 3, .p pv3 [pv2,pv1061],
]
private theorem h0066c09 : checkBlock 542979 128 b0066c09 = true := by
  decide +kernel

private def b0066c10 : List Row := [
  .c 5, .c 3, .c 107, .p pv17 [pv2,pv3,pv5,pv503], .c 3, .c 5, .c 239, .c 3, .c 167,
  .p pv2 [pv2,pv3,pv17,pv2663], .c 3, .c 11, .p pv2 [pv2,pv3,pv30181], .c 3, .c 7, .c 5, .c 3,
  .c 17, .c 37, .c 3, .c 5, .c 7, .c 3, .p pv11 [pv2,pv5,pv6791], .c 13, .c 3,
  .p pv5 [pv2,pv17,pv19,pv29], .p pv11 [pv2,pv3,pv22637], .c 3, .c 599, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv151,pv257], .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv23,pv31,pv127], .c 3,
  .p pv13 [pv2,pv5,pv54331], .p pv5 [pv2,pv3,pv7,pv11], .c 3, .c 311, .c 7, .c 3, .c 11, .c 5,
  .c 3, .c 23, .c 59, .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv7,pv3881], .c 19, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv13,pv43], .c 3, .p pv3 [pv2,pv23,pv2953], .c 5, .c 3,
  .p pv11 [pv2,pv263,pv1033], .c 7, .c 3, .c 5, .c 11, .c 3, .c 17, .c 29, .c 3, .c 157,
  .p pv3 [pv2,pv3,pv11,pv8233], .c 3, .p pv7 [pv2,pv7,pv37,pv1049], .c 5, .c 3, .c 7, .c 43, .c 3,
  .c 5, .c 523, .c 3, .c 83, .c 7, .c 3, .p pv5 [pv2,pv271703], .c 53, .c 3, .c 13, .c 5, .c 3,
  .c 19, .c 23, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv6967], .c 3, .c 7, .c 11, .c 3, .c 67, .c 13,
  .c 3, .c 419, .c 5, .c 3, .c 59, .c 223, .c 3, .c 5, .c 19, .c 3, .c 31,
  .p pv3 [pv2,pv3,pv53,pv1709], .c 3, .c 23, .c 199, .c 3, .c 7, .c 5, .c 3, .c 137, .c 101, .c 3,
  .c 5, .c 7, .c 3,
]
private theorem h0066c10 : checkBlock 543235 128 b0066c10 = true := by
  decide +kernel

private def b0066c11 : List Row := [
  .c 13, .c 37, .c 3, .p pv3 [pv2,pv41,pv1657], .c 11, .c 3, .p pv5 [pv2,pv331,pv821], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv47,pv59], .c 421, .c 3, .c 5, .c 13, .c 3, .c 11, .c 31, .c 3, .c 367, .c 7,
  .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv271769], .c 17, .c 3, .c 5, .c 29, .c 3,
  .p pv17 [pv2,pv5,pv7,pv1553], .p pv5 [pv2,pv3,pv19,pv149], .c 3, .c 7, .c 23, .c 3, .c 43, .c 5,
  .c 3, .c 13, .c 7, .c 3, .c 5, .c 617, .c 3, .c 337, .c 109, .c 3, .c 11, .c 233, .c 3,
  .p pv3 [pv2,pv7,pv17,pv571], .c 5, .c 3, .c 7, .p pv47 [pv2,pv3,pv5,pv151], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv43], .c 3, .p pv2 [pv2,pv5,pv54361], .c 7, .c 3, .p pv3 [pv2,pv31,pv137],
  .c 41, .c 3, .c 179, .c 5, .c 3, .c 139, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv15101], .c 3,
  .c 7, .c 17, .c 3, .c 13, .c 43, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv271829],
  .p pv2 [pv2,pv3,pv5,pv13,pv17,pv41], .c 3, .c 5, .c 107, .c 3, .p pv7 [pv2,pv5,pv54367], .c 13,
  .c 3, .c 17, .p pv3 [pv2,pv3,pv31,pv37,pv79], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv67961],
  .c 157, .c 3, .c 5, .c 7, .c 3, .c 41, .p pv3 [pv2,pv3,pv90617], .c 3, .p pv2 [pv2,pv271853],
  .c 31, .c 3, .p pv3 [pv2,pv13,pv1307], .c 5, .c 3, .c 11, .c 29, .c 3, .c 5, .c 53, .c 3,
  .c 613, .c 83, .c 3, .c 103, .c 7, .c 3, .c 23, .c 5,
]
private theorem h0066c11 : checkBlock 543491 128 b0066c11 = true := by
  decide +kernel

private def b0066c12 : List Row := [
  .c 3, .c 347, .c 13, .c 3, .c 5, .c 79, .c 3, .c 19, .c 11, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv139,pv163], .c 3, .p pv2 [pv2,pv67,pv2029], .c 5, .c 3, .c 17, .c 7, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv90631], .c 3, .p pv17 [pv2,pv5,pv13,pv47,pv89],
  .p pv5 [pv2,pv3,pv11329], .c 3, .p pv3 [pv2,pv11,pv17,pv727], .c 19, .c 3, .c 13, .c 5, .c 3,
  .c 7, .p pv3 [pv2,pv3,pv5,pv18127], .c 3, .c 5, .c 691, .c 3, .c 43, .c 7, .c 3,
  .p pv2 [pv2,pv37,pv7349], .c 11, .c 3, .c 31, .c 5, .c 3, .c 67,
  .p pv53 [pv2,pv3,pv5,pv11,pv103], .c 3, .c 5, .c 17, .c 3, .c 7, .p pv2 [pv2,pv3,pv15107], .c 3,
  .p pv3 [pv2,pv19,pv1789], .p pv7 [pv2,pv3,pv7,pv23,pv563], .c 3, .c 37, .c 5, .c 3, .c 113,
  .p pv23 [pv2,pv3,pv5,pv6043], .c 3, .c 5, .p pv7 [pv2,pv3,pv61,pv743], .c 3, .c 13,
  .p pv5 [pv2,pv3,pv90647], .c 3, .p pv7 [pv2,pv7,pv53,pv733], .p pv7 [pv2,pv3,pv1259], .c 3,
  .c 7, .c 5, .c 3, .c 83, .p pv2 [pv2,pv3,pv5,pv7,pv37], .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv109,pv499], .c 19, .c 3, .c 11, .c 167, .c 3, .c 73, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv11,pv883], .c 47, .c 3, .c 5, .c 37, .c 3, .c 127, .c 103, .c 3, .c 41, .c 7,
  .c 3, .c 29, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .p pv7 [pv2,pv3,pv17,pv5333], .c 3,
  .p pv2 [pv2,pv5,pv7,pv19,pv409], .c 23, .c 3, .c 7, .c 487, .c 3, .c 11, .c 5, .c 3, .c 19,
  .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv23,pv73], .c 3, .p pv3 [pv2,pv5,pv17],
]
private theorem h0066c12 : checkBlock 543747 128 b0066c12 = true := by
  decide +kernel

private def b0066c13 : List Row := [
  .c 661, .c 3, .p pv5 [pv2,pv272003], .p pv29 [pv2,pv3,pv19,pv1193], .c 3,
  .p pv2 [pv2,pv7,pv19429], .c 5, .c 3, .c 7, .p pv19 [pv2,pv3,pv5,pv9067], .c 3, .c 5, .c 11,
  .c 3, .p pv13 [pv2,pv5,pv54403], .c 7, .c 3, .c 13, .c 59, .c 3, .c 131, .c 5, .c 3, .c 11,
  .c 17, .c 3, .c 5, .c 89, .c 3, .c 7, .c 13, .c 3, .c 193, .c 29, .c 3, .c 71, .c 5, .c 3,
  .c 43, .c 31, .c 3, .c 5, .c 101, .c 3, .c 349, .c 11, .c 3, .p pv3 [pv2,pv7,pv347],
  .p pv2 [pv2,pv3,pv29,pv53,pv59], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv136027], .c 23, .c 3,
  .c 5, .c 7, .c 3, .c 509, .p pv2 [pv2,pv3,pv19,pv37,pv43], .c 3, .c 29,
  .p pv7 [pv2,pv3,pv13,pv109], .c 3, .p pv2 [pv2,pv136033], .c 5, .c 3, .p pv2 [pv2,pv7,pv38867],
  .c 13, .c 3, .c 5, .c 263, .c 3, .c 53, .c 17, .c 3, .c 23, .c 7, .c 3, .c 571, .c 5, .c 3,
  .c 211, .p pv19 [pv2,pv3,pv5,pv11,pv17,pv97], .c 3, .c 5, .p pv5 [pv2,pv3,pv3779], .c 3, .c 11,
  .p pv5 [pv2,pv3,pv90697], .c 3, .c 7, .c 557, .c 3, .c 13, .c 5, .c 3,
  .p pv13 [pv2,pv19,pv14321], .c 7, .c 3, .c 5, .c 373, .c 3, .c 389, .c 47, .c 3, .c 19, .c 13,
  .c 3, .p pv5 [pv2,pv7,pv38873], .c 5, .c 3, .c 7, .c 79, .c 3, .c 5, .c 109, .c 3, .c 67, .c 7,
  .c 3, .c 11, .c 23, .c 3, .c 167, .c 5, .c 3,
]
private theorem h0066c13 : checkBlock 544003 128 b0066c13 = true := by
  decide +kernel

private def b0066c14 : List Row := [
  .p pv2 [pv2,pv11,pv13,pv173], .c 367, .c 3, .c 5, .c 31, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv17,pv23,pv29], .c 3, .p pv2 [pv2,pv136069], .p pv7 [pv2,pv3,pv7,pv12959],
  .c 3, .c 719, .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .c 13, .c 3, .c 29, .c 61, .c 3, .c 37,
  .c 107, .c 3, .c 7, .c 5, .c 3, .c 157, .c 113, .c 3, .c 5, .c 7, .c 3, .c 19, .c 229, .c 3,
  .c 43, .c 179, .c 3, .c 223, .c 5, .c 3, .c 13, .c 683, .c 3, .c 5, .c 11, .c 3, .c 73, .c 53,
  .c 3, .p pv5 [pv2,pv272183], .c 7, .c 3, .p pv2 [pv2,pv136093], .c 5, .c 3, .c 11, .c 37, .c 3,
  .c 5, .c 23, .c 3, .c 17, .c 59, .c 3, .c 7, .p pv3 [pv2,pv3,pv41,pv2213], .c 3,
  .p pv2 [pv2,pv272201], .c 5, .c 3, .c 499, .c 7, .c 3, .c 5, .c 29, .c 3, .c 563, .c 11, .c 3,
  .c 13, .p pv11 [pv2,pv3,pv71], .c 3, .c 23, .c 5, .c 3, .c 7, .c 461, .c 3, .c 5, .c 443, .c 3,
  .p pv2 [pv2,pv5,pv10889], .c 7, .c 3, .c 673, .c 17, .c 3, .c 139, .c 5, .c 3, .c 53,
  .p pv11 [pv2,pv3,pv5,pv18149], .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv157], .c 3, .c 7, .c 19, .c 3,
  .p pv5 [pv2,pv61,pv4463], .c 11, .c 3, .c 17, .c 5, .c 3, .c 71, .p pv2 [pv2,pv3,pv5,pv11],
  .c 3, .c 5, .c 73, .c 3, .c 11, .p pv5 [pv2,pv3,pv709],
]
private theorem h0066c14 : checkBlock 544259 128 b0066c14 = true := by
  decide +kernel

private def b0066c15 : List Row := [
  .c 3, .p pv2 [pv2,pv7,pv19447], .c 491, .c 3, .c 7, .c 5, .c 3, .c 37, .c 13, .c 3, .c 5, .c 7,
  .c 3, .c 191, .p pv3 [pv2,pv3,pv47,pv1931], .c 3, .c 61, .p pv7 [pv2,pv3,pv23,pv1973], .c 3,
  .c 631, .c 5, .c 3, .c 19, .c 17, .c 3, .c 5, .c 131, .c 3, .c 23, .c 227, .c 3, .c 11, .c 7,
  .c 3, .c 13, .c 5, .c 3, .c 47, .c 29, .c 3, .c 5, .c 19, .c 3, .p pv3 [pv2,pv5,pv7,pv389],
  .c 37, .c 3, .c 7, .c 13, .c 3, .p pv3 [pv2,pv17,pv8009], .c 5, .c 3, .c 733, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv79,pv383], .c 3, .p pv41 [pv2,pv5,pv107,pv509], .c 157, .c 3, .c 449, .c 31,
  .c 3, .c 11, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv3631], .c 3, .c 5, .c 151, .c 3, .c 13,
  .c 7, .c 3, .p pv2 [pv2,pv272333], .c 61, .c 3, .c 19, .c 5, .c 3, .c 353, .c 43, .c 3, .c 5,
  .c 11, .c 3, .c 7, .c 101, .c 3, .c 17, .p pv7 [pv2,pv3,pv7,pv11,pv131], .c 3, .c 127, .c 5,
  .c 3, .c 11, .c 19, .c 3, .c 5, .p pv5 [pv2,pv3,pv15131], .c 3, .p pv3 [pv2,pv5,pv11,pv619],
  .p pv2 [pv2,pv3,pv90787], .c 3, .p pv5 [pv2,pv7,pv13,pv41,pv73], .c 83, .c 3, .c 7, .c 5, .c 3,
  .c 13, .c 139, .c 3, .c 5, .c 7, .c 3, .c 37, .c 11, .c 3, .p pv2 [pv2,pv136189],
  .p pv3 [pv2,pv3,pv90793], .c 3, .c 31, .c 5, .c 3, .c 89,
]
private theorem h0066c15 : checkBlock 544515 128 b0066c15 = true := by
  decide +kernel

private def b0066c16 : List Row := [
  .p pv3 [pv2,pv3,pv5,pv6053], .c 3, .c 5, .c 47, .c 3, .p pv2 [pv2,pv5,pv27239], .c 71, .c 3,
  .c 19, .c 7, .c 3, .p pv3 [pv2,pv68099], .c 5, .c 3, .c 17, .c 23, .c 3, .c 5,
  .p pv19 [pv2,pv3,pv19,pv59], .c 3, .c 617, .p pv17 [pv2,pv3,pv83,pv547], .c 3, .c 7, .c 11,
  .c 3, .c 29, .c 5, .c 3, .c 131, .c 7, .c 3, .c 5, .p pv13 [pv2,pv3,pv45403], .c 3, .c 11,
  .c 13, .c 3, .c 23, .c 41, .c 3, .c 43, .c 5, .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv1009], .c 3,
  .c 5, .c 17, .c 3, .c 47, .c 7, .c 3, .p pv2 [pv2,pv179,pv761], .p pv3 [pv2,pv3,pv30271], .c 3,
  .p pv2 [pv2,pv13,pv19,pv1103], .c 5, .c 3, .p pv3 [pv2,pv68111], .c 109, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv43], .c 3, .c 7, .p pv3 [pv2,pv3,pv197,pv461], .c 3, .c 11, .c 163, .c 3,
  .c 61, .c 5, .c 3, .p pv7 [pv2,pv11,pv17,pv31,pv47], .c 13, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv90821], .c 3, .c 41, .c 313, .c 3, .p pv3 [pv2,pv7,pv37,pv263], .c 19, .c 3,
  .c 7, .c 5, .c 3, .c 31, .c 11, .c 3, .c 5, .c 7, .c 3, .p pv19 [pv2,pv5,pv13,pv131],
  .p pv3 [pv2,pv3,pv11,pv23,pv359], .c 3, .c 593, .c 17, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv67,pv83], .c 271, .c 3, .c 5, .c 233, .c 3, .c 181, .c 659, .c 3, .c 29, .c 7,
  .c 3, .c 17, .c 5, .c 3, .c 383, .c 31, .c 3, .c 5, .c 11, .c 3, .c 79,
  .p pv3 [pv2,pv3,pv10093], .c 3,
]
private theorem h0066c16 : checkBlock 544771 128 b0066c16 = true := by
  decide +kernel

private def b0066c17 : List Row := [
  .c 7, .p pv2 [pv2,pv3,pv11,pv4129], .c 3, .p pv3 [pv2,pv193,pv353], .c 5, .c 3, .c 11, .c 7,
  .c 3, .c 5, .c 37, .c 3, .c 13, .c 19, .c 3, .p pv3 [pv2,pv17033], .c 47, .c 3,
  .p pv5 [pv2,pv7,pv38933], .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 13, .c 3, .c 397, .c 7, .c 3,
  .p pv5 [pv2,pv449,pv607], .p pv7 [pv2,pv3,pv17,pv167], .c 3, .p pv2 [pv2,pv136273], .c 5, .c 3,
  .c 197, .c 59, .c 3, .c 5, .c 601, .c 3, .c 7, .c 29, .c 3, .p pv3 [pv2,pv11,pv13,pv953],
  .c 419, .c 3, .c 23, .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv673], .c 3, .c 5, .c 347, .c 3,
  .p pv2 [pv2,pv5,pv97,pv281], .p pv3 [pv2,pv3,pv13,pv29,pv241], .c 3, .c 433, .c 11, .c 3, .c 7,
  .c 5, .c 3, .c 239, .p pv13 [pv2,pv3,pv5,pv7,pv11,pv59], .c 3, .c 5, .c 7, .c 3, .c 11, .c 17,
  .c 3, .c 41, .c 67, .c 3, .c 311, .c 5, .c 3, .p pv3 [pv2,pv7,pv19471], .c 149, .c 3, .c 5,
  .c 31, .c 3, .c 457, .p pv3 [pv2,pv3,pv7,pv4327], .c 3, .c 13, .c 7, .c 3,
  .p pv2 [pv2,pv136303], .c 5, .c 3, .c 59, .c 709, .c 3, .c 5, .c 83, .c 3,
  .p pv7 [pv2,pv5,pv7,pv7789], .c 13, .c 3, .c 7, .p pv3 [pv2,pv3,pv23,pv439], .c 3, .c 19, .c 5,
  .c 3, .c 229, .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv7573], .c 3, .c 23, .c 269, .c 3,
  .p pv2 [pv2,pv337,pv809], .c 37, .c 3, .c 293, .c 5, .c 3, .c 7, .c 11,
]
private theorem h0066c17 : checkBlock 545027 128 b0066c17 = true := by
  decide +kernel

private def b0066c18 : List Row := [
  .c 3, .c 5, .c 29, .c 3, .p pv2 [pv2,pv5,pv31,pv1759], .c 7, .c 3, .c 139, .c 101, .c 3, .c 11,
  .c 5, .c 3, .c 17, .c 13, .c 3, .c 5, .c 53, .c 3, .c 7, .c 587, .c 3, .c 109,
  .p pv17 [pv2,pv3,pv7,pv541], .c 3, .c 443, .c 5, .c 3, .c 619, .c 41, .c 3, .c 5, .c 11, .c 3,
  .c 71, .c 23, .c 3, .c 19, .c 547, .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv13 [pv2,pv3,pv5,pv7,pv53], .c 3, .c 5, .c 7, .c 3, .c 379, .c 31, .c 3,
  .p pv2 [pv2,pv272693], .c 13, .c 3, .c 83, .c 5, .c 3, .c 23, .c 61, .c 3, .c 5, .c 499, .c 3,
  .c 17, .c 11, .c 3, .c 37, .c 7, .c 3, .c 41, .c 5, .c 3, .p pv2 [pv2,pv13,pv17,pv617], .c 97,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv109,pv139], .c 3, .c 13, .p pv2 [pv2,pv3,pv90907], .c 3, .c 7,
  .p pv13 [pv2,pv3,pv22727], .c 3, .c 233, .c 5, .c 3, .c 199, .c 7, .c 3, .c 5, .c 13, .c 3,
  .c 19, .p pv5 [pv2,pv3,pv947], .c 3, .p pv2 [pv2,pv31,pv53,pv83], .c 11, .c 3,
  .p pv2 [pv2,pv7,pv47,pv829], .c 5, .c 3, .c 7, .c 23, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv7,pv17,pv191], .c 3, .c 11, .c 7, .c 3, .c 31, .c 19, .c 3, .c 17, .c 5,
  .c 3, .c 13, .p pv23 [pv2,pv3,pv5,pv2273], .c 3, .c 5, .p pv13 [pv2,pv3,pv30307], .c 3, .c 7,
  .p pv17 [pv2,pv3,pv13,pv269], .c 3, .c 23,
]
private theorem h0066c18 : checkBlock 545283 128 b0066c18 = true := by
  decide +kernel

private def b0066c19 : List Row := [
  .c 307, .c 3, .p pv5 [pv2,pv272771], .c 5, .c 3, .p pv2 [pv2,pv29,pv4703],
  .p pv3 [pv2,pv3,pv5,pv3637], .c 3, .c 5, .c 317, .c 3, .c 163, .c 151, .c 3, .c 11, .c 31, .c 3,
  .c 7, .c 5, .c 3, .p pv2 [pv2,pv11,pv24799], .c 17, .c 3, .c 5, .c 7, .c 3, .c 103, .c 107,
  .c 3, .c 13, .p pv41 [pv2,pv3,pv17,pv1783], .c 3, .c 337, .c 5, .c 3, .p pv3 [pv2,pv7,pv9743],
  .c 11, .c 3, .c 5, .p pv19 [pv2,pv3,pv421], .c 3, .p pv2 [pv2,pv5,pv27281], .c 13, .c 3, .c 43,
  .c 7, .c 3, .c 11, .c 5, .c 3, .c 37, .p pv13 [pv2,pv3,pv5,pv4547], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv211,pv431], .c 3, .p pv2 [pv2,pv5,pv7,pv1559], .c 79, .c 3, .c 7, .c 89, .c 3,
  .p pv5 [pv2,pv13,pv31,pv677], .c 5, .c 3, .c 41, .c 7, .c 3, .c 5, .c 11, .c 3, .c 223, .c 17,
  .c 3, .c 191, .c 599, .c 3, .c 29, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 229, .c 3,
  .p pv11 [pv2,pv5,pv11,pv41], .c 7, .c 3, .c 17, .c 127, .c 3, .p pv2 [pv2,pv29,pv97], .c 5,
  .c 3, .c 367, .p pv3 [pv2,pv3,pv5,pv18191], .c 3, .c 5, .c 19, .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv131,pv2083], .p pv23 [pv2,pv3,pv7,pv73,pv89], .c 3, .c 13, .c 5, .c 3,
  .p pv7 [pv2,pv272879], .c 401, .c 3, .c 5, .c 23, .c 3, .c 179, .p pv2 [pv2,pv3,pv45481], .c 3,
  .c 71, .c 13, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv136447],
  .p pv7 [pv2,pv3,pv5,pv7,pv23,pv113], .c 3,
]
private theorem h0066c19 : checkBlock 545539 128 b0066c19 = true := by
  decide +kernel

private def b0066c20 : List Row := [
  .c 5, .c 7, .c 3, .c 269, .c 673, .c 3, .c 107, .c 11, .c 3, .c 19, .c 5, .c 3, .c 17, .c 73,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv90971], .c 3, .c 11, .c 41, .c 3, .c 89, .c 7, .c 3,
  .p pv2 [pv2,pv11,pv43,pv577], .c 5, .c 3, .c 67, .c 19, .c 3, .c 5, .c 13, .c 3, .c 37,
  .p pv5 [pv2,pv3,pv90977], .c 3, .c 7, .c 541, .c 3, .p pv3 [pv2,pv109,pv313], .c 5, .c 3, .c 31,
  .c 7, .c 3, .c 5, .c 17, .c 3, .c 83, .p pv2 [pv2,pv3,pv45491], .c 3, .c 11,
  .p pv7 [pv2,pv3,pv37,pv2459], .c 3, .c 113, .c 5, .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv31,pv587],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv67,pv97], .c 3, .c 17, .c 7, .c 3, .c 19,
  .p pv13 [pv2,pv3,pv23,pv43], .c 3, .p pv2 [pv2,pv136483], .c 5, .c 3, .p pv2 [pv2,pv17,pv16057],
  .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv19,pv4789], .c 3, .c 7, .c 53, .c 3, .c 419,
  .p pv7 [pv2,pv3,pv7,pv619], .c 3, .c 11, .c 5, .c 3, .c 79, .c 43, .c 3, .c 5, .c 727, .c 3,
  .c 109, .c 29, .c 3, .c 13, .c 17, .c 3, .c 7, .c 5, .c 3, .c 47,
  .p pv31 [pv2,pv3,pv5,pv7,pv13], .c 3, .c 5, .c 7, .c 3, .c 61, .c 13, .c 3,
  .p pv3 [pv2,pv113,pv151], .p pv2 [pv2,pv3,pv11,pv8273], .c 3, .c 17, .c 5, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv5,pv6067], .c 3, .c 5, .c 421, .c 3, .c 19, .c 23, .c 3,
  .p pv5 [pv2,pv37,pv47,pv157], .c 7,
]
private theorem h0066c20 : checkBlock 545795 128 b0066c20 = true := by
  decide +kernel

private def b0066c21 : List Row := [
  .c 3, .p pv2 [pv2,pv13,pv10501], .c 5, .c 3, .c 53, .c 71, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv23,pv1319], .c 3, .p pv11 [pv2,pv5,pv7,pv29,pv269], .c 11, .c 3, .c 7, .c 19,
  .c 3, .c 37, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv31,pv367], .c 3,
  .p pv2 [pv2,pv5,pv43,pv127], .p pv3 [pv2,pv3,pv3371], .c 3, .c 101,
  .p pv13 [pv2,pv3,pv17,pv2677], .c 3, .c 73, .c 5, .c 3, .c 7, .c 739, .c 3, .c 5, .c 31, .c 3,
  .c 139, .c 7, .c 3, .p pv3 [pv2,pv19,pv3593], .c 11, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv136537], .p pv3 [pv2,pv3,pv5,pv11,pv331], .c 3, .c 5, .c 29, .c 3, .c 7, .c 59,
  .c 3, .c 151, .c 13, .c 3, .p pv2 [pv2,pv11,pv12413], .c 5, .c 3, .p pv2 [pv2,pv347,pv787],
  .c 23, .c 3, .c 5, .c 47, .c 3, .c 317, .c 17, .c 3, .p pv2 [pv2,pv7,pv19507], .c 109, .c 3,
  .c 7, .c 5, .c 3, .c 103, .p pv3 [pv2,pv3,pv5,pv7,pv17], .c 3, .c 5, .c 7, .c 3, .c 13, .c 83,
  .c 3, .c 11, .c 43, .c 3, .p pv3 [pv2,pv68279], .c 5, .c 3, .p pv7 [pv2,pv7,pv11,pv3547],
  .p pv19 [pv2,pv3,pv5,pv569], .c 3, .c 5, .c 13, .c 3, .c 31, .p pv2 [pv2,pv3,pv7,pv929], .c 3,
  .c 167, .c 7, .c 3, .p pv5 [pv2,pv273131], .c 5, .c 3, .c 19, .c 11, .c 3, .c 5, .c 337, .c 3,
  .c 47, .p pv2 [pv2,pv3,pv11,pv31,pv89], .c 3, .c 7, .p pv17 [pv2,pv3,pv19,pv599], .c 3, .c 11,
  .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
]
private theorem h0066c21 : checkBlock 546051 128 b0066c21 = true := by
  decide +kernel

private def b0066c22 : List Row := [
  .c 19, .c 3, .c 659, .c 31, .c 3, .p pv2 [pv2,pv61,pv2239], .c 23, .c 3,
  .p pv2 [pv2,pv7,pv39023], .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .c 11, .c 3,
  .p pv3 [pv2,pv5,pv59,pv463], .c 7, .c 3, .c 241, .p pv2 [pv2,pv3,pv11,pv4139], .c 3,
  .p pv3 [pv2,pv34147], .c 5, .c 3, .c 11, .p pv37 [pv2,pv3,pv5,pv29,pv157], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv41,pv2221], .c 3, .c 7, .p pv2 [pv2,pv3,pv5059], .c 3, .c 13, .c 37, .c 3,
  .c 19, .c 5, .c 3, .c 29, .p pv29 [pv2,pv3,pv5,pv13,pv467], .c 3, .c 5, .c 17, .c 3, .c 43,
  .c 11, .c 3, .c 41, .c 139, .c 3, .c 7, .c 5, .c 3, .c 577, .c 19, .c 3, .c 5, .c 7, .c 3,
  .c 17, .c 449, .c 3, .c 31, .c 181, .c 3, .c 79, .c 5, .c 3, .c 107, .c 191, .c 3, .c 5, .c 23,
  .c 3, .p pv2 [pv2,pv5,pv89,pv307], .c 367, .c 3, .p pv2 [pv2,pv273233], .c 7, .c 3, .c 283,
  .c 5, .c 3, .p pv17 [pv2,pv19,pv73,pv197], .c 13, .c 3, .c 5, .c 43, .c 3, .c 11, .c 137, .c 3,
  .c 7, .c 17, .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv317,pv431], .c 7, .c 3, .c 5, .c 59, .c 3,
  .c 277, .p pv2 [pv2,pv3,pv79,pv1153], .c 3, .c 37, .c 521, .c 3, .c 13, .c 5, .c 3, .c 7,
  .c 383, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv11,pv13], .c 3, .c 73, .c 7, .c 3, .c 11, .c 13, .c 3,
]
private theorem h0066c22 : checkBlock 546307 128 b0066c22 = true := by
  decide +kernel

private def b0066c23 : List Row := [
  .c 29, .c 5, .c 3, .p pv3 [pv2,pv11,pv6211], .c 41, .c 3, .c 5, .c 619, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv91097], .c 3, .p pv2 [pv2,pv67,pv4079], .c 53, .c 3, .c 239, .c 5, .c 3,
  .p pv7 [pv2,pv13,pv21023], .c 11, .c 3, .c 5, .c 271, .c 3, .c 13,
  .p pv5 [pv2,pv3,pv11,pv41,pv101], .c 3, .p pv5 [pv2,pv7,pv43,pv227],
  .p pv2 [pv2,pv3,pv17,pv23,pv233], .c 3, .c 7, .c 5, .c 3, .c 71,
  .p pv13 [pv2,pv3,pv5,pv7,pv19,pv137], .c 3, .c 5, .c 7, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv53,pv191], .c 3, .c 661, .c 19, .c 3, .c 41, .c 5, .c 3, .c 43,
  .p pv13 [pv2,pv3,pv5,pv3037], .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv54667], .c 563, .c 3,
  .p pv2 [pv2,pv13,pv10513], .c 7, .c 3, .p pv2 [pv2,pv61,pv4481], .c 5, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv5,pv18223], .c 3, .c 5, .c 73, .c 3, .c 211, .c 17, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv29,pv1571], .c 3, .c 101, .c 5, .c 3, .p pv23 [pv2,pv273359], .c 7, .c 3,
  .c 5, .c 89, .c 3, .p pv11 [pv2,pv5,pv54673], .c 11, .c 3, .c 17, .p pv2 [pv2,pv3,pv293,pv311],
  .c 3, .c 61, .c 5, .c 3, .c 7, .c 47, .c 3, .c 5, .c 359, .c 3, .c 503, .c 7, .c 3, .c 13,
  .c 193, .c 3, .c 641, .c 5, .c 3, .c 23, .p pv19 [pv2,pv3,pv5,pv13,pv701], .c 3, .c 5, .c 67,
  .c 3, .c 7, .c 13, .c 3, .c 353, .c 11, .c 3, .c 463, .c 5, .c 3, .c 31, .c 313, .c 3, .c 5,
  .c 41,
]
private theorem h0066c23 : checkBlock 546563 128 b0066c23 = true := by
  decide +kernel

private def b0066c24 : List Row := [
  .c 3, .c 11, .c 37, .c 3, .c 103, .c 241, .c 3, .c 7, .c 5, .c 3, .c 17,
  .p pv19 [pv2,pv3,pv5,pv7,pv31], .c 3, .c 5, .c 7, .c 3, .c 233, .c 29, .c 3, .c 467,
  .p pv3 [pv2,pv3,pv13,pv19,pv41], .c 3, .p pv5 [pv2,pv127,pv2153], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv19531], .c 13, .c 3, .c 5, .c 19, .c 3, .p pv3 [pv2,pv5,pv1709], .c 349, .c 3,
  .c 11, .c 7, .c 3, .p pv2 [pv2,pv47,pv2909], .c 5, .c 3, .c 41, .c 487, .c 3, .c 5, .c 17, .c 3,
  .c 29, .c 71, .c 3, .c 7, .p pv3 [pv2,pv3,pv91153], .c 3, .c 13, .c 5, .c 3, .c 251, .c 7, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv13,pv1753], .c 3, .c 17, .p pv11 [pv2,pv3,pv11,pv8287], .c 3,
  .p pv2 [pv2,pv273473], .c 13, .c 3, .c 11, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv43,pv53],
  .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv1447], .c 3, .c 37, .c 7, .c 3, .p pv3 [pv2,pv17093], .c 149,
  .c 3, .c 97, .c 5, .c 3, .c 59, .c 19, .c 3, .c 5, .c 11, .c 3, .c 7, .c 43, .c 3,
  .p pv5 [pv2,pv273503], .c 17, .c 3, .c 53, .c 5, .c 3, .c 11, .p pv11 [pv2,pv3,pv5,pv1013],
  .c 3, .c 5, .c 13, .c 3, .c 293, .c 47, .c 3, .p pv2 [pv2,pv7,pv2791], .c 283, .c 3, .c 7, .c 5,
  .c 3, .c 311, .c 199, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv17,pv1609], .c 11, .c 3, .c 19,
  .c 197, .c 3, .c 151,
]
private theorem h0066c24 : checkBlock 546819 128 b0066c24 = true := by
  decide +kernel

private def b0066c25 : List Row := [
  .c 5, .c 3, .c 13, .c 229, .c 3, .c 5, .p pv3 [pv2,pv3,pv19,pv4799], .c 3, .c 107,
  .p pv29 [pv2,pv3,pv7,pv13,pv167], .c 3, .p pv3 [pv2,pv11,pv6217], .c 7, .c 3,
  .p pv5 [pv2,pv273551], .c 5, .c 3, .c 61, .c 17, .c 3, .c 5, .c 101, .c 3,
  .p pv3 [pv2,pv5,pv7,pv977], .c 211, .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv43,pv3181], .c 5,
  .c 3, .p pv2 [pv2,pv273569], .c 7, .c 3, .c 5, .c 23, .c 3, .c 11, .c 257, .c 3, .c 13, .c 719,
  .c 3, .c 181, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv13,pv23,pv61], .c 3, .c 5, .c 97, .c 3,
  .c 19, .c 7, .c 3, .c 131, .c 67, .c 3, .c 23, .c 5, .c 3, .c 173, .c 29, .c 3, .c 5, .c 461,
  .c 3, .c 7, .c 17, .c 3, .c 11, .c 19, .c 3, .p pv5 [pv2,pv13,pv1619], .c 5, .c 3,
  .p pv2 [pv2,pv11,pv12437], .c 61, .c 3, .c 5, .p pv5 [pv2,pv3,pv563], .c 3,
  .p pv3 [pv2,pv5,pv13681], .c 31, .c 3, .c 17, .p pv11 [pv2,pv3,pv13,pv877], .c 3, .c 7, .c 5,
  .c 3, .c 29, .c 11, .c 3, .c 5, .c 7, .c 3, .p pv17 [pv2,pv5,pv54727],
  .p pv5 [pv2,pv3,pv11,pv691], .c 3, .c 149, .c 617, .c 3, .c 11, .c 5, .c 3, .c 109,
  .p pv2 [pv2,pv3,pv5,pv2027], .c 3, .c 5, .c 227, .c 3, .p pv2 [pv2,pv5,pv13,pv421], .c 263,
  .c 3, .c 383, .c 7, .c 3, .c 13, .c 5, .c 3, .c 101, .p pv13 [pv2,pv3,pv5,pv4561], .c 3, .c 5,
  .c 11, .c 3,
]
private theorem h0066c25 : checkBlock 547075 128 b0066c25 = true := by
  decide +kernel

private def b0066c26 : List Row := [
  .c 23, .c 19, .c 3, .c 7, .c 13, .c 3, .c 59, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv45613], .c 3, .p pv3 [pv2,pv5,pv11,pv311], .p pv5 [pv2,pv3,pv47,pv647], .c 3,
  .c 31, .p pv17 [pv2,pv3,pv22807], .c 3, .p pv2 [pv2,pv7,pv113,pv173], .c 5, .c 3, .c 7, .c 307,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv13033], .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv136849],
  .p pv3 [pv2,pv3,pv31,pv109], .c 3, .c 499, .c 5, .c 3, .c 19, .p pv7 [pv2,pv3,pv5,pv71,pv257],
  .c 3, .c 5, .c 13, .c 3, .c 7, .c 23, .c 3, .c 73, .c 31, .c 3, .c 29, .c 5, .c 3, .c 89,
  .p pv17 [pv2,pv3,pv5,pv2281], .c 3, .c 5, .c 19, .c 3, .c 17, .p pv31 [pv2,pv3,pv37,pv137],
  .c 3, .c 67, .c 11, .c 3, .c 7, .c 5, .c 3, .c 13, .p pv7 [pv2,pv3,pv5,pv7,pv11,pv79], .c 3,
  .c 5, .c 7, .c 3, .c 11, .p pv2 [pv2,pv3,pv13,pv7019], .c 3, .p pv5 [pv2,pv457,pv599], .c 37,
  .c 3, .p pv2 [pv2,pv11,pv23,pv541], .c 5, .c 3, .p pv2 [pv2,pv7,pv39107],
  .p pv2 [pv2,pv3,pv5,pv73], .c 3, .c 5, .c 109, .c 3, .c 601, .p pv5 [pv2,pv3,pv7,pv3259], .c 3,
  .c 163, .c 7, .c 3, .c 19, .c 5, .c 3, .p pv3 [pv2,pv89,pv769], .c 557, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv17,pv61], .c 3, .c 193, .c 53, .c 3, .c 7, .c 29, .c 3, .c 17, .c 5,
  .c 3, .p pv11 [pv2,pv11,pv24889], .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv263,pv347], .c 3, .c 521,
  .c 13, .c 3, .p pv3 [pv2,pv68447], .c 59, .c 3, .p pv5 [pv2,pv7,pv39113], .c 5,
]
private theorem h0066c26 : checkBlock 547331 128 b0066c26 = true := by
  decide +kernel

private def b0066c27 : List Row := [
  .c 3, .c 7, .c 11, .c 3, .c 5, .c 47, .c 3, .p pv3 [pv2,pv5,pv37], .c 7, .c 3, .c 23,
  .p pv7 [pv2,pv3,pv22817], .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv19,pv14411], .c 17, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv107,pv853], .c 3, .c 7, .c 419, .c 3, .c 19,
  .p pv3 [pv2,pv3,pv7,pv13,pv17,pv59], .c 3, .p pv2 [pv2,pv273821], .c 5, .c 3, .c 53, .c 13,
  .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv139,pv197], .p pv3 [pv2,pv3,pv97,pv941], .c 3,
  .c 257, .c 281, .c 3, .c 7, .c 5, .c 3, .c 11, .p pv23 [pv2,pv3,pv5,pv7,pv163], .c 3, .c 5,
  .c 7, .c 3, .c 43, .c 677, .c 3, .c 59, .c 23, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv31,pv631], .c 37, .c 3, .c 5, .c 83, .c 3, .c 421, .c 11, .c 3,
  .p pv5 [pv2,pv137,pv1999], .c 7, .c 3, .c 107, .c 5, .c 3, .c 31,
  .p pv2 [pv2,pv3,pv5,pv17,pv179], .c 3, .c 5, .p pv2 [pv2,pv3,pv91291], .c 3, .c 19,
  .p pv7 [pv2,pv3,pv29,pv787], .c 3, .c 7, .c 97, .c 3, .p pv2 [pv2,pv273881], .c 5, .c 3,
  .p pv7 [pv2,pv13,pv23,pv229], .c 7, .c 3, .c 5, .c 43, .c 3, .c 13, .c 233, .c 3,
  .p pv2 [pv2,pv79,pv3467], .c 11, .c 3, .c 241, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5, .c 13, .c 3,
  .c 11, .c 7, .c 3, .p pv3 [pv2,pv68477], .p pv2 [pv2,pv3,pv91303], .c 3,
  .p pv5 [pv2,pv11,pv37,pv673], .c 5, .c 3, .c 263, .p pv3 [pv2,pv3,pv5,pv2029], .c 3, .c 5,
  .c 23, .c 3, .c 7,
]
private theorem h0066c27 : checkBlock 547587 128 b0066c27 = true := by
  decide +kernel

private def b0066c28 : List Row := [
  .c 163, .c 3, .c 199, .p pv17 [pv2,pv3,pv7,pv1087], .c 3, .p pv2 [pv2,pv136963], .c 5, .c 3,
  .c 13, .c 53, .c 3, .c 5, .c 653, .c 3, .p pv7 [pv2,pv5,pv54787], .c 149, .c 3, .c 11, .c 47,
  .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv11,pv283], .c 173, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv5479], .c 19, .c 3, .c 71, .p pv7 [pv2,pv3,pv45659], .c 3, .c 347, .c 5, .c 3,
  .c 179, .c 11, .c 3, .c 5, .c 17, .c 3, .c 367, .c 37, .c 3, .c 13, .c 7, .c 3, .c 11, .c 5,
  .c 3, .c 43, .p pv37 [pv2,pv3,pv5,pv13,pv281], .c 3, .c 5, .p pv13 [pv2,pv3,pv31,pv491], .c 3,
  .c 17, .c 13, .c 3, .c 7, .c 661, .c 3, .c 47, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 11, .c 3,
  .c 443, .c 67, .c 3, .c 229, .p pv3 [pv2,pv3,pv11,pv19,pv23], .c 3,
  .p pv2 [pv2,pv7,pv13,pv3011], .c 5, .c 3, .c 7, .c 73, .c 3, .c 5, .c 19, .c 3, .c 23, .c 7,
  .c 3, .c 239, .c 17, .c 3, .c 541, .c 5, .c 3, .p pv7 [pv2,pv274019], .c 13, .c 3, .c 5, .c 41,
  .c 3, .c 7, .c 11, .c 3, .c 709, .p pv13 [pv2,pv3,pv7,pv13049], .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv181,pv757], .c 29, .c 3, .c 5, .c 139, .c 3, .c 37, .p pv2 [pv2,pv3,pv30449],
  .c 3, .c 157, .p pv7 [pv2,pv3,pv41,pv557], .c 3, .c 7, .c 5, .c 3,
]
private theorem h0066c28 : checkBlock 547843 128 b0066c28 = true := by
  decide +kernel

private def b0066c29 : List Row := [
  .p pv2 [pv2,pv179,pv1531], .c 389, .c 3, .c 5, .c 7, .c 3, .c 31, .c 23, .c 3,
  .p pv2 [pv2,pv137029], .c 11, .c 3, .p pv2 [pv2,pv274061], .c 5, .c 3, .c 29, .c 17, .c 3, .c 5,
  .c 137, .c 3, .c 11, .p pv3 [pv2,pv3,pv7,pv31,pv421], .c 3, .c 97, .c 7, .c 3,
  .p pv3 [pv2,pv11,pv6229], .c 5, .c 3, .c 23, .c 47, .c 3, .c 5, .c 401, .c 3, .c 13, .c 31,
  .c 3, .c 7, .c 53, .c 3, .c 277, .c 5, .c 3, .p pv3 [pv2,pv19,pv7213], .c 7, .c 3, .c 5, .c 13,
  .c 3, .p pv3 [pv2,pv5,pv2741], .c 293, .c 3, .c 11, .c 353, .c 3, .p pv2 [pv2,pv7,pv2797], .c 5,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv9137], .c 3, .c 5, .p pv11 [pv2,pv3,pv7,pv19,pv229], .c 3,
  .c 281, .c 7, .c 3, .c 173, .p pv3 [pv2,pv3,pv91373], .c 3, .p pv2 [pv2,pv274121], .c 5, .c 3,
  .c 13, .c 11, .c 3, .c 5, .c 397, .c 3, .c 7, .p pv3 [pv2,pv3,pv11,pv13,pv71], .c 3, .c 17,
  .c 103, .c 3, .c 11, .c 5, .c 3, .c 349, .c 151, .c 3, .c 5, .c 59, .c 3,
  .p pv2 [pv2,pv5,pv54829], .c 41, .c 3, .c 23, .c 337, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv137077], .c 439, .c 3, .c 5, .c 7, .c 3, .c 19, .p pv2 [pv2,pv3,pv91387], .c 3,
  .c 13, .c 61, .c 3, .c 71, .c 5, .c 3, .c 11, .c 97, .c 3, .c 5, .p pv2 [pv2,pv3,pv59,pv1549],
  .c 3, .p pv13 [pv2,pv5,pv11,pv997], .c 13,
]
private theorem h0066c29 : checkBlock 548099 128 b0066c29 = true := by
  decide +kernel

private def b0066c30 : List Row := [
  .c 3, .c 223, .c 7, .c 3, .p pv2 [pv2,pv487,pv563], .c 5, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv5,pv677], .c 3, .c 5, .c 37, .c 3, .c 83, .c 11, .c 3, .c 7, .c 23, .c 3,
  .p pv3 [pv2,pv13,pv5273], .c 5, .c 3, .p pv11 [pv2,pv274199], .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv30467], .c 3, .c 137, .c 379, .c 3, .p pv3 [pv2,pv11,pv19,pv41], .c 29, .c 3,
  .p pv5 [pv2,pv7,pv43,pv911], .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 17, .c 3,
  .p pv3 [pv2,pv5,pv13711], .c 7, .c 3, .c 491, .c 11, .c 3, .p pv2 [pv2,pv31,pv4423], .c 5, .c 3,
  .p pv2 [pv2,pv23,pv11923], .p pv61 [pv2,pv3,pv5,pv11,pv277], .c 3, .c 5, .c 331, .c 3, .c 7,
  .c 19, .c 3, .c 29, .c 643, .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv17,pv37,pv109], .c 269, .c 3,
  .c 5, .c 53, .c 3, .p pv2 [pv2,pv5,pv1097], .p pv3 [pv2,pv3,pv113,pv809], .c 3, .c 89, .c 13,
  .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv274259], .p pv11 [pv2,pv3,pv5,pv7,pv653], .c 3, .c 5,
  .c 7, .c 3, .c 101, .p pv5 [pv2,pv3,pv1693], .c 3, .c 11, .c 17, .c 3, .p pv5 [pv2,pv274271],
  .c 5, .c 3, .c 19, .c 43, .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv2689], .c 3, .c 13, .c 421, .c 3,
  .p pv5 [pv2,pv274283], .c 7, .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv103,pv2663], .c 11, .c 3,
  .c 5, .c 13, .c 3, .p pv19 [pv2,pv5,pv7,pv17,pv461], .c 29, .c 3, .c 7, .c 37, .c 3, .c 11,
  .c 5, .c 3, .c 307,
]
private theorem h0066c30 : checkBlock 548355 128 b0066c30 = true := by
  decide +kernel

private def b0066c31 : List Row := [
  .c 7, .c 3, .c 5, .c 71, .c 3, .c 41, .p pv3 [pv2,pv3,pv29,pv1051], .c 3, .c 523,
  .p pv2 [pv2,pv3,pv131,pv349], .c 3, .c 139, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 11, .c 3,
  .c 29, .c 7, .c 3, .p pv3 [pv2,pv53,pv647], .c 227, .c 3, .c 19, .c 5, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv5,pv18289], .c 3, .c 5, .p pv5 [pv2,pv3,pv15241], .c 3, .c 7, .c 373, .c 3,
  .p pv5 [pv2,pv251,pv1093], .c 313, .c 3, .p pv2 [pv2,pv17,pv8069], .c 5, .c 3, .c 193, .c 19,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv109,pv839], .c 3, .c 23, .c 11, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv91453], .c 3, .c 7, .c 5, .c 3, .c 97, .c 31, .c 3, .c 5, .c 7, .c 3, .c 73,
  .c 13, .c 3, .c 37, .p pv2 [pv2,pv3,pv5081], .c 3, .p pv3 [pv2,pv34297], .c 5, .c 3, .c 59,
  .p pv37 [pv2,pv3,pv5,pv17,pv269], .c 3, .c 5, .c 29, .c 3, .p pv2 [pv2,pv5,pv54877], .c 503,
  .c 3, .c 17, .c 7, .c 3, .p pv5 [pv2,pv13,pv21107], .c 5, .c 3, .c 293,
  .p pv3 [pv2,pv3,pv5,pv11,pv1663], .c 3, .c 5, .c 67, .c 3, .c 11, .c 23, .c 3, .c 7, .c 43,
  .c 3, .c 79, .c 5, .c 3, .c 47, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv23,pv41,pv97], .c 3,
  .p pv17 [pv2,pv5,pv71,pv773], .p pv11 [pv2,pv3,pv5717], .c 3, .p pv2 [pv2,pv137209], .c 383,
  .c 3, .p pv2 [pv2,pv7,pv197,pv199], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv3659], .c 3, .c 5,
  .c 457, .c 3, .p pv7 [pv2,pv5,pv13,pv2111], .c 7, .c 3,
]
private theorem h0066c31 : checkBlock 548611 128 b0066c31 = true := by
  decide +kernel

def rows0066 : List Row :=
  b0066c00 ++ b0066c01 ++ b0066c02 ++ b0066c03 ++ b0066c04 ++ b0066c05 ++ b0066c06 ++ b0066c07 ++
  b0066c08 ++ b0066c09 ++ b0066c10 ++ b0066c11 ++ b0066c12 ++ b0066c13 ++ b0066c14 ++ b0066c15 ++
  b0066c16 ++ b0066c17 ++ b0066c18 ++ b0066c19 ++ b0066c20 ++ b0066c21 ++ b0066c22 ++ b0066c23 ++
  b0066c24 ++ b0066c25 ++ b0066c26 ++ b0066c27 ++ b0066c28 ++ b0066c29 ++ b0066c30 ++ b0066c31

attribute [local irreducible] checkBlock checkRows checkPrime

theorem checked0066 : checkBlock 540675 4096 rows0066 = true :=
  checkBlock_append h0066c00 (
    checkBlock_append h0066c01 (
    checkBlock_append h0066c02 (
    checkBlock_append h0066c03 (
    checkBlock_append h0066c04 (
    checkBlock_append h0066c05 (
    checkBlock_append h0066c06 (
    checkBlock_append h0066c07 (
    checkBlock_append h0066c08 (
    checkBlock_append h0066c09 (
    checkBlock_append h0066c10 (
    checkBlock_append h0066c11 (
    checkBlock_append h0066c12 (
    checkBlock_append h0066c13 (
    checkBlock_append h0066c14 (
    checkBlock_append h0066c15 (
    checkBlock_append h0066c16 (
    checkBlock_append h0066c17 (
    checkBlock_append h0066c18 (
    checkBlock_append h0066c19 (
    checkBlock_append h0066c20 (
    checkBlock_append h0066c21 (
    checkBlock_append h0066c22 (
    checkBlock_append h0066c23 (
    checkBlock_append h0066c24 (
    checkBlock_append h0066c25 (
    checkBlock_append h0066c26 (
    checkBlock_append h0066c27 (
    checkBlock_append h0066c28 (
    checkBlock_append h0066c29 (
    checkBlock_append h0066c30 (
    h0066c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
