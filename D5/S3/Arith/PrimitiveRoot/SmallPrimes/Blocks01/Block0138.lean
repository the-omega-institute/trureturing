/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0138
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0138.checked0138
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table018
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table021
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table025
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table031
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table042
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table063
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table117

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0138c00 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv7,pv17,pv19], .c 11, .c 3, .c 7, .c 827, .c 3, .c 43, .c 5, .c 3, .c 13,
  .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv181,pv347], .c 3, .c 241, .c 71, .c 3, .c 151, .c 31, .c 3,
  .c 53, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 19, .c 3, .p pv7 [pv2,pv5,pv3533], .c 7, .c 3,
  .c 89, .c 11, .c 3, .c 229, .c 5, .c 3, .p pv2 [pv2,pv565289], .p pv31 [pv2,pv3,pv5,pv11,pv571],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv188431], .c 3, .c 7, .c 929, .c 3, .c 13, .c 43, .c 3, .c 569,
  .c 5, .c 3, .c 37, .c 23, .c 3, .c 5, .c 59, .c 3, .p pv2 [pv2,pv5,pv56531], .c 13, .c 3,
  .p pv2 [pv2,pv7,pv83,pv139], .p pv2 [pv2,pv3,pv94219], .c 3, .c 7, .c 5, .c 3,
  .p pv11 [pv2,pv565319], .p pv11 [pv2,pv3,pv5,pv7,pv673], .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv22613], .c 17, .c 3, .c 11, .c 353, .c 3, .c 31, .c 5, .c 3, .c 107, .c 19,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv59,pv1597], .c 3, .c 29, .c 37, .c 3, .c 17, .c 7, .c 3,
  .p pv2 [pv2,pv67,pv4219], .c 5, .c 3, .p pv2 [pv2,pv41,pv13789], .c 11, .c 3, .c 5, .c 181,
  .c 3, .p pv17 [pv2,pv5,pv7,pv29,pv557], .c 701, .c 3, .c 7, .p pv7 [pv2,pv3,pv199,pv947], .c 3,
  .c 11, .c 5, .c 3, .c 97, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv23557], .c 3,
  .p pv3 [pv2,pv5,pv13,pv4349], .c 179, .c 3, .c 19, .c 23, .c 3, .c 13,
]
private theorem h0138c00 : checkBlock 1130499 128 b0138c00 = true := by
  decide +kernel

private def b0138c01 : List Row := [
  .c 5, .c 3, .c 7, .c 149, .c 3, .c 5, .c 11, .c 3, .c 43, .c 7, .c 3, .p pv3 [pv2,pv107,pv1321],
  .c 13, .c 3, .p pv5 [pv2,pv565391], .c 5, .c 3, .c 11, .c 113, .c 3, .c 5, .c 29, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv229,pv823], .c 3, .p pv13 [pv2,pv17,pv79,pv421],
  .p pv17 [pv2,pv3,pv7,pv53,pv127], .c 3, .p pv2 [pv2,pv282703], .c 5, .c 3,
  .p pv2 [pv2,pv13,pv23,pv31,pv61], .c 41, .c 3, .c 5, .p pv11 [pv2,pv3,pv29,pv67,pv97], .c 3,
  .c 13, .c 11, .c 3, .c 103, .c 151, .c 3, .c 7, .c 5, .c 3, .c 31, .c 593, .c 3, .c 5, .c 7,
  .c 3, .c 19, .p pv3 [pv2,pv3,pv41,pv4597], .c 3, .c 47, .c 313, .c 3, .c 347, .c 5, .c 3, .c 61,
  .c 419, .c 3, .c 5, .c 23, .c 3, .c 17, .c 67, .c 3, .c 101, .c 7, .c 3, .c 41, .c 5, .c 3,
  .c 13, .c 31, .c 3, .c 5, .c 199, .c 3, .c 11, .c 89, .c 3, .c 7, .p pv13 [pv2,pv3,pv23561],
  .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv565469], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv188491],
  .c 3, .p pv23 [pv2,pv5,pv22619], .p pv7 [pv2,pv3,pv47123], .c 3, .p pv2 [pv2,pv19,pv23,pv647],
  .c 17, .c 3, .p pv2 [pv2,pv7,pv80783], .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .c 197, .c 3,
  .p pv7 [pv2,pv5,pv193,pv293], .c 7, .c 3, .c 11, .c 73, .c 3, .c 17, .c 5, .c 3, .c 383, .c 61,
  .c 3, .c 5, .c 1031, .c 3,
]
private theorem h0138c01 : checkBlock 1130755 128 b0138c01 = true := by
  decide +kernel

private def b0138c02 : List Row := [
  .c 7, .c 13, .c 3, .c 113, .c 733, .c 3, .p pv5 [pv2,pv565511], .c 5, .c 3, .c 29, .c 11, .c 3,
  .c 5, .c 643, .c 3, .c 83, .c 79, .c 3, .p pv5 [pv2,pv7,pv80789], .p pv11 [pv2,pv3,pv23,pv683],
  .c 3, .c 7, .c 5, .c 3, .c 149, .c 17, .c 3, .c 5, .c 7, .c 3, .c 23, .c 53, .c 3,
  .p pv2 [pv2,pv282769], .p pv3 [pv2,pv3,pv13,pv17,pv853], .c 3, .p pv2 [pv2,pv601,pv941], .c 5,
  .c 3, .c 19, .c 13, .c 3, .c 5, .c 11, .c 3, .c 71, .p pv3 [pv2,pv3,pv7,pv47,pv191], .c 3,
  .c 311, .c 7, .c 3, .p pv3 [pv2,pv17,pv8317], .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv1571],
  .c 3, .c 5, .c 19, .c 3, .p pv11 [pv2,pv5,pv7,pv11,pv13,pv113], .p pv2 [pv2,pv3,pv94261], .c 3,
  .c 7, .p pv3 [pv2,pv3,pv20947], .c 3, .c 13, .c 5, .c 3, .c 41, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv2417], .c 3, .c 67, .c 11, .c 3, .c 691, .c 13, .c 3, .c 193, .c 5, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv5,pv17,pv1109], .c 3, .c 5, .c 239, .c 3,
  .p pv19 [pv2,pv5,pv31,pv41,pv89], .c 7, .c 3, .c 17, .c 769, .c 3, .c 19, .c 5, .c 3, .c 23,
  .c 953, .c 3, .c 5, .p pv5 [pv2,pv3,pv23567], .c 3, .c 7, .p pv3 [pv2,pv3,pv19,pv9923], .c 3,
  .c 421, .c 11, .c 3, .c 499, .c 5, .c 3, .p pv7 [pv2,pv37,pv15287], .c 19, .c 3, .c 5, .c 13,
  .c 3, .c 11, .p pv2 [pv2,pv3,pv31,pv3041], .c 3, .c 251, .p pv2 [pv2,pv3,pv167,pv1129], .c 3,
  .c 7, .c 5,
]
private theorem h0138c02 : checkBlock 1131011 128 b0138c02 = true := by
  decide +kernel

private def b0138c03 : List Row := [
  .c 3, .p pv2 [pv2,pv277,pv1021], .p pv17 [pv2,pv3,pv5,pv7,pv5387], .c 3, .c 5, .c 7, .c 3,
  .c 73, .c 31, .c 3, .c 43, .c 919, .c 3, .c 191, .c 5, .c 3, .c 13, .c 23, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv61,pv281], .c 3, .c 97, .c 41, .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv565661], .c 5, .c 3, .p pv3 [pv2,pv11,pv1607], .p pv11 [pv2,pv3,pv5,pv43,pv877],
  .c 3, .c 5, .c 47, .c 3, .p pv3 [pv2,pv5,pv7,pv8081], .p pv3 [pv2,pv3,pv157,pv1201], .c 3, .c 7,
  .c 37, .c 3, .p pv3 [pv2,pv103,pv1373], .c 5, .c 3, .c 79, .c 7, .c 3, .c 5, .c 17, .c 3,
  .c 197, .c 43, .c 3, .c 13, .p pv3 [pv2,pv3,pv188563], .c 3, .c 11, .c 5, .c 3, .c 7, .c 53,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv13469], .c 3, .c 17, .c 7, .c 3, .c 31, .c 739, .c 3,
  .p pv2 [pv2,pv19,pv14887], .c 5, .c 3, .p pv2 [pv2,pv17,pv107,pv311],
  .p pv13 [pv2,pv3,pv5,pv109,pv173], .c 3, .c 5, .c 11, .c 3, .c 7, .c 983, .c 3,
  .p pv2 [pv2,pv41,pv6899], .c 23, .c 3, .c 59, .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv19,pv397], .c 3, .c 5, .c 89, .c 3, .c 367, .p pv3 [pv2,pv3,pv23,pv911],
  .c 3, .p pv2 [pv2,pv7,pv80819], .c 17, .c 3, .c 7, .c 5, .c 3, .p pv13 [pv2,pv47,pv12037],
  .c 13, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv113149], .c 11, .c 3, .c 37, .c 157, .c 3,
  .c 17, .c 5, .c 3, .p pv3 [pv2,pv7,pv23,pv251], .c 599, .c 3, .c 5, .c 79, .c 3, .c 1013,
]
private theorem h0138c03 : checkBlock 1131267 128 b0138c03 = true := by
  decide +kernel

private def b0138c04 : List Row := [
  .p pv7 [pv2,pv3,pv7,pv29,pv929], .c 3, .c 71, .c 7, .c 3, .c 13, .c 5, .c 3, .c 83, .c 467,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv89,pv163], .c 3, .c 29, .p pv5 [pv2,pv3,pv3929], .c 3, .c 7,
  .c 11, .c 3, .c 67, .c 5, .c 3, .p pv3 [pv2,pv197,pv359], .c 7, .c 3, .c 5, .c 23, .c 3, .c 11,
  .c 19, .c 3, .c 281, .c 743, .c 3, .c 31, .c 5, .c 3, .c 7, .c 389, .c 3, .c 5, .c 761, .c 3,
  .c 13, .c 7, .c 3, .p pv3 [pv2,pv35363], .c 47, .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv282907],
  .c 43, .c 3, .c 5, .c 13, .c 3, .c 7, .p pv2 [pv2,pv3,pv62869], .c 3, .c 11, .c 653, .c 3,
  .p pv2 [pv2,pv282913], .c 5, .c 3, .c 19, .c 103, .c 3, .c 5, .c 29, .c 3,
  .p pv7 [pv2,pv5,pv113167], .c 17, .c 3, .p pv3 [pv2,pv7,pv13,pv3109], .c 59, .c 3, .c 7, .c 5,
  .c 3, .c 13, .c 11, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv11317], .c 409, .c 3, .c 17,
  .c 53, .c 3, .c 11, .c 5, .c 3, .c 37, .p pv7 [pv2,pv3,pv5,pv9431], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv188621], .c 3, .c 683, .c 61, .c 3, .p pv3 [pv2,pv241,pv587], .c 7, .c 3,
  .c 547, .c 5, .c 3, .p pv2 [pv2,pv31,pv9127], .p pv11 [pv2,pv3,pv5,pv503], .c 3, .c 5, .c 11,
  .c 3, .c 23, .p pv2 [pv2,pv3,pv53,pv3559], .c 3, .c 7, .p pv17 [pv2,pv3,pv11,pv1429], .c 3,
  .c 19, .c 5, .c 3,
]
private theorem h0138c04 : checkBlock 1131523 128 b0138c04 = true := by
  decide +kernel

private def b0138c05 : List Row := [
  .c 11, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv20959], .c 3, .c 809, .c 13, .c 3, .c 59,
  .p pv3 [pv2,pv3,pv188633], .c 3, .c 43, .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 179, .c 3,
  .p pv2 [pv2,pv5,pv56591], .c 7, .c 3, .p pv2 [pv2,pv17,pv33289], .p pv2 [pv2,pv3,pv257,pv367],
  .c 3, .c 79, .c 5, .c 3, .p pv7 [pv2,pv565919], .c 29, .c 3, .c 5, .c 397, .c 3, .c 7, .c 23,
  .c 3, .p pv3 [pv2,pv11,pv59,pv109], .c 293, .c 3, .p pv5 [pv2,pv433,pv1307], .c 5, .c 3,
  .p pv2 [pv2,pv19,pv53,pv281], .c 13, .c 3, .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv28297],
  .p pv2 [pv2,pv3,pv71,pv2657], .c 3, .c 19, .c 11, .c 3, .c 7, .c 5, .c 3, .c 23, .c 47, .c 3,
  .c 5, .c 7, .c 3, .c 11, .p pv5 [pv2,pv3,pv79,pv199], .c 3, .p pv2 [pv2,pv61,pv4639],
  .p pv3 [pv2,pv3,pv188653], .c 3, .c 13, .c 5, .c 3, .c 449, .c 853, .c 3, .c 5,
  .p pv19 [pv2,pv3,pv13,pv907], .c 3, .c 37, .p pv3 [pv2,pv3,pv7,pv26951], .c 3, .c 229, .c 7,
  .c 3, .c 71, .c 5, .c 3, .p pv11 [pv2,pv565979], .p pv11 [pv2,pv3,pv5,pv9433], .c 3, .c 5,
  .c 271, .c 3, .c 131, .p pv2 [pv2,pv3,pv94331], .c 3, .c 7, .c 17, .c 3, .c 337, .c 5, .c 3,
  .c 457, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv31,pv179], .c 3, .c 13,
  .p pv2 [pv2,pv3,pv20963], .c 3, .c 317, .p pv13 [pv2,pv3,pv101,pv467], .c 3, .c 17, .c 5, .c 3,
  .c 7, .c 11, .c 3, .c 5, .c 13, .c 3, .c 137, .c 7,
]
private theorem h0138c05 : checkBlock 1131779 128 b0138c05 = true := by
  decide +kernel

private def b0138c06 : List Row := [
  .c 3, .c 23, .c 19, .c 3, .c 11, .c 5, .c 3, .c 227, .c 41, .c 3, .c 5, .c 191, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv188677], .c 3, .p pv2 [pv2,pv13,pv43541], .c 421, .c 3, .c 29, .c 5, .c 3,
  .c 13, .c 17, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv113209], .c 167, .c 3, .c 857, .c 61,
  .c 3, .c 7, .c 5, .c 3, .c 11, .c 199, .c 3, .c 5, .c 7, .c 3, .c 313,
  .p pv3 [pv2,pv3,pv188687], .c 3, .c 157, .c 23, .c 3, .c 41, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv193,pv419], .p pv29 [pv2,pv3,pv5,pv18869], .c 3, .c 5, .c 43, .c 3, .c 31,
  .c 11, .c 3, .c 13, .c 7, .c 3, .c 37, .c 5, .c 3, .c 89, .c 223, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv103,pv229], .c 3, .c 439, .c 13, .c 3, .c 7, .c 29, .c 3, .c 563, .c 5, .c 3,
  .p pv23 [pv2,pv23,pv151,pv163], .c 7, .c 3, .c 5, .c 877, .c 3, .c 613, .c 31, .c 3, .c 17,
  .c 11, .c 3, .p pv5 [pv2,pv7,pv13,pv6221], .c 5, .c 3, .c 7, .c 499, .c 3, .c 5, .c 37, .c 3,
  .c 11, .c 7, .c 3, .c 29, .p pv7 [pv2,pv3,pv13,pv19,pv191], .c 3, .c 503, .c 5, .c 3,
  .p pv2 [pv2,pv89,pv6361], .c 13, .c 3, .c 5, .c 19, .c 3, .c 7, .c 709, .c 3, .c 47, .c 103,
  .c 3, .c 283, .c 5, .c 3, .c 1021,
]
private theorem h0138c06 : checkBlock 1132035 128 b0138c06 = true := by
  decide +kernel

private def b0138c07 : List Row := [
  .p pv2 [pv2,pv3,pv5,pv23,pv547], .c 3, .c 5, .c 41, .c 3, .p pv2 [pv2,pv5,pv13,pv67], .c 73,
  .c 3, .c 11, .p pv7 [pv2,pv3,pv71,pv443], .c 3, .c 7, .c 5, .c 3, .c 17,
  .p pv13 [pv2,pv3,pv5,pv7,pv337], .c 3, .c 5, .c 7, .c 3, .c 193, .p pv17 [pv2,pv3,pv127,pv743],
  .c 3, .c 31, .c 13, .c 3, .c 19, .c 5, .c 3, .c 151, .c 11, .c 3, .c 5, .c 967, .c 3, .c 163,
  .c 29, .c 3, .c 67, .c 7, .c 3, .c 11, .c 5, .c 3, .c 41, .c 19, .c 3, .c 5, .c 17, .c 3, .c 13,
  .p pv5 [pv2,pv3,pv29,pv1627], .c 3, .c 7, .c 31, .c 3, .p pv2 [pv2,pv566201], .c 5, .c 3,
  .p pv3 [pv2,pv141551], .c 7, .c 3, .c 5, .c 11, .c 3, .c 17, .p pv3 [pv2,pv3,pv37,pv5101], .c 3,
  .c 167, .p pv2 [pv2,pv3,pv11,pv23,pv373], .c 3, .c 139, .c 5, .c 3, .c 7, .c 157, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv59,pv457], .c 3, .c 23, .c 7, .c 3, .c 19, .c 37, .c 3,
  .p pv5 [pv2,pv566231], .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv12583], .c 3, .c 5,
  .p pv13 [pv2,pv3,pv19,pv4967], .c 3, .c 7, .c 11, .c 3, .p pv5 [pv2,pv113,pv5011], .c 17, .c 3,
  .c 787, .c 5, .c 3, .p pv2 [pv2,pv463,pv1223], .c 67, .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv3701],
  .c 3, .p pv7 [pv2,pv5,pv109,pv1039], .c 101, .c 3, .c 181, .p pv3 [pv2,pv3,pv188753], .c 3,
  .c 7, .c 5, .c 3, .p pv3 [pv2,pv70783], .c 383, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv17,pv3331], .c 23, .c 3,
]
private theorem h0138c07 : checkBlock 1132291 128 b0138c07 = true := by
  decide +kernel

private def b0138c08 : List Row := [
  .c 13, .c 11, .c 3, .c 197, .c 5, .c 3, .c 47, .p pv43 [pv2,pv3,pv5,pv11,pv13], .c 3, .c 5,
  .p pv23 [pv2,pv3,pv23,pv29,pv283], .c 3, .c 11, .c 13, .c 3, .c 43, .c 7, .c 3,
  .p pv5 [pv2,pv11,pv51481], .c 5, .c 3, .c 23, .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv10487], .c 3,
  .p pv3 [pv2,pv5,pv7,pv809], .p pv2 [pv2,pv3,pv188767], .c 3, .c 7, .c 19, .c 3, .c 233, .c 5,
  .c 3, .c 109, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv131], .c 3, .c 173,
  .p pv5 [pv2,pv3,pv15731], .c 3, .c 11, .p pv3 [pv2,pv3,pv13,pv1117], .c 3,
  .p pv7 [pv2,pv7,pv17,pv4759], .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 337, .c 3,
  .p pv2 [pv2,pv5,pv56633], .c 7, .c 3, .p pv2 [pv2,pv19,pv41,pv727], .c 97, .c 3,
  .p pv3 [pv2,pv8849], .c 5, .c 3, .p pv7 [pv2,pv31,pv18269], .c 11, .c 3, .c 5, .c 163, .c 3,
  .c 7, .c 17, .c 3, .p pv3 [pv2,pv141587], .c 887, .c 3, .c 11, .c 5, .c 3, .c 31, .c 29, .c 3,
  .c 5, .c 193, .c 3, .p pv3 [pv2,pv5,pv14159], .c 19, .c 3, .c 17, .c 13, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv293,pv1933], .c 59, .c 3, .c 5, .c 7, .c 3, .c 443, .p pv7 [pv2,pv3,pv23599],
  .c 3, .c 131, .c 269, .c 3, .c 251, .c 5, .c 3, .c 11, .c 31, .c 3, .c 5, .c 353, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv7,pv3853], .c 3, .p pv2 [pv2,pv566393], .c 7, .c 3,
  .p pv3 [pv2,pv37,pv43,pv89], .c 5, .c 3, .c 19, .c 373,
]
private theorem h0138c08 : checkBlock 1132547 128 b0138c08 = true := by
  decide +kernel

private def b0138c09 : List Row := [
  .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv7,pv16183], .c 11, .c 3, .c 7, .c 23, .c 3,
  .p pv5 [pv2,pv53,pv10687], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 19, .c 3, .c 47, .c 907,
  .c 3, .c 149, .c 283, .c 3, .c 137, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv79,pv239], .c 3,
  .c 5, .c 83, .c 3, .c 41, .c 7, .c 3, .p pv2 [pv2,pv71,pv3989], .c 11, .c 3,
  .p pv2 [pv2,pv566441], .c 5, .c 3, .c 883, .c 179, .c 3, .c 5, .c 17, .c 3, .c 7, .c 37, .c 3,
  .c 199, .p pv2 [pv2,pv3,pv7,pv13487], .c 3, .c 19, .c 5, .c 3, .p pv7 [pv2,pv59,pv9601], .c 43,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv31,pv6091], .c 3, .c 17, .p pv2 [pv2,pv3,pv19,pv4969], .c 3,
  .c 13, .c 79, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv17,pv16661], .c 19, .c 3, .c 5, .c 7, .c 3,
  .c 463, .c 13, .c 3, .c 11, .p pv11 [pv2,pv3,pv47207], .c 3, .c 311, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv11,pv1051], .c 53, .c 3, .c 5, .p pv2 [pv2,pv3,pv188831], .c 3,
  .p pv13 [pv2,pv5,pv137,pv827], .p pv17 [pv2,pv3,pv7,pv281], .c 3, .p pv2 [pv2,pv149,pv1901],
  .c 7, .c 3, .c 23, .c 5, .c 3, .p pv3 [pv2,pv19,pv3727], .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv17,pv2777], .c 3, .c 859, .c 107, .c 3, .c 7, .c 47, .c 3, .c 11, .c 5, .c 3,
  .p pv13 [pv2,pv397,pv1427], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv19,pv3313], .c 3, .c 37,
  .p pv2 [pv2,pv3,pv94421], .c 3, .c 97,
]
private theorem h0138c09 : checkBlock 1132803 128 b0138c09 = true := by
  decide +kernel

private def b0138c10 : List Row := [
  .c 29, .c 3, .c 223, .c 5, .c 3, .c 7, .p pv19 [pv2,pv3,pv5,pv179,pv211], .c 3, .c 5, .c 11,
  .c 3, .c 31, .c 7, .c 3, .c 53, .c 71, .c 3, .c 13, .c 5, .c 3, .c 11, .c 17, .c 3, .c 5,
  .c 1009, .c 3, .c 7, .c 257, .c 3, .c 29, .c 13, .c 3, .c 47, .c 5, .c 3, .c 761,
  .p pv2 [pv2,pv3,pv5,pv107,pv353], .c 3, .c 5, .c 307, .c 3, .c 19, .c 11, .c 3,
  .p pv2 [pv2,pv7,pv29,pv2791], .p pv2 [pv2,pv3,pv89,pv1061], .c 3, .c 7, .c 5, .c 3,
  .p pv11 [pv2,pv13,pv41,pv1063], .c 433, .c 3, .c 5, .c 7, .c 3, .c 13, .p pv2 [pv2,pv3,pv31477],
  .c 3, .p pv3 [pv2,pv11,pv79,pv163], .c 19, .c 3, .p pv5 [pv2,pv241,pv2351], .c 5, .c 3,
  .p pv3 [pv2,pv7,pv40471], .p pv3 [pv2,pv3,pv5,pv1399], .c 3, .c 5, .c 13, .c 3, .c 1033, .c 17,
  .c 3, .c 277, .c 7, .c 3, .c 59, .c 5, .c 3, .p pv2 [pv2,pv733,pv773], .c 127, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv157,pv401], .c 3, .c 11, .c 23, .c 3, .c 7, .p pv3 [pv2,pv3,pv67,pv2819],
  .c 3, .c 829, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv23,pv2053], .c 3,
  .p pv7 [pv2,pv5,pv56663], .p pv5 [pv2,pv3,pv13,pv29,pv167], .c 3, .c 31, .c 607, .c 3, .c 37,
  .c 5, .c 3, .c 7, .c 41, .c 3, .c 5, .p pv23 [pv2,pv3,pv7,pv11,pv223], .c 3, .c 29, .c 7, .c 3,
  .c 11, .c 53, .c 3, .p pv5 [pv2,pv23,pv71,pv347], .c 5, .c 3, .c 103, .c 47, .c 3,
]
private theorem h0138c10 : checkBlock 1133059 128 b0138c10 = true := by
  decide +kernel

private def b0138c11 : List Row := [
  .c 5, .p pv2 [pv2,pv3,pv31481], .c 3, .c 7, .c 173, .c 3, .c 13, .c 31, .c 3,
  .p pv2 [pv2,pv421,pv673], .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .c 37, .c 3, .c 43, .c 13, .c 3,
  .p pv2 [pv2,pv7,pv17,pv2381], .p pv3 [pv2,pv3,pv47,pv4019], .c 3, .c 7, .c 5, .c 3, .c 19,
  .c 23, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv61,pv929], .c 157, .c 3, .p pv2 [pv2,pv566693],
  .c 619, .c 3, .c 727, .c 5, .c 3, .c 983, .c 137, .c 3, .c 5, .c 11, .c 3, .c 227, .c 79, .c 3,
  .c 23, .c 7, .c 3, .c 241, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 43, .c 3, .c 17, .c 149,
  .c 3, .c 7, .c 59, .c 3, .c 31, .c 5, .c 3, .p pv2 [pv2,pv17,pv37,pv53], .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv188911], .c 3, .c 73, .c 11, .c 3, .p pv2 [pv2,pv283369],
  .p pv7 [pv2,pv3,pv62971], .c 3, .c 13, .c 5, .c 3, .c 7, .c 109, .c 3, .c 5, .c 587, .c 3,
  .p pv2 [pv2,pv5,pv2267], .c 7, .c 3, .p pv2 [pv2,pv11,pv67,pv769], .c 13, .c 3,
  .p pv3 [pv2,pv141689], .c 5, .c 3, .p pv7 [pv2,pv566759], .c 19, .c 3, .c 5, .c 41, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv23,pv37], .c 3, .p pv3 [pv2,pv35423], .c 11, .c 3, .c 17, .c 5, .c 3,
  .c 1039, .p pv3 [pv2,pv3,pv5,pv11,pv229], .c 3, .c 5, .c 151, .c 3, .c 11, .c 61, .c 3, .c 59,
  .c 37,
]
private theorem h0138c11 : checkBlock 1133315 128 b0138c11 = true := by
  decide +kernel

private def b0138c12 : List Row := [
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv19,pv23,pv1297], .c 29, .c 3, .c 5, .c 7, .c 3,
  .p pv17 [pv2,pv5,pv113359], .c 47, .c 3, .c 19, .c 461, .c 3, .c 181, .c 5, .c 3, .c 41, .c 17,
  .c 3, .c 5, .c 53, .c 3, .p pv2 [pv2,pv5,pv56681], .p pv3 [pv2,pv3,pv7,pv2999], .c 3, .c 11,
  .c 7, .c 3, .p pv3 [pv2,pv17713], .c 5, .c 3, .c 13, .p pv7 [pv2,pv3,pv5,pv47,pv67], .c 3, .c 5,
  .c 23, .c 3, .p pv23 [pv2,pv5,pv7,pv41,pv79], .p pv5 [pv2,pv3,pv13,pv43], .c 3, .c 7,
  .p pv7 [pv2,pv3,pv62981], .c 3, .c 367, .c 5, .c 3, .c 173, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv3499], .c 3, .p pv3 [pv2,pv5,pv37,pv383], .p pv2 [pv2,pv3,pv11,pv89,pv193],
  .c 3, .c 47, .p pv11 [pv2,pv3,pv47237], .c 3, .c 11, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5, .c 67,
  .c 3, .c 19, .c 7, .c 3, .c 13, .c 491, .c 3, .c 53, .c 5, .c 3, .c 79,
  .p pv2 [pv2,pv3,pv5,pv13,pv17,pv19], .c 3, .c 5, .c 11, .c 3, .c 7, .c 13, .c 3, .c 17, .c 19,
  .c 3, .c 421, .c 5, .c 3, .c 11, .c 277, .c 3, .c 5, .c 251, .c 3, .c 89, .c 41, .c 3,
  .p pv3 [pv2,pv7,pv53,pv191], .c 229, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv283447], .c 37, .c 3,
  .c 5, .c 7, .c 3, .c 821, .c 11, .c 3, .c 61, .p pv7 [pv2,pv3,pv13,pv23,pv79], .c 3, .c 29,
  .c 5, .c 3, .p pv2 [pv2,pv7,pv109,pv743], .c 13, .c 3, .c 5,
]
private theorem h0138c12 : checkBlock 1133571 128 b0138c12 = true := by
  decide +kernel

private def b0138c13 : List Row := [
  .p pv2 [pv2,pv3,pv101,pv1871], .c 3, .c 23, .c 97, .c 3, .p pv2 [pv2,pv11,pv73,pv353], .c 7,
  .c 3, .p pv2 [pv2,pv29,pv113,pv173], .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv7559], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv31,pv127], .c 3, .p pv2 [pv2,pv5,pv7,pv13,pv89], .c 19, .c 3, .c 7, .c 11,
  .c 3, .c 13, .c 5, .c 3, .c 107, .c 7, .c 3, .c 5, .c 31, .c 3, .c 11, .p pv2 [pv2,pv3,pv10499],
  .c 3, .p pv3 [pv2,pv41,pv3457], .c 13, .c 3, .p pv7 [pv2,pv7,pv11,pv37,pv199], .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv43,pv293], .c 3, .c 5, .c 17, .c 3, .c 59, .c 7, .c 3, .c 101, .c 29,
  .c 3, .p pv2 [pv2,pv197,pv1439], .c 5, .c 3, .c 19, .c 71, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv23,pv83], .c 3, .c 7, .c 43, .c 3, .c 11, .p pv3 [pv2,pv3,pv7,pv19,pv29],
  .c 3, .p pv2 [pv2,pv139,pv4079], .c 5, .c 3, .c 23, .p pv2 [pv2,pv3,pv5,pv37799], .c 3, .c 5,
  .c 13, .c 3, .c 283, .c 127, .c 3, .c 29, .p pv2 [pv2,pv3,pv53,pv1783], .c 3, .c 7, .c 5, .c 3,
  .c 313, .c 11, .c 3, .c 5, .c 7, .c 3, .c 31, .c 37, .c 3, .c 569, .c 17, .c 3, .c 11, .c 5,
  .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv103,pv367], .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv109], .c 3,
  .c 53, .p pv3 [pv2,pv3,pv7,pv13,pv31,pv67], .c 3, .p pv5 [pv2,pv617,pv919], .c 7, .c 3, .c 17,
  .c 5, .c 3, .p pv2 [pv2,pv307,pv1847], .c 23, .c 3, .c 5, .c 11, .c 3,
  .p pv7 [pv2,pv5,pv7,pv17,pv953], .c 31, .c 3, .c 7, .p pv3 [pv2,pv3,pv11,pv17183], .c 3,
]
private theorem h0138c13 : checkBlock 1133827 128 b0138c13 = true := by
  decide +kernel

private def b0138c14 : List Row := [
  .c 71, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 167, .c 3, .c 41, .c 29, .c 3, .c 13, .c 67,
  .c 3, .p pv3 [pv2,pv7,pv61,pv83], .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 89, .c 3, .c 797,
  .c 7, .c 3, .p pv3 [pv2,pv141767], .c 659, .c 3, .p pv5 [pv2,pv41,pv13831], .c 5, .c 3,
  .p pv2 [pv2,pv19,pv14923], .p pv3 [pv2,pv3,pv5,pv7561], .c 3, .c 5, .c 47, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv7001], .c 3, .c 19, .p pv19 [pv2,pv3,pv7,pv43,pv157], .c 3, .c 61, .c 5, .c 3,
  .p pv2 [pv2,pv223,pv2543], .c 113, .c 3, .c 5, .p pv2 [pv2,pv3,pv19,pv9949], .c 3, .c 647,
  .p pv23 [pv2,pv3,pv23629], .c 3, .c 31, .c 11, .c 3, .c 7, .c 5, .c 3, .c 1061, .c 13, .c 3,
  .c 5, .c 7, .c 3, .c 11, .c 17, .c 3, .c 499, .c 397, .c 3, .c 419, .c 5, .c 3,
  .p pv13 [pv2,pv7,pv81017], .p pv7 [pv2,pv3,pv5,pv17,pv139], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv189041], .c 3, .c 47, .c 53, .c 3, .c 17, .c 7, .c 3, .c 13, .c 5, .c 3,
  .c 251, .p pv3 [pv2,pv3,pv5,pv4201], .c 3, .c 5, .c 29, .c 3, .c 19,
  .p pv5 [pv2,pv3,pv79,pv2393], .c 3, .c 7, .c 13, .c 3, .c 373, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv47,pv1097], .c 7, .c 3, .c 5, .c 107, .c 3, .p pv17 [pv2,pv5,pv67,pv1693],
  .p pv5 [pv2,pv3,pv151,pv313], .c 3, .c 163, .c 19, .c 3, .c 179, .c 5, .c 3, .c 7, .c 11, .c 3,
  .c 5, .c 23,
]
private theorem h0138c14 : checkBlock 1134083 128 b0138c14 = true := by
  decide +kernel

private def b0138c15 : List Row := [
  .c 3, .c 13, .c 7, .c 3, .c 41, .c 191, .c 3, .c 11, .c 5, .c 3, .c 17, .c 79, .c 3, .c 5,
  .c 13, .c 3, .c 7, .c 269, .c 3, .c 67, .c 139, .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv41,pv6917], .p pv3 [pv2,pv3,pv5,pv37813], .c 3, .c 5, .c 11, .c 3, .c 223,
  .p pv2 [pv2,pv3,pv189067], .c 3, .c 113, .c 593, .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv67 [pv2,pv3,pv5,pv7,pv37,pv73], .c 3, .c 5, .c 7, .c 3, .c 167, .c 19, .c 3,
  .p pv2 [pv2,pv283609], .c 47, .c 3, .p pv2 [pv2,pv103,pv5507], .c 5, .c 3,
  .p pv11 [pv2,pv7,pv1447], .c 29, .c 3, .c 5, .c 37, .c 3, .c 17, .c 11, .c 3,
  .p pv2 [pv2,pv229,pv2477], .c 7, .c 3, .c 887, .c 5, .c 3, .p pv13 [pv2,pv17,pv61,pv547],
  .p pv7 [pv2,pv3,pv5,pv29,pv163], .c 3, .c 5, .p pv3 [pv2,pv3,pv47,pv149], .c 3, .c 127, .c 73,
  .c 3, .c 7, .c 199, .c 3, .p pv13 [pv2,pv179,pv3169], .c 5, .c 3, .c 19, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv94543], .c 3, .c 23, .c 13, .c 3, .c 83, .c 11, .c 3, .c 47, .c 5, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv5,pv11,pv191], .c 3, .c 5, .c 19, .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv283639], .p pv29 [pv2,pv3,pv63031], .c 3, .c 17, .c 5, .c 3, .c 31, .c 53, .c 3,
  .c 5, .c 571, .c 3, .c 7, .p pv3 [pv2,pv3,pv263,pv719], .c 3, .p pv2 [pv2,pv569,pv997], .c 811,
  .c 3, .c 41,
]
private theorem h0138c15 : checkBlock 1134339 128 b0138c15 = true := by
  decide +kernel

private def b0138c16 : List Row := [
  .c 5, .c 3, .c 349, .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv17191], .c 3,
  .p pv2 [pv2,pv5,pv83,pv1367], .c 23, .c 3, .c 11, .p pv2 [pv2,pv3,pv127,pv1489], .c 3, .c 7,
  .c 5, .c 3, .c 59, .c 17, .c 3, .c 5, .c 7, .c 3, .c 43, .c 163, .c 3, .c 193,
  .p pv7 [pv2,pv3,pv17,pv103], .c 3, .c 13, .c 5, .c 3, .c 23, .c 11, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv13,pv373], .c 3, .c 587, .p pv13 [pv2,pv3,pv7,pv11,pv307], .c 3, .c 53, .c 7,
  .c 3, .c 11, .c 5, .c 3, .c 181, .p pv3 [pv2,pv3,pv5,pv109,pv347], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv47279], .c 3, .c 491, .p pv3 [pv2,pv3,pv21013], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv94559], .c 3, .c 389, .c 5, .c 3, .p pv11 [pv2,pv13,pv19,pv2297], .c 7, .c 3,
  .c 5, .c 11, .c 3, .c 13, .c 17, .c 3, .c 19, .c 859, .c 3, .c 757, .c 5, .c 3, .c 7, .c 23,
  .c 3, .c 5, .c 13, .c 3, .c 751, .c 7, .c 3, .c 17, .p pv19 [pv2,pv3,pv47,pv503], .c 3, .c 227,
  .c 5, .c 3, .c 67, .p pv11 [pv2,pv3,pv5,pv18913], .c 3, .c 5, .p pv2 [pv2,pv3,pv31,pv6101],
  .c 3, .c 7, .c 11, .c 3, .c 23, .c 29, .c 3, .c 97, .c 5, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv5,pv467], .c 3, .c 5, .c 31, .c 3, .p pv2 [pv2,pv5,pv23,pv2467], .c 431, .c 3,
  .c 37, .c 383, .c 3, .c 7, .c 5, .c 3, .c 41, .p pv31 [pv2,pv3,pv5,pv7,pv193], .c 3, .c 5, .c 7,
  .c 3,
]
private theorem h0138c16 : checkBlock 1134595 128 b0138c16 = true := by
  decide +kernel

private def b0138c17 : List Row := [
  .c 19, .c 131, .c 3, .c 29, .c 11, .c 3, .p pv5 [pv2,pv47,pv12073], .c 5, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv5,pv11,pv19,pv181], .c 3, .c 5, .p pv2 [pv2,pv3,pv94573], .c 3, .c 11,
  .p pv2 [pv2,pv3,pv7,pv9007], .c 3, .c 13, .c 7, .c 3, .c 433, .c 5, .c 3, .c 43, .c 37, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv189151], .c 3, .c 269, .c 13, .c 3, .c 7, .c 701, .c 3,
  .p pv2 [pv2,pv191,pv2971], .c 5, .c 3, .p pv3 [pv2,pv89,pv797], .c 7, .c 3, .c 5, .c 17, .c 3,
  .c 31, .c 233, .c 3, .c 11, .c 107, .c 3, .c 157, .c 5, .c 3, .c 7,
  .p pv17 [pv2,pv3,pv5,pv4729], .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv61,pv443], .c 3, .c 17, .c 7,
  .c 3, .p pv3 [pv2,pv8867], .c 307, .c 3, .c 59, .c 5, .c 3, .p pv2 [pv2,pv17,pv16691], .c 11,
  .c 3, .c 5, .c 97, .c 3, .c 7, .c 19, .c 3, .p pv5 [pv2,pv71,pv7993],
  .p pv13 [pv2,pv3,pv7,pv563], .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv541,pv1049],
  .p pv2 [pv2,pv3,pv5,pv18917], .c 3, .c 5, .c 23, .c 3, .c 29, .c 193, .c 3, .c 347, .c 17, .c 3,
  .c 7, .c 5, .c 3, .c 37, .c 181, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv19,pv29,pv103],
  .p pv3 [pv2,pv3,pv63059], .c 3, .c 151, .c 13, .c 3, .c 17, .c 5, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv5,pv1051], .c 3, .c 5, .p pv5 [pv2,pv3,pv37,pv5113], .c 3,
  .p pv2 [pv2,pv5,pv11,pv17,pv607], .p pv2 [pv2,pv3,pv7,pv13513], .c 3, .c 47, .c 7, .c 3,
  .p pv5 [pv2,pv389,pv1459], .c 5,
]
private theorem h0138c17 : checkBlock 1134851 128 b0138c17 = true := by
  decide +kernel

private def b0138c18 : List Row := [
  .c 3, .c 709, .p pv43 [pv2,pv3,pv5,pv157,pv241], .c 3, .c 5, .c 19, .c 3, .c 13, .c 11, .c 3,
  .c 7, .p pv11 [pv2,pv3,pv47297], .c 3, .p pv2 [pv2,pv163,pv1741], .c 5, .c 3, .c 101, .c 7,
  .c 3, .c 5, .c 13, .c 3, .c 79, .c 229, .c 3, .c 43, .p pv3 [pv2,pv3,pv17,pv31,pv359], .c 3,
  .c 103, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv12613], .c 3, .c 5, .c 317, .c 3, .c 67, .c 7,
  .c 3, .p pv2 [pv2,pv13,pv43661], .c 11, .c 3, .c 19, .c 5, .c 3, .c 13,
  .p pv19 [pv2,pv3,pv5,pv11,pv43], .c 3, .c 5, .c 53, .c 3, .c 7, .c 139, .c 3,
  .p pv3 [pv2,pv70951], .c 59, .c 3, .c 73, .c 5, .c 3, .p pv2 [pv2,pv283807], .c 19, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv94603], .c 3, .p pv11 [pv2,pv5,pv101,pv281], .c 17, .c 3,
  .p pv7 [pv2,pv7,pv131,pv619], .c 41, .c 3, .c 7, .c 5, .c 3, .c 521,
  .p pv11 [pv2,pv3,pv5,pv7,pv17,pv53], .c 3, .c 5, .c 7, .c 3, .c 37, .c 251, .c 3, .c 11,
  .p pv13 [pv2,pv3,pv59,pv1069], .c 3, .p pv2 [pv2,pv31,pv18311], .c 5, .c 3, .c 601,
  .p pv2 [pv2,pv3,pv5,pv13,pv41,pv71], .c 3, .c 5, .c 349, .c 3, .c 719, .c 13, .c 3, .c 19, .c 7,
  .c 3, .c 31, .c 5, .c 3, .c 137, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv19,pv23,pv433], .c 3,
  .c 41, .p pv2 [pv2,pv3,pv11,pv47,pv61], .c 3, .c 7, .p pv2 [pv2,pv3,pv189223], .c 3, .c 11,
  .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 83, .c 3, .c 71,
]
private theorem h0138c18 : checkBlock 1135107 128 b0138c18 = true := by
  decide +kernel

private def b0138c19 : List Row := [
  .p pv3 [pv2,pv3,pv17,pv11131], .c 3, .p pv5 [pv2,pv53,pv10711], .c 73, .c 3, .c 89, .c 5, .c 3,
  .c 7, .c 13, .c 3, .c 5, .c 11, .c 3, .c 211, .c 7, .c 3, .c 179, .c 173, .c 3,
  .p pv2 [pv2,pv19,pv29879], .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv37847], .c 3, .c 5, .c 733,
  .c 3, .c 7, .c 277, .c 3, .p pv2 [pv2,pv47,pv257], .p pv19 [pv2,pv3,pv7,pv1931], .c 3, .c 13,
  .c 5, .c 3, .p pv7 [pv2,pv567719], .c 23, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv22709],
  .c 11, .c 3, .c 659, .c 13, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv31,pv9157], .c 827, .c 3,
  .c 5, .c 7, .c 3, .c 17, .p pv5 [pv2,pv3,pv97,pv1951], .c 3, .c 23, .c 239, .c 3, .c 37, .c 5,
  .c 3, .c 31, .c 43, .c 3, .c 5, .c 127, .c 3, .c 13, .p pv5 [pv2,pv3,pv7,pv751], .c 3, .c 359,
  .c 7, .c 3, .c 83, .c 5, .c 3, .c 149, .p pv3 [pv2,pv3,pv5,pv11,pv31,pv37], .c 3, .c 5, .c 13,
  .c 3, .c 11, .c 101, .c 3, .c 7, .c 17, .c 3, .c 29, .c 5, .c 3, .c 541, .c 7, .c 3, .c 5,
  .c 37, .c 3, .c 563, .c 19, .c 3, .c 41, .c 23, .c 3, .c 17, .c 5, .c 3, .c 7, .c 107, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv7,pv11,pv1229], .c 3, .c 353, .c 7, .c 3, .c 11, .c 881, .c 3,
  .p pv2 [pv2,pv193,pv1471], .c 5, .c 3,
]
private theorem h0138c19 : checkBlock 1135363 128 b0138c19 = true := by
  decide +kernel

private def b0138c20 : List Row := [
  .p pv2 [pv2,pv11,pv41,pv1259], .c 163, .c 3, .c 5, .c 1039, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv59,pv401], .c 3, .c 61, .c 131, .c 3, .p pv2 [pv2,pv233,pv2437], .c 5, .c 3,
  .c 19, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv15773], .c 3, .c 47, .p pv3 [pv2,pv3,pv11,pv17207],
  .c 3, .c 13, .c 29, .c 3, .c 7, .c 5, .c 3, .c 283, .c 227, .c 3, .c 5, .c 7, .c 3, .c 59,
  .c 13, .c 3, .c 607, .p pv3 [pv2,pv3,pv29,pv61,pv107], .c 3, .p pv5 [pv2,pv17,pv33403], .c 5,
  .c 3, .c 479, .p pv3 [pv2,pv3,pv5,pv12619], .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv28393],
  .c 557, .c 3, .c 29, .c 7, .c 3, .p pv2 [pv2,pv13,pv21841], .c 5, .c 3, .c 11, .c 41, .c 3,
  .c 5, .c 31, .c 3, .p pv7 [pv2,pv5,pv7,pv11,pv59], .c 17, .c 3, .c 7, .c 43, .c 3, .c 19, .c 5,
  .c 3, .c 139, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv11831], .c 3, .c 103, .c 11, .c 3, .c 17,
  .c 37, .c 3, .c 409, .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 73, .c 3, .c 317, .c 7, .c 3,
  .c 397, .p pv3 [pv2,pv3,pv89,pv709], .c 3, .c 13, .c 5, .c 3, .c 683,
  .p pv3 [pv2,pv3,pv5,pv37861], .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv809], .c 3, .c 7, .c 29, .c 3,
  .p pv5 [pv2,pv101,pv5623], .c 11, .c 3, .p pv2 [pv2,pv443,pv641], .c 5, .c 3,
  .p pv2 [pv2,pv19,pv71,pv421], .p pv2 [pv2,pv3,pv5,pv11,pv1721], .c 3, .c 5, .c 137, .c 3, .c 11,
  .p pv5 [pv2,pv3,pv17,pv29],
]
private theorem h0138c20 : checkBlock 1135619 128 b0138c20 = true := by
  decide +kernel

private def b0138c21 : List Row := [
  .c 3, .c 19, .p pv3 [pv2,pv3,pv23,pv8231], .c 3, .c 7, .c 5, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv5,pv7,pv601], .c 3, .c 5, .c 7, .c 3, .c 13, .p pv5 [pv2,pv3,pv31,pv197],
  .c 3, .c 89, .c 419, .c 3, .p pv3 [pv2,pv107,pv1327], .c 5, .c 3, .p pv7 [pv2,pv7,pv67,pv173],
  .p pv13 [pv2,pv3,pv5,pv4733], .c 3, .c 5, .c 13, .c 3, .c 43, .c 31, .c 3, .c 11, .c 7, .c 3,
  .c 47, .c 5, .c 3, .c 53, .p pv3 [pv2,pv3,pv5,pv7573], .c 3, .c 5, .c 17, .c 3, .c 293,
  .p pv3 [pv2,pv3,pv223,pv283], .c 3, .c 7, .p pv11 [pv2,pv3,pv11833], .c 3, .c 151, .c 5, .c 3,
  .c 13, .c 7, .c 3, .c 5, .c 41, .c 3, .c 17, .c 23, .c 3, .p pv2 [pv2,pv89,pv3191],
  .p pv3 [pv2,pv3,pv109,pv193], .c 3, .c 11, .c 5, .c 3, .c 7, .c 37, .c 3, .c 5, .c 29, .c 3,
  .c 83, .c 7, .c 3, .c 337, .c 19, .c 3, .c 401, .c 5, .c 3, .c 23, .p pv31 [pv2,pv3,pv5,pv9467],
  .c 3, .c 5, .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv67,pv157], .c 3, .c 13, .c 17, .c 3,
  .p pv5 [pv2,pv23,pv24697], .c 5, .c 3, .c 11, .c 71, .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv5569],
  .c 3, .p pv3 [pv2,pv5,pv11,pv1291], .c 13, .c 3, .p pv5 [pv2,pv7,pv19,pv4271],
  .p pv7 [pv2,pv3,pv31,pv509], .c 3, .c 7, .c 5, .c 3, .c 73, .c 167, .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv17,pv41,pv163], .c 11, .c 3, .p pv2 [pv2,pv431,pv659], .c 31, .c 3,
  .p pv2 [pv2,pv13,pv37,pv1181], .c 5, .c 3, .p pv3 [pv2,pv7,pv317],
]
private theorem h0138c21 : checkBlock 1135875 128 b0138c21 = true := by
  decide +kernel

private def b0138c22 : List Row := [
  .c 23, .c 3, .c 5, .c 181, .c 3, .c 137, .c 19, .c 3, .p pv5 [pv2,pv11,pv43,pv1201], .c 7, .c 3,
  .p pv3 [pv2,pv142019], .c 5, .c 3, .c 37, .c 13, .c 3, .c 5, .c 929, .c 3, .c 487, .c 761, .c 3,
  .c 7, .c 11, .c 3, .p pv5 [pv2,pv568091], .c 5, .c 3, .c 43, .c 7, .c 3, .c 5, .c 257, .c 3,
  .c 11, .p pv2 [pv2,pv3,pv409,pv463], .c 3, .c 307, .c 157, .c 3, .c 13, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv29,pv653], .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv13,pv2081], .c 3,
  .p pv13 [pv2,pv5,pv113623], .c 7, .c 3, .p pv2 [pv2,pv284059], .c 13, .c 3, .c 31, .c 5, .c 3,
  .c 29, .c 977, .c 3, .c 5, .c 19, .c 3, .c 7, .c 17, .c 3, .c 11, .c 23, .c 3, .c 163, .c 5,
  .c 3, .c 421, .c 59, .c 3, .c 5, .p pv3 [pv2,pv3,pv63127], .c 3, .c 13, .c 569, .c 3, .c 17,
  .p pv13 [pv2,pv3,pv229,pv827], .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv61,pv4657], .c 11, .c 3,
  .c 5, .c 7, .c 3, .c 701, .c 331, .c 3, .p pv5 [pv2,pv568163], .p pv11 [pv2,pv3,pv113,pv419],
  .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv7,pv23,pv3529], .c 233, .c 3, .c 5, .c 1063, .c 3,
  .c 101, .c 83, .c 3, .p pv2 [pv2,pv13,pv41], .c 7, .c 3, .p pv2 [pv2,pv227,pv2503], .c 5, .c 3,
  .c 13, .c 19, .c 3, .c 5, .c 11, .c 3, .c 37, .p pv3 [pv2,pv3,pv13,pv17,pv857], .c 3,
]
private theorem h0138c22 : checkBlock 1136131 128 b0138c22 = true := by
  decide +kernel

private def b0138c23 : List Row := [
  .c 7, .p pv2 [pv2,pv3,pv11,pv8609], .c 3, .p pv3 [pv2,pv142049], .c 5, .c 3, .c 11, .c 7, .c 3,
  .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv11,pv10331], .c 47, .c 3, .p pv3 [pv2,pv17,pv2089], .c 449,
  .c 3, .c 29, .c 5, .c 3, .c 7, .c 631, .c 3, .c 5, .c 173, .c 3, .c 89, .c 7, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv1973], .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv59,pv9631],
  .p pv2 [pv2,pv3,pv5,pv13,pv31,pv47], .c 3, .c 5, .c 17, .c 3, .c 7, .c 13, .c 3,
  .p pv2 [pv2,pv11,pv23,pv1123], .c 41, .c 3, .p pv2 [pv2,pv568241], .c 5, .c 3, .c 199, .c 31,
  .c 3, .c 5, .c 71, .c 3, .c 17, .c 313, .c 3, .c 47, .c 11, .c 3, .c 7, .c 5, .c 3, .c 83,
  .c 67, .c 3, .c 5, .c 7, .c 3, .c 11, .c 43, .c 3, .c 73, .c 29, .c 3, .c 109, .c 5, .c 3,
  .c 97, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv131,pv241], .c 3, .c 19, .c 823, .c 3,
  .p pv5 [pv2,pv37,pv15359], .c 7, .c 3, .c 79, .c 5, .c 3, .p pv2 [pv2,pv568289], .c 937, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv11,pv17,pv1013], .c 3, .c 23, .p pv5 [pv2,pv3,pv877], .c 3, .c 7, .c 19,
  .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv11,pv3229], .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv3643], .c 3, .c 379, .p pv5 [pv2,pv3,pv189437], .c 3,
  .p pv2 [pv2,pv29,pv19597], .c 13, .c 3, .p pv3 [pv2,pv7,pv20297], .c 5, .c 3, .c 7, .c 11,
]
private theorem h0138c23 : checkBlock 1136387 128 b0138c23 = true := by
  decide +kernel

private def b0138c24 : List Row := [
  .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv31,pv97], .c 3, .p pv2 [pv2,pv5,pv127,pv179], .c 7, .c 3,
  .c 211, .p pv3 [pv2,pv3,pv389,pv487], .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv13,pv21859], .c 17,
  .c 3, .c 5, .c 31, .c 3, .c 7, .c 23, .c 3, .c 131, .c 137, .c 3, .c 349, .c 5, .c 3,
  .p pv2 [pv2,pv568349], .c 337, .c 3, .c 5, .c 11, .c 3, .c 257, .c 19, .c 3,
  .p pv3 [pv2,pv7,pv40597], .p pv3 [pv2,pv3,pv11,pv5741], .c 3, .c 7, .c 5, .c 3, .c 11, .c 79,
  .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv11,pv5167], .c 97, .c 3, .c 419,
  .p pv2 [pv2,pv3,pv43,pv2203], .c 3, .c 59, .c 5, .c 3, .c 13, .c 109, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv41,pv4621], .c 3, .c 29, .c 11, .c 3, .c 127, .c 7, .c 3, .c 173, .c 5, .c 3,
  .c 19, .c 43, .c 3, .c 5, .c 53, .c 3, .c 31, .c 919, .c 3, .c 7, .p pv13 [pv2,pv3,pv19,pv277],
  .c 3, .p pv2 [pv2,pv59,pv4817], .c 5, .c 3, .p pv2 [pv2,pv131,pv4339], .c 7, .c 3, .c 5, .c 19,
  .c 3, .p pv11 [pv2,pv5,pv113683], .p pv5 [pv2,pv3,pv31,pv191], .c 3, .c 13, .c 11, .c 3,
  .p pv2 [pv2,pv7,pv81203], .c 5, .c 3, .c 7, .c 83, .c 3, .c 5, .c 61, .c 3, .c 11, .c 7, .c 3,
  .c 23, .p pv2 [pv2,pv3,pv211,pv449], .c 3, .c 653, .c 5, .c 3, .c 151, .c 139, .c 3, .c 5,
  .c 29, .c 3, .c 7, .c 113, .c 3, .p pv3 [pv2,pv4441],
]
private theorem h0138c24 : checkBlock 1136643 128 b0138c24 = true := by
  decide +kernel

private def b0138c25 : List Row := [
  .c 37, .c 3, .c 19, .c 5, .c 3, .c 17, .c 607, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv29], .c 3,
  .p pv13 [pv2,pv5,pv43,pv661], .c 67, .c 3, .c 11, .c 953, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv51679], .c 13, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv22739], .c 359,
  .c 3, .c 101, .c 23, .c 3, .c 43, .c 5, .c 3, .p pv3 [pv2,pv7,pv79,pv257], .c 11, .c 3, .c 5,
  .c 17, .c 3, .p pv3 [pv2,pv5,pv13,pv4373], .p pv5 [pv2,pv3,pv7,pv11,pv23,pv107], .c 3, .c 31,
  .c 7, .c 3, .c 11, .c 5, .c 3, .p pv13 [pv2,pv19,pv29921], .p pv11 [pv2,pv3,pv5,pv379], .c 3,
  .c 5, .p pv3 [pv2,pv3,pv13,pv43,pv113], .c 3, .c 17, .c 353, .c 3, .c 7, .c 13, .c 3, .c 191,
  .c 5, .c 3, .p pv2 [pv2,pv17,pv23,pv727], .c 7, .c 3, .c 5, .c 11, .c 3, .c 971, .c 227, .c 3,
  .c 37, .c 31, .c 3, .c 41, .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv27073],
  .c 3, .c 13, .c 7, .c 3, .c 223, .c 17, .c 3, .c 773, .c 5, .c 3, .c 107,
  .p pv2 [pv2,pv3,pv5,pv29,pv1307], .c 3, .c 5, .c 13, .c 3, .c 7, .c 11, .c 3, .c 59,
  .p pv11 [pv2,pv3,pv7,pv13537], .c 3, .c 17, .c 5, .c 3, .c 29, .c 37, .c 3, .c 5, .c 383, .c 3,
  .c 19, .c 293, .c 3, .p pv3 [pv2,pv7,pv11,pv13,pv71], .p pv2 [pv2,pv3,pv189523], .c 3, .c 7,
  .c 5, .c 3, .c 13, .c 157, .c 3,
]
private theorem h0138c25 : checkBlock 1136899 128 b0138c25 = true := by
  decide +kernel

private def b0138c26 : List Row := [
  .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv28429], .p pv2 [pv2,pv3,pv13,pv61,pv239], .c 3,
  .p pv5 [pv2,pv23,pv59,pv419], .c 11, .c 3, .c 31, .c 5, .c 3, .p pv2 [pv2,pv7,pv43,pv1889],
  .c 17, .c 3, .c 5, .c 179, .c 3, .c 11, .c 1031, .c 3, .c 109, .c 7, .c 3,
  .p pv2 [pv2,pv11,pv51691], .c 5, .c 3, .p pv3 [pv2,pv142151], .c 131, .c 3, .c 5, .c 41, .c 3,
  .c 43, .c 61, .c 3, .c 7, .p pv2 [pv2,pv3,pv97,pv977], .c 3, .p pv3 [pv2,pv17,pv37,pv113], .c 5,
  .c 3, .c 857, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv17231], .c 3, .c 163, .c 13, .c 3, .c 11,
  .c 47, .c 3, .p pv5 [pv2,pv7,pv81233], .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv167,pv227], .c 3,
  .c 5, .c 373, .c 3, .c 23, .c 7, .c 3, .c 461, .p pv17 [pv2,pv3,pv47387], .c 3, .c 29, .c 5,
  .c 3, .c 41, .c 11, .c 3, .c 5, .c 43, .c 3, .c 7, .p pv5 [pv2,pv3,pv11,pv359], .c 3, .c 17,
  .c 797, .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv31,pv2293], .c 13, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv47389], .c 3, .p pv2 [pv2,pv5,pv19,pv41,pv73], .c 37, .c 3, .c 947, .c 71,
  .c 3, .c 7, .c 5, .c 3, .c 19, .c 101, .c 3, .c 5, .c 7, .c 3, .c 881, .c 23, .c 3, .c 283,
  .c 379, .c 3, .c 13, .c 5, .c 3, .c 11, .c 349, .c 3, .c 5, .c 19, .c 3, .c 239,
  .p pv3 [pv2,pv3,pv7,pv17,pv59], .c 3, .p pv5 [pv2,pv61,pv9323], .c 7,
]
private theorem h0138c26 : checkBlock 1137155 128 b0138c26 = true := by
  decide +kernel

private def b0138c27 : List Row := [
  .c 3, .c 73, .c 5, .c 3, .c 17, .c 31, .c 3, .c 5, .p pv2 [pv2,pv3,pv293,pv647], .c 3, .c 569,
  .c 11, .c 3, .c 7, .p pv3 [pv2,pv3,pv29,pv2179], .c 3, .c 229, .c 5, .c 3, .c 439, .c 7, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv2633], .c 3, .c 13, .c 41, .c 3, .c 29, .c 877, .c 3, .c 19, .c 5, .c 3,
  .c 7, .p pv13 [pv2,pv3,pv5,pv9479], .c 3, .c 5, .c 13, .c 3, .c 37, .c 7, .c 3, .c 227, .c 11,
  .c 3, .p pv5 [pv2,pv568751], .c 5, .c 3, .c 89, .c 19, .c 3, .c 5, .c 107, .c 3, .c 7, .c 223,
  .c 3, .p pv5 [pv2,pv13,pv67,pv653], .p pv31 [pv2,pv3,pv7,pv37,pv61], .c 3, .c 743, .c 5, .c 3,
  .c 13, .c 47, .c 3, .c 5, .p pv11 [pv2,pv3,pv63197], .c 3, .p pv29 [pv2,pv5,pv22751],
  .p pv11 [pv2,pv3,pv13,pv1823], .c 3, .c 23, .c 73, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv19,pv1871], .c 113, .c 3, .c 5, .c 7, .c 3, .c 661, .c 29, .c 3, .c 11, .c 17,
  .c 3, .c 67, .c 5, .c 3, .c 1013, .c 269, .c 3, .c 5, .c 31, .c 3, .p pv2 [pv2,pv5,pv113761],
  .p pv17 [pv2,pv3,pv7,pv29,pv467], .c 3, .c 13, .c 7, .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv284407], .c 11, .c 3, .c 5, .c 401, .c 3, .c 29, .c 13, .c 3, .c 7, .c 23, .c 3,
  .c 11, .c 5, .c 3, .p pv2 [pv2,pv271,pv2099], .c 7, .c 3, .c 5,
]
private theorem h0138c27 : checkBlock 1137411 128 b0138c27 = true := by
  decide +kernel

private def b0138c28 : List Row := [
  .p pv2 [pv2,pv3,pv127,pv1493], .c 3, .c 359, .p pv5 [pv2,pv3,pv23,pv229], .c 3,
  .p pv2 [pv2,pv37,pv7687], .c 79, .c 3, .c 199, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 11, .c 3,
  .c 19, .c 7, .c 3, .p pv2 [pv2,pv568853], .c 41, .c 3, .c 37, .c 5, .c 3, .c 11, .c 13, .c 3,
  .c 5, .c 67, .c 3, .c 7, .p pv2 [pv2,pv3,pv94811], .c 3, .c 43, .c 19, .c 3,
  .p pv5 [pv2,pv17,pv109,pv307], .c 5, .c 3, .p pv2 [pv2,pv461,pv617], .c 53, .c 3, .c 5, .c 29,
  .c 3, .c 241, .c 11, .c 3, .p pv5 [pv2,pv7,pv181,pv449], .c 281, .c 3, .c 7, .c 5, .c 3, .c 157,
  .p pv2 [pv2,pv3,pv5,pv7,pv43], .c 3, .c 5, .c 7, .c 3, .c 41, .c 17, .c 3, .c 113, .c 13, .c 3,
  .p pv2 [pv2,pv397,pv1433], .c 5, .c 3, .p pv3 [pv2,pv7,pv10159],
  .p pv11 [pv2,pv3,pv5,pv17,pv23,pv97], .c 3, .c 5, .p pv5 [pv2,pv3,pv15803], .c 3, .c 173, .c 43,
  .c 3, .c 17, .c 7, .c 3, .c 23, .c 5, .c 3, .c 911, .c 103, .c 3, .c 5, .c 83, .c 3, .c 11,
  .c 19, .c 3, .c 7, .p pv2 [pv2,pv3,pv189643], .c 3, .p pv5 [pv2,pv11,pv51721], .c 5, .c 3,
  .p pv2 [pv2,pv284467], .c 7, .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv28447],
  .p pv3 [pv2,pv3,pv199,pv953], .c 3, .p pv5 [pv2,pv31,pv18353], .p pv23 [pv2,pv3,pv439], .c 3,
  .c 383, .c 5, .c 3, .c 7, .c 229, .c 3, .c 5, .c 97, .c 3, .p pv11 [pv2,pv5,pv19,pv53,pv113],
  .c 7, .c 3, .c 11, .p pv17 [pv2,pv3,pv189653], .c 3,
]
private theorem h0138c28 : checkBlock 1137667 128 b0138c28 = true := by
  decide +kernel

private def b0138c29 : List Row := [
  .c 211, .c 5, .c 3, .c 13, .c 29, .c 3, .c 5, .p pv5 [pv2,pv3,pv151,pv157], .c 3, .c 7, .c 283,
  .c 3, .c 181, .c 311, .c 3, .p pv3 [pv2,pv43,pv827], .c 5, .c 3, .p pv7 [pv2,pv568979], .c 11,
  .c 3, .c 5, .c 19, .c 3, .c 23, .p pv5 [pv2,pv3,pv11,pv37,pv233], .c 3, .p pv3 [pv2,pv7,pv2903],
  .c 31, .c 3, .c 7, .c 5, .c 3, .c 29, .p pv3 [pv2,pv3,pv5,pv7,pv5419], .c 3, .c 5, .c 7, .c 3,
  .c 263, .c 571, .c 3, .c 13, .c 37, .c 3, .c 83, .c 5, .c 3, .p pv2 [pv2,pv7,pv29,pv2803],
  .c 887, .c 3, .c 5, .c 11, .c 3, .c 17, .c 13, .c 3, .c 41, .c 7, .c 3, .c 19, .c 5, .c 3,
  .c 11, .c 59, .c 3, .c 5, .p pv13 [pv2,pv3,pv47419], .c 3, .p pv2 [pv2,pv5,pv7,pv11,pv739],
  .c 23, .c 3, .c 7, .c 53, .c 3, .c 647, .c 5, .c 3, .c 467, .c 7, .c 3, .c 5, .c 151, .c 3,
  .p pv2 [pv2,pv5,pv113809], .c 11, .c 3, .p pv3 [pv2,pv83,pv857], .c 17, .c 3, .c 31, .c 5, .c 3,
  .c 7, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv17,pv797], .c 3, .c 193, .c 7, .c 3,
  .p pv5 [pv2,pv11,pv4703], .c 67, .c 3, .c 17, .c 5, .c 3, .c 269, .p pv2 [pv2,pv3,pv5,pv6323],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv189691], .c 3, .c 7, .c 79, .c 3, .c 19, .c 11, .c 3, .c 13, .c 5,
  .c 3, .c 59, .p pv23 [pv2,pv3,pv5,pv11,pv3449], .c 3, .c 5, .c 719,
]
private theorem h0138c29 : checkBlock 1137923 128 b0138c29 = true := by
  decide +kernel

private def b0138c30 : List Row := [
  .c 3, .c 11, .p pv3 [pv2,pv3,pv189697], .c 3, .c 883, .c 13, .c 3, .c 7, .c 5, .c 3, .c 47,
  .c 17, .c 3, .c 5, .c 7, .c 3, .c 149, .p pv2 [pv2,pv3,pv1171], .c 3, .c 829, .c 499, .c 3,
  .c 1019, .c 5, .c 3, .c 163, .c 37, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv8623], .c 3, .c 13,
  .c 241, .c 3, .c 11, .c 7, .c 3, .c 43, .c 5, .c 3, .c 131, .c 179, .c 3, .c 5, .c 13, .c 3,
  .c 19, .p pv5 [pv2,pv3,pv71,pv167], .c 3, .c 7, .c 29, .c 3, .c 41, .c 5, .c 3, .c 31, .c 7,
  .c 3, .c 5, .c 863, .c 3, .c 127, .c 17, .c 3, .c 547, .c 19, .c 3, .c 11, .c 5, .c 3, .c 7,
  .c 61, .c 3, .c 5, .c 439, .c 3, .c 281, .c 7, .c 3, .c 17, .c 23, .c 3, .c 71, .c 5, .c 3,
  .c 733, .c 31, .c 3, .c 5, .c 11, .c 3, .c 7, .p pv13 [pv2,pv3,pv23,pv73,pv113], .c 3,
  .p pv5 [pv2,pv19,pv29,pv1033], .p pv19 [pv2,pv3,pv7,pv11], .c 3, .c 107, .c 5, .c 3, .c 11,
  .c 313, .c 3, .c 5, .c 47, .c 3, .p pv7 [pv2,pv5,pv11,pv79,pv131], .p pv5 [pv2,pv3,pv97,pv163],
  .c 3, .c 13, .c 89, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv23,pv269],
  .p pv17 [pv2,pv3,pv5,pv7,pv13,pv139], .c 3, .c 5, .c 7, .c 3, .c 577, .c 11, .c 3,
  .p pv2 [pv2,pv569213], .p pv2 [pv2,pv3,pv83,pv127], .c 3, .p pv3 [pv2,pv4447],
]
private theorem h0138c30 : checkBlock 1138179 128 b0138c30 = true := by
  decide +kernel

private def b0138c31 : List Row := [
  .c 5, .c 3, .c 17, .p pv7 [pv2,pv3,pv5,pv53,pv179], .c 3, .c 5, .c 41, .c 3,
  .p pv2 [pv2,pv5,pv22769], .c 29, .c 3, .p pv3 [pv2,pv11,pv17,pv761], .c 7, .c 3, .c 197, .c 5,
  .c 3, .c 79, .c 271, .c 3, .c 5, .c 23, .c 3, .c 47, .p pv2 [pv2,pv3,pv29,pv727], .c 3, .c 7,
  .c 11, .c 3, .c 53, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 17, .c 3, .c 11, .c 173, .c 3,
  .c 463, .p pv3 [pv2,pv3,pv19,pv3329], .c 3, .c 23, .c 5, .c 3, .c 7, .c 67, .c 3, .c 5, .c 19,
  .c 3, .c 17, .c 7, .c 3, .p pv2 [pv2,pv23,pv53,pv467], .c 139, .c 3, .c 13, .c 5, .c 3,
  .p pv7 [pv2,pv17,pv33487], .c 683, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv13,pv1327], .c 3, .c 7,
  .c 101, .c 3, .c 11, .c 13, .c 3, .c 479, .c 5, .c 3, .p pv2 [pv2,pv11,pv113,pv229],
  .p pv3 [pv2,pv3,pv5,pv4217], .c 3, .c 5, .c 43, .c 3, .c 37, .c 389, .c 3, .c 137, .c 17, .c 3,
  .c 7, .c 5, .c 3, .c 179, .c 11, .c 3, .c 5, .c 7, .c 3, .c 13, .c 509, .c 3,
  .p pv2 [pv2,pv284659], .p pv19 [pv2,pv3,pv23,pv37,pv223], .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv20333], .c 19, .c 3, .c 5, .c 13, .c 3, .c 23, .c 307, .c 3,
  .p pv2 [pv2,pv89,pv6397], .c 7, .c 3, .p pv3 [pv2,pv71167], .c 5, .c 3,
  .p pv11 [pv2,pv199,pv2861], .p pv7 [pv2,pv3,pv5,pv3163], .c 3, .c 5, .c 11, .c 3,
]
private theorem h0138c31 : checkBlock 1138435 128 b0138c31 = true := by
  decide +kernel

def rows0138 : List Row :=
  b0138c00 ++ b0138c01 ++ b0138c02 ++ b0138c03 ++ b0138c04 ++ b0138c05 ++ b0138c06 ++ b0138c07 ++
  b0138c08 ++ b0138c09 ++ b0138c10 ++ b0138c11 ++ b0138c12 ++ b0138c13 ++ b0138c14 ++ b0138c15 ++
  b0138c16 ++ b0138c17 ++ b0138c18 ++ b0138c19 ++ b0138c20 ++ b0138c21 ++ b0138c22 ++ b0138c23 ++
  b0138c24 ++ b0138c25 ++ b0138c26 ++ b0138c27 ++ b0138c28 ++ b0138c29 ++ b0138c30 ++ b0138c31

theorem checked0138 : checkBlock 1130499 4096 rows0138 = true :=
  checkBlock_append h0138c00 (
    checkBlock_append h0138c01 (
    checkBlock_append h0138c02 (
    checkBlock_append h0138c03 (
    checkBlock_append h0138c04 (
    checkBlock_append h0138c05 (
    checkBlock_append h0138c06 (
    checkBlock_append h0138c07 (
    checkBlock_append h0138c08 (
    checkBlock_append h0138c09 (
    checkBlock_append h0138c10 (
    checkBlock_append h0138c11 (
    checkBlock_append h0138c12 (
    checkBlock_append h0138c13 (
    checkBlock_append h0138c14 (
    checkBlock_append h0138c15 (
    checkBlock_append h0138c16 (
    checkBlock_append h0138c17 (
    checkBlock_append h0138c18 (
    checkBlock_append h0138c19 (
    checkBlock_append h0138c20 (
    checkBlock_append h0138c21 (
    checkBlock_append h0138c22 (
    checkBlock_append h0138c23 (
    checkBlock_append h0138c24 (
    checkBlock_append h0138c25 (
    checkBlock_append h0138c26 (
    checkBlock_append h0138c27 (
    checkBlock_append h0138c28 (
    checkBlock_append h0138c29 (
    checkBlock_append h0138c30 (
    h0138c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
