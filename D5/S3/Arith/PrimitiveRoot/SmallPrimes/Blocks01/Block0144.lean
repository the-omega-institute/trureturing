/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0144
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0144.checked0144
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table119

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0144c00 : List Row := [
  .c 3, .c 19, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 829, .c 3, .c 37, .c 11, .c 3,
  .p pv2 [pv2,pv294919], .c 61, .c 3, .c 937, .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 313, .c 3,
  .c 211, .c 7, .c 3, .c 79, .c 443, .c 3, .c 787, .c 5, .c 3, .c 227, .c 863, .c 3, .c 5, .c 53,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv17,pv5783], .c 3, .c 13, .c 11, .c 3, .c 277, .c 5, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv5,pv11,pv13], .c 3, .c 5, .p pv2 [pv2,pv3,pv32771], .c 3, .c 11, .c 13, .c 3,
  .c 19, .c 673, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv29,pv20341], .c 101, .c 3, .c 5, .c 7,
  .c 3, .c 43, .p pv5 [pv2,pv3,pv2731], .c 3, .p pv2 [pv2,pv294949], .c 373, .c 3, .c 67, .c 5,
  .c 3, .c 193, .c 97, .c 3, .c 5, .c 17, .c 3, .c 751, .c 59, .c 3, .c 11, .c 7, .c 3, .c 53,
  .c 5, .c 3, .p pv11 [pv2,pv11,pv53629], .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv7283], .c 3, .c 17,
  .p pv2 [pv2,pv3,pv98321], .c 3, .c 7, .p pv2 [pv2,pv3,pv196643], .c 3,
  .p pv11 [pv2,pv19,pv61,pv509], .c 5, .c 3, .p pv2 [pv2,pv17,pv17351], .c 7, .c 3, .c 5, .c 23,
  .c 3, .c 19, .p pv2 [pv2,pv3,pv11,pv59,pv101], .c 3, .c 257, .c 107, .c 3, .c 11, .c 5, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv5,pv19,pv23], .c 3, .c 5,
]
private theorem h0144c00 : checkBlock 1179651 128 b0144c00 = true := by
  decide +kernel

private def b0144c01 : List Row := [
  .p pv5 [pv2,pv3,pv7,pv13,pv2161], .c 3, .c 293, .c 7, .c 3, .c 131, .c 13, .c 3, .c 23, .c 5,
  .c 3, .p pv3 [pv2,pv83,pv1777], .c 149, .c 3, .c 5, .c 11, .c 3, .c 7, .c 239, .c 3,
  .p pv2 [pv2,pv23,pv113,pv227], .c 71, .c 3, .c 17, .c 5, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv5,pv9833], .c 3, .c 5, .c 37, .c 3, .c 13, .p pv2 [pv2,pv3,pv73,pv449], .c 3,
  .p pv3 [pv2,pv7,pv19,pv1109], .p pv3 [pv2,pv3,pv196663], .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv294997], .p pv7 [pv2,pv3,pv5,pv7,pv1873], .c 3, .c 5, .c 7, .c 3, .c 487, .c 11,
  .c 3, .c 907, .p pv7 [pv2,pv3,pv607], .c 3, .p pv2 [pv2,pv157,pv1879], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv12041], .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv65557], .c 3,
  .p pv13 [pv2,pv5,pv197,pv599], .c 19, .c 3, .c 229, .c 7, .c 3, .p pv2 [pv2,pv590021], .c 5,
  .c 3, .c 13, .c 89, .c 3, .c 5, .p pv11 [pv2,pv3,pv49169], .c 3, .c 23, .c 421, .c 3, .c 7,
  .c 11, .c 3, .p pv3 [pv2,pv17,pv8677], .c 5, .c 3, .c 353, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv196681], .c 3, .c 11, .p pv2 [pv2,pv3,pv43,pv2287], .c 3, .c 29,
  .p pv2 [pv2,pv3,pv53,pv1237], .c 3, .c 41, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv139,pv283],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv223], .c 3, .p pv3 [pv2,pv5,pv163,pv181], .c 7, .c 3, .c 13,
  .c 827, .c 3, .p pv2 [pv2,pv295033], .c 5, .c 3, .c 31, .p pv2 [pv2,pv3,pv5,pv13,pv17,pv89],
  .c 3, .c 5, .c 19, .c 3, .c 7, .c 13, .c 3, .c 11, .p pv3 [pv2,pv3,pv7,pv28099], .c 3,
]
private theorem h0144c01 : checkBlock 1179907 128 b0144c01 = true := by
  decide +kernel

private def b0144c02 : List Row := [
  .c 757, .c 5, .c 3, .c 157, .p pv3 [pv2,pv3,pv5,pv31,pv47], .c 3, .c 5, .c 59, .c 3, .c 79,
  .c 739, .c 3, .c 463, .c 37, .c 3, .c 7, .c 5, .c 3, .c 23, .c 11, .c 3, .c 5, .c 7, .c 3,
  .c 127, .c 29, .c 3, .c 47, .p pv2 [pv2,pv3,pv13,pv15131], .c 3, .c 11, .c 5, .c 3, .c 89,
  .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv59,pv1667], .c 3, .p pv3 [pv2,pv5,pv14753],
  .p pv3 [pv2,pv3,pv7,pv17,pv19,pv29], .c 3, .p pv5 [pv2,pv590123], .c 7, .c 3,
  .p pv2 [pv2,pv109,pv2707], .c 5, .c 3, .c 17, .c 19, .c 3, .c 5, .c 11, .c 3, .c 29, .c 1051,
  .c 3, .c 7, .p pv11 [pv2,pv3,pv11,pv1987], .c 3, .c 13, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5,
  .c 277, .c 3, .c 181, .p pv3 [pv2,pv3,pv196717], .c 3, .c 43, .c 13, .c 3,
  .p pv5 [pv2,pv7,pv3011], .c 5, .c 3, .c 7, .c 617, .c 3, .c 5, .c 17, .c 3, .c 809, .c 7, .c 3,
  .c 19, .c 67, .c 3, .c 83, .c 5, .c 3, .c 41, .p pv3 [pv2,pv3,pv5,pv43,pv61], .c 3, .c 5,
  .c 797, .c 3, .c 7, .c 53, .c 3, .c 151, .p pv19 [pv2,pv3,pv7,pv1171], .c 3,
  .p pv2 [pv2,pv269,pv1097], .c 5, .c 3, .c 173, .p pv7 [pv2,pv3,pv5,pv103,pv191], .c 3, .c 5,
  .c 13, .c 3, .p pv7 [pv2,pv5,pv41,pv2879], .c 43, .c 3, .p pv2 [pv2,pv7,pv42157], .c 11, .c 3,
  .c 7, .c 5, .c 3, .p pv3 [pv2,pv147551], .c 37, .c 3, .c 5, .c 7,
]
private theorem h0144c02 : checkBlock 1180163 128 b0144c02 = true := by
  decide +kernel

private def b0144c03 : List Row := [
  .c 3, .c 11, .p pv31 [pv2,pv3,pv65579], .c 3, .p pv2 [pv2,pv13,pv83,pv547], .c 17, .c 3, .c 619,
  .c 5, .c 3, .c 13, .c 131, .c 3, .c 5, .p pv3 [pv2,pv3,pv17,pv71,pv163], .c 3, .c 19, .c 251,
  .c 3, .c 587, .c 7, .c 3, .c 17, .c 5, .c 3, .c 53, .c 439, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv271], .c 3, .c 281, .c 73, .c 3, .c 7, .c 19, .c 3,
  .p pv2 [pv2,pv295123], .c 5, .c 3, .c 47, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv196751], .c 3,
  .c 31, .c 41, .c 3, .c 13, .p pv3 [pv2,pv3,pv151,pv1303], .c 3, .c 167, .c 5, .c 3, .c 7, .c 11,
  .c 3, .c 5, .p pv41 [pv2,pv3,pv7,pv7027], .c 3, .c 503, .c 7, .c 3,
  .p pv2 [pv2,pv19,pv47,pv661], .p pv7 [pv2,pv3,pv17,pv643], .c 3, .c 11, .c 5, .c 3, .c 37,
  .c 29, .c 3, .c 5, .c 23, .c 3, .c 7, .c 31, .c 3, .p pv3 [pv2,pv79,pv467], .c 109, .c 3,
  .c 983, .c 5, .c 3, .c 101, .p pv11 [pv2,pv3,pv5,pv23,pv29,pv59], .c 3, .c 5, .c 11, .c 3,
  .c 631, .c 19, .c 3, .c 67, .c 163, .c 3, .c 7, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 7,
  .c 3, .p pv7 [pv2,pv5,pv11,pv10733], .c 17, .c 3, .p pv2 [pv2,pv23,pv41,pv313], .c 367, .c 3,
  .p pv2 [pv2,pv590321], .c 5, .c 3, .c 59, .c 43, .c 3, .c 5, .p pv5 [pv2,pv3,pv911], .c 3,
  .p pv2 [pv2,pv5,pv13,pv19,pv239], .c 11, .c 3, .c 17, .c 7, .c 3, .c 13,
]
private theorem h0144c03 : checkBlock 1180419 128 b0144c03 = true := by
  decide +kernel

private def b0144c04 : List Row := [
  .c 5, .c 3, .c 19, .c 53, .c 3, .c 5, .c 47, .c 3, .p pv2 [pv2,pv5,pv7,pv101,pv167],
  .p pv2 [pv2,pv3,pv32797], .c 3, .c 7, .c 13, .c 3, .c 131, .c 5, .c 3, .p pv2 [pv2,pv59,pv5003],
  .c 7, .c 3, .c 5, .c 19, .c 3, .p pv3 [pv2,pv5,pv14759], .p pv2 [pv2,pv3,pv307,pv641], .c 3,
  .p pv5 [pv2,pv590363], .c 11, .c 3, .p pv2 [pv2,pv7,pv42169], .c 5, .c 3, .c 7, .c 67, .c 3,
  .c 5, .c 271, .c 3, .c 11, .c 7, .c 3, .p pv2 [pv2,pv211,pv1399], .c 31, .c 3, .c 89, .c 5,
  .c 3, .c 17, .p pv7 [pv2,pv3,pv5,pv39359], .c 3, .c 5, .c 13, .c 3, .c 7, .c 409, .c 3, .c 53,
  .c 383, .c 3, .c 19, .c 5, .c 3, .p pv7 [pv2,pv590399], .c 71, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv11,pv17891], .c 3, .p pv2 [pv2,pv5,pv118081], .c 79, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv37,pv197], .c 3, .c 7, .c 5, .c 3, .c 13, .c 19, .c 3, .c 5, .c 7, .c 3,
  .c 41, .c 23, .c 3, .p pv5 [pv2,pv127,pv4649], .p pv7 [pv2,pv3,pv73,pv337], .c 3,
  .p pv2 [pv2,pv31,pv89,pv107], .c 5, .c 3, .p pv2 [pv2,pv7,pv84347], .c 11, .c 3, .c 5, .c 311,
  .c 3, .c 17, .p pv5 [pv2,pv3,pv7,pv11,pv71], .c 3, .p pv2 [pv2,pv295219], .c 7, .c 3, .c 11,
  .c 5, .c 3, .c 23, .p pv2 [pv2,pv3,pv5,pv13121], .c 3, .c 5, .p pv5 [pv2,pv3,pv12301], .c 3,
  .p pv2 [pv2,pv5,pv7,pv241], .p pv3 [pv2,pv3,pv196817], .c 3, .c 7, .c 29, .c 3,
  .p pv3 [pv2,pv23,pv3209], .c 5, .c 3, .c 691, .c 7, .c 3, .c 5, .c 11, .c 3,
]
private theorem h0144c04 : checkBlock 1180675 128 b0144c04 = true := by
  decide +kernel

private def b0144c05 : List Row := [
  .p pv2 [pv2,pv5,pv118093], .c 13, .c 3, .p pv3 [pv2,pv147617], .c 17, .c 3, .c 71, .c 5, .c 3,
  .c 7, .p pv3 [pv2,pv3,pv5,pv7873], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv17,pv827], .c 3,
  .p pv7 [pv2,pv5,pv11,pv61], .c 7, .c 3, .c 29, .c 47, .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv590489], .c 23, .c 3, .c 5, .p pv3 [pv2,pv3,pv196831], .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv29,pv10181], .c 53, .c 3, .c 37, .c 5, .c 3, .c 67, .c 13, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv47,pv349], .c 3, .c 19, .p pv5 [pv2,pv3,pv196837], .c 3, .c 23, .c 307, .c 3,
  .c 7, .c 5, .c 3, .p pv13 [pv2,pv31,pv43,pv443], .c 17, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv13,pv23,pv79], .p pv2 [pv2,pv3,pv53,pv619], .c 3, .p pv3 [pv2,pv9227], .c 11,
  .c 3, .c 13, .c 5, .c 3, .c 31, .c 173, .c 3, .c 5, .c 37, .c 3, .c 11, .c 29, .c 3, .c 41,
  .c 7, .c 3, .p pv2 [pv2,pv11,pv17,pv1579], .c 5, .c 3, .p pv2 [pv2,pv163,pv3623], .c 103, .c 3,
  .c 5, .c 521, .c 3, .c 157, .c 463, .c 3, .c 7, .c 23, .c 3, .c 149, .c 5, .c 3, .c 79, .c 7,
  .c 3, .c 5, .p pv67 [pv2,pv3,pv11,pv2237], .c 3, .c 13, .c 17, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv98429], .c 3, .p pv3 [pv2,pv7,pv5273], .c 5, .c 3, .c 7, .c 419, .c 3, .c 5,
  .c 13, .c 3, .p pv2 [pv2,pv5,pv29,pv4073], .c 7, .c 3, .c 17, .c 269, .c 3,
  .p pv5 [pv2,pv229,pv2579], .c 5,
]
private theorem h0144c05 : checkBlock 1180931 128 b0144c05 = true := by
  decide +kernel

private def b0144c06 : List Row := [
  .c 3, .c 113, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv10937], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv11,pv1627], .c 3, .c 661, .p pv11 [pv2,pv3,pv7,pv79,pv89], .c 3, .c 11, .c 5,
  .c 3, .c 13, .c 179, .c 3, .c 5, .c 71, .c 3, .c 223, .c 109, .c 3, .p pv2 [pv2,pv7,pv42187],
  .c 59, .c 3, .c 7, .c 5, .c 3, .c 19, .c 41, .c 3, .c 5, .c 7, .c 3, .c 163,
  .p pv3 [pv2,pv3,pv17,pv37,pv313], .c 3, .p pv2 [pv2,pv97,pv6089],
  .p pv13 [pv2,pv3,pv11,pv19,pv157], .c 3, .c 151, .c 5, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv5,pv23,pv107], .c 3, .c 5, .c 19, .c 3, .c 373, .p pv2 [pv2,pv3,pv7,pv41],
  .c 3, .c 13, .c 7, .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv227,pv1301],
  .p pv41 [pv2,pv3,pv5,pv13,pv233], .c 3, .c 5, .c 31, .c 3, .p pv3 [pv2,pv5,pv7,pv4219], .c 11,
  .c 3, .c 7, .p pv11 [pv2,pv3,pv24611], .c 3, .c 41, .c 5, .c 3, .c 43, .c 7, .c 3, .c 5, .c 17,
  .c 3, .c 137, .c 193, .c 3, .c 59, .c 73, .c 3, .c 19, .c 5, .c 3, .c 7, .c 431, .c 3, .c 5,
  .c 239, .c 3, .c 17, .c 7, .c 3, .c 61, .c 11, .c 3, .c 389, .c 5, .c 3, .c 571, .c 13, .c 3,
  .c 5, .p pv13 [pv2,pv3,pv196901], .c 3, .c 7, .p pv5 [pv2,pv3,pv10939], .c 3, .c 173, .c 821,
  .c 3, .c 53, .c 5, .c 3, .c 257, .c 29, .c 3, .c 5, .p pv2 [pv2,pv3,pv98453], .c 3, .c 23,
]
private theorem h0144c06 : checkBlock 1181187 128 b0144c06 = true := by
  decide +kernel

private def b0144c07 : List Row := [
  .p pv2 [pv2,pv3,pv196907], .c 3, .c 37, .c 17, .c 3, .c 7, .c 5, .c 3, .c 317,
  .p pv11 [pv2,pv3,pv5,pv7,pv29,pv97], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv118147],
  .p pv5 [pv2,pv3,pv31,pv397], .c 3, .c 11, .c 13, .c 3, .c 17, .c 5, .c 3, .c 29, .c 353, .c 3,
  .c 5, .c 41, .c 3, .p pv2 [pv2,pv5,pv17,pv139], .c 31, .c 3, .p pv2 [pv2,pv590753], .c 7, .c 3,
  .c 103, .c 5, .c 3, .p pv19 [pv2,pv13,pv29,pv1567], .c 11, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv191,pv1031], .c 3, .c 13, .c 23, .c 3, .c 7, .c 1009, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv295387], .c 7, .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv109,pv271],
  .p pv2 [pv2,pv3,pv196927], .c 3, .c 911, .c 1087, .c 3, .p pv2 [pv2,pv7,pv19,pv2221], .c 5,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv47,pv419], .c 3, .c 5, .c 11, .c 3, .c 19, .c 7, .c 3, .c 43,
  .c 101, .c 3, .c 79, .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv19,pv691], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv103,pv239], .c 3, .c 7, .c 241, .c 3, .c 31, .c 19, .c 3,
  .p pv3 [pv2,pv37,pv499], .c 5, .c 3, .c 139, .c 113, .c 3, .c 5, .p pv3 [pv2,pv3,pv65647], .c 3,
  .c 73, .c 11, .c 3, .c 433, .c 263, .c 3, .c 7, .c 5, .c 3, .c 37, .c 23, .c 3, .c 5, .c 7,
  .c 3, .p pv3 [pv2,pv5,pv14771], .c 43, .c 3, .c 13, .c 31, .c 3, .c 479, .c 5, .c 3,
]
private theorem h0144c07 : checkBlock 1181443 128 b0144c07 = true := by
  decide +kernel

private def b0144c08 : List Row := [
  .p pv2 [pv2,pv7,pv84407], .p pv2 [pv2,pv3,pv5,pv13,pv101], .c 3, .c 5, .c 971, .c 3, .c 59,
  .c 13, .c 3, .c 23, .c 7, .c 3, .p pv2 [pv2,pv379,pv1559], .c 5, .c 3, .p pv3 [pv2,pv36929],
  .p pv11 [pv2,pv3,pv5,pv11,pv3581], .c 3, .c 5, .c 563, .c 3, .c 11, .c 19, .c 3, .c 7, .c 181,
  .c 3, .c 61, .c 5, .c 3, .p pv13 [pv2,pv179,pv3301], .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv196961], .c 3, .p pv13 [pv2,pv5,pv59,pv2003], .p pv5 [pv2,pv3,pv17,pv1931],
  .c 3, .p pv3 [pv2,pv233,pv317], .c 29, .c 3, .c 827, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 73,
  .c 3, .c 101, .c 7, .c 3, .c 11, .c 23, .c 3, .c 31, .c 5, .c 3, .c 19, .c 907, .c 3, .c 5,
  .c 599, .c 3, .c 7, .c 761, .c 3, .c 29, .p pv37 [pv2,pv3,pv7,pv19,pv1481], .c 3, .c 13, .c 5,
  .c 3, .c 593, .c 11, .c 3, .c 5, .c 17, .c 3, .c 199, .c 631, .c 3, .c 113, .c 13, .c 3, .c 7,
  .c 5, .c 3, .p pv17 [pv2,pv23,pv25693], .p pv29 [pv2,pv3,pv5,pv7,pv67], .c 3, .c 5, .c 7, .c 3,
  .c 17, .p pv2 [pv2,pv3,pv98491], .c 3, .p pv3 [pv2,pv157,pv941], .c 137, .c 3, .c 709, .c 5,
  .c 3, .c 47, .p pv17 [pv2,pv3,pv5,pv39397], .c 3, .c 5, .c 11, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv7,pv107,pv263], .c 3, .p pv5 [pv2,pv590963], .c 7, .c 3, .c 19, .c 5, .c 3,
  .c 11, .c 43, .c 3, .c 5, .c 13, .c 3, .c 797, .c 29,
]
private theorem h0144c08 : checkBlock 1181699 128 b0144c08 = true := by
  decide +kernel

private def b0144c09 : List Row := [
  .c 3, .c 7, .c 17, .c 3, .p pv2 [pv2,pv293,pv2017], .c 5, .c 3, .p pv3 [pv2,pv31,pv2383], .c 7,
  .c 3, .c 5, .c 467, .c 3, .p pv2 [pv2,pv5,pv113,pv523], .c 11, .c 3, .p pv2 [pv2,pv13,pv269],
  .c 41, .c 3, .c 17, .c 5, .c 3, .c 7, .c 331, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv53,pv59], .c 3,
  .c 29, .c 7, .c 3, .c 149, .p pv3 [pv2,pv3,pv197003], .c 3, .p pv5 [pv2,pv211,pv2801], .c 5,
  .c 3, .c 107, .p pv11 [pv2,pv3,pv5,pv31,pv41], .c 3, .c 5, .c 373, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv97,pv677], .c 3, .c 19, .c 11, .c 3, .c 157, .c 5, .c 3, .c 53, .c 17, .c 3,
  .c 5, .c 547, .c 3, .c 11, .p pv23 [pv2,pv3,pv49253], .c 3, .c 13, .c 71, .c 3, .c 7, .c 5,
  .c 3, .c 73, .c 283, .c 3, .c 5, .c 7, .c 3, .c 379, .c 13, .c 3, .c 367, .c 173, .c 3, .c 37,
  .c 5, .c 3, .c 61, .p pv7 [pv2,pv3,pv5,pv9851], .c 3, .c 5, .c 29, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv7,pv4691], .c 3, .c 11, .c 7, .c 3, .p pv5 [pv2,pv13,pv19,pv2393], .c 5, .c 3,
  .c 521, .c 839, .c 3, .c 5, .p pv2 [pv2,pv3,pv29,pv43,pv79], .c 3, .c 19, .c 17, .c 3, .c 7,
  .c 83, .c 3, .c 137, .c 5, .c 3, .c 151, .c 7, .c 3, .c 5, .c 37, .c 3, .c 47, .c 167, .c 3,
  .c 17, .c 19, .c 3, .c 11, .c 5, .c 3, .c 7,
]
private theorem h0144c09 : checkBlock 1181955 128 b0144c09 = true := by
  decide +kernel

private def b0144c10 : List Row := [
  .p pv2 [pv2,pv3,pv5,pv157,pv251], .c 3, .c 5, .c 449, .c 3, .c 71, .c 7, .c 3, .c 439, .c 347,
  .c 3, .c 13, .c 5, .c 3, .c 163, .c 61, .c 3, .c 5, .c 11, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv83,pv1187], .c 3, .c 307, .c 13, .c 3, .c 991, .c 5, .c 3, .c 11, .c 53, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv41,pv89], .c 3, .p pv3 [pv2,pv5,pv11,pv2687],
  .p pv7 [pv2,pv3,pv17,pv67,pv173], .c 3, .p pv5 [pv2,pv7,pv84449], .p pv19 [pv2,pv3,pv24631],
  .c 3, .c 7, .c 5, .c 3, .c 17, .c 29, .c 3, .c 5, .c 7, .c 3, .c 13, .c 11, .c 3, .c 41, .c 113,
  .c 3, .c 109, .c 5, .c 3, .c 733, .p pv3 [pv2,pv3,pv5,pv29,pv151], .c 3, .c 5, .c 13, .c 3,
  .p pv2 [pv2,pv5,pv31,pv1907], .p pv3 [pv2,pv3,pv7,pv28151], .c 3, .p pv2 [pv2,pv11,pv223,pv241],
  .c 7, .c 3, .p pv3 [pv2,pv73897], .c 5, .c 3, .c 29, .c 23, .c 3, .c 5, .c 17, .c 3, .c 31,
  .c 271, .c 3, .c 7, .c 11, .c 3, .p pv5 [pv2,pv569,pv1039], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv98533], .c 3, .c 11, .p pv2 [pv2,pv3,pv13,pv31,pv163], .c 3, .c 23, .c 37,
  .c 3, .p pv2 [pv2,pv7,pv11,pv349], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv6569], .c 3, .c 5,
  .c 19, .c 3, .p pv19 [pv2,pv5,pv23,pv53,pv97], .c 7, .c 3, .p pv2 [pv2,pv487,pv607],
  .p pv3 [pv2,pv3,pv811], .c 3, .c 227, .c 5, .c 3, .p pv3 [pv2,pv263,pv281],
  .p pv3 [pv2,pv3,pv5,pv7883], .c 3, .c 5, .c 43, .c 3, .c 7, .p pv3 [pv2,pv3,pv197077], .c 3,
]
private theorem h0144c10 : checkBlock 1182211 128 b0144c10 = true := by
  decide +kernel

private def b0144c11 : List Row := [
  .c 11, .c 17, .c 3, .c 47, .c 5, .c 3, .p pv7 [pv2,pv11,pv59,pv911], .c 41, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv17,pv11593], .c 3, .p pv17 [pv2,pv5,pv118249], .c 13, .c 3, .c 127, .c 23,
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv101,pv2927], .c 11, .c 3, .c 5, .c 7, .c 3,
  .p pv13 [pv2,pv5,pv17,pv37,pv47], .c 433, .c 3, .c 73, .c 661, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv84467], .c 19, .c 3, .c 5, .p pv3 [pv2,pv3,pv61,pv359], .c 3, .c 79, .c 503,
  .c 3, .c 31, .c 7, .c 3, .c 41, .c 5, .c 3, .c 223, .c 13, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv7,pv8447], .c 653, .c 3, .c 7, .c 53, .c 3, .p pv3 [pv2,pv9239], .c 5, .c 3,
  .c 11, .c 7, .c 3, .c 5, .c 61, .c 3, .p pv2 [pv2,pv5,pv11,pv13,pv827], .c 149, .c 3, .c 19,
  .c 31, .c 3, .c 13, .c 5, .c 3, .c 7, .c 37, .c 3, .c 5, .c 23, .c 3, .c 967, .c 7, .c 3, .c 71,
  .c 13, .c 3, .c 179, .c 5, .c 3, .p pv2 [pv2,pv113,pv5233], .c 47, .c 3, .c 5, .c 83, .c 3,
  .c 7, .c 17, .c 3, .p pv2 [pv2,pv11,pv26879], .p pv3 [pv2,pv3,pv7,pv29,pv971], .c 3, .c 23,
  .c 5, .c 3, .p pv3 [pv2,pv13,pv2843], .p pv2 [pv2,pv3,pv5,pv17,pv773], .c 3, .c 5,
  .p pv7 [pv2,pv3,pv49279], .c 3, .c 13, .p pv3 [pv2,pv3,pv197117], .c 3, .c 17, .c 11, .c 3,
  .c 7, .c 5, .c 3, .c 677, .c 89,
]
private theorem h0144c11 : checkBlock 1182467 128 b0144c11 = true := by
  decide +kernel

private def b0144c12 : List Row := [
  .c 3, .c 5, .c 7, .c 3, .c 11, .c 311, .c 3, .p pv3 [pv2,pv29,pv2549],
  .p pv2 [pv2,pv3,pv197123], .c 3, .c 31, .c 5, .c 3, .c 103, .c 67, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv98563], .c 3, .c 349, .p pv2 [pv2,pv3,pv7,pv149], .c 3,
  .p pv5 [pv2,pv13,pv45491], .c 7, .c 3, .c 59, .c 5, .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv6571],
  .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv17921], .c 3, .p pv11 [pv2,pv5,pv7,pv61,pv277], .c 269, .c 3,
  .c 7, .c 131, .c 3, .c 947, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv37], .c 3,
  .c 23, .c 29, .c 3, .c 313, .c 727, .c 3, .c 83, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv28163], .c 3, .c 61, .c 7, .c 3, .c 13, .c 379, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv109,pv2713], .c 307, .c 3, .c 5, .c 17, .c 3, .c 7, .c 13, .c 3, .c 43,
  .p pv23 [pv2,pv3,pv7,pv2347], .c 3, .p pv2 [pv2,pv73,pv4051], .c 5, .c 3, .c 89,
  .p pv2 [pv2,pv3,pv5,pv3943], .c 3, .c 5, .c 11, .c 3, .c 17, .c 23, .c 3,
  .p pv2 [pv2,pv7,pv83,pv509], .p pv3 [pv2,pv3,pv11,pv17923], .c 3, .c 7, .c 5, .c 3, .c 11,
  .c 71, .c 3, .c 5, .c 7, .c 3, .c 233, .c 47, .c 3, .p pv2 [pv2,pv79,pv7487], .c 389, .c 3,
  .p pv3 [pv2,pv67,pv2207], .c 5, .c 3, .c 19, .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv197161], .c 3,
  .c 257, .c 11, .c 3, .c 109,
]
private theorem h0144c12 : checkBlock 1182723 128 b0144c12 = true := by
  decide +kernel

private def b0144c13 : List Row := [
  .c 7, .c 3, .c 829, .c 5, .c 3, .p pv2 [pv2,pv89,pv3323], .c 31, .c 3, .c 5, .c 19, .c 3, .c 37,
  .p pv2 [pv2,pv3,pv71,pv2777], .c 3, .c 7, .c 59, .c 3, .c 13, .c 5, .c 3, .c 67, .c 7, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv13,pv29,pv523], .c 3, .p pv11 [pv2,pv5,pv17,pv6959],
  .p pv5 [pv2,pv3,pv5477], .c 3, .c 47, .c 11, .c 3, .c 607, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv503], .c 3, .c 11, .c 7, .c 3, .c 277, .c 241, .c 3, .c 19, .c 5, .c 3,
  .p pv7 [pv2,pv13,pv45503], .c 17, .c 3, .c 5, .c 383, .c 3, .c 7, .p pv5 [pv2,pv3,pv19,pv5189],
  .c 3, .c 23, .c 107, .c 3, .p pv5 [pv2,pv43,pv13757], .c 5, .c 3, .c 97, .c 19, .c 3, .c 5,
  .c 13, .c 3, .p pv3 [pv2,pv5,pv23,pv643], .p pv3 [pv2,pv3,pv65729], .c 3, .c 11, .c 499, .c 3,
  .c 7, .c 5, .c 3, .c 739, .p pv2 [pv2,pv3,pv5,pv7,pv313], .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv23663], .c 67, .c 3, .p pv2 [pv2,pv13,pv61,pv373], .p pv3 [pv2,pv3,pv65731],
  .c 3, .p pv2 [pv2,pv591581], .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 31, .c 3,
  .p pv2 [pv2,pv5,pv59159], .c 17, .c 3, .c 19, .c 7, .c 3, .c 11, .c 5, .c 3,
  .p pv37 [pv2,pv591599], .p pv11 [pv2,pv3,pv5,pv17,pv29], .c 3, .c 5, .c 337, .c 3,
  .p pv2 [pv2,pv5,pv7,pv16903], .p pv2 [pv2,pv3,pv23,pv1429], .c 3, .c 7, .c 41, .c 3, .c 37,
  .c 5, .c 3, .c 29, .c 7, .c 3,
]
private theorem h0144c13 : checkBlock 1182979 128 b0144c13 = true := by
  decide +kernel

private def b0144c14 : List Row := [
  .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv29581], .c 229, .c 3, .c 13, .c 811, .c 3, .c 443, .c 5,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv13,pv37,pv41], .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv9391], .c 3,
  .p pv11 [pv2,pv5,pv11,pv31,pv347], .c 7, .c 3, .p pv2 [pv2,pv295819],
  .p pv3 [pv2,pv3,pv53,pv61], .c 3, .c 193, .c 5, .c 3, .c 239, .c 281, .c 3, .c 5, .c 37, .c 3,
  .c 7, .c 11, .c 3, .c 139, .c 157, .c 3, .c 107, .c 5, .c 3, .c 17, .c 709, .c 3, .c 5, .c 23,
  .c 3, .c 53, .p pv5 [pv2,pv3,pv31,pv3181], .c 3, .p pv5 [pv2,pv7,pv11,pv17,pv113], .c 19, .c 3,
  .c 7, .c 5, .c 3, .p pv2 [pv2,pv295837], .c 13, .c 3, .c 5, .c 7, .c 3, .c 317, .c 31, .c 3,
  .c 103, .c 11, .c 3, .c 23, .c 5, .c 3, .c 197, .p pv7 [pv2,pv3,pv5,pv11,pv163], .c 3, .c 5,
  .c 17, .c 3, .c 11, .p pv5 [pv2,pv3,pv7,pv587], .c 3, .p pv2 [pv2,pv19,pv23,pv677], .c 7, .c 3,
  .c 13, .c 5, .c 3, .p pv3 [pv2,pv37,pv1999], .p pv2 [pv2,pv3,pv5,pv487], .c 3, .c 5, .c 101,
  .c 3, .c 17, .p pv3 [pv2,pv3,pv59,pv3343], .c 3, .c 7, .c 13, .c 3, .c 89, .c 5, .c 3, .c 997,
  .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv43,pv139], .c 3, .p pv2 [pv2,pv5,pv23669], .c 19, .c 3,
  .c 11, .c 349, .c 3, .c 773, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv103,pv383], .c 3, .c 5,
  .p pv17 [pv2,pv3,pv7,pv73,pv193], .c 3, .c 13, .c 7, .c 3, .c 31, .c 17,
]
private theorem h0144c14 : checkBlock 1183235 128 b0144c14 = true := by
  decide +kernel

private def b0144c15 : List Row := [
  .c 3, .c 173, .c 5, .c 3, .c 71, .c 11, .c 3, .c 5, .c 13, .c 3, .c 7, .c 127, .c 3, .c 857,
  .c 29, .c 3, .c 11, .c 5, .c 3, .c 19, .p pv2 [pv2,pv3,pv5,pv39451], .c 3, .c 5,
  .p pv7 [pv2,pv3,pv8219], .c 3, .p pv2 [pv2,pv5,pv17,pv59], .c 53, .c 3, .c 41, .c 31, .c 3,
  .c 7, .c 5, .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv7,pv1409], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv71,pv1667], .c 103, .c 3, .c 29, .p pv2 [pv2,pv3,pv11,pv79,pv227], .c 3,
  .c 61, .c 5, .c 3, .c 11, .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv53,pv1861], .c 3, .c 47, .c 23,
  .c 3, .p pv5 [pv2,pv29,pv20407], .c 7, .c 3, .p pv2 [pv2,pv295903], .c 5, .c 3, .c 101, .c 277,
  .c 3, .c 5, .c 191, .c 3, .c 109, .c 11, .c 3, .c 7, .c 683, .c 3, .c 19, .c 5, .c 3, .c 23,
  .c 7, .c 3, .c 5, .c 79, .c 3, .c 43, .c 13, .c 3, .c 37, .c 193, .c 3, .c 31, .c 5, .c 3, .c 7,
  .c 19, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv28183], .c 3, .c 97, .c 7, .c 3,
  .p pv3 [pv2,pv167,pv443], .c 11, .c 3, .c 613, .c 5, .c 3, .p pv2 [pv2,pv541,pv547], .c 41,
  .c 3, .c 5, .c 59, .c 3, .c 7, .p pv3 [pv2,pv3,pv29,pv6803], .c 3, .c 17,
  .p pv19 [pv2,pv3,pv7,pv13,pv271], .c 3, .p pv2 [pv2,pv11,pv26903], .c 5, .c 3,
  .p pv2 [pv2,pv19,pv31151], .c 13, .c 3, .c 5,
]
private theorem h0144c15 : checkBlock 1183491 128 b0144c15 = true := by
  decide +kernel

private def b0144c16 : List Row := [
  .c 43, .c 3, .c 29, .p pv19 [pv2,pv3,pv41,pv401], .c 3, .c 19, .p pv3 [pv2,pv3,pv197293], .c 3,
  .c 7, .c 5, .c 3, .p pv7 [pv2,pv73,pv2027], .p pv3 [pv2,pv3,pv5,pv7,pv1879], .c 3, .c 5, .c 7,
  .c 3, .p pv2 [pv2,pv5,pv13,pv29,pv157], .c 71, .c 3, .c 11, .c 47, .c 3, .c 13, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv11,pv7687], .c 491, .c 3, .c 5, .c 673, .c 3, .p pv2 [pv2,pv5,pv23,pv5147],
  .p pv13 [pv2,pv3,pv7,pv17,pv829], .c 3, .c 137, .c 7, .c 3, .c 67, .c 5, .c 3, .c 17, .c 11,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv47,pv2099], .c 3, .c 73, .p pv2 [pv2,pv3,pv11,pv1993], .c 3, .c 7,
  .c 109, .c 3, .c 11, .c 5, .c 3, .c 31, .c 7, .c 3, .c 5, .c 29, .c 3, .c 13, .c 233, .c 3,
  .p pv2 [pv2,pv43,pv6883], .c 23, .c 3, .c 47, .c 5, .c 3, .c 7, .c 463, .c 3, .c 5, .c 11, .c 3,
  .c 113, .c 7, .c 3, .c 223, .c 19, .c 3, .p pv3 [pv2,pv83,pv1783], .c 5, .c 3, .c 11, .c 31,
  .c 3, .c 5, .c 641, .c 3, .c 7, .p pv2 [pv2,pv3,pv32887], .c 3, .c 157,
  .p pv7 [pv2,pv3,pv7,pv4027], .c 3, .p pv5 [pv2,pv367,pv1613], .c 5, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv5,pv877], .c 3, .c 5, .c 41, .c 3, .p pv3 [pv2,pv5,pv29599], .c 11, .c 3,
  .c 53, .p pv7 [pv2,pv3,pv4111], .c 3, .c 7, .c 5, .c 3, .c 587, .p pv2 [pv2,pv3,pv5,pv7,pv2819],
  .c 3, .c 5, .c 7, .c 3, .c 151, .p pv13 [pv2,pv3,pv49333], .c 3, .p pv2 [pv2,pv11,pv71,pv379],
  .c 17, .c 3,
]
private theorem h0144c16 : checkBlock 1183747 128 b0144c16 = true := by
  decide +kernel

private def b0144c17 : List Row := [
  .p pv2 [pv2,pv139,pv4259], .c 5, .c 3, .c 191, .p pv43 [pv2,pv3,pv5,pv61,pv647], .c 3, .c 5,
  .c 23, .c 3, .c 127, .c 19, .c 3, .c 13, .c 7, .c 3, .c 17, .c 5, .c 3, .c 41, .c 29, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv197341], .c 3, .c 11, .c 13, .c 3, .c 7, .p pv2 [pv2,pv3,pv7309], .c 3,
  .c 23, .c 5, .c 3, .p pv2 [pv2,pv296017], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv31,pv1061], .c 3,
  .p pv3 [pv2,pv5,pv19,pv41], .p pv2 [pv2,pv3,pv197347], .c 3, .c 457, .c 569, .c 3,
  .p pv2 [pv2,pv7,pv13,pv3253], .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 31, .c 3, .c 37, .c 7,
  .c 3, .c 11, .p pv3 [pv2,pv3,pv13,pv17,pv19,pv47], .c 3, .p pv2 [pv2,pv592061], .c 5, .c 3,
  .p pv3 [pv2,pv11,pv29], .c 13, .c 3, .c 5, .c 19, .c 3, .c 7, .p pv3 [pv2,pv3,pv151,pv1307],
  .c 3, .c 619, .p pv23 [pv2,pv3,pv7,pv37,pv127], .c 3, .c 401, .c 5, .c 3, .c 229, .c 11, .c 3,
  .c 5, .c 197, .c 3, .p pv2 [pv2,pv5,pv13,pv9109], .p pv2 [pv2,pv3,pv11,pv8971], .c 3, .c 43,
  .c 53, .c 3, .c 7, .c 5, .c 3, .c 59, .c 103, .c 3, .c 5, .c 7, .c 3, .c 23, .c 17, .c 3,
  .p pv5 [pv2,pv73,pv8111], .c 13, .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv7,pv251,pv337], .c 593,
  .c 3, .c 5, .c 11, .c 3, .c 31, .c 521, .c 3, .c 17, .c 7, .c 3, .p pv2 [pv2,pv592121], .c 5,
  .c 3, .c 11, .c 19, .c 3, .c 5, .c 607,
]
private theorem h0144c17 : checkBlock 1184003 128 b0144c17 = true := by
  decide +kernel

private def b0144c18 : List Row := [
  .c 3, .c 13, .c 43, .c 3, .c 7, .p pv13 [pv2,pv3,pv98689], .c 3, .c 29, .c 5, .c 3, .c 73, .c 7,
  .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv118429], .c 11, .c 3, .c 823,
  .p pv7 [pv2,pv3,pv197383], .c 3, .p pv31 [pv2,pv7,pv29,pv2917], .c 5, .c 3, .c 7, .c 347, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv7,pv23,pv613], .c 3, .c 1049, .c 7, .c 3, .c 19,
  .p pv7 [pv2,pv3,pv5483], .c 3, .c 37, .c 5, .c 3, .c 13, .c 359, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv19,pv3463], .c 3, .c 7, .c 47, .c 3, .p pv2 [pv2,pv17,pv17417], .c 11, .c 3,
  .p pv2 [pv2,pv23,pv25747], .c 5, .c 3, .p pv3 [pv2,pv79,pv937], .c 131, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv61,pv809], .c 3, .c 11, .c 107, .c 3, .c 631, .c 29, .c 3, .c 7, .c 5, .c 3,
  .p pv13 [pv2,pv592199], .c 149, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv83,pv1427],
  .p pv2 [pv2,pv3,pv89,pv1109], .c 3, .c 13, .c 139, .c 3, .p pv5 [pv2,pv19,pv71,pv439], .c 5,
  .c 3, .p pv17 [pv2,pv7,pv6043], .c 23, .c 3, .c 5, .c 61, .c 3, .c 17, .c 13, .c 3, .c 11, .c 7,
  .c 3, .p pv2 [pv2,pv277,pv1069], .c 5, .c 3, .p pv2 [pv2,pv11,pv17,pv3167],
  .p pv7 [pv2,pv3,pv5,pv19,pv1039], .c 3, .c 5, .c 97, .c 3, .p pv7 [pv2,pv5,pv7,pv16921],
  .p pv7 [pv2,pv3,pv16451], .c 3, .c 7, .c 19, .c 3, .p pv2 [pv2,pv13,pv45557], .c 5, .c 3,
  .p pv3 [pv2,pv148061], .c 7, .c 3, .c 5, .c 53, .c 3, .c 89, .c 109, .c 3,
  .p pv2 [pv2,pv349,pv1697], .c 17, .c 3, .c 11,
]
private theorem h0144c18 : checkBlock 1184259 128 b0144c18 = true := by
  decide +kernel

private def b0144c19 : List Row := [
  .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .p pv7 [pv2,pv3,pv7,pv17,pv79], .c 3, .c 41, .c 7, .c 3,
  .p pv3 [pv2,pv19,pv7793], .p pv2 [pv2,pv3,pv197423], .c 3, .c 17, .c 5, .c 3,
  .p pv2 [pv2,pv296137], .p pv7 [pv2,pv3,pv5,pv53,pv149], .c 3, .c 5, .c 11, .c 3, .c 7, .c 29,
  .c 3, .c 479, .c 23, .c 3, .c 13, .c 5, .c 3, .c 11, .c 577, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv13,pv15187], .c 3, .c 919, .c 19, .c 3, .c 107, .c 13, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv37019], .c 17, .c 3, .c 5, .c 7, .c 3, .c 29, .c 11, .c 3, .c 67, .c 37, .c 3,
  .c 131, .c 5, .c 3, .c 137, .c 829, .c 3, .c 5, .c 199, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv7,pv1567], .c 3, .c 647, .c 7, .c 3, .p pv5 [pv2,pv17,pv34843], .c 5, .c 3,
  .c 19, .p pv29 [pv2,pv3,pv5,pv13163], .c 3, .c 5, .c 13, .c 3, .c 61,
  .p pv3 [pv2,pv3,pv47,pv4201], .c 3, .c 7, .c 11, .c 3, .c 43, .c 5, .c 3, .c 149, .c 7, .c 3,
  .c 5, .c 19, .c 3, .c 11, .c 17, .c 3, .c 73, .c 941, .c 3, .c 239, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv17,pv23,pv101], .c 3, .c 5, .c 29, .c 3, .p pv3 [pv2,pv5,pv37,pv1601],
  .c 7, .c 3, .c 17, .p pv13 [pv2,pv3,pv98729], .c 3, .c 23, .c 5, .c 3,
  .p pv7 [pv2,pv31,pv97,pv197], .c 67, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv29,pv619], .c 3,
]
private theorem h0144c19 : checkBlock 1184515 128 b0144c19 = true := by
  decide +kernel

private def b0144c20 : List Row := [
  .c 7, .c 191, .c 3, .c 11, .c 43, .c 3, .c 19, .c 5, .c 3, .c 31,
  .p pv3 [pv2,pv3,pv5,pv73,pv541], .c 3, .c 5, .p pv2 [pv2,pv3,pv32911], .c 3, .c 179, .c 61,
  .c 3, .c 13, .c 103, .c 3, .c 7, .c 5, .c 3, .c 431, .c 11, .c 3, .c 5, .c 7, .c 3, .c 101,
  .c 13, .c 3, .p pv2 [pv2,pv139,pv2131], .p pv3 [pv2,pv3,pv59,pv3347], .c 3, .c 11, .c 5, .c 3,
  .c 17, .c 31, .c 3, .c 5, .c 89, .c 3, .c 439, .c 73, .c 3, .p pv2 [pv2,pv17,pv34849], .c 7,
  .c 3, .c 409, .c 5, .c 3, .c 157, .p pv19 [pv2,pv3,pv5,pv4937], .c 3, .c 5, .c 11, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv293,pv337], .c 3, .c 7, .c 863, .c 3, .p pv5 [pv2,pv592451], .c 5, .c 3,
  .c 11, .c 7, .c 3, .c 5, .c 17, .c 3, .c 53, .p pv2 [pv2,pv3,pv21943], .c 3,
  .p pv5 [pv2,pv592463], .c 613, .c 3, .p pv2 [pv2,pv7,pv101,pv419], .c 5, .c 3, .c 7, .c 41,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv89,pv317], .c 3, .c 17, .c 7, .c 3, .p pv2 [pv2,pv59,pv5021],
  .p pv3 [pv2,pv3,pv65831], .c 3, .c 13, .c 5, .c 3, .c 29, .c 251, .c 3, .c 5, .c 281, .c 3,
  .c 7, .c 23, .c 3, .p pv2 [pv2,pv11,pv61,pv883], .c 13, .c 3, .p pv5 [pv2,pv19,pv1949], .c 5,
  .c 3, .c 37, .c 457, .c 3, .c 5, .c 181, .c 3, .c 19, .p pv2 [pv2,pv3,pv32917], .c 3,
  .p pv3 [pv2,pv7,pv3023], .c 11, .c 3, .c 7, .c 5,
]
private theorem h0144c20 : checkBlock 1184771 128 b0144c20 = true := by
  decide +kernel

private def b0144c21 : List Row := [
  .c 3, .c 23, .c 113, .c 3, .c 5, .c 7, .c 3, .c 11, .c 367, .c 3, .c 61, .c 19, .c 3, .c 17,
  .c 5, .c 3, .c 359, .c 71, .c 3, .c 5, .c 13, .c 3, .p pv29 [pv2,pv5,pv17,pv6971], .c 37, .c 3,
  .p pv2 [pv2,pv296269], .c 7, .c 3, .c 271, .c 5, .c 3, .p pv3 [pv2,pv18517], .c 827, .c 3, .c 5,
  .c 1019, .c 3, .c 977, .p pv29 [pv2,pv3,pv65839], .c 3, .c 7, .p pv2 [pv2,pv3,pv61,pv1619],
  .c 3, .p pv3 [pv2,pv148139], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv197521],
  .c 3, .p pv17 [pv2,pv5,pv31,pv3823], .c 53, .c 3, .c 1061, .c 797, .c 3, .c 29, .c 5, .c 3,
  .c 7, .c 11, .c 3, .c 5, .c 83, .c 3, .c 31, .c 7, .c 3, .c 23, .c 61, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv592589], .p pv2 [pv2,pv3,pv5,pv19753], .c 3, .c 5, .c 41, .c 3, .c 7, .c 157,
  .c 3, .c 13, .c 47, .c 3, .c 71, .c 5, .c 3, .c 43, .c 911, .c 3, .c 5, .c 11, .c 3, .c 37,
  .c 13, .c 3, .c 569, .c 337, .c 3, .c 7, .c 5, .c 3, .c 11, .p pv11 [pv2,pv3,pv5,pv7,pv17,pv83],
  .c 3, .c 5, .c 7, .c 3, .c 59, .c 139, .c 3, .c 17, .c 23, .c 3, .c 317, .c 5, .c 3, .c 41,
  .c 233, .c 3, .c 5, .c 19, .c 3, .p pv3 [pv2,pv5,pv463],
]
private theorem h0144c21 : checkBlock 1185027 128 b0144c21 = true := by
  decide +kernel

private def b0144c22 : List Row := [
  .c 11, .c 3, .p pv5 [pv2,pv592643], .c 7, .c 3, .c 47, .c 5, .c 3, .p pv2 [pv2,pv592649], .c 13,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv197551], .c 3, .c 331, .p pv5 [pv2,pv3,pv12347], .c 3, .c 7,
  .p pv3 [pv2,pv3,pv65851], .c 3, .c 83, .c 5, .c 3, .p pv3 [pv2,pv23,pv3221], .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv101,pv163], .c 3, .c 263, .p pv11 [pv2,pv3,pv17,pv11621], .c 3, .c 31, .c 11,
  .c 3, .c 13, .c 5, .c 3, .c 7, .p pv19 [pv2,pv3,pv5,pv11,pv449], .c 3, .c 5,
  .p pv29 [pv2,pv3,pv7,pv13,pv167], .c 3, .c 11, .c 7, .c 3, .p pv5 [pv2,pv17,pv2179], .c 13,
  .c 3, .p pv5 [pv2,pv11,pv53881], .c 5, .c 3, .p pv2 [pv2,pv296347], .c 19, .c 3, .c 5, .c 23,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv197567], .c 3, .c 593, .c 31, .c 3, .c 61, .c 5, .c 3, .c 131,
  .c 599, .c 3, .c 5, .c 17, .c 3, .c 13, .c 29, .c 3, .c 11, .p pv3 [pv2,pv3,pv197573], .c 3,
  .c 7, .c 5, .c 3, .c 907, .c 53, .c 3, .c 5, .c 7, .c 3, .c 17, .p pv3 [pv2,pv3,pv29,pv757],
  .c 3, .c 19, .p pv2 [pv2,pv3,pv223,pv443], .c 3, .c 251, .c 5, .c 3, .c 241, .c 11, .c 3, .c 5,
  .c 59, .c 3, .c 29, .p pv5 [pv2,pv3,pv7,pv11,pv1283], .c 3, .p pv3 [pv2,pv13,pv11399], .c 7,
  .c 3, .c 11, .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv43,pv919], .c 3, .c 5, .c 37, .c 3,
  .c 1069, .p pv2 [pv2,pv3,pv13,pv15199], .c 3, .c 7, .c 17, .c 3, .c 31, .c 5, .c 3,
]
private theorem h0144c22 : checkBlock 1185283 128 b0144c22 = true := by
  decide +kernel

private def b0144c23 : List Row := [
  .c 281, .c 7, .c 3, .c 5, .c 11, .c 3, .p pv11 [pv2,pv5,pv131,pv181], .c 43, .c 3, .c 53,
  .p pv19 [pv2,pv3,pv11,pv23,pv71], .c 3, .c 17, .c 5, .c 3, .c 7, .c 503, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv7057], .c 3, .c 19, .c 7, .c 3, .c 13, .p pv2 [pv2,pv3,pv32933], .c 3,
  .c 73, .c 5, .c 3, .c 193, .p pv31 [pv2,pv3,pv5,pv13,pv19], .c 3, .c 5, .c 29, .c 3, .c 7,
  .c 11, .c 3, .p pv3 [pv2,pv74101], .c 19, .c 3, .p pv5 [pv2,pv47,pv12613], .c 5, .c 3, .c 71,
  .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv29,pv3407], .c 3, .c 523, .p pv2 [pv2,pv3,pv199,pv331],
  .c 3, .p pv5 [pv2,pv7,pv11,pv7699], .c 631, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv89,pv6661],
  .p pv2 [pv2,pv3,pv5,pv7,pv941], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv139,pv853], .c 23,
  .c 3, .p pv2 [pv2,pv19,pv15601], .c 11, .c 3, .p pv2 [pv2,pv17,pv43,pv811], .c 5, .c 3,
  .p pv3 [pv2,pv7,pv31,pv683], .c 13, .c 3, .c 5, .p pv11 [pv2,pv3,pv23,pv179], .c 3, .c 11,
  .p pv7 [pv2,pv3,pv7,pv37,pv109], .c 3, .p pv2 [pv2,pv592853], .c 7, .c 3, .c 467, .c 5, .c 3,
  .c 23, .p pv47 [pv2,pv3,pv5,pv41,pv241], .c 3, .c 5, .c 353, .c 3, .c 181, .c 17, .c 3, .c 7,
  .c 37, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv296437], .c 7, .c 3, .c 5, .c 401, .c 3, .c 41,
  .c 47, .c 3, .c 11, .c 13, .c 3, .c 601, .c 5, .c 3, .c 7, .c 29, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv3137], .c 3, .p pv17 [pv2,pv5,pv19,pv79], .c 7,
]
private theorem h0144c23 : checkBlock 1185539 128 b0144c23 = true := by
  decide +kernel

private def b0144c24 : List Row := [
  .c 3, .p pv2 [pv2,pv521,pv569], .c 127, .c 3, .c 151, .c 5, .c 3, .c 19, .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv49409], .c 3, .c 7, .p pv7 [pv2,pv3,pv11,pv53,pv113], .c 3,
  .p pv2 [pv2,pv673,pv881], .c 751, .c 3, .c 11, .c 5, .c 3, .c 29, .c 59, .c 3, .c 5, .c 13,
  .c 3, .p pv2 [pv2,pv5,pv37,pv641], .c 557, .c 3, .c 23, .p pv2 [pv2,pv3,pv65881], .c 3, .c 7,
  .c 5, .c 3, .c 17, .p pv7 [pv2,pv3,pv5,pv7,pv5647], .c 3, .c 5, .c 7, .c 3, .c 107,
  .p pv3 [pv2,pv3,pv197647], .c 3, .c 37, .p pv29 [pv2,pv3,pv11,pv1123], .c 3,
  .p pv2 [pv2,pv296473], .c 5, .c 3, .c 11, .c 61, .c 3, .c 5, .p pv2 [pv2,pv3,pv197651], .c 3,
  .c 443, .c 71, .c 3, .c 1087, .c 7, .c 3, .c 19, .c 5, .c 3, .p pv3 [pv2,pv53,pv2797],
  .p pv41 [pv2,pv3,pv5,pv13177], .c 3, .c 5, .c 17, .c 3, .c 307, .c 11, .c 3, .c 7, .c 23, .c 3,
  .p pv3 [pv2,pv37061], .c 5, .c 3, .c 59, .c 7, .c 3, .c 5, .c 31, .c 3, .c 17, .c 331, .c 3,
  .c 13, .p pv2 [pv2,pv3,pv157,pv1259], .c 3, .c 43, .c 5, .c 3, .c 7, .c 229, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv2017], .c 3, .p pv3 [pv2,pv5,pv593], .c 7, .c 3, .c 41, .c 11, .c 3,
  .c 29, .c 5, .c 3, .c 97, .c 269, .c 3, .c 5, .c 79, .c 3, .c 7, .p pv17 [pv2,pv3,pv24709],
  .c 3, .c 19, .c 17, .c 3, .c 101, .c 5, .c 3, .p pv3 [pv2,pv41,pv113],
]
private theorem h0144c24 : checkBlock 1185795 128 b0144c24 = true := by
  decide +kernel

private def b0144c25 : List Row := [
  .p pv2 [pv2,pv3,pv5,pv7907], .c 3, .c 5, .p pv13 [pv2,pv3,pv17,pv19], .c 3, .c 389,
  .p pv3 [pv2,pv3,pv197677], .c 3, .p pv2 [pv2,pv7,pv84719], .c 43, .c 3, .c 7, .c 5, .c 3,
  .p pv11 [pv2,pv607,pv977], .c 13, .c 3, .c 5, .c 7, .c 3, .c 31, .c 181, .c 3, .c 11,
  .p pv13 [pv2,pv3,pv197683], .c 3, .c 89, .c 5, .c 3, .c 37, .p pv29 [pv2,pv3,pv5,pv23,pv191],
  .c 3, .c 5, .p pv5 [pv2,pv3,pv97,pv1019], .c 3, .p pv3 [pv2,pv5,pv13,pv2281], .c 499, .c 3,
  .p pv5 [pv2,pv71,pv8353], .c 7, .c 3, .c 13, .c 5, .c 3, .c 47, .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv37,pv137], .c 3, .c 19, .c 31, .c 3, .c 7, .c 13, .c 3, .c 11, .c 5,
  .c 3, .p pv3 [pv2,pv67,pv2213], .c 7, .c 3, .c 5, .c 73, .c 3, .p pv11 [pv2,pv5,pv127,pv467],
  .c 37, .c 3, .c 29, .c 19, .c 3, .c 53, .c 5, .c 3, .c 7, .c 167, .c 3, .c 5, .c 11, .c 3,
  .c 13, .c 7, .c 3, .p pv3 [pv2,pv29,pv5113], .c 757, .c 3, .c 1013, .c 5, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv5,pv39541], .c 3, .c 5, .c 13, .c 3, .c 7, .c 17, .c 3, .c 109,
  .p pv31 [pv2,pv3,pv7,pv23,pv307], .c 3, .c 41, .c 5, .c 3, .p pv2 [pv2,pv449,pv1321], .c 173,
  .c 3, .c 5, .c 61, .c 3, .c 23, .c 11, .c 3, .c 17, .c 859, .c 3, .c 7, .c 5, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv5,pv7,pv269], .c 3, .c 5, .c 7, .c 3, .c 191, .c 19, .c 3,
]
private theorem h0144c25 : checkBlock 1186051 128 b0144c25 = true := by
  decide +kernel

private def b0144c26 : List Row := [
  .c 127, .c 107, .c 3, .c 59, .c 5, .c 3, .c 83, .p pv13 [pv2,pv3,pv5,pv4943], .c 3, .c 5, .c 43,
  .c 3, .c 37, .c 929, .c 3, .p pv3 [pv2,pv131,pv283], .c 7, .c 3, .c 79, .c 5, .c 3,
  .p pv2 [pv2,pv296587], .p pv11 [pv2,pv3,pv5,pv11,pv719], .c 3, .c 5, .c 293, .c 3, .c 11, .c 23,
  .c 3, .c 7, .c 67, .c 3, .p pv2 [pv2,pv11,pv59,pv457], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5,
  .c 113, .c 3, .c 277, .c 13, .c 3, .p pv2 [pv2,pv17,pv73,pv239], .c 761, .c 3,
  .p pv2 [pv2,pv7,pv83,pv1021], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv71,pv557], .c 3, .c 5,
  .c 19, .c 3, .c 47, .c 7, .c 3, .c 11, .c 919, .c 3, .c 353, .c 5, .c 3,
  .p pv7 [pv2,pv11,pv199,pv271], .p pv17 [pv2,pv3,pv5,pv9887], .c 3, .c 5, .c 17, .c 3, .c 7,
  .c 211, .c 3, .c 103, .c 89, .c 3, .c 31, .c 5, .c 3, .c 73, .c 11, .c 3, .c 5, .c 29, .c 3,
  .c 17, .c 479, .c 3, .c 149, .p pv7 [pv2,pv3,pv1831], .c 3, .c 7, .c 5, .c 3, .c 41, .c 23,
  .c 3, .c 5, .c 7, .c 3, .c 53, .c 373, .c 3, .p pv2 [pv2,pv37,pv8017],
  .p pv3 [pv2,pv3,pv197753], .c 3, .c 13, .c 5, .c 3, .c 227, .c 19, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv41,pv1447], .c 431, .c 3, .c 23, .c 7, .c 3, .c 37, .c 5, .c 3, .c 11, .c 127,
]
private theorem h0144c26 : checkBlock 1186307 128 b0144c26 = true := by
  decide +kernel

private def b0144c27 : List Row := [
  .c 3, .c 5, .c 769, .c 3, .c 743, .p pv2 [pv2,pv3,pv61,pv1621], .c 3, .c 7, .c 1051, .c 3,
  .c 17, .c 5, .c 3, .p pv2 [pv2,pv13,pv19,pv1201], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv10987],
  .c 3, .c 13, .c 11, .c 3, .c 19, .c 47, .c 3, .c 113, .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv19777], .c 3, .c 5, .c 13, .c 3, .p pv17 [pv2,pv5,pv107,pv1109], .c 7,
  .c 3, .c 67, .c 23, .c 3, .c 139, .c 5, .c 3, .c 31, .c 17, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv47,pv263], .c 3, .c 7, .c 41, .c 3, .c 59, .c 11, .c 3, .p pv3 [pv2,pv74167],
  .c 5, .c 3, .c 13, .c 1031, .c 3, .c 5, .c 523, .c 3, .c 11, .p pv2 [pv2,pv3,pv13,pv7607], .c 3,
  .p pv3 [pv2,pv7,pv21191], .p pv2 [pv2,pv3,pv97,pv2039], .c 3, .c 7, .c 5, .c 3, .c 29, .c 31,
  .c 3, .c 5, .c 7, .c 3, .c 19, .c 53, .c 3, .c 733, .c 131, .c 3, .c 797, .c 5, .c 3,
  .p pv11 [pv2,pv7,pv29,pv37,pv79], .p pv29 [pv2,pv3,pv5,pv19,pv347], .c 3, .c 5, .c 491, .c 3,
  .p pv11 [pv2,pv5,pv47,pv101], .c 17, .c 3, .c 11, .c 7, .c 3, .c 157, .c 5, .c 3,
  .p pv3 [pv2,pv11,pv613], .c 67, .c 3, .c 5, .c 23, .c 3, .c 677, .c 13, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv98899], .c 3, .c 701, .c 5, .c 3, .c 421, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv223,pv887], .c 3, .p pv2 [pv2,pv5,pv118681], .p pv5 [pv2,pv3,pv11,pv37], .c 3,
  .c 79,
]
private theorem h0144c27 : checkBlock 1186563 128 b0144c27 = true := by
  decide +kernel

private def b0144c28 : List Row := [
  .c 487, .c 3, .c 11, .c 5, .c 3, .c 7, .c 137, .c 3, .c 5, .p pv13 [pv2,pv3,pv7,pv71,pv199],
  .c 3, .p pv3 [pv2,pv5,pv29671], .c 7, .c 3, .p pv5 [pv2,pv23,pv25801], .c 37, .c 3, .c 433,
  .c 5, .c 3, .c 659, .c 13, .c 3, .c 5, .c 11, .c 3, .c 7, .c 19, .c 3, .c 61,
  .p pv3 [pv2,pv3,pv7,pv11,pv367], .c 3, .c 29, .c 5, .c 3, .c 11, .c 47, .c 3, .c 5, .c 31, .c 3,
  .c 109, .c 59, .c 3, .c 71, .c 41, .c 3, .c 7, .c 5, .c 3, .c 263, .c 139, .c 3, .c 5, .c 7,
  .c 3, .p pv7 [pv2,pv5,pv19,pv6247], .c 11, .c 3, .p pv3 [pv2,pv148367], .c 13, .c 3, .c 293,
  .c 5, .c 3, .c 19, .c 107, .c 3, .c 5, .c 17, .c 3, .c 23, .p pv23 [pv2,pv3,pv7,pv59,pv479],
  .c 3, .c 557, .c 7, .c 3, .p pv2 [pv2,pv43,pv67,pv103], .c 5, .c 3, .c 251,
  .p pv19 [pv2,pv3,pv5,pv73,pv271], .c 3, .c 5, .c 19, .c 3, .c 13, .c 89, .c 3, .c 7, .c 11,
  .c 3, .p pv2 [pv2,pv593501], .c 5, .c 3, .p pv3 [pv2,pv17,pv1091], .c 7, .c 3, .c 5, .c 13,
  .c 3, .c 11, .p pv5 [pv2,pv3,pv197837], .c 3, .c 419, .c 223, .c 3, .c 911, .c 5, .c 3, .c 7,
  .c 53, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv9421], .c 3, .p pv2 [pv2,pv5,pv23741], .c 7, .c 3,
  .c 29, .c 17, .c 3, .c 19, .c 5, .c 3, .c 13, .c 37, .c 3,
]
private theorem h0144c28 : checkBlock 1186819 128 b0144c28 = true := by
  decide +kernel

private def b0144c29 : List Row := [
  .c 5, .c 157, .c 3, .c 7, .c 31, .c 3, .c 11, .p pv11 [pv2,pv3,pv7,pv3533], .c 3, .c 17, .c 5,
  .c 3, .c 23, .c 19, .c 3, .c 5, .p pv2 [pv2,pv3,pv67,pv2953], .c 3,
  .p pv7 [pv2,pv5,pv17,pv6983], .c 239, .c 3, .p pv2 [pv2,pv7,pv42397], .c 109, .c 3, .c 7, .c 5,
  .c 3, .c 163, .c 11, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv59357], .c 193, .c 3, .c 13,
  .c 83, .c 3, .c 11, .c 5, .c 3, .p pv7 [pv2,pv7,pv19,pv4463], .c 17, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv241,pv821], .c 3, .c 89, .c 13, .c 3, .c 19, .c 7, .c 3, .c 97, .c 5, .c 3,
  .p pv2 [pv2,pv296797], .c 23, .c 3, .c 5, .c 11, .c 3, .p pv13 [pv2,pv5,pv7,pv53], .c 167, .c 3,
  .c 7, .c 313, .c 3, .c 359, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv65957], .c 3,
  .c 29, .p pv5 [pv2,pv3,pv83,pv149], .c 3, .c 23, .p pv11 [pv2,pv3,pv13,pv31,pv491], .c 3, .c 61,
  .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 59, .c 3, .p pv2 [pv2,pv5,pv23,pv29,pv89], .c 7, .c 3,
  .c 47, .c 31, .c 3, .c 43, .c 5, .c 3, .p pv7 [pv2,pv41,pv14479], .c 103, .c 3, .c 5,
  .p pv23 [pv2,pv3,pv433,pv457], .c 3, .c 7, .c 37, .c 3, .c 17, .c 173, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv296827], .p pv11 [pv2,pv3,pv5,pv19,pv2083], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv13,pv43,pv59], .c 3, .p pv3 [pv2,pv5,pv29683], .c 127, .c 3, .c 409, .c 11,
]
private theorem h0144c29 : checkBlock 1187075 128 b0144c29 = true := by
  decide +kernel

private def b0144c30 : List Row := [
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv139,pv4271], .p pv2 [pv2,pv3,pv5,pv7,pv11,pv257], .c 3,
  .c 5, .c 7, .c 3, .c 11, .p pv5 [pv2,pv3,pv23,pv239], .c 3, .p pv2 [pv2,pv101,pv2939], .c 43,
  .c 3, .p pv2 [pv2,pv11,pv31,pv1741], .c 5, .c 3, .p pv3 [pv2,pv7,pv13,pv233], .c 1063, .c 3,
  .c 5, .c 97, .c 3, .c 13, .p pv5 [pv2,pv3,pv7,pv17,pv1663], .c 3, .p pv2 [pv2,pv19,pv31247],
  .c 7, .c 3, .c 31, .c 5, .c 3, .c 17, .c 41, .c 3, .c 5, .c 13, .c 3,
  .p pv2 [pv2,pv5,pv7,pv16963], .p pv2 [pv2,pv3,pv53,pv1867], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv73,pv2711], .c 3, .c 1021, .c 5, .c 3, .p pv2 [pv2,pv11,pv26987], .c 7, .c 3,
  .c 5, .c 227, .c 3, .c 37, .c 19, .c 3, .c 191, .c 79, .c 3, .p pv2 [pv2,pv7,pv42409], .c 5,
  .c 3, .c 7, .c 11, .c 3, .c 5, .c 17, .c 3, .p pv19 [pv2,pv5,pv118747], .c 7, .c 3, .c 139,
  .p pv3 [pv2,pv3,pv37,pv1783], .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv43,pv863], .c 73, .c 3,
  .c 5, .c 509, .c 3, .c 7, .c 569, .c 3, .p pv2 [pv2,pv281,pv2113],
  .p pv2 [pv2,pv3,pv7,pv67,pv211], .c 3, .c 23, .c 5, .c 3, .c 19, .c 29, .c 3, .c 5, .c 11, .c 3,
  .c 43, .c 971, .c 3, .c 13, .p pv3 [pv2,pv3,pv11,pv19,pv947], .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv5,pv7,pv13,pv29], .c 3, .c 5, .c 7, .c 3, .p pv13 [pv2,pv5,pv11,pv2699],
  .c 13, .c 3, .p pv5 [pv2,pv593783], .c 17, .c 3, .c 739, .c 5, .c 3, .c 29, .c 467, .c 3, .c 5,
]
private theorem h0144c30 : checkBlock 1187331 128 b0144c30 = true := by
  decide +kernel

private def b0144c31 : List Row := [
  .p pv2 [pv2,pv3,pv17,pv3881], .c 3, .c 239, .c 11, .c 3, .c 257, .c 7, .c 3, .c 17, .c 5, .c 3,
  .c 61, .c 59, .c 3, .c 5, .c 43, .c 3, .c 643, .p pv3 [pv2,pv3,pv7331], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv13,pv23,pv331], .c 3, .c 19, .c 5, .c 3, .p pv13 [pv2,pv191,pv3109], .c 7,
  .c 3, .c 5, .c 41, .c 3, .c 23, .c 137, .c 3, .p pv3 [pv2,pv148457], .c 11, .c 3, .c 37, .c 5,
  .c 3, .c 7, .c 17, .c 3, .c 5, .c 53, .c 3, .c 11, .c 7, .c 3, .p pv5 [pv2,pv79,pv7517],
  .p pv7 [pv2,pv3,pv17,pv41,pv71], .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv223,pv2663],
  .p pv2 [pv2,pv3,pv5,pv37,pv107], .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv15227], .c 3, .c 7, .c 197,
  .c 3, .p pv2 [pv2,pv296929], .c 13, .c 3, .p pv2 [pv2,pv17,pv181,pv193], .c 5, .c 3, .c 41,
  .c 61, .c 3, .c 5, .c 37, .c 3, .p pv2 [pv2,pv5,pv59387], .c 23, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv32993], .c 3, .c 7, .c 5, .c 3, .c 71, .p pv17 [pv2,pv3,pv5,pv7,pv101], .c 3,
  .c 5, .c 7, .c 3, .c 13, .c 17, .c 3, .c 131, .c 593, .c 3, .c 53, .c 5, .c 3, .c 23, .c 11,
  .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv5939], .p pv2 [pv2,pv3,pv7,pv11,pv857], .c 3, .c 17,
  .c 7, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv173,pv3433], .p pv2 [pv2,pv3,pv5,pv6599], .c 3,
  .c 5, .c 31, .c 3, .c 47, .p pv5 [pv2,pv3,pv43,pv1151], .c 3, .c 7, .p pv11 [pv2,pv3,pv21997],
  .c 3,
]
private theorem h0144c31 : checkBlock 1187587 128 b0144c31 = true := by
  decide +kernel

def rows0144 : List Row :=
  b0144c00 ++ b0144c01 ++ b0144c02 ++ b0144c03 ++ b0144c04 ++ b0144c05 ++ b0144c06 ++ b0144c07 ++
  b0144c08 ++ b0144c09 ++ b0144c10 ++ b0144c11 ++ b0144c12 ++ b0144c13 ++ b0144c14 ++ b0144c15 ++
  b0144c16 ++ b0144c17 ++ b0144c18 ++ b0144c19 ++ b0144c20 ++ b0144c21 ++ b0144c22 ++ b0144c23 ++
  b0144c24 ++ b0144c25 ++ b0144c26 ++ b0144c27 ++ b0144c28 ++ b0144c29 ++ b0144c30 ++ b0144c31

theorem checked0144 : checkBlock 1179651 4096 rows0144 = true :=
  checkBlock_append h0144c00 (
    checkBlock_append h0144c01 (
    checkBlock_append h0144c02 (
    checkBlock_append h0144c03 (
    checkBlock_append h0144c04 (
    checkBlock_append h0144c05 (
    checkBlock_append h0144c06 (
    checkBlock_append h0144c07 (
    checkBlock_append h0144c08 (
    checkBlock_append h0144c09 (
    checkBlock_append h0144c10 (
    checkBlock_append h0144c11 (
    checkBlock_append h0144c12 (
    checkBlock_append h0144c13 (
    checkBlock_append h0144c14 (
    checkBlock_append h0144c15 (
    checkBlock_append h0144c16 (
    checkBlock_append h0144c17 (
    checkBlock_append h0144c18 (
    checkBlock_append h0144c19 (
    checkBlock_append h0144c20 (
    checkBlock_append h0144c21 (
    checkBlock_append h0144c22 (
    checkBlock_append h0144c23 (
    checkBlock_append h0144c24 (
    checkBlock_append h0144c25 (
    checkBlock_append h0144c26 (
    checkBlock_append h0144c27 (
    checkBlock_append h0144c28 (
    checkBlock_append h0144c29 (
    checkBlock_append h0144c30 (
    h0144c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
