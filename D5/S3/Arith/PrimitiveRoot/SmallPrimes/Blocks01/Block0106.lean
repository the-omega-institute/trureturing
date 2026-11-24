/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0106
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks01/Block0106.checked0106
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table104

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0106c00 : List Row := [
  .c 5, .c 7, .c 3, .c 13, .c 557, .c 3, .c 157, .p pv7 [pv2,pv3,pv79,pv229], .c 3, .c 11, .c 5,
  .c 3, .p pv2 [pv2,pv7,pv8861], .p pv2 [pv2,pv3,pv5,pv41,pv353], .c 3, .c 5, .c 13, .c 3, .c 233,
  .c 103, .c 3, .p pv2 [pv2,pv61,pv3559], .c 7, .c 3, .c 31, .c 5, .c 3, .p pv3 [pv2,pv73,pv1487],
  .c 17, .c 3, .c 5, .c 11, .c 3, .c 41, .p pv3 [pv2,pv3,pv144737], .c 3, .c 7, .c 83, .c 3,
  .c 19, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 79, .c 3, .p pv11 [pv2,pv5,pv11,pv1579],
  .p pv5 [pv2,pv3,pv13,pv19,pv293], .c 3, .c 23, .p pv7 [pv2,pv3,pv53,pv2731], .c 3, .c 29, .c 5,
  .c 3, .c 7, .c 19, .c 3, .c 5, .c 191, .c 3, .c 73, .c 7, .c 3, .p pv5 [pv2,pv434243],
  .p pv11 [pv2,pv3,pv36187], .c 3, .p pv2 [pv2,pv29,pv7487], .c 5, .c 3, .c 101, .c 37, .c 3,
  .c 5, .c 521, .c 3, .c 7, .c 17, .c 3, .c 13, .c 107, .c 3, .c 421, .c 5, .c 3,
  .p pv3 [pv2,pv19,pv2857], .p pv3 [pv2,pv3,pv5,pv13,pv17,pv131], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv4021], .c 3, .c 347, .c 13, .c 3, .c 17, .c 11, .c 3, .c 7, .c 5, .c 3,
  .p pv17 [pv2,pv31,pv14009], .p pv17 [pv2,pv3,pv5,pv7,pv11,pv47], .c 3, .c 5, .c 7, .c 3, .c 11,
  .c 197, .c 3, .p pv3 [pv2,pv27143], .c 29, .c 3, .p pv5 [pv2,pv11,pv13,pv3037], .c 5, .c 3,
  .c 31, .c 677, .c 3, .c 5, .c 229, .c 3, .c 269, .p pv3 [pv2,pv3,pv7,pv20681], .c 3, .c 47,
  .c 7,
]
private theorem h0106c00 : checkBlock 868355 128 b0106c00 = true := by
  decide +kernel

private def b0106c01 : List Row := [
  .c 3, .p pv2 [pv2,pv37,pv5869], .c 5, .c 3, .c 181, .c 13, .c 3, .c 5, .c 73, .c 3, .c 113,
  .c 173, .c 3, .c 7, .p pv3 [pv2,pv3,pv144773], .c 3, .c 43, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5,
  .c 59, .c 3, .c 19, .p pv17 [pv2,pv3,pv48259], .c 3, .c 41, .p pv2 [pv2,pv3,pv191,pv379], .c 3,
  .c 13, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv86869], .c 7, .c 3,
  .p pv3 [pv2,pv108587], .c 13, .c 3, .c 11, .c 5, .c 3, .c 563, .c 251, .c 3, .c 5, .c 17, .c 3,
  .c 7, .c 37, .c 3, .p pv5 [pv2,pv434363], .c 43, .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv33413], .p pv2 [pv2,pv3,pv5,pv14479], .c 3, .c 5, .c 11, .c 3, .c 13, .c 29,
  .c 3, .c 457, .c 499, .c 3, .c 7, .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv7,pv197], .c 3, .c 5,
  .c 7, .c 3, .c 439, .p pv3 [pv2,pv3,pv29,pv4993], .c 3, .p pv2 [pv2,pv337,pv1289], .c 67, .c 3,
  .p pv3 [pv2,pv131,pv829], .c 5, .c 3, .p pv7 [pv2,pv7,pv62057], .p pv7 [pv2,pv3,pv5,pv181],
  .c 3, .c 5, .c 127, .c 3, .c 29, .c 11, .c 3, .p pv3 [pv2,pv13,pv4177], .c 7, .c 3, .c 61, .c 5,
  .c 3, .c 13, .c 41, .c 3, .c 5, .c 31, .c 3, .p pv3 [pv2,pv5,pv7,pv29,pv107], .c 673, .c 3,
  .c 7, .p pv13 [pv2,pv3,pv23,pv787], .c 3, .c 17, .c 5, .c 3, .c 191, .c 7, .c 3, .c 5,
]
private theorem h0106c01 : checkBlock 868611 128 b0106c01 = true := by
  decide +kernel

private def b0106c02 : List Row := [
  .p pv5 [pv2,pv3,pv179,pv809], .c 3, .c 23, .p pv5 [pv2,pv3,pv41,pv883], .c 3,
  .p pv2 [pv2,pv217219], .c 11, .c 3, .p pv2 [pv2,pv7,pv53,pv1171], .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv11,pv2633], .c 3, .c 5, .c 317, .c 3, .c 11, .c 7, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv19,pv37,pv103], .c 3, .c 41, .c 5, .c 3, .c 73, .c 17, .c 3, .c 5, .c 19,
  .c 3, .c 7, .c 13, .c 3, .p pv3 [pv2,pv47,pv2311], .p pv3 [pv2,pv3,pv7,pv17,pv1217], .c 3,
  .p pv5 [pv2,pv434471], .c 5, .c 3, .c 277, .p pv3 [pv2,pv3,pv5,pv1931], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv29,pv227], .c 3, .c 31, .c 23, .c 3, .c 11, .c 71, .c 3, .c 7, .c 5,
  .c 3, .c 173, .c 181, .c 3, .c 5, .c 7, .c 3, .c 137, .p pv7 [pv2,pv3,pv31,pv73], .c 3,
  .p pv2 [pv2,pv89,pv2441], .p pv23 [pv2,pv3,pv13,pv857], .c 3, .c 19, .c 5, .c 3, .c 23, .c 11,
  .c 3, .c 5, .p pv11 [pv2,pv3,pv36209], .c 3, .p pv2 [pv2,pv5,pv43451], .c 17, .c 3, .c 383,
  .c 7, .c 3, .c 11, .c 5, .c 3, .p pv13 [pv2,pv293,pv1483], .c 19, .c 3, .c 5, .c 379, .c 3,
  .c 463, .p pv5 [pv2,pv3,pv72421], .c 3, .c 7, .p pv2 [pv2,pv3,pv48281], .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv167,pv1301], .c 7, .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv21727], .c 113,
  .c 3, .c 467, .c 13, .c 3, .c 37, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 877, .c 3, .c 71,
  .c 7, .c 3, .c 19, .p pv17 [pv2,pv3,pv41,pv3533], .c 3,
]
private theorem h0106c02 : checkBlock 868867 128 b0106c02 = true := by
  decide +kernel

private def b0106c03 : List Row := [
  .c 337, .c 5, .c 3, .c 59, .p pv2 [pv2,pv3,pv5,pv29,pv37], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv19,pv953], .c 3, .c 7, .c 11, .c 3, .c 23, .c 599, .c 3,
  .p pv3 [pv2,pv157,pv173], .c 5, .c 3, .c 17, .c 107, .c 3, .c 5, .c 13, .c 3, .c 47,
  .p pv2 [pv2,pv3,pv72431], .c 3, .c 827, .p pv11 [pv2,pv3,pv31,pv4673], .c 3, .c 7, .c 5, .c 3,
  .c 61, .c 67, .c 3, .c 5, .c 7, .c 3, .c 313, .p pv3 [pv2,pv3,pv43,pv1123], .c 3, .c 853, .c 11,
  .c 3, .c 251, .c 5, .c 3, .c 13, .c 659, .c 3, .c 5, .c 17, .c 3, .c 11,
  .p pv5 [pv2,pv3,pv7,pv13,pv199], .c 3, .c 79, .c 7, .c 3, .c 239, .c 5, .c 3,
  .p pv3 [pv2,pv6791], .p pv11 [pv2,pv3,pv5,pv19,pv61], .c 3, .c 5, .p pv31 [pv2,pv3,pv12073],
  .c 3, .c 17, .c 89, .c 3, .c 7, .c 19, .c 3, .p pv3 [pv2,pv193,pv563], .c 5, .c 3, .c 163, .c 7,
  .c 3, .c 5, .c 241, .c 3, .p pv2 [pv2,pv5,pv86929], .p pv2 [pv2,pv3,pv2683], .c 3, .c 11,
  .p pv3 [pv2,pv3,pv144883], .c 3, .p pv7 [pv2,pv7,pv31,pv2003], .c 5, .c 3, .c 7, .c 61, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv7,pv79,pv131], .c 3, .p pv7 [pv2,pv5,pv103,pv211], .c 7, .c 3, .c 431,
  .c 17, .c 3, .c 29, .c 5, .c 3, .p pv2 [pv2,pv593,pv733], .c 11, .c 3, .c 5, .c 587, .c 3, .c 7,
  .c 617, .c 3, .c 73, .c 47, .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv271,pv401],
  .p pv31 [pv2,pv3,pv5,pv28979], .c 3, .c 5, .c 23,
]
private theorem h0106c03 : checkBlock 869123 128 b0106c03 = true := by
  decide +kernel

private def b0106c04 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv17,pv2557], .c 19, .c 3, .c 541, .c 37, .c 3, .c 7, .c 5, .c 3,
  .p pv11 [pv2,pv434699], .c 13, .c 3, .c 5, .c 7, .c 3, .c 97, .p pv37 [pv2,pv3,pv53,pv1367],
  .c 3, .c 43, .p pv2 [pv2,pv3,pv11,pv4391], .c 3, .c 23, .c 5, .c 3, .c 11, .c 17, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv24151], .c 3, .c 89, .p pv2 [pv2,pv3,pv7,pv127,pv163], .c 3, .c 131, .c 7,
  .c 3, .c 13, .c 5, .c 3, .c 19, .p pv13 [pv2,pv3,pv5,pv43,pv337], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv13,pv71,pv157], .c 3, .p pv7 [pv2,pv5,pv7,pv12421], .c 11, .c 3, .c 7, .c 13,
  .c 3, .c 59, .c 5, .c 3, .p pv3 [pv2,pv31,pv1753], .c 7, .c 3, .c 5, .c 19, .c 3,
  .p pv11 [pv2,pv5,pv37,pv47], .c 43, .c 3, .c 29, .c 101, .c 3, .c 229, .c 5, .c 3, .c 7,
  .p pv17 [pv2,pv3,pv5,pv3623], .c 3, .c 5, .c 797, .c 3, .c 13, .c 7, .c 3, .c 37, .c 11, .c 3,
  .p pv5 [pv2,pv59,pv7369], .c 5, .c 3, .c 521, .p pv11 [pv2,pv3,pv5,pv11,pv17,pv31], .c 3, .c 5,
  .c 13, .c 3, .c 7, .p pv2 [pv2,pv3,pv16103], .c 3, .c 17, .c 41, .c 3, .c 19, .c 5, .c 3,
  .p pv2 [pv2,pv131,pv3319], .c 31, .c 3, .c 5, .p pv3 [pv2,pv3,pv144931], .c 3, .c 83, .c 67,
  .c 3, .p pv3 [pv2,pv7,pv13,pv2389], .p pv19 [pv2,pv3,pv48311], .c 3, .c 7, .c 5, .c 3, .c 13,
  .c 19, .c 3, .c 5, .c 7, .c 3, .c 829, .c 29, .c 3, .c 11, .c 103, .c 3, .c 571,
]
private theorem h0106c04 : checkBlock 869379 128 b0106c04 = true := by
  decide +kernel

private def b0106c05 : List Row := [
  .c 5, .c 3, .c 271, .c 47, .c 3, .c 5, .c 601, .c 3, .c 41, .c 23, .c 3, .p pv3 [pv2,pv108707],
  .c 7, .c 3, .p pv5 [pv2,pv434831], .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .c 53, .c 3, .c 29,
  .p pv2 [pv2,pv3,pv11,pv13177], .c 3, .c 7, .p pv13 [pv2,pv3,pv47,pv257], .c 3, .c 11, .c 5,
  .c 3, .c 23, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv19,pv2543], .c 3, .c 79, .c 13, .c 3,
  .p pv2 [pv2,pv217429], .c 59, .c 3, .c 139, .c 5, .c 3, .c 7, .c 307, .c 3, .c 5, .c 11, .c 3,
  .c 263, .c 7, .c 3, .p pv2 [pv2,pv434873], .c 523, .c 3, .p pv3 [pv2,pv13,pv8363], .c 5, .c 3,
  .c 11, .c 43, .c 3, .c 5, .c 31, .c 3, .c 7, .p pv5 [pv2,pv3,pv72481], .c 3,
  .p pv3 [pv2,pv54361], .p pv2 [pv2,pv3,pv7,pv13,pv59], .c 3, .c 53, .c 5, .c 3, .c 233, .c 13,
  .c 3, .c 5, .c 29, .c 3, .c 19, .c 11, .c 3, .p pv5 [pv2,pv7,pv62129], .p pv7 [pv2,pv3,pv18121],
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv434909], .c 71, .c 3, .c 5, .c 7, .c 3, .c 607, .c 37,
  .c 3, .c 23, .c 17, .c 3, .c 13, .c 5, .c 3, .p pv11 [pv2,pv7,pv317], .c 193, .c 3, .c 5,
  .c 359, .c 3, .c 67, .p pv5 [pv2,pv3,pv7,pv139,pv149], .c 3, .c 311, .c 7, .c 3, .c 17, .c 5,
  .c 3, .p pv17 [pv2,pv434939], .c 509, .c 3, .c 5, .p pv3 [pv2,pv3,pv89,pv181], .c 3,
]
private theorem h0106c05 : checkBlock 869635 128 b0106c05 = true := by
  decide +kernel

private def b0106c06 : List Row := [
  .c 11, .p pv5 [pv2,pv3,pv71,pv1021], .c 3, .c 7, .p pv2 [pv2,pv3,pv144983], .c 3, .c 167, .c 5,
  .c 3, .p pv2 [pv2,pv13,pv16729], .c 7, .c 3, .c 5, .c 293, .c 3, .c 13, .c 47, .c 3,
  .p pv5 [pv2,pv434963], .c 23, .c 3, .c 43, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 13, .c 3,
  .p pv11 [pv2,pv5,pv127,pv137], .c 7, .c 3, .c 11, .p pv3 [pv2,pv3,pv17,pv2843], .c 3, .c 71,
  .c 5, .c 3, .c 691, .c 29, .c 3, .c 5, .c 463, .c 3, .c 7, .p pv5 [pv2,pv3,pv61,pv2377], .c 3,
  .c 113, .p pv2 [pv2,pv3,pv7,pv10357], .c 3, .c 97, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv83,pv1747], .c 3, .c 149, .p pv2 [pv2,pv3,pv11,pv13], .c 3, .c 47, .c 43,
  .c 3, .c 7, .c 5, .c 3, .c 19, .p pv41 [pv2,pv3,pv5,pv7,pv1381], .c 3, .c 5, .c 7, .c 3, .c 103,
  .c 17, .c 3, .p pv5 [pv2,pv31,pv14033], .p pv7 [pv2,pv3,pv19,pv53], .c 3, .c 743, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv29,pv2143], .c 41, .c 3, .c 5, .c 11, .c 3, .c 733, .c 59, .c 3, .c 13, .c 7,
  .c 3, .p pv2 [pv2,pv435041], .c 5, .c 3, .c 11, .c 227, .c 3, .c 5, .p pv5 [pv2,pv3,pv18127],
  .c 3, .c 53, .c 13, .c 3, .c 7, .p pv23 [pv2,pv3,pv31,pv2339], .c 3, .c 23, .c 5, .c 3, .c 179,
  .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv145021], .c 3, .p pv2 [pv2,pv5,pv87013], .c 11, .c 3,
  .p pv3 [pv2,pv23,pv4729], .c 31, .c 3, .c 19, .c 5,
]
private theorem h0106c06 : checkBlock 869891 128 b0106c06 = true := by
  decide +kernel

private def b0106c07 : List Row := [
  .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv5801], .c 3, .c 5, .c 367, .c 3, .p pv7 [pv2,pv5,pv73,pv149],
  .c 7, .c 3, .c 859, .p pv7 [pv2,pv3,pv13,pv2789], .c 3, .p pv2 [pv2,pv83,pv2621], .c 5, .c 3,
  .c 17, .c 13, .c 3, .c 5, .c 97, .c 3, .c 7, .c 389, .c 3, .p pv3 [pv2,pv17,pv67,pv191], .c 11,
  .c 3, .c 29, .c 5, .c 3, .c 373, .p pv19 [pv2,pv3,pv5,pv11,pv293], .c 3, .c 5, .c 251, .c 3,
  .c 11, .p pv3 [pv2,pv3,pv145037], .c 3, .c 199, .p pv2 [pv2,pv3,pv23,pv1051], .c 3, .c 7, .c 5,
  .c 3, .p pv13 [pv2,pv19,pv22901], .p pv13 [pv2,pv3,pv5,pv7,pv37], .c 3, .c 5, .c 7, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv47,pv1543], .c 3, .c 19, .c 13, .c 3, .c 31, .c 5, .c 3, .c 487,
  .p pv3 [pv2,pv3,pv5,pv29009], .c 3, .c 5, .c 37, .c 3, .c 17, .p pv2 [pv2,pv3,pv7,pv6907], .c 3,
  .c 11, .c 7, .c 3, .c 919, .c 5, .c 3, .c 47, .p pv2 [pv2,pv3,pv5,pv967], .c 3, .c 5, .c 41,
  .c 3, .c 13, .c 53, .c 3, .c 7, .c 29, .c 3, .p pv2 [pv2,pv435161], .c 5, .c 3,
  .p pv3 [pv2,pv108791], .c 7, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv43517], .c 23, .c 3,
  .c 599, .c 17, .c 3, .c 11, .c 5, .c 3, .c 7, .c 137, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv17,pv23,pv53], .c 3, .c 19, .c 7, .c 3, .c 29, .c 73, .c 3, .c 17, .c 5,
  .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv19,pv509], .c 3, .c 5, .c 11, .c 3, .c 7,
]
private theorem h0106c07 : checkBlock 870147 128 b0106c07 = true := by
  decide +kernel

private def b0106c08 : List Row := [
  .p pv2 [pv2,pv3,pv13,pv11159], .c 3, .p pv5 [pv2,pv29,pv43,pv349], .c 19, .c 3,
  .p pv2 [pv2,pv23,pv9461], .c 5, .c 3, .c 11, .c 83, .c 3, .c 5, .c 59, .c 3,
  .p pv7 [pv2,pv5,pv11,pv41,pv193], .p pv5 [pv2,pv3,pv9067], .c 3, .p pv2 [pv2,pv7,pv4441],
  .c 113, .c 3, .c 7, .c 5, .c 3, .c 31, .c 17, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv71,pv613], .c 11, .c 3, .c 13, .c 541, .c 3, .c 929, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv97,pv641], .c 23, .c 3, .c 5, .c 47, .c 3, .p pv2 [pv2,pv5,pv87049], .c 13,
  .c 3, .p pv3 [pv2,pv11,pv2473], .c 7, .c 3, .c 293, .c 5, .c 3, .c 89, .c 31, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv24181], .c 3, .c 587, .c 19, .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv13,pv16741], .c 5, .c 3, .c 659, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv145091],
  .c 3, .c 11, .c 17, .c 3, .c 139, .c 383, .c 3, .c 379, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv7,pv2591], .c 3, .c 47, .c 7, .c 3, .c 17, .p pv2 [pv2,pv3,pv2687], .c 3,
  .p pv3 [pv2,pv61,pv223], .c 5, .c 3, .c 19, .p pv11 [pv2,pv3,pv5,pv1451], .c 3, .c 5, .c 149,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv72551], .c 3, .c 11, .c 23, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv47,pv421], .c 53, .c 3, .c 5, .c 19, .c 3, .p pv3 [pv2,pv5,pv10883],
  .p pv2 [pv2,pv3,pv23,pv701], .c 3, .c 37, .c 13, .c 3, .c 7, .c 5, .c 3,
]
private theorem h0106c08 : checkBlock 870403 128 b0106c08 = true := by
  decide +kernel

private def b0106c09 : List Row := [
  .c 79, .c 11, .c 3, .c 5, .c 7, .c 3, .c 73, .c 71, .c 3, .c 239, .p pv3 [pv2,pv3,pv48371],
  .c 3, .c 11, .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv29023], .c 3, .c 5, .c 31, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv7,pv20731], .c 3, .c 43, .c 7, .c 3, .c 19, .c 5, .c 3, .c 251, .c 37, .c 3,
  .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv7,pv1777], .c 241, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv11,pv79,pv167], .c 3, .p pv5 [pv2,pv435371], .c 5, .c 3, .c 11, .c 7, .c 3,
  .c 5, .c 17, .c 3, .c 409, .c 433, .c 3, .c 863, .c 47, .c 3, .p pv2 [pv2,pv7,pv137,pv227],
  .c 5, .c 3, .c 7, .c 59, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv6911], .c 3, .c 17, .c 7, .c 3,
  .c 211, .c 41, .c 3, .c 23, .c 5, .c 3, .p pv3 [pv2,pv17,pv19,pv337],
  .p pv7 [pv2,pv3,pv5,pv29027], .c 3, .c 5, .c 73, .c 3, .c 7, .p pv7 [pv2,pv3,pv101,pv479], .c 3,
  .c 19, .c 461, .c 3, .p pv3 [pv2,pv37,pv1471], .c 5, .c 3, .c 127, .c 29, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv19,pv7639], .c 3, .c 353, .p pv2 [pv2,pv3,pv31,pv2341], .c 3, .c 13, .c 11,
  .c 3, .c 7, .c 5, .c 3, .c 37, .p pv11 [pv2,pv3,pv5,pv7,pv11,pv13,pv29], .c 3, .c 5, .c 7, .c 3,
  .c 11, .c 13, .c 3, .c 229, .p pv7 [pv2,pv3,pv131,pv277], .c 3, .c 17, .c 5, .c 3, .c 29,
  .p pv13 [pv2,pv3,pv5,pv2903], .c 3, .c 5, .p pv2 [pv2,pv3,pv37,pv3923], .c 3,
  .p pv13 [pv2,pv5,pv17,pv47,pv109], .c 853,
]
private theorem h0106c09 : checkBlock 870659 128 b0106c09 = true := by
  decide +kernel

private def b0106c10 : List Row := [
  .c 3, .p pv2 [pv2,pv239,pv911], .c 7, .c 3, .c 101, .c 5, .c 3, .p pv3 [pv2,pv29,pv1877],
  .p pv43 [pv2,pv3,pv5,pv9677], .c 3, .c 5, .c 197, .c 3, .c 19, .c 37, .c 3, .c 7, .c 53, .c 3,
  .p pv3 [pv2,pv108869], .c 5, .c 3, .c 307, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv127], .c 3,
  .c 389, .c 257, .c 3, .p pv3 [pv2,pv31,pv439], .c 19, .c 3, .p pv5 [pv2,pv7,pv62213], .c 5,
  .c 3, .c 7, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv10369], .c 3, .p pv3 [pv2,pv5,pv13,pv67],
  .c 7, .c 3, .c 31, .c 193, .c 3, .c 11, .c 5, .c 3, .c 61, .p pv2 [pv2,pv3,pv5,pv1613], .c 3,
  .c 5, .p pv3 [pv2,pv3,pv13,pv859], .c 3, .c 7, .c 23, .c 3, .p pv2 [pv2,pv19,pv73,pv157], .c 13,
  .c 3, .c 89, .c 5, .c 3, .c 421, .c 43, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv97,pv449],
  .c 17, .c 3, .c 67, .c 31, .c 3, .c 7, .c 5, .c 3, .c 11, .c 821, .c 3, .c 5, .c 7, .c 3, .c 13,
  .c 19, .c 3, .c 17, .c 71, .c 3, .p pv5 [pv2,pv23,pv29,pv653], .c 5, .c 3, .c 73, .c 311, .c 3,
  .c 5, .c 13, .c 3, .c 797, .c 11, .c 3, .c 41, .c 7, .c 3, .c 79, .c 5, .c 3, .c 569, .c 61,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv48397], .c 3, .c 191, .c 181, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv145193], .c 3, .p pv2 [pv2,pv31,pv14051], .c 5, .c 3, .c 13,
]
private theorem h0106c10 : checkBlock 870915 128 b0106c10 = true := by
  decide +kernel

private def b0106c11 : List Row := [
  .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv36299], .c 3, .p pv2 [pv2,pv5,pv43,pv1013], .c 137, .c 3,
  .c 233, .c 11, .c 3, .c 31, .c 5, .c 3, .c 7, .c 67, .c 3, .c 5, .c 19, .c 3, .c 11, .c 7, .c 3,
  .c 23, .c 211, .c 3, .c 43, .c 5, .c 3, .p pv2 [pv2,pv173,pv1259],
  .p pv3 [pv2,pv3,pv5,pv113,pv257], .c 3, .c 5, .c 109, .c 3, .c 7, .c 487, .c 3, .c 13,
  .p pv29 [pv2,pv3,pv7,pv2593], .c 3, .c 59, .c 5, .c 3, .p pv2 [pv2,pv367,pv1187], .c 223, .c 3,
  .c 5, .c 17, .c 3, .p pv11 [pv2,pv5,pv151,pv577], .c 13, .c 3, .c 11, .c 829, .c 3, .c 7, .c 5,
  .c 3, .p pv3 [pv2,pv11,pv9901], .c 41, .c 3, .c 5, .c 7, .c 3, .c 17,
  .p pv5 [pv2,pv3,pv19,pv7643], .c 3, .c 757, .c 23, .c 3, .c 37, .c 5, .c 3, .c 263, .c 11, .c 3,
  .c 5, .c 101, .c 3, .c 197, .c 47, .c 3, .p pv3 [pv2,pv108917], .c 7, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv31,pv7027], .c 13, .c 3, .c 5, .c 283, .c 3, .c 709, .c 29, .c 3, .c 7, .c 17,
  .c 3, .c 41, .c 5, .c 3, .c 31, .c 7, .c 3, .c 5, .c 11, .c 3, .c 139,
  .p pv7 [pv2,pv3,pv29,pv313], .c 3, .c 19, .c 89, .c 3, .c 13, .c 5, .c 3, .c 7, .c 631, .c 3,
  .c 5, .c 83, .c 3, .c 29, .c 7, .c 3,
]
private theorem h0106c11 : checkBlock 871171 128 b0106c11 = true := by
  decide +kernel

private def b0106c12 : List Row := [
  .c 47, .c 13, .c 3, .c 317, .c 5, .c 3, .p pv7 [pv2,pv43,pv10133], .c 31, .c 3, .c 5, .c 23,
  .c 3, .c 7, .c 11, .c 3, .c 137, .p pv3 [pv2,pv3,pv7,pv20749], .c 3, .p pv5 [pv2,pv435731],
  .c 5, .c 3, .c 67, .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv72623], .c 3, .c 13, .c 103, .c 3,
  .c 257, .c 59, .c 3, .c 7, .c 5, .c 3, .c 457, .c 149, .c 3, .c 5, .c 7, .c 3, .c 19,
  .p pv5 [pv2,pv3,pv36313], .c 3, .p pv2 [pv2,pv23,pv9473], .c 11, .c 3, .c 331, .c 5, .c 3,
  .c 101, .p pv19 [pv2,pv3,pv5,pv11,pv19,pv139], .c 3, .c 5, .c 29, .c 3, .c 11, .c 131, .c 3,
  .c 73, .c 7, .c 3, .p pv3 [pv2,pv11,pv619], .c 5, .c 3, .c 13, .c 163, .c 3, .c 5, .c 43, .c 3,
  .p pv2 [pv2,pv5,pv7,pv12451], .c 17, .c 3, .c 7, .c 409, .c 3, .c 83, .c 5, .c 3,
  .p pv2 [pv2,pv193,pv1129], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv31,pv71], .c 3, .c 127,
  .c 67, .c 3, .c 11, .c 37, .c 3, .p pv2 [pv2,pv7,pv4447], .c 5, .c 3, .c 7,
  .p pv17 [pv2,pv3,pv5,pv73,pv199], .c 3, .c 5, .c 31, .c 3, .c 23, .c 7, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv53,pv2741], .c 3, .p pv2 [pv2,pv97,pv4493], .c 5, .c 3, .p pv3 [pv2,pv27239],
  .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv36319], .c 3, .c 7, .c 13, .c 3, .c 71, .c 139, .c 3,
  .c 11, .c 5, .c 3, .p pv7 [pv2,pv435839], .p pv13 [pv2,pv3,pv5,pv227],
]
private theorem h0106c12 : checkBlock 871427 128 b0106c12 = true := by
  decide +kernel

private def b0106c13 : List Row := [
  .c 3, .c 5, .p pv3 [pv2,pv3,pv79,pv613], .c 3, .c 53, .c 73, .c 3, .c 241, .c 503, .c 3, .c 7,
  .c 5, .c 3, .c 17, .c 29, .c 3, .c 5, .c 7, .c 3, .c 839, .c 23, .c 3,
  .p pv5 [pv2,pv17,pv25639], .c 107, .c 3, .c 311, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 173,
  .c 3, .c 31, .c 499, .c 3, .c 37, .c 7, .c 3, .p pv2 [pv2,pv435881], .c 5, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv5,pv29059], .c 3, .c 5, .c 17, .c 3, .c 193, .c 11, .c 3, .c 7,
  .p pv17 [pv2,pv3,pv72649], .c 3, .c 13, .c 5, .c 3, .c 149, .c 7, .c 3, .c 5, .c 271, .c 3,
  .c 17, .c 31, .c 3, .p pv3 [pv2,pv11,pv9907], .c 13, .c 3, .p pv23 [pv2,pv7,pv62273], .c 5,
  .c 3, .c 7, .c 37, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv97,pv107], .c 3, .c 523, .c 7, .c 3,
  .c 577, .c 11, .c 3, .c 19, .c 5, .c 3, .c 661, .c 23, .c 3, .c 5, .p pv2 [pv2,pv3,pv48437],
  .c 3, .c 7, .c 61, .c 3, .c 181, .c 17, .c 3, .p pv2 [pv2,pv11,pv39631], .c 5, .c 3, .c 467,
  .c 19, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv8719], .c 53, .c 3, .c 23, .c 179, .c 3, .c 7,
  .c 5, .c 3, .p pv11 [pv2,pv547,pv797], .c 887, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv17,pv23,pv223], .c 89, .c 3, .c 11,
]
private theorem h0106c13 : checkBlock 871683 128 b0106c13 = true := by
  decide +kernel

private def b0106c14 : List Row := [
  .c 419, .c 3, .c 29, .c 5, .c 3, .c 13, .c 71, .c 3, .c 5, .p pv2 [pv2,pv3,pv53,pv457], .c 3,
  .c 59, .p pv2 [pv2,pv3,pv7,pv13,pv1597], .c 3, .c 19, .c 7, .c 3, .p pv2 [pv2,pv29,pv7517],
  .c 5, .c 3, .c 37, .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv19,pv7649], .c 3, .c 47,
  .p pv7 [pv2,pv3,pv11,pv367], .c 3, .c 7, .c 23, .c 3, .c 11, .c 5, .c 3, .c 53, .c 7, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv37,pv491], .c 3, .c 113, .p pv3 [pv2,pv3,pv23,pv71,pv89], .c 3, .c 13,
  .c 41, .c 3, .p pv3 [pv2,pv7,pv17,pv229], .c 5, .c 3, .c 7, .p pv41 [pv2,pv3,pv5,pv13,pv43],
  .c 3, .c 5, .c 11, .c 3, .c 601, .c 7, .c 3, .p pv3 [pv2,pv61,pv1787], .c 29, .c 3, .c 211,
  .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv41,pv709], .c 3, .c 5, .p pv2 [pv2,pv3,pv72673], .c 3,
  .c 7, .c 17, .c 3, .c 563, .p pv17 [pv2,pv3,pv7,pv29,pv179], .c 3, .c 71, .c 5, .c 3,
  .p pv2 [pv2,pv269,pv1621], .c 103, .c 3, .c 5, .p pv2 [pv2,pv3,pv191,pv761], .c 3, .c 41, .c 11,
  .c 3, .c 17, .c 19, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv13627], .c 13, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv43607], .p pv19 [pv2,pv3,pv137,pv1061], .c 3, .c 719,
  .p pv2 [pv2,pv3,pv72679], .c 3, .c 223, .c 5, .c 3, .p pv7 [pv2,pv7,pv62297],
  .p pv7 [pv2,pv3,pv5,pv23,pv79], .c 3, .c 5, .c 193, .c 3, .c 619, .p pv5 [pv2,pv3,pv7,pv3461],
  .c 3, .p pv3 [pv2,pv19,pv151], .c 7, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv218047], .c 683,
  .c 3,
]
private theorem h0106c14 : checkBlock 871939 128 b0106c14 = true := by
  decide +kernel

private def b0106c15 : List Row := [
  .c 5, .c 59, .c 3, .c 11, .p pv2 [pv2,pv3,pv17,pv503], .c 3, .c 7, .c 13, .c 3, .c 163, .c 5,
  .c 3, .c 17, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv47,pv1031], .c 3, .p pv17 [pv2,pv5,pv87223],
  .c 19, .c 3, .p pv2 [pv2,pv17,pv101,pv127], .c 61, .c 3, .p pv2 [pv2,pv7,pv62303], .c 5, .c 3,
  .c 7, .p pv29 [pv2,pv3,pv5,pv1163], .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv11,pv59], .c 3, .c 13,
  .c 7, .c 3, .c 11, .p pv7 [pv2,pv3,pv72689], .c 3, .c 47, .c 5, .c 3, .c 137,
  .p pv13 [pv2,pv3,pv5,pv2423], .c 3, .c 5, .c 13, .c 3, .c 7, .c 439, .c 3, .c 191, .c 613, .c 3,
  .c 593, .c 5, .c 3, .c 19, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv41,pv197], .c 3, .c 17,
  .p pv2 [pv2,pv3,pv11,pv13217], .c 3, .c 53, .c 131, .c 3, .c 7, .c 5, .c 3, .c 13, .c 43, .c 3,
  .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv73,pv239], .p pv5 [pv2,pv3,pv13,pv233], .c 3, .c 41, .c 367,
  .c 3, .c 127, .c 5, .c 3, .p pv3 [pv2,pv7,pv7789], .c 31, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv53,pv823], .p pv3 [pv2,pv3,pv7,pv20771], .c 3, .p pv2 [pv2,pv37,pv11789],
  .c 7, .c 3, .p pv3 [pv2,pv109049], .c 5, .c 3, .c 11, .c 641, .c 3, .c 5, .c 29, .c 3,
  .p pv17 [pv2,pv5,pv7,pv11,pv103], .c 23, .c 3, .c 7, .p pv3 [pv2,pv3,pv97,pv1499], .c 3, .c 17,
  .c 5, .c 3, .p pv2 [pv2,pv218107], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv23,pv29,pv109], .c 3,
  .p pv3 [pv2,pv5,pv17,pv1283], .c 11, .c 3, .c 373, .c 157,
]
private theorem h0106c15 : checkBlock 872195 128 b0106c15 = true := by
  decide +kernel

private def b0106c16 : List Row := [
  .c 3, .p pv2 [pv2,pv7,pv31159], .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 89, .c 3,
  .p pv13 [pv2,pv5,pv43,pv2029], .c 7, .c 3, .p pv2 [pv2,pv11,pv79,pv251],
  .p pv3 [pv2,pv3,pv107,pv151], .c 3, .c 61, .c 5, .c 3, .c 283, .c 17, .c 3, .c 5, .c 37, .c 3,
  .c 7, .c 139, .c 3, .c 491, .c 11, .c 3, .c 43, .c 5, .c 3, .c 71, .c 13, .c 3, .c 5, .c 389,
  .c 3, .c 11, .p pv2 [pv2,pv3,pv2693], .c 3, .c 19, .c 53, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv218137], .c 23, .c 3, .c 5, .c 7, .c 3, .p pv23 [pv2,pv5,pv13,pv839],
  .p pv2 [pv2,pv3,pv41,pv3547], .c 3, .p pv5 [pv2,pv436283], .c 73, .c 3, .c 13, .c 5, .c 3,
  .c 83, .c 29, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv13,pv113], .c 3, .c 131, .c 17, .c 3, .c 11,
  .c 7, .c 3, .c 41, .c 5, .c 3, .p pv3 [pv2,pv11,pv37,pv67], .p pv2 [pv2,pv3,pv5,pv17,pv29,pv59],
  .c 3, .c 5, .c 127, .c 3, .p pv2 [pv2,pv5,pv7,pv23,pv271], .p pv11 [pv2,pv3,pv48479], .c 3,
  .c 7, .c 151, .c 3, .c 541, .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .p pv17 [pv2,pv3,pv145441],
  .c 3, .c 13, .c 677, .c 3, .p pv3 [pv2,pv54541], .p pv2 [pv2,pv3,pv48481], .c 3, .c 11, .c 5,
  .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv19,pv1531], .c 3, .c 5, .c 13, .c 3, .c 31, .c 7, .c 3,
  .p pv5 [pv2,pv436343], .c 19, .c 3, .c 149, .c 5, .c 3, .c 113, .c 317, .c 3, .c 5,
]
private theorem h0106c16 : checkBlock 872451 128 b0106c16 = true := by
  decide +kernel

private def b0106c17 : List Row := [
  .c 11, .c 3, .c 7, .c 79, .c 3, .c 773, .c 37, .c 3, .c 821, .c 5, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv5,pv9697], .c 3, .c 5, .p pv41 [pv2,pv3,pv9091], .c 3, .c 101, .c 31, .c 3,
  .p pv2 [pv2,pv7,pv17,pv19,pv193], .p pv2 [pv2,pv3,pv8081], .c 3, .c 7, .c 5, .c 3, .c 739,
  .p pv11 [pv2,pv3,pv5,pv7,pv1039], .c 3, .c 5, .c 7, .c 3, .c 43, .c 11, .c 3, .c 419, .c 709,
  .c 3, .c 787, .c 5, .c 3, .p pv2 [pv2,pv7,pv61,pv73], .p pv3 [pv2,pv3,pv5,pv47,pv619], .c 3,
  .c 5, .c 17, .c 3, .c 307, .c 19, .c 3, .c 13, .c 7, .c 3, .c 29, .c 5, .c 3, .c 557, .c 757,
  .c 3, .c 5, .c 23, .c 3, .c 17, .c 13, .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv29,pv101,pv149],
  .c 5, .c 3, .c 41, .c 7, .c 3, .c 5, .c 43, .c 3, .c 11, .p pv3 [pv2,pv3,pv145477], .c 3, .c 31,
  .c 587, .c 3, .c 23, .c 5, .c 3, .c 7, .c 673, .c 3, .c 5, .c 523, .c 3, .c 271, .c 7, .c 3,
  .c 263, .c 17, .c 3, .c 97, .c 5, .c 3, .c 167, .c 13, .c 3, .c 5, .c 19, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv145487], .c 3, .c 11, .c 29, .c 3, .c 17, .c 5, .c 3, .c 193, .c 37, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv48497], .c 3, .p pv59 [pv2,pv5,pv13,pv17,pv79],
  .p pv5 [pv2,pv3,pv36373], .c 3, .c 313, .p pv3 [pv2,pv3,pv29,pv173], .c 3,
]
private theorem h0106c17 : checkBlock 872707 128 b0106c17 = true := by
  decide +kernel

private def b0106c18 : List Row := [
  .c 7, .c 5, .c 3, .c 353, .c 11, .c 3, .c 5, .c 7, .c 3, .c 109, .c 179, .c 3, .c 29, .c 13,
  .c 3, .c 11, .c 5, .c 3, .p pv7 [pv2,pv7,pv127,pv491], .c 17, .c 3, .c 5, .c 73, .c 3, .c 23,
  .c 41, .c 3, .p pv5 [pv2,pv29,pv53,pv71], .c 7, .c 3, .c 59, .c 5, .c 3, .c 43, .c 19, .c 3,
  .c 5, .c 11, .c 3, .c 13, .p pv5 [pv2,pv3,pv227,pv641], .c 3, .c 7,
  .p pv19 [pv2,pv3,pv11,pv3307], .c 3, .c 31, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 13, .c 3,
  .c 881, .p pv7 [pv2,pv3,pv43,pv47], .c 3, .c 67, .p pv3 [pv2,pv3,pv145513], .c 3,
  .p pv2 [pv2,pv7,pv59,pv151], .c 5, .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv89,pv109], .c 3, .c 5,
  .c 97, .c 3, .c 137, .c 7, .c 3, .c 19, .p pv2 [pv2,pv3,pv79,pv307], .c 3,
  .p pv3 [pv2,pv109139], .c 5, .c 3, .c 13, .p pv11 [pv2,pv3,pv5,pv17,pv107], .c 3, .c 5, .c 727,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv13,pv29,pv193], .c 3, .c 17, .p pv2 [pv2,pv3,pv7,pv20789], .c 3,
  .c 241, .c 5, .c 3, .c 23, .c 113, .c 3, .c 5, .p pv5 [pv2,pv3,pv72763], .c 3, .c 29, .c 37,
  .c 3, .c 337, .c 11, .c 3, .c 7, .c 5, .c 3, .c 89, .c 661, .c 3, .c 5, .c 7, .c 3, .c 11,
  .c 373, .c 3, .c 13, .c 109, .c 3, .c 823, .c 5, .c 3, .p pv3 [pv2,pv7,pv31,pv503], .c 67, .c 3,
  .c 5, .c 479,
]
private theorem h0106c18 : checkBlock 872963 128 b0106c18 = true := by
  decide +kernel

private def b0106c19 : List Row := [
  .c 3, .c 19, .c 13, .c 3, .c 107, .c 7, .c 3, .c 151, .c 5, .c 3, .c 17, .c 23, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv101,pv131], .c 3, .p pv2 [pv2,pv5,pv7,pv499], .c 601, .c 3, .c 7, .c 19,
  .c 3, .p pv5 [pv2,pv13,pv33587], .c 5, .c 3, .c 227, .c 7, .c 3, .c 5, .c 29, .c 3, .c 53,
  .c 857, .c 3, .c 23, .c 149, .c 3, .p pv2 [pv2,pv7,pv31189], .c 5, .c 3, .c 7, .c 11, .c 3,
  .c 5, .c 17, .c 3, .c 37, .c 7, .c 3, .p pv2 [pv2,pv19,pv11491], .p pv3 [pv2,pv3,pv59,pv2467],
  .c 3, .c 11, .c 5, .c 3, .c 211, .p pv2 [pv2,pv3,pv5,pv43,pv677], .c 3, .c 5, .c 61, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv599], .c 3, .c 101, .p pv2 [pv2,pv3,pv7,pv37,pv281], .c 3, .c 13, .c 5, .c 3,
  .p pv7 [pv2,pv17,pv1511], .c 433, .c 3, .c 5, .c 11, .c 3, .c 71, .c 19, .c 3, .c 59, .c 13,
  .c 3, .c 7, .c 5, .c 3, .c 11, .c 157, .c 3, .c 5, .c 7, .c 3, .c 47,
  .p pv2 [pv2,pv3,pv23,pv6329], .c 3, .p pv5 [pv2,pv229,pv1907], .c 17, .c 3, .c 751, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv13,pv4799], .p pv2 [pv2,pv3,pv5,pv14557], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv17,pv8563], .c 3, .c 13, .c 11, .c 3, .p pv2 [pv2,pv59,pv3701], .c 7, .c 3,
  .c 17, .c 5, .c 3, .c 19, .c 29, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv7,pv17,pv367],
  .p pv5 [pv2,pv3,pv145577], .c 3, .c 7, .p pv2 [pv2,pv3,pv19,pv1277], .c 3, .c 607,
]
private theorem h0106c19 : checkBlock 873219 128 b0106c19 = true := by
  decide +kernel

private def b0106c20 : List Row := [
  .c 5, .c 3, .c 67, .c 7, .c 3, .c 5, .c 19, .c 3, .c 223, .c 53, .c 3,
  .p pv3 [pv2,pv13,pv37,pv227], .c 11, .c 3, .c 79, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 23,
  .c 3, .c 11, .c 7, .c 3, .p pv5 [pv2,pv109,pv4007], .p pv13 [pv2,pv3,pv17,pv2141], .c 3, .c 37,
  .c 5, .c 3, .p pv7 [pv2,pv29,pv15061], .p pv31 [pv2,pv3,pv5,pv23,pv211], .c 3, .c 5, .c 349,
  .c 3, .c 7, .p pv5 [pv2,pv3,pv18199], .c 3, .c 683, .c 547, .c 3, .c 19, .c 5, .c 3,
  .p pv3 [pv2,pv27299], .p pv3 [pv2,pv3,pv5,pv37,pv787], .c 3, .c 5, .c 167, .c 3, .c 61, .c 313,
  .c 3, .c 11, .c 47, .c 3, .c 7, .c 5, .c 3, .c 53, .c 19, .c 3, .c 5, .c 7, .c 3, .c 31, .c 13,
  .c 3, .p pv3 [pv2,pv54601], .p pv3 [pv2,pv3,pv145603], .c 3, .c 383, .c 5, .c 3, .c 281, .c 11,
  .c 3, .c 5, .c 431, .c 3, .p pv3 [pv2,pv5,pv21841], .p pv2 [pv2,pv3,pv7,pv11,pv31,pv61], .c 3,
  .c 17, .c 7, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv19,pv83,pv277], .c 79, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv5393], .c 3, .p pv13 [pv2,pv5,pv7,pv1783], .c 31, .c 3, .c 7, .c 97, .c 3,
  .c 29, .c 5, .c 3, .p pv3 [pv2,pv109211], .c 7, .c 3, .c 5, .c 11, .c 3, .c 23, .c 61, .c 3,
  .p pv2 [pv2,pv436853], .p pv13 [pv2,pv3,pv11,pv6619], .c 3, .c 89, .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv809], .c 3, .c 5, .p pv7 [pv2,pv3,pv7,pv71,pv293], .c 3,
]
private theorem h0106c20 : checkBlock 873475 128 b0106c20 = true := by
  decide +kernel

private def b0106c21 : List Row := [
  .c 59, .c 7, .c 3, .c 73, .p pv2 [pv2,pv3,pv48541], .c 3, .c 13, .c 5, .c 3, .c 17, .c 41, .c 3,
  .c 5, .c 467, .c 3, .c 7, .c 11, .c 3, .p pv5 [pv2,pv17,pv31,pv829], .c 13, .c 3,
  .p pv2 [pv2,pv19,pv11497], .c 5, .c 3, .c 401, .p pv7 [pv2,pv3,pv5,pv14563], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv137,pv1063], .c 3, .c 19, .c 23, .c 3, .c 31, .c 29, .c 3, .c 7, .c 5, .c 3,
  .c 199, .c 53, .c 3, .c 5, .c 7, .c 3, .c 13, .c 173, .c 3, .c 367, .c 11, .c 3, .c 41, .c 5,
  .c 3, .c 23, .c 337, .c 3, .c 5, .c 13, .c 3, .c 11, .c 109, .c 3, .c 29, .c 7, .c 3,
  .p pv5 [pv2,pv11,pv23,pv157], .c 5, .c 3, .c 107, .c 47, .c 3, .c 5, .p pv23 [pv2,pv3,pv72823],
  .c 3, .c 67, .c 73, .c 3, .c 7, .c 43, .c 3, .c 139, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 83,
  .c 3, .c 167, .p pv11 [pv2,pv3,pv13,pv2801], .c 3, .c 11, .c 17, .c 3, .c 137, .c 5, .c 3, .c 7,
  .c 23, .c 3, .c 5, .c 223, .c 3, .c 599, .c 7, .c 3, .c 61, .c 263, .c 3, .c 17, .c 5, .c 3,
  .p pv7 [pv2,pv436979], .c 11, .c 3, .c 5, .c 59, .c 3, .c 7, .c 29, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv7,pv20809], .c 3, .c 11, .c 5,
]
private theorem h0106c21 : checkBlock 873731 128 b0106c21 = true := by
  decide +kernel

private def b0106c22 : List Row := [
  .c 3, .p pv2 [pv2,pv151,pv1447], .p pv31 [pv2,pv3,pv5,pv13,pv83], .c 3, .c 5, .c 41, .c 3,
  .p pv11 [pv2,pv5,pv19,pv23], .c 13, .c 3, .c 677, .p pv7 [pv2,pv3,pv61,pv199], .c 3, .c 7, .c 5,
  .c 3, .c 19, .c 17, .c 3, .c 5, .c 7, .c 3, .c 29, .c 409, .c 3, .p pv2 [pv2,pv218509], .c 443,
  .c 3, .c 587, .c 5, .c 3, .c 11, .c 37, .c 3, .c 5, .c 19, .c 3, .c 43,
  .p pv3 [pv2,pv3,pv7,pv991], .c 3, .c 97, .c 7, .c 3, .c 83, .c 5, .c 3, .c 41, .c 13, .c 3,
  .c 5, .p pv11 [pv2,pv3,pv145681], .c 3, .p pv2 [pv2,pv5,pv7,pv12487], .c 11, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv16187], .c 3, .p pv5 [pv2,pv73,pv5987], .c 5, .c 3, .p pv2 [pv2,pv218527],
  .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv24281], .c 3, .p pv3 [pv2,pv5,pv13,pv41], .c 17, .c 3,
  .p pv5 [pv2,pv11,pv39733], .c 53, .c 3, .c 13, .c 5, .c 3, .c 7, .c 127, .c 3, .c 5, .c 29,
  .c 3, .p pv11 [pv2,pv5,pv17483], .c 7, .c 3, .c 17, .c 11, .c 3, .c 131, .c 5, .c 3, .c 31,
  .c 19, .c 3, .c 5, .c 227, .c 3, .c 7, .c 149, .c 3, .c 283, .c 929, .c 3,
  .p pv3 [pv2,pv11,pv4967], .c 5, .c 3, .c 37, .c 571, .c 3, .c 5, .c 23, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv263,pv277], .c 3, .p pv3 [pv2,pv7,pv67,pv233], .c 863, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv19,pv11503], .c 31, .c 3, .c 5, .c 7, .c 3, .c 457,
]
private theorem h0106c22 : checkBlock 873987 128 b0106c22 = true := by
  decide +kernel

private def b0106c23 : List Row := [
  .c 41, .c 3, .c 11, .p pv11 [pv2,pv3,pv73,pv499], .c 3, .c 23, .c 5, .c 3, .c 17, .c 97, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv19,pv7669], .c 3, .p pv13 [pv2,pv5,pv87427], .c 37, .c 3,
  .p pv2 [pv2,pv13,pv17,pv23,pv43], .c 7, .c 3, .c 67, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5,
  .c 107, .c 3, .p pv3 [pv2,pv5,pv7,pv1249], .p pv3 [pv2,pv3,pv11,pv13,pv1019], .c 3, .c 7,
  .c 797, .c 3, .c 11, .c 5, .c 3, .c 43, .c 7, .c 3, .c 5, .c 17, .c 3,
  .p pv23 [pv2,pv5,pv87433], .c 157, .c 3, .p pv3 [pv2,pv89,pv307], .c 563, .c 3,
  .p pv5 [pv2,pv7,pv19,pv173], .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv29,pv67], .c 3, .c 5,
  .c 11, .c 3, .c 17, .c 7, .c 3, .c 13, .c 877, .c 3, .p pv2 [pv2,pv79,pv2767], .c 5, .c 3,
  .c 11, .c 353, .c 3, .c 5, .p pv3 [pv2,pv3,pv31,pv1567], .c 3, .c 7, .c 13, .c 3,
  .p pv2 [pv2,pv218599], .c 19, .c 3, .p pv2 [pv2,pv437201], .c 5, .c 3, .p pv3 [pv2,pv29,pv3769],
  .c 181, .c 3, .c 5, .c 31, .c 3, .c 37, .c 11, .c 3, .p pv2 [pv2,pv7,pv62459], .c 17, .c 3,
  .c 7, .c 5, .c 3, .c 59, .c 151, .c 3, .c 5, .c 7, .c 3, .c 79, .c 419, .c 3,
  .p pv3 [pv2,pv11,pv19,pv523], .p pv3 [pv2,pv3,pv13,pv37,pv101], .c 3, .c 17, .c 5, .c 3, .c 733,
  .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv2699], .c 3, .c 149, .c 23, .c 3, .p pv5 [pv2,pv437243],
  .c 7, .c 3, .c 659, .c 5, .c 3,
]
private theorem h0106c23 : checkBlock 874243 128 b0106c23 = true := by
  decide +kernel

private def b0106c24 : List Row := [
  .c 431, .c 239, .c 3, .c 5, .c 71, .c 3, .c 11, .c 19, .c 3, .c 7, .c 269, .c 3, .c 13, .c 5,
  .c 3, .c 23, .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv13,pv2803], .c 3, .c 31,
  .p pv5 [pv2,pv3,pv145757], .c 3, .p pv2 [pv2,pv437273], .c 13, .c 3, .c 29, .c 5, .c 3, .c 7,
  .c 367, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv11,pv631], .c 3, .c 41, .c 7, .c 3, .c 11, .c 167,
  .c 3, .p pv5 [pv2,pv17,pv29,pv887], .c 5, .c 3, .c 19, .c 397, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv72883], .c 3, .c 7, .c 31, .c 3, .c 463, .c 79, .c 3, .c 73, .c 5, .c 3,
  .p pv2 [pv2,pv61,pv67,pv107], .c 11, .c 3, .c 5, .c 13, .c 3, .c 227, .c 17, .c 3,
  .p pv2 [pv2,pv7,pv31237], .p pv3 [pv2,pv3,pv5399], .c 3, .c 7, .c 5, .c 3, .c 71,
  .p pv3 [pv2,pv3,pv5,pv7,pv17], .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv101,pv433], .c 43,
  .c 3, .c 17, .c 29, .c 3, .p pv3 [pv2,pv54667], .c 5, .c 3, .c 13,
  .p pv29 [pv2,pv3,pv5,pv37,pv197], .c 3, .c 5, .c 11, .c 3, .c 467,
  .p pv11 [pv2,pv3,pv7,pv13,pv89], .c 3, .p pv3 [pv2,pv31,pv3527], .c 7, .c 3, .c 19, .c 5, .c 3,
  .c 11, .p pv3 [pv2,pv3,pv5,pv9719], .c 3, .c 5, .c 37, .c 3, .p pv19 [pv2,pv5,pv7,pv11,pv71],
  .p pv2 [pv2,pv3,pv19,pv7673], .c 3, .c 7, .p pv13 [pv2,pv3,pv12149], .c 3, .c 113, .c 5, .c 3,
  .p pv2 [pv2,pv263,pv1663], .c 7, .c 3, .c 5, .c 499, .c 3, .c 613, .c 11,
]
private theorem h0106c24 : checkBlock 874499 128 b0106c24 = true := by
  decide +kernel

private def b0106c25 : List Row := [
  .c 3, .c 13, .c 23, .c 3, .p pv2 [pv2,pv7,pv62483], .c 5, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv5,pv13,pv2243], .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv41,pv127], .c 3, .c 89,
  .c 7, .c 3, .c 347, .c 31, .c 3, .c 59, .c 5, .c 3, .p pv7 [pv2,pv19,pv23021], .c 61, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv211,pv691], .c 3, .c 7, .p pv2 [pv2,pv3,pv72901], .c 3, .c 19, .c 11,
  .c 3, .p pv5 [pv2,pv13,pv33647], .c 5, .c 3, .c 223, .p pv3 [pv2,pv3,pv5,pv11,pv241], .c 3,
  .c 5, .c 17, .c 3, .c 11, .c 29, .c 3, .p pv5 [pv2,pv7,pv79,pv113], .c 823, .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv41,pv47,pv227], .c 13, .c 3, .c 5, .c 7, .c 3, .c 17,
  .p pv5 [pv2,pv3,pv29,pv419], .c 3, .c 197, .p pv13 [pv2,pv3,pv43,pv3391], .c 3, .c 359, .c 5,
  .c 3, .p pv3 [pv2,pv7,pv17,pv919], .p pv2 [pv2,pv3,pv5,pv9721], .c 3, .c 5, .c 23, .c 3, .c 29,
  .c 83, .c 3, .c 11, .c 7, .c 3, .c 13, .c 5, .c 3, .p pv11 [pv2,pv11,pv39769], .c 43, .c 3,
  .c 5, .c 439, .c 3, .c 19, .c 71, .c 3, .c 7, .c 13, .c 3, .c 23, .c 5, .c 3, .c 131, .c 7,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv4289], .c 3, .c 157, .c 101, .c 3, .p pv7 [pv2,pv23,pv827],
  .c 19, .c 3, .c 11, .c 5, .c 3, .c 7, .c 41, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv83,pv251], .c 3,
  .c 13, .c 7, .c 3, .c 857, .c 47, .c 3, .c 199, .c 5, .c 3, .c 229,
]
private theorem h0106c25 : checkBlock 874755 128 b0106c25 = true := by
  decide +kernel

private def b0106c26 : List Row := [
  .p pv2 [pv2,pv3,pv5,pv29167], .c 3, .c 5, .c 11, .c 3, .c 7, .c 719, .c 3,
  .p pv2 [pv2,pv19,pv23027], .c 59, .c 3, .p pv3 [pv2,pv109379], .c 5, .c 3, .c 11, .c 17, .c 3,
  .c 5, .c 557, .c 3, .c 73, .c 883, .c 3, .c 269, .c 271, .c 3, .c 7, .c 5, .c 3, .c 13, .c 241,
  .c 3, .c 5, .c 7, .c 3, .c 23, .c 11, .c 3, .c 37, .p pv7 [pv2,pv3,pv59,pv103], .c 3, .c 43,
  .c 5, .c 3, .c 31, .c 449, .c 3, .c 5, .p pv3 [pv2,pv3,pv61,pv797], .c 3, .c 379,
  .p pv5 [pv2,pv3,pv7,pv5209], .c 3, .p pv2 [pv2,pv11,pv19889], .c 7, .c 3, .c 643, .c 5, .c 3,
  .p pv3 [pv2,pv109391], .c 179, .c 3, .c 5, .c 89, .c 3, .p pv3 [pv2,pv5,pv7,pv19,pv47], .c 17,
  .c 3, .c 7, .c 11, .c 3, .c 107, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 61, .c 3, .c 11, .c 13,
  .c 3, .c 17, .c 43, .c 3, .p pv7 [pv2,pv7,pv11,pv5683], .c 5, .c 3, .c 7, .c 29, .c 3, .c 5,
  .c 19, .c 3, .p pv7 [pv2,pv5,pv547], .c 7, .c 3, .c 173, .p pv19 [pv2,pv3,pv36467], .c 3,
  .p pv2 [pv2,pv13,pv16831], .c 5, .c 3, .c 23, .c 67, .c 3, .c 5, .c 41, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv1013], .c 3, .c 11, .p pv3 [pv2,pv3,pv7,pv13,pv229], .c 3,
  .p pv2 [pv2,pv23,pv53,pv359], .c 5, .c 3, .c 29, .c 13, .c 3, .c 5, .c 307, .c 3,
  .p pv2 [pv2,pv5,pv107,pv409], .p pv3 [pv2,pv3,pv17,pv8581], .c 3,
]
private theorem h0106c26 : checkBlock 875011 128 b0106c26 = true := by
  decide +kernel

private def b0106c27 : List Row := [
  .p pv2 [pv2,pv7,pv101,pv619], .p pv2 [pv2,pv3,pv41,pv593], .c 3, .c 7, .c 5, .c 3, .c 17, .c 11,
  .c 3, .c 5, .c 7, .c 3, .c 419, .c 137, .c 3, .p pv3 [pv2,pv17,pv1609],
  .p pv2 [pv2,pv3,pv113,pv1291], .c 3, .c 11, .c 5, .c 3, .c 37, .c 19, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv13,pv31,pv181], .c 3, .c 859, .p pv2 [pv2,pv3,pv7,pv6947], .c 3,
  .p pv5 [pv2,pv269,pv1627], .c 7, .c 3, .p pv2 [pv2,pv218833], .c 5, .c 3,
  .p pv2 [pv2,pv541,pv809], .p pv2 [pv2,pv3,pv5,pv1621], .c 3, .c 5, .c 11, .c 3, .c 43, .c 191,
  .c 3, .c 7, .c 71, .c 3, .p pv2 [pv2,pv437681], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv6079], .c 3, .c 13, .c 37, .c 3, .c 19, .p pv13 [pv2,pv3,pv72949], .c 3,
  .p pv3 [pv2,pv7,pv977], .c 5, .c 3, .c 7, .c 53, .c 3, .c 5, .c 13, .c 3, .c 61, .c 7, .c 3,
  .p pv3 [pv2,pv73,pv1499], .p pv2 [pv2,pv3,pv145903], .c 3, .c 29, .c 5, .c 3,
  .p pv2 [pv2,pv218857], .c 373, .c 3, .c 5, .c 43, .c 3, .c 7, .p pv3 [pv2,pv3,pv59,pv2473],
  .c 3, .p pv11 [pv2,pv11,pv13,pv3061], .c 17, .c 3, .c 491, .c 5, .c 3, .c 13, .c 313, .c 3,
  .c 5, .c 229, .c 3, .c 31, .c 41, .c 3, .p pv2 [pv2,pv7,pv31267], .c 11, .c 3, .c 7, .c 5, .c 3,
  .c 67, .p pv3 [pv2,pv3,pv5,pv7,pv11,pv379], .c 3, .c 5, .c 7, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv31,pv523], .c 3, .c 53, .p pv11 [pv2,pv3,pv72959], .c 3,
  .p pv5 [pv2,pv11,pv9949], .c 5, .c 3, .p pv7 [pv2,pv7,pv23,pv2719], .p pv29 [pv2,pv3,pv5,pv19],
]
private theorem h0106c27 : checkBlock 875267 128 b0106c27 = true := by
  decide +kernel

private def b0106c28 : List Row := [
  .c 3, .c 5, .c 263, .c 3, .c 37, .c 31, .c 3, .c 13, .c 7, .c 3, .p pv5 [pv2,pv437771], .c 5,
  .c 3, .c 701, .c 17, .c 3, .c 5, .c 79, .c 3, .c 139, .c 13, .c 3, .c 7, .c 101, .c 3, .c 673,
  .c 5, .c 3, .p pv2 [pv2,pv11,pv39799], .c 7, .c 3, .c 5, .c 23, .c 3, .p pv17 [pv2,pv5,pv87559],
  .p pv5 [pv2,pv3,pv12161], .c 3, .c 29, .c 257, .c 3, .c 103, .c 5, .c 3, .c 7, .c 11, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv7,pv1303], .c 3, .p pv2 [pv2,pv5,pv43781], .c 7, .c 3,
  .p pv2 [pv2,pv29,pv31,pv487], .p pv7 [pv2,pv3,pv13,pv1871], .c 3, .c 11, .c 5, .c 3, .c 389,
  .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv48647], .c 3, .c 7, .c 17, .c 3, .c 31,
  .p pv2 [pv2,pv3,pv7,pv20849], .c 3, .p pv5 [pv2,pv367,pv1193], .c 5, .c 3, .c 409, .c 89, .c 3,
  .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv13,pv421], .p pv3 [pv2,pv3,pv48649], .c 3, .c 17,
  .p pv7 [pv2,pv3,pv11,pv31,pv107], .c 3, .c 7, .c 5, .c 3, .c 11,
  .p pv17 [pv2,pv3,pv5,pv7,pv139], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv11,pv19,pv419],
  .c 29, .c 3, .p pv2 [pv2,pv37,pv61,pv97], .c 13, .c 3, .c 503, .c 5, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv5,pv29191], .c 3, .c 5, .c 59, .c 3, .p pv2 [pv2,pv5,pv43787], .c 11, .c 3,
  .c 547, .c 7, .c 3, .c 37, .c 5, .c 3, .p pv11 [pv2,pv13,pv2591],
  .p pv11 [pv2,pv3,pv5,pv41,pv89], .c 3, .c 5, .c 19, .c 3, .c 13, .p pv5 [pv2,pv3,pv17,pv53],
  .c 3, .c 7,
]
private theorem h0106c28 : checkBlock 875523 128 b0106c28 = true := by
  decide +kernel

private def b0106c29 : List Row := [
  .p pv2 [pv2,pv3,pv145963], .c 3, .p pv5 [pv2,pv397,pv1103], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5,
  .c 13, .c 3, .c 41, .p pv13 [pv2,pv3,pv145967], .c 3, .c 919, .c 11, .c 3, .c 97, .c 5, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv5,pv11,pv1327], .c 3, .c 5, .c 37, .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv13,pv16843], .c 139, .c 3, .c 19, .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv5839],
  .c 3, .c 5, .c 17, .c 3, .c 7, .c 23, .c 3, .c 43, .c 379, .c 3, .c 79, .c 5, .c 3, .c 541,
  .c 19, .c 3, .c 5, .c 29, .c 3, .c 17, .p pv2 [pv2,pv3,pv47,pv1553], .c 3, .c 11, .c 61, .c 3,
  .c 7, .c 5, .c 3, .c 23, .c 761, .c 3, .c 5, .c 7, .c 3, .c 383, .p pv3 [pv2,pv3,pv145987],
  .c 3, .c 13, .p pv11 [pv2,pv3,pv36497], .c 3, .p pv3 [pv2,pv23,pv9521], .c 5, .c 3, .c 47,
  .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv145991], .c 3, .c 151, .c 13, .c 3, .c 19, .c 7, .c 3,
  .c 11, .c 5, .c 3, .p pv3 [pv2,pv13687], .c 149, .c 3, .c 5, .c 613, .c 3,
  .p pv3 [pv2,pv5,pv7,pv6257], .p pv3 [pv2,pv3,pv83,pv1759], .c 3, .c 7, .c 509, .c 3, .c 17,
  .c 5, .c 3, .c 449, .c 7, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv17,pv5153],
  .p pv2 [pv2,pv3,pv37,pv1973], .c 3, .p pv3 [pv2,pv54751], .p pv3 [pv2,pv3,pv11,pv13,pv1021],
  .c 3, .p pv5 [pv2,pv7,pv1277], .c 5, .c 3, .c 7, .c 13, .c 3,
]
private theorem h0106c29 : checkBlock 875779 128 b0106c29 = true := by
  decide +kernel

private def b0106c30 : List Row := [
  .c 5, .c 53, .c 3, .p pv3 [pv2,pv5,pv11,pv181], .c 7, .c 3, .c 23, .c 37, .c 3, .c 263, .c 5,
  .c 3, .c 197, .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv146011], .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv219019], .p pv23 [pv2,pv3,pv7,pv17,pv409], .c 3, .c 13, .c 5, .c 3, .c 113, .c 31,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv13], .c 3, .c 421, .p pv3 [pv2,pv3,pv151,pv967], .c 3,
  .p pv2 [pv2,pv7,pv11,pv5689], .c 13, .c 3, .c 7, .c 5, .c 3, .c 29,
  .p pv29 [pv2,pv3,pv5,pv7,pv149], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv87613], .c 269, .c 3,
  .p pv3 [pv2,pv109517], .c 11, .c 3, .c 53, .c 5, .c 3, .p pv11 [pv2,pv7,pv13,pv29,pv83], .c 277,
  .c 3, .c 5, .c 331, .c 3, .c 11, .c 17, .c 3, .c 223, .c 7, .c 3, .c 127, .c 5, .c 3, .c 397,
  .p pv41 [pv2,pv3,pv5,pv17,pv859], .c 3, .c 5, .c 13, .c 3, .p pv7 [pv2,pv5,pv7,pv12517],
  .p pv5 [pv2,pv3,pv9127], .c 3, .c 7, .p pv3 [pv2,pv3,pv146033], .c 3, .p pv2 [pv2,pv113,pv3877],
  .c 5, .c 3, .c 59, .c 7, .c 3, .c 5, .c 157, .c 3, .c 47, .c 19, .c 3, .c 11,
  .p pv23 [pv2,pv3,pv73019], .c 3, .p pv3 [pv2,pv7,pv15647], .c 5, .c 3, .c 7, .c 251, .c 3, .c 5,
  .c 641, .c 3, .c 109, .c 7, .c 3, .p pv3 [pv2,pv139,pv197], .c 131, .c 3, .p pv5 [pv2,pv438131],
  .c 5, .c 3, .c 149, .c 11, .c 3, .c 5, .c 23, .c 3, .c 7, .c 211, .c 3, .p pv5 [pv2,pv438143],
  .c 683,
]
private theorem h0106c30 : checkBlock 876035 128 b0106c30 = true := by
  decide +kernel

private def b0106c31 : List Row := [
  .c 3, .c 11, .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv23,pv127], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv146051], .c 3, .p pv13 [pv2,pv5,pv87631], .c 233, .c 3, .c 13, .c 359, .c 3,
  .c 7, .c 5, .c 3, .p pv3 [pv2,pv109541], .p pv3 [pv2,pv3,pv5,pv7,pv13,pv107], .c 3, .c 5, .c 7,
  .c 3, .p pv3 [pv2,pv5,pv43,pv1019], .c 13, .c 3, .c 79, .p pv2 [pv2,pv3,pv11,pv2213], .c 3,
  .c 71, .c 5, .c 3, .c 11, .c 461, .c 3, .c 5, .c 17, .c 3, .p pv11 [pv2,pv5,pv11,pv31,pv257],
  .p pv17 [pv2,pv3,pv7,pv10433], .c 3, .c 101, .c 7, .c 3, .c 43, .c 5, .c 3, .c 137, .c 587,
  .c 3, .c 5, .c 83, .c 3, .c 17, .c 11, .c 3, .c 7, .c 29, .c 3, .c 19, .c 5, .c 3, .c 37, .c 7,
  .c 3, .c 5, .c 67, .c 3, .p pv23 [pv2,pv5,pv87643], .p pv7 [pv2,pv3,pv19,pv31], .c 3, .c 107,
  .c 281, .c 3, .p pv19 [pv2,pv7,pv62603], .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 41, .c 3,
  .c 23, .c 7, .c 3, .c 29, .c 11, .c 3, .c 13, .c 5, .c 3, .p pv7 [pv2,pv101,pv4339],
  .p pv17 [pv2,pv3,pv5,pv11,pv83], .c 3, .c 5, .c 409, .c 3, .c 7, .c 37, .c 3,
  .p pv3 [pv2,pv29,pv1889], .c 13, .c 3, .c 17, .c 5, .c 3, .c 61, .c 73, .c 3, .c 5, .c 241,
  .c 3, .c 131, .p pv2 [pv2,pv3,pv347,pv421], .c 3, .c 19, .p pv7 [pv2,pv3,pv2029], .c 3, .c 7,
  .c 5, .c 3, .c 41, .c 113, .c 3, .c 5,
]
private theorem h0106c31 : checkBlock 876291 128 b0106c31 = true := by
  decide +kernel

def rows0106 : List Row :=
  b0106c00 ++ b0106c01 ++ b0106c02 ++ b0106c03 ++ b0106c04 ++ b0106c05 ++ b0106c06 ++ b0106c07 ++
  b0106c08 ++ b0106c09 ++ b0106c10 ++ b0106c11 ++ b0106c12 ++ b0106c13 ++ b0106c14 ++ b0106c15 ++
  b0106c16 ++ b0106c17 ++ b0106c18 ++ b0106c19 ++ b0106c20 ++ b0106c21 ++ b0106c22 ++ b0106c23 ++
  b0106c24 ++ b0106c25 ++ b0106c26 ++ b0106c27 ++ b0106c28 ++ b0106c29 ++ b0106c30 ++ b0106c31

theorem checked0106 : checkBlock 868355 4096 rows0106 = true :=
  checkBlock_append h0106c00 (
    checkBlock_append h0106c01 (
    checkBlock_append h0106c02 (
    checkBlock_append h0106c03 (
    checkBlock_append h0106c04 (
    checkBlock_append h0106c05 (
    checkBlock_append h0106c06 (
    checkBlock_append h0106c07 (
    checkBlock_append h0106c08 (
    checkBlock_append h0106c09 (
    checkBlock_append h0106c10 (
    checkBlock_append h0106c11 (
    checkBlock_append h0106c12 (
    checkBlock_append h0106c13 (
    checkBlock_append h0106c14 (
    checkBlock_append h0106c15 (
    checkBlock_append h0106c16 (
    checkBlock_append h0106c17 (
    checkBlock_append h0106c18 (
    checkBlock_append h0106c19 (
    checkBlock_append h0106c20 (
    checkBlock_append h0106c21 (
    checkBlock_append h0106c22 (
    checkBlock_append h0106c23 (
    checkBlock_append h0106c24 (
    checkBlock_append h0106c25 (
    checkBlock_append h0106c26 (
    checkBlock_append h0106c27 (
    checkBlock_append h0106c28 (
    checkBlock_append h0106c29 (
    checkBlock_append h0106c30 (
    h0106c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
