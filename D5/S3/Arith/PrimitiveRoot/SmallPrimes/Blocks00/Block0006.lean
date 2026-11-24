/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks00/Block0006
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks00/Block0006.checked0006
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table004
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table010
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table011
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table012

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0006c00 : List Row := [
  .c 3, .p pv2 [pv2,pv12289], .c 11, .c 3, .c 211, .c 5, .c 3, .p pv3 [pv2,pv7,pv439],
  .p pv2 [pv2,pv3,pv5,pv11,pv149], .c 3, .c 5, .p pv5 [pv2,pv3,pv683], .c 3, .c 11, .c 137, .c 3,
  .c 101, .c 7, .c 3, .p pv3 [pv2,pv11,pv13,pv43], .c 5, .c 3, .p pv13 [pv2,pv17,pv1447],
  .p pv7 [pv2,pv3,pv5,pv41], .c 3, .c 5, .p pv3 [pv2,pv3,pv59,pv139], .c 3,
  .p pv2 [pv2,pv5,pv7,pv19,pv37], .c 29, .c 3, .c 7, .c 83, .c 3, .p pv5 [pv2,pv24611], .c 5,
  .c 3, .c 19, .c 7, .c 3, .c 5, .c 53, .c 3, .c 41, .c 23, .c 3, .c 11, .c 17, .c 3,
  .p pv2 [pv2,pv7,pv1759], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv821], .c 3, .c 5, .c 19, .c 3,
  .c 29, .c 7, .c 3, .p pv2 [pv2,pv97,pv127], .p pv3 [pv2,pv3,pv43,pv191], .c 3, .c 13, .c 5,
  .c 3, .c 23, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv79], .c 3, .c 7, .c 47, .c 3,
  .p pv2 [pv2,pv89,pv277], .c 13, .c 3, .c 11, .c 5, .c 3, .c 149, .c 31, .c 3, .c 5, .c 107,
  .c 3, .p pv2 [pv2,pv5,pv4933], .p pv2 [pv2,pv3,pv4111], .c 3, .c 103, .p pv11 [pv2,pv3,pv2741],
  .c 3, .c 7, .c 5, .c 3, .c 61, .c 17, .c 3, .c 5, .c 7, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv19,pv433], .c 3, .p pv5 [pv2,pv24683], .p pv13 [pv2,pv3,pv11,pv17], .c 3,
  .c 97, .c 5, .c 3, .c 11, .c 19, .c 3, .c 5, .c 13, .c 3, .p pv11 [pv2,pv5,pv11,pv449],
  .p pv5 [pv2,pv3,pv7], .c 3, .c 47, .c 7, .c 3, .c 127, .c 5, .c 3, .p pv3 [pv2,pv193],
]
private theorem h0006c00 : checkBlock 49155 128 b0006c00 = true := by
  decide +kernel

private def b0006c01 : List Row := [
  .p pv2 [pv2,pv3,pv5,pv61], .c 3, .c 5, .p pv5 [pv2,pv3,pv29,pv71], .c 3, .c 73, .c 11, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv1373], .c 3, .p pv3 [pv2,pv37,pv167], .c 5, .c 3, .c 13, .c 7, .c 3,
  .c 5, .c 197, .c 3, .p pv23 [pv2,pv5,pv23,pv43], .c 17, .c 3, .c 19, .p pv3 [pv2,pv3,pv8243],
  .c 3, .p pv5 [pv2,pv7,pv3533], .c 5, .c 3, .c 7, .c 61, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv7,pv19,pv31], .c 3, .p pv3 [pv2,pv5,pv1237], .c 7, .c 3, .c 17, .c 11, .c 3,
  .c 43, .c 5, .c 3, .p pv2 [pv2,pv24749], .c 59, .c 3, .c 5, .c 31, .c 3, .c 7, .c 67, .c 3,
  .c 13, .c 23, .c 3, .p pv2 [pv2,pv11,pv2251], .c 5, .c 3, .p pv3 [pv2,pv41,pv151],
  .p pv11 [pv2,pv3,pv5,pv13,pv127], .c 3, .c 5, .p pv13 [pv2,pv3,pv43], .c 3, .c 107, .c 13, .c 3,
  .p pv2 [pv2,pv7,pv3539], .p pv7 [pv2,pv3,pv4129], .c 3, .c 7, .c 5, .c 3,
  .p pv11 [pv2,pv71,pv349], .c 29, .c 3, .c 5, .c 7, .c 3, .c 19, .c 89, .c 3, .c 11, .c 43, .c 3,
  .c 179, .c 5, .c 3, .c 17, .c 101, .c 3, .c 5, .p pv5 [pv2,pv3,pv4133], .c 3, .c 193,
  .p pv3 [pv2,pv3,pv7,pv1181], .c 3, .c 113, .c 7, .c 3, .p pv2 [pv2,pv79,pv157], .c 5, .c 3,
  .c 29, .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv919], .c 3, .c 31, .p pv5 [pv2,pv3,pv11,pv47], .c 3,
  .c 7, .p pv3 [pv2,pv3,pv8273], .c 3, .c 11, .c 5, .c 3, .c 131, .c 7, .c 3, .c 5, .c 17, .c 3,
  .c 53, .p pv3 [pv2,pv3,pv31,pv89], .c 3,
]
private theorem h0006c01 : checkBlock 49411 128 b0006c01 = true := by
  decide +kernel

private def b0006c02 : List Row := [
  .p pv2 [pv2,pv19,pv1307], .p pv2 [pv2,pv3,pv4139], .c 3, .c 13, .c 5, .c 3, .c 7,
  .p pv17 [pv2,pv3,pv5,pv23], .c 3, .c 5, .c 11, .c 3, .c 17, .c 7, .c 3, .p pv3 [pv2,pv1553],
  .c 13, .c 3, .c 23, .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv1657], .c 3, .c 5, .c 83, .c 3,
  .c 7, .c 19, .c 3, .p pv5 [pv2,pv23,pv47], .c 223, .c 3, .c 41, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv1913], .p pv2 [pv2,pv3,pv5,pv829], .c 3, .c 5, .p pv3 [pv2,pv3,pv8291], .c 3,
  .c 13, .c 11, .c 3, .p pv2 [pv2,pv7,pv1777], .c 17, .c 3, .c 7, .c 5, .c 3, .c 157, .c 71, .c 3,
  .c 5, .c 7, .c 3, .c 67, .p pv3 [pv2,pv3,pv8297], .c 3, .p pv2 [pv2,pv11,pv31,pv73],
  .p pv23 [pv2,pv3,pv461], .c 3, .c 17, .c 5, .c 3, .c 19, .p pv13 [pv2,pv3,pv5,pv83], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv2767], .c 3, .p pv11 [pv2,pv5,pv17,pv293], .c 109, .c 3, .c 31, .c 7, .c 3,
  .p pv5 [pv2,pv29,pv859], .c 5, .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv11,pv151], .c 3, .c 5, .c 19,
  .c 3, .c 11, .p pv2 [pv2,pv3,pv13,pv71], .c 3, .c 7, .c 79, .c 3, .p pv2 [pv2,pv11,pv103], .c 5,
  .c 3, .c 73, .c 7, .c 3, .c 5, .c 47, .c 3, .p pv17 [pv2,pv5,pv4987], .c 53, .c 3,
  .p pv2 [pv2,pv37,pv337], .c 31, .c 3, .c 83, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv1663],
  .c 3, .c 5, .c 41, .c 3, .c 139, .c 7, .c 3, .c 11, .c 29, .c 3, .c 19, .c 5, .c 3,
  .p pv7 [pv2,pv11,pv2269], .p pv23 [pv2,pv3,pv5,pv13],
]
private theorem h0006c02 : checkBlock 49667 128 b0006c02 = true := by
  decide +kernel

private def b0006c03 : List Row := [
  .c 3, .c 5, .p pv3 [pv2,pv3,pv53,pv157], .c 3, .c 7, .c 13, .c 3, .p pv3 [pv2,pv3121],
  .p pv7 [pv2,pv3,pv7,pv29,pv41], .c 3, .p pv5 [pv2,pv24971], .c 5, .c 3, .c 199, .c 11, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv23,pv181], .c 3, .c 47, .c 17, .c 3, .c 29, .c 107, .c 3, .c 7, .c 5,
  .c 3, .c 23, .c 151, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv4999], .p pv5 [pv2,pv3,pv2083],
  .c 3, .c 17, .p pv3 [pv2,pv3,pv13,pv641], .c 3, .c 31, .c 5, .c 3, .c 43, .c 13, .c 3, .c 5,
  .c 11, .c 3, .p pv2 [pv2,pv5,pv41,pv61], .p pv3 [pv2,pv3,pv7,pv397], .c 3, .c 19, .c 7, .c 3,
  .p pv5 [pv2,pv53,pv59], .c 5, .c 3, .c 11, .c 163, .c 3, .c 5, .p pv37 [pv2,pv3,pv19,pv439],
  .c 3, .p pv2 [pv2,pv5,pv7,pv11,pv13], .p pv2 [pv2,pv3,pv43,pv97], .c 3, .c 7, .c 113, .c 3,
  .c 13, .c 5, .c 3, .p pv2 [pv2,pv12517], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv107], .c 3,
  .c 61, .c 11, .c 3, .p pv5 [pv2,pv79,pv317], .c 13, .c 3, .p pv2 [pv2,pv7,pv1789], .c 5, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv5,pv167], .c 3, .c 5, .c 89, .c 3, .p pv17 [pv2,pv5,pv5011], .c 7, .c 3,
  .c 23, .p pv3 [pv2,pv3,pv8353], .c 3, .p pv2 [pv2,pv19,pv1319], .c 5, .c 3,
  .p pv3 [pv2,pv13,pv241], .p pv2 [pv2,pv3,pv5,pv557], .c 3, .c 5, .c 181, .c 3, .c 7, .c 41,
  .c 3, .p pv2 [pv2,pv25073], .c 11, .c 3, .p pv3 [pv2,pv6269], .c 5, .c 3,
  .p pv7 [pv2,pv31,pv809], .c 103, .c 3, .c 5, .c 13, .c 3, .c 11, .c 131, .c 3, .p pv3 [pv2,pv7],
]
private theorem h0006c03 : checkBlock 49923 128 b0006c03 = true := by
  decide +kernel

private def b0006c04 : List Row := [
  .c 19, .c 3, .c 7, .c 5, .c 3, .c 31, .c 53, .c 3, .c 5, .c 7, .c 3, .c 17, .c 61, .c 3,
  .p pv5 [pv2,pv13,pv1931], .c 23, .c 3, .c 149, .c 5, .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv31],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv761], .c 3, .p pv11 [pv2,pv5,pv5023], .c 191, .c 3, .c 11,
  .c 7, .c 3, .c 47, .c 5, .c 3, .c 109, .c 31, .c 3, .c 5, .c 29, .c 3,
  .p pv3 [pv2,pv5,pv7,pv359], .p pv3 [pv2,pv3,pv8377], .c 3, .c 7, .c 17, .c 3,
  .p pv3 [pv2,pv1571], .c 5, .c 3, .c 137, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv17,pv29], .c 3,
  .p pv2 [pv2,pv5,pv47,pv107], .c 19, .c 3, .c 13, .c 179, .c 3, .c 11, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv13,pv43], .c 3, .c 5, .c 67, .c 3, .p pv7 [pv2,pv5,pv17,pv37], .c 7, .c 3,
  .c 59, .p pv7 [pv2,pv3,pv233], .c 3, .p pv2 [pv2,pv12583], .c 5, .c 3, .c 71,
  .p pv2 [pv2,pv3,pv5,pv839], .c 3, .c 5, .c 11, .c 3, .c 7, .c 43, .c 3, .c 37,
  .p pv3 [pv2,pv3,pv7,pv11,pv109], .c 3, .p pv2 [pv2,pv13,pv149], .c 5, .c 3, .c 11, .c 17, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv2099], .c 3, .c 83, .p pv3 [pv2,pv3,pv311], .c 3,
  .p pv2 [pv2,pv7,pv59,pv61], .c 41, .c 3, .c 7, .c 5, .c 3, .c 101, .c 13, .c 3, .c 5, .c 7,
  .c 3, .p pv2 [pv2,pv5,pv71], .c 11, .c 3, .p pv3 [pv2,pv23,pv137], .c 127, .c 3,
  .p pv5 [pv2,pv17,pv1483], .c 5, .c 3, .c 211, .c 29, .c 3,
]
private theorem h0006c04 : checkBlock 50179 128 b0006c04 = true := by
  decide +kernel

private def b0006c05 : List Row := [
  .c 5, .c 31, .c 3, .p pv7 [pv2,pv5,pv13,pv97], .c 73, .c 3, .c 61, .c 7, .c 3, .c 13, .c 5,
  .c 3, .p pv2 [pv2,pv25229], .p pv7 [pv2,pv3,pv5,pv29], .c 3, .c 5, .c 109, .c 3, .c 41, .c 17,
  .c 3, .c 7, .c 11, .c 3, .c 19, .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv263],
  .c 3, .c 11, .p pv5 [pv2,pv3,pv19,pv443], .c 3, .c 17, .c 53, .c 3, .p pv3 [pv2,pv7,pv11,pv41],
  .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv401], .c 3, .c 13, .c 7, .c 3, .c 97,
  .p pv2 [pv2,pv3,pv8423], .c 3, .p pv5 [pv2,pv37,pv683], .c 5, .c 3, .p pv2 [pv2,pv12637],
  .p pv3 [pv2,pv3,pv5,pv337], .c 3, .c 5, .c 13, .c 3, .c 7, .c 59, .c 3, .c 11, .c 61, .c 3,
  .c 103, .c 5, .c 3, .c 37, .p pv2 [pv2,pv3,pv5,pv281], .c 3, .c 5, .p pv17 [pv2,pv3,pv8431],
  .c 3, .p pv7 [pv2,pv5,pv5059], .p pv5 [pv2,pv3,pv17,pv31], .c 3, .c 19, .p pv3 [pv2,pv3,pv937],
  .c 3, .c 7, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 7, .c 3, .c 223, .c 23, .c 3,
  .p pv2 [pv2,pv17,pv1489], .c 197, .c 3, .c 11, .c 5, .c 3, .c 79, .c 89, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv23,pv367], .c 3, .p pv2 [pv2,pv5,pv1013], .c 37, .c 3, .c 179, .c 7, .c 3,
  .c 29, .c 5, .c 3, .c 23, .p pv11 [pv2,pv3,pv5,pv563], .c 3, .c 5, .c 11, .c 3, .c 59,
  .p pv2 [pv2,pv3,pv8447], .c 3, .c 7, .c 173,
]
private theorem h0006c05 : checkBlock 50435 128 b0006c05 = true := by
  decide +kernel

private def b0006c06 : List Row := [
  .c 3, .c 163, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv313], .c 3, .c 17, .c 13,
  .c 3, .c 41, .c 67, .c 3, .p pv2 [pv2,pv7,pv3623], .c 5, .c 3, .c 7, .c 97, .c 3, .c 5, .c 113,
  .c 3, .p pv2 [pv2,pv5,pv43,pv59], .c 7, .c 3, .c 31, .c 19, .c 3, .p pv3 [pv2,pv13,pv61], .c 5,
  .c 3, .c 193, .c 23, .c 3, .c 5, .p pv5 [pv2,pv3,pv8461], .c 3, .c 7, .p pv11 [pv2,pv3,pv4231],
  .c 3, .p pv3 [pv2,pv11,pv577], .c 17, .c 3, .c 43, .c 5, .c 3, .p pv2 [pv2,pv12697], .c 13,
  .c 3, .c 5, .c 79, .c 3, .c 37, .c 101, .c 3, .c 23, .c 11, .c 3, .c 7, .c 5, .c 3, .c 89,
  .p pv2 [pv2,pv3,pv5,pv7,pv11], .c 3, .c 5, .c 7, .c 3, .c 11, .p pv7 [pv2,pv3,pv353], .c 3,
  .c 29, .p pv3 [pv2,pv3,pv37,pv229], .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv7,pv227], .c 211,
  .c 3, .c 5, .p pv19 [pv2,pv3,pv13,pv163], .c 3, .c 181, .c 19, .c 3, .p pv2 [pv2,pv29,pv877],
  .c 7, .c 3, .p pv3 [pv2,pv6359], .c 5, .c 3, .c 83, .c 17, .c 3, .c 5, .c 151, .c 3,
  .p pv2 [pv2,pv5,pv7,pv727], .p pv2 [pv2,pv3,pv4241], .c 3, .c 7, .c 23, .c 3, .c 109, .c 5,
  .c 3, .p pv2 [pv2,pv11,pv13,pv89], .c 7, .c 3, .c 5, .c 59, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv23,pv41], .c 3, .c 127, .p pv11 [pv2,pv3,pv1061], .c 3, .c 31, .c 5, .c 3,
  .c 7, .c 11, .c 3, .c 5,
]
private theorem h0006c06 : checkBlock 50691 128 b0006c06 = true := by
  decide +kernel

private def b0006c07 : List Row := [
  .c 13, .c 3, .p pv23 [pv2,pv5,pv1019], .c 7, .c 3, .p pv2 [pv2,pv12739], .c 131, .c 3, .c 11,
  .c 5, .c 3, .p pv3 [pv2,pv23,pv277], .p pv2 [pv2,pv3,pv5,pv1699], .c 3, .c 5, .c 19, .c 3, .c 7,
  .c 17, .c 3, .c 67, .p pv2 [pv2,pv3,pv7,pv607], .c 3, .p pv3 [pv2,pv3187], .c 5, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv5,pv17], .c 3, .c 5, .c 11, .c 3, .c 29, .c 139, .c 3, .c 17, .c 163, .c 3,
  .c 7, .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv7], .c 3, .c 5, .c 7, .c 3, .c 43,
  .p pv2 [pv2,pv3,pv47,pv181], .c 3, .p pv5 [pv2,pv25523], .c 71, .c 3, .c 19, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv521], .p pv2 [pv2,pv3,pv5,pv23,pv37], .c 3, .c 5, .c 223, .c 3,
  .p pv11 [pv2,pv5,pv5107], .c 11, .c 3, .c 13, .c 7, .c 3, .c 23, .c 5, .c 3, .c 47, .c 19, .c 3,
  .c 5, .c 37, .c 3, .c 137, .c 13, .c 3, .c 7, .p pv13 [pv2,pv3,pv4259], .c 3, .c 79, .c 5, .c 3,
  .c 17, .c 7, .c 3, .c 5, .c 29, .c 3, .p pv11 [pv2,pv5,pv5113], .p pv2 [pv2,pv3,pv4261], .c 3,
  .p pv3 [pv2,pv17,pv47], .c 11, .c 3, .c 199, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv11,pv31],
  .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv29], .c 3, .c 11, .c 7, .c 3, .c 19,
  .p pv19 [pv2,pv3,pv13,pv41], .c 3, .c 73, .c 5, .c 3, .c 61, .c 13, .c 3, .c 5, .c 17, .c 3,
  .c 7, .p pv5 [pv2,pv3,pv79], .c 3, .p pv2 [pv2,pv12799], .p pv13 [pv2,pv3,pv7,pv23,pv53], .c 3,
]
private theorem h0006c07 : checkBlock 50947 128 b0006c07 = true := by
  decide +kernel

private def b0006c08 : List Row := [
  .p pv2 [pv2,pv25601], .c 5, .c 3, .c 41, .c 83, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv97], .c 3,
  .c 17, .c 181, .c 3, .c 11, .p pv2 [pv2,pv3,pv1423], .c 3, .c 7, .c 5, .c 3,
  .p pv23 [pv2,pv11,pv17,pv137], .p pv17 [pv2,pv3,pv5,pv7,pv61], .c 3, .c 5, .c 7, .c 3, .c 53,
  .c 107, .c 3, .p pv3 [pv2,pv43,pv149], .c 13, .c 3, .p pv5 [pv2,pv19,pv71], .c 5, .c 3, .c 167,
  .c 11, .c 3, .c 5, .c 47, .c 3, .c 19, .p pv2 [pv2,pv3,pv7,pv11,pv37], .c 3,
  .p pv5 [pv2,pv25643], .c 7, .c 3, .c 11, .c 5, .c 3, .c 43, .c 29, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv17,pv503], .c 3, .c 13, .c 23, .c 3, .c 7, .c 19, .c 3, .c 17, .c 5, .c 3,
  .p pv3 [pv2,pv401], .c 7, .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv17,pv151],
  .p pv5 [pv2,pv3,pv43,pv199], .c 3, .p pv2 [pv2,pv25673], .p pv31 [pv2,pv3,pv11,pv389], .c 3,
  .c 89, .c 5, .c 3, .c 7, .p pv37 [pv2,pv3,pv5,pv107], .c 3, .c 5, .c 31, .c 3, .c 47, .c 7,
  .c 3, .c 83, .c 191, .c 3, .p pv5 [pv2,pv23,pv1117], .c 5, .c 3, .c 13, .c 17, .c 3, .c 5,
  .c 103, .c 3, .c 7, .c 11, .c 3, .p pv5 [pv2,pv25703], .c 101, .c 3, .p pv2 [pv2,pv12853], .c 5,
  .c 3, .p pv2 [pv2,pv47,pv547], .p pv2 [pv2,pv3,pv5,pv857], .c 3, .c 5, .p pv2 [pv2,pv3,pv2857],
  .c 3, .p pv7 [pv2,pv5,pv37,pv139], .c 19, .c 3, .p pv2 [pv2,pv7,pv11,pv167],
  .p pv3 [pv2,pv3,pv8573], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv59,pv109], .c 23, .c 3, .c 5,
  .c 7,
]
private theorem h0006c08 : checkBlock 51203 128 b0006c08 = true := by
  decide +kernel

private def b0006c09 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv31,pv83], .c 53, .c 3, .c 13, .c 11, .c 3, .p pv3 [pv2,pv3217], .c 5,
  .c 3, .p pv7 [pv2,pv7,pv3677], .p pv17 [pv2,pv3,pv5,pv11,pv13], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv8581], .c 3, .c 11, .c 13, .c 3, .c 23, .c 7, .c 3, .p pv5 [pv2,pv11,pv2341],
  .c 5, .c 3, .c 19, .p pv11 [pv2,pv3,pv5,pv17,pv101], .c 3, .c 5, .p pv13 [pv2,pv3,pv53], .c 3,
  .p pv3 [pv2,pv5,pv7,pv23], .c 67, .c 3, .c 7, .c 227, .c 3, .c 29, .c 5, .c 3,
  .p pv2 [pv2,pv73,pv353], .c 7, .c 3, .c 5, .c 19, .c 3, .p pv11 [pv2,pv5,pv1031], .c 31, .c 3,
  .c 11, .c 47, .c 3, .p pv2 [pv2,pv7,pv29,pv127], .c 5, .c 3, .c 7, .c 13, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv7,pv307], .c 3, .p pv2 [pv2,pv5,pv2579], .c 7, .c 3, .c 79, .c 23, .c 3,
  .p pv3 [pv2,pv6449], .c 5, .c 3, .p pv7 [pv2,pv25799], .c 11, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv47,pv61], .c 3, .c 7, .p pv2 [pv2,pv3,pv11,pv17,pv23], .c 3, .c 71, .c 41,
  .c 3, .c 11, .c 5, .c 3, .c 17, .p pv29 [pv2,pv3,pv5,pv1721], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv331], .c 3, .c 113, .c 43, .c 3, .p pv7 [pv2,pv7,pv17,pv31], .c 13, .c 3,
  .c 7, .c 5, .c 3, .p pv2 [pv2,pv23,pv1123], .c 19, .c 3, .c 5, .c 7, .c 3, .c 163,
  .p pv7 [pv2,pv3,pv2153], .c 3, .c 31, .p pv31 [pv2,pv3,pv11,pv29], .c 3, .p pv2 [pv2,pv25841],
  .c 5, .c 3, .c 11, .p pv17 [pv2,pv3,pv5,pv1723], .c 3, .c 5, .c 17, .c 3, .c 13, .c 149, .c 3,
  .c 29, .c 7, .c 3, .p pv3 [pv2,pv101],
]
private theorem h0006c09 : checkBlock 51459 128 b0006c09 = true := by
  decide +kernel

private def b0006c10 : List Row := [
  .c 5, .c 3, .p pv13 [pv2,pv19,pv1361], .p pv7 [pv2,pv3,pv5,pv431], .c 3, .c 5, .c 13, .c 3,
  .c 17, .c 11, .c 3, .c 7, .c 31, .c 3, .c 59, .c 5, .c 3, .p pv2 [pv2,pv17,pv761], .c 7, .c 3,
  .c 5, .c 73, .c 3, .c 191, .c 37, .c 3, .p pv5 [pv2,pv11,pv13,pv181], .p pv19 [pv2,pv3,pv719],
  .c 3, .c 23, .c 5, .c 3, .c 7, .c 53, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv137], .c 3, .c 67, .c 7,
  .c 3, .p pv3 [pv2,pv23,pv563], .c 11, .c 3, .p pv2 [pv2,pv59,pv439], .c 5, .c 3, .c 103, .c 197,
  .c 3, .c 5, .p pv11 [pv2,pv3,pv17,pv127], .c 3, .c 7, .c 29, .c 3, .p pv2 [pv2,pv25913],
  .p pv2 [pv2,pv3,pv7,pv617], .c 3, .c 17, .c 5, .c 3, .p pv7 [pv2,pv25919], .c 47, .c 3, .c 5,
  .c 139, .c 3, .c 19, .p pv11 [pv2,pv3,pv29,pv149], .c 3, .c 13, .p pv3 [pv2,pv3,pv43,pv67],
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv12967], .p pv7 [pv2,pv3,pv5,pv7,pv13,pv19], .c 3, .c 5,
  .c 7, .c 3, .c 29, .c 13, .c 3, .c 11, .c 19, .c 3, .p pv2 [pv2,pv12973], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv11,pv337], .c 17, .c 3, .c 5, .p pv11 [pv2,pv3,pv41,pv211], .c 3, .c 23,
  .p pv43 [pv2,pv3,pv7,pv103], .c 3, .c 193, .c 7, .c 3, .c 137, .c 5, .c 3, .p pv3 [pv2,pv6491],
  .c 11, .c 3, .c 5, .c 167, .c 3, .p pv3 [pv2,pv5,pv7,pv53], .c 127, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv13,pv37], .c 3, .c 11, .c 5, .c 3, .c 223, .c 7, .c 3, .c 5, .c 157, .c 3,
]
private theorem h0006c10 : checkBlock 51715 128 b0006c10 = true := by
  decide +kernel

private def b0006c11 : List Row := [
  .p pv2 [pv2,pv5,pv5197], .p pv2 [pv2,pv3,pv61,pv71], .c 3, .p pv3 [pv2,pv73,pv89], .c 59, .c 3,
  .c 227, .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv1733], .c 3, .c 5, .c 11, .c 3, .c 149, .c 7,
  .c 3, .c 131, .p pv17 [pv2,pv3,pv11,pv197], .c 3, .c 13, .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv17], .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv23,pv29], .c 3, .c 7, .c 61, .c 3,
  .c 17, .c 13, .c 3, .c 71, .c 5, .c 3, .c 23, .p pv2 [pv2,pv3,pv5,pv347], .c 3, .c 5,
  .p pv7 [pv2,pv3,pv241], .c 3, .c 79, .c 11, .c 3, .p pv2 [pv2,pv7,pv3719],
  .p pv2 [pv2,pv3,pv4339], .c 3, .c 7, .c 5, .c 3, .c 19, .p pv17 [pv2,pv3,pv5,pv7,pv31], .c 3,
  .c 5, .c 7, .c 3, .c 13, .c 113, .c 3, .c 59, .c 53, .c 3, .p pv5 [pv2,pv109,pv239], .c 5, .c 3,
  .c 107, .c 31, .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv1303], .c 47, .c 3,
  .p pv5 [pv2,pv67,pv389], .c 7, .c 3, .c 37, .c 5, .c 3, .c 17, .c 23, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv2897], .c 3, .c 11, .p pv5 [pv2,pv3,pv41,pv53], .c 3, .c 7, .c 43, .c 3,
  .p pv2 [pv2,pv11,pv2371], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv1087], .c 3,
  .p pv3 [pv2,pv5,pv2609], .p pv3 [pv2,pv3,pv13,pv223], .c 3, .c 23, .p pv13 [pv2,pv3,pv4349],
  .c 3, .c 19, .c 5, .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv29], .c 3, .c 5, .c 17, .c 3, .c 109,
  .c 7, .c 3, .c 11, .c 79, .c 3, .p pv5 [pv2,pv26111], .c 5,
]
private theorem h0006c11 : checkBlock 51971 128 b0006c11 = true := by
  decide +kernel

private def b0006c12 : List Row := [
  .c 3, .c 29, .c 19, .c 3, .c 5, .p pv7 [pv2,pv3,pv1451], .c 3, .c 7, .c 89, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv7,pv311], .c 3, .p pv2 [pv2,pv13063], .c 5, .c 3,
  .p pv2 [pv2,pv17,pv29,pv53], .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv31,pv281], .c 3, .c 167,
  .c 13, .c 3, .c 61, .c 23, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv19,pv43],
  .p pv7 [pv2,pv3,pv5,pv7,pv83], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv523], .c 193, .c 3,
  .c 19, .c 17, .c 3, .p pv3 [pv2,pv13,pv503], .c 5, .c 3, .c 113, .p pv17 [pv2,pv3,pv5,pv109],
  .c 3, .c 5, .c 11, .c 3, .c 43, .c 59, .c 3, .c 199, .c 7, .c 3, .c 17, .c 5, .c 3, .c 11,
  .c 13, .c 3, .c 5, .c 41, .c 3, .p pv37 [pv2,pv5,pv7,pv11,pv17], .p pv5 [pv2,pv3,pv2909], .c 3,
  .c 7, .p pv13 [pv2,pv3,pv1091], .c 3, .c 83, .c 5, .c 3, .p pv2 [pv2,pv26189], .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv8731], .c 3, .p pv11 [pv2,pv5,pv13,pv31], .c 11, .c 3, .c 151, .c 61, .c 3,
  .c 13, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 23, .c 3, .c 19, .c 7, .c 3, .c 103, .c 13, .c 3,
  .p pv3 [pv2,pv29,pv113], .c 5, .c 3, .c 41, .c 229, .c 3, .c 5, .c 179, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv31,pv47], .c 3, .p pv3 [pv2,pv79,pv83], .c 11, .c 3, .c 23, .c 5, .c 3, .c 71,
  .c 137, .c 3, .c 5, .c 97, .c 3, .c 11,
]
private theorem h0006c12 : checkBlock 52227 128 b0006c12 = true := by
  decide +kernel

private def b0006c13 : List Row := [
  .c 31, .c 3, .c 73, .p pv7 [pv2,pv3], .c 3, .c 7, .c 5, .c 3, .c 47, .p pv17 [pv2,pv3,pv5,pv7],
  .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv59,pv89], .c 17, .c 3, .p pv2 [pv2,pv19,pv691], .c 29,
  .c 3, .c 53, .c 5, .c 3, .p pv3 [pv2,pv7,pv67], .c 131, .c 3, .c 5, .c 107, .c 3,
  .p pv2 [pv2,pv5,pv37,pv71], .p pv3 [pv2,pv3,pv7,pv139], .c 3, .c 11, .c 7, .c 3,
  .p pv3 [pv2,pv6569], .c 5, .c 3, .c 13, .p pv7 [pv2,pv3,pv5,pv73], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv8761], .c 3, .p pv2 [pv2,pv5,pv7,pv751], .c 19, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv23,pv127], .c 3, .p pv5 [pv2,pv61,pv431], .c 5, .c 3, .c 43, .c 7, .c 3, .c 5,
  .c 149, .c 3, .c 23, .c 41, .c 3, .c 31, .p pv11 [pv2,pv3,pv137], .c 3, .c 11, .c 5, .c 3, .c 7,
  .c 101, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv179], .c 3, .p pv13 [pv2,pv5,pv19,pv277], .c 7, .c 3,
  .c 13, .p pv3 [pv2,pv3,pv31,pv283], .c 3, .c 61, .c 5, .c 3, .c 17, .c 37, .c 3, .c 5, .c 11,
  .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv17,pv1549], .c 31, .c 3, .p pv3 [pv2,pv823], .c 5, .c 3,
  .c 11, .c 139, .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv11,pv479], .c 23, .c 3,
  .p pv3 [pv2,pv7,pv941], .c 151, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv13177],
  .p pv23 [pv2,pv3,pv5,pv7,pv251], .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv659], .c 11, .c 3,
  .p pv5 [pv2,pv41,pv643], .c 67, .c 3, .p pv2 [pv2,pv13183], .c 5, .c 3,
]
private theorem h0006c13 : checkBlock 52483 128 b0006c13 = true := by
  decide +kernel

private def b0006c14 : List Row := [
  .c 23, .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv59,pv149], .c 3, .c 17, .c 71, .c 3,
  .p pv2 [pv2,pv11,pv109], .c 7, .c 3, .c 19, .c 5, .c 3, .p pv3 [pv2,pv17,pv97], .c 113, .c 3,
  .c 5, .c 89, .c 3, .c 47, .p pv5 [pv2,pv3,pv19,pv463], .c 3, .c 7, .c 11, .c 3, .c 13, .c 5,
  .c 3, .c 37, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv677], .c 3, .c 11, .p pv2 [pv2,pv3,pv163],
  .c 3, .p pv3 [pv2,pv3301], .c 13, .c 3, .c 101, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv17,pv37], .c 3, .c 53, .c 7, .c 3, .c 43, .c 41, .c 3, .c 17, .c 5, .c 3,
  .p pv7 [pv2,pv13,pv19,pv107], .p pv11 [pv2,pv3,pv5,pv881], .c 3, .c 5, .c 29, .c 3, .c 7, .c 37,
  .c 3, .c 11, .p pv3 [pv2,pv3,pv7,pv1259], .c 3, .p pv2 [pv2,pv137,pv193], .c 5, .c 3,
  .p pv3 [pv2,pv11,pv601], .c 227, .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv23],
  .p pv3 [pv2,pv3,pv2939], .c 3, .c 191, .c 157, .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv26459],
  .c 11, .c 3, .c 5, .c 7, .c 3, .c 41, .c 43, .c 3, .p pv5 [pv2,pv13,pv509], .c 167, .c 3, .c 11,
  .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv353], .c 3, .c 5, .p pv5 [pv2,pv3,pv1471], .c 3,
  .c 211, .p pv3 [pv2,pv3,pv7,pv13,pv97], .c 3, .p pv5 [pv2,pv71,pv373], .c 7, .c 3,
  .p pv2 [pv2,pv17,pv19,pv41], .c 5, .c 3, .c 31, .p pv2 [pv2,pv3,pv5,pv883], .c 3, .c 5, .c 11,
  .c 3, .c 19, .c 197,
]
private theorem h0006c14 : checkBlock 52739 128 b0006c14 = true := by
  decide +kernel

private def b0006c15 : List Row := [
  .c 3, .c 7, .p pv3 [pv2,pv3,pv11,pv73], .c 3, .p pv2 [pv2,pv26501], .c 5, .c 3, .c 11, .c 7,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv47], .c 3, .c 37, .c 17, .c 3, .c 13, .c 19, .c 3, .c 181, .c 5,
  .c 3, .c 7, .c 29, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv421], .c 3, .p pv11 [pv2,pv5,pv1061], .c 7,
  .c 3, .c 17, .c 97, .c 3, .c 47, .c 5, .c 3, .p pv2 [pv2,pv13267], .c 73, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv4423], .c 3, .c 7, .c 109, .c 3, .p pv5 [pv2,pv11,pv19,pv127],
  .p pv31 [pv2,pv3,pv7,pv79], .c 3, .p pv2 [pv2,pv13,pv1021], .c 5, .c 3, .c 29,
  .p pv2 [pv2,pv3,pv5,pv59], .c 3, .c 5, .c 23, .c 3, .c 173, .p pv5 [pv2,pv3,pv2213], .c 3,
  .p pv2 [pv2,pv7,pv271], .c 11, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv29,pv229], .c 13, .c 3,
  .c 5, .c 7, .c 3, .c 11, .c 19, .c 3, .p pv2 [pv2,pv26573], .p pv13 [pv2,pv3,pv43,pv103], .c 3,
  .c 23, .c 5, .c 3, .c 17, .p pv31 [pv2,pv3,pv5,pv443], .c 3, .c 5, .c 79, .c 3,
  .p pv2 [pv2,pv5,pv13,pv409], .p pv23 [pv2,pv3,pv7,pv211], .c 3, .c 41, .c 7, .c 3, .c 13, .c 5,
  .c 3, .p pv2 [pv2,pv13297], .c 43, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv13,pv31], .c 3,
  .p pv3 [pv2,pv5,pv7,pv19], .c 83, .c 3, .c 7, .c 13, .c 3, .c 127, .c 5, .c 3, .c 19, .c 7,
  .c 3, .c 5, .c 17, .c 3, .p pv23 [pv2,pv5,pv5323], .p pv5 [pv2,pv3,pv1109], .c 3, .c 139,
  .p pv3 [pv2,pv3,pv19,pv467], .c 3, .c 37, .c 5, .c 3, .c 7,
]
private theorem h0006c15 : checkBlock 52995 128 b0006c15 = true := by
  decide +kernel

private def b0006c16 : List Row := [
  .c 11, .c 3, .c 5, .c 19, .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv26633],
  .p pv7 [pv2,pv3,pv23,pv193], .c 3, .c 11, .c 5, .c 3, .p pv7 [pv2,pv17,pv1567],
  .p pv11 [pv2,pv3,pv5,pv37], .c 3, .c 5, .c 13, .c 3, .c 7, .c 137, .c 3, .c 223,
  .p pv2 [pv2,pv3,pv7,pv47], .c 3, .c 151, .c 5, .c 3, .p pv2 [pv2,pv13327], .c 89, .c 3, .c 5,
  .c 11, .c 3, .c 71, .p pv2 [pv2,pv3,pv8887], .c 3, .p pv5 [pv2,pv7,pv13,pv293], .c 17, .c 3,
  .c 7, .c 5, .c 3, .c 11, .c 41, .c 3, .c 5, .c 7, .c 3, .c 31, .p pv7 [pv2,pv3,pv13,pv19], .c 3,
  .c 229, .p pv3 [pv2,pv3,pv8893], .c 3, .c 17, .c 5, .c 3, .c 83, .c 19, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv139], .c 3, .p pv2 [pv2,pv5,pv17,pv157], .c 11, .c 3, .c 197, .c 7, .c 3,
  .c 107, .c 5, .c 3, .c 67, .p pv7 [pv2,pv3,pv5,pv89], .c 3, .c 5, .p pv5 [pv2,pv3,pv23,pv43],
  .c 3, .p pv2 [pv2,pv5,pv7,pv109], .c 31, .c 3, .c 7, .p pv2 [pv2,pv3,pv29,pv307], .c 3, .c 41,
  .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv61,pv73], .c 3, .p pv3 [pv2,pv5,pv167],
  .c 13, .c 3, .c 19, .c 11, .c 3, .p pv2 [pv2,pv7,pv23,pv83], .c 5, .c 3, .c 7, .c 193, .c 3,
  .c 5, .c 127, .c 3, .c 11, .c 7, .c 3, .c 53, .p pv3 [pv2,pv3,pv2971], .c 3, .c 79, .c 5, .c 3,
  .c 89, .c 149, .c 3, .c 5, .c 61, .c 3, .c 7, .p pv3 [pv2,pv3,pv37,pv241], .c 3,
]
private theorem h0006c16 : checkBlock 53251 128 b0006c16 = true := by
  decide +kernel

private def b0006c17 : List Row := [
  .p pv2 [pv2,pv31,pv863], .c 73, .c 3, .c 59, .c 5, .c 3, .c 109, .c 13, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv811], .c 3, .c 199, .c 17, .c 3, .c 11, .c 37, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv1217], .p pv3 [pv2,pv3,pv5,pv7,pv17], .c 3, .c 5, .c 7, .c 3, .c 19, .c 29,
  .c 3, .c 17, .p pv19 [pv2,pv3,pv31], .c 3, .c 13, .c 5, .c 3, .c 131, .c 11, .c 3, .c 5, .c 41,
  .c 3, .p pv13 [pv2,pv5,pv23,pv233], .p pv5 [pv2,pv3,pv7,pv11,pv29], .c 3, .p pv2 [pv2,pv13399],
  .c 7, .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv6701], .p pv17 [pv2,pv3,pv5,pv1787], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv1117], .c 3, .c 29, .p pv3 [pv2,pv3,pv331], .c 3, .c 7,
  .p pv29 [pv2,pv3,pv41,pv109], .c 3, .p pv3 [pv2,pv419], .c 5, .c 3, .p pv11 [pv2,pv13,pv2063],
  .c 7, .c 3, .c 5, .c 11, .c 3, .c 13, .p pv2 [pv2,pv3,pv17,pv263], .c 3,
  .p pv3 [pv2,pv19,pv353], .c 23, .c 3, .c 103, .c 5, .c 3, .c 7, .c 191, .c 3, .c 5, .c 13, .c 3,
  .p pv3 [pv2,pv5,pv11,pv61], .c 7, .c 3, .c 37, .c 53, .c 3, .p pv2 [pv2,pv31,pv433], .c 5, .c 3,
  .p pv2 [pv2,pv26849], .c 83, .c 3, .c 5, .c 43, .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv13,pv1033], .p pv7 [pv2,pv3,pv7,pv1279], .c 3, .c 31, .c 5, .c 3, .c 13,
  .p pv17 [pv2,pv3,pv5,pv199], .c 3, .c 5, .c 17, .c 3, .c 61, .c 223, .c 3, .c 71, .c 59, .c 3,
  .c 7, .c 5, .c 3, .p pv17 [pv2,pv26879], .c 37,
]
private theorem h0006c17 : checkBlock 53507 128 b0006c17 = true := by
  decide +kernel

private def b0006c18 : List Row := [
  .c 3, .c 5, .c 7, .c 3, .c 17, .p pv2 [pv2,pv3,pv4481], .c 3, .p pv3 [pv2,pv3361], .c 11, .c 3,
  .p pv5 [pv2,pv26891], .c 5, .c 3, .c 19, .p pv17 [pv2,pv3,pv5,pv11,pv163], .c 3, .c 5, .c 23,
  .c 3, .c 11, .c 173, .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv11,pv1223], .c 5, .c 3,
  .p pv2 [pv2,pv71,pv379], .c 107, .c 3, .c 5, .c 19, .c 3, .p pv7 [pv2,pv5,pv7,pv769], .c 13,
  .c 3, .c 7, .c 17, .c 3, .c 23, .c 5, .c 3, .p pv3 [pv2,pv53,pv127], .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv17], .c 3, .p pv2 [pv2,pv5,pv2693], .c 61, .c 3, .c 11, .c 103, .c 3,
  .c 17, .c 5, .c 3, .c 7, .p pv31 [pv2,pv3,pv5,pv449], .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv1283],
  .c 3, .p pv2 [pv2,pv5,pv17,pv317], .c 7, .c 3, .p pv3 [pv2,pv6737], .p pv2 [pv2,pv3,pv13,pv691],
  .c 3, .c 19, .c 5, .c 3, .c 31, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv4493], .c 3, .c 7,
  .p pv5 [pv2,pv3,pv11,pv19,pv43], .c 3, .p pv5 [pv2,pv59,pv457], .c 199, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv149,pv181], .c 17, .c 3, .c 5, .c 73, .c 3, .p pv7 [pv2,pv5,pv13,pv83], .c 163,
  .c 3, .c 79, .p pv3 [pv2,pv3,pv17,pv23], .c 3, .c 7, .c 5, .c 3, .c 29, .c 31, .c 3, .c 5, .c 7,
  .c 3, .c 23, .c 37, .c 3, .p pv2 [pv2,pv26993], .c 13, .c 3, .p pv3 [pv2,pv17,pv397], .c 5,
  .c 3, .c 11, .p pv11 [pv2,pv3,pv5], .c 3, .c 5, .c 53, .c 3, .p pv2 [pv2,pv5,pv11,pv491],
  .p pv5 [pv2,pv3,pv7,pv643], .c 3, .c 19,
]
private theorem h0006c18 : checkBlock 53763 128 b0006c18 = true := by
  decide +kernel

private def b0006c19 : List Row := [
  .c 7, .c 3, .c 89, .c 5, .c 3, .c 97, .c 71, .c 3, .c 5, .p pv2 [pv2,pv3,pv19,pv79], .c 3,
  .c 13, .c 11, .c 3, .c 7, .p pv11 [pv2,pv3,pv563], .c 3, .c 191, .c 5, .c 3,
  .p pv2 [pv2,pv151,pv179], .c 7, .c 3, .c 5, .c 13, .c 3, .c 139, .c 23, .c 3, .c 17, .c 41,
  .c 3, .p pv2 [pv2,pv7,pv3863], .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv601], .c 3, .c 5, .c 47,
  .c 3, .p pv3 [pv2,pv5,pv541], .c 7, .c 3, .c 61, .c 11, .c 3, .c 53, .c 5, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv5,pv11,pv41], .c 3, .c 5, .c 113, .c 3, .c 7, .p pv5 [pv2,pv3,pv13,pv347],
  .c 3, .c 43, .p pv2 [pv2,pv3,pv7,pv1289], .c 3, .c 29, .c 5, .c 3, .c 173,
  .p pv11 [pv2,pv3,pv5,pv19], .c 3, .c 5, .c 31, .c 3, .c 41, .p pv2 [pv2,pv3,pv17,pv59], .c 3,
  .p pv5 [pv2,pv7,pv53,pv73], .c 19, .c 3, .c 7, .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv7,pv43],
  .c 3, .c 5, .c 7, .c 3, .c 47, .p pv11 [pv2,pv3,pv1129], .c 3, .c 11, .c 83, .c 3, .c 67, .c 5,
  .c 3, .c 151, .c 23, .c 3, .c 5, .p pv5 [pv2,pv3,pv251], .c 3, .c 59, .c 13, .c 3, .c 211, .c 7,
  .c 3, .c 193, .c 5, .c 3, .c 73, .c 11, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv7,pv31],
  .c 227, .c 3, .c 7, .c 29, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv13567], .c 7, .c 3,
]
private theorem h0006c19 : checkBlock 54019 128 b0006c19 = true := by
  decide +kernel

private def b0006c20 : List Row := [
  .c 5, .p pv5 [pv2,pv3,pv4523], .c 3, .c 17, .c 19, .c 3, .p pv5 [pv2,pv27143], .c 233, .c 3,
  .p pv2 [pv2,pv7,pv277], .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 11, .c 3,
  .p pv11 [pv2,pv5,pv5431], .c 7, .c 3, .c 29, .p pv3 [pv2,pv3,pv11,pv823], .c 3,
  .p pv2 [pv2,pv157,pv173], .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv1811], .c 3, .c 5, .c 67,
  .c 3, .c 7, .c 31, .c 3, .p pv2 [pv2,pv29,pv937], .c 17, .c 3, .c 13, .c 5, .c 3, .c 19,
  .p pv7 [pv2,pv3,pv5,pv151], .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv17,pv41], .c 3,
  .p pv7 [pv2,pv5,pv5437], .c 11, .c 3, .p pv5 [pv2,pv7,pv971], .c 13, .c 3, .c 7, .c 5, .c 3,
  .c 137, .c 109, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv17], .p pv2 [pv2,pv3,pv9067], .c 3,
  .c 41, .p pv7 [pv2,pv3,pv2267], .c 3, .p pv2 [pv2,pv61,pv223], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv13,pv23], .p pv2 [pv2,pv3,pv5,pv907], .c 3, .c 5, .c 37, .c 3, .c 13, .c 29,
  .c 3, .p pv2 [pv2,pv31,pv439], .c 7, .c 3, .p pv2 [pv2,pv163,pv167], .c 5, .c 3,
  .p pv3 [pv2,pv41,pv83], .c 17, .c 3, .c 5, .c 13, .c 3, .c 11, .c 107, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv17,pv89], .c 3, .c 19, .c 5, .c 3, .c 157, .c 7, .c 3, .c 5, .c 23, .c 3,
  .c 29, .p pv2 [pv2,pv3,pv19,pv239], .c 3, .p pv3 [pv2,pv13,pv131], .p pv3 [pv2,pv3,pv31,pv293],
  .c 3, .p pv7 [pv2,pv7,pv17,pv229], .c 5, .c 3, .c 7, .c 19, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv11,pv59], .c 3, .p pv3 [pv2,pv5,pv29,pv47], .c 7, .c 3, .c 11, .c 31,
]
private theorem h0006c20 : checkBlock 54275 128 b0006c20 = true := by
  decide +kernel

private def b0006c21 : List Row := [
  .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv11,pv37,pv67], .p pv2 [pv2,pv3,pv5,pv101], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv9091], .c 3, .c 7, .c 17, .c 3, .c 89, .p pv3 [pv2,pv3,pv7,pv433], .c 3,
  .p pv2 [pv2,pv27281], .c 5, .c 3, .c 197, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv379], .c 3,
  .p pv13 [pv2,pv5,pv2729], .p pv5 [pv2,pv3,pv11,pv827], .c 3, .c 13, .c 79, .c 3, .c 7, .c 5,
  .c 3, .c 71, .p pv41 [pv2,pv3,pv5,pv7,pv13], .c 3, .c 5, .c 7, .c 3, .c 97, .c 13, .c 3,
  .p pv3 [pv2,pv6827], .c 193, .c 3, .p pv5 [pv2,pv31,pv881], .c 5, .c 3, .p pv3 [pv2,pv7,pv1951],
  .p pv11 [pv2,pv3,pv5,pv607], .c 3, .c 5, .c 11, .c 3, .c 101, .c 53, .c 3,
  .p pv5 [pv2,pv89,pv307], .c 7, .c 3, .c 31, .c 5, .c 3, .c 11, .c 47, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv3037], .c 3, .c 23, .p pv5 [pv2,pv3,pv17,pv67], .c 3, .c 7,
  .p pv7 [pv2,pv3,pv13,pv701], .c 3, .c 149, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 83, .c 3,
  .c 19, .c 11, .c 3, .c 227, .p pv2 [pv2,pv3,pv47,pv97], .c 3, .p pv5 [pv2,pv7,pv977], .c 5,
  .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv19], .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv1303], .c 3, .c 229,
  .c 7, .c 3, .c 127, .c 19, .c 3, .c 13, .c 5, .c 3, .c 53, .p pv31 [pv2,pv3,pv5,pv73], .c 3,
  .c 5, .c 17, .c 3, .c 7, .c 23, .c 3, .p pv5 [pv2,pv139,pv197], .c 11, .c 3,
  .p pv2 [pv2,pv13693], .c 5, .c 3, .p pv2 [pv2,pv61,pv449], .c 29, .c 3, .c 5,
]
private theorem h0006c21 : checkBlock 54531 128 b0006c21 = true := by
  decide +kernel

private def b0006c22 : List Row := [
  .p pv2 [pv2,pv3,pv23,pv397], .c 3, .c 11, .c 157, .c 3, .c 37, .p pv3 [pv2,pv3,pv9133], .c 3,
  .c 7, .c 5, .c 3, .c 23, .c 59, .c 3, .c 5, .c 7, .c 3, .c 13, .c 73, .c 3, .c 109,
  .p pv2 [pv2,pv3,pv1523], .c 3, .p pv3 [pv2,pv23,pv149], .c 5, .c 3, .c 29, .c 173, .c 3, .c 5,
  .c 13, .c 3, .p pv11 [pv2,pv5,pv1097], .c 19, .c 3, .c 11, .c 7, .c 3, .c 83, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv29,pv43], .c 37, .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv269], .c 3,
  .p pv3 [pv2,pv5,pv7], .c 71, .c 3, .c 7, .c 131, .c 3, .c 17, .c 5, .c 3, .c 13, .c 7, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv9151], .c 3, .c 43, .c 89, .c 3, .p pv2 [pv2,pv13729],
  .p pv3 [pv2,pv3,pv113], .c 3, .c 11, .c 5, .c 3, .c 7, .c 163, .c 3, .c 5, .c 137, .c 3,
  .p pv2 [pv2,pv5,pv41,pv67], .c 7, .c 3, .c 23, .p pv2 [pv2,pv3,pv19,pv241], .c 3, .c 179, .c 5,
  .c 3, .p pv7 [pv2,pv27479], .c 17, .c 3, .c 5, .c 11, .c 3, .c 7, .p pv17 [pv2,pv3,pv509], .c 3,
  .c 13, .p pv3 [pv2,pv3,pv7,pv11,pv17], .c 3, .p pv5 [pv2,pv37,pv743], .c 5, .c 3, .c 11, .c 127,
  .c 3, .c 5, .c 43, .c 3, .p pv3 [pv2,pv5,pv11], .c 13, .c 3, .c 67, .p pv7 [pv2,pv3,pv191],
  .c 3, .c 7, .c 5, .c 3, .c 37, .p pv11 [pv2,pv3,pv5,pv7,pv131], .c 3, .c 5, .c 7, .c 3, .c 113,
  .c 11, .c 3, .c 47, .c 23, .c 3,
]
private theorem h0006c22 : checkBlock 54787 128 b0006c22 = true := by
  decide +kernel

private def b0006c23 : List Row := [
  .c 19, .c 5, .c 3, .p pv13 [pv2,pv7,pv983], .p pv2 [pv2,pv3,pv5,pv367], .c 3, .c 5,
  .p pv13 [pv2,pv3,pv31,pv37], .c 3, .p pv2 [pv2,pv5,pv2753], .c 17, .c 3, .c 53, .c 7, .c 3,
  .p pv3 [pv2,pv1721], .c 5, .c 3, .p pv13 [pv2,pv27539], .c 13, .c 3, .c 5, .c 31, .c 3, .c 89,
  .c 37, .c 3, .c 7, .c 11, .c 3, .p pv5 [pv2,pv27551], .c 5, .c 3, .p pv2 [pv2,pv23,pv599], .c 7,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv1531], .c 3, .c 11, .c 199, .c 3, .p pv5 [pv2,pv43,pv641], .c 29,
  .c 3, .c 13, .c 5, .c 3, .c 7, .c 67, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv13,pv101], .c 3, .c 131,
  .c 7, .c 3, .c 19, .c 13, .c 3, .p pv2 [pv2,pv27581], .c 5, .c 3, .c 43,
  .p pv17 [pv2,pv3,pv5,pv613], .c 3, .c 5, .c 23, .c 3, .c 7, .c 139, .c 3, .c 11, .c 229, .c 3,
  .c 97, .c 5, .c 3, .c 17, .p pv7 [pv2,pv3,pv5,pv23], .c 3, .c 5, .p pv5 [pv2,pv3,pv3067], .c 3,
  .c 13, .p pv2 [pv2,pv3,pv43,pv107], .c 3, .p pv3 [pv2,pv7,pv17,pv29], .p pv2 [pv2,pv3,pv9203],
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv13807], .c 11, .c 3, .c 5, .c 7, .c 3, .c 37,
  .p pv2 [pv2,pv3,pv11,pv31], .c 3, .c 101, .p pv11 [pv2,pv3,pv1151], .c 3, .c 11, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv3947], .c 73, .c 3, .c 5, .c 17, .c 3, .c 19, .c 31, .c 3, .c 167, .c 7, .c 3,
  .c 59, .c 5, .c 3, .c 13, .p pv11 [pv2,pv3,pv5,pv19,pv97], .c 3, .c 5, .c 11,
]
private theorem h0006c23 : checkBlock 55043 128 b0006c23 = true := by
  decide +kernel

private def b0006c24 : List Row := [
  .c 3, .c 17, .c 29, .c 3, .c 7, .c 19, .c 3, .p pv3 [pv2,pv3457], .c 5, .c 3, .c 11, .c 7, .c 3,
  .c 5, .c 61, .c 3, .p pv2 [pv2,pv5,pv11,pv503], .p pv7 [pv2,pv3,pv29,pv53], .c 3,
  .p pv3 [pv2,pv6917], .p pv2 [pv2,pv3,pv23,pv401], .c 3, .p pv7 [pv2,pv7,pv59,pv67], .c 5, .c 3,
  .c 7, .p pv7 [pv2,pv3,pv5,pv41], .c 3, .c 5, .c 197, .c 3, .c 23, .c 7, .c 3, .c 13, .c 17,
  .c 3, .p pv2 [pv2,pv109,pv127], .c 5, .c 3, .c 79, .p pv11 [pv2,pv3,pv5,pv13,pv71], .c 3, .c 5,
  .c 97, .c 3, .c 7, .c 13, .c 3, .c 31, .p pv11 [pv2,pv3,pv7,pv1319], .c 3, .c 17, .c 5, .c 3,
  .c 67, .p pv2 [pv2,pv3,pv5,pv1847], .c 3, .c 5, .c 151, .c 3, .c 157, .c 19, .c 3, .c 43, .c 11,
  .c 3, .c 7, .c 5, .c 3, .p pv13 [pv2,pv53,pv523], .p pv59 [pv2,pv3,pv5,pv7,pv11], .c 3, .c 5,
  .c 7, .c 3, .c 11, .c 23, .c 3, .p pv3 [pv2,pv1733], .c 31, .c 3, .c 37, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv283], .c 13, .c 3, .c 5, .c 29, .c 3, .c 109, .c 113, .c 3,
  .p pv5 [pv2,pv27743], .c 7, .c 3, .c 211, .c 5, .c 3, .c 19, .p pv7 [pv2,pv3,pv5,pv37], .c 3,
  .c 5, .c 47, .c 3, .p pv11 [pv2,pv5,pv7,pv13,pv61], .c 43, .c 3, .c 7, .c 59, .c 3, .c 13, .c 5,
  .c 3, .p pv3 [pv2,pv11,pv631], .c 7, .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv2777], .c 67,
  .c 3, .p pv2 [pv2,pv27773], .c 13, .c 3, .c 73,
]
private theorem h0006c24 : checkBlock 55299 128 b0006c24 = true := by
  decide +kernel

private def b0006c25 : List Row := [
  .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 181, .c 3, .c 61, .c 7, .c 3, .c 149,
  .p pv2 [pv2,pv3,pv59,pv157], .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv13,pv1069], .c 23, .c 3,
  .c 5, .c 53, .c 3, .c 7, .p pv2 [pv2,pv3,pv3089], .c 3, .c 17, .p pv13 [pv2,pv3,pv7,pv331],
  .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv27809], .p pv2 [pv2,pv3,pv5,pv103], .c 3, .c 5, .c 11,
  .c 3, .p pv7 [pv2,pv5,pv5563], .p pv5 [pv2,pv3,pv19,pv61], .c 3, .c 23,
  .p pv3 [pv2,pv3,pv11,pv281], .c 3, .c 7, .c 5, .c 3, .c 11, .c 19, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv11,pv23], .p pv3 [pv2,pv3,pv9277], .c 3, .p pv2 [pv2,pv13,pv2141], .c 179,
  .c 3, .p pv3 [pv2,pv6959], .c 5, .c 3, .c 13, .p pv11 [pv2,pv3,pv5,pv29], .c 3, .c 5, .c 233,
  .c 3, .p pv2 [pv2,pv5,pv5569], .c 11, .c 3, .p pv3 [pv2,pv59], .c 7, .c 3, .c 53, .c 5, .c 3,
  .c 17, .p pv3 [pv2,pv3,pv5,pv619], .c 3, .c 5, .p pv2 [pv2,pv3,pv4643], .c 3,
  .p pv3 [pv2,pv5,pv7,pv199], .c 103, .c 3, .c 7, .c 23, .c 3, .p pv2 [pv2,pv13933], .c 5, .c 3,
  .c 139, .c 7, .c 3, .c 5, .c 107, .c 3, .c 197, .c 127, .c 3, .c 13, .c 11, .c 3,
  .p pv2 [pv2,pv7,pv569], .c 5, .c 3, .c 7, .c 43, .c 3, .c 5, .c 17, .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv27893], .c 47, .c 3, .p pv3 [pv2,pv11,pv317], .c 5, .c 3,
  .p pv7 [pv2,pv23,pv1213], .c 41, .c 3, .c 5, .p pv3 [pv2,pv3,pv71,pv131], .c 3,
]
private theorem h0006c25 : checkBlock 55555 128 b0006c25 = true := by
  decide +kernel

private def b0006c26 : List Row := [
  .c 7, .p pv2 [pv2,pv3,pv4651], .c 3, .p pv3 [pv2,pv6977], .p pv2 [pv2,pv3,pv7,pv443], .c 3,
  .p pv5 [pv2,pv13,pv19,pv113], .c 5, .c 3, .p pv2 [pv2,pv17,pv821], .c 31, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv47], .c 3, .c 19, .p pv2 [pv2,pv3,pv41,pv227], .c 3, .c 11,
  .p pv41 [pv2,pv3,pv13,pv179], .c 3, .c 7, .c 5, .c 3, .c 83, .c 13, .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv37,pv151], .c 59, .c 3, .c 71, .c 17, .c 3, .c 29, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv499], .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv137], .c 3,
  .p pv2 [pv2,pv5,pv13,pv43], .p pv11 [pv2,pv3,pv7,pv11], .c 3, .c 37, .c 7, .c 3, .c 11, .c 5,
  .c 3, .c 199, .p pv37 [pv2,pv3,pv5,pv233], .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv239], .c 3,
  .p pv13 [pv2,pv5,pv7,pv17,pv47], .p pv2 [pv2,pv3,pv59,pv79], .c 3, .c 7, .c 13, .c 3, .c 43,
  .c 5, .c 3, .p pv2 [pv2,pv71,pv197], .c 7, .c 3, .c 5, .c 11, .c 3, .c 107, .c 191, .c 3,
  .p pv5 [pv2,pv27983], .c 97, .c 3, .c 223, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv31,pv43], .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv13999], .c 29, .c 3,
  .p pv2 [pv2,pv28001], .c 5, .c 3, .p pv3 [pv2,pv7001], .c 79, .c 3, .c 5, .c 13, .c 3, .c 7,
  .c 11, .c 3, .c 179, .c 43, .c 3, .c 137, .c 5, .c 3, .p pv7 [pv2,pv28019],
  .p pv7 [pv2,pv3,pv5,pv467], .c 3, .c 5, .c 41, .c 3, .c 23, .p pv2 [pv2,pv3,pv173], .c 3, .c 29,
  .c 61, .c 3, .c 7, .c 5,
]
private theorem h0006c26 : checkBlock 55811 128 b0006c26 = true := by
  decide +kernel

private def b0006c27 : List Row := [
  .c 3, .c 13, .c 47, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv701], .c 17, .c 3,
  .p pv5 [pv2,pv29,pv967], .c 11, .c 3, .p pv2 [pv2,pv37,pv379], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv4007], .p pv7 [pv2,pv3,pv5,pv11,pv17], .c 3, .c 5, .c 19, .c 3, .c 11,
  .p pv5 [pv2,pv3,pv7,pv167], .c 3, .c 17, .c 7, .c 3, .p pv2 [pv2,pv11,pv2551], .c 5, .c 3,
  .c 37, .p pv2 [pv2,pv3,pv5,pv1871], .c 3, .c 5, .c 73, .c 3, .c 31, .c 23, .c 3, .c 7,
  .p pv37 [pv2,pv3,pv4679], .c 3, .c 233, .c 5, .c 3, .c 89, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv23,pv37], .c 3, .p pv2 [pv2,pv5,pv41,pv137], .c 13, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv3121], .c 3, .c 19, .c 5, .c 3, .c 7, .c 83, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv7,pv223], .c 3, .c 43, .c 7, .c 3, .p pv5 [pv2,pv157,pv179],
  .p pv7 [pv2,pv3,pv1171], .c 3, .c 67, .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .c 59, .c 3, .c 7,
  .c 53, .c 3, .p pv2 [pv2,pv17,pv827], .p pv3 [pv2,pv3,pv7,pv13,pv103], .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv79,pv89], .c 13, .c 3, .c 5, .c 101, .c 3, .c 127, .p pv3 [pv2,pv3,pv9377], .c 3,
  .p pv2 [pv2,pv7,pv4019], .p pv2 [pv2,pv3,pv521], .c 3, .c 7, .c 5, .c 3, .c 167, .c 23, .c 3,
  .c 5, .c 7, .c 3, .c 181, .c 41, .c 3, .c 19, .p pv17 [pv2,pv3,pv11,pv853], .c 3, .c 13, .c 5,
  .c 3, .c 11, .p pv13 [pv2,pv3,pv5,pv1877], .c 3, .c 5, .c 199, .c 3, .c 17,
]
private theorem h0006c27 : checkBlock 56067 128 b0006c27 = true := by
  decide +kernel

private def b0006c28 : List Row := [
  .c 151, .c 3, .c 23, .c 7, .c 3, .p pv2 [pv2,pv14083], .c 5, .c 3, .c 53, .c 103, .c 3, .c 5,
  .c 29, .c 3, .c 37, .c 11, .c 3, .c 7, .p pv3 [pv2,pv3,pv31,pv101], .c 3, .c 157, .c 5, .c 3,
  .p pv3 [pv2,pv13,pv271], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv29], .c 3, .c 13,
  .p pv3 [pv2,pv3,pv9397], .c 3, .c 113, .c 17, .c 3, .p pv3 [pv2,pv7,pv19,pv53], .c 5, .c 3,
  .c 7, .p pv13 [pv2,pv3,pv5,pv47], .c 3, .c 5, .c 13, .c 3, .c 19, .c 7, .c 3,
  .p pv3 [pv2,pv41,pv43], .c 11, .c 3, .c 17, .c 5, .c 3, .c 73, .p pv3 [pv2,pv3,pv5,pv11,pv19],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv4703], .c 3, .c 7, .p pv5 [pv2,pv3,pv23,pv409], .c 3, .c 47,
  .c 19, .c 3, .p pv2 [pv2,pv11,pv1283], .c 5, .c 3, .c 13, .c 131, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv3137], .c 3, .c 149, .p pv5 [pv2,pv3,pv13,pv181], .c 3,
  .p pv2 [pv2,pv7,pv2017], .p pv13 [pv2,pv3,pv9413], .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv23,pv307], .c 17, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv113],
  .p pv3 [pv2,pv3,pv43,pv73], .c 3, .c 11, .p pv2 [pv2,pv3,pv17,pv277], .c 3, .c 31, .c 5, .c 3,
  .p pv13 [pv2,pv7,pv11,pv367], .c 29, .c 3, .c 5, .p pv3 [pv2,pv3,pv9421], .c 3,
  .p pv2 [pv2,pv5,pv5653], .p pv5 [pv2,pv3,pv7,pv673], .c 3, .c 13, .c 7, .c 3,
  .p pv5 [pv2,pv17,pv1663], .c 5, .c 3, .c 193, .c 11, .c 3, .c 5, .c 23, .c 3, .c 163, .c 13,
  .c 3, .c 7, .p pv11 [pv2,pv3,pv2357], .c 3, .c 11, .c 5, .c 3,
]
private theorem h0006c28 : checkBlock 56323 128 b0006c28 = true := by
  decide +kernel

private def b0006c29 : List Row := [
  .c 29, .c 7, .c 3, .c 5, .c 71, .c 3, .p pv19 [pv2,pv5,pv5659], .c 17, .c 3,
  .p pv2 [pv2,pv14149], .p pv3 [pv2,pv3,pv9433], .c 3, .c 23, .c 5, .c 3, .c 7,
  .p pv29 [pv2,pv3,pv5,pv17,pv37], .c 3, .c 5, .c 11, .c 3, .c 41, .c 7, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv11,pv13], .c 3, .p pv3 [pv2,pv7079], .c 5, .c 3, .c 11, .c 13, .c 3, .c 5,
  .c 37, .c 3, .c 7, .c 181, .c 3, .c 53, .p pv2 [pv2,pv3,pv7,pv19,pv71], .c 3,
  .p pv5 [pv2,pv41,pv691], .c 5, .c 3, .c 61, .p pv3 [pv2,pv3,pv5,pv1889], .c 3, .c 5, .c 19,
  .c 3, .p pv3 [pv2,pv5,pv13,pv109], .c 11, .c 3, .p pv5 [pv2,pv7,pv4049], .c 83, .c 3, .c 7,
  .c 5, .c 3, .c 31, .p pv2 [pv2,pv3,pv5,pv7], .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv53,pv107], .p pv5 [pv2,pv3,pv17,pv139], .c 3, .c 43, .c 13, .c 3, .c 131,
  .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv31,pv61], .c 3, .c 5, .p pv11 [pv2,pv3,pv197], .c 3,
  .c 23, .c 179, .c 3, .p pv2 [pv2,pv17,pv1669], .c 7, .c 3, .c 19, .c 5, .c 3, .c 211, .c 31,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv9461], .c 3, .c 11, .p pv2 [pv2,pv3,pv19,pv83], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv9463], .c 3, .p pv5 [pv2,pv11,pv29,pv89], .c 5, .c 3, .c 109, .c 7, .c 3,
  .c 5, .c 13, .c 3, .c 79, .c 43, .c 3, .p pv5 [pv2,pv28403], .p pv17 [pv2,pv3,pv263], .c 3,
  .p pv3 [pv2,pv7,pv2029], .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv947], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv11,pv41], .c 3, .c 17, .c 7,
]
private theorem h0006c29 : checkBlock 56579 128 b0006c29 = true := by
  decide +kernel

private def b0006c30 : List Row := [
  .c 3, .c 11, .c 113, .c 3, .p pv2 [pv2,pv97,pv293], .c 5, .c 3, .c 13, .c 139, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv23,pv103], .c 3, .c 7, .c 101, .c 3, .c 19, .c 29, .c 3, .p pv3 [pv2,pv7109],
  .c 5, .c 3, .c 23, .c 11, .c 3, .c 5, .c 163, .c 3, .p pv2 [pv2,pv5,pv5689],
  .p pv2 [pv2,pv3,pv11,pv431], .c 3, .p pv5 [pv2,pv7,pv127], .c 17, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv41,pv347], .p pv3 [pv2,pv3,pv5,pv7,pv271], .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv1423], .p pv3 [pv2,pv3,pv53,pv179], .c 3, .c 13, .p pv29 [pv2,pv3,pv593],
  .c 3, .c 17, .c 5, .c 3, .c 97, .p pv2 [pv2,pv3,pv5,pv13,pv73], .c 3, .c 5, .c 11, .c 3,
  .p pv13 [pv2,pv5,pv17,pv67], .c 13, .c 3, .p pv2 [pv2,pv29,pv491], .c 7, .c 3,
  .p pv2 [pv2,pv19,pv1499], .c 5, .c 3, .c 11, .c 23, .c 3, .c 5, .c 227, .c 3, .c 19,
  .p pv3 [pv2,pv3,pv9497], .c 3, .c 7, .p pv31 [pv2,pv3,pv1583], .c 3, .p pv3 [pv2,pv13,pv137],
  .c 5, .c 3, .p pv13 [pv2,pv28499], .c 7, .c 3, .c 5, .c 109, .c 3, .c 47, .c 11, .c 3, .c 23,
  .c 19, .c 3, .c 127, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv97], .c 3,
  .p pv11 [pv2,pv5,pv23,pv31], .c 7, .c 3, .p pv7 [pv2,pv11,pv2593], .c 89, .c 3, .c 59, .c 5,
  .c 3, .p pv2 [pv2,pv47,pv607], .c 43, .c 3, .c 5, .c 149, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv29,pv41], .c 3, .p pv2 [pv2,pv19,pv751], .c 11, .c 3, .c 13, .c 5, .c 3,
  .p pv3 [pv2,pv223],
]
private theorem h0006c30 : checkBlock 56835 128 b0006c30 = true := by
  decide +kernel

private def b0006c31 : List Row := [
  .c 37, .c 3, .c 5, .p pv7 [pv2,pv3,pv13,pv61], .c 3, .c 11, .c 17, .c 3,
  .p pv2 [pv2,pv7,pv4079], .c 13, .c 3, .c 7, .c 5, .c 3, .p pv19 [pv2,pv28559], .c 239, .c 3,
  .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv29,pv197], .c 19, .c 3, .c 17, .p pv2 [pv2,pv3,pv89,pv107],
  .c 3, .p pv5 [pv2,pv28571], .c 5, .c 3, .p pv2 [pv2,pv7,pv13,pv157], .c 67, .c 3, .c 5, .c 61,
  .c 3, .c 13, .p pv2 [pv2,pv3,pv7,pv1361], .c 3, .c 11, .c 7, .c 3, .p pv2 [pv2,pv14293], .c 5,
  .c 3, .p pv2 [pv2,pv11,pv23,pv113], .c 211, .c 3, .c 5, .c 13, .c 3,
  .p pv7 [pv2,pv5,pv7,pv19,pv43], .p pv5 [pv2,pv3,pv2383], .c 3, .c 7, .c 47, .c 3,
  .p pv2 [pv2,pv37,pv773], .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 29, .c 3,
  .p pv2 [pv2,pv5,pv2861], .p pv3 [pv2,pv3,pv11,pv17], .c 3, .c 89, .c 151, .c 3, .c 11, .c 5,
  .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv53], .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv229], .c 7,
  .c 3, .c 31, .p pv2 [pv2,pv3,pv3181], .c 3, .c 173, .c 5, .c 3, .p pv2 [pv2,pv103,pv139],
  .p pv3 [pv2,pv3,pv5,pv23,pv83], .c 3, .c 5, .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv9547], .c 3,
  .p pv5 [pv2,pv28643], .c 59, .c 3, .c 23, .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv191], .c 3,
  .c 5, .c 17, .c 3, .c 223, .c 37, .c 3, .c 13, .c 31, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv3583], .p pv2 [pv2,pv3,pv5,pv7,pv13], .c 3, .c 5, .c 7, .c 3, .c 17, .c 11, .c 3,
]
private theorem h0006c31 : checkBlock 57091 128 b0006c31 = true := by
  decide +kernel

def rows0006 : List Row :=
  b0006c00 ++ b0006c01 ++ b0006c02 ++ b0006c03 ++ b0006c04 ++ b0006c05 ++ b0006c06 ++ b0006c07 ++
  b0006c08 ++ b0006c09 ++ b0006c10 ++ b0006c11 ++ b0006c12 ++ b0006c13 ++ b0006c14 ++ b0006c15 ++
  b0006c16 ++ b0006c17 ++ b0006c18 ++ b0006c19 ++ b0006c20 ++ b0006c21 ++ b0006c22 ++ b0006c23 ++
  b0006c24 ++ b0006c25 ++ b0006c26 ++ b0006c27 ++ b0006c28 ++ b0006c29 ++ b0006c30 ++ b0006c31

attribute [local irreducible] checkBlock checkRows checkPrime

theorem checked0006 : checkBlock 49155 4096 rows0006 = true :=
  checkBlock_append h0006c00 (
    checkBlock_append h0006c01 (
    checkBlock_append h0006c02 (
    checkBlock_append h0006c03 (
    checkBlock_append h0006c04 (
    checkBlock_append h0006c05 (
    checkBlock_append h0006c06 (
    checkBlock_append h0006c07 (
    checkBlock_append h0006c08 (
    checkBlock_append h0006c09 (
    checkBlock_append h0006c10 (
    checkBlock_append h0006c11 (
    checkBlock_append h0006c12 (
    checkBlock_append h0006c13 (
    checkBlock_append h0006c14 (
    checkBlock_append h0006c15 (
    checkBlock_append h0006c16 (
    checkBlock_append h0006c17 (
    checkBlock_append h0006c18 (
    checkBlock_append h0006c19 (
    checkBlock_append h0006c20 (
    checkBlock_append h0006c21 (
    checkBlock_append h0006c22 (
    checkBlock_append h0006c23 (
    checkBlock_append h0006c24 (
    checkBlock_append h0006c25 (
    checkBlock_append h0006c26 (
    checkBlock_append h0006c27 (
    checkBlock_append h0006c28 (
    checkBlock_append h0006c29 (
    checkBlock_append h0006c30 (
    h0006c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
