/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks03/Block0247
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks03/Block0247.checked0247
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table138

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0247c00 : List Row := [
  .c 7, .c 71, .c 3, .p pv3 [pv2,pv31,pv41,pv199], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv29,pv401], .c 3, .c 43, .p pv23 [pv2,pv3,pv56207], .c 3, .c 83, .c 17, .c 3,
  .c 13, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 107, .c 3, .c 19, .c 7, .c 3, .c 53, .c 13, .c 3,
  .c 17, .c 5, .c 3, .c 761, .p pv2 [pv2,pv3,pv5,pv19,pv71], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv79,pv1423], .c 3, .c 7, .c 613, .c 3, .c 23, .c 19, .c 3, .c 59, .c 5, .c 3,
  .p pv11 [pv2,pv13,pv19457], .p pv29 [pv2,pv3,pv5,pv37,pv1823], .c 3, .c 5, .c 43, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv12491], .c 3, .p pv2 [pv2,pv7,pv144539], .c 11, .c 3, .c 7, .c 5, .c 3,
  .c 1303, .c 17, .c 3, .c 5, .c 7, .c 3, .c 11, .c 157, .c 3, .p pv3 [pv2,pv19,pv13313],
  .p pv2 [pv2,pv3,pv17,pv389], .c 3, .c 797, .c 5, .c 3, .c 829, .c 29, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv41,pv457], .c 3, .c 67, .p pv2 [pv2,pv3,pv7,pv6883], .c 3,
  .p pv5 [pv2,pv13,pv5987], .c 7, .c 3, .c 239, .c 5, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv5,pv29,pv1163], .c 3, .c 5, .c 137, .c 3, .c 199, .c 19, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv367,pv919], .c 3, .c 449, .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .c 881, .c 3,
  .p pv2 [pv2,pv5,pv101183], .c 17, .c 3, .p pv2 [pv2,pv43,pv23531], .c 827, .c 3, .c 229, .c 5,
  .c 3, .c 7, .c 11,
]
private theorem h0247c00 : checkBlock 2023427 128 b0247c00 = true := by
  decide +kernel

private def b0247c01 : List Row := [
  .c 3, .c 5, .c 269, .c 3, .c 107, .c 7, .c 3, .c 13, .c 53, .c 3, .c 11, .c 5, .c 3, .c 19,
  .c 31, .c 3, .c 5, .c 113, .c 3, .c 7, .c 13, .c 3, .p pv5 [pv2,pv47,pv21529], .c 683, .c 3,
  .c 283, .c 5, .c 3, .c 947, .p pv7 [pv2,pv3,pv5,pv11243], .c 3, .c 5, .c 11, .c 3, .c 293,
  .p pv11 [pv2,pv3,pv37,pv43,pv53], .c 3, .c 823, .c 59, .c 3, .c 7, .c 5, .c 3, .c 11, .c 89,
  .c 3, .c 5, .c 7, .c 3, .c 197, .p pv11 [pv2,pv3,pv17,pv19841], .c 3, .c 701, .c 37, .c 3,
  .c 23, .c 5, .c 3, .c 17, .c 13, .c 3, .c 5, .c 1361, .c 3, .p pv11 [pv2,pv5,pv202381], .c 11,
  .c 3, .p pv5 [pv2,pv17,pv23,pv647], .c 7, .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv271,pv1867],
  .p pv3 [pv2,pv3,pv5,pv113,pv199], .c 3, .c 5, .p pv2 [pv2,pv3,pv191,pv883], .c 3,
  .p pv3 [pv2,pv5,pv7,pv13,pv139], .p pv2 [pv2,pv3,pv19,pv41,pv433], .c 3, .c 7,
  .p pv23 [pv2,pv3,pv28109], .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv53,pv61,pv313], .c 7, .c 3,
  .c 5, .c 17, .c 3, .c 1217, .c 167, .c 3, .c 59, .c 11, .c 3, .c 41, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv11,pv6133], .c 3, .c 5, .c 31, .c 3, .c 11, .c 7, .c 3,
  .p pv2 [pv2,pv397,pv2549], .c 593, .c 3, .p pv5 [pv2,pv11,pv109,pv211], .c 5, .c 3, .c 61,
  .p pv17 [pv2,pv3,pv5,pv937], .c 3, .c 5, .c 173, .c 3, .c 7, .c 569, .c 3, .c 19,
]
private theorem h0247c01 : checkBlock 2023683 128 b0247c01 = true := by
  decide +kernel

private def b0247c02 : List Row := [
  .c 29, .c 3, .c 113, .c 5, .c 3, .c 89, .p pv3 [pv2,pv3,pv5,pv103,pv131], .c 3, .c 5, .c 13,
  .c 3, .c 47, .p pv2 [pv2,pv3,pv337327], .c 3, .c 11, .c 17, .c 3, .c 7, .c 5, .c 3, .c 139,
  .p pv13 [pv2,pv3,pv5,pv7,pv61,pv79], .c 3, .c 5, .c 7, .c 3, .c 193, .p pv7 [pv2,pv3,pv28111],
  .c 3, .c 29, .c 127, .c 3, .c 17, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 53, .c 3, .c 31,
  .c 23, .c 3, .c 191, .c 7, .c 3, .c 11, .c 5, .c 3, .c 277, .c 61, .c 3, .c 5, .c 41, .c 3,
  .c 19, .c 43, .c 3, .c 7, .c 79, .c 3, .p pv5 [pv2,pv1012031], .c 5, .c 3, .c 23, .c 7, .c 3,
  .c 5, .c 11, .c 3, .c 131, .c 31, .c 3, .c 13, .c 19, .c 3, .p pv2 [pv2,pv7,pv23,pv449], .c 5,
  .c 3, .c 7, .p pv19 [pv2,pv3,pv5,pv13,pv173], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv48193], .c 3,
  .p pv11 [pv2,pv5,pv11,pv18401], .c 7, .c 3, .p pv2 [pv2,pv577,pv877], .c 107, .c 3, .c 53, .c 5,
  .c 3, .c 41, .c 229, .c 3, .c 5, .c 67, .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv19,pv53267],
  .c 47, .c 3, .p pv3 [pv2,pv13,pv19463], .c 5, .c 3, .c 37, .c 23, .c 3, .c 5,
  .p pv17 [pv2,pv3,pv337361], .c 3, .c 29, .c 17, .c 3, .p pv3 [pv2,pv7,pv11,pv31,pv53],
  .p pv3 [pv2,pv3,pv13,pv25951], .c 3, .c 7, .c 5, .c 3, .c 419, .c 13, .c 3,
]
private theorem h0247c02 : checkBlock 2023939 128 b0247c02 = true := by
  decide +kernel

private def b0247c03 : List Row := [
  .c 5, .c 7, .c 3, .c 157, .c 19, .c 3, .c 17, .c 11, .c 3, .p pv2 [pv2,pv131,pv3863], .c 5,
  .c 3, .p pv2 [pv2,pv7,pv191,pv757], .p pv7 [pv2,pv3,pv5,pv11,pv3067], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv107,pv1051], .c 3, .c 11, .c 37, .c 3, .p pv2 [pv2,pv463,pv1093], .c 7, .c 3,
  .c 13, .c 5, .c 3, .p pv3 [pv2,pv401,pv631], .c 461, .c 3, .c 5, .c 139, .c 3,
  .p pv2 [pv2,pv5,pv7,pv19,pv761], .p pv5 [pv2,pv3,pv112459], .c 3, .c 7, .c 13, .c 3, .c 173,
  .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 29, .c 3, .c 929, .c 41, .c 3, .c 11, .c 23, .c 3,
  .c 397, .c 5, .c 3, .c 7, .c 43, .c 3, .c 5, .c 19, .c 3, .c 13, .c 7, .c 3,
  .p pv5 [pv2,pv17,pv59539], .p pv11 [pv2,pv3,pv84347], .c 3, .c 107, .c 5, .c 3,
  .p pv2 [pv2,pv67,pv15107], .c 11, .c 3, .c 5, .c 13, .c 3, .c 7, .c 1399, .c 3,
  .p pv2 [pv2,pv389,pv1301], .c 337, .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv23,pv5501],
  .p pv2 [pv2,pv3,pv5,pv83,pv271], .c 3, .c 5, .c 17, .c 3, .c 37, .p pv19 [pv2,pv3,pv337397],
  .c 3, .p pv7 [pv2,pv7,pv13,pv227], .c 257, .c 3, .c 7, .c 5, .c 3, .c 13, .c 359, .c 3, .c 5,
  .c 7, .c 3, .c 17, .p pv5 [pv2,pv3,pv13,pv19,pv683], .c 3, .p pv3 [pv2,pv41,pv1543],
  .p pv2 [pv2,pv3,pv11,pv37,pv829], .c 3, .c 71, .c 5, .c 3, .c 11, .c 19, .c 3, .c 5, .c 23,
  .c 3, .c 53, .c 499, .c 3, .c 547, .c 7,
]
private theorem h0247c03 : checkBlock 2024195 128 b0247c03 = true := by
  decide +kernel

private def b0247c04 : List Row := [
  .c 3, .c 83, .c 5, .c 3, .c 487, .c 29, .c 3, .c 5, .c 59, .c 3, .p pv7 [pv2,pv5,pv7,pv28921],
  .c 11, .c 3, .c 7, .c 17, .c 3, .c 23, .c 5, .c 3, .p pv3 [pv2,pv19,pv701], .c 7, .c 3, .c 5,
  .c 1213, .c 3, .p pv2 [pv2,pv5,pv4049], .c 13, .c 3, .c 19, .c 73, .c 3, .c 17, .c 5, .c 3,
  .c 7, .c 1193, .c 3, .c 5, .c 1367, .c 3, .p pv11 [pv2,pv5,pv17,pv11909], .c 7, .c 3, .c 233,
  .c 11, .c 3, .c 1307, .c 5, .c 3, .c 349, .p pv3 [pv2,pv3,pv5,pv11,pv409], .c 3, .c 5, .c 919,
  .c 3, .c 7, .c 587, .c 3, .p pv5 [pv2,pv37,pv109,pv251], .c 43, .c 3,
  .p pv2 [pv2,pv11,pv47,pv89], .c 5, .c 3, .c 31, .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv137,pv821],
  .c 3, .p pv7 [pv2,pv5,pv61,pv3319], .c 277, .c 3, .p pv2 [pv2,pv7,pv72307],
  .p pv3 [pv2,pv3,pv17,pv23,pv863], .c 3, .c 7, .c 5, .c 3, .c 1151,
  .p pv2 [pv2,pv3,pv5,pv7,pv31,pv311], .c 3, .c 5, .c 7, .c 3, .c 19, .c 163, .c 3, .c 11,
  .c 1249, .c 3, .c 13, .c 5, .c 3, .p pv7 [pv2,pv7,pv11,pv13147], .c 31, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv13,pv101,pv257], .c 3, .c 61, .c 53, .c 3, .c 1279, .c 7, .c 3, .c 859, .c 5,
  .c 3, .c 179, .c 11, .c 3, .c 5, .c 37, .c 3, .c 97, .c 17, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv42181], .c 3, .c 11, .c 5, .c 3, .c 463, .c 7, .c 3, .c 5,
]
private theorem h0247c04 : checkBlock 2024451 128 b0247c04 = true := by
  decide +kernel

private def b0247c05 : List Row := [
  .c 71, .c 3, .c 13, .c 23, .c 3, .c 17, .c 883, .c 3, .c 137, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv7499], .c 3, .c 5, .c 11, .c 3, .c 43, .c 7, .c 3, .c 101, .c 619, .c 3,
  .c 1019, .c 5, .c 3, .c 11, .c 107, .c 3, .c 5, .p pv3 [pv2,pv3,pv197,pv571], .c 3, .c 7, .c 19,
  .c 3, .c 769, .p pv2 [pv2,pv3,pv7,pv71,pv97], .c 3, .c 1163, .c 5, .c 3, .c 13, .c 191, .c 3,
  .c 5, .c 313, .c 3, .c 73, .c 11, .c 3, .c 47, .c 29, .c 3, .c 7, .c 5, .c 3, .c 17, .c 59,
  .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv19,pv10657], .p pv5 [pv2,pv3,pv5273], .c 3, .c 263,
  .c 89, .c 3, .p pv2 [pv2,pv1012421], .c 5, .c 3, .c 19, .c 23, .c 3, .c 5, .c 937, .c 3,
  .p pv2 [pv2,pv5,pv137,pv739], .p pv3 [pv2,pv3,pv7,pv37,pv1303], .c 3, .c 13, .c 7, .c 3,
  .p pv3 [pv2,pv253109], .c 5, .c 3, .c 631, .p pv7 [pv2,pv3,pv5,pv11,pv13,pv59], .c 3, .c 5,
  .c 17, .c 3, .c 11, .c 13, .c 3, .c 7, .c 37, .c 3, .c 257, .c 5, .c 3,
  .p pv2 [pv2,pv41,pv12347], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv168743], .c 3, .c 17, .c 293,
  .c 3, .c 809, .c 1423, .c 3, .p pv3 [pv2,pv7,pv13,pv5563], .c 5, .c 3, .c 7, .c 67, .c 3, .c 5,
  .c 73, .c 3, .c 31, .c 7, .c 3, .c 11, .c 409, .c 3,
]
private theorem h0247c05 : checkBlock 2024707 128 b0247c05 = true := by
  decide +kernel

private def b0247c06 : List Row := [
  .c 19, .c 5, .c 3, .c 1237, .c 13, .c 3, .c 5, .p pv19 [pv2,pv3,pv42187], .c 3, .c 7, .c 29,
  .c 3, .c 1013, .c 17, .c 3, .c 877, .c 5, .c 3, .c 43, .c 11, .c 3, .c 5, .c 79, .c 3, .c 1039,
  .c 31, .c 3, .c 61, .c 1289, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv181,pv2797], .c 41, .c 3,
  .c 5, .c 7, .c 3, .c 29, .p pv2 [pv2,pv3,pv43,pv47,pv167], .c 3, .c 37, .c 13, .c 3,
  .p pv2 [pv2,pv506263], .c 5, .c 3, .c 149, .c 151, .c 3, .c 5, .c 11, .c 3, .c 569, .c 113,
  .c 3, .c 19, .c 7, .c 3, .c 103, .c 5, .c 3, .c 11, .c 17, .c 3, .c 5, .c 397, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv337517], .c 3, .c 7, .p pv13 [pv2,pv3,pv17,pv1103], .c 3, .c 41, .c 5, .c 3,
  .c 359, .c 7, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv53,pv3821], .c 11, .c 3, .c 31, .c 61,
  .c 3, .c 157, .c 5, .c 3, .c 7, .c 101, .c 3, .c 5, .c 29, .c 3, .c 353, .c 7, .c 3, .c 281,
  .p pv7 [pv2,pv3,pv31,pv1361], .c 3, .c 23, .c 5, .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv11251],
  .c 3, .c 5, .p pv17 [pv2,pv3,pv29,pv103,pv113], .c 3, .c 7, .c 17, .c 3,
  .p pv2 [pv2,pv23,pv22013], .c 11, .c 3, .p pv2 [pv2,pv1012601], .c 5, .c 3, .c 67,
  .p pv3 [pv2,pv3,pv5,pv11,pv17,pv19], .c 3, .c 5, .p pv17 [pv2,pv3,pv293],
]
private theorem h0247c06 : checkBlock 2024963 128 b0247c06 = true := by
  decide +kernel

private def b0247c07 : List Row := [
  .c 3, .c 11, .c 199, .c 3, .c 17, .c 19, .c 3, .c 7, .c 5, .c 3, .c 73,
  .p pv17 [pv2,pv3,pv5,pv7,pv2411], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv8101],
  .p pv5 [pv2,pv3,pv101,pv557], .c 3, .c 13, .p pv2 [pv2,pv3,pv337543], .c 3, .c 97, .c 5, .c 3,
  .c 37, .c 137, .c 3, .c 5, .c 41, .c 3, .p pv7 [pv2,pv5,pv6329], .c 13, .c 3, .c 11, .c 7, .c 3,
  .c 59, .c 5, .c 3, .c 113, .c 269, .c 3, .c 5, .p pv3 [pv2,pv3,pv37,pv3041], .c 3, .c 23,
  .c 317, .c 3, .c 7, .c 251, .c 3, .c 31, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 571, .c 3,
  .p pv3 [pv2,pv5,pv101267], .c 19, .c 3, .p pv2 [pv2,pv17,pv71,pv839],
  .p pv2 [pv2,pv3,pv13,pv12983], .c 3, .c 11, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv7,pv83], .c 3, .c 47, .c 7, .c 3, .p pv3 [pv2,pv167,pv379], .c 467, .c 3,
  .c 61, .c 5, .c 3, .c 29, .c 131, .c 3, .c 5, .c 11, .c 3, .c 7, .c 23, .c 3, .c 821,
  .p pv31 [pv2,pv3,pv7,pv11,pv137], .c 3, .c 13, .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv33757],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv23,pv1129], .c 3, .c 17, .c 487, .c 3,
  .p pv2 [pv2,pv7,pv72337], .c 13, .c 3, .c 7, .c 5, .c 3, .c 23, .c 401, .c 3, .c 5, .c 7, .c 3,
  .c 863, .c 11, .c 3, .p pv2 [pv2,pv1012733], .c 233, .c 3, .c 367,
]
private theorem h0247c07 : checkBlock 2025219 128 b0247c07 = true := by
  decide +kernel

private def b0247c08 : List Row := [
  .c 5, .c 3, .p pv11 [pv2,pv7,pv13,pv31,pv359], .c 79, .c 3, .c 5, .p pv3 [pv2,pv3,pv12503],
  .c 3, .c 13, .p pv5 [pv2,pv3,pv7,pv24113], .c 3, .p pv3 [pv2,pv11,pv23017], .c 7, .c 3,
  .p pv5 [pv2,pv1012751], .c 5, .c 3, .c 31, .p pv3 [pv2,pv3,pv5,pv107,pv631], .c 3, .c 5, .c 13,
  .c 3, .c 227, .c 41, .c 3, .c 7, .c 11, .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv1012769], .c 7,
  .c 3, .c 5, .c 109, .c 3, .c 11, .p pv11 [pv2,pv3,pv19,pv2221], .c 3, .p pv2 [pv2,pv13,pv38953],
  .c 47, .c 3, .c 29, .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv4019], .c 3,
  .c 503, .c 7, .c 3, .c 23, .p pv2 [pv2,pv3,pv59,pv2861], .c 3, .p pv3 [pv2,pv29,pv8731], .c 5,
  .c 3, .c 739, .c 17, .c 3, .c 5, .c 53, .c 3, .c 7, .c 709, .c 3, .c 11, .c 1049, .c 3,
  .p pv5 [pv2,pv1012811], .c 5, .c 3, .p pv2 [pv2,pv11,pv19,pv2423],
  .p pv3 [pv2,pv3,pv5,pv71,pv317], .c 3, .c 5, .p pv2 [pv2,pv3,pv168803], .c 3,
  .p pv3 [pv2,pv5,pv89,pv569], .p pv2 [pv2,pv3,pv337607], .c 3, .c 13, .p pv17 [pv2,pv3,pv521],
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv1012829], .c 11, .c 3, .c 5, .c 7, .c 3,
  .p pv13 [pv2,pv5,pv202567], .c 13, .c 3, .c 73, .c 23, .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv61,pv593], .c 479, .c 3, .c 5, .p pv5 [pv2,pv3,pv21101], .c 3, .c 71, .c 17,
  .c 3, .c 337, .c 7, .c 3, .c 37, .c 5, .c 3, .p pv11 [pv2,pv79,pv12821],
  .p pv37 [pv2,pv3,pv5,pv17,pv331], .c 3, .c 5, .c 11, .c 3,
]
private theorem h0247c08 : checkBlock 2025475 128 b0247c08 = true := by
  decide +kernel

private def b0247c09 : List Row := [
  .c 1259, .p pv2 [pv2,pv3,pv223,pv757], .c 3, .c 7, .p pv53 [pv2,pv3,pv11,pv13,pv787], .c 3,
  .c 179, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 31, .c 3, .c 19, .c 373, .c 3,
  .p pv5 [pv2,pv29,pv53,pv659], .c 41, .c 3, .c 43, .c 5, .c 3, .c 7, .c 83, .c 3, .c 5, .c 37,
  .c 3, .p pv17 [pv2,pv5,pv13,pv15583], .c 7, .c 3, .c 79, .c 19, .c 3, .c 13, .c 5, .c 3, .c 557,
  .c 211, .c 3, .c 5, .c 23, .c 3, .c 7, .c 73, .c 3, .p pv2 [pv2,pv11,pv92083], .c 13, .c 3,
  .p pv3 [pv2,pv253229], .c 5, .c 3, .c 17, .c 47, .c 3, .c 5, .c 577, .c 3, .c 41, .c 29, .c 3,
  .c 1283, .c 11, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv13,pv38959], .c 61, .c 3, .c 5, .c 7,
  .c 3, .c 11, .c 59, .c 3, .p pv5 [pv2,pv23,pv44041], .c 263, .c 3, .c 307, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv37,pv3911], .p pv7 [pv2,pv3,pv5,pv2251], .c 3, .c 5, .c 13, .c 3, .c 29,
  .c 19, .c 3, .p pv2 [pv2,pv506479], .c 7, .c 3, .p pv2 [pv2,pv179,pv5659], .c 5, .c 3,
  .p pv3 [pv2,pv157,pv1613], .c 257, .c 3, .c 5, .c 191, .c 3, .c 17, .c 31, .c 3, .c 7,
  .p pv23 [pv2,pv3,pv197,pv857], .c 3, .c 149, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 151, .c 3,
  .c 601, .c 941, .c 3, .c 113, .p pv2 [pv2,pv3,pv23,pv53,pv277], .c 3, .c 109, .c 5,
]
private theorem h0247c09 : checkBlock 2025731 128 b0247c09 = true := by
  decide +kernel

private def b0247c10 : List Row := [
  .c 3, .c 7, .c 11, .c 3, .c 5, .c 283, .c 3, .c 23, .c 7, .c 3, .c 433, .c 17, .c 3, .c 11,
  .c 5, .c 3, .c 199, .p pv11 [pv2,pv3,pv5,pv33767], .c 3, .c 5, .c 19, .c 3, .c 7, .c 773, .c 3,
  .c 13, .c 97, .c 3, .c 17, .c 5, .c 3, .c 313, .c 331, .c 3, .c 5, .c 11, .c 3,
  .p pv13 [pv2,pv5,pv17,pv59,pv101], .c 13, .c 3, .c 31, .p pv2 [pv2,pv3,pv11,pv15349], .c 3,
  .c 7, .c 5, .c 3, .c 11, .p pv11 [pv2,pv3,pv5,pv7,pv67], .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv11,pv113,pv163], .c 23, .c 3, .c 41, .p pv3 [pv2,pv3,pv31,pv3631], .c 3,
  .c 19, .c 5, .c 3, .p pv2 [pv2,pv7,pv269], .c 17, .c 3, .c 5, .c 43, .c 3,
  .p pv3 [pv2,pv5,pv37], .c 11, .c 3, .c 71, .c 7, .c 3, .c 347, .c 5, .c 3, .c 23, .c 13, .c 3,
  .c 5, .c 67, .c 3, .p pv17 [pv2,pv5,pv7,pv827], .p pv5 [pv2,pv3,pv107,pv263], .c 3, .c 7,
  .c 1097, .c 3, .p pv2 [pv2,pv17,pv23,pv2591], .c 5, .c 3, .c 521, .c 7, .c 3, .c 5, .c 131,
  .c 3, .p pv2 [pv2,pv5,pv13,pv7793], .p pv3 [pv2,pv3,pv337697], .c 3, .p pv2 [pv2,pv409,pv2477],
  .c 11, .c 3, .c 13, .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .c 367, .c 3, .c 11, .c 7, .c 3, .c 19,
  .c 13, .c 3, .p pv5 [pv2,pv11,pv31,pv2971], .c 5, .c 3, .p pv2 [pv2,pv617,pv821], .c 23, .c 3,
  .c 5, .c 59, .c 3, .c 7,
]
private theorem h0247c10 : checkBlock 2025987 128 b0247c10 = true := by
  decide +kernel

private def b0247c11 : List Row := [
  .c 53, .c 3, .c 17, .p pv29 [pv2,pv3,pv7,pv1723], .c 3, .c 31, .c 5, .c 3, .c 29, .c 41, .c 3,
  .c 5, .c 271, .c 3, .c 13, .c 421, .c 3, .c 11, .c 83, .c 3, .c 7, .c 5, .c 3, .c 43, .c 281,
  .c 3, .c 5, .c 7, .c 3, .c 389, .p pv3 [pv2,pv3,pv41,pv8237], .c 3, .c 193,
  .p pv11 [pv2,pv3,pv131,pv1289], .c 3, .c 467, .c 5, .c 3, .c 103, .c 11, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv337721], .c 3, .c 19, .p pv2 [pv2,pv3,pv7,pv11,pv17,pv43], .c 3, .c 449, .c 7,
  .c 3, .c 11, .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv19,pv79], .c 3, .c 5, .c 491, .c 3,
  .p pv3 [pv2,pv5,pv7,pv7237], .c 101, .c 3, .c 7, .c 19, .c 3, .p pv2 [pv2,pv506593], .c 5, .c 3,
  .c 37, .c 7, .c 3, .c 5, .c 11, .c 3, .p pv31 [pv2,pv5,pv202639], .p pv5 [pv2,pv3,pv23,pv3671],
  .c 3, .p pv2 [pv2,pv506599], .c 157, .c 3, .c 673, .c 5, .c 3, .c 7, .c 71, .c 3, .c 5, .c 17,
  .c 3, .c 229, .c 7, .c 3, .c 13, .c 79, .c 3, .c 29, .c 5, .c 3, .c 31, .c 89, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv337741], .c 3, .c 7, .c 11, .c 3, .p pv3 [pv2,pv253307], .c 179, .c 3,
  .p pv5 [pv2,pv29,pv34939], .c 5, .c 3, .p pv2 [pv2,pv17,pv1753],
  .p pv3 [pv2,pv3,pv5,pv31,pv2179], .c 3, .c 5, .c 971, .c 3, .c 61, .c 19, .c 3,
  .p pv7 [pv2,pv7,pv11,pv13159], .c 757, .c 3, .c 7, .c 5, .c 3,
]
private theorem h0247c11 : checkBlock 2026243 128 b0247c11 = true := by
  decide +kernel

private def b0247c12 : List Row := [
  .c 47, .c 31, .c 3, .c 5, .c 7, .c 3, .c 1223, .c 379, .c 3, .p pv2 [pv2,pv506629], .c 11, .c 3,
  .p pv2 [pv2,pv173,pv5857], .c 5, .c 3, .c 1361, .c 13, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv17,pv4967], .c 3, .c 11, .c 761, .c 3, .c 43, .c 7, .c 3, .c 17, .c 5, .c 3,
  .c 19, .c 53, .c 3, .c 5, .p pv3 [pv2,pv3,pv37529], .c 3, .c 151, .c 353, .c 3, .c 7, .c 163,
  .c 3, .c 13, .c 5, .c 3, .c 41, .c 7, .c 3, .c 5, .c 19, .c 3, .c 37, .c 61, .c 3, .c 11, .c 13,
  .c 3, .p pv3 [pv2,pv7,pv72379], .c 5, .c 3, .c 7, .c 17, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv73,pv661], .c 3, .p pv17 [pv2,pv5,pv41,pv4943], .c 7, .c 3, .c 109,
  .p pv29 [pv2,pv3,pv17,pv37,pv179], .c 3, .c 349, .c 5, .c 3, .c 479, .c 11, .c 3, .c 5, .c 181,
  .c 3, .c 7, .p pv3 [pv2,pv3,pv11,pv30707], .c 3, .c 53, .p pv47 [pv2,pv3,pv7,pv23,pv1049], .c 3,
  .c 11, .c 5, .c 3, .p pv7 [pv2,pv263,pv3853], .c 293, .c 3, .c 5, .c 13, .c 3, .c 23, .c 193,
  .c 3, .p pv3 [pv2,pv7,pv36191], .c 73, .c 3, .c 7, .c 5, .c 3, .c 59, .c 19, .c 3, .c 5, .c 7,
  .c 3, .p pv19 [pv2,pv5,pv53,pv239], .c 17, .c 3, .p pv5 [pv2,pv13,pv77951],
  .p pv17 [pv2,pv3,pv11,pv853], .c 3, .p pv2 [pv2,pv506683], .c 5, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv5,pv17,pv1987], .c 3, .c 5, .c 877, .c 3, .p pv11 [pv2,pv5,pv11,pv67], .c 41,
]
private theorem h0247c12 : checkBlock 2026499 128 b0247c12 = true := by
  decide +kernel

private def b0247c13 : List Row := [
  .c 3, .c 17, .c 7, .c 3, .p pv2 [pv2,pv43,pv23567], .c 5, .c 3, .p pv3 [pv2,pv19,pv59,pv113],
  .c 797, .c 3, .c 5, .c 83, .c 3, .c 29, .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv168899], .c 3,
  .c 127, .c 5, .c 3, .p pv11 [pv2,pv1013399], .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv19,pv23,pv773],
  .c 3, .c 31, .p pv5 [pv2,pv3,pv168901], .c 3, .c 13, .p pv3 [pv2,pv3,pv112601], .c 3, .c 37,
  .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv13,pv5197], .c 3, .c 5, .c 71, .c 3,
  .p pv7 [pv2,pv5,pv50671], .c 7, .c 3, .c 61, .c 11, .c 3, .c 281, .c 5, .c 3, .c 17, .c 719,
  .c 3, .c 5, .c 233, .c 3, .c 7, .c 31, .c 3, .p pv2 [pv2,pv17,pv41,pv727], .c 53, .c 3, .c 227,
  .c 5, .c 3, .p pv3 [pv2,pv253361], .c 43, .c 3, .c 5, .c 29, .c 3, .c 19, .c 79, .c 3, .c 1193,
  .p pv2 [pv2,pv3,pv13,pv61,pv71], .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv73,pv13883], .c 13,
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv202693], .c 197, .c 3, .c 11, .c 19, .c 3, .c 83,
  .c 5, .c 3, .c 751, .c 67, .c 3, .c 5, .p pv2 [pv2,pv3,pv168913], .c 3, .c 17, .c 131, .c 3,
  .c 23, .c 7, .c 3, .c 13, .c 5, .c 3, .c 71, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv1999],
  .c 3, .c 73, .c 431, .c 3, .c 7, .c 13, .c 3, .c 11, .c 5, .c 3, .c 97,
]
private theorem h0247c13 : checkBlock 2026755 128 b0247c13 = true := by
  decide +kernel

private def b0247c14 : List Row := [
  .c 7, .c 3, .c 5, .c 461, .c 3, .p pv2 [pv2,pv5,pv43,pv2357], .p pv5 [pv2,pv3,pv337837], .c 3,
  .c 157, .c 17, .c 3, .p pv3 [pv2,pv7,pv5171], .c 5, .c 3, .c 7, .c 173, .c 3, .c 5, .c 11, .c 3,
  .c 13, .c 7, .c 3, .p pv3 [pv2,pv126691], .c 23, .c 3, .c 17, .c 5, .c 3, .c 11, .c 29, .c 3,
  .c 5, .c 13, .c 3, .c 7, .c 191, .c 3, .p pv5 [pv2,pv277,pv3659], .c 1039, .c 3,
  .p pv2 [pv2,pv506773], .c 5, .c 3, .p pv2 [pv2,pv311,pv3259], .p pv13 [pv2,pv3,pv5,pv29,pv233],
  .c 3, .c 5, .c 113, .c 3, .p pv7 [pv2,pv5,pv19,pv47,pv227], .c 11, .c 3,
  .p pv2 [pv2,pv7,pv13,pv5569], .c 37, .c 3, .c 7, .c 5, .c 3, .c 13, .c 17, .c 3, .c 5, .c 7,
  .c 3, .c 1063, .c 103, .c 3, .p pv5 [pv2,pv11,pv92143], .c 43, .c 3, .c 89, .c 5, .c 3,
  .p pv17 [pv2,pv7,pv29,pv4993], .p pv7 [pv2,pv3,pv5,pv1877], .c 3, .c 5, .c 19, .c 3, .c 101,
  .c 601, .c 3, .p pv3 [pv2,pv139,pv1823], .c 7, .c 3, .c 31, .c 5, .c 3, .c 137, .c 613, .c 3,
  .c 5, .c 23, .c 3, .c 11, .c 97, .c 3, .c 7, .p pv11 [pv2,pv3,pv84467], .c 3, .c 61, .c 5, .c 3,
  .c 67, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv337871], .c 3, .c 163, .c 13, .c 3,
  .p pv2 [pv2,pv506809], .p pv7 [pv2,pv3,pv337873], .c 3, .c 19, .c 5, .c 3, .c 7, .c 47, .c 3,
  .c 5, .p pv13 [pv2,pv3,pv7,pv11,pv1097], .c 3, .c 1367, .c 7, .c 3,
]
private theorem h0247c14 : checkBlock 2027011 128 b0247c14 = true := by
  decide +kernel

private def b0247c15 : List Row := [
  .c 11, .p pv2 [pv2,pv3,pv6257], .c 3, .c 359, .c 5, .c 3, .c 353, .c 19, .c 3, .c 5, .c 661,
  .c 3, .c 7, .c 223, .c 3, .p pv3 [pv2,pv63353], .c 59, .c 3, .c 29, .c 5, .c 3,
  .p pv2 [pv2,pv367,pv1381], .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv168943], .c 3, .c 43,
  .p pv2 [pv2,pv3,pv11,pv3413], .c 3, .c 41, .c 107, .c 3, .c 7, .c 5, .c 3, .c 491, .c 37, .c 3,
  .c 5, .c 7, .c 3, .c 271, .c 67, .c 3, .c 19, .p pv3 [pv2,pv3,pv23,pv59,pv83], .c 3, .c 13,
  .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv67579], .c 3, .c 5, .c 11, .c 3, .c 23,
  .p pv3 [pv2,pv3,pv7,pv48271], .c 3, .c 173, .c 7, .c 3, .p pv3 [pv2,pv47,pv337], .c 5, .c 3,
  .c 11, .p pv11 [pv2,pv3,pv5,pv31,pv109], .c 3, .c 5, .c 43, .c 3,
  .p pv2 [pv2,pv5,pv7,pv11,pv2633], .c 409, .c 3, .c 7, .c 29, .c 3, .p pv5 [pv2,pv1013711], .c 5,
  .c 3, .c 73, .c 7, .c 3, .c 5, .c 17, .c 3, .c 13, .c 11, .c 3, .p pv5 [pv2,pv113,pv8971],
  .p pv17 [pv2,pv3,pv29,pv971], .c 3, .c 269, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv33791],
  .c 3, .c 5, .c 13, .c 3, .c 17, .c 7, .c 3, .c 29, .c 397, .c 3, .c 641, .c 5, .c 3, .c 37,
  .c 41, .c 3, .c 5, .p pv5 [pv2,pv3,pv23,pv3673], .c 3, .c 7, .p pv5 [pv2,pv3,pv73,pv1543], .c 3,
  .p pv2 [pv2,pv13,pv29,pv2689], .c 11, .c 3, .p pv3 [pv2,pv253439], .c 5, .c 3, .c 13, .c 347,
]
private theorem h0247c15 : checkBlock 2027267 128 b0247c15 = true := by
  decide +kernel

private def b0247c16 : List Row := [
  .c 3, .c 5, .c 947, .c 3, .c 11, .c 47, .c 3, .p pv3 [pv2,pv7,pv43,pv421], .c 17, .c 3, .c 7,
  .c 5, .c 3, .p pv2 [pv2,pv506887], .c 1409, .c 3, .c 5, .c 7, .c 3,
  .p pv11 [pv2,pv5,pv173,pv293], .c 37, .c 3, .p pv5 [pv2,pv19,pv229,pv233],
  .p pv13 [pv2,pv3,pv53,pv797], .c 3, .c 17, .c 5, .c 3, .c 43, .c 853, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv31,pv991], .c 3, .c 97, .c 29, .c 3, .c 11, .c 7, .c 3, .c 727, .c 5,
  .c 3, .p pv3 [pv2,pv11,pv23041], .c 23, .c 3, .c 5, .c 31, .c 3, .c 53, .c 13, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv151,pv373], .c 3, .p pv3 [pv2,pv353,pv359], .c 5, .c 3,
  .p pv11 [pv2,pv1013819], .c 7, .c 3, .c 5, .c 743, .c 3, .c 29, .c 59, .c 3, .c 23,
  .p pv19 [pv2,pv3,pv17,pv103,pv193], .c 3, .c 11, .c 5, .c 3, .c 7, .c 523, .c 3, .c 5,
  .p pv29 [pv2,pv3,pv7,pv101,pv239], .c 3, .p pv3 [pv2,pv5,pv19,pv23,pv29], .c 7, .c 3, .c 89,
  .c 71, .c 3, .c 79, .c 5, .c 3, .c 19, .c 13, .c 3, .c 5, .c 11, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv59,pv179], .c 3, .c 1049, .p pv3 [pv2,pv3,pv7,pv11,pv19], .c 3,
  .p pv2 [pv2,pv269,pv3769], .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv257,pv263], .c 3, .c 5,
  .c 19, .c 3, .c 31, .c 17, .c 3, .p pv5 [pv2,pv7,pv144839], .c 23, .c 3, .c 7, .c 5, .c 3,
  .p pv13 [pv2,pv1013879], .c 103, .c 3, .c 5, .c 7, .c 3, .c 59, .c 11, .c 3, .c 17,
]
private theorem h0247c16 : checkBlock 2027523 128 b0247c16 = true := by
  decide +kernel

private def b0247c17 : List Row := [
  .c 13, .c 3, .p pv5 [pv2,pv1013891], .c 5, .c 3, .p pv2 [pv2,pv7,pv72421], .c 227, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv29,pv5827], .c 3, .p pv3 [pv2,pv5,pv10139], .c 31, .c 3,
  .p pv11 [pv2,pv11,pv92173], .c 7, .c 3, .c 19, .c 5, .c 3, .c 41, .p pv17 [pv2,pv3,pv5,pv33797],
  .c 3, .c 5, .c 683, .c 3, .c 13, .c 53, .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv1013921], .c 5,
  .c 3, .c 317, .c 7, .c 3, .c 5, .c 13, .c 3, .c 11, .c 839, .c 3, .c 73,
  .p pv2 [pv2,pv3,pv347,pv487], .c 3, .p pv3 [pv2,pv7,pv11,pv823], .c 5, .c 3, .c 7, .c 167, .c 3,
  .c 5, .c 23, .c 3, .c 179, .c 7, .c 3, .p pv3 [pv2,pv13,pv17,pv31,pv37],
  .p pv2 [pv2,pv3,pv113,pv997], .c 3, .p pv5 [pv2,pv71,pv14281], .c 5, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv5,pv23,pv2939], .c 3, .c 5, .c 277, .c 3, .c 7, .c 43, .c 3, .c 11, .c 983,
  .c 3, .c 23, .c 5, .c 3, .c 53, .c 29, .c 3, .c 5, .c 17, .c 3, .p pv23 [pv2,pv5,pv40559],
  .p pv5 [pv2,pv3,pv14083], .c 3, .c 421, .p pv3 [pv2,pv3,pv31,pv10903], .c 3, .c 7, .c 5, .c 3,
  .c 157, .c 11, .c 3, .c 5, .c 7, .c 3, .c 17, .c 41, .c 3, .c 13, .c 31, .c 3, .c 11, .c 5,
  .c 3, .c 29, .c 373, .c 3, .c 5, .c 37, .c 3, .c 113, .c 13, .c 3, .p pv3 [pv2,pv126751], .c 7,
  .c 3, .c 67, .c 5, .c 3, .c 379, .c 311, .c 3,
]
private theorem h0247c17 : checkBlock 2027779 128 b0247c17 = true := by
  decide +kernel

private def b0247c18 : List Row := [
  .c 5, .c 11, .c 3, .c 19, .c 89, .c 3, .c 7, .c 17, .c 3, .p pv2 [pv2,pv13,pv43,pv907], .c 5,
  .c 3, .c 11, .c 7, .c 3, .c 5, .c 61, .c 3, .c 23, .p pv5 [pv2,pv3,pv84503], .c 3,
  .p pv2 [pv2,pv97,pv5227], .c 19, .c 3, .c 17, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 47, .c 3,
  .p pv3 [pv2,pv5,pv17,pv1193], .c 7, .c 3, .p pv2 [pv2,pv41,pv24733], .p pv2 [pv2,pv3,pv169009],
  .c 3, .c 31, .c 5, .c 3, .p pv7 [pv2,pv37,pv27407], .p pv11 [pv2,pv3,pv5,pv16901], .c 3, .c 5,
  .c 1153, .c 3, .c 7, .c 449, .c 3, .p pv5 [pv2,pv11,pv19,pv1213],
  .p pv7 [pv2,pv3,pv7,pv43,pv1123], .c 3, .c 13, .c 5, .c 3, .c 139, .c 17, .c 3, .c 5, .c 67,
  .c 3, .c 1291, .c 23, .c 3, .c 79, .c 11, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv1014089], .c 43,
  .c 3, .c 5, .c 7, .c 3, .c 11, .c 19, .c 3, .p pv2 [pv2,pv507049], .p pv17 [pv2,pv3,pv338033],
  .c 3, .p pv2 [pv2,pv11,pv17,pv29], .c 5, .c 3, .c 23, .c 733, .c 3, .c 5,
  .p pv29 [pv2,pv3,pv84509], .c 3, .c 13, .p pv3 [pv2,pv3,pv7,pv16097], .c 3,
  .p pv2 [pv2,pv1014113], .c 7, .c 3, .c 919, .c 5, .c 3, .p pv11 [pv2,pv47,pv21577],
  .p pv17 [pv2,pv3,pv5,pv313], .c 3, .c 5, .c 13, .c 3, .c 883, .c 17, .c 3, .c 7, .c 1301, .c 3,
  .p pv5 [pv2,pv1014131], .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .p pv19 [pv2,pv3,pv103,pv547],
  .c 3, .p pv7 [pv2,pv5,pv50707], .c 157, .c 3, .c 17, .c 29,
]
private theorem h0247c18 : checkBlock 2028035 128 b0247c18 = true := by
  decide +kernel

private def b0247c19 : List Row := [
  .c 3, .p pv3 [pv2,pv7,pv107,pv677], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 19, .c 3, .c 41,
  .c 7, .c 3, .c 127, .p pv3 [pv2,pv3,pv29,pv11657], .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv71,pv3571], .c 251, .c 3, .c 5, .c 149, .c 3, .c 7, .c 211, .c 3, .c 23, .c 307,
  .c 3, .c 43, .c 5, .c 3, .p pv7 [pv2,pv67,pv15137], .c 31, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv23,pv8819], .p pv2 [pv2,pv3,pv17,pv61,pv163], .c 3, .c 13, .c 47, .c 3, .c 7,
  .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv7,pv13,pv743], .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv11,pv461], .c 13, .c 3, .c 199, .c 367, .c 3, .p pv2 [pv2,pv507103], .c 5,
  .c 3, .c 971, .c 19, .c 3, .c 5, .c 139, .c 3, .p pv13 [pv2,pv5,pv193,pv1051], .c 11, .c 3,
  .c 83, .c 7, .c 3, .p pv2 [pv2,pv13,pv78017], .c 5, .c 3, .c 709, .c 37, .c 3, .c 5, .c 17,
  .c 3, .p pv2 [pv2,pv5,pv7,pv14489], .c 29, .c 3, .c 7, .c 53, .c 3, .c 47, .c 5, .c 3, .c 59,
  .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv149,pv2269], .c 3, .c 17, .p pv2 [pv2,pv3,pv29,pv67], .c 3,
  .c 19, .c 11, .c 3, .p pv5 [pv2,pv7,pv2957], .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv11,pv683],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv19,pv31,pv41], .c 3, .c 11, .c 7, .c 3,
  .p pv5 [pv2,pv1014263], .c 269, .c 3, .c 13, .c 5, .c 3, .c 281, .c 71, .c 3, .c 5,
]
private theorem h0247c19 : checkBlock 2028291 128 b0247c19 = true := by
  decide +kernel

private def b0247c20 : List Row := [
  .c 31, .c 3, .c 7, .c 313, .c 3, .c 41, .c 13, .c 3, .c 829, .c 5, .c 3, .c 887, .c 127, .c 3,
  .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv101429], .c 1187, .c 3, .c 11, .p pv7 [pv2,pv3,pv169049],
  .c 3, .c 7, .c 5, .c 3, .c 37, .p pv31 [pv2,pv3,pv5,pv7,pv23], .c 3, .c 5, .c 7, .c 3, .c 13,
  .c 107, .c 3, .p pv3 [pv2,pv61,pv4157], .c 439, .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv53,pv1367], .c 11, .c 3, .c 5, .c 13, .c 3, .c 79,
  .p pv2 [pv2,pv3,pv7,pv11,pv4391], .c 3, .p pv5 [pv2,pv23,pv44101], .c 7, .c 3, .c 11, .c 5,
  .c 3, .c 401, .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv29,pv89,pv131], .c 3, .c 31, .c 37, .c 3,
  .c 7, .p pv3 [pv2,pv3,pv17,pv19889], .c 3, .c 71, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 11,
  .c 3, .p pv2 [pv2,pv5,pv20287], .p pv3 [pv2,pv3,pv13,pv31,pv839], .c 3,
  .p pv2 [pv2,pv19,pv197,pv271], .c 359, .c 3, .p pv3 [pv2,pv7,pv17,pv2131], .c 5, .c 3, .c 7,
  .c 41, .c 3, .c 5, .c 1021, .c 3, .c 233, .c 7, .c 3, .c 349, .c 1217, .c 3, .c 73, .c 5, .c 3,
  .p pv2 [pv2,pv277,pv1831], .c 383, .c 3, .c 5, .p pv2 [pv2,pv3,pv169063], .c 3, .c 7, .c 11,
  .c 3, .c 13, .c 83, .c 3, .p pv2 [pv2,pv507193], .c 5, .c 3, .p pv2 [pv2,pv1014389],
  .p pv2 [pv2,pv3,pv5,pv13,pv17], .c 3, .c 5, .c 53, .c 3, .c 103, .c 13, .c 3, .c 17, .c 61,
  .c 3,
]
private theorem h0247c20 : checkBlock 2028547 128 b0247c20 = true := by
  decide +kernel

private def b0247c21 : List Row := [
  .c 7, .c 5, .c 3, .p pv3 [pv2,pv253601], .c 29, .c 3, .c 5, .c 7, .c 3, .c 37, .c 547, .c 3,
  .c 67, .c 11, .c 3, .c 59, .c 5, .c 3, .c 19, .p pv7 [pv2,pv3,pv5,pv11,pv29,pv53], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv338141], .c 3, .c 11, .c 23, .c 3, .c 31, .c 7, .c 3,
  .p pv5 [pv2,pv11,pv92221], .c 5, .c 3, .c 29, .c 13, .c 3, .c 5, .c 19, .c 3,
  .p pv23 [pv2,pv5,pv7,pv3623], .c 167, .c 3, .c 7, .c 73, .c 3, .c 53, .c 5, .c 3, .c 17, .c 7,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv10247], .c 3, .c 157, .c 863, .c 3, .c 11, .c 31, .c 3,
  .c 13, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv67631], .c 3, .c 5, .c 953, .c 3,
  .p pv2 [pv2,pv5,pv229,pv443], .c 7, .c 3, .p pv2 [pv2,pv53,pv19141], .c 13, .c 3, .c 19, .c 5,
  .c 3, .c 907, .c 11, .c 3, .c 5, .c 17, .c 3, .c 7, .p pv2 [pv2,pv3,pv11,pv19,pv809], .c 3,
  .c 271, .c 241, .c 3, .c 11, .c 5, .c 3, .c 101, .c 19, .c 3, .c 5, .c 103, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv338167], .c 3, .p pv5 [pv2,pv7,pv37,pv3917], .c 193, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv17,pv83,pv719], .p pv17 [pv2,pv3,pv5,pv7,pv4831], .c 3, .c 5, .c 7, .c 3, .c 449,
  .p pv7 [pv2,pv3,pv28181], .c 3, .c 23, .c 1013, .c 3, .c 29, .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv167], .c 3, .c 5, .c 727,
]
private theorem h0247c21 : checkBlock 2028803 128 b0247c21 = true := by
  decide +kernel

private def b0247c22 : List Row := [
  .c 3, .c 659, .p pv5 [pv2,pv3,pv7,pv48311], .c 3, .c 19, .c 7, .c 3, .p pv3 [pv2,pv29,pv4373],
  .c 5, .c 3, .c 13, .p pv11 [pv2,pv3,pv5,pv37,pv457], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv17,pv19,pv349], .c 3, .p pv17 [pv2,pv5,pv7,pv41,pv101], .c 11, .c 3, .c 7,
  .c 1009, .c 3, .c 17, .c 5, .c 3, .c 71, .c 7, .c 3, .c 5, .c 37, .c 3,
  .p pv3 [pv2,pv5,pv17,pv373], .p pv13 [pv2,pv3,pv139,pv811], .c 3, .c 43, .c 23, .c 3, .c 743,
  .c 5, .c 3, .c 7, .c 113, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv48313], .c 3, .c 557, .c 7, .c 3,
  .c 13, .c 11, .c 3, .p pv2 [pv2,pv19,pv67,pv797], .c 5, .c 3, .c 229, .c 17, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv28183], .c 3, .c 7, .c 13, .c 3, .c 59, .p pv2 [pv2,pv3,pv7,pv17,pv29], .c 3,
  .c 683, .c 5, .c 3, .p pv17 [pv2,pv23,pv31,pv1423], .c 607, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv127,pv2663], .c 3, .c 53, .c 41, .c 3, .c 29, .c 19, .c 3, .c 7, .c 5, .c 3,
  .c 31, .c 149, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv97,pv523], .p pv5 [pv2,pv3,pv338207],
  .c 3, .c 11, .p pv17 [pv2,pv3,pv13,pv271], .c 3, .c 109, .c 5, .c 3, .c 587, .c 13, .c 3, .c 5,
  .c 23, .c 3, .p pv23 [pv2,pv5,pv307,pv661], .c 17, .c 3, .p pv2 [pv2,pv19,pv26701], .c 7, .c 3,
  .p pv2 [pv2,pv1014641], .c 5, .c 3, .c 89, .c 11, .c 3, .c 5, .c 197, .c 3,
  .p pv17 [pv2,pv5,pv7,pv13,pv223], .c 491, .c 3, .c 7, .c 577, .c 3, .c 11,
]
private theorem h0247c22 : checkBlock 2029059 128 b0247c22 = true := by
  decide +kernel

private def b0247c23 : List Row := [
  .c 5, .c 3, .c 47, .c 7, .c 3, .c 5, .c 73, .c 3, .p pv2 [pv2,pv5,pv202933], .c 19, .c 3, .c 97,
  .c 13, .c 3, .c 1171, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv83,pv163], .c 3, .c 5, .c 11,
  .c 3, .c 331, .c 7, .c 3, .c 113, .p pv17 [pv2,pv3,pv11,pv7687], .c 3,
  .p pv2 [pv2,pv181,pv2803], .c 5, .c 3, .c 11, .c 137, .c 3, .c 5, .p pv2 [pv2,pv3,pv338231],
  .c 3, .c 7, .c 71, .c 3, .c 353, .p pv13 [pv2,pv3,pv7,pv211,pv229], .c 3,
  .p pv2 [pv2,pv199,pv5099], .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv22549], .c 3, .c 5, .c 13,
  .c 3, .c 947, .c 11, .c 3, .c 359, .c 1087, .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv1014719],
  .p pv13 [pv2,pv3,pv5,pv7,pv151], .c 3, .c 5, .c 7, .c 3, .c 23, .p pv5 [pv2,pv3,pv131,pv1291],
  .c 3, .p pv3 [pv2,pv11,pv13,pv887], .c 41, .c 3, .c 173, .c 5, .c 3, .c 13, .c 43, .c 3, .c 5,
  .c 17, .c 3, .c 1051, .p pv5 [pv2,pv3,pv7,pv13,pv59], .c 3, .c 37, .c 7, .c 3, .c 373, .c 5,
  .c 3, .p pv2 [pv2,pv1014749], .p pv2 [pv2,pv3,pv5,pv11,pv41], .c 3, .c 5, .c 29, .c 3, .c 11,
  .c 163, .c 3, .c 7, .c 271, .c 3, .c 19, .c 5, .c 3, .c 53, .c 7, .c 3, .c 5, .c 457, .c 3,
  .c 41, .c 23, .c 3, .c 13, .p pv13 [pv2,pv3,pv169129], .c 3, .c 181, .c 5, .c 3, .c 7, .c 19,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv11,pv23,pv191], .c 3,
]
private theorem h0247c23 : checkBlock 2029315 128 b0247c23 = true := by
  decide +kernel

private def b0247c24 : List Row := [
  .c 263, .c 7, .c 3, .c 11, .c 17, .c 3, .c 131, .c 5, .c 3, .c 23, .c 151, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv17,pv9949], .c 3, .c 7, .c 347, .c 3, .c 227, .c 211, .c 3, .c 17, .c 5, .c 3,
  .c 73, .c 11, .c 3, .c 5, .c 229, .c 3, .c 67, .p pv5 [pv2,pv3,pv11,pv31], .c 3, .c 19, .c 647,
  .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv47,pv2699], .c 13, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv101483], .c 31, .c 3, .p pv2 [pv2,pv1014833], .p pv2 [pv2,pv3,pv79,pv2141],
  .c 3, .c 787, .c 5, .c 3, .p pv7 [pv2,pv7,pv139,pv149], .c 17, .c 3, .c 5, .c 11, .c 3, .c 197,
  .c 1061, .c 3, .p pv3 [pv2,pv101,pv157], .c 7, .c 3, .c 13, .c 5, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv5,pv29,pv2333], .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv4337], .c 3,
  .p pv3 [pv2,pv5,pv7,pv11,pv659], .p pv2 [pv2,pv3,pv338287], .c 3, .c 7, .c 13, .c 3, .c 967,
  .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .c 79, .c 3, .c 19, .c 11, .c 3, .c 191,
  .p pv3 [pv2,pv3,pv338293], .c 3, .c 523, .c 5, .c 3, .c 7, .c 1307, .c 3, .c 5, .c 59, .c 3,
  .c 13, .c 7, .c 3, .c 31, .c 19, .c 3, .p pv3 [pv2,pv137,pv463], .c 5, .c 3,
  .p pv7 [pv2,pv109,pv9311], .p pv23 [pv2,pv3,pv5,pv17,pv199], .c 3, .c 5, .c 13, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv169151], .c 3, .c 17, .c 11, .c 3, .c 89, .c 5,
]
private theorem h0247c24 : checkBlock 2029571 128 b0247c24 = true := by
  decide +kernel

private def b0247c25 : List Row := [
  .c 3, .p pv2 [pv2,pv41,pv12377], .p pv3 [pv2,pv3,pv5,pv11,pv6151], .c 3, .c 5, .c 251, .c 3,
  .c 11, .p pv3 [pv2,pv3,pv23,pv4903], .c 3, .c 53, .c 31, .c 3, .c 7, .c 5, .c 3, .c 13, .c 397,
  .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv202987], .p pv7 [pv2,pv3,pv13,pv3253], .c 3, .c 367,
  .p pv3 [pv2,pv3,pv112771], .c 3, .c 47, .c 5, .c 3, .p pv3 [pv2,pv7,pv23,pv197],
  .p pv2 [pv2,pv3,pv5,pv71,pv953], .c 3, .c 5, .c 61, .c 3, .c 43, .c 19, .c 3, .c 11, .c 7, .c 3,
  .c 29, .c 5, .c 3, .c 17, .p pv7 [pv2,pv3,pv5,pv4229], .c 3, .c 5, .c 631, .c 3, .c 37, .c 811,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv338323], .c 3, .c 241, .c 5, .c 3, .c 1399, .c 7, .c 3, .c 5,
  .c 23, .c 3, .c 71, .c 13, .c 3, .p pv5 [pv2,pv67,pv15149], .c 223, .c 3, .c 11, .c 5, .c 3,
  .c 7, .p pv2 [pv2,pv3,pv5,pv23,pv1471], .c 3, .c 5, .c 17, .c 3, .p pv13 [pv2,pv5,pv202999],
  .c 7, .c 3, .p pv2 [pv2,pv507499], .c 101, .c 3, .c 23, .c 5, .c 3, .p pv3 [pv2,pv253751],
  .c 599, .c 3, .c 5, .c 11, .c 3, .c 7, .c 331, .c 3, .c 103, .c 29, .c 3, .c 41, .c 5, .c 3,
  .c 11, .c 13, .c 3, .c 5, .c 641, .c 3, .p pv7 [pv2,pv5,pv11,pv3691],
  .p pv2 [pv2,pv3,pv167,pv1013], .c 3, .c 73, .c 53, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv317,pv1601], .c 47, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv13,pv61],
]
private theorem h0247c25 : checkBlock 2029827 128 b0247c25 = true := by
  decide +kernel

private def b0247c26 : List Row := [
  .c 11, .c 3, .c 29, .c 17, .c 3, .c 13, .c 5, .c 3, .p pv7 [pv2,pv7,pv145007],
  .p pv2 [pv2,pv3,pv5,pv67,pv101], .c 3, .c 5, .c 131, .c 3, .c 107, .c 97, .c 3,
  .p pv2 [pv2,pv11,pv29,pv37,pv43], .c 7, .c 3, .c 17, .c 5, .c 3, .c 233, .c 19, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv84589], .c 3, .c 23, .c 269, .c 3, .c 7, .c 11, .c 3, .c 37, .c 5, .c 3,
  .c 31, .c 7, .c 3, .c 5, .c 67, .c 3, .c 11, .p pv2 [pv2,pv3,pv169181], .c 3, .c 653, .c 89,
  .c 3, .p pv5 [pv2,pv7,pv11,pv13183], .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 13, .c 3, .c 101,
  .c 7, .c 3, .c 19, .p pv23 [pv2,pv3,pv17,pv311], .c 3, .p pv2 [pv2,pv47,pv10799], .c 5, .c 3,
  .c 167, .c 31, .c 3, .c 5, .c 37, .c 3, .c 7, .c 23, .c 3, .c 11, .c 373, .c 3,
  .p pv2 [pv2,pv17,pv211,pv283], .c 5, .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv2707], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv23,pv613], .c 3, .c 29, .c 61, .c 3, .p pv2 [pv2,pv7,pv20717], .c 443, .c 3,
  .c 7, .c 5, .c 3, .c 23, .c 11, .c 3, .c 5, .c 7, .c 3, .p pv23 [pv2,pv5,pv29,pv7001], .c 17,
  .c 3, .c 347, .p pv2 [pv2,pv3,pv338383], .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv7,pv59,pv1229],
  .p pv19 [pv2,pv3,pv5,pv17,pv1327], .c 3, .c 5, .p pv2 [pv2,pv3,pv71,pv2383], .c 3, .c 19,
  .c 677, .c 3, .c 13, .c 7, .c 3, .c 821, .c 5, .c 3,
]
private theorem h0247c26 : checkBlock 2030083 128 b0247c26 = true := by
  decide +kernel

private def b0247c27 : List Row := [
  .c 251, .c 823, .c 3, .c 5, .c 11, .c 3, .c 1091, .c 13, .c 3, .c 7, .c 19, .c 3,
  .p pv2 [pv2,pv233,pv4357], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 29, .c 3,
  .p pv2 [pv2,pv5,pv11,pv839], .p pv3 [pv2,pv3,pv112799], .c 3, .c 71, .p pv17 [pv2,pv3,pv169199],
  .c 3, .p pv3 [pv2,pv7,pv13,pv2789], .c 5, .c 3, .c 7, .c 509, .c 3, .c 5, .c 31, .c 3,
  .p pv11 [pv2,pv5,pv277,pv733], .c 7, .c 3, .c 23, .p pv2 [pv2,pv3,pv13,pv8677], .c 3, .c 149,
  .c 5, .c 3, .c 17, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv56401], .c 3, .c 7, .c 41, .c 3, .c 47,
  .c 37, .c 3, .c 211, .c 5, .c 3, .p pv2 [pv2,pv71,pv79,pv181], .p pv7 [pv2,pv3,pv5,pv43,pv787],
  .c 3, .c 5, .p pv3 [pv2,pv3,pv338411], .c 3, .p pv7 [pv2,pv5,pv13,pv15619], .c 19, .c 3, .c 137,
  .c 11, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv253811], .c 163, .c 3, .c 5, .c 7, .c 3, .c 11,
  .c 43, .c 3, .c 61, .c 13, .c 3, .p pv3 [pv2,pv11,pv83,pv139], .c 5, .c 3, .c 311, .c 191, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv112807], .c 3, .c 17, .p pv13 [pv2,pv3,pv7,pv23,pv1051], .c 3, .c 79,
  .c 7, .c 3, .c 229, .c 5, .c 3, .c 19, .c 29, .c 3, .c 5, .c 257, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv31,pv1213], .c 3, .c 7, .c 67, .c 3, .p pv2 [pv2,pv149,pv3407], .c 5, .c 3,
  .c 1109, .c 7, .c 3, .c 5, .c 13, .c 3, .p pv19 [pv2,pv5,pv251,pv809], .c 31,
]
private theorem h0247c27 : checkBlock 2030339 128 b0247c27 = true := by
  decide +kernel

private def b0247c28 : List Row := [
  .c 3, .c 37, .c 17, .c 3, .c 59, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv17,pv79], .c 3, .c 1423, .c 7, .c 3, .p pv2 [pv2,pv13,pv78101], .c 61,
  .c 3, .c 11, .c 5, .c 3, .c 13, .c 73, .c 3, .c 5, .c 23, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv13,pv4339], .c 3, .p pv3 [pv2,pv31729], .p pv2 [pv2,pv3,pv7,pv6907], .c 3,
  .c 19, .c 5, .c 3, .p pv2 [pv2,pv507667], .c 37, .c 3, .c 5, .c 11, .c 3, .c 269,
  .p pv3 [pv2,pv3,pv19,pv47,pv379], .c 3, .c 277, .c 41, .c 3, .c 7, .c 5, .c 3, .c 11, .c 17,
  .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv11,pv18461], .c 89, .c 3, .c 13,
  .p pv23 [pv2,pv3,pv17,pv43,pv463], .c 3, .c 113, .c 5, .c 3, .c 47,
  .p pv2 [pv2,pv3,pv5,pv13,pv41,pv127], .c 3, .c 5, .p pv5 [pv2,pv3,pv42307], .c 3, .c 563, .c 11,
  .c 3, .p pv2 [pv2,pv193,pv5261], .c 7, .c 3, .c 107, .c 5, .c 3, .p pv11 [pv2,pv19,pv53441],
  .c 43, .c 3, .c 5, .c 1259, .c 3, .c 41, .c 907, .c 3, .c 7, .c 31, .c 3, .c 29, .c 5, .c 3,
  .p pv2 [pv2,pv507697], .c 7, .c 3, .c 5, .c 701, .c 3, .c 53, .c 17, .c 3, .c 101, .c 11, .c 3,
  .c 71, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 449, .c 3, .c 11, .c 7, .c 3, .c 17, .c 59, .c 3,
  .c 953, .c 5, .c 3, .c 691,
]
private theorem h0247c28 : checkBlock 2030595 128 b0247c28 = true := by
  decide +kernel

private def b0247c29 : List Row := [
  .c 103, .c 3, .c 5, .c 127, .c 3, .c 7, .c 359, .c 3, .c 1019, .c 613, .c 3, .c 13, .c 5, .c 3,
  .p pv7 [pv2,pv983,pv1033], .p pv11 [pv2,pv3,pv5,pv4231], .c 3, .c 5, .c 167, .c 3, .c 19, .c 37,
  .c 3, .c 11, .c 13, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv11,pv101,pv457],
  .p pv7 [pv2,pv3,pv5,pv7,pv19,pv509], .c 3, .c 5, .c 7, .c 3, .p pv11 [pv2,pv5,pv50773], .c 23,
  .c 3, .c 83, .c 19, .c 3, .c 43, .c 5, .c 3, .c 17, .c 11, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv23,pv14717], .c 3, .c 13, .p pv13 [pv2,pv3,pv7,pv11,pv157], .c 3, .c 29, .c 7,
  .c 3, .c 11, .c 5, .c 3, .c 23, .c 67, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv7,pv89,pv163],
  .c 467, .c 3, .c 7, .c 1283, .c 3, .c 853, .c 5, .c 3, .p pv11 [pv2,pv1015499], .c 7, .c 3,
  .c 5, .c 11, .c 3, .c 47, .c 53, .c 3, .c 41, .c 43, .c 3, .p pv5 [pv2,pv7,pv239,pv607], .c 5,
  .c 3, .c 7, .c 757, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv24179], .c 3, .c 17, .c 7, .c 3, .c 571,
  .c 383, .c 3, .p pv2 [pv2,pv397,pv1279], .c 5, .c 3, .p pv2 [pv2,pv17,pv31,pv41,pv47], .c 23,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv53,pv2129], .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv293,pv1733],
  .c 73, .c 3, .c 97, .c 5, .c 3, .c 31, .c 283, .c 3, .c 5, .c 71, .c 3, .c 151,
  .p pv3 [pv2,pv3,pv29,pv1297], .c 3,
]
private theorem h0247c29 : checkBlock 2030851 128 b0247c29 = true := by
  decide +kernel

private def b0247c30 : List Row := [
  .c 13, .c 17, .c 3, .c 7, .c 5, .c 3, .c 19, .p pv17 [pv2,pv3,pv5,pv7,pv13,pv31], .c 3, .c 5,
  .c 7, .c 3, .c 29, .c 13, .c 3, .p pv3 [pv2,pv63473], .c 11, .c 3, .c 17, .c 5, .c 3, .c 263,
  .c 31, .c 3, .c 5, .c 19, .c 3, .c 11, .p pv2 [pv2,pv3,pv7,pv137,pv353], .c 3,
  .p pv5 [pv2,pv461,pv2203], .c 7, .c 3, .c 1217, .c 5, .c 3, .p pv2 [pv2,pv61,pv16649], .c 41,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv338531], .c 3, .c 43, .c 59, .c 3, .c 7, .c 23, .c 3, .c 433,
  .c 5, .c 3, .c 599, .c 7, .c 3, .c 5, .p pv7 [pv2,pv3,pv11,pv3847], .c 3, .c 167,
  .p pv3 [pv2,pv3,pv23,pv41,pv359], .c 3, .c 11, .p pv2 [pv2,pv3,pv17,pv3319], .c 3, .c 19, .c 5,
  .c 3, .c 7, .c 277, .c 3, .c 5, .c 29, .c 3, .p pv17 [pv2,pv5,pv13], .c 7, .c 3,
  .p pv3 [pv2,pv253907], .c 83, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv23,pv22079], .c 11, .c 3,
  .c 5, .c 43, .c 3, .c 7, .p pv3 [pv2,pv3,pv11,pv10259], .c 3, .p pv5 [pv2,pv131,pv7753], .c 13,
  .c 3, .c 11, .c 5, .c 3, .c 137, .p pv17 [pv2,pv3,pv5,pv37,pv61], .c 3, .c 5, .c 223, .c 3,
  .c 59, .c 17, .c 3, .c 149, .p pv3 [pv2,pv3,pv12539], .c 3, .c 7, .c 5, .c 3, .c 641, .c 53,
  .c 3, .c 5, .c 7, .c 3, .c 13, .c 251, .c 3, .c 17, .c 281, .c 3, .p pv3 [pv2,pv253919], .c 5,
  .c 3, .c 11, .c 61,
]
private theorem h0247c30 : checkBlock 2031107 128 b0247c30 = true := by
  decide +kernel

private def b0247c31 : List Row := [
  .c 3, .c 5, .c 13, .c 3, .c 73, .c 67, .c 3, .c 1303, .c 7, .c 3, .c 23, .c 5, .c 3, .c 241,
  .p pv3 [pv2,pv3,pv5,pv22571], .c 3, .c 5, .p pv2 [pv2,pv3,pv169283], .c 3, .c 113, .c 11, .c 3,
  .c 7, .p pv11 [pv2,pv3,pv14107], .c 3, .c 101, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 41, .c 3,
  .p pv23 [pv2,pv5,pv31,pv6553], .c 109, .c 3, .c 53, .c 479, .c 3, .p pv2 [pv2,pv7,pv19,pv1091],
  .c 5, .c 3, .c 7, .c 1381, .c 3, .c 5, .p pv11 [pv2,pv3,pv7,pv3023], .c 3, .c 19, .c 7, .c 3,
  .p pv2 [pv2,pv17,pv149,pv401], .c 11, .c 3, .p pv3 [pv2,pv126967], .c 5, .c 3, .c 29, .c 47,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv338581], .c 3, .c 7, .p pv5 [pv2,pv3,pv31,pv43,pv127], .c 3,
  .c 13, .c 19, .c 3, .c 409, .c 5, .c 3, .c 41, .c 739, .c 3, .c 5, .c 17, .c 3, .c 23, .c 13,
  .c 3, .c 233, .c 349, .c 3, .c 7, .c 5, .c 3, .c 173, .p pv11 [pv2,pv3,pv5,pv7,pv691], .c 3,
  .c 5, .c 7, .c 3, .c 17, .c 797, .c 3, .c 11, .c 37, .c 3, .p pv7 [pv2,pv13,pv78137], .c 5,
  .c 3, .p pv3 [pv2,pv7,pv11,pv17,pv97], .p pv2 [pv2,pv3,pv5,pv22573], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv84649], .c 3, .c 359, .c 1051, .c 3, .p pv2 [pv2,pv881,pv1153], .c 7, .c 3,
  .p pv3 [pv2,pv253949], .c 5, .c 3, .p pv11 [pv2,pv443,pv2293], .c 11, .c 3, .c 5, .c 587, .c 3,
  .p pv19 [pv2,pv5,pv7,pv29023], .c 19, .c 3, .c 7,
]
private theorem h0247c31 : checkBlock 2031363 128 b0247c31 = true := by
  decide +kernel

def rows0247 : List Row :=
  b0247c00 ++ b0247c01 ++ b0247c02 ++ b0247c03 ++ b0247c04 ++ b0247c05 ++ b0247c06 ++ b0247c07 ++
  b0247c08 ++ b0247c09 ++ b0247c10 ++ b0247c11 ++ b0247c12 ++ b0247c13 ++ b0247c14 ++ b0247c15 ++
  b0247c16 ++ b0247c17 ++ b0247c18 ++ b0247c19 ++ b0247c20 ++ b0247c21 ++ b0247c22 ++ b0247c23 ++
  b0247c24 ++ b0247c25 ++ b0247c26 ++ b0247c27 ++ b0247c28 ++ b0247c29 ++ b0247c30 ++ b0247c31

theorem checked0247 : checkBlock 2023427 4096 rows0247 = true :=
  checkBlock_append h0247c00 (
    checkBlock_append h0247c01 (
    checkBlock_append h0247c02 (
    checkBlock_append h0247c03 (
    checkBlock_append h0247c04 (
    checkBlock_append h0247c05 (
    checkBlock_append h0247c06 (
    checkBlock_append h0247c07 (
    checkBlock_append h0247c08 (
    checkBlock_append h0247c09 (
    checkBlock_append h0247c10 (
    checkBlock_append h0247c11 (
    checkBlock_append h0247c12 (
    checkBlock_append h0247c13 (
    checkBlock_append h0247c14 (
    checkBlock_append h0247c15 (
    checkBlock_append h0247c16 (
    checkBlock_append h0247c17 (
    checkBlock_append h0247c18 (
    checkBlock_append h0247c19 (
    checkBlock_append h0247c20 (
    checkBlock_append h0247c21 (
    checkBlock_append h0247c22 (
    checkBlock_append h0247c23 (
    checkBlock_append h0247c24 (
    checkBlock_append h0247c25 (
    checkBlock_append h0247c26 (
    checkBlock_append h0247c27 (
    checkBlock_append h0247c28 (
    checkBlock_append h0247c29 (
    checkBlock_append h0247c30 (
    h0247c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
