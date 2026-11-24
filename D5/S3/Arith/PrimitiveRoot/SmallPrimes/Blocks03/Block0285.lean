/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks03/Block0285
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks03/Block0285.checked0285
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table142

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0285c00 : List Row := [
  .c 3, .c 5, .c 431, .c 3, .c 7, .c 643, .c 3, .c 37, .c 11, .c 3, .p pv5 [pv2,pv353,pv3307],
  .c 5, .c 3, .c 67, .p pv17 [pv2,pv3,pv5,pv11,pv283], .c 3, .c 5, .c 397, .c 3, .c 11, .c 17,
  .c 3, .p pv5 [pv2,pv7,pv79,pv2111], .p pv7 [pv2,pv3,pv127,pv383], .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv389,pv3001], .p pv2 [pv2,pv3,pv5,pv7,pv17,pv109], .c 3, .c 5, .c 7, .c 3, .c 239,
  .p pv7 [pv2,pv3,pv97283], .c 3, .c 17, .c 23, .c 3, .p pv2 [pv2,pv251,pv4651], .c 5, .c 3,
  .c 53, .c 37, .c 3, .c 5, .c 101, .c 3, .c 499, .p pv3 [pv2,pv3,pv7,pv23,pv2417], .c 3, .c 11,
  .c 7, .c 3, .c 277, .c 5, .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv19457], .c 3, .c 5, .c 107, .c 3,
  .c 823, .c 19, .c 3, .c 7, .c 751, .c 3, .p pv5 [pv2,pv53,pv22027], .c 5, .c 3, .c 811, .c 7,
  .c 3, .c 5, .c 29, .c 3, .p pv3 [pv2,pv5,pv14593], .c 67, .c 3, .c 97, .c 31, .c 3, .c 11, .c 5,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv43,pv181], .c 3, .c 5, .c 103, .c 3,
  .p pv17 [pv2,pv5,pv19,pv12289], .c 7, .c 3, .c 13, .c 113, .c 3, .p pv2 [pv2,pv37,pv139,pv227],
  .c 5, .c 3, .c 19, .c 1399, .c 3, .c 5, .c 11, .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv1167473],
  .p pv2 [pv2,pv3,pv7,pv11,pv19], .c 3, .p pv3 [pv2,pv291869], .c 5, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv5,pv23,pv47], .c 3, .c 5, .c 17, .c 3, .c 1453, .c 677, .c 3, .c 71,
]
private theorem h0285c00 : checkBlock 2334723 128 b0285c00 = true := by
  decide +kernel

private def b0285c01 : List Row := [
  .c 149, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv311,pv1877], .c 41, .c 3, .c 5, .c 7, .c 3, .c 17,
  .c 11, .c 3, .c 47, .p pv11 [pv2,pv3,pv13,pv1871], .c 3, .c 31, .c 5, .c 3, .c 61, .c 13, .c 3,
  .c 5, .c 1021, .c 3, .c 701, .c 37, .c 3, .p pv2 [pv2,pv11,pv53069], .c 7, .c 3, .c 19, .c 5,
  .c 3, .c 241, .c 29, .c 3, .c 5, .p pv5 [pv2,pv3,pv48647], .c 3, .c 107,
  .p pv3 [pv2,pv3,pv19,pv20483], .c 3, .c 7, .c 11, .c 3, .c 13, .c 5, .c 3,
  .p pv13 [pv2,pv1167539], .c 7, .c 3, .c 5, .c 419, .c 3, .c 11, .c 89, .c 3,
  .p pv3 [pv2,pv291887], .c 13, .c 3, .c 17, .c 5, .c 3, .c 7, .p pv19 [pv2,pv3,pv5,pv277,pv281],
  .c 3, .c 5, .p pv17 [pv2,pv3,pv7,pv27799], .c 3, .c 23, .c 7, .c 3, .c 53, .c 607, .c 3,
  .p pv2 [pv2,pv583783], .c 5, .c 3, .p pv2 [pv2,pv13,pv19,pv29,pv163], .c 61, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv35381], .c 3, .c 7, .p pv5 [pv2,pv3,pv48649], .c 3, .c 11, .c 349, .c 3,
  .c 641, .c 5, .c 3, .c 433, .c 17, .c 3, .c 5, .c 13, .c 3, .c 37, .p pv3 [pv2,pv3,pv89,pv4373],
  .c 3, .p pv2 [pv2,pv7,pv166799], .c 269, .c 3, .c 7, .c 5, .c 3, .c 31, .c 11, .c 3, .c 5, .c 7,
  .c 3, .p pv2 [pv2,pv5,pv293,pv797], .c 23, .c 3, .p pv3 [pv2,pv13,pv103,pv109],
  .p pv17 [pv2,pv3,pv37,pv67,pv157], .c 3, .c 11, .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv31],
  .c 3,
]
private theorem h0285c01 : checkBlock 2334979 128 b0285c01 = true := by
  decide +kernel

private def b0285c02 : List Row := [
  .c 5, .c 41, .c 3, .p pv3 [pv2,pv5,pv79,pv739], .p pv2 [pv2,pv3,pv7,pv13,pv47], .c 3,
  .p pv5 [pv2,pv1167623], .c 7, .c 3, .p pv3 [pv2,pv19,pv30727], .c 5, .c 3, .c 23, .c 31, .c 3,
  .c 5, .c 11, .c 3, .c 19, .c 17, .c 3, .c 7, .c 59, .c 3, .c 29, .c 5, .c 3, .c 11, .c 7, .c 3,
  .c 5, .p pv7 [pv2,pv3,pv12163], .c 3, .c 163, .p pv3 [pv2,pv3,pv137,pv947], .c 3, .c 13, .c 19,
  .c 3, .c 661, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv13,pv499], .c 3, .c 5, .c 173, .c 3,
  .c 631, .c 7, .c 3, .c 131, .c 53, .c 3, .c 73, .c 5, .c 3, .c 307, .c 23, .c 3, .c 5, .c 191,
  .c 3, .c 7, .p pv3 [pv2,pv3,pv389227], .c 3, .p pv11 [pv2,pv11,pv19,pv37,pv151],
  .p pv17 [pv2,pv3,pv7,pv13901], .c 3, .c 43, .c 5, .c 3, .c 1151, .p pv2 [pv2,pv3,pv5,pv38923],
  .c 3, .c 5, .c 277, .c 3, .c 281, .p pv5 [pv2,pv3,pv17,pv53], .c 3, .c 23, .c 11, .c 3, .c 7,
  .c 5, .c 3, .c 17, .c 13, .c 3, .c 5, .c 7, .c 3, .c 11, .c 19, .c 3,
  .p pv2 [pv2,pv17,pv149,pv461], .c 503, .c 3, .p pv3 [pv2,pv11,pv26539], .c 5, .c 3, .c 137,
  .p pv19 [pv2,pv3,pv5,pv37,pv263], .c 3, .c 5, .c 31, .c 3, .c 877, .c 769, .c 3, .c 29, .c 7,
  .c 3, .c 13, .c 5, .c 3, .c 97, .c 887, .c 3, .c 5, .c 17, .c 3,
  .p pv3 [pv2,pv5,pv7,pv19,pv439], .c 41, .c 3, .c 7, .c 13,
]
private theorem h0285c02 : checkBlock 2335235 128 b0285c02 = true := by
  decide +kernel

private def b0285c03 : List Row := [
  .c 3, .c 193, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 61, .c 3, .c 17, .c 1097, .c 3, .c 151,
  .p pv3 [pv2,pv3,pv19,pv6829], .c 3, .p pv2 [pv2,pv7,pv166823], .c 5, .c 3, .c 7, .c 11, .c 3,
  .c 5, .c 19, .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv1167773], .p pv7 [pv2,pv3,pv191,pv1019],
  .c 3, .c 11, .c 5, .c 3, .c 211, .p pv11 [pv2,pv3,pv5,pv19463], .c 3, .c 5, .c 13, .c 3, .c 7,
  .c 29, .c 3, .p pv3 [pv2,pv137,pv2131], .c 17, .c 3, .c 809, .c 5, .c 3, .c 431,
  .p pv11 [pv2,pv3,pv5,pv25951], .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv5839], .c 227, .c 3,
  .p pv5 [pv2,pv7,pv13,pv41,pv313], .c 1307, .c 3, .c 7, .c 5, .c 3, .c 11, .c 859, .c 3, .c 5,
  .c 7, .c 3, .c 29, .c 31, .c 3, .p pv2 [pv2,pv583909], .p pv3 [pv2,pv3,pv389273], .c 3, .c 521,
  .c 5, .c 3, .p pv3 [pv2,pv7,pv10427], .c 19, .c 3, .c 5, .c 53, .c 3,
  .p pv2 [pv2,pv5,pv29,pv4027], .c 11, .c 3, .p pv2 [pv2,pv1167833], .c 7, .c 3, .c 23, .c 5,
  .c 3, .p pv11 [pv2,pv1167839], .c 17, .c 3, .c 5, .c 67, .c 3, .p pv7 [pv2,pv5,pv7,pv61,pv547],
  .p pv2 [pv2,pv3,pv59,pv3299], .c 3, .c 7, .c 37, .c 3, .c 83, .c 5, .c 3,
  .p pv2 [pv2,pv19,pv73,pv421], .c 7, .c 3, .c 5, .c 43, .c 3, .p pv7 [pv2,pv5,pv58393], .c 13,
  .c 3, .c 19, .c 11, .c 3, .p pv2 [pv2,pv7,pv17,pv701], .c 5, .c 3, .c 7, .c 1093, .c 3, .c 5,
]
private theorem h0285c03 : checkBlock 2335491 128 b0285c03 = true := by
  decide +kernel

private def b0285c04 : List Row := [
  .c 29, .c 3, .c 11, .c 7, .c 3, .c 31, .c 47, .c 3, .c 53, .c 5, .c 3, .p pv3 [pv2,pv291971],
  .c 179, .c 3, .c 5, .c 379, .c 3, .c 7, .c 17, .c 3, .c 991,
  .p pv17 [pv2,pv3,pv7,pv13,pv23,pv31], .c 3, .c 79, .c 5, .c 3, .c 409, .c 13, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv11,pv47,pv251], .c 3, .c 23, .p pv5 [pv2,pv3,pv61,pv3191], .c 3, .c 11,
  .c 31, .c 3, .c 7, .c 5, .c 3, .c 71, .c 1091, .c 3, .c 5, .c 7, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv129769], .c 3, .c 37, .p pv7 [pv2,pv3,pv97327], .c 3, .c 13, .c 5, .c 3,
  .c 1459, .c 11, .c 3, .c 5, .c 331, .c 3, .p pv13 [pv2,pv5,pv109,pv2143], .c 61, .c 3,
  .p pv2 [pv2,pv583969], .c 7, .c 3, .c 11, .c 5, .c 3, .c 43, .p pv3 [pv2,pv3,pv5,pv77863], .c 3,
  .c 5, .c 1297, .c 3, .c 1129, .c 23, .c 3, .c 7, .p pv2 [pv2,pv3,pv194659], .c 3,
  .p pv3 [pv2,pv31,pv9419], .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 11, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv43,pv503], .c 3, .c 103, .c 443, .c 3, .c 31, .c 5, .c 3, .c 7, .c 79, .c 3,
  .c 5, .c 13, .c 3, .c 571, .c 7, .c 3, .p pv5 [pv2,pv263,pv4441], .p pv29 [pv2,pv3,pv8111],
  .c 3, .c 317, .c 5, .c 3, .c 29, .c 211, .c 3, .c 5, .c 17, .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv13,pv167,pv269], .c 1427, .c 3,
]
private theorem h0285c04 : checkBlock 2335747 128 b0285c04 = true := by
  decide +kernel

private def b0285c05 : List Row := [
  .c 157, .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv77867], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv41,pv1187], .c 3, .c 17, .p pv7 [pv2,pv3,pv13,pv67,pv149], .c 3,
  .p pv5 [pv2,pv7,pv11,pv197], .c 101, .c 3, .c 7, .c 5, .c 3, .p pv29 [pv2,pv17,pv127,pv541],
  .c 23, .c 3, .c 5, .c 7, .c 3, .c 97, .p pv5 [pv2,pv3,pv194671], .c 3, .c 41, .c 11, .c 3,
  .p pv5 [pv2,pv1168031], .c 5, .c 3, .c 19, .c 733, .c 3, .c 5, .c 1487, .c 3, .c 11, .c 479,
  .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv11,pv53093], .c 5, .c 3, .c 373,
  .p pv7 [pv2,pv3,pv5,pv13,pv599], .c 3, .c 5, .c 19, .c 3, .p pv7 [pv2,pv5,pv7,pv23,pv1451],
  .c 13, .c 3, .c 7, .p pv3 [pv2,pv3,pv83,pv4691], .c 3, .c 17, .c 5, .c 3, .c 31, .c 7, .c 3,
  .c 5, .p pv17 [pv2,pv3,pv11,pv8849], .c 3, .c 863, .c 37, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv97,pv223], .c 3, .c 29, .c 5, .c 3, .c 7, .c 89, .c 3, .c 5, .c 181, .c 3,
  .c 149, .c 7, .c 3, .p pv3 [pv2,pv146011], .c 23, .c 3, .c 19, .c 5, .c 3,
  .p pv2 [pv2,pv79,pv7393], .c 11, .c 3, .c 5, .c 109, .c 3, .c 7, .c 1367, .c 3,
  .p pv5 [pv2,pv349,pv3347], .p pv23 [pv2,pv3,pv7,pv17,pv409], .c 3, .c 11, .c 5, .c 3, .c 73,
  .c 19, .c 3, .c 5, .p pv2 [pv2,pv3,pv401,pv971], .c 3, .c 101, .c 43, .c 3, .c 547, .c 61, .c 3,
  .c 7, .c 5, .c 3, .c 947, .p pv3 [pv2,pv3,pv5,pv7,pv89], .c 3, .c 5, .c 7,
]
private theorem h0285c05 : checkBlock 2336003 128 b0285c05 = true := by
  decide +kernel

private def b0285c06 : List Row := [
  .c 3, .c 137, .p pv3 [pv2,pv3,pv41,pv9497], .c 3, .c 79, .c 13, .c 3, .c 577, .c 5, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv5,pv19469], .c 3, .c 5, .p pv3 [pv2,pv3,pv389381], .c 3, .c 37, .c 17, .c 3,
  .c 19, .c 7, .c 3, .c 41, .c 5, .c 3, .p pv2 [pv2,pv13,pv179,pv251],
  .p pv37 [pv2,pv3,pv5,pv17,pv509], .c 3, .c 5, .c 23, .c 3, .c 13, .c 11, .c 3, .c 7, .c 1229,
  .c 3, .p pv2 [pv2,pv101,pv5783], .c 5, .c 3, .c 89, .c 7, .c 3, .c 5, .c 13, .c 3, .c 347,
  .p pv7 [pv2,pv3,pv24337], .c 3, .c 67, .p pv7 [pv2,pv3,pv439,pv887], .c 3, .c 23, .c 5, .c 3,
  .c 7, .c 223, .c 3, .c 5, .c 31, .c 3, .p pv2 [pv2,pv5,pv116819], .c 7, .c 3, .c 257, .c 11,
  .c 3, .p pv3 [pv2,pv19,pv809], .c 5, .c 3, .c 13, .c 467, .c 3, .c 5, .p pv5 [pv2,pv3,pv389401],
  .c 3, .c 7, .p pv11 [pv2,pv3,pv13,pv17,pv881], .c 3, .c 47, .c 127, .c 3, .c 151, .c 5, .c 3,
  .c 17, .p pv3 [pv2,pv3,pv5,pv19,pv4099], .c 3, .c 5, .p pv2 [pv2,pv3,pv64901], .c 3,
  .p pv3 [pv2,pv5,pv58411], .c 29, .c 3, .p pv5 [pv2,pv7,pv17,pv9817], .c 19, .c 3, .c 7, .c 5,
  .c 3, .c 59, .p pv11 [pv2,pv3,pv5,pv7,pv5563], .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv31,pv7537], .p pv5 [pv2,pv3,pv29,pv373], .c 3, .c 11,
  .p pv3 [pv2,pv3,pv23,pv16931], .c 3, .c 61, .c 5, .c 3, .p pv3 [pv2,pv7,pv11,pv3793], .c 43,
  .c 3, .c 5, .c 17, .c 3, .c 23, .c 13, .c 3, .c 353, .c 7, .c 3, .c 37,
]
private theorem h0285c06 : checkBlock 2336259 128 b0285c06 = true := by
  decide +kernel

private def b0285c07 : List Row := [
  .c 5, .c 3, .p pv11 [pv2,pv59,pv19801], .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv14423], .c 3,
  .c 17, .c 83, .c 3, .c 7, .c 71, .c 3, .c 11, .c 5, .c 3, .c 41, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv194713], .c 3, .p pv3 [pv2,pv5,pv29207], .c 19, .c 3, .c 1019,
  .p pv23 [pv2,pv3,pv13,pv7489], .c 3, .p pv2 [pv2,pv7,pv83449], .c 5, .c 3, .c 7, .c 13, .c 3,
  .c 5, .c 11, .c 3, .c 983, .c 7, .c 3, .p pv2 [pv2,pv449,pv1301], .c 17, .c 3, .c 787, .c 5,
  .c 3, .c 11, .c 53, .c 3, .c 5, .c 29, .c 3, .c 7, .p pv5 [pv2,pv3,pv389437], .c 3, .c 401,
  .p pv2 [pv2,pv3,pv7,pv27817], .c 3, .c 13, .c 5, .c 3, .c 19, .c 457, .c 3, .c 5, .c 131, .c 3,
  .c 193, .c 11, .c 3, .c 73, .c 13, .c 3, .c 7, .c 5, .c 3, .c 491,
  .p pv3 [pv2,pv3,pv5,pv7,pv3709], .c 3, .c 5, .c 7, .c 3, .c 71, .c 383, .c 3, .c 31, .c 367,
  .c 3, .c 1237, .c 5, .c 3, .c 47, .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv43,pv3019], .c 3, .c 13,
  .c 41, .c 3, .c 53, .c 7, .c 3, .c 389, .c 5, .c 3, .c 139, .c 23, .c 3, .c 5, .c 13, .c 3,
  .c 11, .p pv5 [pv2,pv3,pv109,pv397], .c 3, .c 7, .c 31, .c 3, .c 19, .c 5, .c 3, .c 67, .c 7,
  .c 3, .c 5, .c 149, .c 3,
]
private theorem h0285c07 : checkBlock 2336515 128 b0285c07 = true := by
  decide +kernel

private def b0285c08 : List Row := [
  .p pv2 [pv2,pv5,pv53,pv4409], .c 107, .c 3, .c 23, .c 773, .c 3, .p pv5 [pv2,pv7,pv83,pv2011],
  .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 439, .c 3, .p pv3 [pv2,pv5,pv23,pv127], .c 7, .c 3,
  .c 11, .c 37, .c 3, .c 59, .c 5, .c 3, .c 509, .p pv23 [pv2,pv3,pv5,pv17,pv29,pv79], .c 3, .c 5,
  .c 97, .c 3, .c 7, .c 271, .c 3, .c 17, .p pv13 [pv2,pv3,pv7,pv55639], .c 3,
  .p pv2 [pv2,pv31,pv37691], .c 5, .c 3, .c 29, .c 11, .c 3, .c 5, .c 199, .c 3,
  .p pv2 [pv2,pv5,pv331,pv353], .p pv3 [pv2,pv3,pv11,pv35407], .c 3, .c 13, .c 23, .c 3, .c 7,
  .c 5, .c 3, .c 1249, .p pv19 [pv2,pv3,pv5,pv7,pv13,pv107], .c 3, .c 5, .c 7, .c 3, .c 181,
  .c 13, .c 3, .p pv3 [pv2,pv18257], .c 79, .c 3, .p pv5 [pv2,pv1168451], .c 5, .c 3, .c 131,
  .p pv3 [pv2,pv3,pv5,pv61,pv1277], .c 3, .c 5, .c 11, .c 3, .c 43,
  .p pv2 [pv2,pv3,pv7,pv17,pv1091], .c 3, .c 127, .c 7, .c 3, .p pv2 [pv2,pv13,pv3457], .c 5,
  .c 3, .c 11, .c 1499, .c 3, .c 5, .p pv2 [pv2,pv3,pv137,pv2843], .c 3, .c 829, .c 113, .c 3,
  .c 7, .c 41, .c 3, .c 1123, .c 5, .c 3, .p pv3 [pv2,pv293,pv997], .c 7, .c 3, .c 5, .c 241,
  .c 3, .c 19, .c 11, .c 3, .c 107, .p pv2 [pv2,pv3,pv194749], .c 3, .p pv3 [pv2,pv7,pv10433],
  .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv19,pv41], .c 3, .c 5, .c 17, .c 3, .c 197, .c 7, .c 3,
  .c 919, .c 19, .c 3, .c 13, .c 5,
]
private theorem h0285c08 : checkBlock 2336771 128 b0285c08 = true := by
  decide +kernel

private def b0285c09 : List Row := [
  .c 3, .p pv2 [pv2,pv31,pv47,pv401], .c 37, .c 3, .c 5, .c 193, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv389507], .c 3, .p pv5 [pv2,pv1168523], .c 11, .c 3, .c 23, .c 5, .c 3, .c 31,
  .c 251, .c 3, .c 5, .p pv3 [pv2,pv3,pv113,pv383], .c 3, .c 11, .p pv13 [pv2,pv3,pv181,pv269],
  .c 3, .c 281, .p pv23 [pv2,pv3,pv389513], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv13,pv53],
  .p pv7 [pv2,pv3,pv5,pv7,pv31,pv359], .c 3, .c 5, .c 7, .c 3, .c 13, .c 571, .c 3, .c 71, .c 17,
  .c 3, .c 487, .c 5, .c 3, .p pv7 [pv2,pv7,pv97,pv1721], .c 31, .c 3, .c 5, .c 13, .c 3, .c 1153,
  .c 19, .c 3, .c 11, .c 7, .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv11,pv53117],
  .p pv3 [pv2,pv3,pv5,pv15581], .c 3, .c 5, .p pv2 [pv2,pv3,pv64921], .c 3, .c 67,
  .p pv3 [pv2,pv3,pv389527], .c 3, .c 7, .c 47, .c 3, .c 103, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv389531], .c 3, .c 23, .p pv5 [pv2,pv3,pv11,pv13,pv227], .c 3, .c 29, .c 1181,
  .c 3, .c 11, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .p pv53 [pv2,pv3,pv7,pv37,pv47], .c 3,
  .p pv2 [pv2,pv5,pv137,pv853], .c 7, .c 3, .p pv2 [pv2,pv29,pv59,pv683], .c 89, .c 3,
  .p pv3 [pv2,pv146077], .c 5, .c 3, .c 967, .c 73, .c 3, .c 5, .c 11, .c 3, .c 7, .c 37, .c 3,
  .c 13, .c 157, .c 3, .c 47, .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv13,pv461], .c 3, .c 5,
  .c 1031, .c 3, .c 263,
]
private theorem h0285c09 : checkBlock 2337027 128 b0285c09 = true := by
  decide +kernel

private def b0285c10 : List Row := [
  .c 13, .c 3, .c 41, .c 601, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv599,pv1951], .c 883, .c 3,
  .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv47,pv4973], .c 11, .c 3, .p pv2 [pv2,pv499,pv1171],
  .p pv3 [pv2,pv3,pv89,pv1459], .c 3, .c 19, .c 5, .c 3, .c 23, .c 547, .c 3, .c 5, .c 61, .c 3,
  .c 269, .p pv19 [pv2,pv3,pv7,pv19,pv29,pv101], .c 3, .c 17, .c 7, .c 3, .c 53, .c 5, .c 3,
  .p pv13 [pv2,pv281,pv4159], .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv389561], .c 3, .c 29, .c 79,
  .c 3, .c 7, .c 11, .c 3, .c 1061, .c 5, .c 3, .p pv2 [pv2,pv584347], .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv109,pv1787], .c 3, .c 11, .c 59, .c 3, .c 89, .c 97, .c 3, .c 13, .c 5, .c 3,
  .c 7, .c 23, .c 3, .c 5, .c 577, .c 3, .c 31, .c 7, .c 3, .c 19, .c 13, .c 3, .c 101, .c 5,
  .c 3, .c 17, .c 41, .c 3, .c 5, .c 739, .c 3, .c 7, .p pv5 [pv2,pv3,pv31,pv59,pv71], .c 3,
  .c 11, .c 719, .c 3, .c 659, .c 5, .c 3, .p pv7 [pv2,pv11,pv13,pv743],
  .p pv23 [pv2,pv3,pv5,pv43,pv151], .c 3, .c 5, .c 29, .c 3, .c 13, .c 31, .c 3,
  .p pv3 [pv2,pv7,pv67,pv89], .c 167, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv584377], .c 11, .c 3,
  .c 5, .c 7, .c 3, .c 59, .c 43, .c 3, .p pv5 [pv2,pv1168763], .c 83, .c 3, .c 11, .c 5, .c 3,
]
private theorem h0285c10 : checkBlock 2337283 128 b0285c10 = true := by
  decide +kernel

private def b0285c11 : List Row := [
  .p pv2 [pv2,pv7,pv166967], .p pv2 [pv2,pv3,pv5,pv38959], .c 3, .c 5, .p pv2 [pv2,pv3,pv389591],
  .c 3, .c 17, .p pv5 [pv2,pv3,pv7,pv773], .c 3, .c 607, .c 7, .c 3, .c 67, .c 5, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv5,pv19,pv1367], .c 3, .c 5, .c 11, .c 3, .c 61, .c 163, .c 3, .c 7, .c 19,
  .c 3, .p pv3 [pv2,pv47,pv6217], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5,
  .p pv17 [pv2,pv3,pv73,pv593], .c 3, .c 647, .p pv2 [pv2,pv3,pv83,pv2347], .c 3, .c 31, .c 17,
  .c 3, .c 37, .c 5, .c 3, .c 7, .c 113, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv17,pv1637], .c 3,
  .p pv3 [pv2,pv5,pv58441], .c 7, .c 3, .c 13, .c 191, .c 3, .c 17, .c 5, .c 3, .c 239, .c 29,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv167,pv2333], .c 3, .c 7, .c 13, .c 3, .p pv2 [pv2,pv11,pv53129],
  .c 31, .c 3, .p pv2 [pv2,pv1168841], .c 5, .c 3, .c 79, .p pv2 [pv2,pv3,pv5,pv29,pv2687], .c 3,
  .c 5, .c 23, .c 3, .p pv3 [pv2,pv5,pv97,pv241], .c 19, .c 3, .c 1097, .c 11, .c 3, .c 7, .c 5,
  .c 3, .c 29, .c 17, .c 3, .c 5, .c 7, .c 3, .c 11, .c 47, .c 3, .p pv3 [pv2,pv107,pv2731],
  .c 347, .c 3, .c 23, .c 5, .c 3, .c 173, .c 13, .c 3, .c 5, .c 59, .c 3,
  .p pv3 [pv2,pv5,pv19,pv769], .c 89, .c 3, .c 433, .c 7, .c 3, .p pv2 [pv2,pv17,pv31,pv1109],
  .c 5, .c 3, .c 19, .c 43, .c 3, .c 5, .c 311, .c 3, .c 103, .p pv5 [pv2,pv3,pv761],
]
private theorem h0285c11 : checkBlock 2337539 128 b0285c11 = true := by
  decide +kernel

private def b0285c12 : List Row := [
  .c 3, .c 7, .c 197, .c 3, .c 13, .c 5, .c 3, .c 193, .c 7, .c 3, .c 5, .c 19, .c 3,
  .p pv3 [pv2,pv5,pv41,pv2851], .c 17, .c 3, .c 47, .c 13, .c 3, .c 167, .c 5, .c 3, .c 7, .c 11,
  .c 3, .c 5, .c 79, .c 3, .p pv2 [pv2,pv5,pv46757], .c 7, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv23,pv5647], .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv13,pv44959],
  .p pv3 [pv2,pv3,pv5,pv77929], .c 3, .c 5, .c 1453, .c 3, .c 7, .c 53, .c 3, .c 157,
  .p pv19 [pv2,pv3,pv7,pv71], .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv67,pv73,pv239],
  .p pv2 [pv2,pv3,pv5,pv7793], .c 3, .c 5, .c 11, .c 3, .p pv7 [pv2,pv5,pv43,pv5437],
  .p pv5 [pv2,pv3,pv19,pv1709], .c 3, .c 271, .c 37, .c 3, .c 7, .c 5, .c 3, .c 11, .c 19, .c 3,
  .c 5, .c 7, .c 3, .c 89, .c 41, .c 3, .c 61, .p pv7 [pv2,pv3,pv101,pv643], .c 3, .c 43, .c 5,
  .c 3, .c 13, .c 977, .c 3, .c 5, .p pv3 [pv2,pv3,pv129887], .c 3, .c 73, .c 11, .c 3, .c 181,
  .c 7, .c 3, .p pv5 [pv2,pv613,pv1907], .c 5, .c 3, .c 31, .c 97, .c 3, .c 5, .c 103, .c 3,
  .c 1291, .p pv2 [pv2,pv3,pv193,pv673], .c 3, .c 7, .c 29, .c 3, .c 1091, .c 5, .c 3, .c 23,
  .c 7, .c 3, .c 5, .c 17, .c 3, .c 191, .c 1381, .c 3, .c 13, .c 11, .c 3,
  .p pv2 [pv2,pv7,pv23,pv53,pv137], .c 5, .c 3, .c 7,
]
private theorem h0285c12 : checkBlock 2337795 128 b0285c12 = true := by
  decide +kernel

private def b0285c13 : List Row := [
  .c 31, .c 3, .c 5, .c 107, .c 3, .c 11, .c 7, .c 3, .c 29, .c 61, .c 3, .c 853, .c 5, .c 3,
  .p pv29 [pv2,pv17,pv68767], .p pv13 [pv2,pv3,pv5,pv4871], .c 3, .c 5, .c 487, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv21649], .c 3, .p pv3 [pv2,pv29,pv5039], .c 67, .c 3,
  .p pv5 [pv2,pv13,pv19,pv4733], .c 5, .c 3, .c 47, .c 23, .c 3, .c 5, .c 73, .c 3, .c 19,
  .p pv3 [pv2,pv3,pv389687], .c 3, .c 11, .c 17, .c 3, .c 7, .c 5, .c 3, .c 563, .c 13, .c 3,
  .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv101,pv463], .p pv5 [pv2,pv3,pv97423], .c 3, .c 23, .c 19,
  .c 3, .c 17, .c 5, .c 3, .p pv3 [pv2,pv7,pv43,pv971], .c 11, .c 3, .c 5, .c 787, .c 3,
  .p pv3 [pv2,pv5,pv13,pv17,pv23], .c 29, .c 3, .c 1277, .c 7, .c 3, .c 11, .c 5, .c 3, .c 593,
  .c 53, .c 3, .c 5, .p pv3 [pv2,pv3,pv13,pv31,pv967], .c 3, .c 43, .p pv2 [pv2,pv3,pv29,pv6719],
  .c 3, .c 7, .c 13, .c 3, .c 1307, .c 5, .c 3, .c 59, .c 7, .c 3, .c 5, .c 11, .c 3, .c 29,
  .c 71, .c 3, .p pv5 [pv2,pv907,pv1289], .c 23, .c 3, .c 409, .c 5, .c 3, .c 7,
  .p pv31 [pv2,pv3,pv5,pv38971], .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv55673], .c 3, .c 13, .c 7,
  .c 3, .c 179, .c 389, .c 3, .p pv2 [pv2,pv17,pv97,pv709], .c 5, .c 3, .c 37,
  .p pv2 [pv2,pv3,pv5,pv25981], .c 3, .c 5, .c 13, .c 3, .c 7, .c 11, .c 3,
]
private theorem h0285c13 : checkBlock 2338051 128 b0285c13 = true := by
  decide +kernel

private def b0285c14 : List Row := [
  .c 53, .c 113, .c 3, .c 61, .c 5, .c 3, .c 229, .c 79, .c 3, .c 5, .c 227, .c 3,
  .p pv2 [pv2,pv5,pv19,pv31,pv397], .c 17, .c 3, .c 373, .c 181, .c 3, .c 7, .c 5, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv5,pv7,pv17,pv131], .c 3, .c 5, .c 7, .c 3, .c 31, .c 37, .c 3, .c 17, .c 11,
  .c 3, .c 757, .c 5, .c 3, .c 97, .p pv2 [pv2,pv3,pv5,pv11,pv1181], .c 3, .c 5, .c 19, .c 3,
  .c 11, .c 653, .c 3, .c 139, .c 7, .c 3, .p pv2 [pv2,pv11,pv106291], .c 5, .c 3, .c 73,
  .p pv17 [pv2,pv3,pv5,pv23,pv3389], .c 3, .c 5, .c 269, .c 3, .p pv2 [pv2,pv5,pv7,pv16703],
  .c 31, .c 3, .c 7, .c 283, .c 3, .c 23, .c 5, .c 3, .c 419, .c 7, .c 3, .c 5, .c 503, .c 3,
  .c 127, .c 13, .c 3, .c 11, .c 271, .c 3, .c 19, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv2887],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv41,pv97], .c 3, .c 131, .c 7, .c 3, .c 1171,
  .p pv7 [pv2,pv3,pv32479], .c 3, .p pv2 [pv2,pv13,pv44971], .c 5, .c 3, .c 1481, .c 11, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv129917], .c 3, .c 7, .c 211, .c 3, .c 41, .c 53, .c 3, .c 11, .c 5,
  .c 3, .c 769, .c 13, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv116927],
  .p pv3 [pv2,pv3,pv129919], .c 3, .c 31, .p pv13 [pv2,pv3,pv23,pv37,pv229], .c 3, .c 7, .c 5,
  .c 3, .p pv11 [pv2,pv19,pv41,pv79], .c 163,
]
private theorem h0285c14 : checkBlock 2338307 128 b0285c14 = true := by
  decide +kernel

private def b0285c15 : List Row := [
  .c 3, .c 5, .c 7, .c 3, .c 17, .c 97, .c 3, .c 19, .c 47, .c 3, .c 13, .c 5, .c 3, .c 11,
  .c 643, .c 3, .c 5, .c 443, .c 3, .c 223, .p pv2 [pv2,pv3,pv7,pv55681], .c 3,
  .p pv5 [pv2,pv431,pv2713], .c 7, .c 3, .c 463, .c 5, .c 3, .p pv2 [pv2,pv29,pv61,pv661], .c 233,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv47,pv8293], .c 3, .p pv7 [pv2,pv5,pv7,pv33409], .c 11, .c 3, .c 7,
  .c 17, .c 3, .p pv2 [pv2,pv59,pv19819], .c 5, .c 3, .c 349, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv17,pv1433], .c 3, .c 13, .c 23, .c 3, .p pv2 [pv2,pv11,pv106303], .c 71, .c 3,
  .c 17, .c 5, .c 3, .c 7, .c 41, .c 3, .c 5, .c 13, .c 3, .c 19, .c 7, .c 3,
  .p pv3 [pv2,pv37,pv7901], .c 11, .c 3, .p pv5 [pv2,pv31,pv67,pv563], .c 5, .c 3, .c 23, .c 277,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv79,pv2467], .c 3, .c 7, .p pv2 [pv2,pv3,pv41,pv3169], .c 3, .c 43,
  .c 19, .c 3, .c 31, .c 5, .c 3, .c 13, .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv389791], .c 3,
  .p pv7 [pv2,pv5,pv1871], .c 857, .c 3, .p pv2 [pv2,pv7,pv101,pv827], .c 727, .c 3, .c 7, .c 5,
  .c 3, .c 67, .c 607, .c 3, .c 5, .c 7, .c 3, .c 227, .p pv3 [pv2,pv3,pv389797], .c 3, .c 11,
  .c 1039, .c 3, .c 1163, .c 5, .c 3, .p pv13 [pv2,pv7,pv11,pv15187], .c 23, .c 3, .c 5, .c 37,
  .c 3, .c 71, .c 43, .c 3, .c 13,
]
private theorem h0285c15 : checkBlock 2338563 128 b0285c15 = true := by
  decide +kernel

private def b0285c16 : List Row := [
  .c 7, .c 3, .p pv5 [pv2,pv1169411], .c 5, .c 3, .c 157, .c 11, .c 3, .c 5, .c 53, .c 3, .c 449,
  .c 13, .c 3, .c 7, .p pv11 [pv2,pv3,pv2707], .c 3, .c 11, .c 5, .c 3, .c 263, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv129937], .c 3, .p pv19 [pv2,pv5,pv23,pv10169], .p pv5 [pv2,pv3,pv97453], .c 3,
  .c 17, .c 29, .c 3, .p pv2 [pv2,pv7,pv13,pv71,pv181], .c 5, .c 3, .c 7, .c 367, .c 3, .c 5,
  .c 11, .c 3, .p pv2 [pv2,pv5,pv19,pv1231], .c 7, .c 3, .c 719, .c 1283, .c 3, .c 107, .c 5,
  .c 3, .c 11, .c 13, .c 3, .c 5, .c 41, .c 3, .c 7, .p pv2 [pv2,pv3,pv194911], .c 3, .c 29,
  .c 23, .c 3, .c 53, .c 5, .c 3, .p pv2 [pv2,pv584737], .p pv3 [pv2,pv3,pv5,pv31,pv503], .c 3,
  .c 5, .c 19, .c 3, .c 97, .c 11, .c 3, .c 193, .p pv17 [pv2,pv3,pv41,pv2377], .c 3, .c 7, .c 5,
  .c 3, .c 17, .c 31, .c 3, .c 5, .c 7, .c 3, .c 709, .c 73, .c 3,
  .p pv2 [pv2,pv11,pv17,pv53,pv59], .c 13, .c 3, .c 733, .c 5, .c 3, .c 41,
  .p pv3 [pv2,pv3,pv5,pv8663], .c 3, .c 5, .c 1013, .c 3, .p pv2 [pv2,pv5,pv107,pv1093], .c 83,
  .c 3, .c 103, .c 7, .c 3, .c 19, .c 5, .c 3, .p pv23 [pv2,pv13,pv89963],
  .p pv17 [pv2,pv3,pv5,pv11,pv443], .c 3, .c 5, .c 17, .c 3, .c 11, .c 29, .c 3, .c 7, .c 101,
  .c 3, .c 181, .c 5, .c 3, .c 251, .c 7, .c 3,
]
private theorem h0285c16 : checkBlock 2338819 128 b0285c16 = true := by
  decide +kernel

private def b0285c17 : List Row := [
  .c 5, .c 13, .c 3, .c 17, .c 373, .c 3, .c 233, .p pv19 [pv2,pv3,pv48731], .c 3, .c 239, .c 5,
  .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv23,pv113], .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv11,pv61,pv83],
  .c 3, .c 29, .c 7, .c 3, .c 11, .p pv31 [pv2,pv3,pv4813], .c 3, .c 23, .c 5, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv5,pv103,pv757], .c 3, .c 5, .p pv5 [pv2,pv3,pv31,pv131], .c 3, .c 7, .c 47,
  .c 3, .c 19, .c 17, .c 3, .c 907, .c 5, .c 3, .c 569, .c 11, .c 3, .c 5, .c 31, .c 3, .c 67,
  .c 41, .c 3, .c 37, .p pv3 [pv2,pv3,pv197,pv1979], .c 3, .c 7, .c 5, .c 3, .c 83,
  .p pv3 [pv2,pv3,pv5,pv7,pv47,pv79], .c 3, .c 5, .c 7, .c 3, .c 619, .c 467, .c 3, .c 13,
  .c 1123, .c 3, .c 113, .c 5, .c 3, .c 1489, .p pv2 [pv2,pv3,pv5,pv13,pv2999], .c 3, .c 5, .c 11,
  .c 3, .c 139, .c 13, .c 3, .c 47, .c 7, .c 3, .c 43, .c 5, .c 3, .c 11, .c 17, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv29,pv3361], .c 3, .c 19, .p pv3 [pv2,pv3,pv129959], .c 3, .c 7, .c 79, .c 3,
  .c 1429, .c 5, .c 3, .c 661, .c 7, .c 3, .c 5, .p pv11 [pv2,pv3,pv43,pv9067], .c 3, .c 31,
  .c 11, .c 3, .p pv3 [pv2,pv41,pv1783], .c 19, .c 3, .p pv5 [pv2,pv7,pv17,pv9829], .c 5, .c 3,
  .c 7, .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv9283], .c 3, .p pv3 [pv2,pv5,pv233,pv251], .c 7,
  .c 3, .p pv11 [pv2,pv11,pv113,pv941], .c 43,
]
private theorem h0285c17 : checkBlock 2339075 128 b0285c17 = true := by
  decide +kernel

private def b0285c18 : List Row := [
  .c 3, .p pv2 [pv2,pv239,pv2447], .c 5, .c 3, .c 1031, .c 107, .c 3, .c 5, .c 349, .c 3, .c 7,
  .c 17, .c 3, .c 211, .c 11, .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv191,pv1531],
  .p pv11 [pv2,pv3,pv5,pv11,pv17,pv139], .c 3, .c 5, .c 1249, .c 3, .c 11, .c 457, .c 3, .c 17,
  .c 13, .c 3, .c 7, .c 5, .c 3, .c 23, .c 29, .c 3, .c 5, .c 7, .c 3, .c 61, .c 19, .c 3,
  .p pv3 [pv2,pv292427], .c 41, .c 3, .p pv5 [pv2,pv23,pv50857], .c 5, .c 3,
  .p pv2 [pv2,pv7,pv13,pv6427], .c 73, .c 3, .c 5, .c 1153, .c 3, .c 13, .c 151, .c 3, .c 11,
  .c 7, .c 3, .c 503, .c 5, .c 3, .c 29, .p pv7 [pv2,pv3,pv5,pv41,pv317], .c 3, .c 5, .c 13, .c 3,
  .c 257, .c 37, .c 3, .c 7, .c 173, .c 3, .c 443, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 421,
  .c 3, .c 41, .c 167, .c 3, .p pv2 [pv2,pv13,pv17,pv67,pv79], .c 139, .c 3, .c 11, .c 5, .c 3,
  .c 7, .c 71, .c 3, .c 5, .c 19, .c 3, .c 1493, .c 7, .c 3, .c 23, .c 31, .c 3, .c 89, .c 5,
  .c 3, .c 137, .p pv3 [pv2,pv3,pv5,pv1733], .c 3, .c 5, .c 11, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv389927], .c 3, .c 379, .p pv17 [pv2,pv3,pv7,pv11,pv211], .c 3, .c 67, .c 5,
  .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv38993], .c 3, .c 5,
]
private theorem h0285c18 : checkBlock 2339331 128 b0285c18 = true := by
  decide +kernel

private def b0285c19 : List Row := [
  .c 43, .c 3, .c 17, .c 863, .c 3, .c 13, .c 1223, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv17,pv17203], .p pv3 [pv2,pv3,pv5,pv7,pv13,pv857], .c 3, .c 5, .c 7, .c 3, .c 37,
  .c 11, .c 3, .p pv2 [pv2,pv719,pv1627], .c 23, .c 3, .c 29, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv167117], .c 19, .c 3, .c 5, .c 307, .c 3, .p pv2 [pv2,pv5,pv73,pv641], .c 311,
  .c 3, .p pv3 [pv2,pv11,pv2417], .c 7, .c 3, .c 31, .c 5, .c 3, .p pv2 [pv2,pv584917],
  .p pv3 [pv2,pv3,pv5,pv167,pv467], .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv3823], .c 3,
  .p pv3 [pv2,pv5,pv7,pv2089], .p pv2 [pv2,pv3,pv389947], .c 3, .c 7, .c 11, .c 3, .c 17, .c 5,
  .c 3, .c 653, .c 7, .c 3, .c 5, .c 47, .c 3, .c 11, .p pv7 [pv2,pv3,pv677], .c 3, .c 19,
  .p pv3 [pv2,pv3,pv389953], .c 3, .c 73, .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv25997], .c 3,
  .c 5, .c 97, .c 3, .p pv3 [pv2,pv5,pv13,pv8999], .c 7, .c 3, .c 41, .c 29, .c 3, .c 13, .c 5,
  .c 3, .c 43, .c 17, .c 3, .c 5, .c 23, .c 3, .c 7, .p pv2 [pv2,pv3,pv194981], .c 3, .c 11,
  .c 13, .c 3, .p pv5 [pv2,pv587,pv1993], .c 5, .c 3, .c 823, .c 53, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv73,pv2671], .c 3, .c 47, .p pv7 [pv2,pv3,pv43,pv3023], .c 3, .c 29,
  .p pv7 [pv2,pv3,pv24373], .c 3, .c 7, .c 5, .c 3, .c 277, .c 11, .c 3, .c 5, .c 7, .c 3, .c 13,
  .p pv5 [pv2,pv3,pv11,pv8863], .c 3, .c 167, .c 331, .c 3,
]
private theorem h0285c19 : checkBlock 2339587 128 b0285c19 = true := by
  decide +kernel

private def b0285c20 : List Row := [
  .c 11, .c 5, .c 3, .c 31, .c 103, .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv116993], .c 17,
  .c 3, .c 101, .c 7, .c 3, .c 509, .c 5, .c 3, .p pv11 [pv2,pv1169939], .c 59, .c 3, .c 5, .c 11,
  .c 3, .c 113, .p pv7 [pv2,pv3,pv64997], .c 3, .c 7, .c 61, .c 3, .c 109, .c 5, .c 3, .c 11,
  .c 7, .c 3, .c 5, .c 37, .c 3, .p pv3 [pv2,pv5,pv11,pv2659], .c 29, .c 3,
  .p pv5 [pv2,pv19,pv139,pv443], .p pv19 [pv2,pv3,pv23,pv157], .c 3, .p pv2 [pv2,pv7,pv193,pv433],
  .c 5, .c 3, .c 7, .c 191, .c 3, .c 5, .c 71, .c 3, .c 23, .c 7, .c 3, .c 557, .c 997, .c 3,
  .p pv2 [pv2,pv359,pv3259], .c 5, .c 3, .p pv3 [pv2,pv101,pv181], .c 839, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv97499], .c 3, .c 7, .c 19, .c 3, .c 13, .c 47, .c 3, .c 41, .c 5, .c 3, .c 17,
  .p pv7 [pv2,pv3,pv5,pv13], .c 3, .c 5, .p pv3 [pv2,pv3,pv390001], .c 3,
  .p pv2 [pv2,pv5,pv29,pv8069], .c 13, .c 3, .c 43, .c 11, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv37,pv97,pv163], .c 269, .c 3, .c 5, .c 7, .c 3, .c 11, .c 23, .c 3, .c 151,
  .c 239, .c 3, .c 131, .c 5, .c 3, .c 19, .p pv17 [pv2,pv3,pv5,pv43,pv907], .c 3, .c 5, .c 17,
  .c 3, .p pv13 [pv2,pv5,pv234007], .c 251, .c 3, .c 89, .c 7, .c 3, .c 47, .c 5, .c 3, .c 23,
  .c 13, .c 3, .c 5, .c 19,
]
private theorem h0285c20 : checkBlock 2339843 128 b0285c20 = true := by
  decide +kernel

private def b0285c21 : List Row := [
  .c 3, .c 17, .c 43, .c 3, .c 7, .c 53, .c 3, .c 1093, .c 5, .c 3,
  .p pv11 [pv2,pv11,pv17,pv6257], .c 7, .c 3, .c 5, .c 283, .c 3, .c 1231,
  .p pv23 [pv2,pv3,pv191,pv1021], .c 3, .c 467, .c 37, .c 3, .c 13, .c 5, .c 3, .c 7, .c 11, .c 3,
  .c 5, .c 41, .c 3, .c 73, .c 7, .c 3, .p pv5 [pv2,pv89,pv13147], .c 13, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv1170089], .c 23, .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv22943], .c 3, .c 7,
  .p pv13 [pv2,pv3,pv19,pv1283], .c 3, .c 107, .c 647, .c 3, .c 17, .c 5, .c 3,
  .p pv17 [pv2,pv13,pv11251], .c 19, .c 3, .c 5, .c 11, .c 3, .c 13, .p pv3 [pv2,pv3,pv97,pv4021],
  .c 3, .c 23, .c 127, .c 3, .c 7, .c 5, .c 3, .c 11, .p pv11 [pv2,pv3,pv5,pv7,pv199], .c 3, .c 5,
  .c 7, .c 3, .p pv2 [pv2,pv5,pv11,pv23,pv37], .p pv5 [pv2,pv3,pv31,pv233], .c 3,
  .p pv3 [pv2,pv73133], .p pv2 [pv2,pv3,pv390043], .c 3, .c 103, .c 5, .c 3,
  .p pv11 [pv2,pv7,pv19,pv53,pv83], .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv195023], .c 3, .c 617,
  .c 11, .c 3, .c 19, .c 7, .c 3, .c 599, .c 5, .c 3, .c 13, .c 313, .c 3, .c 5, .c 73, .c 3,
  .c 1087, .p pv5 [pv2,pv3,pv13,pv577], .c 3, .c 7, .c 23, .c 3, .c 191, .c 5, .c 3, .c 29, .c 7,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv48757], .c 3, .p pv2 [pv2,pv5,pv117017], .c 113, .c 3,
  .p pv2 [pv2,pv1170173], .c 11, .c 3, .c 59,
]
private theorem h0285c21 : checkBlock 2340099 128 b0285c21 = true := by
  decide +kernel

private def b0285c22 : List Row := [
  .c 5, .c 3, .c 7, .c 37, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv103,pv541], .c 3, .c 11, .c 7, .c 3,
  .c 13, .c 631, .c 3, .p pv5 [pv2,pv11,pv19,pv509], .c 5, .c 3, .c 677, .c 563, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv65011], .c 3, .c 7, .c 13, .c 3, .c 17, .c 709, .c 3, .c 739, .c 5, .c 3,
  .p pv2 [pv2,pv1170209], .p pv11 [pv2,pv3,pv5,pv19,pv2053], .c 3, .c 5, .c 53, .c 3,
  .p pv7 [pv2,pv5,pv234043], .c 89, .c 3, .c 11, .c 19, .c 3, .c 7, .c 5, .c 3, .c 281,
  .p pv2 [pv2,pv3,pv5,pv7,pv743], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv117023], .c 1451,
  .c 3, .c 857, .c 31, .c 3, .c 101, .c 5, .c 3, .p pv7 [pv2,pv7,pv167177], .c 11, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv130027], .c 3, .p pv2 [pv2,pv5,pv43,pv5443],
  .p pv2 [pv2,pv3,pv7,pv11,pv17,pv149], .c 3, .c 461, .c 7, .c 3, .c 11, .c 5, .c 3, .c 17, .c 67,
  .c 3, .c 5, .c 83, .c 3, .p pv17 [pv2,pv5,pv7,pv13,pv643], .c 983, .c 3, .c 7, .c 571, .c 3,
  .c 13, .c 5, .c 3, .c 1511, .c 7, .c 3, .c 5, .c 11, .c 3, .p pv13 [pv2,pv5,pv46811], .c 19,
  .c 3, .c 109, .c 13, .c 3, .p pv2 [pv2,pv7,pv31,pv5393], .c 5, .c 3, .c 7, .c 593, .c 3, .c 5,
  .c 17, .c 3, .p pv2 [pv2,pv5,pv11,pv10639], .c 7, .c 3, .p pv2 [pv2,pv53,pv71,pv311], .c 59,
  .c 3, .c 31, .c 5, .c 3, .c 73, .c 661, .c 3, .c 5, .p pv23 [pv2,pv3,pv390101], .c 3,
]
private theorem h0285c22 : checkBlock 2340355 128 b0285c22 = true := by
  decide +kernel

private def b0285c23 : List Row := [
  .c 7, .c 11, .c 3, .p pv3 [pv2,pv292577], .c 29, .c 3, .c 211, .c 5, .c 3, .c 19, .c 61, .c 3,
  .c 5, .c 13, .c 3, .c 23, .c 1019, .c 3, .c 47, .c 41, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv1170329], .p pv43 [pv2,pv3,pv5,pv7,pv5573], .c 3, .c 5, .c 7, .c 3, .c 821,
  .p pv7 [pv2,pv3,pv73,pv167], .c 3, .c 29, .c 11, .c 3, .c 83, .c 5, .c 3, .c 13, .c 79, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv17,pv5737], .c 3, .c 11, .p pv5 [pv2,pv3,pv7,pv13,pv1429], .c 3, .c 59,
  .c 7, .c 3, .c 17, .c 5, .c 3, .p pv17 [pv2,pv233,pv5023], .p pv7 [pv2,pv3,pv5,pv3251], .c 3,
  .c 5, .p pv3 [pv2,pv3,pv367,pv1063], .c 3, .c 37, .c 23, .c 3, .c 7, .p pv2 [pv2,pv3,pv14449],
  .c 3, .c 19, .c 5, .c 3, .c 1201, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv23,pv257], .c 3,
  .c 431, .p pv2 [pv2,pv3,pv19,pv20533], .c 3, .c 11, .p pv17 [pv2,pv3,pv37,pv659], .c 3,
  .p pv2 [pv2,pv7,pv41,pv2039], .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv55733],
  .c 3, .c 43, .c 7, .c 3, .p pv2 [pv2,pv585199], .c 71, .c 3, .p pv2 [pv2,pv23,pv151,pv337],
  .c 5, .c 3, .c 499, .c 11, .c 3, .c 5, .c 881, .c 3, .c 7, .p pv19 [pv2,pv3,pv11,pv29,pv1223],
  .c 3, .p pv2 [pv2,pv251,pv4663], .c 1171, .c 3, .c 11, .c 5, .c 3, .c 107, .c 31, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv67,pv647], .c 3, .c 29, .c 521, .c 3, .c 19, .p pv11 [pv2,pv3,pv13,pv30011],
  .c 3, .c 7, .c 5,
]
private theorem h0285c23 : checkBlock 2340611 128 b0285c23 = true := by
  decide +kernel

private def b0285c24 : List Row := [
  .c 3, .p pv2 [pv2,pv585217], .c 13, .c 3, .c 5, .c 7, .c 3, .c 103, .c 17, .c 3,
  .p pv5 [pv2,pv1170443], .c 577, .c 3, .p pv2 [pv2,pv599,pv977], .c 5, .c 3, .c 11, .c 97, .c 3,
  .c 5, .c 541, .c 3, .p pv11 [pv2,pv5,pv11,pv13,pv1637], .c 67, .c 3, .c 17, .c 7, .c 3, .c 13,
  .c 5, .c 3, .c 47, .p pv2 [pv2,pv3,pv5,pv78031], .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv41,pv61],
  .c 3, .c 71, .c 11, .c 3, .c 7, .c 13, .c 3, .c 37, .c 5, .c 3, .p pv11 [pv2,pv461,pv2539],
  .c 7, .c 3, .c 5, .c 29, .c 3, .c 19, .p pv5 [pv2,pv3,pv65027], .c 3, .c 41,
  .p pv2 [pv2,pv3,pv101,pv3863], .c 3, .p pv5 [pv2,pv7,pv167213], .c 5, .c 3, .c 7, .c 127, .c 3,
  .c 5, .c 61, .c 3, .c 13, .c 7, .c 3, .c 79, .c 11, .c 3, .c 257, .c 5, .c 3, .c 17, .c 113,
  .c 3, .c 5, .c 13, .c 3, .c 7, .p pv5 [pv2,pv3,pv23,pv4241], .c 3, .c 73, .c 359, .c 3, .c 1013,
  .c 5, .c 3, .c 43, .c 227, .c 3, .c 5, .p pv5 [pv2,pv3,pv89,pv137], .c 3, .c 59, .c 53, .c 3,
  .c 229, .p pv2 [pv2,pv3,pv195089], .c 3, .c 7, .c 5, .c 3, .c 13, .c 971, .c 3, .c 5, .c 7,
  .c 3, .p pv2 [pv2,pv5,pv193,pv1213], .c 367, .c 3, .c 11, .c 1109, .c 3,
  .p pv5 [pv2,pv109,pv10739], .c 5, .c 3, .c 397, .p pv3 [pv2,pv3,pv5,pv73,pv1069], .c 3, .c 5,
  .c 47, .c 3, .c 17,
]
private theorem h0285c24 : checkBlock 2340867 128 b0285c24 = true := by
  decide +kernel

private def b0285c25 : List Row := [
  .c 19, .c 3, .p pv5 [pv2,pv1170563], .c 7, .c 3, .p pv2 [pv2,pv585283], .c 5, .c 3, .c 337,
  .c 11, .c 3, .c 5, .c 23, .c 3, .c 31, .c 1021, .c 3, .c 7, .p pv3 [pv2,pv3,pv390193], .c 3,
  .c 11, .c 5, .c 3, .c 53, .c 7, .c 3, .c 5, .c 139, .c 3, .c 67, .c 13, .c 3, .c 439, .c 17,
  .c 3, .c 23, .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv1951], .c 3, .c 5, .c 11, .c 3, .c 47,
  .c 7, .c 3, .p pv3 [pv2,pv23,pv3181], .p pv2 [pv2,pv3,pv11,pv19,pv1867], .c 3, .c 17, .c 5,
  .c 3, .c 11, .c 433, .c 3, .c 5, .c 19, .c 3, .c 7, .p pv2 [pv2,pv3,pv130069], .c 3, .c 113,
  .c 37, .c 3, .c 1439, .c 5, .c 3, .c 283, .c 13, .c 3, .c 5, .c 107, .c 3,
  .p pv7 [pv2,pv5,pv257,pv911], .c 11, .c 3, .c 223, .c 383, .c 3, .c 7, .c 5, .c 3, .c 97, .c 17,
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv13,pv1801], .p pv3 [pv2,pv3,pv61,pv6397], .c 3, .c 43,
  .p pv2 [pv2,pv3,pv17,pv23,pv499], .c 3, .c 13, .c 5, .c 3, .c 863, .c 373, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv13,pv2309], .c 3, .c 23, .p pv2 [pv2,pv3,pv7,pv19,pv163], .c 3, .c 31, .c 7,
  .c 3, .p pv5 [pv2,pv17,pv68863], .c 5, .c 3, .p pv2 [pv2,pv585337], .c 19, .c 3, .c 5, .c 811,
  .c 3, .c 11, .c 61, .c 3, .c 7, .p pv11 [pv2,pv3,pv31,pv1049], .c 3, .c 29, .c 5, .c 3,
]
private theorem h0285c25 : checkBlock 2341123 128 b0285c25 = true := by
  decide +kernel

private def b0285c26 : List Row := [
  .p pv2 [pv2,pv13,pv90053], .c 7, .c 3, .c 5, .c 41, .c 3, .c 13, .c 17, .c 3, .c 37, .c 31,
  .c 3, .p pv2 [pv2,pv7,pv29,pv73,pv79], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv17,pv4591], .c 3,
  .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv117071], .c 7, .c 3, .c 11, .c 109, .c 3,
  .p pv3 [pv2,pv292679], .c 5, .c 3, .c 401, .c 349, .c 3, .c 5, .p pv3 [pv2,pv3,pv19,pv23,pv47],
  .c 3, .c 7, .p pv5 [pv2,pv3,pv195121], .c 3, .p pv3 [pv2,pv13,pv11257],
  .p pv2 [pv2,pv3,pv7,pv18583], .c 3, .p pv5 [pv2,pv379,pv3089], .c 5, .c 3, .c 13, .c 11, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv193,pv337], .c 3, .c 79, .c 97, .c 3, .c 53, .c 29, .c 3, .c 7, .c 5,
  .c 3, .c 103, .c 89, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv41,pv5711], .c 83, .c 3, .c 563,
  .c 311, .c 3, .c 31, .c 5, .c 3, .c 17, .p pv11 [pv2,pv3,pv5,pv26017], .c 3, .c 5, .c 11, .c 3,
  .c 19, .c 587, .c 3, .c 13, .c 7, .c 3, .c 313, .c 5, .c 3, .c 11, .c 23, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv130087], .c 3, .p pv2 [pv2,pv5,pv7,pv11,pv3041], .c 13, .c 3, .c 7, .c 19,
  .c 3, .c 67, .c 5, .c 3, .p pv2 [pv2,pv107,pv5471], .c 7, .c 3, .c 5, .c 17, .c 3,
  .p pv3 [pv2,pv5,pv2927], .c 11, .c 3, .c 23, .p pv17 [pv2,pv3,pv43,pv2269], .c 3,
  .p pv2 [pv2,pv7,pv13,pv919], .c 5, .c 3, .c 7, .c 73, .c 3, .c 5, .c 1061, .c 3, .c 17, .c 7,
]
private theorem h0285c26 : checkBlock 2341379 128 b0285c26 = true := by
  decide +kernel

private def b0285c27 : List Row := [
  .c 3, .p pv2 [pv2,pv11,pv19,pv2801], .c 79, .c 3, .p pv2 [pv2,pv1170821], .c 5, .c 3, .c 839,
  .c 13, .c 3, .c 5, .c 1483, .c 3, .c 7, .c 29, .c 3, .c 727, .c 11, .c 3, .p pv3 [pv2,pv292709],
  .c 5, .c 3, .c 83, .c 47, .c 3, .c 5, .p pv3 [pv2,pv3,pv390281], .c 3, .c 11, .c 19, .c 3,
  .p pv3 [pv2,pv7,pv5227], .c 17, .c 3, .c 7, .c 5, .c 3, .c 31, .c 271, .c 3, .c 5, .c 7, .c 3,
  .c 29, .c 223, .c 3, .p pv5 [pv2,pv1170863], .c 13, .c 3, .c 17, .c 5, .c 3, .c 197, .c 137,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv11827], .c 3, .p pv11 [pv2,pv5,pv17,pv19,pv29], .c 127, .c 3,
  .c 11, .c 7, .c 3, .p pv2 [pv2,pv83,pv14107], .c 5, .c 3, .c 19, .c 31, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv48787], .c 3, .c 13, .c 719, .c 3, .c 7, .c 1063, .c 3, .c 71, .c 5, .c 3,
  .c 691, .c 7, .c 3, .c 5, .c 13, .c 3, .c 1033, .c 337, .c 3, .p pv3 [pv2,pv292727],
  .p pv2 [pv2,pv3,pv17,pv2551], .c 3, .c 11, .c 5, .c 3, .c 7, .c 479, .c 3, .c 5, .c 23, .c 3,
  .c 37, .c 7, .c 3, .p pv5 [pv2,pv13,pv90071], .c 1279, .c 3, .p pv3 [pv2,pv17,pv34439], .c 5,
  .c 3, .c 13, .p pv53 [pv2,pv3,pv5,pv23,pv1697], .c 3, .c 5, .c 11, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv13,pv139], .c 3, .p pv2 [pv2,pv79,pv7411], .c 41, .c 3, .c 19, .c 5, .c 3,
  .c 11,
]
private theorem h0285c27 : checkBlock 2341635 128 b0285c27 = true := by
  decide +kernel

private def b0285c28 : List Row := [
  .c 739, .c 3, .c 5, .p pv5 [pv2,pv3,pv97579], .c 3, .c 173, .c 17, .c 3,
  .p pv2 [pv2,pv7,pv23,pv1039], .c 43, .c 3, .c 7, .c 5, .c 3, .p pv13 [pv2,pv67,pv17477], .c 19,
  .c 3, .c 5, .c 7, .c 3, .c 947, .c 11, .c 3, .c 13, .p pv2 [pv2,pv3,pv390323], .c 3,
  .p pv5 [pv2,pv1170971], .c 5, .c 3, .c 293, .c 1187, .c 3, .c 5, .c 31, .c 3, .c 41, .c 13,
  .c 3, .p pv11 [pv2,pv11,pv106453], .c 7, .c 3, .c 61, .c 5, .c 3, .p pv2 [pv2,pv19,pv61631],
  .p pv7 [pv2,pv3,pv5,pv4337], .c 3, .c 5, .p pv2 [pv2,pv3,pv73,pv5347], .c 3,
  .p pv7 [pv2,pv5,pv7,pv33457], .p pv5 [pv2,pv3,pv97583], .c 3, .c 7, .c 11, .c 3,
  .p pv5 [pv2,pv13,pv41], .c 5, .c 3, .c 929, .c 7, .c 3, .c 5, .c 53, .c 3, .c 11, .c 421, .c 3,
  .p pv2 [pv2,pv37,pv31649], .p pv11 [pv2,pv3,pv13,pv15013], .c 3, .p pv3 [pv2,pv7,pv11,pv1901],
  .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv55763], .c 3,
  .p pv2 [pv2,pv5,pv31,pv1511], .c 7, .c 3, .c 47, .c 73, .c 3, .c 37, .c 5, .c 3, .c 29,
  .p pv7 [pv2,pv3,pv5,pv53,pv491], .c 3, .c 5, .c 71, .c 3, .c 7, .c 109, .c 3, .c 11, .c 101,
  .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv11,pv29,pv3671], .p pv2 [pv2,pv3,pv5,pv37,pv211], .c 3,
  .c 5, .c 17, .c 3, .c 19, .c 23, .c 3, .c 103, .c 13, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv146383], .c 11, .c 3, .c 5, .c 7, .c 3, .c 17, .c 31, .c 3,
]
private theorem h0285c28 : checkBlock 2341891 128 b0285c28 = true := by
  decide +kernel

private def b0285c29 : List Row := [
  .c 163, .c 19, .c 3, .c 11, .c 5, .c 3, .c 23, .c 151, .c 3, .c 5, .c 43, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv7,pv27883], .c 3, .c 83, .c 7, .c 3, .c 269, .c 5, .c 3,
  .p pv2 [pv2,pv585547], .p pv11 [pv2,pv3,pv5,pv101,pv773], .c 3, .c 5, .c 11, .c 3,
  .p pv19 [pv2,pv5,pv7,pv239], .p pv2 [pv2,pv3,pv390367], .c 3, .c 7, .c 17, .c 3, .c 89, .c 5,
  .c 3, .c 11, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv17,pv22963], .c 3,
  .p pv11 [pv2,pv5,pv11,pv107,pv199], .c 191, .c 3, .p pv2 [pv2,pv13,pv31,pv1453],
  .p pv7 [pv2,pv3,pv390373], .c 3, .c 17, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv6971], .c 3, .c 127, .c 7, .c 3, .c 31, .p pv2 [pv2,pv3,pv65063], .c 3,
  .c 613, .c 5, .c 3, .c 241, .c 1361, .c 3, .c 5, .p pv3 [pv2,pv3,pv130127], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv47,pv4153], .c 3, .c 23, .c 1093, .c 3, .c 1213, .c 5, .c 3,
  .p pv2 [pv2,pv585577], .c 17, .c 3, .c 5, .c 463, .c 3, .c 181, .c 103, .c 3, .c 13, .c 11,
  .c 3, .c 7, .c 5, .c 3, .c 19, .c 461, .c 3, .c 5, .c 7, .c 3, .c 11, .c 13, .c 3,
  .p pv2 [pv2,pv97,pv6037], .c 29, .c 3, .p pv5 [pv2,pv11,pv17,pv6263], .c 5, .c 3, .c 751, .c 41,
  .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv117119], .c 797, .c 3, .c 67, .c 7, .c 3,
  .p pv3 [pv2,pv13,pv101,pv223], .c 5, .c 3, .p pv11 [pv2,pv1171199], .p pv11 [pv2,pv3,pv5,pv61],
]
private theorem h0285c29 : checkBlock 2342147 128 b0285c29 = true := by
  decide +kernel

private def b0285c30 : List Row := [
  .c 3, .c 5, .p pv7 [pv2,pv3,pv11,pv35491], .c 3, .c 131, .c 17, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv13,pv59,pv509], .c 3, .p pv5 [pv2,pv31,pv37781], .c 5, .c 3, .c 79, .c 7,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv195203], .c 3, .c 53, .p pv2 [pv2,pv3,pv390407], .c 3, .c 17,
  .c 643, .c 3, .c 19, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 877, .c 3, .c 503, .c 7, .c 3,
  .c 59, .p pv3 [pv2,pv3,pv390413], .c 3, .c 11, .c 5, .c 3, .c 983, .c 19, .c 3, .c 5, .c 73,
  .c 3, .c 7, .c 71, .c 3, .c 37, .c 13, .c 3, .p pv3 [pv2,pv146407], .c 5, .c 3, .c 109, .c 67,
  .c 3, .c 5, .c 11, .c 3, .c 919, .c 29, .c 3, .p pv3 [pv2,pv7,pv59,pv709],
  .p pv2 [pv2,pv3,pv11,pv11831], .c 3, .c 7, .c 5, .c 3, .c 11, .c 107, .c 3, .c 5, .c 7, .c 3,
  .c 13, .c 137, .c 3, .c 19, .c 89, .c 3, .c 23, .c 5, .c 3, .c 881, .c 37, .c 3, .c 5, .c 13,
  .c 3, .c 29, .c 11, .c 3, .c 43, .c 7, .c 3, .c 113, .c 5, .c 3, .p pv3 [pv2,pv31,pv4723],
  .p pv2 [pv2,pv3,pv5,pv26029], .c 3, .c 5, .c 17, .c 3, .c 47, .p pv5 [pv2,pv3,pv390437], .c 3,
  .c 7, .c 419, .c 3, .p pv3 [pv2,pv103,pv2843], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 97, .c 3,
  .c 17, .c 53, .c 3, .p pv3 [pv2,pv9151],
]
private theorem h0285c30 : checkBlock 2342403 128 b0285c30 = true := by
  decide +kernel

private def b0285c31 : List Row := [
  .c 11, .c 3, .p pv5 [pv2,pv7,pv19,pv8807], .c 5, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv5,pv11,pv31,pv229], .c 3, .c 5, .p pv43 [pv2,pv3,pv7,pv167], .c 3, .c 11,
  .c 7, .c 3, .p pv5 [pv2,pv1171343], .c 599, .c 3, .c 1447, .c 5, .c 3, .c 41, .c 31, .c 3, .c 5,
  .c 29, .c 3, .c 7, .c 59, .c 3, .c 13, .c 17, .c 3, .p pv2 [pv2,pv67,pv17483], .c 5, .c 3,
  .c 37, .p pv2 [pv2,pv3,pv5,pv13,pv6007], .c 3, .c 5, .c 109, .c 3, .p pv2 [pv2,pv5,pv41,pv2857],
  .c 13, .c 3, .c 11, .c 617, .c 3, .c 7, .c 5, .c 3, .c 53, .c 241, .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv17,pv13781], .p pv2 [pv2,pv3,pv59,pv1103], .c 3, .p pv5 [pv2,pv19,pv15413],
  .p pv2 [pv2,pv3,pv390463], .c 3, .p pv5 [pv2,pv13,pv90107], .c 5, .c 3, .c 67, .c 11, .c 3,
  .c 5, .p pv11 [pv2,pv3,pv101,pv1933], .c 3, .c 547, .c 23, .c 3, .p pv5 [pv2,pv191,pv6133],
  .c 7, .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv331,pv3539], .c 13, .c 3, .c 5, .c 61, .c 3, .c 59,
  .c 19, .c 3, .c 7, .p pv3 [pv2,pv3,pv17,pv103,pv223], .c 3, .c 167, .c 5, .c 3, .c 23, .c 7,
  .c 3, .c 5, .c 11, .c 3, .c 353, .c 41, .c 3, .c 227, .p pv2 [pv2,pv3,pv11,pv17749], .c 3,
  .c 13, .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .c 31, .c 3, .c 827, .c 7, .c 3, .c 101, .c 13,
  .c 3, .c 47, .c 5, .c 3, .c 19, .c 157, .c 3,
]
private theorem h0285c31 : checkBlock 2342659 128 b0285c31 = true := by
  decide +kernel

def rows0285 : List Row :=
  b0285c00 ++ b0285c01 ++ b0285c02 ++ b0285c03 ++ b0285c04 ++ b0285c05 ++ b0285c06 ++ b0285c07 ++
  b0285c08 ++ b0285c09 ++ b0285c10 ++ b0285c11 ++ b0285c12 ++ b0285c13 ++ b0285c14 ++ b0285c15 ++
  b0285c16 ++ b0285c17 ++ b0285c18 ++ b0285c19 ++ b0285c20 ++ b0285c21 ++ b0285c22 ++ b0285c23 ++
  b0285c24 ++ b0285c25 ++ b0285c26 ++ b0285c27 ++ b0285c28 ++ b0285c29 ++ b0285c30 ++ b0285c31

theorem checked0285 : checkBlock 2334723 4096 rows0285 = true :=
  checkBlock_append h0285c00 (
    checkBlock_append h0285c01 (
    checkBlock_append h0285c02 (
    checkBlock_append h0285c03 (
    checkBlock_append h0285c04 (
    checkBlock_append h0285c05 (
    checkBlock_append h0285c06 (
    checkBlock_append h0285c07 (
    checkBlock_append h0285c08 (
    checkBlock_append h0285c09 (
    checkBlock_append h0285c10 (
    checkBlock_append h0285c11 (
    checkBlock_append h0285c12 (
    checkBlock_append h0285c13 (
    checkBlock_append h0285c14 (
    checkBlock_append h0285c15 (
    checkBlock_append h0285c16 (
    checkBlock_append h0285c17 (
    checkBlock_append h0285c18 (
    checkBlock_append h0285c19 (
    checkBlock_append h0285c20 (
    checkBlock_append h0285c21 (
    checkBlock_append h0285c22 (
    checkBlock_append h0285c23 (
    checkBlock_append h0285c24 (
    checkBlock_append h0285c25 (
    checkBlock_append h0285c26 (
    checkBlock_append h0285c27 (
    checkBlock_append h0285c28 (
    checkBlock_append h0285c29 (
    checkBlock_append h0285c30 (
    h0285c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
