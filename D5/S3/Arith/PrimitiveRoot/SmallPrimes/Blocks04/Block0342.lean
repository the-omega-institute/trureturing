/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks04/Block0342
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks04/Block0342.checked0342
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table026
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table029
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table040
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table046
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table054
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table065
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table081
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table082
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table107
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table147
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table148

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0342c00 : List Row := [
  .c 3, .c 13, .c 479, .c 3, .c 5, .c 37, .c 3, .p pv3 [pv2,pv5,pv7,pv5003], .c 19, .c 3, .c 7,
  .c 11, .c 3, .p pv2 [pv2,pv700423], .c 5, .c 3, .c 23, .c 7, .c 3, .c 5,
  .p pv17 [pv2,pv3,pv466951], .c 3, .c 11, .p pv5 [pv2,pv3,pv58369], .c 3, .c 47, .c 17, .c 3,
  .c 907, .c 5, .c 3, .c 7, .c 71, .c 3, .c 5, .p pv47 [pv2,pv3,pv7,pv17,pv109], .c 3,
  .p pv2 [pv2,pv5,pv19,pv73,pv101], .c 7, .c 3, .c 13, .c 31, .c 3, .c 17, .c 5, .c 3, .c 19,
  .c 353, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv42451], .c 3, .c 7, .c 13, .c 3, .c 11, .c 191, .c 3,
  .p pv5 [pv2,pv1400891], .c 5, .c 3, .p pv2 [pv2,pv11,pv37,pv1721], .c 23, .c 3, .c 5, .c 19,
  .c 3, .p pv3 [pv2,pv5,pv14009], .p pv2 [pv2,pv3,pv71,pv6577], .c 3, .c 163, .c 89, .c 3, .c 7,
  .c 5, .c 3, .p pv2 [pv2,pv337,pv4157], .c 11, .c 3, .c 5, .c 7, .c 3, .c 83,
  .p pv5 [pv2,pv3,pv11,pv10613], .c 3, .c 23, .c 541, .c 3, .c 11, .c 5, .c 3, .c 1069, .c 13,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv14593], .c 3, .c 227, .p pv3 [pv2,pv3,pv7,pv37,pv601], .c 3,
  .c 457, .c 7, .c 3, .c 19, .c 5, .c 3, .c 1049, .c 1451, .c 3, .c 5, .c 11, .c 3,
  .p pv7 [pv2,pv5,pv7,pv13,pv3079], .c 29, .c 3, .c 7, .c 37, .c 3, .c 13, .c 5, .c 3, .c 11,
  .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv5987], .c 3, .p pv3 [pv2,pv5,pv11,pv199],
]
private theorem h0342c00 : checkBlock 2801667 128 b0342c00 = true := by
  decide +kernel

private def b0342c01 : List Row := [
  .c 17, .c 3, .p pv5 [pv2,pv167,pv8389], .c 13, .c 3, .c 1201, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv17,pv41,pv67], .c 3, .c 5, .c 379, .c 3, .c 29, .c 7, .c 3, .c 17, .c 73,
  .c 3, .c 317, .c 5, .c 3, .c 59, .p pv3 [pv2,pv3,pv5,pv163,pv191], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv313,pv373], .c 3, .c 7, .c 283, .c 3, .c 19, .c 307, .c 3, .c 1009, .c 5,
  .c 3, .c 47, .c 127, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv37,pv7573],
  .p pv2 [pv2,pv3,pv103,pv2267], .c 3, .p pv3 [pv2,pv7,pv1787], .c 11, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv31,pv59,pv383], .c 919, .c 3, .c 5, .c 7, .c 3, .c 11, .c 101, .c 3, .c 37,
  .c 1381, .c 3, .p pv2 [pv2,pv11,pv43,pv1481], .c 5, .c 3, .c 13, .c 113, .c 3, .c 5, .c 23,
  .c 3, .c 257, .c 821, .c 3, .p pv2 [pv2,pv17,pv89,pv463], .c 7, .c 3, .p pv2 [pv2,pv19,pv3881],
  .c 5, .c 3, .p pv3 [pv2,pv227,pv1543], .p pv3 [pv2,pv3,pv5,pv23,pv31,pv131], .c 3, .c 5,
  .p pv19 [pv2,pv3,pv11,pv29,pv61], .c 3, .c 19, .c 677, .c 3, .c 7, .p pv2 [pv2,pv3,pv233509],
  .c 3, .c 23, .c 5, .c 3, .c 199, .c 7, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv79,pv3547],
  .c 163, .c 3, .c 13, .c 19, .c 3, .p pv5 [pv2,pv7,pv200153], .c 5, .c 3, .c 7, .c 11, .c 3,
  .c 5, .c 61, .c 3, .c 17, .c 7, .c 3, .c 193, .p pv7 [pv2,pv3,pv12973], .c 3, .c 11, .c 5, .c 3,
]
private theorem h0342c01 : checkBlock 2801923 128 b0342c01 = true := by
  decide +kernel

private def b0342c02 : List Row := [
  .p pv2 [pv2,pv17,pv73,pv1129], .c 43, .c 3, .c 5, .c 47, .c 3, .c 7, .p pv5 [pv2,pv3,pv58379],
  .c 3, .c 1399, .p pv7 [pv2,pv3,pv7,pv137,pv487], .c 3, .c 1171, .c 5, .c 3, .c 79,
  .p pv2 [pv2,pv3,pv5,pv93407], .c 3, .c 5, .c 11, .c 3, .c 131, .c 107, .c 3, .c 41, .c 17, .c 3,
  .c 7, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 7, .c 3, .c 23, .c 19, .c 3,
  .p pv3 [pv2,pv175141], .c 733, .c 3, .c 17, .c 5, .c 3, .c 37, .c 631, .c 3, .c 5,
  .p pv17 [pv2,pv3,pv31], .c 3, .c 47, .c 11, .c 3, .c 113, .c 7, .c 3, .c 13, .c 5, .c 3, .c 29,
  .p pv11 [pv2,pv3,pv5,pv9341], .c 3, .c 5, .c 31, .c 3, .p pv7 [pv2,pv5,pv7,pv19,pv43],
  .p pv5 [pv2,pv3,pv38921], .c 3, .c 7, .c 13, .c 3, .c 59, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv29191], .c 3, .p pv2 [pv2,pv5,pv61,pv2297], .c 23, .c 3,
  .p pv2 [pv2,pv101,pv13873], .c 11, .c 3, .c 43, .c 5, .c 3, .c 7, .c 1493, .c 3, .c 5, .c 19,
  .c 3, .c 11, .c 7, .c 3, .p pv3 [pv2,pv433,pv809], .c 139, .c 3,
  .p pv5 [pv2,pv11,pv17,pv59,pv127], .c 5, .c 3, .c 23, .c 41, .c 3, .c 5, .c 13, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv155689], .c 3, .p pv5 [pv2,pv1401203], .c 67, .c 3, .c 281, .c 5, .c 3,
  .c 461, .c 311, .c 3, .c 5, .c 97, .c 3, .c 31, .c 17,
]
private theorem h0342c02 : checkBlock 2802179 128 b0342c02 = true := by
  decide +kernel

private def b0342c03 : List Row := [
  .c 3, .c 11, .c 43, .c 3, .c 7, .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv7,pv17,pv157], .c 3,
  .c 5, .c 7, .c 3, .c 881, .c 601, .c 3, .c 17, .c 47, .c 3, .c 29, .c 5, .c 3,
  .p pv7 [pv2,pv7,pv200177], .c 11, .c 3, .c 5, .p pv7 [pv2,pv3,pv467081], .c 3, .c 37, .c 31,
  .c 3, .p pv3 [pv2,pv43789], .c 7, .c 3, .c 11, .c 5, .c 3, .c 127, .p pv3 [pv2,pv3,pv5,pv31139],
  .c 3, .c 5, .c 199, .c 3, .c 89, .c 61, .c 3, .c 7, .c 1033, .c 3, .c 983, .c 5, .c 3, .c 463,
  .c 7, .c 3, .c 5, .c 11, .c 3, .p pv13 [pv2,pv5,pv23,pv2437], .c 13, .c 3, .c 19, .c 59, .c 3,
  .c 47, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv93419], .c 3, .c 5, .c 331, .c 3,
  .p pv2 [pv2,pv5,pv11,pv12739], .c 7, .c 3, .c 53, .c 29, .c 3, .p pv3 [pv2,pv13,pv6737], .c 5,
  .c 3, .p pv7 [pv2,pv701,pv1999], .p pv31 [pv2,pv3,pv5,pv173], .c 3, .c 5, .c 157, .c 3, .c 7,
  .c 11, .c 3, .c 31, .c 23, .c 3, .p pv5 [pv2,pv163,pv8597], .c 5, .c 3, .c 479, .c 13, .c 3,
  .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv53,pv661], .p pv3 [pv2,pv3,pv23,pv883], .c 3, .c 29,
  .c 101, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv449,pv3121], .c 83, .c 3, .c 5, .c 7, .c 3, .c 17,
  .p pv5 [pv2,pv3,pv19463], .c 3, .c 59, .c 11, .c 3, .c 13, .c 5, .c 3, .c 73,
]
private theorem h0342c03 : checkBlock 2802435 128 b0342c03 = true := by
  decide +kernel

private def b0342c04 : List Row := [
  .c 419, .c 3, .c 5, .c 43, .c 3, .c 11, .c 827, .c 3, .p pv2 [pv2,pv61,pv22973], .c 7, .c 3,
  .c 37, .c 5, .c 3, .c 41, .c 599, .c 3, .c 5, .c 659, .c 3, .c 229, .c 103, .c 3, .c 7, .c 17,
  .c 3, .p pv5 [pv2,pv1401371], .c 5, .c 3, .p pv2 [pv2,pv13,pv53899], .c 7, .c 3, .c 5, .c 23,
  .c 3, .c 13, .c 29, .c 3, .c 11, .c 227, .c 3, .c 17, .c 5, .c 3, .c 7, .c 457, .c 3, .c 5,
  .c 13, .c 3, .c 263, .c 7, .c 3, .p pv2 [pv2,pv71,pv139], .c 53, .c 3, .c 23, .c 5, .c 3,
  .c 433, .c 11, .c 3, .c 5, .c 1297, .c 3, .c 7, .c 19, .c 3, .c 83, .c 337, .c 3, .c 11, .c 5,
  .c 3, .c 13, .c 17, .c 3, .c 5, .p pv3 [pv2,pv3,pv467141], .c 3, .c 101,
  .p pv2 [pv2,pv3,pv13,pv53,pv113], .c 3, .p pv3 [pv2,pv7,pv50051], .p pv2 [pv2,pv3,pv17,pv27479],
  .c 3, .c 7, .c 5, .c 3, .c 43, .p pv29 [pv2,pv3,pv5,pv7,pv1483], .c 3, .c 5, .c 7, .c 3,
  .p pv17 [pv2,pv5,pv19,pv461], .c 41, .c 3, .c 223, .c 61, .c 3, .p pv2 [pv2,pv17,pv47,pv877],
  .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv9343], .c 3, .c 5, .p pv5 [pv2,pv3,pv155717], .c 3,
  .p pv11 [pv2,pv5,pv11,pv83,pv307], .c 59, .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv1401461], .c 5,
  .c 3, .p pv3 [pv2,pv167,pv1049], .p pv17 [pv2,pv3,pv5,pv13,pv7187], .c 3, .c 5, .c 19, .c 3,
  .c 23, .c 11, .c 3,
]
private theorem h0342c04 : checkBlock 2802691 128 b0342c04 = true := by
  decide +kernel

private def b0342c05 : List Row := [
  .c 7, .p pv11 [pv2,pv3,pv163,pv1433], .c 3, .c 271, .c 5, .c 3, .p pv11 [pv2,pv31,pv53,pv853],
  .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv29,pv89,pv181], .c 3, .c 1013,
  .p pv2 [pv2,pv3,pv37,pv59,pv107], .c 3, .c 17, .p pv19 [pv2,pv3,pv51907], .c 3,
  .p pv5 [pv2,pv7,pv13,pv15401], .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv233,pv401], .c 3, .c 5,
  .p pv11 [pv2,pv3,pv7,pv227], .c 3, .p pv3 [pv2,pv5,pv2803], .c 7, .c 3, .c 131, .c 11, .c 3,
  .c 19, .c 5, .c 3, .p pv2 [pv2,pv421,pv3329], .c 13, .c 3, .c 5, .c 739, .c 3, .c 7, .c 23,
  .c 3, .p pv2 [pv2,pv700759], .c 571, .c 3, .c 311, .c 5, .c 3, .c 797, .c 19, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv23,pv2539], .c 3, .p pv3 [pv2,pv5,pv13,pv10781], .c 509, .c 3,
  .p pv5 [pv2,pv7,pv347,pv577], .p pv2 [pv2,pv3,pv77863], .c 3, .c 7, .c 5, .c 3, .c 17,
  .p pv31 [pv2,pv3,pv5,pv7,pv47,pv71], .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv59,pv4751],
  .c 641, .c 3, .c 11, .c 13, .c 3, .p pv5 [pv2,pv23,pv60937], .c 5, .c 3,
  .p pv3 [pv2,pv7,pv11,pv19,pv479], .c 29, .c 3, .c 5, .c 53, .c 3, .p pv3 [pv2,pv5,pv37,pv947],
  .p pv2 [pv2,pv3,pv7,pv22247], .c 3, .c 19, .c 7, .c 3, .c 61, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv131,pv823], .c 11, .c 3, .c 5, .c 17, .c 3, .c 13, .c 109, .c 3, .c 7, .c 83,
  .c 3, .c 11, .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .c 13, .c 3, .c 17, .p pv3 [pv2,pv3,pv467197],
  .c 3, .p pv2 [pv2,pv107,pv13099], .c 229, .c 3, .p pv3 [pv2,pv7,pv7151], .c 5, .c 3, .c 7,
  .p pv17 [pv2,pv3,pv5,pv73],
]
private theorem h0342c05 : checkBlock 2802947 128 b0342c05 = true := by
  decide +kernel

private def b0342c06 : List Row := [
  .c 3, .c 5, .c 11, .c 3, .c 41, .c 7, .c 3, .c 23, .c 503, .c 3, .c 53, .c 5, .c 3, .c 11,
  .c 37, .c 3, .c 5, .c 31, .c 3, .c 7, .c 1213, .c 3, .c 857, .c 17, .c 3,
  .p pv2 [pv2,pv41,pv17093], .c 5, .c 3, .p pv2 [pv2,pv1401629], .c 1531, .c 3, .c 5, .c 59, .c 3,
  .c 127, .c 11, .c 3, .c 971, .c 19, .c 3, .c 7, .c 5, .c 3, .c 1031,
  .p pv43 [pv2,pv3,pv5,pv7,pv1907], .c 3, .c 5, .c 7, .c 3, .c 661, .p pv3 [pv2,pv3,pv51913],
  .c 3, .c 13, .c 23, .c 3, .c 199, .c 5, .c 3, .c 179, .c 1627, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv59,pv7919], .c 3, .p pv2 [pv2,pv5,pv31,pv9043], .c 13, .c 3,
  .p pv3 [pv2,pv19,pv18443], .c 7, .c 3, .c 29, .c 5, .c 3, .c 1229, .c 17, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv101,pv257], .c 3, .c 11, .c 1567, .c 3, .c 7, .p pv19 [pv2,pv3,pv17,pv6871],
  .c 3, .c 1087, .c 5, .c 3, .c 37, .c 7, .c 3, .c 5, .c 691, .c 3, .c 401, .c 19, .c 3, .c 97,
  .p pv3 [pv2,pv3,pv13,pv127,pv283], .c 3, .p pv2 [pv2,pv7,pv17,pv11779], .c 5, .c 3, .c 7, .c 13,
  .c 3, .c 5, .c 113, .c 3, .p pv2 [pv2,pv5,pv140171], .c 7, .c 3, .c 11, .c 167, .c 3,
  .p pv3 [pv2,pv350429], .c 5, .c 3, .c 421, .p pv17 [pv2,pv3,pv5,pv11681], .c 3, .c 5, .c 23,
  .c 3, .c 7, .c 17, .c 3, .c 41,
]
private theorem h0342c06 : checkBlock 2803203 128 b0342c06 = true := by
  decide +kernel

private def b0342c07 : List Row := [
  .c 29, .c 3, .c 13, .c 5, .c 3, .c 19, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv17971], .c 3,
  .c 67, .c 751, .c 3, .c 17, .c 13, .c 3, .c 7, .c 5, .c 3, .c 61, .c 521, .c 3, .c 5, .c 7,
  .c 3, .p pv17 [pv2,pv5,pv280351], .c 367, .c 3, .c 29, .p pv29 [pv2,pv3,pv193,pv269], .c 3,
  .c 389, .c 5, .c 3, .c 419, .c 131, .c 3, .c 5, .c 11, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv7,pv66751], .c 3, .c 31, .c 7, .c 3, .c 241, .c 5, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv5,pv61,pv383], .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv7,pv11,pv331],
  .p pv2 [pv2,pv3,pv17,pv509], .c 3, .c 7, .p pv2 [pv2,pv3,pv31,pv15073], .c 3, .c 19, .c 5, .c 3,
  .c 17, .c 7, .c 3, .c 5, .c 47, .c 3, .c 37, .c 11, .c 3, .p pv5 [pv2,pv13,pv17,pv6343], .c 31,
  .c 3, .c 257, .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 811, .c 3, .c 23, .c 7, .c 3,
  .p pv2 [pv2,pv11,pv63719], .p pv11 [pv2,pv3,pv37,pv73,pv173], .c 3, .c 43, .c 5, .c 3,
  .p pv3 [pv2,pv71,pv617], .p pv2 [pv2,pv3,pv5,pv18691], .c 3, .c 5, .c 17, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv29,pv41,pv131], .c 3, .p pv2 [pv2,pv1021,pv1373], .c 11, .c 3,
  .p pv3 [pv2,pv350459], .c 5, .c 3, .p pv7 [pv2,pv19,pv89,pv829], .c 283, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv43,pv10867], .c 3, .c 11, .p pv19 [pv2,pv3,pv233641], .c 3, .c 13,
  .p pv3 [pv2,pv3,pv109,pv1429], .c 3, .c 7, .c 5, .c 3, .c 239, .c 73, .c 3,
]
private theorem h0342c07 : checkBlock 2803459 128 b0342c07 = true := by
  decide +kernel

private def b0342c08 : List Row := [
  .c 5, .c 7, .c 3, .c 107, .c 13, .c 3, .p pv5 [pv2,pv953,pv1471], .c 43, .c 3, .c 31, .c 5,
  .c 3, .c 59, .p pv13 [pv2,pv3,pv5,pv83,pv563], .c 3, .c 5, .c 443, .c 3,
  .p pv11 [pv2,pv5,pv2243], .c 53, .c 3, .c 11, .c 7, .c 3, .c 103, .c 5, .c 3, .c 23,
  .p pv17 [pv2,pv3,pv5,pv31153], .c 3, .c 5, .p pv13 [pv2,pv3,pv17,pv859], .c 3,
  .p pv2 [pv2,pv5,pv7,pv2861], .p pv3 [pv2,pv3,pv467297], .c 3, .c 7, .c 79, .c 3, .c 17, .c 5,
  .c 3, .p pv11 [pv2,pv59,pv23761], .c 7, .c 3, .c 5, .c 29, .c 3, .c 19,
  .p pv5 [pv2,pv3,pv11,pv1931], .c 3, .p pv3 [pv2,pv67,pv5231], .p pv2 [pv2,pv3,pv281,pv1663],
  .c 3, .c 11, .c 5, .c 3, .c 7, .c 307, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv29,pv1151], .c 3,
  .c 373, .c 7, .c 3, .p pv5 [pv2,pv797,pv1759], .c 19, .c 3, .c 13, .c 5, .c 3, .c 53, .c 17,
  .c 3, .c 5, .c 11, .c 3, .c 7, .p pv5 [pv2,pv3,pv29207], .c 3, .p pv2 [pv2,pv229,pv3061], .c 13,
  .c 3, .c 67, .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv93463], .c 3, .c 5, .c 37, .c 3, .c 43,
  .p pv3 [pv2,pv3,pv467317], .c 3, .c 23, .p pv2 [pv2,pv3,pv41,pv139], .c 3, .c 7, .c 5, .c 3,
  .c 31, .c 251, .c 3, .c 5, .c 7, .c 3, .c 13, .c 11, .c 3, .p pv3 [pv2,pv87623],
  .p pv3 [pv2,pv3,pv557,pv839], .c 3, .c 383, .c 5, .c 3, .c 41, .c 1327, .c 3, .c 5, .c 13, .c 3,
  .c 823, .c 17, .c 3, .p pv5 [pv2,pv11,pv127453], .c 7,
]
private theorem h0342c08 : checkBlock 2803715 128 b0342c08 = true := by
  decide +kernel

private def b0342c09 : List Row := [
  .c 3, .c 47, .c 5, .c 3, .c 97, .c 29, .c 3, .c 5, .c 43, .c 3, .p pv7 [pv2,pv5,pv7,pv41,pv977],
  .c 1163, .c 3, .c 7, .c 11, .c 3, .c 71, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 67, .c 3,
  .c 11, .p pv3 [pv2,pv3,pv13,pv23,pv521], .c 3, .p pv2 [pv2,pv79,pv17747],
  .p pv11 [pv2,pv3,pv233669], .c 3, .c 127, .c 5, .c 3, .c 7, .p pv13 [pv2,pv3,pv5,pv7789], .c 3,
  .c 5, .c 139, .c 3, .p pv2 [pv2,pv5,pv56081], .c 7, .c 3, .p pv3 [pv2,pv269,pv1303],
  .p pv2 [pv2,pv3,pv19,pv911], .c 3, .c 101, .c 5, .c 3, .p pv2 [pv2,pv23,pv29,pv1051], .c 53,
  .c 3, .c 5, .c 19, .c 3, .c 7, .p pv2 [pv2,pv3,pv17,pv37,pv743], .c 3, .c 11, .c 163, .c 3,
  .c 59, .c 5, .c 3, .c 17, .c 491, .c 3, .c 5, .c 347, .c 3, .p pv7 [pv2,pv5,pv280411], .c 13,
  .c 3, .p pv2 [pv2,pv7,pv17,pv43,pv137], .c 37, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv87629],
  .c 11, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv140207], .p pv19 [pv2,pv3,pv11,pv42487], .c 3,
  .p pv2 [pv2,pv487,pv2879], .c 73, .c 3, .c 11, .c 5, .c 3, .c 43, .c 47, .c 3, .c 5, .c 17,
  .c 3, .p pv2 [pv2,pv5,pv61,pv4597], .c 97, .c 3, .c 53, .c 7, .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv701047], .c 13, .c 3, .c 5, .c 11, .c 3, .c 17, .p pv2 [pv2,pv3,pv43,pv3623],
  .c 3, .c 7, .p pv31 [pv2,pv3,pv11,pv47,pv113], .c 3, .c 29, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5,
]
private theorem h0342c09 : checkBlock 2803971 128 b0342c09 = true := by
  decide +kernel

private def b0342c10 : List Row := [
  .p pv2 [pv2,pv3,pv467371], .c 3, .c 61, .c 181, .c 3, .p pv2 [pv2,pv41,pv17099],
  .p pv7 [pv2,pv3,pv83,pv1877], .c 3, .c 13, .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv3739], .c 3,
  .c 5, .p pv17 [pv2,pv3,pv7,pv13,pv107], .c 3, .c 1039, .c 7, .c 3, .c 19, .c 13, .c 3,
  .p pv3 [pv2,pv175267], .c 5, .c 3, .c 1237, .c 421, .c 3, .c 5, .c 71, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv61,pv1277], .c 3, .c 593, .p pv2 [pv2,pv3,pv7,pv23,pv2903], .c 3, .c 17, .c 5,
  .c 3, .p pv2 [pv2,pv13,pv199,pv271], .p pv19 [pv2,pv3,pv5,pv31159], .c 3, .c 5, .c 131, .c 3,
  .c 13, .p pv7 [pv2,pv3,pv31,pv15077], .c 3, .p pv5 [pv2,pv7,pv383,pv523], .c 11, .c 3, .c 7,
  .c 5, .c 3, .c 1223, .c 37, .c 3, .c 5, .c 7, .c 3, .c 11, .c 31, .c 3, .c 827, .c 41, .c 3,
  .c 107, .c 5, .c 3, .c 263, .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv116849], .c 3, .c 19,
  .p pv23 [pv2,pv3,pv7,pv2473], .c 3, .c 29, .c 7, .c 3, .c 179, .c 5, .c 3, .c 13, .c 211, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv11,pv42491], .c 3, .p pv2 [pv2,pv5,pv7,pv40063], .c 23, .c 3, .c 7,
  .c 19, .c 3, .c 251, .c 5, .c 3, .c 71, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv23,pv1129], .c 3,
  .c 41, .c 47, .c 3, .c 59, .p pv11 [pv2,pv3,pv131,pv223], .c 3, .c 191, .c 5, .c 3, .c 7, .c 11,
  .c 3, .c 5, .c 101, .c 3, .p pv23 [pv2,pv5,pv107,pv2621], .c 7, .c 3, .c 13, .c 89, .c 3,
]
private theorem h0342c10 : checkBlock 2804227 128 b0342c10 = true := by
  decide +kernel

private def b0342c11 : List Row := [
  .c 11, .c 5, .c 3, .c 37, .c 157, .c 3, .c 5, .p pv5 [pv2,pv3,pv58427], .c 3, .c 7, .c 13, .c 3,
  .c 17, .p pv13 [pv2,pv3,pv7,pv31,pv359], .c 3, .c 409, .c 5, .c 3, .p pv7 [pv2,pv599,pv2341],
  .p pv7 [pv2,pv3,pv5,pv23371], .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv283,pv991], .c 19,
  .c 3, .c 47, .c 31, .c 3, .c 7, .c 5, .c 3, .c 11, .c 23, .c 3, .c 5, .c 7, .c 3, .c 29, .c 37,
  .c 3, .p pv5 [pv2,pv1402283], .p pv7 [pv2,pv3,pv13,pv89,pv101], .c 3, .p pv2 [pv2,pv179,pv3917],
  .c 5, .c 3, .c 79, .c 13, .c 3, .c 5, .c 73, .c 3, .p pv11 [pv2,pv5,pv19,pv29,pv509], .c 11,
  .c 3, .c 23, .c 7, .c 3, .c 139, .c 5, .c 3, .c 17, .c 1439, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv38953], .c 3, .c 233, .c 661, .c 3, .c 7, .c 1499, .c 3, .c 13, .c 5, .c 3,
  .p pv13 [pv2,pv1093,pv1283], .c 7, .c 3, .c 5, .c 19, .c 3, .c 929, .c 83, .c 3, .c 89, .c 11,
  .c 3, .c 31, .c 5, .c 3, .c 7, .c 223, .c 3, .c 5, .c 17, .c 3, .c 11, .c 7, .c 3, .c 41, .c 23,
  .c 3, .p pv3 [pv2,pv11,pv63743], .c 5, .c 3, .p pv2 [pv2,pv13,pv107873], .c 701, .c 3, .c 5,
  .c 53, .c 3, .c 7, .c 71, .c 3, .p pv2 [pv2,pv701179], .c 61, .c 3, .c 19, .c 5, .c 3,
  .p pv3 [pv2,pv17,pv41,pv503], .p pv3 [pv2,pv3,pv5,pv93491], .c 3, .c 5, .c 13,
]
private theorem h0342c11 : checkBlock 2804483 128 b0342c11 = true := by
  decide +kernel

private def b0342c12 : List Row := [
  .c 3, .c 163, .c 1193, .c 3, .c 11, .p pv29 [pv2,pv3,pv37,pv6317], .c 3, .c 7, .c 5, .c 3,
  .p pv11 [pv2,pv11,pv23,pv241], .c 19, .c 3, .c 5, .c 7, .c 3, .c 439, .c 113, .c 3, .c 839,
  .c 17, .c 3, .c 1451, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 577, .c 3, .c 59, .c 809, .c 3,
  .p pv5 [pv2,pv73,pv19211], .c 7, .c 3, .c 11, .c 5, .c 3, .c 47, .c 67, .c 3, .c 5, .c 23, .c 3,
  .p pv7 [pv2,pv5,pv7,pv17,pv2357], .p pv5 [pv2,pv3,pv9739], .c 3, .c 7,
  .p pv3 [pv2,pv3,pv467473], .c 3, .p pv2 [pv2,pv1402421], .c 5, .c 3, .c 31, .c 7, .c 3, .c 5,
  .c 11, .c 3, .p pv3 [pv2,pv5,pv59,pv2377], .c 269, .c 3, .c 13, .c 193, .c 3, .c 23, .c 5, .c 3,
  .c 7, .c 17, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv113,pv197], .c 3,
  .p pv2 [pv2,pv5,pv11,pv43,pv593], .c 7, .c 3, .c 109, .p pv2 [pv2,pv3,pv17,pv107,pv257], .c 3,
  .c 449, .c 5, .c 3, .c 29, .c 31, .c 3, .c 5, .p pv2 [pv2,pv3,pv233743], .c 3, .c 7, .c 11,
  .c 3, .p pv5 [pv2,pv71,pv19753], .c 1103, .c 3, .c 37, .c 5, .c 3,
  .p pv2 [pv2,pv29,pv137,pv353], .p pv2 [pv2,pv3,pv5,pv15583], .c 3, .c 5, .c 607, .c 3, .c 19,
  .p pv11 [pv2,pv3,pv73,pv1601], .c 3, .c 181, .p pv29 [pv2,pv3,pv13,pv11987], .c 3, .c 7, .c 5,
  .c 3, .c 911, .c 13, .c 3, .c 5, .c 7, .c 3, .c 367, .c 17, .c 3, .c 1151, .c 11, .c 3,
  .p pv3 [pv2,pv10957],
]
private theorem h0342c12 : checkBlock 2804739 128 b0342c12 = true := by
  decide +kernel

private def b0342c13 : List Row := [
  .c 5, .c 3, .c 103, .p pv7 [pv2,pv3,pv5,pv11,pv17], .c 3, .c 5, .c 37, .c 3, .c 11, .c 89, .c 3,
  .c 17, .c 7, .c 3, .c 13, .c 5, .c 3, .c 1097, .p pv17 [pv2,pv3,pv5,pv3463], .c 3, .c 5, .c 59,
  .c 3, .p pv11 [pv2,pv5,pv7,pv5009], .p pv5 [pv2,pv3,pv467507], .c 3, .c 7, .c 13, .c 3, .c 79,
  .c 5, .c 3, .c 307, .c 7, .c 3, .c 5, .c 163, .c 3, .p pv11 [pv2,pv5,pv280507], .c 101, .c 3,
  .c 11, .c 389, .c 3, .c 29, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv93503], .c 3, .c 5, .c 31,
  .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv313,pv4481], .c 179, .c 3, .p pv3 [pv2,pv29,pv107,pv113],
  .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .c 13, .c 3, .c 7, .c 317, .c 3,
  .p pv5 [pv2,pv17,pv10313], .c 71, .c 3, .c 11, .c 5, .c 3, .c 23, .c 83, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv67,pv1163], .c 3, .p pv3 [pv2,pv5,pv19,pv3691], .p pv3 [pv2,pv3,pv467527],
  .c 3, .p pv5 [pv2,pv7,pv13,pv15413], .p pv7 [pv2,pv3,pv58441], .c 3, .c 7, .c 5, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv5,pv7,pv6679], .c 3, .c 5, .c 7, .c 3, .c 43, .p pv7 [pv2,pv3,pv13,pv37],
  .c 3, .c 1471, .c 29, .c 3, .p pv2 [pv2,pv397,pv3533], .c 5, .c 3, .c 11, .c 79, .c 3, .c 5,
  .c 19, .c 3, .c 17, .c 67, .c 3, .p pv2 [pv2,pv359,pv3907], .c 7, .c 3, .p pv3 [pv2,pv175327],
  .c 5, .c 3, .c 1549, .c 23, .c 3, .c 5, .p pv3 [pv2,pv3,pv51949], .c 3,
]
private theorem h0342c13 : checkBlock 2804995 128 b0342c13 = true := by
  decide +kernel

private def b0342c14 : List Row := [
  .p pv2 [pv2,pv5,pv7,pv229], .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv467543], .c 3,
  .p pv5 [pv2,pv349,pv4019], .c 5, .c 3, .c 467, .c 7, .c 3, .c 5, .c 43, .c 3, .c 71, .c 13,
  .c 3, .c 23, .c 17, .c 3, .c 19, .c 5, .c 3, .c 7, .c 1657, .c 3, .c 5, .c 1019, .c 3,
  .p pv13 [pv2,pv5,pv23,pv12197], .c 7, .c 3, .c 73, .c 11, .c 3, .c 17, .c 5, .c 3, .c 61, .c 19,
  .c 3, .c 5, .c 97, .c 3, .c 7, .c 41, .c 3, .c 1493, .c 137, .c 3, .p pv3 [pv2,pv11,pv71,pv449],
  .c 5, .c 3, .c 1303, .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv307,pv1523], .c 3,
  .p pv2 [pv2,pv5,pv280537], .c 29, .c 3, .c 37, .c 23, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv19,pv36913], .c 17, .c 3, .c 5, .c 7, .c 3, .c 269,
  .p pv2 [pv2,pv3,pv23,pv29,pv701], .c 3, .c 11, .c 643, .c 3, .c 13, .c 5, .c 3, .c 313, .c 263,
  .c 3, .c 5, .c 251, .c 3, .c 29, .c 107, .c 3, .c 139, .c 7, .c 3,
  .p pv2 [pv2,pv17,pv109,pv757], .c 5, .c 3, .c 43, .c 11, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv211,pv277], .c 3, .p pv11 [pv2,pv5,pv7,pv29,pv691], .c 73, .c 3, .c 7, .c 31,
  .c 3, .c 11, .c 5, .c 3, .c 229, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv137,pv3413], .c 3, .c 13,
  .c 17, .c 3, .p pv3 [pv2,pv131,pv2677], .c 617, .c 3, .c 479, .c 5,
]
private theorem h0342c14 : checkBlock 2805251 128 b0342c14 = true := by
  decide +kernel

private def b0342c15 : List Row := [
  .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv17,pv5501], .c 3, .c 5, .c 11, .c 3, .c 19, .c 7, .c 3, .c 17,
  .p pv19 [pv2,pv3,pv11,pv10627], .c 3, .p pv2 [pv2,pv701383], .c 5, .c 3, .c 11, .c 173, .c 3,
  .c 5, .c 29, .c 3, .c 7, .c 233, .c 3, .c 127, .c 19, .c 3, .c 23, .c 5, .c 3, .c 13, .c 47,
  .c 3, .c 5, .p pv7 [pv2,pv3,pv29,pv139], .c 3, .c 887, .c 11, .c 3,
  .p pv2 [pv2,pv7,pv23,pv8713], .c 41, .c 3, .c 7, .c 5, .c 3, .c 37,
  .p pv13 [pv2,pv3,pv5,pv7,pv167], .c 3, .c 5, .c 7, .c 3, .c 349, .c 863, .c 3, .c 103,
  .p pv3 [pv2,pv3,pv47,pv9949], .c 3, .c 137, .c 5, .c 3, .c 17, .p pv3 [pv2,pv3,pv5,pv41,pv2281],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv37,pv71,pv89], .c 3, .c 193, .p pv3 [pv2,pv3,pv7,pv3181], .c 3,
  .c 13, .c 7, .c 3, .p pv2 [pv2,pv701413], .c 5, .c 3, .p pv2 [pv2,pv1402829], .c 53, .c 3, .c 5,
  .c 211, .c 3, .c 11, .c 13, .c 3, .c 7, .c 101, .c 3, .p pv2 [pv2,pv11,pv73,pv1747], .c 5, .c 3,
  .p pv3 [pv2,pv350711], .c 7, .c 3, .c 5, .c 17, .c 3, .c 23, .p pv3 [pv2,pv3,pv467617], .c 3,
  .c 43, .p pv17 [pv2,pv3,pv229,pv1021], .c 3, .p pv3 [pv2,pv7,pv13,pv41,pv47], .c 5, .c 3, .c 7,
  .c 29, .c 3, .c 5, .c 1619, .c 3, .c 17, .c 7, .c 3, .c 11, .c 569, .c 3, .c 1453, .c 5, .c 3,
  .c 19, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv61,pv3833], .c 3, .c 7,
]
private theorem h0342c15 : checkBlock 2805507 128 b0342c15 = true := by
  decide +kernel

private def b0342c16 : List Row := [
  .p pv2 [pv2,pv3,pv467627], .c 3, .c 53, .c 109, .c 3, .p pv2 [pv2,pv701443], .c 5, .c 3, .c 29,
  .c 11, .c 3, .c 5, .c 19, .c 3, .p pv19 [pv2,pv5,pv13,pv113,pv191], .c 23, .c 3, .c 401, .c 17,
  .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv29,pv6047], .c 127, .c 3, .c 5, .c 7, .c 3, .c 37, .c 103,
  .c 3, .p pv2 [pv2,pv67,pv20939], .c 13, .c 3, .c 17, .c 5, .c 3, .c 23, .c 31, .c 3, .c 5,
  .c 11, .c 3, .p pv11 [pv2,pv5,pv17,pv3301], .c 47, .c 3, .c 389, .c 7, .c 3, .c 19, .c 5, .c 3,
  .c 11, .c 197, .c 3, .c 5, .c 499, .c 3, .c 13, .c 1579, .c 3, .c 7, .c 131, .c 3, .c 67, .c 5,
  .c 3, .p pv2 [pv2,pv83,pv16903], .c 7, .c 3, .c 5, .c 13, .c 3, .p pv11 [pv2,pv5,pv280591],
  .c 11, .c 3, .c 41, .c 97, .c 3, .p pv2 [pv2,pv7,pv43,pv59,pv79], .c 5, .c 3, .c 7, .c 23, .c 3,
  .c 5, .c 229, .c 3, .c 653, .c 7, .c 3, .c 47, .p pv2 [pv2,pv3,pv25981], .c 3, .c 29, .c 5,
  .c 3, .c 13, .c 947, .c 3, .c 5, .p pv3 [pv2,pv3,pv155887], .c 3, .c 7,
  .p pv19 [pv2,pv3,pv13,pv17987], .c 3, .c 19, .c 11, .c 3, .c 739, .c 5, .c 3,
  .p pv2 [pv2,pv701497], .c 71, .c 3, .c 5, .c 353, .c 3, .c 11, .c 17, .c 3,
  .p pv7 [pv2,pv7,pv37,pv5417], .c 223, .c 3, .c 7, .c 5, .c 3,
]
private theorem h0342c16 : checkBlock 2805763 128 b0342c16 = true := by
  decide +kernel

private def b0342c17 : List Row := [
  .c 233, .p pv23 [pv2,pv3,pv5,pv7,pv17,pv131], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv280603],
  .c 151, .c 3, .c 13, .c 647, .c 3, .c 37, .c 5, .c 3, .p pv3 [pv2,pv7,pv12527], .c 43, .c 3,
  .c 5, .c 631, .c 3, .c 61, .c 13, .c 3, .c 11, .c 7, .c 3, .p pv5 [pv2,pv19,pv18461], .c 5,
  .c 3, .c 373, .c 41, .c 3, .c 5, .p pv3 [pv2,pv3,pv467681], .c 3, .c 19,
  .p pv2 [pv2,pv3,pv23,pv3389], .c 3, .c 7, .c 59, .c 3, .c 701, .c 5, .c 3,
  .p pv2 [pv2,pv701527], .c 7, .c 3, .c 5, .c 37, .c 3, .p pv7 [pv2,pv5,pv31,pv73],
  .p pv5 [pv2,pv3,pv11,pv17,pv41,pv61], .c 3, .c 29, .c 19, .c 3, .c 11, .c 5, .c 3, .c 7, .c 13,
  .c 3, .c 5, .c 83, .c 3, .c 31, .c 7, .c 3, .p pv2 [pv2,pv17,pv29,pv1423], .c 79, .c 3, .c 41,
  .c 5, .c 3, .p pv3 [pv2,pv350771], .c 137, .c 3, .c 5, .c 11, .c 3, .c 7, .c 61, .c 3,
  .p pv2 [pv2,pv19,pv73847], .c 347, .c 3, .c 13, .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv1559],
  .c 3, .c 5, .c 17, .c 3, .p pv7 [pv2,pv5,pv11,pv97,pv263], .c 31, .c 3, .c 59, .c 13, .c 3,
  .c 7, .c 5, .c 3, .c 47, .p pv7 [pv2,pv3,pv5,pv7,pv23,pv83], .c 3, .c 5, .c 7, .c 3, .c 17,
  .c 11, .c 3, .p pv5 [pv2,pv389,pv3607], .p pv7 [pv2,pv3,pv116927], .c 3, .c 23, .c 5, .c 3,
  .c 89, .p pv2 [pv2,pv3,pv5,pv46771], .c 3, .c 5, .p pv2 [pv2,pv3,pv43,pv73,pv149], .c 3, .c 13,
  .c 433,
]
private theorem h0342c17 : checkBlock 2806019 128 b0342c17 = true := by
  decide +kernel

private def b0342c18 : List Row := [
  .c 3, .p pv2 [pv2,pv11,pv23,pv47,pv59], .c 7, .c 3, .p pv2 [pv2,pv131,pv10711], .c 5, .c 3,
  .c 107, .p pv13 [pv2,pv3,pv5,pv31181], .c 3, .c 5, .c 13, .c 3, .c 29, .c 359, .c 3, .c 7,
  .c 11, .c 3, .c 83, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 41, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv233861], .c 3, .c 31, .c 37, .c 3, .c 17, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv53,pv353], .c 3, .c 5, .c 19, .c 3, .p pv3 [pv2,pv5,pv17,pv4127], .c 7,
  .c 3, .p pv5 [pv2,pv61,pv23003], .p pv7 [pv2,pv3,pv23,pv31,pv41], .c 3, .p pv2 [pv2,pv701593],
  .c 5, .c 3, .p pv2 [pv2,pv1403189], .p pv13 [pv2,pv3,pv5,pv5197], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv101,pv421], .c 3, .c 7, .c 397, .c 3, .c 11, .c 31, .c 3, .c 53, .c 5,
  .c 3, .c 41, .c 17, .c 3, .c 5, .c 29, .c 3, .c 809, .c 109, .c 3, .c 13, .c 67, .c 3, .c 7,
  .c 5, .c 3, .p pv11 [pv2,pv43,pv32633], .c 11, .c 3, .c 5, .c 7, .c 3, .c 1367, .c 13, .c 3,
  .p pv3 [pv2,pv53,pv6619], .p pv3 [pv2,pv3,pv467743], .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv113,pv887], .c 19, .c 3, .c 5, .c 269, .c 3, .c 43, .c 23, .c 3, .c 37, .c 7,
  .c 3, .p pv2 [pv2,pv13,pv31,pv1741], .c 5, .c 3, .p pv2 [pv2,pv1403249], .c 97, .c 3, .c 5,
  .c 11, .c 3, .c 47, .c 17, .c 3, .c 7, .p pv17 [pv2,pv3,pv11,pv13,pv3271], .c 3, .c 31, .c 5,
  .c 3, .c 11,
]
private theorem h0342c18 : checkBlock 2806275 128 b0342c18 = true := by
  decide +kernel

private def b0342c19 : List Row := [
  .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv337,pv347], .c 3, .c 179, .p pv5 [pv2,pv3,pv51973], .c 3,
  .c 17, .c 61, .c 3, .c 1601, .c 5, .c 3, .c 7, .c 37, .c 3, .c 5, .c 43, .c 3, .c 59, .c 7,
  .c 3, .c 239, .c 173, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv101,pv6947], .c 29, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv13,pv1999], .c 3, .c 7, .p pv2 [pv2,pv3,pv167,pv2801], .c 3,
  .p pv5 [pv2,pv11,pv193,pv661], .c 13, .c 3, .p pv2 [pv2,pv701653], .c 5, .c 3,
  .p pv2 [pv2,pv1403309], .c 23, .c 3, .c 5, .c 521, .c 3, .c 73, .c 79, .c 3, .c 151, .c 11,
  .c 3, .c 7, .c 5, .c 3, .c 17, .p pv3 [pv2,pv3,pv5,pv7,pv11], .c 3, .c 5, .c 7, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv359,pv1303], .c 3, .c 23, .c 593, .c 3, .p pv3 [pv2,pv11,pv37,pv431], .c 5,
  .c 3, .p pv7 [pv2,pv7,pv29,pv31,pv223], .c 659, .c 3, .c 5, .c 13, .c 3,
  .p pv2 [pv2,pv5,pv23,pv12203], .p pv11 [pv2,pv3,pv7,pv33413], .c 3, .c 67, .c 7, .c 3, .c 353,
  .c 5, .c 3, .c 31, .p pv3 [pv2,pv3,pv5,pv93557], .c 3, .c 5, .c 17, .c 3, .c 53, .c 557, .c 3,
  .c 7, .c 1021, .c 3, .c 617, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 271, .c 3, .c 17, .c 1237,
  .c 3, .p pv2 [pv2,pv19,pv36931], .c 23, .c 3, .c 773, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5,
  .c 73, .c 3, .p pv2 [pv2,pv5,pv140339], .c 7, .c 3,
]
private theorem h0342c19 : checkBlock 2806531 128 b0342c19 = true := by
  decide +kernel

private def b0342c20 : List Row := [
  .p pv2 [pv2,pv1403393], .p pv7 [pv2,pv3,pv151,pv1549], .c 3, .c 11, .c 5, .c 3, .c 193,
  .p pv31 [pv2,pv3,pv5,pv2339], .c 3, .c 5, .c 59, .c 3, .c 7, .c 19, .c 3, .c 13, .c 17, .c 3,
  .c 29, .c 5, .c 3, .p pv2 [pv2,pv23,pv30509], .c 67, .c 3, .c 5, .c 11, .c 3, .c 277, .c 13,
  .c 3, .p pv5 [pv2,pv7,pv157,pv1277], .p pv13 [pv2,pv3,pv11,pv443], .c 3, .c 7, .c 5, .c 3,
  .c 11, .p pv2 [pv2,pv3,pv5,pv7,pv41,pv163], .c 3, .c 5, .c 7, .c 3, .c 811, .c 337, .c 3,
  .c 569, .c 1109, .c 3, .c 347, .c 5, .c 3, .c 19, .c 101, .c 3, .c 5, .c 23, .c 3, .c 41, .c 11,
  .c 3, .p pv2 [pv2,pv1403453], .c 7, .c 3, .p pv3 [pv2,pv21929], .c 5, .c 3,
  .p pv11 [pv2,pv1403459], .c 13, .c 3, .c 5, .c 19, .c 3, .c 37, .c 53, .c 3, .c 7, .c 29, .c 3,
  .c 23, .c 5, .c 3, .c 79, .c 7, .c 3, .c 5, .c 31, .c 3, .p pv3 [pv2,pv5,pv13,pv2699],
  .p pv2 [pv2,pv3,pv467827], .c 3, .c 409, .c 11, .c 3, .c 13, .c 5, .c 3, .c 7, .c 47, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv7,pv13,pv53,pv97], .c 3, .c 11, .c 7, .c 3, .c 29, .c 13, .c 3, .c 19,
  .c 5, .c 3, .p pv3 [pv2,pv87719], .c 149, .c 3, .c 5, .p pv5 [pv2,pv3,pv116959], .c 3, .c 7,
  .c 17, .c 3, .p pv2 [pv2,pv29,pv48397], .c 461, .c 3, .c 113, .c 5, .c 3, .c 53, .c 19,
]
private theorem h0342c20 : checkBlock 2806787 128 b0342c20 = true := by
  decide +kernel

private def b0342c21 : List Row := [
  .c 3, .c 5, .c 491, .c 3, .c 13, .c 197, .c 3, .c 11, .c 103, .c 3, .c 7, .c 5, .c 3, .c 73,
  .p pv13 [pv2,pv3,pv5,pv7,pv13367], .c 3, .c 5, .c 7, .c 3, .c 23, .c 43, .c 3,
  .p pv5 [pv2,pv311,pv4513], .p pv7 [pv2,pv3,pv58481], .c 3, .c 101, .c 5, .c 3, .c 67, .c 11,
  .c 3, .c 5, .c 79, .c 3, .p pv13 [pv2,pv5,pv280711], .c 29, .c 3, .c 19, .c 7, .c 3, .c 11,
  .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv137,pv683], .c 3, .c 5, .c 467, .c 3,
  .p pv3 [pv2,pv5,pv7,pv20051], .c 31, .c 3, .c 7, .c 89, .c 3, .c 37, .c 5, .c 3, .c 17, .c 7,
  .c 3, .c 5, .c 11, .c 3, .c 29, .c 23, .c 3, .p pv3 [pv2,pv17,pv20641],
  .p pv2 [pv2,pv3,pv11,pv42533], .c 3, .c 367, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv37,pv281],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv23,pv1453], .c 3, .c 967, .c 7, .c 3, .c 13,
  .p pv37 [pv2,pv3,pv127,pv307], .c 3, .p pv2 [pv2,pv19,pv43,pv859], .c 5, .c 3, .c 23, .c 1051,
  .c 3, .c 5, .c 17, .c 3, .c 7, .c 11, .c 3, .c 1181, .p pv13 [pv2,pv3,pv7,pv89,pv751], .c 3,
  .c 503, .c 5, .c 3, .c 541, .c 53, .c 3, .c 5, .c 179, .c 3, .c 17, .c 47, .c 3, .c 31, .c 19,
  .c 3, .c 7, .c 5, .c 3, .c 59, .c 61, .c 3, .c 5, .c 7, .c 3, .c 443, .c 199, .c 3, .c 313,
]
private theorem h0342c21 : checkBlock 2807043 128 b0342c21 = true := by
  decide +kernel

private def b0342c22 : List Row := [
  .c 11, .c 3, .p pv5 [pv2,pv1403651], .c 5, .c 3, .c 83, .c 13, .c 3, .c 5, .c 157, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv7,pv66841], .c 3, .c 89, .c 7, .c 3, .c 647, .c 5, .c 3, .c 863, .c 43, .c 3,
  .c 5, .c 223, .c 3, .c 457, .p pv7 [pv2,pv3,pv41,pv317], .c 3, .c 7, .c 107, .c 3, .c 13, .c 5,
  .c 3, .p pv3 [pv2,pv103,pv3407], .c 7, .c 3, .c 5, .c 1571, .c 3,
  .p pv2 [pv2,pv5,pv17,pv23,pv359], .c 19, .c 3, .c 11, .c 13, .c 3, .c 41, .c 5, .c 3, .c 7,
  .c 401, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv1061], .c 3, .c 71, .c 7, .c 3, .c 233, .c 479, .c 3,
  .c 79, .c 5, .c 3, .c 1607, .c 11, .c 3, .c 5, .c 167, .c 3, .c 7, .p pv2 [pv2,pv3,pv11,pv1289],
  .c 3, .c 197, .c 23, .c 3, .c 11, .c 5, .c 3, .c 19, .c 29, .c 3, .c 5, .c 13, .c 3, .c 97,
  .p pv19 [pv2,pv3,pv23,pv2543], .c 3, .p pv2 [pv2,pv7,pv100267], .p pv3 [pv2,pv3,pv19,pv8209],
  .c 3, .c 7, .c 5, .c 3, .c 1439, .c 181, .c 3, .c 5, .c 7, .c 3, .c 67, .c 991, .c 3, .c 73,
  .c 191, .c 3, .c 43, .c 5, .c 3, .c 11, .p pv7 [pv2,pv3,pv5,pv5849], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv293,pv1597], .c 3, .p pv11 [pv2,pv5,pv11,pv25523], .c 17, .c 3,
  .p pv3 [pv2,pv227,pv773], .c 7, .c 3, .c 151, .c 5, .c 3, .p pv2 [pv2,pv29,pv24203],
  .p pv13 [pv2,pv3,pv5,pv17,pv367], .c 3,
]
private theorem h0342c22 : checkBlock 2807299 128 b0342c22 = true := by
  decide +kernel

private def b0342c23 : List Row := [
  .c 5, .c 41, .c 3, .p pv3 [pv2,pv5,pv7,pv37,pv271], .c 11, .c 3, .c 7, .c 53, .c 3, .c 19, .c 5,
  .c 3, .c 1423, .c 7, .c 3, .c 5, .c 23, .c 3, .p pv13 [pv2,pv5,pv280759],
  .p pv5 [pv2,pv3,pv19,pv47,pv131], .c 3, .c 13, .c 43, .c 3, .p pv5 [pv2,pv7,pv28649], .c 5,
  .c 3, .c 7, .c 19, .c 3, .c 5, .c 173, .c 3, .c 587, .c 7, .c 3, .c 1499, .c 11, .c 3, .c 23,
  .c 5, .c 3, .c 31, .c 83, .c 3, .c 5, .c 61, .c 3, .c 7, .c 73, .c 3, .p pv3 [pv2,pv23,pv15259],
  .p pv3 [pv2,pv3,pv7,pv22283], .c 3, .p pv5 [pv2,pv11,pv13,pv9817], .c 5, .c 3, .c 17, .c 37,
  .c 3, .c 5, .c 103, .c 3, .c 563, .c 89, .c 3, .c 19, .p pv7 [pv2,pv3,pv13,pv8999], .c 3, .c 7,
  .c 5, .c 3, .c 101, .c 13, .c 3, .c 5, .c 7, .c 3, .c 113, .c 757, .c 3, .c 11, .c 419, .c 3,
  .c 131, .c 5, .c 3, .p pv3 [pv2,pv7,pv11,pv43,pv53], .c 109, .c 3, .c 5, .c 17, .c 3,
  .p pv3 [pv2,pv5,pv13,pv10799], .c 1361, .c 3, .c 881, .c 7, .c 3, .c 13, .c 5, .c 3, .c 1559,
  .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv71], .c 3, .c 17, .c 383, .c 3, .c 7, .c 13, .c 3,
  .c 11, .c 5, .c 3, .p pv2 [pv2,pv17,pv157,pv263], .c 7, .c 3, .c 5, .c 743, .c 3, .c 19, .c 41,
  .c 3, .c 83, .c 29,
]
private theorem h0342c23 : checkBlock 2807555 128 b0342c23 = true := by
  decide +kernel

private def b0342c24 : List Row := [
  .c 3, .c 683, .c 5, .c 3, .c 7, .p pv37 [pv2,pv3,pv5,pv19,pv821], .c 3, .c 5, .c 11, .c 3,
  .c 13, .c 7, .c 3, .c 71, .c 17, .c 3, .c 127, .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv18719],
  .c 3, .c 5, .c 13, .c 3, .c 7, .c 23, .c 3, .c 29, .c 59, .c 3, .c 17, .c 5, .c 3,
  .p pv7 [pv2,pv1403939], .p pv29 [pv2,pv3,pv5,pv23399], .c 3, .c 5, .c 31, .c 3, .c 61, .c 11,
  .c 3, .c 79, .p pv2 [pv2,pv3,pv479,pv977], .c 3, .c 7, .c 5, .c 3, .c 13, .c 1231, .c 3, .c 5,
  .c 7, .c 3, .c 47, .c 313, .c 3, .p pv5 [pv2,pv11,pv41,pv283], .p pv7 [pv2,pv3,pv59,pv661],
  .c 3, .p pv2 [pv2,pv23,pv1327], .c 5, .c 3, .c 139, .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv17333],
  .c 3, .c 461, .c 19, .c 3, .c 193, .c 7, .c 3, .c 173, .c 5, .c 3, .p pv3 [pv2,pv47,pv1867],
  .p pv2 [pv2,pv3,pv5,pv11,pv67,pv127], .c 3, .c 5, .p pv5 [pv2,pv3,pv79,pv1481], .c 3, .c 11,
  .c 29, .c 3, .c 7, .c 751, .c 3, .c 53, .c 5, .c 3, .c 659, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv468001], .c 3, .c 31, .c 13, .c 3, .p pv3 [pv2,pv223,pv787], .c 311, .c 3,
  .p pv5 [pv2,pv7,pv200573], .c 5, .c 3, .c 7, .p pv17 [pv2,pv3,pv5,pv93601], .c 3, .c 5, .c 67,
  .c 3, .c 29, .c 7, .c 3, .c 11, .c 41, .c 3, .c 97, .c 5, .c 3, .p pv2 [pv2,pv11,pv109,pv1171],
  .p pv2 [pv2,pv3,pv5,pv17,pv2753], .c 3, .c 5,
]
private theorem h0342c24 : checkBlock 2807811 128 b0342c24 = true := by
  decide +kernel

private def b0342c25 : List Row := [
  .c 19, .c 3, .c 7, .c 31, .c 3, .c 17, .p pv3 [pv2,pv3,pv7,pv13,pv37,pv139], .c 3,
  .p pv2 [pv2,pv191,pv7351], .c 5, .c 3, .c 103, .c 11, .c 3, .c 5, .c 127, .c 3,
  .p pv2 [pv2,pv5,pv28081], .c 101, .c 3, .p pv2 [pv2,pv7,pv200579], .c 47, .c 3, .c 7, .c 5,
  .c 3, .p pv13 [pv2,pv1404059], .c 71, .c 3, .c 5, .c 7, .c 3, .c 41, .c 839, .c 3, .c 1409,
  .c 23, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv7,pv100291], .c 1319, .c 3, .c 5, .c 11, .c 3,
  .p pv7 [pv2,pv5,pv17551], .c 113, .c 3, .c 109, .c 7, .c 3, .c 1049, .c 5, .c 3, .c 11, .c 19,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv29,pv16139], .c 3, .c 389, .p pv17 [pv2,pv3,pv71,pv103], .c 3,
  .c 7, .c 211, .c 3, .c 47, .c 5, .c 3, .c 283, .c 7, .c 3, .c 5, .c 89, .c 3, .c 13, .c 11,
  .c 3, .c 229, .p pv2 [pv2,pv3,pv31,pv7549], .c 3, .c 1613, .c 5, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv5,pv11701], .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv47,pv239], .c 7, .c 3,
  .c 19, .c 31, .c 3, .c 37, .c 5, .c 3, .p pv2 [pv2,pv702067], .c 347, .c 3, .c 5, .c 23, .c 3,
  .c 7, .c 439, .c 3, .c 43, .c 11, .c 3, .p pv2 [pv2,pv79,pv8887], .c 5, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv5,pv11,pv23,pv37], .c 3, .c 5, .p pv3 [pv2,pv3,pv89,pv1753], .c 3, .c 11,
  .p pv5 [pv2,pv3,pv13,pv9001], .c 3, .c 373, .p pv13 [pv2,pv3,pv61,pv7673], .c 3,
]
private theorem h0342c25 : checkBlock 2808067 128 b0342c25 = true := by
  decide +kernel

private def b0342c26 : List Row := [
  .c 7, .c 5, .c 3, .p pv3 [pv2,pv351041], .c 29, .c 3, .c 5, .c 7, .c 3, .c 59, .c 193, .c 3,
  .p pv2 [pv2,pv23,pv61051], .c 17, .c 3, .p pv3 [pv2,pv19,pv31,pv149], .c 5, .c 3,
  .p pv7 [pv2,pv7,pv200597], .p pv11 [pv2,pv3,pv5,pv29,pv269], .c 3, .c 5, .c 929, .c 3, .c 19,
  .c 43, .c 3, .c 11, .c 7, .c 3, .c 17, .c 5, .c 3, .c 29, .c 47, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv181,pv431], .c 3, .c 727, .c 13, .c 3, .c 7, .c 19, .c 3,
  .p pv2 [pv2,pv461,pv1523], .c 5, .c 3, .p pv2 [pv2,pv29,pv41,pv1181], .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv468071], .c 3, .c 983, .p pv5 [pv2,pv3,pv11,pv197], .c 3,
  .p pv2 [pv2,pv307,pv2287], .c 67, .c 3, .c 11, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 359,
  .c 3, .c 23, .c 7, .c 3, .c 1061, .p pv2 [pv2,pv3,pv13,pv17,pv353], .c 3, .c 601, .c 5, .c 3,
  .p pv7 [pv2,pv127,pv11057], .c 13, .c 3, .c 5, .c 11, .c 3, .c 7, .c 811, .c 3,
  .p pv3 [pv2,pv257,pv683], .p pv2 [pv2,pv3,pv7,pv11,pv6079], .c 3, .c 277, .c 5, .c 3, .c 11,
  .p pv19 [pv2,pv3,pv5,pv179,pv523], .c 3, .c 5, .p pv2 [pv2,pv3,pv234043], .c 3,
  .p pv3 [pv2,pv5,pv11,pv13,pv491], .c 19, .c 3, .p pv5 [pv2,pv7,pv200609], .c 73, .c 3, .c 7,
  .c 5, .c 3, .c 383, .c 41, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv56171], .c 11, .c 3,
  .c 419, .c 13, .c 3, .c 29, .c 5, .c 3, .c 31, .p pv2 [pv2,pv3,pv5,pv17,pv5507], .c 3, .c 5,
  .c 59,
]
private theorem h0342c26 : checkBlock 2808323 128 b0342c26 = true := by
  decide +kernel

private def b0342c27 : List Row := [
  .c 3, .c 631, .p pv7 [pv2,pv3,pv7,pv41,pv233], .c 3, .c 17, .c 7, .c 3,
  .p pv3 [pv2,pv29,pv6053], .c 5, .c 3, .c 19, .p pv7 [pv2,pv3,pv5,pv31,pv151], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv167,pv2803], .c 3, .c 13, .c 911, .c 3, .c 7, .c 11, .c 3, .c 41, .c 5, .c 3,
  .c 53, .c 7, .c 3, .c 5, .c 13, .c 3, .c 11, .c 107, .c 3, .p pv5 [pv2,pv1404323], .c 1453,
  .c 3, .c 163, .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv46811], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv22291], .c 3, .c 227, .c 7, .c 3, .p pv2 [pv2,pv13,pv54013], .c 29, .c 3,
  .p pv2 [pv2,pv53,pv26497], .c 5, .c 3, .c 13, .c 23, .c 3, .c 5, .p pv7 [pv2,pv3,pv11,pv10639],
  .c 3, .c 7, .p pv31 [pv2,pv3,pv13,pv4001], .c 3, .c 11, .c 101, .c 3, .c 19, .c 5, .c 3,
  .p pv7 [pv2,pv11,pv127669], .p pv7 [pv2,pv3,pv5,pv47,pv83], .c 3, .c 5, .c 1033, .c 3, .c 1289,
  .p pv2 [pv2,pv3,pv19,pv97,pv127], .c 3, .c 23, .p pv2 [pv2,pv3,pv156041], .c 3, .c 7, .c 5,
  .c 3, .c 571, .c 11, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv23,pv43,pv71],
  .p pv2 [pv2,pv3,pv11,pv42557], .c 3, .c 13, .c 379, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv28661], .c 37, .c 3, .c 5, .c 41, .c 3, .c 17, .c 13, .c 3,
  .p pv2 [pv2,pv702199], .c 7, .c 3, .c 43, .c 5, .c 3, .p pv3 [pv2,pv17,pv19,pv1087],
  .p pv2 [pv2,pv3,pv5,pv101,pv103], .c 3, .c 5, .c 11, .c 3, .c 73, .c 883, .c 3, .c 7, .c 23,
  .c 3, .p pv3 [pv2,pv13,pv211],
]
private theorem h0342c27 : checkBlock 2808579 128 b0342c27 = true := by
  decide +kernel

private def b0342c28 : List Row := [
  .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv19,pv43,pv191], .c 3, .c 761, .c 29,
  .c 3, .c 107, .c 17, .c 3, .p pv5 [pv2,pv7,pv313,pv641], .c 5, .c 3, .c 7, .c 13, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv17,pv281], .c 3, .p pv3 [pv2,pv5,pv35111], .c 7, .c 3, .c 157, .c 43,
  .c 3, .c 17, .c 5, .c 3, .c 823, .p pv2 [pv2,pv3,pv5,pv3121], .c 3, .c 5, .c 701, .c 3, .c 7,
  .c 103, .c 3, .p pv2 [pv2,pv11,pv63839], .p pv3 [pv2,pv3,pv7,pv2477], .c 3, .c 13, .c 5, .c 3,
  .c 37, .c 59, .c 3, .c 5, .c 317, .c 3, .c 19, .c 1487, .c 3, .c 53, .c 11, .c 3, .c 7, .c 5,
  .c 3, .p pv29 [pv2,pv1404479], .c 17, .c 3, .c 5, .c 7, .c 3, .c 11, .c 71, .c 3,
  .p pv3 [pv2,pv419], .c 19, .c 3, .p pv5 [pv2,pv11,pv127681], .c 5, .c 3, .c 61, .c 293, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv234083], .c 3, .c 13, .c 31, .c 3, .p pv5 [pv2,pv1404503], .c 7, .c 3,
  .c 23, .c 5, .c 3, .p pv2 [pv2,pv43,pv89,pv367], .c 463, .c 3, .c 5, .c 13, .c 3, .c 877, .c 41,
  .c 3, .c 7, .c 109, .c 3, .c 211, .c 5, .c 3, .c 47, .c 7, .c 3, .c 5, .c 277, .c 3, .c 43,
  .c 17, .c 3, .c 113, .p pv11 [pv2,pv3,pv234089], .c 3, .p pv3 [pv2,pv7,pv3583], .c 5, .c 3,
  .c 7, .c 11, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv66883], .c 3,
]
private theorem h0342c28 : checkBlock 2808835 128 b0342c28 = true := by
  decide +kernel

private def b0342c29 : List Row := [
  .p pv2 [pv2,pv5,pv280909], .c 7, .c 3, .c 17, .p pv2 [pv2,pv3,pv156061], .c 3, .c 11, .c 5,
  .c 3, .c 67, .c 61, .c 3, .c 5, .p pv7 [pv2,pv3,pv78031], .c 3, .c 7, .c 1597, .c 3, .c 31,
  .c 887, .c 3, .c 719, .c 5, .c 3, .c 1201, .p pv17 [pv2,pv3,pv5,pv46819], .c 3, .c 5, .c 11,
  .c 3, .c 23, .c 569, .c 3, .c 13, .c 53, .c 3, .c 7, .c 5, .c 3, .c 11, .c 509, .c 3, .c 5,
  .c 7, .c 3, .p pv2 [pv2,pv5,pv11,pv113], .c 13, .c 3, .p pv2 [pv2,pv71,pv73,pv271], .c 31, .c 3,
  .c 1621, .c 5, .c 3, .c 17, .c 29, .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv280921], .c 11,
  .c 3, .c 97, .c 7, .c 3, .p pv5 [pv2,pv13,pv103,pv1049], .c 5, .c 3, .c 1171, .c 1223, .c 3,
  .c 5, .c 47, .c 3, .p pv3 [pv2,pv5,pv7,pv79,pv127], .c 23, .c 3, .c 7,
  .p pv41 [pv2,pv3,pv13,pv2251], .c 3, .p pv2 [pv2,pv702313], .c 5, .c 3, .c 29, .c 7, .c 3, .c 5,
  .c 17, .c 3, .p pv11 [pv2,pv5,pv280927], .p pv23 [pv2,pv3,pv117053], .c 3,
  .p pv2 [pv2,pv43,pv16333], .c 11, .c 3, .c 19, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv11,pv8513], .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv929], .c 3, .c 11, .c 7,
  .c 3, .p pv2 [pv2,pv1404653], .p pv7 [pv2,pv3,pv193,pv1213], .c 3, .c 13, .c 5, .c 3, .c 43,
  .c 19, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv36017], .c 3, .c 7, .c 421, .c 3, .c 241, .c 13, .c 3,
  .p pv5 [pv2,pv1404671], .c 5,
]
private theorem h0342c29 : checkBlock 2809091 128 b0342c29 = true := by
  decide +kernel

private def b0342c30 : List Row := [
  .c 3, .p pv2 [pv2,pv702337], .p pv23 [pv2,pv3,pv5,pv2081], .c 3, .c 5, .c 307, .c 3, .c 41,
  .p pv2 [pv2,pv3,pv43,pv10889], .c 3, .c 11, .c 17, .c 3, .c 7, .c 5, .c 3, .c 613, .c 23, .c 3,
  .c 5, .c 7, .c 3, .c 13, .c 449, .c 3, .c 19, .c 71, .c 3, .c 17, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv6271], .c 11, .c 3, .c 5, .c 13, .c 3, .c 409,
  .p pv3 [pv2,pv3,pv7,pv11,pv2027], .c 3, .c 23, .c 7, .c 3, .c 11, .c 5, .c 3,
  .p pv19 [pv2,pv281,pv4999], .c 167, .c 3, .c 5, .c 37, .c 3, .p pv13 [pv2,pv5,pv7,pv23,pv349],
  .p pv19 [pv2,pv3,pv234121], .c 3, .c 7, .c 137, .c 3, .c 89, .c 5, .c 3, .c 13, .c 7, .c 3,
  .c 5, .c 11, .c 3, .c 829, .p pv3 [pv2,pv3,pv13,pv181,pv199], .c 3, .p pv5 [pv2,pv1404743],
  .p pv13 [pv2,pv3,pv11,pv17,pv313], .c 3, .p pv2 [pv2,pv7,pv19,pv5281], .c 5, .c 3, .c 7, .c 193,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv151,pv443], .c 3, .c 19, .c 7, .c 3, .c 101, .c 23, .c 3,
  .p pv2 [pv2,pv17,pv82633], .c 5, .c 3, .p pv3 [pv2,pv331,pv1061], .c 103, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv14633], .c 3, .c 7, .c 11, .c 3, .c 13, .c 19, .c 3, .p pv3 [pv2,pv89,pv1973],
  .c 5, .c 3, .p pv7 [pv2,pv37,pv37967], .c 31, .c 3, .c 5, .p pv3 [pv2,pv3,pv41,pv47], .c 3,
  .c 317, .c 13, .c 3, .c 43, .c 227, .c 3, .c 7, .c 5, .c 3, .c 733, .c 1151, .c 3, .c 5, .c 7,
  .c 3, .c 229,
]
private theorem h0342c30 : checkBlock 2809347 128 b0342c30 = true := by
  decide +kernel

private def b0342c31 : List Row := [
  .p pv2 [pv2,pv3,pv156089], .c 3, .c 17, .c 11, .c 3, .c 47, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv101,pv1987], .c 127, .c 3, .c 5, .p pv2 [pv2,pv3,pv468271], .c 3, .c 11,
  .c 83, .c 3, .p pv3 [pv2,pv29,pv53,pv457], .c 7, .c 3, .p pv2 [pv2,pv11,pv127711], .c 5, .c 3,
  .p pv3 [pv2,pv41,pv4283], .c 13, .c 3, .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv7,pv47,pv61], .c 19,
  .c 3, .c 7, .c 37, .c 3, .p pv3 [pv2,pv157,pv2237], .c 5, .c 3, .p pv11 [pv2,pv739,pv1901],
  .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv42571], .c 3, .p pv2 [pv2,pv5,pv13,pv21613], .c 109,
  .c 3, .c 11, .p pv2 [pv2,pv3,pv59,pv7937], .c 3, .c 13, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv31219], .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv13,pv31,pv83], .c 3, .c 61,
  .c 7, .c 3, .p pv5 [pv2,pv17,pv23,pv3593], .c 13, .c 3, .c 137, .c 5, .c 3, .c 19, .c 11, .c 3,
  .c 5, .c 31, .c 3, .c 7, .c 521, .c 3, .c 59, .p pv7 [pv2,pv3,pv7,pv19,pv503], .c 3, .c 11,
  .c 5, .c 3, .p pv3 [pv2,pv13,pv27017], .c 41, .c 3, .c 5, .c 17, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv61,pv853], .c 3, .p pv2 [pv2,pv7,pv200699], .c 859, .c 3, .c 7, .c 5, .c 3,
  .c 83, .c 47, .c 3, .c 5, .c 7, .c 3, .c 17, .p pv13 [pv2,pv3,pv41,pv5711], .c 3, .c 37, .c 89,
  .c 3, .p pv5 [pv2,pv1404911], .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv229,pv409], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv26017], .c 3, .c 23, .c 61, .c 3, .p pv5 [pv2,pv13,pv67,pv1613], .c 7, .c 3,
  .c 19, .c 5, .c 3,
]
private theorem h0342c31 : checkBlock 2809603 128 b0342c31 = true := by
  decide +kernel

def rows0342 : List Row :=
  b0342c00 ++ b0342c01 ++ b0342c02 ++ b0342c03 ++ b0342c04 ++ b0342c05 ++ b0342c06 ++ b0342c07 ++
  b0342c08 ++ b0342c09 ++ b0342c10 ++ b0342c11 ++ b0342c12 ++ b0342c13 ++ b0342c14 ++ b0342c15 ++
  b0342c16 ++ b0342c17 ++ b0342c18 ++ b0342c19 ++ b0342c20 ++ b0342c21 ++ b0342c22 ++ b0342c23 ++
  b0342c24 ++ b0342c25 ++ b0342c26 ++ b0342c27 ++ b0342c28 ++ b0342c29 ++ b0342c30 ++ b0342c31

theorem checked0342 : checkBlock 2801667 4096 rows0342 = true :=
  checkBlock_append h0342c00 (
    checkBlock_append h0342c01 (
    checkBlock_append h0342c02 (
    checkBlock_append h0342c03 (
    checkBlock_append h0342c04 (
    checkBlock_append h0342c05 (
    checkBlock_append h0342c06 (
    checkBlock_append h0342c07 (
    checkBlock_append h0342c08 (
    checkBlock_append h0342c09 (
    checkBlock_append h0342c10 (
    checkBlock_append h0342c11 (
    checkBlock_append h0342c12 (
    checkBlock_append h0342c13 (
    checkBlock_append h0342c14 (
    checkBlock_append h0342c15 (
    checkBlock_append h0342c16 (
    checkBlock_append h0342c17 (
    checkBlock_append h0342c18 (
    checkBlock_append h0342c19 (
    checkBlock_append h0342c20 (
    checkBlock_append h0342c21 (
    checkBlock_append h0342c22 (
    checkBlock_append h0342c23 (
    checkBlock_append h0342c24 (
    checkBlock_append h0342c25 (
    checkBlock_append h0342c26 (
    checkBlock_append h0342c27 (
    checkBlock_append h0342c28 (
    checkBlock_append h0342c29 (
    checkBlock_append h0342c30 (
    h0342c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
