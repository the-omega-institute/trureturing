/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks02/Block0228
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks02/Block0228.checked0228
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table020
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table028
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table032
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table039
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table048
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table062
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table087
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table135
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table136

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0228c00 : List Row := [
  .c 3, .c 31, .p pv3 [pv2,pv3,pv7,pv6353], .c 3, .p pv2 [pv2,pv933893], .c 7, .c 3, .c 101, .c 5,
  .c 3, .p pv13 [pv2,pv131,pv7129], .c 13, .c 3, .c 5, .c 17, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv31,pv5021], .c 3, .c 7, .p pv3 [pv2,pv3,pv311303], .c 3,
  .p pv5 [pv2,pv11,pv59,pv1439], .c 5, .c 3, .c 157, .c 7, .c 3, .c 5, .c 41, .c 3, .c 17, .c 31,
  .c 3, .p pv5 [pv2,pv933923], .p pv41 [pv2,pv3,pv223,pv349], .c 3, .c 13, .c 5, .c 3, .c 7,
  .c 29, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv11,pv13,pv311], .c 3, .c 19, .c 7, .c 3, .c 11, .c 13,
  .c 3, .p pv2 [pv2,pv139,pv6719], .c 5, .c 3, .c 647, .c 383, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv25943], .c 3, .c 7, .c 409, .c 3, .p pv2 [pv2,pv933953], .c 17, .c 3,
  .p pv3 [pv2,pv233489], .c 5, .c 3, .c 29, .c 11, .c 3, .c 5, .p pv29 [pv2,pv3,pv17,pv18313],
  .c 3, .c 13, .c 109, .c 3, .c 1093, .c 71, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv29,pv16103],
  .p pv13 [pv2,pv3,pv5,pv7,pv593], .c 3, .c 5, .c 7, .c 3, .c 233, .c 43, .c 3, .c 31,
  .p pv7 [pv2,pv3,pv23,pv47], .c 3, .p pv2 [pv2,pv461,pv1013], .c 5, .c 3, .p pv2 [pv2,pv7,pv389],
  .c 809, .c 3, .c 5, .c 11, .c 3, .c 23, .p pv5 [pv2,pv3,pv7,pv11119], .c 3, .c 73, .c 7, .c 3,
  .c 61, .c 5, .c 3, .c 11, .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv38917], .c 3, .c 89, .c 19, .c 3,
  .c 7, .c 31, .c 3, .p pv3 [pv2,pv7297],
]
private theorem h0228c00 : checkBlock 1867779 128 b0228c00 = true := by
  decide +kernel

private def b0228c01 : List Row := [
  .c 5, .c 3, .p pv17 [pv2,pv53,pv17623], .c 7, .c 3, .c 5, .c 193, .c 3,
  .p pv2 [pv2,pv5,pv37361], .c 11, .c 3, .p pv3 [pv2,pv37,pv6311], .p pv2 [pv2,pv3,pv59,pv1759],
  .c 3, .p pv5 [pv2,pv7,pv17,pv47,pv167], .c 5, .c 3, .c 7, .c 223, .c 3, .c 5, .c 1291, .c 3,
  .c 71, .c 7, .c 3, .c 13, .c 263, .c 3, .c 29, .c 5, .c 3, .c 19, .c 181, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv23,pv13537], .c 3, .c 7, .c 13, .c 3, .c 59, .c 11, .c 3, .c 97, .c 5, .c 3,
  .c 23, .c 443, .c 3, .c 5, .c 19, .c 3, .c 11, .c 73, .c 3, .c 17, .p pv19 [pv2,pv3,pv51893],
  .c 3, .c 7, .c 5, .c 3, .p pv13 [pv2,pv934079], .c 67, .c 3, .c 5, .c 7, .c 3, .c 191,
  .p pv2 [pv2,pv3,pv151,pv1031], .c 3, .c 311, .p pv2 [pv2,pv3,pv13,pv43,pv557], .c 3,
  .p pv5 [pv2,pv229,pv4079], .c 5, .c 3, .p pv2 [pv2,pv7,pv66721], .c 13, .c 3, .c 5, .c 53, .c 3,
  .p pv3 [pv2,pv5,pv9341], .c 47, .c 3, .c 11, .c 7, .c 3, .c 19, .c 5, .c 3, .c 929, .c 23, .c 3,
  .c 5, .c 173, .c 3, .p pv31 [pv2,pv5,pv7,pv13,pv2053], .c 653, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv29,pv1193], .c 3, .c 13, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv499], .c 3, .p pv2 [pv2,pv5,pv109,pv857], .c 239, .c 3, .c 23, .c 13,
  .c 3, .c 11, .c 5, .c 3, .c 7, .c 599, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv44483], .c 3,
]
private theorem h0228c01 : checkBlock 1868035 128 b0228c01 = true := by
  decide +kernel

private def b0228c02 : List Row := [
  .p pv2 [pv2,pv5,pv23,pv8123], .c 7, .c 3, .c 47, .c 139, .c 3, .c 53, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv19,pv31,pv61], .c 149, .c 3, .c 5, .c 11, .c 3, .c 7, .c 151, .c 3, .c 19,
  .c 41, .c 3, .p pv2 [pv2,pv467083], .c 5, .c 3, .c 11, .c 773, .c 3, .c 5, .c 13, .c 3, .c 17,
  .c 59, .c 3, .c 373, .c 23, .c 3, .c 7, .c 5, .c 3, .c 61, .p pv2 [pv2,pv3,pv5,pv7,pv31,pv41],
  .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv93419], .c 11, .c 3, .p pv2 [pv2,pv13,pv71861], .c 37,
  .c 3, .c 43, .c 5, .c 3, .c 13, .c 31, .c 3, .c 5, .p pv3 [pv2,pv3,pv137,pv2273], .c 3, .c 41,
  .c 83, .c 3, .c 733, .c 7, .c 3, .p pv5 [pv2,pv19,pv49169], .c 5, .c 3, .c 67, .c 947, .c 3,
  .c 5, .c 227, .c 3, .c 19, .p pv2 [pv2,pv3,pv311407], .c 3, .c 7, .c 11, .c 3, .c 17, .c 5,
  .c 3, .p pv2 [pv2,pv934229], .c 7, .c 3, .c 5, .c 467, .c 3, .c 11, .c 241, .c 3, .c 13, .c 19,
  .c 3, .p pv5 [pv2,pv7,pv11,pv1103], .c 5, .c 3, .c 7, .c 61, .c 3, .c 5, .c 23, .c 3,
  .p pv2 [pv2,pv5,pv37,pv101], .c 7, .c 3, .c 71, .c 601, .c 3, .p pv3 [pv2,pv58391], .c 5, .c 3,
  .p pv7 [pv2,pv934259], .c 17, .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv9437], .c 3, .c 7,
  .p pv2 [pv2,pv3,pv47,pv3313], .c 3, .c 11, .c 509, .c 3, .c 23, .c 5,
]
private theorem h0228c02 : checkBlock 1868291 128 b0228c02 = true := by
  decide +kernel

private def b0228c03 : List Row := [
  .c 3, .p pv2 [pv2,pv11,pv42467], .c 127, .c 3, .c 5, .c 29, .c 3, .p pv11 [pv2,pv5,pv23357],
  .c 67, .c 3, .p pv5 [pv2,pv7,pv23,pv829], .p pv11 [pv2,pv3,pv13,pv53,pv113], .c 3, .c 7, .c 5,
  .c 3, .c 47, .c 11, .c 3, .c 5, .c 7, .c 3, .p pv19 [pv2,pv5,pv186859], .c 19, .c 3, .c 563,
  .p pv3 [pv2,pv3,pv103811], .c 3, .c 11, .c 5, .c 3, .c 149, .c 37, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv41,pv211], .c 3, .c 53, .c 17, .c 3, .p pv2 [pv2,pv47,pv103,pv193], .c 7,
  .c 3, .c 13, .c 5, .c 3, .p pv11 [pv2,pv934319], .p pv7 [pv2,pv3,pv5,pv17,pv229], .c 3, .c 5,
  .c 11, .c 3, .c 43, .c 1361, .c 3, .c 7, .c 13, .c 3, .p pv5 [pv2,pv83,pv11257], .c 5, .c 3,
  .c 11, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv155723], .c 3, .c 23, .c 983, .c 3,
  .p pv5 [pv2,pv934343], .c 1367, .c 3, .p pv3 [pv2,pv7,pv66739], .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv6229], .c 3, .c 5, .c 19, .c 3, .c 13, .c 7, .c 3,
  .p pv2 [pv2,pv139,pv3361], .p pv3 [pv2,pv3,pv311453], .c 3, .p pv2 [pv2,pv37,pv25253], .c 5,
  .c 3, .c 103, .c 29, .c 3, .c 5, .c 13, .c 3, .c 7, .c 269, .c 3, .p pv2 [pv2,pv11,pv173,pv491],
  .p pv2 [pv2,pv3,pv7,pv22247], .c 3, .p pv3 [pv2,pv116797], .c 5, .c 3, .c 17, .c 619, .c 3,
  .c 5, .c 47, .c 3, .c 157, .c 23, .c 3, .p pv3 [pv2,pv7,pv13,pv17,pv151], .c 11, .c 3, .c 7,
  .c 5, .c 3, .c 13, .c 71, .c 3, .c 5, .c 7, .c 3, .c 11,
]
private theorem h0228c03 : checkBlock 1868547 128 b0228c03 = true := by
  decide +kernel

private def b0228c04 : List Row := [
  .c 101, .c 3, .p pv5 [pv2,pv934403], .c 199, .c 3, .p pv2 [pv2,pv11,pv42473], .c 5, .c 3, .c 23,
  .c 19, .c 3, .c 5, .c 17, .c 3, .c 67, .c 37, .c 3, .p pv2 [pv2,pv467209], .c 7, .c 3,
  .p pv2 [pv2,pv23,pv40627], .c 5, .c 3, .c 379, .p pv19 [pv2,pv3,pv5,pv4153], .c 3, .c 5, .c 61,
  .c 3, .c 17, .p pv3 [pv2,pv3,pv41,pv71,pv107], .c 3, .c 7, .c 229, .c 3, .c 73, .c 5, .c 3,
  .p pv11 [pv2,pv11,pv17,pv19,pv263], .c 7, .c 3, .c 5, .c 877, .c 3, .c 227, .c 13, .c 3, .c 19,
  .c 97, .c 3, .c 41, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv19,pv1171], .c 3,
  .c 673, .c 7, .c 3, .c 151, .c 17, .c 3, .c 11, .c 5, .c 3, .c 53, .c 1163, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv17,pv73,pv251], .c 3, .c 7, .c 607, .c 3, .c 23, .c 31, .c 3, .c 17, .c 5,
  .c 3, .c 107, .c 13, .c 3, .c 5, .c 11, .c 3, .c 37, .p pv3 [pv2,pv3,pv79,pv3943], .c 3,
  .p pv2 [pv2,pv7,pv133499], .p pv2 [pv2,pv3,pv11,pv14159], .c 3, .c 7, .c 5, .c 3, .c 11, .c 977,
  .c 3, .c 5, .c 7, .c 3, .c 19, .c 1153, .c 3, .c 443, .c 73, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv66751], .c 17, .c 3, .c 5, .c 613, .c 3, .p pv7 [pv2,pv5,pv61,pv383], .c 11,
  .c 3, .c 293, .c 7, .c 3, .p pv2 [pv2,pv31,pv15073], .c 5, .c 3,
]
private theorem h0228c04 : checkBlock 1868803 128 b0228c04 = true := by
  decide +kernel

private def b0228c05 : List Row := [
  .c 127, .c 59, .c 3, .c 5, .c 41, .c 3, .p pv7 [pv2,pv5,pv7,pv26701],
  .p pv7 [pv2,pv3,pv23,pv1693], .c 3, .c 7, .c 29, .c 3, .c 31, .c 5, .c 3, .c 89, .c 7, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv47,pv1657], .c 3, .c 13, .c 373, .c 3, .c 1237, .c 11, .c 3,
  .p pv3 [pv2,pv7,pv33377], .c 5, .c 3, .c 7, .c 163, .c 3, .c 5, .c 13, .c 3, .c 11, .c 7, .c 3,
  .c 29, .p pv2 [pv2,pv3,pv103841], .c 3, .c 47, .c 5, .c 3, .c 41, .c 53, .c 3, .c 5, .c 331,
  .c 3, .c 7, .c 19, .c 3, .c 17, .p pv29 [pv2,pv3,pv7,pv5563], .c 3, .p pv2 [pv2,pv467293], .c 5,
  .c 3, .c 13, .p pv11 [pv2,pv3,pv5,pv31153], .c 3, .c 5, .c 23, .c 3,
  .p pv7 [pv2,pv5,pv41,pv47,pv97], .p pv11 [pv2,pv3,pv13,pv1997], .c 3, .c 11,
  .p pv3 [pv2,pv3,pv311533], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv11,pv1931], .c 967, .c 3, .c 5,
  .c 7, .c 3, .p pv2 [pv2,pv5,pv19,pv4919], .c 61, .c 3, .p pv2 [pv2,pv934613], .c 151, .c 3,
  .c 23, .c 5, .c 3, .c 19, .c 11, .c 3, .c 5, .c 431, .c 3, .p pv2 [pv2,pv5,pv7477], .c 29, .c 3,
  .c 13, .c 7, .c 3, .c 11, .c 5, .c 3, .c 17, .p pv3 [pv2,pv3,pv5,pv13,pv4793], .c 3, .c 5,
  .c 19, .c 3, .c 269, .c 13, .c 3, .c 7, .c 347, .c 3, .p pv2 [pv2,pv557,pv839], .c 5, .c 3,
  .p pv2 [pv2,pv79,pv11831], .c 7, .c 3, .c 5, .c 11, .c 3, .c 29, .c 41,
]
private theorem h0228c05 : checkBlock 1869059 128 b0228c05 = true := by
  decide +kernel

private def b0228c06 : List Row := [
  .c 3, .c 191, .p pv3 [pv2,pv3,pv11,pv1049], .c 3, .c 307, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5,
  .c 17, .c 3, .p pv2 [pv2,pv5,pv11,pv29,pv293], .c 7, .c 3, .c 103, .c 317, .c 3, .c 19, .c 5,
  .c 3, .c 71, .c 13, .c 3, .c 5, .c 67, .c 3, .c 7, .c 11, .c 3, .c 79,
  .p pv2 [pv2,pv3,pv7,pv47,pv947], .c 3, .p pv5 [pv2,pv43,pv21737], .c 5, .c 3,
  .p pv2 [pv2,pv17,pv37,pv743], .c 19, .c 3, .c 5, .c 107, .c 3, .c 467,
  .p pv2 [pv2,pv3,pv311567], .c 3, .p pv5 [pv2,pv7,pv11,pv61,pv199], .c 83, .c 3, .c 7, .c 5,
  .c 3, .p pv2 [pv2,pv257,pv3637], .c 311, .c 3, .c 5, .c 7, .c 3, .c 1193,
  .p pv5 [pv2,pv3,pv77893], .c 3, .c 241, .c 11, .c 3, .p pv2 [pv2,pv934721], .c 5, .c 3,
  .p pv3 [pv2,pv7,pv19,pv251], .c 1021, .c 3, .c 5, .c 73, .c 3, .c 11, .c 23, .c 3, .c 19, .c 7,
  .c 3, .c 17, .c 5, .c 3, .c 599, .c 97, .c 3, .c 5, .p pv5 [pv2,pv3,pv19,pv23,pv31], .c 3,
  .c 13, .c 281, .c 3, .c 7, .c 37, .c 3, .c 149, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 13,
  .c 3, .p pv3 [pv2,pv5,pv23369], .c 1181, .c 3, .c 11, .p pv11 [pv2,pv3,pv61,pv1277], .c 3,
  .c 59, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv6359], .c 3,
  .p pv29 [pv2,pv5,pv139,pv269], .c 7, .c 3, .c 509, .c 41, .c 3, .p pv2 [pv2,pv19,pv49199], .c 5,
  .c 3, .c 13,
]
private theorem h0228c06 : checkBlock 1869315 128 b0228c06 = true := by
  decide +kernel

private def b0228c07 : List Row := [
  .c 11, .c 3, .c 5, .p pv7 [pv2,pv3,pv77899], .c 3, .c 7, .c 659, .c 3, .c 457, .c 61, .c 3,
  .c 11, .c 5, .c 3, .c 809, .c 23, .c 3, .c 5, .c 379, .c 3, .c 101, .c 47, .c 3,
  .p pv3 [pv2,pv7,pv16693], .c 19, .c 3, .c 7, .c 5, .c 3, .c 271,
  .p pv3 [pv2,pv3,pv5,pv7,pv29,pv307], .c 3, .c 5, .c 7, .c 3, .c 31, .c 17, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv11,pv3541], .c 3, .c 631, .c 5, .c 3, .c 11, .c 421, .c 3, .c 5, .c 263, .c 3,
  .c 211, .c 13, .c 3, .c 17, .c 7, .c 3, .c 43, .c 5, .c 3, .c 139,
  .p pv17 [pv2,pv3,pv5,pv62323], .c 3, .c 5, .c 239, .c 3, .c 439, .c 11, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv155809], .c 3, .c 157, .c 5, .c 3, .p pv11 [pv2,pv107,pv8737], .c 7, .c 3,
  .c 5, .c 197, .c 3, .p pv2 [pv2,pv5,pv181,pv1033], .c 19, .c 3, .p pv3 [pv2,pv11,pv21247],
  .c 23, .c 3, .c 1327, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv22259], .c 3,
  .p pv3 [pv2,pv5,pv5843], .c 7, .c 3, .c 941, .c 11, .c 3, .c 163, .c 5, .c 3, .c 17, .c 283,
  .c 3, .c 5, .c 53, .c 3, .c 7, .p pv11 [pv2,pv3,pv19477], .c 3, .c 641, .c 227, .c 3, .c 13,
  .c 5, .c 3, .c 19, .c 113, .c 3, .c 5, .c 1063, .c 3, .c 127, .p pv3 [pv2,pv3,pv73,pv1423],
  .c 3,
]
private theorem h0228c07 : checkBlock 1869571 128 b0228c07 = true := by
  decide +kernel

private def b0228c08 : List Row := [
  .c 31, .c 13, .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv934919], .c 353, .c 3, .c 5, .c 7, .c 3,
  .c 79, .p pv2 [pv2,pv3,pv155821], .c 3, .c 11, .p pv2 [pv2,pv3,pv31,pv1117], .c 3, .c 401, .c 5,
  .c 3, .c 37, .p pv17 [pv2,pv3,pv5,pv157,pv397], .c 3, .c 5, .c 23, .c 3, .c 13, .c 733, .c 3,
  .c 41, .c 7, .c 3, .c 53, .c 5, .c 3, .c 167, .c 11, .c 3, .c 5, .c 13, .c 3, .c 181, .c 137,
  .c 3, .c 7, .c 241, .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv41,pv5701], .c 7, .c 3, .c 5, .c 307,
  .c 3, .c 43, .c 37, .c 3, .p pv2 [pv2,pv13,pv23,pv53,pv59], .c 17, .c 3,
  .p pv3 [pv2,pv7,pv2087], .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv67,pv2791], .c 7, .c 3, .c 193, .c 89, .c 3, .c 17, .c 5, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv5,pv83,pv751], .c 3, .c 5, .c 419, .c 3, .c 7, .c 199, .c 3, .c 29, .c 79,
  .c 3, .c 31, .c 5, .c 3, .p pv2 [pv2,pv19,pv49211], .p pv11 [pv2,pv3,pv5,pv3463], .c 3, .c 5,
  .c 43, .c 3, .c 359, .c 11, .c 3, .c 13, .c 107, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv58439],
  .c 17, .c 3, .c 5, .c 7, .c 3, .c 23, .c 13, .c 3, .p pv2 [pv2,pv11,pv167,pv509], .c 71, .c 3,
  .c 83, .c 5, .c 3, .p pv7 [pv2,pv7,pv223,pv599], .c 191,
]
private theorem h0228c08 : checkBlock 1869827 128 b0228c08 = true := by
  decide +kernel

private def b0228c09 : List Row := [
  .c 3, .c 5, .c 1171, .c 3, .c 37, .c 211, .c 3, .p pv3 [pv2,pv116881], .c 7, .c 3,
  .p pv5 [pv2,pv13,pv17,pv4231], .c 5, .c 3, .c 431, .p pv3 [pv2,pv3,pv5,pv11,pv1889], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv101,pv1543], .c 3, .c 11, .c 29, .c 3, .c 7, .p pv11 [pv2,pv3,pv13,pv37],
  .c 3, .c 41, .c 5, .c 3, .p pv2 [pv2,pv61,pv15329], .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv107,pv971], .c 3, .c 19, .c 17, .c 3, .c 89, .p pv3 [pv2,pv3,pv53,pv5881],
  .c 3, .p pv2 [pv2,pv7,pv133583], .c 5, .c 3, .c 7, .c 67, .c 3, .c 5, .c 47, .c 3, .c 29, .c 7,
  .c 3, .c 11, .c 19, .c 3, .c 13, .c 5, .c 3, .c 23, .c 251, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv23977], .c 3, .c 7, .p pv5 [pv2,pv3,pv155851], .c 3, .c 101, .c 13, .c 3,
  .p pv5 [pv2,pv23,pv109,pv373], .c 5, .c 3, .p pv2 [pv2,pv467557], .c 11, .c 3, .c 5, .c 541,
  .c 3, .c 59, .c 229, .c 3, .p pv5 [pv2,pv7,pv19,pv79,pv89], .p pv7 [pv2,pv3,pv149,pv523], .c 3,
  .c 7, .c 5, .c 3, .p pv2 [pv2,pv13,pv71933], .c 31, .c 3, .c 5, .c 7, .c 3, .c 13, .c 181, .c 3,
  .c 461, .p pv3 [pv2,pv3,pv311713], .c 3, .c 911, .c 5, .c 3, .c 17, .c 23, .c 3, .c 5, .c 11,
  .c 3, .c 223, .c 19, .c 3, .p pv2 [pv2,pv17,pv55009], .c 7, .c 3, .c 37, .c 5, .c 3, .c 11,
  .c 61, .c 3, .c 5, .p pv5 [pv2,pv3,pv29,pv3583], .c 3, .c 109, .c 73, .c 3, .c 7,
]
private theorem h0228c09 : checkBlock 1870083 128 b0228c09 = true := by
  decide +kernel

private def b0228c10 : List Row := [
  .c 1289, .c 3, .p pv5 [pv2,pv709,pv1319], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 17, .c 3,
  .p pv7 [pv2,pv5,pv19,pv23,pv107], .c 11, .c 3, .c 1049, .p pv13 [pv2,pv3,pv19483], .c 3,
  .p pv2 [pv2,pv7,pv67,pv997], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv10391], .c 3, .c 5, .c 37,
  .c 3, .c 17, .c 7, .c 3, .c 149, .p pv11 [pv2,pv3,pv19,pv1823], .c 3, .p pv2 [pv2,pv935201],
  .c 5, .c 3, .c 739, .p pv2 [pv2,pv3,pv5,pv62347], .c 3, .c 5, .c 19, .c 3, .c 7, .c 53, .c 3,
  .c 13, .c 11, .c 3, .p pv3 [pv2,pv58451], .c 5, .c 3, .c 67,
  .p pv7 [pv2,pv3,pv5,pv11,pv13,pv109], .c 3, .c 5, .c 31, .c 3, .c 11, .c 13, .c 3, .c 43, .c 17,
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv467617], .c 29, .c 3, .c 5, .c 7, .c 3, .c 331, .c 79,
  .c 3, .c 643, .c 113, .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv7,pv23,pv37,pv157], .c 457, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv11,pv47,pv67], .c 3, .p pv11 [pv2,pv5,pv17,pv11003], .c 89, .c 3, .c 11,
  .c 7, .c 3, .c 139, .c 5, .c 3, .c 29, .c 13, .c 3, .c 5, .c 691, .c 3,
  .p pv2 [pv2,pv5,pv7,pv31,pv431], .c 41, .c 3, .c 7, .c 109, .c 3, .c 47, .c 5, .c 3, .c 797,
  .c 7, .c 3, .c 5, .c 23, .c 3, .c 31, .c 67, .c 3, .p pv3 [pv2,pv116911], .c 439, .c 3, .c 11,
  .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv23,pv2711], .c 3,
]
private theorem h0228c10 : checkBlock 1870339 128 b0228c10 = true := by
  decide +kernel

private def b0228c11 : List Row := [
  .c 5, .p pv2 [pv2,pv3,pv7,pv13,pv571], .c 3, .p pv7 [pv2,pv5,pv47,pv199], .c 7, .c 3, .c 19,
  .c 13, .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv619,pv1511], .c 101, .c 3, .c 5, .c 11, .c 3,
  .c 7, .c 31, .c 3, .c 71, .p pv7 [pv2,pv3,pv7,pv11,pv4049], .c 3, .p pv2 [pv2,pv241,pv3881],
  .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv4157], .c 3, .c 5, .c 503, .c 3, .c 13, .c 17, .c 3,
  .p pv2 [pv2,pv7,pv41,pv3259], .p pv7 [pv2,pv3,pv17321], .c 3, .c 7, .c 5, .c 3, .c 823, .c 107,
  .c 3, .c 5, .c 7, .c 3, .c 89, .c 11, .c 3, .c 17, .c 787, .c 3, .c 29, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv71,pv941], .p pv3 [pv2,pv3,pv5,pv127,pv491], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv155893], .c 3, .c 19, .p pv3 [pv2,pv3,pv7,pv101], .c 3, .c 1087, .c 7, .c 3,
  .p pv2 [pv2,pv29,pv16127], .c 5, .c 3, .c 13, .c 47, .c 3, .c 5, .c 223, .c 3, .c 23, .c 1129,
  .c 3, .c 7, .c 11, .c 3, .c 1033, .c 5, .c 3, .c 587, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv2887],
  .c 3, .c 11, .p pv3 [pv2,pv3,pv17,pv18341], .c 3, .p pv2 [pv2,pv935393], .c 41, .c 3,
  .p pv5 [pv2,pv7,pv11,pv3037], .c 5, .c 3, .c 7, .c 43, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv44543],
  .c 3, .c 131, .c 7, .c 3, .c 13, .c 29, .c 3, .c 101, .c 5, .c 3, .p pv2 [pv2,pv113,pv4139],
  .c 37, .c 3, .c 5, .c 127, .c 3, .c 7, .c 13, .c 3, .c 11, .c 563,
]
private theorem h0228c11 : checkBlock 1870595 128 b0228c11 = true := by
  decide +kernel

private def b0228c12 : List Row := [
  .c 3, .p pv2 [pv2,pv467713], .c 5, .c 3, .p pv2 [pv2,pv11,pv277,pv307],
  .p pv2 [pv2,pv3,pv5,pv31181], .c 3, .c 5, .c 17, .c 3, .c 41, .c 19, .c 3, .c 29,
  .p pv17 [pv2,pv3,pv79,pv3947], .c 3, .c 7, .c 5, .c 3, .c 23, .c 11, .c 3, .c 5, .c 7, .c 3,
  .c 17, .c 83, .c 3, .p pv2 [pv2,pv29,pv32257], .c 197, .c 3, .c 11, .c 5, .c 3,
  .p pv13 [pv2,pv7,pv17,pv1123], .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv311821], .c 3, .c 61,
  .p pv5 [pv2,pv3,pv7,pv22273], .c 3, .c 211, .c 7, .c 3, .c 31, .c 5, .c 3, .c 19,
  .p pv11 [pv2,pv3,pv5,pv12473], .c 3, .c 5, .c 11, .c 3, .p pv3 [pv2,pv5,pv7,pv13,pv257], .c 557,
  .c 3, .c 7, .c 17, .c 3, .c 13, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 19, .c 3,
  .p pv11 [pv2,pv5,pv11,pv73,pv233], .c 29, .c 3, .c 181, .c 13, .c 3, .c 17, .c 5, .c 3, .c 7,
  .c 1013, .c 3, .c 5, .p pv79 [pv2,pv3,pv7,pv37,pv43], .c 3, .p pv19 [pv2,pv5,pv17,pv5503], .c 7,
  .c 3, .c 23, .p pv7 [pv2,pv3,pv51973], .c 3, .c 97, .c 5, .c 3, .p pv7 [pv2,pv13,pv71963],
  .c 151, .c 3, .c 5, .c 89, .c 3, .c 7, .c 37, .c 3, .p pv3 [pv2,pv11,pv10631], .c 43, .c 3,
  .c 19, .c 5, .c 3, .c 83, .c 17, .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv29,pv1613],
  .p pv5 [pv2,pv3,pv19,pv5471], .c 3, .c 179, .c 11, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv31,pv103,pv293], .c 19, .c 3, .c 5,
]
private theorem h0228c12 : checkBlock 1870851 128 b0228c12 = true := by
  decide +kernel

private def b0228c13 : List Row := [
  .c 7, .c 3, .c 11, .p pv5 [pv2,pv3,pv53,pv1471], .c 3, .c 41, .c 23, .c 3, .c 379, .c 5, .c 3,
  .c 13, .c 239, .c 3, .c 5, .p pv5 [pv2,pv3,pv73,pv89], .c 3, .c 907, .c 331, .c 3,
  .p pv2 [pv2,pv137,pv6829], .c 7, .c 3, .p pv3 [pv2,pv83,pv1409], .c 5, .c 3, .c 229, .c 227,
  .c 3, .c 5, .c 29, .c 3, .p pv2 [pv2,pv5,pv7,pv26731], .c 17, .c 3, .c 7, .c 281, .c 3,
  .p pv5 [pv2,pv935591], .c 5, .c 3, .c 937, .c 7, .c 3, .c 5, .c 199, .c 3, .c 37, .c 109, .c 3,
  .c 13, .c 73, .c 3, .p pv2 [pv2,pv7,pv9547], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 97, .c 3,
  .c 43, .c 7, .c 3, .c 619, .c 1039, .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv116953], .c 317,
  .c 3, .c 5, .c 23, .c 3, .c 7, .p pv3 [pv2,pv3,pv11551], .c 3, .c 1163, .c 467, .c 3, .c 79,
  .c 5, .c 3, .p pv7 [pv2,pv935639], .c 41, .c 3, .c 5, .c 11, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv17,pv9173], .c 3, .c 61, .c 761, .c 3, .c 7, .c 5, .c 3, .c 11, .c 13, .c 3,
  .c 5, .c 7, .c 3, .p pv53 [pv2,pv5,pv11,pv4253], .c 107, .c 3, .p pv5 [pv2,pv17,pv23,pv2393],
  .c 19, .c 3, .c 367, .c 5, .c 3, .p pv7 [pv2,pv7,pv349,pv383], .c 29, .c 3, .c 5, .c 71, .c 3,
  .p pv11 [pv2,pv5,pv13,pv2879], .c 11, .c 3, .c 139, .c 7, .c 3,
]
private theorem h0228c13 : checkBlock 1871107 128 b0228c13 = true := by
  decide +kernel

private def b0228c14 : List Row := [
  .c 13, .c 5, .c 3, .c 997, .c 347, .c 3, .c 5, .c 17, .c 3, .c 607, .p pv3 [pv2,pv3,pv311897],
  .c 3, .c 7, .c 13, .c 3, .c 113, .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .c 103, .c 3, .c 17,
  .p pv7 [pv2,pv3,pv277,pv563], .c 3, .p pv3 [pv2,pv223,pv1049], .c 11, .c 3, .c 37, .c 5, .c 3,
  .c 7, .c 79, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv22279], .c 3, .c 11, .c 7, .c 3,
  .p pv5 [pv2,pv43,pv47,pv463], .p pv7 [pv2,pv3,pv77977], .c 3, .c 479, .c 5, .c 3,
  .p pv2 [pv2,pv397,pv2357], .p pv2 [pv2,pv3,pv5,pv37,pv281], .c 3, .c 5, .c 13, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv127,pv307], .c 3, .p pv2 [pv2,pv467869], .c 17, .c 3, .c 53, .c 5, .c 3,
  .c 43, .p pv3 [pv2,pv3,pv5,pv62383], .c 3, .c 5, .c 37, .c 3, .c 31,
  .p pv17 [pv2,pv3,pv379,pv823], .c 3, .c 11, .p pv7 [pv2,pv3,pv263,pv593], .c 3, .c 7, .c 5,
  .c 3, .c 13, .c 193, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv17,pv101,pv109], .c 23, .c 3,
  .c 107, .c 59, .c 3, .p pv5 [pv2,pv935771], .c 5, .c 3, .p pv2 [pv2,pv7,pv66841], .c 11, .c 3,
  .c 5, .c 19, .c 3, .p pv3 [pv2,pv5,pv71,pv659], .c 31, .c 3, .c 83, .c 7, .c 3, .c 11, .c 5,
  .c 3, .c 23, .c 17, .c 3, .c 5, .c 47, .c 3, .p pv7 [pv2,pv5,pv7,pv26737], .c 509, .c 3, .c 7,
  .c 127, .c 3, .p pv2 [pv2,pv23,pv29,pv61], .c 5, .c 3, .c 41, .c 7, .c 3, .c 5, .c 11,
]
private theorem h0228c14 : checkBlock 1871363 128 b0228c14 = true := by
  decide +kernel

private def b0228c15 : List Row := [
  .c 3, .p pv2 [pv2,pv5,pv93581], .c 13, .c 3, .p pv2 [pv2,pv935813],
  .p pv2 [pv2,pv3,pv11,pv1289], .c 3, .c 19, .c 5, .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv1733], .c 3,
  .c 5, .c 73, .c 3, .p pv2 [pv2,pv5,pv11,pv41,pv83], .c 7, .c 3, .c 59, .c 1213, .c 3, .c 61,
  .c 5, .c 3, .p pv2 [pv2,pv79,pv5923], .c 19, .c 3, .c 5, .p pv5 [pv2,pv3,pv51991], .c 3, .c 7,
  .c 11, .c 3, .c 31, .c 29, .c 3, .p pv2 [pv2,pv491,pv953], .c 5, .c 3,
  .p pv2 [pv2,pv337,pv2777], .c 13, .c 3, .c 5, .c 251, .c 3, .p pv17 [pv2,pv5,pv187171],
  .p pv5 [pv2,pv3,pv67,pv97], .c 3, .c 17, .c 37, .c 3, .c 7, .c 5, .c 3, .c 163, .c 257, .c 3,
  .c 5, .c 7, .c 3, .c 281, .p pv3 [pv2,pv3,pv311957], .c 3, .c 19, .c 11, .c 3, .c 13, .c 5,
  .c 3, .c 89, .c 859, .c 3, .c 5, .c 1229, .c 3, .c 11, .c 41, .c 3, .p pv3 [pv2,pv29,pv2017],
  .c 7, .c 3, .p pv5 [pv2,pv11,pv85081], .c 5, .c 3, .p pv2 [pv2,pv577,pv811], .c 1103, .c 3,
  .c 5, .c 271, .c 3, .c 53, .c 179, .c 3, .c 7, .c 23, .c 3, .p pv2 [pv2,pv467953], .c 5, .c 3,
  .c 17, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv79,pv359], .c 3, .c 13, .c 43, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv103991], .c 3, .p pv5 [pv2,pv7,pv19,pv31,pv227], .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv12479], .c 3, .c 5, .c 13, .c 3, .c 19, .c 7, .c 3, .c 37, .c 47, .c 3,
  .c 31,
]
private theorem h0228c15 : checkBlock 1871619 128 b0228c15 = true := by
  decide +kernel

private def b0228c16 : List Row := [
  .c 5, .c 3, .p pv7 [pv2,pv23,pv40693], .c 11, .c 3, .c 5, .c 17, .c 3, .c 7, .c 59, .c 3,
  .c 1283, .c 19, .c 3, .c 11, .c 5, .c 3, .c 13, .c 157, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv47,pv3319], .c 3, .c 17, .p pv7 [pv2,pv3,pv13,pv103,pv233], .c 3,
  .p pv5 [pv2,pv7,pv133709], .p pv23 [pv2,pv3,pv25999], .c 3, .c 7, .c 5, .c 3, .c 73, .c 37,
  .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv29,pv1291], .c 521, .c 3, .p pv2 [pv2,pv19,pv24631],
  .c 353, .c 3, .c 47, .c 5, .c 3, .c 11, .c 269, .c 3, .c 5, .c 293, .c 3,
  .p pv2 [pv2,pv5,pv11,pv67,pv127], .p pv3 [pv2,pv3,pv7,pv83,pv179], .c 3, .c 13, .c 7, .c 3,
  .c 23, .c 5, .c 3, .c 991, .p pv7 [pv2,pv3,pv5,pv13], .c 3, .c 5, .p pv3 [pv2,pv3,pv17,pv18353],
  .c 3, .c 59, .c 11, .c 3, .c 7, .c 41, .c 3, .c 17, .c 5, .c 3, .c 61, .c 7, .c 3, .c 5, .c 29,
  .c 3, .c 1123, .p pv3 [pv2,pv3,pv312007], .c 3, .c 67, .p pv29 [pv2,pv3,pv43,pv907], .c 3,
  .c 313, .c 5, .c 3, .c 7, .c 757, .c 3, .c 5, .c 367, .c 3, .c 113, .c 7, .c 3, .c 557, .c 11,
  .c 3, .c 181, .c 5, .c 3, .c 19, .c 13, .c 3, .c 5, .p pv5 [pv2,pv3,pv19501], .c 3, .c 7,
  .c 683, .c 3, .c 127, .p pv43 [pv2,pv3,pv7,pv17,pv19,pv23], .c 3, .p pv3 [pv2,pv11,pv967], .c 5,
  .c 3, .c 53, .c 31, .c 3, .c 5, .c 19, .c 3,
]
private theorem h0228c16 : checkBlock 1871875 128 b0228c16 = true := by
  decide +kernel

private def b0228c17 : List Row := [
  .c 23, .c 1259, .c 3, .p pv3 [pv2,pv7,pv101,pv331], .c 1301, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv83,pv5639], .c 47, .c 3, .c 5, .c 7, .c 3, .c 179, .c 37, .c 3, .c 11, .c 13,
  .c 3, .p pv2 [pv2,pv53,pv8831], .c 5, .c 3, .c 107, .c 67, .c 3, .c 5, .c 421, .c 3, .c 139,
  .c 17, .c 3, .c 97, .c 7, .c 3, .c 19, .c 5, .c 3, .c 251, .c 11, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv26003], .c 3, .c 13, .c 23, .c 3, .c 7, .p pv2 [pv2,pv3,pv156019], .c 3,
  .c 11, .c 5, .c 3, .p pv13 [pv2,pv936119], .c 7, .c 3, .c 5, .c 13, .c 3, .c 1249,
  .p pv5 [pv2,pv3,pv131,pv397], .c 3, .c 389, .p pv2 [pv2,pv3,pv312043], .c 3, .c 43, .c 5, .c 3,
  .c 7, .p pv17 [pv2,pv3,pv5,pv71,pv293], .c 3, .c 5, .c 11, .c 3, .p pv7 [pv2,pv5,pv46807], .c 7,
  .c 3, .p pv5 [pv2,pv13,pv107,pv673], .p pv17 [pv2,pv3,pv11,pv197], .c 3, .c 89, .c 5, .c 3,
  .c 11, .p pv2 [pv2,pv3,pv5,pv79], .c 3, .c 5, .c 31, .c 3, .c 7,
  .p pv29 [pv2,pv3,pv13,pv17,pv353], .c 3, .c 19, .p pv3 [pv2,pv3,pv7,pv44579], .c 3,
  .p pv2 [pv2,pv936161], .c 5, .c 3, .c 17, .c 53, .c 3, .c 5, .p pv5 [pv2,pv3,pv19,pv2053], .c 3,
  .c 71, .c 11, .c 3, .c 41, .c 43, .c 3, .c 7, .c 5, .c 3, .c 1201, .c 23, .c 3, .c 5, .c 7,
  .c 3, .c 701, .c 191, .c 3, .c 13, .c 79, .c 3, .c 131, .c 5,
]
private theorem h0228c17 : checkBlock 1872131 128 b0228c17 = true := by
  decide +kernel

private def b0228c18 : List Row := [
  .c 3, .p pv3 [pv2,pv7,pv41,pv233], .c 97, .c 3, .c 5, .c 17, .c 3, .c 541, .c 13, .c 3, .c 23,
  .c 7, .c 3, .c 1223, .c 5, .c 3, .p pv2 [pv2,pv647,pv1447], .p pv2 [pv2,pv3,pv5,pv11,pv2837],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv312071], .c 3, .c 11, .c 47, .c 3, .c 7, .c 101, .c 3, .c 29,
  .c 5, .c 3, .c 67, .c 7, .c 3, .c 5, .c 887, .c 3, .p pv3 [pv2,pv5,pv251,pv373],
  .p pv3 [pv2,pv3,pv31,pv10067], .c 3, .c 331, .c 19, .c 3, .p pv3 [pv2,pv7,pv29,pv1153], .c 5,
  .c 3, .c 7, .c 13, .c 3, .c 5, .c 383, .c 3, .p pv2 [pv2,pv5,pv53,pv3533], .c 7, .c 3, .c 11,
  .c 17, .c 3, .p pv5 [pv2,pv257,pv3643], .c 5, .c 3, .c 269, .c 41, .c 3, .c 5, .c 61, .c 3,
  .c 7, .c 73, .c 3, .c 47, .p pv19 [pv2,pv3,pv7,pv5573], .c 3, .c 13, .c 5, .c 3, .c 157, .c 11,
  .c 3, .c 5, .p pv17 [pv2,pv3,pv13,pv24007], .c 3, .c 151, .p pv5 [pv2,pv3,pv11,pv41,pv173],
  .c 3, .p pv2 [pv2,pv7,pv66877], .c 13, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv23,pv10177],
  .c 167, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv93629], .c 19, .c 3,
  .p pv2 [pv2,pv31,pv30203], .p pv2 [pv2,pv3,pv29,pv5381], .c 3, .c 41, .c 5, .c 3, .c 811, .c 17,
  .c 3, .c 5, .c 11, .c 3, .c 13, .c 661, .c 3, .c 29, .c 7, .c 3, .p pv5 [pv2,pv936311], .c 5,
  .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv20807], .c 3, .c 5, .c 13, .c 3, .c 101,
]
private theorem h0228c18 : checkBlock 1872387 128 b0228c18 = true := by
  decide +kernel

private def b0228c19 : List Row := [
  .c 103, .c 3, .c 7, .c 53, .c 3, .c 137, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv34679], .c 3, .p pv11 [pv2,pv5,pv401,pv467], .c 11, .c 3, .c 1151, .c 31,
  .c 3, .c 23, .c 5, .c 3, .c 7, .p pv23 [pv2,pv3,pv5,pv62423], .c 3, .c 5, .c 19, .c 3, .c 821,
  .c 7, .c 3, .c 163, .c 337, .c 3, .p pv3 [pv2,pv234089], .c 5, .c 3, .c 59,
  .p pv23 [pv2,pv3,pv5,pv17], .c 3, .c 5, .p pv3 [pv2,pv3,pv312121], .c 3, .c 7, .c 29, .c 3,
  .c 17, .c 11, .c 3, .p pv5 [pv2,pv73,pv101,pv127], .c 5, .c 3, .c 113,
  .p pv3 [pv2,pv3,pv5,pv11,pv227], .c 3, .c 5, .c 41, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv29,pv47,pv229], .c 3, .c 13, .p pv7 [pv2,pv3,pv4877], .c 3, .c 7, .c 5, .c 3,
  .c 43, .c 149, .c 3, .c 5, .c 7, .c 3, .c 29, .c 13, .c 3, .c 277,
  .p pv3 [pv2,pv3,pv23,pv41,pv331], .c 3, .c 31, .c 5, .c 3, .c 47, .c 19, .c 3, .c 5,
  .p pv17 [pv2,pv3,pv11,pv3547], .c 3, .c 23, .c 263, .c 3, .c 11, .c 7, .c 3, .c 373, .c 5, .c 3,
  .c 17, .p pv29 [pv2,pv3,pv5,pv15607], .c 3, .c 5, .p pv3 [pv2,pv3,pv104047], .c 3, .c 67, .c 79,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv13,pv1847], .c 3, .c 523, .c 5, .c 3, .c 127, .c 7, .c 3, .c 5,
  .c 179, .c 3, .c 271, .c 61, .c 3, .c 19, .p pv11 [pv2,pv3,pv73,pv1069], .c 3, .c 11, .c 5,
  .c 3,
]
private theorem h0228c19 : checkBlock 1872643 128 b0228c19 = true := by
  decide +kernel

private def b0228c20 : List Row := [
  .c 7, .c 1087, .c 3, .c 5, .c 17, .c 3, .p pv19 [pv2,pv5,pv13,pv14407], .c 7, .c 3, .c 1289,
  .p pv3 [pv2,pv3,pv67,pv1553], .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv107,pv547], .c 1307, .c 3,
  .c 5, .c 11, .c 3, .c 7, .p pv5 [pv2,pv3,pv541,pv577], .c 3, .c 109, .c 13, .c 3,
  .p pv3 [pv2,pv103,pv2273], .c 5, .c 3, .c 11, .c 73, .c 3, .c 5, .c 53, .c 3,
  .p pv2 [pv2,pv5,pv11,pv17027], .c 97, .c 3, .c 37, .c 773, .c 3, .c 7, .c 5, .c 3, .c 31,
  .c 229, .c 3, .c 5, .c 7, .c 3, .c 13, .c 11, .c 3, .c 307, .c 17, .c 3, .p pv2 [pv2,pv468253],
  .c 5, .c 3, .p pv2 [pv2,pv7,pv353,pv379], .p pv2 [pv2,pv3,pv5,pv19,pv31,pv53], .c 3, .c 5,
  .c 13, .c 3, .p pv17 [pv2,pv5,pv187303], .c 163, .c 3, .c 43, .c 7, .c 3, .c 17, .c 5, .c 3,
  .p pv3 [pv2,pv234131], .c 23, .c 3, .c 5, .p pv5 [pv2,pv3,pv109,pv179], .c 3, .c 83, .c 937,
  .c 3, .c 7, .c 11, .c 3, .c 53, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 233, .c 3, .c 11,
  .p pv5 [pv2,pv3,pv13,pv12007], .c 3, .c 23, .p pv2 [pv2,pv3,pv34687], .c 3, .c 743, .c 5, .c 3,
  .c 7, .c 17, .c 3, .c 5, .c 587, .c 3, .p pv3 [pv2,pv5,pv23,pv509], .c 7, .c 3, .c 61, .c 331,
  .c 3, .p pv2 [pv2,pv59,pv7937], .c 5, .c 3, .c 29, .p pv2 [pv2,pv3,pv5,pv31219], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv101,pv281], .c 3, .c 7, .c 19,
]
private theorem h0228c20 : checkBlock 1872899 128 b0228c20 = true := by
  decide +kernel

private def b0228c21 : List Row := [
  .c 3, .c 11, .p pv7 [pv2,pv3,pv7,pv103,pv433], .c 3, .p pv2 [pv2,pv17,pv37,pv1489], .c 5, .c 3,
  .c 79, .p pv2 [pv2,pv3,pv5,pv13,pv1601], .c 3, .c 5, .c 283, .c 3, .p pv2 [pv2,pv5,pv73,pv1283],
  .c 13, .c 3, .c 199, .c 23, .c 3, .c 7, .c 5, .c 3, .c 37, .c 11, .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv19,pv9859], .c 17, .c 3, .p pv3 [pv2,pv29269], .p pv17 [pv2,pv3,pv312203],
  .c 3, .c 11, .c 5, .c 3, .c 19, .p pv3 [pv2,pv3,pv5,pv17,pv3673], .c 3, .c 5, .c 31, .c 3,
  .c 1291, .c 457, .c 3, .c 17, .c 7, .c 3, .c 67, .c 5, .c 3, .c 677, .c 13, .c 3, .c 5, .c 11,
  .c 3, .p pv7 [pv2,pv5,pv7,pv3823], .c 37, .c 3, .c 7, .c 47, .c 3, .p pv2 [pv2,pv239,pv3919],
  .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv13009], .c 3, .c 691, .c 139, .c 3,
  .p pv2 [pv2,pv151,pv6203], .c 59, .c 3, .c 13, .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv67,pv233], .c 3, .c 5, .c 23, .c 3, .c 41, .c 7, .c 3,
  .p pv3 [pv2,pv234167], .c 13, .c 3, .c 19, .c 5, .c 3, .c 17, .c 277, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv107,pv1459], .c 3, .c 7, .c 997, .c 3, .p pv5 [pv2,pv11,pv17,pv5009], .c 479,
  .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv13,pv72053], .c 19, .c 3, .c 5, .c 67, .c 3, .c 13,
  .c 83, .c 3, .c 379, .c 11, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv3659],
]
private theorem h0228c21 : checkBlock 1873155 128 b0228c21 = true := by
  decide +kernel

private def b0228c22 : List Row := [
  .p pv7 [pv2,pv3,pv5,pv7,pv11,pv811], .c 3, .c 5, .c 7, .c 3, .c 11, .c 31, .c 3, .c 59, .c 29,
  .c 3, .p pv3 [pv2,pv11,pv61,pv349], .c 5, .c 3, .c 631, .p pv13 [pv2,pv3,pv5,pv1301], .c 3,
  .c 5, .c 443, .c 3, .c 17, .c 347, .c 3, .c 19, .c 7, .c 3, .c 107, .c 5, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv5,pv197,pv317], .c 3, .c 5, .c 71, .c 3, .c 157, .c 541, .c 3, .c 7, .c 487,
  .c 3, .c 61, .c 5, .c 3, .p pv11 [pv2,pv11,pv85159], .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv312251], .c 3, .c 23, .p pv7 [pv2,pv3,pv26021], .c 3,
  .p pv2 [pv2,pv29,pv31,pv521], .c 17, .c 3, .p pv2 [pv2,pv7,pv163,pv821], .c 5, .c 3, .c 7,
  .c 11, .c 3, .c 5, .c 659, .c 3, .p pv3 [pv2,pv5,pv113,pv829], .c 7, .c 3, .c 13,
  .p pv7 [pv2,pv3,pv71,pv733], .c 3, .c 11, .c 5, .c 3, .c 83, .c 47, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv104087], .c 3, .c 7, .c 13, .c 3, .c 41, .c 373, .c 3,
  .p pv5 [pv2,pv761,pv1231], .c 5, .c 3, .p pv2 [pv2,pv67,pv6991], .c 433, .c 3, .c 5, .c 11,
  .c 3, .c 109, .c 23, .c 3, .p pv5 [pv2,pv7,pv37,pv3617], .c 19, .c 3, .c 7, .c 5, .c 3, .c 11,
  .c 17, .c 3, .c 5, .c 7, .c 3, .c 127, .p pv5 [pv2,pv3,pv29,pv673], .c 3,
  .p pv2 [pv2,pv383,pv1223], .c 43, .c 3, .c 37, .c 5, .c 3, .c 23, .c 13, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv53,pv491], .c 3, .c 29, .c 11, .c 3,
]
private theorem h0228c22 : checkBlock 1873411 128 b0228c22 = true := by
  decide +kernel

private def b0228c23 : List Row := [
  .c 197, .c 7, .c 3, .c 103, .c 5, .c 3, .p pv11 [pv2,pv229,pv4091],
  .p pv7 [pv2,pv3,pv5,pv37,pv211], .c 3, .c 5, .p pv3 [pv2,pv3,pv312281], .c 3, .c 73, .c 131,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv312283], .c 3, .c 13, .c 5, .c 3, .c 53, .c 7, .c 3, .c 5, .c 37,
  .c 3, .p pv3 [pv2,pv5,pv139,pv337], .c 17, .c 3, .p pv5 [pv2,pv883,pv1061], .c 11, .c 3, .c 31,
  .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 797, .c 3, .c 11, .c 7, .c 3, .c 17, .c 151, .c 3,
  .c 173, .c 5, .c 3, .p pv3 [pv2,pv13,pv43,pv419], .p pv2 [pv2,pv3,pv5,pv62459], .c 3, .c 5,
  .c 29, .c 3, .c 7, .p pv3 [pv2,pv3,pv41,pv2539], .c 3, .c 23, .c 67, .c 3, .c 929, .c 5, .c 3,
  .c 19, .c 79, .c 3, .c 5, .c 13, .c 3, .c 43, .c 389, .c 3, .c 11, .c 109, .c 3, .c 7, .c 5,
  .c 3, .c 617, .p pv11 [pv2,pv3,pv5,pv7,pv8923], .c 3, .c 5, .c 7, .c 3, .c 919, .c 47, .c 3,
  .c 787, .p pv7 [pv2,pv3,pv163,pv479], .c 3, .c 101, .c 5, .c 3, .c 13, .c 11, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv312311], .c 3, .c 421, .c 401, .c 3, .p pv2 [pv2,pv17,pv1621], .c 7, .c 3,
  .c 11, .c 5, .c 3, .p pv3 [pv2,pv31,pv1889], .c 83, .c 3, .c 5, .c 43, .c 3, .c 191, .c 71,
  .c 3, .c 7, .c 523, .c 3, .c 19, .c 5, .c 3, .c 31, .c 7,
]
private theorem h0228c23 : checkBlock 1873667 128 b0228c23 = true := by
  decide +kernel

private def b0228c24 : List Row := [
  .c 3, .c 5, .c 11, .c 3, .c 313, .c 1051, .c 3, .c 13, .c 37, .c 3, .c 97, .c 5, .c 3, .c 7,
  .c 19, .c 3, .c 5, .c 1069, .c 3, .c 17, .c 7, .c 3, .p pv5 [pv2,pv251,pv3733],
  .p pv13 [pv2,pv3,pv39041], .c 3, .c 149, .c 5, .c 3, .p pv2 [pv2,pv17,pv55117], .c 31, .c 3,
  .c 5, .c 41, .c 3, .c 7, .c 11, .c 3, .c 1103, .c 239, .c 3, .p pv2 [pv2,pv13,pv72077], .c 5,
  .c 3, .c 29, .c 163, .c 3, .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv93701], .c 137, .c 3, .c 19,
  .c 17, .c 3, .c 7, .c 5, .c 3, .p pv13 [pv2,pv29,pv79,pv409], .c 13, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv37,pv1013], .c 769, .c 3, .c 67, .c 11, .c 3, .c 17, .c 5, .c 3, .c 41,
  .c 467, .c 3, .c 5, .c 353, .c 3, .c 11, .p pv3 [pv2,pv3,pv7,pv44621], .c 3, .c 37, .c 7, .c 3,
  .c 13, .c 5, .c 3, .p pv2 [pv2,pv937049], .p pv2 [pv2,pv3,pv5,pv6247], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv13,pv8009], .c 3, .p pv7 [pv2,pv5,pv7,pv41,pv653], .c 947, .c 3, .c 7, .c 13,
  .c 3, .c 269, .c 5, .c 3, .c 73, .c 7, .c 3, .c 5, .c 97, .c 3, .c 19,
  .p pv3 [pv2,pv3,pv104119], .c 3, .c 11, .c 877, .c 3, .p pv3 [pv2,pv7,pv683], .c 5, .c 3, .c 7,
  .c 37, .c 3, .c 5, .c 31, .c 3, .c 13, .c 7, .c 3, .p pv3 [pv2,pv7321],
]
private theorem h0228c24 : checkBlock 1873923 128 b0228c24 = true := by
  decide +kernel

private def b0228c25 : List Row := [
  .c 19, .c 3, .c 29, .c 5, .c 3, .p pv2 [pv2,pv103,pv4549], .c 11, .c 3, .c 5, .c 13, .c 3, .c 7,
  .c 1193, .c 3, .p pv5 [pv2,pv727,pv1289], .p pv17 [pv2,pv3,pv7,pv2789], .c 3, .c 11, .c 5, .c 3,
  .c 47, .c 811, .c 3, .c 5, .c 563, .c 3, .c 887, .c 17, .c 3, .c 397, .c 53, .c 3, .c 7, .c 5,
  .c 3, .c 13, .c 89, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv31,pv3023],
  .p pv3 [pv2,pv3,pv13,pv24029], .c 3, .c 17, .c 367, .c 3, .c 1187, .c 5, .c 3, .c 11, .c 733,
  .c 3, .c 5, .c 1123, .c 3, .c 31, .c 19, .c 3, .c 137, .c 7, .c 3, .p pv5 [pv2,pv937151], .c 5,
  .c 3, .c 37, .p pv29 [pv2,pv3,pv5,pv62477], .c 3, .c 5, .p pv2 [pv2,pv3,pv23,pv6791], .c 3,
  .c 293, .c 11, .c 3, .c 7, .c 71, .c 3, .c 443, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 61,
  .c 3, .p pv19 [pv2,pv5,pv19,pv1973], .c 13, .c 3, .c 29, .c 647, .c 3, .c 151, .c 5, .c 3, .c 7,
  .c 59, .c 3, .c 5, .p pv19 [pv2,pv3,pv7,pv3719], .c 3, .c 199, .c 7, .c 3,
  .p pv2 [pv2,pv17,pv29,pv1901], .c 11, .c 3, .c 127, .c 5, .c 3, .p pv7 [pv2,pv53,pv17683],
  .c 263, .c 3, .c 5, .c 19, .c 3, .c 7, .c 43, .c 3, .p pv3 [pv2,pv193,pv607], .c 431, .c 3,
  .c 157, .c 5, .c 3, .c 89, .c 13, .c 3,
]
private theorem h0228c25 : checkBlock 1874179 128 b0228c25 = true := by
  decide +kernel

private def b0228c26 : List Row := [
  .c 5, .c 17, .c 3, .p pv3 [pv2,pv5,pv46861], .p pv2 [pv2,pv3,pv312407], .c 3, .c 409,
  .p pv7 [pv2,pv3,pv4339], .c 3, .c 7, .c 5, .c 3, .c 67, .p pv11 [pv2,pv3,pv5,pv7,pv4463], .c 3,
  .c 5, .c 7, .c 3, .c 17, .c 29, .c 3, .c 11, .c 41, .c 3, .c 13, .c 5, .c 3, .c 59,
  .p pv17 [pv2,pv3,pv5,pv62483], .c 3, .c 5, .c 103, .c 3, .c 47, .p pv3 [pv2,pv3,pv7,pv19,pv29],
  .c 3, .c 271, .c 7, .c 3, .p pv3 [pv2,pv79,pv1483], .c 5, .c 3, .c 601, .c 11, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv67,pv4663], .c 3, .c 29, .c 107, .c 3, .c 7, .c 17, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv47,pv59], .c 7, .c 3, .c 5, .c 53, .c 3, .c 13, .c 1049, .c 3, .c 73, .c 23,
  .c 3, .c 17, .c 5, .c 3, .c 7, .c 983, .c 3, .c 5, .c 11, .c 3, .c 61, .c 7, .c 3, .c 19,
  .p pv11 [pv2,pv3,pv11,pv28403], .c 3, .p pv2 [pv2,pv41,pv22861], .c 5, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv5,pv53,pv131], .c 3, .c 5, .c 181, .c 3, .c 7, .p pv3 [pv2,pv3,pv97,pv3221],
  .c 3, .p pv2 [pv2,pv13,pv72101], .p pv17 [pv2,pv3,pv7,pv43,pv173], .c 3,
  .p pv3 [pv2,pv31,pv7559], .c 5, .c 3, .c 13, .c 17, .c 3, .c 5, .c 29, .c 3, .c 1259, .c 11,
  .c 3, .p pv3 [pv2,pv7,pv8369], .p pv2 [pv2,pv3,pv17,pv18379], .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv468667], .c 43, .c 3, .c 5, .c 7, .c 3, .c 503, .c 691, .c 3, .c 463, .c 47,
]
private theorem h0228c26 : checkBlock 1874435 128 b0228c26 = true := by
  decide +kernel

private def b0228c27 : List Row := [
  .c 3, .c 139, .c 5, .c 3, .p pv2 [pv2,pv7,pv359,pv373], .c 631, .c 3, .c 5, .c 23, .c 3, .c 19,
  .c 61, .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv929,pv1009], .c 5, .c 3, .p pv3 [pv2,pv234341],
  .c 337, .c 3, .c 5, .c 157, .c 3, .c 11, .c 13, .c 3, .c 7, .c 19, .c 3, .c 23, .c 5, .c 3,
  .p pv23 [pv2,pv937379], .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv41,pv7621], .c 3, .c 1171, .c 1097,
  .c 3, .c 17, .c 199, .c 3, .c 47, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv37,pv563], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv7,pv11,pv2029], .c 3, .c 173, .c 7, .c 3, .c 11, .c 827, .c 3, .c 1231, .c 5,
  .c 3, .p pv2 [pv2,pv11,pv31,pv2749], .c 13, .c 3, .c 5, .c 37, .c 3, .c 7,
  .p pv19 [pv2,pv3,pv139,pv281], .c 3, .p pv2 [pv2,pv468709], .p pv3 [pv2,pv3,pv7,pv911], .c 3,
  .c 43, .c 5, .c 3, .c 31, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv191,pv409], .c 3, .c 67, .c 19,
  .c 3, .c 149, .p pv2 [pv2,pv3,pv23,pv6793], .c 3, .c 7, .c 5, .c 3, .c 17,
  .p pv13 [pv2,pv3,pv5,pv7,pv31], .c 3, .c 5, .c 7, .c 3, .c 23, .p pv5 [pv2,pv3,pv156241], .c 3,
  .c 71, .c 13, .c 3, .p pv5 [pv2,pv59,pv15889], .c 5, .c 3, .c 103, .c 31, .c 3, .c 5, .c 11,
  .c 3, .p pv3 [pv2,pv5,pv19,pv2467], .p pv3 [pv2,pv3,pv7,pv44641], .c 3, .c 263, .c 7, .c 3,
  .c 727, .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv31249], .c 3, .c 5,
]
private theorem h0228c27 : checkBlock 1874691 128 b0228c27 = true := by
  decide +kernel

private def b0228c28 : List Row := [
  .c 17, .c 3, .c 13, .p pv7 [pv2,pv3,pv26041], .c 3, .c 7, .p pv3 [pv2,pv3,pv19,pv16447], .c 3,
  .c 89, .c 5, .c 3, .c 439, .c 7, .c 3, .c 5, .c 13, .c 3, .c 17, .c 11, .c 3,
  .p pv2 [pv2,pv79,pv11867], .c 163, .c 3, .p pv5 [pv2,pv7,pv16741], .c 5, .c 3, .c 7, .c 971,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv23,pv647], .c 3, .p pv13 [pv2,pv5,pv97,pv1933], .c 7, .c 3,
  .c 1303, .c 311, .c 3, .c 607, .c 5, .c 3, .c 13, .c 397, .c 3, .c 5, .p pv2 [pv2,pv3,pv156253],
  .c 3, .c 7, .p pv2 [pv2,pv3,pv13,pv2671], .c 3, .c 191, .c 11, .c 3, .c 19, .c 5, .c 3,
  .p pv2 [pv2,pv43,pv21803], .p pv2 [pv2,pv3,pv5,pv11,pv947], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv17,pv31,pv593], .c 3, .c 11, .p pv13 [pv2,pv3,pv19,pv257], .c 3,
  .p pv2 [pv2,pv7,pv167,pv401], .c 59, .c 3, .c 7, .c 5, .c 3, .c 757, .c 19, .c 3, .c 5, .c 7,
  .c 3, .c 43, .p pv3 [pv2,pv3,pv312517], .c 3, .c 13, .p pv2 [pv2,pv3,pv156259], .c 3, .c 281,
  .c 5, .c 3, .c 137, .c 23, .c 3, .c 5, .c 109, .c 3, .p pv2 [pv2,pv5,pv187513], .c 13, .c 3,
  .c 11, .c 7, .c 3, .p pv5 [pv2,pv937571], .c 5, .c 3, .p pv2 [pv2,pv11,pv19,pv2243], .c 17,
  .c 3, .c 5, .c 211, .c 3, .p pv3 [pv2,pv5,pv7,pv37,pv181], .p pv2 [pv2,pv3,pv312527], .c 3,
  .c 7, .c 29, .c 3, .p pv2 [pv2,pv13,pv36061], .c 5, .c 3, .p pv2 [pv2,pv937589], .c 7, .c 3,
  .c 5, .c 43, .c 3, .p pv13 [pv2,pv5,pv23,pv31,pv263], .c 53, .c 3, .c 37, .c 269, .c 3,
]
private theorem h0228c28 : checkBlock 1874947 128 b0228c28 = true := by
  decide +kernel

private def b0228c29 : List Row := [
  .c 11, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 41, .c 3, .c 31, .c 7, .c 3, .c 29,
  .p pv2 [pv2,pv3,pv156269], .c 3, .p pv3 [pv2,pv58601], .c 5, .c 3, .p pv7 [pv2,pv191,pv4909],
  .p pv23 [pv2,pv3,pv5,pv5209], .c 3, .c 5, .c 11, .c 3, .c 7, .c 17, .c 3, .c 661, .c 23, .c 3,
  .c 13, .c 5, .c 3, .c 11, .c 37, .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv4007], .c 3, .c 19, .c 31,
  .c 3, .c 17, .c 13, .c 3, .c 7, .c 5, .c 3, .c 41, .c 97, .c 3, .c 5, .c 7, .c 3,
  .p pv11 [pv2,pv5,pv187531], .c 11, .c 3, .p pv2 [pv2,pv43,pv10903], .c 19, .c 3, .c 61, .c 5,
  .c 3, .c 257, .p pv2 [pv2,pv3,pv5,pv67,pv311], .c 3, .c 5, .p pv19 [pv2,pv3,pv78139], .c 3,
  .c 13, .c 29, .c 3, .c 47, .c 7, .c 3, .c 563, .c 5, .c 3, .c 43, .p pv23 [pv2,pv3,pv5,pv3907],
  .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv7,pv73,pv367], .p pv2 [pv2,pv3,pv17,pv29,pv317],
  .c 3, .c 7, .c 11, .c 3, .c 179, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 23, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv43,pv2423], .c 3, .c 31, .c 127, .c 3, .c 941, .c 5, .c 3, .c 7, .c 787, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv7,pv6379], .c 3, .p pv19 [pv2,pv5,pv29,pv223], .c 7, .c 3, .c 487,
  .p pv3 [pv2,pv3,pv31,pv3361], .c 3, .c 23, .c 5, .c 3, .p pv3 [pv2,pv234431],
  .p pv3 [pv2,pv3,pv5,pv12503], .c 3, .c 5, .c 17,
]
private theorem h0228c29 : checkBlock 1875203 128 b0228c29 = true := by
  decide +kernel

private def b0228c30 : List Row := [
  .c 3, .c 7, .c 41, .c 3, .c 11, .c 31, .c 3, .c 449, .c 5, .c 3, .p pv7 [pv2,pv11,pv163,pv523],
  .p pv7 [pv2,pv3,pv5,pv15629], .c 3, .c 5, .p pv5 [pv2,pv3,pv312581], .c 3, .c 17, .c 37, .c 3,
  .c 13, .p pv2 [pv2,pv3,pv312583], .c 3, .c 7, .c 5, .c 3, .c 19, .c 11, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv5861], .c 13, .c 3, .c 103, .p pv7 [pv2,pv3,pv19,pv457], .c 3, .c 11, .c 5,
  .c 3, .c 79, .p pv2 [pv2,pv3,pv5,pv31259], .c 3, .c 5, .c 19, .c 3, .c 59,
  .p pv5 [pv2,pv3,pv7,pv2791], .c 3, .p pv2 [pv2,pv468889], .c 7, .c 3, .c 109, .c 5, .c 3,
  .p pv3 [pv2,pv117223], .c 151, .c 3, .c 5, .c 11, .c 3, .c 23, .p pv3 [pv2,pv3,pv47,pv739],
  .c 3, .c 7, .c 73, .c 3, .c 17, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 71, .c 3,
  .p pv2 [pv2,pv5,pv11,pv17,pv59], .c 463, .c 3, .c 43, .p pv2 [pv2,pv3,pv79,pv1319], .c 3, .c 19,
  .c 5, .c 3, .c 7, .c 643, .c 3, .c 5, .c 197, .c 3, .c 37, .c 7, .c 3, .c 541, .c 881, .c 3,
  .c 13, .c 5, .c 3, .c 593, .c 17, .c 3, .c 5, .c 137, .c 3, .c 7, .c 23, .c 3,
  .p pv2 [pv2,pv11,pv47,pv907], .c 13, .c 3, .p pv2 [pv2,pv937841], .c 5, .c 3, .c 61, .c 29,
  .c 3, .c 5, .c 79, .c 3, .c 227, .c 43, .c 3, .p pv2 [pv2,pv7,pv133979], .c 11, .c 3, .c 7,
]
private theorem h0228c30 : checkBlock 1875459 128 b0228c30 = true := by
  decide +kernel

private def b0228c31 : List Row := [
  .c 5, .c 3, .c 23, .c 601, .c 3, .c 5, .c 7, .c 3, .c 11, .c 103, .c 3, .c 19, .c 229, .c 3,
  .p pv5 [pv2,pv11,pv23,pv337], .c 5, .c 3, .c 29, .p pv3 [pv2,pv3,pv5,pv41,pv61], .c 3, .c 5,
  .c 13, .c 3, .c 149, .c 17, .c 3, .c 193, .c 7, .c 3, .p pv2 [pv2,pv101,pv4643], .c 5, .c 3,
  .c 31, .c 109, .c 3, .c 5, .c 59, .c 3, .c 41, .p pv5 [pv2,pv3,pv39079], .c 3, .c 7, .c 67,
  .c 3, .p pv2 [pv2,pv937901], .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 47, .c 3,
  .p pv2 [pv2,pv5,pv71,pv1321], .c 1291, .c 3, .c 577, .c 53, .c 3,
  .p pv3 [pv2,pv7,pv19,pv41,pv43], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 439, .c 3, .c 19, .c 7,
  .c 3, .c 23, .p pv2 [pv2,pv3,pv312643], .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv468967], .c 719,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv223,pv701], .c 3, .c 7, .c 83, .c 3, .c 13, .c 19, .c 3,
  .p pv2 [pv2,pv468973], .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv13,pv37], .c 3, .c 5, .c 11,
  .c 3, .c 47, .c 13, .c 3, .c 127, .c 1163, .c 3, .c 7, .c 5, .c 3, .c 11, .c 1153, .c 3, .c 5,
  .c 7, .c 3, .c 137, .p pv3 [pv2,pv3,pv89,pv1171], .c 3, .p pv2 [pv2,pv19,pv49367], .c 23, .c 3,
  .p pv3 [pv2,pv13,pv29,pv311], .c 5, .c 3, .p pv7 [pv2,pv7,pv47,pv2851], .c 43, .c 3, .c 5,
  .c 17, .c 3,
]
private theorem h0228c31 : checkBlock 1875715 128 b0228c31 = true := by
  decide +kernel

def rows0228 : List Row :=
  b0228c00 ++ b0228c01 ++ b0228c02 ++ b0228c03 ++ b0228c04 ++ b0228c05 ++ b0228c06 ++ b0228c07 ++
  b0228c08 ++ b0228c09 ++ b0228c10 ++ b0228c11 ++ b0228c12 ++ b0228c13 ++ b0228c14 ++ b0228c15 ++
  b0228c16 ++ b0228c17 ++ b0228c18 ++ b0228c19 ++ b0228c20 ++ b0228c21 ++ b0228c22 ++ b0228c23 ++
  b0228c24 ++ b0228c25 ++ b0228c26 ++ b0228c27 ++ b0228c28 ++ b0228c29 ++ b0228c30 ++ b0228c31

attribute [local irreducible] checkBlock checkRows checkPrime

theorem checked0228 : checkBlock 1867779 4096 rows0228 = true :=
  checkBlock_append h0228c00 (
    checkBlock_append h0228c01 (
    checkBlock_append h0228c02 (
    checkBlock_append h0228c03 (
    checkBlock_append h0228c04 (
    checkBlock_append h0228c05 (
    checkBlock_append h0228c06 (
    checkBlock_append h0228c07 (
    checkBlock_append h0228c08 (
    checkBlock_append h0228c09 (
    checkBlock_append h0228c10 (
    checkBlock_append h0228c11 (
    checkBlock_append h0228c12 (
    checkBlock_append h0228c13 (
    checkBlock_append h0228c14 (
    checkBlock_append h0228c15 (
    checkBlock_append h0228c16 (
    checkBlock_append h0228c17 (
    checkBlock_append h0228c18 (
    checkBlock_append h0228c19 (
    checkBlock_append h0228c20 (
    checkBlock_append h0228c21 (
    checkBlock_append h0228c22 (
    checkBlock_append h0228c23 (
    checkBlock_append h0228c24 (
    checkBlock_append h0228c25 (
    checkBlock_append h0228c26 (
    checkBlock_append h0228c27 (
    checkBlock_append h0228c28 (
    checkBlock_append h0228c29 (
    checkBlock_append h0228c30 (
    h0228c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
