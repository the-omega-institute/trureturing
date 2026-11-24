/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks04/Block0386
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks04/Block0386.checked0386
   digest: Kernel proof of checker success on consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table029
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table035
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table039
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table044
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table051
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table059
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table071
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table087
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table088
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table113
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table152

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0386c00 : List Row := [
  .c 5, .c 3, .c 17, .c 599, .c 3, .c 5, .c 71, .c 3, .c 7, .c 13, .c 3, .c 11, .c 53, .c 3,
  .p pv5 [pv2,pv1581071], .c 5, .c 3, .p pv2 [pv2,pv11,pv71867], .c 19, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv263513], .c 3, .c 241, .c 499, .c 3, .p pv5 [pv2,pv7,pv41,pv787], .c 587,
  .c 3, .c 7, .c 5, .c 3, .c 61, .c 11, .c 3, .c 5, .c 7, .c 3, .c 839, .c 419, .c 3, .c 1163,
  .c 67, .c 3, .c 11, .c 5, .c 3, .c 101, .c 13, .c 3, .c 5, .c 31, .c 3, .c 17, .c 59, .c 3,
  .c 19, .c 7, .c 3, .c 1201, .c 5, .c 3, .c 313, .c 1327, .c 3, .c 5, .c 11, .c 3, .c 181,
  .p pv7 [pv2,pv3,pv263521], .c 3, .c 7, .c 89, .c 3, .c 13, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv13,pv29,pv233], .c 3, .c 991, .p pv3 [pv2,pv3,pv59,pv8933], .c 3, .c 73,
  .c 13, .c 3, .c 23, .c 5, .c 3, .c 7, .c 47, .c 3, .c 5, .c 449, .c 3, .c 983, .c 7, .c 3,
  .p pv2 [pv2,pv23,pv37,pv929], .p pv3 [pv2,pv3,pv527053], .c 3, .c 17, .c 5, .c 3, .c 1129,
  .p pv2 [pv2,pv3,pv5,pv41,pv857], .c 3, .c 5, .c 227, .c 3, .c 7, .c 773, .c 3,
  .p pv2 [pv2,pv11,pv143743], .c 43, .c 3, .c 37, .c 5, .c 3, .p pv7 [pv2,pv479,pv3301], .c 503,
  .c 3, .c 5, .c 13, .c 3,
]
private theorem h0386c00 : checkBlock 3162115 128 b0386c00 = true := by
  decide +kernel

private def b0386c01 : List Row := [
  .c 41, .p pv2 [pv2,pv3,pv31,pv8501], .c 3, .c 1429, .c 11, .c 3, .c 7, .c 5, .c 3, .c 139,
  .c 17, .c 3, .c 5, .c 7, .c 3, .c 11, .c 31, .c 3, .c 307, .c 103, .c 3,
  .p pv2 [pv2,pv11,pv41,pv1753], .c 5, .c 3, .c 13, .c 29, .c 3, .c 5, .c 37, .c 3, .c 23, .c 73,
  .c 3, .c 89, .c 7, .c 3, .p pv2 [pv2,pv17,pv47,pv1979], .c 5, .c 3, .c 79, .c 157, .c 3, .c 5,
  .c 53, .c 3, .c 751, .p pv3 [pv2,pv3,pv601,pv877], .c 3, .c 7, .c 593, .c 3,
  .p pv3 [pv2,pv395309], .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .p pv11 [pv2,pv3,pv527081], .c 3,
  .c 97, .c 17, .c 3, .c 13, .p pv2 [pv2,pv3,pv193,pv2731], .c 3, .p pv5 [pv2,pv7,pv397,pv569],
  .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv37649], .c 3, .c 43, .c 7, .c 3,
  .c 17, .p pv13 [pv2,pv3,pv79,pv139], .c 3, .c 11, .c 5, .c 3, .p pv2 [pv2,pv37,pv42737], .c 659,
  .c 3, .c 5, .c 971, .c 3, .c 7, .c 71, .c 3, .p pv2 [pv2,pv439,pv1801], .c 311, .c 3, .c 53,
  .c 5, .c 3, .c 19, .c 1621, .c 3, .c 5, .c 11, .c 3, .c 523, .c 47, .c 3,
  .p pv2 [pv2,pv7,pv223,pv1013], .c 31, .c 3, .c 7, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 7,
  .c 3, .p pv2 [pv2,pv5,pv11,pv28751], .c 101, .c 3, .c 41, .p pv2 [pv2,pv3,pv58567], .c 3,
  .p pv5 [pv2,pv1581311], .c 5,
]
private theorem h0386c01 : checkBlock 3162371 128 b0386c01 = true := by
  decide +kernel

private def b0386c02 : List Row := [
  .c 3, .c 17, .c 1433, .c 3, .c 5, .p pv23 [pv2,pv3,pv59,pv1489], .c 3,
  .p pv3 [pv2,pv5,pv13,pv3041], .c 11, .c 3, .p pv5 [pv2,pv17,pv167,pv557], .c 7, .c 3, .c 13,
  .c 5, .c 3, .p pv2 [pv2,pv41,pv38569], .c 23, .c 3, .c 5, .c 61, .c 3,
  .p pv13 [pv2,pv5,pv7,pv45181], .p pv5 [pv2,pv3,pv7321], .c 3, .c 7, .c 13, .c 3, .c 19, .c 5,
  .c 3, .c 163, .c 7, .c 3, .c 5, .c 17, .c 3, .c 941, .p pv5 [pv2,pv3,pv19,pv27743], .c 3, .c 23,
  .c 11, .c 3, .c 31, .c 5, .c 3, .c 7, .c 19, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv2789], .c 3,
  .c 11, .c 7, .c 3, .c 1579, .p pv3 [pv2,pv3,pv527123], .c 3, .p pv5 [pv2,pv11,pv233,pv617],
  .c 5, .c 3, .p pv2 [pv2,pv17,pv46511], .c 179, .c 3, .c 5, .c 13, .c 3, .c 7,
  .p pv7 [pv2,pv3,pv175709], .c 3, .p pv5 [pv2,pv71,pv22273], .c 29, .c 3, .p pv2 [pv2,pv790693],
  .c 5, .c 3, .c 43, .c 41, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv173,pv277], .c 3, .c 227, .c 89,
  .c 3, .c 11, .c 17, .c 3, .c 7, .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv7,pv15061], .c 3, .c 5,
  .c 7, .c 3, .c 103, .c 149, .c 3, .c 29, .p pv11 [pv2,pv3,pv53,pv4973], .c 3, .c 17, .c 5, .c 3,
  .p pv17 [pv2,pv7,pv263,pv859], .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv151,pv3491], .c 3, .c 251,
  .c 109, .c 3, .p pv3 [pv2,pv29,pv13633], .c 7, .c 3, .c 11, .c 5, .c 3, .c 67, .c 37, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv263573], .c 3, .c 53,
]
private theorem h0386c02 : checkBlock 3162627 128 b0386c02 = true := by
  decide +kernel

private def b0386c03 : List Row := [
  .p pv2 [pv2,pv3,pv89,pv5923], .c 3, .c 7, .p pv13 [pv2,pv3,pv1627], .c 3,
  .p pv3 [pv2,pv19,pv41617], .c 5, .c 3, .c 31, .c 7, .c 3, .c 5, .c 11, .c 3, .c 19, .c 13, .c 3,
  .c 643, .c 137, .c 3, .c 79, .c 5, .c 3, .c 7, .c 59, .c 3, .c 5, .c 23, .c 3,
  .p pv2 [pv2,pv5,pv11,pv1307], .c 7, .c 3, .p pv2 [pv2,pv1581473], .c 19, .c 3, .c 787, .c 5,
  .c 3, .c 47, .c 31, .c 3, .c 5, .c 1279, .c 3, .c 7, .c 11, .c 3, .p pv3 [pv2,pv97,pv1019],
  .c 71, .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv790747], .c 13, .c 3, .c 5, .c 151, .c 3, .c 29,
  .c 17, .c 3, .c 953, .c 1237, .c 3, .c 7, .c 5, .c 3, .c 37, .c 307, .c 3, .c 5, .c 7, .c 3,
  .c 419, .c 61, .c 3, .c 17, .c 11, .c 3, .c 13, .c 5, .c 3, .c 59,
  .p pv13 [pv2,pv3,pv5,pv11,pv71], .c 3, .c 5, .c 967, .c 3, .c 11, .c 19, .c 3,
  .p pv2 [pv2,pv1581533], .c 7, .c 3, .c 97, .c 5, .c 3, .c 157, .c 79, .c 3, .c 5,
  .p pv11 [pv2,pv3,pv175727], .c 3, .c 283, .c 37, .c 3, .c 7, .p pv7 [pv2,pv3,pv23,pv22921],
  .c 3, .p pv5 [pv2,pv251,pv6301], .c 5, .c 3, .c 41, .c 7, .c 3, .c 5, .c 29, .c 3, .c 13, .c 43,
  .c 3, .c 11, .c 1277, .c 3, .p pv2 [pv2,pv7,pv173,pv653], .c 5, .c 3,
]
private theorem h0386c03 : checkBlock 3162883 128 b0386c03 = true := by
  decide +kernel

private def b0386c04 : List Row := [
  .c 7, .p pv13 [pv2,pv3,pv5,pv17573], .c 3, .c 5, .c 13, .c 3, .c 191, .c 7, .c 3,
  .p pv2 [pv2,pv17,pv181,pv257], .p pv3 [pv2,pv3,pv19,pv3083], .c 3, .c 73, .c 5, .c 3,
  .p pv3 [pv2,pv98849], .c 11, .c 3, .c 5, .c 19, .c 3, .c 7, .c 647, .c 3, .c 857, .c 127, .c 3,
  .c 11, .c 5, .c 3, .c 13, .p pv13 [pv2,pv3,pv5,pv659], .c 3, .c 5, .c 17, .c 3, .c 1559, .c 23,
  .c 3, .c 281, .c 101, .c 3, .c 7, .c 5, .c 3, .c 197, .p pv11 [pv2,pv3,pv5,pv7,pv5021], .c 3,
  .c 5, .c 7, .c 3, .c 17, .p pv2 [pv2,pv3,pv527207], .c 3, .p pv5 [pv2,pv1581623],
  .p pv7 [pv2,pv3,pv11,pv1997], .c 3, .c 19, .c 5, .c 3, .c 11, .p pv11 [pv2,pv3,pv5,pv52721],
  .c 3, .c 5, .c 97, .c 3, .c 31, .c 41, .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv23,pv68767], .c 5,
  .c 3, .c 109, .c 19, .c 3, .c 5, .p pv5 [pv2,pv3,pv83,pv397], .c 3, .c 547, .c 11, .c 3, .c 7,
  .c 17, .c 3, .c 821, .c 5, .c 3, .c 599, .c 7, .c 3, .c 5, .c 89, .c 3,
  .p pv2 [pv2,pv5,pv137,pv2309], .c 31, .c 3, .c 181, .c 877, .c 3, .c 17, .c 5, .c 3, .c 7,
  .c 23, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv12553], .c 3, .p pv3 [pv2,pv5,pv17,pv1163], .c 7, .c 3,
  .c 19, .c 11, .c 3, .p pv2 [pv2,pv790843], .c 5, .c 3, .c 83, .c 13, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv19,pv27749], .c 3, .c 7, .c 157,
]
private theorem h0386c04 : checkBlock 3163139 128 b0386c04 = true := by
  decide +kernel

private def b0386c05 : List Row := [
  .c 3, .c 23, .c 61, .c 3, .c 59, .c 5, .c 3, .p pv3 [pv2,pv197713], .c 17, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv89,pv1481], .c 3, .c 101, .p pv3 [pv2,pv3,pv527237], .c 3,
  .p pv5 [pv2,pv7,pv31,pv37,pv197], .c 47, .c 3, .c 7, .c 5, .c 3, .c 103, .c 233, .c 3, .c 5,
  .c 7, .c 3, .p pv2 [pv2,pv5,pv151,pv419], .p pv2 [pv2,pv3,pv263621], .c 3, .c 11, .c 13, .c 3,
  .c 37, .c 5, .c 3, .p pv2 [pv2,pv7,pv11,pv10271], .p pv31 [pv2,pv3,pv5,pv105449], .c 3, .c 5,
  .c 761, .c 3, .c 19, .p pv2 [pv2,pv3,pv7,pv8369], .c 3, .p pv5 [pv2,pv1581743], .c 7, .c 3,
  .p pv2 [pv2,pv311,pv2543], .c 5, .c 3, .p pv2 [pv2,pv13,pv281,pv433], .c 11, .c 3, .c 5, .c 109,
  .c 3, .c 13, .c 17, .c 3, .c 7, .c 19, .c 3, .c 11, .c 5, .c 3, .p pv3 [pv2,pv73,pv5417], .c 7,
  .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv367,pv431], .p pv11 [pv2,pv3,pv103,pv5119], .c 3,
  .c 17, .p pv23 [pv2,pv3,pv113,pv2333], .c 3, .c 43, .c 5, .c 3, .c 7,
  .p pv31 [pv2,pv3,pv5,pv41,pv643], .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv47,pv53,pv127],
  .c 7, .c 3, .p pv3 [pv2,pv13,pv19,pv1601], .p pv3 [pv2,pv3,pv11,pv47933], .c 3,
  .p pv5 [pv2,pv61,pv25931], .c 5, .c 3, .c 11, .p pv3 [pv2,pv3,pv5,pv11717], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv43,pv6131], .c 3, .c 7, .p pv2 [pv2,pv3,pv13,pv40559], .c 3, .c 241,
  .p pv13 [pv2,pv3,pv7,pv6277], .c 3, .c 701, .c 5, .c 3, .p pv2 [pv2,pv71,pv22279], .c 677, .c 3,
  .c 5, .c 23, .c 3, .p pv7 [pv2,pv5,pv316363], .c 11, .c 3, .p pv2 [pv2,pv7,pv16141], .c 29,
  .c 3, .c 7, .c 5, .c 3, .c 17,
]
private theorem h0386c05 : checkBlock 3163395 128 b0386c05 = true := by
  decide +kernel

private def b0386c06 : List Row := [
  .c 173, .c 3, .c 5, .c 7, .c 3, .c 113, .p pv3 [pv2,pv3,pv175759], .c 3, .c 13, .c 107, .c 3,
  .c 23, .c 5, .c 3, .c 463, .p pv7 [pv2,pv3,pv5,pv13], .c 3, .c 5, .p pv7 [pv2,pv3,pv527281],
  .c 3, .c 577, .c 13, .c 3, .c 29, .c 7, .c 3, .p pv5 [pv2,pv199,pv7949], .c 5, .c 3, .c 19,
  .c 47, .c 3, .c 5, .c 17, .c 3, .c 11, .p pv2 [pv2,pv3,pv37,pv14251], .c 3, .c 7, .c 53, .c 3,
  .p pv2 [pv2,pv11,pv13,pv5531], .c 5, .c 3, .p pv2 [pv2,pv1581869], .c 7, .c 3, .c 5, .c 19,
  .c 3, .c 17, .p pv5 [pv2,pv3,pv97,pv151], .c 3, .c 59, .c 37, .c 3, .p pv2 [pv2,pv7,pv225983],
  .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 853, .c 3, .c 131, .c 7, .c 3, .c 11, .c 883, .c 3,
  .p pv3 [pv2,pv79,pv2503], .c 5, .c 3, .p pv7 [pv2,pv11,pv31,pv4639],
  .p pv29 [pv2,pv3,pv5,pv5273], .c 3, .c 5, .c 67, .c 3, .c 7, .c 29, .c 3, .c 1747, .c 17, .c 3,
  .c 13, .c 5, .c 3, .c 31, .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv13,pv17,pv1193], .c 3,
  .p pv3 [pv2,pv5,pv9887], .c 461, .c 3, .c 41, .c 13, .c 3, .c 7, .c 5, .c 3, .c 659, .c 19,
  .c 3, .c 5, .c 7, .c 3, .c 29, .c 439, .c 3, .c 83, .p pv3 [pv2,pv3,pv137,pv1283], .c 3, .c 107,
  .c 5, .c 3, .c 773, .c 31, .c 3, .c 5, .c 11, .c 3, .c 13, .c 23, .c 3,
]
private theorem h0386c06 : checkBlock 3163651 128 b0386c06 = true := by
  decide +kernel

private def b0386c07 : List Row := [
  .c 37, .c 7, .c 3, .p pv3 [pv2,pv131,pv3019], .c 5, .c 3, .c 11, .c 17, .c 3, .c 5, .c 13, .c 3,
  .c 433, .p pv2 [pv2,pv3,pv87887], .c 3, .c 7, .c 353, .c 3, .c 109, .c 5, .c 3, .c 23, .c 7,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv19,pv13877], .c 3, .p pv3 [pv2,pv5,pv83,pv953], .c 11, .c 3,
  .p pv5 [pv2,pv13,pv73,pv1667], .p pv19 [pv2,pv3,pv1831], .c 3, .c 71, .c 5, .c 3, .c 7, .c 37,
  .c 3, .c 5, .c 29, .c 3, .p pv19 [pv2,pv5,pv107,pv2957], .c 7, .c 3, .c 173, .c 809, .c 3,
  .p pv2 [pv2,pv1582001], .c 5, .c 3, .c 61, .c 41, .c 3, .c 5, .c 197, .c 3, .c 7, .c 17, .c 3,
  .c 101, .c 11, .c 3, .c 521, .c 5, .c 3, .c 73, .c 23, .c 3, .c 5, .c 53, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv41,pv59,pv109], .c 3, .c 13, .p pv2 [pv2,pv3,pv175781], .c 3, .c 7, .c 5,
  .c 3, .c 43, .p pv11 [pv2,pv3,pv5,pv7,pv13,pv19,pv61], .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv39551], .c 13, .c 3, .c 23, .c 19, .c 3, .c 41, .c 5, .c 3, .c 1151,
  .p pv7 [pv2,pv3,pv5,pv53,pv199], .c 3, .c 5, .c 293, .c 3, .c 59, .c 113, .c 3, .c 11, .c 7,
  .c 3, .p pv2 [pv2,pv13,pv121697], .c 5, .c 3, .c 37, .c 61, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv131839], .c 3, .p pv2 [pv2,pv5,pv7,pv97,pv233],
  .p pv5 [pv2,pv3,pv17,pv67,pv463], .c 3, .c 7, .c 167, .c 3, .c 53, .c 5, .c 3, .c 17, .c 7,
]
private theorem h0386c07 : checkBlock 3163907 128 b0386c07 = true := by
  decide +kernel

private def b0386c08 : List Row := [
  .c 3, .c 5, .p pv31 [pv2,pv3,pv37,pv4751], .c 3, .c 277, .p pv2 [pv2,pv3,pv11,pv23971], .c 3,
  .p pv3 [pv2,pv17,pv11633], .c 23, .c 3, .c 11, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv29,pv3637], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv139,pv271], .c 3, .c 31,
  .c 7, .c 3, .c 661, .c 67, .c 3, .c 13, .c 5, .c 3, .c 29, .p pv29 [pv2,pv3,pv5,pv17579], .c 3,
  .c 5, .c 11, .c 3, .c 7, .p pv5 [pv2,pv3,pv31,pv4253], .c 3, .c 97, .c 13, .c 3,
  .p pv2 [pv2,pv181,pv8741], .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv4219], .c 3, .c 5, .c 41,
  .c 3, .c 17, .c 31, .c 3, .c 709, .p pv7 [pv2,pv3,pv457,pv577], .c 3, .c 7, .c 5, .c 3, .c 19,
  .c 1319, .c 3, .c 5, .c 7, .c 3, .c 13, .c 11, .c 3, .c 191, .c 199, .c 3,
  .p pv5 [pv2,pv1582151], .c 5, .c 3, .c 541, .c 107, .c 3, .c 5, .c 13, .c 3, .c 1637,
  .p pv3 [pv2,pv3,pv7,pv47,pv229], .c 3, .c 43, .c 7, .c 3, .p pv2 [pv2,pv127,pv6229], .c 5, .c 3,
  .c 41, .c 281, .c 3, .c 5, .c 59, .c 3, .c 37, .p pv5 [pv2,pv3,pv16481], .c 3, .c 7, .c 11,
  .c 3, .c 17, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv131849], .c 3, .c 11,
  .c 349, .c 3, .c 31, .c 1499, .c 3, .c 19, .c 5, .c 3, .c 7, .p pv19 [pv2,pv3,pv5,pv293], .c 3,
  .c 5, .p pv7 [pv2,pv3,pv7,pv59,pv1277], .c 3, .c 197, .c 7, .c 3, .c 1583,
]
private theorem h0386c08 : checkBlock 3164163 128 b0386c08 = true := by
  decide +kernel

private def b0386c09 : List Row := [
  .p pv2 [pv2,pv3,pv31,pv53,pv107], .c 3, .c 181, .c 5, .c 3, .p pv2 [pv2,pv193,pv4099], .c 17,
  .c 3, .c 5, .c 743, .c 3, .c 7, .p pv2 [pv2,pv3,pv527407], .c 3, .c 11, .c 31, .c 3, .c 509,
  .c 5, .c 3, .c 127, .c 1117, .c 3, .c 5, .c 271, .c 3, .c 53, .c 13, .c 3, .c 67,
  .p pv3 [pv2,pv3,pv23,pv997], .c 3, .c 7, .c 5, .c 3, .c 971, .c 11, .c 3, .c 5, .c 7, .c 3,
  .c 23, .c 41, .c 3, .c 19, .c 29, .c 3, .c 11, .c 5, .c 3, .p pv13 [pv2,pv7,pv659],
  .p pv7 [pv2,pv3,pv5,pv26371], .c 3, .c 5, .c 787, .c 3, .p pv2 [pv2,pv5,pv316453], .c 17, .c 3,
  .p pv3 [pv2,pv37,pv10691], .c 7, .c 3, .p pv5 [pv2,pv31,pv43,pv1187], .c 5, .c 3,
  .p pv2 [pv2,pv791137], .c 13, .c 3, .c 5, .c 11, .c 3, .c 1051, .c 137, .c 3, .c 7,
  .p pv13 [pv2,pv3,pv11,pv11987], .c 3, .c 31, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 1129, .c 3,
  .p pv11 [pv2,pv5,pv11,pv13,pv2213], .c 23, .c 3, .c 109, .c 239, .c 3, .c 13, .c 5, .c 3, .c 7,
  .c 67, .c 3, .c 5, .c 641, .c 3, .c 19, .c 7, .c 3, .p pv2 [pv2,pv41,pv38593], .c 13, .c 3,
  .c 101, .c 5, .c 3, .c 23, .c 367, .c 3, .c 5, .c 37, .c 3, .c 7, .p pv19 [pv2,pv3,pv17,pv5171],
  .c 3, .c 421, .c 19, .c 3, .p pv5 [pv2,pv23,pv89,pv773], .c 5, .c 3, .c 17, .c 43, .c 3,
]
private theorem h0386c09 : checkBlock 3164419 128 b0386c09 = true := by
  decide +kernel

private def b0386c10 : List Row := [
  .c 5, .p pv5 [pv2,pv3,pv263723], .c 3, .c 13, .c 29, .c 3, .p pv5 [pv2,pv7,pv17,pv13297], .c 11,
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv47,pv131,pv257], .c 59, .c 3, .c 5, .c 7, .c 3, .c 11,
  .c 127, .c 3, .c 1213, .p pv37 [pv2,pv3,pv527453], .c 3, .p pv2 [pv2,pv11,pv97,pv1483], .c 5,
  .c 3, .c 383, .c 23, .c 3, .c 5, .c 17, .c 3, .c 29, .c 313, .c 3, .p pv2 [pv2,pv13,pv121721],
  .c 7, .c 3, .c 479, .c 5, .c 3, .c 13, .p pv11 [pv2,pv3,pv5,pv59,pv149], .c 3, .c 5, .c 337,
  .c 3, .c 17, .c 19, .c 3, .c 7, .p pv3 [pv2,pv3,pv103,pv569], .c 3, .p pv5 [pv2,pv1582391],
  .c 5, .c 3, .c 53, .c 7, .c 3, .c 5, .c 433, .c 3, .p pv3 [pv2,pv5,pv23,pv43],
  .p pv2 [pv2,pv3,pv61,pv8647], .c 3, .p pv5 [pv2,pv157,pv10079], .c 151, .c 3,
  .p pv2 [pv2,pv7,pv67,pv241], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .p pv7 [pv2,pv3,pv7,pv75353],
  .c 3, .c 41, .c 7, .c 3, .c 13, .c 17, .c 3, .c 11, .c 5, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv5,pv13,pv541], .c 3, .c 5, .c 29, .c 3, .c 7, .c 13, .c 3,
  .p pv2 [pv2,pv601,pv2633], .c 23, .c 3, .c 17, .c 5, .c 3, .c 67, .c 103, .c 3, .c 5, .c 11,
  .c 3, .c 139, .p pv5 [pv2,pv3,pv23,pv11467], .c 3, .c 1481, .c 179, .c 3, .c 7, .c 5, .c 3,
  .c 11, .p pv3 [pv2,pv3,pv5,pv7,pv2153], .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv11,pv7193],
  .p pv2 [pv2,pv3,pv175829], .c 3, .p pv5 [pv2,pv1582463], .c 43,
]
private theorem h0386c10 : checkBlock 3164675 128 b0386c10 = true := by
  decide +kernel

private def b0386c11 : List Row := [
  .c 3, .c 47, .c 5, .c 3, .p pv7 [pv2,pv7,pv23,pv9829], .c 13, .c 3, .c 5, .c 619, .c 3,
  .p pv17 [pv2,pv5,pv63299], .c 11, .c 3, .p pv2 [pv2,pv83,pv9533], .c 7, .c 3, .c 19, .c 5, .c 3,
  .p pv3 [pv2,pv395621], .c 163, .c 3, .c 5, .c 79, .c 3, .p pv23 [pv2,pv5,pv7,pv13,pv37,pv47],
  .p pv3 [pv2,pv3,pv19,pv27763], .c 3, .c 7, .p pv2 [pv2,pv3,pv73,pv3613], .c 3, .c 13, .c 5,
  .c 3, .c 761, .c 7, .c 3, .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv316501], .c 67, .c 3, .c 37,
  .c 11, .c 3, .p pv5 [pv2,pv7,pv331,pv683], .c 5, .c 3, .c 7, .c 29, .c 3, .c 5, .c 101, .c 3,
  .c 11, .c 7, .c 3, .c 311, .p pv7 [pv2,pv3,pv14653], .c 3, .c 23, .c 5, .c 3,
  .p pv2 [pv2,pv13,pv19,pv43,pv149], .c 73, .c 3, .c 5, .p pv3 [pv2,pv3,pv175837], .c 3, .c 7,
  .p pv13 [pv2,pv3,pv233,pv283], .c 3, .c 17, .p pv3 [pv2,pv3,pv7,pv179,pv421], .c 3,
  .p pv2 [pv2,pv1582541], .c 5, .c 3, .c 29, .c 37, .c 3, .c 5, .c 13, .c 3, .c 43, .c 929, .c 3,
  .c 11, .c 71, .c 3, .c 7, .c 5, .c 3, .c 673, .c 47, .c 3, .c 5, .c 7, .c 3, .c 31,
  .p pv2 [pv2,pv3,pv263761], .c 3, .c 739, .p pv2 [pv2,pv3,pv101,pv1741], .c 3,
  .p pv5 [pv2,pv109,pv14519], .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 499, .c 3, .c 1283,
  .p pv2 [pv2,pv3,pv7,pv11,pv13,pv17,pv31], .c 3, .c 107, .c 7, .c 3, .c 11, .c 5, .c 3, .c 17,
  .p pv11 [pv2,pv3,pv5,pv71,pv743], .c 3, .c 5,
]
private theorem h0386c11 : checkBlock 3164931 128 b0386c11 = true := by
  decide +kernel

private def b0386c12 : List Row := [
  .c 43, .c 3, .c 19, .c 31, .c 3, .c 7, .c 197, .c 3, .p pv2 [pv2,pv37,pv42773], .c 5, .c 3,
  .p pv3 [pv2,pv173,pv2287], .c 7, .c 3, .c 5, .c 11, .c 3, .c 127, .p pv3 [pv2,pv3,pv131,pv4027],
  .c 3, .c 13, .c 19, .c 3, .c 1009, .c 5, .c 3, .c 7, .c 41, .c 3, .c 5, .c 17, .c 3, .c 71,
  .c 7, .c 3, .c 179, .p pv2 [pv2,pv3,pv641,pv823], .c 3, .c 29, .c 5, .c 3,
  .p pv2 [pv2,pv791317], .p pv13 [pv2,pv3,pv5,pv105509], .c 3, .c 5, .c 157, .c 3, .c 7, .c 11,
  .c 3, .p pv5 [pv2,pv19,pv31,pv2687], .p pv11 [pv2,pv3,pv7,pv83,pv227], .c 3, .c 79, .c 5, .c 3,
  .p pv2 [pv2,pv17,pv93097], .p pv17 [pv2,pv3,pv5,pv3517], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv23,pv22937], .c 3, .p pv7 [pv2,pv5,pv316531], .c 37, .c 3, .c 31, .c 53, .c 3,
  .c 7, .c 5, .c 3, .c 23, .c 13, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv101,pv1567], .c 19,
  .c 3, .c 569, .c 11, .c 3, .c 73, .c 5, .c 3, .c 43, .c 251, .c 3, .c 5,
  .p pv7 [pv2,pv3,pv17,pv31033], .c 3, .c 11, .p pv2 [pv2,pv3,pv7,pv53,pv79], .c 3,
  .p pv3 [pv2,pv49459], .c 7, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv791347], .c 541, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv13,pv103,pv197], .c 3, .c 97, .c 47, .c 3, .c 7, .c 13, .c 3, .c 151, .c 5,
  .c 3, .c 19, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv73], .c 3, .c 557, .c 881, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv19,pv27767], .c 3,
]
private theorem h0386c12 : checkBlock 3165187 128 b0386c12 = true := by
  decide +kernel

private def b0386c13 : List Row := [
  .c 191, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 19, .c 3, .c 13, .c 7, .c 3, .c 23, .c 109,
  .c 3, .c 61, .c 5, .c 3, .p pv7 [pv2,pv53,pv29863], .c 11, .c 3, .c 5, .c 13, .c 3, .c 7,
  .c 199, .c 3, .c 47, .c 73, .c 3, .c 11, .c 5, .c 3, .c 181, .p pv3 [pv2,pv3,pv5,pv105517],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv87931], .c 3, .p pv3 [pv2,pv5,pv39569],
  .p pv2 [pv2,pv3,pv137,pv3851], .c 3, .c 59, .c 661, .c 3, .c 7, .c 5, .c 3, .c 13,
  .p pv17 [pv2,pv3,pv5,pv7,pv7537], .c 3, .c 5, .c 7, .c 3, .c 271, .c 17, .c 3,
  .p pv2 [pv2,pv277,pv2857], .c 23, .c 3, .p pv2 [pv2,pv317,pv4993], .c 5, .c 3, .c 11, .c 19,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv131899], .c 3, .p pv7 [pv2,pv5,pv11,pv14389],
  .p pv3 [pv2,pv3,pv7,pv23,pv29,pv113], .c 3, .c 17, .c 7, .c 3, .c 197, .c 5, .c 3,
  .p pv13 [pv2,pv1582799], .p pv23 [pv2,pv3,pv5,pv1319], .c 3, .c 5, .p pv3 [pv2,pv3,pv71,pv2477],
  .c 3, .c 29, .c 11, .c 3, .c 7, .p pv2 [pv2,pv3,pv527603], .c 3, .c 163, .c 5, .c 3, .c 439,
  .c 7, .c 3, .c 5, .c 53, .c 3, .c 89, .c 13, .c 3, .c 19, .p pv13 [pv2,pv3,pv65951], .c 3,
  .p pv3 [pv2,pv7,pv167,pv677], .c 5, .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv43,pv409], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv19,pv3967], .c 3, .p pv13 [pv2,pv5,pv316567], .c 7, .c 3, .c 71, .c 11,
  .c 3, .c 37, .c 5, .c 3, .c 17, .c 587, .c 3, .c 5, .c 23,
]
private theorem h0386c13 : checkBlock 3165443 128 b0386c13 = true := by
  decide +kernel

private def b0386c14 : List Row := [
  .c 3, .c 7, .c 43, .c 3, .p pv2 [pv2,pv17,pv5477], .p pv11 [pv2,pv3,pv7,pv13,pv223], .c 3,
  .p pv3 [pv2,pv11,pv17987], .c 5, .c 3, .c 523, .c 13, .c 3, .c 5, .c 29, .c 3, .c 263, .c 41,
  .c 3, .c 1123, .p pv2 [pv2,pv3,pv527623], .c 3, .c 7, .c 5, .c 3, .c 563, .c 31, .c 3, .c 5,
  .c 7, .c 3, .c 19, .c 59, .c 3, .c 11, .p pv7 [pv2,pv3,pv43969], .c 3, .c 13, .c 5, .c 3, .c 47,
  .p pv17 [pv2,pv3,pv5,pv19,pv2777], .c 3, .c 5, .c 379, .c 3, .c 17, .c 467, .c 3,
  .p pv2 [pv2,pv53,pv109,pv137], .c 7, .c 3, .c 149, .c 5, .c 3, .c 107, .c 11, .c 3, .c 5, .c 67,
  .c 3, .c 947, .c 1487, .c 3, .c 7, .p pv2 [pv2,pv3,pv263819], .c 3, .c 11, .c 5, .c 3, .c 61,
  .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv79,pv6679], .c 3, .c 13, .p pv2 [pv2,pv3,pv263821], .c 3,
  .p pv3 [pv2,pv19,pv41,pv127], .c 17, .c 3, .c 251, .c 5, .c 3, .c 7, .c 181, .c 3, .c 5, .c 11,
  .c 3, .c 23, .c 7, .c 3, .p pv5 [pv2,pv97,pv16319], .p pv61 [pv2,pv3,pv11,pv1499], .c 3, .c 17,
  .c 5, .c 3, .c 11, .c 29, .c 3, .c 5, .p pv2 [pv2,pv3,pv31,pv17021], .c 3, .c 7, .c 19, .c 3,
  .p pv2 [pv2,pv13,pv107,pv569], .p pv7 [pv2,pv3,pv7,pv43,pv1753], .c 3, .c 743, .c 5, .c 3,
  .c 13, .c 223, .c 3, .c 5, .c 31, .c 3, .p pv2 [pv2,pv5,pv59,pv2683], .c 11, .c 3,
  .p pv2 [pv2,pv7,pv101,pv2239], .c 163, .c 3, .c 7,
]
private theorem h0386c14 : checkBlock 3165699 128 b0386c14 = true := by
  decide +kernel

private def b0386c15 : List Row := [
  .c 5, .c 3, .c 29, .c 17, .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv19,pv877], .c 23, .c 3,
  .c 1297, .c 37, .c 3, .c 97, .c 5, .c 3, .c 19, .p pv3 [pv2,pv3,pv5,pv105533], .c 3, .c 5,
  .c 89, .c 3, .p pv3 [pv2,pv5,pv1583], .c 139, .c 3, .c 13, .c 7, .c 3,
  .p pv2 [pv2,pv17,pv46559], .c 5, .c 3, .c 23, .c 359, .c 3, .c 5, .c 19, .c 3, .c 11, .c 13,
  .c 3, .c 7, .p pv17 [pv2,pv3,pv175891], .c 3, .p pv2 [pv2,pv11,pv23,pv6257], .c 5, .c 3,
  .p pv3 [pv2,pv98939], .c 7, .c 3, .c 5, .c 353, .c 3, .c 31, .c 17, .c 3,
  .p pv2 [pv2,pv1583033], .c 409, .c 3, .c 173, .c 5, .c 3, .c 7, .c 823, .c 3, .c 5, .c 1453,
  .c 3, .c 307, .c 7, .c 3, .c 11, .p pv3 [pv2,pv3,pv13,pv40591], .c 3, .c 19, .c 5, .c 3, .c 367,
  .c 13, .c 3, .c 5, .c 59, .c 3, .c 7, .c 31, .c 3, .c 37, .p pv11 [pv2,pv3,pv7,pv349], .c 3,
  .c 29, .c 5, .c 3, .c 131, .c 11, .c 3, .c 5, .c 113, .c 3, .p pv17 [pv2,pv5,pv13,pv4871],
  .c 167, .c 3, .c 23, .p pv3 [pv2,pv3,pv293,pv1801], .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv151,pv2621], .p pv2 [pv2,pv3,pv5,pv7,pv15077], .c 3, .c 5, .c 7, .c 3,
  .p pv11 [pv2,pv5,pv23,pv6883], .p pv3 [pv2,pv3,pv17,pv3449], .c 3, .p pv2 [pv2,pv1583093],
  .c 13, .c 3, .p pv3 [pv2,pv197887], .c 5, .c 3, .c 17, .c 37, .c 3, .c 5, .c 11, .c 3,
]
private theorem h0386c15 : checkBlock 3165955 128 b0386c15 = true := by
  decide +kernel

private def b0386c16 : List Row := [
  .p pv2 [pv2,pv5,pv316621], .p pv11 [pv2,pv3,pv7,pv37693], .c 3, .c 19, .c 7, .c 3,
  .p pv5 [pv2,pv1193,pv1327], .c 5, .c 3, .c 11, .p pv29 [pv2,pv3,pv5,pv105541], .c 3, .c 5,
  .c 107, .c 3, .c 13, .c 983, .c 3, .c 7, .c 23, .c 3, .p pv2 [pv2,pv791563], .c 5, .c 3,
  .p pv2 [pv2,pv241,pv6569], .c 7, .c 3, .c 5, .c 13, .c 3, .p pv11 [pv2,pv5,pv131,pv2417], .c 11,
  .c 3, .p pv2 [pv2,pv791569], .p pv17 [pv2,pv3,pv29,pv31,pv587], .c 3, .p pv2 [pv2,pv7,pv32309],
  .c 5, .c 3, .c 7, .c 311, .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv47,pv401], .c 3, .c 17, .c 7, .c 3,
  .c 29, .c 31, .c 3, .p pv3 [pv2,pv19,pv37,pv563], .c 5, .c 3, .c 13,
  .p pv13 [pv2,pv3,pv5,pv79,pv167], .c 3, .c 5, .c 61, .c 3, .c 7, .p pv19 [pv2,pv3,pv13,pv20297],
  .c 3, .c 907, .c 11, .c 3, .c 47, .c 5, .c 3, .c 37, .p pv3 [pv2,pv3,pv5,pv11,pv19,pv101], .c 3,
  .c 5, .p pv2 [pv2,pv3,pv263863], .c 3, .c 11, .p pv5 [pv2,pv3,pv175909], .c 3, .c 83, .c 17,
  .c 3, .c 7, .c 5, .c 3, .c 53, .c 197, .c 3, .c 5, .c 7, .c 3, .c 43, .p pv5 [pv2,pv3,pv131933],
  .c 3, .c 13, .c 79, .c 3, .c 17, .c 5, .c 3, .p pv17 [pv2,pv7,pv56543],
  .p pv2 [pv2,pv3,pv5,pv13,pv23,pv353], .c 3, .c 5, .c 701, .c 3, .c 1093, .c 13, .c 3, .c 11,
  .c 7, .c 3, .c 23, .c 5, .c 3, .p pv11 [pv2,pv11,pv163,pv883], .p pv7 [pv2,pv3,pv5,pv26387],
  .c 3, .c 5, .p pv3 [pv2,pv3,pv527741], .c 3, .c 101, .p pv2 [pv2,pv3,pv29,pv337], .c 3, .c 7,
  .c 491, .c 3, .p pv5 [pv2,pv13,pv121787], .c 5,
]
private theorem h0386c16 : checkBlock 3166211 128 b0386c16 = true := by
  decide +kernel

private def b0386c17 : List Row := [
  .c 3, .p pv2 [pv2,pv97,pv8161], .c 7, .c 3, .c 5, .c 43, .c 3, .c 29, .c 19, .c 3, .c 67,
  .c 509, .c 3, .c 11, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 439, .c 3, .c 239, .c 7, .c 3,
  .p pv2 [pv2,pv791629], .p pv11 [pv2,pv3,pv527753], .c 3, .p pv2 [pv2,pv17,pv93133], .c 5, .c 3,
  .c 71, .c 47, .c 3, .c 5, .c 11, .c 3, .c 7, .p pv3 [pv2,pv3,pv175919], .c 3,
  .p pv2 [pv2,pv1583273], .p pv29 [pv2,pv3,pv7,pv11,pv23,pv149], .c 3, .c 13, .c 5, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv5,pv733], .c 3, .c 5, .c 1553, .c 3, .c 23, .c 17, .c 3,
  .p pv5 [pv2,pv7,pv577], .c 13, .c 3, .c 7, .c 5, .c 3, .c 59, .c 53, .c 3, .c 5, .c 7, .c 3,
  .c 163, .c 11, .c 3, .c 17, .c 461, .c 3, .p pv2 [pv2,pv229,pv3457], .c 5, .c 3, .c 31, .c 67,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv29,pv18199], .c 3, .c 13, .c 1381, .c 3,
  .p pv2 [pv2,pv11,pv79,pv911], .c 7, .c 3, .p pv2 [pv2,pv1583321], .c 5, .c 3, .c 43,
  .p pv3 [pv2,pv3,pv5,pv31,pv227], .c 3, .c 5, .c 13, .c 3, .p pv3 [pv2,pv5,pv7,pv22619], .c 23,
  .c 3, .c 7, .c 11, .c 3, .c 19, .c 5, .c 3, .p pv19 [pv2,pv1583339], .c 7, .c 3, .c 5, .c 199,
  .c 3, .c 11, .c 61, .c 3, .c 53, .c 83, .c 3, .c 233, .c 5, .c 3, .c 7, .c 19, .c 3, .c 5,
  .c 41, .c 3, .p pv3 [pv2,pv5,pv1237],
]
private theorem h0386c17 : checkBlock 3166467 128 b0386c17 = true := by
  decide +kernel

private def b0386c18 : List Row := [
  .c 7, .c 3, .c 467, .p pv13 [pv2,pv3,pv131947], .c 3, .p pv2 [pv2,pv23,pv34421], .c 5, .c 3,
  .c 359, .p pv11 [pv2,pv3,pv5,pv73,pv241], .c 3, .c 5, .p pv2 [pv2,pv3,pv11,pv47981], .c 3, .c 7,
  .p pv5 [pv2,pv3,pv32987], .c 3, .c 11, .c 97, .c 3, .c 353, .c 5, .c 3,
  .p pv3 [pv2,pv11,pv19,pv947], .c 29, .c 3, .c 5, .c 17, .c 3, .p pv2 [pv2,pv5,pv191,pv829],
  .c 263, .c 3, .c 13, .c 337, .c 3, .c 7, .c 5, .c 3, .c 41, .c 11, .c 3, .c 5, .c 7, .c 3,
  .c 17, .c 13, .c 3, .p pv3 [pv2,pv98963], .c 953, .c 3, .c 11, .c 5, .c 3, .c 29,
  .p pv3 [pv2,pv3,pv5,pv37,pv317], .c 3, .c 5, .c 139, .c 3, .c 229, .c 367, .c 3, .c 23, .c 7,
  .c 3, .c 691, .c 5, .c 3, .p pv2 [pv2,pv29,pv54601], .c 1307, .c 3, .c 5, .c 11, .c 3,
  .p pv11 [pv2,pv5,pv7,pv23,pv281], .c 79, .c 3, .c 7, .c 17, .c 3, .p pv2 [pv2,pv19,pv83339],
  .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv17,pv3881], .c 3, .c 19,
  .p pv3 [pv2,pv3,pv175939], .c 3, .c 43, .c 53, .c 3, .c 17, .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv19,pv463], .c 3, .c 5, .c 163, .c 3, .c 1049, .c 7, .c 3, .c 61, .c 19,
  .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv83,pv9539], .p pv3 [pv2,pv3,pv5,pv43,pv491], .c 3, .c 5,
  .c 181, .c 3, .c 7, .c 41, .c 3, .c 751, .c 13, .c 3, .p pv2 [pv2,pv197,pv4019], .c 5, .c 3,
]
private theorem h0386c18 : checkBlock 3166723 128 b0386c18 = true := by
  decide +kernel

private def b0386c19 : List Row := [
  .p pv2 [pv2,pv37,pv42797], .c 17, .c 3, .c 5, .p pv2 [pv2,pv3,pv107,pv4933], .c 3, .c 31, .c 43,
  .c 3, .p pv2 [pv2,pv7,pv19,pv5953], .c 11, .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv13,pv23,pv331],
  .c 257, .c 3, .c 5, .c 7, .c 3, .c 11, .c 67, .c 3, .c 383, .c 137, .c 3,
  .p pv5 [pv2,pv11,pv17,pv29,pv73], .c 5, .c 3, .c 1097, .p pv23 [pv2,pv3,pv5,pv3299], .c 3, .c 5,
  .c 13, .c 3, .c 113, .c 19, .c 3, .c 101, .c 7, .c 3, .c 1471, .c 5, .c 3, .c 347, .c 683, .c 3,
  .c 5, .c 23, .c 3, .p pv3 [pv2,pv5,pv7,pv11311], .c 17, .c 3, .c 7, .c 37, .c 3, .c 107, .c 5,
  .c 3, .c 13, .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv527851], .c 3, .c 173,
  .p pv5 [pv2,pv3,pv13,pv10151], .c 3, .c 17, .c 29, .c 3, .c 23, .c 5, .c 3, .c 7, .c 11, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv7,pv1571], .c 3, .p pv2 [pv2,pv5,pv158357], .c 7, .c 3, .c 97,
  .p pv2 [pv2,pv3,pv19,pv29,pv479], .c 3, .c 11, .c 5, .c 3, .c 521, .c 157, .c 3, .c 5, .c 19,
  .c 3, .c 7, .c 1091, .c 3, .c 13, .c 59, .c 3, .c 421, .c 5, .c 3, .c 47,
  .p pv11 [pv2,pv3,pv5,pv13,pv2707], .c 3, .c 5, .c 11, .c 3, .p pv19 [pv2,pv5,pv37,pv107], .c 13,
  .c 3, .p pv5 [pv2,pv7,pv29,pv269], .c 41, .c 3, .c 7, .c 5, .c 3, .c 11, .c 419, .c 3, .c 5,
  .c 7, .c 3, .p pv7 [pv2,pv5,pv11,pv28793], .p pv5 [pv2,pv3,pv1031],
]
private theorem h0386c19 : checkBlock 3166979 128 b0386c19 = true := by
  decide +kernel

private def b0386c20 : List Row := [
  .c 3, .c 37, .c 31, .c 3, .c 19, .c 5, .c 3, .p pv3 [pv2,pv7,pv28279], .c 43, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv131969], .c 3, .c 23, .c 11, .c 3, .p pv2 [pv2,pv397,pv3989], .c 7, .c 3,
  .p pv3 [pv2,pv395909], .c 5, .c 3, .p pv11 [pv2,pv797,pv1987], .c 13, .c 3, .c 5, .c 17, .c 3,
  .c 41, .c 29, .c 3, .c 7, .c 229, .c 3, .c 61, .c 5, .c 3, .c 263, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv29327], .c 3, .c 17, .c 193, .c 3, .p pv5 [pv2,pv607,pv2609], .c 11, .c 3,
  .c 13, .c 5, .c 3, .c 7, .c 97, .c 3, .c 5, .c 79, .c 3, .c 11, .c 7, .c 3, .c 19, .c 13, .c 3,
  .c 31, .c 5, .c 3, .c 251, .c 613, .c 3, .c 5, .c 47, .c 3, .c 7, .c 463, .c 3, .c 1499, .c 17,
  .c 3, .c 139, .c 5, .c 3, .c 23, .p pv29 [pv2,pv3,pv5,pv5279], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv11,pv17,pv941], .c 3, .c 13, .p pv2 [pv2,pv3,pv263951], .c 3, .c 11, .c 431,
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv11,pv71987], .c 109, .c 3, .c 5, .c 7, .c 3, .c 491,
  .p pv2 [pv2,pv3,pv149,pv1181], .c 3, .c 1069, .c 131, .c 3, .p pv2 [pv2,pv19,pv71,pv587], .c 5,
  .c 3, .c 37, .c 11, .c 3, .c 5, .c 29, .c 3, .c 19, .p pv5 [pv2,pv3,pv7,pv11,pv857], .c 3,
  .c 887, .c 7, .c 3, .c 11, .c 5, .c 3, .c 13,
]
private theorem h0386c20 : checkBlock 3167235 128 b0386c20 = true := by
  decide +kernel

private def b0386c21 : List Row := [
  .c 17, .c 3, .c 5, .p pv13 [pv2,pv3,pv29,pv37,pv41], .c 3, .p pv2 [pv2,pv5,pv7,pv181], .c 113,
  .c 3, .c 7, .c 19, .c 3, .p pv3 [pv2,pv599,pv661], .c 5, .c 3, .p pv11 [pv2,pv31,pv47,pv1087],
  .c 7, .c 3, .c 5, .c 11, .c 3, .c 461, .c 37, .c 3, .c 23, .c 727, .c 3, .c 73, .c 5, .c 3,
  .c 7, .p pv3 [pv2,pv3,pv5,pv7039], .c 3, .c 5, .p pv5 [pv2,pv3,pv7,pv5387], .c 3,
  .p pv7 [pv2,pv5,pv11,pv23,pv313], .c 7, .c 3, .c 13, .p pv7 [pv2,pv3,pv21997], .c 3,
  .p pv2 [pv2,pv263,pv3011], .c 5, .c 3, .c 163, .p pv2 [pv2,pv3,pv5,pv13,pv31,pv131], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv19553], .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv791899], .c 89, .c 3, .c 1693,
  .c 5, .c 3, .c 829, .c 31, .c 3, .c 5, .p pv5 [pv2,pv3,pv73,pv113], .c 3,
  .p pv3 [pv2,pv5,pv251,pv631], .c 19, .c 3, .c 17, .c 23, .c 3, .c 7, .c 5, .c 3, .c 1531, .c 29,
  .c 3, .c 5, .c 7, .c 3, .c 53, .p pv5 [pv2,pv3,pv23,pv499], .c 3, .p pv3 [pv2,pv167,pv2371],
  .c 11, .c 3, .c 79, .c 5, .c 3, .c 61, .c 13, .c 3, .c 5, .c 547, .c 3, .c 11, .c 677, .c 3,
  .p pv5 [pv2,pv1583843], .c 7, .c 3, .c 67, .c 5, .c 3, .c 19, .c 41, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv47,pv239], .c 3, .c 131, .c 281, .c 3, .c 7, .c 271, .c 3, .c 13, .c 5, .c 3,
  .c 17, .c 7, .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv149,pv1063], .c 211, .c 3,
]
private theorem h0386c21 : checkBlock 3167491 128 b0386c21 = true := by
  decide +kernel

private def b0386c22 : List Row := [
  .c 11, .c 13, .c 3, .c 47, .c 5, .c 3, .c 7, .c 127, .c 3, .c 5, .c 23, .c 3,
  .p pv2 [pv2,pv5,pv316777], .c 7, .c 3, .c 89, .c 1543, .c 3, .c 41, .c 5, .c 3, .c 157, .c 11,
  .c 3, .c 5, .c 17, .c 3, .c 7, .c 173, .c 3, .c 71, .p pv11 [pv2,pv3,pv7,pv2357], .c 3, .c 11,
  .c 5, .c 3, .c 701, .c 79, .c 3, .c 5, .c 13, .c 3, .c 17, .p pv23 [pv2,pv3,pv19,pv6947], .c 3,
  .p pv2 [pv2,pv7,pv23,pv4919], .p pv19 [pv2,pv3,pv175991], .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv17,pv23293], .c 19, .c 3, .c 5, .c 7, .c 3, .c 83, .c 53, .c 3, .c 109,
  .p pv2 [pv2,pv3,pv11,pv103,pv233], .c 3, .c 29, .c 5, .c 3, .c 11, .c 199, .c 3, .c 5, .c 59,
  .c 3, .p pv2 [pv2,pv5,pv11,pv31,pv929], .c 443, .c 3, .p pv3 [pv2,pv43,pv9209], .c 7, .c 3,
  .c 37, .c 5, .c 3, .p pv2 [pv2,pv19,pv73,pv571], .c 1039, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv17,pv53,pv293], .c 3, .c 31, .c 11, .c 3, .c 7, .p pv11 [pv2,pv3,pv23,pv1913],
  .c 3, .c 17, .c 5, .c 3, .c 43, .c 7, .c 3, .c 5, .c 41, .c 3, .c 23,
  .p pv5 [pv2,pv3,pv31,pv2129], .c 3, .c 13, .c 1759, .c 3, .p pv2 [pv2,pv7,pv226283], .c 5, .c 3,
  .c 7, .c 103, .c 3, .c 5, .c 37, .c 3, .c 73, .c 7, .c 3, .p pv2 [pv2,pv229,pv6917], .c 11,
  .c 3, .p pv3 [pv2,pv461,pv859], .c 5, .c 3, .p pv7 [pv2,pv1583999], .c 17,
]
private theorem h0386c22 : checkBlock 3167747 128 b0386c22 = true := by
  decide +kernel

private def b0386c23 : List Row := [
  .c 3, .c 5, .p pv3 [pv2,pv3,pv528001], .c 3, .c 7, .c 269, .c 3, .p pv3 [pv2,pv389,pv509],
  .p pv2 [pv2,pv3,pv7,pv17,pv29], .c 3, .p pv5 [pv2,pv11,pv13,pv19,pv53], .c 5, .c 3, .c 41,
  .p pv19 [pv2,pv3,pv5,pv105601], .c 3, .c 5, .p pv7 [pv2,pv3,pv88001], .c 3, .c 19, .c 23, .c 3,
  .c 29, .c 277, .c 3, .c 7, .c 5, .c 3, .c 419, .c 13, .c 3, .c 5, .c 7, .c 3, .c 1019, .c 863,
  .c 3, .c 11, .c 19, .c 3, .c 1279, .c 5, .c 3, .c 23, .c 71, .c 3, .c 5,
  .p pv29 [pv2,pv3,pv61,pv541], .c 3, .c 233, .c 17, .c 3, .c 31, .c 7, .c 3, .c 13, .c 5, .c 3,
  .p pv11 [pv2,pv1584059], .c 11, .c 3, .c 5, .c 73, .c 3, .c 151, .c 89, .c 3, .c 7, .c 13, .c 3,
  .c 11, .c 5, .c 3, .c 173, .c 7, .c 3, .c 5, .c 61, .c 3, .c 223, .c 29, .c 3,
  .p pv5 [pv2,pv1584083], .c 31, .c 3, .c 661, .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .c 11, .c 3,
  .c 13, .c 7, .c 3, .c 43, .c 37, .c 3, .p pv2 [pv2,pv1584101], .c 5, .c 3, .c 11, .c 1033, .c 3,
  .c 5, .c 13, .c 3, .c 7, .c 47, .c 3, .c 23, .c 67, .c 3, .c 71, .c 5, .c 3, .c 17, .c 59, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv528041], .c 3, .c 631, .c 11, .c 3, .p pv3 [pv2,pv7,pv13,pv17],
]
private theorem h0386c23 : checkBlock 3168003 128 b0386c23 = true := by
  decide +kernel

private def b0386c24 : List Row := [
  .p pv2 [pv2,pv3,pv528043], .c 3, .c 7, .c 5, .c 3, .c 13, .p pv3 [pv2,pv3,pv5,pv7,pv47,pv107],
  .c 3, .c 5, .c 7, .c 3, .c 431, .c 43, .c 3, .c 53, .p pv13 [pv2,pv3,pv19,pv193], .c 3, .c 31,
  .c 5, .c 3, .c 1697, .c 401, .c 3, .c 5, .c 17, .c 3, .c 89, .p pv5 [pv2,pv3,pv7,pv18859], .c 3,
  .c 47, .c 7, .c 3, .p pv2 [pv2,pv173,pv9157], .c 5, .c 3, .c 857,
  .p pv3 [pv2,pv3,pv5,pv11,pv9601], .c 3, .c 5, .c 29, .c 3, .c 11, .p pv19 [pv2,pv3,pv23,pv2551],
  .c 3, .c 7, .p pv23 [pv2,pv3,pv264029], .c 3, .p pv3 [pv2,pv11,pv9001], .c 5, .c 3, .c 59, .c 7,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv29,pv131,pv139], .c 3, .p pv2 [pv2,pv5,pv101,pv3137], .c 13, .c 3,
  .c 107, .c 1601, .c 3, .c 19, .c 5, .c 3, .c 7, .c 1777, .c 3, .c 5, .c 503, .c 3, .c 61, .c 7,
  .c 3, .c 11, .c 17, .c 3, .c 1109, .c 5, .c 3, .c 73, .c 19, .c 3, .c 5, .c 241, .c 3, .c 7,
  .c 151, .c 3, .c 683, .c 41, .c 3, .c 17, .c 5, .c 3, .p pv3 [pv2,pv31,pv1597], .c 11, .c 3,
  .c 5, .c 23, .c 3, .p pv3 [pv2,pv5,pv17,pv9319], .c 641, .c 3, .p pv2 [pv2,pv7,pv227,pv997],
  .c 751, .c 3, .c 7, .c 5, .c 3, .c 31, .c 193, .c 3, .c 5, .c 7, .c 3, .c 167,
  .p pv2 [pv2,pv3,pv73,pv3617], .c 3, .c 19, .c 53, .c 3, .c 13, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv113161], .c 17, .c 3,
]
private theorem h0386c24 : checkBlock 3168259 128 b0386c24 = true := by
  decide +kernel

private def b0386c25 : List Row := [
  .c 5, .c 11, .c 3, .c 41, .c 61, .c 3, .c 773, .c 7, .c 3, .p pv2 [pv2,pv37,pv79,pv271], .c 5,
  .c 3, .c 11, .c 31, .c 3, .c 5, .c 307, .c 3, .c 269, .c 257, .c 3, .c 7, .c 383, .c 3,
  .p pv2 [pv2,pv17,pv41,pv2273], .c 5, .c 3, .c 29, .c 7, .c 3, .c 5, .c 811, .c 3, .c 13, .c 11,
  .c 3, .c 211, .c 103, .c 3, .c 449, .c 5, .c 3, .c 7, .c 877, .c 3, .c 5, .c 13, .c 3, .c 19,
  .c 7, .c 3, .p pv3 [pv2,pv11,pv36007], .p pv2 [pv2,pv3,pv23,pv22961], .c 3, .c 1181, .c 5, .c 3,
  .p pv2 [pv2,pv131,pv6047], .c 67, .c 3, .c 5, .c 541, .c 3, .c 7, .c 37, .c 3, .c 17, .c 11,
  .c 3, .p pv2 [pv2,pv792163], .c 5, .c 3, .c 13, .c 619, .c 3, .c 5, .c 89, .c 3, .c 11, .c 101,
  .c 3, .c 199, .p pv3 [pv2,pv3,pv367,pv1439], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv198043],
  .c 83, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv31687], .c 1151, .c 3, .c 1571,
  .p pv2 [pv2,pv3,pv264059], .c 3, .c 43, .c 5, .c 3, .p pv11 [pv2,pv7,pv226337],
  .p pv7 [pv2,pv3,pv5,pv163], .c 3, .c 5, .c 31, .c 3, .c 157, .c 23, .c 3, .c 11, .c 7, .c 3,
  .c 29, .c 5, .c 3, .c 17, .c 283, .c 3, .c 5, .p pv2 [pv2,pv3,pv23,pv43,pv89], .c 3, .c 569,
  .c 13, .c 3, .c 7, .c 79,
]
private theorem h0386c25 : checkBlock 3168515 128 b0386c25 = true := by
  decide +kernel

private def b0386c26 : List Row := [
  .c 3, .c 557, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .c 47, .c 3, .c 37, .c 1223, .c 3, .c 1487,
  .c 43, .c 3, .c 11, .c 5, .c 3, .c 7, .c 337, .c 3, .c 5, .c 17, .c 3,
  .p pv3 [pv2,pv5,pv19,pv31,pv269], .c 7, .c 3, .p pv2 [pv2,pv1584413],
  .p pv2 [pv2,pv3,pv13,pv37,pv61], .c 3, .p pv3 [pv2,pv67,pv739], .c 5, .c 3, .c 19, .c 13, .c 3,
  .c 5, .c 11, .c 3, .c 7, .c 809, .c 3, .c 73, .c 29, .c 3, .p pv5 [pv2,pv1584431], .c 5, .c 3,
  .c 11, .c 23, .c 3, .c 5, .c 19, .c 3, .c 47, .c 163, .c 3, .c 263, .c 61, .c 3, .c 7, .c 5,
  .c 3, .c 67, .c 239, .c 3, .c 5, .c 7, .c 3, .p pv11 [pv2,pv5,pv316891], .c 11, .c 3, .c 23,
  .c 13, .c 3, .c 53, .c 5, .c 3, .c 1117, .c 41, .c 3, .c 5, .p pv13 [pv2,pv3,pv17,pv863], .c 3,
  .p pv3 [pv2,pv5,pv23,pv83], .c 71, .c 3, .c 137, .c 7, .c 3, .c 17, .c 5, .c 3,
  .p pv17 [pv2,pv13,pv121883], .p pv29 [pv2,pv3,pv5,pv3301], .c 3, .c 5, .c 1667, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv19,pv41,pv113], .c 3, .c 7, .c 11, .c 3, .p pv5 [pv2,pv1584491], .c 5, .c 3,
  .p pv2 [pv2,pv792247], .c 7, .c 3, .c 5, .c 13, .c 3, .c 11, .c 73, .c 3,
  .p pv5 [pv2,pv31,pv79,pv647], .c 23, .c 3, .c 37, .c 5, .c 3, .c 7, .c 17, .c 3, .c 5,
]
private theorem h0386c26 : checkBlock 3168771 128 b0386c26 = true := by
  decide +kernel

private def b0386c27 : List Row := [
  .p pv2 [pv2,pv3,pv7,pv3593], .c 3, .c 127, .c 7, .c 3, .c 31, .p pv41 [pv2,pv3,pv17,pv31069],
  .c 3, .p pv2 [pv2,pv449,pv3529], .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv37,pv571], .c 3, .c 5,
  .c 43, .c 3, .c 7, .p pv3 [pv2,pv3,pv13,pv29,pv467], .c 3, .c 11, .c 47, .c 3, .c 601, .c 5,
  .c 3, .c 1321, .c 149, .c 3, .c 5, .c 37, .c 3, .c 29, .p pv2 [pv2,pv3,pv264091], .c 3,
  .p pv5 [pv2,pv7,pv56591], .c 31, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv792277], .c 11, .c 3,
  .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv29,pv683], .c 17, .c 3, .c 13, .c 181, .c 3, .c 11, .c 5,
  .c 3, .c 197, .c 439, .c 3, .c 5, .c 23, .c 3, .c 347, .c 13, .c 3, .c 17, .c 7, .c 3, .c 47,
  .c 5, .c 3, .p pv3 [pv2,pv198073], .c 1483, .c 3, .c 5, .c 11, .c 3, .c 19, .c 389, .c 3, .c 7,
  .c 83, .c 3, .c 23, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 29, .c 3,
  .p pv2 [pv2,pv5,pv11,pv47,pv613], .c 587, .c 3, .p pv3 [pv2,pv23,pv2153], .c 19, .c 3, .c 31,
  .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv29,pv1301], .c 3, .c 53, .c 7, .c 3,
  .p pv5 [pv2,pv1584623], .c 787, .c 3, .c 193, .c 5, .c 3, .c 17, .p pv2 [pv2,pv3,pv5,pv5869],
  .c 3, .c 5, .c 829, .c 3, .c 7, .p pv5 [pv2,pv3,pv37,pv43,pv83], .c 3,
  .p pv2 [pv2,pv11,pv17,pv19,pv223], .c 101, .c 3,
]
private theorem h0386c27 : checkBlock 3169027 128 b0386c27 = true := by
  decide +kernel

private def b0386c28 : List Row := [
  .c 13, .c 5, .c 3, .p pv3 [pv2,pv421,pv941], .p pv2 [pv2,pv3,pv5,pv89,pv1187], .c 3, .c 5,
  .p pv7 [pv2,pv3,pv13,pv1693], .c 3, .c 67, .c 59, .c 3, .p pv2 [pv2,pv7,pv226379], .c 11, .c 3,
  .c 7, .c 5, .c 3, .p pv19 [pv2,pv547,pv2897], .p pv17 [pv2,pv3,pv5,pv7,pv11], .c 3, .c 5, .c 7,
  .c 3, .c 11, .c 19, .c 3, .p pv3 [pv2,pv197,pv2011], .c 139, .c 3, .p pv5 [pv2,pv11,pv144061],
  .c 5, .c 3, .p pv2 [pv2,pv7,pv13,pv8707], .c 47, .c 3, .c 5, .p pv2 [pv2,pv3,pv264113], .c 3,
  .c 13, .c 1523, .c 3, .c 1427, .c 7, .c 3, .c 823, .c 5, .c 3, .c 89, .c 29, .c 3, .c 5, .c 13,
  .c 3, .c 241, .c 109, .c 3, .c 7, .c 281, .c 3, .c 503, .c 5, .c 3, .c 19, .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv132059], .c 3, .c 59, .c 23, .c 3, .p pv2 [pv2,pv13,pv9377], .c 17, .c 3,
  .p pv3 [pv2,pv7,pv56597], .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 19, .c 3,
  .p pv2 [pv2,pv5,pv63389], .c 7, .c 3, .c 37, .p pv2 [pv2,pv3,pv176081], .c 3, .c 11, .c 5, .c 3,
  .c 23, .c 31, .c 3, .c 5, .p pv5 [pv2,pv3,pv29347], .c 3, .c 7, .p pv2 [pv2,pv3,pv528247], .c 3,
  .c 43, .p pv13 [pv2,pv3,pv7,pv9433], .c 3, .c 167, .c 5, .c 3, .c 61,
  .p pv2 [pv2,pv3,pv5,pv2113], .c 3, .c 5, .c 11, .c 3, .c 71, .c 631, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv11,pv48023], .c 3, .c 7, .c 5, .c 3, .c 11, .c 17, .c 3, .c 5, .c 7,
]
private theorem h0386c28 : checkBlock 3169283 128 b0386c28 = true := by
  decide +kernel

private def b0386c29 : List Row := [
  .c 3, .p pv3 [pv2,pv5,pv11,pv14407], .c 13, .c 3, .p pv2 [pv2,pv41,pv38653],
  .p pv2 [pv2,pv3,pv17,pv5179], .c 3, .c 179, .c 5, .c 3, .c 53, .c 19, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv176087], .c 3, .c 739, .c 11, .c 3, .c 379, .c 7, .c 3,
  .p pv5 [pv2,pv13,pv17,pv71,pv101], .c 5, .c 3, .c 229, .c 1229, .c 3, .c 5, .c 1153, .c 3,
  .c 227, .p pv2 [pv2,pv3,pv176089], .c 3, .c 7, .c 947, .c 3, .c 29, .c 5, .c 3, .c 103, .c 7,
  .c 3, .c 5, .c 269, .c 3, .c 919, .c 17, .c 3, .c 19, .c 11, .c 3,
  .p pv5 [pv2,pv7,pv29,pv37,pv211], .c 5, .c 3, .c 7, .c 1289, .c 3, .c 5, .c 31, .c 3, .c 11,
  .c 7, .c 3, .c 17, .c 41, .c 3, .c 13, .c 5, .c 3, .c 37, .p pv13 [pv2,pv3,pv5,pv47,pv281],
  .c 3, .c 5, .c 83, .c 3, .c 7, .p pv2 [pv2,pv3,pv1087], .c 3, .p pv3 [pv2,pv99053], .c 13, .c 3,
  .c 67, .c 5, .c 3, .c 421, .c 277, .c 3, .c 5, .c 79, .c 3, .p pv3 [pv2,pv5,pv109,pv727],
  .p pv3 [pv2,pv3,pv23,pv103,pv223], .c 3, .c 11, .c 29, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv13,pv11083], .p pv17 [pv2,pv3,pv5,pv7,pv7547], .c 3, .c 5, .c 7, .c 3, .c 13,
  .c 37, .c 3, .p pv2 [pv2,pv139,pv5701], .p pv3 [pv2,pv3,pv29,pv18217], .c 3, .c 113, .c 5, .c 3,
  .c 17, .c 11, .c 3, .c 5, .c 13, .c 3, .c 31, .p pv3 [pv2,pv3,pv7,pv11,pv2287], .c 3, .c 29,
  .c 7, .c 3, .c 11,
]
private theorem h0386c29 : checkBlock 3169539 128 b0386c29 = true := by
  decide +kernel

private def b0386c30 : List Row := [
  .c 5, .c 3, .c 863, .c 1193, .c 3, .c 5, .c 131, .c 3, .p pv13 [pv2,pv5,pv7,pv6469],
  .p pv5 [pv2,pv3,pv31,pv8521], .c 3, .c 7, .p pv2 [pv2,pv3,pv229,pv769], .c 3, .c 613, .c 5,
  .c 3, .c 13, .c 7, .c 3, .c 5, .c 11, .c 3, .c 1657, .c 31, .c 3, .p pv5 [pv2,pv19,pv83417],
  .p pv67 [pv2,pv3,pv11,pv12007], .c 3, .c 83, .c 5, .c 3, .c 7, .c 163, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv7,pv71,pv1063], .c 3, .c 17, .c 7, .c 3, .c 53, .c 73, .c 3, .c 23, .c 5,
  .c 3, .p pv3 [pv2,pv17,pv5827], .c 827, .c 3, .c 5, .c 1171, .c 3, .c 7, .c 11, .c 3, .c 13,
  .p pv11 [pv2,pv3,pv7,pv599], .c 3, .c 89, .c 5, .c 3, .p pv7 [pv2,pv1584959],
  .p pv7 [pv2,pv3,pv5,pv13,pv127], .c 3, .c 5, .c 197, .c 3, .p pv2 [pv2,pv5,pv53,pv5981], .c 13,
  .c 3, .c 71, .c 17, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv792487],
  .p pv3 [pv2,pv3,pv5,pv7,pv3019], .c 3, .c 5, .c 7, .c 3, .c 29, .p pv2 [pv2,pv3,pv47,pv1249],
  .c 3, .c 31, .c 11, .c 3, .c 17, .c 5, .c 3, .c 19, .p pv2 [pv2,pv3,pv5,pv11,pv1601], .c 3,
  .c 5, .c 61, .c 3, .c 11, .c 433, .c 3, .c 41, .c 7, .c 3, .c 43, .c 5, .c 3, .c 47, .c 13,
  .c 3, .c 5, .c 19, .c 3, .c 23, .c 311, .c 3, .c 7, .c 31, .c 3, .c 79, .c 5, .c 3,
  .p pv11 [pv2,pv41,pv67,pv577], .c 7, .c 3, .c 5, .c 109, .c 3,
]
private theorem h0386c30 : checkBlock 3169795 128 b0386c30 = true := by
  decide +kernel

private def b0386c31 : List Row := [
  .p pv2 [pv2,pv5,pv13,pv4877], .p pv2 [pv2,pv3,pv173,pv509], .c 3, .c 11,
  .p pv19 [pv2,pv3,pv17,pv31079], .c 3, .c 13, .c 5, .c 3, .c 7, .c 719, .c 3, .c 5, .c 29, .c 3,
  .c 1489, .c 7, .c 3, .c 101, .c 13, .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv73,pv21713], .c 11,
  .c 3, .c 5, .p pv5 [pv2,pv3,pv29,pv6073], .c 3, .c 7, .c 23, .c 3, .c 1439,
  .p pv19 [pv2,pv3,pv7,pv75479], .c 3, .c 11, .c 5, .c 3, .c 59, .c 19, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv23,pv5743], .c 3, .c 13, .c 17, .c 3, .c 499, .p pv2 [pv2,pv3,pv264179], .c 3,
  .c 7, .c 5, .c 3, .c 23, .c 41, .c 3, .c 5, .c 7, .c 3, .c 73, .c 139, .c 3, .c 17,
  .p pv11 [pv2,pv3,pv11,pv593], .c 3, .p pv5 [pv2,pv23,pv68917], .c 5, .c 3, .c 11, .c 79, .c 3,
  .c 5, .c 37, .c 3, .p pv7 [pv2,pv5,pv11,pv131], .c 1327, .c 3, .c 19, .c 7, .c 3,
  .p pv2 [pv2,pv792553], .c 5, .c 3, .c 13, .c 71, .c 3, .c 5, .p pv3 [pv2,pv3,pv19,pv27809],
  .c 3, .c 61, .c 11, .c 3, .c 7, .c 67, .c 3, .c 41, .c 5, .c 3, .p pv3 [pv2,pv53,pv7477], .c 7,
  .c 3, .c 5, .c 1373, .c 3, .c 43, .p pv3 [pv2,pv3,pv17,pv31081], .c 3,
  .p pv2 [pv2,pv11,pv144103], .c 89, .c 3, .c 149, .c 5, .c 3, .c 7,
  .p pv41 [pv2,pv3,pv5,pv29,pv911], .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv8387], .c 3, .c 47, .c 7,
  .c 3, .c 13, .c 11, .c 3, .c 107, .c 5,
]
private theorem h0386c31 : checkBlock 3170051 128 b0386c31 = true := by
  decide +kernel

def rows0386 : List Row :=
  b0386c00 ++ b0386c01 ++ b0386c02 ++ b0386c03 ++ b0386c04 ++ b0386c05 ++ b0386c06 ++ b0386c07 ++
  b0386c08 ++ b0386c09 ++ b0386c10 ++ b0386c11 ++ b0386c12 ++ b0386c13 ++ b0386c14 ++ b0386c15 ++
  b0386c16 ++ b0386c17 ++ b0386c18 ++ b0386c19 ++ b0386c20 ++ b0386c21 ++ b0386c22 ++ b0386c23 ++
  b0386c24 ++ b0386c25 ++ b0386c26 ++ b0386c27 ++ b0386c28 ++ b0386c29 ++ b0386c30 ++ b0386c31

attribute [local irreducible] checkBlock checkRows checkPrime

theorem checked0386 : checkBlock 3162115 4096 rows0386 = true :=
  checkBlock_append h0386c00 (
    checkBlock_append h0386c01 (
    checkBlock_append h0386c02 (
    checkBlock_append h0386c03 (
    checkBlock_append h0386c04 (
    checkBlock_append h0386c05 (
    checkBlock_append h0386c06 (
    checkBlock_append h0386c07 (
    checkBlock_append h0386c08 (
    checkBlock_append h0386c09 (
    checkBlock_append h0386c10 (
    checkBlock_append h0386c11 (
    checkBlock_append h0386c12 (
    checkBlock_append h0386c13 (
    checkBlock_append h0386c14 (
    checkBlock_append h0386c15 (
    checkBlock_append h0386c16 (
    checkBlock_append h0386c17 (
    checkBlock_append h0386c18 (
    checkBlock_append h0386c19 (
    checkBlock_append h0386c20 (
    checkBlock_append h0386c21 (
    checkBlock_append h0386c22 (
    checkBlock_append h0386c23 (
    checkBlock_append h0386c24 (
    checkBlock_append h0386c25 (
    checkBlock_append h0386c26 (
    checkBlock_append h0386c27 (
    checkBlock_append h0386c28 (
    checkBlock_append h0386c29 (
    checkBlock_append h0386c30 (
    h0386c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
