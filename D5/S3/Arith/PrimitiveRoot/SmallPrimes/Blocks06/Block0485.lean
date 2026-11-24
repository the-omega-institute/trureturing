/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks06/Block0485
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks06/Block0485.checked0485
   digest: Kernel proof of checker success on extended consecutive odd slots. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table043
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table047
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table053
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table061
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table070
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table082
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table099
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table123
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table157
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table159
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table160
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table162
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table163
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table165
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table168
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table171
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table175
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table182
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table183
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table191
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table203
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables02.Table224
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables03.Table249

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private def b0485c00 : List Row := [
  .c 107, .c 3, .c 5, .p pv17 [pv2,pv3,pv7,pv5903], .c 3, .c 1531, .c 7, .c 3, .c 79, .c 263,
  .c 3, .c 13, .c 5, .c 3, .c 19, .c 71, .c 3, .c 5, .c 47, .c 3, .c 7, .c 11, .c 3,
  .p pv3 [pv2,pv23,pv21559], .c 13, .c 3, .p pv5 [pv2,pv859,pv2309], .c 5, .c 3, .c 67,
  .p pv53 [pv2,pv3,pv5,pv132229], .c 3, .c 5, .c 19, .c 3, .c 29, .p pv2 [pv2,pv3,pv17,pv38891],
  .c 3, .p pv7 [pv2,pv7,pv11,pv25759], .p pv17 [pv2,pv3,pv165287], .c 3, .c 7, .c 5, .c 3, .c 17,
  .c 1493, .c 3, .c 5, .c 7, .c 3, .c 13, .p pv23 [pv2,pv3,pv71,pv97], .c 3, .c 277, .c 11, .c 3,
  .p pv2 [pv2,pv43,pv193,pv239], .c 5, .c 3, .p pv3 [pv2,pv7,pv35419], .c 163, .c 3, .c 5, .c 13,
  .c 3, .c 11, .c 269, .c 3, .c 223, .c 7, .c 3, .c 19, .c 5, .c 3, .c 701,
  .p pv13 [pv2,pv3,pv5,pv16529], .c 3, .c 5, .c 17, .c 3, .c 23, .c 991, .c 3, .c 7, .c 1181,
  .c 3, .c 59, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 29, .c 3, .c 17, .c 67, .c 3, .c 11, .c 97,
  .c 3, .c 61, .c 5, .c 3, .c 7, .c 1459, .c 3, .c 5, .p pv3 [pv2,pv3,pv7,pv29,pv3257], .c 3,
  .c 691, .c 7, .c 3, .c 41, .c 31, .c 3, .p pv2 [pv2,pv59,pv33619], .c 5, .c 3,
  .p pv3 [pv2,pv19,pv26099], .c 11, .c 3, .c 5, .p pv5 [pv2,pv3,pv3061], .c 3, .c 7, .c 23, .c 3,
]
private theorem h0485c00 : checkBlock 3966811 128 b0485c00 = true := by
  decide +kernel

private def b0485c01 : List Row := [
  .c 13, .c 17, .c 3, .c 11, .c 5, .c 3, .c 1061, .p pv17 [pv2,pv3,pv5,pv13,pv2543], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv17,pv19,pv23,pv89], .c 3, .c 113, .c 13, .c 3, .c 631, .c 127, .c 3, .c 7,
  .c 5, .c 3, .c 23, .p pv3 [pv2,pv3,pv5,pv7,pv2099], .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv17,pv2917], .p pv2 [pv2,pv3,pv661187], .c 3, .p pv5 [pv2,pv1983563], .c 47,
  .c 3, .p pv2 [pv2,pv13,pv23,pv31,pv107], .c 5, .c 3, .c 11, .p pv2 [pv2,pv3,pv5,pv37,pv1787],
  .c 3, .c 5, .p pv2 [pv2,pv3,pv433,pv509], .c 3, .c 83, .c 541, .c 3, .p pv2 [pv2,pv53,pv18713],
  .c 7, .c 3, .c 31, .c 5, .c 3, .c 271, .c 13, .c 3, .c 5, .c 37, .c 3, .c 19, .c 11, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv17,pv19447], .c 3, .p pv3 [pv2,pv495899], .c 5, .c 3, .c 139, .c 7, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv661201], .c 3, .c 863, .c 1669, .c 3, .c 457, .c 19, .c 3, .c 13, .c 5,
  .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv132241], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv13,pv173], .c 3,
  .p pv3 [pv2,pv5,pv99181], .c 7, .c 3, .c 23, .c 11, .c 3, .p pv2 [pv2,pv167,pv5939], .c 5, .c 3,
  .p pv2 [pv2,pv29,pv73,pv937], .c 191, .c 3, .c 5, .c 71, .c 3, .c 7, .c 17, .c 3,
  .p pv2 [pv2,pv19,pv52201], .c 227, .c 3, .c 41, .c 5, .c 3, .p pv3 [pv2,pv13,pv37,pv1031],
  .c 233, .c 3, .c 5, .p pv5 [pv2,pv3,pv20663], .c 3, .c 13, .c 853, .c 3, .c 17, .c 43, .c 3,
  .c 7, .c 5, .c 3, .c 883, .p pv17 [pv2,pv3,pv5,pv7,pv4723],
]
private theorem h0485c01 : checkBlock 3967067 128 b0485c01 = true := by
  decide +kernel

private def b0485c02 : List Row := [
  .c 3, .c 5, .c 7, .c 3, .c 73, .c 19, .c 3, .c 11, .c 23, .c 3, .p pv5 [pv2,pv241,pv8231], .c 5,
  .c 3, .c 31, .p pv11 [pv2,pv3,pv5,pv26449], .c 3, .c 5, .p pv5 [pv2,pv3,pv179,pv1847], .c 3,
  .c 307, .p pv7 [pv2,pv3,pv7,pv23,pv37], .c 3, .c 353, .c 7, .c 3, .p pv2 [pv2,pv379,pv2617],
  .c 5, .c 3, .c 13, .c 11, .c 3, .c 5, .c 1901, .c 3, .c 547, .c 223, .c 3, .c 7, .c 37, .c 3,
  .c 11, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv55103], .c 3, .c 53, .c 149, .c 3,
  .c 311, .p pv13 [pv2,pv3,pv19,pv17401], .c 3, .c 211, .c 5, .c 3, .c 7,
  .p pv19 [pv2,pv3,pv5,pv61,pv271], .c 3, .c 5, .c 11, .c 3, .p pv2 [pv2,pv5,pv79349], .c 7, .c 3,
  .c 13, .c 79, .c 3, .c 199, .c 5, .c 3, .c 11, .c 277, .c 3, .c 5, .c 17, .c 3, .c 7, .c 13,
  .c 3, .p pv5 [pv2,pv1983743], .p pv13 [pv2,pv3,pv7,pv41], .c 3, .p pv2 [pv2,pv991873], .c 5,
  .c 3, .p pv2 [pv2,pv1983749], .c 61, .c 3, .c 5, .p pv2 [pv2,pv3,pv227,pv971], .c 3, .c 17,
  .c 11, .c 3, .p pv2 [pv2,pv7,pv141697], .c 29, .c 3, .c 7, .c 5, .c 3, .c 41, .c 89, .c 3, .c 5,
  .c 7, .c 3, .p pv2 [pv2,pv5,pv198377], .c 113, .c 3, .c 37, .c 499, .c 3,
  .p pv3 [pv2,pv47,pv1319], .c 5, .c 3, .c 1123, .c 13, .c 3, .c 5, .c 43, .c 3,
  .p pv2 [pv2,pv5,pv41,pv9677], .c 59, .c 3, .c 29,
]
private theorem h0485c02 : checkBlock 3967323 128 b0485c02 = true := by
  decide +kernel

private def b0485c03 : List Row := [
  .c 7, .c 3, .c 101, .c 5, .c 3, .c 487, .c 97, .c 3, .c 5, .c 31, .c 3, .c 11, .c 1801, .c 3,
  .c 7, .p pv11 [pv2,pv3,pv165317], .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv19,pv263,pv397], .c 7,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv13,pv50867], .c 3, .c 839, .c 53, .c 3, .c 19, .c 13, .c 3,
  .c 191, .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv2939], .c 3, .c 5, .c 137, .c 3, .c 23, .c 7,
  .c 3, .c 11, .p pv2 [pv2,pv3,pv307,pv359], .c 3, .c 67, .c 5, .c 3,
  .p pv7 [pv2,pv11,pv13,pv13873], .c 17, .c 3, .c 5, .p pv3 [pv2,pv3,pv53,pv4159], .c 3, .c 7,
  .c 29, .c 3, .c 331, .p pv3 [pv2,pv3,pv7,pv17,pv5557], .c 3, .c 1973, .c 5, .c 3, .c 89, .c 11,
  .c 3, .c 5, .c 13, .c 3, .c 31, .c 1213, .c 3, .p pv5 [pv2,pv7,pv40487], .c 733, .c 3, .c 7,
  .c 5, .c 3, .c 43, .p pv11 [pv2,pv3,pv5,pv7,pv47,pv67], .c 3, .c 5, .c 7, .c 3, .c 19, .c 23,
  .c 3, .c 233, .c 929, .c 3, .c 593, .c 5, .c 3, .c 13, .c 491, .c 3, .c 5, .c 11, .c 3, .c 349,
  .c 17, .c 3, .c 47, .c 7, .c 3, .p pv3 [pv2,pv53,pv4679], .c 5, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv5,pv17,pv389], .c 3, .c 5, .c 67, .c 3, .p pv11 [pv2,pv5,pv7,pv11,pv5153],
  .c 449, .c 3, .c 7, .p pv2 [pv2,pv3,pv109,pv6067], .c 3, .c 257, .c 5, .c 3,
  .p pv2 [pv2,pv991957], .c 7, .c 3,
]
private theorem h0485c03 : checkBlock 3967579 128 b0485c03 = true := by
  decide +kernel

private def b0485c04 : List Row := [
  .c 5, .p pv5 [pv2,pv3,pv330653], .c 3, .p pv3 [pv2,pv5,pv24799], .c 11, .c 3, .c 13, .c 1097,
  .c 3, .c 1499, .c 5, .c 3, .c 7, .c 127, .c 3, .c 5, .c 29, .c 3,
  .p pv17 [pv2,pv5,pv149,pv2663], .c 7, .c 3, .p pv2 [pv2,pv11,pv31,pv2909], .c 571, .c 3, .c 229,
  .c 5, .c 3, .c 317, .c 23, .c 3, .c 5, .c 677, .c 3, .c 7, .c 19, .c 3, .c 31, .c 11, .c 3,
  .p pv3 [pv2,pv13,pv38153], .c 5, .c 3, .c 17, .c 1013, .c 3, .c 5, .c 59, .c 3, .c 11, .c 79,
  .c 3, .c 23, .c 41, .c 3, .c 7, .c 5, .c 3, .c 613, .c 13, .c 3, .c 5, .c 7, .c 3,
  .p pv3 [pv2,pv5,pv19,pv23,pv227], .p pv17 [pv2,pv3,pv661327], .c 3, .c 1091, .c 31, .c 3,
  .p pv2 [pv2,pv103,pv9631], .c 5, .c 3, .c 19, .c 83, .c 3, .c 5, .c 17, .c 3, .c 37,
  .p pv5 [pv2,pv3,pv7,pv7873], .c 3, .c 11, .c 7, .c 3, .c 13, .c 5, .c 3,
  .p pv3 [pv2,pv11,pv67,pv673], .p pv17 [pv2,pv3,pv5,pv44089], .c 3, .c 5, .c 19, .c 3, .c 17,
  .p pv3 [pv2,pv3,pv47,pv14071], .c 3, .c 7, .c 13, .c 3, .c 139, .c 5, .c 3, .c 1987, .c 7, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv220447], .c 3, .c 647, .p pv2 [pv2,pv3,pv11,pv23,pv1307], .c 3, .c 53,
  .c 251, .c 3, .c 11, .c 5, .c 3, .c 7, .p pv7 [pv2,pv3,pv5,pv29,pv4561], .c 3, .c 5,
  .p pv17 [pv2,pv3,pv7,pv97,pv487], .c 3, .c 13, .c 7, .c 3, .c 167, .c 17,
]
private theorem h0485c04 : checkBlock 3967835 128 b0485c04 = true := by
  decide +kernel

private def b0485c05 : List Row := [
  .c 3, .c 19, .c 5, .c 3, .c 29, .c 173, .c 3, .c 5, .c 11, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv19,pv229], .c 3, .c 239, .c 71, .c 3, .c 17, .c 5, .c 3, .c 11, .c 19, .c 3,
  .c 5, .p pv5 [pv2,pv3,pv18371], .c 3, .c 1187, .c 1453, .c 3, .c 83, .p pv2 [pv2,pv3,pv330679],
  .c 3, .c 7, .c 5, .c 3, .c 13, .c 719, .c 3, .c 5, .c 7, .c 3, .c 197, .c 11, .c 3,
  .p pv3 [pv2,pv37,pv6703], .c 1063, .c 3, .p pv5 [pv2,pv1984091], .c 5, .c 3, .c 101, .c 17,
  .c 3, .c 5, .c 941, .c 3, .p pv3 [pv2,pv5,pv19841], .p pv2 [pv2,pv3,pv7,pv107,pv883], .c 3,
  .c 19, .c 7, .c 3, .c 23, .c 5, .c 3, .p pv2 [pv2,pv1984109], .c 113, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv19,pv41,pv283], .c 3, .p pv11 [pv2,pv5,pv7,pv83,pv683], .c 61, .c 3, .c 7,
  .c 11, .c 3, .c 89, .c 5, .c 3, .c 79, .c 7, .c 3, .c 5, .c 47, .c 3, .c 11, .c 13, .c 3, .c 41,
  .c 53, .c 3, .c 29, .c 5, .c 3, .c 7, .c 59, .c 3, .c 5, .c 37, .c 3,
  .p pv2 [pv2,pv5,pv101,pv3929], .c 7, .c 3, .p pv3 [pv2,pv401,pv1237],
  .p pv2 [pv2,pv3,pv43,pv1709], .c 3, .p pv5 [pv2,pv13,pv19,pv29,pv277], .c 5, .c 3, .c 107,
  .c 139, .c 3, .c 5, .c 149, .c 3, .c 7, .p pv2 [pv2,pv3,pv53,pv12479], .c 3, .c 11,
  .p pv107 [pv2,pv3,pv7,pv13,pv23,pv79], .c 3, .c 1429, .c 5, .c 3, .p pv2 [pv2,pv11,pv180379],
  .c 13, .c 3, .c 5,
]
private theorem h0485c05 : checkBlock 3968091 128 b0485c05 = true := by
  decide +kernel

private def b0485c06 : List Row := [
  .c 373, .c 3, .c 23, .c 73, .c 3, .p pv2 [pv2,pv7,pv239,pv593], .c 19, .c 3, .c 7, .c 5, .c 3,
  .c 127, .c 11, .c 3, .c 5, .c 7, .c 3, .p pv2 [pv2,pv5,pv13,pv15263], .c 131, .c 3,
  .p pv2 [pv2,pv359,pv5527], .c 29, .c 3, .c 11, .c 5, .c 3, .c 59, .c 1367, .c 3, .c 5, .c 79,
  .c 3, .p pv2 [pv2,pv5,pv67,pv5923], .c 691, .c 3, .p pv3 [pv2,pv19,pv61,pv107], .c 7, .c 3,
  .c 829, .c 5, .c 3, .c 17, .c 41, .c 3, .c 5, .c 11, .c 3, .c 1229, .c 23, .c 3, .c 7, .c 1933,
  .c 3, .p pv2 [pv2,pv992113], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 1907, .c 3, .c 13, .c 19,
  .c 3, .c 61, .c 83, .c 3, .p pv2 [pv2,pv7,pv283463], .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv132283], .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv7937], .c 7, .c 3,
  .p pv2 [pv2,pv823,pv2411], .c 37, .c 3, .c 41, .c 5, .c 3, .c 1171,
  .p pv11 [pv2,pv3,pv5,pv33071], .c 3, .c 5, .c 31, .c 3, .c 7, .p pv2 [pv2,pv3,pv110237], .c 3,
  .p pv3 [pv2,pv11,pv13,pv3469], .c 47, .c 3, .p pv5 [pv2,pv1984271], .c 5, .c 3, .c 13,
  .p pv11 [pv2,pv3,pv5,pv8819], .c 3, .c 5, .c 269, .c 3, .c 97, .c 29, .c 3,
  .p pv5 [pv2,pv7,pv467,pv607], .c 11, .c 3, .c 7, .c 5, .c 3, .c 277, .c 23, .c 3, .c 5, .c 7,
  .c 3, .c 11, .c 101, .c 3, .p pv2 [pv2,pv643,pv1543], .c 17, .c 3,
]
private theorem h0485c06 : checkBlock 3968347 128 b0485c06 = true := by
  decide +kernel

private def b0485c07 : List Row := [
  .p pv5 [pv2,pv11,pv180391], .c 5, .c 3, .c 179, .c 67, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv17,pv71,pv137], .c 3, .c 29, .c 127, .c 3, .c 13, .c 7, .c 3, .c 17, .c 5,
  .c 3, .c 347, .c 227, .c 3, .c 5, .p pv3 [pv2,pv3,pv11,pv157,pv383], .c 3, .c 31, .c 13, .c 3,
  .c 7, .c 193, .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv11,pv90197], .c 7, .c 3, .c 5, .c 41, .c 3,
  .c 673, .c 1093, .c 3, .c 71, .c 233, .c 3, .c 53, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 587,
  .c 3, .c 449, .c 7, .c 3, .p pv2 [pv2,pv992179], .c 23, .c 3, .c 11, .c 5, .c 3,
  .p pv3 [pv2,pv43,pv83,pv139], .c 13, .c 3, .c 5, .c 29, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv23,pv28759], .c 3, .c 1423, .c 461, .c 3, .c 59, .c 5, .c 3, .c 41,
  .p pv59 [pv2,pv3,pv5,pv33073], .c 3, .c 5, .c 11, .c 3, .c 43, .c 827, .c 3, .c 19, .c 353,
  .c 3, .c 7, .c 5, .c 3, .c 11, .c 73, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv11,pv41], .c 17,
  .c 3, .p pv5 [pv2,pv31,pv64013], .c 13, .c 3, .p pv2 [pv2,pv59,pv67,pv251], .c 5, .c 3,
  .p pv7 [pv2,pv7,pv283487], .c 47, .c 3, .c 5, .p pv2 [pv2,pv3,pv269,pv2459], .c 3, .c 1289,
  .c 11, .c 3, .c 17, .c 7, .c 3, .c 61, .c 5, .c 3, .c 337, .c 257, .c 3, .c 5, .c 23,
]
private theorem h0485c07 : checkBlock 3968603 128 b0485c07 = true := by
  decide +kernel

private def b0485c08 : List Row := [
  .c 3, .c 13, .p pv3 [pv2,pv3,pv661477], .c 3, .c 7, .p pv2 [pv2,pv3,pv31,pv47,pv227], .c 3,
  .p pv3 [pv2,pv19,pv26111], .c 5, .c 3, .c 37, .c 7, .c 3, .c 5, .c 13, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv36749], .c 3, .p pv3 [pv2,pv101,pv307], .c 11, .c 3, .c 23, .c 5, .c 3, .c 7,
  .c 29, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv37,pv1277], .c 3, .c 11, .c 7, .c 3, .c 1787, .c 19,
  .c 3, .c 263, .c 5, .c 3, .c 13, .p pv2 [pv2,pv3,pv5,pv29,pv2281], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv67,pv1097], .c 3, .c 7, .c 37, .c 3, .p pv2 [pv2,pv17,pv58367], .c 197, .c 3,
  .c 1399, .c 5, .c 3, .c 29, .c 71, .c 3, .c 5, .c 83, .c 3, .p pv2 [pv2,pv5,pv191,pv1039],
  .p pv3 [pv2,pv3,pv311,pv709], .c 3, .c 11, .c 59, .c 3, .c 7, .c 5, .c 3, .c 439,
  .p pv29 [pv2,pv3,pv5,pv7], .c 3, .c 5, .c 7, .c 3, .c 53, .c 67, .c 3, .c 13,
  .p pv3 [pv2,pv3,pv23,pv9587], .c 3, .c 31, .c 5, .c 3, .c 43, .c 11, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv110251], .c 3, .c 17, .c 13, .c 3, .c 523, .c 7, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv17,pv107,pv1091], .p pv2 [pv2,pv3,pv5,pv83,pv797], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv271,pv2441], .c 3, .p pv7 [pv2,pv5,pv7,pv56701], .c 239, .c 3, .c 7, .c 431,
  .c 3, .c 73, .c 5, .c 3, .c 167, .c 7, .c 3, .c 5, .c 11, .c 3, .c 37, .c 47, .c 3, .c 59,
  .c 17, .c 3, .c 71,
]
private theorem h0485c08 : checkBlock 3968859 128 b0485c08 = true := by
  decide +kernel

private def b0485c09 : List Row := [
  .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 1667, .c 3, .c 127, .c 7, .c 3, .p pv3 [pv2,pv248071],
  .c 173, .c 3, .c 17, .c 5, .c 3, .c 181, .p pv7 [pv2,pv3,pv5,pv47,pv563], .c 3, .c 5, .c 19,
  .c 3, .c 7, .c 11, .c 3, .p pv5 [pv2,pv59,pv33637], .c 41, .c 3, .c 13, .c 5, .c 3, .c 23,
  .p pv2 [pv2,pv3,pv5,pv22051], .c 3, .c 5, .c 419, .c 3, .p pv7 [pv2,pv5,pv396919],
  .p pv5 [pv2,pv3,pv165383], .c 3, .c 47, .c 13, .c 3, .c 7, .c 5, .c 3, .c 31, .c 17, .c 3, .c 5,
  .c 7, .c 3, .p pv3 [pv2,pv5,pv198461], .c 53, .c 3, .c 911, .c 11, .c 3, .c 19, .c 5, .c 3,
  .c 643, .p pv7 [pv2,pv3,pv5,pv11,pv31,pv97], .c 3, .c 5, .p pv3 [pv2,pv3,pv661541], .c 3, .c 11,
  .p pv2 [pv2,pv3,pv7,pv19,pv829], .c 3, .c 229, .c 7, .c 3, .p pv5 [pv2,pv11,pv17,pv10613], .c 5,
  .c 3, .p pv2 [pv2,pv992317], .c 19, .c 3, .c 5, .c 13, .c 3, .c 67, .c 1697, .c 3, .c 7,
  .p pv17 [pv2,pv3,pv29,pv1901], .c 3, .c 311, .c 5, .c 3, .c 463, .c 7, .c 3, .c 5,
  .p pv2 [pv2,pv3,pv11,pv20047], .c 3, .c 89, .c 17, .c 3, .c 11, .c 1163, .c 3, .c 37, .c 5,
  .c 3, .c 7, .c 61, .c 3, .c 5, .c 97, .c 3, .c 1181, .c 7, .c 3, .c 17,
  .p pv2 [pv2,pv3,pv67,pv4937], .c 3, .c 197, .c 5, .c 3, .c 1307, .c 11, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv19,pv34819], .c 3,
]
private theorem h0485c09 : checkBlock 3969115 128 b0485c09 = true := by
  decide +kernel

private def b0485c10 : List Row := [
  .c 7, .c 43, .c 3, .p pv3 [pv2,pv163,pv761], .c 107, .c 3, .c 11, .c 5, .c 3,
  .p pv2 [pv2,pv233,pv4259], .p pv17 [pv2,pv3,pv5,pv132313], .c 3, .c 5, .c 37, .c 3, .c 101,
  .c 1609, .c 3, .c 13, .c 23, .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv1984709],
  .p pv17 [pv2,pv3,pv5,pv7,pv13,pv727], .c 3, .c 5, .c 7, .c 3, .c 131, .c 13, .c 3,
  .p pv2 [pv2,pv992359], .c 859, .c 3, .p pv2 [pv2,pv19,pv104459], .c 5, .c 3, .c 11,
  .p pv2 [pv2,pv3,pv5,pv8821], .c 3, .c 5, .c 31, .c 3, .c 19, .c 359, .c 3,
  .p pv2 [pv2,pv17,pv313,pv373], .c 7, .c 3, .c 479, .c 5, .c 3, .c 47,
  .p pv7 [pv2,pv3,pv5,pv19,pv1741], .c 3, .c 5, .p pv5 [pv2,pv3,pv107,pv229], .c 3, .c 29, .c 11,
  .c 3, .c 7, .c 19, .c 3, .p pv5 [pv2,pv43,pv101,pv457], .c 5, .c 3, .c 149, .c 7, .c 3, .c 5,
  .c 17, .c 3, .c 73, .c 337, .c 3, .p pv5 [pv2,pv11,pv47,pv349], .p pv13 [pv2,pv3,pv165397],
  .c 3, .c 1237, .c 5, .c 3, .c 7, .c 53, .c 3, .c 5, .c 23, .c 3, .c 17, .c 7, .c 3,
  .p pv2 [pv2,pv19,pv2749], .c 11, .c 3, .c 13, .c 5, .c 3, .p pv3 [pv2,pv17,pv7297],
  .p pv17 [pv2,pv3,pv5,pv11,pv23,pv523], .c 3, .c 5, .c 113, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv37,pv17881], .c 3, .c 653, .c 13, .c 3, .c 23, .c 5, .c 3, .c 719,
  .p pv41 [pv2,pv3,pv5,pv827], .c 3, .c 5, .c 29, .c 3, .p pv7 [pv2,pv5,pv71,pv5591], .c 19, .c 3,
  .c 929, .c 17, .c 3, .c 7, .c 5,
]
private theorem h0485c10 : checkBlock 3969371 128 b0485c10 = true := by
  decide +kernel

private def b0485c11 : List Row := [
  .c 3, .p pv2 [pv2,pv13,pv97,pv787], .c 43, .c 3, .c 5, .c 7, .c 3, .c 13, .c 31, .c 3, .c 11,
  .p pv11 [pv2,pv3,pv1021], .c 3, .c 17, .c 5, .c 3, .p pv2 [pv2,pv7,pv11,pv149,pv173], .c 41,
  .c 3, .c 5, .c 13, .c 3, .c 79, .p pv5 [pv2,pv3,pv7,pv23629], .c 3, .p pv2 [pv2,pv503,pv1973],
  .c 7, .c 3, .c 67, .c 5, .c 3, .c 19, .c 11, .c 3, .c 5, .c 59, .c 3, .c 139,
  .p pv23 [pv2,pv3,pv11,pv41,pv163], .c 3, .c 7, .p pv11 [pv2,pv3,pv19,pv23,pv757], .c 3, .c 11,
  .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 19, .c 3, .c 23, .p pv2 [pv2,pv3,pv13,pv25447], .c 3,
  .p pv3 [pv2,pv31,pv16007], .c 557, .c 3, .c 41, .c 5, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv5,pv67,pv79], .c 3, .c 5, .c 11, .c 3, .c 47, .c 7, .c 3, .c 31,
  .p pv7 [pv2,pv3,pv11,pv1367], .c 3, .p pv3 [pv2,pv17,pv58379], .c 5, .c 3, .c 11, .c 29, .c 3,
  .c 5, .p pv3 [pv2,pv3,pv751,pv881], .c 3, .c 7, .p pv5 [pv2,pv3,pv1723], .c 3, .c 13, .c 1151,
  .c 3, .c 19, .c 5, .c 3, .p pv3 [pv2,pv47,pv5279], .p pv3 [pv2,pv3,pv5,pv13,pv29], .c 3, .c 5,
  .c 67, .c 3, .p pv2 [pv2,pv5,pv198491], .c 11, .c 3, .p pv2 [pv2,pv7,pv103,pv2753], .c 31, .c 3,
  .c 7, .c 5, .c 3, .c 29, .c 19, .c 3, .c 5, .c 7, .c 3, .c 199, .p pv5 [pv2,pv3,pv330821], .c 3,
  .c 17, .c 53, .c 3, .p pv5 [pv2,pv13,pv179,pv853], .c 5, .c 3, .c 23,
  .p pv17 [pv2,pv3,pv5,pv132329], .c 3, .c 5, .c 439, .c 3, .c 587,
]
private theorem h0485c11 : checkBlock 3969627 128 b0485c11 = true := by
  decide +kernel

private def b0485c12 : List Row := [
  .c 1531, .c 3, .c 1493, .c 7, .c 3, .c 127, .c 5, .c 3, .p pv2 [pv2,pv19,pv104471], .c 13, .c 3,
  .c 5, .c 41, .c 3, .c 11, .c 569, .c 3, .c 7, .c 97, .c 3, .p pv2 [pv2,pv11,pv31,pv5821], .c 5,
  .c 3, .c 103, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv19,pv1451], .c 3, .c 61,
  .p pv3 [pv2,pv3,pv17,pv38921], .c 3, .c 1013, .c 47, .c 3, .c 13, .c 5, .c 3, .c 7, .c 23, .c 3,
  .c 5, .c 467, .c 3, .p pv2 [pv2,pv5,pv396997], .c 7, .c 3, .c 11, .c 13, .c 3,
  .p pv5 [pv2,pv1984991], .c 5, .c 3, .c 37, .c 1483, .c 3, .c 5, .p pv2 [pv2,pv3,pv47,pv7039],
  .c 3, .c 7, .c 227, .c 3, .c 23, .p pv43 [pv2,pv3,pv7,pv7877], .c 3, .c 29, .c 5, .c 3, .c 1039,
  .c 11, .c 3, .c 5, .c 17, .c 3, .c 13, .p pv5 [pv2,pv3,pv11,pv73,pv103], .c 3, .c 1361,
  .p pv13 [pv2,pv3,pv661673], .c 3, .c 7, .c 5, .c 3, .p pv3 [pv2,pv3877], .c 59, .c 3, .c 5,
  .c 7, .c 3, .c 17, .c 37, .c 3, .c 251, .c 19, .c 3, .p pv3 [pv2,pv496259], .c 5, .c 3, .c 941,
  .c 829, .c 3, .c 5, .c 11, .c 3, .c 167, .c 523, .c 3, .p pv3 [pv2,pv13,pv19087], .c 7, .c 3,
  .p pv5 [pv2,pv1985051], .c 5, .c 3, .c 11, .p pv19 [pv2,pv3,pv5,pv59,pv2243], .c 3, .c 5,
  .c 1297, .c 3, .p pv3 [pv2,pv5,pv7,pv11,pv1289], .c 137, .c 3, .c 7, .c 17, .c 3,
  .p pv2 [pv2,pv461,pv2153], .c 5, .c 3,
]
private theorem h0485c12 : checkBlock 3969883 128 b0485c12 = true := by
  decide +kernel

private def b0485c13 : List Row := [
  .c 31, .c 7, .c 3, .c 5, .c 43, .c 3, .p pv11 [pv2,pv5,pv271,pv293], .c 11, .c 3,
  .p pv2 [pv2,pv992539], .p pv7 [pv2,pv3,pv29,pv22817], .c 3, .c 17, .c 5, .c 3, .c 7, .c 269,
  .c 3, .c 5, .c 53, .c 3, .c 359, .c 7, .c 3, .c 13, .p pv7 [pv2,pv3,pv36761], .c 3, .c 1277,
  .c 5, .c 3, .p pv7 [pv2,pv953,pv2083], .c 31, .c 3, .c 5, .c 283, .c 3, .c 7, .c 13, .c 3,
  .c 131, .c 11, .c 3, .p pv5 [pv2,pv83,pv23917], .c 5, .c 3, .c 1471, .c 17, .c 3, .c 5, .c 23,
  .c 3, .c 11, .c 151, .c 3, .p pv5 [pv2,pv7,pv61,pv4649], .c 71, .c 3, .c 7, .c 5, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv5,pv7,pv23,pv137], .c 3, .c 5, .c 7, .c 3, .p pv7 [pv2,pv5,pv397027],
  .p pv5 [pv2,pv3,pv41357], .c 3, .p pv2 [pv2,pv41,pv43,pv563], .c 683, .c 3, .c 23, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv35449], .c 13, .c 3, .c 5, .c 19, .c 3, .c 401, .c 29, .c 3, .c 11, .c 7,
  .c 3, .p pv3 [pv2,pv496289], .c 5, .c 3, .c 43, .p pv7 [pv2,pv3,pv5,pv71,pv233], .c 3, .c 5,
  .c 1879, .c 3, .p pv2 [pv2,pv5,pv7,pv13,pv4363], .c 17, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv197,pv3359], .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv131,pv7577], .c 7, .c 3,
  .c 5, .p pv2 [pv2,pv3,pv13,pv31,pv821], .c 3, .c 29, .p pv2 [pv2,pv3,pv11,pv43,pv1399], .c 3,
  .c 17, .c 13, .c 3, .c 11, .c 5, .c 3, .c 7, .c 1031, .c 3, .c 5, .c 31, .c 3, .c 71, .c 7,
]
private theorem h0485c13 : checkBlock 3970139 128 b0485c13 = true := by
  decide +kernel

private def b0485c14 : List Row := [
  .c 3, .c 73, .c 41, .c 3, .c 149, .c 5, .c 3, .p pv3 [pv2,pv13,pv38177], .c 19, .c 3, .c 5,
  .c 11, .c 3, .c 7, .p pv5 [pv2,pv3,pv220579], .c 3, .c 827, .c 61, .c 3, .c 37, .c 5, .c 3,
  .c 11, .p pv17 [pv2,pv3,pv5,pv41,pv269], .c 3, .c 5, .c 13, .c 3, .c 421,
  .p pv5 [pv2,pv3,pv17,pv19463], .c 3, .c 227, .p pv3 [pv2,pv3,pv24509], .c 3, .c 7, .c 5, .c 3,
  .c 17, .c 83, .c 3, .c 5, .c 7, .c 3, .c 41, .c 11, .c 3, .c 19, .p pv7 [pv2,pv3,pv165437],
  .c 3, .p pv2 [pv2,pv992623], .c 5, .c 3, .c 13, .c 97, .c 3, .c 5, .c 37, .c 3, .c 31, .c 23,
  .c 3, .c 163, .c 7, .c 3, .c 59, .c 5, .c 3, .p pv3 [pv2,pv127,pv977],
  .p pv3 [pv2,pv3,pv5,pv157,pv281], .c 3, .c 5, .c 17, .c 3, .c 521, .c 73, .c 3, .c 7, .c 11,
  .c 3, .c 233, .c 5, .c 3, .c 23, .c 7, .c 3, .c 5, .p pv3 [pv2,pv3,pv73529], .c 3, .c 11, .c 31,
  .c 3, .c 13, .p pv2 [pv2,pv3,pv179,pv3697], .c 3, .p pv5 [pv2,pv7,pv11,pv19,pv23,pv59], .c 5,
  .c 3, .c 7, .p pv11 [pv2,pv3,pv5,pv13,pv10181], .c 3, .c 5, .c 181, .c 3, .c 19, .c 7, .c 3,
  .c 47, .c 443, .c 3, .c 101, .c 5, .c 3, .c 79, .c 67, .c 3, .c 5, .c 661, .c 3, .c 7,
  .p pv5 [pv2,pv3,pv165443], .c 3, .c 11, .c 17, .c 3, .p pv2 [pv2,pv13,pv152717], .c 5, .c 3,
  .p pv3 [pv2,pv11,pv45121],
]
private theorem h0485c14 : checkBlock 3970395 128 b0485c14 = true := by
  decide +kernel

private def b0485c15 : List Row := [
  .c 23, .c 3, .c 5, .p pv7 [pv2,pv3,pv17,pv811], .c 3, .c 733, .c 43, .c 3, .c 881, .c 1021,
  .c 3, .c 7, .c 5, .c 3, .p pv11 [pv2,pv1051,pv1889], .c 11, .c 3, .c 5, .c 7, .c 3,
  .p pv29 [pv2,pv5,pv17,pv23357], .c 1129, .c 3, .c 23, .c 191, .c 3, .c 11, .c 5, .c 3, .c 29,
  .p pv37 [pv2,pv3,pv5,pv44119], .c 3, .c 5, .c 491, .c 3, .c 347, .p pv3 [pv2,pv3,pv7,pv94541],
  .c 3, .c 41, .c 7, .c 3, .c 13, .c 5, .c 3, .p pv2 [pv2,pv29,pv223,pv307], .c 17, .c 3, .c 5,
  .c 11, .c 3, .p pv7 [pv2,pv5,pv7,pv2269], .c 19, .c 3, .c 7, .c 13, .c 3,
  .p pv2 [pv2,pv73,pv27197], .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 79, .c 3,
  .p pv2 [pv2,pv5,pv11,pv18049], .c 379, .c 3, .p pv2 [pv2,pv233,pv8521], .c 23, .c 3,
  .p pv5 [pv2,pv7,pv17,pv43,pv97], .c 5, .c 3, .c 7, .p pv31 [pv2,pv3,pv5,pv1103], .c 3, .c 5,
  .c 601, .c 3, .c 13, .c 7, .c 3, .c 71, .p pv2 [pv2,pv3,pv59,pv3739], .c 3,
  .p pv5 [pv2,pv67,pv29633], .c 5, .c 3, .c 19, .p pv3 [pv2,pv3,pv5,pv132361], .c 3, .c 5, .c 13,
  .c 3, .c 7, .c 17, .c 3, .c 151, .p pv61 [pv2,pv3,pv7,pv19,pv311], .c 3, .c 557, .c 5, .c 3,
  .p pv2 [pv2,pv23,pv86323], .c 1171, .c 3, .c 5, .c 19, .c 3, .c 337, .c 457, .c 3, .c 17, .c 11,
  .c 3, .c 7, .c 5, .c 3, .c 13, .c 41, .c 3, .c 5, .c 7, .c 3, .c 11,
  .p pv3 [pv2,pv3,pv13,pv50909], .c 3,
]
private theorem h0485c15 : checkBlock 3970651 128 b0485c15 = true := by
  decide +kernel

private def b0485c16 : List Row := [
  .c 257, .c 127, .c 3, .c 89, .c 5, .c 3, .c 53, .c 43, .c 3, .c 5, .c 23, .c 3, .c 1747, .c 113,
  .c 3, .c 991, .c 7, .c 3, .c 19, .c 5, .c 3, .p pv2 [pv2,pv992737], .c 37, .c 3, .c 5, .c 241,
  .c 3, .c 223, .c 271, .c 3, .c 7, .c 83, .c 3, .c 23, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5,
  .c 839, .c 3, .p pv13 [pv2,pv5,pv397099], .c 13, .c 3, .p pv2 [pv2,pv17,pv23,pv2539], .c 29,
  .c 3, .c 131, .c 5, .c 3, .c 7, .c 11, .c 3, .c 5, .c 101, .c 3, .c 1553, .c 7, .c 3,
  .p pv2 [pv2,pv1985513], .c 293, .c 3, .c 11, .c 5, .c 3, .c 61, .p pv11 [pv2,pv3,pv5,pv8273],
  .c 3, .c 5, .c 17, .c 3, .c 7, .p pv2 [pv2,pv3,pv83,pv443], .c 3, .c 19, .c 317, .c 3,
  .p pv5 [pv2,pv37,pv103,pv521], .c 5, .c 3, .c 31, .c 13, .c 3, .c 5, .c 11, .c 3, .c 17, .c 97,
  .c 3, .p pv7 [pv2,pv7,pv29,pv9781], .c 229, .c 3, .c 7, .c 5, .c 3, .c 11, .c 71, .c 3, .c 5,
  .c 7, .c 3, .c 23, .c 59, .c 3, .p pv2 [pv2,pv769,pv1291], .p pv3 [pv2,pv3,pv101,pv6553], .c 3,
  .c 13, .c 5, .c 3, .p pv3 [pv2,pv7,pv70913], .c 31, .c 3, .c 5, .c 41, .c 3,
  .p pv2 [pv2,pv5,pv181,pv1097], .c 11, .c 3, .p pv2 [pv2,pv1985573], .c 7, .c 3,
  .p pv3 [pv2,pv19,pv13063], .c 5, .c 3, .c 113, .c 61,
]
private theorem h0485c16 : checkBlock 3970907 128 b0485c16 = true := by
  decide +kernel

private def b0485c17 : List Row := [
  .c 3, .c 5, .p pv3 [pv2,pv3,pv17,pv38933], .c 3, .c 19, .c 29, .c 3, .c 7, .c 43, .c 3, .c 17,
  .c 5, .c 3, .c 1901, .c 7, .c 3, .c 5, .c 109, .c 3, .c 13, .c 23, .c 3,
  .p pv5 [pv2,pv1231,pv1613], .c 11, .c 3, .p pv2 [pv2,pv7,pv141829], .c 5, .c 3, .c 7, .c 1741,
  .c 3, .c 5, .c 13, .c 3, .c 11, .c 7, .c 3, .c 53, .p pv3 [pv2,pv3,pv661873], .c 3, .c 71, .c 5,
  .c 3, .c 23, .c 17, .c 3, .c 5, .p pv19 [pv2,pv3,pv165469], .c 3, .c 7,
  .p pv3 [pv2,pv3,pv661877], .c 3, .p pv2 [pv2,pv13,pv19,pv8039], .c 89, .c 3, .c 73, .c 5, .c 3,
  .c 13, .p pv7 [pv2,pv3,pv5,pv16547], .c 3, .c 5, .p pv11 [pv2,pv3,pv11,pv31,pv647], .c 3, .c 67,
  .c 421, .c 3, .c 11, .p pv2 [pv2,pv3,pv661883], .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv43,pv2099], .p pv7 [pv2,pv3,pv5,pv7,pv18911], .c 3, .c 5, .c 7, .c 3, .c 37,
  .c 19, .c 3, .c 383, .c 1109, .c 3, .p pv2 [pv2,pv163,pv6091], .c 5, .c 3, .c 283, .c 11, .c 3,
  .c 5, .c 29, .c 3, .c 43, .c 17, .c 3, .c 13, .c 7, .c 3, .c 11, .c 5, .c 3, .c 139, .c 103,
  .c 3, .c 5, .p pv13 [pv2,pv3,pv29,pv317], .c 3, .c 809, .c 13, .c 3, .c 7, .c 479, .c 3,
  .p pv3 [pv2,pv62053], .c 5, .c 3, .c 19, .c 7, .c 3, .c 5, .c 11, .c 3,
  .p pv2 [pv2,pv5,pv23,pv31,pv557], .p pv2 [pv2,pv3,pv107,pv1031], .c 3, .c 127,
]
private theorem h0485c17 : checkBlock 3971163 128 b0485c17 = true := by
  decide +kernel

private def b0485c18 : List Row := [
  .c 73, .c 3, .p pv5 [pv2,pv7,pv13,pv21821], .c 5, .c 3, .c 7, .p pv3 [pv2,pv3,pv5,pv4903], .c 3,
  .c 5, .c 19, .c 3, .c 31, .c 7, .c 3, .c 89, .c 53, .c 3, .c 47, .c 5, .c 3,
  .p pv2 [pv2,pv1985729], .c 13, .c 3, .c 5, .c 59, .c 3, .c 7, .c 11, .c 3,
  .p pv2 [pv2,pv433,pv2293], .c 23, .c 3, .p pv2 [pv2,pv1985741], .c 5, .c 3, .c 17, .c 577, .c 3,
  .c 5, .c 1193, .c 3, .p pv2 [pv2,pv5,pv13,pv47], .c 31, .c 3, .c 1627, .c 1319, .c 3, .c 7,
  .c 5, .c 3, .c 107, .c 29, .c 3, .c 5, .c 7, .c 3, .p pv11 [pv2,pv5,pv397153],
  .p pv5 [pv2,pv3,pv19,pv17419], .c 3, .p pv3 [pv2,pv89,pv2789], .c 11, .c 3, .c 37, .c 5, .c 3,
  .p pv2 [pv2,pv7,pv23,pv881], .c 19, .c 3, .c 5, .c 17, .c 3, .c 11, .c 263, .c 3, .c 79, .c 7,
  .c 3, .c 251, .c 5, .c 3, .c 29, .p pv2 [pv2,pv3,pv5,pv37,pv1789], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv661931], .c 3, .c 13, .c 1423, .c 3, .c 7, .p pv7 [pv2,pv3,pv71,pv9323], .c 3,
  .c 353, .c 5, .c 3, .c 43, .c 7, .c 3, .c 5, .c 13, .c 3, .p pv2 [pv2,pv5,pv349,pv569], .c 101,
  .c 3, .c 11, .c 41, .c 3, .c 83, .c 5, .c 3, .c 7, .c 47, .c 3, .c 5, .c 139, .c 3,
  .p pv13 [pv2,pv5,pv79433], .c 7, .c 3, .c 313, .c 17, .c 3, .c 23, .c 5, .c 3, .c 13, .c 11,
  .c 3,
]
private theorem h0485c18 : checkBlock 3971419 128 b0485c18 = true := by
  decide +kernel

private def b0485c19 : List Row := [
  .c 5, .p pv11 [pv2,pv3,pv17,pv19469], .c 3, .c 7, .c 181, .c 3, .p pv5 [pv2,pv23,pv86341],
  .c 31, .c 3, .c 11, .c 5, .c 3, .c 491, .c 419, .c 3, .c 5, .c 1201, .c 3, .c 41,
  .p pv5 [pv2,pv3,pv10343], .c 3, .c 197, .p pv3 [pv2,pv3,pv233,pv947], .c 3, .c 7, .c 5, .c 3,
  .c 1051, .p pv2 [pv2,pv3,pv5,pv7,pv18913], .c 3, .c 5, .c 7, .c 3, .c 19,
  .p pv47 [pv2,pv3,pv109,pv6073], .c 3, .c 13, .p pv2 [pv2,pv3,pv11,pv30089], .c 3, .c 29, .c 5,
  .c 3, .c 11, .c 17, .c 3, .c 5, .c 53, .c 3, .c 61, .c 13, .c 3, .c 1487, .c 7, .c 3, .c 103,
  .c 5, .c 3, .c 131, .p pv23 [pv2,pv3,pv5,pv44131], .c 3, .c 5, .p pv5 [pv2,pv3,pv330983], .c 3,
  .c 23, .c 11, .c 3, .c 7, .p pv11 [pv2,pv3,pv4597], .c 3, .c 31, .c 5, .c 3, .c 227, .c 7, .c 3,
  .c 5, .c 67, .c 3, .c 179, .p pv5 [pv2,pv3,pv61,pv2713], .c 3, .c 113, .c 37, .c 3,
  .p pv2 [pv2,pv7,pv40529], .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 73, .c 3,
  .p pv3 [pv2,pv5,pv198593], .c 7, .c 3, .c 43, .c 11, .c 3, .c 53, .c 5, .c 3,
  .p pv7 [pv2,pv1985939], .p pv23 [pv2,pv3,pv5,pv11,pv17,pv59], .c 3, .c 5,
  .p pv3 [pv2,pv3,pv103,pv6427], .c 3, .c 7, .c 19, .c 3, .c 17, .p pv2 [pv2,pv3,pv7,pv29,pv1087],
  .c 3, .c 13, .c 5, .c 3, .c 433, .p pv3 [pv2,pv3,pv5,pv43,pv3079], .c 3, .c 5,
  .p pv2 [pv2,pv3,pv13,pv23,pv41], .c 3, .c 241, .c 47, .c 3, .c 29, .c 13,
]
private theorem h0485c19 : checkBlock 3971675 128 b0485c19 = true := by
  decide +kernel

private def b0485c20 : List Row := [
  .c 3, .c 7, .c 5, .c 3, .c 23, .c 239, .c 3, .c 5, .c 7, .c 3, .c 233, .c 43, .c 3, .c 11,
  .c 677, .c 3, .p pv2 [pv2,pv23,pv79,pv1093], .c 5, .c 3, .c 19, .c 1409, .c 3, .c 5,
  .p pv17 [pv2,pv3,pv359,pv461], .c 3, .c 13, .p pv3 [pv2,pv3,pv7,pv17,pv5563], .c 3, .c 37, .c 7,
  .c 3, .p pv3 [pv2,pv496499], .c 5, .c 3, .c 17, .c 11, .c 3, .c 5, .c 13, .c 3,
  .p pv2 [pv2,pv5,pv7,pv179,pv317], .c 1987, .c 3, .c 7, .p pv2 [pv2,pv3,pv662003], .c 3, .c 11,
  .c 5, .c 3, .p pv2 [pv2,pv67,pv14821], .c 7, .c 3, .c 5, .p pv2 [pv2,pv3,pv191,pv1733], .c 3,
  .c 79, .c 29, .c 3, .c 271, .c 1993, .c 3, .c 97, .c 5, .c 3, .c 7, .c 31, .c 3, .c 5, .c 11,
  .c 3, .p pv11 [pv2,pv5,pv89,pv4463], .c 7, .c 3, .c 23, .c 389, .c 3, .c 19, .c 5, .c 3, .c 11,
  .p pv7 [pv2,pv3,pv5,pv132403], .c 3, .c 5, .c 1039, .c 3, .c 7, .p pv3 [pv2,pv3,pv19,pv34843],
  .c 3, .p pv2 [pv2,pv1986053], .c 347, .c 3, .p pv3 [pv2,pv248257], .c 5, .c 3,
  .p pv7 [pv2,pv17,pv116827], .c 19, .c 3, .c 5, .c 733, .c 3, .c 83, .c 11, .c 3, .c 13,
  .p pv2 [pv2,pv3,pv53,pv12491], .c 3, .c 7, .c 5, .c 3, .c 73,
  .p pv3 [pv2,pv3,pv5,pv7,pv13,pv97], .c 3, .c 5, .c 7, .c 3, .c 107, .c 13, .c 3,
  .p pv5 [pv2,pv11,pv71,pv2543], .c 17, .c 3, .p pv2 [pv2,pv37,pv26839], .c 5, .c 3, .c 127,
  .p pv7 [pv2,pv3,pv5,pv239,pv277], .c 3, .c 5,
]
private theorem h0485c20 : checkBlock 3971931 128 b0485c20 = true := by
  decide +kernel

private def b0485c21 : List Row := [
  .p pv3 [pv2,pv3,pv17,pv4327], .c 3, .c 53, .p pv17 [pv2,pv3,pv7,pv23,pv257], .c 3, .c 19, .c 7,
  .c 3, .c 17, .c 5, .c 3, .c 37, .c 43, .c 3, .c 5, .c 29, .c 3, .c 11,
  .p pv5 [pv2,pv3,pv73,pv3023], .c 3, .c 7, .c 67, .c 3, .p pv3 [pv2,pv11,pv45139], .c 5, .c 3,
  .c 199, .c 7, .c 3, .c 5, .c 31, .c 3, .p pv2 [pv2,pv5,pv15889], .c 173, .c 3, .c 157, .c 61,
  .c 3, .p pv7 [pv2,pv7,pv167,pv1699], .c 5, .c 3, .c 7, .c 17, .c 3, .c 5, .c 641, .c 3, .c 1907,
  .c 7, .c 3, .c 11, .c 113, .c 3, .c 13, .c 5, .c 3, .c 47, .p pv13 [pv2,pv3,pv5,pv13241], .c 3,
  .c 5, .c 23, .c 3, .c 7, .c 131, .c 3, .c 1823, .c 13, .c 3, .c 269, .c 5, .c 3,
  .p pv3 [pv2,pv683,pv727], .c 11, .c 3, .c 5, .c 89, .c 3, .p pv2 [pv2,pv5,pv31,pv43,pv149],
  .p pv3 [pv2,pv3,pv11,pv139,pv433], .c 3, .c 479, .c 19, .c 3, .c 7, .c 5, .c 3,
  .p pv23 [pv2,pv13,pv152783], .c 971, .c 3, .c 5, .c 7, .c 3, .c 13, .c 17, .c 3,
  .p pv3 [pv2,pv23,pv21589], .c 71, .c 3, .c 43, .c 5, .c 3, .c 863, .c 29, .c 3, .c 5, .c 11,
  .c 3, .c 103, .c 53, .c 3, .c 17, .c 7, .c 3, .p pv2 [pv2,pv993103], .c 5, .c 3, .c 11, .c 853,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv43,pv89,pv173], .c 3, .c 37, .c 31, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv199,pv1109], .c 3,
]
private theorem h0485c21 : checkBlock 3972187 128 b0485c21 = true := by
  decide +kernel

private def b0485c22 : List Row := [
  .c 1031, .c 5, .c 3, .c 13, .c 7, .c 3, .c 5, .c 277, .c 3, .c 1667, .c 11, .c 3,
  .p pv2 [pv2,pv1986233], .c 43, .c 3, .c 163, .c 5, .c 3, .c 7, .c 139, .c 3, .c 5, .c 47, .c 3,
  .c 23, .c 7, .c 3, .c 67, .p pv13 [pv2,pv3,pv662083], .c 3, .c 61, .c 5, .c 3, .c 17, .c 439,
  .c 3, .c 5, .p pv2 [pv2,pv3,pv331043], .c 3, .c 7, .p pv2 [pv2,pv3,pv223,pv2969], .c 3, .c 13,
  .c 11, .c 3, .p pv2 [pv2,pv101,pv9833], .c 5, .c 3, .c 19, .p pv2 [pv2,pv3,pv5,pv11,pv13,pv463],
  .c 3, .c 5, .c 179, .c 3, .c 11, .c 13, .c 3, .c 31, .c 691, .c 3, .c 7, .c 5, .c 3,
  .p pv3 [pv2,pv599,pv829], .c 157, .c 3, .c 5, .c 7, .c 3, .c 47, .c 23, .c 3, .c 73, .c 107,
  .c 3, .p pv3 [pv2,pv13,pv71,pv269], .c 5, .c 3, .c 173, .p pv11 [pv2,pv3,pv5,pv2207], .c 3,
  .c 5, .c 103, .c 3, .c 17, .c 41, .c 3, .c 11, .c 7, .c 3, .c 29, .c 5, .c 3, .c 23, .c 13,
  .c 3, .c 5, .c 199, .c 3, .c 43, .p pv2 [pv2,pv3,pv662107], .c 3, .c 7,
  .p pv11 [pv2,pv3,pv165527], .c 3, .c 19, .c 5, .c 3, .c 151, .c 7, .c 3, .c 5, .c 349, .c 3,
  .p pv37 [pv2,pv5,pv13,pv30559], .c 79, .c 3, .c 1697, .c 17, .c 3, .c 11, .c 5, .c 3, .c 7,
  .c 19, .c 3, .c 5, .p pv23 [pv2,pv3,pv7,pv13,pv17,pv107],
]
private theorem h0485c22 : checkBlock 3972443 128 b0485c22 = true := by
  decide +kernel

private def b0485c23 : List Row := [
  .c 3, .c 457, .c 7, .c 3, .c 401, .c 13, .c 3, .c 17, .c 5, .c 3, .c 673, .c 23, .c 3, .c 5,
  .c 11, .c 3, .c 7, .c 73, .c 3, .p pv3 [pv2,pv41,pv757], .c 29, .c 3, .c 31, .c 5, .c 3, .c 11,
  .p pv29 [pv2,pv3,pv5,pv5297], .c 3, .c 5, .p pv2 [pv2,pv3,pv331063], .c 3, .c 13, .c 167, .c 3,
  .c 19, .c 47, .c 3, .c 7, .c 5, .c 3, .c 397, .c 17, .c 3, .c 5, .c 7, .c 3,
  .p pv7 [pv2,pv5,pv23,pv751], .c 11, .c 3, .c 29, .c 163, .c 3, .c 107, .c 5, .c 3,
  .p pv3 [pv2,pv7,pv61,pv1163], .p pv2 [pv2,pv3,pv5,pv151,pv877], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv47,pv587], .c 3, .c 743, .c 373, .c 3, .c 53, .c 7, .c 3,
  .p pv3 [pv2,pv17,pv67,pv109], .c 5, .c 3, .c 13, .p pv7 [pv2,pv3,pv5,pv33107], .c 3, .c 5,
  .c 1303, .c 3, .p pv2 [pv2,pv5,pv7,pv11351], .c 613, .c 3, .c 7, .c 11, .c 3, .c 47, .c 5, .c 3,
  .c 61, .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv71,pv4663], .c 3, .c 11, .c 17, .c 3, .c 307,
  .c 1187, .c 3, .c 337, .c 5, .c 3, .c 7, .p pv23 [pv2,pv3,pv5,pv17,pv19,pv41], .c 3, .c 5,
  .c 1663, .c 3, .p pv23 [pv2,pv5,pv47,pv79,pv107], .c 7, .c 3, .c 13, .c 19, .c 3,
  .p pv2 [pv2,pv1986461], .c 5, .c 3, .c 31, .p pv2 [pv2,pv3,pv5,pv13,pv61,pv167], .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv101,pv149], .c 3, .c 7, .c 13, .c 3, .c 11, .c 37, .c 3,
  .p pv3 [pv2,pv73,pv6803],
]
private theorem h0485c23 : checkBlock 3972699 128 b0485c23 = true := by
  decide +kernel

private def b0485c24 : List Row := [
  .c 5, .c 3, .p pv7 [pv2,pv11,pv419,pv431], .c 83, .c 3, .c 5, .c 113, .c 3, .c 29,
  .p pv2 [pv2,pv3,pv331081], .c 3, .c 421, .p pv2 [pv2,pv3,pv220721], .c 3, .c 7, .c 5, .c 3,
  .c 79, .c 11, .c 3, .c 5, .c 7, .c 3, .c 59, .c 463, .c 3, .p pv5 [pv2,pv1103,pv1801],
  .p pv7 [pv2,pv3,pv13,pv6367], .c 3, .c 11, .c 5, .c 3, .c 17, .c 13, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv409,pv1619], .c 3, .p pv17 [pv2,pv5,pv397303], .c 19, .c 3, .c 101, .c 7,
  .c 3, .c 23, .c 5, .c 3, .c 89, .c 47, .c 3, .c 5, .c 11, .c 3,
  .p pv29 [pv2,pv5,pv7,pv13,pv37,pv59], .p pv3 [pv2,pv3,pv662177], .c 3, .c 7, .c 1249, .c 3,
  .c 13, .c 5, .c 3, .c 11, .c 7, .c 3, .c 5, .c 17, .c 3, .c 563, .p pv2 [pv2,pv3,pv53,pv6247],
  .c 3, .c 37, .c 13, .c 3, .p pv5 [pv2,pv7,pv283793], .c 5, .c 3, .c 7, .c 659, .c 3, .c 5,
  .p pv13 [pv2,pv3,pv7,pv29,pv233], .c 3, .c 17, .c 7, .c 3, .c 83, .p pv7 [pv2,pv3,pv19,pv8713],
  .c 3, .p pv2 [pv2,pv993283], .c 5, .c 3, .p pv2 [pv2,pv13,pv17,pv89,pv101], .c 263, .c 3, .c 5,
  .c 19, .c 3, .c 7, .p pv5 [pv2,pv3,pv41387], .c 3, .c 43, .c 109, .c 3, .p pv2 [pv2,pv1986581],
  .c 5, .c 3, .c 1117, .c 37, .c 3, .c 5, .c 13, .c 3, .c 23, .p pv5 [pv2,pv3,pv191,pv3467], .c 3,
  .c 41, .c 11, .c 3, .c 7, .c 5, .c 3, .c 157, .c 449, .c 3, .c 5, .c 7, .c 3,
]
private theorem h0485c24 : checkBlock 3972955 128 b0485c24 = true := by
  decide +kernel

private def b0485c25 : List Row := [
  .c 11, .p pv2 [pv2,pv3,pv12263], .c 3, .c 97, .p pv3 [pv2,pv3,pv662203], .c 3, .c 17, .c 5,
  .c 3, .c 13, .c 71, .c 3, .c 5, .c 59, .c 3, .p pv3 [pv2,pv5,pv17,pv5843], .c 43, .c 3,
  .p pv5 [pv2,pv389,pv5107], .c 7, .c 3, .p pv2 [pv2,pv863,pv1151], .c 5, .c 3,
  .p pv2 [pv2,pv1986629], .c 19, .c 3, .c 5, .c 443, .c 3, .c 661, .c 23, .c 3, .c 7,
  .p pv3 [pv2,pv3,pv317,pv2089], .c 3, .p pv2 [pv2,pv37,pv53693], .c 5, .c 3,
  .p pv7 [pv2,pv11,pv163,pv277], .c 7, .c 3, .c 5, .p pv5 [pv2,pv3,pv23,pv59,pv61], .c 3, .c 31,
  .p pv3 [pv2,pv3,pv71,pv3109], .c 3, .c 13, .p pv2 [pv2,pv3,pv17,pv19477], .c 3, .c 677, .c 5,
  .c 3, .c 7, .c 11, .c 3, .c 5, .c 569, .c 3, .p pv13 [pv2,pv5,pv251,pv1583], .c 7, .c 3, .c 19,
  .p pv2 [pv2,pv3,pv107,pv2063], .c 3, .c 11, .c 5, .c 3, .c 233, .c 41, .c 3, .c 5, .c 53, .c 3,
  .c 7, .c 31, .c 3, .c 241, .c 1789, .c 3, .c 71, .c 5, .c 3, .c 229,
  .p pv2 [pv2,pv3,pv5,pv47,pv1409], .c 3, .c 5, .c 11, .c 3, .p pv7 [pv2,pv5,pv73,pv5443], .c 17,
  .c 3, .c 829, .c 269, .c 3, .c 7, .c 5, .c 3, .c 11, .c 13, .c 3, .c 5, .c 7, .c 3,
  .p pv2 [pv2,pv5,pv11,pv18061], .c 769, .c 3, .c 17, .p pv2 [pv2,pv3,pv36791], .c 3, .c 41, .c 5,
  .c 3, .p pv7 [pv2,pv7,pv283817], .c 101, .c 3, .c 5, .p pv7 [pv2,pv3,pv220747], .c 3, .c 19,
  .c 11, .c 3, .c 23, .c 7, .c 3, .c 13, .c 5,
]
private theorem h0485c25 : checkBlock 3973211 128 b0485c25 = true := by
  decide +kernel

private def b0485c26 : List Row := [
  .c 3, .p pv2 [pv2,pv993367], .c 1693, .c 3, .c 5, .c 257, .c 3, .p pv3 [pv2,pv5,pv7,pv23,pv617],
  .p pv2 [pv2,pv3,pv73583], .c 3, .c 7, .c 13, .c 3, .c 29, .c 5, .c 3, .p pv2 [pv2,pv1986749],
  .c 7, .c 3, .c 5, .c 1523, .c 3, .p pv11 [pv2,pv5,pv397351], .c 157, .c 3,
  .p pv2 [pv2,pv53,pv18743], .c 11, .c 3, .c 1481, .c 5, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv5,pv11,pv12041], .c 3, .c 5, .c 499, .c 3, .c 11, .c 7, .c 3, .c 1109, .c 23,
  .c 3, .p pv3 [pv2,pv11,pv107,pv211], .c 5, .c 3, .c 641, .p pv13 [pv2,pv3,pv5,pv33113], .c 3,
  .c 5, .c 13, .c 3, .c 7, .c 397, .c 3, .p pv3 [pv2,pv127,pv3911],
  .p pv3 [pv2,pv3,pv7,pv37,pv2557], .c 3, .c 89, .c 5, .c 3, .c 571, .c 59, .c 3, .c 5, .c 17,
  .c 3, .c 61, .c 19, .c 3, .c 11, .c 29, .c 3, .c 7, .c 5, .c 3, .c 13, .c 79, .c 3, .c 5, .c 7,
  .c 3, .c 17, .p pv7 [pv2,pv3,pv13,pv199], .c 3, .c 103, .p pv3 [pv2,pv3,pv29,pv41,pv557], .c 3,
  .c 101, .c 5, .c 3, .p pv29 [pv2,pv7,pv17,pv2087], .c 11, .c 3, .c 5, .c 71, .c 3,
  .p pv2 [pv2,pv5,pv19,pv10457], .c 491, .c 3, .c 29, .c 7, .c 3, .c 11, .c 5, .c 3, .c 19,
  .c 149, .c 3, .c 5, .c 23, .c 3, .p pv2 [pv2,pv5,pv7,pv56767], .c 593, .c 3, .c 7, .c 17, .c 3,
  .c 67, .c 5, .c 3, .c 47, .c 7, .c 3, .c 5, .c 11, .c 3, .c 353,
]
private theorem h0485c26 : checkBlock 3973467 128 b0485c26 = true := by
  decide +kernel

private def b0485c27 : List Row := [
  .c 13, .c 3, .p pv5 [pv2,pv37,pv53699], .p pv13 [pv2,pv3,pv11,pv53,pv71], .c 3, .c 17, .c 5,
  .c 3, .c 7, .p pv2 [pv2,pv3,pv5,pv103,pv643], .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv94613], .c 3,
  .p pv11 [pv2,pv5,pv11,pv17], .c 7, .c 3, .p pv2 [pv2,pv23,pv47,pv919], .c 43, .c 3, .c 37, .c 5,
  .c 3, .c 1733, .c 359, .c 3, .c 5, .c 163, .c 3, .c 7, .c 11, .c 3, .p pv2 [pv2,pv1986893],
  .c 1721, .c 3, .c 19, .c 5, .c 3, .c 71, .c 13, .c 3, .c 5, .p pv3 [pv2,pv3,pv73589], .c 3,
  .p pv2 [pv2,pv5,pv173,pv2297], .c 109, .c 3, .c 937, .c 421, .c 3, .c 7, .c 5, .c 3,
  .p pv2 [pv2,pv31,pv73,pv439], .c 19, .c 3, .c 5, .c 7, .c 3, .c 29, .c 41, .c 3,
  .p pv5 [pv2,pv1986923], .c 11, .c 3, .c 13, .c 5, .c 3, .c 31, .p pv2 [pv2,pv3,pv5,pv11,pv223],
  .c 3, .c 5, .c 151, .c 3, .c 11, .c 107, .c 3, .p pv2 [pv2,pv367,pv2707], .c 7, .c 3, .c 1193,
  .c 5, .c 3, .c 1669, .c 1559, .c 3, .c 5, .c 47, .c 3, .c 73, .c 17, .c 3, .c 7, .c 857, .c 3,
  .c 719, .c 5, .c 3, .p pv11 [pv2,pv13,pv152843], .c 7, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv11,pv19,pv3169], .c 3, .c 13, .p pv2 [pv2,pv3,pv167,pv661], .c 3, .c 11,
  .c 89, .c 3, .p pv5 [pv2,pv7,pv373,pv761], .c 5, .c 3, .c 7, .c 1033, .c 3, .c 5, .c 13, .c 3,
  .c 1699, .c 7, .c 3, .c 61, .c 701, .c 3, .p pv2 [pv2,pv993493], .c 5, .c 3,
]
private theorem h0485c27 : checkBlock 3973723 128 b0485c27 = true := by
  decide +kernel

private def b0485c28 : List Row := [
  .c 149, .c 11, .c 3, .c 5, .c 1289, .c 3, .c 7, .c 53, .c 3, .p pv2 [pv2,pv13,pv76423], .c 1013,
  .c 3, .c 11, .c 5, .c 3, .c 13, .c 1949, .c 3, .c 5, .c 43, .c 3, .c 19,
  .p pv11 [pv2,pv3,pv13,pv17,pv37], .c 3, .p pv2 [pv2,pv7,pv283859], .c 607, .c 3, .c 7, .c 5,
  .c 3, .c 17, .p pv13 [pv2,pv3,pv5,pv7,pv19,pv83], .c 3, .c 5, .c 7, .c 3, .c 1753,
  .p pv5 [pv2,pv3,pv331171], .c 3, .p pv3 [pv2,pv17,pv29221], .c 19, .c 3, .c 59, .c 5, .c 3,
  .c 11, .p pv23 [pv2,pv3,pv5,pv132469], .c 3, .c 5, .p pv2 [pv2,pv3,pv31,pv1187], .c 3, .c 197,
  .c 71, .c 3, .c 13, .c 7, .c 3, .p pv2 [pv2,pv239,pv4157], .c 5, .c 3, .c 53, .c 23, .c 3, .c 5,
  .c 17, .c 3, .c 1607, .c 11, .c 3, .c 7, .c 277, .c 3, .c 83, .c 5, .c 3,
  .p pv3 [pv2,pv149,pv1667], .c 7, .c 3, .c 5, .c 191, .c 3, .c 17, .p pv3 [pv2,pv3,pv662357],
  .c 3, .c 23, .c 139, .c 3, .c 443, .c 5, .c 3, .c 7, .c 313, .c 3, .c 5,
  .p pv3 [pv2,pv3,pv7,pv31541], .c 3, .c 41, .c 7, .c 3, .p pv3 [pv2,pv124193], .c 11, .c 3,
  .c 281, .c 5, .c 3, .c 29, .c 13, .c 3, .c 5, .p pv2 [pv2,pv3,pv331183], .c 3, .c 7, .c 503,
  .c 3, .c 37, .c 17, .c 3, .p pv2 [pv2,pv11,pv41,pv2203], .c 5, .c 3, .p pv2 [pv2,pv29,pv68521],
  .p pv2 [pv2,pv3,pv5,pv22079], .c 3, .c 5, .p pv3 [pv2,pv3,pv17,pv47,pv829], .c 3, .c 31, .c 137,
]
private theorem h0485c28 : checkBlock 3973979 128 b0485c28 = true := by
  decide +kernel

private def b0485c29 : List Row := [
  .c 3, .p pv3 [pv2,pv7,pv141937], .c 23, .c 3, .c 7, .c 5, .c 3, .c 19, .c 431, .c 3, .c 5, .c 7,
  .c 3, .p pv2 [pv2,pv5,pv17,pv11689], .c 479, .c 3, .c 11, .c 13, .c 3, .c 47, .c 5, .c 3,
  .p pv11 [pv2,pv7,pv11,pv131,pv197], .c 37, .c 3, .c 5, .c 19, .c 3, .p pv2 [pv2,pv5,pv397429],
  .c 31, .c 3, .c 1123, .c 7, .c 3, .c 971, .c 5, .c 3, .p pv2 [pv2,pv13,pv23,pv3323], .c 11,
  .c 3, .c 5, .c 331, .c 3, .c 13, .c 113, .c 3, .c 7, .c 173, .c 3, .c 11, .c 5, .c 3, .c 73,
  .c 7, .c 3, .c 5, .c 13, .c 3, .p pv17 [pv2,pv5,pv101,pv787], .p pv5 [pv2,pv3,pv82799], .c 3,
  .p pv2 [pv2,pv993589], .p pv7 [pv2,pv3,pv59,pv103,pv109], .c 3, .c 19, .c 5, .c 3, .c 7,
  .p pv11 [pv2,pv3,pv5,pv137,pv967], .c 3, .c 5, .c 11, .c 3, .c 97, .c 7, .c 3,
  .p pv2 [pv2,pv13,pv31,pv4931], .p pv2 [pv2,pv3,pv11,pv30109], .c 3,
  .p pv3 [pv2,pv29,pv37,pv463], .c 5, .c 3, .c 11, .c 19, .c 3, .c 5, .c 487, .c 3, .c 7, .c 17,
  .c 3, .c 31, .p pv2 [pv2,pv3,pv7,pv31543], .c 3, .c 23, .c 5, .c 3, .c 37, .c 1097, .c 3, .c 5,
  .p pv5 [pv2,pv3,pv113,pv977], .c 3, .p pv3 [pv2,pv5,pv67,pv1483], .c 11, .c 3, .c 17, .c 193,
  .c 3, .c 7, .c 5, .c 3, .p pv2 [pv2,pv19,pv41,pv2551], .c 47, .c 3, .c 5, .c 7, .c 3, .c 151,
  .c 89, .c 3, .c 13, .c 29, .c 3, .p pv2 [pv2,pv1987241], .c 5, .c 3, .c 359,
]
private theorem h0485c29 : checkBlock 3974235 128 b0485c29 = true := by
  decide +kernel

private def b0485c30 : List Row := [
  .p pv43 [pv2,pv3,pv5,pv13,pv43,pv79], .c 3, .c 5, .p pv5 [pv2,pv3,pv19,pv2179], .c 3,
  .p pv2 [pv2,pv5,pv7949], .c 13, .c 3, .c 67, .c 7, .c 3, .c 1091, .c 5, .c 3, .c 191, .c 647,
  .c 3, .c 5, .p pv3 [pv2,pv3,pv220807], .c 3, .c 11, .c 43, .c 3, .c 7,
  .p pv2 [pv2,pv3,pv23,pv83,pv347], .c 3, .c 227, .c 5, .c 3, .c 17, .c 7, .c 3, .c 5, .c 1063,
  .c 3, .c 23, .p pv2 [pv2,pv3,pv89,pv827], .c 3, .p pv5 [pv2,pv17,pv29,pv139], .c 79, .c 3,
  .c 379, .c 5, .c 3, .c 7, .c 13, .c 3, .c 5, .c 1307, .c 3, .c 19, .c 7, .c 3, .c 11, .c 619,
  .c 3, .c 31, .c 5, .c 3, .p pv3 [pv2,pv11,pv2053], .p pv2 [pv2,pv3,pv5,pv19,pv367], .c 3, .c 5,
  .c 17, .c 3, .c 7, .p pv3 [pv2,pv3,pv41,pv107,pv151], .c 3, .c 199, .c 19, .c 3, .c 13, .c 5,
  .c 3, .c 797, .c 11, .c 3, .c 5, .c 887, .c 3, .c 17, .c 23, .c 3, .p pv3 [pv2,pv7,pv1109],
  .c 13, .c 3, .c 7, .c 5, .c 3, .c 631, .c 131, .c 3, .c 5, .c 7, .c 3, .p pv3 [pv2,pv5,pv99367],
  .p pv2 [pv2,pv3,pv29,pv53,pv431], .c 3, .p pv5 [pv2,pv19,pv104597], .p pv7 [pv2,pv3,pv37,pv373],
  .c 3, .c 911, .c 5, .c 3, .c 23, .p pv2 [pv2,pv3,pv5,pv13249], .c 3, .c 5, .c 11, .c 3, .c 13,
  .p pv5 [pv2,pv3,pv7,pv59,pv401], .c 3, .p pv2 [pv2,pv993679], .c 7, .c 3,
  .p pv2 [pv2,pv23,pv71,pv1217], .c 5, .c 3, .c 11, .c 571, .c 3, .c 5, .c 13, .c 3,
  .p pv23 [pv2,pv5,pv7,pv11,pv29,pv89], .c 19, .c 3,
]
private theorem h0485c30 : checkBlock 3974491 128 b0485c30 = true := by
  decide +kernel

private def b0485c31 : List Row := [
  .c 7, .p pv31 [pv2,pv3,pv43,pv7703], .c 3, .c 17, .c 5, .c 3, .p pv17 [pv2,pv31,pv64109], .c 7,
  .c 3, .c 5, .c 167, .c 3, .c 59, .c 11, .c 3, .c 73, .p pv2 [pv2,pv3,pv73607], .c 3,
  .p pv5 [pv2,pv7,pv40559], .c 5, .c 3, .c 7, .c 23, .c 3, .c 5, .p pv2 [pv2,pv3,pv7,pv15773],
  .c 3, .p pv3 [pv2,pv5,pv19,pv523], .c 7, .c 3, .c 1801, .c 239, .c 3, .c 241, .c 5, .c 3, .c 19,
  .c 17, .c 3, .c 5, .c 29, .c 3, .c 7, .p pv5 [pv2,pv3,pv3067], .c 3, .c 23, .c 11, .c 3,
  .c 1867, .c 5, .c 3, .p pv3 [pv2,pv173,pv359], .c 31, .c 3, .c 5, .c 19, .c 3, .c 11, .c 317,
  .c 3, .c 13, .c 197, .c 3, .c 7, .c 5, .c 3, .c 593, .p pv41 [pv2,pv3,pv5,pv7,pv13], .c 3, .c 5,
  .c 7, .c 3, .c 311, .c 13, .c 3, .p pv3 [pv2,pv248431], .c 1231, .c 3, .c 109, .c 5, .c 3,
  .c 41, .p pv13 [pv2,pv3,pv5,pv37,pv3581], .c 3, .c 5, .p pv5 [pv2,pv3,pv11,pv30113], .c 3,
  .p pv3 [pv2,pv5,pv43,pv2311], .c 17, .c 3, .c 11, .c 7, .c 3, .c 19, .c 5, .c 3,
  .p pv2 [pv2,pv11,pv180679], .c 181, .c 3, .c 5, .c 37, .c 3, .p pv7 [pv2,pv5,pv7,pv41,pv277],
  .c 83, .c 3, .c 7, .p pv7 [pv2,pv3,pv13,pv16987], .c 3, .c 43, .c 5, .c 3,
  .p pv3 [pv2,pv496871], .c 7, .c 3, .c 5, .c 367, .c 3, .p pv3 [pv2,pv5,pv233,pv853], .c 139,
  .c 3, .p pv2 [pv2,pv457,pv4349], .c 1291, .c 3, .c 11, .c 5, .c 3, .c 7, .c 29,
]
private theorem h0485c31 : checkBlock 3974747 128 b0485c31 = true := by
  decide +kernel

def rows0485 : List Row :=
  b0485c00 ++ b0485c01 ++ b0485c02 ++ b0485c03 ++ b0485c04 ++ b0485c05 ++ b0485c06 ++ b0485c07 ++
  b0485c08 ++ b0485c09 ++ b0485c10 ++ b0485c11 ++ b0485c12 ++ b0485c13 ++ b0485c14 ++ b0485c15 ++
  b0485c16 ++ b0485c17 ++ b0485c18 ++ b0485c19 ++ b0485c20 ++ b0485c21 ++ b0485c22 ++ b0485c23 ++
  b0485c24 ++ b0485c25 ++ b0485c26 ++ b0485c27 ++ b0485c28 ++ b0485c29 ++ b0485c30 ++ b0485c31

theorem checked0485 : checkBlock 3966811 4096 rows0485 = true :=
  checkBlock_append h0485c00 (
    checkBlock_append h0485c01 (
    checkBlock_append h0485c02 (
    checkBlock_append h0485c03 (
    checkBlock_append h0485c04 (
    checkBlock_append h0485c05 (
    checkBlock_append h0485c06 (
    checkBlock_append h0485c07 (
    checkBlock_append h0485c08 (
    checkBlock_append h0485c09 (
    checkBlock_append h0485c10 (
    checkBlock_append h0485c11 (
    checkBlock_append h0485c12 (
    checkBlock_append h0485c13 (
    checkBlock_append h0485c14 (
    checkBlock_append h0485c15 (
    checkBlock_append h0485c16 (
    checkBlock_append h0485c17 (
    checkBlock_append h0485c18 (
    checkBlock_append h0485c19 (
    checkBlock_append h0485c20 (
    checkBlock_append h0485c21 (
    checkBlock_append h0485c22 (
    checkBlock_append h0485c23 (
    checkBlock_append h0485c24 (
    checkBlock_append h0485c25 (
    checkBlock_append h0485c26 (
    checkBlock_append h0485c27 (
    checkBlock_append h0485c28 (
    checkBlock_append h0485c29 (
    checkBlock_append h0485c30 (
    h0485c31)))))))))))))))))))))))))))))))

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
