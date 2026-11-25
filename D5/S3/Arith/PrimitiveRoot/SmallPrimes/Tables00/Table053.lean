/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table053
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table053.pv149953
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table007
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table011
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table029
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table030

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr149953 : PrimeCertificate 149953 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv11,pv71]) (by decide +kernel)
def pv149953 : PrimeValue := ⟨149953, pr149953⟩
private theorem pr149971 : PrimeCertificate 149971 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv4999]) (by decide +kernel)
def pv149971 : PrimeValue := ⟨149971, pr149971⟩
private theorem pr150001 : PrimeCertificate 150001 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv150001 : PrimeValue := ⟨150001, pr150001⟩
private theorem pr150011 : PrimeCertificate 150011 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv7,pv2143]) (by decide +kernel)
def pv150011 : PrimeValue := ⟨150011, pr150011⟩
private theorem pr150041 : PrimeCertificate 150041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv31]) (by decide +kernel)
def pv150041 : PrimeValue := ⟨150041, pr150041⟩
private theorem pr150053 : PrimeCertificate 150053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv23,pv233]) (by decide +kernel)
def pv150053 : PrimeValue := ⟨150053, pr150053⟩
private theorem pr150061 : PrimeCertificate 150061 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv41,pv61]) (by decide +kernel)
def pv150061 : PrimeValue := ⟨150061, pr150061⟩
private theorem pr150067 : PrimeCertificate 150067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv397]) (by decide +kernel)
def pv150067 : PrimeValue := ⟨150067, pr150067⟩
private theorem pr150089 : PrimeCertificate 150089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv73,pv257]) (by decide +kernel)
def pv150089 : PrimeValue := ⟨150089, pr150089⟩
private theorem pr150091 : PrimeCertificate 150091 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv5003]) (by decide +kernel)
def pv150091 : PrimeValue := ⟨150091, pr150091⟩
private theorem pr150097 : PrimeCertificate 150097 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv53,pv59]) (by decide +kernel)
def pv150097 : PrimeValue := ⟨150097, pr150097⟩
private theorem pr150107 : PrimeCertificate 150107 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv6823]) (by decide +kernel)
def pv150107 : PrimeValue := ⟨150107, pr150107⟩
private theorem pr150131 : PrimeCertificate 150131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv15013]) (by decide +kernel)
def pv150131 : PrimeValue := ⟨150131, pr150131⟩
private theorem pr150151 : PrimeCertificate 150151 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv5,pv7,pv11,pv13]) (by decide +kernel)
def pv150151 : PrimeValue := ⟨150151, pr150151⟩
private theorem pr150169 : PrimeCertificate 150169 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv6257]) (by decide +kernel)
def pv150169 : PrimeValue := ⟨150169, pr150169⟩
private theorem pr150197 : PrimeCertificate 150197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37549]) (by decide +kernel)
def pv150197 : PrimeValue := ⟨150197, pr150197⟩
private theorem pr150203 : PrimeCertificate 150203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv53,pv109]) (by decide +kernel)
def pv150203 : PrimeValue := ⟨150203, pr150203⟩
private theorem pr150209 : PrimeCertificate 150209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2347]) (by decide +kernel)
def pv150209 : PrimeValue := ⟨150209, pr150209⟩
private theorem pr150211 : PrimeCertificate 150211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1669]) (by decide +kernel)
def pv150211 : PrimeValue := ⟨150211, pr150211⟩
private theorem pr150217 : PrimeCertificate 150217 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv569]) (by decide +kernel)
def pv150217 : PrimeValue := ⟨150217, pr150217⟩
private theorem pr150221 : PrimeCertificate 150221 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv29,pv37]) (by decide +kernel)
def pv150221 : PrimeValue := ⟨150221, pr150221⟩
private theorem pr150223 : PrimeCertificate 150223 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv25037]) (by decide +kernel)
def pv150223 : PrimeValue := ⟨150223, pr150223⟩
private theorem pr150247 : PrimeCertificate 150247 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv491]) (by decide +kernel)
def pv150247 : PrimeValue := ⟨150247, pr150247⟩
private theorem pr150287 : PrimeCertificate 150287 :=
  certifyPrime (q := pv5) (ls := [pv2,pv163,pv461]) (by decide +kernel)
def pv150287 : PrimeValue := ⟨150287, pr150287⟩
private theorem pr150299 : PrimeCertificate 150299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv75149]) (by decide +kernel)
def pv150299 : PrimeValue := ⟨150299, pr150299⟩
private theorem pr150301 : PrimeCertificate 150301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv167]) (by decide +kernel)
def pv150301 : PrimeValue := ⟨150301, pr150301⟩
private theorem pr150323 : PrimeCertificate 150323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv75161]) (by decide +kernel)
def pv150323 : PrimeValue := ⟨150323, pr150323⟩
private theorem pr150329 : PrimeCertificate 150329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv23,pv43]) (by decide +kernel)
def pv150329 : PrimeValue := ⟨150329, pr150329⟩
private theorem pr150343 : PrimeCertificate 150343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv25057]) (by decide +kernel)
def pv150343 : PrimeValue := ⟨150343, pr150343⟩
private theorem pr150373 : PrimeCertificate 150373 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4177]) (by decide +kernel)
def pv150373 : PrimeValue := ⟨150373, pr150373⟩
private theorem pr150377 : PrimeCertificate 150377 :=
  certifyPrime (q := pv3) (ls := [pv2,pv18797]) (by decide +kernel)
def pv150377 : PrimeValue := ⟨150377, pr150377⟩
private theorem pr150379 : PrimeCertificate 150379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv71,pv353]) (by decide +kernel)
def pv150379 : PrimeValue := ⟨150379, pr150379⟩
private theorem pr150383 : PrimeCertificate 150383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv4423]) (by decide +kernel)
def pv150383 : PrimeValue := ⟨150383, pr150383⟩
private theorem pr150401 : PrimeCertificate 150401 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv47]) (by decide +kernel)
def pv150401 : PrimeValue := ⟨150401, pr150401⟩
private theorem pr150407 : PrimeCertificate 150407 :=
  certifyPrime (q := pv5) (ls := [pv2,pv157,pv479]) (by decide +kernel)
def pv150407 : PrimeValue := ⟨150407, pr150407⟩
private theorem pr150427 : PrimeCertificate 150427 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv61,pv137]) (by decide +kernel)
def pv150427 : PrimeValue := ⟨150427, pr150427⟩
private theorem pr150439 : PrimeCertificate 150439 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv25073]) (by decide +kernel)
def pv150439 : PrimeValue := ⟨150439, pr150439⟩
private theorem pr150473 : PrimeCertificate 150473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv2687]) (by decide +kernel)
def pv150473 : PrimeValue := ⟨150473, pr150473⟩
private theorem pr150497 : PrimeCertificate 150497 :=
  certifyPrime (q := pv3) (ls := [pv2,pv4703]) (by decide +kernel)
def pv150497 : PrimeValue := ⟨150497, pr150497⟩
private theorem pr150517 : PrimeCertificate 150517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv113]) (by decide +kernel)
def pv150517 : PrimeValue := ⟨150517, pr150517⟩
private theorem pr150523 : PrimeCertificate 150523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv25087]) (by decide +kernel)
def pv150523 : PrimeValue := ⟨150523, pr150523⟩
private theorem pr150551 : PrimeCertificate 150551 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv3011]) (by decide +kernel)
def pv150551 : PrimeValue := ⟨150551, pr150551⟩
private theorem pr150559 : PrimeCertificate 150559 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv1091]) (by decide +kernel)
def pv150559 : PrimeValue := ⟨150559, pr150559⟩
private theorem pr150571 : PrimeCertificate 150571 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv239]) (by decide +kernel)
def pv150571 : PrimeValue := ⟨150571, pr150571⟩
private theorem pr150583 : PrimeCertificate 150583 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv25097]) (by decide +kernel)
def pv150583 : PrimeValue := ⟨150583, pr150583⟩
private theorem pr150587 : PrimeCertificate 150587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv43,pv103]) (by decide +kernel)
def pv150587 : PrimeValue := ⟨150587, pr150587⟩
private theorem pr150607 : PrimeCertificate 150607 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv2789]) (by decide +kernel)
def pv150607 : PrimeValue := ⟨150607, pr150607⟩
private theorem pr150611 : PrimeCertificate 150611 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv15061]) (by decide +kernel)
def pv150611 : PrimeValue := ⟨150611, pr150611⟩
private theorem pr150617 : PrimeCertificate 150617 :=
  certifyPrime (q := pv3) (ls := [pv2,pv67,pv281]) (by decide +kernel)
def pv150617 : PrimeValue := ⟨150617, pr150617⟩
private theorem pr150649 : PrimeCertificate 150649 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv6277]) (by decide +kernel)
def pv150649 : PrimeValue := ⟨150649, pr150649⟩
private theorem pr150659 : PrimeCertificate 150659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv75329]) (by decide +kernel)
def pv150659 : PrimeValue := ⟨150659, pr150659⟩
private theorem pr150697 : PrimeCertificate 150697 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv23]) (by decide +kernel)
def pv150697 : PrimeValue := ⟨150697, pr150697⟩
private theorem pr150721 : PrimeCertificate 150721 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv157]) (by decide +kernel)
def pv150721 : PrimeValue := ⟨150721, pr150721⟩
private theorem pr150743 : PrimeCertificate 150743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv29,pv113]) (by decide +kernel)
def pv150743 : PrimeValue := ⟨150743, pr150743⟩
private theorem pr150769 : PrimeCertificate 150769 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv349]) (by decide +kernel)
def pv150769 : PrimeValue := ⟨150769, pr150769⟩
private theorem pr150779 : PrimeCertificate 150779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv75389]) (by decide +kernel)
def pv150779 : PrimeValue := ⟨150779, pr150779⟩
private theorem pr150791 : PrimeCertificate 150791 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv17,pv887]) (by decide +kernel)
def pv150791 : PrimeValue := ⟨150791, pr150791⟩
private theorem pr150797 : PrimeCertificate 150797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37699]) (by decide +kernel)
def pv150797 : PrimeValue := ⟨150797, pr150797⟩
private theorem pr150827 : PrimeCertificate 150827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv5801]) (by decide +kernel)
def pv150827 : PrimeValue := ⟨150827, pr150827⟩
private theorem pr150833 : PrimeCertificate 150833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv857]) (by decide +kernel)
def pv150833 : PrimeValue := ⟨150833, pr150833⟩
private theorem pr150847 : PrimeCertificate 150847 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31,pv811]) (by decide +kernel)
def pv150847 : PrimeValue := ⟨150847, pr150847⟩
private theorem pr150881 : PrimeCertificate 150881 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv23,pv41]) (by decide +kernel)
def pv150881 : PrimeValue := ⟨150881, pr150881⟩
private theorem pr150883 : PrimeCertificate 150883 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv25147]) (by decide +kernel)
def pv150883 : PrimeValue := ⟨150883, pr150883⟩
private theorem pr150889 : PrimeCertificate 150889 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv6287]) (by decide +kernel)
def pv150889 : PrimeValue := ⟨150889, pr150889⟩
private theorem pr150901 : PrimeCertificate 150901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv503]) (by decide +kernel)
def pv150901 : PrimeValue := ⟨150901, pr150901⟩
private theorem pr150907 : PrimeCertificate 150907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv3593]) (by decide +kernel)
def pv150907 : PrimeValue := ⟨150907, pr150907⟩
private theorem pr150919 : PrimeCertificate 150919 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv25153]) (by decide +kernel)
def pv150919 : PrimeValue := ⟨150919, pr150919⟩
private theorem pr150961 : PrimeCertificate 150961 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv17,pv37]) (by decide +kernel)
def pv150961 : PrimeValue := ⟨150961, pr150961⟩
private theorem pr150967 : PrimeCertificate 150967 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv8387]) (by decide +kernel)
def pv150967 : PrimeValue := ⟨150967, pr150967⟩
private theorem pr150979 : PrimeCertificate 150979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv25163]) (by decide +kernel)
def pv150979 : PrimeValue := ⟨150979, pr150979⟩
private theorem pr150989 : PrimeCertificate 150989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37747]) (by decide +kernel)
def pv150989 : PrimeValue := ⟨150989, pr150989⟩
private theorem pr150991 : PrimeCertificate 150991 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv719]) (by decide +kernel)
def pv150991 : PrimeValue := ⟨150991, pr150991⟩
private theorem pr151007 : PrimeCertificate 151007 :=
  certifyPrime (q := pv5) (ls := [pv2,pv75503]) (by decide +kernel)
def pv151007 : PrimeValue := ⟨151007, pr151007⟩
private theorem pr151013 : PrimeCertificate 151013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv1987]) (by decide +kernel)
def pv151013 : PrimeValue := ⟨151013, pr151013⟩
private theorem pr151049 : PrimeCertificate 151049 :=
  certifyPrime (q := pv3) (ls := [pv2,pv79,pv239]) (by decide +kernel)
def pv151049 : PrimeValue := ⟨151049, pr151049⟩
private theorem pr151051 : PrimeCertificate 151051 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv19,pv53]) (by decide +kernel)
def pv151051 : PrimeValue := ⟨151051, pr151051⟩
private theorem pr151057 : PrimeCertificate 151057 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv1049]) (by decide +kernel)
def pv151057 : PrimeValue := ⟨151057, pr151057⟩
private theorem pr151121 : PrimeCertificate 151121 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1889]) (by decide +kernel)
def pv151121 : PrimeValue := ⟨151121, pr151121⟩
private theorem pr151141 : PrimeCertificate 151141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv229]) (by decide +kernel)
def pv151141 : PrimeValue := ⟨151141, pr151141⟩
private theorem pr151153 : PrimeCertificate 151153 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv47,pv67]) (by decide +kernel)
def pv151153 : PrimeValue := ⟨151153, pr151153⟩
private theorem pr151157 : PrimeCertificate 151157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv31,pv53]) (by decide +kernel)
def pv151157 : PrimeValue := ⟨151157, pr151157⟩
private theorem pr151169 : PrimeCertificate 151169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1181]) (by decide +kernel)
def pv151169 : PrimeValue := ⟨151169, pr151169⟩
private theorem pr151171 : PrimeCertificate 151171 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv5039]) (by decide +kernel)
def pv151171 : PrimeValue := ⟨151171, pr151171⟩
private theorem pr151189 : PrimeCertificate 151189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv293]) (by decide +kernel)
def pv151189 : PrimeValue := ⟨151189, pr151189⟩
private theorem pr151201 : PrimeCertificate 151201 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv151201 : PrimeValue := ⟨151201, pr151201⟩
private theorem pr151213 : PrimeCertificate 151213 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv12601]) (by decide +kernel)
def pv151213 : PrimeValue := ⟨151213, pr151213⟩
private theorem pr151237 : PrimeCertificate 151237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv4201]) (by decide +kernel)
def pv151237 : PrimeValue := ⟨151237, pr151237⟩
private theorem pr151241 : PrimeCertificate 151241 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv19,pv199]) (by decide +kernel)
def pv151241 : PrimeValue := ⟨151241, pr151241⟩
private theorem pr151243 : PrimeCertificate 151243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv277]) (by decide +kernel)
def pv151243 : PrimeValue := ⟨151243, pr151243⟩
private theorem pr151247 : PrimeCertificate 151247 :=
  certifyPrime (q := pv5) (ls := [pv2,pv47,pv1609]) (by decide +kernel)
def pv151247 : PrimeValue := ⟨151247, pr151247⟩
private theorem pr151253 : PrimeCertificate 151253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37813]) (by decide +kernel)
def pv151253 : PrimeValue := ⟨151253, pr151253⟩
private theorem pr151273 : PrimeCertificate 151273 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv191]) (by decide +kernel)
def pv151273 : PrimeValue := ⟨151273, pr151273⟩
private theorem pr151279 : PrimeCertificate 151279 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv1327]) (by decide +kernel)
def pv151279 : PrimeValue := ⟨151279, pr151279⟩
private theorem pr151289 : PrimeCertificate 151289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv18911]) (by decide +kernel)
def pv151289 : PrimeValue := ⟨151289, pr151289⟩
private theorem pr151303 : PrimeCertificate 151303 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv151,pv167]) (by decide +kernel)
def pv151303 : PrimeValue := ⟨151303, pr151303⟩
private theorem pr151337 : PrimeCertificate 151337 :=
  certifyPrime (q := pv3) (ls := [pv2,pv18917]) (by decide +kernel)
def pv151337 : PrimeValue := ⟨151337, pr151337⟩
private theorem pr151339 : PrimeCertificate 151339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv2293]) (by decide +kernel)
def pv151339 : PrimeValue := ⟨151339, pr151339⟩
private theorem pr151343 : PrimeCertificate 151343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv31,pv2441]) (by decide +kernel)
def pv151343 : PrimeValue := ⟨151343, pr151343⟩
private theorem pr151357 : PrimeCertificate 151357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv12613]) (by decide +kernel)
def pv151357 : PrimeValue := ⟨151357, pr151357⟩
private theorem pr151379 : PrimeCertificate 151379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv75689]) (by decide +kernel)
def pv151379 : PrimeValue := ⟨151379, pr151379⟩
private theorem pr151381 : PrimeCertificate 151381 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv29]) (by decide +kernel)
def pv151381 : PrimeValue := ⟨151381, pr151381⟩
private theorem pr151423 : PrimeCertificate 151423 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv25237]) (by decide +kernel)
def pv151423 : PrimeValue := ⟨151423, pr151423⟩
private theorem pr151429 : PrimeCertificate 151429 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv12619]) (by decide +kernel)
def pv151429 : PrimeValue := ⟨151429, pr151429⟩
private theorem pr151433 : PrimeCertificate 151433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv823]) (by decide +kernel)
def pv151433 : PrimeValue := ⟨151433, pr151433⟩
private theorem pr151451 : PrimeCertificate 151451 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv233]) (by decide +kernel)
def pv151451 : PrimeValue := ⟨151451, pr151451⟩
private theorem pr151471 : PrimeCertificate 151471 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv17]) (by decide +kernel)
def pv151471 : PrimeValue := ⟨151471, pr151471⟩
private theorem pr151477 : PrimeCertificate 151477 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv13,pv971]) (by decide +kernel)
def pv151477 : PrimeValue := ⟨151477, pr151477⟩
private theorem pr151483 : PrimeCertificate 151483 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv25247]) (by decide +kernel)
def pv151483 : PrimeValue := ⟨151483, pr151483⟩
private theorem pr151499 : PrimeCertificate 151499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv211,pv359]) (by decide +kernel)
def pv151499 : PrimeValue := ⟨151499, pr151499⟩
private theorem pr151507 : PrimeCertificate 151507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv443]) (by decide +kernel)
def pv151507 : PrimeValue := ⟨151507, pr151507⟩
private theorem pr151517 : PrimeCertificate 151517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37879]) (by decide +kernel)
def pv151517 : PrimeValue := ⟨151517, pr151517⟩
private theorem pr151523 : PrimeCertificate 151523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv79,pv137]) (by decide +kernel)
def pv151523 : PrimeValue := ⟨151523, pr151523⟩
private theorem pr151531 : PrimeCertificate 151531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv5051]) (by decide +kernel)
def pv151531 : PrimeValue := ⟨151531, pr151531⟩
private theorem pr151553 : PrimeCertificate 151553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37]) (by decide +kernel)
def pv151553 : PrimeValue := ⟨151553, pr151553⟩
private theorem pr151579 : PrimeCertificate 151579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv401]) (by decide +kernel)
def pv151579 : PrimeValue := ⟨151579, pr151579⟩
private theorem pr151597 : PrimeCertificate 151597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv4211]) (by decide +kernel)
def pv151597 : PrimeValue := ⟨151597, pr151597⟩
private theorem pr151603 : PrimeCertificate 151603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv2297]) (by decide +kernel)
def pv151603 : PrimeValue := ⟨151603, pr151603⟩
private theorem pr151607 : PrimeCertificate 151607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv13,pv17]) (by decide +kernel)
def pv151607 : PrimeValue := ⟨151607, pr151607⟩
private theorem pr151631 : PrimeCertificate 151631 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv59,pv257]) (by decide +kernel)
def pv151631 : PrimeValue := ⟨151631, pr151631⟩
private theorem pr151637 : PrimeCertificate 151637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv167,pv227]) (by decide +kernel)
def pv151637 : PrimeValue := ⟨151637, pr151637⟩
private theorem pr151643 : PrimeCertificate 151643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv75821]) (by decide +kernel)
def pv151643 : PrimeValue := ⟨151643, pr151643⟩
private theorem pr151651 : PrimeCertificate 151651 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv337]) (by decide +kernel)
def pv151651 : PrimeValue := ⟨151651, pr151651⟩
private theorem pr151667 : PrimeCertificate 151667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv75833]) (by decide +kernel)
def pv151667 : PrimeValue := ⟨151667, pr151667⟩
private theorem pr151673 : PrimeCertificate 151673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv18959]) (by decide +kernel)
def pv151673 : PrimeValue := ⟨151673, pr151673⟩
private theorem pr151687 : PrimeCertificate 151687 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv53]) (by decide +kernel)
def pv151687 : PrimeValue := ⟨151687, pr151687⟩
private theorem pr151703 : PrimeCertificate 151703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv101,pv751]) (by decide +kernel)
def pv151703 : PrimeValue := ⟨151703, pr151703⟩
private theorem pr151717 : PrimeCertificate 151717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv269]) (by decide +kernel)
def pv151717 : PrimeValue := ⟨151717, pr151717⟩
private theorem pr151729 : PrimeCertificate 151729 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv29,pv109]) (by decide +kernel)
def pv151729 : PrimeValue := ⟨151729, pr151729⟩
private theorem pr151769 : PrimeCertificate 151769 :=
  certifyPrime (q := pv3) (ls := [pv2,pv61,pv311]) (by decide +kernel)
def pv151769 : PrimeValue := ⟨151769, pr151769⟩
private theorem pr151771 : PrimeCertificate 151771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv5059]) (by decide +kernel)
def pv151771 : PrimeValue := ⟨151771, pr151771⟩
private theorem pr151783 : PrimeCertificate 151783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv41,pv617]) (by decide +kernel)
def pv151783 : PrimeValue := ⟨151783, pr151783⟩
private theorem pr151799 : PrimeCertificate 151799 :=
  certifyPrime (q := pv7) (ls := [pv2,pv71,pv1069]) (by decide +kernel)
def pv151799 : PrimeValue := ⟨151799, pr151799⟩
private theorem pr151813 : PrimeCertificate 151813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv4217]) (by decide +kernel)
def pv151813 : PrimeValue := ⟨151813, pr151813⟩
private theorem pr151841 : PrimeCertificate 151841 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv73]) (by decide +kernel)
def pv151841 : PrimeValue := ⟨151841, pr151841⟩
private theorem pr151849 : PrimeCertificate 151849 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv19,pv37]) (by decide +kernel)
def pv151849 : PrimeValue := ⟨151849, pr151849⟩
private theorem pr151871 : PrimeCertificate 151871 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv15187]) (by decide +kernel)
def pv151871 : PrimeValue := ⟨151871, pr151871⟩
private theorem pr151883 : PrimeCertificate 151883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv75941]) (by decide +kernel)
def pv151883 : PrimeValue := ⟨151883, pr151883⟩
private theorem pr151897 : PrimeCertificate 151897 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv6329]) (by decide +kernel)
def pv151897 : PrimeValue := ⟨151897, pr151897⟩
private theorem pr151901 : PrimeCertificate 151901 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv7,pv31]) (by decide +kernel)
def pv151901 : PrimeValue := ⟨151901, pr151901⟩
private theorem pr151903 : PrimeCertificate 151903 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv29,pv97]) (by decide +kernel)
def pv151903 : PrimeValue := ⟨151903, pr151903⟩
private theorem pr151937 : PrimeCertificate 151937 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1187]) (by decide +kernel)
def pv151937 : PrimeValue := ⟨151937, pr151937⟩
private theorem pr151939 : PrimeCertificate 151939 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23,pv367]) (by decide +kernel)
def pv151939 : PrimeValue := ⟨151939, pr151939⟩
private theorem pr151967 : PrimeCertificate 151967 :=
  certifyPrime (q := pv5) (ls := [pv2,pv75983]) (by decide +kernel)
def pv151967 : PrimeValue := ⟨151967, pr151967⟩
private theorem pr151969 : PrimeCertificate 151969 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1583]) (by decide +kernel)
def pv151969 : PrimeValue := ⟨151969, pr151969⟩
private theorem pr152003 : PrimeCertificate 152003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv76001]) (by decide +kernel)
def pv152003 : PrimeValue := ⟨152003, pr152003⟩
private theorem pr152017 : PrimeCertificate 152017 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv3167]) (by decide +kernel)
def pv152017 : PrimeValue := ⟨152017, pr152017⟩
private theorem pr152029 : PrimeCertificate 152029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv103]) (by decide +kernel)
def pv152029 : PrimeValue := ⟨152029, pr152029⟩
private theorem pr152039 : PrimeCertificate 152039 :=
  certifyPrime (q := pv19) (ls := [pv2,pv19,pv4001]) (by decide +kernel)
def pv152039 : PrimeValue := ⟨152039, pr152039⟩
private theorem pr152041 : PrimeCertificate 152041 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv181]) (by decide +kernel)
def pv152041 : PrimeValue := ⟨152041, pr152041⟩
private theorem pr152063 : PrimeCertificate 152063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv76031]) (by decide +kernel)
def pv152063 : PrimeValue := ⟨152063, pr152063⟩
private theorem pr152077 : PrimeCertificate 152077 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv19,pv23,pv29]) (by decide +kernel)
def pv152077 : PrimeValue := ⟨152077, pr152077⟩
private theorem pr152081 : PrimeCertificate 152081 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1901]) (by decide +kernel)
def pv152081 : PrimeValue := ⟨152081, pr152081⟩
private theorem pr152083 : PrimeCertificate 152083 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv17,pv71]) (by decide +kernel)
def pv152083 : PrimeValue := ⟨152083, pr152083⟩
private theorem pr152093 : PrimeCertificate 152093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv809]) (by decide +kernel)
def pv152093 : PrimeValue := ⟨152093, pr152093⟩
private theorem pr152111 : PrimeCertificate 152111 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv41,pv53]) (by decide +kernel)
def pv152111 : PrimeValue := ⟨152111, pr152111⟩
private theorem pr152123 : PrimeCertificate 152123 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv3307]) (by decide +kernel)
def pv152123 : PrimeValue := ⟨152123, pr152123⟩
private theorem pr152147 : PrimeCertificate 152147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv127,pv599]) (by decide +kernel)
def pv152147 : PrimeValue := ⟨152147, pr152147⟩
private theorem pr152183 : PrimeCertificate 152183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv76091]) (by decide +kernel)
def pv152183 : PrimeValue := ⟨152183, pr152183⟩
private theorem pr152189 : PrimeCertificate 152189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv38047]) (by decide +kernel)
def pv152189 : PrimeValue := ⟨152189, pr152189⟩
private theorem pr152197 : PrimeCertificate 152197 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv1153]) (by decide +kernel)
def pv152197 : PrimeValue := ⟨152197, pr152197⟩
private theorem pr152213 : PrimeCertificate 152213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv38053]) (by decide +kernel)
def pv152213 : PrimeValue := ⟨152213, pr152213⟩
private theorem pr152219 : PrimeCertificate 152219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv17,pv37]) (by decide +kernel)
def pv152219 : PrimeValue := ⟨152219, pr152219⟩
private theorem pr152239 : PrimeCertificate 152239 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv25373]) (by decide +kernel)
def pv152239 : PrimeValue := ⟨152239, pr152239⟩
private theorem pr152249 : PrimeCertificate 152249 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19031]) (by decide +kernel)
def pv152249 : PrimeValue := ⟨152249, pr152249⟩
private theorem pr152287 : PrimeCertificate 152287 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv1493]) (by decide +kernel)
def pv152287 : PrimeValue := ⟨152287, pr152287⟩
private theorem pr152293 : PrimeCertificate 152293 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv37]) (by decide +kernel)
def pv152293 : PrimeValue := ⟨152293, pr152293⟩
private theorem pr152311 : PrimeCertificate 152311 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv5,pv5077]) (by decide +kernel)
def pv152311 : PrimeValue := ⟨152311, pr152311⟩
private theorem pr152377 : PrimeCertificate 152377 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv907]) (by decide +kernel)
def pv152377 : PrimeValue := ⟨152377, pr152377⟩
private theorem pr152381 : PrimeCertificate 152381 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv19,pv401]) (by decide +kernel)
def pv152381 : PrimeValue := ⟨152381, pr152381⟩
private theorem pr152389 : PrimeCertificate 152389 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv83]) (by decide +kernel)
def pv152389 : PrimeValue := ⟨152389, pr152389⟩
private theorem pr152393 : PrimeCertificate 152393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43,pv443]) (by decide +kernel)
def pv152393 : PrimeValue := ⟨152393, pr152393⟩
private theorem pr152407 : PrimeCertificate 152407 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv8467]) (by decide +kernel)
def pv152407 : PrimeValue := ⟨152407, pr152407⟩
private theorem pr152417 : PrimeCertificate 152417 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv433]) (by decide +kernel)
def pv152417 : PrimeValue := ⟨152417, pr152417⟩
private theorem pr152419 : PrimeCertificate 152419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv19,pv191]) (by decide +kernel)
def pv152419 : PrimeValue := ⟨152419, pr152419⟩
private theorem pr152423 : PrimeCertificate 152423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv4483]) (by decide +kernel)
def pv152423 : PrimeValue := ⟨152423, pr152423⟩
private theorem pr152429 : PrimeCertificate 152429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv719]) (by decide +kernel)
def pv152429 : PrimeValue := ⟨152429, pr152429⟩
private theorem pr152441 : PrimeCertificate 152441 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv37,pv103]) (by decide +kernel)
def pv152441 : PrimeValue := ⟨152441, pr152441⟩
private theorem pr152443 : PrimeCertificate 152443 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv941]) (by decide +kernel)
def pv152443 : PrimeValue := ⟨152443, pr152443⟩
private theorem pr152459 : PrimeCertificate 152459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv2459]) (by decide +kernel)
def pv152459 : PrimeValue := ⟨152459, pr152459⟩
private theorem pr152461 : PrimeCertificate 152461 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv7,pv11]) (by decide +kernel)
def pv152461 : PrimeValue := ⟨152461, pr152461⟩
private theorem pr152501 : PrimeCertificate 152501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv61]) (by decide +kernel)
def pv152501 : PrimeValue := ⟨152501, pr152501⟩
private theorem pr152519 : PrimeCertificate 152519 :=
  certifyPrime (q := pv11) (ls := [pv2,pv76259]) (by decide +kernel)
def pv152519 : PrimeValue := ⟨152519, pr152519⟩
private theorem pr152531 : PrimeCertificate 152531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv2179]) (by decide +kernel)
def pv152531 : PrimeValue := ⟨152531, pr152531⟩
private theorem pr152533 : PrimeCertificate 152533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv223]) (by decide +kernel)
def pv152533 : PrimeValue := ⟨152533, pr152533⟩
private theorem pr152539 : PrimeCertificate 152539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv25423]) (by decide +kernel)
def pv152539 : PrimeValue := ⟨152539, pr152539⟩
private theorem pr152563 : PrimeCertificate 152563 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv47,pv541]) (by decide +kernel)
def pv152563 : PrimeValue := ⟨152563, pr152563⟩
private theorem pr152567 : PrimeCertificate 152567 :=
  certifyPrime (q := pv5) (ls := [pv2,pv76283]) (by decide +kernel)
def pv152567 : PrimeValue := ⟨152567, pr152567⟩
private theorem pr152597 : PrimeCertificate 152597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv38149]) (by decide +kernel)
def pv152597 : PrimeValue := ⟨152597, pr152597⟩
private theorem pr152617 : PrimeCertificate 152617 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv6359]) (by decide +kernel)
def pv152617 : PrimeValue := ⟨152617, pr152617⟩
private theorem pr152623 : PrimeCertificate 152623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv61,pv139]) (by decide +kernel)
def pv152623 : PrimeValue := ⟨152623, pr152623⟩
private theorem pr152629 : PrimeCertificate 152629 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv7,pv23,pv79]) (by decide +kernel)
def pv152629 : PrimeValue := ⟨152629, pr152629⟩
private theorem pr152639 : PrimeCertificate 152639 :=
  certifyPrime (q := pv7) (ls := [pv2,pv167,pv457]) (by decide +kernel)
def pv152639 : PrimeValue := ⟨152639, pr152639⟩
private theorem pr152641 : PrimeCertificate 152641 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv53]) (by decide +kernel)
def pv152641 : PrimeValue := ⟨152641, pr152641⟩
private theorem pr152657 : PrimeCertificate 152657 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv29,pv47]) (by decide +kernel)
def pv152657 : PrimeValue := ⟨152657, pr152657⟩
private theorem pr152681 : PrimeCertificate 152681 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv347]) (by decide +kernel)
def pv152681 : PrimeValue := ⟨152681, pr152681⟩
private theorem pr152723 : PrimeCertificate 152723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv4019]) (by decide +kernel)
def pv152723 : PrimeValue := ⟨152723, pr152723⟩
private theorem pr152729 : PrimeCertificate 152729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv1123]) (by decide +kernel)
def pv152729 : PrimeValue := ⟨152729, pr152729⟩
private theorem pr152767 : PrimeCertificate 152767 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv41]) (by decide +kernel)
def pv152767 : PrimeValue := ⟨152767, pr152767⟩
private theorem pr152777 : PrimeCertificate 152777 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv113]) (by decide +kernel)
def pv152777 : PrimeValue := ⟨152777, pr152777⟩
private theorem pr152791 : PrimeCertificate 152791 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv463]) (by decide +kernel)
def pv152791 : PrimeValue := ⟨152791, pr152791⟩
private theorem pr152819 : PrimeCertificate 152819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv109,pv701]) (by decide +kernel)
def pv152819 : PrimeValue := ⟨152819, pr152819⟩
private theorem pr152821 : PrimeCertificate 152821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv283]) (by decide +kernel)
def pv152821 : PrimeValue := ⟨152821, pr152821⟩
private theorem pr152833 : PrimeCertificate 152833 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv199]) (by decide +kernel)
def pv152833 : PrimeValue := ⟨152833, pr152833⟩
private theorem pr152839 : PrimeCertificate 152839 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv1213]) (by decide +kernel)
def pv152839 : PrimeValue := ⟨152839, pr152839⟩
private theorem pr152843 : PrimeCertificate 152843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv76421]) (by decide +kernel)
def pv152843 : PrimeValue := ⟨152843, pr152843⟩
private theorem pr152851 : PrimeCertificate 152851 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv1019]) (by decide +kernel)
def pv152851 : PrimeValue := ⟨152851, pr152851⟩
private theorem pr152857 : PrimeCertificate 152857 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv193]) (by decide +kernel)
def pv152857 : PrimeValue := ⟨152857, pr152857⟩
private theorem pr152879 : PrimeCertificate 152879 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv6949]) (by decide +kernel)
def pv152879 : PrimeValue := ⟨152879, pr152879⟩
private theorem pr152897 : PrimeCertificate 152897 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2389]) (by decide +kernel)
def pv152897 : PrimeValue := ⟨152897, pr152897⟩
private theorem pr152909 : PrimeCertificate 152909 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv43,pv127]) (by decide +kernel)
def pv152909 : PrimeValue := ⟨152909, pr152909⟩
private theorem pr152947 : PrimeCertificate 152947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv293]) (by decide +kernel)
def pv152947 : PrimeValue := ⟨152947, pr152947⟩
private theorem pr152953 : PrimeCertificate 152953 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv6373]) (by decide +kernel)
def pv152953 : PrimeValue := ⟨152953, pr152953⟩
private theorem pr152959 : PrimeCertificate 152959 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13,pv37,pv53]) (by decide +kernel)
def pv152959 : PrimeValue := ⟨152959, pr152959⟩
private theorem pr152981 : PrimeCertificate 152981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7649]) (by decide +kernel)
def pv152981 : PrimeValue := ⟨152981, pr152981⟩
private theorem pr152989 : PrimeCertificate 152989 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv19,pv61]) (by decide +kernel)
def pv152989 : PrimeValue := ⟨152989, pr152989⟩
private theorem pr152993 : PrimeCertificate 152993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv683]) (by decide +kernel)
def pv152993 : PrimeValue := ⟨152993, pr152993⟩
private theorem pr153001 : PrimeCertificate 153001 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv153001 : PrimeValue := ⟨153001, pr153001⟩
private theorem pr153059 : PrimeCertificate 153059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv103,pv743]) (by decide +kernel)
def pv153059 : PrimeValue := ⟨153059, pr153059⟩
private theorem pr153071 : PrimeCertificate 153071 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv15307]) (by decide +kernel)
def pv153071 : PrimeValue := ⟨153071, pr153071⟩
private theorem pr153073 : PrimeCertificate 153073 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1063]) (by decide +kernel)
def pv153073 : PrimeValue := ⟨153073, pr153073⟩
private theorem pr153077 : PrimeCertificate 153077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv71]) (by decide +kernel)
def pv153077 : PrimeValue := ⟨153077, pr153077⟩
private theorem pr153089 : PrimeCertificate 153089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv23]) (by decide +kernel)
def pv153089 : PrimeValue := ⟨153089, pr153089⟩
private theorem pr153107 : PrimeCertificate 153107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv2069]) (by decide +kernel)
def pv153107 : PrimeValue := ⟨153107, pr153107⟩
private theorem pr153113 : PrimeCertificate 153113 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19139]) (by decide +kernel)
def pv153113 : PrimeValue := ⟨153113, pr153113⟩
private theorem pr153133 : PrimeCertificate 153133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1823]) (by decide +kernel)
def pv153133 : PrimeValue := ⟨153133, pr153133⟩
private theorem pr153137 : PrimeCertificate 153137 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv563]) (by decide +kernel)
def pv153137 : PrimeValue := ⟨153137, pr153137⟩
private theorem pr153151 : PrimeCertificate 153151 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv1021]) (by decide +kernel)
def pv153151 : PrimeValue := ⟨153151, pr153151⟩
private theorem pr153191 : PrimeCertificate 153191 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv15319]) (by decide +kernel)
def pv153191 : PrimeValue := ⟨153191, pr153191⟩
private theorem pr153247 : PrimeCertificate 153247 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv25541]) (by decide +kernel)
def pv153247 : PrimeValue := ⟨153247, pr153247⟩
private theorem pr153269 : PrimeCertificate 153269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv38317]) (by decide +kernel)
def pv153269 : PrimeValue := ⟨153269, pr153269⟩
private theorem pr153271 : PrimeCertificate 153271 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv13,pv131]) (by decide +kernel)
def pv153271 : PrimeValue := ⟨153271, pr153271⟩
private theorem pr153277 : PrimeCertificate 153277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53,pv241]) (by decide +kernel)
def pv153277 : PrimeValue := ⟨153277, pr153277⟩
private theorem pr153281 : PrimeCertificate 153281 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv479]) (by decide +kernel)
def pv153281 : PrimeValue := ⟨153281, pr153281⟩
private theorem pr153287 : PrimeCertificate 153287 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv10949]) (by decide +kernel)
def pv153287 : PrimeValue := ⟨153287, pr153287⟩
private theorem pr153313 : PrimeCertificate 153313 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1597]) (by decide +kernel)
def pv153313 : PrimeValue := ⟨153313, pr153313⟩
private theorem pr153343 : PrimeCertificate 153343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv1217]) (by decide +kernel)
def pv153343 : PrimeValue := ⟨153343, pr153343⟩
private theorem pr153353 : PrimeCertificate 153353 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv661]) (by decide +kernel)
def pv153353 : PrimeValue := ⟨153353, pr153353⟩
private theorem pr153359 : PrimeCertificate 153359 :=
  certifyPrime (q := pv13) (ls := [pv2,pv76679]) (by decide +kernel)
def pv153359 : PrimeValue := ⟨153359, pr153359⟩
private theorem pr153371 : PrimeCertificate 153371 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv313]) (by decide +kernel)
def pv153371 : PrimeValue := ⟨153371, pr153371⟩
private theorem pr153407 : PrimeCertificate 153407 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv19,pv367]) (by decide +kernel)
def pv153407 : PrimeValue := ⟨153407, pr153407⟩
private theorem pr153409 : PrimeCertificate 153409 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv17,pv47]) (by decide +kernel)
def pv153409 : PrimeValue := ⟨153409, pr153409⟩
private theorem pr153427 : PrimeCertificate 153427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv281]) (by decide +kernel)
def pv153427 : PrimeValue := ⟨153427, pr153427⟩
private theorem pr153437 : PrimeCertificate 153437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89,pv431]) (by decide +kernel)
def pv153437 : PrimeValue := ⟨153437, pr153437⟩
private theorem pr153443 : PrimeCertificate 153443 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv4513]) (by decide +kernel)
def pv153443 : PrimeValue := ⟨153443, pr153443⟩
private theorem pr153449 : PrimeCertificate 153449 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19181]) (by decide +kernel)
def pv153449 : PrimeValue := ⟨153449, pr153449⟩
private theorem pr153457 : PrimeCertificate 153457 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv139]) (by decide +kernel)
def pv153457 : PrimeValue := ⟨153457, pr153457⟩
private theorem pr153469 : PrimeCertificate 153469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv29]) (by decide +kernel)
def pv153469 : PrimeValue := ⟨153469, pr153469⟩
private theorem pr153499 : PrimeCertificate 153499 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv25583]) (by decide +kernel)
def pv153499 : PrimeValue := ⟨153499, pr153499⟩
private theorem pr153509 : PrimeCertificate 153509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv38377]) (by decide +kernel)
def pv153509 : PrimeValue := ⟨153509, pr153509⟩
private theorem pr153511 : PrimeCertificate 153511 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv17,pv43]) (by decide +kernel)
def pv153511 : PrimeValue := ⟨153511, pr153511⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
