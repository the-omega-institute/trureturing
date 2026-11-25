/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table049
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table049.pv135977
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table006
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table010
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table027

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr135977 : PrimeCertificate 135977 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv739]) (by decide +kernel)
def pv135977 : PrimeValue := ⟨135977, pr135977⟩
private theorem pr136027 : PrimeCertificate 136027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv229]) (by decide +kernel)
def pv136027 : PrimeValue := ⟨136027, pr136027⟩
private theorem pr136033 : PrimeCertificate 136033 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv109]) (by decide +kernel)
def pv136033 : PrimeValue := ⟨136033, pr136033⟩
private theorem pr136057 : PrimeCertificate 136057 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv5669]) (by decide +kernel)
def pv136057 : PrimeValue := ⟨136057, pr136057⟩
private theorem pr136067 : PrimeCertificate 136067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv9719]) (by decide +kernel)
def pv136067 : PrimeValue := ⟨136067, pr136067⟩
private theorem pr136069 : PrimeCertificate 136069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv23,pv29]) (by decide +kernel)
def pv136069 : PrimeValue := ⟨136069, pr136069⟩
private theorem pr136093 : PrimeCertificate 136093 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv1031]) (by decide +kernel)
def pv136093 : PrimeValue := ⟨136093, pr136093⟩
private theorem pr136111 : PrimeCertificate 136111 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv349]) (by decide +kernel)
def pv136111 : PrimeValue := ⟨136111, pr136111⟩
private theorem pr136133 : PrimeCertificate 136133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv34033]) (by decide +kernel)
def pv136133 : PrimeValue := ⟨136133, pr136133⟩
private theorem pr136139 : PrimeCertificate 136139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv1583]) (by decide +kernel)
def pv136139 : PrimeValue := ⟨136139, pr136139⟩
private theorem pr136189 : PrimeCertificate 136189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv97]) (by decide +kernel)
def pv136189 : PrimeValue := ⟨136189, pr136189⟩
private theorem pr136193 : PrimeCertificate 136193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv19]) (by decide +kernel)
def pv136193 : PrimeValue := ⟨136193, pr136193⟩
private theorem pr136207 : PrimeCertificate 136207 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv23,pv47]) (by decide +kernel)
def pv136207 : PrimeValue := ⟨136207, pr136207⟩
private theorem pr136217 : PrimeCertificate 136217 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17027]) (by decide +kernel)
def pv136217 : PrimeValue := ⟨136217, pr136217⟩
private theorem pr136223 : PrimeCertificate 136223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv68111]) (by decide +kernel)
def pv136223 : PrimeValue := ⟨136223, pr136223⟩
private theorem pr136237 : PrimeCertificate 136237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11353]) (by decide +kernel)
def pv136237 : PrimeValue := ⟨136237, pr136237⟩
private theorem pr136247 : PrimeCertificate 136247 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv563]) (by decide +kernel)
def pv136247 : PrimeValue := ⟨136247, pr136247⟩
private theorem pr136261 : PrimeCertificate 136261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv757]) (by decide +kernel)
def pv136261 : PrimeValue := ⟨136261, pr136261⟩
private theorem pr136273 : PrimeCertificate 136273 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv167]) (by decide +kernel)
def pv136273 : PrimeValue := ⟨136273, pr136273⟩
private theorem pr136277 : PrimeCertificate 136277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv31,pv157]) (by decide +kernel)
def pv136277 : PrimeValue := ⟨136277, pr136277⟩
private theorem pr136303 : PrimeCertificate 136303 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv22717]) (by decide +kernel)
def pv136303 : PrimeValue := ⟨136303, pr136303⟩
private theorem pr136319 : PrimeCertificate 136319 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv13,pv107]) (by decide +kernel)
def pv136319 : PrimeValue := ⟨136319, pr136319⟩
private theorem pr136327 : PrimeCertificate 136327 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv22721]) (by decide +kernel)
def pv136327 : PrimeValue := ⟨136327, pr136327⟩
private theorem pr136333 : PrimeCertificate 136333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv541]) (by decide +kernel)
def pv136333 : PrimeValue := ⟨136333, pr136333⟩
private theorem pr136337 : PrimeCertificate 136337 :=
  certifyPrime (q := pv3) (ls := [pv2,pv8521]) (by decide +kernel)
def pv136337 : PrimeValue := ⟨136337, pr136337⟩
private theorem pr136351 : PrimeCertificate 136351 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv101]) (by decide +kernel)
def pv136351 : PrimeValue := ⟨136351, pr136351⟩
private theorem pr136361 : PrimeCertificate 136361 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv7,pv487]) (by decide +kernel)
def pv136361 : PrimeValue := ⟨136361, pr136361⟩
private theorem pr136373 : PrimeCertificate 136373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv103,pv331]) (by decide +kernel)
def pv136373 : PrimeValue := ⟨136373, pr136373⟩
private theorem pr136379 : PrimeCertificate 136379 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv6199]) (by decide +kernel)
def pv136379 : PrimeValue := ⟨136379, pr136379⟩
private theorem pr136393 : PrimeCertificate 136393 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv5683]) (by decide +kernel)
def pv136393 : PrimeValue := ⟨136393, pr136393⟩
private theorem pr136397 : PrimeCertificate 136397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv43,pv61]) (by decide +kernel)
def pv136397 : PrimeValue := ⟨136397, pr136397⟩
private theorem pr136399 : PrimeCertificate 136399 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv127,pv179]) (by decide +kernel)
def pv136399 : PrimeValue := ⟨136399, pr136399⟩
private theorem pr136403 : PrimeCertificate 136403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv9743]) (by decide +kernel)
def pv136403 : PrimeValue := ⟨136403, pr136403⟩
private theorem pr136417 : PrimeCertificate 136417 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv29]) (by decide +kernel)
def pv136417 : PrimeValue := ⟨136417, pr136417⟩
private theorem pr136421 : PrimeCertificate 136421 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv19,pv359]) (by decide +kernel)
def pv136421 : PrimeValue := ⟨136421, pr136421⟩
private theorem pr136429 : PrimeCertificate 136429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11369]) (by decide +kernel)
def pv136429 : PrimeValue := ⟨136429, pr136429⟩
private theorem pr136447 : PrimeCertificate 136447 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv22741]) (by decide +kernel)
def pv136447 : PrimeValue := ⟨136447, pr136447⟩
private theorem pr136453 : PrimeCertificate 136453 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv83,pv137]) (by decide +kernel)
def pv136453 : PrimeValue := ⟨136453, pr136453⟩
private theorem pr136463 : PrimeCertificate 136463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv31,pv71]) (by decide +kernel)
def pv136463 : PrimeValue := ⟨136463, pr136463⟩
private theorem pr136471 : PrimeCertificate 136471 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv4549]) (by decide +kernel)
def pv136471 : PrimeValue := ⟨136471, pr136471⟩
private theorem pr136481 : PrimeCertificate 136481 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv853]) (by decide +kernel)
def pv136481 : PrimeValue := ⟨136481, pr136481⟩
private theorem pr136483 : PrimeCertificate 136483 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv43]) (by decide +kernel)
def pv136483 : PrimeValue := ⟨136483, pr136483⟩
private theorem pr136501 : PrimeCertificate 136501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv13]) (by decide +kernel)
def pv136501 : PrimeValue := ⟨136501, pr136501⟩
private theorem pr136511 : PrimeCertificate 136511 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv17,pv73]) (by decide +kernel)
def pv136511 : PrimeValue := ⟨136511, pr136511⟩
private theorem pr136519 : PrimeCertificate 136519 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv61,pv373]) (by decide +kernel)
def pv136519 : PrimeValue := ⟨136519, pr136519⟩
private theorem pr136523 : PrimeCertificate 136523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv68261]) (by decide +kernel)
def pv136523 : PrimeValue := ⟨136523, pr136523⟩
private theorem pr136531 : PrimeCertificate 136531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv37,pv41]) (by decide +kernel)
def pv136531 : PrimeValue := ⟨136531, pr136531⟩
private theorem pr136537 : PrimeCertificate 136537 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv5689]) (by decide +kernel)
def pv136537 : PrimeValue := ⟨136537, pr136537⟩
private theorem pr136541 : PrimeCertificate 136541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv6827]) (by decide +kernel)
def pv136541 : PrimeValue := ⟨136541, pr136541⟩
private theorem pr136559 : PrimeCertificate 136559 :=
  certifyPrime (q := pv11) (ls := [pv2,pv68279]) (by decide +kernel)
def pv136559 : PrimeValue := ⟨136559, pr136559⟩
private theorem pr136573 : PrimeCertificate 136573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv599]) (by decide +kernel)
def pv136573 : PrimeValue := ⟨136573, pr136573⟩
private theorem pr136601 : PrimeCertificate 136601 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv683]) (by decide +kernel)
def pv136601 : PrimeValue := ⟨136601, pr136601⟩
private theorem pr136603 : PrimeCertificate 136603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7589]) (by decide +kernel)
def pv136603 : PrimeValue := ⟨136603, pr136603⟩
private theorem pr136607 : PrimeCertificate 136607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv167,pv409]) (by decide +kernel)
def pv136607 : PrimeValue := ⟨136607, pr136607⟩
private theorem pr136649 : PrimeCertificate 136649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv29,pv31]) (by decide +kernel)
def pv136649 : PrimeValue := ⟨136649, pr136649⟩
private theorem pr136651 : PrimeCertificate 136651 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv911]) (by decide +kernel)
def pv136651 : PrimeValue := ⟨136651, pr136651⟩
private theorem pr136657 : PrimeCertificate 136657 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv73]) (by decide +kernel)
def pv136657 : PrimeValue := ⟨136657, pr136657⟩
private theorem pr136691 : PrimeCertificate 136691 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13669]) (by decide +kernel)
def pv136691 : PrimeValue := ⟨136691, pr136691⟩
private theorem pr136693 : PrimeCertificate 136693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3797]) (by decide +kernel)
def pv136693 : PrimeValue := ⟨136693, pr136693⟩
private theorem pr136709 : PrimeCertificate 136709 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv13,pv239]) (by decide +kernel)
def pv136709 : PrimeValue := ⟨136709, pr136709⟩
private theorem pr136727 : PrimeCertificate 136727 :=
  certifyPrime (q := pv5) (ls := [pv2,pv137,pv499]) (by decide +kernel)
def pv136727 : PrimeValue := ⟨136727, pr136727⟩
private theorem pr136733 : PrimeCertificate 136733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv34183]) (by decide +kernel)
def pv136733 : PrimeValue := ⟨136733, pr136733⟩
private theorem pr136739 : PrimeCertificate 136739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv9767]) (by decide +kernel)
def pv136739 : PrimeValue := ⟨136739, pr136739⟩
private theorem pr136751 : PrimeCertificate 136751 :=
  certifyPrime (q := pv31) (ls := [pv2,pv5,pv547]) (by decide +kernel)
def pv136751 : PrimeValue := ⟨136751, pr136751⟩
private theorem pr136753 : PrimeCertificate 136753 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv37]) (by decide +kernel)
def pv136753 : PrimeValue := ⟨136753, pr136753⟩
private theorem pr136769 : PrimeCertificate 136769 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2137]) (by decide +kernel)
def pv136769 : PrimeValue := ⟨136769, pr136769⟩
private theorem pr136811 : PrimeCertificate 136811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13681]) (by decide +kernel)
def pv136811 : PrimeValue := ⟨136811, pr136811⟩
private theorem pr136813 : PrimeCertificate 136813 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv877]) (by decide +kernel)
def pv136813 : PrimeValue := ⟨136813, pr136813⟩
private theorem pr136841 : PrimeCertificate 136841 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv311]) (by decide +kernel)
def pv136841 : PrimeValue := ⟨136841, pr136841⟩
private theorem pr136849 : PrimeCertificate 136849 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv2851]) (by decide +kernel)
def pv136849 : PrimeValue := ⟨136849, pr136849⟩
private theorem pr136859 : PrimeCertificate 136859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv1669]) (by decide +kernel)
def pv136859 : PrimeValue := ⟨136859, pr136859⟩
private theorem pr136861 : PrimeCertificate 136861 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv2281]) (by decide +kernel)
def pv136861 : PrimeValue := ⟨136861, pr136861⟩
private theorem pr136879 : PrimeCertificate 136879 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv3259]) (by decide +kernel)
def pv136879 : PrimeValue := ⟨136879, pr136879⟩
private theorem pr136883 : PrimeCertificate 136883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89,pv769]) (by decide +kernel)
def pv136883 : PrimeValue := ⟨136883, pr136883⟩
private theorem pr136889 : PrimeCertificate 136889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv71,pv241]) (by decide +kernel)
def pv136889 : PrimeValue := ⟨136889, pr136889⟩
private theorem pr136897 : PrimeCertificate 136897 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv31]) (by decide +kernel)
def pv136897 : PrimeValue := ⟨136897, pr136897⟩
private theorem pr136943 : PrimeCertificate 136943 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv23,pv229]) (by decide +kernel)
def pv136943 : PrimeValue := ⟨136943, pr136943⟩
private theorem pr136949 : PrimeCertificate 136949 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv67,pv73]) (by decide +kernel)
def pv136949 : PrimeValue := ⟨136949, pr136949⟩
private theorem pr136963 : PrimeCertificate 136963 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv1087]) (by decide +kernel)
def pv136963 : PrimeValue := ⟨136963, pr136963⟩
private theorem pr136973 : PrimeCertificate 136973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv283]) (by decide +kernel)
def pv136973 : PrimeValue := ⟨136973, pr136973⟩
private theorem pr136979 : PrimeCertificate 136979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv68489]) (by decide +kernel)
def pv136979 : PrimeValue := ⟨136979, pr136979⟩
private theorem pr136987 : PrimeCertificate 136987 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv79]) (by decide +kernel)
def pv136987 : PrimeValue := ⟨136987, pr136987⟩
private theorem pr136991 : PrimeCertificate 136991 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv7,pv19,pv103]) (by decide +kernel)
def pv136991 : PrimeValue := ⟨136991, pr136991⟩
private theorem pr136993 : PrimeCertificate 136993 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1427]) (by decide +kernel)
def pv136993 : PrimeValue := ⟨136993, pr136993⟩
private theorem pr136999 : PrimeCertificate 136999 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv43,pv59]) (by decide +kernel)
def pv136999 : PrimeValue := ⟨136999, pr136999⟩
private theorem pr137029 : PrimeCertificate 137029 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv19,pv601]) (by decide +kernel)
def pv137029 : PrimeValue := ⟨137029, pr137029⟩
private theorem pr137077 : PrimeCertificate 137077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11423]) (by decide +kernel)
def pv137077 : PrimeValue := ⟨137077, pr137077⟩
private theorem pr137087 : PrimeCertificate 137087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv68543]) (by decide +kernel)
def pv137087 : PrimeValue := ⟨137087, pr137087⟩
private theorem pr137089 : PrimeCertificate 137089 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv17]) (by decide +kernel)
def pv137089 : PrimeValue := ⟨137089, pr137089⟩
private theorem pr137119 : PrimeCertificate 137119 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv22853]) (by decide +kernel)
def pv137119 : PrimeValue := ⟨137119, pr137119⟩
private theorem pr137143 : PrimeCertificate 137143 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv19,pv401]) (by decide +kernel)
def pv137143 : PrimeValue := ⟨137143, pr137143⟩
private theorem pr137147 : PrimeCertificate 137147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv1459]) (by decide +kernel)
def pv137147 : PrimeValue := ⟨137147, pr137147⟩
private theorem pr137153 : PrimeCertificate 137153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2143]) (by decide +kernel)
def pv137153 : PrimeValue := ⟨137153, pr137153⟩
private theorem pr137177 : PrimeCertificate 137177 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv1319]) (by decide +kernel)
def pv137177 : PrimeValue := ⟨137177, pr137177⟩
private theorem pr137191 : PrimeCertificate 137191 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv17,pv269]) (by decide +kernel)
def pv137191 : PrimeValue := ⟨137191, pr137191⟩
private theorem pr137197 : PrimeCertificate 137197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv103]) (by decide +kernel)
def pv137197 : PrimeValue := ⟨137197, pr137197⟩
private theorem pr137201 : PrimeCertificate 137201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7]) (by decide +kernel)
def pv137201 : PrimeValue := ⟨137201, pr137201⟩
private theorem pr137209 : PrimeCertificate 137209 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5717]) (by decide +kernel)
def pv137209 : PrimeValue := ⟨137209, pr137209⟩
private theorem pr137219 : PrimeCertificate 137219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv23,pv157]) (by decide +kernel)
def pv137219 : PrimeValue := ⟨137219, pr137219⟩
private theorem pr137239 : PrimeCertificate 137239 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv89,pv257]) (by decide +kernel)
def pv137239 : PrimeValue := ⟨137239, pr137239⟩
private theorem pr137251 : PrimeCertificate 137251 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv61]) (by decide +kernel)
def pv137251 : PrimeValue := ⟨137251, pr137251⟩
private theorem pr137273 : PrimeCertificate 137273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17159]) (by decide +kernel)
def pv137273 : PrimeValue := ⟨137273, pr137273⟩
private theorem pr137279 : PrimeCertificate 137279 :=
  certifyPrime (q := pv7) (ls := [pv2,pv68639]) (by decide +kernel)
def pv137279 : PrimeValue := ⟨137279, pr137279⟩
private theorem pr137303 : PrimeCertificate 137303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv79]) (by decide +kernel)
def pv137303 : PrimeValue := ⟨137303, pr137303⟩
private theorem pr137321 : PrimeCertificate 137321 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv3433]) (by decide +kernel)
def pv137321 : PrimeValue := ⟨137321, pr137321⟩
private theorem pr137339 : PrimeCertificate 137339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv68669]) (by decide +kernel)
def pv137339 : PrimeValue := ⟨137339, pr137339⟩
private theorem pr137341 : PrimeCertificate 137341 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv5,pv7,pv109]) (by decide +kernel)
def pv137341 : PrimeValue := ⟨137341, pr137341⟩
private theorem pr137353 : PrimeCertificate 137353 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv59,pv97]) (by decide +kernel)
def pv137353 : PrimeValue := ⟨137353, pr137353⟩
private theorem pr137359 : PrimeCertificate 137359 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv13,pv587]) (by decide +kernel)
def pv137359 : PrimeValue := ⟨137359, pr137359⟩
private theorem pr137363 : PrimeCertificate 137363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv173,pv397]) (by decide +kernel)
def pv137363 : PrimeValue := ⟨137363, pr137363⟩
private theorem pr137369 : PrimeCertificate 137369 :=
  certifyPrime (q := pv19) (ls := [pv2,pv7,pv11,pv223]) (by decide +kernel)
def pv137369 : PrimeValue := ⟨137369, pr137369⟩
private theorem pr137383 : PrimeCertificate 137383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv3271]) (by decide +kernel)
def pv137383 : PrimeValue := ⟨137383, pr137383⟩
private theorem pr137387 : PrimeCertificate 137387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv941]) (by decide +kernel)
def pv137387 : PrimeValue := ⟨137387, pr137387⟩
private theorem pr137393 : PrimeCertificate 137393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv277]) (by decide +kernel)
def pv137393 : PrimeValue := ⟨137393, pr137393⟩
private theorem pr137399 : PrimeCertificate 137399 :=
  certifyPrime (q := pv11) (ls := [pv2,pv68699]) (by decide +kernel)
def pv137399 : PrimeValue := ⟨137399, pr137399⟩
private theorem pr137413 : PrimeCertificate 137413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv347]) (by decide +kernel)
def pv137413 : PrimeValue := ⟨137413, pr137413⟩
private theorem pr137437 : PrimeCertificate 137437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv881]) (by decide +kernel)
def pv137437 : PrimeValue := ⟨137437, pr137437⟩
private theorem pr137443 : PrimeCertificate 137443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv22907]) (by decide +kernel)
def pv137443 : PrimeValue := ⟨137443, pr137443⟩
private theorem pr137447 : PrimeCertificate 137447 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv3617]) (by decide +kernel)
def pv137447 : PrimeValue := ⟨137447, pr137447⟩
private theorem pr137453 : PrimeCertificate 137453 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv4909]) (by decide +kernel)
def pv137453 : PrimeValue := ⟨137453, pr137453⟩
private theorem pr137477 : PrimeCertificate 137477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv34369]) (by decide +kernel)
def pv137477 : PrimeValue := ⟨137477, pr137477⟩
private theorem pr137483 : PrimeCertificate 137483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv1297]) (by decide +kernel)
def pv137483 : PrimeValue := ⟨137483, pr137483⟩
private theorem pr137491 : PrimeCertificate 137491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv4583]) (by decide +kernel)
def pv137491 : PrimeValue := ⟨137491, pr137491⟩
private theorem pr137507 : PrimeCertificate 137507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv197,pv349]) (by decide +kernel)
def pv137507 : PrimeValue := ⟨137507, pr137507⟩
private theorem pr137519 : PrimeCertificate 137519 :=
  certifyPrime (q := pv7) (ls := [pv2,pv29,pv2371]) (by decide +kernel)
def pv137519 : PrimeValue := ⟨137519, pr137519⟩
private theorem pr137567 : PrimeCertificate 137567 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv13,pv37]) (by decide +kernel)
def pv137567 : PrimeValue := ⟨137567, pr137567⟩
private theorem pr137573 : PrimeCertificate 137573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv163,pv211]) (by decide +kernel)
def pv137573 : PrimeValue := ⟨137573, pr137573⟩
private theorem pr137587 : PrimeCertificate 137587 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv997]) (by decide +kernel)
def pv137587 : PrimeValue := ⟨137587, pr137587⟩
private theorem pr137593 : PrimeCertificate 137593 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv13]) (by decide +kernel)
def pv137593 : PrimeValue := ⟨137593, pr137593⟩
private theorem pr137597 : PrimeCertificate 137597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv839]) (by decide +kernel)
def pv137597 : PrimeValue := ⟨137597, pr137597⟩
private theorem pr137623 : PrimeCertificate 137623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv22937]) (by decide +kernel)
def pv137623 : PrimeValue := ⟨137623, pr137623⟩
private theorem pr137633 : PrimeCertificate 137633 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv17,pv23]) (by decide +kernel)
def pv137633 : PrimeValue := ⟨137633, pr137633⟩
private theorem pr137639 : PrimeCertificate 137639 :=
  certifyPrime (q := pv13) (ls := [pv2,pv68819]) (by decide +kernel)
def pv137639 : PrimeValue := ⟨137639, pr137639⟩
private theorem pr137653 : PrimeCertificate 137653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11471]) (by decide +kernel)
def pv137653 : PrimeValue := ⟨137653, pr137653⟩
private theorem pr137659 : PrimeCertificate 137659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv22943]) (by decide +kernel)
def pv137659 : PrimeValue := ⟨137659, pr137659⟩
private theorem pr137699 : PrimeCertificate 137699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv569]) (by decide +kernel)
def pv137699 : PrimeValue := ⟨137699, pr137699⟩
private theorem pr137707 : PrimeCertificate 137707 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv59,pv389]) (by decide +kernel)
def pv137707 : PrimeValue := ⟨137707, pr137707⟩
private theorem pr137723 : PrimeCertificate 137723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv5297]) (by decide +kernel)
def pv137723 : PrimeValue := ⟨137723, pr137723⟩
private theorem pr137737 : PrimeCertificate 137737 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1913]) (by decide +kernel)
def pv137737 : PrimeValue := ⟨137737, pr137737⟩
private theorem pr137743 : PrimeCertificate 137743 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv2087]) (by decide +kernel)
def pv137743 : PrimeValue := ⟨137743, pr137743⟩
private theorem pr137771 : PrimeCertificate 137771 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv23,pv599]) (by decide +kernel)
def pv137771 : PrimeValue := ⟨137771, pr137771⟩
private theorem pr137777 : PrimeCertificate 137777 :=
  certifyPrime (q := pv3) (ls := [pv2,pv79,pv109]) (by decide +kernel)
def pv137777 : PrimeValue := ⟨137777, pr137777⟩
private theorem pr137791 : PrimeCertificate 137791 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv1531]) (by decide +kernel)
def pv137791 : PrimeValue := ⟨137791, pr137791⟩
private theorem pr137803 : PrimeCertificate 137803 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv17,pv193]) (by decide +kernel)
def pv137803 : PrimeValue := ⟨137803, pr137803⟩
private theorem pr137827 : PrimeCertificate 137827 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv19,pv31]) (by decide +kernel)
def pv137827 : PrimeValue := ⟨137827, pr137827⟩
private theorem pr137831 : PrimeCertificate 137831 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv11,pv179]) (by decide +kernel)
def pv137831 : PrimeValue := ⟨137831, pr137831⟩
private theorem pr137849 : PrimeCertificate 137849 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17231]) (by decide +kernel)
def pv137849 : PrimeValue := ⟨137849, pr137849⟩
private theorem pr137867 : PrimeCertificate 137867 :=
  certifyPrime (q := pv5) (ls := [pv2,pv29,pv2377]) (by decide +kernel)
def pv137867 : PrimeValue := ⟨137867, pr137867⟩
private theorem pr137869 : PrimeCertificate 137869 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11489]) (by decide +kernel)
def pv137869 : PrimeValue := ⟨137869, pr137869⟩
private theorem pr137873 : PrimeCertificate 137873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv1231]) (by decide +kernel)
def pv137873 : PrimeValue := ⟨137873, pr137873⟩
private theorem pr137909 : PrimeCertificate 137909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv1499]) (by decide +kernel)
def pv137909 : PrimeValue := ⟨137909, pr137909⟩
private theorem pr137911 : PrimeCertificate 137911 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv4597]) (by decide +kernel)
def pv137911 : PrimeValue := ⟨137911, pr137911⟩
private theorem pr137927 : PrimeCertificate 137927 :=
  certifyPrime (q := pv5) (ls := [pv2,pv68963]) (by decide +kernel)
def pv137927 : PrimeValue := ⟨137927, pr137927⟩
private theorem pr137933 : PrimeCertificate 137933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv34483]) (by decide +kernel)
def pv137933 : PrimeValue := ⟨137933, pr137933⟩
private theorem pr137957 : PrimeCertificate 137957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv379]) (by decide +kernel)
def pv137957 : PrimeValue := ⟨137957, pr137957⟩
private theorem pr137983 : PrimeCertificate 137983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv29,pv61]) (by decide +kernel)
def pv137983 : PrimeValue := ⟨137983, pr137983⟩
private theorem pr137993 : PrimeCertificate 137993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv47,pv367]) (by decide +kernel)
def pv137993 : PrimeValue := ⟨137993, pr137993⟩
private theorem pr137999 : PrimeCertificate 137999 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv9857]) (by decide +kernel)
def pv137999 : PrimeValue := ⟨137999, pr137999⟩
private theorem pr138007 : PrimeCertificate 138007 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv17,pv41]) (by decide +kernel)
def pv138007 : PrimeValue := ⟨138007, pr138007⟩
private theorem pr138041 : PrimeCertificate 138041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv17,pv29]) (by decide +kernel)
def pv138041 : PrimeValue := ⟨138041, pr138041⟩
private theorem pr138059 : PrimeCertificate 138059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv69029]) (by decide +kernel)
def pv138059 : PrimeValue := ⟨138059, pr138059⟩
private theorem pr138071 : PrimeCertificate 138071 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv13807]) (by decide +kernel)
def pv138071 : PrimeValue := ⟨138071, pr138071⟩
private theorem pr138079 : PrimeCertificate 138079 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv2557]) (by decide +kernel)
def pv138079 : PrimeValue := ⟨138079, pr138079⟩
private theorem pr138101 : PrimeCertificate 138101 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1381]) (by decide +kernel)
def pv138101 : PrimeValue := ⟨138101, pr138101⟩
private theorem pr138107 : PrimeCertificate 138107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv199,pv347]) (by decide +kernel)
def pv138107 : PrimeValue := ⟨138107, pr138107⟩
private theorem pr138113 : PrimeCertificate 138113 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv83]) (by decide +kernel)
def pv138113 : PrimeValue := ⟨138113, pr138113⟩
private theorem pr138139 : PrimeCertificate 138139 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv11,pv13,pv23]) (by decide +kernel)
def pv138139 : PrimeValue := ⟨138139, pr138139⟩
private theorem pr138143 : PrimeCertificate 138143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv239]) (by decide +kernel)
def pv138143 : PrimeValue := ⟨138143, pr138143⟩
private theorem pr138157 : PrimeCertificate 138157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv397]) (by decide +kernel)
def pv138157 : PrimeValue := ⟨138157, pr138157⟩
private theorem pr138179 : PrimeCertificate 138179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59,pv1171]) (by decide +kernel)
def pv138179 : PrimeValue := ⟨138179, pr138179⟩
private theorem pr138181 : PrimeCertificate 138181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv47]) (by decide +kernel)
def pv138181 : PrimeValue := ⟨138181, pr138181⟩
private theorem pr138191 : PrimeCertificate 138191 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv1063]) (by decide +kernel)
def pv138191 : PrimeValue := ⟨138191, pr138191⟩
private theorem pr138209 : PrimeCertificate 138209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv617]) (by decide +kernel)
def pv138209 : PrimeValue := ⟨138209, pr138209⟩
private theorem pr138239 : PrimeCertificate 138239 :=
  certifyPrime (q := pv17) (ls := [pv2,pv69119]) (by decide +kernel)
def pv138239 : PrimeValue := ⟨138239, pr138239⟩
private theorem pr138241 : PrimeCertificate 138241 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv138241 : PrimeValue := ⟨138241, pr138241⟩
private theorem pr138247 : PrimeCertificate 138247 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23041]) (by decide +kernel)
def pv138247 : PrimeValue := ⟨138247, pr138247⟩
private theorem pr138251 : PrimeCertificate 138251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv79]) (by decide +kernel)
def pv138251 : PrimeValue := ⟨138251, pr138251⟩
private theorem pr138283 : PrimeCertificate 138283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv1213]) (by decide +kernel)
def pv138283 : PrimeValue := ⟨138283, pr138283⟩
private theorem pr138289 : PrimeCertificate 138289 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv43,pv67]) (by decide +kernel)
def pv138289 : PrimeValue := ⟨138289, pr138289⟩
private theorem pr138311 : PrimeCertificate 138311 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv13831]) (by decide +kernel)
def pv138311 : PrimeValue := ⟨138311, pr138311⟩
private theorem pr138319 : PrimeCertificate 138319 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23053]) (by decide +kernel)
def pv138319 : PrimeValue := ⟨138319, pr138319⟩
private theorem pr138323 : PrimeCertificate 138323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv31,pv97]) (by decide +kernel)
def pv138323 : PrimeValue := ⟨138323, pr138323⟩
private theorem pr138337 : PrimeCertificate 138337 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv11,pv131]) (by decide +kernel)
def pv138337 : PrimeValue := ⟨138337, pr138337⟩
private theorem pr138349 : PrimeCertificate 138349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv61]) (by decide +kernel)
def pv138349 : PrimeValue := ⟨138349, pr138349⟩
private theorem pr138371 : PrimeCertificate 138371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv101,pv137]) (by decide +kernel)
def pv138371 : PrimeValue := ⟨138371, pr138371⟩
private theorem pr138373 : PrimeCertificate 138373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv887]) (by decide +kernel)
def pv138373 : PrimeValue := ⟨138373, pr138373⟩
private theorem pr138389 : PrimeCertificate 138389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv1193]) (by decide +kernel)
def pv138389 : PrimeValue := ⟨138389, pr138389⟩
private theorem pr138403 : PrimeCertificate 138403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv233]) (by decide +kernel)
def pv138403 : PrimeValue := ⟨138403, pr138403⟩
private theorem pr138407 : PrimeCertificate 138407 :=
  certifyPrime (q := pv5) (ls := [pv2,pv69203]) (by decide +kernel)
def pv138407 : PrimeValue := ⟨138407, pr138407⟩
private theorem pr138427 : PrimeCertificate 138427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23071]) (by decide +kernel)
def pv138427 : PrimeValue := ⟨138427, pr138427⟩
private theorem pr138433 : PrimeCertificate 138433 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv103]) (by decide +kernel)
def pv138433 : PrimeValue := ⟨138433, pr138433⟩
private theorem pr138449 : PrimeCertificate 138449 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv509]) (by decide +kernel)
def pv138449 : PrimeValue := ⟨138449, pr138449⟩
private theorem pr138451 : PrimeCertificate 138451 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv71]) (by decide +kernel)
def pv138451 : PrimeValue := ⟨138451, pr138451⟩
private theorem pr138461 : PrimeCertificate 138461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv23,pv43]) (by decide +kernel)
def pv138461 : PrimeValue := ⟨138461, pr138461⟩
private theorem pr138469 : PrimeCertificate 138469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv1049]) (by decide +kernel)
def pv138469 : PrimeValue := ⟨138469, pr138469⟩
private theorem pr138493 : PrimeCertificate 138493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3847]) (by decide +kernel)
def pv138493 : PrimeValue := ⟨138493, pr138493⟩
private theorem pr138497 : PrimeCertificate 138497 :=
  certifyPrime (q := pv3) (ls := [pv2,pv541]) (by decide +kernel)
def pv138497 : PrimeValue := ⟨138497, pr138497⟩
private theorem pr138511 : PrimeCertificate 138511 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv138511 : PrimeValue := ⟨138511, pr138511⟩
private theorem pr138517 : PrimeCertificate 138517 :=
  certifyPrime (q := pv59) (ls := [pv2,pv3,pv7,pv17,pv97]) (by decide +kernel)
def pv138517 : PrimeValue := ⟨138517, pr138517⟩
private theorem pr138547 : PrimeCertificate 138547 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv43,pv179]) (by decide +kernel)
def pv138547 : PrimeValue := ⟨138547, pr138547⟩
private theorem pr138559 : PrimeCertificate 138559 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv3299]) (by decide +kernel)
def pv138559 : PrimeValue := ⟨138559, pr138559⟩
private theorem pr138563 : PrimeCertificate 138563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv2389]) (by decide +kernel)
def pv138563 : PrimeValue := ⟨138563, pr138563⟩
private theorem pr138569 : PrimeCertificate 138569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17321]) (by decide +kernel)
def pv138569 : PrimeValue := ⟨138569, pr138569⟩
private theorem pr138571 : PrimeCertificate 138571 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv31,pv149]) (by decide +kernel)
def pv138571 : PrimeValue := ⟨138571, pr138571⟩
private theorem pr138577 : PrimeCertificate 138577 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2887]) (by decide +kernel)
def pv138577 : PrimeValue := ⟨138577, pr138577⟩
private theorem pr138581 : PrimeCertificate 138581 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv41]) (by decide +kernel)
def pv138581 : PrimeValue := ⟨138581, pr138581⟩
private theorem pr138587 : PrimeCertificate 138587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv19,pv521]) (by decide +kernel)
def pv138587 : PrimeValue := ⟨138587, pr138587⟩
private theorem pr138599 : PrimeCertificate 138599 :=
  certifyPrime (q := pv23) (ls := [pv2,pv23,pv131]) (by decide +kernel)
def pv138599 : PrimeValue := ⟨138599, pr138599⟩
private theorem pr138617 : PrimeCertificate 138617 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17327]) (by decide +kernel)
def pv138617 : PrimeValue := ⟨138617, pr138617⟩
private theorem pr138629 : PrimeCertificate 138629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv4951]) (by decide +kernel)
def pv138629 : PrimeValue := ⟨138629, pr138629⟩
private theorem pr138641 : PrimeCertificate 138641 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1733]) (by decide +kernel)
def pv138641 : PrimeValue := ⟨138641, pr138641⟩
private theorem pr138661 : PrimeCertificate 138661 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv2311]) (by decide +kernel)
def pv138661 : PrimeValue := ⟨138661, pr138661⟩
private theorem pr138683 : PrimeCertificate 138683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv69341]) (by decide +kernel)
def pv138683 : PrimeValue := ⟨138683, pr138683⟩
private theorem pr138727 : PrimeCertificate 138727 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv367]) (by decide +kernel)
def pv138727 : PrimeValue := ⟨138727, pr138727⟩
private theorem pr138739 : PrimeCertificate 138739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv1217]) (by decide +kernel)
def pv138739 : PrimeValue := ⟨138739, pr138739⟩
private theorem pr138763 : PrimeCertificate 138763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv593]) (by decide +kernel)
def pv138763 : PrimeValue := ⟨138763, pr138763⟩
private theorem pr138793 : PrimeCertificate 138793 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv5783]) (by decide +kernel)
def pv138793 : PrimeValue := ⟨138793, pr138793⟩
private theorem pr138797 : PrimeCertificate 138797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv4957]) (by decide +kernel)
def pv138797 : PrimeValue := ⟨138797, pr138797⟩
private theorem pr138799 : PrimeCertificate 138799 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11,pv701]) (by decide +kernel)
def pv138799 : PrimeValue := ⟨138799, pr138799⟩
private theorem pr138821 : PrimeCertificate 138821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv631]) (by decide +kernel)
def pv138821 : PrimeValue := ⟨138821, pr138821⟩
private theorem pr138841 : PrimeCertificate 138841 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv13,pv89]) (by decide +kernel)
def pv138841 : PrimeValue := ⟨138841, pr138841⟩
private theorem pr138863 : PrimeCertificate 138863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv69431]) (by decide +kernel)
def pv138863 : PrimeValue := ⟨138863, pr138863⟩
private theorem pr138869 : PrimeCertificate 138869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv149,pv233]) (by decide +kernel)
def pv138869 : PrimeValue := ⟨138869, pr138869⟩
private theorem pr138883 : PrimeCertificate 138883 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv79,pv293]) (by decide +kernel)
def pv138883 : PrimeValue := ⟨138883, pr138883⟩
private theorem pr138889 : PrimeCertificate 138889 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv643]) (by decide +kernel)
def pv138889 : PrimeValue := ⟨138889, pr138889⟩
private theorem pr138893 : PrimeCertificate 138893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv2671]) (by decide +kernel)
def pv138893 : PrimeValue := ⟨138893, pr138893⟩
private theorem pr138899 : PrimeCertificate 138899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv1877]) (by decide +kernel)
def pv138899 : PrimeValue := ⟨138899, pr138899⟩
private theorem pr138917 : PrimeCertificate 138917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv34729]) (by decide +kernel)
def pv138917 : PrimeValue := ⟨138917, pr138917⟩
private theorem pr138923 : PrimeCertificate 138923 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv9923]) (by decide +kernel)
def pv138923 : PrimeValue := ⟨138923, pr138923⟩
private theorem pr138937 : PrimeCertificate 138937 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv827]) (by decide +kernel)
def pv138937 : PrimeValue := ⟨138937, pr138937⟩
private theorem pr138959 : PrimeCertificate 138959 :=
  certifyPrime (q := pv7) (ls := [pv2,pv17,pv61,pv67]) (by decide +kernel)
def pv138959 : PrimeValue := ⟨138959, pr138959⟩
private theorem pr138977 : PrimeCertificate 138977 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43,pv101]) (by decide +kernel)
def pv138977 : PrimeValue := ⟨138977, pr138977⟩
private theorem pr139021 : PrimeCertificate 139021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv331]) (by decide +kernel)
def pv139021 : PrimeValue := ⟨139021, pr139021⟩
private theorem pr139033 : PrimeCertificate 139033 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1931]) (by decide +kernel)
def pv139033 : PrimeValue := ⟨139033, pr139033⟩
private theorem pr139067 : PrimeCertificate 139067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv2243]) (by decide +kernel)
def pv139067 : PrimeValue := ⟨139067, pr139067⟩
private theorem pr139079 : PrimeCertificate 139079 :=
  certifyPrime (q := pv13) (ls := [pv2,pv69539]) (by decide +kernel)
def pv139079 : PrimeValue := ⟨139079, pr139079⟩
private theorem pr139091 : PrimeCertificate 139091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv1987]) (by decide +kernel)
def pv139091 : PrimeValue := ⟨139091, pr139091⟩
private theorem pr139109 : PrimeCertificate 139109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv83,pv419]) (by decide +kernel)
def pv139109 : PrimeValue := ⟨139109, pr139109⟩
private theorem pr139121 : PrimeCertificate 139121 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv37,pv47]) (by decide +kernel)
def pv139121 : PrimeValue := ⟨139121, pr139121⟩
private theorem pr139123 : PrimeCertificate 139123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv59,pv131]) (by decide +kernel)
def pv139123 : PrimeValue := ⟨139123, pr139123⟩
private theorem pr139133 : PrimeCertificate 139133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv4969]) (by decide +kernel)
def pv139133 : PrimeValue := ⟨139133, pr139133⟩
private theorem pr139169 : PrimeCertificate 139169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv4349]) (by decide +kernel)
def pv139169 : PrimeValue := ⟨139169, pr139169⟩
private theorem pr139177 : PrimeCertificate 139177 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv1933]) (by decide +kernel)
def pv139177 : PrimeValue := ⟨139177, pr139177⟩
private theorem pr139187 : PrimeCertificate 139187 :=
  certifyPrime (q := pv2) (ls := [pv2,pv69593]) (by decide +kernel)
def pv139187 : PrimeValue := ⟨139187, pr139187⟩
private theorem pr139201 : PrimeCertificate 139201 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv29]) (by decide +kernel)
def pv139201 : PrimeValue := ⟨139201, pr139201⟩
private theorem pr139267 : PrimeCertificate 139267 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv2579]) (by decide +kernel)
def pv139267 : PrimeValue := ⟨139267, pr139267⟩
private theorem pr139273 : PrimeCertificate 139273 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv829]) (by decide +kernel)
def pv139273 : PrimeValue := ⟨139273, pr139273⟩
private theorem pr139291 : PrimeCertificate 139291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv4643]) (by decide +kernel)
def pv139291 : PrimeValue := ⟨139291, pr139291⟩
private theorem pr139297 : PrimeCertificate 139297 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv1451]) (by decide +kernel)
def pv139297 : PrimeValue := ⟨139297, pr139297⟩
private theorem pr139303 : PrimeCertificate 139303 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv71,pv109]) (by decide +kernel)
def pv139303 : PrimeValue := ⟨139303, pr139303⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
