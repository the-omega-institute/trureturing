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

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr135977 : Nat.Prime 135977 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv739]) (by decide +kernel)
def pv135977 : PrimeValue := ⟨135977, pr135977⟩
private theorem pr136027 : Nat.Prime 136027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv229]) (by decide +kernel)
def pv136027 : PrimeValue := ⟨136027, pr136027⟩
private theorem pr136033 : Nat.Prime 136033 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv109]) (by decide +kernel)
def pv136033 : PrimeValue := ⟨136033, pr136033⟩
private theorem pr136057 : Nat.Prime 136057 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv5669]) (by decide +kernel)
def pv136057 : PrimeValue := ⟨136057, pr136057⟩
private theorem pr136067 : Nat.Prime 136067 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv9719]) (by decide +kernel)
def pv136067 : PrimeValue := ⟨136067, pr136067⟩
private theorem pr136069 : Nat.Prime 136069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv23,pv29]) (by decide +kernel)
def pv136069 : PrimeValue := ⟨136069, pr136069⟩
private theorem pr136093 : Nat.Prime 136093 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv1031]) (by decide +kernel)
def pv136093 : PrimeValue := ⟨136093, pr136093⟩
private theorem pr136111 : Nat.Prime 136111 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv349]) (by decide +kernel)
def pv136111 : PrimeValue := ⟨136111, pr136111⟩
private theorem pr136133 : Nat.Prime 136133 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv34033]) (by decide +kernel)
def pv136133 : PrimeValue := ⟨136133, pr136133⟩
private theorem pr136139 : Nat.Prime 136139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv1583]) (by decide +kernel)
def pv136139 : PrimeValue := ⟨136139, pr136139⟩
private theorem pr136189 : Nat.Prime 136189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv97]) (by decide +kernel)
def pv136189 : PrimeValue := ⟨136189, pr136189⟩
private theorem pr136193 : Nat.Prime 136193 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv19]) (by decide +kernel)
def pv136193 : PrimeValue := ⟨136193, pr136193⟩
private theorem pr136207 : Nat.Prime 136207 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv23,pv47]) (by decide +kernel)
def pv136207 : PrimeValue := ⟨136207, pr136207⟩
private theorem pr136217 : Nat.Prime 136217 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17027]) (by decide +kernel)
def pv136217 : PrimeValue := ⟨136217, pr136217⟩
private theorem pr136223 : Nat.Prime 136223 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv68111]) (by decide +kernel)
def pv136223 : PrimeValue := ⟨136223, pr136223⟩
private theorem pr136237 : Nat.Prime 136237 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11353]) (by decide +kernel)
def pv136237 : PrimeValue := ⟨136237, pr136237⟩
private theorem pr136247 : Nat.Prime 136247 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv563]) (by decide +kernel)
def pv136247 : PrimeValue := ⟨136247, pr136247⟩
private theorem pr136261 : Nat.Prime 136261 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv757]) (by decide +kernel)
def pv136261 : PrimeValue := ⟨136261, pr136261⟩
private theorem pr136273 : Nat.Prime 136273 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv167]) (by decide +kernel)
def pv136273 : PrimeValue := ⟨136273, pr136273⟩
private theorem pr136277 : Nat.Prime 136277 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv31,pv157]) (by decide +kernel)
def pv136277 : PrimeValue := ⟨136277, pr136277⟩
private theorem pr136303 : Nat.Prime 136303 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv22717]) (by decide +kernel)
def pv136303 : PrimeValue := ⟨136303, pr136303⟩
private theorem pr136319 : Nat.Prime 136319 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv13,pv107]) (by decide +kernel)
def pv136319 : PrimeValue := ⟨136319, pr136319⟩
private theorem pr136327 : Nat.Prime 136327 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv22721]) (by decide +kernel)
def pv136327 : PrimeValue := ⟨136327, pr136327⟩
private theorem pr136333 : Nat.Prime 136333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv541]) (by decide +kernel)
def pv136333 : PrimeValue := ⟨136333, pr136333⟩
private theorem pr136337 : Nat.Prime 136337 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv8521]) (by decide +kernel)
def pv136337 : PrimeValue := ⟨136337, pr136337⟩
private theorem pr136351 : Nat.Prime 136351 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv101]) (by decide +kernel)
def pv136351 : PrimeValue := ⟨136351, pr136351⟩
private theorem pr136361 : Nat.Prime 136361 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv7,pv487]) (by decide +kernel)
def pv136361 : PrimeValue := ⟨136361, pr136361⟩
private theorem pr136373 : Nat.Prime 136373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv103,pv331]) (by decide +kernel)
def pv136373 : PrimeValue := ⟨136373, pr136373⟩
private theorem pr136379 : Nat.Prime 136379 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv11,pv6199]) (by decide +kernel)
def pv136379 : PrimeValue := ⟨136379, pr136379⟩
private theorem pr136393 : Nat.Prime 136393 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv5683]) (by decide +kernel)
def pv136393 : PrimeValue := ⟨136393, pr136393⟩
private theorem pr136397 : Nat.Prime 136397 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv43,pv61]) (by decide +kernel)
def pv136397 : PrimeValue := ⟨136397, pr136397⟩
private theorem pr136399 : Nat.Prime 136399 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv127,pv179]) (by decide +kernel)
def pv136399 : PrimeValue := ⟨136399, pr136399⟩
private theorem pr136403 : Nat.Prime 136403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv9743]) (by decide +kernel)
def pv136403 : PrimeValue := ⟨136403, pr136403⟩
private theorem pr136417 : Nat.Prime 136417 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv29]) (by decide +kernel)
def pv136417 : PrimeValue := ⟨136417, pr136417⟩
private theorem pr136421 : Nat.Prime 136421 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv19,pv359]) (by decide +kernel)
def pv136421 : PrimeValue := ⟨136421, pr136421⟩
private theorem pr136429 : Nat.Prime 136429 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11369]) (by decide +kernel)
def pv136429 : PrimeValue := ⟨136429, pr136429⟩
private theorem pr136447 : Nat.Prime 136447 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv22741]) (by decide +kernel)
def pv136447 : PrimeValue := ⟨136447, pr136447⟩
private theorem pr136453 : Nat.Prime 136453 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv83,pv137]) (by decide +kernel)
def pv136453 : PrimeValue := ⟨136453, pr136453⟩
private theorem pr136463 : Nat.Prime 136463 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv31,pv71]) (by decide +kernel)
def pv136463 : PrimeValue := ⟨136463, pr136463⟩
private theorem pr136471 : Nat.Prime 136471 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv4549]) (by decide +kernel)
def pv136471 : PrimeValue := ⟨136471, pr136471⟩
private theorem pr136481 : Nat.Prime 136481 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv853]) (by decide +kernel)
def pv136481 : PrimeValue := ⟨136481, pr136481⟩
private theorem pr136483 : Nat.Prime 136483 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv43]) (by decide +kernel)
def pv136483 : PrimeValue := ⟨136483, pr136483⟩
private theorem pr136501 : Nat.Prime 136501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv13]) (by decide +kernel)
def pv136501 : PrimeValue := ⟨136501, pr136501⟩
private theorem pr136511 : Nat.Prime 136511 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv17,pv73]) (by decide +kernel)
def pv136511 : PrimeValue := ⟨136511, pr136511⟩
private theorem pr136519 : Nat.Prime 136519 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv61,pv373]) (by decide +kernel)
def pv136519 : PrimeValue := ⟨136519, pr136519⟩
private theorem pr136523 : Nat.Prime 136523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv68261]) (by decide +kernel)
def pv136523 : PrimeValue := ⟨136523, pr136523⟩
private theorem pr136531 : Nat.Prime 136531 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv37,pv41]) (by decide +kernel)
def pv136531 : PrimeValue := ⟨136531, pr136531⟩
private theorem pr136537 : Nat.Prime 136537 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv5689]) (by decide +kernel)
def pv136537 : PrimeValue := ⟨136537, pr136537⟩
private theorem pr136541 : Nat.Prime 136541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv6827]) (by decide +kernel)
def pv136541 : PrimeValue := ⟨136541, pr136541⟩
private theorem pr136559 : Nat.Prime 136559 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv68279]) (by decide +kernel)
def pv136559 : PrimeValue := ⟨136559, pr136559⟩
private theorem pr136573 : Nat.Prime 136573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv599]) (by decide +kernel)
def pv136573 : PrimeValue := ⟨136573, pr136573⟩
private theorem pr136601 : Nat.Prime 136601 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv683]) (by decide +kernel)
def pv136601 : PrimeValue := ⟨136601, pr136601⟩
private theorem pr136603 : Nat.Prime 136603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7589]) (by decide +kernel)
def pv136603 : PrimeValue := ⟨136603, pr136603⟩
private theorem pr136607 : Nat.Prime 136607 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv167,pv409]) (by decide +kernel)
def pv136607 : PrimeValue := ⟨136607, pr136607⟩
private theorem pr136649 : Nat.Prime 136649 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv29,pv31]) (by decide +kernel)
def pv136649 : PrimeValue := ⟨136649, pr136649⟩
private theorem pr136651 : Nat.Prime 136651 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv911]) (by decide +kernel)
def pv136651 : PrimeValue := ⟨136651, pr136651⟩
private theorem pr136657 : Nat.Prime 136657 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv73]) (by decide +kernel)
def pv136657 : PrimeValue := ⟨136657, pr136657⟩
private theorem pr136691 : Nat.Prime 136691 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13669]) (by decide +kernel)
def pv136691 : PrimeValue := ⟨136691, pr136691⟩
private theorem pr136693 : Nat.Prime 136693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv3797]) (by decide +kernel)
def pv136693 : PrimeValue := ⟨136693, pr136693⟩
private theorem pr136709 : Nat.Prime 136709 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv13,pv239]) (by decide +kernel)
def pv136709 : PrimeValue := ⟨136709, pr136709⟩
private theorem pr136727 : Nat.Prime 136727 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv137,pv499]) (by decide +kernel)
def pv136727 : PrimeValue := ⟨136727, pr136727⟩
private theorem pr136733 : Nat.Prime 136733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv34183]) (by decide +kernel)
def pv136733 : PrimeValue := ⟨136733, pr136733⟩
private theorem pr136739 : Nat.Prime 136739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv9767]) (by decide +kernel)
def pv136739 : PrimeValue := ⟨136739, pr136739⟩
private theorem pr136751 : Nat.Prime 136751 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv5,pv547]) (by decide +kernel)
def pv136751 : PrimeValue := ⟨136751, pr136751⟩
private theorem pr136753 : Nat.Prime 136753 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv37]) (by decide +kernel)
def pv136753 : PrimeValue := ⟨136753, pr136753⟩
private theorem pr136769 : Nat.Prime 136769 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2137]) (by decide +kernel)
def pv136769 : PrimeValue := ⟨136769, pr136769⟩
private theorem pr136811 : Nat.Prime 136811 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13681]) (by decide +kernel)
def pv136811 : PrimeValue := ⟨136811, pr136811⟩
private theorem pr136813 : Nat.Prime 136813 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv877]) (by decide +kernel)
def pv136813 : PrimeValue := ⟨136813, pr136813⟩
private theorem pr136841 : Nat.Prime 136841 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv311]) (by decide +kernel)
def pv136841 : PrimeValue := ⟨136841, pr136841⟩
private theorem pr136849 : Nat.Prime 136849 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv2851]) (by decide +kernel)
def pv136849 : PrimeValue := ⟨136849, pr136849⟩
private theorem pr136859 : Nat.Prime 136859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv1669]) (by decide +kernel)
def pv136859 : PrimeValue := ⟨136859, pr136859⟩
private theorem pr136861 : Nat.Prime 136861 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv2281]) (by decide +kernel)
def pv136861 : PrimeValue := ⟨136861, pr136861⟩
private theorem pr136879 : Nat.Prime 136879 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv3259]) (by decide +kernel)
def pv136879 : PrimeValue := ⟨136879, pr136879⟩
private theorem pr136883 : Nat.Prime 136883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv89,pv769]) (by decide +kernel)
def pv136883 : PrimeValue := ⟨136883, pr136883⟩
private theorem pr136889 : Nat.Prime 136889 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv71,pv241]) (by decide +kernel)
def pv136889 : PrimeValue := ⟨136889, pr136889⟩
private theorem pr136897 : Nat.Prime 136897 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23,pv31]) (by decide +kernel)
def pv136897 : PrimeValue := ⟨136897, pr136897⟩
private theorem pr136943 : Nat.Prime 136943 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv23,pv229]) (by decide +kernel)
def pv136943 : PrimeValue := ⟨136943, pr136943⟩
private theorem pr136949 : Nat.Prime 136949 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv67,pv73]) (by decide +kernel)
def pv136949 : PrimeValue := ⟨136949, pr136949⟩
private theorem pr136963 : Nat.Prime 136963 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv1087]) (by decide +kernel)
def pv136963 : PrimeValue := ⟨136963, pr136963⟩
private theorem pr136973 : Nat.Prime 136973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv283]) (by decide +kernel)
def pv136973 : PrimeValue := ⟨136973, pr136973⟩
private theorem pr136979 : Nat.Prime 136979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv68489]) (by decide +kernel)
def pv136979 : PrimeValue := ⟨136979, pr136979⟩
private theorem pr136987 : Nat.Prime 136987 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv17,pv79]) (by decide +kernel)
def pv136987 : PrimeValue := ⟨136987, pr136987⟩
private theorem pr136991 : Nat.Prime 136991 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv7,pv19,pv103]) (by decide +kernel)
def pv136991 : PrimeValue := ⟨136991, pr136991⟩
private theorem pr136993 : Nat.Prime 136993 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1427]) (by decide +kernel)
def pv136993 : PrimeValue := ⟨136993, pr136993⟩
private theorem pr136999 : Nat.Prime 136999 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv43,pv59]) (by decide +kernel)
def pv136999 : PrimeValue := ⟨136999, pr136999⟩
private theorem pr137029 : Nat.Prime 137029 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv19,pv601]) (by decide +kernel)
def pv137029 : PrimeValue := ⟨137029, pr137029⟩
private theorem pr137077 : Nat.Prime 137077 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11423]) (by decide +kernel)
def pv137077 : PrimeValue := ⟨137077, pr137077⟩
private theorem pr137087 : Nat.Prime 137087 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv68543]) (by decide +kernel)
def pv137087 : PrimeValue := ⟨137087, pr137087⟩
private theorem pr137089 : Nat.Prime 137089 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv17]) (by decide +kernel)
def pv137089 : PrimeValue := ⟨137089, pr137089⟩
private theorem pr137119 : Nat.Prime 137119 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv22853]) (by decide +kernel)
def pv137119 : PrimeValue := ⟨137119, pr137119⟩
private theorem pr137143 : Nat.Prime 137143 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv19,pv401]) (by decide +kernel)
def pv137143 : PrimeValue := ⟨137143, pr137143⟩
private theorem pr137147 : Nat.Prime 137147 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv1459]) (by decide +kernel)
def pv137147 : PrimeValue := ⟨137147, pr137147⟩
private theorem pr137153 : Nat.Prime 137153 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2143]) (by decide +kernel)
def pv137153 : PrimeValue := ⟨137153, pr137153⟩
private theorem pr137177 : Nat.Prime 137177 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv1319]) (by decide +kernel)
def pv137177 : PrimeValue := ⟨137177, pr137177⟩
private theorem pr137191 : Nat.Prime 137191 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv17,pv269]) (by decide +kernel)
def pv137191 : PrimeValue := ⟨137191, pr137191⟩
private theorem pr137197 : Nat.Prime 137197 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv103]) (by decide +kernel)
def pv137197 : PrimeValue := ⟨137197, pr137197⟩
private theorem pr137201 : Nat.Prime 137201 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7]) (by decide +kernel)
def pv137201 : PrimeValue := ⟨137201, pr137201⟩
private theorem pr137209 : Nat.Prime 137209 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5717]) (by decide +kernel)
def pv137209 : PrimeValue := ⟨137209, pr137209⟩
private theorem pr137219 : Nat.Prime 137219 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv23,pv157]) (by decide +kernel)
def pv137219 : PrimeValue := ⟨137219, pr137219⟩
private theorem pr137239 : Nat.Prime 137239 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv89,pv257]) (by decide +kernel)
def pv137239 : PrimeValue := ⟨137239, pr137239⟩
private theorem pr137251 : Nat.Prime 137251 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv61]) (by decide +kernel)
def pv137251 : PrimeValue := ⟨137251, pr137251⟩
private theorem pr137273 : Nat.Prime 137273 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17159]) (by decide +kernel)
def pv137273 : PrimeValue := ⟨137273, pr137273⟩
private theorem pr137279 : Nat.Prime 137279 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv68639]) (by decide +kernel)
def pv137279 : PrimeValue := ⟨137279, pr137279⟩
private theorem pr137303 : Nat.Prime 137303 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv79]) (by decide +kernel)
def pv137303 : PrimeValue := ⟨137303, pr137303⟩
private theorem pr137321 : Nat.Prime 137321 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv3433]) (by decide +kernel)
def pv137321 : PrimeValue := ⟨137321, pr137321⟩
private theorem pr137339 : Nat.Prime 137339 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv68669]) (by decide +kernel)
def pv137339 : PrimeValue := ⟨137339, pr137339⟩
private theorem pr137341 : Nat.Prime 137341 :=
  checkPrime_prime (q := pv43) (ls := [pv2,pv3,pv5,pv7,pv109]) (by decide +kernel)
def pv137341 : PrimeValue := ⟨137341, pr137341⟩
private theorem pr137353 : Nat.Prime 137353 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv59,pv97]) (by decide +kernel)
def pv137353 : PrimeValue := ⟨137353, pr137353⟩
private theorem pr137359 : Nat.Prime 137359 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv13,pv587]) (by decide +kernel)
def pv137359 : PrimeValue := ⟨137359, pr137359⟩
private theorem pr137363 : Nat.Prime 137363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv173,pv397]) (by decide +kernel)
def pv137363 : PrimeValue := ⟨137363, pr137363⟩
private theorem pr137369 : Nat.Prime 137369 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv7,pv11,pv223]) (by decide +kernel)
def pv137369 : PrimeValue := ⟨137369, pr137369⟩
private theorem pr137383 : Nat.Prime 137383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv3271]) (by decide +kernel)
def pv137383 : PrimeValue := ⟨137383, pr137383⟩
private theorem pr137387 : Nat.Prime 137387 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv73,pv941]) (by decide +kernel)
def pv137387 : PrimeValue := ⟨137387, pr137387⟩
private theorem pr137393 : Nat.Prime 137393 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv277]) (by decide +kernel)
def pv137393 : PrimeValue := ⟨137393, pr137393⟩
private theorem pr137399 : Nat.Prime 137399 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv68699]) (by decide +kernel)
def pv137399 : PrimeValue := ⟨137399, pr137399⟩
private theorem pr137413 : Nat.Prime 137413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv347]) (by decide +kernel)
def pv137413 : PrimeValue := ⟨137413, pr137413⟩
private theorem pr137437 : Nat.Prime 137437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv881]) (by decide +kernel)
def pv137437 : PrimeValue := ⟨137437, pr137437⟩
private theorem pr137443 : Nat.Prime 137443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv22907]) (by decide +kernel)
def pv137443 : PrimeValue := ⟨137443, pr137443⟩
private theorem pr137447 : Nat.Prime 137447 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv3617]) (by decide +kernel)
def pv137447 : PrimeValue := ⟨137447, pr137447⟩
private theorem pr137453 : Nat.Prime 137453 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv4909]) (by decide +kernel)
def pv137453 : PrimeValue := ⟨137453, pr137453⟩
private theorem pr137477 : Nat.Prime 137477 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv34369]) (by decide +kernel)
def pv137477 : PrimeValue := ⟨137477, pr137477⟩
private theorem pr137483 : Nat.Prime 137483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53,pv1297]) (by decide +kernel)
def pv137483 : PrimeValue := ⟨137483, pr137483⟩
private theorem pr137491 : Nat.Prime 137491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv4583]) (by decide +kernel)
def pv137491 : PrimeValue := ⟨137491, pr137491⟩
private theorem pr137507 : Nat.Prime 137507 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv197,pv349]) (by decide +kernel)
def pv137507 : PrimeValue := ⟨137507, pr137507⟩
private theorem pr137519 : Nat.Prime 137519 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv29,pv2371]) (by decide +kernel)
def pv137519 : PrimeValue := ⟨137519, pr137519⟩
private theorem pr137567 : Nat.Prime 137567 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv11,pv13,pv37]) (by decide +kernel)
def pv137567 : PrimeValue := ⟨137567, pr137567⟩
private theorem pr137573 : Nat.Prime 137573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv163,pv211]) (by decide +kernel)
def pv137573 : PrimeValue := ⟨137573, pr137573⟩
private theorem pr137587 : Nat.Prime 137587 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv997]) (by decide +kernel)
def pv137587 : PrimeValue := ⟨137587, pr137587⟩
private theorem pr137593 : Nat.Prime 137593 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv7,pv13]) (by decide +kernel)
def pv137593 : PrimeValue := ⟨137593, pr137593⟩
private theorem pr137597 : Nat.Prime 137597 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv839]) (by decide +kernel)
def pv137597 : PrimeValue := ⟨137597, pr137597⟩
private theorem pr137623 : Nat.Prime 137623 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv22937]) (by decide +kernel)
def pv137623 : PrimeValue := ⟨137623, pr137623⟩
private theorem pr137633 : Nat.Prime 137633 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv17,pv23]) (by decide +kernel)
def pv137633 : PrimeValue := ⟨137633, pr137633⟩
private theorem pr137639 : Nat.Prime 137639 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv68819]) (by decide +kernel)
def pv137639 : PrimeValue := ⟨137639, pr137639⟩
private theorem pr137653 : Nat.Prime 137653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11471]) (by decide +kernel)
def pv137653 : PrimeValue := ⟨137653, pr137653⟩
private theorem pr137659 : Nat.Prime 137659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv22943]) (by decide +kernel)
def pv137659 : PrimeValue := ⟨137659, pr137659⟩
private theorem pr137699 : Nat.Prime 137699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv569]) (by decide +kernel)
def pv137699 : PrimeValue := ⟨137699, pr137699⟩
private theorem pr137707 : Nat.Prime 137707 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv59,pv389]) (by decide +kernel)
def pv137707 : PrimeValue := ⟨137707, pr137707⟩
private theorem pr137723 : Nat.Prime 137723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv5297]) (by decide +kernel)
def pv137723 : PrimeValue := ⟨137723, pr137723⟩
private theorem pr137737 : Nat.Prime 137737 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1913]) (by decide +kernel)
def pv137737 : PrimeValue := ⟨137737, pr137737⟩
private theorem pr137743 : Nat.Prime 137743 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv2087]) (by decide +kernel)
def pv137743 : PrimeValue := ⟨137743, pr137743⟩
private theorem pr137771 : Nat.Prime 137771 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv23,pv599]) (by decide +kernel)
def pv137771 : PrimeValue := ⟨137771, pr137771⟩
private theorem pr137777 : Nat.Prime 137777 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv79,pv109]) (by decide +kernel)
def pv137777 : PrimeValue := ⟨137777, pr137777⟩
private theorem pr137791 : Nat.Prime 137791 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv1531]) (by decide +kernel)
def pv137791 : PrimeValue := ⟨137791, pr137791⟩
private theorem pr137803 : Nat.Prime 137803 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv17,pv193]) (by decide +kernel)
def pv137803 : PrimeValue := ⟨137803, pr137803⟩
private theorem pr137827 : Nat.Prime 137827 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv19,pv31]) (by decide +kernel)
def pv137827 : PrimeValue := ⟨137827, pr137827⟩
private theorem pr137831 : Nat.Prime 137831 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv11,pv179]) (by decide +kernel)
def pv137831 : PrimeValue := ⟨137831, pr137831⟩
private theorem pr137849 : Nat.Prime 137849 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17231]) (by decide +kernel)
def pv137849 : PrimeValue := ⟨137849, pr137849⟩
private theorem pr137867 : Nat.Prime 137867 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv29,pv2377]) (by decide +kernel)
def pv137867 : PrimeValue := ⟨137867, pr137867⟩
private theorem pr137869 : Nat.Prime 137869 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv11489]) (by decide +kernel)
def pv137869 : PrimeValue := ⟨137869, pr137869⟩
private theorem pr137873 : Nat.Prime 137873 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv1231]) (by decide +kernel)
def pv137873 : PrimeValue := ⟨137873, pr137873⟩
private theorem pr137909 : Nat.Prime 137909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv1499]) (by decide +kernel)
def pv137909 : PrimeValue := ⟨137909, pr137909⟩
private theorem pr137911 : Nat.Prime 137911 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv4597]) (by decide +kernel)
def pv137911 : PrimeValue := ⟨137911, pr137911⟩
private theorem pr137927 : Nat.Prime 137927 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv68963]) (by decide +kernel)
def pv137927 : PrimeValue := ⟨137927, pr137927⟩
private theorem pr137933 : Nat.Prime 137933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv34483]) (by decide +kernel)
def pv137933 : PrimeValue := ⟨137933, pr137933⟩
private theorem pr137957 : Nat.Prime 137957 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv13,pv379]) (by decide +kernel)
def pv137957 : PrimeValue := ⟨137957, pr137957⟩
private theorem pr137983 : Nat.Prime 137983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv29,pv61]) (by decide +kernel)
def pv137983 : PrimeValue := ⟨137983, pr137983⟩
private theorem pr137993 : Nat.Prime 137993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv47,pv367]) (by decide +kernel)
def pv137993 : PrimeValue := ⟨137993, pr137993⟩
private theorem pr137999 : Nat.Prime 137999 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv9857]) (by decide +kernel)
def pv137999 : PrimeValue := ⟨137999, pr137999⟩
private theorem pr138007 : Nat.Prime 138007 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv17,pv41]) (by decide +kernel)
def pv138007 : PrimeValue := ⟨138007, pr138007⟩
private theorem pr138041 : Nat.Prime 138041 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv17,pv29]) (by decide +kernel)
def pv138041 : PrimeValue := ⟨138041, pr138041⟩
private theorem pr138059 : Nat.Prime 138059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv69029]) (by decide +kernel)
def pv138059 : PrimeValue := ⟨138059, pr138059⟩
private theorem pr138071 : Nat.Prime 138071 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv13807]) (by decide +kernel)
def pv138071 : PrimeValue := ⟨138071, pr138071⟩
private theorem pr138079 : Nat.Prime 138079 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv2557]) (by decide +kernel)
def pv138079 : PrimeValue := ⟨138079, pr138079⟩
private theorem pr138101 : Nat.Prime 138101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1381]) (by decide +kernel)
def pv138101 : PrimeValue := ⟨138101, pr138101⟩
private theorem pr138107 : Nat.Prime 138107 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv199,pv347]) (by decide +kernel)
def pv138107 : PrimeValue := ⟨138107, pr138107⟩
private theorem pr138113 : Nat.Prime 138113 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv83]) (by decide +kernel)
def pv138113 : PrimeValue := ⟨138113, pr138113⟩
private theorem pr138139 : Nat.Prime 138139 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv7,pv11,pv13,pv23]) (by decide +kernel)
def pv138139 : PrimeValue := ⟨138139, pr138139⟩
private theorem pr138143 : Nat.Prime 138143 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv239]) (by decide +kernel)
def pv138143 : PrimeValue := ⟨138143, pr138143⟩
private theorem pr138157 : Nat.Prime 138157 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv397]) (by decide +kernel)
def pv138157 : PrimeValue := ⟨138157, pr138157⟩
private theorem pr138179 : Nat.Prime 138179 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv59,pv1171]) (by decide +kernel)
def pv138179 : PrimeValue := ⟨138179, pr138179⟩
private theorem pr138181 : Nat.Prime 138181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv47]) (by decide +kernel)
def pv138181 : PrimeValue := ⟨138181, pr138181⟩
private theorem pr138191 : Nat.Prime 138191 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv1063]) (by decide +kernel)
def pv138191 : PrimeValue := ⟨138191, pr138191⟩
private theorem pr138209 : Nat.Prime 138209 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv617]) (by decide +kernel)
def pv138209 : PrimeValue := ⟨138209, pr138209⟩
private theorem pr138239 : Nat.Prime 138239 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv69119]) (by decide +kernel)
def pv138239 : PrimeValue := ⟨138239, pr138239⟩
private theorem pr138241 : Nat.Prime 138241 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv138241 : PrimeValue := ⟨138241, pr138241⟩
private theorem pr138247 : Nat.Prime 138247 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23041]) (by decide +kernel)
def pv138247 : PrimeValue := ⟨138247, pr138247⟩
private theorem pr138251 : Nat.Prime 138251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv79]) (by decide +kernel)
def pv138251 : PrimeValue := ⟨138251, pr138251⟩
private theorem pr138283 : Nat.Prime 138283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv1213]) (by decide +kernel)
def pv138283 : PrimeValue := ⟨138283, pr138283⟩
private theorem pr138289 : Nat.Prime 138289 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv43,pv67]) (by decide +kernel)
def pv138289 : PrimeValue := ⟨138289, pr138289⟩
private theorem pr138311 : Nat.Prime 138311 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv13831]) (by decide +kernel)
def pv138311 : PrimeValue := ⟨138311, pr138311⟩
private theorem pr138319 : Nat.Prime 138319 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23053]) (by decide +kernel)
def pv138319 : PrimeValue := ⟨138319, pr138319⟩
private theorem pr138323 : Nat.Prime 138323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv31,pv97]) (by decide +kernel)
def pv138323 : PrimeValue := ⟨138323, pr138323⟩
private theorem pr138337 : Nat.Prime 138337 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv11,pv131]) (by decide +kernel)
def pv138337 : PrimeValue := ⟨138337, pr138337⟩
private theorem pr138349 : Nat.Prime 138349 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv61]) (by decide +kernel)
def pv138349 : PrimeValue := ⟨138349, pr138349⟩
private theorem pr138371 : Nat.Prime 138371 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv101,pv137]) (by decide +kernel)
def pv138371 : PrimeValue := ⟨138371, pr138371⟩
private theorem pr138373 : Nat.Prime 138373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv887]) (by decide +kernel)
def pv138373 : PrimeValue := ⟨138373, pr138373⟩
private theorem pr138389 : Nat.Prime 138389 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv1193]) (by decide +kernel)
def pv138389 : PrimeValue := ⟨138389, pr138389⟩
private theorem pr138403 : Nat.Prime 138403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv233]) (by decide +kernel)
def pv138403 : PrimeValue := ⟨138403, pr138403⟩
private theorem pr138407 : Nat.Prime 138407 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv69203]) (by decide +kernel)
def pv138407 : PrimeValue := ⟨138407, pr138407⟩
private theorem pr138427 : Nat.Prime 138427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23071]) (by decide +kernel)
def pv138427 : PrimeValue := ⟨138427, pr138427⟩
private theorem pr138433 : Nat.Prime 138433 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv103]) (by decide +kernel)
def pv138433 : PrimeValue := ⟨138433, pr138433⟩
private theorem pr138449 : Nat.Prime 138449 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv509]) (by decide +kernel)
def pv138449 : PrimeValue := ⟨138449, pr138449⟩
private theorem pr138451 : Nat.Prime 138451 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv71]) (by decide +kernel)
def pv138451 : PrimeValue := ⟨138451, pr138451⟩
private theorem pr138461 : Nat.Prime 138461 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv23,pv43]) (by decide +kernel)
def pv138461 : PrimeValue := ⟨138461, pr138461⟩
private theorem pr138469 : Nat.Prime 138469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv1049]) (by decide +kernel)
def pv138469 : PrimeValue := ⟨138469, pr138469⟩
private theorem pr138493 : Nat.Prime 138493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv3847]) (by decide +kernel)
def pv138493 : PrimeValue := ⟨138493, pr138493⟩
private theorem pr138497 : Nat.Prime 138497 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv541]) (by decide +kernel)
def pv138497 : PrimeValue := ⟨138497, pr138497⟩
private theorem pr138511 : Nat.Prime 138511 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv138511 : PrimeValue := ⟨138511, pr138511⟩
private theorem pr138517 : Nat.Prime 138517 :=
  checkPrime_prime (q := pv59) (ls := [pv2,pv3,pv7,pv17,pv97]) (by decide +kernel)
def pv138517 : PrimeValue := ⟨138517, pr138517⟩
private theorem pr138547 : Nat.Prime 138547 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv43,pv179]) (by decide +kernel)
def pv138547 : PrimeValue := ⟨138547, pr138547⟩
private theorem pr138559 : Nat.Prime 138559 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv3299]) (by decide +kernel)
def pv138559 : PrimeValue := ⟨138559, pr138559⟩
private theorem pr138563 : Nat.Prime 138563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv2389]) (by decide +kernel)
def pv138563 : PrimeValue := ⟨138563, pr138563⟩
private theorem pr138569 : Nat.Prime 138569 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17321]) (by decide +kernel)
def pv138569 : PrimeValue := ⟨138569, pr138569⟩
private theorem pr138571 : Nat.Prime 138571 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv31,pv149]) (by decide +kernel)
def pv138571 : PrimeValue := ⟨138571, pr138571⟩
private theorem pr138577 : Nat.Prime 138577 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2887]) (by decide +kernel)
def pv138577 : PrimeValue := ⟨138577, pr138577⟩
private theorem pr138581 : Nat.Prime 138581 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv41]) (by decide +kernel)
def pv138581 : PrimeValue := ⟨138581, pr138581⟩
private theorem pr138587 : Nat.Prime 138587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv19,pv521]) (by decide +kernel)
def pv138587 : PrimeValue := ⟨138587, pr138587⟩
private theorem pr138599 : Nat.Prime 138599 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv23,pv131]) (by decide +kernel)
def pv138599 : PrimeValue := ⟨138599, pr138599⟩
private theorem pr138617 : Nat.Prime 138617 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17327]) (by decide +kernel)
def pv138617 : PrimeValue := ⟨138617, pr138617⟩
private theorem pr138629 : Nat.Prime 138629 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv4951]) (by decide +kernel)
def pv138629 : PrimeValue := ⟨138629, pr138629⟩
private theorem pr138641 : Nat.Prime 138641 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv1733]) (by decide +kernel)
def pv138641 : PrimeValue := ⟨138641, pr138641⟩
private theorem pr138661 : Nat.Prime 138661 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv2311]) (by decide +kernel)
def pv138661 : PrimeValue := ⟨138661, pr138661⟩
private theorem pr138683 : Nat.Prime 138683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv69341]) (by decide +kernel)
def pv138683 : PrimeValue := ⟨138683, pr138683⟩
private theorem pr138727 : Nat.Prime 138727 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv367]) (by decide +kernel)
def pv138727 : PrimeValue := ⟨138727, pr138727⟩
private theorem pr138739 : Nat.Prime 138739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv1217]) (by decide +kernel)
def pv138739 : PrimeValue := ⟨138739, pr138739⟩
private theorem pr138763 : Nat.Prime 138763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv593]) (by decide +kernel)
def pv138763 : PrimeValue := ⟨138763, pr138763⟩
private theorem pr138793 : Nat.Prime 138793 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv5783]) (by decide +kernel)
def pv138793 : PrimeValue := ⟨138793, pr138793⟩
private theorem pr138797 : Nat.Prime 138797 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv4957]) (by decide +kernel)
def pv138797 : PrimeValue := ⟨138797, pr138797⟩
private theorem pr138799 : Nat.Prime 138799 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv11,pv701]) (by decide +kernel)
def pv138799 : PrimeValue := ⟨138799, pr138799⟩
private theorem pr138821 : Nat.Prime 138821 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv631]) (by decide +kernel)
def pv138821 : PrimeValue := ⟨138821, pr138821⟩
private theorem pr138841 : Nat.Prime 138841 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv13,pv89]) (by decide +kernel)
def pv138841 : PrimeValue := ⟨138841, pr138841⟩
private theorem pr138863 : Nat.Prime 138863 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv69431]) (by decide +kernel)
def pv138863 : PrimeValue := ⟨138863, pr138863⟩
private theorem pr138869 : Nat.Prime 138869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv149,pv233]) (by decide +kernel)
def pv138869 : PrimeValue := ⟨138869, pr138869⟩
private theorem pr138883 : Nat.Prime 138883 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv79,pv293]) (by decide +kernel)
def pv138883 : PrimeValue := ⟨138883, pr138883⟩
private theorem pr138889 : Nat.Prime 138889 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv3,pv643]) (by decide +kernel)
def pv138889 : PrimeValue := ⟨138889, pr138889⟩
private theorem pr138893 : Nat.Prime 138893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv2671]) (by decide +kernel)
def pv138893 : PrimeValue := ⟨138893, pr138893⟩
private theorem pr138899 : Nat.Prime 138899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv1877]) (by decide +kernel)
def pv138899 : PrimeValue := ⟨138899, pr138899⟩
private theorem pr138917 : Nat.Prime 138917 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv34729]) (by decide +kernel)
def pv138917 : PrimeValue := ⟨138917, pr138917⟩
private theorem pr138923 : Nat.Prime 138923 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv9923]) (by decide +kernel)
def pv138923 : PrimeValue := ⟨138923, pr138923⟩
private theorem pr138937 : Nat.Prime 138937 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv827]) (by decide +kernel)
def pv138937 : PrimeValue := ⟨138937, pr138937⟩
private theorem pr138959 : Nat.Prime 138959 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv17,pv61,pv67]) (by decide +kernel)
def pv138959 : PrimeValue := ⟨138959, pr138959⟩
private theorem pr138977 : Nat.Prime 138977 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv43,pv101]) (by decide +kernel)
def pv138977 : PrimeValue := ⟨138977, pr138977⟩
private theorem pr139021 : Nat.Prime 139021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv331]) (by decide +kernel)
def pv139021 : PrimeValue := ⟨139021, pr139021⟩
private theorem pr139033 : Nat.Prime 139033 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1931]) (by decide +kernel)
def pv139033 : PrimeValue := ⟨139033, pr139033⟩
private theorem pr139067 : Nat.Prime 139067 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv2243]) (by decide +kernel)
def pv139067 : PrimeValue := ⟨139067, pr139067⟩
private theorem pr139079 : Nat.Prime 139079 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv69539]) (by decide +kernel)
def pv139079 : PrimeValue := ⟨139079, pr139079⟩
private theorem pr139091 : Nat.Prime 139091 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv1987]) (by decide +kernel)
def pv139091 : PrimeValue := ⟨139091, pr139091⟩
private theorem pr139109 : Nat.Prime 139109 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv83,pv419]) (by decide +kernel)
def pv139109 : PrimeValue := ⟨139109, pr139109⟩
private theorem pr139121 : Nat.Prime 139121 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv37,pv47]) (by decide +kernel)
def pv139121 : PrimeValue := ⟨139121, pr139121⟩
private theorem pr139123 : Nat.Prime 139123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv59,pv131]) (by decide +kernel)
def pv139123 : PrimeValue := ⟨139123, pr139123⟩
private theorem pr139133 : Nat.Prime 139133 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv4969]) (by decide +kernel)
def pv139133 : PrimeValue := ⟨139133, pr139133⟩
private theorem pr139169 : Nat.Prime 139169 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv4349]) (by decide +kernel)
def pv139169 : PrimeValue := ⟨139169, pr139169⟩
private theorem pr139177 : Nat.Prime 139177 :=
  checkPrime_prime (q := pv43) (ls := [pv2,pv3,pv1933]) (by decide +kernel)
def pv139177 : PrimeValue := ⟨139177, pr139177⟩
private theorem pr139187 : Nat.Prime 139187 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv69593]) (by decide +kernel)
def pv139187 : PrimeValue := ⟨139187, pr139187⟩
private theorem pr139201 : Nat.Prime 139201 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv29]) (by decide +kernel)
def pv139201 : PrimeValue := ⟨139201, pr139201⟩
private theorem pr139267 : Nat.Prime 139267 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2579]) (by decide +kernel)
def pv139267 : PrimeValue := ⟨139267, pr139267⟩
private theorem pr139273 : Nat.Prime 139273 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv829]) (by decide +kernel)
def pv139273 : PrimeValue := ⟨139273, pr139273⟩
private theorem pr139291 : Nat.Prime 139291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv4643]) (by decide +kernel)
def pv139291 : PrimeValue := ⟨139291, pr139291⟩
private theorem pr139297 : Nat.Prime 139297 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv1451]) (by decide +kernel)
def pv139297 : PrimeValue := ⟨139297, pr139297⟩
private theorem pr139303 : Nat.Prime 139303 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv71,pv109]) (by decide +kernel)
def pv139303 : PrimeValue := ⟨139303, pr139303⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
