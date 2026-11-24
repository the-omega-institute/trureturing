/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table176
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table176.pv333923
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table014
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table023
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table057
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table058

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr333923 : Nat.Prime 333923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv199,pv839]) (by decide +kernel)
def pv333923 : PrimeValue := ⟨333923, pr333923⟩
private theorem pr334021 : Nat.Prime 334021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv293]) (by decide +kernel)
def pv334021 : PrimeValue := ⟨334021, pr334021⟩
private theorem pr334189 : Nat.Prime 334189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv9283]) (by decide +kernel)
def pv334189 : PrimeValue := ⟨334189, pr334189⟩
private theorem pr334379 : Nat.Prime 334379 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv15199]) (by decide +kernel)
def pv334379 : PrimeValue := ⟨334379, pr334379⟩
private theorem pr334403 : Nat.Prime 334403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv2741]) (by decide +kernel)
def pv334403 : PrimeValue := ⟨334403, pr334403⟩
private theorem pr334693 : Nat.Prime 334693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1033]) (by decide +kernel)
def pv334693 : PrimeValue := ⟨334693, pr334693⟩
private theorem pr334793 : Nat.Prime 334793 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv41849]) (by decide +kernel)
def pv334793 : PrimeValue := ⟨334793, pr334793⟩
private theorem pr335029 : Nat.Prime 335029 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv27919]) (by decide +kernel)
def pv335029 : PrimeValue := ⟨335029, pr335029⟩
private theorem pr335033 : Nat.Prime 335033 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv41879]) (by decide +kernel)
def pv335033 : PrimeValue := ⟨335033, pr335033⟩
private theorem pr335057 : Nat.Prime 335057 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv43,pv487]) (by decide +kernel)
def pv335057 : PrimeValue := ⟨335057, pr335057⟩
private theorem pr335113 : Nat.Prime 335113 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv13963]) (by decide +kernel)
def pv335113 : PrimeValue := ⟨335113, pr335113⟩
private theorem pr335123 : Nat.Prime 335123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv8819]) (by decide +kernel)
def pv335123 : PrimeValue := ⟨335123, pr335123⟩
private theorem pr335273 : Nat.Prime 335273 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv5987]) (by decide +kernel)
def pv335273 : PrimeValue := ⟨335273, pr335273⟩
private theorem pr335429 : Nat.Prime 335429 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv83857]) (by decide +kernel)
def pv335429 : PrimeValue := ⟨335429, pr335429⟩
private theorem pr335449 : Nat.Prime 335449 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv1553]) (by decide +kernel)
def pv335449 : PrimeValue := ⟨335449, pr335449⟩
private theorem pr335539 : Nat.Prime 335539 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv2663]) (by decide +kernel)
def pv335539 : PrimeValue := ⟨335539, pr335539⟩
private theorem pr335641 : Nat.Prime 335641 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv3,pv5,pv2797]) (by decide +kernel)
def pv335641 : PrimeValue := ⟨335641, pr335641⟩
private theorem pr335663 : Nat.Prime 335663 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv23,pv7297]) (by decide +kernel)
def pv335663 : PrimeValue := ⟨335663, pr335663⟩
private theorem pr335681 : Nat.Prime 335681 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv1049]) (by decide +kernel)
def pv335681 : PrimeValue := ⟨335681, pr335681⟩
private theorem pr335771 : Nat.Prime 335771 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv5,pv33577]) (by decide +kernel)
def pv335771 : PrimeValue := ⟨335771, pr335771⟩
private theorem pr335809 : Nat.Prime 335809 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv53]) (by decide +kernel)
def pv335809 : PrimeValue := ⟨335809, pr335809⟩
private theorem pr335813 : Nat.Prime 335813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv2269]) (by decide +kernel)
def pv335813 : PrimeValue := ⟨335813, pr335813⟩
private theorem pr335843 : Nat.Prime 335843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv12917]) (by decide +kernel)
def pv335843 : PrimeValue := ⟨335843, pr335843⟩
private theorem pr336079 : Nat.Prime 336079 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv18671]) (by decide +kernel)
def pv336079 : PrimeValue := ⟨336079, pr336079⟩
private theorem pr336163 : Nat.Prime 336163 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv179,pv313]) (by decide +kernel)
def pv336163 : PrimeValue := ⟨336163, pr336163⟩
private theorem pr336239 : Nat.Prime 336239 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv47,pv73]) (by decide +kernel)
def pv336239 : PrimeValue := ⟨336239, pr336239⟩
private theorem pr336251 : Nat.Prime 336251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv269]) (by decide +kernel)
def pv336251 : PrimeValue := ⟨336251, pr336251⟩
private theorem pr336527 : Nat.Prime 336527 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv168263]) (by decide +kernel)
def pv336527 : PrimeValue := ⟨336527, pr336527⟩
private theorem pr336551 : Nat.Prime 336551 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv53,pv127]) (by decide +kernel)
def pv336551 : PrimeValue := ⟨336551, pr336551⟩
private theorem pr336593 : Nat.Prime 336593 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv109,pv193]) (by decide +kernel)
def pv336593 : PrimeValue := ⟨336593, pr336593⟩
private theorem pr336683 : Nat.Prime 336683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv71,pv2371]) (by decide +kernel)
def pv336683 : PrimeValue := ⟨336683, pr336683⟩
private theorem pr336773 : Nat.Prime 336773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv59,pv1427]) (by decide +kernel)
def pv336773 : PrimeValue := ⟨336773, pr336773⟩
private theorem pr336793 : Nat.Prime 336793 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv14033]) (by decide +kernel)
def pv336793 : PrimeValue := ⟨336793, pr336793⟩
private theorem pr336799 : Nat.Prime 336799 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv11]) (by decide +kernel)
def pv336799 : PrimeValue := ⟨336799, pr336799⟩
private theorem pr336829 : Nat.Prime 336829 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv28069]) (by decide +kernel)
def pv336829 : PrimeValue := ⟨336829, pr336829⟩
private theorem pr336899 : Nat.Prime 336899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv168449]) (by decide +kernel)
def pv336899 : PrimeValue := ⟨336899, pr336899⟩
private theorem pr336911 : Nat.Prime 336911 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv4813]) (by decide +kernel)
def pv336911 : PrimeValue := ⟨336911, pr336911⟩
private theorem pr337013 : Nat.Prime 337013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv6481]) (by decide +kernel)
def pv337013 : PrimeValue := ⟨337013, pr337013⟩
private theorem pr337153 : Nat.Prime 337153 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv439]) (by decide +kernel)
def pv337153 : PrimeValue := ⟨337153, pr337153⟩
private theorem pr337279 : Nat.Prime 337279 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv67,pv839]) (by decide +kernel)
def pv337279 : PrimeValue := ⟨337279, pr337279⟩
private theorem pr337283 : Nat.Prime 337283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv15331]) (by decide +kernel)
def pv337283 : PrimeValue := ⟨337283, pr337283⟩
private theorem pr337367 : Nat.Prime 337367 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv37,pv47,pv97]) (by decide +kernel)
def pv337367 : PrimeValue := ⟨337367, pr337367⟩
private theorem pr337511 : Nat.Prime 337511 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv33751]) (by decide +kernel)
def pv337511 : PrimeValue := ⟨337511, pr337511⟩
private theorem pr337583 : Nat.Prime 337583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv24113]) (by decide +kernel)
def pv337583 : PrimeValue := ⟨337583, pr337583⟩
private theorem pr337609 : Nat.Prime 337609 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv521]) (by decide +kernel)
def pv337609 : PrimeValue := ⟨337609, pr337609⟩
private theorem pr337651 : Nat.Prime 337651 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv2251]) (by decide +kernel)
def pv337651 : PrimeValue := ⟨337651, pr337651⟩
private theorem pr337781 : Nat.Prime 337781 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv16889]) (by decide +kernel)
def pv337781 : PrimeValue := ⟨337781, pr337781⟩
private theorem pr337853 : Nat.Prime 337853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv84463]) (by decide +kernel)
def pv337853 : PrimeValue := ⟨337853, pr337853⟩
private theorem pr337859 : Nat.Prime 337859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv19,pv523]) (by decide +kernel)
def pv337859 : PrimeValue := ⟨337859, pr337859⟩
private theorem pr337903 : Nat.Prime 337903 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv199,pv283]) (by decide +kernel)
def pv337903 : PrimeValue := ⟨337903, pr337903⟩
private theorem pr337907 : Nat.Prime 337907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv107,pv1579]) (by decide +kernel)
def pv337907 : PrimeValue := ⟨337907, pr337907⟩
private theorem pr338159 : Nat.Prime 338159 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv169079]) (by decide +kernel)
def pv338159 : PrimeValue := ⟨338159, pr338159⟩
private theorem pr338183 : Nat.Prime 338183 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv13007]) (by decide +kernel)
def pv338183 : PrimeValue := ⟨338183, pr338183⟩
private theorem pr338237 : Nat.Prime 338237 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv84559]) (by decide +kernel)
def pv338237 : PrimeValue := ⟨338237, pr338237⟩
private theorem pr338269 : Nat.Prime 338269 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv4027]) (by decide +kernel)
def pv338269 : PrimeValue := ⟨338269, pr338269⟩
private theorem pr338423 : Nat.Prime 338423 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv23,pv1051]) (by decide +kernel)
def pv338423 : PrimeValue := ⟨338423, pr338423⟩
private theorem pr338609 : Nat.Prime 338609 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv21163]) (by decide +kernel)
def pv338609 : PrimeValue := ⟨338609, pr338609⟩
private theorem pr338683 : Nat.Prime 338683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv47,pv1201]) (by decide +kernel)
def pv338683 : PrimeValue := ⟨338683, pr338683⟩
private theorem pr338993 : Nat.Prime 338993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv21187]) (by decide +kernel)
def pv338993 : PrimeValue := ⟨338993, pr338993⟩
private theorem pr338999 : Nat.Prime 338999 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv11,pv19,pv811]) (by decide +kernel)
def pv338999 : PrimeValue := ⟨338999, pr338999⟩
private theorem pr339263 : Nat.Prime 339263 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv11,pv2203]) (by decide +kernel)
def pv339263 : PrimeValue := ⟨339263, pr339263⟩
private theorem pr339373 : Nat.Prime 339373 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv11,pv857]) (by decide +kernel)
def pv339373 : PrimeValue := ⟨339373, pr339373⟩
private theorem pr339433 : Nat.Prime 339433 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv14143]) (by decide +kernel)
def pv339433 : PrimeValue := ⟨339433, pr339433⟩
private theorem pr339601 : Nat.Prime 339601 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv283]) (by decide +kernel)
def pv339601 : PrimeValue := ⟨339601, pr339601⟩
private theorem pr339653 : Nat.Prime 339653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv84913]) (by decide +kernel)
def pv339653 : PrimeValue := ⟨339653, pr339653⟩
private theorem pr339707 : Nat.Prime 339707 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv5857]) (by decide +kernel)
def pv339707 : PrimeValue := ⟨339707, pr339707⟩
private theorem pr340007 : Nat.Prime 340007 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv170003]) (by decide +kernel)
def pv340007 : PrimeValue := ⟨340007, pr340007⟩
private theorem pr340049 : Nat.Prime 340049 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv53,pv401]) (by decide +kernel)
def pv340049 : PrimeValue := ⟨340049, pr340049⟩
private theorem pr340121 : Nat.Prime 340121 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv773]) (by decide +kernel)
def pv340121 : PrimeValue := ⟨340121, pr340121⟩
private theorem pr340169 : Nat.Prime 340169 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv101,pv421]) (by decide +kernel)
def pv340169 : PrimeValue := ⟨340169, pr340169⟩
private theorem pr340201 : Nat.Prime 340201 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv340201 : PrimeValue := ⟨340201, pr340201⟩
private theorem pr340321 : Nat.Prime 340321 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv709]) (by decide +kernel)
def pv340321 : PrimeValue := ⟨340321, pr340321⟩
private theorem pr340409 : Nat.Prime 340409 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv2503]) (by decide +kernel)
def pv340409 : PrimeValue := ⟨340409, pr340409⟩
private theorem pr340451 : Nat.Prime 340451 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv619]) (by decide +kernel)
def pv340451 : PrimeValue := ⟨340451, pr340451⟩
private theorem pr340591 : Nat.Prime 340591 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv11353]) (by decide +kernel)
def pv340591 : PrimeValue := ⟨340591, pr340591⟩
private theorem pr340633 : Nat.Prime 340633 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv83]) (by decide +kernel)
def pv340633 : PrimeValue := ⟨340633, pr340633⟩
private theorem pr340693 : Nat.Prime 340693 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv29,pv89]) (by decide +kernel)
def pv340693 : PrimeValue := ⟨340693, pr340693⟩
private theorem pr340979 : Nat.Prime 340979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv1409]) (by decide +kernel)
def pv340979 : PrimeValue := ⟨340979, pr340979⟩
private theorem pr341027 : Nat.Prime 341027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv24359]) (by decide +kernel)
def pv341027 : PrimeValue := ⟨341027, pr341027⟩
private theorem pr341059 : Nat.Prime 341059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv56843]) (by decide +kernel)
def pv341059 : PrimeValue := ⟨341059, pr341059⟩
private theorem pr341063 : Nat.Prime 341063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv31,pv5501]) (by decide +kernel)
def pv341063 : PrimeValue := ⟨341063, pr341063⟩
private theorem pr341083 : Nat.Prime 341083 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv2707]) (by decide +kernel)
def pv341083 : PrimeValue := ⟨341083, pr341083⟩
private theorem pr341087 : Nat.Prime 341087 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv199,pv857]) (by decide +kernel)
def pv341087 : PrimeValue := ⟨341087, pr341087⟩
private theorem pr341269 : Nat.Prime 341269 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv28439]) (by decide +kernel)
def pv341269 : PrimeValue := ⟨341269, pr341269⟩
private theorem pr341333 : Nat.Prime 341333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv85333]) (by decide +kernel)
def pv341333 : PrimeValue := ⟨341333, pr341333⟩
private theorem pr341423 : Nat.Prime 341423 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv170711]) (by decide +kernel)
def pv341423 : PrimeValue := ⟨341423, pr341423⟩
private theorem pr341459 : Nat.Prime 341459 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv23,pv571]) (by decide +kernel)
def pv341459 : PrimeValue := ⟨341459, pr341459⟩
private theorem pr341597 : Nat.Prime 341597 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv47,pv79]) (by decide +kernel)
def pv341597 : PrimeValue := ⟨341597, pr341597⟩
private theorem pr341603 : Nat.Prime 341603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv170801]) (by decide +kernel)
def pv341603 : PrimeValue := ⟨341603, pr341603⟩
private theorem pr341701 : Nat.Prime 341701 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv17,pv67]) (by decide +kernel)
def pv341701 : PrimeValue := ⟨341701, pr341701⟩
private theorem pr341729 : Nat.Prime 341729 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv59,pv181]) (by decide +kernel)
def pv341729 : PrimeValue := ⟨341729, pr341729⟩
private theorem pr341813 : Nat.Prime 341813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv85453]) (by decide +kernel)
def pv341813 : PrimeValue := ⟨341813, pr341813⟩
private theorem pr341839 : Nat.Prime 341839 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv2713]) (by decide +kernel)
def pv341839 : PrimeValue := ⟨341839, pr341839⟩
private theorem pr341963 : Nat.Prime 341963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv8999]) (by decide +kernel)
def pv341963 : PrimeValue := ⟨341963, pr341963⟩
private theorem pr341983 : Nat.Prime 341983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2111]) (by decide +kernel)
def pv341983 : PrimeValue := ⟨341983, pr341983⟩
private theorem pr341993 : Nat.Prime 341993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv31,pv197]) (by decide +kernel)
def pv341993 : PrimeValue := ⟨341993, pr341993⟩
private theorem pr342061 : Nat.Prime 342061 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv5701]) (by decide +kernel)
def pv342061 : PrimeValue := ⟨342061, pr342061⟩
private theorem pr342071 : Nat.Prime 342071 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv79,pv433]) (by decide +kernel)
def pv342071 : PrimeValue := ⟨342071, pr342071⟩
private theorem pr342131 : Nat.Prime 342131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv34213]) (by decide +kernel)
def pv342131 : PrimeValue := ⟨342131, pr342131⟩
private theorem pr342191 : Nat.Prime 342191 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv19,pv1801]) (by decide +kernel)
def pv342191 : PrimeValue := ⟨342191, pr342191⟩
private theorem pr342281 : Nat.Prime 342281 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv43,pv199]) (by decide +kernel)
def pv342281 : PrimeValue := ⟨342281, pr342281⟩
private theorem pr342359 : Nat.Prime 342359 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv171179]) (by decide +kernel)
def pv342359 : PrimeValue := ⟨342359, pr342359⟩
private theorem pr342371 : Nat.Prime 342371 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv67,pv73]) (by decide +kernel)
def pv342371 : PrimeValue := ⟨342371, pr342371⟩
private theorem pr342373 : Nat.Prime 342373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv103,pv277]) (by decide +kernel)
def pv342373 : PrimeValue := ⟨342373, pr342373⟩
private theorem pr342389 : Nat.Prime 342389 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv85597]) (by decide +kernel)
def pv342389 : PrimeValue := ⟨342389, pr342389⟩
private theorem pr342449 : Nat.Prime 342449 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv1259]) (by decide +kernel)
def pv342449 : PrimeValue := ⟨342449, pr342449⟩
private theorem pr342469 : Nat.Prime 342469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv151]) (by decide +kernel)
def pv342469 : PrimeValue := ⟨342469, pr342469⟩
private theorem pr342553 : Nat.Prime 342553 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv2039]) (by decide +kernel)
def pv342553 : PrimeValue := ⟨342553, pr342553⟩
private theorem pr342647 : Nat.Prime 342647 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv71,pv127]) (by decide +kernel)
def pv342647 : PrimeValue := ⟨342647, pr342647⟩
private theorem pr342653 : Nat.Prime 342653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv5039]) (by decide +kernel)
def pv342653 : PrimeValue := ⟨342653, pr342653⟩
private theorem pr342679 : Nat.Prime 342679 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv41,pv199]) (by decide +kernel)
def pv342679 : PrimeValue := ⟨342679, pr342679⟩
private theorem pr342799 : Nat.Prime 342799 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv31,pv97]) (by decide +kernel)
def pv342799 : PrimeValue := ⟨342799, pr342799⟩
private theorem pr342803 : Nat.Prime 342803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv171401]) (by decide +kernel)
def pv342803 : PrimeValue := ⟨342803, pr342803⟩
private theorem pr342833 : Nat.Prime 342833 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv3061]) (by decide +kernel)
def pv342833 : PrimeValue := ⟨342833, pr342833⟩
private theorem pr342989 : Nat.Prime 342989 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv4513]) (by decide +kernel)
def pv342989 : PrimeValue := ⟨342989, pr342989⟩
private theorem pr343163 : Nat.Prime 343163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv10093]) (by decide +kernel)
def pv343163 : PrimeValue := ⟨343163, pr343163⟩
private theorem pr343193 : Nat.Prime 343193 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv42899]) (by decide +kernel)
def pv343193 : PrimeValue := ⟨343193, pr343193⟩
private theorem pr343261 : Nat.Prime 343261 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1907]) (by decide +kernel)
def pv343261 : PrimeValue := ⟨343261, pr343261⟩
private theorem pr343337 : Nat.Prime 343337 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv6131]) (by decide +kernel)
def pv343337 : PrimeValue := ⟨343337, pr343337⟩
private theorem pr343559 : Nat.Prime 343559 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv19,pv9041]) (by decide +kernel)
def pv343559 : PrimeValue := ⟨343559, pr343559⟩
private theorem pr343583 : Nat.Prime 343583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv37,pv4643]) (by decide +kernel)
def pv343583 : PrimeValue := ⟨343583, pr343583⟩
private theorem pr343709 : Nat.Prime 343709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv2963]) (by decide +kernel)
def pv343709 : PrimeValue := ⟨343709, pr343709⟩
private theorem pr343727 : Nat.Prime 343727 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv171863]) (by decide +kernel)
def pv343727 : PrimeValue := ⟨343727, pr343727⟩
private theorem pr343769 : Nat.Prime 343769 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv97,pv443]) (by decide +kernel)
def pv343769 : PrimeValue := ⟨343769, pr343769⟩
private theorem pr343829 : Nat.Prime 343829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv1999]) (by decide +kernel)
def pv343829 : PrimeValue := ⟨343829, pr343829⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
