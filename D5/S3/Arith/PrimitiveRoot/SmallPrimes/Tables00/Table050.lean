/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table050
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table050.pv139313
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table006
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table010
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table027
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table028

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr139313 : PrimeCertificate 139313 :=
  certifyPrime (q := pv3) (ls := [pv2,pv8707]) (by decide +kernel)
def pv139313 : PrimeValue := ⟨139313, pr139313⟩
private theorem pr139333 : PrimeCertificate 139333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv683]) (by decide +kernel)
def pv139333 : PrimeValue := ⟨139333, pr139333⟩
private theorem pr139339 : PrimeCertificate 139339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7741]) (by decide +kernel)
def pv139339 : PrimeValue := ⟨139339, pr139339⟩
private theorem pr139343 : PrimeCertificate 139343 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv37,pv269]) (by decide +kernel)
def pv139343 : PrimeValue := ⟨139343, pr139343⟩
private theorem pr139367 : PrimeCertificate 139367 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv4099]) (by decide +kernel)
def pv139367 : PrimeValue := ⟨139367, pr139367⟩
private theorem pr139387 : PrimeCertificate 139387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv1787]) (by decide +kernel)
def pv139387 : PrimeValue := ⟨139387, pr139387⟩
private theorem pr139393 : PrimeCertificate 139393 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv139393 : PrimeValue := ⟨139393, pr139393⟩
private theorem pr139397 : PrimeCertificate 139397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv34849]) (by decide +kernel)
def pv139397 : PrimeValue := ⟨139397, pr139397⟩
private theorem pr139409 : PrimeCertificate 139409 :=
  certifyPrime (q := pv3) (ls := [pv2,pv8713]) (by decide +kernel)
def pv139409 : PrimeValue := ⟨139409, pr139409⟩
private theorem pr139423 : PrimeCertificate 139423 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv1223]) (by decide +kernel)
def pv139423 : PrimeValue := ⟨139423, pr139423⟩
private theorem pr139429 : PrimeCertificate 139429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1291]) (by decide +kernel)
def pv139429 : PrimeValue := ⟨139429, pr139429⟩
private theorem pr139439 : PrimeCertificate 139439 :=
  certifyPrime (q := pv11) (ls := [pv2,pv13,pv31,pv173]) (by decide +kernel)
def pv139439 : PrimeValue := ⟨139439, pr139439⟩
private theorem pr139457 : PrimeCertificate 139457 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2179]) (by decide +kernel)
def pv139457 : PrimeValue := ⟨139457, pr139457⟩
private theorem pr139459 : PrimeCertificate 139459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv2113]) (by decide +kernel)
def pv139459 : PrimeValue := ⟨139459, pr139459⟩
private theorem pr139483 : PrimeCertificate 139483 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv41]) (by decide +kernel)
def pv139483 : PrimeValue := ⟨139483, pr139483⟩
private theorem pr139487 : PrimeCertificate 139487 :=
  certifyPrime (q := pv5) (ls := [pv2,pv97,pv719]) (by decide +kernel)
def pv139487 : PrimeValue := ⟨139487, pr139487⟩
private theorem pr139493 : PrimeCertificate 139493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv811]) (by decide +kernel)
def pv139493 : PrimeValue := ⟨139493, pr139493⟩
private theorem pr139501 : PrimeCertificate 139501 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv31]) (by decide +kernel)
def pv139501 : PrimeValue := ⟨139501, pr139501⟩
private theorem pr139511 : PrimeCertificate 139511 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv1993]) (by decide +kernel)
def pv139511 : PrimeValue := ⟨139511, pr139511⟩
private theorem pr139537 : PrimeCertificate 139537 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv19]) (by decide +kernel)
def pv139537 : PrimeValue := ⟨139537, pr139537⟩
private theorem pr139547 : PrimeCertificate 139547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv6343]) (by decide +kernel)
def pv139547 : PrimeValue := ⟨139547, pr139547⟩
private theorem pr139571 : PrimeCertificate 139571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv821]) (by decide +kernel)
def pv139571 : PrimeValue := ⟨139571, pr139571⟩
private theorem pr139589 : PrimeCertificate 139589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv34897]) (by decide +kernel)
def pv139589 : PrimeValue := ⟨139589, pr139589⟩
private theorem pr139591 : PrimeCertificate 139591 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv47]) (by decide +kernel)
def pv139591 : PrimeValue := ⟨139591, pr139591⟩
private theorem pr139597 : PrimeCertificate 139597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11633]) (by decide +kernel)
def pv139597 : PrimeValue := ⟨139597, pr139597⟩
private theorem pr139619 : PrimeCertificate 139619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv69809]) (by decide +kernel)
def pv139619 : PrimeValue := ⟨139619, pr139619⟩
private theorem pr139627 : PrimeCertificate 139627 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7757]) (by decide +kernel)
def pv139627 : PrimeValue := ⟨139627, pr139627⟩
private theorem pr139661 : PrimeCertificate 139661 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv6983]) (by decide +kernel)
def pv139661 : PrimeValue := ⟨139661, pr139661⟩
private theorem pr139663 : PrimeCertificate 139663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7759]) (by decide +kernel)
def pv139663 : PrimeValue := ⟨139663, pr139663⟩
private theorem pr139681 : PrimeCertificate 139681 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv97]) (by decide +kernel)
def pv139681 : PrimeValue := ⟨139681, pr139681⟩
private theorem pr139697 : PrimeCertificate 139697 :=
  certifyPrime (q := pv3) (ls := [pv2,pv8731]) (by decide +kernel)
def pv139697 : PrimeValue := ⟨139697, pr139697⟩
private theorem pr139703 : PrimeCertificate 139703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv3037]) (by decide +kernel)
def pv139703 : PrimeValue := ⟨139703, pr139703⟩
private theorem pr139709 : PrimeCertificate 139709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv659]) (by decide +kernel)
def pv139709 : PrimeValue := ⟨139709, pr139709⟩
private theorem pr139721 : PrimeCertificate 139721 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv7,pv499]) (by decide +kernel)
def pv139721 : PrimeValue := ⟨139721, pr139721⟩
private theorem pr139729 : PrimeCertificate 139729 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv41,pv71]) (by decide +kernel)
def pv139729 : PrimeValue := ⟨139729, pr139729⟩
private theorem pr139739 : PrimeCertificate 139739 :=
  certifyPrime (q := pv13) (ls := [pv2,pv109,pv641]) (by decide +kernel)
def pv139739 : PrimeValue := ⟨139739, pr139739⟩
private theorem pr139747 : PrimeCertificate 139747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23291]) (by decide +kernel)
def pv139747 : PrimeValue := ⟨139747, pr139747⟩
private theorem pr139753 : PrimeCertificate 139753 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv647]) (by decide +kernel)
def pv139753 : PrimeValue := ⟨139753, pr139753⟩
private theorem pr139759 : PrimeCertificate 139759 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23293]) (by decide +kernel)
def pv139759 : PrimeValue := ⟨139759, pr139759⟩
private theorem pr139801 : PrimeCertificate 139801 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv233]) (by decide +kernel)
def pv139801 : PrimeValue := ⟨139801, pr139801⟩
private theorem pr139813 : PrimeCertificate 139813 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv61,pv191]) (by decide +kernel)
def pv139813 : PrimeValue := ⟨139813, pr139813⟩
private theorem pr139837 : PrimeCertificate 139837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv271]) (by decide +kernel)
def pv139837 : PrimeValue := ⟨139837, pr139837⟩
private theorem pr139861 : PrimeCertificate 139861 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv37]) (by decide +kernel)
def pv139861 : PrimeValue := ⟨139861, pr139861⟩
private theorem pr139871 : PrimeCertificate 139871 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv71,pv197]) (by decide +kernel)
def pv139871 : PrimeValue := ⟨139871, pr139871⟩
private theorem pr139883 : PrimeCertificate 139883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv69941]) (by decide +kernel)
def pv139883 : PrimeValue := ⟨139883, pr139883⟩
private theorem pr139891 : PrimeCertificate 139891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv4663]) (by decide +kernel)
def pv139891 : PrimeValue := ⟨139891, pr139891⟩
private theorem pr139907 : PrimeCertificate 139907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv5381]) (by decide +kernel)
def pv139907 : PrimeValue := ⟨139907, pr139907⟩
private theorem pr139939 : PrimeCertificate 139939 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv83,pv281]) (by decide +kernel)
def pv139939 : PrimeValue := ⟨139939, pr139939⟩
private theorem pr139967 : PrimeCertificate 139967 :=
  certifyPrime (q := pv5) (ls := [pv2,pv47,pv1489]) (by decide +kernel)
def pv139967 : PrimeValue := ⟨139967, pr139967⟩
private theorem pr139969 : PrimeCertificate 139969 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3]) (by decide +kernel)
def pv139969 : PrimeValue := ⟨139969, pr139969⟩
private theorem pr139981 : PrimeCertificate 139981 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv2333]) (by decide +kernel)
def pv139981 : PrimeValue := ⟨139981, pr139981⟩
private theorem pr139987 : PrimeCertificate 139987 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv101]) (by decide +kernel)
def pv139987 : PrimeValue := ⟨139987, pr139987⟩
private theorem pr140009 : PrimeCertificate 140009 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv37,pv43]) (by decide +kernel)
def pv140009 : PrimeValue := ⟨140009, pr140009⟩
private theorem pr140053 : PrimeCertificate 140053 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv1061]) (by decide +kernel)
def pv140053 : PrimeValue := ⟨140053, pr140053⟩
private theorem pr140057 : PrimeCertificate 140057 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv41,pv61]) (by decide +kernel)
def pv140057 : PrimeValue := ⟨140057, pr140057⟩
private theorem pr140069 : PrimeCertificate 140069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv97]) (by decide +kernel)
def pv140069 : PrimeValue := ⟨140069, pr140069⟩
private theorem pr140111 : PrimeCertificate 140111 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv14011]) (by decide +kernel)
def pv140111 : PrimeValue := ⟨140111, pr140111⟩
private theorem pr140143 : PrimeCertificate 140143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23357]) (by decide +kernel)
def pv140143 : PrimeValue := ⟨140143, pr140143⟩
private theorem pr140167 : PrimeCertificate 140167 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv599]) (by decide +kernel)
def pv140167 : PrimeValue := ⟨140167, pr140167⟩
private theorem pr140171 : PrimeCertificate 140171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv107,pv131]) (by decide +kernel)
def pv140171 : PrimeValue := ⟨140171, pr140171⟩
private theorem pr140177 : PrimeCertificate 140177 :=
  certifyPrime (q := pv3) (ls := [pv2,pv8761]) (by decide +kernel)
def pv140177 : PrimeValue := ⟨140177, pr140177⟩
private theorem pr140191 : PrimeCertificate 140191 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv4673]) (by decide +kernel)
def pv140191 : PrimeValue := ⟨140191, pr140191⟩
private theorem pr140197 : PrimeCertificate 140197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1669]) (by decide +kernel)
def pv140197 : PrimeValue := ⟨140197, pr140197⟩
private theorem pr140207 : PrimeCertificate 140207 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv6373]) (by decide +kernel)
def pv140207 : PrimeValue := ⟨140207, pr140207⟩
private theorem pr140221 : PrimeCertificate 140221 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv19,pv41]) (by decide +kernel)
def pv140221 : PrimeValue := ⟨140221, pr140221⟩
private theorem pr140227 : PrimeCertificate 140227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23371]) (by decide +kernel)
def pv140227 : PrimeValue := ⟨140227, pr140227⟩
private theorem pr140237 : PrimeCertificate 140237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv35059]) (by decide +kernel)
def pv140237 : PrimeValue := ⟨140237, pr140237⟩
private theorem pr140249 : PrimeCertificate 140249 :=
  certifyPrime (q := pv3) (ls := [pv2,pv47,pv373]) (by decide +kernel)
def pv140249 : PrimeValue := ⟨140249, pr140249⟩
private theorem pr140263 : PrimeCertificate 140263 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv97,pv241]) (by decide +kernel)
def pv140263 : PrimeValue := ⟨140263, pr140263⟩
private theorem pr140281 : PrimeCertificate 140281 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv7,pv167]) (by decide +kernel)
def pv140281 : PrimeValue := ⟨140281, pr140281⟩
private theorem pr140297 : PrimeCertificate 140297 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv19,pv71]) (by decide +kernel)
def pv140297 : PrimeValue := ⟨140297, pr140297⟩
private theorem pr140321 : PrimeCertificate 140321 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv877]) (by decide +kernel)
def pv140321 : PrimeValue := ⟨140321, pr140321⟩
private theorem pr140339 : PrimeCertificate 140339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv6379]) (by decide +kernel)
def pv140339 : PrimeValue := ⟨140339, pr140339⟩
private theorem pr140351 : PrimeCertificate 140351 :=
  certifyPrime (q := pv31) (ls := [pv2,pv5,pv7,pv401]) (by decide +kernel)
def pv140351 : PrimeValue := ⟨140351, pr140351⟩
private theorem pr140401 : PrimeCertificate 140401 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv140401 : PrimeValue := ⟨140401, pr140401⟩
private theorem pr140407 : PrimeCertificate 140407 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv3343]) (by decide +kernel)
def pv140407 : PrimeValue := ⟨140407, pr140407⟩
private theorem pr140417 : PrimeCertificate 140417 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1097]) (by decide +kernel)
def pv140417 : PrimeValue := ⟨140417, pr140417⟩
private theorem pr140419 : PrimeCertificate 140419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv269]) (by decide +kernel)
def pv140419 : PrimeValue := ⟨140419, pr140419⟩
private theorem pr140423 : PrimeCertificate 140423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv61,pv1151]) (by decide +kernel)
def pv140423 : PrimeValue := ⟨140423, pr140423⟩
private theorem pr140443 : PrimeCertificate 140443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv89,pv263]) (by decide +kernel)
def pv140443 : PrimeValue := ⟨140443, pr140443⟩
private theorem pr140449 : PrimeCertificate 140449 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv11,pv19]) (by decide +kernel)
def pv140449 : PrimeValue := ⟨140449, pr140449⟩
private theorem pr140453 : PrimeCertificate 140453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv37,pv73]) (by decide +kernel)
def pv140453 : PrimeValue := ⟨140453, pr140453⟩
private theorem pr140473 : PrimeCertificate 140473 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv1951]) (by decide +kernel)
def pv140473 : PrimeValue := ⟨140473, pr140473⟩
private theorem pr140477 : PrimeCertificate 140477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv29,pv173]) (by decide +kernel)
def pv140477 : PrimeValue := ⟨140477, pr140477⟩
private theorem pr140521 : PrimeCertificate 140521 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv1171]) (by decide +kernel)
def pv140521 : PrimeValue := ⟨140521, pr140521⟩
private theorem pr140533 : PrimeCertificate 140533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv239]) (by decide +kernel)
def pv140533 : PrimeValue := ⟨140533, pr140533⟩
private theorem pr140549 : PrimeCertificate 140549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv857]) (by decide +kernel)
def pv140549 : PrimeValue := ⟨140549, pr140549⟩
private theorem pr140551 : PrimeCertificate 140551 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv937]) (by decide +kernel)
def pv140551 : PrimeValue := ⟨140551, pr140551⟩
private theorem pr140587 : PrimeCertificate 140587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23431]) (by decide +kernel)
def pv140587 : PrimeValue := ⟨140587, pr140587⟩
private theorem pr140593 : PrimeCertificate 140593 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv29,pv101]) (by decide +kernel)
def pv140593 : PrimeValue := ⟨140593, pr140593⟩
private theorem pr140603 : PrimeCertificate 140603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv83]) (by decide +kernel)
def pv140603 : PrimeValue := ⟨140603, pr140603⟩
private theorem pr140611 : PrimeCertificate 140611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv43,pv109]) (by decide +kernel)
def pv140611 : PrimeValue := ⟨140611, pr140611⟩
private theorem pr140617 : PrimeCertificate 140617 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv7,pv31]) (by decide +kernel)
def pv140617 : PrimeValue := ⟨140617, pr140617⟩
private theorem pr140627 : PrimeCertificate 140627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv70313]) (by decide +kernel)
def pv140627 : PrimeValue := ⟨140627, pr140627⟩
private theorem pr140629 : PrimeCertificate 140629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11719]) (by decide +kernel)
def pv140629 : PrimeValue := ⟨140629, pr140629⟩
private theorem pr140639 : PrimeCertificate 140639 :=
  certifyPrime (q := pv7) (ls := [pv2,pv19,pv3701]) (by decide +kernel)
def pv140639 : PrimeValue := ⟨140639, pr140639⟩
private theorem pr140659 : PrimeCertificate 140659 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv17,pv197]) (by decide +kernel)
def pv140659 : PrimeValue := ⟨140659, pr140659⟩
private theorem pr140663 : PrimeCertificate 140663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv53,pv1327]) (by decide +kernel)
def pv140663 : PrimeValue := ⟨140663, pr140663⟩
private theorem pr140677 : PrimeCertificate 140677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv617]) (by decide +kernel)
def pv140677 : PrimeValue := ⟨140677, pr140677⟩
private theorem pr140681 : PrimeCertificate 140681 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv3517]) (by decide +kernel)
def pv140681 : PrimeValue := ⟨140681, pr140681⟩
private theorem pr140683 : PrimeCertificate 140683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23447]) (by decide +kernel)
def pv140683 : PrimeValue := ⟨140683, pr140683⟩
private theorem pr140689 : PrimeCertificate 140689 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv977]) (by decide +kernel)
def pv140689 : PrimeValue := ⟨140689, pr140689⟩
private theorem pr140717 : PrimeCertificate 140717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv127,pv277]) (by decide +kernel)
def pv140717 : PrimeValue := ⟨140717, pr140717⟩
private theorem pr140729 : PrimeCertificate 140729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv359]) (by decide +kernel)
def pv140729 : PrimeValue := ⟨140729, pr140729⟩
private theorem pr140731 : PrimeCertificate 140731 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv4691]) (by decide +kernel)
def pv140731 : PrimeValue := ⟨140731, pr140731⟩
private theorem pr140741 : PrimeCertificate 140741 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31,pv227]) (by decide +kernel)
def pv140741 : PrimeValue := ⟨140741, pr140741⟩
private theorem pr140759 : PrimeCertificate 140759 :=
  certifyPrime (q := pv11) (ls := [pv2,pv70379]) (by decide +kernel)
def pv140759 : PrimeValue := ⟨140759, pr140759⟩
private theorem pr140761 : PrimeCertificate 140761 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv17,pv23]) (by decide +kernel)
def pv140761 : PrimeValue := ⟨140761, pr140761⟩
private theorem pr140773 : PrimeCertificate 140773 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11731]) (by decide +kernel)
def pv140773 : PrimeValue := ⟨140773, pr140773⟩
private theorem pr140779 : PrimeCertificate 140779 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv79]) (by decide +kernel)
def pv140779 : PrimeValue := ⟨140779, pr140779⟩
private theorem pr140797 : PrimeCertificate 140797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3911]) (by decide +kernel)
def pv140797 : PrimeValue := ⟨140797, pr140797⟩
private theorem pr140813 : PrimeCertificate 140813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv47,pv107]) (by decide +kernel)
def pv140813 : PrimeValue := ⟨140813, pr140813⟩
private theorem pr140831 : PrimeCertificate 140831 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv14083]) (by decide +kernel)
def pv140831 : PrimeValue := ⟨140831, pr140831⟩
private theorem pr140837 : PrimeCertificate 140837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv137,pv257]) (by decide +kernel)
def pv140837 : PrimeValue := ⟨140837, pr140837⟩
private theorem pr140839 : PrimeCertificate 140839 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv23473]) (by decide +kernel)
def pv140839 : PrimeValue := ⟨140839, pr140839⟩
private theorem pr140863 : PrimeCertificate 140863 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv1381]) (by decide +kernel)
def pv140863 : PrimeValue := ⟨140863, pr140863⟩
private theorem pr140867 : PrimeCertificate 140867 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv19,pv337]) (by decide +kernel)
def pv140867 : PrimeValue := ⟨140867, pr140867⟩
private theorem pr140869 : PrimeCertificate 140869 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv13,pv43]) (by decide +kernel)
def pv140869 : PrimeValue := ⟨140869, pr140869⟩
private theorem pr140891 : PrimeCertificate 140891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv73,pv193]) (by decide +kernel)
def pv140891 : PrimeValue := ⟨140891, pr140891⟩
private theorem pr140897 : PrimeCertificate 140897 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv17,pv37]) (by decide +kernel)
def pv140897 : PrimeValue := ⟨140897, pr140897⟩
private theorem pr140909 : PrimeCertificate 140909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv35227]) (by decide +kernel)
def pv140909 : PrimeValue := ⟨140909, pr140909⟩
private theorem pr140929 : PrimeCertificate 140929 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv367]) (by decide +kernel)
def pv140929 : PrimeValue := ⟨140929, pr140929⟩
private theorem pr140939 : PrimeCertificate 140939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv10067]) (by decide +kernel)
def pv140939 : PrimeValue := ⟨140939, pr140939⟩
private theorem pr140977 : PrimeCertificate 140977 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv89]) (by decide +kernel)
def pv140977 : PrimeValue := ⟨140977, pr140977⟩
private theorem pr140983 : PrimeCertificate 140983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23497]) (by decide +kernel)
def pv140983 : PrimeValue := ⟨140983, pr140983⟩
private theorem pr140989 : PrimeCertificate 140989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv379]) (by decide +kernel)
def pv140989 : PrimeValue := ⟨140989, pr140989⟩
private theorem pr141023 : PrimeCertificate 141023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv1439]) (by decide +kernel)
def pv141023 : PrimeValue := ⟨141023, pr141023⟩
private theorem pr141041 : PrimeCertificate 141041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv41,pv43]) (by decide +kernel)
def pv141041 : PrimeValue := ⟨141041, pr141041⟩
private theorem pr141061 : PrimeCertificate 141061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv2351]) (by decide +kernel)
def pv141061 : PrimeValue := ⟨141061, pr141061⟩
private theorem pr141067 : PrimeCertificate 141067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv461]) (by decide +kernel)
def pv141067 : PrimeValue := ⟨141067, pr141067⟩
private theorem pr141073 : PrimeCertificate 141073 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2939]) (by decide +kernel)
def pv141073 : PrimeValue := ⟨141073, pr141073⟩
private theorem pr141079 : PrimeCertificate 141079 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv3359]) (by decide +kernel)
def pv141079 : PrimeValue := ⟨141079, pr141079⟩
private theorem pr141107 : PrimeCertificate 141107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv10079]) (by decide +kernel)
def pv141107 : PrimeValue := ⟨141107, pr141107⟩
private theorem pr141121 : PrimeCertificate 141121 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv141121 : PrimeValue := ⟨141121, pr141121⟩
private theorem pr141157 : PrimeCertificate 141157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1307]) (by decide +kernel)
def pv141157 : PrimeValue := ⟨141157, pr141157⟩
private theorem pr141161 : PrimeCertificate 141161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv3529]) (by decide +kernel)
def pv141161 : PrimeValue := ⟨141161, pr141161⟩
private theorem pr141179 : PrimeCertificate 141179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv70589]) (by decide +kernel)
def pv141179 : PrimeValue := ⟨141179, pr141179⟩
private theorem pr141199 : PrimeCertificate 141199 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv101,pv233]) (by decide +kernel)
def pv141199 : PrimeValue := ⟨141199, pr141199⟩
private theorem pr141209 : PrimeCertificate 141209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv929]) (by decide +kernel)
def pv141209 : PrimeValue := ⟨141209, pr141209⟩
private theorem pr141221 : PrimeCertificate 141221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv307]) (by decide +kernel)
def pv141221 : PrimeValue := ⟨141221, pr141221⟩
private theorem pr141223 : PrimeCertificate 141223 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23537]) (by decide +kernel)
def pv141223 : PrimeValue := ⟨141223, pr141223⟩
private theorem pr141241 : PrimeCertificate 141241 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv11,pv107]) (by decide +kernel)
def pv141241 : PrimeValue := ⟨141241, pr141241⟩
private theorem pr141257 : PrimeCertificate 141257 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17657]) (by decide +kernel)
def pv141257 : PrimeValue := ⟨141257, pr141257⟩
private theorem pr141263 : PrimeCertificate 141263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv6421]) (by decide +kernel)
def pv141263 : PrimeValue := ⟨141263, pr141263⟩
private theorem pr141277 : PrimeCertificate 141277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61,pv193]) (by decide +kernel)
def pv141277 : PrimeValue := ⟨141277, pr141277⟩
private theorem pr141283 : PrimeCertificate 141283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv167]) (by decide +kernel)
def pv141283 : PrimeValue := ⟨141283, pr141283⟩
private theorem pr141307 : PrimeCertificate 141307 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv2141]) (by decide +kernel)
def pv141307 : PrimeValue := ⟨141307, pr141307⟩
private theorem pr141319 : PrimeCertificate 141319 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv2617]) (by decide +kernel)
def pv141319 : PrimeValue := ⟨141319, pr141319⟩
private theorem pr141353 : PrimeCertificate 141353 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17669]) (by decide +kernel)
def pv141353 : PrimeValue := ⟨141353, pr141353⟩
private theorem pr141359 : PrimeCertificate 141359 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv23,pv439]) (by decide +kernel)
def pv141359 : PrimeValue := ⟨141359, pr141359⟩
private theorem pr141371 : PrimeCertificate 141371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv67,pv211]) (by decide +kernel)
def pv141371 : PrimeValue := ⟨141371, pr141371⟩
private theorem pr141397 : PrimeCertificate 141397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11783]) (by decide +kernel)
def pv141397 : PrimeValue := ⟨141397, pr141397⟩
private theorem pr141403 : PrimeCertificate 141403 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23567]) (by decide +kernel)
def pv141403 : PrimeValue := ⟨141403, pr141403⟩
private theorem pr141413 : PrimeCertificate 141413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv35353]) (by decide +kernel)
def pv141413 : PrimeValue := ⟨141413, pr141413⟩
private theorem pr141439 : PrimeCertificate 141439 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv2143]) (by decide +kernel)
def pv141439 : PrimeValue := ⟨141439, pr141439⟩
private theorem pr141443 : PrimeCertificate 141443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv10103]) (by decide +kernel)
def pv141443 : PrimeValue := ⟨141443, pr141443⟩
private theorem pr141461 : PrimeCertificate 141461 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv643]) (by decide +kernel)
def pv141461 : PrimeValue := ⟨141461, pr141461⟩
private theorem pr141481 : PrimeCertificate 141481 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv131]) (by decide +kernel)
def pv141481 : PrimeValue := ⟨141481, pr141481⟩
private theorem pr141497 : PrimeCertificate 141497 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv769]) (by decide +kernel)
def pv141497 : PrimeValue := ⟨141497, pr141497⟩
private theorem pr141499 : PrimeCertificate 141499 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv1123]) (by decide +kernel)
def pv141499 : PrimeValue := ⟨141499, pr141499⟩
private theorem pr141509 : PrimeCertificate 141509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv2081]) (by decide +kernel)
def pv141509 : PrimeValue := ⟨141509, pr141509⟩
private theorem pr141511 : PrimeCertificate 141511 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv53,pv89]) (by decide +kernel)
def pv141511 : PrimeValue := ⟨141511, pr141511⟩
private theorem pr141529 : PrimeCertificate 141529 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5897]) (by decide +kernel)
def pv141529 : PrimeValue := ⟨141529, pr141529⟩
private theorem pr141539 : PrimeCertificate 141539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv70769]) (by decide +kernel)
def pv141539 : PrimeValue := ⟨141539, pr141539⟩
private theorem pr141551 : PrimeCertificate 141551 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv19,pv149]) (by decide +kernel)
def pv141551 : PrimeValue := ⟨141551, pr141551⟩
private theorem pr141587 : PrimeCertificate 141587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv70793]) (by decide +kernel)
def pv141587 : PrimeValue := ⟨141587, pr141587⟩
private theorem pr141601 : PrimeCertificate 141601 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv59]) (by decide +kernel)
def pv141601 : PrimeValue := ⟨141601, pr141601⟩
private theorem pr141613 : PrimeCertificate 141613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11801]) (by decide +kernel)
def pv141613 : PrimeValue := ⟨141613, pr141613⟩
private theorem pr141619 : PrimeCertificate 141619 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23603]) (by decide +kernel)
def pv141619 : PrimeValue := ⟨141619, pr141619⟩
private theorem pr141623 : PrimeCertificate 141623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv419]) (by decide +kernel)
def pv141623 : PrimeValue := ⟨141623, pr141623⟩
private theorem pr141637 : PrimeCertificate 141637 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv29,pv37]) (by decide +kernel)
def pv141637 : PrimeValue := ⟨141637, pr141637⟩
private theorem pr141649 : PrimeCertificate 141649 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv13,pv227]) (by decide +kernel)
def pv141649 : PrimeValue := ⟨141649, pr141649⟩
private theorem pr141653 : PrimeCertificate 141653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv5059]) (by decide +kernel)
def pv141653 : PrimeValue := ⟨141653, pr141653⟩
private theorem pr141667 : PrimeCertificate 141667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv3373]) (by decide +kernel)
def pv141667 : PrimeValue := ⟨141667, pr141667⟩
private theorem pr141671 : PrimeCertificate 141671 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv31,pv457]) (by decide +kernel)
def pv141671 : PrimeValue := ⟨141671, pr141671⟩
private theorem pr141677 : PrimeCertificate 141677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv35419]) (by decide +kernel)
def pv141677 : PrimeValue := ⟨141677, pr141677⟩
private theorem pr141679 : PrimeCertificate 141679 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv17,pv463]) (by decide +kernel)
def pv141679 : PrimeValue := ⟨141679, pr141679⟩
private theorem pr141689 : PrimeCertificate 141689 :=
  certifyPrime (q := pv3) (ls := [pv2,pv89,pv199]) (by decide +kernel)
def pv141689 : PrimeValue := ⟨141689, pr141689⟩
private theorem pr141707 : PrimeCertificate 141707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv70853]) (by decide +kernel)
def pv141707 : PrimeValue := ⟨141707, pr141707⟩
private theorem pr141709 : PrimeCertificate 141709 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv241]) (by decide +kernel)
def pv141709 : PrimeValue := ⟨141709, pr141709⟩
private theorem pr141731 : PrimeCertificate 141731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv14173]) (by decide +kernel)
def pv141731 : PrimeValue := ⟨141731, pr141731⟩
private theorem pr141761 : PrimeCertificate 141761 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv443]) (by decide +kernel)
def pv141761 : PrimeValue := ⟨141761, pr141761⟩
private theorem pr141767 : PrimeCertificate 141767 :=
  certifyPrime (q := pv5) (ls := [pv2,pv73,pv971]) (by decide +kernel)
def pv141767 : PrimeValue := ⟨141767, pr141767⟩
private theorem pr141773 : PrimeCertificate 141773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv67]) (by decide +kernel)
def pv141773 : PrimeValue := ⟨141773, pr141773⟩
private theorem pr141793 : PrimeCertificate 141793 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv211]) (by decide +kernel)
def pv141793 : PrimeValue := ⟨141793, pr141793⟩
private theorem pr141803 : PrimeCertificate 141803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv70901]) (by decide +kernel)
def pv141803 : PrimeValue := ⟨141803, pr141803⟩
private theorem pr141811 : PrimeCertificate 141811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv29,pv163]) (by decide +kernel)
def pv141811 : PrimeValue := ⟨141811, pr141811⟩
private theorem pr141833 : PrimeCertificate 141833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17729]) (by decide +kernel)
def pv141833 : PrimeValue := ⟨141833, pr141833⟩
private theorem pr141853 : PrimeCertificate 141853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11821]) (by decide +kernel)
def pv141853 : PrimeValue := ⟨141853, pr141853⟩
private theorem pr141871 : PrimeCertificate 141871 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv4729]) (by decide +kernel)
def pv141871 : PrimeValue := ⟨141871, pr141871⟩
private theorem pr141917 : PrimeCertificate 141917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv2087]) (by decide +kernel)
def pv141917 : PrimeValue := ⟨141917, pr141917⟩
private theorem pr141931 : PrimeCertificate 141931 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv83]) (by decide +kernel)
def pv141931 : PrimeValue := ⟨141931, pr141931⟩
private theorem pr141937 : PrimeCertificate 141937 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv2957]) (by decide +kernel)
def pv141937 : PrimeValue := ⟨141937, pr141937⟩
private theorem pr141941 : PrimeCertificate 141941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv47,pv151]) (by decide +kernel)
def pv141941 : PrimeValue := ⟨141941, pr141941⟩
private theorem pr141959 : PrimeCertificate 141959 :=
  certifyPrime (q := pv11) (ls := [pv2,pv70979]) (by decide +kernel)
def pv141959 : PrimeValue := ⟨141959, pr141959⟩
private theorem pr141961 : PrimeCertificate 141961 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv7,pv13]) (by decide +kernel)
def pv141961 : PrimeValue := ⟨141961, pr141961⟩
private theorem pr141991 : PrimeCertificate 141991 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv4733]) (by decide +kernel)
def pv141991 : PrimeValue := ⟨141991, pr141991⟩
private theorem pr142019 : PrimeCertificate 142019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv4177]) (by decide +kernel)
def pv142019 : PrimeValue := ⟨142019, pr142019⟩
private theorem pr142031 : PrimeCertificate 142031 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv2029]) (by decide +kernel)
def pv142031 : PrimeValue := ⟨142031, pr142031⟩
private theorem pr142049 : PrimeCertificate 142049 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv193]) (by decide +kernel)
def pv142049 : PrimeValue := ⟨142049, pr142049⟩
private theorem pr142057 : PrimeCertificate 142057 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1973]) (by decide +kernel)
def pv142057 : PrimeValue := ⟨142057, pr142057⟩
private theorem pr142061 : PrimeCertificate 142061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7103]) (by decide +kernel)
def pv142061 : PrimeValue := ⟨142061, pr142061⟩
private theorem pr142097 : PrimeCertificate 142097 :=
  certifyPrime (q := pv3) (ls := [pv2,pv83,pv107]) (by decide +kernel)
def pv142097 : PrimeValue := ⟨142097, pr142097⟩
private theorem pr142099 : PrimeCertificate 142099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv2153]) (by decide +kernel)
def pv142099 : PrimeValue := ⟨142099, pr142099⟩
private theorem pr142111 : PrimeCertificate 142111 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv1579]) (by decide +kernel)
def pv142111 : PrimeValue := ⟨142111, pr142111⟩
private theorem pr142123 : PrimeCertificate 142123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23687]) (by decide +kernel)
def pv142123 : PrimeValue := ⟨142123, pr142123⟩
private theorem pr142151 : PrimeCertificate 142151 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv2843]) (by decide +kernel)
def pv142151 : PrimeValue := ⟨142151, pr142151⟩
private theorem pr142169 : PrimeCertificate 142169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv1367]) (by decide +kernel)
def pv142169 : PrimeValue := ⟨142169, pr142169⟩
private theorem pr142189 : PrimeCertificate 142189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv41]) (by decide +kernel)
def pv142189 : PrimeValue := ⟨142189, pr142189⟩
private theorem pr142193 : PrimeCertificate 142193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv8887]) (by decide +kernel)
def pv142193 : PrimeValue := ⟨142193, pr142193⟩
private theorem pr142211 : PrimeCertificate 142211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv14221]) (by decide +kernel)
def pv142211 : PrimeValue := ⟨142211, pr142211⟩
private theorem pr142223 : PrimeCertificate 142223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv47,pv89]) (by decide +kernel)
def pv142223 : PrimeValue := ⟨142223, pr142223⟩
private theorem pr142231 : PrimeCertificate 142231 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv431]) (by decide +kernel)
def pv142231 : PrimeValue := ⟨142231, pr142231⟩
private theorem pr142271 : PrimeCertificate 142271 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv41,pv347]) (by decide +kernel)
def pv142271 : PrimeValue := ⟨142271, pr142271⟩
private theorem pr142297 : PrimeCertificate 142297 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv11]) (by decide +kernel)
def pv142297 : PrimeValue := ⟨142297, pr142297⟩
private theorem pr142319 : PrimeCertificate 142319 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv6469]) (by decide +kernel)
def pv142319 : PrimeValue := ⟨142319, pr142319⟩
private theorem pr142369 : PrimeCertificate 142369 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv1483]) (by decide +kernel)
def pv142369 : PrimeValue := ⟨142369, pr142369⟩
private theorem pr142381 : PrimeCertificate 142381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv113]) (by decide +kernel)
def pv142381 : PrimeValue := ⟨142381, pr142381⟩
private theorem pr142391 : PrimeCertificate 142391 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv29,pv491]) (by decide +kernel)
def pv142391 : PrimeValue := ⟨142391, pr142391⟩
private theorem pr142403 : PrimeCertificate 142403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv5477]) (by decide +kernel)
def pv142403 : PrimeValue := ⟨142403, pr142403⟩
private theorem pr142421 : PrimeCertificate 142421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7121]) (by decide +kernel)
def pv142421 : PrimeValue := ⟨142421, pr142421⟩
private theorem pr142427 : PrimeCertificate 142427 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv59,pv71]) (by decide +kernel)
def pv142427 : PrimeValue := ⟨142427, pr142427⟩
private theorem pr142433 : PrimeCertificate 142433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv4451]) (by decide +kernel)
def pv142433 : PrimeValue := ⟨142433, pr142433⟩
private theorem pr142453 : PrimeCertificate 142453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1319]) (by decide +kernel)
def pv142453 : PrimeValue := ⟨142453, pr142453⟩
private theorem pr142469 : PrimeCertificate 142469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv35617]) (by decide +kernel)
def pv142469 : PrimeValue := ⟨142469, pr142469⟩
private theorem pr142501 : PrimeCertificate 142501 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv142501 : PrimeValue := ⟨142501, pr142501⟩
private theorem pr142529 : PrimeCertificate 142529 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv131]) (by decide +kernel)
def pv142529 : PrimeValue := ⟨142529, pr142529⟩
private theorem pr142537 : PrimeCertificate 142537 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv5939]) (by decide +kernel)
def pv142537 : PrimeValue := ⟨142537, pr142537⟩
private theorem pr142543 : PrimeCertificate 142543 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7919]) (by decide +kernel)
def pv142543 : PrimeValue := ⟨142543, pr142543⟩
private theorem pr142547 : PrimeCertificate 142547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv263,pv271]) (by decide +kernel)
def pv142547 : PrimeValue := ⟨142547, pr142547⟩
private theorem pr142553 : PrimeCertificate 142553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv103,pv173]) (by decide +kernel)
def pv142553 : PrimeValue := ⟨142553, pr142553⟩
private theorem pr142559 : PrimeCertificate 142559 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv5483]) (by decide +kernel)
def pv142559 : PrimeValue := ⟨142559, pr142559⟩
private theorem pr142573 : PrimeCertificate 142573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv109]) (by decide +kernel)
def pv142573 : PrimeValue := ⟨142573, pr142573⟩
private theorem pr142589 : PrimeCertificate 142589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv829]) (by decide +kernel)
def pv142589 : PrimeValue := ⟨142589, pr142589⟩
private theorem pr142591 : PrimeCertificate 142591 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv97]) (by decide +kernel)
def pv142591 : PrimeValue := ⟨142591, pr142591⟩
private theorem pr142601 : PrimeCertificate 142601 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv23,pv31]) (by decide +kernel)
def pv142601 : PrimeValue := ⟨142601, pr142601⟩
private theorem pr142607 : PrimeCertificate 142607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv113,pv631]) (by decide +kernel)
def pv142607 : PrimeValue := ⟨142607, pr142607⟩
private theorem pr142609 : PrimeCertificate 142609 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv2971]) (by decide +kernel)
def pv142609 : PrimeValue := ⟨142609, pr142609⟩
private theorem pr142657 : PrimeCertificate 142657 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv743]) (by decide +kernel)
def pv142657 : PrimeValue := ⟨142657, pr142657⟩
private theorem pr142673 : PrimeCertificate 142673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv241]) (by decide +kernel)
def pv142673 : PrimeValue := ⟨142673, pr142673⟩
private theorem pr142699 : PrimeCertificate 142699 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv17,pv1399]) (by decide +kernel)
def pv142699 : PrimeValue := ⟨142699, pr142699⟩
private theorem pr142711 : PrimeCertificate 142711 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv67,pv71]) (by decide +kernel)
def pv142711 : PrimeValue := ⟨142711, pr142711⟩
private theorem pr142757 : PrimeCertificate 142757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89,pv401]) (by decide +kernel)
def pv142757 : PrimeValue := ⟨142757, pr142757⟩
private theorem pr142759 : PrimeCertificate 142759 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv11,pv103]) (by decide +kernel)
def pv142759 : PrimeValue := ⟨142759, pr142759⟩
private theorem pr142771 : PrimeCertificate 142771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv4759]) (by decide +kernel)
def pv142771 : PrimeValue := ⟨142771, pr142771⟩
private theorem pr142789 : PrimeCertificate 142789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv73,pv163]) (by decide +kernel)
def pv142789 : PrimeValue := ⟨142789, pr142789⟩
private theorem pr142799 : PrimeCertificate 142799 :=
  certifyPrime (q := pv13) (ls := [pv2,pv71399]) (by decide +kernel)
def pv142799 : PrimeValue := ⟨142799, pr142799⟩
private theorem pr142811 : PrimeCertificate 142811 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv14281]) (by decide +kernel)
def pv142811 : PrimeValue := ⟨142811, pr142811⟩
private theorem pr142837 : PrimeCertificate 142837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11903]) (by decide +kernel)
def pv142837 : PrimeValue := ⟨142837, pr142837⟩
private theorem pr142841 : PrimeCertificate 142841 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv3571]) (by decide +kernel)
def pv142841 : PrimeValue := ⟨142841, pr142841⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
