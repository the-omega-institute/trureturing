/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table107
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table107.pv465643
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table014
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table019
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table030
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table072
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table073

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr465643 : Nat.Prime 465643 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv8623]) (by decide +kernel)
def pv465643 : PrimeValue := ⟨465643, pr465643⟩
private theorem pr465659 : Nat.Prime 465659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv53,pv191]) (by decide +kernel)
def pv465659 : PrimeValue := ⟨465659, pr465659⟩
private theorem pr465739 : Nat.Prime 465739 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv853]) (by decide +kernel)
def pv465739 : PrimeValue := ⟨465739, pr465739⟩
private theorem pr465743 : Nat.Prime 465743 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv232871]) (by decide +kernel)
def pv465743 : PrimeValue := ⟨465743, pr465743⟩
private theorem pr465761 : Nat.Prime 465761 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv41,pv71]) (by decide +kernel)
def pv465761 : PrimeValue := ⟨465761, pr465761⟩
private theorem pr465841 : Nat.Prime 465841 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv647]) (by decide +kernel)
def pv465841 : PrimeValue := ⟨465841, pr465841⟩
private theorem pr465887 : Nat.Prime 465887 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv73,pv3191]) (by decide +kernel)
def pv465887 : PrimeValue := ⟨465887, pr465887⟩
private theorem pr465929 : Nat.Prime 465929 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv139,pv419]) (by decide +kernel)
def pv465929 : PrimeValue := ⟨465929, pr465929⟩
private theorem pr466019 : Nat.Prime 466019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv33287]) (by decide +kernel)
def pv466019 : PrimeValue := ⟨466019, pr466019⟩
private theorem pr466027 : Nat.Prime 466027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv23,pv307]) (by decide +kernel)
def pv466027 : PrimeValue := ⟨466027, pr466027⟩
private theorem pr466043 : Nat.Prime 466043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv233021]) (by decide +kernel)
def pv466043 : PrimeValue := ⟨466043, pr466043⟩
private theorem pr466087 : Nat.Prime 466087 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv77681]) (by decide +kernel)
def pv466087 : PrimeValue := ⟨466087, pr466087⟩
private theorem pr466153 : Nat.Prime 466153 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19423]) (by decide +kernel)
def pv466153 : PrimeValue := ⟨466153, pr466153⟩
private theorem pr466261 : Nat.Prime 466261 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv19,pv409]) (by decide +kernel)
def pv466261 : PrimeValue := ⟨466261, pr466261⟩
private theorem pr466267 : Nat.Prime 466267 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv77711]) (by decide +kernel)
def pv466267 : PrimeValue := ⟨466267, pr466267⟩
private theorem pr466283 : Nat.Prime 466283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv233141]) (by decide +kernel)
def pv466283 : PrimeValue := ⟨466283, pr466283⟩
private theorem pr466303 : Nat.Prime 466303 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv31,pv109]) (by decide +kernel)
def pv466303 : PrimeValue := ⟨466303, pr466303⟩
private theorem pr466331 : Nat.Prime 466331 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv46633]) (by decide +kernel)
def pv466331 : PrimeValue := ⟨466331, pr466331⟩
private theorem pr466357 : Nat.Prime 466357 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv3533]) (by decide +kernel)
def pv466357 : PrimeValue := ⟨466357, pr466357⟩
private theorem pr466409 : Nat.Prime 466409 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv173,pv337]) (by decide +kernel)
def pv466409 : PrimeValue := ⟨466409, pr466409⟩
private theorem pr466423 : Nat.Prime 466423 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv37,pv191]) (by decide +kernel)
def pv466423 : PrimeValue := ⟨466423, pr466423⟩
private theorem pr466441 : Nat.Prime 466441 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv13,pv23]) (by decide +kernel)
def pv466441 : PrimeValue := ⟨466441, pr466441⟩
private theorem pr466451 : Nat.Prime 466451 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19,pv491]) (by decide +kernel)
def pv466451 : PrimeValue := ⟨466451, pr466451⟩
private theorem pr466483 : Nat.Prime 466483 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv77747]) (by decide +kernel)
def pv466483 : PrimeValue := ⟨466483, pr466483⟩
private theorem pr466517 : Nat.Prime 466517 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv223,pv523]) (by decide +kernel)
def pv466517 : PrimeValue := ⟨466517, pr466517⟩
private theorem pr466567 : Nat.Prime 466567 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv77761]) (by decide +kernel)
def pv466567 : PrimeValue := ⟨466567, pr466567⟩
private theorem pr466717 : Nat.Prime 466717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv23,pv89]) (by decide +kernel)
def pv466717 : PrimeValue := ⟨466717, pr466717⟩
private theorem pr466723 : Nat.Prime 466723 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv43,pv67]) (by decide +kernel)
def pv466723 : PrimeValue := ⟨466723, pr466723⟩
private theorem pr466747 : Nat.Prime 466747 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv11113]) (by decide +kernel)
def pv466747 : PrimeValue := ⟨466747, pr466747⟩
private theorem pr466751 : Nat.Prime 466751 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv1867]) (by decide +kernel)
def pv466751 : PrimeValue := ⟨466751, pr466751⟩
private theorem pr466777 : Nat.Prime 466777 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2161]) (by decide +kernel)
def pv466777 : PrimeValue := ⟨466777, pr466777⟩
private theorem pr466853 : Nat.Prime 466853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv127,pv919]) (by decide +kernel)
def pv466853 : PrimeValue := ⟨466853, pr466853⟩
private theorem pr466913 : Nat.Prime 466913 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv14591]) (by decide +kernel)
def pv466913 : PrimeValue := ⟨466913, pr466913⟩
private theorem pr466919 : Nat.Prime 466919 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv157,pv1487]) (by decide +kernel)
def pv466919 : PrimeValue := ⟨466919, pr466919⟩
private theorem pr466951 : Nat.Prime 466951 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv283]) (by decide +kernel)
def pv466951 : PrimeValue := ⟨466951, pr466951⟩
private theorem pr467063 : Nat.Prime 467063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv347,pv673]) (by decide +kernel)
def pv467063 : PrimeValue := ⟨467063, pr467063⟩
private theorem pr467081 : Nat.Prime 467081 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11677]) (by decide +kernel)
def pv467081 : PrimeValue := ⟨467081, pr467081⟩
private theorem pr467083 : Nat.Prime 467083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv337]) (by decide +kernel)
def pv467083 : PrimeValue := ⟨467083, pr467083⟩
private theorem pr467141 : Nat.Prime 467141 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23357]) (by decide +kernel)
def pv467141 : PrimeValue := ⟨467141, pr467141⟩
private theorem pr467171 : Nat.Prime 467171 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv31,pv137]) (by decide +kernel)
def pv467171 : PrimeValue := ⟨467171, pr467171⟩
private theorem pr467197 : Nat.Prime 467197 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv38933]) (by decide +kernel)
def pv467197 : PrimeValue := ⟨467197, pr467197⟩
private theorem pr467209 : Nat.Prime 467209 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv103]) (by decide +kernel)
def pv467209 : PrimeValue := ⟨467209, pr467209⟩
private theorem pr467261 : Nat.Prime 467261 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv61,pv383]) (by decide +kernel)
def pv467261 : PrimeValue := ⟨467261, pr467261⟩
private theorem pr467293 : Nat.Prime 467293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv5563]) (by decide +kernel)
def pv467293 : PrimeValue := ⟨467293, pr467293⟩
private theorem pr467297 : Nat.Prime 467297 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv859]) (by decide +kernel)
def pv467297 : PrimeValue := ⟨467297, pr467297⟩
private theorem pr467317 : Nat.Prime 467317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4327]) (by decide +kernel)
def pv467317 : PrimeValue := ⟨467317, pr467317⟩
private theorem pr467371 : Nat.Prime 467371 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv577]) (by decide +kernel)
def pv467371 : PrimeValue := ⟨467371, pr467371⟩
private theorem pr467399 : Nat.Prime 467399 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv17,pv59,pv233]) (by decide +kernel)
def pv467399 : PrimeValue := ⟨467399, pr467399⟩
private theorem pr467471 : Nat.Prime 467471 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv46747]) (by decide +kernel)
def pv467471 : PrimeValue := ⟨467471, pr467471⟩
private theorem pr467473 : Nat.Prime 467473 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv9739]) (by decide +kernel)
def pv467473 : PrimeValue := ⟨467473, pr467473⟩
private theorem pr467507 : Nat.Prime 467507 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv17981]) (by decide +kernel)
def pv467507 : PrimeValue := ⟨467507, pr467507⟩
private theorem pr467527 : Nat.Prime 467527 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv67,pv1163]) (by decide +kernel)
def pv467527 : PrimeValue := ⟨467527, pr467527⟩
private theorem pr467531 : Nat.Prime 467531 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv6679]) (by decide +kernel)
def pv467531 : PrimeValue := ⟨467531, pr467531⟩
private theorem pr467543 : Nat.Prime 467543 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv31,pv7541]) (by decide +kernel)
def pv467543 : PrimeValue := ⟨467543, pr467543⟩
private theorem pr467557 : Nat.Prime 467557 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv47,pv829]) (by decide +kernel)
def pv467557 : PrimeValue := ⟨467557, pr467557⟩
private theorem pr467591 : Nat.Prime 467591 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv19,pv23,pv107]) (by decide +kernel)
def pv467591 : PrimeValue := ⟨467591, pr467591⟩
private theorem pr467617 : Nat.Prime 467617 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv4871]) (by decide +kernel)
def pv467617 : PrimeValue := ⟨467617, pr467617⟩
private theorem pr467627 : Nat.Prime 467627 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv3833]) (by decide +kernel)
def pv467627 : PrimeValue := ⟨467627, pr467627⟩
private theorem pr467651 : Nat.Prime 467651 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv47,pv199]) (by decide +kernel)
def pv467651 : PrimeValue := ⟨467651, pr467651⟩
private theorem pr467669 : Nat.Prime 467669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv2719]) (by decide +kernel)
def pv467669 : PrimeValue := ⟨467669, pr467669⟩
private theorem pr467681 : Nat.Prime 467681 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv37,pv79]) (by decide +kernel)
def pv467681 : PrimeValue := ⟨467681, pr467681⟩
private theorem pr467699 : Nat.Prime 467699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv3037]) (by decide +kernel)
def pv467699 : PrimeValue := ⟨467699, pr467699⟩
private theorem pr467713 : Nat.Prime 467713 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv29]) (by decide +kernel)
def pv467713 : PrimeValue := ⟨467713, pr467713⟩
private theorem pr467743 : Nat.Prime 467743 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv19,pv373]) (by decide +kernel)
def pv467743 : PrimeValue := ⟨467743, pr467743⟩
private theorem pr467827 : Nat.Prime 467827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv103,pv757]) (by decide +kernel)
def pv467827 : PrimeValue := ⟨467827, pr467827⟩
private theorem pr467869 : Nat.Prime 467869 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv127,pv307]) (by decide +kernel)
def pv467869 : PrimeValue := ⟨467869, pr467869⟩
private theorem pr467953 : Nat.Prime 467953 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv9749]) (by decide +kernel)
def pv467953 : PrimeValue := ⟨467953, pr467953⟩
private theorem pr468001 : Nat.Prime 468001 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv468001 : PrimeValue := ⟨468001, pr468001⟩
private theorem pr468059 : Nat.Prime 468059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv234029]) (by decide +kernel)
def pv468059 : PrimeValue := ⟨468059, pr468059⟩
private theorem pr468071 : Nat.Prime 468071 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv46807]) (by decide +kernel)
def pv468071 : PrimeValue := ⟨468071, pr468071⟩
private theorem pr468113 : Nat.Prime 468113 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv1721]) (by decide +kernel)
def pv468113 : PrimeValue := ⟨468113, pr468113⟩
private theorem pr468253 : Nat.Prime 468253 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13007]) (by decide +kernel)
def pv468253 : PrimeValue := ⟨468253, pr468253⟩
private theorem pr468271 : Nat.Prime 468271 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv43]) (by decide +kernel)
def pv468271 : PrimeValue := ⟨468271, pr468271⟩
private theorem pr468323 : Nat.Prime 468323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv234161]) (by decide +kernel)
def pv468323 : PrimeValue := ⟨468323, pr468323⟩
private theorem pr468389 : Nat.Prime 468389 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv6163]) (by decide +kernel)
def pv468389 : PrimeValue := ⟨468389, pr468389⟩
private theorem pr468451 : Nat.Prime 468451 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv347]) (by decide +kernel)
def pv468451 : PrimeValue := ⟨468451, pr468451⟩
private theorem pr468493 : Nat.Prime 468493 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv39041]) (by decide +kernel)
def pv468493 : PrimeValue := ⟨468493, pr468493⟩
private theorem pr468527 : Nat.Prime 468527 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv317,pv739]) (by decide +kernel)
def pv468527 : PrimeValue := ⟨468527, pr468527⟩
private theorem pr468557 : Nat.Prime 468557 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv23,pv463]) (by decide +kernel)
def pv468557 : PrimeValue := ⟨468557, pr468557⟩
private theorem pr468593 : Nat.Prime 468593 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29287]) (by decide +kernel)
def pv468593 : PrimeValue := ⟨468593, pr468593⟩
private theorem pr468647 : Nat.Prime 468647 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv234323]) (by decide +kernel)
def pv468647 : PrimeValue := ⟨468647, pr468647⟩
private theorem pr468667 : Nat.Prime 468667 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv263]) (by decide +kernel)
def pv468667 : PrimeValue := ⟨468667, pr468667⟩
private theorem pr468683 : Nat.Prime 468683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv234341]) (by decide +kernel)
def pv468683 : PrimeValue := ⟨468683, pr468683⟩
private theorem pr468703 : Nat.Prime 468703 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv2003]) (by decide +kernel)
def pv468703 : PrimeValue := ⟨468703, pr468703⟩
private theorem pr468709 : Nat.Prime 468709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv139,pv281]) (by decide +kernel)
def pv468709 : PrimeValue := ⟨468709, pr468709⟩
private theorem pr468737 : Nat.Prime 468737 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1831]) (by decide +kernel)
def pv468737 : PrimeValue := ⟨468737, pr468737⟩
private theorem pr468773 : Nat.Prime 468773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv117193]) (by decide +kernel)
def pv468773 : PrimeValue := ⟨468773, pr468773⟩
private theorem pr468781 : Nat.Prime 468781 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv13,pv601]) (by decide +kernel)
def pv468781 : PrimeValue := ⟨468781, pr468781⟩
private theorem pr468803 : Nat.Prime 468803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv157,pv1493]) (by decide +kernel)
def pv468803 : PrimeValue := ⟨468803, pr468803⟩
private theorem pr468841 : Nat.Prime 468841 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv3907]) (by decide +kernel)
def pv468841 : PrimeValue := ⟨468841, pr468841⟩
private theorem pr468883 : Nat.Prime 468883 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv457]) (by decide +kernel)
def pv468883 : PrimeValue := ⟨468883, pr468883⟩
private theorem pr468887 : Nat.Prime 468887 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv21313]) (by decide +kernel)
def pv468887 : PrimeValue := ⟨468887, pr468887⟩
private theorem pr468889 : Nat.Prime 468889 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv7,pv2791]) (by decide +kernel)
def pv468889 : PrimeValue := ⟨468889, pr468889⟩
private theorem pr468913 : Nat.Prime 468913 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv9769]) (by decide +kernel)
def pv468913 : PrimeValue := ⟨468913, pr468913⟩
private theorem pr468953 : Nat.Prime 468953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv73]) (by decide +kernel)
def pv468953 : PrimeValue := ⟨468953, pr468953⟩
private theorem pr468967 : Nat.Prime 468967 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv47,pv1663]) (by decide +kernel)
def pv468967 : PrimeValue := ⟨468967, pr468967⟩
private theorem pr468973 : Nat.Prime 468973 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv1861]) (by decide +kernel)
def pv468973 : PrimeValue := ⟨468973, pr468973⟩
private theorem pr469121 : Nat.Prime 469121 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv733]) (by decide +kernel)
def pv469121 : PrimeValue := ⟨469121, pr469121⟩
private theorem pr469193 : Nat.Prime 469193 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv223,pv263]) (by decide +kernel)
def pv469193 : PrimeValue := ⟨469193, pr469193⟩
private theorem pr469207 : Nat.Prime 469207 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv8689]) (by decide +kernel)
def pv469207 : PrimeValue := ⟨469207, pr469207⟩
private theorem pr469229 : Nat.Prime 469229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv117307]) (by decide +kernel)
def pv469229 : PrimeValue := ⟨469229, pr469229⟩
private theorem pr469237 : Nat.Prime 469237 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv39103]) (by decide +kernel)
def pv469237 : PrimeValue := ⟨469237, pr469237⟩
private theorem pr469241 : Nat.Prime 469241 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11731]) (by decide +kernel)
def pv469241 : PrimeValue := ⟨469241, pr469241⟩
private theorem pr469253 : Nat.Prime 469253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv16759]) (by decide +kernel)
def pv469253 : PrimeValue := ⟨469253, pr469253⟩
private theorem pr469267 : Nat.Prime 469267 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv11173]) (by decide +kernel)
def pv469267 : PrimeValue := ⟨469267, pr469267⟩
private theorem pr469321 : Nat.Prime 469321 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv3911]) (by decide +kernel)
def pv469321 : PrimeValue := ⟨469321, pr469321⟩
private theorem pr469429 : Nat.Prime 469429 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv39119]) (by decide +kernel)
def pv469429 : PrimeValue := ⟨469429, pr469429⟩
private theorem pr469439 : Nat.Prime 469439 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv17,pv13807]) (by decide +kernel)
def pv469439 : PrimeValue := ⟨469439, pr469439⟩
private theorem pr469501 : Nat.Prime 469501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv313]) (by decide +kernel)
def pv469501 : PrimeValue := ⟨469501, pr469501⟩
private theorem pr469543 : Nat.Prime 469543 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv139,pv563]) (by decide +kernel)
def pv469543 : PrimeValue := ⟨469543, pr469543⟩
private theorem pr469583 : Nat.Prime 469583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv234791]) (by decide +kernel)
def pv469583 : PrimeValue := ⟨469583, pr469583⟩
private theorem pr469589 : Nat.Prime 469589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv31,pv541]) (by decide +kernel)
def pv469589 : PrimeValue := ⟨469589, pr469589⟩
private theorem pr469649 : Nat.Prime 469649 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv149,pv197]) (by decide +kernel)
def pv469649 : PrimeValue := ⟨469649, pr469649⟩
private theorem pr469657 : Nat.Prime 469657 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv593]) (by decide +kernel)
def pv469657 : PrimeValue := ⟨469657, pr469657⟩
private theorem pr469673 : Nat.Prime 469673 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv8387]) (by decide +kernel)
def pv469673 : PrimeValue := ⟨469673, pr469673⟩
private theorem pr469691 : Nat.Prime 469691 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv13,pv3613]) (by decide +kernel)
def pv469691 : PrimeValue := ⟨469691, pr469691⟩
private theorem pr469717 : Nat.Prime 469717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv3011]) (by decide +kernel)
def pv469717 : PrimeValue := ⟨469717, pr469717⟩
private theorem pr469811 : Nat.Prime 469811 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv4271]) (by decide +kernel)
def pv469811 : PrimeValue := ⟨469811, pr469811⟩
private theorem pr469823 : Nat.Prime 469823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv61,pv3851]) (by decide +kernel)
def pv469823 : PrimeValue := ⟨469823, pr469823⟩
private theorem pr469879 : Nat.Prime 469879 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv71,pv1103]) (by decide +kernel)
def pv469879 : PrimeValue := ⟨469879, pr469879⟩
private theorem pr469891 : Nat.Prime 469891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv23,pv227]) (by decide +kernel)
def pv469891 : PrimeValue := ⟨469891, pr469891⟩
private theorem pr469919 : Nat.Prime 469919 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv234959]) (by decide +kernel)
def pv469919 : PrimeValue := ⟨469919, pr469919⟩
private theorem pr469957 : Nat.Prime 469957 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv39163]) (by decide +kernel)
def pv469957 : PrimeValue := ⟨469957, pr469957⟩
private theorem pr469993 : Nat.Prime 469993 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19583]) (by decide +kernel)
def pv469993 : PrimeValue := ⟨469993, pr469993⟩
private theorem pr470021 : Nat.Prime 470021 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv71,pv331]) (by decide +kernel)
def pv470021 : PrimeValue := ⟨470021, pr470021⟩
private theorem pr470077 : Nat.Prime 470077 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv43,pv911]) (by decide +kernel)
def pv470077 : PrimeValue := ⟨470077, pr470077⟩
private theorem pr470089 : Nat.Prime 470089 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv6529]) (by decide +kernel)
def pv470089 : PrimeValue := ⟨470089, pr470089⟩
private theorem pr470131 : Nat.Prime 470131 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv15671]) (by decide +kernel)
def pv470131 : PrimeValue := ⟨470131, pr470131⟩
private theorem pr470149 : Nat.Prime 470149 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv29,pv193]) (by decide +kernel)
def pv470149 : PrimeValue := ⟨470149, pr470149⟩
private theorem pr470153 : Nat.Prime 470153 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv3457]) (by decide +kernel)
def pv470153 : PrimeValue := ⟨470153, pr470153⟩
private theorem pr470201 : Nat.Prime 470201 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv2351]) (by decide +kernel)
def pv470201 : PrimeValue := ⟨470201, pr470201⟩
private theorem pr470227 : Nat.Prime 470227 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv109,pv719]) (by decide +kernel)
def pv470227 : PrimeValue := ⟨470227, pr470227⟩
private theorem pr470243 : Nat.Prime 470243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv191,pv1231]) (by decide +kernel)
def pv470243 : PrimeValue := ⟨470243, pr470243⟩
private theorem pr470299 : Nat.Prime 470299 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv103,pv761]) (by decide +kernel)
def pv470299 : PrimeValue := ⟨470299, pr470299⟩
private theorem pr470303 : Nat.Prime 470303 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv4799]) (by decide +kernel)
def pv470303 : PrimeValue := ⟨470303, pr470303⟩
private theorem pr470333 : Nat.Prime 470333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv3793]) (by decide +kernel)
def pv470333 : PrimeValue := ⟨470333, pr470333⟩
private theorem pr470347 : Nat.Prime 470347 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv277,pv283]) (by decide +kernel)
def pv470347 : PrimeValue := ⟨470347, pr470347⟩
private theorem pr470417 : Nat.Prime 470417 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29401]) (by decide +kernel)
def pv470417 : PrimeValue := ⟨470417, pr470417⟩
private theorem pr470453 : Nat.Prime 470453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv337,pv349]) (by decide +kernel)
def pv470453 : PrimeValue := ⟨470453, pr470453⟩
private theorem pr470513 : Nat.Prime 470513 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv4201]) (by decide +kernel)
def pv470513 : PrimeValue := ⟨470513, pr470513⟩
private theorem pr470579 : Nat.Prime 470579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv235289]) (by decide +kernel)
def pv470579 : PrimeValue := ⟨470579, pr470579⟩
private theorem pr470593 : Nat.Prime 470593 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv19,pv43]) (by decide +kernel)
def pv470593 : PrimeValue := ⟨470593, pr470593⟩
private theorem pr470627 : Nat.Prime 470627 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv23,pv787]) (by decide +kernel)
def pv470627 : PrimeValue := ⟨470627, pr470627⟩
private theorem pr470647 : Nat.Prime 470647 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv2377]) (by decide +kernel)
def pv470647 : PrimeValue := ⟨470647, pr470647⟩
private theorem pr470719 : Nat.Prime 470719 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv23,pv379]) (by decide +kernel)
def pv470719 : PrimeValue := ⟨470719, pr470719⟩
private theorem pr470731 : Nat.Prime 470731 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv13,pv17,pv71]) (by decide +kernel)
def pv470731 : PrimeValue := ⟨470731, pr470731⟩
private theorem pr470749 : Nat.Prime 470749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv39229]) (by decide +kernel)
def pv470749 : PrimeValue := ⟨470749, pr470749⟩
private theorem pr470831 : Nat.Prime 470831 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv5,pv197,pv239]) (by decide +kernel)
def pv470831 : PrimeValue := ⟨470831, pr470831⟩
private theorem pr470881 : Nat.Prime 470881 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv109]) (by decide +kernel)
def pv470881 : PrimeValue := ⟨470881, pr470881⟩
private theorem pr470903 : Nat.Prime 470903 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv23,pv29,pv353]) (by decide +kernel)
def pv470903 : PrimeValue := ⟨470903, pr470903⟩
private theorem pr470993 : Nat.Prime 470993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29437]) (by decide +kernel)
def pv470993 : PrimeValue := ⟨470993, pr470993⟩
private theorem pr470999 : Nat.Prime 470999 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv79,pv271]) (by decide +kernel)
def pv470999 : PrimeValue := ⟨470999, pr470999⟩
private theorem pr471061 : Nat.Prime 471061 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv2617]) (by decide +kernel)
def pv471061 : PrimeValue := ⟨471061, pr471061⟩
private theorem pr471073 : Nat.Prime 471073 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv701]) (by decide +kernel)
def pv471073 : PrimeValue := ⟨471073, pr471073⟩
private theorem pr471187 : Nat.Prime 471187 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv26177]) (by decide +kernel)
def pv471187 : PrimeValue := ⟨471187, pr471187⟩
private theorem pr471193 : Nat.Prime 471193 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29,pv677]) (by decide +kernel)
def pv471193 : PrimeValue := ⟨471193, pr471193⟩
private theorem pr471253 : Nat.Prime 471253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv173,pv227]) (by decide +kernel)
def pv471253 : PrimeValue := ⟨471253, pr471253⟩
private theorem pr471281 : Nat.Prime 471281 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv43,pv137]) (by decide +kernel)
def pv471281 : PrimeValue := ⟨471281, pr471281⟩
private theorem pr471313 : Nat.Prime 471313 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1091]) (by decide +kernel)
def pv471313 : PrimeValue := ⟨471313, pr471313⟩
private theorem pr471389 : Nat.Prime 471389 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv191,pv617]) (by decide +kernel)
def pv471389 : PrimeValue := ⟨471389, pr471389⟩
private theorem pr471403 : Nat.Prime 471403 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv26189]) (by decide +kernel)
def pv471403 : PrimeValue := ⟨471403, pr471403⟩
private theorem pr471439 : Nat.Prime 471439 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv2381]) (by decide +kernel)
def pv471439 : PrimeValue := ⟨471439, pr471439⟩
private theorem pr471481 : Nat.Prime 471481 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv3929]) (by decide +kernel)
def pv471481 : PrimeValue := ⟨471481, pr471481⟩
private theorem pr471487 : Nat.Prime 471487 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv179,pv439]) (by decide +kernel)
def pv471487 : PrimeValue := ⟨471487, pr471487⟩
private theorem pr471521 : Nat.Prime 471521 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv7,pv421]) (by decide +kernel)
def pv471521 : PrimeValue := ⟨471521, pr471521⟩
private theorem pr471539 : Nat.Prime 471539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv5483]) (by decide +kernel)
def pv471539 : PrimeValue := ⟨471539, pr471539⟩
private theorem pr471617 : Nat.Prime 471617 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7369]) (by decide +kernel)
def pv471617 : PrimeValue := ⟨471617, pr471617⟩
private theorem pr471671 : Nat.Prime 471671 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv101,pv467]) (by decide +kernel)
def pv471671 : PrimeValue := ⟨471671, pr471671⟩
private theorem pr471673 : Nat.Prime 471673 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv6551]) (by decide +kernel)
def pv471673 : PrimeValue := ⟨471673, pr471673⟩
private theorem pr471683 : Nat.Prime 471683 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv13873]) (by decide +kernel)
def pv471683 : PrimeValue := ⟨471683, pr471683⟩
private theorem pr471749 : Nat.Prime 471749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv117937]) (by decide +kernel)
def pv471749 : PrimeValue := ⟨471749, pr471749⟩
private theorem pr471893 : Nat.Prime 471893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv117973]) (by decide +kernel)
def pv471893 : PrimeValue := ⟨471893, pr471893⟩
private theorem pr471901 : Nat.Prime 471901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv13]) (by decide +kernel)
def pv471901 : PrimeValue := ⟨471901, pr471901⟩
private theorem pr471923 : Nat.Prime 471923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv19,pv1129]) (by decide +kernel)
def pv471923 : PrimeValue := ⟨471923, pr471923⟩
private theorem pr471943 : Nat.Prime 471943 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv157,pv167]) (by decide +kernel)
def pv471943 : PrimeValue := ⟨471943, pr471943⟩
private theorem pr471949 : Nat.Prime 471949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv67,pv587]) (by decide +kernel)
def pv471949 : PrimeValue := ⟨471949, pr471949⟩
private theorem pr472019 : Nat.Prime 472019 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv53,pv61,pv73]) (by decide +kernel)
def pv472019 : PrimeValue := ⟨472019, pr472019⟩
private theorem pr472027 : Nat.Prime 472027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv151,pv521]) (by decide +kernel)
def pv472027 : PrimeValue := ⟨472027, pr472027⟩
private theorem pr472063 : Nat.Prime 472063 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29,pv2713]) (by decide +kernel)
def pv472063 : PrimeValue := ⟨472063, pr472063⟩
private theorem pr472111 : Nat.Prime 472111 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv15737]) (by decide +kernel)
def pv472111 : PrimeValue := ⟨472111, pr472111⟩
private theorem pr472133 : Nat.Prime 472133 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv118033]) (by decide +kernel)
def pv472133 : PrimeValue := ⟨472133, pr472133⟩
private theorem pr472193 : Nat.Prime 472193 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv17,pv31]) (by decide +kernel)
def pv472193 : PrimeValue := ⟨472193, pr472193⟩
private theorem pr472247 : Nat.Prime 472247 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv389,pv607]) (by decide +kernel)
def pv472247 : PrimeValue := ⟨472247, pr472247⟩
private theorem pr472289 : Nat.Prime 472289 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv14759]) (by decide +kernel)
def pv472289 : PrimeValue := ⟨472289, pr472289⟩
private theorem pr472369 : Nat.Prime 472369 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv13,pv757]) (by decide +kernel)
def pv472369 : PrimeValue := ⟨472369, pr472369⟩
private theorem pr472391 : Nat.Prime 472391 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv97,pv487]) (by decide +kernel)
def pv472391 : PrimeValue := ⟨472391, pr472391⟩
private theorem pr472411 : Nat.Prime 472411 :=
  checkPrime_prime (q := pv47) (ls := [pv2,pv3,pv5,pv29,pv181]) (by decide +kernel)
def pv472411 : PrimeValue := ⟨472411, pr472411⟩
private theorem pr472421 : Nat.Prime 472421 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv23,pv79]) (by decide +kernel)
def pv472421 : PrimeValue := ⟨472421, pr472421⟩
private theorem pr472523 : Nat.Prime 472523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv236261]) (by decide +kernel)
def pv472523 : PrimeValue := ⟨472523, pr472523⟩
private theorem pr472543 : Nat.Prime 472543 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv11251]) (by decide +kernel)
def pv472543 : PrimeValue := ⟨472543, pr472543⟩
private theorem pr472561 : Nat.Prime 472561 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv179]) (by decide +kernel)
def pv472561 : PrimeValue := ⟨472561, pr472561⟩
private theorem pr472573 : Nat.Prime 472573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13127]) (by decide +kernel)
def pv472573 : PrimeValue := ⟨472573, pr472573⟩
private theorem pr472597 : Nat.Prime 472597 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv39383]) (by decide +kernel)
def pv472597 : PrimeValue := ⟨472597, pr472597⟩
private theorem pr472669 : Nat.Prime 472669 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv7,pv17,pv331]) (by decide +kernel)
def pv472669 : PrimeValue := ⟨472669, pr472669⟩
private theorem pr472741 : Nat.Prime 472741 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv7879]) (by decide +kernel)
def pv472741 : PrimeValue := ⟨472741, pr472741⟩
private theorem pr472793 : Nat.Prime 472793 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv113,pv523]) (by decide +kernel)
def pv472793 : PrimeValue := ⟨472793, pr472793⟩
private theorem pr472847 : Nat.Prime 472847 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv21493]) (by decide +kernel)
def pv472847 : PrimeValue := ⟨472847, pr472847⟩
private theorem pr472883 : Nat.Prime 472883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv101,pv2341]) (by decide +kernel)
def pv472883 : PrimeValue := ⟨472883, pr472883⟩
private theorem pr473089 : Nat.Prime 473089 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv7,pv11]) (by decide +kernel)
def pv473089 : PrimeValue := ⟨473089, pr473089⟩
private theorem pr473167 : Nat.Prime 473167 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv97,pv271]) (by decide +kernel)
def pv473167 : PrimeValue := ⟨473167, pr473167⟩
private theorem pr473197 : Nat.Prime 473197 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv47,pv839]) (by decide +kernel)
def pv473197 : PrimeValue := ⟨473197, pr473197⟩
private theorem pr473227 : Nat.Prime 473227 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv6067]) (by decide +kernel)
def pv473227 : PrimeValue := ⟨473227, pr473227⟩
private theorem pr473257 : Nat.Prime 473257 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv313]) (by decide +kernel)
def pv473257 : PrimeValue := ⟨473257, pr473257⟩
private theorem pr473293 : Nat.Prime 473293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13147]) (by decide +kernel)
def pv473293 : PrimeValue := ⟨473293, pr473293⟩
private theorem pr473321 : Nat.Prime 473321 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11833]) (by decide +kernel)
def pv473321 : PrimeValue := ⟨473321, pr473321⟩
private theorem pr473353 : Nat.Prime 473353 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv163]) (by decide +kernel)
def pv473353 : PrimeValue := ⟨473353, pr473353⟩
private theorem pr473377 : Nat.Prime 473377 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv4931]) (by decide +kernel)
def pv473377 : PrimeValue := ⟨473377, pr473377⟩
private theorem pr473383 : Nat.Prime 473383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv17]) (by decide +kernel)
def pv473383 : PrimeValue := ⟨473383, pr473383⟩
private theorem pr473411 : Nat.Prime 473411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv6763]) (by decide +kernel)
def pv473411 : PrimeValue := ⟨473411, pr473411⟩
private theorem pr473441 : Nat.Prime 473441 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv11,pv269]) (by decide +kernel)
def pv473441 : PrimeValue := ⟨473441, pr473441⟩
private theorem pr473471 : Nat.Prime 473471 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv113,pv419]) (by decide +kernel)
def pv473471 : PrimeValue := ⟨473471, pr473471⟩
private theorem pr473479 : Nat.Prime 473479 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv47,pv73]) (by decide +kernel)
def pv473479 : PrimeValue := ⟨473479, pr473479⟩
private theorem pr473503 : Nat.Prime 473503 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv53,pv1489]) (by decide +kernel)
def pv473503 : PrimeValue := ⟨473503, pr473503⟩
private theorem pr473513 : Nat.Prime 473513 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv29,pv157]) (by decide +kernel)
def pv473513 : PrimeValue := ⟨473513, pr473513⟩
private theorem pr473531 : Nat.Prime 473531 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv47353]) (by decide +kernel)
def pv473531 : PrimeValue := ⟨473531, pr473531⟩
private theorem pr473533 : Nat.Prime 473533 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv39461]) (by decide +kernel)
def pv473533 : PrimeValue := ⟨473533, pr473533⟩
private theorem pr473633 : Nat.Prime 473633 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv41]) (by decide +kernel)
def pv473633 : PrimeValue := ⟨473633, pr473633⟩
private theorem pr473741 : Nat.Prime 473741 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23687]) (by decide +kernel)
def pv473741 : PrimeValue := ⟨473741, pr473741⟩
private theorem pr473743 : Nat.Prime 473743 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv31,pv283]) (by decide +kernel)
def pv473743 : PrimeValue := ⟨473743, pr473743⟩
private theorem pr473789 : Nat.Prime 473789 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv16921]) (by decide +kernel)
def pv473789 : PrimeValue := ⟨473789, pr473789⟩
private theorem pr473839 : Nat.Prime 473839 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv151,pv523]) (by decide +kernel)
def pv473839 : PrimeValue := ⟨473839, pr473839⟩
private theorem pr473857 : Nat.Prime 473857 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv617]) (by decide +kernel)
def pv473857 : PrimeValue := ⟨473857, pr473857⟩
private theorem pr473923 : Nat.Prime 473923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv113,pv233]) (by decide +kernel)
def pv473923 : PrimeValue := ⟨473923, pr473923⟩
private theorem pr473981 : Nat.Prime 473981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv1823]) (by decide +kernel)
def pv473981 : PrimeValue := ⟨473981, pr473981⟩
private theorem pr474017 : Nat.Prime 474017 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv14813]) (by decide +kernel)
def pv474017 : PrimeValue := ⟨474017, pr474017⟩
private theorem pr474037 : Nat.Prime 474037 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv39503]) (by decide +kernel)
def pv474037 : PrimeValue := ⟨474037, pr474037⟩
private theorem pr474043 : Nat.Prime 474043 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv41,pv47]) (by decide +kernel)
def pv474043 : PrimeValue := ⟨474043, pr474043⟩
private theorem pr474101 : Nat.Prime 474101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv431]) (by decide +kernel)
def pv474101 : PrimeValue := ⟨474101, pr474101⟩
private theorem pr474143 : Nat.Prime 474143 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv237071]) (by decide +kernel)
def pv474143 : PrimeValue := ⟨474143, pr474143⟩
private theorem pr474169 : Nat.Prime 474169 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv23,pv859]) (by decide +kernel)
def pv474169 : PrimeValue := ⟨474169, pr474169⟩
private theorem pr474223 : Nat.Prime 474223 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv1613]) (by decide +kernel)
def pv474223 : PrimeValue := ⟨474223, pr474223⟩
private theorem pr474307 : Nat.Prime 474307 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv23,pv491]) (by decide +kernel)
def pv474307 : PrimeValue := ⟨474307, pr474307⟩
private theorem pr474319 : Nat.Prime 474319 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv2027]) (by decide +kernel)
def pv474319 : PrimeValue := ⟨474319, pr474319⟩
private theorem pr474347 : Nat.Prime 474347 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv237173]) (by decide +kernel)
def pv474347 : PrimeValue := ⟨474347, pr474347⟩
private theorem pr474379 : Nat.Prime 474379 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv79063]) (by decide +kernel)
def pv474379 : PrimeValue := ⟨474379, pr474379⟩
private theorem pr474413 : Nat.Prime 474413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv118603]) (by decide +kernel)
def pv474413 : PrimeValue := ⟨474413, pr474413⟩
private theorem pr474433 : Nat.Prime 474433 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv353]) (by decide +kernel)
def pv474433 : PrimeValue := ⟨474433, pr474433⟩
private theorem pr474443 : Nat.Prime 474443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv151,pv1571]) (by decide +kernel)
def pv474443 : PrimeValue := ⟨474443, pr474443⟩
private theorem pr474557 : Nat.Prime 474557 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv4091]) (by decide +kernel)
def pv474557 : PrimeValue := ⟨474557, pr474557⟩
private theorem pr474583 : Nat.Prime 474583 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv23,pv181]) (by decide +kernel)
def pv474583 : PrimeValue := ⟨474583, pr474583⟩
private theorem pr474707 : Nat.Prime 474707 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv71,pv3343]) (by decide +kernel)
def pv474707 : PrimeValue := ⟨474707, pr474707⟩
private theorem pr474751 : Nat.Prime 474751 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv211]) (by decide +kernel)
def pv474751 : PrimeValue := ⟨474751, pr474751⟩
private theorem pr474769 : Nat.Prime 474769 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv7,pv157]) (by decide +kernel)
def pv474769 : PrimeValue := ⟨474769, pr474769⟩
private theorem pr474787 : Nat.Prime 474787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv2029]) (by decide +kernel)
def pv474787 : PrimeValue := ⟨474787, pr474787⟩
private theorem pr474941 : Nat.Prime 474941 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23747]) (by decide +kernel)
def pv474941 : PrimeValue := ⟨474941, pr474941⟩
private theorem pr474949 : Nat.Prime 474949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv79,pv167]) (by decide +kernel)
def pv474949 : PrimeValue := ⟨474949, pr474949⟩
private theorem pr474983 : Nat.Prime 474983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv31,pv47,pv163]) (by decide +kernel)
def pv474983 : PrimeValue := ⟨474983, pr474983⟩
private theorem pr475037 : Nat.Prime 475037 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv103,pv1153]) (by decide +kernel)
def pv475037 : PrimeValue := ⟨475037, pr475037⟩
private theorem pr475081 : Nat.Prime 475081 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv37,pv107]) (by decide +kernel)
def pv475081 : PrimeValue := ⟨475081, pr475081⟩
private theorem pr475093 : Nat.Prime 475093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv53,pv83]) (by decide +kernel)
def pv475093 : PrimeValue := ⟨475093, pr475093⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
