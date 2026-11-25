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
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr465643 : PrimeCertificate 465643 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv8623]) (by decide +kernel)
def pv465643 : PrimeValue := ⟨465643, pr465643⟩
private theorem pr465659 : PrimeCertificate 465659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv53,pv191]) (by decide +kernel)
def pv465659 : PrimeValue := ⟨465659, pr465659⟩
private theorem pr465739 : PrimeCertificate 465739 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv853]) (by decide +kernel)
def pv465739 : PrimeValue := ⟨465739, pr465739⟩
private theorem pr465743 : PrimeCertificate 465743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv232871]) (by decide +kernel)
def pv465743 : PrimeValue := ⟨465743, pr465743⟩
private theorem pr465761 : PrimeCertificate 465761 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv41,pv71]) (by decide +kernel)
def pv465761 : PrimeValue := ⟨465761, pr465761⟩
private theorem pr465841 : PrimeCertificate 465841 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv647]) (by decide +kernel)
def pv465841 : PrimeValue := ⟨465841, pr465841⟩
private theorem pr465887 : PrimeCertificate 465887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv73,pv3191]) (by decide +kernel)
def pv465887 : PrimeValue := ⟨465887, pr465887⟩
private theorem pr465929 : PrimeCertificate 465929 :=
  certifyPrime (q := pv3) (ls := [pv2,pv139,pv419]) (by decide +kernel)
def pv465929 : PrimeValue := ⟨465929, pr465929⟩
private theorem pr466019 : PrimeCertificate 466019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv33287]) (by decide +kernel)
def pv466019 : PrimeValue := ⟨466019, pr466019⟩
private theorem pr466027 : PrimeCertificate 466027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv23,pv307]) (by decide +kernel)
def pv466027 : PrimeValue := ⟨466027, pr466027⟩
private theorem pr466043 : PrimeCertificate 466043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv233021]) (by decide +kernel)
def pv466043 : PrimeValue := ⟨466043, pr466043⟩
private theorem pr466087 : PrimeCertificate 466087 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv77681]) (by decide +kernel)
def pv466087 : PrimeValue := ⟨466087, pr466087⟩
private theorem pr466153 : PrimeCertificate 466153 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19423]) (by decide +kernel)
def pv466153 : PrimeValue := ⟨466153, pr466153⟩
private theorem pr466261 : PrimeCertificate 466261 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv19,pv409]) (by decide +kernel)
def pv466261 : PrimeValue := ⟨466261, pr466261⟩
private theorem pr466267 : PrimeCertificate 466267 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv77711]) (by decide +kernel)
def pv466267 : PrimeValue := ⟨466267, pr466267⟩
private theorem pr466283 : PrimeCertificate 466283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv233141]) (by decide +kernel)
def pv466283 : PrimeValue := ⟨466283, pr466283⟩
private theorem pr466303 : PrimeCertificate 466303 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv31,pv109]) (by decide +kernel)
def pv466303 : PrimeValue := ⟨466303, pr466303⟩
private theorem pr466331 : PrimeCertificate 466331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv46633]) (by decide +kernel)
def pv466331 : PrimeValue := ⟨466331, pr466331⟩
private theorem pr466357 : PrimeCertificate 466357 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv3533]) (by decide +kernel)
def pv466357 : PrimeValue := ⟨466357, pr466357⟩
private theorem pr466409 : PrimeCertificate 466409 :=
  certifyPrime (q := pv3) (ls := [pv2,pv173,pv337]) (by decide +kernel)
def pv466409 : PrimeValue := ⟨466409, pr466409⟩
private theorem pr466423 : PrimeCertificate 466423 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv37,pv191]) (by decide +kernel)
def pv466423 : PrimeValue := ⟨466423, pr466423⟩
private theorem pr466441 : PrimeCertificate 466441 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv13,pv23]) (by decide +kernel)
def pv466441 : PrimeValue := ⟨466441, pr466441⟩
private theorem pr466451 : PrimeCertificate 466451 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv491]) (by decide +kernel)
def pv466451 : PrimeValue := ⟨466451, pr466451⟩
private theorem pr466483 : PrimeCertificate 466483 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv77747]) (by decide +kernel)
def pv466483 : PrimeValue := ⟨466483, pr466483⟩
private theorem pr466517 : PrimeCertificate 466517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv223,pv523]) (by decide +kernel)
def pv466517 : PrimeValue := ⟨466517, pr466517⟩
private theorem pr466567 : PrimeCertificate 466567 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv77761]) (by decide +kernel)
def pv466567 : PrimeValue := ⟨466567, pr466567⟩
private theorem pr466717 : PrimeCertificate 466717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv23,pv89]) (by decide +kernel)
def pv466717 : PrimeValue := ⟨466717, pr466717⟩
private theorem pr466723 : PrimeCertificate 466723 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv43,pv67]) (by decide +kernel)
def pv466723 : PrimeValue := ⟨466723, pr466723⟩
private theorem pr466747 : PrimeCertificate 466747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11113]) (by decide +kernel)
def pv466747 : PrimeValue := ⟨466747, pr466747⟩
private theorem pr466751 : PrimeCertificate 466751 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv1867]) (by decide +kernel)
def pv466751 : PrimeValue := ⟨466751, pr466751⟩
private theorem pr466777 : PrimeCertificate 466777 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2161]) (by decide +kernel)
def pv466777 : PrimeValue := ⟨466777, pr466777⟩
private theorem pr466853 : PrimeCertificate 466853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv127,pv919]) (by decide +kernel)
def pv466853 : PrimeValue := ⟨466853, pr466853⟩
private theorem pr466913 : PrimeCertificate 466913 :=
  certifyPrime (q := pv3) (ls := [pv2,pv14591]) (by decide +kernel)
def pv466913 : PrimeValue := ⟨466913, pr466913⟩
private theorem pr466919 : PrimeCertificate 466919 :=
  certifyPrime (q := pv13) (ls := [pv2,pv157,pv1487]) (by decide +kernel)
def pv466919 : PrimeValue := ⟨466919, pr466919⟩
private theorem pr466951 : PrimeCertificate 466951 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv283]) (by decide +kernel)
def pv466951 : PrimeValue := ⟨466951, pr466951⟩
private theorem pr467063 : PrimeCertificate 467063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv347,pv673]) (by decide +kernel)
def pv467063 : PrimeValue := ⟨467063, pr467063⟩
private theorem pr467081 : PrimeCertificate 467081 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11677]) (by decide +kernel)
def pv467081 : PrimeValue := ⟨467081, pr467081⟩
private theorem pr467083 : PrimeCertificate 467083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv337]) (by decide +kernel)
def pv467083 : PrimeValue := ⟨467083, pr467083⟩
private theorem pr467141 : PrimeCertificate 467141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23357]) (by decide +kernel)
def pv467141 : PrimeValue := ⟨467141, pr467141⟩
private theorem pr467171 : PrimeCertificate 467171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv31,pv137]) (by decide +kernel)
def pv467171 : PrimeValue := ⟨467171, pr467171⟩
private theorem pr467197 : PrimeCertificate 467197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv38933]) (by decide +kernel)
def pv467197 : PrimeValue := ⟨467197, pr467197⟩
private theorem pr467209 : PrimeCertificate 467209 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv103]) (by decide +kernel)
def pv467209 : PrimeValue := ⟨467209, pr467209⟩
private theorem pr467261 : PrimeCertificate 467261 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv61,pv383]) (by decide +kernel)
def pv467261 : PrimeValue := ⟨467261, pr467261⟩
private theorem pr467293 : PrimeCertificate 467293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv5563]) (by decide +kernel)
def pv467293 : PrimeValue := ⟨467293, pr467293⟩
private theorem pr467297 : PrimeCertificate 467297 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv859]) (by decide +kernel)
def pv467297 : PrimeValue := ⟨467297, pr467297⟩
private theorem pr467317 : PrimeCertificate 467317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv4327]) (by decide +kernel)
def pv467317 : PrimeValue := ⟨467317, pr467317⟩
private theorem pr467371 : PrimeCertificate 467371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv577]) (by decide +kernel)
def pv467371 : PrimeValue := ⟨467371, pr467371⟩
private theorem pr467399 : PrimeCertificate 467399 :=
  certifyPrime (q := pv7) (ls := [pv2,pv17,pv59,pv233]) (by decide +kernel)
def pv467399 : PrimeValue := ⟨467399, pr467399⟩
private theorem pr467471 : PrimeCertificate 467471 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv46747]) (by decide +kernel)
def pv467471 : PrimeValue := ⟨467471, pr467471⟩
private theorem pr467473 : PrimeCertificate 467473 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv9739]) (by decide +kernel)
def pv467473 : PrimeValue := ⟨467473, pr467473⟩
private theorem pr467507 : PrimeCertificate 467507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv17981]) (by decide +kernel)
def pv467507 : PrimeValue := ⟨467507, pr467507⟩
private theorem pr467527 : PrimeCertificate 467527 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv67,pv1163]) (by decide +kernel)
def pv467527 : PrimeValue := ⟨467527, pr467527⟩
private theorem pr467531 : PrimeCertificate 467531 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv6679]) (by decide +kernel)
def pv467531 : PrimeValue := ⟨467531, pr467531⟩
private theorem pr467543 : PrimeCertificate 467543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv31,pv7541]) (by decide +kernel)
def pv467543 : PrimeValue := ⟨467543, pr467543⟩
private theorem pr467557 : PrimeCertificate 467557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv829]) (by decide +kernel)
def pv467557 : PrimeValue := ⟨467557, pr467557⟩
private theorem pr467591 : PrimeCertificate 467591 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv19,pv23,pv107]) (by decide +kernel)
def pv467591 : PrimeValue := ⟨467591, pr467591⟩
private theorem pr467617 : PrimeCertificate 467617 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4871]) (by decide +kernel)
def pv467617 : PrimeValue := ⟨467617, pr467617⟩
private theorem pr467627 : PrimeCertificate 467627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv3833]) (by decide +kernel)
def pv467627 : PrimeValue := ⟨467627, pr467627⟩
private theorem pr467651 : PrimeCertificate 467651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv47,pv199]) (by decide +kernel)
def pv467651 : PrimeValue := ⟨467651, pr467651⟩
private theorem pr467669 : PrimeCertificate 467669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv2719]) (by decide +kernel)
def pv467669 : PrimeValue := ⟨467669, pr467669⟩
private theorem pr467681 : PrimeCertificate 467681 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv37,pv79]) (by decide +kernel)
def pv467681 : PrimeValue := ⟨467681, pr467681⟩
private theorem pr467699 : PrimeCertificate 467699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv3037]) (by decide +kernel)
def pv467699 : PrimeValue := ⟨467699, pr467699⟩
private theorem pr467713 : PrimeCertificate 467713 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv29]) (by decide +kernel)
def pv467713 : PrimeValue := ⟨467713, pr467713⟩
private theorem pr467743 : PrimeCertificate 467743 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv19,pv373]) (by decide +kernel)
def pv467743 : PrimeValue := ⟨467743, pr467743⟩
private theorem pr467827 : PrimeCertificate 467827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv103,pv757]) (by decide +kernel)
def pv467827 : PrimeValue := ⟨467827, pr467827⟩
private theorem pr467869 : PrimeCertificate 467869 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv127,pv307]) (by decide +kernel)
def pv467869 : PrimeValue := ⟨467869, pr467869⟩
private theorem pr467953 : PrimeCertificate 467953 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv9749]) (by decide +kernel)
def pv467953 : PrimeValue := ⟨467953, pr467953⟩
private theorem pr468001 : PrimeCertificate 468001 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv468001 : PrimeValue := ⟨468001, pr468001⟩
private theorem pr468059 : PrimeCertificate 468059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv234029]) (by decide +kernel)
def pv468059 : PrimeValue := ⟨468059, pr468059⟩
private theorem pr468071 : PrimeCertificate 468071 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv46807]) (by decide +kernel)
def pv468071 : PrimeValue := ⟨468071, pr468071⟩
private theorem pr468113 : PrimeCertificate 468113 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv1721]) (by decide +kernel)
def pv468113 : PrimeValue := ⟨468113, pr468113⟩
private theorem pr468253 : PrimeCertificate 468253 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13007]) (by decide +kernel)
def pv468253 : PrimeValue := ⟨468253, pr468253⟩
private theorem pr468271 : PrimeCertificate 468271 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv43]) (by decide +kernel)
def pv468271 : PrimeValue := ⟨468271, pr468271⟩
private theorem pr468323 : PrimeCertificate 468323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv234161]) (by decide +kernel)
def pv468323 : PrimeValue := ⟨468323, pr468323⟩
private theorem pr468389 : PrimeCertificate 468389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv6163]) (by decide +kernel)
def pv468389 : PrimeValue := ⟨468389, pr468389⟩
private theorem pr468451 : PrimeCertificate 468451 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv347]) (by decide +kernel)
def pv468451 : PrimeValue := ⟨468451, pr468451⟩
private theorem pr468493 : PrimeCertificate 468493 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv39041]) (by decide +kernel)
def pv468493 : PrimeValue := ⟨468493, pr468493⟩
private theorem pr468527 : PrimeCertificate 468527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv317,pv739]) (by decide +kernel)
def pv468527 : PrimeValue := ⟨468527, pr468527⟩
private theorem pr468557 : PrimeCertificate 468557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv23,pv463]) (by decide +kernel)
def pv468557 : PrimeValue := ⟨468557, pr468557⟩
private theorem pr468593 : PrimeCertificate 468593 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29287]) (by decide +kernel)
def pv468593 : PrimeValue := ⟨468593, pr468593⟩
private theorem pr468647 : PrimeCertificate 468647 :=
  certifyPrime (q := pv5) (ls := [pv2,pv234323]) (by decide +kernel)
def pv468647 : PrimeValue := ⟨468647, pr468647⟩
private theorem pr468667 : PrimeCertificate 468667 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv263]) (by decide +kernel)
def pv468667 : PrimeValue := ⟨468667, pr468667⟩
private theorem pr468683 : PrimeCertificate 468683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv234341]) (by decide +kernel)
def pv468683 : PrimeValue := ⟨468683, pr468683⟩
private theorem pr468703 : PrimeCertificate 468703 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv2003]) (by decide +kernel)
def pv468703 : PrimeValue := ⟨468703, pr468703⟩
private theorem pr468709 : PrimeCertificate 468709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv139,pv281]) (by decide +kernel)
def pv468709 : PrimeValue := ⟨468709, pr468709⟩
private theorem pr468737 : PrimeCertificate 468737 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1831]) (by decide +kernel)
def pv468737 : PrimeValue := ⟨468737, pr468737⟩
private theorem pr468773 : PrimeCertificate 468773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv117193]) (by decide +kernel)
def pv468773 : PrimeValue := ⟨468773, pr468773⟩
private theorem pr468781 : PrimeCertificate 468781 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv13,pv601]) (by decide +kernel)
def pv468781 : PrimeValue := ⟨468781, pr468781⟩
private theorem pr468803 : PrimeCertificate 468803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv157,pv1493]) (by decide +kernel)
def pv468803 : PrimeValue := ⟨468803, pr468803⟩
private theorem pr468841 : PrimeCertificate 468841 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv3907]) (by decide +kernel)
def pv468841 : PrimeValue := ⟨468841, pr468841⟩
private theorem pr468883 : PrimeCertificate 468883 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv457]) (by decide +kernel)
def pv468883 : PrimeValue := ⟨468883, pr468883⟩
private theorem pr468887 : PrimeCertificate 468887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv21313]) (by decide +kernel)
def pv468887 : PrimeValue := ⟨468887, pr468887⟩
private theorem pr468889 : PrimeCertificate 468889 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv7,pv2791]) (by decide +kernel)
def pv468889 : PrimeValue := ⟨468889, pr468889⟩
private theorem pr468913 : PrimeCertificate 468913 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv9769]) (by decide +kernel)
def pv468913 : PrimeValue := ⟨468913, pr468913⟩
private theorem pr468953 : PrimeCertificate 468953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv73]) (by decide +kernel)
def pv468953 : PrimeValue := ⟨468953, pr468953⟩
private theorem pr468967 : PrimeCertificate 468967 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv47,pv1663]) (by decide +kernel)
def pv468967 : PrimeValue := ⟨468967, pr468967⟩
private theorem pr468973 : PrimeCertificate 468973 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv1861]) (by decide +kernel)
def pv468973 : PrimeValue := ⟨468973, pr468973⟩
private theorem pr469121 : PrimeCertificate 469121 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv733]) (by decide +kernel)
def pv469121 : PrimeValue := ⟨469121, pr469121⟩
private theorem pr469193 : PrimeCertificate 469193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv223,pv263]) (by decide +kernel)
def pv469193 : PrimeValue := ⟨469193, pr469193⟩
private theorem pr469207 : PrimeCertificate 469207 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv8689]) (by decide +kernel)
def pv469207 : PrimeValue := ⟨469207, pr469207⟩
private theorem pr469229 : PrimeCertificate 469229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv117307]) (by decide +kernel)
def pv469229 : PrimeValue := ⟨469229, pr469229⟩
private theorem pr469237 : PrimeCertificate 469237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv39103]) (by decide +kernel)
def pv469237 : PrimeValue := ⟨469237, pr469237⟩
private theorem pr469241 : PrimeCertificate 469241 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11731]) (by decide +kernel)
def pv469241 : PrimeValue := ⟨469241, pr469241⟩
private theorem pr469253 : PrimeCertificate 469253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv16759]) (by decide +kernel)
def pv469253 : PrimeValue := ⟨469253, pr469253⟩
private theorem pr469267 : PrimeCertificate 469267 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11173]) (by decide +kernel)
def pv469267 : PrimeValue := ⟨469267, pr469267⟩
private theorem pr469321 : PrimeCertificate 469321 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv3911]) (by decide +kernel)
def pv469321 : PrimeValue := ⟨469321, pr469321⟩
private theorem pr469429 : PrimeCertificate 469429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv39119]) (by decide +kernel)
def pv469429 : PrimeValue := ⟨469429, pr469429⟩
private theorem pr469439 : PrimeCertificate 469439 :=
  certifyPrime (q := pv11) (ls := [pv2,pv17,pv13807]) (by decide +kernel)
def pv469439 : PrimeValue := ⟨469439, pr469439⟩
private theorem pr469501 : PrimeCertificate 469501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv313]) (by decide +kernel)
def pv469501 : PrimeValue := ⟨469501, pr469501⟩
private theorem pr469543 : PrimeCertificate 469543 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv139,pv563]) (by decide +kernel)
def pv469543 : PrimeValue := ⟨469543, pr469543⟩
private theorem pr469583 : PrimeCertificate 469583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv234791]) (by decide +kernel)
def pv469583 : PrimeValue := ⟨469583, pr469583⟩
private theorem pr469589 : PrimeCertificate 469589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv31,pv541]) (by decide +kernel)
def pv469589 : PrimeValue := ⟨469589, pr469589⟩
private theorem pr469649 : PrimeCertificate 469649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv149,pv197]) (by decide +kernel)
def pv469649 : PrimeValue := ⟨469649, pr469649⟩
private theorem pr469657 : PrimeCertificate 469657 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv593]) (by decide +kernel)
def pv469657 : PrimeValue := ⟨469657, pr469657⟩
private theorem pr469673 : PrimeCertificate 469673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv8387]) (by decide +kernel)
def pv469673 : PrimeValue := ⟨469673, pr469673⟩
private theorem pr469691 : PrimeCertificate 469691 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv13,pv3613]) (by decide +kernel)
def pv469691 : PrimeValue := ⟨469691, pr469691⟩
private theorem pr469717 : PrimeCertificate 469717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv3011]) (by decide +kernel)
def pv469717 : PrimeValue := ⟨469717, pr469717⟩
private theorem pr469811 : PrimeCertificate 469811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv4271]) (by decide +kernel)
def pv469811 : PrimeValue := ⟨469811, pr469811⟩
private theorem pr469823 : PrimeCertificate 469823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv61,pv3851]) (by decide +kernel)
def pv469823 : PrimeValue := ⟨469823, pr469823⟩
private theorem pr469879 : PrimeCertificate 469879 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv71,pv1103]) (by decide +kernel)
def pv469879 : PrimeValue := ⟨469879, pr469879⟩
private theorem pr469891 : PrimeCertificate 469891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv23,pv227]) (by decide +kernel)
def pv469891 : PrimeValue := ⟨469891, pr469891⟩
private theorem pr469919 : PrimeCertificate 469919 :=
  certifyPrime (q := pv7) (ls := [pv2,pv234959]) (by decide +kernel)
def pv469919 : PrimeValue := ⟨469919, pr469919⟩
private theorem pr469957 : PrimeCertificate 469957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv39163]) (by decide +kernel)
def pv469957 : PrimeValue := ⟨469957, pr469957⟩
private theorem pr469993 : PrimeCertificate 469993 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19583]) (by decide +kernel)
def pv469993 : PrimeValue := ⟨469993, pr469993⟩
private theorem pr470021 : PrimeCertificate 470021 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv71,pv331]) (by decide +kernel)
def pv470021 : PrimeValue := ⟨470021, pr470021⟩
private theorem pr470077 : PrimeCertificate 470077 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv43,pv911]) (by decide +kernel)
def pv470077 : PrimeValue := ⟨470077, pr470077⟩
private theorem pr470089 : PrimeCertificate 470089 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv6529]) (by decide +kernel)
def pv470089 : PrimeValue := ⟨470089, pr470089⟩
private theorem pr470131 : PrimeCertificate 470131 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv15671]) (by decide +kernel)
def pv470131 : PrimeValue := ⟨470131, pr470131⟩
private theorem pr470149 : PrimeCertificate 470149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv29,pv193]) (by decide +kernel)
def pv470149 : PrimeValue := ⟨470149, pr470149⟩
private theorem pr470153 : PrimeCertificate 470153 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv3457]) (by decide +kernel)
def pv470153 : PrimeValue := ⟨470153, pr470153⟩
private theorem pr470201 : PrimeCertificate 470201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv2351]) (by decide +kernel)
def pv470201 : PrimeValue := ⟨470201, pr470201⟩
private theorem pr470227 : PrimeCertificate 470227 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv109,pv719]) (by decide +kernel)
def pv470227 : PrimeValue := ⟨470227, pr470227⟩
private theorem pr470243 : PrimeCertificate 470243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv191,pv1231]) (by decide +kernel)
def pv470243 : PrimeValue := ⟨470243, pr470243⟩
private theorem pr470299 : PrimeCertificate 470299 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv103,pv761]) (by decide +kernel)
def pv470299 : PrimeValue := ⟨470299, pr470299⟩
private theorem pr470303 : PrimeCertificate 470303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv4799]) (by decide +kernel)
def pv470303 : PrimeValue := ⟨470303, pr470303⟩
private theorem pr470333 : PrimeCertificate 470333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv3793]) (by decide +kernel)
def pv470333 : PrimeValue := ⟨470333, pr470333⟩
private theorem pr470347 : PrimeCertificate 470347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv277,pv283]) (by decide +kernel)
def pv470347 : PrimeValue := ⟨470347, pr470347⟩
private theorem pr470417 : PrimeCertificate 470417 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29401]) (by decide +kernel)
def pv470417 : PrimeValue := ⟨470417, pr470417⟩
private theorem pr470453 : PrimeCertificate 470453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv337,pv349]) (by decide +kernel)
def pv470453 : PrimeValue := ⟨470453, pr470453⟩
private theorem pr470513 : PrimeCertificate 470513 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv4201]) (by decide +kernel)
def pv470513 : PrimeValue := ⟨470513, pr470513⟩
private theorem pr470579 : PrimeCertificate 470579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv235289]) (by decide +kernel)
def pv470579 : PrimeValue := ⟨470579, pr470579⟩
private theorem pr470593 : PrimeCertificate 470593 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv19,pv43]) (by decide +kernel)
def pv470593 : PrimeValue := ⟨470593, pr470593⟩
private theorem pr470627 : PrimeCertificate 470627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv23,pv787]) (by decide +kernel)
def pv470627 : PrimeValue := ⟨470627, pr470627⟩
private theorem pr470647 : PrimeCertificate 470647 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv2377]) (by decide +kernel)
def pv470647 : PrimeValue := ⟨470647, pr470647⟩
private theorem pr470719 : PrimeCertificate 470719 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23,pv379]) (by decide +kernel)
def pv470719 : PrimeValue := ⟨470719, pr470719⟩
private theorem pr470731 : PrimeCertificate 470731 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv13,pv17,pv71]) (by decide +kernel)
def pv470731 : PrimeValue := ⟨470731, pr470731⟩
private theorem pr470749 : PrimeCertificate 470749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv39229]) (by decide +kernel)
def pv470749 : PrimeValue := ⟨470749, pr470749⟩
private theorem pr470831 : PrimeCertificate 470831 :=
  certifyPrime (q := pv37) (ls := [pv2,pv5,pv197,pv239]) (by decide +kernel)
def pv470831 : PrimeValue := ⟨470831, pr470831⟩
private theorem pr470881 : PrimeCertificate 470881 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv109]) (by decide +kernel)
def pv470881 : PrimeValue := ⟨470881, pr470881⟩
private theorem pr470903 : PrimeCertificate 470903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv29,pv353]) (by decide +kernel)
def pv470903 : PrimeValue := ⟨470903, pr470903⟩
private theorem pr470993 : PrimeCertificate 470993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29437]) (by decide +kernel)
def pv470993 : PrimeValue := ⟨470993, pr470993⟩
private theorem pr470999 : PrimeCertificate 470999 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv79,pv271]) (by decide +kernel)
def pv470999 : PrimeValue := ⟨470999, pr470999⟩
private theorem pr471061 : PrimeCertificate 471061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv2617]) (by decide +kernel)
def pv471061 : PrimeValue := ⟨471061, pr471061⟩
private theorem pr471073 : PrimeCertificate 471073 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv701]) (by decide +kernel)
def pv471073 : PrimeValue := ⟨471073, pr471073⟩
private theorem pr471187 : PrimeCertificate 471187 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv26177]) (by decide +kernel)
def pv471187 : PrimeValue := ⟨471187, pr471187⟩
private theorem pr471193 : PrimeCertificate 471193 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29,pv677]) (by decide +kernel)
def pv471193 : PrimeValue := ⟨471193, pr471193⟩
private theorem pr471253 : PrimeCertificate 471253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv173,pv227]) (by decide +kernel)
def pv471253 : PrimeValue := ⟨471253, pr471253⟩
private theorem pr471281 : PrimeCertificate 471281 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv43,pv137]) (by decide +kernel)
def pv471281 : PrimeValue := ⟨471281, pr471281⟩
private theorem pr471313 : PrimeCertificate 471313 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1091]) (by decide +kernel)
def pv471313 : PrimeValue := ⟨471313, pr471313⟩
private theorem pr471389 : PrimeCertificate 471389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv191,pv617]) (by decide +kernel)
def pv471389 : PrimeValue := ⟨471389, pr471389⟩
private theorem pr471403 : PrimeCertificate 471403 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv26189]) (by decide +kernel)
def pv471403 : PrimeValue := ⟨471403, pr471403⟩
private theorem pr471439 : PrimeCertificate 471439 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv2381]) (by decide +kernel)
def pv471439 : PrimeValue := ⟨471439, pr471439⟩
private theorem pr471481 : PrimeCertificate 471481 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv3929]) (by decide +kernel)
def pv471481 : PrimeValue := ⟨471481, pr471481⟩
private theorem pr471487 : PrimeCertificate 471487 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv179,pv439]) (by decide +kernel)
def pv471487 : PrimeValue := ⟨471487, pr471487⟩
private theorem pr471521 : PrimeCertificate 471521 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv421]) (by decide +kernel)
def pv471521 : PrimeValue := ⟨471521, pr471521⟩
private theorem pr471539 : PrimeCertificate 471539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv5483]) (by decide +kernel)
def pv471539 : PrimeValue := ⟨471539, pr471539⟩
private theorem pr471617 : PrimeCertificate 471617 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7369]) (by decide +kernel)
def pv471617 : PrimeValue := ⟨471617, pr471617⟩
private theorem pr471671 : PrimeCertificate 471671 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv101,pv467]) (by decide +kernel)
def pv471671 : PrimeValue := ⟨471671, pr471671⟩
private theorem pr471673 : PrimeCertificate 471673 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv6551]) (by decide +kernel)
def pv471673 : PrimeValue := ⟨471673, pr471673⟩
private theorem pr471683 : PrimeCertificate 471683 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv13873]) (by decide +kernel)
def pv471683 : PrimeValue := ⟨471683, pr471683⟩
private theorem pr471749 : PrimeCertificate 471749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv117937]) (by decide +kernel)
def pv471749 : PrimeValue := ⟨471749, pr471749⟩
private theorem pr471893 : PrimeCertificate 471893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv117973]) (by decide +kernel)
def pv471893 : PrimeValue := ⟨471893, pr471893⟩
private theorem pr471901 : PrimeCertificate 471901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv13]) (by decide +kernel)
def pv471901 : PrimeValue := ⟨471901, pr471901⟩
private theorem pr471923 : PrimeCertificate 471923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv19,pv1129]) (by decide +kernel)
def pv471923 : PrimeValue := ⟨471923, pr471923⟩
private theorem pr471943 : PrimeCertificate 471943 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv157,pv167]) (by decide +kernel)
def pv471943 : PrimeValue := ⟨471943, pr471943⟩
private theorem pr471949 : PrimeCertificate 471949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv67,pv587]) (by decide +kernel)
def pv471949 : PrimeValue := ⟨471949, pr471949⟩
private theorem pr472019 : PrimeCertificate 472019 :=
  certifyPrime (q := pv7) (ls := [pv2,pv53,pv61,pv73]) (by decide +kernel)
def pv472019 : PrimeValue := ⟨472019, pr472019⟩
private theorem pr472027 : PrimeCertificate 472027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv151,pv521]) (by decide +kernel)
def pv472027 : PrimeValue := ⟨472027, pr472027⟩
private theorem pr472063 : PrimeCertificate 472063 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv2713]) (by decide +kernel)
def pv472063 : PrimeValue := ⟨472063, pr472063⟩
private theorem pr472111 : PrimeCertificate 472111 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv15737]) (by decide +kernel)
def pv472111 : PrimeValue := ⟨472111, pr472111⟩
private theorem pr472133 : PrimeCertificate 472133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv118033]) (by decide +kernel)
def pv472133 : PrimeValue := ⟨472133, pr472133⟩
private theorem pr472193 : PrimeCertificate 472193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv17,pv31]) (by decide +kernel)
def pv472193 : PrimeValue := ⟨472193, pr472193⟩
private theorem pr472247 : PrimeCertificate 472247 :=
  certifyPrime (q := pv5) (ls := [pv2,pv389,pv607]) (by decide +kernel)
def pv472247 : PrimeValue := ⟨472247, pr472247⟩
private theorem pr472289 : PrimeCertificate 472289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv14759]) (by decide +kernel)
def pv472289 : PrimeValue := ⟨472289, pr472289⟩
private theorem pr472369 : PrimeCertificate 472369 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv13,pv757]) (by decide +kernel)
def pv472369 : PrimeValue := ⟨472369, pr472369⟩
private theorem pr472391 : PrimeCertificate 472391 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv97,pv487]) (by decide +kernel)
def pv472391 : PrimeValue := ⟨472391, pr472391⟩
private theorem pr472411 : PrimeCertificate 472411 :=
  certifyPrime (q := pv47) (ls := [pv2,pv3,pv5,pv29,pv181]) (by decide +kernel)
def pv472411 : PrimeValue := ⟨472411, pr472411⟩
private theorem pr472421 : PrimeCertificate 472421 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv23,pv79]) (by decide +kernel)
def pv472421 : PrimeValue := ⟨472421, pr472421⟩
private theorem pr472523 : PrimeCertificate 472523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv236261]) (by decide +kernel)
def pv472523 : PrimeValue := ⟨472523, pr472523⟩
private theorem pr472543 : PrimeCertificate 472543 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv11251]) (by decide +kernel)
def pv472543 : PrimeValue := ⟨472543, pr472543⟩
private theorem pr472561 : PrimeCertificate 472561 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv179]) (by decide +kernel)
def pv472561 : PrimeValue := ⟨472561, pr472561⟩
private theorem pr472573 : PrimeCertificate 472573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13127]) (by decide +kernel)
def pv472573 : PrimeValue := ⟨472573, pr472573⟩
private theorem pr472597 : PrimeCertificate 472597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv39383]) (by decide +kernel)
def pv472597 : PrimeValue := ⟨472597, pr472597⟩
private theorem pr472669 : PrimeCertificate 472669 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv7,pv17,pv331]) (by decide +kernel)
def pv472669 : PrimeValue := ⟨472669, pr472669⟩
private theorem pr472741 : PrimeCertificate 472741 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7879]) (by decide +kernel)
def pv472741 : PrimeValue := ⟨472741, pr472741⟩
private theorem pr472793 : PrimeCertificate 472793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv113,pv523]) (by decide +kernel)
def pv472793 : PrimeValue := ⟨472793, pr472793⟩
private theorem pr472847 : PrimeCertificate 472847 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv21493]) (by decide +kernel)
def pv472847 : PrimeValue := ⟨472847, pr472847⟩
private theorem pr472883 : PrimeCertificate 472883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv101,pv2341]) (by decide +kernel)
def pv472883 : PrimeValue := ⟨472883, pr472883⟩
private theorem pr473089 : PrimeCertificate 473089 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv7,pv11]) (by decide +kernel)
def pv473089 : PrimeValue := ⟨473089, pr473089⟩
private theorem pr473167 : PrimeCertificate 473167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv97,pv271]) (by decide +kernel)
def pv473167 : PrimeValue := ⟨473167, pr473167⟩
private theorem pr473197 : PrimeCertificate 473197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv839]) (by decide +kernel)
def pv473197 : PrimeValue := ⟨473197, pr473197⟩
private theorem pr473227 : PrimeCertificate 473227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv6067]) (by decide +kernel)
def pv473227 : PrimeValue := ⟨473227, pr473227⟩
private theorem pr473257 : PrimeCertificate 473257 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv313]) (by decide +kernel)
def pv473257 : PrimeValue := ⟨473257, pr473257⟩
private theorem pr473293 : PrimeCertificate 473293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13147]) (by decide +kernel)
def pv473293 : PrimeValue := ⟨473293, pr473293⟩
private theorem pr473321 : PrimeCertificate 473321 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11833]) (by decide +kernel)
def pv473321 : PrimeValue := ⟨473321, pr473321⟩
private theorem pr473353 : PrimeCertificate 473353 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv163]) (by decide +kernel)
def pv473353 : PrimeValue := ⟨473353, pr473353⟩
private theorem pr473377 : PrimeCertificate 473377 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4931]) (by decide +kernel)
def pv473377 : PrimeValue := ⟨473377, pr473377⟩
private theorem pr473383 : PrimeCertificate 473383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv17]) (by decide +kernel)
def pv473383 : PrimeValue := ⟨473383, pr473383⟩
private theorem pr473411 : PrimeCertificate 473411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv6763]) (by decide +kernel)
def pv473411 : PrimeValue := ⟨473411, pr473411⟩
private theorem pr473441 : PrimeCertificate 473441 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv11,pv269]) (by decide +kernel)
def pv473441 : PrimeValue := ⟨473441, pr473441⟩
private theorem pr473471 : PrimeCertificate 473471 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv113,pv419]) (by decide +kernel)
def pv473471 : PrimeValue := ⟨473471, pr473471⟩
private theorem pr473479 : PrimeCertificate 473479 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv47,pv73]) (by decide +kernel)
def pv473479 : PrimeValue := ⟨473479, pr473479⟩
private theorem pr473503 : PrimeCertificate 473503 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv53,pv1489]) (by decide +kernel)
def pv473503 : PrimeValue := ⟨473503, pr473503⟩
private theorem pr473513 : PrimeCertificate 473513 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv29,pv157]) (by decide +kernel)
def pv473513 : PrimeValue := ⟨473513, pr473513⟩
private theorem pr473531 : PrimeCertificate 473531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv47353]) (by decide +kernel)
def pv473531 : PrimeValue := ⟨473531, pr473531⟩
private theorem pr473533 : PrimeCertificate 473533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv39461]) (by decide +kernel)
def pv473533 : PrimeValue := ⟨473533, pr473533⟩
private theorem pr473633 : PrimeCertificate 473633 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv41]) (by decide +kernel)
def pv473633 : PrimeValue := ⟨473633, pr473633⟩
private theorem pr473741 : PrimeCertificate 473741 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23687]) (by decide +kernel)
def pv473741 : PrimeValue := ⟨473741, pr473741⟩
private theorem pr473743 : PrimeCertificate 473743 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31,pv283]) (by decide +kernel)
def pv473743 : PrimeValue := ⟨473743, pr473743⟩
private theorem pr473789 : PrimeCertificate 473789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv16921]) (by decide +kernel)
def pv473789 : PrimeValue := ⟨473789, pr473789⟩
private theorem pr473839 : PrimeCertificate 473839 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv151,pv523]) (by decide +kernel)
def pv473839 : PrimeValue := ⟨473839, pr473839⟩
private theorem pr473857 : PrimeCertificate 473857 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv617]) (by decide +kernel)
def pv473857 : PrimeValue := ⟨473857, pr473857⟩
private theorem pr473923 : PrimeCertificate 473923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv113,pv233]) (by decide +kernel)
def pv473923 : PrimeValue := ⟨473923, pr473923⟩
private theorem pr473981 : PrimeCertificate 473981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv1823]) (by decide +kernel)
def pv473981 : PrimeValue := ⟨473981, pr473981⟩
private theorem pr474017 : PrimeCertificate 474017 :=
  certifyPrime (q := pv3) (ls := [pv2,pv14813]) (by decide +kernel)
def pv474017 : PrimeValue := ⟨474017, pr474017⟩
private theorem pr474037 : PrimeCertificate 474037 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv39503]) (by decide +kernel)
def pv474037 : PrimeValue := ⟨474037, pr474037⟩
private theorem pr474043 : PrimeCertificate 474043 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv41,pv47]) (by decide +kernel)
def pv474043 : PrimeValue := ⟨474043, pr474043⟩
private theorem pr474101 : PrimeCertificate 474101 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv431]) (by decide +kernel)
def pv474101 : PrimeValue := ⟨474101, pr474101⟩
private theorem pr474143 : PrimeCertificate 474143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv237071]) (by decide +kernel)
def pv474143 : PrimeValue := ⟨474143, pr474143⟩
private theorem pr474169 : PrimeCertificate 474169 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23,pv859]) (by decide +kernel)
def pv474169 : PrimeValue := ⟨474169, pr474169⟩
private theorem pr474223 : PrimeCertificate 474223 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv1613]) (by decide +kernel)
def pv474223 : PrimeValue := ⟨474223, pr474223⟩
private theorem pr474307 : PrimeCertificate 474307 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv23,pv491]) (by decide +kernel)
def pv474307 : PrimeValue := ⟨474307, pr474307⟩
private theorem pr474319 : PrimeCertificate 474319 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv2027]) (by decide +kernel)
def pv474319 : PrimeValue := ⟨474319, pr474319⟩
private theorem pr474347 : PrimeCertificate 474347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv237173]) (by decide +kernel)
def pv474347 : PrimeValue := ⟨474347, pr474347⟩
private theorem pr474379 : PrimeCertificate 474379 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv79063]) (by decide +kernel)
def pv474379 : PrimeValue := ⟨474379, pr474379⟩
private theorem pr474413 : PrimeCertificate 474413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv118603]) (by decide +kernel)
def pv474413 : PrimeValue := ⟨474413, pr474413⟩
private theorem pr474433 : PrimeCertificate 474433 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv353]) (by decide +kernel)
def pv474433 : PrimeValue := ⟨474433, pr474433⟩
private theorem pr474443 : PrimeCertificate 474443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv151,pv1571]) (by decide +kernel)
def pv474443 : PrimeValue := ⟨474443, pr474443⟩
private theorem pr474557 : PrimeCertificate 474557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv4091]) (by decide +kernel)
def pv474557 : PrimeValue := ⟨474557, pr474557⟩
private theorem pr474583 : PrimeCertificate 474583 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv23,pv181]) (by decide +kernel)
def pv474583 : PrimeValue := ⟨474583, pr474583⟩
private theorem pr474707 : PrimeCertificate 474707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71,pv3343]) (by decide +kernel)
def pv474707 : PrimeValue := ⟨474707, pr474707⟩
private theorem pr474751 : PrimeCertificate 474751 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv211]) (by decide +kernel)
def pv474751 : PrimeValue := ⟨474751, pr474751⟩
private theorem pr474769 : PrimeCertificate 474769 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv7,pv157]) (by decide +kernel)
def pv474769 : PrimeValue := ⟨474769, pr474769⟩
private theorem pr474787 : PrimeCertificate 474787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv2029]) (by decide +kernel)
def pv474787 : PrimeValue := ⟨474787, pr474787⟩
private theorem pr474941 : PrimeCertificate 474941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23747]) (by decide +kernel)
def pv474941 : PrimeValue := ⟨474941, pr474941⟩
private theorem pr474949 : PrimeCertificate 474949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv79,pv167]) (by decide +kernel)
def pv474949 : PrimeValue := ⟨474949, pr474949⟩
private theorem pr474983 : PrimeCertificate 474983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv31,pv47,pv163]) (by decide +kernel)
def pv474983 : PrimeValue := ⟨474983, pr474983⟩
private theorem pr475037 : PrimeCertificate 475037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv103,pv1153]) (by decide +kernel)
def pv475037 : PrimeValue := ⟨475037, pr475037⟩
private theorem pr475081 : PrimeCertificate 475081 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv37,pv107]) (by decide +kernel)
def pv475081 : PrimeValue := ⟨475081, pr475081⟩
private theorem pr475093 : PrimeCertificate 475093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53,pv83]) (by decide +kernel)
def pv475093 : PrimeValue := ⟨475093, pr475093⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
