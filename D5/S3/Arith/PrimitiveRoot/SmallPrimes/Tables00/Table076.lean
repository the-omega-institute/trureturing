/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table076
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table076.pv248473
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table008
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table011
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table017
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table045
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table046

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr248473 : PrimeCertificate 248473 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv17,pv29]) (by decide +kernel)
def pv248473 : PrimeValue := ⟨248473, pr248473⟩
private theorem pr248477 : PrimeCertificate 248477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv62119]) (by decide +kernel)
def pv248477 : PrimeValue := ⟨248477, pr248477⟩
private theorem pr248483 : PrimeCertificate 248483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv19,pv503]) (by decide +kernel)
def pv248483 : PrimeValue := ⟨248483, pr248483⟩
private theorem pr248533 : PrimeCertificate 248533 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv139,pv149]) (by decide +kernel)
def pv248533 : PrimeValue := ⟨248533, pr248533⟩
private theorem pr248537 : PrimeCertificate 248537 :=
  certifyPrime (q := pv3) (ls := [pv2,pv47,pv661]) (by decide +kernel)
def pv248537 : PrimeValue := ⟨248537, pr248537⟩
private theorem pr248543 : PrimeCertificate 248543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv41,pv433]) (by decide +kernel)
def pv248543 : PrimeValue := ⟨248543, pr248543⟩
private theorem pr248579 : PrimeCertificate 248579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv11299]) (by decide +kernel)
def pv248579 : PrimeValue := ⟨248579, pr248579⟩
private theorem pr248593 : PrimeCertificate 248593 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv5179]) (by decide +kernel)
def pv248593 : PrimeValue := ⟨248593, pr248593⟩
private theorem pr248597 : PrimeCertificate 248597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv3271]) (by decide +kernel)
def pv248597 : PrimeValue := ⟨248597, pr248597⟩
private theorem pr248621 : PrimeCertificate 248621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31,pv401]) (by decide +kernel)
def pv248621 : PrimeValue := ⟨248621, pr248621⟩
private theorem pr248639 : PrimeCertificate 248639 :=
  certifyPrime (q := pv17) (ls := [pv2,pv13,pv73,pv131]) (by decide +kernel)
def pv248639 : PrimeValue := ⟨248639, pr248639⟩
private theorem pr248657 : PrimeCertificate 248657 :=
  certifyPrime (q := pv3) (ls := [pv2,pv15541]) (by decide +kernel)
def pv248657 : PrimeValue := ⟨248657, pr248657⟩
private theorem pr248683 : PrimeCertificate 248683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv31,pv191]) (by decide +kernel)
def pv248683 : PrimeValue := ⟨248683, pr248683⟩
private theorem pr248707 : PrimeCertificate 248707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv337]) (by decide +kernel)
def pv248707 : PrimeValue := ⟨248707, pr248707⟩
private theorem pr248719 : PrimeCertificate 248719 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41453]) (by decide +kernel)
def pv248719 : PrimeValue := ⟨248719, pr248719⟩
private theorem pr248737 : PrimeCertificate 248737 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2591]) (by decide +kernel)
def pv248737 : PrimeValue := ⟨248737, pr248737⟩
private theorem pr248749 : PrimeCertificate 248749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv1091]) (by decide +kernel)
def pv248749 : PrimeValue := ⟨248749, pr248749⟩
private theorem pr248753 : PrimeCertificate 248753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv2221]) (by decide +kernel)
def pv248753 : PrimeValue := ⟨248753, pr248753⟩
private theorem pr248779 : PrimeCertificate 248779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv271]) (by decide +kernel)
def pv248779 : PrimeValue := ⟨248779, pr248779⟩
private theorem pr248783 : PrimeCertificate 248783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv53,pv2347]) (by decide +kernel)
def pv248783 : PrimeValue := ⟨248783, pr248783⟩
private theorem pr248789 : PrimeCertificate 248789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv41]) (by decide +kernel)
def pv248789 : PrimeValue := ⟨248789, pr248789⟩
private theorem pr248797 : PrimeCertificate 248797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv6911]) (by decide +kernel)
def pv248797 : PrimeValue := ⟨248797, pr248797⟩
private theorem pr248813 : PrimeCertificate 248813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv3659]) (by decide +kernel)
def pv248813 : PrimeValue := ⟨248813, pr248813⟩
private theorem pr248827 : PrimeCertificate 248827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv113,pv367]) (by decide +kernel)
def pv248827 : PrimeValue := ⟨248827, pr248827⟩
private theorem pr248839 : PrimeCertificate 248839 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv67,pv619]) (by decide +kernel)
def pv248839 : PrimeValue := ⟨248839, pr248839⟩
private theorem pr248861 : PrimeCertificate 248861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv541]) (by decide +kernel)
def pv248861 : PrimeValue := ⟨248861, pr248861⟩
private theorem pr248869 : PrimeCertificate 248869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv223]) (by decide +kernel)
def pv248869 : PrimeValue := ⟨248869, pr248869⟩
private theorem pr248887 : PrimeCertificate 248887 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv419]) (by decide +kernel)
def pv248887 : PrimeValue := ⟨248887, pr248887⟩
private theorem pr248893 : PrimeCertificate 248893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv2963]) (by decide +kernel)
def pv248893 : PrimeValue := ⟨248893, pr248893⟩
private theorem pr248981 : PrimeCertificate 248981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv59,pv211]) (by decide +kernel)
def pv248981 : PrimeValue := ⟨248981, pr248981⟩
private theorem pr249059 : PrimeCertificate 249059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv124529]) (by decide +kernel)
def pv249059 : PrimeValue := ⟨249059, pr249059⟩
private theorem pr249079 : PrimeCertificate 249079 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41513]) (by decide +kernel)
def pv249079 : PrimeValue := ⟨249079, pr249079⟩
private theorem pr249089 : PrimeCertificate 249089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv139]) (by decide +kernel)
def pv249089 : PrimeValue := ⟨249089, pr249089⟩
private theorem pr249097 : PrimeCertificate 249097 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv97,pv107]) (by decide +kernel)
def pv249097 : PrimeValue := ⟨249097, pr249097⟩
private theorem pr249103 : PrimeCertificate 249103 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv7,pv659]) (by decide +kernel)
def pv249103 : PrimeValue := ⟨249103, pr249103⟩
private theorem pr249107 : PrimeCertificate 249107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13,pv67]) (by decide +kernel)
def pv249107 : PrimeValue := ⟨249107, pr249107⟩
private theorem pr249131 : PrimeCertificate 249131 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv3559]) (by decide +kernel)
def pv249131 : PrimeValue := ⟨249131, pr249131⟩
private theorem pr249133 : PrimeCertificate 249133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv1597]) (by decide +kernel)
def pv249133 : PrimeValue := ⟨249133, pr249133⟩
private theorem pr249143 : PrimeCertificate 249143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv43,pv2897]) (by decide +kernel)
def pv249143 : PrimeValue := ⟨249143, pr249143⟩
private theorem pr249187 : PrimeCertificate 249187 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv17,pv349]) (by decide +kernel)
def pv249187 : PrimeValue := ⟨249187, pr249187⟩
private theorem pr249211 : PrimeCertificate 249211 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv71]) (by decide +kernel)
def pv249211 : PrimeValue := ⟨249211, pr249211⟩
private theorem pr249229 : PrimeCertificate 249229 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv23,pv43]) (by decide +kernel)
def pv249229 : PrimeValue := ⟨249229, pr249229⟩
private theorem pr249233 : PrimeCertificate 249233 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv421]) (by decide +kernel)
def pv249233 : PrimeValue := ⟨249233, pr249233⟩
private theorem pr249253 : PrimeCertificate 249253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv20771]) (by decide +kernel)
def pv249253 : PrimeValue := ⟨249253, pr249253⟩
private theorem pr249287 : PrimeCertificate 249287 :=
  certifyPrime (q := pv5) (ls := [pv2,pv124643]) (by decide +kernel)
def pv249287 : PrimeValue := ⟨249287, pr249287⟩
private theorem pr249311 : PrimeCertificate 249311 :=
  certifyPrime (q := pv29) (ls := [pv2,pv5,pv107,pv233]) (by decide +kernel)
def pv249311 : PrimeValue := ⟨249311, pr249311⟩
private theorem pr249367 : PrimeCertificate 249367 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv23,pv139]) (by decide +kernel)
def pv249367 : PrimeValue := ⟨249367, pr249367⟩
private theorem pr249383 : PrimeCertificate 249383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv47,pv379]) (by decide +kernel)
def pv249383 : PrimeValue := ⟨249383, pr249383⟩
private theorem pr249397 : PrimeCertificate 249397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv2969]) (by decide +kernel)
def pv249397 : PrimeValue := ⟨249397, pr249397⟩
private theorem pr249419 : PrimeCertificate 249419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv53,pv181]) (by decide +kernel)
def pv249419 : PrimeValue := ⟨249419, pr249419⟩
private theorem pr249427 : PrimeCertificate 249427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv149]) (by decide +kernel)
def pv249427 : PrimeValue := ⟨249427, pr249427⟩
private theorem pr249439 : PrimeCertificate 249439 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv5939]) (by decide +kernel)
def pv249439 : PrimeValue := ⟨249439, pr249439⟩
private theorem pr249463 : PrimeCertificate 249463 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13859]) (by decide +kernel)
def pv249463 : PrimeValue := ⟨249463, pr249463⟩
private theorem pr249497 : PrimeCertificate 249497 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv2399]) (by decide +kernel)
def pv249497 : PrimeValue := ⟨249497, pr249497⟩
private theorem pr249499 : PrimeCertificate 249499 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv83,pv167]) (by decide +kernel)
def pv249499 : PrimeValue := ⟨249499, pr249499⟩
private theorem pr249503 : PrimeCertificate 249503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv1031]) (by decide +kernel)
def pv249503 : PrimeValue := ⟨249503, pr249503⟩
private theorem pr249517 : PrimeCertificate 249517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv239]) (by decide +kernel)
def pv249517 : PrimeValue := ⟨249517, pr249517⟩
private theorem pr249521 : PrimeCertificate 249521 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv3119]) (by decide +kernel)
def pv249521 : PrimeValue := ⟨249521, pr249521⟩
private theorem pr249533 : PrimeCertificate 249533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv62383]) (by decide +kernel)
def pv249533 : PrimeValue := ⟨249533, pr249533⟩
private theorem pr249539 : PrimeCertificate 249539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv124769]) (by decide +kernel)
def pv249539 : PrimeValue := ⟨249539, pr249539⟩
private theorem pr249541 : PrimeCertificate 249541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv4159]) (by decide +kernel)
def pv249541 : PrimeValue := ⟨249541, pr249541⟩
private theorem pr249563 : PrimeCertificate 249563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv124781]) (by decide +kernel)
def pv249563 : PrimeValue := ⟨249563, pr249563⟩
private theorem pr249583 : PrimeCertificate 249583 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41597]) (by decide +kernel)
def pv249583 : PrimeValue := ⟨249583, pr249583⟩
private theorem pr249607 : PrimeCertificate 249607 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv283]) (by decide +kernel)
def pv249607 : PrimeValue := ⟨249607, pr249607⟩
private theorem pr249671 : PrimeCertificate 249671 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv24967]) (by decide +kernel)
def pv249671 : PrimeValue := ⟨249671, pr249671⟩
private theorem pr249703 : PrimeCertificate 249703 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41617]) (by decide +kernel)
def pv249703 : PrimeValue := ⟨249703, pr249703⟩
private theorem pr249721 : PrimeCertificate 249721 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv2081]) (by decide +kernel)
def pv249721 : PrimeValue := ⟨249721, pr249721⟩
private theorem pr249727 : PrimeCertificate 249727 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41621]) (by decide +kernel)
def pv249727 : PrimeValue := ⟨249727, pr249727⟩
private theorem pr249763 : PrimeCertificate 249763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41627]) (by decide +kernel)
def pv249763 : PrimeValue := ⟨249763, pr249763⟩
private theorem pr249779 : PrimeCertificate 249779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71,pv1759]) (by decide +kernel)
def pv249779 : PrimeValue := ⟨249779, pr249779⟩
private theorem pr249827 : PrimeCertificate 249827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv5431]) (by decide +kernel)
def pv249827 : PrimeValue := ⟨249827, pr249827⟩
private theorem pr249833 : PrimeCertificate 249833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv17,pv167]) (by decide +kernel)
def pv249833 : PrimeValue := ⟨249833, pr249833⟩
private theorem pr249859 : PrimeCertificate 249859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv661]) (by decide +kernel)
def pv249859 : PrimeValue := ⟨249859, pr249859⟩
private theorem pr249863 : PrimeCertificate 249863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv271,pv461]) (by decide +kernel)
def pv249863 : PrimeValue := ⟨249863, pr249863⟩
private theorem pr249871 : PrimeCertificate 249871 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv8329]) (by decide +kernel)
def pv249871 : PrimeValue := ⟨249871, pr249871⟩
private theorem pr249881 : PrimeCertificate 249881 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv6247]) (by decide +kernel)
def pv249881 : PrimeValue := ⟨249881, pr249881⟩
private theorem pr249911 : PrimeCertificate 249911 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv67,pv373]) (by decide +kernel)
def pv249911 : PrimeValue := ⟨249911, pr249911⟩
private theorem pr249943 : PrimeCertificate 249943 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv541]) (by decide +kernel)
def pv249943 : PrimeValue := ⟨249943, pr249943⟩
private theorem pr249947 : PrimeCertificate 249947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv2659]) (by decide +kernel)
def pv249947 : PrimeValue := ⟨249947, pr249947⟩
private theorem pr249967 : PrimeCertificate 249967 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1543]) (by decide +kernel)
def pv249967 : PrimeValue := ⟨249967, pr249967⟩
private theorem pr249971 : PrimeCertificate 249971 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv3571]) (by decide +kernel)
def pv249971 : PrimeValue := ⟨249971, pr249971⟩
private theorem pr249973 : PrimeCertificate 249973 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv37,pv563]) (by decide +kernel)
def pv249973 : PrimeValue := ⟨249973, pr249973⟩
private theorem pr249989 : PrimeCertificate 249989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv62497]) (by decide +kernel)
def pv249989 : PrimeValue := ⟨249989, pr249989⟩
private theorem pr250007 : PrimeCertificate 250007 :=
  certifyPrime (q := pv5) (ls := [pv2,pv125003]) (by decide +kernel)
def pv250007 : PrimeValue := ⟨250007, pr250007⟩
private theorem pr250031 : PrimeCertificate 250031 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv2273]) (by decide +kernel)
def pv250031 : PrimeValue := ⟨250031, pr250031⟩
private theorem pr250049 : PrimeCertificate 250049 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3907]) (by decide +kernel)
def pv250049 : PrimeValue := ⟨250049, pr250049⟩
private theorem pr250123 : PrimeCertificate 250123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41687]) (by decide +kernel)
def pv250123 : PrimeValue := ⟨250123, pr250123⟩
private theorem pr250147 : PrimeCertificate 250147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv1069]) (by decide +kernel)
def pv250147 : PrimeValue := ⟨250147, pr250147⟩
private theorem pr250153 : PrimeCertificate 250153 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv1489]) (by decide +kernel)
def pv250153 : PrimeValue := ⟨250153, pr250153⟩
private theorem pr250169 : PrimeCertificate 250169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31271]) (by decide +kernel)
def pv250169 : PrimeValue := ⟨250169, pr250169⟩
private theorem pr250259 : PrimeCertificate 250259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv157,pv797]) (by decide +kernel)
def pv250259 : PrimeValue := ⟨250259, pr250259⟩
private theorem pr250267 : PrimeCertificate 250267 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53,pv787]) (by decide +kernel)
def pv250267 : PrimeValue := ⟨250267, pr250267⟩
private theorem pr250301 : PrimeCertificate 250301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv2503]) (by decide +kernel)
def pv250301 : PrimeValue := ⟨250301, pr250301⟩
private theorem pr250361 : PrimeCertificate 250361 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv11,pv569]) (by decide +kernel)
def pv250361 : PrimeValue := ⟨250361, pr250361⟩
private theorem pr250403 : PrimeCertificate 250403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv125201]) (by decide +kernel)
def pv250403 : PrimeValue := ⟨250403, pr250403⟩
private theorem pr250409 : PrimeCertificate 250409 :=
  certifyPrime (q := pv3) (ls := [pv2,pv113,pv277]) (by decide +kernel)
def pv250409 : PrimeValue := ⟨250409, pr250409⟩
private theorem pr250441 : PrimeCertificate 250441 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv2087]) (by decide +kernel)
def pv250441 : PrimeValue := ⟨250441, pr250441⟩
private theorem pr250489 : PrimeCertificate 250489 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv71]) (by decide +kernel)
def pv250489 : PrimeValue := ⟨250489, pr250489⟩
private theorem pr250501 : PrimeCertificate 250501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv167]) (by decide +kernel)
def pv250501 : PrimeValue := ⟨250501, pr250501⟩
private theorem pr250543 : PrimeCertificate 250543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv449]) (by decide +kernel)
def pv250543 : PrimeValue := ⟨250543, pr250543⟩
private theorem pr250583 : PrimeCertificate 250583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv349,pv359]) (by decide +kernel)
def pv250583 : PrimeValue := ⟨250583, pr250583⟩
private theorem pr250619 : PrimeCertificate 250619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv149]) (by decide +kernel)
def pv250619 : PrimeValue := ⟨250619, pr250619⟩
private theorem pr250643 : PrimeCertificate 250643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv17903]) (by decide +kernel)
def pv250643 : PrimeValue := ⟨250643, pr250643⟩
private theorem pr250673 : PrimeCertificate 250673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv15667]) (by decide +kernel)
def pv250673 : PrimeValue := ⟨250673, pr250673⟩
private theorem pr250693 : PrimeCertificate 250693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv1607]) (by decide +kernel)
def pv250693 : PrimeValue := ⟨250693, pr250693⟩
private theorem pr250703 : PrimeCertificate 250703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv103,pv1217]) (by decide +kernel)
def pv250703 : PrimeValue := ⟨250703, pr250703⟩
private theorem pr250709 : PrimeCertificate 250709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv233,pv269]) (by decide +kernel)
def pv250709 : PrimeValue := ⟨250709, pr250709⟩
private theorem pr250721 : PrimeCertificate 250721 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv1567]) (by decide +kernel)
def pv250721 : PrimeValue := ⟨250721, pr250721⟩
private theorem pr250751 : PrimeCertificate 250751 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv17,pv59]) (by decide +kernel)
def pv250751 : PrimeValue := ⟨250751, pr250751⟩
private theorem pr250753 : PrimeCertificate 250753 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv653]) (by decide +kernel)
def pv250753 : PrimeValue := ⟨250753, pr250753⟩
private theorem pr250777 : PrimeCertificate 250777 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv43]) (by decide +kernel)
def pv250777 : PrimeValue := ⟨250777, pr250777⟩
private theorem pr250787 : PrimeCertificate 250787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv3389]) (by decide +kernel)
def pv250787 : PrimeValue := ⟨250787, pr250787⟩
private theorem pr250799 : PrimeCertificate 250799 :=
  certifyPrime (q := pv31) (ls := [pv2,pv125399]) (by decide +kernel)
def pv250799 : PrimeValue := ⟨250799, pr250799⟩
private theorem pr250807 : PrimeCertificate 250807 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41801]) (by decide +kernel)
def pv250807 : PrimeValue := ⟨250807, pr250807⟩
private theorem pr250813 : PrimeCertificate 250813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv6967]) (by decide +kernel)
def pv250813 : PrimeValue := ⟨250813, pr250813⟩
private theorem pr250829 : PrimeCertificate 250829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv859]) (by decide +kernel)
def pv250829 : PrimeValue := ⟨250829, pr250829⟩
private theorem pr250837 : PrimeCertificate 250837 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv20903]) (by decide +kernel)
def pv250837 : PrimeValue := ⟨250837, pr250837⟩
private theorem pr250841 : PrimeCertificate 250841 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv6271]) (by decide +kernel)
def pv250841 : PrimeValue := ⟨250841, pr250841⟩
private theorem pr250853 : PrimeCertificate 250853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv17,pv31]) (by decide +kernel)
def pv250853 : PrimeValue := ⟨250853, pr250853⟩
private theorem pr250867 : PrimeCertificate 250867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv181]) (by decide +kernel)
def pv250867 : PrimeValue := ⟨250867, pr250867⟩
private theorem pr250871 : PrimeCertificate 250871 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv25087]) (by decide +kernel)
def pv250871 : PrimeValue := ⟨250871, pr250871⟩
private theorem pr250889 : PrimeCertificate 250889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv2851]) (by decide +kernel)
def pv250889 : PrimeValue := ⟨250889, pr250889⟩
private theorem pr250919 : PrimeCertificate 250919 :=
  certifyPrime (q := pv7) (ls := [pv2,pv109,pv1151]) (by decide +kernel)
def pv250919 : PrimeValue := ⟨250919, pr250919⟩
private theorem pr250967 : PrimeCertificate 250967 :=
  certifyPrime (q := pv5) (ls := [pv2,pv29,pv4327]) (by decide +kernel)
def pv250967 : PrimeValue := ⟨250967, pr250967⟩
private theorem pr250969 : PrimeCertificate 250969 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv10457]) (by decide +kernel)
def pv250969 : PrimeValue := ⟨250969, pr250969⟩
private theorem pr250993 : PrimeCertificate 250993 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv83]) (by decide +kernel)
def pv250993 : PrimeValue := ⟨250993, pr250993⟩
private theorem pr251033 : PrimeCertificate 251033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31379]) (by decide +kernel)
def pv251033 : PrimeValue := ⟨251033, pr251033⟩
private theorem pr251059 : PrimeCertificate 251059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41843]) (by decide +kernel)
def pv251059 : PrimeValue := ⟨251059, pr251059⟩
private theorem pr251081 : PrimeCertificate 251081 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv6277]) (by decide +kernel)
def pv251081 : PrimeValue := ⟨251081, pr251081⟩
private theorem pr251087 : PrimeCertificate 251087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv101,pv113]) (by decide +kernel)
def pv251087 : PrimeValue := ⟨251087, pr251087⟩
private theorem pr251099 : PrimeCertificate 251099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv223,pv563]) (by decide +kernel)
def pv251099 : PrimeValue := ⟨251099, pr251099⟩
private theorem pr251179 : PrimeCertificate 251179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41863]) (by decide +kernel)
def pv251179 : PrimeValue := ⟨251179, pr251179⟩
private theorem pr251191 : PrimeCertificate 251191 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv2791]) (by decide +kernel)
def pv251191 : PrimeValue := ⟨251191, pr251191⟩
private theorem pr251197 : PrimeCertificate 251197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv173]) (by decide +kernel)
def pv251197 : PrimeValue := ⟨251197, pr251197⟩
private theorem pr251219 : PrimeCertificate 251219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv19,pv601]) (by decide +kernel)
def pv251219 : PrimeValue := ⟨251219, pr251219⟩
private theorem pr251221 : PrimeCertificate 251221 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv53,pv79]) (by decide +kernel)
def pv251221 : PrimeValue := ⟨251221, pr251221⟩
private theorem pr251233 : PrimeCertificate 251233 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2617]) (by decide +kernel)
def pv251233 : PrimeValue := ⟨251233, pr251233⟩
private theorem pr251257 : PrimeCertificate 251257 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv19,pv29]) (by decide +kernel)
def pv251257 : PrimeValue := ⟨251257, pr251257⟩
private theorem pr251261 : PrimeCertificate 251261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv739]) (by decide +kernel)
def pv251261 : PrimeValue := ⟨251261, pr251261⟩
private theorem pr251291 : PrimeCertificate 251291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv1933]) (by decide +kernel)
def pv251291 : PrimeValue := ⟨251291, pr251291⟩
private theorem pr251323 : PrimeCertificate 251323 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41887]) (by decide +kernel)
def pv251323 : PrimeValue := ⟨251323, pr251323⟩
private theorem pr251353 : PrimeCertificate 251353 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3491]) (by decide +kernel)
def pv251353 : PrimeValue := ⟨251353, pr251353⟩
private theorem pr251359 : PrimeCertificate 251359 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41893]) (by decide +kernel)
def pv251359 : PrimeValue := ⟨251359, pr251359⟩
private theorem pr251387 : PrimeCertificate 251387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv125693]) (by decide +kernel)
def pv251387 : PrimeValue := ⟨251387, pr251387⟩
private theorem pr251393 : PrimeCertificate 251393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv491]) (by decide +kernel)
def pv251393 : PrimeValue := ⟨251393, pr251393⟩
private theorem pr251431 : PrimeCertificate 251431 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv17,pv29]) (by decide +kernel)
def pv251431 : PrimeValue := ⟨251431, pr251431⟩
private theorem pr251437 : PrimeCertificate 251437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv911]) (by decide +kernel)
def pv251437 : PrimeValue := ⟨251437, pr251437⟩
private theorem pr251443 : PrimeCertificate 251443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61,pv229]) (by decide +kernel)
def pv251443 : PrimeValue := ⟨251443, pr251443⟩
private theorem pr251467 : PrimeCertificate 251467 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41911]) (by decide +kernel)
def pv251467 : PrimeValue := ⟨251467, pr251467⟩
private theorem pr251473 : PrimeCertificate 251473 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv31]) (by decide +kernel)
def pv251473 : PrimeValue := ⟨251473, pr251473⟩
private theorem pr251501 : PrimeCertificate 251501 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv503]) (by decide +kernel)
def pv251501 : PrimeValue := ⟨251501, pr251501⟩
private theorem pr251519 : PrimeCertificate 251519 :=
  certifyPrime (q := pv7) (ls := [pv2,pv67,pv1877]) (by decide +kernel)
def pv251519 : PrimeValue := ⟨251519, pr251519⟩
private theorem pr251527 : PrimeCertificate 251527 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv37,pv103]) (by decide +kernel)
def pv251527 : PrimeValue := ⟨251527, pr251527⟩
private theorem pr251533 : PrimeCertificate 251533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv137]) (by decide +kernel)
def pv251533 : PrimeValue := ⟨251533, pr251533⟩
private theorem pr251543 : PrimeCertificate 251543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv173,pv727]) (by decide +kernel)
def pv251543 : PrimeValue := ⟨251543, pr251543⟩
private theorem pr251561 : PrimeCertificate 251561 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv19,pv331]) (by decide +kernel)
def pv251561 : PrimeValue := ⟨251561, pr251561⟩
private theorem pr251611 : PrimeCertificate 251611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv8387]) (by decide +kernel)
def pv251611 : PrimeValue := ⟨251611, pr251611⟩
private theorem pr251621 : PrimeCertificate 251621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv547]) (by decide +kernel)
def pv251621 : PrimeValue := ⟨251621, pr251621⟩
private theorem pr251623 : PrimeCertificate 251623 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv1997]) (by decide +kernel)
def pv251623 : PrimeValue := ⟨251623, pr251623⟩
private theorem pr251639 : PrimeCertificate 251639 :=
  certifyPrime (q := pv11) (ls := [pv2,pv47,pv2677]) (by decide +kernel)
def pv251639 : PrimeValue := ⟨251639, pr251639⟩
private theorem pr251653 : PrimeCertificate 251653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv67,pv313]) (by decide +kernel)
def pv251653 : PrimeValue := ⟨251653, pr251653⟩
private theorem pr251663 : PrimeCertificate 251663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv29,pv4339]) (by decide +kernel)
def pv251663 : PrimeValue := ⟨251663, pr251663⟩
private theorem pr251677 : PrimeCertificate 251677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv6991]) (by decide +kernel)
def pv251677 : PrimeValue := ⟨251677, pr251677⟩
private theorem pr251701 : PrimeCertificate 251701 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv839]) (by decide +kernel)
def pv251701 : PrimeValue := ⟨251701, pr251701⟩
private theorem pr251737 : PrimeCertificate 251737 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv17,pv617]) (by decide +kernel)
def pv251737 : PrimeValue := ⟨251737, pr251737⟩
private theorem pr251761 : PrimeCertificate 251761 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv1049]) (by decide +kernel)
def pv251761 : PrimeValue := ⟨251761, pr251761⟩
private theorem pr251791 : PrimeCertificate 251791 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv11,pv109]) (by decide +kernel)
def pv251791 : PrimeValue := ⟨251791, pr251791⟩
private theorem pr251831 : PrimeCertificate 251831 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv25183]) (by decide +kernel)
def pv251831 : PrimeValue := ⟨251831, pr251831⟩
private theorem pr251857 : PrimeCertificate 251857 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv53]) (by decide +kernel)
def pv251857 : PrimeValue := ⟨251857, pr251857⟩
private theorem pr251861 : PrimeCertificate 251861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv257]) (by decide +kernel)
def pv251861 : PrimeValue := ⟨251861, pr251861⟩
private theorem pr251879 : PrimeCertificate 251879 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv107]) (by decide +kernel)
def pv251879 : PrimeValue := ⟨251879, pr251879⟩
private theorem pr251887 : PrimeCertificate 251887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv41981]) (by decide +kernel)
def pv251887 : PrimeValue := ⟨251887, pr251887⟩
private theorem pr251897 : PrimeCertificate 251897 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv37]) (by decide +kernel)
def pv251897 : PrimeValue := ⟨251897, pr251897⟩
private theorem pr251903 : PrimeCertificate 251903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv19,pv947]) (by decide +kernel)
def pv251903 : PrimeValue := ⟨251903, pr251903⟩
private theorem pr251917 : PrimeCertificate 251917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv2999]) (by decide +kernel)
def pv251917 : PrimeValue := ⟨251917, pr251917⟩
private theorem pr251939 : PrimeCertificate 251939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv103,pv1223]) (by decide +kernel)
def pv251939 : PrimeValue := ⟨251939, pr251939⟩
private theorem pr251941 : PrimeCertificate 251941 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv13,pv17,pv19]) (by decide +kernel)
def pv251941 : PrimeValue := ⟨251941, pr251941⟩
private theorem pr251947 : PrimeCertificate 251947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13997]) (by decide +kernel)
def pv251947 : PrimeValue := ⟨251947, pr251947⟩
private theorem pr251969 : PrimeCertificate 251969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv127]) (by decide +kernel)
def pv251969 : PrimeValue := ⟨251969, pr251969⟩
private theorem pr251971 : PrimeCertificate 251971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv37,pv227]) (by decide +kernel)
def pv251971 : PrimeValue := ⟨251971, pr251971⟩
private theorem pr251983 : PrimeCertificate 251983 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13999]) (by decide +kernel)
def pv251983 : PrimeValue := ⟨251983, pr251983⟩
private theorem pr252001 : PrimeCertificate 252001 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv252001 : PrimeValue := ⟨252001, pr252001⟩
private theorem pr252013 : PrimeCertificate 252013 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv21001]) (by decide +kernel)
def pv252013 : PrimeValue := ⟨252013, pr252013⟩
private theorem pr252017 : PrimeCertificate 252017 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv829]) (by decide +kernel)
def pv252017 : PrimeValue := ⟨252017, pr252017⟩
private theorem pr252029 : PrimeCertificate 252029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv9001]) (by decide +kernel)
def pv252029 : PrimeValue := ⟨252029, pr252029⟩
private theorem pr252037 : PrimeCertificate 252037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7001]) (by decide +kernel)
def pv252037 : PrimeValue := ⟨252037, pr252037⟩
private theorem pr252079 : PrimeCertificate 252079 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv42013]) (by decide +kernel)
def pv252079 : PrimeValue := ⟨252079, pr252079⟩
private theorem pr252101 : PrimeCertificate 252101 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv2521]) (by decide +kernel)
def pv252101 : PrimeValue := ⟨252101, pr252101⟩
private theorem pr252139 : PrimeCertificate 252139 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv42023]) (by decide +kernel)
def pv252139 : PrimeValue := ⟨252139, pr252139⟩
private theorem pr252157 : PrimeCertificate 252157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv21013]) (by decide +kernel)
def pv252157 : PrimeValue := ⟨252157, pr252157⟩
private theorem pr252173 : PrimeCertificate 252173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv2741]) (by decide +kernel)
def pv252173 : PrimeValue := ⟨252173, pr252173⟩
private theorem pr252181 : PrimeCertificate 252181 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv467]) (by decide +kernel)
def pv252181 : PrimeValue := ⟨252181, pr252181⟩
private theorem pr252193 : PrimeCertificate 252193 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv37,pv71]) (by decide +kernel)
def pv252193 : PrimeValue := ⟨252193, pr252193⟩
private theorem pr252209 : PrimeCertificate 252209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv1433]) (by decide +kernel)
def pv252209 : PrimeValue := ⟨252209, pr252209⟩
private theorem pr252223 : PrimeCertificate 252223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv127,pv331]) (by decide +kernel)
def pv252223 : PrimeValue := ⟨252223, pr252223⟩
private theorem pr252233 : PrimeCertificate 252233 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41,pv769]) (by decide +kernel)
def pv252233 : PrimeValue := ⟨252233, pr252233⟩
private theorem pr252283 : PrimeCertificate 252283 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv2213]) (by decide +kernel)
def pv252283 : PrimeValue := ⟨252283, pr252283⟩
private theorem pr252289 : PrimeCertificate 252289 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv73]) (by decide +kernel)
def pv252289 : PrimeValue := ⟨252289, pr252289⟩
private theorem pr252341 : PrimeCertificate 252341 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv11,pv31,pv37]) (by decide +kernel)
def pv252341 : PrimeValue := ⟨252341, pr252341⟩
private theorem pr252359 : PrimeCertificate 252359 :=
  certifyPrime (q := pv7) (ls := [pv2,pv19,pv29,pv229]) (by decide +kernel)
def pv252359 : PrimeValue := ⟨252359, pr252359⟩
private theorem pr252383 : PrimeCertificate 252383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv17,pv571]) (by decide +kernel)
def pv252383 : PrimeValue := ⟨252383, pr252383⟩
private theorem pr252401 : PrimeCertificate 252401 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv631]) (by decide +kernel)
def pv252401 : PrimeValue := ⟨252401, pr252401⟩
private theorem pr252409 : PrimeCertificate 252409 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv809]) (by decide +kernel)
def pv252409 : PrimeValue := ⟨252409, pr252409⟩
private theorem pr252431 : PrimeCertificate 252431 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv25243]) (by decide +kernel)
def pv252431 : PrimeValue := ⟨252431, pr252431⟩
private theorem pr252443 : PrimeCertificate 252443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv113,pv1117]) (by decide +kernel)
def pv252443 : PrimeValue := ⟨252443, pr252443⟩
private theorem pr252481 : PrimeCertificate 252481 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv263]) (by decide +kernel)
def pv252481 : PrimeValue := ⟨252481, pr252481⟩
private theorem pr252533 : PrimeCertificate 252533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv29,pv311]) (by decide +kernel)
def pv252533 : PrimeValue := ⟨252533, pr252533⟩
private theorem pr252559 : PrimeCertificate 252559 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv1559]) (by decide +kernel)
def pv252559 : PrimeValue := ⟨252559, pr252559⟩
private theorem pr252583 : PrimeCertificate 252583 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv43,pv89]) (by decide +kernel)
def pv252583 : PrimeValue := ⟨252583, pr252583⟩
private theorem pr252589 : PrimeCertificate 252589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv31,pv97]) (by decide +kernel)
def pv252589 : PrimeValue := ⟨252589, pr252589⟩
private theorem pr252607 : PrimeCertificate 252607 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv42101]) (by decide +kernel)
def pv252607 : PrimeValue := ⟨252607, pr252607⟩
private theorem pr252611 : PrimeCertificate 252611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv25261]) (by decide +kernel)
def pv252611 : PrimeValue := ⟨252611, pr252611⟩
private theorem pr252641 : PrimeCertificate 252641 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1579]) (by decide +kernel)
def pv252641 : PrimeValue := ⟨252641, pr252641⟩
private theorem pr252713 : PrimeCertificate 252713 :=
  certifyPrime (q := pv5) (ls := [pv2,pv31,pv1019]) (by decide +kernel)
def pv252713 : PrimeValue := ⟨252713, pr252713⟩
private theorem pr252727 : PrimeCertificate 252727 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv73,pv577]) (by decide +kernel)
def pv252727 : PrimeValue := ⟨252727, pr252727⟩
private theorem pr252731 : PrimeCertificate 252731 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv127,pv199]) (by decide +kernel)
def pv252731 : PrimeValue := ⟨252731, pr252731⟩
private theorem pr252761 : PrimeCertificate 252761 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv71,pv89]) (by decide +kernel)
def pv252761 : PrimeValue := ⟨252761, pr252761⟩
private theorem pr252779 : PrimeCertificate 252779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv211,pv599]) (by decide +kernel)
def pv252779 : PrimeValue := ⟨252779, pr252779⟩
private theorem pr252823 : PrimeCertificate 252823 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv29,pv1453]) (by decide +kernel)
def pv252823 : PrimeValue := ⟨252823, pr252823⟩
private theorem pr252827 : PrimeCertificate 252827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv18059]) (by decide +kernel)
def pv252827 : PrimeValue := ⟨252827, pr252827⟩
private theorem pr252877 : PrimeCertificate 252877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv1621]) (by decide +kernel)
def pv252877 : PrimeValue := ⟨252877, pr252877⟩
private theorem pr252881 : PrimeCertificate 252881 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv29,pv109]) (by decide +kernel)
def pv252881 : PrimeValue := ⟨252881, pr252881⟩
private theorem pr252887 : PrimeCertificate 252887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv126443]) (by decide +kernel)
def pv252887 : PrimeValue := ⟨252887, pr252887⟩
private theorem pr252911 : PrimeCertificate 252911 :=
  certifyPrime (q := pv29) (ls := [pv2,pv5,pv7,pv3613]) (by decide +kernel)
def pv252911 : PrimeValue := ⟨252911, pr252911⟩
private theorem pr252919 : PrimeCertificate 252919 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv14051]) (by decide +kernel)
def pv252919 : PrimeValue := ⟨252919, pr252919⟩
private theorem pr252937 : PrimeCertificate 252937 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1171]) (by decide +kernel)
def pv252937 : PrimeValue := ⟨252937, pr252937⟩
private theorem pr252949 : PrimeCertificate 252949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv107,pv197]) (by decide +kernel)
def pv252949 : PrimeValue := ⟨252949, pr252949⟩
private theorem pr252971 : PrimeCertificate 252971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41,pv617]) (by decide +kernel)
def pv252971 : PrimeValue := ⟨252971, pr252971⟩
private theorem pr252979 : PrimeCertificate 252979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv3833]) (by decide +kernel)
def pv252979 : PrimeValue := ⟨252979, pr252979⟩
private theorem pr253003 : PrimeCertificate 253003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv149,pv283]) (by decide +kernel)
def pv253003 : PrimeValue := ⟨253003, pr253003⟩
private theorem pr253049 : PrimeCertificate 253049 :=
  certifyPrime (q := pv3) (ls := [pv2,pv47,pv673]) (by decide +kernel)
def pv253049 : PrimeValue := ⟨253049, pr253049⟩
private theorem pr253063 : PrimeCertificate 253063 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv827]) (by decide +kernel)
def pv253063 : PrimeValue := ⟨253063, pr253063⟩
private theorem pr253109 : PrimeCertificate 253109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv63277]) (by decide +kernel)
def pv253109 : PrimeValue := ⟨253109, pr253109⟩
private theorem pr253133 : PrimeCertificate 253133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv523]) (by decide +kernel)
def pv253133 : PrimeValue := ⟨253133, pr253133⟩
private theorem pr253159 : PrimeCertificate 253159 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv42193]) (by decide +kernel)
def pv253159 : PrimeValue := ⟨253159, pr253159⟩
private theorem pr253229 : PrimeCertificate 253229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv37,pv59]) (by decide +kernel)
def pv253229 : PrimeValue := ⟨253229, pr253229⟩
private theorem pr253307 : PrimeCertificate 253307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv126653]) (by decide +kernel)
def pv253307 : PrimeValue := ⟨253307, pr253307⟩
private theorem pr253321 : PrimeCertificate 253321 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv5,pv2111]) (by decide +kernel)
def pv253321 : PrimeValue := ⟨253321, pr253321⟩
private theorem pr253343 : PrimeCertificate 253343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv197,pv643]) (by decide +kernel)
def pv253343 : PrimeValue := ⟨253343, pr253343⟩
private theorem pr253349 : PrimeCertificate 253349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv63337]) (by decide +kernel)
def pv253349 : PrimeValue := ⟨253349, pr253349⟩
private theorem pr253361 : PrimeCertificate 253361 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv3167]) (by decide +kernel)
def pv253361 : PrimeValue := ⟨253361, pr253361⟩
private theorem pr253367 : PrimeCertificate 253367 :=
  certifyPrime (q := pv5) (ls := [pv2,pv126683]) (by decide +kernel)
def pv253367 : PrimeValue := ⟨253367, pr253367⟩
private theorem pr253369 : PrimeCertificate 253369 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv17,pv23]) (by decide +kernel)
def pv253369 : PrimeValue := ⟨253369, pr253369⟩
private theorem pr253381 : PrimeCertificate 253381 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv41,pv103]) (by decide +kernel)
def pv253381 : PrimeValue := ⟨253381, pr253381⟩
private theorem pr253417 : PrimeCertificate 253417 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv10559]) (by decide +kernel)
def pv253417 : PrimeValue := ⟨253417, pr253417⟩
private theorem pr253423 : PrimeCertificate 253423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv19]) (by decide +kernel)
def pv253423 : PrimeValue := ⟨253423, pr253423⟩
private theorem pr253439 : PrimeCertificate 253439 :=
  certifyPrime (q := pv7) (ls := [pv2,pv126719]) (by decide +kernel)
def pv253439 : PrimeValue := ⟨253439, pr253439⟩
private theorem pr253447 : PrimeCertificate 253447 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv53,pv797]) (by decide +kernel)
def pv253447 : PrimeValue := ⟨253447, pr253447⟩
private theorem pr253481 : PrimeCertificate 253481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv6337]) (by decide +kernel)
def pv253481 : PrimeValue := ⟨253481, pr253481⟩
private theorem pr253493 : PrimeCertificate 253493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv127,pv499]) (by decide +kernel)
def pv253493 : PrimeValue := ⟨253493, pr253493⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
