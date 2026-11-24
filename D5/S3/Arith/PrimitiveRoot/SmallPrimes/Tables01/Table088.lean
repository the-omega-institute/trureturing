/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table088
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table088.pv316501
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table010
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table013
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table021
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table055
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table056

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr316501 : Nat.Prime 316501 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv211]) (by decide +kernel)
def pv316501 : PrimeValue := ⟨316501, pr316501⟩
private theorem pr316531 : Nat.Prime 316531 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv3517]) (by decide +kernel)
def pv316531 : PrimeValue := ⟨316531, pr316531⟩
private theorem pr316567 : Nat.Prime 316567 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv43,pv409]) (by decide +kernel)
def pv316567 : PrimeValue := ⟨316567, pr316567⟩
private theorem pr316621 : Nat.Prime 316621 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1759]) (by decide +kernel)
def pv316621 : PrimeValue := ⟨316621, pr316621⟩
private theorem pr316691 : Nat.Prime 316691 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv2879]) (by decide +kernel)
def pv316691 : PrimeValue := ⟨316691, pr316691⟩
private theorem pr316697 : Nat.Prime 316697 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv1277]) (by decide +kernel)
def pv316697 : PrimeValue := ⟨316697, pr316697⟩
private theorem pr316703 : Nat.Prime 316703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv158351]) (by decide +kernel)
def pv316703 : PrimeValue := ⟨316703, pr316703⟩
private theorem pr316717 : Nat.Prime 316717 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv26393]) (by decide +kernel)
def pv316717 : PrimeValue := ⟨316717, pr316717⟩
private theorem pr316769 : Nat.Prime 316769 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv521]) (by decide +kernel)
def pv316769 : PrimeValue := ⟨316769, pr316769⟩
private theorem pr316777 : Nat.Prime 316777 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv67,pv197]) (by decide +kernel)
def pv316777 : PrimeValue := ⟨316777, pr316777⟩
private theorem pr316817 : Nat.Prime 316817 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19801]) (by decide +kernel)
def pv316817 : PrimeValue := ⟨316817, pr316817⟩
private theorem pr316879 : Nat.Prime 316879 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv52813]) (by decide +kernel)
def pv316879 : PrimeValue := ⟨316879, pr316879⟩
private theorem pr316891 : Nat.Prime 316891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv503]) (by decide +kernel)
def pv316891 : PrimeValue := ⟨316891, pr316891⟩
private theorem pr316903 : Nat.Prime 316903 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv52817]) (by decide +kernel)
def pv316903 : PrimeValue := ⟨316903, pr316903⟩
private theorem pr316919 : Nat.Prime 316919 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv22637]) (by decide +kernel)
def pv316919 : PrimeValue := ⟨316919, pr316919⟩
private theorem pr316961 : Nat.Prime 316961 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv283]) (by decide +kernel)
def pv316961 : PrimeValue := ⟨316961, pr316961⟩
private theorem pr316991 : Nat.Prime 316991 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv31699]) (by decide +kernel)
def pv316991 : PrimeValue := ⟨316991, pr316991⟩
private theorem pr317021 : Nat.Prime 317021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv131]) (by decide +kernel)
def pv317021 : PrimeValue := ⟨317021, pr317021⟩
private theorem pr317063 : Nat.Prime 317063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv47,pv3373]) (by decide +kernel)
def pv317063 : PrimeValue := ⟨317063, pr317063⟩
private theorem pr317071 : Nat.Prime 317071 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv271]) (by decide +kernel)
def pv317071 : PrimeValue := ⟨317071, pr317071⟩
private theorem pr317077 : Nat.Prime 317077 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv26423]) (by decide +kernel)
def pv317077 : PrimeValue := ⟨317077, pr317077⟩
private theorem pr317087 : Nat.Prime 317087 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv11,pv29,pv71]) (by decide +kernel)
def pv317087 : PrimeValue := ⟨317087, pr317087⟩
private theorem pr317089 : Nat.Prime 317089 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv367]) (by decide +kernel)
def pv317089 : PrimeValue := ⟨317089, pr317089⟩
private theorem pr317123 : Nat.Prime 317123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv12197]) (by decide +kernel)
def pv317123 : PrimeValue := ⟨317123, pr317123⟩
private theorem pr317171 : Nat.Prime 317171 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv7,pv23,pv197]) (by decide +kernel)
def pv317171 : PrimeValue := ⟨317171, pr317171⟩
private theorem pr317197 : Nat.Prime 317197 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv89]) (by decide +kernel)
def pv317197 : PrimeValue := ⟨317197, pr317197⟩
private theorem pr317227 : Nat.Prime 317227 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv83]) (by decide +kernel)
def pv317227 : PrimeValue := ⟨317227, pr317227⟩
private theorem pr317263 : Nat.Prime 317263 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv19,pv23]) (by decide +kernel)
def pv317263 : PrimeValue := ⟨317263, pr317263⟩
private theorem pr317269 : Nat.Prime 317269 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv1259]) (by decide +kernel)
def pv317269 : PrimeValue := ⟨317269, pr317269⟩
private theorem pr317321 : Nat.Prime 317321 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7933]) (by decide +kernel)
def pv317321 : PrimeValue := ⟨317321, pr317321⟩
private theorem pr317327 : Nat.Prime 317327 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv158663]) (by decide +kernel)
def pv317327 : PrimeValue := ⟨317327, pr317327⟩
private theorem pr317351 : Nat.Prime 317351 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv11,pv577]) (by decide +kernel)
def pv317351 : PrimeValue := ⟨317351, pr317351⟩
private theorem pr317353 : Nat.Prime 317353 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv1889]) (by decide +kernel)
def pv317353 : PrimeValue := ⟨317353, pr317353⟩
private theorem pr317363 : Nat.Prime 317363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv107,pv1483]) (by decide +kernel)
def pv317363 : PrimeValue := ⟨317363, pr317363⟩
private theorem pr317411 : Nat.Prime 317411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv31741]) (by decide +kernel)
def pv317411 : PrimeValue := ⟨317411, pr317411⟩
private theorem pr317419 : Nat.Prime 317419 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv52903]) (by decide +kernel)
def pv317419 : PrimeValue := ⟨317419, pr317419⟩
private theorem pr317431 : Nat.Prime 317431 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv3527]) (by decide +kernel)
def pv317431 : PrimeValue := ⟨317431, pr317431⟩
private theorem pr317437 : Nat.Prime 317437 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv7,pv3779]) (by decide +kernel)
def pv317437 : PrimeValue := ⟨317437, pr317437⟩
private theorem pr317453 : Nat.Prime 317453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv4177]) (by decide +kernel)
def pv317453 : PrimeValue := ⟨317453, pr317453⟩
private theorem pr317489 : Nat.Prime 317489 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19843]) (by decide +kernel)
def pv317489 : PrimeValue := ⟨317489, pr317489⟩
private theorem pr317491 : Nat.Prime 317491 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv19,pv557]) (by decide +kernel)
def pv317491 : PrimeValue := ⟨317491, pr317491⟩
private theorem pr317503 : Nat.Prime 317503 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv31,pv569]) (by decide +kernel)
def pv317503 : PrimeValue := ⟨317503, pr317503⟩
private theorem pr317539 : Nat.Prime 317539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv23,pv59]) (by decide +kernel)
def pv317539 : PrimeValue := ⟨317539, pr317539⟩
private theorem pr317587 : Nat.Prime 317587 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv41,pv1291]) (by decide +kernel)
def pv317587 : PrimeValue := ⟨317587, pr317587⟩
private theorem pr317617 : Nat.Prime 317617 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv13,pv509]) (by decide +kernel)
def pv317617 : PrimeValue := ⟨317617, pr317617⟩
private theorem pr317621 : Nat.Prime 317621 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv15881]) (by decide +kernel)
def pv317621 : PrimeValue := ⟨317621, pr317621⟩
private theorem pr317663 : Nat.Prime 317663 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv9343]) (by decide +kernel)
def pv317663 : PrimeValue := ⟨317663, pr317663⟩
private theorem pr317693 : Nat.Prime 317693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79423]) (by decide +kernel)
def pv317693 : PrimeValue := ⟨317693, pr317693⟩
private theorem pr317711 : Nat.Prime 317711 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv31771]) (by decide +kernel)
def pv317711 : PrimeValue := ⟨317711, pr317711⟩
private theorem pr317731 : Nat.Prime 317731 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv17,pv89]) (by decide +kernel)
def pv317731 : PrimeValue := ⟨317731, pr317731⟩
private theorem pr317741 : Nat.Prime 317741 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv15887]) (by decide +kernel)
def pv317741 : PrimeValue := ⟨317741, pr317741⟩
private theorem pr317771 : Nat.Prime 317771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv43,pv739]) (by decide +kernel)
def pv317771 : PrimeValue := ⟨317771, pr317771⟩
private theorem pr317783 : Nat.Prime 317783 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv29,pv5479]) (by decide +kernel)
def pv317783 : PrimeValue := ⟨317783, pr317783⟩
private theorem pr317797 : Nat.Prime 317797 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv71,pv373]) (by decide +kernel)
def pv317797 : PrimeValue := ⟨317797, pr317797⟩
private theorem pr317827 : Nat.Prime 317827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17657]) (by decide +kernel)
def pv317827 : PrimeValue := ⟨317827, pr317827⟩
private theorem pr317831 : Nat.Prime 317831 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv5,pv37,pv859]) (by decide +kernel)
def pv317831 : PrimeValue := ⟨317831, pr317831⟩
private theorem pr317857 : Nat.Prime 317857 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv11,pv43]) (by decide +kernel)
def pv317857 : PrimeValue := ⟨317857, pr317857⟩
private theorem pr317921 : Nat.Prime 317921 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv1987]) (by decide +kernel)
def pv317921 : PrimeValue := ⟨317921, pr317921⟩
private theorem pr317957 : Nat.Prime 317957 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv2741]) (by decide +kernel)
def pv317957 : PrimeValue := ⟨317957, pr317957⟩
private theorem pr317969 : Nat.Prime 317969 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv17,pv167]) (by decide +kernel)
def pv317969 : PrimeValue := ⟨317969, pr317969⟩
private theorem pr317983 : Nat.Prime 317983 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv67,pv113]) (by decide +kernel)
def pv317983 : PrimeValue := ⟨317983, pr317983⟩
private theorem pr318007 : Nat.Prime 318007 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv151]) (by decide +kernel)
def pv318007 : PrimeValue := ⟨318007, pr318007⟩
private theorem pr318077 : Nat.Prime 318077 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv7229]) (by decide +kernel)
def pv318077 : PrimeValue := ⟨318077, pr318077⟩
private theorem pr318161 : Nat.Prime 318161 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv41,pv97]) (by decide +kernel)
def pv318161 : PrimeValue := ⟨318161, pr318161⟩
private theorem pr318179 : Nat.Prime 318179 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv22727]) (by decide +kernel)
def pv318179 : PrimeValue := ⟨318179, pr318179⟩
private theorem pr318181 : Nat.Prime 318181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv5303]) (by decide +kernel)
def pv318181 : PrimeValue := ⟨318181, pr318181⟩
private theorem pr318191 : Nat.Prime 318191 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv47,pv677]) (by decide +kernel)
def pv318191 : PrimeValue := ⟨318191, pr318191⟩
private theorem pr318203 : Nat.Prime 318203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv389,pv409]) (by decide +kernel)
def pv318203 : PrimeValue := ⟨318203, pr318203⟩
private theorem pr318211 : Nat.Prime 318211 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv10607]) (by decide +kernel)
def pv318211 : PrimeValue := ⟨318211, pr318211⟩
private theorem pr318229 : Nat.Prime 318229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv1153]) (by decide +kernel)
def pv318229 : PrimeValue := ⟨318229, pr318229⟩
private theorem pr318233 : Nat.Prime 318233 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv39779]) (by decide +kernel)
def pv318233 : PrimeValue := ⟨318233, pr318233⟩
private theorem pr318247 : Nat.Prime 318247 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29,pv31,pv59]) (by decide +kernel)
def pv318247 : PrimeValue := ⟨318247, pr318247⟩
private theorem pr318259 : Nat.Prime 318259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17681]) (by decide +kernel)
def pv318259 : PrimeValue := ⟨318259, pr318259⟩
private theorem pr318281 : Nat.Prime 318281 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv73,pv109]) (by decide +kernel)
def pv318281 : PrimeValue := ⟨318281, pr318281⟩
private theorem pr318289 : Nat.Prime 318289 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv19,pv349]) (by decide +kernel)
def pv318289 : PrimeValue := ⟨318289, pr318289⟩
private theorem pr318299 : Nat.Prime 318299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv2609]) (by decide +kernel)
def pv318299 : PrimeValue := ⟨318299, pr318299⟩
private theorem pr318301 : Nat.Prime 318301 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1061]) (by decide +kernel)
def pv318301 : PrimeValue := ⟨318301, pr318301⟩
private theorem pr318337 : Nat.Prime 318337 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv829]) (by decide +kernel)
def pv318337 : PrimeValue := ⟨318337, pr318337⟩
private theorem pr318347 : Nat.Prime 318347 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv22739]) (by decide +kernel)
def pv318347 : PrimeValue := ⟨318347, pr318347⟩
private theorem pr318349 : Nat.Prime 318349 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv239]) (by decide +kernel)
def pv318349 : PrimeValue := ⟨318349, pr318349⟩
private theorem pr318377 : Nat.Prime 318377 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv2341]) (by decide +kernel)
def pv318377 : PrimeValue := ⟨318377, pr318377⟩
private theorem pr318407 : Nat.Prime 318407 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv41,pv353]) (by decide +kernel)
def pv318407 : PrimeValue := ⟨318407, pr318407⟩
private theorem pr318431 : Nat.Prime 318431 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv4549]) (by decide +kernel)
def pv318431 : PrimeValue := ⟨318431, pr318431⟩
private theorem pr318473 : Nat.Prime 318473 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv7,pv11,pv47]) (by decide +kernel)
def pv318473 : PrimeValue := ⟨318473, pr318473⟩
private theorem pr318569 : Nat.Prime 318569 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv39821]) (by decide +kernel)
def pv318569 : PrimeValue := ⟨318569, pr318569⟩
private theorem pr318581 : Nat.Prime 318581 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv937]) (by decide +kernel)
def pv318581 : PrimeValue := ⟨318581, pr318581⟩
private theorem pr318601 : Nat.Prime 318601 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv59]) (by decide +kernel)
def pv318601 : PrimeValue := ⟨318601, pr318601⟩
private theorem pr318641 : Nat.Prime 318641 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv569]) (by decide +kernel)
def pv318641 : PrimeValue := ⟨318641, pr318641⟩
private theorem pr318653 : Nat.Prime 318653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv41,pv67]) (by decide +kernel)
def pv318653 : PrimeValue := ⟨318653, pr318653⟩
private theorem pr318671 : Nat.Prime 318671 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv11,pv2897]) (by decide +kernel)
def pv318671 : PrimeValue := ⟨318671, pr318671⟩
private theorem pr318677 : Nat.Prime 318677 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79669]) (by decide +kernel)
def pv318677 : PrimeValue := ⟨318677, pr318677⟩
private theorem pr318679 : Nat.Prime 318679 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv53113]) (by decide +kernel)
def pv318679 : PrimeValue := ⟨318679, pr318679⟩
private theorem pr318691 : Nat.Prime 318691 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv3541]) (by decide +kernel)
def pv318691 : PrimeValue := ⟨318691, pr318691⟩
private theorem pr318737 : Nat.Prime 318737 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv1811]) (by decide +kernel)
def pv318737 : PrimeValue := ⟨318737, pr318737⟩
private theorem pr318743 : Nat.Prime 318743 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv31,pv53,pv97]) (by decide +kernel)
def pv318743 : PrimeValue := ⟨318743, pr318743⟩
private theorem pr318749 : Nat.Prime 318749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79687]) (by decide +kernel)
def pv318749 : PrimeValue := ⟨318749, pr318749⟩
private theorem pr318751 : Nat.Prime 318751 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv318751 : PrimeValue := ⟨318751, pr318751⟩
private theorem pr318793 : Nat.Prime 318793 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv37,pv359]) (by decide +kernel)
def pv318793 : PrimeValue := ⟨318793, pr318793⟩
private theorem pr318817 : Nat.Prime 318817 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv41]) (by decide +kernel)
def pv318817 : PrimeValue := ⟨318817, pr318817⟩
private theorem pr318823 : Nat.Prime 318823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv7591]) (by decide +kernel)
def pv318823 : PrimeValue := ⟨318823, pr318823⟩
private theorem pr318841 : Nat.Prime 318841 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv2657]) (by decide +kernel)
def pv318841 : PrimeValue := ⟨318841, pr318841⟩
private theorem pr318863 : Nat.Prime 318863 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv159431]) (by decide +kernel)
def pv318863 : PrimeValue := ⟨318863, pr318863⟩
private theorem pr318881 : Nat.Prime 318881 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv1993]) (by decide +kernel)
def pv318881 : PrimeValue := ⟨318881, pr318881⟩
private theorem pr318883 : Nat.Prime 318883 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv53147]) (by decide +kernel)
def pv318883 : PrimeValue := ⟨318883, pr318883⟩
private theorem pr318911 : Nat.Prime 318911 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv31891]) (by decide +kernel)
def pv318911 : PrimeValue := ⟨318911, pr318911⟩
private theorem pr318919 : Nat.Prime 318919 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv23,pv2311]) (by decide +kernel)
def pv318919 : PrimeValue := ⟨318919, pr318919⟩
private theorem pr318949 : Nat.Prime 318949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv3797]) (by decide +kernel)
def pv318949 : PrimeValue := ⟨318949, pr318949⟩
private theorem pr319001 : Nat.Prime 319001 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv29]) (by decide +kernel)
def pv319001 : PrimeValue := ⟨319001, pr319001⟩
private theorem pr319027 : Nat.Prime 319027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv53171]) (by decide +kernel)
def pv319027 : PrimeValue := ⟨319027, pr319027⟩
private theorem pr319031 : Nat.Prime 319031 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv61,pv523]) (by decide +kernel)
def pv319031 : PrimeValue := ⟨319031, pr319031⟩
private theorem pr319049 : Nat.Prime 319049 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv2099]) (by decide +kernel)
def pv319049 : PrimeValue := ⟨319049, pr319049⟩
private theorem pr319057 : Nat.Prime 319057 :=
  checkPrime_prime (q := pv67) (ls := [pv2,pv3,pv17,pv23]) (by decide +kernel)
def pv319057 : PrimeValue := ⟨319057, pr319057⟩
private theorem pr319061 : Nat.Prime 319061 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv43,pv53]) (by decide +kernel)
def pv319061 : PrimeValue := ⟨319061, pr319061⟩
private theorem pr319097 : Nat.Prime 319097 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv39887]) (by decide +kernel)
def pv319097 : PrimeValue := ⟨319097, pr319097⟩
private theorem pr319127 : Nat.Prime 319127 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv159563]) (by decide +kernel)
def pv319127 : PrimeValue := ⟨319127, pr319127⟩
private theorem pr319147 : Nat.Prime 319147 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv43,pv1237]) (by decide +kernel)
def pv319147 : PrimeValue := ⟨319147, pr319147⟩
private theorem pr319159 : Nat.Prime 319159 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv17,pv149]) (by decide +kernel)
def pv319159 : PrimeValue := ⟨319159, pr319159⟩
private theorem pr319183 : Nat.Prime 319183 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv53197]) (by decide +kernel)
def pv319183 : PrimeValue := ⟨319183, pr319183⟩
private theorem pr319211 : Nat.Prime 319211 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv137,pv233]) (by decide +kernel)
def pv319211 : PrimeValue := ⟨319211, pr319211⟩
private theorem pr319237 : Nat.Prime 319237 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv719]) (by decide +kernel)
def pv319237 : PrimeValue := ⟨319237, pr319237⟩
private theorem pr319289 : Nat.Prime 319289 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv107,pv373]) (by decide +kernel)
def pv319289 : PrimeValue := ⟨319289, pr319289⟩
private theorem pr319327 : Nat.Prime 319327 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv7603]) (by decide +kernel)
def pv319327 : PrimeValue := ⟨319327, pr319327⟩
private theorem pr319339 : Nat.Prime 319339 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv113,pv157]) (by decide +kernel)
def pv319339 : PrimeValue := ⟨319339, pr319339⟩
private theorem pr319351 : Nat.Prime 319351 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv2129]) (by decide +kernel)
def pv319351 : PrimeValue := ⟨319351, pr319351⟩
private theorem pr319357 : Nat.Prime 319357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2957]) (by decide +kernel)
def pv319357 : PrimeValue := ⟨319357, pr319357⟩
private theorem pr319387 : Nat.Prime 319387 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv53231]) (by decide +kernel)
def pv319387 : PrimeValue := ⟨319387, pr319387⟩
private theorem pr319391 : Nat.Prime 319391 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv19,pv41]) (by decide +kernel)
def pv319391 : PrimeValue := ⟨319391, pr319391⟩
private theorem pr319399 : Nat.Prime 319399 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv53233]) (by decide +kernel)
def pv319399 : PrimeValue := ⟨319399, pr319399⟩
private theorem pr319411 : Nat.Prime 319411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv13]) (by decide +kernel)
def pv319411 : PrimeValue := ⟨319411, pr319411⟩
private theorem pr319433 : Nat.Prime 319433 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv39929]) (by decide +kernel)
def pv319433 : PrimeValue := ⟨319433, pr319433⟩
private theorem pr319441 : Nat.Prime 319441 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv319441 : PrimeValue := ⟨319441, pr319441⟩
private theorem pr319453 : Nat.Prime 319453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv3803]) (by decide +kernel)
def pv319453 : PrimeValue := ⟨319453, pr319453⟩
private theorem pr319469 : Nat.Prime 319469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79867]) (by decide +kernel)
def pv319469 : PrimeValue := ⟨319469, pr319469⟩
private theorem pr319477 : Nat.Prime 319477 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv79,pv337]) (by decide +kernel)
def pv319477 : PrimeValue := ⟨319477, pr319477⟩
private theorem pr319489 : Nat.Prime 319489 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv319489 : PrimeValue := ⟨319489, pr319489⟩
private theorem pr319499 : Nat.Prime 319499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv9397]) (by decide +kernel)
def pv319499 : PrimeValue := ⟨319499, pr319499⟩
private theorem pr319541 : Nat.Prime 319541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv1229]) (by decide +kernel)
def pv319541 : PrimeValue := ⟨319541, pr319541⟩
private theorem pr319577 : Nat.Prime 319577 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv43,pv929]) (by decide +kernel)
def pv319577 : PrimeValue := ⟨319577, pr319577⟩
private theorem pr319589 : Nat.Prime 319589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv109,pv733]) (by decide +kernel)
def pv319589 : PrimeValue := ⟨319589, pr319589⟩
private theorem pr319591 : Nat.Prime 319591 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv53,pv67]) (by decide +kernel)
def pv319591 : PrimeValue := ⟨319591, pr319591⟩
private theorem pr319607 : Nat.Prime 319607 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv37,pv617]) (by decide +kernel)
def pv319607 : PrimeValue := ⟨319607, pr319607⟩
private theorem pr319679 : Nat.Prime 319679 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv159839]) (by decide +kernel)
def pv319679 : PrimeValue := ⟨319679, pr319679⟩
private theorem pr319681 : Nat.Prime 319681 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv37]) (by decide +kernel)
def pv319681 : PrimeValue := ⟨319681, pr319681⟩
private theorem pr319687 : Nat.Prime 319687 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv53281]) (by decide +kernel)
def pv319687 : PrimeValue := ⟨319687, pr319687⟩
private theorem pr319727 : Nat.Prime 319727 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv14533]) (by decide +kernel)
def pv319727 : PrimeValue := ⟨319727, pr319727⟩
private theorem pr319811 : Nat.Prime 319811 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv31981]) (by decide +kernel)
def pv319811 : PrimeValue := ⟨319811, pr319811⟩
private theorem pr319819 : Nat.Prime 319819 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv151,pv353]) (by decide +kernel)
def pv319819 : PrimeValue := ⟨319819, pr319819⟩
private theorem pr319883 : Nat.Prime 319883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv47,pv83]) (by decide +kernel)
def pv319883 : PrimeValue := ⟨319883, pr319883⟩
private theorem pr319897 : Nat.Prime 319897 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv1481]) (by decide +kernel)
def pv319897 : PrimeValue := ⟨319897, pr319897⟩
private theorem pr319919 : Nat.Prime 319919 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv103,pv1553]) (by decide +kernel)
def pv319919 : PrimeValue := ⟨319919, pr319919⟩
private theorem pr319931 : Nat.Prime 319931 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv13,pv23,pv107]) (by decide +kernel)
def pv319931 : PrimeValue := ⟨319931, pr319931⟩
private theorem pr319937 : Nat.Prime 319937 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv4999]) (by decide +kernel)
def pv319937 : PrimeValue := ⟨319937, pr319937⟩
private theorem pr319973 : Nat.Prime 319973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv167,pv479]) (by decide +kernel)
def pv319973 : PrimeValue := ⟨319973, pr319973⟩
private theorem pr319981 : Nat.Prime 319981 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv5333]) (by decide +kernel)
def pv319981 : PrimeValue := ⟨319981, pr319981⟩
private theorem pr319993 : Nat.Prime 319993 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv67,pv199]) (by decide +kernel)
def pv319993 : PrimeValue := ⟨319993, pr319993⟩
private theorem pr320009 : Nat.Prime 320009 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv17,pv181]) (by decide +kernel)
def pv320009 : PrimeValue := ⟨320009, pr320009⟩
private theorem pr320011 : Nat.Prime 320011 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv10667]) (by decide +kernel)
def pv320011 : PrimeValue := ⟨320011, pr320011⟩
private theorem pr320057 : Nat.Prime 320057 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv3637]) (by decide +kernel)
def pv320057 : PrimeValue := ⟨320057, pr320057⟩
private theorem pr320063 : Nat.Prime 320063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv160031]) (by decide +kernel)
def pv320063 : PrimeValue := ⟨320063, pr320063⟩
private theorem pr320081 : Nat.Prime 320081 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv4001]) (by decide +kernel)
def pv320081 : PrimeValue := ⟨320081, pr320081⟩
private theorem pr320083 : Nat.Prime 320083 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv7621]) (by decide +kernel)
def pv320083 : PrimeValue := ⟨320083, pr320083⟩
private theorem pr320113 : Nat.Prime 320113 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv19]) (by decide +kernel)
def pv320113 : PrimeValue := ⟨320113, pr320113⟩
private theorem pr320141 : Nat.Prime 320141 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv16007]) (by decide +kernel)
def pv320141 : PrimeValue := ⟨320141, pr320141⟩
private theorem pr320143 : Nat.Prime 320143 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv229,pv233]) (by decide +kernel)
def pv320143 : PrimeValue := ⟨320143, pr320143⟩
private theorem pr320149 : Nat.Prime 320149 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv8893]) (by decide +kernel)
def pv320149 : PrimeValue := ⟨320149, pr320149⟩
private theorem pr320153 : Nat.Prime 320153 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv5717]) (by decide +kernel)
def pv320153 : PrimeValue := ⟨320153, pr320153⟩
private theorem pr320209 : Nat.Prime 320209 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv953]) (by decide +kernel)
def pv320209 : PrimeValue := ⟨320209, pr320209⟩
private theorem pr320219 : Nat.Prime 320219 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv29,pv5521]) (by decide +kernel)
def pv320219 : PrimeValue := ⟨320219, pr320219⟩
private theorem pr320239 : Nat.Prime 320239 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17791]) (by decide +kernel)
def pv320239 : PrimeValue := ⟨320239, pr320239⟩
private theorem pr320269 : Nat.Prime 320269 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv2053]) (by decide +kernel)
def pv320269 : PrimeValue := ⟨320269, pr320269⟩
private theorem pr320291 : Nat.Prime 320291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv32029]) (by decide +kernel)
def pv320291 : PrimeValue := ⟨320291, pr320291⟩
private theorem pr320303 : Nat.Prime 320303 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv8429]) (by decide +kernel)
def pv320303 : PrimeValue := ⟨320303, pr320303⟩
private theorem pr320329 : Nat.Prime 320329 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv1483]) (by decide +kernel)
def pv320329 : PrimeValue := ⟨320329, pr320329⟩
private theorem pr320339 : Nat.Prime 320339 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv160169]) (by decide +kernel)
def pv320339 : PrimeValue := ⟨320339, pr320339⟩
private theorem pr320377 : Nat.Prime 320377 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv1907]) (by decide +kernel)
def pv320377 : PrimeValue := ⟨320377, pr320377⟩
private theorem pr320401 : Nat.Prime 320401 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv89]) (by decide +kernel)
def pv320401 : PrimeValue := ⟨320401, pr320401⟩
private theorem pr320471 : Nat.Prime 320471 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv73,pv439]) (by decide +kernel)
def pv320471 : PrimeValue := ⟨320471, pr320471⟩
private theorem pr320477 : Nat.Prime 320477 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv6163]) (by decide +kernel)
def pv320477 : PrimeValue := ⟨320477, pr320477⟩
private theorem pr320483 : Nat.Prime 320483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv6967]) (by decide +kernel)
def pv320483 : PrimeValue := ⟨320483, pr320483⟩
private theorem pr320513 : Nat.Prime 320513 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv313]) (by decide +kernel)
def pv320513 : PrimeValue := ⟨320513, pr320513⟩
private theorem pr320521 : Nat.Prime 320521 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv2671]) (by decide +kernel)
def pv320521 : PrimeValue := ⟨320521, pr320521⟩
private theorem pr320533 : Nat.Prime 320533 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv26711]) (by decide +kernel)
def pv320533 : PrimeValue := ⟨320533, pr320533⟩
private theorem pr320561 : Nat.Prime 320561 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv4007]) (by decide +kernel)
def pv320561 : PrimeValue := ⟨320561, pr320561⟩
private theorem pr320591 : Nat.Prime 320591 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv32059]) (by decide +kernel)
def pv320591 : PrimeValue := ⟨320591, pr320591⟩
private theorem pr320627 : Nat.Prime 320627 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv160313]) (by decide +kernel)
def pv320627 : PrimeValue := ⟨320627, pr320627⟩
private theorem pr320647 : Nat.Prime 320647 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv53441]) (by decide +kernel)
def pv320647 : PrimeValue := ⟨320647, pr320647⟩
private theorem pr320657 : Nat.Prime 320657 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv409]) (by decide +kernel)
def pv320657 : PrimeValue := ⟨320657, pr320657⟩
private theorem pr320659 : Nat.Prime 320659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv4111]) (by decide +kernel)
def pv320659 : PrimeValue := ⟨320659, pr320659⟩
private theorem pr320693 : Nat.Prime 320693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv80173]) (by decide +kernel)
def pv320693 : PrimeValue := ⟨320693, pr320693⟩
private theorem pr320699 : Nat.Prime 320699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv22907]) (by decide +kernel)
def pv320699 : PrimeValue := ⟨320699, pr320699⟩
private theorem pr320759 : Nat.Prime 320759 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv19,pv23,pv367]) (by decide +kernel)
def pv320759 : PrimeValue := ⟨320759, pr320759⟩
private theorem pr320767 : Nat.Prime 320767 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv193,pv277]) (by decide +kernel)
def pv320767 : PrimeValue := ⟨320767, pr320767⟩
private theorem pr320821 : Nat.Prime 320821 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv5347]) (by decide +kernel)
def pv320821 : PrimeValue := ⟨320821, pr320821⟩
private theorem pr320833 : Nat.Prime 320833 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv557]) (by decide +kernel)
def pv320833 : PrimeValue := ⟨320833, pr320833⟩
private theorem pr320843 : Nat.Prime 320843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv59,pv2719]) (by decide +kernel)
def pv320843 : PrimeValue := ⟨320843, pr320843⟩
private theorem pr320923 : Nat.Prime 320923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv283]) (by decide +kernel)
def pv320923 : PrimeValue := ⟨320923, pr320923⟩
private theorem pr320927 : Nat.Prime 320927 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv9439]) (by decide +kernel)
def pv320927 : PrimeValue := ⟨320927, pr320927⟩
private theorem pr320953 : Nat.Prime 320953 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv43,pv311]) (by decide +kernel)
def pv320953 : PrimeValue := ⟨320953, pr320953⟩
private theorem pr321031 : Nat.Prime 321031 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv29,pv41]) (by decide +kernel)
def pv321031 : PrimeValue := ⟨321031, pr321031⟩
private theorem pr321037 : Nat.Prime 321037 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv863]) (by decide +kernel)
def pv321037 : PrimeValue := ⟨321037, pr321037⟩
private theorem pr321047 : Nat.Prime 321047 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv14593]) (by decide +kernel)
def pv321047 : PrimeValue := ⟨321047, pr321047⟩
private theorem pr321073 : Nat.Prime 321073 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv6689]) (by decide +kernel)
def pv321073 : PrimeValue := ⟨321073, pr321073⟩
private theorem pr321203 : Nat.Prime 321203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv22943]) (by decide +kernel)
def pv321203 : PrimeValue := ⟨321203, pr321203⟩
private theorem pr321221 : Nat.Prime 321221 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv16061]) (by decide +kernel)
def pv321221 : PrimeValue := ⟨321221, pr321221⟩
private theorem pr321227 : Nat.Prime 321227 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv2633]) (by decide +kernel)
def pv321227 : PrimeValue := ⟨321227, pr321227⟩
private theorem pr321247 : Nat.Prime 321247 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv661]) (by decide +kernel)
def pv321247 : PrimeValue := ⟨321247, pr321247⟩
private theorem pr321301 : Nat.Prime 321301 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv17]) (by decide +kernel)
def pv321301 : PrimeValue := ⟨321301, pr321301⟩
private theorem pr321311 : Nat.Prime 321311 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv11,pv23,pv127]) (by decide +kernel)
def pv321311 : PrimeValue := ⟨321311, pr321311⟩
private theorem pr321313 : Nat.Prime 321313 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv3347]) (by decide +kernel)
def pv321313 : PrimeValue := ⟨321313, pr321313⟩
private theorem pr321341 : Nat.Prime 321341 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv16067]) (by decide +kernel)
def pv321341 : PrimeValue := ⟨321341, pr321341⟩
private theorem pr321367 : Nat.Prime 321367 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv2819]) (by decide +kernel)
def pv321367 : PrimeValue := ⟨321367, pr321367⟩
private theorem pr321371 : Nat.Prime 321371 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv4591]) (by decide +kernel)
def pv321371 : PrimeValue := ⟨321371, pr321371⟩
private theorem pr321397 : Nat.Prime 321397 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv26783]) (by decide +kernel)
def pv321397 : PrimeValue := ⟨321397, pr321397⟩
private theorem pr321403 : Nat.Prime 321403 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv17,pv23,pv137]) (by decide +kernel)
def pv321403 : PrimeValue := ⟨321403, pr321403⟩
private theorem pr321427 : Nat.Prime 321427 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv2551]) (by decide +kernel)
def pv321427 : PrimeValue := ⟨321427, pr321427⟩
private theorem pr321443 : Nat.Prime 321443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv19,pv769]) (by decide +kernel)
def pv321443 : PrimeValue := ⟨321443, pr321443⟩
private theorem pr321449 : Nat.Prime 321449 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv1747]) (by decide +kernel)
def pv321449 : PrimeValue := ⟨321449, pr321449⟩
private theorem pr321469 : Nat.Prime 321469 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv43,pv89]) (by decide +kernel)
def pv321469 : PrimeValue := ⟨321469, pr321469⟩
private theorem pr321547 : Nat.Prime 321547 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv53591]) (by decide +kernel)
def pv321547 : PrimeValue := ⟨321547, pr321547⟩
private theorem pr321571 : Nat.Prime 321571 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv397]) (by decide +kernel)
def pv321571 : PrimeValue := ⟨321571, pr321571⟩
private theorem pr321593 : Nat.Prime 321593 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv61,pv659]) (by decide +kernel)
def pv321593 : PrimeValue := ⟨321593, pr321593⟩
private theorem pr321617 : Nat.Prime 321617 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv20101]) (by decide +kernel)
def pv321617 : PrimeValue := ⟨321617, pr321617⟩
private theorem pr321661 : Nat.Prime 321661 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1787]) (by decide +kernel)
def pv321661 : PrimeValue := ⟨321661, pr321661⟩
private theorem pr321707 : Nat.Prime 321707 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv2089]) (by decide +kernel)
def pv321707 : PrimeValue := ⟨321707, pr321707⟩
private theorem pr321709 : Nat.Prime 321709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv19,pv83]) (by decide +kernel)
def pv321709 : PrimeValue := ⟨321709, pr321709⟩
private theorem pr321757 : Nat.Prime 321757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv26813]) (by decide +kernel)
def pv321757 : PrimeValue := ⟨321757, pr321757⟩
private theorem pr321779 : Nat.Prime 321779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv349,pv461]) (by decide +kernel)
def pv321779 : PrimeValue := ⟨321779, pr321779⟩
private theorem pr321799 : Nat.Prime 321799 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv53633]) (by decide +kernel)
def pv321799 : PrimeValue := ⟨321799, pr321799⟩
private theorem pr321821 : Nat.Prime 321821 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv16091]) (by decide +kernel)
def pv321821 : PrimeValue := ⟨321821, pr321821⟩
private theorem pr321823 : Nat.Prime 321823 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv941]) (by decide +kernel)
def pv321823 : PrimeValue := ⟨321823, pr321823⟩
private theorem pr321847 : Nat.Prime 321847 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv79,pv97]) (by decide +kernel)
def pv321847 : PrimeValue := ⟨321847, pr321847⟩
private theorem pr321851 : Nat.Prime 321851 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv41,pv157]) (by decide +kernel)
def pv321851 : PrimeValue := ⟨321851, pr321851⟩
private theorem pr321911 : Nat.Prime 321911 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv32191]) (by decide +kernel)
def pv321911 : PrimeValue := ⟨321911, pr321911⟩
private theorem pr322009 : Nat.Prime 322009 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv13417]) (by decide +kernel)
def pv322009 : PrimeValue := ⟨322009, pr322009⟩
private theorem pr322037 : Nat.Prime 322037 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv13,pv563]) (by decide +kernel)
def pv322037 : PrimeValue := ⟨322037, pr322037⟩
private theorem pr322073 : Nat.Prime 322073 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv127,pv317]) (by decide +kernel)
def pv322073 : PrimeValue := ⟨322073, pr322073⟩
private theorem pr322079 : Nat.Prime 322079 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv161039]) (by decide +kernel)
def pv322079 : PrimeValue := ⟨322079, pr322079⟩
private theorem pr322111 : Nat.Prime 322111 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv1193]) (by decide +kernel)
def pv322111 : PrimeValue := ⟨322111, pr322111⟩
private theorem pr322193 : Nat.Prime 322193 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv1549]) (by decide +kernel)
def pv322193 : PrimeValue := ⟨322193, pr322193⟩
private theorem pr322213 : Nat.Prime 322213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv2441]) (by decide +kernel)
def pv322213 : PrimeValue := ⟨322213, pr322213⟩
private theorem pr322229 : Nat.Prime 322229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv80557]) (by decide +kernel)
def pv322229 : PrimeValue := ⟨322229, pr322229⟩
private theorem pr322237 : Nat.Prime 322237 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv8951]) (by decide +kernel)
def pv322237 : PrimeValue := ⟨322237, pr322237⟩
private theorem pr322249 : Nat.Prime 322249 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv29,pv463]) (by decide +kernel)
def pv322249 : PrimeValue := ⟨322249, pr322249⟩
private theorem pr322339 : Nat.Prime 322339 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv1733]) (by decide +kernel)
def pv322339 : PrimeValue := ⟨322339, pr322339⟩
private theorem pr322397 : Nat.Prime 322397 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv80599]) (by decide +kernel)
def pv322397 : PrimeValue := ⟨322397, pr322397⟩
private theorem pr322403 : Nat.Prime 322403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv161201]) (by decide +kernel)
def pv322403 : PrimeValue := ⟨322403, pr322403⟩
private theorem pr322409 : Nat.Prime 322409 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv191,pv211]) (by decide +kernel)
def pv322409 : PrimeValue := ⟨322409, pr322409⟩
private theorem pr322417 : Nat.Prime 322417 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2239]) (by decide +kernel)
def pv322417 : PrimeValue := ⟨322417, pr322417⟩
private theorem pr322433 : Nat.Prime 322433 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv229]) (by decide +kernel)
def pv322433 : PrimeValue := ⟨322433, pr322433⟩
private theorem pr322459 : Nat.Prime 322459 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv223,pv241]) (by decide +kernel)
def pv322459 : PrimeValue := ⟨322459, pr322459⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
