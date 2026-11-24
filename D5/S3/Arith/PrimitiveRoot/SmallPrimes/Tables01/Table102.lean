/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table102
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table102.pv421133
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table010
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table017
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table027
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table028
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table068

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr421133 : Nat.Prime 421133 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv127,pv829]) (by decide +kernel)
def pv421133 : PrimeValue := ⟨421133, pr421133⟩
private theorem pr421147 : Nat.Prime 421147 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv709]) (by decide +kernel)
def pv421147 : PrimeValue := ⟨421147, pr421147⟩
private theorem pr421181 : Nat.Prime 421181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv21059]) (by decide +kernel)
def pv421181 : PrimeValue := ⟨421181, pr421181⟩
private theorem pr421207 : Nat.Prime 421207 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv70201]) (by decide +kernel)
def pv421207 : PrimeValue := ⟨421207, pr421207⟩
private theorem pr421241 : Nat.Prime 421241 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv10531]) (by decide +kernel)
def pv421241 : PrimeValue := ⟨421241, pr421241⟩
private theorem pr421273 : Nat.Prime 421273 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5851]) (by decide +kernel)
def pv421273 : PrimeValue := ⟨421273, pr421273⟩
private theorem pr421313 : Nat.Prime 421313 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv227]) (by decide +kernel)
def pv421313 : PrimeValue := ⟨421313, pr421313⟩
private theorem pr421331 : Nat.Prime 421331 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv13,pv463]) (by decide +kernel)
def pv421331 : PrimeValue := ⟨421331, pr421331⟩
private theorem pr421361 : Nat.Prime 421361 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv23,pv229]) (by decide +kernel)
def pv421361 : PrimeValue := ⟨421361, pr421361⟩
private theorem pr421409 : Nat.Prime 421409 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv1013]) (by decide +kernel)
def pv421409 : PrimeValue := ⟨421409, pr421409⟩
private theorem pr421417 : Nat.Prime 421417 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1951]) (by decide +kernel)
def pv421417 : PrimeValue := ⟨421417, pr421417⟩
private theorem pr421433 : Nat.Prime 421433 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv4789]) (by decide +kernel)
def pv421433 : PrimeValue := ⟨421433, pr421433⟩
private theorem pr421459 : Nat.Prime 421459 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv3697]) (by decide +kernel)
def pv421459 : PrimeValue := ⟨421459, pr421459⟩
private theorem pr421469 : Nat.Prime 421469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv105367]) (by decide +kernel)
def pv421469 : PrimeValue := ⟨421469, pr421469⟩
private theorem pr421483 : Nat.Prime 421483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv199,pv353]) (by decide +kernel)
def pv421483 : PrimeValue := ⟨421483, pr421483⟩
private theorem pr421493 : Nat.Prime 421493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv105373]) (by decide +kernel)
def pv421493 : PrimeValue := ⟨421493, pr421493⟩
private theorem pr421607 : Nat.Prime 421607 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv210803]) (by decide +kernel)
def pv421607 : PrimeValue := ⟨421607, pr421607⟩
private theorem pr421633 : Nat.Prime 421633 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv61]) (by decide +kernel)
def pv421633 : PrimeValue := ⟨421633, pr421633⟩
private theorem pr421661 : Nat.Prime 421661 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv29,pv727]) (by decide +kernel)
def pv421661 : PrimeValue := ⟨421661, pr421661⟩
private theorem pr421691 : Nat.Prime 421691 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv42169]) (by decide +kernel)
def pv421691 : PrimeValue := ⟨421691, pr421691⟩
private theorem pr421711 : Nat.Prime 421711 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv14057]) (by decide +kernel)
def pv421711 : PrimeValue := ⟨421711, pr421711⟩
private theorem pr421783 : Nat.Prime 421783 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv70297]) (by decide +kernel)
def pv421783 : PrimeValue := ⟨421783, pr421783⟩
private theorem pr421831 : Nat.Prime 421831 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv43,pv109]) (by decide +kernel)
def pv421831 : PrimeValue := ⟨421831, pr421831⟩
private theorem pr421847 : Nat.Prime 421847 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv210923]) (by decide +kernel)
def pv421847 : PrimeValue := ⟨421847, pr421847⟩
private theorem pr421907 : Nat.Prime 421907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv12409]) (by decide +kernel)
def pv421907 : PrimeValue := ⟨421907, pr421907⟩
private theorem pr421987 : Nat.Prime 421987 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv53,pv1327]) (by decide +kernel)
def pv421987 : PrimeValue := ⟨421987, pr421987⟩
private theorem pr421997 : Nat.Prime 421997 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv105499]) (by decide +kernel)
def pv421997 : PrimeValue := ⟨421997, pr421997⟩
private theorem pr422063 : Nat.Prime 422063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv281,pv751]) (by decide +kernel)
def pv422063 : PrimeValue := ⟨422063, pr422063⟩
private theorem pr422069 : Nat.Prime 422069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv105517]) (by decide +kernel)
def pv422069 : PrimeValue := ⟨422069, pr422069⟩
private theorem pr422099 : Nat.Prime 422099 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv211049]) (by decide +kernel)
def pv422099 : PrimeValue := ⟨422099, pr422099⟩
private theorem pr422137 : Nat.Prime 422137 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv13,pv41]) (by decide +kernel)
def pv422137 : PrimeValue := ⟨422137, pr422137⟩
private theorem pr422209 : Nat.Prime 422209 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv733]) (by decide +kernel)
def pv422209 : PrimeValue := ⟨422209, pr422209⟩
private theorem pr422231 : Nat.Prime 422231 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv5,pv42223]) (by decide +kernel)
def pv422231 : PrimeValue := ⟨422231, pr422231⟩
private theorem pr422249 : Nat.Prime 422249 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv47,pv1123]) (by decide +kernel)
def pv422249 : PrimeValue := ⟨422249, pr422249⟩
private theorem pr422291 : Nat.Prime 422291 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv11,pv349]) (by decide +kernel)
def pv422291 : PrimeValue := ⟨422291, pr422291⟩
private theorem pr422309 : Nat.Prime 422309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv71,pv1487]) (by decide +kernel)
def pv422309 : PrimeValue := ⟨422309, pr422309⟩
private theorem pr422321 : Nat.Prime 422321 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv5279]) (by decide +kernel)
def pv422321 : PrimeValue := ⟨422321, pr422321⟩
private theorem pr422363 : Nat.Prime 422363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv223,pv947]) (by decide +kernel)
def pv422363 : PrimeValue := ⟨422363, pr422363⟩
private theorem pr422407 : Nat.Prime 422407 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv31,pv757]) (by decide +kernel)
def pv422407 : PrimeValue := ⟨422407, pr422407⟩
private theorem pr422537 : Nat.Prime 422537 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv52817]) (by decide +kernel)
def pv422537 : PrimeValue := ⟨422537, pr422537⟩
private theorem pr422549 : Nat.Prime 422549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv15091]) (by decide +kernel)
def pv422549 : PrimeValue := ⟨422549, pr422549⟩
private theorem pr422551 : Nat.Prime 422551 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv313]) (by decide +kernel)
def pv422551 : PrimeValue := ⟨422551, pr422551⟩
private theorem pr422557 : Nat.Prime 422557 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv1531]) (by decide +kernel)
def pv422557 : PrimeValue := ⟨422557, pr422557⟩
private theorem pr422563 : Nat.Prime 422563 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv10061]) (by decide +kernel)
def pv422563 : PrimeValue := ⟨422563, pr422563⟩
private theorem pr422581 : Nat.Prime 422581 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7043]) (by decide +kernel)
def pv422581 : PrimeValue := ⟨422581, pr422581⟩
private theorem pr422621 : Nat.Prime 422621 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv17,pv113]) (by decide +kernel)
def pv422621 : PrimeValue := ⟨422621, pr422621⟩
private theorem pr422627 : Nat.Prime 422627 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv211313]) (by decide +kernel)
def pv422627 : PrimeValue := ⟨422627, pr422627⟩
private theorem pr422689 : Nat.Prime 422689 :=
  checkPrime_prime (q := pv53) (ls := [pv2,pv3,pv7,pv17,pv37]) (by decide +kernel)
def pv422689 : PrimeValue := ⟨422689, pr422689⟩
private theorem pr422707 : Nat.Prime 422707 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv70451]) (by decide +kernel)
def pv422707 : PrimeValue := ⟨422707, pr422707⟩
private theorem pr422711 : Nat.Prime 422711 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv41,pv1031]) (by decide +kernel)
def pv422711 : PrimeValue := ⟨422711, pr422711⟩
private theorem pr422797 : Nat.Prime 422797 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv3203]) (by decide +kernel)
def pv422797 : PrimeValue := ⟨422797, pr422797⟩
private theorem pr422803 : Nat.Prime 422803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv83,pv283]) (by decide +kernel)
def pv422803 : PrimeValue := ⟨422803, pr422803⟩
private theorem pr422857 : Nat.Prime 422857 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv839]) (by decide +kernel)
def pv422857 : PrimeValue := ⟨422857, pr422857⟩
private theorem pr422861 : Nat.Prime 422861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv21143]) (by decide +kernel)
def pv422861 : PrimeValue := ⟨422861, pr422861⟩
private theorem pr422881 : Nat.Prime 422881 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv881]) (by decide +kernel)
def pv422881 : PrimeValue := ⟨422881, pr422881⟩
private theorem pr422911 : Nat.Prime 422911 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv37,pv127]) (by decide +kernel)
def pv422911 : PrimeValue := ⟨422911, pr422911⟩
private theorem pr422923 : Nat.Prime 422923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv70487]) (by decide +kernel)
def pv422923 : PrimeValue := ⟨422923, pr422923⟩
private theorem pr422969 : Nat.Prime 422969 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv13,pv83]) (by decide +kernel)
def pv422969 : PrimeValue := ⟨422969, pr422969⟩
private theorem pr422987 : Nat.Prime 422987 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv211493]) (by decide +kernel)
def pv422987 : PrimeValue := ⟨422987, pr422987⟩
private theorem pr423013 : Nat.Prime 423013 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv35251]) (by decide +kernel)
def pv423013 : PrimeValue := ⟨423013, pr423013⟩
private theorem pr423083 : Nat.Prime 423083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv19231]) (by decide +kernel)
def pv423083 : PrimeValue := ⟨423083, pr423083⟩
private theorem pr423103 : Nat.Prime 423103 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv151,pv467]) (by decide +kernel)
def pv423103 : PrimeValue := ⟨423103, pr423103⟩
private theorem pr423179 : Nat.Prime 423179 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv167,pv181]) (by decide +kernel)
def pv423179 : PrimeValue := ⟨423179, pr423179⟩
private theorem pr423191 : Nat.Prime 423191 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv101,pv419]) (by decide +kernel)
def pv423191 : PrimeValue := ⟨423191, pr423191⟩
private theorem pr423229 : Nat.Prime 423229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv2713]) (by decide +kernel)
def pv423229 : PrimeValue := ⟨423229, pr423229⟩
private theorem pr423233 : Nat.Prime 423233 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv389]) (by decide +kernel)
def pv423233 : PrimeValue := ⟨423233, pr423233⟩
private theorem pr423257 : Nat.Prime 423257 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv191,pv277]) (by decide +kernel)
def pv423257 : PrimeValue := ⟨423257, pr423257⟩
private theorem pr423281 : Nat.Prime 423281 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv13,pv37]) (by decide +kernel)
def pv423281 : PrimeValue := ⟨423281, pr423281⟩
private theorem pr423287 : Nat.Prime 423287 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv211643]) (by decide +kernel)
def pv423287 : PrimeValue := ⟨423287, pr423287⟩
private theorem pr423299 : Nat.Prime 423299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv113,pv1873]) (by decide +kernel)
def pv423299 : PrimeValue := ⟨423299, pr423299⟩
private theorem pr423323 : Nat.Prime 423323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv211661]) (by decide +kernel)
def pv423323 : PrimeValue := ⟨423323, pr423323⟩
private theorem pr423341 : Nat.Prime 423341 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv61,pv347]) (by decide +kernel)
def pv423341 : PrimeValue := ⟨423341, pr423341⟩
private theorem pr423389 : Nat.Prime 423389 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv15121]) (by decide +kernel)
def pv423389 : PrimeValue := ⟨423389, pr423389⟩
private theorem pr423403 : Nat.Prime 423403 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv17,pv593]) (by decide +kernel)
def pv423403 : PrimeValue := ⟨423403, pr423403⟩
private theorem pr423413 : Nat.Prime 423413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv9623]) (by decide +kernel)
def pv423413 : PrimeValue := ⟨423413, pr423413⟩
private theorem pr423427 : Nat.Prime 423427 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv70571]) (by decide +kernel)
def pv423427 : PrimeValue := ⟨423427, pr423427⟩
private theorem pr423457 : Nat.Prime 423457 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv401]) (by decide +kernel)
def pv423457 : PrimeValue := ⟨423457, pr423457⟩
private theorem pr423461 : Nat.Prime 423461 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv31,pv683]) (by decide +kernel)
def pv423461 : PrimeValue := ⟨423461, pr423461⟩
private theorem pr423481 : Nat.Prime 423481 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv3529]) (by decide +kernel)
def pv423481 : PrimeValue := ⟨423481, pr423481⟩
private theorem pr423497 : Nat.Prime 423497 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv52937]) (by decide +kernel)
def pv423497 : PrimeValue := ⟨423497, pr423497⟩
private theorem pr423581 : Nat.Prime 423581 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv21179]) (by decide +kernel)
def pv423581 : PrimeValue := ⟨423581, pr423581⟩
private theorem pr423617 : Nat.Prime 423617 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv6619]) (by decide +kernel)
def pv423617 : PrimeValue := ⟨423617, pr423617⟩
private theorem pr423727 : Nat.Prime 423727 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv70621]) (by decide +kernel)
def pv423727 : PrimeValue := ⟨423727, pr423727⟩
private theorem pr423749 : Nat.Prime 423749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv29,pv281]) (by decide +kernel)
def pv423749 : PrimeValue := ⟨423749, pr423749⟩
private theorem pr423791 : Nat.Prime 423791 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv42379]) (by decide +kernel)
def pv423791 : PrimeValue := ⟨423791, pr423791⟩
private theorem pr423803 : Nat.Prime 423803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv313,pv677]) (by decide +kernel)
def pv423803 : PrimeValue := ⟨423803, pr423803⟩
private theorem pr423823 : Nat.Prime 423823 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv10091]) (by decide +kernel)
def pv423823 : PrimeValue := ⟨423823, pr423823⟩
private theorem pr423853 : Nat.Prime 423853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv13,pv19]) (by decide +kernel)
def pv423853 : PrimeValue := ⟨423853, pr423853⟩
private theorem pr423859 : Nat.Prime 423859 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv41,pv1723]) (by decide +kernel)
def pv423859 : PrimeValue := ⟨423859, pr423859⟩
private theorem pr423869 : Nat.Prime 423869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv105967]) (by decide +kernel)
def pv423869 : PrimeValue := ⟨423869, pr423869⟩
private theorem pr423887 : Nat.Prime 423887 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv211943]) (by decide +kernel)
def pv423887 : PrimeValue := ⟨423887, pr423887⟩
private theorem pr423949 : Nat.Prime 423949 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv7,pv103]) (by decide +kernel)
def pv423949 : PrimeValue := ⟨423949, pr423949⟩
private theorem pr424027 : Nat.Prime 424027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23557]) (by decide +kernel)
def pv424027 : PrimeValue := ⟨424027, pr424027⟩
private theorem pr424079 : Nat.Prime 424079 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv212039]) (by decide +kernel)
def pv424079 : PrimeValue := ⟨424079, pr424079⟩
private theorem pr424091 : Nat.Prime 424091 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv42409]) (by decide +kernel)
def pv424091 : PrimeValue := ⟨424091, pr424091⟩
private theorem pr424129 : Nat.Prime 424129 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv47]) (by decide +kernel)
def pv424129 : PrimeValue := ⟨424129, pr424129⟩
private theorem pr424147 : Nat.Prime 424147 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv223,pv317]) (by decide +kernel)
def pv424147 : PrimeValue := ⟨424147, pr424147⟩
private theorem pr424157 : Nat.Prime 424157 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv5581]) (by decide +kernel)
def pv424157 : PrimeValue := ⟨424157, pr424157⟩
private theorem pr424199 : Nat.Prime 424199 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv212099]) (by decide +kernel)
def pv424199 : PrimeValue := ⟨424199, pr424199⟩
private theorem pr424243 : Nat.Prime 424243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv37]) (by decide +kernel)
def pv424243 : PrimeValue := ⟨424243, pr424243⟩
private theorem pr424267 : Nat.Prime 424267 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv2281]) (by decide +kernel)
def pv424267 : PrimeValue := ⟨424267, pr424267⟩
private theorem pr424339 : Nat.Prime 424339 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv197,pv359]) (by decide +kernel)
def pv424339 : PrimeValue := ⟨424339, pr424339⟩
private theorem pr424397 : Nat.Prime 424397 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv7,pv23,pv659]) (by decide +kernel)
def pv424397 : PrimeValue := ⟨424397, pr424397⟩
private theorem pr424423 : Nat.Prime 424423 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv19,pv73]) (by decide +kernel)
def pv424423 : PrimeValue := ⟨424423, pr424423⟩
private theorem pr424493 : Nat.Prime 424493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv106123]) (by decide +kernel)
def pv424493 : PrimeValue := ⟨424493, pr424493⟩
private theorem pr424519 : Nat.Prime 424519 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv70753]) (by decide +kernel)
def pv424519 : PrimeValue := ⟨424519, pr424519⟩
private theorem pr424547 : Nat.Prime 424547 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79,pv2687]) (by decide +kernel)
def pv424547 : PrimeValue := ⟨424547, pr424547⟩
private theorem pr424559 : Nat.Prime 424559 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv17,pv12487]) (by decide +kernel)
def pv424559 : PrimeValue := ⟨424559, pr424559⟩
private theorem pr424597 : Nat.Prime 424597 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv41,pv863]) (by decide +kernel)
def pv424597 : PrimeValue := ⟨424597, pr424597⟩
private theorem pr424601 : Nat.Prime 424601 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv193]) (by decide +kernel)
def pv424601 : PrimeValue := ⟨424601, pr424601⟩
private theorem pr424661 : Nat.Prime 424661 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv1249]) (by decide +kernel)
def pv424661 : PrimeValue := ⟨424661, pr424661⟩
private theorem pr424667 : Nat.Prime 424667 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv97,pv199]) (by decide +kernel)
def pv424667 : PrimeValue := ⟨424667, pr424667⟩
private theorem pr424693 : Nat.Prime 424693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv47,pv251]) (by decide +kernel)
def pv424693 : PrimeValue := ⟨424693, pr424693⟩
private theorem pr424709 : Nat.Prime 424709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv89,pv1193]) (by decide +kernel)
def pv424709 : PrimeValue := ⟨424709, pr424709⟩
private theorem pr424757 : Nat.Prime 424757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv106189]) (by decide +kernel)
def pv424757 : PrimeValue := ⟨424757, pr424757⟩
private theorem pr424769 : Nat.Prime 424769 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv6637]) (by decide +kernel)
def pv424769 : PrimeValue := ⟨424769, pr424769⟩
private theorem pr424771 : Nat.Prime 424771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv14159]) (by decide +kernel)
def pv424771 : PrimeValue := ⟨424771, pr424771⟩
private theorem pr424777 : Nat.Prime 424777 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv1609]) (by decide +kernel)
def pv424777 : PrimeValue := ⟨424777, pr424777⟩
private theorem pr424811 : Nat.Prime 424811 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23,pv1847]) (by decide +kernel)
def pv424811 : PrimeValue := ⟨424811, pr424811⟩
private theorem pr424867 : Nat.Prime 424867 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv419]) (by decide +kernel)
def pv424867 : PrimeValue := ⟨424867, pr424867⟩
private theorem pr424913 : Nat.Prime 424913 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv26557]) (by decide +kernel)
def pv424913 : PrimeValue := ⟨424913, pr424913⟩
private theorem pr424961 : Nat.Prime 424961 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv83]) (by decide +kernel)
def pv424961 : PrimeValue := ⟨424961, pr424961⟩
private theorem pr425003 : Nat.Prime 425003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv212501]) (by decide +kernel)
def pv425003 : PrimeValue := ⟨425003, pr425003⟩
private theorem pr425027 : Nat.Prime 425027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv4337]) (by decide +kernel)
def pv425027 : PrimeValue := ⟨425027, pr425027⟩
private theorem pr425057 : Nat.Prime 425057 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv37,pv359]) (by decide +kernel)
def pv425057 : PrimeValue := ⟨425057, pr425057⟩
private theorem pr425101 : Nat.Prime 425101 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv13,pv109]) (by decide +kernel)
def pv425101 : PrimeValue := ⟨425101, pr425101⟩
private theorem pr425123 : Nat.Prime 425123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv212561]) (by decide +kernel)
def pv425123 : PrimeValue := ⟨425123, pr425123⟩
private theorem pr425273 : Nat.Prime 425273 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv53,pv59]) (by decide +kernel)
def pv425273 : PrimeValue := ⟨425273, pr425273⟩
private theorem pr425279 : Nat.Prime 425279 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv37,pv821]) (by decide +kernel)
def pv425279 : PrimeValue := ⟨425279, pr425279⟩
private theorem pr425281 : Nat.Prime 425281 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv443]) (by decide +kernel)
def pv425281 : PrimeValue := ⟨425281, pr425281⟩
private theorem pr425309 : Nat.Prime 425309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv8179]) (by decide +kernel)
def pv425309 : PrimeValue := ⟨425309, pr425309⟩
private theorem pr425317 : Nat.Prime 425317 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv23,pv67]) (by decide +kernel)
def pv425317 : PrimeValue := ⟨425317, pr425317⟩
private theorem pr425333 : Nat.Prime 425333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv113,pv941]) (by decide +kernel)
def pv425333 : PrimeValue := ⟨425333, pr425333⟩
private theorem pr425363 : Nat.Prime 425363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv23,pv1321]) (by decide +kernel)
def pv425363 : PrimeValue := ⟨425363, pr425363⟩
private theorem pr425377 : Nat.Prime 425377 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv211]) (by decide +kernel)
def pv425377 : PrimeValue := ⟨425377, pr425377⟩
private theorem pr425393 : Nat.Prime 425393 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv2417]) (by decide +kernel)
def pv425393 : PrimeValue := ⟨425393, pr425393⟩
private theorem pr425417 : Nat.Prime 425417 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv41,pv1297]) (by decide +kernel)
def pv425417 : PrimeValue := ⟨425417, pr425417⟩
private theorem pr425441 : Nat.Prime 425441 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv2659]) (by decide +kernel)
def pv425441 : PrimeValue := ⟨425441, pr425441⟩
private theorem pr425443 : Nat.Prime 425443 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv43,pv97]) (by decide +kernel)
def pv425443 : PrimeValue := ⟨425443, pr425443⟩
private theorem pr425471 : Nat.Prime 425471 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv157,pv271]) (by decide +kernel)
def pv425471 : PrimeValue := ⟨425471, pr425471⟩
private theorem pr425489 : Nat.Prime 425489 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv29,pv131]) (by decide +kernel)
def pv425489 : PrimeValue := ⟨425489, pr425489⟩
private theorem pr425519 : Nat.Prime 425519 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv151,pv1409]) (by decide +kernel)
def pv425519 : PrimeValue := ⟨425519, pr425519⟩
private theorem pr425533 : Nat.Prime 425533 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv35461]) (by decide +kernel)
def pv425533 : PrimeValue := ⟨425533, pr425533⟩
private theorem pr425549 : Nat.Prime 425549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv191,pv557]) (by decide +kernel)
def pv425549 : PrimeValue := ⟨425549, pr425549⟩
private theorem pr425591 : Nat.Prime 425591 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv5,pv11,pv53,pv73]) (by decide +kernel)
def pv425591 : PrimeValue := ⟨425591, pr425591⟩
private theorem pr425681 : Nat.Prime 425681 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17,pv313]) (by decide +kernel)
def pv425681 : PrimeValue := ⟨425681, pr425681⟩
private theorem pr425801 : Nat.Prime 425801 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv2129]) (by decide +kernel)
def pv425801 : PrimeValue := ⟨425801, pr425801⟩
private theorem pr425819 : Nat.Prime 425819 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv212909]) (by decide +kernel)
def pv425819 : PrimeValue := ⟨425819, pr425819⟩
private theorem pr425861 : Nat.Prime 425861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv107,pv199]) (by decide +kernel)
def pv425861 : PrimeValue := ⟨425861, pr425861⟩
private theorem pr425977 : Nat.Prime 425977 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17749]) (by decide +kernel)
def pv425977 : PrimeValue := ⟨425977, pr425977⟩
private theorem pr425989 : Nat.Prime 425989 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11833]) (by decide +kernel)
def pv425989 : PrimeValue := ⟨425989, pr425989⟩
private theorem pr426011 : Nat.Prime 426011 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv13,pv29,pv113]) (by decide +kernel)
def pv426011 : PrimeValue := ⟨426011, pr426011⟩
private theorem pr426089 : Nat.Prime 426089 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv17,pv241]) (by decide +kernel)
def pv426089 : PrimeValue := ⟨426089, pr426089⟩
private theorem pr426131 : Nat.Prime 426131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv43,pv991]) (by decide +kernel)
def pv426131 : PrimeValue := ⟨426131, pr426131⟩
private theorem pr426161 : Nat.Prime 426161 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv761]) (by decide +kernel)
def pv426161 : PrimeValue := ⟨426161, pr426161⟩
private theorem pr426197 : Nat.Prime 426197 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv2267]) (by decide +kernel)
def pv426197 : PrimeValue := ⟨426197, pr426197⟩
private theorem pr426253 : Nat.Prime 426253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv35521]) (by decide +kernel)
def pv426253 : PrimeValue := ⟨426253, pr426253⟩
private theorem pr426311 : Nat.Prime 426311 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv89,pv479]) (by decide +kernel)
def pv426311 : PrimeValue := ⟨426311, pr426311⟩
private theorem pr426421 : Nat.Prime 426421 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv23,pv103]) (by decide +kernel)
def pv426421 : PrimeValue := ⟨426421, pr426421⟩
private theorem pr426541 : Nat.Prime 426541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7109]) (by decide +kernel)
def pv426541 : PrimeValue := ⟨426541, pr426541⟩
private theorem pr426551 : Nat.Prime 426551 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv19,pv449]) (by decide +kernel)
def pv426551 : PrimeValue := ⟨426551, pr426551⟩
private theorem pr426553 : Nat.Prime 426553 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv2539]) (by decide +kernel)
def pv426553 : PrimeValue := ⟨426553, pr426553⟩
private theorem pr426563 : Nat.Prime 426563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv213281]) (by decide +kernel)
def pv426563 : PrimeValue := ⟨426563, pr426563⟩
private theorem pr426631 : Nat.Prime 426631 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv14221]) (by decide +kernel)
def pv426631 : PrimeValue := ⟨426631, pr426631⟩
private theorem pr426641 : Nat.Prime 426641 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv5333]) (by decide +kernel)
def pv426641 : PrimeValue := ⟨426641, pr426641⟩
private theorem pr426691 : Nat.Prime 426691 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv431]) (by decide +kernel)
def pv426691 : PrimeValue := ⟨426691, pr426691⟩
private theorem pr426731 : Nat.Prime 426731 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv139,pv307]) (by decide +kernel)
def pv426731 : PrimeValue := ⟨426731, pr426731⟩
private theorem pr426737 : Nat.Prime 426737 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv149,pv179]) (by decide +kernel)
def pv426737 : PrimeValue := ⟨426737, pr426737⟩
private theorem pr426757 : Nat.Prime 426757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv53,pv61]) (by decide +kernel)
def pv426757 : PrimeValue := ⟨426757, pr426757⟩
private theorem pr426773 : Nat.Prime 426773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv106693]) (by decide +kernel)
def pv426773 : PrimeValue := ⟨426773, pr426773⟩
private theorem pr426779 : Nat.Prime 426779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv19,pv1021]) (by decide +kernel)
def pv426779 : PrimeValue := ⟨426779, pr426779⟩
private theorem pr426799 : Nat.Prime 426799 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv131,pv181]) (by decide +kernel)
def pv426799 : PrimeValue := ⟨426799, pr426799⟩
private theorem pr426859 : Nat.Prime 426859 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv71143]) (by decide +kernel)
def pv426859 : PrimeValue := ⟨426859, pr426859⟩
private theorem pr426863 : Nat.Prime 426863 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv53,pv4027]) (by decide +kernel)
def pv426863 : PrimeValue := ⟨426863, pr426863⟩
private theorem pr426871 : Nat.Prime 426871 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv17,pv31]) (by decide +kernel)
def pv426871 : PrimeValue := ⟨426871, pr426871⟩
private theorem pr426917 : Nat.Prime 426917 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv79,pv193]) (by decide +kernel)
def pv426917 : PrimeValue := ⟨426917, pr426917⟩
private theorem pr427067 : Nat.Prime 427067 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv213533]) (by decide +kernel)
def pv427067 : PrimeValue := ⟨427067, pr427067⟩
private theorem pr427079 : Nat.Prime 427079 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv213539]) (by decide +kernel)
def pv427079 : PrimeValue := ⟨427079, pr427079⟩
private theorem pr427103 : Nat.Prime 427103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv16427]) (by decide +kernel)
def pv427103 : PrimeValue := ⟨427103, pr427103⟩
private theorem pr427151 : Nat.Prime 427151 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv5,pv8543]) (by decide +kernel)
def pv427151 : PrimeValue := ⟨427151, pr427151⟩
private theorem pr427169 : Nat.Prime 427169 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv1907]) (by decide +kernel)
def pv427169 : PrimeValue := ⟨427169, pr427169⟩
private theorem pr427181 : Nat.Prime 427181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv31,pv53]) (by decide +kernel)
def pv427181 : PrimeValue := ⟨427181, pr427181⟩
private theorem pr427213 : Nat.Prime 427213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11867]) (by decide +kernel)
def pv427213 : PrimeValue := ⟨427213, pr427213⟩
private theorem pr427247 : Nat.Prime 427247 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv213623]) (by decide +kernel)
def pv427247 : PrimeValue := ⟨427247, pr427247⟩
private theorem pr427249 : Nat.Prime 427249 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv23,pv43]) (by decide +kernel)
def pv427249 : PrimeValue := ⟨427249, pr427249⟩
private theorem pr427379 : Nat.Prime 427379 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv89]) (by decide +kernel)
def pv427379 : PrimeValue := ⟨427379, pr427379⟩
private theorem pr427403 : Nat.Prime 427403 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv29,pv7369]) (by decide +kernel)
def pv427403 : PrimeValue := ⟨427403, pr427403⟩
private theorem pr427423 : Nat.Prime 427423 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv71237]) (by decide +kernel)
def pv427423 : PrimeValue := ⟨427423, pr427423⟩
private theorem pr427447 : Nat.Prime 427447 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23747]) (by decide +kernel)
def pv427447 : PrimeValue := ⟨427447, pr427447⟩
private theorem pr427451 : Nat.Prime 427451 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv83,pv103]) (by decide +kernel)
def pv427451 : PrimeValue := ⟨427451, pr427451⟩
private theorem pr427477 : Nat.Prime 427477 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv727]) (by decide +kernel)
def pv427477 : PrimeValue := ⟨427477, pr427477⟩
private theorem pr427517 : Nat.Prime 427517 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv6287]) (by decide +kernel)
def pv427517 : PrimeValue := ⟨427517, pr427517⟩
private theorem pr427523 : Nat.Prime 427523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv181,pv1181]) (by decide +kernel)
def pv427523 : PrimeValue := ⟨427523, pr427523⟩
private theorem pr427529 : Nat.Prime 427529 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv53441]) (by decide +kernel)
def pv427529 : PrimeValue := ⟨427529, pr427529⟩
private theorem pr427597 : Nat.Prime 427597 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv2741]) (by decide +kernel)
def pv427597 : PrimeValue := ⟨427597, pr427597⟩
private theorem pr427717 : Nat.Prime 427717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv109]) (by decide +kernel)
def pv427717 : PrimeValue := ⟨427717, pr427717⟩
private theorem pr427723 : Nat.Prime 427723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv71287]) (by decide +kernel)
def pv427723 : PrimeValue := ⟨427723, pr427723⟩
private theorem pr427733 : Nat.Prime 427733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv1753]) (by decide +kernel)
def pv427733 : PrimeValue := ⟨427733, pr427733⟩
private theorem pr427781 : Nat.Prime 427781 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv73,pv293]) (by decide +kernel)
def pv427781 : PrimeValue := ⟨427781, pr427781⟩
private theorem pr427787 : Nat.Prime 427787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv107,pv1999]) (by decide +kernel)
def pv427787 : PrimeValue := ⟨427787, pr427787⟩
private theorem pr427849 : Nat.Prime 427849 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv17827]) (by decide +kernel)
def pv427849 : PrimeValue := ⟨427849, pr427849⟩
private theorem pr427859 : Nat.Prime 427859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv213929]) (by decide +kernel)
def pv427859 : PrimeValue := ⟨427859, pr427859⟩
private theorem pr427879 : Nat.Prime 427879 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv2161]) (by decide +kernel)
def pv427879 : PrimeValue := ⟨427879, pr427879⟩
private theorem pr427991 : Nat.Prime 427991 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv127,pv337]) (by decide +kernel)
def pv427991 : PrimeValue := ⟨427991, pr427991⟩
private theorem pr427993 : Nat.Prime 427993 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv1049]) (by decide +kernel)
def pv427993 : PrimeValue := ⟨427993, pr427993⟩
private theorem pr428083 : Nat.Prime 428083 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv71347]) (by decide +kernel)
def pv428083 : PrimeValue := ⟨428083, pr428083⟩
private theorem pr428093 : Nat.Prime 428093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv15289]) (by decide +kernel)
def pv428093 : PrimeValue := ⟨428093, pr428093⟩
private theorem pr428137 : Nat.Prime 428137 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17839]) (by decide +kernel)
def pv428137 : PrimeValue := ⟨428137, pr428137⟩
private theorem pr428167 : Nat.Prime 428167 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv881]) (by decide +kernel)
def pv428167 : PrimeValue := ⟨428167, pr428167⟩
private theorem pr428221 : Nat.Prime 428221 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv61]) (by decide +kernel)
def pv428221 : PrimeValue := ⟨428221, pr428221⟩
private theorem pr428273 : Nat.Prime 428273 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv29,pv71]) (by decide +kernel)
def pv428273 : PrimeValue := ⟨428273, pr428273⟩
private theorem pr428297 : Nat.Prime 428297 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv31,pv157]) (by decide +kernel)
def pv428297 : PrimeValue := ⟨428297, pr428297⟩
private theorem pr428353 : Nat.Prime 428353 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv23,pv97]) (by decide +kernel)
def pv428353 : PrimeValue := ⟨428353, pr428353⟩
private theorem pr428411 : Nat.Prime 428411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv42841]) (by decide +kernel)
def pv428411 : PrimeValue := ⟨428411, pr428411⟩
private theorem pr428471 : Nat.Prime 428471 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv6121]) (by decide +kernel)
def pv428471 : PrimeValue := ⟨428471, pr428471⟩
private theorem pr428489 : Nat.Prime 428489 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv2819]) (by decide +kernel)
def pv428489 : PrimeValue := ⟨428489, pr428489⟩
private theorem pr428539 : Nat.Prime 428539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv43,pv151]) (by decide +kernel)
def pv428539 : PrimeValue := ⟨428539, pr428539⟩
private theorem pr428551 : Nat.Prime 428551 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv2857]) (by decide +kernel)
def pv428551 : PrimeValue := ⟨428551, pr428551⟩
private theorem pr428563 : Nat.Prime 428563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv821]) (by decide +kernel)
def pv428563 : PrimeValue := ⟨428563, pr428563⟩
private theorem pr428633 : Nat.Prime 428633 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv131,pv409]) (by decide +kernel)
def pv428633 : PrimeValue := ⟨428633, pr428633⟩
private theorem pr428639 : Nat.Prime 428639 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv17,pv1801]) (by decide +kernel)
def pv428639 : PrimeValue := ⟨428639, pr428639⟩
private theorem pr428663 : Nat.Prime 428663 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv13,pv16487]) (by decide +kernel)
def pv428663 : PrimeValue := ⟨428663, pr428663⟩
private theorem pr428671 : Nat.Prime 428671 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv433]) (by decide +kernel)
def pv428671 : PrimeValue := ⟨428671, pr428671⟩
private theorem pr428683 : Nat.Prime 428683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv1931]) (by decide +kernel)
def pv428683 : PrimeValue := ⟨428683, pr428683⟩
private theorem pr428777 : Nat.Prime 428777 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv53597]) (by decide +kernel)
def pv428777 : PrimeValue := ⟨428777, pr428777⟩
private theorem pr428809 : Nat.Prime 428809 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv17,pv1051]) (by decide +kernel)
def pv428809 : PrimeValue := ⟨428809, pr428809⟩
private theorem pr428843 : Nat.Prime 428843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv12613]) (by decide +kernel)
def pv428843 : PrimeValue := ⟨428843, pr428843⟩
private theorem pr428851 : Nat.Prime 428851 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv953]) (by decide +kernel)
def pv428851 : PrimeValue := ⟨428851, pr428851⟩
private theorem pr428951 : Nat.Prime 428951 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv23,pv373]) (by decide +kernel)
def pv428951 : PrimeValue := ⟨428951, pr428951⟩
private theorem pr429007 : Nat.Prime 429007 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv127,pv563]) (by decide +kernel)
def pv429007 : PrimeValue := ⟨429007, pr429007⟩
private theorem pr429017 : Nat.Prime 429017 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv47,pv163]) (by decide +kernel)
def pv429017 : PrimeValue := ⟨429017, pr429017⟩
private theorem pr429083 : Nat.Prime 429083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv214541]) (by decide +kernel)
def pv429083 : PrimeValue := ⟨429083, pr429083⟩
private theorem pr429119 : Nat.Prime 429119 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv214559]) (by decide +kernel)
def pv429119 : PrimeValue := ⟨429119, pr429119⟩
private theorem pr429127 : Nat.Prime 429127 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv37,pv1933]) (by decide +kernel)
def pv429127 : PrimeValue := ⟨429127, pr429127⟩
private theorem pr429137 : Nat.Prime 429137 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv26821]) (by decide +kernel)
def pv429137 : PrimeValue := ⟨429137, pr429137⟩
private theorem pr429139 : Nat.Prime 429139 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv883]) (by decide +kernel)
def pv429139 : PrimeValue := ⟨429139, pr429139⟩
private theorem pr429161 : Nat.Prime 429161 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv10729]) (by decide +kernel)
def pv429161 : PrimeValue := ⟨429161, pr429161⟩
private theorem pr429223 : Nat.Prime 429223 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv71537]) (by decide +kernel)
def pv429223 : PrimeValue := ⟨429223, pr429223⟩
private theorem pr429271 : Nat.Prime 429271 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv41,pv349]) (by decide +kernel)
def pv429271 : PrimeValue := ⟨429271, pr429271⟩
private theorem pr429277 : Nat.Prime 429277 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv83,pv431]) (by decide +kernel)
def pv429277 : PrimeValue := ⟨429277, pr429277⟩
private theorem pr429281 : Nat.Prime 429281 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv2683]) (by decide +kernel)
def pv429281 : PrimeValue := ⟨429281, pr429281⟩
private theorem pr429329 : Nat.Prime 429329 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv26833]) (by decide +kernel)
def pv429329 : PrimeValue := ⟨429329, pr429329⟩
private theorem pr429409 : Nat.Prime 429409 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv71]) (by decide +kernel)
def pv429409 : PrimeValue := ⟨429409, pr429409⟩
private theorem pr429449 : Nat.Prime 429449 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv53681]) (by decide +kernel)
def pv429449 : PrimeValue := ⟨429449, pr429449⟩
private theorem pr429463 : Nat.Prime 429463 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv241]) (by decide +kernel)
def pv429463 : PrimeValue := ⟨429463, pr429463⟩
private theorem pr429497 : Nat.Prime 429497 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv37,pv1451]) (by decide +kernel)
def pv429497 : PrimeValue := ⟨429497, pr429497⟩
private theorem pr429547 : Nat.Prime 429547 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv5507]) (by decide +kernel)
def pv429547 : PrimeValue := ⟨429547, pr429547⟩
private theorem pr429551 : Nat.Prime 429551 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv11,pv71]) (by decide +kernel)
def pv429551 : PrimeValue := ⟨429551, pr429551⟩
private theorem pr429581 : Nat.Prime 429581 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv47,pv457]) (by decide +kernel)
def pv429581 : PrimeValue := ⟨429581, pr429581⟩
private theorem pr429589 : Nat.Prime 429589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11933]) (by decide +kernel)
def pv429589 : PrimeValue := ⟨429589, pr429589⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
