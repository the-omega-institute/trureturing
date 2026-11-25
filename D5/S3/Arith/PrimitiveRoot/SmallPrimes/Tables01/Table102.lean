/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table102
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table102.pv421133
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table010
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table017
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table027
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table028
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table068

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr421133 : PrimeCertificate 421133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv127,pv829]) (by decide +kernel)
def pv421133 : PrimeValue := ⟨421133, pr421133⟩
private theorem pr421147 : PrimeCertificate 421147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv709]) (by decide +kernel)
def pv421147 : PrimeValue := ⟨421147, pr421147⟩
private theorem pr421181 : PrimeCertificate 421181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv21059]) (by decide +kernel)
def pv421181 : PrimeValue := ⟨421181, pr421181⟩
private theorem pr421207 : PrimeCertificate 421207 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv70201]) (by decide +kernel)
def pv421207 : PrimeValue := ⟨421207, pr421207⟩
private theorem pr421241 : PrimeCertificate 421241 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv10531]) (by decide +kernel)
def pv421241 : PrimeValue := ⟨421241, pr421241⟩
private theorem pr421273 : PrimeCertificate 421273 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5851]) (by decide +kernel)
def pv421273 : PrimeValue := ⟨421273, pr421273⟩
private theorem pr421313 : PrimeCertificate 421313 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv227]) (by decide +kernel)
def pv421313 : PrimeValue := ⟨421313, pr421313⟩
private theorem pr421331 : PrimeCertificate 421331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv13,pv463]) (by decide +kernel)
def pv421331 : PrimeValue := ⟨421331, pr421331⟩
private theorem pr421361 : PrimeCertificate 421361 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv23,pv229]) (by decide +kernel)
def pv421361 : PrimeValue := ⟨421361, pr421361⟩
private theorem pr421409 : PrimeCertificate 421409 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv1013]) (by decide +kernel)
def pv421409 : PrimeValue := ⟨421409, pr421409⟩
private theorem pr421417 : PrimeCertificate 421417 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1951]) (by decide +kernel)
def pv421417 : PrimeValue := ⟨421417, pr421417⟩
private theorem pr421433 : PrimeCertificate 421433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv4789]) (by decide +kernel)
def pv421433 : PrimeValue := ⟨421433, pr421433⟩
private theorem pr421459 : PrimeCertificate 421459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv3697]) (by decide +kernel)
def pv421459 : PrimeValue := ⟨421459, pr421459⟩
private theorem pr421469 : PrimeCertificate 421469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv105367]) (by decide +kernel)
def pv421469 : PrimeValue := ⟨421469, pr421469⟩
private theorem pr421483 : PrimeCertificate 421483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv199,pv353]) (by decide +kernel)
def pv421483 : PrimeValue := ⟨421483, pr421483⟩
private theorem pr421493 : PrimeCertificate 421493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv105373]) (by decide +kernel)
def pv421493 : PrimeValue := ⟨421493, pr421493⟩
private theorem pr421607 : PrimeCertificate 421607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv210803]) (by decide +kernel)
def pv421607 : PrimeValue := ⟨421607, pr421607⟩
private theorem pr421633 : PrimeCertificate 421633 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv61]) (by decide +kernel)
def pv421633 : PrimeValue := ⟨421633, pr421633⟩
private theorem pr421661 : PrimeCertificate 421661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29,pv727]) (by decide +kernel)
def pv421661 : PrimeValue := ⟨421661, pr421661⟩
private theorem pr421691 : PrimeCertificate 421691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv42169]) (by decide +kernel)
def pv421691 : PrimeValue := ⟨421691, pr421691⟩
private theorem pr421711 : PrimeCertificate 421711 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv14057]) (by decide +kernel)
def pv421711 : PrimeValue := ⟨421711, pr421711⟩
private theorem pr421783 : PrimeCertificate 421783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv70297]) (by decide +kernel)
def pv421783 : PrimeValue := ⟨421783, pr421783⟩
private theorem pr421831 : PrimeCertificate 421831 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv43,pv109]) (by decide +kernel)
def pv421831 : PrimeValue := ⟨421831, pr421831⟩
private theorem pr421847 : PrimeCertificate 421847 :=
  certifyPrime (q := pv5) (ls := [pv2,pv210923]) (by decide +kernel)
def pv421847 : PrimeValue := ⟨421847, pr421847⟩
private theorem pr421907 : PrimeCertificate 421907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv12409]) (by decide +kernel)
def pv421907 : PrimeValue := ⟨421907, pr421907⟩
private theorem pr421987 : PrimeCertificate 421987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53,pv1327]) (by decide +kernel)
def pv421987 : PrimeValue := ⟨421987, pr421987⟩
private theorem pr421997 : PrimeCertificate 421997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv105499]) (by decide +kernel)
def pv421997 : PrimeValue := ⟨421997, pr421997⟩
private theorem pr422063 : PrimeCertificate 422063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv281,pv751]) (by decide +kernel)
def pv422063 : PrimeValue := ⟨422063, pr422063⟩
private theorem pr422069 : PrimeCertificate 422069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv105517]) (by decide +kernel)
def pv422069 : PrimeValue := ⟨422069, pr422069⟩
private theorem pr422099 : PrimeCertificate 422099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv211049]) (by decide +kernel)
def pv422099 : PrimeValue := ⟨422099, pr422099⟩
private theorem pr422137 : PrimeCertificate 422137 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv13,pv41]) (by decide +kernel)
def pv422137 : PrimeValue := ⟨422137, pr422137⟩
private theorem pr422209 : PrimeCertificate 422209 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv733]) (by decide +kernel)
def pv422209 : PrimeValue := ⟨422209, pr422209⟩
private theorem pr422231 : PrimeCertificate 422231 :=
  certifyPrime (q := pv37) (ls := [pv2,pv5,pv42223]) (by decide +kernel)
def pv422231 : PrimeValue := ⟨422231, pr422231⟩
private theorem pr422249 : PrimeCertificate 422249 :=
  certifyPrime (q := pv3) (ls := [pv2,pv47,pv1123]) (by decide +kernel)
def pv422249 : PrimeValue := ⟨422249, pr422249⟩
private theorem pr422291 : PrimeCertificate 422291 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv349]) (by decide +kernel)
def pv422291 : PrimeValue := ⟨422291, pr422291⟩
private theorem pr422309 : PrimeCertificate 422309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71,pv1487]) (by decide +kernel)
def pv422309 : PrimeValue := ⟨422309, pr422309⟩
private theorem pr422321 : PrimeCertificate 422321 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv5279]) (by decide +kernel)
def pv422321 : PrimeValue := ⟨422321, pr422321⟩
private theorem pr422363 : PrimeCertificate 422363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv223,pv947]) (by decide +kernel)
def pv422363 : PrimeValue := ⟨422363, pr422363⟩
private theorem pr422407 : PrimeCertificate 422407 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv757]) (by decide +kernel)
def pv422407 : PrimeValue := ⟨422407, pr422407⟩
private theorem pr422537 : PrimeCertificate 422537 :=
  certifyPrime (q := pv3) (ls := [pv2,pv52817]) (by decide +kernel)
def pv422537 : PrimeValue := ⟨422537, pr422537⟩
private theorem pr422549 : PrimeCertificate 422549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv15091]) (by decide +kernel)
def pv422549 : PrimeValue := ⟨422549, pr422549⟩
private theorem pr422551 : PrimeCertificate 422551 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv313]) (by decide +kernel)
def pv422551 : PrimeValue := ⟨422551, pr422551⟩
private theorem pr422557 : PrimeCertificate 422557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv1531]) (by decide +kernel)
def pv422557 : PrimeValue := ⟨422557, pr422557⟩
private theorem pr422563 : PrimeCertificate 422563 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv10061]) (by decide +kernel)
def pv422563 : PrimeValue := ⟨422563, pr422563⟩
private theorem pr422581 : PrimeCertificate 422581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7043]) (by decide +kernel)
def pv422581 : PrimeValue := ⟨422581, pr422581⟩
private theorem pr422621 : PrimeCertificate 422621 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv17,pv113]) (by decide +kernel)
def pv422621 : PrimeValue := ⟨422621, pr422621⟩
private theorem pr422627 : PrimeCertificate 422627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv211313]) (by decide +kernel)
def pv422627 : PrimeValue := ⟨422627, pr422627⟩
private theorem pr422689 : PrimeCertificate 422689 :=
  certifyPrime (q := pv53) (ls := [pv2,pv3,pv7,pv17,pv37]) (by decide +kernel)
def pv422689 : PrimeValue := ⟨422689, pr422689⟩
private theorem pr422707 : PrimeCertificate 422707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv70451]) (by decide +kernel)
def pv422707 : PrimeValue := ⟨422707, pr422707⟩
private theorem pr422711 : PrimeCertificate 422711 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv41,pv1031]) (by decide +kernel)
def pv422711 : PrimeValue := ⟨422711, pr422711⟩
private theorem pr422797 : PrimeCertificate 422797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv3203]) (by decide +kernel)
def pv422797 : PrimeValue := ⟨422797, pr422797⟩
private theorem pr422803 : PrimeCertificate 422803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv83,pv283]) (by decide +kernel)
def pv422803 : PrimeValue := ⟨422803, pr422803⟩
private theorem pr422857 : PrimeCertificate 422857 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv839]) (by decide +kernel)
def pv422857 : PrimeValue := ⟨422857, pr422857⟩
private theorem pr422861 : PrimeCertificate 422861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv21143]) (by decide +kernel)
def pv422861 : PrimeValue := ⟨422861, pr422861⟩
private theorem pr422881 : PrimeCertificate 422881 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv881]) (by decide +kernel)
def pv422881 : PrimeValue := ⟨422881, pr422881⟩
private theorem pr422911 : PrimeCertificate 422911 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv37,pv127]) (by decide +kernel)
def pv422911 : PrimeValue := ⟨422911, pr422911⟩
private theorem pr422923 : PrimeCertificate 422923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv70487]) (by decide +kernel)
def pv422923 : PrimeValue := ⟨422923, pr422923⟩
private theorem pr422969 : PrimeCertificate 422969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv13,pv83]) (by decide +kernel)
def pv422969 : PrimeValue := ⟨422969, pr422969⟩
private theorem pr422987 : PrimeCertificate 422987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv211493]) (by decide +kernel)
def pv422987 : PrimeValue := ⟨422987, pr422987⟩
private theorem pr423013 : PrimeCertificate 423013 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv35251]) (by decide +kernel)
def pv423013 : PrimeValue := ⟨423013, pr423013⟩
private theorem pr423083 : PrimeCertificate 423083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv19231]) (by decide +kernel)
def pv423083 : PrimeValue := ⟨423083, pr423083⟩
private theorem pr423103 : PrimeCertificate 423103 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv151,pv467]) (by decide +kernel)
def pv423103 : PrimeValue := ⟨423103, pr423103⟩
private theorem pr423179 : PrimeCertificate 423179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv167,pv181]) (by decide +kernel)
def pv423179 : PrimeValue := ⟨423179, pr423179⟩
private theorem pr423191 : PrimeCertificate 423191 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv101,pv419]) (by decide +kernel)
def pv423191 : PrimeValue := ⟨423191, pr423191⟩
private theorem pr423229 : PrimeCertificate 423229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv2713]) (by decide +kernel)
def pv423229 : PrimeValue := ⟨423229, pr423229⟩
private theorem pr423233 : PrimeCertificate 423233 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv389]) (by decide +kernel)
def pv423233 : PrimeValue := ⟨423233, pr423233⟩
private theorem pr423257 : PrimeCertificate 423257 :=
  certifyPrime (q := pv3) (ls := [pv2,pv191,pv277]) (by decide +kernel)
def pv423257 : PrimeValue := ⟨423257, pr423257⟩
private theorem pr423281 : PrimeCertificate 423281 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv13,pv37]) (by decide +kernel)
def pv423281 : PrimeValue := ⟨423281, pr423281⟩
private theorem pr423287 : PrimeCertificate 423287 :=
  certifyPrime (q := pv5) (ls := [pv2,pv211643]) (by decide +kernel)
def pv423287 : PrimeValue := ⟨423287, pr423287⟩
private theorem pr423299 : PrimeCertificate 423299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv113,pv1873]) (by decide +kernel)
def pv423299 : PrimeValue := ⟨423299, pr423299⟩
private theorem pr423323 : PrimeCertificate 423323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv211661]) (by decide +kernel)
def pv423323 : PrimeValue := ⟨423323, pr423323⟩
private theorem pr423341 : PrimeCertificate 423341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv61,pv347]) (by decide +kernel)
def pv423341 : PrimeValue := ⟨423341, pr423341⟩
private theorem pr423389 : PrimeCertificate 423389 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv15121]) (by decide +kernel)
def pv423389 : PrimeValue := ⟨423389, pr423389⟩
private theorem pr423403 : PrimeCertificate 423403 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv17,pv593]) (by decide +kernel)
def pv423403 : PrimeValue := ⟨423403, pr423403⟩
private theorem pr423413 : PrimeCertificate 423413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv9623]) (by decide +kernel)
def pv423413 : PrimeValue := ⟨423413, pr423413⟩
private theorem pr423427 : PrimeCertificate 423427 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv70571]) (by decide +kernel)
def pv423427 : PrimeValue := ⟨423427, pr423427⟩
private theorem pr423457 : PrimeCertificate 423457 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv401]) (by decide +kernel)
def pv423457 : PrimeValue := ⟨423457, pr423457⟩
private theorem pr423461 : PrimeCertificate 423461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31,pv683]) (by decide +kernel)
def pv423461 : PrimeValue := ⟨423461, pr423461⟩
private theorem pr423481 : PrimeCertificate 423481 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv3529]) (by decide +kernel)
def pv423481 : PrimeValue := ⟨423481, pr423481⟩
private theorem pr423497 : PrimeCertificate 423497 :=
  certifyPrime (q := pv3) (ls := [pv2,pv52937]) (by decide +kernel)
def pv423497 : PrimeValue := ⟨423497, pr423497⟩
private theorem pr423581 : PrimeCertificate 423581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv21179]) (by decide +kernel)
def pv423581 : PrimeValue := ⟨423581, pr423581⟩
private theorem pr423617 : PrimeCertificate 423617 :=
  certifyPrime (q := pv3) (ls := [pv2,pv6619]) (by decide +kernel)
def pv423617 : PrimeValue := ⟨423617, pr423617⟩
private theorem pr423727 : PrimeCertificate 423727 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv70621]) (by decide +kernel)
def pv423727 : PrimeValue := ⟨423727, pr423727⟩
private theorem pr423749 : PrimeCertificate 423749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv29,pv281]) (by decide +kernel)
def pv423749 : PrimeValue := ⟨423749, pr423749⟩
private theorem pr423791 : PrimeCertificate 423791 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv42379]) (by decide +kernel)
def pv423791 : PrimeValue := ⟨423791, pr423791⟩
private theorem pr423803 : PrimeCertificate 423803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv313,pv677]) (by decide +kernel)
def pv423803 : PrimeValue := ⟨423803, pr423803⟩
private theorem pr423823 : PrimeCertificate 423823 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv10091]) (by decide +kernel)
def pv423823 : PrimeValue := ⟨423823, pr423823⟩
private theorem pr423853 : PrimeCertificate 423853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv13,pv19]) (by decide +kernel)
def pv423853 : PrimeValue := ⟨423853, pr423853⟩
private theorem pr423859 : PrimeCertificate 423859 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv41,pv1723]) (by decide +kernel)
def pv423859 : PrimeValue := ⟨423859, pr423859⟩
private theorem pr423869 : PrimeCertificate 423869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv105967]) (by decide +kernel)
def pv423869 : PrimeValue := ⟨423869, pr423869⟩
private theorem pr423887 : PrimeCertificate 423887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv211943]) (by decide +kernel)
def pv423887 : PrimeValue := ⟨423887, pr423887⟩
private theorem pr423949 : PrimeCertificate 423949 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv103]) (by decide +kernel)
def pv423949 : PrimeValue := ⟨423949, pr423949⟩
private theorem pr424027 : PrimeCertificate 424027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23557]) (by decide +kernel)
def pv424027 : PrimeValue := ⟨424027, pr424027⟩
private theorem pr424079 : PrimeCertificate 424079 :=
  certifyPrime (q := pv13) (ls := [pv2,pv212039]) (by decide +kernel)
def pv424079 : PrimeValue := ⟨424079, pr424079⟩
private theorem pr424091 : PrimeCertificate 424091 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv42409]) (by decide +kernel)
def pv424091 : PrimeValue := ⟨424091, pr424091⟩
private theorem pr424129 : PrimeCertificate 424129 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv47]) (by decide +kernel)
def pv424129 : PrimeValue := ⟨424129, pr424129⟩
private theorem pr424147 : PrimeCertificate 424147 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv223,pv317]) (by decide +kernel)
def pv424147 : PrimeValue := ⟨424147, pr424147⟩
private theorem pr424157 : PrimeCertificate 424157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv5581]) (by decide +kernel)
def pv424157 : PrimeValue := ⟨424157, pr424157⟩
private theorem pr424199 : PrimeCertificate 424199 :=
  certifyPrime (q := pv19) (ls := [pv2,pv212099]) (by decide +kernel)
def pv424199 : PrimeValue := ⟨424199, pr424199⟩
private theorem pr424243 : PrimeCertificate 424243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv37]) (by decide +kernel)
def pv424243 : PrimeValue := ⟨424243, pr424243⟩
private theorem pr424267 : PrimeCertificate 424267 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv2281]) (by decide +kernel)
def pv424267 : PrimeValue := ⟨424267, pr424267⟩
private theorem pr424339 : PrimeCertificate 424339 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv197,pv359]) (by decide +kernel)
def pv424339 : PrimeValue := ⟨424339, pr424339⟩
private theorem pr424397 : PrimeCertificate 424397 :=
  certifyPrime (q := pv11) (ls := [pv2,pv7,pv23,pv659]) (by decide +kernel)
def pv424397 : PrimeValue := ⟨424397, pr424397⟩
private theorem pr424423 : PrimeCertificate 424423 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv19,pv73]) (by decide +kernel)
def pv424423 : PrimeValue := ⟨424423, pr424423⟩
private theorem pr424493 : PrimeCertificate 424493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv106123]) (by decide +kernel)
def pv424493 : PrimeValue := ⟨424493, pr424493⟩
private theorem pr424519 : PrimeCertificate 424519 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv70753]) (by decide +kernel)
def pv424519 : PrimeValue := ⟨424519, pr424519⟩
private theorem pr424547 : PrimeCertificate 424547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv79,pv2687]) (by decide +kernel)
def pv424547 : PrimeValue := ⟨424547, pr424547⟩
private theorem pr424559 : PrimeCertificate 424559 :=
  certifyPrime (q := pv7) (ls := [pv2,pv17,pv12487]) (by decide +kernel)
def pv424559 : PrimeValue := ⟨424559, pr424559⟩
private theorem pr424597 : PrimeCertificate 424597 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv41,pv863]) (by decide +kernel)
def pv424597 : PrimeValue := ⟨424597, pr424597⟩
private theorem pr424601 : PrimeCertificate 424601 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv193]) (by decide +kernel)
def pv424601 : PrimeValue := ⟨424601, pr424601⟩
private theorem pr424661 : PrimeCertificate 424661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv1249]) (by decide +kernel)
def pv424661 : PrimeValue := ⟨424661, pr424661⟩
private theorem pr424667 : PrimeCertificate 424667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv97,pv199]) (by decide +kernel)
def pv424667 : PrimeValue := ⟨424667, pr424667⟩
private theorem pr424693 : PrimeCertificate 424693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv251]) (by decide +kernel)
def pv424693 : PrimeValue := ⟨424693, pr424693⟩
private theorem pr424709 : PrimeCertificate 424709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89,pv1193]) (by decide +kernel)
def pv424709 : PrimeValue := ⟨424709, pr424709⟩
private theorem pr424757 : PrimeCertificate 424757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv106189]) (by decide +kernel)
def pv424757 : PrimeValue := ⟨424757, pr424757⟩
private theorem pr424769 : PrimeCertificate 424769 :=
  certifyPrime (q := pv3) (ls := [pv2,pv6637]) (by decide +kernel)
def pv424769 : PrimeValue := ⟨424769, pr424769⟩
private theorem pr424771 : PrimeCertificate 424771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv14159]) (by decide +kernel)
def pv424771 : PrimeValue := ⟨424771, pr424771⟩
private theorem pr424777 : PrimeCertificate 424777 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv1609]) (by decide +kernel)
def pv424777 : PrimeValue := ⟨424777, pr424777⟩
private theorem pr424811 : PrimeCertificate 424811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv1847]) (by decide +kernel)
def pv424811 : PrimeValue := ⟨424811, pr424811⟩
private theorem pr424867 : PrimeCertificate 424867 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv419]) (by decide +kernel)
def pv424867 : PrimeValue := ⟨424867, pr424867⟩
private theorem pr424913 : PrimeCertificate 424913 :=
  certifyPrime (q := pv3) (ls := [pv2,pv26557]) (by decide +kernel)
def pv424913 : PrimeValue := ⟨424913, pr424913⟩
private theorem pr424961 : PrimeCertificate 424961 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv83]) (by decide +kernel)
def pv424961 : PrimeValue := ⟨424961, pr424961⟩
private theorem pr425003 : PrimeCertificate 425003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv212501]) (by decide +kernel)
def pv425003 : PrimeValue := ⟨425003, pr425003⟩
private theorem pr425027 : PrimeCertificate 425027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv4337]) (by decide +kernel)
def pv425027 : PrimeValue := ⟨425027, pr425027⟩
private theorem pr425057 : PrimeCertificate 425057 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv359]) (by decide +kernel)
def pv425057 : PrimeValue := ⟨425057, pr425057⟩
private theorem pr425101 : PrimeCertificate 425101 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv13,pv109]) (by decide +kernel)
def pv425101 : PrimeValue := ⟨425101, pr425101⟩
private theorem pr425123 : PrimeCertificate 425123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv212561]) (by decide +kernel)
def pv425123 : PrimeValue := ⟨425123, pr425123⟩
private theorem pr425273 : PrimeCertificate 425273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv53,pv59]) (by decide +kernel)
def pv425273 : PrimeValue := ⟨425273, pr425273⟩
private theorem pr425279 : PrimeCertificate 425279 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv37,pv821]) (by decide +kernel)
def pv425279 : PrimeValue := ⟨425279, pr425279⟩
private theorem pr425281 : PrimeCertificate 425281 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv443]) (by decide +kernel)
def pv425281 : PrimeValue := ⟨425281, pr425281⟩
private theorem pr425309 : PrimeCertificate 425309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv8179]) (by decide +kernel)
def pv425309 : PrimeValue := ⟨425309, pr425309⟩
private theorem pr425317 : PrimeCertificate 425317 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv23,pv67]) (by decide +kernel)
def pv425317 : PrimeValue := ⟨425317, pr425317⟩
private theorem pr425333 : PrimeCertificate 425333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv113,pv941]) (by decide +kernel)
def pv425333 : PrimeValue := ⟨425333, pr425333⟩
private theorem pr425363 : PrimeCertificate 425363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv23,pv1321]) (by decide +kernel)
def pv425363 : PrimeValue := ⟨425363, pr425363⟩
private theorem pr425377 : PrimeCertificate 425377 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv211]) (by decide +kernel)
def pv425377 : PrimeValue := ⟨425377, pr425377⟩
private theorem pr425393 : PrimeCertificate 425393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv2417]) (by decide +kernel)
def pv425393 : PrimeValue := ⟨425393, pr425393⟩
private theorem pr425417 : PrimeCertificate 425417 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41,pv1297]) (by decide +kernel)
def pv425417 : PrimeValue := ⟨425417, pr425417⟩
private theorem pr425441 : PrimeCertificate 425441 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv2659]) (by decide +kernel)
def pv425441 : PrimeValue := ⟨425441, pr425441⟩
private theorem pr425443 : PrimeCertificate 425443 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv43,pv97]) (by decide +kernel)
def pv425443 : PrimeValue := ⟨425443, pr425443⟩
private theorem pr425471 : PrimeCertificate 425471 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv157,pv271]) (by decide +kernel)
def pv425471 : PrimeValue := ⟨425471, pr425471⟩
private theorem pr425489 : PrimeCertificate 425489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv29,pv131]) (by decide +kernel)
def pv425489 : PrimeValue := ⟨425489, pr425489⟩
private theorem pr425519 : PrimeCertificate 425519 :=
  certifyPrime (q := pv29) (ls := [pv2,pv151,pv1409]) (by decide +kernel)
def pv425519 : PrimeValue := ⟨425519, pr425519⟩
private theorem pr425533 : PrimeCertificate 425533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv35461]) (by decide +kernel)
def pv425533 : PrimeValue := ⟨425533, pr425533⟩
private theorem pr425549 : PrimeCertificate 425549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv191,pv557]) (by decide +kernel)
def pv425549 : PrimeValue := ⟨425549, pr425549⟩
private theorem pr425591 : PrimeCertificate 425591 :=
  certifyPrime (q := pv37) (ls := [pv2,pv5,pv11,pv53,pv73]) (by decide +kernel)
def pv425591 : PrimeValue := ⟨425591, pr425591⟩
private theorem pr425681 : PrimeCertificate 425681 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17,pv313]) (by decide +kernel)
def pv425681 : PrimeValue := ⟨425681, pr425681⟩
private theorem pr425801 : PrimeCertificate 425801 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv2129]) (by decide +kernel)
def pv425801 : PrimeValue := ⟨425801, pr425801⟩
private theorem pr425819 : PrimeCertificate 425819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv212909]) (by decide +kernel)
def pv425819 : PrimeValue := ⟨425819, pr425819⟩
private theorem pr425861 : PrimeCertificate 425861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv107,pv199]) (by decide +kernel)
def pv425861 : PrimeValue := ⟨425861, pr425861⟩
private theorem pr425977 : PrimeCertificate 425977 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17749]) (by decide +kernel)
def pv425977 : PrimeValue := ⟨425977, pr425977⟩
private theorem pr425989 : PrimeCertificate 425989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11833]) (by decide +kernel)
def pv425989 : PrimeValue := ⟨425989, pr425989⟩
private theorem pr426011 : PrimeCertificate 426011 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv13,pv29,pv113]) (by decide +kernel)
def pv426011 : PrimeValue := ⟨426011, pr426011⟩
private theorem pr426089 : PrimeCertificate 426089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv17,pv241]) (by decide +kernel)
def pv426089 : PrimeValue := ⟨426089, pr426089⟩
private theorem pr426131 : PrimeCertificate 426131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv43,pv991]) (by decide +kernel)
def pv426131 : PrimeValue := ⟨426131, pr426131⟩
private theorem pr426161 : PrimeCertificate 426161 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv761]) (by decide +kernel)
def pv426161 : PrimeValue := ⟨426161, pr426161⟩
private theorem pr426197 : PrimeCertificate 426197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv2267]) (by decide +kernel)
def pv426197 : PrimeValue := ⟨426197, pr426197⟩
private theorem pr426253 : PrimeCertificate 426253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv35521]) (by decide +kernel)
def pv426253 : PrimeValue := ⟨426253, pr426253⟩
private theorem pr426311 : PrimeCertificate 426311 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv89,pv479]) (by decide +kernel)
def pv426311 : PrimeValue := ⟨426311, pr426311⟩
private theorem pr426421 : PrimeCertificate 426421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv23,pv103]) (by decide +kernel)
def pv426421 : PrimeValue := ⟨426421, pr426421⟩
private theorem pr426541 : PrimeCertificate 426541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7109]) (by decide +kernel)
def pv426541 : PrimeValue := ⟨426541, pr426541⟩
private theorem pr426551 : PrimeCertificate 426551 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv19,pv449]) (by decide +kernel)
def pv426551 : PrimeValue := ⟨426551, pr426551⟩
private theorem pr426553 : PrimeCertificate 426553 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv2539]) (by decide +kernel)
def pv426553 : PrimeValue := ⟨426553, pr426553⟩
private theorem pr426563 : PrimeCertificate 426563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv213281]) (by decide +kernel)
def pv426563 : PrimeValue := ⟨426563, pr426563⟩
private theorem pr426631 : PrimeCertificate 426631 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv14221]) (by decide +kernel)
def pv426631 : PrimeValue := ⟨426631, pr426631⟩
private theorem pr426641 : PrimeCertificate 426641 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv5333]) (by decide +kernel)
def pv426641 : PrimeValue := ⟨426641, pr426641⟩
private theorem pr426691 : PrimeCertificate 426691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv431]) (by decide +kernel)
def pv426691 : PrimeValue := ⟨426691, pr426691⟩
private theorem pr426731 : PrimeCertificate 426731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv139,pv307]) (by decide +kernel)
def pv426731 : PrimeValue := ⟨426731, pr426731⟩
private theorem pr426737 : PrimeCertificate 426737 :=
  certifyPrime (q := pv3) (ls := [pv2,pv149,pv179]) (by decide +kernel)
def pv426737 : PrimeValue := ⟨426737, pr426737⟩
private theorem pr426757 : PrimeCertificate 426757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv53,pv61]) (by decide +kernel)
def pv426757 : PrimeValue := ⟨426757, pr426757⟩
private theorem pr426773 : PrimeCertificate 426773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv106693]) (by decide +kernel)
def pv426773 : PrimeValue := ⟨426773, pr426773⟩
private theorem pr426779 : PrimeCertificate 426779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv19,pv1021]) (by decide +kernel)
def pv426779 : PrimeValue := ⟨426779, pr426779⟩
private theorem pr426799 : PrimeCertificate 426799 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv131,pv181]) (by decide +kernel)
def pv426799 : PrimeValue := ⟨426799, pr426799⟩
private theorem pr426859 : PrimeCertificate 426859 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv71143]) (by decide +kernel)
def pv426859 : PrimeValue := ⟨426859, pr426859⟩
private theorem pr426863 : PrimeCertificate 426863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv53,pv4027]) (by decide +kernel)
def pv426863 : PrimeValue := ⟨426863, pr426863⟩
private theorem pr426871 : PrimeCertificate 426871 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv17,pv31]) (by decide +kernel)
def pv426871 : PrimeValue := ⟨426871, pr426871⟩
private theorem pr426917 : PrimeCertificate 426917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv79,pv193]) (by decide +kernel)
def pv426917 : PrimeValue := ⟨426917, pr426917⟩
private theorem pr427067 : PrimeCertificate 427067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv213533]) (by decide +kernel)
def pv427067 : PrimeValue := ⟨427067, pr427067⟩
private theorem pr427079 : PrimeCertificate 427079 :=
  certifyPrime (q := pv7) (ls := [pv2,pv213539]) (by decide +kernel)
def pv427079 : PrimeValue := ⟨427079, pr427079⟩
private theorem pr427103 : PrimeCertificate 427103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv16427]) (by decide +kernel)
def pv427103 : PrimeValue := ⟨427103, pr427103⟩
private theorem pr427151 : PrimeCertificate 427151 :=
  certifyPrime (q := pv29) (ls := [pv2,pv5,pv8543]) (by decide +kernel)
def pv427151 : PrimeValue := ⟨427151, pr427151⟩
private theorem pr427169 : PrimeCertificate 427169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv1907]) (by decide +kernel)
def pv427169 : PrimeValue := ⟨427169, pr427169⟩
private theorem pr427181 : PrimeCertificate 427181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv31,pv53]) (by decide +kernel)
def pv427181 : PrimeValue := ⟨427181, pr427181⟩
private theorem pr427213 : PrimeCertificate 427213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11867]) (by decide +kernel)
def pv427213 : PrimeValue := ⟨427213, pr427213⟩
private theorem pr427247 : PrimeCertificate 427247 :=
  certifyPrime (q := pv5) (ls := [pv2,pv213623]) (by decide +kernel)
def pv427247 : PrimeValue := ⟨427247, pr427247⟩
private theorem pr427249 : PrimeCertificate 427249 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv23,pv43]) (by decide +kernel)
def pv427249 : PrimeValue := ⟨427249, pr427249⟩
private theorem pr427379 : PrimeCertificate 427379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv89]) (by decide +kernel)
def pv427379 : PrimeValue := ⟨427379, pr427379⟩
private theorem pr427403 : PrimeCertificate 427403 :=
  certifyPrime (q := pv5) (ls := [pv2,pv29,pv7369]) (by decide +kernel)
def pv427403 : PrimeValue := ⟨427403, pr427403⟩
private theorem pr427423 : PrimeCertificate 427423 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv71237]) (by decide +kernel)
def pv427423 : PrimeValue := ⟨427423, pr427423⟩
private theorem pr427447 : PrimeCertificate 427447 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23747]) (by decide +kernel)
def pv427447 : PrimeValue := ⟨427447, pr427447⟩
private theorem pr427451 : PrimeCertificate 427451 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv83,pv103]) (by decide +kernel)
def pv427451 : PrimeValue := ⟨427451, pr427451⟩
private theorem pr427477 : PrimeCertificate 427477 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv727]) (by decide +kernel)
def pv427477 : PrimeValue := ⟨427477, pr427477⟩
private theorem pr427517 : PrimeCertificate 427517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv6287]) (by decide +kernel)
def pv427517 : PrimeValue := ⟨427517, pr427517⟩
private theorem pr427523 : PrimeCertificate 427523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv181,pv1181]) (by decide +kernel)
def pv427523 : PrimeValue := ⟨427523, pr427523⟩
private theorem pr427529 : PrimeCertificate 427529 :=
  certifyPrime (q := pv3) (ls := [pv2,pv53441]) (by decide +kernel)
def pv427529 : PrimeValue := ⟨427529, pr427529⟩
private theorem pr427597 : PrimeCertificate 427597 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv2741]) (by decide +kernel)
def pv427597 : PrimeValue := ⟨427597, pr427597⟩
private theorem pr427717 : PrimeCertificate 427717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv109]) (by decide +kernel)
def pv427717 : PrimeValue := ⟨427717, pr427717⟩
private theorem pr427723 : PrimeCertificate 427723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv71287]) (by decide +kernel)
def pv427723 : PrimeValue := ⟨427723, pr427723⟩
private theorem pr427733 : PrimeCertificate 427733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv1753]) (by decide +kernel)
def pv427733 : PrimeValue := ⟨427733, pr427733⟩
private theorem pr427781 : PrimeCertificate 427781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv73,pv293]) (by decide +kernel)
def pv427781 : PrimeValue := ⟨427781, pr427781⟩
private theorem pr427787 : PrimeCertificate 427787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv107,pv1999]) (by decide +kernel)
def pv427787 : PrimeValue := ⟨427787, pr427787⟩
private theorem pr427849 : PrimeCertificate 427849 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv17827]) (by decide +kernel)
def pv427849 : PrimeValue := ⟨427849, pr427849⟩
private theorem pr427859 : PrimeCertificate 427859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv213929]) (by decide +kernel)
def pv427859 : PrimeValue := ⟨427859, pr427859⟩
private theorem pr427879 : PrimeCertificate 427879 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv2161]) (by decide +kernel)
def pv427879 : PrimeValue := ⟨427879, pr427879⟩
private theorem pr427991 : PrimeCertificate 427991 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv127,pv337]) (by decide +kernel)
def pv427991 : PrimeValue := ⟨427991, pr427991⟩
private theorem pr427993 : PrimeCertificate 427993 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv1049]) (by decide +kernel)
def pv427993 : PrimeValue := ⟨427993, pr427993⟩
private theorem pr428083 : PrimeCertificate 428083 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv71347]) (by decide +kernel)
def pv428083 : PrimeValue := ⟨428083, pr428083⟩
private theorem pr428093 : PrimeCertificate 428093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv15289]) (by decide +kernel)
def pv428093 : PrimeValue := ⟨428093, pr428093⟩
private theorem pr428137 : PrimeCertificate 428137 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17839]) (by decide +kernel)
def pv428137 : PrimeValue := ⟨428137, pr428137⟩
private theorem pr428167 : PrimeCertificate 428167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv881]) (by decide +kernel)
def pv428167 : PrimeValue := ⟨428167, pr428167⟩
private theorem pr428221 : PrimeCertificate 428221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv61]) (by decide +kernel)
def pv428221 : PrimeValue := ⟨428221, pr428221⟩
private theorem pr428273 : PrimeCertificate 428273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv29,pv71]) (by decide +kernel)
def pv428273 : PrimeValue := ⟨428273, pr428273⟩
private theorem pr428297 : PrimeCertificate 428297 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv31,pv157]) (by decide +kernel)
def pv428297 : PrimeValue := ⟨428297, pr428297⟩
private theorem pr428353 : PrimeCertificate 428353 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv23,pv97]) (by decide +kernel)
def pv428353 : PrimeValue := ⟨428353, pr428353⟩
private theorem pr428411 : PrimeCertificate 428411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv42841]) (by decide +kernel)
def pv428411 : PrimeValue := ⟨428411, pr428411⟩
private theorem pr428471 : PrimeCertificate 428471 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv6121]) (by decide +kernel)
def pv428471 : PrimeValue := ⟨428471, pr428471⟩
private theorem pr428489 : PrimeCertificate 428489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv2819]) (by decide +kernel)
def pv428489 : PrimeValue := ⟨428489, pr428489⟩
private theorem pr428539 : PrimeCertificate 428539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv43,pv151]) (by decide +kernel)
def pv428539 : PrimeValue := ⟨428539, pr428539⟩
private theorem pr428551 : PrimeCertificate 428551 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv2857]) (by decide +kernel)
def pv428551 : PrimeValue := ⟨428551, pr428551⟩
private theorem pr428563 : PrimeCertificate 428563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv821]) (by decide +kernel)
def pv428563 : PrimeValue := ⟨428563, pr428563⟩
private theorem pr428633 : PrimeCertificate 428633 :=
  certifyPrime (q := pv3) (ls := [pv2,pv131,pv409]) (by decide +kernel)
def pv428633 : PrimeValue := ⟨428633, pr428633⟩
private theorem pr428639 : PrimeCertificate 428639 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv17,pv1801]) (by decide +kernel)
def pv428639 : PrimeValue := ⟨428639, pr428639⟩
private theorem pr428663 : PrimeCertificate 428663 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv16487]) (by decide +kernel)
def pv428663 : PrimeValue := ⟨428663, pr428663⟩
private theorem pr428671 : PrimeCertificate 428671 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv433]) (by decide +kernel)
def pv428671 : PrimeValue := ⟨428671, pr428671⟩
private theorem pr428683 : PrimeCertificate 428683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv1931]) (by decide +kernel)
def pv428683 : PrimeValue := ⟨428683, pr428683⟩
private theorem pr428777 : PrimeCertificate 428777 :=
  certifyPrime (q := pv3) (ls := [pv2,pv53597]) (by decide +kernel)
def pv428777 : PrimeValue := ⟨428777, pr428777⟩
private theorem pr428809 : PrimeCertificate 428809 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv17,pv1051]) (by decide +kernel)
def pv428809 : PrimeValue := ⟨428809, pr428809⟩
private theorem pr428843 : PrimeCertificate 428843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv12613]) (by decide +kernel)
def pv428843 : PrimeValue := ⟨428843, pr428843⟩
private theorem pr428851 : PrimeCertificate 428851 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv953]) (by decide +kernel)
def pv428851 : PrimeValue := ⟨428851, pr428851⟩
private theorem pr428951 : PrimeCertificate 428951 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv23,pv373]) (by decide +kernel)
def pv428951 : PrimeValue := ⟨428951, pr428951⟩
private theorem pr429007 : PrimeCertificate 429007 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv127,pv563]) (by decide +kernel)
def pv429007 : PrimeValue := ⟨429007, pr429007⟩
private theorem pr429017 : PrimeCertificate 429017 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv47,pv163]) (by decide +kernel)
def pv429017 : PrimeValue := ⟨429017, pr429017⟩
private theorem pr429083 : PrimeCertificate 429083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv214541]) (by decide +kernel)
def pv429083 : PrimeValue := ⟨429083, pr429083⟩
private theorem pr429119 : PrimeCertificate 429119 :=
  certifyPrime (q := pv11) (ls := [pv2,pv214559]) (by decide +kernel)
def pv429119 : PrimeValue := ⟨429119, pr429119⟩
private theorem pr429127 : PrimeCertificate 429127 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv37,pv1933]) (by decide +kernel)
def pv429127 : PrimeValue := ⟨429127, pr429127⟩
private theorem pr429137 : PrimeCertificate 429137 :=
  certifyPrime (q := pv3) (ls := [pv2,pv26821]) (by decide +kernel)
def pv429137 : PrimeValue := ⟨429137, pr429137⟩
private theorem pr429139 : PrimeCertificate 429139 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv883]) (by decide +kernel)
def pv429139 : PrimeValue := ⟨429139, pr429139⟩
private theorem pr429161 : PrimeCertificate 429161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv10729]) (by decide +kernel)
def pv429161 : PrimeValue := ⟨429161, pr429161⟩
private theorem pr429223 : PrimeCertificate 429223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv71537]) (by decide +kernel)
def pv429223 : PrimeValue := ⟨429223, pr429223⟩
private theorem pr429271 : PrimeCertificate 429271 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv41,pv349]) (by decide +kernel)
def pv429271 : PrimeValue := ⟨429271, pr429271⟩
private theorem pr429277 : PrimeCertificate 429277 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv83,pv431]) (by decide +kernel)
def pv429277 : PrimeValue := ⟨429277, pr429277⟩
private theorem pr429281 : PrimeCertificate 429281 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv2683]) (by decide +kernel)
def pv429281 : PrimeValue := ⟨429281, pr429281⟩
private theorem pr429329 : PrimeCertificate 429329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv26833]) (by decide +kernel)
def pv429329 : PrimeValue := ⟨429329, pr429329⟩
private theorem pr429409 : PrimeCertificate 429409 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv71]) (by decide +kernel)
def pv429409 : PrimeValue := ⟨429409, pr429409⟩
private theorem pr429449 : PrimeCertificate 429449 :=
  certifyPrime (q := pv3) (ls := [pv2,pv53681]) (by decide +kernel)
def pv429449 : PrimeValue := ⟨429449, pr429449⟩
private theorem pr429463 : PrimeCertificate 429463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv241]) (by decide +kernel)
def pv429463 : PrimeValue := ⟨429463, pr429463⟩
private theorem pr429497 : PrimeCertificate 429497 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv1451]) (by decide +kernel)
def pv429497 : PrimeValue := ⟨429497, pr429497⟩
private theorem pr429547 : PrimeCertificate 429547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv5507]) (by decide +kernel)
def pv429547 : PrimeValue := ⟨429547, pr429547⟩
private theorem pr429551 : PrimeCertificate 429551 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv11,pv71]) (by decide +kernel)
def pv429551 : PrimeValue := ⟨429551, pr429551⟩
private theorem pr429581 : PrimeCertificate 429581 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv47,pv457]) (by decide +kernel)
def pv429581 : PrimeValue := ⟨429581, pr429581⟩
private theorem pr429589 : PrimeCertificate 429589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11933]) (by decide +kernel)
def pv429589 : PrimeValue := ⟨429589, pr429589⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
