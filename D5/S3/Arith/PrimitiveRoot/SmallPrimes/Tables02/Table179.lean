/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table179
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table179.pv360323
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table015
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table024
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table060
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table061

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr360323 : Nat.Prime 360323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv180161]) (by decide +kernel)
def pv360323 : PrimeValue := ⟨360323, pr360323⟩
private theorem pr360589 : Nat.Prime 360589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv151,pv199]) (by decide +kernel)
def pv360589 : PrimeValue := ⟨360589, pr360589⟩
private theorem pr360649 : Nat.Prime 360649 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5009]) (by decide +kernel)
def pv360649 : PrimeValue := ⟨360649, pr360649⟩
private theorem pr360769 : Nat.Prime 360769 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv1879]) (by decide +kernel)
def pv360769 : PrimeValue := ⟨360769, pr360769⟩
private theorem pr360853 : Nat.Prime 360853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv30071]) (by decide +kernel)
def pv360853 : PrimeValue := ⟨360853, pr360853⟩
private theorem pr360863 : Nat.Prime 360863 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv67,pv2693]) (by decide +kernel)
def pv360863 : PrimeValue := ⟨360863, pr360863⟩
private theorem pr360907 : Nat.Prime 360907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv661]) (by decide +kernel)
def pv360907 : PrimeValue := ⟨360907, pr360907⟩
private theorem pr360973 : Nat.Prime 360973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv271]) (by decide +kernel)
def pv360973 : PrimeValue := ⟨360973, pr360973⟩
private theorem pr360979 : Nat.Prime 360979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv3539]) (by decide +kernel)
def pv360979 : PrimeValue := ⟨360979, pr360979⟩
private theorem pr361033 : Nat.Prime 361033 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv307]) (by decide +kernel)
def pv361033 : PrimeValue := ⟨361033, pr361033⟩
private theorem pr361159 : Nat.Prime 361159 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv8599]) (by decide +kernel)
def pv361159 : PrimeValue := ⟨361159, pr361159⟩
private theorem pr361183 : Nat.Prime 361183 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv3541]) (by decide +kernel)
def pv361183 : PrimeValue := ⟨361183, pr361183⟩
private theorem pr361321 : Nat.Prime 361321 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv3011]) (by decide +kernel)
def pv361321 : PrimeValue := ⟨361321, pr361321⟩
private theorem pr361327 : Nat.Prime 361327 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv1229]) (by decide +kernel)
def pv361327 : PrimeValue := ⟨361327, pr361327⟩
private theorem pr361411 : Nat.Prime 361411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv1721]) (by decide +kernel)
def pv361411 : PrimeValue := ⟨361411, pr361411⟩
private theorem pr361441 : Nat.Prime 361441 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv251]) (by decide +kernel)
def pv361441 : PrimeValue := ⟨361441, pr361441⟩
private theorem pr361511 : Nat.Prime 361511 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv36151]) (by decide +kernel)
def pv361511 : PrimeValue := ⟨361511, pr361511⟩
private theorem pr361523 : Nat.Prime 361523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv17,pv31]) (by decide +kernel)
def pv361523 : PrimeValue := ⟨361523, pr361523⟩
private theorem pr361663 : Nat.Prime 361663 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv79,pv109]) (by decide +kernel)
def pv361663 : PrimeValue := ⟨361663, pr361663⟩
private theorem pr361763 : Nat.Prime 361763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv277,pv653]) (by decide +kernel)
def pv361763 : PrimeValue := ⟨361763, pr361763⟩
private theorem pr361807 : Nat.Prime 361807 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv47,pv1283]) (by decide +kernel)
def pv361807 : PrimeValue := ⟨361807, pr361807⟩
private theorem pr361871 : Nat.Prime 361871 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv36187]) (by decide +kernel)
def pv361871 : PrimeValue := ⟨361871, pr361871⟩
private theorem pr362069 : Nat.Prime 362069 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv67,pv193]) (by decide +kernel)
def pv362069 : PrimeValue := ⟨362069, pr362069⟩
private theorem pr362191 : Nat.Prime 362191 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv12073]) (by decide +kernel)
def pv362191 : PrimeValue := ⟨362191, pr362191⟩
private theorem pr362213 : Nat.Prime 362213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv83,pv1091]) (by decide +kernel)
def pv362213 : PrimeValue := ⟨362213, pr362213⟩
private theorem pr362281 : Nat.Prime 362281 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv3019]) (by decide +kernel)
def pv362281 : PrimeValue := ⟨362281, pr362281⟩
private theorem pr362333 : Nat.Prime 362333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv90583]) (by decide +kernel)
def pv362333 : PrimeValue := ⟨362333, pr362333⟩
private theorem pr362393 : Nat.Prime 362393 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv97,pv467]) (by decide +kernel)
def pv362393 : PrimeValue := ⟨362393, pr362393⟩
private theorem pr362419 : Nat.Prime 362419 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv8629]) (by decide +kernel)
def pv362419 : PrimeValue := ⟨362419, pr362419⟩
private theorem pr362443 : Nat.Prime 362443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv2083]) (by decide +kernel)
def pv362443 : PrimeValue := ⟨362443, pr362443⟩
private theorem pr362561 : Nat.Prime 362561 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv103]) (by decide +kernel)
def pv362561 : PrimeValue := ⟨362561, pr362561⟩
private theorem pr362599 : Nat.Prime 362599 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv223,pv271]) (by decide +kernel)
def pv362599 : PrimeValue := ⟨362599, pr362599⟩
private theorem pr362629 : Nat.Prime 362629 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv1439]) (by decide +kernel)
def pv362629 : PrimeValue := ⟨362629, pr362629⟩
private theorem pr362741 : Nat.Prime 362741 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv2591]) (by decide +kernel)
def pv362741 : PrimeValue := ⟨362741, pr362741⟩
private theorem pr362851 : Nat.Prime 362851 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv41,pv59]) (by decide +kernel)
def pv362851 : PrimeValue := ⟨362851, pr362851⟩
private theorem pr362863 : Nat.Prime 362863 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv1061]) (by decide +kernel)
def pv362863 : PrimeValue := ⟨362863, pr362863⟩
private theorem pr362953 : Nat.Prime 362953 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv71]) (by decide +kernel)
def pv362953 : PrimeValue := ⟨362953, pr362953⟩
private theorem pr363119 : Nat.Prime 363119 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv7,pv37,pv701]) (by decide +kernel)
def pv363119 : PrimeValue := ⟨363119, pr363119⟩
private theorem pr363217 : Nat.Prime 363217 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv23,pv47]) (by decide +kernel)
def pv363217 : PrimeValue := ⟨363217, pr363217⟩
private theorem pr363271 : Nat.Prime 363271 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv12109]) (by decide +kernel)
def pv363271 : PrimeValue := ⟨363271, pr363271⟩
private theorem pr363343 : Nat.Prime 363343 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv41,pv211]) (by decide +kernel)
def pv363343 : PrimeValue := ⟨363343, pr363343⟩
private theorem pr363361 : Nat.Prime 363361 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv757]) (by decide +kernel)
def pv363361 : PrimeValue := ⟨363361, pr363361⟩
private theorem pr363379 : Nat.Prime 363379 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv71,pv853]) (by decide +kernel)
def pv363379 : PrimeValue := ⟨363379, pr363379⟩
private theorem pr363401 : Nat.Prime 363401 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv23,pv79]) (by decide +kernel)
def pv363401 : PrimeValue := ⟨363401, pr363401⟩
private theorem pr363403 : Nat.Prime 363403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv1553]) (by decide +kernel)
def pv363403 : PrimeValue := ⟨363403, pr363403⟩
private theorem pr363481 : Nat.Prime 363481 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv13,pv233]) (by decide +kernel)
def pv363481 : PrimeValue := ⟨363481, pr363481⟩
private theorem pr363529 : Nat.Prime 363529 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv11,pv17]) (by decide +kernel)
def pv363529 : PrimeValue := ⟨363529, pr363529⟩
private theorem pr363551 : Nat.Prime 363551 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv11,pv661]) (by decide +kernel)
def pv363551 : PrimeValue := ⟨363551, pr363551⟩
private theorem pr363589 : Nat.Prime 363589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv41,pv739]) (by decide +kernel)
def pv363589 : PrimeValue := ⟨363589, pr363589⟩
private theorem pr363691 : Nat.Prime 363691 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv449]) (by decide +kernel)
def pv363691 : PrimeValue := ⟨363691, pr363691⟩
private theorem pr363751 : Nat.Prime 363751 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv97]) (by decide +kernel)
def pv363751 : PrimeValue := ⟨363751, pr363751⟩
private theorem pr363889 : Nat.Prime 363889 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv19]) (by decide +kernel)
def pv363889 : PrimeValue := ⟨363889, pr363889⟩
private theorem pr364141 : Nat.Prime 364141 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv17]) (by decide +kernel)
def pv364141 : PrimeValue := ⟨364141, pr364141⟩
private theorem pr364183 : Nat.Prime 364183 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv23,pv29]) (by decide +kernel)
def pv364183 : PrimeValue := ⟨364183, pr364183⟩
private theorem pr364271 : Nat.Prime 364271 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv73,pv499]) (by decide +kernel)
def pv364271 : PrimeValue := ⟨364271, pr364271⟩
private theorem pr364423 : Nat.Prime 364423 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv60737]) (by decide +kernel)
def pv364423 : PrimeValue := ⟨364423, pr364423⟩
private theorem pr364499 : Nat.Prime 364499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv5879]) (by decide +kernel)
def pv364499 : PrimeValue := ⟨364499, pr364499⟩
private theorem pr364523 : Nat.Prime 364523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv182261]) (by decide +kernel)
def pv364523 : PrimeValue := ⟨364523, pr364523⟩
private theorem pr364537 : Nat.Prime 364537 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv61,pv83]) (by decide +kernel)
def pv364537 : PrimeValue := ⟨364537, pr364537⟩
private theorem pr364643 : Nat.Prime 364643 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv7927]) (by decide +kernel)
def pv364643 : PrimeValue := ⟨364643, pr364643⟩
private theorem pr364753 : Nat.Prime 364753 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv149]) (by decide +kernel)
def pv364753 : PrimeValue := ⟨364753, pr364753⟩
private theorem pr364853 : Nat.Prime 364853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53,pv1721]) (by decide +kernel)
def pv364853 : PrimeValue := ⟨364853, pr364853⟩
private theorem pr364873 : Nat.Prime 364873 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23,pv661]) (by decide +kernel)
def pv364873 : PrimeValue := ⟨364873, pr364873⟩
private theorem pr364909 : Nat.Prime 364909 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv47,pv647]) (by decide +kernel)
def pv364909 : PrimeValue := ⟨364909, pr364909⟩
private theorem pr364993 : Nat.Prime 364993 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1901]) (by decide +kernel)
def pv364993 : PrimeValue := ⟨364993, pr364993⟩
private theorem pr365003 : Nat.Prime 365003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv47,pv353]) (by decide +kernel)
def pv365003 : PrimeValue := ⟨365003, pr365003⟩
private theorem pr365063 : Nat.Prime 365063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv167,pv1093]) (by decide +kernel)
def pv365063 : PrimeValue := ⟨365063, pr365063⟩
private theorem pr365119 : Nat.Prime 365119 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv31,pv151]) (by decide +kernel)
def pv365119 : PrimeValue := ⟨365119, pr365119⟩
private theorem pr365129 : Nat.Prime 365129 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv45641]) (by decide +kernel)
def pv365129 : PrimeValue := ⟨365129, pr365129⟩
private theorem pr365173 : Nat.Prime 365173 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv30431]) (by decide +kernel)
def pv365173 : PrimeValue := ⟨365173, pr365173⟩
private theorem pr365179 : Nat.Prime 365179 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv503]) (by decide +kernel)
def pv365179 : PrimeValue := ⟨365179, pr365179⟩
private theorem pr365231 : Nat.Prime 365231 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv36523]) (by decide +kernel)
def pv365231 : PrimeValue := ⟨365231, pr365231⟩
private theorem pr365293 : Nat.Prime 365293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv73,pv139]) (by decide +kernel)
def pv365293 : PrimeValue := ⟨365293, pr365293⟩
private theorem pr365413 : Nat.Prime 365413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv823]) (by decide +kernel)
def pv365413 : PrimeValue := ⟨365413, pr365413⟩
private theorem pr365461 : Nat.Prime 365461 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv6091]) (by decide +kernel)
def pv365461 : PrimeValue := ⟨365461, pr365461⟩
private theorem pr365467 : Nat.Prime 365467 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv3583]) (by decide +kernel)
def pv365467 : PrimeValue := ⟨365467, pr365467⟩
private theorem pr365527 : Nat.Prime 365527 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv967]) (by decide +kernel)
def pv365527 : PrimeValue := ⟨365527, pr365527⟩
private theorem pr365611 : Nat.Prime 365611 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv1741]) (by decide +kernel)
def pv365611 : PrimeValue := ⟨365611, pr365611⟩
private theorem pr365689 : Nat.Prime 365689 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv1693]) (by decide +kernel)
def pv365689 : PrimeValue := ⟨365689, pr365689⟩
private theorem pr365791 : Nat.Prime 365791 :=
  checkPrime_prime (q := pv61) (ls := [pv2,pv3,pv5,pv89,pv137]) (by decide +kernel)
def pv365791 : PrimeValue := ⟨365791, pr365791⟩
private theorem pr365809 : Nat.Prime 365809 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7621]) (by decide +kernel)
def pv365809 : PrimeValue := ⟨365809, pr365809⟩
private theorem pr365839 : Nat.Prime 365839 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv11,pv23,pv241]) (by decide +kernel)
def pv365839 : PrimeValue := ⟨365839, pr365839⟩
private theorem pr366001 : Nat.Prime 366001 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv61]) (by decide +kernel)
def pv366001 : PrimeValue := ⟨366001, pr366001⟩
private theorem pr366019 : Nat.Prime 366019 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv53,pv1151]) (by decide +kernel)
def pv366019 : PrimeValue := ⟨366019, pr366019⟩
private theorem pr366139 : Nat.Prime 366139 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv20341]) (by decide +kernel)
def pv366139 : PrimeValue := ⟨366139, pr366139⟩
private theorem pr366169 : Nat.Prime 366169 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv11,pv19,pv73]) (by decide +kernel)
def pv366169 : PrimeValue := ⟨366169, pr366169⟩
private theorem pr366211 : Nat.Prime 366211 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv313]) (by decide +kernel)
def pv366211 : PrimeValue := ⟨366211, pr366211⟩
private theorem pr366259 : Nat.Prime 366259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv61043]) (by decide +kernel)
def pv366259 : PrimeValue := ⟨366259, pr366259⟩
private theorem pr366383 : Nat.Prime 366383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv183191]) (by decide +kernel)
def pv366383 : PrimeValue := ⟨366383, pr366383⟩
private theorem pr366397 : Nat.Prime 366397 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv1607]) (by decide +kernel)
def pv366397 : PrimeValue := ⟨366397, pr366397⟩
private theorem pr366511 : Nat.Prime 366511 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv19,pv643]) (by decide +kernel)
def pv366511 : PrimeValue := ⟨366511, pr366511⟩
private theorem pr366517 : Nat.Prime 366517 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv10181]) (by decide +kernel)
def pv366517 : PrimeValue := ⟨366517, pr366517⟩
private theorem pr366631 : Nat.Prime 366631 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv11,pv101]) (by decide +kernel)
def pv366631 : PrimeValue := ⟨366631, pr366631⟩
private theorem pr366683 : Nat.Prime 366683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv139,pv1319]) (by decide +kernel)
def pv366683 : PrimeValue := ⟨366683, pr366683⟩
private theorem pr366703 : Nat.Prime 366703 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv8731]) (by decide +kernel)
def pv366703 : PrimeValue := ⟨366703, pr366703⟩
private theorem pr366869 : Nat.Prime 366869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv2237]) (by decide +kernel)
def pv366869 : PrimeValue := ⟨366869, pr366869⟩
private theorem pr366889 : Nat.Prime 366889 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv15287]) (by decide +kernel)
def pv366889 : PrimeValue := ⟨366889, pr366889⟩
private theorem pr366901 : Nat.Prime 366901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1223]) (by decide +kernel)
def pv366901 : PrimeValue := ⟨366901, pr366901⟩
private theorem pr367033 : Nat.Prime 367033 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv41,pv373]) (by decide +kernel)
def pv367033 : PrimeValue := ⟨367033, pr367033⟩
private theorem pr367123 : Nat.Prime 367123 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv8741]) (by decide +kernel)
def pv367123 : PrimeValue := ⟨367123, pr367123⟩
private theorem pr367189 : Nat.Prime 367189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv827]) (by decide +kernel)
def pv367189 : PrimeValue := ⟨367189, pr367189⟩
private theorem pr367229 : Nat.Prime 367229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv91807]) (by decide +kernel)
def pv367229 : PrimeValue := ⟨367229, pr367229⟩
private theorem pr367231 : Nat.Prime 367231 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv12241]) (by decide +kernel)
def pv367231 : PrimeValue := ⟨367231, pr367231⟩
private theorem pr367261 : Nat.Prime 367261 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv6121]) (by decide +kernel)
def pv367261 : PrimeValue := ⟨367261, pr367261⟩
private theorem pr367309 : Nat.Prime 367309 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv19,pv179]) (by decide +kernel)
def pv367309 : PrimeValue := ⟨367309, pr367309⟩
private theorem pr367321 : Nat.Prime 367321 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv3061]) (by decide +kernel)
def pv367321 : PrimeValue := ⟨367321, pr367321⟩
private theorem pr367391 : Nat.Prime 367391 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv36739]) (by decide +kernel)
def pv367391 : PrimeValue := ⟨367391, pr367391⟩
private theorem pr367453 : Nat.Prime 367453 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv59,pv173]) (by decide +kernel)
def pv367453 : PrimeValue := ⟨367453, pr367453⟩
private theorem pr367501 : Nat.Prime 367501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv367501 : PrimeValue := ⟨367501, pr367501⟩
private theorem pr367519 : Nat.Prime 367519 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv61253]) (by decide +kernel)
def pv367519 : PrimeValue := ⟨367519, pr367519⟩
private theorem pr367573 : Nat.Prime 367573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv30631]) (by decide +kernel)
def pv367573 : PrimeValue := ⟨367573, pr367573⟩
private theorem pr367613 : Nat.Prime 367613 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv19,pv691]) (by decide +kernel)
def pv367613 : PrimeValue := ⟨367613, pr367613⟩
private theorem pr367621 : Nat.Prime 367621 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv11,pv557]) (by decide +kernel)
def pv367621 : PrimeValue := ⟨367621, pr367621⟩
private theorem pr367673 : Nat.Prime 367673 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv45959]) (by decide +kernel)
def pv367673 : PrimeValue := ⟨367673, pr367673⟩
private theorem pr367711 : Nat.Prime 367711 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv17,pv103]) (by decide +kernel)
def pv367711 : PrimeValue := ⟨367711, pr367711⟩
private theorem pr367831 : Nat.Prime 367831 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv61,pv67]) (by decide +kernel)
def pv367831 : PrimeValue := ⟨367831, pr367831⟩
private theorem pr367879 : Nat.Prime 367879 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv19,pv461]) (by decide +kernel)
def pv367879 : PrimeValue := ⟨367879, pr367879⟩
private theorem pr367909 : Nat.Prime 367909 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv23,pv31,pv43]) (by decide +kernel)
def pv367909 : PrimeValue := ⟨367909, pr367909⟩
private theorem pr368111 : Nat.Prime 368111 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv131,pv281]) (by decide +kernel)
def pv368111 : PrimeValue := ⟨368111, pr368111⟩
private theorem pr368189 : Nat.Prime 368189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv83,pv1109]) (by decide +kernel)
def pv368189 : PrimeValue := ⟨368189, pr368189⟩
private theorem pr368233 : Nat.Prime 368233 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv67,pv229]) (by decide +kernel)
def pv368233 : PrimeValue := ⟨368233, pr368233⟩
private theorem pr368243 : Nat.Prime 368243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv29,pv907]) (by decide +kernel)
def pv368243 : PrimeValue := ⟨368243, pr368243⟩
private theorem pr368359 : Nat.Prime 368359 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv29,pv73]) (by decide +kernel)
def pv368359 : PrimeValue := ⟨368359, pr368359⟩
private theorem pr368471 : Nat.Prime 368471 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv36847]) (by decide +kernel)
def pv368471 : PrimeValue := ⟨368471, pr368471⟩
private theorem pr368551 : Nat.Prime 368551 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv13]) (by decide +kernel)
def pv368551 : PrimeValue := ⟨368551, pr368551⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
