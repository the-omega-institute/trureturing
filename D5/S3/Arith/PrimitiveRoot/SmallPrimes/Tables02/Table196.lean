/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table196
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table196.pv590609
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table014
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table024
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table037
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table084
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table085

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr590609 : Nat.Prime 590609 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv36913]) (by decide +kernel)
def pv590609 : PrimeValue := ⟨590609, pr590609⟩
private theorem pr590627 : Nat.Prime 590627 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv295313]) (by decide +kernel)
def pv590627 : PrimeValue := ⟨590627, pr590627⟩
private theorem pr590657 : Nat.Prime 590657 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv839]) (by decide +kernel)
def pv590657 : PrimeValue := ⟨590657, pr590657⟩
private theorem pr590669 : Nat.Prime 590669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv37,pv307]) (by decide +kernel)
def pv590669 : PrimeValue := ⟨590669, pr590669⟩
private theorem pr590867 : Nat.Prime 590867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv295433]) (by decide +kernel)
def pv590867 : PrimeValue := ⟨590867, pr590867⟩
private theorem pr591023 : Nat.Prime 591023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv17383]) (by decide +kernel)
def pv591023 : PrimeValue := ⟨591023, pr591023⟩
private theorem pr591163 : Nat.Prime 591163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv13,pv53]) (by decide +kernel)
def pv591163 : PrimeValue := ⟨591163, pr591163⟩
private theorem pr591233 : Nat.Prime 591233 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv149]) (by decide +kernel)
def pv591233 : PrimeValue := ⟨591233, pr591233⟩
private theorem pr591287 : Nat.Prime 591287 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv239,pv1237]) (by decide +kernel)
def pv591287 : PrimeValue := ⟨591287, pr591287⟩
private theorem pr591341 : Nat.Prime 591341 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv29567]) (by decide +kernel)
def pv591341 : PrimeValue := ⟨591341, pr591341⟩
private theorem pr591509 : Nat.Prime 591509 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv19,pv43,pv181]) (by decide +kernel)
def pv591509 : PrimeValue := ⟨591509, pr591509⟩
private theorem pr591553 : Nat.Prime 591553 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv13,pv79]) (by decide +kernel)
def pv591553 : PrimeValue := ⟨591553, pr591553⟩
private theorem pr591659 : Nat.Prime 591659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv101]) (by decide +kernel)
def pv591659 : PrimeValue := ⟨591659, pr591659⟩
private theorem pr591791 : Nat.Prime 591791 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv23,pv31,pv83]) (by decide +kernel)
def pv591791 : PrimeValue := ⟨591791, pr591791⟩
private theorem pr591887 : Nat.Prime 591887 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv295943]) (by decide +kernel)
def pv591887 : PrimeValue := ⟨591887, pr591887⟩
private theorem pr591973 : Nat.Prime 591973 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv49331]) (by decide +kernel)
def pv591973 : PrimeValue := ⟨591973, pr591973⟩
private theorem pr592019 : Nat.Prime 592019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv863]) (by decide +kernel)
def pv592019 : PrimeValue := ⟨592019, pr592019⟩
private theorem pr592139 : Nat.Prime 592139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv107,pv2767]) (by decide +kernel)
def pv592139 : PrimeValue := ⟨592139, pr592139⟩
private theorem pr592237 : Nat.Prime 592237 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv16451]) (by decide +kernel)
def pv592237 : PrimeValue := ⟨592237, pr592237⟩
private theorem pr592303 : Nat.Prime 592303 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv98717]) (by decide +kernel)
def pv592303 : PrimeValue := ⟨592303, pr592303⟩
private theorem pr592307 : Nat.Prime 592307 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv13,pv19,pv109]) (by decide +kernel)
def pv592307 : PrimeValue := ⟨592307, pr592307⟩
private theorem pr592343 : Nat.Prime 592343 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv23,pv79,pv163]) (by decide +kernel)
def pv592343 : PrimeValue := ⟨592343, pr592343⟩
private theorem pr592351 : Nat.Prime 592351 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv359]) (by decide +kernel)
def pv592351 : PrimeValue := ⟨592351, pr592351⟩
private theorem pr592367 : Nat.Prime 592367 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv296183]) (by decide +kernel)
def pv592367 : PrimeValue := ⟨592367, pr592367⟩
private theorem pr592393 : Nat.Prime 592393 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv24683]) (by decide +kernel)
def pv592393 : PrimeValue := ⟨592393, pr592393⟩
private theorem pr592507 : Nat.Prime 592507 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv32917]) (by decide +kernel)
def pv592507 : PrimeValue := ⟨592507, pr592507⟩
private theorem pr592517 : Nat.Prime 592517 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv167,pv887]) (by decide +kernel)
def pv592517 : PrimeValue := ⟨592517, pr592517⟩
private theorem pr592577 : Nat.Prime 592577 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv47,pv197]) (by decide +kernel)
def pv592577 : PrimeValue := ⟨592577, pr592577⟩
private theorem pr592661 : Nat.Prime 592661 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv29633]) (by decide +kernel)
def pv592661 : PrimeValue := ⟨592661, pr592661⟩
private theorem pr592681 : Nat.Prime 592681 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv11,pv449]) (by decide +kernel)
def pv592681 : PrimeValue := ⟨592681, pr592681⟩
private theorem pr592741 : Nat.Prime 592741 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv37,pv89]) (by decide +kernel)
def pv592741 : PrimeValue := ⟨592741, pr592741⟩
private theorem pr592861 : Nat.Prime 592861 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv41,pv241]) (by decide +kernel)
def pv592861 : PrimeValue := ⟨592861, pr592861⟩
private theorem pr592877 : Nat.Prime 592877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv29,pv269]) (by decide +kernel)
def pv592877 : PrimeValue := ⟨592877, pr592877⟩
private theorem pr592967 : Nat.Prime 592967 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv26953]) (by decide +kernel)
def pv592967 : PrimeValue := ⟨592967, pr592967⟩
private theorem pr593003 : Nat.Prime 593003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv479,pv619]) (by decide +kernel)
def pv593003 : PrimeValue := ⟨593003, pr593003⟩
private theorem pr593051 : Nat.Prime 593051 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv29,pv409]) (by decide +kernel)
def pv593051 : PrimeValue := ⟨593051, pr593051⟩
private theorem pr593171 : Nat.Prime 593171 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23,pv2579]) (by decide +kernel)
def pv593171 : PrimeValue := ⟨593171, pr593171⟩
private theorem pr593213 : Nat.Prime 593213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv148303]) (by decide +kernel)
def pv593213 : PrimeValue := ⟨593213, pr593213⟩
private theorem pr593231 : Nat.Prime 593231 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv5393]) (by decide +kernel)
def pv593231 : PrimeValue := ⟨593231, pr593231⟩
private theorem pr593233 : Nat.Prime 593233 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv727]) (by decide +kernel)
def pv593233 : PrimeValue := ⟨593233, pr593233⟩
private theorem pr593261 : Nat.Prime 593261 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv29663]) (by decide +kernel)
def pv593261 : PrimeValue := ⟨593261, pr593261⟩
private theorem pr593291 : Nat.Prime 593291 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv79,pv751]) (by decide +kernel)
def pv593291 : PrimeValue := ⟨593291, pr593291⟩
private theorem pr593297 : Nat.Prime 593297 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv3371]) (by decide +kernel)
def pv593297 : PrimeValue := ⟨593297, pr593297⟩
private theorem pr593321 : Nat.Prime 593321 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv5,pv7,pv13,pv163]) (by decide +kernel)
def pv593321 : PrimeValue := ⟨593321, pr593321⟩
private theorem pr593447 : Nat.Prime 593447 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv19,pv23,pv97]) (by decide +kernel)
def pv593447 : PrimeValue := ⟨593447, pr593447⟩
private theorem pr593519 : Nat.Prime 593519 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv167,pv1777]) (by decide +kernel)
def pv593519 : PrimeValue := ⟨593519, pr593519⟩
private theorem pr593633 : Nat.Prime 593633 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv1427]) (by decide +kernel)
def pv593633 : PrimeValue := ⟨593633, pr593633⟩
private theorem pr593641 : Nat.Prime 593641 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv17,pv97]) (by decide +kernel)
def pv593641 : PrimeValue := ⟨593641, pr593641⟩
private theorem pr593651 : Nat.Prime 593651 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv31,pv383]) (by decide +kernel)
def pv593651 : PrimeValue := ⟨593651, pr593651⟩
private theorem pr593711 : Nat.Prime 593711 :=
  checkPrime_prime (q := pv43) (ls := [pv2,pv5,pv13,pv4567]) (by decide +kernel)
def pv593711 : PrimeValue := ⟨593711, pr593711⟩
private theorem pr593777 : Nat.Prime 593777 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv37,pv59]) (by decide +kernel)
def pv593777 : PrimeValue := ⟨593777, pr593777⟩
private theorem pr594023 : Nat.Prime 594023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv13,pv31,pv67]) (by decide +kernel)
def pv594023 : PrimeValue := ⟨594023, pr594023⟩
private theorem pr594047 : Nat.Prime 594047 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv297023]) (by decide +kernel)
def pv594047 : PrimeValue := ⟨594047, pr594047⟩
private theorem pr594103 : Nat.Prime 594103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv99017]) (by decide +kernel)
def pv594103 : PrimeValue := ⟨594103, pr594103⟩
private theorem pr594107 : Nat.Prime 594107 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv127,pv2339]) (by decide +kernel)
def pv594107 : PrimeValue := ⟨594107, pr594107⟩
private theorem pr594137 : Nat.Prime 594137 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv3229]) (by decide +kernel)
def pv594137 : PrimeValue := ⟨594137, pr594137⟩
private theorem pr594161 : Nat.Prime 594161 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv1061]) (by decide +kernel)
def pv594161 : PrimeValue := ⟨594161, pr594161⟩
private theorem pr594241 : Nat.Prime 594241 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv619]) (by decide +kernel)
def pv594241 : PrimeValue := ⟨594241, pr594241⟩
private theorem pr594281 : Nat.Prime 594281 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv83,pv179]) (by decide +kernel)
def pv594281 : PrimeValue := ⟨594281, pr594281⟩
private theorem pr594311 : Nat.Prime 594311 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv103,pv577]) (by decide +kernel)
def pv594311 : PrimeValue := ⟨594311, pr594311⟩
private theorem pr594397 : Nat.Prime 594397 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv19,pv79]) (by decide +kernel)
def pv594397 : PrimeValue := ⟨594397, pr594397⟩
private theorem pr594401 : Nat.Prime 594401 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv743]) (by decide +kernel)
def pv594401 : PrimeValue := ⟨594401, pr594401⟩
private theorem pr594421 : Nat.Prime 594421 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv9907]) (by decide +kernel)
def pv594421 : PrimeValue := ⟨594421, pr594421⟩
private theorem pr594457 : Nat.Prime 594457 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv17,pv31,pv47]) (by decide +kernel)
def pv594457 : PrimeValue := ⟨594457, pr594457⟩
private theorem pr594569 : Nat.Prime 594569 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv5717]) (by decide +kernel)
def pv594569 : PrimeValue := ⟨594569, pr594569⟩
private theorem pr594617 : Nat.Prime 594617 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv29,pv233]) (by decide +kernel)
def pv594617 : PrimeValue := ⟨594617, pr594617⟩
private theorem pr594641 : Nat.Prime 594641 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7433]) (by decide +kernel)
def pv594641 : PrimeValue := ⟨594641, pr594641⟩
private theorem pr594653 : Nat.Prime 594653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv148663]) (by decide +kernel)
def pv594653 : PrimeValue := ⟨594653, pr594653⟩
private theorem pr594827 : Nat.Prime 594827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv67,pv193]) (by decide +kernel)
def pv594827 : PrimeValue := ⟨594827, pr594827⟩
private theorem pr594857 : Nat.Prime 594857 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv74357]) (by decide +kernel)
def pv594857 : PrimeValue := ⟨594857, pr594857⟩
private theorem pr594899 : Nat.Prime 594899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv17497]) (by decide +kernel)
def pv594899 : PrimeValue := ⟨594899, pr594899⟩
private theorem pr594977 : Nat.Prime 594977 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv18593]) (by decide +kernel)
def pv594977 : PrimeValue := ⟨594977, pr594977⟩
private theorem pr594989 : Nat.Prime 594989 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv148747]) (by decide +kernel)
def pv594989 : PrimeValue := ⟨594989, pr594989⟩
private theorem pr595037 : Nat.Prime 595037 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv11443]) (by decide +kernel)
def pv595037 : PrimeValue := ⟨595037, pr595037⟩
private theorem pr595073 : Nat.Prime 595073 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv4649]) (by decide +kernel)
def pv595073 : PrimeValue := ⟨595073, pr595073⟩
private theorem pr595097 : Nat.Prime 595097 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv73,pv1019]) (by decide +kernel)
def pv595097 : PrimeValue := ⟨595097, pr595097⟩
private theorem pr595117 : Nat.Prime 595117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv61,pv271]) (by decide +kernel)
def pv595117 : PrimeValue := ⟨595117, pr595117⟩
private theorem pr595157 : Nat.Prime 595157 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv41,pv191]) (by decide +kernel)
def pv595157 : PrimeValue := ⟨595157, pr595157⟩
private theorem pr595271 : Nat.Prime 595271 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv13,pv19,pv241]) (by decide +kernel)
def pv595271 : PrimeValue := ⟨595271, pr595271⟩
private theorem pr595291 : Nat.Prime 595291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv19843]) (by decide +kernel)
def pv595291 : PrimeValue := ⟨595291, pr595291⟩
private theorem pr595333 : Nat.Prime 595333 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23,pv719]) (by decide +kernel)
def pv595333 : PrimeValue := ⟨595333, pr595333⟩
private theorem pr595381 : Nat.Prime 595381 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv9923]) (by decide +kernel)
def pv595381 : PrimeValue := ⟨595381, pr595381⟩
private theorem pr595411 : Nat.Prime 595411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv89,pv223]) (by decide +kernel)
def pv595411 : PrimeValue := ⟨595411, pr595411⟩
private theorem pr595451 : Nat.Prime 595451 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11909]) (by decide +kernel)
def pv595451 : PrimeValue := ⟨595451, pr595451⟩
private theorem pr595481 : Nat.Prime 595481 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv14887]) (by decide +kernel)
def pv595481 : PrimeValue := ⟨595481, pr595481⟩
private theorem pr595523 : Nat.Prime 595523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv167,pv1783]) (by decide +kernel)
def pv595523 : PrimeValue := ⟨595523, pr595523⟩
private theorem pr595613 : Nat.Prime 595613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv19,pv461]) (by decide +kernel)
def pv595613 : PrimeValue := ⟨595613, pr595613⟩
private theorem pr595877 : Nat.Prime 595877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv311,pv479]) (by decide +kernel)
def pv595877 : PrimeValue := ⟨595877, pr595877⟩
private theorem pr595951 : Nat.Prime 595951 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv29,pv137]) (by decide +kernel)
def pv595951 : PrimeValue := ⟨595951, pr595951⟩
private theorem pr596009 : Nat.Prime 596009 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv29,pv367]) (by decide +kernel)
def pv596009 : PrimeValue := ⟨596009, pr596009⟩
private theorem pr596021 : Nat.Prime 596021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv1753]) (by decide +kernel)
def pv596021 : PrimeValue := ⟨596021, pr596021⟩
private theorem pr596027 : Nat.Prime 596027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv298013]) (by decide +kernel)
def pv596027 : PrimeValue := ⟨596027, pr596027⟩
private theorem pr596047 : Nat.Prime 596047 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv821]) (by decide +kernel)
def pv596047 : PrimeValue := ⟨596047, pr596047⟩
private theorem pr596053 : Nat.Prime 596053 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv5519]) (by decide +kernel)
def pv596053 : PrimeValue := ⟨596053, pr596053⟩
private theorem pr596117 : Nat.Prime 596117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv71,pv2099]) (by decide +kernel)
def pv596117 : PrimeValue := ⟨596117, pr596117⟩
private theorem pr596159 : Nat.Prime 596159 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv173,pv1723]) (by decide +kernel)
def pv596159 : PrimeValue := ⟨596159, pr596159⟩
private theorem pr596243 : Nat.Prime 596243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv6343]) (by decide +kernel)
def pv596243 : PrimeValue := ⟨596243, pr596243⟩
private theorem pr596251 : Nat.Prime 596251 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv53]) (by decide +kernel)
def pv596251 : PrimeValue := ⟨596251, pr596251⟩
private theorem pr596257 : Nat.Prime 596257 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv6211]) (by decide +kernel)
def pv596257 : PrimeValue := ⟨596257, pr596257⟩
private theorem pr596291 : Nat.Prime 596291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv59629]) (by decide +kernel)
def pv596291 : PrimeValue := ⟨596291, pr596291⟩
private theorem pr596507 : Nat.Prime 596507 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv101,pv2953]) (by decide +kernel)
def pv596507 : PrimeValue := ⟨596507, pr596507⟩
private theorem pr596587 : Nat.Prime 596587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv99431]) (by decide +kernel)
def pv596587 : PrimeValue := ⟨596587, pr596587⟩
private theorem pr596851 : Nat.Prime 596851 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv23,pv173]) (by decide +kernel)
def pv596851 : PrimeValue := ⟨596851, pr596851⟩
private theorem pr596861 : Nat.Prime 596861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv2713]) (by decide +kernel)
def pv596861 : PrimeValue := ⟨596861, pr596861⟩
private theorem pr596917 : Nat.Prime 596917 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5527]) (by decide +kernel)
def pv596917 : PrimeValue := ⟨596917, pr596917⟩
private theorem pr596927 : Nat.Prime 596927 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv43,pv631]) (by decide +kernel)
def pv596927 : PrimeValue := ⟨596927, pr596927⟩
private theorem pr596963 : Nat.Prime 596963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv59,pv5059]) (by decide +kernel)
def pv596963 : PrimeValue := ⟨596963, pr596963⟩
private theorem pr596987 : Nat.Prime 596987 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv22961]) (by decide +kernel)
def pv596987 : PrimeValue := ⟨596987, pr596987⟩
private theorem pr597137 : Nat.Prime 597137 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv37321]) (by decide +kernel)
def pv597137 : PrimeValue := ⟨597137, pr597137⟩
private theorem pr597263 : Nat.Prime 597263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv298631]) (by decide +kernel)
def pv597263 : PrimeValue := ⟨597263, pr597263⟩
private theorem pr597269 : Nat.Prime 597269 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv83,pv257]) (by decide +kernel)
def pv597269 : PrimeValue := ⟨597269, pr597269⟩
private theorem pr597307 : Nat.Prime 597307 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv99551]) (by decide +kernel)
def pv597307 : PrimeValue := ⟨597307, pr597307⟩
private theorem pr597419 : Nat.Prime 597419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv298709]) (by decide +kernel)
def pv597419 : PrimeValue := ⟨597419, pr597419⟩
private theorem pr597437 : Nat.Prime 597437 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv19,pv1123]) (by decide +kernel)
def pv597437 : PrimeValue := ⟨597437, pr597437⟩
private theorem pr597497 : Nat.Prime 597497 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv74687]) (by decide +kernel)
def pv597497 : PrimeValue := ⟨597497, pr597497⟩
private theorem pr597523 : Nat.Prime 597523 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv53,pv1879]) (by decide +kernel)
def pv597523 : PrimeValue := ⟨597523, pr597523⟩
private theorem pr597551 : Nat.Prime 597551 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv17,pv19,pv37]) (by decide +kernel)
def pv597551 : PrimeValue := ⟨597551, pr597551⟩
private theorem pr597581 : Nat.Prime 597581 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv29879]) (by decide +kernel)
def pv597581 : PrimeValue := ⟨597581, pr597581⟩
private theorem pr597613 : Nat.Prime 597613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv49801]) (by decide +kernel)
def pv597613 : PrimeValue := ⟨597613, pr597613⟩
private theorem pr597637 : Nat.Prime 597637 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv1277]) (by decide +kernel)
def pv597637 : PrimeValue := ⟨597637, pr597637⟩
private theorem pr597643 : Nat.Prime 597643 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv99607]) (by decide +kernel)
def pv597643 : PrimeValue := ⟨597643, pr597643⟩
private theorem pr597677 : Nat.Prime 597677 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv149419]) (by decide +kernel)
def pv597677 : PrimeValue := ⟨597677, pr597677⟩
private theorem pr597757 : Nat.Prime 597757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv109,pv457]) (by decide +kernel)
def pv597757 : PrimeValue := ⟨597757, pr597757⟩
private theorem pr597803 : Nat.Prime 597803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv499,pv599]) (by decide +kernel)
def pv597803 : PrimeValue := ⟨597803, pr597803⟩
private theorem pr597901 : Nat.Prime 597901 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv1993]) (by decide +kernel)
def pv597901 : PrimeValue := ⟨597901, pr597901⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
