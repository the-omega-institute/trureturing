/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table207
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table207.pv697951
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table027
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table043
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table093

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr697951 : Nat.Prime 697951 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv47]) (by decide +kernel)
def pv697951 : PrimeValue := ⟨697951, pr697951⟩
private theorem pr697973 : Nat.Prime 697973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv29,pv547]) (by decide +kernel)
def pv697973 : PrimeValue := ⟨697973, pr697973⟩
private theorem pr698021 : Nat.Prime 698021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv2053]) (by decide +kernel)
def pv698021 : PrimeValue := ⟨698021, pr698021⟩
private theorem pr698171 : Nat.Prime 698171 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv577]) (by decide +kernel)
def pv698171 : PrimeValue := ⟨698171, pr698171⟩
private theorem pr698183 : Nat.Prime 698183 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv31,pv11261]) (by decide +kernel)
def pv698183 : PrimeValue := ⟨698183, pr698183⟩
private theorem pr698393 : Nat.Prime 698393 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv87299]) (by decide +kernel)
def pv698393 : PrimeValue := ⟨698393, pr698393⟩
private theorem pr698417 : Nat.Prime 698417 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv43651]) (by decide +kernel)
def pv698417 : PrimeValue := ⟨698417, pr698417⟩
private theorem pr698507 : Nat.Prime 698507 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv311,pv1123]) (by decide +kernel)
def pv698507 : PrimeValue := ⟨698507, pr698507⟩
private theorem pr698567 : Nat.Prime 698567 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv113,pv281]) (by decide +kernel)
def pv698567 : PrimeValue := ⟨698567, pr698567⟩
private theorem pr698653 : Nat.Prime 698653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv6469]) (by decide +kernel)
def pv698653 : PrimeValue := ⟨698653, pr698653⟩
private theorem pr698827 : Nat.Prime 698827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv116471]) (by decide +kernel)
def pv698827 : PrimeValue := ⟨698827, pr698827⟩
private theorem pr699001 : Nat.Prime 699001 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv233]) (by decide +kernel)
def pv699001 : PrimeValue := ⟨699001, pr699001⟩
private theorem pr699073 : Nat.Prime 699073 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv331]) (by decide +kernel)
def pv699073 : PrimeValue := ⟨699073, pr699073⟩
private theorem pr699151 : Nat.Prime 699151 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv59,pv79]) (by decide +kernel)
def pv699151 : PrimeValue := ⟨699151, pr699151⟩
private theorem pr699197 : Nat.Prime 699197 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv174799]) (by decide +kernel)
def pv699197 : PrimeValue := ⟨699197, pr699197⟩
private theorem pr699221 : Nat.Prime 699221 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv34961]) (by decide +kernel)
def pv699221 : PrimeValue := ⟨699221, pr699221⟩
private theorem pr699383 : Nat.Prime 699383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv241,pv1451]) (by decide +kernel)
def pv699383 : PrimeValue := ⟨699383, pr699383⟩
private theorem pr699401 : Nat.Prime 699401 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv269]) (by decide +kernel)
def pv699401 : PrimeValue := ⟨699401, pr699401⟩
private theorem pr699443 : Nat.Prime 699443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv191,pv1831]) (by decide +kernel)
def pv699443 : PrimeValue := ⟨699443, pr699443⟩
private theorem pr699463 : Nat.Prime 699463 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv12953]) (by decide +kernel)
def pv699463 : PrimeValue := ⟨699463, pr699463⟩
private theorem pr699527 : Nat.Prime 699527 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv101,pv3463]) (by decide +kernel)
def pv699527 : PrimeValue := ⟨699527, pr699527⟩
private theorem pr699557 : Nat.Prime 699557 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv13,pv1223]) (by decide +kernel)
def pv699557 : PrimeValue := ⟨699557, pr699557⟩
private theorem pr699757 : Nat.Prime 699757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv58313]) (by decide +kernel)
def pv699757 : PrimeValue := ⟨699757, pr699757⟩
private theorem pr699761 : Nat.Prime 699761 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv8747]) (by decide +kernel)
def pv699761 : PrimeValue := ⟨699761, pr699761⟩
private theorem pr699793 : Nat.Prime 699793 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv61,pv239]) (by decide +kernel)
def pv699793 : PrimeValue := ⟨699793, pr699793⟩
private theorem pr699943 : Nat.Prime 699943 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv116657]) (by decide +kernel)
def pv699943 : PrimeValue := ⟨699943, pr699943⟩
private theorem pr699967 : Nat.Prime 699967 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv37,pv1051]) (by decide +kernel)
def pv699967 : PrimeValue := ⟨699967, pr699967⟩
private theorem pr700067 : Nat.Prime 700067 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv350033]) (by decide +kernel)
def pv700067 : PrimeValue := ⟨700067, pr700067⟩
private theorem pr700081 : Nat.Prime 700081 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv2917]) (by decide +kernel)
def pv700081 : PrimeValue := ⟨700081, pr700081⟩
private theorem pr700087 : Nat.Prime 700087 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv116681]) (by decide +kernel)
def pv700087 : PrimeValue := ⟨700087, pr700087⟩
private theorem pr700201 : Nat.Prime 700201 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv389]) (by decide +kernel)
def pv700201 : PrimeValue := ⟨700201, pr700201⟩
private theorem pr700241 : Nat.Prime 700241 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv8753]) (by decide +kernel)
def pv700241 : PrimeValue := ⟨700241, pr700241⟩
private theorem pr700307 : Nat.Prime 700307 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv487,pv719]) (by decide +kernel)
def pv700307 : PrimeValue := ⟨700307, pr700307⟩
private theorem pr700361 : Nat.Prime 700361 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17509]) (by decide +kernel)
def pv700361 : PrimeValue := ⟨700361, pr700361⟩
private theorem pr700367 : Nat.Prime 700367 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv20599]) (by decide +kernel)
def pv700367 : PrimeValue := ⟨700367, pr700367⟩
private theorem pr700471 : Nat.Prime 700471 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv43,pv181]) (by decide +kernel)
def pv700471 : PrimeValue := ⟨700471, pr700471⟩
private theorem pr700523 : Nat.Prime 700523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv227,pv1543]) (by decide +kernel)
def pv700523 : PrimeValue := ⟨700523, pr700523⟩
private theorem pr700597 : Nat.Prime 700597 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv499]) (by decide +kernel)
def pv700597 : PrimeValue := ⟨700597, pr700597⟩
private theorem pr700633 : Nat.Prime 700633 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv37,pv263]) (by decide +kernel)
def pv700633 : PrimeValue := ⟨700633, pr700633⟩
private theorem pr700781 : Nat.Prime 700781 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv37,pv947]) (by decide +kernel)
def pv700781 : PrimeValue := ⟨700781, pr700781⟩
private theorem pr700801 : Nat.Prime 700801 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv73]) (by decide +kernel)
def pv700801 : PrimeValue := ⟨700801, pr700801⟩
private theorem pr700933 : Nat.Prime 700933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv58411]) (by decide +kernel)
def pv700933 : PrimeValue := ⟨700933, pr700933⟩
private theorem pr700937 : Nat.Prime 700937 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv41,pv2137]) (by decide +kernel)
def pv700937 : PrimeValue := ⟨700937, pr700937⟩
private theorem pr700963 : Nat.Prime 700963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv116827]) (by decide +kernel)
def pv700963 : PrimeValue := ⟨700963, pr700963⟩
private theorem pr701117 : Nat.Prime 701117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv97,pv139]) (by decide +kernel)
def pv701117 : PrimeValue := ⟨701117, pr701117⟩
private theorem pr701357 : Nat.Prime 701357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv67,pv2617]) (by decide +kernel)
def pv701357 : PrimeValue := ⟨701357, pr701357⟩
private theorem pr701531 : Nat.Prime 701531 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv31,pv73]) (by decide +kernel)
def pv701531 : PrimeValue := ⟨701531, pr701531⟩
private theorem pr701627 : Nat.Prime 701627 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv12097]) (by decide +kernel)
def pv701627 : PrimeValue := ⟨701627, pr701627⟩
private theorem pr701741 : Nat.Prime 701741 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv13,pv2699]) (by decide +kernel)
def pv701741 : PrimeValue := ⟨701741, pr701741⟩
private theorem pr701837 : Nat.Prime 701837 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79,pv2221]) (by decide +kernel)
def pv701837 : PrimeValue := ⟨701837, pr701837⟩
private theorem pr701957 : Nat.Prime 701957 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv113,pv1553]) (by decide +kernel)
def pv701957 : PrimeValue := ⟨701957, pr701957⟩
private theorem pr702113 : Nat.Prime 702113 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv37,pv593]) (by decide +kernel)
def pv702113 : PrimeValue := ⟨702113, pr702113⟩
private theorem pr702127 : Nat.Prime 702127 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv2053]) (by decide +kernel)
def pv702127 : PrimeValue := ⟨702127, pr702127⟩
private theorem pr702193 : Nat.Prime 702193 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv14629]) (by decide +kernel)
def pv702193 : PrimeValue := ⟨702193, pr702193⟩
private theorem pr702257 : Nat.Prime 702257 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv43891]) (by decide +kernel)
def pv702257 : PrimeValue := ⟨702257, pr702257⟩
private theorem pr702413 : Nat.Prime 702413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv4283]) (by decide +kernel)
def pv702413 : PrimeValue := ⟨702413, pr702413⟩
private theorem pr702721 : Nat.Prime 702721 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv61]) (by decide +kernel)
def pv702721 : PrimeValue := ⟨702721, pr702721⟩
private theorem pr702803 : Nat.Prime 702803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv351401]) (by decide +kernel)
def pv702803 : PrimeValue := ⟨702803, pr702803⟩
private theorem pr702827 : Nat.Prime 702827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv351413]) (by decide +kernel)
def pv702827 : PrimeValue := ⟨702827, pr702827⟩
private theorem pr702881 : Nat.Prime 702881 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv23,pv191]) (by decide +kernel)
def pv702881 : PrimeValue := ⟨702881, pr702881⟩
private theorem pr702937 : Nat.Prime 702937 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv13,pv751]) (by decide +kernel)
def pv702937 : PrimeValue := ⟨702937, pr702937⟩
private theorem pr703033 : Nat.Prime 703033 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv2663]) (by decide +kernel)
def pv703033 : PrimeValue := ⟨703033, pr703033⟩
private theorem pr703127 : Nat.Prime 703127 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv351563]) (by decide +kernel)
def pv703127 : PrimeValue := ⟨703127, pr703127⟩
private theorem pr703141 : Nat.Prime 703141 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11719]) (by decide +kernel)
def pv703141 : PrimeValue := ⟨703141, pr703141⟩
private theorem pr703331 : Nat.Prime 703331 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv61,pv1153]) (by decide +kernel)
def pv703331 : PrimeValue := ⟨703331, pr703331⟩
private theorem pr703357 : Nat.Prime 703357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv58613]) (by decide +kernel)
def pv703357 : PrimeValue := ⟨703357, pr703357⟩
private theorem pr703537 : Nat.Prime 703537 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv14657]) (by decide +kernel)
def pv703537 : PrimeValue := ⟨703537, pr703537⟩
private theorem pr703631 : Nat.Prime 703631 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv17,pv4139]) (by decide +kernel)
def pv703631 : PrimeValue := ⟨703631, pr703631⟩
private theorem pr703897 : Nat.Prime 703897 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv139,pv211]) (by decide +kernel)
def pv703897 : PrimeValue := ⟨703897, pr703897⟩
private theorem pr704023 : Nat.Prime 704023 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv10667]) (by decide +kernel)
def pv704023 : PrimeValue := ⟨704023, pr704023⟩
private theorem pr704101 : Nat.Prime 704101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv2347]) (by decide +kernel)
def pv704101 : PrimeValue := ⟨704101, pr704101⟩
private theorem pr704111 : Nat.Prime 704111 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv37,pv173]) (by decide +kernel)
def pv704111 : PrimeValue := ⟨704111, pr704111⟩
private theorem pr704161 : Nat.Prime 704161 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv163]) (by decide +kernel)
def pv704161 : PrimeValue := ⟨704161, pr704161⟩
private theorem pr704441 : Nat.Prime 704441 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv1601]) (by decide +kernel)
def pv704441 : PrimeValue := ⟨704441, pr704441⟩
private theorem pr704461 : Nat.Prime 704461 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv59,pv199]) (by decide +kernel)
def pv704461 : PrimeValue := ⟨704461, pr704461⟩
private theorem pr704507 : Nat.Prime 704507 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv31,pv1033]) (by decide +kernel)
def pv704507 : PrimeValue := ⟨704507, pr704507⟩
private theorem pr704731 : Nat.Prime 704731 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv13,pv139]) (by decide +kernel)
def pv704731 : PrimeValue := ⟨704731, pr704731⟩
private theorem pr704807 : Nat.Prime 704807 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv352403]) (by decide +kernel)
def pv704807 : PrimeValue := ⟨704807, pr704807⟩
private theorem pr704857 : Nat.Prime 704857 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv43,pv683]) (by decide +kernel)
def pv704857 : PrimeValue := ⟨704857, pr704857⟩
private theorem pr704861 : Nat.Prime 704861 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv2711]) (by decide +kernel)
def pv704861 : PrimeValue := ⟨704861, pr704861⟩
private theorem pr704897 : Nat.Prime 704897 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5507]) (by decide +kernel)
def pv704897 : PrimeValue := ⟨704897, pr704897⟩
private theorem pr705247 : Nat.Prime 705247 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv117541]) (by decide +kernel)
def pv705247 : PrimeValue := ⟨705247, pr705247⟩
private theorem pr705437 : Nat.Prime 705437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv5689]) (by decide +kernel)
def pv705437 : PrimeValue := ⟨705437, pr705437⟩
private theorem pr705533 : Nat.Prime 705533 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv176383]) (by decide +kernel)
def pv705533 : PrimeValue := ⟨705533, pr705533⟩
private theorem pr705631 : Nat.Prime 705631 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv43,pv547]) (by decide +kernel)
def pv705631 : PrimeValue := ⟨705631, pr705631⟩
private theorem pr705737 : Nat.Prime 705737 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv4643]) (by decide +kernel)
def pv705737 : PrimeValue := ⟨705737, pr705737⟩
private theorem pr705787 : Nat.Prime 705787 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv79,pv1489]) (by decide +kernel)
def pv705787 : PrimeValue := ⟨705787, pr705787⟩
private theorem pr705821 : Nat.Prime 705821 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv35291]) (by decide +kernel)
def pv705821 : PrimeValue := ⟨705821, pr705821⟩
private theorem pr705827 : Nat.Prime 705827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv32083]) (by decide +kernel)
def pv705827 : PrimeValue := ⟨705827, pr705827⟩
private theorem pr705883 : Nat.Prime 705883 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv71,pv1657]) (by decide +kernel)
def pv705883 : PrimeValue := ⟨705883, pr705883⟩
private theorem pr706051 : Nat.Prime 706051 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv523]) (by decide +kernel)
def pv706051 : PrimeValue := ⟨706051, pr706051⟩
private theorem pr706117 : Nat.Prime 706117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv163]) (by decide +kernel)
def pv706117 : PrimeValue := ⟨706117, pr706117⟩
private theorem pr706267 : Nat.Prime 706267 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv29,pv41]) (by decide +kernel)
def pv706267 : PrimeValue := ⟨706267, pr706267⟩
private theorem pr706283 : Nat.Prime 706283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv20773]) (by decide +kernel)
def pv706283 : PrimeValue := ⟨706283, pr706283⟩
private theorem pr706291 : Nat.Prime 706291 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv1811]) (by decide +kernel)
def pv706291 : PrimeValue := ⟨706291, pr706291⟩
private theorem pr706507 : Nat.Prime 706507 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv117751]) (by decide +kernel)
def pv706507 : PrimeValue := ⟨706507, pr706507⟩
private theorem pr706621 : Nat.Prime 706621 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv11777]) (by decide +kernel)
def pv706621 : PrimeValue := ⟨706621, pr706621⟩
private theorem pr706703 : Nat.Prime 706703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv53,pv59,pv113]) (by decide +kernel)
def pv706703 : PrimeValue := ⟨706703, pr706703⟩
private theorem pr706733 : Nat.Prime 706733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv13591]) (by decide +kernel)
def pv706733 : PrimeValue := ⟨706733, pr706733⟩
private theorem pr706753 : Nat.Prime 706753 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv409]) (by decide +kernel)
def pv706753 : PrimeValue := ⟨706753, pr706753⟩
private theorem pr706801 : Nat.Prime 706801 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv19,pv31]) (by decide +kernel)
def pv706801 : PrimeValue := ⟨706801, pr706801⟩
private theorem pr706837 : Nat.Prime 706837 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv23,pv197]) (by decide +kernel)
def pv706837 : PrimeValue := ⟨706837, pr706837⟩
private theorem pr706907 : Nat.Prime 706907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv353453]) (by decide +kernel)
def pv706907 : PrimeValue := ⟨706907, pr706907⟩
private theorem pr706943 : Nat.Prime 706943 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv353471]) (by decide +kernel)
def pv706943 : PrimeValue := ⟨706943, pr706943⟩
private theorem pr707143 : Nat.Prime 707143 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv6203]) (by decide +kernel)
def pv707143 : PrimeValue := ⟨707143, pr707143⟩
private theorem pr707191 : Nat.Prime 707191 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv2143]) (by decide +kernel)
def pv707191 : PrimeValue := ⟨707191, pr707191⟩
private theorem pr707321 : Nat.Prime 707321 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17683]) (by decide +kernel)
def pv707321 : PrimeValue := ⟨707321, pr707321⟩
private theorem pr707383 : Nat.Prime 707383 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv3023]) (by decide +kernel)
def pv707383 : PrimeValue := ⟨707383, pr707383⟩
private theorem pr707543 : Nat.Prime 707543 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv11,pv29,pv1109]) (by decide +kernel)
def pv707543 : PrimeValue := ⟨707543, pr707543⟩
private theorem pr707633 : Nat.Prime 707633 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv47,pv941]) (by decide +kernel)
def pv707633 : PrimeValue := ⟨707633, pr707633⟩
private theorem pr707717 : Nat.Prime 707717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv6101]) (by decide +kernel)
def pv707717 : PrimeValue := ⟨707717, pr707717⟩
private theorem pr707801 : Nat.Prime 707801 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv3539]) (by decide +kernel)
def pv707801 : PrimeValue := ⟨707801, pr707801⟩
private theorem pr707831 : Nat.Prime 707831 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv70783]) (by decide +kernel)
def pv707831 : PrimeValue := ⟨707831, pr707831⟩
private theorem pr707923 : Nat.Prime 707923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv67,pv587]) (by decide +kernel)
def pv707923 : PrimeValue := ⟨707923, pr707923⟩
private theorem pr707951 : Nat.Prime 707951 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv14159]) (by decide +kernel)
def pv707951 : PrimeValue := ⟨707951, pr707951⟩
private theorem pr707957 : Nat.Prime 707957 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv176989]) (by decide +kernel)
def pv707957 : PrimeValue := ⟨707957, pr707957⟩
private theorem pr708007 : Nat.Prime 708007 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv29,pv313]) (by decide +kernel)
def pv708007 : PrimeValue := ⟨708007, pr708007⟩
private theorem pr708017 : Nat.Prime 708017 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv19,pv137]) (by decide +kernel)
def pv708017 : PrimeValue := ⟨708017, pr708017⟩
private theorem pr708031 : Nat.Prime 708031 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7867]) (by decide +kernel)
def pv708031 : PrimeValue := ⟨708031, pr708031⟩
private theorem pr708053 : Nat.Prime 708053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv177013]) (by decide +kernel)
def pv708053 : PrimeValue := ⟨708053, pr708053⟩
private theorem pr708137 : Nat.Prime 708137 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv13,pv619]) (by decide +kernel)
def pv708137 : PrimeValue := ⟨708137, pr708137⟩
private theorem pr708161 : Nat.Prime 708161 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv2213]) (by decide +kernel)
def pv708161 : PrimeValue := ⟨708161, pr708161⟩
private theorem pr708221 : Nat.Prime 708221 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv2083]) (by decide +kernel)
def pv708221 : PrimeValue := ⟨708221, pr708221⟩
private theorem pr708287 : Nat.Prime 708287 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv354143]) (by decide +kernel)
def pv708287 : PrimeValue := ⟨708287, pr708287⟩
private theorem pr708311 : Nat.Prime 708311 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv193,pv367]) (by decide +kernel)
def pv708311 : PrimeValue := ⟨708311, pr708311⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
