/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table039
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table039.pv103231
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table005
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table007
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table008
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table021

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr103231 : Nat.Prime 103231 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv31,pv37]) (by decide +kernel)
def pv103231 : PrimeValue := ⟨103231, pr103231⟩
private theorem pr103237 : Nat.Prime 103237 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv1229]) (by decide +kernel)
def pv103237 : PrimeValue := ⟨103237, pr103237⟩
private theorem pr103289 : Nat.Prime 103289 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv12911]) (by decide +kernel)
def pv103289 : PrimeValue := ⟨103289, pr103289⟩
private theorem pr103291 : Nat.Prime 103291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv313]) (by decide +kernel)
def pv103291 : PrimeValue := ⟨103291, pr103291⟩
private theorem pr103319 : Nat.Prime 103319 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv51659]) (by decide +kernel)
def pv103319 : PrimeValue := ⟨103319, pr103319⟩
private theorem pr103333 : Nat.Prime 103333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv79,pv109]) (by decide +kernel)
def pv103333 : PrimeValue := ⟨103333, pr103333⟩
private theorem pr103349 : Nat.Prime 103349 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv3691]) (by decide +kernel)
def pv103349 : PrimeValue := ⟨103349, pr103349⟩
private theorem pr103357 : Nat.Prime 103357 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv11,pv29]) (by decide +kernel)
def pv103357 : PrimeValue := ⟨103357, pr103357⟩
private theorem pr103387 : Nat.Prime 103387 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17231]) (by decide +kernel)
def pv103387 : PrimeValue := ⟨103387, pr103387⟩
private theorem pr103391 : Nat.Prime 103391 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv211]) (by decide +kernel)
def pv103391 : PrimeValue := ⟨103391, pr103391⟩
private theorem pr103393 : Nat.Prime 103393 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv359]) (by decide +kernel)
def pv103393 : PrimeValue := ⟨103393, pr103393⟩
private theorem pr103399 : Nat.Prime 103399 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv907]) (by decide +kernel)
def pv103399 : PrimeValue := ⟨103399, pr103399⟩
private theorem pr103409 : Nat.Prime 103409 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv281]) (by decide +kernel)
def pv103409 : PrimeValue := ⟨103409, pr103409⟩
private theorem pr103421 : Nat.Prime 103421 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv5171]) (by decide +kernel)
def pv103421 : PrimeValue := ⟨103421, pr103421⟩
private theorem pr103423 : Nat.Prime 103423 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv1567]) (by decide +kernel)
def pv103423 : PrimeValue := ⟨103423, pr103423⟩
private theorem pr103451 : Nat.Prime 103451 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv2069]) (by decide +kernel)
def pv103451 : PrimeValue := ⟨103451, pr103451⟩
private theorem pr103457 : Nat.Prime 103457 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv53,pv61]) (by decide +kernel)
def pv103457 : PrimeValue := ⟨103457, pr103457⟩
private theorem pr103471 : Nat.Prime 103471 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv3449]) (by decide +kernel)
def pv103471 : PrimeValue := ⟨103471, pr103471⟩
private theorem pr103529 : Nat.Prime 103529 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv12941]) (by decide +kernel)
def pv103529 : PrimeValue := ⟨103529, pr103529⟩
private theorem pr103549 : Nat.Prime 103549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv8629]) (by decide +kernel)
def pv103549 : PrimeValue := ⟨103549, pr103549⟩
private theorem pr103553 : Nat.Prime 103553 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv809]) (by decide +kernel)
def pv103553 : PrimeValue := ⟨103553, pr103553⟩
private theorem pr103561 : Nat.Prime 103561 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv863]) (by decide +kernel)
def pv103561 : PrimeValue := ⟨103561, pr103561⟩
private theorem pr103567 : Nat.Prime 103567 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv41,pv421]) (by decide +kernel)
def pv103567 : PrimeValue := ⟨103567, pr103567⟩
private theorem pr103573 : Nat.Prime 103573 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv137]) (by decide +kernel)
def pv103573 : PrimeValue := ⟨103573, pr103573⟩
private theorem pr103577 : Nat.Prime 103577 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv107]) (by decide +kernel)
def pv103577 : PrimeValue := ⟨103577, pr103577⟩
private theorem pr103583 : Nat.Prime 103583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv67,pv773]) (by decide +kernel)
def pv103583 : PrimeValue := ⟨103583, pr103583⟩
private theorem pr103591 : Nat.Prime 103591 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv1151]) (by decide +kernel)
def pv103591 : PrimeValue := ⟨103591, pr103591⟩
private theorem pr103613 : Nat.Prime 103613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv25903]) (by decide +kernel)
def pv103613 : PrimeValue := ⟨103613, pr103613⟩
private theorem pr103619 : Nat.Prime 103619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv103,pv503]) (by decide +kernel)
def pv103619 : PrimeValue := ⟨103619, pr103619⟩
private theorem pr103643 : Nat.Prime 103643 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv673]) (by decide +kernel)
def pv103643 : PrimeValue := ⟨103643, pr103643⟩
private theorem pr103651 : Nat.Prime 103651 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv691]) (by decide +kernel)
def pv103651 : PrimeValue := ⟨103651, pr103651⟩
private theorem pr103657 : Nat.Prime 103657 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv617]) (by decide +kernel)
def pv103657 : PrimeValue := ⟨103657, pr103657⟩
private theorem pr103669 : Nat.Prime 103669 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv53,pv163]) (by decide +kernel)
def pv103669 : PrimeValue := ⟨103669, pr103669⟩
private theorem pr103681 : Nat.Prime 103681 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv103681 : PrimeValue := ⟨103681, pr103681⟩
private theorem pr103687 : Nat.Prime 103687 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv1571]) (by decide +kernel)
def pv103687 : PrimeValue := ⟨103687, pr103687⟩
private theorem pr103699 : Nat.Prime 103699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv823]) (by decide +kernel)
def pv103699 : PrimeValue := ⟨103699, pr103699⟩
private theorem pr103703 : Nat.Prime 103703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv2729]) (by decide +kernel)
def pv103703 : PrimeValue := ⟨103703, pr103703⟩
private theorem pr103723 : Nat.Prime 103723 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv59,pv293]) (by decide +kernel)
def pv103723 : PrimeValue := ⟨103723, pr103723⟩
private theorem pr103769 : Nat.Prime 103769 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv17,pv109]) (by decide +kernel)
def pv103769 : PrimeValue := ⟨103769, pr103769⟩
private theorem pr103787 : Nat.Prime 103787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv51893]) (by decide +kernel)
def pv103787 : PrimeValue := ⟨103787, pr103787⟩
private theorem pr103801 : Nat.Prime 103801 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv173]) (by decide +kernel)
def pv103801 : PrimeValue := ⟨103801, pr103801⟩
private theorem pr103811 : Nat.Prime 103811 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv1483]) (by decide +kernel)
def pv103811 : PrimeValue := ⟨103811, pr103811⟩
private theorem pr103813 : Nat.Prime 103813 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv41,pv211]) (by decide +kernel)
def pv103813 : PrimeValue := ⟨103813, pr103813⟩
private theorem pr103837 : Nat.Prime 103837 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv509]) (by decide +kernel)
def pv103837 : PrimeValue := ⟨103837, pr103837⟩
private theorem pr103841 : Nat.Prime 103841 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv59]) (by decide +kernel)
def pv103841 : PrimeValue := ⟨103841, pr103841⟩
private theorem pr103843 : Nat.Prime 103843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv641]) (by decide +kernel)
def pv103843 : PrimeValue := ⟨103843, pr103843⟩
private theorem pr103867 : Nat.Prime 103867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv2473]) (by decide +kernel)
def pv103867 : PrimeValue := ⟨103867, pr103867⟩
private theorem pr103889 : Nat.Prime 103889 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv43,pv151]) (by decide +kernel)
def pv103889 : PrimeValue := ⟨103889, pr103889⟩
private theorem pr103903 : Nat.Prime 103903 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17317]) (by decide +kernel)
def pv103903 : PrimeValue := ⟨103903, pr103903⟩
private theorem pr103913 : Nat.Prime 103913 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv419]) (by decide +kernel)
def pv103913 : PrimeValue := ⟨103913, pr103913⟩
private theorem pr103919 : Nat.Prime 103919 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv223,pv233]) (by decide +kernel)
def pv103919 : PrimeValue := ⟨103919, pr103919⟩
private theorem pr103951 : Nat.Prime 103951 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv7,pv11]) (by decide +kernel)
def pv103951 : PrimeValue := ⟨103951, pr103951⟩
private theorem pr103963 : Nat.Prime 103963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17327]) (by decide +kernel)
def pv103963 : PrimeValue := ⟨103963, pr103963⟩
private theorem pr103967 : Nat.Prime 103967 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv227,pv229]) (by decide +kernel)
def pv103967 : PrimeValue := ⟨103967, pr103967⟩
private theorem pr103969 : Nat.Prime 103969 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv19]) (by decide +kernel)
def pv103969 : PrimeValue := ⟨103969, pr103969⟩
private theorem pr103979 : Nat.Prime 103979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv1061]) (by decide +kernel)
def pv103979 : PrimeValue := ⟨103979, pr103979⟩
private theorem pr103991 : Nat.Prime 103991 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv10399]) (by decide +kernel)
def pv103991 : PrimeValue := ⟨103991, pr103991⟩
private theorem pr103993 : Nat.Prime 103993 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv619]) (by decide +kernel)
def pv103993 : PrimeValue := ⟨103993, pr103993⟩
private theorem pr103997 : Nat.Prime 103997 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv25999]) (by decide +kernel)
def pv103997 : PrimeValue := ⟨103997, pr103997⟩
private theorem pr104003 : Nat.Prime 104003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv149,pv349]) (by decide +kernel)
def pv104003 : PrimeValue := ⟨104003, pr104003⟩
private theorem pr104009 : Nat.Prime 104009 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13001]) (by decide +kernel)
def pv104009 : PrimeValue := ⟨104009, pr104009⟩
private theorem pr104021 : Nat.Prime 104021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv743]) (by decide +kernel)
def pv104021 : PrimeValue := ⟨104021, pr104021⟩
private theorem pr104033 : Nat.Prime 104033 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3251]) (by decide +kernel)
def pv104033 : PrimeValue := ⟨104033, pr104033⟩
private theorem pr104047 : Nat.Prime 104047 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17341]) (by decide +kernel)
def pv104047 : PrimeValue := ⟨104047, pr104047⟩
private theorem pr104053 : Nat.Prime 104053 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv23,pv29]) (by decide +kernel)
def pv104053 : PrimeValue := ⟨104053, pr104053⟩
private theorem pr104059 : Nat.Prime 104059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv41,pv47]) (by decide +kernel)
def pv104059 : PrimeValue := ⟨104059, pr104059⟩
private theorem pr104087 : Nat.Prime 104087 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv71,pv733]) (by decide +kernel)
def pv104087 : PrimeValue := ⟨104087, pr104087⟩
private theorem pr104089 : Nat.Prime 104089 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv4337]) (by decide +kernel)
def pv104089 : PrimeValue := ⟨104089, pr104089⟩
private theorem pr104107 : Nat.Prime 104107 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17351]) (by decide +kernel)
def pv104107 : PrimeValue := ⟨104107, pr104107⟩
private theorem pr104119 : Nat.Prime 104119 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv37,pv67]) (by decide +kernel)
def pv104119 : PrimeValue := ⟨104119, pr104119⟩
private theorem pr104123 : Nat.Prime 104123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79,pv659]) (by decide +kernel)
def pv104123 : PrimeValue := ⟨104123, pr104123⟩
private theorem pr104147 : Nat.Prime 104147 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv43,pv173]) (by decide +kernel)
def pv104147 : PrimeValue := ⟨104147, pr104147⟩
private theorem pr104149 : Nat.Prime 104149 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv263]) (by decide +kernel)
def pv104149 : PrimeValue := ⟨104149, pr104149⟩
private theorem pr104161 : Nat.Prime 104161 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv7,pv31]) (by decide +kernel)
def pv104161 : PrimeValue := ⟨104161, pr104161⟩
private theorem pr104173 : Nat.Prime 104173 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv8681]) (by decide +kernel)
def pv104173 : PrimeValue := ⟨104173, pr104173⟩
private theorem pr104179 : Nat.Prime 104179 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv97,pv179]) (by decide +kernel)
def pv104179 : PrimeValue := ⟨104179, pr104179⟩
private theorem pr104183 : Nat.Prime 104183 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv4007]) (by decide +kernel)
def pv104183 : PrimeValue := ⟨104183, pr104183⟩
private theorem pr104207 : Nat.Prime 104207 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv52103]) (by decide +kernel)
def pv104207 : PrimeValue := ⟨104207, pr104207⟩
private theorem pr104231 : Nat.Prime 104231 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv1489]) (by decide +kernel)
def pv104231 : PrimeValue := ⟨104231, pr104231⟩
private theorem pr104233 : Nat.Prime 104233 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv43,pv101]) (by decide +kernel)
def pv104233 : PrimeValue := ⟨104233, pr104233⟩
private theorem pr104239 : Nat.Prime 104239 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5791]) (by decide +kernel)
def pv104239 : PrimeValue := ⟨104239, pr104239⟩
private theorem pr104243 : Nat.Prime 104243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv52121]) (by decide +kernel)
def pv104243 : PrimeValue := ⟨104243, pr104243⟩
private theorem pr104281 : Nat.Prime 104281 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv11,pv79]) (by decide +kernel)
def pv104281 : PrimeValue := ⟨104281, pr104281⟩
private theorem pr104287 : Nat.Prime 104287 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv191]) (by decide +kernel)
def pv104287 : PrimeValue := ⟨104287, pr104287⟩
private theorem pr104297 : Nat.Prime 104297 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13037]) (by decide +kernel)
def pv104297 : PrimeValue := ⟨104297, pr104297⟩
private theorem pr104309 : Nat.Prime 104309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv89,pv293]) (by decide +kernel)
def pv104309 : PrimeValue := ⟨104309, pr104309⟩
private theorem pr104311 : Nat.Prime 104311 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv19,pv61]) (by decide +kernel)
def pv104311 : PrimeValue := ⟨104311, pr104311⟩
private theorem pr104323 : Nat.Prime 104323 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17387]) (by decide +kernel)
def pv104323 : PrimeValue := ⟨104323, pr104323⟩
private theorem pr104327 : Nat.Prime 104327 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv52163]) (by decide +kernel)
def pv104327 : PrimeValue := ⟨104327, pr104327⟩
private theorem pr104347 : Nat.Prime 104347 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv11,pv17,pv31]) (by decide +kernel)
def pv104347 : PrimeValue := ⟨104347, pr104347⟩
private theorem pr104369 : Nat.Prime 104369 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv593]) (by decide +kernel)
def pv104369 : PrimeValue := ⟨104369, pr104369⟩
private theorem pr104381 : Nat.Prime 104381 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv307]) (by decide +kernel)
def pv104381 : PrimeValue := ⟨104381, pr104381⟩
private theorem pr104383 : Nat.Prime 104383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1933]) (by decide +kernel)
def pv104383 : PrimeValue := ⟨104383, pr104383⟩
private theorem pr104393 : Nat.Prime 104393 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13049]) (by decide +kernel)
def pv104393 : PrimeValue := ⟨104393, pr104393⟩
private theorem pr104399 : Nat.Prime 104399 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv7457]) (by decide +kernel)
def pv104399 : PrimeValue := ⟨104399, pr104399⟩
private theorem pr104417 : Nat.Prime 104417 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv13,pv251]) (by decide +kernel)
def pv104417 : PrimeValue := ⟨104417, pr104417⟩
private theorem pr104459 : Nat.Prime 104459 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv1801]) (by decide +kernel)
def pv104459 : PrimeValue := ⟨104459, pr104459⟩
private theorem pr104491 : Nat.Prime 104491 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv43]) (by decide +kernel)
def pv104491 : PrimeValue := ⟨104491, pr104491⟩
private theorem pr104513 : Nat.Prime 104513 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv71]) (by decide +kernel)
def pv104513 : PrimeValue := ⟨104513, pr104513⟩
private theorem pr104527 : Nat.Prime 104527 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5807]) (by decide +kernel)
def pv104527 : PrimeValue := ⟨104527, pr104527⟩
private theorem pr104551 : Nat.Prime 104551 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv17,pv41]) (by decide +kernel)
def pv104551 : PrimeValue := ⟨104551, pr104551⟩
private theorem pr104561 : Nat.Prime 104561 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv1307]) (by decide +kernel)
def pv104561 : PrimeValue := ⟨104561, pr104561⟩
private theorem pr104579 : Nat.Prime 104579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv52289]) (by decide +kernel)
def pv104579 : PrimeValue := ⟨104579, pr104579⟩
private theorem pr104593 : Nat.Prime 104593 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2179]) (by decide +kernel)
def pv104593 : PrimeValue := ⟨104593, pr104593⟩
private theorem pr104597 : Nat.Prime 104597 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79,pv331]) (by decide +kernel)
def pv104597 : PrimeValue := ⟨104597, pr104597⟩
private theorem pr104623 : Nat.Prime 104623 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv47,pv53]) (by decide +kernel)
def pv104623 : PrimeValue := ⟨104623, pr104623⟩
private theorem pr104639 : Nat.Prime 104639 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv113,pv463]) (by decide +kernel)
def pv104639 : PrimeValue := ⟨104639, pr104639⟩
private theorem pr104659 : Nat.Prime 104659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17443]) (by decide +kernel)
def pv104659 : PrimeValue := ⟨104659, pr104659⟩
private theorem pr104677 : Nat.Prime 104677 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv13,pv61]) (by decide +kernel)
def pv104677 : PrimeValue := ⟨104677, pr104677⟩
private theorem pr104681 : Nat.Prime 104681 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv2617]) (by decide +kernel)
def pv104681 : PrimeValue := ⟨104681, pr104681⟩
private theorem pr104683 : Nat.Prime 104683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv73,pv239]) (by decide +kernel)
def pv104683 : PrimeValue := ⟨104683, pr104683⟩
private theorem pr104693 : Nat.Prime 104693 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv3739]) (by decide +kernel)
def pv104693 : PrimeValue := ⟨104693, pr104693⟩
private theorem pr104701 : Nat.Prime 104701 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv349]) (by decide +kernel)
def pv104701 : PrimeValue := ⟨104701, pr104701⟩
private theorem pr104707 : Nat.Prime 104707 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv277]) (by decide +kernel)
def pv104707 : PrimeValue := ⟨104707, pr104707⟩
private theorem pr104711 : Nat.Prime 104711 :=
  checkPrime_prime (q := pv43) (ls := [pv2,pv5,pv37,pv283]) (by decide +kernel)
def pv104711 : PrimeValue := ⟨104711, pr104711⟩
private theorem pr104717 : Nat.Prime 104717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv557]) (by decide +kernel)
def pv104717 : PrimeValue := ⟨104717, pr104717⟩
private theorem pr104723 : Nat.Prime 104723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv52361]) (by decide +kernel)
def pv104723 : PrimeValue := ⟨104723, pr104723⟩
private theorem pr104729 : Nat.Prime 104729 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv13,pv19,pv53]) (by decide +kernel)
def pv104729 : PrimeValue := ⟨104729, pr104729⟩
private theorem pr104743 : Nat.Prime 104743 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv23]) (by decide +kernel)
def pv104743 : PrimeValue := ⟨104743, pr104743⟩
private theorem pr104759 : Nat.Prime 104759 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv52379]) (by decide +kernel)
def pv104759 : PrimeValue := ⟨104759, pr104759⟩
private theorem pr104761 : Nat.Prime 104761 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv97]) (by decide +kernel)
def pv104761 : PrimeValue := ⟨104761, pr104761⟩
private theorem pr104779 : Nat.Prime 104779 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5821]) (by decide +kernel)
def pv104779 : PrimeValue := ⟨104779, pr104779⟩
private theorem pr104789 : Nat.Prime 104789 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv23,pv67]) (by decide +kernel)
def pv104789 : PrimeValue := ⟨104789, pr104789⟩
private theorem pr104803 : Nat.Prime 104803 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17467]) (by decide +kernel)
def pv104803 : PrimeValue := ⟨104803, pr104803⟩
private theorem pr104827 : Nat.Prime 104827 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17471]) (by decide +kernel)
def pv104827 : PrimeValue := ⟨104827, pr104827⟩
private theorem pr104831 : Nat.Prime 104831 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv5,pv11,pv953]) (by decide +kernel)
def pv104831 : PrimeValue := ⟨104831, pr104831⟩
private theorem pr104849 : Nat.Prime 104849 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv6553]) (by decide +kernel)
def pv104849 : PrimeValue := ⟨104849, pr104849⟩
private theorem pr104869 : Nat.Prime 104869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv971]) (by decide +kernel)
def pv104869 : PrimeValue := ⟨104869, pr104869⟩
private theorem pr104879 : Nat.Prime 104879 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv41,pv1279]) (by decide +kernel)
def pv104879 : PrimeValue := ⟨104879, pr104879⟩
private theorem pr104891 : Nat.Prime 104891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv617]) (by decide +kernel)
def pv104891 : PrimeValue := ⟨104891, pr104891⟩
private theorem pr104911 : Nat.Prime 104911 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv13,pv269]) (by decide +kernel)
def pv104911 : PrimeValue := ⟨104911, pr104911⟩
private theorem pr104917 : Nat.Prime 104917 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv1249]) (by decide +kernel)
def pv104917 : PrimeValue := ⟨104917, pr104917⟩
private theorem pr104933 : Nat.Prime 104933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv709]) (by decide +kernel)
def pv104933 : PrimeValue := ⟨104933, pr104933⟩
private theorem pr104947 : Nat.Prime 104947 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17491]) (by decide +kernel)
def pv104947 : PrimeValue := ⟨104947, pr104947⟩
private theorem pr104953 : Nat.Prime 104953 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv4373]) (by decide +kernel)
def pv104953 : PrimeValue := ⟨104953, pr104953⟩
private theorem pr104959 : Nat.Prime 104959 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv17]) (by decide +kernel)
def pv104959 : PrimeValue := ⟨104959, pr104959⟩
private theorem pr104971 : Nat.Prime 104971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv3499]) (by decide +kernel)
def pv104971 : PrimeValue := ⟨104971, pr104971⟩
private theorem pr104987 : Nat.Prime 104987 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv7499]) (by decide +kernel)
def pv104987 : PrimeValue := ⟨104987, pr104987⟩
private theorem pr104999 : Nat.Prime 104999 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv47,pv1117]) (by decide +kernel)
def pv104999 : PrimeValue := ⟨104999, pr104999⟩
private theorem pr105019 : Nat.Prime 105019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv761]) (by decide +kernel)
def pv105019 : PrimeValue := ⟨105019, pr105019⟩
private theorem pr105023 : Nat.Prime 105023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv52511]) (by decide +kernel)
def pv105023 : PrimeValue := ⟨105023, pr105023⟩
private theorem pr105037 : Nat.Prime 105037 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv8753]) (by decide +kernel)
def pv105037 : PrimeValue := ⟨105037, pr105037⟩
private theorem pr105071 : Nat.Prime 105071 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv19,pv79]) (by decide +kernel)
def pv105071 : PrimeValue := ⟨105071, pr105071⟩
private theorem pr105097 : Nat.Prime 105097 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv29,pv151]) (by decide +kernel)
def pv105097 : PrimeValue := ⟨105097, pr105097⟩
private theorem pr105107 : Nat.Prime 105107 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv52553]) (by decide +kernel)
def pv105107 : PrimeValue := ⟨105107, pr105107⟩
private theorem pr105137 : Nat.Prime 105137 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv6571]) (by decide +kernel)
def pv105137 : PrimeValue := ⟨105137, pr105137⟩
private theorem pr105143 : Nat.Prime 105143 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv52571]) (by decide +kernel)
def pv105143 : PrimeValue := ⟨105143, pr105143⟩
private theorem pr105167 : Nat.Prime 105167 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv52583]) (by decide +kernel)
def pv105167 : PrimeValue := ⟨105167, pr105167⟩
private theorem pr105173 : Nat.Prime 105173 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv26293]) (by decide +kernel)
def pv105173 : PrimeValue := ⟨105173, pr105173⟩
private theorem pr105199 : Nat.Prime 105199 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv89,pv197]) (by decide +kernel)
def pv105199 : PrimeValue := ⟨105199, pr105199⟩
private theorem pr105211 : Nat.Prime 105211 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv167]) (by decide +kernel)
def pv105211 : PrimeValue := ⟨105211, pr105211⟩
private theorem pr105227 : Nat.Prime 105227 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv4783]) (by decide +kernel)
def pv105227 : PrimeValue := ⟨105227, pr105227⟩
private theorem pr105229 : Nat.Prime 105229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv79]) (by decide +kernel)
def pv105229 : PrimeValue := ⟨105229, pr105229⟩
private theorem pr105239 : Nat.Prime 105239 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv7,pv7517]) (by decide +kernel)
def pv105239 : PrimeValue := ⟨105239, pr105239⟩
private theorem pr105251 : Nat.Prime 105251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv421]) (by decide +kernel)
def pv105251 : PrimeValue := ⟨105251, pr105251⟩
private theorem pr105253 : Nat.Prime 105253 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv179]) (by decide +kernel)
def pv105253 : PrimeValue := ⟨105253, pr105253⟩
private theorem pr105263 : Nat.Prime 105263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv52631]) (by decide +kernel)
def pv105263 : PrimeValue := ⟨105263, pr105263⟩
private theorem pr105269 : Nat.Prime 105269 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv26317]) (by decide +kernel)
def pv105269 : PrimeValue := ⟨105269, pr105269⟩
private theorem pr105277 : Nat.Prime 105277 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv31,pv283]) (by decide +kernel)
def pv105277 : PrimeValue := ⟨105277, pr105277⟩
private theorem pr105319 : Nat.Prime 105319 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5851]) (by decide +kernel)
def pv105319 : PrimeValue := ⟨105319, pr105319⟩
private theorem pr105323 : Nat.Prime 105323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv7523]) (by decide +kernel)
def pv105323 : PrimeValue := ⟨105323, pr105323⟩
private theorem pr105331 : Nat.Prime 105331 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv3511]) (by decide +kernel)
def pv105331 : PrimeValue := ⟨105331, pr105331⟩
private theorem pr105337 : Nat.Prime 105337 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv11,pv19]) (by decide +kernel)
def pv105337 : PrimeValue := ⟨105337, pr105337⟩
private theorem pr105341 : Nat.Prime 105341 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23,pv229]) (by decide +kernel)
def pv105341 : PrimeValue := ⟨105341, pr105341⟩
private theorem pr105359 : Nat.Prime 105359 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv4789]) (by decide +kernel)
def pv105359 : PrimeValue := ⟨105359, pr105359⟩
private theorem pr105361 : Nat.Prime 105361 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv439]) (by decide +kernel)
def pv105361 : PrimeValue := ⟨105361, pr105361⟩
private theorem pr105367 : Nat.Prime 105367 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv1033]) (by decide +kernel)
def pv105367 : PrimeValue := ⟨105367, pr105367⟩
private theorem pr105373 : Nat.Prime 105373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2927]) (by decide +kernel)
def pv105373 : PrimeValue := ⟨105373, pr105373⟩
private theorem pr105379 : Nat.Prime 105379 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv193]) (by decide +kernel)
def pv105379 : PrimeValue := ⟨105379, pr105379⟩
private theorem pr105389 : Nat.Prime 105389 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv26347]) (by decide +kernel)
def pv105389 : PrimeValue := ⟨105389, pr105389⟩
private theorem pr105397 : Nat.Prime 105397 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv8783]) (by decide +kernel)
def pv105397 : PrimeValue := ⟨105397, pr105397⟩
private theorem pr105401 : Nat.Prime 105401 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17,pv31]) (by decide +kernel)
def pv105401 : PrimeValue := ⟨105401, pr105401⟩
private theorem pr105407 : Nat.Prime 105407 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv7529]) (by decide +kernel)
def pv105407 : PrimeValue := ⟨105407, pr105407⟩
private theorem pr105437 : Nat.Prime 105437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv613]) (by decide +kernel)
def pv105437 : PrimeValue := ⟨105437, pr105437⟩
private theorem pr105449 : Nat.Prime 105449 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv7,pv269]) (by decide +kernel)
def pv105449 : PrimeValue := ⟨105449, pr105449⟩
private theorem pr105467 : Nat.Prime 105467 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv52733]) (by decide +kernel)
def pv105467 : PrimeValue := ⟨105467, pr105467⟩
private theorem pr105499 : Nat.Prime 105499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5861]) (by decide +kernel)
def pv105499 : PrimeValue := ⟨105499, pr105499⟩
private theorem pr105503 : Nat.Prime 105503 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv17,pv29,pv107]) (by decide +kernel)
def pv105503 : PrimeValue := ⟨105503, pr105503⟩
private theorem pr105509 : Nat.Prime 105509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv2029]) (by decide +kernel)
def pv105509 : PrimeValue := ⟨105509, pr105509⟩
private theorem pr105517 : Nat.Prime 105517 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv977]) (by decide +kernel)
def pv105517 : PrimeValue := ⟨105517, pr105517⟩
private theorem pr105527 : Nat.Prime 105527 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv2777]) (by decide +kernel)
def pv105527 : PrimeValue := ⟨105527, pr105527⟩
private theorem pr105529 : Nat.Prime 105529 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv4397]) (by decide +kernel)
def pv105529 : PrimeValue := ⟨105529, pr105529⟩
private theorem pr105533 : Nat.Prime 105533 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv3769]) (by decide +kernel)
def pv105533 : PrimeValue := ⟨105533, pr105533⟩
private theorem pr105541 : Nat.Prime 105541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1759]) (by decide +kernel)
def pv105541 : PrimeValue := ⟨105541, pr105541⟩
private theorem pr105557 : Nat.Prime 105557 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv2399]) (by decide +kernel)
def pv105557 : PrimeValue := ⟨105557, pr105557⟩
private theorem pr105563 : Nat.Prime 105563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv1123]) (by decide +kernel)
def pv105563 : PrimeValue := ⟨105563, pr105563⟩
private theorem pr105601 : Nat.Prime 105601 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv105601 : PrimeValue := ⟨105601, pr105601⟩
private theorem pr105607 : Nat.Prime 105607 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5867]) (by decide +kernel)
def pv105607 : PrimeValue := ⟨105607, pr105607⟩
private theorem pr105613 : Nat.Prime 105613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv677]) (by decide +kernel)
def pv105613 : PrimeValue := ⟨105613, pr105613⟩
private theorem pr105619 : Nat.Prime 105619 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29,pv607]) (by decide +kernel)
def pv105619 : PrimeValue := ⟨105619, pr105619⟩
private theorem pr105649 : Nat.Prime 105649 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv31,pv71]) (by decide +kernel)
def pv105649 : PrimeValue := ⟨105649, pr105649⟩
private theorem pr105653 : Nat.Prime 105653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv433]) (by decide +kernel)
def pv105653 : PrimeValue := ⟨105653, pr105653⟩
private theorem pr105667 : Nat.Prime 105667 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv1601]) (by decide +kernel)
def pv105667 : PrimeValue := ⟨105667, pr105667⟩
private theorem pr105673 : Nat.Prime 105673 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv17,pv37]) (by decide +kernel)
def pv105673 : PrimeValue := ⟨105673, pr105673⟩
private theorem pr105683 : Nat.Prime 105683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53,pv997]) (by decide +kernel)
def pv105683 : PrimeValue := ⟨105683, pr105683⟩
private theorem pr105691 : Nat.Prime 105691 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv271]) (by decide +kernel)
def pv105691 : PrimeValue := ⟨105691, pr105691⟩
private theorem pr105701 : Nat.Prime 105701 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv151]) (by decide +kernel)
def pv105701 : PrimeValue := ⟨105701, pr105701⟩
private theorem pr105727 : Nat.Prime 105727 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv67,pv263]) (by decide +kernel)
def pv105727 : PrimeValue := ⟨105727, pr105727⟩
private theorem pr105733 : Nat.Prime 105733 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv89]) (by decide +kernel)
def pv105733 : PrimeValue := ⟨105733, pr105733⟩
private theorem pr105751 : Nat.Prime 105751 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv47]) (by decide +kernel)
def pv105751 : PrimeValue := ⟨105751, pr105751⟩
private theorem pr105761 : Nat.Prime 105761 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv661]) (by decide +kernel)
def pv105761 : PrimeValue := ⟨105761, pr105761⟩
private theorem pr105767 : Nat.Prime 105767 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv52883]) (by decide +kernel)
def pv105767 : PrimeValue := ⟨105767, pr105767⟩
private theorem pr105769 : Nat.Prime 105769 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv113]) (by decide +kernel)
def pv105769 : PrimeValue := ⟨105769, pr105769⟩
private theorem pr105817 : Nat.Prime 105817 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv4409]) (by decide +kernel)
def pv105817 : PrimeValue := ⟨105817, pr105817⟩
private theorem pr105863 : Nat.Prime 105863 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv41,pv1291]) (by decide +kernel)
def pv105863 : PrimeValue := ⟨105863, pr105863⟩
private theorem pr105871 : Nat.Prime 105871 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv3529]) (by decide +kernel)
def pv105871 : PrimeValue := ⟨105871, pr105871⟩
private theorem pr105883 : Nat.Prime 105883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv2521]) (by decide +kernel)
def pv105883 : PrimeValue := ⟨105883, pr105883⟩
private theorem pr105899 : Nat.Prime 105899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv4073]) (by decide +kernel)
def pv105899 : PrimeValue := ⟨105899, pr105899⟩
private theorem pr105907 : Nat.Prime 105907 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv929]) (by decide +kernel)
def pv105907 : PrimeValue := ⟨105907, pr105907⟩
private theorem pr105913 : Nat.Prime 105913 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv1471]) (by decide +kernel)
def pv105913 : PrimeValue := ⟨105913, pr105913⟩
private theorem pr105929 : Nat.Prime 105929 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13241]) (by decide +kernel)
def pv105929 : PrimeValue := ⟨105929, pr105929⟩
private theorem pr105943 : Nat.Prime 105943 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17657]) (by decide +kernel)
def pv105943 : PrimeValue := ⟨105943, pr105943⟩
private theorem pr105953 : Nat.Prime 105953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv11,pv43]) (by decide +kernel)
def pv105953 : PrimeValue := ⟨105953, pr105953⟩
private theorem pr105967 : Nat.Prime 105967 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv29]) (by decide +kernel)
def pv105967 : PrimeValue := ⟨105967, pr105967⟩
private theorem pr105971 : Nat.Prime 105971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv10597]) (by decide +kernel)
def pv105971 : PrimeValue := ⟨105971, pr105971⟩
private theorem pr105977 : Nat.Prime 105977 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv1019]) (by decide +kernel)
def pv105977 : PrimeValue := ⟨105977, pr105977⟩
private theorem pr105983 : Nat.Prime 105983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv2789]) (by decide +kernel)
def pv105983 : PrimeValue := ⟨105983, pr105983⟩
private theorem pr105997 : Nat.Prime 105997 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv73]) (by decide +kernel)
def pv105997 : PrimeValue := ⟨105997, pr105997⟩
private theorem pr106013 : Nat.Prime 106013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv1559]) (by decide +kernel)
def pv106013 : PrimeValue := ⟨106013, pr106013⟩
private theorem pr106019 : Nat.Prime 106019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv61,pv79]) (by decide +kernel)
def pv106019 : PrimeValue := ⟨106019, pr106019⟩
private theorem pr106031 : Nat.Prime 106031 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv23,pv461]) (by decide +kernel)
def pv106031 : PrimeValue := ⟨106031, pr106031⟩
private theorem pr106033 : Nat.Prime 106033 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv47]) (by decide +kernel)
def pv106033 : PrimeValue := ⟨106033, pr106033⟩
private theorem pr106087 : Nat.Prime 106087 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17681]) (by decide +kernel)
def pv106087 : PrimeValue := ⟨106087, pr106087⟩
private theorem pr106103 : Nat.Prime 106103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv53051]) (by decide +kernel)
def pv106103 : PrimeValue := ⟨106103, pr106103⟩
private theorem pr106109 : Nat.Prime 106109 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv647]) (by decide +kernel)
def pv106109 : PrimeValue := ⟨106109, pr106109⟩
private theorem pr106121 : Nat.Prime 106121 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv379]) (by decide +kernel)
def pv106121 : PrimeValue := ⟨106121, pr106121⟩
private theorem pr106123 : Nat.Prime 106123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv769]) (by decide +kernel)
def pv106123 : PrimeValue := ⟨106123, pr106123⟩
private theorem pr106129 : Nat.Prime 106129 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv11,pv67]) (by decide +kernel)
def pv106129 : PrimeValue := ⟨106129, pr106129⟩
private theorem pr106163 : Nat.Prime 106163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv7583]) (by decide +kernel)
def pv106163 : PrimeValue := ⟨106163, pr106163⟩
private theorem pr106187 : Nat.Prime 106187 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53093]) (by decide +kernel)
def pv106187 : PrimeValue := ⟨106187, pr106187⟩
private theorem pr106189 : Nat.Prime 106189 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv8849]) (by decide +kernel)
def pv106189 : PrimeValue := ⟨106189, pr106189⟩
private theorem pr106207 : Nat.Prime 106207 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv31,pv571]) (by decide +kernel)
def pv106207 : PrimeValue := ⟨106207, pr106207⟩
private theorem pr106213 : Nat.Prime 106213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv53,pv167]) (by decide +kernel)
def pv106213 : PrimeValue := ⟨106213, pr106213⟩
private theorem pr106219 : Nat.Prime 106219 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv281]) (by decide +kernel)
def pv106219 : PrimeValue := ⟨106219, pr106219⟩
private theorem pr106243 : Nat.Prime 106243 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17707]) (by decide +kernel)
def pv106243 : PrimeValue := ⟨106243, pr106243⟩
private theorem pr106261 : Nat.Prime 106261 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv11,pv23]) (by decide +kernel)
def pv106261 : PrimeValue := ⟨106261, pr106261⟩
private theorem pr106273 : Nat.Prime 106273 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv41]) (by decide +kernel)
def pv106273 : PrimeValue := ⟨106273, pr106273⟩
private theorem pr106277 : Nat.Prime 106277 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv163]) (by decide +kernel)
def pv106277 : PrimeValue := ⟨106277, pr106277⟩
private theorem pr106279 : Nat.Prime 106279 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17713]) (by decide +kernel)
def pv106279 : PrimeValue := ⟨106279, pr106279⟩
private theorem pr106291 : Nat.Prime 106291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1181]) (by decide +kernel)
def pv106291 : PrimeValue := ⟨106291, pr106291⟩
private theorem pr106297 : Nat.Prime 106297 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv43,pv103]) (by decide +kernel)
def pv106297 : PrimeValue := ⟨106297, pr106297⟩
private theorem pr106303 : Nat.Prime 106303 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv2531]) (by decide +kernel)
def pv106303 : PrimeValue := ⟨106303, pr106303⟩
private theorem pr106307 : Nat.Prime 106307 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv2311]) (by decide +kernel)
def pv106307 : PrimeValue := ⟨106307, pr106307⟩
private theorem pr106319 : Nat.Prime 106319 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv17,pv53,pv59]) (by decide +kernel)
def pv106319 : PrimeValue := ⟨106319, pr106319⟩
private theorem pr106321 : Nat.Prime 106321 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv443]) (by decide +kernel)
def pv106321 : PrimeValue := ⟨106321, pr106321⟩
private theorem pr106331 : Nat.Prime 106331 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv31]) (by decide +kernel)
def pv106331 : PrimeValue := ⟨106331, pr106331⟩
private theorem pr106357 : Nat.Prime 106357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv8863]) (by decide +kernel)
def pv106357 : PrimeValue := ⟨106357, pr106357⟩
private theorem pr106363 : Nat.Prime 106363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv311]) (by decide +kernel)
def pv106363 : PrimeValue := ⟨106363, pr106363⟩
private theorem pr106367 : Nat.Prime 106367 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv4091]) (by decide +kernel)
def pv106367 : PrimeValue := ⟨106367, pr106367⟩
private theorem pr106373 : Nat.Prime 106373 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv29,pv131]) (by decide +kernel)
def pv106373 : PrimeValue := ⟨106373, pr106373⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
