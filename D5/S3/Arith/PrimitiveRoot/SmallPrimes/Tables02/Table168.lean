/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table168
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table168.pv246151
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table008
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table010
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table011
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table017
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table045
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table046

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr246151 : Nat.Prime 246151 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv547]) (by decide +kernel)
def pv246151 : PrimeValue := ⟨246151, pr246151⟩
private theorem pr246167 : Nat.Prime 246167 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv123083]) (by decide +kernel)
def pv246167 : PrimeValue := ⟨246167, pr246167⟩
private theorem pr246247 : Nat.Prime 246247 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv13,pv41]) (by decide +kernel)
def pv246247 : PrimeValue := ⟨246247, pr246247⟩
private theorem pr246439 : Nat.Prime 246439 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13691]) (by decide +kernel)
def pv246439 : PrimeValue := ⟨246439, pr246439⟩
private theorem pr246509 : Nat.Prime 246509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61627]) (by decide +kernel)
def pv246509 : PrimeValue := ⟨246509, pr246509⟩
private theorem pr246539 : Nat.Prime 246539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv123269]) (by decide +kernel)
def pv246539 : PrimeValue := ⟨246539, pr246539⟩
private theorem pr246577 : Nat.Prime 246577 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv467]) (by decide +kernel)
def pv246577 : PrimeValue := ⟨246577, pr246577⟩
private theorem pr246661 : Nat.Prime 246661 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv4111]) (by decide +kernel)
def pv246661 : PrimeValue := ⟨246661, pr246661⟩
private theorem pr246773 : Nat.Prime 246773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv19,pv191]) (by decide +kernel)
def pv246773 : PrimeValue := ⟨246773, pr246773⟩
private theorem pr246947 : Nat.Prime 246947 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv31,pv569]) (by decide +kernel)
def pv246947 : PrimeValue := ⟨246947, pr246947⟩
private theorem pr246971 : Nat.Prime 246971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv24697]) (by decide +kernel)
def pv246971 : PrimeValue := ⟨246971, pr246971⟩
private theorem pr247087 : Nat.Prime 247087 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv37,pv53]) (by decide +kernel)
def pv247087 : PrimeValue := ⟨247087, pr247087⟩
private theorem pr247201 : Nat.Prime 247201 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv103]) (by decide +kernel)
def pv247201 : PrimeValue := ⟨247201, pr247201⟩
private theorem pr247433 : Nat.Prime 247433 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv157,pv197]) (by decide +kernel)
def pv247433 : PrimeValue := ⟨247433, pr247433⟩
private theorem pr247439 : Nat.Prime 247439 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv123719]) (by decide +kernel)
def pv247439 : PrimeValue := ⟨247439, pr247439⟩
private theorem pr247531 : Nat.Prime 247531 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv37,pv223]) (by decide +kernel)
def pv247531 : PrimeValue := ⟨247531, pr247531⟩
private theorem pr247649 : Nat.Prime 247649 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv71,pv109]) (by decide +kernel)
def pv247649 : PrimeValue := ⟨247649, pr247649⟩
private theorem pr247739 : Nat.Prime 247739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv97,pv1277]) (by decide +kernel)
def pv247739 : PrimeValue := ⟨247739, pr247739⟩
private theorem pr247799 : Nat.Prime 247799 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv19,pv6521]) (by decide +kernel)
def pv247799 : PrimeValue := ⟨247799, pr247799⟩
private theorem pr247879 : Nat.Prime 247879 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv47,pv293]) (by decide +kernel)
def pv247879 : PrimeValue := ⟨247879, pr247879⟩
private theorem pr247901 : Nat.Prime 247901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv37,pv67]) (by decide +kernel)
def pv247901 : PrimeValue := ⟨247901, pr247901⟩
private theorem pr248117 : Nat.Prime 248117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv5639]) (by decide +kernel)
def pv248117 : PrimeValue := ⟨248117, pr248117⟩
private theorem pr248257 : Nat.Prime 248257 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv431]) (by decide +kernel)
def pv248257 : PrimeValue := ⟨248257, pr248257⟩
private theorem pr248609 : Nat.Prime 248609 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv457]) (by decide +kernel)
def pv248609 : PrimeValue := ⟨248609, pr248609⟩
private theorem pr248641 : Nat.Prime 248641 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv3,pv5,pv7,pv37]) (by decide +kernel)
def pv248641 : PrimeValue := ⟨248641, pr248641⟩
private theorem pr248821 : Nat.Prime 248821 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv11,pv13,pv29]) (by decide +kernel)
def pv248821 : PrimeValue := ⟨248821, pr248821⟩
private theorem pr248851 : Nat.Prime 248851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv79]) (by decide +kernel)
def pv248851 : PrimeValue := ⟨248851, pr248851⟩
private theorem pr248867 : Nat.Prime 248867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv124433]) (by decide +kernel)
def pv248867 : PrimeValue := ⟨248867, pr248867⟩
private theorem pr248891 : Nat.Prime 248891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv24889]) (by decide +kernel)
def pv248891 : PrimeValue := ⟨248891, pr248891⟩
private theorem pr248909 : Nat.Prime 248909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv5657]) (by decide +kernel)
def pv248909 : PrimeValue := ⟨248909, pr248909⟩
private theorem pr248971 : Nat.Prime 248971 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv43,pv193]) (by decide +kernel)
def pv248971 : PrimeValue := ⟨248971, pr248971⟩
private theorem pr248987 : Nat.Prime 248987 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv124493]) (by decide +kernel)
def pv248987 : PrimeValue := ⟨248987, pr248987⟩
private theorem pr249127 : Nat.Prime 249127 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv41521]) (by decide +kernel)
def pv249127 : PrimeValue := ⟨249127, pr249127⟩
private theorem pr249181 : Nat.Prime 249181 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv4153]) (by decide +kernel)
def pv249181 : PrimeValue := ⟨249181, pr249181⟩
private theorem pr249217 : Nat.Prime 249217 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv59]) (by decide +kernel)
def pv249217 : PrimeValue := ⟨249217, pr249217⟩
private theorem pr249329 : Nat.Prime 249329 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv15583]) (by decide +kernel)
def pv249329 : PrimeValue := ⟨249329, pr249329⟩
private theorem pr249421 : Nat.Prime 249421 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv4157]) (by decide +kernel)
def pv249421 : PrimeValue := ⟨249421, pr249421⟩
private theorem pr249433 : Nat.Prime 249433 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv547]) (by decide +kernel)
def pv249433 : PrimeValue := ⟨249433, pr249433⟩
private theorem pr249437 : Nat.Prime 249437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv5669]) (by decide +kernel)
def pv249437 : PrimeValue := ⟨249437, pr249437⟩
private theorem pr249449 : Nat.Prime 249449 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31181]) (by decide +kernel)
def pv249449 : PrimeValue := ⟨249449, pr249449⟩
private theorem pr249589 : Nat.Prime 249589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2311]) (by decide +kernel)
def pv249589 : PrimeValue := ⟨249589, pr249589⟩
private theorem pr249593 : Nat.Prime 249593 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv4457]) (by decide +kernel)
def pv249593 : PrimeValue := ⟨249593, pr249593⟩
private theorem pr249647 : Nat.Prime 249647 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv124823]) (by decide +kernel)
def pv249647 : PrimeValue := ⟨249647, pr249647⟩
private theorem pr249749 : Nat.Prime 249749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv2153]) (by decide +kernel)
def pv249749 : PrimeValue := ⟨249749, pr249749⟩
private theorem pr249797 : Nat.Prime 249797 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv197,pv317]) (by decide +kernel)
def pv249797 : PrimeValue := ⟨249797, pr249797⟩
private theorem pr249811 : Nat.Prime 249811 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv757]) (by decide +kernel)
def pv249811 : PrimeValue := ⟨249811, pr249811⟩
private theorem pr249853 : Nat.Prime 249853 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv47,pv443]) (by decide +kernel)
def pv249853 : PrimeValue := ⟨249853, pr249853⟩
private theorem pr249857 : Nat.Prime 249857 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv61]) (by decide +kernel)
def pv249857 : PrimeValue := ⟨249857, pr249857⟩
private theorem pr250013 : Nat.Prime 250013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv8929]) (by decide +kernel)
def pv250013 : PrimeValue := ⟨250013, pr250013⟩
private theorem pr250037 : Nat.Prime 250037 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv3677]) (by decide +kernel)
def pv250037 : PrimeValue := ⟨250037, pr250037⟩
private theorem pr250057 : Nat.Prime 250057 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv23,pv151]) (by decide +kernel)
def pv250057 : PrimeValue := ⟨250057, pr250057⟩
private theorem pr250109 : Nat.Prime 250109 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv2017]) (by decide +kernel)
def pv250109 : PrimeValue := ⟨250109, pr250109⟩
private theorem pr250499 : Nat.Prime 250499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv251,pv499]) (by decide +kernel)
def pv250499 : PrimeValue := ⟨250499, pr250499⟩
private theorem pr250727 : Nat.Prime 250727 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv17909]) (by decide +kernel)
def pv250727 : PrimeValue := ⟨250727, pr250727⟩
private theorem pr250793 : Nat.Prime 250793 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv29,pv47]) (by decide +kernel)
def pv250793 : PrimeValue := ⟨250793, pr250793⟩
private theorem pr250951 : Nat.Prime 250951 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv239]) (by decide +kernel)
def pv250951 : PrimeValue := ⟨250951, pr250951⟩
private theorem pr251057 : Nat.Prime 251057 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv17,pv71]) (by decide +kernel)
def pv251057 : PrimeValue := ⟨251057, pr251057⟩
private theorem pr251117 : Nat.Prime 251117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv67,pv937]) (by decide +kernel)
def pv251117 : PrimeValue := ⟨251117, pr251117⟩
private theorem pr251171 : Nat.Prime 251171 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv25117]) (by decide +kernel)
def pv251171 : PrimeValue := ⟨251171, pr251171⟩
private theorem pr251287 : Nat.Prime 251287 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv31,pv193]) (by decide +kernel)
def pv251287 : PrimeValue := ⟨251287, pr251287⟩
private theorem pr251429 : Nat.Prime 251429 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv239,pv263]) (by decide +kernel)
def pv251429 : PrimeValue := ⟨251429, pr251429⟩
private theorem pr251513 : Nat.Prime 251513 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv149,pv211]) (by decide +kernel)
def pv251513 : PrimeValue := ⟨251513, pr251513⟩
private theorem pr251567 : Nat.Prime 251567 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv17,pv151]) (by decide +kernel)
def pv251567 : PrimeValue := ⟨251567, pr251567⟩
private theorem pr251843 : Nat.Prime 251843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv125921]) (by decide +kernel)
def pv251843 : PrimeValue := ⟨251843, pr251843⟩
private theorem pr252253 : Nat.Prime 252253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv13]) (by decide +kernel)
def pv252253 : PrimeValue := ⟨252253, pr252253⟩
private theorem pr252277 : Nat.Prime 252277 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv21023]) (by decide +kernel)
def pv252277 : PrimeValue := ⟨252277, pr252277⟩
private theorem pr252293 : Nat.Prime 252293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv63073]) (by decide +kernel)
def pv252293 : PrimeValue := ⟨252293, pr252293⟩
private theorem pr252319 : Nat.Prime 252319 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv3823]) (by decide +kernel)
def pv252319 : PrimeValue := ⟨252319, pr252319⟩
private theorem pr252323 : Nat.Prime 252323 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv67,pv269]) (by decide +kernel)
def pv252323 : PrimeValue := ⟨252323, pr252323⟩
private theorem pr252391 : Nat.Prime 252391 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv47,pv179]) (by decide +kernel)
def pv252391 : PrimeValue := ⟨252391, pr252391⟩
private theorem pr252419 : Nat.Prime 252419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv2069]) (by decide +kernel)
def pv252419 : PrimeValue := ⟨252419, pr252419⟩
private theorem pr252449 : Nat.Prime 252449 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv23]) (by decide +kernel)
def pv252449 : PrimeValue := ⟨252449, pr252449⟩
private theorem pr252509 : Nat.Prime 252509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv63127]) (by decide +kernel)
def pv252509 : PrimeValue := ⟨252509, pr252509⟩
private theorem pr252667 : Nat.Prime 252667 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv4679]) (by decide +kernel)
def pv252667 : PrimeValue := ⟨252667, pr252667⟩
private theorem pr252869 : Nat.Prime 252869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv821]) (by decide +kernel)
def pv252869 : PrimeValue := ⟨252869, pr252869⟩
private theorem pr252893 : Nat.Prime 252893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv3719]) (by decide +kernel)
def pv252893 : PrimeValue := ⟨252893, pr252893⟩
private theorem pr252899 : Nat.Prime 252899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv4079]) (by decide +kernel)
def pv252899 : PrimeValue := ⟨252899, pr252899⟩
private theorem pr253867 : Nat.Prime 253867 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29,pv1459]) (by decide +kernel)
def pv253867 : PrimeValue := ⟨253867, pr253867⟩
private theorem pr253993 : Nat.Prime 253993 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv19,pv557]) (by decide +kernel)
def pv253993 : PrimeValue := ⟨253993, pr253993⟩
private theorem pr254027 : Nat.Prime 254027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv157,pv809]) (by decide +kernel)
def pv254027 : PrimeValue := ⟨254027, pr254027⟩
private theorem pr254071 : Nat.Prime 254071 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv941]) (by decide +kernel)
def pv254071 : PrimeValue := ⟨254071, pr254071⟩
private theorem pr254147 : Nat.Prime 254147 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv83,pv1531]) (by decide +kernel)
def pv254147 : PrimeValue := ⟨254147, pr254147⟩
private theorem pr254161 : Nat.Prime 254161 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv353]) (by decide +kernel)
def pv254161 : PrimeValue := ⟨254161, pr254161⟩
private theorem pr254213 : Nat.Prime 254213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv1297]) (by decide +kernel)
def pv254213 : PrimeValue := ⟨254213, pr254213⟩
private theorem pr254281 : Nat.Prime 254281 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv13,pv163]) (by decide +kernel)
def pv254281 : PrimeValue := ⟨254281, pr254281⟩
private theorem pr254299 : Nat.Prime 254299 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv3853]) (by decide +kernel)
def pv254299 : PrimeValue := ⟨254299, pr254299⟩
private theorem pr254369 : Nat.Prime 254369 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7949]) (by decide +kernel)
def pv254369 : PrimeValue := ⟨254369, pr254369⟩
private theorem pr254407 : Nat.Prime 254407 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv109,pv389]) (by decide +kernel)
def pv254407 : PrimeValue := ⟨254407, pr254407⟩
private theorem pr254447 : Nat.Prime 254447 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv29,pv41,pv107]) (by decide +kernel)
def pv254447 : PrimeValue := ⟨254447, pr254447⟩
private theorem pr254461 : Nat.Prime 254461 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv4241]) (by decide +kernel)
def pv254461 : PrimeValue := ⟨254461, pr254461⟩
private theorem pr254489 : Nat.Prime 254489 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv2447]) (by decide +kernel)
def pv254489 : PrimeValue := ⟨254489, pr254489⟩
private theorem pr254537 : Nat.Prime 254537 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31817]) (by decide +kernel)
def pv254537 : PrimeValue := ⟨254537, pr254537⟩
private theorem pr254647 : Nat.Prime 254647 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv43,pv47]) (by decide +kernel)
def pv254647 : PrimeValue := ⟨254647, pr254647⟩
private theorem pr254729 : Nat.Prime 254729 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv1873]) (by decide +kernel)
def pv254729 : PrimeValue := ⟨254729, pr254729⟩
private theorem pr254869 : Nat.Prime 254869 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv67,pv317]) (by decide +kernel)
def pv254869 : PrimeValue := ⟨254869, pr254869⟩
private theorem pr254879 : Nat.Prime 254879 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv13,pv9803]) (by decide +kernel)
def pv254879 : PrimeValue := ⟨254879, pr254879⟩
private theorem pr254963 : Nat.Prime 254963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv127481]) (by decide +kernel)
def pv254963 : PrimeValue := ⟨254963, pr254963⟩
private theorem pr254971 : Nat.Prime 254971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv2833]) (by decide +kernel)
def pv254971 : PrimeValue := ⟨254971, pr254971⟩
private theorem pr255077 : Nat.Prime 255077 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv1483]) (by decide +kernel)
def pv255077 : PrimeValue := ⟨255077, pr255077⟩
private theorem pr255259 : Nat.Prime 255259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv163]) (by decide +kernel)
def pv255259 : PrimeValue := ⟨255259, pr255259⟩
private theorem pr255419 : Nat.Prime 255419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv127709]) (by decide +kernel)
def pv255419 : PrimeValue := ⟨255419, pr255419⟩
private theorem pr255637 : Nat.Prime 255637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv263]) (by decide +kernel)
def pv255637 : PrimeValue := ⟨255637, pr255637⟩
private theorem pr255667 : Nat.Prime 255667 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv42611]) (by decide +kernel)
def pv255667 : PrimeValue := ⟨255667, pr255667⟩
private theorem pr255757 : Nat.Prime 255757 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv21313]) (by decide +kernel)
def pv255757 : PrimeValue := ⟨255757, pr255757⟩
private theorem pr255877 : Nat.Prime 255877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv21323]) (by decide +kernel)
def pv255877 : PrimeValue := ⟨255877, pr255877⟩
private theorem pr255977 : Nat.Prime 255977 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv653]) (by decide +kernel)
def pv255977 : PrimeValue := ⟨255977, pr255977⟩
private theorem pr256117 : Nat.Prime 256117 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv3049]) (by decide +kernel)
def pv256117 : PrimeValue := ⟨256117, pr256117⟩
private theorem pr256163 : Nat.Prime 256163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv263,pv487]) (by decide +kernel)
def pv256163 : PrimeValue := ⟨256163, pr256163⟩
private theorem pr256187 : Nat.Prime 256187 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv29,pv631]) (by decide +kernel)
def pv256187 : PrimeValue := ⟨256187, pr256187⟩
private theorem pr256279 : Nat.Prime 256279 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv353]) (by decide +kernel)
def pv256279 : PrimeValue := ⟨256279, pr256279⟩
private theorem pr256313 : Nat.Prime 256313 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv23,pv199]) (by decide +kernel)
def pv256313 : PrimeValue := ⟨256313, pr256313⟩
private theorem pr256393 : Nat.Prime 256393 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv1187]) (by decide +kernel)
def pv256393 : PrimeValue := ⟨256393, pr256393⟩
private theorem pr256469 : Nat.Prime 256469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv97,pv661]) (by decide +kernel)
def pv256469 : PrimeValue := ⟨256469, pr256469⟩
private theorem pr256831 : Nat.Prime 256831 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv1223]) (by decide +kernel)
def pv256831 : PrimeValue := ⟨256831, pr256831⟩
private theorem pr257161 : Nat.Prime 257161 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv2143]) (by decide +kernel)
def pv257161 : PrimeValue := ⟨257161, pr257161⟩
private theorem pr257263 : Nat.Prime 257263 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv53,pv809]) (by decide +kernel)
def pv257263 : PrimeValue := ⟨257263, pr257263⟩
private theorem pr257399 : Nat.Prime 257399 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv41,pv43,pv73]) (by decide +kernel)
def pv257399 : PrimeValue := ⟨257399, pr257399⟩
private theorem pr257459 : Nat.Prime 257459 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv109,pv1181]) (by decide +kernel)
def pv257459 : PrimeValue := ⟨257459, pr257459⟩
private theorem pr257627 : Nat.Prime 257627 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv128813]) (by decide +kernel)
def pv257627 : PrimeValue := ⟨257627, pr257627⟩
private theorem pr257657 : Nat.Prime 257657 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv43,pv107]) (by decide +kernel)
def pv257657 : PrimeValue := ⟨257657, pr257657⟩
private theorem pr257717 : Nat.Prime 257717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv3391]) (by decide +kernel)
def pv257717 : PrimeValue := ⟨257717, pr257717⟩
private theorem pr257947 : Nat.Prime 257947 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv3307]) (by decide +kernel)
def pv257947 : PrimeValue := ⟨257947, pr257947⟩
private theorem pr257981 : Nat.Prime 257981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv12899]) (by decide +kernel)
def pv257981 : PrimeValue := ⟨257981, pr257981⟩
private theorem pr258061 : Nat.Prime 258061 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv17,pv23]) (by decide +kernel)
def pv258061 : PrimeValue := ⟨258061, pr258061⟩
private theorem pr258119 : Nat.Prime 258119 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv103,pv179]) (by decide +kernel)
def pv258119 : PrimeValue := ⟨258119, pr258119⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
