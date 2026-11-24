/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table007
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table007.pv14951
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table003
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table004

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr14951 : Nat.Prime 14951 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv13,pv23]) (by decide +kernel)
def pv14951 : PrimeValue := ⟨14951, pr14951⟩
private theorem pr14957 : Nat.Prime 14957 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3739]) (by decide +kernel)
def pv14957 : PrimeValue := ⟨14957, pr14957⟩
private theorem pr14969 : Nat.Prime 14969 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1871]) (by decide +kernel)
def pv14969 : PrimeValue := ⟨14969, pr14969⟩
private theorem pr14983 : Nat.Prime 14983 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv227]) (by decide +kernel)
def pv14983 : PrimeValue := ⟨14983, pr14983⟩
private theorem pr15013 : Nat.Prime 15013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv139]) (by decide +kernel)
def pv15013 : PrimeValue := ⟨15013, pr15013⟩
private theorem pr15017 : Nat.Prime 15017 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1877]) (by decide +kernel)
def pv15017 : PrimeValue := ⟨15017, pr15017⟩
private theorem pr15031 : Nat.Prime 15031 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv167]) (by decide +kernel)
def pv15031 : PrimeValue := ⟨15031, pr15031⟩
private theorem pr15053 : Nat.Prime 15053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53,pv71]) (by decide +kernel)
def pv15053 : PrimeValue := ⟨15053, pr15053⟩
private theorem pr15061 : Nat.Prime 15061 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv251]) (by decide +kernel)
def pv15061 : PrimeValue := ⟨15061, pr15061⟩
private theorem pr15073 : Nat.Prime 15073 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv157]) (by decide +kernel)
def pv15073 : PrimeValue := ⟨15073, pr15073⟩
private theorem pr15077 : Nat.Prime 15077 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3769]) (by decide +kernel)
def pv15077 : PrimeValue := ⟨15077, pr15077⟩
private theorem pr15083 : Nat.Prime 15083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7541]) (by decide +kernel)
def pv15083 : PrimeValue := ⟨15083, pr15083⟩
private theorem pr15091 : Nat.Prime 15091 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv503]) (by decide +kernel)
def pv15091 : PrimeValue := ⟨15091, pr15091⟩
private theorem pr15101 : Nat.Prime 15101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv151]) (by decide +kernel)
def pv15101 : PrimeValue := ⟨15101, pr15101⟩
private theorem pr15107 : Nat.Prime 15107 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv13,pv83]) (by decide +kernel)
def pv15107 : PrimeValue := ⟨15107, pr15107⟩
private theorem pr15121 : Nat.Prime 15121 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv15121 : PrimeValue := ⟨15121, pr15121⟩
private theorem pr15131 : Nat.Prime 15131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv89]) (by decide +kernel)
def pv15131 : PrimeValue := ⟨15131, pr15131⟩
private theorem pr15137 : Nat.Prime 15137 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv43]) (by decide +kernel)
def pv15137 : PrimeValue := ⟨15137, pr15137⟩
private theorem pr15139 : Nat.Prime 15139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29]) (by decide +kernel)
def pv15139 : PrimeValue := ⟨15139, pr15139⟩
private theorem pr15149 : Nat.Prime 15149 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv541]) (by decide +kernel)
def pv15149 : PrimeValue := ⟨15149, pr15149⟩
private theorem pr15161 : Nat.Prime 15161 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv379]) (by decide +kernel)
def pv15161 : PrimeValue := ⟨15161, pr15161⟩
private theorem pr15173 : Nat.Prime 15173 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3793]) (by decide +kernel)
def pv15173 : PrimeValue := ⟨15173, pr15173⟩
private theorem pr15187 : Nat.Prime 15187 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2531]) (by decide +kernel)
def pv15187 : PrimeValue := ⟨15187, pr15187⟩
private theorem pr15193 : Nat.Prime 15193 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv211]) (by decide +kernel)
def pv15193 : PrimeValue := ⟨15193, pr15193⟩
private theorem pr15199 : Nat.Prime 15199 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv17,pv149]) (by decide +kernel)
def pv15199 : PrimeValue := ⟨15199, pr15199⟩
private theorem pr15217 : Nat.Prime 15217 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv317]) (by decide +kernel)
def pv15217 : PrimeValue := ⟨15217, pr15217⟩
private theorem pr15227 : Nat.Prime 15227 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv331]) (by decide +kernel)
def pv15227 : PrimeValue := ⟨15227, pr15227⟩
private theorem pr15233 : Nat.Prime 15233 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv17]) (by decide +kernel)
def pv15233 : PrimeValue := ⟨15233, pr15233⟩
private theorem pr15241 : Nat.Prime 15241 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv127]) (by decide +kernel)
def pv15241 : PrimeValue := ⟨15241, pr15241⟩
private theorem pr15259 : Nat.Prime 15259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2543]) (by decide +kernel)
def pv15259 : PrimeValue := ⟨15259, pr15259⟩
private theorem pr15263 : Nat.Prime 15263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv587]) (by decide +kernel)
def pv15263 : PrimeValue := ⟨15263, pr15263⟩
private theorem pr15269 : Nat.Prime 15269 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv347]) (by decide +kernel)
def pv15269 : PrimeValue := ⟨15269, pr15269⟩
private theorem pr15271 : Nat.Prime 15271 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv509]) (by decide +kernel)
def pv15271 : PrimeValue := ⟨15271, pr15271⟩
private theorem pr15277 : Nat.Prime 15277 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv19,pv67]) (by decide +kernel)
def pv15277 : PrimeValue := ⟨15277, pr15277⟩
private theorem pr15287 : Nat.Prime 15287 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7643]) (by decide +kernel)
def pv15287 : PrimeValue := ⟨15287, pr15287⟩
private theorem pr15289 : Nat.Prime 15289 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv13]) (by decide +kernel)
def pv15289 : PrimeValue := ⟨15289, pr15289⟩
private theorem pr15299 : Nat.Prime 15299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7649]) (by decide +kernel)
def pv15299 : PrimeValue := ⟨15299, pr15299⟩
private theorem pr15307 : Nat.Prime 15307 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv2551]) (by decide +kernel)
def pv15307 : PrimeValue := ⟨15307, pr15307⟩
private theorem pr15313 : Nat.Prime 15313 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv29]) (by decide +kernel)
def pv15313 : PrimeValue := ⟨15313, pr15313⟩
private theorem pr15319 : Nat.Prime 15319 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv37]) (by decide +kernel)
def pv15319 : PrimeValue := ⟨15319, pr15319⟩
private theorem pr15329 : Nat.Prime 15329 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv479]) (by decide +kernel)
def pv15329 : PrimeValue := ⟨15329, pr15329⟩
private theorem pr15331 : Nat.Prime 15331 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv73]) (by decide +kernel)
def pv15331 : PrimeValue := ⟨15331, pr15331⟩
private theorem pr15349 : Nat.Prime 15349 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1279]) (by decide +kernel)
def pv15349 : PrimeValue := ⟨15349, pr15349⟩
private theorem pr15359 : Nat.Prime 15359 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv7,pv1097]) (by decide +kernel)
def pv15359 : PrimeValue := ⟨15359, pr15359⟩
private theorem pr15361 : Nat.Prime 15361 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv15361 : PrimeValue := ⟨15361, pr15361⟩
private theorem pr15373 : Nat.Prime 15373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv61]) (by decide +kernel)
def pv15373 : PrimeValue := ⟨15373, pr15373⟩
private theorem pr15377 : Nat.Prime 15377 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31]) (by decide +kernel)
def pv15377 : PrimeValue := ⟨15377, pr15377⟩
private theorem pr15383 : Nat.Prime 15383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7691]) (by decide +kernel)
def pv15383 : PrimeValue := ⟨15383, pr15383⟩
private theorem pr15391 : Nat.Prime 15391 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv15391 : PrimeValue := ⟨15391, pr15391⟩
private theorem pr15401 : Nat.Prime 15401 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv7,pv11]) (by decide +kernel)
def pv15401 : PrimeValue := ⟨15401, pr15401⟩
private theorem pr15413 : Nat.Prime 15413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3853]) (by decide +kernel)
def pv15413 : PrimeValue := ⟨15413, pr15413⟩
private theorem pr15427 : Nat.Prime 15427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv857]) (by decide +kernel)
def pv15427 : PrimeValue := ⟨15427, pr15427⟩
private theorem pr15439 : Nat.Prime 15439 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv31,pv83]) (by decide +kernel)
def pv15439 : PrimeValue := ⟨15439, pr15439⟩
private theorem pr15443 : Nat.Prime 15443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv1103]) (by decide +kernel)
def pv15443 : PrimeValue := ⟨15443, pr15443⟩
private theorem pr15451 : Nat.Prime 15451 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv103]) (by decide +kernel)
def pv15451 : PrimeValue := ⟨15451, pr15451⟩
private theorem pr15461 : Nat.Prime 15461 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv773]) (by decide +kernel)
def pv15461 : PrimeValue := ⟨15461, pr15461⟩
private theorem pr15467 : Nat.Prime 15467 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv19,pv37]) (by decide +kernel)
def pv15467 : PrimeValue := ⟨15467, pr15467⟩
private theorem pr15473 : Nat.Prime 15473 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv967]) (by decide +kernel)
def pv15473 : PrimeValue := ⟨15473, pr15473⟩
private theorem pr15493 : Nat.Prime 15493 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1291]) (by decide +kernel)
def pv15493 : PrimeValue := ⟨15493, pr15493⟩
private theorem pr15497 : Nat.Prime 15497 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv149]) (by decide +kernel)
def pv15497 : PrimeValue := ⟨15497, pr15497⟩
private theorem pr15511 : Nat.Prime 15511 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv47]) (by decide +kernel)
def pv15511 : PrimeValue := ⟨15511, pr15511⟩
private theorem pr15527 : Nat.Prime 15527 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv1109]) (by decide +kernel)
def pv15527 : PrimeValue := ⟨15527, pr15527⟩
private theorem pr15541 : Nat.Prime 15541 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv7,pv37]) (by decide +kernel)
def pv15541 : PrimeValue := ⟨15541, pr15541⟩
private theorem pr15551 : Nat.Prime 15551 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv311]) (by decide +kernel)
def pv15551 : PrimeValue := ⟨15551, pr15551⟩
private theorem pr15559 : Nat.Prime 15559 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv2593]) (by decide +kernel)
def pv15559 : PrimeValue := ⟨15559, pr15559⟩
private theorem pr15569 : Nat.Prime 15569 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv139]) (by decide +kernel)
def pv15569 : PrimeValue := ⟨15569, pr15569⟩
private theorem pr15581 : Nat.Prime 15581 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19,pv41]) (by decide +kernel)
def pv15581 : PrimeValue := ⟨15581, pr15581⟩
private theorem pr15583 : Nat.Prime 15583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv53]) (by decide +kernel)
def pv15583 : PrimeValue := ⟨15583, pr15583⟩
private theorem pr15601 : Nat.Prime 15601 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv15601 : PrimeValue := ⟨15601, pr15601⟩
private theorem pr15607 : Nat.Prime 15607 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17]) (by decide +kernel)
def pv15607 : PrimeValue := ⟨15607, pr15607⟩
private theorem pr15619 : Nat.Prime 15619 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv19,pv137]) (by decide +kernel)
def pv15619 : PrimeValue := ⟨15619, pr15619⟩
private theorem pr15629 : Nat.Prime 15629 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3907]) (by decide +kernel)
def pv15629 : PrimeValue := ⟨15629, pr15629⟩
private theorem pr15641 : Nat.Prime 15641 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17,pv23]) (by decide +kernel)
def pv15641 : PrimeValue := ⟨15641, pr15641⟩
private theorem pr15643 : Nat.Prime 15643 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv79]) (by decide +kernel)
def pv15643 : PrimeValue := ⟨15643, pr15643⟩
private theorem pr15647 : Nat.Prime 15647 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7823]) (by decide +kernel)
def pv15647 : PrimeValue := ⟨15647, pr15647⟩
private theorem pr15649 : Nat.Prime 15649 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv163]) (by decide +kernel)
def pv15649 : PrimeValue := ⟨15649, pr15649⟩
private theorem pr15661 : Nat.Prime 15661 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv29]) (by decide +kernel)
def pv15661 : PrimeValue := ⟨15661, pr15661⟩
private theorem pr15667 : Nat.Prime 15667 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv373]) (by decide +kernel)
def pv15667 : PrimeValue := ⟨15667, pr15667⟩
private theorem pr15671 : Nat.Prime 15671 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv1567]) (by decide +kernel)
def pv15671 : PrimeValue := ⟨15671, pr15671⟩
private theorem pr15679 : Nat.Prime 15679 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv13,pv67]) (by decide +kernel)
def pv15679 : PrimeValue := ⟨15679, pr15679⟩
private theorem pr15683 : Nat.Prime 15683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7841]) (by decide +kernel)
def pv15683 : PrimeValue := ⟨15683, pr15683⟩
private theorem pr15727 : Nat.Prime 15727 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv2621]) (by decide +kernel)
def pv15727 : PrimeValue := ⟨15727, pr15727⟩
private theorem pr15731 : Nat.Prime 15731 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv13]) (by decide +kernel)
def pv15731 : PrimeValue := ⟨15731, pr15731⟩
private theorem pr15733 : Nat.Prime 15733 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv19,pv23]) (by decide +kernel)
def pv15733 : PrimeValue := ⟨15733, pr15733⟩
private theorem pr15737 : Nat.Prime 15737 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv281]) (by decide +kernel)
def pv15737 : PrimeValue := ⟨15737, pr15737⟩
private theorem pr15739 : Nat.Prime 15739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv43,pv61]) (by decide +kernel)
def pv15739 : PrimeValue := ⟨15739, pr15739⟩
private theorem pr15749 : Nat.Prime 15749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv127]) (by decide +kernel)
def pv15749 : PrimeValue := ⟨15749, pr15749⟩
private theorem pr15761 : Nat.Prime 15761 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv197]) (by decide +kernel)
def pv15761 : PrimeValue := ⟨15761, pr15761⟩
private theorem pr15767 : Nat.Prime 15767 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7883]) (by decide +kernel)
def pv15767 : PrimeValue := ⟨15767, pr15767⟩
private theorem pr15773 : Nat.Prime 15773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3943]) (by decide +kernel)
def pv15773 : PrimeValue := ⟨15773, pr15773⟩
private theorem pr15787 : Nat.Prime 15787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv877]) (by decide +kernel)
def pv15787 : PrimeValue := ⟨15787, pr15787⟩
private theorem pr15791 : Nat.Prime 15791 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv5,pv1579]) (by decide +kernel)
def pv15791 : PrimeValue := ⟨15791, pr15791⟩
private theorem pr15797 : Nat.Prime 15797 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv359]) (by decide +kernel)
def pv15797 : PrimeValue := ⟨15797, pr15797⟩
private theorem pr15803 : Nat.Prime 15803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7901]) (by decide +kernel)
def pv15803 : PrimeValue := ⟨15803, pr15803⟩
private theorem pr15809 : Nat.Prime 15809 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv19]) (by decide +kernel)
def pv15809 : PrimeValue := ⟨15809, pr15809⟩
private theorem pr15817 : Nat.Prime 15817 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv659]) (by decide +kernel)
def pv15817 : PrimeValue := ⟨15817, pr15817⟩
private theorem pr15823 : Nat.Prime 15823 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv293]) (by decide +kernel)
def pv15823 : PrimeValue := ⟨15823, pr15823⟩
private theorem pr15859 : Nat.Prime 15859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv881]) (by decide +kernel)
def pv15859 : PrimeValue := ⟨15859, pr15859⟩
private theorem pr15877 : Nat.Prime 15877 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv15877 : PrimeValue := ⟨15877, pr15877⟩
private theorem pr15881 : Nat.Prime 15881 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv397]) (by decide +kernel)
def pv15881 : PrimeValue := ⟨15881, pr15881⟩
private theorem pr15887 : Nat.Prime 15887 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv47]) (by decide +kernel)
def pv15887 : PrimeValue := ⟨15887, pr15887⟩
private theorem pr15889 : Nat.Prime 15889 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv331]) (by decide +kernel)
def pv15889 : PrimeValue := ⟨15889, pr15889⟩
private theorem pr15901 : Nat.Prime 15901 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv53]) (by decide +kernel)
def pv15901 : PrimeValue := ⟨15901, pr15901⟩
private theorem pr15907 : Nat.Prime 15907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv241]) (by decide +kernel)
def pv15907 : PrimeValue := ⟨15907, pr15907⟩
private theorem pr15913 : Nat.Prime 15913 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv17]) (by decide +kernel)
def pv15913 : PrimeValue := ⟨15913, pr15913⟩
private theorem pr15919 : Nat.Prime 15919 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv379]) (by decide +kernel)
def pv15919 : PrimeValue := ⟨15919, pr15919⟩
private theorem pr15923 : Nat.Prime 15923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv419]) (by decide +kernel)
def pv15923 : PrimeValue := ⟨15923, pr15923⟩
private theorem pr15937 : Nat.Prime 15937 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv83]) (by decide +kernel)
def pv15937 : PrimeValue := ⟨15937, pr15937⟩
private theorem pr15959 : Nat.Prime 15959 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv79,pv101]) (by decide +kernel)
def pv15959 : PrimeValue := ⟨15959, pr15959⟩
private theorem pr15971 : Nat.Prime 15971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1597]) (by decide +kernel)
def pv15971 : PrimeValue := ⟨15971, pr15971⟩
private theorem pr15973 : Nat.Prime 15973 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv15973 : PrimeValue := ⟨15973, pr15973⟩
private theorem pr15991 : Nat.Prime 15991 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv13,pv41]) (by decide +kernel)
def pv15991 : PrimeValue := ⟨15991, pr15991⟩
private theorem pr16001 : Nat.Prime 16001 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5]) (by decide +kernel)
def pv16001 : PrimeValue := ⟨16001, pr16001⟩
private theorem pr16007 : Nat.Prime 16007 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv53,pv151]) (by decide +kernel)
def pv16007 : PrimeValue := ⟨16007, pr16007⟩
private theorem pr16033 : Nat.Prime 16033 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv167]) (by decide +kernel)
def pv16033 : PrimeValue := ⟨16033, pr16033⟩
private theorem pr16057 : Nat.Prime 16057 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv223]) (by decide +kernel)
def pv16057 : PrimeValue := ⟨16057, pr16057⟩
private theorem pr16061 : Nat.Prime 16061 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv11,pv73]) (by decide +kernel)
def pv16061 : PrimeValue := ⟨16061, pr16061⟩
private theorem pr16063 : Nat.Prime 16063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2677]) (by decide +kernel)
def pv16063 : PrimeValue := ⟨16063, pr16063⟩
private theorem pr16067 : Nat.Prime 16067 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv277]) (by decide +kernel)
def pv16067 : PrimeValue := ⟨16067, pr16067⟩
private theorem pr16069 : Nat.Prime 16069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv103]) (by decide +kernel)
def pv16069 : PrimeValue := ⟨16069, pr16069⟩
private theorem pr16073 : Nat.Prime 16073 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv41]) (by decide +kernel)
def pv16073 : PrimeValue := ⟨16073, pr16073⟩
private theorem pr16087 : Nat.Prime 16087 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv383]) (by decide +kernel)
def pv16087 : PrimeValue := ⟨16087, pr16087⟩
private theorem pr16091 : Nat.Prime 16091 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv1609]) (by decide +kernel)
def pv16091 : PrimeValue := ⟨16091, pr16091⟩
private theorem pr16097 : Nat.Prime 16097 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv503]) (by decide +kernel)
def pv16097 : PrimeValue := ⟨16097, pr16097⟩
private theorem pr16103 : Nat.Prime 16103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv83,pv97]) (by decide +kernel)
def pv16103 : PrimeValue := ⟨16103, pr16103⟩
private theorem pr16111 : Nat.Prime 16111 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv179]) (by decide +kernel)
def pv16111 : PrimeValue := ⟨16111, pr16111⟩
private theorem pr16127 : Nat.Prime 16127 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv733]) (by decide +kernel)
def pv16127 : PrimeValue := ⟨16127, pr16127⟩
private theorem pr16139 : Nat.Prime 16139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv8069]) (by decide +kernel)
def pv16139 : PrimeValue := ⟨16139, pr16139⟩
private theorem pr16141 : Nat.Prime 16141 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv269]) (by decide +kernel)
def pv16141 : PrimeValue := ⟨16141, pr16141⟩
private theorem pr16183 : Nat.Prime 16183 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29,pv31]) (by decide +kernel)
def pv16183 : PrimeValue := ⟨16183, pr16183⟩
private theorem pr16187 : Nat.Prime 16187 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv8093]) (by decide +kernel)
def pv16187 : PrimeValue := ⟨16187, pr16187⟩
private theorem pr16189 : Nat.Prime 16189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv71]) (by decide +kernel)
def pv16189 : PrimeValue := ⟨16189, pr16189⟩
private theorem pr16193 : Nat.Prime 16193 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv23]) (by decide +kernel)
def pv16193 : PrimeValue := ⟨16193, pr16193⟩
private theorem pr16217 : Nat.Prime 16217 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2027]) (by decide +kernel)
def pv16217 : PrimeValue := ⟨16217, pr16217⟩
private theorem pr16223 : Nat.Prime 16223 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv8111]) (by decide +kernel)
def pv16223 : PrimeValue := ⟨16223, pr16223⟩
private theorem pr16229 : Nat.Prime 16229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv4057]) (by decide +kernel)
def pv16229 : PrimeValue := ⟨16229, pr16229⟩
private theorem pr16231 : Nat.Prime 16231 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv541]) (by decide +kernel)
def pv16231 : PrimeValue := ⟨16231, pr16231⟩
private theorem pr16249 : Nat.Prime 16249 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv677]) (by decide +kernel)
def pv16249 : PrimeValue := ⟨16249, pr16249⟩
private theorem pr16253 : Nat.Prime 16253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv239]) (by decide +kernel)
def pv16253 : PrimeValue := ⟨16253, pr16253⟩
private theorem pr16267 : Nat.Prime 16267 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv2711]) (by decide +kernel)
def pv16267 : PrimeValue := ⟨16267, pr16267⟩
private theorem pr16273 : Nat.Prime 16273 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv113]) (by decide +kernel)
def pv16273 : PrimeValue := ⟨16273, pr16273⟩
private theorem pr16301 : Nat.Prime 16301 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv163]) (by decide +kernel)
def pv16301 : PrimeValue := ⟨16301, pr16301⟩
private theorem pr16319 : Nat.Prime 16319 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv41,pv199]) (by decide +kernel)
def pv16319 : PrimeValue := ⟨16319, pr16319⟩
private theorem pr16333 : Nat.Prime 16333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1361]) (by decide +kernel)
def pv16333 : PrimeValue := ⟨16333, pr16333⟩
private theorem pr16339 : Nat.Prime 16339 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv389]) (by decide +kernel)
def pv16339 : PrimeValue := ⟨16339, pr16339⟩
private theorem pr16349 : Nat.Prime 16349 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv67]) (by decide +kernel)
def pv16349 : PrimeValue := ⟨16349, pr16349⟩
private theorem pr16361 : Nat.Prime 16361 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv409]) (by decide +kernel)
def pv16361 : PrimeValue := ⟨16361, pr16361⟩
private theorem pr16363 : Nat.Prime 16363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv101]) (by decide +kernel)
def pv16363 : PrimeValue := ⟨16363, pr16363⟩
private theorem pr16369 : Nat.Prime 16369 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv31]) (by decide +kernel)
def pv16369 : PrimeValue := ⟨16369, pr16369⟩
private theorem pr16381 : Nat.Prime 16381 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv13]) (by decide +kernel)
def pv16381 : PrimeValue := ⟨16381, pr16381⟩
private theorem pr16411 : Nat.Prime 16411 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv547]) (by decide +kernel)
def pv16411 : PrimeValue := ⟨16411, pr16411⟩
private theorem pr16417 : Nat.Prime 16417 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv19]) (by decide +kernel)
def pv16417 : PrimeValue := ⟨16417, pr16417⟩
private theorem pr16421 : Nat.Prime 16421 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv821]) (by decide +kernel)
def pv16421 : PrimeValue := ⟨16421, pr16421⟩
private theorem pr16427 : Nat.Prime 16427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv191]) (by decide +kernel)
def pv16427 : PrimeValue := ⟨16427, pr16427⟩
private theorem pr16433 : Nat.Prime 16433 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv79]) (by decide +kernel)
def pv16433 : PrimeValue := ⟨16433, pr16433⟩
private theorem pr16447 : Nat.Prime 16447 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv2741]) (by decide +kernel)
def pv16447 : PrimeValue := ⟨16447, pr16447⟩
private theorem pr16451 : Nat.Prime 16451 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv47]) (by decide +kernel)
def pv16451 : PrimeValue := ⟨16451, pr16451⟩
private theorem pr16453 : Nat.Prime 16453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv457]) (by decide +kernel)
def pv16453 : PrimeValue := ⟨16453, pr16453⟩
private theorem pr16477 : Nat.Prime 16477 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1373]) (by decide +kernel)
def pv16477 : PrimeValue := ⟨16477, pr16477⟩
private theorem pr16481 : Nat.Prime 16481 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv103]) (by decide +kernel)
def pv16481 : PrimeValue := ⟨16481, pr16481⟩
private theorem pr16487 : Nat.Prime 16487 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv8243]) (by decide +kernel)
def pv16487 : PrimeValue := ⟨16487, pr16487⟩
private theorem pr16493 : Nat.Prime 16493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv19,pv31]) (by decide +kernel)
def pv16493 : PrimeValue := ⟨16493, pr16493⟩
private theorem pr16519 : Nat.Prime 16519 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv2753]) (by decide +kernel)
def pv16519 : PrimeValue := ⟨16519, pr16519⟩
private theorem pr16529 : Nat.Prime 16529 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1033]) (by decide +kernel)
def pv16529 : PrimeValue := ⟨16529, pr16529⟩
private theorem pr16547 : Nat.Prime 16547 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv8273]) (by decide +kernel)
def pv16547 : PrimeValue := ⟨16547, pr16547⟩
private theorem pr16553 : Nat.Prime 16553 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2069]) (by decide +kernel)
def pv16553 : PrimeValue := ⟨16553, pr16553⟩
private theorem pr16561 : Nat.Prime 16561 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv23]) (by decide +kernel)
def pv16561 : PrimeValue := ⟨16561, pr16561⟩
private theorem pr16567 : Nat.Prime 16567 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv251]) (by decide +kernel)
def pv16567 : PrimeValue := ⟨16567, pr16567⟩
private theorem pr16573 : Nat.Prime 16573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1381]) (by decide +kernel)
def pv16573 : PrimeValue := ⟨16573, pr16573⟩
private theorem pr16603 : Nat.Prime 16603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2767]) (by decide +kernel)
def pv16603 : PrimeValue := ⟨16603, pr16603⟩
private theorem pr16607 : Nat.Prime 16607 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv23]) (by decide +kernel)
def pv16607 : PrimeValue := ⟨16607, pr16607⟩
private theorem pr16619 : Nat.Prime 16619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv1187]) (by decide +kernel)
def pv16619 : PrimeValue := ⟨16619, pr16619⟩
private theorem pr16631 : Nat.Prime 16631 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv1663]) (by decide +kernel)
def pv16631 : PrimeValue := ⟨16631, pr16631⟩
private theorem pr16633 : Nat.Prime 16633 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv7,pv11]) (by decide +kernel)
def pv16633 : PrimeValue := ⟨16633, pr16633⟩
private theorem pr16649 : Nat.Prime 16649 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2081]) (by decide +kernel)
def pv16649 : PrimeValue := ⟨16649, pr16649⟩
private theorem pr16651 : Nat.Prime 16651 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv37]) (by decide +kernel)
def pv16651 : PrimeValue := ⟨16651, pr16651⟩
private theorem pr16657 : Nat.Prime 16657 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv347]) (by decide +kernel)
def pv16657 : PrimeValue := ⟨16657, pr16657⟩
private theorem pr16661 : Nat.Prime 16661 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv17]) (by decide +kernel)
def pv16661 : PrimeValue := ⟨16661, pr16661⟩
private theorem pr16673 : Nat.Prime 16673 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv521]) (by decide +kernel)
def pv16673 : PrimeValue := ⟨16673, pr16673⟩
private theorem pr16691 : Nat.Prime 16691 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv1669]) (by decide +kernel)
def pv16691 : PrimeValue := ⟨16691, pr16691⟩
private theorem pr16693 : Nat.Prime 16693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv107]) (by decide +kernel)
def pv16693 : PrimeValue := ⟨16693, pr16693⟩
private theorem pr16699 : Nat.Prime 16699 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv23]) (by decide +kernel)
def pv16699 : PrimeValue := ⟨16699, pr16699⟩
private theorem pr16703 : Nat.Prime 16703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv1193]) (by decide +kernel)
def pv16703 : PrimeValue := ⟨16703, pr16703⟩
private theorem pr16729 : Nat.Prime 16729 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv17,pv41]) (by decide +kernel)
def pv16729 : PrimeValue := ⟨16729, pr16729⟩
private theorem pr16741 : Nat.Prime 16741 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv31]) (by decide +kernel)
def pv16741 : PrimeValue := ⟨16741, pr16741⟩
private theorem pr16747 : Nat.Prime 16747 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2791]) (by decide +kernel)
def pv16747 : PrimeValue := ⟨16747, pr16747⟩
private theorem pr16759 : Nat.Prime 16759 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv19]) (by decide +kernel)
def pv16759 : PrimeValue := ⟨16759, pr16759⟩
private theorem pr16763 : Nat.Prime 16763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv29]) (by decide +kernel)
def pv16763 : PrimeValue := ⟨16763, pr16763⟩
private theorem pr16787 : Nat.Prime 16787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv109]) (by decide +kernel)
def pv16787 : PrimeValue := ⟨16787, pr16787⟩
private theorem pr16811 : Nat.Prime 16811 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv41]) (by decide +kernel)
def pv16811 : PrimeValue := ⟨16811, pr16811⟩
private theorem pr16823 : Nat.Prime 16823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv647]) (by decide +kernel)
def pv16823 : PrimeValue := ⟨16823, pr16823⟩
private theorem pr16829 : Nat.Prime 16829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv601]) (by decide +kernel)
def pv16829 : PrimeValue := ⟨16829, pr16829⟩
private theorem pr16831 : Nat.Prime 16831 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv17]) (by decide +kernel)
def pv16831 : PrimeValue := ⟨16831, pr16831⟩
private theorem pr16843 : Nat.Prime 16843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv401]) (by decide +kernel)
def pv16843 : PrimeValue := ⟨16843, pr16843⟩
private theorem pr16871 : Nat.Prime 16871 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv7,pv241]) (by decide +kernel)
def pv16871 : PrimeValue := ⟨16871, pr16871⟩
private theorem pr16879 : Nat.Prime 16879 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29,pv97]) (by decide +kernel)
def pv16879 : PrimeValue := ⟨16879, pr16879⟩
private theorem pr16883 : Nat.Prime 16883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv367]) (by decide +kernel)
def pv16883 : PrimeValue := ⟨16883, pr16883⟩
private theorem pr16889 : Nat.Prime 16889 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2111]) (by decide +kernel)
def pv16889 : PrimeValue := ⟨16889, pr16889⟩
private theorem pr16901 : Nat.Prime 16901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13]) (by decide +kernel)
def pv16901 : PrimeValue := ⟨16901, pr16901⟩
private theorem pr16903 : Nat.Prime 16903 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv313]) (by decide +kernel)
def pv16903 : PrimeValue := ⟨16903, pr16903⟩
private theorem pr16921 : Nat.Prime 16921 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv47]) (by decide +kernel)
def pv16921 : PrimeValue := ⟨16921, pr16921⟩
private theorem pr16927 : Nat.Prime 16927 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv13,pv31]) (by decide +kernel)
def pv16927 : PrimeValue := ⟨16927, pr16927⟩
private theorem pr16931 : Nat.Prime 16931 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1693]) (by decide +kernel)
def pv16931 : PrimeValue := ⟨16931, pr16931⟩
private theorem pr16937 : Nat.Prime 16937 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv73]) (by decide +kernel)
def pv16937 : PrimeValue := ⟨16937, pr16937⟩
private theorem pr16943 : Nat.Prime 16943 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv43,pv197]) (by decide +kernel)
def pv16943 : PrimeValue := ⟨16943, pr16943⟩
private theorem pr16963 : Nat.Prime 16963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv257]) (by decide +kernel)
def pv16963 : PrimeValue := ⟨16963, pr16963⟩
private theorem pr16979 : Nat.Prime 16979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv653]) (by decide +kernel)
def pv16979 : PrimeValue := ⟨16979, pr16979⟩
private theorem pr16981 : Nat.Prime 16981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv283]) (by decide +kernel)
def pv16981 : PrimeValue := ⟨16981, pr16981⟩
private theorem pr16987 : Nat.Prime 16987 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv149]) (by decide +kernel)
def pv16987 : PrimeValue := ⟨16987, pr16987⟩
private theorem pr16993 : Nat.Prime 16993 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv59]) (by decide +kernel)
def pv16993 : PrimeValue := ⟨16993, pr16993⟩
private theorem pr17011 : Nat.Prime 17011 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv17011 : PrimeValue := ⟨17011, pr17011⟩
private theorem pr17021 : Nat.Prime 17021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23,pv37]) (by decide +kernel)
def pv17021 : PrimeValue := ⟨17021, pr17021⟩
private theorem pr17027 : Nat.Prime 17027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv8513]) (by decide +kernel)
def pv17027 : PrimeValue := ⟨17027, pr17027⟩
private theorem pr17029 : Nat.Prime 17029 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv11,pv43]) (by decide +kernel)
def pv17029 : PrimeValue := ⟨17029, pr17029⟩
private theorem pr17033 : Nat.Prime 17033 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2129]) (by decide +kernel)
def pv17033 : PrimeValue := ⟨17033, pr17033⟩
private theorem pr17041 : Nat.Prime 17041 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv71]) (by decide +kernel)
def pv17041 : PrimeValue := ⟨17041, pr17041⟩
private theorem pr17047 : Nat.Prime 17047 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv947]) (by decide +kernel)
def pv17047 : PrimeValue := ⟨17047, pr17047⟩
private theorem pr17053 : Nat.Prime 17053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv29]) (by decide +kernel)
def pv17053 : PrimeValue := ⟨17053, pr17053⟩
private theorem pr17077 : Nat.Prime 17077 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1423]) (by decide +kernel)
def pv17077 : PrimeValue := ⟨17077, pr17077⟩
private theorem pr17093 : Nat.Prime 17093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv4273]) (by decide +kernel)
def pv17093 : PrimeValue := ⟨17093, pr17093⟩
private theorem pr17099 : Nat.Prime 17099 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv83,pv103]) (by decide +kernel)
def pv17099 : PrimeValue := ⟨17099, pr17099⟩
private theorem pr17107 : Nat.Prime 17107 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv2851]) (by decide +kernel)
def pv17107 : PrimeValue := ⟨17107, pr17107⟩
private theorem pr17117 : Nat.Prime 17117 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv389]) (by decide +kernel)
def pv17117 : PrimeValue := ⟨17117, pr17117⟩
private theorem pr17123 : Nat.Prime 17123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv1223]) (by decide +kernel)
def pv17123 : PrimeValue := ⟨17123, pr17123⟩
private theorem pr17137 : Nat.Prime 17137 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv17]) (by decide +kernel)
def pv17137 : PrimeValue := ⟨17137, pr17137⟩
private theorem pr17159 : Nat.Prime 17159 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv23,pv373]) (by decide +kernel)
def pv17159 : PrimeValue := ⟨17159, pr17159⟩
private theorem pr17167 : Nat.Prime 17167 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv2861]) (by decide +kernel)
def pv17167 : PrimeValue := ⟨17167, pr17167⟩
private theorem pr17183 : Nat.Prime 17183 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv71]) (by decide +kernel)
def pv17183 : PrimeValue := ⟨17183, pr17183⟩
private theorem pr17189 : Nat.Prime 17189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv4297]) (by decide +kernel)
def pv17189 : PrimeValue := ⟨17189, pr17189⟩
private theorem pr17191 : Nat.Prime 17191 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv191]) (by decide +kernel)
def pv17191 : PrimeValue := ⟨17191, pr17191⟩
private theorem pr17203 : Nat.Prime 17203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv47,pv61]) (by decide +kernel)
def pv17203 : PrimeValue := ⟨17203, pr17203⟩
private theorem pr17207 : Nat.Prime 17207 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv1229]) (by decide +kernel)
def pv17207 : PrimeValue := ⟨17207, pr17207⟩
private theorem pr17209 : Nat.Prime 17209 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv239]) (by decide +kernel)
def pv17209 : PrimeValue := ⟨17209, pr17209⟩
private theorem pr17231 : Nat.Prime 17231 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv1723]) (by decide +kernel)
def pv17231 : PrimeValue := ⟨17231, pr17231⟩
private theorem pr17239 : Nat.Prime 17239 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv13,pv17]) (by decide +kernel)
def pv17239 : PrimeValue := ⟨17239, pr17239⟩
private theorem pr17257 : Nat.Prime 17257 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv719]) (by decide +kernel)
def pv17257 : PrimeValue := ⟨17257, pr17257⟩
private theorem pr17291 : Nat.Prime 17291 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv13,pv19]) (by decide +kernel)
def pv17291 : PrimeValue := ⟨17291, pr17291⟩
private theorem pr17293 : Nat.Prime 17293 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv131]) (by decide +kernel)
def pv17293 : PrimeValue := ⟨17293, pr17293⟩
private theorem pr17299 : Nat.Prime 17299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31]) (by decide +kernel)
def pv17299 : PrimeValue := ⟨17299, pr17299⟩
private theorem pr17317 : Nat.Prime 17317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv37]) (by decide +kernel)
def pv17317 : PrimeValue := ⟨17317, pr17317⟩
private theorem pr17321 : Nat.Prime 17321 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv433]) (by decide +kernel)
def pv17321 : PrimeValue := ⟨17321, pr17321⟩
private theorem pr17327 : Nat.Prime 17327 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv8663]) (by decide +kernel)
def pv17327 : PrimeValue := ⟨17327, pr17327⟩
private theorem pr17333 : Nat.Prime 17333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv619]) (by decide +kernel)
def pv17333 : PrimeValue := ⟨17333, pr17333⟩
private theorem pr17341 : Nat.Prime 17341 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv17341 : PrimeValue := ⟨17341, pr17341⟩
private theorem pr17351 : Nat.Prime 17351 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv347]) (by decide +kernel)
def pv17351 : PrimeValue := ⟨17351, pr17351⟩
private theorem pr17359 : Nat.Prime 17359 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv263]) (by decide +kernel)
def pv17359 : PrimeValue := ⟨17359, pr17359⟩
private theorem pr17377 : Nat.Prime 17377 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv181]) (by decide +kernel)
def pv17377 : PrimeValue := ⟨17377, pr17377⟩
private theorem pr17383 : Nat.Prime 17383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2897]) (by decide +kernel)
def pv17383 : PrimeValue := ⟨17383, pr17383⟩
private theorem pr17387 : Nat.Prime 17387 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv8693]) (by decide +kernel)
def pv17387 : PrimeValue := ⟨17387, pr17387⟩
private theorem pr17389 : Nat.Prime 17389 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv23]) (by decide +kernel)
def pv17389 : PrimeValue := ⟨17389, pr17389⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
