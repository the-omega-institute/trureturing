/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table161
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table161.pv163309
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table012
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table032
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table033
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table034

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr163309 : Nat.Prime 163309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv439]) (by decide +kernel)
def pv163309 : PrimeValue := ⟨163309, pr163309⟩
private theorem pr163327 : Nat.Prime 163327 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv163,pv167]) (by decide +kernel)
def pv163327 : PrimeValue := ⟨163327, pr163327⟩
private theorem pr163477 : Nat.Prime 163477 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv19,pv239]) (by decide +kernel)
def pv163477 : PrimeValue := ⟨163477, pr163477⟩
private theorem pr163543 : Nat.Prime 163543 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv97,pv281]) (by decide +kernel)
def pv163543 : PrimeValue := ⟨163543, pr163543⟩
private theorem pr163567 : Nat.Prime 163567 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv13,pv233]) (by decide +kernel)
def pv163567 : PrimeValue := ⟨163567, pr163567⟩
private theorem pr163613 : Nat.Prime 163613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv40903]) (by decide +kernel)
def pv163613 : PrimeValue := ⟨163613, pr163613⟩
private theorem pr163661 : Nat.Prime 163661 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv167]) (by decide +kernel)
def pv163661 : PrimeValue := ⟨163661, pr163661⟩
private theorem pr163861 : Nat.Prime 163861 :=
  checkPrime_prime (q := pv59) (ls := [pv2,pv3,pv5,pv2731]) (by decide +kernel)
def pv163861 : PrimeValue := ⟨163861, pr163861⟩
private theorem pr163973 : Nat.Prime 163973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv40993]) (by decide +kernel)
def pv163973 : PrimeValue := ⟨163973, pr163973⟩
private theorem pr163979 : Nat.Prime 163979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv163,pv503]) (by decide +kernel)
def pv163979 : PrimeValue := ⟨163979, pr163979⟩
private theorem pr163993 : Nat.Prime 163993 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv6833]) (by decide +kernel)
def pv163993 : PrimeValue := ⟨163993, pr163993⟩
private theorem pr163997 : Nat.Prime 163997 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv5857]) (by decide +kernel)
def pv163997 : PrimeValue := ⟨163997, pr163997⟩
private theorem pr164209 : Nat.Prime 164209 :=
  checkPrime_prime (q := pv47) (ls := [pv2,pv3,pv11,pv311]) (by decide +kernel)
def pv164209 : PrimeValue := ⟨164209, pr164209⟩
private theorem pr164251 : Nat.Prime 164251 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv73]) (by decide +kernel)
def pv164251 : PrimeValue := ⟨164251, pr164251⟩
private theorem pr164267 : Nat.Prime 164267 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv3571]) (by decide +kernel)
def pv164267 : PrimeValue := ⟨164267, pr164267⟩
private theorem pr164291 : Nat.Prime 164291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv2347]) (by decide +kernel)
def pv164291 : PrimeValue := ⟨164291, pr164291⟩
private theorem pr164377 : Nat.Prime 164377 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv761]) (by decide +kernel)
def pv164377 : PrimeValue := ⟨164377, pr164377⟩
private theorem pr164503 : Nat.Prime 164503 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv19,pv37]) (by decide +kernel)
def pv164503 : PrimeValue := ⟨164503, pr164503⟩
private theorem pr164599 : Nat.Prime 164599 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv3919]) (by decide +kernel)
def pv164599 : PrimeValue := ⟨164599, pr164599⟩
private theorem pr164701 : Nat.Prime 164701 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv61]) (by decide +kernel)
def pv164701 : PrimeValue := ⟨164701, pr164701⟩
private theorem pr164821 : Nat.Prime 164821 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv41,pv67]) (by decide +kernel)
def pv164821 : PrimeValue := ⟨164821, pr164821⟩
private theorem pr164893 : Nat.Prime 164893 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv13,pv151]) (by decide +kernel)
def pv164893 : PrimeValue := ⟨164893, pr164893⟩
private theorem pr164963 : Nat.Prime 164963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11783]) (by decide +kernel)
def pv164963 : PrimeValue := ⟨164963, pr164963⟩
private theorem pr165059 : Nat.Prime 165059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv82529]) (by decide +kernel)
def pv165059 : PrimeValue := ⟨165059, pr165059⟩
private theorem pr165211 : Nat.Prime 165211 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv5507]) (by decide +kernel)
def pv165211 : PrimeValue := ⟨165211, pr165211⟩
private theorem pr165349 : Nat.Prime 165349 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1531]) (by decide +kernel)
def pv165349 : PrimeValue := ⟨165349, pr165349⟩
private theorem pr165391 : Nat.Prime 165391 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv37,pv149]) (by decide +kernel)
def pv165391 : PrimeValue := ⟨165391, pr165391⟩
private theorem pr165463 : Nat.Prime 165463 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv23,pv109]) (by decide +kernel)
def pv165463 : PrimeValue := ⟨165463, pr165463⟩
private theorem pr165667 : Nat.Prime 165667 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv27611]) (by decide +kernel)
def pv165667 : PrimeValue := ⟨165667, pr165667⟩
private theorem pr165703 : Nat.Prime 165703 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv27617]) (by decide +kernel)
def pv165703 : PrimeValue := ⟨165703, pr165703⟩
private theorem pr165709 : Nat.Prime 165709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4603]) (by decide +kernel)
def pv165709 : PrimeValue := ⟨165709, pr165709⟩
private theorem pr165799 : Nat.Prime 165799 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv61,pv151]) (by decide +kernel)
def pv165799 : PrimeValue := ⟨165799, pr165799⟩
private theorem pr165883 : Nat.Prime 165883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv27647]) (by decide +kernel)
def pv165883 : PrimeValue := ⟨165883, pr165883⟩
private theorem pr166099 : Nat.Prime 166099 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv31,pv47]) (by decide +kernel)
def pv166099 : PrimeValue := ⟨166099, pr166099⟩
private theorem pr166207 : Nat.Prime 166207 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv27701]) (by decide +kernel)
def pv166207 : PrimeValue := ⟨166207, pr166207⟩
private theorem pr166363 : Nat.Prime 166363 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv17,pv233]) (by decide +kernel)
def pv166363 : PrimeValue := ⟨166363, pr166363⟩
private theorem pr166417 : Nat.Prime 166417 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv3467]) (by decide +kernel)
def pv166417 : PrimeValue := ⟨166417, pr166417⟩
private theorem pr166601 : Nat.Prime 166601 :=
  checkPrime_prime (q := pv47) (ls := [pv2,pv5,pv7,pv17]) (by decide +kernel)
def pv166601 : PrimeValue := ⟨166601, pr166601⟩
private theorem pr166603 : Nat.Prime 166603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv27767]) (by decide +kernel)
def pv166603 : PrimeValue := ⟨166603, pr166603⟩
private theorem pr166631 : Nat.Prime 166631 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv19,pv877]) (by decide +kernel)
def pv166631 : PrimeValue := ⟨166631, pr166631⟩
private theorem pr166703 : Nat.Prime 166703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv4903]) (by decide +kernel)
def pv166703 : PrimeValue := ⟨166703, pr166703⟩
private theorem pr166741 : Nat.Prime 166741 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv397]) (by decide +kernel)
def pv166741 : PrimeValue := ⟨166741, pr166741⟩
private theorem pr166849 : Nat.Prime 166849 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv11,pv79]) (by decide +kernel)
def pv166849 : PrimeValue := ⟨166849, pr166849⟩
private theorem pr167033 : Nat.Prime 167033 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv20879]) (by decide +kernel)
def pv167033 : PrimeValue := ⟨167033, pr167033⟩
private theorem pr167077 : Nat.Prime 167077 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv17]) (by decide +kernel)
def pv167077 : PrimeValue := ⟨167077, pr167077⟩
private theorem pr167107 : Nat.Prime 167107 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv27851]) (by decide +kernel)
def pv167107 : PrimeValue := ⟨167107, pr167107⟩
private theorem pr167191 : Nat.Prime 167191 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv5573]) (by decide +kernel)
def pv167191 : PrimeValue := ⟨167191, pr167191⟩
private theorem pr167197 : Nat.Prime 167197 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13933]) (by decide +kernel)
def pv167197 : PrimeValue := ⟨167197, pr167197⟩
private theorem pr167449 : Nat.Prime 167449 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv6977]) (by decide +kernel)
def pv167449 : PrimeValue := ⟨167449, pr167449⟩
private theorem pr167521 : Nat.Prime 167521 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv349]) (by decide +kernel)
def pv167521 : PrimeValue := ⟨167521, pr167521⟩
private theorem pr167543 : Nat.Prime 167543 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv4409]) (by decide +kernel)
def pv167543 : PrimeValue := ⟨167543, pr167543⟩
private theorem pr167899 : Nat.Prime 167899 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv27983]) (by decide +kernel)
def pv167899 : PrimeValue := ⟨167899, pr167899⟩
private theorem pr168323 : Nat.Prime 168323 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv11,pv1093]) (by decide +kernel)
def pv168323 : PrimeValue := ⟨168323, pr168323⟩
private theorem pr168677 : Nat.Prime 168677 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv42169]) (by decide +kernel)
def pv168677 : PrimeValue := ⟨168677, pr168677⟩
private theorem pr169249 : Nat.Prime 169249 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv41,pv43]) (by decide +kernel)
def pv169249 : PrimeValue := ⟨169249, pr169249⟩
private theorem pr169627 : Nat.Prime 169627 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv1663]) (by decide +kernel)
def pv169627 : PrimeValue := ⟨169627, pr169627⟩
private theorem pr169783 : Nat.Prime 169783 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv28297]) (by decide +kernel)
def pv169783 : PrimeValue := ⟨169783, pr169783⟩
private theorem pr169951 : Nat.Prime 169951 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv103]) (by decide +kernel)
def pv169951 : PrimeValue := ⟨169951, pr169951⟩
private theorem pr170101 : Nat.Prime 170101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv170101 : PrimeValue := ⟨170101, pr170101⟩
private theorem pr170213 : Nat.Prime 170213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv6079]) (by decide +kernel)
def pv170213 : PrimeValue := ⟨170213, pr170213⟩
private theorem pr170341 : Nat.Prime 170341 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv17,pv167]) (by decide +kernel)
def pv170341 : PrimeValue := ⟨170341, pr170341⟩
private theorem pr170413 : Nat.Prime 170413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv1291]) (by decide +kernel)
def pv170413 : PrimeValue := ⟨170413, pr170413⟩
private theorem pr170749 : Nat.Prime 170749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv31]) (by decide +kernel)
def pv170749 : PrimeValue := ⟨170749, pr170749⟩
private theorem pr170759 : Nat.Prime 170759 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv12197]) (by decide +kernel)
def pv170759 : PrimeValue := ⟨170759, pr170759⟩
private theorem pr170773 : Nat.Prime 170773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv19,pv107]) (by decide +kernel)
def pv170773 : PrimeValue := ⟨170773, pr170773⟩
private theorem pr170851 : Nat.Prime 170851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv67]) (by decide +kernel)
def pv170851 : PrimeValue := ⟨170851, pr170851⟩
private theorem pr171427 : Nat.Prime 171427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv28571]) (by decide +kernel)
def pv171427 : PrimeValue := ⟨171427, pr171427⟩
private theorem pr171469 : Nat.Prime 171469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv433]) (by decide +kernel)
def pv171469 : PrimeValue := ⟨171469, pr171469⟩
private theorem pr171559 : Nat.Prime 171559 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv353]) (by decide +kernel)
def pv171559 : PrimeValue := ⟨171559, pr171559⟩
private theorem pr171713 : Nat.Prime 171713 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2683]) (by decide +kernel)
def pv171713 : PrimeValue := ⟨171713, pr171713⟩
private theorem pr171733 : Nat.Prime 171733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv1301]) (by decide +kernel)
def pv171733 : PrimeValue := ⟨171733, pr171733⟩
private theorem pr171947 : Nat.Prime 171947 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv149,pv577]) (by decide +kernel)
def pv171947 : PrimeValue := ⟨171947, pr171947⟩
private theorem pr172153 : Nat.Prime 172153 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv797]) (by decide +kernel)
def pv172153 : PrimeValue := ⟨172153, pr172153⟩
private theorem pr172561 : Nat.Prime 172561 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv719]) (by decide +kernel)
def pv172561 : PrimeValue := ⟨172561, pr172561⟩
private theorem pr172607 : Nat.Prime 172607 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv12329]) (by decide +kernel)
def pv172607 : PrimeValue := ⟨172607, pr172607⟩
private theorem pr172643 : Nat.Prime 172643 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv2333]) (by decide +kernel)
def pv172643 : PrimeValue := ⟨172643, pr172643⟩
private theorem pr172709 : Nat.Prime 172709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43177]) (by decide +kernel)
def pv172709 : PrimeValue := ⟨172709, pr172709⟩
private theorem pr173023 : Nat.Prime 173023 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv28837]) (by decide +kernel)
def pv173023 : PrimeValue := ⟨173023, pr173023⟩
private theorem pr173207 : Nat.Prime 173207 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv7873]) (by decide +kernel)
def pv173207 : PrimeValue := ⟨173207, pr173207⟩
private theorem pr173347 : Nat.Prime 173347 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv167,pv173]) (by decide +kernel)
def pv173347 : PrimeValue := ⟨173347, pr173347⟩
private theorem pr173561 : Nat.Prime 173561 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv4339]) (by decide +kernel)
def pv173561 : PrimeValue := ⟨173561, pr173561⟩
private theorem pr173599 : Nat.Prime 173599 :=
  checkPrime_prime (q := pv59) (ls := [pv2,pv3,pv28933]) (by decide +kernel)
def pv173599 : PrimeValue := ⟨173599, pr173599⟩
private theorem pr173617 : Nat.Prime 173617 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv3617]) (by decide +kernel)
def pv173617 : PrimeValue := ⟨173617, pr173617⟩
private theorem pr173659 : Nat.Prime 173659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv103,pv281]) (by decide +kernel)
def pv173659 : PrimeValue := ⟨173659, pr173659⟩
private theorem pr173713 : Nat.Prime 173713 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv47]) (by decide +kernel)
def pv173713 : PrimeValue := ⟨173713, pr173713⟩
private theorem pr174067 : Nat.Prime 174067 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv67,pv433]) (by decide +kernel)
def pv174067 : PrimeValue := ⟨174067, pr174067⟩
private theorem pr174077 : Nat.Prime 174077 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv6217]) (by decide +kernel)
def pv174077 : PrimeValue := ⟨174077, pr174077⟩
private theorem pr174299 : Nat.Prime 174299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv87149]) (by decide +kernel)
def pv174299 : PrimeValue := ⟨174299, pr174299⟩
private theorem pr174571 : Nat.Prime 174571 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv23]) (by decide +kernel)
def pv174571 : PrimeValue := ⟨174571, pr174571⟩
private theorem pr174631 : Nat.Prime 174631 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv5821]) (by decide +kernel)
def pv174631 : PrimeValue := ⟨174631, pr174631⟩
private theorem pr174767 : Nat.Prime 174767 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv87383]) (by decide +kernel)
def pv174767 : PrimeValue := ⟨174767, pr174767⟩
private theorem pr174929 : Nat.Prime 174929 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv29]) (by decide +kernel)
def pv174929 : PrimeValue := ⟨174929, pr174929⟩
private theorem pr175003 : Nat.Prime 175003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29167]) (by decide +kernel)
def pv175003 : PrimeValue := ⟨175003, pr175003⟩
private theorem pr175067 : Nat.Prime 175067 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv19,pv271]) (by decide +kernel)
def pv175067 : PrimeValue := ⟨175067, pr175067⟩
private theorem pr175333 : Nat.Prime 175333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv769]) (by decide +kernel)
def pv175333 : PrimeValue := ⟨175333, pr175333⟩
private theorem pr175493 : Nat.Prime 175493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv73,pv601]) (by decide +kernel)
def pv175493 : PrimeValue := ⟨175493, pr175493⟩
private theorem pr175499 : Nat.Prime 175499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv1867]) (by decide +kernel)
def pv175499 : PrimeValue := ⟨175499, pr175499⟩
private theorem pr175649 : Nat.Prime 175649 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv499]) (by decide +kernel)
def pv175649 : PrimeValue := ⟨175649, pr175649⟩
private theorem pr175663 : Nat.Prime 175663 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv3253]) (by decide +kernel)
def pv175663 : PrimeValue := ⟨175663, pr175663⟩
private theorem pr175757 : Nat.Prime 175757 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv6277]) (by decide +kernel)
def pv175757 : PrimeValue := ⟨175757, pr175757⟩
private theorem pr175783 : Nat.Prime 175783 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29297]) (by decide +kernel)
def pv175783 : PrimeValue := ⟨175783, pr175783⟩
private theorem pr175859 : Nat.Prime 175859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv3823]) (by decide +kernel)
def pv175859 : PrimeValue := ⟨175859, pr175859⟩
private theorem pr175937 : Nat.Prime 175937 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2749]) (by decide +kernel)
def pv175937 : PrimeValue := ⟨175937, pr175937⟩
private theorem pr175949 : Nat.Prime 175949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43987]) (by decide +kernel)
def pv175949 : PrimeValue := ⟨175949, pr175949⟩
private theorem pr176023 : Nat.Prime 176023 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv11,pv127]) (by decide +kernel)
def pv176023 : PrimeValue := ⟨176023, pr176023⟩
private theorem pr176153 : Nat.Prime 176153 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv97,pv227]) (by decide +kernel)
def pv176153 : PrimeValue := ⟨176153, pr176153⟩
private theorem pr176179 : Nat.Prime 176179 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29363]) (by decide +kernel)
def pv176179 : PrimeValue := ⟨176179, pr176179⟩
private theorem pr176207 : Nat.Prime 176207 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv4637]) (by decide +kernel)
def pv176207 : PrimeValue := ⟨176207, pr176207⟩
private theorem pr176333 : Nat.Prime 176333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv3391]) (by decide +kernel)
def pv176333 : PrimeValue := ⟨176333, pr176333⟩
private theorem pr176419 : Nat.Prime 176419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv176419 : PrimeValue := ⟨176419, pr176419⟩
private theorem pr176531 : Nat.Prime 176531 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv127,pv139]) (by decide +kernel)
def pv176531 : PrimeValue := ⟨176531, pr176531⟩
private theorem pr176651 : Nat.Prime 176651 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv3533]) (by decide +kernel)
def pv176651 : PrimeValue := ⟨176651, pr176651⟩
private theorem pr176741 : Nat.Prime 176741 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv8837]) (by decide +kernel)
def pv176741 : PrimeValue := ⟨176741, pr176741⟩
private theorem pr176899 : Nat.Prime 176899 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29483]) (by decide +kernel)
def pv176899 : PrimeValue := ⟨176899, pr176899⟩
private theorem pr176927 : Nat.Prime 176927 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv88463]) (by decide +kernel)
def pv176927 : PrimeValue := ⟨176927, pr176927⟩
private theorem pr177283 : Nat.Prime 177283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv67]) (by decide +kernel)
def pv177283 : PrimeValue := ⟨177283, pr177283⟩
private theorem pr177383 : Nat.Prime 177383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv31,pv2861]) (by decide +kernel)
def pv177383 : PrimeValue := ⟨177383, pr177383⟩
private theorem pr177433 : Nat.Prime 177433 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7393]) (by decide +kernel)
def pv177433 : PrimeValue := ⟨177433, pr177433⟩
private theorem pr177493 : Nat.Prime 177493 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv2113]) (by decide +kernel)
def pv177493 : PrimeValue := ⟨177493, pr177493⟩
private theorem pr177533 : Nat.Prime 177533 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv44383]) (by decide +kernel)
def pv177533 : PrimeValue := ⟨177533, pr177533⟩
private theorem pr177691 : Nat.Prime 177691 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv5923]) (by decide +kernel)
def pv177691 : PrimeValue := ⟨177691, pr177691⟩
private theorem pr177763 : Nat.Prime 177763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv43,pv53]) (by decide +kernel)
def pv177763 : PrimeValue := ⟨177763, pr177763⟩
private theorem pr177889 : Nat.Prime 177889 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv17,pv109]) (by decide +kernel)
def pv177889 : PrimeValue := ⟨177889, pr177889⟩
private theorem pr177917 : Nat.Prime 177917 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv2341]) (by decide +kernel)
def pv177917 : PrimeValue := ⟨177917, pr177917⟩
private theorem pr177943 : Nat.Prime 177943 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv47,pv631]) (by decide +kernel)
def pv177943 : PrimeValue := ⟨177943, pr177943⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
