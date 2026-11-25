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
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr163309 : PrimeCertificate 163309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv439]) (by decide +kernel)
def pv163309 : PrimeValue := ⟨163309, pr163309⟩
private theorem pr163327 : PrimeCertificate 163327 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv163,pv167]) (by decide +kernel)
def pv163327 : PrimeValue := ⟨163327, pr163327⟩
private theorem pr163477 : PrimeCertificate 163477 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv19,pv239]) (by decide +kernel)
def pv163477 : PrimeValue := ⟨163477, pr163477⟩
private theorem pr163543 : PrimeCertificate 163543 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv97,pv281]) (by decide +kernel)
def pv163543 : PrimeValue := ⟨163543, pr163543⟩
private theorem pr163567 : PrimeCertificate 163567 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13,pv233]) (by decide +kernel)
def pv163567 : PrimeValue := ⟨163567, pr163567⟩
private theorem pr163613 : PrimeCertificate 163613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv40903]) (by decide +kernel)
def pv163613 : PrimeValue := ⟨163613, pr163613⟩
private theorem pr163661 : PrimeCertificate 163661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv167]) (by decide +kernel)
def pv163661 : PrimeValue := ⟨163661, pr163661⟩
private theorem pr163861 : PrimeCertificate 163861 :=
  certifyPrime (q := pv59) (ls := [pv2,pv3,pv5,pv2731]) (by decide +kernel)
def pv163861 : PrimeValue := ⟨163861, pr163861⟩
private theorem pr163973 : PrimeCertificate 163973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv40993]) (by decide +kernel)
def pv163973 : PrimeValue := ⟨163973, pr163973⟩
private theorem pr163979 : PrimeCertificate 163979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv163,pv503]) (by decide +kernel)
def pv163979 : PrimeValue := ⟨163979, pr163979⟩
private theorem pr163993 : PrimeCertificate 163993 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv6833]) (by decide +kernel)
def pv163993 : PrimeValue := ⟨163993, pr163993⟩
private theorem pr163997 : PrimeCertificate 163997 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv5857]) (by decide +kernel)
def pv163997 : PrimeValue := ⟨163997, pr163997⟩
private theorem pr164209 : PrimeCertificate 164209 :=
  certifyPrime (q := pv47) (ls := [pv2,pv3,pv11,pv311]) (by decide +kernel)
def pv164209 : PrimeValue := ⟨164209, pr164209⟩
private theorem pr164251 : PrimeCertificate 164251 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv73]) (by decide +kernel)
def pv164251 : PrimeValue := ⟨164251, pr164251⟩
private theorem pr164267 : PrimeCertificate 164267 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv3571]) (by decide +kernel)
def pv164267 : PrimeValue := ⟨164267, pr164267⟩
private theorem pr164291 : PrimeCertificate 164291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv2347]) (by decide +kernel)
def pv164291 : PrimeValue := ⟨164291, pr164291⟩
private theorem pr164377 : PrimeCertificate 164377 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv761]) (by decide +kernel)
def pv164377 : PrimeValue := ⟨164377, pr164377⟩
private theorem pr164503 : PrimeCertificate 164503 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv19,pv37]) (by decide +kernel)
def pv164503 : PrimeValue := ⟨164503, pr164503⟩
private theorem pr164599 : PrimeCertificate 164599 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv3919]) (by decide +kernel)
def pv164599 : PrimeValue := ⟨164599, pr164599⟩
private theorem pr164701 : PrimeCertificate 164701 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv61]) (by decide +kernel)
def pv164701 : PrimeValue := ⟨164701, pr164701⟩
private theorem pr164821 : PrimeCertificate 164821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv41,pv67]) (by decide +kernel)
def pv164821 : PrimeValue := ⟨164821, pr164821⟩
private theorem pr164893 : PrimeCertificate 164893 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv13,pv151]) (by decide +kernel)
def pv164893 : PrimeValue := ⟨164893, pr164893⟩
private theorem pr164963 : PrimeCertificate 164963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11783]) (by decide +kernel)
def pv164963 : PrimeValue := ⟨164963, pr164963⟩
private theorem pr165059 : PrimeCertificate 165059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv82529]) (by decide +kernel)
def pv165059 : PrimeValue := ⟨165059, pr165059⟩
private theorem pr165211 : PrimeCertificate 165211 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv5507]) (by decide +kernel)
def pv165211 : PrimeValue := ⟨165211, pr165211⟩
private theorem pr165349 : PrimeCertificate 165349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1531]) (by decide +kernel)
def pv165349 : PrimeValue := ⟨165349, pr165349⟩
private theorem pr165391 : PrimeCertificate 165391 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv37,pv149]) (by decide +kernel)
def pv165391 : PrimeValue := ⟨165391, pr165391⟩
private theorem pr165463 : PrimeCertificate 165463 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv23,pv109]) (by decide +kernel)
def pv165463 : PrimeValue := ⟨165463, pr165463⟩
private theorem pr165667 : PrimeCertificate 165667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv27611]) (by decide +kernel)
def pv165667 : PrimeValue := ⟨165667, pr165667⟩
private theorem pr165703 : PrimeCertificate 165703 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv27617]) (by decide +kernel)
def pv165703 : PrimeValue := ⟨165703, pr165703⟩
private theorem pr165709 : PrimeCertificate 165709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv4603]) (by decide +kernel)
def pv165709 : PrimeValue := ⟨165709, pr165709⟩
private theorem pr165799 : PrimeCertificate 165799 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv61,pv151]) (by decide +kernel)
def pv165799 : PrimeValue := ⟨165799, pr165799⟩
private theorem pr165883 : PrimeCertificate 165883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv27647]) (by decide +kernel)
def pv165883 : PrimeValue := ⟨165883, pr165883⟩
private theorem pr166099 : PrimeCertificate 166099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv31,pv47]) (by decide +kernel)
def pv166099 : PrimeValue := ⟨166099, pr166099⟩
private theorem pr166207 : PrimeCertificate 166207 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv27701]) (by decide +kernel)
def pv166207 : PrimeValue := ⟨166207, pr166207⟩
private theorem pr166363 : PrimeCertificate 166363 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv17,pv233]) (by decide +kernel)
def pv166363 : PrimeValue := ⟨166363, pr166363⟩
private theorem pr166417 : PrimeCertificate 166417 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3467]) (by decide +kernel)
def pv166417 : PrimeValue := ⟨166417, pr166417⟩
private theorem pr166601 : PrimeCertificate 166601 :=
  certifyPrime (q := pv47) (ls := [pv2,pv5,pv7,pv17]) (by decide +kernel)
def pv166601 : PrimeValue := ⟨166601, pr166601⟩
private theorem pr166603 : PrimeCertificate 166603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv27767]) (by decide +kernel)
def pv166603 : PrimeValue := ⟨166603, pr166603⟩
private theorem pr166631 : PrimeCertificate 166631 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv19,pv877]) (by decide +kernel)
def pv166631 : PrimeValue := ⟨166631, pr166631⟩
private theorem pr166703 : PrimeCertificate 166703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv4903]) (by decide +kernel)
def pv166703 : PrimeValue := ⟨166703, pr166703⟩
private theorem pr166741 : PrimeCertificate 166741 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv397]) (by decide +kernel)
def pv166741 : PrimeValue := ⟨166741, pr166741⟩
private theorem pr166849 : PrimeCertificate 166849 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv11,pv79]) (by decide +kernel)
def pv166849 : PrimeValue := ⟨166849, pr166849⟩
private theorem pr167033 : PrimeCertificate 167033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv20879]) (by decide +kernel)
def pv167033 : PrimeValue := ⟨167033, pr167033⟩
private theorem pr167077 : PrimeCertificate 167077 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv17]) (by decide +kernel)
def pv167077 : PrimeValue := ⟨167077, pr167077⟩
private theorem pr167107 : PrimeCertificate 167107 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv27851]) (by decide +kernel)
def pv167107 : PrimeValue := ⟨167107, pr167107⟩
private theorem pr167191 : PrimeCertificate 167191 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv5573]) (by decide +kernel)
def pv167191 : PrimeValue := ⟨167191, pr167191⟩
private theorem pr167197 : PrimeCertificate 167197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13933]) (by decide +kernel)
def pv167197 : PrimeValue := ⟨167197, pr167197⟩
private theorem pr167449 : PrimeCertificate 167449 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv6977]) (by decide +kernel)
def pv167449 : PrimeValue := ⟨167449, pr167449⟩
private theorem pr167521 : PrimeCertificate 167521 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv349]) (by decide +kernel)
def pv167521 : PrimeValue := ⟨167521, pr167521⟩
private theorem pr167543 : PrimeCertificate 167543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv4409]) (by decide +kernel)
def pv167543 : PrimeValue := ⟨167543, pr167543⟩
private theorem pr167899 : PrimeCertificate 167899 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv27983]) (by decide +kernel)
def pv167899 : PrimeValue := ⟨167899, pr167899⟩
private theorem pr168323 : PrimeCertificate 168323 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11,pv1093]) (by decide +kernel)
def pv168323 : PrimeValue := ⟨168323, pr168323⟩
private theorem pr168677 : PrimeCertificate 168677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv42169]) (by decide +kernel)
def pv168677 : PrimeValue := ⟨168677, pr168677⟩
private theorem pr169249 : PrimeCertificate 169249 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv41,pv43]) (by decide +kernel)
def pv169249 : PrimeValue := ⟨169249, pr169249⟩
private theorem pr169627 : PrimeCertificate 169627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv1663]) (by decide +kernel)
def pv169627 : PrimeValue := ⟨169627, pr169627⟩
private theorem pr169783 : PrimeCertificate 169783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv28297]) (by decide +kernel)
def pv169783 : PrimeValue := ⟨169783, pr169783⟩
private theorem pr169951 : PrimeCertificate 169951 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv103]) (by decide +kernel)
def pv169951 : PrimeValue := ⟨169951, pr169951⟩
private theorem pr170101 : PrimeCertificate 170101 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv170101 : PrimeValue := ⟨170101, pr170101⟩
private theorem pr170213 : PrimeCertificate 170213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv6079]) (by decide +kernel)
def pv170213 : PrimeValue := ⟨170213, pr170213⟩
private theorem pr170341 : PrimeCertificate 170341 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv17,pv167]) (by decide +kernel)
def pv170341 : PrimeValue := ⟨170341, pr170341⟩
private theorem pr170413 : PrimeCertificate 170413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv1291]) (by decide +kernel)
def pv170413 : PrimeValue := ⟨170413, pr170413⟩
private theorem pr170749 : PrimeCertificate 170749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv31]) (by decide +kernel)
def pv170749 : PrimeValue := ⟨170749, pr170749⟩
private theorem pr170759 : PrimeCertificate 170759 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv12197]) (by decide +kernel)
def pv170759 : PrimeValue := ⟨170759, pr170759⟩
private theorem pr170773 : PrimeCertificate 170773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv19,pv107]) (by decide +kernel)
def pv170773 : PrimeValue := ⟨170773, pr170773⟩
private theorem pr170851 : PrimeCertificate 170851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv67]) (by decide +kernel)
def pv170851 : PrimeValue := ⟨170851, pr170851⟩
private theorem pr171427 : PrimeCertificate 171427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv28571]) (by decide +kernel)
def pv171427 : PrimeValue := ⟨171427, pr171427⟩
private theorem pr171469 : PrimeCertificate 171469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv433]) (by decide +kernel)
def pv171469 : PrimeValue := ⟨171469, pr171469⟩
private theorem pr171559 : PrimeCertificate 171559 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv353]) (by decide +kernel)
def pv171559 : PrimeValue := ⟨171559, pr171559⟩
private theorem pr171713 : PrimeCertificate 171713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2683]) (by decide +kernel)
def pv171713 : PrimeValue := ⟨171713, pr171713⟩
private theorem pr171733 : PrimeCertificate 171733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv1301]) (by decide +kernel)
def pv171733 : PrimeValue := ⟨171733, pr171733⟩
private theorem pr171947 : PrimeCertificate 171947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv149,pv577]) (by decide +kernel)
def pv171947 : PrimeValue := ⟨171947, pr171947⟩
private theorem pr172153 : PrimeCertificate 172153 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv797]) (by decide +kernel)
def pv172153 : PrimeValue := ⟨172153, pr172153⟩
private theorem pr172561 : PrimeCertificate 172561 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv719]) (by decide +kernel)
def pv172561 : PrimeValue := ⟨172561, pr172561⟩
private theorem pr172607 : PrimeCertificate 172607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv12329]) (by decide +kernel)
def pv172607 : PrimeValue := ⟨172607, pr172607⟩
private theorem pr172643 : PrimeCertificate 172643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv2333]) (by decide +kernel)
def pv172643 : PrimeValue := ⟨172643, pr172643⟩
private theorem pr172709 : PrimeCertificate 172709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43177]) (by decide +kernel)
def pv172709 : PrimeValue := ⟨172709, pr172709⟩
private theorem pr173023 : PrimeCertificate 173023 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv28837]) (by decide +kernel)
def pv173023 : PrimeValue := ⟨173023, pr173023⟩
private theorem pr173207 : PrimeCertificate 173207 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv7873]) (by decide +kernel)
def pv173207 : PrimeValue := ⟨173207, pr173207⟩
private theorem pr173347 : PrimeCertificate 173347 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv167,pv173]) (by decide +kernel)
def pv173347 : PrimeValue := ⟨173347, pr173347⟩
private theorem pr173561 : PrimeCertificate 173561 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv4339]) (by decide +kernel)
def pv173561 : PrimeValue := ⟨173561, pr173561⟩
private theorem pr173599 : PrimeCertificate 173599 :=
  certifyPrime (q := pv59) (ls := [pv2,pv3,pv28933]) (by decide +kernel)
def pv173599 : PrimeValue := ⟨173599, pr173599⟩
private theorem pr173617 : PrimeCertificate 173617 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3617]) (by decide +kernel)
def pv173617 : PrimeValue := ⟨173617, pr173617⟩
private theorem pr173659 : PrimeCertificate 173659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv103,pv281]) (by decide +kernel)
def pv173659 : PrimeValue := ⟨173659, pr173659⟩
private theorem pr173713 : PrimeCertificate 173713 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv47]) (by decide +kernel)
def pv173713 : PrimeValue := ⟨173713, pr173713⟩
private theorem pr174067 : PrimeCertificate 174067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv67,pv433]) (by decide +kernel)
def pv174067 : PrimeValue := ⟨174067, pr174067⟩
private theorem pr174077 : PrimeCertificate 174077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv6217]) (by decide +kernel)
def pv174077 : PrimeValue := ⟨174077, pr174077⟩
private theorem pr174299 : PrimeCertificate 174299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv87149]) (by decide +kernel)
def pv174299 : PrimeValue := ⟨174299, pr174299⟩
private theorem pr174571 : PrimeCertificate 174571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv23]) (by decide +kernel)
def pv174571 : PrimeValue := ⟨174571, pr174571⟩
private theorem pr174631 : PrimeCertificate 174631 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv5821]) (by decide +kernel)
def pv174631 : PrimeValue := ⟨174631, pr174631⟩
private theorem pr174767 : PrimeCertificate 174767 :=
  certifyPrime (q := pv5) (ls := [pv2,pv87383]) (by decide +kernel)
def pv174767 : PrimeValue := ⟨174767, pr174767⟩
private theorem pr174929 : PrimeCertificate 174929 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv29]) (by decide +kernel)
def pv174929 : PrimeValue := ⟨174929, pr174929⟩
private theorem pr175003 : PrimeCertificate 175003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29167]) (by decide +kernel)
def pv175003 : PrimeValue := ⟨175003, pr175003⟩
private theorem pr175067 : PrimeCertificate 175067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv19,pv271]) (by decide +kernel)
def pv175067 : PrimeValue := ⟨175067, pr175067⟩
private theorem pr175333 : PrimeCertificate 175333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv769]) (by decide +kernel)
def pv175333 : PrimeValue := ⟨175333, pr175333⟩
private theorem pr175493 : PrimeCertificate 175493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv601]) (by decide +kernel)
def pv175493 : PrimeValue := ⟨175493, pr175493⟩
private theorem pr175499 : PrimeCertificate 175499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv1867]) (by decide +kernel)
def pv175499 : PrimeValue := ⟨175499, pr175499⟩
private theorem pr175649 : PrimeCertificate 175649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv499]) (by decide +kernel)
def pv175649 : PrimeValue := ⟨175649, pr175649⟩
private theorem pr175663 : PrimeCertificate 175663 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv3253]) (by decide +kernel)
def pv175663 : PrimeValue := ⟨175663, pr175663⟩
private theorem pr175757 : PrimeCertificate 175757 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv6277]) (by decide +kernel)
def pv175757 : PrimeValue := ⟨175757, pr175757⟩
private theorem pr175783 : PrimeCertificate 175783 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29297]) (by decide +kernel)
def pv175783 : PrimeValue := ⟨175783, pr175783⟩
private theorem pr175859 : PrimeCertificate 175859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv3823]) (by decide +kernel)
def pv175859 : PrimeValue := ⟨175859, pr175859⟩
private theorem pr175937 : PrimeCertificate 175937 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2749]) (by decide +kernel)
def pv175937 : PrimeValue := ⟨175937, pr175937⟩
private theorem pr175949 : PrimeCertificate 175949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43987]) (by decide +kernel)
def pv175949 : PrimeValue := ⟨175949, pr175949⟩
private theorem pr176023 : PrimeCertificate 176023 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv11,pv127]) (by decide +kernel)
def pv176023 : PrimeValue := ⟨176023, pr176023⟩
private theorem pr176153 : PrimeCertificate 176153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv97,pv227]) (by decide +kernel)
def pv176153 : PrimeValue := ⟨176153, pr176153⟩
private theorem pr176179 : PrimeCertificate 176179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29363]) (by decide +kernel)
def pv176179 : PrimeValue := ⟨176179, pr176179⟩
private theorem pr176207 : PrimeCertificate 176207 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv4637]) (by decide +kernel)
def pv176207 : PrimeValue := ⟨176207, pr176207⟩
private theorem pr176333 : PrimeCertificate 176333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv3391]) (by decide +kernel)
def pv176333 : PrimeValue := ⟨176333, pr176333⟩
private theorem pr176419 : PrimeCertificate 176419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv176419 : PrimeValue := ⟨176419, pr176419⟩
private theorem pr176531 : PrimeCertificate 176531 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv127,pv139]) (by decide +kernel)
def pv176531 : PrimeValue := ⟨176531, pr176531⟩
private theorem pr176651 : PrimeCertificate 176651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv3533]) (by decide +kernel)
def pv176651 : PrimeValue := ⟨176651, pr176651⟩
private theorem pr176741 : PrimeCertificate 176741 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv8837]) (by decide +kernel)
def pv176741 : PrimeValue := ⟨176741, pr176741⟩
private theorem pr176899 : PrimeCertificate 176899 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29483]) (by decide +kernel)
def pv176899 : PrimeValue := ⟨176899, pr176899⟩
private theorem pr176927 : PrimeCertificate 176927 :=
  certifyPrime (q := pv5) (ls := [pv2,pv88463]) (by decide +kernel)
def pv176927 : PrimeValue := ⟨176927, pr176927⟩
private theorem pr177283 : PrimeCertificate 177283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv67]) (by decide +kernel)
def pv177283 : PrimeValue := ⟨177283, pr177283⟩
private theorem pr177383 : PrimeCertificate 177383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv31,pv2861]) (by decide +kernel)
def pv177383 : PrimeValue := ⟨177383, pr177383⟩
private theorem pr177433 : PrimeCertificate 177433 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7393]) (by decide +kernel)
def pv177433 : PrimeValue := ⟨177433, pr177433⟩
private theorem pr177493 : PrimeCertificate 177493 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv2113]) (by decide +kernel)
def pv177493 : PrimeValue := ⟨177493, pr177493⟩
private theorem pr177533 : PrimeCertificate 177533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv44383]) (by decide +kernel)
def pv177533 : PrimeValue := ⟨177533, pr177533⟩
private theorem pr177691 : PrimeCertificate 177691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv5923]) (by decide +kernel)
def pv177691 : PrimeValue := ⟨177691, pr177691⟩
private theorem pr177763 : PrimeCertificate 177763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv43,pv53]) (by decide +kernel)
def pv177763 : PrimeValue := ⟨177763, pr177763⟩
private theorem pr177889 : PrimeCertificate 177889 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv109]) (by decide +kernel)
def pv177889 : PrimeValue := ⟨177889, pr177889⟩
private theorem pr177917 : PrimeCertificate 177917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv2341]) (by decide +kernel)
def pv177917 : PrimeValue := ⟨177917, pr177917⟩
private theorem pr177943 : PrimeCertificate 177943 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv47,pv631]) (by decide +kernel)
def pv177943 : PrimeValue := ⟨177943, pr177943⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
