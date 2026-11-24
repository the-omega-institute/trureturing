/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table082
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table082.pv280541
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table009
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table012
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table019
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table050

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr280541 : Nat.Prime 280541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv83]) (by decide +kernel)
def pv280541 : PrimeValue := ⟨280541, pr280541⟩
private theorem pr280547 : Nat.Prime 280547 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv29,pv691]) (by decide +kernel)
def pv280547 : PrimeValue := ⟨280547, pr280547⟩
private theorem pr280549 : Nat.Prime 280549 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7793]) (by decide +kernel)
def pv280549 : PrimeValue := ⟨280549, pr280549⟩
private theorem pr280589 : Nat.Prime 280589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv911]) (by decide +kernel)
def pv280589 : PrimeValue := ⟨280589, pr280589⟩
private theorem pr280591 : Nat.Prime 280591 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv47,pv199]) (by decide +kernel)
def pv280591 : PrimeValue := ⟨280591, pr280591⟩
private theorem pr280597 : Nat.Prime 280597 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv67,pv349]) (by decide +kernel)
def pv280597 : PrimeValue := ⟨280597, pr280597⟩
private theorem pr280603 : Nat.Prime 280603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv131]) (by decide +kernel)
def pv280603 : PrimeValue := ⟨280603, pr280603⟩
private theorem pr280613 : Nat.Prime 280613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv73]) (by decide +kernel)
def pv280613 : PrimeValue := ⟨280613, pr280613⟩
private theorem pr280639 : Nat.Prime 280639 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5197]) (by decide +kernel)
def pv280639 : PrimeValue := ⟨280639, pr280639⟩
private theorem pr280673 : Nat.Prime 280673 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv179]) (by decide +kernel)
def pv280673 : PrimeValue := ⟨280673, pr280673⟩
private theorem pr280697 : Nat.Prime 280697 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv2699]) (by decide +kernel)
def pv280697 : PrimeValue := ⟨280697, pr280697⟩
private theorem pr280711 : Nat.Prime 280711 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv3119]) (by decide +kernel)
def pv280711 : PrimeValue := ⟨280711, pr280711⟩
private theorem pr280717 : Nat.Prime 280717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv149,pv157]) (by decide +kernel)
def pv280717 : PrimeValue := ⟨280717, pr280717⟩
private theorem pr280759 : Nat.Prime 280759 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv73,pv641]) (by decide +kernel)
def pv280759 : PrimeValue := ⟨280759, pr280759⟩
private theorem pr280811 : Nat.Prime 280811 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv28081]) (by decide +kernel)
def pv280811 : PrimeValue := ⟨280811, pr280811⟩
private theorem pr280817 : Nat.Prime 280817 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17551]) (by decide +kernel)
def pv280817 : PrimeValue := ⟨280817, pr280817⟩
private theorem pr280837 : Nat.Prime 280837 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv269]) (by decide +kernel)
def pv280837 : PrimeValue := ⟨280837, pr280837⟩
private theorem pr280843 : Nat.Prime 280843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv46807]) (by decide +kernel)
def pv280843 : PrimeValue := ⟨280843, pr280843⟩
private theorem pr280859 : Nat.Prime 280859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv389]) (by decide +kernel)
def pv280859 : PrimeValue := ⟨280859, pr280859⟩
private theorem pr280871 : Nat.Prime 280871 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv28087]) (by decide +kernel)
def pv280871 : PrimeValue := ⟨280871, pr280871⟩
private theorem pr280879 : Nat.Prime 280879 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv277]) (by decide +kernel)
def pv280879 : PrimeValue := ⟨280879, pr280879⟩
private theorem pr280883 : Nat.Prime 280883 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv20063]) (by decide +kernel)
def pv280883 : PrimeValue := ⟨280883, pr280883⟩
private theorem pr280897 : Nat.Prime 280897 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv19]) (by decide +kernel)
def pv280897 : PrimeValue := ⟨280897, pr280897⟩
private theorem pr280909 : Nat.Prime 280909 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv17]) (by decide +kernel)
def pv280909 : PrimeValue := ⟨280909, pr280909⟩
private theorem pr280913 : Nat.Prime 280913 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv97,pv181]) (by decide +kernel)
def pv280913 : PrimeValue := ⟨280913, pr280913⟩
private theorem pr280921 : Nat.Prime 280921 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv2341]) (by decide +kernel)
def pv280921 : PrimeValue := ⟨280921, pr280921⟩
private theorem pr280927 : Nat.Prime 280927 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv15607]) (by decide +kernel)
def pv280927 : PrimeValue := ⟨280927, pr280927⟩
private theorem pr280933 : Nat.Prime 280933 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv41,pv571]) (by decide +kernel)
def pv280933 : PrimeValue := ⟨280933, pr280933⟩
private theorem pr280963 : Nat.Prime 280963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv43]) (by decide +kernel)
def pv280963 : PrimeValue := ⟨280963, pr280963⟩
private theorem pr280967 : Nat.Prime 280967 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv47,pv61]) (by decide +kernel)
def pv280967 : PrimeValue := ⟨280967, pr280967⟩
private theorem pr280997 : Nat.Prime 280997 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv70249]) (by decide +kernel)
def pv280997 : PrimeValue := ⟨280997, pr280997⟩
private theorem pr281023 : Nat.Prime 281023 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv6691]) (by decide +kernel)
def pv281023 : PrimeValue := ⟨281023, pr281023⟩
private theorem pr281053 : Nat.Prime 281053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv211]) (by decide +kernel)
def pv281053 : PrimeValue := ⟨281053, pr281053⟩
private theorem pr281063 : Nat.Prime 281063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv89,pv1579]) (by decide +kernel)
def pv281063 : PrimeValue := ⟨281063, pr281063⟩
private theorem pr281117 : Nat.Prime 281117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv6389]) (by decide +kernel)
def pv281117 : PrimeValue := ⟨281117, pr281117⟩
private theorem pr281131 : Nat.Prime 281131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv9371]) (by decide +kernel)
def pv281131 : PrimeValue := ⟨281131, pr281131⟩
private theorem pr281153 : Nat.Prime 281153 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv191]) (by decide +kernel)
def pv281153 : PrimeValue := ⟨281153, pr281153⟩
private theorem pr281233 : Nat.Prime 281233 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv31]) (by decide +kernel)
def pv281233 : PrimeValue := ⟨281233, pr281233⟩
private theorem pr281251 : Nat.Prime 281251 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv281251 : PrimeValue := ⟨281251, pr281251⟩
private theorem pr281279 : Nat.Prime 281279 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv140639]) (by decide +kernel)
def pv281279 : PrimeValue := ⟨281279, pr281279⟩
private theorem pr281297 : Nat.Prime 281297 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17581]) (by decide +kernel)
def pv281297 : PrimeValue := ⟨281297, pr281297⟩
private theorem pr281317 : Nat.Prime 281317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv197]) (by decide +kernel)
def pv281317 : PrimeValue := ⟨281317, pr281317⟩
private theorem pr281327 : Nat.Prime 281327 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv140663]) (by decide +kernel)
def pv281327 : PrimeValue := ⟨281327, pr281327⟩
private theorem pr281339 : Nat.Prime 281339 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv163,pv863]) (by decide +kernel)
def pv281339 : PrimeValue := ⟨281339, pr281339⟩
private theorem pr281357 : Nat.Prime 281357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv2269]) (by decide +kernel)
def pv281357 : PrimeValue := ⟨281357, pr281357⟩
private theorem pr281363 : Nat.Prime 281363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv140681]) (by decide +kernel)
def pv281363 : PrimeValue := ⟨281363, pr281363⟩
private theorem pr281381 : Nat.Prime 281381 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv1279]) (by decide +kernel)
def pv281381 : PrimeValue := ⟨281381, pr281381⟩
private theorem pr281419 : Nat.Prime 281419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv31,pv89]) (by decide +kernel)
def pv281419 : PrimeValue := ⟨281419, pr281419⟩
private theorem pr281431 : Nat.Prime 281431 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv53,pv59]) (by decide +kernel)
def pv281431 : PrimeValue := ⟨281431, pr281431⟩
private theorem pr281509 : Nat.Prime 281509 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv23459]) (by decide +kernel)
def pv281509 : PrimeValue := ⟨281509, pr281509⟩
private theorem pr281527 : Nat.Prime 281527 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv6703]) (by decide +kernel)
def pv281527 : PrimeValue := ⟨281527, pr281527⟩
private theorem pr281531 : Nat.Prime 281531 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv47,pv599]) (by decide +kernel)
def pv281531 : PrimeValue := ⟨281531, pr281531⟩
private theorem pr281549 : Nat.Prime 281549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv59,pv1193]) (by decide +kernel)
def pv281549 : PrimeValue := ⟨281549, pr281549⟩
private theorem pr281557 : Nat.Prime 281557 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv79]) (by decide +kernel)
def pv281557 : PrimeValue := ⟨281557, pr281557⟩
private theorem pr281563 : Nat.Prime 281563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv167,pv281]) (by decide +kernel)
def pv281563 : PrimeValue := ⟨281563, pr281563⟩
private theorem pr281609 : Nat.Prime 281609 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv35201]) (by decide +kernel)
def pv281609 : PrimeValue := ⟨281609, pr281609⟩
private theorem pr281623 : Nat.Prime 281623 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv17,pv251]) (by decide +kernel)
def pv281623 : PrimeValue := ⟨281623, pr281623⟩
private theorem pr281627 : Nat.Prime 281627 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv140813]) (by decide +kernel)
def pv281627 : PrimeValue := ⟨281627, pr281627⟩
private theorem pr281641 : Nat.Prime 281641 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv2347]) (by decide +kernel)
def pv281641 : PrimeValue := ⟨281641, pr281641⟩
private theorem pr281651 : Nat.Prime 281651 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv43,pv131]) (by decide +kernel)
def pv281651 : PrimeValue := ⟨281651, pr281651⟩
private theorem pr281653 : Nat.Prime 281653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv479]) (by decide +kernel)
def pv281653 : PrimeValue := ⟨281653, pr281653⟩
private theorem pr281663 : Nat.Prime 281663 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv140831]) (by decide +kernel)
def pv281663 : PrimeValue := ⟨281663, pr281663⟩
private theorem pr281669 : Nat.Prime 281669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv67,pv1051]) (by decide +kernel)
def pv281669 : PrimeValue := ⟨281669, pr281669⟩
private theorem pr281683 : Nat.Prime 281683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv15649]) (by decide +kernel)
def pv281683 : PrimeValue := ⟨281683, pr281683⟩
private theorem pr281717 : Nat.Prime 281717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv70429]) (by decide +kernel)
def pv281717 : PrimeValue := ⟨281717, pr281717⟩
private theorem pr281737 : Nat.Prime 281737 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv7,pv13,pv43]) (by decide +kernel)
def pv281737 : PrimeValue := ⟨281737, pr281737⟩
private theorem pr281747 : Nat.Prime 281747 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv179,pv787]) (by decide +kernel)
def pv281747 : PrimeValue := ⟨281747, pr281747⟩
private theorem pr281767 : Nat.Prime 281767 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv151,pv311]) (by decide +kernel)
def pv281767 : PrimeValue := ⟨281767, pr281767⟩
private theorem pr281791 : Nat.Prime 281791 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv31,pv101]) (by decide +kernel)
def pv281791 : PrimeValue := ⟨281791, pr281791⟩
private theorem pr281797 : Nat.Prime 281797 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23,pv1021]) (by decide +kernel)
def pv281797 : PrimeValue := ⟨281797, pr281797⟩
private theorem pr281807 : Nat.Prime 281807 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv20129]) (by decide +kernel)
def pv281807 : PrimeValue := ⟨281807, pr281807⟩
private theorem pr281833 : Nat.Prime 281833 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11743]) (by decide +kernel)
def pv281833 : PrimeValue := ⟨281833, pr281833⟩
private theorem pr281837 : Nat.Prime 281837 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv70459]) (by decide +kernel)
def pv281837 : PrimeValue := ⟨281837, pr281837⟩
private theorem pr281839 : Nat.Prime 281839 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv107,pv439]) (by decide +kernel)
def pv281839 : PrimeValue := ⟨281839, pr281839⟩
private theorem pr281849 : Nat.Prime 281849 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv719]) (by decide +kernel)
def pv281849 : PrimeValue := ⟨281849, pr281849⟩
private theorem pr281867 : Nat.Prime 281867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv37,pv293]) (by decide +kernel)
def pv281867 : PrimeValue := ⟨281867, pr281867⟩
private theorem pr281893 : Nat.Prime 281893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv139]) (by decide +kernel)
def pv281893 : PrimeValue := ⟨281893, pr281893⟩
private theorem pr281921 : Nat.Prime 281921 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv881]) (by decide +kernel)
def pv281921 : PrimeValue := ⟨281921, pr281921⟩
private theorem pr281923 : Nat.Prime 281923 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv19,pv2473]) (by decide +kernel)
def pv281923 : PrimeValue := ⟨281923, pr281923⟩
private theorem pr281947 : Nat.Prime 281947 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv137]) (by decide +kernel)
def pv281947 : PrimeValue := ⟨281947, pr281947⟩
private theorem pr281959 : Nat.Prime 281959 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv46993]) (by decide +kernel)
def pv281959 : PrimeValue := ⟨281959, pr281959⟩
private theorem pr281971 : Nat.Prime 281971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv241]) (by decide +kernel)
def pv281971 : PrimeValue := ⟨281971, pr281971⟩
private theorem pr281989 : Nat.Prime 281989 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv373]) (by decide +kernel)
def pv281989 : PrimeValue := ⟨281989, pr281989⟩
private theorem pr281993 : Nat.Prime 281993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv101,pv349]) (by decide +kernel)
def pv281993 : PrimeValue := ⟨281993, pr281993⟩
private theorem pr282011 : Nat.Prime 282011 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv28201]) (by decide +kernel)
def pv282011 : PrimeValue := ⟨282011, pr282011⟩
private theorem pr282053 : Nat.Prime 282053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv107,pv659]) (by decide +kernel)
def pv282053 : PrimeValue := ⟨282053, pr282053⟩
private theorem pr282059 : Nat.Prime 282059 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv20147]) (by decide +kernel)
def pv282059 : PrimeValue := ⟨282059, pr282059⟩
private theorem pr282089 : Nat.Prime 282089 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv37,pv953]) (by decide +kernel)
def pv282089 : PrimeValue := ⟨282089, pr282089⟩
private theorem pr282097 : Nat.Prime 282097 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv653]) (by decide +kernel)
def pv282097 : PrimeValue := ⟨282097, pr282097⟩
private theorem pr282127 : Nat.Prime 282127 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv3617]) (by decide +kernel)
def pv282127 : PrimeValue := ⟨282127, pr282127⟩
private theorem pr282143 : Nat.Prime 282143 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv2879]) (by decide +kernel)
def pv282143 : PrimeValue := ⟨282143, pr282143⟩
private theorem pr282157 : Nat.Prime 282157 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv3359]) (by decide +kernel)
def pv282157 : PrimeValue := ⟨282157, pr282157⟩
private theorem pr282221 : Nat.Prime 282221 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv103,pv137]) (by decide +kernel)
def pv282221 : PrimeValue := ⟨282221, pr282221⟩
private theorem pr282229 : Nat.Prime 282229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv811]) (by decide +kernel)
def pv282229 : PrimeValue := ⟨282229, pr282229⟩
private theorem pr282241 : Nat.Prime 282241 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv282241 : PrimeValue := ⟨282241, pr282241⟩
private theorem pr282253 : Nat.Prime 282253 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv43,pv547]) (by decide +kernel)
def pv282253 : PrimeValue := ⟨282253, pr282253⟩
private theorem pr282307 : Nat.Prime 282307 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv47051]) (by decide +kernel)
def pv282307 : PrimeValue := ⟨282307, pr282307⟩
private theorem pr282311 : Nat.Prime 282311 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv37,pv109]) (by decide +kernel)
def pv282311 : PrimeValue := ⟨282311, pr282311⟩
private theorem pr282313 : Nat.Prime 282313 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv1307]) (by decide +kernel)
def pv282313 : PrimeValue := ⟨282313, pr282313⟩
private theorem pr282377 : Nat.Prime 282377 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv47,pv751]) (by decide +kernel)
def pv282377 : PrimeValue := ⟨282377, pr282377⟩
private theorem pr282389 : Nat.Prime 282389 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv227,pv311]) (by decide +kernel)
def pv282389 : PrimeValue := ⟨282389, pr282389⟩
private theorem pr282391 : Nat.Prime 282391 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv9413]) (by decide +kernel)
def pv282391 : PrimeValue := ⟨282391, pr282391⟩
private theorem pr282407 : Nat.Prime 282407 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv337,pv419]) (by decide +kernel)
def pv282407 : PrimeValue := ⟨282407, pr282407⟩
private theorem pr282413 : Nat.Prime 282413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv5431]) (by decide +kernel)
def pv282413 : PrimeValue := ⟨282413, pr282413⟩
private theorem pr282439 : Nat.Prime 282439 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv17,pv71]) (by decide +kernel)
def pv282439 : PrimeValue := ⟨282439, pr282439⟩
private theorem pr282461 : Nat.Prime 282461 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv29,pv487]) (by decide +kernel)
def pv282461 : PrimeValue := ⟨282461, pr282461⟩
private theorem pr282481 : Nat.Prime 282481 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv11,pv107]) (by decide +kernel)
def pv282481 : PrimeValue := ⟨282481, pr282481⟩
private theorem pr282559 : Nat.Prime 282559 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv47093]) (by decide +kernel)
def pv282559 : PrimeValue := ⟨282559, pr282559⟩
private theorem pr282563 : Nat.Prime 282563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv20183]) (by decide +kernel)
def pv282563 : PrimeValue := ⟨282563, pr282563⟩
private theorem pr282589 : Nat.Prime 282589 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv23549]) (by decide +kernel)
def pv282589 : PrimeValue := ⟨282589, pr282589⟩
private theorem pr282599 : Nat.Prime 282599 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv101,pv1399]) (by decide +kernel)
def pv282599 : PrimeValue := ⟨282599, pr282599⟩
private theorem pr282661 : Nat.Prime 282661 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv673]) (by decide +kernel)
def pv282661 : PrimeValue := ⟨282661, pr282661⟩
private theorem pr282671 : Nat.Prime 282671 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv23,pv1229]) (by decide +kernel)
def pv282671 : PrimeValue := ⟨282671, pr282671⟩
private theorem pr282683 : Nat.Prime 282683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv43,pv173]) (by decide +kernel)
def pv282683 : PrimeValue := ⟨282683, pr282683⟩
private theorem pr282703 : Nat.Prime 282703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv53,pv127]) (by decide +kernel)
def pv282703 : PrimeValue := ⟨282703, pr282703⟩
private theorem pr282713 : Nat.Prime 282713 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv35339]) (by decide +kernel)
def pv282713 : PrimeValue := ⟨282713, pr282713⟩
private theorem pr282769 : Nat.Prime 282769 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv43,pv137]) (by decide +kernel)
def pv282769 : PrimeValue := ⟨282769, pr282769⟩
private theorem pr282833 : Nat.Prime 282833 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv1607]) (by decide +kernel)
def pv282833 : PrimeValue := ⟨282833, pr282833⟩
private theorem pr282847 : Nat.Prime 282847 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv47,pv59]) (by decide +kernel)
def pv282847 : PrimeValue := ⟨282847, pr282847⟩
private theorem pr282851 : Nat.Prime 282851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv5657]) (by decide +kernel)
def pv282851 : PrimeValue := ⟨282851, pr282851⟩
private theorem pr282869 : Nat.Prime 282869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv70717]) (by decide +kernel)
def pv282869 : PrimeValue := ⟨282869, pr282869⟩
private theorem pr282881 : Nat.Prime 282881 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv17]) (by decide +kernel)
def pv282881 : PrimeValue := ⟨282881, pr282881⟩
private theorem pr282907 : Nat.Prime 282907 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv31]) (by decide +kernel)
def pv282907 : PrimeValue := ⟨282907, pr282907⟩
private theorem pr282913 : Nat.Prime 282913 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv421]) (by decide +kernel)
def pv282913 : PrimeValue := ⟨282913, pr282913⟩
private theorem pr282917 : Nat.Prime 282917 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv70729]) (by decide +kernel)
def pv282917 : PrimeValue := ⟨282917, pr282917⟩
private theorem pr282959 : Nat.Prime 282959 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv13,pv10883]) (by decide +kernel)
def pv282959 : PrimeValue := ⟨282959, pr282959⟩
private theorem pr282977 : Nat.Prime 282977 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv37,pv239]) (by decide +kernel)
def pv282977 : PrimeValue := ⟨282977, pr282977⟩
private theorem pr282991 : Nat.Prime 282991 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv9433]) (by decide +kernel)
def pv282991 : PrimeValue := ⟨282991, pr282991⟩
private theorem pr283001 : Nat.Prime 283001 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv283]) (by decide +kernel)
def pv283001 : PrimeValue := ⟨283001, pr283001⟩
private theorem pr283007 : Nat.Prime 283007 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv71,pv1993]) (by decide +kernel)
def pv283007 : PrimeValue := ⟨283007, pr283007⟩
private theorem pr283051 : Nat.Prime 283051 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv17,pv37]) (by decide +kernel)
def pv283051 : PrimeValue := ⟨283051, pr283051⟩
private theorem pr283093 : Nat.Prime 283093 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv31,pv761]) (by decide +kernel)
def pv283093 : PrimeValue := ⟨283093, pr283093⟩
private theorem pr283097 : Nat.Prime 283097 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv3217]) (by decide +kernel)
def pv283097 : PrimeValue := ⟨283097, pr283097⟩
private theorem pr283121 : Nat.Prime 283121 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv3539]) (by decide +kernel)
def pv283121 : PrimeValue := ⟨283121, pr283121⟩
private theorem pr283133 : Nat.Prime 283133 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv70783]) (by decide +kernel)
def pv283133 : PrimeValue := ⟨283133, pr283133⟩
private theorem pr283193 : Nat.Prime 283193 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv13,pv389]) (by decide +kernel)
def pv283193 : PrimeValue := ⟨283193, pr283193⟩
private theorem pr283277 : Nat.Prime 283277 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv67,pv151]) (by decide +kernel)
def pv283277 : PrimeValue := ⟨283277, pr283277⟩
private theorem pr283303 : Nat.Prime 283303 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv15739]) (by decide +kernel)
def pv283303 : PrimeValue := ⟨283303, pr283303⟩
private theorem pr283369 : Nat.Prime 283369 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv11807]) (by decide +kernel)
def pv283369 : PrimeValue := ⟨283369, pr283369⟩
private theorem pr283397 : Nat.Prime 283397 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv70849]) (by decide +kernel)
def pv283397 : PrimeValue := ⟨283397, pr283397⟩
private theorem pr283447 : Nat.Prime 283447 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29,pv181]) (by decide +kernel)
def pv283447 : PrimeValue := ⟨283447, pr283447⟩
private theorem pr283463 : Nat.Prime 283463 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv141731]) (by decide +kernel)
def pv283463 : PrimeValue := ⟨283463, pr283463⟩
private theorem pr283489 : Nat.Prime 283489 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv2953]) (by decide +kernel)
def pv283489 : PrimeValue := ⟨283489, pr283489⟩
private theorem pr283501 : Nat.Prime 283501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv283501 : PrimeValue := ⟨283501, pr283501⟩
private theorem pr283553 : Nat.Prime 283553 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv8861]) (by decide +kernel)
def pv283553 : PrimeValue := ⟨283553, pr283553⟩
private theorem pr283571 : Nat.Prime 283571 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv4051]) (by decide +kernel)
def pv283571 : PrimeValue := ⟨283571, pr283571⟩
private theorem pr283573 : Nat.Prime 283573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7877]) (by decide +kernel)
def pv283573 : PrimeValue := ⟨283573, pr283573⟩
private theorem pr283601 : Nat.Prime 283601 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv709]) (by decide +kernel)
def pv283601 : PrimeValue := ⟨283601, pr283601⟩
private theorem pr283607 : Nat.Prime 283607 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv141803]) (by decide +kernel)
def pv283607 : PrimeValue := ⟨283607, pr283607⟩
private theorem pr283609 : Nat.Prime 283609 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv13,pv101]) (by decide +kernel)
def pv283609 : PrimeValue := ⟨283609, pr283609⟩
private theorem pr283631 : Nat.Prime 283631 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv113,pv251]) (by decide +kernel)
def pv283631 : PrimeValue := ⟨283631, pr283631⟩
private theorem pr283637 : Nat.Prime 283637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv3083]) (by decide +kernel)
def pv283637 : PrimeValue := ⟨283637, pr283637⟩
private theorem pr283639 : Nat.Prime 283639 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv41,pv1153]) (by decide +kernel)
def pv283639 : PrimeValue := ⟨283639, pr283639⟩
private theorem pr283721 : Nat.Prime 283721 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv41,pv173]) (by decide +kernel)
def pv283721 : PrimeValue := ⟨283721, pr283721⟩
private theorem pr283741 : Nat.Prime 283741 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv4729]) (by decide +kernel)
def pv283741 : PrimeValue := ⟨283741, pr283741⟩
private theorem pr283763 : Nat.Prime 283763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53,pv2677]) (by decide +kernel)
def pv283763 : PrimeValue := ⟨283763, pr283763⟩
private theorem pr283769 : Nat.Prime 283769 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv79,pv449]) (by decide +kernel)
def pv283769 : PrimeValue := ⟨283769, pr283769⟩
private theorem pr283771 : Nat.Prime 283771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1051]) (by decide +kernel)
def pv283771 : PrimeValue := ⟨283771, pr283771⟩
private theorem pr283799 : Nat.Prime 283799 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv17,pv491]) (by decide +kernel)
def pv283799 : PrimeValue := ⟨283799, pr283799⟩
private theorem pr283807 : Nat.Prime 283807 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv15767]) (by decide +kernel)
def pv283807 : PrimeValue := ⟨283807, pr283807⟩
private theorem pr283813 : Nat.Prime 283813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv67,pv353]) (by decide +kernel)
def pv283813 : PrimeValue := ⟨283813, pr283813⟩
private theorem pr283817 : Nat.Prime 283817 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv2729]) (by decide +kernel)
def pv283817 : PrimeValue := ⟨283817, pr283817⟩
private theorem pr283831 : Nat.Prime 283831 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv9461]) (by decide +kernel)
def pv283831 : PrimeValue := ⟨283831, pr283831⟩
private theorem pr283859 : Nat.Prime 283859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv71,pv1999]) (by decide +kernel)
def pv283859 : PrimeValue := ⟨283859, pr283859⟩
private theorem pr283861 : Nat.Prime 283861 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv19,pv83]) (by decide +kernel)
def pv283861 : PrimeValue := ⟨283861, pr283861⟩
private theorem pr283937 : Nat.Prime 283937 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv467]) (by decide +kernel)
def pv283937 : PrimeValue := ⟨283937, pr283937⟩
private theorem pr283949 : Nat.Prime 283949 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv10141]) (by decide +kernel)
def pv283949 : PrimeValue := ⟨283949, pr283949⟩
private theorem pr283961 : Nat.Prime 283961 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv31,pv229]) (by decide +kernel)
def pv283961 : PrimeValue := ⟨283961, pr283961⟩
private theorem pr284003 : Nat.Prime 284003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv8353]) (by decide +kernel)
def pv284003 : PrimeValue := ⟨284003, pr284003⟩
private theorem pr284051 : Nat.Prime 284051 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv19,pv23]) (by decide +kernel)
def pv284051 : PrimeValue := ⟨284051, pr284051⟩
private theorem pr284057 : Nat.Prime 284057 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv35507]) (by decide +kernel)
def pv284057 : PrimeValue := ⟨284057, pr284057⟩
private theorem pr284059 : Nat.Prime 284059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv43,pv367]) (by decide +kernel)
def pv284059 : PrimeValue := ⟨284059, pr284059⟩
private theorem pr284083 : Nat.Prime 284083 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv113,pv419]) (by decide +kernel)
def pv284083 : PrimeValue := ⟨284083, pr284083⟩
private theorem pr284093 : Nat.Prime 284093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv71023]) (by decide +kernel)
def pv284093 : PrimeValue := ⟨284093, pr284093⟩
private theorem pr284131 : Nat.Prime 284131 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv11,pv41]) (by decide +kernel)
def pv284131 : PrimeValue := ⟨284131, pr284131⟩
private theorem pr284149 : Nat.Prime 284149 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv877]) (by decide +kernel)
def pv284149 : PrimeValue := ⟨284149, pr284149⟩
private theorem pr284153 : Nat.Prime 284153 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv3229]) (by decide +kernel)
def pv284153 : PrimeValue := ⟨284153, pr284153⟩
private theorem pr284159 : Nat.Prime 284159 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv20297]) (by decide +kernel)
def pv284159 : PrimeValue := ⟨284159, pr284159⟩
private theorem pr284191 : Nat.Prime 284191 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv9473]) (by decide +kernel)
def pv284191 : PrimeValue := ⟨284191, pr284191⟩
private theorem pr284231 : Nat.Prime 284231 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv5,pv43,pv661]) (by decide +kernel)
def pv284231 : PrimeValue := ⟨284231, pr284231⟩
private theorem pr284233 : Nat.Prime 284233 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv911]) (by decide +kernel)
def pv284233 : PrimeValue := ⟨284233, pr284233⟩
private theorem pr284243 : Nat.Prime 284243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv79,pv257]) (by decide +kernel)
def pv284243 : PrimeValue := ⟨284243, pr284243⟩
private theorem pr284261 : Nat.Prime 284261 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv61,pv233]) (by decide +kernel)
def pv284261 : PrimeValue := ⟨284261, pr284261⟩
private theorem pr284269 : Nat.Prime 284269 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23689]) (by decide +kernel)
def pv284269 : PrimeValue := ⟨284269, pr284269⟩
private theorem pr284293 : Nat.Prime 284293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv53,pv149]) (by decide +kernel)
def pv284293 : PrimeValue := ⟨284293, pr284293⟩
private theorem pr284311 : Nat.Prime 284311 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv284311 : PrimeValue := ⟨284311, pr284311⟩
private theorem pr284341 : Nat.Prime 284341 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv677]) (by decide +kernel)
def pv284341 : PrimeValue := ⟨284341, pr284341⟩
private theorem pr284387 : Nat.Prime 284387 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv142193]) (by decide +kernel)
def pv284387 : PrimeValue := ⟨284387, pr284387⟩
private theorem pr284407 : Nat.Prime 284407 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv107,pv443]) (by decide +kernel)
def pv284407 : PrimeValue := ⟨284407, pr284407⟩
private theorem pr284413 : Nat.Prime 284413 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv137,pv173]) (by decide +kernel)
def pv284413 : PrimeValue := ⟨284413, pr284413⟩
private theorem pr284423 : Nat.Prime 284423 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv142211]) (by decide +kernel)
def pv284423 : PrimeValue := ⟨284423, pr284423⟩
private theorem pr284467 : Nat.Prime 284467 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv521]) (by decide +kernel)
def pv284467 : PrimeValue := ⟨284467, pr284467⟩
private theorem pr284477 : Nat.Prime 284477 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv71119]) (by decide +kernel)
def pv284477 : PrimeValue := ⟨284477, pr284477⟩
private theorem pr284489 : Nat.Prime 284489 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv43,pv827]) (by decide +kernel)
def pv284489 : PrimeValue := ⟨284489, pr284489⟩
private theorem pr284509 : Nat.Prime 284509 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv7,pv1129]) (by decide +kernel)
def pv284509 : PrimeValue := ⟨284509, pr284509⟩
private theorem pr284521 : Nat.Prime 284521 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv2371]) (by decide +kernel)
def pv284521 : PrimeValue := ⟨284521, pr284521⟩
private theorem pr284527 : Nat.Prime 284527 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv479]) (by decide +kernel)
def pv284527 : PrimeValue := ⟨284527, pr284527⟩
private theorem pr284539 : Nat.Prime 284539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv47,pv1009]) (by decide +kernel)
def pv284539 : PrimeValue := ⟨284539, pr284539⟩
private theorem pr284561 : Nat.Prime 284561 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv3557]) (by decide +kernel)
def pv284561 : PrimeValue := ⟨284561, pr284561⟩
private theorem pr284573 : Nat.Prime 284573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv71143]) (by decide +kernel)
def pv284573 : PrimeValue := ⟨284573, pr284573⟩
private theorem pr284587 : Nat.Prime 284587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv47431]) (by decide +kernel)
def pv284587 : PrimeValue := ⟨284587, pr284587⟩
private theorem pr284633 : Nat.Prime 284633 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv47,pv757]) (by decide +kernel)
def pv284633 : PrimeValue := ⟨284633, pr284633⟩
private theorem pr284651 : Nat.Prime 284651 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv5693]) (by decide +kernel)
def pv284651 : PrimeValue := ⟨284651, pr284651⟩
private theorem pr284657 : Nat.Prime 284657 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17791]) (by decide +kernel)
def pv284657 : PrimeValue := ⟨284657, pr284657⟩
private theorem pr284659 : Nat.Prime 284659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv19,pv227]) (by decide +kernel)
def pv284659 : PrimeValue := ⟨284659, pr284659⟩
private theorem pr284681 : Nat.Prime 284681 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv5,pv11,pv647]) (by decide +kernel)
def pv284681 : PrimeValue := ⟨284681, pr284681⟩
private theorem pr284689 : Nat.Prime 284689 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv659]) (by decide +kernel)
def pv284689 : PrimeValue := ⟨284689, pr284689⟩
private theorem pr284701 : Nat.Prime 284701 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv73]) (by decide +kernel)
def pv284701 : PrimeValue := ⟨284701, pr284701⟩
private theorem pr284707 : Nat.Prime 284707 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv15817]) (by decide +kernel)
def pv284707 : PrimeValue := ⟨284707, pr284707⟩
private theorem pr284723 : Nat.Prime 284723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv4909]) (by decide +kernel)
def pv284723 : PrimeValue := ⟨284723, pr284723⟩
private theorem pr284729 : Nat.Prime 284729 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv35591]) (by decide +kernel)
def pv284729 : PrimeValue := ⟨284729, pr284729⟩
private theorem pr284731 : Nat.Prime 284731 :=
  checkPrime_prime (q := pv61) (ls := [pv2,pv3,pv5,pv9491]) (by decide +kernel)
def pv284731 : PrimeValue := ⟨284731, pr284731⟩
private theorem pr284741 : Nat.Prime 284741 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv23,pv619]) (by decide +kernel)
def pv284741 : PrimeValue := ⟨284741, pr284741⟩
private theorem pr284743 : Nat.Prime 284743 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5273]) (by decide +kernel)
def pv284743 : PrimeValue := ⟨284743, pr284743⟩
private theorem pr284749 : Nat.Prime 284749 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv61,pv389]) (by decide +kernel)
def pv284749 : PrimeValue := ⟨284749, pr284749⟩
private theorem pr284777 : Nat.Prime 284777 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv35597]) (by decide +kernel)
def pv284777 : PrimeValue := ⟨284777, pr284777⟩
private theorem pr284803 : Nat.Prime 284803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv6781]) (by decide +kernel)
def pv284803 : PrimeValue := ⟨284803, pr284803⟩
private theorem pr284819 : Nat.Prime 284819 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv8377]) (by decide +kernel)
def pv284819 : PrimeValue := ⟨284819, pr284819⟩
private theorem pr284831 : Nat.Prime 284831 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv13,pv313]) (by decide +kernel)
def pv284831 : PrimeValue := ⟨284831, pr284831⟩
private theorem pr284839 : Nat.Prime 284839 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29,pv1637]) (by decide +kernel)
def pv284839 : PrimeValue := ⟨284839, pr284839⟩
private theorem pr284857 : Nat.Prime 284857 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv11,pv13,pv83]) (by decide +kernel)
def pv284857 : PrimeValue := ⟨284857, pr284857⟩
private theorem pr284881 : Nat.Prime 284881 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv5,pv1187]) (by decide +kernel)
def pv284881 : PrimeValue := ⟨284881, pr284881⟩
private theorem pr284917 : Nat.Prime 284917 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23743]) (by decide +kernel)
def pv284917 : PrimeValue := ⟨284917, pr284917⟩
private theorem pr284957 : Nat.Prime 284957 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv10177]) (by decide +kernel)
def pv284957 : PrimeValue := ⟨284957, pr284957⟩
private theorem pr284969 : Nat.Prime 284969 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv179,pv199]) (by decide +kernel)
def pv284969 : PrimeValue := ⟨284969, pr284969⟩
private theorem pr284989 : Nat.Prime 284989 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv11,pv17,pv127]) (by decide +kernel)
def pv284989 : PrimeValue := ⟨284989, pr284989⟩
private theorem pr285023 : Nat.Prime 285023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv83,pv101]) (by decide +kernel)
def pv285023 : PrimeValue := ⟨285023, pr285023⟩
private theorem pr285031 : Nat.Prime 285031 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv3167]) (by decide +kernel)
def pv285031 : PrimeValue := ⟨285031, pr285031⟩
private theorem pr285049 : Nat.Prime 285049 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv37,pv107]) (by decide +kernel)
def pv285049 : PrimeValue := ⟨285049, pr285049⟩
private theorem pr285101 : Nat.Prime 285101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv2851]) (by decide +kernel)
def pv285101 : PrimeValue := ⟨285101, pr285101⟩
private theorem pr285139 : Nat.Prime 285139 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv31,pv73]) (by decide +kernel)
def pv285139 : PrimeValue := ⟨285139, pr285139⟩
private theorem pr285151 : Nat.Prime 285151 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv1901]) (by decide +kernel)
def pv285151 : PrimeValue := ⟨285151, pr285151⟩
private theorem pr285179 : Nat.Prime 285179 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv142589]) (by decide +kernel)
def pv285179 : PrimeValue := ⟨285179, pr285179⟩
private theorem pr285191 : Nat.Prime 285191 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv19,pv79]) (by decide +kernel)
def pv285191 : PrimeValue := ⟨285191, pr285191⟩
private theorem pr285199 : Nat.Prime 285199 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv47533]) (by decide +kernel)
def pv285199 : PrimeValue := ⟨285199, pr285199⟩
private theorem pr285221 : Nat.Prime 285221 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv1097]) (by decide +kernel)
def pv285221 : PrimeValue := ⟨285221, pr285221⟩
private theorem pr285281 : Nat.Prime 285281 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv1783]) (by decide +kernel)
def pv285281 : PrimeValue := ⟨285281, pr285281⟩
private theorem pr285317 : Nat.Prime 285317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv71329]) (by decide +kernel)
def pv285317 : PrimeValue := ⟨285317, pr285317⟩
private theorem pr285343 : Nat.Prime 285343 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv2503]) (by decide +kernel)
def pv285343 : PrimeValue := ⟨285343, pr285343⟩
private theorem pr285433 : Nat.Prime 285433 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv1699]) (by decide +kernel)
def pv285433 : PrimeValue := ⟨285433, pr285433⟩
private theorem pr285451 : Nat.Prime 285451 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv173]) (by decide +kernel)
def pv285451 : PrimeValue := ⟨285451, pr285451⟩
private theorem pr285457 : Nat.Prime 285457 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv19,pv313]) (by decide +kernel)
def pv285457 : PrimeValue := ⟨285457, pr285457⟩
private theorem pr285463 : Nat.Prime 285463 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv15859]) (by decide +kernel)
def pv285463 : PrimeValue := ⟨285463, pr285463⟩
private theorem pr285469 : Nat.Prime 285469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23789]) (by decide +kernel)
def pv285469 : PrimeValue := ⟨285469, pr285469⟩
private theorem pr285473 : Nat.Prime 285473 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv811]) (by decide +kernel)
def pv285473 : PrimeValue := ⟨285473, pr285473⟩
private theorem pr285517 : Nat.Prime 285517 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv103]) (by decide +kernel)
def pv285517 : PrimeValue := ⟨285517, pr285517⟩
private theorem pr285553 : Nat.Prime 285553 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv661]) (by decide +kernel)
def pv285553 : PrimeValue := ⟨285553, pr285553⟩
private theorem pr285557 : Nat.Prime 285557 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv71389]) (by decide +kernel)
def pv285557 : PrimeValue := ⟨285557, pr285557⟩
private theorem pr285559 : Nat.Prime 285559 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv7,pv13,pv523]) (by decide +kernel)
def pv285559 : PrimeValue := ⟨285559, pr285559⟩
private theorem pr285599 : Nat.Prime 285599 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv142799]) (by decide +kernel)
def pv285599 : PrimeValue := ⟨285599, pr285599⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
