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
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr280541 : PrimeCertificate 280541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv83]) (by decide +kernel)
def pv280541 : PrimeValue := ⟨280541, pr280541⟩
private theorem pr280547 : PrimeCertificate 280547 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv29,pv691]) (by decide +kernel)
def pv280547 : PrimeValue := ⟨280547, pr280547⟩
private theorem pr280549 : PrimeCertificate 280549 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7793]) (by decide +kernel)
def pv280549 : PrimeValue := ⟨280549, pr280549⟩
private theorem pr280589 : PrimeCertificate 280589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv911]) (by decide +kernel)
def pv280589 : PrimeValue := ⟨280589, pr280589⟩
private theorem pr280591 : PrimeCertificate 280591 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv47,pv199]) (by decide +kernel)
def pv280591 : PrimeValue := ⟨280591, pr280591⟩
private theorem pr280597 : PrimeCertificate 280597 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv67,pv349]) (by decide +kernel)
def pv280597 : PrimeValue := ⟨280597, pr280597⟩
private theorem pr280603 : PrimeCertificate 280603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv131]) (by decide +kernel)
def pv280603 : PrimeValue := ⟨280603, pr280603⟩
private theorem pr280613 : PrimeCertificate 280613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv73]) (by decide +kernel)
def pv280613 : PrimeValue := ⟨280613, pr280613⟩
private theorem pr280639 : PrimeCertificate 280639 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5197]) (by decide +kernel)
def pv280639 : PrimeValue := ⟨280639, pr280639⟩
private theorem pr280673 : PrimeCertificate 280673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv179]) (by decide +kernel)
def pv280673 : PrimeValue := ⟨280673, pr280673⟩
private theorem pr280697 : PrimeCertificate 280697 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv2699]) (by decide +kernel)
def pv280697 : PrimeValue := ⟨280697, pr280697⟩
private theorem pr280711 : PrimeCertificate 280711 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv3119]) (by decide +kernel)
def pv280711 : PrimeValue := ⟨280711, pr280711⟩
private theorem pr280717 : PrimeCertificate 280717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv149,pv157]) (by decide +kernel)
def pv280717 : PrimeValue := ⟨280717, pr280717⟩
private theorem pr280759 : PrimeCertificate 280759 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv73,pv641]) (by decide +kernel)
def pv280759 : PrimeValue := ⟨280759, pr280759⟩
private theorem pr280811 : PrimeCertificate 280811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv28081]) (by decide +kernel)
def pv280811 : PrimeValue := ⟨280811, pr280811⟩
private theorem pr280817 : PrimeCertificate 280817 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17551]) (by decide +kernel)
def pv280817 : PrimeValue := ⟨280817, pr280817⟩
private theorem pr280837 : PrimeCertificate 280837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv269]) (by decide +kernel)
def pv280837 : PrimeValue := ⟨280837, pr280837⟩
private theorem pr280843 : PrimeCertificate 280843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv46807]) (by decide +kernel)
def pv280843 : PrimeValue := ⟨280843, pr280843⟩
private theorem pr280859 : PrimeCertificate 280859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv389]) (by decide +kernel)
def pv280859 : PrimeValue := ⟨280859, pr280859⟩
private theorem pr280871 : PrimeCertificate 280871 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv28087]) (by decide +kernel)
def pv280871 : PrimeValue := ⟨280871, pr280871⟩
private theorem pr280879 : PrimeCertificate 280879 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv277]) (by decide +kernel)
def pv280879 : PrimeValue := ⟨280879, pr280879⟩
private theorem pr280883 : PrimeCertificate 280883 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv20063]) (by decide +kernel)
def pv280883 : PrimeValue := ⟨280883, pr280883⟩
private theorem pr280897 : PrimeCertificate 280897 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv19]) (by decide +kernel)
def pv280897 : PrimeValue := ⟨280897, pr280897⟩
private theorem pr280909 : PrimeCertificate 280909 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17]) (by decide +kernel)
def pv280909 : PrimeValue := ⟨280909, pr280909⟩
private theorem pr280913 : PrimeCertificate 280913 :=
  certifyPrime (q := pv3) (ls := [pv2,pv97,pv181]) (by decide +kernel)
def pv280913 : PrimeValue := ⟨280913, pr280913⟩
private theorem pr280921 : PrimeCertificate 280921 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv2341]) (by decide +kernel)
def pv280921 : PrimeValue := ⟨280921, pr280921⟩
private theorem pr280927 : PrimeCertificate 280927 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv15607]) (by decide +kernel)
def pv280927 : PrimeValue := ⟨280927, pr280927⟩
private theorem pr280933 : PrimeCertificate 280933 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv41,pv571]) (by decide +kernel)
def pv280933 : PrimeValue := ⟨280933, pr280933⟩
private theorem pr280963 : PrimeCertificate 280963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv43]) (by decide +kernel)
def pv280963 : PrimeValue := ⟨280963, pr280963⟩
private theorem pr280967 : PrimeCertificate 280967 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv47,pv61]) (by decide +kernel)
def pv280967 : PrimeValue := ⟨280967, pr280967⟩
private theorem pr280997 : PrimeCertificate 280997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv70249]) (by decide +kernel)
def pv280997 : PrimeValue := ⟨280997, pr280997⟩
private theorem pr281023 : PrimeCertificate 281023 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv6691]) (by decide +kernel)
def pv281023 : PrimeValue := ⟨281023, pr281023⟩
private theorem pr281053 : PrimeCertificate 281053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv211]) (by decide +kernel)
def pv281053 : PrimeValue := ⟨281053, pr281053⟩
private theorem pr281063 : PrimeCertificate 281063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv89,pv1579]) (by decide +kernel)
def pv281063 : PrimeValue := ⟨281063, pr281063⟩
private theorem pr281117 : PrimeCertificate 281117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv6389]) (by decide +kernel)
def pv281117 : PrimeValue := ⟨281117, pr281117⟩
private theorem pr281131 : PrimeCertificate 281131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv9371]) (by decide +kernel)
def pv281131 : PrimeValue := ⟨281131, pr281131⟩
private theorem pr281153 : PrimeCertificate 281153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv191]) (by decide +kernel)
def pv281153 : PrimeValue := ⟨281153, pr281153⟩
private theorem pr281233 : PrimeCertificate 281233 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv31]) (by decide +kernel)
def pv281233 : PrimeValue := ⟨281233, pr281233⟩
private theorem pr281251 : PrimeCertificate 281251 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv281251 : PrimeValue := ⟨281251, pr281251⟩
private theorem pr281279 : PrimeCertificate 281279 :=
  certifyPrime (q := pv11) (ls := [pv2,pv140639]) (by decide +kernel)
def pv281279 : PrimeValue := ⟨281279, pr281279⟩
private theorem pr281297 : PrimeCertificate 281297 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17581]) (by decide +kernel)
def pv281297 : PrimeValue := ⟨281297, pr281297⟩
private theorem pr281317 : PrimeCertificate 281317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv197]) (by decide +kernel)
def pv281317 : PrimeValue := ⟨281317, pr281317⟩
private theorem pr281327 : PrimeCertificate 281327 :=
  certifyPrime (q := pv5) (ls := [pv2,pv140663]) (by decide +kernel)
def pv281327 : PrimeValue := ⟨281327, pr281327⟩
private theorem pr281339 : PrimeCertificate 281339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv163,pv863]) (by decide +kernel)
def pv281339 : PrimeValue := ⟨281339, pr281339⟩
private theorem pr281357 : PrimeCertificate 281357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv2269]) (by decide +kernel)
def pv281357 : PrimeValue := ⟨281357, pr281357⟩
private theorem pr281363 : PrimeCertificate 281363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv140681]) (by decide +kernel)
def pv281363 : PrimeValue := ⟨281363, pr281363⟩
private theorem pr281381 : PrimeCertificate 281381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv1279]) (by decide +kernel)
def pv281381 : PrimeValue := ⟨281381, pr281381⟩
private theorem pr281419 : PrimeCertificate 281419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv31,pv89]) (by decide +kernel)
def pv281419 : PrimeValue := ⟨281419, pr281419⟩
private theorem pr281431 : PrimeCertificate 281431 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv53,pv59]) (by decide +kernel)
def pv281431 : PrimeValue := ⟨281431, pr281431⟩
private theorem pr281509 : PrimeCertificate 281509 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv23459]) (by decide +kernel)
def pv281509 : PrimeValue := ⟨281509, pr281509⟩
private theorem pr281527 : PrimeCertificate 281527 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv6703]) (by decide +kernel)
def pv281527 : PrimeValue := ⟨281527, pr281527⟩
private theorem pr281531 : PrimeCertificate 281531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv47,pv599]) (by decide +kernel)
def pv281531 : PrimeValue := ⟨281531, pr281531⟩
private theorem pr281549 : PrimeCertificate 281549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59,pv1193]) (by decide +kernel)
def pv281549 : PrimeValue := ⟨281549, pr281549⟩
private theorem pr281557 : PrimeCertificate 281557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv79]) (by decide +kernel)
def pv281557 : PrimeValue := ⟨281557, pr281557⟩
private theorem pr281563 : PrimeCertificate 281563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv167,pv281]) (by decide +kernel)
def pv281563 : PrimeValue := ⟨281563, pr281563⟩
private theorem pr281609 : PrimeCertificate 281609 :=
  certifyPrime (q := pv3) (ls := [pv2,pv35201]) (by decide +kernel)
def pv281609 : PrimeValue := ⟨281609, pr281609⟩
private theorem pr281623 : PrimeCertificate 281623 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv17,pv251]) (by decide +kernel)
def pv281623 : PrimeValue := ⟨281623, pr281623⟩
private theorem pr281627 : PrimeCertificate 281627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv140813]) (by decide +kernel)
def pv281627 : PrimeValue := ⟨281627, pr281627⟩
private theorem pr281641 : PrimeCertificate 281641 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv2347]) (by decide +kernel)
def pv281641 : PrimeValue := ⟨281641, pr281641⟩
private theorem pr281651 : PrimeCertificate 281651 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv43,pv131]) (by decide +kernel)
def pv281651 : PrimeValue := ⟨281651, pr281651⟩
private theorem pr281653 : PrimeCertificate 281653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv479]) (by decide +kernel)
def pv281653 : PrimeValue := ⟨281653, pr281653⟩
private theorem pr281663 : PrimeCertificate 281663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv140831]) (by decide +kernel)
def pv281663 : PrimeValue := ⟨281663, pr281663⟩
private theorem pr281669 : PrimeCertificate 281669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67,pv1051]) (by decide +kernel)
def pv281669 : PrimeValue := ⟨281669, pr281669⟩
private theorem pr281683 : PrimeCertificate 281683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv15649]) (by decide +kernel)
def pv281683 : PrimeValue := ⟨281683, pr281683⟩
private theorem pr281717 : PrimeCertificate 281717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv70429]) (by decide +kernel)
def pv281717 : PrimeValue := ⟨281717, pr281717⟩
private theorem pr281737 : PrimeCertificate 281737 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv7,pv13,pv43]) (by decide +kernel)
def pv281737 : PrimeValue := ⟨281737, pr281737⟩
private theorem pr281747 : PrimeCertificate 281747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv179,pv787]) (by decide +kernel)
def pv281747 : PrimeValue := ⟨281747, pr281747⟩
private theorem pr281767 : PrimeCertificate 281767 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv151,pv311]) (by decide +kernel)
def pv281767 : PrimeValue := ⟨281767, pr281767⟩
private theorem pr281791 : PrimeCertificate 281791 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv31,pv101]) (by decide +kernel)
def pv281791 : PrimeValue := ⟨281791, pr281791⟩
private theorem pr281797 : PrimeCertificate 281797 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv1021]) (by decide +kernel)
def pv281797 : PrimeValue := ⟨281797, pr281797⟩
private theorem pr281807 : PrimeCertificate 281807 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv20129]) (by decide +kernel)
def pv281807 : PrimeValue := ⟨281807, pr281807⟩
private theorem pr281833 : PrimeCertificate 281833 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11743]) (by decide +kernel)
def pv281833 : PrimeValue := ⟨281833, pr281833⟩
private theorem pr281837 : PrimeCertificate 281837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv70459]) (by decide +kernel)
def pv281837 : PrimeValue := ⟨281837, pr281837⟩
private theorem pr281839 : PrimeCertificate 281839 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv107,pv439]) (by decide +kernel)
def pv281839 : PrimeValue := ⟨281839, pr281839⟩
private theorem pr281849 : PrimeCertificate 281849 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv719]) (by decide +kernel)
def pv281849 : PrimeValue := ⟨281849, pr281849⟩
private theorem pr281867 : PrimeCertificate 281867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv37,pv293]) (by decide +kernel)
def pv281867 : PrimeValue := ⟨281867, pr281867⟩
private theorem pr281893 : PrimeCertificate 281893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv139]) (by decide +kernel)
def pv281893 : PrimeValue := ⟨281893, pr281893⟩
private theorem pr281921 : PrimeCertificate 281921 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv881]) (by decide +kernel)
def pv281921 : PrimeValue := ⟨281921, pr281921⟩
private theorem pr281923 : PrimeCertificate 281923 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv19,pv2473]) (by decide +kernel)
def pv281923 : PrimeValue := ⟨281923, pr281923⟩
private theorem pr281947 : PrimeCertificate 281947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv137]) (by decide +kernel)
def pv281947 : PrimeValue := ⟨281947, pr281947⟩
private theorem pr281959 : PrimeCertificate 281959 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv46993]) (by decide +kernel)
def pv281959 : PrimeValue := ⟨281959, pr281959⟩
private theorem pr281971 : PrimeCertificate 281971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv241]) (by decide +kernel)
def pv281971 : PrimeValue := ⟨281971, pr281971⟩
private theorem pr281989 : PrimeCertificate 281989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv373]) (by decide +kernel)
def pv281989 : PrimeValue := ⟨281989, pr281989⟩
private theorem pr281993 : PrimeCertificate 281993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv101,pv349]) (by decide +kernel)
def pv281993 : PrimeValue := ⟨281993, pr281993⟩
private theorem pr282011 : PrimeCertificate 282011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv28201]) (by decide +kernel)
def pv282011 : PrimeValue := ⟨282011, pr282011⟩
private theorem pr282053 : PrimeCertificate 282053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv107,pv659]) (by decide +kernel)
def pv282053 : PrimeValue := ⟨282053, pr282053⟩
private theorem pr282059 : PrimeCertificate 282059 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv20147]) (by decide +kernel)
def pv282059 : PrimeValue := ⟨282059, pr282059⟩
private theorem pr282089 : PrimeCertificate 282089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv953]) (by decide +kernel)
def pv282089 : PrimeValue := ⟨282089, pr282089⟩
private theorem pr282097 : PrimeCertificate 282097 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv653]) (by decide +kernel)
def pv282097 : PrimeValue := ⟨282097, pr282097⟩
private theorem pr282127 : PrimeCertificate 282127 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv3617]) (by decide +kernel)
def pv282127 : PrimeValue := ⟨282127, pr282127⟩
private theorem pr282143 : PrimeCertificate 282143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv2879]) (by decide +kernel)
def pv282143 : PrimeValue := ⟨282143, pr282143⟩
private theorem pr282157 : PrimeCertificate 282157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv3359]) (by decide +kernel)
def pv282157 : PrimeValue := ⟨282157, pr282157⟩
private theorem pr282221 : PrimeCertificate 282221 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv103,pv137]) (by decide +kernel)
def pv282221 : PrimeValue := ⟨282221, pr282221⟩
private theorem pr282229 : PrimeCertificate 282229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv811]) (by decide +kernel)
def pv282229 : PrimeValue := ⟨282229, pr282229⟩
private theorem pr282241 : PrimeCertificate 282241 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv282241 : PrimeValue := ⟨282241, pr282241⟩
private theorem pr282253 : PrimeCertificate 282253 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv43,pv547]) (by decide +kernel)
def pv282253 : PrimeValue := ⟨282253, pr282253⟩
private theorem pr282307 : PrimeCertificate 282307 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv47051]) (by decide +kernel)
def pv282307 : PrimeValue := ⟨282307, pr282307⟩
private theorem pr282311 : PrimeCertificate 282311 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv37,pv109]) (by decide +kernel)
def pv282311 : PrimeValue := ⟨282311, pr282311⟩
private theorem pr282313 : PrimeCertificate 282313 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv1307]) (by decide +kernel)
def pv282313 : PrimeValue := ⟨282313, pr282313⟩
private theorem pr282377 : PrimeCertificate 282377 :=
  certifyPrime (q := pv3) (ls := [pv2,pv47,pv751]) (by decide +kernel)
def pv282377 : PrimeValue := ⟨282377, pr282377⟩
private theorem pr282389 : PrimeCertificate 282389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv227,pv311]) (by decide +kernel)
def pv282389 : PrimeValue := ⟨282389, pr282389⟩
private theorem pr282391 : PrimeCertificate 282391 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv9413]) (by decide +kernel)
def pv282391 : PrimeValue := ⟨282391, pr282391⟩
private theorem pr282407 : PrimeCertificate 282407 :=
  certifyPrime (q := pv5) (ls := [pv2,pv337,pv419]) (by decide +kernel)
def pv282407 : PrimeValue := ⟨282407, pr282407⟩
private theorem pr282413 : PrimeCertificate 282413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv5431]) (by decide +kernel)
def pv282413 : PrimeValue := ⟨282413, pr282413⟩
private theorem pr282439 : PrimeCertificate 282439 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv17,pv71]) (by decide +kernel)
def pv282439 : PrimeValue := ⟨282439, pr282439⟩
private theorem pr282461 : PrimeCertificate 282461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29,pv487]) (by decide +kernel)
def pv282461 : PrimeValue := ⟨282461, pr282461⟩
private theorem pr282481 : PrimeCertificate 282481 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv11,pv107]) (by decide +kernel)
def pv282481 : PrimeValue := ⟨282481, pr282481⟩
private theorem pr282559 : PrimeCertificate 282559 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv47093]) (by decide +kernel)
def pv282559 : PrimeValue := ⟨282559, pr282559⟩
private theorem pr282563 : PrimeCertificate 282563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv20183]) (by decide +kernel)
def pv282563 : PrimeValue := ⟨282563, pr282563⟩
private theorem pr282589 : PrimeCertificate 282589 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23549]) (by decide +kernel)
def pv282589 : PrimeValue := ⟨282589, pr282589⟩
private theorem pr282599 : PrimeCertificate 282599 :=
  certifyPrime (q := pv7) (ls := [pv2,pv101,pv1399]) (by decide +kernel)
def pv282599 : PrimeValue := ⟨282599, pr282599⟩
private theorem pr282661 : PrimeCertificate 282661 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv673]) (by decide +kernel)
def pv282661 : PrimeValue := ⟨282661, pr282661⟩
private theorem pr282671 : PrimeCertificate 282671 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv23,pv1229]) (by decide +kernel)
def pv282671 : PrimeValue := ⟨282671, pr282671⟩
private theorem pr282683 : PrimeCertificate 282683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv43,pv173]) (by decide +kernel)
def pv282683 : PrimeValue := ⟨282683, pr282683⟩
private theorem pr282703 : PrimeCertificate 282703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv53,pv127]) (by decide +kernel)
def pv282703 : PrimeValue := ⟨282703, pr282703⟩
private theorem pr282713 : PrimeCertificate 282713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv35339]) (by decide +kernel)
def pv282713 : PrimeValue := ⟨282713, pr282713⟩
private theorem pr282769 : PrimeCertificate 282769 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv43,pv137]) (by decide +kernel)
def pv282769 : PrimeValue := ⟨282769, pr282769⟩
private theorem pr282833 : PrimeCertificate 282833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv1607]) (by decide +kernel)
def pv282833 : PrimeValue := ⟨282833, pr282833⟩
private theorem pr282847 : PrimeCertificate 282847 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv47,pv59]) (by decide +kernel)
def pv282847 : PrimeValue := ⟨282847, pr282847⟩
private theorem pr282851 : PrimeCertificate 282851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv5657]) (by decide +kernel)
def pv282851 : PrimeValue := ⟨282851, pr282851⟩
private theorem pr282869 : PrimeCertificate 282869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv70717]) (by decide +kernel)
def pv282869 : PrimeValue := ⟨282869, pr282869⟩
private theorem pr282881 : PrimeCertificate 282881 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv17]) (by decide +kernel)
def pv282881 : PrimeValue := ⟨282881, pr282881⟩
private theorem pr282907 : PrimeCertificate 282907 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv31]) (by decide +kernel)
def pv282907 : PrimeValue := ⟨282907, pr282907⟩
private theorem pr282913 : PrimeCertificate 282913 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv421]) (by decide +kernel)
def pv282913 : PrimeValue := ⟨282913, pr282913⟩
private theorem pr282917 : PrimeCertificate 282917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv70729]) (by decide +kernel)
def pv282917 : PrimeValue := ⟨282917, pr282917⟩
private theorem pr282959 : PrimeCertificate 282959 :=
  certifyPrime (q := pv17) (ls := [pv2,pv13,pv10883]) (by decide +kernel)
def pv282959 : PrimeValue := ⟨282959, pr282959⟩
private theorem pr282977 : PrimeCertificate 282977 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv239]) (by decide +kernel)
def pv282977 : PrimeValue := ⟨282977, pr282977⟩
private theorem pr282991 : PrimeCertificate 282991 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv9433]) (by decide +kernel)
def pv282991 : PrimeValue := ⟨282991, pr282991⟩
private theorem pr283001 : PrimeCertificate 283001 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv283]) (by decide +kernel)
def pv283001 : PrimeValue := ⟨283001, pr283001⟩
private theorem pr283007 : PrimeCertificate 283007 :=
  certifyPrime (q := pv5) (ls := [pv2,pv71,pv1993]) (by decide +kernel)
def pv283007 : PrimeValue := ⟨283007, pr283007⟩
private theorem pr283051 : PrimeCertificate 283051 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv17,pv37]) (by decide +kernel)
def pv283051 : PrimeValue := ⟨283051, pr283051⟩
private theorem pr283093 : PrimeCertificate 283093 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv761]) (by decide +kernel)
def pv283093 : PrimeValue := ⟨283093, pr283093⟩
private theorem pr283097 : PrimeCertificate 283097 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv3217]) (by decide +kernel)
def pv283097 : PrimeValue := ⟨283097, pr283097⟩
private theorem pr283121 : PrimeCertificate 283121 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv3539]) (by decide +kernel)
def pv283121 : PrimeValue := ⟨283121, pr283121⟩
private theorem pr283133 : PrimeCertificate 283133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv70783]) (by decide +kernel)
def pv283133 : PrimeValue := ⟨283133, pr283133⟩
private theorem pr283193 : PrimeCertificate 283193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv13,pv389]) (by decide +kernel)
def pv283193 : PrimeValue := ⟨283193, pr283193⟩
private theorem pr283277 : PrimeCertificate 283277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv67,pv151]) (by decide +kernel)
def pv283277 : PrimeValue := ⟨283277, pr283277⟩
private theorem pr283303 : PrimeCertificate 283303 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv15739]) (by decide +kernel)
def pv283303 : PrimeValue := ⟨283303, pr283303⟩
private theorem pr283369 : PrimeCertificate 283369 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv11807]) (by decide +kernel)
def pv283369 : PrimeValue := ⟨283369, pr283369⟩
private theorem pr283397 : PrimeCertificate 283397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv70849]) (by decide +kernel)
def pv283397 : PrimeValue := ⟨283397, pr283397⟩
private theorem pr283447 : PrimeCertificate 283447 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv181]) (by decide +kernel)
def pv283447 : PrimeValue := ⟨283447, pr283447⟩
private theorem pr283463 : PrimeCertificate 283463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv141731]) (by decide +kernel)
def pv283463 : PrimeValue := ⟨283463, pr283463⟩
private theorem pr283489 : PrimeCertificate 283489 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv2953]) (by decide +kernel)
def pv283489 : PrimeValue := ⟨283489, pr283489⟩
private theorem pr283501 : PrimeCertificate 283501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv283501 : PrimeValue := ⟨283501, pr283501⟩
private theorem pr283553 : PrimeCertificate 283553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv8861]) (by decide +kernel)
def pv283553 : PrimeValue := ⟨283553, pr283553⟩
private theorem pr283571 : PrimeCertificate 283571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv4051]) (by decide +kernel)
def pv283571 : PrimeValue := ⟨283571, pr283571⟩
private theorem pr283573 : PrimeCertificate 283573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7877]) (by decide +kernel)
def pv283573 : PrimeValue := ⟨283573, pr283573⟩
private theorem pr283601 : PrimeCertificate 283601 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv709]) (by decide +kernel)
def pv283601 : PrimeValue := ⟨283601, pr283601⟩
private theorem pr283607 : PrimeCertificate 283607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv141803]) (by decide +kernel)
def pv283607 : PrimeValue := ⟨283607, pr283607⟩
private theorem pr283609 : PrimeCertificate 283609 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv13,pv101]) (by decide +kernel)
def pv283609 : PrimeValue := ⟨283609, pr283609⟩
private theorem pr283631 : PrimeCertificate 283631 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv113,pv251]) (by decide +kernel)
def pv283631 : PrimeValue := ⟨283631, pr283631⟩
private theorem pr283637 : PrimeCertificate 283637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv3083]) (by decide +kernel)
def pv283637 : PrimeValue := ⟨283637, pr283637⟩
private theorem pr283639 : PrimeCertificate 283639 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv41,pv1153]) (by decide +kernel)
def pv283639 : PrimeValue := ⟨283639, pr283639⟩
private theorem pr283721 : PrimeCertificate 283721 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv41,pv173]) (by decide +kernel)
def pv283721 : PrimeValue := ⟨283721, pr283721⟩
private theorem pr283741 : PrimeCertificate 283741 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv4729]) (by decide +kernel)
def pv283741 : PrimeValue := ⟨283741, pr283741⟩
private theorem pr283763 : PrimeCertificate 283763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv2677]) (by decide +kernel)
def pv283763 : PrimeValue := ⟨283763, pr283763⟩
private theorem pr283769 : PrimeCertificate 283769 :=
  certifyPrime (q := pv3) (ls := [pv2,pv79,pv449]) (by decide +kernel)
def pv283769 : PrimeValue := ⟨283769, pr283769⟩
private theorem pr283771 : PrimeCertificate 283771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1051]) (by decide +kernel)
def pv283771 : PrimeValue := ⟨283771, pr283771⟩
private theorem pr283799 : PrimeCertificate 283799 :=
  certifyPrime (q := pv23) (ls := [pv2,pv17,pv491]) (by decide +kernel)
def pv283799 : PrimeValue := ⟨283799, pr283799⟩
private theorem pr283807 : PrimeCertificate 283807 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv15767]) (by decide +kernel)
def pv283807 : PrimeValue := ⟨283807, pr283807⟩
private theorem pr283813 : PrimeCertificate 283813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv67,pv353]) (by decide +kernel)
def pv283813 : PrimeValue := ⟨283813, pr283813⟩
private theorem pr283817 : PrimeCertificate 283817 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv2729]) (by decide +kernel)
def pv283817 : PrimeValue := ⟨283817, pr283817⟩
private theorem pr283831 : PrimeCertificate 283831 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv9461]) (by decide +kernel)
def pv283831 : PrimeValue := ⟨283831, pr283831⟩
private theorem pr283859 : PrimeCertificate 283859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71,pv1999]) (by decide +kernel)
def pv283859 : PrimeValue := ⟨283859, pr283859⟩
private theorem pr283861 : PrimeCertificate 283861 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv19,pv83]) (by decide +kernel)
def pv283861 : PrimeValue := ⟨283861, pr283861⟩
private theorem pr283937 : PrimeCertificate 283937 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv467]) (by decide +kernel)
def pv283937 : PrimeValue := ⟨283937, pr283937⟩
private theorem pr283949 : PrimeCertificate 283949 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv10141]) (by decide +kernel)
def pv283949 : PrimeValue := ⟨283949, pr283949⟩
private theorem pr283961 : PrimeCertificate 283961 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv31,pv229]) (by decide +kernel)
def pv283961 : PrimeValue := ⟨283961, pr283961⟩
private theorem pr284003 : PrimeCertificate 284003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv8353]) (by decide +kernel)
def pv284003 : PrimeValue := ⟨284003, pr284003⟩
private theorem pr284051 : PrimeCertificate 284051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv19,pv23]) (by decide +kernel)
def pv284051 : PrimeValue := ⟨284051, pr284051⟩
private theorem pr284057 : PrimeCertificate 284057 :=
  certifyPrime (q := pv3) (ls := [pv2,pv35507]) (by decide +kernel)
def pv284057 : PrimeValue := ⟨284057, pr284057⟩
private theorem pr284059 : PrimeCertificate 284059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv367]) (by decide +kernel)
def pv284059 : PrimeValue := ⟨284059, pr284059⟩
private theorem pr284083 : PrimeCertificate 284083 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv113,pv419]) (by decide +kernel)
def pv284083 : PrimeValue := ⟨284083, pr284083⟩
private theorem pr284093 : PrimeCertificate 284093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71023]) (by decide +kernel)
def pv284093 : PrimeValue := ⟨284093, pr284093⟩
private theorem pr284131 : PrimeCertificate 284131 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv11,pv41]) (by decide +kernel)
def pv284131 : PrimeValue := ⟨284131, pr284131⟩
private theorem pr284149 : PrimeCertificate 284149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv877]) (by decide +kernel)
def pv284149 : PrimeValue := ⟨284149, pr284149⟩
private theorem pr284153 : PrimeCertificate 284153 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv3229]) (by decide +kernel)
def pv284153 : PrimeValue := ⟨284153, pr284153⟩
private theorem pr284159 : PrimeCertificate 284159 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv20297]) (by decide +kernel)
def pv284159 : PrimeValue := ⟨284159, pr284159⟩
private theorem pr284191 : PrimeCertificate 284191 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv9473]) (by decide +kernel)
def pv284191 : PrimeValue := ⟨284191, pr284191⟩
private theorem pr284231 : PrimeCertificate 284231 :=
  certifyPrime (q := pv41) (ls := [pv2,pv5,pv43,pv661]) (by decide +kernel)
def pv284231 : PrimeValue := ⟨284231, pr284231⟩
private theorem pr284233 : PrimeCertificate 284233 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv911]) (by decide +kernel)
def pv284233 : PrimeValue := ⟨284233, pr284233⟩
private theorem pr284243 : PrimeCertificate 284243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv79,pv257]) (by decide +kernel)
def pv284243 : PrimeValue := ⟨284243, pr284243⟩
private theorem pr284261 : PrimeCertificate 284261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv61,pv233]) (by decide +kernel)
def pv284261 : PrimeValue := ⟨284261, pr284261⟩
private theorem pr284269 : PrimeCertificate 284269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23689]) (by decide +kernel)
def pv284269 : PrimeValue := ⟨284269, pr284269⟩
private theorem pr284293 : PrimeCertificate 284293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53,pv149]) (by decide +kernel)
def pv284293 : PrimeValue := ⟨284293, pr284293⟩
private theorem pr284311 : PrimeCertificate 284311 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv284311 : PrimeValue := ⟨284311, pr284311⟩
private theorem pr284341 : PrimeCertificate 284341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv677]) (by decide +kernel)
def pv284341 : PrimeValue := ⟨284341, pr284341⟩
private theorem pr284387 : PrimeCertificate 284387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv142193]) (by decide +kernel)
def pv284387 : PrimeValue := ⟨284387, pr284387⟩
private theorem pr284407 : PrimeCertificate 284407 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv107,pv443]) (by decide +kernel)
def pv284407 : PrimeValue := ⟨284407, pr284407⟩
private theorem pr284413 : PrimeCertificate 284413 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv137,pv173]) (by decide +kernel)
def pv284413 : PrimeValue := ⟨284413, pr284413⟩
private theorem pr284423 : PrimeCertificate 284423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv142211]) (by decide +kernel)
def pv284423 : PrimeValue := ⟨284423, pr284423⟩
private theorem pr284467 : PrimeCertificate 284467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv521]) (by decide +kernel)
def pv284467 : PrimeValue := ⟨284467, pr284467⟩
private theorem pr284477 : PrimeCertificate 284477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71119]) (by decide +kernel)
def pv284477 : PrimeValue := ⟨284477, pr284477⟩
private theorem pr284489 : PrimeCertificate 284489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43,pv827]) (by decide +kernel)
def pv284489 : PrimeValue := ⟨284489, pr284489⟩
private theorem pr284509 : PrimeCertificate 284509 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv7,pv1129]) (by decide +kernel)
def pv284509 : PrimeValue := ⟨284509, pr284509⟩
private theorem pr284521 : PrimeCertificate 284521 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv2371]) (by decide +kernel)
def pv284521 : PrimeValue := ⟨284521, pr284521⟩
private theorem pr284527 : PrimeCertificate 284527 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv479]) (by decide +kernel)
def pv284527 : PrimeValue := ⟨284527, pr284527⟩
private theorem pr284539 : PrimeCertificate 284539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv1009]) (by decide +kernel)
def pv284539 : PrimeValue := ⟨284539, pr284539⟩
private theorem pr284561 : PrimeCertificate 284561 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv3557]) (by decide +kernel)
def pv284561 : PrimeValue := ⟨284561, pr284561⟩
private theorem pr284573 : PrimeCertificate 284573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71143]) (by decide +kernel)
def pv284573 : PrimeValue := ⟨284573, pr284573⟩
private theorem pr284587 : PrimeCertificate 284587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47431]) (by decide +kernel)
def pv284587 : PrimeValue := ⟨284587, pr284587⟩
private theorem pr284633 : PrimeCertificate 284633 :=
  certifyPrime (q := pv3) (ls := [pv2,pv47,pv757]) (by decide +kernel)
def pv284633 : PrimeValue := ⟨284633, pr284633⟩
private theorem pr284651 : PrimeCertificate 284651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv5693]) (by decide +kernel)
def pv284651 : PrimeValue := ⟨284651, pr284651⟩
private theorem pr284657 : PrimeCertificate 284657 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17791]) (by decide +kernel)
def pv284657 : PrimeValue := ⟨284657, pr284657⟩
private theorem pr284659 : PrimeCertificate 284659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv19,pv227]) (by decide +kernel)
def pv284659 : PrimeValue := ⟨284659, pr284659⟩
private theorem pr284681 : PrimeCertificate 284681 :=
  certifyPrime (q := pv29) (ls := [pv2,pv5,pv11,pv647]) (by decide +kernel)
def pv284681 : PrimeValue := ⟨284681, pr284681⟩
private theorem pr284689 : PrimeCertificate 284689 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv659]) (by decide +kernel)
def pv284689 : PrimeValue := ⟨284689, pr284689⟩
private theorem pr284701 : PrimeCertificate 284701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv73]) (by decide +kernel)
def pv284701 : PrimeValue := ⟨284701, pr284701⟩
private theorem pr284707 : PrimeCertificate 284707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv15817]) (by decide +kernel)
def pv284707 : PrimeValue := ⟨284707, pr284707⟩
private theorem pr284723 : PrimeCertificate 284723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv4909]) (by decide +kernel)
def pv284723 : PrimeValue := ⟨284723, pr284723⟩
private theorem pr284729 : PrimeCertificate 284729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv35591]) (by decide +kernel)
def pv284729 : PrimeValue := ⟨284729, pr284729⟩
private theorem pr284731 : PrimeCertificate 284731 :=
  certifyPrime (q := pv61) (ls := [pv2,pv3,pv5,pv9491]) (by decide +kernel)
def pv284731 : PrimeValue := ⟨284731, pr284731⟩
private theorem pr284741 : PrimeCertificate 284741 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv23,pv619]) (by decide +kernel)
def pv284741 : PrimeValue := ⟨284741, pr284741⟩
private theorem pr284743 : PrimeCertificate 284743 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5273]) (by decide +kernel)
def pv284743 : PrimeValue := ⟨284743, pr284743⟩
private theorem pr284749 : PrimeCertificate 284749 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv61,pv389]) (by decide +kernel)
def pv284749 : PrimeValue := ⟨284749, pr284749⟩
private theorem pr284777 : PrimeCertificate 284777 :=
  certifyPrime (q := pv3) (ls := [pv2,pv35597]) (by decide +kernel)
def pv284777 : PrimeValue := ⟨284777, pr284777⟩
private theorem pr284803 : PrimeCertificate 284803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv6781]) (by decide +kernel)
def pv284803 : PrimeValue := ⟨284803, pr284803⟩
private theorem pr284819 : PrimeCertificate 284819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv8377]) (by decide +kernel)
def pv284819 : PrimeValue := ⟨284819, pr284819⟩
private theorem pr284831 : PrimeCertificate 284831 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv13,pv313]) (by decide +kernel)
def pv284831 : PrimeValue := ⟨284831, pr284831⟩
private theorem pr284839 : PrimeCertificate 284839 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv1637]) (by decide +kernel)
def pv284839 : PrimeValue := ⟨284839, pr284839⟩
private theorem pr284857 : PrimeCertificate 284857 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv11,pv13,pv83]) (by decide +kernel)
def pv284857 : PrimeValue := ⟨284857, pr284857⟩
private theorem pr284881 : PrimeCertificate 284881 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv5,pv1187]) (by decide +kernel)
def pv284881 : PrimeValue := ⟨284881, pr284881⟩
private theorem pr284917 : PrimeCertificate 284917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23743]) (by decide +kernel)
def pv284917 : PrimeValue := ⟨284917, pr284917⟩
private theorem pr284957 : PrimeCertificate 284957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv10177]) (by decide +kernel)
def pv284957 : PrimeValue := ⟨284957, pr284957⟩
private theorem pr284969 : PrimeCertificate 284969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv179,pv199]) (by decide +kernel)
def pv284969 : PrimeValue := ⟨284969, pr284969⟩
private theorem pr284989 : PrimeCertificate 284989 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv11,pv17,pv127]) (by decide +kernel)
def pv284989 : PrimeValue := ⟨284989, pr284989⟩
private theorem pr285023 : PrimeCertificate 285023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv83,pv101]) (by decide +kernel)
def pv285023 : PrimeValue := ⟨285023, pr285023⟩
private theorem pr285031 : PrimeCertificate 285031 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv3167]) (by decide +kernel)
def pv285031 : PrimeValue := ⟨285031, pr285031⟩
private theorem pr285049 : PrimeCertificate 285049 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv37,pv107]) (by decide +kernel)
def pv285049 : PrimeValue := ⟨285049, pr285049⟩
private theorem pr285101 : PrimeCertificate 285101 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv2851]) (by decide +kernel)
def pv285101 : PrimeValue := ⟨285101, pr285101⟩
private theorem pr285139 : PrimeCertificate 285139 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv31,pv73]) (by decide +kernel)
def pv285139 : PrimeValue := ⟨285139, pr285139⟩
private theorem pr285151 : PrimeCertificate 285151 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv1901]) (by decide +kernel)
def pv285151 : PrimeValue := ⟨285151, pr285151⟩
private theorem pr285179 : PrimeCertificate 285179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv142589]) (by decide +kernel)
def pv285179 : PrimeValue := ⟨285179, pr285179⟩
private theorem pr285191 : PrimeCertificate 285191 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv19,pv79]) (by decide +kernel)
def pv285191 : PrimeValue := ⟨285191, pr285191⟩
private theorem pr285199 : PrimeCertificate 285199 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv47533]) (by decide +kernel)
def pv285199 : PrimeValue := ⟨285199, pr285199⟩
private theorem pr285221 : PrimeCertificate 285221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv1097]) (by decide +kernel)
def pv285221 : PrimeValue := ⟨285221, pr285221⟩
private theorem pr285281 : PrimeCertificate 285281 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1783]) (by decide +kernel)
def pv285281 : PrimeValue := ⟨285281, pr285281⟩
private theorem pr285317 : PrimeCertificate 285317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71329]) (by decide +kernel)
def pv285317 : PrimeValue := ⟨285317, pr285317⟩
private theorem pr285343 : PrimeCertificate 285343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv2503]) (by decide +kernel)
def pv285343 : PrimeValue := ⟨285343, pr285343⟩
private theorem pr285433 : PrimeCertificate 285433 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv1699]) (by decide +kernel)
def pv285433 : PrimeValue := ⟨285433, pr285433⟩
private theorem pr285451 : PrimeCertificate 285451 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv173]) (by decide +kernel)
def pv285451 : PrimeValue := ⟨285451, pr285451⟩
private theorem pr285457 : PrimeCertificate 285457 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv19,pv313]) (by decide +kernel)
def pv285457 : PrimeValue := ⟨285457, pr285457⟩
private theorem pr285463 : PrimeCertificate 285463 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv15859]) (by decide +kernel)
def pv285463 : PrimeValue := ⟨285463, pr285463⟩
private theorem pr285469 : PrimeCertificate 285469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23789]) (by decide +kernel)
def pv285469 : PrimeValue := ⟨285469, pr285469⟩
private theorem pr285473 : PrimeCertificate 285473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv811]) (by decide +kernel)
def pv285473 : PrimeValue := ⟨285473, pr285473⟩
private theorem pr285517 : PrimeCertificate 285517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv103]) (by decide +kernel)
def pv285517 : PrimeValue := ⟨285517, pr285517⟩
private theorem pr285553 : PrimeCertificate 285553 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv661]) (by decide +kernel)
def pv285553 : PrimeValue := ⟨285553, pr285553⟩
private theorem pr285557 : PrimeCertificate 285557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71389]) (by decide +kernel)
def pv285557 : PrimeValue := ⟨285557, pr285557⟩
private theorem pr285559 : PrimeCertificate 285559 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv7,pv13,pv523]) (by decide +kernel)
def pv285559 : PrimeValue := ⟨285559, pr285559⟩
private theorem pr285599 : PrimeCertificate 285599 :=
  certifyPrime (q := pv13) (ls := [pv2,pv142799]) (by decide +kernel)
def pv285599 : PrimeValue := ⟨285599, pr285599⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
