/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table015
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table015.pv35171
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table003
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table008

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr35171 : Nat.Prime 35171 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv3517]) (by decide +kernel)
def pv35171 : PrimeValue := ⟨35171, pr35171⟩
private theorem pr35201 : Nat.Prime 35201 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11]) (by decide +kernel)
def pv35201 : PrimeValue := ⟨35201, pr35201⟩
private theorem pr35221 : Nat.Prime 35221 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv587]) (by decide +kernel)
def pv35221 : PrimeValue := ⟨35221, pr35221⟩
private theorem pr35227 : Nat.Prime 35227 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv103]) (by decide +kernel)
def pv35227 : PrimeValue := ⟨35227, pr35227⟩
private theorem pr35251 : Nat.Prime 35251 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv47]) (by decide +kernel)
def pv35251 : PrimeValue := ⟨35251, pr35251⟩
private theorem pr35257 : Nat.Prime 35257 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv113]) (by decide +kernel)
def pv35257 : PrimeValue := ⟨35257, pr35257⟩
private theorem pr35267 : Nat.Prime 35267 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv229]) (by decide +kernel)
def pv35267 : PrimeValue := ⟨35267, pr35267⟩
private theorem pr35279 : Nat.Prime 35279 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv31,pv569]) (by decide +kernel)
def pv35279 : PrimeValue := ⟨35279, pr35279⟩
private theorem pr35281 : Nat.Prime 35281 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv35281 : PrimeValue := ⟨35281, pr35281⟩
private theorem pr35291 : Nat.Prime 35291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv3529]) (by decide +kernel)
def pv35291 : PrimeValue := ⟨35291, pr35291⟩
private theorem pr35311 : Nat.Prime 35311 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv107]) (by decide +kernel)
def pv35311 : PrimeValue := ⟨35311, pr35311⟩
private theorem pr35317 : Nat.Prime 35317 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv109]) (by decide +kernel)
def pv35317 : PrimeValue := ⟨35317, pr35317⟩
private theorem pr35323 : Nat.Prime 35323 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv29]) (by decide +kernel)
def pv35323 : PrimeValue := ⟨35323, pr35323⟩
private theorem pr35327 : Nat.Prime 35327 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv1039]) (by decide +kernel)
def pv35327 : PrimeValue := ⟨35327, pr35327⟩
private theorem pr35339 : Nat.Prime 35339 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17669]) (by decide +kernel)
def pv35339 : PrimeValue := ⟨35339, pr35339⟩
private theorem pr35353 : Nat.Prime 35353 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv491]) (by decide +kernel)
def pv35353 : PrimeValue := ⟨35353, pr35353⟩
private theorem pr35363 : Nat.Prime 35363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17681]) (by decide +kernel)
def pv35363 : PrimeValue := ⟨35363, pr35363⟩
private theorem pr35381 : Nat.Prime 35381 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv29,pv61]) (by decide +kernel)
def pv35381 : PrimeValue := ⟨35381, pr35381⟩
private theorem pr35393 : Nat.Prime 35393 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv79]) (by decide +kernel)
def pv35393 : PrimeValue := ⟨35393, pr35393⟩
private theorem pr35401 : Nat.Prime 35401 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv59]) (by decide +kernel)
def pv35401 : PrimeValue := ⟨35401, pr35401⟩
private theorem pr35407 : Nat.Prime 35407 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv281]) (by decide +kernel)
def pv35407 : PrimeValue := ⟨35407, pr35407⟩
private theorem pr35419 : Nat.Prime 35419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5903]) (by decide +kernel)
def pv35419 : PrimeValue := ⟨35419, pr35419⟩
private theorem pr35423 : Nat.Prime 35423 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv89,pv199]) (by decide +kernel)
def pv35423 : PrimeValue := ⟨35423, pr35423⟩
private theorem pr35437 : Nat.Prime 35437 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv2953]) (by decide +kernel)
def pv35437 : PrimeValue := ⟨35437, pr35437⟩
private theorem pr35447 : Nat.Prime 35447 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv37,pv479]) (by decide +kernel)
def pv35447 : PrimeValue := ⟨35447, pr35447⟩
private theorem pr35449 : Nat.Prime 35449 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv211]) (by decide +kernel)
def pv35449 : PrimeValue := ⟨35449, pr35449⟩
private theorem pr35461 : Nat.Prime 35461 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv197]) (by decide +kernel)
def pv35461 : PrimeValue := ⟨35461, pr35461⟩
private theorem pr35491 : Nat.Prime 35491 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv13]) (by decide +kernel)
def pv35491 : PrimeValue := ⟨35491, pr35491⟩
private theorem pr35507 : Nat.Prime 35507 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv433]) (by decide +kernel)
def pv35507 : PrimeValue := ⟨35507, pr35507⟩
private theorem pr35509 : Nat.Prime 35509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv269]) (by decide +kernel)
def pv35509 : PrimeValue := ⟨35509, pr35509⟩
private theorem pr35521 : Nat.Prime 35521 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv37]) (by decide +kernel)
def pv35521 : PrimeValue := ⟨35521, pr35521⟩
private theorem pr35527 : Nat.Prime 35527 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv31,pv191]) (by decide +kernel)
def pv35527 : PrimeValue := ⟨35527, pr35527⟩
private theorem pr35531 : Nat.Prime 35531 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv11,pv17,pv19]) (by decide +kernel)
def pv35531 : PrimeValue := ⟨35531, pr35531⟩
private theorem pr35533 : Nat.Prime 35533 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv47]) (by decide +kernel)
def pv35533 : PrimeValue := ⟨35533, pr35533⟩
private theorem pr35537 : Nat.Prime 35537 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2221]) (by decide +kernel)
def pv35537 : PrimeValue := ⟨35537, pr35537⟩
private theorem pr35543 : Nat.Prime 35543 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv1367]) (by decide +kernel)
def pv35543 : PrimeValue := ⟨35543, pr35543⟩
private theorem pr35569 : Nat.Prime 35569 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv13,pv19]) (by decide +kernel)
def pv35569 : PrimeValue := ⟨35569, pr35569⟩
private theorem pr35573 : Nat.Prime 35573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv8893]) (by decide +kernel)
def pv35573 : PrimeValue := ⟨35573, pr35573⟩
private theorem pr35591 : Nat.Prime 35591 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv3559]) (by decide +kernel)
def pv35591 : PrimeValue := ⟨35591, pr35591⟩
private theorem pr35593 : Nat.Prime 35593 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1483]) (by decide +kernel)
def pv35593 : PrimeValue := ⟨35593, pr35593⟩
private theorem pr35597 : Nat.Prime 35597 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv809]) (by decide +kernel)
def pv35597 : PrimeValue := ⟨35597, pr35597⟩
private theorem pr35603 : Nat.Prime 35603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv2543]) (by decide +kernel)
def pv35603 : PrimeValue := ⟨35603, pr35603⟩
private theorem pr35617 : Nat.Prime 35617 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv53]) (by decide +kernel)
def pv35617 : PrimeValue := ⟨35617, pr35617⟩
private theorem pr35671 : Nat.Prime 35671 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv29,pv41]) (by decide +kernel)
def pv35671 : PrimeValue := ⟨35671, pr35671⟩
private theorem pr35677 : Nat.Prime 35677 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv991]) (by decide +kernel)
def pv35677 : PrimeValue := ⟨35677, pr35677⟩
private theorem pr35729 : Nat.Prime 35729 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv11,pv29]) (by decide +kernel)
def pv35729 : PrimeValue := ⟨35729, pr35729⟩
private theorem pr35731 : Nat.Prime 35731 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv397]) (by decide +kernel)
def pv35731 : PrimeValue := ⟨35731, pr35731⟩
private theorem pr35747 : Nat.Prime 35747 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv293]) (by decide +kernel)
def pv35747 : PrimeValue := ⟨35747, pr35747⟩
private theorem pr35753 : Nat.Prime 35753 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv41,pv109]) (by decide +kernel)
def pv35753 : PrimeValue := ⟨35753, pr35753⟩
private theorem pr35759 : Nat.Prime 35759 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv19,pv941]) (by decide +kernel)
def pv35759 : PrimeValue := ⟨35759, pr35759⟩
private theorem pr35771 : Nat.Prime 35771 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv7,pv73]) (by decide +kernel)
def pv35771 : PrimeValue := ⟨35771, pr35771⟩
private theorem pr35797 : Nat.Prime 35797 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv157]) (by decide +kernel)
def pv35797 : PrimeValue := ⟨35797, pr35797⟩
private theorem pr35801 : Nat.Prime 35801 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv179]) (by decide +kernel)
def pv35801 : PrimeValue := ⟨35801, pr35801⟩
private theorem pr35803 : Nat.Prime 35803 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv13,pv17]) (by decide +kernel)
def pv35803 : PrimeValue := ⟨35803, pr35803⟩
private theorem pr35809 : Nat.Prime 35809 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv373]) (by decide +kernel)
def pv35809 : PrimeValue := ⟨35809, pr35809⟩
private theorem pr35831 : Nat.Prime 35831 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv3583]) (by decide +kernel)
def pv35831 : PrimeValue := ⟨35831, pr35831⟩
private theorem pr35837 : Nat.Prime 35837 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv31]) (by decide +kernel)
def pv35837 : PrimeValue := ⟨35837, pr35837⟩
private theorem pr35839 : Nat.Prime 35839 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv11,pv181]) (by decide +kernel)
def pv35839 : PrimeValue := ⟨35839, pr35839⟩
private theorem pr35851 : Nat.Prime 35851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv239]) (by decide +kernel)
def pv35851 : PrimeValue := ⟨35851, pr35851⟩
private theorem pr35863 : Nat.Prime 35863 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv43,pv139]) (by decide +kernel)
def pv35863 : PrimeValue := ⟨35863, pr35863⟩
private theorem pr35869 : Nat.Prime 35869 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv61]) (by decide +kernel)
def pv35869 : PrimeValue := ⟨35869, pr35869⟩
private theorem pr35879 : Nat.Prime 35879 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv17939]) (by decide +kernel)
def pv35879 : PrimeValue := ⟨35879, pr35879⟩
private theorem pr35897 : Nat.Prime 35897 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv641]) (by decide +kernel)
def pv35897 : PrimeValue := ⟨35897, pr35897⟩
private theorem pr35899 : Nat.Prime 35899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv193]) (by decide +kernel)
def pv35899 : PrimeValue := ⟨35899, pr35899⟩
private theorem pr35911 : Nat.Prime 35911 :=
  checkPrime_prime (q := pv61) (ls := [pv2,pv3,pv5,pv7,pv19]) (by decide +kernel)
def pv35911 : PrimeValue := ⟨35911, pr35911⟩
private theorem pr35923 : Nat.Prime 35923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5987]) (by decide +kernel)
def pv35923 : PrimeValue := ⟨35923, pr35923⟩
private theorem pr35933 : Nat.Prime 35933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv691]) (by decide +kernel)
def pv35933 : PrimeValue := ⟨35933, pr35933⟩
private theorem pr35951 : Nat.Prime 35951 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv719]) (by decide +kernel)
def pv35951 : PrimeValue := ⟨35951, pr35951⟩
private theorem pr35963 : Nat.Prime 35963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17981]) (by decide +kernel)
def pv35963 : PrimeValue := ⟨35963, pr35963⟩
private theorem pr35969 : Nat.Prime 35969 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv281]) (by decide +kernel)
def pv35969 : PrimeValue := ⟨35969, pr35969⟩
private theorem pr35977 : Nat.Prime 35977 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv1499]) (by decide +kernel)
def pv35977 : PrimeValue := ⟨35977, pr35977⟩
private theorem pr35983 : Nat.Prime 35983 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv1999]) (by decide +kernel)
def pv35983 : PrimeValue := ⟨35983, pr35983⟩
private theorem pr35993 : Nat.Prime 35993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv409]) (by decide +kernel)
def pv35993 : PrimeValue := ⟨35993, pr35993⟩
private theorem pr35999 : Nat.Prime 35999 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv41,pv439]) (by decide +kernel)
def pv35999 : PrimeValue := ⟨35999, pr35999⟩
private theorem pr36007 : Nat.Prime 36007 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv353]) (by decide +kernel)
def pv36007 : PrimeValue := ⟨36007, pr36007⟩
private theorem pr36011 : Nat.Prime 36011 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv277]) (by decide +kernel)
def pv36011 : PrimeValue := ⟨36011, pr36011⟩
private theorem pr36013 : Nat.Prime 36013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv3001]) (by decide +kernel)
def pv36013 : PrimeValue := ⟨36013, pr36013⟩
private theorem pr36017 : Nat.Prime 36017 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2251]) (by decide +kernel)
def pv36017 : PrimeValue := ⟨36017, pr36017⟩
private theorem pr36037 : Nat.Prime 36037 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv13]) (by decide +kernel)
def pv36037 : PrimeValue := ⟨36037, pr36037⟩
private theorem pr36061 : Nat.Prime 36061 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv601]) (by decide +kernel)
def pv36061 : PrimeValue := ⟨36061, pr36061⟩
private theorem pr36067 : Nat.Prime 36067 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv6011]) (by decide +kernel)
def pv36067 : PrimeValue := ⟨36067, pr36067⟩
private theorem pr36073 : Nat.Prime 36073 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv167]) (by decide +kernel)
def pv36073 : PrimeValue := ⟨36073, pr36073⟩
private theorem pr36083 : Nat.Prime 36083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv18041]) (by decide +kernel)
def pv36083 : PrimeValue := ⟨36083, pr36083⟩
private theorem pr36097 : Nat.Prime 36097 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv47]) (by decide +kernel)
def pv36097 : PrimeValue := ⟨36097, pr36097⟩
private theorem pr36107 : Nat.Prime 36107 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv2579]) (by decide +kernel)
def pv36107 : PrimeValue := ⟨36107, pr36107⟩
private theorem pr36109 : Nat.Prime 36109 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv59]) (by decide +kernel)
def pv36109 : PrimeValue := ⟨36109, pr36109⟩
private theorem pr36131 : Nat.Prime 36131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv3613]) (by decide +kernel)
def pv36131 : PrimeValue := ⟨36131, pr36131⟩
private theorem pr36137 : Nat.Prime 36137 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv4517]) (by decide +kernel)
def pv36137 : PrimeValue := ⟨36137, pr36137⟩
private theorem pr36151 : Nat.Prime 36151 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv241]) (by decide +kernel)
def pv36151 : PrimeValue := ⟨36151, pr36151⟩
private theorem pr36161 : Nat.Prime 36161 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv113]) (by decide +kernel)
def pv36161 : PrimeValue := ⟨36161, pr36161⟩
private theorem pr36187 : Nat.Prime 36187 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv37,pv163]) (by decide +kernel)
def pv36187 : PrimeValue := ⟨36187, pr36187⟩
private theorem pr36191 : Nat.Prime 36191 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv11,pv47]) (by decide +kernel)
def pv36191 : PrimeValue := ⟨36191, pr36191⟩
private theorem pr36209 : Nat.Prime 36209 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv73]) (by decide +kernel)
def pv36209 : PrimeValue := ⟨36209, pr36209⟩
private theorem pr36217 : Nat.Prime 36217 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv503]) (by decide +kernel)
def pv36217 : PrimeValue := ⟨36217, pr36217⟩
private theorem pr36229 : Nat.Prime 36229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv3019]) (by decide +kernel)
def pv36229 : PrimeValue := ⟨36229, pr36229⟩
private theorem pr36241 : Nat.Prime 36241 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv151]) (by decide +kernel)
def pv36241 : PrimeValue := ⟨36241, pr36241⟩
private theorem pr36251 : Nat.Prime 36251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv29]) (by decide +kernel)
def pv36251 : PrimeValue := ⟨36251, pr36251⟩
private theorem pr36263 : Nat.Prime 36263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv18131]) (by decide +kernel)
def pv36263 : PrimeValue := ⟨36263, pr36263⟩
private theorem pr36269 : Nat.Prime 36269 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv9067]) (by decide +kernel)
def pv36269 : PrimeValue := ⟨36269, pr36269⟩
private theorem pr36277 : Nat.Prime 36277 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv3023]) (by decide +kernel)
def pv36277 : PrimeValue := ⟨36277, pr36277⟩
private theorem pr36293 : Nat.Prime 36293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv211]) (by decide +kernel)
def pv36293 : PrimeValue := ⟨36293, pr36293⟩
private theorem pr36299 : Nat.Prime 36299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv18149]) (by decide +kernel)
def pv36299 : PrimeValue := ⟨36299, pr36299⟩
private theorem pr36307 : Nat.Prime 36307 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2017]) (by decide +kernel)
def pv36307 : PrimeValue := ⟨36307, pr36307⟩
private theorem pr36313 : Nat.Prime 36313 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv89]) (by decide +kernel)
def pv36313 : PrimeValue := ⟨36313, pr36313⟩
private theorem pr36319 : Nat.Prime 36319 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv6053]) (by decide +kernel)
def pv36319 : PrimeValue := ⟨36319, pr36319⟩
private theorem pr36341 : Nat.Prime 36341 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23,pv79]) (by decide +kernel)
def pv36341 : PrimeValue := ⟨36341, pr36341⟩
private theorem pr36343 : Nat.Prime 36343 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv673]) (by decide +kernel)
def pv36343 : PrimeValue := ⟨36343, pr36343⟩
private theorem pr36353 : Nat.Prime 36353 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv71]) (by decide +kernel)
def pv36353 : PrimeValue := ⟨36353, pr36353⟩
private theorem pr36373 : Nat.Prime 36373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv433]) (by decide +kernel)
def pv36373 : PrimeValue := ⟨36373, pr36373⟩
private theorem pr36383 : Nat.Prime 36383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv18191]) (by decide +kernel)
def pv36383 : PrimeValue := ⟨36383, pr36383⟩
private theorem pr36389 : Nat.Prime 36389 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv827]) (by decide +kernel)
def pv36389 : PrimeValue := ⟨36389, pr36389⟩
private theorem pr36433 : Nat.Prime 36433 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv23]) (by decide +kernel)
def pv36433 : PrimeValue := ⟨36433, pr36433⟩
private theorem pr36451 : Nat.Prime 36451 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv36451 : PrimeValue := ⟨36451, pr36451⟩
private theorem pr36457 : Nat.Prime 36457 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv31]) (by decide +kernel)
def pv36457 : PrimeValue := ⟨36457, pr36457⟩
private theorem pr36467 : Nat.Prime 36467 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv18233]) (by decide +kernel)
def pv36467 : PrimeValue := ⟨36467, pr36467⟩
private theorem pr36469 : Nat.Prime 36469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1013]) (by decide +kernel)
def pv36469 : PrimeValue := ⟨36469, pr36469⟩
private theorem pr36473 : Nat.Prime 36473 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv47,pv97]) (by decide +kernel)
def pv36473 : PrimeValue := ⟨36473, pr36473⟩
private theorem pr36479 : Nat.Prime 36479 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv13,pv23,pv61]) (by decide +kernel)
def pv36479 : PrimeValue := ⟨36479, pr36479⟩
private theorem pr36493 : Nat.Prime 36493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv3041]) (by decide +kernel)
def pv36493 : PrimeValue := ⟨36493, pr36493⟩
private theorem pr36497 : Nat.Prime 36497 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2281]) (by decide +kernel)
def pv36497 : PrimeValue := ⟨36497, pr36497⟩
private theorem pr36523 : Nat.Prime 36523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2029]) (by decide +kernel)
def pv36523 : PrimeValue := ⟨36523, pr36523⟩
private theorem pr36527 : Nat.Prime 36527 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv2609]) (by decide +kernel)
def pv36527 : PrimeValue := ⟨36527, pr36527⟩
private theorem pr36529 : Nat.Prime 36529 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv761]) (by decide +kernel)
def pv36529 : PrimeValue := ⟨36529, pr36529⟩
private theorem pr36541 : Nat.Prime 36541 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv7,pv29]) (by decide +kernel)
def pv36541 : PrimeValue := ⟨36541, pr36541⟩
private theorem pr36551 : Nat.Prime 36551 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv17,pv43]) (by decide +kernel)
def pv36551 : PrimeValue := ⟨36551, pr36551⟩
private theorem pr36559 : Nat.Prime 36559 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv677]) (by decide +kernel)
def pv36559 : PrimeValue := ⟨36559, pr36559⟩
private theorem pr36563 : Nat.Prime 36563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv101,pv181]) (by decide +kernel)
def pv36563 : PrimeValue := ⟨36563, pr36563⟩
private theorem pr36571 : Nat.Prime 36571 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv23,pv53]) (by decide +kernel)
def pv36571 : PrimeValue := ⟨36571, pr36571⟩
private theorem pr36583 : Nat.Prime 36583 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv13,pv67]) (by decide +kernel)
def pv36583 : PrimeValue := ⟨36583, pr36583⟩
private theorem pr36587 : Nat.Prime 36587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv1663]) (by decide +kernel)
def pv36587 : PrimeValue := ⟨36587, pr36587⟩
private theorem pr36599 : Nat.Prime 36599 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv29,pv631]) (by decide +kernel)
def pv36599 : PrimeValue := ⟨36599, pr36599⟩
private theorem pr36607 : Nat.Prime 36607 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv6101]) (by decide +kernel)
def pv36607 : PrimeValue := ⟨36607, pr36607⟩
private theorem pr36629 : Nat.Prime 36629 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv9157]) (by decide +kernel)
def pv36629 : PrimeValue := ⟨36629, pr36629⟩
private theorem pr36637 : Nat.Prime 36637 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv43,pv71]) (by decide +kernel)
def pv36637 : PrimeValue := ⟨36637, pr36637⟩
private theorem pr36643 : Nat.Prime 36643 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv31,pv197]) (by decide +kernel)
def pv36643 : PrimeValue := ⟨36643, pr36643⟩
private theorem pr36653 : Nat.Prime 36653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv17]) (by decide +kernel)
def pv36653 : PrimeValue := ⟨36653, pr36653⟩
private theorem pr36671 : Nat.Prime 36671 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv19,pv193]) (by decide +kernel)
def pv36671 : PrimeValue := ⟨36671, pr36671⟩
private theorem pr36677 : Nat.Prime 36677 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53,pv173]) (by decide +kernel)
def pv36677 : PrimeValue := ⟨36677, pr36677⟩
private theorem pr36683 : Nat.Prime 36683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv18341]) (by decide +kernel)
def pv36683 : PrimeValue := ⟨36683, pr36683⟩
private theorem pr36691 : Nat.Prime 36691 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1223]) (by decide +kernel)
def pv36691 : PrimeValue := ⟨36691, pr36691⟩
private theorem pr36697 : Nat.Prime 36697 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv139]) (by decide +kernel)
def pv36697 : PrimeValue := ⟨36697, pr36697⟩
private theorem pr36709 : Nat.Prime 36709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv19,pv23]) (by decide +kernel)
def pv36709 : PrimeValue := ⟨36709, pr36709⟩
private theorem pr36713 : Nat.Prime 36713 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv353]) (by decide +kernel)
def pv36713 : PrimeValue := ⟨36713, pr36713⟩
private theorem pr36721 : Nat.Prime 36721 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv36721 : PrimeValue := ⟨36721, pr36721⟩
private theorem pr36739 : Nat.Prime 36739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv157]) (by decide +kernel)
def pv36739 : PrimeValue := ⟨36739, pr36739⟩
private theorem pr36749 : Nat.Prime 36749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv9187]) (by decide +kernel)
def pv36749 : PrimeValue := ⟨36749, pr36749⟩
private theorem pr36761 : Nat.Prime 36761 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv919]) (by decide +kernel)
def pv36761 : PrimeValue := ⟨36761, pr36761⟩
private theorem pr36767 : Nat.Prime 36767 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv31,pv593]) (by decide +kernel)
def pv36767 : PrimeValue := ⟨36767, pr36767⟩
private theorem pr36779 : Nat.Prime 36779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv37,pv71]) (by decide +kernel)
def pv36779 : PrimeValue := ⟨36779, pr36779⟩
private theorem pr36781 : Nat.Prime 36781 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv613]) (by decide +kernel)
def pv36781 : PrimeValue := ⟨36781, pr36781⟩
private theorem pr36787 : Nat.Prime 36787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv6131]) (by decide +kernel)
def pv36787 : PrimeValue := ⟨36787, pr36787⟩
private theorem pr36791 : Nat.Prime 36791 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv13,pv283]) (by decide +kernel)
def pv36791 : PrimeValue := ⟨36791, pr36791⟩
private theorem pr36793 : Nat.Prime 36793 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv73]) (by decide +kernel)
def pv36793 : PrimeValue := ⟨36793, pr36793⟩
private theorem pr36809 : Nat.Prime 36809 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv43,pv107]) (by decide +kernel)
def pv36809 : PrimeValue := ⟨36809, pr36809⟩
private theorem pr36821 : Nat.Prime 36821 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv263]) (by decide +kernel)
def pv36821 : PrimeValue := ⟨36821, pr36821⟩
private theorem pr36833 : Nat.Prime 36833 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1151]) (by decide +kernel)
def pv36833 : PrimeValue := ⟨36833, pr36833⟩
private theorem pr36847 : Nat.Prime 36847 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv89]) (by decide +kernel)
def pv36847 : PrimeValue := ⟨36847, pr36847⟩
private theorem pr36857 : Nat.Prime 36857 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv271]) (by decide +kernel)
def pv36857 : PrimeValue := ⟨36857, pr36857⟩
private theorem pr36871 : Nat.Prime 36871 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv5,pv1229]) (by decide +kernel)
def pv36871 : PrimeValue := ⟨36871, pr36871⟩
private theorem pr36877 : Nat.Prime 36877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv439]) (by decide +kernel)
def pv36877 : PrimeValue := ⟨36877, pr36877⟩
private theorem pr36887 : Nat.Prime 36887 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv18443]) (by decide +kernel)
def pv36887 : PrimeValue := ⟨36887, pr36887⟩
private theorem pr36899 : Nat.Prime 36899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv971]) (by decide +kernel)
def pv36899 : PrimeValue := ⟨36899, pr36899⟩
private theorem pr36901 : Nat.Prime 36901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv41]) (by decide +kernel)
def pv36901 : PrimeValue := ⟨36901, pr36901⟩
private theorem pr36913 : Nat.Prime 36913 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv769]) (by decide +kernel)
def pv36913 : PrimeValue := ⟨36913, pr36913⟩
private theorem pr36919 : Nat.Prime 36919 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv293]) (by decide +kernel)
def pv36919 : PrimeValue := ⟨36919, pr36919⟩
private theorem pr36923 : Nat.Prime 36923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv18461]) (by decide +kernel)
def pv36923 : PrimeValue := ⟨36923, pr36923⟩
private theorem pr36929 : Nat.Prime 36929 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv577]) (by decide +kernel)
def pv36929 : PrimeValue := ⟨36929, pr36929⟩
private theorem pr36931 : Nat.Prime 36931 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1231]) (by decide +kernel)
def pv36931 : PrimeValue := ⟨36931, pr36931⟩
private theorem pr36943 : Nat.Prime 36943 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv47,pv131]) (by decide +kernel)
def pv36943 : PrimeValue := ⟨36943, pr36943⟩
private theorem pr36947 : Nat.Prime 36947 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv13,pv29]) (by decide +kernel)
def pv36947 : PrimeValue := ⟨36947, pr36947⟩
private theorem pr36973 : Nat.Prime 36973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv79]) (by decide +kernel)
def pv36973 : PrimeValue := ⟨36973, pr36973⟩
private theorem pr36979 : Nat.Prime 36979 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv6163]) (by decide +kernel)
def pv36979 : PrimeValue := ⟨36979, pr36979⟩
private theorem pr36997 : Nat.Prime 36997 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv3083]) (by decide +kernel)
def pv36997 : PrimeValue := ⟨36997, pr36997⟩
private theorem pr37003 : Nat.Prime 37003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv881]) (by decide +kernel)
def pv37003 : PrimeValue := ⟨37003, pr37003⟩
private theorem pr37013 : Nat.Prime 37013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv487]) (by decide +kernel)
def pv37013 : PrimeValue := ⟨37013, pr37013⟩
private theorem pr37019 : Nat.Prime 37019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv83,pv223]) (by decide +kernel)
def pv37019 : PrimeValue := ⟨37019, pr37019⟩
private theorem pr37021 : Nat.Prime 37021 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv617]) (by decide +kernel)
def pv37021 : PrimeValue := ⟨37021, pr37021⟩
private theorem pr37039 : Nat.Prime 37039 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv6173]) (by decide +kernel)
def pv37039 : PrimeValue := ⟨37039, pr37039⟩
private theorem pr37049 : Nat.Prime 37049 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv421]) (by decide +kernel)
def pv37049 : PrimeValue := ⟨37049, pr37049⟩
private theorem pr37057 : Nat.Prime 37057 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv193]) (by decide +kernel)
def pv37057 : PrimeValue := ⟨37057, pr37057⟩
private theorem pr37061 : Nat.Prime 37061 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv109]) (by decide +kernel)
def pv37061 : PrimeValue := ⟨37061, pr37061⟩
private theorem pr37087 : Nat.Prime 37087 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv883]) (by decide +kernel)
def pv37087 : PrimeValue := ⟨37087, pr37087⟩
private theorem pr37097 : Nat.Prime 37097 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv4637]) (by decide +kernel)
def pv37097 : PrimeValue := ⟨37097, pr37097⟩
private theorem pr37117 : Nat.Prime 37117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1031]) (by decide +kernel)
def pv37117 : PrimeValue := ⟨37117, pr37117⟩
private theorem pr37123 : Nat.Prime 37123 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv269]) (by decide +kernel)
def pv37123 : PrimeValue := ⟨37123, pr37123⟩
private theorem pr37139 : Nat.Prime 37139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv599]) (by decide +kernel)
def pv37139 : PrimeValue := ⟨37139, pr37139⟩
private theorem pr37159 : Nat.Prime 37159 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv563]) (by decide +kernel)
def pv37159 : PrimeValue := ⟨37159, pr37159⟩
private theorem pr37171 : Nat.Prime 37171 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv59]) (by decide +kernel)
def pv37171 : PrimeValue := ⟨37171, pr37171⟩
private theorem pr37181 : Nat.Prime 37181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv13]) (by decide +kernel)
def pv37181 : PrimeValue := ⟨37181, pr37181⟩
private theorem pr37189 : Nat.Prime 37189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1033]) (by decide +kernel)
def pv37189 : PrimeValue := ⟨37189, pr37189⟩
private theorem pr37199 : Nat.Prime 37199 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv2657]) (by decide +kernel)
def pv37199 : PrimeValue := ⟨37199, pr37199⟩
private theorem pr37201 : Nat.Prime 37201 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv31]) (by decide +kernel)
def pv37201 : PrimeValue := ⟨37201, pr37201⟩
private theorem pr37217 : Nat.Prime 37217 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1163]) (by decide +kernel)
def pv37217 : PrimeValue := ⟨37217, pr37217⟩
private theorem pr37223 : Nat.Prime 37223 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv37,pv503]) (by decide +kernel)
def pv37223 : PrimeValue := ⟨37223, pr37223⟩
private theorem pr37243 : Nat.Prime 37243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2069]) (by decide +kernel)
def pv37243 : PrimeValue := ⟨37243, pr37243⟩
private theorem pr37253 : Nat.Prime 37253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv67,pv139]) (by decide +kernel)
def pv37253 : PrimeValue := ⟨37253, pr37253⟩
private theorem pr37273 : Nat.Prime 37273 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1553]) (by decide +kernel)
def pv37273 : PrimeValue := ⟨37273, pr37273⟩
private theorem pr37277 : Nat.Prime 37277 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv9319]) (by decide +kernel)
def pv37277 : PrimeValue := ⟨37277, pr37277⟩
private theorem pr37307 : Nat.Prime 37307 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv811]) (by decide +kernel)
def pv37307 : PrimeValue := ⟨37307, pr37307⟩
private theorem pr37309 : Nat.Prime 37309 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv3109]) (by decide +kernel)
def pv37309 : PrimeValue := ⟨37309, pr37309⟩
private theorem pr37313 : Nat.Prime 37313 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv53]) (by decide +kernel)
def pv37313 : PrimeValue := ⟨37313, pr37313⟩
private theorem pr37321 : Nat.Prime 37321 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv311]) (by decide +kernel)
def pv37321 : PrimeValue := ⟨37321, pr37321⟩
private theorem pr37337 : Nat.Prime 37337 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv359]) (by decide +kernel)
def pv37337 : PrimeValue := ⟨37337, pr37337⟩
private theorem pr37339 : Nat.Prime 37339 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv127]) (by decide +kernel)
def pv37339 : PrimeValue := ⟨37339, pr37339⟩
private theorem pr37357 : Nat.Prime 37357 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv283]) (by decide +kernel)
def pv37357 : PrimeValue := ⟨37357, pr37357⟩
private theorem pr37361 : Nat.Prime 37361 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv467]) (by decide +kernel)
def pv37361 : PrimeValue := ⟨37361, pr37361⟩
private theorem pr37363 : Nat.Prime 37363 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv479]) (by decide +kernel)
def pv37363 : PrimeValue := ⟨37363, pr37363⟩
private theorem pr37369 : Nat.Prime 37369 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv173]) (by decide +kernel)
def pv37369 : PrimeValue := ⟨37369, pr37369⟩
private theorem pr37379 : Nat.Prime 37379 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv1699]) (by decide +kernel)
def pv37379 : PrimeValue := ⟨37379, pr37379⟩
private theorem pr37397 : Nat.Prime 37397 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv9349]) (by decide +kernel)
def pv37397 : PrimeValue := ⟨37397, pr37397⟩
private theorem pr37409 : Nat.Prime 37409 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv167]) (by decide +kernel)
def pv37409 : PrimeValue := ⟨37409, pr37409⟩
private theorem pr37423 : Nat.Prime 37423 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv11]) (by decide +kernel)
def pv37423 : PrimeValue := ⟨37423, pr37423⟩
private theorem pr37441 : Nat.Prime 37441 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv37441 : PrimeValue := ⟨37441, pr37441⟩
private theorem pr37447 : Nat.Prime 37447 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv79]) (by decide +kernel)
def pv37447 : PrimeValue := ⟨37447, pr37447⟩
private theorem pr37463 : Nat.Prime 37463 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv18731]) (by decide +kernel)
def pv37463 : PrimeValue := ⟨37463, pr37463⟩
private theorem pr37483 : Nat.Prime 37483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv6247]) (by decide +kernel)
def pv37483 : PrimeValue := ⟨37483, pr37483⟩
private theorem pr37489 : Nat.Prime 37489 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv11,pv71]) (by decide +kernel)
def pv37489 : PrimeValue := ⟨37489, pr37489⟩
private theorem pr37493 : Nat.Prime 37493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv13,pv103]) (by decide +kernel)
def pv37493 : PrimeValue := ⟨37493, pr37493⟩
private theorem pr37501 : Nat.Prime 37501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv37501 : PrimeValue := ⟨37501, pr37501⟩
private theorem pr37507 : Nat.Prime 37507 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv19,pv47]) (by decide +kernel)
def pv37507 : PrimeValue := ⟨37507, pr37507⟩
private theorem pr37511 : Nat.Prime 37511 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv11,pv31]) (by decide +kernel)
def pv37511 : PrimeValue := ⟨37511, pr37511⟩
private theorem pr37517 : Nat.Prime 37517 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv83,pv113]) (by decide +kernel)
def pv37517 : PrimeValue := ⟨37517, pr37517⟩
private theorem pr37529 : Nat.Prime 37529 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv4691]) (by decide +kernel)
def pv37529 : PrimeValue := ⟨37529, pr37529⟩
private theorem pr37537 : Nat.Prime 37537 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv17,pv23]) (by decide +kernel)
def pv37537 : PrimeValue := ⟨37537, pr37537⟩
private theorem pr37547 : Nat.Prime 37547 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv18773]) (by decide +kernel)
def pv37547 : PrimeValue := ⟨37547, pr37547⟩
private theorem pr37549 : Nat.Prime 37549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv149]) (by decide +kernel)
def pv37549 : PrimeValue := ⟨37549, pr37549⟩
private theorem pr37561 : Nat.Prime 37561 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv313]) (by decide +kernel)
def pv37561 : PrimeValue := ⟨37561, pr37561⟩
private theorem pr37567 : Nat.Prime 37567 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv2087]) (by decide +kernel)
def pv37567 : PrimeValue := ⟨37567, pr37567⟩
private theorem pr37571 : Nat.Prime 37571 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv17]) (by decide +kernel)
def pv37571 : PrimeValue := ⟨37571, pr37571⟩
private theorem pr37573 : Nat.Prime 37573 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv31,pv101]) (by decide +kernel)
def pv37573 : PrimeValue := ⟨37573, pr37573⟩
private theorem pr37579 : Nat.Prime 37579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv6263]) (by decide +kernel)
def pv37579 : PrimeValue := ⟨37579, pr37579⟩
private theorem pr37589 : Nat.Prime 37589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv9397]) (by decide +kernel)
def pv37589 : PrimeValue := ⟨37589, pr37589⟩
private theorem pr37591 : Nat.Prime 37591 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv179]) (by decide +kernel)
def pv37591 : PrimeValue := ⟨37591, pr37591⟩
private theorem pr37607 : Nat.Prime 37607 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv18803]) (by decide +kernel)
def pv37607 : PrimeValue := ⟨37607, pr37607⟩
private theorem pr37619 : Nat.Prime 37619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv2687]) (by decide +kernel)
def pv37619 : PrimeValue := ⟨37619, pr37619⟩
private theorem pr37633 : Nat.Prime 37633 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv37633 : PrimeValue := ⟨37633, pr37633⟩
private theorem pr37643 : Nat.Prime 37643 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv29,pv59]) (by decide +kernel)
def pv37643 : PrimeValue := ⟨37643, pr37643⟩
private theorem pr37649 : Nat.Prime 37649 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv181]) (by decide +kernel)
def pv37649 : PrimeValue := ⟨37649, pr37649⟩
private theorem pr37657 : Nat.Prime 37657 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv523]) (by decide +kernel)
def pv37657 : PrimeValue := ⟨37657, pr37657⟩
private theorem pr37663 : Nat.Prime 37663 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv6277]) (by decide +kernel)
def pv37663 : PrimeValue := ⟨37663, pr37663⟩
private theorem pr37691 : Nat.Prime 37691 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv3769]) (by decide +kernel)
def pv37691 : PrimeValue := ⟨37691, pr37691⟩
private theorem pr37693 : Nat.Prime 37693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv349]) (by decide +kernel)
def pv37693 : PrimeValue := ⟨37693, pr37693⟩
private theorem pr37699 : Nat.Prime 37699 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv61,pv103]) (by decide +kernel)
def pv37699 : PrimeValue := ⟨37699, pr37699⟩
private theorem pr37717 : Nat.Prime 37717 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv449]) (by decide +kernel)
def pv37717 : PrimeValue := ⟨37717, pr37717⟩
private theorem pr37747 : Nat.Prime 37747 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv233]) (by decide +kernel)
def pv37747 : PrimeValue := ⟨37747, pr37747⟩
private theorem pr37781 : Nat.Prime 37781 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1889]) (by decide +kernel)
def pv37781 : PrimeValue := ⟨37781, pr37781⟩
private theorem pr37783 : Nat.Prime 37783 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv2099]) (by decide +kernel)
def pv37783 : PrimeValue := ⟨37783, pr37783⟩
private theorem pr37799 : Nat.Prime 37799 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv18899]) (by decide +kernel)
def pv37799 : PrimeValue := ⟨37799, pr37799⟩
private theorem pr37811 : Nat.Prime 37811 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv19,pv199]) (by decide +kernel)
def pv37811 : PrimeValue := ⟨37811, pr37811⟩
private theorem pr37813 : Nat.Prime 37813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv137]) (by decide +kernel)
def pv37813 : PrimeValue := ⟨37813, pr37813⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
