/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table058
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table058.pv168913
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table007
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table012
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table032
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table033

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr168913 : Nat.Prime 168913 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv17,pv23]) (by decide +kernel)
def pv168913 : PrimeValue := ⟨168913, pr168913⟩
private theorem pr168937 : Nat.Prime 168937 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7039]) (by decide +kernel)
def pv168937 : PrimeValue := ⟨168937, pr168937⟩
private theorem pr168943 : Nat.Prime 168943 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv37,pv761]) (by decide +kernel)
def pv168943 : PrimeValue := ⟨168943, pr168943⟩
private theorem pr168977 : Nat.Prime 168977 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv59,pv179]) (by decide +kernel)
def pv168977 : PrimeValue := ⟨168977, pr168977⟩
private theorem pr168991 : Nat.Prime 168991 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv43,pv131]) (by decide +kernel)
def pv168991 : PrimeValue := ⟨168991, pr168991⟩
private theorem pr169003 : Nat.Prime 169003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv41,pv229]) (by decide +kernel)
def pv169003 : PrimeValue := ⟨169003, pr169003⟩
private theorem pr169007 : Nat.Prime 169007 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv84503]) (by decide +kernel)
def pv169007 : PrimeValue := ⟨169007, pr169007⟩
private theorem pr169009 : Nat.Prime 169009 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv503]) (by decide +kernel)
def pv169009 : PrimeValue := ⟨169009, pr169009⟩
private theorem pr169019 : Nat.Prime 169019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv84509]) (by decide +kernel)
def pv169019 : PrimeValue := ⟨169019, pr169019⟩
private theorem pr169049 : Nat.Prime 169049 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv17,pv113]) (by decide +kernel)
def pv169049 : PrimeValue := ⟨169049, pr169049⟩
private theorem pr169063 : Nat.Prime 169063 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv1483]) (by decide +kernel)
def pv169063 : PrimeValue := ⟨169063, pr169063⟩
private theorem pr169067 : Nat.Prime 169067 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv84533]) (by decide +kernel)
def pv169067 : PrimeValue := ⟨169067, pr169067⟩
private theorem pr169069 : Nat.Prime 169069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv73,pv193]) (by decide +kernel)
def pv169069 : PrimeValue := ⟨169069, pr169069⟩
private theorem pr169079 : Nat.Prime 169079 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv7,pv13,pv929]) (by decide +kernel)
def pv169079 : PrimeValue := ⟨169079, pr169079⟩
private theorem pr169093 : Nat.Prime 169093 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv11,pv61]) (by decide +kernel)
def pv169093 : PrimeValue := ⟨169093, pr169093⟩
private theorem pr169097 : Nat.Prime 169097 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv919]) (by decide +kernel)
def pv169097 : PrimeValue := ⟨169097, pr169097⟩
private theorem pr169129 : Nat.Prime 169129 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv29]) (by decide +kernel)
def pv169129 : PrimeValue := ⟨169129, pr169129⟩
private theorem pr169151 : Nat.Prime 169151 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv17,pv199]) (by decide +kernel)
def pv169151 : PrimeValue := ⟨169151, pr169151⟩
private theorem pr169159 : Nat.Prime 169159 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv233]) (by decide +kernel)
def pv169159 : PrimeValue := ⟨169159, pr169159⟩
private theorem pr169177 : Nat.Prime 169177 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv19,pv53]) (by decide +kernel)
def pv169177 : PrimeValue := ⟨169177, pr169177⟩
private theorem pr169181 : Nat.Prime 169181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv769]) (by decide +kernel)
def pv169181 : PrimeValue := ⟨169181, pr169181⟩
private theorem pr169199 : Nat.Prime 169199 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv31,pv2729]) (by decide +kernel)
def pv169199 : PrimeValue := ⟨169199, pr169199⟩
private theorem pr169219 : Nat.Prime 169219 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv79]) (by decide +kernel)
def pv169219 : PrimeValue := ⟨169219, pr169219⟩
private theorem pr169243 : Nat.Prime 169243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv67,pv421]) (by decide +kernel)
def pv169243 : PrimeValue := ⟨169243, pr169243⟩
private theorem pr169259 : Nat.Prime 169259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv84629]) (by decide +kernel)
def pv169259 : PrimeValue := ⟨169259, pr169259⟩
private theorem pr169283 : Nat.Prime 169283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53,pv1597]) (by decide +kernel)
def pv169283 : PrimeValue := ⟨169283, pr169283⟩
private theorem pr169307 : Nat.Prime 169307 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv84653]) (by decide +kernel)
def pv169307 : PrimeValue := ⟨169307, pr169307⟩
private theorem pr169313 : Nat.Prime 169313 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv13,pv37]) (by decide +kernel)
def pv169313 : PrimeValue := ⟨169313, pr169313⟩
private theorem pr169327 : Nat.Prime 169327 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv409]) (by decide +kernel)
def pv169327 : PrimeValue := ⟨169327, pr169327⟩
private theorem pr169339 : Nat.Prime 169339 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv167]) (by decide +kernel)
def pv169339 : PrimeValue := ⟨169339, pr169339⟩
private theorem pr169343 : Nat.Prime 169343 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv227,pv373]) (by decide +kernel)
def pv169343 : PrimeValue := ⟨169343, pr169343⟩
private theorem pr169361 : Nat.Prime 169361 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv29,pv73]) (by decide +kernel)
def pv169361 : PrimeValue := ⟨169361, pr169361⟩
private theorem pr169369 : Nat.Prime 169369 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7057]) (by decide +kernel)
def pv169369 : PrimeValue := ⟨169369, pr169369⟩
private theorem pr169373 : Nat.Prime 169373 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv23,pv263]) (by decide +kernel)
def pv169373 : PrimeValue := ⟨169373, pr169373⟩
private theorem pr169399 : Nat.Prime 169399 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv3137]) (by decide +kernel)
def pv169399 : PrimeValue := ⟨169399, pr169399⟩
private theorem pr169409 : Nat.Prime 169409 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2647]) (by decide +kernel)
def pv169409 : PrimeValue := ⟨169409, pr169409⟩
private theorem pr169457 : Nat.Prime 169457 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv7,pv17,pv89]) (by decide +kernel)
def pv169457 : PrimeValue := ⟨169457, pr169457⟩
private theorem pr169471 : Nat.Prime 169471 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv269]) (by decide +kernel)
def pv169471 : PrimeValue := ⟨169471, pr169471⟩
private theorem pr169483 : Nat.Prime 169483 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv47,pv601]) (by decide +kernel)
def pv169483 : PrimeValue := ⟨169483, pr169483⟩
private theorem pr169489 : Nat.Prime 169489 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv11,pv107]) (by decide +kernel)
def pv169489 : PrimeValue := ⟨169489, pr169489⟩
private theorem pr169493 : Nat.Prime 169493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv42373]) (by decide +kernel)
def pv169493 : PrimeValue := ⟨169493, pr169493⟩
private theorem pr169501 : Nat.Prime 169501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv113]) (by decide +kernel)
def pv169501 : PrimeValue := ⟨169501, pr169501⟩
private theorem pr169523 : Nat.Prime 169523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv84761]) (by decide +kernel)
def pv169523 : PrimeValue := ⟨169523, pr169523⟩
private theorem pr169553 : Nat.Prime 169553 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv10597]) (by decide +kernel)
def pv169553 : PrimeValue := ⟨169553, pr169553⟩
private theorem pr169567 : Nat.Prime 169567 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv59,pv479]) (by decide +kernel)
def pv169567 : PrimeValue := ⟨169567, pr169567⟩
private theorem pr169583 : Nat.Prime 169583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv12113]) (by decide +kernel)
def pv169583 : PrimeValue := ⟨169583, pr169583⟩
private theorem pr169591 : Nat.Prime 169591 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv5653]) (by decide +kernel)
def pv169591 : PrimeValue := ⟨169591, pr169591⟩
private theorem pr169607 : Nat.Prime 169607 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv137,pv619]) (by decide +kernel)
def pv169607 : PrimeValue := ⟨169607, pr169607⟩
private theorem pr169633 : Nat.Prime 169633 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv31]) (by decide +kernel)
def pv169633 : PrimeValue := ⟨169633, pr169633⟩
private theorem pr169639 : Nat.Prime 169639 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv577]) (by decide +kernel)
def pv169639 : PrimeValue := ⟨169639, pr169639⟩
private theorem pr169649 : Nat.Prime 169649 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv461]) (by decide +kernel)
def pv169649 : PrimeValue := ⟨169649, pr169649⟩
private theorem pr169657 : Nat.Prime 169657 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7069]) (by decide +kernel)
def pv169657 : PrimeValue := ⟨169657, pr169657⟩
private theorem pr169661 : Nat.Prime 169661 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17,pv499]) (by decide +kernel)
def pv169661 : PrimeValue := ⟨169661, pr169661⟩
private theorem pr169667 : Nat.Prime 169667 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv12119]) (by decide +kernel)
def pv169667 : PrimeValue := ⟨169667, pr169667⟩
private theorem pr169681 : Nat.Prime 169681 :=
  checkPrime_prime (q := pv47) (ls := [pv2,pv3,pv5,pv7,pv101]) (by decide +kernel)
def pv169681 : PrimeValue := ⟨169681, pr169681⟩
private theorem pr169691 : Nat.Prime 169691 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv71,pv239]) (by decide +kernel)
def pv169691 : PrimeValue := ⟨169691, pr169691⟩
private theorem pr169693 : Nat.Prime 169693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv79,pv179]) (by decide +kernel)
def pv169693 : PrimeValue := ⟨169693, pr169693⟩
private theorem pr169709 : Nat.Prime 169709 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv7,pv11,pv19,pv29]) (by decide +kernel)
def pv169709 : PrimeValue := ⟨169709, pr169709⟩
private theorem pr169733 : Nat.Prime 169733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv42433]) (by decide +kernel)
def pv169733 : PrimeValue := ⟨169733, pr169733⟩
private theorem pr169751 : Nat.Prime 169751 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv7,pv97]) (by decide +kernel)
def pv169751 : PrimeValue := ⟨169751, pr169751⟩
private theorem pr169753 : Nat.Prime 169753 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv643]) (by decide +kernel)
def pv169753 : PrimeValue := ⟨169753, pr169753⟩
private theorem pr169769 : Nat.Prime 169769 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv21221]) (by decide +kernel)
def pv169769 : PrimeValue := ⟨169769, pr169769⟩
private theorem pr169777 : Nat.Prime 169777 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv131]) (by decide +kernel)
def pv169777 : PrimeValue := ⟨169777, pr169777⟩
private theorem pr169789 : Nat.Prime 169789 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv14149]) (by decide +kernel)
def pv169789 : PrimeValue := ⟨169789, pr169789⟩
private theorem pr169817 : Nat.Prime 169817 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv21227]) (by decide +kernel)
def pv169817 : PrimeValue := ⟨169817, pr169817⟩
private theorem pr169823 : Nat.Prime 169823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv41,pv109]) (by decide +kernel)
def pv169823 : PrimeValue := ⟨169823, pr169823⟩
private theorem pr169831 : Nat.Prime 169831 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv17,pv37]) (by decide +kernel)
def pv169831 : PrimeValue := ⟨169831, pr169831⟩
private theorem pr169837 : Nat.Prime 169837 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv14153]) (by decide +kernel)
def pv169837 : PrimeValue := ⟨169837, pr169837⟩
private theorem pr169843 : Nat.Prime 169843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv28307]) (by decide +kernel)
def pv169843 : PrimeValue := ⟨169843, pr169843⟩
private theorem pr169889 : Nat.Prime 169889 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5309]) (by decide +kernel)
def pv169889 : PrimeValue := ⟨169889, pr169889⟩
private theorem pr169891 : Nat.Prime 169891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv809]) (by decide +kernel)
def pv169891 : PrimeValue := ⟨169891, pr169891⟩
private theorem pr169909 : Nat.Prime 169909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv14159]) (by decide +kernel)
def pv169909 : PrimeValue := ⟨169909, pr169909⟩
private theorem pr169913 : Nat.Prime 169913 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv67,pv317]) (by decide +kernel)
def pv169913 : PrimeValue := ⟨169913, pr169913⟩
private theorem pr169919 : Nat.Prime 169919 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv53,pv229]) (by decide +kernel)
def pv169919 : PrimeValue := ⟨169919, pr169919⟩
private theorem pr169933 : Nat.Prime 169933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv17]) (by decide +kernel)
def pv169933 : PrimeValue := ⟨169933, pr169933⟩
private theorem pr169937 : Nat.Prime 169937 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv19,pv43]) (by decide +kernel)
def pv169937 : PrimeValue := ⟨169937, pr169937⟩
private theorem pr169943 : Nat.Prime 169943 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv31,pv2741]) (by decide +kernel)
def pv169943 : PrimeValue := ⟨169943, pr169943⟩
private theorem pr169957 : Nat.Prime 169957 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4721]) (by decide +kernel)
def pv169957 : PrimeValue := ⟨169957, pr169957⟩
private theorem pr169987 : Nat.Prime 169987 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv41,pv691]) (by decide +kernel)
def pv169987 : PrimeValue := ⟨169987, pr169987⟩
private theorem pr169991 : Nat.Prime 169991 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv5,pv89,pv191]) (by decide +kernel)
def pv169991 : PrimeValue := ⟨169991, pr169991⟩
private theorem pr170003 : Nat.Prime 170003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv12143]) (by decide +kernel)
def pv170003 : PrimeValue := ⟨170003, pr170003⟩
private theorem pr170021 : Nat.Prime 170021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv8501]) (by decide +kernel)
def pv170021 : PrimeValue := ⟨170021, pr170021⟩
private theorem pr170047 : Nat.Prime 170047 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv47,pv67]) (by decide +kernel)
def pv170047 : PrimeValue := ⟨170047, pr170047⟩
private theorem pr170057 : Nat.Prime 170057 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv733]) (by decide +kernel)
def pv170057 : PrimeValue := ⟨170057, pr170057⟩
private theorem pr170063 : Nat.Prime 170063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv23,pv3697]) (by decide +kernel)
def pv170063 : PrimeValue := ⟨170063, pr170063⟩
private theorem pr170081 : Nat.Prime 170081 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv1063]) (by decide +kernel)
def pv170081 : PrimeValue := ⟨170081, pr170081⟩
private theorem pr170099 : Nat.Prime 170099 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv85049]) (by decide +kernel)
def pv170099 : PrimeValue := ⟨170099, pr170099⟩
private theorem pr170111 : Nat.Prime 170111 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv17011]) (by decide +kernel)
def pv170111 : PrimeValue := ⟨170111, pr170111⟩
private theorem pr170123 : Nat.Prime 170123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv85061]) (by decide +kernel)
def pv170123 : PrimeValue := ⟨170123, pr170123⟩
private theorem pr170141 : Nat.Prime 170141 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv47,pv181]) (by decide +kernel)
def pv170141 : PrimeValue := ⟨170141, pr170141⟩
private theorem pr170179 : Nat.Prime 170179 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv113,pv251]) (by decide +kernel)
def pv170179 : PrimeValue := ⟨170179, pr170179⟩
private theorem pr170197 : Nat.Prime 170197 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv1091]) (by decide +kernel)
def pv170197 : PrimeValue := ⟨170197, pr170197⟩
private theorem pr170207 : Nat.Prime 170207 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv85103]) (by decide +kernel)
def pv170207 : PrimeValue := ⟨170207, pr170207⟩
private theorem pr170231 : Nat.Prime 170231 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv29,pv587]) (by decide +kernel)
def pv170231 : PrimeValue := ⟨170231, pr170231⟩
private theorem pr170249 : Nat.Prime 170249 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv1637]) (by decide +kernel)
def pv170249 : PrimeValue := ⟨170249, pr170249⟩
private theorem pr170263 : Nat.Prime 170263 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv1051]) (by decide +kernel)
def pv170263 : PrimeValue := ⟨170263, pr170263⟩
private theorem pr170267 : Nat.Prime 170267 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv85133]) (by decide +kernel)
def pv170267 : PrimeValue := ⟨170267, pr170267⟩
private theorem pr170279 : Nat.Prime 170279 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv19,pv4481]) (by decide +kernel)
def pv170279 : PrimeValue := ⟨170279, pr170279⟩
private theorem pr170293 : Nat.Prime 170293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv617]) (by decide +kernel)
def pv170293 : PrimeValue := ⟨170293, pr170293⟩
private theorem pr170299 : Nat.Prime 170299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv9461]) (by decide +kernel)
def pv170299 : PrimeValue := ⟨170299, pr170299⟩
private theorem pr170327 : Nat.Prime 170327 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv6551]) (by decide +kernel)
def pv170327 : PrimeValue := ⟨170327, pr170327⟩
private theorem pr170347 : Nat.Prime 170347 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv29,pv89]) (by decide +kernel)
def pv170347 : PrimeValue := ⟨170347, pr170347⟩
private theorem pr170351 : Nat.Prime 170351 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv3407]) (by decide +kernel)
def pv170351 : PrimeValue := ⟨170351, pr170351⟩
private theorem pr170353 : Nat.Prime 170353 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv13]) (by decide +kernel)
def pv170353 : PrimeValue := ⟨170353, pr170353⟩
private theorem pr170363 : Nat.Prime 170363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv103,pv827]) (by decide +kernel)
def pv170363 : PrimeValue := ⟨170363, pr170363⟩
private theorem pr170389 : Nat.Prime 170389 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4733]) (by decide +kernel)
def pv170389 : PrimeValue := ⟨170389, pr170389⟩
private theorem pr170393 : Nat.Prime 170393 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv59]) (by decide +kernel)
def pv170393 : PrimeValue := ⟨170393, pr170393⟩
private theorem pr170447 : Nat.Prime 170447 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv85223]) (by decide +kernel)
def pv170447 : PrimeValue := ⟨170447, pr170447⟩
private theorem pr170473 : Nat.Prime 170473 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7103]) (by decide +kernel)
def pv170473 : PrimeValue := ⟨170473, pr170473⟩
private theorem pr170483 : Nat.Prime 170483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv79,pv83]) (by decide +kernel)
def pv170483 : PrimeValue := ⟨170483, pr170483⟩
private theorem pr170497 : Nat.Prime 170497 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv37]) (by decide +kernel)
def pv170497 : PrimeValue := ⟨170497, pr170497⟩
private theorem pr170503 : Nat.Prime 170503 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv157,pv181]) (by decide +kernel)
def pv170503 : PrimeValue := ⟨170503, pr170503⟩
private theorem pr170509 : Nat.Prime 170509 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv1093]) (by decide +kernel)
def pv170509 : PrimeValue := ⟨170509, pr170509⟩
private theorem pr170537 : Nat.Prime 170537 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv21317]) (by decide +kernel)
def pv170537 : PrimeValue := ⟨170537, pr170537⟩
private theorem pr170539 : Nat.Prime 170539 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv43,pv661]) (by decide +kernel)
def pv170539 : PrimeValue := ⟨170539, pr170539⟩
private theorem pr170557 : Nat.Prime 170557 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv61,pv233]) (by decide +kernel)
def pv170557 : PrimeValue := ⟨170557, pr170557⟩
private theorem pr170579 : Nat.Prime 170579 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv17,pv29,pv173]) (by decide +kernel)
def pv170579 : PrimeValue := ⟨170579, pr170579⟩
private theorem pr170603 : Nat.Prime 170603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv197,pv433]) (by decide +kernel)
def pv170603 : PrimeValue := ⟨170603, pr170603⟩
private theorem pr170609 : Nat.Prime 170609 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv10663]) (by decide +kernel)
def pv170609 : PrimeValue := ⟨170609, pr170609⟩
private theorem pr170627 : Nat.Prime 170627 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv85313]) (by decide +kernel)
def pv170627 : PrimeValue := ⟨170627, pr170627⟩
private theorem pr170633 : Nat.Prime 170633 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv11,pv277]) (by decide +kernel)
def pv170633 : PrimeValue := ⟨170633, pr170633⟩
private theorem pr170641 : Nat.Prime 170641 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv79]) (by decide +kernel)
def pv170641 : PrimeValue := ⟨170641, pr170641⟩
private theorem pr170647 : Nat.Prime 170647 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv17,pv239]) (by decide +kernel)
def pv170647 : PrimeValue := ⟨170647, pr170647⟩
private theorem pr170669 : Nat.Prime 170669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv42667]) (by decide +kernel)
def pv170669 : PrimeValue := ⟨170669, pr170669⟩
private theorem pr170689 : Nat.Prime 170689 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv7,pv127]) (by decide +kernel)
def pv170689 : PrimeValue := ⟨170689, pr170689⟩
private theorem pr170701 : Nat.Prime 170701 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv569]) (by decide +kernel)
def pv170701 : PrimeValue := ⟨170701, pr170701⟩
private theorem pr170707 : Nat.Prime 170707 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv1237]) (by decide +kernel)
def pv170707 : PrimeValue := ⟨170707, pr170707⟩
private theorem pr170711 : Nat.Prime 170711 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv43,pv397]) (by decide +kernel)
def pv170711 : PrimeValue := ⟨170711, pr170711⟩
private theorem pr170761 : Nat.Prime 170761 :=
  checkPrime_prime (q := pv43) (ls := [pv2,pv3,pv5,pv1423]) (by decide +kernel)
def pv170761 : PrimeValue := ⟨170761, pr170761⟩
private theorem pr170767 : Nat.Prime 170767 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv53,pv179]) (by decide +kernel)
def pv170767 : PrimeValue := ⟨170767, pr170767⟩
private theorem pr170777 : Nat.Prime 170777 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv21347]) (by decide +kernel)
def pv170777 : PrimeValue := ⟨170777, pr170777⟩
private theorem pr170801 : Nat.Prime 170801 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv61]) (by decide +kernel)
def pv170801 : PrimeValue := ⟨170801, pr170801⟩
private theorem pr170827 : Nat.Prime 170827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv71,pv401]) (by decide +kernel)
def pv170827 : PrimeValue := ⟨170827, pr170827⟩
private theorem pr170837 : Nat.Prime 170837 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv42709]) (by decide +kernel)
def pv170837 : PrimeValue := ⟨170837, pr170837⟩
private theorem pr170843 : Nat.Prime 170843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv12203]) (by decide +kernel)
def pv170843 : PrimeValue := ⟨170843, pr170843⟩
private theorem pr170857 : Nat.Prime 170857 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv113]) (by decide +kernel)
def pv170857 : PrimeValue := ⟨170857, pr170857⟩
private theorem pr170873 : Nat.Prime 170873 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv31,pv53]) (by decide +kernel)
def pv170873 : PrimeValue := ⟨170873, pr170873⟩
private theorem pr170881 : Nat.Prime 170881 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv89]) (by decide +kernel)
def pv170881 : PrimeValue := ⟨170881, pr170881⟩
private theorem pr170887 : Nat.Prime 170887 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv1499]) (by decide +kernel)
def pv170887 : PrimeValue := ⟨170887, pr170887⟩
private theorem pr170899 : Nat.Prime 170899 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv313]) (by decide +kernel)
def pv170899 : PrimeValue := ⟨170899, pr170899⟩
private theorem pr170927 : Nat.Prime 170927 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv29,pv421]) (by decide +kernel)
def pv170927 : PrimeValue := ⟨170927, pr170927⟩
private theorem pr170953 : Nat.Prime 170953 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv17,pv419]) (by decide +kernel)
def pv170953 : PrimeValue := ⟨170953, pr170953⟩
private theorem pr170971 : Nat.Prime 170971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv41,pv139]) (by decide +kernel)
def pv170971 : PrimeValue := ⟨170971, pr170971⟩
private theorem pr171007 : Nat.Prime 171007 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv2591]) (by decide +kernel)
def pv171007 : PrimeValue := ⟨171007, pr171007⟩
private theorem pr171023 : Nat.Prime 171023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv233,pv367]) (by decide +kernel)
def pv171023 : PrimeValue := ⟨171023, pr171023⟩
private theorem pr171029 : Nat.Prime 171029 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv13,pv23]) (by decide +kernel)
def pv171029 : PrimeValue := ⟨171029, pr171029⟩
private theorem pr171043 : Nat.Prime 171043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv983]) (by decide +kernel)
def pv171043 : PrimeValue := ⟨171043, pr171043⟩
private theorem pr171047 : Nat.Prime 171047 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv85523]) (by decide +kernel)
def pv171047 : PrimeValue := ⟨171047, pr171047⟩
private theorem pr171049 : Nat.Prime 171049 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7127]) (by decide +kernel)
def pv171049 : PrimeValue := ⟨171049, pr171049⟩
private theorem pr171053 : Nat.Prime 171053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv41,pv149]) (by decide +kernel)
def pv171053 : PrimeValue := ⟨171053, pr171053⟩
private theorem pr171077 : Nat.Prime 171077 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv2251]) (by decide +kernel)
def pv171077 : PrimeValue := ⟨171077, pr171077⟩
private theorem pr171079 : Nat.Prime 171079 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv28513]) (by decide +kernel)
def pv171079 : PrimeValue := ⟨171079, pr171079⟩
private theorem pr171091 : Nat.Prime 171091 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1901]) (by decide +kernel)
def pv171091 : PrimeValue := ⟨171091, pr171091⟩
private theorem pr171103 : Nat.Prime 171103 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv28517]) (by decide +kernel)
def pv171103 : PrimeValue := ⟨171103, pr171103⟩
private theorem pr171131 : Nat.Prime 171131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv109,pv157]) (by decide +kernel)
def pv171131 : PrimeValue := ⟨171131, pr171131⟩
private theorem pr171163 : Nat.Prime 171163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv257]) (by decide +kernel)
def pv171163 : PrimeValue := ⟨171163, pr171163⟩
private theorem pr171167 : Nat.Prime 171167 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv23,pv61]) (by decide +kernel)
def pv171167 : PrimeValue := ⟨171167, pr171167⟩
private theorem pr171179 : Nat.Prime 171179 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv12227]) (by decide +kernel)
def pv171179 : PrimeValue := ⟨171179, pr171179⟩
private theorem pr171203 : Nat.Prime 171203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv85601]) (by decide +kernel)
def pv171203 : PrimeValue := ⟨171203, pr171203⟩
private theorem pr171233 : Nat.Prime 171233 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5351]) (by decide +kernel)
def pv171233 : PrimeValue := ⟨171233, pr171233⟩
private theorem pr171251 : Nat.Prime 171251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv137]) (by decide +kernel)
def pv171251 : PrimeValue := ⟨171251, pr171251⟩
private theorem pr171253 : Nat.Prime 171253 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv67,pv71]) (by decide +kernel)
def pv171253 : PrimeValue := ⟨171253, pr171253⟩
private theorem pr171263 : Nat.Prime 171263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv13,pv941]) (by decide +kernel)
def pv171263 : PrimeValue := ⟨171263, pr171263⟩
private theorem pr171271 : Nat.Prime 171271 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv173]) (by decide +kernel)
def pv171271 : PrimeValue := ⟨171271, pr171271⟩
private theorem pr171293 : Nat.Prime 171293 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv17,pv229]) (by decide +kernel)
def pv171293 : PrimeValue := ⟨171293, pr171293⟩
private theorem pr171299 : Nat.Prime 171299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv2089]) (by decide +kernel)
def pv171299 : PrimeValue := ⟨171299, pr171299⟩
private theorem pr171329 : Nat.Prime 171329 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2677]) (by decide +kernel)
def pv171329 : PrimeValue := ⟨171329, pr171329⟩
private theorem pr171341 : Nat.Prime 171341 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv659]) (by decide +kernel)
def pv171341 : PrimeValue := ⟨171341, pr171341⟩
private theorem pr171383 : Nat.Prime 171383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv85691]) (by decide +kernel)
def pv171383 : PrimeValue := ⟨171383, pr171383⟩
private theorem pr171401 : Nat.Prime 171401 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv857]) (by decide +kernel)
def pv171401 : PrimeValue := ⟨171401, pr171401⟩
private theorem pr171403 : Nat.Prime 171403 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv7,pv11,pv53]) (by decide +kernel)
def pv171403 : PrimeValue := ⟨171403, pr171403⟩
private theorem pr171439 : Nat.Prime 171439 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv28573]) (by decide +kernel)
def pv171439 : PrimeValue := ⟨171439, pr171439⟩
private theorem pr171449 : Nat.Prime 171449 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv739]) (by decide +kernel)
def pv171449 : PrimeValue := ⟨171449, pr171449⟩
private theorem pr171467 : Nat.Prime 171467 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv85733]) (by decide +kernel)
def pv171467 : PrimeValue := ⟨171467, pr171467⟩
private theorem pr171473 : Nat.Prime 171473 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv1531]) (by decide +kernel)
def pv171473 : PrimeValue := ⟨171473, pr171473⟩
private theorem pr171491 : Nat.Prime 171491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv1559]) (by decide +kernel)
def pv171491 : PrimeValue := ⟨171491, pr171491⟩
private theorem pr171517 : Nat.Prime 171517 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv14293]) (by decide +kernel)
def pv171517 : PrimeValue := ⟨171517, pr171517⟩
private theorem pr171529 : Nat.Prime 171529 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv1021]) (by decide +kernel)
def pv171529 : PrimeValue := ⟨171529, pr171529⟩
private theorem pr171539 : Nat.Prime 171539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv199,pv431]) (by decide +kernel)
def pv171539 : PrimeValue := ⟨171539, pr171539⟩
private theorem pr171541 : Nat.Prime 171541 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv953]) (by decide +kernel)
def pv171541 : PrimeValue := ⟨171541, pr171541⟩
private theorem pr171571 : Nat.Prime 171571 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv19,pv43]) (by decide +kernel)
def pv171571 : PrimeValue := ⟨171571, pr171571⟩
private theorem pr171583 : Nat.Prime 171583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv28597]) (by decide +kernel)
def pv171583 : PrimeValue := ⟨171583, pr171583⟩
private theorem pr171617 : Nat.Prime 171617 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv173]) (by decide +kernel)
def pv171617 : PrimeValue := ⟨171617, pr171617⟩
private theorem pr171629 : Nat.Prime 171629 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv107,pv401]) (by decide +kernel)
def pv171629 : PrimeValue := ⟨171629, pr171629⟩
private theorem pr171637 : Nat.Prime 171637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv14303]) (by decide +kernel)
def pv171637 : PrimeValue := ⟨171637, pr171637⟩
private theorem pr171641 : Nat.Prime 171641 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv613]) (by decide +kernel)
def pv171641 : PrimeValue := ⟨171641, pr171641⟩
private theorem pr171653 : Nat.Prime 171653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv3301]) (by decide +kernel)
def pv171653 : PrimeValue := ⟨171653, pr171653⟩
private theorem pr171671 : Nat.Prime 171671 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv17167]) (by decide +kernel)
def pv171671 : PrimeValue := ⟨171671, pr171671⟩
private theorem pr171673 : Nat.Prime 171673 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv23,pv311]) (by decide +kernel)
def pv171673 : PrimeValue := ⟨171673, pr171673⟩
private theorem pr171679 : Nat.Prime 171679 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv3,pv13,pv31,pv71]) (by decide +kernel)
def pv171679 : PrimeValue := ⟨171679, pr171679⟩
private theorem pr171697 : Nat.Prime 171697 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv7,pv73]) (by decide +kernel)
def pv171697 : PrimeValue := ⟨171697, pr171697⟩
private theorem pr171707 : Nat.Prime 171707 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv85853]) (by decide +kernel)
def pv171707 : PrimeValue := ⟨171707, pr171707⟩
private theorem pr171719 : Nat.Prime 171719 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv23,pv3733]) (by decide +kernel)
def pv171719 : PrimeValue := ⟨171719, pr171719⟩
private theorem pr171757 : Nat.Prime 171757 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv367]) (by decide +kernel)
def pv171757 : PrimeValue := ⟨171757, pr171757⟩
private theorem pr171761 : Nat.Prime 171761 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv19,pv113]) (by decide +kernel)
def pv171761 : PrimeValue := ⟨171761, pr171761⟩
private theorem pr171763 : Nat.Prime 171763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv28627]) (by decide +kernel)
def pv171763 : PrimeValue := ⟨171763, pr171763⟩
private theorem pr171793 : Nat.Prime 171793 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1193]) (by decide +kernel)
def pv171793 : PrimeValue := ⟨171793, pr171793⟩
private theorem pr171799 : Nat.Prime 171799 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv19,pv137]) (by decide +kernel)
def pv171799 : PrimeValue := ⟨171799, pr171799⟩
private theorem pr171803 : Nat.Prime 171803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv31,pv163]) (by decide +kernel)
def pv171803 : PrimeValue := ⟨171803, pr171803⟩
private theorem pr171811 : Nat.Prime 171811 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv23,pv83]) (by decide +kernel)
def pv171811 : PrimeValue := ⟨171811, pr171811⟩
private theorem pr171823 : Nat.Prime 171823 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv4091]) (by decide +kernel)
def pv171823 : PrimeValue := ⟨171823, pr171823⟩
private theorem pr171827 : Nat.Prime 171827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53,pv1621]) (by decide +kernel)
def pv171827 : PrimeValue := ⟨171827, pr171827⟩
private theorem pr171851 : Nat.Prime 171851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv491]) (by decide +kernel)
def pv171851 : PrimeValue := ⟨171851, pr171851⟩
private theorem pr171863 : Nat.Prime 171863 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv85931]) (by decide +kernel)
def pv171863 : PrimeValue := ⟨171863, pr171863⟩
private theorem pr171869 : Nat.Prime 171869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv42967]) (by decide +kernel)
def pv171869 : PrimeValue := ⟨171869, pr171869⟩
private theorem pr171877 : Nat.Prime 171877 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv14323]) (by decide +kernel)
def pv171877 : PrimeValue := ⟨171877, pr171877⟩
private theorem pr171881 : Nat.Prime 171881 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv4297]) (by decide +kernel)
def pv171881 : PrimeValue := ⟨171881, pr171881⟩
private theorem pr171889 : Nat.Prime 171889 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv3581]) (by decide +kernel)
def pv171889 : PrimeValue := ⟨171889, pr171889⟩
private theorem pr171917 : Nat.Prime 171917 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv42979]) (by decide +kernel)
def pv171917 : PrimeValue := ⟨171917, pr171917⟩
private theorem pr171929 : Nat.Prime 171929 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv21491]) (by decide +kernel)
def pv171929 : PrimeValue := ⟨171929, pr171929⟩
private theorem pr171937 : Nat.Prime 171937 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv199]) (by decide +kernel)
def pv171937 : PrimeValue := ⟨171937, pr171937⟩
private theorem pr172001 : Nat.Prime 172001 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv43]) (by decide +kernel)
def pv172001 : PrimeValue := ⟨172001, pr172001⟩
private theorem pr172009 : Nat.Prime 172009 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv2389]) (by decide +kernel)
def pv172009 : PrimeValue := ⟨172009, pr172009⟩
private theorem pr172021 : Nat.Prime 172021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv47,pv61]) (by decide +kernel)
def pv172021 : PrimeValue := ⟨172021, pr172021⟩
private theorem pr172031 : Nat.Prime 172031 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv17203]) (by decide +kernel)
def pv172031 : PrimeValue := ⟨172031, pr172031⟩
private theorem pr172049 : Nat.Prime 172049 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv10753]) (by decide +kernel)
def pv172049 : PrimeValue := ⟨172049, pr172049⟩
private theorem pr172069 : Nat.Prime 172069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv1103]) (by decide +kernel)
def pv172069 : PrimeValue := ⟨172069, pr172069⟩
private theorem pr172079 : Nat.Prime 172079 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv97,pv887]) (by decide +kernel)
def pv172079 : PrimeValue := ⟨172079, pr172079⟩
private theorem pr172093 : Nat.Prime 172093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv14341]) (by decide +kernel)
def pv172093 : PrimeValue := ⟨172093, pr172093⟩
private theorem pr172097 : Nat.Prime 172097 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2689]) (by decide +kernel)
def pv172097 : PrimeValue := ⟨172097, pr172097⟩
private theorem pr172127 : Nat.Prime 172127 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv89,pv967]) (by decide +kernel)
def pv172127 : PrimeValue := ⟨172127, pr172127⟩
private theorem pr172147 : Nat.Prime 172147 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv2207]) (by decide +kernel)
def pv172147 : PrimeValue := ⟨172147, pr172147⟩
private theorem pr172157 : Nat.Prime 172157 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv193,pv223]) (by decide +kernel)
def pv172157 : PrimeValue := ⟨172157, pr172157⟩
private theorem pr172169 : Nat.Prime 172169 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv21521]) (by decide +kernel)
def pv172169 : PrimeValue := ⟨172169, pr172169⟩
private theorem pr172171 : Nat.Prime 172171 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1913]) (by decide +kernel)
def pv172171 : PrimeValue := ⟨172171, pr172171⟩
private theorem pr172181 : Nat.Prime 172181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv8609]) (by decide +kernel)
def pv172181 : PrimeValue := ⟨172181, pr172181⟩
private theorem pr172213 : Nat.Prime 172213 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv113,pv127]) (by decide +kernel)
def pv172213 : PrimeValue := ⟨172213, pr172213⟩
private theorem pr172217 : Nat.Prime 172217 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv19,pv103]) (by decide +kernel)
def pv172217 : PrimeValue := ⟨172217, pr172217⟩
private theorem pr172219 : Nat.Prime 172219 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv28703]) (by decide +kernel)
def pv172219 : PrimeValue := ⟨172219, pr172219⟩
private theorem pr172223 : Nat.Prime 172223 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv86111]) (by decide +kernel)
def pv172223 : PrimeValue := ⟨172223, pr172223⟩
private theorem pr172243 : Nat.Prime 172243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv1367]) (by decide +kernel)
def pv172243 : PrimeValue := ⟨172243, pr172243⟩
private theorem pr172259 : Nat.Prime 172259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv2003]) (by decide +kernel)
def pv172259 : PrimeValue := ⟨172259, pr172259⟩
private theorem pr172279 : Nat.Prime 172279 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv563]) (by decide +kernel)
def pv172279 : PrimeValue := ⟨172279, pr172279⟩
private theorem pr172283 : Nat.Prime 172283 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv41,pv191]) (by decide +kernel)
def pv172283 : PrimeValue := ⟨172283, pr172283⟩
private theorem pr172297 : Nat.Prime 172297 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2393]) (by decide +kernel)
def pv172297 : PrimeValue := ⟨172297, pr172297⟩
private theorem pr172307 : Nat.Prime 172307 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv101,pv853]) (by decide +kernel)
def pv172307 : PrimeValue := ⟨172307, pr172307⟩
private theorem pr172321 : Nat.Prime 172321 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv359]) (by decide +kernel)
def pv172321 : PrimeValue := ⟨172321, pr172321⟩
private theorem pr172331 : Nat.Prime 172331 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19,pv907]) (by decide +kernel)
def pv172331 : PrimeValue := ⟨172331, pr172331⟩
private theorem pr172343 : Nat.Prime 172343 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv86171]) (by decide +kernel)
def pv172343 : PrimeValue := ⟨172343, pr172343⟩
private theorem pr172351 : Nat.Prime 172351 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv383]) (by decide +kernel)
def pv172351 : PrimeValue := ⟨172351, pr172351⟩
private theorem pr172373 : Nat.Prime 172373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43093]) (by decide +kernel)
def pv172373 : PrimeValue := ⟨172373, pr172373⟩
private theorem pr172399 : Nat.Prime 172399 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv59,pv487]) (by decide +kernel)
def pv172399 : PrimeValue := ⟨172399, pr172399⟩
private theorem pr172421 : Nat.Prime 172421 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv37,pv233]) (by decide +kernel)
def pv172421 : PrimeValue := ⟨172421, pr172421⟩
private theorem pr172423 : Nat.Prime 172423 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv31,pv103]) (by decide +kernel)
def pv172423 : PrimeValue := ⟨172423, pr172423⟩
private theorem pr172427 : Nat.Prime 172427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv73,pv1181]) (by decide +kernel)
def pv172427 : PrimeValue := ⟨172427, pr172427⟩
private theorem pr172433 : Nat.Prime 172433 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv829]) (by decide +kernel)
def pv172433 : PrimeValue := ⟨172433, pr172433⟩
private theorem pr172439 : Nat.Prime 172439 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv109,pv113]) (by decide +kernel)
def pv172439 : PrimeValue := ⟨172439, pr172439⟩
private theorem pr172441 : Nat.Prime 172441 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv479]) (by decide +kernel)
def pv172441 : PrimeValue := ⟨172441, pr172441⟩
private theorem pr172489 : Nat.Prime 172489 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7187]) (by decide +kernel)
def pv172489 : PrimeValue := ⟨172489, pr172489⟩
private theorem pr172507 : Nat.Prime 172507 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv28751]) (by decide +kernel)
def pv172507 : PrimeValue := ⟨172507, pr172507⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
