/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table029
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table029.pv73673
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table006
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table015
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table016

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr73673 : Nat.Prime 73673 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv9209]) (by decide +kernel)
def pv73673 : PrimeValue := ⟨73673, pr73673⟩
private theorem pr73679 : Nat.Prime 73679 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv11,pv17,pv197]) (by decide +kernel)
def pv73679 : PrimeValue := ⟨73679, pr73679⟩
private theorem pr73681 : Nat.Prime 73681 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv307]) (by decide +kernel)
def pv73681 : PrimeValue := ⟨73681, pr73681⟩
private theorem pr73693 : Nat.Prime 73693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv89]) (by decide +kernel)
def pv73693 : PrimeValue := ⟨73693, pr73693⟩
private theorem pr73699 : Nat.Prime 73699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv71,pv173]) (by decide +kernel)
def pv73699 : PrimeValue := ⟨73699, pr73699⟩
private theorem pr73709 : Nat.Prime 73709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv18427]) (by decide +kernel)
def pv73709 : PrimeValue := ⟨73709, pr73709⟩
private theorem pr73721 : Nat.Prime 73721 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv19,pv97]) (by decide +kernel)
def pv73721 : PrimeValue := ⟨73721, pr73721⟩
private theorem pr73727 : Nat.Prime 73727 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv191,pv193]) (by decide +kernel)
def pv73727 : PrimeValue := ⟨73727, pr73727⟩
private theorem pr73751 : Nat.Prime 73751 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv59]) (by decide +kernel)
def pv73751 : PrimeValue := ⟨73751, pr73751⟩
private theorem pr73757 : Nat.Prime 73757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv18439]) (by decide +kernel)
def pv73757 : PrimeValue := ⟨73757, pr73757⟩
private theorem pr73771 : Nat.Prime 73771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv2459]) (by decide +kernel)
def pv73771 : PrimeValue := ⟨73771, pr73771⟩
private theorem pr73783 : Nat.Prime 73783 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv4099]) (by decide +kernel)
def pv73783 : PrimeValue := ⟨73783, pr73783⟩
private theorem pr73819 : Nat.Prime 73819 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv1367]) (by decide +kernel)
def pv73819 : PrimeValue := ⟨73819, pr73819⟩
private theorem pr73823 : Nat.Prime 73823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv5273]) (by decide +kernel)
def pv73823 : PrimeValue := ⟨73823, pr73823⟩
private theorem pr73847 : Nat.Prime 73847 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv36923]) (by decide +kernel)
def pv73847 : PrimeValue := ⟨73847, pr73847⟩
private theorem pr73849 : Nat.Prime 73849 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv17,pv181]) (by decide +kernel)
def pv73849 : PrimeValue := ⟨73849, pr73849⟩
private theorem pr73859 : Nat.Prime 73859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv36929]) (by decide +kernel)
def pv73859 : PrimeValue := ⟨73859, pr73859⟩
private theorem pr73867 : Nat.Prime 73867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv947]) (by decide +kernel)
def pv73867 : PrimeValue := ⟨73867, pr73867⟩
private theorem pr73877 : Nat.Prime 73877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv23,pv73]) (by decide +kernel)
def pv73877 : PrimeValue := ⟨73877, pr73877⟩
private theorem pr73883 : Nat.Prime 73883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv41,pv53]) (by decide +kernel)
def pv73883 : PrimeValue := ⟨73883, pr73883⟩
private theorem pr73897 : Nat.Prime 73897 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv3079]) (by decide +kernel)
def pv73897 : PrimeValue := ⟨73897, pr73897⟩
private theorem pr73907 : Nat.Prime 73907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv5279]) (by decide +kernel)
def pv73907 : PrimeValue := ⟨73907, pr73907⟩
private theorem pr73939 : Nat.Prime 73939 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv12323]) (by decide +kernel)
def pv73939 : PrimeValue := ⟨73939, pr73939⟩
private theorem pr73943 : Nat.Prime 73943 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv3361]) (by decide +kernel)
def pv73943 : PrimeValue := ⟨73943, pr73943⟩
private theorem pr73951 : Nat.Prime 73951 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv17,pv29]) (by decide +kernel)
def pv73951 : PrimeValue := ⟨73951, pr73951⟩
private theorem pr73961 : Nat.Prime 73961 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv43]) (by decide +kernel)
def pv73961 : PrimeValue := ⟨73961, pr73961⟩
private theorem pr73973 : Nat.Prime 73973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv18493]) (by decide +kernel)
def pv73973 : PrimeValue := ⟨73973, pr73973⟩
private theorem pr73999 : Nat.Prime 73999 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv4111]) (by decide +kernel)
def pv73999 : PrimeValue := ⟨73999, pr73999⟩
private theorem pr74017 : Nat.Prime 74017 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv257]) (by decide +kernel)
def pv74017 : PrimeValue := ⟨74017, pr74017⟩
private theorem pr74021 : Nat.Prime 74021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv3701]) (by decide +kernel)
def pv74021 : PrimeValue := ⟨74021, pr74021⟩
private theorem pr74027 : Nat.Prime 74027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37013]) (by decide +kernel)
def pv74027 : PrimeValue := ⟨74027, pr74027⟩
private theorem pr74047 : Nat.Prime 74047 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv41,pv43]) (by decide +kernel)
def pv74047 : PrimeValue := ⟨74047, pr74047⟩
private theorem pr74051 : Nat.Prime 74051 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv5,pv1481]) (by decide +kernel)
def pv74051 : PrimeValue := ⟨74051, pr74051⟩
private theorem pr74071 : Nat.Prime 74071 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv823]) (by decide +kernel)
def pv74071 : PrimeValue := ⟨74071, pr74071⟩
private theorem pr74077 : Nat.Prime 74077 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv6173]) (by decide +kernel)
def pv74077 : PrimeValue := ⟨74077, pr74077⟩
private theorem pr74093 : Nat.Prime 74093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv18523]) (by decide +kernel)
def pv74093 : PrimeValue := ⟨74093, pr74093⟩
private theorem pr74099 : Nat.Prime 74099 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37049]) (by decide +kernel)
def pv74099 : PrimeValue := ⟨74099, pr74099⟩
private theorem pr74101 : Nat.Prime 74101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv19]) (by decide +kernel)
def pv74101 : PrimeValue := ⟨74101, pr74101⟩
private theorem pr74131 : Nat.Prime 74131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv353]) (by decide +kernel)
def pv74131 : PrimeValue := ⟨74131, pr74131⟩
private theorem pr74143 : Nat.Prime 74143 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1373]) (by decide +kernel)
def pv74143 : PrimeValue := ⟨74143, pr74143⟩
private theorem pr74149 : Nat.Prime 74149 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv167]) (by decide +kernel)
def pv74149 : PrimeValue := ⟨74149, pr74149⟩
private theorem pr74159 : Nat.Prime 74159 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv7,pv5297]) (by decide +kernel)
def pv74159 : PrimeValue := ⟨74159, pr74159⟩
private theorem pr74161 : Nat.Prime 74161 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv103]) (by decide +kernel)
def pv74161 : PrimeValue := ⟨74161, pr74161⟩
private theorem pr74167 : Nat.Prime 74167 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv47,pv263]) (by decide +kernel)
def pv74167 : PrimeValue := ⟨74167, pr74167⟩
private theorem pr74177 : Nat.Prime 74177 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv61]) (by decide +kernel)
def pv74177 : PrimeValue := ⟨74177, pr74177⟩
private theorem pr74189 : Nat.Prime 74189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv1091]) (by decide +kernel)
def pv74189 : PrimeValue := ⟨74189, pr74189⟩
private theorem pr74197 : Nat.Prime 74197 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv229]) (by decide +kernel)
def pv74197 : PrimeValue := ⟨74197, pr74197⟩
private theorem pr74201 : Nat.Prime 74201 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv53]) (by decide +kernel)
def pv74201 : PrimeValue := ⟨74201, pr74201⟩
private theorem pr74203 : Nat.Prime 74203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv83,pv149]) (by decide +kernel)
def pv74203 : PrimeValue := ⟨74203, pr74203⟩
private theorem pr74209 : Nat.Prime 74209 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv773]) (by decide +kernel)
def pv74209 : PrimeValue := ⟨74209, pr74209⟩
private theorem pr74219 : Nat.Prime 74219 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv863]) (by decide +kernel)
def pv74219 : PrimeValue := ⟨74219, pr74219⟩
private theorem pr74231 : Nat.Prime 74231 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv13,pv571]) (by decide +kernel)
def pv74231 : PrimeValue := ⟨74231, pr74231⟩
private theorem pr74257 : Nat.Prime 74257 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv17]) (by decide +kernel)
def pv74257 : PrimeValue := ⟨74257, pr74257⟩
private theorem pr74279 : Nat.Prime 74279 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv37139]) (by decide +kernel)
def pv74279 : PrimeValue := ⟨74279, pr74279⟩
private theorem pr74287 : Nat.Prime 74287 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv4127]) (by decide +kernel)
def pv74287 : PrimeValue := ⟨74287, pr74287⟩
private theorem pr74293 : Nat.Prime 74293 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv41,pv151]) (by decide +kernel)
def pv74293 : PrimeValue := ⟨74293, pr74293⟩
private theorem pr74297 : Nat.Prime 74297 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv37,pv251]) (by decide +kernel)
def pv74297 : PrimeValue := ⟨74297, pr74297⟩
private theorem pr74311 : Nat.Prime 74311 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv2477]) (by decide +kernel)
def pv74311 : PrimeValue := ⟨74311, pr74311⟩
private theorem pr74317 : Nat.Prime 74317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv563]) (by decide +kernel)
def pv74317 : PrimeValue := ⟨74317, pr74317⟩
private theorem pr74323 : Nat.Prime 74323 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv4129]) (by decide +kernel)
def pv74323 : PrimeValue := ⟨74323, pr74323⟩
private theorem pr74353 : Nat.Prime 74353 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1549]) (by decide +kernel)
def pv74353 : PrimeValue := ⟨74353, pr74353⟩
private theorem pr74357 : Nat.Prime 74357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv641]) (by decide +kernel)
def pv74357 : PrimeValue := ⟨74357, pr74357⟩
private theorem pr74363 : Nat.Prime 74363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37181]) (by decide +kernel)
def pv74363 : PrimeValue := ⟨74363, pr74363⟩
private theorem pr74377 : Nat.Prime 74377 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1033]) (by decide +kernel)
def pv74377 : PrimeValue := ⟨74377, pr74377⟩
private theorem pr74381 : Nat.Prime 74381 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv3719]) (by decide +kernel)
def pv74381 : PrimeValue := ⟨74381, pr74381⟩
private theorem pr74383 : Nat.Prime 74383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv23]) (by decide +kernel)
def pv74383 : PrimeValue := ⟨74383, pr74383⟩
private theorem pr74411 : Nat.Prime 74411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv1063]) (by decide +kernel)
def pv74411 : PrimeValue := ⟨74411, pr74411⟩
private theorem pr74413 : Nat.Prime 74413 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv53]) (by decide +kernel)
def pv74413 : PrimeValue := ⟨74413, pr74413⟩
private theorem pr74419 : Nat.Prime 74419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv79,pv157]) (by decide +kernel)
def pv74419 : PrimeValue := ⟨74419, pr74419⟩
private theorem pr74441 : Nat.Prime 74441 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv1861]) (by decide +kernel)
def pv74441 : PrimeValue := ⟨74441, pr74441⟩
private theorem pr74449 : Nat.Prime 74449 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv11,pv47]) (by decide +kernel)
def pv74449 : PrimeValue := ⟨74449, pr74449⟩
private theorem pr74453 : Nat.Prime 74453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv2659]) (by decide +kernel)
def pv74453 : PrimeValue := ⟨74453, pr74453⟩
private theorem pr74471 : Nat.Prime 74471 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv11,pv677]) (by decide +kernel)
def pv74471 : PrimeValue := ⟨74471, pr74471⟩
private theorem pr74489 : Nat.Prime 74489 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv9311]) (by decide +kernel)
def pv74489 : PrimeValue := ⟨74489, pr74489⟩
private theorem pr74509 : Nat.Prime 74509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv887]) (by decide +kernel)
def pv74509 : PrimeValue := ⟨74509, pr74509⟩
private theorem pr74521 : Nat.Prime 74521 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv23]) (by decide +kernel)
def pv74521 : PrimeValue := ⟨74521, pr74521⟩
private theorem pr74527 : Nat.Prime 74527 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv12421]) (by decide +kernel)
def pv74527 : PrimeValue := ⟨74527, pr74527⟩
private theorem pr74531 : Nat.Prime 74531 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv29,pv257]) (by decide +kernel)
def pv74531 : PrimeValue := ⟨74531, pr74531⟩
private theorem pr74551 : Nat.Prime 74551 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv71]) (by decide +kernel)
def pv74551 : PrimeValue := ⟨74551, pr74551⟩
private theorem pr74561 : Nat.Prime 74561 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv233]) (by decide +kernel)
def pv74561 : PrimeValue := ⟨74561, pr74561⟩
private theorem pr74567 : Nat.Prime 74567 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv23,pv1621]) (by decide +kernel)
def pv74567 : PrimeValue := ⟨74567, pr74567⟩
private theorem pr74573 : Nat.Prime 74573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv103,pv181]) (by decide +kernel)
def pv74573 : PrimeValue := ⟨74573, pr74573⟩
private theorem pr74587 : Nat.Prime 74587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv401]) (by decide +kernel)
def pv74587 : PrimeValue := ⟨74587, pr74587⟩
private theorem pr74597 : Nat.Prime 74597 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv1097]) (by decide +kernel)
def pv74597 : PrimeValue := ⟨74597, pr74597⟩
private theorem pr74609 : Nat.Prime 74609 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv4663]) (by decide +kernel)
def pv74609 : PrimeValue := ⟨74609, pr74609⟩
private theorem pr74611 : Nat.Prime 74611 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv829]) (by decide +kernel)
def pv74611 : PrimeValue := ⟨74611, pr74611⟩
private theorem pr74623 : Nat.Prime 74623 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv12437]) (by decide +kernel)
def pv74623 : PrimeValue := ⟨74623, pr74623⟩
private theorem pr74653 : Nat.Prime 74653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv6221]) (by decide +kernel)
def pv74653 : PrimeValue := ⟨74653, pr74653⟩
private theorem pr74687 : Nat.Prime 74687 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv107,pv349]) (by decide +kernel)
def pv74687 : PrimeValue := ⟨74687, pr74687⟩
private theorem pr74699 : Nat.Prime 74699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv17]) (by decide +kernel)
def pv74699 : PrimeValue := ⟨74699, pr74699⟩
private theorem pr74707 : Nat.Prime 74707 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv12451]) (by decide +kernel)
def pv74707 : PrimeValue := ⟨74707, pr74707⟩
private theorem pr74713 : Nat.Prime 74713 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv11,pv283]) (by decide +kernel)
def pv74713 : PrimeValue := ⟨74713, pr74713⟩
private theorem pr74717 : Nat.Prime 74717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv18679]) (by decide +kernel)
def pv74717 : PrimeValue := ⟨74717, pr74717⟩
private theorem pr74719 : Nat.Prime 74719 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv593]) (by decide +kernel)
def pv74719 : PrimeValue := ⟨74719, pr74719⟩
private theorem pr74729 : Nat.Prime 74729 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv9341]) (by decide +kernel)
def pv74729 : PrimeValue := ⟨74729, pr74729⟩
private theorem pr74731 : Nat.Prime 74731 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv47,pv53]) (by decide +kernel)
def pv74731 : PrimeValue := ⟨74731, pr74731⟩
private theorem pr74747 : Nat.Prime 74747 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv19,pv281]) (by decide +kernel)
def pv74747 : PrimeValue := ⟨74747, pr74747⟩
private theorem pr74759 : Nat.Prime 74759 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv37379]) (by decide +kernel)
def pv74759 : PrimeValue := ⟨74759, pr74759⟩
private theorem pr74761 : Nat.Prime 74761 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv7,pv89]) (by decide +kernel)
def pv74761 : PrimeValue := ⟨74761, pr74761⟩
private theorem pr74771 : Nat.Prime 74771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7477]) (by decide +kernel)
def pv74771 : PrimeValue := ⟨74771, pr74771⟩
private theorem pr74779 : Nat.Prime 74779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv103]) (by decide +kernel)
def pv74779 : PrimeValue := ⟨74779, pr74779⟩
private theorem pr74797 : Nat.Prime 74797 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23,pv271]) (by decide +kernel)
def pv74797 : PrimeValue := ⟨74797, pr74797⟩
private theorem pr74821 : Nat.Prime 74821 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv29,pv43]) (by decide +kernel)
def pv74821 : PrimeValue := ⟨74821, pr74821⟩
private theorem pr74827 : Nat.Prime 74827 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv4157]) (by decide +kernel)
def pv74827 : PrimeValue := ⟨74827, pr74827⟩
private theorem pr74831 : Nat.Prime 74831 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv1069]) (by decide +kernel)
def pv74831 : PrimeValue := ⟨74831, pr74831⟩
private theorem pr74843 : Nat.Prime 74843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv1627]) (by decide +kernel)
def pv74843 : PrimeValue := ⟨74843, pr74843⟩
private theorem pr74857 : Nat.Prime 74857 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv3119]) (by decide +kernel)
def pv74857 : PrimeValue := ⟨74857, pr74857⟩
private theorem pr74869 : Nat.Prime 74869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv367]) (by decide +kernel)
def pv74869 : PrimeValue := ⟨74869, pr74869⟩
private theorem pr74873 : Nat.Prime 74873 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv191]) (by decide +kernel)
def pv74873 : PrimeValue := ⟨74873, pr74873⟩
private theorem pr74887 : Nat.Prime 74887 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv1783]) (by decide +kernel)
def pv74887 : PrimeValue := ⟨74887, pr74887⟩
private theorem pr74891 : Nat.Prime 74891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7489]) (by decide +kernel)
def pv74891 : PrimeValue := ⟨74891, pr74891⟩
private theorem pr74897 : Nat.Prime 74897 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv151]) (by decide +kernel)
def pv74897 : PrimeValue := ⟨74897, pr74897⟩
private theorem pr74903 : Nat.Prime 74903 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv2203]) (by decide +kernel)
def pv74903 : PrimeValue := ⟨74903, pr74903⟩
private theorem pr74923 : Nat.Prime 74923 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv12487]) (by decide +kernel)
def pv74923 : PrimeValue := ⟨74923, pr74923⟩
private theorem pr74929 : Nat.Prime 74929 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv223]) (by decide +kernel)
def pv74929 : PrimeValue := ⟨74929, pr74929⟩
private theorem pr74933 : Nat.Prime 74933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv13,pv131]) (by decide +kernel)
def pv74933 : PrimeValue := ⟨74933, pr74933⟩
private theorem pr74941 : Nat.Prime 74941 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv1249]) (by decide +kernel)
def pv74941 : PrimeValue := ⟨74941, pr74941⟩
private theorem pr74959 : Nat.Prime 74959 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv31]) (by decide +kernel)
def pv74959 : PrimeValue := ⟨74959, pr74959⟩
private theorem pr75011 : Nat.Prime 75011 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv13,pv577]) (by decide +kernel)
def pv75011 : PrimeValue := ⟨75011, pr75011⟩
private theorem pr75013 : Nat.Prime 75013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv19,pv47]) (by decide +kernel)
def pv75013 : PrimeValue := ⟨75013, pr75013⟩
private theorem pr75017 : Nat.Prime 75017 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv9377]) (by decide +kernel)
def pv75017 : PrimeValue := ⟨75017, pr75017⟩
private theorem pr75029 : Nat.Prime 75029 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv18757]) (by decide +kernel)
def pv75029 : PrimeValue := ⟨75029, pr75029⟩
private theorem pr75037 : Nat.Prime 75037 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv37]) (by decide +kernel)
def pv75037 : PrimeValue := ⟨75037, pr75037⟩
private theorem pr75041 : Nat.Prime 75041 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv67]) (by decide +kernel)
def pv75041 : PrimeValue := ⟨75041, pr75041⟩
private theorem pr75079 : Nat.Prime 75079 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv43,pv97]) (by decide +kernel)
def pv75079 : PrimeValue := ⟨75079, pr75079⟩
private theorem pr75083 : Nat.Prime 75083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv31,pv173]) (by decide +kernel)
def pv75083 : PrimeValue := ⟨75083, pr75083⟩
private theorem pr75109 : Nat.Prime 75109 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv569]) (by decide +kernel)
def pv75109 : PrimeValue := ⟨75109, pr75109⟩
private theorem pr75133 : Nat.Prime 75133 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2087]) (by decide +kernel)
def pv75133 : PrimeValue := ⟨75133, pr75133⟩
private theorem pr75149 : Nat.Prime 75149 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv18787]) (by decide +kernel)
def pv75149 : PrimeValue := ⟨75149, pr75149⟩
private theorem pr75161 : Nat.Prime 75161 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv1879]) (by decide +kernel)
def pv75161 : PrimeValue := ⟨75161, pr75161⟩
private theorem pr75167 : Nat.Prime 75167 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv13,pv59]) (by decide +kernel)
def pv75167 : PrimeValue := ⟨75167, pr75167⟩
private theorem pr75169 : Nat.Prime 75169 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv29]) (by decide +kernel)
def pv75169 : PrimeValue := ⟨75169, pr75169⟩
private theorem pr75181 : Nat.Prime 75181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv179]) (by decide +kernel)
def pv75181 : PrimeValue := ⟨75181, pr75181⟩
private theorem pr75193 : Nat.Prime 75193 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv241]) (by decide +kernel)
def pv75193 : PrimeValue := ⟨75193, pr75193⟩
private theorem pr75209 : Nat.Prime 75209 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv17,pv79]) (by decide +kernel)
def pv75209 : PrimeValue := ⟨75209, pr75209⟩
private theorem pr75211 : Nat.Prime 75211 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv23,pv109]) (by decide +kernel)
def pv75211 : PrimeValue := ⟨75211, pr75211⟩
private theorem pr75217 : Nat.Prime 75217 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1567]) (by decide +kernel)
def pv75217 : PrimeValue := ⟨75217, pr75217⟩
private theorem pr75223 : Nat.Prime 75223 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv199]) (by decide +kernel)
def pv75223 : PrimeValue := ⟨75223, pr75223⟩
private theorem pr75227 : Nat.Prime 75227 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv1297]) (by decide +kernel)
def pv75227 : PrimeValue := ⟨75227, pr75227⟩
private theorem pr75239 : Nat.Prime 75239 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv37619]) (by decide +kernel)
def pv75239 : PrimeValue := ⟨75239, pr75239⟩
private theorem pr75253 : Nat.Prime 75253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv6271]) (by decide +kernel)
def pv75253 : PrimeValue := ⟨75253, pr75253⟩
private theorem pr75269 : Nat.Prime 75269 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv607]) (by decide +kernel)
def pv75269 : PrimeValue := ⟨75269, pr75269⟩
private theorem pr75277 : Nat.Prime 75277 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv41]) (by decide +kernel)
def pv75277 : PrimeValue := ⟨75277, pr75277⟩
private theorem pr75289 : Nat.Prime 75289 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv3137]) (by decide +kernel)
def pv75289 : PrimeValue := ⟨75289, pr75289⟩
private theorem pr75307 : Nat.Prime 75307 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv163]) (by decide +kernel)
def pv75307 : PrimeValue := ⟨75307, pr75307⟩
private theorem pr75323 : Nat.Prime 75323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv2897]) (by decide +kernel)
def pv75323 : PrimeValue := ⟨75323, pr75323⟩
private theorem pr75329 : Nat.Prime 75329 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv107]) (by decide +kernel)
def pv75329 : PrimeValue := ⟨75329, pr75329⟩
private theorem pr75337 : Nat.Prime 75337 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv43,pv73]) (by decide +kernel)
def pv75337 : PrimeValue := ⟨75337, pr75337⟩
private theorem pr75347 : Nat.Prime 75347 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv101,pv373]) (by decide +kernel)
def pv75347 : PrimeValue := ⟨75347, pr75347⟩
private theorem pr75353 : Nat.Prime 75353 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv9419]) (by decide +kernel)
def pv75353 : PrimeValue := ⟨75353, pr75353⟩
private theorem pr75377 : Nat.Prime 75377 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv673]) (by decide +kernel)
def pv75377 : PrimeValue := ⟨75377, pr75377⟩
private theorem pr75389 : Nat.Prime 75389 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv401]) (by decide +kernel)
def pv75389 : PrimeValue := ⟨75389, pr75389⟩
private theorem pr75391 : Nat.Prime 75391 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv359]) (by decide +kernel)
def pv75391 : PrimeValue := ⟨75391, pr75391⟩
private theorem pr75401 : Nat.Prime 75401 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv29]) (by decide +kernel)
def pv75401 : PrimeValue := ⟨75401, pr75401⟩
private theorem pr75403 : Nat.Prime 75403 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv59,pv71]) (by decide +kernel)
def pv75403 : PrimeValue := ⟨75403, pr75403⟩
private theorem pr75407 : Nat.Prime 75407 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv37,pv1019]) (by decide +kernel)
def pv75407 : PrimeValue := ⟨75407, pr75407⟩
private theorem pr75431 : Nat.Prime 75431 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv19,pv397]) (by decide +kernel)
def pv75431 : PrimeValue := ⟨75431, pr75431⟩
private theorem pr75437 : Nat.Prime 75437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv18859]) (by decide +kernel)
def pv75437 : PrimeValue := ⟨75437, pr75437⟩
private theorem pr75479 : Nat.Prime 75479 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv13,pv2903]) (by decide +kernel)
def pv75479 : PrimeValue := ⟨75479, pr75479⟩
private theorem pr75503 : Nat.Prime 75503 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv5393]) (by decide +kernel)
def pv75503 : PrimeValue := ⟨75503, pr75503⟩
private theorem pr75511 : Nat.Prime 75511 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv839]) (by decide +kernel)
def pv75511 : PrimeValue := ⟨75511, pr75511⟩
private theorem pr75521 : Nat.Prime 75521 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv59]) (by decide +kernel)
def pv75521 : PrimeValue := ⟨75521, pr75521⟩
private theorem pr75527 : Nat.Prime 75527 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv3433]) (by decide +kernel)
def pv75527 : PrimeValue := ⟨75527, pr75527⟩
private theorem pr75533 : Nat.Prime 75533 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv821]) (by decide +kernel)
def pv75533 : PrimeValue := ⟨75533, pr75533⟩
private theorem pr75539 : Nat.Prime 75539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv179,pv211]) (by decide +kernel)
def pv75539 : PrimeValue := ⟨75539, pr75539⟩
private theorem pr75541 : Nat.Prime 75541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1259]) (by decide +kernel)
def pv75541 : PrimeValue := ⟨75541, pr75541⟩
private theorem pr75553 : Nat.Prime 75553 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv787]) (by decide +kernel)
def pv75553 : PrimeValue := ⟨75553, pr75553⟩
private theorem pr75557 : Nat.Prime 75557 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv1453]) (by decide +kernel)
def pv75557 : PrimeValue := ⟨75557, pr75557⟩
private theorem pr75571 : Nat.Prime 75571 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv229]) (by decide +kernel)
def pv75571 : PrimeValue := ⟨75571, pr75571⟩
private theorem pr75577 : Nat.Prime 75577 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv47,pv67]) (by decide +kernel)
def pv75577 : PrimeValue := ⟨75577, pr75577⟩
private theorem pr75583 : Nat.Prime 75583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv17,pv19]) (by decide +kernel)
def pv75583 : PrimeValue := ⟨75583, pr75583⟩
private theorem pr75611 : Nat.Prime 75611 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7561]) (by decide +kernel)
def pv75611 : PrimeValue := ⟨75611, pr75611⟩
private theorem pr75617 : Nat.Prime 75617 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv139]) (by decide +kernel)
def pv75617 : PrimeValue := ⟨75617, pr75617⟩
private theorem pr75619 : Nat.Prime 75619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4201]) (by decide +kernel)
def pv75619 : PrimeValue := ⟨75619, pr75619⟩
private theorem pr75629 : Nat.Prime 75629 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv37,pv73]) (by decide +kernel)
def pv75629 : PrimeValue := ⟨75629, pr75629⟩
private theorem pr75641 : Nat.Prime 75641 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv31,pv61]) (by decide +kernel)
def pv75641 : PrimeValue := ⟨75641, pr75641⟩
private theorem pr75653 : Nat.Prime 75653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv18913]) (by decide +kernel)
def pv75653 : PrimeValue := ⟨75653, pr75653⟩
private theorem pr75659 : Nat.Prime 75659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv19,pv181]) (by decide +kernel)
def pv75659 : PrimeValue := ⟨75659, pr75659⟩
private theorem pr75679 : Nat.Prime 75679 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv12613]) (by decide +kernel)
def pv75679 : PrimeValue := ⟨75679, pr75679⟩
private theorem pr75683 : Nat.Prime 75683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79,pv479]) (by decide +kernel)
def pv75683 : PrimeValue := ⟨75683, pr75683⟩
private theorem pr75689 : Nat.Prime 75689 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv9461]) (by decide +kernel)
def pv75689 : PrimeValue := ⟨75689, pr75689⟩
private theorem pr75703 : Nat.Prime 75703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv31,pv37]) (by decide +kernel)
def pv75703 : PrimeValue := ⟨75703, pr75703⟩
private theorem pr75707 : Nat.Prime 75707 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37853]) (by decide +kernel)
def pv75707 : PrimeValue := ⟨75707, pr75707⟩
private theorem pr75709 : Nat.Prime 75709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv701]) (by decide +kernel)
def pv75709 : PrimeValue := ⟨75709, pr75709⟩
private theorem pr75721 : Nat.Prime 75721 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv631]) (by decide +kernel)
def pv75721 : PrimeValue := ⟨75721, pr75721⟩
private theorem pr75731 : Nat.Prime 75731 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7573]) (by decide +kernel)
def pv75731 : PrimeValue := ⟨75731, pr75731⟩
private theorem pr75743 : Nat.Prime 75743 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv37871]) (by decide +kernel)
def pv75743 : PrimeValue := ⟨75743, pr75743⟩
private theorem pr75767 : Nat.Prime 75767 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv43,pv881]) (by decide +kernel)
def pv75767 : PrimeValue := ⟨75767, pr75767⟩
private theorem pr75773 : Nat.Prime 75773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv997]) (by decide +kernel)
def pv75773 : PrimeValue := ⟨75773, pr75773⟩
private theorem pr75781 : Nat.Prime 75781 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv421]) (by decide +kernel)
def pv75781 : PrimeValue := ⟨75781, pr75781⟩
private theorem pr75787 : Nat.Prime 75787 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv743]) (by decide +kernel)
def pv75787 : PrimeValue := ⟨75787, pr75787⟩
private theorem pr75793 : Nat.Prime 75793 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv1579]) (by decide +kernel)
def pv75793 : PrimeValue := ⟨75793, pr75793⟩
private theorem pr75797 : Nat.Prime 75797 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv2707]) (by decide +kernel)
def pv75797 : PrimeValue := ⟨75797, pr75797⟩
private theorem pr75821 : Nat.Prime 75821 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv223]) (by decide +kernel)
def pv75821 : PrimeValue := ⟨75821, pr75821⟩
private theorem pr75833 : Nat.Prime 75833 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv9479]) (by decide +kernel)
def pv75833 : PrimeValue := ⟨75833, pr75833⟩
private theorem pr75853 : Nat.Prime 75853 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv43]) (by decide +kernel)
def pv75853 : PrimeValue := ⟨75853, pr75853⟩
private theorem pr75869 : Nat.Prime 75869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv1459]) (by decide +kernel)
def pv75869 : PrimeValue := ⟨75869, pr75869⟩
private theorem pr75883 : Nat.Prime 75883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv12647]) (by decide +kernel)
def pv75883 : PrimeValue := ⟨75883, pr75883⟩
private theorem pr75913 : Nat.Prime 75913 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv3163]) (by decide +kernel)
def pv75913 : PrimeValue := ⟨75913, pr75913⟩
private theorem pr75931 : Nat.Prime 75931 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv2531]) (by decide +kernel)
def pv75931 : PrimeValue := ⟨75931, pr75931⟩
private theorem pr75937 : Nat.Prime 75937 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv7,pv113]) (by decide +kernel)
def pv75937 : PrimeValue := ⟨75937, pr75937⟩
private theorem pr75941 : Nat.Prime 75941 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv3797]) (by decide +kernel)
def pv75941 : PrimeValue := ⟨75941, pr75941⟩
private theorem pr75967 : Nat.Prime 75967 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv1151]) (by decide +kernel)
def pv75967 : PrimeValue := ⟨75967, pr75967⟩
private theorem pr75979 : Nat.Prime 75979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv67]) (by decide +kernel)
def pv75979 : PrimeValue := ⟨75979, pr75979⟩
private theorem pr75983 : Nat.Prime 75983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv37991]) (by decide +kernel)
def pv75983 : PrimeValue := ⟨75983, pr75983⟩
private theorem pr75989 : Nat.Prime 75989 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv157]) (by decide +kernel)
def pv75989 : PrimeValue := ⟨75989, pr75989⟩
private theorem pr75991 : Nat.Prime 75991 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv17,pv149]) (by decide +kernel)
def pv75991 : PrimeValue := ⟨75991, pr75991⟩
private theorem pr75997 : Nat.Prime 75997 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2111]) (by decide +kernel)
def pv75997 : PrimeValue := ⟨75997, pr75997⟩
private theorem pr76001 : Nat.Prime 76001 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv19]) (by decide +kernel)
def pv76001 : PrimeValue := ⟨76001, pr76001⟩
private theorem pr76003 : Nat.Prime 76003 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv53,pv239]) (by decide +kernel)
def pv76003 : PrimeValue := ⟨76003, pr76003⟩
private theorem pr76031 : Nat.Prime 76031 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7603]) (by decide +kernel)
def pv76031 : PrimeValue := ⟨76031, pr76031⟩
private theorem pr76039 : Nat.Prime 76039 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv19,pv23,pv29]) (by decide +kernel)
def pv76039 : PrimeValue := ⟨76039, pr76039⟩
private theorem pr76079 : Nat.Prime 76079 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv38039]) (by decide +kernel)
def pv76079 : PrimeValue := ⟨76079, pr76079⟩
private theorem pr76081 : Nat.Prime 76081 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv317]) (by decide +kernel)
def pv76081 : PrimeValue := ⟨76081, pr76081⟩
private theorem pr76091 : Nat.Prime 76091 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv1087]) (by decide +kernel)
def pv76091 : PrimeValue := ⟨76091, pr76091⟩
private theorem pr76099 : Nat.Prime 76099 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv1153]) (by decide +kernel)
def pv76099 : PrimeValue := ⟨76099, pr76099⟩
private theorem pr76103 : Nat.Prime 76103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv2927]) (by decide +kernel)
def pv76103 : PrimeValue := ⟨76103, pr76103⟩
private theorem pr76123 : Nat.Prime 76123 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv4229]) (by decide +kernel)
def pv76123 : PrimeValue := ⟨76123, pr76123⟩
private theorem pr76129 : Nat.Prime 76129 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv13,pv61]) (by decide +kernel)
def pv76129 : PrimeValue := ⟨76129, pr76129⟩
private theorem pr76147 : Nat.Prime 76147 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv37]) (by decide +kernel)
def pv76147 : PrimeValue := ⟨76147, pr76147⟩
private theorem pr76157 : Nat.Prime 76157 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79,pv241]) (by decide +kernel)
def pv76157 : PrimeValue := ⟨76157, pr76157⟩
private theorem pr76159 : Nat.Prime 76159 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv4231]) (by decide +kernel)
def pv76159 : PrimeValue := ⟨76159, pr76159⟩
private theorem pr76163 : Nat.Prime 76163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv113,pv337]) (by decide +kernel)
def pv76163 : PrimeValue := ⟨76163, pr76163⟩
private theorem pr76207 : Nat.Prime 76207 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv977]) (by decide +kernel)
def pv76207 : PrimeValue := ⟨76207, pr76207⟩
private theorem pr76213 : Nat.Prime 76213 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29,pv73]) (by decide +kernel)
def pv76213 : PrimeValue := ⟨76213, pr76213⟩
private theorem pr76231 : Nat.Prime 76231 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv11]) (by decide +kernel)
def pv76231 : PrimeValue := ⟨76231, pr76231⟩
private theorem pr76243 : Nat.Prime 76243 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv97,pv131]) (by decide +kernel)
def pv76243 : PrimeValue := ⟨76243, pr76243⟩
private theorem pr76249 : Nat.Prime 76249 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv353]) (by decide +kernel)
def pv76249 : PrimeValue := ⟨76249, pr76249⟩
private theorem pr76253 : Nat.Prime 76253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv1733]) (by decide +kernel)
def pv76253 : PrimeValue := ⟨76253, pr76253⟩
private theorem pr76259 : Nat.Prime 76259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv13,pv419]) (by decide +kernel)
def pv76259 : PrimeValue := ⟨76259, pr76259⟩
private theorem pr76261 : Nat.Prime 76261 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv31,pv41]) (by decide +kernel)
def pv76261 : PrimeValue := ⟨76261, pr76261⟩
private theorem pr76283 : Nat.Prime 76283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv887]) (by decide +kernel)
def pv76283 : PrimeValue := ⟨76283, pr76283⟩
private theorem pr76289 : Nat.Prime 76289 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv149]) (by decide +kernel)
def pv76289 : PrimeValue := ⟨76289, pr76289⟩
private theorem pr76303 : Nat.Prime 76303 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv157]) (by decide +kernel)
def pv76303 : PrimeValue := ⟨76303, pr76303⟩
private theorem pr76333 : Nat.Prime 76333 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv6361]) (by decide +kernel)
def pv76333 : PrimeValue := ⟨76333, pr76333⟩
private theorem pr76343 : Nat.Prime 76343 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv19,pv41]) (by decide +kernel)
def pv76343 : PrimeValue := ⟨76343, pr76343⟩
private theorem pr76369 : Nat.Prime 76369 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv37,pv43]) (by decide +kernel)
def pv76369 : PrimeValue := ⟨76369, pr76369⟩
private theorem pr76379 : Nat.Prime 76379 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv38189]) (by decide +kernel)
def pv76379 : PrimeValue := ⟨76379, pr76379⟩
private theorem pr76387 : Nat.Prime 76387 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29,pv439]) (by decide +kernel)
def pv76387 : PrimeValue := ⟨76387, pr76387⟩
private theorem pr76403 : Nat.Prime 76403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv38201]) (by decide +kernel)
def pv76403 : PrimeValue := ⟨76403, pr76403⟩
private theorem pr76421 : Nat.Prime 76421 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv3821]) (by decide +kernel)
def pv76421 : PrimeValue := ⟨76421, pr76421⟩
private theorem pr76423 : Nat.Prime 76423 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv47,pv271]) (by decide +kernel)
def pv76423 : PrimeValue := ⟨76423, pr76423⟩
private theorem pr76441 : Nat.Prime 76441 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv13]) (by decide +kernel)
def pv76441 : PrimeValue := ⟨76441, pr76441⟩
private theorem pr76463 : Nat.Prime 76463 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv38231]) (by decide +kernel)
def pv76463 : PrimeValue := ⟨76463, pr76463⟩
private theorem pr76471 : Nat.Prime 76471 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv2549]) (by decide +kernel)
def pv76471 : PrimeValue := ⟨76471, pr76471⟩
private theorem pr76481 : Nat.Prime 76481 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv239]) (by decide +kernel)
def pv76481 : PrimeValue := ⟨76481, pr76481⟩
private theorem pr76487 : Nat.Prime 76487 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv167,pv229]) (by decide +kernel)
def pv76487 : PrimeValue := ⟨76487, pr76487⟩
private theorem pr76493 : Nat.Prime 76493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv1471]) (by decide +kernel)
def pv76493 : PrimeValue := ⟨76493, pr76493⟩
private theorem pr76507 : Nat.Prime 76507 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv41,pv311]) (by decide +kernel)
def pv76507 : PrimeValue := ⟨76507, pr76507⟩
private theorem pr76511 : Nat.Prime 76511 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv1093]) (by decide +kernel)
def pv76511 : PrimeValue := ⟨76511, pr76511⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
