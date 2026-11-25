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
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr73673 : PrimeCertificate 73673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv9209]) (by decide +kernel)
def pv73673 : PrimeValue := ⟨73673, pr73673⟩
private theorem pr73679 : PrimeCertificate 73679 :=
  certifyPrime (q := pv19) (ls := [pv2,pv11,pv17,pv197]) (by decide +kernel)
def pv73679 : PrimeValue := ⟨73679, pr73679⟩
private theorem pr73681 : PrimeCertificate 73681 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv307]) (by decide +kernel)
def pv73681 : PrimeValue := ⟨73681, pr73681⟩
private theorem pr73693 : PrimeCertificate 73693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv89]) (by decide +kernel)
def pv73693 : PrimeValue := ⟨73693, pr73693⟩
private theorem pr73699 : PrimeCertificate 73699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv71,pv173]) (by decide +kernel)
def pv73699 : PrimeValue := ⟨73699, pr73699⟩
private theorem pr73709 : PrimeCertificate 73709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv18427]) (by decide +kernel)
def pv73709 : PrimeValue := ⟨73709, pr73709⟩
private theorem pr73721 : PrimeCertificate 73721 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv19,pv97]) (by decide +kernel)
def pv73721 : PrimeValue := ⟨73721, pr73721⟩
private theorem pr73727 : PrimeCertificate 73727 :=
  certifyPrime (q := pv5) (ls := [pv2,pv191,pv193]) (by decide +kernel)
def pv73727 : PrimeValue := ⟨73727, pr73727⟩
private theorem pr73751 : PrimeCertificate 73751 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv59]) (by decide +kernel)
def pv73751 : PrimeValue := ⟨73751, pr73751⟩
private theorem pr73757 : PrimeCertificate 73757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv18439]) (by decide +kernel)
def pv73757 : PrimeValue := ⟨73757, pr73757⟩
private theorem pr73771 : PrimeCertificate 73771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv2459]) (by decide +kernel)
def pv73771 : PrimeValue := ⟨73771, pr73771⟩
private theorem pr73783 : PrimeCertificate 73783 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv4099]) (by decide +kernel)
def pv73783 : PrimeValue := ⟨73783, pr73783⟩
private theorem pr73819 : PrimeCertificate 73819 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1367]) (by decide +kernel)
def pv73819 : PrimeValue := ⟨73819, pr73819⟩
private theorem pr73823 : PrimeCertificate 73823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv5273]) (by decide +kernel)
def pv73823 : PrimeValue := ⟨73823, pr73823⟩
private theorem pr73847 : PrimeCertificate 73847 :=
  certifyPrime (q := pv5) (ls := [pv2,pv36923]) (by decide +kernel)
def pv73847 : PrimeValue := ⟨73847, pr73847⟩
private theorem pr73849 : PrimeCertificate 73849 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv181]) (by decide +kernel)
def pv73849 : PrimeValue := ⟨73849, pr73849⟩
private theorem pr73859 : PrimeCertificate 73859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv36929]) (by decide +kernel)
def pv73859 : PrimeValue := ⟨73859, pr73859⟩
private theorem pr73867 : PrimeCertificate 73867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv947]) (by decide +kernel)
def pv73867 : PrimeValue := ⟨73867, pr73867⟩
private theorem pr73877 : PrimeCertificate 73877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv23,pv73]) (by decide +kernel)
def pv73877 : PrimeValue := ⟨73877, pr73877⟩
private theorem pr73883 : PrimeCertificate 73883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv41,pv53]) (by decide +kernel)
def pv73883 : PrimeValue := ⟨73883, pr73883⟩
private theorem pr73897 : PrimeCertificate 73897 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3079]) (by decide +kernel)
def pv73897 : PrimeValue := ⟨73897, pr73897⟩
private theorem pr73907 : PrimeCertificate 73907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv5279]) (by decide +kernel)
def pv73907 : PrimeValue := ⟨73907, pr73907⟩
private theorem pr73939 : PrimeCertificate 73939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv12323]) (by decide +kernel)
def pv73939 : PrimeValue := ⟨73939, pr73939⟩
private theorem pr73943 : PrimeCertificate 73943 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv3361]) (by decide +kernel)
def pv73943 : PrimeValue := ⟨73943, pr73943⟩
private theorem pr73951 : PrimeCertificate 73951 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv17,pv29]) (by decide +kernel)
def pv73951 : PrimeValue := ⟨73951, pr73951⟩
private theorem pr73961 : PrimeCertificate 73961 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv43]) (by decide +kernel)
def pv73961 : PrimeValue := ⟨73961, pr73961⟩
private theorem pr73973 : PrimeCertificate 73973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv18493]) (by decide +kernel)
def pv73973 : PrimeValue := ⟨73973, pr73973⟩
private theorem pr73999 : PrimeCertificate 73999 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv4111]) (by decide +kernel)
def pv73999 : PrimeValue := ⟨73999, pr73999⟩
private theorem pr74017 : PrimeCertificate 74017 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv257]) (by decide +kernel)
def pv74017 : PrimeValue := ⟨74017, pr74017⟩
private theorem pr74021 : PrimeCertificate 74021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv3701]) (by decide +kernel)
def pv74021 : PrimeValue := ⟨74021, pr74021⟩
private theorem pr74027 : PrimeCertificate 74027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37013]) (by decide +kernel)
def pv74027 : PrimeValue := ⟨74027, pr74027⟩
private theorem pr74047 : PrimeCertificate 74047 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv41,pv43]) (by decide +kernel)
def pv74047 : PrimeValue := ⟨74047, pr74047⟩
private theorem pr74051 : PrimeCertificate 74051 :=
  certifyPrime (q := pv29) (ls := [pv2,pv5,pv1481]) (by decide +kernel)
def pv74051 : PrimeValue := ⟨74051, pr74051⟩
private theorem pr74071 : PrimeCertificate 74071 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv823]) (by decide +kernel)
def pv74071 : PrimeValue := ⟨74071, pr74071⟩
private theorem pr74077 : PrimeCertificate 74077 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv6173]) (by decide +kernel)
def pv74077 : PrimeValue := ⟨74077, pr74077⟩
private theorem pr74093 : PrimeCertificate 74093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv18523]) (by decide +kernel)
def pv74093 : PrimeValue := ⟨74093, pr74093⟩
private theorem pr74099 : PrimeCertificate 74099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37049]) (by decide +kernel)
def pv74099 : PrimeValue := ⟨74099, pr74099⟩
private theorem pr74101 : PrimeCertificate 74101 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv19]) (by decide +kernel)
def pv74101 : PrimeValue := ⟨74101, pr74101⟩
private theorem pr74131 : PrimeCertificate 74131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv353]) (by decide +kernel)
def pv74131 : PrimeValue := ⟨74131, pr74131⟩
private theorem pr74143 : PrimeCertificate 74143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1373]) (by decide +kernel)
def pv74143 : PrimeValue := ⟨74143, pr74143⟩
private theorem pr74149 : PrimeCertificate 74149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv167]) (by decide +kernel)
def pv74149 : PrimeValue := ⟨74149, pr74149⟩
private theorem pr74159 : PrimeCertificate 74159 :=
  certifyPrime (q := pv13) (ls := [pv2,pv7,pv5297]) (by decide +kernel)
def pv74159 : PrimeValue := ⟨74159, pr74159⟩
private theorem pr74161 : PrimeCertificate 74161 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv103]) (by decide +kernel)
def pv74161 : PrimeValue := ⟨74161, pr74161⟩
private theorem pr74167 : PrimeCertificate 74167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv47,pv263]) (by decide +kernel)
def pv74167 : PrimeValue := ⟨74167, pr74167⟩
private theorem pr74177 : PrimeCertificate 74177 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv61]) (by decide +kernel)
def pv74177 : PrimeValue := ⟨74177, pr74177⟩
private theorem pr74189 : PrimeCertificate 74189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv1091]) (by decide +kernel)
def pv74189 : PrimeValue := ⟨74189, pr74189⟩
private theorem pr74197 : PrimeCertificate 74197 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv229]) (by decide +kernel)
def pv74197 : PrimeValue := ⟨74197, pr74197⟩
private theorem pr74201 : PrimeCertificate 74201 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv53]) (by decide +kernel)
def pv74201 : PrimeValue := ⟨74201, pr74201⟩
private theorem pr74203 : PrimeCertificate 74203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv83,pv149]) (by decide +kernel)
def pv74203 : PrimeValue := ⟨74203, pr74203⟩
private theorem pr74209 : PrimeCertificate 74209 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv773]) (by decide +kernel)
def pv74209 : PrimeValue := ⟨74209, pr74209⟩
private theorem pr74219 : PrimeCertificate 74219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv863]) (by decide +kernel)
def pv74219 : PrimeValue := ⟨74219, pr74219⟩
private theorem pr74231 : PrimeCertificate 74231 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv13,pv571]) (by decide +kernel)
def pv74231 : PrimeValue := ⟨74231, pr74231⟩
private theorem pr74257 : PrimeCertificate 74257 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv17]) (by decide +kernel)
def pv74257 : PrimeValue := ⟨74257, pr74257⟩
private theorem pr74279 : PrimeCertificate 74279 :=
  certifyPrime (q := pv7) (ls := [pv2,pv37139]) (by decide +kernel)
def pv74279 : PrimeValue := ⟨74279, pr74279⟩
private theorem pr74287 : PrimeCertificate 74287 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv4127]) (by decide +kernel)
def pv74287 : PrimeValue := ⟨74287, pr74287⟩
private theorem pr74293 : PrimeCertificate 74293 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv41,pv151]) (by decide +kernel)
def pv74293 : PrimeValue := ⟨74293, pr74293⟩
private theorem pr74297 : PrimeCertificate 74297 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv251]) (by decide +kernel)
def pv74297 : PrimeValue := ⟨74297, pr74297⟩
private theorem pr74311 : PrimeCertificate 74311 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv2477]) (by decide +kernel)
def pv74311 : PrimeValue := ⟨74311, pr74311⟩
private theorem pr74317 : PrimeCertificate 74317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv563]) (by decide +kernel)
def pv74317 : PrimeValue := ⟨74317, pr74317⟩
private theorem pr74323 : PrimeCertificate 74323 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4129]) (by decide +kernel)
def pv74323 : PrimeValue := ⟨74323, pr74323⟩
private theorem pr74353 : PrimeCertificate 74353 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1549]) (by decide +kernel)
def pv74353 : PrimeValue := ⟨74353, pr74353⟩
private theorem pr74357 : PrimeCertificate 74357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv641]) (by decide +kernel)
def pv74357 : PrimeValue := ⟨74357, pr74357⟩
private theorem pr74363 : PrimeCertificate 74363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37181]) (by decide +kernel)
def pv74363 : PrimeValue := ⟨74363, pr74363⟩
private theorem pr74377 : PrimeCertificate 74377 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1033]) (by decide +kernel)
def pv74377 : PrimeValue := ⟨74377, pr74377⟩
private theorem pr74381 : PrimeCertificate 74381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv3719]) (by decide +kernel)
def pv74381 : PrimeValue := ⟨74381, pr74381⟩
private theorem pr74383 : PrimeCertificate 74383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv23]) (by decide +kernel)
def pv74383 : PrimeValue := ⟨74383, pr74383⟩
private theorem pr74411 : PrimeCertificate 74411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv1063]) (by decide +kernel)
def pv74411 : PrimeValue := ⟨74411, pr74411⟩
private theorem pr74413 : PrimeCertificate 74413 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv53]) (by decide +kernel)
def pv74413 : PrimeValue := ⟨74413, pr74413⟩
private theorem pr74419 : PrimeCertificate 74419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv79,pv157]) (by decide +kernel)
def pv74419 : PrimeValue := ⟨74419, pr74419⟩
private theorem pr74441 : PrimeCertificate 74441 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1861]) (by decide +kernel)
def pv74441 : PrimeValue := ⟨74441, pr74441⟩
private theorem pr74449 : PrimeCertificate 74449 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv47]) (by decide +kernel)
def pv74449 : PrimeValue := ⟨74449, pr74449⟩
private theorem pr74453 : PrimeCertificate 74453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv2659]) (by decide +kernel)
def pv74453 : PrimeValue := ⟨74453, pr74453⟩
private theorem pr74471 : PrimeCertificate 74471 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv677]) (by decide +kernel)
def pv74471 : PrimeValue := ⟨74471, pr74471⟩
private theorem pr74489 : PrimeCertificate 74489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv9311]) (by decide +kernel)
def pv74489 : PrimeValue := ⟨74489, pr74489⟩
private theorem pr74509 : PrimeCertificate 74509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv887]) (by decide +kernel)
def pv74509 : PrimeValue := ⟨74509, pr74509⟩
private theorem pr74521 : PrimeCertificate 74521 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv23]) (by decide +kernel)
def pv74521 : PrimeValue := ⟨74521, pr74521⟩
private theorem pr74527 : PrimeCertificate 74527 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv12421]) (by decide +kernel)
def pv74527 : PrimeValue := ⟨74527, pr74527⟩
private theorem pr74531 : PrimeCertificate 74531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29,pv257]) (by decide +kernel)
def pv74531 : PrimeValue := ⟨74531, pr74531⟩
private theorem pr74551 : PrimeCertificate 74551 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv71]) (by decide +kernel)
def pv74551 : PrimeValue := ⟨74551, pr74551⟩
private theorem pr74561 : PrimeCertificate 74561 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv233]) (by decide +kernel)
def pv74561 : PrimeValue := ⟨74561, pr74561⟩
private theorem pr74567 : PrimeCertificate 74567 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv1621]) (by decide +kernel)
def pv74567 : PrimeValue := ⟨74567, pr74567⟩
private theorem pr74573 : PrimeCertificate 74573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv103,pv181]) (by decide +kernel)
def pv74573 : PrimeValue := ⟨74573, pr74573⟩
private theorem pr74587 : PrimeCertificate 74587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv401]) (by decide +kernel)
def pv74587 : PrimeValue := ⟨74587, pr74587⟩
private theorem pr74597 : PrimeCertificate 74597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv1097]) (by decide +kernel)
def pv74597 : PrimeValue := ⟨74597, pr74597⟩
private theorem pr74609 : PrimeCertificate 74609 :=
  certifyPrime (q := pv3) (ls := [pv2,pv4663]) (by decide +kernel)
def pv74609 : PrimeValue := ⟨74609, pr74609⟩
private theorem pr74611 : PrimeCertificate 74611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv829]) (by decide +kernel)
def pv74611 : PrimeValue := ⟨74611, pr74611⟩
private theorem pr74623 : PrimeCertificate 74623 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv12437]) (by decide +kernel)
def pv74623 : PrimeValue := ⟨74623, pr74623⟩
private theorem pr74653 : PrimeCertificate 74653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv6221]) (by decide +kernel)
def pv74653 : PrimeValue := ⟨74653, pr74653⟩
private theorem pr74687 : PrimeCertificate 74687 :=
  certifyPrime (q := pv5) (ls := [pv2,pv107,pv349]) (by decide +kernel)
def pv74687 : PrimeValue := ⟨74687, pr74687⟩
private theorem pr74699 : PrimeCertificate 74699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv17]) (by decide +kernel)
def pv74699 : PrimeValue := ⟨74699, pr74699⟩
private theorem pr74707 : PrimeCertificate 74707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv12451]) (by decide +kernel)
def pv74707 : PrimeValue := ⟨74707, pr74707⟩
private theorem pr74713 : PrimeCertificate 74713 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv283]) (by decide +kernel)
def pv74713 : PrimeValue := ⟨74713, pr74713⟩
private theorem pr74717 : PrimeCertificate 74717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv18679]) (by decide +kernel)
def pv74717 : PrimeValue := ⟨74717, pr74717⟩
private theorem pr74719 : PrimeCertificate 74719 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv593]) (by decide +kernel)
def pv74719 : PrimeValue := ⟨74719, pr74719⟩
private theorem pr74729 : PrimeCertificate 74729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv9341]) (by decide +kernel)
def pv74729 : PrimeValue := ⟨74729, pr74729⟩
private theorem pr74731 : PrimeCertificate 74731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv47,pv53]) (by decide +kernel)
def pv74731 : PrimeValue := ⟨74731, pr74731⟩
private theorem pr74747 : PrimeCertificate 74747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv19,pv281]) (by decide +kernel)
def pv74747 : PrimeValue := ⟨74747, pr74747⟩
private theorem pr74759 : PrimeCertificate 74759 :=
  certifyPrime (q := pv11) (ls := [pv2,pv37379]) (by decide +kernel)
def pv74759 : PrimeValue := ⟨74759, pr74759⟩
private theorem pr74761 : PrimeCertificate 74761 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv7,pv89]) (by decide +kernel)
def pv74761 : PrimeValue := ⟨74761, pr74761⟩
private theorem pr74771 : PrimeCertificate 74771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7477]) (by decide +kernel)
def pv74771 : PrimeValue := ⟨74771, pr74771⟩
private theorem pr74779 : PrimeCertificate 74779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv103]) (by decide +kernel)
def pv74779 : PrimeValue := ⟨74779, pr74779⟩
private theorem pr74797 : PrimeCertificate 74797 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv271]) (by decide +kernel)
def pv74797 : PrimeValue := ⟨74797, pr74797⟩
private theorem pr74821 : PrimeCertificate 74821 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv29,pv43]) (by decide +kernel)
def pv74821 : PrimeValue := ⟨74821, pr74821⟩
private theorem pr74827 : PrimeCertificate 74827 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv4157]) (by decide +kernel)
def pv74827 : PrimeValue := ⟨74827, pr74827⟩
private theorem pr74831 : PrimeCertificate 74831 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv1069]) (by decide +kernel)
def pv74831 : PrimeValue := ⟨74831, pr74831⟩
private theorem pr74843 : PrimeCertificate 74843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv1627]) (by decide +kernel)
def pv74843 : PrimeValue := ⟨74843, pr74843⟩
private theorem pr74857 : PrimeCertificate 74857 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3119]) (by decide +kernel)
def pv74857 : PrimeValue := ⟨74857, pr74857⟩
private theorem pr74869 : PrimeCertificate 74869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv367]) (by decide +kernel)
def pv74869 : PrimeValue := ⟨74869, pr74869⟩
private theorem pr74873 : PrimeCertificate 74873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv191]) (by decide +kernel)
def pv74873 : PrimeValue := ⟨74873, pr74873⟩
private theorem pr74887 : PrimeCertificate 74887 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv1783]) (by decide +kernel)
def pv74887 : PrimeValue := ⟨74887, pr74887⟩
private theorem pr74891 : PrimeCertificate 74891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7489]) (by decide +kernel)
def pv74891 : PrimeValue := ⟨74891, pr74891⟩
private theorem pr74897 : PrimeCertificate 74897 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv151]) (by decide +kernel)
def pv74897 : PrimeValue := ⟨74897, pr74897⟩
private theorem pr74903 : PrimeCertificate 74903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv2203]) (by decide +kernel)
def pv74903 : PrimeValue := ⟨74903, pr74903⟩
private theorem pr74923 : PrimeCertificate 74923 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv12487]) (by decide +kernel)
def pv74923 : PrimeValue := ⟨74923, pr74923⟩
private theorem pr74929 : PrimeCertificate 74929 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv223]) (by decide +kernel)
def pv74929 : PrimeValue := ⟨74929, pr74929⟩
private theorem pr74933 : PrimeCertificate 74933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13,pv131]) (by decide +kernel)
def pv74933 : PrimeValue := ⟨74933, pr74933⟩
private theorem pr74941 : PrimeCertificate 74941 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv1249]) (by decide +kernel)
def pv74941 : PrimeValue := ⟨74941, pr74941⟩
private theorem pr74959 : PrimeCertificate 74959 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv31]) (by decide +kernel)
def pv74959 : PrimeValue := ⟨74959, pr74959⟩
private theorem pr75011 : PrimeCertificate 75011 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv13,pv577]) (by decide +kernel)
def pv75011 : PrimeValue := ⟨75011, pr75011⟩
private theorem pr75013 : PrimeCertificate 75013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv19,pv47]) (by decide +kernel)
def pv75013 : PrimeValue := ⟨75013, pr75013⟩
private theorem pr75017 : PrimeCertificate 75017 :=
  certifyPrime (q := pv3) (ls := [pv2,pv9377]) (by decide +kernel)
def pv75017 : PrimeValue := ⟨75017, pr75017⟩
private theorem pr75029 : PrimeCertificate 75029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv18757]) (by decide +kernel)
def pv75029 : PrimeValue := ⟨75029, pr75029⟩
private theorem pr75037 : PrimeCertificate 75037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv37]) (by decide +kernel)
def pv75037 : PrimeValue := ⟨75037, pr75037⟩
private theorem pr75041 : PrimeCertificate 75041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv67]) (by decide +kernel)
def pv75041 : PrimeValue := ⟨75041, pr75041⟩
private theorem pr75079 : PrimeCertificate 75079 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv43,pv97]) (by decide +kernel)
def pv75079 : PrimeValue := ⟨75079, pr75079⟩
private theorem pr75083 : PrimeCertificate 75083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv31,pv173]) (by decide +kernel)
def pv75083 : PrimeValue := ⟨75083, pr75083⟩
private theorem pr75109 : PrimeCertificate 75109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv569]) (by decide +kernel)
def pv75109 : PrimeValue := ⟨75109, pr75109⟩
private theorem pr75133 : PrimeCertificate 75133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv2087]) (by decide +kernel)
def pv75133 : PrimeValue := ⟨75133, pr75133⟩
private theorem pr75149 : PrimeCertificate 75149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv18787]) (by decide +kernel)
def pv75149 : PrimeValue := ⟨75149, pr75149⟩
private theorem pr75161 : PrimeCertificate 75161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1879]) (by decide +kernel)
def pv75161 : PrimeValue := ⟨75161, pr75161⟩
private theorem pr75167 : PrimeCertificate 75167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv13,pv59]) (by decide +kernel)
def pv75167 : PrimeValue := ⟨75167, pr75167⟩
private theorem pr75169 : PrimeCertificate 75169 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv29]) (by decide +kernel)
def pv75169 : PrimeValue := ⟨75169, pr75169⟩
private theorem pr75181 : PrimeCertificate 75181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv179]) (by decide +kernel)
def pv75181 : PrimeValue := ⟨75181, pr75181⟩
private theorem pr75193 : PrimeCertificate 75193 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv241]) (by decide +kernel)
def pv75193 : PrimeValue := ⟨75193, pr75193⟩
private theorem pr75209 : PrimeCertificate 75209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv17,pv79]) (by decide +kernel)
def pv75209 : PrimeValue := ⟨75209, pr75209⟩
private theorem pr75211 : PrimeCertificate 75211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv23,pv109]) (by decide +kernel)
def pv75211 : PrimeValue := ⟨75211, pr75211⟩
private theorem pr75217 : PrimeCertificate 75217 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1567]) (by decide +kernel)
def pv75217 : PrimeValue := ⟨75217, pr75217⟩
private theorem pr75223 : PrimeCertificate 75223 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv199]) (by decide +kernel)
def pv75223 : PrimeValue := ⟨75223, pr75223⟩
private theorem pr75227 : PrimeCertificate 75227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv1297]) (by decide +kernel)
def pv75227 : PrimeValue := ⟨75227, pr75227⟩
private theorem pr75239 : PrimeCertificate 75239 :=
  certifyPrime (q := pv13) (ls := [pv2,pv37619]) (by decide +kernel)
def pv75239 : PrimeValue := ⟨75239, pr75239⟩
private theorem pr75253 : PrimeCertificate 75253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv6271]) (by decide +kernel)
def pv75253 : PrimeValue := ⟨75253, pr75253⟩
private theorem pr75269 : PrimeCertificate 75269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv607]) (by decide +kernel)
def pv75269 : PrimeValue := ⟨75269, pr75269⟩
private theorem pr75277 : PrimeCertificate 75277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv41]) (by decide +kernel)
def pv75277 : PrimeValue := ⟨75277, pr75277⟩
private theorem pr75289 : PrimeCertificate 75289 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv3137]) (by decide +kernel)
def pv75289 : PrimeValue := ⟨75289, pr75289⟩
private theorem pr75307 : PrimeCertificate 75307 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv163]) (by decide +kernel)
def pv75307 : PrimeValue := ⟨75307, pr75307⟩
private theorem pr75323 : PrimeCertificate 75323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv2897]) (by decide +kernel)
def pv75323 : PrimeValue := ⟨75323, pr75323⟩
private theorem pr75329 : PrimeCertificate 75329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv107]) (by decide +kernel)
def pv75329 : PrimeValue := ⟨75329, pr75329⟩
private theorem pr75337 : PrimeCertificate 75337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv43,pv73]) (by decide +kernel)
def pv75337 : PrimeValue := ⟨75337, pr75337⟩
private theorem pr75347 : PrimeCertificate 75347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv101,pv373]) (by decide +kernel)
def pv75347 : PrimeValue := ⟨75347, pr75347⟩
private theorem pr75353 : PrimeCertificate 75353 :=
  certifyPrime (q := pv3) (ls := [pv2,pv9419]) (by decide +kernel)
def pv75353 : PrimeValue := ⟨75353, pr75353⟩
private theorem pr75377 : PrimeCertificate 75377 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv673]) (by decide +kernel)
def pv75377 : PrimeValue := ⟨75377, pr75377⟩
private theorem pr75389 : PrimeCertificate 75389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv401]) (by decide +kernel)
def pv75389 : PrimeValue := ⟨75389, pr75389⟩
private theorem pr75391 : PrimeCertificate 75391 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv359]) (by decide +kernel)
def pv75391 : PrimeValue := ⟨75391, pr75391⟩
private theorem pr75401 : PrimeCertificate 75401 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv29]) (by decide +kernel)
def pv75401 : PrimeValue := ⟨75401, pr75401⟩
private theorem pr75403 : PrimeCertificate 75403 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv59,pv71]) (by decide +kernel)
def pv75403 : PrimeValue := ⟨75403, pr75403⟩
private theorem pr75407 : PrimeCertificate 75407 :=
  certifyPrime (q := pv5) (ls := [pv2,pv37,pv1019]) (by decide +kernel)
def pv75407 : PrimeValue := ⟨75407, pr75407⟩
private theorem pr75431 : PrimeCertificate 75431 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv19,pv397]) (by decide +kernel)
def pv75431 : PrimeValue := ⟨75431, pr75431⟩
private theorem pr75437 : PrimeCertificate 75437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv18859]) (by decide +kernel)
def pv75437 : PrimeValue := ⟨75437, pr75437⟩
private theorem pr75479 : PrimeCertificate 75479 :=
  certifyPrime (q := pv19) (ls := [pv2,pv13,pv2903]) (by decide +kernel)
def pv75479 : PrimeValue := ⟨75479, pr75479⟩
private theorem pr75503 : PrimeCertificate 75503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv5393]) (by decide +kernel)
def pv75503 : PrimeValue := ⟨75503, pr75503⟩
private theorem pr75511 : PrimeCertificate 75511 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv839]) (by decide +kernel)
def pv75511 : PrimeValue := ⟨75511, pr75511⟩
private theorem pr75521 : PrimeCertificate 75521 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv59]) (by decide +kernel)
def pv75521 : PrimeValue := ⟨75521, pr75521⟩
private theorem pr75527 : PrimeCertificate 75527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv3433]) (by decide +kernel)
def pv75527 : PrimeValue := ⟨75527, pr75527⟩
private theorem pr75533 : PrimeCertificate 75533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv821]) (by decide +kernel)
def pv75533 : PrimeValue := ⟨75533, pr75533⟩
private theorem pr75539 : PrimeCertificate 75539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv179,pv211]) (by decide +kernel)
def pv75539 : PrimeValue := ⟨75539, pr75539⟩
private theorem pr75541 : PrimeCertificate 75541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1259]) (by decide +kernel)
def pv75541 : PrimeValue := ⟨75541, pr75541⟩
private theorem pr75553 : PrimeCertificate 75553 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv787]) (by decide +kernel)
def pv75553 : PrimeValue := ⟨75553, pr75553⟩
private theorem pr75557 : PrimeCertificate 75557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv1453]) (by decide +kernel)
def pv75557 : PrimeValue := ⟨75557, pr75557⟩
private theorem pr75571 : PrimeCertificate 75571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv229]) (by decide +kernel)
def pv75571 : PrimeValue := ⟨75571, pr75571⟩
private theorem pr75577 : PrimeCertificate 75577 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv47,pv67]) (by decide +kernel)
def pv75577 : PrimeValue := ⟨75577, pr75577⟩
private theorem pr75583 : PrimeCertificate 75583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv17,pv19]) (by decide +kernel)
def pv75583 : PrimeValue := ⟨75583, pr75583⟩
private theorem pr75611 : PrimeCertificate 75611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7561]) (by decide +kernel)
def pv75611 : PrimeValue := ⟨75611, pr75611⟩
private theorem pr75617 : PrimeCertificate 75617 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv139]) (by decide +kernel)
def pv75617 : PrimeValue := ⟨75617, pr75617⟩
private theorem pr75619 : PrimeCertificate 75619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv4201]) (by decide +kernel)
def pv75619 : PrimeValue := ⟨75619, pr75619⟩
private theorem pr75629 : PrimeCertificate 75629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv37,pv73]) (by decide +kernel)
def pv75629 : PrimeValue := ⟨75629, pr75629⟩
private theorem pr75641 : PrimeCertificate 75641 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv31,pv61]) (by decide +kernel)
def pv75641 : PrimeValue := ⟨75641, pr75641⟩
private theorem pr75653 : PrimeCertificate 75653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv18913]) (by decide +kernel)
def pv75653 : PrimeValue := ⟨75653, pr75653⟩
private theorem pr75659 : PrimeCertificate 75659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv19,pv181]) (by decide +kernel)
def pv75659 : PrimeValue := ⟨75659, pr75659⟩
private theorem pr75679 : PrimeCertificate 75679 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv12613]) (by decide +kernel)
def pv75679 : PrimeValue := ⟨75679, pr75679⟩
private theorem pr75683 : PrimeCertificate 75683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv79,pv479]) (by decide +kernel)
def pv75683 : PrimeValue := ⟨75683, pr75683⟩
private theorem pr75689 : PrimeCertificate 75689 :=
  certifyPrime (q := pv3) (ls := [pv2,pv9461]) (by decide +kernel)
def pv75689 : PrimeValue := ⟨75689, pr75689⟩
private theorem pr75703 : PrimeCertificate 75703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv31,pv37]) (by decide +kernel)
def pv75703 : PrimeValue := ⟨75703, pr75703⟩
private theorem pr75707 : PrimeCertificate 75707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37853]) (by decide +kernel)
def pv75707 : PrimeValue := ⟨75707, pr75707⟩
private theorem pr75709 : PrimeCertificate 75709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv701]) (by decide +kernel)
def pv75709 : PrimeValue := ⟨75709, pr75709⟩
private theorem pr75721 : PrimeCertificate 75721 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv631]) (by decide +kernel)
def pv75721 : PrimeValue := ⟨75721, pr75721⟩
private theorem pr75731 : PrimeCertificate 75731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7573]) (by decide +kernel)
def pv75731 : PrimeValue := ⟨75731, pr75731⟩
private theorem pr75743 : PrimeCertificate 75743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv37871]) (by decide +kernel)
def pv75743 : PrimeValue := ⟨75743, pr75743⟩
private theorem pr75767 : PrimeCertificate 75767 :=
  certifyPrime (q := pv5) (ls := [pv2,pv43,pv881]) (by decide +kernel)
def pv75767 : PrimeValue := ⟨75767, pr75767⟩
private theorem pr75773 : PrimeCertificate 75773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv997]) (by decide +kernel)
def pv75773 : PrimeValue := ⟨75773, pr75773⟩
private theorem pr75781 : PrimeCertificate 75781 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv421]) (by decide +kernel)
def pv75781 : PrimeValue := ⟨75781, pr75781⟩
private theorem pr75787 : PrimeCertificate 75787 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv743]) (by decide +kernel)
def pv75787 : PrimeValue := ⟨75787, pr75787⟩
private theorem pr75793 : PrimeCertificate 75793 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv1579]) (by decide +kernel)
def pv75793 : PrimeValue := ⟨75793, pr75793⟩
private theorem pr75797 : PrimeCertificate 75797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv2707]) (by decide +kernel)
def pv75797 : PrimeValue := ⟨75797, pr75797⟩
private theorem pr75821 : PrimeCertificate 75821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv223]) (by decide +kernel)
def pv75821 : PrimeValue := ⟨75821, pr75821⟩
private theorem pr75833 : PrimeCertificate 75833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv9479]) (by decide +kernel)
def pv75833 : PrimeValue := ⟨75833, pr75833⟩
private theorem pr75853 : PrimeCertificate 75853 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv43]) (by decide +kernel)
def pv75853 : PrimeValue := ⟨75853, pr75853⟩
private theorem pr75869 : PrimeCertificate 75869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv1459]) (by decide +kernel)
def pv75869 : PrimeValue := ⟨75869, pr75869⟩
private theorem pr75883 : PrimeCertificate 75883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv12647]) (by decide +kernel)
def pv75883 : PrimeValue := ⟨75883, pr75883⟩
private theorem pr75913 : PrimeCertificate 75913 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3163]) (by decide +kernel)
def pv75913 : PrimeValue := ⟨75913, pr75913⟩
private theorem pr75931 : PrimeCertificate 75931 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv2531]) (by decide +kernel)
def pv75931 : PrimeValue := ⟨75931, pr75931⟩
private theorem pr75937 : PrimeCertificate 75937 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv7,pv113]) (by decide +kernel)
def pv75937 : PrimeValue := ⟨75937, pr75937⟩
private theorem pr75941 : PrimeCertificate 75941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv3797]) (by decide +kernel)
def pv75941 : PrimeValue := ⟨75941, pr75941⟩
private theorem pr75967 : PrimeCertificate 75967 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv1151]) (by decide +kernel)
def pv75967 : PrimeValue := ⟨75967, pr75967⟩
private theorem pr75979 : PrimeCertificate 75979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv67]) (by decide +kernel)
def pv75979 : PrimeValue := ⟨75979, pr75979⟩
private theorem pr75983 : PrimeCertificate 75983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv37991]) (by decide +kernel)
def pv75983 : PrimeValue := ⟨75983, pr75983⟩
private theorem pr75989 : PrimeCertificate 75989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv157]) (by decide +kernel)
def pv75989 : PrimeValue := ⟨75989, pr75989⟩
private theorem pr75991 : PrimeCertificate 75991 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv17,pv149]) (by decide +kernel)
def pv75991 : PrimeValue := ⟨75991, pr75991⟩
private theorem pr75997 : PrimeCertificate 75997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv2111]) (by decide +kernel)
def pv75997 : PrimeValue := ⟨75997, pr75997⟩
private theorem pr76001 : PrimeCertificate 76001 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv19]) (by decide +kernel)
def pv76001 : PrimeValue := ⟨76001, pr76001⟩
private theorem pr76003 : PrimeCertificate 76003 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv53,pv239]) (by decide +kernel)
def pv76003 : PrimeValue := ⟨76003, pr76003⟩
private theorem pr76031 : PrimeCertificate 76031 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7603]) (by decide +kernel)
def pv76031 : PrimeValue := ⟨76031, pr76031⟩
private theorem pr76039 : PrimeCertificate 76039 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv19,pv23,pv29]) (by decide +kernel)
def pv76039 : PrimeValue := ⟨76039, pr76039⟩
private theorem pr76079 : PrimeCertificate 76079 :=
  certifyPrime (q := pv11) (ls := [pv2,pv38039]) (by decide +kernel)
def pv76079 : PrimeValue := ⟨76079, pr76079⟩
private theorem pr76081 : PrimeCertificate 76081 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv317]) (by decide +kernel)
def pv76081 : PrimeValue := ⟨76081, pr76081⟩
private theorem pr76091 : PrimeCertificate 76091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv1087]) (by decide +kernel)
def pv76091 : PrimeValue := ⟨76091, pr76091⟩
private theorem pr76099 : PrimeCertificate 76099 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv1153]) (by decide +kernel)
def pv76099 : PrimeValue := ⟨76099, pr76099⟩
private theorem pr76103 : PrimeCertificate 76103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv2927]) (by decide +kernel)
def pv76103 : PrimeValue := ⟨76103, pr76103⟩
private theorem pr76123 : PrimeCertificate 76123 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv4229]) (by decide +kernel)
def pv76123 : PrimeValue := ⟨76123, pr76123⟩
private theorem pr76129 : PrimeCertificate 76129 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13,pv61]) (by decide +kernel)
def pv76129 : PrimeValue := ⟨76129, pr76129⟩
private theorem pr76147 : PrimeCertificate 76147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv37]) (by decide +kernel)
def pv76147 : PrimeValue := ⟨76147, pr76147⟩
private theorem pr76157 : PrimeCertificate 76157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv79,pv241]) (by decide +kernel)
def pv76157 : PrimeValue := ⟨76157, pr76157⟩
private theorem pr76159 : PrimeCertificate 76159 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv4231]) (by decide +kernel)
def pv76159 : PrimeValue := ⟨76159, pr76159⟩
private theorem pr76163 : PrimeCertificate 76163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv113,pv337]) (by decide +kernel)
def pv76163 : PrimeValue := ⟨76163, pr76163⟩
private theorem pr76207 : PrimeCertificate 76207 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv977]) (by decide +kernel)
def pv76207 : PrimeValue := ⟨76207, pr76207⟩
private theorem pr76213 : PrimeCertificate 76213 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29,pv73]) (by decide +kernel)
def pv76213 : PrimeValue := ⟨76213, pr76213⟩
private theorem pr76231 : PrimeCertificate 76231 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv11]) (by decide +kernel)
def pv76231 : PrimeValue := ⟨76231, pr76231⟩
private theorem pr76243 : PrimeCertificate 76243 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv97,pv131]) (by decide +kernel)
def pv76243 : PrimeValue := ⟨76243, pr76243⟩
private theorem pr76249 : PrimeCertificate 76249 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv353]) (by decide +kernel)
def pv76249 : PrimeValue := ⟨76249, pr76249⟩
private theorem pr76253 : PrimeCertificate 76253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv1733]) (by decide +kernel)
def pv76253 : PrimeValue := ⟨76253, pr76253⟩
private theorem pr76259 : PrimeCertificate 76259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv419]) (by decide +kernel)
def pv76259 : PrimeValue := ⟨76259, pr76259⟩
private theorem pr76261 : PrimeCertificate 76261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv31,pv41]) (by decide +kernel)
def pv76261 : PrimeValue := ⟨76261, pr76261⟩
private theorem pr76283 : PrimeCertificate 76283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv887]) (by decide +kernel)
def pv76283 : PrimeValue := ⟨76283, pr76283⟩
private theorem pr76289 : PrimeCertificate 76289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv149]) (by decide +kernel)
def pv76289 : PrimeValue := ⟨76289, pr76289⟩
private theorem pr76303 : PrimeCertificate 76303 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv157]) (by decide +kernel)
def pv76303 : PrimeValue := ⟨76303, pr76303⟩
private theorem pr76333 : PrimeCertificate 76333 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv6361]) (by decide +kernel)
def pv76333 : PrimeValue := ⟨76333, pr76333⟩
private theorem pr76343 : PrimeCertificate 76343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv19,pv41]) (by decide +kernel)
def pv76343 : PrimeValue := ⟨76343, pr76343⟩
private theorem pr76369 : PrimeCertificate 76369 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv37,pv43]) (by decide +kernel)
def pv76369 : PrimeValue := ⟨76369, pr76369⟩
private theorem pr76379 : PrimeCertificate 76379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv38189]) (by decide +kernel)
def pv76379 : PrimeValue := ⟨76379, pr76379⟩
private theorem pr76387 : PrimeCertificate 76387 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv439]) (by decide +kernel)
def pv76387 : PrimeValue := ⟨76387, pr76387⟩
private theorem pr76403 : PrimeCertificate 76403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv38201]) (by decide +kernel)
def pv76403 : PrimeValue := ⟨76403, pr76403⟩
private theorem pr76421 : PrimeCertificate 76421 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv3821]) (by decide +kernel)
def pv76421 : PrimeValue := ⟨76421, pr76421⟩
private theorem pr76423 : PrimeCertificate 76423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv47,pv271]) (by decide +kernel)
def pv76423 : PrimeValue := ⟨76423, pr76423⟩
private theorem pr76441 : PrimeCertificate 76441 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv13]) (by decide +kernel)
def pv76441 : PrimeValue := ⟨76441, pr76441⟩
private theorem pr76463 : PrimeCertificate 76463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv38231]) (by decide +kernel)
def pv76463 : PrimeValue := ⟨76463, pr76463⟩
private theorem pr76471 : PrimeCertificate 76471 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv2549]) (by decide +kernel)
def pv76471 : PrimeValue := ⟨76471, pr76471⟩
private theorem pr76481 : PrimeCertificate 76481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv239]) (by decide +kernel)
def pv76481 : PrimeValue := ⟨76481, pr76481⟩
private theorem pr76487 : PrimeCertificate 76487 :=
  certifyPrime (q := pv5) (ls := [pv2,pv167,pv229]) (by decide +kernel)
def pv76487 : PrimeValue := ⟨76487, pr76487⟩
private theorem pr76493 : PrimeCertificate 76493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv1471]) (by decide +kernel)
def pv76493 : PrimeValue := ⟨76493, pr76493⟩
private theorem pr76507 : PrimeCertificate 76507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv311]) (by decide +kernel)
def pv76507 : PrimeValue := ⟨76507, pr76507⟩
private theorem pr76511 : PrimeCertificate 76511 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv1093]) (by decide +kernel)
def pv76511 : PrimeValue := ⟨76511, pr76511⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
