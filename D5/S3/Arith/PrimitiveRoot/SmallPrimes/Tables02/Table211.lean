/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table211
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table211.pv746041
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table014
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table017
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table029
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table045
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table046
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table096

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr746041 : Nat.Prime 746041 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv6217]) (by decide +kernel)
def pv746041 : PrimeValue := ⟨746041, pr746041⟩
private theorem pr746477 : Nat.Prime 746477 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv186619]) (by decide +kernel)
def pv746477 : PrimeValue := ⟨746477, pr746477⟩
private theorem pr746483 : Nat.Prime 746483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv33931]) (by decide +kernel)
def pv746483 : PrimeValue := ⟨746483, pr746483⟩
private theorem pr746497 : Nat.Prime 746497 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3]) (by decide +kernel)
def pv746497 : PrimeValue := ⟨746497, pr746497⟩
private theorem pr746531 : Nat.Prime 746531 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv74653]) (by decide +kernel)
def pv746531 : PrimeValue := ⟨746531, pr746531⟩
private theorem pr746533 : Nat.Prime 746533 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv89,pv233]) (by decide +kernel)
def pv746533 : PrimeValue := ⟨746533, pr746533⟩
private theorem pr746653 : Nat.Prime 746653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv43,pv1447]) (by decide +kernel)
def pv746653 : PrimeValue := ⟨746653, pr746653⟩
private theorem pr746797 : Nat.Prime 746797 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv62233]) (by decide +kernel)
def pv746797 : PrimeValue := ⟨746797, pr746797⟩
private theorem pr747053 : Nat.Prime 747053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv186763]) (by decide +kernel)
def pv747053 : PrimeValue := ⟨747053, pr747053⟩
private theorem pr747157 : Nat.Prime 747157 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv29,pv113]) (by decide +kernel)
def pv747157 : PrimeValue := ⟨747157, pr747157⟩
private theorem pr747277 : Nat.Prime 747277 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv62273]) (by decide +kernel)
def pv747277 : PrimeValue := ⟨747277, pr747277⟩
private theorem pr747323 : Nat.Prime 747323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv373661]) (by decide +kernel)
def pv747323 : PrimeValue := ⟨747323, pr747323⟩
private theorem pr747361 : Nat.Prime 747361 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv173]) (by decide +kernel)
def pv747361 : PrimeValue := ⟨747361, pr747361⟩
private theorem pr747457 : Nat.Prime 747457 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv17,pv229]) (by decide +kernel)
def pv747457 : PrimeValue := ⟨747457, pr747457⟩
private theorem pr747493 : Nat.Prime 747493 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv167,pv373]) (by decide +kernel)
def pv747493 : PrimeValue := ⟨747493, pr747493⟩
private theorem pr747497 : Nat.Prime 747497 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv223,pv419]) (by decide +kernel)
def pv747497 : PrimeValue := ⟨747497, pr747497⟩
private theorem pr747563 : Nat.Prime 747563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv12889]) (by decide +kernel)
def pv747563 : PrimeValue := ⟨747563, pr747563⟩
private theorem pr747647 : Nat.Prime 747647 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv373823]) (by decide +kernel)
def pv747647 : PrimeValue := ⟨747647, pr747647⟩
private theorem pr747743 : Nat.Prime 747743 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv461,pv811]) (by decide +kernel)
def pv747743 : PrimeValue := ⟨747743, pr747743⟩
private theorem pr747917 : Nat.Prime 747917 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv19,pv757]) (by decide +kernel)
def pv747917 : PrimeValue := ⟨747917, pr747917⟩
private theorem pr747953 : Nat.Prime 747953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv46747]) (by decide +kernel)
def pv747953 : PrimeValue := ⟨747953, pr747953⟩
private theorem pr748513 : Nat.Prime 748513 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23,pv113]) (by decide +kernel)
def pv748513 : PrimeValue := ⟨748513, pr748513⟩
private theorem pr748687 : Nat.Prime 748687 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv124781]) (by decide +kernel)
def pv748687 : PrimeValue := ⟨748687, pr748687⟩
private theorem pr748921 : Nat.Prime 748921 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv79]) (by decide +kernel)
def pv748921 : PrimeValue := ⟨748921, pr748921⟩
private theorem pr748963 : Nat.Prime 748963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv41609]) (by decide +kernel)
def pv748963 : PrimeValue := ⟨748963, pr748963⟩
private theorem pr749011 : Nat.Prime 749011 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv24967]) (by decide +kernel)
def pv749011 : PrimeValue := ⟨749011, pr749011⟩
private theorem pr749081 : Nat.Prime 749081 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv61,pv307]) (by decide +kernel)
def pv749081 : PrimeValue := ⟨749081, pr749081⟩
private theorem pr749143 : Nat.Prime 749143 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13873]) (by decide +kernel)
def pv749143 : PrimeValue := ⟨749143, pr749143⟩
private theorem pr749347 : Nat.Prime 749347 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv739]) (by decide +kernel)
def pv749347 : PrimeValue := ⟨749347, pr749347⟩
private theorem pr749383 : Nat.Prime 749383 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv124897]) (by decide +kernel)
def pv749383 : PrimeValue := ⟨749383, pr749383⟩
private theorem pr749423 : Nat.Prime 749423 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv97,pv3863]) (by decide +kernel)
def pv749423 : PrimeValue := ⟨749423, pr749423⟩
private theorem pr749557 : Nat.Prime 749557 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv47,pv443]) (by decide +kernel)
def pv749557 : PrimeValue := ⟨749557, pr749557⟩
private theorem pr749653 : Nat.Prime 749653 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv179,pv349]) (by decide +kernel)
def pv749653 : PrimeValue := ⟨749653, pr749653⟩
private theorem pr749843 : Nat.Prime 749843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv10133]) (by decide +kernel)
def pv749843 : PrimeValue := ⟨749843, pr749843⟩
private theorem pr749851 : Nat.Prime 749851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv4999]) (by decide +kernel)
def pv749851 : PrimeValue := ⟨749851, pr749851⟩
private theorem pr749893 : Nat.Prime 749893 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv13,pv19,pv23]) (by decide +kernel)
def pv749893 : PrimeValue := ⟨749893, pr749893⟩
private theorem pr750131 : Nat.Prime 750131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv75013]) (by decide +kernel)
def pv750131 : PrimeValue := ⟨750131, pr750131⟩
private theorem pr750133 : Nat.Prime 750133 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv67,pv311]) (by decide +kernel)
def pv750133 : PrimeValue := ⟨750133, pr750133⟩
private theorem pr750151 : Nat.Prime 750151 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv1667]) (by decide +kernel)
def pv750151 : PrimeValue := ⟨750151, pr750151⟩
private theorem pr750157 : Nat.Prime 750157 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv5683]) (by decide +kernel)
def pv750157 : PrimeValue := ⟨750157, pr750157⟩
private theorem pr750287 : Nat.Prime 750287 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv37,pv10139]) (by decide +kernel)
def pv750287 : PrimeValue := ⟨750287, pr750287⟩
private theorem pr750437 : Nat.Prime 750437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv4363]) (by decide +kernel)
def pv750437 : PrimeValue := ⟨750437, pr750437⟩
private theorem pr750571 : Nat.Prime 750571 :=
  checkPrime_prime (q := pv43) (ls := [pv2,pv3,pv5,pv127,pv197]) (by decide +kernel)
def pv750571 : PrimeValue := ⟨750571, pr750571⟩
private theorem pr750691 : Nat.Prime 750691 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv439]) (by decide +kernel)
def pv750691 : PrimeValue := ⟨750691, pr750691⟩
private theorem pr750707 : Nat.Prime 750707 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv34123]) (by decide +kernel)
def pv750707 : PrimeValue := ⟨750707, pr750707⟩
private theorem pr750917 : Nat.Prime 750917 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv227,pv827]) (by decide +kernel)
def pv750917 : PrimeValue := ⟨750917, pr750917⟩
private theorem pr750977 : Nat.Prime 750977 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5867]) (by decide +kernel)
def pv750977 : PrimeValue := ⟨750977, pr750977⟩
private theorem pr750983 : Nat.Prime 750983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv89,pv4219]) (by decide +kernel)
def pv750983 : PrimeValue := ⟨750983, pr750983⟩
private theorem pr751007 : Nat.Prime 751007 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv31,pv12113]) (by decide +kernel)
def pv751007 : PrimeValue := ⟨751007, pr751007⟩
private theorem pr751021 : Nat.Prime 751021 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv12517]) (by decide +kernel)
def pv751021 : PrimeValue := ⟨751021, pr751021⟩
private theorem pr751151 : Nat.Prime 751151 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv83,pv181]) (by decide +kernel)
def pv751151 : PrimeValue := ⟨751151, pr751151⟩
private theorem pr751183 : Nat.Prime 751183 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv125197]) (by decide +kernel)
def pv751183 : PrimeValue := ⟨751183, pr751183⟩
private theorem pr751273 : Nat.Prime 751273 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23,pv1361]) (by decide +kernel)
def pv751273 : PrimeValue := ⟨751273, pr751273⟩
private theorem pr751351 : Nat.Prime 751351 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv5009]) (by decide +kernel)
def pv751351 : PrimeValue := ⟨751351, pr751351⟩
private theorem pr751481 : Nat.Prime 751481 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv18787]) (by decide +kernel)
def pv751481 : PrimeValue := ⟨751481, pr751481⟩
private theorem pr751627 : Nat.Prime 751627 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv31,pv449]) (by decide +kernel)
def pv751627 : PrimeValue := ⟨751627, pr751627⟩
private theorem pr751691 : Nat.Prime 751691 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv75169]) (by decide +kernel)
def pv751691 : PrimeValue := ⟨751691, pr751691⟩
private theorem pr751763 : Nat.Prime 751763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv34171]) (by decide +kernel)
def pv751763 : PrimeValue := ⟨751763, pr751763⟩
private theorem pr751921 : Nat.Prime 751921 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv13,pv241]) (by decide +kernel)
def pv751921 : PrimeValue := ⟨751921, pr751921⟩
private theorem pr752083 : Nat.Prime 752083 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv163,pv769]) (by decide +kernel)
def pv752083 : PrimeValue := ⟨752083, pr752083⟩
private theorem pr752177 : Nat.Prime 752177 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv53,pv887]) (by decide +kernel)
def pv752177 : PrimeValue := ⟨752177, pr752177⟩
private theorem pr752183 : Nat.Prime 752183 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv22123]) (by decide +kernel)
def pv752183 : PrimeValue := ⟨752183, pr752183⟩
private theorem pr752293 : Nat.Prime 752293 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv20897]) (by decide +kernel)
def pv752293 : PrimeValue := ⟨752293, pr752293⟩
private theorem pr752413 : Nat.Prime 752413 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv62701]) (by decide +kernel)
def pv752413 : PrimeValue := ⟨752413, pr752413⟩
private theorem pr752581 : Nat.Prime 752581 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv37,pv113]) (by decide +kernel)
def pv752581 : PrimeValue := ⟨752581, pr752581⟩
private theorem pr752701 : Nat.Prime 752701 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv13,pv193]) (by decide +kernel)
def pv752701 : PrimeValue := ⟨752701, pr752701⟩
private theorem pr752831 : Nat.Prime 752831 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv5791]) (by decide +kernel)
def pv752831 : PrimeValue := ⟨752831, pr752831⟩
private theorem pr752891 : Nat.Prime 752891 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv75289]) (by decide +kernel)
def pv752891 : PrimeValue := ⟨752891, pr752891⟩
private theorem pr752903 : Nat.Prime 752903 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv487,pv773]) (by decide +kernel)
def pv752903 : PrimeValue := ⟨752903, pr752903⟩
private theorem pr753031 : Nat.Prime 753031 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv2789]) (by decide +kernel)
def pv753031 : PrimeValue := ⟨753031, pr753031⟩
private theorem pr753161 : Nat.Prime 753161 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv19,pv991]) (by decide +kernel)
def pv753161 : PrimeValue := ⟨753161, pr753161⟩
private theorem pr753307 : Nat.Prime 753307 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv125551]) (by decide +kernel)
def pv753307 : PrimeValue := ⟨753307, pr753307⟩
private theorem pr753373 : Nat.Prime 753373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv1231]) (by decide +kernel)
def pv753373 : PrimeValue := ⟨753373, pr753373⟩
private theorem pr753427 : Nat.Prime 753427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv2203]) (by decide +kernel)
def pv753427 : PrimeValue := ⟨753427, pr753427⟩
private theorem pr753461 : Nat.Prime 753461 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv101,pv373]) (by decide +kernel)
def pv753461 : PrimeValue := ⟨753461, pr753461⟩
private theorem pr753497 : Nat.Prime 753497 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv97,pv971]) (by decide +kernel)
def pv753497 : PrimeValue := ⟨753497, pr753497⟩
private theorem pr753587 : Nat.Prime 753587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv376793]) (by decide +kernel)
def pv753587 : PrimeValue := ⟨753587, pr753587⟩
private theorem pr753721 : Nat.Prime 753721 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv571]) (by decide +kernel)
def pv753721 : PrimeValue := ⟨753721, pr753721⟩
private theorem pr753941 : Nat.Prime 753941 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv23,pv149]) (by decide +kernel)
def pv753941 : PrimeValue := ⟨753941, pr753941⟩
private theorem pr754003 : Nat.Prime 754003 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv13963]) (by decide +kernel)
def pv754003 : PrimeValue := ⟨754003, pr754003⟩
private theorem pr754217 : Nat.Prime 754217 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv4099]) (by decide +kernel)
def pv754217 : PrimeValue := ⟨754217, pr754217⟩
private theorem pr754267 : Nat.Prime 754267 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv125711]) (by decide +kernel)
def pv754267 : PrimeValue := ⟨754267, pr754267⟩
private theorem pr754333 : Nat.Prime 754333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv62861]) (by decide +kernel)
def pv754333 : PrimeValue := ⟨754333, pr754333⟩
private theorem pr754381 : Nat.Prime 754381 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv127]) (by decide +kernel)
def pv754381 : PrimeValue := ⟨754381, pr754381⟩
private theorem pr754451 : Nat.Prime 754451 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv79,pv191]) (by decide +kernel)
def pv754451 : PrimeValue := ⟨754451, pr754451⟩
private theorem pr754513 : Nat.Prime 754513 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv1429]) (by decide +kernel)
def pv754513 : PrimeValue := ⟨754513, pr754513⟩
private theorem pr754651 : Nat.Prime 754651 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv13,pv43]) (by decide +kernel)
def pv754651 : PrimeValue := ⟨754651, pr754651⟩
private theorem pr754751 : Nat.Prime 754751 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv3019]) (by decide +kernel)
def pv754751 : PrimeValue := ⟨754751, pr754751⟩
private theorem pr754771 : Nat.Prime 754771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv139,pv181]) (by decide +kernel)
def pv754771 : PrimeValue := ⟨754771, pr754771⟩
private theorem pr754861 : Nat.Prime 754861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv23,pv547]) (by decide +kernel)
def pv754861 : PrimeValue := ⟨754861, pr754861⟩
private theorem pr754877 : Nat.Prime 754877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv188719]) (by decide +kernel)
def pv754877 : PrimeValue := ⟨754877, pr754877⟩
private theorem pr754891 : Nat.Prime 754891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv25163]) (by decide +kernel)
def pv754891 : PrimeValue := ⟨754891, pr754891⟩
private theorem pr754903 : Nat.Prime 754903 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv2467]) (by decide +kernel)
def pv754903 : PrimeValue := ⟨754903, pr754903⟩
private theorem pr755033 : Nat.Prime 755033 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv94379]) (by decide +kernel)
def pv755033 : PrimeValue := ⟨755033, pr755033⟩
private theorem pr755057 : Nat.Prime 755057 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv41,pv1151]) (by decide +kernel)
def pv755057 : PrimeValue := ⟨755057, pr755057⟩
private theorem pr755233 : Nat.Prime 755233 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7867]) (by decide +kernel)
def pv755233 : PrimeValue := ⟨755233, pr755233⟩
private theorem pr755257 : Nat.Prime 755257 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv31469]) (by decide +kernel)
def pv755257 : PrimeValue := ⟨755257, pr755257⟩
private theorem pr755267 : Nat.Prime 755267 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv377633]) (by decide +kernel)
def pv755267 : PrimeValue := ⟨755267, pr755267⟩
private theorem pr755311 : Nat.Prime 755311 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv17,pv1481]) (by decide +kernel)
def pv755311 : PrimeValue := ⟨755311, pr755311⟩
private theorem pr755317 : Nat.Prime 755317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv20981]) (by decide +kernel)
def pv755317 : PrimeValue := ⟨755317, pr755317⟩
private theorem pr755333 : Nat.Prime 755333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv188833]) (by decide +kernel)
def pv755333 : PrimeValue := ⟨755333, pr755333⟩
private theorem pr755597 : Nat.Prime 755597 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv43,pv191]) (by decide +kernel)
def pv755597 : PrimeValue := ⟨755597, pr755597⟩
private theorem pr755767 : Nat.Prime 755767 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv347]) (by decide +kernel)
def pv755767 : PrimeValue := ⟨755767, pr755767⟩
private theorem pr755977 : Nat.Prime 755977 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv13,pv2423]) (by decide +kernel)
def pv755977 : PrimeValue := ⟨755977, pr755977⟩
private theorem pr756023 : Nat.Prime 756023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv378011]) (by decide +kernel)
def pv756023 : PrimeValue := ⟨756023, pr756023⟩
private theorem pr756097 : Nat.Prime 756097 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv179]) (by decide +kernel)
def pv756097 : PrimeValue := ⟨756097, pr756097⟩
private theorem pr756331 : Nat.Prime 756331 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv17,pv1483]) (by decide +kernel)
def pv756331 : PrimeValue := ⟨756331, pr756331⟩
private theorem pr756527 : Nat.Prime 756527 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv293,pv1291]) (by decide +kernel)
def pv756527 : PrimeValue := ⟨756527, pr756527⟩
private theorem pr756541 : Nat.Prime 756541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv467]) (by decide +kernel)
def pv756541 : PrimeValue := ⟨756541, pr756541⟩
private theorem pr756571 : Nat.Prime 756571 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv25219]) (by decide +kernel)
def pv756571 : PrimeValue := ⟨756571, pr756571⟩
private theorem pr756601 : Nat.Prime 756601 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv13,pv97]) (by decide +kernel)
def pv756601 : PrimeValue := ⟨756601, pr756601⟩
private theorem pr756703 : Nat.Prime 756703 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv173]) (by decide +kernel)
def pv756703 : PrimeValue := ⟨756703, pr756703⟩
private theorem pr756727 : Nat.Prime 756727 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29,pv4349]) (by decide +kernel)
def pv756727 : PrimeValue := ⟨756727, pr756727⟩
private theorem pr756881 : Nat.Prime 756881 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv9461]) (by decide +kernel)
def pv756881 : PrimeValue := ⟨756881, pr756881⟩
private theorem pr756971 : Nat.Prime 756971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv59,pv1283]) (by decide +kernel)
def pv756971 : PrimeValue := ⟨756971, pr756971⟩
private theorem pr757201 : Nat.Prime 757201 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv3,pv5,pv631]) (by decide +kernel)
def pv757201 : PrimeValue := ⟨757201, pr757201⟩
private theorem pr757543 : Nat.Prime 757543 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv126257]) (by decide +kernel)
def pv757543 : PrimeValue := ⟨757543, pr757543⟩
private theorem pr757607 : Nat.Prime 757607 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv19937]) (by decide +kernel)
def pv757607 : PrimeValue := ⟨757607, pr757607⟩
private theorem pr757633 : Nat.Prime 757633 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1973]) (by decide +kernel)
def pv757633 : PrimeValue := ⟨757633, pr757633⟩
private theorem pr757661 : Nat.Prime 757661 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv43,pv881]) (by decide +kernel)
def pv757661 : PrimeValue := ⟨757661, pr757661⟩
private theorem pr757763 : Nat.Prime 757763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv9241]) (by decide +kernel)
def pv757763 : PrimeValue := ⟨757763, pr757763⟩
private theorem pr757903 : Nat.Prime 757903 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv126317]) (by decide +kernel)
def pv757903 : PrimeValue := ⟨757903, pr757903⟩
private theorem pr758111 : Nat.Prime 758111 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv47,pv1613]) (by decide +kernel)
def pv758111 : PrimeValue := ⟨758111, pr758111⟩
private theorem pr758323 : Nat.Prime 758323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv151]) (by decide +kernel)
def pv758323 : PrimeValue := ⟨758323, pr758323⟩
private theorem pr758363 : Nat.Prime 758363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv34471]) (by decide +kernel)
def pv758363 : PrimeValue := ⟨758363, pr758363⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
