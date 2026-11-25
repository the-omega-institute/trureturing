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
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr746041 : PrimeCertificate 746041 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv6217]) (by decide +kernel)
def pv746041 : PrimeValue := ⟨746041, pr746041⟩
private theorem pr746477 : PrimeCertificate 746477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv186619]) (by decide +kernel)
def pv746477 : PrimeValue := ⟨746477, pr746477⟩
private theorem pr746483 : PrimeCertificate 746483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv33931]) (by decide +kernel)
def pv746483 : PrimeValue := ⟨746483, pr746483⟩
private theorem pr746497 : PrimeCertificate 746497 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3]) (by decide +kernel)
def pv746497 : PrimeValue := ⟨746497, pr746497⟩
private theorem pr746531 : PrimeCertificate 746531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv74653]) (by decide +kernel)
def pv746531 : PrimeValue := ⟨746531, pr746531⟩
private theorem pr746533 : PrimeCertificate 746533 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv89,pv233]) (by decide +kernel)
def pv746533 : PrimeValue := ⟨746533, pr746533⟩
private theorem pr746653 : PrimeCertificate 746653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv1447]) (by decide +kernel)
def pv746653 : PrimeValue := ⟨746653, pr746653⟩
private theorem pr746797 : PrimeCertificate 746797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv62233]) (by decide +kernel)
def pv746797 : PrimeValue := ⟨746797, pr746797⟩
private theorem pr747053 : PrimeCertificate 747053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv186763]) (by decide +kernel)
def pv747053 : PrimeValue := ⟨747053, pr747053⟩
private theorem pr747157 : PrimeCertificate 747157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv29,pv113]) (by decide +kernel)
def pv747157 : PrimeValue := ⟨747157, pr747157⟩
private theorem pr747277 : PrimeCertificate 747277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv62273]) (by decide +kernel)
def pv747277 : PrimeValue := ⟨747277, pr747277⟩
private theorem pr747323 : PrimeCertificate 747323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv373661]) (by decide +kernel)
def pv747323 : PrimeValue := ⟨747323, pr747323⟩
private theorem pr747361 : PrimeCertificate 747361 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv173]) (by decide +kernel)
def pv747361 : PrimeValue := ⟨747361, pr747361⟩
private theorem pr747457 : PrimeCertificate 747457 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv17,pv229]) (by decide +kernel)
def pv747457 : PrimeValue := ⟨747457, pr747457⟩
private theorem pr747493 : PrimeCertificate 747493 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv167,pv373]) (by decide +kernel)
def pv747493 : PrimeValue := ⟨747493, pr747493⟩
private theorem pr747497 : PrimeCertificate 747497 :=
  certifyPrime (q := pv3) (ls := [pv2,pv223,pv419]) (by decide +kernel)
def pv747497 : PrimeValue := ⟨747497, pr747497⟩
private theorem pr747563 : PrimeCertificate 747563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv12889]) (by decide +kernel)
def pv747563 : PrimeValue := ⟨747563, pr747563⟩
private theorem pr747647 : PrimeCertificate 747647 :=
  certifyPrime (q := pv5) (ls := [pv2,pv373823]) (by decide +kernel)
def pv747647 : PrimeValue := ⟨747647, pr747647⟩
private theorem pr747743 : PrimeCertificate 747743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv461,pv811]) (by decide +kernel)
def pv747743 : PrimeValue := ⟨747743, pr747743⟩
private theorem pr747917 : PrimeCertificate 747917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv19,pv757]) (by decide +kernel)
def pv747917 : PrimeValue := ⟨747917, pr747917⟩
private theorem pr747953 : PrimeCertificate 747953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv46747]) (by decide +kernel)
def pv747953 : PrimeValue := ⟨747953, pr747953⟩
private theorem pr748513 : PrimeCertificate 748513 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv113]) (by decide +kernel)
def pv748513 : PrimeValue := ⟨748513, pr748513⟩
private theorem pr748687 : PrimeCertificate 748687 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv124781]) (by decide +kernel)
def pv748687 : PrimeValue := ⟨748687, pr748687⟩
private theorem pr748921 : PrimeCertificate 748921 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv79]) (by decide +kernel)
def pv748921 : PrimeValue := ⟨748921, pr748921⟩
private theorem pr748963 : PrimeCertificate 748963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41609]) (by decide +kernel)
def pv748963 : PrimeValue := ⟨748963, pr748963⟩
private theorem pr749011 : PrimeCertificate 749011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv24967]) (by decide +kernel)
def pv749011 : PrimeValue := ⟨749011, pr749011⟩
private theorem pr749081 : PrimeCertificate 749081 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv61,pv307]) (by decide +kernel)
def pv749081 : PrimeValue := ⟨749081, pr749081⟩
private theorem pr749143 : PrimeCertificate 749143 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13873]) (by decide +kernel)
def pv749143 : PrimeValue := ⟨749143, pr749143⟩
private theorem pr749347 : PrimeCertificate 749347 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv739]) (by decide +kernel)
def pv749347 : PrimeValue := ⟨749347, pr749347⟩
private theorem pr749383 : PrimeCertificate 749383 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv124897]) (by decide +kernel)
def pv749383 : PrimeValue := ⟨749383, pr749383⟩
private theorem pr749423 : PrimeCertificate 749423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv97,pv3863]) (by decide +kernel)
def pv749423 : PrimeValue := ⟨749423, pr749423⟩
private theorem pr749557 : PrimeCertificate 749557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv443]) (by decide +kernel)
def pv749557 : PrimeValue := ⟨749557, pr749557⟩
private theorem pr749653 : PrimeCertificate 749653 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv179,pv349]) (by decide +kernel)
def pv749653 : PrimeValue := ⟨749653, pr749653⟩
private theorem pr749843 : PrimeCertificate 749843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv10133]) (by decide +kernel)
def pv749843 : PrimeValue := ⟨749843, pr749843⟩
private theorem pr749851 : PrimeCertificate 749851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv4999]) (by decide +kernel)
def pv749851 : PrimeValue := ⟨749851, pr749851⟩
private theorem pr749893 : PrimeCertificate 749893 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv13,pv19,pv23]) (by decide +kernel)
def pv749893 : PrimeValue := ⟨749893, pr749893⟩
private theorem pr750131 : PrimeCertificate 750131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv75013]) (by decide +kernel)
def pv750131 : PrimeValue := ⟨750131, pr750131⟩
private theorem pr750133 : PrimeCertificate 750133 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv67,pv311]) (by decide +kernel)
def pv750133 : PrimeValue := ⟨750133, pr750133⟩
private theorem pr750151 : PrimeCertificate 750151 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv1667]) (by decide +kernel)
def pv750151 : PrimeValue := ⟨750151, pr750151⟩
private theorem pr750157 : PrimeCertificate 750157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv5683]) (by decide +kernel)
def pv750157 : PrimeValue := ⟨750157, pr750157⟩
private theorem pr750287 : PrimeCertificate 750287 :=
  certifyPrime (q := pv5) (ls := [pv2,pv37,pv10139]) (by decide +kernel)
def pv750287 : PrimeValue := ⟨750287, pr750287⟩
private theorem pr750437 : PrimeCertificate 750437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv4363]) (by decide +kernel)
def pv750437 : PrimeValue := ⟨750437, pr750437⟩
private theorem pr750571 : PrimeCertificate 750571 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv5,pv127,pv197]) (by decide +kernel)
def pv750571 : PrimeValue := ⟨750571, pr750571⟩
private theorem pr750691 : PrimeCertificate 750691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv439]) (by decide +kernel)
def pv750691 : PrimeValue := ⟨750691, pr750691⟩
private theorem pr750707 : PrimeCertificate 750707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv34123]) (by decide +kernel)
def pv750707 : PrimeValue := ⟨750707, pr750707⟩
private theorem pr750917 : PrimeCertificate 750917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv227,pv827]) (by decide +kernel)
def pv750917 : PrimeValue := ⟨750917, pr750917⟩
private theorem pr750977 : PrimeCertificate 750977 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5867]) (by decide +kernel)
def pv750977 : PrimeValue := ⟨750977, pr750977⟩
private theorem pr750983 : PrimeCertificate 750983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv89,pv4219]) (by decide +kernel)
def pv750983 : PrimeValue := ⟨750983, pr750983⟩
private theorem pr751007 : PrimeCertificate 751007 :=
  certifyPrime (q := pv5) (ls := [pv2,pv31,pv12113]) (by decide +kernel)
def pv751007 : PrimeValue := ⟨751007, pr751007⟩
private theorem pr751021 : PrimeCertificate 751021 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv12517]) (by decide +kernel)
def pv751021 : PrimeValue := ⟨751021, pr751021⟩
private theorem pr751151 : PrimeCertificate 751151 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv83,pv181]) (by decide +kernel)
def pv751151 : PrimeValue := ⟨751151, pr751151⟩
private theorem pr751183 : PrimeCertificate 751183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv125197]) (by decide +kernel)
def pv751183 : PrimeValue := ⟨751183, pr751183⟩
private theorem pr751273 : PrimeCertificate 751273 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv1361]) (by decide +kernel)
def pv751273 : PrimeValue := ⟨751273, pr751273⟩
private theorem pr751351 : PrimeCertificate 751351 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv5009]) (by decide +kernel)
def pv751351 : PrimeValue := ⟨751351, pr751351⟩
private theorem pr751481 : PrimeCertificate 751481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv18787]) (by decide +kernel)
def pv751481 : PrimeValue := ⟨751481, pr751481⟩
private theorem pr751627 : PrimeCertificate 751627 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv31,pv449]) (by decide +kernel)
def pv751627 : PrimeValue := ⟨751627, pr751627⟩
private theorem pr751691 : PrimeCertificate 751691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv75169]) (by decide +kernel)
def pv751691 : PrimeValue := ⟨751691, pr751691⟩
private theorem pr751763 : PrimeCertificate 751763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv34171]) (by decide +kernel)
def pv751763 : PrimeValue := ⟨751763, pr751763⟩
private theorem pr751921 : PrimeCertificate 751921 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv13,pv241]) (by decide +kernel)
def pv751921 : PrimeValue := ⟨751921, pr751921⟩
private theorem pr752083 : PrimeCertificate 752083 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv163,pv769]) (by decide +kernel)
def pv752083 : PrimeValue := ⟨752083, pr752083⟩
private theorem pr752177 : PrimeCertificate 752177 :=
  certifyPrime (q := pv3) (ls := [pv2,pv53,pv887]) (by decide +kernel)
def pv752177 : PrimeValue := ⟨752177, pr752177⟩
private theorem pr752183 : PrimeCertificate 752183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv22123]) (by decide +kernel)
def pv752183 : PrimeValue := ⟨752183, pr752183⟩
private theorem pr752293 : PrimeCertificate 752293 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv20897]) (by decide +kernel)
def pv752293 : PrimeValue := ⟨752293, pr752293⟩
private theorem pr752413 : PrimeCertificate 752413 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv62701]) (by decide +kernel)
def pv752413 : PrimeValue := ⟨752413, pr752413⟩
private theorem pr752581 : PrimeCertificate 752581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv37,pv113]) (by decide +kernel)
def pv752581 : PrimeValue := ⟨752581, pr752581⟩
private theorem pr752701 : PrimeCertificate 752701 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv13,pv193]) (by decide +kernel)
def pv752701 : PrimeValue := ⟨752701, pr752701⟩
private theorem pr752831 : PrimeCertificate 752831 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv5791]) (by decide +kernel)
def pv752831 : PrimeValue := ⟨752831, pr752831⟩
private theorem pr752891 : PrimeCertificate 752891 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv75289]) (by decide +kernel)
def pv752891 : PrimeValue := ⟨752891, pr752891⟩
private theorem pr752903 : PrimeCertificate 752903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv487,pv773]) (by decide +kernel)
def pv752903 : PrimeValue := ⟨752903, pr752903⟩
private theorem pr753031 : PrimeCertificate 753031 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv2789]) (by decide +kernel)
def pv753031 : PrimeValue := ⟨753031, pr753031⟩
private theorem pr753161 : PrimeCertificate 753161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv19,pv991]) (by decide +kernel)
def pv753161 : PrimeValue := ⟨753161, pr753161⟩
private theorem pr753307 : PrimeCertificate 753307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv125551]) (by decide +kernel)
def pv753307 : PrimeValue := ⟨753307, pr753307⟩
private theorem pr753373 : PrimeCertificate 753373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv1231]) (by decide +kernel)
def pv753373 : PrimeValue := ⟨753373, pr753373⟩
private theorem pr753427 : PrimeCertificate 753427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv2203]) (by decide +kernel)
def pv753427 : PrimeValue := ⟨753427, pr753427⟩
private theorem pr753461 : PrimeCertificate 753461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv101,pv373]) (by decide +kernel)
def pv753461 : PrimeValue := ⟨753461, pr753461⟩
private theorem pr753497 : PrimeCertificate 753497 :=
  certifyPrime (q := pv3) (ls := [pv2,pv97,pv971]) (by decide +kernel)
def pv753497 : PrimeValue := ⟨753497, pr753497⟩
private theorem pr753587 : PrimeCertificate 753587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv376793]) (by decide +kernel)
def pv753587 : PrimeValue := ⟨753587, pr753587⟩
private theorem pr753721 : PrimeCertificate 753721 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv571]) (by decide +kernel)
def pv753721 : PrimeValue := ⟨753721, pr753721⟩
private theorem pr753941 : PrimeCertificate 753941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv23,pv149]) (by decide +kernel)
def pv753941 : PrimeValue := ⟨753941, pr753941⟩
private theorem pr754003 : PrimeCertificate 754003 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv13963]) (by decide +kernel)
def pv754003 : PrimeValue := ⟨754003, pr754003⟩
private theorem pr754217 : PrimeCertificate 754217 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv4099]) (by decide +kernel)
def pv754217 : PrimeValue := ⟨754217, pr754217⟩
private theorem pr754267 : PrimeCertificate 754267 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv125711]) (by decide +kernel)
def pv754267 : PrimeValue := ⟨754267, pr754267⟩
private theorem pr754333 : PrimeCertificate 754333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv62861]) (by decide +kernel)
def pv754333 : PrimeValue := ⟨754333, pr754333⟩
private theorem pr754381 : PrimeCertificate 754381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv127]) (by decide +kernel)
def pv754381 : PrimeValue := ⟨754381, pr754381⟩
private theorem pr754451 : PrimeCertificate 754451 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv79,pv191]) (by decide +kernel)
def pv754451 : PrimeValue := ⟨754451, pr754451⟩
private theorem pr754513 : PrimeCertificate 754513 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv1429]) (by decide +kernel)
def pv754513 : PrimeValue := ⟨754513, pr754513⟩
private theorem pr754651 : PrimeCertificate 754651 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv13,pv43]) (by decide +kernel)
def pv754651 : PrimeValue := ⟨754651, pr754651⟩
private theorem pr754751 : PrimeCertificate 754751 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv3019]) (by decide +kernel)
def pv754751 : PrimeValue := ⟨754751, pr754751⟩
private theorem pr754771 : PrimeCertificate 754771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv139,pv181]) (by decide +kernel)
def pv754771 : PrimeValue := ⟨754771, pr754771⟩
private theorem pr754861 : PrimeCertificate 754861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv23,pv547]) (by decide +kernel)
def pv754861 : PrimeValue := ⟨754861, pr754861⟩
private theorem pr754877 : PrimeCertificate 754877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv188719]) (by decide +kernel)
def pv754877 : PrimeValue := ⟨754877, pr754877⟩
private theorem pr754891 : PrimeCertificate 754891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv25163]) (by decide +kernel)
def pv754891 : PrimeValue := ⟨754891, pr754891⟩
private theorem pr754903 : PrimeCertificate 754903 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv2467]) (by decide +kernel)
def pv754903 : PrimeValue := ⟨754903, pr754903⟩
private theorem pr755033 : PrimeCertificate 755033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv94379]) (by decide +kernel)
def pv755033 : PrimeValue := ⟨755033, pr755033⟩
private theorem pr755057 : PrimeCertificate 755057 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41,pv1151]) (by decide +kernel)
def pv755057 : PrimeValue := ⟨755057, pr755057⟩
private theorem pr755233 : PrimeCertificate 755233 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7867]) (by decide +kernel)
def pv755233 : PrimeValue := ⟨755233, pr755233⟩
private theorem pr755257 : PrimeCertificate 755257 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31469]) (by decide +kernel)
def pv755257 : PrimeValue := ⟨755257, pr755257⟩
private theorem pr755267 : PrimeCertificate 755267 :=
  certifyPrime (q := pv2) (ls := [pv2,pv377633]) (by decide +kernel)
def pv755267 : PrimeValue := ⟨755267, pr755267⟩
private theorem pr755311 : PrimeCertificate 755311 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv17,pv1481]) (by decide +kernel)
def pv755311 : PrimeValue := ⟨755311, pr755311⟩
private theorem pr755317 : PrimeCertificate 755317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv20981]) (by decide +kernel)
def pv755317 : PrimeValue := ⟨755317, pr755317⟩
private theorem pr755333 : PrimeCertificate 755333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv188833]) (by decide +kernel)
def pv755333 : PrimeValue := ⟨755333, pr755333⟩
private theorem pr755597 : PrimeCertificate 755597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv43,pv191]) (by decide +kernel)
def pv755597 : PrimeValue := ⟨755597, pr755597⟩
private theorem pr755767 : PrimeCertificate 755767 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv347]) (by decide +kernel)
def pv755767 : PrimeValue := ⟨755767, pr755767⟩
private theorem pr755977 : PrimeCertificate 755977 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv13,pv2423]) (by decide +kernel)
def pv755977 : PrimeValue := ⟨755977, pr755977⟩
private theorem pr756023 : PrimeCertificate 756023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv378011]) (by decide +kernel)
def pv756023 : PrimeValue := ⟨756023, pr756023⟩
private theorem pr756097 : PrimeCertificate 756097 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv179]) (by decide +kernel)
def pv756097 : PrimeValue := ⟨756097, pr756097⟩
private theorem pr756331 : PrimeCertificate 756331 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv17,pv1483]) (by decide +kernel)
def pv756331 : PrimeValue := ⟨756331, pr756331⟩
private theorem pr756527 : PrimeCertificate 756527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv293,pv1291]) (by decide +kernel)
def pv756527 : PrimeValue := ⟨756527, pr756527⟩
private theorem pr756541 : PrimeCertificate 756541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv467]) (by decide +kernel)
def pv756541 : PrimeValue := ⟨756541, pr756541⟩
private theorem pr756571 : PrimeCertificate 756571 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv25219]) (by decide +kernel)
def pv756571 : PrimeValue := ⟨756571, pr756571⟩
private theorem pr756601 : PrimeCertificate 756601 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv13,pv97]) (by decide +kernel)
def pv756601 : PrimeValue := ⟨756601, pr756601⟩
private theorem pr756703 : PrimeCertificate 756703 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv173]) (by decide +kernel)
def pv756703 : PrimeValue := ⟨756703, pr756703⟩
private theorem pr756727 : PrimeCertificate 756727 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv4349]) (by decide +kernel)
def pv756727 : PrimeValue := ⟨756727, pr756727⟩
private theorem pr756881 : PrimeCertificate 756881 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv9461]) (by decide +kernel)
def pv756881 : PrimeValue := ⟨756881, pr756881⟩
private theorem pr756971 : PrimeCertificate 756971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv59,pv1283]) (by decide +kernel)
def pv756971 : PrimeValue := ⟨756971, pr756971⟩
private theorem pr757201 : PrimeCertificate 757201 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv5,pv631]) (by decide +kernel)
def pv757201 : PrimeValue := ⟨757201, pr757201⟩
private theorem pr757543 : PrimeCertificate 757543 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv126257]) (by decide +kernel)
def pv757543 : PrimeValue := ⟨757543, pr757543⟩
private theorem pr757607 : PrimeCertificate 757607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv19937]) (by decide +kernel)
def pv757607 : PrimeValue := ⟨757607, pr757607⟩
private theorem pr757633 : PrimeCertificate 757633 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1973]) (by decide +kernel)
def pv757633 : PrimeValue := ⟨757633, pr757633⟩
private theorem pr757661 : PrimeCertificate 757661 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv43,pv881]) (by decide +kernel)
def pv757661 : PrimeValue := ⟨757661, pr757661⟩
private theorem pr757763 : PrimeCertificate 757763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv9241]) (by decide +kernel)
def pv757763 : PrimeValue := ⟨757763, pr757763⟩
private theorem pr757903 : PrimeCertificate 757903 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv126317]) (by decide +kernel)
def pv757903 : PrimeValue := ⟨757903, pr757903⟩
private theorem pr758111 : PrimeCertificate 758111 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv47,pv1613]) (by decide +kernel)
def pv758111 : PrimeValue := ⟨758111, pr758111⟩
private theorem pr758323 : PrimeCertificate 758323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv151]) (by decide +kernel)
def pv758323 : PrimeValue := ⟨758323, pr758323⟩
private theorem pr758363 : PrimeCertificate 758363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv34471]) (by decide +kernel)
def pv758363 : PrimeValue := ⟨758363, pr758363⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
