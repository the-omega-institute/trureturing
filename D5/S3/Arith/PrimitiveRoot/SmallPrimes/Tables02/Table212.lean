/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table212
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table212.pv758551
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table017
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table029
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table030
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table046
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table096
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table097

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr758551 : Nat.Prime 758551 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv5,pv13,pv389]) (by decide +kernel)
def pv758551 : PrimeValue := ⟨758551, pr758551⟩
private theorem pr758573 : Nat.Prime 758573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv189643]) (by decide +kernel)
def pv758573 : PrimeValue := ⟨758573, pr758573⟩
private theorem pr758687 : Nat.Prime 758687 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv379343]) (by decide +kernel)
def pv758687 : PrimeValue := ⟨758687, pr758687⟩
private theorem pr758971 : Nat.Prime 758971 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv937]) (by decide +kernel)
def pv758971 : PrimeValue := ⟨758971, pr758971⟩
private theorem pr759001 : Nat.Prime 759001 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv5,pv11,pv23]) (by decide +kernel)
def pv759001 : PrimeValue := ⟨759001, pr759001⟩
private theorem pr759103 : Nat.Prime 759103 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv126517]) (by decide +kernel)
def pv759103 : PrimeValue := ⟨759103, pr759103⟩
private theorem pr759181 : Nat.Prime 759181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv12653]) (by decide +kernel)
def pv759181 : PrimeValue := ⟨759181, pr759181⟩
private theorem pr759223 : Nat.Prime 759223 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv42179]) (by decide +kernel)
def pv759223 : PrimeValue := ⟨759223, pr759223⟩
private theorem pr759287 : Nat.Prime 759287 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv34513]) (by decide +kernel)
def pv759287 : PrimeValue := ⟨759287, pr759287⟩
private theorem pr759377 : Nat.Prime 759377 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv1531]) (by decide +kernel)
def pv759377 : PrimeValue := ⟨759377, pr759377⟩
private theorem pr759401 : Nat.Prime 759401 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv3797]) (by decide +kernel)
def pv759401 : PrimeValue := ⟨759401, pr759401⟩
private theorem pr759463 : Nat.Prime 759463 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv37,pv311]) (by decide +kernel)
def pv759463 : PrimeValue := ⟨759463, pr759463⟩
private theorem pr759491 : Nat.Prime 759491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv53,pv1433]) (by decide +kernel)
def pv759491 : PrimeValue := ⟨759491, pr759491⟩
private theorem pr759637 : Nat.Prime 759637 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv21101]) (by decide +kernel)
def pv759637 : PrimeValue := ⟨759637, pr759637⟩
private theorem pr759701 : Nat.Prime 759701 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv71,pv107]) (by decide +kernel)
def pv759701 : PrimeValue := ⟨759701, pr759701⟩
private theorem pr759821 : Nat.Prime 759821 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv37991]) (by decide +kernel)
def pv759821 : PrimeValue := ⟨759821, pr759821⟩
private theorem pr759881 : Nat.Prime 759881 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv157]) (by decide +kernel)
def pv759881 : PrimeValue := ⟨759881, pr759881⟩
private theorem pr759923 : Nat.Prime 759923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv409,pv929]) (by decide +kernel)
def pv759923 : PrimeValue := ⟨759923, pr759923⟩
private theorem pr759947 : Nat.Prime 759947 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv34543]) (by decide +kernel)
def pv759947 : PrimeValue := ⟨759947, pr759947⟩
private theorem pr759961 : Nat.Prime 759961 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv2111]) (by decide +kernel)
def pv759961 : PrimeValue := ⟨759961, pr759961⟩
private theorem pr760141 : Nat.Prime 760141 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv41,pv103]) (by decide +kernel)
def pv760141 : PrimeValue := ⟨760141, pr760141⟩
private theorem pr760147 : Nat.Prime 760147 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv126691]) (by decide +kernel)
def pv760147 : PrimeValue := ⟨760147, pr760147⟩
private theorem pr760267 : Nat.Prime 760267 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv19]) (by decide +kernel)
def pv760267 : PrimeValue := ⟨760267, pr760267⟩
private theorem pr760273 : Nat.Prime 760273 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv47,pv337]) (by decide +kernel)
def pv760273 : PrimeValue := ⟨760273, pr760273⟩
private theorem pr760301 : Nat.Prime 760301 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7603]) (by decide +kernel)
def pv760301 : PrimeValue := ⟨760301, pr760301⟩
private theorem pr760423 : Nat.Prime 760423 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv9749]) (by decide +kernel)
def pv760423 : PrimeValue := ⟨760423, pr760423⟩
private theorem pr760457 : Nat.Prime 760457 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv5003]) (by decide +kernel)
def pv760457 : PrimeValue := ⟨760457, pr760457⟩
private theorem pr760553 : Nat.Prime 760553 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv71,pv103]) (by decide +kernel)
def pv760553 : PrimeValue := ⟨760553, pr760553⟩
private theorem pr760561 : Nat.Prime 760561 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv3169]) (by decide +kernel)
def pv760561 : PrimeValue := ⟨760561, pr760561⟩
private theorem pr760841 : Nat.Prime 760841 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv23,pv827]) (by decide +kernel)
def pv760841 : PrimeValue := ⟨760841, pr760841⟩
private theorem pr760927 : Nat.Prime 760927 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv31,pv4091]) (by decide +kernel)
def pv760927 : PrimeValue := ⟨760927, pr760927⟩
private theorem pr760933 : Nat.Prime 760933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv919]) (by decide +kernel)
def pv760933 : PrimeValue := ⟨760933, pr760933⟩
private theorem pr761003 : Nat.Prime 761003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv34591]) (by decide +kernel)
def pv761003 : PrimeValue := ⟨761003, pr761003⟩
private theorem pr761203 : Nat.Prime 761203 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv3253]) (by decide +kernel)
def pv761203 : PrimeValue := ⟨761203, pr761203⟩
private theorem pr761261 : Nat.Prime 761261 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17,pv2239]) (by decide +kernel)
def pv761261 : PrimeValue := ⟨761261, pr761261⟩
private theorem pr761263 : Nat.Prime 761263 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv71,pv1787]) (by decide +kernel)
def pv761263 : PrimeValue := ⟨761263, pr761263⟩
private theorem pr761357 : Nat.Prime 761357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv190339]) (by decide +kernel)
def pv761357 : PrimeValue := ⟨761357, pr761357⟩
private theorem pr761437 : Nat.Prime 761437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv1627]) (by decide +kernel)
def pv761437 : PrimeValue := ⟨761437, pr761437⟩
private theorem pr761441 : Nat.Prime 761441 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv4759]) (by decide +kernel)
def pv761441 : PrimeValue := ⟨761441, pr761441⟩
private theorem pr761471 : Nat.Prime 761471 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv76147]) (by decide +kernel)
def pv761471 : PrimeValue := ⟨761471, pr761471⟩
private theorem pr761483 : Nat.Prime 761483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv29,pv691]) (by decide +kernel)
def pv761483 : PrimeValue := ⟨761483, pr761483⟩
private theorem pr761521 : Nat.Prime 761521 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv19,pv167]) (by decide +kernel)
def pv761521 : PrimeValue := ⟨761521, pr761521⟩
private theorem pr761591 : Nat.Prime 761591 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv5,pv76159]) (by decide +kernel)
def pv761591 : PrimeValue := ⟨761591, pr761591⟩
private theorem pr761603 : Nat.Prime 761603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv197,pv1933]) (by decide +kernel)
def pv761603 : PrimeValue := ⟨761603, pr761603⟩
private theorem pr761611 : Nat.Prime 761611 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv53,pv479]) (by decide +kernel)
def pv761611 : PrimeValue := ⟨761611, pr761611⟩
private theorem pr761681 : Nat.Prime 761681 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv9521]) (by decide +kernel)
def pv761681 : PrimeValue := ⟨761681, pr761681⟩
private theorem pr761777 : Nat.Prime 761777 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv47,pv1013]) (by decide +kernel)
def pv761777 : PrimeValue := ⟨761777, pr761777⟩
private theorem pr761807 : Nat.Prime 761807 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv23,pv16561]) (by decide +kernel)
def pv761807 : PrimeValue := ⟨761807, pr761807⟩
private theorem pr762121 : Nat.Prime 762121 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv29,pv73]) (by decide +kernel)
def pv762121 : PrimeValue := ⟨762121, pr762121⟩
private theorem pr762187 : Nat.Prime 762187 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv127031]) (by decide +kernel)
def pv762187 : PrimeValue := ⟨762187, pr762187⟩
private theorem pr762227 : Nat.Prime 762227 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv97,pv3929]) (by decide +kernel)
def pv762227 : PrimeValue := ⟨762227, pr762227⟩
private theorem pr762253 : Nat.Prime 762253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv63521]) (by decide +kernel)
def pv762253 : PrimeValue := ⟨762253, pr762253⟩
private theorem pr762373 : Nat.Prime 762373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv181]) (by decide +kernel)
def pv762373 : PrimeValue := ⟨762373, pr762373⟩
private theorem pr762401 : Nat.Prime 762401 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv953]) (by decide +kernel)
def pv762401 : PrimeValue := ⟨762401, pr762401⟩
private theorem pr762407 : Nat.Prime 762407 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv103,pv3701]) (by decide +kernel)
def pv762407 : PrimeValue := ⟨762407, pr762407⟩
private theorem pr762547 : Nat.Prime 762547 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv6689]) (by decide +kernel)
def pv762547 : PrimeValue := ⟨762547, pr762547⟩
private theorem pr762563 : Nat.Prime 762563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv8867]) (by decide +kernel)
def pv762563 : PrimeValue := ⟨762563, pr762563⟩
private theorem pr762737 : Nat.Prime 762737 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv19,pv193]) (by decide +kernel)
def pv762737 : PrimeValue := ⟨762737, pr762737⟩
private theorem pr762743 : Nat.Prime 762743 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv381371]) (by decide +kernel)
def pv762743 : PrimeValue := ⟨762743, pr762743⟩
private theorem pr762823 : Nat.Prime 762823 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv42379]) (by decide +kernel)
def pv762823 : PrimeValue := ⟨762823, pr762823⟩
private theorem pr763027 : Nat.Prime 763027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv1051]) (by decide +kernel)
def pv763027 : PrimeValue := ⟨763027, pr763027⟩
private theorem pr763031 : Nat.Prime 763031 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv76303]) (by decide +kernel)
def pv763031 : PrimeValue := ⟨763031, pr763031⟩
private theorem pr763073 : Nat.Prime 763073 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11923]) (by decide +kernel)
def pv763073 : PrimeValue := ⟨763073, pr763073⟩
private theorem pr763111 : Nat.Prime 763111 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv61,pv139]) (by decide +kernel)
def pv763111 : PrimeValue := ⟨763111, pr763111⟩
private theorem pr763223 : Nat.Prime 763223 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv29,pv13159]) (by decide +kernel)
def pv763223 : PrimeValue := ⟨763223, pr763223⟩
private theorem pr763261 : Nat.Prime 763261 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv12721]) (by decide +kernel)
def pv763261 : PrimeValue := ⟨763261, pr763261⟩
private theorem pr763381 : Nat.Prime 763381 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv4241]) (by decide +kernel)
def pv763381 : PrimeValue := ⟨763381, pr763381⟩
private theorem pr763457 : Nat.Prime 763457 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv79,pv151]) (by decide +kernel)
def pv763457 : PrimeValue := ⟨763457, pr763457⟩
private theorem pr763493 : Nat.Prime 763493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv163,pv1171]) (by decide +kernel)
def pv763493 : PrimeValue := ⟨763493, pr763493⟩
private theorem pr763513 : Nat.Prime 763513 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29,pv1097]) (by decide +kernel)
def pv763513 : PrimeValue := ⟨763513, pr763513⟩
private theorem pr763621 : Nat.Prime 763621 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv13,pv89]) (by decide +kernel)
def pv763621 : PrimeValue := ⟨763621, pr763621⟩
private theorem pr763787 : Nat.Prime 763787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv521,pv733]) (by decide +kernel)
def pv763787 : PrimeValue := ⟨763787, pr763787⟩
private theorem pr763801 : Nat.Prime 763801 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv19,pv67]) (by decide +kernel)
def pv763801 : PrimeValue := ⟨763801, pr763801⟩
private theorem pr763927 : Nat.Prime 763927 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv127321]) (by decide +kernel)
def pv763927 : PrimeValue := ⟨763927, pr763927⟩
private theorem pr764041 : Nat.Prime 764041 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv6367]) (by decide +kernel)
def pv764041 : PrimeValue := ⟨764041, pr764041⟩
private theorem pr764081 : Nat.Prime 764081 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv9551]) (by decide +kernel)
def pv764081 : PrimeValue := ⟨764081, pr764081⟩
private theorem pr764131 : Nat.Prime 764131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv25471]) (by decide +kernel)
def pv764131 : PrimeValue := ⟨764131, pr764131⟩
private theorem pr764143 : Nat.Prime 764143 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv6703]) (by decide +kernel)
def pv764143 : PrimeValue := ⟨764143, pr764143⟩
private theorem pr764381 : Nat.Prime 764381 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv38219]) (by decide +kernel)
def pv764381 : PrimeValue := ⟨764381, pr764381⟩
private theorem pr764431 : Nat.Prime 764431 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv83,pv307]) (by decide +kernel)
def pv764431 : PrimeValue := ⟨764431, pr764431⟩
private theorem pr764501 : Nat.Prime 764501 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv11,pv139]) (by decide +kernel)
def pv764501 : PrimeValue := ⟨764501, pr764501⟩
private theorem pr764593 : Nat.Prime 764593 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv937]) (by decide +kernel)
def pv764593 : PrimeValue := ⟨764593, pr764593⟩
private theorem pr764627 : Nat.Prime 764627 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv43,pv523]) (by decide +kernel)
def pv764627 : PrimeValue := ⟨764627, pr764627⟩
private theorem pr764683 : Nat.Prime 764683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv127447]) (by decide +kernel)
def pv764683 : PrimeValue := ⟨764683, pr764683⟩
private theorem pr764893 : Nat.Prime 764893 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv21247]) (by decide +kernel)
def pv764893 : PrimeValue := ⟨764893, pr764893⟩
private theorem pr765007 : Nat.Prime 765007 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv67,pv173]) (by decide +kernel)
def pv765007 : PrimeValue := ⟨765007, pr765007⟩
private theorem pr765047 : Nat.Prime 765047 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv179,pv2137]) (by decide +kernel)
def pv765047 : PrimeValue := ⟨765047, pr765047⟩
private theorem pr765097 : Nat.Prime 765097 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv71,pv449]) (by decide +kernel)
def pv765097 : PrimeValue := ⟨765097, pr765097⟩
private theorem pr765211 : Nat.Prime 765211 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv23,pv1109]) (by decide +kernel)
def pv765211 : PrimeValue := ⟨765211, pr765211⟩
private theorem pr765251 : Nat.Prime 765251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv3061]) (by decide +kernel)
def pv765251 : PrimeValue := ⟨765251, pr765251⟩
private theorem pr765287 : Nat.Prime 765287 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv382643]) (by decide +kernel)
def pv765287 : PrimeValue := ⟨765287, pr765287⟩
private theorem pr765467 : Nat.Prime 765467 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv59,pv499]) (by decide +kernel)
def pv765467 : PrimeValue := ⟨765467, pr765467⟩
private theorem pr765497 : Nat.Prime 765497 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv103,pv929]) (by decide +kernel)
def pv765497 : PrimeValue := ⟨765497, pr765497⟩
private theorem pr765613 : Nat.Prime 765613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv139]) (by decide +kernel)
def pv765613 : PrimeValue := ⟨765613, pr765613⟩
private theorem pr765823 : Nat.Prime 765823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv127637]) (by decide +kernel)
def pv765823 : PrimeValue := ⟨765823, pr765823⟩
private theorem pr765971 : Nat.Prime 765971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv76597]) (by decide +kernel)
def pv765971 : PrimeValue := ⟨765971, pr765971⟩
private theorem pr765991 : Nat.Prime 765991 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv2837]) (by decide +kernel)
def pv765991 : PrimeValue := ⟨765991, pr765991⟩
private theorem pr766177 : Nat.Prime 766177 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv23,pv347]) (by decide +kernel)
def pv766177 : PrimeValue := ⟨766177, pr766177⟩
private theorem pr766321 : Nat.Prime 766321 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv31,pv103]) (by decide +kernel)
def pv766321 : PrimeValue := ⟨766321, pr766321⟩
private theorem pr766373 : Nat.Prime 766373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv4673]) (by decide +kernel)
def pv766373 : PrimeValue := ⟨766373, pr766373⟩
private theorem pr766393 : Nat.Prime 766393 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv2903]) (by decide +kernel)
def pv766393 : PrimeValue := ⟨766393, pr766393⟩
private theorem pr766457 : Nat.Prime 766457 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv149,pv643]) (by decide +kernel)
def pv766457 : PrimeValue := ⟨766457, pr766457⟩
private theorem pr766861 : Nat.Prime 766861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv12781]) (by decide +kernel)
def pv766861 : PrimeValue := ⟨766861, pr766861⟩
private theorem pr766873 : Nat.Prime 766873 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv10651]) (by decide +kernel)
def pv766873 : PrimeValue := ⟨766873, pr766873⟩
private theorem pr767287 : Nat.Prime 767287 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv1093]) (by decide +kernel)
def pv767287 : PrimeValue := ⟨767287, pr767287⟩
private theorem pr767357 : Nat.Prime 767357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv4679]) (by decide +kernel)
def pv767357 : PrimeValue := ⟨767357, pr767357⟩
private theorem pr767443 : Nat.Prime 767443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv9839]) (by decide +kernel)
def pv767443 : PrimeValue := ⟨767443, pr767443⟩
private theorem pr767783 : Nat.Prime 767783 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv383891]) (by decide +kernel)
def pv767783 : PrimeValue := ⟨767783, pr767783⟩
private theorem pr767827 : Nat.Prime 767827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv59,pv241]) (by decide +kernel)
def pv767827 : PrimeValue := ⟨767827, pr767827⟩
private theorem pr767843 : Nat.Prime 767843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv127,pv3023]) (by decide +kernel)
def pv767843 : PrimeValue := ⟨767843, pr767843⟩
private theorem pr768101 : Nat.Prime 768101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7681]) (by decide +kernel)
def pv768101 : PrimeValue := ⟨768101, pr768101⟩
private theorem pr768221 : Nat.Prime 768221 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv71,pv541]) (by decide +kernel)
def pv768221 : PrimeValue := ⟨768221, pr768221⟩
private theorem pr768241 : Nat.Prime 768241 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv97]) (by decide +kernel)
def pv768241 : PrimeValue := ⟨768241, pr768241⟩
private theorem pr768457 : Nat.Prime 768457 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv821]) (by decide +kernel)
def pv768457 : PrimeValue := ⟨768457, pr768457⟩
private theorem pr768631 : Nat.Prime 768631 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv25621]) (by decide +kernel)
def pv768631 : PrimeValue := ⟨768631, pr768631⟩
private theorem pr768641 : Nat.Prime 768641 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv1201]) (by decide +kernel)
def pv768641 : PrimeValue := ⟨768641, pr768641⟩
private theorem pr768773 : Nat.Prime 768773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv192193]) (by decide +kernel)
def pv768773 : PrimeValue := ⟨768773, pr768773⟩
private theorem pr768787 : Nat.Prime 768787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv3463]) (by decide +kernel)
def pv768787 : PrimeValue := ⟨768787, pr768787⟩
private theorem pr769073 : Nat.Prime 769073 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv71,pv677]) (by decide +kernel)
def pv769073 : PrimeValue := ⟨769073, pr769073⟩
private theorem pr769081 : Nat.Prime 769081 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv13,pv17,pv29]) (by decide +kernel)
def pv769081 : PrimeValue := ⟨769081, pr769081⟩
private theorem pr769297 : Nat.Prime 769297 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv11,pv31,pv47]) (by decide +kernel)
def pv769297 : PrimeValue := ⟨769297, pr769297⟩
private theorem pr769463 : Nat.Prime 769463 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv20249]) (by decide +kernel)
def pv769463 : PrimeValue := ⟨769463, pr769463⟩
private theorem pr769543 : Nat.Prime 769543 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv128257]) (by decide +kernel)
def pv769543 : PrimeValue := ⟨769543, pr769543⟩
private theorem pr769577 : Nat.Prime 769577 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv61,pv83]) (by decide +kernel)
def pv769577 : PrimeValue := ⟨769577, pr769577⟩
private theorem pr769661 : Nat.Prime 769661 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv29,pv1327]) (by decide +kernel)
def pv769661 : PrimeValue := ⟨769661, pr769661⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
