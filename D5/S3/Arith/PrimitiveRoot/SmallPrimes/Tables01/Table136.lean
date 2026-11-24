/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table136
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table136.pv934319
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table026
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table027
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table035
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table036
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table107
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table108

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr934319 : Nat.Prime 934319 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv7,pv11,pv6067]) (by decide +kernel)
def pv934319 : PrimeValue := ⟨934319, pr934319⟩
private theorem pr934343 : Nat.Prime 934343 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv467171]) (by decide +kernel)
def pv934343 : PrimeValue := ⟨934343, pr934343⟩
private theorem pr934403 : Nat.Prime 934403 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv31,pv2153]) (by decide +kernel)
def pv934403 : PrimeValue := ⟨934403, pr934403⟩
private theorem pr934613 : Nat.Prime 934613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv29,pv1151]) (by decide +kernel)
def pv934613 : PrimeValue := ⟨934613, pr934613⟩
private theorem pr934721 : Nat.Prime 934721 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv23,pv127]) (by decide +kernel)
def pv934721 : PrimeValue := ⟨934721, pr934721⟩
private theorem pr934919 : Nat.Prime 934919 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv67,pv6977]) (by decide +kernel)
def pv934919 : PrimeValue := ⟨934919, pr934919⟩
private theorem pr935201 : Nat.Prime 935201 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv7,pv167]) (by decide +kernel)
def pv935201 : PrimeValue := ⟨935201, pr935201⟩
private theorem pr935393 : Nat.Prime 935393 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29231]) (by decide +kernel)
def pv935393 : PrimeValue := ⟨935393, pr935393⟩
private theorem pr935591 : Nat.Prime 935591 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv93559]) (by decide +kernel)
def pv935591 : PrimeValue := ⟨935591, pr935591⟩
private theorem pr935639 : Nat.Prime 935639 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv11,pv71,pv599]) (by decide +kernel)
def pv935639 : PrimeValue := ⟨935639, pr935639⟩
private theorem pr935771 : Nat.Prime 935771 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv47,pv181]) (by decide +kernel)
def pv935771 : PrimeValue := ⟨935771, pr935771⟩
private theorem pr935813 : Nat.Prime 935813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv179,pv1307]) (by decide +kernel)
def pv935813 : PrimeValue := ⟨935813, pr935813⟩
private theorem pr936119 : Nat.Prime 936119 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv468059]) (by decide +kernel)
def pv936119 : PrimeValue := ⟨936119, pr936119⟩
private theorem pr936161 : Nat.Prime 936161 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv5851]) (by decide +kernel)
def pv936161 : PrimeValue := ⟨936161, pr936161⟩
private theorem pr936311 : Nat.Prime 936311 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv109,pv859]) (by decide +kernel)
def pv936311 : PrimeValue := ⟨936311, pr936311⟩
private theorem pr937049 : Nat.Prime 937049 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv29,pv577]) (by decide +kernel)
def pv937049 : PrimeValue := ⟨937049, pr937049⟩
private theorem pr937151 : Nat.Prime 937151 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv18743]) (by decide +kernel)
def pv937151 : PrimeValue := ⟨937151, pr937151⟩
private theorem pr937379 : Nat.Prime 937379 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv31,pv1163]) (by decide +kernel)
def pv937379 : PrimeValue := ⟨937379, pr937379⟩
private theorem pr937571 : Nat.Prime 937571 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv29,pv53,pv61]) (by decide +kernel)
def pv937571 : PrimeValue := ⟨937571, pr937571⟩
private theorem pr937589 : Nat.Prime 937589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv5717]) (by decide +kernel)
def pv937589 : PrimeValue := ⟨937589, pr937589⟩
private theorem pr937841 : Nat.Prime 937841 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv19,pv617]) (by decide +kernel)
def pv937841 : PrimeValue := ⟨937841, pr937841⟩
private theorem pr937901 : Nat.Prime 937901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv83,pv113]) (by decide +kernel)
def pv937901 : PrimeValue := ⟨937901, pr937901⟩
private theorem pr937991 : Nat.Prime 937991 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv97,pv967]) (by decide +kernel)
def pv937991 : PrimeValue := ⟨937991, pr937991⟩
private theorem pr938183 : Nat.Prime 938183 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv19,pv3527]) (by decide +kernel)
def pv938183 : PrimeValue := ⟨938183, pr938183⟩
private theorem pr938279 : Nat.Prime 938279 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv11,pv42649]) (by decide +kernel)
def pv938279 : PrimeValue := ⟨938279, pr938279⟩
private theorem pr938351 : Nat.Prime 938351 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv383]) (by decide +kernel)
def pv938351 : PrimeValue := ⟨938351, pr938351⟩
private theorem pr938573 : Nat.Prime 938573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv59,pv97]) (by decide +kernel)
def pv938573 : PrimeValue := ⟨938573, pr938573⟩
private theorem pr938681 : Nat.Prime 938681 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv31,pv757]) (by decide +kernel)
def pv938681 : PrimeValue := ⟨938681, pr938681⟩
private theorem pr939413 : Nat.Prime 939413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv10211]) (by decide +kernel)
def pv939413 : PrimeValue := ⟨939413, pr939413⟩
private theorem pr939443 : Nat.Prime 939443 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv67103]) (by decide +kernel)
def pv939443 : PrimeValue := ⟨939443, pr939443⟩
private theorem pr939551 : Nat.Prime 939551 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv19,pv23,pv43]) (by decide +kernel)
def pv939551 : PrimeValue := ⟨939551, pr939551⟩
private theorem pr939923 : Nat.Prime 939923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv233,pv2017]) (by decide +kernel)
def pv939923 : PrimeValue := ⟨939923, pr939923⟩
private theorem pr940169 : Nat.Prime 940169 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv31,pv223]) (by decide +kernel)
def pv940169 : PrimeValue := ⟨940169, pr940169⟩
private theorem pr940301 : Nat.Prime 940301 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv9403]) (by decide +kernel)
def pv940301 : PrimeValue := ⟨940301, pr940301⟩
private theorem pr940403 : Nat.Prime 940403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv470201]) (by decide +kernel)
def pv940403 : PrimeValue := ⟨940403, pr940403⟩
private theorem pr940421 : Nat.Prime 940421 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv3617]) (by decide +kernel)
def pv940421 : PrimeValue := ⟨940421, pr940421⟩
private theorem pr940469 : Nat.Prime 940469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv235117]) (by decide +kernel)
def pv940469 : PrimeValue := ⟨940469, pr940469⟩
private theorem pr940739 : Nat.Prime 940739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv647,pv727]) (by decide +kernel)
def pv940739 : PrimeValue := ⟨940739, pr940739⟩
private theorem pr940931 : Nat.Prime 940931 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv23,pv4091]) (by decide +kernel)
def pv940931 : PrimeValue := ⟨940931, pr940931⟩
private theorem pr940949 : Nat.Prime 940949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv67,pv3511]) (by decide +kernel)
def pv940949 : PrimeValue := ⟨940949, pr940949⟩
private theorem pr941123 : Nat.Prime 941123 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv13,pv5171]) (by decide +kernel)
def pv941123 : PrimeValue := ⟨941123, pr941123⟩
private theorem pr941159 : Nat.Prime 941159 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv470579]) (by decide +kernel)
def pv941159 : PrimeValue := ⟨941159, pr941159⟩
private theorem pr941201 : Nat.Prime 941201 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv181]) (by decide +kernel)
def pv941201 : PrimeValue := ⟨941201, pr941201⟩
private theorem pr941351 : Nat.Prime 941351 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv67,pv281]) (by decide +kernel)
def pv941351 : PrimeValue := ⟨941351, pr941351⟩
private theorem pr941513 : Nat.Prime 941513 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv13,pv823]) (by decide +kernel)
def pv941513 : PrimeValue := ⟨941513, pr941513⟩
private theorem pr941813 : Nat.Prime 941813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv173,pv1361]) (by decide +kernel)
def pv941813 : PrimeValue := ⟨941813, pr941813⟩
private theorem pr941879 : Nat.Prime 941879 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv1373]) (by decide +kernel)
def pv941879 : PrimeValue := ⟨941879, pr941879⟩
private theorem pr942041 : Nat.Prime 942041 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv2141]) (by decide +kernel)
def pv942041 : PrimeValue := ⟨942041, pr942041⟩
private theorem pr942113 : Nat.Prime 942113 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv59,pv499]) (by decide +kernel)
def pv942113 : PrimeValue := ⟨942113, pr942113⟩
private theorem pr942269 : Nat.Prime 942269 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv8123]) (by decide +kernel)
def pv942269 : PrimeValue := ⟨942269, pr942269⟩
private theorem pr942401 : Nat.Prime 942401 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv19,pv31]) (by decide +kernel)
def pv942401 : PrimeValue := ⟨942401, pr942401⟩
private theorem pr942521 : Nat.Prime 942521 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv23563]) (by decide +kernel)
def pv942521 : PrimeValue := ⟨942521, pr942521⟩
private theorem pr942653 : Nat.Prime 942653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv235663]) (by decide +kernel)
def pv942653 : PrimeValue := ⟨942653, pr942653⟩
private theorem pr942719 : Nat.Prime 942719 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv17,pv233]) (by decide +kernel)
def pv942719 : PrimeValue := ⟨942719, pr942719⟩
private theorem pr943139 : Nat.Prime 943139 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv23,pv29,pv101]) (by decide +kernel)
def pv943139 : PrimeValue := ⟨943139, pr943139⟩
private theorem pr943499 : Nat.Prime 943499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv471749]) (by decide +kernel)
def pv943499 : PrimeValue := ⟨943499, pr943499⟩
private theorem pr943571 : Nat.Prime 943571 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv157,pv601]) (by decide +kernel)
def pv943571 : PrimeValue := ⟨943571, pr943571⟩
private theorem pr943769 : Nat.Prime 943769 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv19,pv887]) (by decide +kernel)
def pv943769 : PrimeValue := ⟨943769, pr943769⟩
private theorem pr943781 : Nat.Prime 943781 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv47189]) (by decide +kernel)
def pv943781 : PrimeValue := ⟨943781, pr943781⟩
private theorem pr944039 : Nat.Prime 944039 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv472019]) (by decide +kernel)
def pv944039 : PrimeValue := ⟨944039, pr944039⟩
private theorem pr944123 : Nat.Prime 944123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv547,pv863]) (by decide +kernel)
def pv944123 : PrimeValue := ⟨944123, pr944123⟩
private theorem pr944453 : Nat.Prime 944453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv19,pv43]) (by decide +kernel)
def pv944453 : PrimeValue := ⟨944453, pr944453⟩
private theorem pr944519 : Nat.Prime 944519 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv23,pv20533]) (by decide +kernel)
def pv944519 : PrimeValue := ⟨944519, pr944519⟩
private theorem pr944543 : Nat.Prime 944543 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv193,pv2447]) (by decide +kernel)
def pv944543 : PrimeValue := ⟨944543, pr944543⟩
private theorem pr944609 : Nat.Prime 944609 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv4217]) (by decide +kernel)
def pv944609 : PrimeValue := ⟨944609, pr944609⟩
private theorem pr944711 : Nat.Prime 944711 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv13,pv43]) (by decide +kernel)
def pv944711 : PrimeValue := ⟨944711, pr944711⟩
private theorem pr944873 : Nat.Prime 944873 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv83,pv1423]) (by decide +kernel)
def pv944873 : PrimeValue := ⟨944873, pr944873⟩
private theorem pr945233 : Nat.Prime 945233 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv59077]) (by decide +kernel)
def pv945233 : PrimeValue := ⟨945233, pr945233⟩
private theorem pr945359 : Nat.Prime 945359 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv47,pv89,pv113]) (by decide +kernel)
def pv945359 : PrimeValue := ⟨945359, pr945359⟩
private theorem pr945809 : Nat.Prime 945809 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv59113]) (by decide +kernel)
def pv945809 : PrimeValue := ⟨945809, pr945809⟩
private theorem pr945929 : Nat.Prime 945929 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv317,pv373]) (by decide +kernel)
def pv945929 : PrimeValue := ⟨945929, pr945929⟩
private theorem pr946091 : Nat.Prime 946091 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv37,pv2557]) (by decide +kernel)
def pv946091 : PrimeValue := ⟨946091, pr946091⟩
private theorem pr946331 : Nat.Prime 946331 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv11,pv1229]) (by decide +kernel)
def pv946331 : PrimeValue := ⟨946331, pr946331⟩
private theorem pr946391 : Nat.Prime 946391 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv17,pv19,pv293]) (by decide +kernel)
def pv946391 : PrimeValue := ⟨946391, pr946391⟩
private theorem pr946733 : Nat.Prime 946733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv12457]) (by decide +kernel)
def pv946733 : PrimeValue := ⟨946733, pr946733⟩
private theorem pr946769 : Nat.Prime 946769 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv47,pv1259]) (by decide +kernel)
def pv946769 : PrimeValue := ⟨946769, pr946769⟩
private theorem pr946853 : Nat.Prime 946853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv236713]) (by decide +kernel)
def pv946853 : PrimeValue := ⟨946853, pr946853⟩
private theorem pr946859 : Nat.Prime 946859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv193,pv223]) (by decide +kernel)
def pv946859 : PrimeValue := ⟨946859, pr946859⟩
private theorem pr946943 : Nat.Prime 946943 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv473471]) (by decide +kernel)
def pv946943 : PrimeValue := ⟨946943, pr946943⟩
private theorem pr947603 : Nat.Prime 947603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv229,pv2069]) (by decide +kernel)
def pv947603 : PrimeValue := ⟨947603, pr947603⟩
private theorem pr947753 : Nat.Prime 947753 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv701]) (by decide +kernel)
def pv947753 : PrimeValue := ⟨947753, pr947753⟩
private theorem pr947783 : Nat.Prime 947783 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv67,pv643]) (by decide +kernel)
def pv947783 : PrimeValue := ⟨947783, pr947783⟩
private theorem pr948263 : Nat.Prime 948263 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv67733]) (by decide +kernel)
def pv948263 : PrimeValue := ⟨948263, pr948263⟩
private theorem pr948281 : Nat.Prime 948281 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv151,pv157]) (by decide +kernel)
def pv948281 : PrimeValue := ⟨948281, pr948281⟩
private theorem pr948443 : Nat.Prime 948443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv19,pv2269]) (by decide +kernel)
def pv948443 : PrimeValue := ⟨948443, pr948443⟩
private theorem pr948449 : Nat.Prime 948449 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv107,pv277]) (by decide +kernel)
def pv948449 : PrimeValue := ⟨948449, pr948449⟩
private theorem pr948581 : Nat.Prime 948581 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv43,pv1103]) (by decide +kernel)
def pv948581 : PrimeValue := ⟨948581, pr948581⟩
private theorem pr948971 : Nat.Prime 948971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv8627]) (by decide +kernel)
def pv948971 : PrimeValue := ⟨948971, pr948971⟩
private theorem pr948989 : Nat.Prime 948989 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv67,pv3541]) (by decide +kernel)
def pv948989 : PrimeValue := ⟨948989, pr948989⟩
private theorem pr949043 : Nat.Prime 949043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv103,pv271]) (by decide +kernel)
def pv949043 : PrimeValue := ⟨949043, pr949043⟩
private theorem pr949121 : Nat.Prime 949121 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv1483]) (by decide +kernel)
def pv949121 : PrimeValue := ⟨949121, pr949121⟩
private theorem pr949241 : Nat.Prime 949241 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv19,pv1249]) (by decide +kernel)
def pv949241 : PrimeValue := ⟨949241, pr949241⟩
private theorem pr949391 : Nat.Prime 949391 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv67,pv109]) (by decide +kernel)
def pv949391 : PrimeValue := ⟨949391, pr949391⟩
private theorem pr949523 : Nat.Prime 949523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv9689]) (by decide +kernel)
def pv949523 : PrimeValue := ⟨949523, pr949523⟩
private theorem pr949583 : Nat.Prime 949583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv24989]) (by decide +kernel)
def pv949583 : PrimeValue := ⟨949583, pr949583⟩
private theorem pr949631 : Nat.Prime 949631 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv89,pv97]) (by decide +kernel)
def pv949631 : PrimeValue := ⟨949631, pr949631⟩
private theorem pr949673 : Nat.Prime 949673 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv118709]) (by decide +kernel)
def pv949673 : PrimeValue := ⟨949673, pr949673⟩
private theorem pr949853 : Nat.Prime 949853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv83,pv2861]) (by decide +kernel)
def pv949853 : PrimeValue := ⟨949853, pr949853⟩
private theorem pr949961 : Nat.Prime 949961 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv17,pv127]) (by decide +kernel)
def pv949961 : PrimeValue := ⟨949961, pr949961⟩
private theorem pr950039 : Nat.Prime 950039 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv19,pv23,pv1087]) (by decide +kernel)
def pv950039 : PrimeValue := ⟨950039, pr950039⟩
private theorem pr950231 : Nat.Prime 950231 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv167,pv569]) (by decide +kernel)
def pv950231 : PrimeValue := ⟨950231, pr950231⟩
private theorem pr950333 : Nat.Prime 950333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv193,pv1231]) (by decide +kernel)
def pv950333 : PrimeValue := ⟨950333, pr950333⟩
private theorem pr950633 : Nat.Prime 950633 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv331,pv359]) (by decide +kernel)
def pv950633 : PrimeValue := ⟨950633, pr950633⟩
private theorem pr950681 : Nat.Prime 950681 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv23767]) (by decide +kernel)
def pv950681 : PrimeValue := ⟨950681, pr950681⟩
private theorem pr950753 : Nat.Prime 950753 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv37,pv73]) (by decide +kernel)
def pv950753 : PrimeValue := ⟨950753, pr950753⟩
private theorem pr950783 : Nat.Prime 950783 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv113,pv601]) (by decide +kernel)
def pv950783 : PrimeValue := ⟨950783, pr950783⟩
private theorem pr950819 : Nat.Prime 950819 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv3929]) (by decide +kernel)
def pv950819 : PrimeValue := ⟨950819, pr950819⟩
private theorem pr950879 : Nat.Prime 950879 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv17,pv27967]) (by decide +kernel)
def pv950879 : PrimeValue := ⟨950879, pr950879⟩
private theorem pr950993 : Nat.Prime 950993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv1213]) (by decide +kernel)
def pv950993 : PrimeValue := ⟨950993, pr950993⟩
private theorem pr951053 : Nat.Prime 951053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv237763]) (by decide +kernel)
def pv951053 : PrimeValue := ⟨951053, pr951053⟩
private theorem pr951059 : Nat.Prime 951059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv475529]) (by decide +kernel)
def pv951059 : PrimeValue := ⟨951059, pr951059⟩
private theorem pr951101 : Nat.Prime 951101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv9511]) (by decide +kernel)
def pv951101 : PrimeValue := ⟨951101, pr951101⟩
private theorem pr951389 : Nat.Prime 951389 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv823]) (by decide +kernel)
def pv951389 : PrimeValue := ⟨951389, pr951389⟩
private theorem pr951449 : Nat.Prime 951449 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv118931]) (by decide +kernel)
def pv951449 : PrimeValue := ⟨951449, pr951449⟩
private theorem pr951623 : Nat.Prime 951623 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv101,pv673]) (by decide +kernel)
def pv951623 : PrimeValue := ⟨951623, pr951623⟩
private theorem pr951689 : Nat.Prime 951689 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv337,pv353]) (by decide +kernel)
def pv951689 : PrimeValue := ⟨951689, pr951689⟩
private theorem pr951851 : Nat.Prime 951851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19037]) (by decide +kernel)
def pv951851 : PrimeValue := ⟨951851, pr951851⟩
private theorem pr951893 : Nat.Prime 951893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv237973]) (by decide +kernel)
def pv951893 : PrimeValue := ⟨951893, pr951893⟩
private theorem pr952439 : Nat.Prime 952439 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv476219]) (by decide +kernel)
def pv952439 : PrimeValue := ⟨952439, pr952439⟩
private theorem pr952481 : Nat.Prime 952481 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv5953]) (by decide +kernel)
def pv952481 : PrimeValue := ⟨952481, pr952481⟩
private theorem pr952691 : Nat.Prime 952691 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv47,pv2027]) (by decide +kernel)
def pv952691 : PrimeValue := ⟨952691, pr952691⟩
private theorem pr952883 : Nat.Prime 952883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv29,pv2347]) (by decide +kernel)
def pv952883 : PrimeValue := ⟨952883, pr952883⟩
private theorem pr953093 : Nat.Prime 953093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv34039]) (by decide +kernel)
def pv953093 : PrimeValue := ⟨953093, pr953093⟩
private theorem pr953171 : Nat.Prime 953171 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv95317]) (by decide +kernel)
def pv953171 : PrimeValue := ⟨953171, pr953171⟩
private theorem pr953261 : Nat.Prime 953261 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv619]) (by decide +kernel)
def pv953261 : PrimeValue := ⟨953261, pr953261⟩
private theorem pr953321 : Nat.Prime 953321 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv23833]) (by decide +kernel)
def pv953321 : PrimeValue := ⟨953321, pr953321⟩
private theorem pr953651 : Nat.Prime 953651 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19073]) (by decide +kernel)
def pv953651 : PrimeValue := ⟨953651, pr953651⟩
private theorem pr953873 : Nat.Prime 953873 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv59617]) (by decide +kernel)
def pv953873 : PrimeValue := ⟨953873, pr953873⟩
private theorem pr954203 : Nat.Prime 954203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv163,pv2927]) (by decide +kernel)
def pv954203 : PrimeValue := ⟨954203, pr954203⟩
private theorem pr954221 : Nat.Prime 954221 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv47711]) (by decide +kernel)
def pv954221 : PrimeValue := ⟨954221, pr954221⟩
private theorem pr954263 : Nat.Prime 954263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv477131]) (by decide +kernel)
def pv954263 : PrimeValue := ⟨954263, pr954263⟩
private theorem pr954461 : Nat.Prime 954461 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv3671]) (by decide +kernel)
def pv954461 : PrimeValue := ⟨954461, pr954461⟩
private theorem pr954539 : Nat.Prime 954539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv36713]) (by decide +kernel)
def pv954539 : PrimeValue := ⟨954539, pr954539⟩
private theorem pr954599 : Nat.Prime 954599 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv19,pv25121]) (by decide +kernel)
def pv954599 : PrimeValue := ⟨954599, pr954599⟩
private theorem pr954641 : Nat.Prime 954641 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv11933]) (by decide +kernel)
def pv954641 : PrimeValue := ⟨954641, pr954641⟩
private theorem pr954671 : Nat.Prime 954671 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv95467]) (by decide +kernel)
def pv954671 : PrimeValue := ⟨954671, pr954671⟩
private theorem pr954743 : Nat.Prime 954743 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv53,pv9007]) (by decide +kernel)
def pv954743 : PrimeValue := ⟨954743, pr954743⟩
private theorem pr954851 : Nat.Prime 954851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv113]) (by decide +kernel)
def pv954851 : PrimeValue := ⟨954851, pr954851⟩
private theorem pr955061 : Nat.Prime 955061 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv53]) (by decide +kernel)
def pv955061 : PrimeValue := ⟨955061, pr955061⟩
private theorem pr955211 : Nat.Prime 955211 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv59,pv1619]) (by decide +kernel)
def pv955211 : PrimeValue := ⟨955211, pr955211⟩
private theorem pr955379 : Nat.Prime 955379 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53,pv9013]) (by decide +kernel)
def pv955379 : PrimeValue := ⟨955379, pr955379⟩
private theorem pr955541 : Nat.Prime 955541 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv47777]) (by decide +kernel)
def pv955541 : PrimeValue := ⟨955541, pr955541⟩
private theorem pr955613 : Nat.Prime 955613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv34129]) (by decide +kernel)
def pv955613 : PrimeValue := ⟨955613, pr955613⟩
private theorem pr955919 : Nat.Prime 955919 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv59,pv8101]) (by decide +kernel)
def pv955919 : PrimeValue := ⟨955919, pr955919⟩
private theorem pr956723 : Nat.Prime 956723 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv31,pv1187]) (by decide +kernel)
def pv956723 : PrimeValue := ⟨956723, pr956723⟩
private theorem pr956843 : Nat.Prime 956843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv478421]) (by decide +kernel)
def pv956843 : PrimeValue := ⟨956843, pr956843⟩
private theorem pr956909 : Nat.Prime 956909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv7717]) (by decide +kernel)
def pv956909 : PrimeValue := ⟨956909, pr956909⟩
private theorem pr956951 : Nat.Prime 956951 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv19139]) (by decide +kernel)
def pv956951 : PrimeValue := ⟨956951, pr956951⟩
private theorem pr956999 : Nat.Prime 956999 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv17,pv4021]) (by decide +kernel)
def pv956999 : PrimeValue := ⟨956999, pr956999⟩
private theorem pr957119 : Nat.Prime 957119 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv373,pv1283]) (by decide +kernel)
def pv957119 : PrimeValue := ⟨957119, pr957119⟩
private theorem pr957161 : Nat.Prime 957161 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv23929]) (by decide +kernel)
def pv957161 : PrimeValue := ⟨957161, pr957161⟩
private theorem pr957221 : Nat.Prime 957221 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv19,pv229]) (by decide +kernel)
def pv957221 : PrimeValue := ⟨957221, pr957221⟩
private theorem pr957263 : Nat.Prime 957263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv478631]) (by decide +kernel)
def pv957263 : PrimeValue := ⟨957263, pr957263⟩
private theorem pr957611 : Nat.Prime 957611 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv43,pv131]) (by decide +kernel)
def pv957611 : PrimeValue := ⟨957611, pr957611⟩
private theorem pr957851 : Nat.Prime 957851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19157]) (by decide +kernel)
def pv957851 : PrimeValue := ⟨957851, pr957851⟩
private theorem pr957959 : Nat.Prime 957959 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv461,pv1039]) (by decide +kernel)
def pv957959 : PrimeValue := ⟨957959, pr957959⟩
private theorem pr958049 : Nat.Prime 958049 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv7,pv13,pv47]) (by decide +kernel)
def pv958049 : PrimeValue := ⟨958049, pr958049⟩
private theorem pr958343 : Nat.Prime 958343 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv11,pv127]) (by decide +kernel)
def pv958343 : PrimeValue := ⟨958343, pr958343⟩
private theorem pr958739 : Nat.Prime 958739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv43579]) (by decide +kernel)
def pv958739 : PrimeValue := ⟨958739, pr958739⟩
private theorem pr958829 : Nat.Prime 958829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv18439]) (by decide +kernel)
def pv958829 : PrimeValue := ⟨958829, pr958829⟩
private theorem pr958871 : Nat.Prime 958871 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv23,pv379]) (by decide +kernel)
def pv958871 : PrimeValue := ⟨958871, pr958871⟩
private theorem pr958883 : Nat.Prime 958883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv479441]) (by decide +kernel)
def pv958883 : PrimeValue := ⟨958883, pr958883⟩
private theorem pr959009 : Nat.Prime 959009 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv1303]) (by decide +kernel)
def pv959009 : PrimeValue := ⟨959009, pr959009⟩
private theorem pr959219 : Nat.Prime 959219 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv79,pv467]) (by decide +kernel)
def pv959219 : PrimeValue := ⟨959219, pr959219⟩
private theorem pr959333 : Nat.Prime 959333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv21803]) (by decide +kernel)
def pv959333 : PrimeValue := ⟨959333, pr959333⟩
private theorem pr959489 : Nat.Prime 959489 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv937]) (by decide +kernel)
def pv959489 : PrimeValue := ⟨959489, pr959489⟩
private theorem pr959561 : Nat.Prime 959561 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv23,pv149]) (by decide +kernel)
def pv959561 : PrimeValue := ⟨959561, pr959561⟩
private theorem pr959681 : Nat.Prime 959681 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv2999]) (by decide +kernel)
def pv959681 : PrimeValue := ⟨959681, pr959681⟩
private theorem pr959921 : Nat.Prime 959921 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv71]) (by decide +kernel)
def pv959921 : PrimeValue := ⟨959921, pr959921⟩
private theorem pr960119 : Nat.Prime 960119 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv480059]) (by decide +kernel)
def pv960119 : PrimeValue := ⟨960119, pr960119⟩
private theorem pr960191 : Nat.Prime 960191 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv11,pv29,pv43]) (by decide +kernel)
def pv960191 : PrimeValue := ⟨960191, pr960191⟩
private theorem pr960293 : Nat.Prime 960293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv240073]) (by decide +kernel)
def pv960293 : PrimeValue := ⟨960293, pr960293⟩
private theorem pr960299 : Nat.Prime 960299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv37,pv683]) (by decide +kernel)
def pv960299 : PrimeValue := ⟨960299, pr960299⟩
private theorem pr960341 : Nat.Prime 960341 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv48017]) (by decide +kernel)
def pv960341 : PrimeValue := ⟨960341, pr960341⟩
private theorem pr960419 : Nat.Prime 960419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv480209]) (by decide +kernel)
def pv960419 : PrimeValue := ⟨960419, pr960419⟩
private theorem pr960941 : Nat.Prime 960941 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23,pv2089]) (by decide +kernel)
def pv960941 : PrimeValue := ⟨960941, pr960941⟩
private theorem pr960983 : Nat.Prime 960983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv19]) (by decide +kernel)
def pv960983 : PrimeValue := ⟨960983, pr960983⟩
private theorem pr961073 : Nat.Prime 961073 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv8581]) (by decide +kernel)
def pv961073 : PrimeValue := ⟨961073, pr961073⟩
private theorem pr961283 : Nat.Prime 961283 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv17,pv577]) (by decide +kernel)
def pv961283 : PrimeValue := ⟨961283, pr961283⟩
private theorem pr961529 : Nat.Prime 961529 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv263,pv457]) (by decide +kernel)
def pv961529 : PrimeValue := ⟨961529, pr961529⟩
private theorem pr961601 : Nat.Prime 961601 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv601]) (by decide +kernel)
def pv961601 : PrimeValue := ⟨961601, pr961601⟩
private theorem pr961661 : Nat.Prime 961661 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv6869]) (by decide +kernel)
def pv961661 : PrimeValue := ⟨961661, pr961661⟩
private theorem pr961739 : Nat.Prime 961739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv53,pv211]) (by decide +kernel)
def pv961739 : PrimeValue := ⟨961739, pr961739⟩
private theorem pr961841 : Nat.Prime 961841 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv1093]) (by decide +kernel)
def pv961841 : PrimeValue := ⟨961841, pr961841⟩
private theorem pr961853 : Nat.Prime 961853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv67,pv97]) (by decide +kernel)
def pv961853 : PrimeValue := ⟨961853, pr961853⟩
private theorem pr961991 : Nat.Prime 961991 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv96199]) (by decide +kernel)
def pv961991 : PrimeValue := ⟨961991, pr961991⟩
private theorem pr962033 : Nat.Prime 962033 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv60127]) (by decide +kernel)
def pv962033 : PrimeValue := ⟨962033, pr962033⟩
private theorem pr962099 : Nat.Prime 962099 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv28297]) (by decide +kernel)
def pv962099 : PrimeValue := ⟨962099, pr962099⟩
private theorem pr962243 : Nat.Prime 962243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv149,pv3229]) (by decide +kernel)
def pv962243 : PrimeValue := ⟨962243, pr962243⟩
private theorem pr962309 : Nat.Prime 962309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv113,pv2129]) (by decide +kernel)
def pv962309 : PrimeValue := ⟨962309, pr962309⟩
private theorem pr962543 : Nat.Prime 962543 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv7,pv197,pv349]) (by decide +kernel)
def pv962543 : PrimeValue := ⟨962543, pr962543⟩
private theorem pr962609 : Nat.Prime 962609 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv3539]) (by decide +kernel)
def pv962609 : PrimeValue := ⟨962609, pr962609⟩
private theorem pr962789 : Nat.Prime 962789 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv313,pv769]) (by decide +kernel)
def pv962789 : PrimeValue := ⟨962789, pr962789⟩
private theorem pr963311 : Nat.Prime 963311 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv96331]) (by decide +kernel)
def pv963311 : PrimeValue := ⟨963311, pr963311⟩
private theorem pr963323 : Nat.Prime 963323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv29,pv977]) (by decide +kernel)
def pv963323 : PrimeValue := ⟨963323, pr963323⟩
private theorem pr963419 : Nat.Prime 963419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv41,pv379]) (by decide +kernel)
def pv963419 : PrimeValue := ⟨963419, pr963419⟩
private theorem pr963629 : Nat.Prime 963629 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv37,pv383]) (by decide +kernel)
def pv963629 : PrimeValue := ⟨963629, pr963629⟩
private theorem pr963659 : Nat.Prime 963659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv137,pv3517]) (by decide +kernel)
def pv963659 : PrimeValue := ⟨963659, pr963659⟩
private theorem pr963779 : Nat.Prime 963779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv109,pv4421]) (by decide +kernel)
def pv963779 : PrimeValue := ⟨963779, pr963779⟩
private theorem pr964049 : Nat.Prime 964049 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv89,pv677]) (by decide +kernel)
def pv964049 : PrimeValue := ⟨964049, pr964049⟩
private theorem pr964283 : Nat.Prime 964283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv53,pv827]) (by decide +kernel)
def pv964283 : PrimeValue := ⟨964283, pr964283⟩
private theorem pr964559 : Nat.Prime 964559 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv68897]) (by decide +kernel)
def pv964559 : PrimeValue := ⟨964559, pr964559⟩
private theorem pr964703 : Nat.Prime 964703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv482351]) (by decide +kernel)
def pv964703 : PrimeValue := ⟨964703, pr964703⟩
private theorem pr964823 : Nat.Prime 964823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv467,pv1033]) (by decide +kernel)
def pv964823 : PrimeValue := ⟨964823, pr964823⟩
private theorem pr964889 : Nat.Prime 964889 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv4159]) (by decide +kernel)
def pv964889 : PrimeValue := ⟨964889, pr964889⟩
private theorem pr964913 : Nat.Prime 964913 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv4639]) (by decide +kernel)
def pv964913 : PrimeValue := ⟨964913, pr964913⟩
private theorem pr964973 : Nat.Prime 964973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv12697]) (by decide +kernel)
def pv964973 : PrimeValue := ⟨964973, pr964973⟩
private theorem pr965291 : Nat.Prime 965291 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv83,pv1163]) (by decide +kernel)
def pv965291 : PrimeValue := ⟨965291, pr965291⟩
private theorem pr965411 : Nat.Prime 965411 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv29,pv3329]) (by decide +kernel)
def pv965411 : PrimeValue := ⟨965411, pr965411⟩
private theorem pr965759 : Nat.Prime 965759 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv29,pv16651]) (by decide +kernel)
def pv965759 : PrimeValue := ⟨965759, pr965759⟩
private theorem pr965963 : Nat.Prime 965963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv127,pv3803]) (by decide +kernel)
def pv965963 : PrimeValue := ⟨965963, pr965963⟩
private theorem pr966029 : Nat.Prime 966029 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv34501]) (by decide +kernel)
def pv966029 : PrimeValue := ⟨966029, pr966029⟩
private theorem pr966233 : Nat.Prime 966233 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv120779]) (by decide +kernel)
def pv966233 : PrimeValue := ⟨966233, pr966233⟩
private theorem pr966401 : Nat.Prime 966401 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv151]) (by decide +kernel)
def pv966401 : PrimeValue := ⟨966401, pr966401⟩
private theorem pr966419 : Nat.Prime 966419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv483209]) (by decide +kernel)
def pv966419 : PrimeValue := ⟨966419, pr966419⟩
private theorem pr966863 : Nat.Prime 966863 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv13,pv41,pv907]) (by decide +kernel)
def pv966863 : PrimeValue := ⟨966863, pr966863⟩
private theorem pr967049 : Nat.Prime 967049 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv109,pv1109]) (by decide +kernel)
def pv967049 : PrimeValue := ⟨967049, pr967049⟩
private theorem pr967139 : Nat.Prime 967139 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv19,pv31,pv821]) (by decide +kernel)
def pv967139 : PrimeValue := ⟨967139, pr967139⟩
private theorem pr967229 : Nat.Prime 967229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv241807]) (by decide +kernel)
def pv967229 : PrimeValue := ⟨967229, pr967229⟩
private theorem pr967259 : Nat.Prime 967259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv483629]) (by decide +kernel)
def pv967259 : PrimeValue := ⟨967259, pr967259⟩
private theorem pr967289 : Nat.Prime 967289 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv7,pv23,pv751]) (by decide +kernel)
def pv967289 : PrimeValue := ⟨967289, pr967289⟩
private theorem pr967493 : Nat.Prime 967493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv241873]) (by decide +kernel)
def pv967493 : PrimeValue := ⟨967493, pr967493⟩
private theorem pr967709 : Nat.Prime 967709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv17,pv19,pv107]) (by decide +kernel)
def pv967709 : PrimeValue := ⟨967709, pr967709⟩
private theorem pr967721 : Nat.Prime 967721 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv1861]) (by decide +kernel)
def pv967721 : PrimeValue := ⟨967721, pr967721⟩
private theorem pr968111 : Nat.Prime 968111 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv13,pv677]) (by decide +kernel)
def pv968111 : PrimeValue := ⟨968111, pr968111⟩
private theorem pr968213 : Nat.Prime 968213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv151,pv229]) (by decide +kernel)
def pv968213 : PrimeValue := ⟨968213, pr968213⟩
private theorem pr968273 : Nat.Prime 968273 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv73,pv829]) (by decide +kernel)
def pv968273 : PrimeValue := ⟨968273, pr968273⟩
private theorem pr968321 : Nat.Prime 968321 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv17,pv89]) (by decide +kernel)
def pv968321 : PrimeValue := ⟨968321, pr968321⟩
private theorem pr968501 : Nat.Prime 968501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv149]) (by decide +kernel)
def pv968501 : PrimeValue := ⟨968501, pr968501⟩
private theorem pr968729 : Nat.Prime 968729 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv419]) (by decide +kernel)
def pv968729 : PrimeValue := ⟨968729, pr968729⟩
private theorem pr968801 : Nat.Prime 968801 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv7,pv173]) (by decide +kernel)
def pv968801 : PrimeValue := ⟨968801, pr968801⟩
private theorem pr968879 : Nat.Prime 968879 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv484439]) (by decide +kernel)
def pv968879 : PrimeValue := ⟨968879, pr968879⟩
private theorem pr968939 : Nat.Prime 968939 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv269,pv1801]) (by decide +kernel)
def pv968939 : PrimeValue := ⟨968939, pr968939⟩
private theorem pr968963 : Nat.Prime 968963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv43,pv593]) (by decide +kernel)
def pv968963 : PrimeValue := ⟨968963, pr968963⟩
private theorem pr969113 : Nat.Prime 969113 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv121139]) (by decide +kernel)
def pv969113 : PrimeValue := ⟨969113, pr969113⟩
private theorem pr969179 : Nat.Prime 969179 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv37,pv1871]) (by decide +kernel)
def pv969179 : PrimeValue := ⟨969179, pr969179⟩
private theorem pr969359 : Nat.Prime 969359 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv13,pv23,pv1621]) (by decide +kernel)
def pv969359 : PrimeValue := ⟨969359, pr969359⟩
private theorem pr969431 : Nat.Prime 969431 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv11,pv1259]) (by decide +kernel)
def pv969431 : PrimeValue := ⟨969431, pr969431⟩
private theorem pr969443 : Nat.Prime 969443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv28513]) (by decide +kernel)
def pv969443 : PrimeValue := ⟨969443, pr969443⟩
private theorem pr969593 : Nat.Prime 969593 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv9323]) (by decide +kernel)
def pv969593 : PrimeValue := ⟨969593, pr969593⟩
private theorem pr969641 : Nat.Prime 969641 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv3463]) (by decide +kernel)
def pv969641 : PrimeValue := ⟨969641, pr969641⟩
private theorem pr969719 : Nat.Prime 969719 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv71,pv6829]) (by decide +kernel)
def pv969719 : PrimeValue := ⟨969719, pr969719⟩
private theorem pr969863 : Nat.Prime 969863 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv239,pv2029]) (by decide +kernel)
def pv969863 : PrimeValue := ⟨969863, pr969863⟩
private theorem pr970043 : Nat.Prime 970043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv485021]) (by decide +kernel)
def pv970043 : PrimeValue := ⟨970043, pr970043⟩
private theorem pr970061 : Nat.Prime 970061 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv13,pv41]) (by decide +kernel)
def pv970061 : PrimeValue := ⟨970061, pr970061⟩
private theorem pr970493 : Nat.Prime 970493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv331,pv733]) (by decide +kernel)
def pv970493 : PrimeValue := ⟨970493, pr970493⟩
private theorem pr970829 : Nat.Prime 970829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv163,pv1489]) (by decide +kernel)
def pv970829 : PrimeValue := ⟨970829, pr970829⟩
private theorem pr971153 : Nat.Prime 971153 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv13,pv23,pv29]) (by decide +kernel)
def pv971153 : PrimeValue := ⟨971153, pr971153⟩
private theorem pr971273 : Nat.Prime 971273 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv167,pv727]) (by decide +kernel)
def pv971273 : PrimeValue := ⟨971273, pr971273⟩
private theorem pr971381 : Nat.Prime 971381 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv2857]) (by decide +kernel)
def pv971381 : PrimeValue := ⟨971381, pr971381⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
