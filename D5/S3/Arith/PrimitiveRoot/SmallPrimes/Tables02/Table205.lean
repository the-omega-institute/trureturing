/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table205
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table205.pv675863
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table013
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table016
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table027
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table042
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table091
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table092

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr675863 : Nat.Prime 675863 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv31,pv991]) (by decide +kernel)
def pv675863 : PrimeValue := ⟨675863, pr675863⟩
private theorem pr675923 : Nat.Prime 675923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv25997]) (by decide +kernel)
def pv675923 : PrimeValue := ⟨675923, pr675923⟩
private theorem pr675973 : Nat.Prime 675973 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv569]) (by decide +kernel)
def pv675973 : PrimeValue := ⟨675973, pr675973⟩
private theorem pr676147 : Nat.Prime 676147 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv112691]) (by decide +kernel)
def pv676147 : PrimeValue := ⟨676147, pr676147⟩
private theorem pr676703 : Nat.Prime 676703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv17,pv1531]) (by decide +kernel)
def pv676703 : PrimeValue := ⟨676703, pr676703⟩
private theorem pr676763 : Nat.Prime 676763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv523,pv647]) (by decide +kernel)
def pv676763 : PrimeValue := ⟨676763, pr676763⟩
private theorem pr676891 : Nat.Prime 676891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv23,pv109]) (by decide +kernel)
def pv676891 : PrimeValue := ⟨676891, pr676891⟩
private theorem pr676961 : Nat.Prime 676961 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv4231]) (by decide +kernel)
def pv676961 : PrimeValue := ⟨676961, pr676961⟩
private theorem pr676967 : Nat.Prime 676967 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv59,pv5737]) (by decide +kernel)
def pv676967 : PrimeValue := ⟨676967, pr676967⟩
private theorem pr676981 : Nat.Prime 676981 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv3761]) (by decide +kernel)
def pv676981 : PrimeValue := ⟨676981, pr676981⟩
private theorem pr676987 : Nat.Prime 676987 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv112831]) (by decide +kernel)
def pv676987 : PrimeValue := ⟨676987, pr676987⟩
private theorem pr677177 : Nat.Prime 677177 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv47,pv1801]) (by decide +kernel)
def pv677177 : PrimeValue := ⟨677177, pr677177⟩
private theorem pr677227 : Nat.Prime 677227 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv31,pv331]) (by decide +kernel)
def pv677227 : PrimeValue := ⟨677227, pr677227⟩
private theorem pr677357 : Nat.Prime 677357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv169339]) (by decide +kernel)
def pv677357 : PrimeValue := ⟨677357, pr677357⟩
private theorem pr677371 : Nat.Prime 677371 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv67,pv337]) (by decide +kernel)
def pv677371 : PrimeValue := ⟨677371, pr677371⟩
private theorem pr677387 : Nat.Prime 677387 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv151,pv2243]) (by decide +kernel)
def pv677387 : PrimeValue := ⟨677387, pr677387⟩
private theorem pr677423 : Nat.Prime 677423 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv43,pv7877]) (by decide +kernel)
def pv677423 : PrimeValue := ⟨677423, pr677423⟩
private theorem pr677441 : Nat.Prime 677441 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv29,pv73]) (by decide +kernel)
def pv677441 : PrimeValue := ⟨677441, pr677441⟩
private theorem pr677473 : Nat.Prime 677473 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7057]) (by decide +kernel)
def pv677473 : PrimeValue := ⟨677473, pr677473⟩
private theorem pr677533 : Nat.Prime 677533 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv131,pv431]) (by decide +kernel)
def pv677533 : PrimeValue := ⟨677533, pr677533⟩
private theorem pr677563 : Nat.Prime 677563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv112927]) (by decide +kernel)
def pv677563 : PrimeValue := ⟨677563, pr677563⟩
private theorem pr677791 : Nat.Prime 677791 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv17,pv443]) (by decide +kernel)
def pv677791 : PrimeValue := ⟨677791, pr677791⟩
private theorem pr677813 : Nat.Prime 677813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv4133]) (by decide +kernel)
def pv677813 : PrimeValue := ⟨677813, pr677813⟩
private theorem pr677857 : Nat.Prime 677857 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv23,pv307]) (by decide +kernel)
def pv677857 : PrimeValue := ⟨677857, pr677857⟩
private theorem pr678023 : Nat.Prime 678023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv47,pv7213]) (by decide +kernel)
def pv678023 : PrimeValue := ⟨678023, pr678023⟩
private theorem pr678047 : Nat.Prime 678047 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv339023]) (by decide +kernel)
def pv678047 : PrimeValue := ⟨678047, pr678047⟩
private theorem pr678101 : Nat.Prime 678101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv6781]) (by decide +kernel)
def pv678101 : PrimeValue := ⟨678101, pr678101⟩
private theorem pr678103 : Nat.Prime 678103 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv113017]) (by decide +kernel)
def pv678103 : PrimeValue := ⟨678103, pr678103⟩
private theorem pr678157 : Nat.Prime 678157 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv1823]) (by decide +kernel)
def pv678157 : PrimeValue := ⟨678157, pr678157⟩
private theorem pr678211 : Nat.Prime 678211 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv37,pv47]) (by decide +kernel)
def pv678211 : PrimeValue := ⟨678211, pr678211⟩
private theorem pr678221 : Nat.Prime 678221 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv33911]) (by decide +kernel)
def pv678221 : PrimeValue := ⟨678221, pr678221⟩
private theorem pr678367 : Nat.Prime 678367 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv223]) (by decide +kernel)
def pv678367 : PrimeValue := ⟨678367, pr678367⟩
private theorem pr678593 : Nat.Prime 678593 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv461]) (by decide +kernel)
def pv678593 : PrimeValue := ⟨678593, pr678593⟩
private theorem pr679157 : Nat.Prime 679157 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv169789]) (by decide +kernel)
def pv679157 : PrimeValue := ⟨679157, pr679157⟩
private theorem pr679207 : Nat.Prime 679207 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv41,pv251]) (by decide +kernel)
def pv679207 : PrimeValue := ⟨679207, pr679207⟩
private theorem pr679361 : Nat.Prime 679361 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv193]) (by decide +kernel)
def pv679361 : PrimeValue := ⟨679361, pr679361⟩
private theorem pr679381 : Nat.Prime 679381 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv67]) (by decide +kernel)
def pv679381 : PrimeValue := ⟨679381, pr679381⟩
private theorem pr679433 : Nat.Prime 679433 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv47,pv139]) (by decide +kernel)
def pv679433 : PrimeValue := ⟨679433, pr679433⟩
private theorem pr679517 : Nat.Prime 679517 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv8941]) (by decide +kernel)
def pv679517 : PrimeValue := ⟨679517, pr679517⟩
private theorem pr679537 : Nat.Prime 679537 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv13]) (by decide +kernel)
def pv679537 : PrimeValue := ⟨679537, pr679537⟩
private theorem pr679607 : Nat.Prime 679607 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv373,pv911]) (by decide +kernel)
def pv679607 : PrimeValue := ⟨679607, pr679607⟩
private theorem pr679843 : Nat.Prime 679843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv179,pv211]) (by decide +kernel)
def pv679843 : PrimeValue := ⟨679843, pr679843⟩
private theorem pr679867 : Nat.Prime 679867 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv10301]) (by decide +kernel)
def pv679867 : PrimeValue := ⟨679867, pr679867⟩
private theorem pr679891 : Nat.Prime 679891 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv131,pv173]) (by decide +kernel)
def pv679891 : PrimeValue := ⟨679891, pr679891⟩
private theorem pr679951 : Nat.Prime 679951 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv1511]) (by decide +kernel)
def pv679951 : PrimeValue := ⟨679951, pr679951⟩
private theorem pr679961 : Nat.Prime 679961 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv89,pv191]) (by decide +kernel)
def pv679961 : PrimeValue := ⟨679961, pr679961⟩
private theorem pr680027 : Nat.Prime 680027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv8293]) (by decide +kernel)
def pv680027 : PrimeValue := ⟨680027, pr680027⟩
private theorem pr680077 : Nat.Prime 680077 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2099]) (by decide +kernel)
def pv680077 : PrimeValue := ⟨680077, pr680077⟩
private theorem pr680237 : Nat.Prime 680237 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv173,pv983]) (by decide +kernel)
def pv680237 : PrimeValue := ⟨680237, pr680237⟩
private theorem pr680291 : Nat.Prime 680291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv5233]) (by decide +kernel)
def pv680291 : PrimeValue := ⟨680291, pr680291⟩
private theorem pr680327 : Nat.Prime 680327 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv31,pv10973]) (by decide +kernel)
def pv680327 : PrimeValue := ⟨680327, pr680327⟩
private theorem pr680453 : Nat.Prime 680453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv67,pv2539]) (by decide +kernel)
def pv680453 : PrimeValue := ⟨680453, pr680453⟩
private theorem pr680651 : Nat.Prime 680651 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13613]) (by decide +kernel)
def pv680651 : PrimeValue := ⟨680651, pr680651⟩
private theorem pr680803 : Nat.Prime 680803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv113467]) (by decide +kernel)
def pv680803 : PrimeValue := ⟨680803, pr680803⟩
private theorem pr680861 : Nat.Prime 680861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv59,pv577]) (by decide +kernel)
def pv680861 : PrimeValue := ⟨680861, pr680861⟩
private theorem pr680873 : Nat.Prime 680873 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv85109]) (by decide +kernel)
def pv680873 : PrimeValue := ⟨680873, pr680873⟩
private theorem pr680971 : Nat.Prime 680971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv22699]) (by decide +kernel)
def pv680971 : PrimeValue := ⟨680971, pr680971⟩
private theorem pr680987 : Nat.Prime 680987 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv20029]) (by decide +kernel)
def pv680987 : PrimeValue := ⟨680987, pr680987⟩
private theorem pr681061 : Nat.Prime 681061 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv11351]) (by decide +kernel)
def pv681061 : PrimeValue := ⟨681061, pr681061⟩
private theorem pr681113 : Nat.Prime 681113 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv4481]) (by decide +kernel)
def pv681113 : PrimeValue := ⟨681113, pr681113⟩
private theorem pr681271 : Nat.Prime 681271 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv22709]) (by decide +kernel)
def pv681271 : PrimeValue := ⟨681271, pr681271⟩
private theorem pr681341 : Nat.Prime 681341 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv19,pv163]) (by decide +kernel)
def pv681341 : PrimeValue := ⟨681341, pr681341⟩
private theorem pr681407 : Nat.Prime 681407 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv47,pv659]) (by decide +kernel)
def pv681407 : PrimeValue := ⟨681407, pr681407⟩
private theorem pr681427 : Nat.Prime 681427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv12619]) (by decide +kernel)
def pv681427 : PrimeValue := ⟨681427, pr681427⟩
private theorem pr681487 : Nat.Prime 681487 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv8737]) (by decide +kernel)
def pv681487 : PrimeValue := ⟨681487, pr681487⟩
private theorem pr681607 : Nat.Prime 681607 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv1993]) (by decide +kernel)
def pv681607 : PrimeValue := ⟨681607, pr681607⟩
private theorem pr681763 : Nat.Prime 681763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv83]) (by decide +kernel)
def pv681763 : PrimeValue := ⟨681763, pr681763⟩
private theorem pr681841 : Nat.Prime 681841 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv947]) (by decide +kernel)
def pv681841 : PrimeValue := ⟨681841, pr681841⟩
private theorem pr681883 : Nat.Prime 681883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv113647]) (by decide +kernel)
def pv681883 : PrimeValue := ⟨681883, pr681883⟩
private theorem pr681931 : Nat.Prime 681931 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7577]) (by decide +kernel)
def pv681931 : PrimeValue := ⟨681931, pr681931⟩
private theorem pr681977 : Nat.Prime 681977 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv85247]) (by decide +kernel)
def pv681977 : PrimeValue := ⟨681977, pr681977⟩
private theorem pr682001 : Nat.Prime 682001 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv11,pv31]) (by decide +kernel)
def pv682001 : PrimeValue := ⟨682001, pr682001⟩
private theorem pr682063 : Nat.Prime 682063 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv31,pv193]) (by decide +kernel)
def pv682063 : PrimeValue := ⟨682063, pr682063⟩
private theorem pr682147 : Nat.Prime 682147 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv37897]) (by decide +kernel)
def pv682147 : PrimeValue := ⟨682147, pr682147⟩
private theorem pr682247 : Nat.Prime 682247 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv341123]) (by decide +kernel)
def pv682247 : PrimeValue := ⟨682247, pr682247⟩
private theorem pr682447 : Nat.Prime 682447 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv107,pv1063]) (by decide +kernel)
def pv682447 : PrimeValue := ⟨682447, pr682447⟩
private theorem pr682531 : Nat.Prime 682531 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv22751]) (by decide +kernel)
def pv682531 : PrimeValue := ⟨682531, pr682531⟩
private theorem pr682637 : Nat.Prime 682637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv157,pv1087]) (by decide +kernel)
def pv682637 : PrimeValue := ⟨682637, pr682637⟩
private theorem pr682763 : Nat.Prime 682763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv337,pv1013]) (by decide +kernel)
def pv682763 : PrimeValue := ⟨682763, pr682763⟩
private theorem pr682777 : Nat.Prime 682777 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29,pv109]) (by decide +kernel)
def pv682777 : PrimeValue := ⟨682777, pr682777⟩
private theorem pr682951 : Nat.Prime 682951 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv29,pv157]) (by decide +kernel)
def pv682951 : PrimeValue := ⟨682951, pr682951⟩
private theorem pr683041 : Nat.Prime 683041 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv3,pv5,pv1423]) (by decide +kernel)
def pv683041 : PrimeValue := ⟨683041, pr683041⟩
private theorem pr683071 : Nat.Prime 683071 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv22769]) (by decide +kernel)
def pv683071 : PrimeValue := ⟨683071, pr683071⟩
private theorem pr683083 : Nat.Prime 683083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv137,pv277]) (by decide +kernel)
def pv683083 : PrimeValue := ⟨683083, pr683083⟩
private theorem pr683317 : Nat.Prime 683317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv37]) (by decide +kernel)
def pv683317 : PrimeValue := ⟨683317, pr683317⟩
private theorem pr683377 : Nat.Prime 683377 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23,pv619]) (by decide +kernel)
def pv683377 : PrimeValue := ⟨683377, pr683377⟩
private theorem pr683401 : Nat.Prime 683401 :=
  checkPrime_prime (q := pv53) (ls := [pv2,pv3,pv5,pv17,pv67]) (by decide +kernel)
def pv683401 : PrimeValue := ⟨683401, pr683401⟩
private theorem pr683651 : Nat.Prime 683651 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv11,pv113]) (by decide +kernel)
def pv683651 : PrimeValue := ⟨683651, pr683651⟩
private theorem pr683653 : Nat.Prime 683653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv2477]) (by decide +kernel)
def pv683653 : PrimeValue := ⟨683653, pr683653⟩
private theorem pr683687 : Nat.Prime 683687 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv37,pv9239]) (by decide +kernel)
def pv683687 : PrimeValue := ⟨683687, pr683687⟩
private theorem pr683777 : Nat.Prime 683777 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2671]) (by decide +kernel)
def pv683777 : PrimeValue := ⟨683777, pr683777⟩
private theorem pr683783 : Nat.Prime 683783 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv31081]) (by decide +kernel)
def pv683783 : PrimeValue := ⟨683783, pr683783⟩
private theorem pr683807 : Nat.Prime 683807 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv53,pv6451]) (by decide +kernel)
def pv683807 : PrimeValue := ⟨683807, pr683807⟩
private theorem pr683821 : Nat.Prime 683821 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv29,pv131]) (by decide +kernel)
def pv683821 : PrimeValue := ⟨683821, pr683821⟩
private theorem pr683833 : Nat.Prime 683833 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv28493]) (by decide +kernel)
def pv683833 : PrimeValue := ⟨683833, pr683833⟩
private theorem pr683863 : Nat.Prime 683863 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv293,pv389]) (by decide +kernel)
def pv683863 : PrimeValue := ⟨683863, pr683863⟩
private theorem pr683911 : Nat.Prime 683911 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv17,pv149]) (by decide +kernel)
def pv683911 : PrimeValue := ⟨683911, pr683911⟩
private theorem pr684007 : Nat.Prime 684007 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv114001]) (by decide +kernel)
def pv684007 : PrimeValue := ⟨684007, pr684007⟩
private theorem pr684017 : Nat.Prime 684017 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv42751]) (by decide +kernel)
def pv684017 : PrimeValue := ⟨684017, pr684017⟩
private theorem pr684053 : Nat.Prime 684053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv5897]) (by decide +kernel)
def pv684053 : PrimeValue := ⟨684053, pr684053⟩
private theorem pr684347 : Nat.Prime 684347 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv26321]) (by decide +kernel)
def pv684347 : PrimeValue := ⟨684347, pr684347⟩
private theorem pr684373 : Nat.Prime 684373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv41,pv107]) (by decide +kernel)
def pv684373 : PrimeValue := ⟨684373, pr684373⟩
private theorem pr684427 : Nat.Prime 684427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv3083]) (by decide +kernel)
def pv684427 : PrimeValue := ⟨684427, pr684427⟩
private theorem pr684443 : Nat.Prime 684443 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv53,pv587]) (by decide +kernel)
def pv684443 : PrimeValue := ⟨684443, pr684443⟩
private theorem pr684493 : Nat.Prime 684493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv57041]) (by decide +kernel)
def pv684493 : PrimeValue := ⟨684493, pr684493⟩
private theorem pr684527 : Nat.Prime 684527 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv23,pv647]) (by decide +kernel)
def pv684527 : PrimeValue := ⟨684527, pr684527⟩
private theorem pr684581 : Nat.Prime 684581 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv2633]) (by decide +kernel)
def pv684581 : PrimeValue := ⟨684581, pr684581⟩
private theorem pr684731 : Nat.Prime 684731 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv68473]) (by decide +kernel)
def pv684731 : PrimeValue := ⟨684731, pr684731⟩
private theorem pr684973 : Nat.Prime 684973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv53,pv359]) (by decide +kernel)
def pv684973 : PrimeValue := ⟨684973, pr684973⟩
private theorem pr685057 : Nat.Prime 685057 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv223]) (by decide +kernel)
def pv685057 : PrimeValue := ⟨685057, pr685057⟩
private theorem pr685073 : Nat.Prime 685073 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv47,pv911]) (by decide +kernel)
def pv685073 : PrimeValue := ⟨685073, pr685073⟩
private theorem pr685337 : Nat.Prime 685337 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv85667]) (by decide +kernel)
def pv685337 : PrimeValue := ⟨685337, pr685337⟩
private theorem pr685591 : Nat.Prime 685591 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv22853]) (by decide +kernel)
def pv685591 : PrimeValue := ⟨685591, pr685591⟩
private theorem pr685697 : Nat.Prime 685697 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv487]) (by decide +kernel)
def pv685697 : PrimeValue := ⟨685697, pr685697⟩
private theorem pr685753 : Nat.Prime 685753 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv28573]) (by decide +kernel)
def pv685753 : PrimeValue := ⟨685753, pr685753⟩
private theorem pr685907 : Nat.Prime 685907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv23,pv31,pv37]) (by decide +kernel)
def pv685907 : PrimeValue := ⟨685907, pr685907⟩
private theorem pr685963 : Nat.Prime 685963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv12703]) (by decide +kernel)
def pv685963 : PrimeValue := ⟨685963, pr685963⟩
private theorem pr686003 : Nat.Prime 686003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv71,pv4831]) (by decide +kernel)
def pv686003 : PrimeValue := ⟨686003, pr686003⟩
private theorem pr686027 : Nat.Prime 686027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv31183]) (by decide +kernel)
def pv686027 : PrimeValue := ⟨686027, pr686027⟩
private theorem pr686551 : Nat.Prime 686551 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv23,pv199]) (by decide +kernel)
def pv686551 : PrimeValue := ⟨686551, pr686551⟩
private theorem pr686611 : Nat.Prime 686611 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv2543]) (by decide +kernel)
def pv686611 : PrimeValue := ⟨686611, pr686611⟩
private theorem pr686801 : Nat.Prime 686801 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv17,pv101]) (by decide +kernel)
def pv686801 : PrimeValue := ⟨686801, pr686801⟩
private theorem pr686963 : Nat.Prime 686963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv343481]) (by decide +kernel)
def pv686963 : PrimeValue := ⟨686963, pr686963⟩
private theorem pr686971 : Nat.Prime 686971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv449]) (by decide +kernel)
def pv686971 : PrimeValue := ⟨686971, pr686971⟩
private theorem pr686993 : Nat.Prime 686993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv42937]) (by decide +kernel)
def pv686993 : PrimeValue := ⟨686993, pr686993⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
