/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table206
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table206.pv687007
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table016
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table027
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table042
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table043
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table092
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table093

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr687007 : Nat.Prime 687007 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv38167]) (by decide +kernel)
def pv687007 : PrimeValue := ⟨687007, pr687007⟩
private theorem pr687017 : Nat.Prime 687017 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv37,pv211]) (by decide +kernel)
def pv687017 : PrimeValue := ⟨687017, pr687017⟩
private theorem pr687031 : Nat.Prime 687031 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv22901]) (by decide +kernel)
def pv687031 : PrimeValue := ⟨687031, pr687031⟩
private theorem pr687101 : Nat.Prime 687101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv6871]) (by decide +kernel)
def pv687101 : PrimeValue := ⟨687101, pr687101⟩
private theorem pr687383 : Nat.Prime 687383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv18089]) (by decide +kernel)
def pv687383 : PrimeValue := ⟨687383, pr687383⟩
private theorem pr687433 : Nat.Prime 687433 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv28643]) (by decide +kernel)
def pv687433 : PrimeValue := ⟨687433, pr687433⟩
private theorem pr687437 : Nat.Prime 687437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv89,pv1931]) (by decide +kernel)
def pv687437 : PrimeValue := ⟨687437, pr687437⟩
private theorem pr687593 : Nat.Prime 687593 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv61,pv1409]) (by decide +kernel)
def pv687593 : PrimeValue := ⟨687593, pr687593⟩
private theorem pr687683 : Nat.Prime 687683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv9293]) (by decide +kernel)
def pv687683 : PrimeValue := ⟨687683, pr687683⟩
private theorem pr687721 : Nat.Prime 687721 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv521]) (by decide +kernel)
def pv687721 : PrimeValue := ⟨687721, pr687721⟩
private theorem pr687847 : Nat.Prime 687847 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv114641]) (by decide +kernel)
def pv687847 : PrimeValue := ⟨687847, pr687847⟩
private theorem pr687893 : Nat.Prime 687893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv3659]) (by decide +kernel)
def pv687893 : PrimeValue := ⟨687893, pr687893⟩
private theorem pr687901 : Nat.Prime 687901 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv2293]) (by decide +kernel)
def pv687901 : PrimeValue := ⟨687901, pr687901⟩
private theorem pr687977 : Nat.Prime 687977 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv3739]) (by decide +kernel)
def pv687977 : PrimeValue := ⟨687977, pr687977⟩
private theorem pr688013 : Nat.Prime 688013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv101,pv131]) (by decide +kernel)
def pv688013 : PrimeValue := ⟨688013, pr688013⟩
private theorem pr688063 : Nat.Prime 688063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv41,pv2797]) (by decide +kernel)
def pv688063 : PrimeValue := ⟨688063, pr688063⟩
private theorem pr688253 : Nat.Prime 688253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv7481]) (by decide +kernel)
def pv688253 : PrimeValue := ⟨688253, pr688253⟩
private theorem pr688357 : Nat.Prime 688357 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19121]) (by decide +kernel)
def pv688357 : PrimeValue := ⟨688357, pr688357⟩
private theorem pr688447 : Nat.Prime 688447 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv19,pv61]) (by decide +kernel)
def pv688447 : PrimeValue := ⟨688447, pr688447⟩
private theorem pr688561 : Nat.Prime 688561 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv19,pv151]) (by decide +kernel)
def pv688561 : PrimeValue := ⟨688561, pr688561⟩
private theorem pr688627 : Nat.Prime 688627 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv67,pv571]) (by decide +kernel)
def pv688627 : PrimeValue := ⟨688627, pr688627⟩
private theorem pr689113 : Nat.Prime 689113 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv563]) (by decide +kernel)
def pv689113 : PrimeValue := ⟨689113, pr689113⟩
private theorem pr689141 : Nat.Prime 689141 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv34457]) (by decide +kernel)
def pv689141 : PrimeValue := ⟨689141, pr689141⟩
private theorem pr689167 : Nat.Prime 689167 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv38287]) (by decide +kernel)
def pv689167 : PrimeValue := ⟨689167, pr689167⟩
private theorem pr689261 : Nat.Prime 689261 :=
  checkPrime_prime (q := pv59) (ls := [pv2,pv5,pv11,pv13,pv241]) (by decide +kernel)
def pv689261 : PrimeValue := ⟨689261, pr689261⟩
private theorem pr689461 : Nat.Prime 689461 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11491]) (by decide +kernel)
def pv689461 : PrimeValue := ⟨689461, pr689461⟩
private theorem pr689713 : Nat.Prime 689713 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv14369]) (by decide +kernel)
def pv689713 : PrimeValue := ⟨689713, pr689713⟩
private theorem pr689761 : Nat.Prime 689761 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv479]) (by decide +kernel)
def pv689761 : PrimeValue := ⟨689761, pr689761⟩
private theorem pr689771 : Nat.Prime 689771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23,pv2999]) (by decide +kernel)
def pv689771 : PrimeValue := ⟨689771, pr689771⟩
private theorem pr689803 : Nat.Prime 689803 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv114967]) (by decide +kernel)
def pv689803 : PrimeValue := ⟨689803, pr689803⟩
private theorem pr689807 : Nat.Prime 689807 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv43,pv617]) (by decide +kernel)
def pv689807 : PrimeValue := ⟨689807, pr689807⟩
private theorem pr689827 : Nat.Prime 689827 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv6763]) (by decide +kernel)
def pv689827 : PrimeValue := ⟨689827, pr689827⟩
private theorem pr689867 : Nat.Prime 689867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv47,pv179]) (by decide +kernel)
def pv689867 : PrimeValue := ⟨689867, pr689867⟩
private theorem pr689903 : Nat.Prime 689903 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv37,pv9323]) (by decide +kernel)
def pv689903 : PrimeValue := ⟨689903, pr689903⟩
private theorem pr689917 : Nat.Prime 689917 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv57493]) (by decide +kernel)
def pv689917 : PrimeValue := ⟨689917, pr689917⟩
private theorem pr689987 : Nat.Prime 689987 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv79,pv397]) (by decide +kernel)
def pv689987 : PrimeValue := ⟨689987, pr689987⟩
private theorem pr690073 : Nat.Prime 690073 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv28753]) (by decide +kernel)
def pv690073 : PrimeValue := ⟨690073, pr690073⟩
private theorem pr690233 : Nat.Prime 690233 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv239]) (by decide +kernel)
def pv690233 : PrimeValue := ⟨690233, pr690233⟩
private theorem pr690293 : Nat.Prime 690293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv172573]) (by decide +kernel)
def pv690293 : PrimeValue := ⟨690293, pr690293⟩
private theorem pr690511 : Nat.Prime 690511 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv23017]) (by decide +kernel)
def pv690511 : PrimeValue := ⟨690511, pr690511⟩
private theorem pr690583 : Nat.Prime 690583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv179,pv643]) (by decide +kernel)
def pv690583 : PrimeValue := ⟨690583, pr690583⟩
private theorem pr690661 : Nat.Prime 690661 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv1279]) (by decide +kernel)
def pv690661 : PrimeValue := ⟨690661, pr690661⟩
private theorem pr690841 : Nat.Prime 690841 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv19,pv101]) (by decide +kernel)
def pv690841 : PrimeValue := ⟨690841, pr690841⟩
private theorem pr691063 : Nat.Prime 691063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv149,pv773]) (by decide +kernel)
def pv691063 : PrimeValue := ⟨691063, pr691063⟩
private theorem pr691151 : Nat.Prime 691151 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv5,pv23,pv601]) (by decide +kernel)
def pv691151 : PrimeValue := ⟨691151, pr691151⟩
private theorem pr691193 : Nat.Prime 691193 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv86399]) (by decide +kernel)
def pv691193 : PrimeValue := ⟨691193, pr691193⟩
private theorem pr691343 : Nat.Prime 691343 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv41,pv8431]) (by decide +kernel)
def pv691343 : PrimeValue := ⟨691343, pr691343⟩
private theorem pr691651 : Nat.Prime 691651 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv29,pv53]) (by decide +kernel)
def pv691651 : PrimeValue := ⟨691651, pr691651⟩
private theorem pr691787 : Nat.Prime 691787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv113,pv3061]) (by decide +kernel)
def pv691787 : PrimeValue := ⟨691787, pr691787⟩
private theorem pr691837 : Nat.Prime 691837 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv57653]) (by decide +kernel)
def pv691837 : PrimeValue := ⟨691837, pr691837⟩
private theorem pr691891 : Nat.Prime 691891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv23063]) (by decide +kernel)
def pv691891 : PrimeValue := ⟨691891, pr691891⟩
private theorem pr692141 : Nat.Prime 692141 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv34607]) (by decide +kernel)
def pv692141 : PrimeValue := ⟨692141, pr692141⟩
private theorem pr692281 : Nat.Prime 692281 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv641]) (by decide +kernel)
def pv692281 : PrimeValue := ⟨692281, pr692281⟩
private theorem pr692333 : Nat.Prime 692333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv73,pv2371]) (by decide +kernel)
def pv692333 : PrimeValue := ⟨692333, pr692333⟩
private theorem pr692347 : Nat.Prime 692347 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv29,pv173]) (by decide +kernel)
def pv692347 : PrimeValue := ⟨692347, pr692347⟩
private theorem pr692453 : Nat.Prime 692453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv331,pv523]) (by decide +kernel)
def pv692453 : PrimeValue := ⟨692453, pr692453⟩
private theorem pr692513 : Nat.Prime 692513 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv19,pv67]) (by decide +kernel)
def pv692513 : PrimeValue := ⟨692513, pr692513⟩
private theorem pr692771 : Nat.Prime 692771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv73]) (by decide +kernel)
def pv692771 : PrimeValue := ⟨692771, pr692771⟩
private theorem pr692927 : Nat.Prime 692927 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv29,pv919]) (by decide +kernel)
def pv692927 : PrimeValue := ⟨692927, pr692927⟩
private theorem pr693061 : Nat.Prime 693061 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11551]) (by decide +kernel)
def pv693061 : PrimeValue := ⟨693061, pr693061⟩
private theorem pr693137 : Nat.Prime 693137 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv43321]) (by decide +kernel)
def pv693137 : PrimeValue := ⟨693137, pr693137⟩
private theorem pr693283 : Nat.Prime 693283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv115547]) (by decide +kernel)
def pv693283 : PrimeValue := ⟨693283, pr693283⟩
private theorem pr693353 : Nat.Prime 693353 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv7879]) (by decide +kernel)
def pv693353 : PrimeValue := ⟨693353, pr693353⟩
private theorem pr693401 : Nat.Prime 693401 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv3467]) (by decide +kernel)
def pv693401 : PrimeValue := ⟨693401, pr693401⟩
private theorem pr693527 : Nat.Prime 693527 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv346763]) (by decide +kernel)
def pv693527 : PrimeValue := ⟨693527, pr693527⟩
private theorem pr693601 : Nat.Prime 693601 :=
  checkPrime_prime (q := pv73) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv693601 : PrimeValue := ⟨693601, pr693601⟩
private theorem pr693677 : Nat.Prime 693677 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv43,pv109]) (by decide +kernel)
def pv693677 : PrimeValue := ⟨693677, pr693677⟩
private theorem pr693697 : Nat.Prime 693697 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv3613]) (by decide +kernel)
def pv693697 : PrimeValue := ⟨693697, pr693697⟩
private theorem pr693881 : Nat.Prime 693881 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv19,pv83]) (by decide +kernel)
def pv693881 : PrimeValue := ⟨693881, pr693881⟩
private theorem pr693943 : Nat.Prime 693943 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv115657]) (by decide +kernel)
def pv693943 : PrimeValue := ⟨693943, pr693943⟩
private theorem pr693961 : Nat.Prime 693961 :=
  checkPrime_prime (q := pv43) (ls := [pv2,pv3,pv5,pv5783]) (by decide +kernel)
def pv693961 : PrimeValue := ⟨693961, pr693961⟩
private theorem pr694061 : Nat.Prime 694061 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv34703]) (by decide +kernel)
def pv694061 : PrimeValue := ⟨694061, pr694061⟩
private theorem pr694207 : Nat.Prime 694207 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv38567]) (by decide +kernel)
def pv694207 : PrimeValue := ⟨694207, pr694207⟩
private theorem pr694223 : Nat.Prime 694223 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv18269]) (by decide +kernel)
def pv694223 : PrimeValue := ⟨694223, pr694223⟩
private theorem pr694271 : Nat.Prime 694271 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv69427]) (by decide +kernel)
def pv694271 : PrimeValue := ⟨694271, pr694271⟩
private theorem pr694333 : Nat.Prime 694333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2143]) (by decide +kernel)
def pv694333 : PrimeValue := ⟨694333, pr694333⟩
private theorem pr694357 : Nat.Prime 694357 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv4451]) (by decide +kernel)
def pv694357 : PrimeValue := ⟨694357, pr694357⟩
private theorem pr694367 : Nat.Prime 694367 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv347183]) (by decide +kernel)
def pv694367 : PrimeValue := ⟨694367, pr694367⟩
private theorem pr694381 : Nat.Prime 694381 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv71,pv163]) (by decide +kernel)
def pv694381 : PrimeValue := ⟨694381, pr694381⟩
private theorem pr694427 : Nat.Prime 694427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv103,pv3371]) (by decide +kernel)
def pv694427 : PrimeValue := ⟨694427, pr694427⟩
private theorem pr694717 : Nat.Prime 694717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv19,pv277]) (by decide +kernel)
def pv694717 : PrimeValue := ⟨694717, pr694717⟩
private theorem pr694721 : Nat.Prime 694721 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv167]) (by decide +kernel)
def pv694721 : PrimeValue := ⟨694721, pr694721⟩
private theorem pr694763 : Nat.Prime 694763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv383,pv907]) (by decide +kernel)
def pv694763 : PrimeValue := ⟨694763, pr694763⟩
private theorem pr694831 : Nat.Prime 694831 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv19,pv23,pv53]) (by decide +kernel)
def pv694831 : PrimeValue := ⟨694831, pr694831⟩
private theorem pr694867 : Nat.Prime 694867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv115811]) (by decide +kernel)
def pv694867 : PrimeValue := ⟨694867, pr694867⟩
private theorem pr695117 : Nat.Prime 695117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv173779]) (by decide +kernel)
def pv695117 : PrimeValue := ⟨695117, pr695117⟩
private theorem pr695207 : Nat.Prime 695207 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv31,pv11213]) (by decide +kernel)
def pv695207 : PrimeValue := ⟨695207, pr695207⟩
private theorem pr695243 : Nat.Prime 695243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv347621]) (by decide +kernel)
def pv695243 : PrimeValue := ⟨695243, pr695243⟩
private theorem pr695293 : Nat.Prime 695293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv4457]) (by decide +kernel)
def pv695293 : PrimeValue := ⟨695293, pr695293⟩
private theorem pr695477 : Nat.Prime 695477 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv9151]) (by decide +kernel)
def pv695477 : PrimeValue := ⟨695477, pr695477⟩
private theorem pr695581 : Nat.Prime 695581 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv11593]) (by decide +kernel)
def pv695581 : PrimeValue := ⟨695581, pr695581⟩
private theorem pr695621 : Nat.Prime 695621 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv34781]) (by decide +kernel)
def pv695621 : PrimeValue := ⟨695621, pr695621⟩
private theorem pr695641 : Nat.Prime 695641 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv11,pv17,pv31]) (by decide +kernel)
def pv695641 : PrimeValue := ⟨695641, pr695641⟩
private theorem pr695701 : Nat.Prime 695701 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv773]) (by decide +kernel)
def pv695701 : PrimeValue := ⟨695701, pr695701⟩
private theorem pr695867 : Nat.Prime 695867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv347933]) (by decide +kernel)
def pv695867 : PrimeValue := ⟨695867, pr695867⟩
private theorem pr695917 : Nat.Prime 695917 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv1487]) (by decide +kernel)
def pv695917 : PrimeValue := ⟨695917, pr695917⟩
private theorem pr696253 : Nat.Prime 696253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv3413]) (by decide +kernel)
def pv696253 : PrimeValue := ⟨696253, pr696253⟩
private theorem pr696257 : Nat.Prime 696257 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv23,pv43]) (by decide +kernel)
def pv696257 : PrimeValue := ⟨696257, pr696257⟩
private theorem pr696281 : Nat.Prime 696281 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv103]) (by decide +kernel)
def pv696281 : PrimeValue := ⟨696281, pr696281⟩
private theorem pr696323 : Nat.Prime 696323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv31,pv1021]) (by decide +kernel)
def pv696323 : PrimeValue := ⟨696323, pr696323⟩
private theorem pr696433 : Nat.Prime 696433 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv1319]) (by decide +kernel)
def pv696433 : PrimeValue := ⟨696433, pr696433⟩
private theorem pr696481 : Nat.Prime 696481 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv1451]) (by decide +kernel)
def pv696481 : PrimeValue := ⟨696481, pr696481⟩
private theorem pr696497 : Nat.Prime 696497 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv101,pv431]) (by decide +kernel)
def pv696497 : PrimeValue := ⟨696497, pr696497⟩
private theorem pr696523 : Nat.Prime 696523 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29,pv4003]) (by decide +kernel)
def pv696523 : PrimeValue := ⟨696523, pr696523⟩
private theorem pr696611 : Nat.Prime 696611 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv69661]) (by decide +kernel)
def pv696611 : PrimeValue := ⟨696611, pr696611⟩
private theorem pr696653 : Nat.Prime 696653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv71,pv223]) (by decide +kernel)
def pv696653 : PrimeValue := ⟨696653, pr696653⟩
private theorem pr696887 : Nat.Prime 696887 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv348443]) (by decide +kernel)
def pv696887 : PrimeValue := ⟨696887, pr696887⟩
private theorem pr697063 : Nat.Prime 697063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv116177]) (by decide +kernel)
def pv697063 : PrimeValue := ⟨697063, pr697063⟩
private theorem pr697093 : Nat.Prime 697093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv5281]) (by decide +kernel)
def pv697093 : PrimeValue := ⟨697093, pr697093⟩
private theorem pr697111 : Nat.Prime 697111 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv19,pv1223]) (by decide +kernel)
def pv697111 : PrimeValue := ⟨697111, pr697111⟩
private theorem pr697181 : Nat.Prime 697181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv3169]) (by decide +kernel)
def pv697181 : PrimeValue := ⟨697181, pr697181⟩
private theorem pr697217 : Nat.Prime 697217 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv419]) (by decide +kernel)
def pv697217 : PrimeValue := ⟨697217, pr697217⟩
private theorem pr697261 : Nat.Prime 697261 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11621]) (by decide +kernel)
def pv697261 : PrimeValue := ⟨697261, pr697261⟩
private theorem pr697351 : Nat.Prime 697351 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv4649]) (by decide +kernel)
def pv697351 : PrimeValue := ⟨697351, pr697351⟩
private theorem pr697441 : Nat.Prime 697441 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv1453]) (by decide +kernel)
def pv697441 : PrimeValue := ⟨697441, pr697441⟩
private theorem pr697457 : Nat.Prime 697457 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv43591]) (by decide +kernel)
def pv697457 : PrimeValue := ⟨697457, pr697457⟩
private theorem pr697511 : Nat.Prime 697511 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv11,pv17,pv373]) (by decide +kernel)
def pv697511 : PrimeValue := ⟨697511, pr697511⟩
private theorem pr697591 : Nat.Prime 697591 :=
  checkPrime_prime (q := pv67) (ls := [pv2,pv3,pv5,pv23,pv337]) (by decide +kernel)
def pv697591 : PrimeValue := ⟨697591, pr697591⟩
private theorem pr697603 : Nat.Prime 697603 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv233,pv499]) (by decide +kernel)
def pv697603 : PrimeValue := ⟨697603, pr697603⟩
private theorem pr697637 : Nat.Prime 697637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv7583]) (by decide +kernel)
def pv697637 : PrimeValue := ⟨697637, pr697637⟩
private theorem pr697681 : Nat.Prime 697681 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv17,pv19]) (by decide +kernel)
def pv697681 : PrimeValue := ⟨697681, pr697681⟩
private theorem pr697687 : Nat.Prime 697687 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv31]) (by decide +kernel)
def pv697687 : PrimeValue := ⟨697687, pr697687⟩
private theorem pr697703 : Nat.Prime 697703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv348851]) (by decide +kernel)
def pv697703 : PrimeValue := ⟨697703, pr697703⟩
private theorem pr697787 : Nat.Prime 697787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv269,pv1297]) (by decide +kernel)
def pv697787 : PrimeValue := ⟨697787, pr697787⟩
private theorem pr697913 : Nat.Prime 697913 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv3793]) (by decide +kernel)
def pv697913 : PrimeValue := ⟨697913, pr697913⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
