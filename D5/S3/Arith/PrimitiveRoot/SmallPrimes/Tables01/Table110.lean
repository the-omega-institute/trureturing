/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table110
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table110.pv495611
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table015
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table020
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table032
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table075
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table076

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr495611 : Nat.Prime 495611 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv29,pv1709]) (by decide +kernel)
def pv495611 : PrimeValue := ⟨495611, pr495611⟩
private theorem pr495617 : Nat.Prime 495617 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11]) (by decide +kernel)
def pv495617 : PrimeValue := ⟨495617, pr495617⟩
private theorem pr495667 : Nat.Prime 495667 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv67,pv137]) (by decide +kernel)
def pv495667 : PrimeValue := ⟨495667, pr495667⟩
private theorem pr495713 : Nat.Prime 495713 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv2213]) (by decide +kernel)
def pv495713 : PrimeValue := ⟨495713, pr495713⟩
private theorem pr495749 : Nat.Prime 495749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv19,pv593]) (by decide +kernel)
def pv495749 : PrimeValue := ⟨495749, pr495749⟩
private theorem pr495769 : Nat.Prime 495769 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv13,pv227]) (by decide +kernel)
def pv495769 : PrimeValue := ⟨495769, pr495769⟩
private theorem pr495773 : Nat.Prime 495773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv3023]) (by decide +kernel)
def pv495773 : PrimeValue := ⟨495773, pr495773⟩
private theorem pr495787 : Nat.Prime 495787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv4349]) (by decide +kernel)
def pv495787 : PrimeValue := ⟨495787, pr495787⟩
private theorem pr495791 : Nat.Prime 495791 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv43,pv1153]) (by decide +kernel)
def pv495791 : PrimeValue := ⟨495791, pr495791⟩
private theorem pr495799 : Nat.Prime 495799 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv82633]) (by decide +kernel)
def pv495799 : PrimeValue := ⟨495799, pr495799⟩
private theorem pr495821 : Nat.Prime 495821 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv1907]) (by decide +kernel)
def pv495821 : PrimeValue := ⟨495821, pr495821⟩
private theorem pr495851 : Nat.Prime 495851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv47,pv211]) (by decide +kernel)
def pv495851 : PrimeValue := ⟨495851, pr495851⟩
private theorem pr495877 : Nat.Prime 495877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv43]) (by decide +kernel)
def pv495877 : PrimeValue := ⟨495877, pr495877⟩
private theorem pr495947 : Nat.Prime 495947 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv22543]) (by decide +kernel)
def pv495947 : PrimeValue := ⟨495947, pr495947⟩
private theorem pr495973 : Nat.Prime 495973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv599]) (by decide +kernel)
def pv495973 : PrimeValue := ⟨495973, pr495973⟩
private theorem pr496297 : Nat.Prime 496297 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv61,pv113]) (by decide +kernel)
def pv496297 : PrimeValue := ⟨496297, pr496297⟩
private theorem pr496303 : Nat.Prime 496303 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv181,pv457]) (by decide +kernel)
def pv496303 : PrimeValue := ⟨496303, pr496303⟩
private theorem pr496481 : Nat.Prime 496481 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv29,pv107]) (by decide +kernel)
def pv496481 : PrimeValue := ⟨496481, pr496481⟩
private theorem pr496487 : Nat.Prime 496487 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv248243]) (by decide +kernel)
def pv496487 : PrimeValue := ⟨496487, pr496487⟩
private theorem pr496493 : Nat.Prime 496493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv124123]) (by decide +kernel)
def pv496493 : PrimeValue := ⟨496493, pr496493⟩
private theorem pr496609 : Nat.Prime 496609 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv7,pv739]) (by decide +kernel)
def pv496609 : PrimeValue := ⟨496609, pr496609⟩
private theorem pr496687 : Nat.Prime 496687 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv82781]) (by decide +kernel)
def pv496687 : PrimeValue := ⟨496687, pr496687⟩
private theorem pr496703 : Nat.Prime 496703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv248351]) (by decide +kernel)
def pv496703 : PrimeValue := ⟨496703, pr496703⟩
private theorem pr496733 : Nat.Prime 496733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv124183]) (by decide +kernel)
def pv496733 : PrimeValue := ⟨496733, pr496733⟩
private theorem pr496747 : Nat.Prime 496747 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv9199]) (by decide +kernel)
def pv496747 : PrimeValue := ⟨496747, pr496747⟩
private theorem pr496763 : Nat.Prime 496763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv37,pv137]) (by decide +kernel)
def pv496763 : PrimeValue := ⟨496763, pr496763⟩
private theorem pr496789 : Nat.Prime 496789 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv41399]) (by decide +kernel)
def pv496789 : PrimeValue := ⟨496789, pr496789⟩
private theorem pr496817 : Nat.Prime 496817 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31051]) (by decide +kernel)
def pv496817 : PrimeValue := ⟨496817, pr496817⟩
private theorem pr496841 : Nat.Prime 496841 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv12421]) (by decide +kernel)
def pv496841 : PrimeValue := ⟨496841, pr496841⟩
private theorem pr496877 : Nat.Prime 496877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv7307]) (by decide +kernel)
def pv496877 : PrimeValue := ⟨496877, pr496877⟩
private theorem pr496889 : Nat.Prime 496889 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv19,pv467]) (by decide +kernel)
def pv496889 : PrimeValue := ⟨496889, pr496889⟩
private theorem pr496897 : Nat.Prime 496897 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv647]) (by decide +kernel)
def pv496897 : PrimeValue := ⟨496897, pr496897⟩
private theorem pr496913 : Nat.Prime 496913 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv2389]) (by decide +kernel)
def pv496913 : PrimeValue := ⟨496913, pr496913⟩
private theorem pr496963 : Nat.Prime 496963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv9203]) (by decide +kernel)
def pv496963 : PrimeValue := ⟨496963, pr496963⟩
private theorem pr497041 : Nat.Prime 497041 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv19,pv109]) (by decide +kernel)
def pv497041 : PrimeValue := ⟨497041, pr497041⟩
private theorem pr497047 : Nat.Prime 497047 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv17,pv443]) (by decide +kernel)
def pv497047 : PrimeValue := ⟨497047, pr497047⟩
private theorem pr497093 : Nat.Prime 497093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv151,pv823]) (by decide +kernel)
def pv497093 : PrimeValue := ⟨497093, pr497093⟩
private theorem pr497113 : Nat.Prime 497113 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv11,pv269]) (by decide +kernel)
def pv497113 : PrimeValue := ⟨497113, pr497113⟩
private theorem pr497137 : Nat.Prime 497137 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv10357]) (by decide +kernel)
def pv497137 : PrimeValue := ⟨497137, pr497137⟩
private theorem pr497153 : Nat.Prime 497153 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv971]) (by decide +kernel)
def pv497153 : PrimeValue := ⟨497153, pr497153⟩
private theorem pr497257 : Nat.Prime 497257 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv20719]) (by decide +kernel)
def pv497257 : PrimeValue := ⟨497257, pr497257⟩
private theorem pr497269 : Nat.Prime 497269 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv19,pv727]) (by decide +kernel)
def pv497269 : PrimeValue := ⟨497269, pr497269⟩
private theorem pr497279 : Nat.Prime 497279 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv248639]) (by decide +kernel)
def pv497279 : PrimeValue := ⟨497279, pr497279⟩
private theorem pr497291 : Nat.Prime 497291 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv223]) (by decide +kernel)
def pv497291 : PrimeValue := ⟨497291, pr497291⟩
private theorem pr497303 : Nat.Prime 497303 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv31,pv617]) (by decide +kernel)
def pv497303 : PrimeValue := ⟨497303, pr497303⟩
private theorem pr497501 : Nat.Prime 497501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv199]) (by decide +kernel)
def pv497501 : PrimeValue := ⟨497501, pr497501⟩
private theorem pr497521 : Nat.Prime 497521 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv691]) (by decide +kernel)
def pv497521 : PrimeValue := ⟨497521, pr497521⟩
private theorem pr497557 : Nat.Prime 497557 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv271]) (by decide +kernel)
def pv497557 : PrimeValue := ⟨497557, pr497557⟩
private theorem pr497597 : Nat.Prime 497597 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv43,pv263]) (by decide +kernel)
def pv497597 : PrimeValue := ⟨497597, pr497597⟩
private theorem pr497663 : Nat.Prime 497663 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv22621]) (by decide +kernel)
def pv497663 : PrimeValue := ⟨497663, pr497663⟩
private theorem pr497677 : Nat.Prime 497677 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv67,pv619]) (by decide +kernel)
def pv497677 : PrimeValue := ⟨497677, pr497677⟩
private theorem pr497831 : Nat.Prime 497831 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv5,pv49783]) (by decide +kernel)
def pv497831 : PrimeValue := ⟨497831, pr497831⟩
private theorem pr497839 : Nat.Prime 497839 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv11,pv19,pv397]) (by decide +kernel)
def pv497839 : PrimeValue := ⟨497839, pr497839⟩
private theorem pr497869 : Nat.Prime 497869 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv5927]) (by decide +kernel)
def pv497869 : PrimeValue := ⟨497869, pr497869⟩
private theorem pr497873 : Nat.Prime 497873 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv37]) (by decide +kernel)
def pv497873 : PrimeValue := ⟨497873, pr497873⟩
private theorem pr497899 : Nat.Prime 497899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv139,pv199]) (by decide +kernel)
def pv497899 : PrimeValue := ⟨497899, pr497899⟩
private theorem pr497963 : Nat.Prime 497963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv248981]) (by decide +kernel)
def pv497963 : PrimeValue := ⟨497963, pr497963⟩
private theorem pr497977 : Nat.Prime 497977 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv20749]) (by decide +kernel)
def pv497977 : PrimeValue := ⟨497977, pr497977⟩
private theorem pr497993 : Nat.Prime 497993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv5659]) (by decide +kernel)
def pv497993 : PrimeValue := ⟨497993, pr497993⟩
private theorem pr498013 : Nat.Prime 498013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv47,pv883]) (by decide +kernel)
def pv498013 : PrimeValue := ⟨498013, pr498013⟩
private theorem pr498073 : Nat.Prime 498073 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv20753]) (by decide +kernel)
def pv498073 : PrimeValue := ⟨498073, pr498073⟩
private theorem pr498101 : Nat.Prime 498101 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17,pv293]) (by decide +kernel)
def pv498101 : PrimeValue := ⟨498101, pr498101⟩
private theorem pr498103 : Nat.Prime 498103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv7547]) (by decide +kernel)
def pv498103 : PrimeValue := ⟨498103, pr498103⟩
private theorem pr498167 : Nat.Prime 498167 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv83,pv3001]) (by decide +kernel)
def pv498167 : PrimeValue := ⟨498167, pr498167⟩
private theorem pr498181 : Nat.Prime 498181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv23]) (by decide +kernel)
def pv498181 : PrimeValue := ⟨498181, pr498181⟩
private theorem pr498259 : Nat.Prime 498259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv9227]) (by decide +kernel)
def pv498259 : PrimeValue := ⟨498259, pr498259⟩
private theorem pr498343 : Nat.Prime 498343 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv6389]) (by decide +kernel)
def pv498343 : PrimeValue := ⟨498343, pr498343⟩
private theorem pr498391 : Nat.Prime 498391 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv37,pv449]) (by decide +kernel)
def pv498391 : PrimeValue := ⟨498391, pr498391⟩
private theorem pr498401 : Nat.Prime 498401 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv89]) (by decide +kernel)
def pv498401 : PrimeValue := ⟨498401, pr498401⟩
private theorem pr498409 : Nat.Prime 498409 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv19,pv1093]) (by decide +kernel)
def pv498409 : PrimeValue := ⟨498409, pr498409⟩
private theorem pr498439 : Nat.Prime 498439 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv27691]) (by decide +kernel)
def pv498439 : PrimeValue := ⟨498439, pr498439⟩
private theorem pr498469 : Nat.Prime 498469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv41539]) (by decide +kernel)
def pv498469 : PrimeValue := ⟨498469, pr498469⟩
private theorem pr498493 : Nat.Prime 498493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv61,pv227]) (by decide +kernel)
def pv498493 : PrimeValue := ⟨498493, pr498493⟩
private theorem pr498497 : Nat.Prime 498497 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7789]) (by decide +kernel)
def pv498497 : PrimeValue := ⟨498497, pr498497⟩
private theorem pr498521 : Nat.Prime 498521 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv103]) (by decide +kernel)
def pv498521 : PrimeValue := ⟨498521, pr498521⟩
private theorem pr498523 : Nat.Prime 498523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv4373]) (by decide +kernel)
def pv498523 : PrimeValue := ⟨498523, pr498523⟩
private theorem pr498551 : Nat.Prime 498551 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv59]) (by decide +kernel)
def pv498551 : PrimeValue := ⟨498551, pr498551⟩
private theorem pr498577 : Nat.Prime 498577 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv13,pv17,pv47]) (by decide +kernel)
def pv498577 : PrimeValue := ⟨498577, pr498577⟩
private theorem pr498647 : Nat.Prime 498647 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv283,pv881]) (by decide +kernel)
def pv498647 : PrimeValue := ⟨498647, pr498647⟩
private theorem pr498653 : Nat.Prime 498653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv1619]) (by decide +kernel)
def pv498653 : PrimeValue := ⟨498653, pr498653⟩
private theorem pr498679 : Nat.Prime 498679 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv17,pv4889]) (by decide +kernel)
def pv498679 : PrimeValue := ⟨498679, pr498679⟩
private theorem pr498689 : Nat.Prime 498689 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv487]) (by decide +kernel)
def pv498689 : PrimeValue := ⟨498689, pr498689⟩
private theorem pr498691 : Nat.Prime 498691 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv1847]) (by decide +kernel)
def pv498691 : PrimeValue := ⟨498691, pr498691⟩
private theorem pr498761 : Nat.Prime 498761 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv37,pv337]) (by decide +kernel)
def pv498761 : PrimeValue := ⟨498761, pr498761⟩
private theorem pr498781 : Nat.Prime 498781 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv163]) (by decide +kernel)
def pv498781 : PrimeValue := ⟨498781, pr498781⟩
private theorem pr498787 : Nat.Prime 498787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv59,pv1409]) (by decide +kernel)
def pv498787 : PrimeValue := ⟨498787, pr498787⟩
private theorem pr498791 : Nat.Prime 498791 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv31,pv1609]) (by decide +kernel)
def pv498791 : PrimeValue := ⟨498791, pr498791⟩
private theorem pr498833 : Nat.Prime 498833 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31177]) (by decide +kernel)
def pv498833 : PrimeValue := ⟨498833, pr498833⟩
private theorem pr498907 : Nat.Prime 498907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv9239]) (by decide +kernel)
def pv498907 : PrimeValue := ⟨498907, pr498907⟩
private theorem pr498973 : Nat.Prime 498973 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv43,pv967]) (by decide +kernel)
def pv498973 : PrimeValue := ⟨498973, pr498973⟩
private theorem pr499021 : Nat.Prime 499021 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv8317]) (by decide +kernel)
def pv499021 : PrimeValue := ⟨499021, pr499021⟩
private theorem pr499027 : Nat.Prime 499027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv7561]) (by decide +kernel)
def pv499027 : PrimeValue := ⟨499027, pr499027⟩
private theorem pr499067 : Nat.Prime 499067 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv249533]) (by decide +kernel)
def pv499067 : PrimeValue := ⟨499067, pr499067⟩
private theorem pr499129 : Nat.Prime 499129 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv2971]) (by decide +kernel)
def pv499129 : PrimeValue := ⟨499129, pr499129⟩
private theorem pr499141 : Nat.Prime 499141 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv47,pv59]) (by decide +kernel)
def pv499141 : PrimeValue := ⟨499141, pr499141⟩
private theorem pr499183 : Nat.Prime 499183 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv271,pv307]) (by decide +kernel)
def pv499183 : PrimeValue := ⟨499183, pr499183⟩
private theorem pr499211 : Nat.Prime 499211 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv49921]) (by decide +kernel)
def pv499211 : PrimeValue := ⟨499211, pr499211⟩
private theorem pr499363 : Nat.Prime 499363 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv83227]) (by decide +kernel)
def pv499363 : PrimeValue := ⟨499363, pr499363⟩
private theorem pr499391 : Nat.Prime 499391 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv49939]) (by decide +kernel)
def pv499391 : PrimeValue := ⟨499391, pr499391⟩
private theorem pr499403 : Nat.Prime 499403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv5807]) (by decide +kernel)
def pv499403 : PrimeValue := ⟨499403, pr499403⟩
private theorem pr499423 : Nat.Prime 499423 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv23,pv47]) (by decide +kernel)
def pv499423 : PrimeValue := ⟨499423, pr499423⟩
private theorem pr499483 : Nat.Prime 499483 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv27749]) (by decide +kernel)
def pv499483 : PrimeValue := ⟨499483, pr499483⟩
private theorem pr499519 : Nat.Prime 499519 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv27751]) (by decide +kernel)
def pv499519 : PrimeValue := ⟨499519, pr499519⟩
private theorem pr499621 : Nat.Prime 499621 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv11,pv757]) (by decide +kernel)
def pv499621 : PrimeValue := ⟨499621, pr499621⟩
private theorem pr499633 : Nat.Prime 499633 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv1487]) (by decide +kernel)
def pv499633 : PrimeValue := ⟨499633, pr499633⟩
private theorem pr499637 : Nat.Prime 499637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv124909]) (by decide +kernel)
def pv499637 : PrimeValue := ⟨499637, pr499637⟩
private theorem pr499679 : Nat.Prime 499679 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv229,pv1091]) (by decide +kernel)
def pv499679 : PrimeValue := ⟨499679, pr499679⟩
private theorem pr499693 : Nat.Prime 499693 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv41641]) (by decide +kernel)
def pv499693 : PrimeValue := ⟨499693, pr499693⟩
private theorem pr499729 : Nat.Prime 499729 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv29,pv359]) (by decide +kernel)
def pv499729 : PrimeValue := ⟨499729, pr499729⟩
private theorem pr499747 : Nat.Prime 499747 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv43,pv149]) (by decide +kernel)
def pv499747 : PrimeValue := ⟨499747, pr499747⟩
private theorem pr499781 : Nat.Prime 499781 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv24989]) (by decide +kernel)
def pv499781 : PrimeValue := ⟨499781, pr499781⟩
private theorem pr499853 : Nat.Prime 499853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv6577]) (by decide +kernel)
def pv499853 : PrimeValue := ⟨499853, pr499853⟩
private theorem pr499883 : Nat.Prime 499883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv10867]) (by decide +kernel)
def pv499883 : PrimeValue := ⟨499883, pr499883⟩
private theorem pr499979 : Nat.Prime 499979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv249989]) (by decide +kernel)
def pv499979 : PrimeValue := ⟨499979, pr499979⟩
private theorem pr500057 : Nat.Prime 500057 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv62507]) (by decide +kernel)
def pv500057 : PrimeValue := ⟨500057, pr500057⟩
private theorem pr500107 : Nat.Prime 500107 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv4903]) (by decide +kernel)
def pv500107 : PrimeValue := ⟨500107, pr500107⟩
private theorem pr500153 : Nat.Prime 500153 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv101,pv619]) (by decide +kernel)
def pv500153 : PrimeValue := ⟨500153, pr500153⟩
private theorem pr500167 : Nat.Prime 500167 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv37,pv751]) (by decide +kernel)
def pv500167 : PrimeValue := ⟨500167, pr500167⟩
private theorem pr500173 : Nat.Prime 500173 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv41681]) (by decide +kernel)
def pv500173 : PrimeValue := ⟨500173, pr500173⟩
private theorem pr500179 : Nat.Prime 500179 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv11909]) (by decide +kernel)
def pv500179 : PrimeValue := ⟨500179, pr500179⟩
private theorem pr500231 : Nat.Prime 500231 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv50023]) (by decide +kernel)
def pv500231 : PrimeValue := ⟨500231, pr500231⟩
private theorem pr500237 : Nat.Prime 500237 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv11369]) (by decide +kernel)
def pv500237 : PrimeValue := ⟨500237, pr500237⟩
private theorem pr500257 : Nat.Prime 500257 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv193]) (by decide +kernel)
def pv500257 : PrimeValue := ⟨500257, pr500257⟩
private theorem pr500317 : Nat.Prime 500317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv173,pv241]) (by decide +kernel)
def pv500317 : PrimeValue := ⟨500317, pr500317⟩
private theorem pr500321 : Nat.Prime 500321 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv53,pv59]) (by decide +kernel)
def pv500321 : PrimeValue := ⟨500321, pr500321⟩
private theorem pr500333 : Nat.Prime 500333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv107,pv167]) (by decide +kernel)
def pv500333 : PrimeValue := ⟨500333, pr500333⟩
private theorem pr500413 : Nat.Prime 500413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv17,pv223]) (by decide +kernel)
def pv500413 : PrimeValue := ⟨500413, pr500413⟩
private theorem pr500459 : Nat.Prime 500459 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv35747]) (by decide +kernel)
def pv500459 : PrimeValue := ⟨500459, pr500459⟩
private theorem pr500483 : Nat.Prime 500483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv8629]) (by decide +kernel)
def pv500483 : PrimeValue := ⟨500483, pr500483⟩
private theorem pr500501 : Nat.Prime 500501 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv7,pv11,pv13]) (by decide +kernel)
def pv500501 : PrimeValue := ⟨500501, pr500501⟩
private theorem pr500579 : Nat.Prime 500579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv1481]) (by decide +kernel)
def pv500579 : PrimeValue := ⟨500579, pr500579⟩
private theorem pr500587 : Nat.Prime 500587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv83431]) (by decide +kernel)
def pv500587 : PrimeValue := ⟨500587, pr500587⟩
private theorem pr500677 : Nat.Prime 500677 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv3793]) (by decide +kernel)
def pv500677 : PrimeValue := ⟨500677, pr500677⟩
private theorem pr500693 : Nat.Prime 500693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv43,pv71]) (by decide +kernel)
def pv500693 : PrimeValue := ⟨500693, pr500693⟩
private theorem pr500713 : Nat.Prime 500713 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv31,pv673]) (by decide +kernel)
def pv500713 : PrimeValue := ⟨500713, pr500713⟩
private theorem pr500719 : Nat.Prime 500719 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv17,pv4909]) (by decide +kernel)
def pv500719 : PrimeValue := ⟨500719, pr500719⟩
private theorem pr500723 : Nat.Prime 500723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv250361]) (by decide +kernel)
def pv500723 : PrimeValue := ⟨500723, pr500723⟩
private theorem pr500729 : Nat.Prime 500729 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv62591]) (by decide +kernel)
def pv500729 : PrimeValue := ⟨500729, pr500729⟩
private theorem pr500809 : Nat.Prime 500809 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv11,pv271]) (by decide +kernel)
def pv500809 : PrimeValue := ⟨500809, pr500809⟩
private theorem pr500831 : Nat.Prime 500831 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv11,pv29,pv157]) (by decide +kernel)
def pv500831 : PrimeValue := ⟨500831, pr500831⟩
private theorem pr500861 : Nat.Prime 500861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv79,pv317]) (by decide +kernel)
def pv500861 : PrimeValue := ⟨500861, pr500861⟩
private theorem pr500891 : Nat.Prime 500891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv3853]) (by decide +kernel)
def pv500891 : PrimeValue := ⟨500891, pr500891⟩
private theorem pr500933 : Nat.Prime 500933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv2053]) (by decide +kernel)
def pv500933 : PrimeValue := ⟨500933, pr500933⟩
private theorem pr501131 : Nat.Prime 501131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv7159]) (by decide +kernel)
def pv501131 : PrimeValue := ⟨501131, pr501131⟩
private theorem pr501173 : Nat.Prime 501173 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv2557]) (by decide +kernel)
def pv501173 : PrimeValue := ⟨501173, pr501173⟩
private theorem pr501197 : Nat.Prime 501197 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv125299]) (by decide +kernel)
def pv501197 : PrimeValue := ⟨501197, pr501197⟩
private theorem pr501203 : Nat.Prime 501203 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv37,pv521]) (by decide +kernel)
def pv501203 : PrimeValue := ⟨501203, pr501203⟩
private theorem pr501229 : Nat.Prime 501229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv17]) (by decide +kernel)
def pv501229 : PrimeValue := ⟨501229, pr501229⟩
private theorem pr501233 : Nat.Prime 501233 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31327]) (by decide +kernel)
def pv501233 : PrimeValue := ⟨501233, pr501233⟩
private theorem pr501287 : Nat.Prime 501287 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv250643]) (by decide +kernel)
def pv501287 : PrimeValue := ⟨501287, pr501287⟩
private theorem pr501343 : Nat.Prime 501343 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv83557]) (by decide +kernel)
def pv501343 : PrimeValue := ⟨501343, pr501343⟩
private theorem pr501383 : Nat.Prime 501383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv59,pv607]) (by decide +kernel)
def pv501383 : PrimeValue := ⟨501383, pr501383⟩
private theorem pr501427 : Nat.Prime 501427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv89,pv313]) (by decide +kernel)
def pv501427 : PrimeValue := ⟨501427, pr501427⟩
private theorem pr501563 : Nat.Prime 501563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv67,pv197]) (by decide +kernel)
def pv501563 : PrimeValue := ⟨501563, pr501563⟩
private theorem pr501601 : Nat.Prime 501601 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv11,pv19]) (by decide +kernel)
def pv501601 : PrimeValue := ⟨501601, pr501601⟩
private theorem pr501617 : Nat.Prime 501617 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv107,pv293]) (by decide +kernel)
def pv501617 : PrimeValue := ⟨501617, pr501617⟩
private theorem pr501637 : Nat.Prime 501637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv2459]) (by decide +kernel)
def pv501637 : PrimeValue := ⟨501637, pr501637⟩
private theorem pr501703 : Nat.Prime 501703 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv83617]) (by decide +kernel)
def pv501703 : PrimeValue := ⟨501703, pr501703⟩
private theorem pr501731 : Nat.Prime 501731 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv131,pv383]) (by decide +kernel)
def pv501731 : PrimeValue := ⟨501731, pr501731⟩
private theorem pr501769 : Nat.Prime 501769 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv23,pv101]) (by decide +kernel)
def pv501769 : PrimeValue := ⟨501769, pr501769⟩
private theorem pr501863 : Nat.Prime 501863 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv349,pv719]) (by decide +kernel)
def pv501863 : PrimeValue := ⟨501863, pr501863⟩
private theorem pr501889 : Nat.Prime 501889 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv1307]) (by decide +kernel)
def pv501889 : PrimeValue := ⟨501889, pr501889⟩
private theorem pr501931 : Nat.Prime 501931 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv13]) (by decide +kernel)
def pv501931 : PrimeValue := ⟨501931, pr501931⟩
private theorem pr501953 : Nat.Prime 501953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv23,pv31]) (by decide +kernel)
def pv501953 : PrimeValue := ⟨501953, pr501953⟩
private theorem pr501967 : Nat.Prime 501967 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv79,pv353]) (by decide +kernel)
def pv501967 : PrimeValue := ⟨501967, pr501967⟩
private theorem pr501971 : Nat.Prime 501971 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv71,pv101]) (by decide +kernel)
def pv501971 : PrimeValue := ⟨501971, pr501971⟩
private theorem pr502001 : Nat.Prime 502001 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv251]) (by decide +kernel)
def pv502001 : PrimeValue := ⟨502001, pr502001⟩
private theorem pr502013 : Nat.Prime 502013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv17929]) (by decide +kernel)
def pv502013 : PrimeValue := ⟨502013, pr502013⟩
private theorem pr502057 : Nat.Prime 502057 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv367]) (by decide +kernel)
def pv502057 : PrimeValue := ⟨502057, pr502057⟩
private theorem pr502087 : Nat.Prime 502087 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv41,pv157]) (by decide +kernel)
def pv502087 : PrimeValue := ⟨502087, pr502087⟩
private theorem pr502093 : Nat.Prime 502093 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv4649]) (by decide +kernel)
def pv502093 : PrimeValue := ⟨502093, pr502093⟩
private theorem pr502121 : Nat.Prime 502121 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv12553]) (by decide +kernel)
def pv502121 : PrimeValue := ⟨502121, pr502121⟩
private theorem pr502181 : Nat.Prime 502181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv17,pv211]) (by decide +kernel)
def pv502181 : PrimeValue := ⟨502181, pr502181⟩
private theorem pr502237 : Nat.Prime 502237 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv1993]) (by decide +kernel)
def pv502237 : PrimeValue := ⟨502237, pr502237⟩
private theorem pr502261 : Nat.Prime 502261 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv11,pv761]) (by decide +kernel)
def pv502261 : PrimeValue := ⟨502261, pr502261⟩
private theorem pr502277 : Nat.Prime 502277 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv199,pv631]) (by decide +kernel)
def pv502277 : PrimeValue := ⟨502277, pr502277⟩
private theorem pr502441 : Nat.Prime 502441 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv53,pv79]) (by decide +kernel)
def pv502441 : PrimeValue := ⟨502441, pr502441⟩
private theorem pr502451 : Nat.Prime 502451 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv13,pv773]) (by decide +kernel)
def pv502451 : PrimeValue := ⟨502451, pr502451⟩
private theorem pr502487 : Nat.Prime 502487 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv14779]) (by decide +kernel)
def pv502487 : PrimeValue := ⟨502487, pr502487⟩
private theorem pr502501 : Nat.Prime 502501 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv67]) (by decide +kernel)
def pv502501 : PrimeValue := ⟨502501, pr502501⟩
private theorem pr502553 : Nat.Prime 502553 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv62819]) (by decide +kernel)
def pv502553 : PrimeValue := ⟨502553, pr502553⟩
private theorem pr502597 : Nat.Prime 502597 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv607]) (by decide +kernel)
def pv502597 : PrimeValue := ⟨502597, pr502597⟩
private theorem pr502631 : Nat.Prime 502631 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv50263]) (by decide +kernel)
def pv502631 : PrimeValue := ⟨502631, pr502631⟩
private theorem pr502633 : Nat.Prime 502633 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv179]) (by decide +kernel)
def pv502633 : PrimeValue := ⟨502633, pr502633⟩
private theorem pr502643 : Nat.Prime 502643 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv23,pv223]) (by decide +kernel)
def pv502643 : PrimeValue := ⟨502643, pr502643⟩
private theorem pr502669 : Nat.Prime 502669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13963]) (by decide +kernel)
def pv502669 : PrimeValue := ⟨502669, pr502669⟩
private theorem pr502703 : Nat.Prime 502703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv13229]) (by decide +kernel)
def pv502703 : PrimeValue := ⟨502703, pr502703⟩
private theorem pr502771 : Nat.Prime 502771 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv5,pv16759]) (by decide +kernel)
def pv502771 : PrimeValue := ⟨502771, pr502771⟩
private theorem pr502819 : Nat.Prime 502819 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv181,pv463]) (by decide +kernel)
def pv502819 : PrimeValue := ⟨502819, pr502819⟩
private theorem pr502861 : Nat.Prime 502861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv29]) (by decide +kernel)
def pv502861 : PrimeValue := ⟨502861, pr502861⟩
private theorem pr502921 : Nat.Prime 502921 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv127]) (by decide +kernel)
def pv502921 : PrimeValue := ⟨502921, pr502921⟩
private theorem pr503003 : Nat.Prime 503003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv251501]) (by decide +kernel)
def pv503003 : PrimeValue := ⟨503003, pr503003⟩
private theorem pr503197 : Nat.Prime 503197 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv2207]) (by decide +kernel)
def pv503197 : PrimeValue := ⟨503197, pr503197⟩
private theorem pr503207 : Nat.Prime 503207 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv89,pv257]) (by decide +kernel)
def pv503207 : PrimeValue := ⟨503207, pr503207⟩
private theorem pr503227 : Nat.Prime 503227 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv9319]) (by decide +kernel)
def pv503227 : PrimeValue := ⟨503227, pr503227⟩
private theorem pr503231 : Nat.Prime 503231 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv13,pv79]) (by decide +kernel)
def pv503231 : PrimeValue := ⟨503231, pr503231⟩
private theorem pr503267 : Nat.Prime 503267 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv8677]) (by decide +kernel)
def pv503267 : PrimeValue := ⟨503267, pr503267⟩
private theorem pr503369 : Nat.Prime 503369 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv62921]) (by decide +kernel)
def pv503369 : PrimeValue := ⟨503369, pr503369⟩
private theorem pr503383 : Nat.Prime 503383 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv29,pv263]) (by decide +kernel)
def pv503383 : PrimeValue := ⟨503383, pr503383⟩
private theorem pr503407 : Nat.Prime 503407 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv27967]) (by decide +kernel)
def pv503407 : PrimeValue := ⟨503407, pr503407⟩
private theorem pr503413 : Nat.Prime 503413 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv7,pv13,pv461]) (by decide +kernel)
def pv503413 : PrimeValue := ⟨503413, pr503413⟩
private theorem pr503423 : Nat.Prime 503423 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv37,pv6803]) (by decide +kernel)
def pv503423 : PrimeValue := ⟨503423, pr503423⟩
private theorem pr503431 : Nat.Prime 503431 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv97,pv173]) (by decide +kernel)
def pv503431 : PrimeValue := ⟨503431, pr503431⟩
private theorem pr503441 : Nat.Prime 503441 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv29,pv31]) (by decide +kernel)
def pv503441 : PrimeValue := ⟨503441, pr503441⟩
private theorem pr503549 : Nat.Prime 503549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv125887]) (by decide +kernel)
def pv503549 : PrimeValue := ⟨503549, pr503549⟩
private theorem pr503621 : Nat.Prime 503621 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv149]) (by decide +kernel)
def pv503621 : PrimeValue := ⟨503621, pr503621⟩
private theorem pr503647 : Nat.Prime 503647 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv13,pv587]) (by decide +kernel)
def pv503647 : PrimeValue := ⟨503647, pr503647⟩
private theorem pr503653 : Nat.Prime 503653 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv47]) (by decide +kernel)
def pv503653 : PrimeValue := ⟨503653, pr503653⟩
private theorem pr503663 : Nat.Prime 503663 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv251831]) (by decide +kernel)
def pv503663 : PrimeValue := ⟨503663, pr503663⟩
private theorem pr503803 : Nat.Prime 503803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv2153]) (by decide +kernel)
def pv503803 : PrimeValue := ⟨503803, pr503803⟩
private theorem pr503827 : Nat.Prime 503827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv131,pv641]) (by decide +kernel)
def pv503827 : PrimeValue := ⟨503827, pr503827⟩
private theorem pr503879 : Nat.Prime 503879 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv251939]) (by decide +kernel)
def pv503879 : PrimeValue := ⟨503879, pr503879⟩
private theorem pr503927 : Nat.Prime 503927 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv197,pv1279]) (by decide +kernel)
def pv503927 : PrimeValue := ⟨503927, pr503927⟩
private theorem pr503969 : Nat.Prime 503969 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv15749]) (by decide +kernel)
def pv503969 : PrimeValue := ⟨503969, pr503969⟩
private theorem pr503983 : Nat.Prime 503983 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv17,pv61]) (by decide +kernel)
def pv503983 : PrimeValue := ⟨503983, pr503983⟩
private theorem pr504073 : Nat.Prime 504073 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7001]) (by decide +kernel)
def pv504073 : PrimeValue := ⟨504073, pr504073⟩
private theorem pr504151 : Nat.Prime 504151 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv3361]) (by decide +kernel)
def pv504151 : PrimeValue := ⟨504151, pr504151⟩
private theorem pr504157 : Nat.Prime 504157 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv42013]) (by decide +kernel)
def pv504157 : PrimeValue := ⟨504157, pr504157⟩
private theorem pr504209 : Nat.Prime 504209 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31513]) (by decide +kernel)
def pv504209 : PrimeValue := ⟨504209, pr504209⟩
private theorem pr504221 : Nat.Prime 504221 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17,pv1483]) (by decide +kernel)
def pv504221 : PrimeValue := ⟨504221, pr504221⟩
private theorem pr504349 : Nat.Prime 504349 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv53,pv61]) (by decide +kernel)
def pv504349 : PrimeValue := ⟨504349, pr504349⟩
private theorem pr504359 : Nat.Prime 504359 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv421,pv599]) (by decide +kernel)
def pv504359 : PrimeValue := ⟨504359, pr504359⟩
private theorem pr504389 : Nat.Prime 504389 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv126097]) (by decide +kernel)
def pv504389 : PrimeValue := ⟨504389, pr504389⟩
private theorem pr504461 : Nat.Prime 504461 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv2293]) (by decide +kernel)
def pv504461 : PrimeValue := ⟨504461, pr504461⟩
private theorem pr504473 : Nat.Prime 504473 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv63059]) (by decide +kernel)
def pv504473 : PrimeValue := ⟨504473, pr504473⟩
private theorem pr504527 : Nat.Prime 504527 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv17,pv19,pv71]) (by decide +kernel)
def pv504527 : PrimeValue := ⟨504527, pr504527⟩
private theorem pr504563 : Nat.Prime 504563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv5867]) (by decide +kernel)
def pv504563 : PrimeValue := ⟨504563, pr504563⟩
private theorem pr504599 : Nat.Prime 504599 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv157,pv1607]) (by decide +kernel)
def pv504599 : PrimeValue := ⟨504599, pr504599⟩
private theorem pr504607 : Nat.Prime 504607 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv37,pv2273]) (by decide +kernel)
def pv504607 : PrimeValue := ⟨504607, pr504607⟩
private theorem pr504671 : Nat.Prime 504671 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv109,pv463]) (by decide +kernel)
def pv504671 : PrimeValue := ⟨504671, pr504671⟩
private theorem pr504677 : Nat.Prime 504677 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv281,pv449]) (by decide +kernel)
def pv504677 : PrimeValue := ⟨504677, pr504677⟩
private theorem pr504683 : Nat.Prime 504683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv252341]) (by decide +kernel)
def pv504683 : PrimeValue := ⟨504683, pr504683⟩
private theorem pr504767 : Nat.Prime 504767 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv252383]) (by decide +kernel)
def pv504767 : PrimeValue := ⟨504767, pr504767⟩
private theorem pr504817 : Nat.Prime 504817 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv809]) (by decide +kernel)
def pv504817 : PrimeValue := ⟨504817, pr504817⟩
private theorem pr504821 : Nat.Prime 504821 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv43,pv587]) (by decide +kernel)
def pv504821 : PrimeValue := ⟨504821, pr504821⟩
private theorem pr504877 : Nat.Prime 504877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv42073]) (by decide +kernel)
def pv504877 : PrimeValue := ⟨504877, pr504877⟩
private theorem pr504893 : Nat.Prime 504893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv126223]) (by decide +kernel)
def pv504893 : PrimeValue := ⟨504893, pr504893⟩
private theorem pr504929 : Nat.Prime 504929 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv509]) (by decide +kernel)
def pv504929 : PrimeValue := ⟨504929, pr504929⟩
private theorem pr504937 : Nat.Prime 504937 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7013]) (by decide +kernel)
def pv504937 : PrimeValue := ⟨504937, pr504937⟩
private theorem pr504967 : Nat.Prime 504967 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv1093]) (by decide +kernel)
def pv504967 : PrimeValue := ⟨504967, pr504967⟩
private theorem pr504991 : Nat.Prime 504991 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv31,pv181]) (by decide +kernel)
def pv504991 : PrimeValue := ⟨504991, pr504991⟩
private theorem pr505027 : Nat.Prime 505027 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv28057]) (by decide +kernel)
def pv505027 : PrimeValue := ⟨505027, pr505027⟩
private theorem pr505111 : Nat.Prime 505111 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv113,pv149]) (by decide +kernel)
def pv505111 : PrimeValue := ⟨505111, pr505111⟩
private theorem pr505123 : Nat.Prime 505123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv2903]) (by decide +kernel)
def pv505123 : PrimeValue := ⟨505123, pr505123⟩
private theorem pr505213 : Nat.Prime 505213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv42101]) (by decide +kernel)
def pv505213 : PrimeValue := ⟨505213, pr505213⟩
private theorem pr505231 : Nat.Prime 505231 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv3,pv5,pv11,pv1531]) (by decide +kernel)
def pv505231 : PrimeValue := ⟨505231, pr505231⟩
private theorem pr505283 : Nat.Prime 505283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv252641]) (by decide +kernel)
def pv505283 : PrimeValue := ⟨505283, pr505283⟩
private theorem pr505301 : Nat.Prime 505301 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv31,pv163]) (by decide +kernel)
def pv505301 : PrimeValue := ⟨505301, pr505301⟩
private theorem pr505313 : Nat.Prime 505313 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv15791]) (by decide +kernel)
def pv505313 : PrimeValue := ⟨505313, pr505313⟩
private theorem pr505321 : Nat.Prime 505321 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv4211]) (by decide +kernel)
def pv505321 : PrimeValue := ⟨505321, pr505321⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
