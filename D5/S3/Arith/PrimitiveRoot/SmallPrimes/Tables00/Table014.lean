/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table014
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table014.pv32611
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table007
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table008

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr32611 : Nat.Prime 32611 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv1087]) (by decide +kernel)
def pv32611 : PrimeValue := ⟨32611, pr32611⟩
private theorem pr32621 : Nat.Prime 32621 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv233]) (by decide +kernel)
def pv32621 : PrimeValue := ⟨32621, pr32621⟩
private theorem pr32633 : Nat.Prime 32633 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv4079]) (by decide +kernel)
def pv32633 : PrimeValue := ⟨32633, pr32633⟩
private theorem pr32647 : Nat.Prime 32647 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5441]) (by decide +kernel)
def pv32647 : PrimeValue := ⟨32647, pr32647⟩
private theorem pr32653 : Nat.Prime 32653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv907]) (by decide +kernel)
def pv32653 : PrimeValue := ⟨32653, pr32653⟩
private theorem pr32687 : Nat.Prime 32687 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv59,pv277]) (by decide +kernel)
def pv32687 : PrimeValue := ⟨32687, pr32687⟩
private theorem pr32693 : Nat.Prime 32693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv743]) (by decide +kernel)
def pv32693 : PrimeValue := ⟨32693, pr32693⟩
private theorem pr32707 : Nat.Prime 32707 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv79]) (by decide +kernel)
def pv32707 : PrimeValue := ⟨32707, pr32707⟩
private theorem pr32713 : Nat.Prime 32713 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29,pv47]) (by decide +kernel)
def pv32713 : PrimeValue := ⟨32713, pr32713⟩
private theorem pr32717 : Nat.Prime 32717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv8179]) (by decide +kernel)
def pv32717 : PrimeValue := ⟨32717, pr32717⟩
private theorem pr32719 : Nat.Prime 32719 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv19,pv41]) (by decide +kernel)
def pv32719 : PrimeValue := ⟨32719, pr32719⟩
private theorem pr32749 : Nat.Prime 32749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2729]) (by decide +kernel)
def pv32749 : PrimeValue := ⟨32749, pr32749⟩
private theorem pr32771 : Nat.Prime 32771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv29,pv113]) (by decide +kernel)
def pv32771 : PrimeValue := ⟨32771, pr32771⟩
private theorem pr32779 : Nat.Prime 32779 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv607]) (by decide +kernel)
def pv32779 : PrimeValue := ⟨32779, pr32779⟩
private theorem pr32783 : Nat.Prime 32783 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv37,pv443]) (by decide +kernel)
def pv32783 : PrimeValue := ⟨32783, pr32783⟩
private theorem pr32789 : Nat.Prime 32789 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv1171]) (by decide +kernel)
def pv32789 : PrimeValue := ⟨32789, pr32789⟩
private theorem pr32797 : Nat.Prime 32797 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv911]) (by decide +kernel)
def pv32797 : PrimeValue := ⟨32797, pr32797⟩
private theorem pr32801 : Nat.Prime 32801 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv41]) (by decide +kernel)
def pv32801 : PrimeValue := ⟨32801, pr32801⟩
private theorem pr32803 : Nat.Prime 32803 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv71]) (by decide +kernel)
def pv32803 : PrimeValue := ⟨32803, pr32803⟩
private theorem pr32831 : Nat.Prime 32831 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv7,pv67]) (by decide +kernel)
def pv32831 : PrimeValue := ⟨32831, pr32831⟩
private theorem pr32833 : Nat.Prime 32833 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19]) (by decide +kernel)
def pv32833 : PrimeValue := ⟨32833, pr32833⟩
private theorem pr32839 : Nat.Prime 32839 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv421]) (by decide +kernel)
def pv32839 : PrimeValue := ⟨32839, pr32839⟩
private theorem pr32843 : Nat.Prime 32843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv16421]) (by decide +kernel)
def pv32843 : PrimeValue := ⟨32843, pr32843⟩
private theorem pr32869 : Nat.Prime 32869 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv11,pv83]) (by decide +kernel)
def pv32869 : PrimeValue := ⟨32869, pr32869⟩
private theorem pr32887 : Nat.Prime 32887 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv29]) (by decide +kernel)
def pv32887 : PrimeValue := ⟨32887, pr32887⟩
private theorem pr32909 : Nat.Prime 32909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv433]) (by decide +kernel)
def pv32909 : PrimeValue := ⟨32909, pr32909⟩
private theorem pr32911 : Nat.Prime 32911 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv1097]) (by decide +kernel)
def pv32911 : PrimeValue := ⟨32911, pr32911⟩
private theorem pr32917 : Nat.Prime 32917 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv211]) (by decide +kernel)
def pv32917 : PrimeValue := ⟨32917, pr32917⟩
private theorem pr32933 : Nat.Prime 32933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv8233]) (by decide +kernel)
def pv32933 : PrimeValue := ⟨32933, pr32933⟩
private theorem pr32939 : Nat.Prime 32939 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv383]) (by decide +kernel)
def pv32939 : PrimeValue := ⟨32939, pr32939⟩
private theorem pr32941 : Nat.Prime 32941 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv61]) (by decide +kernel)
def pv32941 : PrimeValue := ⟨32941, pr32941⟩
private theorem pr32957 : Nat.Prime 32957 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv7,pv11,pv107]) (by decide +kernel)
def pv32957 : PrimeValue := ⟨32957, pr32957⟩
private theorem pr32969 : Nat.Prime 32969 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv317]) (by decide +kernel)
def pv32969 : PrimeValue := ⟨32969, pr32969⟩
private theorem pr32971 : Nat.Prime 32971 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv157]) (by decide +kernel)
def pv32971 : PrimeValue := ⟨32971, pr32971⟩
private theorem pr32983 : Nat.Prime 32983 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv239]) (by decide +kernel)
def pv32983 : PrimeValue := ⟨32983, pr32983⟩
private theorem pr32987 : Nat.Prime 32987 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv16493]) (by decide +kernel)
def pv32987 : PrimeValue := ⟨32987, pr32987⟩
private theorem pr32993 : Nat.Prime 32993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1031]) (by decide +kernel)
def pv32993 : PrimeValue := ⟨32993, pr32993⟩
private theorem pr32999 : Nat.Prime 32999 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv2357]) (by decide +kernel)
def pv32999 : PrimeValue := ⟨32999, pr32999⟩
private theorem pr33013 : Nat.Prime 33013 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv131]) (by decide +kernel)
def pv33013 : PrimeValue := ⟨33013, pr33013⟩
private theorem pr33023 : Nat.Prime 33023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv19,pv79]) (by decide +kernel)
def pv33023 : PrimeValue := ⟨33023, pr33023⟩
private theorem pr33029 : Nat.Prime 33029 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv359]) (by decide +kernel)
def pv33029 : PrimeValue := ⟨33029, pr33029⟩
private theorem pr33037 : Nat.Prime 33037 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2753]) (by decide +kernel)
def pv33037 : PrimeValue := ⟨33037, pr33037⟩
private theorem pr33049 : Nat.Prime 33049 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv17]) (by decide +kernel)
def pv33049 : PrimeValue := ⟨33049, pr33049⟩
private theorem pr33053 : Nat.Prime 33053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv8263]) (by decide +kernel)
def pv33053 : PrimeValue := ⟨33053, pr33053⟩
private theorem pr33071 : Nat.Prime 33071 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv3307]) (by decide +kernel)
def pv33071 : PrimeValue := ⟨33071, pr33071⟩
private theorem pr33073 : Nat.Prime 33073 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv53]) (by decide +kernel)
def pv33073 : PrimeValue := ⟨33073, pr33073⟩
private theorem pr33083 : Nat.Prime 33083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv17,pv139]) (by decide +kernel)
def pv33083 : PrimeValue := ⟨33083, pr33083⟩
private theorem pr33091 : Nat.Prime 33091 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv1103]) (by decide +kernel)
def pv33091 : PrimeValue := ⟨33091, pr33091⟩
private theorem pr33107 : Nat.Prime 33107 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv16553]) (by decide +kernel)
def pv33107 : PrimeValue := ⟨33107, pr33107⟩
private theorem pr33113 : Nat.Prime 33113 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv4139]) (by decide +kernel)
def pv33113 : PrimeValue := ⟨33113, pr33113⟩
private theorem pr33119 : Nat.Prime 33119 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv29,pv571]) (by decide +kernel)
def pv33119 : PrimeValue := ⟨33119, pr33119⟩
private theorem pr33149 : Nat.Prime 33149 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv8287]) (by decide +kernel)
def pv33149 : PrimeValue := ⟨33149, pr33149⟩
private theorem pr33151 : Nat.Prime 33151 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv17]) (by decide +kernel)
def pv33151 : PrimeValue := ⟨33151, pr33151⟩
private theorem pr33161 : Nat.Prime 33161 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv829]) (by decide +kernel)
def pv33161 : PrimeValue := ⟨33161, pr33161⟩
private theorem pr33179 : Nat.Prime 33179 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53,pv313]) (by decide +kernel)
def pv33179 : PrimeValue := ⟨33179, pr33179⟩
private theorem pr33181 : Nat.Prime 33181 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv79]) (by decide +kernel)
def pv33181 : PrimeValue := ⟨33181, pr33181⟩
private theorem pr33191 : Nat.Prime 33191 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv3319]) (by decide +kernel)
def pv33191 : PrimeValue := ⟨33191, pr33191⟩
private theorem pr33199 : Nat.Prime 33199 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv503]) (by decide +kernel)
def pv33199 : PrimeValue := ⟨33199, pr33199⟩
private theorem pr33203 : Nat.Prime 33203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv1277]) (by decide +kernel)
def pv33203 : PrimeValue := ⟨33203, pr33203⟩
private theorem pr33211 : Nat.Prime 33211 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv41]) (by decide +kernel)
def pv33211 : PrimeValue := ⟨33211, pr33211⟩
private theorem pr33223 : Nat.Prime 33223 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv113]) (by decide +kernel)
def pv33223 : PrimeValue := ⟨33223, pr33223⟩
private theorem pr33247 : Nat.Prime 33247 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1847]) (by decide +kernel)
def pv33247 : PrimeValue := ⟨33247, pr33247⟩
private theorem pr33287 : Nat.Prime 33287 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv17,pv89]) (by decide +kernel)
def pv33287 : PrimeValue := ⟨33287, pr33287⟩
private theorem pr33289 : Nat.Prime 33289 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv19,pv73]) (by decide +kernel)
def pv33289 : PrimeValue := ⟨33289, pr33289⟩
private theorem pr33301 : Nat.Prime 33301 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv37]) (by decide +kernel)
def pv33301 : PrimeValue := ⟨33301, pr33301⟩
private theorem pr33311 : Nat.Prime 33311 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv3331]) (by decide +kernel)
def pv33311 : PrimeValue := ⟨33311, pr33311⟩
private theorem pr33317 : Nat.Prime 33317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv8329]) (by decide +kernel)
def pv33317 : PrimeValue := ⟨33317, pr33317⟩
private theorem pr33329 : Nat.Prime 33329 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2083]) (by decide +kernel)
def pv33329 : PrimeValue := ⟨33329, pr33329⟩
private theorem pr33331 : Nat.Prime 33331 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv101]) (by decide +kernel)
def pv33331 : PrimeValue := ⟨33331, pr33331⟩
private theorem pr33343 : Nat.Prime 33343 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5557]) (by decide +kernel)
def pv33343 : PrimeValue := ⟨33343, pr33343⟩
private theorem pr33347 : Nat.Prime 33347 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv16673]) (by decide +kernel)
def pv33347 : PrimeValue := ⟨33347, pr33347⟩
private theorem pr33349 : Nat.Prime 33349 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv397]) (by decide +kernel)
def pv33349 : PrimeValue := ⟨33349, pr33349⟩
private theorem pr33353 : Nat.Prime 33353 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv379]) (by decide +kernel)
def pv33353 : PrimeValue := ⟨33353, pr33353⟩
private theorem pr33359 : Nat.Prime 33359 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv13,pv1283]) (by decide +kernel)
def pv33359 : PrimeValue := ⟨33359, pr33359⟩
private theorem pr33377 : Nat.Prime 33377 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv149]) (by decide +kernel)
def pv33377 : PrimeValue := ⟨33377, pr33377⟩
private theorem pr33391 : Nat.Prime 33391 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv53]) (by decide +kernel)
def pv33391 : PrimeValue := ⟨33391, pr33391⟩
private theorem pr33403 : Nat.Prime 33403 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv293]) (by decide +kernel)
def pv33403 : PrimeValue := ⟨33403, pr33403⟩
private theorem pr33409 : Nat.Prime 33409 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv29]) (by decide +kernel)
def pv33409 : PrimeValue := ⟨33409, pr33409⟩
private theorem pr33413 : Nat.Prime 33413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv8353]) (by decide +kernel)
def pv33413 : PrimeValue := ⟨33413, pr33413⟩
private theorem pr33427 : Nat.Prime 33427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv619]) (by decide +kernel)
def pv33427 : PrimeValue := ⟨33427, pr33427⟩
private theorem pr33457 : Nat.Prime 33457 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv17,pv41]) (by decide +kernel)
def pv33457 : PrimeValue := ⟨33457, pr33457⟩
private theorem pr33461 : Nat.Prime 33461 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv239]) (by decide +kernel)
def pv33461 : PrimeValue := ⟨33461, pr33461⟩
private theorem pr33469 : Nat.Prime 33469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2789]) (by decide +kernel)
def pv33469 : PrimeValue := ⟨33469, pr33469⟩
private theorem pr33479 : Nat.Prime 33479 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv19,pv881]) (by decide +kernel)
def pv33479 : PrimeValue := ⟨33479, pr33479⟩
private theorem pr33487 : Nat.Prime 33487 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5581]) (by decide +kernel)
def pv33487 : PrimeValue := ⟨33487, pr33487⟩
private theorem pr33493 : Nat.Prime 33493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2791]) (by decide +kernel)
def pv33493 : PrimeValue := ⟨33493, pr33493⟩
private theorem pr33503 : Nat.Prime 33503 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv2393]) (by decide +kernel)
def pv33503 : PrimeValue := ⟨33503, pr33503⟩
private theorem pr33521 : Nat.Prime 33521 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv419]) (by decide +kernel)
def pv33521 : PrimeValue := ⟨33521, pr33521⟩
private theorem pr33529 : Nat.Prime 33529 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv127]) (by decide +kernel)
def pv33529 : PrimeValue := ⟨33529, pr33529⟩
private theorem pr33533 : Nat.Prime 33533 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv83,pv101]) (by decide +kernel)
def pv33533 : PrimeValue := ⟨33533, pr33533⟩
private theorem pr33547 : Nat.Prime 33547 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5591]) (by decide +kernel)
def pv33547 : PrimeValue := ⟨33547, pr33547⟩
private theorem pr33563 : Nat.Prime 33563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv97,pv173]) (by decide +kernel)
def pv33563 : PrimeValue := ⟨33563, pr33563⟩
private theorem pr33569 : Nat.Prime 33569 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1049]) (by decide +kernel)
def pv33569 : PrimeValue := ⟨33569, pr33569⟩
private theorem pr33577 : Nat.Prime 33577 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1399]) (by decide +kernel)
def pv33577 : PrimeValue := ⟨33577, pr33577⟩
private theorem pr33581 : Nat.Prime 33581 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23,pv73]) (by decide +kernel)
def pv33581 : PrimeValue := ⟨33581, pr33581⟩
private theorem pr33587 : Nat.Prime 33587 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv2399]) (by decide +kernel)
def pv33587 : PrimeValue := ⟨33587, pr33587⟩
private theorem pr33589 : Nat.Prime 33589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv311]) (by decide +kernel)
def pv33589 : PrimeValue := ⟨33589, pr33589⟩
private theorem pr33599 : Nat.Prime 33599 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv107,pv157]) (by decide +kernel)
def pv33599 : PrimeValue := ⟨33599, pr33599⟩
private theorem pr33601 : Nat.Prime 33601 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv33601 : PrimeValue := ⟨33601, pr33601⟩
private theorem pr33613 : Nat.Prime 33613 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2801]) (by decide +kernel)
def pv33613 : PrimeValue := ⟨33613, pr33613⟩
private theorem pr33617 : Nat.Prime 33617 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv191]) (by decide +kernel)
def pv33617 : PrimeValue := ⟨33617, pr33617⟩
private theorem pr33619 : Nat.Prime 33619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv431]) (by decide +kernel)
def pv33619 : PrimeValue := ⟨33619, pr33619⟩
private theorem pr33623 : Nat.Prime 33623 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv16811]) (by decide +kernel)
def pv33623 : PrimeValue := ⟨33623, pr33623⟩
private theorem pr33629 : Nat.Prime 33629 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv1201]) (by decide +kernel)
def pv33629 : PrimeValue := ⟨33629, pr33629⟩
private theorem pr33637 : Nat.Prime 33637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2803]) (by decide +kernel)
def pv33637 : PrimeValue := ⟨33637, pr33637⟩
private theorem pr33641 : Nat.Prime 33641 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv29]) (by decide +kernel)
def pv33641 : PrimeValue := ⟨33641, pr33641⟩
private theorem pr33647 : Nat.Prime 33647 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv16823]) (by decide +kernel)
def pv33647 : PrimeValue := ⟨33647, pr33647⟩
private theorem pr33679 : Nat.Prime 33679 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv1871]) (by decide +kernel)
def pv33679 : PrimeValue := ⟨33679, pr33679⟩
private theorem pr33703 : Nat.Prime 33703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv41,pv137]) (by decide +kernel)
def pv33703 : PrimeValue := ⟨33703, pr33703⟩
private theorem pr33713 : Nat.Prime 33713 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv43]) (by decide +kernel)
def pv33713 : PrimeValue := ⟨33713, pr33713⟩
private theorem pr33721 : Nat.Prime 33721 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv281]) (by decide +kernel)
def pv33721 : PrimeValue := ⟨33721, pr33721⟩
private theorem pr33739 : Nat.Prime 33739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5623]) (by decide +kernel)
def pv33739 : PrimeValue := ⟨33739, pr33739⟩
private theorem pr33749 : Nat.Prime 33749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv13,pv59]) (by decide +kernel)
def pv33749 : PrimeValue := ⟨33749, pr33749⟩
private theorem pr33751 : Nat.Prime 33751 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv33751 : PrimeValue := ⟨33751, pr33751⟩
private theorem pr33757 : Nat.Prime 33757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv97]) (by decide +kernel)
def pv33757 : PrimeValue := ⟨33757, pr33757⟩
private theorem pr33767 : Nat.Prime 33767 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv16883]) (by decide +kernel)
def pv33767 : PrimeValue := ⟨33767, pr33767⟩
private theorem pr33769 : Nat.Prime 33769 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv67]) (by decide +kernel)
def pv33769 : PrimeValue := ⟨33769, pr33769⟩
private theorem pr33773 : Nat.Prime 33773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv8443]) (by decide +kernel)
def pv33773 : PrimeValue := ⟨33773, pr33773⟩
private theorem pr33791 : Nat.Prime 33791 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv31,pv109]) (by decide +kernel)
def pv33791 : PrimeValue := ⟨33791, pr33791⟩
private theorem pr33797 : Nat.Prime 33797 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv17,pv71]) (by decide +kernel)
def pv33797 : PrimeValue := ⟨33797, pr33797⟩
private theorem pr33809 : Nat.Prime 33809 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2113]) (by decide +kernel)
def pv33809 : PrimeValue := ⟨33809, pr33809⟩
private theorem pr33811 : Nat.Prime 33811 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv7,pv23]) (by decide +kernel)
def pv33811 : PrimeValue := ⟨33811, pr33811⟩
private theorem pr33827 : Nat.Prime 33827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv1301]) (by decide +kernel)
def pv33827 : PrimeValue := ⟨33827, pr33827⟩
private theorem pr33829 : Nat.Prime 33829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2819]) (by decide +kernel)
def pv33829 : PrimeValue := ⟨33829, pr33829⟩
private theorem pr33851 : Nat.Prime 33851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv677]) (by decide +kernel)
def pv33851 : PrimeValue := ⟨33851, pr33851⟩
private theorem pr33857 : Nat.Prime 33857 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23]) (by decide +kernel)
def pv33857 : PrimeValue := ⟨33857, pr33857⟩
private theorem pr33863 : Nat.Prime 33863 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv16931]) (by decide +kernel)
def pv33863 : PrimeValue := ⟨33863, pr33863⟩
private theorem pr33871 : Nat.Prime 33871 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv1129]) (by decide +kernel)
def pv33871 : PrimeValue := ⟨33871, pr33871⟩
private theorem pr33889 : Nat.Prime 33889 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv353]) (by decide +kernel)
def pv33889 : PrimeValue := ⟨33889, pr33889⟩
private theorem pr33893 : Nat.Prime 33893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv229]) (by decide +kernel)
def pv33893 : PrimeValue := ⟨33893, pr33893⟩
private theorem pr33911 : Nat.Prime 33911 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv3391]) (by decide +kernel)
def pv33911 : PrimeValue := ⟨33911, pr33911⟩
private theorem pr33923 : Nat.Prime 33923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv2423]) (by decide +kernel)
def pv33923 : PrimeValue := ⟨33923, pr33923⟩
private theorem pr33931 : Nat.Prime 33931 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv29]) (by decide +kernel)
def pv33931 : PrimeValue := ⟨33931, pr33931⟩
private theorem pr33937 : Nat.Prime 33937 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv101]) (by decide +kernel)
def pv33937 : PrimeValue := ⟨33937, pr33937⟩
private theorem pr33941 : Nat.Prime 33941 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1697]) (by decide +kernel)
def pv33941 : PrimeValue := ⟨33941, pr33941⟩
private theorem pr33961 : Nat.Prime 33961 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv283]) (by decide +kernel)
def pv33961 : PrimeValue := ⟨33961, pr33961⟩
private theorem pr33967 : Nat.Prime 33967 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv37]) (by decide +kernel)
def pv33967 : PrimeValue := ⟨33967, pr33967⟩
private theorem pr33997 : Nat.Prime 33997 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2833]) (by decide +kernel)
def pv33997 : PrimeValue := ⟨33997, pr33997⟩
private theorem pr34019 : Nat.Prime 34019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv73,pv233]) (by decide +kernel)
def pv34019 : PrimeValue := ⟨34019, pr34019⟩
private theorem pr34031 : Nat.Prime 34031 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv41,pv83]) (by decide +kernel)
def pv34031 : PrimeValue := ⟨34031, pr34031⟩
private theorem pr34033 : Nat.Prime 34033 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv709]) (by decide +kernel)
def pv34033 : PrimeValue := ⟨34033, pr34033⟩
private theorem pr34039 : Nat.Prime 34039 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv31,pv61]) (by decide +kernel)
def pv34039 : PrimeValue := ⟨34039, pr34039⟩
private theorem pr34057 : Nat.Prime 34057 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv43]) (by decide +kernel)
def pv34057 : PrimeValue := ⟨34057, pr34057⟩
private theorem pr34061 : Nat.Prime 34061 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv131]) (by decide +kernel)
def pv34061 : PrimeValue := ⟨34061, pr34061⟩
private theorem pr34123 : Nat.Prime 34123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv47]) (by decide +kernel)
def pv34123 : PrimeValue := ⟨34123, pr34123⟩
private theorem pr34127 : Nat.Prime 34127 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv113,pv151]) (by decide +kernel)
def pv34127 : PrimeValue := ⟨34127, pr34127⟩
private theorem pr34129 : Nat.Prime 34129 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv79]) (by decide +kernel)
def pv34129 : PrimeValue := ⟨34129, pr34129⟩
private theorem pr34141 : Nat.Prime 34141 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv569]) (by decide +kernel)
def pv34141 : PrimeValue := ⟨34141, pr34141⟩
private theorem pr34147 : Nat.Prime 34147 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv271]) (by decide +kernel)
def pv34147 : PrimeValue := ⟨34147, pr34147⟩
private theorem pr34157 : Nat.Prime 34157 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv8539]) (by decide +kernel)
def pv34157 : PrimeValue := ⟨34157, pr34157⟩
private theorem pr34159 : Nat.Prime 34159 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5693]) (by decide +kernel)
def pv34159 : PrimeValue := ⟨34159, pr34159⟩
private theorem pr34171 : Nat.Prime 34171 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv67]) (by decide +kernel)
def pv34171 : PrimeValue := ⟨34171, pr34171⟩
private theorem pr34183 : Nat.Prime 34183 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv211]) (by decide +kernel)
def pv34183 : PrimeValue := ⟨34183, pr34183⟩
private theorem pr34211 : Nat.Prime 34211 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv311]) (by decide +kernel)
def pv34211 : PrimeValue := ⟨34211, pr34211⟩
private theorem pr34213 : Nat.Prime 34213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2851]) (by decide +kernel)
def pv34213 : PrimeValue := ⟨34213, pr34213⟩
private theorem pr34217 : Nat.Prime 34217 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv13,pv47]) (by decide +kernel)
def pv34217 : PrimeValue := ⟨34217, pr34217⟩
private theorem pr34231 : Nat.Prime 34231 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv163]) (by decide +kernel)
def pv34231 : PrimeValue := ⟨34231, pr34231⟩
private theorem pr34253 : Nat.Prime 34253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv8563]) (by decide +kernel)
def pv34253 : PrimeValue := ⟨34253, pr34253⟩
private theorem pr34259 : Nat.Prime 34259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv2447]) (by decide +kernel)
def pv34259 : PrimeValue := ⟨34259, pr34259⟩
private theorem pr34261 : Nat.Prime 34261 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv571]) (by decide +kernel)
def pv34261 : PrimeValue := ⟨34261, pr34261⟩
private theorem pr34267 : Nat.Prime 34267 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5711]) (by decide +kernel)
def pv34267 : PrimeValue := ⟨34267, pr34267⟩
private theorem pr34273 : Nat.Prime 34273 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv17]) (by decide +kernel)
def pv34273 : PrimeValue := ⟨34273, pr34273⟩
private theorem pr34283 : Nat.Prime 34283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv281]) (by decide +kernel)
def pv34283 : PrimeValue := ⟨34283, pr34283⟩
private theorem pr34297 : Nat.Prime 34297 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1429]) (by decide +kernel)
def pv34297 : PrimeValue := ⟨34297, pr34297⟩
private theorem pr34301 : Nat.Prime 34301 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7]) (by decide +kernel)
def pv34301 : PrimeValue := ⟨34301, pr34301⟩
private theorem pr34303 : Nat.Prime 34303 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5717]) (by decide +kernel)
def pv34303 : PrimeValue := ⟨34303, pr34303⟩
private theorem pr34313 : Nat.Prime 34313 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv4289]) (by decide +kernel)
def pv34313 : PrimeValue := ⟨34313, pr34313⟩
private theorem pr34319 : Nat.Prime 34319 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv17159]) (by decide +kernel)
def pv34319 : PrimeValue := ⟨34319, pr34319⟩
private theorem pr34327 : Nat.Prime 34327 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1907]) (by decide +kernel)
def pv34327 : PrimeValue := ⟨34327, pr34327⟩
private theorem pr34337 : Nat.Prime 34337 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv37]) (by decide +kernel)
def pv34337 : PrimeValue := ⟨34337, pr34337⟩
private theorem pr34351 : Nat.Prime 34351 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv229]) (by decide +kernel)
def pv34351 : PrimeValue := ⟨34351, pr34351⟩
private theorem pr34361 : Nat.Prime 34361 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv859]) (by decide +kernel)
def pv34361 : PrimeValue := ⟨34361, pr34361⟩
private theorem pr34367 : Nat.Prime 34367 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17183]) (by decide +kernel)
def pv34367 : PrimeValue := ⟨34367, pr34367⟩
private theorem pr34369 : Nat.Prime 34369 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv179]) (by decide +kernel)
def pv34369 : PrimeValue := ⟨34369, pr34369⟩
private theorem pr34381 : Nat.Prime 34381 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv191]) (by decide +kernel)
def pv34381 : PrimeValue := ⟨34381, pr34381⟩
private theorem pr34403 : Nat.Prime 34403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv103,pv167]) (by decide +kernel)
def pv34403 : PrimeValue := ⟨34403, pr34403⟩
private theorem pr34421 : Nat.Prime 34421 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1721]) (by decide +kernel)
def pv34421 : PrimeValue := ⟨34421, pr34421⟩
private theorem pr34429 : Nat.Prime 34429 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv151]) (by decide +kernel)
def pv34429 : PrimeValue := ⟨34429, pr34429⟩
private theorem pr34439 : Nat.Prime 34439 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv67,pv257]) (by decide +kernel)
def pv34439 : PrimeValue := ⟨34439, pr34439⟩
private theorem pr34457 : Nat.Prime 34457 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv59,pv73]) (by decide +kernel)
def pv34457 : PrimeValue := ⟨34457, pr34457⟩
private theorem pr34469 : Nat.Prime 34469 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv7,pv1231]) (by decide +kernel)
def pv34469 : PrimeValue := ⟨34469, pr34469⟩
private theorem pr34471 : Nat.Prime 34471 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv383]) (by decide +kernel)
def pv34471 : PrimeValue := ⟨34471, pr34471⟩
private theorem pr34483 : Nat.Prime 34483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv821]) (by decide +kernel)
def pv34483 : PrimeValue := ⟨34483, pr34483⟩
private theorem pr34487 : Nat.Prime 34487 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv43,pv401]) (by decide +kernel)
def pv34487 : PrimeValue := ⟨34487, pr34487⟩
private theorem pr34499 : Nat.Prime 34499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv367]) (by decide +kernel)
def pv34499 : PrimeValue := ⟨34499, pr34499⟩
private theorem pr34501 : Nat.Prime 34501 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv23]) (by decide +kernel)
def pv34501 : PrimeValue := ⟨34501, pr34501⟩
private theorem pr34511 : Nat.Prime 34511 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv17,pv29]) (by decide +kernel)
def pv34511 : PrimeValue := ⟨34511, pr34511⟩
private theorem pr34513 : Nat.Prime 34513 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv719]) (by decide +kernel)
def pv34513 : PrimeValue := ⟨34513, pr34513⟩
private theorem pr34519 : Nat.Prime 34519 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv523]) (by decide +kernel)
def pv34519 : PrimeValue := ⟨34519, pr34519⟩
private theorem pr34537 : Nat.Prime 34537 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1439]) (by decide +kernel)
def pv34537 : PrimeValue := ⟨34537, pr34537⟩
private theorem pr34543 : Nat.Prime 34543 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv19,pv101]) (by decide +kernel)
def pv34543 : PrimeValue := ⟨34543, pr34543⟩
private theorem pr34549 : Nat.Prime 34549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2879]) (by decide +kernel)
def pv34549 : PrimeValue := ⟨34549, pr34549⟩
private theorem pr34583 : Nat.Prime 34583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17291]) (by decide +kernel)
def pv34583 : PrimeValue := ⟨34583, pr34583⟩
private theorem pr34589 : Nat.Prime 34589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv8647]) (by decide +kernel)
def pv34589 : PrimeValue := ⟨34589, pr34589⟩
private theorem pr34591 : Nat.Prime 34591 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv1153]) (by decide +kernel)
def pv34591 : PrimeValue := ⟨34591, pr34591⟩
private theorem pr34603 : Nat.Prime 34603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv73,pv79]) (by decide +kernel)
def pv34603 : PrimeValue := ⟨34603, pr34603⟩
private theorem pr34607 : Nat.Prime 34607 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv11,pv13]) (by decide +kernel)
def pv34607 : PrimeValue := ⟨34607, pr34607⟩
private theorem pr34613 : Nat.Prime 34613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv509]) (by decide +kernel)
def pv34613 : PrimeValue := ⟨34613, pr34613⟩
private theorem pr34631 : Nat.Prime 34631 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv3463]) (by decide +kernel)
def pv34631 : PrimeValue := ⟨34631, pr34631⟩
private theorem pr34649 : Nat.Prime 34649 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv61,pv71]) (by decide +kernel)
def pv34649 : PrimeValue := ⟨34649, pr34649⟩
private theorem pr34651 : Nat.Prime 34651 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv11]) (by decide +kernel)
def pv34651 : PrimeValue := ⟨34651, pr34651⟩
private theorem pr34667 : Nat.Prime 34667 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17333]) (by decide +kernel)
def pv34667 : PrimeValue := ⟨34667, pr34667⟩
private theorem pr34673 : Nat.Prime 34673 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv197]) (by decide +kernel)
def pv34673 : PrimeValue := ⟨34673, pr34673⟩
private theorem pr34679 : Nat.Prime 34679 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv2477]) (by decide +kernel)
def pv34679 : PrimeValue := ⟨34679, pr34679⟩
private theorem pr34687 : Nat.Prime 34687 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv41,pv47]) (by decide +kernel)
def pv34687 : PrimeValue := ⟨34687, pr34687⟩
private theorem pr34693 : Nat.Prime 34693 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv7,pv59]) (by decide +kernel)
def pv34693 : PrimeValue := ⟨34693, pr34693⟩
private theorem pr34703 : Nat.Prime 34703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17351]) (by decide +kernel)
def pv34703 : PrimeValue := ⟨34703, pr34703⟩
private theorem pr34721 : Nat.Prime 34721 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv31]) (by decide +kernel)
def pv34721 : PrimeValue := ⟨34721, pr34721⟩
private theorem pr34729 : Nat.Prime 34729 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv1447]) (by decide +kernel)
def pv34729 : PrimeValue := ⟨34729, pr34729⟩
private theorem pr34739 : Nat.Prime 34739 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv11,pv1579]) (by decide +kernel)
def pv34739 : PrimeValue := ⟨34739, pr34739⟩
private theorem pr34747 : Nat.Prime 34747 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5791]) (by decide +kernel)
def pv34747 : PrimeValue := ⟨34747, pr34747⟩
private theorem pr34757 : Nat.Prime 34757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv8689]) (by decide +kernel)
def pv34757 : PrimeValue := ⟨34757, pr34757⟩
private theorem pr34759 : Nat.Prime 34759 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv1931]) (by decide +kernel)
def pv34759 : PrimeValue := ⟨34759, pr34759⟩
private theorem pr34763 : Nat.Prime 34763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv13,pv191]) (by decide +kernel)
def pv34763 : PrimeValue := ⟨34763, pr34763⟩
private theorem pr34781 : Nat.Prime 34781 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv37,pv47]) (by decide +kernel)
def pv34781 : PrimeValue := ⟨34781, pr34781⟩
private theorem pr34807 : Nat.Prime 34807 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5801]) (by decide +kernel)
def pv34807 : PrimeValue := ⟨34807, pr34807⟩
private theorem pr34819 : Nat.Prime 34819 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv829]) (by decide +kernel)
def pv34819 : PrimeValue := ⟨34819, pr34819⟩
private theorem pr34841 : Nat.Prime 34841 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv67]) (by decide +kernel)
def pv34841 : PrimeValue := ⟨34841, pr34841⟩
private theorem pr34843 : Nat.Prime 34843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5807]) (by decide +kernel)
def pv34843 : PrimeValue := ⟨34843, pr34843⟩
private theorem pr34847 : Nat.Prime 34847 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv19,pv131]) (by decide +kernel)
def pv34847 : PrimeValue := ⟨34847, pr34847⟩
private theorem pr34849 : Nat.Prime 34849 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv34849 : PrimeValue := ⟨34849, pr34849⟩
private theorem pr34871 : Nat.Prime 34871 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv317]) (by decide +kernel)
def pv34871 : PrimeValue := ⟨34871, pr34871⟩
private theorem pr34877 : Nat.Prime 34877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv8719]) (by decide +kernel)
def pv34877 : PrimeValue := ⟨34877, pr34877⟩
private theorem pr34883 : Nat.Prime 34883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv107,pv163]) (by decide +kernel)
def pv34883 : PrimeValue := ⟨34883, pr34883⟩
private theorem pr34897 : Nat.Prime 34897 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv727]) (by decide +kernel)
def pv34897 : PrimeValue := ⟨34897, pr34897⟩
private theorem pr34913 : Nat.Prime 34913 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1091]) (by decide +kernel)
def pv34913 : PrimeValue := ⟨34913, pr34913⟩
private theorem pr34919 : Nat.Prime 34919 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv13,pv17,pv79]) (by decide +kernel)
def pv34919 : PrimeValue := ⟨34919, pr34919⟩
private theorem pr34939 : Nat.Prime 34939 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv647]) (by decide +kernel)
def pv34939 : PrimeValue := ⟨34939, pr34939⟩
private theorem pr34949 : Nat.Prime 34949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv8737]) (by decide +kernel)
def pv34949 : PrimeValue := ⟨34949, pr34949⟩
private theorem pr34961 : Nat.Prime 34961 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv19,pv23]) (by decide +kernel)
def pv34961 : PrimeValue := ⟨34961, pr34961⟩
private theorem pr34963 : Nat.Prime 34963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5827]) (by decide +kernel)
def pv34963 : PrimeValue := ⟨34963, pr34963⟩
private theorem pr34981 : Nat.Prime 34981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv53]) (by decide +kernel)
def pv34981 : PrimeValue := ⟨34981, pr34981⟩
private theorem pr35023 : Nat.Prime 35023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv449]) (by decide +kernel)
def pv35023 : PrimeValue := ⟨35023, pr35023⟩
private theorem pr35027 : Nat.Prime 35027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv83,pv211]) (by decide +kernel)
def pv35027 : PrimeValue := ⟨35027, pr35027⟩
private theorem pr35051 : Nat.Prime 35051 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv701]) (by decide +kernel)
def pv35051 : PrimeValue := ⟨35051, pr35051⟩
private theorem pr35053 : Nat.Prime 35053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv127]) (by decide +kernel)
def pv35053 : PrimeValue := ⟨35053, pr35053⟩
private theorem pr35059 : Nat.Prime 35059 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5843]) (by decide +kernel)
def pv35059 : PrimeValue := ⟨35059, pr35059⟩
private theorem pr35069 : Nat.Prime 35069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv797]) (by decide +kernel)
def pv35069 : PrimeValue := ⟨35069, pr35069⟩
private theorem pr35081 : Nat.Prime 35081 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv877]) (by decide +kernel)
def pv35081 : PrimeValue := ⟨35081, pr35081⟩
private theorem pr35083 : Nat.Prime 35083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1949]) (by decide +kernel)
def pv35083 : PrimeValue := ⟨35083, pr35083⟩
private theorem pr35089 : Nat.Prime 35089 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv17,pv43]) (by decide +kernel)
def pv35089 : PrimeValue := ⟨35089, pr35089⟩
private theorem pr35099 : Nat.Prime 35099 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv23,pv109]) (by decide +kernel)
def pv35099 : PrimeValue := ⟨35099, pr35099⟩
private theorem pr35107 : Nat.Prime 35107 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5851]) (by decide +kernel)
def pv35107 : PrimeValue := ⟨35107, pr35107⟩
private theorem pr35111 : Nat.Prime 35111 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv3511]) (by decide +kernel)
def pv35111 : PrimeValue := ⟨35111, pr35111⟩
private theorem pr35117 : Nat.Prime 35117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv8779]) (by decide +kernel)
def pv35117 : PrimeValue := ⟨35117, pr35117⟩
private theorem pr35129 : Nat.Prime 35129 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv4391]) (by decide +kernel)
def pv35129 : PrimeValue := ⟨35129, pr35129⟩
private theorem pr35141 : Nat.Prime 35141 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv251]) (by decide +kernel)
def pv35141 : PrimeValue := ⟨35141, pr35141⟩
private theorem pr35149 : Nat.Prime 35149 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv101]) (by decide +kernel)
def pv35149 : PrimeValue := ⟨35149, pr35149⟩
private theorem pr35153 : Nat.Prime 35153 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13]) (by decide +kernel)
def pv35153 : PrimeValue := ⟨35153, pr35153⟩
private theorem pr35159 : Nat.Prime 35159 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv17579]) (by decide +kernel)
def pv35159 : PrimeValue := ⟨35159, pr35159⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
