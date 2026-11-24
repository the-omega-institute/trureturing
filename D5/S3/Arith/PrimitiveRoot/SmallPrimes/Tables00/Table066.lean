/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table066
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table066.pv201493
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table009
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table014
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table038

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr201493 : Nat.Prime 201493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv193]) (by decide +kernel)
def pv201493 : PrimeValue := ⟨201493, pr201493⟩
private theorem pr201577 : Nat.Prime 201577 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv37,pv227]) (by decide +kernel)
def pv201577 : PrimeValue := ⟨201577, pr201577⟩
private theorem pr201581 : Nat.Prime 201581 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv10079]) (by decide +kernel)
def pv201581 : PrimeValue := ⟨201581, pr201581⟩
private theorem pr201589 : Nat.Prime 201589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv107,pv157]) (by decide +kernel)
def pv201589 : PrimeValue := ⟨201589, pr201589⟩
private theorem pr201599 : Nat.Prime 201599 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv100799]) (by decide +kernel)
def pv201599 : PrimeValue := ⟨201599, pr201599⟩
private theorem pr201623 : Nat.Prime 201623 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv100811]) (by decide +kernel)
def pv201623 : PrimeValue := ⟨201623, pr201623⟩
private theorem pr201629 : Nat.Prime 201629 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv19,pv379]) (by decide +kernel)
def pv201629 : PrimeValue := ⟨201629, pr201629⟩
private theorem pr201653 : Nat.Prime 201653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv4583]) (by decide +kernel)
def pv201653 : PrimeValue := ⟨201653, pr201653⟩
private theorem pr201667 : Nat.Prime 201667 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv29,pv61]) (by decide +kernel)
def pv201667 : PrimeValue := ⟨201667, pr201667⟩
private theorem pr201673 : Nat.Prime 201673 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv2801]) (by decide +kernel)
def pv201673 : PrimeValue := ⟨201673, pr201673⟩
private theorem pr201701 : Nat.Prime 201701 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv2017]) (by decide +kernel)
def pv201701 : PrimeValue := ⟨201701, pr201701⟩
private theorem pr201731 : Nat.Prime 201731 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv20173]) (by decide +kernel)
def pv201731 : PrimeValue := ⟨201731, pr201731⟩
private theorem pr201743 : Nat.Prime 201743 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv19,pv5309]) (by decide +kernel)
def pv201743 : PrimeValue := ⟨201743, pr201743⟩
private theorem pr201769 : Nat.Prime 201769 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv7,pv1201]) (by decide +kernel)
def pv201769 : PrimeValue := ⟨201769, pr201769⟩
private theorem pr201781 : Nat.Prime 201781 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv19,pv59]) (by decide +kernel)
def pv201781 : PrimeValue := ⟨201781, pr201781⟩
private theorem pr201787 : Nat.Prime 201787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv199]) (by decide +kernel)
def pv201787 : PrimeValue := ⟨201787, pr201787⟩
private theorem pr201791 : Nat.Prime 201791 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv17,pv1187]) (by decide +kernel)
def pv201791 : PrimeValue := ⟨201791, pr201791⟩
private theorem pr201797 : Nat.Prime 201797 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv7207]) (by decide +kernel)
def pv201797 : PrimeValue := ⟨201797, pr201797⟩
private theorem pr201823 : Nat.Prime 201823 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv33637]) (by decide +kernel)
def pv201823 : PrimeValue := ⟨201823, pr201823⟩
private theorem pr201833 : Nat.Prime 201833 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv25229]) (by decide +kernel)
def pv201833 : PrimeValue := ⟨201833, pr201833⟩
private theorem pr201847 : Nat.Prime 201847 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv33641]) (by decide +kernel)
def pv201847 : PrimeValue := ⟨201847, pr201847⟩
private theorem pr201881 : Nat.Prime 201881 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv7,pv103]) (by decide +kernel)
def pv201881 : PrimeValue := ⟨201881, pr201881⟩
private theorem pr201893 : Nat.Prime 201893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv2969]) (by decide +kernel)
def pv201893 : PrimeValue := ⟨201893, pr201893⟩
private theorem pr201907 : Nat.Prime 201907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv3739]) (by decide +kernel)
def pv201907 : PrimeValue := ⟨201907, pr201907⟩
private theorem pr201919 : Nat.Prime 201919 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv73,pv461]) (by decide +kernel)
def pv201919 : PrimeValue := ⟨201919, pr201919⟩
private theorem pr201937 : Nat.Prime 201937 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv601]) (by decide +kernel)
def pv201937 : PrimeValue := ⟨201937, pr201937⟩
private theorem pr201953 : Nat.Prime 201953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv6311]) (by decide +kernel)
def pv201953 : PrimeValue := ⟨201953, pr201953⟩
private theorem pr201961 : Nat.Prime 201961 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv11,pv17]) (by decide +kernel)
def pv201961 : PrimeValue := ⟨201961, pr201961⟩
private theorem pr201997 : Nat.Prime 201997 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv31,pv181]) (by decide +kernel)
def pv201997 : PrimeValue := ⟨201997, pr201997⟩
private theorem pr202001 : Nat.Prime 202001 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv101]) (by decide +kernel)
def pv202001 : PrimeValue := ⟨202001, pr202001⟩
private theorem pr202031 : Nat.Prime 202031 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv89,pv227]) (by decide +kernel)
def pv202031 : PrimeValue := ⟨202031, pr202031⟩
private theorem pr202049 : Nat.Prime 202049 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv7,pv11,pv41]) (by decide +kernel)
def pv202049 : PrimeValue := ⟨202049, pr202049⟩
private theorem pr202061 : Nat.Prime 202061 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv10103]) (by decide +kernel)
def pv202061 : PrimeValue := ⟨202061, pr202061⟩
private theorem pr202067 : Nat.Prime 202067 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv71,pv1423]) (by decide +kernel)
def pv202067 : PrimeValue := ⟨202067, pr202067⟩
private theorem pr202087 : Nat.Prime 202087 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv103,pv109]) (by decide +kernel)
def pv202087 : PrimeValue := ⟨202087, pr202087⟩
private theorem pr202109 : Nat.Prime 202109 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv50527]) (by decide +kernel)
def pv202109 : PrimeValue := ⟨202109, pr202109⟩
private theorem pr202121 : Nat.Prime 202121 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv31,pv163]) (by decide +kernel)
def pv202121 : PrimeValue := ⟨202121, pr202121⟩
private theorem pr202129 : Nat.Prime 202129 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv4211]) (by decide +kernel)
def pv202129 : PrimeValue := ⟨202129, pr202129⟩
private theorem pr202183 : Nat.Prime 202183 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv31,pv1087]) (by decide +kernel)
def pv202183 : PrimeValue := ⟨202183, pr202183⟩
private theorem pr202201 : Nat.Prime 202201 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv337]) (by decide +kernel)
def pv202201 : PrimeValue := ⟨202201, pr202201⟩
private theorem pr202219 : Nat.Prime 202219 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv33703]) (by decide +kernel)
def pv202219 : PrimeValue := ⟨202219, pr202219⟩
private theorem pr202231 : Nat.Prime 202231 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv107]) (by decide +kernel)
def pv202231 : PrimeValue := ⟨202231, pr202231⟩
private theorem pr202243 : Nat.Prime 202243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv911]) (by decide +kernel)
def pv202243 : PrimeValue := ⟨202243, pr202243⟩
private theorem pr202277 : Nat.Prime 202277 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv829]) (by decide +kernel)
def pv202277 : PrimeValue := ⟨202277, pr202277⟩
private theorem pr202291 : Nat.Prime 202291 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv613]) (by decide +kernel)
def pv202291 : PrimeValue := ⟨202291, pr202291⟩
private theorem pr202327 : Nat.Prime 202327 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv33721]) (by decide +kernel)
def pv202327 : PrimeValue := ⟨202327, pr202327⟩
private theorem pr202339 : Nat.Prime 202339 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1249]) (by decide +kernel)
def pv202339 : PrimeValue := ⟨202339, pr202339⟩
private theorem pr202343 : Nat.Prime 202343 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv97,pv149]) (by decide +kernel)
def pv202343 : PrimeValue := ⟨202343, pr202343⟩
private theorem pr202361 : Nat.Prime 202361 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv5059]) (by decide +kernel)
def pv202361 : PrimeValue := ⟨202361, pr202361⟩
private theorem pr202381 : Nat.Prime 202381 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv3373]) (by decide +kernel)
def pv202381 : PrimeValue := ⟨202381, pr202381⟩
private theorem pr202403 : Nat.Prime 202403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv5953]) (by decide +kernel)
def pv202403 : PrimeValue := ⟨202403, pr202403⟩
private theorem pr202409 : Nat.Prime 202409 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv25301]) (by decide +kernel)
def pv202409 : PrimeValue := ⟨202409, pr202409⟩
private theorem pr202441 : Nat.Prime 202441 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv241]) (by decide +kernel)
def pv202441 : PrimeValue := ⟨202441, pr202441⟩
private theorem pr202471 : Nat.Prime 202471 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv17,pv397]) (by decide +kernel)
def pv202471 : PrimeValue := ⟨202471, pr202471⟩
private theorem pr202481 : Nat.Prime 202481 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv2531]) (by decide +kernel)
def pv202481 : PrimeValue := ⟨202481, pr202481⟩
private theorem pr202493 : Nat.Prime 202493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv31,pv71]) (by decide +kernel)
def pv202493 : PrimeValue := ⟨202493, pr202493⟩
private theorem pr202529 : Nat.Prime 202529 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv6329]) (by decide +kernel)
def pv202529 : PrimeValue := ⟨202529, pr202529⟩
private theorem pr202567 : Nat.Prime 202567 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv53]) (by decide +kernel)
def pv202567 : PrimeValue := ⟨202567, pr202567⟩
private theorem pr202577 : Nat.Prime 202577 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv1151]) (by decide +kernel)
def pv202577 : PrimeValue := ⟨202577, pr202577⟩
private theorem pr202613 : Nat.Prime 202613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37]) (by decide +kernel)
def pv202613 : PrimeValue := ⟨202613, pr202613⟩
private theorem pr202621 : Nat.Prime 202621 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv11,pv307]) (by decide +kernel)
def pv202621 : PrimeValue := ⟨202621, pr202621⟩
private theorem pr202627 : Nat.Prime 202627 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11257]) (by decide +kernel)
def pv202627 : PrimeValue := ⟨202627, pr202627⟩
private theorem pr202637 : Nat.Prime 202637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv7237]) (by decide +kernel)
def pv202637 : PrimeValue := ⟨202637, pr202637⟩
private theorem pr202639 : Nat.Prime 202639 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv33773]) (by decide +kernel)
def pv202639 : PrimeValue := ⟨202639, pr202639⟩
private theorem pr202661 : Nat.Prime 202661 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv10133]) (by decide +kernel)
def pv202661 : PrimeValue := ⟨202661, pr202661⟩
private theorem pr202667 : Nat.Prime 202667 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv101333]) (by decide +kernel)
def pv202667 : PrimeValue := ⟨202667, pr202667⟩
private theorem pr202693 : Nat.Prime 202693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv19,pv127]) (by decide +kernel)
def pv202693 : PrimeValue := ⟨202693, pr202693⟩
private theorem pr202717 : Nat.Prime 202717 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv1877]) (by decide +kernel)
def pv202717 : PrimeValue := ⟨202717, pr202717⟩
private theorem pr202747 : Nat.Prime 202747 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv33791]) (by decide +kernel)
def pv202747 : PrimeValue := ⟨202747, pr202747⟩
private theorem pr202751 : Nat.Prime 202751 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv811]) (by decide +kernel)
def pv202751 : PrimeValue := ⟨202751, pr202751⟩
private theorem pr202753 : Nat.Prime 202753 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv202753 : PrimeValue := ⟨202753, pr202753⟩
private theorem pr202757 : Nat.Prime 202757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv173,pv293]) (by decide +kernel)
def pv202757 : PrimeValue := ⟨202757, pr202757⟩
private theorem pr202799 : Nat.Prime 202799 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv101399]) (by decide +kernel)
def pv202799 : PrimeValue := ⟨202799, pr202799⟩
private theorem pr202817 : Nat.Prime 202817 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3169]) (by decide +kernel)
def pv202817 : PrimeValue := ⟨202817, pr202817⟩
private theorem pr202823 : Nat.Prime 202823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv101411]) (by decide +kernel)
def pv202823 : PrimeValue := ⟨202823, pr202823⟩
private theorem pr202841 : Nat.Prime 202841 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv11,pv461]) (by decide +kernel)
def pv202841 : PrimeValue := ⟨202841, pr202841⟩
private theorem pr202859 : Nat.Prime 202859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv101429]) (by decide +kernel)
def pv202859 : PrimeValue := ⟨202859, pr202859⟩
private theorem pr202889 : Nat.Prime 202889 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv3623]) (by decide +kernel)
def pv202889 : PrimeValue := ⟨202889, pr202889⟩
private theorem pr202907 : Nat.Prime 202907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv23,pv401]) (by decide +kernel)
def pv202907 : PrimeValue := ⟨202907, pr202907⟩
private theorem pr202921 : Nat.Prime 202921 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv19,pv89]) (by decide +kernel)
def pv202921 : PrimeValue := ⟨202921, pr202921⟩
private theorem pr202931 : Nat.Prime 202931 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv13,pv223]) (by decide +kernel)
def pv202931 : PrimeValue := ⟨202931, pr202931⟩
private theorem pr202933 : Nat.Prime 202933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1879]) (by decide +kernel)
def pv202933 : PrimeValue := ⟨202933, pr202933⟩
private theorem pr202949 : Nat.Prime 202949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv113,pv449]) (by decide +kernel)
def pv202949 : PrimeValue := ⟨202949, pr202949⟩
private theorem pr202973 : Nat.Prime 202973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv659]) (by decide +kernel)
def pv202973 : PrimeValue := ⟨202973, pr202973⟩
private theorem pr202981 : Nat.Prime 202981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv199]) (by decide +kernel)
def pv202981 : PrimeValue := ⟨202981, pr202981⟩
private theorem pr202987 : Nat.Prime 202987 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv179]) (by decide +kernel)
def pv202987 : PrimeValue := ⟨202987, pr202987⟩
private theorem pr202999 : Nat.Prime 202999 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv1471]) (by decide +kernel)
def pv202999 : PrimeValue := ⟨202999, pr202999⟩
private theorem pr203023 : Nat.Prime 203023 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11279]) (by decide +kernel)
def pv203023 : PrimeValue := ⟨203023, pr203023⟩
private theorem pr203051 : Nat.Prime 203051 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv31,pv131]) (by decide +kernel)
def pv203051 : PrimeValue := ⟨203051, pr203051⟩
private theorem pr203141 : Nat.Prime 203141 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv1451]) (by decide +kernel)
def pv203141 : PrimeValue := ⟨203141, pr203141⟩
private theorem pr203173 : Nat.Prime 203173 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv16931]) (by decide +kernel)
def pv203173 : PrimeValue := ⟨203173, pr203173⟩
private theorem pr203209 : Nat.Prime 203209 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv8467]) (by decide +kernel)
def pv203209 : PrimeValue := ⟨203209, pr203209⟩
private theorem pr203213 : Nat.Prime 203213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv101,pv503]) (by decide +kernel)
def pv203213 : PrimeValue := ⟨203213, pr203213⟩
private theorem pr203227 : Nat.Prime 203227 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv33871]) (by decide +kernel)
def pv203227 : PrimeValue := ⟨203227, pr203227⟩
private theorem pr203233 : Nat.Prime 203233 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv29,pv73]) (by decide +kernel)
def pv203233 : PrimeValue := ⟨203233, pr203233⟩
private theorem pr203249 : Nat.Prime 203249 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv12703]) (by decide +kernel)
def pv203249 : PrimeValue := ⟨203249, pr203249⟩
private theorem pr203279 : Nat.Prime 203279 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv37,pv41,pv67]) (by decide +kernel)
def pv203279 : PrimeValue := ⟨203279, pr203279⟩
private theorem pr203293 : Nat.Prime 203293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5647]) (by decide +kernel)
def pv203293 : PrimeValue := ⟨203293, pr203293⟩
private theorem pr203311 : Nat.Prime 203311 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv251]) (by decide +kernel)
def pv203311 : PrimeValue := ⟨203311, pr203311⟩
private theorem pr203317 : Nat.Prime 203317 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv16943]) (by decide +kernel)
def pv203317 : PrimeValue := ⟨203317, pr203317⟩
private theorem pr203339 : Nat.Prime 203339 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv5351]) (by decide +kernel)
def pv203339 : PrimeValue := ⟨203339, pr203339⟩
private theorem pr203351 : Nat.Prime 203351 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv83]) (by decide +kernel)
def pv203351 : PrimeValue := ⟨203351, pr203351⟩
private theorem pr203353 : Nat.Prime 203353 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv37,pv229]) (by decide +kernel)
def pv203353 : PrimeValue := ⟨203353, pr203353⟩
private theorem pr203363 : Nat.Prime 203363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv101681]) (by decide +kernel)
def pv203363 : PrimeValue := ⟨203363, pr203363⟩
private theorem pr203381 : Nat.Prime 203381 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv10169]) (by decide +kernel)
def pv203381 : PrimeValue := ⟨203381, pr203381⟩
private theorem pr203417 : Nat.Prime 203417 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv47,pv541]) (by decide +kernel)
def pv203417 : PrimeValue := ⟨203417, pr203417⟩
private theorem pr203419 : Nat.Prime 203419 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv3767]) (by decide +kernel)
def pv203419 : PrimeValue := ⟨203419, pr203419⟩
private theorem pr203429 : Nat.Prime 203429 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv50857]) (by decide +kernel)
def pv203429 : PrimeValue := ⟨203429, pr203429⟩
private theorem pr203431 : Nat.Prime 203431 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv6781]) (by decide +kernel)
def pv203431 : PrimeValue := ⟨203431, pr203431⟩
private theorem pr203449 : Nat.Prime 203449 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv173]) (by decide +kernel)
def pv203449 : PrimeValue := ⟨203449, pr203449⟩
private theorem pr203461 : Nat.Prime 203461 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv3391]) (by decide +kernel)
def pv203461 : PrimeValue := ⟨203461, pr203461⟩
private theorem pr203549 : Nat.Prime 203549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv151,pv337]) (by decide +kernel)
def pv203549 : PrimeValue := ⟨203549, pr203549⟩
private theorem pr203563 : Nat.Prime 203563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv43,pv263]) (by decide +kernel)
def pv203563 : PrimeValue := ⟨203563, pr203563⟩
private theorem pr203579 : Nat.Prime 203579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv101789]) (by decide +kernel)
def pv203579 : PrimeValue := ⟨203579, pr203579⟩
private theorem pr203591 : Nat.Prime 203591 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv20359]) (by decide +kernel)
def pv203591 : PrimeValue := ⟨203591, pr203591⟩
private theorem pr203617 : Nat.Prime 203617 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv101]) (by decide +kernel)
def pv203617 : PrimeValue := ⟨203617, pr203617⟩
private theorem pr203653 : Nat.Prime 203653 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5657]) (by decide +kernel)
def pv203653 : PrimeValue := ⟨203653, pr203653⟩
private theorem pr203713 : Nat.Prime 203713 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1061]) (by decide +kernel)
def pv203713 : PrimeValue := ⟨203713, pr203713⟩
private theorem pr203761 : Nat.Prime 203761 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv283]) (by decide +kernel)
def pv203761 : PrimeValue := ⟨203761, pr203761⟩
private theorem pr203767 : Nat.Prime 203767 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv33961]) (by decide +kernel)
def pv203767 : PrimeValue := ⟨203767, pr203767⟩
private theorem pr203771 : Nat.Prime 203771 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv41,pv71]) (by decide +kernel)
def pv203771 : PrimeValue := ⟨203771, pr203771⟩
private theorem pr203773 : Nat.Prime 203773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv16981]) (by decide +kernel)
def pv203773 : PrimeValue := ⟨203773, pr203773⟩
private theorem pr203789 : Nat.Prime 203789 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv3919]) (by decide +kernel)
def pv203789 : PrimeValue := ⟨203789, pr203789⟩
private theorem pr203807 : Nat.Prime 203807 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv181,pv563]) (by decide +kernel)
def pv203807 : PrimeValue := ⟨203807, pr203807⟩
private theorem pr203843 : Nat.Prime 203843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv101921]) (by decide +kernel)
def pv203843 : PrimeValue := ⟨203843, pr203843⟩
private theorem pr203873 : Nat.Prime 203873 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv277]) (by decide +kernel)
def pv203873 : PrimeValue := ⟨203873, pr203873⟩
private theorem pr203897 : Nat.Prime 203897 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv11,pv331]) (by decide +kernel)
def pv203897 : PrimeValue := ⟨203897, pr203897⟩
private theorem pr203921 : Nat.Prime 203921 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv2549]) (by decide +kernel)
def pv203921 : PrimeValue := ⟨203921, pr203921⟩
private theorem pr203947 : Nat.Prime 203947 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv1789]) (by decide +kernel)
def pv203947 : PrimeValue := ⟨203947, pr203947⟩
private theorem pr203953 : Nat.Prime 203953 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv3,pv7,pv607]) (by decide +kernel)
def pv203953 : PrimeValue := ⟨203953, pr203953⟩
private theorem pr203977 : Nat.Prime 203977 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2833]) (by decide +kernel)
def pv203977 : PrimeValue := ⟨203977, pr203977⟩
private theorem pr204013 : Nat.Prime 204013 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1889]) (by decide +kernel)
def pv204013 : PrimeValue := ⟨204013, pr204013⟩
private theorem pr204019 : Nat.Prime 204019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv919]) (by decide +kernel)
def pv204019 : PrimeValue := ⟨204019, pr204019⟩
private theorem pr204059 : Nat.Prime 204059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv257,pv397]) (by decide +kernel)
def pv204059 : PrimeValue := ⟨204059, pr204059⟩
private theorem pr204067 : Nat.Prime 204067 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv3779]) (by decide +kernel)
def pv204067 : PrimeValue := ⟨204067, pr204067⟩
private theorem pr204101 : Nat.Prime 204101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv157]) (by decide +kernel)
def pv204101 : PrimeValue := ⟨204101, pr204101⟩
private theorem pr204137 : Nat.Prime 204137 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv19,pv79]) (by decide +kernel)
def pv204137 : PrimeValue := ⟨204137, pr204137⟩
private theorem pr204143 : Nat.Prime 204143 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv102071]) (by decide +kernel)
def pv204143 : PrimeValue := ⟨204143, pr204143⟩
private theorem pr204151 : Nat.Prime 204151 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv1361]) (by decide +kernel)
def pv204151 : PrimeValue := ⟨204151, pr204151⟩
private theorem pr204161 : Nat.Prime 204161 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv29]) (by decide +kernel)
def pv204161 : PrimeValue := ⟨204161, pr204161⟩
private theorem pr204163 : Nat.Prime 204163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv4861]) (by decide +kernel)
def pv204163 : PrimeValue := ⟨204163, pr204163⟩
private theorem pr204173 : Nat.Prime 204173 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv51043]) (by decide +kernel)
def pv204173 : PrimeValue := ⟨204173, pr204173⟩
private theorem pr204251 : Nat.Prime 204251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19,pv43]) (by decide +kernel)
def pv204251 : PrimeValue := ⟨204251, pr204251⟩
private theorem pr204299 : Nat.Prime 204299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv102149]) (by decide +kernel)
def pv204299 : PrimeValue := ⟨204299, pr204299⟩
private theorem pr204301 : Nat.Prime 204301 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv227]) (by decide +kernel)
def pv204301 : PrimeValue := ⟨204301, pr204301⟩
private theorem pr204311 : Nat.Prime 204311 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv20431]) (by decide +kernel)
def pv204311 : PrimeValue := ⟨204311, pr204311⟩
private theorem pr204319 : Nat.Prime 204319 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv11351]) (by decide +kernel)
def pv204319 : PrimeValue := ⟨204319, pr204319⟩
private theorem pr204329 : Nat.Prime 204329 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv25541]) (by decide +kernel)
def pv204329 : PrimeValue := ⟨204329, pr204329⟩
private theorem pr204331 : Nat.Prime 204331 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv139]) (by decide +kernel)
def pv204331 : PrimeValue := ⟨204331, pr204331⟩
private theorem pr204359 : Nat.Prime 204359 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv11,pv1327]) (by decide +kernel)
def pv204359 : PrimeValue := ⟨204359, pr204359⟩
private theorem pr204371 : Nat.Prime 204371 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv107,pv191]) (by decide +kernel)
def pv204371 : PrimeValue := ⟨204371, pr204371⟩
private theorem pr204377 : Nat.Prime 204377 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv59,pv433]) (by decide +kernel)
def pv204377 : PrimeValue := ⟨204377, pr204377⟩
private theorem pr204397 : Nat.Prime 204397 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17033]) (by decide +kernel)
def pv204397 : PrimeValue := ⟨204397, pr204397⟩
private theorem pr204427 : Nat.Prime 204427 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv41,pv277]) (by decide +kernel)
def pv204427 : PrimeValue := ⟨204427, pr204427⟩
private theorem pr204431 : Nat.Prime 204431 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv20443]) (by decide +kernel)
def pv204431 : PrimeValue := ⟨204431, pr204431⟩
private theorem pr204437 : Nat.Prime 204437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv51109]) (by decide +kernel)
def pv204437 : PrimeValue := ⟨204437, pr204437⟩
private theorem pr204439 : Nat.Prime 204439 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv2621]) (by decide +kernel)
def pv204439 : PrimeValue := ⟨204439, pr204439⟩
private theorem pr204443 : Nat.Prime 204443 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv17,pv859]) (by decide +kernel)
def pv204443 : PrimeValue := ⟨204443, pr204443⟩
private theorem pr204461 : Nat.Prime 204461 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv10223]) (by decide +kernel)
def pv204461 : PrimeValue := ⟨204461, pr204461⟩
private theorem pr204509 : Nat.Prime 204509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv41,pv43]) (by decide +kernel)
def pv204509 : PrimeValue := ⟨204509, pr204509⟩
private theorem pr204517 : Nat.Prime 204517 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv19,pv23]) (by decide +kernel)
def pv204517 : PrimeValue := ⟨204517, pr204517⟩
private theorem pr204521 : Nat.Prime 204521 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv5113]) (by decide +kernel)
def pv204521 : PrimeValue := ⟨204521, pr204521⟩
private theorem pr204557 : Nat.Prime 204557 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv4649]) (by decide +kernel)
def pv204557 : PrimeValue := ⟨204557, pr204557⟩
private theorem pr204563 : Nat.Prime 204563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv4447]) (by decide +kernel)
def pv204563 : PrimeValue := ⟨204563, pr204563⟩
private theorem pr204583 : Nat.Prime 204583 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv4871]) (by decide +kernel)
def pv204583 : PrimeValue := ⟨204583, pr204583⟩
private theorem pr204587 : Nat.Prime 204587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv102293]) (by decide +kernel)
def pv204587 : PrimeValue := ⟨204587, pr204587⟩
private theorem pr204601 : Nat.Prime 204601 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv3,pv5,pv11,pv31]) (by decide +kernel)
def pv204601 : PrimeValue := ⟨204601, pr204601⟩
private theorem pr204613 : Nat.Prime 204613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv59]) (by decide +kernel)
def pv204613 : PrimeValue := ⟨204613, pr204613⟩
private theorem pr204623 : Nat.Prime 204623 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv71,pv131]) (by decide +kernel)
def pv204623 : PrimeValue := ⟨204623, pr204623⟩
private theorem pr204641 : Nat.Prime 204641 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv1279]) (by decide +kernel)
def pv204641 : PrimeValue := ⟨204641, pr204641⟩
private theorem pr204679 : Nat.Prime 204679 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv83,pv137]) (by decide +kernel)
def pv204679 : PrimeValue := ⟨204679, pr204679⟩
private theorem pr204707 : Nat.Prime 204707 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv5387]) (by decide +kernel)
def pv204707 : PrimeValue := ⟨204707, pr204707⟩
private theorem pr204733 : Nat.Prime 204733 :=
  checkPrime_prime (q := pv67) (ls := [pv2,pv3,pv11,pv47]) (by decide +kernel)
def pv204733 : PrimeValue := ⟨204733, pr204733⟩
private theorem pr204749 : Nat.Prime 204749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv3011]) (by decide +kernel)
def pv204749 : PrimeValue := ⟨204749, pr204749⟩
private theorem pr204781 : Nat.Prime 204781 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv3413]) (by decide +kernel)
def pv204781 : PrimeValue := ⟨204781, pr204781⟩
private theorem pr204793 : Nat.Prime 204793 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv23,pv53]) (by decide +kernel)
def pv204793 : PrimeValue := ⟨204793, pr204793⟩
private theorem pr204797 : Nat.Prime 204797 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv51199]) (by decide +kernel)
def pv204797 : PrimeValue := ⟨204797, pr204797⟩
private theorem pr204803 : Nat.Prime 204803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv7877]) (by decide +kernel)
def pv204803 : PrimeValue := ⟨204803, pr204803⟩
private theorem pr204821 : Nat.Prime 204821 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv19]) (by decide +kernel)
def pv204821 : PrimeValue := ⟨204821, pr204821⟩
private theorem pr204859 : Nat.Prime 204859 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv19,pv599]) (by decide +kernel)
def pv204859 : PrimeValue := ⟨204859, pr204859⟩
private theorem pr204871 : Nat.Prime 204871 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv6829]) (by decide +kernel)
def pv204871 : PrimeValue := ⟨204871, pr204871⟩
private theorem pr204887 : Nat.Prime 204887 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv67,pv139]) (by decide +kernel)
def pv204887 : PrimeValue := ⟨204887, pr204887⟩
private theorem pr204913 : Nat.Prime 204913 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv1423]) (by decide +kernel)
def pv204913 : PrimeValue := ⟨204913, pr204913⟩
private theorem pr204947 : Nat.Prime 204947 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv14639]) (by decide +kernel)
def pv204947 : PrimeValue := ⟨204947, pr204947⟩
private theorem pr204979 : Nat.Prime 204979 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv127,pv269]) (by decide +kernel)
def pv204979 : PrimeValue := ⟨204979, pr204979⟩
private theorem pr204983 : Nat.Prime 204983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv113,pv907]) (by decide +kernel)
def pv204983 : PrimeValue := ⟨204983, pr204983⟩
private theorem pr205019 : Nat.Prime 205019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv9319]) (by decide +kernel)
def pv205019 : PrimeValue := ⟨205019, pr205019⟩
private theorem pr205031 : Nat.Prime 205031 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv7,pv29,pv101]) (by decide +kernel)
def pv205031 : PrimeValue := ⟨205031, pr205031⟩
private theorem pr205033 : Nat.Prime 205033 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv8543]) (by decide +kernel)
def pv205033 : PrimeValue := ⟨205033, pr205033⟩
private theorem pr205043 : Nat.Prime 205043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv157,pv653]) (by decide +kernel)
def pv205043 : PrimeValue := ⟨205043, pr205043⟩
private theorem pr205063 : Nat.Prime 205063 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv13,pv239]) (by decide +kernel)
def pv205063 : PrimeValue := ⟨205063, pr205063⟩
private theorem pr205081 : Nat.Prime 205081 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv1709]) (by decide +kernel)
def pv205081 : PrimeValue := ⟨205081, pr205081⟩
private theorem pr205097 : Nat.Prime 205097 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv827]) (by decide +kernel)
def pv205097 : PrimeValue := ⟨205097, pr205097⟩
private theorem pr205103 : Nat.Prime 205103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv102551]) (by decide +kernel)
def pv205103 : PrimeValue := ⟨205103, pr205103⟩
private theorem pr205111 : Nat.Prime 205111 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv43,pv53]) (by decide +kernel)
def pv205111 : PrimeValue := ⟨205111, pr205111⟩
private theorem pr205151 : Nat.Prime 205151 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv373]) (by decide +kernel)
def pv205151 : PrimeValue := ⟨205151, pr205151⟩
private theorem pr205201 : Nat.Prime 205201 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv205201 : PrimeValue := ⟨205201, pr205201⟩
private theorem pr205211 : Nat.Prime 205211 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv20521]) (by decide +kernel)
def pv205211 : PrimeValue := ⟨205211, pr205211⟩
private theorem pr205213 : Nat.Prime 205213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv349]) (by decide +kernel)
def pv205213 : PrimeValue := ⟨205213, pr205213⟩
private theorem pr205223 : Nat.Prime 205223 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv102611]) (by decide +kernel)
def pv205223 : PrimeValue := ⟨205223, pr205223⟩
private theorem pr205237 : Nat.Prime 205237 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv5701]) (by decide +kernel)
def pv205237 : PrimeValue := ⟨205237, pr205237⟩
private theorem pr205253 : Nat.Prime 205253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv97]) (by decide +kernel)
def pv205253 : PrimeValue := ⟨205253, pr205253⟩
private theorem pr205267 : Nat.Prime 205267 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv34211]) (by decide +kernel)
def pv205267 : PrimeValue := ⟨205267, pr205267⟩
private theorem pr205297 : Nat.Prime 205297 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv13,pv47]) (by decide +kernel)
def pv205297 : PrimeValue := ⟨205297, pr205297⟩
private theorem pr205307 : Nat.Prime 205307 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv102653]) (by decide +kernel)
def pv205307 : PrimeValue := ⟨205307, pr205307⟩
private theorem pr205319 : Nat.Prime 205319 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv251,pv409]) (by decide +kernel)
def pv205319 : PrimeValue := ⟨205319, pr205319⟩
private theorem pr205357 : Nat.Prime 205357 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv109,pv157]) (by decide +kernel)
def pv205357 : PrimeValue := ⟨205357, pr205357⟩
private theorem pr205391 : Nat.Prime 205391 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv19,pv23,pv47]) (by decide +kernel)
def pv205391 : PrimeValue := ⟨205391, pr205391⟩
private theorem pr205399 : Nat.Prime 205399 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11411]) (by decide +kernel)
def pv205399 : PrimeValue := ⟨205399, pr205399⟩
private theorem pr205421 : Nat.Prime 205421 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv10271]) (by decide +kernel)
def pv205421 : PrimeValue := ⟨205421, pr205421⟩
private theorem pr205423 : Nat.Prime 205423 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv67,pv73]) (by decide +kernel)
def pv205423 : PrimeValue := ⟨205423, pr205423⟩
private theorem pr205427 : Nat.Prime 205427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv7901]) (by decide +kernel)
def pv205427 : PrimeValue := ⟨205427, pr205427⟩
private theorem pr205453 : Nat.Prime 205453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv439]) (by decide +kernel)
def pv205453 : PrimeValue := ⟨205453, pr205453⟩
private theorem pr205463 : Nat.Prime 205463 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv6043]) (by decide +kernel)
def pv205463 : PrimeValue := ⟨205463, pr205463⟩
private theorem pr205477 : Nat.Prime 205477 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17123]) (by decide +kernel)
def pv205477 : PrimeValue := ⟨205477, pr205477⟩
private theorem pr205493 : Nat.Prime 205493 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv41,pv179]) (by decide +kernel)
def pv205493 : PrimeValue := ⟨205493, pr205493⟩
private theorem pr205507 : Nat.Prime 205507 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv7,pv233]) (by decide +kernel)
def pv205507 : PrimeValue := ⟨205507, pr205507⟩
private theorem pr205519 : Nat.Prime 205519 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv34253]) (by decide +kernel)
def pv205519 : PrimeValue := ⟨205519, pr205519⟩
private theorem pr205529 : Nat.Prime 205529 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv1117]) (by decide +kernel)
def pv205529 : PrimeValue := ⟨205529, pr205529⟩
private theorem pr205549 : Nat.Prime 205549 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv2447]) (by decide +kernel)
def pv205549 : PrimeValue := ⟨205549, pr205549⟩
private theorem pr205553 : Nat.Prime 205553 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv443]) (by decide +kernel)
def pv205553 : PrimeValue := ⟨205553, pr205553⟩
private theorem pr205559 : Nat.Prime 205559 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv79,pv1301]) (by decide +kernel)
def pv205559 : PrimeValue := ⟨205559, pr205559⟩
private theorem pr205589 : Nat.Prime 205589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv103,pv499]) (by decide +kernel)
def pv205589 : PrimeValue := ⟨205589, pr205589⟩
private theorem pr205603 : Nat.Prime 205603 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv34267]) (by decide +kernel)
def pv205603 : PrimeValue := ⟨205603, pr205603⟩
private theorem pr205619 : Nat.Prime 205619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv19,pv773]) (by decide +kernel)
def pv205619 : PrimeValue := ⟨205619, pr205619⟩
private theorem pr205627 : Nat.Prime 205627 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv43,pv797]) (by decide +kernel)
def pv205627 : PrimeValue := ⟨205627, pr205627⟩
private theorem pr205651 : Nat.Prime 205651 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv457]) (by decide +kernel)
def pv205651 : PrimeValue := ⟨205651, pr205651⟩
private theorem pr205663 : Nat.Prime 205663 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv151,pv227]) (by decide +kernel)
def pv205663 : PrimeValue := ⟨205663, pr205663⟩
private theorem pr205703 : Nat.Prime 205703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv2099]) (by decide +kernel)
def pv205703 : PrimeValue := ⟨205703, pr205703⟩
private theorem pr205721 : Nat.Prime 205721 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv5,pv37,pv139]) (by decide +kernel)
def pv205721 : PrimeValue := ⟨205721, pr205721⟩
private theorem pr205763 : Nat.Prime 205763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv102881]) (by decide +kernel)
def pv205763 : PrimeValue := ⟨205763, pr205763⟩
private theorem pr205837 : Nat.Prime 205837 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv1009]) (by decide +kernel)
def pv205837 : PrimeValue := ⟨205837, pr205837⟩
private theorem pr205847 : Nat.Prime 205847 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv5417]) (by decide +kernel)
def pv205847 : PrimeValue := ⟨205847, pr205847⟩
private theorem pr205913 : Nat.Prime 205913 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv3677]) (by decide +kernel)
def pv205913 : PrimeValue := ⟨205913, pr205913⟩
private theorem pr205937 : Nat.Prime 205937 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv61,pv211]) (by decide +kernel)
def pv205937 : PrimeValue := ⟨205937, pr205937⟩
private theorem pr205949 : Nat.Prime 205949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv51487]) (by decide +kernel)
def pv205949 : PrimeValue := ⟨205949, pr205949⟩
private theorem pr205951 : Nat.Prime 205951 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv1373]) (by decide +kernel)
def pv205951 : PrimeValue := ⟨205951, pr205951⟩
private theorem pr205957 : Nat.Prime 205957 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1907]) (by decide +kernel)
def pv205957 : PrimeValue := ⟨205957, pr205957⟩
private theorem pr205967 : Nat.Prime 205967 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv102983]) (by decide +kernel)
def pv205967 : PrimeValue := ⟨205967, pr205967⟩
private theorem pr205981 : Nat.Prime 205981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv3433]) (by decide +kernel)
def pv205981 : PrimeValue := ⟨205981, pr205981⟩
private theorem pr205991 : Nat.Prime 205991 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv20599]) (by decide +kernel)
def pv205991 : PrimeValue := ⟨205991, pr205991⟩
private theorem pr205993 : Nat.Prime 205993 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2861]) (by decide +kernel)
def pv205993 : PrimeValue := ⟨205993, pr205993⟩
private theorem pr206009 : Nat.Prime 206009 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv2341]) (by decide +kernel)
def pv206009 : PrimeValue := ⟨206009, pr206009⟩
private theorem pr206027 : Nat.Prime 206027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv3323]) (by decide +kernel)
def pv206027 : PrimeValue := ⟨206027, pr206027⟩
private theorem pr206033 : Nat.Prime 206033 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv79,pv163]) (by decide +kernel)
def pv206033 : PrimeValue := ⟨206033, pr206033⟩
private theorem pr206039 : Nat.Prime 206039 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv14717]) (by decide +kernel)
def pv206039 : PrimeValue := ⟨206039, pr206039⟩
private theorem pr206047 : Nat.Prime 206047 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11447]) (by decide +kernel)
def pv206047 : PrimeValue := ⟨206047, pr206047⟩
private theorem pr206051 : Nat.Prime 206051 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv13,pv317]) (by decide +kernel)
def pv206051 : PrimeValue := ⟨206051, pr206051⟩
private theorem pr206069 : Nat.Prime 206069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv51517]) (by decide +kernel)
def pv206069 : PrimeValue := ⟨206069, pr206069⟩
private theorem pr206153 : Nat.Prime 206153 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv73,pv353]) (by decide +kernel)
def pv206153 : PrimeValue := ⟨206153, pr206153⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
