/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table127
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table127.pv735473
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table017
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table028
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table029
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table045
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table095
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table096

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr735473 : Nat.Prime 735473 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv43,pv1069]) (by decide +kernel)
def pv735473 : PrimeValue := ⟨735473, pr735473⟩
private theorem pr735491 : Nat.Prime 735491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv19,pv79]) (by decide +kernel)
def pv735491 : PrimeValue := ⟨735491, pr735491⟩
private theorem pr735653 : Nat.Prime 735653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv353,pv521]) (by decide +kernel)
def pv735653 : PrimeValue := ⟨735653, pr735653⟩
private theorem pr735809 : Nat.Prime 735809 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11497]) (by decide +kernel)
def pv735809 : PrimeValue := ⟨735809, pr735809⟩
private theorem pr735937 : Nat.Prime 735937 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv3833]) (by decide +kernel)
def pv735937 : PrimeValue := ⟨735937, pr735937⟩
private theorem pr735949 : Nat.Prime 735949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv20443]) (by decide +kernel)
def pv735949 : PrimeValue := ⟨735949, pr735949⟩
private theorem pr735953 : Nat.Prime 735953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv6571]) (by decide +kernel)
def pv735953 : PrimeValue := ⟨735953, pr735953⟩
private theorem pr736147 : Nat.Prime 736147 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv40897]) (by decide +kernel)
def pv736147 : PrimeValue := ⟨736147, pr736147⟩
private theorem pr736159 : Nat.Prime 736159 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv122693]) (by decide +kernel)
def pv736159 : PrimeValue := ⟨736159, pr736159⟩
private theorem pr736357 : Nat.Prime 736357 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv61363]) (by decide +kernel)
def pv736357 : PrimeValue := ⟨736357, pr736357⟩
private theorem pr736511 : Nat.Prime 736511 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv73651]) (by decide +kernel)
def pv736511 : PrimeValue := ⟨736511, pr736511⟩
private theorem pr736691 : Nat.Prime 736691 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23,pv3203]) (by decide +kernel)
def pv736691 : PrimeValue := ⟨736691, pr736691⟩
private theorem pr736721 : Nat.Prime 736721 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv9209]) (by decide +kernel)
def pv736721 : PrimeValue := ⟨736721, pr736721⟩
private theorem pr736871 : Nat.Prime 736871 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv31,pv2377]) (by decide +kernel)
def pv736871 : PrimeValue := ⟨736871, pr736871⟩
private theorem pr736927 : Nat.Prime 736927 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv263,pv467]) (by decide +kernel)
def pv736927 : PrimeValue := ⟨736927, pr736927⟩
private theorem pr736987 : Nat.Prime 736987 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv113,pv1087]) (by decide +kernel)
def pv736987 : PrimeValue := ⟨736987, pr736987⟩
private theorem pr737039 : Nat.Prime 737039 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv401,pv919]) (by decide +kernel)
def pv737039 : PrimeValue := ⟨737039, pr737039⟩
private theorem pr737047 : Nat.Prime 737047 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13649]) (by decide +kernel)
def pv737047 : PrimeValue := ⟨737047, pr737047⟩
private theorem pr737053 : Nat.Prime 737053 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv3613]) (by decide +kernel)
def pv737053 : PrimeValue := ⟨737053, pr737053⟩
private theorem pr737083 : Nat.Prime 737083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv40949]) (by decide +kernel)
def pv737083 : PrimeValue := ⟨737083, pr737083⟩
private theorem pr737129 : Nat.Prime 737129 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv13163]) (by decide +kernel)
def pv737129 : PrimeValue := ⟨737129, pr737129⟩
private theorem pr737279 : Nat.Prime 737279 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv43,pv8573]) (by decide +kernel)
def pv737279 : PrimeValue := ⟨737279, pr737279⟩
private theorem pr737293 : Nat.Prime 737293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv61441]) (by decide +kernel)
def pv737293 : PrimeValue := ⟨737293, pr737293⟩
private theorem pr737351 : Nat.Prime 737351 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv14747]) (by decide +kernel)
def pv737351 : PrimeValue := ⟨737351, pr737351⟩
private theorem pr737479 : Nat.Prime 737479 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv1951]) (by decide +kernel)
def pv737479 : PrimeValue := ⟨737479, pr737479⟩
private theorem pr737501 : Nat.Prime 737501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv59]) (by decide +kernel)
def pv737501 : PrimeValue := ⟨737501, pr737501⟩
private theorem pr737509 : Nat.Prime 737509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv41,pv1499]) (by decide +kernel)
def pv737509 : PrimeValue := ⟨737509, pr737509⟩
private theorem pr737533 : Nat.Prime 737533 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv6829]) (by decide +kernel)
def pv737533 : PrimeValue := ⟨737533, pr737533⟩
private theorem pr737563 : Nat.Prime 737563 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv17,pv1033]) (by decide +kernel)
def pv737563 : PrimeValue := ⟨737563, pr737563⟩
private theorem pr737573 : Nat.Prime 737573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv16763]) (by decide +kernel)
def pv737573 : PrimeValue := ⟨737573, pr737573⟩
private theorem pr737629 : Nat.Prime 737629 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv61469]) (by decide +kernel)
def pv737629 : PrimeValue := ⟨737629, pr737629⟩
private theorem pr737797 : Nat.Prime 737797 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv61483]) (by decide +kernel)
def pv737797 : PrimeValue := ⟨737797, pr737797⟩
private theorem pr737809 : Nat.Prime 737809 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv19,pv809]) (by decide +kernel)
def pv737809 : PrimeValue := ⟨737809, pr737809⟩
private theorem pr737843 : Nat.Prime 737843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv7529]) (by decide +kernel)
def pv737843 : PrimeValue := ⟨737843, pr737843⟩
private theorem pr737921 : Nat.Prime 737921 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv1153]) (by decide +kernel)
def pv737921 : PrimeValue := ⟨737921, pr737921⟩
private theorem pr737929 : Nat.Prime 737929 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv37,pv277]) (by decide +kernel)
def pv737929 : PrimeValue := ⟨737929, pr737929⟩
private theorem pr738011 : Nat.Prime 738011 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv13,pv811]) (by decide +kernel)
def pv738011 : PrimeValue := ⟨738011, pr738011⟩
private theorem pr738109 : Nat.Prime 738109 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv29,pv101]) (by decide +kernel)
def pv738109 : PrimeValue := ⟨738109, pr738109⟩
private theorem pr738223 : Nat.Prime 738223 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv61,pv2017]) (by decide +kernel)
def pv738223 : PrimeValue := ⟨738223, pr738223⟩
private theorem pr738401 : Nat.Prime 738401 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv71]) (by decide +kernel)
def pv738401 : PrimeValue := ⟨738401, pr738401⟩
private theorem pr738443 : Nat.Prime 738443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv251,pv1471]) (by decide +kernel)
def pv738443 : PrimeValue := ⟨738443, pr738443⟩
private theorem pr738523 : Nat.Prime 738523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv89,pv461]) (by decide +kernel)
def pv738523 : PrimeValue := ⟨738523, pr738523⟩
private theorem pr738583 : Nat.Prime 738583 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv13,pv17,pv557]) (by decide +kernel)
def pv738583 : PrimeValue := ⟨738583, pr738583⟩
private theorem pr738791 : Nat.Prime 738791 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv5683]) (by decide +kernel)
def pv738791 : PrimeValue := ⟨738791, pr738791⟩
private theorem pr738851 : Nat.Prime 738851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv2111]) (by decide +kernel)
def pv738851 : PrimeValue := ⟨738851, pr738851⟩
private theorem pr738937 : Nat.Prime 738937 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv311]) (by decide +kernel)
def pv738937 : PrimeValue := ⟨738937, pr738937⟩
private theorem pr738953 : Nat.Prime 738953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv92369]) (by decide +kernel)
def pv738953 : PrimeValue := ⟨738953, pr738953⟩
private theorem pr738989 : Nat.Prime 738989 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv239,pv773]) (by decide +kernel)
def pv738989 : PrimeValue := ⟨738989, pr738989⟩
private theorem pr739003 : Nat.Prime 739003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv11197]) (by decide +kernel)
def pv739003 : PrimeValue := ⟨739003, pr739003⟩
private theorem pr739031 : Nat.Prime 739031 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv263,pv281]) (by decide +kernel)
def pv739031 : PrimeValue := ⟨739031, pr739031⟩
private theorem pr739061 : Nat.Prime 739061 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv5279]) (by decide +kernel)
def pv739061 : PrimeValue := ⟨739061, pr739061⟩
private theorem pr739103 : Nat.Prime 739103 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv13,pv31,pv131]) (by decide +kernel)
def pv739103 : PrimeValue := ⟨739103, pr739103⟩
private theorem pr739331 : Nat.Prime 739331 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv4349]) (by decide +kernel)
def pv739331 : PrimeValue := ⟨739331, pr739331⟩
private theorem pr739369 : Nat.Prime 739369 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv163]) (by decide +kernel)
def pv739369 : PrimeValue := ⟨739369, pr739369⟩
private theorem pr739379 : Nat.Prime 739379 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv337,pv1097]) (by decide +kernel)
def pv739379 : PrimeValue := ⟨739379, pr739379⟩
private theorem pr739493 : Nat.Prime 739493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv14221]) (by decide +kernel)
def pv739493 : PrimeValue := ⟨739493, pr739493⟩
private theorem pr739523 : Nat.Prime 739523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv101,pv523]) (by decide +kernel)
def pv739523 : PrimeValue := ⟨739523, pr739523⟩
private theorem pr739603 : Nat.Prime 739603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv2417]) (by decide +kernel)
def pv739603 : PrimeValue := ⟨739603, pr739603⟩
private theorem pr739631 : Nat.Prime 739631 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv37,pv1999]) (by decide +kernel)
def pv739631 : PrimeValue := ⟨739631, pr739631⟩
private theorem pr739693 : Nat.Prime 739693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv761]) (by decide +kernel)
def pv739693 : PrimeValue := ⟨739693, pr739693⟩
private theorem pr739943 : Nat.Prime 739943 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv7,pv17,pv3109]) (by decide +kernel)
def pv739943 : PrimeValue := ⟨739943, pr739943⟩
private theorem pr740053 : Nat.Prime 740053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv61,pv337]) (by decide +kernel)
def pv740053 : PrimeValue := ⟨740053, pr740053⟩
private theorem pr740189 : Nat.Prime 740189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv211,pv877]) (by decide +kernel)
def pv740189 : PrimeValue := ⟨740189, pr740189⟩
private theorem pr740287 : Nat.Prime 740287 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13709]) (by decide +kernel)
def pv740287 : PrimeValue := ⟨740287, pr740287⟩
private theorem pr740321 : Nat.Prime 740321 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv661]) (by decide +kernel)
def pv740321 : PrimeValue := ⟨740321, pr740321⟩
private theorem pr740359 : Nat.Prime 740359 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv41131]) (by decide +kernel)
def pv740359 : PrimeValue := ⟨740359, pr740359⟩
private theorem pr740513 : Nat.Prime 740513 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv73,pv317]) (by decide +kernel)
def pv740513 : PrimeValue := ⟨740513, pr740513⟩
private theorem pr740533 : Nat.Prime 740533 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv47,pv101]) (by decide +kernel)
def pv740533 : PrimeValue := ⟨740533, pr740533⟩
private theorem pr740549 : Nat.Prime 740549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv185137]) (by decide +kernel)
def pv740549 : PrimeValue := ⟨740549, pr740549⟩
private theorem pr740599 : Nat.Prime 740599 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv123433]) (by decide +kernel)
def pv740599 : PrimeValue := ⟨740599, pr740599⟩
private theorem pr740659 : Nat.Prime 740659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv73,pv89]) (by decide +kernel)
def pv740659 : PrimeValue := ⟨740659, pr740659⟩
private theorem pr740693 : Nat.Prime 740693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv83,pv97]) (by decide +kernel)
def pv740693 : PrimeValue := ⟨740693, pr740693⟩
private theorem pr740713 : Nat.Prime 740713 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv4409]) (by decide +kernel)
def pv740713 : PrimeValue := ⟨740713, pr740713⟩
private theorem pr740801 : Nat.Prime 740801 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv463]) (by decide +kernel)
def pv740801 : PrimeValue := ⟨740801, pr740801⟩
private theorem pr740891 : Nat.Prime 740891 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv43,pv1723]) (by decide +kernel)
def pv740891 : PrimeValue := ⟨740891, pr740891⟩
private theorem pr740989 : Nat.Prime 740989 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2287]) (by decide +kernel)
def pv740989 : PrimeValue := ⟨740989, pr740989⟩
private theorem pr741011 : Nat.Prime 741011 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv74101]) (by decide +kernel)
def pv741011 : PrimeValue := ⟨741011, pr741011⟩
private theorem pr741127 : Nat.Prime 741127 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv149,pv829]) (by decide +kernel)
def pv741127 : PrimeValue := ⟨741127, pr741127⟩
private theorem pr741131 : Nat.Prime 741131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv5701]) (by decide +kernel)
def pv741131 : PrimeValue := ⟨741131, pr741131⟩
private theorem pr741343 : Nat.Prime 741343 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv19,pv929]) (by decide +kernel)
def pv741343 : PrimeValue := ⟨741343, pr741343⟩
private theorem pr741413 : Nat.Prime 741413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv26479]) (by decide +kernel)
def pv741413 : PrimeValue := ⟨741413, pr741413⟩
private theorem pr741431 : Nat.Prime 741431 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv74143]) (by decide +kernel)
def pv741431 : PrimeValue := ⟨741431, pr741431⟩
private theorem pr741469 : Nat.Prime 741469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv97]) (by decide +kernel)
def pv741469 : PrimeValue := ⟨741469, pr741469⟩
private theorem pr741479 : Nat.Prime 741479 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv173,pv2143]) (by decide +kernel)
def pv741479 : PrimeValue := ⟨741479, pr741479⟩
private theorem pr741509 : Nat.Prime 741509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv197,pv941]) (by decide +kernel)
def pv741509 : PrimeValue := ⟨741509, pr741509⟩
private theorem pr741547 : Nat.Prime 741547 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv3169]) (by decide +kernel)
def pv741547 : PrimeValue := ⟨741547, pr741547⟩
private theorem pr741593 : Nat.Prime 741593 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv92699]) (by decide +kernel)
def pv741593 : PrimeValue := ⟨741593, pr741593⟩
private theorem pr741641 : Nat.Prime 741641 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv18541]) (by decide +kernel)
def pv741641 : PrimeValue := ⟨741641, pr741641⟩
private theorem pr741709 : Nat.Prime 741709 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv11,pv1873]) (by decide +kernel)
def pv741709 : PrimeValue := ⟨741709, pr741709⟩
private theorem pr741847 : Nat.Prime 741847 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv17,pv1039]) (by decide +kernel)
def pv741847 : PrimeValue := ⟨741847, pr741847⟩
private theorem pr741869 : Nat.Prime 741869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv185467]) (by decide +kernel)
def pv741869 : PrimeValue := ⟨741869, pr741869⟩
private theorem pr741877 : Nat.Prime 741877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv211,pv293]) (by decide +kernel)
def pv741877 : PrimeValue := ⟨741877, pr741877⟩
private theorem pr741941 : Nat.Prime 741941 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv37097]) (by decide +kernel)
def pv741941 : PrimeValue := ⟨741941, pr741941⟩
private theorem pr741973 : Nat.Prime 741973 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv11,pv73]) (by decide +kernel)
def pv741973 : PrimeValue := ⟨741973, pr741973⟩
private theorem pr742009 : Nat.Prime 742009 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv43,pv719]) (by decide +kernel)
def pv742009 : PrimeValue := ⟨742009, pr742009⟩
private theorem pr742151 : Nat.Prime 742151 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv14843]) (by decide +kernel)
def pv742151 : PrimeValue := ⟨742151, pr742151⟩
private theorem pr742193 : Nat.Prime 742193 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv4217]) (by decide +kernel)
def pv742193 : PrimeValue := ⟨742193, pr742193⟩
private theorem pr742219 : Nat.Prime 742219 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv103,pv1201]) (by decide +kernel)
def pv742219 : PrimeValue := ⟨742219, pr742219⟩
private theorem pr742229 : Nat.Prime 742229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv185557]) (by decide +kernel)
def pv742229 : PrimeValue := ⟨742229, pr742229⟩
private theorem pr742253 : Nat.Prime 742253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv541]) (by decide +kernel)
def pv742253 : PrimeValue := ⟨742253, pr742253⟩
private theorem pr742289 : Nat.Prime 742289 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv17,pv2729]) (by decide +kernel)
def pv742289 : PrimeValue := ⟨742289, pr742289⟩
private theorem pr742333 : Nat.Prime 742333 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv3,pv61861]) (by decide +kernel)
def pv742333 : PrimeValue := ⟨742333, pr742333⟩
private theorem pr742393 : Nat.Prime 742393 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv491]) (by decide +kernel)
def pv742393 : PrimeValue := ⟨742393, pr742393⟩
private theorem pr742499 : Nat.Prime 742499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv371249]) (by decide +kernel)
def pv742499 : PrimeValue := ⟨742499, pr742499⟩
private theorem pr742657 : Nat.Prime 742657 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv967]) (by decide +kernel)
def pv742657 : PrimeValue := ⟨742657, pr742657⟩
private theorem pr742673 : Nat.Prime 742673 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv19,pv349]) (by decide +kernel)
def pv742673 : PrimeValue := ⟨742673, pr742673⟩
private theorem pr742699 : Nat.Prime 742699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv31]) (by decide +kernel)
def pv742699 : PrimeValue := ⟨742699, pr742699⟩
private theorem pr742723 : Nat.Prime 742723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv123787]) (by decide +kernel)
def pv742723 : PrimeValue := ⟨742723, pr742723⟩
private theorem pr742993 : Nat.Prime 742993 :=
  checkPrime_prime (q := pv53) (ls := [pv2,pv3,pv23,pv673]) (by decide +kernel)
def pv742993 : PrimeValue := ⟨742993, pr742993⟩
private theorem pr743069 : Nat.Prime 743069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv185767]) (by decide +kernel)
def pv743069 : PrimeValue := ⟨743069, pr743069⟩
private theorem pr743111 : Nat.Prime 743111 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv74311]) (by decide +kernel)
def pv743111 : PrimeValue := ⟨743111, pr743111⟩
private theorem pr743137 : Nat.Prime 743137 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7741]) (by decide +kernel)
def pv743137 : PrimeValue := ⟨743137, pr743137⟩
private theorem pr743143 : Nat.Prime 743143 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv211,pv587]) (by decide +kernel)
def pv743143 : PrimeValue := ⟨743143, pr743143⟩
private theorem pr743173 : Nat.Prime 743173 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv3643]) (by decide +kernel)
def pv743173 : PrimeValue := ⟨743173, pr743173⟩
private theorem pr743263 : Nat.Prime 743263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv733]) (by decide +kernel)
def pv743263 : PrimeValue := ⟨743263, pr743263⟩
private theorem pr743269 : Nat.Prime 743269 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv2693]) (by decide +kernel)
def pv743269 : PrimeValue := ⟨743269, pr743269⟩
private theorem pr743273 : Nat.Prime 743273 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv53,pv1753]) (by decide +kernel)
def pv743273 : PrimeValue := ⟨743273, pr743273⟩
private theorem pr743423 : Nat.Prime 743423 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv337,pv1103]) (by decide +kernel)
def pv743423 : PrimeValue := ⟨743423, pr743423⟩
private theorem pr743549 : Nat.Prime 743549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv79,pv181]) (by decide +kernel)
def pv743549 : PrimeValue := ⟨743549, pr743549⟩
private theorem pr743579 : Nat.Prime 743579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv73,pv463]) (by decide +kernel)
def pv743579 : PrimeValue := ⟨743579, pr743579⟩
private theorem pr743609 : Nat.Prime 743609 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv92951]) (by decide +kernel)
def pv743609 : PrimeValue := ⟨743609, pr743609⟩
private theorem pr743689 : Nat.Prime 743689 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv11,pv313]) (by decide +kernel)
def pv743689 : PrimeValue := ⟨743689, pr743689⟩
private theorem pr743779 : Nat.Prime 743779 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv5903]) (by decide +kernel)
def pv743779 : PrimeValue := ⟨743779, pr743779⟩
private theorem pr743933 : Nat.Prime 743933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv163]) (by decide +kernel)
def pv743933 : PrimeValue := ⟨743933, pr743933⟩
private theorem pr743989 : Nat.Prime 743989 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv3,pv7,pv17,pv521]) (by decide +kernel)
def pv743989 : PrimeValue := ⟨743989, pr743989⟩
private theorem pr744071 : Nat.Prime 744071 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv5,pv37,pv2011]) (by decide +kernel)
def pv744071 : PrimeValue := ⟨744071, pr744071⟩
private theorem pr744083 : Nat.Prime 744083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv12829]) (by decide +kernel)
def pv744083 : PrimeValue := ⟨744083, pr744083⟩
private theorem pr744127 : Nat.Prime 744127 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv124021]) (by decide +kernel)
def pv744127 : PrimeValue := ⟨744127, pr744127⟩
private theorem pr744199 : Nat.Prime 744199 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv29,pv47]) (by decide +kernel)
def pv744199 : PrimeValue := ⟨744199, pr744199⟩
private theorem pr744313 : Nat.Prime 744313 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv31013]) (by decide +kernel)
def pv744313 : PrimeValue := ⟨744313, pr744313⟩
private theorem pr744547 : Nat.Prime 744547 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv29,pv389]) (by decide +kernel)
def pv744547 : PrimeValue := ⟨744547, pr744547⟩
private theorem pr744599 : Nat.Prime 744599 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv372299]) (by decide +kernel)
def pv744599 : PrimeValue := ⟨744599, pr744599⟩
private theorem pr744607 : Nat.Prime 744607 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13789]) (by decide +kernel)
def pv744607 : PrimeValue := ⟨744607, pr744607⟩
private theorem pr744641 : Nat.Prime 744641 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv13,pv179]) (by decide +kernel)
def pv744641 : PrimeValue := ⟨744641, pr744641⟩
private theorem pr744701 : Nat.Prime 744701 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv677]) (by decide +kernel)
def pv744701 : PrimeValue := ⟨744701, pr744701⟩
private theorem pr744833 : Nat.Prime 744833 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv23]) (by decide +kernel)
def pv744833 : PrimeValue := ⟨744833, pr744833⟩
private theorem pr744949 : Nat.Prime 744949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv20693]) (by decide +kernel)
def pv744949 : PrimeValue := ⟨744949, pr744949⟩
private theorem pr745103 : Nat.Prime 745103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv103,pv3617]) (by decide +kernel)
def pv745103 : PrimeValue := ⟨745103, pr745103⟩
private theorem pr745117 : Nat.Prime 745117 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv31,pv2003]) (by decide +kernel)
def pv745117 : PrimeValue := ⟨745117, pr745117⟩
private theorem pr745133 : Nat.Prime 745133 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv186283]) (by decide +kernel)
def pv745133 : PrimeValue := ⟨745133, pr745133⟩
private theorem pr745243 : Nat.Prime 745243 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29,pv4283]) (by decide +kernel)
def pv745243 : PrimeValue := ⟨745243, pr745243⟩
private theorem pr745301 : Nat.Prime 745301 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv29,pv257]) (by decide +kernel)
def pv745301 : PrimeValue := ⟨745301, pr745301⟩
private theorem pr745543 : Nat.Prime 745543 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv61,pv97]) (by decide +kernel)
def pv745543 : PrimeValue := ⟨745543, pr745543⟩
private theorem pr745649 : Nat.Prime 745649 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv1607]) (by decide +kernel)
def pv745649 : PrimeValue := ⟨745649, pr745649⟩
private theorem pr745709 : Nat.Prime 745709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv4547]) (by decide +kernel)
def pv745709 : PrimeValue := ⟨745709, pr745709⟩
private theorem pr745859 : Nat.Prime 745859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv21937]) (by decide +kernel)
def pv745859 : PrimeValue := ⟨745859, pr745859⟩
private theorem pr745873 : Nat.Prime 745873 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv41,pv379]) (by decide +kernel)
def pv745873 : PrimeValue := ⟨745873, pr745873⟩
private theorem pr745931 : Nat.Prime 745931 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv97,pv769]) (by decide +kernel)
def pv745931 : PrimeValue := ⟨745931, pr745931⟩
private theorem pr745973 : Nat.Prime 745973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv251,pv743]) (by decide +kernel)
def pv745973 : PrimeValue := ⟨745973, pr745973⟩
private theorem pr746153 : Nat.Prime 746153 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv61,pv139]) (by decide +kernel)
def pv746153 : PrimeValue := ⟨746153, pr746153⟩
private theorem pr746171 : Nat.Prime 746171 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv29,pv31,pv83]) (by decide +kernel)
def pv746171 : PrimeValue := ⟨746171, pr746171⟩
private theorem pr746227 : Nat.Prime 746227 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv1063]) (by decide +kernel)
def pv746227 : PrimeValue := ⟨746227, pr746227⟩
private theorem pr746303 : Nat.Prime 746303 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv373151]) (by decide +kernel)
def pv746303 : PrimeValue := ⟨746303, pr746303⟩
private theorem pr746329 : Nat.Prime 746329 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv257]) (by decide +kernel)
def pv746329 : PrimeValue := ⟨746329, pr746329⟩
private theorem pr746411 : Nat.Prime 746411 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv5,pv7,pv10663]) (by decide +kernel)
def pv746411 : PrimeValue := ⟨746411, pr746411⟩
private theorem pr746429 : Nat.Prime 746429 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv191,pv977]) (by decide +kernel)
def pv746429 : PrimeValue := ⟨746429, pr746429⟩
private theorem pr746509 : Nat.Prime 746509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv8887]) (by decide +kernel)
def pv746509 : PrimeValue := ⟨746509, pr746509⟩
private theorem pr746563 : Nat.Prime 746563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv124427]) (by decide +kernel)
def pv746563 : PrimeValue := ⟨746563, pr746563⟩
private theorem pr746659 : Nat.Prime 746659 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv11,pv419]) (by decide +kernel)
def pv746659 : PrimeValue := ⟨746659, pr746659⟩
private theorem pr746723 : Nat.Prime 746723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv373361]) (by decide +kernel)
def pv746723 : PrimeValue := ⟨746723, pr746723⟩
private theorem pr746869 : Nat.Prime 746869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv109,pv571]) (by decide +kernel)
def pv746869 : PrimeValue := ⟨746869, pr746869⟩
private theorem pr746891 : Nat.Prime 746891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19,pv3931]) (by decide +kernel)
def pv746891 : PrimeValue := ⟨746891, pr746891⟩
private theorem pr746939 : Nat.Prime 746939 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv9109]) (by decide +kernel)
def pv746939 : PrimeValue := ⟨746939, pr746939⟩
private theorem pr746951 : Nat.Prime 746951 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv14939]) (by decide +kernel)
def pv746951 : PrimeValue := ⟨746951, pr746951⟩
private theorem pr746981 : Nat.Prime 746981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv17]) (by decide +kernel)
def pv746981 : PrimeValue := ⟨746981, pr746981⟩
private theorem pr747259 : Nat.Prime 747259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv124543]) (by decide +kernel)
def pv747259 : PrimeValue := ⟨747259, pr747259⟩
private theorem pr747343 : Nat.Prime 747343 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv41519]) (by decide +kernel)
def pv747343 : PrimeValue := ⟨747343, pr747343⟩
private theorem pr747401 : Nat.Prime 747401 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv37,pv101]) (by decide +kernel)
def pv747401 : PrimeValue := ⟨747401, pr747401⟩
private theorem pr747499 : Nat.Prime 747499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv79,pv83]) (by decide +kernel)
def pv747499 : PrimeValue := ⟨747499, pr747499⟩
private theorem pr747547 : Nat.Prime 747547 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv5417]) (by decide +kernel)
def pv747547 : PrimeValue := ⟨747547, pr747547⟩
private theorem pr747583 : Nat.Prime 747583 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv47,pv241]) (by decide +kernel)
def pv747583 : PrimeValue := ⟨747583, pr747583⟩
private theorem pr747679 : Nat.Prime 747679 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29,pv4297]) (by decide +kernel)
def pv747679 : PrimeValue := ⟨747679, pr747679⟩
private theorem pr747731 : Nat.Prime 747731 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23,pv3251]) (by decide +kernel)
def pv747731 : PrimeValue := ⟨747731, pr747731⟩
private theorem pr747863 : Nat.Prime 747863 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv179,pv2089]) (by decide +kernel)
def pv747863 : PrimeValue := ⟨747863, pr747863⟩
private theorem pr747979 : Nat.Prime 747979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv1619]) (by decide +kernel)
def pv747979 : PrimeValue := ⟨747979, pr747979⟩
private theorem pr748003 : Nat.Prime 748003 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv59,pv2113]) (by decide +kernel)
def pv748003 : PrimeValue := ⟨748003, pr748003⟩
private theorem pr748019 : Nat.Prime 748019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv374009]) (by decide +kernel)
def pv748019 : PrimeValue := ⟨748019, pr748019⟩
private theorem pr748057 : Nat.Prime 748057 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv71,pv439]) (by decide +kernel)
def pv748057 : PrimeValue := ⟨748057, pr748057⟩
private theorem pr748093 : Nat.Prime 748093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv2011]) (by decide +kernel)
def pv748093 : PrimeValue := ⟨748093, pr748093⟩
private theorem pr748133 : Nat.Prime 748133 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv347]) (by decide +kernel)
def pv748133 : PrimeValue := ⟨748133, pr748133⟩
private theorem pr748183 : Nat.Prime 748183 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv6563]) (by decide +kernel)
def pv748183 : PrimeValue := ⟨748183, pr748183⟩
private theorem pr748199 : Nat.Prime 748199 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv71,pv479]) (by decide +kernel)
def pv748199 : PrimeValue := ⟨748199, pr748199⟩
private theorem pr748211 : Nat.Prime 748211 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv74821]) (by decide +kernel)
def pv748211 : PrimeValue := ⟨748211, pr748211⟩
private theorem pr748271 : Nat.Prime 748271 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv74827]) (by decide +kernel)
def pv748271 : PrimeValue := ⟨748271, pr748271⟩
private theorem pr748273 : Nat.Prime 748273 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv17,pv131]) (by decide +kernel)
def pv748273 : PrimeValue := ⟨748273, pr748273⟩
private theorem pr748283 : Nat.Prime 748283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv16267]) (by decide +kernel)
def pv748283 : PrimeValue := ⟨748283, pr748283⟩
private theorem pr748339 : Nat.Prime 748339 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv191,pv653]) (by decide +kernel)
def pv748339 : PrimeValue := ⟨748339, pr748339⟩
private theorem pr748361 : Nat.Prime 748361 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv53,pv353]) (by decide +kernel)
def pv748361 : PrimeValue := ⟨748361, pr748361⟩
private theorem pr748453 : Nat.Prime 748453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv97,pv643]) (by decide +kernel)
def pv748453 : PrimeValue := ⟨748453, pr748453⟩
private theorem pr748463 : Nat.Prime 748463 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv13,pv2617]) (by decide +kernel)
def pv748463 : PrimeValue := ⟨748463, pr748463⟩
private theorem pr748597 : Nat.Prime 748597 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv62383]) (by decide +kernel)
def pv748597 : PrimeValue := ⟨748597, pr748597⟩
private theorem pr748603 : Nat.Prime 748603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4621]) (by decide +kernel)
def pv748603 : PrimeValue := ⟨748603, pr748603⟩
private theorem pr748609 : Nat.Prime 748609 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv557]) (by decide +kernel)
def pv748609 : PrimeValue := ⟨748609, pr748609⟩
private theorem pr748613 : Nat.Prime 748613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv101,pv109]) (by decide +kernel)
def pv748613 : PrimeValue := ⟨748613, pr748613⟩
private theorem pr748703 : Nat.Prime 748703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv374351]) (by decide +kernel)
def pv748703 : PrimeValue := ⟨748703, pr748703⟩
private theorem pr748717 : Nat.Prime 748717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv43,pv1451]) (by decide +kernel)
def pv748717 : PrimeValue := ⟨748717, pr748717⟩
private theorem pr748829 : Nat.Prime 748829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv59,pv167]) (by decide +kernel)
def pv748829 : PrimeValue := ⟨748829, pr748829⟩
private theorem pr748849 : Nat.Prime 748849 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv15601]) (by decide +kernel)
def pv748849 : PrimeValue := ⟨748849, pr748849⟩
private theorem pr749069 : Nat.Prime 749069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv401,pv467]) (by decide +kernel)
def pv749069 : PrimeValue := ⟨749069, pr749069⟩
private theorem pr749083 : Nat.Prime 749083 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv124847]) (by decide +kernel)
def pv749083 : PrimeValue := ⟨749083, pr749083⟩
private theorem pr749197 : Nat.Prime 749197 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv991]) (by decide +kernel)
def pv749197 : PrimeValue := ⟨749197, pr749197⟩
private theorem pr749219 : Nat.Prime 749219 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv101,pv3709]) (by decide +kernel)
def pv749219 : PrimeValue := ⟨749219, pr749219⟩
private theorem pr749443 : Nat.Prime 749443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv124907]) (by decide +kernel)
def pv749443 : PrimeValue := ⟨749443, pr749443⟩
private theorem pr749899 : Nat.Prime 749899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1543]) (by decide +kernel)
def pv749899 : PrimeValue := ⟨749899, pr749899⟩
private theorem pr749923 : Nat.Prime 749923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv124987]) (by decide +kernel)
def pv749923 : PrimeValue := ⟨749923, pr749923⟩
private theorem pr750019 : Nat.Prime 750019 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv125003]) (by decide +kernel)
def pv750019 : PrimeValue := ⟨750019, pr750019⟩
private theorem pr750173 : Nat.Prime 750173 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv223]) (by decide +kernel)
def pv750173 : PrimeValue := ⟨750173, pr750173⟩
private theorem pr750203 : Nat.Prime 750203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv375101]) (by decide +kernel)
def pv750203 : PrimeValue := ⟨750203, pr750203⟩
private theorem pr750209 : Nat.Prime 750209 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5861]) (by decide +kernel)
def pv750209 : PrimeValue := ⟨750209, pr750209⟩
private theorem pr750313 : Nat.Prime 750313 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv17,pv613]) (by decide +kernel)
def pv750313 : PrimeValue := ⟨750313, pr750313⟩
private theorem pr750383 : Nat.Prime 750383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv41,pv9151]) (by decide +kernel)
def pv750383 : PrimeValue := ⟨750383, pr750383⟩
private theorem pr750413 : Nat.Prime 750413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv14431]) (by decide +kernel)
def pv750413 : PrimeValue := ⟨750413, pr750413⟩
private theorem pr750419 : Nat.Prime 750419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv375209]) (by decide +kernel)
def pv750419 : PrimeValue := ⟨750419, pr750419⟩
private theorem pr750521 : Nat.Prime 750521 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv29,pv647]) (by decide +kernel)
def pv750521 : PrimeValue := ⟨750521, pr750521⟩
private theorem pr750613 : Nat.Prime 750613 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv71,pv881]) (by decide +kernel)
def pv750613 : PrimeValue := ⟨750613, pr750613⟩
private theorem pr750653 : Nat.Prime 750653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv17,pv19,pv83]) (by decide +kernel)
def pv750653 : PrimeValue := ⟨750653, pr750653⟩
private theorem pr750667 : Nat.Prime 750667 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv61,pv293]) (by decide +kernel)
def pv750667 : PrimeValue := ⟨750667, pr750667⟩
private theorem pr750713 : Nat.Prime 750713 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv107,pv877]) (by decide +kernel)
def pv750713 : PrimeValue := ⟨750713, pr750713⟩
private theorem pr750749 : Nat.Prime 750749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv187687]) (by decide +kernel)
def pv750749 : PrimeValue := ⟨750749, pr750749⟩
private theorem pr750787 : Nat.Prime 750787 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv125131]) (by decide +kernel)
def pv750787 : PrimeValue := ⟨750787, pr750787⟩
private theorem pr750791 : Nat.Prime 750791 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv75079]) (by decide +kernel)
def pv750791 : PrimeValue := ⟨750791, pr750791⟩
private theorem pr750803 : Nat.Prime 750803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv67,pv431]) (by decide +kernel)
def pv750803 : PrimeValue := ⟨750803, pr750803⟩
private theorem pr750929 : Nat.Prime 750929 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv46933]) (by decide +kernel)
def pv750929 : PrimeValue := ⟨750929, pr750929⟩
private theorem pr750943 : Nat.Prime 750943 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv41719]) (by decide +kernel)
def pv750943 : PrimeValue := ⟨750943, pr750943⟩
private theorem pr751057 : Nat.Prime 751057 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv15647]) (by decide +kernel)
def pv751057 : PrimeValue := ⟨751057, pr751057⟩
private theorem pr751087 : Nat.Prime 751087 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv1987]) (by decide +kernel)
def pv751087 : PrimeValue := ⟨751087, pr751087⟩
private theorem pr751123 : Nat.Prime 751123 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv41729]) (by decide +kernel)
def pv751123 : PrimeValue := ⟨751123, pr751123⟩
private theorem pr751207 : Nat.Prime 751207 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv125201]) (by decide +kernel)
def pv751207 : PrimeValue := ⟨751207, pr751207⟩
private theorem pr751319 : Nat.Prime 751319 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv23,pv16333]) (by decide +kernel)
def pv751319 : PrimeValue := ⟨751319, pr751319⟩
private theorem pr751343 : Nat.Prime 751343 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv47,pv7993]) (by decide +kernel)
def pv751343 : PrimeValue := ⟨751343, pr751343⟩
private theorem pr751379 : Nat.Prime 751379 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv12119]) (by decide +kernel)
def pv751379 : PrimeValue := ⟨751379, pr751379⟩
private theorem pr751423 : Nat.Prime 751423 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv17891]) (by decide +kernel)
def pv751423 : PrimeValue := ⟨751423, pr751423⟩
private theorem pr751529 : Nat.Prime 751529 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv93941]) (by decide +kernel)
def pv751529 : PrimeValue := ⟨751529, pr751529⟩
private theorem pr751579 : Nat.Prime 751579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv229,pv547]) (by decide +kernel)
def pv751579 : PrimeValue := ⟨751579, pr751579⟩
private theorem pr751631 : Nat.Prime 751631 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv11,pv6833]) (by decide +kernel)
def pv751631 : PrimeValue := ⟨751631, pr751631⟩
private theorem pr751633 : Nat.Prime 751633 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv2237]) (by decide +kernel)
def pv751633 : PrimeValue := ⟨751633, pr751633⟩
private theorem pr751643 : Nat.Prime 751643 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv101]) (by decide +kernel)
def pv751643 : PrimeValue := ⟨751643, pr751643⟩
private theorem pr751669 : Nat.Prime 751669 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv62639]) (by decide +kernel)
def pv751669 : PrimeValue := ⟨751669, pr751669⟩
private theorem pr751739 : Nat.Prime 751739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv29,pv997]) (by decide +kernel)
def pv751739 : PrimeValue := ⟨751739, pr751739⟩
private theorem pr751747 : Nat.Prime 751747 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv349,pv359]) (by decide +kernel)
def pv751747 : PrimeValue := ⟨751747, pr751747⟩
private theorem pr751813 : Nat.Prime 751813 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv31,pv43,pv47]) (by decide +kernel)
def pv751813 : PrimeValue := ⟨751813, pr751813⟩
private theorem pr751823 : Nat.Prime 751823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv199,pv1889]) (by decide +kernel)
def pv751823 : PrimeValue := ⟨751823, pr751823⟩
private theorem pr751841 : Nat.Prime 751841 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv37,pv127]) (by decide +kernel)
def pv751841 : PrimeValue := ⟨751841, pr751841⟩
private theorem pr751867 : Nat.Prime 751867 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv125311]) (by decide +kernel)
def pv751867 : PrimeValue := ⟨751867, pr751867⟩
private theorem pr752033 : Nat.Prime 752033 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv71,pv331]) (by decide +kernel)
def pv752033 : PrimeValue := ⟨752033, pr752033⟩
private theorem pr752093 : Nat.Prime 752093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv17093]) (by decide +kernel)
def pv752093 : PrimeValue := ⟨752093, pr752093⟩
private theorem pr752107 : Nat.Prime 752107 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv103,pv1217]) (by decide +kernel)
def pv752107 : PrimeValue := ⟨752107, pr752107⟩
private theorem pr752189 : Nat.Prime 752189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv4001]) (by decide +kernel)
def pv752189 : PrimeValue := ⟨752189, pr752189⟩
private theorem pr752291 : Nat.Prime 752291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv977]) (by decide +kernel)
def pv752291 : PrimeValue := ⟨752291, pr752291⟩
private theorem pr752359 : Nat.Prime 752359 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv37,pv3389]) (by decide +kernel)
def pv752359 : PrimeValue := ⟨752359, pr752359⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
