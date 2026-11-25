/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table127
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table127.pv735473
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table017
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table028
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table029
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table045
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table095
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table096

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr735473 : PrimeCertificate 735473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43,pv1069]) (by decide +kernel)
def pv735473 : PrimeValue := ⟨735473, pr735473⟩
private theorem pr735491 : PrimeCertificate 735491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv19,pv79]) (by decide +kernel)
def pv735491 : PrimeValue := ⟨735491, pr735491⟩
private theorem pr735653 : PrimeCertificate 735653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv353,pv521]) (by decide +kernel)
def pv735653 : PrimeValue := ⟨735653, pr735653⟩
private theorem pr735809 : PrimeCertificate 735809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11497]) (by decide +kernel)
def pv735809 : PrimeValue := ⟨735809, pr735809⟩
private theorem pr735937 : PrimeCertificate 735937 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3833]) (by decide +kernel)
def pv735937 : PrimeValue := ⟨735937, pr735937⟩
private theorem pr735949 : PrimeCertificate 735949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv20443]) (by decide +kernel)
def pv735949 : PrimeValue := ⟨735949, pr735949⟩
private theorem pr735953 : PrimeCertificate 735953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv6571]) (by decide +kernel)
def pv735953 : PrimeValue := ⟨735953, pr735953⟩
private theorem pr736147 : PrimeCertificate 736147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv40897]) (by decide +kernel)
def pv736147 : PrimeValue := ⟨736147, pr736147⟩
private theorem pr736159 : PrimeCertificate 736159 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv122693]) (by decide +kernel)
def pv736159 : PrimeValue := ⟨736159, pr736159⟩
private theorem pr736357 : PrimeCertificate 736357 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv61363]) (by decide +kernel)
def pv736357 : PrimeValue := ⟨736357, pr736357⟩
private theorem pr736511 : PrimeCertificate 736511 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv73651]) (by decide +kernel)
def pv736511 : PrimeValue := ⟨736511, pr736511⟩
private theorem pr736691 : PrimeCertificate 736691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv3203]) (by decide +kernel)
def pv736691 : PrimeValue := ⟨736691, pr736691⟩
private theorem pr736721 : PrimeCertificate 736721 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv9209]) (by decide +kernel)
def pv736721 : PrimeValue := ⟨736721, pr736721⟩
private theorem pr736871 : PrimeCertificate 736871 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv31,pv2377]) (by decide +kernel)
def pv736871 : PrimeValue := ⟨736871, pr736871⟩
private theorem pr736927 : PrimeCertificate 736927 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv263,pv467]) (by decide +kernel)
def pv736927 : PrimeValue := ⟨736927, pr736927⟩
private theorem pr736987 : PrimeCertificate 736987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv113,pv1087]) (by decide +kernel)
def pv736987 : PrimeValue := ⟨736987, pr736987⟩
private theorem pr737039 : PrimeCertificate 737039 :=
  certifyPrime (q := pv7) (ls := [pv2,pv401,pv919]) (by decide +kernel)
def pv737039 : PrimeValue := ⟨737039, pr737039⟩
private theorem pr737047 : PrimeCertificate 737047 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13649]) (by decide +kernel)
def pv737047 : PrimeValue := ⟨737047, pr737047⟩
private theorem pr737053 : PrimeCertificate 737053 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv3613]) (by decide +kernel)
def pv737053 : PrimeValue := ⟨737053, pr737053⟩
private theorem pr737083 : PrimeCertificate 737083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv40949]) (by decide +kernel)
def pv737083 : PrimeValue := ⟨737083, pr737083⟩
private theorem pr737129 : PrimeCertificate 737129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv13163]) (by decide +kernel)
def pv737129 : PrimeValue := ⟨737129, pr737129⟩
private theorem pr737279 : PrimeCertificate 737279 :=
  certifyPrime (q := pv7) (ls := [pv2,pv43,pv8573]) (by decide +kernel)
def pv737279 : PrimeValue := ⟨737279, pr737279⟩
private theorem pr737293 : PrimeCertificate 737293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61441]) (by decide +kernel)
def pv737293 : PrimeValue := ⟨737293, pr737293⟩
private theorem pr737351 : PrimeCertificate 737351 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv14747]) (by decide +kernel)
def pv737351 : PrimeValue := ⟨737351, pr737351⟩
private theorem pr737479 : PrimeCertificate 737479 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv1951]) (by decide +kernel)
def pv737479 : PrimeValue := ⟨737479, pr737479⟩
private theorem pr737501 : PrimeCertificate 737501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv59]) (by decide +kernel)
def pv737501 : PrimeValue := ⟨737501, pr737501⟩
private theorem pr737509 : PrimeCertificate 737509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv1499]) (by decide +kernel)
def pv737509 : PrimeValue := ⟨737509, pr737509⟩
private theorem pr737533 : PrimeCertificate 737533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv6829]) (by decide +kernel)
def pv737533 : PrimeValue := ⟨737533, pr737533⟩
private theorem pr737563 : PrimeCertificate 737563 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv17,pv1033]) (by decide +kernel)
def pv737563 : PrimeValue := ⟨737563, pr737563⟩
private theorem pr737573 : PrimeCertificate 737573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv16763]) (by decide +kernel)
def pv737573 : PrimeValue := ⟨737573, pr737573⟩
private theorem pr737629 : PrimeCertificate 737629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61469]) (by decide +kernel)
def pv737629 : PrimeValue := ⟨737629, pr737629⟩
private theorem pr737797 : PrimeCertificate 737797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61483]) (by decide +kernel)
def pv737797 : PrimeValue := ⟨737797, pr737797⟩
private theorem pr737809 : PrimeCertificate 737809 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv19,pv809]) (by decide +kernel)
def pv737809 : PrimeValue := ⟨737809, pr737809⟩
private theorem pr737843 : PrimeCertificate 737843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv7529]) (by decide +kernel)
def pv737843 : PrimeValue := ⟨737843, pr737843⟩
private theorem pr737921 : PrimeCertificate 737921 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv1153]) (by decide +kernel)
def pv737921 : PrimeValue := ⟨737921, pr737921⟩
private theorem pr737929 : PrimeCertificate 737929 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv37,pv277]) (by decide +kernel)
def pv737929 : PrimeValue := ⟨737929, pr737929⟩
private theorem pr738011 : PrimeCertificate 738011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv13,pv811]) (by decide +kernel)
def pv738011 : PrimeValue := ⟨738011, pr738011⟩
private theorem pr738109 : PrimeCertificate 738109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv29,pv101]) (by decide +kernel)
def pv738109 : PrimeValue := ⟨738109, pr738109⟩
private theorem pr738223 : PrimeCertificate 738223 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv61,pv2017]) (by decide +kernel)
def pv738223 : PrimeValue := ⟨738223, pr738223⟩
private theorem pr738401 : PrimeCertificate 738401 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv71]) (by decide +kernel)
def pv738401 : PrimeValue := ⟨738401, pr738401⟩
private theorem pr738443 : PrimeCertificate 738443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv251,pv1471]) (by decide +kernel)
def pv738443 : PrimeValue := ⟨738443, pr738443⟩
private theorem pr738523 : PrimeCertificate 738523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv89,pv461]) (by decide +kernel)
def pv738523 : PrimeValue := ⟨738523, pr738523⟩
private theorem pr738583 : PrimeCertificate 738583 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv13,pv17,pv557]) (by decide +kernel)
def pv738583 : PrimeValue := ⟨738583, pr738583⟩
private theorem pr738791 : PrimeCertificate 738791 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv5683]) (by decide +kernel)
def pv738791 : PrimeValue := ⟨738791, pr738791⟩
private theorem pr738851 : PrimeCertificate 738851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv2111]) (by decide +kernel)
def pv738851 : PrimeValue := ⟨738851, pr738851⟩
private theorem pr738937 : PrimeCertificate 738937 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv311]) (by decide +kernel)
def pv738937 : PrimeValue := ⟨738937, pr738937⟩
private theorem pr738953 : PrimeCertificate 738953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv92369]) (by decide +kernel)
def pv738953 : PrimeValue := ⟨738953, pr738953⟩
private theorem pr738989 : PrimeCertificate 738989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv239,pv773]) (by decide +kernel)
def pv738989 : PrimeValue := ⟨738989, pr738989⟩
private theorem pr739003 : PrimeCertificate 739003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv11197]) (by decide +kernel)
def pv739003 : PrimeValue := ⟨739003, pr739003⟩
private theorem pr739031 : PrimeCertificate 739031 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv263,pv281]) (by decide +kernel)
def pv739031 : PrimeValue := ⟨739031, pr739031⟩
private theorem pr739061 : PrimeCertificate 739061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv5279]) (by decide +kernel)
def pv739061 : PrimeValue := ⟨739061, pr739061⟩
private theorem pr739103 : PrimeCertificate 739103 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv13,pv31,pv131]) (by decide +kernel)
def pv739103 : PrimeValue := ⟨739103, pr739103⟩
private theorem pr739331 : PrimeCertificate 739331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv4349]) (by decide +kernel)
def pv739331 : PrimeValue := ⟨739331, pr739331⟩
private theorem pr739369 : PrimeCertificate 739369 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv163]) (by decide +kernel)
def pv739369 : PrimeValue := ⟨739369, pr739369⟩
private theorem pr739379 : PrimeCertificate 739379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv337,pv1097]) (by decide +kernel)
def pv739379 : PrimeValue := ⟨739379, pr739379⟩
private theorem pr739493 : PrimeCertificate 739493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv14221]) (by decide +kernel)
def pv739493 : PrimeValue := ⟨739493, pr739493⟩
private theorem pr739523 : PrimeCertificate 739523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv101,pv523]) (by decide +kernel)
def pv739523 : PrimeValue := ⟨739523, pr739523⟩
private theorem pr739603 : PrimeCertificate 739603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv2417]) (by decide +kernel)
def pv739603 : PrimeValue := ⟨739603, pr739603⟩
private theorem pr739631 : PrimeCertificate 739631 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv37,pv1999]) (by decide +kernel)
def pv739631 : PrimeValue := ⟨739631, pr739631⟩
private theorem pr739693 : PrimeCertificate 739693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv761]) (by decide +kernel)
def pv739693 : PrimeValue := ⟨739693, pr739693⟩
private theorem pr739943 : PrimeCertificate 739943 :=
  certifyPrime (q := pv19) (ls := [pv2,pv7,pv17,pv3109]) (by decide +kernel)
def pv739943 : PrimeValue := ⟨739943, pr739943⟩
private theorem pr740053 : PrimeCertificate 740053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61,pv337]) (by decide +kernel)
def pv740053 : PrimeValue := ⟨740053, pr740053⟩
private theorem pr740189 : PrimeCertificate 740189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv211,pv877]) (by decide +kernel)
def pv740189 : PrimeValue := ⟨740189, pr740189⟩
private theorem pr740287 : PrimeCertificate 740287 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13709]) (by decide +kernel)
def pv740287 : PrimeValue := ⟨740287, pr740287⟩
private theorem pr740321 : PrimeCertificate 740321 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv661]) (by decide +kernel)
def pv740321 : PrimeValue := ⟨740321, pr740321⟩
private theorem pr740359 : PrimeCertificate 740359 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41131]) (by decide +kernel)
def pv740359 : PrimeValue := ⟨740359, pr740359⟩
private theorem pr740513 : PrimeCertificate 740513 :=
  certifyPrime (q := pv3) (ls := [pv2,pv73,pv317]) (by decide +kernel)
def pv740513 : PrimeValue := ⟨740513, pr740513⟩
private theorem pr740533 : PrimeCertificate 740533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv47,pv101]) (by decide +kernel)
def pv740533 : PrimeValue := ⟨740533, pr740533⟩
private theorem pr740549 : PrimeCertificate 740549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv185137]) (by decide +kernel)
def pv740549 : PrimeValue := ⟨740549, pr740549⟩
private theorem pr740599 : PrimeCertificate 740599 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv123433]) (by decide +kernel)
def pv740599 : PrimeValue := ⟨740599, pr740599⟩
private theorem pr740659 : PrimeCertificate 740659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv73,pv89]) (by decide +kernel)
def pv740659 : PrimeValue := ⟨740659, pr740659⟩
private theorem pr740693 : PrimeCertificate 740693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv83,pv97]) (by decide +kernel)
def pv740693 : PrimeValue := ⟨740693, pr740693⟩
private theorem pr740713 : PrimeCertificate 740713 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv4409]) (by decide +kernel)
def pv740713 : PrimeValue := ⟨740713, pr740713⟩
private theorem pr740801 : PrimeCertificate 740801 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv463]) (by decide +kernel)
def pv740801 : PrimeValue := ⟨740801, pr740801⟩
private theorem pr740891 : PrimeCertificate 740891 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv43,pv1723]) (by decide +kernel)
def pv740891 : PrimeValue := ⟨740891, pr740891⟩
private theorem pr740989 : PrimeCertificate 740989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv2287]) (by decide +kernel)
def pv740989 : PrimeValue := ⟨740989, pr740989⟩
private theorem pr741011 : PrimeCertificate 741011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv74101]) (by decide +kernel)
def pv741011 : PrimeValue := ⟨741011, pr741011⟩
private theorem pr741127 : PrimeCertificate 741127 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv149,pv829]) (by decide +kernel)
def pv741127 : PrimeValue := ⟨741127, pr741127⟩
private theorem pr741131 : PrimeCertificate 741131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv5701]) (by decide +kernel)
def pv741131 : PrimeValue := ⟨741131, pr741131⟩
private theorem pr741343 : PrimeCertificate 741343 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv19,pv929]) (by decide +kernel)
def pv741343 : PrimeValue := ⟨741343, pr741343⟩
private theorem pr741413 : PrimeCertificate 741413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv26479]) (by decide +kernel)
def pv741413 : PrimeValue := ⟨741413, pr741413⟩
private theorem pr741431 : PrimeCertificate 741431 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv74143]) (by decide +kernel)
def pv741431 : PrimeValue := ⟨741431, pr741431⟩
private theorem pr741469 : PrimeCertificate 741469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv97]) (by decide +kernel)
def pv741469 : PrimeValue := ⟨741469, pr741469⟩
private theorem pr741479 : PrimeCertificate 741479 :=
  certifyPrime (q := pv7) (ls := [pv2,pv173,pv2143]) (by decide +kernel)
def pv741479 : PrimeValue := ⟨741479, pr741479⟩
private theorem pr741509 : PrimeCertificate 741509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv197,pv941]) (by decide +kernel)
def pv741509 : PrimeValue := ⟨741509, pr741509⟩
private theorem pr741547 : PrimeCertificate 741547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv3169]) (by decide +kernel)
def pv741547 : PrimeValue := ⟨741547, pr741547⟩
private theorem pr741593 : PrimeCertificate 741593 :=
  certifyPrime (q := pv3) (ls := [pv2,pv92699]) (by decide +kernel)
def pv741593 : PrimeValue := ⟨741593, pr741593⟩
private theorem pr741641 : PrimeCertificate 741641 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv18541]) (by decide +kernel)
def pv741641 : PrimeValue := ⟨741641, pr741641⟩
private theorem pr741709 : PrimeCertificate 741709 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv1873]) (by decide +kernel)
def pv741709 : PrimeValue := ⟨741709, pr741709⟩
private theorem pr741847 : PrimeCertificate 741847 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv17,pv1039]) (by decide +kernel)
def pv741847 : PrimeValue := ⟨741847, pr741847⟩
private theorem pr741869 : PrimeCertificate 741869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv185467]) (by decide +kernel)
def pv741869 : PrimeValue := ⟨741869, pr741869⟩
private theorem pr741877 : PrimeCertificate 741877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv211,pv293]) (by decide +kernel)
def pv741877 : PrimeValue := ⟨741877, pr741877⟩
private theorem pr741941 : PrimeCertificate 741941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv37097]) (by decide +kernel)
def pv741941 : PrimeValue := ⟨741941, pr741941⟩
private theorem pr741973 : PrimeCertificate 741973 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv11,pv73]) (by decide +kernel)
def pv741973 : PrimeValue := ⟨741973, pr741973⟩
private theorem pr742009 : PrimeCertificate 742009 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv43,pv719]) (by decide +kernel)
def pv742009 : PrimeValue := ⟨742009, pr742009⟩
private theorem pr742151 : PrimeCertificate 742151 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv14843]) (by decide +kernel)
def pv742151 : PrimeValue := ⟨742151, pr742151⟩
private theorem pr742193 : PrimeCertificate 742193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv4217]) (by decide +kernel)
def pv742193 : PrimeValue := ⟨742193, pr742193⟩
private theorem pr742219 : PrimeCertificate 742219 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv103,pv1201]) (by decide +kernel)
def pv742219 : PrimeValue := ⟨742219, pr742219⟩
private theorem pr742229 : PrimeCertificate 742229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv185557]) (by decide +kernel)
def pv742229 : PrimeValue := ⟨742229, pr742229⟩
private theorem pr742253 : PrimeCertificate 742253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv541]) (by decide +kernel)
def pv742253 : PrimeValue := ⟨742253, pr742253⟩
private theorem pr742289 : PrimeCertificate 742289 :=
  certifyPrime (q := pv13) (ls := [pv2,pv17,pv2729]) (by decide +kernel)
def pv742289 : PrimeValue := ⟨742289, pr742289⟩
private theorem pr742333 : PrimeCertificate 742333 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv61861]) (by decide +kernel)
def pv742333 : PrimeValue := ⟨742333, pr742333⟩
private theorem pr742393 : PrimeCertificate 742393 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv491]) (by decide +kernel)
def pv742393 : PrimeValue := ⟨742393, pr742393⟩
private theorem pr742499 : PrimeCertificate 742499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv371249]) (by decide +kernel)
def pv742499 : PrimeValue := ⟨742499, pr742499⟩
private theorem pr742657 : PrimeCertificate 742657 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv967]) (by decide +kernel)
def pv742657 : PrimeValue := ⟨742657, pr742657⟩
private theorem pr742673 : PrimeCertificate 742673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv19,pv349]) (by decide +kernel)
def pv742673 : PrimeValue := ⟨742673, pr742673⟩
private theorem pr742699 : PrimeCertificate 742699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv31]) (by decide +kernel)
def pv742699 : PrimeValue := ⟨742699, pr742699⟩
private theorem pr742723 : PrimeCertificate 742723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv123787]) (by decide +kernel)
def pv742723 : PrimeValue := ⟨742723, pr742723⟩
private theorem pr742993 : PrimeCertificate 742993 :=
  certifyPrime (q := pv53) (ls := [pv2,pv3,pv23,pv673]) (by decide +kernel)
def pv742993 : PrimeValue := ⟨742993, pr742993⟩
private theorem pr743069 : PrimeCertificate 743069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv185767]) (by decide +kernel)
def pv743069 : PrimeValue := ⟨743069, pr743069⟩
private theorem pr743111 : PrimeCertificate 743111 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv74311]) (by decide +kernel)
def pv743111 : PrimeValue := ⟨743111, pr743111⟩
private theorem pr743137 : PrimeCertificate 743137 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7741]) (by decide +kernel)
def pv743137 : PrimeValue := ⟨743137, pr743137⟩
private theorem pr743143 : PrimeCertificate 743143 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv211,pv587]) (by decide +kernel)
def pv743143 : PrimeValue := ⟨743143, pr743143⟩
private theorem pr743173 : PrimeCertificate 743173 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv3643]) (by decide +kernel)
def pv743173 : PrimeValue := ⟨743173, pr743173⟩
private theorem pr743263 : PrimeCertificate 743263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv733]) (by decide +kernel)
def pv743263 : PrimeValue := ⟨743263, pr743263⟩
private theorem pr743269 : PrimeCertificate 743269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv2693]) (by decide +kernel)
def pv743269 : PrimeValue := ⟨743269, pr743269⟩
private theorem pr743273 : PrimeCertificate 743273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv53,pv1753]) (by decide +kernel)
def pv743273 : PrimeValue := ⟨743273, pr743273⟩
private theorem pr743423 : PrimeCertificate 743423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv337,pv1103]) (by decide +kernel)
def pv743423 : PrimeValue := ⟨743423, pr743423⟩
private theorem pr743549 : PrimeCertificate 743549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv79,pv181]) (by decide +kernel)
def pv743549 : PrimeValue := ⟨743549, pr743549⟩
private theorem pr743579 : PrimeCertificate 743579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv73,pv463]) (by decide +kernel)
def pv743579 : PrimeValue := ⟨743579, pr743579⟩
private theorem pr743609 : PrimeCertificate 743609 :=
  certifyPrime (q := pv3) (ls := [pv2,pv92951]) (by decide +kernel)
def pv743609 : PrimeValue := ⟨743609, pr743609⟩
private theorem pr743689 : PrimeCertificate 743689 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv313]) (by decide +kernel)
def pv743689 : PrimeValue := ⟨743689, pr743689⟩
private theorem pr743779 : PrimeCertificate 743779 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv5903]) (by decide +kernel)
def pv743779 : PrimeValue := ⟨743779, pr743779⟩
private theorem pr743933 : PrimeCertificate 743933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv163]) (by decide +kernel)
def pv743933 : PrimeValue := ⟨743933, pr743933⟩
private theorem pr743989 : PrimeCertificate 743989 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv7,pv17,pv521]) (by decide +kernel)
def pv743989 : PrimeValue := ⟨743989, pr743989⟩
private theorem pr744071 : PrimeCertificate 744071 :=
  certifyPrime (q := pv29) (ls := [pv2,pv5,pv37,pv2011]) (by decide +kernel)
def pv744071 : PrimeValue := ⟨744071, pr744071⟩
private theorem pr744083 : PrimeCertificate 744083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv12829]) (by decide +kernel)
def pv744083 : PrimeValue := ⟨744083, pr744083⟩
private theorem pr744127 : PrimeCertificate 744127 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv124021]) (by decide +kernel)
def pv744127 : PrimeValue := ⟨744127, pr744127⟩
private theorem pr744199 : PrimeCertificate 744199 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv29,pv47]) (by decide +kernel)
def pv744199 : PrimeValue := ⟨744199, pr744199⟩
private theorem pr744313 : PrimeCertificate 744313 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv31013]) (by decide +kernel)
def pv744313 : PrimeValue := ⟨744313, pr744313⟩
private theorem pr744547 : PrimeCertificate 744547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv29,pv389]) (by decide +kernel)
def pv744547 : PrimeValue := ⟨744547, pr744547⟩
private theorem pr744599 : PrimeCertificate 744599 :=
  certifyPrime (q := pv7) (ls := [pv2,pv372299]) (by decide +kernel)
def pv744599 : PrimeValue := ⟨744599, pr744599⟩
private theorem pr744607 : PrimeCertificate 744607 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13789]) (by decide +kernel)
def pv744607 : PrimeValue := ⟨744607, pr744607⟩
private theorem pr744641 : PrimeCertificate 744641 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv13,pv179]) (by decide +kernel)
def pv744641 : PrimeValue := ⟨744641, pr744641⟩
private theorem pr744701 : PrimeCertificate 744701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv677]) (by decide +kernel)
def pv744701 : PrimeValue := ⟨744701, pr744701⟩
private theorem pr744833 : PrimeCertificate 744833 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv23]) (by decide +kernel)
def pv744833 : PrimeValue := ⟨744833, pr744833⟩
private theorem pr744949 : PrimeCertificate 744949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv20693]) (by decide +kernel)
def pv744949 : PrimeValue := ⟨744949, pr744949⟩
private theorem pr745103 : PrimeCertificate 745103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv103,pv3617]) (by decide +kernel)
def pv745103 : PrimeValue := ⟨745103, pr745103⟩
private theorem pr745117 : PrimeCertificate 745117 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv2003]) (by decide +kernel)
def pv745117 : PrimeValue := ⟨745117, pr745117⟩
private theorem pr745133 : PrimeCertificate 745133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv186283]) (by decide +kernel)
def pv745133 : PrimeValue := ⟨745133, pr745133⟩
private theorem pr745243 : PrimeCertificate 745243 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29,pv4283]) (by decide +kernel)
def pv745243 : PrimeValue := ⟨745243, pr745243⟩
private theorem pr745301 : PrimeCertificate 745301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29,pv257]) (by decide +kernel)
def pv745301 : PrimeValue := ⟨745301, pr745301⟩
private theorem pr745543 : PrimeCertificate 745543 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv61,pv97]) (by decide +kernel)
def pv745543 : PrimeValue := ⟨745543, pr745543⟩
private theorem pr745649 : PrimeCertificate 745649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv1607]) (by decide +kernel)
def pv745649 : PrimeValue := ⟨745649, pr745649⟩
private theorem pr745709 : PrimeCertificate 745709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv4547]) (by decide +kernel)
def pv745709 : PrimeValue := ⟨745709, pr745709⟩
private theorem pr745859 : PrimeCertificate 745859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv21937]) (by decide +kernel)
def pv745859 : PrimeValue := ⟨745859, pr745859⟩
private theorem pr745873 : PrimeCertificate 745873 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv41,pv379]) (by decide +kernel)
def pv745873 : PrimeValue := ⟨745873, pr745873⟩
private theorem pr745931 : PrimeCertificate 745931 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv97,pv769]) (by decide +kernel)
def pv745931 : PrimeValue := ⟨745931, pr745931⟩
private theorem pr745973 : PrimeCertificate 745973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv251,pv743]) (by decide +kernel)
def pv745973 : PrimeValue := ⟨745973, pr745973⟩
private theorem pr746153 : PrimeCertificate 746153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv61,pv139]) (by decide +kernel)
def pv746153 : PrimeValue := ⟨746153, pr746153⟩
private theorem pr746171 : PrimeCertificate 746171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29,pv31,pv83]) (by decide +kernel)
def pv746171 : PrimeValue := ⟨746171, pr746171⟩
private theorem pr746227 : PrimeCertificate 746227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv1063]) (by decide +kernel)
def pv746227 : PrimeValue := ⟨746227, pr746227⟩
private theorem pr746303 : PrimeCertificate 746303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv373151]) (by decide +kernel)
def pv746303 : PrimeValue := ⟨746303, pr746303⟩
private theorem pr746329 : PrimeCertificate 746329 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv257]) (by decide +kernel)
def pv746329 : PrimeValue := ⟨746329, pr746329⟩
private theorem pr746411 : PrimeCertificate 746411 :=
  certifyPrime (q := pv41) (ls := [pv2,pv5,pv7,pv10663]) (by decide +kernel)
def pv746411 : PrimeValue := ⟨746411, pr746411⟩
private theorem pr746429 : PrimeCertificate 746429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv191,pv977]) (by decide +kernel)
def pv746429 : PrimeValue := ⟨746429, pr746429⟩
private theorem pr746509 : PrimeCertificate 746509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv8887]) (by decide +kernel)
def pv746509 : PrimeValue := ⟨746509, pr746509⟩
private theorem pr746563 : PrimeCertificate 746563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv124427]) (by decide +kernel)
def pv746563 : PrimeValue := ⟨746563, pr746563⟩
private theorem pr746659 : PrimeCertificate 746659 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11,pv419]) (by decide +kernel)
def pv746659 : PrimeValue := ⟨746659, pr746659⟩
private theorem pr746723 : PrimeCertificate 746723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv373361]) (by decide +kernel)
def pv746723 : PrimeValue := ⟨746723, pr746723⟩
private theorem pr746869 : PrimeCertificate 746869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv109,pv571]) (by decide +kernel)
def pv746869 : PrimeValue := ⟨746869, pr746869⟩
private theorem pr746891 : PrimeCertificate 746891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv3931]) (by decide +kernel)
def pv746891 : PrimeValue := ⟨746891, pr746891⟩
private theorem pr746939 : PrimeCertificate 746939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv9109]) (by decide +kernel)
def pv746939 : PrimeValue := ⟨746939, pr746939⟩
private theorem pr746951 : PrimeCertificate 746951 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv14939]) (by decide +kernel)
def pv746951 : PrimeValue := ⟨746951, pr746951⟩
private theorem pr746981 : PrimeCertificate 746981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv17]) (by decide +kernel)
def pv746981 : PrimeValue := ⟨746981, pr746981⟩
private theorem pr747259 : PrimeCertificate 747259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv124543]) (by decide +kernel)
def pv747259 : PrimeValue := ⟨747259, pr747259⟩
private theorem pr747343 : PrimeCertificate 747343 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41519]) (by decide +kernel)
def pv747343 : PrimeValue := ⟨747343, pr747343⟩
private theorem pr747401 : PrimeCertificate 747401 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv37,pv101]) (by decide +kernel)
def pv747401 : PrimeValue := ⟨747401, pr747401⟩
private theorem pr747499 : PrimeCertificate 747499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv79,pv83]) (by decide +kernel)
def pv747499 : PrimeValue := ⟨747499, pr747499⟩
private theorem pr747547 : PrimeCertificate 747547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv5417]) (by decide +kernel)
def pv747547 : PrimeValue := ⟨747547, pr747547⟩
private theorem pr747583 : PrimeCertificate 747583 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv47,pv241]) (by decide +kernel)
def pv747583 : PrimeValue := ⟨747583, pr747583⟩
private theorem pr747679 : PrimeCertificate 747679 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv4297]) (by decide +kernel)
def pv747679 : PrimeValue := ⟨747679, pr747679⟩
private theorem pr747731 : PrimeCertificate 747731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv3251]) (by decide +kernel)
def pv747731 : PrimeValue := ⟨747731, pr747731⟩
private theorem pr747863 : PrimeCertificate 747863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv179,pv2089]) (by decide +kernel)
def pv747863 : PrimeValue := ⟨747863, pr747863⟩
private theorem pr747979 : PrimeCertificate 747979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv1619]) (by decide +kernel)
def pv747979 : PrimeValue := ⟨747979, pr747979⟩
private theorem pr748003 : PrimeCertificate 748003 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv59,pv2113]) (by decide +kernel)
def pv748003 : PrimeValue := ⟨748003, pr748003⟩
private theorem pr748019 : PrimeCertificate 748019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv374009]) (by decide +kernel)
def pv748019 : PrimeValue := ⟨748019, pr748019⟩
private theorem pr748057 : PrimeCertificate 748057 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv71,pv439]) (by decide +kernel)
def pv748057 : PrimeValue := ⟨748057, pr748057⟩
private theorem pr748093 : PrimeCertificate 748093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv2011]) (by decide +kernel)
def pv748093 : PrimeValue := ⟨748093, pr748093⟩
private theorem pr748133 : PrimeCertificate 748133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv347]) (by decide +kernel)
def pv748133 : PrimeValue := ⟨748133, pr748133⟩
private theorem pr748183 : PrimeCertificate 748183 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv6563]) (by decide +kernel)
def pv748183 : PrimeValue := ⟨748183, pr748183⟩
private theorem pr748199 : PrimeCertificate 748199 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv71,pv479]) (by decide +kernel)
def pv748199 : PrimeValue := ⟨748199, pr748199⟩
private theorem pr748211 : PrimeCertificate 748211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv74821]) (by decide +kernel)
def pv748211 : PrimeValue := ⟨748211, pr748211⟩
private theorem pr748271 : PrimeCertificate 748271 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv74827]) (by decide +kernel)
def pv748271 : PrimeValue := ⟨748271, pr748271⟩
private theorem pr748273 : PrimeCertificate 748273 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv17,pv131]) (by decide +kernel)
def pv748273 : PrimeValue := ⟨748273, pr748273⟩
private theorem pr748283 : PrimeCertificate 748283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv16267]) (by decide +kernel)
def pv748283 : PrimeValue := ⟨748283, pr748283⟩
private theorem pr748339 : PrimeCertificate 748339 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv191,pv653]) (by decide +kernel)
def pv748339 : PrimeValue := ⟨748339, pr748339⟩
private theorem pr748361 : PrimeCertificate 748361 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv53,pv353]) (by decide +kernel)
def pv748361 : PrimeValue := ⟨748361, pr748361⟩
private theorem pr748453 : PrimeCertificate 748453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv97,pv643]) (by decide +kernel)
def pv748453 : PrimeValue := ⟨748453, pr748453⟩
private theorem pr748463 : PrimeCertificate 748463 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv13,pv2617]) (by decide +kernel)
def pv748463 : PrimeValue := ⟨748463, pr748463⟩
private theorem pr748597 : PrimeCertificate 748597 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv62383]) (by decide +kernel)
def pv748597 : PrimeValue := ⟨748597, pr748597⟩
private theorem pr748603 : PrimeCertificate 748603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv4621]) (by decide +kernel)
def pv748603 : PrimeValue := ⟨748603, pr748603⟩
private theorem pr748609 : PrimeCertificate 748609 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv557]) (by decide +kernel)
def pv748609 : PrimeValue := ⟨748609, pr748609⟩
private theorem pr748613 : PrimeCertificate 748613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv101,pv109]) (by decide +kernel)
def pv748613 : PrimeValue := ⟨748613, pr748613⟩
private theorem pr748703 : PrimeCertificate 748703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv374351]) (by decide +kernel)
def pv748703 : PrimeValue := ⟨748703, pr748703⟩
private theorem pr748717 : PrimeCertificate 748717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv1451]) (by decide +kernel)
def pv748717 : PrimeValue := ⟨748717, pr748717⟩
private theorem pr748829 : PrimeCertificate 748829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv59,pv167]) (by decide +kernel)
def pv748829 : PrimeValue := ⟨748829, pr748829⟩
private theorem pr748849 : PrimeCertificate 748849 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv15601]) (by decide +kernel)
def pv748849 : PrimeValue := ⟨748849, pr748849⟩
private theorem pr749069 : PrimeCertificate 749069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv401,pv467]) (by decide +kernel)
def pv749069 : PrimeValue := ⟨749069, pr749069⟩
private theorem pr749083 : PrimeCertificate 749083 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv124847]) (by decide +kernel)
def pv749083 : PrimeValue := ⟨749083, pr749083⟩
private theorem pr749197 : PrimeCertificate 749197 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv991]) (by decide +kernel)
def pv749197 : PrimeValue := ⟨749197, pr749197⟩
private theorem pr749219 : PrimeCertificate 749219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv101,pv3709]) (by decide +kernel)
def pv749219 : PrimeValue := ⟨749219, pr749219⟩
private theorem pr749443 : PrimeCertificate 749443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv124907]) (by decide +kernel)
def pv749443 : PrimeValue := ⟨749443, pr749443⟩
private theorem pr749899 : PrimeCertificate 749899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1543]) (by decide +kernel)
def pv749899 : PrimeValue := ⟨749899, pr749899⟩
private theorem pr749923 : PrimeCertificate 749923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv124987]) (by decide +kernel)
def pv749923 : PrimeValue := ⟨749923, pr749923⟩
private theorem pr750019 : PrimeCertificate 750019 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv125003]) (by decide +kernel)
def pv750019 : PrimeValue := ⟨750019, pr750019⟩
private theorem pr750173 : PrimeCertificate 750173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv223]) (by decide +kernel)
def pv750173 : PrimeValue := ⟨750173, pr750173⟩
private theorem pr750203 : PrimeCertificate 750203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv375101]) (by decide +kernel)
def pv750203 : PrimeValue := ⟨750203, pr750203⟩
private theorem pr750209 : PrimeCertificate 750209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5861]) (by decide +kernel)
def pv750209 : PrimeValue := ⟨750209, pr750209⟩
private theorem pr750313 : PrimeCertificate 750313 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv17,pv613]) (by decide +kernel)
def pv750313 : PrimeValue := ⟨750313, pr750313⟩
private theorem pr750383 : PrimeCertificate 750383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv41,pv9151]) (by decide +kernel)
def pv750383 : PrimeValue := ⟨750383, pr750383⟩
private theorem pr750413 : PrimeCertificate 750413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv14431]) (by decide +kernel)
def pv750413 : PrimeValue := ⟨750413, pr750413⟩
private theorem pr750419 : PrimeCertificate 750419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv375209]) (by decide +kernel)
def pv750419 : PrimeValue := ⟨750419, pr750419⟩
private theorem pr750521 : PrimeCertificate 750521 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv29,pv647]) (by decide +kernel)
def pv750521 : PrimeValue := ⟨750521, pr750521⟩
private theorem pr750613 : PrimeCertificate 750613 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv71,pv881]) (by decide +kernel)
def pv750613 : PrimeValue := ⟨750613, pr750613⟩
private theorem pr750653 : PrimeCertificate 750653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv17,pv19,pv83]) (by decide +kernel)
def pv750653 : PrimeValue := ⟨750653, pr750653⟩
private theorem pr750667 : PrimeCertificate 750667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv61,pv293]) (by decide +kernel)
def pv750667 : PrimeValue := ⟨750667, pr750667⟩
private theorem pr750713 : PrimeCertificate 750713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv107,pv877]) (by decide +kernel)
def pv750713 : PrimeValue := ⟨750713, pr750713⟩
private theorem pr750749 : PrimeCertificate 750749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv187687]) (by decide +kernel)
def pv750749 : PrimeValue := ⟨750749, pr750749⟩
private theorem pr750787 : PrimeCertificate 750787 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv125131]) (by decide +kernel)
def pv750787 : PrimeValue := ⟨750787, pr750787⟩
private theorem pr750791 : PrimeCertificate 750791 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv75079]) (by decide +kernel)
def pv750791 : PrimeValue := ⟨750791, pr750791⟩
private theorem pr750803 : PrimeCertificate 750803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv67,pv431]) (by decide +kernel)
def pv750803 : PrimeValue := ⟨750803, pr750803⟩
private theorem pr750929 : PrimeCertificate 750929 :=
  certifyPrime (q := pv3) (ls := [pv2,pv46933]) (by decide +kernel)
def pv750929 : PrimeValue := ⟨750929, pr750929⟩
private theorem pr750943 : PrimeCertificate 750943 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41719]) (by decide +kernel)
def pv750943 : PrimeValue := ⟨750943, pr750943⟩
private theorem pr751057 : PrimeCertificate 751057 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv15647]) (by decide +kernel)
def pv751057 : PrimeValue := ⟨751057, pr751057⟩
private theorem pr751087 : PrimeCertificate 751087 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv1987]) (by decide +kernel)
def pv751087 : PrimeValue := ⟨751087, pr751087⟩
private theorem pr751123 : PrimeCertificate 751123 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41729]) (by decide +kernel)
def pv751123 : PrimeValue := ⟨751123, pr751123⟩
private theorem pr751207 : PrimeCertificate 751207 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv125201]) (by decide +kernel)
def pv751207 : PrimeValue := ⟨751207, pr751207⟩
private theorem pr751319 : PrimeCertificate 751319 :=
  certifyPrime (q := pv23) (ls := [pv2,pv23,pv16333]) (by decide +kernel)
def pv751319 : PrimeValue := ⟨751319, pr751319⟩
private theorem pr751343 : PrimeCertificate 751343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv47,pv7993]) (by decide +kernel)
def pv751343 : PrimeValue := ⟨751343, pr751343⟩
private theorem pr751379 : PrimeCertificate 751379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv12119]) (by decide +kernel)
def pv751379 : PrimeValue := ⟨751379, pr751379⟩
private theorem pr751423 : PrimeCertificate 751423 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv17891]) (by decide +kernel)
def pv751423 : PrimeValue := ⟨751423, pr751423⟩
private theorem pr751529 : PrimeCertificate 751529 :=
  certifyPrime (q := pv3) (ls := [pv2,pv93941]) (by decide +kernel)
def pv751529 : PrimeValue := ⟨751529, pr751529⟩
private theorem pr751579 : PrimeCertificate 751579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv229,pv547]) (by decide +kernel)
def pv751579 : PrimeValue := ⟨751579, pr751579⟩
private theorem pr751631 : PrimeCertificate 751631 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv11,pv6833]) (by decide +kernel)
def pv751631 : PrimeValue := ⟨751631, pr751631⟩
private theorem pr751633 : PrimeCertificate 751633 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv2237]) (by decide +kernel)
def pv751633 : PrimeValue := ⟨751633, pr751633⟩
private theorem pr751643 : PrimeCertificate 751643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv101]) (by decide +kernel)
def pv751643 : PrimeValue := ⟨751643, pr751643⟩
private theorem pr751669 : PrimeCertificate 751669 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv62639]) (by decide +kernel)
def pv751669 : PrimeValue := ⟨751669, pr751669⟩
private theorem pr751739 : PrimeCertificate 751739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv29,pv997]) (by decide +kernel)
def pv751739 : PrimeValue := ⟨751739, pr751739⟩
private theorem pr751747 : PrimeCertificate 751747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv349,pv359]) (by decide +kernel)
def pv751747 : PrimeValue := ⟨751747, pr751747⟩
private theorem pr751813 : PrimeCertificate 751813 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv31,pv43,pv47]) (by decide +kernel)
def pv751813 : PrimeValue := ⟨751813, pr751813⟩
private theorem pr751823 : PrimeCertificate 751823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv199,pv1889]) (by decide +kernel)
def pv751823 : PrimeValue := ⟨751823, pr751823⟩
private theorem pr751841 : PrimeCertificate 751841 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv37,pv127]) (by decide +kernel)
def pv751841 : PrimeValue := ⟨751841, pr751841⟩
private theorem pr751867 : PrimeCertificate 751867 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv125311]) (by decide +kernel)
def pv751867 : PrimeValue := ⟨751867, pr751867⟩
private theorem pr752033 : PrimeCertificate 752033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv71,pv331]) (by decide +kernel)
def pv752033 : PrimeValue := ⟨752033, pr752033⟩
private theorem pr752093 : PrimeCertificate 752093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv17093]) (by decide +kernel)
def pv752093 : PrimeValue := ⟨752093, pr752093⟩
private theorem pr752107 : PrimeCertificate 752107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv103,pv1217]) (by decide +kernel)
def pv752107 : PrimeValue := ⟨752107, pr752107⟩
private theorem pr752189 : PrimeCertificate 752189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv4001]) (by decide +kernel)
def pv752189 : PrimeValue := ⟨752189, pr752189⟩
private theorem pr752291 : PrimeCertificate 752291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv977]) (by decide +kernel)
def pv752291 : PrimeValue := ⟨752291, pr752291⟩
private theorem pr752359 : PrimeCertificate 752359 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37,pv3389]) (by decide +kernel)
def pv752359 : PrimeValue := ⟨752359, pr752359⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
