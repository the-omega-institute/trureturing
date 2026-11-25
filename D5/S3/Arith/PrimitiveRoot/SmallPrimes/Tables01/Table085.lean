/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table085
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table085.pv297421
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table012
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table013
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table020
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table052
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table053

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr297421 : PrimeCertificate 297421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv4957]) (by decide +kernel)
def pv297421 : PrimeValue := ⟨297421, pr297421⟩
private theorem pr297439 : PrimeCertificate 297439 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv89,pv557]) (by decide +kernel)
def pv297439 : PrimeValue := ⟨297439, pr297439⟩
private theorem pr297457 : PrimeCertificate 297457 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv6197]) (by decide +kernel)
def pv297457 : PrimeValue := ⟨297457, pr297457⟩
private theorem pr297467 : PrimeCertificate 297467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv17,pv673]) (by decide +kernel)
def pv297467 : PrimeValue := ⟨297467, pr297467⟩
private theorem pr297469 : PrimeCertificate 297469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv8263]) (by decide +kernel)
def pv297469 : PrimeValue := ⟨297469, pr297469⟩
private theorem pr297503 : PrimeCertificate 297503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv7829]) (by decide +kernel)
def pv297503 : PrimeValue := ⟨297503, pr297503⟩
private theorem pr297601 : PrimeCertificate 297601 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv31]) (by decide +kernel)
def pv297601 : PrimeValue := ⟨297601, pr297601⟩
private theorem pr297607 : PrimeCertificate 297607 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv193,pv257]) (by decide +kernel)
def pv297607 : PrimeValue := ⟨297607, pr297607⟩
private theorem pr297623 : PrimeCertificate 297623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv11447]) (by decide +kernel)
def pv297623 : PrimeValue := ⟨297623, pr297623⟩
private theorem pr297629 : PrimeCertificate 297629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv2011]) (by decide +kernel)
def pv297629 : PrimeValue := ⟨297629, pr297629⟩
private theorem pr297659 : PrimeCertificate 297659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv148829]) (by decide +kernel)
def pv297659 : PrimeValue := ⟨297659, pr297659⟩
private theorem pr297707 : PrimeCertificate 297707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv148853]) (by decide +kernel)
def pv297707 : PrimeValue := ⟨297707, pr297707⟩
private theorem pr297727 : PrimeCertificate 297727 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv13,pv347]) (by decide +kernel)
def pv297727 : PrimeValue := ⟨297727, pr297727⟩
private theorem pr297757 : PrimeCertificate 297757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv919]) (by decide +kernel)
def pv297757 : PrimeValue := ⟨297757, pr297757⟩
private theorem pr297797 : PrimeCertificate 297797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv74449]) (by decide +kernel)
def pv297797 : PrimeValue := ⟨297797, pr297797⟩
private theorem pr297809 : PrimeCertificate 297809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv2659]) (by decide +kernel)
def pv297809 : PrimeValue := ⟨297809, pr297809⟩
private theorem pr297811 : PrimeCertificate 297811 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv1103]) (by decide +kernel)
def pv297811 : PrimeValue := ⟨297811, pr297811⟩
private theorem pr297841 : PrimeCertificate 297841 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv17,pv73]) (by decide +kernel)
def pv297841 : PrimeValue := ⟨297841, pr297841⟩
private theorem pr297881 : PrimeCertificate 297881 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv677]) (by decide +kernel)
def pv297881 : PrimeValue := ⟨297881, pr297881⟩
private theorem pr297931 : PrimeCertificate 297931 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv9931]) (by decide +kernel)
def pv297931 : PrimeValue := ⟨297931, pr297931⟩
private theorem pr297953 : PrimeCertificate 297953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv9311]) (by decide +kernel)
def pv297953 : PrimeValue := ⟨297953, pr297953⟩
private theorem pr297967 : PrimeCertificate 297967 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv53,pv937]) (by decide +kernel)
def pv297967 : PrimeValue := ⟨297967, pr297967⟩
private theorem pr297971 : PrimeCertificate 297971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv83,pv359]) (by decide +kernel)
def pv297971 : PrimeValue := ⟨297971, pr297971⟩
private theorem pr298013 : PrimeCertificate 298013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13,pv521]) (by decide +kernel)
def pv298013 : PrimeValue := ⟨298013, pr298013⟩
private theorem pr298031 : PrimeCertificate 298031 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv29803]) (by decide +kernel)
def pv298031 : PrimeValue := ⟨298031, pr298031⟩
private theorem pr298063 : PrimeCertificate 298063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29,pv571]) (by decide +kernel)
def pv298063 : PrimeValue := ⟨298063, pr298063⟩
private theorem pr298087 : PrimeCertificate 298087 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv49681]) (by decide +kernel)
def pv298087 : PrimeValue := ⟨298087, pr298087⟩
private theorem pr298093 : PrimeCertificate 298093 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv24841]) (by decide +kernel)
def pv298093 : PrimeValue := ⟨298093, pr298093⟩
private theorem pr298171 : PrimeCertificate 298171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv3313]) (by decide +kernel)
def pv298171 : PrimeValue := ⟨298171, pr298171⟩
private theorem pr298201 : PrimeCertificate 298201 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv71]) (by decide +kernel)
def pv298201 : PrimeValue := ⟨298201, pr298201⟩
private theorem pr298211 : PrimeCertificate 298211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv2711]) (by decide +kernel)
def pv298211 : PrimeValue := ⟨298211, pr298211⟩
private theorem pr298213 : PrimeCertificate 298213 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv24851]) (by decide +kernel)
def pv298213 : PrimeValue := ⟨298213, pr298213⟩
private theorem pr298247 : PrimeCertificate 298247 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv11471]) (by decide +kernel)
def pv298247 : PrimeValue := ⟨298247, pr298247⟩
private theorem pr298261 : PrimeCertificate 298261 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv1657]) (by decide +kernel)
def pv298261 : PrimeValue := ⟨298261, pr298261⟩
private theorem pr298327 : PrimeCertificate 298327 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv7103]) (by decide +kernel)
def pv298327 : PrimeValue := ⟨298327, pr298327⟩
private theorem pr298343 : PrimeCertificate 298343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv71,pv191]) (by decide +kernel)
def pv298343 : PrimeValue := ⟨298343, pr298343⟩
private theorem pr298349 : PrimeCertificate 298349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv74587]) (by decide +kernel)
def pv298349 : PrimeValue := ⟨298349, pr298349⟩
private theorem pr298427 : PrimeCertificate 298427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv149213]) (by decide +kernel)
def pv298427 : PrimeValue := ⟨298427, pr298427⟩
private theorem pr298451 : PrimeCertificate 298451 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv47,pv127]) (by decide +kernel)
def pv298451 : PrimeValue := ⟨298451, pr298451⟩
private theorem pr298477 : PrimeCertificate 298477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv8291]) (by decide +kernel)
def pv298477 : PrimeValue := ⟨298477, pr298477⟩
private theorem pr298483 : PrimeCertificate 298483 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv49747]) (by decide +kernel)
def pv298483 : PrimeValue := ⟨298483, pr298483⟩
private theorem pr298559 : PrimeCertificate 298559 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv11483]) (by decide +kernel)
def pv298559 : PrimeValue := ⟨298559, pr298559⟩
private theorem pr298631 : PrimeCertificate 298631 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv29863]) (by decide +kernel)
def pv298631 : PrimeValue := ⟨298631, pr298631⟩
private theorem pr298681 : PrimeCertificate 298681 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv19,pv131]) (by decide +kernel)
def pv298681 : PrimeValue := ⟨298681, pr298681⟩
private theorem pr298687 : PrimeCertificate 298687 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv67,pv743]) (by decide +kernel)
def pv298687 : PrimeValue := ⟨298687, pr298687⟩
private theorem pr298691 : PrimeCertificate 298691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv17,pv251]) (by decide +kernel)
def pv298691 : PrimeValue := ⟨298691, pr298691⟩
private theorem pr298693 : PrimeCertificate 298693 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv8297]) (by decide +kernel)
def pv298693 : PrimeValue := ⟨298693, pr298693⟩
private theorem pr298709 : PrimeCertificate 298709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv1409]) (by decide +kernel)
def pv298709 : PrimeValue := ⟨298709, pr298709⟩
private theorem pr298723 : PrimeCertificate 298723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv49787]) (by decide +kernel)
def pv298723 : PrimeValue := ⟨298723, pr298723⟩
private theorem pr298757 : PrimeCertificate 298757 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv3931]) (by decide +kernel)
def pv298757 : PrimeValue := ⟨298757, pr298757⟩
private theorem pr298759 : PrimeCertificate 298759 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv29,pv101]) (by decide +kernel)
def pv298759 : PrimeValue := ⟨298759, pr298759⟩
private theorem pr298777 : PrimeCertificate 298777 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv59,pv211]) (by decide +kernel)
def pv298777 : PrimeValue := ⟨298777, pr298777⟩
private theorem pr298799 : PrimeCertificate 298799 :=
  certifyPrime (q := pv7) (ls := [pv2,pv149399]) (by decide +kernel)
def pv298799 : PrimeValue := ⟨298799, pr298799⟩
private theorem pr298819 : PrimeCertificate 298819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv1277]) (by decide +kernel)
def pv298819 : PrimeValue := ⟨298819, pr298819⟩
private theorem pr298841 : PrimeCertificate 298841 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv31,pv241]) (by decide +kernel)
def pv298841 : PrimeValue := ⟨298841, pr298841⟩
private theorem pr298853 : PrimeCertificate 298853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv74713]) (by decide +kernel)
def pv298853 : PrimeValue := ⟨298853, pr298853⟩
private theorem pr298861 : PrimeCertificate 298861 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv17,pv293]) (by decide +kernel)
def pv298861 : PrimeValue := ⟨298861, pr298861⟩
private theorem pr298897 : PrimeCertificate 298897 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv13,pv479]) (by decide +kernel)
def pv298897 : PrimeValue := ⟨298897, pr298897⟩
private theorem pr299053 : PrimeCertificate 299053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv71]) (by decide +kernel)
def pv299053 : PrimeValue := ⟨299053, pr299053⟩
private theorem pr299063 : PrimeCertificate 299063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv149531]) (by decide +kernel)
def pv299063 : PrimeValue := ⟨299063, pr299063⟩
private theorem pr299087 : PrimeCertificate 299087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv149543]) (by decide +kernel)
def pv299087 : PrimeValue := ⟨299087, pr299087⟩
private theorem pr299113 : PrimeCertificate 299113 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv103]) (by decide +kernel)
def pv299113 : PrimeValue := ⟨299113, pr299113⟩
private theorem pr299137 : PrimeCertificate 299137 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv41]) (by decide +kernel)
def pv299137 : PrimeValue := ⟨299137, pr299137⟩
private theorem pr299147 : PrimeCertificate 299147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv373,pv401]) (by decide +kernel)
def pv299147 : PrimeValue := ⟨299147, pr299147⟩
private theorem pr299179 : PrimeCertificate 299179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv1511]) (by decide +kernel)
def pv299179 : PrimeValue := ⟨299179, pr299179⟩
private theorem pr299197 : PrimeCertificate 299197 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv8311]) (by decide +kernel)
def pv299197 : PrimeValue := ⟨299197, pr299197⟩
private theorem pr299213 : PrimeCertificate 299213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv31,pv127]) (by decide +kernel)
def pv299213 : PrimeValue := ⟨299213, pr299213⟩
private theorem pr299281 : PrimeCertificate 299281 :=
  certifyPrime (q := pv79) (ls := [pv2,pv3,pv5,pv29,pv43]) (by decide +kernel)
def pv299281 : PrimeValue := ⟨299281, pr299281⟩
private theorem pr299311 : PrimeCertificate 299311 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv907]) (by decide +kernel)
def pv299311 : PrimeValue := ⟨299311, pr299311⟩
private theorem pr299317 : PrimeCertificate 299317 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv24943]) (by decide +kernel)
def pv299317 : PrimeValue := ⟨299317, pr299317⟩
private theorem pr299357 : PrimeCertificate 299357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67,pv1117]) (by decide +kernel)
def pv299357 : PrimeValue := ⟨299357, pr299357⟩
private theorem pr299359 : PrimeCertificate 299359 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv16631]) (by decide +kernel)
def pv299359 : PrimeValue := ⟨299359, pr299359⟩
private theorem pr299363 : PrimeCertificate 299363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv21383]) (by decide +kernel)
def pv299363 : PrimeValue := ⟨299363, pr299363⟩
private theorem pr299371 : PrimeCertificate 299371 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv17,pv587]) (by decide +kernel)
def pv299371 : PrimeValue := ⟨299371, pr299371⟩
private theorem pr299389 : PrimeCertificate 299389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61,pv409]) (by decide +kernel)
def pv299389 : PrimeValue := ⟨299389, pr299389⟩
private theorem pr299417 : PrimeCertificate 299417 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv2879]) (by decide +kernel)
def pv299417 : PrimeValue := ⟨299417, pr299417⟩
private theorem pr299471 : PrimeCertificate 299471 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv29947]) (by decide +kernel)
def pv299471 : PrimeValue := ⟨299471, pr299471⟩
private theorem pr299473 : PrimeCertificate 299473 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv367]) (by decide +kernel)
def pv299473 : PrimeValue := ⟨299473, pr299473⟩
private theorem pr299477 : PrimeCertificate 299477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv74869]) (by decide +kernel)
def pv299477 : PrimeValue := ⟨299477, pr299477⟩
private theorem pr299501 : PrimeCertificate 299501 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv599]) (by decide +kernel)
def pv299501 : PrimeValue := ⟨299501, pr299501⟩
private theorem pr299527 : PrimeCertificate 299527 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv49921]) (by decide +kernel)
def pv299527 : PrimeValue := ⟨299527, pr299527⟩
private theorem pr299539 : PrimeCertificate 299539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43]) (by decide +kernel)
def pv299539 : PrimeValue := ⟨299539, pr299539⟩
private theorem pr299569 : PrimeCertificate 299569 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv79]) (by decide +kernel)
def pv299569 : PrimeValue := ⟨299569, pr299569⟩
private theorem pr299617 : PrimeCertificate 299617 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv3121]) (by decide +kernel)
def pv299617 : PrimeValue := ⟨299617, pr299617⟩
private theorem pr299653 : PrimeCertificate 299653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv24971]) (by decide +kernel)
def pv299653 : PrimeValue := ⟨299653, pr299653⟩
private theorem pr299681 : PrimeCertificate 299681 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1873]) (by decide +kernel)
def pv299681 : PrimeValue := ⟨299681, pr299681⟩
private theorem pr299699 : PrimeCertificate 299699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv21407]) (by decide +kernel)
def pv299699 : PrimeValue := ⟨299699, pr299699⟩
private theorem pr299701 : PrimeCertificate 299701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv37]) (by decide +kernel)
def pv299701 : PrimeValue := ⟨299701, pr299701⟩
private theorem pr299731 : PrimeCertificate 299731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv97,pv103]) (by decide +kernel)
def pv299731 : PrimeValue := ⟨299731, pr299731⟩
private theorem pr299743 : PrimeCertificate 299743 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv49957]) (by decide +kernel)
def pv299743 : PrimeValue := ⟨299743, pr299743⟩
private theorem pr299749 : PrimeCertificate 299749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv24979]) (by decide +kernel)
def pv299749 : PrimeValue := ⟨299749, pr299749⟩
private theorem pr299771 : PrimeCertificate 299771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31,pv967]) (by decide +kernel)
def pv299771 : PrimeValue := ⟨299771, pr299771⟩
private theorem pr299861 : PrimeCertificate 299861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv29,pv47]) (by decide +kernel)
def pv299861 : PrimeValue := ⟨299861, pr299861⟩
private theorem pr299881 : PrimeCertificate 299881 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv7,pv17]) (by decide +kernel)
def pv299881 : PrimeValue := ⟨299881, pr299881⟩
private theorem pr299891 : PrimeCertificate 299891 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv29989]) (by decide +kernel)
def pv299891 : PrimeValue := ⟨299891, pr299891⟩
private theorem pr299909 : PrimeCertificate 299909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv10711]) (by decide +kernel)
def pv299909 : PrimeValue := ⟨299909, pr299909⟩
private theorem pr299933 : PrimeCertificate 299933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv167,pv449]) (by decide +kernel)
def pv299933 : PrimeValue := ⟨299933, pr299933⟩
private theorem pr299941 : PrimeCertificate 299941 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv4999]) (by decide +kernel)
def pv299941 : PrimeValue := ⟨299941, pr299941⟩
private theorem pr299969 : PrimeCertificate 299969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43,pv109]) (by decide +kernel)
def pv299969 : PrimeValue := ⟨299969, pr299969⟩
private theorem pr299977 : PrimeCertificate 299977 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv29,pv431]) (by decide +kernel)
def pv299977 : PrimeValue := ⟨299977, pr299977⟩
private theorem pr299983 : PrimeCertificate 299983 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv173]) (by decide +kernel)
def pv299983 : PrimeValue := ⟨299983, pr299983⟩
private theorem pr300017 : PrimeCertificate 300017 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv1103]) (by decide +kernel)
def pv300017 : PrimeValue := ⟨300017, pr300017⟩
private theorem pr300043 : PrimeCertificate 300043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv79,pv211]) (by decide +kernel)
def pv300043 : PrimeValue := ⟨300043, pr300043⟩
private theorem pr300119 : PrimeCertificate 300119 :=
  certifyPrime (q := pv29) (ls := [pv2,pv7,pv13,pv17,pv97]) (by decide +kernel)
def pv300119 : PrimeValue := ⟨300119, pr300119⟩
private theorem pr300137 : PrimeCertificate 300137 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37517]) (by decide +kernel)
def pv300137 : PrimeValue := ⟨300137, pr300137⟩
private theorem pr300151 : PrimeCertificate 300151 :=
  certifyPrime (q := pv61) (ls := [pv2,pv3,pv5,pv23,pv29]) (by decide +kernel)
def pv300151 : PrimeValue := ⟨300151, pr300151⟩
private theorem pr300163 : PrimeCertificate 300163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv2633]) (by decide +kernel)
def pv300163 : PrimeValue := ⟨300163, pr300163⟩
private theorem pr300193 : PrimeCertificate 300193 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv53,pv59]) (by decide +kernel)
def pv300193 : PrimeValue := ⟨300193, pr300193⟩
private theorem pr300229 : PrimeCertificate 300229 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv127,pv197]) (by decide +kernel)
def pv300229 : PrimeValue := ⟨300229, pr300229⟩
private theorem pr300247 : PrimeCertificate 300247 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv163,pv307]) (by decide +kernel)
def pv300247 : PrimeValue := ⟨300247, pr300247⟩
private theorem pr300317 : PrimeCertificate 300317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv75079]) (by decide +kernel)
def pv300317 : PrimeValue := ⟨300317, pr300317⟩
private theorem pr300319 : PrimeCertificate 300319 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv50053]) (by decide +kernel)
def pv300319 : PrimeValue := ⟨300319, pr300319⟩
private theorem pr300343 : PrimeCertificate 300343 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv7151]) (by decide +kernel)
def pv300343 : PrimeValue := ⟨300343, pr300343⟩
private theorem pr300347 : PrimeCertificate 300347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv263,pv571]) (by decide +kernel)
def pv300347 : PrimeValue := ⟨300347, pr300347⟩
private theorem pr300367 : PrimeCertificate 300367 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv37,pv41]) (by decide +kernel)
def pv300367 : PrimeValue := ⟨300367, pr300367⟩
private theorem pr300397 : PrimeCertificate 300397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv25033]) (by decide +kernel)
def pv300397 : PrimeValue := ⟨300397, pr300397⟩
private theorem pr300413 : PrimeCertificate 300413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv10729]) (by decide +kernel)
def pv300413 : PrimeValue := ⟨300413, pr300413⟩
private theorem pr300427 : PrimeCertificate 300427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv23,pv311]) (by decide +kernel)
def pv300427 : PrimeValue := ⟨300427, pr300427⟩
private theorem pr300463 : PrimeCertificate 300463 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv50077]) (by decide +kernel)
def pv300463 : PrimeValue := ⟨300463, pr300463⟩
private theorem pr300491 : PrimeCertificate 300491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv151,pv199]) (by decide +kernel)
def pv300491 : PrimeValue := ⟨300491, pr300491⟩
private theorem pr300497 : PrimeCertificate 300497 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv2683]) (by decide +kernel)
def pv300497 : PrimeValue := ⟨300497, pr300497⟩
private theorem pr300583 : PrimeCertificate 300583 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv16699]) (by decide +kernel)
def pv300583 : PrimeValue := ⟨300583, pr300583⟩
private theorem pr300593 : PrimeCertificate 300593 :=
  certifyPrime (q := pv3) (ls := [pv2,pv18787]) (by decide +kernel)
def pv300593 : PrimeValue := ⟨300593, pr300593⟩
private theorem pr300623 : PrimeCertificate 300623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv109,pv197]) (by decide +kernel)
def pv300623 : PrimeValue := ⟨300623, pr300623⟩
private theorem pr300719 : PrimeCertificate 300719 :=
  certifyPrime (q := pv19) (ls := [pv2,pv11,pv13669]) (by decide +kernel)
def pv300719 : PrimeValue := ⟨300719, pr300719⟩
private theorem pr300733 : PrimeCertificate 300733 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv1319]) (by decide +kernel)
def pv300733 : PrimeValue := ⟨300733, pr300733⟩
private theorem pr300743 : PrimeCertificate 300743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv43,pv269]) (by decide +kernel)
def pv300743 : PrimeValue := ⟨300743, pr300743⟩
private theorem pr300779 : PrimeCertificate 300779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv101,pv1489]) (by decide +kernel)
def pv300779 : PrimeValue := ⟨300779, pr300779⟩
private theorem pr300787 : PrimeCertificate 300787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv50131]) (by decide +kernel)
def pv300787 : PrimeValue := ⟨300787, pr300787⟩
private theorem pr300821 : PrimeCertificate 300821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv89]) (by decide +kernel)
def pv300821 : PrimeValue := ⟨300821, pr300821⟩
private theorem pr300823 : PrimeCertificate 300823 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv181,pv277]) (by decide +kernel)
def pv300823 : PrimeValue := ⟨300823, pr300823⟩
private theorem pr300857 : PrimeCertificate 300857 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37607]) (by decide +kernel)
def pv300857 : PrimeValue := ⟨300857, pr300857⟩
private theorem pr300877 : PrimeCertificate 300877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv25073]) (by decide +kernel)
def pv300877 : PrimeValue := ⟨300877, pr300877⟩
private theorem pr300889 : PrimeCertificate 300889 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv199]) (by decide +kernel)
def pv300889 : PrimeValue := ⟨300889, pr300889⟩
private theorem pr300893 : PrimeCertificate 300893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv75223]) (by decide +kernel)
def pv300893 : PrimeValue := ⟨300893, pr300893⟩
private theorem pr300931 : PrimeCertificate 300931 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv1433]) (by decide +kernel)
def pv300931 : PrimeValue := ⟨300931, pr300931⟩
private theorem pr300961 : PrimeCertificate 300961 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv19]) (by decide +kernel)
def pv300961 : PrimeValue := ⟨300961, pr300961⟩
private theorem pr300973 : PrimeCertificate 300973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv3583]) (by decide +kernel)
def pv300973 : PrimeValue := ⟨300973, pr300973⟩
private theorem pr300977 : PrimeCertificate 300977 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv1447]) (by decide +kernel)
def pv300977 : PrimeValue := ⟨300977, pr300977⟩
private theorem pr300997 : PrimeCertificate 300997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv929]) (by decide +kernel)
def pv300997 : PrimeValue := ⟨300997, pr300997⟩
private theorem pr301039 : PrimeCertificate 301039 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv131,pv383]) (by decide +kernel)
def pv301039 : PrimeValue := ⟨301039, pr301039⟩
private theorem pr301123 : PrimeCertificate 301123 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv16729]) (by decide +kernel)
def pv301123 : PrimeValue := ⟨301123, pr301123⟩
private theorem pr301153 : PrimeCertificate 301153 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3137]) (by decide +kernel)
def pv301153 : PrimeValue := ⟨301153, pr301153⟩
private theorem pr301177 : PrimeCertificate 301177 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv47,pv89]) (by decide +kernel)
def pv301177 : PrimeValue := ⟨301177, pr301177⟩
private theorem pr301211 : PrimeCertificate 301211 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv13,pv331]) (by decide +kernel)
def pv301211 : PrimeValue := ⟨301211, pr301211⟩
private theorem pr301319 : PrimeCertificate 301319 :=
  certifyPrime (q := pv7) (ls := [pv2,pv150659]) (by decide +kernel)
def pv301319 : PrimeValue := ⟨301319, pr301319⟩
private theorem pr301331 : PrimeCertificate 301331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv30133]) (by decide +kernel)
def pv301331 : PrimeValue := ⟨301331, pr301331⟩
private theorem pr301333 : PrimeCertificate 301333 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv25111]) (by decide +kernel)
def pv301333 : PrimeValue := ⟨301333, pr301333⟩
private theorem pr301361 : PrimeCertificate 301361 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv3767]) (by decide +kernel)
def pv301361 : PrimeValue := ⟨301361, pr301361⟩
private theorem pr301423 : PrimeCertificate 301423 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv4567]) (by decide +kernel)
def pv301423 : PrimeValue := ⟨301423, pr301423⟩
private theorem pr301429 : PrimeCertificate 301429 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv2791]) (by decide +kernel)
def pv301429 : PrimeValue := ⟨301429, pr301429⟩
private theorem pr301447 : PrimeCertificate 301447 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv16747]) (by decide +kernel)
def pv301447 : PrimeValue := ⟨301447, pr301447⟩
private theorem pr301487 : PrimeCertificate 301487 :=
  certifyPrime (q := pv5) (ls := [pv2,pv150743]) (by decide +kernel)
def pv301487 : PrimeValue := ⟨301487, pr301487⟩
private theorem pr301493 : PrimeCertificate 301493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv3967]) (by decide +kernel)
def pv301493 : PrimeValue := ⟨301493, pr301493⟩
private theorem pr301577 : PrimeCertificate 301577 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv23,pv149]) (by decide +kernel)
def pv301577 : PrimeValue := ⟨301577, pr301577⟩
private theorem pr301579 : PrimeCertificate 301579 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv50263]) (by decide +kernel)
def pv301579 : PrimeValue := ⟨301579, pr301579⟩
private theorem pr301591 : PrimeCertificate 301591 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv1117]) (by decide +kernel)
def pv301591 : PrimeValue := ⟨301591, pr301591⟩
private theorem pr301601 : PrimeCertificate 301601 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv13,pv29]) (by decide +kernel)
def pv301601 : PrimeValue := ⟨301601, pr301601⟩
private theorem pr301627 : PrimeCertificate 301627 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv1289]) (by decide +kernel)
def pv301627 : PrimeValue := ⟨301627, pr301627⟩
private theorem pr301643 : PrimeCertificate 301643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13711]) (by decide +kernel)
def pv301643 : PrimeValue := ⟨301643, pr301643⟩
private theorem pr301669 : PrimeCertificate 301669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv1093]) (by decide +kernel)
def pv301669 : PrimeValue := ⟨301669, pr301669⟩
private theorem pr301681 : PrimeCertificate 301681 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv419]) (by decide +kernel)
def pv301681 : PrimeValue := ⟨301681, pr301681⟩
private theorem pr301703 : PrimeCertificate 301703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv251,pv601]) (by decide +kernel)
def pv301703 : PrimeValue := ⟨301703, pr301703⟩
private theorem pr301747 : PrimeCertificate 301747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv50291]) (by decide +kernel)
def pv301747 : PrimeValue := ⟨301747, pr301747⟩
private theorem pr301751 : PrimeCertificate 301751 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv17,pv71]) (by decide +kernel)
def pv301751 : PrimeValue := ⟨301751, pr301751⟩
private theorem pr301831 : PrimeCertificate 301831 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv10061]) (by decide +kernel)
def pv301831 : PrimeValue := ⟨301831, pr301831⟩
private theorem pr301843 : PrimeCertificate 301843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv409]) (by decide +kernel)
def pv301843 : PrimeValue := ⟨301843, pr301843⟩
private theorem pr301901 : PrimeCertificate 301901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv3019]) (by decide +kernel)
def pv301901 : PrimeValue := ⟨301901, pr301901⟩
private theorem pr301907 : PrimeCertificate 301907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13723]) (by decide +kernel)
def pv301907 : PrimeValue := ⟨301907, pr301907⟩
private theorem pr301949 : PrimeCertificate 301949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv29,pv137]) (by decide +kernel)
def pv301949 : PrimeValue := ⟨301949, pr301949⟩
private theorem pr301993 : PrimeCertificate 301993 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv12583]) (by decide +kernel)
def pv301993 : PrimeValue := ⟨301993, pr301993⟩
private theorem pr301997 : PrimeCertificate 301997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv103,pv733]) (by decide +kernel)
def pv301997 : PrimeValue := ⟨301997, pr301997⟩
private theorem pr302111 : PrimeCertificate 302111 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv30211]) (by decide +kernel)
def pv302111 : PrimeValue := ⟨302111, pr302111⟩
private theorem pr302143 : PrimeCertificate 302143 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37,pv1361]) (by decide +kernel)
def pv302143 : PrimeValue := ⟨302143, pr302143⟩
private theorem pr302167 : PrimeCertificate 302167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv16787]) (by decide +kernel)
def pv302167 : PrimeValue := ⟨302167, pr302167⟩
private theorem pr302171 : PrimeCertificate 302171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv41,pv67]) (by decide +kernel)
def pv302171 : PrimeValue := ⟨302171, pr302171⟩
private theorem pr302173 : PrimeCertificate 302173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv149]) (by decide +kernel)
def pv302173 : PrimeValue := ⟨302173, pr302173⟩
private theorem pr302189 : PrimeCertificate 302189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv2437]) (by decide +kernel)
def pv302189 : PrimeValue := ⟨302189, pr302189⟩
private theorem pr302213 : PrimeCertificate 302213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv75553]) (by decide +kernel)
def pv302213 : PrimeValue := ⟨302213, pr302213⟩
private theorem pr302221 : PrimeCertificate 302221 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv23,pv73]) (by decide +kernel)
def pv302221 : PrimeValue := ⟨302221, pr302221⟩
private theorem pr302273 : PrimeCertificate 302273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv4723]) (by decide +kernel)
def pv302273 : PrimeValue := ⟨302273, pr302273⟩
private theorem pr302279 : PrimeCertificate 302279 :=
  certifyPrime (q := pv23) (ls := [pv2,pv359,pv421]) (by decide +kernel)
def pv302279 : PrimeValue := ⟨302279, pr302279⟩
private theorem pr302287 : PrimeCertificate 302287 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv83,pv607]) (by decide +kernel)
def pv302287 : PrimeValue := ⟨302287, pr302287⟩
private theorem pr302317 : PrimeCertificate 302317 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv59,pv61]) (by decide +kernel)
def pv302317 : PrimeValue := ⟨302317, pr302317⟩
private theorem pr302411 : PrimeCertificate 302411 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv30241]) (by decide +kernel)
def pv302411 : PrimeValue := ⟨302411, pr302411⟩
private theorem pr302429 : PrimeCertificate 302429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv1543]) (by decide +kernel)
def pv302429 : PrimeValue := ⟨302429, pr302429⟩
private theorem pr302443 : PrimeCertificate 302443 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv19,pv379]) (by decide +kernel)
def pv302443 : PrimeValue := ⟨302443, pr302443⟩
private theorem pr302507 : PrimeCertificate 302507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv151253]) (by decide +kernel)
def pv302507 : PrimeValue := ⟨302507, pr302507⟩
private theorem pr302551 : PrimeCertificate 302551 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv2017]) (by decide +kernel)
def pv302551 : PrimeValue := ⟨302551, pr302551⟩
private theorem pr302567 : PrimeCertificate 302567 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv17,pv809]) (by decide +kernel)
def pv302567 : PrimeValue := ⟨302567, pr302567⟩
private theorem pr302573 : PrimeCertificate 302573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67,pv1129]) (by decide +kernel)
def pv302573 : PrimeValue := ⟨302573, pr302573⟩
private theorem pr302579 : PrimeCertificate 302579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv151289]) (by decide +kernel)
def pv302579 : PrimeValue := ⟨302579, pr302579⟩
private theorem pr302587 : PrimeCertificate 302587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv37,pv47]) (by decide +kernel)
def pv302587 : PrimeValue := ⟨302587, pr302587⟩
private theorem pr302593 : PrimeCertificate 302593 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv197]) (by decide +kernel)
def pv302593 : PrimeValue := ⟨302593, pr302593⟩
private theorem pr302647 : PrimeCertificate 302647 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv50441]) (by decide +kernel)
def pv302647 : PrimeValue := ⟨302647, pr302647⟩
private theorem pr302681 : PrimeCertificate 302681 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv23,pv47]) (by decide +kernel)
def pv302681 : PrimeValue := ⟨302681, pr302681⟩
private theorem pr302759 : PrimeCertificate 302759 :=
  certifyPrime (q := pv7) (ls := [pv2,pv151379]) (by decide +kernel)
def pv302759 : PrimeValue := ⟨302759, pr302759⟩
private theorem pr302801 : PrimeCertificate 302801 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv757]) (by decide +kernel)
def pv302801 : PrimeValue := ⟨302801, pr302801⟩
private theorem pr302831 : PrimeCertificate 302831 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv2753]) (by decide +kernel)
def pv302831 : PrimeValue := ⟨302831, pr302831⟩
private theorem pr302833 : PrimeCertificate 302833 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv701]) (by decide +kernel)
def pv302833 : PrimeValue := ⟨302833, pr302833⟩
private theorem pr302837 : PrimeCertificate 302837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv75709]) (by decide +kernel)
def pv302837 : PrimeValue := ⟨302837, pr302837⟩
private theorem pr302843 : PrimeCertificate 302843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv2857]) (by decide +kernel)
def pv302843 : PrimeValue := ⟨302843, pr302843⟩
private theorem pr302851 : PrimeCertificate 302851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv673]) (by decide +kernel)
def pv302851 : PrimeValue := ⟨302851, pr302851⟩
private theorem pr302927 : PrimeCertificate 302927 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv61,pv191]) (by decide +kernel)
def pv302927 : PrimeValue := ⟨302927, pr302927⟩
private theorem pr302969 : PrimeCertificate 302969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37871]) (by decide +kernel)
def pv302969 : PrimeValue := ⟨302969, pr302969⟩
private theorem pr302971 : PrimeCertificate 302971 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv10099]) (by decide +kernel)
def pv302971 : PrimeValue := ⟨302971, pr302971⟩
private theorem pr302977 : PrimeCertificate 302977 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv263]) (by decide +kernel)
def pv302977 : PrimeValue := ⟨302977, pr302977⟩
private theorem pr302983 : PrimeCertificate 302983 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv50497]) (by decide +kernel)
def pv302983 : PrimeValue := ⟨302983, pr302983⟩
private theorem pr303011 : PrimeCertificate 303011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv157,pv193]) (by decide +kernel)
def pv303011 : PrimeValue := ⟨303011, pr303011⟩
private theorem pr303013 : PrimeCertificate 303013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv443]) (by decide +kernel)
def pv303013 : PrimeValue := ⟨303013, pr303013⟩
private theorem pr303019 : PrimeCertificate 303019 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv50503]) (by decide +kernel)
def pv303019 : PrimeValue := ⟨303019, pr303019⟩
private theorem pr303029 : PrimeCertificate 303029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv71,pv97]) (by decide +kernel)
def pv303029 : PrimeValue := ⟨303029, pr303029⟩
private theorem pr303073 : PrimeCertificate 303073 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv41]) (by decide +kernel)
def pv303073 : PrimeValue := ⟨303073, pr303073⟩
private theorem pr303089 : PrimeCertificate 303089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv997]) (by decide +kernel)
def pv303089 : PrimeValue := ⟨303089, pr303089⟩
private theorem pr303097 : PrimeCertificate 303097 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv73,pv173]) (by decide +kernel)
def pv303097 : PrimeValue := ⟨303097, pr303097⟩
private theorem pr303119 : PrimeCertificate 303119 :=
  certifyPrime (q := pv11) (ls := [pv2,pv31,pv4889]) (by decide +kernel)
def pv303119 : PrimeValue := ⟨303119, pr303119⟩
private theorem pr303157 : PrimeCertificate 303157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv401]) (by decide +kernel)
def pv303157 : PrimeValue := ⟨303157, pr303157⟩
private theorem pr303187 : PrimeCertificate 303187 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv23]) (by decide +kernel)
def pv303187 : PrimeValue := ⟨303187, pr303187⟩
private theorem pr303257 : PrimeCertificate 303257 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37907]) (by decide +kernel)
def pv303257 : PrimeValue := ⟨303257, pr303257⟩
private theorem pr303283 : PrimeCertificate 303283 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv29,pv83]) (by decide +kernel)
def pv303283 : PrimeValue := ⟨303283, pr303283⟩
private theorem pr303287 : PrimeCertificate 303287 :=
  certifyPrime (q := pv5) (ls := [pv2,pv151643]) (by decide +kernel)
def pv303287 : PrimeValue := ⟨303287, pr303287⟩
private theorem pr303293 : PrimeCertificate 303293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv61,pv113]) (by decide +kernel)
def pv303293 : PrimeValue := ⟨303293, pr303293⟩
private theorem pr303307 : PrimeCertificate 303307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv50551]) (by decide +kernel)
def pv303307 : PrimeValue := ⟨303307, pr303307⟩
private theorem pr303313 : PrimeCertificate 303313 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv71,pv89]) (by decide +kernel)
def pv303313 : PrimeValue := ⟨303313, pr303313⟩
private theorem pr303337 : PrimeCertificate 303337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv383]) (by decide +kernel)
def pv303337 : PrimeValue := ⟨303337, pr303337⟩
private theorem pr303341 : PrimeCertificate 303341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29,pv523]) (by decide +kernel)
def pv303341 : PrimeValue := ⟨303341, pr303341⟩
private theorem pr303367 : PrimeCertificate 303367 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv31,pv233]) (by decide +kernel)
def pv303367 : PrimeValue := ⟨303367, pr303367⟩
private theorem pr303371 : PrimeCertificate 303371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv1319]) (by decide +kernel)
def pv303371 : PrimeValue := ⟨303371, pr303371⟩
private theorem pr303379 : PrimeCertificate 303379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv59,pv857]) (by decide +kernel)
def pv303379 : PrimeValue := ⟨303379, pr303379⟩
private theorem pr303421 : PrimeCertificate 303421 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv13,pv389]) (by decide +kernel)
def pv303421 : PrimeValue := ⟨303421, pr303421⟩
private theorem pr303431 : PrimeCertificate 303431 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv19,pv1597]) (by decide +kernel)
def pv303431 : PrimeValue := ⟨303431, pr303431⟩
private theorem pr303491 : PrimeCertificate 303491 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv31,pv89]) (by decide +kernel)
def pv303491 : PrimeValue := ⟨303491, pr303491⟩
private theorem pr303497 : PrimeCertificate 303497 :=
  certifyPrime (q := pv3) (ls := [pv2,pv59,pv643]) (by decide +kernel)
def pv303497 : PrimeValue := ⟨303497, pr303497⟩
private theorem pr303529 : PrimeCertificate 303529 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv12647]) (by decide +kernel)
def pv303529 : PrimeValue := ⟨303529, pr303529⟩
private theorem pr303539 : PrimeCertificate 303539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv151769]) (by decide +kernel)
def pv303539 : PrimeValue := ⟨303539, pr303539⟩
private theorem pr303547 : PrimeCertificate 303547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv50591]) (by decide +kernel)
def pv303547 : PrimeValue := ⟨303547, pr303547⟩
private theorem pr303553 : PrimeCertificate 303553 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv31]) (by decide +kernel)
def pv303553 : PrimeValue := ⟨303553, pr303553⟩
private theorem pr303571 : PrimeCertificate 303571 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv3373]) (by decide +kernel)
def pv303571 : PrimeValue := ⟨303571, pr303571⟩
private theorem pr303581 : PrimeCertificate 303581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv43,pv353]) (by decide +kernel)
def pv303581 : PrimeValue := ⟨303581, pr303581⟩
private theorem pr303613 : PrimeCertificate 303613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv25301]) (by decide +kernel)
def pv303613 : PrimeValue := ⟨303613, pr303613⟩
private theorem pr303643 : PrimeCertificate 303643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5623]) (by decide +kernel)
def pv303643 : PrimeValue := ⟨303643, pr303643⟩
private theorem pr303647 : PrimeCertificate 303647 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv23,pv41]) (by decide +kernel)
def pv303647 : PrimeValue := ⟨303647, pr303647⟩
private theorem pr303649 : PrimeCertificate 303649 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv3163]) (by decide +kernel)
def pv303649 : PrimeValue := ⟨303649, pr303649⟩
private theorem pr303691 : PrimeCertificate 303691 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv53,pv191]) (by decide +kernel)
def pv303691 : PrimeValue := ⟨303691, pr303691⟩
private theorem pr303703 : PrimeCertificate 303703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv1033]) (by decide +kernel)
def pv303703 : PrimeValue := ⟨303703, pr303703⟩
private theorem pr303727 : PrimeCertificate 303727 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv223,pv227]) (by decide +kernel)
def pv303727 : PrimeValue := ⟨303727, pr303727⟩
private theorem pr303817 : PrimeCertificate 303817 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv12659]) (by decide +kernel)
def pv303817 : PrimeValue := ⟨303817, pr303817⟩
private theorem pr303827 : PrimeCertificate 303827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv2081]) (by decide +kernel)
def pv303827 : PrimeValue := ⟨303827, pr303827⟩
private theorem pr303859 : PrimeCertificate 303859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv331]) (by decide +kernel)
def pv303859 : PrimeValue := ⟨303859, pr303859⟩
private theorem pr303889 : PrimeCertificate 303889 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv13,pv487]) (by decide +kernel)
def pv303889 : PrimeValue := ⟨303889, pr303889⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
