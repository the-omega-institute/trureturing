/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table059
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table059.pv172517
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table007
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table008
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table012
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table033

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr172517 : Nat.Prime 172517 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv43,pv59]) (by decide +kernel)
def pv172517 : PrimeValue := ⟨172517, pr172517⟩
private theorem pr172519 : Nat.Prime 172519 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv28753]) (by decide +kernel)
def pv172519 : PrimeValue := ⟨172519, pr172519⟩
private theorem pr172541 : Nat.Prime 172541 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv8627]) (by decide +kernel)
def pv172541 : PrimeValue := ⟨172541, pr172541⟩
private theorem pr172553 : Nat.Prime 172553 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv21569]) (by decide +kernel)
def pv172553 : PrimeValue := ⟨172553, pr172553⟩
private theorem pr172573 : Nat.Prime 172573 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv73,pv197]) (by decide +kernel)
def pv172573 : PrimeValue := ⟨172573, pr172573⟩
private theorem pr172583 : Nat.Prime 172583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv86291]) (by decide +kernel)
def pv172583 : PrimeValue := ⟨172583, pr172583⟩
private theorem pr172589 : Nat.Prime 172589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv3319]) (by decide +kernel)
def pv172589 : PrimeValue := ⟨172589, pr172589⟩
private theorem pr172597 : Nat.Prime 172597 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv757]) (by decide +kernel)
def pv172597 : PrimeValue := ⟨172597, pr172597⟩
private theorem pr172603 : Nat.Prime 172603 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv43,pv223]) (by decide +kernel)
def pv172603 : PrimeValue := ⟨172603, pr172603⟩
private theorem pr172619 : Nat.Prime 172619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv5077]) (by decide +kernel)
def pv172619 : PrimeValue := ⟨172619, pr172619⟩
private theorem pr172633 : Nat.Prime 172633 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7193]) (by decide +kernel)
def pv172633 : PrimeValue := ⟨172633, pr172633⟩
private theorem pr172649 : Nat.Prime 172649 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv3083]) (by decide +kernel)
def pv172649 : PrimeValue := ⟨172649, pr172649⟩
private theorem pr172657 : Nat.Prime 172657 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv11,pv109]) (by decide +kernel)
def pv172657 : PrimeValue := ⟨172657, pr172657⟩
private theorem pr172663 : Nat.Prime 172663 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv4111]) (by decide +kernel)
def pv172663 : PrimeValue := ⟨172663, pr172663⟩
private theorem pr172673 : Nat.Prime 172673 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv71]) (by decide +kernel)
def pv172673 : PrimeValue := ⟨172673, pr172673⟩
private theorem pr172681 : Nat.Prime 172681 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv1439]) (by decide +kernel)
def pv172681 : PrimeValue := ⟨172681, pr172681⟩
private theorem pr172687 : Nat.Prime 172687 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv1693]) (by decide +kernel)
def pv172687 : PrimeValue := ⟨172687, pr172687⟩
private theorem pr172717 : Nat.Prime 172717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv389]) (by decide +kernel)
def pv172717 : PrimeValue := ⟨172717, pr172717⟩
private theorem pr172721 : Nat.Prime 172721 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17,pv127]) (by decide +kernel)
def pv172721 : PrimeValue := ⟨172721, pr172721⟩
private theorem pr172741 : Nat.Prime 172741 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv2879]) (by decide +kernel)
def pv172741 : PrimeValue := ⟨172741, pr172741⟩
private theorem pr172759 : Nat.Prime 172759 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv28793]) (by decide +kernel)
def pv172759 : PrimeValue := ⟨172759, pr172759⟩
private theorem pr172787 : Nat.Prime 172787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv4547]) (by decide +kernel)
def pv172787 : PrimeValue := ⟨172787, pr172787⟩
private theorem pr172801 : Nat.Prime 172801 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv172801 : PrimeValue := ⟨172801, pr172801⟩
private theorem pr172807 : Nat.Prime 172807 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv83,pv347]) (by decide +kernel)
def pv172807 : PrimeValue := ⟨172807, pr172807⟩
private theorem pr172829 : Nat.Prime 172829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43207]) (by decide +kernel)
def pv172829 : PrimeValue := ⟨172829, pr172829⟩
private theorem pr172853 : Nat.Prime 172853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79,pv547]) (by decide +kernel)
def pv172853 : PrimeValue := ⟨172853, pr172853⟩
private theorem pr172867 : Nat.Prime 172867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv47,pv613]) (by decide +kernel)
def pv172867 : PrimeValue := ⟨172867, pr172867⟩
private theorem pr172871 : Nat.Prime 172871 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv59,pv293]) (by decide +kernel)
def pv172871 : PrimeValue := ⟨172871, pr172871⟩
private theorem pr172877 : Nat.Prime 172877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv3929]) (by decide +kernel)
def pv172877 : PrimeValue := ⟨172877, pr172877⟩
private theorem pr172933 : Nat.Prime 172933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv14411]) (by decide +kernel)
def pv172933 : PrimeValue := ⟨172933, pr172933⟩
private theorem pr172969 : Nat.Prime 172969 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7207]) (by decide +kernel)
def pv172969 : PrimeValue := ⟨172969, pr172969⟩
private theorem pr172973 : Nat.Prime 172973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv83,pv521]) (by decide +kernel)
def pv172973 : PrimeValue := ⟨172973, pr172973⟩
private theorem pr172981 : Nat.Prime 172981 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv31]) (by decide +kernel)
def pv172981 : PrimeValue := ⟨172981, pr172981⟩
private theorem pr172987 : Nat.Prime 172987 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv2621]) (by decide +kernel)
def pv172987 : PrimeValue := ⟨172987, pr172987⟩
private theorem pr172993 : Nat.Prime 172993 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv53]) (by decide +kernel)
def pv172993 : PrimeValue := ⟨172993, pr172993⟩
private theorem pr172999 : Nat.Prime 172999 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv1373]) (by decide +kernel)
def pv172999 : PrimeValue := ⟨172999, pr172999⟩
private theorem pr173021 : Nat.Prime 173021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv41,pv211]) (by decide +kernel)
def pv173021 : PrimeValue := ⟨173021, pr173021⟩
private theorem pr173039 : Nat.Prime 173039 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv241,pv359]) (by decide +kernel)
def pv173039 : PrimeValue := ⟨173039, pr173039⟩
private theorem pr173053 : Nat.Prime 173053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv19,pv23]) (by decide +kernel)
def pv173053 : PrimeValue := ⟨173053, pr173053⟩
private theorem pr173059 : Nat.Prime 173059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv28843]) (by decide +kernel)
def pv173059 : PrimeValue := ⟨173059, pr173059⟩
private theorem pr173081 : Nat.Prime 173081 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv4327]) (by decide +kernel)
def pv173081 : PrimeValue := ⟨173081, pr173081⟩
private theorem pr173087 : Nat.Prime 173087 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv37,pv2339]) (by decide +kernel)
def pv173087 : PrimeValue := ⟨173087, pr173087⟩
private theorem pr173099 : Nat.Prime 173099 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv53,pv71]) (by decide +kernel)
def pv173099 : PrimeValue := ⟨173099, pr173099⟩
private theorem pr173137 : Nat.Prime 173137 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv3607]) (by decide +kernel)
def pv173137 : PrimeValue := ⟨173137, pr173137⟩
private theorem pr173141 : Nat.Prime 173141 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv787]) (by decide +kernel)
def pv173141 : PrimeValue := ⟨173141, pr173141⟩
private theorem pr173149 : Nat.Prime 173149 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv47,pv307]) (by decide +kernel)
def pv173149 : PrimeValue := ⟨173149, pr173149⟩
private theorem pr173177 : Nat.Prime 173177 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv21647]) (by decide +kernel)
def pv173177 : PrimeValue := ⟨173177, pr173177⟩
private theorem pr173183 : Nat.Prime 173183 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv131,pv661]) (by decide +kernel)
def pv173183 : PrimeValue := ⟨173183, pr173183⟩
private theorem pr173191 : Nat.Prime 173191 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv23,pv251]) (by decide +kernel)
def pv173191 : PrimeValue := ⟨173191, pr173191⟩
private theorem pr173209 : Nat.Prime 173209 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv7,pv1031]) (by decide +kernel)
def pv173209 : PrimeValue := ⟨173209, pr173209⟩
private theorem pr173219 : Nat.Prime 173219 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv257,pv337]) (by decide +kernel)
def pv173219 : PrimeValue := ⟨173219, pr173219⟩
private theorem pr173249 : Nat.Prime 173249 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2707]) (by decide +kernel)
def pv173249 : PrimeValue := ⟨173249, pr173249⟩
private theorem pr173263 : Nat.Prime 173263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv67,pv431]) (by decide +kernel)
def pv173263 : PrimeValue := ⟨173263, pr173263⟩
private theorem pr173267 : Nat.Prime 173267 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv2113]) (by decide +kernel)
def pv173267 : PrimeValue := ⟨173267, pr173267⟩
private theorem pr173273 : Nat.Prime 173273 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv179]) (by decide +kernel)
def pv173273 : PrimeValue := ⟨173273, pr173273⟩
private theorem pr173297 : Nat.Prime 173297 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv10831]) (by decide +kernel)
def pv173297 : PrimeValue := ⟨173297, pr173297⟩
private theorem pr173309 : Nat.Prime 173309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv1171]) (by decide +kernel)
def pv173309 : PrimeValue := ⟨173309, pr173309⟩
private theorem pr173357 : Nat.Prime 173357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv2281]) (by decide +kernel)
def pv173357 : PrimeValue := ⟨173357, pr173357⟩
private theorem pr173359 : Nat.Prime 173359 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv9631]) (by decide +kernel)
def pv173359 : PrimeValue := ⟨173359, pr173359⟩
private theorem pr173429 : Nat.Prime 173429 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv191,pv227]) (by decide +kernel)
def pv173429 : PrimeValue := ⟨173429, pr173429⟩
private theorem pr173431 : Nat.Prime 173431 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv41,pv47]) (by decide +kernel)
def pv173431 : PrimeValue := ⟨173431, pr173431⟩
private theorem pr173473 : Nat.Prime 173473 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv139]) (by decide +kernel)
def pv173473 : PrimeValue := ⟨173473, pr173473⟩
private theorem pr173483 : Nat.Prime 173483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv127,pv683]) (by decide +kernel)
def pv173483 : PrimeValue := ⟨173483, pr173483⟩
private theorem pr173491 : Nat.Prime 173491 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv5,pv5783]) (by decide +kernel)
def pv173491 : PrimeValue := ⟨173491, pr173491⟩
private theorem pr173497 : Nat.Prime 173497 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7229]) (by decide +kernel)
def pv173497 : PrimeValue := ⟨173497, pr173497⟩
private theorem pr173501 : Nat.Prime 173501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv347]) (by decide +kernel)
def pv173501 : PrimeValue := ⟨173501, pr173501⟩
private theorem pr173531 : Nat.Prime 173531 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv37,pv67]) (by decide +kernel)
def pv173531 : PrimeValue := ⟨173531, pr173531⟩
private theorem pr173539 : Nat.Prime 173539 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv31,pv311]) (by decide +kernel)
def pv173539 : PrimeValue := ⟨173539, pr173539⟩
private theorem pr173549 : Nat.Prime 173549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv1009]) (by decide +kernel)
def pv173549 : PrimeValue := ⟨173549, pr173549⟩
private theorem pr173629 : Nat.Prime 173629 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv7,pv13,pv53]) (by decide +kernel)
def pv173629 : PrimeValue := ⟨173629, pr173629⟩
private theorem pr173647 : Nat.Prime 173647 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv877]) (by decide +kernel)
def pv173647 : PrimeValue := ⟨173647, pr173647⟩
private theorem pr173651 : Nat.Prime 173651 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23,pv151]) (by decide +kernel)
def pv173651 : PrimeValue := ⟨173651, pr173651⟩
private theorem pr173669 : Nat.Prime 173669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv3947]) (by decide +kernel)
def pv173669 : PrimeValue := ⟨173669, pr173669⟩
private theorem pr173671 : Nat.Prime 173671 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv827]) (by decide +kernel)
def pv173671 : PrimeValue := ⟨173671, pr173671⟩
private theorem pr173683 : Nat.Prime 173683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv9649]) (by decide +kernel)
def pv173683 : PrimeValue := ⟨173683, pr173683⟩
private theorem pr173687 : Nat.Prime 173687 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv86843]) (by decide +kernel)
def pv173687 : PrimeValue := ⟨173687, pr173687⟩
private theorem pr173699 : Nat.Prime 173699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv19,pv653]) (by decide +kernel)
def pv173699 : PrimeValue := ⟨173699, pr173699⟩
private theorem pr173707 : Nat.Prime 173707 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv17,pv131]) (by decide +kernel)
def pv173707 : PrimeValue := ⟨173707, pr173707⟩
private theorem pr173729 : Nat.Prime 173729 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv61,pv89]) (by decide +kernel)
def pv173729 : PrimeValue := ⟨173729, pr173729⟩
private theorem pr173741 : Nat.Prime 173741 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv17,pv73]) (by decide +kernel)
def pv173741 : PrimeValue := ⟨173741, pr173741⟩
private theorem pr173743 : Nat.Prime 173743 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv1259]) (by decide +kernel)
def pv173743 : PrimeValue := ⟨173743, pr173743⟩
private theorem pr173773 : Nat.Prime 173773 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1609]) (by decide +kernel)
def pv173773 : PrimeValue := ⟨173773, pr173773⟩
private theorem pr173777 : Nat.Prime 173777 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv10861]) (by decide +kernel)
def pv173777 : PrimeValue := ⟨173777, pr173777⟩
private theorem pr173779 : Nat.Prime 173779 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv2633]) (by decide +kernel)
def pv173779 : PrimeValue := ⟨173779, pr173779⟩
private theorem pr173807 : Nat.Prime 173807 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv43,pv47]) (by decide +kernel)
def pv173807 : PrimeValue := ⟨173807, pr173807⟩
private theorem pr173819 : Nat.Prime 173819 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv233,pv373]) (by decide +kernel)
def pv173819 : PrimeValue := ⟨173819, pr173819⟩
private theorem pr173827 : Nat.Prime 173827 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29,pv37]) (by decide +kernel)
def pv173827 : PrimeValue := ⟨173827, pr173827⟩
private theorem pr173839 : Nat.Prime 173839 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv4139]) (by decide +kernel)
def pv173839 : PrimeValue := ⟨173839, pr173839⟩
private theorem pr173851 : Nat.Prime 173851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv61]) (by decide +kernel)
def pv173851 : PrimeValue := ⟨173851, pr173851⟩
private theorem pr173861 : Nat.Prime 173861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv8693]) (by decide +kernel)
def pv173861 : PrimeValue := ⟨173861, pr173861⟩
private theorem pr173867 : Nat.Prime 173867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv1129]) (by decide +kernel)
def pv173867 : PrimeValue := ⟨173867, pr173867⟩
private theorem pr173891 : Nat.Prime 173891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17389]) (by decide +kernel)
def pv173891 : PrimeValue := ⟨173891, pr173891⟩
private theorem pr173897 : Nat.Prime 173897 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv21737]) (by decide +kernel)
def pv173897 : PrimeValue := ⟨173897, pr173897⟩
private theorem pr173909 : Nat.Prime 173909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv6211]) (by decide +kernel)
def pv173909 : PrimeValue := ⟨173909, pr173909⟩
private theorem pr173923 : Nat.Prime 173923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv41,pv101]) (by decide +kernel)
def pv173923 : PrimeValue := ⟨173923, pr173923⟩
private theorem pr173933 : Nat.Prime 173933 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv59,pv67]) (by decide +kernel)
def pv173933 : PrimeValue := ⟨173933, pr173933⟩
private theorem pr173969 : Nat.Prime 173969 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv83,pv131]) (by decide +kernel)
def pv173969 : PrimeValue := ⟨173969, pr173969⟩
private theorem pr173981 : Nat.Prime 173981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv8699]) (by decide +kernel)
def pv173981 : PrimeValue := ⟨173981, pr173981⟩
private theorem pr173993 : Nat.Prime 173993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv13,pv239]) (by decide +kernel)
def pv173993 : PrimeValue := ⟨173993, pr173993⟩
private theorem pr174007 : Nat.Prime 174007 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv1381]) (by decide +kernel)
def pv174007 : PrimeValue := ⟨174007, pr174007⟩
private theorem pr174017 : Nat.Prime 174017 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2719]) (by decide +kernel)
def pv174017 : PrimeValue := ⟨174017, pr174017⟩
private theorem pr174019 : Nat.Prime 174019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv23,pv97]) (by decide +kernel)
def pv174019 : PrimeValue := ⟨174019, pr174019⟩
private theorem pr174047 : Nat.Prime 174047 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv5119]) (by decide +kernel)
def pv174047 : PrimeValue := ⟨174047, pr174047⟩
private theorem pr174049 : Nat.Prime 174049 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv37]) (by decide +kernel)
def pv174049 : PrimeValue := ⟨174049, pr174049⟩
private theorem pr174061 : Nat.Prime 174061 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv967]) (by decide +kernel)
def pv174061 : PrimeValue := ⟨174061, pr174061⟩
private theorem pr174071 : Nat.Prime 174071 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv103]) (by decide +kernel)
def pv174071 : PrimeValue := ⟨174071, pr174071⟩
private theorem pr174079 : Nat.Prime 174079 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv19,pv509]) (by decide +kernel)
def pv174079 : PrimeValue := ⟨174079, pr174079⟩
private theorem pr174091 : Nat.Prime 174091 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv829]) (by decide +kernel)
def pv174091 : PrimeValue := ⟨174091, pr174091⟩
private theorem pr174101 : Nat.Prime 174101 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1741]) (by decide +kernel)
def pv174101 : PrimeValue := ⟨174101, pr174101⟩
private theorem pr174121 : Nat.Prime 174121 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv1451]) (by decide +kernel)
def pv174121 : PrimeValue := ⟨174121, pr174121⟩
private theorem pr174137 : Nat.Prime 174137 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv21767]) (by decide +kernel)
def pv174137 : PrimeValue := ⟨174137, pr174137⟩
private theorem pr174143 : Nat.Prime 174143 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv87071]) (by decide +kernel)
def pv174143 : PrimeValue := ⟨174143, pr174143⟩
private theorem pr174149 : Nat.Prime 174149 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv17,pv197]) (by decide +kernel)
def pv174149 : PrimeValue := ⟨174149, pr174149⟩
private theorem pr174157 : Nat.Prime 174157 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv631]) (by decide +kernel)
def pv174157 : PrimeValue := ⟨174157, pr174157⟩
private theorem pr174169 : Nat.Prime 174169 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv41,pv59]) (by decide +kernel)
def pv174169 : PrimeValue := ⟨174169, pr174169⟩
private theorem pr174197 : Nat.Prime 174197 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv37,pv107]) (by decide +kernel)
def pv174197 : PrimeValue := ⟨174197, pr174197⟩
private theorem pr174221 : Nat.Prime 174221 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv31,pv281]) (by decide +kernel)
def pv174221 : PrimeValue := ⟨174221, pr174221⟩
private theorem pr174241 : Nat.Prime 174241 :=
  checkPrime_prime (q := pv59) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv174241 : PrimeValue := ⟨174241, pr174241⟩
private theorem pr174257 : Nat.Prime 174257 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv10891]) (by decide +kernel)
def pv174257 : PrimeValue := ⟨174257, pr174257⟩
private theorem pr174259 : Nat.Prime 174259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv461]) (by decide +kernel)
def pv174259 : PrimeValue := ⟨174259, pr174259⟩
private theorem pr174263 : Nat.Prime 174263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv89]) (by decide +kernel)
def pv174263 : PrimeValue := ⟨174263, pr174263⟩
private theorem pr174281 : Nat.Prime 174281 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv4357]) (by decide +kernel)
def pv174281 : PrimeValue := ⟨174281, pr174281⟩
private theorem pr174289 : Nat.Prime 174289 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv3631]) (by decide +kernel)
def pv174289 : PrimeValue := ⟨174289, pr174289⟩
private theorem pr174311 : Nat.Prime 174311 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv17431]) (by decide +kernel)
def pv174311 : PrimeValue := ⟨174311, pr174311⟩
private theorem pr174329 : Nat.Prime 174329 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv11,pv283]) (by decide +kernel)
def pv174329 : PrimeValue := ⟨174329, pr174329⟩
private theorem pr174331 : Nat.Prime 174331 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv149]) (by decide +kernel)
def pv174331 : PrimeValue := ⟨174331, pr174331⟩
private theorem pr174337 : Nat.Prime 174337 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv227]) (by decide +kernel)
def pv174337 : PrimeValue := ⟨174337, pr174337⟩
private theorem pr174347 : Nat.Prime 174347 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv179,pv487]) (by decide +kernel)
def pv174347 : PrimeValue := ⟨174347, pr174347⟩
private theorem pr174367 : Nat.Prime 174367 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv3229]) (by decide +kernel)
def pv174367 : PrimeValue := ⟨174367, pr174367⟩
private theorem pr174389 : Nat.Prime 174389 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43597]) (by decide +kernel)
def pv174389 : PrimeValue := ⟨174389, pr174389⟩
private theorem pr174407 : Nat.Prime 174407 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv29,pv31,pv97]) (by decide +kernel)
def pv174407 : PrimeValue := ⟨174407, pr174407⟩
private theorem pr174413 : Nat.Prime 174413 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv6229]) (by decide +kernel)
def pv174413 : PrimeValue := ⟨174413, pr174413⟩
private theorem pr174431 : Nat.Prime 174431 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv17443]) (by decide +kernel)
def pv174431 : PrimeValue := ⟨174431, pr174431⟩
private theorem pr174443 : Nat.Prime 174443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv87221]) (by decide +kernel)
def pv174443 : PrimeValue := ⟨174443, pr174443⟩
private theorem pr174467 : Nat.Prime 174467 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv83,pv1051]) (by decide +kernel)
def pv174467 : PrimeValue := ⟨174467, pr174467⟩
private theorem pr174469 : Nat.Prime 174469 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv7,pv31,pv67]) (by decide +kernel)
def pv174469 : PrimeValue := ⟨174469, pr174469⟩
private theorem pr174481 : Nat.Prime 174481 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv727]) (by decide +kernel)
def pv174481 : PrimeValue := ⟨174481, pr174481⟩
private theorem pr174487 : Nat.Prime 174487 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv2237]) (by decide +kernel)
def pv174487 : PrimeValue := ⟨174487, pr174487⟩
private theorem pr174491 : Nat.Prime 174491 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv17449]) (by decide +kernel)
def pv174491 : PrimeValue := ⟨174491, pr174491⟩
private theorem pr174527 : Nat.Prime 174527 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv7933]) (by decide +kernel)
def pv174527 : PrimeValue := ⟨174527, pr174527⟩
private theorem pr174533 : Nat.Prime 174533 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43633]) (by decide +kernel)
def pv174533 : PrimeValue := ⟨174533, pr174533⟩
private theorem pr174583 : Nat.Prime 174583 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv53,pv61]) (by decide +kernel)
def pv174583 : PrimeValue := ⟨174583, pr174583⟩
private theorem pr174599 : Nat.Prime 174599 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv87299]) (by decide +kernel)
def pv174599 : PrimeValue := ⟨174599, pr174599⟩
private theorem pr174613 : Nat.Prime 174613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv14551]) (by decide +kernel)
def pv174613 : PrimeValue := ⟨174613, pr174613⟩
private theorem pr174617 : Nat.Prime 174617 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv23,pv73]) (by decide +kernel)
def pv174617 : PrimeValue := ⟨174617, pr174617⟩
private theorem pr174637 : Nat.Prime 174637 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv11]) (by decide +kernel)
def pv174637 : PrimeValue := ⟨174637, pr174637⟩
private theorem pr174649 : Nat.Prime 174649 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv19,pv383]) (by decide +kernel)
def pv174649 : PrimeValue := ⟨174649, pr174649⟩
private theorem pr174653 : Nat.Prime 174653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv929]) (by decide +kernel)
def pv174653 : PrimeValue := ⟨174653, pr174653⟩
private theorem pr174659 : Nat.Prime 174659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv17,pv467]) (by decide +kernel)
def pv174659 : PrimeValue := ⟨174659, pr174659⟩
private theorem pr174673 : Nat.Prime 174673 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv1213]) (by decide +kernel)
def pv174673 : PrimeValue := ⟨174673, pr174673⟩
private theorem pr174703 : Nat.Prime 174703 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv2647]) (by decide +kernel)
def pv174703 : PrimeValue := ⟨174703, pr174703⟩
private theorem pr174721 : Nat.Prime 174721 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv13]) (by decide +kernel)
def pv174721 : PrimeValue := ⟨174721, pr174721⟩
private theorem pr174737 : Nat.Prime 174737 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv67,pv163]) (by decide +kernel)
def pv174737 : PrimeValue := ⟨174737, pr174737⟩
private theorem pr174749 : Nat.Prime 174749 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv79]) (by decide +kernel)
def pv174749 : PrimeValue := ⟨174749, pr174749⟩
private theorem pr174761 : Nat.Prime 174761 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17,pv257]) (by decide +kernel)
def pv174761 : PrimeValue := ⟨174761, pr174761⟩
private theorem pr174763 : Nat.Prime 174763 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv19,pv73]) (by decide +kernel)
def pv174763 : PrimeValue := ⟨174763, pr174763⟩
private theorem pr174773 : Nat.Prime 174773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv3361]) (by decide +kernel)
def pv174773 : PrimeValue := ⟨174773, pr174773⟩
private theorem pr174799 : Nat.Prime 174799 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv83]) (by decide +kernel)
def pv174799 : PrimeValue := ⟨174799, pr174799⟩
private theorem pr174821 : Nat.Prime 174821 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv8741]) (by decide +kernel)
def pv174821 : PrimeValue := ⟨174821, pr174821⟩
private theorem pr174829 : Nat.Prime 174829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv857]) (by decide +kernel)
def pv174829 : PrimeValue := ⟨174829, pr174829⟩
private theorem pr174859 : Nat.Prime 174859 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv151,pv193]) (by decide +kernel)
def pv174859 : PrimeValue := ⟨174859, pr174859⟩
private theorem pr174877 : Nat.Prime 174877 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv19,pv59]) (by decide +kernel)
def pv174877 : PrimeValue := ⟨174877, pr174877⟩
private theorem pr174893 : Nat.Prime 174893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv1901]) (by decide +kernel)
def pv174893 : PrimeValue := ⟨174893, pr174893⟩
private theorem pr174901 : Nat.Prime 174901 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv5,pv11,pv53]) (by decide +kernel)
def pv174901 : PrimeValue := ⟨174901, pr174901⟩
private theorem pr174907 : Nat.Prime 174907 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv41,pv79]) (by decide +kernel)
def pv174907 : PrimeValue := ⟨174907, pr174907⟩
private theorem pr174943 : Nat.Prime 174943 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv9719]) (by decide +kernel)
def pv174943 : PrimeValue := ⟨174943, pr174943⟩
private theorem pr174959 : Nat.Prime 174959 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv12497]) (by decide +kernel)
def pv174959 : PrimeValue := ⟨174959, pr174959⟩
private theorem pr174989 : Nat.Prime 174989 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv41,pv97]) (by decide +kernel)
def pv174989 : PrimeValue := ⟨174989, pr174989⟩
private theorem pr174991 : Nat.Prime 174991 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv19,pv307]) (by decide +kernel)
def pv174991 : PrimeValue := ⟨174991, pr174991⟩
private theorem pr175013 : Nat.Prime 175013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43753]) (by decide +kernel)
def pv175013 : PrimeValue := ⟨175013, pr175013⟩
private theorem pr175039 : Nat.Prime 175039 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29173]) (by decide +kernel)
def pv175039 : PrimeValue := ⟨175039, pr175039⟩
private theorem pr175061 : Nat.Prime 175061 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv8753]) (by decide +kernel)
def pv175061 : PrimeValue := ⟨175061, pr175061⟩
private theorem pr175069 : Nat.Prime 175069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1621]) (by decide +kernel)
def pv175069 : PrimeValue := ⟨175069, pr175069⟩
private theorem pr175079 : Nat.Prime 175079 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv87539]) (by decide +kernel)
def pv175079 : PrimeValue := ⟨175079, pr175079⟩
private theorem pr175081 : Nat.Prime 175081 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv1459]) (by decide +kernel)
def pv175081 : PrimeValue := ⟨175081, pr175081⟩
private theorem pr175103 : Nat.Prime 175103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv29,pv3019]) (by decide +kernel)
def pv175103 : PrimeValue := ⟨175103, pr175103⟩
private theorem pr175129 : Nat.Prime 175129 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7297]) (by decide +kernel)
def pv175129 : PrimeValue := ⟨175129, pr175129⟩
private theorem pr175141 : Nat.Prime 175141 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv139]) (by decide +kernel)
def pv175141 : PrimeValue := ⟨175141, pr175141⟩
private theorem pr175211 : Nat.Prime 175211 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv2503]) (by decide +kernel)
def pv175211 : PrimeValue := ⟨175211, pr175211⟩
private theorem pr175229 : Nat.Prime 175229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv71,pv617]) (by decide +kernel)
def pv175229 : PrimeValue := ⟨175229, pr175229⟩
private theorem pr175267 : Nat.Prime 175267 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv107]) (by decide +kernel)
def pv175267 : PrimeValue := ⟨175267, pr175267⟩
private theorem pr175277 : Nat.Prime 175277 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv1511]) (by decide +kernel)
def pv175277 : PrimeValue := ⟨175277, pr175277⟩
private theorem pr175291 : Nat.Prime 175291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv5843]) (by decide +kernel)
def pv175291 : PrimeValue := ⟨175291, pr175291⟩
private theorem pr175303 : Nat.Prime 175303 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv9739]) (by decide +kernel)
def pv175303 : PrimeValue := ⟨175303, pr175303⟩
private theorem pr175309 : Nat.Prime 175309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv2087]) (by decide +kernel)
def pv175309 : PrimeValue := ⟨175309, pr175309⟩
private theorem pr175327 : Nat.Prime 175327 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29221]) (by decide +kernel)
def pv175327 : PrimeValue := ⟨175327, pr175327⟩
private theorem pr175349 : Nat.Prime 175349 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv59,pv743]) (by decide +kernel)
def pv175349 : PrimeValue := ⟨175349, pr175349⟩
private theorem pr175391 : Nat.Prime 175391 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv17539]) (by decide +kernel)
def pv175391 : PrimeValue := ⟨175391, pr175391⟩
private theorem pr175393 : Nat.Prime 175393 :=
  checkPrime_prime (q := pv43) (ls := [pv2,pv3,pv7,pv29]) (by decide +kernel)
def pv175393 : PrimeValue := ⟨175393, pr175393⟩
private theorem pr175403 : Nat.Prime 175403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv87701]) (by decide +kernel)
def pv175403 : PrimeValue := ⟨175403, pr175403⟩
private theorem pr175411 : Nat.Prime 175411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1949]) (by decide +kernel)
def pv175411 : PrimeValue := ⟨175411, pr175411⟩
private theorem pr175433 : Nat.Prime 175433 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv21929]) (by decide +kernel)
def pv175433 : PrimeValue := ⟨175433, pr175433⟩
private theorem pr175453 : Nat.Prime 175453 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv14621]) (by decide +kernel)
def pv175453 : PrimeValue := ⟨175453, pr175453⟩
private theorem pr175463 : Nat.Prime 175463 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv83,pv151]) (by decide +kernel)
def pv175463 : PrimeValue := ⟨175463, pr175463⟩
private theorem pr175481 : Nat.Prime 175481 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv41,pv107]) (by decide +kernel)
def pv175481 : PrimeValue := ⟨175481, pr175481⟩
private theorem pr175519 : Nat.Prime 175519 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv199]) (by decide +kernel)
def pv175519 : PrimeValue := ⟨175519, pr175519⟩
private theorem pr175523 : Nat.Prime 175523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv31,pv149]) (by decide +kernel)
def pv175523 : PrimeValue := ⟨175523, pr175523⟩
private theorem pr175543 : Nat.Prime 175543 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv1721]) (by decide +kernel)
def pv175543 : PrimeValue := ⟨175543, pr175543⟩
private theorem pr175573 : Nat.Prime 175573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4877]) (by decide +kernel)
def pv175573 : PrimeValue := ⟨175573, pr175573⟩
private theorem pr175621 : Nat.Prime 175621 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv2927]) (by decide +kernel)
def pv175621 : PrimeValue := ⟨175621, pr175621⟩
private theorem pr175633 : Nat.Prime 175633 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv3659]) (by decide +kernel)
def pv175633 : PrimeValue := ⟨175633, pr175633⟩
private theorem pr175673 : Nat.Prime 175673 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv3137]) (by decide +kernel)
def pv175673 : PrimeValue := ⟨175673, pr175673⟩
private theorem pr175691 : Nat.Prime 175691 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17569]) (by decide +kernel)
def pv175691 : PrimeValue := ⟨175691, pr175691⟩
private theorem pr175699 : Nat.Prime 175699 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv43,pv227]) (by decide +kernel)
def pv175699 : PrimeValue := ⟨175699, pr175699⟩
private theorem pr175709 : Nat.Prime 175709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv31,pv109]) (by decide +kernel)
def pv175709 : PrimeValue := ⟨175709, pr175709⟩
private theorem pr175723 : Nat.Prime 175723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29287]) (by decide +kernel)
def pv175723 : PrimeValue := ⟨175723, pr175723⟩
private theorem pr175727 : Nat.Prime 175727 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv41,pv2143]) (by decide +kernel)
def pv175727 : PrimeValue := ⟨175727, pr175727⟩
private theorem pr175753 : Nat.Prime 175753 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2441]) (by decide +kernel)
def pv175753 : PrimeValue := ⟨175753, pr175753⟩
private theorem pr175759 : Nat.Prime 175759 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv11,pv2663]) (by decide +kernel)
def pv175759 : PrimeValue := ⟨175759, pr175759⟩
private theorem pr175781 : Nat.Prime 175781 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv17,pv47]) (by decide +kernel)
def pv175781 : PrimeValue := ⟨175781, pr175781⟩
private theorem pr175811 : Nat.Prime 175811 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17581]) (by decide +kernel)
def pv175811 : PrimeValue := ⟨175811, pr175811⟩
private theorem pr175829 : Nat.Prime 175829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv113,pv389]) (by decide +kernel)
def pv175829 : PrimeValue := ⟨175829, pr175829⟩
private theorem pr175837 : Nat.Prime 175837 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv14653]) (by decide +kernel)
def pv175837 : PrimeValue := ⟨175837, pr175837⟩
private theorem pr175853 : Nat.Prime 175853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43963]) (by decide +kernel)
def pv175853 : PrimeValue := ⟨175853, pr175853⟩
private theorem pr175873 : Nat.Prime 175873 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv229]) (by decide +kernel)
def pv175873 : PrimeValue := ⟨175873, pr175873⟩
private theorem pr175891 : Nat.Prime 175891 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv13,pv41]) (by decide +kernel)
def pv175891 : PrimeValue := ⟨175891, pr175891⟩
private theorem pr175909 : Nat.Prime 175909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv107,pv137]) (by decide +kernel)
def pv175909 : PrimeValue := ⟨175909, pr175909⟩
private theorem pr175919 : Nat.Prime 175919 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv87959]) (by decide +kernel)
def pv175919 : PrimeValue := ⟨175919, pr175919⟩
private theorem pr175939 : Nat.Prime 175939 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv59,pv71]) (by decide +kernel)
def pv175939 : PrimeValue := ⟨175939, pr175939⟩
private theorem pr175961 : Nat.Prime 175961 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv53,pv83]) (by decide +kernel)
def pv175961 : PrimeValue := ⟨175961, pr175961⟩
private theorem pr175979 : Nat.Prime 175979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv19,pv421]) (by decide +kernel)
def pv175979 : PrimeValue := ⟨175979, pr175979⟩
private theorem pr175991 : Nat.Prime 175991 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv17599]) (by decide +kernel)
def pv175991 : PrimeValue := ⟨175991, pr175991⟩
private theorem pr175993 : Nat.Prime 175993 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7333]) (by decide +kernel)
def pv175993 : PrimeValue := ⟨175993, pr175993⟩
private theorem pr176017 : Nat.Prime 176017 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv193]) (by decide +kernel)
def pv176017 : PrimeValue := ⟨176017, pr176017⟩
private theorem pr176021 : Nat.Prime 176021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv677]) (by decide +kernel)
def pv176021 : PrimeValue := ⟨176021, pr176021⟩
private theorem pr176041 : Nat.Prime 176041 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv163]) (by decide +kernel)
def pv176041 : PrimeValue := ⟨176041, pr176041⟩
private theorem pr176047 : Nat.Prime 176047 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv37,pv61]) (by decide +kernel)
def pv176047 : PrimeValue := ⟨176047, pr176047⟩
private theorem pr176051 : Nat.Prime 176051 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv503]) (by decide +kernel)
def pv176051 : PrimeValue := ⟨176051, pr176051⟩
private theorem pr176053 : Nat.Prime 176053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv863]) (by decide +kernel)
def pv176053 : PrimeValue := ⟨176053, pr176053⟩
private theorem pr176063 : Nat.Prime 176063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv47,pv1873]) (by decide +kernel)
def pv176063 : PrimeValue := ⟨176063, pr176063⟩
private theorem pr176081 : Nat.Prime 176081 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv31,pv71]) (by decide +kernel)
def pv176081 : PrimeValue := ⟨176081, pr176081⟩
private theorem pr176087 : Nat.Prime 176087 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv5179]) (by decide +kernel)
def pv176087 : PrimeValue := ⟨176087, pr176087⟩
private theorem pr176089 : Nat.Prime 176089 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv11,pv23,pv29]) (by decide +kernel)
def pv176089 : PrimeValue := ⟨176089, pr176089⟩
private theorem pr176123 : Nat.Prime 176123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv107,pv823]) (by decide +kernel)
def pv176123 : PrimeValue := ⟨176123, pr176123⟩
private theorem pr176129 : Nat.Prime 176129 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv43]) (by decide +kernel)
def pv176129 : PrimeValue := ⟨176129, pr176129⟩
private theorem pr176161 : Nat.Prime 176161 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv367]) (by decide +kernel)
def pv176161 : PrimeValue := ⟨176161, pr176161⟩
private theorem pr176191 : Nat.Prime 176191 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv839]) (by decide +kernel)
def pv176191 : PrimeValue := ⟨176191, pr176191⟩
private theorem pr176201 : Nat.Prime 176201 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv881]) (by decide +kernel)
def pv176201 : PrimeValue := ⟨176201, pr176201⟩
private theorem pr176213 : Nat.Prime 176213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv44053]) (by decide +kernel)
def pv176213 : PrimeValue := ⟨176213, pr176213⟩
private theorem pr176221 : Nat.Prime 176221 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv89]) (by decide +kernel)
def pv176221 : PrimeValue := ⟨176221, pr176221⟩
private theorem pr176227 : Nat.Prime 176227 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv1277]) (by decide +kernel)
def pv176227 : PrimeValue := ⟨176227, pr176227⟩
private theorem pr176237 : Nat.Prime 176237 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv44059]) (by decide +kernel)
def pv176237 : PrimeValue := ⟨176237, pr176237⟩
private theorem pr176243 : Nat.Prime 176243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv8011]) (by decide +kernel)
def pv176243 : PrimeValue := ⟨176243, pr176243⟩
private theorem pr176261 : Nat.Prime 176261 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv1259]) (by decide +kernel)
def pv176261 : PrimeValue := ⟨176261, pr176261⟩
private theorem pr176299 : Nat.Prime 176299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29383]) (by decide +kernel)
def pv176299 : PrimeValue := ⟨176299, pr176299⟩
private theorem pr176303 : Nat.Prime 176303 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv7,pv257]) (by decide +kernel)
def pv176303 : PrimeValue := ⟨176303, pr176303⟩
private theorem pr176317 : Nat.Prime 176317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv2099]) (by decide +kernel)
def pv176317 : PrimeValue := ⟨176317, pr176317⟩
private theorem pr176321 : Nat.Prime 176321 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv19,pv29]) (by decide +kernel)
def pv176321 : PrimeValue := ⟨176321, pr176321⟩
private theorem pr176327 : Nat.Prime 176327 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv131,pv673]) (by decide +kernel)
def pv176327 : PrimeValue := ⟨176327, pr176327⟩
private theorem pr176329 : Nat.Prime 176329 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv31,pv79]) (by decide +kernel)
def pv176329 : PrimeValue := ⟨176329, pr176329⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
