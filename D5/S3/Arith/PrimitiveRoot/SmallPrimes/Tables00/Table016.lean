/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table016
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table016.pv37831
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table008
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table009

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr37831 : Nat.Prime 37831 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv97]) (by decide +kernel)
def pv37831 : PrimeValue := ⟨37831, pr37831⟩
private theorem pr37847 : Nat.Prime 37847 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv127,pv149]) (by decide +kernel)
def pv37847 : PrimeValue := ⟨37847, pr37847⟩
private theorem pr37853 : Nat.Prime 37853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv9463]) (by decide +kernel)
def pv37853 : PrimeValue := ⟨37853, pr37853⟩
private theorem pr37861 : Nat.Prime 37861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv631]) (by decide +kernel)
def pv37861 : PrimeValue := ⟨37861, pr37861⟩
private theorem pr37871 : Nat.Prime 37871 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv541]) (by decide +kernel)
def pv37871 : PrimeValue := ⟨37871, pr37871⟩
private theorem pr37879 : Nat.Prime 37879 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv59,pv107]) (by decide +kernel)
def pv37879 : PrimeValue := ⟨37879, pr37879⟩
private theorem pr37889 : Nat.Prime 37889 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv37]) (by decide +kernel)
def pv37889 : PrimeValue := ⟨37889, pr37889⟩
private theorem pr37897 : Nat.Prime 37897 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1579]) (by decide +kernel)
def pv37897 : PrimeValue := ⟨37897, pr37897⟩
private theorem pr37907 : Nat.Prime 37907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv1723]) (by decide +kernel)
def pv37907 : PrimeValue := ⟨37907, pr37907⟩
private theorem pr37951 : Nat.Prime 37951 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv23]) (by decide +kernel)
def pv37951 : PrimeValue := ⟨37951, pr37951⟩
private theorem pr37957 : Nat.Prime 37957 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv3163]) (by decide +kernel)
def pv37957 : PrimeValue := ⟨37957, pr37957⟩
private theorem pr37963 : Nat.Prime 37963 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv37]) (by decide +kernel)
def pv37963 : PrimeValue := ⟨37963, pr37963⟩
private theorem pr37967 : Nat.Prime 37967 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv41,pv463]) (by decide +kernel)
def pv37967 : PrimeValue := ⟨37967, pr37967⟩
private theorem pr37987 : Nat.Prime 37987 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv487]) (by decide +kernel)
def pv37987 : PrimeValue := ⟨37987, pr37987⟩
private theorem pr37991 : Nat.Prime 37991 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv29,pv131]) (by decide +kernel)
def pv37991 : PrimeValue := ⟨37991, pr37991⟩
private theorem pr37993 : Nat.Prime 37993 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv1583]) (by decide +kernel)
def pv37993 : PrimeValue := ⟨37993, pr37993⟩
private theorem pr37997 : Nat.Prime 37997 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv23,pv59]) (by decide +kernel)
def pv37997 : PrimeValue := ⟨37997, pr37997⟩
private theorem pr38011 : Nat.Prime 38011 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv181]) (by decide +kernel)
def pv38011 : PrimeValue := ⟨38011, pr38011⟩
private theorem pr38039 : Nat.Prime 38039 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv11,pv13,pv19]) (by decide +kernel)
def pv38039 : PrimeValue := ⟨38039, pr38039⟩
private theorem pr38047 : Nat.Prime 38047 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv373]) (by decide +kernel)
def pv38047 : PrimeValue := ⟨38047, pr38047⟩
private theorem pr38053 : Nat.Prime 38053 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv151]) (by decide +kernel)
def pv38053 : PrimeValue := ⟨38053, pr38053⟩
private theorem pr38069 : Nat.Prime 38069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv307]) (by decide +kernel)
def pv38069 : PrimeValue := ⟨38069, pr38069⟩
private theorem pr38083 : Nat.Prime 38083 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv577]) (by decide +kernel)
def pv38083 : PrimeValue := ⟨38083, pr38083⟩
private theorem pr38113 : Nat.Prime 38113 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv397]) (by decide +kernel)
def pv38113 : PrimeValue := ⟨38113, pr38113⟩
private theorem pr38119 : Nat.Prime 38119 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv6353]) (by decide +kernel)
def pv38119 : PrimeValue := ⟨38119, pr38119⟩
private theorem pr38149 : Nat.Prime 38149 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv11,pv17]) (by decide +kernel)
def pv38149 : PrimeValue := ⟨38149, pr38149⟩
private theorem pr38153 : Nat.Prime 38153 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv251]) (by decide +kernel)
def pv38153 : PrimeValue := ⟨38153, pr38153⟩
private theorem pr38167 : Nat.Prime 38167 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv6361]) (by decide +kernel)
def pv38167 : PrimeValue := ⟨38167, pr38167⟩
private theorem pr38177 : Nat.Prime 38177 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1193]) (by decide +kernel)
def pv38177 : PrimeValue := ⟨38177, pr38177⟩
private theorem pr38183 : Nat.Prime 38183 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv1123]) (by decide +kernel)
def pv38183 : PrimeValue := ⟨38183, pr38183⟩
private theorem pr38189 : Nat.Prime 38189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv9547]) (by decide +kernel)
def pv38189 : PrimeValue := ⟨38189, pr38189⟩
private theorem pr38197 : Nat.Prime 38197 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1061]) (by decide +kernel)
def pv38197 : PrimeValue := ⟨38197, pr38197⟩
private theorem pr38201 : Nat.Prime 38201 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv191]) (by decide +kernel)
def pv38201 : PrimeValue := ⟨38201, pr38201⟩
private theorem pr38219 : Nat.Prime 38219 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv97,pv197]) (by decide +kernel)
def pv38219 : PrimeValue := ⟨38219, pr38219⟩
private theorem pr38231 : Nat.Prime 38231 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv3823]) (by decide +kernel)
def pv38231 : PrimeValue := ⟨38231, pr38231⟩
private theorem pr38237 : Nat.Prime 38237 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv79]) (by decide +kernel)
def pv38237 : PrimeValue := ⟨38237, pr38237⟩
private theorem pr38239 : Nat.Prime 38239 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv6373]) (by decide +kernel)
def pv38239 : PrimeValue := ⟨38239, pr38239⟩
private theorem pr38261 : Nat.Prime 38261 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1913]) (by decide +kernel)
def pv38261 : PrimeValue := ⟨38261, pr38261⟩
private theorem pr38273 : Nat.Prime 38273 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv23]) (by decide +kernel)
def pv38273 : PrimeValue := ⟨38273, pr38273⟩
private theorem pr38281 : Nat.Prime 38281 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv11,pv29]) (by decide +kernel)
def pv38281 : PrimeValue := ⟨38281, pr38281⟩
private theorem pr38287 : Nat.Prime 38287 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv709]) (by decide +kernel)
def pv38287 : PrimeValue := ⟨38287, pr38287⟩
private theorem pr38299 : Nat.Prime 38299 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv491]) (by decide +kernel)
def pv38299 : PrimeValue := ⟨38299, pr38299⟩
private theorem pr38303 : Nat.Prime 38303 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv1741]) (by decide +kernel)
def pv38303 : PrimeValue := ⟨38303, pr38303⟩
private theorem pr38317 : Nat.Prime 38317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv103]) (by decide +kernel)
def pv38317 : PrimeValue := ⟨38317, pr38317⟩
private theorem pr38321 : Nat.Prime 38321 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv479]) (by decide +kernel)
def pv38321 : PrimeValue := ⟨38321, pr38321⟩
private theorem pr38327 : Nat.Prime 38327 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19163]) (by decide +kernel)
def pv38327 : PrimeValue := ⟨38327, pr38327⟩
private theorem pr38329 : Nat.Prime 38329 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv1597]) (by decide +kernel)
def pv38329 : PrimeValue := ⟨38329, pr38329⟩
private theorem pr38333 : Nat.Prime 38333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv37]) (by decide +kernel)
def pv38333 : PrimeValue := ⟨38333, pr38333⟩
private theorem pr38351 : Nat.Prime 38351 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv13,pv59]) (by decide +kernel)
def pv38351 : PrimeValue := ⟨38351, pr38351⟩
private theorem pr38371 : Nat.Prime 38371 :=
  checkPrime_prime (q := pv43) (ls := [pv2,pv3,pv5,pv1279]) (by decide +kernel)
def pv38371 : PrimeValue := ⟨38371, pr38371⟩
private theorem pr38377 : Nat.Prime 38377 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv41]) (by decide +kernel)
def pv38377 : PrimeValue := ⟨38377, pr38377⟩
private theorem pr38393 : Nat.Prime 38393 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv4799]) (by decide +kernel)
def pv38393 : PrimeValue := ⟨38393, pr38393⟩
private theorem pr38431 : Nat.Prime 38431 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv61]) (by decide +kernel)
def pv38431 : PrimeValue := ⟨38431, pr38431⟩
private theorem pr38447 : Nat.Prime 38447 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv47,pv409]) (by decide +kernel)
def pv38447 : PrimeValue := ⟨38447, pr38447⟩
private theorem pr38449 : Nat.Prime 38449 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv89]) (by decide +kernel)
def pv38449 : PrimeValue := ⟨38449, pr38449⟩
private theorem pr38453 : Nat.Prime 38453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv9613]) (by decide +kernel)
def pv38453 : PrimeValue := ⟨38453, pr38453⟩
private theorem pr38459 : Nat.Prime 38459 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv41,pv67]) (by decide +kernel)
def pv38459 : PrimeValue := ⟨38459, pr38459⟩
private theorem pr38461 : Nat.Prime 38461 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv641]) (by decide +kernel)
def pv38461 : PrimeValue := ⟨38461, pr38461⟩
private theorem pr38501 : Nat.Prime 38501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv11]) (by decide +kernel)
def pv38501 : PrimeValue := ⟨38501, pr38501⟩
private theorem pr38543 : Nat.Prime 38543 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv2753]) (by decide +kernel)
def pv38543 : PrimeValue := ⟨38543, pr38543⟩
private theorem pr38557 : Nat.Prime 38557 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv17]) (by decide +kernel)
def pv38557 : PrimeValue := ⟨38557, pr38557⟩
private theorem pr38561 : Nat.Prime 38561 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv241]) (by decide +kernel)
def pv38561 : PrimeValue := ⟨38561, pr38561⟩
private theorem pr38567 : Nat.Prime 38567 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv1753]) (by decide +kernel)
def pv38567 : PrimeValue := ⟨38567, pr38567⟩
private theorem pr38569 : Nat.Prime 38569 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv1607]) (by decide +kernel)
def pv38569 : PrimeValue := ⟨38569, pr38569⟩
private theorem pr38593 : Nat.Prime 38593 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv67]) (by decide +kernel)
def pv38593 : PrimeValue := ⟨38593, pr38593⟩
private theorem pr38603 : Nat.Prime 38603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19301]) (by decide +kernel)
def pv38603 : PrimeValue := ⟨38603, pr38603⟩
private theorem pr38609 : Nat.Prime 38609 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv127]) (by decide +kernel)
def pv38609 : PrimeValue := ⟨38609, pr38609⟩
private theorem pr38611 : Nat.Prime 38611 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv13]) (by decide +kernel)
def pv38611 : PrimeValue := ⟨38611, pr38611⟩
private theorem pr38629 : Nat.Prime 38629 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv37]) (by decide +kernel)
def pv38629 : PrimeValue := ⟨38629, pr38629⟩
private theorem pr38639 : Nat.Prime 38639 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv19319]) (by decide +kernel)
def pv38639 : PrimeValue := ⟨38639, pr38639⟩
private theorem pr38651 : Nat.Prime 38651 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv773]) (by decide +kernel)
def pv38651 : PrimeValue := ⟨38651, pr38651⟩
private theorem pr38653 : Nat.Prime 38653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv3221]) (by decide +kernel)
def pv38653 : PrimeValue := ⟨38653, pr38653⟩
private theorem pr38669 : Nat.Prime 38669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv1381]) (by decide +kernel)
def pv38669 : PrimeValue := ⟨38669, pr38669⟩
private theorem pr38671 : Nat.Prime 38671 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv1289]) (by decide +kernel)
def pv38671 : PrimeValue := ⟨38671, pr38671⟩
private theorem pr38677 : Nat.Prime 38677 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv293]) (by decide +kernel)
def pv38677 : PrimeValue := ⟨38677, pr38677⟩
private theorem pr38693 : Nat.Prime 38693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv569]) (by decide +kernel)
def pv38693 : PrimeValue := ⟨38693, pr38693⟩
private theorem pr38699 : Nat.Prime 38699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv1759]) (by decide +kernel)
def pv38699 : PrimeValue := ⟨38699, pr38699⟩
private theorem pr38707 : Nat.Prime 38707 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv6451]) (by decide +kernel)
def pv38707 : PrimeValue := ⟨38707, pr38707⟩
private theorem pr38711 : Nat.Prime 38711 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv79]) (by decide +kernel)
def pv38711 : PrimeValue := ⟨38711, pr38711⟩
private theorem pr38713 : Nat.Prime 38713 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1613]) (by decide +kernel)
def pv38713 : PrimeValue := ⟨38713, pr38713⟩
private theorem pr38723 : Nat.Prime 38723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv1019]) (by decide +kernel)
def pv38723 : PrimeValue := ⟨38723, pr38723⟩
private theorem pr38729 : Nat.Prime 38729 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv47,pv103]) (by decide +kernel)
def pv38729 : PrimeValue := ⟨38729, pr38729⟩
private theorem pr38737 : Nat.Prime 38737 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv269]) (by decide +kernel)
def pv38737 : PrimeValue := ⟨38737, pr38737⟩
private theorem pr38747 : Nat.Prime 38747 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19373]) (by decide +kernel)
def pv38747 : PrimeValue := ⟨38747, pr38747⟩
private theorem pr38749 : Nat.Prime 38749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv3229]) (by decide +kernel)
def pv38749 : PrimeValue := ⟨38749, pr38749⟩
private theorem pr38767 : Nat.Prime 38767 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv71]) (by decide +kernel)
def pv38767 : PrimeValue := ⟨38767, pr38767⟩
private theorem pr38783 : Nat.Prime 38783 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19391]) (by decide +kernel)
def pv38783 : PrimeValue := ⟨38783, pr38783⟩
private theorem pr38791 : Nat.Prime 38791 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv431]) (by decide +kernel)
def pv38791 : PrimeValue := ⟨38791, pr38791⟩
private theorem pr38803 : Nat.Prime 38803 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29,pv223]) (by decide +kernel)
def pv38803 : PrimeValue := ⟨38803, pr38803⟩
private theorem pr38821 : Nat.Prime 38821 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv647]) (by decide +kernel)
def pv38821 : PrimeValue := ⟨38821, pr38821⟩
private theorem pr38833 : Nat.Prime 38833 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv809]) (by decide +kernel)
def pv38833 : PrimeValue := ⟨38833, pr38833⟩
private theorem pr38839 : Nat.Prime 38839 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv6473]) (by decide +kernel)
def pv38839 : PrimeValue := ⟨38839, pr38839⟩
private theorem pr38851 : Nat.Prime 38851 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv37]) (by decide +kernel)
def pv38851 : PrimeValue := ⟨38851, pr38851⟩
private theorem pr38861 : Nat.Prime 38861 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv29,pv67]) (by decide +kernel)
def pv38861 : PrimeValue := ⟨38861, pr38861⟩
private theorem pr38867 : Nat.Prime 38867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19433]) (by decide +kernel)
def pv38867 : PrimeValue := ⟨38867, pr38867⟩
private theorem pr38873 : Nat.Prime 38873 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv43,pv113]) (by decide +kernel)
def pv38873 : PrimeValue := ⟨38873, pr38873⟩
private theorem pr38891 : Nat.Prime 38891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv3889]) (by decide +kernel)
def pv38891 : PrimeValue := ⟨38891, pr38891⟩
private theorem pr38903 : Nat.Prime 38903 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv53,pv367]) (by decide +kernel)
def pv38903 : PrimeValue := ⟨38903, pr38903⟩
private theorem pr38917 : Nat.Prime 38917 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23,pv47]) (by decide +kernel)
def pv38917 : PrimeValue := ⟨38917, pr38917⟩
private theorem pr38921 : Nat.Prime 38921 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv7,pv139]) (by decide +kernel)
def pv38921 : PrimeValue := ⟨38921, pr38921⟩
private theorem pr38923 : Nat.Prime 38923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv499]) (by decide +kernel)
def pv38923 : PrimeValue := ⟨38923, pr38923⟩
private theorem pr38933 : Nat.Prime 38933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv9733]) (by decide +kernel)
def pv38933 : PrimeValue := ⟨38933, pr38933⟩
private theorem pr38953 : Nat.Prime 38953 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv541]) (by decide +kernel)
def pv38953 : PrimeValue := ⟨38953, pr38953⟩
private theorem pr38959 : Nat.Prime 38959 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv43,pv151]) (by decide +kernel)
def pv38959 : PrimeValue := ⟨38959, pr38959⟩
private theorem pr38971 : Nat.Prime 38971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv433]) (by decide +kernel)
def pv38971 : PrimeValue := ⟨38971, pr38971⟩
private theorem pr38977 : Nat.Prime 38977 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv29]) (by decide +kernel)
def pv38977 : PrimeValue := ⟨38977, pr38977⟩
private theorem pr38993 : Nat.Prime 38993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2437]) (by decide +kernel)
def pv38993 : PrimeValue := ⟨38993, pr38993⟩
private theorem pr39019 : Nat.Prime 39019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv929]) (by decide +kernel)
def pv39019 : PrimeValue := ⟨39019, pr39019⟩
private theorem pr39023 : Nat.Prime 39023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv109,pv179]) (by decide +kernel)
def pv39023 : PrimeValue := ⟨39023, pr39023⟩
private theorem pr39041 : Nat.Prime 39041 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv61]) (by decide +kernel)
def pv39041 : PrimeValue := ⟨39041, pr39041⟩
private theorem pr39043 : Nat.Prime 39043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv241]) (by decide +kernel)
def pv39043 : PrimeValue := ⟨39043, pr39043⟩
private theorem pr39047 : Nat.Prime 39047 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv2789]) (by decide +kernel)
def pv39047 : PrimeValue := ⟨39047, pr39047⟩
private theorem pr39079 : Nat.Prime 39079 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv167]) (by decide +kernel)
def pv39079 : PrimeValue := ⟨39079, pr39079⟩
private theorem pr39089 : Nat.Prime 39089 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv349]) (by decide +kernel)
def pv39089 : PrimeValue := ⟨39089, pr39089⟩
private theorem pr39097 : Nat.Prime 39097 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv181]) (by decide +kernel)
def pv39097 : PrimeValue := ⟨39097, pr39097⟩
private theorem pr39103 : Nat.Prime 39103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv19]) (by decide +kernel)
def pv39103 : PrimeValue := ⟨39103, pr39103⟩
private theorem pr39107 : Nat.Prime 39107 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19553]) (by decide +kernel)
def pv39107 : PrimeValue := ⟨39107, pr39107⟩
private theorem pr39113 : Nat.Prime 39113 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv4889]) (by decide +kernel)
def pv39113 : PrimeValue := ⟨39113, pr39113⟩
private theorem pr39119 : Nat.Prime 39119 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv19559]) (by decide +kernel)
def pv39119 : PrimeValue := ⟨39119, pr39119⟩
private theorem pr39133 : Nat.Prime 39133 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1087]) (by decide +kernel)
def pv39133 : PrimeValue := ⟨39133, pr39133⟩
private theorem pr39139 : Nat.Prime 39139 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv593]) (by decide +kernel)
def pv39139 : PrimeValue := ⟨39139, pr39139⟩
private theorem pr39157 : Nat.Prime 39157 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv251]) (by decide +kernel)
def pv39157 : PrimeValue := ⟨39157, pr39157⟩
private theorem pr39161 : Nat.Prime 39161 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv89]) (by decide +kernel)
def pv39161 : PrimeValue := ⟨39161, pr39161⟩
private theorem pr39163 : Nat.Prime 39163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv61,pv107]) (by decide +kernel)
def pv39163 : PrimeValue := ⟨39163, pr39163⟩
private theorem pr39181 : Nat.Prime 39181 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv653]) (by decide +kernel)
def pv39181 : PrimeValue := ⟨39181, pr39181⟩
private theorem pr39191 : Nat.Prime 39191 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv3919]) (by decide +kernel)
def pv39191 : PrimeValue := ⟨39191, pr39191⟩
private theorem pr39199 : Nat.Prime 39199 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv47,pv139]) (by decide +kernel)
def pv39199 : PrimeValue := ⟨39199, pr39199⟩
private theorem pr39209 : Nat.Prime 39209 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv29]) (by decide +kernel)
def pv39209 : PrimeValue := ⟨39209, pr39209⟩
private theorem pr39217 : Nat.Prime 39217 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv19,pv43]) (by decide +kernel)
def pv39217 : PrimeValue := ⟨39217, pr39217⟩
private theorem pr39227 : Nat.Prime 39227 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv1783]) (by decide +kernel)
def pv39227 : PrimeValue := ⟨39227, pr39227⟩
private theorem pr39229 : Nat.Prime 39229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv467]) (by decide +kernel)
def pv39229 : PrimeValue := ⟨39229, pr39229⟩
private theorem pr39233 : Nat.Prime 39233 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv613]) (by decide +kernel)
def pv39233 : PrimeValue := ⟨39233, pr39233⟩
private theorem pr39239 : Nat.Prime 39239 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv23,pv853]) (by decide +kernel)
def pv39239 : PrimeValue := ⟨39239, pr39239⟩
private theorem pr39241 : Nat.Prime 39241 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv109]) (by decide +kernel)
def pv39241 : PrimeValue := ⟨39241, pr39241⟩
private theorem pr39251 : Nat.Prime 39251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv157]) (by decide +kernel)
def pv39251 : PrimeValue := ⟨39251, pr39251⟩
private theorem pr39293 : Nat.Prime 39293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv19,pv47]) (by decide +kernel)
def pv39293 : PrimeValue := ⟨39293, pr39293⟩
private theorem pr39301 : Nat.Prime 39301 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv131]) (by decide +kernel)
def pv39301 : PrimeValue := ⟨39301, pr39301⟩
private theorem pr39313 : Nat.Prime 39313 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv7,pv13]) (by decide +kernel)
def pv39313 : PrimeValue := ⟨39313, pr39313⟩
private theorem pr39317 : Nat.Prime 39317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv9829]) (by decide +kernel)
def pv39317 : PrimeValue := ⟨39317, pr39317⟩
private theorem pr39323 : Nat.Prime 39323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19661]) (by decide +kernel)
def pv39323 : PrimeValue := ⟨39323, pr39323⟩
private theorem pr39341 : Nat.Prime 39341 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv281]) (by decide +kernel)
def pv39341 : PrimeValue := ⟨39341, pr39341⟩
private theorem pr39343 : Nat.Prime 39343 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv79,pv83]) (by decide +kernel)
def pv39343 : PrimeValue := ⟨39343, pr39343⟩
private theorem pr39359 : Nat.Prime 39359 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv11,pv1789]) (by decide +kernel)
def pv39359 : PrimeValue := ⟨39359, pr39359⟩
private theorem pr39367 : Nat.Prime 39367 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3]) (by decide +kernel)
def pv39367 : PrimeValue := ⟨39367, pr39367⟩
private theorem pr39371 : Nat.Prime 39371 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv31,pv127]) (by decide +kernel)
def pv39371 : PrimeValue := ⟨39371, pr39371⟩
private theorem pr39373 : Nat.Prime 39373 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv17,pv193]) (by decide +kernel)
def pv39373 : PrimeValue := ⟨39373, pr39373⟩
private theorem pr39383 : Nat.Prime 39383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv29,pv97]) (by decide +kernel)
def pv39383 : PrimeValue := ⟨39383, pr39383⟩
private theorem pr39397 : Nat.Prime 39397 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv67]) (by decide +kernel)
def pv39397 : PrimeValue := ⟨39397, pr39397⟩
private theorem pr39409 : Nat.Prime 39409 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv821]) (by decide +kernel)
def pv39409 : PrimeValue := ⟨39409, pr39409⟩
private theorem pr39419 : Nat.Prime 39419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19709]) (by decide +kernel)
def pv39419 : PrimeValue := ⟨39419, pr39419⟩
private theorem pr39439 : Nat.Prime 39439 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv313]) (by decide +kernel)
def pv39439 : PrimeValue := ⟨39439, pr39439⟩
private theorem pr39443 : Nat.Prime 39443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv37,pv41]) (by decide +kernel)
def pv39443 : PrimeValue := ⟨39443, pr39443⟩
private theorem pr39451 : Nat.Prime 39451 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv263]) (by decide +kernel)
def pv39451 : PrimeValue := ⟨39451, pr39451⟩
private theorem pr39461 : Nat.Prime 39461 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1973]) (by decide +kernel)
def pv39461 : PrimeValue := ⟨39461, pr39461⟩
private theorem pr39499 : Nat.Prime 39499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv227]) (by decide +kernel)
def pv39499 : PrimeValue := ⟨39499, pr39499⟩
private theorem pr39503 : Nat.Prime 39503 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19751]) (by decide +kernel)
def pv39503 : PrimeValue := ⟨39503, pr39503⟩
private theorem pr39509 : Nat.Prime 39509 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv17,pv83]) (by decide +kernel)
def pv39509 : PrimeValue := ⟨39509, pr39509⟩
private theorem pr39511 : Nat.Prime 39511 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv439]) (by decide +kernel)
def pv39511 : PrimeValue := ⟨39511, pr39511⟩
private theorem pr39521 : Nat.Prime 39521 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv19]) (by decide +kernel)
def pv39521 : PrimeValue := ⟨39521, pr39521⟩
private theorem pr39541 : Nat.Prime 39541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv659]) (by decide +kernel)
def pv39541 : PrimeValue := ⟨39541, pr39541⟩
private theorem pr39551 : Nat.Prime 39551 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv113]) (by decide +kernel)
def pv39551 : PrimeValue := ⟨39551, pr39551⟩
private theorem pr39563 : Nat.Prime 39563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv131,pv151]) (by decide +kernel)
def pv39563 : PrimeValue := ⟨39563, pr39563⟩
private theorem pr39569 : Nat.Prime 39569 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2473]) (by decide +kernel)
def pv39569 : PrimeValue := ⟨39569, pr39569⟩
private theorem pr39581 : Nat.Prime 39581 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1979]) (by decide +kernel)
def pv39581 : PrimeValue := ⟨39581, pr39581⟩
private theorem pr39607 : Nat.Prime 39607 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv23,pv41]) (by decide +kernel)
def pv39607 : PrimeValue := ⟨39607, pr39607⟩
private theorem pr39619 : Nat.Prime 39619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv71]) (by decide +kernel)
def pv39619 : PrimeValue := ⟨39619, pr39619⟩
private theorem pr39623 : Nat.Prime 39623 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv1801]) (by decide +kernel)
def pv39623 : PrimeValue := ⟨39623, pr39623⟩
private theorem pr39631 : Nat.Prime 39631 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv1321]) (by decide +kernel)
def pv39631 : PrimeValue := ⟨39631, pr39631⟩
private theorem pr39659 : Nat.Prime 39659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79,pv251]) (by decide +kernel)
def pv39659 : PrimeValue := ⟨39659, pr39659⟩
private theorem pr39667 : Nat.Prime 39667 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv601]) (by decide +kernel)
def pv39667 : PrimeValue := ⟨39667, pr39667⟩
private theorem pr39671 : Nat.Prime 39671 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv3967]) (by decide +kernel)
def pv39671 : PrimeValue := ⟨39671, pr39671⟩
private theorem pr39679 : Nat.Prime 39679 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv17,pv389]) (by decide +kernel)
def pv39679 : PrimeValue := ⟨39679, pr39679⟩
private theorem pr39703 : Nat.Prime 39703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv509]) (by decide +kernel)
def pv39703 : PrimeValue := ⟨39703, pr39703⟩
private theorem pr39709 : Nat.Prime 39709 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv1103]) (by decide +kernel)
def pv39709 : PrimeValue := ⟨39709, pr39709⟩
private theorem pr39719 : Nat.Prime 39719 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv2837]) (by decide +kernel)
def pv39719 : PrimeValue := ⟨39719, pr39719⟩
private theorem pr39727 : Nat.Prime 39727 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv2207]) (by decide +kernel)
def pv39727 : PrimeValue := ⟨39727, pr39727⟩
private theorem pr39733 : Nat.Prime 39733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv43]) (by decide +kernel)
def pv39733 : PrimeValue := ⟨39733, pr39733⟩
private theorem pr39749 : Nat.Prime 39749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv523]) (by decide +kernel)
def pv39749 : PrimeValue := ⟨39749, pr39749⟩
private theorem pr39761 : Nat.Prime 39761 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv71]) (by decide +kernel)
def pv39761 : PrimeValue := ⟨39761, pr39761⟩
private theorem pr39769 : Nat.Prime 39769 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv1657]) (by decide +kernel)
def pv39769 : PrimeValue := ⟨39769, pr39769⟩
private theorem pr39779 : Nat.Prime 39779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19889]) (by decide +kernel)
def pv39779 : PrimeValue := ⟨39779, pr39779⟩
private theorem pr39791 : Nat.Prime 39791 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv23,pv173]) (by decide +kernel)
def pv39791 : PrimeValue := ⟨39791, pr39791⟩
private theorem pr39799 : Nat.Prime 39799 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv67]) (by decide +kernel)
def pv39799 : PrimeValue := ⟨39799, pr39799⟩
private theorem pr39821 : Nat.Prime 39821 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv181]) (by decide +kernel)
def pv39821 : PrimeValue := ⟨39821, pr39821⟩
private theorem pr39827 : Nat.Prime 39827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19913]) (by decide +kernel)
def pv39827 : PrimeValue := ⟨39827, pr39827⟩
private theorem pr39829 : Nat.Prime 39829 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv3319]) (by decide +kernel)
def pv39829 : PrimeValue := ⟨39829, pr39829⟩
private theorem pr39839 : Nat.Prime 39839 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv19919]) (by decide +kernel)
def pv39839 : PrimeValue := ⟨39839, pr39839⟩
private theorem pr39841 : Nat.Prime 39841 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv83]) (by decide +kernel)
def pv39841 : PrimeValue := ⟨39841, pr39841⟩
private theorem pr39847 : Nat.Prime 39847 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29,pv229]) (by decide +kernel)
def pv39847 : PrimeValue := ⟨39847, pr39847⟩
private theorem pr39857 : Nat.Prime 39857 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv47,pv53]) (by decide +kernel)
def pv39857 : PrimeValue := ⟨39857, pr39857⟩
private theorem pr39863 : Nat.Prime 39863 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv1049]) (by decide +kernel)
def pv39863 : PrimeValue := ⟨39863, pr39863⟩
private theorem pr39869 : Nat.Prime 39869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv9967]) (by decide +kernel)
def pv39869 : PrimeValue := ⟨39869, pr39869⟩
private theorem pr39877 : Nat.Prime 39877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv3323]) (by decide +kernel)
def pv39877 : PrimeValue := ⟨39877, pr39877⟩
private theorem pr39883 : Nat.Prime 39883 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv23]) (by decide +kernel)
def pv39883 : PrimeValue := ⟨39883, pr39883⟩
private theorem pr39887 : Nat.Prime 39887 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv11,pv37]) (by decide +kernel)
def pv39887 : PrimeValue := ⟨39887, pr39887⟩
private theorem pr39901 : Nat.Prime 39901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv19]) (by decide +kernel)
def pv39901 : PrimeValue := ⟨39901, pr39901⟩
private theorem pr39929 : Nat.Prime 39929 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv23,pv31]) (by decide +kernel)
def pv39929 : PrimeValue := ⟨39929, pr39929⟩
private theorem pr39937 : Nat.Prime 39937 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv39937 : PrimeValue := ⟨39937, pr39937⟩
private theorem pr39953 : Nat.Prime 39953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv227]) (by decide +kernel)
def pv39953 : PrimeValue := ⟨39953, pr39953⟩
private theorem pr39971 : Nat.Prime 39971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv571]) (by decide +kernel)
def pv39971 : PrimeValue := ⟨39971, pr39971⟩
private theorem pr39979 : Nat.Prime 39979 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv2221]) (by decide +kernel)
def pv39979 : PrimeValue := ⟨39979, pr39979⟩
private theorem pr39983 : Nat.Prime 39983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19991]) (by decide +kernel)
def pv39983 : PrimeValue := ⟨39983, pr39983⟩
private theorem pr39989 : Nat.Prime 39989 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv769]) (by decide +kernel)
def pv39989 : PrimeValue := ⟨39989, pr39989⟩
private theorem pr40009 : Nat.Prime 40009 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv1667]) (by decide +kernel)
def pv40009 : PrimeValue := ⟨40009, pr40009⟩
private theorem pr40013 : Nat.Prime 40013 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv1429]) (by decide +kernel)
def pv40013 : PrimeValue := ⟨40013, pr40013⟩
private theorem pr40031 : Nat.Prime 40031 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv4003]) (by decide +kernel)
def pv40031 : PrimeValue := ⟨40031, pr40031⟩
private theorem pr40037 : Nat.Prime 40037 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv10009]) (by decide +kernel)
def pv40037 : PrimeValue := ⟨40037, pr40037⟩
private theorem pr40039 : Nat.Prime 40039 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv6673]) (by decide +kernel)
def pv40039 : PrimeValue := ⟨40039, pr40039⟩
private theorem pr40063 : Nat.Prime 40063 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv607]) (by decide +kernel)
def pv40063 : PrimeValue := ⟨40063, pr40063⟩
private theorem pr40087 : Nat.Prime 40087 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv131]) (by decide +kernel)
def pv40087 : PrimeValue := ⟨40087, pr40087⟩
private theorem pr40093 : Nat.Prime 40093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv257]) (by decide +kernel)
def pv40093 : PrimeValue := ⟨40093, pr40093⟩
private theorem pr40099 : Nat.Prime 40099 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv41,pv163]) (by decide +kernel)
def pv40099 : PrimeValue := ⟨40099, pr40099⟩
private theorem pr40111 : Nat.Prime 40111 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv191]) (by decide +kernel)
def pv40111 : PrimeValue := ⟨40111, pr40111⟩
private theorem pr40123 : Nat.Prime 40123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv743]) (by decide +kernel)
def pv40123 : PrimeValue := ⟨40123, pr40123⟩
private theorem pr40127 : Nat.Prime 40127 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv20063]) (by decide +kernel)
def pv40127 : PrimeValue := ⟨40127, pr40127⟩
private theorem pr40129 : Nat.Prime 40129 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv19]) (by decide +kernel)
def pv40129 : PrimeValue := ⟨40129, pr40129⟩
private theorem pr40151 : Nat.Prime 40151 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv11,pv73]) (by decide +kernel)
def pv40151 : PrimeValue := ⟨40151, pr40151⟩
private theorem pr40153 : Nat.Prime 40153 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv239]) (by decide +kernel)
def pv40153 : PrimeValue := ⟨40153, pr40153⟩
private theorem pr40163 : Nat.Prime 40163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv467]) (by decide +kernel)
def pv40163 : PrimeValue := ⟨40163, pr40163⟩
private theorem pr40169 : Nat.Prime 40169 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5021]) (by decide +kernel)
def pv40169 : PrimeValue := ⟨40169, pr40169⟩
private theorem pr40177 : Nat.Prime 40177 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv31]) (by decide +kernel)
def pv40177 : PrimeValue := ⟨40177, pr40177⟩
private theorem pr40189 : Nat.Prime 40189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv197]) (by decide +kernel)
def pv40189 : PrimeValue := ⟨40189, pr40189⟩
private theorem pr40193 : Nat.Prime 40193 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv157]) (by decide +kernel)
def pv40193 : PrimeValue := ⟨40193, pr40193⟩
private theorem pr40213 : Nat.Prime 40213 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv1117]) (by decide +kernel)
def pv40213 : PrimeValue := ⟨40213, pr40213⟩
private theorem pr40231 : Nat.Prime 40231 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv149]) (by decide +kernel)
def pv40231 : PrimeValue := ⟨40231, pr40231⟩
private theorem pr40237 : Nat.Prime 40237 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv7,pv479]) (by decide +kernel)
def pv40237 : PrimeValue := ⟨40237, pr40237⟩
private theorem pr40241 : Nat.Prime 40241 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv503]) (by decide +kernel)
def pv40241 : PrimeValue := ⟨40241, pr40241⟩
private theorem pr40253 : Nat.Prime 40253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv347]) (by decide +kernel)
def pv40253 : PrimeValue := ⟨40253, pr40253⟩
private theorem pr40277 : Nat.Prime 40277 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv10069]) (by decide +kernel)
def pv40277 : PrimeValue := ⟨40277, pr40277⟩
private theorem pr40283 : Nat.Prime 40283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv1831]) (by decide +kernel)
def pv40283 : PrimeValue := ⟨40283, pr40283⟩
private theorem pr40289 : Nat.Prime 40289 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1259]) (by decide +kernel)
def pv40289 : PrimeValue := ⟨40289, pr40289⟩
private theorem pr40343 : Nat.Prime 40343 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv23,pv877]) (by decide +kernel)
def pv40343 : PrimeValue := ⟨40343, pr40343⟩
private theorem pr40351 : Nat.Prime 40351 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv269]) (by decide +kernel)
def pv40351 : PrimeValue := ⟨40351, pr40351⟩
private theorem pr40357 : Nat.Prime 40357 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv59]) (by decide +kernel)
def pv40357 : PrimeValue := ⟨40357, pr40357⟩
private theorem pr40361 : Nat.Prime 40361 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv1009]) (by decide +kernel)
def pv40361 : PrimeValue := ⟨40361, pr40361⟩
private theorem pr40387 : Nat.Prime 40387 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv53,pv127]) (by decide +kernel)
def pv40387 : PrimeValue := ⟨40387, pr40387⟩
private theorem pr40423 : Nat.Prime 40423 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv6737]) (by decide +kernel)
def pv40423 : PrimeValue := ⟨40423, pr40423⟩
private theorem pr40427 : Nat.Prime 40427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv29,pv41]) (by decide +kernel)
def pv40427 : PrimeValue := ⟨40427, pr40427⟩
private theorem pr40429 : Nat.Prime 40429 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv1123]) (by decide +kernel)
def pv40429 : PrimeValue := ⟨40429, pr40429⟩
private theorem pr40433 : Nat.Prime 40433 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv19]) (by decide +kernel)
def pv40433 : PrimeValue := ⟨40433, pr40433⟩
private theorem pr40459 : Nat.Prime 40459 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv613]) (by decide +kernel)
def pv40459 : PrimeValue := ⟨40459, pr40459⟩
private theorem pr40471 : Nat.Prime 40471 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv19,pv71]) (by decide +kernel)
def pv40471 : PrimeValue := ⟨40471, pr40471⟩
private theorem pr40483 : Nat.Prime 40483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv173]) (by decide +kernel)
def pv40483 : PrimeValue := ⟨40483, pr40483⟩
private theorem pr40487 : Nat.Prime 40487 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv31,pv653]) (by decide +kernel)
def pv40487 : PrimeValue := ⟨40487, pr40487⟩
private theorem pr40493 : Nat.Prime 40493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53,pv191]) (by decide +kernel)
def pv40493 : PrimeValue := ⟨40493, pr40493⟩
private theorem pr40499 : Nat.Prime 40499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv20249]) (by decide +kernel)
def pv40499 : PrimeValue := ⟨40499, pr40499⟩
private theorem pr40507 : Nat.Prime 40507 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv43,pv157]) (by decide +kernel)
def pv40507 : PrimeValue := ⟨40507, pr40507⟩
private theorem pr40519 : Nat.Prime 40519 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv2251]) (by decide +kernel)
def pv40519 : PrimeValue := ⟨40519, pr40519⟩
private theorem pr40529 : Nat.Prime 40529 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv149]) (by decide +kernel)
def pv40529 : PrimeValue := ⟨40529, pr40529⟩
private theorem pr40531 : Nat.Prime 40531 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv193]) (by decide +kernel)
def pv40531 : PrimeValue := ⟨40531, pr40531⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
