/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table016
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table016.pv37831
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table008
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table009

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr37831 : PrimeCertificate 37831 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv97]) (by decide +kernel)
def pv37831 : PrimeValue := ⟨37831, pr37831⟩
private theorem pr37847 : PrimeCertificate 37847 :=
  certifyPrime (q := pv5) (ls := [pv2,pv127,pv149]) (by decide +kernel)
def pv37847 : PrimeValue := ⟨37847, pr37847⟩
private theorem pr37853 : PrimeCertificate 37853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv9463]) (by decide +kernel)
def pv37853 : PrimeValue := ⟨37853, pr37853⟩
private theorem pr37861 : PrimeCertificate 37861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv631]) (by decide +kernel)
def pv37861 : PrimeValue := ⟨37861, pr37861⟩
private theorem pr37871 : PrimeCertificate 37871 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv541]) (by decide +kernel)
def pv37871 : PrimeValue := ⟨37871, pr37871⟩
private theorem pr37879 : PrimeCertificate 37879 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv59,pv107]) (by decide +kernel)
def pv37879 : PrimeValue := ⟨37879, pr37879⟩
private theorem pr37889 : PrimeCertificate 37889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37]) (by decide +kernel)
def pv37889 : PrimeValue := ⟨37889, pr37889⟩
private theorem pr37897 : PrimeCertificate 37897 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1579]) (by decide +kernel)
def pv37897 : PrimeValue := ⟨37897, pr37897⟩
private theorem pr37907 : PrimeCertificate 37907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv1723]) (by decide +kernel)
def pv37907 : PrimeValue := ⟨37907, pr37907⟩
private theorem pr37951 : PrimeCertificate 37951 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv23]) (by decide +kernel)
def pv37951 : PrimeValue := ⟨37951, pr37951⟩
private theorem pr37957 : PrimeCertificate 37957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3163]) (by decide +kernel)
def pv37957 : PrimeValue := ⟨37957, pr37957⟩
private theorem pr37963 : PrimeCertificate 37963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv37]) (by decide +kernel)
def pv37963 : PrimeValue := ⟨37963, pr37963⟩
private theorem pr37967 : PrimeCertificate 37967 :=
  certifyPrime (q := pv5) (ls := [pv2,pv41,pv463]) (by decide +kernel)
def pv37967 : PrimeValue := ⟨37967, pr37967⟩
private theorem pr37987 : PrimeCertificate 37987 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv487]) (by decide +kernel)
def pv37987 : PrimeValue := ⟨37987, pr37987⟩
private theorem pr37991 : PrimeCertificate 37991 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv29,pv131]) (by decide +kernel)
def pv37991 : PrimeValue := ⟨37991, pr37991⟩
private theorem pr37993 : PrimeCertificate 37993 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv1583]) (by decide +kernel)
def pv37993 : PrimeValue := ⟨37993, pr37993⟩
private theorem pr37997 : PrimeCertificate 37997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv23,pv59]) (by decide +kernel)
def pv37997 : PrimeValue := ⟨37997, pr37997⟩
private theorem pr38011 : PrimeCertificate 38011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv181]) (by decide +kernel)
def pv38011 : PrimeValue := ⟨38011, pr38011⟩
private theorem pr38039 : PrimeCertificate 38039 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv11,pv13,pv19]) (by decide +kernel)
def pv38039 : PrimeValue := ⟨38039, pr38039⟩
private theorem pr38047 : PrimeCertificate 38047 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv373]) (by decide +kernel)
def pv38047 : PrimeValue := ⟨38047, pr38047⟩
private theorem pr38053 : PrimeCertificate 38053 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv151]) (by decide +kernel)
def pv38053 : PrimeValue := ⟨38053, pr38053⟩
private theorem pr38069 : PrimeCertificate 38069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv307]) (by decide +kernel)
def pv38069 : PrimeValue := ⟨38069, pr38069⟩
private theorem pr38083 : PrimeCertificate 38083 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv577]) (by decide +kernel)
def pv38083 : PrimeValue := ⟨38083, pr38083⟩
private theorem pr38113 : PrimeCertificate 38113 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv397]) (by decide +kernel)
def pv38113 : PrimeValue := ⟨38113, pr38113⟩
private theorem pr38119 : PrimeCertificate 38119 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv6353]) (by decide +kernel)
def pv38119 : PrimeValue := ⟨38119, pr38119⟩
private theorem pr38149 : PrimeCertificate 38149 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv11,pv17]) (by decide +kernel)
def pv38149 : PrimeValue := ⟨38149, pr38149⟩
private theorem pr38153 : PrimeCertificate 38153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv251]) (by decide +kernel)
def pv38153 : PrimeValue := ⟨38153, pr38153⟩
private theorem pr38167 : PrimeCertificate 38167 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv6361]) (by decide +kernel)
def pv38167 : PrimeValue := ⟨38167, pr38167⟩
private theorem pr38177 : PrimeCertificate 38177 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1193]) (by decide +kernel)
def pv38177 : PrimeValue := ⟨38177, pr38177⟩
private theorem pr38183 : PrimeCertificate 38183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv1123]) (by decide +kernel)
def pv38183 : PrimeValue := ⟨38183, pr38183⟩
private theorem pr38189 : PrimeCertificate 38189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv9547]) (by decide +kernel)
def pv38189 : PrimeValue := ⟨38189, pr38189⟩
private theorem pr38197 : PrimeCertificate 38197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1061]) (by decide +kernel)
def pv38197 : PrimeValue := ⟨38197, pr38197⟩
private theorem pr38201 : PrimeCertificate 38201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv191]) (by decide +kernel)
def pv38201 : PrimeValue := ⟨38201, pr38201⟩
private theorem pr38219 : PrimeCertificate 38219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv97,pv197]) (by decide +kernel)
def pv38219 : PrimeValue := ⟨38219, pr38219⟩
private theorem pr38231 : PrimeCertificate 38231 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv3823]) (by decide +kernel)
def pv38231 : PrimeValue := ⟨38231, pr38231⟩
private theorem pr38237 : PrimeCertificate 38237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv79]) (by decide +kernel)
def pv38237 : PrimeValue := ⟨38237, pr38237⟩
private theorem pr38239 : PrimeCertificate 38239 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv6373]) (by decide +kernel)
def pv38239 : PrimeValue := ⟨38239, pr38239⟩
private theorem pr38261 : PrimeCertificate 38261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1913]) (by decide +kernel)
def pv38261 : PrimeValue := ⟨38261, pr38261⟩
private theorem pr38273 : PrimeCertificate 38273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv23]) (by decide +kernel)
def pv38273 : PrimeValue := ⟨38273, pr38273⟩
private theorem pr38281 : PrimeCertificate 38281 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv11,pv29]) (by decide +kernel)
def pv38281 : PrimeValue := ⟨38281, pr38281⟩
private theorem pr38287 : PrimeCertificate 38287 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv709]) (by decide +kernel)
def pv38287 : PrimeValue := ⟨38287, pr38287⟩
private theorem pr38299 : PrimeCertificate 38299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv491]) (by decide +kernel)
def pv38299 : PrimeValue := ⟨38299, pr38299⟩
private theorem pr38303 : PrimeCertificate 38303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv1741]) (by decide +kernel)
def pv38303 : PrimeValue := ⟨38303, pr38303⟩
private theorem pr38317 : PrimeCertificate 38317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv103]) (by decide +kernel)
def pv38317 : PrimeValue := ⟨38317, pr38317⟩
private theorem pr38321 : PrimeCertificate 38321 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv479]) (by decide +kernel)
def pv38321 : PrimeValue := ⟨38321, pr38321⟩
private theorem pr38327 : PrimeCertificate 38327 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19163]) (by decide +kernel)
def pv38327 : PrimeValue := ⟨38327, pr38327⟩
private theorem pr38329 : PrimeCertificate 38329 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv1597]) (by decide +kernel)
def pv38329 : PrimeValue := ⟨38329, pr38329⟩
private theorem pr38333 : PrimeCertificate 38333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv37]) (by decide +kernel)
def pv38333 : PrimeValue := ⟨38333, pr38333⟩
private theorem pr38351 : PrimeCertificate 38351 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv13,pv59]) (by decide +kernel)
def pv38351 : PrimeValue := ⟨38351, pr38351⟩
private theorem pr38371 : PrimeCertificate 38371 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv5,pv1279]) (by decide +kernel)
def pv38371 : PrimeValue := ⟨38371, pr38371⟩
private theorem pr38377 : PrimeCertificate 38377 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv41]) (by decide +kernel)
def pv38377 : PrimeValue := ⟨38377, pr38377⟩
private theorem pr38393 : PrimeCertificate 38393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv4799]) (by decide +kernel)
def pv38393 : PrimeValue := ⟨38393, pr38393⟩
private theorem pr38431 : PrimeCertificate 38431 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv61]) (by decide +kernel)
def pv38431 : PrimeValue := ⟨38431, pr38431⟩
private theorem pr38447 : PrimeCertificate 38447 :=
  certifyPrime (q := pv5) (ls := [pv2,pv47,pv409]) (by decide +kernel)
def pv38447 : PrimeValue := ⟨38447, pr38447⟩
private theorem pr38449 : PrimeCertificate 38449 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv89]) (by decide +kernel)
def pv38449 : PrimeValue := ⟨38449, pr38449⟩
private theorem pr38453 : PrimeCertificate 38453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv9613]) (by decide +kernel)
def pv38453 : PrimeValue := ⟨38453, pr38453⟩
private theorem pr38459 : PrimeCertificate 38459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv41,pv67]) (by decide +kernel)
def pv38459 : PrimeValue := ⟨38459, pr38459⟩
private theorem pr38461 : PrimeCertificate 38461 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv641]) (by decide +kernel)
def pv38461 : PrimeValue := ⟨38461, pr38461⟩
private theorem pr38501 : PrimeCertificate 38501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv11]) (by decide +kernel)
def pv38501 : PrimeValue := ⟨38501, pr38501⟩
private theorem pr38543 : PrimeCertificate 38543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv2753]) (by decide +kernel)
def pv38543 : PrimeValue := ⟨38543, pr38543⟩
private theorem pr38557 : PrimeCertificate 38557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv17]) (by decide +kernel)
def pv38557 : PrimeValue := ⟨38557, pr38557⟩
private theorem pr38561 : PrimeCertificate 38561 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv241]) (by decide +kernel)
def pv38561 : PrimeValue := ⟨38561, pr38561⟩
private theorem pr38567 : PrimeCertificate 38567 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv1753]) (by decide +kernel)
def pv38567 : PrimeValue := ⟨38567, pr38567⟩
private theorem pr38569 : PrimeCertificate 38569 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv1607]) (by decide +kernel)
def pv38569 : PrimeValue := ⟨38569, pr38569⟩
private theorem pr38593 : PrimeCertificate 38593 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv67]) (by decide +kernel)
def pv38593 : PrimeValue := ⟨38593, pr38593⟩
private theorem pr38603 : PrimeCertificate 38603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19301]) (by decide +kernel)
def pv38603 : PrimeValue := ⟨38603, pr38603⟩
private theorem pr38609 : PrimeCertificate 38609 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv127]) (by decide +kernel)
def pv38609 : PrimeValue := ⟨38609, pr38609⟩
private theorem pr38611 : PrimeCertificate 38611 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv13]) (by decide +kernel)
def pv38611 : PrimeValue := ⟨38611, pr38611⟩
private theorem pr38629 : PrimeCertificate 38629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv37]) (by decide +kernel)
def pv38629 : PrimeValue := ⟨38629, pr38629⟩
private theorem pr38639 : PrimeCertificate 38639 :=
  certifyPrime (q := pv29) (ls := [pv2,pv19319]) (by decide +kernel)
def pv38639 : PrimeValue := ⟨38639, pr38639⟩
private theorem pr38651 : PrimeCertificate 38651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv773]) (by decide +kernel)
def pv38651 : PrimeValue := ⟨38651, pr38651⟩
private theorem pr38653 : PrimeCertificate 38653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3221]) (by decide +kernel)
def pv38653 : PrimeValue := ⟨38653, pr38653⟩
private theorem pr38669 : PrimeCertificate 38669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv1381]) (by decide +kernel)
def pv38669 : PrimeValue := ⟨38669, pr38669⟩
private theorem pr38671 : PrimeCertificate 38671 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv1289]) (by decide +kernel)
def pv38671 : PrimeValue := ⟨38671, pr38671⟩
private theorem pr38677 : PrimeCertificate 38677 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv293]) (by decide +kernel)
def pv38677 : PrimeValue := ⟨38677, pr38677⟩
private theorem pr38693 : PrimeCertificate 38693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv569]) (by decide +kernel)
def pv38693 : PrimeValue := ⟨38693, pr38693⟩
private theorem pr38699 : PrimeCertificate 38699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv1759]) (by decide +kernel)
def pv38699 : PrimeValue := ⟨38699, pr38699⟩
private theorem pr38707 : PrimeCertificate 38707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv6451]) (by decide +kernel)
def pv38707 : PrimeValue := ⟨38707, pr38707⟩
private theorem pr38711 : PrimeCertificate 38711 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv79]) (by decide +kernel)
def pv38711 : PrimeValue := ⟨38711, pr38711⟩
private theorem pr38713 : PrimeCertificate 38713 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1613]) (by decide +kernel)
def pv38713 : PrimeValue := ⟨38713, pr38713⟩
private theorem pr38723 : PrimeCertificate 38723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv1019]) (by decide +kernel)
def pv38723 : PrimeValue := ⟨38723, pr38723⟩
private theorem pr38729 : PrimeCertificate 38729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv47,pv103]) (by decide +kernel)
def pv38729 : PrimeValue := ⟨38729, pr38729⟩
private theorem pr38737 : PrimeCertificate 38737 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv269]) (by decide +kernel)
def pv38737 : PrimeValue := ⟨38737, pr38737⟩
private theorem pr38747 : PrimeCertificate 38747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19373]) (by decide +kernel)
def pv38747 : PrimeValue := ⟨38747, pr38747⟩
private theorem pr38749 : PrimeCertificate 38749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3229]) (by decide +kernel)
def pv38749 : PrimeValue := ⟨38749, pr38749⟩
private theorem pr38767 : PrimeCertificate 38767 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv71]) (by decide +kernel)
def pv38767 : PrimeValue := ⟨38767, pr38767⟩
private theorem pr38783 : PrimeCertificate 38783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19391]) (by decide +kernel)
def pv38783 : PrimeValue := ⟨38783, pr38783⟩
private theorem pr38791 : PrimeCertificate 38791 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv431]) (by decide +kernel)
def pv38791 : PrimeValue := ⟨38791, pr38791⟩
private theorem pr38803 : PrimeCertificate 38803 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29,pv223]) (by decide +kernel)
def pv38803 : PrimeValue := ⟨38803, pr38803⟩
private theorem pr38821 : PrimeCertificate 38821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv647]) (by decide +kernel)
def pv38821 : PrimeValue := ⟨38821, pr38821⟩
private theorem pr38833 : PrimeCertificate 38833 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv809]) (by decide +kernel)
def pv38833 : PrimeValue := ⟨38833, pr38833⟩
private theorem pr38839 : PrimeCertificate 38839 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv6473]) (by decide +kernel)
def pv38839 : PrimeValue := ⟨38839, pr38839⟩
private theorem pr38851 : PrimeCertificate 38851 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv37]) (by decide +kernel)
def pv38851 : PrimeValue := ⟨38851, pr38851⟩
private theorem pr38861 : PrimeCertificate 38861 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv29,pv67]) (by decide +kernel)
def pv38861 : PrimeValue := ⟨38861, pr38861⟩
private theorem pr38867 : PrimeCertificate 38867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19433]) (by decide +kernel)
def pv38867 : PrimeValue := ⟨38867, pr38867⟩
private theorem pr38873 : PrimeCertificate 38873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43,pv113]) (by decide +kernel)
def pv38873 : PrimeValue := ⟨38873, pr38873⟩
private theorem pr38891 : PrimeCertificate 38891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv3889]) (by decide +kernel)
def pv38891 : PrimeValue := ⟨38891, pr38891⟩
private theorem pr38903 : PrimeCertificate 38903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv53,pv367]) (by decide +kernel)
def pv38903 : PrimeValue := ⟨38903, pr38903⟩
private theorem pr38917 : PrimeCertificate 38917 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv47]) (by decide +kernel)
def pv38917 : PrimeValue := ⟨38917, pr38917⟩
private theorem pr38921 : PrimeCertificate 38921 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv7,pv139]) (by decide +kernel)
def pv38921 : PrimeValue := ⟨38921, pr38921⟩
private theorem pr38923 : PrimeCertificate 38923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv499]) (by decide +kernel)
def pv38923 : PrimeValue := ⟨38923, pr38923⟩
private theorem pr38933 : PrimeCertificate 38933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv9733]) (by decide +kernel)
def pv38933 : PrimeValue := ⟨38933, pr38933⟩
private theorem pr38953 : PrimeCertificate 38953 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv541]) (by decide +kernel)
def pv38953 : PrimeValue := ⟨38953, pr38953⟩
private theorem pr38959 : PrimeCertificate 38959 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv43,pv151]) (by decide +kernel)
def pv38959 : PrimeValue := ⟨38959, pr38959⟩
private theorem pr38971 : PrimeCertificate 38971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv433]) (by decide +kernel)
def pv38971 : PrimeValue := ⟨38971, pr38971⟩
private theorem pr38977 : PrimeCertificate 38977 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv29]) (by decide +kernel)
def pv38977 : PrimeValue := ⟨38977, pr38977⟩
private theorem pr38993 : PrimeCertificate 38993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2437]) (by decide +kernel)
def pv38993 : PrimeValue := ⟨38993, pr38993⟩
private theorem pr39019 : PrimeCertificate 39019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv929]) (by decide +kernel)
def pv39019 : PrimeValue := ⟨39019, pr39019⟩
private theorem pr39023 : PrimeCertificate 39023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv109,pv179]) (by decide +kernel)
def pv39023 : PrimeValue := ⟨39023, pr39023⟩
private theorem pr39041 : PrimeCertificate 39041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv61]) (by decide +kernel)
def pv39041 : PrimeValue := ⟨39041, pr39041⟩
private theorem pr39043 : PrimeCertificate 39043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv241]) (by decide +kernel)
def pv39043 : PrimeValue := ⟨39043, pr39043⟩
private theorem pr39047 : PrimeCertificate 39047 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv2789]) (by decide +kernel)
def pv39047 : PrimeValue := ⟨39047, pr39047⟩
private theorem pr39079 : PrimeCertificate 39079 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv167]) (by decide +kernel)
def pv39079 : PrimeValue := ⟨39079, pr39079⟩
private theorem pr39089 : PrimeCertificate 39089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv349]) (by decide +kernel)
def pv39089 : PrimeValue := ⟨39089, pr39089⟩
private theorem pr39097 : PrimeCertificate 39097 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv181]) (by decide +kernel)
def pv39097 : PrimeValue := ⟨39097, pr39097⟩
private theorem pr39103 : PrimeCertificate 39103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv19]) (by decide +kernel)
def pv39103 : PrimeValue := ⟨39103, pr39103⟩
private theorem pr39107 : PrimeCertificate 39107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19553]) (by decide +kernel)
def pv39107 : PrimeValue := ⟨39107, pr39107⟩
private theorem pr39113 : PrimeCertificate 39113 :=
  certifyPrime (q := pv3) (ls := [pv2,pv4889]) (by decide +kernel)
def pv39113 : PrimeValue := ⟨39113, pr39113⟩
private theorem pr39119 : PrimeCertificate 39119 :=
  certifyPrime (q := pv11) (ls := [pv2,pv19559]) (by decide +kernel)
def pv39119 : PrimeValue := ⟨39119, pr39119⟩
private theorem pr39133 : PrimeCertificate 39133 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1087]) (by decide +kernel)
def pv39133 : PrimeValue := ⟨39133, pr39133⟩
private theorem pr39139 : PrimeCertificate 39139 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv593]) (by decide +kernel)
def pv39139 : PrimeValue := ⟨39139, pr39139⟩
private theorem pr39157 : PrimeCertificate 39157 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv251]) (by decide +kernel)
def pv39157 : PrimeValue := ⟨39157, pr39157⟩
private theorem pr39161 : PrimeCertificate 39161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv89]) (by decide +kernel)
def pv39161 : PrimeValue := ⟨39161, pr39161⟩
private theorem pr39163 : PrimeCertificate 39163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61,pv107]) (by decide +kernel)
def pv39163 : PrimeValue := ⟨39163, pr39163⟩
private theorem pr39181 : PrimeCertificate 39181 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv653]) (by decide +kernel)
def pv39181 : PrimeValue := ⟨39181, pr39181⟩
private theorem pr39191 : PrimeCertificate 39191 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv3919]) (by decide +kernel)
def pv39191 : PrimeValue := ⟨39191, pr39191⟩
private theorem pr39199 : PrimeCertificate 39199 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv47,pv139]) (by decide +kernel)
def pv39199 : PrimeValue := ⟨39199, pr39199⟩
private theorem pr39209 : PrimeCertificate 39209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv29]) (by decide +kernel)
def pv39209 : PrimeValue := ⟨39209, pr39209⟩
private theorem pr39217 : PrimeCertificate 39217 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv19,pv43]) (by decide +kernel)
def pv39217 : PrimeValue := ⟨39217, pr39217⟩
private theorem pr39227 : PrimeCertificate 39227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv1783]) (by decide +kernel)
def pv39227 : PrimeValue := ⟨39227, pr39227⟩
private theorem pr39229 : PrimeCertificate 39229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv467]) (by decide +kernel)
def pv39229 : PrimeValue := ⟨39229, pr39229⟩
private theorem pr39233 : PrimeCertificate 39233 :=
  certifyPrime (q := pv3) (ls := [pv2,pv613]) (by decide +kernel)
def pv39233 : PrimeValue := ⟨39233, pr39233⟩
private theorem pr39239 : PrimeCertificate 39239 :=
  certifyPrime (q := pv7) (ls := [pv2,pv23,pv853]) (by decide +kernel)
def pv39239 : PrimeValue := ⟨39239, pr39239⟩
private theorem pr39241 : PrimeCertificate 39241 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv109]) (by decide +kernel)
def pv39241 : PrimeValue := ⟨39241, pr39241⟩
private theorem pr39251 : PrimeCertificate 39251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv157]) (by decide +kernel)
def pv39251 : PrimeValue := ⟨39251, pr39251⟩
private theorem pr39293 : PrimeCertificate 39293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv19,pv47]) (by decide +kernel)
def pv39293 : PrimeValue := ⟨39293, pr39293⟩
private theorem pr39301 : PrimeCertificate 39301 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv131]) (by decide +kernel)
def pv39301 : PrimeValue := ⟨39301, pr39301⟩
private theorem pr39313 : PrimeCertificate 39313 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv13]) (by decide +kernel)
def pv39313 : PrimeValue := ⟨39313, pr39313⟩
private theorem pr39317 : PrimeCertificate 39317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv9829]) (by decide +kernel)
def pv39317 : PrimeValue := ⟨39317, pr39317⟩
private theorem pr39323 : PrimeCertificate 39323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19661]) (by decide +kernel)
def pv39323 : PrimeValue := ⟨39323, pr39323⟩
private theorem pr39341 : PrimeCertificate 39341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv281]) (by decide +kernel)
def pv39341 : PrimeValue := ⟨39341, pr39341⟩
private theorem pr39343 : PrimeCertificate 39343 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv79,pv83]) (by decide +kernel)
def pv39343 : PrimeValue := ⟨39343, pr39343⟩
private theorem pr39359 : PrimeCertificate 39359 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv1789]) (by decide +kernel)
def pv39359 : PrimeValue := ⟨39359, pr39359⟩
private theorem pr39367 : PrimeCertificate 39367 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3]) (by decide +kernel)
def pv39367 : PrimeValue := ⟨39367, pr39367⟩
private theorem pr39371 : PrimeCertificate 39371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31,pv127]) (by decide +kernel)
def pv39371 : PrimeValue := ⟨39371, pr39371⟩
private theorem pr39373 : PrimeCertificate 39373 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv17,pv193]) (by decide +kernel)
def pv39373 : PrimeValue := ⟨39373, pr39373⟩
private theorem pr39383 : PrimeCertificate 39383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv29,pv97]) (by decide +kernel)
def pv39383 : PrimeValue := ⟨39383, pr39383⟩
private theorem pr39397 : PrimeCertificate 39397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv67]) (by decide +kernel)
def pv39397 : PrimeValue := ⟨39397, pr39397⟩
private theorem pr39409 : PrimeCertificate 39409 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv821]) (by decide +kernel)
def pv39409 : PrimeValue := ⟨39409, pr39409⟩
private theorem pr39419 : PrimeCertificate 39419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19709]) (by decide +kernel)
def pv39419 : PrimeValue := ⟨39419, pr39419⟩
private theorem pr39439 : PrimeCertificate 39439 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv313]) (by decide +kernel)
def pv39439 : PrimeValue := ⟨39439, pr39439⟩
private theorem pr39443 : PrimeCertificate 39443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv37,pv41]) (by decide +kernel)
def pv39443 : PrimeValue := ⟨39443, pr39443⟩
private theorem pr39451 : PrimeCertificate 39451 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv263]) (by decide +kernel)
def pv39451 : PrimeValue := ⟨39451, pr39451⟩
private theorem pr39461 : PrimeCertificate 39461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1973]) (by decide +kernel)
def pv39461 : PrimeValue := ⟨39461, pr39461⟩
private theorem pr39499 : PrimeCertificate 39499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv227]) (by decide +kernel)
def pv39499 : PrimeValue := ⟨39499, pr39499⟩
private theorem pr39503 : PrimeCertificate 39503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19751]) (by decide +kernel)
def pv39503 : PrimeValue := ⟨39503, pr39503⟩
private theorem pr39509 : PrimeCertificate 39509 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv17,pv83]) (by decide +kernel)
def pv39509 : PrimeValue := ⟨39509, pr39509⟩
private theorem pr39511 : PrimeCertificate 39511 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv439]) (by decide +kernel)
def pv39511 : PrimeValue := ⟨39511, pr39511⟩
private theorem pr39521 : PrimeCertificate 39521 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv19]) (by decide +kernel)
def pv39521 : PrimeValue := ⟨39521, pr39521⟩
private theorem pr39541 : PrimeCertificate 39541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv659]) (by decide +kernel)
def pv39541 : PrimeValue := ⟨39541, pr39541⟩
private theorem pr39551 : PrimeCertificate 39551 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv113]) (by decide +kernel)
def pv39551 : PrimeValue := ⟨39551, pr39551⟩
private theorem pr39563 : PrimeCertificate 39563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv131,pv151]) (by decide +kernel)
def pv39563 : PrimeValue := ⟨39563, pr39563⟩
private theorem pr39569 : PrimeCertificate 39569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2473]) (by decide +kernel)
def pv39569 : PrimeValue := ⟨39569, pr39569⟩
private theorem pr39581 : PrimeCertificate 39581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1979]) (by decide +kernel)
def pv39581 : PrimeValue := ⟨39581, pr39581⟩
private theorem pr39607 : PrimeCertificate 39607 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv23,pv41]) (by decide +kernel)
def pv39607 : PrimeValue := ⟨39607, pr39607⟩
private theorem pr39619 : PrimeCertificate 39619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv71]) (by decide +kernel)
def pv39619 : PrimeValue := ⟨39619, pr39619⟩
private theorem pr39623 : PrimeCertificate 39623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv1801]) (by decide +kernel)
def pv39623 : PrimeValue := ⟨39623, pr39623⟩
private theorem pr39631 : PrimeCertificate 39631 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv1321]) (by decide +kernel)
def pv39631 : PrimeValue := ⟨39631, pr39631⟩
private theorem pr39659 : PrimeCertificate 39659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv79,pv251]) (by decide +kernel)
def pv39659 : PrimeValue := ⟨39659, pr39659⟩
private theorem pr39667 : PrimeCertificate 39667 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv601]) (by decide +kernel)
def pv39667 : PrimeValue := ⟨39667, pr39667⟩
private theorem pr39671 : PrimeCertificate 39671 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv3967]) (by decide +kernel)
def pv39671 : PrimeValue := ⟨39671, pr39671⟩
private theorem pr39679 : PrimeCertificate 39679 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv17,pv389]) (by decide +kernel)
def pv39679 : PrimeValue := ⟨39679, pr39679⟩
private theorem pr39703 : PrimeCertificate 39703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv509]) (by decide +kernel)
def pv39703 : PrimeValue := ⟨39703, pr39703⟩
private theorem pr39709 : PrimeCertificate 39709 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1103]) (by decide +kernel)
def pv39709 : PrimeValue := ⟨39709, pr39709⟩
private theorem pr39719 : PrimeCertificate 39719 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv2837]) (by decide +kernel)
def pv39719 : PrimeValue := ⟨39719, pr39719⟩
private theorem pr39727 : PrimeCertificate 39727 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv2207]) (by decide +kernel)
def pv39727 : PrimeValue := ⟨39727, pr39727⟩
private theorem pr39733 : PrimeCertificate 39733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv43]) (by decide +kernel)
def pv39733 : PrimeValue := ⟨39733, pr39733⟩
private theorem pr39749 : PrimeCertificate 39749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv523]) (by decide +kernel)
def pv39749 : PrimeValue := ⟨39749, pr39749⟩
private theorem pr39761 : PrimeCertificate 39761 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv71]) (by decide +kernel)
def pv39761 : PrimeValue := ⟨39761, pr39761⟩
private theorem pr39769 : PrimeCertificate 39769 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv1657]) (by decide +kernel)
def pv39769 : PrimeValue := ⟨39769, pr39769⟩
private theorem pr39779 : PrimeCertificate 39779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19889]) (by decide +kernel)
def pv39779 : PrimeValue := ⟨39779, pr39779⟩
private theorem pr39791 : PrimeCertificate 39791 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv23,pv173]) (by decide +kernel)
def pv39791 : PrimeValue := ⟨39791, pr39791⟩
private theorem pr39799 : PrimeCertificate 39799 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv67]) (by decide +kernel)
def pv39799 : PrimeValue := ⟨39799, pr39799⟩
private theorem pr39821 : PrimeCertificate 39821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv181]) (by decide +kernel)
def pv39821 : PrimeValue := ⟨39821, pr39821⟩
private theorem pr39827 : PrimeCertificate 39827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19913]) (by decide +kernel)
def pv39827 : PrimeValue := ⟨39827, pr39827⟩
private theorem pr39829 : PrimeCertificate 39829 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv3319]) (by decide +kernel)
def pv39829 : PrimeValue := ⟨39829, pr39829⟩
private theorem pr39839 : PrimeCertificate 39839 :=
  certifyPrime (q := pv7) (ls := [pv2,pv19919]) (by decide +kernel)
def pv39839 : PrimeValue := ⟨39839, pr39839⟩
private theorem pr39841 : PrimeCertificate 39841 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv83]) (by decide +kernel)
def pv39841 : PrimeValue := ⟨39841, pr39841⟩
private theorem pr39847 : PrimeCertificate 39847 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29,pv229]) (by decide +kernel)
def pv39847 : PrimeValue := ⟨39847, pr39847⟩
private theorem pr39857 : PrimeCertificate 39857 :=
  certifyPrime (q := pv3) (ls := [pv2,pv47,pv53]) (by decide +kernel)
def pv39857 : PrimeValue := ⟨39857, pr39857⟩
private theorem pr39863 : PrimeCertificate 39863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv1049]) (by decide +kernel)
def pv39863 : PrimeValue := ⟨39863, pr39863⟩
private theorem pr39869 : PrimeCertificate 39869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv9967]) (by decide +kernel)
def pv39869 : PrimeValue := ⟨39869, pr39869⟩
private theorem pr39877 : PrimeCertificate 39877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3323]) (by decide +kernel)
def pv39877 : PrimeValue := ⟨39877, pr39877⟩
private theorem pr39883 : PrimeCertificate 39883 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv23]) (by decide +kernel)
def pv39883 : PrimeValue := ⟨39883, pr39883⟩
private theorem pr39887 : PrimeCertificate 39887 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv11,pv37]) (by decide +kernel)
def pv39887 : PrimeValue := ⟨39887, pr39887⟩
private theorem pr39901 : PrimeCertificate 39901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv19]) (by decide +kernel)
def pv39901 : PrimeValue := ⟨39901, pr39901⟩
private theorem pr39929 : PrimeCertificate 39929 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv23,pv31]) (by decide +kernel)
def pv39929 : PrimeValue := ⟨39929, pr39929⟩
private theorem pr39937 : PrimeCertificate 39937 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv39937 : PrimeValue := ⟨39937, pr39937⟩
private theorem pr39953 : PrimeCertificate 39953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv227]) (by decide +kernel)
def pv39953 : PrimeValue := ⟨39953, pr39953⟩
private theorem pr39971 : PrimeCertificate 39971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv571]) (by decide +kernel)
def pv39971 : PrimeValue := ⟨39971, pr39971⟩
private theorem pr39979 : PrimeCertificate 39979 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv2221]) (by decide +kernel)
def pv39979 : PrimeValue := ⟨39979, pr39979⟩
private theorem pr39983 : PrimeCertificate 39983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19991]) (by decide +kernel)
def pv39983 : PrimeValue := ⟨39983, pr39983⟩
private theorem pr39989 : PrimeCertificate 39989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv769]) (by decide +kernel)
def pv39989 : PrimeValue := ⟨39989, pr39989⟩
private theorem pr40009 : PrimeCertificate 40009 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv1667]) (by decide +kernel)
def pv40009 : PrimeValue := ⟨40009, pr40009⟩
private theorem pr40013 : PrimeCertificate 40013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv1429]) (by decide +kernel)
def pv40013 : PrimeValue := ⟨40013, pr40013⟩
private theorem pr40031 : PrimeCertificate 40031 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv4003]) (by decide +kernel)
def pv40031 : PrimeValue := ⟨40031, pr40031⟩
private theorem pr40037 : PrimeCertificate 40037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv10009]) (by decide +kernel)
def pv40037 : PrimeValue := ⟨40037, pr40037⟩
private theorem pr40039 : PrimeCertificate 40039 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv6673]) (by decide +kernel)
def pv40039 : PrimeValue := ⟨40039, pr40039⟩
private theorem pr40063 : PrimeCertificate 40063 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv607]) (by decide +kernel)
def pv40063 : PrimeValue := ⟨40063, pr40063⟩
private theorem pr40087 : PrimeCertificate 40087 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv131]) (by decide +kernel)
def pv40087 : PrimeValue := ⟨40087, pr40087⟩
private theorem pr40093 : PrimeCertificate 40093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv257]) (by decide +kernel)
def pv40093 : PrimeValue := ⟨40093, pr40093⟩
private theorem pr40099 : PrimeCertificate 40099 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41,pv163]) (by decide +kernel)
def pv40099 : PrimeValue := ⟨40099, pr40099⟩
private theorem pr40111 : PrimeCertificate 40111 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv191]) (by decide +kernel)
def pv40111 : PrimeValue := ⟨40111, pr40111⟩
private theorem pr40123 : PrimeCertificate 40123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv743]) (by decide +kernel)
def pv40123 : PrimeValue := ⟨40123, pr40123⟩
private theorem pr40127 : PrimeCertificate 40127 :=
  certifyPrime (q := pv5) (ls := [pv2,pv20063]) (by decide +kernel)
def pv40127 : PrimeValue := ⟨40127, pr40127⟩
private theorem pr40129 : PrimeCertificate 40129 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv19]) (by decide +kernel)
def pv40129 : PrimeValue := ⟨40129, pr40129⟩
private theorem pr40151 : PrimeCertificate 40151 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv73]) (by decide +kernel)
def pv40151 : PrimeValue := ⟨40151, pr40151⟩
private theorem pr40153 : PrimeCertificate 40153 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv239]) (by decide +kernel)
def pv40153 : PrimeValue := ⟨40153, pr40153⟩
private theorem pr40163 : PrimeCertificate 40163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv467]) (by decide +kernel)
def pv40163 : PrimeValue := ⟨40163, pr40163⟩
private theorem pr40169 : PrimeCertificate 40169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5021]) (by decide +kernel)
def pv40169 : PrimeValue := ⟨40169, pr40169⟩
private theorem pr40177 : PrimeCertificate 40177 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv31]) (by decide +kernel)
def pv40177 : PrimeValue := ⟨40177, pr40177⟩
private theorem pr40189 : PrimeCertificate 40189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv197]) (by decide +kernel)
def pv40189 : PrimeValue := ⟨40189, pr40189⟩
private theorem pr40193 : PrimeCertificate 40193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv157]) (by decide +kernel)
def pv40193 : PrimeValue := ⟨40193, pr40193⟩
private theorem pr40213 : PrimeCertificate 40213 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv1117]) (by decide +kernel)
def pv40213 : PrimeValue := ⟨40213, pr40213⟩
private theorem pr40231 : PrimeCertificate 40231 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv149]) (by decide +kernel)
def pv40231 : PrimeValue := ⟨40231, pr40231⟩
private theorem pr40237 : PrimeCertificate 40237 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv7,pv479]) (by decide +kernel)
def pv40237 : PrimeValue := ⟨40237, pr40237⟩
private theorem pr40241 : PrimeCertificate 40241 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv503]) (by decide +kernel)
def pv40241 : PrimeValue := ⟨40241, pr40241⟩
private theorem pr40253 : PrimeCertificate 40253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv347]) (by decide +kernel)
def pv40253 : PrimeValue := ⟨40253, pr40253⟩
private theorem pr40277 : PrimeCertificate 40277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv10069]) (by decide +kernel)
def pv40277 : PrimeValue := ⟨40277, pr40277⟩
private theorem pr40283 : PrimeCertificate 40283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv1831]) (by decide +kernel)
def pv40283 : PrimeValue := ⟨40283, pr40283⟩
private theorem pr40289 : PrimeCertificate 40289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1259]) (by decide +kernel)
def pv40289 : PrimeValue := ⟨40289, pr40289⟩
private theorem pr40343 : PrimeCertificate 40343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv877]) (by decide +kernel)
def pv40343 : PrimeValue := ⟨40343, pr40343⟩
private theorem pr40351 : PrimeCertificate 40351 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv269]) (by decide +kernel)
def pv40351 : PrimeValue := ⟨40351, pr40351⟩
private theorem pr40357 : PrimeCertificate 40357 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv59]) (by decide +kernel)
def pv40357 : PrimeValue := ⟨40357, pr40357⟩
private theorem pr40361 : PrimeCertificate 40361 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1009]) (by decide +kernel)
def pv40361 : PrimeValue := ⟨40361, pr40361⟩
private theorem pr40387 : PrimeCertificate 40387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53,pv127]) (by decide +kernel)
def pv40387 : PrimeValue := ⟨40387, pr40387⟩
private theorem pr40423 : PrimeCertificate 40423 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv6737]) (by decide +kernel)
def pv40423 : PrimeValue := ⟨40423, pr40423⟩
private theorem pr40427 : PrimeCertificate 40427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv29,pv41]) (by decide +kernel)
def pv40427 : PrimeValue := ⟨40427, pr40427⟩
private theorem pr40429 : PrimeCertificate 40429 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv1123]) (by decide +kernel)
def pv40429 : PrimeValue := ⟨40429, pr40429⟩
private theorem pr40433 : PrimeCertificate 40433 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv19]) (by decide +kernel)
def pv40433 : PrimeValue := ⟨40433, pr40433⟩
private theorem pr40459 : PrimeCertificate 40459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv613]) (by decide +kernel)
def pv40459 : PrimeValue := ⟨40459, pr40459⟩
private theorem pr40471 : PrimeCertificate 40471 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv19,pv71]) (by decide +kernel)
def pv40471 : PrimeValue := ⟨40471, pr40471⟩
private theorem pr40483 : PrimeCertificate 40483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv173]) (by decide +kernel)
def pv40483 : PrimeValue := ⟨40483, pr40483⟩
private theorem pr40487 : PrimeCertificate 40487 :=
  certifyPrime (q := pv5) (ls := [pv2,pv31,pv653]) (by decide +kernel)
def pv40487 : PrimeValue := ⟨40487, pr40487⟩
private theorem pr40493 : PrimeCertificate 40493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv191]) (by decide +kernel)
def pv40493 : PrimeValue := ⟨40493, pr40493⟩
private theorem pr40499 : PrimeCertificate 40499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv20249]) (by decide +kernel)
def pv40499 : PrimeValue := ⟨40499, pr40499⟩
private theorem pr40507 : PrimeCertificate 40507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv157]) (by decide +kernel)
def pv40507 : PrimeValue := ⟨40507, pr40507⟩
private theorem pr40519 : PrimeCertificate 40519 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv2251]) (by decide +kernel)
def pv40519 : PrimeValue := ⟨40519, pr40519⟩
private theorem pr40529 : PrimeCertificate 40529 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv149]) (by decide +kernel)
def pv40529 : PrimeValue := ⟨40529, pr40529⟩
private theorem pr40531 : PrimeCertificate 40531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv193]) (by decide +kernel)
def pv40531 : PrimeValue := ⟨40531, pr40531⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
