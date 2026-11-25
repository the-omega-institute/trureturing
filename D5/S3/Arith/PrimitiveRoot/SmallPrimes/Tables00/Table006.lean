/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table006
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table006.pv12569
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table003

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr12569 : PrimeCertificate 12569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1571]) (by decide +kernel)
def pv12569 : PrimeValue := ⟨12569, pr12569⟩
private theorem pr12577 : PrimeCertificate 12577 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv131]) (by decide +kernel)
def pv12577 : PrimeValue := ⟨12577, pr12577⟩
private theorem pr12583 : PrimeCertificate 12583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv233]) (by decide +kernel)
def pv12583 : PrimeValue := ⟨12583, pr12583⟩
private theorem pr12589 : PrimeCertificate 12589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1049]) (by decide +kernel)
def pv12589 : PrimeValue := ⟨12589, pr12589⟩
private theorem pr12601 : PrimeCertificate 12601 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv12601 : PrimeValue := ⟨12601, pr12601⟩
private theorem pr12611 : PrimeCertificate 12611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv97]) (by decide +kernel)
def pv12611 : PrimeValue := ⟨12611, pr12611⟩
private theorem pr12613 : PrimeCertificate 12613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1051]) (by decide +kernel)
def pv12613 : PrimeValue := ⟨12613, pr12613⟩
private theorem pr12619 : PrimeCertificate 12619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv701]) (by decide +kernel)
def pv12619 : PrimeValue := ⟨12619, pr12619⟩
private theorem pr12637 : PrimeCertificate 12637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv12637 : PrimeValue := ⟨12637, pr12637⟩
private theorem pr12641 : PrimeCertificate 12641 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv79]) (by decide +kernel)
def pv12641 : PrimeValue := ⟨12641, pr12641⟩
private theorem pr12647 : PrimeCertificate 12647 :=
  certifyPrime (q := pv5) (ls := [pv2,pv6323]) (by decide +kernel)
def pv12647 : PrimeValue := ⟨12647, pr12647⟩
private theorem pr12653 : PrimeCertificate 12653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3163]) (by decide +kernel)
def pv12653 : PrimeValue := ⟨12653, pr12653⟩
private theorem pr12659 : PrimeCertificate 12659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv6329]) (by decide +kernel)
def pv12659 : PrimeValue := ⟨12659, pr12659⟩
private theorem pr12671 : PrimeCertificate 12671 :=
  certifyPrime (q := pv29) (ls := [pv2,pv5,pv7,pv181]) (by decide +kernel)
def pv12671 : PrimeValue := ⟨12671, pr12671⟩
private theorem pr12689 : PrimeCertificate 12689 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv61]) (by decide +kernel)
def pv12689 : PrimeValue := ⟨12689, pr12689⟩
private theorem pr12697 : PrimeCertificate 12697 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23]) (by decide +kernel)
def pv12697 : PrimeValue := ⟨12697, pr12697⟩
private theorem pr12703 : PrimeCertificate 12703 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv73]) (by decide +kernel)
def pv12703 : PrimeValue := ⟨12703, pr12703⟩
private theorem pr12713 : PrimeCertificate 12713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv227]) (by decide +kernel)
def pv12713 : PrimeValue := ⟨12713, pr12713⟩
private theorem pr12721 : PrimeCertificate 12721 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv53]) (by decide +kernel)
def pv12721 : PrimeValue := ⟨12721, pr12721⟩
private theorem pr12739 : PrimeCertificate 12739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv193]) (by decide +kernel)
def pv12739 : PrimeValue := ⟨12739, pr12739⟩
private theorem pr12743 : PrimeCertificate 12743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv277]) (by decide +kernel)
def pv12743 : PrimeValue := ⟨12743, pr12743⟩
private theorem pr12757 : PrimeCertificate 12757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1063]) (by decide +kernel)
def pv12757 : PrimeValue := ⟨12757, pr12757⟩
private theorem pr12763 : PrimeCertificate 12763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv709]) (by decide +kernel)
def pv12763 : PrimeValue := ⟨12763, pr12763⟩
private theorem pr12781 : PrimeCertificate 12781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv71]) (by decide +kernel)
def pv12781 : PrimeValue := ⟨12781, pr12781⟩
private theorem pr12791 : PrimeCertificate 12791 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv1279]) (by decide +kernel)
def pv12791 : PrimeValue := ⟨12791, pr12791⟩
private theorem pr12799 : PrimeCertificate 12799 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv79]) (by decide +kernel)
def pv12799 : PrimeValue := ⟨12799, pr12799⟩
private theorem pr12809 : PrimeCertificate 12809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1601]) (by decide +kernel)
def pv12809 : PrimeValue := ⟨12809, pr12809⟩
private theorem pr12821 : PrimeCertificate 12821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv641]) (by decide +kernel)
def pv12821 : PrimeValue := ⟨12821, pr12821⟩
private theorem pr12823 : PrimeCertificate 12823 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv2137]) (by decide +kernel)
def pv12823 : PrimeValue := ⟨12823, pr12823⟩
private theorem pr12829 : PrimeCertificate 12829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1069]) (by decide +kernel)
def pv12829 : PrimeValue := ⟨12829, pr12829⟩
private theorem pr12841 : PrimeCertificate 12841 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv5,pv107]) (by decide +kernel)
def pv12841 : PrimeValue := ⟨12841, pr12841⟩
private theorem pr12853 : PrimeCertificate 12853 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv17]) (by decide +kernel)
def pv12853 : PrimeValue := ⟨12853, pr12853⟩
private theorem pr12889 : PrimeCertificate 12889 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv179]) (by decide +kernel)
def pv12889 : PrimeValue := ⟨12889, pr12889⟩
private theorem pr12893 : PrimeCertificate 12893 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv293]) (by decide +kernel)
def pv12893 : PrimeValue := ⟨12893, pr12893⟩
private theorem pr12899 : PrimeCertificate 12899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv6449]) (by decide +kernel)
def pv12899 : PrimeValue := ⟨12899, pr12899⟩
private theorem pr12907 : PrimeCertificate 12907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv239]) (by decide +kernel)
def pv12907 : PrimeValue := ⟨12907, pr12907⟩
private theorem pr12911 : PrimeCertificate 12911 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv1291]) (by decide +kernel)
def pv12911 : PrimeValue := ⟨12911, pr12911⟩
private theorem pr12917 : PrimeCertificate 12917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3229]) (by decide +kernel)
def pv12917 : PrimeValue := ⟨12917, pr12917⟩
private theorem pr12919 : PrimeCertificate 12919 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv2153]) (by decide +kernel)
def pv12919 : PrimeValue := ⟨12919, pr12919⟩
private theorem pr12923 : PrimeCertificate 12923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv71]) (by decide +kernel)
def pv12923 : PrimeValue := ⟨12923, pr12923⟩
private theorem pr12941 : PrimeCertificate 12941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv647]) (by decide +kernel)
def pv12941 : PrimeValue := ⟨12941, pr12941⟩
private theorem pr12953 : PrimeCertificate 12953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1619]) (by decide +kernel)
def pv12953 : PrimeValue := ⟨12953, pr12953⟩
private theorem pr12959 : PrimeCertificate 12959 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv19,pv31]) (by decide +kernel)
def pv12959 : PrimeValue := ⟨12959, pr12959⟩
private theorem pr12967 : PrimeCertificate 12967 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv2161]) (by decide +kernel)
def pv12967 : PrimeValue := ⟨12967, pr12967⟩
private theorem pr12973 : PrimeCertificate 12973 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv23,pv47]) (by decide +kernel)
def pv12973 : PrimeValue := ⟨12973, pr12973⟩
private theorem pr12979 : PrimeCertificate 12979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv103]) (by decide +kernel)
def pv12979 : PrimeValue := ⟨12979, pr12979⟩
private theorem pr12983 : PrimeCertificate 12983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv6491]) (by decide +kernel)
def pv12983 : PrimeValue := ⟨12983, pr12983⟩
private theorem pr13001 : PrimeCertificate 13001 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13]) (by decide +kernel)
def pv13001 : PrimeValue := ⟨13001, pr13001⟩
private theorem pr13003 : PrimeCertificate 13003 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv197]) (by decide +kernel)
def pv13003 : PrimeValue := ⟨13003, pr13003⟩
private theorem pr13007 : PrimeCertificate 13007 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv929]) (by decide +kernel)
def pv13007 : PrimeValue := ⟨13007, pr13007⟩
private theorem pr13009 : PrimeCertificate 13009 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv271]) (by decide +kernel)
def pv13009 : PrimeValue := ⟨13009, pr13009⟩
private theorem pr13033 : PrimeCertificate 13033 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv181]) (by decide +kernel)
def pv13033 : PrimeValue := ⟨13033, pr13033⟩
private theorem pr13037 : PrimeCertificate 13037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3259]) (by decide +kernel)
def pv13037 : PrimeValue := ⟨13037, pr13037⟩
private theorem pr13043 : PrimeCertificate 13043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv6521]) (by decide +kernel)
def pv13043 : PrimeValue := ⟨13043, pr13043⟩
private theorem pr13049 : PrimeCertificate 13049 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv233]) (by decide +kernel)
def pv13049 : PrimeValue := ⟨13049, pr13049⟩
private theorem pr13063 : PrimeCertificate 13063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv311]) (by decide +kernel)
def pv13063 : PrimeValue := ⟨13063, pr13063⟩
private theorem pr13093 : PrimeCertificate 13093 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1091]) (by decide +kernel)
def pv13093 : PrimeValue := ⟨13093, pr13093⟩
private theorem pr13099 : PrimeCertificate 13099 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37,pv59]) (by decide +kernel)
def pv13099 : PrimeValue := ⟨13099, pr13099⟩
private theorem pr13103 : PrimeCertificate 13103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv6551]) (by decide +kernel)
def pv13103 : PrimeValue := ⟨13103, pr13103⟩
private theorem pr13109 : PrimeCertificate 13109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv113]) (by decide +kernel)
def pv13109 : PrimeValue := ⟨13109, pr13109⟩
private theorem pr13121 : PrimeCertificate 13121 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv41]) (by decide +kernel)
def pv13121 : PrimeValue := ⟨13121, pr13121⟩
private theorem pr13127 : PrimeCertificate 13127 :=
  certifyPrime (q := pv5) (ls := [pv2,pv6563]) (by decide +kernel)
def pv13127 : PrimeValue := ⟨13127, pr13127⟩
private theorem pr13147 : PrimeCertificate 13147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv313]) (by decide +kernel)
def pv13147 : PrimeValue := ⟨13147, pr13147⟩
private theorem pr13151 : PrimeCertificate 13151 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv263]) (by decide +kernel)
def pv13151 : PrimeValue := ⟨13151, pr13151⟩
private theorem pr13159 : PrimeCertificate 13159 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv43]) (by decide +kernel)
def pv13159 : PrimeValue := ⟨13159, pr13159⟩
private theorem pr13163 : PrimeCertificate 13163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv6581]) (by decide +kernel)
def pv13163 : PrimeValue := ⟨13163, pr13163⟩
private theorem pr13171 : PrimeCertificate 13171 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv439]) (by decide +kernel)
def pv13171 : PrimeValue := ⟨13171, pr13171⟩
private theorem pr13177 : PrimeCertificate 13177 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv61]) (by decide +kernel)
def pv13177 : PrimeValue := ⟨13177, pr13177⟩
private theorem pr13183 : PrimeCertificate 13183 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv13183 : PrimeValue := ⟨13183, pr13183⟩
private theorem pr13187 : PrimeCertificate 13187 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv347]) (by decide +kernel)
def pv13187 : PrimeValue := ⟨13187, pr13187⟩
private theorem pr13217 : PrimeCertificate 13217 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv59]) (by decide +kernel)
def pv13217 : PrimeValue := ⟨13217, pr13217⟩
private theorem pr13219 : PrimeCertificate 13219 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv2203]) (by decide +kernel)
def pv13219 : PrimeValue := ⟨13219, pr13219⟩
private theorem pr13229 : PrimeCertificate 13229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3307]) (by decide +kernel)
def pv13229 : PrimeValue := ⟨13229, pr13229⟩
private theorem pr13241 : PrimeCertificate 13241 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv331]) (by decide +kernel)
def pv13241 : PrimeValue := ⟨13241, pr13241⟩
private theorem pr13249 : PrimeCertificate 13249 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23]) (by decide +kernel)
def pv13249 : PrimeValue := ⟨13249, pr13249⟩
private theorem pr13259 : PrimeCertificate 13259 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv947]) (by decide +kernel)
def pv13259 : PrimeValue := ⟨13259, pr13259⟩
private theorem pr13267 : PrimeCertificate 13267 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv67]) (by decide +kernel)
def pv13267 : PrimeValue := ⟨13267, pr13267⟩
private theorem pr13291 : PrimeCertificate 13291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv443]) (by decide +kernel)
def pv13291 : PrimeValue := ⟨13291, pr13291⟩
private theorem pr13297 : PrimeCertificate 13297 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv277]) (by decide +kernel)
def pv13297 : PrimeValue := ⟨13297, pr13297⟩
private theorem pr13309 : PrimeCertificate 13309 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv1109]) (by decide +kernel)
def pv13309 : PrimeValue := ⟨13309, pr13309⟩
private theorem pr13313 : PrimeCertificate 13313 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13]) (by decide +kernel)
def pv13313 : PrimeValue := ⟨13313, pr13313⟩
private theorem pr13327 : PrimeCertificate 13327 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv2221]) (by decide +kernel)
def pv13327 : PrimeValue := ⟨13327, pr13327⟩
private theorem pr13331 : PrimeCertificate 13331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31,pv43]) (by decide +kernel)
def pv13331 : PrimeValue := ⟨13331, pr13331⟩
private theorem pr13337 : PrimeCertificate 13337 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1667]) (by decide +kernel)
def pv13337 : PrimeValue := ⟨13337, pr13337⟩
private theorem pr13339 : PrimeCertificate 13339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv19]) (by decide +kernel)
def pv13339 : PrimeValue := ⟨13339, pr13339⟩
private theorem pr13367 : PrimeCertificate 13367 :=
  certifyPrime (q := pv5) (ls := [pv2,pv41,pv163]) (by decide +kernel)
def pv13367 : PrimeValue := ⟨13367, pr13367⟩
private theorem pr13381 : PrimeCertificate 13381 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv223]) (by decide +kernel)
def pv13381 : PrimeValue := ⟨13381, pr13381⟩
private theorem pr13397 : PrimeCertificate 13397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv197]) (by decide +kernel)
def pv13397 : PrimeValue := ⟨13397, pr13397⟩
private theorem pr13399 : PrimeCertificate 13399 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv29]) (by decide +kernel)
def pv13399 : PrimeValue := ⟨13399, pr13399⟩
private theorem pr13411 : PrimeCertificate 13411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv149]) (by decide +kernel)
def pv13411 : PrimeValue := ⟨13411, pr13411⟩
private theorem pr13417 : PrimeCertificate 13417 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv43]) (by decide +kernel)
def pv13417 : PrimeValue := ⟨13417, pr13417⟩
private theorem pr13421 : PrimeCertificate 13421 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv11,pv61]) (by decide +kernel)
def pv13421 : PrimeValue := ⟨13421, pr13421⟩
private theorem pr13441 : PrimeCertificate 13441 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv13441 : PrimeValue := ⟨13441, pr13441⟩
private theorem pr13451 : PrimeCertificate 13451 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv269]) (by decide +kernel)
def pv13451 : PrimeValue := ⟨13451, pr13451⟩
private theorem pr13457 : PrimeCertificate 13457 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29]) (by decide +kernel)
def pv13457 : PrimeValue := ⟨13457, pr13457⟩
private theorem pr13463 : PrimeCertificate 13463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv53,pv127]) (by decide +kernel)
def pv13463 : PrimeValue := ⟨13463, pr13463⟩
private theorem pr13469 : PrimeCertificate 13469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv37]) (by decide +kernel)
def pv13469 : PrimeValue := ⟨13469, pr13469⟩
private theorem pr13477 : PrimeCertificate 13477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1123]) (by decide +kernel)
def pv13477 : PrimeValue := ⟨13477, pr13477⟩
private theorem pr13487 : PrimeCertificate 13487 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv613]) (by decide +kernel)
def pv13487 : PrimeValue := ⟨13487, pr13487⟩
private theorem pr13499 : PrimeCertificate 13499 :=
  certifyPrime (q := pv13) (ls := [pv2,pv17,pv397]) (by decide +kernel)
def pv13499 : PrimeValue := ⟨13499, pr13499⟩
private theorem pr13513 : PrimeCertificate 13513 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv563]) (by decide +kernel)
def pv13513 : PrimeValue := ⟨13513, pr13513⟩
private theorem pr13523 : PrimeCertificate 13523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv6761]) (by decide +kernel)
def pv13523 : PrimeValue := ⟨13523, pr13523⟩
private theorem pr13537 : PrimeCertificate 13537 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv47]) (by decide +kernel)
def pv13537 : PrimeValue := ⟨13537, pr13537⟩
private theorem pr13553 : PrimeCertificate 13553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11]) (by decide +kernel)
def pv13553 : PrimeValue := ⟨13553, pr13553⟩
private theorem pr13567 : PrimeCertificate 13567 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv17,pv19]) (by decide +kernel)
def pv13567 : PrimeValue := ⟨13567, pr13567⟩
private theorem pr13577 : PrimeCertificate 13577 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1697]) (by decide +kernel)
def pv13577 : PrimeValue := ⟨13577, pr13577⟩
private theorem pr13591 : PrimeCertificate 13591 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv151]) (by decide +kernel)
def pv13591 : PrimeValue := ⟨13591, pr13591⟩
private theorem pr13597 : PrimeCertificate 13597 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv103]) (by decide +kernel)
def pv13597 : PrimeValue := ⟨13597, pr13597⟩
private theorem pr13613 : PrimeCertificate 13613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv83]) (by decide +kernel)
def pv13613 : PrimeValue := ⟨13613, pr13613⟩
private theorem pr13619 : PrimeCertificate 13619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv619]) (by decide +kernel)
def pv13619 : PrimeValue := ⟨13619, pr13619⟩
private theorem pr13627 : PrimeCertificate 13627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv757]) (by decide +kernel)
def pv13627 : PrimeValue := ⟨13627, pr13627⟩
private theorem pr13633 : PrimeCertificate 13633 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv71]) (by decide +kernel)
def pv13633 : PrimeValue := ⟨13633, pr13633⟩
private theorem pr13649 : PrimeCertificate 13649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv853]) (by decide +kernel)
def pv13649 : PrimeValue := ⟨13649, pr13649⟩
private theorem pr13669 : PrimeCertificate 13669 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv67]) (by decide +kernel)
def pv13669 : PrimeValue := ⟨13669, pr13669⟩
private theorem pr13679 : PrimeCertificate 13679 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv977]) (by decide +kernel)
def pv13679 : PrimeValue := ⟨13679, pr13679⟩
private theorem pr13681 : PrimeCertificate 13681 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv13681 : PrimeValue := ⟨13681, pr13681⟩
private theorem pr13687 : PrimeCertificate 13687 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv2281]) (by decide +kernel)
def pv13687 : PrimeValue := ⟨13687, pr13687⟩
private theorem pr13691 : PrimeCertificate 13691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv37]) (by decide +kernel)
def pv13691 : PrimeValue := ⟨13691, pr13691⟩
private theorem pr13693 : PrimeCertificate 13693 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv163]) (by decide +kernel)
def pv13693 : PrimeValue := ⟨13693, pr13693⟩
private theorem pr13697 : PrimeCertificate 13697 :=
  certifyPrime (q := pv3) (ls := [pv2,pv107]) (by decide +kernel)
def pv13697 : PrimeValue := ⟨13697, pr13697⟩
private theorem pr13709 : PrimeCertificate 13709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv149]) (by decide +kernel)
def pv13709 : PrimeValue := ⟨13709, pr13709⟩
private theorem pr13711 : PrimeCertificate 13711 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv457]) (by decide +kernel)
def pv13711 : PrimeValue := ⟨13711, pr13711⟩
private theorem pr13721 : PrimeCertificate 13721 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7]) (by decide +kernel)
def pv13721 : PrimeValue := ⟨13721, pr13721⟩
private theorem pr13723 : PrimeCertificate 13723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv2287]) (by decide +kernel)
def pv13723 : PrimeValue := ⟨13723, pr13723⟩
private theorem pr13729 : PrimeCertificate 13729 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv11,pv13]) (by decide +kernel)
def pv13729 : PrimeValue := ⟨13729, pr13729⟩
private theorem pr13751 : PrimeCertificate 13751 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11]) (by decide +kernel)
def pv13751 : PrimeValue := ⟨13751, pr13751⟩
private theorem pr13757 : PrimeCertificate 13757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv181]) (by decide +kernel)
def pv13757 : PrimeValue := ⟨13757, pr13757⟩
private theorem pr13759 : PrimeCertificate 13759 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv2293]) (by decide +kernel)
def pv13759 : PrimeValue := ⟨13759, pr13759⟩
private theorem pr13763 : PrimeCertificate 13763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv983]) (by decide +kernel)
def pv13763 : PrimeValue := ⟨13763, pr13763⟩
private theorem pr13781 : PrimeCertificate 13781 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv53]) (by decide +kernel)
def pv13781 : PrimeValue := ⟨13781, pr13781⟩
private theorem pr13789 : PrimeCertificate 13789 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv383]) (by decide +kernel)
def pv13789 : PrimeValue := ⟨13789, pr13789⟩
private theorem pr13799 : PrimeCertificate 13799 :=
  certifyPrime (q := pv7) (ls := [pv2,pv6899]) (by decide +kernel)
def pv13799 : PrimeValue := ⟨13799, pr13799⟩
private theorem pr13807 : PrimeCertificate 13807 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv59]) (by decide +kernel)
def pv13807 : PrimeValue := ⟨13807, pr13807⟩
private theorem pr13829 : PrimeCertificate 13829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3457]) (by decide +kernel)
def pv13829 : PrimeValue := ⟨13829, pr13829⟩
private theorem pr13831 : PrimeCertificate 13831 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv461]) (by decide +kernel)
def pv13831 : PrimeValue := ⟨13831, pr13831⟩
private theorem pr13841 : PrimeCertificate 13841 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv173]) (by decide +kernel)
def pv13841 : PrimeValue := ⟨13841, pr13841⟩
private theorem pr13859 : PrimeCertificate 13859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv41]) (by decide +kernel)
def pv13859 : PrimeValue := ⟨13859, pr13859⟩
private theorem pr13873 : PrimeCertificate 13873 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17]) (by decide +kernel)
def pv13873 : PrimeValue := ⟨13873, pr13873⟩
private theorem pr13877 : PrimeCertificate 13877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3469]) (by decide +kernel)
def pv13877 : PrimeValue := ⟨13877, pr13877⟩
private theorem pr13879 : PrimeCertificate 13879 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv257]) (by decide +kernel)
def pv13879 : PrimeValue := ⟨13879, pr13879⟩
private theorem pr13883 : PrimeCertificate 13883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv631]) (by decide +kernel)
def pv13883 : PrimeValue := ⟨13883, pr13883⟩
private theorem pr13901 : PrimeCertificate 13901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv139]) (by decide +kernel)
def pv13901 : PrimeValue := ⟨13901, pr13901⟩
private theorem pr13903 : PrimeCertificate 13903 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv331]) (by decide +kernel)
def pv13903 : PrimeValue := ⟨13903, pr13903⟩
private theorem pr13907 : PrimeCertificate 13907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv409]) (by decide +kernel)
def pv13907 : PrimeValue := ⟨13907, pr13907⟩
private theorem pr13913 : PrimeCertificate 13913 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv47]) (by decide +kernel)
def pv13913 : PrimeValue := ⟨13913, pr13913⟩
private theorem pr13921 : PrimeCertificate 13921 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv29]) (by decide +kernel)
def pv13921 : PrimeValue := ⟨13921, pr13921⟩
private theorem pr13931 : PrimeCertificate 13931 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv199]) (by decide +kernel)
def pv13931 : PrimeValue := ⟨13931, pr13931⟩
private theorem pr13933 : PrimeCertificate 13933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43]) (by decide +kernel)
def pv13933 : PrimeValue := ⟨13933, pr13933⟩
private theorem pr13963 : PrimeCertificate 13963 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv179]) (by decide +kernel)
def pv13963 : PrimeValue := ⟨13963, pr13963⟩
private theorem pr13967 : PrimeCertificate 13967 :=
  certifyPrime (q := pv5) (ls := [pv2,pv6983]) (by decide +kernel)
def pv13967 : PrimeValue := ⟨13967, pr13967⟩
private theorem pr13997 : PrimeCertificate 13997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3499]) (by decide +kernel)
def pv13997 : PrimeValue := ⟨13997, pr13997⟩
private theorem pr13999 : PrimeCertificate 13999 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv2333]) (by decide +kernel)
def pv13999 : PrimeValue := ⟨13999, pr13999⟩
private theorem pr14009 : PrimeCertificate 14009 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv103]) (by decide +kernel)
def pv14009 : PrimeValue := ⟨14009, pr14009⟩
private theorem pr14011 : PrimeCertificate 14011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv467]) (by decide +kernel)
def pv14011 : PrimeValue := ⟨14011, pr14011⟩
private theorem pr14029 : PrimeCertificate 14029 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv167]) (by decide +kernel)
def pv14029 : PrimeValue := ⟨14029, pr14029⟩
private theorem pr14033 : PrimeCertificate 14033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv877]) (by decide +kernel)
def pv14033 : PrimeValue := ⟨14033, pr14033⟩
private theorem pr14051 : PrimeCertificate 14051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv281]) (by decide +kernel)
def pv14051 : PrimeValue := ⟨14051, pr14051⟩
private theorem pr14057 : PrimeCertificate 14057 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv251]) (by decide +kernel)
def pv14057 : PrimeValue := ⟨14057, pr14057⟩
private theorem pr14071 : PrimeCertificate 14071 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv67]) (by decide +kernel)
def pv14071 : PrimeValue := ⟨14071, pr14071⟩
private theorem pr14081 : PrimeCertificate 14081 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11]) (by decide +kernel)
def pv14081 : PrimeValue := ⟨14081, pr14081⟩
private theorem pr14083 : PrimeCertificate 14083 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv2347]) (by decide +kernel)
def pv14083 : PrimeValue := ⟨14083, pr14083⟩
private theorem pr14087 : PrimeCertificate 14087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7043]) (by decide +kernel)
def pv14087 : PrimeValue := ⟨14087, pr14087⟩
private theorem pr14107 : PrimeCertificate 14107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv2351]) (by decide +kernel)
def pv14107 : PrimeValue := ⟨14107, pr14107⟩
private theorem pr14143 : PrimeCertificate 14143 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv2357]) (by decide +kernel)
def pv14143 : PrimeValue := ⟨14143, pr14143⟩
private theorem pr14149 : PrimeCertificate 14149 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv131]) (by decide +kernel)
def pv14149 : PrimeValue := ⟨14149, pr14149⟩
private theorem pr14153 : PrimeCertificate 14153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv61]) (by decide +kernel)
def pv14153 : PrimeValue := ⟨14153, pr14153⟩
private theorem pr14159 : PrimeCertificate 14159 :=
  certifyPrime (q := pv13) (ls := [pv2,pv7079]) (by decide +kernel)
def pv14159 : PrimeValue := ⟨14159, pr14159⟩
private theorem pr14173 : PrimeCertificate 14173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1181]) (by decide +kernel)
def pv14173 : PrimeValue := ⟨14173, pr14173⟩
private theorem pr14177 : PrimeCertificate 14177 :=
  certifyPrime (q := pv3) (ls := [pv2,pv443]) (by decide +kernel)
def pv14177 : PrimeValue := ⟨14177, pr14177⟩
private theorem pr14197 : PrimeCertificate 14197 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv13]) (by decide +kernel)
def pv14197 : PrimeValue := ⟨14197, pr14197⟩
private theorem pr14207 : PrimeCertificate 14207 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7103]) (by decide +kernel)
def pv14207 : PrimeValue := ⟨14207, pr14207⟩
private theorem pr14221 : PrimeCertificate 14221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv79]) (by decide +kernel)
def pv14221 : PrimeValue := ⟨14221, pr14221⟩
private theorem pr14243 : PrimeCertificate 14243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7121]) (by decide +kernel)
def pv14243 : PrimeValue := ⟨14243, pr14243⟩
private theorem pr14249 : PrimeCertificate 14249 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv137]) (by decide +kernel)
def pv14249 : PrimeValue := ⟨14249, pr14249⟩
private theorem pr14251 : PrimeCertificate 14251 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv14251 : PrimeValue := ⟨14251, pr14251⟩
private theorem pr14281 : PrimeCertificate 14281 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv7,pv17]) (by decide +kernel)
def pv14281 : PrimeValue := ⟨14281, pr14281⟩
private theorem pr14293 : PrimeCertificate 14293 :=
  certifyPrime (q := pv47) (ls := [pv2,pv3,pv397]) (by decide +kernel)
def pv14293 : PrimeValue := ⟨14293, pr14293⟩
private theorem pr14303 : PrimeCertificate 14303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7151]) (by decide +kernel)
def pv14303 : PrimeValue := ⟨14303, pr14303⟩
private theorem pr14321 : PrimeCertificate 14321 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv179]) (by decide +kernel)
def pv14321 : PrimeValue := ⟨14321, pr14321⟩
private theorem pr14323 : PrimeCertificate 14323 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv31]) (by decide +kernel)
def pv14323 : PrimeValue := ⟨14323, pr14323⟩
private theorem pr14327 : PrimeCertificate 14327 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv19,pv29]) (by decide +kernel)
def pv14327 : PrimeValue := ⟨14327, pr14327⟩
private theorem pr14341 : PrimeCertificate 14341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv239]) (by decide +kernel)
def pv14341 : PrimeValue := ⟨14341, pr14341⟩
private theorem pr14347 : PrimeCertificate 14347 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv797]) (by decide +kernel)
def pv14347 : PrimeValue := ⟨14347, pr14347⟩
private theorem pr14369 : PrimeCertificate 14369 :=
  certifyPrime (q := pv3) (ls := [pv2,pv449]) (by decide +kernel)
def pv14369 : PrimeValue := ⟨14369, pr14369⟩
private theorem pr14387 : PrimeCertificate 14387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7193]) (by decide +kernel)
def pv14387 : PrimeValue := ⟨14387, pr14387⟩
private theorem pr14389 : PrimeCertificate 14389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv109]) (by decide +kernel)
def pv14389 : PrimeValue := ⟨14389, pr14389⟩
private theorem pr14401 : PrimeCertificate 14401 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv14401 : PrimeValue := ⟨14401, pr14401⟩
private theorem pr14407 : PrimeCertificate 14407 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv14407 : PrimeValue := ⟨14407, pr14407⟩
private theorem pr14411 : PrimeCertificate 14411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv131]) (by decide +kernel)
def pv14411 : PrimeValue := ⟨14411, pr14411⟩
private theorem pr14419 : PrimeCertificate 14419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv89]) (by decide +kernel)
def pv14419 : PrimeValue := ⟨14419, pr14419⟩
private theorem pr14423 : PrimeCertificate 14423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7211]) (by decide +kernel)
def pv14423 : PrimeValue := ⟨14423, pr14423⟩
private theorem pr14431 : PrimeCertificate 14431 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv37]) (by decide +kernel)
def pv14431 : PrimeValue := ⟨14431, pr14431⟩
private theorem pr14437 : PrimeCertificate 14437 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv401]) (by decide +kernel)
def pv14437 : PrimeValue := ⟨14437, pr14437⟩
private theorem pr14447 : PrimeCertificate 14447 :=
  certifyPrime (q := pv5) (ls := [pv2,pv31,pv233]) (by decide +kernel)
def pv14447 : PrimeValue := ⟨14447, pr14447⟩
private theorem pr14449 : PrimeCertificate 14449 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv7,pv43]) (by decide +kernel)
def pv14449 : PrimeValue := ⟨14449, pr14449⟩
private theorem pr14461 : PrimeCertificate 14461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv241]) (by decide +kernel)
def pv14461 : PrimeValue := ⟨14461, pr14461⟩
private theorem pr14479 : PrimeCertificate 14479 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv127]) (by decide +kernel)
def pv14479 : PrimeValue := ⟨14479, pr14479⟩
private theorem pr14489 : PrimeCertificate 14489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1811]) (by decide +kernel)
def pv14489 : PrimeValue := ⟨14489, pr14489⟩
private theorem pr14503 : PrimeCertificate 14503 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv2417]) (by decide +kernel)
def pv14503 : PrimeValue := ⟨14503, pr14503⟩
private theorem pr14519 : PrimeCertificate 14519 :=
  certifyPrime (q := pv13) (ls := [pv2,pv7,pv17,pv61]) (by decide +kernel)
def pv14519 : PrimeValue := ⟨14519, pr14519⟩
private theorem pr14533 : PrimeCertificate 14533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv173]) (by decide +kernel)
def pv14533 : PrimeValue := ⟨14533, pr14533⟩
private theorem pr14537 : PrimeCertificate 14537 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv79]) (by decide +kernel)
def pv14537 : PrimeValue := ⟨14537, pr14537⟩
private theorem pr14543 : PrimeCertificate 14543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv661]) (by decide +kernel)
def pv14543 : PrimeValue := ⟨14543, pr14543⟩
private theorem pr14549 : PrimeCertificate 14549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3637]) (by decide +kernel)
def pv14549 : PrimeValue := ⟨14549, pr14549⟩
private theorem pr14551 : PrimeCertificate 14551 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv97]) (by decide +kernel)
def pv14551 : PrimeValue := ⟨14551, pr14551⟩
private theorem pr14557 : PrimeCertificate 14557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1213]) (by decide +kernel)
def pv14557 : PrimeValue := ⟨14557, pr14557⟩
private theorem pr14561 : PrimeCertificate 14561 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv13]) (by decide +kernel)
def pv14561 : PrimeValue := ⟨14561, pr14561⟩
private theorem pr14563 : PrimeCertificate 14563 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv809]) (by decide +kernel)
def pv14563 : PrimeValue := ⟨14563, pr14563⟩
private theorem pr14591 : PrimeCertificate 14591 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv1459]) (by decide +kernel)
def pv14591 : PrimeValue := ⟨14591, pr14591⟩
private theorem pr14593 : PrimeCertificate 14593 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19]) (by decide +kernel)
def pv14593 : PrimeValue := ⟨14593, pr14593⟩
private theorem pr14621 : PrimeCertificate 14621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv43]) (by decide +kernel)
def pv14621 : PrimeValue := ⟨14621, pr14621⟩
private theorem pr14627 : PrimeCertificate 14627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71,pv103]) (by decide +kernel)
def pv14627 : PrimeValue := ⟨14627, pr14627⟩
private theorem pr14629 : PrimeCertificate 14629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv53]) (by decide +kernel)
def pv14629 : PrimeValue := ⟨14629, pr14629⟩
private theorem pr14633 : PrimeCertificate 14633 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv59]) (by decide +kernel)
def pv14633 : PrimeValue := ⟨14633, pr14633⟩
private theorem pr14639 : PrimeCertificate 14639 :=
  certifyPrime (q := pv11) (ls := [pv2,pv13,pv563]) (by decide +kernel)
def pv14639 : PrimeValue := ⟨14639, pr14639⟩
private theorem pr14653 : PrimeCertificate 14653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv37]) (by decide +kernel)
def pv14653 : PrimeValue := ⟨14653, pr14653⟩
private theorem pr14657 : PrimeCertificate 14657 :=
  certifyPrime (q := pv3) (ls := [pv2,pv229]) (by decide +kernel)
def pv14657 : PrimeValue := ⟨14657, pr14657⟩
private theorem pr14669 : PrimeCertificate 14669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv193]) (by decide +kernel)
def pv14669 : PrimeValue := ⟨14669, pr14669⟩
private theorem pr14683 : PrimeCertificate 14683 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv2447]) (by decide +kernel)
def pv14683 : PrimeValue := ⟨14683, pr14683⟩
private theorem pr14699 : PrimeCertificate 14699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7349]) (by decide +kernel)
def pv14699 : PrimeValue := ⟨14699, pr14699⟩
private theorem pr14713 : PrimeCertificate 14713 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv613]) (by decide +kernel)
def pv14713 : PrimeValue := ⟨14713, pr14713⟩
private theorem pr14717 : PrimeCertificate 14717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv283]) (by decide +kernel)
def pv14717 : PrimeValue := ⟨14717, pr14717⟩
private theorem pr14723 : PrimeCertificate 14723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv433]) (by decide +kernel)
def pv14723 : PrimeValue := ⟨14723, pr14723⟩
private theorem pr14731 : PrimeCertificate 14731 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv5,pv491]) (by decide +kernel)
def pv14731 : PrimeValue := ⟨14731, pr14731⟩
private theorem pr14737 : PrimeCertificate 14737 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv307]) (by decide +kernel)
def pv14737 : PrimeValue := ⟨14737, pr14737⟩
private theorem pr14741 : PrimeCertificate 14741 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv67]) (by decide +kernel)
def pv14741 : PrimeValue := ⟨14741, pr14741⟩
private theorem pr14747 : PrimeCertificate 14747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv101]) (by decide +kernel)
def pv14747 : PrimeValue := ⟨14747, pr14747⟩
private theorem pr14753 : PrimeCertificate 14753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv461]) (by decide +kernel)
def pv14753 : PrimeValue := ⟨14753, pr14753⟩
private theorem pr14759 : PrimeCertificate 14759 :=
  certifyPrime (q := pv17) (ls := [pv2,pv47,pv157]) (by decide +kernel)
def pv14759 : PrimeValue := ⟨14759, pr14759⟩
private theorem pr14767 : PrimeCertificate 14767 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv107]) (by decide +kernel)
def pv14767 : PrimeValue := ⟨14767, pr14767⟩
private theorem pr14771 : PrimeCertificate 14771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv211]) (by decide +kernel)
def pv14771 : PrimeValue := ⟨14771, pr14771⟩
private theorem pr14779 : PrimeCertificate 14779 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv821]) (by decide +kernel)
def pv14779 : PrimeValue := ⟨14779, pr14779⟩
private theorem pr14783 : PrimeCertificate 14783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv389]) (by decide +kernel)
def pv14783 : PrimeValue := ⟨14783, pr14783⟩
private theorem pr14797 : PrimeCertificate 14797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv137]) (by decide +kernel)
def pv14797 : PrimeValue := ⟨14797, pr14797⟩
private theorem pr14813 : PrimeCertificate 14813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv23]) (by decide +kernel)
def pv14813 : PrimeValue := ⟨14813, pr14813⟩
private theorem pr14821 : PrimeCertificate 14821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv19]) (by decide +kernel)
def pv14821 : PrimeValue := ⟨14821, pr14821⟩
private theorem pr14827 : PrimeCertificate 14827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv353]) (by decide +kernel)
def pv14827 : PrimeValue := ⟨14827, pr14827⟩
private theorem pr14831 : PrimeCertificate 14831 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv1483]) (by decide +kernel)
def pv14831 : PrimeValue := ⟨14831, pr14831⟩
private theorem pr14843 : PrimeCertificate 14843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv181]) (by decide +kernel)
def pv14843 : PrimeValue := ⟨14843, pr14843⟩
private theorem pr14851 : PrimeCertificate 14851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv14851 : PrimeValue := ⟨14851, pr14851⟩
private theorem pr14867 : PrimeCertificate 14867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7433]) (by decide +kernel)
def pv14867 : PrimeValue := ⟨14867, pr14867⟩
private theorem pr14869 : PrimeCertificate 14869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv59]) (by decide +kernel)
def pv14869 : PrimeValue := ⟨14869, pr14869⟩
private theorem pr14879 : PrimeCertificate 14879 :=
  certifyPrime (q := pv7) (ls := [pv2,pv43,pv173]) (by decide +kernel)
def pv14879 : PrimeValue := ⟨14879, pr14879⟩
private theorem pr14887 : PrimeCertificate 14887 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv827]) (by decide +kernel)
def pv14887 : PrimeValue := ⟨14887, pr14887⟩
private theorem pr14891 : PrimeCertificate 14891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1489]) (by decide +kernel)
def pv14891 : PrimeValue := ⟨14891, pr14891⟩
private theorem pr14897 : PrimeCertificate 14897 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv19]) (by decide +kernel)
def pv14897 : PrimeValue := ⟨14897, pr14897⟩
private theorem pr14923 : PrimeCertificate 14923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv829]) (by decide +kernel)
def pv14923 : PrimeValue := ⟨14923, pr14923⟩
private theorem pr14929 : PrimeCertificate 14929 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv311]) (by decide +kernel)
def pv14929 : PrimeValue := ⟨14929, pr14929⟩
private theorem pr14939 : PrimeCertificate 14939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv97]) (by decide +kernel)
def pv14939 : PrimeValue := ⟨14939, pr14939⟩
private theorem pr14947 : PrimeCertificate 14947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv53]) (by decide +kernel)
def pv14947 : PrimeValue := ⟨14947, pr14947⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
