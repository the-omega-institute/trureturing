/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table086
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table086.pv303907
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table013
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table020
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table021
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table053
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table054

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr303907 : PrimeCertificate 303907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv50651]) (by decide +kernel)
def pv303907 : PrimeValue := ⟨303907, pr303907⟩
private theorem pr303959 : PrimeCertificate 303959 :=
  certifyPrime (q := pv13) (ls := [pv2,pv379,pv401]) (by decide +kernel)
def pv303959 : PrimeValue := ⟨303959, pr303959⟩
private theorem pr303983 : PrimeCertificate 303983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv21713]) (by decide +kernel)
def pv303983 : PrimeValue := ⟨303983, pr303983⟩
private theorem pr304009 : PrimeCertificate 304009 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv53,pv239]) (by decide +kernel)
def pv304009 : PrimeValue := ⟨304009, pr304009⟩
private theorem pr304039 : PrimeCertificate 304039 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv19,pv127]) (by decide +kernel)
def pv304039 : PrimeValue := ⟨304039, pr304039⟩
private theorem pr304049 : PrimeCertificate 304049 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv613]) (by decide +kernel)
def pv304049 : PrimeValue := ⟨304049, pr304049⟩
private theorem pr304063 : PrimeCertificate 304063 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv17,pv271]) (by decide +kernel)
def pv304063 : PrimeValue := ⟨304063, pr304063⟩
private theorem pr304067 : PrimeCertificate 304067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv37,pv587]) (by decide +kernel)
def pv304067 : PrimeValue := ⟨304067, pr304067⟩
private theorem pr304069 : PrimeCertificate 304069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv25339]) (by decide +kernel)
def pv304069 : PrimeValue := ⟨304069, pr304069⟩
private theorem pr304081 : PrimeCertificate 304081 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv181]) (by decide +kernel)
def pv304081 : PrimeValue := ⟨304081, pr304081⟩
private theorem pr304151 : PrimeCertificate 304151 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv11,pv79]) (by decide +kernel)
def pv304151 : PrimeValue := ⟨304151, pr304151⟩
private theorem pr304153 : PrimeCertificate 304153 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv19,pv23,pv29]) (by decide +kernel)
def pv304153 : PrimeValue := ⟨304153, pr304153⟩
private theorem pr304169 : PrimeCertificate 304169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv193,pv197]) (by decide +kernel)
def pv304169 : PrimeValue := ⟨304169, pr304169⟩
private theorem pr304211 : PrimeCertificate 304211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29,pv1049]) (by decide +kernel)
def pv304211 : PrimeValue := ⟨304211, pr304211⟩
private theorem pr304259 : PrimeCertificate 304259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv149,pv1021]) (by decide +kernel)
def pv304259 : PrimeValue := ⟨304259, pr304259⟩
private theorem pr304303 : PrimeCertificate 304303 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41,pv1237]) (by decide +kernel)
def pv304303 : PrimeValue := ⟨304303, pr304303⟩
private theorem pr304373 : PrimeCertificate 304373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv1619]) (by decide +kernel)
def pv304373 : PrimeValue := ⟨304373, pr304373⟩
private theorem pr304417 : PrimeCertificate 304417 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv7,pv151]) (by decide +kernel)
def pv304417 : PrimeValue := ⟨304417, pr304417⟩
private theorem pr304457 : PrimeCertificate 304457 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv2003]) (by decide +kernel)
def pv304457 : PrimeValue := ⟨304457, pr304457⟩
private theorem pr304477 : PrimeCertificate 304477 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv25373]) (by decide +kernel)
def pv304477 : PrimeValue := ⟨304477, pr304477⟩
private theorem pr304481 : PrimeCertificate 304481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv173]) (by decide +kernel)
def pv304481 : PrimeValue := ⟨304481, pr304481⟩
private theorem pr304489 : PrimeCertificate 304489 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv4229]) (by decide +kernel)
def pv304489 : PrimeValue := ⟨304489, pr304489⟩
private theorem pr304511 : PrimeCertificate 304511 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv37,pv823]) (by decide +kernel)
def pv304511 : PrimeValue := ⟨304511, pr304511⟩
private theorem pr304517 : PrimeCertificate 304517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv76129]) (by decide +kernel)
def pv304517 : PrimeValue := ⟨304517, pr304517⟩
private theorem pr304523 : PrimeCertificate 304523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv107,pv1423]) (by decide +kernel)
def pv304523 : PrimeValue := ⟨304523, pr304523⟩
private theorem pr304553 : PrimeCertificate 304553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv38069]) (by decide +kernel)
def pv304553 : PrimeValue := ⟨304553, pr304553⟩
private theorem pr304561 : PrimeCertificate 304561 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv47]) (by decide +kernel)
def pv304561 : PrimeValue := ⟨304561, pr304561⟩
private theorem pr304597 : PrimeCertificate 304597 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv8461]) (by decide +kernel)
def pv304597 : PrimeValue := ⟨304597, pr304597⟩
private theorem pr304631 : PrimeCertificate 304631 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv41,pv743]) (by decide +kernel)
def pv304631 : PrimeValue := ⟨304631, pr304631⟩
private theorem pr304663 : PrimeCertificate 304663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv50777]) (by decide +kernel)
def pv304663 : PrimeValue := ⟨304663, pr304663⟩
private theorem pr304687 : PrimeCertificate 304687 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv16927]) (by decide +kernel)
def pv304687 : PrimeValue := ⟨304687, pr304687⟩
private theorem pr304751 : PrimeCertificate 304751 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv23,pv53]) (by decide +kernel)
def pv304751 : PrimeValue := ⟨304751, pr304751⟩
private theorem pr304757 : PrimeCertificate 304757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv1249]) (by decide +kernel)
def pv304757 : PrimeValue := ⟨304757, pr304757⟩
private theorem pr304763 : PrimeCertificate 304763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv152381]) (by decide +kernel)
def pv304763 : PrimeValue := ⟨304763, pr304763⟩
private theorem pr304771 : PrimeCertificate 304771 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv10159]) (by decide +kernel)
def pv304771 : PrimeValue := ⟨304771, pr304771⟩
private theorem pr304867 : PrimeCertificate 304867 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv16937]) (by decide +kernel)
def pv304867 : PrimeValue := ⟨304867, pr304867⟩
private theorem pr304883 : PrimeCertificate 304883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv152441]) (by decide +kernel)
def pv304883 : PrimeValue := ⟨304883, pr304883⟩
private theorem pr304897 : PrimeCertificate 304897 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv397]) (by decide +kernel)
def pv304897 : PrimeValue := ⟨304897, pr304897⟩
private theorem pr304901 : PrimeCertificate 304901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv3049]) (by decide +kernel)
def pv304901 : PrimeValue := ⟨304901, pr304901⟩
private theorem pr304903 : PrimeCertificate 304903 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv1303]) (by decide +kernel)
def pv304903 : PrimeValue := ⟨304903, pr304903⟩
private theorem pr304907 : PrimeCertificate 304907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv29,pv751]) (by decide +kernel)
def pv304907 : PrimeValue := ⟨304907, pr304907⟩
private theorem pr304933 : PrimeCertificate 304933 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv25411]) (by decide +kernel)
def pv304933 : PrimeValue := ⟨304933, pr304933⟩
private theorem pr304937 : PrimeCertificate 304937 :=
  certifyPrime (q := pv3) (ls := [pv2,pv47,pv811]) (by decide +kernel)
def pv304937 : PrimeValue := ⟨304937, pr304937⟩
private theorem pr304943 : PrimeCertificate 304943 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv83,pv167]) (by decide +kernel)
def pv304943 : PrimeValue := ⟨304943, pr304943⟩
private theorem pr304961 : PrimeCertificate 304961 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv953]) (by decide +kernel)
def pv304961 : PrimeValue := ⟨304961, pr304961⟩
private theorem pr305093 : PrimeCertificate 305093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89,pv857]) (by decide +kernel)
def pv305093 : PrimeValue := ⟨305093, pr305093⟩
private theorem pr305101 : PrimeCertificate 305101 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv113]) (by decide +kernel)
def pv305101 : PrimeValue := ⟨305101, pr305101⟩
private theorem pr305143 : PrimeCertificate 305143 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv50857]) (by decide +kernel)
def pv305143 : PrimeValue := ⟨305143, pr305143⟩
private theorem pr305219 : PrimeCertificate 305219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv47,pv191]) (by decide +kernel)
def pv305219 : PrimeValue := ⟨305219, pr305219⟩
private theorem pr305231 : PrimeCertificate 305231 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv131,pv233]) (by decide +kernel)
def pv305231 : PrimeValue := ⟨305231, pr305231⟩
private theorem pr305297 : PrimeCertificate 305297 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19081]) (by decide +kernel)
def pv305297 : PrimeValue := ⟨305297, pr305297⟩
private theorem pr305329 : PrimeCertificate 305329 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv6361]) (by decide +kernel)
def pv305329 : PrimeValue := ⟨305329, pr305329⟩
private theorem pr305351 : PrimeCertificate 305351 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv31,pv197]) (by decide +kernel)
def pv305351 : PrimeValue := ⟨305351, pr305351⟩
private theorem pr305353 : PrimeCertificate 305353 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv4241]) (by decide +kernel)
def pv305353 : PrimeValue := ⟨305353, pr305353⟩
private theorem pr305363 : PrimeCertificate 305363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv152681]) (by decide +kernel)
def pv305363 : PrimeValue := ⟨305363, pr305363⟩
private theorem pr305369 : PrimeCertificate 305369 :=
  certifyPrime (q := pv37) (ls := [pv2,pv7,pv19,pv41]) (by decide +kernel)
def pv305369 : PrimeValue := ⟨305369, pr305369⟩
private theorem pr305401 : PrimeCertificate 305401 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv509]) (by decide +kernel)
def pv305401 : PrimeValue := ⟨305401, pr305401⟩
private theorem pr305411 : PrimeCertificate 305411 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv4363]) (by decide +kernel)
def pv305411 : PrimeValue := ⟨305411, pr305411⟩
private theorem pr305413 : PrimeCertificate 305413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv821]) (by decide +kernel)
def pv305413 : PrimeValue := ⟨305413, pr305413⟩
private theorem pr305423 : PrimeCertificate 305423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv17,pv691]) (by decide +kernel)
def pv305423 : PrimeValue := ⟨305423, pr305423⟩
private theorem pr305477 : PrimeCertificate 305477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv76369]) (by decide +kernel)
def pv305477 : PrimeValue := ⟨305477, pr305477⟩
private theorem pr305479 : PrimeCertificate 305479 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5657]) (by decide +kernel)
def pv305479 : PrimeValue := ⟨305479, pr305479⟩
private theorem pr305497 : PrimeCertificate 305497 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4243]) (by decide +kernel)
def pv305497 : PrimeValue := ⟨305497, pr305497⟩
private theorem pr305521 : PrimeCertificate 305521 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv19,pv67]) (by decide +kernel)
def pv305521 : PrimeValue := ⟨305521, pr305521⟩
private theorem pr305533 : PrimeCertificate 305533 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv23,pv41]) (by decide +kernel)
def pv305533 : PrimeValue := ⟨305533, pr305533⟩
private theorem pr305563 : PrimeCertificate 305563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv127,pv401]) (by decide +kernel)
def pv305563 : PrimeValue := ⟨305563, pr305563⟩
private theorem pr305581 : PrimeCertificate 305581 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv463]) (by decide +kernel)
def pv305581 : PrimeValue := ⟨305581, pr305581⟩
private theorem pr305593 : PrimeCertificate 305593 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv17,pv107]) (by decide +kernel)
def pv305593 : PrimeValue := ⟨305593, pr305593⟩
private theorem pr305603 : PrimeCertificate 305603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv29,pv479]) (by decide +kernel)
def pv305603 : PrimeValue := ⟨305603, pr305603⟩
private theorem pr305611 : PrimeCertificate 305611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv61,pv167]) (by decide +kernel)
def pv305611 : PrimeValue := ⟨305611, pr305611⟩
private theorem pr305639 : PrimeCertificate 305639 :=
  certifyPrime (q := pv11) (ls := [pv2,pv152819]) (by decide +kernel)
def pv305639 : PrimeValue := ⟨305639, pr305639⟩
private theorem pr305717 : PrimeCertificate 305717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv3323]) (by decide +kernel)
def pv305717 : PrimeValue := ⟨305717, pr305717⟩
private theorem pr305741 : PrimeCertificate 305741 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv15287]) (by decide +kernel)
def pv305741 : PrimeValue := ⟨305741, pr305741⟩
private theorem pr305761 : PrimeCertificate 305761 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv7,pv13]) (by decide +kernel)
def pv305761 : PrimeValue := ⟨305761, pr305761⟩
private theorem pr305771 : PrimeCertificate 305771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv30577]) (by decide +kernel)
def pv305771 : PrimeValue := ⟨305771, pr305771⟩
private theorem pr305839 : PrimeCertificate 305839 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv1307]) (by decide +kernel)
def pv305839 : PrimeValue := ⟨305839, pr305839⟩
private theorem pr305861 : PrimeCertificate 305861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41,pv373]) (by decide +kernel)
def pv305861 : PrimeValue := ⟨305861, pr305861⟩
private theorem pr305999 : PrimeCertificate 305999 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv11,pv1987]) (by decide +kernel)
def pv305999 : PrimeValue := ⟨305999, pr305999⟩
private theorem pr306011 : PrimeCertificate 306011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv71,pv431]) (by decide +kernel)
def pv306011 : PrimeValue := ⟨306011, pr306011⟩
private theorem pr306041 : PrimeCertificate 306041 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv1093]) (by decide +kernel)
def pv306041 : PrimeValue := ⟨306041, pr306041⟩
private theorem pr306121 : PrimeCertificate 306121 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv2551]) (by decide +kernel)
def pv306121 : PrimeValue := ⟨306121, pr306121⟩
private theorem pr306133 : PrimeCertificate 306133 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv97,pv263]) (by decide +kernel)
def pv306133 : PrimeValue := ⟨306133, pr306133⟩
private theorem pr306139 : PrimeCertificate 306139 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv37,pv197]) (by decide +kernel)
def pv306139 : PrimeValue := ⟨306139, pr306139⟩
private theorem pr306157 : PrimeCertificate 306157 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv823]) (by decide +kernel)
def pv306157 : PrimeValue := ⟨306157, pr306157⟩
private theorem pr306169 : PrimeCertificate 306169 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv12757]) (by decide +kernel)
def pv306169 : PrimeValue := ⟨306169, pr306169⟩
private theorem pr306191 : PrimeCertificate 306191 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv67,pv457]) (by decide +kernel)
def pv306191 : PrimeValue := ⟨306191, pr306191⟩
private theorem pr306193 : PrimeCertificate 306193 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv6379]) (by decide +kernel)
def pv306193 : PrimeValue := ⟨306193, pr306193⟩
private theorem pr306239 : PrimeCertificate 306239 :=
  certifyPrime (q := pv13) (ls := [pv2,pv17,pv9007]) (by decide +kernel)
def pv306239 : PrimeValue := ⟨306239, pr306239⟩
private theorem pr306253 : PrimeCertificate 306253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv181]) (by decide +kernel)
def pv306253 : PrimeValue := ⟨306253, pr306253⟩
private theorem pr306329 : PrimeCertificate 306329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv59]) (by decide +kernel)
def pv306329 : PrimeValue := ⟨306329, pr306329⟩
private theorem pr306349 : PrimeCertificate 306349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv521]) (by decide +kernel)
def pv306349 : PrimeValue := ⟨306349, pr306349⟩
private theorem pr306359 : PrimeCertificate 306359 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv11783]) (by decide +kernel)
def pv306359 : PrimeValue := ⟨306359, pr306359⟩
private theorem pr306367 : PrimeCertificate 306367 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv51061]) (by decide +kernel)
def pv306367 : PrimeValue := ⟨306367, pr306367⟩
private theorem pr306377 : PrimeCertificate 306377 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv5471]) (by decide +kernel)
def pv306377 : PrimeValue := ⟨306377, pr306377⟩
private theorem pr306407 : PrimeCertificate 306407 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv6661]) (by decide +kernel)
def pv306407 : PrimeValue := ⟨306407, pr306407⟩
private theorem pr306421 : PrimeCertificate 306421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv5107]) (by decide +kernel)
def pv306421 : PrimeValue := ⟨306421, pr306421⟩
private theorem pr306431 : PrimeCertificate 306431 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv30643]) (by decide +kernel)
def pv306431 : PrimeValue := ⟨306431, pr306431⟩
private theorem pr306457 : PrimeCertificate 306457 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv113]) (by decide +kernel)
def pv306457 : PrimeValue := ⟨306457, pr306457⟩
private theorem pr306463 : PrimeCertificate 306463 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv13,pv3929]) (by decide +kernel)
def pv306463 : PrimeValue := ⟨306463, pr306463⟩
private theorem pr306473 : PrimeCertificate 306473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv1321]) (by decide +kernel)
def pv306473 : PrimeValue := ⟨306473, pr306473⟩
private theorem pr306503 : PrimeCertificate 306503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv21893]) (by decide +kernel)
def pv306503 : PrimeValue := ⟨306503, pr306503⟩
private theorem pr306529 : PrimeCertificate 306529 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv31,pv103]) (by decide +kernel)
def pv306529 : PrimeValue := ⟨306529, pr306529⟩
private theorem pr306541 : PrimeCertificate 306541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv131]) (by decide +kernel)
def pv306541 : PrimeValue := ⟨306541, pr306541⟩
private theorem pr306577 : PrimeCertificate 306577 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2129]) (by decide +kernel)
def pv306577 : PrimeValue := ⟨306577, pr306577⟩
private theorem pr306653 : PrimeCertificate 306653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv2473]) (by decide +kernel)
def pv306653 : PrimeValue := ⟨306653, pr306653⟩
private theorem pr306661 : PrimeCertificate 306661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv269]) (by decide +kernel)
def pv306661 : PrimeValue := ⟨306661, pr306661⟩
private theorem pr306703 : PrimeCertificate 306703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv1549]) (by decide +kernel)
def pv306703 : PrimeValue := ⟨306703, pr306703⟩
private theorem pr306707 : PrimeCertificate 306707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv153353]) (by decide +kernel)
def pv306707 : PrimeValue := ⟨306707, pr306707⟩
private theorem pr306739 : PrimeCertificate 306739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17041]) (by decide +kernel)
def pv306739 : PrimeValue := ⟨306739, pr306739⟩
private theorem pr306749 : PrimeCertificate 306749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv17,pv347]) (by decide +kernel)
def pv306749 : PrimeValue := ⟨306749, pr306749⟩
private theorem pr306763 : PrimeCertificate 306763 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv29,pv41,pv43]) (by decide +kernel)
def pv306763 : PrimeValue := ⟨306763, pr306763⟩
private theorem pr306871 : PrimeCertificate 306871 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv53,pv193]) (by decide +kernel)
def pv306871 : PrimeValue := ⟨306871, pr306871⟩
private theorem pr306883 : PrimeCertificate 306883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5683]) (by decide +kernel)
def pv306883 : PrimeValue := ⟨306883, pr306883⟩
private theorem pr306913 : PrimeCertificate 306913 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv139]) (by decide +kernel)
def pv306913 : PrimeValue := ⟨306913, pr306913⟩
private theorem pr306941 : PrimeCertificate 306941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv103,pv149]) (by decide +kernel)
def pv306941 : PrimeValue := ⟨306941, pr306941⟩
private theorem pr306947 : PrimeCertificate 306947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv167,pv919]) (by decide +kernel)
def pv306947 : PrimeValue := ⟨306947, pr306947⟩
private theorem pr306949 : PrimeCertificate 306949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv25579]) (by decide +kernel)
def pv306949 : PrimeValue := ⟨306949, pr306949⟩
private theorem pr306991 : PrimeCertificate 306991 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv379]) (by decide +kernel)
def pv306991 : PrimeValue := ⟨306991, pr306991⟩
private theorem pr307009 : PrimeCertificate 307009 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv41]) (by decide +kernel)
def pv307009 : PrimeValue := ⟨307009, pr307009⟩
private theorem pr307031 : PrimeCertificate 307031 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv30703]) (by decide +kernel)
def pv307031 : PrimeValue := ⟨307031, pr307031⟩
private theorem pr307033 : PrimeCertificate 307033 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv1163]) (by decide +kernel)
def pv307033 : PrimeValue := ⟨307033, pr307033⟩
private theorem pr307091 : PrimeCertificate 307091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv41,pv107]) (by decide +kernel)
def pv307091 : PrimeValue := ⟨307091, pr307091⟩
private theorem pr307093 : PrimeCertificate 307093 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv157,pv163]) (by decide +kernel)
def pv307093 : PrimeValue := ⟨307093, pr307093⟩
private theorem pr307103 : PrimeCertificate 307103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv97,pv1583]) (by decide +kernel)
def pv307103 : PrimeValue := ⟨307103, pr307103⟩
private theorem pr307121 : PrimeCertificate 307121 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv349]) (by decide +kernel)
def pv307121 : PrimeValue := ⟨307121, pr307121⟩
private theorem pr307147 : PrimeCertificate 307147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv71,pv103]) (by decide +kernel)
def pv307147 : PrimeValue := ⟨307147, pr307147⟩
private theorem pr307169 : PrimeCertificate 307169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv331]) (by decide +kernel)
def pv307169 : PrimeValue := ⟨307169, pr307169⟩
private theorem pr307171 : PrimeCertificate 307171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv3413]) (by decide +kernel)
def pv307171 : PrimeValue := ⟨307171, pr307171⟩
private theorem pr307201 : PrimeCertificate 307201 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv307201 : PrimeValue := ⟨307201, pr307201⟩
private theorem pr307243 : PrimeCertificate 307243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv101]) (by decide +kernel)
def pv307243 : PrimeValue := ⟨307243, pr307243⟩
private theorem pr307261 : PrimeCertificate 307261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv569]) (by decide +kernel)
def pv307261 : PrimeValue := ⟨307261, pr307261⟩
private theorem pr307273 : PrimeCertificate 307273 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv31,pv59]) (by decide +kernel)
def pv307273 : PrimeValue := ⟨307273, pr307273⟩
private theorem pr307301 : PrimeCertificate 307301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv439]) (by decide +kernel)
def pv307301 : PrimeValue := ⟨307301, pr307301⟩
private theorem pr307381 : PrimeCertificate 307381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv47,pv109]) (by decide +kernel)
def pv307381 : PrimeValue := ⟨307381, pr307381⟩
private theorem pr307397 : PrimeCertificate 307397 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv37,pv67]) (by decide +kernel)
def pv307397 : PrimeValue := ⟨307397, pr307397⟩
private theorem pr307399 : PrimeCertificate 307399 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv563]) (by decide +kernel)
def pv307399 : PrimeValue := ⟨307399, pr307399⟩
private theorem pr307409 : PrimeCertificate 307409 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19213]) (by decide +kernel)
def pv307409 : PrimeValue := ⟨307409, pr307409⟩
private theorem pr307451 : PrimeCertificate 307451 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv13,pv43]) (by decide +kernel)
def pv307451 : PrimeValue := ⟨307451, pr307451⟩
private theorem pr307471 : PrimeCertificate 307471 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv37,pv277]) (by decide +kernel)
def pv307471 : PrimeValue := ⟨307471, pr307471⟩
private theorem pr307481 : PrimeCertificate 307481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7687]) (by decide +kernel)
def pv307481 : PrimeValue := ⟨307481, pr307481⟩
private theorem pr307523 : PrimeCertificate 307523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv179,pv859]) (by decide +kernel)
def pv307523 : PrimeValue := ⟨307523, pr307523⟩
private theorem pr307577 : PrimeCertificate 307577 :=
  certifyPrime (q := pv3) (ls := [pv2,pv38447]) (by decide +kernel)
def pv307577 : PrimeValue := ⟨307577, pr307577⟩
private theorem pr307583 : PrimeCertificate 307583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv31,pv41]) (by decide +kernel)
def pv307583 : PrimeValue := ⟨307583, pr307583⟩
private theorem pr307633 : PrimeCertificate 307633 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv17,pv29]) (by decide +kernel)
def pv307633 : PrimeValue := ⟨307633, pr307633⟩
private theorem pr307639 : PrimeCertificate 307639 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv211]) (by decide +kernel)
def pv307639 : PrimeValue := ⟨307639, pr307639⟩
private theorem pr307651 : PrimeCertificate 307651 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv293]) (by decide +kernel)
def pv307651 : PrimeValue := ⟨307651, pr307651⟩
private theorem pr307669 : PrimeCertificate 307669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv25639]) (by decide +kernel)
def pv307669 : PrimeValue := ⟨307669, pr307669⟩
private theorem pr307711 : PrimeCertificate 307711 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv263]) (by decide +kernel)
def pv307711 : PrimeValue := ⟨307711, pr307711⟩
private theorem pr307733 : PrimeCertificate 307733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv107,pv719]) (by decide +kernel)
def pv307733 : PrimeValue := ⟨307733, pr307733⟩
private theorem pr307817 : PrimeCertificate 307817 :=
  certifyPrime (q := pv3) (ls := [pv2,pv109,pv353]) (by decide +kernel)
def pv307817 : PrimeValue := ⟨307817, pr307817⟩
private theorem pr307823 : PrimeCertificate 307823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv153911]) (by decide +kernel)
def pv307823 : PrimeValue := ⟨307823, pr307823⟩
private theorem pr307843 : PrimeCertificate 307843 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv51307]) (by decide +kernel)
def pv307843 : PrimeValue := ⟨307843, pr307843⟩
private theorem pr307871 : PrimeCertificate 307871 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv17,pv1811]) (by decide +kernel)
def pv307871 : PrimeValue := ⟨307871, pr307871⟩
private theorem pr307873 : PrimeCertificate 307873 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1069]) (by decide +kernel)
def pv307873 : PrimeValue := ⟨307873, pr307873⟩
private theorem pr307891 : PrimeCertificate 307891 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv11,pv311]) (by decide +kernel)
def pv307891 : PrimeValue := ⟨307891, pr307891⟩
private theorem pr307903 : PrimeCertificate 307903 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv7331]) (by decide +kernel)
def pv307903 : PrimeValue := ⟨307903, pr307903⟩
private theorem pr307939 : PrimeCertificate 307939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv3019]) (by decide +kernel)
def pv307939 : PrimeValue := ⟨307939, pr307939⟩
private theorem pr307969 : PrimeCertificate 307969 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv401]) (by decide +kernel)
def pv307969 : PrimeValue := ⟨307969, pr307969⟩
private theorem pr308017 : PrimeCertificate 308017 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv31]) (by decide +kernel)
def pv308017 : PrimeValue := ⟨308017, pr308017⟩
private theorem pr308041 : PrimeCertificate 308041 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv17,pv151]) (by decide +kernel)
def pv308041 : PrimeValue := ⟨308041, pr308041⟩
private theorem pr308051 : PrimeCertificate 308051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv61,pv101]) (by decide +kernel)
def pv308051 : PrimeValue := ⟨308051, pr308051⟩
private theorem pr308101 : PrimeCertificate 308101 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv13,pv79]) (by decide +kernel)
def pv308101 : PrimeValue := ⟨308101, pr308101⟩
private theorem pr308117 : PrimeCertificate 308117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv77029]) (by decide +kernel)
def pv308117 : PrimeValue := ⟨308117, pr308117⟩
private theorem pr308137 : PrimeCertificate 308137 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv37,pv347]) (by decide +kernel)
def pv308137 : PrimeValue := ⟨308137, pr308137⟩
private theorem pr308141 : PrimeCertificate 308141 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv31,pv71]) (by decide +kernel)
def pv308141 : PrimeValue := ⟨308141, pr308141⟩
private theorem pr308153 : PrimeCertificate 308153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv2963]) (by decide +kernel)
def pv308153 : PrimeValue := ⟨308153, pr308153⟩
private theorem pr308213 : PrimeCertificate 308213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv2657]) (by decide +kernel)
def pv308213 : PrimeValue := ⟨308213, pr308213⟩
private theorem pr308219 : PrimeCertificate 308219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv8111]) (by decide +kernel)
def pv308219 : PrimeValue := ⟨308219, pr308219⟩
private theorem pr308249 : PrimeCertificate 308249 :=
  certifyPrime (q := pv3) (ls := [pv2,pv53,pv727]) (by decide +kernel)
def pv308249 : PrimeValue := ⟨308249, pr308249⟩
private theorem pr308263 : PrimeCertificate 308263 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv83,pv619]) (by decide +kernel)
def pv308263 : PrimeValue := ⟨308263, pr308263⟩
private theorem pr308293 : PrimeCertificate 308293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv1117]) (by decide +kernel)
def pv308293 : PrimeValue := ⟨308293, pr308293⟩
private theorem pr308309 : PrimeCertificate 308309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv13]) (by decide +kernel)
def pv308309 : PrimeValue := ⟨308309, pr308309⟩
private theorem pr308323 : PrimeCertificate 308323 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv2447]) (by decide +kernel)
def pv308323 : PrimeValue := ⟨308323, pr308323⟩
private theorem pr308359 : PrimeCertificate 308359 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37,pv463]) (by decide +kernel)
def pv308359 : PrimeValue := ⟨308359, pr308359⟩
private theorem pr308437 : PrimeCertificate 308437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv25703]) (by decide +kernel)
def pv308437 : PrimeValue := ⟨308437, pr308437⟩
private theorem pr308467 : PrimeCertificate 308467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17137]) (by decide +kernel)
def pv308467 : PrimeValue := ⟨308467, pr308467⟩
private theorem pr308491 : PrimeCertificate 308491 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv7,pv13,pv113]) (by decide +kernel)
def pv308491 : PrimeValue := ⟨308491, pr308491⟩
private theorem pr308507 : PrimeCertificate 308507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv37,pv379]) (by decide +kernel)
def pv308507 : PrimeValue := ⟨308507, pr308507⟩
private theorem pr308519 : PrimeCertificate 308519 :=
  certifyPrime (q := pv17) (ls := [pv2,pv7,pv22037]) (by decide +kernel)
def pv308519 : PrimeValue := ⟨308519, pr308519⟩
private theorem pr308521 : PrimeCertificate 308521 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv857]) (by decide +kernel)
def pv308521 : PrimeValue := ⟨308521, pr308521⟩
private theorem pr308527 : PrimeCertificate 308527 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv51421]) (by decide +kernel)
def pv308527 : PrimeValue := ⟨308527, pr308527⟩
private theorem pr308573 : PrimeCertificate 308573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv7013]) (by decide +kernel)
def pv308573 : PrimeValue := ⟨308573, pr308573⟩
private theorem pr308587 : PrimeCertificate 308587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv51431]) (by decide +kernel)
def pv308587 : PrimeValue := ⟨308587, pr308587⟩
private theorem pr308597 : PrimeCertificate 308597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv179,pv431]) (by decide +kernel)
def pv308597 : PrimeValue := ⟨308597, pr308597⟩
private theorem pr308621 : PrimeCertificate 308621 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv1187]) (by decide +kernel)
def pv308621 : PrimeValue := ⟨308621, pr308621⟩
private theorem pr308663 : PrimeCertificate 308663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv157,pv983]) (by decide +kernel)
def pv308663 : PrimeValue := ⟨308663, pr308663⟩
private theorem pr308681 : PrimeCertificate 308681 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7717]) (by decide +kernel)
def pv308681 : PrimeValue := ⟨308681, pr308681⟩
private theorem pr308713 : PrimeCertificate 308713 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv19,pv677]) (by decide +kernel)
def pv308713 : PrimeValue := ⟨308713, pr308713⟩
private theorem pr308723 : PrimeCertificate 308723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv163,pv947]) (by decide +kernel)
def pv308723 : PrimeValue := ⟨308723, pr308723⟩
private theorem pr308773 : PrimeCertificate 308773 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv953]) (by decide +kernel)
def pv308773 : PrimeValue := ⟨308773, pr308773⟩
private theorem pr308809 : PrimeCertificate 308809 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv4289]) (by decide +kernel)
def pv308809 : PrimeValue := ⟨308809, pr308809⟩
private theorem pr308827 : PrimeCertificate 308827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv19,pv43]) (by decide +kernel)
def pv308827 : PrimeValue := ⟨308827, pr308827⟩
private theorem pr308849 : PrimeCertificate 308849 :=
  certifyPrime (q := pv3) (ls := [pv2,pv97,pv199]) (by decide +kernel)
def pv308849 : PrimeValue := ⟨308849, pr308849⟩
private theorem pr308851 : PrimeCertificate 308851 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv29,pv71]) (by decide +kernel)
def pv308851 : PrimeValue := ⟨308851, pr308851⟩
private theorem pr308923 : PrimeCertificate 308923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv51487]) (by decide +kernel)
def pv308923 : PrimeValue := ⟨308923, pr308923⟩
private theorem pr308927 : PrimeCertificate 308927 :=
  certifyPrime (q := pv5) (ls := [pv2,pv83,pv1861]) (by decide +kernel)
def pv308927 : PrimeValue := ⟨308927, pr308927⟩
private theorem pr308939 : PrimeCertificate 308939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv22067]) (by decide +kernel)
def pv308939 : PrimeValue := ⟨308939, pr308939⟩
private theorem pr308999 : PrimeCertificate 308999 :=
  certifyPrime (q := pv11) (ls := [pv2,pv43,pv3593]) (by decide +kernel)
def pv308999 : PrimeValue := ⟨308999, pr308999⟩
private theorem pr309007 : PrimeCertificate 309007 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17167]) (by decide +kernel)
def pv309007 : PrimeValue := ⟨309007, pr309007⟩
private theorem pr309011 : PrimeCertificate 309011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv2377]) (by decide +kernel)
def pv309011 : PrimeValue := ⟨309011, pr309011⟩
private theorem pr309019 : PrimeCertificate 309019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv51503]) (by decide +kernel)
def pv309019 : PrimeValue := ⟨309019, pr309019⟩
private theorem pr309031 : PrimeCertificate 309031 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv10301]) (by decide +kernel)
def pv309031 : PrimeValue := ⟨309031, pr309031⟩
private theorem pr309037 : PrimeCertificate 309037 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv283]) (by decide +kernel)
def pv309037 : PrimeValue := ⟨309037, pr309037⟩
private theorem pr309059 : PrimeCertificate 309059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv3769]) (by decide +kernel)
def pv309059 : PrimeValue := ⟨309059, pr309059⟩
private theorem pr309079 : PrimeCertificate 309079 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv11,pv223]) (by decide +kernel)
def pv309079 : PrimeValue := ⟨309079, pr309079⟩
private theorem pr309107 : PrimeCertificate 309107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv22079]) (by decide +kernel)
def pv309107 : PrimeValue := ⟨309107, pr309107⟩
private theorem pr309131 : PrimeCertificate 309131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv1627]) (by decide +kernel)
def pv309131 : PrimeValue := ⟨309131, pr309131⟩
private theorem pr309157 : PrimeCertificate 309157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv25763]) (by decide +kernel)
def pv309157 : PrimeValue := ⟨309157, pr309157⟩
private theorem pr309167 : PrimeCertificate 309167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv13,pv23,pv47]) (by decide +kernel)
def pv309167 : PrimeValue := ⟨309167, pr309167⟩
private theorem pr309173 : PrimeCertificate 309173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv2089]) (by decide +kernel)
def pv309173 : PrimeValue := ⟨309173, pr309173⟩
private theorem pr309259 : PrimeCertificate 309259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv83]) (by decide +kernel)
def pv309259 : PrimeValue := ⟨309259, pr309259⟩
private theorem pr309271 : PrimeCertificate 309271 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv61]) (by decide +kernel)
def pv309271 : PrimeValue := ⟨309271, pr309271⟩
private theorem pr309289 : PrimeCertificate 309289 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv7,pv263]) (by decide +kernel)
def pv309289 : PrimeValue := ⟨309289, pr309289⟩
private theorem pr309293 : PrimeCertificate 309293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv77323]) (by decide +kernel)
def pv309293 : PrimeValue := ⟨309293, pr309293⟩
private theorem pr309311 : PrimeCertificate 309311 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv30931]) (by decide +kernel)
def pv309311 : PrimeValue := ⟨309311, pr309311⟩
private theorem pr309313 : PrimeCertificate 309313 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv179]) (by decide +kernel)
def pv309313 : PrimeValue := ⟨309313, pr309313⟩
private theorem pr309359 : PrimeCertificate 309359 :=
  certifyPrime (q := pv13) (ls := [pv2,pv7,pv19,pv1163]) (by decide +kernel)
def pv309359 : PrimeValue := ⟨309359, pr309359⟩
private theorem pr309371 : PrimeCertificate 309371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv30937]) (by decide +kernel)
def pv309371 : PrimeValue := ⟨309371, pr309371⟩
private theorem pr309391 : PrimeCertificate 309391 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv10313]) (by decide +kernel)
def pv309391 : PrimeValue := ⟨309391, pr309391⟩
private theorem pr309403 : PrimeCertificate 309403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17189]) (by decide +kernel)
def pv309403 : PrimeValue := ⟨309403, pr309403⟩
private theorem pr309433 : PrimeCertificate 309433 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv12893]) (by decide +kernel)
def pv309433 : PrimeValue := ⟨309433, pr309433⟩
private theorem pr309437 : PrimeCertificate 309437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv77359]) (by decide +kernel)
def pv309437 : PrimeValue := ⟨309437, pr309437⟩
private theorem pr309457 : PrimeCertificate 309457 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv307]) (by decide +kernel)
def pv309457 : PrimeValue := ⟨309457, pr309457⟩
private theorem pr309461 : PrimeCertificate 309461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv15473]) (by decide +kernel)
def pv309461 : PrimeValue := ⟨309461, pr309461⟩
private theorem pr309469 : PrimeCertificate 309469 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv17,pv37,pv41]) (by decide +kernel)
def pv309469 : PrimeValue := ⟨309469, pr309469⟩
private theorem pr309503 : PrimeCertificate 309503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv9103]) (by decide +kernel)
def pv309503 : PrimeValue := ⟨309503, pr309503⟩
private theorem pr309523 : PrimeCertificate 309523 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv79,pv653]) (by decide +kernel)
def pv309523 : PrimeValue := ⟨309523, pr309523⟩
private theorem pr309539 : PrimeCertificate 309539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv154769]) (by decide +kernel)
def pv309539 : PrimeValue := ⟨309539, pr309539⟩
private theorem pr309583 : PrimeCertificate 309583 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv13]) (by decide +kernel)
def pv309583 : PrimeValue := ⟨309583, pr309583⟩
private theorem pr309623 : PrimeCertificate 309623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv149,pv1039]) (by decide +kernel)
def pv309623 : PrimeValue := ⟨309623, pr309623⟩
private theorem pr309713 : PrimeCertificate 309713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv1489]) (by decide +kernel)
def pv309713 : PrimeValue := ⟨309713, pr309713⟩
private theorem pr309811 : PrimeCertificate 309811 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv23,pv449]) (by decide +kernel)
def pv309811 : PrimeValue := ⟨309811, pr309811⟩
private theorem pr309851 : PrimeCertificate 309851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv6197]) (by decide +kernel)
def pv309851 : PrimeValue := ⟨309851, pr309851⟩
private theorem pr309853 : PrimeCertificate 309853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv151]) (by decide +kernel)
def pv309853 : PrimeValue := ⟨309853, pr309853⟩
private theorem pr309877 : PrimeCertificate 309877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv31]) (by decide +kernel)
def pv309877 : PrimeValue := ⟨309877, pr309877⟩
private theorem pr309977 : PrimeCertificate 309977 :=
  certifyPrime (q := pv3) (ls := [pv2,pv38747]) (by decide +kernel)
def pv309977 : PrimeValue := ⟨309977, pr309977⟩
private theorem pr309989 : PrimeCertificate 309989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11071]) (by decide +kernel)
def pv309989 : PrimeValue := ⟨309989, pr309989⟩
private theorem pr310021 : PrimeCertificate 310021 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv5167]) (by decide +kernel)
def pv310021 : PrimeValue := ⟨310021, pr310021⟩
private theorem pr310027 : PrimeCertificate 310027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv163,pv317]) (by decide +kernel)
def pv310027 : PrimeValue := ⟨310027, pr310027⟩
private theorem pr310049 : PrimeCertificate 310049 :=
  certifyPrime (q := pv3) (ls := [pv2,pv9689]) (by decide +kernel)
def pv310049 : PrimeValue := ⟨310049, pr310049⟩
private theorem pr310091 : PrimeCertificate 310091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv2819]) (by decide +kernel)
def pv310091 : PrimeValue := ⟨310091, pr310091⟩
private theorem pr310117 : PrimeCertificate 310117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv601]) (by decide +kernel)
def pv310117 : PrimeValue := ⟨310117, pr310117⟩
private theorem pr310127 : PrimeCertificate 310127 :=
  certifyPrime (q := pv5) (ls := [pv2,pv29,pv5347]) (by decide +kernel)
def pv310127 : PrimeValue := ⟨310127, pr310127⟩
private theorem pr310129 : PrimeCertificate 310129 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv13,pv71]) (by decide +kernel)
def pv310129 : PrimeValue := ⟨310129, pr310129⟩
private theorem pr310181 : PrimeCertificate 310181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv1193]) (by decide +kernel)
def pv310181 : PrimeValue := ⟨310181, pr310181⟩
private theorem pr310187 : PrimeCertificate 310187 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv5003]) (by decide +kernel)
def pv310187 : PrimeValue := ⟨310187, pr310187⟩
private theorem pr310223 : PrimeCertificate 310223 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv59,pv239]) (by decide +kernel)
def pv310223 : PrimeValue := ⟨310223, pr310223⟩
private theorem pr310229 : PrimeCertificate 310229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv77557]) (by decide +kernel)
def pv310229 : PrimeValue := ⟨310229, pr310229⟩
private theorem pr310231 : PrimeCertificate 310231 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv383]) (by decide +kernel)
def pv310231 : PrimeValue := ⟨310231, pr310231⟩
private theorem pr310237 : PrimeCertificate 310237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv103,pv251]) (by decide +kernel)
def pv310237 : PrimeValue := ⟨310237, pr310237⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
