/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table086
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table086.pv303907
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table013
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table020
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table021
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table053
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table054

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr303907 : Nat.Prime 303907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv50651]) (by decide +kernel)
def pv303907 : PrimeValue := ⟨303907, pr303907⟩
private theorem pr303959 : Nat.Prime 303959 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv379,pv401]) (by decide +kernel)
def pv303959 : PrimeValue := ⟨303959, pr303959⟩
private theorem pr303983 : Nat.Prime 303983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv21713]) (by decide +kernel)
def pv303983 : PrimeValue := ⟨303983, pr303983⟩
private theorem pr304009 : Nat.Prime 304009 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv53,pv239]) (by decide +kernel)
def pv304009 : PrimeValue := ⟨304009, pr304009⟩
private theorem pr304039 : Nat.Prime 304039 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv19,pv127]) (by decide +kernel)
def pv304039 : PrimeValue := ⟨304039, pr304039⟩
private theorem pr304049 : Nat.Prime 304049 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv613]) (by decide +kernel)
def pv304049 : PrimeValue := ⟨304049, pr304049⟩
private theorem pr304063 : Nat.Prime 304063 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv17,pv271]) (by decide +kernel)
def pv304063 : PrimeValue := ⟨304063, pr304063⟩
private theorem pr304067 : Nat.Prime 304067 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv37,pv587]) (by decide +kernel)
def pv304067 : PrimeValue := ⟨304067, pr304067⟩
private theorem pr304069 : Nat.Prime 304069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv25339]) (by decide +kernel)
def pv304069 : PrimeValue := ⟨304069, pr304069⟩
private theorem pr304081 : Nat.Prime 304081 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv181]) (by decide +kernel)
def pv304081 : PrimeValue := ⟨304081, pr304081⟩
private theorem pr304151 : Nat.Prime 304151 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv11,pv79]) (by decide +kernel)
def pv304151 : PrimeValue := ⟨304151, pr304151⟩
private theorem pr304153 : Nat.Prime 304153 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv19,pv23,pv29]) (by decide +kernel)
def pv304153 : PrimeValue := ⟨304153, pr304153⟩
private theorem pr304169 : Nat.Prime 304169 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv193,pv197]) (by decide +kernel)
def pv304169 : PrimeValue := ⟨304169, pr304169⟩
private theorem pr304211 : Nat.Prime 304211 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv29,pv1049]) (by decide +kernel)
def pv304211 : PrimeValue := ⟨304211, pr304211⟩
private theorem pr304259 : Nat.Prime 304259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv149,pv1021]) (by decide +kernel)
def pv304259 : PrimeValue := ⟨304259, pr304259⟩
private theorem pr304303 : Nat.Prime 304303 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv41,pv1237]) (by decide +kernel)
def pv304303 : PrimeValue := ⟨304303, pr304303⟩
private theorem pr304373 : Nat.Prime 304373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv1619]) (by decide +kernel)
def pv304373 : PrimeValue := ⟨304373, pr304373⟩
private theorem pr304417 : Nat.Prime 304417 :=
  checkPrime_prime (q := pv43) (ls := [pv2,pv3,pv7,pv151]) (by decide +kernel)
def pv304417 : PrimeValue := ⟨304417, pr304417⟩
private theorem pr304457 : Nat.Prime 304457 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv2003]) (by decide +kernel)
def pv304457 : PrimeValue := ⟨304457, pr304457⟩
private theorem pr304477 : Nat.Prime 304477 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv25373]) (by decide +kernel)
def pv304477 : PrimeValue := ⟨304477, pr304477⟩
private theorem pr304481 : Nat.Prime 304481 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv173]) (by decide +kernel)
def pv304481 : PrimeValue := ⟨304481, pr304481⟩
private theorem pr304489 : Nat.Prime 304489 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv4229]) (by decide +kernel)
def pv304489 : PrimeValue := ⟨304489, pr304489⟩
private theorem pr304511 : Nat.Prime 304511 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv37,pv823]) (by decide +kernel)
def pv304511 : PrimeValue := ⟨304511, pr304511⟩
private theorem pr304517 : Nat.Prime 304517 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv76129]) (by decide +kernel)
def pv304517 : PrimeValue := ⟨304517, pr304517⟩
private theorem pr304523 : Nat.Prime 304523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv107,pv1423]) (by decide +kernel)
def pv304523 : PrimeValue := ⟨304523, pr304523⟩
private theorem pr304553 : Nat.Prime 304553 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv38069]) (by decide +kernel)
def pv304553 : PrimeValue := ⟨304553, pr304553⟩
private theorem pr304561 : Nat.Prime 304561 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv47]) (by decide +kernel)
def pv304561 : PrimeValue := ⟨304561, pr304561⟩
private theorem pr304597 : Nat.Prime 304597 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv8461]) (by decide +kernel)
def pv304597 : PrimeValue := ⟨304597, pr304597⟩
private theorem pr304631 : Nat.Prime 304631 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv41,pv743]) (by decide +kernel)
def pv304631 : PrimeValue := ⟨304631, pr304631⟩
private theorem pr304663 : Nat.Prime 304663 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv50777]) (by decide +kernel)
def pv304663 : PrimeValue := ⟨304663, pr304663⟩
private theorem pr304687 : Nat.Prime 304687 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv16927]) (by decide +kernel)
def pv304687 : PrimeValue := ⟨304687, pr304687⟩
private theorem pr304751 : Nat.Prime 304751 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv23,pv53]) (by decide +kernel)
def pv304751 : PrimeValue := ⟨304751, pr304751⟩
private theorem pr304757 : Nat.Prime 304757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv1249]) (by decide +kernel)
def pv304757 : PrimeValue := ⟨304757, pr304757⟩
private theorem pr304763 : Nat.Prime 304763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv152381]) (by decide +kernel)
def pv304763 : PrimeValue := ⟨304763, pr304763⟩
private theorem pr304771 : Nat.Prime 304771 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv10159]) (by decide +kernel)
def pv304771 : PrimeValue := ⟨304771, pr304771⟩
private theorem pr304867 : Nat.Prime 304867 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv16937]) (by decide +kernel)
def pv304867 : PrimeValue := ⟨304867, pr304867⟩
private theorem pr304883 : Nat.Prime 304883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv152441]) (by decide +kernel)
def pv304883 : PrimeValue := ⟨304883, pr304883⟩
private theorem pr304897 : Nat.Prime 304897 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv397]) (by decide +kernel)
def pv304897 : PrimeValue := ⟨304897, pr304897⟩
private theorem pr304901 : Nat.Prime 304901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv3049]) (by decide +kernel)
def pv304901 : PrimeValue := ⟨304901, pr304901⟩
private theorem pr304903 : Nat.Prime 304903 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv1303]) (by decide +kernel)
def pv304903 : PrimeValue := ⟨304903, pr304903⟩
private theorem pr304907 : Nat.Prime 304907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv29,pv751]) (by decide +kernel)
def pv304907 : PrimeValue := ⟨304907, pr304907⟩
private theorem pr304933 : Nat.Prime 304933 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv25411]) (by decide +kernel)
def pv304933 : PrimeValue := ⟨304933, pr304933⟩
private theorem pr304937 : Nat.Prime 304937 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv47,pv811]) (by decide +kernel)
def pv304937 : PrimeValue := ⟨304937, pr304937⟩
private theorem pr304943 : Nat.Prime 304943 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv83,pv167]) (by decide +kernel)
def pv304943 : PrimeValue := ⟨304943, pr304943⟩
private theorem pr304961 : Nat.Prime 304961 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv953]) (by decide +kernel)
def pv304961 : PrimeValue := ⟨304961, pr304961⟩
private theorem pr305093 : Nat.Prime 305093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv89,pv857]) (by decide +kernel)
def pv305093 : PrimeValue := ⟨305093, pr305093⟩
private theorem pr305101 : Nat.Prime 305101 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv113]) (by decide +kernel)
def pv305101 : PrimeValue := ⟨305101, pr305101⟩
private theorem pr305143 : Nat.Prime 305143 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv50857]) (by decide +kernel)
def pv305143 : PrimeValue := ⟨305143, pr305143⟩
private theorem pr305219 : Nat.Prime 305219 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv47,pv191]) (by decide +kernel)
def pv305219 : PrimeValue := ⟨305219, pr305219⟩
private theorem pr305231 : Nat.Prime 305231 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv131,pv233]) (by decide +kernel)
def pv305231 : PrimeValue := ⟨305231, pr305231⟩
private theorem pr305297 : Nat.Prime 305297 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19081]) (by decide +kernel)
def pv305297 : PrimeValue := ⟨305297, pr305297⟩
private theorem pr305329 : Nat.Prime 305329 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv6361]) (by decide +kernel)
def pv305329 : PrimeValue := ⟨305329, pr305329⟩
private theorem pr305351 : Nat.Prime 305351 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv31,pv197]) (by decide +kernel)
def pv305351 : PrimeValue := ⟨305351, pr305351⟩
private theorem pr305353 : Nat.Prime 305353 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv4241]) (by decide +kernel)
def pv305353 : PrimeValue := ⟨305353, pr305353⟩
private theorem pr305363 : Nat.Prime 305363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv152681]) (by decide +kernel)
def pv305363 : PrimeValue := ⟨305363, pr305363⟩
private theorem pr305369 : Nat.Prime 305369 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv7,pv19,pv41]) (by decide +kernel)
def pv305369 : PrimeValue := ⟨305369, pr305369⟩
private theorem pr305401 : Nat.Prime 305401 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv509]) (by decide +kernel)
def pv305401 : PrimeValue := ⟨305401, pr305401⟩
private theorem pr305411 : Nat.Prime 305411 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv7,pv4363]) (by decide +kernel)
def pv305411 : PrimeValue := ⟨305411, pr305411⟩
private theorem pr305413 : Nat.Prime 305413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv821]) (by decide +kernel)
def pv305413 : PrimeValue := ⟨305413, pr305413⟩
private theorem pr305423 : Nat.Prime 305423 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv17,pv691]) (by decide +kernel)
def pv305423 : PrimeValue := ⟨305423, pr305423⟩
private theorem pr305477 : Nat.Prime 305477 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv76369]) (by decide +kernel)
def pv305477 : PrimeValue := ⟨305477, pr305477⟩
private theorem pr305479 : Nat.Prime 305479 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5657]) (by decide +kernel)
def pv305479 : PrimeValue := ⟨305479, pr305479⟩
private theorem pr305497 : Nat.Prime 305497 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv4243]) (by decide +kernel)
def pv305497 : PrimeValue := ⟨305497, pr305497⟩
private theorem pr305521 : Nat.Prime 305521 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv19,pv67]) (by decide +kernel)
def pv305521 : PrimeValue := ⟨305521, pr305521⟩
private theorem pr305533 : Nat.Prime 305533 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv23,pv41]) (by decide +kernel)
def pv305533 : PrimeValue := ⟨305533, pr305533⟩
private theorem pr305563 : Nat.Prime 305563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv127,pv401]) (by decide +kernel)
def pv305563 : PrimeValue := ⟨305563, pr305563⟩
private theorem pr305581 : Nat.Prime 305581 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv463]) (by decide +kernel)
def pv305581 : PrimeValue := ⟨305581, pr305581⟩
private theorem pr305593 : Nat.Prime 305593 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv17,pv107]) (by decide +kernel)
def pv305593 : PrimeValue := ⟨305593, pr305593⟩
private theorem pr305603 : Nat.Prime 305603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv29,pv479]) (by decide +kernel)
def pv305603 : PrimeValue := ⟨305603, pr305603⟩
private theorem pr305611 : Nat.Prime 305611 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv61,pv167]) (by decide +kernel)
def pv305611 : PrimeValue := ⟨305611, pr305611⟩
private theorem pr305639 : Nat.Prime 305639 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv152819]) (by decide +kernel)
def pv305639 : PrimeValue := ⟨305639, pr305639⟩
private theorem pr305717 : Nat.Prime 305717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv3323]) (by decide +kernel)
def pv305717 : PrimeValue := ⟨305717, pr305717⟩
private theorem pr305741 : Nat.Prime 305741 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv15287]) (by decide +kernel)
def pv305741 : PrimeValue := ⟨305741, pr305741⟩
private theorem pr305761 : Nat.Prime 305761 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv7,pv13]) (by decide +kernel)
def pv305761 : PrimeValue := ⟨305761, pr305761⟩
private theorem pr305771 : Nat.Prime 305771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv30577]) (by decide +kernel)
def pv305771 : PrimeValue := ⟨305771, pr305771⟩
private theorem pr305839 : Nat.Prime 305839 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv1307]) (by decide +kernel)
def pv305839 : PrimeValue := ⟨305839, pr305839⟩
private theorem pr305861 : Nat.Prime 305861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv41,pv373]) (by decide +kernel)
def pv305861 : PrimeValue := ⟨305861, pr305861⟩
private theorem pr305999 : Nat.Prime 305999 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv11,pv1987]) (by decide +kernel)
def pv305999 : PrimeValue := ⟨305999, pr305999⟩
private theorem pr306011 : Nat.Prime 306011 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv71,pv431]) (by decide +kernel)
def pv306011 : PrimeValue := ⟨306011, pr306011⟩
private theorem pr306041 : Nat.Prime 306041 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv7,pv1093]) (by decide +kernel)
def pv306041 : PrimeValue := ⟨306041, pr306041⟩
private theorem pr306121 : Nat.Prime 306121 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv2551]) (by decide +kernel)
def pv306121 : PrimeValue := ⟨306121, pr306121⟩
private theorem pr306133 : Nat.Prime 306133 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv97,pv263]) (by decide +kernel)
def pv306133 : PrimeValue := ⟨306133, pr306133⟩
private theorem pr306139 : Nat.Prime 306139 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv37,pv197]) (by decide +kernel)
def pv306139 : PrimeValue := ⟨306139, pr306139⟩
private theorem pr306157 : Nat.Prime 306157 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv31,pv823]) (by decide +kernel)
def pv306157 : PrimeValue := ⟨306157, pr306157⟩
private theorem pr306169 : Nat.Prime 306169 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv12757]) (by decide +kernel)
def pv306169 : PrimeValue := ⟨306169, pr306169⟩
private theorem pr306191 : Nat.Prime 306191 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv67,pv457]) (by decide +kernel)
def pv306191 : PrimeValue := ⟨306191, pr306191⟩
private theorem pr306193 : Nat.Prime 306193 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv6379]) (by decide +kernel)
def pv306193 : PrimeValue := ⟨306193, pr306193⟩
private theorem pr306239 : Nat.Prime 306239 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv17,pv9007]) (by decide +kernel)
def pv306239 : PrimeValue := ⟨306239, pr306239⟩
private theorem pr306253 : Nat.Prime 306253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv47,pv181]) (by decide +kernel)
def pv306253 : PrimeValue := ⟨306253, pr306253⟩
private theorem pr306329 : Nat.Prime 306329 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv59]) (by decide +kernel)
def pv306329 : PrimeValue := ⟨306329, pr306329⟩
private theorem pr306349 : Nat.Prime 306349 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv521]) (by decide +kernel)
def pv306349 : PrimeValue := ⟨306349, pr306349⟩
private theorem pr306359 : Nat.Prime 306359 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv13,pv11783]) (by decide +kernel)
def pv306359 : PrimeValue := ⟨306359, pr306359⟩
private theorem pr306367 : Nat.Prime 306367 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv51061]) (by decide +kernel)
def pv306367 : PrimeValue := ⟨306367, pr306367⟩
private theorem pr306377 : Nat.Prime 306377 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv5471]) (by decide +kernel)
def pv306377 : PrimeValue := ⟨306377, pr306377⟩
private theorem pr306407 : Nat.Prime 306407 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv23,pv6661]) (by decide +kernel)
def pv306407 : PrimeValue := ⟨306407, pr306407⟩
private theorem pr306421 : Nat.Prime 306421 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv5107]) (by decide +kernel)
def pv306421 : PrimeValue := ⟨306421, pr306421⟩
private theorem pr306431 : Nat.Prime 306431 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv30643]) (by decide +kernel)
def pv306431 : PrimeValue := ⟨306431, pr306431⟩
private theorem pr306457 : Nat.Prime 306457 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv113]) (by decide +kernel)
def pv306457 : PrimeValue := ⟨306457, pr306457⟩
private theorem pr306463 : Nat.Prime 306463 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv13,pv3929]) (by decide +kernel)
def pv306463 : PrimeValue := ⟨306463, pr306463⟩
private theorem pr306473 : Nat.Prime 306473 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv1321]) (by decide +kernel)
def pv306473 : PrimeValue := ⟨306473, pr306473⟩
private theorem pr306503 : Nat.Prime 306503 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv21893]) (by decide +kernel)
def pv306503 : PrimeValue := ⟨306503, pr306503⟩
private theorem pr306529 : Nat.Prime 306529 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv31,pv103]) (by decide +kernel)
def pv306529 : PrimeValue := ⟨306529, pr306529⟩
private theorem pr306541 : Nat.Prime 306541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv131]) (by decide +kernel)
def pv306541 : PrimeValue := ⟨306541, pr306541⟩
private theorem pr306577 : Nat.Prime 306577 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2129]) (by decide +kernel)
def pv306577 : PrimeValue := ⟨306577, pr306577⟩
private theorem pr306653 : Nat.Prime 306653 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv2473]) (by decide +kernel)
def pv306653 : PrimeValue := ⟨306653, pr306653⟩
private theorem pr306661 : Nat.Prime 306661 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv269]) (by decide +kernel)
def pv306661 : PrimeValue := ⟨306661, pr306661⟩
private theorem pr306703 : Nat.Prime 306703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv1549]) (by decide +kernel)
def pv306703 : PrimeValue := ⟨306703, pr306703⟩
private theorem pr306707 : Nat.Prime 306707 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv153353]) (by decide +kernel)
def pv306707 : PrimeValue := ⟨306707, pr306707⟩
private theorem pr306739 : Nat.Prime 306739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17041]) (by decide +kernel)
def pv306739 : PrimeValue := ⟨306739, pr306739⟩
private theorem pr306749 : Nat.Prime 306749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv17,pv347]) (by decide +kernel)
def pv306749 : PrimeValue := ⟨306749, pr306749⟩
private theorem pr306763 : Nat.Prime 306763 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv29,pv41,pv43]) (by decide +kernel)
def pv306763 : PrimeValue := ⟨306763, pr306763⟩
private theorem pr306871 : Nat.Prime 306871 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv53,pv193]) (by decide +kernel)
def pv306871 : PrimeValue := ⟨306871, pr306871⟩
private theorem pr306883 : Nat.Prime 306883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5683]) (by decide +kernel)
def pv306883 : PrimeValue := ⟨306883, pr306883⟩
private theorem pr306913 : Nat.Prime 306913 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23,pv139]) (by decide +kernel)
def pv306913 : PrimeValue := ⟨306913, pr306913⟩
private theorem pr306941 : Nat.Prime 306941 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv103,pv149]) (by decide +kernel)
def pv306941 : PrimeValue := ⟨306941, pr306941⟩
private theorem pr306947 : Nat.Prime 306947 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv167,pv919]) (by decide +kernel)
def pv306947 : PrimeValue := ⟨306947, pr306947⟩
private theorem pr306949 : Nat.Prime 306949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv25579]) (by decide +kernel)
def pv306949 : PrimeValue := ⟨306949, pr306949⟩
private theorem pr306991 : Nat.Prime 306991 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv379]) (by decide +kernel)
def pv306991 : PrimeValue := ⟨306991, pr306991⟩
private theorem pr307009 : Nat.Prime 307009 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv41]) (by decide +kernel)
def pv307009 : PrimeValue := ⟨307009, pr307009⟩
private theorem pr307031 : Nat.Prime 307031 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv30703]) (by decide +kernel)
def pv307031 : PrimeValue := ⟨307031, pr307031⟩
private theorem pr307033 : Nat.Prime 307033 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv1163]) (by decide +kernel)
def pv307033 : PrimeValue := ⟨307033, pr307033⟩
private theorem pr307091 : Nat.Prime 307091 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv41,pv107]) (by decide +kernel)
def pv307091 : PrimeValue := ⟨307091, pr307091⟩
private theorem pr307093 : Nat.Prime 307093 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv157,pv163]) (by decide +kernel)
def pv307093 : PrimeValue := ⟨307093, pr307093⟩
private theorem pr307103 : Nat.Prime 307103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv97,pv1583]) (by decide +kernel)
def pv307103 : PrimeValue := ⟨307103, pr307103⟩
private theorem pr307121 : Nat.Prime 307121 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv349]) (by decide +kernel)
def pv307121 : PrimeValue := ⟨307121, pr307121⟩
private theorem pr307147 : Nat.Prime 307147 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv71,pv103]) (by decide +kernel)
def pv307147 : PrimeValue := ⟨307147, pr307147⟩
private theorem pr307169 : Nat.Prime 307169 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv331]) (by decide +kernel)
def pv307169 : PrimeValue := ⟨307169, pr307169⟩
private theorem pr307171 : Nat.Prime 307171 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv3413]) (by decide +kernel)
def pv307171 : PrimeValue := ⟨307171, pr307171⟩
private theorem pr307201 : Nat.Prime 307201 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv307201 : PrimeValue := ⟨307201, pr307201⟩
private theorem pr307243 : Nat.Prime 307243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv101]) (by decide +kernel)
def pv307243 : PrimeValue := ⟨307243, pr307243⟩
private theorem pr307261 : Nat.Prime 307261 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv569]) (by decide +kernel)
def pv307261 : PrimeValue := ⟨307261, pr307261⟩
private theorem pr307273 : Nat.Prime 307273 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv31,pv59]) (by decide +kernel)
def pv307273 : PrimeValue := ⟨307273, pr307273⟩
private theorem pr307301 : Nat.Prime 307301 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv439]) (by decide +kernel)
def pv307301 : PrimeValue := ⟨307301, pr307301⟩
private theorem pr307381 : Nat.Prime 307381 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv47,pv109]) (by decide +kernel)
def pv307381 : PrimeValue := ⟨307381, pr307381⟩
private theorem pr307397 : Nat.Prime 307397 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv37,pv67]) (by decide +kernel)
def pv307397 : PrimeValue := ⟨307397, pr307397⟩
private theorem pr307399 : Nat.Prime 307399 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv563]) (by decide +kernel)
def pv307399 : PrimeValue := ⟨307399, pr307399⟩
private theorem pr307409 : Nat.Prime 307409 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19213]) (by decide +kernel)
def pv307409 : PrimeValue := ⟨307409, pr307409⟩
private theorem pr307451 : Nat.Prime 307451 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv13,pv43]) (by decide +kernel)
def pv307451 : PrimeValue := ⟨307451, pr307451⟩
private theorem pr307471 : Nat.Prime 307471 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv37,pv277]) (by decide +kernel)
def pv307471 : PrimeValue := ⟨307471, pr307471⟩
private theorem pr307481 : Nat.Prime 307481 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7687]) (by decide +kernel)
def pv307481 : PrimeValue := ⟨307481, pr307481⟩
private theorem pr307523 : Nat.Prime 307523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv179,pv859]) (by decide +kernel)
def pv307523 : PrimeValue := ⟨307523, pr307523⟩
private theorem pr307577 : Nat.Prime 307577 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv38447]) (by decide +kernel)
def pv307577 : PrimeValue := ⟨307577, pr307577⟩
private theorem pr307583 : Nat.Prime 307583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv31,pv41]) (by decide +kernel)
def pv307583 : PrimeValue := ⟨307583, pr307583⟩
private theorem pr307633 : Nat.Prime 307633 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv17,pv29]) (by decide +kernel)
def pv307633 : PrimeValue := ⟨307633, pr307633⟩
private theorem pr307639 : Nat.Prime 307639 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv211]) (by decide +kernel)
def pv307639 : PrimeValue := ⟨307639, pr307639⟩
private theorem pr307651 : Nat.Prime 307651 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv293]) (by decide +kernel)
def pv307651 : PrimeValue := ⟨307651, pr307651⟩
private theorem pr307669 : Nat.Prime 307669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv25639]) (by decide +kernel)
def pv307669 : PrimeValue := ⟨307669, pr307669⟩
private theorem pr307711 : Nat.Prime 307711 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv263]) (by decide +kernel)
def pv307711 : PrimeValue := ⟨307711, pr307711⟩
private theorem pr307733 : Nat.Prime 307733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv107,pv719]) (by decide +kernel)
def pv307733 : PrimeValue := ⟨307733, pr307733⟩
private theorem pr307817 : Nat.Prime 307817 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv109,pv353]) (by decide +kernel)
def pv307817 : PrimeValue := ⟨307817, pr307817⟩
private theorem pr307823 : Nat.Prime 307823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv153911]) (by decide +kernel)
def pv307823 : PrimeValue := ⟨307823, pr307823⟩
private theorem pr307843 : Nat.Prime 307843 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv51307]) (by decide +kernel)
def pv307843 : PrimeValue := ⟨307843, pr307843⟩
private theorem pr307871 : Nat.Prime 307871 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv17,pv1811]) (by decide +kernel)
def pv307871 : PrimeValue := ⟨307871, pr307871⟩
private theorem pr307873 : Nat.Prime 307873 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1069]) (by decide +kernel)
def pv307873 : PrimeValue := ⟨307873, pr307873⟩
private theorem pr307891 : Nat.Prime 307891 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv11,pv311]) (by decide +kernel)
def pv307891 : PrimeValue := ⟨307891, pr307891⟩
private theorem pr307903 : Nat.Prime 307903 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv7331]) (by decide +kernel)
def pv307903 : PrimeValue := ⟨307903, pr307903⟩
private theorem pr307939 : Nat.Prime 307939 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv3019]) (by decide +kernel)
def pv307939 : PrimeValue := ⟨307939, pr307939⟩
private theorem pr307969 : Nat.Prime 307969 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv401]) (by decide +kernel)
def pv307969 : PrimeValue := ⟨307969, pr307969⟩
private theorem pr308017 : Nat.Prime 308017 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23,pv31]) (by decide +kernel)
def pv308017 : PrimeValue := ⟨308017, pr308017⟩
private theorem pr308041 : Nat.Prime 308041 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv17,pv151]) (by decide +kernel)
def pv308041 : PrimeValue := ⟨308041, pr308041⟩
private theorem pr308051 : Nat.Prime 308051 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv61,pv101]) (by decide +kernel)
def pv308051 : PrimeValue := ⟨308051, pr308051⟩
private theorem pr308101 : Nat.Prime 308101 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv13,pv79]) (by decide +kernel)
def pv308101 : PrimeValue := ⟨308101, pr308101⟩
private theorem pr308117 : Nat.Prime 308117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv77029]) (by decide +kernel)
def pv308117 : PrimeValue := ⟨308117, pr308117⟩
private theorem pr308137 : Nat.Prime 308137 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv37,pv347]) (by decide +kernel)
def pv308137 : PrimeValue := ⟨308137, pr308137⟩
private theorem pr308141 : Nat.Prime 308141 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv31,pv71]) (by decide +kernel)
def pv308141 : PrimeValue := ⟨308141, pr308141⟩
private theorem pr308153 : Nat.Prime 308153 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv2963]) (by decide +kernel)
def pv308153 : PrimeValue := ⟨308153, pr308153⟩
private theorem pr308213 : Nat.Prime 308213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv2657]) (by decide +kernel)
def pv308213 : PrimeValue := ⟨308213, pr308213⟩
private theorem pr308219 : Nat.Prime 308219 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv8111]) (by decide +kernel)
def pv308219 : PrimeValue := ⟨308219, pr308219⟩
private theorem pr308249 : Nat.Prime 308249 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv53,pv727]) (by decide +kernel)
def pv308249 : PrimeValue := ⟨308249, pr308249⟩
private theorem pr308263 : Nat.Prime 308263 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv83,pv619]) (by decide +kernel)
def pv308263 : PrimeValue := ⟨308263, pr308263⟩
private theorem pr308293 : Nat.Prime 308293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv1117]) (by decide +kernel)
def pv308293 : PrimeValue := ⟨308293, pr308293⟩
private theorem pr308309 : Nat.Prime 308309 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv13]) (by decide +kernel)
def pv308309 : PrimeValue := ⟨308309, pr308309⟩
private theorem pr308323 : Nat.Prime 308323 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv2447]) (by decide +kernel)
def pv308323 : PrimeValue := ⟨308323, pr308323⟩
private theorem pr308359 : Nat.Prime 308359 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv37,pv463]) (by decide +kernel)
def pv308359 : PrimeValue := ⟨308359, pr308359⟩
private theorem pr308437 : Nat.Prime 308437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv25703]) (by decide +kernel)
def pv308437 : PrimeValue := ⟨308437, pr308437⟩
private theorem pr308467 : Nat.Prime 308467 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17137]) (by decide +kernel)
def pv308467 : PrimeValue := ⟨308467, pr308467⟩
private theorem pr308491 : Nat.Prime 308491 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv7,pv13,pv113]) (by decide +kernel)
def pv308491 : PrimeValue := ⟨308491, pr308491⟩
private theorem pr308507 : Nat.Prime 308507 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv37,pv379]) (by decide +kernel)
def pv308507 : PrimeValue := ⟨308507, pr308507⟩
private theorem pr308519 : Nat.Prime 308519 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv7,pv22037]) (by decide +kernel)
def pv308519 : PrimeValue := ⟨308519, pr308519⟩
private theorem pr308521 : Nat.Prime 308521 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv857]) (by decide +kernel)
def pv308521 : PrimeValue := ⟨308521, pr308521⟩
private theorem pr308527 : Nat.Prime 308527 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv51421]) (by decide +kernel)
def pv308527 : PrimeValue := ⟨308527, pr308527⟩
private theorem pr308573 : Nat.Prime 308573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv7013]) (by decide +kernel)
def pv308573 : PrimeValue := ⟨308573, pr308573⟩
private theorem pr308587 : Nat.Prime 308587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv51431]) (by decide +kernel)
def pv308587 : PrimeValue := ⟨308587, pr308587⟩
private theorem pr308597 : Nat.Prime 308597 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv179,pv431]) (by decide +kernel)
def pv308597 : PrimeValue := ⟨308597, pr308597⟩
private theorem pr308621 : Nat.Prime 308621 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv1187]) (by decide +kernel)
def pv308621 : PrimeValue := ⟨308621, pr308621⟩
private theorem pr308663 : Nat.Prime 308663 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv157,pv983]) (by decide +kernel)
def pv308663 : PrimeValue := ⟨308663, pr308663⟩
private theorem pr308681 : Nat.Prime 308681 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7717]) (by decide +kernel)
def pv308681 : PrimeValue := ⟨308681, pr308681⟩
private theorem pr308713 : Nat.Prime 308713 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv19,pv677]) (by decide +kernel)
def pv308713 : PrimeValue := ⟨308713, pr308713⟩
private theorem pr308723 : Nat.Prime 308723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv163,pv947]) (by decide +kernel)
def pv308723 : PrimeValue := ⟨308723, pr308723⟩
private theorem pr308773 : Nat.Prime 308773 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv953]) (by decide +kernel)
def pv308773 : PrimeValue := ⟨308773, pr308773⟩
private theorem pr308809 : Nat.Prime 308809 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv4289]) (by decide +kernel)
def pv308809 : PrimeValue := ⟨308809, pr308809⟩
private theorem pr308827 : Nat.Prime 308827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv19,pv43]) (by decide +kernel)
def pv308827 : PrimeValue := ⟨308827, pr308827⟩
private theorem pr308849 : Nat.Prime 308849 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv97,pv199]) (by decide +kernel)
def pv308849 : PrimeValue := ⟨308849, pr308849⟩
private theorem pr308851 : Nat.Prime 308851 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv29,pv71]) (by decide +kernel)
def pv308851 : PrimeValue := ⟨308851, pr308851⟩
private theorem pr308923 : Nat.Prime 308923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv51487]) (by decide +kernel)
def pv308923 : PrimeValue := ⟨308923, pr308923⟩
private theorem pr308927 : Nat.Prime 308927 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv83,pv1861]) (by decide +kernel)
def pv308927 : PrimeValue := ⟨308927, pr308927⟩
private theorem pr308939 : Nat.Prime 308939 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv22067]) (by decide +kernel)
def pv308939 : PrimeValue := ⟨308939, pr308939⟩
private theorem pr308999 : Nat.Prime 308999 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv43,pv3593]) (by decide +kernel)
def pv308999 : PrimeValue := ⟨308999, pr308999⟩
private theorem pr309007 : Nat.Prime 309007 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17167]) (by decide +kernel)
def pv309007 : PrimeValue := ⟨309007, pr309007⟩
private theorem pr309011 : Nat.Prime 309011 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv2377]) (by decide +kernel)
def pv309011 : PrimeValue := ⟨309011, pr309011⟩
private theorem pr309019 : Nat.Prime 309019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv51503]) (by decide +kernel)
def pv309019 : PrimeValue := ⟨309019, pr309019⟩
private theorem pr309031 : Nat.Prime 309031 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv10301]) (by decide +kernel)
def pv309031 : PrimeValue := ⟨309031, pr309031⟩
private theorem pr309037 : Nat.Prime 309037 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv283]) (by decide +kernel)
def pv309037 : PrimeValue := ⟨309037, pr309037⟩
private theorem pr309059 : Nat.Prime 309059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv3769]) (by decide +kernel)
def pv309059 : PrimeValue := ⟨309059, pr309059⟩
private theorem pr309079 : Nat.Prime 309079 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv7,pv11,pv223]) (by decide +kernel)
def pv309079 : PrimeValue := ⟨309079, pr309079⟩
private theorem pr309107 : Nat.Prime 309107 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv22079]) (by decide +kernel)
def pv309107 : PrimeValue := ⟨309107, pr309107⟩
private theorem pr309131 : Nat.Prime 309131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv19,pv1627]) (by decide +kernel)
def pv309131 : PrimeValue := ⟨309131, pr309131⟩
private theorem pr309157 : Nat.Prime 309157 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv25763]) (by decide +kernel)
def pv309157 : PrimeValue := ⟨309157, pr309157⟩
private theorem pr309167 : Nat.Prime 309167 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv13,pv23,pv47]) (by decide +kernel)
def pv309167 : PrimeValue := ⟨309167, pr309167⟩
private theorem pr309173 : Nat.Prime 309173 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv2089]) (by decide +kernel)
def pv309173 : PrimeValue := ⟨309173, pr309173⟩
private theorem pr309259 : Nat.Prime 309259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv83]) (by decide +kernel)
def pv309259 : PrimeValue := ⟨309259, pr309259⟩
private theorem pr309271 : Nat.Prime 309271 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv61]) (by decide +kernel)
def pv309271 : PrimeValue := ⟨309271, pr309271⟩
private theorem pr309289 : Nat.Prime 309289 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv3,pv7,pv263]) (by decide +kernel)
def pv309289 : PrimeValue := ⟨309289, pr309289⟩
private theorem pr309293 : Nat.Prime 309293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv77323]) (by decide +kernel)
def pv309293 : PrimeValue := ⟨309293, pr309293⟩
private theorem pr309311 : Nat.Prime 309311 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv30931]) (by decide +kernel)
def pv309311 : PrimeValue := ⟨309311, pr309311⟩
private theorem pr309313 : Nat.Prime 309313 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv179]) (by decide +kernel)
def pv309313 : PrimeValue := ⟨309313, pr309313⟩
private theorem pr309359 : Nat.Prime 309359 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv7,pv19,pv1163]) (by decide +kernel)
def pv309359 : PrimeValue := ⟨309359, pr309359⟩
private theorem pr309371 : Nat.Prime 309371 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv30937]) (by decide +kernel)
def pv309371 : PrimeValue := ⟨309371, pr309371⟩
private theorem pr309391 : Nat.Prime 309391 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv10313]) (by decide +kernel)
def pv309391 : PrimeValue := ⟨309391, pr309391⟩
private theorem pr309403 : Nat.Prime 309403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17189]) (by decide +kernel)
def pv309403 : PrimeValue := ⟨309403, pr309403⟩
private theorem pr309433 : Nat.Prime 309433 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv12893]) (by decide +kernel)
def pv309433 : PrimeValue := ⟨309433, pr309433⟩
private theorem pr309437 : Nat.Prime 309437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv77359]) (by decide +kernel)
def pv309437 : PrimeValue := ⟨309437, pr309437⟩
private theorem pr309457 : Nat.Prime 309457 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv307]) (by decide +kernel)
def pv309457 : PrimeValue := ⟨309457, pr309457⟩
private theorem pr309461 : Nat.Prime 309461 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv15473]) (by decide +kernel)
def pv309461 : PrimeValue := ⟨309461, pr309461⟩
private theorem pr309469 : Nat.Prime 309469 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv17,pv37,pv41]) (by decide +kernel)
def pv309469 : PrimeValue := ⟨309469, pr309469⟩
private theorem pr309503 : Nat.Prime 309503 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv9103]) (by decide +kernel)
def pv309503 : PrimeValue := ⟨309503, pr309503⟩
private theorem pr309523 : Nat.Prime 309523 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv79,pv653]) (by decide +kernel)
def pv309523 : PrimeValue := ⟨309523, pr309523⟩
private theorem pr309539 : Nat.Prime 309539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv154769]) (by decide +kernel)
def pv309539 : PrimeValue := ⟨309539, pr309539⟩
private theorem pr309583 : Nat.Prime 309583 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv13]) (by decide +kernel)
def pv309583 : PrimeValue := ⟨309583, pr309583⟩
private theorem pr309623 : Nat.Prime 309623 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv149,pv1039]) (by decide +kernel)
def pv309623 : PrimeValue := ⟨309623, pr309623⟩
private theorem pr309713 : Nat.Prime 309713 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv1489]) (by decide +kernel)
def pv309713 : PrimeValue := ⟨309713, pr309713⟩
private theorem pr309811 : Nat.Prime 309811 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv23,pv449]) (by decide +kernel)
def pv309811 : PrimeValue := ⟨309811, pr309811⟩
private theorem pr309851 : Nat.Prime 309851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv6197]) (by decide +kernel)
def pv309851 : PrimeValue := ⟨309851, pr309851⟩
private theorem pr309853 : Nat.Prime 309853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv151]) (by decide +kernel)
def pv309853 : PrimeValue := ⟨309853, pr309853⟩
private theorem pr309877 : Nat.Prime 309877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv31]) (by decide +kernel)
def pv309877 : PrimeValue := ⟨309877, pr309877⟩
private theorem pr309977 : Nat.Prime 309977 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv38747]) (by decide +kernel)
def pv309977 : PrimeValue := ⟨309977, pr309977⟩
private theorem pr309989 : Nat.Prime 309989 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11071]) (by decide +kernel)
def pv309989 : PrimeValue := ⟨309989, pr309989⟩
private theorem pr310021 : Nat.Prime 310021 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv5167]) (by decide +kernel)
def pv310021 : PrimeValue := ⟨310021, pr310021⟩
private theorem pr310027 : Nat.Prime 310027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv163,pv317]) (by decide +kernel)
def pv310027 : PrimeValue := ⟨310027, pr310027⟩
private theorem pr310049 : Nat.Prime 310049 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv9689]) (by decide +kernel)
def pv310049 : PrimeValue := ⟨310049, pr310049⟩
private theorem pr310091 : Nat.Prime 310091 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv2819]) (by decide +kernel)
def pv310091 : PrimeValue := ⟨310091, pr310091⟩
private theorem pr310117 : Nat.Prime 310117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv43,pv601]) (by decide +kernel)
def pv310117 : PrimeValue := ⟨310117, pr310117⟩
private theorem pr310127 : Nat.Prime 310127 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv29,pv5347]) (by decide +kernel)
def pv310127 : PrimeValue := ⟨310127, pr310127⟩
private theorem pr310129 : Nat.Prime 310129 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv13,pv71]) (by decide +kernel)
def pv310129 : PrimeValue := ⟨310129, pr310129⟩
private theorem pr310181 : Nat.Prime 310181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv1193]) (by decide +kernel)
def pv310181 : PrimeValue := ⟨310181, pr310181⟩
private theorem pr310187 : Nat.Prime 310187 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv5003]) (by decide +kernel)
def pv310187 : PrimeValue := ⟨310187, pr310187⟩
private theorem pr310223 : Nat.Prime 310223 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv59,pv239]) (by decide +kernel)
def pv310223 : PrimeValue := ⟨310223, pr310223⟩
private theorem pr310229 : Nat.Prime 310229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv77557]) (by decide +kernel)
def pv310229 : PrimeValue := ⟨310229, pr310229⟩
private theorem pr310231 : Nat.Prime 310231 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv383]) (by decide +kernel)
def pv310231 : PrimeValue := ⟨310231, pr310231⟩
private theorem pr310237 : Nat.Prime 310237 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv103,pv251]) (by decide +kernel)
def pv310237 : PrimeValue := ⟨310237, pr310237⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
