/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table034
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table034.pv88259
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table006
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table007
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table018

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr88259 : PrimeCertificate 88259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv44129]) (by decide +kernel)
def pv88259 : PrimeValue := ⟨88259, pr88259⟩
private theorem pr88261 : PrimeCertificate 88261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1471]) (by decide +kernel)
def pv88261 : PrimeValue := ⟨88261, pr88261⟩
private theorem pr88289 : PrimeCertificate 88289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv89]) (by decide +kernel)
def pv88289 : PrimeValue := ⟨88289, pr88289⟩
private theorem pr88301 : PrimeCertificate 88301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv883]) (by decide +kernel)
def pv88301 : PrimeValue := ⟨88301, pr88301⟩
private theorem pr88321 : PrimeCertificate 88321 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv5,pv23]) (by decide +kernel)
def pv88321 : PrimeValue := ⟨88321, pr88321⟩
private theorem pr88327 : PrimeCertificate 88327 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv701]) (by decide +kernel)
def pv88327 : PrimeValue := ⟨88327, pr88327⟩
private theorem pr88339 : PrimeCertificate 88339 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv14723]) (by decide +kernel)
def pv88339 : PrimeValue := ⟨88339, pr88339⟩
private theorem pr88379 : PrimeCertificate 88379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv44189]) (by decide +kernel)
def pv88379 : PrimeValue := ⟨88379, pr88379⟩
private theorem pr88397 : PrimeCertificate 88397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv41]) (by decide +kernel)
def pv88397 : PrimeValue := ⟨88397, pr88397⟩
private theorem pr88411 : PrimeCertificate 88411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv421]) (by decide +kernel)
def pv88411 : PrimeValue := ⟨88411, pr88411⟩
private theorem pr88423 : PrimeCertificate 88423 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv14737]) (by decide +kernel)
def pv88423 : PrimeValue := ⟨88423, pr88423⟩
private theorem pr88427 : PrimeCertificate 88427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv19,pv179]) (by decide +kernel)
def pv88427 : PrimeValue := ⟨88427, pr88427⟩
private theorem pr88463 : PrimeCertificate 88463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv4021]) (by decide +kernel)
def pv88463 : PrimeValue := ⟨88463, pr88463⟩
private theorem pr88469 : PrimeCertificate 88469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv1301]) (by decide +kernel)
def pv88469 : PrimeValue := ⟨88469, pr88469⟩
private theorem pr88471 : PrimeCertificate 88471 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv983]) (by decide +kernel)
def pv88471 : PrimeValue := ⟨88471, pr88471⟩
private theorem pr88493 : PrimeCertificate 88493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv22123]) (by decide +kernel)
def pv88493 : PrimeValue := ⟨88493, pr88493⟩
private theorem pr88499 : PrimeCertificate 88499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv44249]) (by decide +kernel)
def pv88499 : PrimeValue := ⟨88499, pr88499⟩
private theorem pr88513 : PrimeCertificate 88513 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv461]) (by decide +kernel)
def pv88513 : PrimeValue := ⟨88513, pr88513⟩
private theorem pr88523 : PrimeCertificate 88523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv6323]) (by decide +kernel)
def pv88523 : PrimeValue := ⟨88523, pr88523⟩
private theorem pr88547 : PrimeCertificate 88547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv44273]) (by decide +kernel)
def pv88547 : PrimeValue := ⟨88547, pr88547⟩
private theorem pr88589 : PrimeCertificate 88589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv22147]) (by decide +kernel)
def pv88589 : PrimeValue := ⟨88589, pr88589⟩
private theorem pr88591 : PrimeCertificate 88591 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv2953]) (by decide +kernel)
def pv88591 : PrimeValue := ⟨88591, pr88591⟩
private theorem pr88607 : PrimeCertificate 88607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv6329]) (by decide +kernel)
def pv88607 : PrimeValue := ⟨88607, pr88607⟩
private theorem pr88609 : PrimeCertificate 88609 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13,pv71]) (by decide +kernel)
def pv88609 : PrimeValue := ⟨88609, pr88609⟩
private theorem pr88643 : PrimeCertificate 88643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv41,pv47]) (by decide +kernel)
def pv88643 : PrimeValue := ⟨88643, pr88643⟩
private theorem pr88651 : PrimeCertificate 88651 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv197]) (by decide +kernel)
def pv88651 : PrimeValue := ⟨88651, pr88651⟩
private theorem pr88657 : PrimeCertificate 88657 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1847]) (by decide +kernel)
def pv88657 : PrimeValue := ⟨88657, pr88657⟩
private theorem pr88661 : PrimeCertificate 88661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv13,pv31]) (by decide +kernel)
def pv88661 : PrimeValue := ⟨88661, pr88661⟩
private theorem pr88667 : PrimeCertificate 88667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv1031]) (by decide +kernel)
def pv88667 : PrimeValue := ⟨88667, pr88667⟩
private theorem pr88721 : PrimeCertificate 88721 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1109]) (by decide +kernel)
def pv88721 : PrimeValue := ⟨88721, pr88721⟩
private theorem pr88729 : PrimeCertificate 88729 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv3697]) (by decide +kernel)
def pv88729 : PrimeValue := ⟨88729, pr88729⟩
private theorem pr88741 : PrimeCertificate 88741 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv29]) (by decide +kernel)
def pv88741 : PrimeValue := ⟨88741, pr88741⟩
private theorem pr88747 : PrimeCertificate 88747 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv2113]) (by decide +kernel)
def pv88747 : PrimeValue := ⟨88747, pr88747⟩
private theorem pr88771 : PrimeCertificate 88771 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv269]) (by decide +kernel)
def pv88771 : PrimeValue := ⟨88771, pr88771⟩
private theorem pr88789 : PrimeCertificate 88789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv151]) (by decide +kernel)
def pv88789 : PrimeValue := ⟨88789, pr88789⟩
private theorem pr88799 : PrimeCertificate 88799 :=
  certifyPrime (q := pv7) (ls := [pv2,pv29,pv1531]) (by decide +kernel)
def pv88799 : PrimeValue := ⟨88799, pr88799⟩
private theorem pr88801 : PrimeCertificate 88801 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv37]) (by decide +kernel)
def pv88801 : PrimeValue := ⟨88801, pr88801⟩
private theorem pr88811 : PrimeCertificate 88811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv83,pv107]) (by decide +kernel)
def pv88811 : PrimeValue := ⟨88811, pr88811⟩
private theorem pr88813 : PrimeCertificate 88813 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2467]) (by decide +kernel)
def pv88813 : PrimeValue := ⟨88813, pr88813⟩
private theorem pr88817 : PrimeCertificate 88817 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv13,pv61]) (by decide +kernel)
def pv88817 : PrimeValue := ⟨88817, pr88817⟩
private theorem pr88819 : PrimeCertificate 88819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv113,pv131]) (by decide +kernel)
def pv88819 : PrimeValue := ⟨88819, pr88819⟩
private theorem pr88843 : PrimeCertificate 88843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv17,pv67]) (by decide +kernel)
def pv88843 : PrimeValue := ⟨88843, pr88843⟩
private theorem pr88853 : PrimeCertificate 88853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv97,pv229]) (by decide +kernel)
def pv88853 : PrimeValue := ⟨88853, pr88853⟩
private theorem pr88861 : PrimeCertificate 88861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1481]) (by decide +kernel)
def pv88861 : PrimeValue := ⟨88861, pr88861⟩
private theorem pr88867 : PrimeCertificate 88867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv4937]) (by decide +kernel)
def pv88867 : PrimeValue := ⟨88867, pr88867⟩
private theorem pr88873 : PrimeCertificate 88873 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv7,pv23]) (by decide +kernel)
def pv88873 : PrimeValue := ⟨88873, pr88873⟩
private theorem pr88883 : PrimeCertificate 88883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv2339]) (by decide +kernel)
def pv88883 : PrimeValue := ⟨88883, pr88883⟩
private theorem pr88903 : PrimeCertificate 88903 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv449]) (by decide +kernel)
def pv88903 : PrimeValue := ⟨88903, pr88903⟩
private theorem pr88919 : PrimeCertificate 88919 :=
  certifyPrime (q := pv23) (ls := [pv2,pv23,pv1933]) (by decide +kernel)
def pv88919 : PrimeValue := ⟨88919, pr88919⟩
private theorem pr88937 : PrimeCertificate 88937 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11117]) (by decide +kernel)
def pv88937 : PrimeValue := ⟨88937, pr88937⟩
private theorem pr88951 : PrimeCertificate 88951 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv593]) (by decide +kernel)
def pv88951 : PrimeValue := ⟨88951, pr88951⟩
private theorem pr88969 : PrimeCertificate 88969 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv337]) (by decide +kernel)
def pv88969 : PrimeValue := ⟨88969, pr88969⟩
private theorem pr88993 : PrimeCertificate 88993 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv103]) (by decide +kernel)
def pv88993 : PrimeValue := ⟨88993, pr88993⟩
private theorem pr88997 : PrimeCertificate 88997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv1171]) (by decide +kernel)
def pv88997 : PrimeValue := ⟨88997, pr88997⟩
private theorem pr89003 : PrimeCertificate 89003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv44501]) (by decide +kernel)
def pv89003 : PrimeValue := ⟨89003, pr89003⟩
private theorem pr89021 : PrimeCertificate 89021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv4451]) (by decide +kernel)
def pv89021 : PrimeValue := ⟨89021, pr89021⟩
private theorem pr89041 : PrimeCertificate 89041 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv7,pv53]) (by decide +kernel)
def pv89041 : PrimeValue := ⟨89041, pr89041⟩
private theorem pr89051 : PrimeCertificate 89051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv137]) (by decide +kernel)
def pv89051 : PrimeValue := ⟨89051, pr89051⟩
private theorem pr89057 : PrimeCertificate 89057 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv23]) (by decide +kernel)
def pv89057 : PrimeValue := ⟨89057, pr89057⟩
private theorem pr89071 : PrimeCertificate 89071 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv2969]) (by decide +kernel)
def pv89071 : PrimeValue := ⟨89071, pr89071⟩
private theorem pr89083 : PrimeCertificate 89083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv101]) (by decide +kernel)
def pv89083 : PrimeValue := ⟨89083, pr89083⟩
private theorem pr89087 : PrimeCertificate 89087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv44543]) (by decide +kernel)
def pv89087 : PrimeValue := ⟨89087, pr89087⟩
private theorem pr89101 : PrimeCertificate 89101 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv89101 : PrimeValue := ⟨89101, pr89101⟩
private theorem pr89107 : PrimeCertificate 89107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv14851]) (by decide +kernel)
def pv89107 : PrimeValue := ⟨89107, pr89107⟩
private theorem pr89113 : PrimeCertificate 89113 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv47,pv79]) (by decide +kernel)
def pv89113 : PrimeValue := ⟨89113, pr89113⟩
private theorem pr89119 : PrimeCertificate 89119 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv4951]) (by decide +kernel)
def pv89119 : PrimeValue := ⟨89119, pr89119⟩
private theorem pr89123 : PrimeCertificate 89123 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv4051]) (by decide +kernel)
def pv89123 : PrimeValue := ⟨89123, pr89123⟩
private theorem pr89137 : PrimeCertificate 89137 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv619]) (by decide +kernel)
def pv89137 : PrimeValue := ⟨89137, pr89137⟩
private theorem pr89153 : PrimeCertificate 89153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv199]) (by decide +kernel)
def pv89153 : PrimeValue := ⟨89153, pr89153⟩
private theorem pr89189 : PrimeCertificate 89189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv2027]) (by decide +kernel)
def pv89189 : PrimeValue := ⟨89189, pr89189⟩
private theorem pr89203 : PrimeCertificate 89203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv14867]) (by decide +kernel)
def pv89203 : PrimeValue := ⟨89203, pr89203⟩
private theorem pr89209 : PrimeCertificate 89209 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv7,pv59]) (by decide +kernel)
def pv89209 : PrimeValue := ⟨89209, pr89209⟩
private theorem pr89213 : PrimeCertificate 89213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv22303]) (by decide +kernel)
def pv89213 : PrimeValue := ⟨89213, pr89213⟩
private theorem pr89227 : PrimeCertificate 89227 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv4957]) (by decide +kernel)
def pv89227 : PrimeValue := ⟨89227, pr89227⟩
private theorem pr89231 : PrimeCertificate 89231 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv8923]) (by decide +kernel)
def pv89231 : PrimeValue := ⟨89231, pr89231⟩
private theorem pr89237 : PrimeCertificate 89237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv3187]) (by decide +kernel)
def pv89237 : PrimeValue := ⟨89237, pr89237⟩
private theorem pr89261 : PrimeCertificate 89261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv4463]) (by decide +kernel)
def pv89261 : PrimeValue := ⟨89261, pr89261⟩
private theorem pr89269 : PrimeCertificate 89269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv173]) (by decide +kernel)
def pv89269 : PrimeValue := ⟨89269, pr89269⟩
private theorem pr89273 : PrimeCertificate 89273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11159]) (by decide +kernel)
def pv89273 : PrimeValue := ⟨89273, pr89273⟩
private theorem pr89293 : PrimeCertificate 89293 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv1063]) (by decide +kernel)
def pv89293 : PrimeValue := ⟨89293, pr89293⟩
private theorem pr89303 : PrimeCertificate 89303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv44651]) (by decide +kernel)
def pv89303 : PrimeValue := ⟨89303, pr89303⟩
private theorem pr89317 : PrimeCertificate 89317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv827]) (by decide +kernel)
def pv89317 : PrimeValue := ⟨89317, pr89317⟩
private theorem pr89329 : PrimeCertificate 89329 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv1861]) (by decide +kernel)
def pv89329 : PrimeValue := ⟨89329, pr89329⟩
private theorem pr89363 : PrimeCertificate 89363 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv13,pv491]) (by decide +kernel)
def pv89363 : PrimeValue := ⟨89363, pr89363⟩
private theorem pr89371 : PrimeCertificate 89371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv331]) (by decide +kernel)
def pv89371 : PrimeValue := ⟨89371, pr89371⟩
private theorem pr89381 : PrimeCertificate 89381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41,pv109]) (by decide +kernel)
def pv89381 : PrimeValue := ⟨89381, pr89381⟩
private theorem pr89387 : PrimeCertificate 89387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv17,pv239]) (by decide +kernel)
def pv89387 : PrimeValue := ⟨89387, pr89387⟩
private theorem pr89393 : PrimeCertificate 89393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv151]) (by decide +kernel)
def pv89393 : PrimeValue := ⟨89393, pr89393⟩
private theorem pr89399 : PrimeCertificate 89399 :=
  certifyPrime (q := pv7) (ls := [pv2,pv44699]) (by decide +kernel)
def pv89399 : PrimeValue := ⟨89399, pr89399⟩
private theorem pr89413 : PrimeCertificate 89413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7451]) (by decide +kernel)
def pv89413 : PrimeValue := ⟨89413, pr89413⟩
private theorem pr89417 : PrimeCertificate 89417 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11177]) (by decide +kernel)
def pv89417 : PrimeValue := ⟨89417, pr89417⟩
private theorem pr89431 : PrimeCertificate 89431 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv271]) (by decide +kernel)
def pv89431 : PrimeValue := ⟨89431, pr89431⟩
private theorem pr89443 : PrimeCertificate 89443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv4969]) (by decide +kernel)
def pv89443 : PrimeValue := ⟨89443, pr89443⟩
private theorem pr89449 : PrimeCertificate 89449 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv3727]) (by decide +kernel)
def pv89449 : PrimeValue := ⟨89449, pr89449⟩
private theorem pr89459 : PrimeCertificate 89459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv44729]) (by decide +kernel)
def pv89459 : PrimeValue := ⟨89459, pr89459⟩
private theorem pr89477 : PrimeCertificate 89477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv22369]) (by decide +kernel)
def pv89477 : PrimeValue := ⟨89477, pr89477⟩
private theorem pr89491 : PrimeCertificate 89491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv157]) (by decide +kernel)
def pv89491 : PrimeValue := ⟨89491, pr89491⟩
private theorem pr89501 : PrimeCertificate 89501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv179]) (by decide +kernel)
def pv89501 : PrimeValue := ⟨89501, pr89501⟩
private theorem pr89513 : PrimeCertificate 89513 :=
  certifyPrime (q := pv3) (ls := [pv2,pv67,pv167]) (by decide +kernel)
def pv89513 : PrimeValue := ⟨89513, pr89513⟩
private theorem pr89519 : PrimeCertificate 89519 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv13,pv313]) (by decide +kernel)
def pv89519 : PrimeValue := ⟨89519, pr89519⟩
private theorem pr89521 : PrimeCertificate 89521 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv373]) (by decide +kernel)
def pv89521 : PrimeValue := ⟨89521, pr89521⟩
private theorem pr89527 : PrimeCertificate 89527 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv43,pv347]) (by decide +kernel)
def pv89527 : PrimeValue := ⟨89527, pr89527⟩
private theorem pr89533 : PrimeCertificate 89533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv829]) (by decide +kernel)
def pv89533 : PrimeValue := ⟨89533, pr89533⟩
private theorem pr89561 : PrimeCertificate 89561 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv2239]) (by decide +kernel)
def pv89561 : PrimeValue := ⟨89561, pr89561⟩
private theorem pr89563 : PrimeCertificate 89563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv23,pv59]) (by decide +kernel)
def pv89563 : PrimeValue := ⟨89563, pr89563⟩
private theorem pr89567 : PrimeCertificate 89567 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv2357]) (by decide +kernel)
def pv89567 : PrimeValue := ⟨89567, pr89567⟩
private theorem pr89591 : PrimeCertificate 89591 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv17,pv31]) (by decide +kernel)
def pv89591 : PrimeValue := ⟨89591, pr89591⟩
private theorem pr89597 : PrimeCertificate 89597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv1723]) (by decide +kernel)
def pv89597 : PrimeValue := ⟨89597, pr89597⟩
private theorem pr89599 : PrimeCertificate 89599 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv109,pv137]) (by decide +kernel)
def pv89599 : PrimeValue := ⟨89599, pr89599⟩
private theorem pr89603 : PrimeCertificate 89603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71,pv631]) (by decide +kernel)
def pv89603 : PrimeValue := ⟨89603, pr89603⟩
private theorem pr89611 : PrimeCertificate 89611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv29,pv103]) (by decide +kernel)
def pv89611 : PrimeValue := ⟨89611, pr89611⟩
private theorem pr89627 : PrimeCertificate 89627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv1093]) (by decide +kernel)
def pv89627 : PrimeValue := ⟨89627, pr89627⟩
private theorem pr89633 : PrimeCertificate 89633 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2801]) (by decide +kernel)
def pv89633 : PrimeValue := ⟨89633, pr89633⟩
private theorem pr89653 : PrimeCertificate 89653 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv31,pv241]) (by decide +kernel)
def pv89653 : PrimeValue := ⟨89653, pr89653⟩
private theorem pr89657 : PrimeCertificate 89657 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv1601]) (by decide +kernel)
def pv89657 : PrimeValue := ⟨89657, pr89657⟩
private theorem pr89659 : PrimeCertificate 89659 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv17,pv293]) (by decide +kernel)
def pv89659 : PrimeValue := ⟨89659, pr89659⟩
private theorem pr89669 : PrimeCertificate 89669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv773]) (by decide +kernel)
def pv89669 : PrimeValue := ⟨89669, pr89669⟩
private theorem pr89671 : PrimeCertificate 89671 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv7,pv61]) (by decide +kernel)
def pv89671 : PrimeValue := ⟨89671, pr89671⟩
private theorem pr89681 : PrimeCertificate 89681 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv19,pv59]) (by decide +kernel)
def pv89681 : PrimeValue := ⟨89681, pr89681⟩
private theorem pr89689 : PrimeCertificate 89689 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv37,pv101]) (by decide +kernel)
def pv89689 : PrimeValue := ⟨89689, pr89689⟩
private theorem pr89753 : PrimeCertificate 89753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv863]) (by decide +kernel)
def pv89753 : PrimeValue := ⟨89753, pr89753⟩
private theorem pr89759 : PrimeCertificate 89759 :=
  certifyPrime (q := pv13) (ls := [pv2,pv44879]) (by decide +kernel)
def pv89759 : PrimeValue := ⟨89759, pr89759⟩
private theorem pr89767 : PrimeCertificate 89767 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv4987]) (by decide +kernel)
def pv89767 : PrimeValue := ⟨89767, pr89767⟩
private theorem pr89779 : PrimeCertificate 89779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv1151]) (by decide +kernel)
def pv89779 : PrimeValue := ⟨89779, pr89779⟩
private theorem pr89783 : PrimeCertificate 89783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11,pv53]) (by decide +kernel)
def pv89783 : PrimeValue := ⟨89783, pr89783⟩
private theorem pr89797 : PrimeCertificate 89797 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv1069]) (by decide +kernel)
def pv89797 : PrimeValue := ⟨89797, pr89797⟩
private theorem pr89809 : PrimeCertificate 89809 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1871]) (by decide +kernel)
def pv89809 : PrimeValue := ⟨89809, pr89809⟩
private theorem pr89821 : PrimeCertificate 89821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv499]) (by decide +kernel)
def pv89821 : PrimeValue := ⟨89821, pr89821⟩
private theorem pr89833 : PrimeCertificate 89833 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv197]) (by decide +kernel)
def pv89833 : PrimeValue := ⟨89833, pr89833⟩
private theorem pr89839 : PrimeCertificate 89839 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv23,pv31]) (by decide +kernel)
def pv89839 : PrimeValue := ⟨89839, pr89839⟩
private theorem pr89849 : PrimeCertificate 89849 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv1021]) (by decide +kernel)
def pv89849 : PrimeValue := ⟨89849, pr89849⟩
private theorem pr89867 : PrimeCertificate 89867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv131]) (by decide +kernel)
def pv89867 : PrimeValue := ⟨89867, pr89867⟩
private theorem pr89891 : PrimeCertificate 89891 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv89,pv101]) (by decide +kernel)
def pv89891 : PrimeValue := ⟨89891, pr89891⟩
private theorem pr89897 : PrimeCertificate 89897 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv661]) (by decide +kernel)
def pv89897 : PrimeValue := ⟨89897, pr89897⟩
private theorem pr89899 : PrimeCertificate 89899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv14983]) (by decide +kernel)
def pv89899 : PrimeValue := ⟨89899, pr89899⟩
private theorem pr89909 : PrimeCertificate 89909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv19]) (by decide +kernel)
def pv89909 : PrimeValue := ⟨89909, pr89909⟩
private theorem pr89917 : PrimeCertificate 89917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv59,pv127]) (by decide +kernel)
def pv89917 : PrimeValue := ⟨89917, pr89917⟩
private theorem pr89923 : PrimeCertificate 89923 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv2141]) (by decide +kernel)
def pv89923 : PrimeValue := ⟨89923, pr89923⟩
private theorem pr89939 : PrimeCertificate 89939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv193,pv233]) (by decide +kernel)
def pv89939 : PrimeValue := ⟨89939, pr89939⟩
private theorem pr89959 : PrimeCertificate 89959 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv29,pv47]) (by decide +kernel)
def pv89959 : PrimeValue := ⟨89959, pr89959⟩
private theorem pr89963 : PrimeCertificate 89963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv1451]) (by decide +kernel)
def pv89963 : PrimeValue := ⟨89963, pr89963⟩
private theorem pr89977 : PrimeCertificate 89977 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv163]) (by decide +kernel)
def pv89977 : PrimeValue := ⟨89977, pr89977⟩
private theorem pr89983 : PrimeCertificate 89983 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv4999]) (by decide +kernel)
def pv89983 : PrimeValue := ⟨89983, pr89983⟩
private theorem pr89989 : PrimeCertificate 89989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7499]) (by decide +kernel)
def pv89989 : PrimeValue := ⟨89989, pr89989⟩
private theorem pr90001 : PrimeCertificate 90001 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv90001 : PrimeValue := ⟨90001, pr90001⟩
private theorem pr90007 : PrimeCertificate 90007 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv2143]) (by decide +kernel)
def pv90007 : PrimeValue := ⟨90007, pr90007⟩
private theorem pr90011 : PrimeCertificate 90011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv9001]) (by decide +kernel)
def pv90011 : PrimeValue := ⟨90011, pr90011⟩
private theorem pr90017 : PrimeCertificate 90017 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv97]) (by decide +kernel)
def pv90017 : PrimeValue := ⟨90017, pr90017⟩
private theorem pr90019 : PrimeCertificate 90019 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv1667]) (by decide +kernel)
def pv90019 : PrimeValue := ⟨90019, pr90019⟩
private theorem pr90023 : PrimeCertificate 90023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv23,pv103]) (by decide +kernel)
def pv90023 : PrimeValue := ⟨90023, pr90023⟩
private theorem pr90031 : PrimeCertificate 90031 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv3001]) (by decide +kernel)
def pv90031 : PrimeValue := ⟨90031, pr90031⟩
private theorem pr90053 : PrimeCertificate 90053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv479]) (by decide +kernel)
def pv90053 : PrimeValue := ⟨90053, pr90053⟩
private theorem pr90059 : PrimeCertificate 90059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv1217]) (by decide +kernel)
def pv90059 : PrimeValue := ⟨90059, pr90059⟩
private theorem pr90067 : PrimeCertificate 90067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv883]) (by decide +kernel)
def pv90067 : PrimeValue := ⟨90067, pr90067⟩
private theorem pr90071 : PrimeCertificate 90071 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv9007]) (by decide +kernel)
def pv90071 : PrimeValue := ⟨90071, pr90071⟩
private theorem pr90073 : PrimeCertificate 90073 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv139]) (by decide +kernel)
def pv90073 : PrimeValue := ⟨90073, pr90073⟩
private theorem pr90089 : PrimeCertificate 90089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11261]) (by decide +kernel)
def pv90089 : PrimeValue := ⟨90089, pr90089⟩
private theorem pr90107 : PrimeCertificate 90107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv45053]) (by decide +kernel)
def pv90107 : PrimeValue := ⟨90107, pr90107⟩
private theorem pr90121 : PrimeCertificate 90121 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv751]) (by decide +kernel)
def pv90121 : PrimeValue := ⟨90121, pr90121⟩
private theorem pr90127 : PrimeCertificate 90127 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1669]) (by decide +kernel)
def pv90127 : PrimeValue := ⟨90127, pr90127⟩
private theorem pr90149 : PrimeCertificate 90149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv727]) (by decide +kernel)
def pv90149 : PrimeValue := ⟨90149, pr90149⟩
private theorem pr90163 : PrimeCertificate 90163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5009]) (by decide +kernel)
def pv90163 : PrimeValue := ⟨90163, pr90163⟩
private theorem pr90173 : PrimeCertificate 90173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv22543]) (by decide +kernel)
def pv90173 : PrimeValue := ⟨90173, pr90173⟩
private theorem pr90187 : PrimeCertificate 90187 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv15031]) (by decide +kernel)
def pv90187 : PrimeValue := ⟨90187, pr90187⟩
private theorem pr90191 : PrimeCertificate 90191 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv29,pv311]) (by decide +kernel)
def pv90191 : PrimeValue := ⟨90191, pr90191⟩
private theorem pr90197 : PrimeCertificate 90197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv22549]) (by decide +kernel)
def pv90197 : PrimeValue := ⟨90197, pr90197⟩
private theorem pr90199 : PrimeCertificate 90199 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5011]) (by decide +kernel)
def pv90199 : PrimeValue := ⟨90199, pr90199⟩
private theorem pr90203 : PrimeCertificate 90203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv17,pv379]) (by decide +kernel)
def pv90203 : PrimeValue := ⟨90203, pr90203⟩
private theorem pr90217 : PrimeCertificate 90217 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv7,pv179]) (by decide +kernel)
def pv90217 : PrimeValue := ⟨90217, pr90217⟩
private theorem pr90227 : PrimeCertificate 90227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv197,pv229]) (by decide +kernel)
def pv90227 : PrimeValue := ⟨90227, pr90227⟩
private theorem pr90239 : PrimeCertificate 90239 :=
  certifyPrime (q := pv7) (ls := [pv2,pv45119]) (by decide +kernel)
def pv90239 : PrimeValue := ⟨90239, pr90239⟩
private theorem pr90247 : PrimeCertificate 90247 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv89]) (by decide +kernel)
def pv90247 : PrimeValue := ⟨90247, pr90247⟩
private theorem pr90263 : PrimeCertificate 90263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv45131]) (by decide +kernel)
def pv90263 : PrimeValue := ⟨90263, pr90263⟩
private theorem pr90271 : PrimeCertificate 90271 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv17,pv59]) (by decide +kernel)
def pv90271 : PrimeValue := ⟨90271, pr90271⟩
private theorem pr90281 : PrimeCertificate 90281 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv37,pv61]) (by decide +kernel)
def pv90281 : PrimeValue := ⟨90281, pr90281⟩
private theorem pr90289 : PrimeCertificate 90289 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv11,pv19]) (by decide +kernel)
def pv90289 : PrimeValue := ⟨90289, pr90289⟩
private theorem pr90313 : PrimeCertificate 90313 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv53,pv71]) (by decide +kernel)
def pv90313 : PrimeValue := ⟨90313, pr90313⟩
private theorem pr90353 : PrimeCertificate 90353 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5647]) (by decide +kernel)
def pv90353 : PrimeValue := ⟨90353, pr90353⟩
private theorem pr90359 : PrimeCertificate 90359 :=
  certifyPrime (q := pv11) (ls := [pv2,pv45179]) (by decide +kernel)
def pv90359 : PrimeValue := ⟨90359, pr90359⟩
private theorem pr90371 : PrimeCertificate 90371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv1291]) (by decide +kernel)
def pv90371 : PrimeValue := ⟨90371, pr90371⟩
private theorem pr90373 : PrimeCertificate 90373 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv443]) (by decide +kernel)
def pv90373 : PrimeValue := ⟨90373, pr90373⟩
private theorem pr90379 : PrimeCertificate 90379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5021]) (by decide +kernel)
def pv90379 : PrimeValue := ⟨90379, pr90379⟩
private theorem pr90397 : PrimeCertificate 90397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31]) (by decide +kernel)
def pv90397 : PrimeValue := ⟨90397, pr90397⟩
private theorem pr90401 : PrimeCertificate 90401 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv113]) (by decide +kernel)
def pv90401 : PrimeValue := ⟨90401, pr90401⟩
private theorem pr90403 : PrimeCertificate 90403 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv19,pv61]) (by decide +kernel)
def pv90403 : PrimeValue := ⟨90403, pr90403⟩
private theorem pr90407 : PrimeCertificate 90407 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv2659]) (by decide +kernel)
def pv90407 : PrimeValue := ⟨90407, pr90407⟩
private theorem pr90437 : PrimeCertificate 90437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv983]) (by decide +kernel)
def pv90437 : PrimeValue := ⟨90437, pr90437⟩
private theorem pr90439 : PrimeCertificate 90439 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv15073]) (by decide +kernel)
def pv90439 : PrimeValue := ⟨90439, pr90439⟩
private theorem pr90469 : PrimeCertificate 90469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv359]) (by decide +kernel)
def pv90469 : PrimeValue := ⟨90469, pr90469⟩
private theorem pr90473 : PrimeCertificate 90473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43,pv263]) (by decide +kernel)
def pv90473 : PrimeValue := ⟨90473, pr90473⟩
private theorem pr90481 : PrimeCertificate 90481 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv13,pv29]) (by decide +kernel)
def pv90481 : PrimeValue := ⟨90481, pr90481⟩
private theorem pr90499 : PrimeCertificate 90499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv15083]) (by decide +kernel)
def pv90499 : PrimeValue := ⟨90499, pr90499⟩
private theorem pr90511 : PrimeCertificate 90511 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv431]) (by decide +kernel)
def pv90511 : PrimeValue := ⟨90511, pr90511⟩
private theorem pr90523 : PrimeCertificate 90523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv107]) (by decide +kernel)
def pv90523 : PrimeValue := ⟨90523, pr90523⟩
private theorem pr90527 : PrimeCertificate 90527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv45263]) (by decide +kernel)
def pv90527 : PrimeValue := ⟨90527, pr90527⟩
private theorem pr90529 : PrimeCertificate 90529 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23,pv41]) (by decide +kernel)
def pv90529 : PrimeValue := ⟨90529, pr90529⟩
private theorem pr90533 : PrimeCertificate 90533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv1741]) (by decide +kernel)
def pv90533 : PrimeValue := ⟨90533, pr90533⟩
private theorem pr90583 : PrimeCertificate 90583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv487]) (by decide +kernel)
def pv90583 : PrimeValue := ⟨90583, pr90583⟩
private theorem pr90599 : PrimeCertificate 90599 :=
  certifyPrime (q := pv11) (ls := [pv2,pv97,pv467]) (by decide +kernel)
def pv90599 : PrimeValue := ⟨90599, pr90599⟩
private theorem pr90617 : PrimeCertificate 90617 :=
  certifyPrime (q := pv3) (ls := [pv2,pv47,pv241]) (by decide +kernel)
def pv90617 : PrimeValue := ⟨90617, pr90617⟩
private theorem pr90619 : PrimeCertificate 90619 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv1373]) (by decide +kernel)
def pv90619 : PrimeValue := ⟨90619, pr90619⟩
private theorem pr90631 : PrimeCertificate 90631 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv19,pv53]) (by decide +kernel)
def pv90631 : PrimeValue := ⟨90631, pr90631⟩
private theorem pr90641 : PrimeCertificate 90641 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv103]) (by decide +kernel)
def pv90641 : PrimeValue := ⟨90641, pr90641⟩
private theorem pr90647 : PrimeCertificate 90647 :=
  certifyPrime (q := pv5) (ls := [pv2,pv61,pv743]) (by decide +kernel)
def pv90647 : PrimeValue := ⟨90647, pr90647⟩
private theorem pr90659 : PrimeCertificate 90659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv45329]) (by decide +kernel)
def pv90659 : PrimeValue := ⟨90659, pr90659⟩
private theorem pr90679 : PrimeCertificate 90679 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv17,pv127]) (by decide +kernel)
def pv90679 : PrimeValue := ⟨90679, pr90679⟩
private theorem pr90697 : PrimeCertificate 90697 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3779]) (by decide +kernel)
def pv90697 : PrimeValue := ⟨90697, pr90697⟩
private theorem pr90703 : PrimeCertificate 90703 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5039]) (by decide +kernel)
def pv90703 : PrimeValue := ⟨90703, pr90703⟩
private theorem pr90749 : PrimeCertificate 90749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv463]) (by decide +kernel)
def pv90749 : PrimeValue := ⟨90749, pr90749⟩
private theorem pr90787 : PrimeCertificate 90787 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv15131]) (by decide +kernel)
def pv90787 : PrimeValue := ⟨90787, pr90787⟩
private theorem pr90793 : PrimeCertificate 90793 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv97]) (by decide +kernel)
def pv90793 : PrimeValue := ⟨90793, pr90793⟩
private theorem pr90803 : PrimeCertificate 90803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv83,pv547]) (by decide +kernel)
def pv90803 : PrimeValue := ⟨90803, pr90803⟩
private theorem pr90821 : PrimeCertificate 90821 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv19,pv239]) (by decide +kernel)
def pv90821 : PrimeValue := ⟨90821, pr90821⟩
private theorem pr90823 : PrimeCertificate 90823 :=
  certifyPrime (q := pv61) (ls := [pv2,pv3,pv15137]) (by decide +kernel)
def pv90823 : PrimeValue := ⟨90823, pr90823⟩
private theorem pr90833 : PrimeCertificate 90833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv811]) (by decide +kernel)
def pv90833 : PrimeValue := ⟨90833, pr90833⟩
private theorem pr90841 : PrimeCertificate 90841 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv757]) (by decide +kernel)
def pv90841 : PrimeValue := ⟨90841, pr90841⟩
private theorem pr90847 : PrimeCertificate 90847 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv103]) (by decide +kernel)
def pv90847 : PrimeValue := ⟨90847, pr90847⟩
private theorem pr90863 : PrimeCertificate 90863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv181,pv251]) (by decide +kernel)
def pv90863 : PrimeValue := ⟨90863, pr90863⟩
private theorem pr90887 : PrimeCertificate 90887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv29,pv1567]) (by decide +kernel)
def pv90887 : PrimeValue := ⟨90887, pr90887⟩
private theorem pr90901 : PrimeCertificate 90901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv101]) (by decide +kernel)
def pv90901 : PrimeValue := ⟨90901, pr90901⟩
private theorem pr90907 : PrimeCertificate 90907 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv109,pv139]) (by decide +kernel)
def pv90907 : PrimeValue := ⟨90907, pr90907⟩
private theorem pr90911 : PrimeCertificate 90911 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv9091]) (by decide +kernel)
def pv90911 : PrimeValue := ⟨90911, pr90911⟩
private theorem pr90917 : PrimeCertificate 90917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv17,pv191]) (by decide +kernel)
def pv90917 : PrimeValue := ⟨90917, pr90917⟩
private theorem pr90931 : PrimeCertificate 90931 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv433]) (by decide +kernel)
def pv90931 : PrimeValue := ⟨90931, pr90931⟩
private theorem pr90947 : PrimeCertificate 90947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv1229]) (by decide +kernel)
def pv90947 : PrimeValue := ⟨90947, pr90947⟩
private theorem pr90971 : PrimeCertificate 90971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv827]) (by decide +kernel)
def pv90971 : PrimeValue := ⟨90971, pr90971⟩
private theorem pr90977 : PrimeCertificate 90977 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2843]) (by decide +kernel)
def pv90977 : PrimeValue := ⟨90977, pr90977⟩
private theorem pr90989 : PrimeCertificate 90989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv43]) (by decide +kernel)
def pv90989 : PrimeValue := ⟨90989, pr90989⟩
private theorem pr90997 : PrimeCertificate 90997 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7583]) (by decide +kernel)
def pv90997 : PrimeValue := ⟨90997, pr90997⟩
private theorem pr91009 : PrimeCertificate 91009 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv79]) (by decide +kernel)
def pv91009 : PrimeValue := ⟨91009, pr91009⟩
private theorem pr91019 : PrimeCertificate 91019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv2677]) (by decide +kernel)
def pv91019 : PrimeValue := ⟨91019, pr91019⟩
private theorem pr91033 : PrimeCertificate 91033 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3793]) (by decide +kernel)
def pv91033 : PrimeValue := ⟨91033, pr91033⟩
private theorem pr91079 : PrimeCertificate 91079 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv31,pv113]) (by decide +kernel)
def pv91079 : PrimeValue := ⟨91079, pr91079⟩
private theorem pr91081 : PrimeCertificate 91081 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv11,pv23]) (by decide +kernel)
def pv91081 : PrimeValue := ⟨91081, pr91081⟩
private theorem pr91097 : PrimeCertificate 91097 :=
  certifyPrime (q := pv3) (ls := [pv2,pv59,pv193]) (by decide +kernel)
def pv91097 : PrimeValue := ⟨91097, pr91097⟩
private theorem pr91121 : PrimeCertificate 91121 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv17,pv67]) (by decide +kernel)
def pv91121 : PrimeValue := ⟨91121, pr91121⟩
private theorem pr91127 : PrimeCertificate 91127 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv23,pv283]) (by decide +kernel)
def pv91127 : PrimeValue := ⟨91127, pr91127⟩
private theorem pr91129 : PrimeCertificate 91129 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv3797]) (by decide +kernel)
def pv91129 : PrimeValue := ⟨91129, pr91129⟩
private theorem pr91139 : PrimeCertificate 91139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv45569]) (by decide +kernel)
def pv91139 : PrimeValue := ⟨91139, pr91139⟩
private theorem pr91141 : PrimeCertificate 91141 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv31]) (by decide +kernel)
def pv91141 : PrimeValue := ⟨91141, pr91141⟩
private theorem pr91151 : PrimeCertificate 91151 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv1823]) (by decide +kernel)
def pv91151 : PrimeValue := ⟨91151, pr91151⟩
private theorem pr91153 : PrimeCertificate 91153 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv211]) (by decide +kernel)
def pv91153 : PrimeValue := ⟨91153, pr91153⟩
private theorem pr91159 : PrimeCertificate 91159 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv15193]) (by decide +kernel)
def pv91159 : PrimeValue := ⟨91159, pr91159⟩
private theorem pr91163 : PrimeCertificate 91163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv2399]) (by decide +kernel)
def pv91163 : PrimeValue := ⟨91163, pr91163⟩
private theorem pr91183 : PrimeCertificate 91183 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv167]) (by decide +kernel)
def pv91183 : PrimeValue := ⟨91183, pr91183⟩
private theorem pr91193 : PrimeCertificate 91193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11399]) (by decide +kernel)
def pv91193 : PrimeValue := ⟨91193, pr91193⟩
private theorem pr91199 : PrimeCertificate 91199 :=
  certifyPrime (q := pv11) (ls := [pv2,pv45599]) (by decide +kernel)
def pv91199 : PrimeValue := ⟨91199, pr91199⟩
private theorem pr91229 : PrimeCertificate 91229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv22807]) (by decide +kernel)
def pv91229 : PrimeValue := ⟨91229, pr91229⟩
private theorem pr91237 : PrimeCertificate 91237 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv7603]) (by decide +kernel)
def pv91237 : PrimeValue := ⟨91237, pr91237⟩
private theorem pr91243 : PrimeCertificate 91243 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv37,pv137]) (by decide +kernel)
def pv91243 : PrimeValue := ⟨91243, pr91243⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
