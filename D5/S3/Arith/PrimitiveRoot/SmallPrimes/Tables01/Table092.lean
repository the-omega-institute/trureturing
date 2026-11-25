/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table092
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table092.pv341947
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table014
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table023
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table058
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table059

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr341947 : PrimeCertificate 341947 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv157]) (by decide +kernel)
def pv341947 : PrimeValue := ⟨341947, pr341947⟩
private theorem pr341951 : PrimeCertificate 341951 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv977]) (by decide +kernel)
def pv341951 : PrimeValue := ⟨341951, pr341951⟩
private theorem pr341953 : PrimeCertificate 341953 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv137]) (by decide +kernel)
def pv341953 : PrimeValue := ⟨341953, pr341953⟩
private theorem pr342037 : PrimeCertificate 342037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3167]) (by decide +kernel)
def pv342037 : PrimeValue := ⟨342037, pr342037⟩
private theorem pr342059 : PrimeCertificate 342059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv171029]) (by decide +kernel)
def pv342059 : PrimeValue := ⟨342059, pr342059⟩
private theorem pr342073 : PrimeCertificate 342073 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4751]) (by decide +kernel)
def pv342073 : PrimeValue := ⟨342073, pr342073⟩
private theorem pr342143 : PrimeCertificate 342143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv29,pv347]) (by decide +kernel)
def pv342143 : PrimeValue := ⟨342143, pr342143⟩
private theorem pr342179 : PrimeCertificate 342179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv5519]) (by decide +kernel)
def pv342179 : PrimeValue := ⟨342179, pr342179⟩
private theorem pr342203 : PrimeCertificate 342203 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv24443]) (by decide +kernel)
def pv342203 : PrimeValue := ⟨342203, pr342203⟩
private theorem pr342241 : PrimeCertificate 342241 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv23,pv31]) (by decide +kernel)
def pv342241 : PrimeValue := ⟨342241, pr342241⟩
private theorem pr342283 : PrimeCertificate 342283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv57047]) (by decide +kernel)
def pv342283 : PrimeValue := ⟨342283, pr342283⟩
private theorem pr342299 : PrimeCertificate 342299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv15559]) (by decide +kernel)
def pv342299 : PrimeValue := ⟨342299, pr342299⟩
private theorem pr342319 : PrimeCertificate 342319 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv59,pv967]) (by decide +kernel)
def pv342319 : PrimeValue := ⟨342319, pr342319⟩
private theorem pr342337 : PrimeCertificate 342337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1783]) (by decide +kernel)
def pv342337 : PrimeValue := ⟨342337, pr342337⟩
private theorem pr342341 : PrimeCertificate 342341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17117]) (by decide +kernel)
def pv342341 : PrimeValue := ⟨342341, pr342341⟩
private theorem pr342343 : PrimeCertificate 342343 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv13,pv19]) (by decide +kernel)
def pv342343 : PrimeValue := ⟨342343, pr342343⟩
private theorem pr342379 : PrimeCertificate 342379 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv827]) (by decide +kernel)
def pv342379 : PrimeValue := ⟨342379, pr342379⟩
private theorem pr342451 : PrimeCertificate 342451 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv761]) (by decide +kernel)
def pv342451 : PrimeValue := ⟨342451, pr342451⟩
private theorem pr342497 : PrimeCertificate 342497 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11,pv139]) (by decide +kernel)
def pv342497 : PrimeValue := ⟨342497, pr342497⟩
private theorem pr342521 : PrimeCertificate 342521 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv8563]) (by decide +kernel)
def pv342521 : PrimeValue := ⟨342521, pr342521⟩
private theorem pr342527 : PrimeCertificate 342527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv171263]) (by decide +kernel)
def pv342527 : PrimeValue := ⟨342527, pr342527⟩
private theorem pr342547 : PrimeCertificate 342547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv1543]) (by decide +kernel)
def pv342547 : PrimeValue := ⟨342547, pr342547⟩
private theorem pr342599 : PrimeCertificate 342599 :=
  certifyPrime (q := pv11) (ls := [pv2,pv171299]) (by decide +kernel)
def pv342599 : PrimeValue := ⟨342599, pr342599⟩
private theorem pr342659 : PrimeCertificate 342659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv171329]) (by decide +kernel)
def pv342659 : PrimeValue := ⟨342659, pr342659⟩
private theorem pr342691 : PrimeCertificate 342691 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11423]) (by decide +kernel)
def pv342691 : PrimeValue := ⟨342691, pr342691⟩
private theorem pr342733 : PrimeCertificate 342733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv342733 : PrimeValue := ⟨342733, pr342733⟩
private theorem pr342821 : PrimeCertificate 342821 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv61,pv281]) (by decide +kernel)
def pv342821 : PrimeValue := ⟨342821, pr342821⟩
private theorem pr342841 : PrimeCertificate 342841 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv2857]) (by decide +kernel)
def pv342841 : PrimeValue := ⟨342841, pr342841⟩
private theorem pr342847 : PrimeCertificate 342847 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv907]) (by decide +kernel)
def pv342847 : PrimeValue := ⟨342847, pr342847⟩
private theorem pr342863 : PrimeCertificate 342863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv13187]) (by decide +kernel)
def pv342863 : PrimeValue := ⟨342863, pr342863⟩
private theorem pr342869 : PrimeCertificate 342869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv85717]) (by decide +kernel)
def pv342869 : PrimeValue := ⟨342869, pr342869⟩
private theorem pr342871 : PrimeCertificate 342871 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv1039]) (by decide +kernel)
def pv342871 : PrimeValue := ⟨342871, pr342871⟩
private theorem pr342889 : PrimeCertificate 342889 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv13,pv157]) (by decide +kernel)
def pv342889 : PrimeValue := ⟨342889, pr342889⟩
private theorem pr342929 : PrimeCertificate 342929 :=
  certifyPrime (q := pv3) (ls := [pv2,pv21433]) (by decide +kernel)
def pv342929 : PrimeValue := ⟨342929, pr342929⟩
private theorem pr343019 : PrimeCertificate 343019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv79,pv167]) (by decide +kernel)
def pv343019 : PrimeValue := ⟨343019, pr343019⟩
private theorem pr343037 : PrimeCertificate 343037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv191,pv449]) (by decide +kernel)
def pv343037 : PrimeValue := ⟨343037, pr343037⟩
private theorem pr343073 : PrimeCertificate 343073 :=
  certifyPrime (q := pv3) (ls := [pv2,pv71,pv151]) (by decide +kernel)
def pv343073 : PrimeValue := ⟨343073, pr343073⟩
private theorem pr343141 : PrimeCertificate 343141 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv19,pv43]) (by decide +kernel)
def pv343141 : PrimeValue := ⟨343141, pr343141⟩
private theorem pr343153 : PrimeCertificate 343153 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2383]) (by decide +kernel)
def pv343153 : PrimeValue := ⟨343153, pr343153⟩
private theorem pr343169 : PrimeCertificate 343169 :=
  certifyPrime (q := pv13) (ls := [pv2,pv7,pv383]) (by decide +kernel)
def pv343169 : PrimeValue := ⟨343169, pr343169⟩
private theorem pr343177 : PrimeCertificate 343177 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv79,pv181]) (by decide +kernel)
def pv343177 : PrimeValue := ⟨343177, pr343177⟩
private theorem pr343243 : PrimeCertificate 343243 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19069]) (by decide +kernel)
def pv343243 : PrimeValue := ⟨343243, pr343243⟩
private theorem pr343303 : PrimeCertificate 343303 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv1973]) (by decide +kernel)
def pv343303 : PrimeValue := ⟨343303, pr343303⟩
private theorem pr343307 : PrimeCertificate 343307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv171653]) (by decide +kernel)
def pv343307 : PrimeValue := ⟨343307, pr343307⟩
private theorem pr343313 : PrimeCertificate 343313 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43,pv499]) (by decide +kernel)
def pv343313 : PrimeValue := ⟨343313, pr343313⟩
private theorem pr343379 : PrimeCertificate 343379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv24527]) (by decide +kernel)
def pv343379 : PrimeValue := ⟨343379, pr343379⟩
private theorem pr343381 : PrimeCertificate 343381 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv5,pv59,pv97]) (by decide +kernel)
def pv343381 : PrimeValue := ⟨343381, pr343381⟩
private theorem pr343391 : PrimeCertificate 343391 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv23,pv1493]) (by decide +kernel)
def pv343391 : PrimeValue := ⟨343391, pr343391⟩
private theorem pr343411 : PrimeCertificate 343411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11447]) (by decide +kernel)
def pv343411 : PrimeValue := ⟨343411, pr343411⟩
private theorem pr343433 : PrimeCertificate 343433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv42929]) (by decide +kernel)
def pv343433 : PrimeValue := ⟨343433, pr343433⟩
private theorem pr343481 : PrimeCertificate 343481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv31,pv277]) (by decide +kernel)
def pv343481 : PrimeValue := ⟨343481, pr343481⟩
private theorem pr343489 : PrimeCertificate 343489 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1789]) (by decide +kernel)
def pv343489 : PrimeValue := ⟨343489, pr343489⟩
private theorem pr343531 : PrimeCertificate 343531 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv347]) (by decide +kernel)
def pv343531 : PrimeValue := ⟨343531, pr343531⟩
private theorem pr343543 : PrimeCertificate 343543 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31,pv1847]) (by decide +kernel)
def pv343543 : PrimeValue := ⟨343543, pr343543⟩
private theorem pr343589 : PrimeCertificate 343589 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv1753]) (by decide +kernel)
def pv343589 : PrimeValue := ⟨343589, pr343589⟩
private theorem pr343591 : PrimeCertificate 343591 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv881]) (by decide +kernel)
def pv343591 : PrimeValue := ⟨343591, pr343591⟩
private theorem pr343639 : PrimeCertificate 343639 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv1123]) (by decide +kernel)
def pv343639 : PrimeValue := ⟨343639, pr343639⟩
private theorem pr343649 : PrimeCertificate 343649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv10739]) (by decide +kernel)
def pv343649 : PrimeValue := ⟨343649, pr343649⟩
private theorem pr343661 : PrimeCertificate 343661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17183]) (by decide +kernel)
def pv343661 : PrimeValue := ⟨343661, pr343661⟩
private theorem pr343667 : PrimeCertificate 343667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv31,pv241]) (by decide +kernel)
def pv343667 : PrimeValue := ⟨343667, pr343667⟩
private theorem pr343687 : PrimeCertificate 343687 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv167]) (by decide +kernel)
def pv343687 : PrimeValue := ⟨343687, pr343687⟩
private theorem pr343771 : PrimeCertificate 343771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv1637]) (by decide +kernel)
def pv343771 : PrimeValue := ⟨343771, pr343771⟩
private theorem pr343801 : PrimeCertificate 343801 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv191]) (by decide +kernel)
def pv343801 : PrimeValue := ⟨343801, pr343801⟩
private theorem pr343817 : PrimeCertificate 343817 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv3907]) (by decide +kernel)
def pv343817 : PrimeValue := ⟨343817, pr343817⟩
private theorem pr343823 : PrimeCertificate 343823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv353,pv487]) (by decide +kernel)
def pv343823 : PrimeValue := ⟨343823, pr343823⟩
private theorem pr343939 : PrimeCertificate 343939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv19,pv431]) (by decide +kernel)
def pv343939 : PrimeValue := ⟨343939, pr343939⟩
private theorem pr343951 : PrimeCertificate 343951 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv2293]) (by decide +kernel)
def pv343951 : PrimeValue := ⟨343951, pr343951⟩
private theorem pr343963 : PrimeCertificate 343963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv97,pv197]) (by decide +kernel)
def pv343963 : PrimeValue := ⟨343963, pr343963⟩
private theorem pr343997 : PrimeCertificate 343997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv85999]) (by decide +kernel)
def pv343997 : PrimeValue := ⟨343997, pr343997⟩
private theorem pr344039 : PrimeCertificate 344039 :=
  certifyPrime (q := pv11) (ls := [pv2,pv31,pv179]) (by decide +kernel)
def pv344039 : PrimeValue := ⟨344039, pr344039⟩
private theorem pr344053 : PrimeCertificate 344053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv503]) (by decide +kernel)
def pv344053 : PrimeValue := ⟨344053, pr344053⟩
private theorem pr344111 : PrimeCertificate 344111 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv13,pv2647]) (by decide +kernel)
def pv344111 : PrimeValue := ⟨344111, pr344111⟩
private theorem pr344117 : PrimeCertificate 344117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv86029]) (by decide +kernel)
def pv344117 : PrimeValue := ⟨344117, pr344117⟩
private theorem pr344153 : PrimeCertificate 344153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43019]) (by decide +kernel)
def pv344153 : PrimeValue := ⟨344153, pr344153⟩
private theorem pr344161 : PrimeCertificate 344161 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv239]) (by decide +kernel)
def pv344161 : PrimeValue := ⟨344161, pr344161⟩
private theorem pr344171 : PrimeCertificate 344171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv127,pv271]) (by decide +kernel)
def pv344171 : PrimeValue := ⟨344171, pr344171⟩
private theorem pr344173 : PrimeCertificate 344173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv29,pv43]) (by decide +kernel)
def pv344173 : PrimeValue := ⟨344173, pr344173⟩
private theorem pr344177 : PrimeCertificate 344177 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv439]) (by decide +kernel)
def pv344177 : PrimeValue := ⟨344177, pr344177⟩
private theorem pr344189 : PrimeCertificate 344189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv6619]) (by decide +kernel)
def pv344189 : PrimeValue := ⟨344189, pr344189⟩
private theorem pr344209 : PrimeCertificate 344209 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv71,pv101]) (by decide +kernel)
def pv344209 : PrimeValue := ⟨344209, pr344209⟩
private theorem pr344231 : PrimeCertificate 344231 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv29,pv1187]) (by decide +kernel)
def pv344231 : PrimeValue := ⟨344231, pr344231⟩
private theorem pr344237 : PrimeCertificate 344237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv2099]) (by decide +kernel)
def pv344237 : PrimeValue := ⟨344237, pr344237⟩
private theorem pr344263 : PrimeCertificate 344263 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv181,pv317]) (by decide +kernel)
def pv344263 : PrimeValue := ⟨344263, pr344263⟩
private theorem pr344273 : PrimeCertificate 344273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv21517]) (by decide +kernel)
def pv344273 : PrimeValue := ⟨344273, pr344273⟩
private theorem pr344291 : PrimeCertificate 344291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv34429]) (by decide +kernel)
def pv344291 : PrimeValue := ⟨344291, pr344291⟩
private theorem pr344293 : PrimeCertificate 344293 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv2207]) (by decide +kernel)
def pv344293 : PrimeValue := ⟨344293, pr344293⟩
private theorem pr344327 : PrimeCertificate 344327 :=
  certifyPrime (q := pv5) (ls := [pv2,pv107,pv1609]) (by decide +kernel)
def pv344327 : PrimeValue := ⟨344327, pr344327⟩
private theorem pr344347 : PrimeCertificate 344347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv1979]) (by decide +kernel)
def pv344347 : PrimeValue := ⟨344347, pr344347⟩
private theorem pr344363 : PrimeCertificate 344363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv172181]) (by decide +kernel)
def pv344363 : PrimeValue := ⟨344363, pr344363⟩
private theorem pr344423 : PrimeCertificate 344423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv1019]) (by decide +kernel)
def pv344423 : PrimeValue := ⟨344423, pr344423⟩
private theorem pr344453 : PrimeCertificate 344453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv86113]) (by decide +kernel)
def pv344453 : PrimeValue := ⟨344453, pr344453⟩
private theorem pr344483 : PrimeCertificate 344483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv4201]) (by decide +kernel)
def pv344483 : PrimeValue := ⟨344483, pr344483⟩
private theorem pr344497 : PrimeCertificate 344497 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7177]) (by decide +kernel)
def pv344497 : PrimeValue := ⟨344497, pr344497⟩
private theorem pr344599 : PrimeCertificate 344599 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv79,pv727]) (by decide +kernel)
def pv344599 : PrimeValue := ⟨344599, pr344599⟩
private theorem pr344639 : PrimeCertificate 344639 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv103,pv239]) (by decide +kernel)
def pv344639 : PrimeValue := ⟨344639, pr344639⟩
private theorem pr344653 : PrimeCertificate 344653 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv11,pv373]) (by decide +kernel)
def pv344653 : PrimeValue := ⟨344653, pr344653⟩
private theorem pr344683 : PrimeCertificate 344683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv491]) (by decide +kernel)
def pv344683 : PrimeValue := ⟨344683, pr344683⟩
private theorem pr344749 : PrimeCertificate 344749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv28729]) (by decide +kernel)
def pv344749 : PrimeValue := ⟨344749, pr344749⟩
private theorem pr344753 : PrimeCertificate 344753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv743]) (by decide +kernel)
def pv344753 : PrimeValue := ⟨344753, pr344753⟩
private theorem pr344797 : PrimeCertificate 344797 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv59,pv487]) (by decide +kernel)
def pv344797 : PrimeValue := ⟨344797, pr344797⟩
private theorem pr344801 : PrimeCertificate 344801 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv431]) (by decide +kernel)
def pv344801 : PrimeValue := ⟨344801, pr344801⟩
private theorem pr344863 : PrimeCertificate 344863 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv17,pv23]) (by decide +kernel)
def pv344863 : PrimeValue := ⟨344863, pr344863⟩
private theorem pr344873 : PrimeCertificate 344873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv3919]) (by decide +kernel)
def pv344873 : PrimeValue := ⟨344873, pr344873⟩
private theorem pr344887 : PrimeCertificate 344887 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv47,pv1223]) (by decide +kernel)
def pv344887 : PrimeValue := ⟨344887, pr344887⟩
private theorem pr344917 : PrimeCertificate 344917 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv11,pv13,pv67]) (by decide +kernel)
def pv344917 : PrimeValue := ⟨344917, pr344917⟩
private theorem pr344921 : PrimeCertificate 344921 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv8623]) (by decide +kernel)
def pv344921 : PrimeValue := ⟨344921, pr344921⟩
private theorem pr344941 : PrimeCertificate 344941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv5749]) (by decide +kernel)
def pv344941 : PrimeValue := ⟨344941, pr344941⟩
private theorem pr344959 : PrimeCertificate 344959 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv57493]) (by decide +kernel)
def pv344959 : PrimeValue := ⟨344959, pr344959⟩
private theorem pr344987 : PrimeCertificate 344987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv181,pv953]) (by decide +kernel)
def pv344987 : PrimeValue := ⟨344987, pr344987⟩
private theorem pr345001 : PrimeCertificate 345001 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv23]) (by decide +kernel)
def pv345001 : PrimeValue := ⟨345001, pr345001⟩
private theorem pr345011 : PrimeCertificate 345011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv34501]) (by decide +kernel)
def pv345011 : PrimeValue := ⟨345011, pr345011⟩
private theorem pr345047 : PrimeCertificate 345047 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv23,pv577]) (by decide +kernel)
def pv345047 : PrimeValue := ⟨345047, pr345047⟩
private theorem pr345133 : PrimeCertificate 345133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv9587]) (by decide +kernel)
def pv345133 : PrimeValue := ⟨345133, pr345133⟩
private theorem pr345139 : PrimeCertificate 345139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv41,pv61]) (by decide +kernel)
def pv345139 : PrimeValue := ⟨345139, pr345139⟩
private theorem pr345181 : PrimeCertificate 345181 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv11,pv523]) (by decide +kernel)
def pv345181 : PrimeValue := ⟨345181, pr345181⟩
private theorem pr345193 : PrimeCertificate 345193 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv757]) (by decide +kernel)
def pv345193 : PrimeValue := ⟨345193, pr345193⟩
private theorem pr345263 : PrimeCertificate 345263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv47,pv3673]) (by decide +kernel)
def pv345263 : PrimeValue := ⟨345263, pr345263⟩
private theorem pr345307 : PrimeCertificate 345307 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv19,pv233]) (by decide +kernel)
def pv345307 : PrimeValue := ⟨345307, pr345307⟩
private theorem pr345379 : PrimeCertificate 345379 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv11,pv5233]) (by decide +kernel)
def pv345379 : PrimeValue := ⟨345379, pr345379⟩
private theorem pr345413 : PrimeCertificate 345413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv86353]) (by decide +kernel)
def pv345413 : PrimeValue := ⟨345413, pr345413⟩
private theorem pr345451 : PrimeCertificate 345451 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv47]) (by decide +kernel)
def pv345451 : PrimeValue := ⟨345451, pr345451⟩
private theorem pr345463 : PrimeCertificate 345463 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv43,pv103]) (by decide +kernel)
def pv345463 : PrimeValue := ⟨345463, pr345463⟩
private theorem pr345473 : PrimeCertificate 345473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2699]) (by decide +kernel)
def pv345473 : PrimeValue := ⟨345473, pr345473⟩
private theorem pr345479 : PrimeCertificate 345479 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv24677]) (by decide +kernel)
def pv345479 : PrimeValue := ⟨345479, pr345479⟩
private theorem pr345511 : PrimeCertificate 345511 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv349]) (by decide +kernel)
def pv345511 : PrimeValue := ⟨345511, pr345511⟩
private theorem pr345517 : PrimeCertificate 345517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv28793]) (by decide +kernel)
def pv345517 : PrimeValue := ⟨345517, pr345517⟩
private theorem pr345533 : PrimeCertificate 345533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv7853]) (by decide +kernel)
def pv345533 : PrimeValue := ⟨345533, pr345533⟩
private theorem pr345547 : PrimeCertificate 345547 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv79]) (by decide +kernel)
def pv345547 : PrimeValue := ⟨345547, pr345547⟩
private theorem pr345577 : PrimeCertificate 345577 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv17]) (by decide +kernel)
def pv345577 : PrimeValue := ⟨345577, pr345577⟩
private theorem pr345581 : PrimeCertificate 345581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv37,pv467]) (by decide +kernel)
def pv345581 : PrimeValue := ⟨345581, pr345581⟩
private theorem pr345599 : PrimeCertificate 345599 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv23,pv683]) (by decide +kernel)
def pv345599 : PrimeValue := ⟨345599, pr345599⟩
private theorem pr345601 : PrimeCertificate 345601 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv345601 : PrimeValue := ⟨345601, pr345601⟩
private theorem pr345607 : PrimeCertificate 345607 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv57601]) (by decide +kernel)
def pv345607 : PrimeValue := ⟨345607, pr345607⟩
private theorem pr345637 : PrimeCertificate 345637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv9601]) (by decide +kernel)
def pv345637 : PrimeValue := ⟨345637, pr345637⟩
private theorem pr345643 : PrimeCertificate 345643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv5237]) (by decide +kernel)
def pv345643 : PrimeValue := ⟨345643, pr345643⟩
private theorem pr345647 : PrimeCertificate 345647 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv3527]) (by decide +kernel)
def pv345647 : PrimeValue := ⟨345647, pr345647⟩
private theorem pr345689 : PrimeCertificate 345689 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv6173]) (by decide +kernel)
def pv345689 : PrimeValue := ⟨345689, pr345689⟩
private theorem pr345701 : PrimeCertificate 345701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv3457]) (by decide +kernel)
def pv345701 : PrimeValue := ⟨345701, pr345701⟩
private theorem pr345707 : PrimeCertificate 345707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv172853]) (by decide +kernel)
def pv345707 : PrimeValue := ⟨345707, pr345707⟩
private theorem pr345727 : PrimeCertificate 345727 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19207]) (by decide +kernel)
def pv345727 : PrimeValue := ⟨345727, pr345727⟩
private theorem pr345731 : PrimeCertificate 345731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv449]) (by decide +kernel)
def pv345731 : PrimeValue := ⟨345731, pr345731⟩
private theorem pr345739 : PrimeCertificate 345739 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv29,pv1987]) (by decide +kernel)
def pv345739 : PrimeValue := ⟨345739, pr345739⟩
private theorem pr345749 : PrimeCertificate 345749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv61,pv109]) (by decide +kernel)
def pv345749 : PrimeValue := ⟨345749, pr345749⟩
private theorem pr345757 : PrimeCertificate 345757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv28813]) (by decide +kernel)
def pv345757 : PrimeValue := ⟨345757, pr345757⟩
private theorem pr345769 : PrimeCertificate 345769 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv14407]) (by decide +kernel)
def pv345769 : PrimeValue := ⟨345769, pr345769⟩
private theorem pr345791 : PrimeCertificate 345791 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv151,pv229]) (by decide +kernel)
def pv345791 : PrimeValue := ⟨345791, pr345791⟩
private theorem pr345811 : PrimeCertificate 345811 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11527]) (by decide +kernel)
def pv345811 : PrimeValue := ⟨345811, pr345811⟩
private theorem pr345817 : PrimeCertificate 345817 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1601]) (by decide +kernel)
def pv345817 : PrimeValue := ⟨345817, pr345817⟩
private theorem pr345869 : PrimeCertificate 345869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv86467]) (by decide +kernel)
def pv345869 : PrimeValue := ⟨345869, pr345869⟩
private theorem pr345881 : PrimeCertificate 345881 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv8647]) (by decide +kernel)
def pv345881 : PrimeValue := ⟨345881, pr345881⟩
private theorem pr345887 : PrimeCertificate 345887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv163,pv1061]) (by decide +kernel)
def pv345887 : PrimeValue := ⟨345887, pr345887⟩
private theorem pr345889 : PrimeCertificate 345889 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv1201]) (by decide +kernel)
def pv345889 : PrimeValue := ⟨345889, pr345889⟩
private theorem pr345923 : PrimeCertificate 345923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv257,pv673]) (by decide +kernel)
def pv345923 : PrimeValue := ⟨345923, pr345923⟩
private theorem pr345953 : PrimeCertificate 345953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv569]) (by decide +kernel)
def pv345953 : PrimeValue := ⟨345953, pr345953⟩
private theorem pr345979 : PrimeCertificate 345979 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv43,pv149]) (by decide +kernel)
def pv345979 : PrimeValue := ⟨345979, pr345979⟩
private theorem pr345997 : PrimeCertificate 345997 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv1373]) (by decide +kernel)
def pv345997 : PrimeValue := ⟨345997, pr345997⟩
private theorem pr346043 : PrimeCertificate 346043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv173021]) (by decide +kernel)
def pv346043 : PrimeValue := ⟨346043, pr346043⟩
private theorem pr346051 : PrimeCertificate 346051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv769]) (by decide +kernel)
def pv346051 : PrimeValue := ⟨346051, pr346051⟩
private theorem pr346207 : PrimeCertificate 346207 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv8243]) (by decide +kernel)
def pv346207 : PrimeValue := ⟨346207, pr346207⟩
private theorem pr346217 : PrimeCertificate 346217 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv3329]) (by decide +kernel)
def pv346217 : PrimeValue := ⟨346217, pr346217⟩
private theorem pr346277 : PrimeCertificate 346277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv83,pv149]) (by decide +kernel)
def pv346277 : PrimeValue := ⟨346277, pr346277⟩
private theorem pr346303 : PrimeCertificate 346303 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv53]) (by decide +kernel)
def pv346303 : PrimeValue := ⟨346303, pr346303⟩
private theorem pr346331 : PrimeCertificate 346331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv59,pv587]) (by decide +kernel)
def pv346331 : PrimeValue := ⟨346331, pr346331⟩
private theorem pr346349 : PrimeCertificate 346349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv86587]) (by decide +kernel)
def pv346349 : PrimeValue := ⟨346349, pr346349⟩
private theorem pr346369 : PrimeCertificate 346369 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv11,pv41]) (by decide +kernel)
def pv346369 : PrimeValue := ⟨346369, pr346369⟩
private theorem pr346391 : PrimeCertificate 346391 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv11,pv47,pv67]) (by decide +kernel)
def pv346391 : PrimeValue := ⟨346391, pr346391⟩
private theorem pr346397 : PrimeCertificate 346397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv86599]) (by decide +kernel)
def pv346397 : PrimeValue := ⟨346397, pr346397⟩
private theorem pr346429 : PrimeCertificate 346429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv9623]) (by decide +kernel)
def pv346429 : PrimeValue := ⟨346429, pr346429⟩
private theorem pr346433 : PrimeCertificate 346433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5413]) (by decide +kernel)
def pv346433 : PrimeValue := ⟨346433, pr346433⟩
private theorem pr346439 : PrimeCertificate 346439 :=
  certifyPrime (q := pv7) (ls := [pv2,pv173219]) (by decide +kernel)
def pv346439 : PrimeValue := ⟨346439, pr346439⟩
private theorem pr346441 : PrimeCertificate 346441 :=
  certifyPrime (q := pv53) (ls := [pv2,pv3,pv5,pv2887]) (by decide +kernel)
def pv346441 : PrimeValue := ⟨346441, pr346441⟩
private theorem pr346447 : PrimeCertificate 346447 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv1013]) (by decide +kernel)
def pv346447 : PrimeValue := ⟨346447, pr346447⟩
private theorem pr346453 : PrimeCertificate 346453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv28871]) (by decide +kernel)
def pv346453 : PrimeValue := ⟨346453, pr346453⟩
private theorem pr346561 : PrimeCertificate 346561 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv346561 : PrimeValue := ⟨346561, pr346561⟩
private theorem pr346589 : PrimeCertificate 346589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv7877]) (by decide +kernel)
def pv346589 : PrimeValue := ⟨346589, pr346589⟩
private theorem pr346639 : PrimeCertificate 346639 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv57773]) (by decide +kernel)
def pv346639 : PrimeValue := ⟨346639, pr346639⟩
private theorem pr346657 : PrimeCertificate 346657 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23,pv157]) (by decide +kernel)
def pv346657 : PrimeValue := ⟨346657, pr346657⟩
private theorem pr346667 : PrimeCertificate 346667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv43,pv139]) (by decide +kernel)
def pv346667 : PrimeValue := ⟨346667, pr346667⟩
private theorem pr346751 : PrimeCertificate 346751 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv19,pv73]) (by decide +kernel)
def pv346751 : PrimeValue := ⟨346751, pr346751⟩
private theorem pr346763 : PrimeCertificate 346763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv13337]) (by decide +kernel)
def pv346763 : PrimeValue := ⟨346763, pr346763⟩
private theorem pr346793 : PrimeCertificate 346793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv67,pv647]) (by decide +kernel)
def pv346793 : PrimeValue := ⟨346793, pr346793⟩
private theorem pr346891 : PrimeCertificate 346891 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv5,pv31,pv373]) (by decide +kernel)
def pv346891 : PrimeValue := ⟨346891, pr346891⟩
private theorem pr346903 : PrimeCertificate 346903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv19,pv179]) (by decide +kernel)
def pv346903 : PrimeValue := ⟨346903, pr346903⟩
private theorem pr346933 : PrimeCertificate 346933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv419]) (by decide +kernel)
def pv346933 : PrimeValue := ⟨346933, pr346933⟩
private theorem pr347003 : PrimeCertificate 347003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv173501]) (by decide +kernel)
def pv347003 : PrimeValue := ⟨347003, pr347003⟩
private theorem pr347041 : PrimeCertificate 347041 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv241]) (by decide +kernel)
def pv347041 : PrimeValue := ⟨347041, pr347041⟩
private theorem pr347129 : PrimeCertificate 347129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43391]) (by decide +kernel)
def pv347129 : PrimeValue := ⟨347129, pr347129⟩
private theorem pr347131 : PrimeCertificate 347131 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv19,pv29]) (by decide +kernel)
def pv347131 : PrimeValue := ⟨347131, pr347131⟩
private theorem pr347143 : PrimeCertificate 347143 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv47,pv1231]) (by decide +kernel)
def pv347143 : PrimeValue := ⟨347143, pr347143⟩
private theorem pr347167 : PrimeCertificate 347167 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv2143]) (by decide +kernel)
def pv347167 : PrimeValue := ⟨347167, pr347167⟩
private theorem pr347173 : PrimeCertificate 347173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv4133]) (by decide +kernel)
def pv347173 : PrimeValue := ⟨347173, pr347173⟩
private theorem pr347183 : PrimeCertificate 347183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv43,pv367]) (by decide +kernel)
def pv347183 : PrimeValue := ⟨347183, pr347183⟩
private theorem pr347197 : PrimeCertificate 347197 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv28933]) (by decide +kernel)
def pv347197 : PrimeValue := ⟨347197, pr347197⟩
private theorem pr347201 : PrimeCertificate 347201 :=
  certifyPrime (q := pv41) (ls := [pv2,pv5,pv7,pv31]) (by decide +kernel)
def pv347201 : PrimeValue := ⟨347201, pr347201⟩
private theorem pr347209 : PrimeCertificate 347209 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv17,pv23,pv37]) (by decide +kernel)
def pv347209 : PrimeValue := ⟨347209, pr347209⟩
private theorem pr347233 : PrimeCertificate 347233 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv3617]) (by decide +kernel)
def pv347233 : PrimeValue := ⟨347233, pr347233⟩
private theorem pr347287 : PrimeCertificate 347287 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv57881]) (by decide +kernel)
def pv347287 : PrimeValue := ⟨347287, pr347287⟩
private theorem pr347329 : PrimeCertificate 347329 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv67]) (by decide +kernel)
def pv347329 : PrimeValue := ⟨347329, pr347329⟩
private theorem pr347411 : PrimeCertificate 347411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv709]) (by decide +kernel)
def pv347411 : PrimeValue := ⟨347411, pr347411⟩
private theorem pr347437 : PrimeCertificate 347437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3217]) (by decide +kernel)
def pv347437 : PrimeValue := ⟨347437, pr347437⟩
private theorem pr347489 : PrimeCertificate 347489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv10859]) (by decide +kernel)
def pv347489 : PrimeValue := ⟨347489, pr347489⟩
private theorem pr347519 : PrimeCertificate 347519 :=
  certifyPrime (q := pv7) (ls := [pv2,pv47,pv3697]) (by decide +kernel)
def pv347519 : PrimeValue := ⟨347519, pr347519⟩
private theorem pr347539 : PrimeCertificate 347539 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv57923]) (by decide +kernel)
def pv347539 : PrimeValue := ⟨347539, pr347539⟩
private theorem pr347561 : PrimeCertificate 347561 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv8689]) (by decide +kernel)
def pv347561 : PrimeValue := ⟨347561, pr347561⟩
private theorem pr347563 : PrimeCertificate 347563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19309]) (by decide +kernel)
def pv347563 : PrimeValue := ⟨347563, pr347563⟩
private theorem pr347609 : PrimeCertificate 347609 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43451]) (by decide +kernel)
def pv347609 : PrimeValue := ⟨347609, pr347609⟩
private theorem pr347621 : PrimeCertificate 347621 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv13,pv191]) (by decide +kernel)
def pv347621 : PrimeValue := ⟨347621, pr347621⟩
private theorem pr347629 : PrimeCertificate 347629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv59,pv491]) (by decide +kernel)
def pv347629 : PrimeValue := ⟨347629, pr347629⟩
private theorem pr347651 : PrimeCertificate 347651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv409]) (by decide +kernel)
def pv347651 : PrimeValue := ⟨347651, pr347651⟩
private theorem pr347707 : PrimeCertificate 347707 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv47,pv137]) (by decide +kernel)
def pv347707 : PrimeValue := ⟨347707, pr347707⟩
private theorem pr347717 : PrimeCertificate 347717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv86929]) (by decide +kernel)
def pv347717 : PrimeValue := ⟨347717, pr347717⟩
private theorem pr347773 : PrimeCertificate 347773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv73,pv397]) (by decide +kernel)
def pv347773 : PrimeValue := ⟨347773, pr347773⟩
private theorem pr347801 : PrimeCertificate 347801 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv37,pv47]) (by decide +kernel)
def pv347801 : PrimeValue := ⟨347801, pr347801⟩
private theorem pr347813 : PrimeCertificate 347813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89,pv977]) (by decide +kernel)
def pv347813 : PrimeValue := ⟨347813, pr347813⟩
private theorem pr347887 : PrimeCertificate 347887 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv11,pv251]) (by decide +kernel)
def pv347887 : PrimeValue := ⟨347887, pr347887⟩
private theorem pr347891 : PrimeCertificate 347891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv1831]) (by decide +kernel)
def pv347891 : PrimeValue := ⟨347891, pr347891⟩
private theorem pr347899 : PrimeCertificate 347899 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv2521]) (by decide +kernel)
def pv347899 : PrimeValue := ⟨347899, pr347899⟩
private theorem pr347933 : PrimeCertificate 347933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv6691]) (by decide +kernel)
def pv347933 : PrimeValue := ⟨347933, pr347933⟩
private theorem pr347957 : PrimeCertificate 347957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv17,pv43]) (by decide +kernel)
def pv347957 : PrimeValue := ⟨347957, pr347957⟩
private theorem pr347969 : PrimeCertificate 347969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5437]) (by decide +kernel)
def pv347969 : PrimeValue := ⟨347969, pr347969⟩
private theorem pr347981 : PrimeCertificate 347981 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv127,pv137]) (by decide +kernel)
def pv347981 : PrimeValue := ⟨347981, pr347981⟩
private theorem pr347983 : PrimeCertificate 347983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv59,pv983]) (by decide +kernel)
def pv347983 : PrimeValue := ⟨347983, pr347983⟩
private theorem pr347989 : PrimeCertificate 347989 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv47,pv617]) (by decide +kernel)
def pv347989 : PrimeValue := ⟨347989, pr347989⟩
private theorem pr348001 : PrimeCertificate 348001 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv29]) (by decide +kernel)
def pv348001 : PrimeValue := ⟨348001, pr348001⟩
private theorem pr348017 : PrimeCertificate 348017 :=
  certifyPrime (q := pv3) (ls := [pv2,pv21751]) (by decide +kernel)
def pv348017 : PrimeValue := ⟨348017, pr348017⟩
private theorem pr348043 : PrimeCertificate 348043 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv43,pv71]) (by decide +kernel)
def pv348043 : PrimeValue := ⟨348043, pr348043⟩
private theorem pr348053 : PrimeCertificate 348053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv87013]) (by decide +kernel)
def pv348053 : PrimeValue := ⟨348053, pr348053⟩
private theorem pr348163 : PrimeCertificate 348163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv58027]) (by decide +kernel)
def pv348163 : PrimeValue := ⟨348163, pr348163⟩
private theorem pr348217 : PrimeCertificate 348217 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv1319]) (by decide +kernel)
def pv348217 : PrimeValue := ⟨348217, pr348217⟩
private theorem pr348241 : PrimeCertificate 348241 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv1451]) (by decide +kernel)
def pv348241 : PrimeValue := ⟨348241, pr348241⟩
private theorem pr348269 : PrimeCertificate 348269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv83,pv1049]) (by decide +kernel)
def pv348269 : PrimeValue := ⟨348269, pr348269⟩
private theorem pr348307 : PrimeCertificate 348307 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv8293]) (by decide +kernel)
def pv348307 : PrimeValue := ⟨348307, pr348307⟩
private theorem pr348323 : PrimeCertificate 348323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv13397]) (by decide +kernel)
def pv348323 : PrimeValue := ⟨348323, pr348323⟩
private theorem pr348353 : PrimeCertificate 348353 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5443]) (by decide +kernel)
def pv348353 : PrimeValue := ⟨348353, pr348353⟩
private theorem pr348367 : PrimeCertificate 348367 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv58061]) (by decide +kernel)
def pv348367 : PrimeValue := ⟨348367, pr348367⟩
private theorem pr348437 : PrimeCertificate 348437 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv7919]) (by decide +kernel)
def pv348437 : PrimeValue := ⟨348437, pr348437⟩
private theorem pr348443 : PrimeCertificate 348443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv174221]) (by decide +kernel)
def pv348443 : PrimeValue := ⟨348443, pr348443⟩
private theorem pr348461 : PrimeCertificate 348461 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv19,pv131]) (by decide +kernel)
def pv348461 : PrimeValue := ⟨348461, pr348461⟩
private theorem pr348487 : PrimeCertificate 348487 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv241]) (by decide +kernel)
def pv348487 : PrimeValue := ⟨348487, pr348487⟩
private theorem pr348527 : PrimeCertificate 348527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv174263]) (by decide +kernel)
def pv348527 : PrimeValue := ⟨348527, pr348527⟩
private theorem pr348547 : PrimeCertificate 348547 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv5281]) (by decide +kernel)
def pv348547 : PrimeValue := ⟨348547, pr348547⟩
private theorem pr348553 : PrimeCertificate 348553 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv47,pv103]) (by decide +kernel)
def pv348553 : PrimeValue := ⟨348553, pr348553⟩
private theorem pr348563 : PrimeCertificate 348563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv174281]) (by decide +kernel)
def pv348563 : PrimeValue := ⟨348563, pr348563⟩
private theorem pr348617 : PrimeCertificate 348617 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43577]) (by decide +kernel)
def pv348617 : PrimeValue := ⟨348617, pr348617⟩
private theorem pr348629 : PrimeCertificate 348629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv12451]) (by decide +kernel)
def pv348629 : PrimeValue := ⟨348629, pr348629⟩
private theorem pr348643 : PrimeCertificate 348643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv2767]) (by decide +kernel)
def pv348643 : PrimeValue := ⟨348643, pr348643⟩
private theorem pr348731 : PrimeCertificate 348731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv43,pv811]) (by decide +kernel)
def pv348731 : PrimeValue := ⟨348731, pr348731⟩
private theorem pr348757 : PrimeCertificate 348757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29063]) (by decide +kernel)
def pv348757 : PrimeValue := ⟨348757, pr348757⟩
private theorem pr348769 : PrimeCertificate 348769 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv173]) (by decide +kernel)
def pv348769 : PrimeValue := ⟨348769, pr348769⟩
private theorem pr348779 : PrimeCertificate 348779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv174389]) (by decide +kernel)
def pv348779 : PrimeValue := ⟨348779, pr348779⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
