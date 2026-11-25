/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table025
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table025.pv62299
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table005
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table013

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr62299 : PrimeCertificate 62299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3461]) (by decide +kernel)
def pv62299 : PrimeValue := ⟨62299, pr62299⟩
private theorem pr62303 : PrimeCertificate 62303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv31151]) (by decide +kernel)
def pv62303 : PrimeValue := ⟨62303, pr62303⟩
private theorem pr62311 : PrimeCertificate 62311 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv31,pv67]) (by decide +kernel)
def pv62311 : PrimeValue := ⟨62311, pr62311⟩
private theorem pr62323 : PrimeCertificate 62323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv17,pv47]) (by decide +kernel)
def pv62323 : PrimeValue := ⟨62323, pr62323⟩
private theorem pr62327 : PrimeCertificate 62327 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv2833]) (by decide +kernel)
def pv62327 : PrimeValue := ⟨62327, pr62327⟩
private theorem pr62347 : PrimeCertificate 62347 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv10391]) (by decide +kernel)
def pv62347 : PrimeValue := ⟨62347, pr62347⟩
private theorem pr62351 : PrimeCertificate 62351 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv29,pv43]) (by decide +kernel)
def pv62351 : PrimeValue := ⟨62351, pr62351⟩
private theorem pr62383 : PrimeCertificate 62383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv37,pv281]) (by decide +kernel)
def pv62383 : PrimeValue := ⟨62383, pr62383⟩
private theorem pr62401 : PrimeCertificate 62401 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv62401 : PrimeValue := ⟨62401, pr62401⟩
private theorem pr62417 : PrimeCertificate 62417 :=
  certifyPrime (q := pv3) (ls := [pv2,pv47,pv83]) (by decide +kernel)
def pv62417 : PrimeValue := ⟨62417, pr62417⟩
private theorem pr62423 : PrimeCertificate 62423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv59]) (by decide +kernel)
def pv62423 : PrimeValue := ⟨62423, pr62423⟩
private theorem pr62459 : PrimeCertificate 62459 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv17,pv167]) (by decide +kernel)
def pv62459 : PrimeValue := ⟨62459, pr62459⟩
private theorem pr62467 : PrimeCertificate 62467 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv359]) (by decide +kernel)
def pv62467 : PrimeValue := ⟨62467, pr62467⟩
private theorem pr62473 : PrimeCertificate 62473 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv137]) (by decide +kernel)
def pv62473 : PrimeValue := ⟨62473, pr62473⟩
private theorem pr62477 : PrimeCertificate 62477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv15619]) (by decide +kernel)
def pv62477 : PrimeValue := ⟨62477, pr62477⟩
private theorem pr62483 : PrimeCertificate 62483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv4463]) (by decide +kernel)
def pv62483 : PrimeValue := ⟨62483, pr62483⟩
private theorem pr62497 : PrimeCertificate 62497 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv7,pv31]) (by decide +kernel)
def pv62497 : PrimeValue := ⟨62497, pr62497⟩
private theorem pr62501 : PrimeCertificate 62501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5]) (by decide +kernel)
def pv62501 : PrimeValue := ⟨62501, pr62501⟩
private theorem pr62507 : PrimeCertificate 62507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31253]) (by decide +kernel)
def pv62507 : PrimeValue := ⟨62507, pr62507⟩
private theorem pr62533 : PrimeCertificate 62533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv193]) (by decide +kernel)
def pv62533 : PrimeValue := ⟨62533, pr62533⟩
private theorem pr62539 : PrimeCertificate 62539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1489]) (by decide +kernel)
def pv62539 : PrimeValue := ⟨62539, pr62539⟩
private theorem pr62549 : PrimeCertificate 62549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv823]) (by decide +kernel)
def pv62549 : PrimeValue := ⟨62549, pr62549⟩
private theorem pr62563 : PrimeCertificate 62563 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv10427]) (by decide +kernel)
def pv62563 : PrimeValue := ⟨62563, pr62563⟩
private theorem pr62581 : PrimeCertificate 62581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv149]) (by decide +kernel)
def pv62581 : PrimeValue := ⟨62581, pr62581⟩
private theorem pr62591 : PrimeCertificate 62591 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv569]) (by decide +kernel)
def pv62591 : PrimeValue := ⟨62591, pr62591⟩
private theorem pr62597 : PrimeCertificate 62597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv15649]) (by decide +kernel)
def pv62597 : PrimeValue := ⟨62597, pr62597⟩
private theorem pr62603 : PrimeCertificate 62603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv113,pv277]) (by decide +kernel)
def pv62603 : PrimeValue := ⟨62603, pr62603⟩
private theorem pr62617 : PrimeCertificate 62617 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2609]) (by decide +kernel)
def pv62617 : PrimeValue := ⟨62617, pr62617⟩
private theorem pr62627 : PrimeCertificate 62627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv173,pv181]) (by decide +kernel)
def pv62627 : PrimeValue := ⟨62627, pr62627⟩
private theorem pr62633 : PrimeCertificate 62633 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7829]) (by decide +kernel)
def pv62633 : PrimeValue := ⟨62633, pr62633⟩
private theorem pr62639 : PrimeCertificate 62639 :=
  certifyPrime (q := pv11) (ls := [pv2,pv31319]) (by decide +kernel)
def pv62639 : PrimeValue := ⟨62639, pr62639⟩
private theorem pr62653 : PrimeCertificate 62653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv227]) (by decide +kernel)
def pv62653 : PrimeValue := ⟨62653, pr62653⟩
private theorem pr62659 : PrimeCertificate 62659 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv59]) (by decide +kernel)
def pv62659 : PrimeValue := ⟨62659, pr62659⟩
private theorem pr62683 : PrimeCertificate 62683 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31,pv337]) (by decide +kernel)
def pv62683 : PrimeValue := ⟨62683, pr62683⟩
private theorem pr62687 : PrimeCertificate 62687 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv2411]) (by decide +kernel)
def pv62687 : PrimeValue := ⟨62687, pr62687⟩
private theorem pr62701 : PrimeCertificate 62701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv19]) (by decide +kernel)
def pv62701 : PrimeValue := ⟨62701, pr62701⟩
private theorem pr62723 : PrimeCertificate 62723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv2851]) (by decide +kernel)
def pv62723 : PrimeValue := ⟨62723, pr62723⟩
private theorem pr62731 : PrimeCertificate 62731 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv17,pv41]) (by decide +kernel)
def pv62731 : PrimeValue := ⟨62731, pr62731⟩
private theorem pr62743 : PrimeCertificate 62743 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv10457]) (by decide +kernel)
def pv62743 : PrimeValue := ⟨62743, pr62743⟩
private theorem pr62753 : PrimeCertificate 62753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv53]) (by decide +kernel)
def pv62753 : PrimeValue := ⟨62753, pr62753⟩
private theorem pr62761 : PrimeCertificate 62761 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv523]) (by decide +kernel)
def pv62761 : PrimeValue := ⟨62761, pr62761⟩
private theorem pr62773 : PrimeCertificate 62773 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv5231]) (by decide +kernel)
def pv62773 : PrimeValue := ⟨62773, pr62773⟩
private theorem pr62791 : PrimeCertificate 62791 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv13,pv23]) (by decide +kernel)
def pv62791 : PrimeValue := ⟨62791, pr62791⟩
private theorem pr62801 : PrimeCertificate 62801 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv157]) (by decide +kernel)
def pv62801 : PrimeValue := ⟨62801, pr62801⟩
private theorem pr62819 : PrimeCertificate 62819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv641]) (by decide +kernel)
def pv62819 : PrimeValue := ⟨62819, pr62819⟩
private theorem pr62827 : PrimeCertificate 62827 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37,pv283]) (by decide +kernel)
def pv62827 : PrimeValue := ⟨62827, pr62827⟩
private theorem pr62851 : PrimeCertificate 62851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv419]) (by decide +kernel)
def pv62851 : PrimeValue := ⟨62851, pr62851⟩
private theorem pr62861 : PrimeCertificate 62861 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv449]) (by decide +kernel)
def pv62861 : PrimeValue := ⟨62861, pr62861⟩
private theorem pr62869 : PrimeCertificate 62869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv31]) (by decide +kernel)
def pv62869 : PrimeValue := ⟨62869, pr62869⟩
private theorem pr62873 : PrimeCertificate 62873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv271]) (by decide +kernel)
def pv62873 : PrimeValue := ⟨62873, pr62873⟩
private theorem pr62897 : PrimeCertificate 62897 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3931]) (by decide +kernel)
def pv62897 : PrimeValue := ⟨62897, pr62897⟩
private theorem pr62903 : PrimeCertificate 62903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv4493]) (by decide +kernel)
def pv62903 : PrimeValue := ⟨62903, pr62903⟩
private theorem pr62921 : PrimeCertificate 62921 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv11,pv13]) (by decide +kernel)
def pv62921 : PrimeValue := ⟨62921, pr62921⟩
private theorem pr62927 : PrimeCertificate 62927 :=
  certifyPrime (q := pv5) (ls := [pv2,pv73,pv431]) (by decide +kernel)
def pv62927 : PrimeValue := ⟨62927, pr62927⟩
private theorem pr62929 : PrimeCertificate 62929 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv19,pv23]) (by decide +kernel)
def pv62929 : PrimeValue := ⟨62929, pr62929⟩
private theorem pr62939 : PrimeCertificate 62939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31469]) (by decide +kernel)
def pv62939 : PrimeValue := ⟨62939, pr62939⟩
private theorem pr62969 : PrimeCertificate 62969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv463]) (by decide +kernel)
def pv62969 : PrimeValue := ⟨62969, pr62969⟩
private theorem pr62971 : PrimeCertificate 62971 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv2099]) (by decide +kernel)
def pv62971 : PrimeValue := ⟨62971, pr62971⟩
private theorem pr62981 : PrimeCertificate 62981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv47,pv67]) (by decide +kernel)
def pv62981 : PrimeValue := ⟨62981, pr62981⟩
private theorem pr62983 : PrimeCertificate 62983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3499]) (by decide +kernel)
def pv62983 : PrimeValue := ⟨62983, pr62983⟩
private theorem pr62987 : PrimeCertificate 62987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv409]) (by decide +kernel)
def pv62987 : PrimeValue := ⟨62987, pr62987⟩
private theorem pr62989 : PrimeCertificate 62989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv181]) (by decide +kernel)
def pv62989 : PrimeValue := ⟨62989, pr62989⟩
private theorem pr63029 : PrimeCertificate 63029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv2251]) (by decide +kernel)
def pv63029 : PrimeValue := ⟨63029, pr63029⟩
private theorem pr63031 : PrimeCertificate 63031 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv191]) (by decide +kernel)
def pv63031 : PrimeValue := ⟨63031, pr63031⟩
private theorem pr63059 : PrimeCertificate 63059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv769]) (by decide +kernel)
def pv63059 : PrimeValue := ⟨63059, pr63059⟩
private theorem pr63067 : PrimeCertificate 63067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv457]) (by decide +kernel)
def pv63067 : PrimeValue := ⟨63067, pr63067⟩
private theorem pr63073 : PrimeCertificate 63073 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv73]) (by decide +kernel)
def pv63073 : PrimeValue := ⟨63073, pr63073⟩
private theorem pr63079 : PrimeCertificate 63079 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv10513]) (by decide +kernel)
def pv63079 : PrimeValue := ⟨63079, pr63079⟩
private theorem pr63097 : PrimeCertificate 63097 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv239]) (by decide +kernel)
def pv63097 : PrimeValue := ⟨63097, pr63097⟩
private theorem pr63103 : PrimeCertificate 63103 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv809]) (by decide +kernel)
def pv63103 : PrimeValue := ⟨63103, pr63103⟩
private theorem pr63113 : PrimeCertificate 63113 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv23]) (by decide +kernel)
def pv63113 : PrimeValue := ⟨63113, pr63113⟩
private theorem pr63127 : PrimeCertificate 63127 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv167]) (by decide +kernel)
def pv63127 : PrimeValue := ⟨63127, pr63127⟩
private theorem pr63131 : PrimeCertificate 63131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv59,pv107]) (by decide +kernel)
def pv63131 : PrimeValue := ⟨63131, pr63131⟩
private theorem pr63149 : PrimeCertificate 63149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv15787]) (by decide +kernel)
def pv63149 : PrimeValue := ⟨63149, pr63149⟩
private theorem pr63179 : PrimeCertificate 63179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv1019]) (by decide +kernel)
def pv63179 : PrimeValue := ⟨63179, pr63179⟩
private theorem pr63197 : PrimeCertificate 63197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv37,pv61]) (by decide +kernel)
def pv63197 : PrimeValue := ⟨63197, pr63197⟩
private theorem pr63199 : PrimeCertificate 63199 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv3511]) (by decide +kernel)
def pv63199 : PrimeValue := ⟨63199, pr63199⟩
private theorem pr63211 : PrimeCertificate 63211 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv43]) (by decide +kernel)
def pv63211 : PrimeValue := ⟨63211, pr63211⟩
private theorem pr63241 : PrimeCertificate 63241 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv17,pv31]) (by decide +kernel)
def pv63241 : PrimeValue := ⟨63241, pr63241⟩
private theorem pr63247 : PrimeCertificate 63247 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv83,pv127]) (by decide +kernel)
def pv63247 : PrimeValue := ⟨63247, pr63247⟩
private theorem pr63277 : PrimeCertificate 63277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5273]) (by decide +kernel)
def pv63277 : PrimeValue := ⟨63277, pr63277⟩
private theorem pr63281 : PrimeCertificate 63281 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv7,pv113]) (by decide +kernel)
def pv63281 : PrimeValue := ⟨63281, pr63281⟩
private theorem pr63299 : PrimeCertificate 63299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31649]) (by decide +kernel)
def pv63299 : PrimeValue := ⟨63299, pr63299⟩
private theorem pr63313 : PrimeCertificate 63313 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1319]) (by decide +kernel)
def pv63313 : PrimeValue := ⟨63313, pr63313⟩
private theorem pr63317 : PrimeCertificate 63317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv1439]) (by decide +kernel)
def pv63317 : PrimeValue := ⟨63317, pr63317⟩
private theorem pr63331 : PrimeCertificate 63331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv2111]) (by decide +kernel)
def pv63331 : PrimeValue := ⟨63331, pr63331⟩
private theorem pr63337 : PrimeCertificate 63337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv29]) (by decide +kernel)
def pv63337 : PrimeValue := ⟨63337, pr63337⟩
private theorem pr63347 : PrimeCertificate 63347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv1667]) (by decide +kernel)
def pv63347 : PrimeValue := ⟨63347, pr63347⟩
private theorem pr63353 : PrimeCertificate 63353 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7919]) (by decide +kernel)
def pv63353 : PrimeValue := ⟨63353, pr63353⟩
private theorem pr63361 : PrimeCertificate 63361 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv63361 : PrimeValue := ⟨63361, pr63361⟩
private theorem pr63367 : PrimeCertificate 63367 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv59,pv179]) (by decide +kernel)
def pv63367 : PrimeValue := ⟨63367, pr63367⟩
private theorem pr63377 : PrimeCertificate 63377 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv233]) (by decide +kernel)
def pv63377 : PrimeValue := ⟨63377, pr63377⟩
private theorem pr63389 : PrimeCertificate 63389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv23,pv53]) (by decide +kernel)
def pv63389 : PrimeValue := ⟨63389, pr63389⟩
private theorem pr63391 : PrimeCertificate 63391 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv2113]) (by decide +kernel)
def pv63391 : PrimeValue := ⟨63391, pr63391⟩
private theorem pr63397 : PrimeCertificate 63397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv587]) (by decide +kernel)
def pv63397 : PrimeValue := ⟨63397, pr63397⟩
private theorem pr63409 : PrimeCertificate 63409 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1321]) (by decide +kernel)
def pv63409 : PrimeValue := ⟨63409, pr63409⟩
private theorem pr63419 : PrimeCertificate 63419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv857]) (by decide +kernel)
def pv63419 : PrimeValue := ⟨63419, pr63419⟩
private theorem pr63421 : PrimeCertificate 63421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv151]) (by decide +kernel)
def pv63421 : PrimeValue := ⟨63421, pr63421⟩
private theorem pr63439 : PrimeCertificate 63439 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv97,pv109]) (by decide +kernel)
def pv63439 : PrimeValue := ⟨63439, pr63439⟩
private theorem pr63443 : PrimeCertificate 63443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31721]) (by decide +kernel)
def pv63443 : PrimeValue := ⟨63443, pr63443⟩
private theorem pr63463 : PrimeCertificate 63463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv1511]) (by decide +kernel)
def pv63463 : PrimeValue := ⟨63463, pr63463⟩
private theorem pr63467 : PrimeCertificate 63467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv2441]) (by decide +kernel)
def pv63467 : PrimeValue := ⟨63467, pr63467⟩
private theorem pr63473 : PrimeCertificate 63473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3967]) (by decide +kernel)
def pv63473 : PrimeValue := ⟨63473, pr63473⟩
private theorem pr63487 : PrimeCertificate 63487 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv3527]) (by decide +kernel)
def pv63487 : PrimeValue := ⟨63487, pr63487⟩
private theorem pr63493 : PrimeCertificate 63493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv13,pv37]) (by decide +kernel)
def pv63493 : PrimeValue := ⟨63493, pr63493⟩
private theorem pr63499 : PrimeCertificate 63499 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv557]) (by decide +kernel)
def pv63499 : PrimeValue := ⟨63499, pr63499⟩
private theorem pr63521 : PrimeCertificate 63521 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv397]) (by decide +kernel)
def pv63521 : PrimeValue := ⟨63521, pr63521⟩
private theorem pr63527 : PrimeCertificate 63527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv1381]) (by decide +kernel)
def pv63527 : PrimeValue := ⟨63527, pr63527⟩
private theorem pr63533 : PrimeCertificate 63533 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv2269]) (by decide +kernel)
def pv63533 : PrimeValue := ⟨63533, pr63533⟩
private theorem pr63541 : PrimeCertificate 63541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv353]) (by decide +kernel)
def pv63541 : PrimeValue := ⟨63541, pr63541⟩
private theorem pr63559 : PrimeCertificate 63559 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv107]) (by decide +kernel)
def pv63559 : PrimeValue := ⟨63559, pr63559⟩
private theorem pr63577 : PrimeCertificate 63577 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv883]) (by decide +kernel)
def pv63577 : PrimeValue := ⟨63577, pr63577⟩
private theorem pr63587 : PrimeCertificate 63587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31793]) (by decide +kernel)
def pv63587 : PrimeValue := ⟨63587, pr63587⟩
private theorem pr63589 : PrimeCertificate 63589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv757]) (by decide +kernel)
def pv63589 : PrimeValue := ⟨63589, pr63589⟩
private theorem pr63599 : PrimeCertificate 63599 :=
  certifyPrime (q := pv7) (ls := [pv2,pv31799]) (by decide +kernel)
def pv63599 : PrimeValue := ⟨63599, pr63599⟩
private theorem pr63601 : PrimeCertificate 63601 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv53]) (by decide +kernel)
def pv63601 : PrimeValue := ⟨63601, pr63601⟩
private theorem pr63607 : PrimeCertificate 63607 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv10601]) (by decide +kernel)
def pv63607 : PrimeValue := ⟨63607, pr63607⟩
private theorem pr63611 : PrimeCertificate 63611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv6361]) (by decide +kernel)
def pv63611 : PrimeValue := ⟨63611, pr63611⟩
private theorem pr63617 : PrimeCertificate 63617 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv71]) (by decide +kernel)
def pv63617 : PrimeValue := ⟨63617, pr63617⟩
private theorem pr63629 : PrimeCertificate 63629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv15907]) (by decide +kernel)
def pv63629 : PrimeValue := ⟨63629, pr63629⟩
private theorem pr63647 : PrimeCertificate 63647 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv263]) (by decide +kernel)
def pv63647 : PrimeValue := ⟨63647, pr63647⟩
private theorem pr63649 : PrimeCertificate 63649 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv17]) (by decide +kernel)
def pv63649 : PrimeValue := ⟨63649, pr63649⟩
private theorem pr63659 : PrimeCertificate 63659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv4547]) (by decide +kernel)
def pv63659 : PrimeValue := ⟨63659, pr63659⟩
private theorem pr63667 : PrimeCertificate 63667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv131]) (by decide +kernel)
def pv63667 : PrimeValue := ⟨63667, pr63667⟩
private theorem pr63671 : PrimeCertificate 63671 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv6367]) (by decide +kernel)
def pv63671 : PrimeValue := ⟨63671, pr63671⟩
private theorem pr63689 : PrimeCertificate 63689 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv419]) (by decide +kernel)
def pv63689 : PrimeValue := ⟨63689, pr63689⟩
private theorem pr63691 : PrimeCertificate 63691 :=
  certifyPrime (q := pv47) (ls := [pv2,pv3,pv5,pv11,pv193]) (by decide +kernel)
def pv63691 : PrimeValue := ⟨63691, pr63691⟩
private theorem pr63697 : PrimeCertificate 63697 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1327]) (by decide +kernel)
def pv63697 : PrimeValue := ⟨63697, pr63697⟩
private theorem pr63703 : PrimeCertificate 63703 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv3539]) (by decide +kernel)
def pv63703 : PrimeValue := ⟨63703, pr63703⟩
private theorem pr63709 : PrimeCertificate 63709 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5309]) (by decide +kernel)
def pv63709 : PrimeValue := ⟨63709, pr63709⟩
private theorem pr63719 : PrimeCertificate 63719 :=
  certifyPrime (q := pv13) (ls := [pv2,pv31859]) (by decide +kernel)
def pv63719 : PrimeValue := ⟨63719, pr63719⟩
private theorem pr63727 : PrimeCertificate 63727 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13,pv19,pv43]) (by decide +kernel)
def pv63727 : PrimeValue := ⟨63727, pr63727⟩
private theorem pr63737 : PrimeCertificate 63737 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv257]) (by decide +kernel)
def pv63737 : PrimeValue := ⟨63737, pr63737⟩
private theorem pr63743 : PrimeCertificate 63743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv29,pv157]) (by decide +kernel)
def pv63743 : PrimeValue := ⟨63743, pr63743⟩
private theorem pr63761 : PrimeCertificate 63761 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv797]) (by decide +kernel)
def pv63761 : PrimeValue := ⟨63761, pr63761⟩
private theorem pr63773 : PrimeCertificate 63773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv107,pv149]) (by decide +kernel)
def pv63773 : PrimeValue := ⟨63773, pr63773⟩
private theorem pr63781 : PrimeCertificate 63781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1063]) (by decide +kernel)
def pv63781 : PrimeValue := ⟨63781, pr63781⟩
private theorem pr63793 : PrimeCertificate 63793 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv443]) (by decide +kernel)
def pv63793 : PrimeValue := ⟨63793, pr63793⟩
private theorem pr63799 : PrimeCertificate 63799 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv31]) (by decide +kernel)
def pv63799 : PrimeValue := ⟨63799, pr63799⟩
private theorem pr63803 : PrimeCertificate 63803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv23,pv73]) (by decide +kernel)
def pv63803 : PrimeValue := ⟨63803, pr63803⟩
private theorem pr63809 : PrimeCertificate 63809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv997]) (by decide +kernel)
def pv63809 : PrimeValue := ⟨63809, pr63809⟩
private theorem pr63823 : PrimeCertificate 63823 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv967]) (by decide +kernel)
def pv63823 : PrimeValue := ⟨63823, pr63823⟩
private theorem pr63839 : PrimeCertificate 63839 :=
  certifyPrime (q := pv29) (ls := [pv2,pv59,pv541]) (by decide +kernel)
def pv63839 : PrimeValue := ⟨63839, pr63839⟩
private theorem pr63841 : PrimeCertificate 63841 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv7,pv19]) (by decide +kernel)
def pv63841 : PrimeValue := ⟨63841, pr63841⟩
private theorem pr63853 : PrimeCertificate 63853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv313]) (by decide +kernel)
def pv63853 : PrimeValue := ⟨63853, pr63853⟩
private theorem pr63857 : PrimeCertificate 63857 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv307]) (by decide +kernel)
def pv63857 : PrimeValue := ⟨63857, pr63857⟩
private theorem pr63863 : PrimeCertificate 63863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv37,pv863]) (by decide +kernel)
def pv63863 : PrimeValue := ⟨63863, pr63863⟩
private theorem pr63901 : PrimeCertificate 63901 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv71]) (by decide +kernel)
def pv63901 : PrimeValue := ⟨63901, pr63901⟩
private theorem pr63907 : PrimeCertificate 63907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv10651]) (by decide +kernel)
def pv63907 : PrimeValue := ⟨63907, pr63907⟩
private theorem pr63913 : PrimeCertificate 63913 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv2663]) (by decide +kernel)
def pv63913 : PrimeValue := ⟨63913, pr63913⟩
private theorem pr63929 : PrimeCertificate 63929 :=
  certifyPrime (q := pv3) (ls := [pv2,pv61,pv131]) (by decide +kernel)
def pv63929 : PrimeValue := ⟨63929, pr63929⟩
private theorem pr63949 : PrimeCertificate 63949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv73]) (by decide +kernel)
def pv63949 : PrimeValue := ⟨63949, pr63949⟩
private theorem pr63977 : PrimeCertificate 63977 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv727]) (by decide +kernel)
def pv63977 : PrimeValue := ⟨63977, pr63977⟩
private theorem pr63997 : PrimeCertificate 63997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5333]) (by decide +kernel)
def pv63997 : PrimeValue := ⟨63997, pr63997⟩
private theorem pr64007 : PrimeCertificate 64007 :=
  certifyPrime (q := pv5) (ls := [pv2,pv32003]) (by decide +kernel)
def pv64007 : PrimeValue := ⟨64007, pr64007⟩
private theorem pr64013 : PrimeCertificate 64013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv1231]) (by decide +kernel)
def pv64013 : PrimeValue := ⟨64013, pr64013⟩
private theorem pr64019 : PrimeCertificate 64019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv32009]) (by decide +kernel)
def pv64019 : PrimeValue := ⟨64019, pr64019⟩
private theorem pr64033 : PrimeCertificate 64033 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv29]) (by decide +kernel)
def pv64033 : PrimeValue := ⟨64033, pr64033⟩
private theorem pr64037 : PrimeCertificate 64037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv2287]) (by decide +kernel)
def pv64037 : PrimeValue := ⟨64037, pr64037⟩
private theorem pr64063 : PrimeCertificate 64063 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv3559]) (by decide +kernel)
def pv64063 : PrimeValue := ⟨64063, pr64063⟩
private theorem pr64067 : PrimeCertificate 64067 :=
  certifyPrime (q := pv5) (ls := [pv2,pv103,pv311]) (by decide +kernel)
def pv64067 : PrimeValue := ⟨64067, pr64067⟩
private theorem pr64081 : PrimeCertificate 64081 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv89]) (by decide +kernel)
def pv64081 : PrimeValue := ⟨64081, pr64081⟩
private theorem pr64091 : PrimeCertificate 64091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv17,pv29]) (by decide +kernel)
def pv64091 : PrimeValue := ⟨64091, pr64091⟩
private theorem pr64109 : PrimeCertificate 64109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv31,pv47]) (by decide +kernel)
def pv64109 : PrimeValue := ⟨64109, pr64109⟩
private theorem pr64123 : PrimeCertificate 64123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv10687]) (by decide +kernel)
def pv64123 : PrimeValue := ⟨64123, pr64123⟩
private theorem pr64151 : PrimeCertificate 64151 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv1283]) (by decide +kernel)
def pv64151 : PrimeValue := ⟨64151, pr64151⟩
private theorem pr64153 : PrimeCertificate 64153 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv64153 : PrimeValue := ⟨64153, pr64153⟩
private theorem pr64157 : PrimeCertificate 64157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv373]) (by decide +kernel)
def pv64157 : PrimeValue := ⟨64157, pr64157⟩
private theorem pr64171 : PrimeCertificate 64171 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv23,pv31]) (by decide +kernel)
def pv64171 : PrimeValue := ⟨64171, pr64171⟩
private theorem pr64187 : PrimeCertificate 64187 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67,pv479]) (by decide +kernel)
def pv64187 : PrimeValue := ⟨64187, pr64187⟩
private theorem pr64189 : PrimeCertificate 64189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1783]) (by decide +kernel)
def pv64189 : PrimeValue := ⟨64189, pr64189⟩
private theorem pr64217 : PrimeCertificate 64217 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv349]) (by decide +kernel)
def pv64217 : PrimeValue := ⟨64217, pr64217⟩
private theorem pr64223 : PrimeCertificate 64223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv163,pv197]) (by decide +kernel)
def pv64223 : PrimeValue := ⟨64223, pr64223⟩
private theorem pr64231 : PrimeCertificate 64231 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv2141]) (by decide +kernel)
def pv64231 : PrimeValue := ⟨64231, pr64231⟩
private theorem pr64237 : PrimeCertificate 64237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53,pv101]) (by decide +kernel)
def pv64237 : PrimeValue := ⟨64237, pr64237⟩
private theorem pr64271 : PrimeCertificate 64271 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv6427]) (by decide +kernel)
def pv64271 : PrimeValue := ⟨64271, pr64271⟩
private theorem pr64279 : PrimeCertificate 64279 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv3571]) (by decide +kernel)
def pv64279 : PrimeValue := ⟨64279, pr64279⟩
private theorem pr64283 : PrimeCertificate 64283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv32141]) (by decide +kernel)
def pv64283 : PrimeValue := ⟨64283, pr64283⟩
private theorem pr64301 : PrimeCertificate 64301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv643]) (by decide +kernel)
def pv64301 : PrimeValue := ⟨64301, pr64301⟩
private theorem pr64303 : PrimeCertificate 64303 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv1531]) (by decide +kernel)
def pv64303 : PrimeValue := ⟨64303, pr64303⟩
private theorem pr64319 : PrimeCertificate 64319 :=
  certifyPrime (q := pv13) (ls := [pv2,pv32159]) (by decide +kernel)
def pv64319 : PrimeValue := ⟨64319, pr64319⟩
private theorem pr64327 : PrimeCertificate 64327 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv71,pv151]) (by decide +kernel)
def pv64327 : PrimeValue := ⟨64327, pr64327⟩
private theorem pr64333 : PrimeCertificate 64333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1787]) (by decide +kernel)
def pv64333 : PrimeValue := ⟨64333, pr64333⟩
private theorem pr64373 : PrimeCertificate 64373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv19]) (by decide +kernel)
def pv64373 : PrimeValue := ⟨64373, pr64373⟩
private theorem pr64381 : PrimeCertificate 64381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv29,pv37]) (by decide +kernel)
def pv64381 : PrimeValue := ⟨64381, pr64381⟩
private theorem pr64399 : PrimeCertificate 64399 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv10733]) (by decide +kernel)
def pv64399 : PrimeValue := ⟨64399, pr64399⟩
private theorem pr64403 : PrimeCertificate 64403 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv2477]) (by decide +kernel)
def pv64403 : PrimeValue := ⟨64403, pr64403⟩
private theorem pr64433 : PrimeCertificate 64433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv4027]) (by decide +kernel)
def pv64433 : PrimeValue := ⟨64433, pr64433⟩
private theorem pr64439 : PrimeCertificate 64439 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv29,pv101]) (by decide +kernel)
def pv64439 : PrimeValue := ⟨64439, pr64439⟩
private theorem pr64451 : PrimeCertificate 64451 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1289]) (by decide +kernel)
def pv64451 : PrimeValue := ⟨64451, pr64451⟩
private theorem pr64453 : PrimeCertificate 64453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv131]) (by decide +kernel)
def pv64453 : PrimeValue := ⟨64453, pr64453⟩
private theorem pr64483 : PrimeCertificate 64483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv977]) (by decide +kernel)
def pv64483 : PrimeValue := ⟨64483, pr64483⟩
private theorem pr64489 : PrimeCertificate 64489 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv2687]) (by decide +kernel)
def pv64489 : PrimeValue := ⟨64489, pr64489⟩
private theorem pr64499 : PrimeCertificate 64499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv17,pv271]) (by decide +kernel)
def pv64499 : PrimeValue := ⟨64499, pr64499⟩
private theorem pr64513 : PrimeCertificate 64513 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv64513 : PrimeValue := ⟨64513, pr64513⟩
private theorem pr64567 : PrimeCertificate 64567 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv211]) (by decide +kernel)
def pv64567 : PrimeValue := ⟨64567, pr64567⟩
private theorem pr64577 : PrimeCertificate 64577 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1009]) (by decide +kernel)
def pv64577 : PrimeValue := ⟨64577, pr64577⟩
private theorem pr64579 : PrimeCertificate 64579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv229]) (by decide +kernel)
def pv64579 : PrimeValue := ⟨64579, pr64579⟩
private theorem pr64591 : PrimeCertificate 64591 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv2153]) (by decide +kernel)
def pv64591 : PrimeValue := ⟨64591, pr64591⟩
private theorem pr64601 : PrimeCertificate 64601 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17,pv19]) (by decide +kernel)
def pv64601 : PrimeValue := ⟨64601, pr64601⟩
private theorem pr64609 : PrimeCertificate 64609 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv673]) (by decide +kernel)
def pv64609 : PrimeValue := ⟨64609, pr64609⟩
private theorem pr64613 : PrimeCertificate 64613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv557]) (by decide +kernel)
def pv64613 : PrimeValue := ⟨64613, pr64613⟩
private theorem pr64621 : PrimeCertificate 64621 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv359]) (by decide +kernel)
def pv64621 : PrimeValue := ⟨64621, pr64621⟩
private theorem pr64627 : PrimeCertificate 64627 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv10771]) (by decide +kernel)
def pv64627 : PrimeValue := ⟨64627, pr64627⟩
private theorem pr64633 : PrimeCertificate 64633 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2693]) (by decide +kernel)
def pv64633 : PrimeValue := ⟨64633, pr64633⟩
private theorem pr64661 : PrimeCertificate 64661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv53,pv61]) (by decide +kernel)
def pv64661 : PrimeValue := ⟨64661, pr64661⟩
private theorem pr64663 : PrimeCertificate 64663 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv829]) (by decide +kernel)
def pv64663 : PrimeValue := ⟨64663, pr64663⟩
private theorem pr64667 : PrimeCertificate 64667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv31,pv149]) (by decide +kernel)
def pv64667 : PrimeValue := ⟨64667, pr64667⟩
private theorem pr64679 : PrimeCertificate 64679 :=
  certifyPrime (q := pv17) (ls := [pv2,pv73,pv443]) (by decide +kernel)
def pv64679 : PrimeValue := ⟨64679, pr64679⟩
private theorem pr64693 : PrimeCertificate 64693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv599]) (by decide +kernel)
def pv64693 : PrimeValue := ⟨64693, pr64693⟩
private theorem pr64709 : PrimeCertificate 64709 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv2311]) (by decide +kernel)
def pv64709 : PrimeValue := ⟨64709, pr64709⟩
private theorem pr64717 : PrimeCertificate 64717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5393]) (by decide +kernel)
def pv64717 : PrimeValue := ⟨64717, pr64717⟩
private theorem pr64747 : PrimeCertificate 64747 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv109]) (by decide +kernel)
def pv64747 : PrimeValue := ⟨64747, pr64747⟩
private theorem pr64763 : PrimeCertificate 64763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv32381]) (by decide +kernel)
def pv64763 : PrimeValue := ⟨64763, pr64763⟩
private theorem pr64781 : PrimeCertificate 64781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41,pv79]) (by decide +kernel)
def pv64781 : PrimeValue := ⟨64781, pr64781⟩
private theorem pr64783 : PrimeCertificate 64783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv59,pv61]) (by decide +kernel)
def pv64783 : PrimeValue := ⟨64783, pr64783⟩
private theorem pr64793 : PrimeCertificate 64793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv13,pv89]) (by decide +kernel)
def pv64793 : PrimeValue := ⟨64793, pr64793⟩
private theorem pr64811 : PrimeCertificate 64811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv6481]) (by decide +kernel)
def pv64811 : PrimeValue := ⟨64811, pr64811⟩
private theorem pr64817 : PrimeCertificate 64817 :=
  certifyPrime (q := pv3) (ls := [pv2,pv4051]) (by decide +kernel)
def pv64817 : PrimeValue := ⟨64817, pr64817⟩
private theorem pr64849 : PrimeCertificate 64849 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv193]) (by decide +kernel)
def pv64849 : PrimeValue := ⟨64849, pr64849⟩
private theorem pr64853 : PrimeCertificate 64853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv523]) (by decide +kernel)
def pv64853 : PrimeValue := ⟨64853, pr64853⟩
private theorem pr64871 : PrimeCertificate 64871 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv499]) (by decide +kernel)
def pv64871 : PrimeValue := ⟨64871, pr64871⟩
private theorem pr64877 : PrimeCertificate 64877 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv331]) (by decide +kernel)
def pv64877 : PrimeValue := ⟨64877, pr64877⟩
private theorem pr64879 : PrimeCertificate 64879 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11,pv983]) (by decide +kernel)
def pv64879 : PrimeValue := ⟨64879, pr64879⟩
private theorem pr64891 : PrimeCertificate 64891 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv7,pv103]) (by decide +kernel)
def pv64891 : PrimeValue := ⟨64891, pr64891⟩
private theorem pr64901 : PrimeCertificate 64901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv59]) (by decide +kernel)
def pv64901 : PrimeValue := ⟨64901, pr64901⟩
private theorem pr64919 : PrimeCertificate 64919 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv4637]) (by decide +kernel)
def pv64919 : PrimeValue := ⟨64919, pr64919⟩
private theorem pr64921 : PrimeCertificate 64921 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv541]) (by decide +kernel)
def pv64921 : PrimeValue := ⟨64921, pr64921⟩
private theorem pr64927 : PrimeCertificate 64927 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv3607]) (by decide +kernel)
def pv64927 : PrimeValue := ⟨64927, pr64927⟩
private theorem pr64937 : PrimeCertificate 64937 :=
  certifyPrime (q := pv3) (ls := [pv2,pv8117]) (by decide +kernel)
def pv64937 : PrimeValue := ⟨64937, pr64937⟩
private theorem pr64951 : PrimeCertificate 64951 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv433]) (by decide +kernel)
def pv64951 : PrimeValue := ⟨64951, pr64951⟩
private theorem pr64969 : PrimeCertificate 64969 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv2707]) (by decide +kernel)
def pv64969 : PrimeValue := ⟨64969, pr64969⟩
private theorem pr64997 : PrimeCertificate 64997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv16249]) (by decide +kernel)
def pv64997 : PrimeValue := ⟨64997, pr64997⟩
private theorem pr65003 : PrimeCertificate 65003 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv4643]) (by decide +kernel)
def pv65003 : PrimeValue := ⟨65003, pr65003⟩
private theorem pr65011 : PrimeCertificate 65011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv197]) (by decide +kernel)
def pv65011 : PrimeValue := ⟨65011, pr65011⟩
private theorem pr65027 : PrimeCertificate 65027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv41,pv61]) (by decide +kernel)
def pv65027 : PrimeValue := ⟨65027, pr65027⟩
private theorem pr65029 : PrimeCertificate 65029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5419]) (by decide +kernel)
def pv65029 : PrimeValue := ⟨65029, pr65029⟩
private theorem pr65033 : PrimeCertificate 65033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv739]) (by decide +kernel)
def pv65033 : PrimeValue := ⟨65033, pr65033⟩
private theorem pr65053 : PrimeCertificate 65053 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv139]) (by decide +kernel)
def pv65053 : PrimeValue := ⟨65053, pr65053⟩
private theorem pr65063 : PrimeCertificate 65063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv32531]) (by decide +kernel)
def pv65063 : PrimeValue := ⟨65063, pr65063⟩
private theorem pr65071 : PrimeCertificate 65071 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv241]) (by decide +kernel)
def pv65071 : PrimeValue := ⟨65071, pr65071⟩
private theorem pr65089 : PrimeCertificate 65089 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv113]) (by decide +kernel)
def pv65089 : PrimeValue := ⟨65089, pr65089⟩
private theorem pr65099 : PrimeCertificate 65099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv269]) (by decide +kernel)
def pv65099 : PrimeValue := ⟨65099, pr65099⟩
private theorem pr65101 : PrimeCertificate 65101 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv31]) (by decide +kernel)
def pv65101 : PrimeValue := ⟨65101, pr65101⟩
private theorem pr65111 : PrimeCertificate 65111 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv17,pv383]) (by decide +kernel)
def pv65111 : PrimeValue := ⟨65111, pr65111⟩
private theorem pr65119 : PrimeCertificate 65119 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv10853]) (by decide +kernel)
def pv65119 : PrimeValue := ⟨65119, pr65119⟩
private theorem pr65123 : PrimeCertificate 65123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv32561]) (by decide +kernel)
def pv65123 : PrimeValue := ⟨65123, pr65123⟩
private theorem pr65129 : PrimeCertificate 65129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv1163]) (by decide +kernel)
def pv65129 : PrimeValue := ⟨65129, pr65129⟩
private theorem pr65141 : PrimeCertificate 65141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv3257]) (by decide +kernel)
def pv65141 : PrimeValue := ⟨65141, pr65141⟩
private theorem pr65147 : PrimeCertificate 65147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv32573]) (by decide +kernel)
def pv65147 : PrimeValue := ⟨65147, pr65147⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
