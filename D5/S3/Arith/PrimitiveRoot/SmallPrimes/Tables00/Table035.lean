/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table035
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table035.pv91249
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table007
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table018
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table019

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr91249 : Nat.Prime 91249 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv1901]) (by decide +kernel)
def pv91249 : PrimeValue := ⟨91249, pr91249⟩
private theorem pr91253 : Nat.Prime 91253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv3259]) (by decide +kernel)
def pv91253 : PrimeValue := ⟨91253, pr91253⟩
private theorem pr91283 : Nat.Prime 91283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv45641]) (by decide +kernel)
def pv91283 : PrimeValue := ⟨91283, pr91283⟩
private theorem pr91291 : Nat.Prime 91291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv179]) (by decide +kernel)
def pv91291 : PrimeValue := ⟨91291, pr91291⟩
private theorem pr91297 : Nat.Prime 91297 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv317]) (by decide +kernel)
def pv91297 : PrimeValue := ⟨91297, pr91297⟩
private theorem pr91303 : Nat.Prime 91303 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv15217]) (by decide +kernel)
def pv91303 : PrimeValue := ⟨91303, pr91303⟩
private theorem pr91309 : Nat.Prime 91309 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv7,pv1087]) (by decide +kernel)
def pv91309 : PrimeValue := ⟨91309, pr91309⟩
private theorem pr91331 : Nat.Prime 91331 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv9133]) (by decide +kernel)
def pv91331 : PrimeValue := ⟨91331, pr91331⟩
private theorem pr91367 : Nat.Prime 91367 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv11,pv4153]) (by decide +kernel)
def pv91367 : PrimeValue := ⟨91367, pr91367⟩
private theorem pr91369 : Nat.Prime 91369 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv47]) (by decide +kernel)
def pv91369 : PrimeValue := ⟨91369, pr91369⟩
private theorem pr91373 : Nat.Prime 91373 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv53,pv431]) (by decide +kernel)
def pv91373 : PrimeValue := ⟨91373, pr91373⟩
private theorem pr91381 : Nat.Prime 91381 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv1523]) (by decide +kernel)
def pv91381 : PrimeValue := ⟨91381, pr91381⟩
private theorem pr91387 : Nat.Prime 91387 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5077]) (by decide +kernel)
def pv91387 : PrimeValue := ⟨91387, pr91387⟩
private theorem pr91393 : Nat.Prime 91393 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv7,pv17]) (by decide +kernel)
def pv91393 : PrimeValue := ⟨91393, pr91393⟩
private theorem pr91397 : Nat.Prime 91397 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv73,pv313]) (by decide +kernel)
def pv91397 : PrimeValue := ⟨91397, pr91397⟩
private theorem pr91411 : Nat.Prime 91411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv277]) (by decide +kernel)
def pv91411 : PrimeValue := ⟨91411, pr91411⟩
private theorem pr91423 : Nat.Prime 91423 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv1693]) (by decide +kernel)
def pv91423 : PrimeValue := ⟨91423, pr91423⟩
private theorem pr91433 : Nat.Prime 91433 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv1039]) (by decide +kernel)
def pv91433 : PrimeValue := ⟨91433, pr91433⟩
private theorem pr91453 : Nat.Prime 91453 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7621]) (by decide +kernel)
def pv91453 : PrimeValue := ⟨91453, pr91453⟩
private theorem pr91457 : Nat.Prime 91457 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1429]) (by decide +kernel)
def pv91457 : PrimeValue := ⟨91457, pr91457⟩
private theorem pr91459 : Nat.Prime 91459 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5081]) (by decide +kernel)
def pv91459 : PrimeValue := ⟨91459, pr91459⟩
private theorem pr91463 : Nat.Prime 91463 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv47,pv139]) (by decide +kernel)
def pv91463 : PrimeValue := ⟨91463, pr91463⟩
private theorem pr91493 : Nat.Prime 91493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv89,pv257]) (by decide +kernel)
def pv91493 : PrimeValue := ⟨91493, pr91493⟩
private theorem pr91499 : Nat.Prime 91499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv4159]) (by decide +kernel)
def pv91499 : PrimeValue := ⟨91499, pr91499⟩
private theorem pr91513 : Nat.Prime 91513 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv31,pv41]) (by decide +kernel)
def pv91513 : PrimeValue := ⟨91513, pr91513⟩
private theorem pr91529 : Nat.Prime 91529 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv673]) (by decide +kernel)
def pv91529 : PrimeValue := ⟨91529, pr91529⟩
private theorem pr91541 : Nat.Prime 91541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23,pv199]) (by decide +kernel)
def pv91541 : PrimeValue := ⟨91541, pr91541⟩
private theorem pr91571 : Nat.Prime 91571 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv9157]) (by decide +kernel)
def pv91571 : PrimeValue := ⟨91571, pr91571⟩
private theorem pr91573 : Nat.Prime 91573 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv587]) (by decide +kernel)
def pv91573 : PrimeValue := ⟨91573, pr91573⟩
private theorem pr91577 : Nat.Prime 91577 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11447]) (by decide +kernel)
def pv91577 : PrimeValue := ⟨91577, pr91577⟩
private theorem pr91583 : Nat.Prime 91583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv29,pv1579]) (by decide +kernel)
def pv91583 : PrimeValue := ⟨91583, pr91583⟩
private theorem pr91591 : Nat.Prime 91591 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv43,pv71]) (by decide +kernel)
def pv91591 : PrimeValue := ⟨91591, pr91591⟩
private theorem pr91621 : Nat.Prime 91621 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv509]) (by decide +kernel)
def pv91621 : PrimeValue := ⟨91621, pr91621⟩
private theorem pr91631 : Nat.Prime 91631 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv11,pv17]) (by decide +kernel)
def pv91631 : PrimeValue := ⟨91631, pr91631⟩
private theorem pr91639 : Nat.Prime 91639 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv1697]) (by decide +kernel)
def pv91639 : PrimeValue := ⟨91639, pr91639⟩
private theorem pr91673 : Nat.Prime 91673 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv1637]) (by decide +kernel)
def pv91673 : PrimeValue := ⟨91673, pr91673⟩
private theorem pr91691 : Nat.Prime 91691 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv53,pv173]) (by decide +kernel)
def pv91691 : PrimeValue := ⟨91691, pr91691⟩
private theorem pr91703 : Nat.Prime 91703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv3527]) (by decide +kernel)
def pv91703 : PrimeValue := ⟨91703, pr91703⟩
private theorem pr91711 : Nat.Prime 91711 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv1019]) (by decide +kernel)
def pv91711 : PrimeValue := ⟨91711, pr91711⟩
private theorem pr91733 : Nat.Prime 91733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv19,pv71]) (by decide +kernel)
def pv91733 : PrimeValue := ⟨91733, pr91733⟩
private theorem pr91753 : Nat.Prime 91753 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv3823]) (by decide +kernel)
def pv91753 : PrimeValue := ⟨91753, pr91753⟩
private theorem pr91757 : Nat.Prime 91757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv29,pv113]) (by decide +kernel)
def pv91757 : PrimeValue := ⟨91757, pr91757⟩
private theorem pr91771 : Nat.Prime 91771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv19,pv23]) (by decide +kernel)
def pv91771 : PrimeValue := ⟨91771, pr91771⟩
private theorem pr91781 : Nat.Prime 91781 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv353]) (by decide +kernel)
def pv91781 : PrimeValue := ⟨91781, pr91781⟩
private theorem pr91801 : Nat.Prime 91801 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv91801 : PrimeValue := ⟨91801, pr91801⟩
private theorem pr91807 : Nat.Prime 91807 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv13,pv107]) (by decide +kernel)
def pv91807 : PrimeValue := ⟨91807, pr91807⟩
private theorem pr91811 : Nat.Prime 91811 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv9181]) (by decide +kernel)
def pv91811 : PrimeValue := ⟨91811, pr91811⟩
private theorem pr91813 : Nat.Prime 91813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv1093]) (by decide +kernel)
def pv91813 : PrimeValue := ⟨91813, pr91813⟩
private theorem pr91823 : Nat.Prime 91823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv31,pv1481]) (by decide +kernel)
def pv91823 : PrimeValue := ⟨91823, pr91823⟩
private theorem pr91837 : Nat.Prime 91837 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2551]) (by decide +kernel)
def pv91837 : PrimeValue := ⟨91837, pr91837⟩
private theorem pr91841 : Nat.Prime 91841 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv41]) (by decide +kernel)
def pv91841 : PrimeValue := ⟨91841, pr91841⟩
private theorem pr91867 : Nat.Prime 91867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv61,pv251]) (by decide +kernel)
def pv91867 : PrimeValue := ⟨91867, pr91867⟩
private theorem pr91873 : Nat.Prime 91873 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv29]) (by decide +kernel)
def pv91873 : PrimeValue := ⟨91873, pr91873⟩
private theorem pr91909 : Nat.Prime 91909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv37]) (by decide +kernel)
def pv91909 : PrimeValue := ⟨91909, pr91909⟩
private theorem pr91921 : Nat.Prime 91921 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv383]) (by decide +kernel)
def pv91921 : PrimeValue := ⟨91921, pr91921⟩
private theorem pr91939 : Nat.Prime 91939 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv199]) (by decide +kernel)
def pv91939 : PrimeValue := ⟨91939, pr91939⟩
private theorem pr91943 : Nat.Prime 91943 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv45971]) (by decide +kernel)
def pv91943 : PrimeValue := ⟨91943, pr91943⟩
private theorem pr91951 : Nat.Prime 91951 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv613]) (by decide +kernel)
def pv91951 : PrimeValue := ⟨91951, pr91951⟩
private theorem pr91957 : Nat.Prime 91957 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv79,pv97]) (by decide +kernel)
def pv91957 : PrimeValue := ⟨91957, pr91957⟩
private theorem pr91961 : Nat.Prime 91961 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv11,pv19]) (by decide +kernel)
def pv91961 : PrimeValue := ⟨91961, pr91961⟩
private theorem pr91969 : Nat.Prime 91969 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv479]) (by decide +kernel)
def pv91969 : PrimeValue := ⟨91969, pr91969⟩
private theorem pr91997 : Nat.Prime 91997 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv109,pv211]) (by decide +kernel)
def pv91997 : PrimeValue := ⟨91997, pr91997⟩
private theorem pr92003 : Nat.Prime 92003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv157,pv293]) (by decide +kernel)
def pv92003 : PrimeValue := ⟨92003, pr92003⟩
private theorem pr92009 : Nat.Prime 92009 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv31,pv53]) (by decide +kernel)
def pv92009 : PrimeValue := ⟨92009, pr92009⟩
private theorem pr92033 : Nat.Prime 92033 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv719]) (by decide +kernel)
def pv92033 : PrimeValue := ⟨92033, pr92033⟩
private theorem pr92041 : Nat.Prime 92041 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv13,pv59]) (by decide +kernel)
def pv92041 : PrimeValue := ⟨92041, pr92041⟩
private theorem pr92051 : Nat.Prime 92051 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv263]) (by decide +kernel)
def pv92051 : PrimeValue := ⟨92051, pr92051⟩
private theorem pr92077 : Nat.Prime 92077 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7673]) (by decide +kernel)
def pv92077 : PrimeValue := ⟨92077, pr92077⟩
private theorem pr92083 : Nat.Prime 92083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv103,pv149]) (by decide +kernel)
def pv92083 : PrimeValue := ⟨92083, pr92083⟩
private theorem pr92107 : Nat.Prime 92107 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv43]) (by decide +kernel)
def pv92107 : PrimeValue := ⟨92107, pr92107⟩
private theorem pr92111 : Nat.Prime 92111 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv61,pv151]) (by decide +kernel)
def pv92111 : PrimeValue := ⟨92111, pr92111⟩
private theorem pr92119 : Nat.Prime 92119 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv1181]) (by decide +kernel)
def pv92119 : PrimeValue := ⟨92119, pr92119⟩
private theorem pr92143 : Nat.Prime 92143 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv5119]) (by decide +kernel)
def pv92143 : PrimeValue := ⟨92143, pr92143⟩
private theorem pr92153 : Nat.Prime 92153 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11519]) (by decide +kernel)
def pv92153 : PrimeValue := ⟨92153, pr92153⟩
private theorem pr92173 : Nat.Prime 92173 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7681]) (by decide +kernel)
def pv92173 : PrimeValue := ⟨92173, pr92173⟩
private theorem pr92177 : Nat.Prime 92177 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv7,pv823]) (by decide +kernel)
def pv92177 : PrimeValue := ⟨92177, pr92177⟩
private theorem pr92179 : Nat.Prime 92179 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv569]) (by decide +kernel)
def pv92179 : PrimeValue := ⟨92179, pr92179⟩
private theorem pr92189 : Nat.Prime 92189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv1213]) (by decide +kernel)
def pv92189 : PrimeValue := ⟨92189, pr92189⟩
private theorem pr92203 : Nat.Prime 92203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv127]) (by decide +kernel)
def pv92203 : PrimeValue := ⟨92203, pr92203⟩
private theorem pr92219 : Nat.Prime 92219 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv941]) (by decide +kernel)
def pv92219 : PrimeValue := ⟨92219, pr92219⟩
private theorem pr92221 : Nat.Prime 92221 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv29,pv53]) (by decide +kernel)
def pv92221 : PrimeValue := ⟨92221, pr92221⟩
private theorem pr92227 : Nat.Prime 92227 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv809]) (by decide +kernel)
def pv92227 : PrimeValue := ⟨92227, pr92227⟩
private theorem pr92233 : Nat.Prime 92233 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv61]) (by decide +kernel)
def pv92233 : PrimeValue := ⟨92233, pr92233⟩
private theorem pr92237 : Nat.Prime 92237 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23059]) (by decide +kernel)
def pv92237 : PrimeValue := ⟨92237, pr92237⟩
private theorem pr92243 : Nat.Prime 92243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv2713]) (by decide +kernel)
def pv92243 : PrimeValue := ⟨92243, pr92243⟩
private theorem pr92251 : Nat.Prime 92251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv41]) (by decide +kernel)
def pv92251 : PrimeValue := ⟨92251, pr92251⟩
private theorem pr92269 : Nat.Prime 92269 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv11,pv233]) (by decide +kernel)
def pv92269 : PrimeValue := ⟨92269, pr92269⟩
private theorem pr92297 : Nat.Prime 92297 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv83,pv139]) (by decide +kernel)
def pv92297 : PrimeValue := ⟨92297, pr92297⟩
private theorem pr92311 : Nat.Prime 92311 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv17,pv181]) (by decide +kernel)
def pv92311 : PrimeValue := ⟨92311, pr92311⟩
private theorem pr92317 : Nat.Prime 92317 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv157]) (by decide +kernel)
def pv92317 : PrimeValue := ⟨92317, pr92317⟩
private theorem pr92333 : Nat.Prime 92333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv563]) (by decide +kernel)
def pv92333 : PrimeValue := ⟨92333, pr92333⟩
private theorem pr92347 : Nat.Prime 92347 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv15391]) (by decide +kernel)
def pv92347 : PrimeValue := ⟨92347, pr92347⟩
private theorem pr92353 : Nat.Prime 92353 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv37]) (by decide +kernel)
def pv92353 : PrimeValue := ⟨92353, pr92353⟩
private theorem pr92357 : Nat.Prime 92357 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv2099]) (by decide +kernel)
def pv92357 : PrimeValue := ⟨92357, pr92357⟩
private theorem pr92363 : Nat.Prime 92363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv46181]) (by decide +kernel)
def pv92363 : PrimeValue := ⟨92363, pr92363⟩
private theorem pr92369 : Nat.Prime 92369 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv251]) (by decide +kernel)
def pv92369 : PrimeValue := ⟨92369, pr92369⟩
private theorem pr92377 : Nat.Prime 92377 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv1283]) (by decide +kernel)
def pv92377 : PrimeValue := ⟨92377, pr92377⟩
private theorem pr92381 : Nat.Prime 92381 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv31,pv149]) (by decide +kernel)
def pv92381 : PrimeValue := ⟨92381, pr92381⟩
private theorem pr92383 : Nat.Prime 92383 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv89,pv173]) (by decide +kernel)
def pv92383 : PrimeValue := ⟨92383, pr92383⟩
private theorem pr92387 : Nat.Prime 92387 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv6599]) (by decide +kernel)
def pv92387 : PrimeValue := ⟨92387, pr92387⟩
private theorem pr92399 : Nat.Prime 92399 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv46199]) (by decide +kernel)
def pv92399 : PrimeValue := ⟨92399, pr92399⟩
private theorem pr92401 : Nat.Prime 92401 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv3,pv5,pv7,pv11]) (by decide +kernel)
def pv92401 : PrimeValue := ⟨92401, pr92401⟩
private theorem pr92413 : Nat.Prime 92413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv151]) (by decide +kernel)
def pv92413 : PrimeValue := ⟨92413, pr92413⟩
private theorem pr92419 : Nat.Prime 92419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv73,pv211]) (by decide +kernel)
def pv92419 : PrimeValue := ⟨92419, pr92419⟩
private theorem pr92431 : Nat.Prime 92431 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv3,pv5,pv13,pv79]) (by decide +kernel)
def pv92431 : PrimeValue := ⟨92431, pr92431⟩
private theorem pr92459 : Nat.Prime 92459 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv46229]) (by decide +kernel)
def pv92459 : PrimeValue := ⟨92459, pr92459⟩
private theorem pr92461 : Nat.Prime 92461 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv23,pv67]) (by decide +kernel)
def pv92461 : PrimeValue := ⟨92461, pr92461⟩
private theorem pr92467 : Nat.Prime 92467 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv467]) (by decide +kernel)
def pv92467 : PrimeValue := ⟨92467, pr92467⟩
private theorem pr92479 : Nat.Prime 92479 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv15413]) (by decide +kernel)
def pv92479 : PrimeValue := ⟨92479, pr92479⟩
private theorem pr92489 : Nat.Prime 92489 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv1051]) (by decide +kernel)
def pv92489 : PrimeValue := ⟨92489, pr92489⟩
private theorem pr92503 : Nat.Prime 92503 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv571]) (by decide +kernel)
def pv92503 : PrimeValue := ⟨92503, pr92503⟩
private theorem pr92507 : Nat.Prime 92507 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv2011]) (by decide +kernel)
def pv92507 : PrimeValue := ⟨92507, pr92507⟩
private theorem pr92551 : Nat.Prime 92551 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv617]) (by decide +kernel)
def pv92551 : PrimeValue := ⟨92551, pr92551⟩
private theorem pr92557 : Nat.Prime 92557 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv857]) (by decide +kernel)
def pv92557 : PrimeValue := ⟨92557, pr92557⟩
private theorem pr92569 : Nat.Prime 92569 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv7,pv19,pv29]) (by decide +kernel)
def pv92569 : PrimeValue := ⟨92569, pr92569⟩
private theorem pr92581 : Nat.Prime 92581 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv1543]) (by decide +kernel)
def pv92581 : PrimeValue := ⟨92581, pr92581⟩
private theorem pr92593 : Nat.Prime 92593 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv643]) (by decide +kernel)
def pv92593 : PrimeValue := ⟨92593, pr92593⟩
private theorem pr92623 : Nat.Prime 92623 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv43,pv359]) (by decide +kernel)
def pv92623 : PrimeValue := ⟨92623, pr92623⟩
private theorem pr92627 : Nat.Prime 92627 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv1597]) (by decide +kernel)
def pv92627 : PrimeValue := ⟨92627, pr92627⟩
private theorem pr92639 : Nat.Prime 92639 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv13,pv509]) (by decide +kernel)
def pv92639 : PrimeValue := ⟨92639, pr92639⟩
private theorem pr92641 : Nat.Prime 92641 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv193]) (by decide +kernel)
def pv92641 : PrimeValue := ⟨92641, pr92641⟩
private theorem pr92647 : Nat.Prime 92647 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5147]) (by decide +kernel)
def pv92647 : PrimeValue := ⟨92647, pr92647⟩
private theorem pr92669 : Nat.Prime 92669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23167]) (by decide +kernel)
def pv92669 : PrimeValue := ⟨92669, pr92669⟩
private theorem pr92671 : Nat.Prime 92671 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv3089]) (by decide +kernel)
def pv92671 : PrimeValue := ⟨92671, pr92671⟩
private theorem pr92681 : Nat.Prime 92681 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv331]) (by decide +kernel)
def pv92681 : PrimeValue := ⟨92681, pr92681⟩
private theorem pr92683 : Nat.Prime 92683 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv271]) (by decide +kernel)
def pv92683 : PrimeValue := ⟨92683, pr92683⟩
private theorem pr92693 : Nat.Prime 92693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23173]) (by decide +kernel)
def pv92693 : PrimeValue := ⟨92693, pr92693⟩
private theorem pr92699 : Nat.Prime 92699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv46349]) (by decide +kernel)
def pv92699 : PrimeValue := ⟨92699, pr92699⟩
private theorem pr92707 : Nat.Prime 92707 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv15451]) (by decide +kernel)
def pv92707 : PrimeValue := ⟨92707, pr92707⟩
private theorem pr92717 : Nat.Prime 92717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv1783]) (by decide +kernel)
def pv92717 : PrimeValue := ⟨92717, pr92717⟩
private theorem pr92723 : Nat.Prime 92723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv37,pv179]) (by decide +kernel)
def pv92723 : PrimeValue := ⟨92723, pr92723⟩
private theorem pr92737 : Nat.Prime 92737 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv23]) (by decide +kernel)
def pv92737 : PrimeValue := ⟨92737, pr92737⟩
private theorem pr92753 : Nat.Prime 92753 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv17,pv31]) (by decide +kernel)
def pv92753 : PrimeValue := ⟨92753, pr92753⟩
private theorem pr92761 : Nat.Prime 92761 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv5,pv773]) (by decide +kernel)
def pv92761 : PrimeValue := ⟨92761, pr92761⟩
private theorem pr92767 : Nat.Prime 92767 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv15461]) (by decide +kernel)
def pv92767 : PrimeValue := ⟨92767, pr92767⟩
private theorem pr92779 : Nat.Prime 92779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv47]) (by decide +kernel)
def pv92779 : PrimeValue := ⟨92779, pr92779⟩
private theorem pr92789 : Nat.Prime 92789 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23197]) (by decide +kernel)
def pv92789 : PrimeValue := ⟨92789, pr92789⟩
private theorem pr92791 : Nat.Prime 92791 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv1031]) (by decide +kernel)
def pv92791 : PrimeValue := ⟨92791, pr92791⟩
private theorem pr92801 : Nat.Prime 92801 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv29]) (by decide +kernel)
def pv92801 : PrimeValue := ⟨92801, pr92801⟩
private theorem pr92809 : Nat.Prime 92809 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv1289]) (by decide +kernel)
def pv92809 : PrimeValue := ⟨92809, pr92809⟩
private theorem pr92821 : Nat.Prime 92821 :=
  checkPrime_prime (q := pv47) (ls := [pv2,pv3,pv5,pv7,pv13,pv17]) (by decide +kernel)
def pv92821 : PrimeValue := ⟨92821, pr92821⟩
private theorem pr92831 : Nat.Prime 92831 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv9283]) (by decide +kernel)
def pv92831 : PrimeValue := ⟨92831, pr92831⟩
private theorem pr92849 : Nat.Prime 92849 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv829]) (by decide +kernel)
def pv92849 : PrimeValue := ⟨92849, pr92849⟩
private theorem pr92857 : Nat.Prime 92857 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv53,pv73]) (by decide +kernel)
def pv92857 : PrimeValue := ⟨92857, pr92857⟩
private theorem pr92861 : Nat.Prime 92861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv4643]) (by decide +kernel)
def pv92861 : PrimeValue := ⟨92861, pr92861⟩
private theorem pr92863 : Nat.Prime 92863 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv11,pv67]) (by decide +kernel)
def pv92863 : PrimeValue := ⟨92863, pr92863⟩
private theorem pr92867 : Nat.Prime 92867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv59,pv787]) (by decide +kernel)
def pv92867 : PrimeValue := ⟨92867, pr92867⟩
private theorem pr92893 : Nat.Prime 92893 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7741]) (by decide +kernel)
def pv92893 : PrimeValue := ⟨92893, pr92893⟩
private theorem pr92899 : Nat.Prime 92899 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv397]) (by decide +kernel)
def pv92899 : PrimeValue := ⟨92899, pr92899⟩
private theorem pr92921 : Nat.Prime 92921 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv23,pv101]) (by decide +kernel)
def pv92921 : PrimeValue := ⟨92921, pr92921⟩
private theorem pr92927 : Nat.Prime 92927 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv97,pv479]) (by decide +kernel)
def pv92927 : PrimeValue := ⟨92927, pr92927⟩
private theorem pr92941 : Nat.Prime 92941 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1549]) (by decide +kernel)
def pv92941 : PrimeValue := ⟨92941, pr92941⟩
private theorem pr92951 : Nat.Prime 92951 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv11,pv13]) (by decide +kernel)
def pv92951 : PrimeValue := ⟨92951, pr92951⟩
private theorem pr92957 : Nat.Prime 92957 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv1367]) (by decide +kernel)
def pv92957 : PrimeValue := ⟨92957, pr92957⟩
private theorem pr92959 : Nat.Prime 92959 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv15493]) (by decide +kernel)
def pv92959 : PrimeValue := ⟨92959, pr92959⟩
private theorem pr92987 : Nat.Prime 92987 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv2447]) (by decide +kernel)
def pv92987 : PrimeValue := ⟨92987, pr92987⟩
private theorem pr92993 : Nat.Prime 92993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1453]) (by decide +kernel)
def pv92993 : PrimeValue := ⟨92993, pr92993⟩
private theorem pr93001 : Nat.Prime 93001 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv31]) (by decide +kernel)
def pv93001 : PrimeValue := ⟨93001, pr93001⟩
private theorem pr93047 : Nat.Prime 93047 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv46523]) (by decide +kernel)
def pv93047 : PrimeValue := ⟨93047, pr93047⟩
private theorem pr93053 : Nat.Prime 93053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv541]) (by decide +kernel)
def pv93053 : PrimeValue := ⟨93053, pr93053⟩
private theorem pr93059 : Nat.Prime 93059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv17,pv23]) (by decide +kernel)
def pv93059 : PrimeValue := ⟨93059, pr93059⟩
private theorem pr93077 : Nat.Prime 93077 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23269]) (by decide +kernel)
def pv93077 : PrimeValue := ⟨93077, pr93077⟩
private theorem pr93083 : Nat.Prime 93083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv4231]) (by decide +kernel)
def pv93083 : PrimeValue := ⟨93083, pr93083⟩
private theorem pr93089 : Nat.Prime 93089 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2909]) (by decide +kernel)
def pv93089 : PrimeValue := ⟨93089, pr93089⟩
private theorem pr93097 : Nat.Prime 93097 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv431]) (by decide +kernel)
def pv93097 : PrimeValue := ⟨93097, pr93097⟩
private theorem pr93103 : Nat.Prime 93103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv59,pv263]) (by decide +kernel)
def pv93103 : PrimeValue := ⟨93103, pr93103⟩
private theorem pr93113 : Nat.Prime 93113 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv103,pv113]) (by decide +kernel)
def pv93113 : PrimeValue := ⟨93113, pr93113⟩
private theorem pr93131 : Nat.Prime 93131 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv67,pv139]) (by decide +kernel)
def pv93131 : PrimeValue := ⟨93131, pr93131⟩
private theorem pr93133 : Nat.Prime 93133 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv199]) (by decide +kernel)
def pv93133 : PrimeValue := ⟨93133, pr93133⟩
private theorem pr93151 : Nat.Prime 93151 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv23]) (by decide +kernel)
def pv93151 : PrimeValue := ⟨93151, pr93151⟩
private theorem pr93169 : Nat.Prime 93169 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv647]) (by decide +kernel)
def pv93169 : PrimeValue := ⟨93169, pr93169⟩
private theorem pr93179 : Nat.Prime 93179 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv46589]) (by decide +kernel)
def pv93179 : PrimeValue := ⟨93179, pr93179⟩
private theorem pr93187 : Nat.Prime 93187 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv31,pv167]) (by decide +kernel)
def pv93187 : PrimeValue := ⟨93187, pr93187⟩
private theorem pr93199 : Nat.Prime 93199 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv317]) (by decide +kernel)
def pv93199 : PrimeValue := ⟨93199, pr93199⟩
private theorem pr93229 : Nat.Prime 93229 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv17,pv457]) (by decide +kernel)
def pv93229 : PrimeValue := ⟨93229, pr93229⟩
private theorem pr93239 : Nat.Prime 93239 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv46619]) (by decide +kernel)
def pv93239 : PrimeValue := ⟨93239, pr93239⟩
private theorem pr93241 : Nat.Prime 93241 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv37]) (by decide +kernel)
def pv93241 : PrimeValue := ⟨93241, pr93241⟩
private theorem pr93251 : Nat.Prime 93251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv373]) (by decide +kernel)
def pv93251 : PrimeValue := ⟨93251, pr93251⟩
private theorem pr93253 : Nat.Prime 93253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv409]) (by decide +kernel)
def pv93253 : PrimeValue := ⟨93253, pr93253⟩
private theorem pr93257 : Nat.Prime 93257 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11657]) (by decide +kernel)
def pv93257 : PrimeValue := ⟨93257, pr93257⟩
private theorem pr93263 : Nat.Prime 93263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv17,pv211]) (by decide +kernel)
def pv93263 : PrimeValue := ⟨93263, pr93263⟩
private theorem pr93281 : Nat.Prime 93281 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv53]) (by decide +kernel)
def pv93281 : PrimeValue := ⟨93281, pr93281⟩
private theorem pr93283 : Nat.Prime 93283 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv2221]) (by decide +kernel)
def pv93283 : PrimeValue := ⟨93283, pr93283⟩
private theorem pr93287 : Nat.Prime 93287 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv46643]) (by decide +kernel)
def pv93287 : PrimeValue := ⟨93287, pr93287⟩
private theorem pr93307 : Nat.Prime 93307 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv15551]) (by decide +kernel)
def pv93307 : PrimeValue := ⟨93307, pr93307⟩
private theorem pr93319 : Nat.Prime 93319 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv103,pv151]) (by decide +kernel)
def pv93319 : PrimeValue := ⟨93319, pr93319⟩
private theorem pr93323 : Nat.Prime 93323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv1609]) (by decide +kernel)
def pv93323 : PrimeValue := ⟨93323, pr93323⟩
private theorem pr93329 : Nat.Prime 93329 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv307]) (by decide +kernel)
def pv93329 : PrimeValue := ⟨93329, pr93329⟩
private theorem pr93337 : Nat.Prime 93337 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv3889]) (by decide +kernel)
def pv93337 : PrimeValue := ⟨93337, pr93337⟩
private theorem pr93371 : Nat.Prime 93371 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv9337]) (by decide +kernel)
def pv93371 : PrimeValue := ⟨93371, pr93371⟩
private theorem pr93377 : Nat.Prime 93377 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1459]) (by decide +kernel)
def pv93377 : PrimeValue := ⟨93377, pr93377⟩
private theorem pr93383 : Nat.Prime 93383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv46691]) (by decide +kernel)
def pv93383 : PrimeValue := ⟨93383, pr93383⟩
private theorem pr93407 : Nat.Prime 93407 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv46703]) (by decide +kernel)
def pv93407 : PrimeValue := ⟨93407, pr93407⟩
private theorem pr93419 : Nat.Prime 93419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv3593]) (by decide +kernel)
def pv93419 : PrimeValue := ⟨93419, pr93419⟩
private theorem pr93427 : Nat.Prime 93427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv677]) (by decide +kernel)
def pv93427 : PrimeValue := ⟨93427, pr93427⟩
private theorem pr93463 : Nat.Prime 93463 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv37,pv421]) (by decide +kernel)
def pv93463 : PrimeValue := ⟨93463, pr93463⟩
private theorem pr93479 : Nat.Prime 93479 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv11,pv607]) (by decide +kernel)
def pv93479 : PrimeValue := ⟨93479, pr93479⟩
private theorem pr93481 : Nat.Prime 93481 :=
  checkPrime_prime (q := pv107) (ls := [pv2,pv3,pv5,pv19,pv41]) (by decide +kernel)
def pv93481 : PrimeValue := ⟨93481, pr93481⟩
private theorem pr93487 : Nat.Prime 93487 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv15581]) (by decide +kernel)
def pv93487 : PrimeValue := ⟨93487, pr93487⟩
private theorem pr93491 : Nat.Prime 93491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv9349]) (by decide +kernel)
def pv93491 : PrimeValue := ⟨93491, pr93491⟩
private theorem pr93493 : Nat.Prime 93493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv53]) (by decide +kernel)
def pv93493 : PrimeValue := ⟨93493, pr93493⟩
private theorem pr93497 : Nat.Prime 93497 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv29,pv31]) (by decide +kernel)
def pv93497 : PrimeValue := ⟨93497, pr93497⟩
private theorem pr93503 : Nat.Prime 93503 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv46751]) (by decide +kernel)
def pv93503 : PrimeValue := ⟨93503, pr93503⟩
private theorem pr93523 : Nat.Prime 93523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv13,pv109]) (by decide +kernel)
def pv93523 : PrimeValue := ⟨93523, pr93523⟩
private theorem pr93529 : Nat.Prime 93529 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv433]) (by decide +kernel)
def pv93529 : PrimeValue := ⟨93529, pr93529⟩
private theorem pr93553 : Nat.Prime 93553 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1949]) (by decide +kernel)
def pv93553 : PrimeValue := ⟨93553, pr93553⟩
private theorem pr93557 : Nat.Prime 93557 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv1231]) (by decide +kernel)
def pv93557 : PrimeValue := ⟨93557, pr93557⟩
private theorem pr93559 : Nat.Prime 93559 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv31,pv503]) (by decide +kernel)
def pv93559 : PrimeValue := ⟨93559, pr93559⟩
private theorem pr93563 : Nat.Prime 93563 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv41,pv163]) (by decide +kernel)
def pv93563 : PrimeValue := ⟨93563, pr93563⟩
private theorem pr93581 : Nat.Prime 93581 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv4679]) (by decide +kernel)
def pv93581 : PrimeValue := ⟨93581, pr93581⟩
private theorem pr93601 : Nat.Prime 93601 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv93601 : PrimeValue := ⟨93601, pr93601⟩
private theorem pr93629 : Nat.Prime 93629 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv89,pv263]) (by decide +kernel)
def pv93629 : PrimeValue := ⟨93629, pr93629⟩
private theorem pr93637 : Nat.Prime 93637 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17]) (by decide +kernel)
def pv93637 : PrimeValue := ⟨93637, pr93637⟩
private theorem pr93683 : Nat.Prime 93683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv1511]) (by decide +kernel)
def pv93683 : PrimeValue := ⟨93683, pr93683⟩
private theorem pr93701 : Nat.Prime 93701 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv937]) (by decide +kernel)
def pv93701 : PrimeValue := ⟨93701, pr93701⟩
private theorem pr93703 : Nat.Prime 93703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv23,pv97]) (by decide +kernel)
def pv93703 : PrimeValue := ⟨93703, pr93703⟩
private theorem pr93719 : Nat.Prime 93719 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv47,pv997]) (by decide +kernel)
def pv93719 : PrimeValue := ⟨93719, pr93719⟩
private theorem pr93739 : Nat.Prime 93739 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv919]) (by decide +kernel)
def pv93739 : PrimeValue := ⟨93739, pr93739⟩
private theorem pr93763 : Nat.Prime 93763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5209]) (by decide +kernel)
def pv93763 : PrimeValue := ⟨93763, pr93763⟩
private theorem pr93787 : Nat.Prime 93787 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv7,pv11,pv29]) (by decide +kernel)
def pv93787 : PrimeValue := ⟨93787, pr93787⟩
private theorem pr93809 : Nat.Prime 93809 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv13,pv41]) (by decide +kernel)
def pv93809 : PrimeValue := ⟨93809, pr93809⟩
private theorem pr93827 : Nat.Prime 93827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv1091]) (by decide +kernel)
def pv93827 : PrimeValue := ⟨93827, pr93827⟩
private theorem pr93851 : Nat.Prime 93851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1877]) (by decide +kernel)
def pv93851 : PrimeValue := ⟨93851, pr93851⟩
private theorem pr93871 : Nat.Prime 93871 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv149]) (by decide +kernel)
def pv93871 : PrimeValue := ⟨93871, pr93871⟩
private theorem pr93887 : Nat.Prime 93887 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv23,pv157]) (by decide +kernel)
def pv93887 : PrimeValue := ⟨93887, pr93887⟩
private theorem pr93889 : Nat.Prime 93889 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv163]) (by decide +kernel)
def pv93889 : PrimeValue := ⟨93889, pr93889⟩
private theorem pr93893 : Nat.Prime 93893 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23473]) (by decide +kernel)
def pv93893 : PrimeValue := ⟨93893, pr93893⟩
private theorem pr93901 : Nat.Prime 93901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv313]) (by decide +kernel)
def pv93901 : PrimeValue := ⟨93901, pr93901⟩
private theorem pr93911 : Nat.Prime 93911 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv9391]) (by decide +kernel)
def pv93911 : PrimeValue := ⟨93911, pr93911⟩
private theorem pr93913 : Nat.Prime 93913 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv43]) (by decide +kernel)
def pv93913 : PrimeValue := ⟨93913, pr93913⟩
private theorem pr93937 : Nat.Prime 93937 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv19,pv103]) (by decide +kernel)
def pv93937 : PrimeValue := ⟨93937, pr93937⟩
private theorem pr93941 : Nat.Prime 93941 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv61]) (by decide +kernel)
def pv93941 : PrimeValue := ⟨93941, pr93941⟩
private theorem pr93949 : Nat.Prime 93949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7829]) (by decide +kernel)
def pv93949 : PrimeValue := ⟨93949, pr93949⟩
private theorem pr93967 : Nat.Prime 93967 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv15661]) (by decide +kernel)
def pv93967 : PrimeValue := ⟨93967, pr93967⟩
private theorem pr93971 : Nat.Prime 93971 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv9397]) (by decide +kernel)
def pv93971 : PrimeValue := ⟨93971, pr93971⟩
private theorem pr93979 : Nat.Prime 93979 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv227]) (by decide +kernel)
def pv93979 : PrimeValue := ⟨93979, pr93979⟩
private theorem pr93983 : Nat.Prime 93983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv137]) (by decide +kernel)
def pv93983 : PrimeValue := ⟨93983, pr93983⟩
private theorem pr93997 : Nat.Prime 93997 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv373]) (by decide +kernel)
def pv93997 : PrimeValue := ⟨93997, pr93997⟩
private theorem pr94007 : Nat.Prime 94007 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv4273]) (by decide +kernel)
def pv94007 : PrimeValue := ⟨94007, pr94007⟩
private theorem pr94009 : Nat.Prime 94009 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv3917]) (by decide +kernel)
def pv94009 : PrimeValue := ⟨94009, pr94009⟩
private theorem pr94033 : Nat.Prime 94033 :=
  checkPrime_prime (q := pv47) (ls := [pv2,pv3,pv653]) (by decide +kernel)
def pv94033 : PrimeValue := ⟨94033, pr94033⟩
private theorem pr94049 : Nat.Prime 94049 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2939]) (by decide +kernel)
def pv94049 : PrimeValue := ⟨94049, pr94049⟩
private theorem pr94057 : Nat.Prime 94057 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv3919]) (by decide +kernel)
def pv94057 : PrimeValue := ⟨94057, pr94057⟩
private theorem pr94063 : Nat.Prime 94063 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv61,pv257]) (by decide +kernel)
def pv94063 : PrimeValue := ⟨94063, pr94063⟩
private theorem pr94079 : Nat.Prime 94079 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv17,pv2767]) (by decide +kernel)
def pv94079 : PrimeValue := ⟨94079, pr94079⟩
private theorem pr94099 : Nat.Prime 94099 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv15683]) (by decide +kernel)
def pv94099 : PrimeValue := ⟨94099, pr94099⟩
private theorem pr94109 : Nat.Prime 94109 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv3361]) (by decide +kernel)
def pv94109 : PrimeValue := ⟨94109, pr94109⟩
private theorem pr94111 : Nat.Prime 94111 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv3137]) (by decide +kernel)
def pv94111 : PrimeValue := ⟨94111, pr94111⟩
private theorem pr94117 : Nat.Prime 94117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv23,pv31]) (by decide +kernel)
def pv94117 : PrimeValue := ⟨94117, pr94117⟩
private theorem pr94121 : Nat.Prime 94121 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv181]) (by decide +kernel)
def pv94121 : PrimeValue := ⟨94121, pr94121⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
