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
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr91249 : PrimeCertificate 91249 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv1901]) (by decide +kernel)
def pv91249 : PrimeValue := ⟨91249, pr91249⟩
private theorem pr91253 : PrimeCertificate 91253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv3259]) (by decide +kernel)
def pv91253 : PrimeValue := ⟨91253, pr91253⟩
private theorem pr91283 : PrimeCertificate 91283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv45641]) (by decide +kernel)
def pv91283 : PrimeValue := ⟨91283, pr91283⟩
private theorem pr91291 : PrimeCertificate 91291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv179]) (by decide +kernel)
def pv91291 : PrimeValue := ⟨91291, pr91291⟩
private theorem pr91297 : PrimeCertificate 91297 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv317]) (by decide +kernel)
def pv91297 : PrimeValue := ⟨91297, pr91297⟩
private theorem pr91303 : PrimeCertificate 91303 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv15217]) (by decide +kernel)
def pv91303 : PrimeValue := ⟨91303, pr91303⟩
private theorem pr91309 : PrimeCertificate 91309 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv7,pv1087]) (by decide +kernel)
def pv91309 : PrimeValue := ⟨91309, pr91309⟩
private theorem pr91331 : PrimeCertificate 91331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv9133]) (by decide +kernel)
def pv91331 : PrimeValue := ⟨91331, pr91331⟩
private theorem pr91367 : PrimeCertificate 91367 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv4153]) (by decide +kernel)
def pv91367 : PrimeValue := ⟨91367, pr91367⟩
private theorem pr91369 : PrimeCertificate 91369 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv47]) (by decide +kernel)
def pv91369 : PrimeValue := ⟨91369, pr91369⟩
private theorem pr91373 : PrimeCertificate 91373 :=
  certifyPrime (q := pv3) (ls := [pv2,pv53,pv431]) (by decide +kernel)
def pv91373 : PrimeValue := ⟨91373, pr91373⟩
private theorem pr91381 : PrimeCertificate 91381 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv1523]) (by decide +kernel)
def pv91381 : PrimeValue := ⟨91381, pr91381⟩
private theorem pr91387 : PrimeCertificate 91387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5077]) (by decide +kernel)
def pv91387 : PrimeValue := ⟨91387, pr91387⟩
private theorem pr91393 : PrimeCertificate 91393 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv7,pv17]) (by decide +kernel)
def pv91393 : PrimeValue := ⟨91393, pr91393⟩
private theorem pr91397 : PrimeCertificate 91397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv313]) (by decide +kernel)
def pv91397 : PrimeValue := ⟨91397, pr91397⟩
private theorem pr91411 : PrimeCertificate 91411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv277]) (by decide +kernel)
def pv91411 : PrimeValue := ⟨91411, pr91411⟩
private theorem pr91423 : PrimeCertificate 91423 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1693]) (by decide +kernel)
def pv91423 : PrimeValue := ⟨91423, pr91423⟩
private theorem pr91433 : PrimeCertificate 91433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv1039]) (by decide +kernel)
def pv91433 : PrimeValue := ⟨91433, pr91433⟩
private theorem pr91453 : PrimeCertificate 91453 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7621]) (by decide +kernel)
def pv91453 : PrimeValue := ⟨91453, pr91453⟩
private theorem pr91457 : PrimeCertificate 91457 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1429]) (by decide +kernel)
def pv91457 : PrimeValue := ⟨91457, pr91457⟩
private theorem pr91459 : PrimeCertificate 91459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5081]) (by decide +kernel)
def pv91459 : PrimeValue := ⟨91459, pr91459⟩
private theorem pr91463 : PrimeCertificate 91463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv47,pv139]) (by decide +kernel)
def pv91463 : PrimeValue := ⟨91463, pr91463⟩
private theorem pr91493 : PrimeCertificate 91493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89,pv257]) (by decide +kernel)
def pv91493 : PrimeValue := ⟨91493, pr91493⟩
private theorem pr91499 : PrimeCertificate 91499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv4159]) (by decide +kernel)
def pv91499 : PrimeValue := ⟨91499, pr91499⟩
private theorem pr91513 : PrimeCertificate 91513 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv31,pv41]) (by decide +kernel)
def pv91513 : PrimeValue := ⟨91513, pr91513⟩
private theorem pr91529 : PrimeCertificate 91529 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv673]) (by decide +kernel)
def pv91529 : PrimeValue := ⟨91529, pr91529⟩
private theorem pr91541 : PrimeCertificate 91541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv199]) (by decide +kernel)
def pv91541 : PrimeValue := ⟨91541, pr91541⟩
private theorem pr91571 : PrimeCertificate 91571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv9157]) (by decide +kernel)
def pv91571 : PrimeValue := ⟨91571, pr91571⟩
private theorem pr91573 : PrimeCertificate 91573 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv587]) (by decide +kernel)
def pv91573 : PrimeValue := ⟨91573, pr91573⟩
private theorem pr91577 : PrimeCertificate 91577 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11447]) (by decide +kernel)
def pv91577 : PrimeValue := ⟨91577, pr91577⟩
private theorem pr91583 : PrimeCertificate 91583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv29,pv1579]) (by decide +kernel)
def pv91583 : PrimeValue := ⟨91583, pr91583⟩
private theorem pr91591 : PrimeCertificate 91591 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv43,pv71]) (by decide +kernel)
def pv91591 : PrimeValue := ⟨91591, pr91591⟩
private theorem pr91621 : PrimeCertificate 91621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv509]) (by decide +kernel)
def pv91621 : PrimeValue := ⟨91621, pr91621⟩
private theorem pr91631 : PrimeCertificate 91631 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv11,pv17]) (by decide +kernel)
def pv91631 : PrimeValue := ⟨91631, pr91631⟩
private theorem pr91639 : PrimeCertificate 91639 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1697]) (by decide +kernel)
def pv91639 : PrimeValue := ⟨91639, pr91639⟩
private theorem pr91673 : PrimeCertificate 91673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv1637]) (by decide +kernel)
def pv91673 : PrimeValue := ⟨91673, pr91673⟩
private theorem pr91691 : PrimeCertificate 91691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv53,pv173]) (by decide +kernel)
def pv91691 : PrimeValue := ⟨91691, pr91691⟩
private theorem pr91703 : PrimeCertificate 91703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv3527]) (by decide +kernel)
def pv91703 : PrimeValue := ⟨91703, pr91703⟩
private theorem pr91711 : PrimeCertificate 91711 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv1019]) (by decide +kernel)
def pv91711 : PrimeValue := ⟨91711, pr91711⟩
private theorem pr91733 : PrimeCertificate 91733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv19,pv71]) (by decide +kernel)
def pv91733 : PrimeValue := ⟨91733, pr91733⟩
private theorem pr91753 : PrimeCertificate 91753 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv3823]) (by decide +kernel)
def pv91753 : PrimeValue := ⟨91753, pr91753⟩
private theorem pr91757 : PrimeCertificate 91757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv29,pv113]) (by decide +kernel)
def pv91757 : PrimeValue := ⟨91757, pr91757⟩
private theorem pr91771 : PrimeCertificate 91771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv19,pv23]) (by decide +kernel)
def pv91771 : PrimeValue := ⟨91771, pr91771⟩
private theorem pr91781 : PrimeCertificate 91781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv353]) (by decide +kernel)
def pv91781 : PrimeValue := ⟨91781, pr91781⟩
private theorem pr91801 : PrimeCertificate 91801 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv91801 : PrimeValue := ⟨91801, pr91801⟩
private theorem pr91807 : PrimeCertificate 91807 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv13,pv107]) (by decide +kernel)
def pv91807 : PrimeValue := ⟨91807, pr91807⟩
private theorem pr91811 : PrimeCertificate 91811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv9181]) (by decide +kernel)
def pv91811 : PrimeValue := ⟨91811, pr91811⟩
private theorem pr91813 : PrimeCertificate 91813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1093]) (by decide +kernel)
def pv91813 : PrimeValue := ⟨91813, pr91813⟩
private theorem pr91823 : PrimeCertificate 91823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv31,pv1481]) (by decide +kernel)
def pv91823 : PrimeValue := ⟨91823, pr91823⟩
private theorem pr91837 : PrimeCertificate 91837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv2551]) (by decide +kernel)
def pv91837 : PrimeValue := ⟨91837, pr91837⟩
private theorem pr91841 : PrimeCertificate 91841 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv41]) (by decide +kernel)
def pv91841 : PrimeValue := ⟨91841, pr91841⟩
private theorem pr91867 : PrimeCertificate 91867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61,pv251]) (by decide +kernel)
def pv91867 : PrimeValue := ⟨91867, pr91867⟩
private theorem pr91873 : PrimeCertificate 91873 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv29]) (by decide +kernel)
def pv91873 : PrimeValue := ⟨91873, pr91873⟩
private theorem pr91909 : PrimeCertificate 91909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv37]) (by decide +kernel)
def pv91909 : PrimeValue := ⟨91909, pr91909⟩
private theorem pr91921 : PrimeCertificate 91921 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv383]) (by decide +kernel)
def pv91921 : PrimeValue := ⟨91921, pr91921⟩
private theorem pr91939 : PrimeCertificate 91939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv199]) (by decide +kernel)
def pv91939 : PrimeValue := ⟨91939, pr91939⟩
private theorem pr91943 : PrimeCertificate 91943 :=
  certifyPrime (q := pv5) (ls := [pv2,pv45971]) (by decide +kernel)
def pv91943 : PrimeValue := ⟨91943, pr91943⟩
private theorem pr91951 : PrimeCertificate 91951 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv613]) (by decide +kernel)
def pv91951 : PrimeValue := ⟨91951, pr91951⟩
private theorem pr91957 : PrimeCertificate 91957 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv79,pv97]) (by decide +kernel)
def pv91957 : PrimeValue := ⟨91957, pr91957⟩
private theorem pr91961 : PrimeCertificate 91961 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv11,pv19]) (by decide +kernel)
def pv91961 : PrimeValue := ⟨91961, pr91961⟩
private theorem pr91969 : PrimeCertificate 91969 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv479]) (by decide +kernel)
def pv91969 : PrimeValue := ⟨91969, pr91969⟩
private theorem pr91997 : PrimeCertificate 91997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv109,pv211]) (by decide +kernel)
def pv91997 : PrimeValue := ⟨91997, pr91997⟩
private theorem pr92003 : PrimeCertificate 92003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv157,pv293]) (by decide +kernel)
def pv92003 : PrimeValue := ⟨92003, pr92003⟩
private theorem pr92009 : PrimeCertificate 92009 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv31,pv53]) (by decide +kernel)
def pv92009 : PrimeValue := ⟨92009, pr92009⟩
private theorem pr92033 : PrimeCertificate 92033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv719]) (by decide +kernel)
def pv92033 : PrimeValue := ⟨92033, pr92033⟩
private theorem pr92041 : PrimeCertificate 92041 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv13,pv59]) (by decide +kernel)
def pv92041 : PrimeValue := ⟨92041, pr92041⟩
private theorem pr92051 : PrimeCertificate 92051 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv263]) (by decide +kernel)
def pv92051 : PrimeValue := ⟨92051, pr92051⟩
private theorem pr92077 : PrimeCertificate 92077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7673]) (by decide +kernel)
def pv92077 : PrimeValue := ⟨92077, pr92077⟩
private theorem pr92083 : PrimeCertificate 92083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv103,pv149]) (by decide +kernel)
def pv92083 : PrimeValue := ⟨92083, pr92083⟩
private theorem pr92107 : PrimeCertificate 92107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv43]) (by decide +kernel)
def pv92107 : PrimeValue := ⟨92107, pr92107⟩
private theorem pr92111 : PrimeCertificate 92111 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv61,pv151]) (by decide +kernel)
def pv92111 : PrimeValue := ⟨92111, pr92111⟩
private theorem pr92119 : PrimeCertificate 92119 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv1181]) (by decide +kernel)
def pv92119 : PrimeValue := ⟨92119, pr92119⟩
private theorem pr92143 : PrimeCertificate 92143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv5119]) (by decide +kernel)
def pv92143 : PrimeValue := ⟨92143, pr92143⟩
private theorem pr92153 : PrimeCertificate 92153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11519]) (by decide +kernel)
def pv92153 : PrimeValue := ⟨92153, pr92153⟩
private theorem pr92173 : PrimeCertificate 92173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7681]) (by decide +kernel)
def pv92173 : PrimeValue := ⟨92173, pr92173⟩
private theorem pr92177 : PrimeCertificate 92177 :=
  certifyPrime (q := pv11) (ls := [pv2,pv7,pv823]) (by decide +kernel)
def pv92177 : PrimeValue := ⟨92177, pr92177⟩
private theorem pr92179 : PrimeCertificate 92179 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv569]) (by decide +kernel)
def pv92179 : PrimeValue := ⟨92179, pr92179⟩
private theorem pr92189 : PrimeCertificate 92189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv1213]) (by decide +kernel)
def pv92189 : PrimeValue := ⟨92189, pr92189⟩
private theorem pr92203 : PrimeCertificate 92203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv127]) (by decide +kernel)
def pv92203 : PrimeValue := ⟨92203, pr92203⟩
private theorem pr92219 : PrimeCertificate 92219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv941]) (by decide +kernel)
def pv92219 : PrimeValue := ⟨92219, pr92219⟩
private theorem pr92221 : PrimeCertificate 92221 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv29,pv53]) (by decide +kernel)
def pv92221 : PrimeValue := ⟨92221, pr92221⟩
private theorem pr92227 : PrimeCertificate 92227 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv809]) (by decide +kernel)
def pv92227 : PrimeValue := ⟨92227, pr92227⟩
private theorem pr92233 : PrimeCertificate 92233 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv61]) (by decide +kernel)
def pv92233 : PrimeValue := ⟨92233, pr92233⟩
private theorem pr92237 : PrimeCertificate 92237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23059]) (by decide +kernel)
def pv92237 : PrimeValue := ⟨92237, pr92237⟩
private theorem pr92243 : PrimeCertificate 92243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv2713]) (by decide +kernel)
def pv92243 : PrimeValue := ⟨92243, pr92243⟩
private theorem pr92251 : PrimeCertificate 92251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv41]) (by decide +kernel)
def pv92251 : PrimeValue := ⟨92251, pr92251⟩
private theorem pr92269 : PrimeCertificate 92269 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv233]) (by decide +kernel)
def pv92269 : PrimeValue := ⟨92269, pr92269⟩
private theorem pr92297 : PrimeCertificate 92297 :=
  certifyPrime (q := pv3) (ls := [pv2,pv83,pv139]) (by decide +kernel)
def pv92297 : PrimeValue := ⟨92297, pr92297⟩
private theorem pr92311 : PrimeCertificate 92311 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv17,pv181]) (by decide +kernel)
def pv92311 : PrimeValue := ⟨92311, pr92311⟩
private theorem pr92317 : PrimeCertificate 92317 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv157]) (by decide +kernel)
def pv92317 : PrimeValue := ⟨92317, pr92317⟩
private theorem pr92333 : PrimeCertificate 92333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv563]) (by decide +kernel)
def pv92333 : PrimeValue := ⟨92333, pr92333⟩
private theorem pr92347 : PrimeCertificate 92347 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv15391]) (by decide +kernel)
def pv92347 : PrimeValue := ⟨92347, pr92347⟩
private theorem pr92353 : PrimeCertificate 92353 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv37]) (by decide +kernel)
def pv92353 : PrimeValue := ⟨92353, pr92353⟩
private theorem pr92357 : PrimeCertificate 92357 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv2099]) (by decide +kernel)
def pv92357 : PrimeValue := ⟨92357, pr92357⟩
private theorem pr92363 : PrimeCertificate 92363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv46181]) (by decide +kernel)
def pv92363 : PrimeValue := ⟨92363, pr92363⟩
private theorem pr92369 : PrimeCertificate 92369 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv251]) (by decide +kernel)
def pv92369 : PrimeValue := ⟨92369, pr92369⟩
private theorem pr92377 : PrimeCertificate 92377 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1283]) (by decide +kernel)
def pv92377 : PrimeValue := ⟨92377, pr92377⟩
private theorem pr92381 : PrimeCertificate 92381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31,pv149]) (by decide +kernel)
def pv92381 : PrimeValue := ⟨92381, pr92381⟩
private theorem pr92383 : PrimeCertificate 92383 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv89,pv173]) (by decide +kernel)
def pv92383 : PrimeValue := ⟨92383, pr92383⟩
private theorem pr92387 : PrimeCertificate 92387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv6599]) (by decide +kernel)
def pv92387 : PrimeValue := ⟨92387, pr92387⟩
private theorem pr92399 : PrimeCertificate 92399 :=
  certifyPrime (q := pv13) (ls := [pv2,pv46199]) (by decide +kernel)
def pv92399 : PrimeValue := ⟨92399, pr92399⟩
private theorem pr92401 : PrimeCertificate 92401 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv5,pv7,pv11]) (by decide +kernel)
def pv92401 : PrimeValue := ⟨92401, pr92401⟩
private theorem pr92413 : PrimeCertificate 92413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv151]) (by decide +kernel)
def pv92413 : PrimeValue := ⟨92413, pr92413⟩
private theorem pr92419 : PrimeCertificate 92419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv73,pv211]) (by decide +kernel)
def pv92419 : PrimeValue := ⟨92419, pr92419⟩
private theorem pr92431 : PrimeCertificate 92431 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv5,pv13,pv79]) (by decide +kernel)
def pv92431 : PrimeValue := ⟨92431, pr92431⟩
private theorem pr92459 : PrimeCertificate 92459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv46229]) (by decide +kernel)
def pv92459 : PrimeValue := ⟨92459, pr92459⟩
private theorem pr92461 : PrimeCertificate 92461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv23,pv67]) (by decide +kernel)
def pv92461 : PrimeValue := ⟨92461, pr92461⟩
private theorem pr92467 : PrimeCertificate 92467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv467]) (by decide +kernel)
def pv92467 : PrimeValue := ⟨92467, pr92467⟩
private theorem pr92479 : PrimeCertificate 92479 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv15413]) (by decide +kernel)
def pv92479 : PrimeValue := ⟨92479, pr92479⟩
private theorem pr92489 : PrimeCertificate 92489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv1051]) (by decide +kernel)
def pv92489 : PrimeValue := ⟨92489, pr92489⟩
private theorem pr92503 : PrimeCertificate 92503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv571]) (by decide +kernel)
def pv92503 : PrimeValue := ⟨92503, pr92503⟩
private theorem pr92507 : PrimeCertificate 92507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv2011]) (by decide +kernel)
def pv92507 : PrimeValue := ⟨92507, pr92507⟩
private theorem pr92551 : PrimeCertificate 92551 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv617]) (by decide +kernel)
def pv92551 : PrimeValue := ⟨92551, pr92551⟩
private theorem pr92557 : PrimeCertificate 92557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv857]) (by decide +kernel)
def pv92557 : PrimeValue := ⟨92557, pr92557⟩
private theorem pr92569 : PrimeCertificate 92569 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv7,pv19,pv29]) (by decide +kernel)
def pv92569 : PrimeValue := ⟨92569, pr92569⟩
private theorem pr92581 : PrimeCertificate 92581 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv1543]) (by decide +kernel)
def pv92581 : PrimeValue := ⟨92581, pr92581⟩
private theorem pr92593 : PrimeCertificate 92593 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv643]) (by decide +kernel)
def pv92593 : PrimeValue := ⟨92593, pr92593⟩
private theorem pr92623 : PrimeCertificate 92623 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv43,pv359]) (by decide +kernel)
def pv92623 : PrimeValue := ⟨92623, pr92623⟩
private theorem pr92627 : PrimeCertificate 92627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv1597]) (by decide +kernel)
def pv92627 : PrimeValue := ⟨92627, pr92627⟩
private theorem pr92639 : PrimeCertificate 92639 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv13,pv509]) (by decide +kernel)
def pv92639 : PrimeValue := ⟨92639, pr92639⟩
private theorem pr92641 : PrimeCertificate 92641 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv193]) (by decide +kernel)
def pv92641 : PrimeValue := ⟨92641, pr92641⟩
private theorem pr92647 : PrimeCertificate 92647 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5147]) (by decide +kernel)
def pv92647 : PrimeValue := ⟨92647, pr92647⟩
private theorem pr92669 : PrimeCertificate 92669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23167]) (by decide +kernel)
def pv92669 : PrimeValue := ⟨92669, pr92669⟩
private theorem pr92671 : PrimeCertificate 92671 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv3089]) (by decide +kernel)
def pv92671 : PrimeValue := ⟨92671, pr92671⟩
private theorem pr92681 : PrimeCertificate 92681 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv331]) (by decide +kernel)
def pv92681 : PrimeValue := ⟨92681, pr92681⟩
private theorem pr92683 : PrimeCertificate 92683 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv271]) (by decide +kernel)
def pv92683 : PrimeValue := ⟨92683, pr92683⟩
private theorem pr92693 : PrimeCertificate 92693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23173]) (by decide +kernel)
def pv92693 : PrimeValue := ⟨92693, pr92693⟩
private theorem pr92699 : PrimeCertificate 92699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv46349]) (by decide +kernel)
def pv92699 : PrimeValue := ⟨92699, pr92699⟩
private theorem pr92707 : PrimeCertificate 92707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv15451]) (by decide +kernel)
def pv92707 : PrimeValue := ⟨92707, pr92707⟩
private theorem pr92717 : PrimeCertificate 92717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv1783]) (by decide +kernel)
def pv92717 : PrimeValue := ⟨92717, pr92717⟩
private theorem pr92723 : PrimeCertificate 92723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv37,pv179]) (by decide +kernel)
def pv92723 : PrimeValue := ⟨92723, pr92723⟩
private theorem pr92737 : PrimeCertificate 92737 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv23]) (by decide +kernel)
def pv92737 : PrimeValue := ⟨92737, pr92737⟩
private theorem pr92753 : PrimeCertificate 92753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv17,pv31]) (by decide +kernel)
def pv92753 : PrimeValue := ⟨92753, pr92753⟩
private theorem pr92761 : PrimeCertificate 92761 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv5,pv773]) (by decide +kernel)
def pv92761 : PrimeValue := ⟨92761, pr92761⟩
private theorem pr92767 : PrimeCertificate 92767 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv15461]) (by decide +kernel)
def pv92767 : PrimeValue := ⟨92767, pr92767⟩
private theorem pr92779 : PrimeCertificate 92779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv47]) (by decide +kernel)
def pv92779 : PrimeValue := ⟨92779, pr92779⟩
private theorem pr92789 : PrimeCertificate 92789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23197]) (by decide +kernel)
def pv92789 : PrimeValue := ⟨92789, pr92789⟩
private theorem pr92791 : PrimeCertificate 92791 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv1031]) (by decide +kernel)
def pv92791 : PrimeValue := ⟨92791, pr92791⟩
private theorem pr92801 : PrimeCertificate 92801 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv29]) (by decide +kernel)
def pv92801 : PrimeValue := ⟨92801, pr92801⟩
private theorem pr92809 : PrimeCertificate 92809 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv1289]) (by decide +kernel)
def pv92809 : PrimeValue := ⟨92809, pr92809⟩
private theorem pr92821 : PrimeCertificate 92821 :=
  certifyPrime (q := pv47) (ls := [pv2,pv3,pv5,pv7,pv13,pv17]) (by decide +kernel)
def pv92821 : PrimeValue := ⟨92821, pr92821⟩
private theorem pr92831 : PrimeCertificate 92831 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv9283]) (by decide +kernel)
def pv92831 : PrimeValue := ⟨92831, pr92831⟩
private theorem pr92849 : PrimeCertificate 92849 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv829]) (by decide +kernel)
def pv92849 : PrimeValue := ⟨92849, pr92849⟩
private theorem pr92857 : PrimeCertificate 92857 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv53,pv73]) (by decide +kernel)
def pv92857 : PrimeValue := ⟨92857, pr92857⟩
private theorem pr92861 : PrimeCertificate 92861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv4643]) (by decide +kernel)
def pv92861 : PrimeValue := ⟨92861, pr92861⟩
private theorem pr92863 : PrimeCertificate 92863 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv11,pv67]) (by decide +kernel)
def pv92863 : PrimeValue := ⟨92863, pr92863⟩
private theorem pr92867 : PrimeCertificate 92867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59,pv787]) (by decide +kernel)
def pv92867 : PrimeValue := ⟨92867, pr92867⟩
private theorem pr92893 : PrimeCertificate 92893 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7741]) (by decide +kernel)
def pv92893 : PrimeValue := ⟨92893, pr92893⟩
private theorem pr92899 : PrimeCertificate 92899 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv397]) (by decide +kernel)
def pv92899 : PrimeValue := ⟨92899, pr92899⟩
private theorem pr92921 : PrimeCertificate 92921 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv23,pv101]) (by decide +kernel)
def pv92921 : PrimeValue := ⟨92921, pr92921⟩
private theorem pr92927 : PrimeCertificate 92927 :=
  certifyPrime (q := pv5) (ls := [pv2,pv97,pv479]) (by decide +kernel)
def pv92927 : PrimeValue := ⟨92927, pr92927⟩
private theorem pr92941 : PrimeCertificate 92941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1549]) (by decide +kernel)
def pv92941 : PrimeValue := ⟨92941, pr92941⟩
private theorem pr92951 : PrimeCertificate 92951 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv13]) (by decide +kernel)
def pv92951 : PrimeValue := ⟨92951, pr92951⟩
private theorem pr92957 : PrimeCertificate 92957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv1367]) (by decide +kernel)
def pv92957 : PrimeValue := ⟨92957, pr92957⟩
private theorem pr92959 : PrimeCertificate 92959 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv15493]) (by decide +kernel)
def pv92959 : PrimeValue := ⟨92959, pr92959⟩
private theorem pr92987 : PrimeCertificate 92987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv2447]) (by decide +kernel)
def pv92987 : PrimeValue := ⟨92987, pr92987⟩
private theorem pr92993 : PrimeCertificate 92993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1453]) (by decide +kernel)
def pv92993 : PrimeValue := ⟨92993, pr92993⟩
private theorem pr93001 : PrimeCertificate 93001 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv31]) (by decide +kernel)
def pv93001 : PrimeValue := ⟨93001, pr93001⟩
private theorem pr93047 : PrimeCertificate 93047 :=
  certifyPrime (q := pv5) (ls := [pv2,pv46523]) (by decide +kernel)
def pv93047 : PrimeValue := ⟨93047, pr93047⟩
private theorem pr93053 : PrimeCertificate 93053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv541]) (by decide +kernel)
def pv93053 : PrimeValue := ⟨93053, pr93053⟩
private theorem pr93059 : PrimeCertificate 93059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv17,pv23]) (by decide +kernel)
def pv93059 : PrimeValue := ⟨93059, pr93059⟩
private theorem pr93077 : PrimeCertificate 93077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23269]) (by decide +kernel)
def pv93077 : PrimeValue := ⟨93077, pr93077⟩
private theorem pr93083 : PrimeCertificate 93083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv4231]) (by decide +kernel)
def pv93083 : PrimeValue := ⟨93083, pr93083⟩
private theorem pr93089 : PrimeCertificate 93089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2909]) (by decide +kernel)
def pv93089 : PrimeValue := ⟨93089, pr93089⟩
private theorem pr93097 : PrimeCertificate 93097 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv431]) (by decide +kernel)
def pv93097 : PrimeValue := ⟨93097, pr93097⟩
private theorem pr93103 : PrimeCertificate 93103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv59,pv263]) (by decide +kernel)
def pv93103 : PrimeValue := ⟨93103, pr93103⟩
private theorem pr93113 : PrimeCertificate 93113 :=
  certifyPrime (q := pv3) (ls := [pv2,pv103,pv113]) (by decide +kernel)
def pv93113 : PrimeValue := ⟨93113, pr93113⟩
private theorem pr93131 : PrimeCertificate 93131 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv67,pv139]) (by decide +kernel)
def pv93131 : PrimeValue := ⟨93131, pr93131⟩
private theorem pr93133 : PrimeCertificate 93133 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv199]) (by decide +kernel)
def pv93133 : PrimeValue := ⟨93133, pr93133⟩
private theorem pr93151 : PrimeCertificate 93151 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv23]) (by decide +kernel)
def pv93151 : PrimeValue := ⟨93151, pr93151⟩
private theorem pr93169 : PrimeCertificate 93169 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv647]) (by decide +kernel)
def pv93169 : PrimeValue := ⟨93169, pr93169⟩
private theorem pr93179 : PrimeCertificate 93179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv46589]) (by decide +kernel)
def pv93179 : PrimeValue := ⟨93179, pr93179⟩
private theorem pr93187 : PrimeCertificate 93187 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31,pv167]) (by decide +kernel)
def pv93187 : PrimeValue := ⟨93187, pr93187⟩
private theorem pr93199 : PrimeCertificate 93199 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv317]) (by decide +kernel)
def pv93199 : PrimeValue := ⟨93199, pr93199⟩
private theorem pr93229 : PrimeCertificate 93229 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv17,pv457]) (by decide +kernel)
def pv93229 : PrimeValue := ⟨93229, pr93229⟩
private theorem pr93239 : PrimeCertificate 93239 :=
  certifyPrime (q := pv11) (ls := [pv2,pv46619]) (by decide +kernel)
def pv93239 : PrimeValue := ⟨93239, pr93239⟩
private theorem pr93241 : PrimeCertificate 93241 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv37]) (by decide +kernel)
def pv93241 : PrimeValue := ⟨93241, pr93241⟩
private theorem pr93251 : PrimeCertificate 93251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv373]) (by decide +kernel)
def pv93251 : PrimeValue := ⟨93251, pr93251⟩
private theorem pr93253 : PrimeCertificate 93253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv409]) (by decide +kernel)
def pv93253 : PrimeValue := ⟨93253, pr93253⟩
private theorem pr93257 : PrimeCertificate 93257 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11657]) (by decide +kernel)
def pv93257 : PrimeValue := ⟨93257, pr93257⟩
private theorem pr93263 : PrimeCertificate 93263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv17,pv211]) (by decide +kernel)
def pv93263 : PrimeValue := ⟨93263, pr93263⟩
private theorem pr93281 : PrimeCertificate 93281 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv53]) (by decide +kernel)
def pv93281 : PrimeValue := ⟨93281, pr93281⟩
private theorem pr93283 : PrimeCertificate 93283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv2221]) (by decide +kernel)
def pv93283 : PrimeValue := ⟨93283, pr93283⟩
private theorem pr93287 : PrimeCertificate 93287 :=
  certifyPrime (q := pv5) (ls := [pv2,pv46643]) (by decide +kernel)
def pv93287 : PrimeValue := ⟨93287, pr93287⟩
private theorem pr93307 : PrimeCertificate 93307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv15551]) (by decide +kernel)
def pv93307 : PrimeValue := ⟨93307, pr93307⟩
private theorem pr93319 : PrimeCertificate 93319 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv103,pv151]) (by decide +kernel)
def pv93319 : PrimeValue := ⟨93319, pr93319⟩
private theorem pr93323 : PrimeCertificate 93323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv1609]) (by decide +kernel)
def pv93323 : PrimeValue := ⟨93323, pr93323⟩
private theorem pr93329 : PrimeCertificate 93329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv307]) (by decide +kernel)
def pv93329 : PrimeValue := ⟨93329, pr93329⟩
private theorem pr93337 : PrimeCertificate 93337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3889]) (by decide +kernel)
def pv93337 : PrimeValue := ⟨93337, pr93337⟩
private theorem pr93371 : PrimeCertificate 93371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv9337]) (by decide +kernel)
def pv93371 : PrimeValue := ⟨93371, pr93371⟩
private theorem pr93377 : PrimeCertificate 93377 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1459]) (by decide +kernel)
def pv93377 : PrimeValue := ⟨93377, pr93377⟩
private theorem pr93383 : PrimeCertificate 93383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv46691]) (by decide +kernel)
def pv93383 : PrimeValue := ⟨93383, pr93383⟩
private theorem pr93407 : PrimeCertificate 93407 :=
  certifyPrime (q := pv5) (ls := [pv2,pv46703]) (by decide +kernel)
def pv93407 : PrimeValue := ⟨93407, pr93407⟩
private theorem pr93419 : PrimeCertificate 93419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv3593]) (by decide +kernel)
def pv93419 : PrimeValue := ⟨93419, pr93419⟩
private theorem pr93427 : PrimeCertificate 93427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv677]) (by decide +kernel)
def pv93427 : PrimeValue := ⟨93427, pr93427⟩
private theorem pr93463 : PrimeCertificate 93463 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37,pv421]) (by decide +kernel)
def pv93463 : PrimeValue := ⟨93463, pr93463⟩
private theorem pr93479 : PrimeCertificate 93479 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv11,pv607]) (by decide +kernel)
def pv93479 : PrimeValue := ⟨93479, pr93479⟩
private theorem pr93481 : PrimeCertificate 93481 :=
  certifyPrime (q := pv107) (ls := [pv2,pv3,pv5,pv19,pv41]) (by decide +kernel)
def pv93481 : PrimeValue := ⟨93481, pr93481⟩
private theorem pr93487 : PrimeCertificate 93487 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv15581]) (by decide +kernel)
def pv93487 : PrimeValue := ⟨93487, pr93487⟩
private theorem pr93491 : PrimeCertificate 93491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv9349]) (by decide +kernel)
def pv93491 : PrimeValue := ⟨93491, pr93491⟩
private theorem pr93493 : PrimeCertificate 93493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv53]) (by decide +kernel)
def pv93493 : PrimeValue := ⟨93493, pr93493⟩
private theorem pr93497 : PrimeCertificate 93497 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv29,pv31]) (by decide +kernel)
def pv93497 : PrimeValue := ⟨93497, pr93497⟩
private theorem pr93503 : PrimeCertificate 93503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv46751]) (by decide +kernel)
def pv93503 : PrimeValue := ⟨93503, pr93503⟩
private theorem pr93523 : PrimeCertificate 93523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv13,pv109]) (by decide +kernel)
def pv93523 : PrimeValue := ⟨93523, pr93523⟩
private theorem pr93529 : PrimeCertificate 93529 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv433]) (by decide +kernel)
def pv93529 : PrimeValue := ⟨93529, pr93529⟩
private theorem pr93553 : PrimeCertificate 93553 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1949]) (by decide +kernel)
def pv93553 : PrimeValue := ⟨93553, pr93553⟩
private theorem pr93557 : PrimeCertificate 93557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv1231]) (by decide +kernel)
def pv93557 : PrimeValue := ⟨93557, pr93557⟩
private theorem pr93559 : PrimeCertificate 93559 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31,pv503]) (by decide +kernel)
def pv93559 : PrimeValue := ⟨93559, pr93559⟩
private theorem pr93563 : PrimeCertificate 93563 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv41,pv163]) (by decide +kernel)
def pv93563 : PrimeValue := ⟨93563, pr93563⟩
private theorem pr93581 : PrimeCertificate 93581 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv4679]) (by decide +kernel)
def pv93581 : PrimeValue := ⟨93581, pr93581⟩
private theorem pr93601 : PrimeCertificate 93601 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv93601 : PrimeValue := ⟨93601, pr93601⟩
private theorem pr93629 : PrimeCertificate 93629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89,pv263]) (by decide +kernel)
def pv93629 : PrimeValue := ⟨93629, pr93629⟩
private theorem pr93637 : PrimeCertificate 93637 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17]) (by decide +kernel)
def pv93637 : PrimeValue := ⟨93637, pr93637⟩
private theorem pr93683 : PrimeCertificate 93683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv1511]) (by decide +kernel)
def pv93683 : PrimeValue := ⟨93683, pr93683⟩
private theorem pr93701 : PrimeCertificate 93701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv937]) (by decide +kernel)
def pv93701 : PrimeValue := ⟨93701, pr93701⟩
private theorem pr93703 : PrimeCertificate 93703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv23,pv97]) (by decide +kernel)
def pv93703 : PrimeValue := ⟨93703, pr93703⟩
private theorem pr93719 : PrimeCertificate 93719 :=
  certifyPrime (q := pv13) (ls := [pv2,pv47,pv997]) (by decide +kernel)
def pv93719 : PrimeValue := ⟨93719, pr93719⟩
private theorem pr93739 : PrimeCertificate 93739 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv919]) (by decide +kernel)
def pv93739 : PrimeValue := ⟨93739, pr93739⟩
private theorem pr93763 : PrimeCertificate 93763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5209]) (by decide +kernel)
def pv93763 : PrimeValue := ⟨93763, pr93763⟩
private theorem pr93787 : PrimeCertificate 93787 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv11,pv29]) (by decide +kernel)
def pv93787 : PrimeValue := ⟨93787, pr93787⟩
private theorem pr93809 : PrimeCertificate 93809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv13,pv41]) (by decide +kernel)
def pv93809 : PrimeValue := ⟨93809, pr93809⟩
private theorem pr93827 : PrimeCertificate 93827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv1091]) (by decide +kernel)
def pv93827 : PrimeValue := ⟨93827, pr93827⟩
private theorem pr93851 : PrimeCertificate 93851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1877]) (by decide +kernel)
def pv93851 : PrimeValue := ⟨93851, pr93851⟩
private theorem pr93871 : PrimeCertificate 93871 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv149]) (by decide +kernel)
def pv93871 : PrimeValue := ⟨93871, pr93871⟩
private theorem pr93887 : PrimeCertificate 93887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv23,pv157]) (by decide +kernel)
def pv93887 : PrimeValue := ⟨93887, pr93887⟩
private theorem pr93889 : PrimeCertificate 93889 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv163]) (by decide +kernel)
def pv93889 : PrimeValue := ⟨93889, pr93889⟩
private theorem pr93893 : PrimeCertificate 93893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23473]) (by decide +kernel)
def pv93893 : PrimeValue := ⟨93893, pr93893⟩
private theorem pr93901 : PrimeCertificate 93901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv313]) (by decide +kernel)
def pv93901 : PrimeValue := ⟨93901, pr93901⟩
private theorem pr93911 : PrimeCertificate 93911 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv9391]) (by decide +kernel)
def pv93911 : PrimeValue := ⟨93911, pr93911⟩
private theorem pr93913 : PrimeCertificate 93913 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv43]) (by decide +kernel)
def pv93913 : PrimeValue := ⟨93913, pr93913⟩
private theorem pr93937 : PrimeCertificate 93937 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv19,pv103]) (by decide +kernel)
def pv93937 : PrimeValue := ⟨93937, pr93937⟩
private theorem pr93941 : PrimeCertificate 93941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv61]) (by decide +kernel)
def pv93941 : PrimeValue := ⟨93941, pr93941⟩
private theorem pr93949 : PrimeCertificate 93949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7829]) (by decide +kernel)
def pv93949 : PrimeValue := ⟨93949, pr93949⟩
private theorem pr93967 : PrimeCertificate 93967 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv15661]) (by decide +kernel)
def pv93967 : PrimeValue := ⟨93967, pr93967⟩
private theorem pr93971 : PrimeCertificate 93971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv9397]) (by decide +kernel)
def pv93971 : PrimeValue := ⟨93971, pr93971⟩
private theorem pr93979 : PrimeCertificate 93979 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv227]) (by decide +kernel)
def pv93979 : PrimeValue := ⟨93979, pr93979⟩
private theorem pr93983 : PrimeCertificate 93983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv137]) (by decide +kernel)
def pv93983 : PrimeValue := ⟨93983, pr93983⟩
private theorem pr93997 : PrimeCertificate 93997 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv373]) (by decide +kernel)
def pv93997 : PrimeValue := ⟨93997, pr93997⟩
private theorem pr94007 : PrimeCertificate 94007 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv4273]) (by decide +kernel)
def pv94007 : PrimeValue := ⟨94007, pr94007⟩
private theorem pr94009 : PrimeCertificate 94009 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv3917]) (by decide +kernel)
def pv94009 : PrimeValue := ⟨94009, pr94009⟩
private theorem pr94033 : PrimeCertificate 94033 :=
  certifyPrime (q := pv47) (ls := [pv2,pv3,pv653]) (by decide +kernel)
def pv94033 : PrimeValue := ⟨94033, pr94033⟩
private theorem pr94049 : PrimeCertificate 94049 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2939]) (by decide +kernel)
def pv94049 : PrimeValue := ⟨94049, pr94049⟩
private theorem pr94057 : PrimeCertificate 94057 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv3919]) (by decide +kernel)
def pv94057 : PrimeValue := ⟨94057, pr94057⟩
private theorem pr94063 : PrimeCertificate 94063 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv61,pv257]) (by decide +kernel)
def pv94063 : PrimeValue := ⟨94063, pr94063⟩
private theorem pr94079 : PrimeCertificate 94079 :=
  certifyPrime (q := pv13) (ls := [pv2,pv17,pv2767]) (by decide +kernel)
def pv94079 : PrimeValue := ⟨94079, pr94079⟩
private theorem pr94099 : PrimeCertificate 94099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv15683]) (by decide +kernel)
def pv94099 : PrimeValue := ⟨94099, pr94099⟩
private theorem pr94109 : PrimeCertificate 94109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv3361]) (by decide +kernel)
def pv94109 : PrimeValue := ⟨94109, pr94109⟩
private theorem pr94111 : PrimeCertificate 94111 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv3137]) (by decide +kernel)
def pv94111 : PrimeValue := ⟨94111, pr94111⟩
private theorem pr94117 : PrimeCertificate 94117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv23,pv31]) (by decide +kernel)
def pv94117 : PrimeValue := ⟨94117, pr94117⟩
private theorem pr94121 : PrimeCertificate 94121 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv181]) (by decide +kernel)
def pv94121 : PrimeValue := ⟨94121, pr94121⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
