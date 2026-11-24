/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table010
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table010.pv22343
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table005

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr22343 : Nat.Prime 22343 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11171]) (by decide +kernel)
def pv22343 : PrimeValue := ⟨22343, pr22343⟩
private theorem pr22349 : Nat.Prime 22349 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv151]) (by decide +kernel)
def pv22349 : PrimeValue := ⟨22349, pr22349⟩
private theorem pr22367 : Nat.Prime 22367 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv53,pv211]) (by decide +kernel)
def pv22367 : PrimeValue := ⟨22367, pr22367⟩
private theorem pr22369 : Nat.Prime 22369 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv233]) (by decide +kernel)
def pv22369 : PrimeValue := ⟨22369, pr22369⟩
private theorem pr22381 : Nat.Prime 22381 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv373]) (by decide +kernel)
def pv22381 : PrimeValue := ⟨22381, pr22381⟩
private theorem pr22391 : Nat.Prime 22391 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv2239]) (by decide +kernel)
def pv22391 : PrimeValue := ⟨22391, pr22391⟩
private theorem pr22397 : Nat.Prime 22397 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv509]) (by decide +kernel)
def pv22397 : PrimeValue := ⟨22397, pr22397⟩
private theorem pr22409 : Nat.Prime 22409 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2801]) (by decide +kernel)
def pv22409 : PrimeValue := ⟨22409, pr22409⟩
private theorem pr22433 : Nat.Prime 22433 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv701]) (by decide +kernel)
def pv22433 : PrimeValue := ⟨22433, pr22433⟩
private theorem pr22441 : Nat.Prime 22441 :=
  checkPrime_prime (q := pv47) (ls := [pv2,pv3,pv5,pv11,pv17]) (by decide +kernel)
def pv22441 : PrimeValue := ⟨22441, pr22441⟩
private theorem pr22447 : Nat.Prime 22447 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv29,pv43]) (by decide +kernel)
def pv22447 : PrimeValue := ⟨22447, pr22447⟩
private theorem pr22453 : Nat.Prime 22453 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1871]) (by decide +kernel)
def pv22453 : PrimeValue := ⟨22453, pr22453⟩
private theorem pr22469 : Nat.Prime 22469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv41,pv137]) (by decide +kernel)
def pv22469 : PrimeValue := ⟨22469, pr22469⟩
private theorem pr22481 : Nat.Prime 22481 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv281]) (by decide +kernel)
def pv22481 : PrimeValue := ⟨22481, pr22481⟩
private theorem pr22483 : Nat.Prime 22483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1249]) (by decide +kernel)
def pv22483 : PrimeValue := ⟨22483, pr22483⟩
private theorem pr22501 : Nat.Prime 22501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv22501 : PrimeValue := ⟨22501, pr22501⟩
private theorem pr22511 : Nat.Prime 22511 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv2251]) (by decide +kernel)
def pv22511 : PrimeValue := ⟨22511, pr22511⟩
private theorem pr22531 : Nat.Prime 22531 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv751]) (by decide +kernel)
def pv22531 : PrimeValue := ⟨22531, pr22531⟩
private theorem pr22541 : Nat.Prime 22541 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv23]) (by decide +kernel)
def pv22541 : PrimeValue := ⟨22541, pr22541⟩
private theorem pr22543 : Nat.Prime 22543 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv17]) (by decide +kernel)
def pv22543 : PrimeValue := ⟨22543, pr22543⟩
private theorem pr22549 : Nat.Prime 22549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1879]) (by decide +kernel)
def pv22549 : PrimeValue := ⟨22549, pr22549⟩
private theorem pr22567 : Nat.Prime 22567 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv3761]) (by decide +kernel)
def pv22567 : PrimeValue := ⟨22567, pr22567⟩
private theorem pr22571 : Nat.Prime 22571 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv37,pv61]) (by decide +kernel)
def pv22571 : PrimeValue := ⟨22571, pr22571⟩
private theorem pr22573 : Nat.Prime 22573 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv19]) (by decide +kernel)
def pv22573 : PrimeValue := ⟨22573, pr22573⟩
private theorem pr22613 : Nat.Prime 22613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5653]) (by decide +kernel)
def pv22613 : PrimeValue := ⟨22613, pr22613⟩
private theorem pr22619 : Nat.Prime 22619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv263]) (by decide +kernel)
def pv22619 : PrimeValue := ⟨22619, pr22619⟩
private theorem pr22621 : Nat.Prime 22621 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv29]) (by decide +kernel)
def pv22621 : PrimeValue := ⟨22621, pr22621⟩
private theorem pr22637 : Nat.Prime 22637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5659]) (by decide +kernel)
def pv22637 : PrimeValue := ⟨22637, pr22637⟩
private theorem pr22639 : Nat.Prime 22639 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv11]) (by decide +kernel)
def pv22639 : PrimeValue := ⟨22639, pr22639⟩
private theorem pr22643 : Nat.Prime 22643 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11321]) (by decide +kernel)
def pv22643 : PrimeValue := ⟨22643, pr22643⟩
private theorem pr22651 : Nat.Prime 22651 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv151]) (by decide +kernel)
def pv22651 : PrimeValue := ⟨22651, pr22651⟩
private theorem pr22669 : Nat.Prime 22669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1889]) (by decide +kernel)
def pv22669 : PrimeValue := ⟨22669, pr22669⟩
private theorem pr22679 : Nat.Prime 22679 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv17,pv23,pv29]) (by decide +kernel)
def pv22679 : PrimeValue := ⟨22679, pr22679⟩
private theorem pr22691 : Nat.Prime 22691 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv2269]) (by decide +kernel)
def pv22691 : PrimeValue := ⟨22691, pr22691⟩
private theorem pr22697 : Nat.Prime 22697 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2837]) (by decide +kernel)
def pv22697 : PrimeValue := ⟨22697, pr22697⟩
private theorem pr22699 : Nat.Prime 22699 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv13,pv97]) (by decide +kernel)
def pv22699 : PrimeValue := ⟨22699, pr22699⟩
private theorem pr22709 : Nat.Prime 22709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv811]) (by decide +kernel)
def pv22709 : PrimeValue := ⟨22709, pr22709⟩
private theorem pr22717 : Nat.Prime 22717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv631]) (by decide +kernel)
def pv22717 : PrimeValue := ⟨22717, pr22717⟩
private theorem pr22721 : Nat.Prime 22721 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv71]) (by decide +kernel)
def pv22721 : PrimeValue := ⟨22721, pr22721⟩
private theorem pr22727 : Nat.Prime 22727 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv1033]) (by decide +kernel)
def pv22727 : PrimeValue := ⟨22727, pr22727⟩
private theorem pr22739 : Nat.Prime 22739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11369]) (by decide +kernel)
def pv22739 : PrimeValue := ⟨22739, pr22739⟩
private theorem pr22741 : Nat.Prime 22741 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv379]) (by decide +kernel)
def pv22741 : PrimeValue := ⟨22741, pr22741⟩
private theorem pr22751 : Nat.Prime 22751 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv5,pv7,pv13]) (by decide +kernel)
def pv22751 : PrimeValue := ⟨22751, pr22751⟩
private theorem pr22769 : Nat.Prime 22769 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1423]) (by decide +kernel)
def pv22769 : PrimeValue := ⟨22769, pr22769⟩
private theorem pr22777 : Nat.Prime 22777 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv73]) (by decide +kernel)
def pv22777 : PrimeValue := ⟨22777, pr22777⟩
private theorem pr22783 : Nat.Prime 22783 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv3797]) (by decide +kernel)
def pv22783 : PrimeValue := ⟨22783, pr22783⟩
private theorem pr22787 : Nat.Prime 22787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11393]) (by decide +kernel)
def pv22787 : PrimeValue := ⟨22787, pr22787⟩
private theorem pr22807 : Nat.Prime 22807 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv181]) (by decide +kernel)
def pv22807 : PrimeValue := ⟨22807, pr22807⟩
private theorem pr22811 : Nat.Prime 22811 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv2281]) (by decide +kernel)
def pv22811 : PrimeValue := ⟨22811, pr22811⟩
private theorem pr22817 : Nat.Prime 22817 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv31]) (by decide +kernel)
def pv22817 : PrimeValue := ⟨22817, pr22817⟩
private theorem pr22853 : Nat.Prime 22853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv197]) (by decide +kernel)
def pv22853 : PrimeValue := ⟨22853, pr22853⟩
private theorem pr22859 : Nat.Prime 22859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv1039]) (by decide +kernel)
def pv22859 : PrimeValue := ⟨22859, pr22859⟩
private theorem pr22861 : Nat.Prime 22861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv127]) (by decide +kernel)
def pv22861 : PrimeValue := ⟨22861, pr22861⟩
private theorem pr22871 : Nat.Prime 22871 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv2287]) (by decide +kernel)
def pv22871 : PrimeValue := ⟨22871, pr22871⟩
private theorem pr22877 : Nat.Prime 22877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv19,pv43]) (by decide +kernel)
def pv22877 : PrimeValue := ⟨22877, pr22877⟩
private theorem pr22901 : Nat.Prime 22901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv229]) (by decide +kernel)
def pv22901 : PrimeValue := ⟨22901, pr22901⟩
private theorem pr22907 : Nat.Prime 22907 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv881]) (by decide +kernel)
def pv22907 : PrimeValue := ⟨22907, pr22907⟩
private theorem pr22921 : Nat.Prime 22921 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv191]) (by decide +kernel)
def pv22921 : PrimeValue := ⟨22921, pr22921⟩
private theorem pr22937 : Nat.Prime 22937 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv47,pv61]) (by decide +kernel)
def pv22937 : PrimeValue := ⟨22937, pr22937⟩
private theorem pr22943 : Nat.Prime 22943 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11471]) (by decide +kernel)
def pv22943 : PrimeValue := ⟨22943, pr22943⟩
private theorem pr22961 : Nat.Prime 22961 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv7,pv41]) (by decide +kernel)
def pv22961 : PrimeValue := ⟨22961, pr22961⟩
private theorem pr22963 : Nat.Prime 22963 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv43,pv89]) (by decide +kernel)
def pv22963 : PrimeValue := ⟨22963, pr22963⟩
private theorem pr22973 : Nat.Prime 22973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5743]) (by decide +kernel)
def pv22973 : PrimeValue := ⟨22973, pr22973⟩
private theorem pr22993 : Nat.Prime 22993 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv479]) (by decide +kernel)
def pv22993 : PrimeValue := ⟨22993, pr22993⟩
private theorem pr23003 : Nat.Prime 23003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv31,pv53]) (by decide +kernel)
def pv23003 : PrimeValue := ⟨23003, pr23003⟩
private theorem pr23011 : Nat.Prime 23011 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv13,pv59]) (by decide +kernel)
def pv23011 : PrimeValue := ⟨23011, pr23011⟩
private theorem pr23017 : Nat.Prime 23017 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv137]) (by decide +kernel)
def pv23017 : PrimeValue := ⟨23017, pr23017⟩
private theorem pr23021 : Nat.Prime 23021 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1151]) (by decide +kernel)
def pv23021 : PrimeValue := ⟨23021, pr23021⟩
private theorem pr23027 : Nat.Prime 23027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv397]) (by decide +kernel)
def pv23027 : PrimeValue := ⟨23027, pr23027⟩
private theorem pr23029 : Nat.Prime 23029 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv101]) (by decide +kernel)
def pv23029 : PrimeValue := ⟨23029, pr23029⟩
private theorem pr23039 : Nat.Prime 23039 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11519]) (by decide +kernel)
def pv23039 : PrimeValue := ⟨23039, pr23039⟩
private theorem pr23041 : Nat.Prime 23041 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv23041 : PrimeValue := ⟨23041, pr23041⟩
private theorem pr23053 : Nat.Prime 23053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv113]) (by decide +kernel)
def pv23053 : PrimeValue := ⟨23053, pr23053⟩
private theorem pr23057 : Nat.Prime 23057 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv131]) (by decide +kernel)
def pv23057 : PrimeValue := ⟨23057, pr23057⟩
private theorem pr23059 : Nat.Prime 23059 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv61]) (by decide +kernel)
def pv23059 : PrimeValue := ⟨23059, pr23059⟩
private theorem pr23063 : Nat.Prime 23063 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv887]) (by decide +kernel)
def pv23063 : PrimeValue := ⟨23063, pr23063⟩
private theorem pr23071 : Nat.Prime 23071 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv769]) (by decide +kernel)
def pv23071 : PrimeValue := ⟨23071, pr23071⟩
private theorem pr23081 : Nat.Prime 23081 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv577]) (by decide +kernel)
def pv23081 : PrimeValue := ⟨23081, pr23081⟩
private theorem pr23087 : Nat.Prime 23087 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv17,pv97]) (by decide +kernel)
def pv23087 : PrimeValue := ⟨23087, pr23087⟩
private theorem pr23099 : Nat.Prime 23099 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11549]) (by decide +kernel)
def pv23099 : PrimeValue := ⟨23099, pr23099⟩
private theorem pr23117 : Nat.Prime 23117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5779]) (by decide +kernel)
def pv23117 : PrimeValue := ⟨23117, pr23117⟩
private theorem pr23131 : Nat.Prime 23131 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv257]) (by decide +kernel)
def pv23131 : PrimeValue := ⟨23131, pr23131⟩
private theorem pr23143 : Nat.Prime 23143 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv19,pv29]) (by decide +kernel)
def pv23143 : PrimeValue := ⟨23143, pr23143⟩
private theorem pr23159 : Nat.Prime 23159 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv11579]) (by decide +kernel)
def pv23159 : PrimeValue := ⟨23159, pr23159⟩
private theorem pr23167 : Nat.Prime 23167 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv13]) (by decide +kernel)
def pv23167 : PrimeValue := ⟨23167, pr23167⟩
private theorem pr23173 : Nat.Prime 23173 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1931]) (by decide +kernel)
def pv23173 : PrimeValue := ⟨23173, pr23173⟩
private theorem pr23189 : Nat.Prime 23189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv17,pv31]) (by decide +kernel)
def pv23189 : PrimeValue := ⟨23189, pr23189⟩
private theorem pr23197 : Nat.Prime 23197 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1933]) (by decide +kernel)
def pv23197 : PrimeValue := ⟨23197, pr23197⟩
private theorem pr23201 : Nat.Prime 23201 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv29]) (by decide +kernel)
def pv23201 : PrimeValue := ⟨23201, pr23201⟩
private theorem pr23203 : Nat.Prime 23203 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv1289]) (by decide +kernel)
def pv23203 : PrimeValue := ⟨23203, pr23203⟩
private theorem pr23209 : Nat.Prime 23209 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv967]) (by decide +kernel)
def pv23209 : PrimeValue := ⟨23209, pr23209⟩
private theorem pr23227 : Nat.Prime 23227 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv79]) (by decide +kernel)
def pv23227 : PrimeValue := ⟨23227, pr23227⟩
private theorem pr23251 : Nat.Prime 23251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv31]) (by decide +kernel)
def pv23251 : PrimeValue := ⟨23251, pr23251⟩
private theorem pr23269 : Nat.Prime 23269 :=
  checkPrime_prime (q := pv53) (ls := [pv2,pv3,pv7,pv277]) (by decide +kernel)
def pv23269 : PrimeValue := ⟨23269, pr23269⟩
private theorem pr23279 : Nat.Prime 23279 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv103,pv113]) (by decide +kernel)
def pv23279 : PrimeValue := ⟨23279, pr23279⟩
private theorem pr23291 : Nat.Prime 23291 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv17,pv137]) (by decide +kernel)
def pv23291 : PrimeValue := ⟨23291, pr23291⟩
private theorem pr23293 : Nat.Prime 23293 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv647]) (by decide +kernel)
def pv23293 : PrimeValue := ⟨23293, pr23293⟩
private theorem pr23297 : Nat.Prime 23297 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv13]) (by decide +kernel)
def pv23297 : PrimeValue := ⟨23297, pr23297⟩
private theorem pr23311 : Nat.Prime 23311 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv37]) (by decide +kernel)
def pv23311 : PrimeValue := ⟨23311, pr23311⟩
private theorem pr23321 : Nat.Prime 23321 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv53]) (by decide +kernel)
def pv23321 : PrimeValue := ⟨23321, pr23321⟩
private theorem pr23327 : Nat.Prime 23327 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv107,pv109]) (by decide +kernel)
def pv23327 : PrimeValue := ⟨23327, pr23327⟩
private theorem pr23333 : Nat.Prime 23333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv307]) (by decide +kernel)
def pv23333 : PrimeValue := ⟨23333, pr23333⟩
private theorem pr23339 : Nat.Prime 23339 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv1667]) (by decide +kernel)
def pv23339 : PrimeValue := ⟨23339, pr23339⟩
private theorem pr23357 : Nat.Prime 23357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5839]) (by decide +kernel)
def pv23357 : PrimeValue := ⟨23357, pr23357⟩
private theorem pr23369 : Nat.Prime 23369 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv127]) (by decide +kernel)
def pv23369 : PrimeValue := ⟨23369, pr23369⟩
private theorem pr23371 : Nat.Prime 23371 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv41]) (by decide +kernel)
def pv23371 : PrimeValue := ⟨23371, pr23371⟩
private theorem pr23399 : Nat.Prime 23399 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv11699]) (by decide +kernel)
def pv23399 : PrimeValue := ⟨23399, pr23399⟩
private theorem pr23417 : Nat.Prime 23417 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2927]) (by decide +kernel)
def pv23417 : PrimeValue := ⟨23417, pr23417⟩
private theorem pr23431 : Nat.Prime 23431 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv71]) (by decide +kernel)
def pv23431 : PrimeValue := ⟨23431, pr23431⟩
private theorem pr23447 : Nat.Prime 23447 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv617]) (by decide +kernel)
def pv23447 : PrimeValue := ⟨23447, pr23447⟩
private theorem pr23459 : Nat.Prime 23459 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv317]) (by decide +kernel)
def pv23459 : PrimeValue := ⟨23459, pr23459⟩
private theorem pr23473 : Nat.Prime 23473 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv163]) (by decide +kernel)
def pv23473 : PrimeValue := ⟨23473, pr23473⟩
private theorem pr23497 : Nat.Prime 23497 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv89]) (by decide +kernel)
def pv23497 : PrimeValue := ⟨23497, pr23497⟩
private theorem pr23509 : Nat.Prime 23509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv653]) (by decide +kernel)
def pv23509 : PrimeValue := ⟨23509, pr23509⟩
private theorem pr23531 : Nat.Prime 23531 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv181]) (by decide +kernel)
def pv23531 : PrimeValue := ⟨23531, pr23531⟩
private theorem pr23537 : Nat.Prime 23537 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1471]) (by decide +kernel)
def pv23537 : PrimeValue := ⟨23537, pr23537⟩
private theorem pr23539 : Nat.Prime 23539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv3923]) (by decide +kernel)
def pv23539 : PrimeValue := ⟨23539, pr23539⟩
private theorem pr23549 : Nat.Prime 23549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv29]) (by decide +kernel)
def pv23549 : PrimeValue := ⟨23549, pr23549⟩
private theorem pr23557 : Nat.Prime 23557 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv151]) (by decide +kernel)
def pv23557 : PrimeValue := ⟨23557, pr23557⟩
private theorem pr23561 : Nat.Prime 23561 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv19,pv31]) (by decide +kernel)
def pv23561 : PrimeValue := ⟨23561, pr23561⟩
private theorem pr23563 : Nat.Prime 23563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv17]) (by decide +kernel)
def pv23563 : PrimeValue := ⟨23563, pr23563⟩
private theorem pr23567 : Nat.Prime 23567 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11783]) (by decide +kernel)
def pv23567 : PrimeValue := ⟨23567, pr23567⟩
private theorem pr23581 : Nat.Prime 23581 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv131]) (by decide +kernel)
def pv23581 : PrimeValue := ⟨23581, pr23581⟩
private theorem pr23593 : Nat.Prime 23593 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv983]) (by decide +kernel)
def pv23593 : PrimeValue := ⟨23593, pr23593⟩
private theorem pr23599 : Nat.Prime 23599 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv23]) (by decide +kernel)
def pv23599 : PrimeValue := ⟨23599, pr23599⟩
private theorem pr23603 : Nat.Prime 23603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11801]) (by decide +kernel)
def pv23603 : PrimeValue := ⟨23603, pr23603⟩
private theorem pr23609 : Nat.Prime 23609 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv13,pv227]) (by decide +kernel)
def pv23609 : PrimeValue := ⟨23609, pr23609⟩
private theorem pr23623 : Nat.Prime 23623 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv31,pv127]) (by decide +kernel)
def pv23623 : PrimeValue := ⟨23623, pr23623⟩
private theorem pr23627 : Nat.Prime 23627 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11813]) (by decide +kernel)
def pv23627 : PrimeValue := ⟨23627, pr23627⟩
private theorem pr23629 : Nat.Prime 23629 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv179]) (by decide +kernel)
def pv23629 : PrimeValue := ⟨23629, pr23629⟩
private theorem pr23633 : Nat.Prime 23633 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv211]) (by decide +kernel)
def pv23633 : PrimeValue := ⟨23633, pr23633⟩
private theorem pr23663 : Nat.Prime 23663 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11831]) (by decide +kernel)
def pv23663 : PrimeValue := ⟨23663, pr23663⟩
private theorem pr23669 : Nat.Prime 23669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv97]) (by decide +kernel)
def pv23669 : PrimeValue := ⟨23669, pr23669⟩
private theorem pr23671 : Nat.Prime 23671 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv263]) (by decide +kernel)
def pv23671 : PrimeValue := ⟨23671, pr23671⟩
private theorem pr23677 : Nat.Prime 23677 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1973]) (by decide +kernel)
def pv23677 : PrimeValue := ⟨23677, pr23677⟩
private theorem pr23687 : Nat.Prime 23687 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv911]) (by decide +kernel)
def pv23687 : PrimeValue := ⟨23687, pr23687⟩
private theorem pr23689 : Nat.Prime 23689 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv47]) (by decide +kernel)
def pv23689 : PrimeValue := ⟨23689, pr23689⟩
private theorem pr23719 : Nat.Prime 23719 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv59,pv67]) (by decide +kernel)
def pv23719 : PrimeValue := ⟨23719, pr23719⟩
private theorem pr23741 : Nat.Prime 23741 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1187]) (by decide +kernel)
def pv23741 : PrimeValue := ⟨23741, pr23741⟩
private theorem pr23743 : Nat.Prime 23743 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv1319]) (by decide +kernel)
def pv23743 : PrimeValue := ⟨23743, pr23743⟩
private theorem pr23747 : Nat.Prime 23747 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv383]) (by decide +kernel)
def pv23747 : PrimeValue := ⟨23747, pr23747⟩
private theorem pr23753 : Nat.Prime 23753 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2969]) (by decide +kernel)
def pv23753 : PrimeValue := ⟨23753, pr23753⟩
private theorem pr23761 : Nat.Prime 23761 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv23761 : PrimeValue := ⟨23761, pr23761⟩
private theorem pr23767 : Nat.Prime 23767 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv233]) (by decide +kernel)
def pv23767 : PrimeValue := ⟨23767, pr23767⟩
private theorem pr23773 : Nat.Prime 23773 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv283]) (by decide +kernel)
def pv23773 : PrimeValue := ⟨23773, pr23773⟩
private theorem pr23789 : Nat.Prime 23789 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv313]) (by decide +kernel)
def pv23789 : PrimeValue := ⟨23789, pr23789⟩
private theorem pr23801 : Nat.Prime 23801 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv17]) (by decide +kernel)
def pv23801 : PrimeValue := ⟨23801, pr23801⟩
private theorem pr23813 : Nat.Prime 23813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5953]) (by decide +kernel)
def pv23813 : PrimeValue := ⟨23813, pr23813⟩
private theorem pr23819 : Nat.Prime 23819 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11909]) (by decide +kernel)
def pv23819 : PrimeValue := ⟨23819, pr23819⟩
private theorem pr23827 : Nat.Prime 23827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv19]) (by decide +kernel)
def pv23827 : PrimeValue := ⟨23827, pr23827⟩
private theorem pr23831 : Nat.Prime 23831 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv2383]) (by decide +kernel)
def pv23831 : PrimeValue := ⟨23831, pr23831⟩
private theorem pr23833 : Nat.Prime 23833 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv331]) (by decide +kernel)
def pv23833 : PrimeValue := ⟨23833, pr23833⟩
private theorem pr23857 : Nat.Prime 23857 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv71]) (by decide +kernel)
def pv23857 : PrimeValue := ⟨23857, pr23857⟩
private theorem pr23869 : Nat.Prime 23869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv17]) (by decide +kernel)
def pv23869 : PrimeValue := ⟨23869, pr23869⟩
private theorem pr23873 : Nat.Prime 23873 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv373]) (by decide +kernel)
def pv23873 : PrimeValue := ⟨23873, pr23873⟩
private theorem pr23879 : Nat.Prime 23879 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11939]) (by decide +kernel)
def pv23879 : PrimeValue := ⟨23879, pr23879⟩
private theorem pr23887 : Nat.Prime 23887 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv1327]) (by decide +kernel)
def pv23887 : PrimeValue := ⟨23887, pr23887⟩
private theorem pr23893 : Nat.Prime 23893 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv181]) (by decide +kernel)
def pv23893 : PrimeValue := ⟨23893, pr23893⟩
private theorem pr23899 : Nat.Prime 23899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv569]) (by decide +kernel)
def pv23899 : PrimeValue := ⟨23899, pr23899⟩
private theorem pr23909 : Nat.Prime 23909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv139]) (by decide +kernel)
def pv23909 : PrimeValue := ⟨23909, pr23909⟩
private theorem pr23911 : Nat.Prime 23911 :=
  checkPrime_prime (q := pv73) (ls := [pv2,pv3,pv5,pv797]) (by decide +kernel)
def pv23911 : PrimeValue := ⟨23911, pr23911⟩
private theorem pr23917 : Nat.Prime 23917 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1993]) (by decide +kernel)
def pv23917 : PrimeValue := ⟨23917, pr23917⟩
private theorem pr23929 : Nat.Prime 23929 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv997]) (by decide +kernel)
def pv23929 : PrimeValue := ⟨23929, pr23929⟩
private theorem pr23957 : Nat.Prime 23957 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv53,pv113]) (by decide +kernel)
def pv23957 : PrimeValue := ⟨23957, pr23957⟩
private theorem pr23971 : Nat.Prime 23971 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv17,pv47]) (by decide +kernel)
def pv23971 : PrimeValue := ⟨23971, pr23971⟩
private theorem pr23977 : Nat.Prime 23977 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv37]) (by decide +kernel)
def pv23977 : PrimeValue := ⟨23977, pr23977⟩
private theorem pr23981 : Nat.Prime 23981 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11,pv109]) (by decide +kernel)
def pv23981 : PrimeValue := ⟨23981, pr23981⟩
private theorem pr23993 : Nat.Prime 23993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2999]) (by decide +kernel)
def pv23993 : PrimeValue := ⟨23993, pr23993⟩
private theorem pr24001 : Nat.Prime 24001 :=
  checkPrime_prime (q := pv43) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv24001 : PrimeValue := ⟨24001, pr24001⟩
private theorem pr24007 : Nat.Prime 24007 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv4001]) (by decide +kernel)
def pv24007 : PrimeValue := ⟨24007, pr24007⟩
private theorem pr24019 : Nat.Prime 24019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4003]) (by decide +kernel)
def pv24019 : PrimeValue := ⟨24019, pr24019⟩
private theorem pr24023 : Nat.Prime 24023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv12011]) (by decide +kernel)
def pv24023 : PrimeValue := ⟨24023, pr24023⟩
private theorem pr24029 : Nat.Prime 24029 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv6007]) (by decide +kernel)
def pv24029 : PrimeValue := ⟨24029, pr24029⟩
private theorem pr24043 : Nat.Prime 24043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4007]) (by decide +kernel)
def pv24043 : PrimeValue := ⟨24043, pr24043⟩
private theorem pr24049 : Nat.Prime 24049 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv167]) (by decide +kernel)
def pv24049 : PrimeValue := ⟨24049, pr24049⟩
private theorem pr24061 : Nat.Prime 24061 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv401]) (by decide +kernel)
def pv24061 : PrimeValue := ⟨24061, pr24061⟩
private theorem pr24071 : Nat.Prime 24071 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv29,pv83]) (by decide +kernel)
def pv24071 : PrimeValue := ⟨24071, pr24071⟩
private theorem pr24077 : Nat.Prime 24077 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv463]) (by decide +kernel)
def pv24077 : PrimeValue := ⟨24077, pr24077⟩
private theorem pr24083 : Nat.Prime 24083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv12041]) (by decide +kernel)
def pv24083 : PrimeValue := ⟨24083, pr24083⟩
private theorem pr24091 : Nat.Prime 24091 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv73]) (by decide +kernel)
def pv24091 : PrimeValue := ⟨24091, pr24091⟩
private theorem pr24097 : Nat.Prime 24097 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv251]) (by decide +kernel)
def pv24097 : PrimeValue := ⟨24097, pr24097⟩
private theorem pr24103 : Nat.Prime 24103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv103]) (by decide +kernel)
def pv24103 : PrimeValue := ⟨24103, pr24103⟩
private theorem pr24107 : Nat.Prime 24107 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv709]) (by decide +kernel)
def pv24107 : PrimeValue := ⟨24107, pr24107⟩
private theorem pr24109 : Nat.Prime 24109 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv41]) (by decide +kernel)
def pv24109 : PrimeValue := ⟨24109, pr24109⟩
private theorem pr24113 : Nat.Prime 24113 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv137]) (by decide +kernel)
def pv24113 : PrimeValue := ⟨24113, pr24113⟩
private theorem pr24121 : Nat.Prime 24121 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv67]) (by decide +kernel)
def pv24121 : PrimeValue := ⟨24121, pr24121⟩
private theorem pr24133 : Nat.Prime 24133 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv2011]) (by decide +kernel)
def pv24133 : PrimeValue := ⟨24133, pr24133⟩
private theorem pr24137 : Nat.Prime 24137 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv431]) (by decide +kernel)
def pv24137 : PrimeValue := ⟨24137, pr24137⟩
private theorem pr24151 : Nat.Prime 24151 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv23]) (by decide +kernel)
def pv24151 : PrimeValue := ⟨24151, pr24151⟩
private theorem pr24169 : Nat.Prime 24169 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv19,pv53]) (by decide +kernel)
def pv24169 : PrimeValue := ⟨24169, pr24169⟩
private theorem pr24179 : Nat.Prime 24179 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv157]) (by decide +kernel)
def pv24179 : PrimeValue := ⟨24179, pr24179⟩
private theorem pr24181 : Nat.Prime 24181 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv13,pv31]) (by decide +kernel)
def pv24181 : PrimeValue := ⟨24181, pr24181⟩
private theorem pr24197 : Nat.Prime 24197 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv263]) (by decide +kernel)
def pv24197 : PrimeValue := ⟨24197, pr24197⟩
private theorem pr24203 : Nat.Prime 24203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv12101]) (by decide +kernel)
def pv24203 : PrimeValue := ⟨24203, pr24203⟩
private theorem pr24223 : Nat.Prime 24223 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv367]) (by decide +kernel)
def pv24223 : PrimeValue := ⟨24223, pr24223⟩
private theorem pr24229 : Nat.Prime 24229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv673]) (by decide +kernel)
def pv24229 : PrimeValue := ⟨24229, pr24229⟩
private theorem pr24239 : Nat.Prime 24239 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv12119]) (by decide +kernel)
def pv24239 : PrimeValue := ⟨24239, pr24239⟩
private theorem pr24247 : Nat.Prime 24247 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv449]) (by decide +kernel)
def pv24247 : PrimeValue := ⟨24247, pr24247⟩
private theorem pr24251 : Nat.Prime 24251 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv97]) (by decide +kernel)
def pv24251 : PrimeValue := ⟨24251, pr24251⟩
private theorem pr24281 : Nat.Prime 24281 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv607]) (by decide +kernel)
def pv24281 : PrimeValue := ⟨24281, pr24281⟩
private theorem pr24317 : Nat.Prime 24317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv6079]) (by decide +kernel)
def pv24317 : PrimeValue := ⟨24317, pr24317⟩
private theorem pr24329 : Nat.Prime 24329 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3041]) (by decide +kernel)
def pv24329 : PrimeValue := ⟨24329, pr24329⟩
private theorem pr24337 : Nat.Prime 24337 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv24337 : PrimeValue := ⟨24337, pr24337⟩
private theorem pr24359 : Nat.Prime 24359 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv19,pv641]) (by decide +kernel)
def pv24359 : PrimeValue := ⟨24359, pr24359⟩
private theorem pr24371 : Nat.Prime 24371 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv2437]) (by decide +kernel)
def pv24371 : PrimeValue := ⟨24371, pr24371⟩
private theorem pr24373 : Nat.Prime 24373 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv677]) (by decide +kernel)
def pv24373 : PrimeValue := ⟨24373, pr24373⟩
private theorem pr24379 : Nat.Prime 24379 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv239]) (by decide +kernel)
def pv24379 : PrimeValue := ⟨24379, pr24379⟩
private theorem pr24391 : Nat.Prime 24391 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv271]) (by decide +kernel)
def pv24391 : PrimeValue := ⟨24391, pr24391⟩
private theorem pr24407 : Nat.Prime 24407 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv12203]) (by decide +kernel)
def pv24407 : PrimeValue := ⟨24407, pr24407⟩
private theorem pr24413 : Nat.Prime 24413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv359]) (by decide +kernel)
def pv24413 : PrimeValue := ⟨24413, pr24413⟩
private theorem pr24419 : Nat.Prime 24419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv421]) (by decide +kernel)
def pv24419 : PrimeValue := ⟨24419, pr24419⟩
private theorem pr24421 : Nat.Prime 24421 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv37]) (by decide +kernel)
def pv24421 : PrimeValue := ⟨24421, pr24421⟩
private theorem pr24439 : Nat.Prime 24439 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv4073]) (by decide +kernel)
def pv24439 : PrimeValue := ⟨24439, pr24439⟩
private theorem pr24443 : Nat.Prime 24443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv101]) (by decide +kernel)
def pv24443 : PrimeValue := ⟨24443, pr24443⟩
private theorem pr24469 : Nat.Prime 24469 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv2039]) (by decide +kernel)
def pv24469 : PrimeValue := ⟨24469, pr24469⟩
private theorem pr24473 : Nat.Prime 24473 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv19,pv23]) (by decide +kernel)
def pv24473 : PrimeValue := ⟨24473, pr24473⟩
private theorem pr24481 : Nat.Prime 24481 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv24481 : PrimeValue := ⟨24481, pr24481⟩
private theorem pr24499 : Nat.Prime 24499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1361]) (by decide +kernel)
def pv24499 : PrimeValue := ⟨24499, pr24499⟩
private theorem pr24509 : Nat.Prime 24509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv557]) (by decide +kernel)
def pv24509 : PrimeValue := ⟨24509, pr24509⟩
private theorem pr24517 : Nat.Prime 24517 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv227]) (by decide +kernel)
def pv24517 : PrimeValue := ⟨24517, pr24517⟩
private theorem pr24527 : Nat.Prime 24527 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv12263]) (by decide +kernel)
def pv24527 : PrimeValue := ⟨24527, pr24527⟩
private theorem pr24533 : Nat.Prime 24533 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv6133]) (by decide +kernel)
def pv24533 : PrimeValue := ⟨24533, pr24533⟩
private theorem pr24547 : Nat.Prime 24547 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4091]) (by decide +kernel)
def pv24547 : PrimeValue := ⟨24547, pr24547⟩
private theorem pr24551 : Nat.Prime 24551 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv491]) (by decide +kernel)
def pv24551 : PrimeValue := ⟨24551, pr24551⟩
private theorem pr24571 : Nat.Prime 24571 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv13]) (by decide +kernel)
def pv24571 : PrimeValue := ⟨24571, pr24571⟩
private theorem pr24593 : Nat.Prime 24593 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv53]) (by decide +kernel)
def pv24593 : PrimeValue := ⟨24593, pr24593⟩
private theorem pr24611 : Nat.Prime 24611 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv23,pv107]) (by decide +kernel)
def pv24611 : PrimeValue := ⟨24611, pr24611⟩
private theorem pr24623 : Nat.Prime 24623 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv947]) (by decide +kernel)
def pv24623 : PrimeValue := ⟨24623, pr24623⟩
private theorem pr24631 : Nat.Prime 24631 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv821]) (by decide +kernel)
def pv24631 : PrimeValue := ⟨24631, pr24631⟩
private theorem pr24659 : Nat.Prime 24659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv12329]) (by decide +kernel)
def pv24659 : PrimeValue := ⟨24659, pr24659⟩
private theorem pr24671 : Nat.Prime 24671 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv2467]) (by decide +kernel)
def pv24671 : PrimeValue := ⟨24671, pr24671⟩
private theorem pr24677 : Nat.Prime 24677 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv199]) (by decide +kernel)
def pv24677 : PrimeValue := ⟨24677, pr24677⟩
private theorem pr24683 : Nat.Prime 24683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv41,pv43]) (by decide +kernel)
def pv24683 : PrimeValue := ⟨24683, pr24683⟩
private theorem pr24691 : Nat.Prime 24691 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv823]) (by decide +kernel)
def pv24691 : PrimeValue := ⟨24691, pr24691⟩
private theorem pr24697 : Nat.Prime 24697 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv24697 : PrimeValue := ⟨24697, pr24697⟩
private theorem pr24709 : Nat.Prime 24709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv71]) (by decide +kernel)
def pv24709 : PrimeValue := ⟨24709, pr24709⟩
private theorem pr24733 : Nat.Prime 24733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv229]) (by decide +kernel)
def pv24733 : PrimeValue := ⟨24733, pr24733⟩
private theorem pr24749 : Nat.Prime 24749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv269]) (by decide +kernel)
def pv24749 : PrimeValue := ⟨24749, pr24749⟩
private theorem pr24763 : Nat.Prime 24763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4127]) (by decide +kernel)
def pv24763 : PrimeValue := ⟨24763, pr24763⟩
private theorem pr24767 : Nat.Prime 24767 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv29,pv61]) (by decide +kernel)
def pv24767 : PrimeValue := ⟨24767, pr24767⟩
private theorem pr24781 : Nat.Prime 24781 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv59]) (by decide +kernel)
def pv24781 : PrimeValue := ⟨24781, pr24781⟩
private theorem pr24793 : Nat.Prime 24793 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1033]) (by decide +kernel)
def pv24793 : PrimeValue := ⟨24793, pr24793⟩
private theorem pr24799 : Nat.Prime 24799 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv4133]) (by decide +kernel)
def pv24799 : PrimeValue := ⟨24799, pr24799⟩
private theorem pr24809 : Nat.Prime 24809 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv7,pv443]) (by decide +kernel)
def pv24809 : PrimeValue := ⟨24809, pr24809⟩
private theorem pr24821 : Nat.Prime 24821 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv73]) (by decide +kernel)
def pv24821 : PrimeValue := ⟨24821, pr24821⟩
private theorem pr24841 : Nat.Prime 24841 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv23]) (by decide +kernel)
def pv24841 : PrimeValue := ⟨24841, pr24841⟩
private theorem pr24847 : Nat.Prime 24847 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv41,pv101]) (by decide +kernel)
def pv24847 : PrimeValue := ⟨24847, pr24847⟩
private theorem pr24851 : Nat.Prime 24851 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv71]) (by decide +kernel)
def pv24851 : PrimeValue := ⟨24851, pr24851⟩
private theorem pr24859 : Nat.Prime 24859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1381]) (by decide +kernel)
def pv24859 : PrimeValue := ⟨24859, pr24859⟩
private theorem pr24877 : Nat.Prime 24877 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv691]) (by decide +kernel)
def pv24877 : PrimeValue := ⟨24877, pr24877⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
