/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table061
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table061.pv180181
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table008
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table013
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table034
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table035

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr180181 : PrimeCertificate 180181 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv7,pv11,pv13]) (by decide +kernel)
def pv180181 : PrimeValue := ⟨180181, pr180181⟩
private theorem pr180221 : PrimeCertificate 180221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv9011]) (by decide +kernel)
def pv180221 : PrimeValue := ⟨180221, pr180221⟩
private theorem pr180239 : PrimeCertificate 180239 :=
  certifyPrime (q := pv11) (ls := [pv2,pv227,pv397]) (by decide +kernel)
def pv180239 : PrimeValue := ⟨180239, pr180239⟩
private theorem pr180247 : PrimeCertificate 180247 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv2731]) (by decide +kernel)
def pv180247 : PrimeValue := ⟨180247, pr180247⟩
private theorem pr180259 : PrimeCertificate 180259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv2311]) (by decide +kernel)
def pv180259 : PrimeValue := ⟨180259, pr180259⟩
private theorem pr180281 : PrimeCertificate 180281 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv4507]) (by decide +kernel)
def pv180281 : PrimeValue := ⟨180281, pr180281⟩
private theorem pr180287 : PrimeCertificate 180287 :=
  certifyPrime (q := pv5) (ls := [pv2,pv109,pv827]) (by decide +kernel)
def pv180287 : PrimeValue := ⟨180287, pr180287⟩
private theorem pr180307 : PrimeCertificate 180307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv53]) (by decide +kernel)
def pv180307 : PrimeValue := ⟨180307, pr180307⟩
private theorem pr180317 : PrimeCertificate 180317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv739]) (by decide +kernel)
def pv180317 : PrimeValue := ⟨180317, pr180317⟩
private theorem pr180331 : PrimeCertificate 180331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv6011]) (by decide +kernel)
def pv180331 : PrimeValue := ⟨180331, pr180331⟩
private theorem pr180337 : PrimeCertificate 180337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv17]) (by decide +kernel)
def pv180337 : PrimeValue := ⟨180337, pr180337⟩
private theorem pr180347 : PrimeCertificate 180347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv90173]) (by decide +kernel)
def pv180347 : PrimeValue := ⟨180347, pr180347⟩
private theorem pr180361 : PrimeCertificate 180361 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv167]) (by decide +kernel)
def pv180361 : PrimeValue := ⟨180361, pr180361⟩
private theorem pr180371 : PrimeCertificate 180371 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv17,pv1061]) (by decide +kernel)
def pv180371 : PrimeValue := ⟨180371, pr180371⟩
private theorem pr180391 : PrimeCertificate 180391 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv859]) (by decide +kernel)
def pv180391 : PrimeValue := ⟨180391, pr180391⟩
private theorem pr180413 : PrimeCertificate 180413 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv37,pv53]) (by decide +kernel)
def pv180413 : PrimeValue := ⟨180413, pr180413⟩
private theorem pr180419 : PrimeCertificate 180419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv263]) (by decide +kernel)
def pv180419 : PrimeValue := ⟨180419, pr180419⟩
private theorem pr180437 : PrimeCertificate 180437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv79,pv571]) (by decide +kernel)
def pv180437 : PrimeValue := ⟨180437, pr180437⟩
private theorem pr180463 : PrimeCertificate 180463 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv1583]) (by decide +kernel)
def pv180463 : PrimeValue := ⟨180463, pr180463⟩
private theorem pr180473 : PrimeCertificate 180473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv1327]) (by decide +kernel)
def pv180473 : PrimeValue := ⟨180473, pr180473⟩
private theorem pr180491 : PrimeCertificate 180491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv18049]) (by decide +kernel)
def pv180491 : PrimeValue := ⟨180491, pr180491⟩
private theorem pr180497 : PrimeCertificate 180497 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv389]) (by decide +kernel)
def pv180497 : PrimeValue := ⟨180497, pr180497⟩
private theorem pr180511 : PrimeCertificate 180511 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv547]) (by decide +kernel)
def pv180511 : PrimeValue := ⟨180511, pr180511⟩
private theorem pr180547 : PrimeCertificate 180547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv30091]) (by decide +kernel)
def pv180547 : PrimeValue := ⟨180547, pr180547⟩
private theorem pr180569 : PrimeCertificate 180569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv22571]) (by decide +kernel)
def pv180569 : PrimeValue := ⟨180569, pr180569⟩
private theorem pr180629 : PrimeCertificate 180629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv6451]) (by decide +kernel)
def pv180629 : PrimeValue := ⟨180629, pr180629⟩
private theorem pr180647 : PrimeCertificate 180647 :=
  certifyPrime (q := pv5) (ls := [pv2,pv41,pv2203]) (by decide +kernel)
def pv180647 : PrimeValue := ⟨180647, pr180647⟩
private theorem pr180667 : PrimeCertificate 180667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv10037]) (by decide +kernel)
def pv180667 : PrimeValue := ⟨180667, pr180667⟩
private theorem pr180679 : PrimeCertificate 180679 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv30113]) (by decide +kernel)
def pv180679 : PrimeValue := ⟨180679, pr180679⟩
private theorem pr180701 : PrimeCertificate 180701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv139]) (by decide +kernel)
def pv180701 : PrimeValue := ⟨180701, pr180701⟩
private theorem pr180731 : PrimeCertificate 180731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv31,pv53]) (by decide +kernel)
def pv180731 : PrimeValue := ⟨180731, pr180731⟩
private theorem pr180749 : PrimeCertificate 180749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv619]) (by decide +kernel)
def pv180749 : PrimeValue := ⟨180749, pr180749⟩
private theorem pr180751 : PrimeCertificate 180751 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv241]) (by decide +kernel)
def pv180751 : PrimeValue := ⟨180751, pr180751⟩
private theorem pr180779 : PrimeCertificate 180779 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv17,pv409]) (by decide +kernel)
def pv180779 : PrimeValue := ⟨180779, pr180779⟩
private theorem pr180793 : PrimeCertificate 180793 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv31]) (by decide +kernel)
def pv180793 : PrimeValue := ⟨180793, pr180793⟩
private theorem pr180811 : PrimeCertificate 180811 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv41]) (by decide +kernel)
def pv180811 : PrimeValue := ⟨180811, pr180811⟩
private theorem pr180847 : PrimeCertificate 180847 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv17,pv197]) (by decide +kernel)
def pv180847 : PrimeValue := ⟨180847, pr180847⟩
private theorem pr180871 : PrimeCertificate 180871 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv6029]) (by decide +kernel)
def pv180871 : PrimeValue := ⟨180871, pr180871⟩
private theorem pr180883 : PrimeCertificate 180883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv773]) (by decide +kernel)
def pv180883 : PrimeValue := ⟨180883, pr180883⟩
private theorem pr180907 : PrimeCertificate 180907 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv11,pv2741]) (by decide +kernel)
def pv180907 : PrimeValue := ⟨180907, pr180907⟩
private theorem pr180949 : PrimeCertificate 180949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv887]) (by decide +kernel)
def pv180949 : PrimeValue := ⟨180949, pr180949⟩
private theorem pr180959 : PrimeCertificate 180959 :=
  certifyPrime (q := pv7) (ls := [pv2,pv173,pv523]) (by decide +kernel)
def pv180959 : PrimeValue := ⟨180959, pr180959⟩
private theorem pr181001 : PrimeCertificate 181001 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv181]) (by decide +kernel)
def pv181001 : PrimeValue := ⟨181001, pr181001⟩
private theorem pr181019 : PrimeCertificate 181019 :=
  certifyPrime (q := pv11) (ls := [pv2,pv29,pv3121]) (by decide +kernel)
def pv181019 : PrimeValue := ⟨181019, pr181019⟩
private theorem pr181061 : PrimeCertificate 181061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv823]) (by decide +kernel)
def pv181061 : PrimeValue := ⟨181061, pr181061⟩
private theorem pr181087 : PrimeCertificate 181087 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv30181]) (by decide +kernel)
def pv181087 : PrimeValue := ⟨181087, pr181087⟩
private theorem pr181141 : PrimeCertificate 181141 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv3019]) (by decide +kernel)
def pv181141 : PrimeValue := ⟨181141, pr181141⟩
private theorem pr181157 : PrimeCertificate 181157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv45289]) (by decide +kernel)
def pv181157 : PrimeValue := ⟨181157, pr181157⟩
private theorem pr181183 : PrimeCertificate 181183 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv30197]) (by decide +kernel)
def pv181183 : PrimeValue := ⟨181183, pr181183⟩
private theorem pr181193 : PrimeCertificate 181193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv29,pv71]) (by decide +kernel)
def pv181193 : PrimeValue := ⟨181193, pr181193⟩
private theorem pr181201 : PrimeCertificate 181201 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv151]) (by decide +kernel)
def pv181201 : PrimeValue := ⟨181201, pr181201⟩
private theorem pr181211 : PrimeCertificate 181211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv18121]) (by decide +kernel)
def pv181211 : PrimeValue := ⟨181211, pr181211⟩
private theorem pr181213 : PrimeCertificate 181213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv15101]) (by decide +kernel)
def pv181213 : PrimeValue := ⟨181213, pr181213⟩
private theorem pr181219 : PrimeCertificate 181219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv30203]) (by decide +kernel)
def pv181219 : PrimeValue := ⟨181219, pr181219⟩
private theorem pr181243 : PrimeCertificate 181243 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv10069]) (by decide +kernel)
def pv181243 : PrimeValue := ⟨181243, pr181243⟩
private theorem pr181253 : PrimeCertificate 181253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv113,pv401]) (by decide +kernel)
def pv181253 : PrimeValue := ⟨181253, pr181253⟩
private theorem pr181277 : PrimeCertificate 181277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv45319]) (by decide +kernel)
def pv181277 : PrimeValue := ⟨181277, pr181277⟩
private theorem pr181297 : PrimeCertificate 181297 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1259]) (by decide +kernel)
def pv181297 : PrimeValue := ⟨181297, pr181297⟩
private theorem pr181361 : PrimeCertificate 181361 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv2267]) (by decide +kernel)
def pv181361 : PrimeValue := ⟨181361, pr181361⟩
private theorem pr181387 : PrimeCertificate 181387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3359]) (by decide +kernel)
def pv181387 : PrimeValue := ⟨181387, pr181387⟩
private theorem pr181399 : PrimeCertificate 181399 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv617]) (by decide +kernel)
def pv181399 : PrimeValue := ⟨181399, pr181399⟩
private theorem pr181421 : PrimeCertificate 181421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv47,pv193]) (by decide +kernel)
def pv181421 : PrimeValue := ⟨181421, pr181421⟩
private theorem pr181439 : PrimeCertificate 181439 :=
  certifyPrime (q := pv11) (ls := [pv2,pv83,pv1093]) (by decide +kernel)
def pv181439 : PrimeValue := ⟨181439, pr181439⟩
private theorem pr181459 : PrimeCertificate 181459 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv17,pv593]) (by decide +kernel)
def pv181459 : PrimeValue := ⟨181459, pr181459⟩
private theorem pr181513 : PrimeCertificate 181513 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2521]) (by decide +kernel)
def pv181513 : PrimeValue := ⟨181513, pr181513⟩
private theorem pr181523 : PrimeCertificate 181523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv37,pv223]) (by decide +kernel)
def pv181523 : PrimeValue := ⟨181523, pr181523⟩
private theorem pr181537 : PrimeCertificate 181537 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv61]) (by decide +kernel)
def pv181537 : PrimeValue := ⟨181537, pr181537⟩
private theorem pr181549 : PrimeCertificate 181549 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv41]) (by decide +kernel)
def pv181549 : PrimeValue := ⟨181549, pr181549⟩
private theorem pr181553 : PrimeCertificate 181553 :=
  certifyPrime (q := pv13) (ls := [pv2,pv7,pv1621]) (by decide +kernel)
def pv181553 : PrimeValue := ⟨181553, pr181553⟩
private theorem pr181603 : PrimeCertificate 181603 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv59]) (by decide +kernel)
def pv181603 : PrimeValue := ⟨181603, pr181603⟩
private theorem pr181607 : PrimeCertificate 181607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv90803]) (by decide +kernel)
def pv181607 : PrimeValue := ⟨181607, pr181607⟩
private theorem pr181609 : PrimeCertificate 181609 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv23,pv47]) (by decide +kernel)
def pv181609 : PrimeValue := ⟨181609, pr181609⟩
private theorem pr181619 : PrimeCertificate 181619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71,pv1279]) (by decide +kernel)
def pv181619 : PrimeValue := ⟨181619, pr181619⟩
private theorem pr181639 : PrimeCertificate 181639 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv10091]) (by decide +kernel)
def pv181639 : PrimeValue := ⟨181639, pr181639⟩
private theorem pr181667 : PrimeCertificate 181667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv90833]) (by decide +kernel)
def pv181667 : PrimeValue := ⟨181667, pr181667⟩
private theorem pr181693 : PrimeCertificate 181693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv103]) (by decide +kernel)
def pv181693 : PrimeValue := ⟨181693, pr181693⟩
private theorem pr181711 : PrimeCertificate 181711 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv673]) (by decide +kernel)
def pv181711 : PrimeValue := ⟨181711, pr181711⟩
private theorem pr181717 : PrimeCertificate 181717 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv19,pv797]) (by decide +kernel)
def pv181717 : PrimeValue := ⟨181717, pr181717⟩
private theorem pr181721 : PrimeCertificate 181721 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv11,pv59]) (by decide +kernel)
def pv181721 : PrimeValue := ⟨181721, pr181721⟩
private theorem pr181729 : PrimeCertificate 181729 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv631]) (by decide +kernel)
def pv181729 : PrimeValue := ⟨181729, pr181729⟩
private theorem pr181739 : PrimeCertificate 181739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89,pv1021]) (by decide +kernel)
def pv181739 : PrimeValue := ⟨181739, pr181739⟩
private theorem pr181777 : PrimeCertificate 181777 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv541]) (by decide +kernel)
def pv181777 : PrimeValue := ⟨181777, pr181777⟩
private theorem pr181789 : PrimeCertificate 181789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv15149]) (by decide +kernel)
def pv181789 : PrimeValue := ⟨181789, pr181789⟩
private theorem pr181813 : PrimeCertificate 181813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv109,pv139]) (by decide +kernel)
def pv181813 : PrimeValue := ⟨181813, pr181813⟩
private theorem pr181837 : PrimeCertificate 181837 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv5051]) (by decide +kernel)
def pv181837 : PrimeValue := ⟨181837, pr181837⟩
private theorem pr181871 : PrimeCertificate 181871 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv1399]) (by decide +kernel)
def pv181871 : PrimeValue := ⟨181871, pr181871⟩
private theorem pr181873 : PrimeCertificate 181873 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv421]) (by decide +kernel)
def pv181873 : PrimeValue := ⟨181873, pr181873⟩
private theorem pr181889 : PrimeCertificate 181889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv29]) (by decide +kernel)
def pv181889 : PrimeValue := ⟨181889, pr181889⟩
private theorem pr181891 : PrimeCertificate 181891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv43,pv47]) (by decide +kernel)
def pv181891 : PrimeValue := ⟨181891, pr181891⟩
private theorem pr181903 : PrimeCertificate 181903 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv61,pv71]) (by decide +kernel)
def pv181903 : PrimeValue := ⟨181903, pr181903⟩
private theorem pr181919 : PrimeCertificate 181919 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv8269]) (by decide +kernel)
def pv181919 : PrimeValue := ⟨181919, pr181919⟩
private theorem pr181927 : PrimeCertificate 181927 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1123]) (by decide +kernel)
def pv181927 : PrimeValue := ⟨181927, pr181927⟩
private theorem pr181943 : PrimeCertificate 181943 :=
  certifyPrime (q := pv5) (ls := [pv2,pv90971]) (by decide +kernel)
def pv181943 : PrimeValue := ⟨181943, pr181943⟩
private theorem pr181981 : PrimeCertificate 181981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv337]) (by decide +kernel)
def pv181981 : PrimeValue := ⟨181981, pr181981⟩
private theorem pr181997 : PrimeCertificate 181997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv173,pv263]) (by decide +kernel)
def pv181997 : PrimeValue := ⟨181997, pr181997⟩
private theorem pr182009 : PrimeCertificate 182009 :=
  certifyPrime (q := pv3) (ls := [pv2,pv22751]) (by decide +kernel)
def pv182009 : PrimeValue := ⟨182009, pr182009⟩
private theorem pr182011 : PrimeCertificate 182011 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv6067]) (by decide +kernel)
def pv182011 : PrimeValue := ⟨182011, pr182011⟩
private theorem pr182027 : PrimeCertificate 182027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv7001]) (by decide +kernel)
def pv182027 : PrimeValue := ⟨182027, pr182027⟩
private theorem pr182029 : PrimeCertificate 182029 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv11,pv197]) (by decide +kernel)
def pv182029 : PrimeValue := ⟨182029, pr182029⟩
private theorem pr182047 : PrimeCertificate 182047 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv30341]) (by decide +kernel)
def pv182047 : PrimeValue := ⟨182047, pr182047⟩
private theorem pr182059 : PrimeCertificate 182059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv1597]) (by decide +kernel)
def pv182059 : PrimeValue := ⟨182059, pr182059⟩
private theorem pr182089 : PrimeCertificate 182089 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv281]) (by decide +kernel)
def pv182089 : PrimeValue := ⟨182089, pr182089⟩
private theorem pr182099 : PrimeCertificate 182099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13007]) (by decide +kernel)
def pv182099 : PrimeValue := ⟨182099, pr182099⟩
private theorem pr182107 : PrimeCertificate 182107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv67,pv151]) (by decide +kernel)
def pv182107 : PrimeValue := ⟨182107, pr182107⟩
private theorem pr182111 : PrimeCertificate 182111 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv18211]) (by decide +kernel)
def pv182111 : PrimeValue := ⟨182111, pr182111⟩
private theorem pr182129 : PrimeCertificate 182129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11383]) (by decide +kernel)
def pv182129 : PrimeValue := ⟨182129, pr182129⟩
private theorem pr182131 : PrimeCertificate 182131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv467]) (by decide +kernel)
def pv182131 : PrimeValue := ⟨182131, pr182131⟩
private theorem pr182159 : PrimeCertificate 182159 :=
  certifyPrime (q := pv19) (ls := [pv2,pv91079]) (by decide +kernel)
def pv182159 : PrimeValue := ⟨182159, pr182159⟩
private theorem pr182167 : PrimeCertificate 182167 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv97,pv313]) (by decide +kernel)
def pv182167 : PrimeValue := ⟨182167, pr182167⟩
private theorem pr182177 : PrimeCertificate 182177 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5693]) (by decide +kernel)
def pv182177 : PrimeValue := ⟨182177, pr182177⟩
private theorem pr182179 : PrimeCertificate 182179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv349]) (by decide +kernel)
def pv182179 : PrimeValue := ⟨182179, pr182179⟩
private theorem pr182209 : PrimeCertificate 182209 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13,pv73]) (by decide +kernel)
def pv182209 : PrimeValue := ⟨182209, pr182209⟩
private theorem pr182233 : PrimeCertificate 182233 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2531]) (by decide +kernel)
def pv182233 : PrimeValue := ⟨182233, pr182233⟩
private theorem pr182239 : PrimeCertificate 182239 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv7,pv4339]) (by decide +kernel)
def pv182239 : PrimeValue := ⟨182239, pr182239⟩
private theorem pr182243 : PrimeCertificate 182243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv91121]) (by decide +kernel)
def pv182243 : PrimeValue := ⟨182243, pr182243⟩
private theorem pr182261 : PrimeCertificate 182261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv701]) (by decide +kernel)
def pv182261 : PrimeValue := ⟨182261, pr182261⟩
private theorem pr182309 : PrimeCertificate 182309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv17,pv383]) (by decide +kernel)
def pv182309 : PrimeValue := ⟨182309, pr182309⟩
private theorem pr182333 : PrimeCertificate 182333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv79,pv577]) (by decide +kernel)
def pv182333 : PrimeValue := ⟨182333, pr182333⟩
private theorem pr182339 : PrimeCertificate 182339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv7013]) (by decide +kernel)
def pv182339 : PrimeValue := ⟨182339, pr182339⟩
private theorem pr182341 : PrimeCertificate 182341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1013]) (by decide +kernel)
def pv182341 : PrimeValue := ⟨182341, pr182341⟩
private theorem pr182353 : PrimeCertificate 182353 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv29,pv131]) (by decide +kernel)
def pv182353 : PrimeValue := ⟨182353, pr182353⟩
private theorem pr182389 : PrimeCertificate 182389 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv15199]) (by decide +kernel)
def pv182389 : PrimeValue := ⟨182389, pr182389⟩
private theorem pr182417 : PrimeCertificate 182417 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv877]) (by decide +kernel)
def pv182417 : PrimeValue := ⟨182417, pr182417⟩
private theorem pr182423 : PrimeCertificate 182423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv197,pv463]) (by decide +kernel)
def pv182423 : PrimeValue := ⟨182423, pr182423⟩
private theorem pr182431 : PrimeCertificate 182431 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv2027]) (by decide +kernel)
def pv182431 : PrimeValue := ⟨182431, pr182431⟩
private theorem pr182467 : PrimeCertificate 182467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv109]) (by decide +kernel)
def pv182467 : PrimeValue := ⟨182467, pr182467⟩
private theorem pr182471 : PrimeCertificate 182471 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv71,pv257]) (by decide +kernel)
def pv182471 : PrimeValue := ⟨182471, pr182471⟩
private theorem pr182473 : PrimeCertificate 182473 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7603]) (by decide +kernel)
def pv182473 : PrimeValue := ⟨182473, pr182473⟩
private theorem pr182489 : PrimeCertificate 182489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv22811]) (by decide +kernel)
def pv182489 : PrimeValue := ⟨182489, pr182489⟩
private theorem pr182519 : PrimeCertificate 182519 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv13037]) (by decide +kernel)
def pv182519 : PrimeValue := ⟨182519, pr182519⟩
private theorem pr182537 : PrimeCertificate 182537 :=
  certifyPrime (q := pv3) (ls := [pv2,pv22817]) (by decide +kernel)
def pv182537 : PrimeValue := ⟨182537, pr182537⟩
private theorem pr182549 : PrimeCertificate 182549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv971]) (by decide +kernel)
def pv182549 : PrimeValue := ⟨182549, pr182549⟩
private theorem pr182579 : PrimeCertificate 182579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv43,pv193]) (by decide +kernel)
def pv182579 : PrimeValue := ⟨182579, pr182579⟩
private theorem pr182587 : PrimeCertificate 182587 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv30431]) (by decide +kernel)
def pv182587 : PrimeValue := ⟨182587, pr182587⟩
private theorem pr182599 : PrimeCertificate 182599 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv2341]) (by decide +kernel)
def pv182599 : PrimeValue := ⟨182599, pr182599⟩
private theorem pr182617 : PrimeCertificate 182617 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv1087]) (by decide +kernel)
def pv182617 : PrimeValue := ⟨182617, pr182617⟩
private theorem pr182641 : PrimeCertificate 182641 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv761]) (by decide +kernel)
def pv182641 : PrimeValue := ⟨182641, pr182641⟩
private theorem pr182657 : PrimeCertificate 182657 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1427]) (by decide +kernel)
def pv182657 : PrimeValue := ⟨182657, pr182657⟩
private theorem pr182659 : PrimeCertificate 182659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv4349]) (by decide +kernel)
def pv182659 : PrimeValue := ⟨182659, pr182659⟩
private theorem pr182687 : PrimeCertificate 182687 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv13049]) (by decide +kernel)
def pv182687 : PrimeValue := ⟨182687, pr182687⟩
private theorem pr182701 : PrimeCertificate 182701 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv5,pv7,pv29]) (by decide +kernel)
def pv182701 : PrimeValue := ⟨182701, pr182701⟩
private theorem pr182711 : PrimeCertificate 182711 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv151]) (by decide +kernel)
def pv182711 : PrimeValue := ⟨182711, pr182711⟩
private theorem pr182713 : PrimeCertificate 182713 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv23,pv331]) (by decide +kernel)
def pv182713 : PrimeValue := ⟨182713, pr182713⟩
private theorem pr182773 : PrimeCertificate 182773 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5077]) (by decide +kernel)
def pv182773 : PrimeValue := ⟨182773, pr182773⟩
private theorem pr182779 : PrimeCertificate 182779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv743]) (by decide +kernel)
def pv182779 : PrimeValue := ⟨182779, pr182779⟩
private theorem pr182789 : PrimeCertificate 182789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv45697]) (by decide +kernel)
def pv182789 : PrimeValue := ⟨182789, pr182789⟩
private theorem pr182803 : PrimeCertificate 182803 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv30467]) (by decide +kernel)
def pv182803 : PrimeValue := ⟨182803, pr182803⟩
private theorem pr182813 : PrimeCertificate 182813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv6529]) (by decide +kernel)
def pv182813 : PrimeValue := ⟨182813, pr182813⟩
private theorem pr182821 : PrimeCertificate 182821 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv11,pv277]) (by decide +kernel)
def pv182821 : PrimeValue := ⟨182821, pr182821⟩
private theorem pr182839 : PrimeCertificate 182839 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv31,pv983]) (by decide +kernel)
def pv182839 : PrimeValue := ⟨182839, pr182839⟩
private theorem pr182857 : PrimeCertificate 182857 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv401]) (by decide +kernel)
def pv182857 : PrimeValue := ⟨182857, pr182857⟩
private theorem pr182867 : PrimeCertificate 182867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv91433]) (by decide +kernel)
def pv182867 : PrimeValue := ⟨182867, pr182867⟩
private theorem pr182887 : PrimeCertificate 182887 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv17,pv163]) (by decide +kernel)
def pv182887 : PrimeValue := ⟨182887, pr182887⟩
private theorem pr182893 : PrimeCertificate 182893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv15241]) (by decide +kernel)
def pv182893 : PrimeValue := ⟨182893, pr182893⟩
private theorem pr182899 : PrimeCertificate 182899 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv1129]) (by decide +kernel)
def pv182899 : PrimeValue := ⟨182899, pr182899⟩
private theorem pr182921 : PrimeCertificate 182921 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv17,pv269]) (by decide +kernel)
def pv182921 : PrimeValue := ⟨182921, pr182921⟩
private theorem pr182927 : PrimeCertificate 182927 :=
  certifyPrime (q := pv5) (ls := [pv2,pv91463]) (by decide +kernel)
def pv182927 : PrimeValue := ⟨182927, pr182927⟩
private theorem pr182933 : PrimeCertificate 182933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv29,pv83]) (by decide +kernel)
def pv182933 : PrimeValue := ⟨182933, pr182933⟩
private theorem pr182957 : PrimeCertificate 182957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv863]) (by decide +kernel)
def pv182957 : PrimeValue := ⟨182957, pr182957⟩
private theorem pr182969 : PrimeCertificate 182969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv22871]) (by decide +kernel)
def pv182969 : PrimeValue := ⟨182969, pr182969⟩
private theorem pr182999 : PrimeCertificate 182999 :=
  certifyPrime (q := pv11) (ls := [pv2,pv91499]) (by decide +kernel)
def pv182999 : PrimeValue := ⟨182999, pr182999⟩
private theorem pr183023 : PrimeCertificate 183023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv17,pv769]) (by decide +kernel)
def pv183023 : PrimeValue := ⟨183023, pr183023⟩
private theorem pr183037 : PrimeCertificate 183037 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv2179]) (by decide +kernel)
def pv183037 : PrimeValue := ⟨183037, pr183037⟩
private theorem pr183059 : PrimeCertificate 183059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv91529]) (by decide +kernel)
def pv183059 : PrimeValue := ⟨183059, pr183059⟩
private theorem pr183089 : PrimeCertificate 183089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11443]) (by decide +kernel)
def pv183089 : PrimeValue := ⟨183089, pr183089⟩
private theorem pr183091 : PrimeCertificate 183091 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv17,pv359]) (by decide +kernel)
def pv183091 : PrimeValue := ⟨183091, pr183091⟩
private theorem pr183119 : PrimeCertificate 183119 :=
  certifyPrime (q := pv17) (ls := [pv2,pv13,pv7043]) (by decide +kernel)
def pv183119 : PrimeValue := ⟨183119, pr183119⟩
private theorem pr183191 : PrimeCertificate 183191 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv2617]) (by decide +kernel)
def pv183191 : PrimeValue := ⟨183191, pr183191⟩
private theorem pr183203 : PrimeCertificate 183203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv139,pv659]) (by decide +kernel)
def pv183203 : PrimeValue := ⟨183203, pr183203⟩
private theorem pr183247 : PrimeCertificate 183247 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv4363]) (by decide +kernel)
def pv183247 : PrimeValue := ⟨183247, pr183247⟩
private theorem pr183283 : PrimeCertificate 183283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv2777]) (by decide +kernel)
def pv183283 : PrimeValue := ⟨183283, pr183283⟩
private theorem pr183289 : PrimeCertificate 183289 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv1091]) (by decide +kernel)
def pv183289 : PrimeValue := ⟨183289, pr183289⟩
private theorem pr183299 : PrimeCertificate 183299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv2477]) (by decide +kernel)
def pv183299 : PrimeValue := ⟨183299, pr183299⟩
private theorem pr183301 : PrimeCertificate 183301 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv13,pv47]) (by decide +kernel)
def pv183301 : PrimeValue := ⟨183301, pr183301⟩
private theorem pr183307 : PrimeCertificate 183307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv137,pv223]) (by decide +kernel)
def pv183307 : PrimeValue := ⟨183307, pr183307⟩
private theorem pr183319 : PrimeCertificate 183319 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv30553]) (by decide +kernel)
def pv183319 : PrimeValue := ⟨183319, pr183319⟩
private theorem pr183343 : PrimeCertificate 183343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv30557]) (by decide +kernel)
def pv183343 : PrimeValue := ⟨183343, pr183343⟩
private theorem pr183361 : PrimeCertificate 183361 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv191]) (by decide +kernel)
def pv183361 : PrimeValue := ⟨183361, pr183361⟩
private theorem pr183373 : PrimeCertificate 183373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv37,pv59]) (by decide +kernel)
def pv183373 : PrimeValue := ⟨183373, pr183373⟩
private theorem pr183377 : PrimeCertificate 183377 :=
  certifyPrime (q := pv3) (ls := [pv2,pv73,pv157]) (by decide +kernel)
def pv183377 : PrimeValue := ⟨183377, pr183377⟩
private theorem pr183383 : PrimeCertificate 183383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv91691]) (by decide +kernel)
def pv183383 : PrimeValue := ⟨183383, pr183383⟩
private theorem pr183389 : PrimeCertificate 183389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv127]) (by decide +kernel)
def pv183389 : PrimeValue := ⟨183389, pr183389⟩
private theorem pr183397 : PrimeCertificate 183397 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv29,pv31]) (by decide +kernel)
def pv183397 : PrimeValue := ⟨183397, pr183397⟩
private theorem pr183437 : PrimeCertificate 183437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv379]) (by decide +kernel)
def pv183437 : PrimeValue := ⟨183437, pr183437⟩
private theorem pr183439 : PrimeCertificate 183439 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv43,pv79]) (by decide +kernel)
def pv183439 : PrimeValue := ⟨183439, pr183439⟩
private theorem pr183451 : PrimeCertificate 183451 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1223]) (by decide +kernel)
def pv183451 : PrimeValue := ⟨183451, pr183451⟩
private theorem pr183461 : PrimeCertificate 183461 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv9173]) (by decide +kernel)
def pv183461 : PrimeValue := ⟨183461, pr183461⟩
private theorem pr183473 : PrimeCertificate 183473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11467]) (by decide +kernel)
def pv183473 : PrimeValue := ⟨183473, pr183473⟩
private theorem pr183487 : PrimeCertificate 183487 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv53,pv577]) (by decide +kernel)
def pv183487 : PrimeValue := ⟨183487, pr183487⟩
private theorem pr183499 : PrimeCertificate 183499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv257]) (by decide +kernel)
def pv183499 : PrimeValue := ⟨183499, pr183499⟩
private theorem pr183503 : PrimeCertificate 183503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv19,pv439]) (by decide +kernel)
def pv183503 : PrimeValue := ⟨183503, pr183503⟩
private theorem pr183509 : PrimeCertificate 183509 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv3529]) (by decide +kernel)
def pv183509 : PrimeValue := ⟨183509, pr183509⟩
private theorem pr183511 : PrimeCertificate 183511 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv2039]) (by decide +kernel)
def pv183511 : PrimeValue := ⟨183511, pr183511⟩
private theorem pr183523 : PrimeCertificate 183523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv73,pv419]) (by decide +kernel)
def pv183523 : PrimeValue := ⟨183523, pr183523⟩
private theorem pr183569 : PrimeCertificate 183569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11,pv149]) (by decide +kernel)
def pv183569 : PrimeValue := ⟨183569, pr183569⟩
private theorem pr183571 : PrimeCertificate 183571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv29,pv211]) (by decide +kernel)
def pv183571 : PrimeValue := ⟨183571, pr183571⟩
private theorem pr183581 : PrimeCertificate 183581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv67,pv137]) (by decide +kernel)
def pv183581 : PrimeValue := ⟨183581, pr183581⟩
private theorem pr183587 : PrimeCertificate 183587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv23,pv307]) (by decide +kernel)
def pv183587 : PrimeValue := ⟨183587, pr183587⟩
private theorem pr183593 : PrimeCertificate 183593 :=
  certifyPrime (q := pv3) (ls := [pv2,pv53,pv433]) (by decide +kernel)
def pv183593 : PrimeValue := ⟨183593, pr183593⟩
private theorem pr183611 : PrimeCertificate 183611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv43,pv61]) (by decide +kernel)
def pv183611 : PrimeValue := ⟨183611, pr183611⟩
private theorem pr183637 : PrimeCertificate 183637 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv5101]) (by decide +kernel)
def pv183637 : PrimeValue := ⟨183637, pr183637⟩
private theorem pr183661 : PrimeCertificate 183661 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv3061]) (by decide +kernel)
def pv183661 : PrimeValue := ⟨183661, pr183661⟩
private theorem pr183683 : PrimeCertificate 183683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv91841]) (by decide +kernel)
def pv183683 : PrimeValue := ⟨183683, pr183683⟩
private theorem pr183691 : PrimeCertificate 183691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv157]) (by decide +kernel)
def pv183691 : PrimeValue := ⟨183691, pr183691⟩
private theorem pr183697 : PrimeCertificate 183697 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv43,pv89]) (by decide +kernel)
def pv183697 : PrimeValue := ⟨183697, pr183697⟩
private theorem pr183707 : PrimeCertificate 183707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv2963]) (by decide +kernel)
def pv183707 : PrimeValue := ⟨183707, pr183707⟩
private theorem pr183709 : PrimeCertificate 183709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv183709 : PrimeValue := ⟨183709, pr183709⟩
private theorem pr183713 : PrimeCertificate 183713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5741]) (by decide +kernel)
def pv183713 : PrimeValue := ⟨183713, pr183713⟩
private theorem pr183761 : PrimeCertificate 183761 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv2297]) (by decide +kernel)
def pv183761 : PrimeValue := ⟨183761, pr183761⟩
private theorem pr183763 : PrimeCertificate 183763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv83]) (by decide +kernel)
def pv183763 : PrimeValue := ⟨183763, pr183763⟩
private theorem pr183797 : PrimeCertificate 183797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv45949]) (by decide +kernel)
def pv183797 : PrimeValue := ⟨183797, pr183797⟩
private theorem pr183809 : PrimeCertificate 183809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv359]) (by decide +kernel)
def pv183809 : PrimeValue := ⟨183809, pr183809⟩
private theorem pr183823 : PrimeCertificate 183823 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv30637]) (by decide +kernel)
def pv183823 : PrimeValue := ⟨183823, pr183823⟩
private theorem pr183829 : PrimeCertificate 183829 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv15319]) (by decide +kernel)
def pv183829 : PrimeValue := ⟨183829, pr183829⟩
private theorem pr183871 : PrimeCertificate 183871 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv227]) (by decide +kernel)
def pv183871 : PrimeValue := ⟨183871, pr183871⟩
private theorem pr183877 : PrimeCertificate 183877 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv199]) (by decide +kernel)
def pv183877 : PrimeValue := ⟨183877, pr183877⟩
private theorem pr183917 : PrimeCertificate 183917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv45979]) (by decide +kernel)
def pv183917 : PrimeValue := ⟨183917, pr183917⟩
private theorem pr183943 : PrimeCertificate 183943 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv929]) (by decide +kernel)
def pv183943 : PrimeValue := ⟨183943, pr183943⟩
private theorem pr183949 : PrimeCertificate 183949 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv15329]) (by decide +kernel)
def pv183949 : PrimeValue := ⟨183949, pr183949⟩
private theorem pr183973 : PrimeCertificate 183973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv15331]) (by decide +kernel)
def pv183973 : PrimeValue := ⟨183973, pr183973⟩
private theorem pr184003 : PrimeCertificate 184003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv337]) (by decide +kernel)
def pv184003 : PrimeValue := ⟨184003, pr184003⟩
private theorem pr184013 : PrimeCertificate 184013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv179,pv257]) (by decide +kernel)
def pv184013 : PrimeValue := ⟨184013, pr184013⟩
private theorem pr184031 : PrimeCertificate 184031 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv7,pv11,pv239]) (by decide +kernel)
def pv184031 : PrimeValue := ⟨184031, pr184031⟩
private theorem pr184043 : PrimeCertificate 184043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv5413]) (by decide +kernel)
def pv184043 : PrimeValue := ⟨184043, pr184043⟩
private theorem pr184057 : PrimeCertificate 184057 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7669]) (by decide +kernel)
def pv184057 : PrimeValue := ⟨184057, pr184057⟩
private theorem pr184087 : PrimeCertificate 184087 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv487]) (by decide +kernel)
def pv184087 : PrimeValue := ⟨184087, pr184087⟩
private theorem pr184111 : PrimeCertificate 184111 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv17,pv19]) (by decide +kernel)
def pv184111 : PrimeValue := ⟨184111, pr184111⟩
private theorem pr184117 : PrimeCertificate 184117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv67,pv229]) (by decide +kernel)
def pv184117 : PrimeValue := ⟨184117, pr184117⟩
private theorem pr184153 : PrimeCertificate 184153 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7673]) (by decide +kernel)
def pv184153 : PrimeValue := ⟨184153, pr184153⟩
private theorem pr184157 : PrimeCertificate 184157 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv6577]) (by decide +kernel)
def pv184157 : PrimeValue := ⟨184157, pr184157⟩
private theorem pr184181 : PrimeCertificate 184181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv9209]) (by decide +kernel)
def pv184181 : PrimeValue := ⟨184181, pr184181⟩
private theorem pr184189 : PrimeCertificate 184189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv15349]) (by decide +kernel)
def pv184189 : PrimeValue := ⟨184189, pr184189⟩
private theorem pr184199 : PrimeCertificate 184199 :=
  certifyPrime (q := pv13) (ls := [pv2,pv7,pv59,pv223]) (by decide +kernel)
def pv184199 : PrimeValue := ⟨184199, pr184199⟩
private theorem pr184211 : PrimeCertificate 184211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv109]) (by decide +kernel)
def pv184211 : PrimeValue := ⟨184211, pr184211⟩
private theorem pr184231 : PrimeCertificate 184231 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv23,pv89]) (by decide +kernel)
def pv184231 : PrimeValue := ⟨184231, pr184231⟩
private theorem pr184259 : PrimeCertificate 184259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv181,pv509]) (by decide +kernel)
def pv184259 : PrimeValue := ⟨184259, pr184259⟩
private theorem pr184271 : PrimeCertificate 184271 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv18427]) (by decide +kernel)
def pv184271 : PrimeValue := ⟨184271, pr184271⟩
private theorem pr184273 : PrimeCertificate 184273 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv349]) (by decide +kernel)
def pv184273 : PrimeValue := ⟨184273, pr184273⟩
private theorem pr184291 : PrimeCertificate 184291 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv6143]) (by decide +kernel)
def pv184291 : PrimeValue := ⟨184291, pr184291⟩
private theorem pr184309 : PrimeCertificate 184309 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv15359]) (by decide +kernel)
def pv184309 : PrimeValue := ⟨184309, pr184309⟩
private theorem pr184321 : PrimeCertificate 184321 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv184321 : PrimeValue := ⟨184321, pr184321⟩
private theorem pr184333 : PrimeCertificate 184333 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv15361]) (by decide +kernel)
def pv184333 : PrimeValue := ⟨184333, pr184333⟩
private theorem pr184337 : PrimeCertificate 184337 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41,pv281]) (by decide +kernel)
def pv184337 : PrimeValue := ⟨184337, pr184337⟩
private theorem pr184351 : PrimeCertificate 184351 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv1229]) (by decide +kernel)
def pv184351 : PrimeValue := ⟨184351, pr184351⟩
private theorem pr184369 : PrimeCertificate 184369 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv23,pv167]) (by decide +kernel)
def pv184369 : PrimeValue := ⟨184369, pr184369⟩
private theorem pr184409 : PrimeCertificate 184409 :=
  certifyPrime (q := pv17) (ls := [pv2,pv7,pv37,pv89]) (by decide +kernel)
def pv184409 : PrimeValue := ⟨184409, pr184409⟩
private theorem pr184441 : PrimeCertificate 184441 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv29,pv53]) (by decide +kernel)
def pv184441 : PrimeValue := ⟨184441, pr184441⟩
private theorem pr184463 : PrimeCertificate 184463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv149,pv619]) (by decide +kernel)
def pv184463 : PrimeValue := ⟨184463, pr184463⟩
private theorem pr184487 : PrimeCertificate 184487 :=
  certifyPrime (q := pv5) (ls := [pv2,pv92243]) (by decide +kernel)
def pv184487 : PrimeValue := ⟨184487, pr184487⟩
private theorem pr184489 : PrimeCertificate 184489 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7687]) (by decide +kernel)
def pv184489 : PrimeValue := ⟨184489, pr184489⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
