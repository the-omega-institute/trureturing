/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table033
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table033.pv85247
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table006
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table017
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table018

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr85247 : PrimeCertificate 85247 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv6089]) (by decide +kernel)
def pv85247 : PrimeValue := ⟨85247, pr85247⟩
private theorem pr85259 : PrimeCertificate 85259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv907]) (by decide +kernel)
def pv85259 : PrimeValue := ⟨85259, pr85259⟩
private theorem pr85297 : PrimeCertificate 85297 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv1777]) (by decide +kernel)
def pv85297 : PrimeValue := ⟨85297, pr85297⟩
private theorem pr85303 : PrimeCertificate 85303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv677]) (by decide +kernel)
def pv85303 : PrimeValue := ⟨85303, pr85303⟩
private theorem pr85313 : PrimeCertificate 85313 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv43]) (by decide +kernel)
def pv85313 : PrimeValue := ⟨85313, pr85313⟩
private theorem pr85331 : PrimeCertificate 85331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv23,pv53]) (by decide +kernel)
def pv85331 : PrimeValue := ⟨85331, pr85331⟩
private theorem pr85333 : PrimeCertificate 85333 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv547]) (by decide +kernel)
def pv85333 : PrimeValue := ⟨85333, pr85333⟩
private theorem pr85361 : PrimeCertificate 85361 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv97]) (by decide +kernel)
def pv85361 : PrimeValue := ⟨85361, pr85361⟩
private theorem pr85363 : PrimeCertificate 85363 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41,pv347]) (by decide +kernel)
def pv85363 : PrimeValue := ⟨85363, pr85363⟩
private theorem pr85369 : PrimeCertificate 85369 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv3557]) (by decide +kernel)
def pv85369 : PrimeValue := ⟨85369, pr85369⟩
private theorem pr85381 : PrimeCertificate 85381 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv1423]) (by decide +kernel)
def pv85381 : PrimeValue := ⟨85381, pr85381⟩
private theorem pr85411 : PrimeCertificate 85411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv73]) (by decide +kernel)
def pv85411 : PrimeValue := ⟨85411, pr85411⟩
private theorem pr85427 : PrimeCertificate 85427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv353]) (by decide +kernel)
def pv85427 : PrimeValue := ⟨85427, pr85427⟩
private theorem pr85429 : PrimeCertificate 85429 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv7,pv113]) (by decide +kernel)
def pv85429 : PrimeValue := ⟨85429, pr85429⟩
private theorem pr85439 : PrimeCertificate 85439 :=
  certifyPrime (q := pv7) (ls := [pv2,pv42719]) (by decide +kernel)
def pv85439 : PrimeValue := ⟨85439, pr85439⟩
private theorem pr85447 : PrimeCertificate 85447 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv47,pv101]) (by decide +kernel)
def pv85447 : PrimeValue := ⟨85447, pr85447⟩
private theorem pr85451 : PrimeCertificate 85451 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1709]) (by decide +kernel)
def pv85451 : PrimeValue := ⟨85451, pr85451⟩
private theorem pr85453 : PrimeCertificate 85453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7121]) (by decide +kernel)
def pv85453 : PrimeValue := ⟨85453, pr85453⟩
private theorem pr85469 : PrimeCertificate 85469 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv929]) (by decide +kernel)
def pv85469 : PrimeValue := ⟨85469, pr85469⟩
private theorem pr85487 : PrimeCertificate 85487 :=
  certifyPrime (q := pv5) (ls := [pv2,pv42743]) (by decide +kernel)
def pv85487 : PrimeValue := ⟨85487, pr85487⟩
private theorem pr85513 : PrimeCertificate 85513 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv509]) (by decide +kernel)
def pv85513 : PrimeValue := ⟨85513, pr85513⟩
private theorem pr85517 : PrimeCertificate 85517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv21379]) (by decide +kernel)
def pv85517 : PrimeValue := ⟨85517, pr85517⟩
private theorem pr85523 : PrimeCertificate 85523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv701]) (by decide +kernel)
def pv85523 : PrimeValue := ⟨85523, pr85523⟩
private theorem pr85531 : PrimeCertificate 85531 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv2851]) (by decide +kernel)
def pv85531 : PrimeValue := ⟨85531, pr85531⟩
private theorem pr85549 : PrimeCertificate 85549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7129]) (by decide +kernel)
def pv85549 : PrimeValue := ⟨85549, pr85549⟩
private theorem pr85571 : PrimeCertificate 85571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv43,pv199]) (by decide +kernel)
def pv85571 : PrimeValue := ⟨85571, pr85571⟩
private theorem pr85577 : PrimeCertificate 85577 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv563]) (by decide +kernel)
def pv85577 : PrimeValue := ⟨85577, pr85577⟩
private theorem pr85597 : PrimeCertificate 85597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1019]) (by decide +kernel)
def pv85597 : PrimeValue := ⟨85597, pr85597⟩
private theorem pr85601 : PrimeCertificate 85601 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv107]) (by decide +kernel)
def pv85601 : PrimeValue := ⟨85601, pr85601⟩
private theorem pr85607 : PrimeCertificate 85607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv1861]) (by decide +kernel)
def pv85607 : PrimeValue := ⟨85607, pr85607⟩
private theorem pr85619 : PrimeCertificate 85619 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv37,pv89]) (by decide +kernel)
def pv85619 : PrimeValue := ⟨85619, pr85619⟩
private theorem pr85621 : PrimeCertificate 85621 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv1427]) (by decide +kernel)
def pv85621 : PrimeValue := ⟨85621, pr85621⟩
private theorem pr85639 : PrimeCertificate 85639 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv2039]) (by decide +kernel)
def pv85639 : PrimeValue := ⟨85639, pr85639⟩
private theorem pr85643 : PrimeCertificate 85643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv42821]) (by decide +kernel)
def pv85643 : PrimeValue := ⟨85643, pr85643⟩
private theorem pr85661 : PrimeCertificate 85661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv4283]) (by decide +kernel)
def pv85661 : PrimeValue := ⟨85661, pr85661⟩
private theorem pr85667 : PrimeCertificate 85667 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv29,pv211]) (by decide +kernel)
def pv85667 : PrimeValue := ⟨85667, pr85667⟩
private theorem pr85669 : PrimeCertificate 85669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv59]) (by decide +kernel)
def pv85669 : PrimeValue := ⟨85669, pr85669⟩
private theorem pr85691 : PrimeCertificate 85691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv19,pv41]) (by decide +kernel)
def pv85691 : PrimeValue := ⟨85691, pr85691⟩
private theorem pr85703 : PrimeCertificate 85703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv73,pv587]) (by decide +kernel)
def pv85703 : PrimeValue := ⟨85703, pr85703⟩
private theorem pr85717 : PrimeCertificate 85717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv2381]) (by decide +kernel)
def pv85717 : PrimeValue := ⟨85717, pr85717⟩
private theorem pr85733 : PrimeCertificate 85733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv21433]) (by decide +kernel)
def pv85733 : PrimeValue := ⟨85733, pr85733⟩
private theorem pr85751 : PrimeCertificate 85751 :=
  certifyPrime (q := pv31) (ls := [pv2,pv5,pv7]) (by decide +kernel)
def pv85751 : PrimeValue := ⟨85751, pr85751⟩
private theorem pr85781 : PrimeCertificate 85781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv4289]) (by decide +kernel)
def pv85781 : PrimeValue := ⟨85781, pr85781⟩
private theorem pr85793 : PrimeCertificate 85793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv383]) (by decide +kernel)
def pv85793 : PrimeValue := ⟨85793, pr85793⟩
private theorem pr85817 : PrimeCertificate 85817 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv631]) (by decide +kernel)
def pv85817 : PrimeValue := ⟨85817, pr85817⟩
private theorem pr85819 : PrimeCertificate 85819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv14303]) (by decide +kernel)
def pv85819 : PrimeValue := ⟨85819, pr85819⟩
private theorem pr85829 : PrimeCertificate 85829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv499]) (by decide +kernel)
def pv85829 : PrimeValue := ⟨85829, pr85829⟩
private theorem pr85831 : PrimeCertificate 85831 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv2861]) (by decide +kernel)
def pv85831 : PrimeValue := ⟨85831, pr85831⟩
private theorem pr85837 : PrimeCertificate 85837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv311]) (by decide +kernel)
def pv85837 : PrimeValue := ⟨85837, pr85837⟩
private theorem pr85843 : PrimeCertificate 85843 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv251]) (by decide +kernel)
def pv85843 : PrimeValue := ⟨85843, pr85843⟩
private theorem pr85847 : PrimeCertificate 85847 :=
  certifyPrime (q := pv5) (ls := [pv2,pv42923]) (by decide +kernel)
def pv85847 : PrimeValue := ⟨85847, pr85847⟩
private theorem pr85853 : PrimeCertificate 85853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv127]) (by decide +kernel)
def pv85853 : PrimeValue := ⟨85853, pr85853⟩
private theorem pr85889 : PrimeCertificate 85889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv61]) (by decide +kernel)
def pv85889 : PrimeValue := ⟨85889, pr85889⟩
private theorem pr85903 : PrimeCertificate 85903 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv103,pv139]) (by decide +kernel)
def pv85903 : PrimeValue := ⟨85903, pr85903⟩
private theorem pr85909 : PrimeCertificate 85909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7159]) (by decide +kernel)
def pv85909 : PrimeValue := ⟨85909, pr85909⟩
private theorem pr85931 : PrimeCertificate 85931 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv661]) (by decide +kernel)
def pv85931 : PrimeValue := ⟨85931, pr85931⟩
private theorem pr85933 : PrimeCertificate 85933 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv31]) (by decide +kernel)
def pv85933 : PrimeValue := ⟨85933, pr85933⟩
private theorem pr85991 : PrimeCertificate 85991 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv8599]) (by decide +kernel)
def pv85991 : PrimeValue := ⟨85991, pr85991⟩
private theorem pr85999 : PrimeCertificate 85999 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv1303]) (by decide +kernel)
def pv85999 : PrimeValue := ⟨85999, pr85999⟩
private theorem pr86011 : PrimeCertificate 86011 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv47,pv61]) (by decide +kernel)
def pv86011 : PrimeValue := ⟨86011, pr86011⟩
private theorem pr86017 : PrimeCertificate 86017 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv86017 : PrimeValue := ⟨86017, pr86017⟩
private theorem pr86027 : PrimeCertificate 86027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43013]) (by decide +kernel)
def pv86027 : PrimeValue := ⟨86027, pr86027⟩
private theorem pr86029 : PrimeCertificate 86029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv67,pv107]) (by decide +kernel)
def pv86029 : PrimeValue := ⟨86029, pr86029⟩
private theorem pr86069 : PrimeCertificate 86069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv21517]) (by decide +kernel)
def pv86069 : PrimeValue := ⟨86069, pr86069⟩
private theorem pr86077 : PrimeCertificate 86077 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv797]) (by decide +kernel)
def pv86077 : PrimeValue := ⟨86077, pr86077⟩
private theorem pr86083 : PrimeCertificate 86083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv14347]) (by decide +kernel)
def pv86083 : PrimeValue := ⟨86083, pr86083⟩
private theorem pr86111 : PrimeCertificate 86111 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv79,pv109]) (by decide +kernel)
def pv86111 : PrimeValue := ⟨86111, pr86111⟩
private theorem pr86113 : PrimeCertificate 86113 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv23]) (by decide +kernel)
def pv86113 : PrimeValue := ⟨86113, pr86113⟩
private theorem pr86117 : PrimeCertificate 86117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv21529]) (by decide +kernel)
def pv86117 : PrimeValue := ⟨86117, pr86117⟩
private theorem pr86131 : PrimeCertificate 86131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv29]) (by decide +kernel)
def pv86131 : PrimeValue := ⟨86131, pr86131⟩
private theorem pr86137 : PrimeCertificate 86137 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv37,pv97]) (by decide +kernel)
def pv86137 : PrimeValue := ⟨86137, pr86137⟩
private theorem pr86143 : PrimeCertificate 86143 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv293]) (by decide +kernel)
def pv86143 : PrimeValue := ⟨86143, pr86143⟩
private theorem pr86161 : PrimeCertificate 86161 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv359]) (by decide +kernel)
def pv86161 : PrimeValue := ⟨86161, pr86161⟩
private theorem pr86171 : PrimeCertificate 86171 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv1231]) (by decide +kernel)
def pv86171 : PrimeValue := ⟨86171, pr86171⟩
private theorem pr86179 : PrimeCertificate 86179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53,pv271]) (by decide +kernel)
def pv86179 : PrimeValue := ⟨86179, pr86179⟩
private theorem pr86183 : PrimeCertificate 86183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv41,pv1051]) (by decide +kernel)
def pv86183 : PrimeValue := ⟨86183, pr86183⟩
private theorem pr86197 : PrimeCertificate 86197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv653]) (by decide +kernel)
def pv86197 : PrimeValue := ⟨86197, pr86197⟩
private theorem pr86201 : PrimeCertificate 86201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv431]) (by decide +kernel)
def pv86201 : PrimeValue := ⟨86201, pr86201⟩
private theorem pr86209 : PrimeCertificate 86209 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv449]) (by decide +kernel)
def pv86209 : PrimeValue := ⟨86209, pr86209⟩
private theorem pr86239 : PrimeCertificate 86239 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1597]) (by decide +kernel)
def pv86239 : PrimeValue := ⟨86239, pr86239⟩
private theorem pr86243 : PrimeCertificate 86243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv31,pv107]) (by decide +kernel)
def pv86243 : PrimeValue := ⟨86243, pr86243⟩
private theorem pr86249 : PrimeCertificate 86249 :=
  certifyPrime (q := pv3) (ls := [pv2,pv10781]) (by decide +kernel)
def pv86249 : PrimeValue := ⟨86249, pr86249⟩
private theorem pr86257 : PrimeCertificate 86257 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv599]) (by decide +kernel)
def pv86257 : PrimeValue := ⟨86257, pr86257⟩
private theorem pr86263 : PrimeCertificate 86263 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv1307]) (by decide +kernel)
def pv86263 : PrimeValue := ⟨86263, pr86263⟩
private theorem pr86269 : PrimeCertificate 86269 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv13,pv79]) (by decide +kernel)
def pv86269 : PrimeValue := ⟨86269, pr86269⟩
private theorem pr86287 : PrimeCertificate 86287 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv73,pv197]) (by decide +kernel)
def pv86287 : PrimeValue := ⟨86287, pr86287⟩
private theorem pr86291 : PrimeCertificate 86291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv8629]) (by decide +kernel)
def pv86291 : PrimeValue := ⟨86291, pr86291⟩
private theorem pr86293 : PrimeCertificate 86293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv47]) (by decide +kernel)
def pv86293 : PrimeValue := ⟨86293, pr86293⟩
private theorem pr86297 : PrimeCertificate 86297 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv23,pv67]) (by decide +kernel)
def pv86297 : PrimeValue := ⟨86297, pr86297⟩
private theorem pr86311 : PrimeCertificate 86311 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv137]) (by decide +kernel)
def pv86311 : PrimeValue := ⟨86311, pr86311⟩
private theorem pr86323 : PrimeCertificate 86323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv14387]) (by decide +kernel)
def pv86323 : PrimeValue := ⟨86323, pr86323⟩
private theorem pr86341 : PrimeCertificate 86341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1439]) (by decide +kernel)
def pv86341 : PrimeValue := ⟨86341, pr86341⟩
private theorem pr86351 : PrimeCertificate 86351 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv11,pv157]) (by decide +kernel)
def pv86351 : PrimeValue := ⟨86351, pr86351⟩
private theorem pr86353 : PrimeCertificate 86353 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv257]) (by decide +kernel)
def pv86353 : PrimeValue := ⟨86353, pr86353⟩
private theorem pr86357 : PrimeCertificate 86357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv21589]) (by decide +kernel)
def pv86357 : PrimeValue := ⟨86357, pr86357⟩
private theorem pr86369 : PrimeCertificate 86369 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2699]) (by decide +kernel)
def pv86369 : PrimeValue := ⟨86369, pr86369⟩
private theorem pr86371 : PrimeCertificate 86371 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv2879]) (by decide +kernel)
def pv86371 : PrimeValue := ⟨86371, pr86371⟩
private theorem pr86389 : PrimeCertificate 86389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv313]) (by decide +kernel)
def pv86389 : PrimeValue := ⟨86389, pr86389⟩
private theorem pr86399 : PrimeCertificate 86399 :=
  certifyPrime (q := pv11) (ls := [pv2,pv13,pv3323]) (by decide +kernel)
def pv86399 : PrimeValue := ⟨86399, pr86399⟩
private theorem pr86413 : PrimeCertificate 86413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv379]) (by decide +kernel)
def pv86413 : PrimeValue := ⟨86413, pr86413⟩
private theorem pr86423 : PrimeCertificate 86423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv6173]) (by decide +kernel)
def pv86423 : PrimeValue := ⟨86423, pr86423⟩
private theorem pr86441 : PrimeCertificate 86441 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv2161]) (by decide +kernel)
def pv86441 : PrimeValue := ⟨86441, pr86441⟩
private theorem pr86453 : PrimeCertificate 86453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv21613]) (by decide +kernel)
def pv86453 : PrimeValue := ⟨86453, pr86453⟩
private theorem pr86461 : PrimeCertificate 86461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv131]) (by decide +kernel)
def pv86461 : PrimeValue := ⟨86461, pr86461⟩
private theorem pr86467 : PrimeCertificate 86467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv14411]) (by decide +kernel)
def pv86467 : PrimeValue := ⟨86467, pr86467⟩
private theorem pr86477 : PrimeCertificate 86477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv1663]) (by decide +kernel)
def pv86477 : PrimeValue := ⟨86477, pr86477⟩
private theorem pr86491 : PrimeCertificate 86491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv31]) (by decide +kernel)
def pv86491 : PrimeValue := ⟨86491, pr86491⟩
private theorem pr86501 : PrimeCertificate 86501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv173]) (by decide +kernel)
def pv86501 : PrimeValue := ⟨86501, pr86501⟩
private theorem pr86509 : PrimeCertificate 86509 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv89]) (by decide +kernel)
def pv86509 : PrimeValue := ⟨86509, pr86509⟩
private theorem pr86531 : PrimeCertificate 86531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv509]) (by decide +kernel)
def pv86531 : PrimeValue := ⟨86531, pr86531⟩
private theorem pr86533 : PrimeCertificate 86533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7211]) (by decide +kernel)
def pv86533 : PrimeValue := ⟨86533, pr86533⟩
private theorem pr86539 : PrimeCertificate 86539 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv14423]) (by decide +kernel)
def pv86539 : PrimeValue := ⟨86539, pr86539⟩
private theorem pr86561 : PrimeCertificate 86561 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv541]) (by decide +kernel)
def pv86561 : PrimeValue := ⟨86561, pr86561⟩
private theorem pr86573 : PrimeCertificate 86573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv941]) (by decide +kernel)
def pv86573 : PrimeValue := ⟨86573, pr86573⟩
private theorem pr86579 : PrimeCertificate 86579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv593]) (by decide +kernel)
def pv86579 : PrimeValue := ⟨86579, pr86579⟩
private theorem pr86587 : PrimeCertificate 86587 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv14431]) (by decide +kernel)
def pv86587 : PrimeValue := ⟨86587, pr86587⟩
private theorem pr86599 : PrimeCertificate 86599 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv283]) (by decide +kernel)
def pv86599 : PrimeValue := ⟨86599, pr86599⟩
private theorem pr86627 : PrimeCertificate 86627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43313]) (by decide +kernel)
def pv86627 : PrimeValue := ⟨86627, pr86627⟩
private theorem pr86629 : PrimeCertificate 86629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7219]) (by decide +kernel)
def pv86629 : PrimeValue := ⟨86629, pr86629⟩
private theorem pr86677 : PrimeCertificate 86677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv233]) (by decide +kernel)
def pv86677 : PrimeValue := ⟨86677, pr86677⟩
private theorem pr86711 : PrimeCertificate 86711 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv23,pv29]) (by decide +kernel)
def pv86711 : PrimeValue := ⟨86711, pr86711⟩
private theorem pr86719 : PrimeCertificate 86719 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv97,pv149]) (by decide +kernel)
def pv86719 : PrimeValue := ⟨86719, pr86719⟩
private theorem pr86729 : PrimeCertificate 86729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv293]) (by decide +kernel)
def pv86729 : PrimeValue := ⟨86729, pr86729⟩
private theorem pr86743 : PrimeCertificate 86743 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv61,pv79]) (by decide +kernel)
def pv86743 : PrimeValue := ⟨86743, pr86743⟩
private theorem pr86767 : PrimeCertificate 86767 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv14461]) (by decide +kernel)
def pv86767 : PrimeValue := ⟨86767, pr86767⟩
private theorem pr86771 : PrimeCertificate 86771 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv8677]) (by decide +kernel)
def pv86771 : PrimeValue := ⟨86771, pr86771⟩
private theorem pr86783 : PrimeCertificate 86783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv43391]) (by decide +kernel)
def pv86783 : PrimeValue := ⟨86783, pr86783⟩
private theorem pr86813 : PrimeCertificate 86813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv1973]) (by decide +kernel)
def pv86813 : PrimeValue := ⟨86813, pr86813⟩
private theorem pr86837 : PrimeCertificate 86837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv1277]) (by decide +kernel)
def pv86837 : PrimeValue := ⟨86837, pr86837⟩
private theorem pr86843 : PrimeCertificate 86843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv6203]) (by decide +kernel)
def pv86843 : PrimeValue := ⟨86843, pr86843⟩
private theorem pr86851 : PrimeCertificate 86851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv193]) (by decide +kernel)
def pv86851 : PrimeValue := ⟨86851, pr86851⟩
private theorem pr86857 : PrimeCertificate 86857 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv7,pv11,pv47]) (by decide +kernel)
def pv86857 : PrimeValue := ⟨86857, pr86857⟩
private theorem pr86861 : PrimeCertificate 86861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv43,pv101]) (by decide +kernel)
def pv86861 : PrimeValue := ⟨86861, pr86861⟩
private theorem pr86869 : PrimeCertificate 86869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv127]) (by decide +kernel)
def pv86869 : PrimeValue := ⟨86869, pr86869⟩
private theorem pr86923 : PrimeCertificate 86923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv439]) (by decide +kernel)
def pv86923 : PrimeValue := ⟨86923, pr86923⟩
private theorem pr86929 : PrimeCertificate 86929 :=
  certifyPrime (q := pv47) (ls := [pv2,pv3,pv1811]) (by decide +kernel)
def pv86929 : PrimeValue := ⟨86929, pr86929⟩
private theorem pr86939 : PrimeCertificate 86939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv2557]) (by decide +kernel)
def pv86939 : PrimeValue := ⟨86939, pr86939⟩
private theorem pr86951 : PrimeCertificate 86951 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv37,pv47]) (by decide +kernel)
def pv86951 : PrimeValue := ⟨86951, pr86951⟩
private theorem pr86959 : PrimeCertificate 86959 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv4831]) (by decide +kernel)
def pv86959 : PrimeValue := ⟨86959, pr86959⟩
private theorem pr86969 : PrimeCertificate 86969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv1553]) (by decide +kernel)
def pv86969 : PrimeValue := ⟨86969, pr86969⟩
private theorem pr86981 : PrimeCertificate 86981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv4349]) (by decide +kernel)
def pv86981 : PrimeValue := ⟨86981, pr86981⟩
private theorem pr86993 : PrimeCertificate 86993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5437]) (by decide +kernel)
def pv86993 : PrimeValue := ⟨86993, pr86993⟩
private theorem pr87011 : PrimeCertificate 87011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv113]) (by decide +kernel)
def pv87011 : PrimeValue := ⟨87011, pr87011⟩
private theorem pr87013 : PrimeCertificate 87013 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2417]) (by decide +kernel)
def pv87013 : PrimeValue := ⟨87013, pr87013⟩
private theorem pr87037 : PrimeCertificate 87037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7253]) (by decide +kernel)
def pv87037 : PrimeValue := ⟨87037, pr87037⟩
private theorem pr87041 : PrimeCertificate 87041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17]) (by decide +kernel)
def pv87041 : PrimeValue := ⟨87041, pr87041⟩
private theorem pr87049 : PrimeCertificate 87049 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv13,pv31]) (by decide +kernel)
def pv87049 : PrimeValue := ⟨87049, pr87049⟩
private theorem pr87071 : PrimeCertificate 87071 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv8707]) (by decide +kernel)
def pv87071 : PrimeValue := ⟨87071, pr87071⟩
private theorem pr87083 : PrimeCertificate 87083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43541]) (by decide +kernel)
def pv87083 : PrimeValue := ⟨87083, pr87083⟩
private theorem pr87103 : PrimeCertificate 87103 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1613]) (by decide +kernel)
def pv87103 : PrimeValue := ⟨87103, pr87103⟩
private theorem pr87107 : PrimeCertificate 87107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv97,pv449]) (by decide +kernel)
def pv87107 : PrimeValue := ⟨87107, pr87107⟩
private theorem pr87119 : PrimeCertificate 87119 :=
  certifyPrime (q := pv7) (ls := [pv2,pv43,pv1013]) (by decide +kernel)
def pv87119 : PrimeValue := ⟨87119, pr87119⟩
private theorem pr87121 : PrimeCertificate 87121 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv87121 : PrimeValue := ⟨87121, pr87121⟩
private theorem pr87133 : PrimeCertificate 87133 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv53,pv137]) (by decide +kernel)
def pv87133 : PrimeValue := ⟨87133, pr87133⟩
private theorem pr87149 : PrimeCertificate 87149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv21787]) (by decide +kernel)
def pv87149 : PrimeValue := ⟨87149, pr87149⟩
private theorem pr87151 : PrimeCertificate 87151 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv83]) (by decide +kernel)
def pv87151 : PrimeValue := ⟨87151, pr87151⟩
private theorem pr87179 : PrimeCertificate 87179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv479]) (by decide +kernel)
def pv87179 : PrimeValue := ⟨87179, pr87179⟩
private theorem pr87181 : PrimeCertificate 87181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1453]) (by decide +kernel)
def pv87181 : PrimeValue := ⟨87181, pr87181⟩
private theorem pr87187 : PrimeCertificate 87187 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv1321]) (by decide +kernel)
def pv87187 : PrimeValue := ⟨87187, pr87187⟩
private theorem pr87211 : PrimeCertificate 87211 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv17,pv19]) (by decide +kernel)
def pv87211 : PrimeValue := ⟨87211, pr87211⟩
private theorem pr87221 : PrimeCertificate 87221 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv89]) (by decide +kernel)
def pv87221 : PrimeValue := ⟨87221, pr87221⟩
private theorem pr87223 : PrimeCertificate 87223 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv14537]) (by decide +kernel)
def pv87223 : PrimeValue := ⟨87223, pr87223⟩
private theorem pr87251 : PrimeCertificate 87251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv349]) (by decide +kernel)
def pv87251 : PrimeValue := ⟨87251, pr87251⟩
private theorem pr87253 : PrimeCertificate 87253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv661]) (by decide +kernel)
def pv87253 : PrimeValue := ⟨87253, pr87253⟩
private theorem pr87257 : PrimeCertificate 87257 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv839]) (by decide +kernel)
def pv87257 : PrimeValue := ⟨87257, pr87257⟩
private theorem pr87277 : PrimeCertificate 87277 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv1039]) (by decide +kernel)
def pv87277 : PrimeValue := ⟨87277, pr87277⟩
private theorem pr87281 : PrimeCertificate 87281 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1091]) (by decide +kernel)
def pv87281 : PrimeValue := ⟨87281, pr87281⟩
private theorem pr87293 : PrimeCertificate 87293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv139,pv157]) (by decide +kernel)
def pv87293 : PrimeValue := ⟨87293, pr87293⟩
private theorem pr87299 : PrimeCertificate 87299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43649]) (by decide +kernel)
def pv87299 : PrimeValue := ⟨87299, pr87299⟩
private theorem pr87313 : PrimeCertificate 87313 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv107]) (by decide +kernel)
def pv87313 : PrimeValue := ⟨87313, pr87313⟩
private theorem pr87317 : PrimeCertificate 87317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv83,pv263]) (by decide +kernel)
def pv87317 : PrimeValue := ⟨87317, pr87317⟩
private theorem pr87323 : PrimeCertificate 87323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43661]) (by decide +kernel)
def pv87323 : PrimeValue := ⟨87323, pr87323⟩
private theorem pr87337 : PrimeCertificate 87337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1213]) (by decide +kernel)
def pv87337 : PrimeValue := ⟨87337, pr87337⟩
private theorem pr87359 : PrimeCertificate 87359 :=
  certifyPrime (q := pv19) (ls := [pv2,pv31,pv1409]) (by decide +kernel)
def pv87359 : PrimeValue := ⟨87359, pr87359⟩
private theorem pr87383 : PrimeCertificate 87383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv43691]) (by decide +kernel)
def pv87383 : PrimeValue := ⟨87383, pr87383⟩
private theorem pr87403 : PrimeCertificate 87403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv2081]) (by decide +kernel)
def pv87403 : PrimeValue := ⟨87403, pr87403⟩
private theorem pr87407 : PrimeCertificate 87407 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv29,pv137]) (by decide +kernel)
def pv87407 : PrimeValue := ⟨87407, pr87407⟩
private theorem pr87421 : PrimeCertificate 87421 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv31,pv47]) (by decide +kernel)
def pv87421 : PrimeValue := ⟨87421, pr87421⟩
private theorem pr87427 : PrimeCertificate 87427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1619]) (by decide +kernel)
def pv87427 : PrimeValue := ⟨87427, pr87427⟩
private theorem pr87433 : PrimeCertificate 87433 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3643]) (by decide +kernel)
def pv87433 : PrimeValue := ⟨87433, pr87433⟩
private theorem pr87443 : PrimeCertificate 87443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43721]) (by decide +kernel)
def pv87443 : PrimeValue := ⟨87443, pr87443⟩
private theorem pr87473 : PrimeCertificate 87473 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11,pv71]) (by decide +kernel)
def pv87473 : PrimeValue := ⟨87473, pr87473⟩
private theorem pr87481 : PrimeCertificate 87481 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv87481 : PrimeValue := ⟨87481, pr87481⟩
private theorem pr87491 : PrimeCertificate 87491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv673]) (by decide +kernel)
def pv87491 : PrimeValue := ⟨87491, pr87491⟩
private theorem pr87509 : PrimeCertificate 87509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv131,pv167]) (by decide +kernel)
def pv87509 : PrimeValue := ⟨87509, pr87509⟩
private theorem pr87511 : PrimeCertificate 87511 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv2917]) (by decide +kernel)
def pv87511 : PrimeValue := ⟨87511, pr87511⟩
private theorem pr87517 : PrimeCertificate 87517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv13,pv17]) (by decide +kernel)
def pv87517 : PrimeValue := ⟨87517, pr87517⟩
private theorem pr87523 : PrimeCertificate 87523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv503]) (by decide +kernel)
def pv87523 : PrimeValue := ⟨87523, pr87523⟩
private theorem pr87539 : PrimeCertificate 87539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv23,pv173]) (by decide +kernel)
def pv87539 : PrimeValue := ⟨87539, pr87539⟩
private theorem pr87541 : PrimeCertificate 87541 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv1459]) (by decide +kernel)
def pv87541 : PrimeValue := ⟨87541, pr87541⟩
private theorem pr87547 : PrimeCertificate 87547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv14591]) (by decide +kernel)
def pv87547 : PrimeValue := ⟨87547, pr87547⟩
private theorem pr87553 : PrimeCertificate 87553 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19]) (by decide +kernel)
def pv87553 : PrimeValue := ⟨87553, pr87553⟩
private theorem pr87557 : PrimeCertificate 87557 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv53,pv59]) (by decide +kernel)
def pv87557 : PrimeValue := ⟨87557, pr87557⟩
private theorem pr87559 : PrimeCertificate 87559 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv14593]) (by decide +kernel)
def pv87559 : PrimeValue := ⟨87559, pr87559⟩
private theorem pr87583 : PrimeCertificate 87583 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv1327]) (by decide +kernel)
def pv87583 : PrimeValue := ⟨87583, pr87583⟩
private theorem pr87587 : PrimeCertificate 87587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43793]) (by decide +kernel)
def pv87587 : PrimeValue := ⟨87587, pr87587⟩
private theorem pr87589 : PrimeCertificate 87589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv811]) (by decide +kernel)
def pv87589 : PrimeValue := ⟨87589, pr87589⟩
private theorem pr87613 : PrimeCertificate 87613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv149]) (by decide +kernel)
def pv87613 : PrimeValue := ⟨87613, pr87613⟩
private theorem pr87623 : PrimeCertificate 87623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv193,pv227]) (by decide +kernel)
def pv87623 : PrimeValue := ⟨87623, pr87623⟩
private theorem pr87629 : PrimeCertificate 87629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv1153]) (by decide +kernel)
def pv87629 : PrimeValue := ⟨87629, pr87629⟩
private theorem pr87631 : PrimeCertificate 87631 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv23,pv127]) (by decide +kernel)
def pv87631 : PrimeValue := ⟨87631, pr87631⟩
private theorem pr87641 : PrimeCertificate 87641 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv313]) (by decide +kernel)
def pv87641 : PrimeValue := ⟨87641, pr87641⟩
private theorem pr87643 : PrimeCertificate 87643 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv541]) (by decide +kernel)
def pv87643 : PrimeValue := ⟨87643, pr87643⟩
private theorem pr87649 : PrimeCertificate 87649 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv11,pv83]) (by decide +kernel)
def pv87649 : PrimeValue := ⟨87649, pr87649⟩
private theorem pr87671 : PrimeCertificate 87671 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv797]) (by decide +kernel)
def pv87671 : PrimeValue := ⟨87671, pr87671⟩
private theorem pr87679 : PrimeCertificate 87679 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv4871]) (by decide +kernel)
def pv87679 : PrimeValue := ⟨87679, pr87679⟩
private theorem pr87683 : PrimeCertificate 87683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv6263]) (by decide +kernel)
def pv87683 : PrimeValue := ⟨87683, pr87683⟩
private theorem pr87691 : PrimeCertificate 87691 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv37,pv79]) (by decide +kernel)
def pv87691 : PrimeValue := ⟨87691, pr87691⟩
private theorem pr87697 : PrimeCertificate 87697 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv29]) (by decide +kernel)
def pv87697 : PrimeValue := ⟨87697, pr87697⟩
private theorem pr87701 : PrimeCertificate 87701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv877]) (by decide +kernel)
def pv87701 : PrimeValue := ⟨87701, pr87701⟩
private theorem pr87719 : PrimeCertificate 87719 :=
  certifyPrime (q := pv7) (ls := [pv2,pv61,pv719]) (by decide +kernel)
def pv87719 : PrimeValue := ⟨87719, pr87719⟩
private theorem pr87721 : PrimeCertificate 87721 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv17,pv43]) (by decide +kernel)
def pv87721 : PrimeValue := ⟨87721, pr87721⟩
private theorem pr87739 : PrimeCertificate 87739 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv2089]) (by decide +kernel)
def pv87739 : PrimeValue := ⟨87739, pr87739⟩
private theorem pr87743 : PrimeCertificate 87743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv2309]) (by decide +kernel)
def pv87743 : PrimeValue := ⟨87743, pr87743⟩
private theorem pr87767 : PrimeCertificate 87767 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv6269]) (by decide +kernel)
def pv87767 : PrimeValue := ⟨87767, pr87767⟩
private theorem pr87793 : PrimeCertificate 87793 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv59]) (by decide +kernel)
def pv87793 : PrimeValue := ⟨87793, pr87793⟩
private theorem pr87797 : PrimeCertificate 87797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv467]) (by decide +kernel)
def pv87797 : PrimeValue := ⟨87797, pr87797⟩
private theorem pr87803 : PrimeCertificate 87803 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv13,pv307]) (by decide +kernel)
def pv87803 : PrimeValue := ⟨87803, pr87803⟩
private theorem pr87811 : PrimeCertificate 87811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv2927]) (by decide +kernel)
def pv87811 : PrimeValue := ⟨87811, pr87811⟩
private theorem pr87833 : PrimeCertificate 87833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv10979]) (by decide +kernel)
def pv87833 : PrimeValue := ⟨87833, pr87833⟩
private theorem pr87853 : PrimeCertificate 87853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7321]) (by decide +kernel)
def pv87853 : PrimeValue := ⟨87853, pr87853⟩
private theorem pr87869 : PrimeCertificate 87869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv1997]) (by decide +kernel)
def pv87869 : PrimeValue := ⟨87869, pr87869⟩
private theorem pr87877 : PrimeCertificate 87877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv2441]) (by decide +kernel)
def pv87877 : PrimeValue := ⟨87877, pr87877⟩
private theorem pr87881 : PrimeCertificate 87881 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13]) (by decide +kernel)
def pv87881 : PrimeValue := ⟨87881, pr87881⟩
private theorem pr87887 : PrimeCertificate 87887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv43943]) (by decide +kernel)
def pv87887 : PrimeValue := ⟨87887, pr87887⟩
private theorem pr87911 : PrimeCertificate 87911 :=
  certifyPrime (q := pv29) (ls := [pv2,pv5,pv59,pv149]) (by decide +kernel)
def pv87911 : PrimeValue := ⟨87911, pr87911⟩
private theorem pr87917 : PrimeCertificate 87917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv709]) (by decide +kernel)
def pv87917 : PrimeValue := ⟨87917, pr87917⟩
private theorem pr87931 : PrimeCertificate 87931 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv5,pv977]) (by decide +kernel)
def pv87931 : PrimeValue := ⟨87931, pr87931⟩
private theorem pr87943 : PrimeCertificate 87943 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv14657]) (by decide +kernel)
def pv87943 : PrimeValue := ⟨87943, pr87943⟩
private theorem pr87959 : PrimeCertificate 87959 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv17,pv199]) (by decide +kernel)
def pv87959 : PrimeValue := ⟨87959, pr87959⟩
private theorem pr87961 : PrimeCertificate 87961 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv733]) (by decide +kernel)
def pv87961 : PrimeValue := ⟨87961, pr87961⟩
private theorem pr87973 : PrimeCertificate 87973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7331]) (by decide +kernel)
def pv87973 : PrimeValue := ⟨87973, pr87973⟩
private theorem pr87977 : PrimeCertificate 87977 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv1571]) (by decide +kernel)
def pv87977 : PrimeValue := ⟨87977, pr87977⟩
private theorem pr87991 : PrimeCertificate 87991 :=
  certifyPrime (q := pv47) (ls := [pv2,pv3,pv5,pv7,pv419]) (by decide +kernel)
def pv87991 : PrimeValue := ⟨87991, pr87991⟩
private theorem pr88001 : PrimeCertificate 88001 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv11]) (by decide +kernel)
def pv88001 : PrimeValue := ⟨88001, pr88001⟩
private theorem pr88003 : PrimeCertificate 88003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv4889]) (by decide +kernel)
def pv88003 : PrimeValue := ⟨88003, pr88003⟩
private theorem pr88007 : PrimeCertificate 88007 :=
  certifyPrime (q := pv5) (ls := [pv2,pv79,pv557]) (by decide +kernel)
def pv88007 : PrimeValue := ⟨88007, pr88007⟩
private theorem pr88019 : PrimeCertificate 88019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv6287]) (by decide +kernel)
def pv88019 : PrimeValue := ⟨88019, pr88019⟩
private theorem pr88037 : PrimeCertificate 88037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv1693]) (by decide +kernel)
def pv88037 : PrimeValue := ⟨88037, pr88037⟩
private theorem pr88069 : PrimeCertificate 88069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv179]) (by decide +kernel)
def pv88069 : PrimeValue := ⟨88069, pr88069⟩
private theorem pr88079 : PrimeCertificate 88079 :=
  certifyPrime (q := pv31) (ls := [pv2,pv47,pv937]) (by decide +kernel)
def pv88079 : PrimeValue := ⟨88079, pr88079⟩
private theorem pr88093 : PrimeCertificate 88093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv2447]) (by decide +kernel)
def pv88093 : PrimeValue := ⟨88093, pr88093⟩
private theorem pr88117 : PrimeCertificate 88117 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv1049]) (by decide +kernel)
def pv88117 : PrimeValue := ⟨88117, pr88117⟩
private theorem pr88129 : PrimeCertificate 88129 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv17]) (by decide +kernel)
def pv88129 : PrimeValue := ⟨88129, pr88129⟩
private theorem pr88169 : PrimeCertificate 88169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv103,pv107]) (by decide +kernel)
def pv88169 : PrimeValue := ⟨88169, pr88169⟩
private theorem pr88177 : PrimeCertificate 88177 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv167]) (by decide +kernel)
def pv88177 : PrimeValue := ⟨88177, pr88177⟩
private theorem pr88211 : PrimeCertificate 88211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv8821]) (by decide +kernel)
def pv88211 : PrimeValue := ⟨88211, pr88211⟩
private theorem pr88223 : PrimeCertificate 88223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv44111]) (by decide +kernel)
def pv88223 : PrimeValue := ⟨88223, pr88223⟩
private theorem pr88237 : PrimeCertificate 88237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv43]) (by decide +kernel)
def pv88237 : PrimeValue := ⟨88237, pr88237⟩
private theorem pr88241 : PrimeCertificate 88241 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1103]) (by decide +kernel)
def pv88241 : PrimeValue := ⟨88241, pr88241⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
