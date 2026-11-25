/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table075
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table075.pv244021
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table008
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table010
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table017
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table044
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table045

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr244021 : PrimeCertificate 244021 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv83]) (by decide +kernel)
def pv244021 : PrimeValue := ⟨244021, pr244021⟩
private theorem pr244033 : PrimeCertificate 244033 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv41]) (by decide +kernel)
def pv244033 : PrimeValue := ⟨244033, pr244033⟩
private theorem pr244043 : PrimeCertificate 244043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv122021]) (by decide +kernel)
def pv244043 : PrimeValue := ⟨244043, pr244043⟩
private theorem pr244091 : PrimeCertificate 244091 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv7,pv11,pv317]) (by decide +kernel)
def pv244091 : PrimeValue := ⟨244091, pr244091⟩
private theorem pr244121 : PrimeCertificate 244121 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17,pv359]) (by decide +kernel)
def pv244121 : PrimeValue := ⟨244121, pr244121⟩
private theorem pr244159 : PrimeCertificate 244159 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv40693]) (by decide +kernel)
def pv244159 : PrimeValue := ⟨244159, pr244159⟩
private theorem pr244177 : PrimeCertificate 244177 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv5087]) (by decide +kernel)
def pv244177 : PrimeValue := ⟨244177, pr244177⟩
private theorem pr244199 : PrimeCertificate 244199 :=
  certifyPrime (q := pv7) (ls := [pv2,pv122099]) (by decide +kernel)
def pv244199 : PrimeValue := ⟨244199, pr244199⟩
private theorem pr244219 : PrimeCertificate 244219 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13,pv31,pv101]) (by decide +kernel)
def pv244219 : PrimeValue := ⟨244219, pr244219⟩
private theorem pr244247 : PrimeCertificate 244247 :=
  certifyPrime (q := pv5) (ls := [pv2,pv97,pv1259]) (by decide +kernel)
def pv244247 : PrimeValue := ⟨244247, pr244247⟩
private theorem pr244253 : PrimeCertificate 244253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv227,pv269]) (by decide +kernel)
def pv244253 : PrimeValue := ⟨244253, pr244253⟩
private theorem pr244261 : PrimeCertificate 244261 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv23,pv59]) (by decide +kernel)
def pv244261 : PrimeValue := ⟨244261, pr244261⟩
private theorem pr244291 : PrimeCertificate 244291 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv17,pv479]) (by decide +kernel)
def pv244291 : PrimeValue := ⟨244291, pr244291⟩
private theorem pr244297 : PrimeCertificate 244297 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv29]) (by decide +kernel)
def pv244297 : PrimeValue := ⟨244297, pr244297⟩
private theorem pr244301 : PrimeCertificate 244301 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv349]) (by decide +kernel)
def pv244301 : PrimeValue := ⟨244301, pr244301⟩
private theorem pr244303 : PrimeCertificate 244303 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv2143]) (by decide +kernel)
def pv244303 : PrimeValue := ⟨244303, pr244303⟩
private theorem pr244313 : PrimeCertificate 244313 :=
  certifyPrime (q := pv3) (ls := [pv2,pv30539]) (by decide +kernel)
def pv244313 : PrimeValue := ⟨244313, pr244313⟩
private theorem pr244333 : PrimeCertificate 244333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv617]) (by decide +kernel)
def pv244333 : PrimeValue := ⟨244333, pr244333⟩
private theorem pr244339 : PrimeCertificate 244339 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv193,pv211]) (by decide +kernel)
def pv244339 : PrimeValue := ⟨244339, pr244339⟩
private theorem pr244351 : PrimeCertificate 244351 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv181]) (by decide +kernel)
def pv244351 : PrimeValue := ⟨244351, pr244351⟩
private theorem pr244367 : PrimeCertificate 244367 :=
  certifyPrime (q := pv5) (ls := [pv2,pv61,pv2003]) (by decide +kernel)
def pv244367 : PrimeValue := ⟨244367, pr244367⟩
private theorem pr244379 : PrimeCertificate 244379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv59,pv109]) (by decide +kernel)
def pv244379 : PrimeValue := ⟨244379, pr244379⟩
private theorem pr244403 : PrimeCertificate 244403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv122201]) (by decide +kernel)
def pv244403 : PrimeValue := ⟨244403, pr244403⟩
private theorem pr244411 : PrimeCertificate 244411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv8147]) (by decide +kernel)
def pv244411 : PrimeValue := ⟨244411, pr244411⟩
private theorem pr244423 : PrimeCertificate 244423 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv37,pv367]) (by decide +kernel)
def pv244423 : PrimeValue := ⟨244423, pr244423⟩
private theorem pr244429 : PrimeCertificate 244429 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv20369]) (by decide +kernel)
def pv244429 : PrimeValue := ⟨244429, pr244429⟩
private theorem pr244451 : PrimeCertificate 244451 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv4889]) (by decide +kernel)
def pv244451 : PrimeValue := ⟨244451, pr244451⟩
private theorem pr244463 : PrimeCertificate 244463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv122231]) (by decide +kernel)
def pv244463 : PrimeValue := ⟨244463, pr244463⟩
private theorem pr244481 : PrimeCertificate 244481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv191]) (by decide +kernel)
def pv244481 : PrimeValue := ⟨244481, pr244481⟩
private theorem pr244507 : PrimeCertificate 244507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv40751]) (by decide +kernel)
def pv244507 : PrimeValue := ⟨244507, pr244507⟩
private theorem pr244547 : PrimeCertificate 244547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv122273]) (by decide +kernel)
def pv244547 : PrimeValue := ⟨244547, pr244547⟩
private theorem pr244553 : PrimeCertificate 244553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11,pv397]) (by decide +kernel)
def pv244553 : PrimeValue := ⟨244553, pr244553⟩
private theorem pr244561 : PrimeCertificate 244561 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv5,pv1019]) (by decide +kernel)
def pv244561 : PrimeValue := ⟨244561, pr244561⟩
private theorem pr244567 : PrimeCertificate 244567 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv647]) (by decide +kernel)
def pv244567 : PrimeValue := ⟨244567, pr244567⟩
private theorem pr244583 : PrimeCertificate 244583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv23,pv409]) (by decide +kernel)
def pv244583 : PrimeValue := ⟨244583, pr244583⟩
private theorem pr244589 : PrimeCertificate 244589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv1301]) (by decide +kernel)
def pv244589 : PrimeValue := ⟨244589, pr244589⟩
private theorem pr244597 : PrimeCertificate 244597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv17,pv109]) (by decide +kernel)
def pv244597 : PrimeValue := ⟨244597, pr244597⟩
private theorem pr244603 : PrimeCertificate 244603 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv107,pv127]) (by decide +kernel)
def pv244603 : PrimeValue := ⟨244603, pr244603⟩
private theorem pr244619 : PrimeCertificate 244619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv11119]) (by decide +kernel)
def pv244619 : PrimeValue := ⟨244619, pr244619⟩
private theorem pr244633 : PrimeCertificate 244633 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv10193]) (by decide +kernel)
def pv244633 : PrimeValue := ⟨244633, pr244633⟩
private theorem pr244637 : PrimeCertificate 244637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv8737]) (by decide +kernel)
def pv244637 : PrimeValue := ⟨244637, pr244637⟩
private theorem pr244687 : PrimeCertificate 244687 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv3137]) (by decide +kernel)
def pv244687 : PrimeValue := ⟨244687, pr244687⟩
private theorem pr244691 : PrimeCertificate 244691 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv24469]) (by decide +kernel)
def pv244691 : PrimeValue := ⟨244691, pr244691⟩
private theorem pr244703 : PrimeCertificate 244703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv29,pv4219]) (by decide +kernel)
def pv244703 : PrimeValue := ⟨244703, pr244703⟩
private theorem pr244711 : PrimeCertificate 244711 :=
  certifyPrime (q := pv61) (ls := [pv2,pv3,pv5,pv2719]) (by decide +kernel)
def pv244711 : PrimeValue := ⟨244711, pr244711⟩
private theorem pr244733 : PrimeCertificate 244733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv59,pv61]) (by decide +kernel)
def pv244733 : PrimeValue := ⟨244733, pr244733⟩
private theorem pr244753 : PrimeCertificate 244753 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5099]) (by decide +kernel)
def pv244753 : PrimeValue := ⟨244753, pr244753⟩
private theorem pr244759 : PrimeCertificate 244759 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv19,pv113]) (by decide +kernel)
def pv244759 : PrimeValue := ⟨244759, pr244759⟩
private theorem pr244781 : PrimeCertificate 244781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv12239]) (by decide +kernel)
def pv244781 : PrimeValue := ⟨244781, pr244781⟩
private theorem pr244787 : PrimeCertificate 244787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv122393]) (by decide +kernel)
def pv244787 : PrimeValue := ⟨244787, pr244787⟩
private theorem pr244813 : PrimeCertificate 244813 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv887]) (by decide +kernel)
def pv244813 : PrimeValue := ⟨244813, pr244813⟩
private theorem pr244841 : PrimeCertificate 244841 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv6121]) (by decide +kernel)
def pv244841 : PrimeValue := ⟨244841, pr244841⟩
private theorem pr244843 : PrimeCertificate 244843 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv43,pv73]) (by decide +kernel)
def pv244843 : PrimeValue := ⟨244843, pr244843⟩
private theorem pr244859 : PrimeCertificate 244859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv5323]) (by decide +kernel)
def pv244859 : PrimeValue := ⟨244859, pr244859⟩
private theorem pr244861 : PrimeCertificate 244861 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv7,pv11,pv53]) (by decide +kernel)
def pv244861 : PrimeValue := ⟨244861, pr244861⟩
private theorem pr244873 : PrimeCertificate 244873 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv19,pv179]) (by decide +kernel)
def pv244873 : PrimeValue := ⟨244873, pr244873⟩
private theorem pr244877 : PrimeCertificate 244877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv2111]) (by decide +kernel)
def pv244877 : PrimeValue := ⟨244877, pr244877⟩
private theorem pr244889 : PrimeCertificate 244889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv4373]) (by decide +kernel)
def pv244889 : PrimeValue := ⟨244889, pr244889⟩
private theorem pr244901 : PrimeCertificate 244901 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv31,pv79]) (by decide +kernel)
def pv244901 : PrimeValue := ⟨244901, pr244901⟩
private theorem pr244939 : PrimeCertificate 244939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv40823]) (by decide +kernel)
def pv244939 : PrimeValue := ⟨244939, pr244939⟩
private theorem pr244943 : PrimeCertificate 244943 :=
  certifyPrime (q := pv5) (ls := [pv2,pv122471]) (by decide +kernel)
def pv244943 : PrimeValue := ⟨244943, pr244943⟩
private theorem pr244997 : PrimeCertificate 244997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv2663]) (by decide +kernel)
def pv244997 : PrimeValue := ⟨244997, pr244997⟩
private theorem pr245023 : PrimeCertificate 245023 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv97,pv421]) (by decide +kernel)
def pv245023 : PrimeValue := ⟨245023, pr245023⟩
private theorem pr245029 : PrimeCertificate 245029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv2917]) (by decide +kernel)
def pv245029 : PrimeValue := ⟨245029, pr245029⟩
private theorem pr245033 : PrimeCertificate 245033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv109,pv281]) (by decide +kernel)
def pv245033 : PrimeValue := ⟨245033, pr245033⟩
private theorem pr245039 : PrimeCertificate 245039 :=
  certifyPrime (q := pv7) (ls := [pv2,pv17,pv7207]) (by decide +kernel)
def pv245039 : PrimeValue := ⟨245039, pr245039⟩
private theorem pr245071 : PrimeCertificate 245071 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv389]) (by decide +kernel)
def pv245071 : PrimeValue := ⟨245071, pr245071⟩
private theorem pr245083 : PrimeCertificate 245083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv40847]) (by decide +kernel)
def pv245083 : PrimeValue := ⟨245083, pr245083⟩
private theorem pr245087 : PrimeCertificate 245087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv31,pv59,pv67]) (by decide +kernel)
def pv245087 : PrimeValue := ⟨245087, pr245087⟩
private theorem pr245129 : PrimeCertificate 245129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv2357]) (by decide +kernel)
def pv245129 : PrimeValue := ⟨245129, pr245129⟩
private theorem pr245131 : PrimeCertificate 245131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv8171]) (by decide +kernel)
def pv245131 : PrimeValue := ⟨245131, pr245131⟩
private theorem pr245183 : PrimeCertificate 245183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv83,pv211]) (by decide +kernel)
def pv245183 : PrimeValue := ⟨245183, pr245183⟩
private theorem pr245257 : PrimeCertificate 245257 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv929]) (by decide +kernel)
def pv245257 : PrimeValue := ⟨245257, pr245257⟩
private theorem pr245261 : PrimeCertificate 245261 :=
  certifyPrime (q := pv29) (ls := [pv2,pv5,pv12263]) (by decide +kernel)
def pv245261 : PrimeValue := ⟨245261, pr245261⟩
private theorem pr245269 : PrimeCertificate 245269 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv757]) (by decide +kernel)
def pv245269 : PrimeValue := ⟨245269, pr245269⟩
private theorem pr245279 : PrimeCertificate 245279 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv11149]) (by decide +kernel)
def pv245279 : PrimeValue := ⟨245279, pr245279⟩
private theorem pr245317 : PrimeCertificate 245317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv20443]) (by decide +kernel)
def pv245317 : PrimeValue := ⟨245317, pr245317⟩
private theorem pr245321 : PrimeCertificate 245321 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv6133]) (by decide +kernel)
def pv245321 : PrimeValue := ⟨245321, pr245321⟩
private theorem pr245411 : PrimeCertificate 245411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv23,pv97]) (by decide +kernel)
def pv245411 : PrimeValue := ⟨245411, pr245411⟩
private theorem pr245437 : PrimeCertificate 245437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv113,pv181]) (by decide +kernel)
def pv245437 : PrimeValue := ⟨245437, pr245437⟩
private theorem pr245471 : PrimeCertificate 245471 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv24547]) (by decide +kernel)
def pv245471 : PrimeValue := ⟨245471, pr245471⟩
private theorem pr245473 : PrimeCertificate 245473 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2557]) (by decide +kernel)
def pv245473 : PrimeValue := ⟨245473, pr245473⟩
private theorem pr245501 : PrimeCertificate 245501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv491]) (by decide +kernel)
def pv245501 : PrimeValue := ⟨245501, pr245501⟩
private theorem pr245513 : PrimeCertificate 245513 :=
  certifyPrime (q := pv3) (ls := [pv2,pv30689]) (by decide +kernel)
def pv245513 : PrimeValue := ⟨245513, pr245513⟩
private theorem pr245519 : PrimeCertificate 245519 :=
  certifyPrime (q := pv17) (ls := [pv2,pv7,pv13,pv19,pv71]) (by decide +kernel)
def pv245519 : PrimeValue := ⟨245519, pr245519⟩
private theorem pr245533 : PrimeCertificate 245533 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv37,pv79]) (by decide +kernel)
def pv245533 : PrimeValue := ⟨245533, pr245533⟩
private theorem pr245563 : PrimeCertificate 245563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv40927]) (by decide +kernel)
def pv245563 : PrimeValue := ⟨245563, pr245563⟩
private theorem pr245593 : PrimeCertificate 245593 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv379]) (by decide +kernel)
def pv245593 : PrimeValue := ⟨245593, pr245593⟩
private theorem pr245621 : PrimeCertificate 245621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv12281]) (by decide +kernel)
def pv245621 : PrimeValue := ⟨245621, pr245621⟩
private theorem pr245627 : PrimeCertificate 245627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv191,pv643]) (by decide +kernel)
def pv245627 : PrimeValue := ⟨245627, pr245627⟩
private theorem pr245639 : PrimeCertificate 245639 :=
  certifyPrime (q := pv7) (ls := [pv2,pv122819]) (by decide +kernel)
def pv245639 : PrimeValue := ⟨245639, pr245639⟩
private theorem pr245653 : PrimeCertificate 245653 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv11,pv1861]) (by decide +kernel)
def pv245653 : PrimeValue := ⟨245653, pr245653⟩
private theorem pr245671 : PrimeCertificate 245671 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv19,pv431]) (by decide +kernel)
def pv245671 : PrimeValue := ⟨245671, pr245671⟩
private theorem pr245681 : PrimeCertificate 245681 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv37,pv83]) (by decide +kernel)
def pv245681 : PrimeValue := ⟨245681, pr245681⟩
private theorem pr245711 : PrimeCertificate 245711 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv24571]) (by decide +kernel)
def pv245711 : PrimeValue := ⟨245711, pr245711⟩
private theorem pr245723 : PrimeCertificate 245723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv122861]) (by decide +kernel)
def pv245723 : PrimeValue := ⟨245723, pr245723⟩
private theorem pr245741 : PrimeCertificate 245741 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv1117]) (by decide +kernel)
def pv245741 : PrimeValue := ⟨245741, pr245741⟩
private theorem pr245753 : PrimeCertificate 245753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv17,pv139]) (by decide +kernel)
def pv245753 : PrimeValue := ⟨245753, pr245753⟩
private theorem pr245759 : PrimeCertificate 245759 :=
  certifyPrime (q := pv13) (ls := [pv2,pv103,pv1193]) (by decide +kernel)
def pv245759 : PrimeValue := ⟨245759, pr245759⟩
private theorem pr245789 : PrimeCertificate 245789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv1429]) (by decide +kernel)
def pv245789 : PrimeValue := ⟨245789, pr245789⟩
private theorem pr245849 : PrimeCertificate 245849 :=
  certifyPrime (q := pv3) (ls := [pv2,pv79,pv389]) (by decide +kernel)
def pv245849 : PrimeValue := ⟨245849, pr245849⟩
private theorem pr245899 : PrimeCertificate 245899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv719]) (by decide +kernel)
def pv245899 : PrimeValue := ⟨245899, pr245899⟩
private theorem pr245909 : PrimeCertificate 245909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv4729]) (by decide +kernel)
def pv245909 : PrimeValue := ⟨245909, pr245909⟩
private theorem pr245941 : PrimeCertificate 245941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv4099]) (by decide +kernel)
def pv245941 : PrimeValue := ⟨245941, pr245941⟩
private theorem pr245983 : PrimeCertificate 245983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv3727]) (by decide +kernel)
def pv245983 : PrimeValue := ⟨245983, pr245983⟩
private theorem pr246011 : PrimeCertificate 246011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv73,pv337]) (by decide +kernel)
def pv246011 : PrimeValue := ⟨246011, pr246011⟩
private theorem pr246017 : PrimeCertificate 246017 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31]) (by decide +kernel)
def pv246017 : PrimeValue := ⟨246017, pr246017⟩
private theorem pr246119 : PrimeCertificate 246119 :=
  certifyPrime (q := pv11) (ls := [pv2,pv123059]) (by decide +kernel)
def pv246119 : PrimeValue := ⟨246119, pr246119⟩
private theorem pr246131 : PrimeCertificate 246131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv151,pv163]) (by decide +kernel)
def pv246131 : PrimeValue := ⟨246131, pr246131⟩
private theorem pr246133 : PrimeCertificate 246133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv53]) (by decide +kernel)
def pv246133 : PrimeValue := ⟨246133, pr246133⟩
private theorem pr246173 : PrimeCertificate 246173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61543]) (by decide +kernel)
def pv246173 : PrimeValue := ⟨246173, pr246173⟩
private theorem pr246187 : PrimeCertificate 246187 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv97]) (by decide +kernel)
def pv246187 : PrimeValue := ⟨246187, pr246187⟩
private theorem pr246193 : PrimeCertificate 246193 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv223]) (by decide +kernel)
def pv246193 : PrimeValue := ⟨246193, pr246193⟩
private theorem pr246203 : PrimeCertificate 246203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv19,pv31]) (by decide +kernel)
def pv246203 : PrimeValue := ⟨246203, pr246203⟩
private theorem pr246209 : PrimeCertificate 246209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3847]) (by decide +kernel)
def pv246209 : PrimeValue := ⟨246209, pr246209⟩
private theorem pr246217 : PrimeCertificate 246217 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv10259]) (by decide +kernel)
def pv246217 : PrimeValue := ⟨246217, pr246217⟩
private theorem pr246223 : PrimeCertificate 246223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13679]) (by decide +kernel)
def pv246223 : PrimeValue := ⟨246223, pr246223⟩
private theorem pr246241 : PrimeCertificate 246241 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv246241 : PrimeValue := ⟨246241, pr246241⟩
private theorem pr246251 : PrimeCertificate 246251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv197]) (by decide +kernel)
def pv246251 : PrimeValue := ⟨246251, pr246251⟩
private theorem pr246271 : PrimeCertificate 246271 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv8209]) (by decide +kernel)
def pv246271 : PrimeValue := ⟨246271, pr246271⟩
private theorem pr246277 : PrimeCertificate 246277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv6841]) (by decide +kernel)
def pv246277 : PrimeValue := ⟨246277, pr246277⟩
private theorem pr246289 : PrimeCertificate 246289 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv733]) (by decide +kernel)
def pv246289 : PrimeValue := ⟨246289, pr246289⟩
private theorem pr246317 : PrimeCertificate 246317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv19,pv463]) (by decide +kernel)
def pv246317 : PrimeValue := ⟨246317, pr246317⟩
private theorem pr246319 : PrimeCertificate 246319 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv61,pv673]) (by decide +kernel)
def pv246319 : PrimeValue := ⟨246319, pr246319⟩
private theorem pr246329 : PrimeCertificate 246329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41,pv751]) (by decide +kernel)
def pv246329 : PrimeValue := ⟨246329, pr246329⟩
private theorem pr246391 : PrimeCertificate 246391 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv43,pv191]) (by decide +kernel)
def pv246391 : PrimeValue := ⟨246391, pr246391⟩
private theorem pr246403 : PrimeCertificate 246403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv246403 : PrimeValue := ⟨246403, pr246403⟩
private theorem pr246469 : PrimeCertificate 246469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv23,pv47]) (by decide +kernel)
def pv246469 : PrimeValue := ⟨246469, pr246469⟩
private theorem pr246473 : PrimeCertificate 246473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv30809]) (by decide +kernel)
def pv246473 : PrimeValue := ⟨246473, pr246473⟩
private theorem pr246497 : PrimeCertificate 246497 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7703]) (by decide +kernel)
def pv246497 : PrimeValue := ⟨246497, pr246497⟩
private theorem pr246523 : PrimeCertificate 246523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv181,pv227]) (by decide +kernel)
def pv246523 : PrimeValue := ⟨246523, pr246523⟩
private theorem pr246527 : PrimeCertificate 246527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv17609]) (by decide +kernel)
def pv246527 : PrimeValue := ⟨246527, pr246527⟩
private theorem pr246557 : PrimeCertificate 246557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv1163]) (by decide +kernel)
def pv246557 : PrimeValue := ⟨246557, pr246557⟩
private theorem pr246569 : PrimeCertificate 246569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv17,pv37]) (by decide +kernel)
def pv246569 : PrimeValue := ⟨246569, pr246569⟩
private theorem pr246599 : PrimeCertificate 246599 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv1019]) (by decide +kernel)
def pv246599 : PrimeValue := ⟨246599, pr246599⟩
private theorem pr246607 : PrimeCertificate 246607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv1787]) (by decide +kernel)
def pv246607 : PrimeValue := ⟨246607, pr246607⟩
private theorem pr246611 : PrimeCertificate 246611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv13,pv271]) (by decide +kernel)
def pv246611 : PrimeValue := ⟨246611, pr246611⟩
private theorem pr246613 : PrimeCertificate 246613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv20551]) (by decide +kernel)
def pv246613 : PrimeValue := ⟨246613, pr246613⟩
private theorem pr246637 : PrimeCertificate 246637 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv17,pv31]) (by decide +kernel)
def pv246637 : PrimeValue := ⟨246637, pr246637⟩
private theorem pr246641 : PrimeCertificate 246641 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv3083]) (by decide +kernel)
def pv246641 : PrimeValue := ⟨246641, pr246641⟩
private theorem pr246643 : PrimeCertificate 246643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv37,pv101]) (by decide +kernel)
def pv246643 : PrimeValue := ⟨246643, pr246643⟩
private theorem pr246683 : PrimeCertificate 246683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv123341]) (by decide +kernel)
def pv246683 : PrimeValue := ⟨246683, pr246683⟩
private theorem pr246689 : PrimeCertificate 246689 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv593]) (by decide +kernel)
def pv246689 : PrimeValue := ⟨246689, pr246689⟩
private theorem pr246707 : PrimeCertificate 246707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv293,pv421]) (by decide +kernel)
def pv246707 : PrimeValue := ⟨246707, pr246707⟩
private theorem pr246709 : PrimeCertificate 246709 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv11,pv89]) (by decide +kernel)
def pv246709 : PrimeValue := ⟨246709, pr246709⟩
private theorem pr246713 : PrimeCertificate 246713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv30839]) (by decide +kernel)
def pv246713 : PrimeValue := ⟨246713, pr246713⟩
private theorem pr246731 : PrimeCertificate 246731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv2243]) (by decide +kernel)
def pv246731 : PrimeValue := ⟨246731, pr246731⟩
private theorem pr246739 : PrimeCertificate 246739 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv17,pv41,pv59]) (by decide +kernel)
def pv246739 : PrimeValue := ⟨246739, pr246739⟩
private theorem pr246769 : PrimeCertificate 246769 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv53,pv97]) (by decide +kernel)
def pv246769 : PrimeValue := ⟨246769, pr246769⟩
private theorem pr246781 : PrimeCertificate 246781 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv457]) (by decide +kernel)
def pv246781 : PrimeValue := ⟨246781, pr246781⟩
private theorem pr246793 : PrimeCertificate 246793 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv7,pv13,pv113]) (by decide +kernel)
def pv246793 : PrimeValue := ⟨246793, pr246793⟩
private theorem pr246803 : PrimeCertificate 246803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv123401]) (by decide +kernel)
def pv246803 : PrimeValue := ⟨246803, pr246803⟩
private theorem pr246817 : PrimeCertificate 246817 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv857]) (by decide +kernel)
def pv246817 : PrimeValue := ⟨246817, pr246817⟩
private theorem pr246833 : PrimeCertificate 246833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv15427]) (by decide +kernel)
def pv246833 : PrimeValue := ⟨246833, pr246833⟩
private theorem pr246923 : PrimeCertificate 246923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv9497]) (by decide +kernel)
def pv246923 : PrimeValue := ⟨246923, pr246923⟩
private theorem pr246929 : PrimeCertificate 246929 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv23,pv61]) (by decide +kernel)
def pv246929 : PrimeValue := ⟨246929, pr246929⟩
private theorem pr246941 : PrimeCertificate 246941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv12347]) (by decide +kernel)
def pv246941 : PrimeValue := ⟨246941, pr246941⟩
private theorem pr247001 : PrimeCertificate 247001 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv19]) (by decide +kernel)
def pv247001 : PrimeValue := ⟨247001, pr247001⟩
private theorem pr247007 : PrimeCertificate 247007 :=
  certifyPrime (q := pv5) (ls := [pv2,pv123503]) (by decide +kernel)
def pv247007 : PrimeValue := ⟨247007, pr247007⟩
private theorem pr247067 : PrimeCertificate 247067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv41,pv131]) (by decide +kernel)
def pv247067 : PrimeValue := ⟨247067, pr247067⟩
private theorem pr247069 : PrimeCertificate 247069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv6863]) (by decide +kernel)
def pv247069 : PrimeValue := ⟨247069, pr247069⟩
private theorem pr247073 : PrimeCertificate 247073 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv1103]) (by decide +kernel)
def pv247073 : PrimeValue := ⟨247073, pr247073⟩
private theorem pr247099 : PrimeCertificate 247099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41183]) (by decide +kernel)
def pv247099 : PrimeValue := ⟨247099, pr247099⟩
private theorem pr247141 : PrimeCertificate 247141 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv1373]) (by decide +kernel)
def pv247141 : PrimeValue := ⟨247141, pr247141⟩
private theorem pr247183 : PrimeCertificate 247183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv3169]) (by decide +kernel)
def pv247183 : PrimeValue := ⟨247183, pr247183⟩
private theorem pr247193 : PrimeCertificate 247193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv53]) (by decide +kernel)
def pv247193 : PrimeValue := ⟨247193, pr247193⟩
private theorem pr247223 : PrimeCertificate 247223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv71,pv1741]) (by decide +kernel)
def pv247223 : PrimeValue := ⟨247223, pr247223⟩
private theorem pr247229 : PrimeCertificate 247229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv3253]) (by decide +kernel)
def pv247229 : PrimeValue := ⟨247229, pr247229⟩
private theorem pr247241 : PrimeCertificate 247241 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv883]) (by decide +kernel)
def pv247241 : PrimeValue := ⟨247241, pr247241⟩
private theorem pr247259 : PrimeCertificate 247259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv11239]) (by decide +kernel)
def pv247259 : PrimeValue := ⟨247259, pr247259⟩
private theorem pr247279 : PrimeCertificate 247279 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv41213]) (by decide +kernel)
def pv247279 : PrimeValue := ⟨247279, pr247279⟩
private theorem pr247309 : PrimeCertificate 247309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv557]) (by decide +kernel)
def pv247309 : PrimeValue := ⟨247309, pr247309⟩
private theorem pr247337 : PrimeCertificate 247337 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43,pv719]) (by decide +kernel)
def pv247337 : PrimeValue := ⟨247337, pr247337⟩
private theorem pr247339 : PrimeCertificate 247339 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv151]) (by decide +kernel)
def pv247339 : PrimeValue := ⟨247339, pr247339⟩
private theorem pr247343 : PrimeCertificate 247343 :=
  certifyPrime (q := pv13) (ls := [pv2,pv19,pv23,pv283]) (by decide +kernel)
def pv247343 : PrimeValue := ⟨247343, pr247343⟩
private theorem pr247363 : PrimeCertificate 247363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41227]) (by decide +kernel)
def pv247363 : PrimeValue := ⟨247363, pr247363⟩
private theorem pr247369 : PrimeCertificate 247369 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv937]) (by decide +kernel)
def pv247369 : PrimeValue := ⟨247369, pr247369⟩
private theorem pr247381 : PrimeCertificate 247381 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv5,pv7,pv19,pv31]) (by decide +kernel)
def pv247381 : PrimeValue := ⟨247381, pr247381⟩
private theorem pr247391 : PrimeCertificate 247391 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv13,pv173]) (by decide +kernel)
def pv247391 : PrimeValue := ⟨247391, pr247391⟩
private theorem pr247393 : PrimeCertificate 247393 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv859]) (by decide +kernel)
def pv247393 : PrimeValue := ⟨247393, pr247393⟩
private theorem pr247409 : PrimeCertificate 247409 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv47]) (by decide +kernel)
def pv247409 : PrimeValue := ⟨247409, pr247409⟩
private theorem pr247421 : PrimeCertificate 247421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv89,pv139]) (by decide +kernel)
def pv247421 : PrimeValue := ⟨247421, pr247421⟩
private theorem pr247451 : PrimeCertificate 247451 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv101]) (by decide +kernel)
def pv247451 : PrimeValue := ⟨247451, pr247451⟩
private theorem pr247463 : PrimeCertificate 247463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv123731]) (by decide +kernel)
def pv247463 : PrimeValue := ⟨247463, pr247463⟩
private theorem pr247519 : PrimeCertificate 247519 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13751]) (by decide +kernel)
def pv247519 : PrimeValue := ⟨247519, pr247519⟩
private theorem pr247529 : PrimeCertificate 247529 :=
  certifyPrime (q := pv3) (ls := [pv2,pv30941]) (by decide +kernel)
def pv247529 : PrimeValue := ⟨247529, pr247529⟩
private theorem pr247547 : PrimeCertificate 247547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv9521]) (by decide +kernel)
def pv247547 : PrimeValue := ⟨247547, pr247547⟩
private theorem pr247553 : PrimeCertificate 247553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv967]) (by decide +kernel)
def pv247553 : PrimeValue := ⟨247553, pr247553⟩
private theorem pr247579 : PrimeCertificate 247579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41263]) (by decide +kernel)
def pv247579 : PrimeValue := ⟨247579, pr247579⟩
private theorem pr247591 : PrimeCertificate 247591 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv131]) (by decide +kernel)
def pv247591 : PrimeValue := ⟨247591, pr247591⟩
private theorem pr247601 : PrimeCertificate 247601 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv619]) (by decide +kernel)
def pv247601 : PrimeValue := ⟨247601, pr247601⟩
private theorem pr247603 : PrimeCertificate 247603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv1423]) (by decide +kernel)
def pv247603 : PrimeValue := ⟨247603, pr247603⟩
private theorem pr247607 : PrimeCertificate 247607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv123803]) (by decide +kernel)
def pv247607 : PrimeValue := ⟨247607, pr247607⟩
private theorem pr247613 : PrimeCertificate 247613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv103,pv601]) (by decide +kernel)
def pv247613 : PrimeValue := ⟨247613, pr247613⟩
private theorem pr247633 : PrimeCertificate 247633 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv67]) (by decide +kernel)
def pv247633 : PrimeValue := ⟨247633, pr247633⟩
private theorem pr247651 : PrimeCertificate 247651 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv127]) (by decide +kernel)
def pv247651 : PrimeValue := ⟨247651, pr247651⟩
private theorem pr247697 : PrimeCertificate 247697 :=
  certifyPrime (q := pv3) (ls := [pv2,pv113,pv137]) (by decide +kernel)
def pv247697 : PrimeValue := ⟨247697, pr247697⟩
private theorem pr247711 : PrimeCertificate 247711 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv23,pv359]) (by decide +kernel)
def pv247711 : PrimeValue := ⟨247711, pr247711⟩
private theorem pr247717 : PrimeCertificate 247717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv983]) (by decide +kernel)
def pv247717 : PrimeValue := ⟨247717, pr247717⟩
private theorem pr247729 : PrimeCertificate 247729 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13,pv397]) (by decide +kernel)
def pv247729 : PrimeValue := ⟨247729, pr247729⟩
private theorem pr247759 : PrimeCertificate 247759 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv7,pv17,pv347]) (by decide +kernel)
def pv247759 : PrimeValue := ⟨247759, pr247759⟩
private theorem pr247769 : PrimeCertificate 247769 :=
  certifyPrime (q := pv3) (ls := [pv2,pv30971]) (by decide +kernel)
def pv247769 : PrimeValue := ⟨247769, pr247769⟩
private theorem pr247781 : PrimeCertificate 247781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv953]) (by decide +kernel)
def pv247781 : PrimeValue := ⟨247781, pr247781⟩
private theorem pr247811 : PrimeCertificate 247811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv24781]) (by decide +kernel)
def pv247811 : PrimeValue := ⟨247811, pr247811⟩
private theorem pr247829 : PrimeCertificate 247829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv53,pv167]) (by decide +kernel)
def pv247829 : PrimeValue := ⟨247829, pr247829⟩
private theorem pr247847 : PrimeCertificate 247847 :=
  certifyPrime (q := pv5) (ls := [pv2,pv123923]) (by decide +kernel)
def pv247847 : PrimeValue := ⟨247847, pr247847⟩
private theorem pr247853 : PrimeCertificate 247853 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv43,pv131]) (by decide +kernel)
def pv247853 : PrimeValue := ⟨247853, pr247853⟩
private theorem pr247873 : PrimeCertificate 247873 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1291]) (by decide +kernel)
def pv247873 : PrimeValue := ⟨247873, pr247873⟩
private theorem pr247889 : PrimeCertificate 247889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv15493]) (by decide +kernel)
def pv247889 : PrimeValue := ⟨247889, pr247889⟩
private theorem pr247913 : PrimeCertificate 247913 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv19,pv233]) (by decide +kernel)
def pv247913 : PrimeValue := ⟨247913, pr247913⟩
private theorem pr247943 : PrimeCertificate 247943 :=
  certifyPrime (q := pv5) (ls := [pv2,pv151,pv821]) (by decide +kernel)
def pv247943 : PrimeValue := ⟨247943, pr247943⟩
private theorem pr247957 : PrimeCertificate 247957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv20663]) (by decide +kernel)
def pv247957 : PrimeValue := ⟨247957, pr247957⟩
private theorem pr247991 : PrimeCertificate 247991 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv24799]) (by decide +kernel)
def pv247991 : PrimeValue := ⟨247991, pr247991⟩
private theorem pr247993 : PrimeCertificate 247993 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv10333]) (by decide +kernel)
def pv247993 : PrimeValue := ⟨247993, pr247993⟩
private theorem pr247997 : PrimeCertificate 247997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv17,pv521]) (by decide +kernel)
def pv247997 : PrimeValue := ⟨247997, pr247997⟩
private theorem pr247999 : PrimeCertificate 247999 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41333]) (by decide +kernel)
def pv247999 : PrimeValue := ⟨247999, pr247999⟩
private theorem pr248021 : PrimeCertificate 248021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv12401]) (by decide +kernel)
def pv248021 : PrimeValue := ⟨248021, pr248021⟩
private theorem pr248033 : PrimeCertificate 248033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv337]) (by decide +kernel)
def pv248033 : PrimeValue := ⟨248033, pr248033⟩
private theorem pr248041 : PrimeCertificate 248041 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv13,pv53]) (by decide +kernel)
def pv248041 : PrimeValue := ⟨248041, pr248041⟩
private theorem pr248057 : PrimeCertificate 248057 :=
  certifyPrime (q := pv3) (ls := [pv2,pv101,pv307]) (by decide +kernel)
def pv248057 : PrimeValue := ⟨248057, pr248057⟩
private theorem pr248063 : PrimeCertificate 248063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv31,pv4001]) (by decide +kernel)
def pv248063 : PrimeValue := ⟨248063, pr248063⟩
private theorem pr248071 : PrimeCertificate 248071 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv8269]) (by decide +kernel)
def pv248071 : PrimeValue := ⟨248071, pr248071⟩
private theorem pr248077 : PrimeCertificate 248077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv2297]) (by decide +kernel)
def pv248077 : PrimeValue := ⟨248077, pr248077⟩
private theorem pr248089 : PrimeCertificate 248089 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv10337]) (by decide +kernel)
def pv248089 : PrimeValue := ⟨248089, pr248089⟩
private theorem pr248099 : PrimeCertificate 248099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv7297]) (by decide +kernel)
def pv248099 : PrimeValue := ⟨248099, pr248099⟩
private theorem pr248137 : PrimeCertificate 248137 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv211]) (by decide +kernel)
def pv248137 : PrimeValue := ⟨248137, pr248137⟩
private theorem pr248141 : PrimeCertificate 248141 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv19,pv653]) (by decide +kernel)
def pv248141 : PrimeValue := ⟨248141, pr248141⟩
private theorem pr248161 : PrimeCertificate 248161 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv11,pv47]) (by decide +kernel)
def pv248161 : PrimeValue := ⟨248161, pr248161⟩
private theorem pr248167 : PrimeCertificate 248167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv811]) (by decide +kernel)
def pv248167 : PrimeValue := ⟨248167, pr248167⟩
private theorem pr248177 : PrimeCertificate 248177 :=
  certifyPrime (q := pv3) (ls := [pv2,pv15511]) (by decide +kernel)
def pv248177 : PrimeValue := ⟨248177, pr248177⟩
private theorem pr248189 : PrimeCertificate 248189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv62047]) (by decide +kernel)
def pv248189 : PrimeValue := ⟨248189, pr248189⟩
private theorem pr248201 : PrimeCertificate 248201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17,pv73]) (by decide +kernel)
def pv248201 : PrimeValue := ⟨248201, pr248201⟩
private theorem pr248231 : PrimeCertificate 248231 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv103,pv241]) (by decide +kernel)
def pv248231 : PrimeValue := ⟨248231, pr248231⟩
private theorem pr248243 : PrimeCertificate 248243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv124121]) (by decide +kernel)
def pv248243 : PrimeValue := ⟨248243, pr248243⟩
private theorem pr248267 : PrimeCertificate 248267 :=
  certifyPrime (q := pv2) (ls := [pv2,pv124133]) (by decide +kernel)
def pv248267 : PrimeValue := ⟨248267, pr248267⟩
private theorem pr248291 : PrimeCertificate 248291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv3547]) (by decide +kernel)
def pv248291 : PrimeValue := ⟨248291, pr248291⟩
private theorem pr248299 : PrimeCertificate 248299 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv1427]) (by decide +kernel)
def pv248299 : PrimeValue := ⟨248299, pr248299⟩
private theorem pr248309 : PrimeCertificate 248309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv2699]) (by decide +kernel)
def pv248309 : PrimeValue := ⟨248309, pr248309⟩
private theorem pr248317 : PrimeCertificate 248317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv20693]) (by decide +kernel)
def pv248317 : PrimeValue := ⟨248317, pr248317⟩
private theorem pr248323 : PrimeCertificate 248323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41387]) (by decide +kernel)
def pv248323 : PrimeValue := ⟨248323, pr248323⟩
private theorem pr248351 : PrimeCertificate 248351 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv4967]) (by decide +kernel)
def pv248351 : PrimeValue := ⟨248351, pr248351⟩
private theorem pr248357 : PrimeCertificate 248357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv2141]) (by decide +kernel)
def pv248357 : PrimeValue := ⟨248357, pr248357⟩
private theorem pr248371 : PrimeCertificate 248371 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv17,pv487]) (by decide +kernel)
def pv248371 : PrimeValue := ⟨248371, pr248371⟩
private theorem pr248389 : PrimeCertificate 248389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv2957]) (by decide +kernel)
def pv248389 : PrimeValue := ⟨248389, pr248389⟩
private theorem pr248401 : PrimeCertificate 248401 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv23]) (by decide +kernel)
def pv248401 : PrimeValue := ⟨248401, pr248401⟩
private theorem pr248407 : PrimeCertificate 248407 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv2179]) (by decide +kernel)
def pv248407 : PrimeValue := ⟨248407, pr248407⟩
private theorem pr248431 : PrimeCertificate 248431 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv13]) (by decide +kernel)
def pv248431 : PrimeValue := ⟨248431, pr248431⟩
private theorem pr248441 : PrimeCertificate 248441 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv6211]) (by decide +kernel)
def pv248441 : PrimeValue := ⟨248441, pr248441⟩
private theorem pr248447 : PrimeCertificate 248447 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv23,pv491]) (by decide +kernel)
def pv248447 : PrimeValue := ⟨248447, pr248447⟩
private theorem pr248461 : PrimeCertificate 248461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv41,pv101]) (by decide +kernel)
def pv248461 : PrimeValue := ⟨248461, pr248461⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
