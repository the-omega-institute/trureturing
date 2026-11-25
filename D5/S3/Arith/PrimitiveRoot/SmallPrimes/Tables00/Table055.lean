/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table055
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table055.pv157291
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table007
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table011
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table030
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table031

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr157291 : PrimeCertificate 157291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv107]) (by decide +kernel)
def pv157291 : PrimeValue := ⟨157291, pr157291⟩
private theorem pr157303 : PrimeCertificate 157303 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv971]) (by decide +kernel)
def pv157303 : PrimeValue := ⟨157303, pr157303⟩
private theorem pr157307 : PrimeCertificate 157307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv78653]) (by decide +kernel)
def pv157307 : PrimeValue := ⟨157307, pr157307⟩
private theorem pr157327 : PrimeCertificate 157327 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv2017]) (by decide +kernel)
def pv157327 : PrimeValue := ⟨157327, pr157327⟩
private theorem pr157349 : PrimeCertificate 157349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv139,pv283]) (by decide +kernel)
def pv157349 : PrimeValue := ⟨157349, pr157349⟩
private theorem pr157351 : PrimeCertificate 157351 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv5,pv1049]) (by decide +kernel)
def pv157351 : PrimeValue := ⟨157351, pr157351⟩
private theorem pr157363 : PrimeCertificate 157363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv26227]) (by decide +kernel)
def pv157363 : PrimeValue := ⟨157363, pr157363⟩
private theorem pr157393 : PrimeCertificate 157393 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1093]) (by decide +kernel)
def pv157393 : PrimeValue := ⟨157393, pr157393⟩
private theorem pr157411 : PrimeCertificate 157411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv53]) (by decide +kernel)
def pv157411 : PrimeValue := ⟨157411, pr157411⟩
private theorem pr157427 : PrimeCertificate 157427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv78713]) (by decide +kernel)
def pv157427 : PrimeValue := ⟨157427, pr157427⟩
private theorem pr157429 : PrimeCertificate 157429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv4373]) (by decide +kernel)
def pv157429 : PrimeValue := ⟨157429, pr157429⟩
private theorem pr157483 : PrimeCertificate 157483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv673]) (by decide +kernel)
def pv157483 : PrimeValue := ⟨157483, pr157483⟩
private theorem pr157513 : PrimeCertificate 157513 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv6563]) (by decide +kernel)
def pv157513 : PrimeValue := ⟨157513, pr157513⟩
private theorem pr157523 : PrimeCertificate 157523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv41,pv113]) (by decide +kernel)
def pv157523 : PrimeValue := ⟨157523, pr157523⟩
private theorem pr157543 : PrimeCertificate 157543 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv31]) (by decide +kernel)
def pv157543 : PrimeValue := ⟨157543, pr157543⟩
private theorem pr157559 : PrimeCertificate 157559 :=
  certifyPrime (q := pv17) (ls := [pv2,pv78779]) (by decide +kernel)
def pv157559 : PrimeValue := ⟨157559, pr157559⟩
private theorem pr157561 : PrimeCertificate 157561 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv13,pv101]) (by decide +kernel)
def pv157561 : PrimeValue := ⟨157561, pr157561⟩
private theorem pr157571 : PrimeCertificate 157571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv2251]) (by decide +kernel)
def pv157571 : PrimeValue := ⟨157571, pr157571⟩
private theorem pr157579 : PrimeCertificate 157579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv26263]) (by decide +kernel)
def pv157579 : PrimeValue := ⟨157579, pr157579⟩
private theorem pr157627 : PrimeCertificate 157627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv139]) (by decide +kernel)
def pv157627 : PrimeValue := ⟨157627, pr157627⟩
private theorem pr157637 : PrimeCertificate 157637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv39409]) (by decide +kernel)
def pv157637 : PrimeValue := ⟨157637, pr157637⟩
private theorem pr157639 : PrimeCertificate 157639 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv43,pv47]) (by decide +kernel)
def pv157639 : PrimeValue := ⟨157639, pr157639⟩
private theorem pr157649 : PrimeCertificate 157649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv59,pv167]) (by decide +kernel)
def pv157649 : PrimeValue := ⟨157649, pr157649⟩
private theorem pr157667 : PrimeCertificate 157667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv2543]) (by decide +kernel)
def pv157667 : PrimeValue := ⟨157667, pr157667⟩
private theorem pr157669 : PrimeCertificate 157669 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv1877]) (by decide +kernel)
def pv157669 : PrimeValue := ⟨157669, pr157669⟩
private theorem pr157679 : PrimeCertificate 157679 :=
  certifyPrime (q := pv7) (ls := [pv2,pv78839]) (by decide +kernel)
def pv157679 : PrimeValue := ⟨157679, pr157679⟩
private theorem pr157721 : PrimeCertificate 157721 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv3943]) (by decide +kernel)
def pv157721 : PrimeValue := ⟨157721, pr157721⟩
private theorem pr157733 : PrimeCertificate 157733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv839]) (by decide +kernel)
def pv157733 : PrimeValue := ⟨157733, pr157733⟩
private theorem pr157739 : PrimeCertificate 157739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv19,pv593]) (by decide +kernel)
def pv157739 : PrimeValue := ⟨157739, pr157739⟩
private theorem pr157747 : PrimeCertificate 157747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61,pv431]) (by decide +kernel)
def pv157747 : PrimeValue := ⟨157747, pr157747⟩
private theorem pr157769 : PrimeCertificate 157769 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv37,pv41]) (by decide +kernel)
def pv157769 : PrimeValue := ⟨157769, pr157769⟩
private theorem pr157771 : PrimeCertificate 157771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1753]) (by decide +kernel)
def pv157771 : PrimeValue := ⟨157771, pr157771⟩
private theorem pr157793 : PrimeCertificate 157793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv4931]) (by decide +kernel)
def pv157793 : PrimeValue := ⟨157793, pr157793⟩
private theorem pr157799 : PrimeCertificate 157799 :=
  certifyPrime (q := pv11) (ls := [pv2,pv257,pv307]) (by decide +kernel)
def pv157799 : PrimeValue := ⟨157799, pr157799⟩
private theorem pr157813 : PrimeCertificate 157813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13151]) (by decide +kernel)
def pv157813 : PrimeValue := ⟨157813, pr157813⟩
private theorem pr157823 : PrimeCertificate 157823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11273]) (by decide +kernel)
def pv157823 : PrimeValue := ⟨157823, pr157823⟩
private theorem pr157831 : PrimeCertificate 157831 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv5261]) (by decide +kernel)
def pv157831 : PrimeValue := ⟨157831, pr157831⟩
private theorem pr157837 : PrimeCertificate 157837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1879]) (by decide +kernel)
def pv157837 : PrimeValue := ⟨157837, pr157837⟩
private theorem pr157867 : PrimeCertificate 157867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv83,pv317]) (by decide +kernel)
def pv157867 : PrimeValue := ⟨157867, pr157867⟩
private theorem pr157877 : PrimeCertificate 157877 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv1361]) (by decide +kernel)
def pv157877 : PrimeValue := ⟨157877, pr157877⟩
private theorem pr157889 : PrimeCertificate 157889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2467]) (by decide +kernel)
def pv157889 : PrimeValue := ⟨157889, pr157889⟩
private theorem pr157897 : PrimeCertificate 157897 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv43]) (by decide +kernel)
def pv157897 : PrimeValue := ⟨157897, pr157897⟩
private theorem pr157901 : PrimeCertificate 157901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1579]) (by decide +kernel)
def pv157901 : PrimeValue := ⟨157901, pr157901⟩
private theorem pr157933 : PrimeCertificate 157933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv107]) (by decide +kernel)
def pv157933 : PrimeValue := ⟨157933, pr157933⟩
private theorem pr157951 : PrimeCertificate 157951 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv157951 : PrimeValue := ⟨157951, pr157951⟩
private theorem pr157991 : PrimeCertificate 157991 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv37,pv61]) (by decide +kernel)
def pv157991 : PrimeValue := ⟨157991, pr157991⟩
private theorem pr157999 : PrimeCertificate 157999 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv1549]) (by decide +kernel)
def pv157999 : PrimeValue := ⟨157999, pr157999⟩
private theorem pr158003 : PrimeCertificate 158003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv59,pv103]) (by decide +kernel)
def pv158003 : PrimeValue := ⟨158003, pr158003⟩
private theorem pr158009 : PrimeCertificate 158009 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19751]) (by decide +kernel)
def pv158009 : PrimeValue := ⟨158009, pr158009⟩
private theorem pr158017 : PrimeCertificate 158017 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv823]) (by decide +kernel)
def pv158017 : PrimeValue := ⟨158017, pr158017⟩
private theorem pr158029 : PrimeCertificate 158029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv1013]) (by decide +kernel)
def pv158029 : PrimeValue := ⟨158029, pr158029⟩
private theorem pr158047 : PrimeCertificate 158047 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv53,pv71]) (by decide +kernel)
def pv158047 : PrimeValue := ⟨158047, pr158047⟩
private theorem pr158071 : PrimeCertificate 158071 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv479]) (by decide +kernel)
def pv158071 : PrimeValue := ⟨158071, pr158071⟩
private theorem pr158077 : PrimeCertificate 158077 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4391]) (by decide +kernel)
def pv158077 : PrimeValue := ⟨158077, pr158077⟩
private theorem pr158113 : PrimeCertificate 158113 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv61]) (by decide +kernel)
def pv158113 : PrimeValue := ⟨158113, pr158113⟩
private theorem pr158129 : PrimeCertificate 158129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv9883]) (by decide +kernel)
def pv158129 : PrimeValue := ⟨158129, pr158129⟩
private theorem pr158141 : PrimeCertificate 158141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7907]) (by decide +kernel)
def pv158141 : PrimeValue := ⟨158141, pr158141⟩
private theorem pr158143 : PrimeCertificate 158143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv26357]) (by decide +kernel)
def pv158143 : PrimeValue := ⟨158143, pr158143⟩
private theorem pr158161 : PrimeCertificate 158161 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv659]) (by decide +kernel)
def pv158161 : PrimeValue := ⟨158161, pr158161⟩
private theorem pr158201 : PrimeCertificate 158201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv113]) (by decide +kernel)
def pv158201 : PrimeValue := ⟨158201, pr158201⟩
private theorem pr158209 : PrimeCertificate 158209 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv103]) (by decide +kernel)
def pv158209 : PrimeValue := ⟨158209, pr158209⟩
private theorem pr158231 : PrimeCertificate 158231 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv15823]) (by decide +kernel)
def pv158231 : PrimeValue := ⟨158231, pr158231⟩
private theorem pr158261 : PrimeCertificate 158261 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv41,pv193]) (by decide +kernel)
def pv158261 : PrimeValue := ⟨158261, pr158261⟩
private theorem pr158293 : PrimeCertificate 158293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv4397]) (by decide +kernel)
def pv158293 : PrimeValue := ⟨158293, pr158293⟩
private theorem pr158303 : PrimeCertificate 158303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv79151]) (by decide +kernel)
def pv158303 : PrimeValue := ⟨158303, pr158303⟩
private theorem pr158329 : PrimeCertificate 158329 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv733]) (by decide +kernel)
def pv158329 : PrimeValue := ⟨158329, pr158329⟩
private theorem pr158351 : PrimeCertificate 158351 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv3167]) (by decide +kernel)
def pv158351 : PrimeValue := ⟨158351, pr158351⟩
private theorem pr158357 : PrimeCertificate 158357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv59,pv61]) (by decide +kernel)
def pv158357 : PrimeValue := ⟨158357, pr158357⟩
private theorem pr158359 : PrimeCertificate 158359 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv26393]) (by decide +kernel)
def pv158359 : PrimeValue := ⟨158359, pr158359⟩
private theorem pr158363 : PrimeCertificate 158363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv79181]) (by decide +kernel)
def pv158363 : PrimeValue := ⟨158363, pr158363⟩
private theorem pr158371 : PrimeCertificate 158371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv5279]) (by decide +kernel)
def pv158371 : PrimeValue := ⟨158371, pr158371⟩
private theorem pr158393 : PrimeCertificate 158393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv1523]) (by decide +kernel)
def pv158393 : PrimeValue := ⟨158393, pr158393⟩
private theorem pr158407 : PrimeCertificate 158407 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv1553]) (by decide +kernel)
def pv158407 : PrimeValue := ⟨158407, pr158407⟩
private theorem pr158419 : PrimeCertificate 158419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv677]) (by decide +kernel)
def pv158419 : PrimeValue := ⟨158419, pr158419⟩
private theorem pr158429 : PrimeCertificate 158429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv39607]) (by decide +kernel)
def pv158429 : PrimeValue := ⟨158429, pr158429⟩
private theorem pr158443 : PrimeCertificate 158443 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv26407]) (by decide +kernel)
def pv158443 : PrimeValue := ⟨158443, pr158443⟩
private theorem pr158449 : PrimeCertificate 158449 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv3301]) (by decide +kernel)
def pv158449 : PrimeValue := ⟨158449, pr158449⟩
private theorem pr158551 : PrimeCertificate 158551 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv151]) (by decide +kernel)
def pv158551 : PrimeValue := ⟨158551, pr158551⟩
private theorem pr158563 : PrimeCertificate 158563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv383]) (by decide +kernel)
def pv158563 : PrimeValue := ⟨158563, pr158563⟩
private theorem pr158567 : PrimeCertificate 158567 :=
  certifyPrime (q := pv5) (ls := [pv2,pv79283]) (by decide +kernel)
def pv158567 : PrimeValue := ⟨158567, pr158567⟩
private theorem pr158573 : PrimeCertificate 158573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv1367]) (by decide +kernel)
def pv158573 : PrimeValue := ⟨158573, pr158573⟩
private theorem pr158581 : PrimeCertificate 158581 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv881]) (by decide +kernel)
def pv158581 : PrimeValue := ⟨158581, pr158581⟩
private theorem pr158597 : PrimeCertificate 158597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv1279]) (by decide +kernel)
def pv158597 : PrimeValue := ⟨158597, pr158597⟩
private theorem pr158611 : PrimeCertificate 158611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv311]) (by decide +kernel)
def pv158611 : PrimeValue := ⟨158611, pr158611⟩
private theorem pr158617 : PrimeCertificate 158617 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2203]) (by decide +kernel)
def pv158617 : PrimeValue := ⟨158617, pr158617⟩
private theorem pr158633 : PrimeCertificate 158633 :=
  certifyPrime (q := pv3) (ls := [pv2,pv79,pv251]) (by decide +kernel)
def pv158633 : PrimeValue := ⟨158633, pr158633⟩
private theorem pr158647 : PrimeCertificate 158647 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv137,pv193]) (by decide +kernel)
def pv158647 : PrimeValue := ⟨158647, pr158647⟩
private theorem pr158657 : PrimeCertificate 158657 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv67]) (by decide +kernel)
def pv158657 : PrimeValue := ⟨158657, pr158657⟩
private theorem pr158663 : PrimeCertificate 158663 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv1619]) (by decide +kernel)
def pv158663 : PrimeValue := ⟨158663, pr158663⟩
private theorem pr158699 : PrimeCertificate 158699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv79349]) (by decide +kernel)
def pv158699 : PrimeValue := ⟨158699, pr158699⟩
private theorem pr158731 : PrimeCertificate 158731 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv13,pv37]) (by decide +kernel)
def pv158731 : PrimeValue := ⟨158731, pr158731⟩
private theorem pr158749 : PrimeCertificate 158749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13229]) (by decide +kernel)
def pv158749 : PrimeValue := ⟨158749, pr158749⟩
private theorem pr158759 : PrimeCertificate 158759 :=
  certifyPrime (q := pv23) (ls := [pv2,pv79379]) (by decide +kernel)
def pv158759 : PrimeValue := ⟨158759, pr158759⟩
private theorem pr158761 : PrimeCertificate 158761 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv158761 : PrimeValue := ⟨158761, pr158761⟩
private theorem pr158791 : PrimeCertificate 158791 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv67,pv79]) (by decide +kernel)
def pv158791 : PrimeValue := ⟨158791, pr158791⟩
private theorem pr158803 : PrimeCertificate 158803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv19,pv199]) (by decide +kernel)
def pv158803 : PrimeValue := ⟨158803, pr158803⟩
private theorem pr158843 : PrimeCertificate 158843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv1847]) (by decide +kernel)
def pv158843 : PrimeValue := ⟨158843, pr158843⟩
private theorem pr158849 : PrimeCertificate 158849 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv73]) (by decide +kernel)
def pv158849 : PrimeValue := ⟨158849, pr158849⟩
private theorem pr158863 : PrimeCertificate 158863 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv11,pv29,pv83]) (by decide +kernel)
def pv158863 : PrimeValue := ⟨158863, pr158863⟩
private theorem pr158867 : PrimeCertificate 158867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv79433]) (by decide +kernel)
def pv158867 : PrimeValue := ⟨158867, pr158867⟩
private theorem pr158881 : PrimeCertificate 158881 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv331]) (by decide +kernel)
def pv158881 : PrimeValue := ⟨158881, pr158881⟩
private theorem pr158909 : PrimeCertificate 158909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv39727]) (by decide +kernel)
def pv158909 : PrimeValue := ⟨158909, pr158909⟩
private theorem pr158923 : PrimeCertificate 158923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv109]) (by decide +kernel)
def pv158923 : PrimeValue := ⟨158923, pr158923⟩
private theorem pr158927 : PrimeCertificate 158927 :=
  certifyPrime (q := pv5) (ls := [pv2,pv229,pv347]) (by decide +kernel)
def pv158927 : PrimeValue := ⟨158927, pr158927⟩
private theorem pr158941 : PrimeCertificate 158941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv883]) (by decide +kernel)
def pv158941 : PrimeValue := ⟨158941, pr158941⟩
private theorem pr158959 : PrimeCertificate 158959 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv8831]) (by decide +kernel)
def pv158959 : PrimeValue := ⟨158959, pr158959⟩
private theorem pr158981 : PrimeCertificate 158981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7949]) (by decide +kernel)
def pv158981 : PrimeValue := ⟨158981, pr158981⟩
private theorem pr158993 : PrimeCertificate 158993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv523]) (by decide +kernel)
def pv158993 : PrimeValue := ⟨158993, pr158993⟩
private theorem pr159013 : PrimeCertificate 159013 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv7,pv631]) (by decide +kernel)
def pv159013 : PrimeValue := ⟨159013, pr159013⟩
private theorem pr159017 : PrimeCertificate 159017 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv13,pv139]) (by decide +kernel)
def pv159017 : PrimeValue := ⟨159017, pr159017⟩
private theorem pr159023 : PrimeCertificate 159023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv3457]) (by decide +kernel)
def pv159023 : PrimeValue := ⟨159023, pr159023⟩
private theorem pr159059 : PrimeCertificate 159059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67,pv1187]) (by decide +kernel)
def pv159059 : PrimeValue := ⟨159059, pr159059⟩
private theorem pr159073 : PrimeCertificate 159073 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1657]) (by decide +kernel)
def pv159073 : PrimeValue := ⟨159073, pr159073⟩
private theorem pr159079 : PrimeCertificate 159079 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv26513]) (by decide +kernel)
def pv159079 : PrimeValue := ⟨159079, pr159079⟩
private theorem pr159097 : PrimeCertificate 159097 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv947]) (by decide +kernel)
def pv159097 : PrimeValue := ⟨159097, pr159097⟩
private theorem pr159113 : PrimeCertificate 159113 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19889]) (by decide +kernel)
def pv159113 : PrimeValue := ⟨159113, pr159113⟩
private theorem pr159119 : PrimeCertificate 159119 :=
  certifyPrime (q := pv7) (ls := [pv2,pv79559]) (by decide +kernel)
def pv159119 : PrimeValue := ⟨159119, pr159119⟩
private theorem pr159161 : PrimeCertificate 159161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv23,pv173]) (by decide +kernel)
def pv159161 : PrimeValue := ⟨159161, pr159161⟩
private theorem pr159167 : PrimeCertificate 159167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11369]) (by decide +kernel)
def pv159167 : PrimeValue := ⟨159167, pr159167⟩
private theorem pr159169 : PrimeCertificate 159169 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv829]) (by decide +kernel)
def pv159169 : PrimeValue := ⟨159169, pr159169⟩
private theorem pr159179 : PrimeCertificate 159179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv79589]) (by decide +kernel)
def pv159179 : PrimeValue := ⟨159179, pr159179⟩
private theorem pr159191 : PrimeCertificate 159191 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv15919]) (by decide +kernel)
def pv159191 : PrimeValue := ⟨159191, pr159191⟩
private theorem pr159193 : PrimeCertificate 159193 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv67]) (by decide +kernel)
def pv159193 : PrimeValue := ⟨159193, pr159193⟩
private theorem pr159209 : PrimeCertificate 159209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv2843]) (by decide +kernel)
def pv159209 : PrimeValue := ⟨159209, pr159209⟩
private theorem pr159223 : PrimeCertificate 159223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv17,pv223]) (by decide +kernel)
def pv159223 : PrimeValue := ⟨159223, pr159223⟩
private theorem pr159227 : PrimeCertificate 159227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv79613]) (by decide +kernel)
def pv159227 : PrimeValue := ⟨159227, pr159227⟩
private theorem pr159233 : PrimeCertificate 159233 :=
  certifyPrime (q := pv3) (ls := [pv2,pv311]) (by decide +kernel)
def pv159233 : PrimeValue := ⟨159233, pr159233⟩
private theorem pr159287 : PrimeCertificate 159287 :=
  certifyPrime (q := pv5) (ls := [pv2,pv73,pv1091]) (by decide +kernel)
def pv159287 : PrimeValue := ⟨159287, pr159287⟩
private theorem pr159293 : PrimeCertificate 159293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv5689]) (by decide +kernel)
def pv159293 : PrimeValue := ⟨159293, pr159293⟩
private theorem pr159311 : PrimeCertificate 159311 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv89,pv179]) (by decide +kernel)
def pv159311 : PrimeValue := ⟨159311, pr159311⟩
private theorem pr159319 : PrimeCertificate 159319 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv53,pv167]) (by decide +kernel)
def pv159319 : PrimeValue := ⟨159319, pr159319⟩
private theorem pr159337 : PrimeCertificate 159337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2213]) (by decide +kernel)
def pv159337 : PrimeValue := ⟨159337, pr159337⟩
private theorem pr159347 : PrimeCertificate 159347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv7243]) (by decide +kernel)
def pv159347 : PrimeValue := ⟨159347, pr159347⟩
private theorem pr159349 : PrimeCertificate 159349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv271]) (by decide +kernel)
def pv159349 : PrimeValue := ⟨159349, pr159349⟩
private theorem pr159389 : PrimeCertificate 159389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv39847]) (by decide +kernel)
def pv159389 : PrimeValue := ⟨159389, pr159389⟩
private theorem pr159403 : PrimeCertificate 159403 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv857]) (by decide +kernel)
def pv159403 : PrimeValue := ⟨159403, pr159403⟩
private theorem pr159407 : PrimeCertificate 159407 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv6131]) (by decide +kernel)
def pv159407 : PrimeValue := ⟨159407, pr159407⟩
private theorem pr159421 : PrimeCertificate 159421 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv2657]) (by decide +kernel)
def pv159421 : PrimeValue := ⟨159421, pr159421⟩
private theorem pr159431 : PrimeCertificate 159431 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv107,pv149]) (by decide +kernel)
def pv159431 : PrimeValue := ⟨159431, pr159431⟩
private theorem pr159457 : PrimeCertificate 159457 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv151]) (by decide +kernel)
def pv159457 : PrimeValue := ⟨159457, pr159457⟩
private theorem pr159463 : PrimeCertificate 159463 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv2953]) (by decide +kernel)
def pv159463 : PrimeValue := ⟨159463, pr159463⟩
private theorem pr159469 : PrimeCertificate 159469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv97,pv137]) (by decide +kernel)
def pv159469 : PrimeValue := ⟨159469, pr159469⟩
private theorem pr159491 : PrimeCertificate 159491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41,pv389]) (by decide +kernel)
def pv159491 : PrimeValue := ⟨159491, pr159491⟩
private theorem pr159499 : PrimeCertificate 159499 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv8861]) (by decide +kernel)
def pv159499 : PrimeValue := ⟨159499, pr159499⟩
private theorem pr159521 : PrimeCertificate 159521 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv997]) (by decide +kernel)
def pv159521 : PrimeValue := ⟨159521, pr159521⟩
private theorem pr159539 : PrimeCertificate 159539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv79769]) (by decide +kernel)
def pv159539 : PrimeValue := ⟨159539, pr159539⟩
private theorem pr159541 : PrimeCertificate 159541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv2659]) (by decide +kernel)
def pv159541 : PrimeValue := ⟨159541, pr159541⟩
private theorem pr159553 : PrimeCertificate 159553 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv277]) (by decide +kernel)
def pv159553 : PrimeValue := ⟨159553, pr159553⟩
private theorem pr159563 : PrimeCertificate 159563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv17,pv19]) (by decide +kernel)
def pv159563 : PrimeValue := ⟨159563, pr159563⟩
private theorem pr159569 : PrimeCertificate 159569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv9973]) (by decide +kernel)
def pv159569 : PrimeValue := ⟨159569, pr159569⟩
private theorem pr159571 : PrimeCertificate 159571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv197]) (by decide +kernel)
def pv159571 : PrimeValue := ⟨159571, pr159571⟩
private theorem pr159617 : PrimeCertificate 159617 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv43]) (by decide +kernel)
def pv159617 : PrimeValue := ⟨159617, pr159617⟩
private theorem pr159623 : PrimeCertificate 159623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv79811]) (by decide +kernel)
def pv159623 : PrimeValue := ⟨159623, pr159623⟩
private theorem pr159629 : PrimeCertificate 159629 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv5701]) (by decide +kernel)
def pv159629 : PrimeValue := ⟨159629, pr159629⟩
private theorem pr159631 : PrimeCertificate 159631 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv17,pv313]) (by decide +kernel)
def pv159631 : PrimeValue := ⟨159631, pr159631⟩
private theorem pr159667 : PrimeCertificate 159667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv23,pv89]) (by decide +kernel)
def pv159667 : PrimeValue := ⟨159667, pr159667⟩
private theorem pr159671 : PrimeCertificate 159671 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv2281]) (by decide +kernel)
def pv159671 : PrimeValue := ⟨159671, pr159671⟩
private theorem pr159673 : PrimeCertificate 159673 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv6653]) (by decide +kernel)
def pv159673 : PrimeValue := ⟨159673, pr159673⟩
private theorem pr159697 : PrimeCertificate 159697 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1109]) (by decide +kernel)
def pv159697 : PrimeValue := ⟨159697, pr159697⟩
private theorem pr159701 : PrimeCertificate 159701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1597]) (by decide +kernel)
def pv159701 : PrimeValue := ⟨159701, pr159701⟩
private theorem pr159707 : PrimeCertificate 159707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv1699]) (by decide +kernel)
def pv159707 : PrimeValue := ⟨159707, pr159707⟩
private theorem pr159721 : PrimeCertificate 159721 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv159721 : PrimeValue := ⟨159721, pr159721⟩
private theorem pr159737 : PrimeCertificate 159737 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41,pv487]) (by decide +kernel)
def pv159737 : PrimeValue := ⟨159737, pr159737⟩
private theorem pr159739 : PrimeCertificate 159739 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv79,pv337]) (by decide +kernel)
def pv159739 : PrimeValue := ⟨159739, pr159739⟩
private theorem pr159763 : PrimeCertificate 159763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv26627]) (by decide +kernel)
def pv159763 : PrimeValue := ⟨159763, pr159763⟩
private theorem pr159773 : PrimeCertificate 159773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59,pv677]) (by decide +kernel)
def pv159773 : PrimeValue := ⟨159773, pr159773⟩
private theorem pr159779 : PrimeCertificate 159779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv79889]) (by decide +kernel)
def pv159779 : PrimeValue := ⟨159779, pr159779⟩
private theorem pr159791 : PrimeCertificate 159791 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv19,pv29]) (by decide +kernel)
def pv159791 : PrimeValue := ⟨159791, pr159791⟩
private theorem pr159793 : PrimeCertificate 159793 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3329]) (by decide +kernel)
def pv159793 : PrimeValue := ⟨159793, pr159793⟩
private theorem pr159811 : PrimeCertificate 159811 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv761]) (by decide +kernel)
def pv159811 : PrimeValue := ⟨159811, pr159811⟩
private theorem pr159839 : PrimeCertificate 159839 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv233]) (by decide +kernel)
def pv159839 : PrimeValue := ⟨159839, pr159839⟩
private theorem pr159853 : PrimeCertificate 159853 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv7,pv11,pv173]) (by decide +kernel)
def pv159853 : PrimeValue := ⟨159853, pr159853⟩
private theorem pr159857 : PrimeCertificate 159857 :=
  certifyPrime (q := pv3) (ls := [pv2,pv97,pv103]) (by decide +kernel)
def pv159857 : PrimeValue := ⟨159857, pr159857⟩
private theorem pr159869 : PrimeCertificate 159869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv2351]) (by decide +kernel)
def pv159869 : PrimeValue := ⟨159869, pr159869⟩
private theorem pr159871 : PrimeCertificate 159871 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv73]) (by decide +kernel)
def pv159871 : PrimeValue := ⟨159871, pr159871⟩
private theorem pr159899 : PrimeCertificate 159899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv2579]) (by decide +kernel)
def pv159899 : PrimeValue := ⟨159899, pr159899⟩
private theorem pr159911 : PrimeCertificate 159911 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv15991]) (by decide +kernel)
def pv159911 : PrimeValue := ⟨159911, pr159911⟩
private theorem pr159937 : PrimeCertificate 159937 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv17]) (by decide +kernel)
def pv159937 : PrimeValue := ⟨159937, pr159937⟩
private theorem pr159977 : PrimeCertificate 159977 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19997]) (by decide +kernel)
def pv159977 : PrimeValue := ⟨159977, pr159977⟩
private theorem pr160001 : PrimeCertificate 160001 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5]) (by decide +kernel)
def pv160001 : PrimeValue := ⟨160001, pr160001⟩
private theorem pr160019 : PrimeCertificate 160019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv4211]) (by decide +kernel)
def pv160019 : PrimeValue := ⟨160019, pr160019⟩
private theorem pr160031 : PrimeCertificate 160031 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv13,pv1231]) (by decide +kernel)
def pv160031 : PrimeValue := ⟨160031, pr160031⟩
private theorem pr160033 : PrimeCertificate 160033 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1667]) (by decide +kernel)
def pv160033 : PrimeValue := ⟨160033, pr160033⟩
private theorem pr160049 : PrimeCertificate 160049 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv1429]) (by decide +kernel)
def pv160049 : PrimeValue := ⟨160049, pr160049⟩
private theorem pr160079 : PrimeCertificate 160079 :=
  certifyPrime (q := pv17) (ls := [pv2,pv80039]) (by decide +kernel)
def pv160079 : PrimeValue := ⟨160079, pr160079⟩
private theorem pr160081 : PrimeCertificate 160081 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv5,pv23,pv29]) (by decide +kernel)
def pv160081 : PrimeValue := ⟨160081, pr160081⟩
private theorem pr160087 : PrimeCertificate 160087 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv26681]) (by decide +kernel)
def pv160087 : PrimeValue := ⟨160087, pr160087⟩
private theorem pr160091 : PrimeCertificate 160091 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv2287]) (by decide +kernel)
def pv160091 : PrimeValue := ⟨160091, pr160091⟩
private theorem pr160117 : PrimeCertificate 160117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv1213]) (by decide +kernel)
def pv160117 : PrimeValue := ⟨160117, pr160117⟩
private theorem pr160141 : PrimeCertificate 160141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv157]) (by decide +kernel)
def pv160141 : PrimeValue := ⟨160141, pr160141⟩
private theorem pr160159 : PrimeCertificate 160159 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv26693]) (by decide +kernel)
def pv160159 : PrimeValue := ⟨160159, pr160159⟩
private theorem pr160169 : PrimeCertificate 160169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv20021]) (by decide +kernel)
def pv160169 : PrimeValue := ⟨160169, pr160169⟩
private theorem pr160183 : PrimeCertificate 160183 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv809]) (by decide +kernel)
def pv160183 : PrimeValue := ⟨160183, pr160183⟩
private theorem pr160201 : PrimeCertificate 160201 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv89]) (by decide +kernel)
def pv160201 : PrimeValue := ⟨160201, pr160201⟩
private theorem pr160207 : PrimeCertificate 160207 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv26701]) (by decide +kernel)
def pv160207 : PrimeValue := ⟨160207, pr160207⟩
private theorem pr160231 : PrimeCertificate 160231 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv109]) (by decide +kernel)
def pv160231 : PrimeValue := ⟨160231, pr160231⟩
private theorem pr160243 : PrimeCertificate 160243 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv17,pv1571]) (by decide +kernel)
def pv160243 : PrimeValue := ⟨160243, pr160243⟩
private theorem pr160253 : PrimeCertificate 160253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv40063]) (by decide +kernel)
def pv160253 : PrimeValue := ⟨160253, pr160253⟩
private theorem pr160309 : PrimeCertificate 160309 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv61,pv73]) (by decide +kernel)
def pv160309 : PrimeValue := ⟨160309, pr160309⟩
private theorem pr160313 : PrimeCertificate 160313 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv691]) (by decide +kernel)
def pv160313 : PrimeValue := ⟨160313, pr160313⟩
private theorem pr160343 : PrimeCertificate 160343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv13,pv881]) (by decide +kernel)
def pv160343 : PrimeValue := ⟨160343, pr160343⟩
private theorem pr160357 : PrimeCertificate 160357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv23,pv83]) (by decide +kernel)
def pv160357 : PrimeValue := ⟨160357, pr160357⟩
private theorem pr160367 : PrimeCertificate 160367 :=
  certifyPrime (q := pv5) (ls := [pv2,pv181,pv443]) (by decide +kernel)
def pv160367 : PrimeValue := ⟨160367, pr160367⟩
private theorem pr160373 : PrimeCertificate 160373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv40093]) (by decide +kernel)
def pv160373 : PrimeValue := ⟨160373, pr160373⟩
private theorem pr160387 : PrimeCertificate 160387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv26731]) (by decide +kernel)
def pv160387 : PrimeValue := ⟨160387, pr160387⟩
private theorem pr160403 : PrimeCertificate 160403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv23,pv317]) (by decide +kernel)
def pv160403 : PrimeValue := ⟨160403, pr160403⟩
private theorem pr160409 : PrimeCertificate 160409 :=
  certifyPrime (q := pv3) (ls := [pv2,pv20051]) (by decide +kernel)
def pv160409 : PrimeValue := ⟨160409, pr160409⟩
private theorem pr160423 : PrimeCertificate 160423 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv26737]) (by decide +kernel)
def pv160423 : PrimeValue := ⟨160423, pr160423⟩
private theorem pr160441 : PrimeCertificate 160441 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv191]) (by decide +kernel)
def pv160441 : PrimeValue := ⟨160441, pr160441⟩
private theorem pr160453 : PrimeCertificate 160453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv4457]) (by decide +kernel)
def pv160453 : PrimeValue := ⟨160453, pr160453⟩
private theorem pr160481 : PrimeCertificate 160481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17,pv59]) (by decide +kernel)
def pv160481 : PrimeValue := ⟨160481, pr160481⟩
private theorem pr160483 : PrimeCertificate 160483 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv3821]) (by decide +kernel)
def pv160483 : PrimeValue := ⟨160483, pr160483⟩
private theorem pr160507 : PrimeCertificate 160507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv241]) (by decide +kernel)
def pv160507 : PrimeValue := ⟨160507, pr160507⟩
private theorem pr160541 : PrimeCertificate 160541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv349]) (by decide +kernel)
def pv160541 : PrimeValue := ⟨160541, pr160541⟩
private theorem pr160553 : PrimeCertificate 160553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv47,pv61]) (by decide +kernel)
def pv160553 : PrimeValue := ⟨160553, pr160553⟩
private theorem pr160579 : PrimeCertificate 160579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv811]) (by decide +kernel)
def pv160579 : PrimeValue := ⟨160579, pr160579⟩
private theorem pr160583 : PrimeCertificate 160583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv4723]) (by decide +kernel)
def pv160583 : PrimeValue := ⟨160583, pr160583⟩
private theorem pr160603 : PrimeCertificate 160603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv29,pv71]) (by decide +kernel)
def pv160603 : PrimeValue := ⟨160603, pr160603⟩
private theorem pr160619 : PrimeCertificate 160619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv80309]) (by decide +kernel)
def pv160619 : PrimeValue := ⟨160619, pr160619⟩
private theorem pr160621 : PrimeCertificate 160621 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv2677]) (by decide +kernel)
def pv160621 : PrimeValue := ⟨160621, pr160621⟩
private theorem pr160627 : PrimeCertificate 160627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv1409]) (by decide +kernel)
def pv160627 : PrimeValue := ⟨160627, pr160627⟩
private theorem pr160637 : PrimeCertificate 160637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv5737]) (by decide +kernel)
def pv160637 : PrimeValue := ⟨160637, pr160637⟩
private theorem pr160639 : PrimeCertificate 160639 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41,pv653]) (by decide +kernel)
def pv160639 : PrimeValue := ⟨160639, pr160639⟩
private theorem pr160649 : PrimeCertificate 160649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43,pv467]) (by decide +kernel)
def pv160649 : PrimeValue := ⟨160649, pr160649⟩
private theorem pr160651 : PrimeCertificate 160651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv17]) (by decide +kernel)
def pv160651 : PrimeValue := ⟨160651, pr160651⟩
private theorem pr160663 : PrimeCertificate 160663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv26777]) (by decide +kernel)
def pv160663 : PrimeValue := ⟨160663, pr160663⟩
private theorem pr160669 : PrimeCertificate 160669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv4463]) (by decide +kernel)
def pv160669 : PrimeValue := ⟨160669, pr160669⟩
private theorem pr160681 : PrimeCertificate 160681 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv13,pv103]) (by decide +kernel)
def pv160681 : PrimeValue := ⟨160681, pr160681⟩
private theorem pr160687 : PrimeCertificate 160687 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv79,pv113]) (by decide +kernel)
def pv160687 : PrimeValue := ⟨160687, pr160687⟩
private theorem pr160697 : PrimeCertificate 160697 :=
  certifyPrime (q := pv3) (ls := [pv2,pv53,pv379]) (by decide +kernel)
def pv160697 : PrimeValue := ⟨160697, pr160697⟩
private theorem pr160709 : PrimeCertificate 160709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv40177]) (by decide +kernel)
def pv160709 : PrimeValue := ⟨160709, pr160709⟩
private theorem pr160711 : PrimeCertificate 160711 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv487]) (by decide +kernel)
def pv160711 : PrimeValue := ⟨160711, pr160711⟩
private theorem pr160723 : PrimeCertificate 160723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv8929]) (by decide +kernel)
def pv160723 : PrimeValue := ⟨160723, pr160723⟩
private theorem pr160739 : PrimeCertificate 160739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv80369]) (by decide +kernel)
def pv160739 : PrimeValue := ⟨160739, pr160739⟩
private theorem pr160751 : PrimeCertificate 160751 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv643]) (by decide +kernel)
def pv160751 : PrimeValue := ⟨160751, pr160751⟩
private theorem pr160753 : PrimeCertificate 160753 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv197]) (by decide +kernel)
def pv160753 : PrimeValue := ⟨160753, pr160753⟩
private theorem pr160757 : PrimeCertificate 160757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv40189]) (by decide +kernel)
def pv160757 : PrimeValue := ⟨160757, pr160757⟩
private theorem pr160813 : PrimeCertificate 160813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1489]) (by decide +kernel)
def pv160813 : PrimeValue := ⟨160813, pr160813⟩
private theorem pr160817 : PrimeCertificate 160817 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv23]) (by decide +kernel)
def pv160817 : PrimeValue := ⟨160817, pr160817⟩
private theorem pr160829 : PrimeCertificate 160829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv1297]) (by decide +kernel)
def pv160829 : PrimeValue := ⟨160829, pr160829⟩
private theorem pr160841 : PrimeCertificate 160841 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv4021]) (by decide +kernel)
def pv160841 : PrimeValue := ⟨160841, pr160841⟩
private theorem pr160861 : PrimeCertificate 160861 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv383]) (by decide +kernel)
def pv160861 : PrimeValue := ⟨160861, pr160861⟩
private theorem pr160903 : PrimeCertificate 160903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv1277]) (by decide +kernel)
def pv160903 : PrimeValue := ⟨160903, pr160903⟩
private theorem pr160907 : PrimeCertificate 160907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv1871]) (by decide +kernel)
def pv160907 : PrimeValue := ⟨160907, pr160907⟩
private theorem pr160967 : PrimeCertificate 160967 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv41,pv151]) (by decide +kernel)
def pv160967 : PrimeValue := ⟨160967, pr160967⟩
private theorem pr160969 : PrimeCertificate 160969 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv19,pv353]) (by decide +kernel)
def pv160969 : PrimeValue := ⟨160969, pr160969⟩
private theorem pr160981 : PrimeCertificate 160981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv2683]) (by decide +kernel)
def pv160981 : PrimeValue := ⟨160981, pr160981⟩
private theorem pr160997 : PrimeCertificate 160997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv3659]) (by decide +kernel)
def pv160997 : PrimeValue := ⟨160997, pr160997⟩
private theorem pr161009 : PrimeCertificate 161009 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv347]) (by decide +kernel)
def pv161009 : PrimeValue := ⟨161009, pr161009⟩
private theorem pr161033 : PrimeCertificate 161033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv20129]) (by decide +kernel)
def pv161033 : PrimeValue := ⟨161033, pr161033⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
