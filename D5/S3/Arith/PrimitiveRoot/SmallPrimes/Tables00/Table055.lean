/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table055
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table055.pv157291
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table007
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table011
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table030
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table031

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr157291 : Nat.Prime 157291 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv107]) (by decide +kernel)
def pv157291 : PrimeValue := ⟨157291, pr157291⟩
private theorem pr157303 : Nat.Prime 157303 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv971]) (by decide +kernel)
def pv157303 : PrimeValue := ⟨157303, pr157303⟩
private theorem pr157307 : Nat.Prime 157307 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv78653]) (by decide +kernel)
def pv157307 : PrimeValue := ⟨157307, pr157307⟩
private theorem pr157327 : Nat.Prime 157327 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv2017]) (by decide +kernel)
def pv157327 : PrimeValue := ⟨157327, pr157327⟩
private theorem pr157349 : Nat.Prime 157349 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv139,pv283]) (by decide +kernel)
def pv157349 : PrimeValue := ⟨157349, pr157349⟩
private theorem pr157351 : Nat.Prime 157351 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv3,pv5,pv1049]) (by decide +kernel)
def pv157351 : PrimeValue := ⟨157351, pr157351⟩
private theorem pr157363 : Nat.Prime 157363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv26227]) (by decide +kernel)
def pv157363 : PrimeValue := ⟨157363, pr157363⟩
private theorem pr157393 : Nat.Prime 157393 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1093]) (by decide +kernel)
def pv157393 : PrimeValue := ⟨157393, pr157393⟩
private theorem pr157411 : Nat.Prime 157411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv53]) (by decide +kernel)
def pv157411 : PrimeValue := ⟨157411, pr157411⟩
private theorem pr157427 : Nat.Prime 157427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv78713]) (by decide +kernel)
def pv157427 : PrimeValue := ⟨157427, pr157427⟩
private theorem pr157429 : Nat.Prime 157429 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4373]) (by decide +kernel)
def pv157429 : PrimeValue := ⟨157429, pr157429⟩
private theorem pr157483 : Nat.Prime 157483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv673]) (by decide +kernel)
def pv157483 : PrimeValue := ⟨157483, pr157483⟩
private theorem pr157513 : Nat.Prime 157513 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv6563]) (by decide +kernel)
def pv157513 : PrimeValue := ⟨157513, pr157513⟩
private theorem pr157523 : Nat.Prime 157523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv41,pv113]) (by decide +kernel)
def pv157523 : PrimeValue := ⟨157523, pr157523⟩
private theorem pr157543 : Nat.Prime 157543 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv31]) (by decide +kernel)
def pv157543 : PrimeValue := ⟨157543, pr157543⟩
private theorem pr157559 : Nat.Prime 157559 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv78779]) (by decide +kernel)
def pv157559 : PrimeValue := ⟨157559, pr157559⟩
private theorem pr157561 : Nat.Prime 157561 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv13,pv101]) (by decide +kernel)
def pv157561 : PrimeValue := ⟨157561, pr157561⟩
private theorem pr157571 : Nat.Prime 157571 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv2251]) (by decide +kernel)
def pv157571 : PrimeValue := ⟨157571, pr157571⟩
private theorem pr157579 : Nat.Prime 157579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv26263]) (by decide +kernel)
def pv157579 : PrimeValue := ⟨157579, pr157579⟩
private theorem pr157627 : Nat.Prime 157627 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv139]) (by decide +kernel)
def pv157627 : PrimeValue := ⟨157627, pr157627⟩
private theorem pr157637 : Nat.Prime 157637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv39409]) (by decide +kernel)
def pv157637 : PrimeValue := ⟨157637, pr157637⟩
private theorem pr157639 : Nat.Prime 157639 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv43,pv47]) (by decide +kernel)
def pv157639 : PrimeValue := ⟨157639, pr157639⟩
private theorem pr157649 : Nat.Prime 157649 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv59,pv167]) (by decide +kernel)
def pv157649 : PrimeValue := ⟨157649, pr157649⟩
private theorem pr157667 : Nat.Prime 157667 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv2543]) (by decide +kernel)
def pv157667 : PrimeValue := ⟨157667, pr157667⟩
private theorem pr157669 : Nat.Prime 157669 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv1877]) (by decide +kernel)
def pv157669 : PrimeValue := ⟨157669, pr157669⟩
private theorem pr157679 : Nat.Prime 157679 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv78839]) (by decide +kernel)
def pv157679 : PrimeValue := ⟨157679, pr157679⟩
private theorem pr157721 : Nat.Prime 157721 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv3943]) (by decide +kernel)
def pv157721 : PrimeValue := ⟨157721, pr157721⟩
private theorem pr157733 : Nat.Prime 157733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv839]) (by decide +kernel)
def pv157733 : PrimeValue := ⟨157733, pr157733⟩
private theorem pr157739 : Nat.Prime 157739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv19,pv593]) (by decide +kernel)
def pv157739 : PrimeValue := ⟨157739, pr157739⟩
private theorem pr157747 : Nat.Prime 157747 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv61,pv431]) (by decide +kernel)
def pv157747 : PrimeValue := ⟨157747, pr157747⟩
private theorem pr157769 : Nat.Prime 157769 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv37,pv41]) (by decide +kernel)
def pv157769 : PrimeValue := ⟨157769, pr157769⟩
private theorem pr157771 : Nat.Prime 157771 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1753]) (by decide +kernel)
def pv157771 : PrimeValue := ⟨157771, pr157771⟩
private theorem pr157793 : Nat.Prime 157793 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv4931]) (by decide +kernel)
def pv157793 : PrimeValue := ⟨157793, pr157793⟩
private theorem pr157799 : Nat.Prime 157799 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv257,pv307]) (by decide +kernel)
def pv157799 : PrimeValue := ⟨157799, pr157799⟩
private theorem pr157813 : Nat.Prime 157813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13151]) (by decide +kernel)
def pv157813 : PrimeValue := ⟨157813, pr157813⟩
private theorem pr157823 : Nat.Prime 157823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv11273]) (by decide +kernel)
def pv157823 : PrimeValue := ⟨157823, pr157823⟩
private theorem pr157831 : Nat.Prime 157831 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv5261]) (by decide +kernel)
def pv157831 : PrimeValue := ⟨157831, pr157831⟩
private theorem pr157837 : Nat.Prime 157837 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv1879]) (by decide +kernel)
def pv157837 : PrimeValue := ⟨157837, pr157837⟩
private theorem pr157867 : Nat.Prime 157867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv83,pv317]) (by decide +kernel)
def pv157867 : PrimeValue := ⟨157867, pr157867⟩
private theorem pr157877 : Nat.Prime 157877 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv1361]) (by decide +kernel)
def pv157877 : PrimeValue := ⟨157877, pr157877⟩
private theorem pr157889 : Nat.Prime 157889 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv2467]) (by decide +kernel)
def pv157889 : PrimeValue := ⟨157889, pr157889⟩
private theorem pr157897 : Nat.Prime 157897 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv17,pv43]) (by decide +kernel)
def pv157897 : PrimeValue := ⟨157897, pr157897⟩
private theorem pr157901 : Nat.Prime 157901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1579]) (by decide +kernel)
def pv157901 : PrimeValue := ⟨157901, pr157901⟩
private theorem pr157933 : Nat.Prime 157933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv41,pv107]) (by decide +kernel)
def pv157933 : PrimeValue := ⟨157933, pr157933⟩
private theorem pr157951 : Nat.Prime 157951 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv157951 : PrimeValue := ⟨157951, pr157951⟩
private theorem pr157991 : Nat.Prime 157991 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv37,pv61]) (by decide +kernel)
def pv157991 : PrimeValue := ⟨157991, pr157991⟩
private theorem pr157999 : Nat.Prime 157999 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv1549]) (by decide +kernel)
def pv157999 : PrimeValue := ⟨157999, pr157999⟩
private theorem pr158003 : Nat.Prime 158003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv59,pv103]) (by decide +kernel)
def pv158003 : PrimeValue := ⟨158003, pr158003⟩
private theorem pr158009 : Nat.Prime 158009 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19751]) (by decide +kernel)
def pv158009 : PrimeValue := ⟨158009, pr158009⟩
private theorem pr158017 : Nat.Prime 158017 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv823]) (by decide +kernel)
def pv158017 : PrimeValue := ⟨158017, pr158017⟩
private theorem pr158029 : Nat.Prime 158029 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv1013]) (by decide +kernel)
def pv158029 : PrimeValue := ⟨158029, pr158029⟩
private theorem pr158047 : Nat.Prime 158047 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv53,pv71]) (by decide +kernel)
def pv158047 : PrimeValue := ⟨158047, pr158047⟩
private theorem pr158071 : Nat.Prime 158071 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv479]) (by decide +kernel)
def pv158071 : PrimeValue := ⟨158071, pr158071⟩
private theorem pr158077 : Nat.Prime 158077 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv4391]) (by decide +kernel)
def pv158077 : PrimeValue := ⟨158077, pr158077⟩
private theorem pr158113 : Nat.Prime 158113 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv61]) (by decide +kernel)
def pv158113 : PrimeValue := ⟨158113, pr158113⟩
private theorem pr158129 : Nat.Prime 158129 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv9883]) (by decide +kernel)
def pv158129 : PrimeValue := ⟨158129, pr158129⟩
private theorem pr158141 : Nat.Prime 158141 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7907]) (by decide +kernel)
def pv158141 : PrimeValue := ⟨158141, pr158141⟩
private theorem pr158143 : Nat.Prime 158143 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv26357]) (by decide +kernel)
def pv158143 : PrimeValue := ⟨158143, pr158143⟩
private theorem pr158161 : Nat.Prime 158161 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv659]) (by decide +kernel)
def pv158161 : PrimeValue := ⟨158161, pr158161⟩
private theorem pr158201 : Nat.Prime 158201 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv113]) (by decide +kernel)
def pv158201 : PrimeValue := ⟨158201, pr158201⟩
private theorem pr158209 : Nat.Prime 158209 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv103]) (by decide +kernel)
def pv158209 : PrimeValue := ⟨158209, pr158209⟩
private theorem pr158231 : Nat.Prime 158231 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv15823]) (by decide +kernel)
def pv158231 : PrimeValue := ⟨158231, pr158231⟩
private theorem pr158261 : Nat.Prime 158261 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv41,pv193]) (by decide +kernel)
def pv158261 : PrimeValue := ⟨158261, pr158261⟩
private theorem pr158293 : Nat.Prime 158293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4397]) (by decide +kernel)
def pv158293 : PrimeValue := ⟨158293, pr158293⟩
private theorem pr158303 : Nat.Prime 158303 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv79151]) (by decide +kernel)
def pv158303 : PrimeValue := ⟨158303, pr158303⟩
private theorem pr158329 : Nat.Prime 158329 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv733]) (by decide +kernel)
def pv158329 : PrimeValue := ⟨158329, pr158329⟩
private theorem pr158351 : Nat.Prime 158351 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv3167]) (by decide +kernel)
def pv158351 : PrimeValue := ⟨158351, pr158351⟩
private theorem pr158357 : Nat.Prime 158357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv59,pv61]) (by decide +kernel)
def pv158357 : PrimeValue := ⟨158357, pr158357⟩
private theorem pr158359 : Nat.Prime 158359 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv26393]) (by decide +kernel)
def pv158359 : PrimeValue := ⟨158359, pr158359⟩
private theorem pr158363 : Nat.Prime 158363 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79181]) (by decide +kernel)
def pv158363 : PrimeValue := ⟨158363, pr158363⟩
private theorem pr158371 : Nat.Prime 158371 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv5279]) (by decide +kernel)
def pv158371 : PrimeValue := ⟨158371, pr158371⟩
private theorem pr158393 : Nat.Prime 158393 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv1523]) (by decide +kernel)
def pv158393 : PrimeValue := ⟨158393, pr158393⟩
private theorem pr158407 : Nat.Prime 158407 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv1553]) (by decide +kernel)
def pv158407 : PrimeValue := ⟨158407, pr158407⟩
private theorem pr158419 : Nat.Prime 158419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv677]) (by decide +kernel)
def pv158419 : PrimeValue := ⟨158419, pr158419⟩
private theorem pr158429 : Nat.Prime 158429 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv39607]) (by decide +kernel)
def pv158429 : PrimeValue := ⟨158429, pr158429⟩
private theorem pr158443 : Nat.Prime 158443 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv26407]) (by decide +kernel)
def pv158443 : PrimeValue := ⟨158443, pr158443⟩
private theorem pr158449 : Nat.Prime 158449 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv3301]) (by decide +kernel)
def pv158449 : PrimeValue := ⟨158449, pr158449⟩
private theorem pr158551 : Nat.Prime 158551 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv151]) (by decide +kernel)
def pv158551 : PrimeValue := ⟨158551, pr158551⟩
private theorem pr158563 : Nat.Prime 158563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv383]) (by decide +kernel)
def pv158563 : PrimeValue := ⟨158563, pr158563⟩
private theorem pr158567 : Nat.Prime 158567 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv79283]) (by decide +kernel)
def pv158567 : PrimeValue := ⟨158567, pr158567⟩
private theorem pr158573 : Nat.Prime 158573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv1367]) (by decide +kernel)
def pv158573 : PrimeValue := ⟨158573, pr158573⟩
private theorem pr158581 : Nat.Prime 158581 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv881]) (by decide +kernel)
def pv158581 : PrimeValue := ⟨158581, pr158581⟩
private theorem pr158597 : Nat.Prime 158597 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv1279]) (by decide +kernel)
def pv158597 : PrimeValue := ⟨158597, pr158597⟩
private theorem pr158611 : Nat.Prime 158611 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv311]) (by decide +kernel)
def pv158611 : PrimeValue := ⟨158611, pr158611⟩
private theorem pr158617 : Nat.Prime 158617 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2203]) (by decide +kernel)
def pv158617 : PrimeValue := ⟨158617, pr158617⟩
private theorem pr158633 : Nat.Prime 158633 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv79,pv251]) (by decide +kernel)
def pv158633 : PrimeValue := ⟨158633, pr158633⟩
private theorem pr158647 : Nat.Prime 158647 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv137,pv193]) (by decide +kernel)
def pv158647 : PrimeValue := ⟨158647, pr158647⟩
private theorem pr158657 : Nat.Prime 158657 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv37,pv67]) (by decide +kernel)
def pv158657 : PrimeValue := ⟨158657, pr158657⟩
private theorem pr158663 : Nat.Prime 158663 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv1619]) (by decide +kernel)
def pv158663 : PrimeValue := ⟨158663, pr158663⟩
private theorem pr158699 : Nat.Prime 158699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79349]) (by decide +kernel)
def pv158699 : PrimeValue := ⟨158699, pr158699⟩
private theorem pr158731 : Nat.Prime 158731 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv13,pv37]) (by decide +kernel)
def pv158731 : PrimeValue := ⟨158731, pr158731⟩
private theorem pr158749 : Nat.Prime 158749 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13229]) (by decide +kernel)
def pv158749 : PrimeValue := ⟨158749, pr158749⟩
private theorem pr158759 : Nat.Prime 158759 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv79379]) (by decide +kernel)
def pv158759 : PrimeValue := ⟨158759, pr158759⟩
private theorem pr158761 : Nat.Prime 158761 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv158761 : PrimeValue := ⟨158761, pr158761⟩
private theorem pr158791 : Nat.Prime 158791 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv67,pv79]) (by decide +kernel)
def pv158791 : PrimeValue := ⟨158791, pr158791⟩
private theorem pr158803 : Nat.Prime 158803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv19,pv199]) (by decide +kernel)
def pv158803 : PrimeValue := ⟨158803, pr158803⟩
private theorem pr158843 : Nat.Prime 158843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv1847]) (by decide +kernel)
def pv158843 : PrimeValue := ⟨158843, pr158843⟩
private theorem pr158849 : Nat.Prime 158849 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv73]) (by decide +kernel)
def pv158849 : PrimeValue := ⟨158849, pr158849⟩
private theorem pr158863 : Nat.Prime 158863 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv11,pv29,pv83]) (by decide +kernel)
def pv158863 : PrimeValue := ⟨158863, pr158863⟩
private theorem pr158867 : Nat.Prime 158867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79433]) (by decide +kernel)
def pv158867 : PrimeValue := ⟨158867, pr158867⟩
private theorem pr158881 : Nat.Prime 158881 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv331]) (by decide +kernel)
def pv158881 : PrimeValue := ⟨158881, pr158881⟩
private theorem pr158909 : Nat.Prime 158909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv39727]) (by decide +kernel)
def pv158909 : PrimeValue := ⟨158909, pr158909⟩
private theorem pr158923 : Nat.Prime 158923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv109]) (by decide +kernel)
def pv158923 : PrimeValue := ⟨158923, pr158923⟩
private theorem pr158927 : Nat.Prime 158927 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv229,pv347]) (by decide +kernel)
def pv158927 : PrimeValue := ⟨158927, pr158927⟩
private theorem pr158941 : Nat.Prime 158941 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv883]) (by decide +kernel)
def pv158941 : PrimeValue := ⟨158941, pr158941⟩
private theorem pr158959 : Nat.Prime 158959 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv8831]) (by decide +kernel)
def pv158959 : PrimeValue := ⟨158959, pr158959⟩
private theorem pr158981 : Nat.Prime 158981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7949]) (by decide +kernel)
def pv158981 : PrimeValue := ⟨158981, pr158981⟩
private theorem pr158993 : Nat.Prime 158993 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv523]) (by decide +kernel)
def pv158993 : PrimeValue := ⟨158993, pr158993⟩
private theorem pr159013 : Nat.Prime 159013 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv7,pv631]) (by decide +kernel)
def pv159013 : PrimeValue := ⟨159013, pr159013⟩
private theorem pr159017 : Nat.Prime 159017 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv13,pv139]) (by decide +kernel)
def pv159017 : PrimeValue := ⟨159017, pr159017⟩
private theorem pr159023 : Nat.Prime 159023 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv23,pv3457]) (by decide +kernel)
def pv159023 : PrimeValue := ⟨159023, pr159023⟩
private theorem pr159059 : Nat.Prime 159059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv67,pv1187]) (by decide +kernel)
def pv159059 : PrimeValue := ⟨159059, pr159059⟩
private theorem pr159073 : Nat.Prime 159073 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv1657]) (by decide +kernel)
def pv159073 : PrimeValue := ⟨159073, pr159073⟩
private theorem pr159079 : Nat.Prime 159079 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv26513]) (by decide +kernel)
def pv159079 : PrimeValue := ⟨159079, pr159079⟩
private theorem pr159097 : Nat.Prime 159097 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv947]) (by decide +kernel)
def pv159097 : PrimeValue := ⟨159097, pr159097⟩
private theorem pr159113 : Nat.Prime 159113 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19889]) (by decide +kernel)
def pv159113 : PrimeValue := ⟨159113, pr159113⟩
private theorem pr159119 : Nat.Prime 159119 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv79559]) (by decide +kernel)
def pv159119 : PrimeValue := ⟨159119, pr159119⟩
private theorem pr159161 : Nat.Prime 159161 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv23,pv173]) (by decide +kernel)
def pv159161 : PrimeValue := ⟨159161, pr159161⟩
private theorem pr159167 : Nat.Prime 159167 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv11369]) (by decide +kernel)
def pv159167 : PrimeValue := ⟨159167, pr159167⟩
private theorem pr159169 : Nat.Prime 159169 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv829]) (by decide +kernel)
def pv159169 : PrimeValue := ⟨159169, pr159169⟩
private theorem pr159179 : Nat.Prime 159179 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79589]) (by decide +kernel)
def pv159179 : PrimeValue := ⟨159179, pr159179⟩
private theorem pr159191 : Nat.Prime 159191 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv15919]) (by decide +kernel)
def pv159191 : PrimeValue := ⟨159191, pr159191⟩
private theorem pr159193 : Nat.Prime 159193 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv67]) (by decide +kernel)
def pv159193 : PrimeValue := ⟨159193, pr159193⟩
private theorem pr159209 : Nat.Prime 159209 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv2843]) (by decide +kernel)
def pv159209 : PrimeValue := ⟨159209, pr159209⟩
private theorem pr159223 : Nat.Prime 159223 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv17,pv223]) (by decide +kernel)
def pv159223 : PrimeValue := ⟨159223, pr159223⟩
private theorem pr159227 : Nat.Prime 159227 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79613]) (by decide +kernel)
def pv159227 : PrimeValue := ⟨159227, pr159227⟩
private theorem pr159233 : Nat.Prime 159233 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv311]) (by decide +kernel)
def pv159233 : PrimeValue := ⟨159233, pr159233⟩
private theorem pr159287 : Nat.Prime 159287 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv73,pv1091]) (by decide +kernel)
def pv159287 : PrimeValue := ⟨159287, pr159287⟩
private theorem pr159293 : Nat.Prime 159293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv5689]) (by decide +kernel)
def pv159293 : PrimeValue := ⟨159293, pr159293⟩
private theorem pr159311 : Nat.Prime 159311 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv89,pv179]) (by decide +kernel)
def pv159311 : PrimeValue := ⟨159311, pr159311⟩
private theorem pr159319 : Nat.Prime 159319 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv53,pv167]) (by decide +kernel)
def pv159319 : PrimeValue := ⟨159319, pr159319⟩
private theorem pr159337 : Nat.Prime 159337 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2213]) (by decide +kernel)
def pv159337 : PrimeValue := ⟨159337, pr159337⟩
private theorem pr159347 : Nat.Prime 159347 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv7243]) (by decide +kernel)
def pv159347 : PrimeValue := ⟨159347, pr159347⟩
private theorem pr159349 : Nat.Prime 159349 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv271]) (by decide +kernel)
def pv159349 : PrimeValue := ⟨159349, pr159349⟩
private theorem pr159389 : Nat.Prime 159389 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv39847]) (by decide +kernel)
def pv159389 : PrimeValue := ⟨159389, pr159389⟩
private theorem pr159403 : Nat.Prime 159403 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv31,pv857]) (by decide +kernel)
def pv159403 : PrimeValue := ⟨159403, pr159403⟩
private theorem pr159407 : Nat.Prime 159407 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv6131]) (by decide +kernel)
def pv159407 : PrimeValue := ⟨159407, pr159407⟩
private theorem pr159421 : Nat.Prime 159421 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv2657]) (by decide +kernel)
def pv159421 : PrimeValue := ⟨159421, pr159421⟩
private theorem pr159431 : Nat.Prime 159431 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5,pv107,pv149]) (by decide +kernel)
def pv159431 : PrimeValue := ⟨159431, pr159431⟩
private theorem pr159457 : Nat.Prime 159457 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv151]) (by decide +kernel)
def pv159457 : PrimeValue := ⟨159457, pr159457⟩
private theorem pr159463 : Nat.Prime 159463 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv2953]) (by decide +kernel)
def pv159463 : PrimeValue := ⟨159463, pr159463⟩
private theorem pr159469 : Nat.Prime 159469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv97,pv137]) (by decide +kernel)
def pv159469 : PrimeValue := ⟨159469, pr159469⟩
private theorem pr159491 : Nat.Prime 159491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv41,pv389]) (by decide +kernel)
def pv159491 : PrimeValue := ⟨159491, pr159491⟩
private theorem pr159499 : Nat.Prime 159499 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv8861]) (by decide +kernel)
def pv159499 : PrimeValue := ⟨159499, pr159499⟩
private theorem pr159521 : Nat.Prime 159521 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv997]) (by decide +kernel)
def pv159521 : PrimeValue := ⟨159521, pr159521⟩
private theorem pr159539 : Nat.Prime 159539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79769]) (by decide +kernel)
def pv159539 : PrimeValue := ⟨159539, pr159539⟩
private theorem pr159541 : Nat.Prime 159541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv2659]) (by decide +kernel)
def pv159541 : PrimeValue := ⟨159541, pr159541⟩
private theorem pr159553 : Nat.Prime 159553 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv277]) (by decide +kernel)
def pv159553 : PrimeValue := ⟨159553, pr159553⟩
private theorem pr159563 : Nat.Prime 159563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv17,pv19]) (by decide +kernel)
def pv159563 : PrimeValue := ⟨159563, pr159563⟩
private theorem pr159569 : Nat.Prime 159569 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv9973]) (by decide +kernel)
def pv159569 : PrimeValue := ⟨159569, pr159569⟩
private theorem pr159571 : Nat.Prime 159571 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv197]) (by decide +kernel)
def pv159571 : PrimeValue := ⟨159571, pr159571⟩
private theorem pr159617 : Nat.Prime 159617 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv43]) (by decide +kernel)
def pv159617 : PrimeValue := ⟨159617, pr159617⟩
private theorem pr159623 : Nat.Prime 159623 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv79811]) (by decide +kernel)
def pv159623 : PrimeValue := ⟨159623, pr159623⟩
private theorem pr159629 : Nat.Prime 159629 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv5701]) (by decide +kernel)
def pv159629 : PrimeValue := ⟨159629, pr159629⟩
private theorem pr159631 : Nat.Prime 159631 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv17,pv313]) (by decide +kernel)
def pv159631 : PrimeValue := ⟨159631, pr159631⟩
private theorem pr159667 : Nat.Prime 159667 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv23,pv89]) (by decide +kernel)
def pv159667 : PrimeValue := ⟨159667, pr159667⟩
private theorem pr159671 : Nat.Prime 159671 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv2281]) (by decide +kernel)
def pv159671 : PrimeValue := ⟨159671, pr159671⟩
private theorem pr159673 : Nat.Prime 159673 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv6653]) (by decide +kernel)
def pv159673 : PrimeValue := ⟨159673, pr159673⟩
private theorem pr159697 : Nat.Prime 159697 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1109]) (by decide +kernel)
def pv159697 : PrimeValue := ⟨159697, pr159697⟩
private theorem pr159701 : Nat.Prime 159701 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1597]) (by decide +kernel)
def pv159701 : PrimeValue := ⟨159701, pr159701⟩
private theorem pr159707 : Nat.Prime 159707 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv1699]) (by decide +kernel)
def pv159707 : PrimeValue := ⟨159707, pr159707⟩
private theorem pr159721 : Nat.Prime 159721 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv159721 : PrimeValue := ⟨159721, pr159721⟩
private theorem pr159737 : Nat.Prime 159737 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv41,pv487]) (by decide +kernel)
def pv159737 : PrimeValue := ⟨159737, pr159737⟩
private theorem pr159739 : Nat.Prime 159739 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv79,pv337]) (by decide +kernel)
def pv159739 : PrimeValue := ⟨159739, pr159739⟩
private theorem pr159763 : Nat.Prime 159763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv26627]) (by decide +kernel)
def pv159763 : PrimeValue := ⟨159763, pr159763⟩
private theorem pr159773 : Nat.Prime 159773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv59,pv677]) (by decide +kernel)
def pv159773 : PrimeValue := ⟨159773, pr159773⟩
private theorem pr159779 : Nat.Prime 159779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv79889]) (by decide +kernel)
def pv159779 : PrimeValue := ⟨159779, pr159779⟩
private theorem pr159791 : Nat.Prime 159791 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv19,pv29]) (by decide +kernel)
def pv159791 : PrimeValue := ⟨159791, pr159791⟩
private theorem pr159793 : Nat.Prime 159793 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv3329]) (by decide +kernel)
def pv159793 : PrimeValue := ⟨159793, pr159793⟩
private theorem pr159811 : Nat.Prime 159811 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv761]) (by decide +kernel)
def pv159811 : PrimeValue := ⟨159811, pr159811⟩
private theorem pr159839 : Nat.Prime 159839 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv233]) (by decide +kernel)
def pv159839 : PrimeValue := ⟨159839, pr159839⟩
private theorem pr159853 : Nat.Prime 159853 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv7,pv11,pv173]) (by decide +kernel)
def pv159853 : PrimeValue := ⟨159853, pr159853⟩
private theorem pr159857 : Nat.Prime 159857 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv97,pv103]) (by decide +kernel)
def pv159857 : PrimeValue := ⟨159857, pr159857⟩
private theorem pr159869 : Nat.Prime 159869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv2351]) (by decide +kernel)
def pv159869 : PrimeValue := ⟨159869, pr159869⟩
private theorem pr159871 : Nat.Prime 159871 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv73]) (by decide +kernel)
def pv159871 : PrimeValue := ⟨159871, pr159871⟩
private theorem pr159899 : Nat.Prime 159899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv2579]) (by decide +kernel)
def pv159899 : PrimeValue := ⟨159899, pr159899⟩
private theorem pr159911 : Nat.Prime 159911 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv15991]) (by decide +kernel)
def pv159911 : PrimeValue := ⟨159911, pr159911⟩
private theorem pr159937 : Nat.Prime 159937 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv17]) (by decide +kernel)
def pv159937 : PrimeValue := ⟨159937, pr159937⟩
private theorem pr159977 : Nat.Prime 159977 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19997]) (by decide +kernel)
def pv159977 : PrimeValue := ⟨159977, pr159977⟩
private theorem pr160001 : Nat.Prime 160001 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5]) (by decide +kernel)
def pv160001 : PrimeValue := ⟨160001, pr160001⟩
private theorem pr160019 : Nat.Prime 160019 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv4211]) (by decide +kernel)
def pv160019 : PrimeValue := ⟨160019, pr160019⟩
private theorem pr160031 : Nat.Prime 160031 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv13,pv1231]) (by decide +kernel)
def pv160031 : PrimeValue := ⟨160031, pr160031⟩
private theorem pr160033 : Nat.Prime 160033 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv1667]) (by decide +kernel)
def pv160033 : PrimeValue := ⟨160033, pr160033⟩
private theorem pr160049 : Nat.Prime 160049 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv1429]) (by decide +kernel)
def pv160049 : PrimeValue := ⟨160049, pr160049⟩
private theorem pr160079 : Nat.Prime 160079 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv80039]) (by decide +kernel)
def pv160079 : PrimeValue := ⟨160079, pr160079⟩
private theorem pr160081 : Nat.Prime 160081 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv5,pv23,pv29]) (by decide +kernel)
def pv160081 : PrimeValue := ⟨160081, pr160081⟩
private theorem pr160087 : Nat.Prime 160087 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv26681]) (by decide +kernel)
def pv160087 : PrimeValue := ⟨160087, pr160087⟩
private theorem pr160091 : Nat.Prime 160091 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv2287]) (by decide +kernel)
def pv160091 : PrimeValue := ⟨160091, pr160091⟩
private theorem pr160117 : Nat.Prime 160117 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv1213]) (by decide +kernel)
def pv160117 : PrimeValue := ⟨160117, pr160117⟩
private theorem pr160141 : Nat.Prime 160141 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv157]) (by decide +kernel)
def pv160141 : PrimeValue := ⟨160141, pr160141⟩
private theorem pr160159 : Nat.Prime 160159 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv26693]) (by decide +kernel)
def pv160159 : PrimeValue := ⟨160159, pr160159⟩
private theorem pr160169 : Nat.Prime 160169 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv20021]) (by decide +kernel)
def pv160169 : PrimeValue := ⟨160169, pr160169⟩
private theorem pr160183 : Nat.Prime 160183 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv809]) (by decide +kernel)
def pv160183 : PrimeValue := ⟨160183, pr160183⟩
private theorem pr160201 : Nat.Prime 160201 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv89]) (by decide +kernel)
def pv160201 : PrimeValue := ⟨160201, pr160201⟩
private theorem pr160207 : Nat.Prime 160207 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv26701]) (by decide +kernel)
def pv160207 : PrimeValue := ⟨160207, pr160207⟩
private theorem pr160231 : Nat.Prime 160231 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv109]) (by decide +kernel)
def pv160231 : PrimeValue := ⟨160231, pr160231⟩
private theorem pr160243 : Nat.Prime 160243 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv17,pv1571]) (by decide +kernel)
def pv160243 : PrimeValue := ⟨160243, pr160243⟩
private theorem pr160253 : Nat.Prime 160253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv40063]) (by decide +kernel)
def pv160253 : PrimeValue := ⟨160253, pr160253⟩
private theorem pr160309 : Nat.Prime 160309 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv61,pv73]) (by decide +kernel)
def pv160309 : PrimeValue := ⟨160309, pr160309⟩
private theorem pr160313 : Nat.Prime 160313 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv691]) (by decide +kernel)
def pv160313 : PrimeValue := ⟨160313, pr160313⟩
private theorem pr160343 : Nat.Prime 160343 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv13,pv881]) (by decide +kernel)
def pv160343 : PrimeValue := ⟨160343, pr160343⟩
private theorem pr160357 : Nat.Prime 160357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv23,pv83]) (by decide +kernel)
def pv160357 : PrimeValue := ⟨160357, pr160357⟩
private theorem pr160367 : Nat.Prime 160367 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv181,pv443]) (by decide +kernel)
def pv160367 : PrimeValue := ⟨160367, pr160367⟩
private theorem pr160373 : Nat.Prime 160373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv40093]) (by decide +kernel)
def pv160373 : PrimeValue := ⟨160373, pr160373⟩
private theorem pr160387 : Nat.Prime 160387 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv26731]) (by decide +kernel)
def pv160387 : PrimeValue := ⟨160387, pr160387⟩
private theorem pr160403 : Nat.Prime 160403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv23,pv317]) (by decide +kernel)
def pv160403 : PrimeValue := ⟨160403, pr160403⟩
private theorem pr160409 : Nat.Prime 160409 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv20051]) (by decide +kernel)
def pv160409 : PrimeValue := ⟨160409, pr160409⟩
private theorem pr160423 : Nat.Prime 160423 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv26737]) (by decide +kernel)
def pv160423 : PrimeValue := ⟨160423, pr160423⟩
private theorem pr160441 : Nat.Prime 160441 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv191]) (by decide +kernel)
def pv160441 : PrimeValue := ⟨160441, pr160441⟩
private theorem pr160453 : Nat.Prime 160453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4457]) (by decide +kernel)
def pv160453 : PrimeValue := ⟨160453, pr160453⟩
private theorem pr160481 : Nat.Prime 160481 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17,pv59]) (by decide +kernel)
def pv160481 : PrimeValue := ⟨160481, pr160481⟩
private theorem pr160483 : Nat.Prime 160483 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv3821]) (by decide +kernel)
def pv160483 : PrimeValue := ⟨160483, pr160483⟩
private theorem pr160507 : Nat.Prime 160507 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv37,pv241]) (by decide +kernel)
def pv160507 : PrimeValue := ⟨160507, pr160507⟩
private theorem pr160541 : Nat.Prime 160541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv23,pv349]) (by decide +kernel)
def pv160541 : PrimeValue := ⟨160541, pr160541⟩
private theorem pr160553 : Nat.Prime 160553 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv47,pv61]) (by decide +kernel)
def pv160553 : PrimeValue := ⟨160553, pr160553⟩
private theorem pr160579 : Nat.Prime 160579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv811]) (by decide +kernel)
def pv160579 : PrimeValue := ⟨160579, pr160579⟩
private theorem pr160583 : Nat.Prime 160583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv4723]) (by decide +kernel)
def pv160583 : PrimeValue := ⟨160583, pr160583⟩
private theorem pr160603 : Nat.Prime 160603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv29,pv71]) (by decide +kernel)
def pv160603 : PrimeValue := ⟨160603, pr160603⟩
private theorem pr160619 : Nat.Prime 160619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv80309]) (by decide +kernel)
def pv160619 : PrimeValue := ⟨160619, pr160619⟩
private theorem pr160621 : Nat.Prime 160621 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv2677]) (by decide +kernel)
def pv160621 : PrimeValue := ⟨160621, pr160621⟩
private theorem pr160627 : Nat.Prime 160627 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv1409]) (by decide +kernel)
def pv160627 : PrimeValue := ⟨160627, pr160627⟩
private theorem pr160637 : Nat.Prime 160637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv5737]) (by decide +kernel)
def pv160637 : PrimeValue := ⟨160637, pr160637⟩
private theorem pr160639 : Nat.Prime 160639 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv41,pv653]) (by decide +kernel)
def pv160639 : PrimeValue := ⟨160639, pr160639⟩
private theorem pr160649 : Nat.Prime 160649 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv43,pv467]) (by decide +kernel)
def pv160649 : PrimeValue := ⟨160649, pr160649⟩
private theorem pr160651 : Nat.Prime 160651 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv17]) (by decide +kernel)
def pv160651 : PrimeValue := ⟨160651, pr160651⟩
private theorem pr160663 : Nat.Prime 160663 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv26777]) (by decide +kernel)
def pv160663 : PrimeValue := ⟨160663, pr160663⟩
private theorem pr160669 : Nat.Prime 160669 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4463]) (by decide +kernel)
def pv160669 : PrimeValue := ⟨160669, pr160669⟩
private theorem pr160681 : Nat.Prime 160681 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv13,pv103]) (by decide +kernel)
def pv160681 : PrimeValue := ⟨160681, pr160681⟩
private theorem pr160687 : Nat.Prime 160687 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv79,pv113]) (by decide +kernel)
def pv160687 : PrimeValue := ⟨160687, pr160687⟩
private theorem pr160697 : Nat.Prime 160697 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv53,pv379]) (by decide +kernel)
def pv160697 : PrimeValue := ⟨160697, pr160697⟩
private theorem pr160709 : Nat.Prime 160709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv40177]) (by decide +kernel)
def pv160709 : PrimeValue := ⟨160709, pr160709⟩
private theorem pr160711 : Nat.Prime 160711 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv487]) (by decide +kernel)
def pv160711 : PrimeValue := ⟨160711, pr160711⟩
private theorem pr160723 : Nat.Prime 160723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv8929]) (by decide +kernel)
def pv160723 : PrimeValue := ⟨160723, pr160723⟩
private theorem pr160739 : Nat.Prime 160739 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv80369]) (by decide +kernel)
def pv160739 : PrimeValue := ⟨160739, pr160739⟩
private theorem pr160751 : Nat.Prime 160751 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv643]) (by decide +kernel)
def pv160751 : PrimeValue := ⟨160751, pr160751⟩
private theorem pr160753 : Nat.Prime 160753 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv197]) (by decide +kernel)
def pv160753 : PrimeValue := ⟨160753, pr160753⟩
private theorem pr160757 : Nat.Prime 160757 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv40189]) (by decide +kernel)
def pv160757 : PrimeValue := ⟨160757, pr160757⟩
private theorem pr160813 : Nat.Prime 160813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1489]) (by decide +kernel)
def pv160813 : PrimeValue := ⟨160813, pr160813⟩
private theorem pr160817 : Nat.Prime 160817 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv19,pv23]) (by decide +kernel)
def pv160817 : PrimeValue := ⟨160817, pr160817⟩
private theorem pr160829 : Nat.Prime 160829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv1297]) (by decide +kernel)
def pv160829 : PrimeValue := ⟨160829, pr160829⟩
private theorem pr160841 : Nat.Prime 160841 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv4021]) (by decide +kernel)
def pv160841 : PrimeValue := ⟨160841, pr160841⟩
private theorem pr160861 : Nat.Prime 160861 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv383]) (by decide +kernel)
def pv160861 : PrimeValue := ⟨160861, pr160861⟩
private theorem pr160903 : Nat.Prime 160903 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv1277]) (by decide +kernel)
def pv160903 : PrimeValue := ⟨160903, pr160903⟩
private theorem pr160907 : Nat.Prime 160907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv43,pv1871]) (by decide +kernel)
def pv160907 : PrimeValue := ⟨160907, pr160907⟩
private theorem pr160967 : Nat.Prime 160967 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv41,pv151]) (by decide +kernel)
def pv160967 : PrimeValue := ⟨160967, pr160967⟩
private theorem pr160969 : Nat.Prime 160969 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv19,pv353]) (by decide +kernel)
def pv160969 : PrimeValue := ⟨160969, pr160969⟩
private theorem pr160981 : Nat.Prime 160981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv2683]) (by decide +kernel)
def pv160981 : PrimeValue := ⟨160981, pr160981⟩
private theorem pr160997 : Nat.Prime 160997 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv3659]) (by decide +kernel)
def pv160997 : PrimeValue := ⟨160997, pr160997⟩
private theorem pr161009 : Nat.Prime 161009 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv29,pv347]) (by decide +kernel)
def pv161009 : PrimeValue := ⟨161009, pr161009⟩
private theorem pr161033 : Nat.Prime 161033 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv20129]) (by decide +kernel)
def pv161033 : PrimeValue := ⟨161033, pr161033⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
