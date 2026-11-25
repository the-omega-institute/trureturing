/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table056
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table056.pv161039
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table007
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table011
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table012
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table031
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table032

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr161039 : PrimeCertificate 161039 :=
  certifyPrime (q := pv7) (ls := [pv2,pv73,pv1103]) (by decide +kernel)
def pv161039 : PrimeValue := ⟨161039, pr161039⟩
private theorem pr161047 : PrimeCertificate 161047 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv389]) (by decide +kernel)
def pv161047 : PrimeValue := ⟨161047, pr161047⟩
private theorem pr161053 : PrimeCertificate 161053 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13421]) (by decide +kernel)
def pv161053 : PrimeValue := ⟨161053, pr161053⟩
private theorem pr161059 : PrimeCertificate 161059 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv17,pv1579]) (by decide +kernel)
def pv161059 : PrimeValue := ⟨161059, pr161059⟩
private theorem pr161071 : PrimeCertificate 161071 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv13,pv59]) (by decide +kernel)
def pv161071 : PrimeValue := ⟨161071, pr161071⟩
private theorem pr161087 : PrimeCertificate 161087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv239,pv337]) (by decide +kernel)
def pv161087 : PrimeValue := ⟨161087, pr161087⟩
private theorem pr161093 : PrimeCertificate 161093 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv23,pv103]) (by decide +kernel)
def pv161093 : PrimeValue := ⟨161093, pr161093⟩
private theorem pr161123 : PrimeCertificate 161123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv6197]) (by decide +kernel)
def pv161123 : PrimeValue := ⟨161123, pr161123⟩
private theorem pr161137 : PrimeCertificate 161137 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv373]) (by decide +kernel)
def pv161137 : PrimeValue := ⟨161137, pr161137⟩
private theorem pr161141 : PrimeCertificate 161141 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv1151]) (by decide +kernel)
def pv161141 : PrimeValue := ⟨161141, pr161141⟩
private theorem pr161149 : PrimeCertificate 161149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv1033]) (by decide +kernel)
def pv161149 : PrimeValue := ⟨161149, pr161149⟩
private theorem pr161159 : PrimeCertificate 161159 :=
  certifyPrime (q := pv11) (ls := [pv2,pv19,pv4241]) (by decide +kernel)
def pv161159 : PrimeValue := ⟨161159, pr161159⟩
private theorem pr161167 : PrimeCertificate 161167 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv26861]) (by decide +kernel)
def pv161167 : PrimeValue := ⟨161167, pr161167⟩
private theorem pr161201 : PrimeCertificate 161201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv31]) (by decide +kernel)
def pv161201 : PrimeValue := ⟨161201, pr161201⟩
private theorem pr161221 : PrimeCertificate 161221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv2687]) (by decide +kernel)
def pv161221 : PrimeValue := ⟨161221, pr161221⟩
private theorem pr161233 : PrimeCertificate 161233 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3359]) (by decide +kernel)
def pv161233 : PrimeValue := ⟨161233, pr161233⟩
private theorem pr161237 : PrimeCertificate 161237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv173,pv233]) (by decide +kernel)
def pv161237 : PrimeValue := ⟨161237, pr161237⟩
private theorem pr161281 : PrimeCertificate 161281 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv161281 : PrimeValue := ⟨161281, pr161281⟩
private theorem pr161303 : PrimeCertificate 161303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv80651]) (by decide +kernel)
def pv161303 : PrimeValue := ⟨161303, pr161303⟩
private theorem pr161309 : PrimeCertificate 161309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv823]) (by decide +kernel)
def pv161309 : PrimeValue := ⟨161309, pr161309⟩
private theorem pr161333 : PrimeCertificate 161333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv761]) (by decide +kernel)
def pv161333 : PrimeValue := ⟨161333, pr161333⟩
private theorem pr161339 : PrimeCertificate 161339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv80669]) (by decide +kernel)
def pv161339 : PrimeValue := ⟨161339, pr161339⟩
private theorem pr161341 : PrimeCertificate 161341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv2689]) (by decide +kernel)
def pv161341 : PrimeValue := ⟨161341, pr161341⟩
private theorem pr161363 : PrimeCertificate 161363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv80681]) (by decide +kernel)
def pv161363 : PrimeValue := ⟨161363, pr161363⟩
private theorem pr161377 : PrimeCertificate 161377 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv41]) (by decide +kernel)
def pv161377 : PrimeValue := ⟨161377, pr161377⟩
private theorem pr161407 : PrimeCertificate 161407 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv61]) (by decide +kernel)
def pv161407 : PrimeValue := ⟨161407, pr161407⟩
private theorem pr161411 : PrimeCertificate 161411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv16141]) (by decide +kernel)
def pv161411 : PrimeValue := ⟨161411, pr161411⟩
private theorem pr161453 : PrimeCertificate 161453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv181,pv223]) (by decide +kernel)
def pv161453 : PrimeValue := ⟨161453, pr161453⟩
private theorem pr161459 : PrimeCertificate 161459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv41,pv179]) (by decide +kernel)
def pv161459 : PrimeValue := ⟨161459, pr161459⟩
private theorem pr161471 : PrimeCertificate 161471 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv67,pv241]) (by decide +kernel)
def pv161471 : PrimeValue := ⟨161471, pr161471⟩
private theorem pr161503 : PrimeCertificate 161503 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv2447]) (by decide +kernel)
def pv161503 : PrimeValue := ⟨161503, pr161503⟩
private theorem pr161507 : PrimeCertificate 161507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv3511]) (by decide +kernel)
def pv161507 : PrimeValue := ⟨161507, pr161507⟩
private theorem pr161521 : PrimeCertificate 161521 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv673]) (by decide +kernel)
def pv161521 : PrimeValue := ⟨161521, pr161521⟩
private theorem pr161527 : PrimeCertificate 161527 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv26921]) (by decide +kernel)
def pv161527 : PrimeValue := ⟨161527, pr161527⟩
private theorem pr161531 : PrimeCertificate 161531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29,pv557]) (by decide +kernel)
def pv161531 : PrimeValue := ⟨161531, pr161531⟩
private theorem pr161543 : PrimeCertificate 161543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv37,pv59]) (by decide +kernel)
def pv161543 : PrimeValue := ⟨161543, pr161543⟩
private theorem pr161561 : PrimeCertificate 161561 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv577]) (by decide +kernel)
def pv161561 : PrimeValue := ⟨161561, pr161561⟩
private theorem pr161563 : PrimeCertificate 161563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv26927]) (by decide +kernel)
def pv161563 : PrimeValue := ⟨161563, pr161563⟩
private theorem pr161569 : PrimeCertificate 161569 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv17]) (by decide +kernel)
def pv161569 : PrimeValue := ⟨161569, pr161569⟩
private theorem pr161591 : PrimeCertificate 161591 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv13,pv113]) (by decide +kernel)
def pv161591 : PrimeValue := ⟨161591, pr161591⟩
private theorem pr161599 : PrimeCertificate 161599 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv23,pv1171]) (by decide +kernel)
def pv161599 : PrimeValue := ⟨161599, pr161599⟩
private theorem pr161611 : PrimeCertificate 161611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv5387]) (by decide +kernel)
def pv161611 : PrimeValue := ⟨161611, pr161611⟩
private theorem pr161627 : PrimeCertificate 161627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv211,pv383]) (by decide +kernel)
def pv161627 : PrimeValue := ⟨161627, pr161627⟩
private theorem pr161659 : PrimeCertificate 161659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1283]) (by decide +kernel)
def pv161659 : PrimeValue := ⟨161659, pr161659⟩
private theorem pr161717 : PrimeCertificate 161717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv40429]) (by decide +kernel)
def pv161717 : PrimeValue := ⟨161717, pr161717⟩
private theorem pr161729 : PrimeCertificate 161729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv19]) (by decide +kernel)
def pv161729 : PrimeValue := ⟨161729, pr161729⟩
private theorem pr161731 : PrimeCertificate 161731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv599]) (by decide +kernel)
def pv161731 : PrimeValue := ⟨161731, pr161731⟩
private theorem pr161741 : PrimeCertificate 161741 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv8087]) (by decide +kernel)
def pv161741 : PrimeValue := ⟨161741, pr161741⟩
private theorem pr161743 : PrimeCertificate 161743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv3851]) (by decide +kernel)
def pv161743 : PrimeValue := ⟨161743, pr161743⟩
private theorem pr161753 : PrimeCertificate 161753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv20219]) (by decide +kernel)
def pv161753 : PrimeValue := ⟨161753, pr161753⟩
private theorem pr161761 : PrimeCertificate 161761 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv337]) (by decide +kernel)
def pv161761 : PrimeValue := ⟨161761, pr161761⟩
private theorem pr161771 : PrimeCertificate 161771 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv7,pv2311]) (by decide +kernel)
def pv161771 : PrimeValue := ⟨161771, pr161771⟩
private theorem pr161779 : PrimeCertificate 161779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv59,pv457]) (by decide +kernel)
def pv161779 : PrimeValue := ⟨161779, pr161779⟩
private theorem pr161783 : PrimeCertificate 161783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv3517]) (by decide +kernel)
def pv161783 : PrimeValue := ⟨161783, pr161783⟩
private theorem pr161807 : PrimeCertificate 161807 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv4759]) (by decide +kernel)
def pv161807 : PrimeValue := ⟨161807, pr161807⟩
private theorem pr161831 : PrimeCertificate 161831 :=
  certifyPrime (q := pv53) (ls := [pv2,pv5,pv16183]) (by decide +kernel)
def pv161831 : PrimeValue := ⟨161831, pr161831⟩
private theorem pr161839 : PrimeCertificate 161839 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37]) (by decide +kernel)
def pv161839 : PrimeValue := ⟨161839, pr161839⟩
private theorem pr161869 : PrimeCertificate 161869 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv41,pv47]) (by decide +kernel)
def pv161869 : PrimeValue := ⟨161869, pr161869⟩
private theorem pr161873 : PrimeCertificate 161873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv67,pv151]) (by decide +kernel)
def pv161873 : PrimeValue := ⟨161873, pr161873⟩
private theorem pr161879 : PrimeCertificate 161879 :=
  certifyPrime (q := pv7) (ls := [pv2,pv29,pv2791]) (by decide +kernel)
def pv161879 : PrimeValue := ⟨161879, pr161879⟩
private theorem pr161881 : PrimeCertificate 161881 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv19,pv71]) (by decide +kernel)
def pv161881 : PrimeValue := ⟨161881, pr161881⟩
private theorem pr161921 : PrimeCertificate 161921 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv23]) (by decide +kernel)
def pv161921 : PrimeValue := ⟨161921, pr161921⟩
private theorem pr161923 : PrimeCertificate 161923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv26987]) (by decide +kernel)
def pv161923 : PrimeValue := ⟨161923, pr161923⟩
private theorem pr161947 : PrimeCertificate 161947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv2999]) (by decide +kernel)
def pv161947 : PrimeValue := ⟨161947, pr161947⟩
private theorem pr161957 : PrimeCertificate 161957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv2131]) (by decide +kernel)
def pv161957 : PrimeValue := ⟨161957, pr161957⟩
private theorem pr161969 : PrimeCertificate 161969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv53,pv191]) (by decide +kernel)
def pv161969 : PrimeValue := ⟨161969, pr161969⟩
private theorem pr161971 : PrimeCertificate 161971 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv5399]) (by decide +kernel)
def pv161971 : PrimeValue := ⟨161971, pr161971⟩
private theorem pr161977 : PrimeCertificate 161977 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv397]) (by decide +kernel)
def pv161977 : PrimeValue := ⟨161977, pr161977⟩
private theorem pr161983 : PrimeCertificate 161983 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv8999]) (by decide +kernel)
def pv161983 : PrimeValue := ⟨161983, pr161983⟩
private theorem pr161999 : PrimeCertificate 161999 :=
  certifyPrime (q := pv13) (ls := [pv2,pv107,pv757]) (by decide +kernel)
def pv161999 : PrimeValue := ⟨161999, pr161999⟩
private theorem pr162007 : PrimeCertificate 162007 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv31,pv67]) (by decide +kernel)
def pv162007 : PrimeValue := ⟨162007, pr162007⟩
private theorem pr162011 : PrimeCertificate 162011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv953]) (by decide +kernel)
def pv162011 : PrimeValue := ⟨162011, pr162011⟩
private theorem pr162017 : PrimeCertificate 162017 :=
  certifyPrime (q := pv3) (ls := [pv2,pv61,pv83]) (by decide +kernel)
def pv162017 : PrimeValue := ⟨162017, pr162017⟩
private theorem pr162053 : PrimeCertificate 162053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv29,pv127]) (by decide +kernel)
def pv162053 : PrimeValue := ⟨162053, pr162053⟩
private theorem pr162059 : PrimeCertificate 162059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv23,pv271]) (by decide +kernel)
def pv162059 : PrimeValue := ⟨162059, pr162059⟩
private theorem pr162079 : PrimeCertificate 162079 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv17,pv227]) (by decide +kernel)
def pv162079 : PrimeValue := ⟨162079, pr162079⟩
private theorem pr162091 : PrimeCertificate 162091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1801]) (by decide +kernel)
def pv162091 : PrimeValue := ⟨162091, pr162091⟩
private theorem pr162109 : PrimeCertificate 162109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv79]) (by decide +kernel)
def pv162109 : PrimeValue := ⟨162109, pr162109⟩
private theorem pr162119 : PrimeCertificate 162119 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv7369]) (by decide +kernel)
def pv162119 : PrimeValue := ⟨162119, pr162119⟩
private theorem pr162143 : PrimeCertificate 162143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv81071]) (by decide +kernel)
def pv162143 : PrimeValue := ⟨162143, pr162143⟩
private theorem pr162209 : PrimeCertificate 162209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv137]) (by decide +kernel)
def pv162209 : PrimeValue := ⟨162209, pr162209⟩
private theorem pr162229 : PrimeCertificate 162229 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv1229]) (by decide +kernel)
def pv162229 : PrimeValue := ⟨162229, pr162229⟩
private theorem pr162251 : PrimeCertificate 162251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv59]) (by decide +kernel)
def pv162251 : PrimeValue := ⟨162251, pr162251⟩
private theorem pr162257 : PrimeCertificate 162257 :=
  certifyPrime (q := pv3) (ls := [pv2,pv10141]) (by decide +kernel)
def pv162257 : PrimeValue := ⟨162257, pr162257⟩
private theorem pr162263 : PrimeCertificate 162263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv81131]) (by decide +kernel)
def pv162263 : PrimeValue := ⟨162263, pr162263⟩
private theorem pr162269 : PrimeCertificate 162269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv113,pv359]) (by decide +kernel)
def pv162269 : PrimeValue := ⟨162269, pr162269⟩
private theorem pr162277 : PrimeCertificate 162277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13523]) (by decide +kernel)
def pv162277 : PrimeValue := ⟨162277, pr162277⟩
private theorem pr162287 : PrimeCertificate 162287 :=
  certifyPrime (q := pv5) (ls := [pv2,pv53,pv1531]) (by decide +kernel)
def pv162287 : PrimeValue := ⟨162287, pr162287⟩
private theorem pr162289 : PrimeCertificate 162289 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv23]) (by decide +kernel)
def pv162289 : PrimeValue := ⟨162289, pr162289⟩
private theorem pr162293 : PrimeCertificate 162293 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv3121]) (by decide +kernel)
def pv162293 : PrimeValue := ⟨162293, pr162293⟩
private theorem pr162343 : PrimeCertificate 162343 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv311]) (by decide +kernel)
def pv162343 : PrimeValue := ⟨162343, pr162343⟩
private theorem pr162389 : PrimeCertificate 162389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv40597]) (by decide +kernel)
def pv162389 : PrimeValue := ⟨162389, pr162389⟩
private theorem pr162413 : PrimeCertificate 162413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv2137]) (by decide +kernel)
def pv162413 : PrimeValue := ⟨162413, pr162413⟩
private theorem pr162419 : PrimeCertificate 162419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv281]) (by decide +kernel)
def pv162419 : PrimeValue := ⟨162419, pr162419⟩
private theorem pr162439 : PrimeCertificate 162439 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv27073]) (by decide +kernel)
def pv162439 : PrimeValue := ⟨162439, pr162439⟩
private theorem pr162451 : PrimeCertificate 162451 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv162451 : PrimeValue := ⟨162451, pr162451⟩
private theorem pr162457 : PrimeCertificate 162457 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv7,pv967]) (by decide +kernel)
def pv162457 : PrimeValue := ⟨162457, pr162457⟩
private theorem pr162473 : PrimeCertificate 162473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv883]) (by decide +kernel)
def pv162473 : PrimeValue := ⟨162473, pr162473⟩
private theorem pr162493 : PrimeCertificate 162493 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv1231]) (by decide +kernel)
def pv162493 : PrimeValue := ⟨162493, pr162493⟩
private theorem pr162499 : PrimeCertificate 162499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv53,pv73]) (by decide +kernel)
def pv162499 : PrimeValue := ⟨162499, pr162499⟩
private theorem pr162517 : PrimeCertificate 162517 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29,pv467]) (by decide +kernel)
def pv162517 : PrimeValue := ⟨162517, pr162517⟩
private theorem pr162529 : PrimeCertificate 162529 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1693]) (by decide +kernel)
def pv162529 : PrimeValue := ⟨162529, pr162529⟩
private theorem pr162553 : PrimeCertificate 162553 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv13,pv521]) (by decide +kernel)
def pv162553 : PrimeValue := ⟨162553, pr162553⟩
private theorem pr162557 : PrimeCertificate 162557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv40639]) (by decide +kernel)
def pv162557 : PrimeValue := ⟨162557, pr162557⟩
private theorem pr162563 : PrimeCertificate 162563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv81281]) (by decide +kernel)
def pv162563 : PrimeValue := ⟨162563, pr162563⟩
private theorem pr162577 : PrimeCertificate 162577 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1129]) (by decide +kernel)
def pv162577 : PrimeValue := ⟨162577, pr162577⟩
private theorem pr162593 : PrimeCertificate 162593 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5081]) (by decide +kernel)
def pv162593 : PrimeValue := ⟨162593, pr162593⟩
private theorem pr162601 : PrimeCertificate 162601 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv271]) (by decide +kernel)
def pv162601 : PrimeValue := ⟨162601, pr162601⟩
private theorem pr162623 : PrimeCertificate 162623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv4783]) (by decide +kernel)
def pv162623 : PrimeValue := ⟨162623, pr162623⟩
private theorem pr162629 : PrimeCertificate 162629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv109,pv373]) (by decide +kernel)
def pv162629 : PrimeValue := ⟨162629, pr162629⟩
private theorem pr162641 : PrimeCertificate 162641 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv19,pv107]) (by decide +kernel)
def pv162641 : PrimeValue := ⟨162641, pr162641⟩
private theorem pr162671 : PrimeCertificate 162671 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv16267]) (by decide +kernel)
def pv162671 : PrimeValue := ⟨162671, pr162671⟩
private theorem pr162691 : PrimeCertificate 162691 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv17,pv29]) (by decide +kernel)
def pv162691 : PrimeValue := ⟨162691, pr162691⟩
private theorem pr162703 : PrimeCertificate 162703 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23,pv131]) (by decide +kernel)
def pv162703 : PrimeValue := ⟨162703, pr162703⟩
private theorem pr162713 : PrimeCertificate 162713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv43]) (by decide +kernel)
def pv162713 : PrimeValue := ⟨162713, pr162713⟩
private theorem pr162731 : PrimeCertificate 162731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv16273]) (by decide +kernel)
def pv162731 : PrimeValue := ⟨162731, pr162731⟩
private theorem pr162749 : PrimeCertificate 162749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv29,pv61]) (by decide +kernel)
def pv162749 : PrimeValue := ⟨162749, pr162749⟩
private theorem pr162751 : PrimeCertificate 162751 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv31]) (by decide +kernel)
def pv162751 : PrimeValue := ⟨162751, pr162751⟩
private theorem pr162779 : PrimeCertificate 162779 :=
  certifyPrime (q := pv11) (ls := [pv2,pv7,pv11,pv151]) (by decide +kernel)
def pv162779 : PrimeValue := ⟨162779, pr162779⟩
private theorem pr162787 : PrimeCertificate 162787 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv2087]) (by decide +kernel)
def pv162787 : PrimeValue := ⟨162787, pr162787⟩
private theorem pr162791 : PrimeCertificate 162791 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv73,pv223]) (by decide +kernel)
def pv162791 : PrimeValue := ⟨162791, pr162791⟩
private theorem pr162821 : PrimeCertificate 162821 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv1163]) (by decide +kernel)
def pv162821 : PrimeValue := ⟨162821, pr162821⟩
private theorem pr162823 : PrimeCertificate 162823 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv2467]) (by decide +kernel)
def pv162823 : PrimeValue := ⟨162823, pr162823⟩
private theorem pr162829 : PrimeCertificate 162829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv4523]) (by decide +kernel)
def pv162829 : PrimeValue := ⟨162829, pr162829⟩
private theorem pr162853 : PrimeCertificate 162853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv331]) (by decide +kernel)
def pv162853 : PrimeValue := ⟨162853, pr162853⟩
private theorem pr162859 : PrimeCertificate 162859 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv27143]) (by decide +kernel)
def pv162859 : PrimeValue := ⟨162859, pr162859⟩
private theorem pr162881 : PrimeCertificate 162881 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv509]) (by decide +kernel)
def pv162881 : PrimeValue := ⟨162881, pr162881⟩
private theorem pr162889 : PrimeCertificate 162889 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv617]) (by decide +kernel)
def pv162889 : PrimeValue := ⟨162889, pr162889⟩
private theorem pr162901 : PrimeCertificate 162901 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv181]) (by decide +kernel)
def pv162901 : PrimeValue := ⟨162901, pr162901⟩
private theorem pr162907 : PrimeCertificate 162907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv1429]) (by decide +kernel)
def pv162907 : PrimeValue := ⟨162907, pr162907⟩
private theorem pr162971 : PrimeCertificate 162971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv43,pv379]) (by decide +kernel)
def pv162971 : PrimeValue := ⟨162971, pr162971⟩
private theorem pr162973 : PrimeCertificate 162973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv503]) (by decide +kernel)
def pv162973 : PrimeValue := ⟨162973, pr162973⟩
private theorem pr162989 : PrimeCertificate 162989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv5821]) (by decide +kernel)
def pv162989 : PrimeValue := ⟨162989, pr162989⟩
private theorem pr162997 : PrimeCertificate 162997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv47]) (by decide +kernel)
def pv162997 : PrimeValue := ⟨162997, pr162997⟩
private theorem pr163003 : PrimeCertificate 163003 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv3881]) (by decide +kernel)
def pv163003 : PrimeValue := ⟨163003, pr163003⟩
private theorem pr163019 : PrimeCertificate 163019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv81509]) (by decide +kernel)
def pv163019 : PrimeValue := ⟨163019, pr163019⟩
private theorem pr163061 : PrimeCertificate 163061 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv31,pv263]) (by decide +kernel)
def pv163061 : PrimeValue := ⟨163061, pr163061⟩
private theorem pr163109 : PrimeCertificate 163109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv337]) (by decide +kernel)
def pv163109 : PrimeValue := ⟨163109, pr163109⟩
private theorem pr163117 : PrimeCertificate 163117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv197]) (by decide +kernel)
def pv163117 : PrimeValue := ⟨163117, pr163117⟩
private theorem pr163147 : PrimeCertificate 163147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv27191]) (by decide +kernel)
def pv163147 : PrimeValue := ⟨163147, pr163147⟩
private theorem pr163151 : PrimeCertificate 163151 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv251]) (by decide +kernel)
def pv163151 : PrimeValue := ⟨163151, pr163151⟩
private theorem pr163169 : PrimeCertificate 163169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5099]) (by decide +kernel)
def pv163169 : PrimeValue := ⟨163169, pr163169⟩
private theorem pr163171 : PrimeCertificate 163171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv37]) (by decide +kernel)
def pv163171 : PrimeValue := ⟨163171, pr163171⟩
private theorem pr163181 : PrimeCertificate 163181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41,pv199]) (by decide +kernel)
def pv163181 : PrimeValue := ⟨163181, pr163181⟩
private theorem pr163193 : PrimeCertificate 163193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv20399]) (by decide +kernel)
def pv163193 : PrimeValue := ⟨163193, pr163193⟩
private theorem pr163199 : PrimeCertificate 163199 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv11657]) (by decide +kernel)
def pv163199 : PrimeValue := ⟨163199, pr163199⟩
private theorem pr163243 : PrimeCertificate 163243 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv3023]) (by decide +kernel)
def pv163243 : PrimeValue := ⟨163243, pr163243⟩
private theorem pr163249 : PrimeCertificate 163249 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv19,pv179]) (by decide +kernel)
def pv163249 : PrimeValue := ⟨163249, pr163249⟩
private theorem pr163259 : PrimeCertificate 163259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv81629]) (by decide +kernel)
def pv163259 : PrimeValue := ⟨163259, pr163259⟩
private theorem pr163307 : PrimeCertificate 163307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13,pv571]) (by decide +kernel)
def pv163307 : PrimeValue := ⟨163307, pr163307⟩
private theorem pr163321 : PrimeCertificate 163321 :=
  certifyPrime (q := pv47) (ls := [pv2,pv3,pv5,pv1361]) (by decide +kernel)
def pv163321 : PrimeValue := ⟨163321, pr163321⟩
private theorem pr163337 : PrimeCertificate 163337 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv1201]) (by decide +kernel)
def pv163337 : PrimeValue := ⟨163337, pr163337⟩
private theorem pr163351 : PrimeCertificate 163351 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv163351 : PrimeValue := ⟨163351, pr163351⟩
private theorem pr163363 : PrimeCertificate 163363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv1433]) (by decide +kernel)
def pv163363 : PrimeValue := ⟨163363, pr163363⟩
private theorem pr163403 : PrimeCertificate 163403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv81701]) (by decide +kernel)
def pv163403 : PrimeValue := ⟨163403, pr163403⟩
private theorem pr163409 : PrimeCertificate 163409 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv1459]) (by decide +kernel)
def pv163409 : PrimeValue := ⟨163409, pr163409⟩
private theorem pr163417 : PrimeCertificate 163417 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv619]) (by decide +kernel)
def pv163417 : PrimeValue := ⟨163417, pr163417⟩
private theorem pr163433 : PrimeCertificate 163433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv659]) (by decide +kernel)
def pv163433 : PrimeValue := ⟨163433, pr163433⟩
private theorem pr163469 : PrimeCertificate 163469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv40867]) (by decide +kernel)
def pv163469 : PrimeValue := ⟨163469, pr163469⟩
private theorem pr163481 : PrimeCertificate 163481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv61,pv67]) (by decide +kernel)
def pv163481 : PrimeValue := ⟨163481, pr163481⟩
private theorem pr163483 : PrimeCertificate 163483 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11,pv2477]) (by decide +kernel)
def pv163483 : PrimeValue := ⟨163483, pr163483⟩
private theorem pr163487 : PrimeCertificate 163487 :=
  certifyPrime (q := pv5) (ls := [pv2,pv43,pv1901]) (by decide +kernel)
def pv163487 : PrimeValue := ⟨163487, pr163487⟩
private theorem pr163517 : PrimeCertificate 163517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv40879]) (by decide +kernel)
def pv163517 : PrimeValue := ⟨163517, pr163517⟩
private theorem pr163561 : PrimeCertificate 163561 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv29,pv47]) (by decide +kernel)
def pv163561 : PrimeValue := ⟨163561, pr163561⟩
private theorem pr163573 : PrimeCertificate 163573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv317]) (by decide +kernel)
def pv163573 : PrimeValue := ⟨163573, pr163573⟩
private theorem pr163601 : PrimeCertificate 163601 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv409]) (by decide +kernel)
def pv163601 : PrimeValue := ⟨163601, pr163601⟩
private theorem pr163621 : PrimeCertificate 163621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv101]) (by decide +kernel)
def pv163621 : PrimeValue := ⟨163621, pr163621⟩
private theorem pr163627 : PrimeCertificate 163627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv27271]) (by decide +kernel)
def pv163627 : PrimeValue := ⟨163627, pr163627⟩
private theorem pr163633 : PrimeCertificate 163633 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv487]) (by decide +kernel)
def pv163633 : PrimeValue := ⟨163633, pr163633⟩
private theorem pr163637 : PrimeCertificate 163637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv3719]) (by decide +kernel)
def pv163637 : PrimeValue := ⟨163637, pr163637⟩
private theorem pr163643 : PrimeCertificate 163643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv4813]) (by decide +kernel)
def pv163643 : PrimeValue := ⟨163643, pr163643⟩
private theorem pr163673 : PrimeCertificate 163673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41,pv499]) (by decide +kernel)
def pv163673 : PrimeValue := ⟨163673, pr163673⟩
private theorem pr163679 : PrimeCertificate 163679 :=
  certifyPrime (q := pv17) (ls := [pv2,pv81839]) (by decide +kernel)
def pv163679 : PrimeValue := ⟨163679, pr163679⟩
private theorem pr163697 : PrimeCertificate 163697 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv787]) (by decide +kernel)
def pv163697 : PrimeValue := ⟨163697, pr163697⟩
private theorem pr163729 : PrimeCertificate 163729 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv379]) (by decide +kernel)
def pv163729 : PrimeValue := ⟨163729, pr163729⟩
private theorem pr163733 : PrimeCertificate 163733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv40933]) (by decide +kernel)
def pv163733 : PrimeValue := ⟨163733, pr163733⟩
private theorem pr163741 : PrimeCertificate 163741 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv2729]) (by decide +kernel)
def pv163741 : PrimeValue := ⟨163741, pr163741⟩
private theorem pr163753 : PrimeCertificate 163753 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv6823]) (by decide +kernel)
def pv163753 : PrimeValue := ⟨163753, pr163753⟩
private theorem pr163771 : PrimeCertificate 163771 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv5,pv53,pv103]) (by decide +kernel)
def pv163771 : PrimeValue := ⟨163771, pr163771⟩
private theorem pr163781 : PrimeCertificate 163781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv431]) (by decide +kernel)
def pv163781 : PrimeValue := ⟨163781, pr163781⟩
private theorem pr163789 : PrimeCertificate 163789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13649]) (by decide +kernel)
def pv163789 : PrimeValue := ⟨163789, pr163789⟩
private theorem pr163811 : PrimeCertificate 163811 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv16381]) (by decide +kernel)
def pv163811 : PrimeValue := ⟨163811, pr163811⟩
private theorem pr163819 : PrimeCertificate 163819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv479]) (by decide +kernel)
def pv163819 : PrimeValue := ⟨163819, pr163819⟩
private theorem pr163841 : PrimeCertificate 163841 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5]) (by decide +kernel)
def pv163841 : PrimeValue := ⟨163841, pr163841⟩
private theorem pr163847 : PrimeCertificate 163847 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv61,pv79]) (by decide +kernel)
def pv163847 : PrimeValue := ⟨163847, pr163847⟩
private theorem pr163853 : PrimeCertificate 163853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv23,pv137]) (by decide +kernel)
def pv163853 : PrimeValue := ⟨163853, pr163853⟩
private theorem pr163859 : PrimeCertificate 163859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv81929]) (by decide +kernel)
def pv163859 : PrimeValue := ⟨163859, pr163859⟩
private theorem pr163871 : PrimeCertificate 163871 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv2341]) (by decide +kernel)
def pv163871 : PrimeValue := ⟨163871, pr163871⟩
private theorem pr163883 : PrimeCertificate 163883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67,pv1223]) (by decide +kernel)
def pv163883 : PrimeValue := ⟨163883, pr163883⟩
private theorem pr163901 : PrimeCertificate 163901 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv149]) (by decide +kernel)
def pv163901 : PrimeValue := ⟨163901, pr163901⟩
private theorem pr163909 : PrimeCertificate 163909 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv29,pv157]) (by decide +kernel)
def pv163909 : PrimeValue := ⟨163909, pr163909⟩
private theorem pr163927 : PrimeCertificate 163927 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv1301]) (by decide +kernel)
def pv163927 : PrimeValue := ⟨163927, pr163927⟩
private theorem pr163981 : PrimeCertificate 163981 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv911]) (by decide +kernel)
def pv163981 : PrimeValue := ⟨163981, pr163981⟩
private theorem pr163987 : PrimeCertificate 163987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv151,pv181]) (by decide +kernel)
def pv163987 : PrimeValue := ⟨163987, pr163987⟩
private theorem pr163991 : PrimeCertificate 163991 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv23,pv31]) (by decide +kernel)
def pv163991 : PrimeValue := ⟨163991, pr163991⟩
private theorem pr164011 : PrimeCertificate 164011 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv11,pv71]) (by decide +kernel)
def pv164011 : PrimeValue := ⟨164011, pr164011⟩
private theorem pr164023 : PrimeCertificate 164023 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv27337]) (by decide +kernel)
def pv164023 : PrimeValue := ⟨164023, pr164023⟩
private theorem pr164051 : PrimeCertificate 164051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv193]) (by decide +kernel)
def pv164051 : PrimeValue := ⟨164051, pr164051⟩
private theorem pr164057 : PrimeCertificate 164057 :=
  certifyPrime (q := pv3) (ls := [pv2,pv20507]) (by decide +kernel)
def pv164057 : PrimeValue := ⟨164057, pr164057⟩
private theorem pr164071 : PrimeCertificate 164071 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv1823]) (by decide +kernel)
def pv164071 : PrimeValue := ⟨164071, pr164071⟩
private theorem pr164089 : PrimeCertificate 164089 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv43,pv53]) (by decide +kernel)
def pv164089 : PrimeValue := ⟨164089, pr164089⟩
private theorem pr164113 : PrimeCertificate 164113 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv263]) (by decide +kernel)
def pv164113 : PrimeValue := ⟨164113, pr164113⟩
private theorem pr164117 : PrimeCertificate 164117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89,pv461]) (by decide +kernel)
def pv164117 : PrimeValue := ⟨164117, pr164117⟩
private theorem pr164147 : PrimeCertificate 164147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv82073]) (by decide +kernel)
def pv164147 : PrimeValue := ⟨164147, pr164147⟩
private theorem pr164149 : PrimeCertificate 164149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13679]) (by decide +kernel)
def pv164149 : PrimeValue := ⟨164149, pr164149⟩
private theorem pr164191 : PrimeCertificate 164191 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv421]) (by decide +kernel)
def pv164191 : PrimeValue := ⟨164191, pr164191⟩
private theorem pr164201 : PrimeCertificate 164201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv821]) (by decide +kernel)
def pv164201 : PrimeValue := ⟨164201, pr164201⟩
private theorem pr164233 : PrimeCertificate 164233 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2281]) (by decide +kernel)
def pv164233 : PrimeValue := ⟨164233, pr164233⟩
private theorem pr164249 : PrimeCertificate 164249 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv419]) (by decide +kernel)
def pv164249 : PrimeValue := ⟨164249, pr164249⟩
private theorem pr164279 : PrimeCertificate 164279 :=
  certifyPrime (q := pv11) (ls := [pv2,pv82139]) (by decide +kernel)
def pv164279 : PrimeValue := ⟨164279, pr164279⟩
private theorem pr164299 : PrimeCertificate 164299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv139,pv197]) (by decide +kernel)
def pv164299 : PrimeValue := ⟨164299, pr164299⟩
private theorem pr164309 : PrimeCertificate 164309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41077]) (by decide +kernel)
def pv164309 : PrimeValue := ⟨164309, pr164309⟩
private theorem pr164321 : PrimeCertificate 164321 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv79]) (by decide +kernel)
def pv164321 : PrimeValue := ⟨164321, pr164321⟩
private theorem pr164341 : PrimeCertificate 164341 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv11,pv83]) (by decide +kernel)
def pv164341 : PrimeValue := ⟨164341, pr164341⟩
private theorem pr164357 : PrimeCertificate 164357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv2417]) (by decide +kernel)
def pv164357 : PrimeValue := ⟨164357, pr164357⟩
private theorem pr164363 : PrimeCertificate 164363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv31,pv241]) (by decide +kernel)
def pv164363 : PrimeValue := ⟨164363, pr164363⟩
private theorem pr164413 : PrimeCertificate 164413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv4567]) (by decide +kernel)
def pv164413 : PrimeValue := ⟨164413, pr164413⟩
private theorem pr164429 : PrimeCertificate 164429 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv37,pv101]) (by decide +kernel)
def pv164429 : PrimeValue := ⟨164429, pr164429⟩
private theorem pr164431 : PrimeCertificate 164431 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv29]) (by decide +kernel)
def pv164431 : PrimeValue := ⟨164431, pr164431⟩
private theorem pr164443 : PrimeCertificate 164443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv27407]) (by decide +kernel)
def pv164443 : PrimeValue := ⟨164443, pr164443⟩
private theorem pr164447 : PrimeCertificate 164447 :=
  certifyPrime (q := pv5) (ls := [pv2,pv82223]) (by decide +kernel)
def pv164447 : PrimeValue := ⟨164447, pr164447⟩
private theorem pr164449 : PrimeCertificate 164449 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv571]) (by decide +kernel)
def pv164449 : PrimeValue := ⟨164449, pr164449⟩
private theorem pr164471 : PrimeCertificate 164471 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv16447]) (by decide +kernel)
def pv164471 : PrimeValue := ⟨164471, pr164471⟩
private theorem pr164477 : PrimeCertificate 164477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv3163]) (by decide +kernel)
def pv164477 : PrimeValue := ⟨164477, pr164477⟩
private theorem pr164513 : PrimeCertificate 164513 :=
  certifyPrime (q := pv3) (ls := [pv2,pv53,pv97]) (by decide +kernel)
def pv164513 : PrimeValue := ⟨164513, pr164513⟩
private theorem pr164531 : PrimeCertificate 164531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv16453]) (by decide +kernel)
def pv164531 : PrimeValue := ⟨164531, pr164531⟩
private theorem pr164569 : PrimeCertificate 164569 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv6857]) (by decide +kernel)
def pv164569 : PrimeValue := ⟨164569, pr164569⟩
private theorem pr164581 : PrimeCertificate 164581 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv5,pv13,pv211]) (by decide +kernel)
def pv164581 : PrimeValue := ⟨164581, pr164581⟩
private theorem pr164587 : PrimeCertificate 164587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv27431]) (by decide +kernel)
def pv164587 : PrimeValue := ⟨164587, pr164587⟩
private theorem pr164617 : PrimeCertificate 164617 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19]) (by decide +kernel)
def pv164617 : PrimeValue := ⟨164617, pr164617⟩
private theorem pr164621 : PrimeCertificate 164621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv8231]) (by decide +kernel)
def pv164621 : PrimeValue := ⟨164621, pr164621⟩
private theorem pr164623 : PrimeCertificate 164623 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv27437]) (by decide +kernel)
def pv164623 : PrimeValue := ⟨164623, pr164623⟩
private theorem pr164653 : PrimeCertificate 164653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13721]) (by decide +kernel)
def pv164653 : PrimeValue := ⟨164653, pr164653⟩
private theorem pr164663 : PrimeCertificate 164663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv29,pv167]) (by decide +kernel)
def pv164663 : PrimeValue := ⟨164663, pr164663⟩
private theorem pr164677 : PrimeCertificate 164677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13723]) (by decide +kernel)
def pv164677 : PrimeValue := ⟨164677, pr164677⟩
private theorem pr164683 : PrimeCertificate 164683 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv1307]) (by decide +kernel)
def pv164683 : PrimeValue := ⟨164683, pr164683⟩
private theorem pr164707 : PrimeCertificate 164707 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv97,pv283]) (by decide +kernel)
def pv164707 : PrimeValue := ⟨164707, pr164707⟩
private theorem pr164729 : PrimeCertificate 164729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv59,pv349]) (by decide +kernel)
def pv164729 : PrimeValue := ⟨164729, pr164729⟩
private theorem pr164743 : PrimeCertificate 164743 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv27457]) (by decide +kernel)
def pv164743 : PrimeValue := ⟨164743, pr164743⟩
private theorem pr164767 : PrimeCertificate 164767 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv3923]) (by decide +kernel)
def pv164767 : PrimeValue := ⟨164767, pr164767⟩
private theorem pr164771 : PrimeCertificate 164771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv16477]) (by decide +kernel)
def pv164771 : PrimeValue := ⟨164771, pr164771⟩
private theorem pr164789 : PrimeCertificate 164789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv3169]) (by decide +kernel)
def pv164789 : PrimeValue := ⟨164789, pr164789⟩
private theorem pr164809 : PrimeCertificate 164809 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv109]) (by decide +kernel)
def pv164809 : PrimeValue := ⟨164809, pr164809⟩
private theorem pr164831 : PrimeCertificate 164831 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv53,pv311]) (by decide +kernel)
def pv164831 : PrimeValue := ⟨164831, pr164831⟩
private theorem pr164837 : PrimeCertificate 164837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv29]) (by decide +kernel)
def pv164837 : PrimeValue := ⟨164837, pr164837⟩
private theorem pr164839 : PrimeCertificate 164839 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv83,pv331]) (by decide +kernel)
def pv164839 : PrimeValue := ⟨164839, pr164839⟩
private theorem pr164881 : PrimeCertificate 164881 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv229]) (by decide +kernel)
def pv164881 : PrimeValue := ⟨164881, pr164881⟩
private theorem pr164911 : PrimeCertificate 164911 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv23,pv239]) (by decide +kernel)
def pv164911 : PrimeValue := ⟨164911, pr164911⟩
private theorem pr164953 : PrimeCertificate 164953 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29,pv79]) (by decide +kernel)
def pv164953 : PrimeValue := ⟨164953, pr164953⟩
private theorem pr164987 : PrimeCertificate 164987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv82493]) (by decide +kernel)
def pv164987 : PrimeValue := ⟨164987, pr164987⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
