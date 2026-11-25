/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table018
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table018.pv43063
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table009
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table010

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr43063 : PrimeCertificate 43063 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7177]) (by decide +kernel)
def pv43063 : PrimeValue := ⟨43063, pr43063⟩
private theorem pr43067 : PrimeCertificate 43067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv353]) (by decide +kernel)
def pv43067 : PrimeValue := ⟨43067, pr43067⟩
private theorem pr43093 : PrimeCertificate 43093 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv19]) (by decide +kernel)
def pv43093 : PrimeValue := ⟨43093, pr43093⟩
private theorem pr43103 : PrimeCertificate 43103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv937]) (by decide +kernel)
def pv43103 : PrimeValue := ⟨43103, pr43103⟩
private theorem pr43117 : PrimeCertificate 43117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3593]) (by decide +kernel)
def pv43117 : PrimeValue := ⟨43117, pr43117⟩
private theorem pr43133 : PrimeCertificate 43133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv263]) (by decide +kernel)
def pv43133 : PrimeValue := ⟨43133, pr43133⟩
private theorem pr43151 : PrimeCertificate 43151 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv863]) (by decide +kernel)
def pv43151 : PrimeValue := ⟨43151, pr43151⟩
private theorem pr43159 : PrimeCertificate 43159 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7193]) (by decide +kernel)
def pv43159 : PrimeValue := ⟨43159, pr43159⟩
private theorem pr43177 : PrimeCertificate 43177 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv257]) (by decide +kernel)
def pv43177 : PrimeValue := ⟨43177, pr43177⟩
private theorem pr43189 : PrimeCertificate 43189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv59,pv61]) (by decide +kernel)
def pv43189 : PrimeValue := ⟨43189, pr43189⟩
private theorem pr43201 : PrimeCertificate 43201 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv43201 : PrimeValue := ⟨43201, pr43201⟩
private theorem pr43207 : PrimeCertificate 43207 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv379]) (by decide +kernel)
def pv43207 : PrimeValue := ⟨43207, pr43207⟩
private theorem pr43223 : PrimeCertificate 43223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv21611]) (by decide +kernel)
def pv43223 : PrimeValue := ⟨43223, pr43223⟩
private theorem pr43237 : PrimeCertificate 43237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1201]) (by decide +kernel)
def pv43237 : PrimeValue := ⟨43237, pr43237⟩
private theorem pr43261 : PrimeCertificate 43261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv103]) (by decide +kernel)
def pv43261 : PrimeValue := ⟨43261, pr43261⟩
private theorem pr43271 : PrimeCertificate 43271 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv4327]) (by decide +kernel)
def pv43271 : PrimeValue := ⟨43271, pr43271⟩
private theorem pr43283 : PrimeCertificate 43283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv19,pv67]) (by decide +kernel)
def pv43283 : PrimeValue := ⟨43283, pr43283⟩
private theorem pr43291 : PrimeCertificate 43291 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv37]) (by decide +kernel)
def pv43291 : PrimeValue := ⟨43291, pr43291⟩
private theorem pr43313 : PrimeCertificate 43313 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2707]) (by decide +kernel)
def pv43313 : PrimeValue := ⟨43313, pr43313⟩
private theorem pr43319 : PrimeCertificate 43319 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv179]) (by decide +kernel)
def pv43319 : PrimeValue := ⟨43319, pr43319⟩
private theorem pr43321 : PrimeCertificate 43321 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv43321 : PrimeValue := ⟨43321, pr43321⟩
private theorem pr43331 : PrimeCertificate 43331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv619]) (by decide +kernel)
def pv43331 : PrimeValue := ⟨43331, pr43331⟩
private theorem pr43391 : PrimeCertificate 43391 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv4339]) (by decide +kernel)
def pv43391 : PrimeValue := ⟨43391, pr43391⟩
private theorem pr43397 : PrimeCertificate 43397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv571]) (by decide +kernel)
def pv43397 : PrimeValue := ⟨43397, pr43397⟩
private theorem pr43399 : PrimeCertificate 43399 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv2411]) (by decide +kernel)
def pv43399 : PrimeValue := ⟨43399, pr43399⟩
private theorem pr43403 : PrimeCertificate 43403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv21701]) (by decide +kernel)
def pv43403 : PrimeValue := ⟨43403, pr43403⟩
private theorem pr43411 : PrimeCertificate 43411 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv1447]) (by decide +kernel)
def pv43411 : PrimeValue := ⟨43411, pr43411⟩
private theorem pr43427 : PrimeCertificate 43427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv21713]) (by decide +kernel)
def pv43427 : PrimeValue := ⟨43427, pr43427⟩
private theorem pr43441 : PrimeCertificate 43441 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv181]) (by decide +kernel)
def pv43441 : PrimeValue := ⟨43441, pr43441⟩
private theorem pr43451 : PrimeCertificate 43451 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv79]) (by decide +kernel)
def pv43451 : PrimeValue := ⟨43451, pr43451⟩
private theorem pr43457 : PrimeCertificate 43457 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv97]) (by decide +kernel)
def pv43457 : PrimeValue := ⟨43457, pr43457⟩
private theorem pr43481 : PrimeCertificate 43481 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv1087]) (by decide +kernel)
def pv43481 : PrimeValue := ⟨43481, pr43481⟩
private theorem pr43487 : PrimeCertificate 43487 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv1279]) (by decide +kernel)
def pv43487 : PrimeValue := ⟨43487, pr43487⟩
private theorem pr43499 : PrimeCertificate 43499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv239]) (by decide +kernel)
def pv43499 : PrimeValue := ⟨43499, pr43499⟩
private theorem pr43517 : PrimeCertificate 43517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv23,pv43]) (by decide +kernel)
def pv43517 : PrimeValue := ⟨43517, pr43517⟩
private theorem pr43541 : PrimeCertificate 43541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv311]) (by decide +kernel)
def pv43541 : PrimeValue := ⟨43541, pr43541⟩
private theorem pr43543 : PrimeCertificate 43543 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41,pv59]) (by decide +kernel)
def pv43543 : PrimeValue := ⟨43543, pr43543⟩
private theorem pr43573 : PrimeCertificate 43573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3631]) (by decide +kernel)
def pv43573 : PrimeValue := ⟨43573, pr43573⟩
private theorem pr43577 : PrimeCertificate 43577 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv419]) (by decide +kernel)
def pv43577 : PrimeValue := ⟨43577, pr43577⟩
private theorem pr43579 : PrimeCertificate 43579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv269]) (by decide +kernel)
def pv43579 : PrimeValue := ⟨43579, pr43579⟩
private theorem pr43591 : PrimeCertificate 43591 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv1453]) (by decide +kernel)
def pv43591 : PrimeValue := ⟨43591, pr43591⟩
private theorem pr43597 : PrimeCertificate 43597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv173]) (by decide +kernel)
def pv43597 : PrimeValue := ⟨43597, pr43597⟩
private theorem pr43607 : PrimeCertificate 43607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv21803]) (by decide +kernel)
def pv43607 : PrimeValue := ⟨43607, pr43607⟩
private theorem pr43609 : PrimeCertificate 43609 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv23,pv79]) (by decide +kernel)
def pv43609 : PrimeValue := ⟨43609, pr43609⟩
private theorem pr43613 : PrimeCertificate 43613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv10903]) (by decide +kernel)
def pv43613 : PrimeValue := ⟨43613, pr43613⟩
private theorem pr43627 : PrimeCertificate 43627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv661]) (by decide +kernel)
def pv43627 : PrimeValue := ⟨43627, pr43627⟩
private theorem pr43633 : PrimeCertificate 43633 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv101]) (by decide +kernel)
def pv43633 : PrimeValue := ⟨43633, pr43633⟩
private theorem pr43649 : PrimeCertificate 43649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv31]) (by decide +kernel)
def pv43649 : PrimeValue := ⟨43649, pr43649⟩
private theorem pr43651 : PrimeCertificate 43651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv97]) (by decide +kernel)
def pv43651 : PrimeValue := ⟨43651, pr43651⟩
private theorem pr43661 : PrimeCertificate 43661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv37,pv59]) (by decide +kernel)
def pv43661 : PrimeValue := ⟨43661, pr43661⟩
private theorem pr43669 : PrimeCertificate 43669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1213]) (by decide +kernel)
def pv43669 : PrimeValue := ⟨43669, pr43669⟩
private theorem pr43691 : PrimeCertificate 43691 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv17,pv257]) (by decide +kernel)
def pv43691 : PrimeValue := ⟨43691, pr43691⟩
private theorem pr43711 : PrimeCertificate 43711 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv31,pv47]) (by decide +kernel)
def pv43711 : PrimeValue := ⟨43711, pr43711⟩
private theorem pr43717 : PrimeCertificate 43717 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3643]) (by decide +kernel)
def pv43717 : PrimeValue := ⟨43717, pr43717⟩
private theorem pr43721 : PrimeCertificate 43721 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1093]) (by decide +kernel)
def pv43721 : PrimeValue := ⟨43721, pr43721⟩
private theorem pr43753 : PrimeCertificate 43753 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1823]) (by decide +kernel)
def pv43753 : PrimeValue := ⟨43753, pr43753⟩
private theorem pr43759 : PrimeCertificate 43759 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv13,pv17]) (by decide +kernel)
def pv43759 : PrimeValue := ⟨43759, pr43759⟩
private theorem pr43777 : PrimeCertificate 43777 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19]) (by decide +kernel)
def pv43777 : PrimeValue := ⟨43777, pr43777⟩
private theorem pr43781 : PrimeCertificate 43781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv199]) (by decide +kernel)
def pv43781 : PrimeValue := ⟨43781, pr43781⟩
private theorem pr43783 : PrimeCertificate 43783 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7297]) (by decide +kernel)
def pv43783 : PrimeValue := ⟨43783, pr43783⟩
private theorem pr43787 : PrimeCertificate 43787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv21893]) (by decide +kernel)
def pv43787 : PrimeValue := ⟨43787, pr43787⟩
private theorem pr43789 : PrimeCertificate 43789 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv41,pv89]) (by decide +kernel)
def pv43789 : PrimeValue := ⟨43789, pr43789⟩
private theorem pr43793 : PrimeCertificate 43793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv17,pv23]) (by decide +kernel)
def pv43793 : PrimeValue := ⟨43793, pr43793⟩
private theorem pr43801 : PrimeCertificate 43801 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv73]) (by decide +kernel)
def pv43801 : PrimeValue := ⟨43801, pr43801⟩
private theorem pr43853 : PrimeCertificate 43853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv577]) (by decide +kernel)
def pv43853 : PrimeValue := ⟨43853, pr43853⟩
private theorem pr43867 : PrimeCertificate 43867 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv2437]) (by decide +kernel)
def pv43867 : PrimeValue := ⟨43867, pr43867⟩
private theorem pr43889 : PrimeCertificate 43889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv211]) (by decide +kernel)
def pv43889 : PrimeValue := ⟨43889, pr43889⟩
private theorem pr43891 : PrimeCertificate 43891 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv11,pv19]) (by decide +kernel)
def pv43891 : PrimeValue := ⟨43891, pr43891⟩
private theorem pr43913 : PrimeCertificate 43913 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv499]) (by decide +kernel)
def pv43913 : PrimeValue := ⟨43913, pr43913⟩
private theorem pr43933 : PrimeCertificate 43933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv523]) (by decide +kernel)
def pv43933 : PrimeValue := ⟨43933, pr43933⟩
private theorem pr43943 : PrimeCertificate 43943 :=
  certifyPrime (q := pv5) (ls := [pv2,pv127,pv173]) (by decide +kernel)
def pv43943 : PrimeValue := ⟨43943, pr43943⟩
private theorem pr43951 : PrimeCertificate 43951 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv293]) (by decide +kernel)
def pv43951 : PrimeValue := ⟨43951, pr43951⟩
private theorem pr43961 : PrimeCertificate 43961 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv157]) (by decide +kernel)
def pv43961 : PrimeValue := ⟨43961, pr43961⟩
private theorem pr43963 : PrimeCertificate 43963 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv17,pv431]) (by decide +kernel)
def pv43963 : PrimeValue := ⟨43963, pr43963⟩
private theorem pr43969 : PrimeCertificate 43969 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv229]) (by decide +kernel)
def pv43969 : PrimeValue := ⟨43969, pr43969⟩
private theorem pr43973 : PrimeCertificate 43973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv10993]) (by decide +kernel)
def pv43973 : PrimeValue := ⟨43973, pr43973⟩
private theorem pr43987 : PrimeCertificate 43987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7331]) (by decide +kernel)
def pv43987 : PrimeValue := ⟨43987, pr43987⟩
private theorem pr43991 : PrimeCertificate 43991 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv53,pv83]) (by decide +kernel)
def pv43991 : PrimeValue := ⟨43991, pr43991⟩
private theorem pr43997 : PrimeCertificate 43997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv647]) (by decide +kernel)
def pv43997 : PrimeValue := ⟨43997, pr43997⟩
private theorem pr44017 : PrimeCertificate 44017 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv131]) (by decide +kernel)
def pv44017 : PrimeValue := ⟨44017, pr44017⟩
private theorem pr44021 : PrimeCertificate 44021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31,pv71]) (by decide +kernel)
def pv44021 : PrimeValue := ⟨44021, pr44021⟩
private theorem pr44027 : PrimeCertificate 44027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv22013]) (by decide +kernel)
def pv44027 : PrimeValue := ⟨44027, pr44027⟩
private theorem pr44029 : PrimeCertificate 44029 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1223]) (by decide +kernel)
def pv44029 : PrimeValue := ⟨44029, pr44029⟩
private theorem pr44041 : PrimeCertificate 44041 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv367]) (by decide +kernel)
def pv44041 : PrimeValue := ⟨44041, pr44041⟩
private theorem pr44053 : PrimeCertificate 44053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3671]) (by decide +kernel)
def pv44053 : PrimeValue := ⟨44053, pr44053⟩
private theorem pr44059 : PrimeCertificate 44059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1049]) (by decide +kernel)
def pv44059 : PrimeValue := ⟨44059, pr44059⟩
private theorem pr44071 : PrimeCertificate 44071 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv113]) (by decide +kernel)
def pv44071 : PrimeValue := ⟨44071, pr44071⟩
private theorem pr44087 : PrimeCertificate 44087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv47,pv67]) (by decide +kernel)
def pv44087 : PrimeValue := ⟨44087, pr44087⟩
private theorem pr44089 : PrimeCertificate 44089 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv167]) (by decide +kernel)
def pv44089 : PrimeValue := ⟨44089, pr44089⟩
private theorem pr44101 : PrimeCertificate 44101 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv44101 : PrimeValue := ⟨44101, pr44101⟩
private theorem pr44111 : PrimeCertificate 44111 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv401]) (by decide +kernel)
def pv44111 : PrimeValue := ⟨44111, pr44111⟩
private theorem pr44119 : PrimeCertificate 44119 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv19,pv43]) (by decide +kernel)
def pv44119 : PrimeValue := ⟨44119, pr44119⟩
private theorem pr44123 : PrimeCertificate 44123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv1697]) (by decide +kernel)
def pv44123 : PrimeValue := ⟨44123, pr44123⟩
private theorem pr44129 : PrimeCertificate 44129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv197]) (by decide +kernel)
def pv44129 : PrimeValue := ⟨44129, pr44129⟩
private theorem pr44131 : PrimeCertificate 44131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1471]) (by decide +kernel)
def pv44131 : PrimeValue := ⟨44131, pr44131⟩
private theorem pr44159 : PrimeCertificate 44159 :=
  certifyPrime (q := pv11) (ls := [pv2,pv22079]) (by decide +kernel)
def pv44159 : PrimeValue := ⟨44159, pr44159⟩
private theorem pr44171 : PrimeCertificate 44171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv631]) (by decide +kernel)
def pv44171 : PrimeValue := ⟨44171, pr44171⟩
private theorem pr44179 : PrimeCertificate 44179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv199]) (by decide +kernel)
def pv44179 : PrimeValue := ⟨44179, pr44179⟩
private theorem pr44189 : PrimeCertificate 44189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11047]) (by decide +kernel)
def pv44189 : PrimeValue := ⟨44189, pr44189⟩
private theorem pr44201 : PrimeCertificate 44201 :=
  certifyPrime (q := pv37) (ls := [pv2,pv5,pv13,pv17]) (by decide +kernel)
def pv44201 : PrimeValue := ⟨44201, pr44201⟩
private theorem pr44203 : PrimeCertificate 44203 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv53,pv139]) (by decide +kernel)
def pv44203 : PrimeValue := ⟨44203, pr44203⟩
private theorem pr44207 : PrimeCertificate 44207 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv31]) (by decide +kernel)
def pv44207 : PrimeValue := ⟨44207, pr44207⟩
private theorem pr44221 : PrimeCertificate 44221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv67]) (by decide +kernel)
def pv44221 : PrimeValue := ⟨44221, pr44221⟩
private theorem pr44249 : PrimeCertificate 44249 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5531]) (by decide +kernel)
def pv44249 : PrimeValue := ⟨44249, pr44249⟩
private theorem pr44257 : PrimeCertificate 44257 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv461]) (by decide +kernel)
def pv44257 : PrimeValue := ⟨44257, pr44257⟩
private theorem pr44263 : PrimeCertificate 44263 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv2459]) (by decide +kernel)
def pv44263 : PrimeValue := ⟨44263, pr44263⟩
private theorem pr44267 : PrimeCertificate 44267 :=
  certifyPrime (q := pv2) (ls := [pv2,pv22133]) (by decide +kernel)
def pv44267 : PrimeValue := ⟨44267, pr44267⟩
private theorem pr44269 : PrimeCertificate 44269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv31]) (by decide +kernel)
def pv44269 : PrimeValue := ⟨44269, pr44269⟩
private theorem pr44273 : PrimeCertificate 44273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2767]) (by decide +kernel)
def pv44273 : PrimeValue := ⟨44273, pr44273⟩
private theorem pr44279 : PrimeCertificate 44279 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv131]) (by decide +kernel)
def pv44279 : PrimeValue := ⟨44279, pr44279⟩
private theorem pr44281 : PrimeCertificate 44281 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv41]) (by decide +kernel)
def pv44281 : PrimeValue := ⟨44281, pr44281⟩
private theorem pr44293 : PrimeCertificate 44293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3691]) (by decide +kernel)
def pv44293 : PrimeValue := ⟨44293, pr44293⟩
private theorem pr44351 : PrimeCertificate 44351 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv887]) (by decide +kernel)
def pv44351 : PrimeValue := ⟨44351, pr44351⟩
private theorem pr44357 : PrimeCertificate 44357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv853]) (by decide +kernel)
def pv44357 : PrimeValue := ⟨44357, pr44357⟩
private theorem pr44371 : PrimeCertificate 44371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv29]) (by decide +kernel)
def pv44371 : PrimeValue := ⟨44371, pr44371⟩
private theorem pr44381 : PrimeCertificate 44381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv317]) (by decide +kernel)
def pv44381 : PrimeValue := ⟨44381, pr44381⟩
private theorem pr44383 : PrimeCertificate 44383 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv569]) (by decide +kernel)
def pv44383 : PrimeValue := ⟨44383, pr44383⟩
private theorem pr44389 : PrimeCertificate 44389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv137]) (by decide +kernel)
def pv44389 : PrimeValue := ⟨44389, pr44389⟩
private theorem pr44417 : PrimeCertificate 44417 :=
  certifyPrime (q := pv3) (ls := [pv2,pv347]) (by decide +kernel)
def pv44417 : PrimeValue := ⟨44417, pr44417⟩
private theorem pr44449 : PrimeCertificate 44449 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv463]) (by decide +kernel)
def pv44449 : PrimeValue := ⟨44449, pr44449⟩
private theorem pr44453 : PrimeCertificate 44453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11113]) (by decide +kernel)
def pv44453 : PrimeValue := ⟨44453, pr44453⟩
private theorem pr44483 : PrimeCertificate 44483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv967]) (by decide +kernel)
def pv44483 : PrimeValue := ⟨44483, pr44483⟩
private theorem pr44491 : PrimeCertificate 44491 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv1483]) (by decide +kernel)
def pv44491 : PrimeValue := ⟨44491, pr44491⟩
private theorem pr44497 : PrimeCertificate 44497 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv103]) (by decide +kernel)
def pv44497 : PrimeValue := ⟨44497, pr44497⟩
private theorem pr44501 : PrimeCertificate 44501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv89]) (by decide +kernel)
def pv44501 : PrimeValue := ⟨44501, pr44501⟩
private theorem pr44507 : PrimeCertificate 44507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv17]) (by decide +kernel)
def pv44507 : PrimeValue := ⟨44507, pr44507⟩
private theorem pr44519 : PrimeCertificate 44519 :=
  certifyPrime (q := pv13) (ls := [pv2,pv22259]) (by decide +kernel)
def pv44519 : PrimeValue := ⟨44519, pr44519⟩
private theorem pr44531 : PrimeCertificate 44531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv61,pv73]) (by decide +kernel)
def pv44531 : PrimeValue := ⟨44531, pr44531⟩
private theorem pr44533 : PrimeCertificate 44533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1237]) (by decide +kernel)
def pv44533 : PrimeValue := ⟨44533, pr44533⟩
private theorem pr44537 : PrimeCertificate 44537 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv293]) (by decide +kernel)
def pv44537 : PrimeValue := ⟨44537, pr44537⟩
private theorem pr44543 : PrimeCertificate 44543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv22271]) (by decide +kernel)
def pv44543 : PrimeValue := ⟨44543, pr44543⟩
private theorem pr44549 : PrimeCertificate 44549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv37,pv43]) (by decide +kernel)
def pv44549 : PrimeValue := ⟨44549, pr44549⟩
private theorem pr44563 : PrimeCertificate 44563 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv1061]) (by decide +kernel)
def pv44563 : PrimeValue := ⟨44563, pr44563⟩
private theorem pr44579 : PrimeCertificate 44579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv719]) (by decide +kernel)
def pv44579 : PrimeValue := ⟨44579, pr44579⟩
private theorem pr44587 : PrimeCertificate 44587 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv2477]) (by decide +kernel)
def pv44587 : PrimeValue := ⟨44587, pr44587⟩
private theorem pr44617 : PrimeCertificate 44617 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv13]) (by decide +kernel)
def pv44617 : PrimeValue := ⟨44617, pr44617⟩
private theorem pr44621 : PrimeCertificate 44621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv97]) (by decide +kernel)
def pv44621 : PrimeValue := ⟨44621, pr44621⟩
private theorem pr44623 : PrimeCertificate 44623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv37,pv67]) (by decide +kernel)
def pv44623 : PrimeValue := ⟨44623, pr44623⟩
private theorem pr44633 : PrimeCertificate 44633 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv797]) (by decide +kernel)
def pv44633 : PrimeValue := ⟨44633, pr44633⟩
private theorem pr44641 : PrimeCertificate 44641 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv31]) (by decide +kernel)
def pv44641 : PrimeValue := ⟨44641, pr44641⟩
private theorem pr44647 : PrimeCertificate 44647 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv1063]) (by decide +kernel)
def pv44647 : PrimeValue := ⟨44647, pr44647⟩
private theorem pr44651 : PrimeCertificate 44651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv47]) (by decide +kernel)
def pv44651 : PrimeValue := ⟨44651, pr44651⟩
private theorem pr44657 : PrimeCertificate 44657 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2791]) (by decide +kernel)
def pv44657 : PrimeValue := ⟨44657, pr44657⟩
private theorem pr44683 : PrimeCertificate 44683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv677]) (by decide +kernel)
def pv44683 : PrimeValue := ⟨44683, pr44683⟩
private theorem pr44687 : PrimeCertificate 44687 :=
  certifyPrime (q := pv5) (ls := [pv2,pv22343]) (by decide +kernel)
def pv44687 : PrimeValue := ⟨44687, pr44687⟩
private theorem pr44699 : PrimeCertificate 44699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv22349]) (by decide +kernel)
def pv44699 : PrimeValue := ⟨44699, pr44699⟩
private theorem pr44701 : PrimeCertificate 44701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv149]) (by decide +kernel)
def pv44701 : PrimeValue := ⟨44701, pr44701⟩
private theorem pr44711 : PrimeCertificate 44711 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv17,pv263]) (by decide +kernel)
def pv44711 : PrimeValue := ⟨44711, pr44711⟩
private theorem pr44729 : PrimeCertificate 44729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5591]) (by decide +kernel)
def pv44729 : PrimeValue := ⟨44729, pr44729⟩
private theorem pr44741 : PrimeCertificate 44741 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv2237]) (by decide +kernel)
def pv44741 : PrimeValue := ⟨44741, pr44741⟩
private theorem pr44753 : PrimeCertificate 44753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2797]) (by decide +kernel)
def pv44753 : PrimeValue := ⟨44753, pr44753⟩
private theorem pr44771 : PrimeCertificate 44771 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv37]) (by decide +kernel)
def pv44771 : PrimeValue := ⟨44771, pr44771⟩
private theorem pr44773 : PrimeCertificate 44773 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv41]) (by decide +kernel)
def pv44773 : PrimeValue := ⟨44773, pr44773⟩
private theorem pr44777 : PrimeCertificate 44777 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv193]) (by decide +kernel)
def pv44777 : PrimeValue := ⟨44777, pr44777⟩
private theorem pr44789 : PrimeCertificate 44789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11197]) (by decide +kernel)
def pv44789 : PrimeValue := ⟨44789, pr44789⟩
private theorem pr44797 : PrimeCertificate 44797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3733]) (by decide +kernel)
def pv44797 : PrimeValue := ⟨44797, pr44797⟩
private theorem pr44809 : PrimeCertificate 44809 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv1867]) (by decide +kernel)
def pv44809 : PrimeValue := ⟨44809, pr44809⟩
private theorem pr44819 : PrimeCertificate 44819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv22409]) (by decide +kernel)
def pv44819 : PrimeValue := ⟨44819, pr44819⟩
private theorem pr44839 : PrimeCertificate 44839 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv47,pv53]) (by decide +kernel)
def pv44839 : PrimeValue := ⟨44839, pr44839⟩
private theorem pr44843 : PrimeCertificate 44843 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv3203]) (by decide +kernel)
def pv44843 : PrimeValue := ⟨44843, pr44843⟩
private theorem pr44851 : PrimeCertificate 44851 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv13,pv23]) (by decide +kernel)
def pv44851 : PrimeValue := ⟨44851, pr44851⟩
private theorem pr44867 : PrimeCertificate 44867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv22433]) (by decide +kernel)
def pv44867 : PrimeValue := ⟨44867, pr44867⟩
private theorem pr44879 : PrimeCertificate 44879 :=
  certifyPrime (q := pv7) (ls := [pv2,pv19,pv1181]) (by decide +kernel)
def pv44879 : PrimeValue := ⟨44879, pr44879⟩
private theorem pr44887 : PrimeCertificate 44887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7481]) (by decide +kernel)
def pv44887 : PrimeValue := ⟨44887, pr44887⟩
private theorem pr44893 : PrimeCertificate 44893 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29,pv43]) (by decide +kernel)
def pv44893 : PrimeValue := ⟨44893, pr44893⟩
private theorem pr44909 : PrimeCertificate 44909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv103,pv109]) (by decide +kernel)
def pv44909 : PrimeValue := ⟨44909, pr44909⟩
private theorem pr44917 : PrimeCertificate 44917 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv197]) (by decide +kernel)
def pv44917 : PrimeValue := ⟨44917, pr44917⟩
private theorem pr44927 : PrimeCertificate 44927 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv3209]) (by decide +kernel)
def pv44927 : PrimeValue := ⟨44927, pr44927⟩
private theorem pr44939 : PrimeCertificate 44939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv22469]) (by decide +kernel)
def pv44939 : PrimeValue := ⟨44939, pr44939⟩
private theorem pr44953 : PrimeCertificate 44953 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1873]) (by decide +kernel)
def pv44953 : PrimeValue := ⟨44953, pr44953⟩
private theorem pr44959 : PrimeCertificate 44959 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv59,pv127]) (by decide +kernel)
def pv44959 : PrimeValue := ⟨44959, pr44959⟩
private theorem pr44963 : PrimeCertificate 44963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv22481]) (by decide +kernel)
def pv44963 : PrimeValue := ⟨44963, pr44963⟩
private theorem pr44971 : PrimeCertificate 44971 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv1499]) (by decide +kernel)
def pv44971 : PrimeValue := ⟨44971, pr44971⟩
private theorem pr44983 : PrimeCertificate 44983 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv17]) (by decide +kernel)
def pv44983 : PrimeValue := ⟨44983, pr44983⟩
private theorem pr44987 : PrimeCertificate 44987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv83,pv271]) (by decide +kernel)
def pv44987 : PrimeValue := ⟨44987, pr44987⟩
private theorem pr45007 : PrimeCertificate 45007 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv577]) (by decide +kernel)
def pv45007 : PrimeValue := ⟨45007, pr45007⟩
private theorem pr45013 : PrimeCertificate 45013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv31]) (by decide +kernel)
def pv45013 : PrimeValue := ⟨45013, pr45013⟩
private theorem pr45053 : PrimeCertificate 45053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv1609]) (by decide +kernel)
def pv45053 : PrimeValue := ⟨45053, pr45053⟩
private theorem pr45061 : PrimeCertificate 45061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv751]) (by decide +kernel)
def pv45061 : PrimeValue := ⟨45061, pr45061⟩
private theorem pr45077 : PrimeCertificate 45077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59,pv191]) (by decide +kernel)
def pv45077 : PrimeValue := ⟨45077, pr45077⟩
private theorem pr45083 : PrimeCertificate 45083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv22541]) (by decide +kernel)
def pv45083 : PrimeValue := ⟨45083, pr45083⟩
private theorem pr45119 : PrimeCertificate 45119 :=
  certifyPrime (q := pv7) (ls := [pv2,pv17,pv1327]) (by decide +kernel)
def pv45119 : PrimeValue := ⟨45119, pr45119⟩
private theorem pr45121 : PrimeCertificate 45121 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv47]) (by decide +kernel)
def pv45121 : PrimeValue := ⟨45121, pr45121⟩
private theorem pr45127 : PrimeCertificate 45127 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv23,pv109]) (by decide +kernel)
def pv45127 : PrimeValue := ⟨45127, pr45127⟩
private theorem pr45131 : PrimeCertificate 45131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv4513]) (by decide +kernel)
def pv45131 : PrimeValue := ⟨45131, pr45131⟩
private theorem pr45137 : PrimeCertificate 45137 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv13,pv31]) (by decide +kernel)
def pv45137 : PrimeValue := ⟨45137, pr45137⟩
private theorem pr45139 : PrimeCertificate 45139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7523]) (by decide +kernel)
def pv45139 : PrimeValue := ⟨45139, pr45139⟩
private theorem pr45161 : PrimeCertificate 45161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1129]) (by decide +kernel)
def pv45161 : PrimeValue := ⟨45161, pr45161⟩
private theorem pr45179 : PrimeCertificate 45179 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv461]) (by decide +kernel)
def pv45179 : PrimeValue := ⟨45179, pr45179⟩
private theorem pr45181 : PrimeCertificate 45181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv251]) (by decide +kernel)
def pv45181 : PrimeValue := ⟨45181, pr45181⟩
private theorem pr45191 : PrimeCertificate 45191 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv4519]) (by decide +kernel)
def pv45191 : PrimeValue := ⟨45191, pr45191⟩
private theorem pr45197 : PrimeCertificate 45197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11299]) (by decide +kernel)
def pv45197 : PrimeValue := ⟨45197, pr45197⟩
private theorem pr45233 : PrimeCertificate 45233 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv257]) (by decide +kernel)
def pv45233 : PrimeValue := ⟨45233, pr45233⟩
private theorem pr45247 : PrimeCertificate 45247 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7541]) (by decide +kernel)
def pv45247 : PrimeValue := ⟨45247, pr45247⟩
private theorem pr45259 : PrimeCertificate 45259 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv397]) (by decide +kernel)
def pv45259 : PrimeValue := ⟨45259, pr45259⟩
private theorem pr45263 : PrimeCertificate 45263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv53,pv61]) (by decide +kernel)
def pv45263 : PrimeValue := ⟨45263, pr45263⟩
private theorem pr45281 : PrimeCertificate 45281 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv283]) (by decide +kernel)
def pv45281 : PrimeValue := ⟨45281, pr45281⟩
private theorem pr45289 : PrimeCertificate 45289 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv17,pv37]) (by decide +kernel)
def pv45289 : PrimeValue := ⟨45289, pr45289⟩
private theorem pr45293 : PrimeCertificate 45293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv67]) (by decide +kernel)
def pv45293 : PrimeValue := ⟨45293, pr45293⟩
private theorem pr45307 : PrimeCertificate 45307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv839]) (by decide +kernel)
def pv45307 : PrimeValue := ⟨45307, pr45307⟩
private theorem pr45317 : PrimeCertificate 45317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11329]) (by decide +kernel)
def pv45317 : PrimeValue := ⟨45317, pr45317⟩
private theorem pr45319 : PrimeCertificate 45319 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv83]) (by decide +kernel)
def pv45319 : PrimeValue := ⟨45319, pr45319⟩
private theorem pr45329 : PrimeCertificate 45329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2833]) (by decide +kernel)
def pv45329 : PrimeValue := ⟨45329, pr45329⟩
private theorem pr45337 : PrimeCertificate 45337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1889]) (by decide +kernel)
def pv45337 : PrimeValue := ⟨45337, pr45337⟩
private theorem pr45341 : PrimeCertificate 45341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv2267]) (by decide +kernel)
def pv45341 : PrimeValue := ⟨45341, pr45341⟩
private theorem pr45343 : PrimeCertificate 45343 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv229]) (by decide +kernel)
def pv45343 : PrimeValue := ⟨45343, pr45343⟩
private theorem pr45361 : PrimeCertificate 45361 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv45361 : PrimeValue := ⟨45361, pr45361⟩
private theorem pr45377 : PrimeCertificate 45377 :=
  certifyPrime (q := pv3) (ls := [pv2,pv709]) (by decide +kernel)
def pv45377 : PrimeValue := ⟨45377, pr45377⟩
private theorem pr45389 : PrimeCertificate 45389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv1621]) (by decide +kernel)
def pv45389 : PrimeValue := ⟨45389, pr45389⟩
private theorem pr45403 : PrimeCertificate 45403 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv23,pv47]) (by decide +kernel)
def pv45403 : PrimeValue := ⟨45403, pr45403⟩
private theorem pr45413 : PrimeCertificate 45413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11353]) (by decide +kernel)
def pv45413 : PrimeValue := ⟨45413, pr45413⟩
private theorem pr45427 : PrimeCertificate 45427 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv67,pv113]) (by decide +kernel)
def pv45427 : PrimeValue := ⟨45427, pr45427⟩
private theorem pr45433 : PrimeCertificate 45433 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv631]) (by decide +kernel)
def pv45433 : PrimeValue := ⟨45433, pr45433⟩
private theorem pr45439 : PrimeCertificate 45439 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7573]) (by decide +kernel)
def pv45439 : PrimeValue := ⟨45439, pr45439⟩
private theorem pr45481 : PrimeCertificate 45481 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv379]) (by decide +kernel)
def pv45481 : PrimeValue := ⟨45481, pr45481⟩
private theorem pr45491 : PrimeCertificate 45491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv4549]) (by decide +kernel)
def pv45491 : PrimeValue := ⟨45491, pr45491⟩
private theorem pr45497 : PrimeCertificate 45497 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv47]) (by decide +kernel)
def pv45497 : PrimeValue := ⟨45497, pr45497⟩
private theorem pr45503 : PrimeCertificate 45503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv22751]) (by decide +kernel)
def pv45503 : PrimeValue := ⟨45503, pr45503⟩
private theorem pr45523 : PrimeCertificate 45523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv281]) (by decide +kernel)
def pv45523 : PrimeValue := ⟨45523, pr45523⟩
private theorem pr45533 : PrimeCertificate 45533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11383]) (by decide +kernel)
def pv45533 : PrimeValue := ⟨45533, pr45533⟩
private theorem pr45541 : PrimeCertificate 45541 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv11,pv23]) (by decide +kernel)
def pv45541 : PrimeValue := ⟨45541, pr45541⟩
private theorem pr45553 : PrimeCertificate 45553 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv73]) (by decide +kernel)
def pv45553 : PrimeValue := ⟨45553, pr45553⟩
private theorem pr45557 : PrimeCertificate 45557 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv1627]) (by decide +kernel)
def pv45557 : PrimeValue := ⟨45557, pr45557⟩
private theorem pr45569 : PrimeCertificate 45569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv89]) (by decide +kernel)
def pv45569 : PrimeValue := ⟨45569, pr45569⟩
private theorem pr45587 : PrimeCertificate 45587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv991]) (by decide +kernel)
def pv45587 : PrimeValue := ⟨45587, pr45587⟩
private theorem pr45589 : PrimeCertificate 45589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv131]) (by decide +kernel)
def pv45589 : PrimeValue := ⟨45589, pr45589⟩
private theorem pr45599 : PrimeCertificate 45599 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv3257]) (by decide +kernel)
def pv45599 : PrimeValue := ⟨45599, pr45599⟩
private theorem pr45613 : PrimeCertificate 45613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv181]) (by decide +kernel)
def pv45613 : PrimeValue := ⟨45613, pr45613⟩
private theorem pr45631 : PrimeCertificate 45631 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv45631 : PrimeValue := ⟨45631, pr45631⟩
private theorem pr45641 : PrimeCertificate 45641 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv163]) (by decide +kernel)
def pv45641 : PrimeValue := ⟨45641, pr45641⟩
private theorem pr45659 : PrimeCertificate 45659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv617]) (by decide +kernel)
def pv45659 : PrimeValue := ⟨45659, pr45659⟩
private theorem pr45667 : PrimeCertificate 45667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv59]) (by decide +kernel)
def pv45667 : PrimeValue := ⟨45667, pr45667⟩
private theorem pr45673 : PrimeCertificate 45673 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv173]) (by decide +kernel)
def pv45673 : PrimeValue := ⟨45673, pr45673⟩
private theorem pr45677 : PrimeCertificate 45677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv601]) (by decide +kernel)
def pv45677 : PrimeValue := ⟨45677, pr45677⟩
private theorem pr45691 : PrimeCertificate 45691 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv1523]) (by decide +kernel)
def pv45691 : PrimeValue := ⟨45691, pr45691⟩
private theorem pr45697 : PrimeCertificate 45697 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv17]) (by decide +kernel)
def pv45697 : PrimeValue := ⟨45697, pr45697⟩
private theorem pr45707 : PrimeCertificate 45707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv22853]) (by decide +kernel)
def pv45707 : PrimeValue := ⟨45707, pr45707⟩
private theorem pr45737 : PrimeCertificate 45737 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5717]) (by decide +kernel)
def pv45737 : PrimeValue := ⟨45737, pr45737⟩
private theorem pr45751 : PrimeCertificate 45751 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv61]) (by decide +kernel)
def pv45751 : PrimeValue := ⟨45751, pr45751⟩
private theorem pr45757 : PrimeCertificate 45757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv41]) (by decide +kernel)
def pv45757 : PrimeValue := ⟨45757, pr45757⟩
private theorem pr45763 : PrimeCertificate 45763 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29,pv263]) (by decide +kernel)
def pv45763 : PrimeValue := ⟨45763, pr45763⟩
private theorem pr45767 : PrimeCertificate 45767 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv467]) (by decide +kernel)
def pv45767 : PrimeValue := ⟨45767, pr45767⟩
private theorem pr45779 : PrimeCertificate 45779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv487]) (by decide +kernel)
def pv45779 : PrimeValue := ⟨45779, pr45779⟩
private theorem pr45817 : PrimeCertificate 45817 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv83]) (by decide +kernel)
def pv45817 : PrimeValue := ⟨45817, pr45817⟩
private theorem pr45821 : PrimeCertificate 45821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29,pv79]) (by decide +kernel)
def pv45821 : PrimeValue := ⟨45821, pr45821⟩
private theorem pr45823 : PrimeCertificate 45823 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv1091]) (by decide +kernel)
def pv45823 : PrimeValue := ⟨45823, pr45823⟩
private theorem pr45827 : PrimeCertificate 45827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv2083]) (by decide +kernel)
def pv45827 : PrimeValue := ⟨45827, pr45827⟩
private theorem pr45833 : PrimeCertificate 45833 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv337]) (by decide +kernel)
def pv45833 : PrimeValue := ⟨45833, pr45833⟩
private theorem pr45841 : PrimeCertificate 45841 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv191]) (by decide +kernel)
def pv45841 : PrimeValue := ⟨45841, pr45841⟩
private theorem pr45853 : PrimeCertificate 45853 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3821]) (by decide +kernel)
def pv45853 : PrimeValue := ⟨45853, pr45853⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
