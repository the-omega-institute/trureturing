/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table005
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table005.pv10181
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table003

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr10181 : PrimeCertificate 10181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv509]) (by decide +kernel)
def pv10181 : PrimeValue := ⟨10181, pr10181⟩
private theorem pr10193 : PrimeCertificate 10193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv13]) (by decide +kernel)
def pv10193 : PrimeValue := ⟨10193, pr10193⟩
private theorem pr10211 : PrimeCertificate 10211 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv1021]) (by decide +kernel)
def pv10211 : PrimeValue := ⟨10211, pr10211⟩
private theorem pr10223 : PrimeCertificate 10223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv269]) (by decide +kernel)
def pv10223 : PrimeValue := ⟨10223, pr10223⟩
private theorem pr10243 : PrimeCertificate 10243 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv569]) (by decide +kernel)
def pv10243 : PrimeValue := ⟨10243, pr10243⟩
private theorem pr10247 : PrimeCertificate 10247 :=
  certifyPrime (q := pv5) (ls := [pv2,pv47,pv109]) (by decide +kernel)
def pv10247 : PrimeValue := ⟨10247, pr10247⟩
private theorem pr10253 : PrimeCertificate 10253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv233]) (by decide +kernel)
def pv10253 : PrimeValue := ⟨10253, pr10253⟩
private theorem pr10259 : PrimeCertificate 10259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv223]) (by decide +kernel)
def pv10259 : PrimeValue := ⟨10259, pr10259⟩
private theorem pr10267 : PrimeCertificate 10267 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv59]) (by decide +kernel)
def pv10267 : PrimeValue := ⟨10267, pr10267⟩
private theorem pr10271 : PrimeCertificate 10271 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv79]) (by decide +kernel)
def pv10271 : PrimeValue := ⟨10271, pr10271⟩
private theorem pr10273 : PrimeCertificate 10273 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv107]) (by decide +kernel)
def pv10273 : PrimeValue := ⟨10273, pr10273⟩
private theorem pr10289 : PrimeCertificate 10289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv643]) (by decide +kernel)
def pv10289 : PrimeValue := ⟨10289, pr10289⟩
private theorem pr10301 : PrimeCertificate 10301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv103]) (by decide +kernel)
def pv10301 : PrimeValue := ⟨10301, pr10301⟩
private theorem pr10303 : PrimeCertificate 10303 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv101]) (by decide +kernel)
def pv10303 : PrimeValue := ⟨10303, pr10303⟩
private theorem pr10313 : PrimeCertificate 10313 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1289]) (by decide +kernel)
def pv10313 : PrimeValue := ⟨10313, pr10313⟩
private theorem pr10321 : PrimeCertificate 10321 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv43]) (by decide +kernel)
def pv10321 : PrimeValue := ⟨10321, pr10321⟩
private theorem pr10331 : PrimeCertificate 10331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1033]) (by decide +kernel)
def pv10331 : PrimeValue := ⟨10331, pr10331⟩
private theorem pr10333 : PrimeCertificate 10333 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv41]) (by decide +kernel)
def pv10333 : PrimeValue := ⟨10333, pr10333⟩
private theorem pr10337 : PrimeCertificate 10337 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv19]) (by decide +kernel)
def pv10337 : PrimeValue := ⟨10337, pr10337⟩
private theorem pr10343 : PrimeCertificate 10343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv5171]) (by decide +kernel)
def pv10343 : PrimeValue := ⟨10343, pr10343⟩
private theorem pr10357 : PrimeCertificate 10357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv863]) (by decide +kernel)
def pv10357 : PrimeValue := ⟨10357, pr10357⟩
private theorem pr10369 : PrimeCertificate 10369 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3]) (by decide +kernel)
def pv10369 : PrimeValue := ⟨10369, pr10369⟩
private theorem pr10391 : PrimeCertificate 10391 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv1039]) (by decide +kernel)
def pv10391 : PrimeValue := ⟨10391, pr10391⟩
private theorem pr10399 : PrimeCertificate 10399 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1733]) (by decide +kernel)
def pv10399 : PrimeValue := ⟨10399, pr10399⟩
private theorem pr10427 : PrimeCertificate 10427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv401]) (by decide +kernel)
def pv10427 : PrimeValue := ⟨10427, pr10427⟩
private theorem pr10429 : PrimeCertificate 10429 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv79]) (by decide +kernel)
def pv10429 : PrimeValue := ⟨10429, pr10429⟩
private theorem pr10433 : PrimeCertificate 10433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv163]) (by decide +kernel)
def pv10433 : PrimeValue := ⟨10433, pr10433⟩
private theorem pr10453 : PrimeCertificate 10453 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv67]) (by decide +kernel)
def pv10453 : PrimeValue := ⟨10453, pr10453⟩
private theorem pr10457 : PrimeCertificate 10457 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1307]) (by decide +kernel)
def pv10457 : PrimeValue := ⟨10457, pr10457⟩
private theorem pr10459 : PrimeCertificate 10459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv83]) (by decide +kernel)
def pv10459 : PrimeValue := ⟨10459, pr10459⟩
private theorem pr10463 : PrimeCertificate 10463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv5231]) (by decide +kernel)
def pv10463 : PrimeValue := ⟨10463, pr10463⟩
private theorem pr10477 : PrimeCertificate 10477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv97]) (by decide +kernel)
def pv10477 : PrimeValue := ⟨10477, pr10477⟩
private theorem pr10487 : PrimeCertificate 10487 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv107]) (by decide +kernel)
def pv10487 : PrimeValue := ⟨10487, pr10487⟩
private theorem pr10499 : PrimeCertificate 10499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv181]) (by decide +kernel)
def pv10499 : PrimeValue := ⟨10499, pr10499⟩
private theorem pr10501 : PrimeCertificate 10501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv10501 : PrimeValue := ⟨10501, pr10501⟩
private theorem pr10513 : PrimeCertificate 10513 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv73]) (by decide +kernel)
def pv10513 : PrimeValue := ⟨10513, pr10513⟩
private theorem pr10529 : PrimeCertificate 10529 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv47]) (by decide +kernel)
def pv10529 : PrimeValue := ⟨10529, pr10529⟩
private theorem pr10531 : PrimeCertificate 10531 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv10531 : PrimeValue := ⟨10531, pr10531⟩
private theorem pr10559 : PrimeCertificate 10559 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5279]) (by decide +kernel)
def pv10559 : PrimeValue := ⟨10559, pr10559⟩
private theorem pr10567 : PrimeCertificate 10567 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv587]) (by decide +kernel)
def pv10567 : PrimeValue := ⟨10567, pr10567⟩
private theorem pr10589 : PrimeCertificate 10589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv2647]) (by decide +kernel)
def pv10589 : PrimeValue := ⟨10589, pr10589⟩
private theorem pr10597 : PrimeCertificate 10597 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv883]) (by decide +kernel)
def pv10597 : PrimeValue := ⟨10597, pr10597⟩
private theorem pr10601 : PrimeCertificate 10601 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv53]) (by decide +kernel)
def pv10601 : PrimeValue := ⟨10601, pr10601⟩
private theorem pr10607 : PrimeCertificate 10607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv5303]) (by decide +kernel)
def pv10607 : PrimeValue := ⟨10607, pr10607⟩
private theorem pr10613 : PrimeCertificate 10613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv379]) (by decide +kernel)
def pv10613 : PrimeValue := ⟨10613, pr10613⟩
private theorem pr10627 : PrimeCertificate 10627 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv23]) (by decide +kernel)
def pv10627 : PrimeValue := ⟨10627, pr10627⟩
private theorem pr10631 : PrimeCertificate 10631 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv1063]) (by decide +kernel)
def pv10631 : PrimeValue := ⟨10631, pr10631⟩
private theorem pr10639 : PrimeCertificate 10639 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv197]) (by decide +kernel)
def pv10639 : PrimeValue := ⟨10639, pr10639⟩
private theorem pr10651 : PrimeCertificate 10651 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv71]) (by decide +kernel)
def pv10651 : PrimeValue := ⟨10651, pr10651⟩
private theorem pr10657 : PrimeCertificate 10657 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv37]) (by decide +kernel)
def pv10657 : PrimeValue := ⟨10657, pr10657⟩
private theorem pr10663 : PrimeCertificate 10663 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1777]) (by decide +kernel)
def pv10663 : PrimeValue := ⟨10663, pr10663⟩
private theorem pr10667 : PrimeCertificate 10667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5333]) (by decide +kernel)
def pv10667 : PrimeValue := ⟨10667, pr10667⟩
private theorem pr10687 : PrimeCertificate 10687 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv137]) (by decide +kernel)
def pv10687 : PrimeValue := ⟨10687, pr10687⟩
private theorem pr10691 : PrimeCertificate 10691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1069]) (by decide +kernel)
def pv10691 : PrimeValue := ⟨10691, pr10691⟩
private theorem pr10709 : PrimeCertificate 10709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv2677]) (by decide +kernel)
def pv10709 : PrimeValue := ⟨10709, pr10709⟩
private theorem pr10711 : PrimeCertificate 10711 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv17]) (by decide +kernel)
def pv10711 : PrimeValue := ⟨10711, pr10711⟩
private theorem pr10723 : PrimeCertificate 10723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1787]) (by decide +kernel)
def pv10723 : PrimeValue := ⟨10723, pr10723⟩
private theorem pr10729 : PrimeCertificate 10729 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv149]) (by decide +kernel)
def pv10729 : PrimeValue := ⟨10729, pr10729⟩
private theorem pr10733 : PrimeCertificate 10733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv2683]) (by decide +kernel)
def pv10733 : PrimeValue := ⟨10733, pr10733⟩
private theorem pr10739 : PrimeCertificate 10739 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv13,pv59]) (by decide +kernel)
def pv10739 : PrimeValue := ⟨10739, pr10739⟩
private theorem pr10753 : PrimeCertificate 10753 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv10753 : PrimeValue := ⟨10753, pr10753⟩
private theorem pr10771 : PrimeCertificate 10771 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv359]) (by decide +kernel)
def pv10771 : PrimeValue := ⟨10771, pr10771⟩
private theorem pr10781 : PrimeCertificate 10781 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv7,pv11]) (by decide +kernel)
def pv10781 : PrimeValue := ⟨10781, pr10781⟩
private theorem pr10789 : PrimeCertificate 10789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv31]) (by decide +kernel)
def pv10789 : PrimeValue := ⟨10789, pr10789⟩
private theorem pr10799 : PrimeCertificate 10799 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5399]) (by decide +kernel)
def pv10799 : PrimeValue := ⟨10799, pr10799⟩
private theorem pr10831 : PrimeCertificate 10831 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv10831 : PrimeValue := ⟨10831, pr10831⟩
private theorem pr10837 : PrimeCertificate 10837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv43]) (by decide +kernel)
def pv10837 : PrimeValue := ⟨10837, pr10837⟩
private theorem pr10847 : PrimeCertificate 10847 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv17,pv29]) (by decide +kernel)
def pv10847 : PrimeValue := ⟨10847, pr10847⟩
private theorem pr10853 : PrimeCertificate 10853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv2713]) (by decide +kernel)
def pv10853 : PrimeValue := ⟨10853, pr10853⟩
private theorem pr10859 : PrimeCertificate 10859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv89]) (by decide +kernel)
def pv10859 : PrimeValue := ⟨10859, pr10859⟩
private theorem pr10861 : PrimeCertificate 10861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv181]) (by decide +kernel)
def pv10861 : PrimeValue := ⟨10861, pr10861⟩
private theorem pr10867 : PrimeCertificate 10867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1811]) (by decide +kernel)
def pv10867 : PrimeValue := ⟨10867, pr10867⟩
private theorem pr10883 : PrimeCertificate 10883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5441]) (by decide +kernel)
def pv10883 : PrimeValue := ⟨10883, pr10883⟩
private theorem pr10889 : PrimeCertificate 10889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1361]) (by decide +kernel)
def pv10889 : PrimeValue := ⟨10889, pr10889⟩
private theorem pr10891 : PrimeCertificate 10891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv10891 : PrimeValue := ⟨10891, pr10891⟩
private theorem pr10903 : PrimeCertificate 10903 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv79]) (by decide +kernel)
def pv10903 : PrimeValue := ⟨10903, pr10903⟩
private theorem pr10909 : PrimeCertificate 10909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv101]) (by decide +kernel)
def pv10909 : PrimeValue := ⟨10909, pr10909⟩
private theorem pr10937 : PrimeCertificate 10937 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1367]) (by decide +kernel)
def pv10937 : PrimeValue := ⟨10937, pr10937⟩
private theorem pr10939 : PrimeCertificate 10939 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1823]) (by decide +kernel)
def pv10939 : PrimeValue := ⟨10939, pr10939⟩
private theorem pr10949 : PrimeCertificate 10949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv17,pv23]) (by decide +kernel)
def pv10949 : PrimeValue := ⟨10949, pr10949⟩
private theorem pr10957 : PrimeCertificate 10957 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv83]) (by decide +kernel)
def pv10957 : PrimeValue := ⟨10957, pr10957⟩
private theorem pr10973 : PrimeCertificate 10973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv211]) (by decide +kernel)
def pv10973 : PrimeValue := ⟨10973, pr10973⟩
private theorem pr10979 : PrimeCertificate 10979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv499]) (by decide +kernel)
def pv10979 : PrimeValue := ⟨10979, pr10979⟩
private theorem pr10987 : PrimeCertificate 10987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1831]) (by decide +kernel)
def pv10987 : PrimeValue := ⟨10987, pr10987⟩
private theorem pr10993 : PrimeCertificate 10993 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv229]) (by decide +kernel)
def pv10993 : PrimeValue := ⟨10993, pr10993⟩
private theorem pr11003 : PrimeCertificate 11003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5501]) (by decide +kernel)
def pv11003 : PrimeValue := ⟨11003, pr11003⟩
private theorem pr11027 : PrimeCertificate 11027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv149]) (by decide +kernel)
def pv11027 : PrimeValue := ⟨11027, pr11027⟩
private theorem pr11047 : PrimeCertificate 11047 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv263]) (by decide +kernel)
def pv11047 : PrimeValue := ⟨11047, pr11047⟩
private theorem pr11057 : PrimeCertificate 11057 :=
  certifyPrime (q := pv3) (ls := [pv2,pv691]) (by decide +kernel)
def pv11057 : PrimeValue := ⟨11057, pr11057⟩
private theorem pr11059 : PrimeCertificate 11059 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv19,pv97]) (by decide +kernel)
def pv11059 : PrimeValue := ⟨11059, pr11059⟩
private theorem pr11069 : PrimeCertificate 11069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv2767]) (by decide +kernel)
def pv11069 : PrimeValue := ⟨11069, pr11069⟩
private theorem pr11071 : PrimeCertificate 11071 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv41]) (by decide +kernel)
def pv11071 : PrimeValue := ⟨11071, pr11071⟩
private theorem pr11083 : PrimeCertificate 11083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1847]) (by decide +kernel)
def pv11083 : PrimeValue := ⟨11083, pr11083⟩
private theorem pr11087 : PrimeCertificate 11087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv241]) (by decide +kernel)
def pv11087 : PrimeValue := ⟨11087, pr11087⟩
private theorem pr11093 : PrimeCertificate 11093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv59]) (by decide +kernel)
def pv11093 : PrimeValue := ⟨11093, pr11093⟩
private theorem pr11113 : PrimeCertificate 11113 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv463]) (by decide +kernel)
def pv11113 : PrimeValue := ⟨11113, pr11113⟩
private theorem pr11117 : PrimeCertificate 11117 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv397]) (by decide +kernel)
def pv11117 : PrimeValue := ⟨11117, pr11117⟩
private theorem pr11119 : PrimeCertificate 11119 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv109]) (by decide +kernel)
def pv11119 : PrimeValue := ⟨11119, pr11119⟩
private theorem pr11131 : PrimeCertificate 11131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv53]) (by decide +kernel)
def pv11131 : PrimeValue := ⟨11131, pr11131⟩
private theorem pr11149 : PrimeCertificate 11149 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv929]) (by decide +kernel)
def pv11149 : PrimeValue := ⟨11149, pr11149⟩
private theorem pr11159 : PrimeCertificate 11159 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv797]) (by decide +kernel)
def pv11159 : PrimeValue := ⟨11159, pr11159⟩
private theorem pr11161 : PrimeCertificate 11161 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv31]) (by decide +kernel)
def pv11161 : PrimeValue := ⟨11161, pr11161⟩
private theorem pr11171 : PrimeCertificate 11171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1117]) (by decide +kernel)
def pv11171 : PrimeValue := ⟨11171, pr11171⟩
private theorem pr11173 : PrimeCertificate 11173 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv19]) (by decide +kernel)
def pv11173 : PrimeValue := ⟨11173, pr11173⟩
private theorem pr11177 : PrimeCertificate 11177 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv127]) (by decide +kernel)
def pv11177 : PrimeValue := ⟨11177, pr11177⟩
private theorem pr11197 : PrimeCertificate 11197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv311]) (by decide +kernel)
def pv11197 : PrimeValue := ⟨11197, pr11197⟩
private theorem pr11213 : PrimeCertificate 11213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv2803]) (by decide +kernel)
def pv11213 : PrimeValue := ⟨11213, pr11213⟩
private theorem pr11239 : PrimeCertificate 11239 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1873]) (by decide +kernel)
def pv11239 : PrimeValue := ⟨11239, pr11239⟩
private theorem pr11243 : PrimeCertificate 11243 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11,pv73]) (by decide +kernel)
def pv11243 : PrimeValue := ⟨11243, pr11243⟩
private theorem pr11251 : PrimeCertificate 11251 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv11251 : PrimeValue := ⟨11251, pr11251⟩
private theorem pr11257 : PrimeCertificate 11257 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv67]) (by decide +kernel)
def pv11257 : PrimeValue := ⟨11257, pr11257⟩
private theorem pr11261 : PrimeCertificate 11261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv563]) (by decide +kernel)
def pv11261 : PrimeValue := ⟨11261, pr11261⟩
private theorem pr11273 : PrimeCertificate 11273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1409]) (by decide +kernel)
def pv11273 : PrimeValue := ⟨11273, pr11273⟩
private theorem pr11279 : PrimeCertificate 11279 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5639]) (by decide +kernel)
def pv11279 : PrimeValue := ⟨11279, pr11279⟩
private theorem pr11287 : PrimeCertificate 11287 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv19]) (by decide +kernel)
def pv11287 : PrimeValue := ⟨11287, pr11287⟩
private theorem pr11299 : PrimeCertificate 11299 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv269]) (by decide +kernel)
def pv11299 : PrimeValue := ⟨11299, pr11299⟩
private theorem pr11311 : PrimeCertificate 11311 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv29]) (by decide +kernel)
def pv11311 : PrimeValue := ⟨11311, pr11311⟩
private theorem pr11317 : PrimeCertificate 11317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv41]) (by decide +kernel)
def pv11317 : PrimeValue := ⟨11317, pr11317⟩
private theorem pr11321 : PrimeCertificate 11321 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv283]) (by decide +kernel)
def pv11321 : PrimeValue := ⟨11321, pr11321⟩
private theorem pr11329 : PrimeCertificate 11329 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv59]) (by decide +kernel)
def pv11329 : PrimeValue := ⟨11329, pr11329⟩
private theorem pr11351 : PrimeCertificate 11351 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv227]) (by decide +kernel)
def pv11351 : PrimeValue := ⟨11351, pr11351⟩
private theorem pr11353 : PrimeCertificate 11353 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv43]) (by decide +kernel)
def pv11353 : PrimeValue := ⟨11353, pr11353⟩
private theorem pr11369 : PrimeCertificate 11369 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv29]) (by decide +kernel)
def pv11369 : PrimeValue := ⟨11369, pr11369⟩
private theorem pr11383 : PrimeCertificate 11383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv271]) (by decide +kernel)
def pv11383 : PrimeValue := ⟨11383, pr11383⟩
private theorem pr11393 : PrimeCertificate 11393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv89]) (by decide +kernel)
def pv11393 : PrimeValue := ⟨11393, pr11393⟩
private theorem pr11399 : PrimeCertificate 11399 :=
  certifyPrime (q := pv11) (ls := [pv2,pv41,pv139]) (by decide +kernel)
def pv11399 : PrimeValue := ⟨11399, pr11399⟩
private theorem pr11411 : PrimeCertificate 11411 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv163]) (by decide +kernel)
def pv11411 : PrimeValue := ⟨11411, pr11411⟩
private theorem pr11423 : PrimeCertificate 11423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv5711]) (by decide +kernel)
def pv11423 : PrimeValue := ⟨11423, pr11423⟩
private theorem pr11437 : PrimeCertificate 11437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv953]) (by decide +kernel)
def pv11437 : PrimeValue := ⟨11437, pr11437⟩
private theorem pr11443 : PrimeCertificate 11443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1907]) (by decide +kernel)
def pv11443 : PrimeValue := ⟨11443, pr11443⟩
private theorem pr11447 : PrimeCertificate 11447 :=
  certifyPrime (q := pv5) (ls := [pv2,pv59,pv97]) (by decide +kernel)
def pv11447 : PrimeValue := ⟨11447, pr11447⟩
private theorem pr11467 : PrimeCertificate 11467 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv13]) (by decide +kernel)
def pv11467 : PrimeValue := ⟨11467, pr11467⟩
private theorem pr11471 : PrimeCertificate 11471 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv31,pv37]) (by decide +kernel)
def pv11471 : PrimeValue := ⟨11471, pr11471⟩
private theorem pr11483 : PrimeCertificate 11483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5741]) (by decide +kernel)
def pv11483 : PrimeValue := ⟨11483, pr11483⟩
private theorem pr11489 : PrimeCertificate 11489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv359]) (by decide +kernel)
def pv11489 : PrimeValue := ⟨11489, pr11489⟩
private theorem pr11491 : PrimeCertificate 11491 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv383]) (by decide +kernel)
def pv11491 : PrimeValue := ⟨11491, pr11491⟩
private theorem pr11497 : PrimeCertificate 11497 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv479]) (by decide +kernel)
def pv11497 : PrimeValue := ⟨11497, pr11497⟩
private theorem pr11503 : PrimeCertificate 11503 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv71]) (by decide +kernel)
def pv11503 : PrimeValue := ⟨11503, pr11503⟩
private theorem pr11519 : PrimeCertificate 11519 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv443]) (by decide +kernel)
def pv11519 : PrimeValue := ⟨11519, pr11519⟩
private theorem pr11527 : PrimeCertificate 11527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv113]) (by decide +kernel)
def pv11527 : PrimeValue := ⟨11527, pr11527⟩
private theorem pr11549 : PrimeCertificate 11549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv2887]) (by decide +kernel)
def pv11549 : PrimeValue := ⟨11549, pr11549⟩
private theorem pr11551 : PrimeCertificate 11551 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv11]) (by decide +kernel)
def pv11551 : PrimeValue := ⟨11551, pr11551⟩
private theorem pr11579 : PrimeCertificate 11579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv827]) (by decide +kernel)
def pv11579 : PrimeValue := ⟨11579, pr11579⟩
private theorem pr11587 : PrimeCertificate 11587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1931]) (by decide +kernel)
def pv11587 : PrimeValue := ⟨11587, pr11587⟩
private theorem pr11593 : PrimeCertificate 11593 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv23]) (by decide +kernel)
def pv11593 : PrimeValue := ⟨11593, pr11593⟩
private theorem pr11597 : PrimeCertificate 11597 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv223]) (by decide +kernel)
def pv11597 : PrimeValue := ⟨11597, pr11597⟩
private theorem pr11617 : PrimeCertificate 11617 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv11617 : PrimeValue := ⟨11617, pr11617⟩
private theorem pr11621 : PrimeCertificate 11621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv83]) (by decide +kernel)
def pv11621 : PrimeValue := ⟨11621, pr11621⟩
private theorem pr11633 : PrimeCertificate 11633 :=
  certifyPrime (q := pv3) (ls := [pv2,pv727]) (by decide +kernel)
def pv11633 : PrimeValue := ⟨11633, pr11633⟩
private theorem pr11657 : PrimeCertificate 11657 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv47]) (by decide +kernel)
def pv11657 : PrimeValue := ⟨11657, pr11657⟩
private theorem pr11677 : PrimeCertificate 11677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv139]) (by decide +kernel)
def pv11677 : PrimeValue := ⟨11677, pr11677⟩
private theorem pr11681 : PrimeCertificate 11681 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv73]) (by decide +kernel)
def pv11681 : PrimeValue := ⟨11681, pr11681⟩
private theorem pr11689 : PrimeCertificate 11689 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv487]) (by decide +kernel)
def pv11689 : PrimeValue := ⟨11689, pr11689⟩
private theorem pr11699 : PrimeCertificate 11699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5849]) (by decide +kernel)
def pv11699 : PrimeValue := ⟨11699, pr11699⟩
private theorem pr11701 : PrimeCertificate 11701 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv11701 : PrimeValue := ⟨11701, pr11701⟩
private theorem pr11717 : PrimeCertificate 11717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv101]) (by decide +kernel)
def pv11717 : PrimeValue := ⟨11717, pr11717⟩
private theorem pr11719 : PrimeCertificate 11719 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv7,pv31]) (by decide +kernel)
def pv11719 : PrimeValue := ⟨11719, pr11719⟩
private theorem pr11731 : PrimeCertificate 11731 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv17,pv23]) (by decide +kernel)
def pv11731 : PrimeValue := ⟨11731, pr11731⟩
private theorem pr11743 : PrimeCertificate 11743 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv103]) (by decide +kernel)
def pv11743 : PrimeValue := ⟨11743, pr11743⟩
private theorem pr11777 : PrimeCertificate 11777 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23]) (by decide +kernel)
def pv11777 : PrimeValue := ⟨11777, pr11777⟩
private theorem pr11779 : PrimeCertificate 11779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv151]) (by decide +kernel)
def pv11779 : PrimeValue := ⟨11779, pr11779⟩
private theorem pr11783 : PrimeCertificate 11783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv43,pv137]) (by decide +kernel)
def pv11783 : PrimeValue := ⟨11783, pr11783⟩
private theorem pr11789 : PrimeCertificate 11789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv421]) (by decide +kernel)
def pv11789 : PrimeValue := ⟨11789, pr11789⟩
private theorem pr11801 : PrimeCertificate 11801 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv59]) (by decide +kernel)
def pv11801 : PrimeValue := ⟨11801, pr11801⟩
private theorem pr11807 : PrimeCertificate 11807 :=
  certifyPrime (q := pv5) (ls := [pv2,pv5903]) (by decide +kernel)
def pv11807 : PrimeValue := ⟨11807, pr11807⟩
private theorem pr11813 : PrimeCertificate 11813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv2953]) (by decide +kernel)
def pv11813 : PrimeValue := ⟨11813, pr11813⟩
private theorem pr11821 : PrimeCertificate 11821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv197]) (by decide +kernel)
def pv11821 : PrimeValue := ⟨11821, pr11821⟩
private theorem pr11827 : PrimeCertificate 11827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv73]) (by decide +kernel)
def pv11827 : PrimeValue := ⟨11827, pr11827⟩
private theorem pr11831 : PrimeCertificate 11831 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv13]) (by decide +kernel)
def pv11831 : PrimeValue := ⟨11831, pr11831⟩
private theorem pr11833 : PrimeCertificate 11833 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv29]) (by decide +kernel)
def pv11833 : PrimeValue := ⟨11833, pr11833⟩
private theorem pr11839 : PrimeCertificate 11839 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1973]) (by decide +kernel)
def pv11839 : PrimeValue := ⟨11839, pr11839⟩
private theorem pr11863 : PrimeCertificate 11863 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv659]) (by decide +kernel)
def pv11863 : PrimeValue := ⟨11863, pr11863⟩
private theorem pr11867 : PrimeCertificate 11867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv349]) (by decide +kernel)
def pv11867 : PrimeValue := ⟨11867, pr11867⟩
private theorem pr11887 : PrimeCertificate 11887 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv283]) (by decide +kernel)
def pv11887 : PrimeValue := ⟨11887, pr11887⟩
private theorem pr11897 : PrimeCertificate 11897 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1487]) (by decide +kernel)
def pv11897 : PrimeValue := ⟨11897, pr11897⟩
private theorem pr11903 : PrimeCertificate 11903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv541]) (by decide +kernel)
def pv11903 : PrimeValue := ⟨11903, pr11903⟩
private theorem pr11909 : PrimeCertificate 11909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv229]) (by decide +kernel)
def pv11909 : PrimeValue := ⟨11909, pr11909⟩
private theorem pr11923 : PrimeCertificate 11923 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1987]) (by decide +kernel)
def pv11923 : PrimeValue := ⟨11923, pr11923⟩
private theorem pr11927 : PrimeCertificate 11927 :=
  certifyPrime (q := pv5) (ls := [pv2,pv67,pv89]) (by decide +kernel)
def pv11927 : PrimeValue := ⟨11927, pr11927⟩
private theorem pr11933 : PrimeCertificate 11933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv157]) (by decide +kernel)
def pv11933 : PrimeValue := ⟨11933, pr11933⟩
private theorem pr11939 : PrimeCertificate 11939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv127]) (by decide +kernel)
def pv11939 : PrimeValue := ⟨11939, pr11939⟩
private theorem pr11941 : PrimeCertificate 11941 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv199]) (by decide +kernel)
def pv11941 : PrimeValue := ⟨11941, pr11941⟩
private theorem pr11953 : PrimeCertificate 11953 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv83]) (by decide +kernel)
def pv11953 : PrimeValue := ⟨11953, pr11953⟩
private theorem pr11959 : PrimeCertificate 11959 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1993]) (by decide +kernel)
def pv11959 : PrimeValue := ⟨11959, pr11959⟩
private theorem pr11969 : PrimeCertificate 11969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv17]) (by decide +kernel)
def pv11969 : PrimeValue := ⟨11969, pr11969⟩
private theorem pr11971 : PrimeCertificate 11971 :=
  certifyPrime (q := pv79) (ls := [pv2,pv3,pv5,pv7,pv19]) (by decide +kernel)
def pv11971 : PrimeValue := ⟨11971, pr11971⟩
private theorem pr11981 : PrimeCertificate 11981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv599]) (by decide +kernel)
def pv11981 : PrimeValue := ⟨11981, pr11981⟩
private theorem pr11987 : PrimeCertificate 11987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv461]) (by decide +kernel)
def pv11987 : PrimeValue := ⟨11987, pr11987⟩
private theorem pr12007 : PrimeCertificate 12007 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv23,pv29]) (by decide +kernel)
def pv12007 : PrimeValue := ⟨12007, pr12007⟩
private theorem pr12011 : PrimeCertificate 12011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1201]) (by decide +kernel)
def pv12011 : PrimeValue := ⟨12011, pr12011⟩
private theorem pr12037 : PrimeCertificate 12037 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv59]) (by decide +kernel)
def pv12037 : PrimeValue := ⟨12037, pr12037⟩
private theorem pr12041 : PrimeCertificate 12041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv43]) (by decide +kernel)
def pv12041 : PrimeValue := ⟨12041, pr12041⟩
private theorem pr12043 : PrimeCertificate 12043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv223]) (by decide +kernel)
def pv12043 : PrimeValue := ⟨12043, pr12043⟩
private theorem pr12049 : PrimeCertificate 12049 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv251]) (by decide +kernel)
def pv12049 : PrimeValue := ⟨12049, pr12049⟩
private theorem pr12071 : PrimeCertificate 12071 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv17,pv71]) (by decide +kernel)
def pv12071 : PrimeValue := ⟨12071, pr12071⟩
private theorem pr12073 : PrimeCertificate 12073 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv503]) (by decide +kernel)
def pv12073 : PrimeValue := ⟨12073, pr12073⟩
private theorem pr12097 : PrimeCertificate 12097 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv12097 : PrimeValue := ⟨12097, pr12097⟩
private theorem pr12101 : PrimeCertificate 12101 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11]) (by decide +kernel)
def pv12101 : PrimeValue := ⟨12101, pr12101⟩
private theorem pr12107 : PrimeCertificate 12107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv6053]) (by decide +kernel)
def pv12107 : PrimeValue := ⟨12107, pr12107⟩
private theorem pr12109 : PrimeCertificate 12109 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1009]) (by decide +kernel)
def pv12109 : PrimeValue := ⟨12109, pr12109⟩
private theorem pr12113 : PrimeCertificate 12113 :=
  certifyPrime (q := pv3) (ls := [pv2,pv757]) (by decide +kernel)
def pv12113 : PrimeValue := ⟨12113, pr12113⟩
private theorem pr12119 : PrimeCertificate 12119 :=
  certifyPrime (q := pv7) (ls := [pv2,pv73,pv83]) (by decide +kernel)
def pv12119 : PrimeValue := ⟨12119, pr12119⟩
private theorem pr12143 : PrimeCertificate 12143 :=
  certifyPrime (q := pv17) (ls := [pv2,pv13,pv467]) (by decide +kernel)
def pv12143 : PrimeValue := ⟨12143, pr12143⟩
private theorem pr12149 : PrimeCertificate 12149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3037]) (by decide +kernel)
def pv12149 : PrimeValue := ⟨12149, pr12149⟩
private theorem pr12157 : PrimeCertificate 12157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1013]) (by decide +kernel)
def pv12157 : PrimeValue := ⟨12157, pr12157⟩
private theorem pr12161 : PrimeCertificate 12161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv19]) (by decide +kernel)
def pv12161 : PrimeValue := ⟨12161, pr12161⟩
private theorem pr12163 : PrimeCertificate 12163 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2027]) (by decide +kernel)
def pv12163 : PrimeValue := ⟨12163, pr12163⟩
private theorem pr12197 : PrimeCertificate 12197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3049]) (by decide +kernel)
def pv12197 : PrimeValue := ⟨12197, pr12197⟩
private theorem pr12203 : PrimeCertificate 12203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv6101]) (by decide +kernel)
def pv12203 : PrimeValue := ⟨12203, pr12203⟩
private theorem pr12211 : PrimeCertificate 12211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv37]) (by decide +kernel)
def pv12211 : PrimeValue := ⟨12211, pr12211⟩
private theorem pr12227 : PrimeCertificate 12227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv6113]) (by decide +kernel)
def pv12227 : PrimeValue := ⟨12227, pr12227⟩
private theorem pr12239 : PrimeCertificate 12239 :=
  certifyPrime (q := pv13) (ls := [pv2,pv29,pv211]) (by decide +kernel)
def pv12239 : PrimeValue := ⟨12239, pr12239⟩
private theorem pr12241 : PrimeCertificate 12241 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv12241 : PrimeValue := ⟨12241, pr12241⟩
private theorem pr12251 : PrimeCertificate 12251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7]) (by decide +kernel)
def pv12251 : PrimeValue := ⟨12251, pr12251⟩
private theorem pr12253 : PrimeCertificate 12253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1021]) (by decide +kernel)
def pv12253 : PrimeValue := ⟨12253, pr12253⟩
private theorem pr12263 : PrimeCertificate 12263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv6131]) (by decide +kernel)
def pv12263 : PrimeValue := ⟨12263, pr12263⟩
private theorem pr12269 : PrimeCertificate 12269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3067]) (by decide +kernel)
def pv12269 : PrimeValue := ⟨12269, pr12269⟩
private theorem pr12277 : PrimeCertificate 12277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv31]) (by decide +kernel)
def pv12277 : PrimeValue := ⟨12277, pr12277⟩
private theorem pr12281 : PrimeCertificate 12281 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv307]) (by decide +kernel)
def pv12281 : PrimeValue := ⟨12281, pr12281⟩
private theorem pr12289 : PrimeCertificate 12289 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3]) (by decide +kernel)
def pv12289 : PrimeValue := ⟨12289, pr12289⟩
private theorem pr12301 : PrimeCertificate 12301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv41]) (by decide +kernel)
def pv12301 : PrimeValue := ⟨12301, pr12301⟩
private theorem pr12323 : PrimeCertificate 12323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv101]) (by decide +kernel)
def pv12323 : PrimeValue := ⟨12323, pr12323⟩
private theorem pr12329 : PrimeCertificate 12329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv67]) (by decide +kernel)
def pv12329 : PrimeValue := ⟨12329, pr12329⟩
private theorem pr12343 : PrimeCertificate 12343 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv17]) (by decide +kernel)
def pv12343 : PrimeValue := ⟨12343, pr12343⟩
private theorem pr12347 : PrimeCertificate 12347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv6173]) (by decide +kernel)
def pv12347 : PrimeValue := ⟨12347, pr12347⟩
private theorem pr12373 : PrimeCertificate 12373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1031]) (by decide +kernel)
def pv12373 : PrimeValue := ⟨12373, pr12373⟩
private theorem pr12377 : PrimeCertificate 12377 :=
  certifyPrime (q := pv11) (ls := [pv2,pv7,pv13,pv17]) (by decide +kernel)
def pv12377 : PrimeValue := ⟨12377, pr12377⟩
private theorem pr12379 : PrimeCertificate 12379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv2063]) (by decide +kernel)
def pv12379 : PrimeValue := ⟨12379, pr12379⟩
private theorem pr12391 : PrimeCertificate 12391 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv7,pv59]) (by decide +kernel)
def pv12391 : PrimeValue := ⟨12391, pr12391⟩
private theorem pr12401 : PrimeCertificate 12401 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv31]) (by decide +kernel)
def pv12401 : PrimeValue := ⟨12401, pr12401⟩
private theorem pr12409 : PrimeCertificate 12409 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv47]) (by decide +kernel)
def pv12409 : PrimeValue := ⟨12409, pr12409⟩
private theorem pr12413 : PrimeCertificate 12413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv107]) (by decide +kernel)
def pv12413 : PrimeValue := ⟨12413, pr12413⟩
private theorem pr12421 : PrimeCertificate 12421 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv23]) (by decide +kernel)
def pv12421 : PrimeValue := ⟨12421, pr12421⟩
private theorem pr12433 : PrimeCertificate 12433 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv37]) (by decide +kernel)
def pv12433 : PrimeValue := ⟨12433, pr12433⟩
private theorem pr12437 : PrimeCertificate 12437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3109]) (by decide +kernel)
def pv12437 : PrimeValue := ⟨12437, pr12437⟩
private theorem pr12451 : PrimeCertificate 12451 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv83]) (by decide +kernel)
def pv12451 : PrimeValue := ⟨12451, pr12451⟩
private theorem pr12457 : PrimeCertificate 12457 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv173]) (by decide +kernel)
def pv12457 : PrimeValue := ⟨12457, pr12457⟩
private theorem pr12473 : PrimeCertificate 12473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1559]) (by decide +kernel)
def pv12473 : PrimeValue := ⟨12473, pr12473⟩
private theorem pr12479 : PrimeCertificate 12479 :=
  certifyPrime (q := pv23) (ls := [pv2,pv17,pv367]) (by decide +kernel)
def pv12479 : PrimeValue := ⟨12479, pr12479⟩
private theorem pr12487 : PrimeCertificate 12487 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv2081]) (by decide +kernel)
def pv12487 : PrimeValue := ⟨12487, pr12487⟩
private theorem pr12491 : PrimeCertificate 12491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1249]) (by decide +kernel)
def pv12491 : PrimeValue := ⟨12491, pr12491⟩
private theorem pr12497 : PrimeCertificate 12497 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv71]) (by decide +kernel)
def pv12497 : PrimeValue := ⟨12497, pr12497⟩
private theorem pr12503 : PrimeCertificate 12503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv19,pv47]) (by decide +kernel)
def pv12503 : PrimeValue := ⟨12503, pr12503⟩
private theorem pr12511 : PrimeCertificate 12511 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv139]) (by decide +kernel)
def pv12511 : PrimeValue := ⟨12511, pr12511⟩
private theorem pr12517 : PrimeCertificate 12517 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv149]) (by decide +kernel)
def pv12517 : PrimeValue := ⟨12517, pr12517⟩
private theorem pr12527 : PrimeCertificate 12527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv6263]) (by decide +kernel)
def pv12527 : PrimeValue := ⟨12527, pr12527⟩
private theorem pr12539 : PrimeCertificate 12539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv6269]) (by decide +kernel)
def pv12539 : PrimeValue := ⟨12539, pr12539⟩
private theorem pr12541 : PrimeCertificate 12541 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv5,pv11,pv19]) (by decide +kernel)
def pv12541 : PrimeValue := ⟨12541, pr12541⟩
private theorem pr12547 : PrimeCertificate 12547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv41]) (by decide +kernel)
def pv12547 : PrimeValue := ⟨12547, pr12547⟩
private theorem pr12553 : PrimeCertificate 12553 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv523]) (by decide +kernel)
def pv12553 : PrimeValue := ⟨12553, pr12553⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
