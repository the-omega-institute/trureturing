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

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr10181 : Nat.Prime 10181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv509]) (by decide +kernel)
def pv10181 : PrimeValue := ⟨10181, pr10181⟩
private theorem pr10193 : Nat.Prime 10193 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv13]) (by decide +kernel)
def pv10193 : PrimeValue := ⟨10193, pr10193⟩
private theorem pr10211 : Nat.Prime 10211 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv1021]) (by decide +kernel)
def pv10211 : PrimeValue := ⟨10211, pr10211⟩
private theorem pr10223 : Nat.Prime 10223 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv269]) (by decide +kernel)
def pv10223 : PrimeValue := ⟨10223, pr10223⟩
private theorem pr10243 : Nat.Prime 10243 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv569]) (by decide +kernel)
def pv10243 : PrimeValue := ⟨10243, pr10243⟩
private theorem pr10247 : Nat.Prime 10247 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv47,pv109]) (by decide +kernel)
def pv10247 : PrimeValue := ⟨10247, pr10247⟩
private theorem pr10253 : Nat.Prime 10253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv233]) (by decide +kernel)
def pv10253 : PrimeValue := ⟨10253, pr10253⟩
private theorem pr10259 : Nat.Prime 10259 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv223]) (by decide +kernel)
def pv10259 : PrimeValue := ⟨10259, pr10259⟩
private theorem pr10267 : Nat.Prime 10267 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv59]) (by decide +kernel)
def pv10267 : PrimeValue := ⟨10267, pr10267⟩
private theorem pr10271 : Nat.Prime 10271 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv79]) (by decide +kernel)
def pv10271 : PrimeValue := ⟨10271, pr10271⟩
private theorem pr10273 : Nat.Prime 10273 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv107]) (by decide +kernel)
def pv10273 : PrimeValue := ⟨10273, pr10273⟩
private theorem pr10289 : Nat.Prime 10289 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv643]) (by decide +kernel)
def pv10289 : PrimeValue := ⟨10289, pr10289⟩
private theorem pr10301 : Nat.Prime 10301 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv103]) (by decide +kernel)
def pv10301 : PrimeValue := ⟨10301, pr10301⟩
private theorem pr10303 : Nat.Prime 10303 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv101]) (by decide +kernel)
def pv10303 : PrimeValue := ⟨10303, pr10303⟩
private theorem pr10313 : Nat.Prime 10313 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1289]) (by decide +kernel)
def pv10313 : PrimeValue := ⟨10313, pr10313⟩
private theorem pr10321 : Nat.Prime 10321 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv43]) (by decide +kernel)
def pv10321 : PrimeValue := ⟨10321, pr10321⟩
private theorem pr10331 : Nat.Prime 10331 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1033]) (by decide +kernel)
def pv10331 : PrimeValue := ⟨10331, pr10331⟩
private theorem pr10333 : Nat.Prime 10333 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv41]) (by decide +kernel)
def pv10333 : PrimeValue := ⟨10333, pr10333⟩
private theorem pr10337 : Nat.Prime 10337 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv19]) (by decide +kernel)
def pv10337 : PrimeValue := ⟨10337, pr10337⟩
private theorem pr10343 : Nat.Prime 10343 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv5171]) (by decide +kernel)
def pv10343 : PrimeValue := ⟨10343, pr10343⟩
private theorem pr10357 : Nat.Prime 10357 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv863]) (by decide +kernel)
def pv10357 : PrimeValue := ⟨10357, pr10357⟩
private theorem pr10369 : Nat.Prime 10369 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3]) (by decide +kernel)
def pv10369 : PrimeValue := ⟨10369, pr10369⟩
private theorem pr10391 : Nat.Prime 10391 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv1039]) (by decide +kernel)
def pv10391 : PrimeValue := ⟨10391, pr10391⟩
private theorem pr10399 : Nat.Prime 10399 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv1733]) (by decide +kernel)
def pv10399 : PrimeValue := ⟨10399, pr10399⟩
private theorem pr10427 : Nat.Prime 10427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv401]) (by decide +kernel)
def pv10427 : PrimeValue := ⟨10427, pr10427⟩
private theorem pr10429 : Nat.Prime 10429 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv79]) (by decide +kernel)
def pv10429 : PrimeValue := ⟨10429, pr10429⟩
private theorem pr10433 : Nat.Prime 10433 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv163]) (by decide +kernel)
def pv10433 : PrimeValue := ⟨10433, pr10433⟩
private theorem pr10453 : Nat.Prime 10453 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv67]) (by decide +kernel)
def pv10453 : PrimeValue := ⟨10453, pr10453⟩
private theorem pr10457 : Nat.Prime 10457 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1307]) (by decide +kernel)
def pv10457 : PrimeValue := ⟨10457, pr10457⟩
private theorem pr10459 : Nat.Prime 10459 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv83]) (by decide +kernel)
def pv10459 : PrimeValue := ⟨10459, pr10459⟩
private theorem pr10463 : Nat.Prime 10463 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv5231]) (by decide +kernel)
def pv10463 : PrimeValue := ⟨10463, pr10463⟩
private theorem pr10477 : Nat.Prime 10477 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv97]) (by decide +kernel)
def pv10477 : PrimeValue := ⟨10477, pr10477⟩
private theorem pr10487 : Nat.Prime 10487 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv107]) (by decide +kernel)
def pv10487 : PrimeValue := ⟨10487, pr10487⟩
private theorem pr10499 : Nat.Prime 10499 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv181]) (by decide +kernel)
def pv10499 : PrimeValue := ⟨10499, pr10499⟩
private theorem pr10501 : Nat.Prime 10501 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv10501 : PrimeValue := ⟨10501, pr10501⟩
private theorem pr10513 : Nat.Prime 10513 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv73]) (by decide +kernel)
def pv10513 : PrimeValue := ⟨10513, pr10513⟩
private theorem pr10529 : Nat.Prime 10529 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv47]) (by decide +kernel)
def pv10529 : PrimeValue := ⟨10529, pr10529⟩
private theorem pr10531 : Nat.Prime 10531 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv10531 : PrimeValue := ⟨10531, pr10531⟩
private theorem pr10559 : Nat.Prime 10559 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv5279]) (by decide +kernel)
def pv10559 : PrimeValue := ⟨10559, pr10559⟩
private theorem pr10567 : Nat.Prime 10567 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv587]) (by decide +kernel)
def pv10567 : PrimeValue := ⟨10567, pr10567⟩
private theorem pr10589 : Nat.Prime 10589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv2647]) (by decide +kernel)
def pv10589 : PrimeValue := ⟨10589, pr10589⟩
private theorem pr10597 : Nat.Prime 10597 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv883]) (by decide +kernel)
def pv10597 : PrimeValue := ⟨10597, pr10597⟩
private theorem pr10601 : Nat.Prime 10601 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv53]) (by decide +kernel)
def pv10601 : PrimeValue := ⟨10601, pr10601⟩
private theorem pr10607 : Nat.Prime 10607 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv5303]) (by decide +kernel)
def pv10607 : PrimeValue := ⟨10607, pr10607⟩
private theorem pr10613 : Nat.Prime 10613 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv379]) (by decide +kernel)
def pv10613 : PrimeValue := ⟨10613, pr10613⟩
private theorem pr10627 : Nat.Prime 10627 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv23]) (by decide +kernel)
def pv10627 : PrimeValue := ⟨10627, pr10627⟩
private theorem pr10631 : Nat.Prime 10631 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv1063]) (by decide +kernel)
def pv10631 : PrimeValue := ⟨10631, pr10631⟩
private theorem pr10639 : Nat.Prime 10639 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv197]) (by decide +kernel)
def pv10639 : PrimeValue := ⟨10639, pr10639⟩
private theorem pr10651 : Nat.Prime 10651 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv71]) (by decide +kernel)
def pv10651 : PrimeValue := ⟨10651, pr10651⟩
private theorem pr10657 : Nat.Prime 10657 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv37]) (by decide +kernel)
def pv10657 : PrimeValue := ⟨10657, pr10657⟩
private theorem pr10663 : Nat.Prime 10663 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv1777]) (by decide +kernel)
def pv10663 : PrimeValue := ⟨10663, pr10663⟩
private theorem pr10667 : Nat.Prime 10667 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5333]) (by decide +kernel)
def pv10667 : PrimeValue := ⟨10667, pr10667⟩
private theorem pr10687 : Nat.Prime 10687 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv137]) (by decide +kernel)
def pv10687 : PrimeValue := ⟨10687, pr10687⟩
private theorem pr10691 : Nat.Prime 10691 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1069]) (by decide +kernel)
def pv10691 : PrimeValue := ⟨10691, pr10691⟩
private theorem pr10709 : Nat.Prime 10709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv2677]) (by decide +kernel)
def pv10709 : PrimeValue := ⟨10709, pr10709⟩
private theorem pr10711 : Nat.Prime 10711 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv17]) (by decide +kernel)
def pv10711 : PrimeValue := ⟨10711, pr10711⟩
private theorem pr10723 : Nat.Prime 10723 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1787]) (by decide +kernel)
def pv10723 : PrimeValue := ⟨10723, pr10723⟩
private theorem pr10729 : Nat.Prime 10729 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv149]) (by decide +kernel)
def pv10729 : PrimeValue := ⟨10729, pr10729⟩
private theorem pr10733 : Nat.Prime 10733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv2683]) (by decide +kernel)
def pv10733 : PrimeValue := ⟨10733, pr10733⟩
private theorem pr10739 : Nat.Prime 10739 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv13,pv59]) (by decide +kernel)
def pv10739 : PrimeValue := ⟨10739, pr10739⟩
private theorem pr10753 : Nat.Prime 10753 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv10753 : PrimeValue := ⟨10753, pr10753⟩
private theorem pr10771 : Nat.Prime 10771 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv359]) (by decide +kernel)
def pv10771 : PrimeValue := ⟨10771, pr10771⟩
private theorem pr10781 : Nat.Prime 10781 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv7,pv11]) (by decide +kernel)
def pv10781 : PrimeValue := ⟨10781, pr10781⟩
private theorem pr10789 : Nat.Prime 10789 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv29,pv31]) (by decide +kernel)
def pv10789 : PrimeValue := ⟨10789, pr10789⟩
private theorem pr10799 : Nat.Prime 10799 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5399]) (by decide +kernel)
def pv10799 : PrimeValue := ⟨10799, pr10799⟩
private theorem pr10831 : Nat.Prime 10831 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv10831 : PrimeValue := ⟨10831, pr10831⟩
private theorem pr10837 : Nat.Prime 10837 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv43]) (by decide +kernel)
def pv10837 : PrimeValue := ⟨10837, pr10837⟩
private theorem pr10847 : Nat.Prime 10847 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv17,pv29]) (by decide +kernel)
def pv10847 : PrimeValue := ⟨10847, pr10847⟩
private theorem pr10853 : Nat.Prime 10853 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv2713]) (by decide +kernel)
def pv10853 : PrimeValue := ⟨10853, pr10853⟩
private theorem pr10859 : Nat.Prime 10859 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv89]) (by decide +kernel)
def pv10859 : PrimeValue := ⟨10859, pr10859⟩
private theorem pr10861 : Nat.Prime 10861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv181]) (by decide +kernel)
def pv10861 : PrimeValue := ⟨10861, pr10861⟩
private theorem pr10867 : Nat.Prime 10867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1811]) (by decide +kernel)
def pv10867 : PrimeValue := ⟨10867, pr10867⟩
private theorem pr10883 : Nat.Prime 10883 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5441]) (by decide +kernel)
def pv10883 : PrimeValue := ⟨10883, pr10883⟩
private theorem pr10889 : Nat.Prime 10889 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1361]) (by decide +kernel)
def pv10889 : PrimeValue := ⟨10889, pr10889⟩
private theorem pr10891 : Nat.Prime 10891 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv10891 : PrimeValue := ⟨10891, pr10891⟩
private theorem pr10903 : Nat.Prime 10903 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv79]) (by decide +kernel)
def pv10903 : PrimeValue := ⟨10903, pr10903⟩
private theorem pr10909 : Nat.Prime 10909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv101]) (by decide +kernel)
def pv10909 : PrimeValue := ⟨10909, pr10909⟩
private theorem pr10937 : Nat.Prime 10937 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1367]) (by decide +kernel)
def pv10937 : PrimeValue := ⟨10937, pr10937⟩
private theorem pr10939 : Nat.Prime 10939 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv1823]) (by decide +kernel)
def pv10939 : PrimeValue := ⟨10939, pr10939⟩
private theorem pr10949 : Nat.Prime 10949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv17,pv23]) (by decide +kernel)
def pv10949 : PrimeValue := ⟨10949, pr10949⟩
private theorem pr10957 : Nat.Prime 10957 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv83]) (by decide +kernel)
def pv10957 : PrimeValue := ⟨10957, pr10957⟩
private theorem pr10973 : Nat.Prime 10973 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv211]) (by decide +kernel)
def pv10973 : PrimeValue := ⟨10973, pr10973⟩
private theorem pr10979 : Nat.Prime 10979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv499]) (by decide +kernel)
def pv10979 : PrimeValue := ⟨10979, pr10979⟩
private theorem pr10987 : Nat.Prime 10987 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1831]) (by decide +kernel)
def pv10987 : PrimeValue := ⟨10987, pr10987⟩
private theorem pr10993 : Nat.Prime 10993 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv229]) (by decide +kernel)
def pv10993 : PrimeValue := ⟨10993, pr10993⟩
private theorem pr11003 : Nat.Prime 11003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5501]) (by decide +kernel)
def pv11003 : PrimeValue := ⟨11003, pr11003⟩
private theorem pr11027 : Nat.Prime 11027 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv149]) (by decide +kernel)
def pv11027 : PrimeValue := ⟨11027, pr11027⟩
private theorem pr11047 : Nat.Prime 11047 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv263]) (by decide +kernel)
def pv11047 : PrimeValue := ⟨11047, pr11047⟩
private theorem pr11057 : Nat.Prime 11057 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv691]) (by decide +kernel)
def pv11057 : PrimeValue := ⟨11057, pr11057⟩
private theorem pr11059 : Nat.Prime 11059 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv19,pv97]) (by decide +kernel)
def pv11059 : PrimeValue := ⟨11059, pr11059⟩
private theorem pr11069 : Nat.Prime 11069 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv2767]) (by decide +kernel)
def pv11069 : PrimeValue := ⟨11069, pr11069⟩
private theorem pr11071 : Nat.Prime 11071 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv41]) (by decide +kernel)
def pv11071 : PrimeValue := ⟨11071, pr11071⟩
private theorem pr11083 : Nat.Prime 11083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1847]) (by decide +kernel)
def pv11083 : PrimeValue := ⟨11083, pr11083⟩
private theorem pr11087 : Nat.Prime 11087 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv23,pv241]) (by decide +kernel)
def pv11087 : PrimeValue := ⟨11087, pr11087⟩
private theorem pr11093 : Nat.Prime 11093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv59]) (by decide +kernel)
def pv11093 : PrimeValue := ⟨11093, pr11093⟩
private theorem pr11113 : Nat.Prime 11113 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv463]) (by decide +kernel)
def pv11113 : PrimeValue := ⟨11113, pr11113⟩
private theorem pr11117 : Nat.Prime 11117 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv397]) (by decide +kernel)
def pv11117 : PrimeValue := ⟨11117, pr11117⟩
private theorem pr11119 : Nat.Prime 11119 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv109]) (by decide +kernel)
def pv11119 : PrimeValue := ⟨11119, pr11119⟩
private theorem pr11131 : Nat.Prime 11131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv53]) (by decide +kernel)
def pv11131 : PrimeValue := ⟨11131, pr11131⟩
private theorem pr11149 : Nat.Prime 11149 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv929]) (by decide +kernel)
def pv11149 : PrimeValue := ⟨11149, pr11149⟩
private theorem pr11159 : Nat.Prime 11159 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv797]) (by decide +kernel)
def pv11159 : PrimeValue := ⟨11159, pr11159⟩
private theorem pr11161 : Nat.Prime 11161 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv31]) (by decide +kernel)
def pv11161 : PrimeValue := ⟨11161, pr11161⟩
private theorem pr11171 : Nat.Prime 11171 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1117]) (by decide +kernel)
def pv11171 : PrimeValue := ⟨11171, pr11171⟩
private theorem pr11173 : Nat.Prime 11173 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv19]) (by decide +kernel)
def pv11173 : PrimeValue := ⟨11173, pr11173⟩
private theorem pr11177 : Nat.Prime 11177 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv127]) (by decide +kernel)
def pv11177 : PrimeValue := ⟨11177, pr11177⟩
private theorem pr11197 : Nat.Prime 11197 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv311]) (by decide +kernel)
def pv11197 : PrimeValue := ⟨11197, pr11197⟩
private theorem pr11213 : Nat.Prime 11213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv2803]) (by decide +kernel)
def pv11213 : PrimeValue := ⟨11213, pr11213⟩
private theorem pr11239 : Nat.Prime 11239 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv1873]) (by decide +kernel)
def pv11239 : PrimeValue := ⟨11239, pr11239⟩
private theorem pr11243 : Nat.Prime 11243 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv11,pv73]) (by decide +kernel)
def pv11243 : PrimeValue := ⟨11243, pr11243⟩
private theorem pr11251 : Nat.Prime 11251 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv11251 : PrimeValue := ⟨11251, pr11251⟩
private theorem pr11257 : Nat.Prime 11257 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv67]) (by decide +kernel)
def pv11257 : PrimeValue := ⟨11257, pr11257⟩
private theorem pr11261 : Nat.Prime 11261 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv563]) (by decide +kernel)
def pv11261 : PrimeValue := ⟨11261, pr11261⟩
private theorem pr11273 : Nat.Prime 11273 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1409]) (by decide +kernel)
def pv11273 : PrimeValue := ⟨11273, pr11273⟩
private theorem pr11279 : Nat.Prime 11279 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5639]) (by decide +kernel)
def pv11279 : PrimeValue := ⟨11279, pr11279⟩
private theorem pr11287 : Nat.Prime 11287 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv19]) (by decide +kernel)
def pv11287 : PrimeValue := ⟨11287, pr11287⟩
private theorem pr11299 : Nat.Prime 11299 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv269]) (by decide +kernel)
def pv11299 : PrimeValue := ⟨11299, pr11299⟩
private theorem pr11311 : Nat.Prime 11311 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv13,pv29]) (by decide +kernel)
def pv11311 : PrimeValue := ⟨11311, pr11311⟩
private theorem pr11317 : Nat.Prime 11317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv41]) (by decide +kernel)
def pv11317 : PrimeValue := ⟨11317, pr11317⟩
private theorem pr11321 : Nat.Prime 11321 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv283]) (by decide +kernel)
def pv11321 : PrimeValue := ⟨11321, pr11321⟩
private theorem pr11329 : Nat.Prime 11329 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv59]) (by decide +kernel)
def pv11329 : PrimeValue := ⟨11329, pr11329⟩
private theorem pr11351 : Nat.Prime 11351 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv227]) (by decide +kernel)
def pv11351 : PrimeValue := ⟨11351, pr11351⟩
private theorem pr11353 : Nat.Prime 11353 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv43]) (by decide +kernel)
def pv11353 : PrimeValue := ⟨11353, pr11353⟩
private theorem pr11369 : Nat.Prime 11369 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv29]) (by decide +kernel)
def pv11369 : PrimeValue := ⟨11369, pr11369⟩
private theorem pr11383 : Nat.Prime 11383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv271]) (by decide +kernel)
def pv11383 : PrimeValue := ⟨11383, pr11383⟩
private theorem pr11393 : Nat.Prime 11393 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv89]) (by decide +kernel)
def pv11393 : PrimeValue := ⟨11393, pr11393⟩
private theorem pr11399 : Nat.Prime 11399 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv41,pv139]) (by decide +kernel)
def pv11399 : PrimeValue := ⟨11399, pr11399⟩
private theorem pr11411 : Nat.Prime 11411 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv163]) (by decide +kernel)
def pv11411 : PrimeValue := ⟨11411, pr11411⟩
private theorem pr11423 : Nat.Prime 11423 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv5711]) (by decide +kernel)
def pv11423 : PrimeValue := ⟨11423, pr11423⟩
private theorem pr11437 : Nat.Prime 11437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv953]) (by decide +kernel)
def pv11437 : PrimeValue := ⟨11437, pr11437⟩
private theorem pr11443 : Nat.Prime 11443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1907]) (by decide +kernel)
def pv11443 : PrimeValue := ⟨11443, pr11443⟩
private theorem pr11447 : Nat.Prime 11447 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv59,pv97]) (by decide +kernel)
def pv11447 : PrimeValue := ⟨11447, pr11447⟩
private theorem pr11467 : Nat.Prime 11467 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv13]) (by decide +kernel)
def pv11467 : PrimeValue := ⟨11467, pr11467⟩
private theorem pr11471 : Nat.Prime 11471 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv31,pv37]) (by decide +kernel)
def pv11471 : PrimeValue := ⟨11471, pr11471⟩
private theorem pr11483 : Nat.Prime 11483 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5741]) (by decide +kernel)
def pv11483 : PrimeValue := ⟨11483, pr11483⟩
private theorem pr11489 : Nat.Prime 11489 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv359]) (by decide +kernel)
def pv11489 : PrimeValue := ⟨11489, pr11489⟩
private theorem pr11491 : Nat.Prime 11491 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv383]) (by decide +kernel)
def pv11491 : PrimeValue := ⟨11491, pr11491⟩
private theorem pr11497 : Nat.Prime 11497 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv479]) (by decide +kernel)
def pv11497 : PrimeValue := ⟨11497, pr11497⟩
private theorem pr11503 : Nat.Prime 11503 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv71]) (by decide +kernel)
def pv11503 : PrimeValue := ⟨11503, pr11503⟩
private theorem pr11519 : Nat.Prime 11519 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv13,pv443]) (by decide +kernel)
def pv11519 : PrimeValue := ⟨11519, pr11519⟩
private theorem pr11527 : Nat.Prime 11527 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv113]) (by decide +kernel)
def pv11527 : PrimeValue := ⟨11527, pr11527⟩
private theorem pr11549 : Nat.Prime 11549 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv2887]) (by decide +kernel)
def pv11549 : PrimeValue := ⟨11549, pr11549⟩
private theorem pr11551 : Nat.Prime 11551 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv11]) (by decide +kernel)
def pv11551 : PrimeValue := ⟨11551, pr11551⟩
private theorem pr11579 : Nat.Prime 11579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv827]) (by decide +kernel)
def pv11579 : PrimeValue := ⟨11579, pr11579⟩
private theorem pr11587 : Nat.Prime 11587 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1931]) (by decide +kernel)
def pv11587 : PrimeValue := ⟨11587, pr11587⟩
private theorem pr11593 : Nat.Prime 11593 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv23]) (by decide +kernel)
def pv11593 : PrimeValue := ⟨11593, pr11593⟩
private theorem pr11597 : Nat.Prime 11597 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv223]) (by decide +kernel)
def pv11597 : PrimeValue := ⟨11597, pr11597⟩
private theorem pr11617 : Nat.Prime 11617 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv11617 : PrimeValue := ⟨11617, pr11617⟩
private theorem pr11621 : Nat.Prime 11621 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv83]) (by decide +kernel)
def pv11621 : PrimeValue := ⟨11621, pr11621⟩
private theorem pr11633 : Nat.Prime 11633 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv727]) (by decide +kernel)
def pv11633 : PrimeValue := ⟨11633, pr11633⟩
private theorem pr11657 : Nat.Prime 11657 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv47]) (by decide +kernel)
def pv11657 : PrimeValue := ⟨11657, pr11657⟩
private theorem pr11677 : Nat.Prime 11677 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv139]) (by decide +kernel)
def pv11677 : PrimeValue := ⟨11677, pr11677⟩
private theorem pr11681 : Nat.Prime 11681 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv73]) (by decide +kernel)
def pv11681 : PrimeValue := ⟨11681, pr11681⟩
private theorem pr11689 : Nat.Prime 11689 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv487]) (by decide +kernel)
def pv11689 : PrimeValue := ⟨11689, pr11689⟩
private theorem pr11699 : Nat.Prime 11699 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5849]) (by decide +kernel)
def pv11699 : PrimeValue := ⟨11699, pr11699⟩
private theorem pr11701 : Nat.Prime 11701 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv11701 : PrimeValue := ⟨11701, pr11701⟩
private theorem pr11717 : Nat.Prime 11717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv101]) (by decide +kernel)
def pv11717 : PrimeValue := ⟨11717, pr11717⟩
private theorem pr11719 : Nat.Prime 11719 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv7,pv31]) (by decide +kernel)
def pv11719 : PrimeValue := ⟨11719, pr11719⟩
private theorem pr11731 : Nat.Prime 11731 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv17,pv23]) (by decide +kernel)
def pv11731 : PrimeValue := ⟨11731, pr11731⟩
private theorem pr11743 : Nat.Prime 11743 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv19,pv103]) (by decide +kernel)
def pv11743 : PrimeValue := ⟨11743, pr11743⟩
private theorem pr11777 : Nat.Prime 11777 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23]) (by decide +kernel)
def pv11777 : PrimeValue := ⟨11777, pr11777⟩
private theorem pr11779 : Nat.Prime 11779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv151]) (by decide +kernel)
def pv11779 : PrimeValue := ⟨11779, pr11779⟩
private theorem pr11783 : Nat.Prime 11783 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv43,pv137]) (by decide +kernel)
def pv11783 : PrimeValue := ⟨11783, pr11783⟩
private theorem pr11789 : Nat.Prime 11789 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv421]) (by decide +kernel)
def pv11789 : PrimeValue := ⟨11789, pr11789⟩
private theorem pr11801 : Nat.Prime 11801 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv59]) (by decide +kernel)
def pv11801 : PrimeValue := ⟨11801, pr11801⟩
private theorem pr11807 : Nat.Prime 11807 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv5903]) (by decide +kernel)
def pv11807 : PrimeValue := ⟨11807, pr11807⟩
private theorem pr11813 : Nat.Prime 11813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv2953]) (by decide +kernel)
def pv11813 : PrimeValue := ⟨11813, pr11813⟩
private theorem pr11821 : Nat.Prime 11821 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv197]) (by decide +kernel)
def pv11821 : PrimeValue := ⟨11821, pr11821⟩
private theorem pr11827 : Nat.Prime 11827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv73]) (by decide +kernel)
def pv11827 : PrimeValue := ⟨11827, pr11827⟩
private theorem pr11831 : Nat.Prime 11831 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv13]) (by decide +kernel)
def pv11831 : PrimeValue := ⟨11831, pr11831⟩
private theorem pr11833 : Nat.Prime 11833 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv29]) (by decide +kernel)
def pv11833 : PrimeValue := ⟨11833, pr11833⟩
private theorem pr11839 : Nat.Prime 11839 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv1973]) (by decide +kernel)
def pv11839 : PrimeValue := ⟨11839, pr11839⟩
private theorem pr11863 : Nat.Prime 11863 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv659]) (by decide +kernel)
def pv11863 : PrimeValue := ⟨11863, pr11863⟩
private theorem pr11867 : Nat.Prime 11867 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv349]) (by decide +kernel)
def pv11867 : PrimeValue := ⟨11867, pr11867⟩
private theorem pr11887 : Nat.Prime 11887 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv283]) (by decide +kernel)
def pv11887 : PrimeValue := ⟨11887, pr11887⟩
private theorem pr11897 : Nat.Prime 11897 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1487]) (by decide +kernel)
def pv11897 : PrimeValue := ⟨11897, pr11897⟩
private theorem pr11903 : Nat.Prime 11903 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv541]) (by decide +kernel)
def pv11903 : PrimeValue := ⟨11903, pr11903⟩
private theorem pr11909 : Nat.Prime 11909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv229]) (by decide +kernel)
def pv11909 : PrimeValue := ⟨11909, pr11909⟩
private theorem pr11923 : Nat.Prime 11923 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1987]) (by decide +kernel)
def pv11923 : PrimeValue := ⟨11923, pr11923⟩
private theorem pr11927 : Nat.Prime 11927 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv67,pv89]) (by decide +kernel)
def pv11927 : PrimeValue := ⟨11927, pr11927⟩
private theorem pr11933 : Nat.Prime 11933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv157]) (by decide +kernel)
def pv11933 : PrimeValue := ⟨11933, pr11933⟩
private theorem pr11939 : Nat.Prime 11939 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv127]) (by decide +kernel)
def pv11939 : PrimeValue := ⟨11939, pr11939⟩
private theorem pr11941 : Nat.Prime 11941 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv199]) (by decide +kernel)
def pv11941 : PrimeValue := ⟨11941, pr11941⟩
private theorem pr11953 : Nat.Prime 11953 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv83]) (by decide +kernel)
def pv11953 : PrimeValue := ⟨11953, pr11953⟩
private theorem pr11959 : Nat.Prime 11959 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv1993]) (by decide +kernel)
def pv11959 : PrimeValue := ⟨11959, pr11959⟩
private theorem pr11969 : Nat.Prime 11969 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv17]) (by decide +kernel)
def pv11969 : PrimeValue := ⟨11969, pr11969⟩
private theorem pr11971 : Nat.Prime 11971 :=
  checkPrime_prime (q := pv79) (ls := [pv2,pv3,pv5,pv7,pv19]) (by decide +kernel)
def pv11971 : PrimeValue := ⟨11971, pr11971⟩
private theorem pr11981 : Nat.Prime 11981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv599]) (by decide +kernel)
def pv11981 : PrimeValue := ⟨11981, pr11981⟩
private theorem pr11987 : Nat.Prime 11987 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv461]) (by decide +kernel)
def pv11987 : PrimeValue := ⟨11987, pr11987⟩
private theorem pr12007 : Nat.Prime 12007 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv23,pv29]) (by decide +kernel)
def pv12007 : PrimeValue := ⟨12007, pr12007⟩
private theorem pr12011 : Nat.Prime 12011 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1201]) (by decide +kernel)
def pv12011 : PrimeValue := ⟨12011, pr12011⟩
private theorem pr12037 : Nat.Prime 12037 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv59]) (by decide +kernel)
def pv12037 : PrimeValue := ⟨12037, pr12037⟩
private theorem pr12041 : Nat.Prime 12041 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv43]) (by decide +kernel)
def pv12041 : PrimeValue := ⟨12041, pr12041⟩
private theorem pr12043 : Nat.Prime 12043 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv223]) (by decide +kernel)
def pv12043 : PrimeValue := ⟨12043, pr12043⟩
private theorem pr12049 : Nat.Prime 12049 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv251]) (by decide +kernel)
def pv12049 : PrimeValue := ⟨12049, pr12049⟩
private theorem pr12071 : Nat.Prime 12071 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv17,pv71]) (by decide +kernel)
def pv12071 : PrimeValue := ⟨12071, pr12071⟩
private theorem pr12073 : Nat.Prime 12073 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv503]) (by decide +kernel)
def pv12073 : PrimeValue := ⟨12073, pr12073⟩
private theorem pr12097 : Nat.Prime 12097 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv12097 : PrimeValue := ⟨12097, pr12097⟩
private theorem pr12101 : Nat.Prime 12101 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11]) (by decide +kernel)
def pv12101 : PrimeValue := ⟨12101, pr12101⟩
private theorem pr12107 : Nat.Prime 12107 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv6053]) (by decide +kernel)
def pv12107 : PrimeValue := ⟨12107, pr12107⟩
private theorem pr12109 : Nat.Prime 12109 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv1009]) (by decide +kernel)
def pv12109 : PrimeValue := ⟨12109, pr12109⟩
private theorem pr12113 : Nat.Prime 12113 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv757]) (by decide +kernel)
def pv12113 : PrimeValue := ⟨12113, pr12113⟩
private theorem pr12119 : Nat.Prime 12119 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv73,pv83]) (by decide +kernel)
def pv12119 : PrimeValue := ⟨12119, pr12119⟩
private theorem pr12143 : Nat.Prime 12143 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv13,pv467]) (by decide +kernel)
def pv12143 : PrimeValue := ⟨12143, pr12143⟩
private theorem pr12149 : Nat.Prime 12149 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3037]) (by decide +kernel)
def pv12149 : PrimeValue := ⟨12149, pr12149⟩
private theorem pr12157 : Nat.Prime 12157 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1013]) (by decide +kernel)
def pv12157 : PrimeValue := ⟨12157, pr12157⟩
private theorem pr12161 : Nat.Prime 12161 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv19]) (by decide +kernel)
def pv12161 : PrimeValue := ⟨12161, pr12161⟩
private theorem pr12163 : Nat.Prime 12163 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2027]) (by decide +kernel)
def pv12163 : PrimeValue := ⟨12163, pr12163⟩
private theorem pr12197 : Nat.Prime 12197 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3049]) (by decide +kernel)
def pv12197 : PrimeValue := ⟨12197, pr12197⟩
private theorem pr12203 : Nat.Prime 12203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv6101]) (by decide +kernel)
def pv12203 : PrimeValue := ⟨12203, pr12203⟩
private theorem pr12211 : Nat.Prime 12211 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv37]) (by decide +kernel)
def pv12211 : PrimeValue := ⟨12211, pr12211⟩
private theorem pr12227 : Nat.Prime 12227 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv6113]) (by decide +kernel)
def pv12227 : PrimeValue := ⟨12227, pr12227⟩
private theorem pr12239 : Nat.Prime 12239 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv29,pv211]) (by decide +kernel)
def pv12239 : PrimeValue := ⟨12239, pr12239⟩
private theorem pr12241 : Nat.Prime 12241 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv12241 : PrimeValue := ⟨12241, pr12241⟩
private theorem pr12251 : Nat.Prime 12251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7]) (by decide +kernel)
def pv12251 : PrimeValue := ⟨12251, pr12251⟩
private theorem pr12253 : Nat.Prime 12253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1021]) (by decide +kernel)
def pv12253 : PrimeValue := ⟨12253, pr12253⟩
private theorem pr12263 : Nat.Prime 12263 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv6131]) (by decide +kernel)
def pv12263 : PrimeValue := ⟨12263, pr12263⟩
private theorem pr12269 : Nat.Prime 12269 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3067]) (by decide +kernel)
def pv12269 : PrimeValue := ⟨12269, pr12269⟩
private theorem pr12277 : Nat.Prime 12277 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv31]) (by decide +kernel)
def pv12277 : PrimeValue := ⟨12277, pr12277⟩
private theorem pr12281 : Nat.Prime 12281 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv307]) (by decide +kernel)
def pv12281 : PrimeValue := ⟨12281, pr12281⟩
private theorem pr12289 : Nat.Prime 12289 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3]) (by decide +kernel)
def pv12289 : PrimeValue := ⟨12289, pr12289⟩
private theorem pr12301 : Nat.Prime 12301 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv41]) (by decide +kernel)
def pv12301 : PrimeValue := ⟨12301, pr12301⟩
private theorem pr12323 : Nat.Prime 12323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv101]) (by decide +kernel)
def pv12323 : PrimeValue := ⟨12323, pr12323⟩
private theorem pr12329 : Nat.Prime 12329 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv67]) (by decide +kernel)
def pv12329 : PrimeValue := ⟨12329, pr12329⟩
private theorem pr12343 : Nat.Prime 12343 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv17]) (by decide +kernel)
def pv12343 : PrimeValue := ⟨12343, pr12343⟩
private theorem pr12347 : Nat.Prime 12347 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv6173]) (by decide +kernel)
def pv12347 : PrimeValue := ⟨12347, pr12347⟩
private theorem pr12373 : Nat.Prime 12373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1031]) (by decide +kernel)
def pv12373 : PrimeValue := ⟨12373, pr12373⟩
private theorem pr12377 : Nat.Prime 12377 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv7,pv13,pv17]) (by decide +kernel)
def pv12377 : PrimeValue := ⟨12377, pr12377⟩
private theorem pr12379 : Nat.Prime 12379 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2063]) (by decide +kernel)
def pv12379 : PrimeValue := ⟨12379, pr12379⟩
private theorem pr12391 : Nat.Prime 12391 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv7,pv59]) (by decide +kernel)
def pv12391 : PrimeValue := ⟨12391, pr12391⟩
private theorem pr12401 : Nat.Prime 12401 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv31]) (by decide +kernel)
def pv12401 : PrimeValue := ⟨12401, pr12401⟩
private theorem pr12409 : Nat.Prime 12409 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv11,pv47]) (by decide +kernel)
def pv12409 : PrimeValue := ⟨12409, pr12409⟩
private theorem pr12413 : Nat.Prime 12413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv107]) (by decide +kernel)
def pv12413 : PrimeValue := ⟨12413, pr12413⟩
private theorem pr12421 : Nat.Prime 12421 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv23]) (by decide +kernel)
def pv12421 : PrimeValue := ⟨12421, pr12421⟩
private theorem pr12433 : Nat.Prime 12433 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv37]) (by decide +kernel)
def pv12433 : PrimeValue := ⟨12433, pr12433⟩
private theorem pr12437 : Nat.Prime 12437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3109]) (by decide +kernel)
def pv12437 : PrimeValue := ⟨12437, pr12437⟩
private theorem pr12451 : Nat.Prime 12451 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv83]) (by decide +kernel)
def pv12451 : PrimeValue := ⟨12451, pr12451⟩
private theorem pr12457 : Nat.Prime 12457 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv173]) (by decide +kernel)
def pv12457 : PrimeValue := ⟨12457, pr12457⟩
private theorem pr12473 : Nat.Prime 12473 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1559]) (by decide +kernel)
def pv12473 : PrimeValue := ⟨12473, pr12473⟩
private theorem pr12479 : Nat.Prime 12479 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv17,pv367]) (by decide +kernel)
def pv12479 : PrimeValue := ⟨12479, pr12479⟩
private theorem pr12487 : Nat.Prime 12487 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv2081]) (by decide +kernel)
def pv12487 : PrimeValue := ⟨12487, pr12487⟩
private theorem pr12491 : Nat.Prime 12491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1249]) (by decide +kernel)
def pv12491 : PrimeValue := ⟨12491, pr12491⟩
private theorem pr12497 : Nat.Prime 12497 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv71]) (by decide +kernel)
def pv12497 : PrimeValue := ⟨12497, pr12497⟩
private theorem pr12503 : Nat.Prime 12503 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv19,pv47]) (by decide +kernel)
def pv12503 : PrimeValue := ⟨12503, pr12503⟩
private theorem pr12511 : Nat.Prime 12511 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv139]) (by decide +kernel)
def pv12511 : PrimeValue := ⟨12511, pr12511⟩
private theorem pr12517 : Nat.Prime 12517 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv149]) (by decide +kernel)
def pv12517 : PrimeValue := ⟨12517, pr12517⟩
private theorem pr12527 : Nat.Prime 12527 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv6263]) (by decide +kernel)
def pv12527 : PrimeValue := ⟨12527, pr12527⟩
private theorem pr12539 : Nat.Prime 12539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv6269]) (by decide +kernel)
def pv12539 : PrimeValue := ⟨12539, pr12539⟩
private theorem pr12541 : Nat.Prime 12541 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv5,pv11,pv19]) (by decide +kernel)
def pv12541 : PrimeValue := ⟨12541, pr12541⟩
private theorem pr12547 : Nat.Prime 12547 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv41]) (by decide +kernel)
def pv12547 : PrimeValue := ⟨12547, pr12547⟩
private theorem pr12553 : Nat.Prime 12553 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv523]) (by decide +kernel)
def pv12553 : PrimeValue := ⟨12553, pr12553⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
