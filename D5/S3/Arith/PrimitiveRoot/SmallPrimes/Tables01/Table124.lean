/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table124
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table124.pv679837
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table016
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table020
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table027
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table042
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table043
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table091
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table092

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr679837 : PrimeCertificate 679837 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv181,pv313]) (by decide +kernel)
def pv679837 : PrimeValue := ⟨679837, pr679837⟩
private theorem pr679859 : PrimeCertificate 679859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv17891]) (by decide +kernel)
def pv679859 : PrimeValue := ⟨679859, pr679859⟩
private theorem pr679879 : PrimeCertificate 679879 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv107,pv353]) (by decide +kernel)
def pv679879 : PrimeValue := ⟨679879, pr679879⟩
private theorem pr679909 : PrimeCertificate 679909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv56659]) (by decide +kernel)
def pv679909 : PrimeValue := ⟨679909, pr679909⟩
private theorem pr680129 : PrimeCertificate 680129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv10627]) (by decide +kernel)
def pv680129 : PrimeValue := ⟨680129, pr680129⟩
private theorem pr680159 : PrimeCertificate 680159 :=
  certifyPrime (q := pv7) (ls := [pv2,pv340079]) (by decide +kernel)
def pv680159 : PrimeValue := ⟨680159, pr680159⟩
private theorem pr680263 : PrimeCertificate 680263 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv937]) (by decide +kernel)
def pv680263 : PrimeValue := ⟨680263, pr680263⟩
private theorem pr680299 : PrimeCertificate 680299 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv113383]) (by decide +kernel)
def pv680299 : PrimeValue := ⟨680299, pr680299⟩
private theorem pr680353 : PrimeCertificate 680353 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv373]) (by decide +kernel)
def pv680353 : PrimeValue := ⟨680353, pr680353⟩
private theorem pr680443 : PrimeCertificate 680443 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv17,pv953]) (by decide +kernel)
def pv680443 : PrimeValue := ⟨680443, pr680443⟩
private theorem pr680681 : PrimeCertificate 680681 :=
  certifyPrime (q := pv43) (ls := [pv2,pv5,pv7,pv11,pv13,pv17]) (by decide +kernel)
def pv680681 : PrimeValue := ⟨680681, pr680681⟩
private theorem pr680767 : PrimeCertificate 680767 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv83,pv1367]) (by decide +kernel)
def pv680767 : PrimeValue := ⟨680767, pr680767⟩
private theorem pr680929 : PrimeCertificate 680929 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv41,pv173]) (by decide +kernel)
def pv680929 : PrimeValue := ⟨680929, pr680929⟩
private theorem pr680959 : PrimeCertificate 680959 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37831]) (by decide +kernel)
def pv680959 : PrimeValue := ⟨680959, pr680959⟩
private theorem pr681067 : PrimeCertificate 681067 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv157,pv241]) (by decide +kernel)
def pv681067 : PrimeValue := ⟨681067, pr681067⟩
private theorem pr681221 : PrimeCertificate 681221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv34061]) (by decide +kernel)
def pv681221 : PrimeValue := ⟨681221, pr681221⟩
private theorem pr681523 : PrimeCertificate 681523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv97,pv1171]) (by decide +kernel)
def pv681523 : PrimeValue := ⟨681523, pr681523⟩
private theorem pr681613 : PrimeCertificate 681613 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv79,pv719]) (by decide +kernel)
def pv681613 : PrimeValue := ⟨681613, pr681613⟩
private theorem pr681773 : PrimeCertificate 681773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv1873]) (by decide +kernel)
def pv681773 : PrimeValue := ⟨681773, pr681773⟩
private theorem pr681787 : PrimeCertificate 681787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv773]) (by decide +kernel)
def pv681787 : PrimeValue := ⟨681787, pr681787⟩
private theorem pr681839 : PrimeCertificate 681839 :=
  certifyPrime (q := pv7) (ls := [pv2,pv340919]) (by decide +kernel)
def pv681839 : PrimeValue := ⟨681839, pr681839⟩
private theorem pr681949 : PrimeCertificate 681949 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv19,pv997]) (by decide +kernel)
def pv681949 : PrimeValue := ⟨681949, pr681949⟩
private theorem pr682069 : PrimeCertificate 682069 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv113,pv503]) (by decide +kernel)
def pv682069 : PrimeValue := ⟨682069, pr682069⟩
private theorem pr682151 : PrimeCertificate 682151 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv1949]) (by decide +kernel)
def pv682151 : PrimeValue := ⟨682151, pr682151⟩
private theorem pr682219 : PrimeCertificate 682219 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv151,pv251]) (by decide +kernel)
def pv682219 : PrimeValue := ⟨682219, pr682219⟩
private theorem pr682373 : PrimeCertificate 682373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv5503]) (by decide +kernel)
def pv682373 : PrimeValue := ⟨682373, pr682373⟩
private theorem pr682489 : PrimeCertificate 682489 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv9479]) (by decide +kernel)
def pv682489 : PrimeValue := ⟨682489, pr682489⟩
private theorem pr682673 : PrimeCertificate 682673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv42667]) (by decide +kernel)
def pv682673 : PrimeValue := ⟨682673, pr682673⟩
private theorem pr682699 : PrimeCertificate 682699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv113783]) (by decide +kernel)
def pv682699 : PrimeValue := ⟨682699, pr682699⟩
private theorem pr682733 : PrimeCertificate 682733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv41,pv181]) (by decide +kernel)
def pv682733 : PrimeValue := ⟨682733, pr682733⟩
private theorem pr682751 : PrimeCertificate 682751 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv2731]) (by decide +kernel)
def pv682751 : PrimeValue := ⟨682751, pr682751⟩
private theorem pr682819 : PrimeCertificate 682819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv317,pv359]) (by decide +kernel)
def pv682819 : PrimeValue := ⟨682819, pr682819⟩
private theorem pr683299 : PrimeCertificate 683299 :=
  certifyPrime (q := pv59) (ls := [pv2,pv3,pv7,pv11,pv17,pv29]) (by decide +kernel)
def pv683299 : PrimeValue := ⟨683299, pr683299⟩
private theorem pr683381 : PrimeCertificate 683381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv47,pv727]) (by decide +kernel)
def pv683381 : PrimeValue := ⟨683381, pr683381⟩
private theorem pr683407 : PrimeCertificate 683407 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37967]) (by decide +kernel)
def pv683407 : PrimeValue := ⟨683407, pr683407⟩
private theorem pr683437 : PrimeCertificate 683437 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv337]) (by decide +kernel)
def pv683437 : PrimeValue := ⟨683437, pr683437⟩
private theorem pr683453 : PrimeCertificate 683453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv317]) (by decide +kernel)
def pv683453 : PrimeValue := ⟨683453, pr683453⟩
private theorem pr683471 : PrimeCertificate 683471 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv41,pv1667]) (by decide +kernel)
def pv683471 : PrimeValue := ⟨683471, pr683471⟩
private theorem pr683489 : PrimeCertificate 683489 :=
  certifyPrime (q := pv19) (ls := [pv2,pv13,pv31,pv53]) (by decide +kernel)
def pv683489 : PrimeValue := ⟨683489, pr683489⟩
private theorem pr683513 : PrimeCertificate 683513 :=
  certifyPrime (q := pv3) (ls := [pv2,pv85439]) (by decide +kernel)
def pv683513 : PrimeValue := ⟨683513, pr683513⟩
private theorem pr683759 : PrimeCertificate 683759 :=
  certifyPrime (q := pv13) (ls := [pv2,pv341879]) (by decide +kernel)
def pv683759 : PrimeValue := ⟨683759, pr683759⟩
private theorem pr683789 : PrimeCertificate 683789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv24421]) (by decide +kernel)
def pv683789 : PrimeValue := ⟨683789, pr683789⟩
private theorem pr683843 : PrimeCertificate 683843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv20113]) (by decide +kernel)
def pv683843 : PrimeValue := ⟨683843, pr683843⟩
private theorem pr683909 : PrimeCertificate 683909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv4621]) (by decide +kernel)
def pv683909 : PrimeValue := ⟨683909, pr683909⟩
private theorem pr684217 : PrimeCertificate 684217 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv17,pv43]) (by decide +kernel)
def pv684217 : PrimeValue := ⟨684217, pr684217⟩
private theorem pr684221 : PrimeCertificate 684221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv34211]) (by decide +kernel)
def pv684221 : PrimeValue := ⟨684221, pr684221⟩
private theorem pr684289 : PrimeCertificate 684289 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv684289 : PrimeValue := ⟨684289, pr684289⟩
private theorem pr684329 : PrimeCertificate 684329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv113,pv757]) (by decide +kernel)
def pv684329 : PrimeValue := ⟨684329, pr684329⟩
private theorem pr684419 : PrimeCertificate 684419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv19,pv31,pv83]) (by decide +kernel)
def pv684419 : PrimeValue := ⟨684419, pr684419⟩
private theorem pr684569 : PrimeCertificate 684569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv85571]) (by decide +kernel)
def pv684569 : PrimeValue := ⟨684569, pr684569⟩
private theorem pr684643 : PrimeCertificate 684643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv16301]) (by decide +kernel)
def pv684643 : PrimeValue := ⟨684643, pr684643⟩
private theorem pr684713 : PrimeCertificate 684713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv12227]) (by decide +kernel)
def pv684713 : PrimeValue := ⟨684713, pr684713⟩
private theorem pr684809 : PrimeCertificate 684809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv85601]) (by decide +kernel)
def pv684809 : PrimeValue := ⟨684809, pr684809⟩
private theorem pr684889 : PrimeCertificate 684889 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv28537]) (by decide +kernel)
def pv684889 : PrimeValue := ⟨684889, pr684889⟩
private theorem pr685031 : PrimeCertificate 685031 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv61,pv1123]) (by decide +kernel)
def pv685031 : PrimeValue := ⟨685031, pr685031⟩
private theorem pr685109 : PrimeCertificate 685109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59,pv2903]) (by decide +kernel)
def pv685109 : PrimeValue := ⟨685109, pr685109⟩
private theorem pr685339 : PrimeCertificate 685339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv6719]) (by decide +kernel)
def pv685339 : PrimeValue := ⟨685339, pr685339⟩
private theorem pr685361 : PrimeCertificate 685361 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv659]) (by decide +kernel)
def pv685361 : PrimeValue := ⟨685361, pr685361⟩
private theorem pr685453 : PrimeCertificate 685453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv239]) (by decide +kernel)
def pv685453 : PrimeValue := ⟨685453, pr685453⟩
private theorem pr685493 : PrimeCertificate 685493 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv7451]) (by decide +kernel)
def pv685493 : PrimeValue := ⟨685493, pr685493⟩
private theorem pr685631 : PrimeCertificate 685631 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv23,pv271]) (by decide +kernel)
def pv685631 : PrimeValue := ⟨685631, pr685631⟩
private theorem pr685723 : PrimeCertificate 685723 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv4969]) (by decide +kernel)
def pv685723 : PrimeValue := ⟨685723, pr685723⟩
private theorem pr685747 : PrimeCertificate 685747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv83]) (by decide +kernel)
def pv685747 : PrimeValue := ⟨685747, pr685747⟩
private theorem pr685781 : PrimeCertificate 685781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv2017]) (by decide +kernel)
def pv685781 : PrimeValue := ⟨685781, pr685781⟩
private theorem pr685849 : PrimeCertificate 685849 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv17,pv41]) (by decide +kernel)
def pv685849 : PrimeValue := ⟨685849, pr685849⟩
private theorem pr685973 : PrimeCertificate 685973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv24499]) (by decide +kernel)
def pv685973 : PrimeValue := ⟨685973, pr685973⟩
private theorem pr686029 : PrimeCertificate 686029 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv8167]) (by decide +kernel)
def pv686029 : PrimeValue := ⟨686029, pr686029⟩
private theorem pr686039 : PrimeCertificate 686039 :=
  certifyPrime (q := pv7) (ls := [pv2,pv343019]) (by decide +kernel)
def pv686039 : PrimeValue := ⟨686039, pr686039⟩
private theorem pr686051 : PrimeCertificate 686051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13721]) (by decide +kernel)
def pv686051 : PrimeValue := ⟨686051, pr686051⟩
private theorem pr686201 : PrimeCertificate 686201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv47,pv73]) (by decide +kernel)
def pv686201 : PrimeValue := ⟨686201, pr686201⟩
private theorem pr686317 : PrimeCertificate 686317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv57193]) (by decide +kernel)
def pv686317 : PrimeValue := ⟨686317, pr686317⟩
private theorem pr686333 : PrimeCertificate 686333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv171583]) (by decide +kernel)
def pv686333 : PrimeValue := ⟨686333, pr686333⟩
private theorem pr686363 : PrimeCertificate 686363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv113,pv3037]) (by decide +kernel)
def pv686363 : PrimeValue := ⟨686363, pr686363⟩
private theorem pr686449 : PrimeCertificate 686449 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv227]) (by decide +kernel)
def pv686449 : PrimeValue := ⟨686449, pr686449⟩
private theorem pr686513 : PrimeCertificate 686513 :=
  certifyPrime (q := pv3) (ls := [pv2,pv107,pv401]) (by decide +kernel)
def pv686513 : PrimeValue := ⟨686513, pr686513⟩
private theorem pr686737 : PrimeCertificate 686737 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv19,pv251]) (by decide +kernel)
def pv686737 : PrimeValue := ⟨686737, pr686737⟩
private theorem pr686773 : PrimeCertificate 686773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv6359]) (by decide +kernel)
def pv686773 : PrimeValue := ⟨686773, pr686773⟩
private theorem pr687019 : PrimeCertificate 687019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv67,pv1709]) (by decide +kernel)
def pv687019 : PrimeValue := ⟨687019, pr687019⟩
private theorem pr687041 : PrimeCertificate 687041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv19,pv113]) (by decide +kernel)
def pv687041 : PrimeValue := ⟨687041, pr687041⟩
private theorem pr687289 : PrimeCertificate 687289 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv7,pv4091]) (by decide +kernel)
def pv687289 : PrimeValue := ⟨687289, pr687289⟩
private theorem pr687341 : PrimeCertificate 687341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv34367]) (by decide +kernel)
def pv687341 : PrimeValue := ⟨687341, pr687341⟩
private theorem pr687359 : PrimeCertificate 687359 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv29,pv1693]) (by decide +kernel)
def pv687359 : PrimeValue := ⟨687359, pr687359⟩
private theorem pr687397 : PrimeCertificate 687397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv57283]) (by decide +kernel)
def pv687397 : PrimeValue := ⟨687397, pr687397⟩
private theorem pr687413 : PrimeCertificate 687413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv17,pv919]) (by decide +kernel)
def pv687413 : PrimeValue := ⟨687413, pr687413⟩
private theorem pr687443 : PrimeCertificate 687443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv49103]) (by decide +kernel)
def pv687443 : PrimeValue := ⟨687443, pr687443⟩
private theorem pr687521 : PrimeCertificate 687521 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv4297]) (by decide +kernel)
def pv687521 : PrimeValue := ⟨687521, pr687521⟩
private theorem pr687551 : PrimeCertificate 687551 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13751]) (by decide +kernel)
def pv687551 : PrimeValue := ⟨687551, pr687551⟩
private theorem pr687773 : PrimeCertificate 687773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv139,pv1237]) (by decide +kernel)
def pv687773 : PrimeValue := ⟨687773, pr687773⟩
private theorem pr687823 : PrimeCertificate 687823 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv29,pv59,pv67]) (by decide +kernel)
def pv687823 : PrimeValue := ⟨687823, pr687823⟩
private theorem pr687839 : PrimeCertificate 687839 :=
  certifyPrime (q := pv19) (ls := [pv2,pv19,pv23,pv787]) (by decide +kernel)
def pv687839 : PrimeValue := ⟨687839, pr687839⟩
private theorem pr688027 : PrimeCertificate 688027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv114671]) (by decide +kernel)
def pv688027 : PrimeValue := ⟨688027, pr688027⟩
private theorem pr688073 : PrimeCertificate 688073 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11,pv1117]) (by decide +kernel)
def pv688073 : PrimeValue := ⟨688073, pr688073⟩
private theorem pr688087 : PrimeCertificate 688087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv43,pv127]) (by decide +kernel)
def pv688087 : PrimeValue := ⟨688087, pr688087⟩
private theorem pr688159 : PrimeCertificate 688159 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv38231]) (by decide +kernel)
def pv688159 : PrimeValue := ⟨688159, pr688159⟩
private theorem pr688223 : PrimeCertificate 688223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv344111]) (by decide +kernel)
def pv688223 : PrimeValue := ⟨688223, pr688223⟩
private theorem pr688297 : PrimeCertificate 688297 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv17,pv241]) (by decide +kernel)
def pv688297 : PrimeValue := ⟨688297, pr688297⟩
private theorem pr688309 : PrimeCertificate 688309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv1399]) (by decide +kernel)
def pv688309 : PrimeValue := ⟨688309, pr688309⟩
private theorem pr688393 : PrimeCertificate 688393 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3187]) (by decide +kernel)
def pv688393 : PrimeValue := ⟨688393, pr688393⟩
private theorem pr688423 : PrimeCertificate 688423 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv37,pv443]) (by decide +kernel)
def pv688423 : PrimeValue := ⟨688423, pr688423⟩
private theorem pr688477 : PrimeCertificate 688477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv57373]) (by decide +kernel)
def pv688477 : PrimeValue := ⟨688477, pr688477⟩
private theorem pr688511 : PrimeCertificate 688511 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv31,pv2221]) (by decide +kernel)
def pv688511 : PrimeValue := ⟨688511, pr688511⟩
private theorem pr688679 : PrimeCertificate 688679 :=
  certifyPrime (q := pv19) (ls := [pv2,pv149,pv2311]) (by decide +kernel)
def pv688679 : PrimeValue := ⟨688679, pr688679⟩
private theorem pr688957 : PrimeCertificate 688957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv57413]) (by decide +kernel)
def pv688957 : PrimeValue := ⟨688957, pr688957⟩
private theorem pr688969 : PrimeCertificate 688969 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv1367]) (by decide +kernel)
def pv688969 : PrimeValue := ⟨688969, pr688969⟩
private theorem pr688999 : PrimeCertificate 688999 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv114833]) (by decide +kernel)
def pv688999 : PrimeValue := ⟨688999, pr688999⟩
private theorem pr689033 : PrimeCertificate 689033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43,pv2003]) (by decide +kernel)
def pv689033 : PrimeValue := ⟨689033, pr689033⟩
private theorem pr689077 : PrimeCertificate 689077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19141]) (by decide +kernel)
def pv689077 : PrimeValue := ⟨689077, pr689077⟩
private theorem pr689081 : PrimeCertificate 689081 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv23,pv107]) (by decide +kernel)
def pv689081 : PrimeValue := ⟨689081, pr689081⟩
private theorem pr689089 : PrimeCertificate 689089 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv37,pv97]) (by decide +kernel)
def pv689089 : PrimeValue := ⟨689089, pr689089⟩
private theorem pr689093 : PrimeCertificate 689093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv9067]) (by decide +kernel)
def pv689093 : PrimeValue := ⟨689093, pr689093⟩
private theorem pr689219 : PrimeCertificate 689219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv14983]) (by decide +kernel)
def pv689219 : PrimeValue := ⟨689219, pr689219⟩
private theorem pr689233 : PrimeCertificate 689233 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv83,pv173]) (by decide +kernel)
def pv689233 : PrimeValue := ⟨689233, pr689233⟩
private theorem pr689383 : PrimeCertificate 689383 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv38299]) (by decide +kernel)
def pv689383 : PrimeValue := ⟨689383, pr689383⟩
private theorem pr689411 : PrimeCertificate 689411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv71,pv971]) (by decide +kernel)
def pv689411 : PrimeValue := ⟨689411, pr689411⟩
private theorem pr689509 : PrimeCertificate 689509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv107,pv179]) (by decide +kernel)
def pv689509 : PrimeValue := ⟨689509, pr689509⟩
private theorem pr689599 : PrimeCertificate 689599 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv421]) (by decide +kernel)
def pv689599 : PrimeValue := ⟨689599, pr689599⟩
private theorem pr689603 : PrimeCertificate 689603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv344801]) (by decide +kernel)
def pv689603 : PrimeValue := ⟨689603, pr689603⟩
private theorem pr689629 : PrimeCertificate 689629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv101,pv569]) (by decide +kernel)
def pv689629 : PrimeValue := ⟨689629, pr689629⟩
private theorem pr689693 : PrimeCertificate 689693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv172423]) (by decide +kernel)
def pv689693 : PrimeValue := ⟨689693, pr689693⟩
private theorem pr689723 : PrimeCertificate 689723 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv107,pv293]) (by decide +kernel)
def pv689723 : PrimeValue := ⟨689723, pr689723⟩
private theorem pr689789 : PrimeCertificate 689789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv61,pv257]) (by decide +kernel)
def pv689789 : PrimeValue := ⟨689789, pr689789⟩
private theorem pr689797 : PrimeCertificate 689797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv2129]) (by decide +kernel)
def pv689797 : PrimeValue := ⟨689797, pr689797⟩
private theorem pr689831 : PrimeCertificate 689831 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv101,pv683]) (by decide +kernel)
def pv689831 : PrimeValue := ⟨689831, pr689831⟩
private theorem pr689929 : PrimeCertificate 689929 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv17,pv19,pv89]) (by decide +kernel)
def pv689929 : PrimeValue := ⟨689929, pr689929⟩
private theorem pr690127 : PrimeCertificate 690127 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv115021]) (by decide +kernel)
def pv690127 : PrimeValue := ⟨690127, pr690127⟩
private theorem pr690281 : PrimeCertificate 690281 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17257]) (by decide +kernel)
def pv690281 : PrimeValue := ⟨690281, pr690281⟩
private theorem pr690491 : PrimeCertificate 690491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29,pv2381]) (by decide +kernel)
def pv690491 : PrimeValue := ⟨690491, pr690491⟩
private theorem pr690553 : PrimeCertificate 690553 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv139]) (by decide +kernel)
def pv690553 : PrimeValue := ⟨690553, pr690553⟩
private theorem pr690719 : PrimeCertificate 690719 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv103,pv479]) (by decide +kernel)
def pv690719 : PrimeValue := ⟨690719, pr690719⟩
private theorem pr690869 : PrimeCertificate 690869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv172717]) (by decide +kernel)
def pv690869 : PrimeValue := ⟨690869, pr690869⟩
private theorem pr690929 : PrimeCertificate 690929 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv31,pv199]) (by decide +kernel)
def pv690929 : PrimeValue := ⟨690929, pr690929⟩
private theorem pr690953 : PrimeCertificate 690953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv86369]) (by decide +kernel)
def pv690953 : PrimeValue := ⟨690953, pr690953⟩
private theorem pr690997 : PrimeCertificate 690997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv89,pv647]) (by decide +kernel)
def pv690997 : PrimeValue := ⟨690997, pr690997⟩
private theorem pr691079 : PrimeCertificate 691079 :=
  certifyPrime (q := pv7) (ls := [pv2,pv233,pv1483]) (by decide +kernel)
def pv691079 : PrimeValue := ⟨691079, pr691079⟩
private theorem pr691121 : PrimeCertificate 691121 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv53,pv163]) (by decide +kernel)
def pv691121 : PrimeValue := ⟨691121, pr691121⟩
private theorem pr691189 : PrimeCertificate 691189 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv239,pv241]) (by decide +kernel)
def pv691189 : PrimeValue := ⟨691189, pr691189⟩
private theorem pr691333 : PrimeCertificate 691333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53,pv1087]) (by decide +kernel)
def pv691333 : PrimeValue := ⟨691333, pr691333⟩
private theorem pr691363 : PrimeCertificate 691363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv31,pv59]) (by decide +kernel)
def pv691363 : PrimeValue := ⟨691363, pr691363⟩
private theorem pr691399 : PrimeCertificate 691399 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv71,pv541]) (by decide +kernel)
def pv691399 : PrimeValue := ⟨691399, pr691399⟩
private theorem pr691409 : PrimeCertificate 691409 :=
  certifyPrime (q := pv3) (ls := [pv2,pv79,pv547]) (by decide +kernel)
def pv691409 : PrimeValue := ⟨691409, pr691409⟩
private theorem pr691499 : PrimeCertificate 691499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv345749]) (by decide +kernel)
def pv691499 : PrimeValue := ⟨691499, pr691499⟩
private theorem pr691573 : PrimeCertificate 691573 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv7,pv8233]) (by decide +kernel)
def pv691573 : PrimeValue := ⟨691573, pr691573⟩
private theorem pr691661 : PrimeCertificate 691661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv34583]) (by decide +kernel)
def pv691661 : PrimeValue := ⟨691661, pr691661⟩
private theorem pr691723 : PrimeCertificate 691723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv83,pv463]) (by decide +kernel)
def pv691723 : PrimeValue := ⟨691723, pr691723⟩
private theorem pr691729 : PrimeCertificate 691729 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv14411]) (by decide +kernel)
def pv691729 : PrimeValue := ⟨691729, pr691729⟩
private theorem pr691739 : PrimeCertificate 691739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv345869]) (by decide +kernel)
def pv691739 : PrimeValue := ⟨691739, pr691739⟩
private theorem pr691829 : PrimeCertificate 691829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv9103]) (by decide +kernel)
def pv691829 : PrimeValue := ⟨691829, pr691829⟩
private theorem pr691871 : PrimeCertificate 691871 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv43,pv1609]) (by decide +kernel)
def pv691871 : PrimeValue := ⟨691871, pr691871⟩
private theorem pr691973 : PrimeCertificate 691973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv172993]) (by decide +kernel)
def pv691973 : PrimeValue := ⟨691973, pr691973⟩
private theorem pr691979 : PrimeCertificate 691979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv23,pv307]) (by decide +kernel)
def pv691979 : PrimeValue := ⟨691979, pr691979⟩
private theorem pr691991 : PrimeCertificate 691991 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv13,pv5323]) (by decide +kernel)
def pv691991 : PrimeValue := ⟨691991, pr691991⟩
private theorem pr692017 : PrimeCertificate 692017 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv1109]) (by decide +kernel)
def pv692017 : PrimeValue := ⟨692017, pr692017⟩
private theorem pr692059 : PrimeCertificate 692059 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv115343]) (by decide +kernel)
def pv692059 : PrimeValue := ⟨692059, pr692059⟩
private theorem pr692239 : PrimeCertificate 692239 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv113,pv1021]) (by decide +kernel)
def pv692239 : PrimeValue := ⟨692239, pr692239⟩
private theorem pr692249 : PrimeCertificate 692249 :=
  certifyPrime (q := pv3) (ls := [pv2,pv86531]) (by decide +kernel)
def pv692249 : PrimeValue := ⟨692249, pr692249⟩
private theorem pr692269 : PrimeCertificate 692269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv57689]) (by decide +kernel)
def pv692269 : PrimeValue := ⟨692269, pr692269⟩
private theorem pr692287 : PrimeCertificate 692287 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv53,pv311]) (by decide +kernel)
def pv692287 : PrimeValue := ⟨692287, pr692287⟩
private theorem pr692309 : PrimeCertificate 692309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv10181]) (by decide +kernel)
def pv692309 : PrimeValue := ⟨692309, pr692309⟩
private theorem pr692423 : PrimeCertificate 692423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv461,pv751]) (by decide +kernel)
def pv692423 : PrimeValue := ⟨692423, pr692423⟩
private theorem pr692459 : PrimeCertificate 692459 :=
  certifyPrime (q := pv11) (ls := [pv2,pv13,pv26633]) (by decide +kernel)
def pv692459 : PrimeValue := ⟨692459, pr692459⟩
private theorem pr692591 : PrimeCertificate 692591 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv69259]) (by decide +kernel)
def pv692591 : PrimeValue := ⟨692591, pr692591⟩
private theorem pr692647 : PrimeCertificate 692647 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv67,pv1723]) (by decide +kernel)
def pv692647 : PrimeValue := ⟨692647, pr692647⟩
private theorem pr692651 : PrimeCertificate 692651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv1979]) (by decide +kernel)
def pv692651 : PrimeValue := ⟨692651, pr692651⟩
private theorem pr692663 : PrimeCertificate 692663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv346331]) (by decide +kernel)
def pv692663 : PrimeValue := ⟨692663, pr692663⟩
private theorem pr692707 : PrimeCertificate 692707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv16493]) (by decide +kernel)
def pv692707 : PrimeValue := ⟨692707, pr692707⟩
private theorem pr692729 : PrimeCertificate 692729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv131,pv661]) (by decide +kernel)
def pv692729 : PrimeValue := ⟨692729, pr692729⟩
private theorem pr692743 : PrimeCertificate 692743 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv263,pv439]) (by decide +kernel)
def pv692743 : PrimeValue := ⟨692743, pr692743⟩
private theorem pr692753 : PrimeCertificate 692753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv1493]) (by decide +kernel)
def pv692753 : PrimeValue := ⟨692753, pr692753⟩
private theorem pr692779 : PrimeCertificate 692779 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv19,pv59,pv103]) (by decide +kernel)
def pv692779 : PrimeValue := ⟨692779, pr692779⟩
private theorem pr692917 : PrimeCertificate 692917 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv73,pv113]) (by decide +kernel)
def pv692917 : PrimeValue := ⟨692917, pr692917⟩
private theorem pr692983 : PrimeCertificate 692983 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41,pv313]) (by decide +kernel)
def pv692983 : PrimeValue := ⟨692983, pr692983⟩
private theorem pr693041 : PrimeCertificate 693041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv8663]) (by decide +kernel)
def pv693041 : PrimeValue := ⟨693041, pr693041⟩
private theorem pr693079 : PrimeCertificate 693079 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv115513]) (by decide +kernel)
def pv693079 : PrimeValue := ⟨693079, pr693079⟩
private theorem pr693089 : PrimeCertificate 693089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv179]) (by decide +kernel)
def pv693089 : PrimeValue := ⟨693089, pr693089⟩
private theorem pr693157 : PrimeCertificate 693157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv1229]) (by decide +kernel)
def pv693157 : PrimeValue := ⟨693157, pr693157⟩
private theorem pr693337 : PrimeCertificate 693337 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv4127]) (by decide +kernel)
def pv693337 : PrimeValue := ⟨693337, pr693337⟩
private theorem pr693403 : PrimeCertificate 693403 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv163,pv709]) (by decide +kernel)
def pv693403 : PrimeValue := ⟨693403, pr693403⟩
private theorem pr693409 : PrimeCertificate 693409 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv31,pv233]) (by decide +kernel)
def pv693409 : PrimeValue := ⟨693409, pr693409⟩
private theorem pr693431 : PrimeCertificate 693431 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv17,pv4079]) (by decide +kernel)
def pv693431 : PrimeValue := ⟨693431, pr693431⟩
private theorem pr693487 : PrimeCertificate 693487 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv59,pv653]) (by decide +kernel)
def pv693487 : PrimeValue := ⟨693487, pr693487⟩
private theorem pr693503 : PrimeCertificate 693503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv346751]) (by decide +kernel)
def pv693503 : PrimeValue := ⟨693503, pr693503⟩
private theorem pr693529 : PrimeCertificate 693529 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv11,pv37,pv71]) (by decide +kernel)
def pv693529 : PrimeValue := ⟨693529, pr693529⟩
private theorem pr693619 : PrimeCertificate 693619 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv115603]) (by decide +kernel)
def pv693619 : PrimeValue := ⟨693619, pr693619⟩
private theorem pr693629 : PrimeCertificate 693629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv13339]) (by decide +kernel)
def pv693629 : PrimeValue := ⟨693629, pr693629⟩
private theorem pr693683 : PrimeCertificate 693683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv31531]) (by decide +kernel)
def pv693683 : PrimeValue := ⟨693683, pr693683⟩
private theorem pr693701 : PrimeCertificate 693701 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv991]) (by decide +kernel)
def pv693701 : PrimeValue := ⟨693701, pr693701⟩
private theorem pr693727 : PrimeCertificate 693727 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv23,pv457]) (by decide +kernel)
def pv693727 : PrimeValue := ⟨693727, pr693727⟩
private theorem pr693739 : PrimeCertificate 693739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv443]) (by decide +kernel)
def pv693739 : PrimeValue := ⟨693739, pr693739⟩
private theorem pr693793 : PrimeCertificate 693793 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv11,pv73]) (by decide +kernel)
def pv693793 : PrimeValue := ⟨693793, pr693793⟩
private theorem pr694033 : PrimeCertificate 694033 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv19,pv761]) (by decide +kernel)
def pv694033 : PrimeValue := ⟨694033, pr694033⟩
private theorem pr694039 : PrimeCertificate 694039 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv131,pv883]) (by decide +kernel)
def pv694039 : PrimeValue := ⟨694039, pr694039⟩
private theorem pr694091 : PrimeCertificate 694091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31,pv2239]) (by decide +kernel)
def pv694091 : PrimeValue := ⟨694091, pr694091⟩
private theorem pr694123 : PrimeCertificate 694123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv13,pv809]) (by decide +kernel)
def pv694123 : PrimeValue := ⟨694123, pr694123⟩
private theorem pr694313 : PrimeCertificate 694313 :=
  certifyPrime (q := pv3) (ls := [pv2,pv59,pv1471]) (by decide +kernel)
def pv694313 : PrimeValue := ⟨694313, pr694313⟩
private theorem pr694327 : PrimeCertificate 694327 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv97,pv1193]) (by decide +kernel)
def pv694327 : PrimeValue := ⟨694327, pr694327⟩
private theorem pr694409 : PrimeCertificate 694409 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv13,pv607]) (by decide +kernel)
def pv694409 : PrimeValue := ⟨694409, pr694409⟩
private theorem pr694481 : PrimeCertificate 694481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv8681]) (by decide +kernel)
def pv694481 : PrimeValue := ⟨694481, pr694481⟩
private theorem pr694541 : PrimeCertificate 694541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv41]) (by decide +kernel)
def pv694541 : PrimeValue := ⟨694541, pr694541⟩
private theorem pr694549 : PrimeCertificate 694549 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv59,pv109]) (by decide +kernel)
def pv694549 : PrimeValue := ⟨694549, pr694549⟩
private theorem pr694633 : PrimeCertificate 694633 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv103,pv281]) (by decide +kernel)
def pv694633 : PrimeValue := ⟨694633, pr694633⟩
private theorem pr694747 : PrimeCertificate 694747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv2969]) (by decide +kernel)
def pv694747 : PrimeValue := ⟨694747, pr694747⟩
private theorem pr694873 : PrimeCertificate 694873 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv3217]) (by decide +kernel)
def pv694873 : PrimeValue := ⟨694873, pr694873⟩
private theorem pr694987 : PrimeCertificate 694987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv115831]) (by decide +kernel)
def pv694987 : PrimeValue := ⟨694987, pr694987⟩
private theorem pr695021 : PrimeCertificate 695021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv31,pv59]) (by decide +kernel)
def pv695021 : PrimeValue := ⟨695021, pr695021⟩
private theorem pr695089 : PrimeCertificate 695089 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1609]) (by decide +kernel)
def pv695089 : PrimeValue := ⟨695089, pr695089⟩
private theorem pr695099 : PrimeCertificate 695099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv367,pv947]) (by decide +kernel)
def pv695099 : PrimeValue := ⟨695099, pr695099⟩
private theorem pr695141 : PrimeCertificate 695141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv34757]) (by decide +kernel)
def pv695141 : PrimeValue := ⟨695141, pr695141⟩
private theorem pr695171 : PrimeCertificate 695171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv9931]) (by decide +kernel)
def pv695171 : PrimeValue := ⟨695171, pr695171⟩
private theorem pr695257 : PrimeCertificate 695257 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv59,pv491]) (by decide +kernel)
def pv695257 : PrimeValue := ⟨695257, pr695257⟩
private theorem pr695309 : PrimeCertificate 695309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv173827]) (by decide +kernel)
def pv695309 : PrimeValue := ⟨695309, pr695309⟩
private theorem pr695323 : PrimeCertificate 695323 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv38629]) (by decide +kernel)
def pv695323 : PrimeValue := ⟨695323, pr695323⟩
private theorem pr695407 : PrimeCertificate 695407 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv115901]) (by decide +kernel)
def pv695407 : PrimeValue := ⟨695407, pr695407⟩
private theorem pr695599 : PrimeCertificate 695599 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv115933]) (by decide +kernel)
def pv695599 : PrimeValue := ⟨695599, pr695599⟩
private theorem pr695603 : PrimeCertificate 695603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv347801]) (by decide +kernel)
def pv695603 : PrimeValue := ⟨695603, pr695603⟩
private theorem pr695677 : PrimeCertificate 695677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv57973]) (by decide +kernel)
def pv695677 : PrimeValue := ⟨695677, pr695677⟩
private theorem pr695689 : PrimeCertificate 695689 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv41,pv101]) (by decide +kernel)
def pv695689 : PrimeValue := ⟨695689, pr695689⟩
private theorem pr695719 : PrimeCertificate 695719 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv38651]) (by decide +kernel)
def pv695719 : PrimeValue := ⟨695719, pr695719⟩
private theorem pr695743 : PrimeCertificate 695743 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv19,pv359]) (by decide +kernel)
def pv695743 : PrimeValue := ⟨695743, pr695743⟩
private theorem pr696263 : PrimeCertificate 696263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv41,pv1213]) (by decide +kernel)
def pv696263 : PrimeValue := ⟨696263, pr696263⟩
private theorem pr696403 : PrimeCertificate 696403 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv5527]) (by decide +kernel)
def pv696403 : PrimeValue := ⟨696403, pr696403⟩
private theorem pr696427 : PrimeCertificate 696427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv41,pv149]) (by decide +kernel)
def pv696427 : PrimeValue := ⟨696427, pr696427⟩
private theorem pr696491 : PrimeCertificate 696491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv241]) (by decide +kernel)
def pv696491 : PrimeValue := ⟨696491, pr696491⟩
private theorem pr696607 : PrimeCertificate 696607 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv116101]) (by decide +kernel)
def pv696607 : PrimeValue := ⟨696607, pr696607⟩
private theorem pr696809 : PrimeCertificate 696809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv23,pv541]) (by decide +kernel)
def pv696809 : PrimeValue := ⟨696809, pr696809⟩
private theorem pr696823 : PrimeCertificate 696823 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv47,pv353]) (by decide +kernel)
def pv696823 : PrimeValue := ⟨696823, pr696823⟩
private theorem pr696889 : PrimeCertificate 696889 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv9679]) (by decide +kernel)
def pv696889 : PrimeValue := ⟨696889, pr696889⟩
private theorem pr696937 : PrimeCertificate 696937 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv71,pv409]) (by decide +kernel)
def pv696937 : PrimeValue := ⟨696937, pr696937⟩
private theorem pr696989 : PrimeCertificate 696989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv163,pv1069]) (by decide +kernel)
def pv696989 : PrimeValue := ⟨696989, pr696989⟩
private theorem pr697013 : PrimeCertificate 697013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv271,pv643]) (by decide +kernel)
def pv697013 : PrimeValue := ⟨697013, pr697013⟩
private theorem pr697033 : PrimeCertificate 697033 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv461]) (by decide +kernel)
def pv697033 : PrimeValue := ⟨697033, pr697033⟩
private theorem pr697087 : PrimeCertificate 697087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv331]) (by decide +kernel)
def pv697087 : PrimeValue := ⟨697087, pr697087⟩
private theorem pr697211 : PrimeCertificate 697211 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv113,pv617]) (by decide +kernel)
def pv697211 : PrimeValue := ⟨697211, pr697211⟩
private theorem pr697267 : PrimeCertificate 697267 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv38737]) (by decide +kernel)
def pv697267 : PrimeValue := ⟨697267, pr697267⟩
private theorem pr697373 : PrimeCertificate 697373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv13411]) (by decide +kernel)
def pv697373 : PrimeValue := ⟨697373, pr697373⟩
private theorem pr697519 : PrimeCertificate 697519 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv12917]) (by decide +kernel)
def pv697519 : PrimeValue := ⟨697519, pr697519⟩
private theorem pr697523 : PrimeCertificate 697523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv49823]) (by decide +kernel)
def pv697523 : PrimeValue := ⟨697523, pr697523⟩
private theorem pr697583 : PrimeCertificate 697583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv89,pv3919]) (by decide +kernel)
def pv697583 : PrimeValue := ⟨697583, pr697583⟩
private theorem pr697673 : PrimeCertificate 697673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv2357]) (by decide +kernel)
def pv697673 : PrimeValue := ⟨697673, pr697673⟩
private theorem pr697733 : PrimeCertificate 697733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv24919]) (by decide +kernel)
def pv697733 : PrimeValue := ⟨697733, pr697733⟩
private theorem pr697759 : PrimeCertificate 697759 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv116293]) (by decide +kernel)
def pv697759 : PrimeValue := ⟨697759, pr697759⟩
private theorem pr697897 : PrimeCertificate 697897 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv359]) (by decide +kernel)
def pv697897 : PrimeValue := ⟨697897, pr697897⟩
private theorem pr697909 : PrimeCertificate 697909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv3061]) (by decide +kernel)
def pv697909 : PrimeValue := ⟨697909, pr697909⟩
private theorem pr697993 : PrimeCertificate 697993 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv127,pv229]) (by decide +kernel)
def pv697993 : PrimeValue := ⟨697993, pr697993⟩
private theorem pr698051 : PrimeCertificate 698051 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv23,pv607]) (by decide +kernel)
def pv698051 : PrimeValue := ⟨698051, pr698051⟩
private theorem pr698053 : PrimeCertificate 698053 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv58171]) (by decide +kernel)
def pv698053 : PrimeValue := ⟨698053, pr698053⟩
private theorem pr698083 : PrimeCertificate 698083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv1511]) (by decide +kernel)
def pv698083 : PrimeValue := ⟨698083, pr698083⟩
private theorem pr698111 : PrimeCertificate 698111 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv9973]) (by decide +kernel)
def pv698111 : PrimeValue := ⟨698111, pr698111⟩
private theorem pr698239 : PrimeCertificate 698239 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv38791]) (by decide +kernel)
def pv698239 : PrimeValue := ⟨698239, pr698239⟩
private theorem pr698261 : PrimeCertificate 698261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv34913]) (by decide +kernel)
def pv698261 : PrimeValue := ⟨698261, pr698261⟩
private theorem pr698273 : PrimeCertificate 698273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv21821]) (by decide +kernel)
def pv698273 : PrimeValue := ⟨698273, pr698273⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
