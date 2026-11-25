/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table125
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table125.pv698287
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table016
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table020
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table027
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table028
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table043
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table093
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table094

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr698287 : PrimeCertificate 698287 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv116381]) (by decide +kernel)
def pv698287 : PrimeValue := ⟨698287, pr698287⟩
private theorem pr698293 : PrimeCertificate 698293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv163]) (by decide +kernel)
def pv698293 : PrimeValue := ⟨698293, pr698293⟩
private theorem pr698339 : PrimeCertificate 698339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv9437]) (by decide +kernel)
def pv698339 : PrimeValue := ⟨698339, pr698339⟩
private theorem pr698531 : PrimeCertificate 698531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv17,pv587]) (by decide +kernel)
def pv698531 : PrimeValue := ⟨698531, pr698531⟩
private theorem pr698543 : PrimeCertificate 698543 :=
  certifyPrime (q := pv37) (ls := [pv2,pv13,pv67,pv401]) (by decide +kernel)
def pv698543 : PrimeValue := ⟨698543, pr698543⟩
private theorem pr698557 : PrimeCertificate 698557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv2531]) (by decide +kernel)
def pv698557 : PrimeValue := ⟨698557, pr698557⟩
private theorem pr698669 : PrimeCertificate 698669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv29,pv317]) (by decide +kernel)
def pv698669 : PrimeValue := ⟨698669, pr698669⟩
private theorem pr698723 : PrimeCertificate 698723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv8521]) (by decide +kernel)
def pv698723 : PrimeValue := ⟨698723, pr698723⟩
private theorem pr698891 : PrimeCertificate 698891 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv47,pv1487]) (by decide +kernel)
def pv698891 : PrimeValue := ⟨698891, pr698891⟩
private theorem pr698923 : PrimeCertificate 698923 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv43]) (by decide +kernel)
def pv698923 : PrimeValue := ⟨698923, pr698923⟩
private theorem pr699053 : PrimeCertificate 699053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv174763]) (by decide +kernel)
def pv699053 : PrimeValue := ⟨699053, pr699053⟩
private theorem pr699113 : PrimeCertificate 699113 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv2819]) (by decide +kernel)
def pv699113 : PrimeValue := ⟨699113, pr699113⟩
private theorem pr699299 : PrimeCertificate 699299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv11279]) (by decide +kernel)
def pv699299 : PrimeValue := ⟨699299, pr699299⟩
private theorem pr699343 : PrimeCertificate 699343 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv16651]) (by decide +kernel)
def pv699343 : PrimeValue := ⟨699343, pr699343⟩
private theorem pr699373 : PrimeCertificate 699373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19427]) (by decide +kernel)
def pv699373 : PrimeValue := ⟨699373, pr699373⟩
private theorem pr699379 : PrimeCertificate 699379 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41,pv2843]) (by decide +kernel)
def pv699379 : PrimeValue := ⟨699379, pr699379⟩
private theorem pr699641 : PrimeCertificate 699641 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17491]) (by decide +kernel)
def pv699641 : PrimeValue := ⟨699641, pr699641⟩
private theorem pr699649 : PrimeCertificate 699649 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv911]) (by decide +kernel)
def pv699649 : PrimeValue := ⟨699649, pr699649⟩
private theorem pr699709 : PrimeCertificate 699709 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv58309]) (by decide +kernel)
def pv699709 : PrimeValue := ⟨699709, pr699709⟩
private theorem pr699719 : PrimeCertificate 699719 :=
  certifyPrime (q := pv11) (ls := [pv2,pv89,pv3931]) (by decide +kernel)
def pv699719 : PrimeValue := ⟨699719, pr699719⟩
private theorem pr699733 : PrimeCertificate 699733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv19,pv31]) (by decide +kernel)
def pv699733 : PrimeValue := ⟨699733, pr699733⟩
private theorem pr699791 : PrimeCertificate 699791 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv7,pv13,pv769]) (by decide +kernel)
def pv699791 : PrimeValue := ⟨699791, pr699791⟩
private theorem pr700079 : PrimeCertificate 700079 :=
  certifyPrime (q := pv7) (ls := [pv2,pv350039]) (by decide +kernel)
def pv700079 : PrimeValue := ⟨700079, pr700079⟩
private theorem pr700099 : PrimeCertificate 700099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv79,pv211]) (by decide +kernel)
def pv700099 : PrimeValue := ⟨700099, pr700099⟩
private theorem pr700211 : PrimeCertificate 700211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv1429]) (by decide +kernel)
def pv700211 : PrimeValue := ⟨700211, pr700211⟩
private theorem pr700237 : PrimeCertificate 700237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53,pv367]) (by decide +kernel)
def pv700237 : PrimeValue := ⟨700237, pr700237⟩
private theorem pr700393 : PrimeCertificate 700393 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv379]) (by decide +kernel)
def pv700393 : PrimeValue := ⟨700393, pr700393⟩
private theorem pr700423 : PrimeCertificate 700423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv107,pv1091]) (by decide +kernel)
def pv700423 : PrimeValue := ⟨700423, pr700423⟩
private theorem pr700643 : PrimeCertificate 700643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv8147]) (by decide +kernel)
def pv700643 : PrimeValue := ⟨700643, pr700643⟩
private theorem pr700759 : PrimeCertificate 700759 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv19,pv683]) (by decide +kernel)
def pv700759 : PrimeValue := ⟨700759, pr700759⟩
private theorem pr700811 : PrimeCertificate 700811 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv11,pv23,pv277]) (by decide +kernel)
def pv700811 : PrimeValue := ⟨700811, pr700811⟩
private theorem pr700883 : PrimeCertificate 700883 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv13,pv3851]) (by decide +kernel)
def pv700883 : PrimeValue := ⟨700883, pr700883⟩
private theorem pr701009 : PrimeCertificate 701009 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11,pv569]) (by decide +kernel)
def pv701009 : PrimeValue := ⟨701009, pr701009⟩
private theorem pr701047 : PrimeCertificate 701047 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv29,pv79]) (by decide +kernel)
def pv701047 : PrimeValue := ⟨701047, pr701047⟩
private theorem pr701179 : PrimeCertificate 701179 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv5081]) (by decide +kernel)
def pv701179 : PrimeValue := ⟨701179, pr701179⟩
private theorem pr701219 : PrimeCertificate 701219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv50087]) (by decide +kernel)
def pv701219 : PrimeValue := ⟨701219, pr701219⟩
private theorem pr701383 : PrimeCertificate 701383 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv10627]) (by decide +kernel)
def pv701383 : PrimeValue := ⟨701383, pr701383⟩
private theorem pr701399 : PrimeCertificate 701399 :=
  certifyPrime (q := pv41) (ls := [pv2,pv350699]) (by decide +kernel)
def pv701399 : PrimeValue := ⟨701399, pr701399⟩
private theorem pr701413 : PrimeCertificate 701413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv58451]) (by decide +kernel)
def pv701413 : PrimeValue := ⟨701413, pr701413⟩
private theorem pr701443 : PrimeCertificate 701443 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv19,pv293]) (by decide +kernel)
def pv701443 : PrimeValue := ⟨701443, pr701443⟩
private theorem pr701497 : PrimeCertificate 701497 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv9743]) (by decide +kernel)
def pv701497 : PrimeValue := ⟨701497, pr701497⟩
private theorem pr701527 : PrimeCertificate 701527 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv16703]) (by decide +kernel)
def pv701527 : PrimeValue := ⟨701527, pr701527⟩
private theorem pr701579 : PrimeCertificate 701579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv350789]) (by decide +kernel)
def pv701579 : PrimeValue := ⟨701579, pr701579⟩
private theorem pr701593 : PrimeCertificate 701593 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv31,pv41]) (by decide +kernel)
def pv701593 : PrimeValue := ⟨701593, pr701593⟩
private theorem pr701653 : PrimeCertificate 701653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv8353]) (by decide +kernel)
def pv701653 : PrimeValue := ⟨701653, pr701653⟩
private theorem pr701699 : PrimeCertificate 701699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv97,pv3617]) (by decide +kernel)
def pv701699 : PrimeValue := ⟨701699, pr701699⟩
private theorem pr701903 : PrimeCertificate 701903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv31,pv11321]) (by decide +kernel)
def pv701903 : PrimeValue := ⟨701903, pr701903⟩
private theorem pr701951 : PrimeCertificate 701951 :=
  certifyPrime (q := pv31) (ls := [pv2,pv5,pv101,pv139]) (by decide +kernel)
def pv701951 : PrimeValue := ⟨701951, pr701951⟩
private theorem pr701969 : PrimeCertificate 701969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv73,pv601]) (by decide +kernel)
def pv701969 : PrimeValue := ⟨701969, pr701969⟩
private theorem pr702067 : PrimeCertificate 702067 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv6883]) (by decide +kernel)
def pv702067 : PrimeValue := ⟨702067, pr702067⟩
private theorem pr702199 : PrimeCertificate 702199 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv5573]) (by decide +kernel)
def pv702199 : PrimeValue := ⟨702199, pr702199⟩
private theorem pr702239 : PrimeCertificate 702239 :=
  certifyPrime (q := pv13) (ls := [pv2,pv311,pv1129]) (by decide +kernel)
def pv702239 : PrimeValue := ⟨702239, pr702239⟩
private theorem pr702269 : PrimeCertificate 702269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv3583]) (by decide +kernel)
def pv702269 : PrimeValue := ⟨702269, pr702269⟩
private theorem pr702313 : PrimeCertificate 702313 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv2251]) (by decide +kernel)
def pv702313 : PrimeValue := ⟨702313, pr702313⟩
private theorem pr702337 : PrimeCertificate 702337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv59]) (by decide +kernel)
def pv702337 : PrimeValue := ⟨702337, pr702337⟩
private theorem pr702503 : PrimeCertificate 702503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv197,pv1783]) (by decide +kernel)
def pv702503 : PrimeValue := ⟨702503, pr702503⟩
private theorem pr702517 : PrimeCertificate 702517 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv58543]) (by decide +kernel)
def pv702517 : PrimeValue := ⟨702517, pr702517⟩
private theorem pr702623 : PrimeCertificate 702623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv351311]) (by decide +kernel)
def pv702623 : PrimeValue := ⟨702623, pr702623⟩
private theorem pr702671 : PrimeCertificate 702671 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv29,pv2423]) (by decide +kernel)
def pv702671 : PrimeValue := ⟨702671, pr702671⟩
private theorem pr702683 : PrimeCertificate 702683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv351341]) (by decide +kernel)
def pv702683 : PrimeValue := ⟨702683, pr702683⟩
private theorem pr702701 : PrimeCertificate 702701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7027]) (by decide +kernel)
def pv702701 : PrimeValue := ⟨702701, pr702701⟩
private theorem pr702817 : PrimeCertificate 702817 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7321]) (by decide +kernel)
def pv702817 : PrimeValue := ⟨702817, pr702817⟩
private theorem pr702893 : PrimeCertificate 702893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv175723]) (by decide +kernel)
def pv702893 : PrimeValue := ⟨702893, pr702893⟩
private theorem pr703123 : PrimeCertificate 703123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv16741]) (by decide +kernel)
def pv703123 : PrimeValue := ⟨703123, pr703123⟩
private theorem pr703193 : PrimeCertificate 703193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv29,pv433]) (by decide +kernel)
def pv703193 : PrimeValue := ⟨703193, pr703193⟩
private theorem pr703229 : PrimeCertificate 703229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv487]) (by decide +kernel)
def pv703229 : PrimeValue := ⟨703229, pr703229⟩
private theorem pr703327 : PrimeCertificate 703327 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv13,pv71,pv127]) (by decide +kernel)
def pv703327 : PrimeValue := ⟨703327, pr703327⟩
private theorem pr703463 : PrimeCertificate 703463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv351731]) (by decide +kernel)
def pv703463 : PrimeValue := ⟨703463, pr703463⟩
private theorem pr703657 : PrimeCertificate 703657 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29,pv337]) (by decide +kernel)
def pv703657 : PrimeValue := ⟨703657, pr703657⟩
private theorem pr703691 : PrimeCertificate 703691 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv5413]) (by decide +kernel)
def pv703691 : PrimeValue := ⟨703691, pr703691⟩
private theorem pr703733 : PrimeCertificate 703733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv79,pv131]) (by decide +kernel)
def pv703733 : PrimeValue := ⟨703733, pr703733⟩
private theorem pr703789 : PrimeCertificate 703789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv223,pv263]) (by decide +kernel)
def pv703789 : PrimeValue := ⟨703789, pr703789⟩
private theorem pr703873 : PrimeCertificate 703873 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv47]) (by decide +kernel)
def pv703873 : PrimeValue := ⟨703873, pr703873⟩
private theorem pr703903 : PrimeCertificate 703903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv67,pv103]) (by decide +kernel)
def pv703903 : PrimeValue := ⟨703903, pr703903⟩
private theorem pr704003 : PrimeCertificate 704003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv27077]) (by decide +kernel)
def pv704003 : PrimeValue := ⟨704003, pr704003⟩
private theorem pr704183 : PrimeCertificate 704183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv379,pv929]) (by decide +kernel)
def pv704183 : PrimeValue := ⟨704183, pr704183⟩
private theorem pr704269 : PrimeCertificate 704269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv6521]) (by decide +kernel)
def pv704269 : PrimeValue := ⟨704269, pr704269⟩
private theorem pr704299 : PrimeCertificate 704299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv41,pv409]) (by decide +kernel)
def pv704299 : PrimeValue := ⟨704299, pr704299⟩
private theorem pr704309 : PrimeCertificate 704309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv16007]) (by decide +kernel)
def pv704309 : PrimeValue := ⟨704309, pr704309⟩
private theorem pr704393 : PrimeCertificate 704393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv521]) (by decide +kernel)
def pv704393 : PrimeValue := ⟨704393, pr704393⟩
private theorem pr704419 : PrimeCertificate 704419 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv13,pv821]) (by decide +kernel)
def pv704419 : PrimeValue := ⟨704419, pr704419⟩
private theorem pr704449 : PrimeCertificate 704449 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv1223]) (by decide +kernel)
def pv704449 : PrimeValue := ⟨704449, pr704449⟩
private theorem pr704579 : PrimeCertificate 704579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv59,pv853]) (by decide +kernel)
def pv704579 : PrimeValue := ⟨704579, pr704579⟩
private theorem pr704603 : PrimeCertificate 704603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv352301]) (by decide +kernel)
def pv704603 : PrimeValue := ⟨704603, pr704603⟩
private theorem pr704617 : PrimeCertificate 704617 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv11,pv17,pv157]) (by decide +kernel)
def pv704617 : PrimeValue := ⟨704617, pr704617⟩
private theorem pr704663 : PrimeCertificate 704663 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv50333]) (by decide +kernel)
def pv704663 : PrimeValue := ⟨704663, pr704663⟩
private theorem pr704713 : PrimeCertificate 704713 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv29363]) (by decide +kernel)
def pv704713 : PrimeValue := ⟨704713, pr704713⟩
private theorem pr704719 : PrimeCertificate 704719 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv7,pv17,pv47]) (by decide +kernel)
def pv704719 : PrimeValue := ⟨704719, pr704719⟩
private theorem pr704771 : PrimeCertificate 704771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv43,pv149]) (by decide +kernel)
def pv704771 : PrimeValue := ⟨704771, pr704771⟩
private theorem pr704797 : PrimeCertificate 704797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv58733]) (by decide +kernel)
def pv704797 : PrimeValue := ⟨704797, pr704797⟩
private theorem pr704929 : PrimeCertificate 704929 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv1049]) (by decide +kernel)
def pv704929 : PrimeValue := ⟨704929, pr704929⟩
private theorem pr704983 : PrimeCertificate 704983 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv117497]) (by decide +kernel)
def pv704983 : PrimeValue := ⟨704983, pr704983⟩
private theorem pr704999 : PrimeCertificate 704999 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv37,pv1361]) (by decide +kernel)
def pv704999 : PrimeValue := ⟨704999, pr704999⟩
private theorem pr705011 : PrimeCertificate 705011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv70501]) (by decide +kernel)
def pv705011 : PrimeValue := ⟨705011, pr705011⟩
private theorem pr705119 : PrimeCertificate 705119 :=
  certifyPrime (q := pv7) (ls := [pv2,pv41,pv8599]) (by decide +kernel)
def pv705119 : PrimeValue := ⟨705119, pr705119⟩
private theorem pr705127 : PrimeCertificate 705127 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv31,pv223]) (by decide +kernel)
def pv705127 : PrimeValue := ⟨705127, pr705127⟩
private theorem pr705277 : PrimeCertificate 705277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv13,pv137]) (by decide +kernel)
def pv705277 : PrimeValue := ⟨705277, pr705277⟩
private theorem pr705293 : PrimeCertificate 705293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv25189]) (by decide +kernel)
def pv705293 : PrimeValue := ⟨705293, pr705293⟩
private theorem pr705307 : PrimeCertificate 705307 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv2399]) (by decide +kernel)
def pv705307 : PrimeValue := ⟨705307, pr705307⟩
private theorem pr705461 : PrimeCertificate 705461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv5039]) (by decide +kernel)
def pv705461 : PrimeValue := ⟨705461, pr705461⟩
private theorem pr705499 : PrimeCertificate 705499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv3793]) (by decide +kernel)
def pv705499 : PrimeValue := ⟨705499, pr705499⟩
private theorem pr705521 : PrimeCertificate 705521 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv8819]) (by decide +kernel)
def pv705521 : PrimeValue := ⟨705521, pr705521⟩
private theorem pr705713 : PrimeCertificate 705713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv6301]) (by decide +kernel)
def pv705713 : PrimeValue := ⟨705713, pr705713⟩
private theorem pr705763 : PrimeCertificate 705763 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv39209]) (by decide +kernel)
def pv705763 : PrimeValue := ⟨705763, pr705763⟩
private theorem pr705779 : PrimeCertificate 705779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv67,pv229]) (by decide +kernel)
def pv705779 : PrimeValue := ⟨705779, pr705779⟩
private theorem pr705833 : PrimeCertificate 705833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv83,pv1063]) (by decide +kernel)
def pv705833 : PrimeValue := ⟨705833, pr705833⟩
private theorem pr705863 : PrimeCertificate 705863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv352931]) (by decide +kernel)
def pv705863 : PrimeValue := ⟨705863, pr705863⟩
private theorem pr705937 : PrimeCertificate 705937 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv191]) (by decide +kernel)
def pv705937 : PrimeValue := ⟨705937, pr705937⟩
private theorem pr705967 : PrimeCertificate 705967 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv97,pv1213]) (by decide +kernel)
def pv705967 : PrimeValue := ⟨705967, pr705967⟩
private theorem pr705989 : PrimeCertificate 705989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv176497]) (by decide +kernel)
def pv705989 : PrimeValue := ⟨705989, pr705989⟩
private theorem pr706109 : PrimeCertificate 706109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv37,pv367]) (by decide +kernel)
def pv706109 : PrimeValue := ⟨706109, pr706109⟩
private theorem pr706159 : PrimeCertificate 706159 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1453]) (by decide +kernel)
def pv706159 : PrimeValue := ⟨706159, pr706159⟩
private theorem pr706183 : PrimeCertificate 706183 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37,pv3181]) (by decide +kernel)
def pv706183 : PrimeValue := ⟨706183, pr706183⟩
private theorem pr706213 : PrimeCertificate 706213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv503]) (by decide +kernel)
def pv706213 : PrimeValue := ⟨706213, pr706213⟩
private theorem pr706301 : PrimeCertificate 706301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv1009]) (by decide +kernel)
def pv706301 : PrimeValue := ⟨706301, pr706301⟩
private theorem pr706357 : PrimeCertificate 706357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv2803]) (by decide +kernel)
def pv706357 : PrimeValue := ⟨706357, pr706357⟩
private theorem pr706369 : PrimeCertificate 706369 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv283]) (by decide +kernel)
def pv706369 : PrimeValue := ⟨706369, pr706369⟩
private theorem pr706603 : PrimeCertificate 706603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv9059]) (by decide +kernel)
def pv706603 : PrimeValue := ⟨706603, pr706603⟩
private theorem pr706729 : PrimeCertificate 706729 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv11,pv2677]) (by decide +kernel)
def pv706729 : PrimeValue := ⟨706729, pr706729⟩
private theorem pr706763 : PrimeCertificate 706763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv19,pv2657]) (by decide +kernel)
def pv706763 : PrimeValue := ⟨706763, pr706763⟩
private theorem pr706913 : PrimeCertificate 706913 :=
  certifyPrime (q := pv3) (ls := [pv2,pv22091]) (by decide +kernel)
def pv706913 : PrimeValue := ⟨706913, pr706913⟩
private theorem pr707153 : PrimeCertificate 707153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv193,pv229]) (by decide +kernel)
def pv707153 : PrimeValue := ⟨707153, pr707153⟩
private theorem pr707159 : PrimeCertificate 707159 :=
  certifyPrime (q := pv17) (ls := [pv2,pv23,pv15373]) (by decide +kernel)
def pv707159 : PrimeValue := ⟨707159, pr707159⟩
private theorem pr707293 : PrimeCertificate 707293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv59]) (by decide +kernel)
def pv707293 : PrimeValue := ⟨707293, pr707293⟩
private theorem pr707653 : PrimeCertificate 707653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv1787]) (by decide +kernel)
def pv707653 : PrimeValue := ⟨707653, pr707653⟩
private theorem pr707669 : PrimeCertificate 707669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv31,pv439]) (by decide +kernel)
def pv707669 : PrimeValue := ⟨707669, pr707669⟩
private theorem pr707753 : PrimeCertificate 707753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv88469]) (by decide +kernel)
def pv707753 : PrimeValue := ⟨707753, pr707753⟩
private theorem pr707767 : PrimeCertificate 707767 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv179,pv659]) (by decide +kernel)
def pv707767 : PrimeValue := ⟨707767, pr707767⟩
private theorem pr707797 : PrimeCertificate 707797 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv19661]) (by decide +kernel)
def pv707797 : PrimeValue := ⟨707797, pr707797⟩
private theorem pr707857 : PrimeCertificate 707857 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv14747]) (by decide +kernel)
def pv707857 : PrimeValue := ⟨707857, pr707857⟩
private theorem pr708023 : PrimeCertificate 708023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv103,pv491]) (by decide +kernel)
def pv708023 : PrimeValue := ⟨708023, pr708023⟩
private theorem pr708229 : PrimeCertificate 708229 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv103,pv191]) (by decide +kernel)
def pv708229 : PrimeValue := ⟨708229, pr708229⟩
private theorem pr708283 : PrimeCertificate 708283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv109]) (by decide +kernel)
def pv708283 : PrimeValue := ⟨708283, pr708283⟩
private theorem pr708293 : PrimeCertificate 708293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv53,pv257]) (by decide +kernel)
def pv708293 : PrimeValue := ⟨708293, pr708293⟩
private theorem pr708403 : PrimeCertificate 708403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv3191]) (by decide +kernel)
def pv708403 : PrimeValue := ⟨708403, pr708403⟩
private theorem pr708493 : PrimeCertificate 708493 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv23,pv151]) (by decide +kernel)
def pv708493 : PrimeValue := ⟨708493, pr708493⟩
private theorem pr708703 : PrimeCertificate 708703 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv4073]) (by decide +kernel)
def pv708703 : PrimeValue := ⟨708703, pr708703⟩
private theorem pr708823 : PrimeCertificate 708823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv53,pv743]) (by decide +kernel)
def pv708823 : PrimeValue := ⟨708823, pr708823⟩
private theorem pr708839 : PrimeCertificate 708839 :=
  certifyPrime (q := pv17) (ls := [pv2,pv13,pv137,pv199]) (by decide +kernel)
def pv708839 : PrimeValue := ⟨708839, pr708839⟩
private theorem pr708913 : PrimeCertificate 708913 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv547]) (by decide +kernel)
def pv708913 : PrimeValue := ⟨708913, pr708913⟩
private theorem pr708989 : PrimeCertificate 708989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv25321]) (by decide +kernel)
def pv708989 : PrimeValue := ⟨708989, pr708989⟩
private theorem pr709211 : PrimeCertificate 709211 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv70921]) (by decide +kernel)
def pv709211 : PrimeValue := ⟨709211, pr709211⟩
private theorem pr709237 : PrimeCertificate 709237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv199]) (by decide +kernel)
def pv709237 : PrimeValue := ⟨709237, pr709237⟩
private theorem pr709283 : PrimeCertificate 709283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv29,pv1747]) (by decide +kernel)
def pv709283 : PrimeValue := ⟨709283, pr709283⟩
private theorem pr709433 : PrimeCertificate 709433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv71,pv1249]) (by decide +kernel)
def pv709433 : PrimeValue := ⟨709433, pr709433⟩
private theorem pr709537 : PrimeCertificate 709537 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv389]) (by decide +kernel)
def pv709537 : PrimeValue := ⟨709537, pr709537⟩
private theorem pr709589 : PrimeCertificate 709589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv16127]) (by decide +kernel)
def pv709589 : PrimeValue := ⟨709589, pr709589⟩
private theorem pr709679 : PrimeCertificate 709679 :=
  certifyPrime (q := pv11) (ls := [pv2,pv354839]) (by decide +kernel)
def pv709679 : PrimeValue := ⟨709679, pr709679⟩
private theorem pr709729 : PrimeCertificate 709729 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7393]) (by decide +kernel)
def pv709729 : PrimeValue := ⟨709729, pr709729⟩
private theorem pr709913 : PrimeCertificate 709913 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv1811]) (by decide +kernel)
def pv709913 : PrimeValue := ⟨709913, pr709913⟩
private theorem pr709963 : PrimeCertificate 709963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv31,pv347]) (by decide +kernel)
def pv709963 : PrimeValue := ⟨709963, pr709963⟩
private theorem pr710023 : PrimeCertificate 710023 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv6961]) (by decide +kernel)
def pv710023 : PrimeValue := ⟨710023, pr710023⟩
private theorem pr710389 : PrimeCertificate 710389 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv2819]) (by decide +kernel)
def pv710389 : PrimeValue := ⟨710389, pr710389⟩
private theorem pr710441 : PrimeCertificate 710441 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv17761]) (by decide +kernel)
def pv710441 : PrimeValue := ⟨710441, pr710441⟩
private theorem pr710459 : PrimeCertificate 710459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv31,pv1637]) (by decide +kernel)
def pv710459 : PrimeValue := ⟨710459, pr710459⟩
private theorem pr710473 : PrimeCertificate 710473 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv4229]) (by decide +kernel)
def pv710473 : PrimeValue := ⟨710473, pr710473⟩
private theorem pr710483 : PrimeCertificate 710483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv137,pv2593]) (by decide +kernel)
def pv710483 : PrimeValue := ⟨710483, pr710483⟩
private theorem pr710513 : PrimeCertificate 710513 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv367]) (by decide +kernel)
def pv710513 : PrimeValue := ⟨710513, pr710513⟩
private theorem pr710519 : PrimeCertificate 710519 :=
  certifyPrime (q := pv23) (ls := [pv2,pv53,pv6703]) (by decide +kernel)
def pv710519 : PrimeValue := ⟨710519, pr710519⟩
private theorem pr710599 : PrimeCertificate 710599 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv2417]) (by decide +kernel)
def pv710599 : PrimeValue := ⟨710599, pr710599⟩
private theorem pr710621 : PrimeCertificate 710621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv35531]) (by decide +kernel)
def pv710621 : PrimeValue := ⟨710621, pr710621⟩
private theorem pr710683 : PrimeCertificate 710683 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv16921]) (by decide +kernel)
def pv710683 : PrimeValue := ⟨710683, pr710683⟩
private theorem pr710813 : PrimeCertificate 710813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv83,pv2141]) (by decide +kernel)
def pv710813 : PrimeValue := ⟨710813, pr710813⟩
private theorem pr710873 : PrimeCertificate 710873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv5227]) (by decide +kernel)
def pv710873 : PrimeValue := ⟨710873, pr710873⟩
private theorem pr710887 : PrimeCertificate 710887 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv10771]) (by decide +kernel)
def pv710887 : PrimeValue := ⟨710887, pr710887⟩
private theorem pr710929 : PrimeCertificate 710929 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv4937]) (by decide +kernel)
def pv710929 : PrimeValue := ⟨710929, pr710929⟩
private theorem pr710933 : PrimeCertificate 710933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89,pv1997]) (by decide +kernel)
def pv710933 : PrimeValue := ⟨710933, pr710933⟩
private theorem pr710959 : PrimeCertificate 710959 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv118493]) (by decide +kernel)
def pv710959 : PrimeValue := ⟨710959, pr710959⟩
private theorem pr711049 : PrimeCertificate 711049 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv43,pv53]) (by decide +kernel)
def pv711049 : PrimeValue := ⟨711049, pr711049⟩
private theorem pr711143 : PrimeCertificate 711143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv355571]) (by decide +kernel)
def pv711143 : PrimeValue := ⟨711143, pr711143⟩
private theorem pr711209 : PrimeCertificate 711209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv4679]) (by decide +kernel)
def pv711209 : PrimeValue := ⟨711209, pr711209⟩
private theorem pr711299 : PrimeCertificate 711299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv23,pv47]) (by decide +kernel)
def pv711299 : PrimeValue := ⟨711299, pr711299⟩
private theorem pr711409 : PrimeCertificate 711409 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv14821]) (by decide +kernel)
def pv711409 : PrimeValue := ⟨711409, pr711409⟩
private theorem pr711463 : PrimeCertificate 711463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv283,pv419]) (by decide +kernel)
def pv711463 : PrimeValue := ⟨711463, pr711463⟩
private theorem pr711563 : PrimeCertificate 711563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71,pv5011]) (by decide +kernel)
def pv711563 : PrimeValue := ⟨711563, pr711563⟩
private theorem pr711629 : PrimeCertificate 711629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv177907]) (by decide +kernel)
def pv711629 : PrimeValue := ⟨711629, pr711629⟩
private theorem pr711653 : PrimeCertificate 711653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv177913]) (by decide +kernel)
def pv711653 : PrimeValue := ⟨711653, pr711653⟩
private theorem pr711679 : PrimeCertificate 711679 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv11,pv41,pv263]) (by decide +kernel)
def pv711679 : PrimeValue := ⟨711679, pr711679⟩
private theorem pr711701 : PrimeCertificate 711701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv647]) (by decide +kernel)
def pv711701 : PrimeValue := ⟨711701, pr711701⟩
private theorem pr711731 : PrimeCertificate 711731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv103,pv691]) (by decide +kernel)
def pv711731 : PrimeValue := ⟨711731, pr711731⟩
private theorem pr711817 : PrimeCertificate 711817 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv19,pv223]) (by decide +kernel)
def pv711817 : PrimeValue := ⟨711817, pr711817⟩
private theorem pr711847 : PrimeCertificate 711847 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv71,pv557]) (by decide +kernel)
def pv711847 : PrimeValue := ⟨711847, pr711847⟩
private theorem pr711937 : PrimeCertificate 711937 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv103]) (by decide +kernel)
def pv711937 : PrimeValue := ⟨711937, pr711937⟩
private theorem pr711973 : PrimeCertificate 711973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19777]) (by decide +kernel)
def pv711973 : PrimeValue := ⟨711973, pr711973⟩
private theorem pr711983 : PrimeCertificate 711983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv317,pv1123]) (by decide +kernel)
def pv711983 : PrimeValue := ⟨711983, pr711983⟩
private theorem pr712199 : PrimeCertificate 712199 :=
  certifyPrime (q := pv11) (ls := [pv2,pv17,pv20947]) (by decide +kernel)
def pv712199 : PrimeValue := ⟨712199, pr712199⟩
private theorem pr712237 : PrimeCertificate 712237 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv61,pv139]) (by decide +kernel)
def pv712237 : PrimeValue := ⟨712237, pr712237⟩
private theorem pr712301 : PrimeCertificate 712301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv419]) (by decide +kernel)
def pv712301 : PrimeValue := ⟨712301, pr712301⟩
private theorem pr712417 : PrimeCertificate 712417 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv41,pv181]) (by decide +kernel)
def pv712417 : PrimeValue := ⟨712417, pr712417⟩
private theorem pr712483 : PrimeCertificate 712483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv118747]) (by decide +kernel)
def pv712483 : PrimeValue := ⟨712483, pr712483⟩
private theorem pr712693 : PrimeCertificate 712693 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv6599]) (by decide +kernel)
def pv712693 : PrimeValue := ⟨712693, pr712693⟩
private theorem pr713021 : PrimeCertificate 713021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv463]) (by decide +kernel)
def pv713021 : PrimeValue := ⟨713021, pr713021⟩
private theorem pr713077 : PrimeCertificate 713077 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv653]) (by decide +kernel)
def pv713077 : PrimeValue := ⟨713077, pr713077⟩
private theorem pr713107 : PrimeCertificate 713107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv173,pv229]) (by decide +kernel)
def pv713107 : PrimeValue := ⟨713107, pr713107⟩
private theorem pr713171 : PrimeCertificate 713171 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv71317]) (by decide +kernel)
def pv713171 : PrimeValue := ⟨713171, pr713171⟩
private theorem pr713183 : PrimeCertificate 713183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv356591]) (by decide +kernel)
def pv713183 : PrimeValue := ⟨713183, pr713183⟩
private theorem pr713189 : PrimeCertificate 713189 :=
  certifyPrime (q := pv17) (ls := [pv2,pv7,pv25471]) (by decide +kernel)
def pv713189 : PrimeValue := ⟨713189, pr713189⟩
private theorem pr713309 : PrimeCertificate 713309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv178327]) (by decide +kernel)
def pv713309 : PrimeValue := ⟨713309, pr713309⟩
private theorem pr713351 : PrimeCertificate 713351 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv1297]) (by decide +kernel)
def pv713351 : PrimeValue := ⟨713351, pr713351⟩
private theorem pr713353 : PrimeCertificate 713353 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29723]) (by decide +kernel)
def pv713353 : PrimeValue := ⟨713353, pr713353⟩
private theorem pr713467 : PrimeCertificate 713467 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13,pv3049]) (by decide +kernel)
def pv713467 : PrimeValue := ⟨713467, pr713467⟩
private theorem pr713497 : PrimeCertificate 713497 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv31,pv137]) (by decide +kernel)
def pv713497 : PrimeValue := ⟨713497, pr713497⟩
private theorem pr713509 : PrimeCertificate 713509 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv37,pv1607]) (by decide +kernel)
def pv713509 : PrimeValue := ⟨713509, pr713509⟩
private theorem pr713563 : PrimeCertificate 713563 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv118927]) (by decide +kernel)
def pv713563 : PrimeValue := ⟨713563, pr713563⟩
private theorem pr713827 : PrimeCertificate 713827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13219]) (by decide +kernel)
def pv713827 : PrimeValue := ⟨713827, pr713827⟩
private theorem pr713831 : PrimeCertificate 713831 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv13,pv17,pv19]) (by decide +kernel)
def pv713831 : PrimeValue := ⟨713831, pr713831⟩
private theorem pr713873 : PrimeCertificate 713873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv44617]) (by decide +kernel)
def pv713873 : PrimeValue := ⟨713873, pr713873⟩
private theorem pr713939 : PrimeCertificate 713939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv356969]) (by decide +kernel)
def pv713939 : PrimeValue := ⟨713939, pr713939⟩
private theorem pr713981 : PrimeCertificate 713981 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv29,pv1231]) (by decide +kernel)
def pv713981 : PrimeValue := ⟨713981, pr713981⟩
private theorem pr714037 : PrimeCertificate 714037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv157,pv379]) (by decide +kernel)
def pv714037 : PrimeValue := ⟨714037, pr714037⟩
private theorem pr714163 : PrimeCertificate 714163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv119027]) (by decide +kernel)
def pv714163 : PrimeValue := ⟨714163, pr714163⟩
private theorem pr714169 : PrimeCertificate 714169 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv7,pv13,pv109]) (by decide +kernel)
def pv714169 : PrimeValue := ⟨714169, pr714169⟩
private theorem pr714349 : PrimeCertificate 714349 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv19843]) (by decide +kernel)
def pv714349 : PrimeValue := ⟨714349, pr714349⟩
private theorem pr714443 : PrimeCertificate 714443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv21013]) (by decide +kernel)
def pv714443 : PrimeValue := ⟨714443, pr714443⟩
private theorem pr714487 : PrimeCertificate 714487 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv193,pv617]) (by decide +kernel)
def pv714487 : PrimeValue := ⟨714487, pr714487⟩
private theorem pr714577 : PrimeCertificate 714577 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv14887]) (by decide +kernel)
def pv714577 : PrimeValue := ⟨714577, pr714577⟩
private theorem pr714809 : PrimeCertificate 714809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv199,pv449]) (by decide +kernel)
def pv714809 : PrimeValue := ⟨714809, pr714809⟩
private theorem pr714853 : PrimeCertificate 714853 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv6619]) (by decide +kernel)
def pv714853 : PrimeValue := ⟨714853, pr714853⟩
private theorem pr714881 : PrimeCertificate 714881 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv1117]) (by decide +kernel)
def pv714881 : PrimeValue := ⟨714881, pr714881⟩
private theorem pr714919 : PrimeCertificate 714919 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv43,pv163]) (by decide +kernel)
def pv714919 : PrimeValue := ⟨714919, pr714919⟩
private theorem pr714971 : PrimeCertificate 714971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv53,pv71]) (by decide +kernel)
def pv714971 : PrimeValue := ⟨714971, pr714971⟩
private theorem pr715031 : PrimeCertificate 715031 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv71503]) (by decide +kernel)
def pv715031 : PrimeValue := ⟨715031, pr715031⟩
private theorem pr715123 : PrimeCertificate 715123 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv19,pv41]) (by decide +kernel)
def pv715123 : PrimeValue := ⟨715123, pr715123⟩
private theorem pr715189 : PrimeCertificate 715189 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv107,pv557]) (by decide +kernel)
def pv715189 : PrimeValue := ⟨715189, pr715189⟩
private theorem pr715243 : PrimeCertificate 715243 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv10837]) (by decide +kernel)
def pv715243 : PrimeValue := ⟨715243, pr715243⟩
private theorem pr715301 : PrimeCertificate 715301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv311]) (by decide +kernel)
def pv715301 : PrimeValue := ⟨715301, pr715301⟩
private theorem pr715303 : PrimeCertificate 715303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv811]) (by decide +kernel)
def pv715303 : PrimeValue := ⟨715303, pr715303⟩
private theorem pr715417 : PrimeCertificate 715417 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv2293]) (by decide +kernel)
def pv715417 : PrimeValue := ⟨715417, pr715417⟩
private theorem pr715439 : PrimeCertificate 715439 :=
  certifyPrime (q := pv17) (ls := [pv2,pv23,pv103,pv151]) (by decide +kernel)
def pv715439 : PrimeValue := ⟨715439, pr715439⟩
private theorem pr715523 : PrimeCertificate 715523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv131,pv2731]) (by decide +kernel)
def pv715523 : PrimeValue := ⟨715523, pr715523⟩
private theorem pr715873 : PrimeCertificate 715873 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7457]) (by decide +kernel)
def pv715873 : PrimeValue := ⟨715873, pr715873⟩
private theorem pr715879 : PrimeCertificate 715879 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv491]) (by decide +kernel)
def pv715879 : PrimeValue := ⟨715879, pr715879⟩
private theorem pr715889 : PrimeCertificate 715889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv101,pv443]) (by decide +kernel)
def pv715889 : PrimeValue := ⟨715889, pr715889⟩
private theorem pr715961 : PrimeCertificate 715961 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv7,pv2557]) (by decide +kernel)
def pv715961 : PrimeValue := ⟨715961, pr715961⟩
private theorem pr715963 : PrimeCertificate 715963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv67,pv137]) (by decide +kernel)
def pv715963 : PrimeValue := ⟨715963, pr715963⟩
private theorem pr715969 : PrimeCertificate 715969 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv113]) (by decide +kernel)
def pv715969 : PrimeValue := ⟨715969, pr715969⟩
private theorem pr716279 : PrimeCertificate 716279 :=
  certifyPrime (q := pv7) (ls := [pv2,pv17,pv21067]) (by decide +kernel)
def pv716279 : PrimeValue := ⟨716279, pr716279⟩
private theorem pr716291 : PrimeCertificate 716291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv83,pv863]) (by decide +kernel)
def pv716291 : PrimeValue := ⟨716291, pr716291⟩
private theorem pr716351 : PrimeCertificate 716351 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv14327]) (by decide +kernel)
def pv716351 : PrimeValue := ⟨716351, pr716351⟩
private theorem pr716389 : PrimeCertificate 716389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv59699]) (by decide +kernel)
def pv716389 : PrimeValue := ⟨716389, pr716389⟩
private theorem pr716399 : PrimeCertificate 716399 :=
  certifyPrime (q := pv13) (ls := [pv2,pv181,pv1979]) (by decide +kernel)
def pv716399 : PrimeValue := ⟨716399, pr716399⟩
private theorem pr716479 : PrimeCertificate 716479 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv2437]) (by decide +kernel)
def pv716479 : PrimeValue := ⟨716479, pr716479⟩
private theorem pr716857 : PrimeCertificate 716857 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv17,pv251]) (by decide +kernel)
def pv716857 : PrimeValue := ⟨716857, pr716857⟩
private theorem pr716861 : PrimeCertificate 716861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv73,pv491]) (by decide +kernel)
def pv716861 : PrimeValue := ⟨716861, pr716861⟩
private theorem pr716899 : PrimeCertificate 716899 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv101]) (by decide +kernel)
def pv716899 : PrimeValue := ⟨716899, pr716899⟩
private theorem pr716951 : PrimeCertificate 716951 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv1103]) (by decide +kernel)
def pv716951 : PrimeValue := ⟨716951, pr716951⟩
private theorem pr717011 : PrimeCertificate 717011 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv10243]) (by decide +kernel)
def pv717011 : PrimeValue := ⟨717011, pr717011⟩
private theorem pr717139 : PrimeCertificate 717139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv39841]) (by decide +kernel)
def pv717139 : PrimeValue := ⟨717139, pr717139⟩
private theorem pr717191 : PrimeCertificate 717191 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv71719]) (by decide +kernel)
def pv717191 : PrimeValue := ⟨717191, pr717191⟩
private theorem pr717413 : PrimeCertificate 717413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv97]) (by decide +kernel)
def pv717413 : PrimeValue := ⟨717413, pr717413⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
