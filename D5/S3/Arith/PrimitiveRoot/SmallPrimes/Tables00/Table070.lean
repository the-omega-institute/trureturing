/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table070
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table070.pv219749
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table007
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table009
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table015
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table041

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr219749 : PrimeCertificate 219749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv137,pv401]) (by decide +kernel)
def pv219749 : PrimeValue := ⟨219749, pr219749⟩
private theorem pr219761 : PrimeCertificate 219761 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv41,pv67]) (by decide +kernel)
def pv219761 : PrimeValue := ⟨219761, pr219761⟩
private theorem pr219763 : PrimeCertificate 219763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv421]) (by decide +kernel)
def pv219763 : PrimeValue := ⟨219763, pr219763⟩
private theorem pr219797 : PrimeCertificate 219797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv54949]) (by decide +kernel)
def pv219797 : PrimeValue := ⟨219797, pr219797⟩
private theorem pr219829 : PrimeCertificate 219829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv2617]) (by decide +kernel)
def pv219829 : PrimeValue := ⟨219829, pr219829⟩
private theorem pr219847 : PrimeCertificate 219847 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv3331]) (by decide +kernel)
def pv219847 : PrimeValue := ⟨219847, pr219847⟩
private theorem pr219851 : PrimeCertificate 219851 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv4397]) (by decide +kernel)
def pv219851 : PrimeValue := ⟨219851, pr219851⟩
private theorem pr219881 : PrimeCertificate 219881 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv23,pv239]) (by decide +kernel)
def pv219881 : PrimeValue := ⟨219881, pr219881⟩
private theorem pr219911 : PrimeCertificate 219911 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv21991]) (by decide +kernel)
def pv219911 : PrimeValue := ⟨219911, pr219911⟩
private theorem pr219917 : PrimeCertificate 219917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv54979]) (by decide +kernel)
def pv219917 : PrimeValue := ⟨219917, pr219917⟩
private theorem pr219931 : PrimeCertificate 219931 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7331]) (by decide +kernel)
def pv219931 : PrimeValue := ⟨219931, pr219931⟩
private theorem pr219937 : PrimeCertificate 219937 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29,pv79]) (by decide +kernel)
def pv219937 : PrimeValue := ⟨219937, pr219937⟩
private theorem pr219941 : PrimeCertificate 219941 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv1571]) (by decide +kernel)
def pv219941 : PrimeValue := ⟨219941, pr219941⟩
private theorem pr219953 : PrimeCertificate 219953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv59,pv233]) (by decide +kernel)
def pv219953 : PrimeValue := ⟨219953, pr219953⟩
private theorem pr219959 : PrimeCertificate 219959 :=
  certifyPrime (q := pv11) (ls := [pv2,pv71,pv1549]) (by decide +kernel)
def pv219959 : PrimeValue := ⟨219959, pr219959⟩
private theorem pr219979 : PrimeCertificate 219979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv101]) (by decide +kernel)
def pv219979 : PrimeValue := ⟨219979, pr219979⟩
private theorem pr219983 : PrimeCertificate 219983 :=
  certifyPrime (q := pv11) (ls := [pv2,pv7,pv19,pv827]) (by decide +kernel)
def pv219983 : PrimeValue := ⟨219983, pr219983⟩
private theorem pr220019 : PrimeCertificate 220019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv4783]) (by decide +kernel)
def pv220019 : PrimeValue := ⟨220019, pr220019⟩
private theorem pr220021 : PrimeCertificate 220021 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv19,pv193]) (by decide +kernel)
def pv220021 : PrimeValue := ⟨220021, pr220021⟩
private theorem pr220057 : PrimeCertificate 220057 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv53,pv173]) (by decide +kernel)
def pv220057 : PrimeValue := ⟨220057, pr220057⟩
private theorem pr220063 : PrimeCertificate 220063 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv36677]) (by decide +kernel)
def pv220063 : PrimeValue := ⟨220063, pr220063⟩
private theorem pr220147 : PrimeCertificate 220147 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv36691]) (by decide +kernel)
def pv220147 : PrimeValue := ⟨220147, pr220147⟩
private theorem pr220151 : PrimeCertificate 220151 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv17,pv37]) (by decide +kernel)
def pv220151 : PrimeValue := ⟨220151, pr220151⟩
private theorem pr220169 : PrimeCertificate 220169 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv29,pv73]) (by decide +kernel)
def pv220169 : PrimeValue := ⟨220169, pr220169⟩
private theorem pr220177 : PrimeCertificate 220177 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv139]) (by decide +kernel)
def pv220177 : PrimeValue := ⟨220177, pr220177⟩
private theorem pr220217 : PrimeCertificate 220217 :=
  certifyPrime (q := pv3) (ls := [pv2,pv27527]) (by decide +kernel)
def pv220217 : PrimeValue := ⟨220217, pr220217⟩
private theorem pr220243 : PrimeCertificate 220243 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv47,pv71]) (by decide +kernel)
def pv220243 : PrimeValue := ⟨220243, pr220243⟩
private theorem pr220279 : PrimeCertificate 220279 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv36713]) (by decide +kernel)
def pv220279 : PrimeValue := ⟨220279, pr220279⟩
private theorem pr220307 : PrimeCertificate 220307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59,pv1867]) (by decide +kernel)
def pv220307 : PrimeValue := ⟨220307, pr220307⟩
private theorem pr220333 : PrimeCertificate 220333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv43,pv61]) (by decide +kernel)
def pv220333 : PrimeValue := ⟨220333, pr220333⟩
private theorem pr220357 : PrimeCertificate 220357 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv6121]) (by decide +kernel)
def pv220357 : PrimeValue := ⟨220357, pr220357⟩
private theorem pr220361 : PrimeCertificate 220361 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv787]) (by decide +kernel)
def pv220361 : PrimeValue := ⟨220361, pr220361⟩
private theorem pr220369 : PrimeCertificate 220369 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv4591]) (by decide +kernel)
def pv220369 : PrimeValue := ⟨220369, pr220369⟩
private theorem pr220399 : PrimeCertificate 220399 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv109,pv337]) (by decide +kernel)
def pv220399 : PrimeValue := ⟨220399, pr220399⟩
private theorem pr220403 : PrimeCertificate 220403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv173]) (by decide +kernel)
def pv220403 : PrimeValue := ⟨220403, pr220403⟩
private theorem pr220411 : PrimeCertificate 220411 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv31,pv79]) (by decide +kernel)
def pv220411 : PrimeValue := ⟨220411, pr220411⟩
private theorem pr220421 : PrimeCertificate 220421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv103,pv107]) (by decide +kernel)
def pv220421 : PrimeValue := ⟨220421, pr220421⟩
private theorem pr220447 : PrimeCertificate 220447 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37,pv331]) (by decide +kernel)
def pv220447 : PrimeValue := ⟨220447, pr220447⟩
private theorem pr220469 : PrimeCertificate 220469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv55117]) (by decide +kernel)
def pv220469 : PrimeValue := ⟨220469, pr220469⟩
private theorem pr220511 : PrimeCertificate 220511 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv22051]) (by decide +kernel)
def pv220511 : PrimeValue := ⟨220511, pr220511⟩
private theorem pr220513 : PrimeCertificate 220513 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2297]) (by decide +kernel)
def pv220513 : PrimeValue := ⟨220513, pr220513⟩
private theorem pr220529 : PrimeCertificate 220529 :=
  certifyPrime (q := pv31) (ls := [pv2,pv7,pv11,pv179]) (by decide +kernel)
def pv220529 : PrimeValue := ⟨220529, pr220529⟩
private theorem pr220543 : PrimeCertificate 220543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv59,pv89]) (by decide +kernel)
def pv220543 : PrimeValue := ⟨220543, pr220543⟩
private theorem pr220553 : PrimeCertificate 220553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv1451]) (by decide +kernel)
def pv220553 : PrimeValue := ⟨220553, pr220553⟩
private theorem pr220589 : PrimeCertificate 220589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv55147]) (by decide +kernel)
def pv220589 : PrimeValue := ⟨220589, pr220589⟩
private theorem pr220663 : PrimeCertificate 220663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv23,pv41]) (by decide +kernel)
def pv220663 : PrimeValue := ⟨220663, pr220663⟩
private theorem pr220673 : PrimeCertificate 220673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv431]) (by decide +kernel)
def pv220673 : PrimeValue := ⟨220673, pr220673⟩
private theorem pr220681 : PrimeCertificate 220681 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv613]) (by decide +kernel)
def pv220681 : PrimeValue := ⟨220681, pr220681⟩
private theorem pr220687 : PrimeCertificate 220687 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv36781]) (by decide +kernel)
def pv220687 : PrimeValue := ⟨220687, pr220687⟩
private theorem pr220709 : PrimeCertificate 220709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv2399]) (by decide +kernel)
def pv220709 : PrimeValue := ⟨220709, pr220709⟩
private theorem pr220721 : PrimeCertificate 220721 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv31,pv89]) (by decide +kernel)
def pv220721 : PrimeValue := ⟨220721, pr220721⟩
private theorem pr220757 : PrimeCertificate 220757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv229,pv241]) (by decide +kernel)
def pv220757 : PrimeValue := ⟨220757, pr220757⟩
private theorem pr220771 : PrimeCertificate 220771 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv223]) (by decide +kernel)
def pv220771 : PrimeValue := ⟨220771, pr220771⟩
private theorem pr220783 : PrimeCertificate 220783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv1187]) (by decide +kernel)
def pv220783 : PrimeValue := ⟨220783, pr220783⟩
private theorem pr220793 : PrimeCertificate 220793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv13,pv193]) (by decide +kernel)
def pv220793 : PrimeValue := ⟨220793, pr220793⟩
private theorem pr220807 : PrimeCertificate 220807 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv47]) (by decide +kernel)
def pv220807 : PrimeValue := ⟨220807, pr220807⟩
private theorem pr220811 : PrimeCertificate 220811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv71,pv311]) (by decide +kernel)
def pv220811 : PrimeValue := ⟨220811, pr220811⟩
private theorem pr220841 : PrimeCertificate 220841 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv5521]) (by decide +kernel)
def pv220841 : PrimeValue := ⟨220841, pr220841⟩
private theorem pr220877 : PrimeCertificate 220877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv55219]) (by decide +kernel)
def pv220877 : PrimeValue := ⟨220877, pr220877⟩
private theorem pr220879 : PrimeCertificate 220879 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv1753]) (by decide +kernel)
def pv220879 : PrimeValue := ⟨220879, pr220879⟩
private theorem pr220889 : PrimeCertificate 220889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv27611]) (by decide +kernel)
def pv220889 : PrimeValue := ⟨220889, pr220889⟩
private theorem pr220903 : PrimeCertificate 220903 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv3347]) (by decide +kernel)
def pv220903 : PrimeValue := ⟨220903, pr220903⟩
private theorem pr220907 : PrimeCertificate 220907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv31,pv509]) (by decide +kernel)
def pv220907 : PrimeValue := ⟨220907, pr220907⟩
private theorem pr220919 : PrimeCertificate 220919 :=
  certifyPrime (q := pv19) (ls := [pv2,pv110459]) (by decide +kernel)
def pv220919 : PrimeValue := ⟨220919, pr220919⟩
private theorem pr220931 : PrimeCertificate 220931 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv22093]) (by decide +kernel)
def pv220931 : PrimeValue := ⟨220931, pr220931⟩
private theorem pr220933 : PrimeCertificate 220933 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv19]) (by decide +kernel)
def pv220933 : PrimeValue := ⟨220933, pr220933⟩
private theorem pr221059 : PrimeCertificate 221059 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv12281]) (by decide +kernel)
def pv221059 : PrimeValue := ⟨221059, pr221059⟩
private theorem pr221069 : PrimeCertificate 221069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv3251]) (by decide +kernel)
def pv221069 : PrimeValue := ⟨221069, pr221069⟩
private theorem pr221071 : PrimeCertificate 221071 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7369]) (by decide +kernel)
def pv221071 : PrimeValue := ⟨221071, pr221071⟩
private theorem pr221077 : PrimeCertificate 221077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv89]) (by decide +kernel)
def pv221077 : PrimeValue := ⟨221077, pr221077⟩
private theorem pr221083 : PrimeCertificate 221083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv36847]) (by decide +kernel)
def pv221083 : PrimeValue := ⟨221083, pr221083⟩
private theorem pr221101 : PrimeCertificate 221101 :=
  certifyPrime (q := pv71) (ls := [pv2,pv3,pv5,pv11,pv67]) (by decide +kernel)
def pv221101 : PrimeValue := ⟨221101, pr221101⟩
private theorem pr221159 : PrimeCertificate 221159 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv15797]) (by decide +kernel)
def pv221159 : PrimeValue := ⟨221159, pr221159⟩
private theorem pr221173 : PrimeCertificate 221173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv2633]) (by decide +kernel)
def pv221173 : PrimeValue := ⟨221173, pr221173⟩
private theorem pr221197 : PrimeCertificate 221197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv18433]) (by decide +kernel)
def pv221197 : PrimeValue := ⟨221197, pr221197⟩
private theorem pr221203 : PrimeCertificate 221203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv12289]) (by decide +kernel)
def pv221203 : PrimeValue := ⟨221203, pr221203⟩
private theorem pr221219 : PrimeCertificate 221219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv110609]) (by decide +kernel)
def pv221219 : PrimeValue := ⟨221219, pr221219⟩
private theorem pr221227 : PrimeCertificate 221227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv36871]) (by decide +kernel)
def pv221227 : PrimeValue := ⟨221227, pr221227⟩
private theorem pr221239 : PrimeCertificate 221239 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv241]) (by decide +kernel)
def pv221239 : PrimeValue := ⟨221239, pr221239⟩
private theorem pr221261 : PrimeCertificate 221261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv23,pv37]) (by decide +kernel)
def pv221261 : PrimeValue := ⟨221261, pr221261⟩
private theorem pr221303 : PrimeCertificate 221303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv110651]) (by decide +kernel)
def pv221303 : PrimeValue := ⟨221303, pr221303⟩
private theorem pr221317 : PrimeCertificate 221317 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv18443]) (by decide +kernel)
def pv221317 : PrimeValue := ⟨221317, pr221317⟩
private theorem pr221327 : PrimeCertificate 221327 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv15809]) (by decide +kernel)
def pv221327 : PrimeValue := ⟨221327, pr221327⟩
private theorem pr221399 : PrimeCertificate 221399 :=
  certifyPrime (q := pv19) (ls := [pv2,pv23,pv4813]) (by decide +kernel)
def pv221399 : PrimeValue := ⟨221399, pr221399⟩
private theorem pr221401 : PrimeCertificate 221401 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv41]) (by decide +kernel)
def pv221401 : PrimeValue := ⟨221401, pr221401⟩
private theorem pr221411 : PrimeCertificate 221411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv3163]) (by decide +kernel)
def pv221411 : PrimeValue := ⟨221411, pr221411⟩
private theorem pr221413 : PrimeCertificate 221413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv18451]) (by decide +kernel)
def pv221413 : PrimeValue := ⟨221413, pr221413⟩
private theorem pr221447 : PrimeCertificate 221447 :=
  certifyPrime (q := pv5) (ls := [pv2,pv263,pv421]) (by decide +kernel)
def pv221447 : PrimeValue := ⟨221447, pr221447⟩
private theorem pr221461 : PrimeCertificate 221461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv3691]) (by decide +kernel)
def pv221461 : PrimeValue := ⟨221461, pr221461⟩
private theorem pr221471 : PrimeCertificate 221471 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv22147]) (by decide +kernel)
def pv221471 : PrimeValue := ⟨221471, pr221471⟩
private theorem pr221477 : PrimeCertificate 221477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv3257]) (by decide +kernel)
def pv221477 : PrimeValue := ⟨221477, pr221477⟩
private theorem pr221489 : PrimeCertificate 221489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv109,pv127]) (by decide +kernel)
def pv221489 : PrimeValue := ⟨221489, pr221489⟩
private theorem pr221509 : PrimeCertificate 221509 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv293]) (by decide +kernel)
def pv221509 : PrimeValue := ⟨221509, pr221509⟩
private theorem pr221537 : PrimeCertificate 221537 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv23,pv43]) (by decide +kernel)
def pv221537 : PrimeValue := ⟨221537, pr221537⟩
private theorem pr221587 : PrimeCertificate 221587 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv36931]) (by decide +kernel)
def pv221587 : PrimeValue := ⟨221587, pr221587⟩
private theorem pr221603 : PrimeCertificate 221603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv179,pv619]) (by decide +kernel)
def pv221603 : PrimeValue := ⟨221603, pr221603⟩
private theorem pr221621 : PrimeCertificate 221621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv1583]) (by decide +kernel)
def pv221621 : PrimeValue := ⟨221621, pr221621⟩
private theorem pr221623 : PrimeCertificate 221623 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv43,pv859]) (by decide +kernel)
def pv221623 : PrimeValue := ⟨221623, pr221623⟩
private theorem pr221713 : PrimeCertificate 221713 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv149]) (by decide +kernel)
def pv221713 : PrimeValue := ⟨221713, pr221713⟩
private theorem pr221737 : PrimeCertificate 221737 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv9239]) (by decide +kernel)
def pv221737 : PrimeValue := ⟨221737, pr221737⟩
private theorem pr221747 : PrimeCertificate 221747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv47,pv337]) (by decide +kernel)
def pv221747 : PrimeValue := ⟨221747, pr221747⟩
private theorem pr221773 : PrimeCertificate 221773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv18481]) (by decide +kernel)
def pv221773 : PrimeValue := ⟨221773, pr221773⟩
private theorem pr221797 : PrimeCertificate 221797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61,pv101]) (by decide +kernel)
def pv221797 : PrimeValue := ⟨221797, pr221797⟩
private theorem pr221807 : PrimeCertificate 221807 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv19,pv449]) (by decide +kernel)
def pv221807 : PrimeValue := ⟨221807, pr221807⟩
private theorem pr221827 : PrimeCertificate 221827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv3361]) (by decide +kernel)
def pv221827 : PrimeValue := ⟨221827, pr221827⟩
private theorem pr221831 : PrimeCertificate 221831 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv3169]) (by decide +kernel)
def pv221831 : PrimeValue := ⟨221831, pr221831⟩
private theorem pr221849 : PrimeCertificate 221849 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv2521]) (by decide +kernel)
def pv221849 : PrimeValue := ⟨221849, pr221849⟩
private theorem pr221873 : PrimeCertificate 221873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv283]) (by decide +kernel)
def pv221873 : PrimeValue := ⟨221873, pr221873⟩
private theorem pr221891 : PrimeCertificate 221891 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv22189]) (by decide +kernel)
def pv221891 : PrimeValue := ⟨221891, pr221891⟩
private theorem pr221909 : PrimeCertificate 221909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv1913]) (by decide +kernel)
def pv221909 : PrimeValue := ⟨221909, pr221909⟩
private theorem pr221941 : PrimeCertificate 221941 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv137]) (by decide +kernel)
def pv221941 : PrimeValue := ⟨221941, pr221941⟩
private theorem pr221953 : PrimeCertificate 221953 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv17]) (by decide +kernel)
def pv221953 : PrimeValue := ⟨221953, pr221953⟩
private theorem pr221987 : PrimeCertificate 221987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv6529]) (by decide +kernel)
def pv221987 : PrimeValue := ⟨221987, pr221987⟩
private theorem pr221999 : PrimeCertificate 221999 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv101,pv157]) (by decide +kernel)
def pv221999 : PrimeValue := ⟨221999, pr221999⟩
private theorem pr222023 : PrimeCertificate 222023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv31,pv3581]) (by decide +kernel)
def pv222023 : PrimeValue := ⟨222023, pr222023⟩
private theorem pr222043 : PrimeCertificate 222043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv1609]) (by decide +kernel)
def pv222043 : PrimeValue := ⟨222043, pr222043⟩
private theorem pr222059 : PrimeCertificate 222059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv111029]) (by decide +kernel)
def pv222059 : PrimeValue := ⟨222059, pr222059⟩
private theorem pr222067 : PrimeCertificate 222067 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv73]) (by decide +kernel)
def pv222067 : PrimeValue := ⟨222067, pr222067⟩
private theorem pr222073 : PrimeCertificate 222073 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv487]) (by decide +kernel)
def pv222073 : PrimeValue := ⟨222073, pr222073⟩
private theorem pr222113 : PrimeCertificate 222113 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv631]) (by decide +kernel)
def pv222113 : PrimeValue := ⟨222113, pr222113⟩
private theorem pr222127 : PrimeCertificate 222127 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37021]) (by decide +kernel)
def pv222127 : PrimeValue := ⟨222127, pr222127⟩
private theorem pr222137 : PrimeCertificate 222137 :=
  certifyPrime (q := pv3) (ls := [pv2,pv27767]) (by decide +kernel)
def pv222137 : PrimeValue := ⟨222137, pr222137⟩
private theorem pr222151 : PrimeCertificate 222151 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv1481]) (by decide +kernel)
def pv222151 : PrimeValue := ⟨222151, pr222151⟩
private theorem pr222161 : PrimeCertificate 222161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv2777]) (by decide +kernel)
def pv222161 : PrimeValue := ⟨222161, pr222161⟩
private theorem pr222163 : PrimeCertificate 222163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61,pv607]) (by decide +kernel)
def pv222163 : PrimeValue := ⟨222163, pr222163⟩
private theorem pr222193 : PrimeCertificate 222193 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1543]) (by decide +kernel)
def pv222193 : PrimeValue := ⟨222193, pr222193⟩
private theorem pr222197 : PrimeCertificate 222197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv4273]) (by decide +kernel)
def pv222197 : PrimeValue := ⟨222197, pr222197⟩
private theorem pr222199 : PrimeCertificate 222199 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv1277]) (by decide +kernel)
def pv222199 : PrimeValue := ⟨222199, pr222199⟩
private theorem pr222247 : PrimeCertificate 222247 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv12347]) (by decide +kernel)
def pv222247 : PrimeValue := ⟨222247, pr222247⟩
private theorem pr222269 : PrimeCertificate 222269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv181,pv307]) (by decide +kernel)
def pv222269 : PrimeValue := ⟨222269, pr222269⟩
private theorem pr222293 : PrimeCertificate 222293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv17,pv467]) (by decide +kernel)
def pv222293 : PrimeValue := ⟨222293, pr222293⟩
private theorem pr222311 : PrimeCertificate 222311 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv43,pv47]) (by decide +kernel)
def pv222311 : PrimeValue := ⟨222311, pr222311⟩
private theorem pr222317 : PrimeCertificate 222317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv55579]) (by decide +kernel)
def pv222317 : PrimeValue := ⟨222317, pr222317⟩
private theorem pr222329 : PrimeCertificate 222329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv27791]) (by decide +kernel)
def pv222329 : PrimeValue := ⟨222329, pr222329⟩
private theorem pr222337 : PrimeCertificate 222337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv193]) (by decide +kernel)
def pv222337 : PrimeValue := ⟨222337, pr222337⟩
private theorem pr222347 : PrimeCertificate 222347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv107,pv1039]) (by decide +kernel)
def pv222347 : PrimeValue := ⟨222347, pr222347⟩
private theorem pr222361 : PrimeCertificate 222361 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv17,pv109]) (by decide +kernel)
def pv222361 : PrimeValue := ⟨222361, pr222361⟩
private theorem pr222367 : PrimeCertificate 222367 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37061]) (by decide +kernel)
def pv222367 : PrimeValue := ⟨222367, pr222367⟩
private theorem pr222389 : PrimeCertificate 222389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv1049]) (by decide +kernel)
def pv222389 : PrimeValue := ⟨222389, pr222389⟩
private theorem pr222403 : PrimeCertificate 222403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv101,pv367]) (by decide +kernel)
def pv222403 : PrimeValue := ⟨222403, pr222403⟩
private theorem pr222437 : PrimeCertificate 222437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv55609]) (by decide +kernel)
def pv222437 : PrimeValue := ⟨222437, pr222437⟩
private theorem pr222461 : PrimeCertificate 222461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv227]) (by decide +kernel)
def pv222461 : PrimeValue := ⟨222461, pr222461⟩
private theorem pr222493 : PrimeCertificate 222493 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv18541]) (by decide +kernel)
def pv222493 : PrimeValue := ⟨222493, pr222493⟩
private theorem pr222499 : PrimeCertificate 222499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv263]) (by decide +kernel)
def pv222499 : PrimeValue := ⟨222499, pr222499⟩
private theorem pr222511 : PrimeCertificate 222511 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7417]) (by decide +kernel)
def pv222511 : PrimeValue := ⟨222511, pr222511⟩
private theorem pr222527 : PrimeCertificate 222527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv111263]) (by decide +kernel)
def pv222527 : PrimeValue := ⟨222527, pr222527⟩
private theorem pr222533 : PrimeCertificate 222533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv55633]) (by decide +kernel)
def pv222533 : PrimeValue := ⟨222533, pr222533⟩
private theorem pr222553 : PrimeCertificate 222553 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv281]) (by decide +kernel)
def pv222553 : PrimeValue := ⟨222553, pr222553⟩
private theorem pr222557 : PrimeCertificate 222557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv55639]) (by decide +kernel)
def pv222557 : PrimeValue := ⟨222557, pr222557⟩
private theorem pr222613 : PrimeCertificate 222613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv1427]) (by decide +kernel)
def pv222613 : PrimeValue := ⟨222613, pr222613⟩
private theorem pr222643 : PrimeCertificate 222643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv19,pv31]) (by decide +kernel)
def pv222643 : PrimeValue := ⟨222643, pr222643⟩
private theorem pr222659 : PrimeCertificate 222659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv163,pv683]) (by decide +kernel)
def pv222659 : PrimeValue := ⟨222659, pr222659⟩
private theorem pr222679 : PrimeCertificate 222679 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv89,pv139]) (by decide +kernel)
def pv222679 : PrimeValue := ⟨222679, pr222679⟩
private theorem pr222707 : PrimeCertificate 222707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv53,pv191]) (by decide +kernel)
def pv222707 : PrimeValue := ⟨222707, pr222707⟩
private theorem pr222713 : PrimeCertificate 222713 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv41,pv97]) (by decide +kernel)
def pv222713 : PrimeValue := ⟨222713, pr222713⟩
private theorem pr222731 : PrimeCertificate 222731 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv22273]) (by decide +kernel)
def pv222731 : PrimeValue := ⟨222731, pr222731⟩
private theorem pr222773 : PrimeCertificate 222773 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv61,pv83]) (by decide +kernel)
def pv222773 : PrimeValue := ⟨222773, pr222773⟩
private theorem pr222787 : PrimeCertificate 222787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv12377]) (by decide +kernel)
def pv222787 : PrimeValue := ⟨222787, pr222787⟩
private theorem pr222791 : PrimeCertificate 222791 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv22279]) (by decide +kernel)
def pv222791 : PrimeValue := ⟨222791, pr222791⟩
private theorem pr222793 : PrimeCertificate 222793 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv9283]) (by decide +kernel)
def pv222793 : PrimeValue := ⟨222793, pr222793⟩
private theorem pr222823 : PrimeCertificate 222823 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv12379]) (by decide +kernel)
def pv222823 : PrimeValue := ⟨222823, pr222823⟩
private theorem pr222839 : PrimeCertificate 222839 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv11,pv1447]) (by decide +kernel)
def pv222839 : PrimeValue := ⟨222839, pr222839⟩
private theorem pr222841 : PrimeCertificate 222841 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv619]) (by decide +kernel)
def pv222841 : PrimeValue := ⟨222841, pr222841⟩
private theorem pr222857 : PrimeCertificate 222857 :=
  certifyPrime (q := pv3) (ls := [pv2,pv89,pv313]) (by decide +kernel)
def pv222857 : PrimeValue := ⟨222857, pr222857⟩
private theorem pr222863 : PrimeCertificate 222863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv111431]) (by decide +kernel)
def pv222863 : PrimeValue := ⟨222863, pr222863⟩
private theorem pr222877 : PrimeCertificate 222877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv151]) (by decide +kernel)
def pv222877 : PrimeValue := ⟨222877, pr222877⟩
private theorem pr222883 : PrimeCertificate 222883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv307]) (by decide +kernel)
def pv222883 : PrimeValue := ⟨222883, pr222883⟩
private theorem pr222913 : PrimeCertificate 222913 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv43]) (by decide +kernel)
def pv222913 : PrimeValue := ⟨222913, pr222913⟩
private theorem pr222919 : PrimeCertificate 222919 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv53,pv701]) (by decide +kernel)
def pv222919 : PrimeValue := ⟨222919, pr222919⟩
private theorem pr222941 : PrimeCertificate 222941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv71,pv157]) (by decide +kernel)
def pv222941 : PrimeValue := ⟨222941, pr222941⟩
private theorem pr222947 : PrimeCertificate 222947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv5867]) (by decide +kernel)
def pv222947 : PrimeValue := ⟨222947, pr222947⟩
private theorem pr222967 : PrimeCertificate 222967 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv4129]) (by decide +kernel)
def pv222967 : PrimeValue := ⟨222967, pr222967⟩
private theorem pr222979 : PrimeCertificate 222979 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv5309]) (by decide +kernel)
def pv222979 : PrimeValue := ⟨222979, pr222979⟩
private theorem pr223037 : PrimeCertificate 223037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv37,pv137]) (by decide +kernel)
def pv223037 : PrimeValue := ⟨223037, pr223037⟩
private theorem pr223049 : PrimeCertificate 223049 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv569]) (by decide +kernel)
def pv223049 : PrimeValue := ⟨223049, pr223049⟩
private theorem pr223051 : PrimeCertificate 223051 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv1487]) (by decide +kernel)
def pv223051 : PrimeValue := ⟨223051, pr223051⟩
private theorem pr223061 : PrimeCertificate 223061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv587]) (by decide +kernel)
def pv223061 : PrimeValue := ⟨223061, pr223061⟩
private theorem pr223063 : PrimeCertificate 223063 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv47,pv113]) (by decide +kernel)
def pv223063 : PrimeValue := ⟨223063, pr223063⟩
private theorem pr223087 : PrimeCertificate 223087 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv37181]) (by decide +kernel)
def pv223087 : PrimeValue := ⟨223087, pr223087⟩
private theorem pr223133 : PrimeCertificate 223133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv613]) (by decide +kernel)
def pv223133 : PrimeValue := ⟨223133, pr223133⟩
private theorem pr223151 : PrimeCertificate 223151 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv4463]) (by decide +kernel)
def pv223151 : PrimeValue := ⟨223151, pr223151⟩
private theorem pr223207 : PrimeCertificate 223207 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37201]) (by decide +kernel)
def pv223207 : PrimeValue := ⟨223207, pr223207⟩
private theorem pr223211 : PrimeCertificate 223211 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv17,pv101]) (by decide +kernel)
def pv223211 : PrimeValue := ⟨223211, pr223211⟩
private theorem pr223219 : PrimeCertificate 223219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv12401]) (by decide +kernel)
def pv223219 : PrimeValue := ⟨223219, pr223219⟩
private theorem pr223229 : PrimeCertificate 223229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv55807]) (by decide +kernel)
def pv223229 : PrimeValue := ⟨223229, pr223229⟩
private theorem pr223243 : PrimeCertificate 223243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv1283]) (by decide +kernel)
def pv223243 : PrimeValue := ⟨223243, pr223243⟩
private theorem pr223247 : PrimeCertificate 223247 :=
  certifyPrime (q := pv5) (ls := [pv2,pv111623]) (by decide +kernel)
def pv223247 : PrimeValue := ⟨223247, pr223247⟩
private theorem pr223253 : PrimeCertificate 223253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv55813]) (by decide +kernel)
def pv223253 : PrimeValue := ⟨223253, pr223253⟩
private theorem pr223273 : PrimeCertificate 223273 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv443]) (by decide +kernel)
def pv223273 : PrimeValue := ⟨223273, pr223273⟩
private theorem pr223277 : PrimeCertificate 223277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv55819]) (by decide +kernel)
def pv223277 : PrimeValue := ⟨223277, pr223277⟩
private theorem pr223291 : PrimeCertificate 223291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv827]) (by decide +kernel)
def pv223291 : PrimeValue := ⟨223291, pr223291⟩
private theorem pr223303 : PrimeCertificate 223303 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37217]) (by decide +kernel)
def pv223303 : PrimeValue := ⟨223303, pr223303⟩
private theorem pr223319 : PrimeCertificate 223319 :=
  certifyPrime (q := pv13) (ls := [pv2,pv111659]) (by decide +kernel)
def pv223319 : PrimeValue := ⟨223319, pr223319⟩
private theorem pr223331 : PrimeCertificate 223331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv971]) (by decide +kernel)
def pv223331 : PrimeValue := ⟨223331, pr223331⟩
private theorem pr223339 : PrimeCertificate 223339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37223]) (by decide +kernel)
def pv223339 : PrimeValue := ⟨223339, pr223339⟩
private theorem pr223367 : PrimeCertificate 223367 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv13,pv71]) (by decide +kernel)
def pv223367 : PrimeValue := ⟨223367, pr223367⟩
private theorem pr223403 : PrimeCertificate 223403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv5879]) (by decide +kernel)
def pv223403 : PrimeValue := ⟨223403, pr223403⟩
private theorem pr223441 : PrimeCertificate 223441 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv7,pv19]) (by decide +kernel)
def pv223441 : PrimeValue := ⟨223441, pr223441⟩
private theorem pr223463 : PrimeCertificate 223463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv111731]) (by decide +kernel)
def pv223463 : PrimeValue := ⟨223463, pr223463⟩
private theorem pr223493 : PrimeCertificate 223493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59,pv947]) (by decide +kernel)
def pv223493 : PrimeValue := ⟨223493, pr223493⟩
private theorem pr223543 : PrimeCertificate 223543 :=
  certifyPrime (q := pv59) (ls := [pv2,pv3,pv11,pv1129]) (by decide +kernel)
def pv223543 : PrimeValue := ⟨223543, pr223543⟩
private theorem pr223547 : PrimeCertificate 223547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv111773]) (by decide +kernel)
def pv223547 : PrimeValue := ⟨223547, pr223547⟩
private theorem pr223549 : PrimeCertificate 223549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv1433]) (by decide +kernel)
def pv223549 : PrimeValue := ⟨223549, pr223549⟩
private theorem pr223589 : PrimeCertificate 223589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv55897]) (by decide +kernel)
def pv223589 : PrimeValue := ⟨223589, pr223589⟩
private theorem pr223633 : PrimeCertificate 223633 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1553]) (by decide +kernel)
def pv223633 : PrimeValue := ⟨223633, pr223633⟩
private theorem pr223667 : PrimeCertificate 223667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv111833]) (by decide +kernel)
def pv223667 : PrimeValue := ⟨223667, pr223667⟩
private theorem pr223679 : PrimeCertificate 223679 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv13,pv1229]) (by decide +kernel)
def pv223679 : PrimeValue := ⟨223679, pr223679⟩
private theorem pr223681 : PrimeCertificate 223681 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv233]) (by decide +kernel)
def pv223681 : PrimeValue := ⟨223681, pr223681⟩
private theorem pr223711 : PrimeCertificate 223711 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7457]) (by decide +kernel)
def pv223711 : PrimeValue := ⟨223711, pr223711⟩
private theorem pr223753 : PrimeCertificate 223753 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv9323]) (by decide +kernel)
def pv223753 : PrimeValue := ⟨223753, pr223753⟩
private theorem pr223757 : PrimeCertificate 223757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv331]) (by decide +kernel)
def pv223757 : PrimeValue := ⟨223757, pr223757⟩
private theorem pr223781 : PrimeCertificate 223781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv67,pv167]) (by decide +kernel)
def pv223781 : PrimeValue := ⟨223781, pr223781⟩
private theorem pr223823 : PrimeCertificate 223823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv29,pv227]) (by decide +kernel)
def pv223823 : PrimeValue := ⟨223823, pr223823⟩
private theorem pr223829 : PrimeCertificate 223829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv5087]) (by decide +kernel)
def pv223829 : PrimeValue := ⟨223829, pr223829⟩
private theorem pr223831 : PrimeCertificate 223831 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv829]) (by decide +kernel)
def pv223831 : PrimeValue := ⟨223831, pr223831⟩
private theorem pr223841 : PrimeCertificate 223841 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1399]) (by decide +kernel)
def pv223841 : PrimeValue := ⟨223841, pr223841⟩
private theorem pr223843 : PrimeCertificate 223843 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37307]) (by decide +kernel)
def pv223843 : PrimeValue := ⟨223843, pr223843⟩
private theorem pr223849 : PrimeCertificate 223849 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv3109]) (by decide +kernel)
def pv223849 : PrimeValue := ⟨223849, pr223849⟩
private theorem pr223903 : PrimeCertificate 223903 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv1777]) (by decide +kernel)
def pv223903 : PrimeValue := ⟨223903, pr223903⟩
private theorem pr223919 : PrimeCertificate 223919 :=
  certifyPrime (q := pv11) (ls := [pv2,pv111959]) (by decide +kernel)
def pv223919 : PrimeValue := ⟨223919, pr223919⟩
private theorem pr223939 : PrimeCertificate 223939 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11,pv13,pv29]) (by decide +kernel)
def pv223939 : PrimeValue := ⟨223939, pr223939⟩
private theorem pr223963 : PrimeCertificate 223963 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv163,pv229]) (by decide +kernel)
def pv223963 : PrimeValue := ⟨223963, pr223963⟩
private theorem pr224011 : PrimeCertificate 224011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv131]) (by decide +kernel)
def pv224011 : PrimeValue := ⟨224011, pr224011⟩
private theorem pr224027 : PrimeCertificate 224027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv17,pv599]) (by decide +kernel)
def pv224027 : PrimeValue := ⟨224027, pr224027⟩
private theorem pr224033 : PrimeCertificate 224033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7001]) (by decide +kernel)
def pv224033 : PrimeValue := ⟨224033, pr224033⟩
private theorem pr224047 : PrimeCertificate 224047 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv461]) (by decide +kernel)
def pv224047 : PrimeValue := ⟨224047, pr224047⟩
private theorem pr224057 : PrimeCertificate 224057 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv4001]) (by decide +kernel)
def pv224057 : PrimeValue := ⟨224057, pr224057⟩
private theorem pr224069 : PrimeCertificate 224069 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv31,pv139]) (by decide +kernel)
def pv224069 : PrimeValue := ⟨224069, pr224069⟩
private theorem pr224101 : PrimeCertificate 224101 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv83]) (by decide +kernel)
def pv224101 : PrimeValue := ⟨224101, pr224101⟩
private theorem pr224113 : PrimeCertificate 224113 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv23,pv29]) (by decide +kernel)
def pv224113 : PrimeValue := ⟨224113, pr224113⟩
private theorem pr224129 : PrimeCertificate 224129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv103]) (by decide +kernel)
def pv224129 : PrimeValue := ⟨224129, pr224129⟩
private theorem pr224131 : PrimeCertificate 224131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv31,pv241]) (by decide +kernel)
def pv224131 : PrimeValue := ⟨224131, pr224131⟩
private theorem pr224171 : PrimeCertificate 224171 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv29,pv773]) (by decide +kernel)
def pv224171 : PrimeValue := ⟨224171, pr224171⟩
private theorem pr224177 : PrimeCertificate 224177 :=
  certifyPrime (q := pv3) (ls := [pv2,pv14011]) (by decide +kernel)
def pv224177 : PrimeValue := ⟨224177, pr224177⟩
private theorem pr224201 : PrimeCertificate 224201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv19,pv59]) (by decide +kernel)
def pv224201 : PrimeValue := ⟨224201, pr224201⟩
private theorem pr224209 : PrimeCertificate 224209 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv173]) (by decide +kernel)
def pv224209 : PrimeValue := ⟨224209, pr224209⟩
private theorem pr224221 : PrimeCertificate 224221 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv37,pv101]) (by decide +kernel)
def pv224221 : PrimeValue := ⟨224221, pr224221⟩
private theorem pr224251 : PrimeCertificate 224251 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv13,pv23]) (by decide +kernel)
def pv224251 : PrimeValue := ⟨224251, pr224251⟩
private theorem pr224267 : PrimeCertificate 224267 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv83,pv193]) (by decide +kernel)
def pv224267 : PrimeValue := ⟨224267, pr224267⟩
private theorem pr224299 : PrimeCertificate 224299 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv733]) (by decide +kernel)
def pv224299 : PrimeValue := ⟨224299, pr224299⟩
private theorem pr224303 : PrimeCertificate 224303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv8627]) (by decide +kernel)
def pv224303 : PrimeValue := ⟨224303, pr224303⟩
private theorem pr224317 : PrimeCertificate 224317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv67]) (by decide +kernel)
def pv224317 : PrimeValue := ⟨224317, pr224317⟩
private theorem pr224351 : PrimeCertificate 224351 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv641]) (by decide +kernel)
def pv224351 : PrimeValue := ⟨224351, pr224351⟩
private theorem pr224363 : PrimeCertificate 224363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv112181]) (by decide +kernel)
def pv224363 : PrimeValue := ⟨224363, pr224363⟩
private theorem pr224423 : PrimeCertificate 224423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv101]) (by decide +kernel)
def pv224423 : PrimeValue := ⟨224423, pr224423⟩
private theorem pr224429 : PrimeCertificate 224429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv2953]) (by decide +kernel)
def pv224429 : PrimeValue := ⟨224429, pr224429⟩
private theorem pr224449 : PrimeCertificate 224449 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv167]) (by decide +kernel)
def pv224449 : PrimeValue := ⟨224449, pr224449⟩
private theorem pr224461 : PrimeCertificate 224461 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv29,pv43]) (by decide +kernel)
def pv224461 : PrimeValue := ⟨224461, pr224461⟩
private theorem pr224491 : PrimeCertificate 224491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv1069]) (by decide +kernel)
def pv224491 : PrimeValue := ⟨224491, pr224491⟩
private theorem pr224501 : PrimeCertificate 224501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv449]) (by decide +kernel)
def pv224501 : PrimeValue := ⟨224501, pr224501⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
