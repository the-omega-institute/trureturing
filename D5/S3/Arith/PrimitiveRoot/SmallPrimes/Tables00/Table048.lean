/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table048
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table048.pv132611
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table006
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table009
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table010
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table026
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table027

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr132611 : PrimeCertificate 132611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv89,pv149]) (by decide +kernel)
def pv132611 : PrimeValue := ⟨132611, pr132611⟩
private theorem pr132619 : PrimeCertificate 132619 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23,pv31]) (by decide +kernel)
def pv132619 : PrimeValue := ⟨132619, pr132619⟩
private theorem pr132623 : PrimeCertificate 132623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv9473]) (by decide +kernel)
def pv132623 : PrimeValue := ⟨132623, pr132623⟩
private theorem pr132637 : PrimeCertificate 132637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1579]) (by decide +kernel)
def pv132637 : PrimeValue := ⟨132637, pr132637⟩
private theorem pr132647 : PrimeCertificate 132647 :=
  certifyPrime (q := pv5) (ls := [pv2,pv29,pv2287]) (by decide +kernel)
def pv132647 : PrimeValue := ⟨132647, pr132647⟩
private theorem pr132667 : PrimeCertificate 132667 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv22111]) (by decide +kernel)
def pv132667 : PrimeValue := ⟨132667, pr132667⟩
private theorem pr132679 : PrimeCertificate 132679 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv7,pv13]) (by decide +kernel)
def pv132679 : PrimeValue := ⟨132679, pr132679⟩
private theorem pr132689 : PrimeCertificate 132689 :=
  certifyPrime (q := pv3) (ls := [pv2,pv8293]) (by decide +kernel)
def pv132689 : PrimeValue := ⟨132689, pr132689⟩
private theorem pr132697 : PrimeCertificate 132697 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv19,pv97]) (by decide +kernel)
def pv132697 : PrimeValue := ⟨132697, pr132697⟩
private theorem pr132701 : PrimeCertificate 132701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1327]) (by decide +kernel)
def pv132701 : PrimeValue := ⟨132701, pr132701⟩
private theorem pr132707 : PrimeCertificate 132707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv9479]) (by decide +kernel)
def pv132707 : PrimeValue := ⟨132707, pr132707⟩
private theorem pr132709 : PrimeCertificate 132709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11059]) (by decide +kernel)
def pv132709 : PrimeValue := ⟨132709, pr132709⟩
private theorem pr132721 : PrimeCertificate 132721 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv5,pv7,pv79]) (by decide +kernel)
def pv132721 : PrimeValue := ⟨132721, pr132721⟩
private theorem pr132739 : PrimeCertificate 132739 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv22123]) (by decide +kernel)
def pv132739 : PrimeValue := ⟨132739, pr132739⟩
private theorem pr132749 : PrimeCertificate 132749 :=
  certifyPrime (q := pv13) (ls := [pv2,pv7,pv11,pv431]) (by decide +kernel)
def pv132749 : PrimeValue := ⟨132749, pr132749⟩
private theorem pr132751 : PrimeCertificate 132751 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv59]) (by decide +kernel)
def pv132751 : PrimeValue := ⟨132751, pr132751⟩
private theorem pr132761 : PrimeCertificate 132761 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv3319]) (by decide +kernel)
def pv132761 : PrimeValue := ⟨132761, pr132761⟩
private theorem pr132763 : PrimeCertificate 132763 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv29,pv109]) (by decide +kernel)
def pv132763 : PrimeValue := ⟨132763, pr132763⟩
private theorem pr132817 : PrimeCertificate 132817 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2767]) (by decide +kernel)
def pv132817 : PrimeValue := ⟨132817, pr132817⟩
private theorem pr132851 : PrimeCertificate 132851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv2657]) (by decide +kernel)
def pv132851 : PrimeValue := ⟨132851, pr132851⟩
private theorem pr132857 : PrimeCertificate 132857 :=
  certifyPrime (q := pv3) (ls := [pv2,pv16607]) (by decide +kernel)
def pv132857 : PrimeValue := ⟨132857, pr132857⟩
private theorem pr132859 : PrimeCertificate 132859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv61]) (by decide +kernel)
def pv132859 : PrimeValue := ⟨132859, pr132859⟩
private theorem pr132863 : PrimeCertificate 132863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv66431]) (by decide +kernel)
def pv132863 : PrimeValue := ⟨132863, pr132863⟩
private theorem pr132887 : PrimeCertificate 132887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv19,pv269]) (by decide +kernel)
def pv132887 : PrimeValue := ⟨132887, pr132887⟩
private theorem pr132893 : PrimeCertificate 132893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv33223]) (by decide +kernel)
def pv132893 : PrimeValue := ⟨132893, pr132893⟩
private theorem pr132911 : PrimeCertificate 132911 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13291]) (by decide +kernel)
def pv132911 : PrimeValue := ⟨132911, pr132911⟩
private theorem pr132929 : PrimeCertificate 132929 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv67]) (by decide +kernel)
def pv132929 : PrimeValue := ⟨132929, pr132929⟩
private theorem pr132947 : PrimeCertificate 132947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv6043]) (by decide +kernel)
def pv132947 : PrimeValue := ⟨132947, pr132947⟩
private theorem pr132949 : PrimeCertificate 132949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1231]) (by decide +kernel)
def pv132949 : PrimeValue := ⟨132949, pr132949⟩
private theorem pr132953 : PrimeCertificate 132953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv16619]) (by decide +kernel)
def pv132953 : PrimeValue := ⟨132953, pr132953⟩
private theorem pr132961 : PrimeCertificate 132961 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv277]) (by decide +kernel)
def pv132961 : PrimeValue := ⟨132961, pr132961⟩
private theorem pr132967 : PrimeCertificate 132967 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv83,pv89]) (by decide +kernel)
def pv132967 : PrimeValue := ⟨132967, pr132967⟩
private theorem pr132971 : PrimeCertificate 132971 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv13297]) (by decide +kernel)
def pv132971 : PrimeValue := ⟨132971, pr132971⟩
private theorem pr132989 : PrimeCertificate 132989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv33247]) (by decide +kernel)
def pv132989 : PrimeValue := ⟨132989, pr132989⟩
private theorem pr133013 : PrimeCertificate 133013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv3023]) (by decide +kernel)
def pv133013 : PrimeValue := ⟨133013, pr133013⟩
private theorem pr133033 : PrimeCertificate 133033 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv23,pv241]) (by decide +kernel)
def pv133033 : PrimeValue := ⟨133033, pr133033⟩
private theorem pr133051 : PrimeCertificate 133051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv887]) (by decide +kernel)
def pv133051 : PrimeValue := ⟨133051, pr133051⟩
private theorem pr133069 : PrimeCertificate 133069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv853]) (by decide +kernel)
def pv133069 : PrimeValue := ⟨133069, pr133069⟩
private theorem pr133073 : PrimeCertificate 133073 :=
  certifyPrime (q := pv3) (ls := [pv2,pv8317]) (by decide +kernel)
def pv133073 : PrimeValue := ⟨133073, pr133073⟩
private theorem pr133087 : PrimeCertificate 133087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv41,pv541]) (by decide +kernel)
def pv133087 : PrimeValue := ⟨133087, pr133087⟩
private theorem pr133097 : PrimeCertificate 133097 :=
  certifyPrime (q := pv3) (ls := [pv2,pv127,pv131]) (by decide +kernel)
def pv133097 : PrimeValue := ⟨133097, pr133097⟩
private theorem pr133109 : PrimeCertificate 133109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv107,pv311]) (by decide +kernel)
def pv133109 : PrimeValue := ⟨133109, pr133109⟩
private theorem pr133121 : PrimeCertificate 133121 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13]) (by decide +kernel)
def pv133121 : PrimeValue := ⟨133121, pr133121⟩
private theorem pr133157 : PrimeCertificate 133157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv33289]) (by decide +kernel)
def pv133157 : PrimeValue := ⟨133157, pr133157⟩
private theorem pr133183 : PrimeCertificate 133183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv151]) (by decide +kernel)
def pv133183 : PrimeValue := ⟨133183, pr133183⟩
private theorem pr133187 : PrimeCertificate 133187 :=
  certifyPrime (q := pv2) (ls := [pv2,pv66593]) (by decide +kernel)
def pv133187 : PrimeValue := ⟨133187, pr133187⟩
private theorem pr133213 : PrimeCertificate 133213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv653]) (by decide +kernel)
def pv133213 : PrimeValue := ⟨133213, pr133213⟩
private theorem pr133241 : PrimeCertificate 133241 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv3331]) (by decide +kernel)
def pv133241 : PrimeValue := ⟨133241, pr133241⟩
private theorem pr133253 : PrimeCertificate 133253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv4759]) (by decide +kernel)
def pv133253 : PrimeValue := ⟨133253, pr133253⟩
private theorem pr133261 : PrimeCertificate 133261 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv5,pv2221]) (by decide +kernel)
def pv133261 : PrimeValue := ⟨133261, pr133261⟩
private theorem pr133271 : PrimeCertificate 133271 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv13327]) (by decide +kernel)
def pv133271 : PrimeValue := ⟨133271, pr133271⟩
private theorem pr133277 : PrimeCertificate 133277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13,pv233]) (by decide +kernel)
def pv133277 : PrimeValue := ⟨133277, pr133277⟩
private theorem pr133303 : PrimeCertificate 133303 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv1709]) (by decide +kernel)
def pv133303 : PrimeValue := ⟨133303, pr133303⟩
private theorem pr133319 : PrimeCertificate 133319 :=
  certifyPrime (q := pv7) (ls := [pv2,pv191,pv349]) (by decide +kernel)
def pv133319 : PrimeValue := ⟨133319, pr133319⟩
private theorem pr133321 : PrimeCertificate 133321 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv11,pv101]) (by decide +kernel)
def pv133321 : PrimeValue := ⟨133321, pr133321⟩
private theorem pr133327 : PrimeCertificate 133327 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv823]) (by decide +kernel)
def pv133327 : PrimeValue := ⟨133327, pr133327⟩
private theorem pr133337 : PrimeCertificate 133337 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv2381]) (by decide +kernel)
def pv133337 : PrimeValue := ⟨133337, pr133337⟩
private theorem pr133349 : PrimeCertificate 133349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv37,pv53]) (by decide +kernel)
def pv133349 : PrimeValue := ⟨133349, pr133349⟩
private theorem pr133351 : PrimeCertificate 133351 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv127]) (by decide +kernel)
def pv133351 : PrimeValue := ⟨133351, pr133351⟩
private theorem pr133379 : PrimeCertificate 133379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv1361]) (by decide +kernel)
def pv133379 : PrimeValue := ⟨133379, pr133379⟩
private theorem pr133387 : PrimeCertificate 133387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv43,pv47]) (by decide +kernel)
def pv133387 : PrimeValue := ⟨133387, pr133387⟩
private theorem pr133391 : PrimeCertificate 133391 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv13339]) (by decide +kernel)
def pv133391 : PrimeValue := ⟨133391, pr133391⟩
private theorem pr133403 : PrimeCertificate 133403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv66701]) (by decide +kernel)
def pv133403 : PrimeValue := ⟨133403, pr133403⟩
private theorem pr133439 : PrimeCertificate 133439 :=
  certifyPrime (q := pv11) (ls := [pv2,pv137,pv487]) (by decide +kernel)
def pv133439 : PrimeValue := ⟨133439, pr133439⟩
private theorem pr133447 : PrimeCertificate 133447 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv23,pv967]) (by decide +kernel)
def pv133447 : PrimeValue := ⟨133447, pr133447⟩
private theorem pr133451 : PrimeCertificate 133451 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv17,pv157]) (by decide +kernel)
def pv133451 : PrimeValue := ⟨133451, pr133451⟩
private theorem pr133481 : PrimeCertificate 133481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv47,pv71]) (by decide +kernel)
def pv133481 : PrimeValue := ⟨133481, pr133481⟩
private theorem pr133493 : PrimeCertificate 133493 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv1451]) (by decide +kernel)
def pv133493 : PrimeValue := ⟨133493, pr133493⟩
private theorem pr133499 : PrimeCertificate 133499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv66749]) (by decide +kernel)
def pv133499 : PrimeValue := ⟨133499, pr133499⟩
private theorem pr133519 : PrimeCertificate 133519 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv11,pv17]) (by decide +kernel)
def pv133519 : PrimeValue := ⟨133519, pr133519⟩
private theorem pr133541 : PrimeCertificate 133541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv607]) (by decide +kernel)
def pv133541 : PrimeValue := ⟨133541, pr133541⟩
private theorem pr133543 : PrimeCertificate 133543 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv2473]) (by decide +kernel)
def pv133543 : PrimeValue := ⟨133543, pr133543⟩
private theorem pr133559 : PrimeCertificate 133559 :=
  certifyPrime (q := pv17) (ls := [pv2,pv43,pv1553]) (by decide +kernel)
def pv133559 : PrimeValue := ⟨133559, pr133559⟩
private theorem pr133571 : PrimeCertificate 133571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv37]) (by decide +kernel)
def pv133571 : PrimeValue := ⟨133571, pr133571⟩
private theorem pr133583 : PrimeCertificate 133583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv66791]) (by decide +kernel)
def pv133583 : PrimeValue := ⟨133583, pr133583⟩
private theorem pr133597 : PrimeCertificate 133597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1237]) (by decide +kernel)
def pv133597 : PrimeValue := ⟨133597, pr133597⟩
private theorem pr133631 : PrimeCertificate 133631 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv23,pv83]) (by decide +kernel)
def pv133631 : PrimeValue := ⟨133631, pr133631⟩
private theorem pr133633 : PrimeCertificate 133633 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv29]) (by decide +kernel)
def pv133633 : PrimeValue := ⟨133633, pr133633⟩
private theorem pr133649 : PrimeCertificate 133649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv8353]) (by decide +kernel)
def pv133649 : PrimeValue := ⟨133649, pr133649⟩
private theorem pr133657 : PrimeCertificate 133657 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5569]) (by decide +kernel)
def pv133657 : PrimeValue := ⟨133657, pr133657⟩
private theorem pr133691 : PrimeCertificate 133691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29,pv461]) (by decide +kernel)
def pv133691 : PrimeValue := ⟨133691, pr133691⟩
private theorem pr133697 : PrimeCertificate 133697 :=
  certifyPrime (q := pv3) (ls := [pv2,pv2089]) (by decide +kernel)
def pv133697 : PrimeValue := ⟨133697, pr133697⟩
private theorem pr133709 : PrimeCertificate 133709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv33427]) (by decide +kernel)
def pv133709 : PrimeValue := ⟨133709, pr133709⟩
private theorem pr133711 : PrimeCertificate 133711 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv4457]) (by decide +kernel)
def pv133711 : PrimeValue := ⟨133711, pr133711⟩
private theorem pr133723 : PrimeCertificate 133723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv19,pv23]) (by decide +kernel)
def pv133723 : PrimeValue := ⟨133723, pr133723⟩
private theorem pr133733 : PrimeCertificate 133733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67,pv499]) (by decide +kernel)
def pv133733 : PrimeValue := ⟨133733, pr133733⟩
private theorem pr133769 : PrimeCertificate 133769 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv727]) (by decide +kernel)
def pv133769 : PrimeValue := ⟨133769, pr133769⟩
private theorem pr133781 : PrimeCertificate 133781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv6689]) (by decide +kernel)
def pv133781 : PrimeValue := ⟨133781, pr133781⟩
private theorem pr133811 : PrimeCertificate 133811 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv13381]) (by decide +kernel)
def pv133811 : PrimeValue := ⟨133811, pr133811⟩
private theorem pr133813 : PrimeCertificate 133813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv59]) (by decide +kernel)
def pv133813 : PrimeValue := ⟨133813, pr133813⟩
private theorem pr133831 : PrimeCertificate 133831 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv1487]) (by decide +kernel)
def pv133831 : PrimeValue := ⟨133831, pr133831⟩
private theorem pr133843 : PrimeCertificate 133843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv22307]) (by decide +kernel)
def pv133843 : PrimeValue := ⟨133843, pr133843⟩
private theorem pr133853 : PrimeCertificate 133853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv109,pv307]) (by decide +kernel)
def pv133853 : PrimeValue := ⟨133853, pr133853⟩
private theorem pr133873 : PrimeCertificate 133873 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv2789]) (by decide +kernel)
def pv133873 : PrimeValue := ⟨133873, pr133873⟩
private theorem pr133919 : PrimeCertificate 133919 :=
  certifyPrime (q := pv7) (ls := [pv2,pv66959]) (by decide +kernel)
def pv133919 : PrimeValue := ⟨133919, pr133919⟩
private theorem pr133949 : PrimeCertificate 133949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv33487]) (by decide +kernel)
def pv133949 : PrimeValue := ⟨133949, pr133949⟩
private theorem pr133963 : PrimeCertificate 133963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv83,pv269]) (by decide +kernel)
def pv133963 : PrimeValue := ⟨133963, pr133963⟩
private theorem pr133979 : PrimeCertificate 133979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv5153]) (by decide +kernel)
def pv133979 : PrimeValue := ⟨133979, pr133979⟩
private theorem pr133981 : PrimeCertificate 133981 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv7,pv11,pv29]) (by decide +kernel)
def pv133981 : PrimeValue := ⟨133981, pr133981⟩
private theorem pr133993 : PrimeCertificate 133993 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1861]) (by decide +kernel)
def pv133993 : PrimeValue := ⟨133993, pr133993⟩
private theorem pr133999 : PrimeCertificate 133999 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv971]) (by decide +kernel)
def pv133999 : PrimeValue := ⟨133999, pr133999⟩
private theorem pr134033 : PrimeCertificate 134033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv8377]) (by decide +kernel)
def pv134033 : PrimeValue := ⟨134033, pr134033⟩
private theorem pr134039 : PrimeCertificate 134039 :=
  certifyPrime (q := pv11) (ls := [pv2,pv29,pv2311]) (by decide +kernel)
def pv134039 : PrimeValue := ⟨134039, pr134039⟩
private theorem pr134047 : PrimeCertificate 134047 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11,pv677]) (by decide +kernel)
def pv134047 : PrimeValue := ⟨134047, pr134047⟩
private theorem pr134053 : PrimeCertificate 134053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11171]) (by decide +kernel)
def pv134053 : PrimeValue := ⟨134053, pr134053⟩
private theorem pr134059 : PrimeCertificate 134059 :=
  certifyPrime (q := pv53) (ls := [pv2,pv3,pv22343]) (by decide +kernel)
def pv134059 : PrimeValue := ⟨134059, pr134059⟩
private theorem pr134077 : PrimeCertificate 134077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11173]) (by decide +kernel)
def pv134077 : PrimeValue := ⟨134077, pr134077⟩
private theorem pr134087 : PrimeCertificate 134087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv67043]) (by decide +kernel)
def pv134087 : PrimeValue := ⟨134087, pr134087⟩
private theorem pr134089 : PrimeCertificate 134089 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv37,pv151]) (by decide +kernel)
def pv134089 : PrimeValue := ⟨134089, pr134089⟩
private theorem pr134093 : PrimeCertificate 134093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv4789]) (by decide +kernel)
def pv134093 : PrimeValue := ⟨134093, pr134093⟩
private theorem pr134129 : PrimeCertificate 134129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv83,pv101]) (by decide +kernel)
def pv134129 : PrimeValue := ⟨134129, pr134129⟩
private theorem pr134153 : PrimeCertificate 134153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41,pv409]) (by decide +kernel)
def pv134153 : PrimeValue := ⟨134153, pr134153⟩
private theorem pr134161 : PrimeCertificate 134161 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv13,pv43]) (by decide +kernel)
def pv134161 : PrimeValue := ⟨134161, pr134161⟩
private theorem pr134171 : PrimeCertificate 134171 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv13417]) (by decide +kernel)
def pv134171 : PrimeValue := ⟨134171, pr134171⟩
private theorem pr134191 : PrimeCertificate 134191 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv71]) (by decide +kernel)
def pv134191 : PrimeValue := ⟨134191, pr134191⟩
private theorem pr134207 : PrimeCertificate 134207 :=
  certifyPrime (q := pv5) (ls := [pv2,pv67103]) (by decide +kernel)
def pv134207 : PrimeValue := ⟨134207, pr134207⟩
private theorem pr134213 : PrimeCertificate 134213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv29,pv89]) (by decide +kernel)
def pv134213 : PrimeValue := ⟨134213, pr134213⟩
private theorem pr134219 : PrimeCertificate 134219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv9587]) (by decide +kernel)
def pv134219 : PrimeValue := ⟨134219, pr134219⟩
private theorem pr134227 : PrimeCertificate 134227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7457]) (by decide +kernel)
def pv134227 : PrimeValue := ⟨134227, pr134227⟩
private theorem pr134243 : PrimeCertificate 134243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67121]) (by decide +kernel)
def pv134243 : PrimeValue := ⟨134243, pr134243⟩
private theorem pr134257 : PrimeCertificate 134257 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2797]) (by decide +kernel)
def pv134257 : PrimeValue := ⟨134257, pr134257⟩
private theorem pr134263 : PrimeCertificate 134263 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7459]) (by decide +kernel)
def pv134263 : PrimeValue := ⟨134263, pr134263⟩
private theorem pr134287 : PrimeCertificate 134287 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv22381]) (by decide +kernel)
def pv134287 : PrimeValue := ⟨134287, pr134287⟩
private theorem pr134291 : PrimeCertificate 134291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv1033]) (by decide +kernel)
def pv134291 : PrimeValue := ⟨134291, pr134291⟩
private theorem pr134293 : PrimeCertificate 134293 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv19,pv31]) (by decide +kernel)
def pv134293 : PrimeValue := ⟨134293, pr134293⟩
private theorem pr134327 : PrimeCertificate 134327 :=
  certifyPrime (q := pv5) (ls := [pv2,pv47,pv1429]) (by decide +kernel)
def pv134327 : PrimeValue := ⟨134327, pr134327⟩
private theorem pr134333 : PrimeCertificate 134333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv43,pv71]) (by decide +kernel)
def pv134333 : PrimeValue := ⟨134333, pr134333⟩
private theorem pr134339 : PrimeCertificate 134339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67169]) (by decide +kernel)
def pv134339 : PrimeValue := ⟨134339, pr134339⟩
private theorem pr134353 : PrimeCertificate 134353 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv311]) (by decide +kernel)
def pv134353 : PrimeValue := ⟨134353, pr134353⟩
private theorem pr134359 : PrimeCertificate 134359 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv457]) (by decide +kernel)
def pv134359 : PrimeValue := ⟨134359, pr134359⟩
private theorem pr134363 : PrimeCertificate 134363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67181]) (by decide +kernel)
def pv134363 : PrimeValue := ⟨134363, pr134363⟩
private theorem pr134369 : PrimeCertificate 134369 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv17,pv19]) (by decide +kernel)
def pv134369 : PrimeValue := ⟨134369, pr134369⟩
private theorem pr134371 : PrimeCertificate 134371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1493]) (by decide +kernel)
def pv134371 : PrimeValue := ⟨134371, pr134371⟩
private theorem pr134399 : PrimeCertificate 134399 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv41,pv149]) (by decide +kernel)
def pv134399 : PrimeValue := ⟨134399, pr134399⟩
private theorem pr134401 : PrimeCertificate 134401 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv134401 : PrimeValue := ⟨134401, pr134401⟩
private theorem pr134417 : PrimeCertificate 134417 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv271]) (by decide +kernel)
def pv134417 : PrimeValue := ⟨134417, pr134417⟩
private theorem pr134437 : PrimeCertificate 134437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv659]) (by decide +kernel)
def pv134437 : PrimeValue := ⟨134437, pr134437⟩
private theorem pr134443 : PrimeCertificate 134443 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv97]) (by decide +kernel)
def pv134443 : PrimeValue := ⟨134443, pr134443⟩
private theorem pr134471 : PrimeCertificate 134471 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv17,pv113]) (by decide +kernel)
def pv134471 : PrimeValue := ⟨134471, pr134471⟩
private theorem pr134489 : PrimeCertificate 134489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv16811]) (by decide +kernel)
def pv134489 : PrimeValue := ⟨134489, pr134489⟩
private theorem pr134503 : PrimeCertificate 134503 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv29,pv773]) (by decide +kernel)
def pv134503 : PrimeValue := ⟨134503, pr134503⟩
private theorem pr134507 : PrimeCertificate 134507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv109,pv617]) (by decide +kernel)
def pv134507 : PrimeValue := ⟨134507, pr134507⟩
private theorem pr134513 : PrimeCertificate 134513 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv1201]) (by decide +kernel)
def pv134513 : PrimeValue := ⟨134513, pr134513⟩
private theorem pr134581 : PrimeCertificate 134581 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv2243]) (by decide +kernel)
def pv134581 : PrimeValue := ⟨134581, pr134581⟩
private theorem pr134587 : PrimeCertificate 134587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7477]) (by decide +kernel)
def pv134587 : PrimeValue := ⟨134587, pr134587⟩
private theorem pr134591 : PrimeCertificate 134591 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv43,pv313]) (by decide +kernel)
def pv134591 : PrimeValue := ⟨134591, pr134591⟩
private theorem pr134593 : PrimeCertificate 134593 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv701]) (by decide +kernel)
def pv134593 : PrimeValue := ⟨134593, pr134593⟩
private theorem pr134597 : PrimeCertificate 134597 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11,pv19,pv23]) (by decide +kernel)
def pv134597 : PrimeValue := ⟨134597, pr134597⟩
private theorem pr134609 : PrimeCertificate 134609 :=
  certifyPrime (q := pv3) (ls := [pv2,pv47,pv179]) (by decide +kernel)
def pv134609 : PrimeValue := ⟨134609, pr134609⟩
private theorem pr134639 : PrimeCertificate 134639 :=
  certifyPrime (q := pv13) (ls := [pv2,pv7,pv59,pv163]) (by decide +kernel)
def pv134639 : PrimeValue := ⟨134639, pr134639⟩
private theorem pr134669 : PrimeCertificate 134669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv131,pv257]) (by decide +kernel)
def pv134669 : PrimeValue := ⟨134669, pr134669⟩
private theorem pr134677 : PrimeCertificate 134677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv43]) (by decide +kernel)
def pv134677 : PrimeValue := ⟨134677, pr134677⟩
private theorem pr134681 : PrimeCertificate 134681 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv13,pv37]) (by decide +kernel)
def pv134681 : PrimeValue := ⟨134681, pr134681⟩
private theorem pr134683 : PrimeCertificate 134683 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv22447]) (by decide +kernel)
def pv134683 : PrimeValue := ⟨134683, pr134683⟩
private theorem pr134699 : PrimeCertificate 134699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67349]) (by decide +kernel)
def pv134699 : PrimeValue := ⟨134699, pr134699⟩
private theorem pr134707 : PrimeCertificate 134707 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv13,pv157]) (by decide +kernel)
def pv134707 : PrimeValue := ⟨134707, pr134707⟩
private theorem pr134753 : PrimeCertificate 134753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv4211]) (by decide +kernel)
def pv134753 : PrimeValue := ⟨134753, pr134753⟩
private theorem pr134789 : PrimeCertificate 134789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv1087]) (by decide +kernel)
def pv134789 : PrimeValue := ⟨134789, pr134789⟩
private theorem pr134807 : PrimeCertificate 134807 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv9629]) (by decide +kernel)
def pv134807 : PrimeValue := ⟨134807, pr134807⟩
private theorem pr134837 : PrimeCertificate 134837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv2593]) (by decide +kernel)
def pv134837 : PrimeValue := ⟨134837, pr134837⟩
private theorem pr134851 : PrimeCertificate 134851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv29,pv31]) (by decide +kernel)
def pv134851 : PrimeValue := ⟨134851, pr134851⟩
private theorem pr134857 : PrimeCertificate 134857 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1873]) (by decide +kernel)
def pv134857 : PrimeValue := ⟨134857, pr134857⟩
private theorem pr134867 : PrimeCertificate 134867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67433]) (by decide +kernel)
def pv134867 : PrimeValue := ⟨134867, pr134867⟩
private theorem pr134873 : PrimeCertificate 134873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv733]) (by decide +kernel)
def pv134873 : PrimeValue := ⟨134873, pr134873⟩
private theorem pr134887 : PrimeCertificate 134887 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv22481]) (by decide +kernel)
def pv134887 : PrimeValue := ⟨134887, pr134887⟩
private theorem pr134909 : PrimeCertificate 134909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv1163]) (by decide +kernel)
def pv134909 : PrimeValue := ⟨134909, pr134909⟩
private theorem pr134921 : PrimeCertificate 134921 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv3373]) (by decide +kernel)
def pv134921 : PrimeValue := ⟨134921, pr134921⟩
private theorem pr134923 : PrimeCertificate 134923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv113,pv199]) (by decide +kernel)
def pv134923 : PrimeValue := ⟨134923, pr134923⟩
private theorem pr134947 : PrimeCertificate 134947 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv17]) (by decide +kernel)
def pv134947 : PrimeValue := ⟨134947, pr134947⟩
private theorem pr134951 : PrimeCertificate 134951 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv2699]) (by decide +kernel)
def pv134951 : PrimeValue := ⟨134951, pr134951⟩
private theorem pr134989 : PrimeCertificate 134989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1607]) (by decide +kernel)
def pv134989 : PrimeValue := ⟨134989, pr134989⟩
private theorem pr134999 : PrimeCertificate 134999 :=
  certifyPrime (q := pv7) (ls := [pv2,pv67499]) (by decide +kernel)
def pv134999 : PrimeValue := ⟨134999, pr134999⟩
private theorem pr135007 : PrimeCertificate 135007 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv22501]) (by decide +kernel)
def pv135007 : PrimeValue := ⟨135007, pr135007⟩
private theorem pr135017 : PrimeCertificate 135017 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv2411]) (by decide +kernel)
def pv135017 : PrimeValue := ⟨135017, pr135017⟩
private theorem pr135019 : PrimeCertificate 135019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv577]) (by decide +kernel)
def pv135019 : PrimeValue := ⟨135019, pr135019⟩
private theorem pr135029 : PrimeCertificate 135029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv33757]) (by decide +kernel)
def pv135029 : PrimeValue := ⟨135029, pr135029⟩
private theorem pr135043 : PrimeCertificate 135043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv71,pv317]) (by decide +kernel)
def pv135043 : PrimeValue := ⟨135043, pr135043⟩
private theorem pr135049 : PrimeCertificate 135049 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv331]) (by decide +kernel)
def pv135049 : PrimeValue := ⟨135049, pr135049⟩
private theorem pr135059 : PrimeCertificate 135059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv877]) (by decide +kernel)
def pv135059 : PrimeValue := ⟨135059, pr135059⟩
private theorem pr135089 : PrimeCertificate 135089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv8443]) (by decide +kernel)
def pv135089 : PrimeValue := ⟨135089, pr135089⟩
private theorem pr135119 : PrimeCertificate 135119 :=
  certifyPrime (q := pv17) (ls := [pv2,pv67559]) (by decide +kernel)
def pv135119 : PrimeValue := ⟨135119, pr135119⟩
private theorem pr135151 : PrimeCertificate 135151 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv17,pv53]) (by decide +kernel)
def pv135151 : PrimeValue := ⟨135151, pr135151⟩
private theorem pr135173 : PrimeCertificate 135173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv719]) (by decide +kernel)
def pv135173 : PrimeValue := ⟨135173, pr135173⟩
private theorem pr135193 : PrimeCertificate 135193 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv43,pv131]) (by decide +kernel)
def pv135193 : PrimeValue := ⟨135193, pr135193⟩
private theorem pr135197 : PrimeCertificate 135197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv463]) (by decide +kernel)
def pv135197 : PrimeValue := ⟨135197, pr135197⟩
private theorem pr135209 : PrimeCertificate 135209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv16901]) (by decide +kernel)
def pv135209 : PrimeValue := ⟨135209, pr135209⟩
private theorem pr135211 : PrimeCertificate 135211 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv4507]) (by decide +kernel)
def pv135211 : PrimeValue := ⟨135211, pr135211⟩
private theorem pr135221 : PrimeCertificate 135221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv6761]) (by decide +kernel)
def pv135221 : PrimeValue := ⟨135221, pr135221⟩
private theorem pr135241 : PrimeCertificate 135241 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv7,pv23]) (by decide +kernel)
def pv135241 : PrimeValue := ⟨135241, pr135241⟩
private theorem pr135257 : PrimeCertificate 135257 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv29,pv53]) (by decide +kernel)
def pv135257 : PrimeValue := ⟨135257, pr135257⟩
private theorem pr135271 : PrimeCertificate 135271 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv167]) (by decide +kernel)
def pv135271 : PrimeValue := ⟨135271, pr135271⟩
private theorem pr135277 : PrimeCertificate 135277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11273]) (by decide +kernel)
def pv135277 : PrimeValue := ⟨135277, pr135277⟩
private theorem pr135281 : PrimeCertificate 135281 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv19,pv89]) (by decide +kernel)
def pv135281 : PrimeValue := ⟨135281, pr135281⟩
private theorem pr135283 : PrimeCertificate 135283 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv3221]) (by decide +kernel)
def pv135283 : PrimeValue := ⟨135283, pr135283⟩
private theorem pr135301 : PrimeCertificate 135301 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv11,pv41]) (by decide +kernel)
def pv135301 : PrimeValue := ⟨135301, pr135301⟩
private theorem pr135319 : PrimeCertificate 135319 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv19,pv1187]) (by decide +kernel)
def pv135319 : PrimeValue := ⟨135319, pr135319⟩
private theorem pr135329 : PrimeCertificate 135329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv4229]) (by decide +kernel)
def pv135329 : PrimeValue := ⟨135329, pr135329⟩
private theorem pr135347 : PrimeCertificate 135347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv37,pv59]) (by decide +kernel)
def pv135347 : PrimeValue := ⟨135347, pr135347⟩
private theorem pr135349 : PrimeCertificate 135349 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11279]) (by decide +kernel)
def pv135349 : PrimeValue := ⟨135349, pr135349⟩
private theorem pr135353 : PrimeCertificate 135353 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv2417]) (by decide +kernel)
def pv135353 : PrimeValue := ⟨135353, pr135353⟩
private theorem pr135367 : PrimeCertificate 135367 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv293]) (by decide +kernel)
def pv135367 : PrimeValue := ⟨135367, pr135367⟩
private theorem pr135389 : PrimeCertificate 135389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv17,pv181]) (by decide +kernel)
def pv135389 : PrimeValue := ⟨135389, pr135389⟩
private theorem pr135391 : PrimeCertificate 135391 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv4513]) (by decide +kernel)
def pv135391 : PrimeValue := ⟨135391, pr135391⟩
private theorem pr135403 : PrimeCertificate 135403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv22567]) (by decide +kernel)
def pv135403 : PrimeValue := ⟨135403, pr135403⟩
private theorem pr135409 : PrimeCertificate 135409 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv13,pv31]) (by decide +kernel)
def pv135409 : PrimeValue := ⟨135409, pr135409⟩
private theorem pr135427 : PrimeCertificate 135427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv22571]) (by decide +kernel)
def pv135427 : PrimeValue := ⟨135427, pr135427⟩
private theorem pr135431 : PrimeCertificate 135431 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv29,pv467]) (by decide +kernel)
def pv135431 : PrimeValue := ⟨135431, pr135431⟩
private theorem pr135433 : PrimeCertificate 135433 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv19]) (by decide +kernel)
def pv135433 : PrimeValue := ⟨135433, pr135433⟩
private theorem pr135449 : PrimeCertificate 135449 :=
  certifyPrime (q := pv3) (ls := [pv2,pv16931]) (by decide +kernel)
def pv135449 : PrimeValue := ⟨135449, pr135449⟩
private theorem pr135461 : PrimeCertificate 135461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv521]) (by decide +kernel)
def pv135461 : PrimeValue := ⟨135461, pr135461⟩
private theorem pr135463 : PrimeCertificate 135463 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv107,pv211]) (by decide +kernel)
def pv135463 : PrimeValue := ⟨135463, pr135463⟩
private theorem pr135469 : PrimeCertificate 135469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53,pv71]) (by decide +kernel)
def pv135469 : PrimeValue := ⟨135469, pr135469⟩
private theorem pr135479 : PrimeCertificate 135479 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv9677]) (by decide +kernel)
def pv135479 : PrimeValue := ⟨135479, pr135479⟩
private theorem pr135497 : PrimeCertificate 135497 :=
  certifyPrime (q := pv3) (ls := [pv2,pv16937]) (by decide +kernel)
def pv135497 : PrimeValue := ⟨135497, pr135497⟩
private theorem pr135511 : PrimeCertificate 135511 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv4517]) (by decide +kernel)
def pv135511 : PrimeValue := ⟨135511, pr135511⟩
private theorem pr135533 : PrimeCertificate 135533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv1093]) (by decide +kernel)
def pv135533 : PrimeValue := ⟨135533, pr135533⟩
private theorem pr135559 : PrimeCertificate 135559 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv443]) (by decide +kernel)
def pv135559 : PrimeValue := ⟨135559, pr135559⟩
private theorem pr135571 : PrimeCertificate 135571 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv4519]) (by decide +kernel)
def pv135571 : PrimeValue := ⟨135571, pr135571⟩
private theorem pr135581 : PrimeCertificate 135581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv6779]) (by decide +kernel)
def pv135581 : PrimeValue := ⟨135581, pr135581⟩
private theorem pr135589 : PrimeCertificate 135589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11299]) (by decide +kernel)
def pv135589 : PrimeValue := ⟨135589, pr135589⟩
private theorem pr135593 : PrimeCertificate 135593 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv997]) (by decide +kernel)
def pv135593 : PrimeValue := ⟨135593, pr135593⟩
private theorem pr135599 : PrimeCertificate 135599 :=
  certifyPrime (q := pv7) (ls := [pv2,pv151,pv449]) (by decide +kernel)
def pv135599 : PrimeValue := ⟨135599, pr135599⟩
private theorem pr135601 : PrimeCertificate 135601 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv113]) (by decide +kernel)
def pv135601 : PrimeValue := ⟨135601, pr135601⟩
private theorem pr135613 : PrimeCertificate 135613 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3767]) (by decide +kernel)
def pv135613 : PrimeValue := ⟨135613, pr135613⟩
private theorem pr135617 : PrimeCertificate 135617 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv163]) (by decide +kernel)
def pv135617 : PrimeValue := ⟨135617, pr135617⟩
private theorem pr135637 : PrimeCertificate 135637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv89,pv127]) (by decide +kernel)
def pv135637 : PrimeValue := ⟨135637, pr135637⟩
private theorem pr135647 : PrimeCertificate 135647 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv9689]) (by decide +kernel)
def pv135647 : PrimeValue := ⟨135647, pr135647⟩
private theorem pr135649 : PrimeCertificate 135649 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv157]) (by decide +kernel)
def pv135649 : PrimeValue := ⟨135649, pr135649⟩
private theorem pr135661 : PrimeCertificate 135661 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv17,pv19]) (by decide +kernel)
def pv135661 : PrimeValue := ⟨135661, pr135661⟩
private theorem pr135671 : PrimeCertificate 135671 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13567]) (by decide +kernel)
def pv135671 : PrimeValue := ⟨135671, pr135671⟩
private theorem pr135697 : PrimeCertificate 135697 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv11,pv257]) (by decide +kernel)
def pv135697 : PrimeValue := ⟨135697, pr135697⟩
private theorem pr135701 : PrimeCertificate 135701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv59]) (by decide +kernel)
def pv135701 : PrimeValue := ⟨135701, pr135701⟩
private theorem pr135719 : PrimeCertificate 135719 :=
  certifyPrime (q := pv31) (ls := [pv2,pv11,pv31,pv199]) (by decide +kernel)
def pv135719 : PrimeValue := ⟨135719, pr135719⟩
private theorem pr135721 : PrimeCertificate 135721 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv13,pv29]) (by decide +kernel)
def pv135721 : PrimeValue := ⟨135721, pr135721⟩
private theorem pr135727 : PrimeCertificate 135727 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv22621]) (by decide +kernel)
def pv135727 : PrimeValue := ⟨135727, pr135727⟩
private theorem pr135731 : PrimeCertificate 135731 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv277]) (by decide +kernel)
def pv135731 : PrimeValue := ⟨135731, pr135731⟩
private theorem pr135743 : PrimeCertificate 135743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv67,pv1013]) (by decide +kernel)
def pv135743 : PrimeValue := ⟨135743, pr135743⟩
private theorem pr135757 : PrimeCertificate 135757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv419]) (by decide +kernel)
def pv135757 : PrimeValue := ⟨135757, pr135757⟩
private theorem pr135781 : PrimeCertificate 135781 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv31,pv73]) (by decide +kernel)
def pv135781 : PrimeValue := ⟨135781, pr135781⟩
private theorem pr135787 : PrimeCertificate 135787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv53,pv61]) (by decide +kernel)
def pv135787 : PrimeValue := ⟨135787, pr135787⟩
private theorem pr135799 : PrimeCertificate 135799 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv1741]) (by decide +kernel)
def pv135799 : PrimeValue := ⟨135799, pr135799⟩
private theorem pr135841 : PrimeCertificate 135841 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv283]) (by decide +kernel)
def pv135841 : PrimeValue := ⟨135841, pr135841⟩
private theorem pr135851 : PrimeCertificate 135851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv13,pv19]) (by decide +kernel)
def pv135851 : PrimeValue := ⟨135851, pr135851⟩
private theorem pr135859 : PrimeCertificate 135859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv22643]) (by decide +kernel)
def pv135859 : PrimeValue := ⟨135859, pr135859⟩
private theorem pr135887 : PrimeCertificate 135887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv67943]) (by decide +kernel)
def pv135887 : PrimeValue := ⟨135887, pr135887⟩
private theorem pr135893 : PrimeCertificate 135893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv641]) (by decide +kernel)
def pv135893 : PrimeValue := ⟨135893, pr135893⟩
private theorem pr135911 : PrimeCertificate 135911 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv13591]) (by decide +kernel)
def pv135911 : PrimeValue := ⟨135911, pr135911⟩
private theorem pr135913 : PrimeCertificate 135913 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv809]) (by decide +kernel)
def pv135913 : PrimeValue := ⟨135913, pr135913⟩
private theorem pr135929 : PrimeCertificate 135929 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv1307]) (by decide +kernel)
def pv135929 : PrimeValue := ⟨135929, pr135929⟩
private theorem pr135937 : PrimeCertificate 135937 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv59]) (by decide +kernel)
def pv135937 : PrimeValue := ⟨135937, pr135937⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
