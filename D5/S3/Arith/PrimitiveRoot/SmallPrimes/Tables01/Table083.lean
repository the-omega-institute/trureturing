/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table083
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table083.pv285611
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table007
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table009
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table012
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table019
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table051

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr285611 : PrimeCertificate 285611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13]) (by decide +kernel)
def pv285611 : PrimeValue := ⟨285611, pr285611⟩
private theorem pr285641 : PrimeCertificate 285641 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv37,pv193]) (by decide +kernel)
def pv285641 : PrimeValue := ⟨285641, pr285641⟩
private theorem pr285643 : PrimeCertificate 285643 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv2267]) (by decide +kernel)
def pv285643 : PrimeValue := ⟨285643, pr285643⟩
private theorem pr285661 : PrimeCertificate 285661 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv23]) (by decide +kernel)
def pv285661 : PrimeValue := ⟨285661, pr285661⟩
private theorem pr285667 : PrimeCertificate 285667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv1013]) (by decide +kernel)
def pv285667 : PrimeValue := ⟨285667, pr285667⟩
private theorem pr285673 : PrimeCertificate 285673 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11903]) (by decide +kernel)
def pv285673 : PrimeValue := ⟨285673, pr285673⟩
private theorem pr285697 : PrimeCertificate 285697 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31]) (by decide +kernel)
def pv285697 : PrimeValue := ⟨285697, pr285697⟩
private theorem pr285709 : PrimeCertificate 285709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv821]) (by decide +kernel)
def pv285709 : PrimeValue := ⟨285709, pr285709⟩
private theorem pr285721 : PrimeCertificate 285721 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv2381]) (by decide +kernel)
def pv285721 : PrimeValue := ⟨285721, pr285721⟩
private theorem pr285731 : PrimeCertificate 285731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv28573]) (by decide +kernel)
def pv285731 : PrimeValue := ⟨285731, pr285731⟩
private theorem pr285757 : PrimeCertificate 285757 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv23813]) (by decide +kernel)
def pv285757 : PrimeValue := ⟨285757, pr285757⟩
private theorem pr285763 : PrimeCertificate 285763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv97,pv491]) (by decide +kernel)
def pv285763 : PrimeValue := ⟨285763, pr285763⟩
private theorem pr285773 : PrimeCertificate 285773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71443]) (by decide +kernel)
def pv285773 : PrimeValue := ⟨285773, pr285773⟩
private theorem pr285781 : PrimeCertificate 285781 :=
  certifyPrime (q := pv53) (ls := [pv2,pv3,pv5,pv11,pv433]) (by decide +kernel)
def pv285781 : PrimeValue := ⟨285781, pr285781⟩
private theorem pr285823 : PrimeCertificate 285823 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv67,pv79]) (by decide +kernel)
def pv285823 : PrimeValue := ⟨285823, pr285823⟩
private theorem pr285827 : PrimeCertificate 285827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv241,pv593]) (by decide +kernel)
def pv285827 : PrimeValue := ⟨285827, pr285827⟩
private theorem pr285839 : PrimeCertificate 285839 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv17,pv1201]) (by decide +kernel)
def pv285839 : PrimeValue := ⟨285839, pr285839⟩
private theorem pr285841 : PrimeCertificate 285841 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv397]) (by decide +kernel)
def pv285841 : PrimeValue := ⟨285841, pr285841⟩
private theorem pr285871 : PrimeCertificate 285871 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv13,pv733]) (by decide +kernel)
def pv285871 : PrimeValue := ⟨285871, pr285871⟩
private theorem pr285937 : PrimeCertificate 285937 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv23,pv37]) (by decide +kernel)
def pv285937 : PrimeValue := ⟨285937, pr285937⟩
private theorem pr285949 : PrimeCertificate 285949 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv47]) (by decide +kernel)
def pv285949 : PrimeValue := ⟨285949, pr285949⟩
private theorem pr285953 : PrimeCertificate 285953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1117]) (by decide +kernel)
def pv285953 : PrimeValue := ⟨285953, pr285953⟩
private theorem pr285979 : PrimeCertificate 285979 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv619]) (by decide +kernel)
def pv285979 : PrimeValue := ⟨285979, pr285979⟩
private theorem pr285983 : PrimeCertificate 285983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv6217]) (by decide +kernel)
def pv285983 : PrimeValue := ⟨285983, pr285983⟩
private theorem pr285997 : PrimeCertificate 285997 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23833]) (by decide +kernel)
def pv285997 : PrimeValue := ⟨285997, pr285997⟩
private theorem pr286001 : PrimeCertificate 286001 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv13]) (by decide +kernel)
def pv286001 : PrimeValue := ⟨286001, pr286001⟩
private theorem pr286009 : PrimeCertificate 286009 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv17,pv701]) (by decide +kernel)
def pv286009 : PrimeValue := ⟨286009, pr286009⟩
private theorem pr286019 : PrimeCertificate 286019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv83,pv1723]) (by decide +kernel)
def pv286019 : PrimeValue := ⟨286019, pr286019⟩
private theorem pr286043 : PrimeCertificate 286043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv47,pv179]) (by decide +kernel)
def pv286043 : PrimeValue := ⟨286043, pr286043⟩
private theorem pr286061 : PrimeCertificate 286061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv14303]) (by decide +kernel)
def pv286061 : PrimeValue := ⟨286061, pr286061⟩
private theorem pr286063 : PrimeCertificate 286063 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv139]) (by decide +kernel)
def pv286063 : PrimeValue := ⟨286063, pr286063⟩
private theorem pr286103 : PrimeCertificate 286103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv7529]) (by decide +kernel)
def pv286103 : PrimeValue := ⟨286103, pr286103⟩
private theorem pr286129 : PrimeCertificate 286129 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv1987]) (by decide +kernel)
def pv286129 : PrimeValue := ⟨286129, pr286129⟩
private theorem pr286171 : PrimeCertificate 286171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv9539]) (by decide +kernel)
def pv286171 : PrimeValue := ⟨286171, pr286171⟩
private theorem pr286199 : PrimeCertificate 286199 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv13009]) (by decide +kernel)
def pv286199 : PrimeValue := ⟨286199, pr286199⟩
private theorem pr286243 : PrimeCertificate 286243 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv4337]) (by decide +kernel)
def pv286243 : PrimeValue := ⟨286243, pr286243⟩
private theorem pr286249 : PrimeCertificate 286249 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11927]) (by decide +kernel)
def pv286249 : PrimeValue := ⟨286249, pr286249⟩
private theorem pr286289 : PrimeCertificate 286289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv617]) (by decide +kernel)
def pv286289 : PrimeValue := ⟨286289, pr286289⟩
private theorem pr286301 : PrimeCertificate 286301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv409]) (by decide +kernel)
def pv286301 : PrimeValue := ⟨286301, pr286301⟩
private theorem pr286333 : PrimeCertificate 286333 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv107,pv223]) (by decide +kernel)
def pv286333 : PrimeValue := ⟨286333, pr286333⟩
private theorem pr286367 : PrimeCertificate 286367 :=
  certifyPrime (q := pv5) (ls := [pv2,pv131,pv1093]) (by decide +kernel)
def pv286367 : PrimeValue := ⟨286367, pr286367⟩
private theorem pr286381 : PrimeCertificate 286381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv37,pv43]) (by decide +kernel)
def pv286381 : PrimeValue := ⟨286381, pr286381⟩
private theorem pr286393 : PrimeCertificate 286393 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv11933]) (by decide +kernel)
def pv286393 : PrimeValue := ⟨286393, pr286393⟩
private theorem pr286397 : PrimeCertificate 286397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv23,pv283]) (by decide +kernel)
def pv286397 : PrimeValue := ⟨286397, pr286397⟩
private theorem pr286411 : PrimeCertificate 286411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv9547]) (by decide +kernel)
def pv286411 : PrimeValue := ⟨286411, pr286411⟩
private theorem pr286421 : PrimeCertificate 286421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv14321]) (by decide +kernel)
def pv286421 : PrimeValue := ⟨286421, pr286421⟩
private theorem pr286427 : PrimeCertificate 286427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv41,pv499]) (by decide +kernel)
def pv286427 : PrimeValue := ⟨286427, pr286427⟩
private theorem pr286453 : PrimeCertificate 286453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv73,pv109]) (by decide +kernel)
def pv286453 : PrimeValue := ⟨286453, pr286453⟩
private theorem pr286457 : PrimeCertificate 286457 :=
  certifyPrime (q := pv3) (ls := [pv2,pv61,pv587]) (by decide +kernel)
def pv286457 : PrimeValue := ⟨286457, pr286457⟩
private theorem pr286469 : PrimeCertificate 286469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv787]) (by decide +kernel)
def pv286469 : PrimeValue := ⟨286469, pr286469⟩
private theorem pr286477 : PrimeCertificate 286477 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23873]) (by decide +kernel)
def pv286477 : PrimeValue := ⟨286477, pr286477⟩
private theorem pr286483 : PrimeCertificate 286483 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv19,pv359]) (by decide +kernel)
def pv286483 : PrimeValue := ⟨286483, pr286483⟩
private theorem pr286487 : PrimeCertificate 286487 :=
  certifyPrime (q := pv5) (ls := [pv2,pv143243]) (by decide +kernel)
def pv286487 : PrimeValue := ⟨286487, pr286487⟩
private theorem pr286513 : PrimeCertificate 286513 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv47,pv127]) (by decide +kernel)
def pv286513 : PrimeValue := ⟨286513, pr286513⟩
private theorem pr286543 : PrimeCertificate 286543 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv15919]) (by decide +kernel)
def pv286543 : PrimeValue := ⟨286543, pr286543⟩
private theorem pr286553 : PrimeCertificate 286553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv17,pv43]) (by decide +kernel)
def pv286553 : PrimeValue := ⟨286553, pr286553⟩
private theorem pr286589 : PrimeCertificate 286589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71647]) (by decide +kernel)
def pv286589 : PrimeValue := ⟨286589, pr286589⟩
private theorem pr286591 : PrimeCertificate 286591 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv41,pv233]) (by decide +kernel)
def pv286591 : PrimeValue := ⟨286591, pr286591⟩
private theorem pr286609 : PrimeCertificate 286609 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv853]) (by decide +kernel)
def pv286609 : PrimeValue := ⟨286609, pr286609⟩
private theorem pr286633 : PrimeCertificate 286633 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv1327]) (by decide +kernel)
def pv286633 : PrimeValue := ⟨286633, pr286633⟩
private theorem pr286673 : PrimeCertificate 286673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv23,pv41]) (by decide +kernel)
def pv286673 : PrimeValue := ⟨286673, pr286673⟩
private theorem pr286687 : PrimeCertificate 286687 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv5309]) (by decide +kernel)
def pv286687 : PrimeValue := ⟨286687, pr286687⟩
private theorem pr286697 : PrimeCertificate 286697 :=
  certifyPrime (q := pv3) (ls := [pv2,pv35837]) (by decide +kernel)
def pv286697 : PrimeValue := ⟨286697, pr286697⟩
private theorem pr286703 : PrimeCertificate 286703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv11027]) (by decide +kernel)
def pv286703 : PrimeValue := ⟨286703, pr286703⟩
private theorem pr286711 : PrimeCertificate 286711 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv19,pv503]) (by decide +kernel)
def pv286711 : PrimeValue := ⟨286711, pr286711⟩
private theorem pr286733 : PrimeCertificate 286733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv97,pv739]) (by decide +kernel)
def pv286733 : PrimeValue := ⟨286733, pr286733⟩
private theorem pr286751 : PrimeCertificate 286751 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv31,pv37]) (by decide +kernel)
def pv286751 : PrimeValue := ⟨286751, pr286751⟩
private theorem pr286763 : PrimeCertificate 286763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv20483]) (by decide +kernel)
def pv286763 : PrimeValue := ⟨286763, pr286763⟩
private theorem pr286777 : PrimeCertificate 286777 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv569]) (by decide +kernel)
def pv286777 : PrimeValue := ⟨286777, pr286777⟩
private theorem pr286789 : PrimeCertificate 286789 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23899]) (by decide +kernel)
def pv286789 : PrimeValue := ⟨286789, pr286789⟩
private theorem pr286801 : PrimeCertificate 286801 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv239]) (by decide +kernel)
def pv286801 : PrimeValue := ⟨286801, pr286801⟩
private theorem pr286813 : PrimeCertificate 286813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv257]) (by decide +kernel)
def pv286813 : PrimeValue := ⟨286813, pr286813⟩
private theorem pr286859 : PrimeCertificate 286859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13,pv17,pv59]) (by decide +kernel)
def pv286859 : PrimeValue := ⟨286859, pr286859⟩
private theorem pr286927 : PrimeCertificate 286927 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv29,pv97]) (by decide +kernel)
def pv286927 : PrimeValue := ⟨286927, pr286927⟩
private theorem pr286981 : PrimeCertificate 286981 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv4783]) (by decide +kernel)
def pv286981 : PrimeValue := ⟨286981, pr286981⟩
private theorem pr286999 : PrimeCertificate 286999 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv31,pv1543]) (by decide +kernel)
def pv286999 : PrimeValue := ⟨286999, pr286999⟩
private theorem pr287003 : PrimeCertificate 287003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv143501]) (by decide +kernel)
def pv287003 : PrimeValue := ⟨287003, pr287003⟩
private theorem pr287047 : PrimeCertificate 287047 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37,pv431]) (by decide +kernel)
def pv287047 : PrimeValue := ⟨287047, pr287047⟩
private theorem pr287059 : PrimeCertificate 287059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47843]) (by decide +kernel)
def pv287059 : PrimeValue := ⟨287059, pr287059⟩
private theorem pr287137 : PrimeCertificate 287137 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv997]) (by decide +kernel)
def pv287137 : PrimeValue := ⟨287137, pr287137⟩
private theorem pr287141 : PrimeCertificate 287141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv293]) (by decide +kernel)
def pv287141 : PrimeValue := ⟨287141, pr287141⟩
private theorem pr287149 : PrimeCertificate 287149 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv23929]) (by decide +kernel)
def pv287149 : PrimeValue := ⟨287149, pr287149⟩
private theorem pr287159 : PrimeCertificate 287159 :=
  certifyPrime (q := pv11) (ls := [pv2,pv29,pv4951]) (by decide +kernel)
def pv287159 : PrimeValue := ⟨287159, pr287159⟩
private theorem pr287167 : PrimeCertificate 287167 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv19,pv229]) (by decide +kernel)
def pv287167 : PrimeValue := ⟨287167, pr287167⟩
private theorem pr287173 : PrimeCertificate 287173 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv2659]) (by decide +kernel)
def pv287173 : PrimeValue := ⟨287173, pr287173⟩
private theorem pr287191 : PrimeCertificate 287191 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv3191]) (by decide +kernel)
def pv287191 : PrimeValue := ⟨287191, pr287191⟩
private theorem pr287219 : PrimeCertificate 287219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv143609]) (by decide +kernel)
def pv287219 : PrimeValue := ⟨287219, pr287219⟩
private theorem pr287233 : PrimeCertificate 287233 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv17]) (by decide +kernel)
def pv287233 : PrimeValue := ⟨287233, pr287233⟩
private theorem pr287239 : PrimeCertificate 287239 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv977]) (by decide +kernel)
def pv287239 : PrimeValue := ⟨287239, pr287239⟩
private theorem pr287251 : PrimeCertificate 287251 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv383]) (by decide +kernel)
def pv287251 : PrimeValue := ⟨287251, pr287251⟩
private theorem pr287269 : PrimeCertificate 287269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv647]) (by decide +kernel)
def pv287269 : PrimeValue := ⟨287269, pr287269⟩
private theorem pr287279 : PrimeCertificate 287279 :=
  certifyPrime (q := pv11) (ls := [pv2,pv239,pv601]) (by decide +kernel)
def pv287279 : PrimeValue := ⟨287279, pr287279⟩
private theorem pr287281 : PrimeCertificate 287281 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv19]) (by decide +kernel)
def pv287281 : PrimeValue := ⟨287281, pr287281⟩
private theorem pr287291 : PrimeCertificate 287291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv28729]) (by decide +kernel)
def pv287291 : PrimeValue := ⟨287291, pr287291⟩
private theorem pr287297 : PrimeCertificate 287297 :=
  certifyPrime (q := pv3) (ls := [pv2,pv67]) (by decide +kernel)
def pv287297 : PrimeValue := ⟨287297, pr287297⟩
private theorem pr287321 : PrimeCertificate 287321 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv653]) (by decide +kernel)
def pv287321 : PrimeValue := ⟨287321, pr287321⟩
private theorem pr287333 : PrimeCertificate 287333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv2477]) (by decide +kernel)
def pv287333 : PrimeValue := ⟨287333, pr287333⟩
private theorem pr287347 : PrimeCertificate 287347 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv83,pv577]) (by decide +kernel)
def pv287347 : PrimeValue := ⟨287347, pr287347⟩
private theorem pr287383 : PrimeCertificate 287383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv211,pv227]) (by decide +kernel)
def pv287383 : PrimeValue := ⟨287383, pr287383⟩
private theorem pr287437 : PrimeCertificate 287437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv1409]) (by decide +kernel)
def pv287437 : PrimeValue := ⟨287437, pr287437⟩
private theorem pr287449 : PrimeCertificate 287449 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv29,pv59]) (by decide +kernel)
def pv287449 : PrimeValue := ⟨287449, pr287449⟩
private theorem pr287537 : PrimeCertificate 287537 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17971]) (by decide +kernel)
def pv287537 : PrimeValue := ⟨287537, pr287537⟩
private theorem pr287557 : PrimeCertificate 287557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv773]) (by decide +kernel)
def pv287557 : PrimeValue := ⟨287557, pr287557⟩
private theorem pr287597 : PrimeCertificate 287597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71899]) (by decide +kernel)
def pv287597 : PrimeValue := ⟨287597, pr287597⟩
private theorem pr287629 : PrimeCertificate 287629 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv2179]) (by decide +kernel)
def pv287629 : PrimeValue := ⟨287629, pr287629⟩
private theorem pr287689 : PrimeCertificate 287689 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11987]) (by decide +kernel)
def pv287689 : PrimeValue := ⟨287689, pr287689⟩
private theorem pr287701 : PrimeCertificate 287701 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv7,pv137]) (by decide +kernel)
def pv287701 : PrimeValue := ⟨287701, pr287701⟩
private theorem pr287731 : PrimeCertificate 287731 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv23,pv139]) (by decide +kernel)
def pv287731 : PrimeValue := ⟨287731, pr287731⟩
private theorem pr287747 : PrimeCertificate 287747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv143873]) (by decide +kernel)
def pv287747 : PrimeValue := ⟨287747, pr287747⟩
private theorem pr287789 : PrimeCertificate 287789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71947]) (by decide +kernel)
def pv287789 : PrimeValue := ⟨287789, pr287789⟩
private theorem pr287813 : PrimeCertificate 287813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv19,pv541]) (by decide +kernel)
def pv287813 : PrimeValue := ⟨287813, pr287813⟩
private theorem pr287821 : PrimeCertificate 287821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv41]) (by decide +kernel)
def pv287821 : PrimeValue := ⟨287821, pr287821⟩
private theorem pr287849 : PrimeCertificate 287849 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv3271]) (by decide +kernel)
def pv287849 : PrimeValue := ⟨287849, pr287849⟩
private theorem pr287863 : PrimeCertificate 287863 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv47977]) (by decide +kernel)
def pv287863 : PrimeValue := ⟨287863, pr287863⟩
private theorem pr287873 : PrimeCertificate 287873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv173]) (by decide +kernel)
def pv287873 : PrimeValue := ⟨287873, pr287873⟩
private theorem pr287921 : PrimeCertificate 287921 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv59,pv61]) (by decide +kernel)
def pv287921 : PrimeValue := ⟨287921, pr287921⟩
private theorem pr287933 : PrimeCertificate 287933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71983]) (by decide +kernel)
def pv287933 : PrimeValue := ⟨287933, pr287933⟩
private theorem pr287939 : PrimeCertificate 287939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv131,pv157]) (by decide +kernel)
def pv287939 : PrimeValue := ⟨287939, pr287939⟩
private theorem pr287977 : PrimeCertificate 287977 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv71]) (by decide +kernel)
def pv287977 : PrimeValue := ⟨287977, pr287977⟩
private theorem pr288007 : PrimeCertificate 288007 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv2087]) (by decide +kernel)
def pv288007 : PrimeValue := ⟨288007, pr288007⟩
private theorem pr288053 : PrimeCertificate 288053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv31,pv101]) (by decide +kernel)
def pv288053 : PrimeValue := ⟨288053, pr288053⟩
private theorem pr288089 : PrimeCertificate 288089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv36011]) (by decide +kernel)
def pv288089 : PrimeValue := ⟨288089, pr288089⟩
private theorem pr288109 : PrimeCertificate 288109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53,pv151]) (by decide +kernel)
def pv288109 : PrimeValue := ⟨288109, pr288109⟩
private theorem pr288137 : PrimeCertificate 288137 :=
  certifyPrime (q := pv3) (ls := [pv2,pv36017]) (by decide +kernel)
def pv288137 : PrimeValue := ⟨288137, pr288137⟩
private theorem pr288179 : PrimeCertificate 288179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13099]) (by decide +kernel)
def pv288179 : PrimeValue := ⟨288179, pr288179⟩
private theorem pr288181 : PrimeCertificate 288181 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv1601]) (by decide +kernel)
def pv288181 : PrimeValue := ⟨288181, pr288181⟩
private theorem pr288227 : PrimeCertificate 288227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv211,pv683]) (by decide +kernel)
def pv288227 : PrimeValue := ⟨288227, pr288227⟩
private theorem pr288241 : PrimeCertificate 288241 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv1201]) (by decide +kernel)
def pv288241 : PrimeValue := ⟨288241, pr288241⟩
private theorem pr288247 : PrimeCertificate 288247 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv6863]) (by decide +kernel)
def pv288247 : PrimeValue := ⟨288247, pr288247⟩
private theorem pr288257 : PrimeCertificate 288257 :=
  certifyPrime (q := pv3) (ls := [pv2,pv563]) (by decide +kernel)
def pv288257 : PrimeValue := ⟨288257, pr288257⟩
private theorem pr288293 : PrimeCertificate 288293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv72073]) (by decide +kernel)
def pv288293 : PrimeValue := ⟨288293, pr288293⟩
private theorem pr288307 : PrimeCertificate 288307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv281]) (by decide +kernel)
def pv288307 : PrimeValue := ⟨288307, pr288307⟩
private theorem pr288361 : PrimeCertificate 288361 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv89]) (by decide +kernel)
def pv288361 : PrimeValue := ⟨288361, pr288361⟩
private theorem pr288383 : PrimeCertificate 288383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv7589]) (by decide +kernel)
def pv288383 : PrimeValue := ⟨288383, pr288383⟩
private theorem pr288403 : PrimeCertificate 288403 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv71,pv677]) (by decide +kernel)
def pv288403 : PrimeValue := ⟨288403, pr288403⟩
private theorem pr288433 : PrimeCertificate 288433 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2003]) (by decide +kernel)
def pv288433 : PrimeValue := ⟨288433, pr288433⟩
private theorem pr288461 : PrimeCertificate 288461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv14423]) (by decide +kernel)
def pv288461 : PrimeValue := ⟨288461, pr288461⟩
private theorem pr288481 : PrimeCertificate 288481 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv601]) (by decide +kernel)
def pv288481 : PrimeValue := ⟨288481, pr288481⟩
private theorem pr288493 : PrimeCertificate 288493 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv29,pv829]) (by decide +kernel)
def pv288493 : PrimeValue := ⟨288493, pr288493⟩
private theorem pr288499 : PrimeCertificate 288499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv6869]) (by decide +kernel)
def pv288499 : PrimeValue := ⟨288499, pr288499⟩
private theorem pr288539 : PrimeCertificate 288539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89,pv1621]) (by decide +kernel)
def pv288539 : PrimeValue := ⟨288539, pr288539⟩
private theorem pr288559 : PrimeCertificate 288559 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv17,pv23,pv41]) (by decide +kernel)
def pv288559 : PrimeValue := ⟨288559, pr288559⟩
private theorem pr288571 : PrimeCertificate 288571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv9619]) (by decide +kernel)
def pv288571 : PrimeValue := ⟨288571, pr288571⟩
private theorem pr288653 : PrimeCertificate 288653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv61]) (by decide +kernel)
def pv288653 : PrimeValue := ⟨288653, pr288653⟩
private theorem pr288679 : PrimeCertificate 288679 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv13,pv3701]) (by decide +kernel)
def pv288679 : PrimeValue := ⟨288679, pr288679⟩
private theorem pr288689 : PrimeCertificate 288689 :=
  certifyPrime (q := pv3) (ls := [pv2,pv18043]) (by decide +kernel)
def pv288689 : PrimeValue := ⟨288689, pr288689⟩
private theorem pr288697 : PrimeCertificate 288697 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv23,pv523]) (by decide +kernel)
def pv288697 : PrimeValue := ⟨288697, pr288697⟩
private theorem pr288731 : PrimeCertificate 288731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv2221]) (by decide +kernel)
def pv288731 : PrimeValue := ⟨288731, pr288731⟩
private theorem pr288733 : PrimeCertificate 288733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv24061]) (by decide +kernel)
def pv288733 : PrimeValue := ⟨288733, pr288733⟩
private theorem pr288767 : PrimeCertificate 288767 :=
  certifyPrime (q := pv5) (ls := [pv2,pv144383]) (by decide +kernel)
def pv288767 : PrimeValue := ⟨288767, pr288767⟩
private theorem pr288773 : PrimeCertificate 288773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv6563]) (by decide +kernel)
def pv288773 : PrimeValue := ⟨288773, pr288773⟩
private theorem pr288817 : PrimeCertificate 288817 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv547]) (by decide +kernel)
def pv288817 : PrimeValue := ⟨288817, pr288817⟩
private theorem pr288823 : PrimeCertificate 288823 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37,pv1301]) (by decide +kernel)
def pv288823 : PrimeValue := ⟨288823, pr288823⟩
private theorem pr288833 : PrimeCertificate 288833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv4513]) (by decide +kernel)
def pv288833 : PrimeValue := ⟨288833, pr288833⟩
private theorem pr288839 : PrimeCertificate 288839 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv19,pv691]) (by decide +kernel)
def pv288839 : PrimeValue := ⟨288839, pr288839⟩
private theorem pr288853 : PrimeCertificate 288853 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv24071]) (by decide +kernel)
def pv288853 : PrimeValue := ⟨288853, pr288853⟩
private theorem pr288907 : PrimeCertificate 288907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv179,pv269]) (by decide +kernel)
def pv288907 : PrimeValue := ⟨288907, pr288907⟩
private theorem pr288913 : PrimeCertificate 288913 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv13,pv463]) (by decide +kernel)
def pv288913 : PrimeValue := ⟨288913, pr288913⟩
private theorem pr288989 : PrimeCertificate 288989 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv10321]) (by decide +kernel)
def pv288989 : PrimeValue := ⟨288989, pr288989⟩
private theorem pr289021 : PrimeCertificate 289021 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv4817]) (by decide +kernel)
def pv289021 : PrimeValue := ⟨289021, pr289021⟩
private theorem pr289031 : PrimeCertificate 289031 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv4129]) (by decide +kernel)
def pv289031 : PrimeValue := ⟨289031, pr289031⟩
private theorem pr289039 : PrimeCertificate 289039 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv67,pv719]) (by decide +kernel)
def pv289039 : PrimeValue := ⟨289039, pr289039⟩
private theorem pr289103 : PrimeCertificate 289103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv17,pv773]) (by decide +kernel)
def pv289103 : PrimeValue := ⟨289103, pr289103⟩
private theorem pr289109 : PrimeCertificate 289109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv72277]) (by decide +kernel)
def pv289109 : PrimeValue := ⟨289109, pr289109⟩
private theorem pr289127 : PrimeCertificate 289127 :=
  certifyPrime (q := pv5) (ls := [pv2,pv144563]) (by decide +kernel)
def pv289127 : PrimeValue := ⟨289127, pr289127⟩
private theorem pr289129 : PrimeCertificate 289129 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv1721]) (by decide +kernel)
def pv289129 : PrimeValue := ⟨289129, pr289129⟩
private theorem pr289141 : PrimeCertificate 289141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv61,pv79]) (by decide +kernel)
def pv289141 : PrimeValue := ⟨289141, pr289141⟩
private theorem pr289151 : PrimeCertificate 289151 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv5783]) (by decide +kernel)
def pv289151 : PrimeValue := ⟨289151, pr289151⟩
private theorem pr289169 : PrimeCertificate 289169 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv31,pv53]) (by decide +kernel)
def pv289169 : PrimeValue := ⟨289169, pr289169⟩
private theorem pr289181 : PrimeCertificate 289181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv761]) (by decide +kernel)
def pv289181 : PrimeValue := ⟨289181, pr289181⟩
private theorem pr289189 : PrimeCertificate 289189 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv29,pv277]) (by decide +kernel)
def pv289189 : PrimeValue := ⟨289189, pr289189⟩
private theorem pr289193 : PrimeCertificate 289193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv977]) (by decide +kernel)
def pv289193 : PrimeValue := ⟨289193, pr289193⟩
private theorem pr289241 : PrimeCertificate 289241 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv1033]) (by decide +kernel)
def pv289241 : PrimeValue := ⟨289241, pr289241⟩
private theorem pr289249 : PrimeCertificate 289249 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv23,pv131]) (by decide +kernel)
def pv289249 : PrimeValue := ⟨289249, pr289249⟩
private theorem pr289253 : PrimeCertificate 289253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv72313]) (by decide +kernel)
def pv289253 : PrimeValue := ⟨289253, pr289253⟩
private theorem pr289283 : PrimeCertificate 289283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv20663]) (by decide +kernel)
def pv289283 : PrimeValue := ⟨289283, pr289283⟩
private theorem pr289291 : PrimeCertificate 289291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv9643]) (by decide +kernel)
def pv289291 : PrimeValue := ⟨289291, pr289291⟩
private theorem pr289297 : PrimeCertificate 289297 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv41]) (by decide +kernel)
def pv289297 : PrimeValue := ⟨289297, pr289297⟩
private theorem pr289309 : PrimeCertificate 289309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv24109]) (by decide +kernel)
def pv289309 : PrimeValue := ⟨289309, pr289309⟩
private theorem pr289343 : PrimeCertificate 289343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv144671]) (by decide +kernel)
def pv289343 : PrimeValue := ⟨289343, pr289343⟩
private theorem pr289381 : PrimeCertificate 289381 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv7,pv13,pv53]) (by decide +kernel)
def pv289381 : PrimeValue := ⟨289381, pr289381⟩
private theorem pr289397 : PrimeCertificate 289397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71,pv1019]) (by decide +kernel)
def pv289397 : PrimeValue := ⟨289397, pr289397⟩
private theorem pr289417 : PrimeCertificate 289417 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv31,pv389]) (by decide +kernel)
def pv289417 : PrimeValue := ⟨289417, pr289417⟩
private theorem pr289439 : PrimeCertificate 289439 :=
  certifyPrime (q := pv13) (ls := [pv2,pv144719]) (by decide +kernel)
def pv289439 : PrimeValue := ⟨289439, pr289439⟩
private theorem pr289463 : PrimeCertificate 289463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv144731]) (by decide +kernel)
def pv289463 : PrimeValue := ⟨289463, pr289463⟩
private theorem pr289511 : PrimeCertificate 289511 :=
  certifyPrime (q := pv31) (ls := [pv2,pv5,pv13,pv17,pv131]) (by decide +kernel)
def pv289511 : PrimeValue := ⟨289511, pr289511⟩
private theorem pr289543 : PrimeCertificate 289543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv41,pv107]) (by decide +kernel)
def pv289543 : PrimeValue := ⟨289543, pr289543⟩
private theorem pr289559 : PrimeCertificate 289559 :=
  certifyPrime (q := pv7) (ls := [pv2,pv144779]) (by decide +kernel)
def pv289559 : PrimeValue := ⟨289559, pr289559⟩
private theorem pr289573 : PrimeCertificate 289573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv59,pv409]) (by decide +kernel)
def pv289573 : PrimeValue := ⟨289573, pr289573⟩
private theorem pr289577 : PrimeCertificate 289577 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv5171]) (by decide +kernel)
def pv289577 : PrimeValue := ⟨289577, pr289577⟩
private theorem pr289589 : PrimeCertificate 289589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv5569]) (by decide +kernel)
def pv289589 : PrimeValue := ⟨289589, pr289589⟩
private theorem pr289603 : PrimeCertificate 289603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv173]) (by decide +kernel)
def pv289603 : PrimeValue := ⟨289603, pr289603⟩
private theorem pr289637 : PrimeCertificate 289637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv37,pv103]) (by decide +kernel)
def pv289637 : PrimeValue := ⟨289637, pr289637⟩
private theorem pr289643 : PrimeCertificate 289643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv97,pv1493]) (by decide +kernel)
def pv289643 : PrimeValue := ⟨289643, pr289643⟩
private theorem pr289657 : PrimeCertificate 289657 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv149]) (by decide +kernel)
def pv289657 : PrimeValue := ⟨289657, pr289657⟩
private theorem pr289669 : PrimeCertificate 289669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv101,pv239]) (by decide +kernel)
def pv289669 : PrimeValue := ⟨289669, pr289669⟩
private theorem pr289717 : PrimeCertificate 289717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv3449]) (by decide +kernel)
def pv289717 : PrimeValue := ⟨289717, pr289717⟩
private theorem pr289721 : PrimeCertificate 289721 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7243]) (by decide +kernel)
def pv289721 : PrimeValue := ⟨289721, pr289721⟩
private theorem pr289763 : PrimeCertificate 289763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13171]) (by decide +kernel)
def pv289763 : PrimeValue := ⟨289763, pr289763⟩
private theorem pr289771 : PrimeCertificate 289771 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv13,pv743]) (by decide +kernel)
def pv289771 : PrimeValue := ⟨289771, pr289771⟩
private theorem pr289847 : PrimeCertificate 289847 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv6301]) (by decide +kernel)
def pv289847 : PrimeValue := ⟨289847, pr289847⟩
private theorem pr289853 : PrimeCertificate 289853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv233,pv311]) (by decide +kernel)
def pv289853 : PrimeValue := ⟨289853, pr289853⟩
private theorem pr289859 : PrimeCertificate 289859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv3917]) (by decide +kernel)
def pv289859 : PrimeValue := ⟨289859, pr289859⟩
private theorem pr289889 : PrimeCertificate 289889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv9059]) (by decide +kernel)
def pv289889 : PrimeValue := ⟨289889, pr289889⟩
private theorem pr289897 : PrimeCertificate 289897 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv47,pv257]) (by decide +kernel)
def pv289897 : PrimeValue := ⟨289897, pr289897⟩
private theorem pr289951 : PrimeCertificate 289951 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv1933]) (by decide +kernel)
def pv289951 : PrimeValue := ⟨289951, pr289951⟩
private theorem pr289973 : PrimeCertificate 289973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv72493]) (by decide +kernel)
def pv289973 : PrimeValue := ⟨289973, pr289973⟩
private theorem pr289999 : PrimeCertificate 289999 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv16111]) (by decide +kernel)
def pv289999 : PrimeValue := ⟨289999, pr289999⟩
private theorem pr290011 : PrimeCertificate 290011 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv1381]) (by decide +kernel)
def pv290011 : PrimeValue := ⟨290011, pr290011⟩
private theorem pr290021 : PrimeCertificate 290021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv853]) (by decide +kernel)
def pv290021 : PrimeValue := ⟨290021, pr290021⟩
private theorem pr290033 : PrimeCertificate 290033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv18127]) (by decide +kernel)
def pv290033 : PrimeValue := ⟨290033, pr290033⟩
private theorem pr290039 : PrimeCertificate 290039 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv20717]) (by decide +kernel)
def pv290039 : PrimeValue := ⟨290039, pr290039⟩
private theorem pr290041 : PrimeCertificate 290041 :=
  certifyPrime (q := pv103) (ls := [pv2,pv3,pv5,pv2417]) (by decide +kernel)
def pv290041 : PrimeValue := ⟨290041, pr290041⟩
private theorem pr290047 : PrimeCertificate 290047 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv48341]) (by decide +kernel)
def pv290047 : PrimeValue := ⟨290047, pr290047⟩
private theorem pr290083 : PrimeCertificate 290083 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13,pv3719]) (by decide +kernel)
def pv290083 : PrimeValue := ⟨290083, pr290083⟩
private theorem pr290107 : PrimeCertificate 290107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv71,pv227]) (by decide +kernel)
def pv290107 : PrimeValue := ⟨290107, pr290107⟩
private theorem pr290119 : PrimeCertificate 290119 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv48353]) (by decide +kernel)
def pv290119 : PrimeValue := ⟨290119, pr290119⟩
private theorem pr290183 : PrimeCertificate 290183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv145091]) (by decide +kernel)
def pv290183 : PrimeValue := ⟨290183, pr290183⟩
private theorem pr290189 : PrimeCertificate 290189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv72547]) (by decide +kernel)
def pv290189 : PrimeValue := ⟨290189, pr290189⟩
private theorem pr290209 : PrimeCertificate 290209 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv3023]) (by decide +kernel)
def pv290209 : PrimeValue := ⟨290209, pr290209⟩
private theorem pr290243 : PrimeCertificate 290243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv145121]) (by decide +kernel)
def pv290243 : PrimeValue := ⟨290243, pr290243⟩
private theorem pr290249 : PrimeCertificate 290249 :=
  certifyPrime (q := pv13) (ls := [pv2,pv7,pv71,pv73]) (by decide +kernel)
def pv290249 : PrimeValue := ⟨290249, pr290249⟩
private theorem pr290317 : PrimeCertificate 290317 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv1861]) (by decide +kernel)
def pv290317 : PrimeValue := ⟨290317, pr290317⟩
private theorem pr290359 : PrimeCertificate 290359 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv19,pv283]) (by decide +kernel)
def pv290359 : PrimeValue := ⟨290359, pr290359⟩
private theorem pr290369 : PrimeCertificate 290369 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv349]) (by decide +kernel)
def pv290369 : PrimeValue := ⟨290369, pr290369⟩
private theorem pr290393 : PrimeCertificate 290393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv36299]) (by decide +kernel)
def pv290393 : PrimeValue := ⟨290393, pr290393⟩
private theorem pr290429 : PrimeCertificate 290429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv4271]) (by decide +kernel)
def pv290429 : PrimeValue := ⟨290429, pr290429⟩
private theorem pr290441 : PrimeCertificate 290441 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv53,pv137]) (by decide +kernel)
def pv290441 : PrimeValue := ⟨290441, pr290441⟩
private theorem pr290443 : PrimeCertificate 290443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv48407]) (by decide +kernel)
def pv290443 : PrimeValue := ⟨290443, pr290443⟩
private theorem pr290473 : PrimeCertificate 290473 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv19]) (by decide +kernel)
def pv290473 : PrimeValue := ⟨290473, pr290473⟩
private theorem pr290509 : PrimeCertificate 290509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv563]) (by decide +kernel)
def pv290509 : PrimeValue := ⟨290509, pr290509⟩
private theorem pr290557 : PrimeCertificate 290557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1153]) (by decide +kernel)
def pv290557 : PrimeValue := ⟨290557, pr290557⟩
private theorem pr290593 : PrimeCertificate 290593 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1009]) (by decide +kernel)
def pv290593 : PrimeValue := ⟨290593, pr290593⟩
private theorem pr290621 : PrimeCertificate 290621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv1321]) (by decide +kernel)
def pv290621 : PrimeValue := ⟨290621, pr290621⟩
private theorem pr290623 : PrimeCertificate 290623 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv48437]) (by decide +kernel)
def pv290623 : PrimeValue := ⟨290623, pr290623⟩
private theorem pr290671 : PrimeCertificate 290671 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv9689]) (by decide +kernel)
def pv290671 : PrimeValue := ⟨290671, pr290671⟩
private theorem pr290677 : PrimeCertificate 290677 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv24223]) (by decide +kernel)
def pv290677 : PrimeValue := ⟨290677, pr290677⟩
private theorem pr290701 : PrimeCertificate 290701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv19]) (by decide +kernel)
def pv290701 : PrimeValue := ⟨290701, pr290701⟩
private theorem pr290707 : PrimeCertificate 290707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv3727]) (by decide +kernel)
def pv290707 : PrimeValue := ⟨290707, pr290707⟩
private theorem pr290711 : PrimeCertificate 290711 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv4153]) (by decide +kernel)
def pv290711 : PrimeValue := ⟨290711, pr290711⟩
private theorem pr290737 : PrimeCertificate 290737 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv673]) (by decide +kernel)
def pv290737 : PrimeValue := ⟨290737, pr290737⟩
private theorem pr290767 : PrimeCertificate 290767 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv23,pv43]) (by decide +kernel)
def pv290767 : PrimeValue := ⟨290767, pr290767⟩
private theorem pr290803 : PrimeCertificate 290803 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv2851]) (by decide +kernel)
def pv290803 : PrimeValue := ⟨290803, pr290803⟩
private theorem pr290821 : PrimeCertificate 290821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv37,pv131]) (by decide +kernel)
def pv290821 : PrimeValue := ⟨290821, pr290821⟩
private theorem pr290827 : PrimeCertificate 290827 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv107,pv151]) (by decide +kernel)
def pv290827 : PrimeValue := ⟨290827, pr290827⟩
private theorem pr290861 : PrimeCertificate 290861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv14543]) (by decide +kernel)
def pv290861 : PrimeValue := ⟨290861, pr290861⟩
private theorem pr290879 : PrimeCertificate 290879 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv79,pv263]) (by decide +kernel)
def pv290879 : PrimeValue := ⟨290879, pr290879⟩
private theorem pr290959 : PrimeCertificate 290959 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv71,pv683]) (by decide +kernel)
def pv290959 : PrimeValue := ⟨290959, pr290959⟩
private theorem pr290987 : PrimeCertificate 290987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv173]) (by decide +kernel)
def pv290987 : PrimeValue := ⟨290987, pr290987⟩
private theorem pr290999 : PrimeCertificate 290999 :=
  certifyPrime (q := pv7) (ls := [pv2,pv83,pv1753]) (by decide +kernel)
def pv290999 : PrimeValue := ⟨290999, pr290999⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
