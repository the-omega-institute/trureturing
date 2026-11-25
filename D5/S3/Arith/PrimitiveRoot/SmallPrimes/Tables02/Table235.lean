/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table235
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table235.pv1192417
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table012
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table026
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table065
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table066

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr1192417 : PrimeCertificate 1192417 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv12421]) (by decide +kernel)
def pv1192417 : PrimeValue := ⟨1192417, pr1192417⟩
private theorem pr1192423 : PrimeCertificate 1192423 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv29,pv89]) (by decide +kernel)
def pv1192423 : PrimeValue := ⟨1192423, pr1192423⟩
private theorem pr1192579 : PrimeCertificate 1192579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv4229]) (by decide +kernel)
def pv1192579 : PrimeValue := ⟨1192579, pr1192579⟩
private theorem pr1192897 : PrimeCertificate 1192897 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv109]) (by decide +kernel)
def pv1192897 : PrimeValue := ⟨1192897, pr1192897⟩
private theorem pr1192927 : PrimeCertificate 1192927 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv28403]) (by decide +kernel)
def pv1192927 : PrimeValue := ⟨1192927, pr1192927⟩
private theorem pr1193209 : PrimeCertificate 1193209 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv83,pv599]) (by decide +kernel)
def pv1193209 : PrimeValue := ⟨1193209, pr1193209⟩
private theorem pr1193443 : PrimeCertificate 1193443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv443,pv449]) (by decide +kernel)
def pv1193443 : PrimeValue := ⟨1193443, pr1193443⟩
private theorem pr1193653 : PrimeCertificate 1193653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv71,pv467]) (by decide +kernel)
def pv1193653 : PrimeValue := ⟨1193653, pr1193653⟩
private theorem pr1193683 : PrimeCertificate 1193683 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv97,pv293]) (by decide +kernel)
def pv1193683 : PrimeValue := ⟨1193683, pr1193683⟩
private theorem pr1193707 : PrimeCertificate 1193707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv47,pv83]) (by decide +kernel)
def pv1193707 : PrimeValue := ⟨1193707, pr1193707⟩
private theorem pr1193737 : PrimeCertificate 1193737 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv49739]) (by decide +kernel)
def pv1193737 : PrimeValue := ⟨1193737, pr1193737⟩
private theorem pr1193839 : PrimeCertificate 1193839 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv41,pv211]) (by decide +kernel)
def pv1193839 : PrimeValue := ⟨1193839, pr1193839⟩
private theorem pr1193887 : PrimeCertificate 1193887 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv22109]) (by decide +kernel)
def pv1193887 : PrimeValue := ⟨1193887, pr1193887⟩
private theorem pr1194379 : PrimeCertificate 1194379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv10477]) (by decide +kernel)
def pv1194379 : PrimeValue := ⟨1194379, pr1194379⟩
private theorem pr1194733 : PrimeCertificate 1194733 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv11,pv431]) (by decide +kernel)
def pv1194733 : PrimeValue := ⟨1194733, pr1194733⟩
private theorem pr1194757 : PrimeCertificate 1194757 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv99563]) (by decide +kernel)
def pv1194757 : PrimeValue := ⟨1194757, pr1194757⟩
private theorem pr1194889 : PrimeCertificate 1194889 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv49787]) (by decide +kernel)
def pv1194889 : PrimeValue := ⟨1194889, pr1194889⟩
private theorem pr1194997 : PrimeCertificate 1194997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv823]) (by decide +kernel)
def pv1194997 : PrimeValue := ⟨1194997, pr1194997⟩
private theorem pr1195237 : PrimeCertificate 1195237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv31]) (by decide +kernel)
def pv1195237 : PrimeValue := ⟨1195237, pr1195237⟩
private theorem pr1195459 : PrimeCertificate 1195459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv59,pv307]) (by decide +kernel)
def pv1195459 : PrimeValue := ⟨1195459, pr1195459⟩
private theorem pr1195567 : PrimeCertificate 1195567 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv199261]) (by decide +kernel)
def pv1195567 : PrimeValue := ⟨1195567, pr1195567⟩
private theorem pr1195669 : PrimeCertificate 1195669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11071]) (by decide +kernel)
def pv1195669 : PrimeValue := ⟨1195669, pr1195669⟩
private theorem pr1195723 : PrimeCertificate 1195723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv61]) (by decide +kernel)
def pv1195723 : PrimeValue := ⟨1195723, pr1195723⟩
private theorem pr1195837 : PrimeCertificate 1195837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv227,pv439]) (by decide +kernel)
def pv1195837 : PrimeValue := ⟨1195837, pr1195837⟩
private theorem pr1195897 : PrimeCertificate 1195897 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv3833]) (by decide +kernel)
def pv1195897 : PrimeValue := ⟨1195897, pr1195897⟩
private theorem pr1196059 : PrimeCertificate 1196059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv199343]) (by decide +kernel)
def pv1196059 : PrimeValue := ⟨1196059, pr1196059⟩
private theorem pr1196227 : PrimeCertificate 1196227 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv66457]) (by decide +kernel)
def pv1196227 : PrimeValue := ⟨1196227, pr1196227⟩
private theorem pr1196323 : PrimeCertificate 1196323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv8669]) (by decide +kernel)
def pv1196323 : PrimeValue := ⟨1196323, pr1196323⟩
private theorem pr1196509 : PrimeCertificate 1196509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv99709]) (by decide +kernel)
def pv1196509 : PrimeValue := ⟨1196509, pr1196509⟩
private theorem pr1196773 : PrimeCertificate 1196773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv29,pv181]) (by decide +kernel)
def pv1196773 : PrimeValue := ⟨1196773, pr1196773⟩
private theorem pr1196869 : PrimeCertificate 1196869 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv17,pv5867]) (by decide +kernel)
def pv1196869 : PrimeValue := ⟨1196869, pr1196869⟩
private theorem pr1197409 : PrimeCertificate 1197409 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv12473]) (by decide +kernel)
def pv1197409 : PrimeValue := ⟨1197409, pr1197409⟩
private theorem pr1197577 : PrimeCertificate 1197577 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv16633]) (by decide +kernel)
def pv1197577 : PrimeValue := ⟨1197577, pr1197577⟩
private theorem pr1197799 : PrimeCertificate 1197799 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv19,pv79]) (by decide +kernel)
def pv1197799 : PrimeValue := ⟨1197799, pr1197799⟩
private theorem pr1198033 : PrimeCertificate 1198033 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv2269]) (by decide +kernel)
def pv1198033 : PrimeValue := ⟨1198033, pr1198033⟩
private theorem pr1198537 : PrimeCertificate 1198537 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv49939]) (by decide +kernel)
def pv1198537 : PrimeValue := ⟨1198537, pr1198537⟩
private theorem pr1198609 : PrimeCertificate 1198609 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv24971]) (by decide +kernel)
def pv1198609 : PrimeValue := ⟨1198609, pr1198609⟩
private theorem pr1198903 : PrimeCertificate 1198903 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv211,pv947]) (by decide +kernel)
def pv1198903 : PrimeValue := ⟨1198903, pr1198903⟩
private theorem pr1198927 : PrimeCertificate 1198927 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv43,pv1549]) (by decide +kernel)
def pv1198927 : PrimeValue := ⟨1198927, pr1198927⟩
private theorem pr1198999 : PrimeCertificate 1198999 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv59,pv1129]) (by decide +kernel)
def pv1198999 : PrimeValue := ⟨1198999, pr1198999⟩
private theorem pr1199089 : PrimeCertificate 1199089 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv757]) (by decide +kernel)
def pv1199089 : PrimeValue := ⟨1199089, pr1199089⟩
private theorem pr1199557 : PrimeCertificate 1199557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv383]) (by decide +kernel)
def pv1199557 : PrimeValue := ⟨1199557, pr1199557⟩
private theorem pr1199587 : PrimeCertificate 1199587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv199931]) (by decide +kernel)
def pv1199587 : PrimeValue := ⟨1199587, pr1199587⟩
private theorem pr1199593 : PrimeCertificate 1199593 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv16661]) (by decide +kernel)
def pv1199593 : PrimeValue := ⟨1199593, pr1199593⟩
private theorem pr1199683 : PrimeCertificate 1199683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv73,pv83]) (by decide +kernel)
def pv1199683 : PrimeValue := ⟨1199683, pr1199683⟩
private theorem pr1199719 : PrimeCertificate 1199719 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13,pv1709]) (by decide +kernel)
def pv1199719 : PrimeValue := ⟨1199719, pr1199719⟩
private theorem pr1199857 : PrimeCertificate 1199857 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv3571]) (by decide +kernel)
def pv1199857 : PrimeValue := ⟨1199857, pr1199857⟩
private theorem pr1199893 : PrimeCertificate 1199893 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv99991]) (by decide +kernel)
def pv1199893 : PrimeValue := ⟨1199893, pr1199893⟩
private theorem pr1199923 : PrimeCertificate 1199923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv227,pv881]) (by decide +kernel)
def pv1199923 : PrimeValue := ⟨1199923, pr1199923⟩
private theorem pr1200109 : PrimeCertificate 1200109 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv13,pv157]) (by decide +kernel)
def pv1200109 : PrimeValue := ⟨1200109, pr1200109⟩
private theorem pr1200139 : PrimeCertificate 1200139 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv200023]) (by decide +kernel)
def pv1200139 : PrimeValue := ⟨1200139, pr1200139⟩
private theorem pr1200313 : PrimeCertificate 1200313 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv5557]) (by decide +kernel)
def pv1200313 : PrimeValue := ⟨1200313, pr1200313⟩
private theorem pr1200403 : PrimeCertificate 1200403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1361]) (by decide +kernel)
def pv1200403 : PrimeValue := ⟨1200403, pr1200403⟩
private theorem pr1200583 : PrimeCertificate 1200583 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7411]) (by decide +kernel)
def pv1200583 : PrimeValue := ⟨1200583, pr1200583⟩
private theorem pr1200937 : PrimeCertificate 1200937 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv4549]) (by decide +kernel)
def pv1200937 : PrimeValue := ⟨1200937, pr1200937⟩
private theorem pr1200949 : PrimeCertificate 1200949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv29]) (by decide +kernel)
def pv1200949 : PrimeValue := ⟨1200949, pr1200949⟩
private theorem pr1201027 : PrimeCertificate 1201027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv200171]) (by decide +kernel)
def pv1201027 : PrimeValue := ⟨1201027, pr1201027⟩
private theorem pr1201183 : PrimeCertificate 1201183 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv107,pv1871]) (by decide +kernel)
def pv1201183 : PrimeValue := ⟨1201183, pr1201183⟩
private theorem pr1201729 : PrimeCertificate 1201729 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv11,pv569]) (by decide +kernel)
def pv1201729 : PrimeValue := ⟨1201729, pr1201729⟩
private theorem pr1201873 : PrimeCertificate 1201873 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv73]) (by decide +kernel)
def pv1201873 : PrimeValue := ⟨1201873, pr1201873⟩
private theorem pr1201939 : PrimeCertificate 1201939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv200323]) (by decide +kernel)
def pv1201939 : PrimeValue := ⟨1201939, pr1201939⟩
private theorem pr1201969 : PrimeCertificate 1201969 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv17,pv491]) (by decide +kernel)
def pv1201969 : PrimeValue := ⟨1201969, pr1201969⟩
private theorem pr1202629 : PrimeCertificate 1202629 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv7,pv103,pv139]) (by decide +kernel)
def pv1202629 : PrimeValue := ⟨1202629, pr1202629⟩
private theorem pr1202743 : PrimeCertificate 1202743 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv22273]) (by decide +kernel)
def pv1202743 : PrimeValue := ⟨1202743, pr1202743⟩
private theorem pr1202863 : PrimeCertificate 1202863 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv31,pv223]) (by decide +kernel)
def pv1202863 : PrimeValue := ⟨1202863, pr1202863⟩
private theorem pr1202977 : PrimeCertificate 1202977 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4177]) (by decide +kernel)
def pv1202977 : PrimeValue := ⟨1202977, pr1202977⟩
private theorem pr1203019 : PrimeCertificate 1203019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv5419]) (by decide +kernel)
def pv1203019 : PrimeValue := ⟨1203019, pr1203019⟩
private theorem pr1203343 : PrimeCertificate 1203343 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv4093]) (by decide +kernel)
def pv1203343 : PrimeValue := ⟨1203343, pr1203343⟩
private theorem pr1203457 : PrimeCertificate 1203457 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv1567]) (by decide +kernel)
def pv1203457 : PrimeValue := ⟨1203457, pr1203457⟩
private theorem pr1203919 : PrimeCertificate 1203919 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv163,pv1231]) (by decide +kernel)
def pv1203919 : PrimeValue := ⟨1203919, pr1203919⟩
private theorem pr1204447 : PrimeCertificate 1204447 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv191,pv1051]) (by decide +kernel)
def pv1204447 : PrimeValue := ⟨1204447, pr1204447⟩
private theorem pr1204669 : PrimeCertificate 1204669 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv109,pv307]) (by decide +kernel)
def pv1204669 : PrimeValue := ⟨1204669, pr1204669⟩
private theorem pr1204699 : PrimeCertificate 1204699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv18253]) (by decide +kernel)
def pv1204699 : PrimeValue := ⟨1204699, pr1204699⟩
private theorem pr1205257 : PrimeCertificate 1205257 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv13,pv3863]) (by decide +kernel)
def pv1205257 : PrimeValue := ⟨1205257, pr1205257⟩
private theorem pr1205437 : PrimeCertificate 1205437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv19,pv311]) (by decide +kernel)
def pv1205437 : PrimeValue := ⟨1205437, pr1205437⟩
private theorem pr1205557 : PrimeCertificate 1205557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv9133]) (by decide +kernel)
def pv1205557 : PrimeValue := ⟨1205557, pr1205557⟩
private theorem pr1205647 : PrimeCertificate 1205647 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv29,pv41]) (by decide +kernel)
def pv1205647 : PrimeValue := ⟨1205647, pr1205647⟩
private theorem pr1205749 : PrimeCertificate 1205749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv33493]) (by decide +kernel)
def pv1205749 : PrimeValue := ⟨1205749, pr1205749⟩
private theorem pr1205977 : PrimeCertificate 1205977 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv109,pv461]) (by decide +kernel)
def pv1205977 : PrimeValue := ⟨1205977, pr1205977⟩
private theorem pr1206157 : PrimeCertificate 1206157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv83,pv173]) (by decide +kernel)
def pv1206157 : PrimeValue := ⟨1206157, pr1206157⟩
private theorem pr1206223 : PrimeCertificate 1206223 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv201037]) (by decide +kernel)
def pv1206223 : PrimeValue := ⟨1206223, pr1206223⟩
private theorem pr1206277 : PrimeCertificate 1206277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv100523]) (by decide +kernel)
def pv1206277 : PrimeValue := ⟨1206277, pr1206277⟩
private theorem pr1206577 : PrimeCertificate 1206577 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv7,pv19]) (by decide +kernel)
def pv1206577 : PrimeValue := ⟨1206577, pr1206577⟩
private theorem pr1206703 : PrimeCertificate 1206703 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv61,pv157]) (by decide +kernel)
def pv1206703 : PrimeValue := ⟨1206703, pr1206703⟩
private theorem pr1207033 : PrimeCertificate 1207033 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv2647]) (by decide +kernel)
def pv1207033 : PrimeValue := ⟨1207033, pr1207033⟩
private theorem pr1207117 : PrimeCertificate 1207117 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11177]) (by decide +kernel)
def pv1207117 : PrimeValue := ⟨1207117, pr1207117⟩
private theorem pr1207249 : PrimeCertificate 1207249 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv3593]) (by decide +kernel)
def pv1207249 : PrimeValue := ⟨1207249, pr1207249⟩
private theorem pr1207363 : PrimeCertificate 1207363 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv23,pv673]) (by decide +kernel)
def pv1207363 : PrimeValue := ⟨1207363, pr1207363⟩
private theorem pr1207387 : PrimeCertificate 1207387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv257]) (by decide +kernel)
def pv1207387 : PrimeValue := ⟨1207387, pr1207387⟩
private theorem pr1207447 : PrimeCertificate 1207447 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv53,pv3797]) (by decide +kernel)
def pv1207447 : PrimeValue := ⟨1207447, pr1207447⟩
private theorem pr1207537 : PrimeCertificate 1207537 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv2287]) (by decide +kernel)
def pv1207537 : PrimeValue := ⟨1207537, pr1207537⟩
private theorem pr1207699 : PrimeCertificate 1207699 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31,pv43,pv151]) (by decide +kernel)
def pv1207699 : PrimeValue := ⟨1207699, pr1207699⟩
private theorem pr1207903 : PrimeCertificate 1207903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv37,pv5441]) (by decide +kernel)
def pv1207903 : PrimeValue := ⟨1207903, pr1207903⟩
private theorem pr1207909 : PrimeCertificate 1207909 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv13,pv29,pv89]) (by decide +kernel)
def pv1207909 : PrimeValue := ⟨1207909, pr1207909⟩
private theorem pr1207933 : PrimeCertificate 1207933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv9151]) (by decide +kernel)
def pv1207933 : PrimeValue := ⟨1207933, pr1207933⟩
private theorem pr1207957 : PrimeCertificate 1207957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv2341]) (by decide +kernel)
def pv1207957 : PrimeValue := ⟨1207957, pr1207957⟩
private theorem pr1208209 : PrimeCertificate 1208209 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv25171]) (by decide +kernel)
def pv1208209 : PrimeValue := ⟨1208209, pr1208209⟩
private theorem pr1208707 : PrimeCertificate 1208707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv201451]) (by decide +kernel)
def pv1208707 : PrimeValue := ⟨1208707, pr1208707⟩
private theorem pr1208833 : PrimeCertificate 1208833 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv787]) (by decide +kernel)
def pv1208833 : PrimeValue := ⟨1208833, pr1208833⟩
private theorem pr1209379 : PrimeCertificate 1209379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv353,pv571]) (by decide +kernel)
def pv1209379 : PrimeValue := ⟨1209379, pr1209379⟩
private theorem pr1209427 : PrimeCertificate 1209427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv103]) (by decide +kernel)
def pv1209427 : PrimeValue := ⟨1209427, pr1209427⟩
private theorem pr1209463 : PrimeCertificate 1209463 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv201577]) (by decide +kernel)
def pv1209463 : PrimeValue := ⟨1209463, pr1209463⟩
private theorem pr1209583 : PrimeCertificate 1209583 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv41,pv149]) (by decide +kernel)
def pv1209583 : PrimeValue := ⟨1209583, pr1209583⟩
private theorem pr1209697 : PrimeCertificate 1209697 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv12601]) (by decide +kernel)
def pv1209697 : PrimeValue := ⟨1209697, pr1209697⟩
private theorem pr1209973 : PrimeCertificate 1209973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv59,pv1709]) (by decide +kernel)
def pv1209973 : PrimeValue := ⟨1209973, pr1209973⟩
private theorem pr1210477 : PrimeCertificate 1210477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv149,pv677]) (by decide +kernel)
def pv1210477 : PrimeValue := ⟨1210477, pr1210477⟩
private theorem pr1210483 : PrimeCertificate 1210483 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv739]) (by decide +kernel)
def pv1210483 : PrimeValue := ⟨1210483, pr1210483⟩
private theorem pr1210549 : PrimeCertificate 1210549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv281,pv359]) (by decide +kernel)
def pv1210549 : PrimeValue := ⟨1210549, pr1210549⟩
private theorem pr1210717 : PrimeCertificate 1210717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv199]) (by decide +kernel)
def pv1210717 : PrimeValue := ⟨1210717, pr1210717⟩
private theorem pr1210819 : PrimeCertificate 1210819 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv127,pv227]) (by decide +kernel)
def pv1210819 : PrimeValue := ⟨1210819, pr1210819⟩
private theorem pr1210939 : PrimeCertificate 1210939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv201823]) (by decide +kernel)
def pv1210939 : PrimeValue := ⟨1210939, pr1210939⟩
private theorem pr1211179 : PrimeCertificate 1211179 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv337,pv599]) (by decide +kernel)
def pv1211179 : PrimeValue := ⟨1211179, pr1211179⟩
private theorem pr1211227 : PrimeCertificate 1211227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv67,pv131]) (by decide +kernel)
def pv1211227 : PrimeValue := ⟨1211227, pr1211227⟩
private theorem pr1211797 : PrimeCertificate 1211797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv821]) (by decide +kernel)
def pv1211797 : PrimeValue := ⟨1211797, pr1211797⟩
private theorem pr1211827 : PrimeCertificate 1211827 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv43,pv61]) (by decide +kernel)
def pv1211827 : PrimeValue := ⟨1211827, pr1211827⟩
private theorem pr1211983 : PrimeCertificate 1211983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv201997]) (by decide +kernel)
def pv1211983 : PrimeValue := ⟨1211983, pr1211983⟩
private theorem pr1212103 : PrimeCertificate 1212103 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv67339]) (by decide +kernel)
def pv1212103 : PrimeValue := ⟨1212103, pr1212103⟩
private theorem pr1212319 : PrimeCertificate 1212319 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv47,pv1433]) (by decide +kernel)
def pv1212319 : PrimeValue := ⟨1212319, pr1212319⟩
private theorem pr1212397 : PrimeCertificate 1212397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv71,pv1423]) (by decide +kernel)
def pv1212397 : PrimeValue := ⟨1212397, pr1212397⟩
private theorem pr1212649 : PrimeCertificate 1212649 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv50527]) (by decide +kernel)
def pv1212649 : PrimeValue := ⟨1212649, pr1212649⟩
private theorem pr1212793 : PrimeCertificate 1212793 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv7219]) (by decide +kernel)
def pv1212793 : PrimeValue := ⟨1212793, pr1212793⟩
private theorem pr1212889 : PrimeCertificate 1212889 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv97,pv521]) (by decide +kernel)
def pv1212889 : PrimeValue := ⟨1212889, pr1212889⟩
private theorem pr1212973 : PrimeCertificate 1212973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv101081]) (by decide +kernel)
def pv1212973 : PrimeValue := ⟨1212973, pr1212973⟩
private theorem pr1213087 : PrimeCertificate 1213087 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv17,pv1699]) (by decide +kernel)
def pv1213087 : PrimeValue := ⟨1213087, pr1213087⟩
private theorem pr1213327 : PrimeCertificate 1213327 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv22469]) (by decide +kernel)
def pv1213327 : PrimeValue := ⟨1213327, pr1213327⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
