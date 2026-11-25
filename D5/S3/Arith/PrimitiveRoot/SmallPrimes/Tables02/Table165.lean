/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table165
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table165.pv211199
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table009
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table015
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table039
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table040
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table041

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr211199 : PrimeCertificate 211199 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv8123]) (by decide +kernel)
def pv211199 : PrimeValue := ⟨211199, pr211199⟩
private theorem pr211291 : PrimeCertificate 211291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7043]) (by decide +kernel)
def pv211291 : PrimeValue := ⟨211291, pr211291⟩
private theorem pr211297 : PrimeCertificate 211297 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv71]) (by decide +kernel)
def pv211297 : PrimeValue := ⟨211297, pr211297⟩
private theorem pr211369 : PrimeCertificate 211369 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv8807]) (by decide +kernel)
def pv211369 : PrimeValue := ⟨211369, pr211369⟩
private theorem pr211639 : PrimeCertificate 211639 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv5039]) (by decide +kernel)
def pv211639 : PrimeValue := ⟨211639, pr211639⟩
private theorem pr211781 : PrimeCertificate 211781 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv10589]) (by decide +kernel)
def pv211781 : PrimeValue := ⟨211781, pr211781⟩
private theorem pr211817 : PrimeCertificate 211817 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv29,pv83]) (by decide +kernel)
def pv211817 : PrimeValue := ⟨211817, pr211817⟩
private theorem pr211859 : PrimeCertificate 211859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv105929]) (by decide +kernel)
def pv211859 : PrimeValue := ⟨211859, pr211859⟩
private theorem pr211933 : PrimeCertificate 211933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv29]) (by decide +kernel)
def pv211933 : PrimeValue := ⟨211933, pr211933⟩
private theorem pr212167 : PrimeCertificate 212167 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv3929]) (by decide +kernel)
def pv212167 : PrimeValue := ⟨212167, pr212167⟩
private theorem pr212239 : PrimeCertificate 212239 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv907]) (by decide +kernel)
def pv212239 : PrimeValue := ⟨212239, pr212239⟩
private theorem pr212437 : PrimeCertificate 212437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv281]) (by decide +kernel)
def pv212437 : PrimeValue := ⟨212437, pr212437⟩
private theorem pr212777 : PrimeCertificate 212777 :=
  certifyPrime (q := pv3) (ls := [pv2,pv26597]) (by decide +kernel)
def pv212777 : PrimeValue := ⟨212777, pr212777⟩
private theorem pr212851 : PrimeCertificate 212851 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv43]) (by decide +kernel)
def pv212851 : PrimeValue := ⟨212851, pr212851⟩
private theorem pr212881 : PrimeCertificate 212881 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv887]) (by decide +kernel)
def pv212881 : PrimeValue := ⟨212881, pr212881⟩
private theorem pr212903 : PrimeCertificate 212903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv106451]) (by decide +kernel)
def pv212903 : PrimeValue := ⟨212903, pr212903⟩
private theorem pr212981 : PrimeCertificate 212981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv463]) (by decide +kernel)
def pv212981 : PrimeValue := ⟨212981, pr212981⟩
private theorem pr213043 : PrimeCertificate 213043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv35507]) (by decide +kernel)
def pv213043 : PrimeValue := ⟨213043, pr213043⟩
private theorem pr213149 : PrimeCertificate 213149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv4099]) (by decide +kernel)
def pv213149 : PrimeValue := ⟨213149, pr213149⟩
private theorem pr213229 : PrimeCertificate 213229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5923]) (by decide +kernel)
def pv213229 : PrimeValue := ⟨213229, pr213229⟩
private theorem pr213383 : PrimeCertificate 213383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv29,pv283]) (by decide +kernel)
def pv213383 : PrimeValue := ⟨213383, pr213383⟩
private theorem pr213391 : PrimeCertificate 213391 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv2371]) (by decide +kernel)
def pv213391 : PrimeValue := ⟨213391, pr213391⟩
private theorem pr213799 : PrimeCertificate 213799 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv2741]) (by decide +kernel)
def pv213799 : PrimeValue := ⟨213799, pr213799⟩
private theorem pr213821 : PrimeCertificate 213821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv10691]) (by decide +kernel)
def pv213821 : PrimeValue := ⟨213821, pr213821⟩
private theorem pr213901 : PrimeCertificate 213901 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv23,pv31]) (by decide +kernel)
def pv213901 : PrimeValue := ⟨213901, pr213901⟩
private theorem pr213949 : PrimeCertificate 213949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv283]) (by decide +kernel)
def pv213949 : PrimeValue := ⟨213949, pr213949⟩
private theorem pr214133 : PrimeCertificate 214133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv47,pv67]) (by decide +kernel)
def pv214133 : PrimeValue := ⟨214133, pr214133⟩
private theorem pr214163 : PrimeCertificate 214163 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv8237]) (by decide +kernel)
def pv214163 : PrimeValue := ⟨214163, pr214163⟩
private theorem pr214469 : PrimeCertificate 214469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53617]) (by decide +kernel)
def pv214469 : PrimeValue := ⟨214469, pr214469⟩
private theorem pr214483 : PrimeCertificate 214483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv35747]) (by decide +kernel)
def pv214483 : PrimeValue := ⟨214483, pr214483⟩
private theorem pr214561 : PrimeCertificate 214561 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv149]) (by decide +kernel)
def pv214561 : PrimeValue := ⟨214561, pr214561⟩
private theorem pr214729 : PrimeCertificate 214729 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv23,pv389]) (by decide +kernel)
def pv214729 : PrimeValue := ⟨214729, pr214729⟩
private theorem pr214763 : PrimeCertificate 214763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv167,pv643]) (by decide +kernel)
def pv214763 : PrimeValue := ⟨214763, pr214763⟩
private theorem pr214853 : PrimeCertificate 214853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv19,pv257]) (by decide +kernel)
def pv214853 : PrimeValue := ⟨214853, pr214853⟩
private theorem pr215051 : PrimeCertificate 215051 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv17,pv23]) (by decide +kernel)
def pv215051 : PrimeValue := ⟨215051, pr215051⟩
private theorem pr215191 : PrimeCertificate 215191 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv797]) (by decide +kernel)
def pv215191 : PrimeValue := ⟨215191, pr215191⟩
private theorem pr215587 : PrimeCertificate 215587 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv29,pv59]) (by decide +kernel)
def pv215587 : PrimeValue := ⟨215587, pr215587⟩
private theorem pr215693 : PrimeCertificate 215693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53923]) (by decide +kernel)
def pv215693 : PrimeValue := ⟨215693, pr215693⟩
private theorem pr215753 : PrimeCertificate 215753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv149,pv181]) (by decide +kernel)
def pv215753 : PrimeValue := ⟨215753, pr215753⟩
private theorem pr215851 : PrimeCertificate 215851 :=
  certifyPrime (q := pv47) (ls := [pv2,pv3,pv5,pv1439]) (by decide +kernel)
def pv215851 : PrimeValue := ⟨215851, pr215851⟩
private theorem pr215899 : PrimeCertificate 215899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv35983]) (by decide +kernel)
def pv215899 : PrimeValue := ⟨215899, pr215899⟩
private theorem pr216317 : PrimeCertificate 216317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv1319]) (by decide +kernel)
def pv216317 : PrimeValue := ⟨216317, pr216317⟩
private theorem pr216607 : PrimeCertificate 216607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv2777]) (by decide +kernel)
def pv216607 : PrimeValue := ⟨216607, pr216607⟩
private theorem pr217169 : PrimeCertificate 217169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv277]) (by decide +kernel)
def pv217169 : PrimeValue := ⟨217169, pr217169⟩
private theorem pr217241 : PrimeCertificate 217241 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv5431]) (by decide +kernel)
def pv217241 : PrimeValue := ⟨217241, pr217241⟩
private theorem pr217307 : PrimeCertificate 217307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv179,pv607]) (by decide +kernel)
def pv217307 : PrimeValue := ⟨217307, pr217307⟩
private theorem pr217309 : PrimeCertificate 217309 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv7,pv13,pv199]) (by decide +kernel)
def pv217309 : PrimeValue := ⟨217309, pr217309⟩
private theorem pr217351 : PrimeCertificate 217351 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv23]) (by decide +kernel)
def pv217351 : PrimeValue := ⟨217351, pr217351⟩
private theorem pr217367 : PrimeCertificate 217367 :=
  certifyPrime (q := pv5) (ls := [pv2,pv251,pv433]) (by decide +kernel)
def pv217367 : PrimeValue := ⟨217367, pr217367⟩
private theorem pr217369 : PrimeCertificate 217369 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv3019]) (by decide +kernel)
def pv217369 : PrimeValue := ⟨217369, pr217369⟩
private theorem pr217409 : PrimeCertificate 217409 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43,pv79]) (by decide +kernel)
def pv217409 : PrimeValue := ⟨217409, pr217409⟩
private theorem pr217517 : PrimeCertificate 217517 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv47,pv89]) (by decide +kernel)
def pv217517 : PrimeValue := ⟨217517, pr217517⟩
private theorem pr217561 : PrimeCertificate 217561 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv7,pv37]) (by decide +kernel)
def pv217561 : PrimeValue := ⟨217561, pr217561⟩
private theorem pr217661 : PrimeCertificate 217661 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv10883]) (by decide +kernel)
def pv217661 : PrimeValue := ⟨217661, pr217661⟩
private theorem pr217727 : PrimeCertificate 217727 :=
  certifyPrime (q := pv5) (ls := [pv2,pv108863]) (by decide +kernel)
def pv217727 : PrimeValue := ⟨217727, pr217727⟩
private theorem pr217733 : PrimeCertificate 217733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv1877]) (by decide +kernel)
def pv217733 : PrimeValue := ⟨217733, pr217733⟩
private theorem pr217771 : PrimeCertificate 217771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv17,pv61]) (by decide +kernel)
def pv217771 : PrimeValue := ⟨217771, pr217771⟩
private theorem pr217829 : PrimeCertificate 217829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv59,pv71]) (by decide +kernel)
def pv217829 : PrimeValue := ⟨217829, pr217829⟩
private theorem pr217901 : PrimeCertificate 217901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv2179]) (by decide +kernel)
def pv217901 : PrimeValue := ⟨217901, pr217901⟩
private theorem pr217907 : PrimeCertificate 217907 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv17,pv29]) (by decide +kernel)
def pv217907 : PrimeValue := ⟨217907, pr217907⟩
private theorem pr217937 : PrimeCertificate 217937 :=
  certifyPrime (q := pv3) (ls := [pv2,pv53,pv257]) (by decide +kernel)
def pv217937 : PrimeValue := ⟨217937, pr217937⟩
private theorem pr218081 : PrimeCertificate 218081 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv29,pv47]) (by decide +kernel)
def pv218081 : PrimeValue := ⟨218081, pr218081⟩
private theorem pr218149 : PrimeCertificate 218149 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv53]) (by decide +kernel)
def pv218149 : PrimeValue := ⟨218149, pr218149⟩
private theorem pr218371 : PrimeCertificate 218371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv29,pv251]) (by decide +kernel)
def pv218371 : PrimeValue := ⟨218371, pr218371⟩
private theorem pr218401 : PrimeCertificate 218401 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv7,pv13]) (by decide +kernel)
def pv218401 : PrimeValue := ⟨218401, pr218401⟩
private theorem pr218627 : PrimeCertificate 218627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv109313]) (by decide +kernel)
def pv218627 : PrimeValue := ⟨218627, pr218627⟩
private theorem pr218651 : PrimeCertificate 218651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv4373]) (by decide +kernel)
def pv218651 : PrimeValue := ⟨218651, pr218651⟩
private theorem pr218677 : PrimeCertificate 218677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv18223]) (by decide +kernel)
def pv218677 : PrimeValue := ⟨218677, pr218677⟩
private theorem pr218711 : PrimeCertificate 218711 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv21871]) (by decide +kernel)
def pv218711 : PrimeValue := ⟨218711, pr218711⟩
private theorem pr218719 : PrimeCertificate 218719 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv29,pv419]) (by decide +kernel)
def pv218719 : PrimeValue := ⟨218719, pr218719⟩
private theorem pr218737 : PrimeCertificate 218737 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv31]) (by decide +kernel)
def pv218737 : PrimeValue := ⟨218737, pr218737⟩
private theorem pr218809 : PrimeCertificate 218809 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv1013]) (by decide +kernel)
def pv218809 : PrimeValue := ⟨218809, pr218809⟩
private theorem pr218941 : PrimeCertificate 218941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv41,pv89]) (by decide +kernel)
def pv218941 : PrimeValue := ⟨218941, pr218941⟩
private theorem pr218987 : PrimeCertificate 218987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv223,pv491]) (by decide +kernel)
def pv218987 : PrimeValue := ⟨218987, pr218987⟩
private theorem pr219041 : PrimeCertificate 219041 :=
  certifyPrime (q := pv41) (ls := [pv2,pv5,pv37]) (by decide +kernel)
def pv219041 : PrimeValue := ⟨219041, pr219041⟩
private theorem pr219217 : PrimeCertificate 219217 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv4567]) (by decide +kernel)
def pv219217 : PrimeValue := ⟨219217, pr219217⟩
private theorem pr219281 : PrimeCertificate 219281 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv2741]) (by decide +kernel)
def pv219281 : PrimeValue := ⟨219281, pr219281⟩
private theorem pr219517 : PrimeCertificate 219517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv1663]) (by decide +kernel)
def pv219517 : PrimeValue := ⟨219517, pr219517⟩
private theorem pr219721 : PrimeCertificate 219721 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv1831]) (by decide +kernel)
def pv219721 : PrimeValue := ⟨219721, pr219721⟩
private theorem pr219727 : PrimeCertificate 219727 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv313]) (by decide +kernel)
def pv219727 : PrimeValue := ⟨219727, pr219727⟩
private theorem pr219787 : PrimeCertificate 219787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv5233]) (by decide +kernel)
def pv219787 : PrimeValue := ⟨219787, pr219787⟩
private theorem pr219809 : PrimeCertificate 219809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv6869]) (by decide +kernel)
def pv219809 : PrimeValue := ⟨219809, pr219809⟩
private theorem pr219823 : PrimeCertificate 219823 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv36637]) (by decide +kernel)
def pv219823 : PrimeValue := ⟨219823, pr219823⟩
private theorem pr219839 : PrimeCertificate 219839 :=
  certifyPrime (q := pv7) (ls := [pv2,pv109919]) (by decide +kernel)
def pv219839 : PrimeValue := ⟨219839, pr219839⟩
private theorem pr219871 : PrimeCertificate 219871 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv349]) (by decide +kernel)
def pv219871 : PrimeValue := ⟨219871, pr219871⟩
private theorem pr219889 : PrimeCertificate 219889 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv509]) (by decide +kernel)
def pv219889 : PrimeValue := ⟨219889, pr219889⟩
private theorem pr219977 : PrimeCertificate 219977 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv887]) (by decide +kernel)
def pv219977 : PrimeValue := ⟨219977, pr219977⟩
private theorem pr220013 : PrimeCertificate 220013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv4231]) (by decide +kernel)
def pv220013 : PrimeValue := ⟨220013, pr220013⟩
private theorem pr220123 : PrimeCertificate 220123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1747]) (by decide +kernel)
def pv220123 : PrimeValue := ⟨220123, pr220123⟩
private theorem pr220141 : PrimeCertificate 220141 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv5,pv1223]) (by decide +kernel)
def pv220141 : PrimeValue := ⟨220141, pr220141⟩
private theorem pr220301 : PrimeCertificate 220301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv2203]) (by decide +kernel)
def pv220301 : PrimeValue := ⟨220301, pr220301⟩
private theorem pr220327 : PrimeCertificate 220327 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv36721]) (by decide +kernel)
def pv220327 : PrimeValue := ⟨220327, pr220327⟩
private theorem pr220537 : PrimeCertificate 220537 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1021]) (by decide +kernel)
def pv220537 : PrimeValue := ⟨220537, pr220537⟩
private theorem pr220573 : PrimeCertificate 220573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv557]) (by decide +kernel)
def pv220573 : PrimeValue := ⟨220573, pr220573⟩
private theorem pr220579 : PrimeCertificate 220579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv97,pv379]) (by decide +kernel)
def pv220579 : PrimeValue := ⟨220579, pr220579⟩
private theorem pr220667 : PrimeCertificate 220667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv5807]) (by decide +kernel)
def pv220667 : PrimeValue := ⟨220667, pr220667⟩
private theorem pr220747 : PrimeCertificate 220747 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv36791]) (by decide +kernel)
def pv220747 : PrimeValue := ⟨220747, pr220747⟩
private theorem pr220859 : PrimeCertificate 220859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv10039]) (by decide +kernel)
def pv220859 : PrimeValue := ⟨220859, pr220859⟩
private theorem pr220861 : PrimeCertificate 220861 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv409]) (by decide +kernel)
def pv220861 : PrimeValue := ⟨220861, pr220861⟩
private theorem pr220873 : PrimeCertificate 220873 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv9203]) (by decide +kernel)
def pv220873 : PrimeValue := ⟨220873, pr220873⟩
private theorem pr220973 : PrimeCertificate 220973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv55243]) (by decide +kernel)
def pv220973 : PrimeValue := ⟨220973, pr220973⟩
private theorem pr221021 : PrimeCertificate 221021 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv43,pv257]) (by decide +kernel)
def pv221021 : PrimeValue := ⟨221021, pr221021⟩
private theorem pr221087 : PrimeCertificate 221087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv110543]) (by decide +kernel)
def pv221087 : PrimeValue := ⟨221087, pr221087⟩
private theorem pr221093 : PrimeCertificate 221093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv1783]) (by decide +kernel)
def pv221093 : PrimeValue := ⟨221093, pr221093⟩
private theorem pr221201 : PrimeCertificate 221201 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv79]) (by decide +kernel)
def pv221201 : PrimeValue := ⟨221201, pr221201⟩
private theorem pr221209 : PrimeCertificate 221209 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv13,pv709]) (by decide +kernel)
def pv221209 : PrimeValue := ⟨221209, pr221209⟩
private theorem pr221281 : PrimeCertificate 221281 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv461]) (by decide +kernel)
def pv221281 : PrimeValue := ⟨221281, pr221281⟩
private theorem pr221539 : PrimeCertificate 221539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv36923]) (by decide +kernel)
def pv221539 : PrimeValue := ⟨221539, pr221539⟩
private theorem pr221653 : PrimeCertificate 221653 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv47,pv131]) (by decide +kernel)
def pv221653 : PrimeValue := ⟨221653, pr221653⟩
private theorem pr221659 : PrimeCertificate 221659 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv36943]) (by decide +kernel)
def pv221659 : PrimeValue := ⟨221659, pr221659⟩
private theorem pr221671 : PrimeCertificate 221671 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv821]) (by decide +kernel)
def pv221671 : PrimeValue := ⟨221671, pr221671⟩
private theorem pr221677 : PrimeCertificate 221677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv29]) (by decide +kernel)
def pv221677 : PrimeValue := ⟨221677, pr221677⟩
private theorem pr221717 : PrimeCertificate 221717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv5039]) (by decide +kernel)
def pv221717 : PrimeValue := ⟨221717, pr221717⟩
private theorem pr221989 : PrimeCertificate 221989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv1423]) (by decide +kernel)
def pv221989 : PrimeValue := ⟨221989, pr221989⟩
private theorem pr222011 : PrimeCertificate 222011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv149]) (by decide +kernel)
def pv222011 : PrimeValue := ⟨222011, pr222011⟩
private theorem pr222029 : PrimeCertificate 222029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv1181]) (by decide +kernel)
def pv222029 : PrimeValue := ⟨222029, pr222029⟩
private theorem pr222107 : PrimeCertificate 222107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv111053]) (by decide +kernel)
def pv222107 : PrimeValue := ⟨222107, pr222107⟩
private theorem pr222109 : PrimeCertificate 222109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv83,pv223]) (by decide +kernel)
def pv222109 : PrimeValue := ⟨222109, pr222109⟩
private theorem pr222323 : PrimeCertificate 222323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89,pv1249]) (by decide +kernel)
def pv222323 : PrimeValue := ⟨222323, pr222323⟩
private theorem pr222587 : PrimeCertificate 222587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv1223]) (by decide +kernel)
def pv222587 : PrimeValue := ⟨222587, pr222587⟩
private theorem pr222647 : PrimeCertificate 222647 :=
  certifyPrime (q := pv5) (ls := [pv2,pv111323]) (by decide +kernel)
def pv222647 : PrimeValue := ⟨222647, pr222647⟩
private theorem pr222799 : PrimeCertificate 222799 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv71,pv523]) (by decide +kernel)
def pv222799 : PrimeValue := ⟨222799, pr222799⟩
private theorem pr222931 : PrimeCertificate 222931 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv2477]) (by decide +kernel)
def pv222931 : PrimeValue := ⟨222931, pr222931⟩
private theorem pr222977 : PrimeCertificate 222977 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv67]) (by decide +kernel)
def pv222977 : PrimeValue := ⟨222977, pr222977⟩
private theorem pr223009 : PrimeCertificate 223009 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23,pv101]) (by decide +kernel)
def pv223009 : PrimeValue := ⟨223009, pr223009⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
