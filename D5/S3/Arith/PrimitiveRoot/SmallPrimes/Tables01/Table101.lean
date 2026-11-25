/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table101
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table101.pv412831
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table012
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table017
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table027
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table067

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr412831 : PrimeCertificate 412831 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv139]) (by decide +kernel)
def pv412831 : PrimeValue := ⟨412831, pr412831⟩
private theorem pr412901 : PrimeCertificate 412901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv4129]) (by decide +kernel)
def pv412901 : PrimeValue := ⟨412901, pr412901⟩
private theorem pr412939 : PrimeCertificate 412939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv2549]) (by decide +kernel)
def pv412939 : PrimeValue := ⟨412939, pr412939⟩
private theorem pr412943 : PrimeCertificate 412943 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv47,pv191]) (by decide +kernel)
def pv412943 : PrimeValue := ⟨412943, pr412943⟩
private theorem pr412967 : PrimeCertificate 412967 :=
  certifyPrime (q := pv5) (ls := [pv2,pv206483]) (by decide +kernel)
def pv412967 : PrimeValue := ⟨412967, pr412967⟩
private theorem pr413009 : PrimeCertificate 413009 :=
  certifyPrime (q := pv3) (ls := [pv2,pv83,pv311]) (by decide +kernel)
def pv413009 : PrimeValue := ⟨413009, pr413009⟩
private theorem pr413087 : PrimeCertificate 413087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv206543]) (by decide +kernel)
def pv413087 : PrimeValue := ⟨413087, pr413087⟩
private theorem pr413129 : PrimeCertificate 413129 :=
  certifyPrime (q := pv3) (ls := [pv2,pv113,pv457]) (by decide +kernel)
def pv413129 : PrimeValue := ⟨413129, pr413129⟩
private theorem pr413141 : PrimeCertificate 413141 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv13,pv227]) (by decide +kernel)
def pv413141 : PrimeValue := ⟨413141, pr413141⟩
private theorem pr413159 : PrimeCertificate 413159 :=
  certifyPrime (q := pv13) (ls := [pv2,pv167,pv1237]) (by decide +kernel)
def pv413159 : PrimeValue := ⟨413159, pr413159⟩
private theorem pr413197 : PrimeCertificate 413197 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv4919]) (by decide +kernel)
def pv413197 : PrimeValue := ⟨413197, pr413197⟩
private theorem pr413201 : PrimeCertificate 413201 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv1033]) (by decide +kernel)
def pv413201 : PrimeValue := ⟨413201, pr413201⟩
private theorem pr413207 : PrimeCertificate 413207 :=
  certifyPrime (q := pv5) (ls := [pv2,pv206603]) (by decide +kernel)
def pv413207 : PrimeValue := ⟨413207, pr413207⟩
private theorem pr413233 : PrimeCertificate 413233 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv8609]) (by decide +kernel)
def pv413233 : PrimeValue := ⟨413233, pr413233⟩
private theorem pr413251 : PrimeCertificate 413251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv29]) (by decide +kernel)
def pv413251 : PrimeValue := ⟨413251, pr413251⟩
private theorem pr413267 : PrimeCertificate 413267 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv4217]) (by decide +kernel)
def pv413267 : PrimeValue := ⟨413267, pr413267⟩
private theorem pr413353 : PrimeCertificate 413353 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5741]) (by decide +kernel)
def pv413353 : PrimeValue := ⟨413353, pr413353⟩
private theorem pr413411 : PrimeCertificate 413411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41341]) (by decide +kernel)
def pv413411 : PrimeValue := ⟨413411, pr413411⟩
private theorem pr413417 : PrimeCertificate 413417 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv1667]) (by decide +kernel)
def pv413417 : PrimeValue := ⟨413417, pr413417⟩
private theorem pr413461 : PrimeCertificate 413461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv2297]) (by decide +kernel)
def pv413461 : PrimeValue := ⟨413461, pr413461⟩
private theorem pr413551 : PrimeCertificate 413551 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv919]) (by decide +kernel)
def pv413551 : PrimeValue := ⟨413551, pr413551⟩
private theorem pr413579 : PrimeCertificate 413579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv1709]) (by decide +kernel)
def pv413579 : PrimeValue := ⟨413579, pr413579⟩
private theorem pr413597 : PrimeCertificate 413597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv103399]) (by decide +kernel)
def pv413597 : PrimeValue := ⟨413597, pr413597⟩
private theorem pr413683 : PrimeCertificate 413683 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv68947]) (by decide +kernel)
def pv413683 : PrimeValue := ⟨413683, pr413683⟩
private theorem pr413711 : PrimeCertificate 413711 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv3761]) (by decide +kernel)
def pv413711 : PrimeValue := ⟨413711, pr413711⟩
private theorem pr413713 : PrimeCertificate 413713 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv17]) (by decide +kernel)
def pv413713 : PrimeValue := ⟨413713, pr413713⟩
private theorem pr413807 : PrimeCertificate 413807 :=
  certifyPrime (q := pv5) (ls := [pv2,pv113,pv1831]) (by decide +kernel)
def pv413807 : PrimeValue := ⟨413807, pr413807⟩
private theorem pr413827 : PrimeCertificate 413827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv59,pv167]) (by decide +kernel)
def pv413827 : PrimeValue := ⟨413827, pr413827⟩
private theorem pr413849 : PrimeCertificate 413849 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv179]) (by decide +kernel)
def pv413849 : PrimeValue := ⟨413849, pr413849⟩
private theorem pr413863 : PrimeCertificate 413863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv2999]) (by decide +kernel)
def pv413863 : PrimeValue := ⟨413863, pr413863⟩
private theorem pr413951 : PrimeCertificate 413951 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv17,pv487]) (by decide +kernel)
def pv413951 : PrimeValue := ⟨413951, pr413951⟩
private theorem pr413981 : PrimeCertificate 413981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv2957]) (by decide +kernel)
def pv413981 : PrimeValue := ⟨413981, pr413981⟩
private theorem pr414053 : PrimeCertificate 414053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv6089]) (by decide +kernel)
def pv414053 : PrimeValue := ⟨414053, pr414053⟩
private theorem pr414179 : PrimeCertificate 414179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv37,pv193]) (by decide +kernel)
def pv414179 : PrimeValue := ⟨414179, pr414179⟩
private theorem pr414203 : PrimeCertificate 414203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv2837]) (by decide +kernel)
def pv414203 : PrimeValue := ⟨414203, pr414203⟩
private theorem pr414217 : PrimeCertificate 414217 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv523]) (by decide +kernel)
def pv414217 : PrimeValue := ⟨414217, pr414217⟩
private theorem pr414221 : PrimeCertificate 414221 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv139,pv149]) (by decide +kernel)
def pv414221 : PrimeValue := ⟨414221, pr414221⟩
private theorem pr414259 : PrimeCertificate 414259 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13,pv47,pv113]) (by decide +kernel)
def pv414259 : PrimeValue := ⟨414259, pr414259⟩
private theorem pr414277 : PrimeCertificate 414277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv23,pv79]) (by decide +kernel)
def pv414277 : PrimeValue := ⟨414277, pr414277⟩
private theorem pr414311 : PrimeCertificate 414311 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv3187]) (by decide +kernel)
def pv414311 : PrimeValue := ⟨414311, pr414311⟩
private theorem pr414361 : PrimeCertificate 414361 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv1151]) (by decide +kernel)
def pv414361 : PrimeValue := ⟨414361, pr414361⟩
private theorem pr414367 : PrimeCertificate 414367 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv69061]) (by decide +kernel)
def pv414367 : PrimeValue := ⟨414367, pr414367⟩
private theorem pr414397 : PrimeCertificate 414397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1279]) (by decide +kernel)
def pv414397 : PrimeValue := ⟨414397, pr414397⟩
private theorem pr414461 : PrimeCertificate 414461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv23,pv53]) (by decide +kernel)
def pv414461 : PrimeValue := ⟨414461, pr414461⟩
private theorem pr414467 : PrimeCertificate 414467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv19,pv839]) (by decide +kernel)
def pv414467 : PrimeValue := ⟨414467, pr414467⟩
private theorem pr414487 : PrimeCertificate 414487 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23027]) (by decide +kernel)
def pv414487 : PrimeValue := ⟨414487, pr414487⟩
private theorem pr414521 : PrimeCertificate 414521 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv43,pv241]) (by decide +kernel)
def pv414521 : PrimeValue := ⟨414521, pr414521⟩
private theorem pr414553 : PrimeCertificate 414553 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv751]) (by decide +kernel)
def pv414553 : PrimeValue := ⟨414553, pr414553⟩
private theorem pr414577 : PrimeCertificate 414577 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2879]) (by decide +kernel)
def pv414577 : PrimeValue := ⟨414577, pr414577⟩
private theorem pr414607 : PrimeCertificate 414607 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv43,pv1607]) (by decide +kernel)
def pv414607 : PrimeValue := ⟨414607, pr414607⟩
private theorem pr414611 : PrimeCertificate 414611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv5923]) (by decide +kernel)
def pv414611 : PrimeValue := ⟨414611, pr414611⟩
private theorem pr414629 : PrimeCertificate 414629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv103657]) (by decide +kernel)
def pv414629 : PrimeValue := ⟨414629, pr414629⟩
private theorem pr414677 : PrimeCertificate 414677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv103669]) (by decide +kernel)
def pv414677 : PrimeValue := ⟨414677, pr414677⟩
private theorem pr414683 : PrimeCertificate 414683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv207341]) (by decide +kernel)
def pv414683 : PrimeValue := ⟨414683, pr414683⟩
private theorem pr414703 : PrimeCertificate 414703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23039]) (by decide +kernel)
def pv414703 : PrimeValue := ⟨414703, pr414703⟩
private theorem pr414709 : PrimeCertificate 414709 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv4937]) (by decide +kernel)
def pv414709 : PrimeValue := ⟨414709, pr414709⟩
private theorem pr414721 : PrimeCertificate 414721 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv414721 : PrimeValue := ⟨414721, pr414721⟩
private theorem pr414731 : PrimeCertificate 414731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv67,pv619]) (by decide +kernel)
def pv414731 : PrimeValue := ⟨414731, pr414731⟩
private theorem pr414767 : PrimeCertificate 414767 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv17,pv1109]) (by decide +kernel)
def pv414767 : PrimeValue := ⟨414767, pr414767⟩
private theorem pr414773 : PrimeCertificate 414773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv97,pv1069]) (by decide +kernel)
def pv414773 : PrimeValue := ⟨414773, pr414773⟩
private theorem pr414857 : PrimeCertificate 414857 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv3989]) (by decide +kernel)
def pv414857 : PrimeValue := ⟨414857, pr414857⟩
private theorem pr414913 : PrimeCertificate 414913 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2161]) (by decide +kernel)
def pv414913 : PrimeValue := ⟨414913, pr414913⟩
private theorem pr414923 : PrimeCertificate 414923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv61,pv179]) (by decide +kernel)
def pv414923 : PrimeValue := ⟨414923, pr414923⟩
private theorem pr414949 : PrimeCertificate 414949 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv151,pv229]) (by decide +kernel)
def pv414949 : PrimeValue := ⟨414949, pr414949⟩
private theorem pr414991 : PrimeCertificate 414991 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv29,pv53]) (by decide +kernel)
def pv414991 : PrimeValue := ⟨414991, pr414991⟩
private theorem pr415013 : PrimeCertificate 415013 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv23,pv347]) (by decide +kernel)
def pv415013 : PrimeValue := ⟨415013, pr415013⟩
private theorem pr415097 : PrimeCertificate 415097 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv53,pv89]) (by decide +kernel)
def pv415097 : PrimeValue := ⟨415097, pr415097⟩
private theorem pr415109 : PrimeCertificate 415109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv157,pv661]) (by decide +kernel)
def pv415109 : PrimeValue := ⟨415109, pr415109⟩
private theorem pr415111 : PrimeCertificate 415111 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv5,pv101,pv137]) (by decide +kernel)
def pv415111 : PrimeValue := ⟨415111, pr415111⟩
private theorem pr415133 : PrimeCertificate 415133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67,pv1549]) (by decide +kernel)
def pv415133 : PrimeValue := ⟨415133, pr415133⟩
private theorem pr415141 : PrimeCertificate 415141 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv17,pv37]) (by decide +kernel)
def pv415141 : PrimeValue := ⟨415141, pr415141⟩
private theorem pr415187 : PrimeCertificate 415187 :=
  certifyPrime (q := pv2) (ls := [pv2,pv207593]) (by decide +kernel)
def pv415187 : PrimeValue := ⟨415187, pr415187⟩
private theorem pr415201 : PrimeCertificate 415201 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv173]) (by decide +kernel)
def pv415201 : PrimeValue := ⟨415201, pr415201⟩
private theorem pr415231 : PrimeCertificate 415231 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv13841]) (by decide +kernel)
def pv415231 : PrimeValue := ⟨415231, pr415231⟩
private theorem pr415253 : PrimeCertificate 415253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv103813]) (by decide +kernel)
def pv415253 : PrimeValue := ⟨415253, pr415253⟩
private theorem pr415319 : PrimeCertificate 415319 :=
  certifyPrime (q := pv7) (ls := [pv2,pv281,pv739]) (by decide +kernel)
def pv415319 : PrimeValue := ⟨415319, pr415319⟩
private theorem pr415391 : PrimeCertificate 415391 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv41539]) (by decide +kernel)
def pv415391 : PrimeValue := ⟨415391, pr415391⟩
private theorem pr415427 : PrimeCertificate 415427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv23,pv821]) (by decide +kernel)
def pv415427 : PrimeValue := ⟨415427, pr415427⟩
private theorem pr415447 : PrimeCertificate 415447 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv4073]) (by decide +kernel)
def pv415447 : PrimeValue := ⟨415447, pr415447⟩
private theorem pr415469 : PrimeCertificate 415469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv103867]) (by decide +kernel)
def pv415469 : PrimeValue := ⟨415469, pr415469⟩
private theorem pr415507 : PrimeCertificate 415507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv761]) (by decide +kernel)
def pv415507 : PrimeValue := ⟨415507, pr415507⟩
private theorem pr415517 : PrimeCertificate 415517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv1423]) (by decide +kernel)
def pv415517 : PrimeValue := ⟨415517, pr415517⟩
private theorem pr415543 : PrimeCertificate 415543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv69257]) (by decide +kernel)
def pv415543 : PrimeValue := ⟨415543, pr415543⟩
private theorem pr415607 : PrimeCertificate 415607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv10937]) (by decide +kernel)
def pv415607 : PrimeValue := ⟨415607, pr415607⟩
private theorem pr415643 : PrimeCertificate 415643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv207821]) (by decide +kernel)
def pv415643 : PrimeValue := ⟨415643, pr415643⟩
private theorem pr415661 : PrimeCertificate 415661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv2969]) (by decide +kernel)
def pv415661 : PrimeValue := ⟨415661, pr415661⟩
private theorem pr415687 : PrimeCertificate 415687 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv29,pv2389]) (by decide +kernel)
def pv415687 : PrimeValue := ⟨415687, pr415687⟩
private theorem pr415721 : PrimeCertificate 415721 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv19,pv547]) (by decide +kernel)
def pv415721 : PrimeValue := ⟨415721, pr415721⟩
private theorem pr415783 : PrimeCertificate 415783 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv23099]) (by decide +kernel)
def pv415783 : PrimeValue := ⟨415783, pr415783⟩
private theorem pr415799 : PrimeCertificate 415799 :=
  certifyPrime (q := pv13) (ls := [pv2,pv127,pv1637]) (by decide +kernel)
def pv415799 : PrimeValue := ⟨415799, pr415799⟩
private theorem pr415823 : PrimeCertificate 415823 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv41,pv461]) (by decide +kernel)
def pv415823 : PrimeValue := ⟨415823, pr415823⟩
private theorem pr415861 : PrimeCertificate 415861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv29,pv239]) (by decide +kernel)
def pv415861 : PrimeValue := ⟨415861, pr415861⟩
private theorem pr415873 : PrimeCertificate 415873 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19]) (by decide +kernel)
def pv415873 : PrimeValue := ⟨415873, pr415873⟩
private theorem pr415879 : PrimeCertificate 415879 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv69313]) (by decide +kernel)
def pv415879 : PrimeValue := ⟨415879, pr415879⟩
private theorem pr415931 : PrimeCertificate 415931 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41593]) (by decide +kernel)
def pv415931 : PrimeValue := ⟨415931, pr415931⟩
private theorem pr415937 : PrimeCertificate 415937 :=
  certifyPrime (q := pv3) (ls := [pv2,pv67,pv97]) (by decide +kernel)
def pv415937 : PrimeValue := ⟨415937, pr415937⟩
private theorem pr415949 : PrimeCertificate 415949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv19,pv421]) (by decide +kernel)
def pv415949 : PrimeValue := ⟨415949, pr415949⟩
private theorem pr415969 : PrimeCertificate 415969 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv619]) (by decide +kernel)
def pv415969 : PrimeValue := ⟨415969, pr415969⟩
private theorem pr415979 : PrimeCertificate 415979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv9043]) (by decide +kernel)
def pv415979 : PrimeValue := ⟨415979, pr415979⟩
private theorem pr415993 : PrimeCertificate 415993 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17333]) (by decide +kernel)
def pv415993 : PrimeValue := ⟨415993, pr415993⟩
private theorem pr415999 : PrimeCertificate 415999 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv191]) (by decide +kernel)
def pv415999 : PrimeValue := ⟨415999, pr415999⟩
private theorem pr416023 : PrimeCertificate 416023 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv69337]) (by decide +kernel)
def pv416023 : PrimeValue := ⟨416023, pr416023⟩
private theorem pr416107 : PrimeCertificate 416107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23117]) (by decide +kernel)
def pv416107 : PrimeValue := ⟨416107, pr416107⟩
private theorem pr416147 : PrimeCertificate 416147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv208073]) (by decide +kernel)
def pv416147 : PrimeValue := ⟨416147, pr416147⟩
private theorem pr416153 : PrimeCertificate 416153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv4729]) (by decide +kernel)
def pv416153 : PrimeValue := ⟨416153, pr416153⟩
private theorem pr416167 : PrimeCertificate 416167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv139,pv499]) (by decide +kernel)
def pv416167 : PrimeValue := ⟨416167, pr416167⟩
private theorem pr416201 : PrimeCertificate 416201 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv2081]) (by decide +kernel)
def pv416201 : PrimeValue := ⟨416201, pr416201⟩
private theorem pr416243 : PrimeCertificate 416243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv208121]) (by decide +kernel)
def pv416243 : PrimeValue := ⟨416243, pr416243⟩
private theorem pr416249 : PrimeCertificate 416249 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv7433]) (by decide +kernel)
def pv416249 : PrimeValue := ⟨416249, pr416249⟩
private theorem pr416257 : PrimeCertificate 416257 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv271]) (by decide +kernel)
def pv416257 : PrimeValue := ⟨416257, pr416257⟩
private theorem pr416291 : PrimeCertificate 416291 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv19,pv313]) (by decide +kernel)
def pv416291 : PrimeValue := ⟨416291, pr416291⟩
private theorem pr416359 : PrimeCertificate 416359 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23131]) (by decide +kernel)
def pv416359 : PrimeValue := ⟨416359, pr416359⟩
private theorem pr416387 : PrimeCertificate 416387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv3413]) (by decide +kernel)
def pv416387 : PrimeValue := ⟨416387, pr416387⟩
private theorem pr416393 : PrimeCertificate 416393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv31,pv73]) (by decide +kernel)
def pv416393 : PrimeValue := ⟨416393, pr416393⟩
private theorem pr416401 : PrimeCertificate 416401 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv347]) (by decide +kernel)
def pv416401 : PrimeValue := ⟨416401, pr416401⟩
private theorem pr416441 : PrimeCertificate 416441 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv29,pv359]) (by decide +kernel)
def pv416441 : PrimeValue := ⟨416441, pr416441⟩
private theorem pr416443 : PrimeCertificate 416443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv19,pv281]) (by decide +kernel)
def pv416443 : PrimeValue := ⟨416443, pr416443⟩
private theorem pr416459 : PrimeCertificate 416459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv151,pv197]) (by decide +kernel)
def pv416459 : PrimeValue := ⟨416459, pr416459⟩
private theorem pr416573 : PrimeCertificate 416573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv8011]) (by decide +kernel)
def pv416573 : PrimeValue := ⟨416573, pr416573⟩
private theorem pr416621 : PrimeCertificate 416621 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv37,pv563]) (by decide +kernel)
def pv416621 : PrimeValue := ⟨416621, pr416621⟩
private theorem pr416693 : PrimeCertificate 416693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv104173]) (by decide +kernel)
def pv416693 : PrimeValue := ⟨416693, pr416693⟩
private theorem pr416797 : PrimeCertificate 416797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv739]) (by decide +kernel)
def pv416797 : PrimeValue := ⟨416797, pr416797⟩
private theorem pr416833 : PrimeCertificate 416833 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv167]) (by decide +kernel)
def pv416833 : PrimeValue := ⟨416833, pr416833⟩
private theorem pr416839 : PrimeCertificate 416839 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv69473]) (by decide +kernel)
def pv416839 : PrimeValue := ⟨416839, pr416839⟩
private theorem pr416873 : PrimeCertificate 416873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv107,pv487]) (by decide +kernel)
def pv416873 : PrimeValue := ⟨416873, pr416873⟩
private theorem pr416947 : PrimeCertificate 416947 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv69491]) (by decide +kernel)
def pv416947 : PrimeValue := ⟨416947, pr416947⟩
private theorem pr416963 : PrimeCertificate 416963 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv13,pv29,pv79]) (by decide +kernel)
def pv416963 : PrimeValue := ⟨416963, pr416963⟩
private theorem pr416989 : PrimeCertificate 416989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv13]) (by decide +kernel)
def pv416989 : PrimeValue := ⟨416989, pr416989⟩
private theorem pr417089 : PrimeCertificate 417089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv19]) (by decide +kernel)
def pv417089 : PrimeValue := ⟨417089, pr417089⟩
private theorem pr417097 : PrimeCertificate 417097 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1931]) (by decide +kernel)
def pv417097 : PrimeValue := ⟨417097, pr417097⟩
private theorem pr417127 : PrimeCertificate 417127 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv3659]) (by decide +kernel)
def pv417127 : PrimeValue := ⟨417127, pr417127⟩
private theorem pr417191 : PrimeCertificate 417191 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv41719]) (by decide +kernel)
def pv417191 : PrimeValue := ⟨417191, pr417191⟩
private theorem pr417217 : PrimeCertificate 417217 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv41,pv53]) (by decide +kernel)
def pv417217 : PrimeValue := ⟨417217, pr417217⟩
private theorem pr417251 : PrimeCertificate 417251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1669]) (by decide +kernel)
def pv417251 : PrimeValue := ⟨417251, pr417251⟩
private theorem pr417293 : PrimeCertificate 417293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv104323]) (by decide +kernel)
def pv417293 : PrimeValue := ⟨417293, pr417293⟩
private theorem pr417311 : PrimeCertificate 417311 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv29,pv1439]) (by decide +kernel)
def pv417311 : PrimeValue := ⟨417311, pr417311⟩
private theorem pr417317 : PrimeCertificate 417317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv19]) (by decide +kernel)
def pv417317 : PrimeValue := ⟨417317, pr417317⟩
private theorem pr417419 : PrimeCertificate 417419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv12277]) (by decide +kernel)
def pv417419 : PrimeValue := ⟨417419, pr417419⟩
private theorem pr417479 : PrimeCertificate 417479 :=
  certifyPrime (q := pv17) (ls := [pv2,pv208739]) (by decide +kernel)
def pv417479 : PrimeValue := ⟨417479, pr417479⟩
private theorem pr417491 : PrimeCertificate 417491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv83,pv503]) (by decide +kernel)
def pv417491 : PrimeValue := ⟨417491, pr417491⟩
private theorem pr417509 : PrimeCertificate 417509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv31,pv37]) (by decide +kernel)
def pv417509 : PrimeValue := ⟨417509, pr417509⟩
private theorem pr417511 : PrimeCertificate 417511 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv4639]) (by decide +kernel)
def pv417511 : PrimeValue := ⟨417511, pr417511⟩
private theorem pr417523 : PrimeCertificate 417523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv9941]) (by decide +kernel)
def pv417523 : PrimeValue := ⟨417523, pr417523⟩
private theorem pr417541 : PrimeCertificate 417541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv6959]) (by decide +kernel)
def pv417541 : PrimeValue := ⟨417541, pr417541⟩
private theorem pr417553 : PrimeCertificate 417553 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv8699]) (by decide +kernel)
def pv417553 : PrimeValue := ⟨417553, pr417553⟩
private theorem pr417581 : PrimeCertificate 417581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv20879]) (by decide +kernel)
def pv417581 : PrimeValue := ⟨417581, pr417581⟩
private theorem pr417583 : PrimeCertificate 417583 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11,pv19,pv37]) (by decide +kernel)
def pv417583 : PrimeValue := ⟨417583, pr417583⟩
private theorem pr417643 : PrimeCertificate 417643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv1481]) (by decide +kernel)
def pv417643 : PrimeValue := ⟨417643, pr417643⟩
private theorem pr417649 : PrimeCertificate 417649 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv11,pv113]) (by decide +kernel)
def pv417649 : PrimeValue := ⟨417649, pr417649⟩
private theorem pr417671 : PrimeCertificate 417671 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv3797]) (by decide +kernel)
def pv417671 : PrimeValue := ⟨417671, pr417671⟩
private theorem pr417719 : PrimeCertificate 417719 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv29837]) (by decide +kernel)
def pv417719 : PrimeValue := ⟨417719, pr417719⟩
private theorem pr417727 : PrimeCertificate 417727 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23,pv1009]) (by decide +kernel)
def pv417727 : PrimeValue := ⟨417727, pr417727⟩
private theorem pr417763 : PrimeCertificate 417763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23209]) (by decide +kernel)
def pv417763 : PrimeValue := ⟨417763, pr417763⟩
private theorem pr417793 : PrimeCertificate 417793 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17]) (by decide +kernel)
def pv417793 : PrimeValue := ⟨417793, pr417793⟩
private theorem pr417821 : PrimeCertificate 417821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv1607]) (by decide +kernel)
def pv417821 : PrimeValue := ⟨417821, pr417821⟩
private theorem pr417869 : PrimeCertificate 417869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv9497]) (by decide +kernel)
def pv417869 : PrimeValue := ⟨417869, pr417869⟩
private theorem pr417931 : PrimeCertificate 417931 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv13931]) (by decide +kernel)
def pv417931 : PrimeValue := ⟨417931, pr417931⟩
private theorem pr417941 : PrimeCertificate 417941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv20897]) (by decide +kernel)
def pv417941 : PrimeValue := ⟨417941, pr417941⟩
private theorem pr417953 : PrimeCertificate 417953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv353]) (by decide +kernel)
def pv417953 : PrimeValue := ⟨417953, pr417953⟩
private theorem pr417961 : PrimeCertificate 417961 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv43]) (by decide +kernel)
def pv417961 : PrimeValue := ⟨417961, pr417961⟩
private theorem pr417983 : PrimeCertificate 417983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv208991]) (by decide +kernel)
def pv417983 : PrimeValue := ⟨417983, pr417983⟩
private theorem pr418007 : PrimeCertificate 418007 :=
  certifyPrime (q := pv5) (ls := [pv2,pv29,pv7207]) (by decide +kernel)
def pv418007 : PrimeValue := ⟨418007, pr418007⟩
private theorem pr418009 : PrimeCertificate 418009 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv17417]) (by decide +kernel)
def pv418009 : PrimeValue := ⟨418009, pr418009⟩
private theorem pr418031 : PrimeCertificate 418031 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv17,pv2459]) (by decide +kernel)
def pv418031 : PrimeValue := ⟨418031, pr418031⟩
private theorem pr418051 : PrimeCertificate 418051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv929]) (by decide +kernel)
def pv418051 : PrimeValue := ⟨418051, pr418051⟩
private theorem pr418079 : PrimeCertificate 418079 :=
  certifyPrime (q := pv7) (ls := [pv2,pv209039]) (by decide +kernel)
def pv418079 : PrimeValue := ⟨418079, pr418079⟩
private theorem pr418109 : PrimeCertificate 418109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv104527]) (by decide +kernel)
def pv418109 : PrimeValue := ⟨418109, pr418109⟩
private theorem pr418177 : PrimeCertificate 418177 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv418177 : PrimeValue := ⟨418177, pr418177⟩
private theorem pr418199 : PrimeCertificate 418199 :=
  certifyPrime (q := pv13) (ls := [pv2,pv11,pv19009]) (by decide +kernel)
def pv418199 : PrimeValue := ⟨418199, pr418199⟩
private theorem pr418331 : PrimeCertificate 418331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv3803]) (by decide +kernel)
def pv418331 : PrimeValue := ⟨418331, pr418331⟩
private theorem pr418337 : PrimeCertificate 418337 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv769]) (by decide +kernel)
def pv418337 : PrimeValue := ⟨418337, pr418337⟩
private theorem pr418349 : PrimeCertificate 418349 :=
  certifyPrime (q := pv11) (ls := [pv2,pv7,pv67,pv223]) (by decide +kernel)
def pv418349 : PrimeValue := ⟨418349, pr418349⟩
private theorem pr418351 : PrimeCertificate 418351 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv2789]) (by decide +kernel)
def pv418351 : PrimeValue := ⟨418351, pr418351⟩
private theorem pr418373 : PrimeCertificate 418373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv104593]) (by decide +kernel)
def pv418373 : PrimeValue := ⟨418373, pr418373⟩
private theorem pr418427 : PrimeCertificate 418427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv209213]) (by decide +kernel)
def pv418427 : PrimeValue := ⟨418427, pr418427⟩
private theorem pr418553 : PrimeCertificate 418553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv113,pv463]) (by decide +kernel)
def pv418553 : PrimeValue := ⟨418553, pr418553⟩
private theorem pr418601 : PrimeCertificate 418601 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv13,pv23]) (by decide +kernel)
def pv418601 : PrimeValue := ⟨418601, pr418601⟩
private theorem pr418633 : PrimeCertificate 418633 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17443]) (by decide +kernel)
def pv418633 : PrimeValue := ⟨418633, pr418633⟩
private theorem pr418637 : PrimeCertificate 418637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv104659]) (by decide +kernel)
def pv418637 : PrimeValue := ⟨418637, pr418637⟩
private theorem pr418699 : PrimeCertificate 418699 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv3323]) (by decide +kernel)
def pv418699 : PrimeValue := ⟨418699, pr418699⟩
private theorem pr418709 : PrimeCertificate 418709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv104677]) (by decide +kernel)
def pv418709 : PrimeValue := ⟨418709, pr418709⟩
private theorem pr418721 : PrimeCertificate 418721 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv2617]) (by decide +kernel)
def pv418721 : PrimeValue := ⟨418721, pr418721⟩
private theorem pr418751 : PrimeCertificate 418751 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv67]) (by decide +kernel)
def pv418751 : PrimeValue := ⟨418751, pr418751⟩
private theorem pr418783 : PrimeCertificate 418783 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv59]) (by decide +kernel)
def pv418783 : PrimeValue := ⟨418783, pr418783⟩
private theorem pr418787 : PrimeCertificate 418787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv209393]) (by decide +kernel)
def pv418787 : PrimeValue := ⟨418787, pr418787⟩
private theorem pr418793 : PrimeCertificate 418793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv4759]) (by decide +kernel)
def pv418793 : PrimeValue := ⟨418793, pr418793⟩
private theorem pr418799 : PrimeCertificate 418799 :=
  certifyPrime (q := pv19) (ls := [pv2,pv19,pv103,pv107]) (by decide +kernel)
def pv418799 : PrimeValue := ⟨418799, pr418799⟩
private theorem pr418871 : PrimeCertificate 418871 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv41887]) (by decide +kernel)
def pv418871 : PrimeValue := ⟨418871, pr418871⟩
private theorem pr418889 : PrimeCertificate 418889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv52361]) (by decide +kernel)
def pv418889 : PrimeValue := ⟨418889, pr418889⟩
private theorem pr418909 : PrimeCertificate 418909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv4987]) (by decide +kernel)
def pv418909 : PrimeValue := ⟨418909, pr418909⟩
private theorem pr418921 : PrimeCertificate 418921 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv3491]) (by decide +kernel)
def pv418921 : PrimeValue := ⟨418921, pr418921⟩
private theorem pr418933 : PrimeCertificate 418933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv431]) (by decide +kernel)
def pv418933 : PrimeValue := ⟨418933, pr418933⟩
private theorem pr418961 : PrimeCertificate 418961 :=
  certifyPrime (q := pv29) (ls := [pv2,pv5,pv5237]) (by decide +kernel)
def pv418961 : PrimeValue := ⟨418961, pr418961⟩
private theorem pr418981 : PrimeCertificate 418981 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv6983]) (by decide +kernel)
def pv418981 : PrimeValue := ⟨418981, pr418981⟩
private theorem pr419183 : PrimeCertificate 419183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv31,pv6761]) (by decide +kernel)
def pv419183 : PrimeValue := ⟨419183, pr419183⟩
private theorem pr419189 : PrimeCertificate 419189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv1361]) (by decide +kernel)
def pv419189 : PrimeValue := ⟨419189, pr419189⟩
private theorem pr419191 : PrimeCertificate 419191 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv89,pv157]) (by decide +kernel)
def pv419191 : PrimeValue := ⟨419191, pr419191⟩
private theorem pr419201 : PrimeCertificate 419201 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv131]) (by decide +kernel)
def pv419201 : PrimeValue := ⟨419201, pr419201⟩
private theorem pr419231 : PrimeCertificate 419231 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv53,pv113]) (by decide +kernel)
def pv419231 : PrimeValue := ⟨419231, pr419231⟩
private theorem pr419281 : PrimeCertificate 419281 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv1747]) (by decide +kernel)
def pv419281 : PrimeValue := ⟨419281, pr419281⟩
private theorem pr419291 : PrimeCertificate 419291 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv23,pv1823]) (by decide +kernel)
def pv419291 : PrimeValue := ⟨419291, pr419291⟩
private theorem pr419351 : PrimeCertificate 419351 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv8387]) (by decide +kernel)
def pv419351 : PrimeValue := ⟨419351, pr419351⟩
private theorem pr419383 : PrimeCertificate 419383 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv1013]) (by decide +kernel)
def pv419383 : PrimeValue := ⟨419383, pr419383⟩
private theorem pr419417 : PrimeCertificate 419417 :=
  certifyPrime (q := pv3) (ls := [pv2,pv103,pv509]) (by decide +kernel)
def pv419417 : PrimeValue := ⟨419417, pr419417⟩
private theorem pr419443 : PrimeCertificate 419443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53,pv1319]) (by decide +kernel)
def pv419443 : PrimeValue := ⟨419443, pr419443⟩
private theorem pr419459 : PrimeCertificate 419459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv17,pv73]) (by decide +kernel)
def pv419459 : PrimeValue := ⟨419459, pr419459⟩
private theorem pr419477 : PrimeCertificate 419477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv104869]) (by decide +kernel)
def pv419477 : PrimeValue := ⟨419477, pr419477⟩
private theorem pr419491 : PrimeCertificate 419491 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv59,pv79]) (by decide +kernel)
def pv419491 : PrimeValue := ⟨419491, pr419491⟩
private theorem pr419513 : PrimeCertificate 419513 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41,pv1279]) (by decide +kernel)
def pv419513 : PrimeValue := ⟨419513, pr419513⟩
private theorem pr419563 : PrimeCertificate 419563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv13,pv163]) (by decide +kernel)
def pv419563 : PrimeValue := ⟨419563, pr419563⟩
private theorem pr419597 : PrimeCertificate 419597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv5521]) (by decide +kernel)
def pv419597 : PrimeValue := ⟨419597, pr419597⟩
private theorem pr419603 : PrimeCertificate 419603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv209801]) (by decide +kernel)
def pv419603 : PrimeValue := ⟨419603, pr419603⟩
private theorem pr419651 : PrimeCertificate 419651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv109]) (by decide +kernel)
def pv419651 : PrimeValue := ⟨419651, pr419651⟩
private theorem pr419711 : PrimeCertificate 419711 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv19,pv47]) (by decide +kernel)
def pv419711 : PrimeValue := ⟨419711, pr419711⟩
private theorem pr419777 : PrimeCertificate 419777 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv937]) (by decide +kernel)
def pv419777 : PrimeValue := ⟨419777, pr419777⟩
private theorem pr419801 : PrimeCertificate 419801 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv2099]) (by decide +kernel)
def pv419801 : PrimeValue := ⟨419801, pr419801⟩
private theorem pr419803 : PrimeCertificate 419803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv37,pv61]) (by decide +kernel)
def pv419803 : PrimeValue := ⟨419803, pr419803⟩
private theorem pr419821 : PrimeCertificate 419821 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv6997]) (by decide +kernel)
def pv419821 : PrimeValue := ⟨419821, pr419821⟩
private theorem pr419831 : PrimeCertificate 419831 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv41983]) (by decide +kernel)
def pv419831 : PrimeValue := ⟨419831, pr419831⟩
private theorem pr419927 : PrimeCertificate 419927 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv31,pv521]) (by decide +kernel)
def pv419927 : PrimeValue := ⟨419927, pr419927⟩
private theorem pr419999 : PrimeCertificate 419999 :=
  certifyPrime (q := pv13) (ls := [pv2,pv373,pv563]) (by decide +kernel)
def pv419999 : PrimeValue := ⟨419999, pr419999⟩
private theorem pr420037 : PrimeCertificate 420037 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv29,pv71]) (by decide +kernel)
def pv420037 : PrimeValue := ⟨420037, pr420037⟩
private theorem pr420041 : PrimeCertificate 420041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv10501]) (by decide +kernel)
def pv420041 : PrimeValue := ⟨420041, pr420041⟩
private theorem pr420047 : PrimeCertificate 420047 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv61,pv313]) (by decide +kernel)
def pv420047 : PrimeValue := ⟨420047, pr420047⟩
private theorem pr420073 : PrimeCertificate 420073 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv23,pv761]) (by decide +kernel)
def pv420073 : PrimeValue := ⟨420073, pr420073⟩
private theorem pr420149 : PrimeCertificate 420149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv105037]) (by decide +kernel)
def pv420149 : PrimeValue := ⟨420149, pr420149⟩
private theorem pr420163 : PrimeCertificate 420163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv239,pv293]) (by decide +kernel)
def pv420163 : PrimeValue := ⟨420163, pr420163⟩
private theorem pr420191 : PrimeCertificate 420191 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv42019]) (by decide +kernel)
def pv420191 : PrimeValue := ⟨420191, pr420191⟩
private theorem pr420221 : PrimeCertificate 420221 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv21011]) (by decide +kernel)
def pv420221 : PrimeValue := ⟨420221, pr420221⟩
private theorem pr420307 : PrimeCertificate 420307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv70051]) (by decide +kernel)
def pv420307 : PrimeValue := ⟨420307, pr420307⟩
private theorem pr420317 : PrimeCertificate 420317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv59,pv137]) (by decide +kernel)
def pv420317 : PrimeValue := ⟨420317, pr420317⟩
private theorem pr420341 : PrimeCertificate 420341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv21017]) (by decide +kernel)
def pv420341 : PrimeValue := ⟨420341, pr420341⟩
private theorem pr420349 : PrimeCertificate 420349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv1523]) (by decide +kernel)
def pv420349 : PrimeValue := ⟨420349, pr420349⟩
private theorem pr420353 : PrimeCertificate 420353 :=
  certifyPrime (q := pv3) (ls := [pv2,pv821]) (by decide +kernel)
def pv420353 : PrimeValue := ⟨420353, pr420353⟩
private theorem pr420367 : PrimeCertificate 420367 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv70061]) (by decide +kernel)
def pv420367 : PrimeValue := ⟨420367, pr420367⟩
private theorem pr420383 : PrimeCertificate 420383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv210191]) (by decide +kernel)
def pv420383 : PrimeValue := ⟨420383, pr420383⟩
private theorem pr420419 : PrimeCertificate 420419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv210209]) (by decide +kernel)
def pv420419 : PrimeValue := ⟨420419, pr420419⟩
private theorem pr420457 : PrimeCertificate 420457 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17519]) (by decide +kernel)
def pv420457 : PrimeValue := ⟨420457, pr420457⟩
private theorem pr420551 : PrimeCertificate 420551 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv13,pv647]) (by decide +kernel)
def pv420551 : PrimeValue := ⟨420551, pr420551⟩
private theorem pr420557 : PrimeCertificate 420557 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv2237]) (by decide +kernel)
def pv420557 : PrimeValue := ⟨420557, pr420557⟩
private theorem pr420569 : PrimeCertificate 420569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv52571]) (by decide +kernel)
def pv420569 : PrimeValue := ⟨420569, pr420569⟩
private theorem pr420731 : PrimeCertificate 420731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv42073]) (by decide +kernel)
def pv420731 : PrimeValue := ⟨420731, pr420731⟩
private theorem pr420757 : PrimeCertificate 420757 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv5009]) (by decide +kernel)
def pv420757 : PrimeValue := ⟨420757, pr420757⟩
private theorem pr420779 : PrimeCertificate 420779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv3449]) (by decide +kernel)
def pv420779 : PrimeValue := ⟨420779, pr420779⟩
private theorem pr420899 : PrimeCertificate 420899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv389,pv541]) (by decide +kernel)
def pv420899 : PrimeValue := ⟨420899, pr420899⟩
private theorem pr420929 : PrimeCertificate 420929 :=
  certifyPrime (q := pv3) (ls := [pv2,pv6577]) (by decide +kernel)
def pv420929 : PrimeValue := ⟨420929, pr420929⟩
private theorem pr420941 : PrimeCertificate 420941 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv1619]) (by decide +kernel)
def pv420941 : PrimeValue := ⟨420941, pr420941⟩
private theorem pr421037 : PrimeCertificate 421037 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11,pv1367]) (by decide +kernel)
def pv421037 : PrimeValue := ⟨421037, pr421037⟩
private theorem pr421079 : PrimeCertificate 421079 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv19,pv1583]) (by decide +kernel)
def pv421079 : PrimeValue := ⟨421079, pr421079⟩
private theorem pr421093 : PrimeCertificate 421093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv557]) (by decide +kernel)
def pv421093 : PrimeValue := ⟨421093, pr421093⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
