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

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr412831 : Nat.Prime 412831 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv139]) (by decide +kernel)
def pv412831 : PrimeValue := ⟨412831, pr412831⟩
private theorem pr412901 : Nat.Prime 412901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv4129]) (by decide +kernel)
def pv412901 : PrimeValue := ⟨412901, pr412901⟩
private theorem pr412939 : Nat.Prime 412939 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv2549]) (by decide +kernel)
def pv412939 : PrimeValue := ⟨412939, pr412939⟩
private theorem pr412943 : Nat.Prime 412943 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv23,pv47,pv191]) (by decide +kernel)
def pv412943 : PrimeValue := ⟨412943, pr412943⟩
private theorem pr412967 : Nat.Prime 412967 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv206483]) (by decide +kernel)
def pv412967 : PrimeValue := ⟨412967, pr412967⟩
private theorem pr413009 : Nat.Prime 413009 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv83,pv311]) (by decide +kernel)
def pv413009 : PrimeValue := ⟨413009, pr413009⟩
private theorem pr413087 : Nat.Prime 413087 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv206543]) (by decide +kernel)
def pv413087 : PrimeValue := ⟨413087, pr413087⟩
private theorem pr413129 : Nat.Prime 413129 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv113,pv457]) (by decide +kernel)
def pv413129 : PrimeValue := ⟨413129, pr413129⟩
private theorem pr413141 : Nat.Prime 413141 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv13,pv227]) (by decide +kernel)
def pv413141 : PrimeValue := ⟨413141, pr413141⟩
private theorem pr413159 : Nat.Prime 413159 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv167,pv1237]) (by decide +kernel)
def pv413159 : PrimeValue := ⟨413159, pr413159⟩
private theorem pr413197 : Nat.Prime 413197 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv4919]) (by decide +kernel)
def pv413197 : PrimeValue := ⟨413197, pr413197⟩
private theorem pr413201 : Nat.Prime 413201 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv1033]) (by decide +kernel)
def pv413201 : PrimeValue := ⟨413201, pr413201⟩
private theorem pr413207 : Nat.Prime 413207 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv206603]) (by decide +kernel)
def pv413207 : PrimeValue := ⟨413207, pr413207⟩
private theorem pr413233 : Nat.Prime 413233 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv8609]) (by decide +kernel)
def pv413233 : PrimeValue := ⟨413233, pr413233⟩
private theorem pr413251 : Nat.Prime 413251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv29]) (by decide +kernel)
def pv413251 : PrimeValue := ⟨413251, pr413251⟩
private theorem pr413267 : Nat.Prime 413267 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv4217]) (by decide +kernel)
def pv413267 : PrimeValue := ⟨413267, pr413267⟩
private theorem pr413353 : Nat.Prime 413353 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5741]) (by decide +kernel)
def pv413353 : PrimeValue := ⟨413353, pr413353⟩
private theorem pr413411 : Nat.Prime 413411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv41341]) (by decide +kernel)
def pv413411 : PrimeValue := ⟨413411, pr413411⟩
private theorem pr413417 : Nat.Prime 413417 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv31,pv1667]) (by decide +kernel)
def pv413417 : PrimeValue := ⟨413417, pr413417⟩
private theorem pr413461 : Nat.Prime 413461 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv2297]) (by decide +kernel)
def pv413461 : PrimeValue := ⟨413461, pr413461⟩
private theorem pr413551 : Nat.Prime 413551 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv919]) (by decide +kernel)
def pv413551 : PrimeValue := ⟨413551, pr413551⟩
private theorem pr413579 : Nat.Prime 413579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv1709]) (by decide +kernel)
def pv413579 : PrimeValue := ⟨413579, pr413579⟩
private theorem pr413597 : Nat.Prime 413597 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv103399]) (by decide +kernel)
def pv413597 : PrimeValue := ⟨413597, pr413597⟩
private theorem pr413683 : Nat.Prime 413683 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv68947]) (by decide +kernel)
def pv413683 : PrimeValue := ⟨413683, pr413683⟩
private theorem pr413711 : Nat.Prime 413711 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv3761]) (by decide +kernel)
def pv413711 : PrimeValue := ⟨413711, pr413711⟩
private theorem pr413713 : Nat.Prime 413713 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv17]) (by decide +kernel)
def pv413713 : PrimeValue := ⟨413713, pr413713⟩
private theorem pr413807 : Nat.Prime 413807 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv113,pv1831]) (by decide +kernel)
def pv413807 : PrimeValue := ⟨413807, pr413807⟩
private theorem pr413827 : Nat.Prime 413827 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv59,pv167]) (by decide +kernel)
def pv413827 : PrimeValue := ⟨413827, pr413827⟩
private theorem pr413849 : Nat.Prime 413849 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv179]) (by decide +kernel)
def pv413849 : PrimeValue := ⟨413849, pr413849⟩
private theorem pr413863 : Nat.Prime 413863 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23,pv2999]) (by decide +kernel)
def pv413863 : PrimeValue := ⟨413863, pr413863⟩
private theorem pr413951 : Nat.Prime 413951 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv17,pv487]) (by decide +kernel)
def pv413951 : PrimeValue := ⟨413951, pr413951⟩
private theorem pr413981 : Nat.Prime 413981 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv2957]) (by decide +kernel)
def pv413981 : PrimeValue := ⟨413981, pr413981⟩
private theorem pr414053 : Nat.Prime 414053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv6089]) (by decide +kernel)
def pv414053 : PrimeValue := ⟨414053, pr414053⟩
private theorem pr414179 : Nat.Prime 414179 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv37,pv193]) (by decide +kernel)
def pv414179 : PrimeValue := ⟨414179, pr414179⟩
private theorem pr414203 : Nat.Prime 414203 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv73,pv2837]) (by decide +kernel)
def pv414203 : PrimeValue := ⟨414203, pr414203⟩
private theorem pr414217 : Nat.Prime 414217 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv523]) (by decide +kernel)
def pv414217 : PrimeValue := ⟨414217, pr414217⟩
private theorem pr414221 : Nat.Prime 414221 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv139,pv149]) (by decide +kernel)
def pv414221 : PrimeValue := ⟨414221, pr414221⟩
private theorem pr414259 : Nat.Prime 414259 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv13,pv47,pv113]) (by decide +kernel)
def pv414259 : PrimeValue := ⟨414259, pr414259⟩
private theorem pr414277 : Nat.Prime 414277 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv23,pv79]) (by decide +kernel)
def pv414277 : PrimeValue := ⟨414277, pr414277⟩
private theorem pr414311 : Nat.Prime 414311 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv13,pv3187]) (by decide +kernel)
def pv414311 : PrimeValue := ⟨414311, pr414311⟩
private theorem pr414361 : Nat.Prime 414361 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv1151]) (by decide +kernel)
def pv414361 : PrimeValue := ⟨414361, pr414361⟩
private theorem pr414367 : Nat.Prime 414367 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv69061]) (by decide +kernel)
def pv414367 : PrimeValue := ⟨414367, pr414367⟩
private theorem pr414397 : Nat.Prime 414397 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1279]) (by decide +kernel)
def pv414397 : PrimeValue := ⟨414397, pr414397⟩
private theorem pr414461 : Nat.Prime 414461 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv17,pv23,pv53]) (by decide +kernel)
def pv414461 : PrimeValue := ⟨414461, pr414461⟩
private theorem pr414467 : Nat.Prime 414467 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv19,pv839]) (by decide +kernel)
def pv414467 : PrimeValue := ⟨414467, pr414467⟩
private theorem pr414487 : Nat.Prime 414487 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23027]) (by decide +kernel)
def pv414487 : PrimeValue := ⟨414487, pr414487⟩
private theorem pr414521 : Nat.Prime 414521 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv43,pv241]) (by decide +kernel)
def pv414521 : PrimeValue := ⟨414521, pr414521⟩
private theorem pr414553 : Nat.Prime 414553 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23,pv751]) (by decide +kernel)
def pv414553 : PrimeValue := ⟨414553, pr414553⟩
private theorem pr414577 : Nat.Prime 414577 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2879]) (by decide +kernel)
def pv414577 : PrimeValue := ⟨414577, pr414577⟩
private theorem pr414607 : Nat.Prime 414607 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv43,pv1607]) (by decide +kernel)
def pv414607 : PrimeValue := ⟨414607, pr414607⟩
private theorem pr414611 : Nat.Prime 414611 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv5923]) (by decide +kernel)
def pv414611 : PrimeValue := ⟨414611, pr414611⟩
private theorem pr414629 : Nat.Prime 414629 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv103657]) (by decide +kernel)
def pv414629 : PrimeValue := ⟨414629, pr414629⟩
private theorem pr414677 : Nat.Prime 414677 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv103669]) (by decide +kernel)
def pv414677 : PrimeValue := ⟨414677, pr414677⟩
private theorem pr414683 : Nat.Prime 414683 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv207341]) (by decide +kernel)
def pv414683 : PrimeValue := ⟨414683, pr414683⟩
private theorem pr414703 : Nat.Prime 414703 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23039]) (by decide +kernel)
def pv414703 : PrimeValue := ⟨414703, pr414703⟩
private theorem pr414709 : Nat.Prime 414709 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv4937]) (by decide +kernel)
def pv414709 : PrimeValue := ⟨414709, pr414709⟩
private theorem pr414721 : Nat.Prime 414721 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv414721 : PrimeValue := ⟨414721, pr414721⟩
private theorem pr414731 : Nat.Prime 414731 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv67,pv619]) (by decide +kernel)
def pv414731 : PrimeValue := ⟨414731, pr414731⟩
private theorem pr414767 : Nat.Prime 414767 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv17,pv1109]) (by decide +kernel)
def pv414767 : PrimeValue := ⟨414767, pr414767⟩
private theorem pr414773 : Nat.Prime 414773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv97,pv1069]) (by decide +kernel)
def pv414773 : PrimeValue := ⟨414773, pr414773⟩
private theorem pr414857 : Nat.Prime 414857 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv3989]) (by decide +kernel)
def pv414857 : PrimeValue := ⟨414857, pr414857⟩
private theorem pr414913 : Nat.Prime 414913 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv2161]) (by decide +kernel)
def pv414913 : PrimeValue := ⟨414913, pr414913⟩
private theorem pr414923 : Nat.Prime 414923 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv61,pv179]) (by decide +kernel)
def pv414923 : PrimeValue := ⟨414923, pr414923⟩
private theorem pr414949 : Nat.Prime 414949 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv151,pv229]) (by decide +kernel)
def pv414949 : PrimeValue := ⟨414949, pr414949⟩
private theorem pr414991 : Nat.Prime 414991 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv29,pv53]) (by decide +kernel)
def pv414991 : PrimeValue := ⟨414991, pr414991⟩
private theorem pr415013 : Nat.Prime 415013 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv23,pv347]) (by decide +kernel)
def pv415013 : PrimeValue := ⟨415013, pr415013⟩
private theorem pr415097 : Nat.Prime 415097 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv53,pv89]) (by decide +kernel)
def pv415097 : PrimeValue := ⟨415097, pr415097⟩
private theorem pr415109 : Nat.Prime 415109 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv157,pv661]) (by decide +kernel)
def pv415109 : PrimeValue := ⟨415109, pr415109⟩
private theorem pr415111 : Nat.Prime 415111 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv5,pv101,pv137]) (by decide +kernel)
def pv415111 : PrimeValue := ⟨415111, pr415111⟩
private theorem pr415133 : Nat.Prime 415133 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv67,pv1549]) (by decide +kernel)
def pv415133 : PrimeValue := ⟨415133, pr415133⟩
private theorem pr415141 : Nat.Prime 415141 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv17,pv37]) (by decide +kernel)
def pv415141 : PrimeValue := ⟨415141, pr415141⟩
private theorem pr415187 : Nat.Prime 415187 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv207593]) (by decide +kernel)
def pv415187 : PrimeValue := ⟨415187, pr415187⟩
private theorem pr415201 : Nat.Prime 415201 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv173]) (by decide +kernel)
def pv415201 : PrimeValue := ⟨415201, pr415201⟩
private theorem pr415231 : Nat.Prime 415231 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv13841]) (by decide +kernel)
def pv415231 : PrimeValue := ⟨415231, pr415231⟩
private theorem pr415253 : Nat.Prime 415253 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv103813]) (by decide +kernel)
def pv415253 : PrimeValue := ⟨415253, pr415253⟩
private theorem pr415319 : Nat.Prime 415319 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv281,pv739]) (by decide +kernel)
def pv415319 : PrimeValue := ⟨415319, pr415319⟩
private theorem pr415391 : Nat.Prime 415391 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv41539]) (by decide +kernel)
def pv415391 : PrimeValue := ⟨415391, pr415391⟩
private theorem pr415427 : Nat.Prime 415427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv23,pv821]) (by decide +kernel)
def pv415427 : PrimeValue := ⟨415427, pr415427⟩
private theorem pr415447 : Nat.Prime 415447 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv17,pv4073]) (by decide +kernel)
def pv415447 : PrimeValue := ⟨415447, pr415447⟩
private theorem pr415469 : Nat.Prime 415469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv103867]) (by decide +kernel)
def pv415469 : PrimeValue := ⟨415469, pr415469⟩
private theorem pr415507 : Nat.Prime 415507 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv761]) (by decide +kernel)
def pv415507 : PrimeValue := ⟨415507, pr415507⟩
private theorem pr415517 : Nat.Prime 415517 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv73,pv1423]) (by decide +kernel)
def pv415517 : PrimeValue := ⟨415517, pr415517⟩
private theorem pr415543 : Nat.Prime 415543 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv69257]) (by decide +kernel)
def pv415543 : PrimeValue := ⟨415543, pr415543⟩
private theorem pr415607 : Nat.Prime 415607 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv19,pv10937]) (by decide +kernel)
def pv415607 : PrimeValue := ⟨415607, pr415607⟩
private theorem pr415643 : Nat.Prime 415643 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv207821]) (by decide +kernel)
def pv415643 : PrimeValue := ⟨415643, pr415643⟩
private theorem pr415661 : Nat.Prime 415661 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv2969]) (by decide +kernel)
def pv415661 : PrimeValue := ⟨415661, pr415661⟩
private theorem pr415687 : Nat.Prime 415687 :=
  checkPrime_prime (q := pv23) (ls := [pv2,pv3,pv29,pv2389]) (by decide +kernel)
def pv415687 : PrimeValue := ⟨415687, pr415687⟩
private theorem pr415721 : Nat.Prime 415721 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv19,pv547]) (by decide +kernel)
def pv415721 : PrimeValue := ⟨415721, pr415721⟩
private theorem pr415783 : Nat.Prime 415783 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv23099]) (by decide +kernel)
def pv415783 : PrimeValue := ⟨415783, pr415783⟩
private theorem pr415799 : Nat.Prime 415799 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv127,pv1637]) (by decide +kernel)
def pv415799 : PrimeValue := ⟨415799, pr415799⟩
private theorem pr415823 : Nat.Prime 415823 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv11,pv41,pv461]) (by decide +kernel)
def pv415823 : PrimeValue := ⟨415823, pr415823⟩
private theorem pr415861 : Nat.Prime 415861 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv29,pv239]) (by decide +kernel)
def pv415861 : PrimeValue := ⟨415861, pr415861⟩
private theorem pr415873 : Nat.Prime 415873 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19]) (by decide +kernel)
def pv415873 : PrimeValue := ⟨415873, pr415873⟩
private theorem pr415879 : Nat.Prime 415879 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv69313]) (by decide +kernel)
def pv415879 : PrimeValue := ⟨415879, pr415879⟩
private theorem pr415931 : Nat.Prime 415931 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv41593]) (by decide +kernel)
def pv415931 : PrimeValue := ⟨415931, pr415931⟩
private theorem pr415937 : Nat.Prime 415937 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv67,pv97]) (by decide +kernel)
def pv415937 : PrimeValue := ⟨415937, pr415937⟩
private theorem pr415949 : Nat.Prime 415949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv19,pv421]) (by decide +kernel)
def pv415949 : PrimeValue := ⟨415949, pr415949⟩
private theorem pr415969 : Nat.Prime 415969 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv619]) (by decide +kernel)
def pv415969 : PrimeValue := ⟨415969, pr415969⟩
private theorem pr415979 : Nat.Prime 415979 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv9043]) (by decide +kernel)
def pv415979 : PrimeValue := ⟨415979, pr415979⟩
private theorem pr415993 : Nat.Prime 415993 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17333]) (by decide +kernel)
def pv415993 : PrimeValue := ⟨415993, pr415993⟩
private theorem pr415999 : Nat.Prime 415999 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv191]) (by decide +kernel)
def pv415999 : PrimeValue := ⟨415999, pr415999⟩
private theorem pr416023 : Nat.Prime 416023 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv69337]) (by decide +kernel)
def pv416023 : PrimeValue := ⟨416023, pr416023⟩
private theorem pr416107 : Nat.Prime 416107 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23117]) (by decide +kernel)
def pv416107 : PrimeValue := ⟨416107, pr416107⟩
private theorem pr416147 : Nat.Prime 416147 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv208073]) (by decide +kernel)
def pv416147 : PrimeValue := ⟨416147, pr416147⟩
private theorem pr416153 : Nat.Prime 416153 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv4729]) (by decide +kernel)
def pv416153 : PrimeValue := ⟨416153, pr416153⟩
private theorem pr416167 : Nat.Prime 416167 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv139,pv499]) (by decide +kernel)
def pv416167 : PrimeValue := ⟨416167, pr416167⟩
private theorem pr416201 : Nat.Prime 416201 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv2081]) (by decide +kernel)
def pv416201 : PrimeValue := ⟨416201, pr416201⟩
private theorem pr416243 : Nat.Prime 416243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv208121]) (by decide +kernel)
def pv416243 : PrimeValue := ⟨416243, pr416243⟩
private theorem pr416249 : Nat.Prime 416249 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv7433]) (by decide +kernel)
def pv416249 : PrimeValue := ⟨416249, pr416249⟩
private theorem pr416257 : Nat.Prime 416257 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv271]) (by decide +kernel)
def pv416257 : PrimeValue := ⟨416257, pr416257⟩
private theorem pr416291 : Nat.Prime 416291 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv19,pv313]) (by decide +kernel)
def pv416291 : PrimeValue := ⟨416291, pr416291⟩
private theorem pr416359 : Nat.Prime 416359 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23131]) (by decide +kernel)
def pv416359 : PrimeValue := ⟨416359, pr416359⟩
private theorem pr416387 : Nat.Prime 416387 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv3413]) (by decide +kernel)
def pv416387 : PrimeValue := ⟨416387, pr416387⟩
private theorem pr416393 : Nat.Prime 416393 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv31,pv73]) (by decide +kernel)
def pv416393 : PrimeValue := ⟨416393, pr416393⟩
private theorem pr416401 : Nat.Prime 416401 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv347]) (by decide +kernel)
def pv416401 : PrimeValue := ⟨416401, pr416401⟩
private theorem pr416441 : Nat.Prime 416441 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv29,pv359]) (by decide +kernel)
def pv416441 : PrimeValue := ⟨416441, pr416441⟩
private theorem pr416443 : Nat.Prime 416443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv13,pv19,pv281]) (by decide +kernel)
def pv416443 : PrimeValue := ⟨416443, pr416443⟩
private theorem pr416459 : Nat.Prime 416459 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv151,pv197]) (by decide +kernel)
def pv416459 : PrimeValue := ⟨416459, pr416459⟩
private theorem pr416573 : Nat.Prime 416573 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv8011]) (by decide +kernel)
def pv416573 : PrimeValue := ⟨416573, pr416573⟩
private theorem pr416621 : Nat.Prime 416621 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv37,pv563]) (by decide +kernel)
def pv416621 : PrimeValue := ⟨416621, pr416621⟩
private theorem pr416693 : Nat.Prime 416693 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv104173]) (by decide +kernel)
def pv416693 : PrimeValue := ⟨416693, pr416693⟩
private theorem pr416797 : Nat.Prime 416797 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv47,pv739]) (by decide +kernel)
def pv416797 : PrimeValue := ⟨416797, pr416797⟩
private theorem pr416833 : Nat.Prime 416833 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv167]) (by decide +kernel)
def pv416833 : PrimeValue := ⟨416833, pr416833⟩
private theorem pr416839 : Nat.Prime 416839 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv69473]) (by decide +kernel)
def pv416839 : PrimeValue := ⟨416839, pr416839⟩
private theorem pr416873 : Nat.Prime 416873 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv107,pv487]) (by decide +kernel)
def pv416873 : PrimeValue := ⟨416873, pr416873⟩
private theorem pr416947 : Nat.Prime 416947 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv69491]) (by decide +kernel)
def pv416947 : PrimeValue := ⟨416947, pr416947⟩
private theorem pr416963 : Nat.Prime 416963 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv13,pv29,pv79]) (by decide +kernel)
def pv416963 : PrimeValue := ⟨416963, pr416963⟩
private theorem pr416989 : Nat.Prime 416989 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv13]) (by decide +kernel)
def pv416989 : PrimeValue := ⟨416989, pr416989⟩
private theorem pr417089 : Nat.Prime 417089 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv19]) (by decide +kernel)
def pv417089 : PrimeValue := ⟨417089, pr417089⟩
private theorem pr417097 : Nat.Prime 417097 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1931]) (by decide +kernel)
def pv417097 : PrimeValue := ⟨417097, pr417097⟩
private theorem pr417127 : Nat.Prime 417127 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv3659]) (by decide +kernel)
def pv417127 : PrimeValue := ⟨417127, pr417127⟩
private theorem pr417191 : Nat.Prime 417191 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv41719]) (by decide +kernel)
def pv417191 : PrimeValue := ⟨417191, pr417191⟩
private theorem pr417217 : Nat.Prime 417217 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv41,pv53]) (by decide +kernel)
def pv417217 : PrimeValue := ⟨417217, pr417217⟩
private theorem pr417251 : Nat.Prime 417251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv1669]) (by decide +kernel)
def pv417251 : PrimeValue := ⟨417251, pr417251⟩
private theorem pr417293 : Nat.Prime 417293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv104323]) (by decide +kernel)
def pv417293 : PrimeValue := ⟨417293, pr417293⟩
private theorem pr417311 : Nat.Prime 417311 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv29,pv1439]) (by decide +kernel)
def pv417311 : PrimeValue := ⟨417311, pr417311⟩
private theorem pr417317 : Nat.Prime 417317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv19]) (by decide +kernel)
def pv417317 : PrimeValue := ⟨417317, pr417317⟩
private theorem pr417419 : Nat.Prime 417419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv12277]) (by decide +kernel)
def pv417419 : PrimeValue := ⟨417419, pr417419⟩
private theorem pr417479 : Nat.Prime 417479 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv208739]) (by decide +kernel)
def pv417479 : PrimeValue := ⟨417479, pr417479⟩
private theorem pr417491 : Nat.Prime 417491 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv83,pv503]) (by decide +kernel)
def pv417491 : PrimeValue := ⟨417491, pr417491⟩
private theorem pr417509 : Nat.Prime 417509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv13,pv31,pv37]) (by decide +kernel)
def pv417509 : PrimeValue := ⟨417509, pr417509⟩
private theorem pr417511 : Nat.Prime 417511 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv4639]) (by decide +kernel)
def pv417511 : PrimeValue := ⟨417511, pr417511⟩
private theorem pr417523 : Nat.Prime 417523 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv9941]) (by decide +kernel)
def pv417523 : PrimeValue := ⟨417523, pr417523⟩
private theorem pr417541 : Nat.Prime 417541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv6959]) (by decide +kernel)
def pv417541 : PrimeValue := ⟨417541, pr417541⟩
private theorem pr417553 : Nat.Prime 417553 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv8699]) (by decide +kernel)
def pv417553 : PrimeValue := ⟨417553, pr417553⟩
private theorem pr417581 : Nat.Prime 417581 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv20879]) (by decide +kernel)
def pv417581 : PrimeValue := ⟨417581, pr417581⟩
private theorem pr417583 : Nat.Prime 417583 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv11,pv19,pv37]) (by decide +kernel)
def pv417583 : PrimeValue := ⟨417583, pr417583⟩
private theorem pr417643 : Nat.Prime 417643 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv47,pv1481]) (by decide +kernel)
def pv417643 : PrimeValue := ⟨417643, pr417643⟩
private theorem pr417649 : Nat.Prime 417649 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv7,pv11,pv113]) (by decide +kernel)
def pv417649 : PrimeValue := ⟨417649, pr417649⟩
private theorem pr417671 : Nat.Prime 417671 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv11,pv3797]) (by decide +kernel)
def pv417671 : PrimeValue := ⟨417671, pr417671⟩
private theorem pr417719 : Nat.Prime 417719 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv29837]) (by decide +kernel)
def pv417719 : PrimeValue := ⟨417719, pr417719⟩
private theorem pr417727 : Nat.Prime 417727 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv23,pv1009]) (by decide +kernel)
def pv417727 : PrimeValue := ⟨417727, pr417727⟩
private theorem pr417763 : Nat.Prime 417763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23209]) (by decide +kernel)
def pv417763 : PrimeValue := ⟨417763, pr417763⟩
private theorem pr417793 : Nat.Prime 417793 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17]) (by decide +kernel)
def pv417793 : PrimeValue := ⟨417793, pr417793⟩
private theorem pr417821 : Nat.Prime 417821 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv1607]) (by decide +kernel)
def pv417821 : PrimeValue := ⟨417821, pr417821⟩
private theorem pr417869 : Nat.Prime 417869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv9497]) (by decide +kernel)
def pv417869 : PrimeValue := ⟨417869, pr417869⟩
private theorem pr417931 : Nat.Prime 417931 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv13931]) (by decide +kernel)
def pv417931 : PrimeValue := ⟨417931, pr417931⟩
private theorem pr417941 : Nat.Prime 417941 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv20897]) (by decide +kernel)
def pv417941 : PrimeValue := ⟨417941, pr417941⟩
private theorem pr417953 : Nat.Prime 417953 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv37,pv353]) (by decide +kernel)
def pv417953 : PrimeValue := ⟨417953, pr417953⟩
private theorem pr417961 : Nat.Prime 417961 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv43]) (by decide +kernel)
def pv417961 : PrimeValue := ⟨417961, pr417961⟩
private theorem pr417983 : Nat.Prime 417983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv208991]) (by decide +kernel)
def pv417983 : PrimeValue := ⟨417983, pr417983⟩
private theorem pr418007 : Nat.Prime 418007 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv29,pv7207]) (by decide +kernel)
def pv418007 : PrimeValue := ⟨418007, pr418007⟩
private theorem pr418009 : Nat.Prime 418009 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv17417]) (by decide +kernel)
def pv418009 : PrimeValue := ⟨418009, pr418009⟩
private theorem pr418031 : Nat.Prime 418031 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv17,pv2459]) (by decide +kernel)
def pv418031 : PrimeValue := ⟨418031, pr418031⟩
private theorem pr418051 : Nat.Prime 418051 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv929]) (by decide +kernel)
def pv418051 : PrimeValue := ⟨418051, pr418051⟩
private theorem pr418079 : Nat.Prime 418079 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv209039]) (by decide +kernel)
def pv418079 : PrimeValue := ⟨418079, pr418079⟩
private theorem pr418109 : Nat.Prime 418109 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv104527]) (by decide +kernel)
def pv418109 : PrimeValue := ⟨418109, pr418109⟩
private theorem pr418177 : Nat.Prime 418177 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv418177 : PrimeValue := ⟨418177, pr418177⟩
private theorem pr418199 : Nat.Prime 418199 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv11,pv19009]) (by decide +kernel)
def pv418199 : PrimeValue := ⟨418199, pr418199⟩
private theorem pr418331 : Nat.Prime 418331 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv3803]) (by decide +kernel)
def pv418331 : PrimeValue := ⟨418331, pr418331⟩
private theorem pr418337 : Nat.Prime 418337 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv17,pv769]) (by decide +kernel)
def pv418337 : PrimeValue := ⟨418337, pr418337⟩
private theorem pr418349 : Nat.Prime 418349 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv7,pv67,pv223]) (by decide +kernel)
def pv418349 : PrimeValue := ⟨418349, pr418349⟩
private theorem pr418351 : Nat.Prime 418351 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv2789]) (by decide +kernel)
def pv418351 : PrimeValue := ⟨418351, pr418351⟩
private theorem pr418373 : Nat.Prime 418373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv104593]) (by decide +kernel)
def pv418373 : PrimeValue := ⟨418373, pr418373⟩
private theorem pr418427 : Nat.Prime 418427 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv209213]) (by decide +kernel)
def pv418427 : PrimeValue := ⟨418427, pr418427⟩
private theorem pr418553 : Nat.Prime 418553 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv113,pv463]) (by decide +kernel)
def pv418553 : PrimeValue := ⟨418553, pr418553⟩
private theorem pr418601 : Nat.Prime 418601 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv13,pv23]) (by decide +kernel)
def pv418601 : PrimeValue := ⟨418601, pr418601⟩
private theorem pr418633 : Nat.Prime 418633 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17443]) (by decide +kernel)
def pv418633 : PrimeValue := ⟨418633, pr418633⟩
private theorem pr418637 : Nat.Prime 418637 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv104659]) (by decide +kernel)
def pv418637 : PrimeValue := ⟨418637, pr418637⟩
private theorem pr418699 : Nat.Prime 418699 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv3323]) (by decide +kernel)
def pv418699 : PrimeValue := ⟨418699, pr418699⟩
private theorem pr418709 : Nat.Prime 418709 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv104677]) (by decide +kernel)
def pv418709 : PrimeValue := ⟨418709, pr418709⟩
private theorem pr418721 : Nat.Prime 418721 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv2617]) (by decide +kernel)
def pv418721 : PrimeValue := ⟨418721, pr418721⟩
private theorem pr418751 : Nat.Prime 418751 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv67]) (by decide +kernel)
def pv418751 : PrimeValue := ⟨418751, pr418751⟩
private theorem pr418783 : Nat.Prime 418783 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv59]) (by decide +kernel)
def pv418783 : PrimeValue := ⟨418783, pr418783⟩
private theorem pr418787 : Nat.Prime 418787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv209393]) (by decide +kernel)
def pv418787 : PrimeValue := ⟨418787, pr418787⟩
private theorem pr418793 : Nat.Prime 418793 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv4759]) (by decide +kernel)
def pv418793 : PrimeValue := ⟨418793, pr418793⟩
private theorem pr418799 : Nat.Prime 418799 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv19,pv103,pv107]) (by decide +kernel)
def pv418799 : PrimeValue := ⟨418799, pr418799⟩
private theorem pr418871 : Nat.Prime 418871 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv41887]) (by decide +kernel)
def pv418871 : PrimeValue := ⟨418871, pr418871⟩
private theorem pr418889 : Nat.Prime 418889 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv52361]) (by decide +kernel)
def pv418889 : PrimeValue := ⟨418889, pr418889⟩
private theorem pr418909 : Nat.Prime 418909 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv4987]) (by decide +kernel)
def pv418909 : PrimeValue := ⟨418909, pr418909⟩
private theorem pr418921 : Nat.Prime 418921 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv3491]) (by decide +kernel)
def pv418921 : PrimeValue := ⟨418921, pr418921⟩
private theorem pr418933 : Nat.Prime 418933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv431]) (by decide +kernel)
def pv418933 : PrimeValue := ⟨418933, pr418933⟩
private theorem pr418961 : Nat.Prime 418961 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv5,pv5237]) (by decide +kernel)
def pv418961 : PrimeValue := ⟨418961, pr418961⟩
private theorem pr418981 : Nat.Prime 418981 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv6983]) (by decide +kernel)
def pv418981 : PrimeValue := ⟨418981, pr418981⟩
private theorem pr419183 : Nat.Prime 419183 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv31,pv6761]) (by decide +kernel)
def pv419183 : PrimeValue := ⟨419183, pr419183⟩
private theorem pr419189 : Nat.Prime 419189 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv11,pv1361]) (by decide +kernel)
def pv419189 : PrimeValue := ⟨419189, pr419189⟩
private theorem pr419191 : Nat.Prime 419191 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv89,pv157]) (by decide +kernel)
def pv419191 : PrimeValue := ⟨419191, pr419191⟩
private theorem pr419201 : Nat.Prime 419201 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv131]) (by decide +kernel)
def pv419201 : PrimeValue := ⟨419201, pr419201⟩
private theorem pr419231 : Nat.Prime 419231 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv7,pv53,pv113]) (by decide +kernel)
def pv419231 : PrimeValue := ⟨419231, pr419231⟩
private theorem pr419281 : Nat.Prime 419281 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv1747]) (by decide +kernel)
def pv419281 : PrimeValue := ⟨419281, pr419281⟩
private theorem pr419291 : Nat.Prime 419291 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv23,pv1823]) (by decide +kernel)
def pv419291 : PrimeValue := ⟨419291, pr419291⟩
private theorem pr419351 : Nat.Prime 419351 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv8387]) (by decide +kernel)
def pv419351 : PrimeValue := ⟨419351, pr419351⟩
private theorem pr419383 : Nat.Prime 419383 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv23,pv1013]) (by decide +kernel)
def pv419383 : PrimeValue := ⟨419383, pr419383⟩
private theorem pr419417 : Nat.Prime 419417 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv103,pv509]) (by decide +kernel)
def pv419417 : PrimeValue := ⟨419417, pr419417⟩
private theorem pr419443 : Nat.Prime 419443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv53,pv1319]) (by decide +kernel)
def pv419443 : PrimeValue := ⟨419443, pr419443⟩
private theorem pr419459 : Nat.Prime 419459 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv17,pv73]) (by decide +kernel)
def pv419459 : PrimeValue := ⟨419459, pr419459⟩
private theorem pr419477 : Nat.Prime 419477 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv104869]) (by decide +kernel)
def pv419477 : PrimeValue := ⟨419477, pr419477⟩
private theorem pr419491 : Nat.Prime 419491 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv5,pv59,pv79]) (by decide +kernel)
def pv419491 : PrimeValue := ⟨419491, pr419491⟩
private theorem pr419513 : Nat.Prime 419513 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv41,pv1279]) (by decide +kernel)
def pv419513 : PrimeValue := ⟨419513, pr419513⟩
private theorem pr419563 : Nat.Prime 419563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv13,pv163]) (by decide +kernel)
def pv419563 : PrimeValue := ⟨419563, pr419563⟩
private theorem pr419597 : Nat.Prime 419597 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv19,pv5521]) (by decide +kernel)
def pv419597 : PrimeValue := ⟨419597, pr419597⟩
private theorem pr419603 : Nat.Prime 419603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv209801]) (by decide +kernel)
def pv419603 : PrimeValue := ⟨419603, pr419603⟩
private theorem pr419651 : Nat.Prime 419651 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv109]) (by decide +kernel)
def pv419651 : PrimeValue := ⟨419651, pr419651⟩
private theorem pr419711 : Nat.Prime 419711 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv19,pv47]) (by decide +kernel)
def pv419711 : PrimeValue := ⟨419711, pr419711⟩
private theorem pr419777 : Nat.Prime 419777 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv937]) (by decide +kernel)
def pv419777 : PrimeValue := ⟨419777, pr419777⟩
private theorem pr419801 : Nat.Prime 419801 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv2099]) (by decide +kernel)
def pv419801 : PrimeValue := ⟨419801, pr419801⟩
private theorem pr419803 : Nat.Prime 419803 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv31,pv37,pv61]) (by decide +kernel)
def pv419803 : PrimeValue := ⟨419803, pr419803⟩
private theorem pr419821 : Nat.Prime 419821 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv6997]) (by decide +kernel)
def pv419821 : PrimeValue := ⟨419821, pr419821⟩
private theorem pr419831 : Nat.Prime 419831 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv41983]) (by decide +kernel)
def pv419831 : PrimeValue := ⟨419831, pr419831⟩
private theorem pr419927 : Nat.Prime 419927 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv31,pv521]) (by decide +kernel)
def pv419927 : PrimeValue := ⟨419927, pr419927⟩
private theorem pr419999 : Nat.Prime 419999 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv373,pv563]) (by decide +kernel)
def pv419999 : PrimeValue := ⟨419999, pr419999⟩
private theorem pr420037 : Nat.Prime 420037 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv29,pv71]) (by decide +kernel)
def pv420037 : PrimeValue := ⟨420037, pr420037⟩
private theorem pr420041 : Nat.Prime 420041 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv10501]) (by decide +kernel)
def pv420041 : PrimeValue := ⟨420041, pr420041⟩
private theorem pr420047 : Nat.Prime 420047 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv11,pv61,pv313]) (by decide +kernel)
def pv420047 : PrimeValue := ⟨420047, pr420047⟩
private theorem pr420073 : Nat.Prime 420073 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv3,pv23,pv761]) (by decide +kernel)
def pv420073 : PrimeValue := ⟨420073, pr420073⟩
private theorem pr420149 : Nat.Prime 420149 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv105037]) (by decide +kernel)
def pv420149 : PrimeValue := ⟨420149, pr420149⟩
private theorem pr420163 : Nat.Prime 420163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv239,pv293]) (by decide +kernel)
def pv420163 : PrimeValue := ⟨420163, pr420163⟩
private theorem pr420191 : Nat.Prime 420191 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv42019]) (by decide +kernel)
def pv420191 : PrimeValue := ⟨420191, pr420191⟩
private theorem pr420221 : Nat.Prime 420221 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv21011]) (by decide +kernel)
def pv420221 : PrimeValue := ⟨420221, pr420221⟩
private theorem pr420307 : Nat.Prime 420307 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv70051]) (by decide +kernel)
def pv420307 : PrimeValue := ⟨420307, pr420307⟩
private theorem pr420317 : Nat.Prime 420317 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv59,pv137]) (by decide +kernel)
def pv420317 : PrimeValue := ⟨420317, pr420317⟩
private theorem pr420341 : Nat.Prime 420341 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv21017]) (by decide +kernel)
def pv420341 : PrimeValue := ⟨420341, pr420341⟩
private theorem pr420349 : Nat.Prime 420349 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv1523]) (by decide +kernel)
def pv420349 : PrimeValue := ⟨420349, pr420349⟩
private theorem pr420353 : Nat.Prime 420353 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv821]) (by decide +kernel)
def pv420353 : PrimeValue := ⟨420353, pr420353⟩
private theorem pr420367 : Nat.Prime 420367 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv70061]) (by decide +kernel)
def pv420367 : PrimeValue := ⟨420367, pr420367⟩
private theorem pr420383 : Nat.Prime 420383 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv210191]) (by decide +kernel)
def pv420383 : PrimeValue := ⟨420383, pr420383⟩
private theorem pr420419 : Nat.Prime 420419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv210209]) (by decide +kernel)
def pv420419 : PrimeValue := ⟨420419, pr420419⟩
private theorem pr420457 : Nat.Prime 420457 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17519]) (by decide +kernel)
def pv420457 : PrimeValue := ⟨420457, pr420457⟩
private theorem pr420551 : Nat.Prime 420551 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv5,pv13,pv647]) (by decide +kernel)
def pv420551 : PrimeValue := ⟨420551, pr420551⟩
private theorem pr420557 : Nat.Prime 420557 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv47,pv2237]) (by decide +kernel)
def pv420557 : PrimeValue := ⟨420557, pr420557⟩
private theorem pr420569 : Nat.Prime 420569 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv52571]) (by decide +kernel)
def pv420569 : PrimeValue := ⟨420569, pr420569⟩
private theorem pr420731 : Nat.Prime 420731 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv42073]) (by decide +kernel)
def pv420731 : PrimeValue := ⟨420731, pr420731⟩
private theorem pr420757 : Nat.Prime 420757 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv5009]) (by decide +kernel)
def pv420757 : PrimeValue := ⟨420757, pr420757⟩
private theorem pr420779 : Nat.Prime 420779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv3449]) (by decide +kernel)
def pv420779 : PrimeValue := ⟨420779, pr420779⟩
private theorem pr420899 : Nat.Prime 420899 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv389,pv541]) (by decide +kernel)
def pv420899 : PrimeValue := ⟨420899, pr420899⟩
private theorem pr420929 : Nat.Prime 420929 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv6577]) (by decide +kernel)
def pv420929 : PrimeValue := ⟨420929, pr420929⟩
private theorem pr420941 : Nat.Prime 420941 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv1619]) (by decide +kernel)
def pv420941 : PrimeValue := ⟨420941, pr420941⟩
private theorem pr421037 : Nat.Prime 421037 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv11,pv1367]) (by decide +kernel)
def pv421037 : PrimeValue := ⟨421037, pr421037⟩
private theorem pr421079 : Nat.Prime 421079 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv19,pv1583]) (by decide +kernel)
def pv421079 : PrimeValue := ⟨421079, pr421079⟩
private theorem pr421093 : Nat.Prime 421093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv557]) (by decide +kernel)
def pv421093 : PrimeValue := ⟨421093, pr421093⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
